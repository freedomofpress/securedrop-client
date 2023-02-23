---- MODULE Reply ----
EXTENDS FiniteSets, Naturals, Sequences, TLC
CONSTANTS
    JOB_RETRIES,
    InReplies,
    OutReplies,
    ForLocalDeletion,
    ForRemoteDeletion

Replies == InReplies \union OutReplies


\* ---- HELPERS ----

Range(f) == {f[x]: x \in DOMAIN f}
Size(f) == Cardinality(DOMAIN f)

Contains(q, id) == \E el \in Range(q): el.id = id


\* ---- TYPES ----

\* Reply model:
Id == Nat
DEAD == "DEAD"
Deletion == {"DeletedLocally"}
SharedStates == {"Ready"} \union Deletion
TerminalStates == {
    "Ready",
    "DownloadFailed",
    "DecryptionFailed",
    "SendFailed"
    } \union Deletion
DeadReply == [type: {DEAD}]
InReply ==
    [
        type: {"in"},
        state: {
            "DownloadPending",
            "Downloading",
            "DownloadFailed",
            "Downloaded",
            "DecryptionFailed"
        } \union SharedStates
    ]
OutReply ==
    [
        type: {"out"},
        state: {
            "SendPending",
            "Sending",
            "SendFailed"
        } \union SharedStates
    ]
Reply ==
    DeadReply \union
    InReply \union
    OutReply
VARIABLES pool, deleting

IsAlive(id) ==
    /\ id \in DOMAIN pool
    /\ pool[id] \notin DeadReply

IsAvailable(id) ==
    /\ IsAlive(id)
    /\ pool[id].state \notin Deletion

IsInState(id, from) ==
    /\ IsAlive(id)
    /\ pool[id].state = from

Set(id, to) == pool' = [pool EXCEPT ![id].state = to]

\* NB.  We can't do ![id] = DeadReply because the type DeadReply will be evaluated as the set
\* {DeadReply}.
Delete(id) == pool' = [pool EXCEPT ![id] = [type |-> DEAD]]

\* RunnableQueue, sans prioritization.  Current = Head(queue).
DeleteJob == [id: Id, type: {"Delete"}, ttl: Nat]  \* FIXME: DeleteConversationJob
DownloadReplyJob == [id: Id, type: {"DownloadReply"}, ttl: Nat]
SendReplyJob == [id: Id, type: {"SendReply"}, ttl: Nat]
Job ==
    DeleteJob \union
    DownloadReplyJob \union
    SendReplyJob
VARIABLES queue, done


\* ---- INVARIANTS ----

PoolTypeOK ==
    /\ DOMAIN pool \subseteq Replies
    /\ pool \in [DOMAIN pool -> Reply]
QueueTypeOK ==
    /\ queue \in Seq(Job)
    /\ done \in Seq(Job)

TypeOK ==
    /\ PoolTypeOK
    /\ QueueTypeOK


\* ---- QUEUE ACTIONS ----

LocalDelete(id) ==
    /\ id \in DOMAIN pool
    /\ id \notin deleting
    /\ deleting' = deleting \union {id}
    /\ queue' = Append(queue, [
            id |-> id,
            type |-> "Delete",
            ttl |-> JOB_RETRIES
       ])
    /\ UNCHANGED<<done, pool>>

RemoteDelete(id) ==
    /\ IsAlive(id)
    /\ Delete(id)
    /\ UNCHANGED<<deleting, done, queue>>

Enqueue(id) ==
    LET
        dir == IF id \in InReplies THEN "in" ELSE "out"
        state == IF id \in InReplies THEN "DownloadPending" ELSE "SendPending"
        job == IF id \in InReplies THEN "DownloadReply" ELSE "SendReply"
    IN
        \* https://groups.google.com/g/tlaplus/c/-c7o7G9AS5M/m/Fi66-Um8CAAJ
        /\ pool' = pool @@ (id :> [
                type |-> dir,
                state |-> state
            ])
        /\ queue' = Append(queue, [
                id |-> id,
                type |-> job,
                ttl |-> JOB_RETRIES
            ])
        /\ UNCHANGED done

Failed(job) == job.ttl = 0

Retry(job) ==
    /\ job.ttl > 0
    /\ queue' = <<[
        id |-> job.id,
        type |-> job.type,
        ttl |-> job.ttl - 1
        ]>> \o Tail(queue)
    /\ UNCHANGED<<done, pool>>

QueueNext ==
    /\ done' = Append(done, Head(queue))
    /\ queue' = Tail(queue)


\* --- REPLY STATES ---

Trans(id, from, to) ==
    /\ IsInState(id, from)
    /\ Set(id, to)

DeleteInterrupt(job) ==
    /\ Set(job.id, "DeletedLocally")
    /\ UNCHANGED<<done, queue>>

DeletedLocally(job) ==
    \/ /\ Delete(job.id)
       /\ QueueNext
    \/ Retry(job)
    \/ /\ Failed(job)
       /\ QueueNext
       /\ UNCHANGED pool

DownloadPending(job) ==
    /\ Trans(job.id, "DownloadPending", "Downloading")
    /\ UNCHANGED<<done, queue>>

Downloading(job) ==
    \/ /\ Trans(job.id, "Downloading", "Downloaded")
       /\ UNCHANGED<<done, queue>>
    \/ Retry(job)
    \/ /\ Failed(job)
       /\ Trans(job.id, "DownloadPending", "DownloadFailed")
       /\ QueueNext

Downloaded(job) ==
    /\ \/ Trans(job.id, "Downloaded", "Ready")
       \/ Trans(job.id, "Downloaded", "DecryptionFailed")
    /\ QueueNext

SendPending(job) ==
    /\ Trans(job.id, "SendPending", "Sending")
    /\ UNCHANGED<<done, queue>>

Sending(job) ==
    \/ /\ Trans(job.id, "Sending", "Ready")
       /\ QueueNext
    \/ Retry(job)
    \/ /\ Failed(job)
       /\ Trans(job.id, "Sending", "SendFailed")
       /\ QueueNext


\* ---- ACTIONS ----

vars == <<
    pool, deleting,
    queue, done
    >>

FailureRecovery ==
    \E id \in DOMAIN pool:
        /\ IsInState(id, "SendFailed")
        /\ pool' = [pool EXCEPT ![id] = [
                state |-> "DownloadPending",
                type |-> "in"
            ]]
        /\ queue' = Append(queue, [
                id |-> id,
                type |-> "DownloadReply",
                ttl |-> JOB_RETRIES
            ])
        /\ UNCHANGED<<deleting, done>>

ProcessJob ==
    LET job == Head(queue)
    IN
        IF IsAvailable(job.id) THEN
        \/ /\ job \in DownloadReplyJob
           /\ \/ DownloadPending(job)
              \/ Downloading(job)
              \/ Downloaded(job)
        \/ /\ job \in SendReplyJob
           /\ \/ SendPending(job)
              \/ Sending(job)
        \/ /\ job \in DeleteJob
           /\ \/ DeleteInterrupt(job)
              \/ DeletedLocally(job)
        ELSE
        /\ QueueNext
        /\ UNCHANGED pool

QueueRun ==
    \/ /\ Len(queue) > 0
       /\ ProcessJob
       /\ UNCHANGED deleting
    \/ UNCHANGED vars  \* nothing changes if there's nothing to do


\* ---- MODEL SETUP ----

Init ==
    /\ deleting = {}
    /\ pool = <<>>
    /\ queue = <<>>
    /\ done = <<>>

Next ==
    \/ \E id \in Replies:
        /\ id = Size(pool)
        /\ Enqueue(id)
        /\ UNCHANGED deleting
    \/ FailureRecovery
    \/ QueueRun
    \/ \E id \in ForLocalDeletion: LocalDelete(id)
    \/ \E id \in ForRemoteDeletion: RemoteDelete(id)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)


\* ---- PROPERTIES  ---

PoolLiveness ==
    <>[](\A r \in Range(pool):
        \/ r \in DeadReply
        \/ r.state \in TerminalStates
        )

QueueLiveness == <>[](Len(queue) = 0)
====

The following property DeletionWins does *not* hold, for example under the
sequence SendReplyJob (fails) --> DeleteJob (succeeds) --> DownloadReplyJob
(succeeds).

ToBeDeleted == ForLocalDeletion \union ForRemoteDeletion

IsDeleted(id) ==
    \/ ~IsAlive(id)
    \/ ~IsAvailable(id)

DeletionWins ==
    <>[](\A id \in ToBeDeleted: IsDeleted(id))