---- MODULE Reply ----
EXTENDS FiniteSets, Naturals, Sequences, TLC
CONSTANTS
    JOB_RETRIES,
    InReplies,
    OutReplies,
    ToDelete

Replies == InReplies \union OutReplies


\* ---- HELPERS ----

Range(f) == {f[x]: x \in DOMAIN f}
Size(f) == Cardinality(DOMAIN f)

Contains(q, id) == \E el \in Range(q): el.id = id


\* ---- TYPES ----

\* Reply model:
Id == Nat
Deletion == {
    "DeletePending",
    "Deleting",
    "DeletedLocally"
}
SharedStates == {"Ready"} \union Deletion
TerminalStates == {
    "Ready",
    "DownloadFailed",
    "DecryptionFailed",
    "SendFailed",
    "DeletedLocally"
    }
NULL == [type: {"NULL"}]
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
    NULL \union
    InReply \union
    OutReply
VARIABLES pool, deleting

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

Delete(id) ==
    /\ id \in DOMAIN pool
    /\ id \notin deleting
    /\ deleting' = deleting \union {id}
    /\ queue' = Append(queue, [
            id |-> id,
            type |-> "Delete",
            ttl |-> JOB_RETRIES
       ])
    /\ UNCHANGED<<done, pool>>

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

Check(id, from) == pool[id].state = from

Set(id, to) == pool' = [pool EXCEPT ![id].state = to]

Trans(id, from, to) ==
    /\ Check(id, from)
    /\ Set(id, to)

DeleteInterrupt(job) ==
    /\ pool[job.id].state \notin Deletion
    /\ Set(job.id, "DeletePending")
    /\ UNCHANGED<<done, queue>>

DeletePending(job) ==
    /\ Trans(job.id, "DeletePending", "Deleting")
    /\ UNCHANGED<<done, queue>>

Deleting(job) ==
    \/ /\ pool' = [pool EXCEPT ![job.id] = [type |-> "NULL"]]
       /\ QueueNext
    \/ Retry(job)
    \/ /\ Failed(job)
       /\ Trans(job.id, "Deleting", "DeletedLocally")
       /\ QueueNext

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

ProcessJob ==
    LET job == Head(queue)
    IN
        \/ /\ job \in DownloadReplyJob
           /\ \/ DownloadPending(job)
              \/ Downloading(job)
              \/ Downloaded(job)
        \/ /\ job \in SendReplyJob
           /\ \/ SendPending(job)
              \/ Sending(job)
        \/ /\ job \in DeleteJob
           /\ \/ DeleteInterrupt(job)
              \/ DeletePending(job)
              \/ Deleting(job)

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
    \/ QueueRun
    \/ \E id \in ToDelete: Delete(id)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)


\* ---- PROPERTIES  ---

PoolLiveness ==
    <>[](\A r \in Range(pool):
        \/ r \in NULL
        \/ r.state \in TerminalStates
        )

QueueLiveness == <>[](Len(queue) = 0)
====
