---- MODULE Reply ----
EXTENDS FiniteSets, Naturals, Sequences, TLC
CONSTANTS
    InReplies,
    OutReplies

Replies == InReplies \union OutReplies


\* ---- HELPERS ----

Range(f) == {f[x]: x \in DOMAIN f}
Size(f) == Cardinality(DOMAIN f)

Contains(q, id) == \E el \in Range(q): el.id = id


\* ---- TYPES ----

\* Reply model:
Id == Nat
SharedStates == {"Ready", "DeletedLocally"}
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
Reply == InReply \union OutReply
VARIABLES pool

\* RunnableQueue, sans prioritization.  Current = Head(queue).
DownloadReplyJob == [id: Id, type: {"DownloadReply"}]
SendReplyJob == [id: Id, type: {"SendReply"}]
Job == DownloadReplyJob \union SendReplyJob
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

PoolAndQueueInSync ==
    /\ \A job \in Range(queue): job.id \in DOMAIN pool
    /\ \A job \in Range(done): job.id \in DOMAIN pool
    /\ \A id \in DOMAIN pool:
        \/ Contains(queue, id)
        \/ Contains(done, id)


\* ---- QUEUE ACTIONS ----

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
                type |-> job
            ])
        /\ UNCHANGED done

QueueNext ==
    /\ done' = Append(done, Head(queue))
    /\ queue' = Tail(queue)


\* --- REPLY STATES ---

Trans(id, from, to) ==
    /\ pool[id].state = from
    /\ pool' = [pool EXCEPT ![id].state = to]

DownloadPending(job) ==
    /\ Trans(job.id, "DownloadPending", "Downloading")
    /\ UNCHANGED<<done, queue>>

Downloading(job) ==
    \/ /\ Trans(job.id, "Downloading", "Downloaded")
       /\ UNCHANGED<<done, queue>>
    \/ /\ Trans(job.id, "DownloadPending", "DownloadFailed")
       /\ QueueNext

Downloaded(job) ==
    /\ \/ Trans(job.id, "Downloaded", "Ready")
       \/ Trans(job.id, "Downloaded", "DecryptionFailed")
    /\ QueueNext

SendPending(job) ==
    /\ Trans(job.id, "SendPending", "Sending")
    /\ UNCHANGED<<done, queue>>

Sending(job) ==
    /\ \/ Trans(job.id, "Sending", "Ready")
       \/ Trans(job.id, "Sending", "SendFailed")
    /\ QueueNext


\* ---- ACTIONS ----

vars == <<
    pool,
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

QueueRun ==
    \/ /\ Len(queue) > 0
       /\ ProcessJob
    \/ UNCHANGED vars  \* nothing changes if there's nothing to do

Init ==
    /\ pool = <<>>
    /\ queue = <<>>
    /\ done = <<>>

Next ==
    \/ \E id \in Replies:
        /\ id = Size(pool)
        /\ Enqueue(id)
    \/ QueueRun

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)
====
