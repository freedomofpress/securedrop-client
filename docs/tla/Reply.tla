---- MODULE Reply ----
EXTENDS FiniteSets, Naturals, Sequences, TLC
CONSTANTS
    InReplies,
    OutReplies

Replies == InReplies \union OutReplies

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
VARIABLES ids, pool

\* RunnableQueue, sans prioritization.  Current = Head(queue).
DownloadReplyJob == [id: Id, type: {"DownloadReply"}]
SendReplyJob == [id: Id, type: {"SendReply"}]
Job == DownloadReplyJob \union SendReplyJob
VARIABLES queue, done

vars == <<
    ids, pool,
    queue, done
    >>

PoolOK ==
    /\ ids \subseteq Replies
    /\ pool \in [ids -> Reply]
QueueOK ==
    /\ queue \in Seq(Job)
    /\ done \in Seq(Job)

TypeOK ==
    /\ PoolOK
    /\ QueueOK


Enqueue(id) ==
    LET
        dir == IF id \in InReplies THEN "in" ELSE "out"
        state == IF id \in InReplies THEN "DownloadPending" ELSE "SendPending"
        job == IF id \in InReplies THEN "DownloadReply" ELSE "SendReply"
    IN
        /\ ids' = ids \union {id}
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

Process ==
    /\ Len(queue) > 0
    /\ done' = Append(done, Head(queue))
    /\ queue' = Tail(queue)
    /\ UNCHANGED<<ids, pool>>

Init ==
    /\ ids = {}
    /\ pool = <<>>
    /\ queue = <<>>
    /\ done = <<>>

Next ==
    \/ \E id \in Replies:
        /\ id = Cardinality(ids)
        /\ Enqueue(id)
    \/ Process
    \/ UNCHANGED vars

Spec == Init /\ [][Next]_vars
====
