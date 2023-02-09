---- MODULE Reply ----
EXTENDS FiniteSets, Naturals, Sequences

\* Reply model:
Id == Nat
SharedStates == {"Ready", "DeletedLocally"}
InReply ==
    [
        id: Id,
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
        id: Id,
        type: {"out"},
        state: {
            "SendPending",
            "Sending",
            "SendFailed"
        } \union SharedStates
    ]
Reply == InReply \union OutReply
VARIABLES pool

\* RunnableQueue job states, sans prioritization.  Current = Head(queue).
VARIABLES queue, done

vars == <<
    pool,
    queue, done
    >>

TypeOK ==
    /\ \/ Cardinality(pool) = 0
       \/ pool \in Reply
    /\ queue \in Seq(Reply)
    /\ done \in Seq(Reply)

Init ==
    /\ pool = {}
    /\ queue = <<>>
    /\ done = <<>>

Next == UNCHANGED vars

Spec == Init /\ [][Next]_vars
====
