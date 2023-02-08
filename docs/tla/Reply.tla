---- MODULE Reply ----
EXTENDS Sequences

\* Reply states:
VARIABLES DeletedLocally  \* dead
VARIABLES Ready, DecryptionFailed, DownloadFailed, SendFailed  \* alive (terminal)
VARIABLES SendPending, Sending, DownloadPending, Downloading, Downloaded  \* alive

\* Reply types:
InReply == [type: {"in"}]  \* incoming
OutReply == [type: {"out"}]  \* outgoing
Replies == InReply \union OutReply

\* RunnableQueue job states, sans prioritization:
VARIABLES queue, done

vars == <<
    DeletedLocally,
    Ready, DecryptionFailed, DownloadFailed, SendFailed,
    SendPending, Sending, DownloadPending, Downloading, Downloaded,
    queue, done
    >>

TypeOK ==
    /\ queue \in Seq(Replies)
    /\ done \in Seq(Replies)

Init ==
    /\ DeletedLocally = {}
    /\ Ready = {}
    /\ DecryptionFailed = {}
    /\ DownloadFailed = {}
    /\ SendFailed = {}
    /\ SendPending = {}
    /\ Sending = {}
    /\ DownloadPending = {}
    /\ Downloading = {}
    /\ Downloaded = {}
    /\ queue = <<>>
    /\ done = <<>>

Next == UNCHANGED vars

Spec == Init /\ [][Next]_vars
====
