Adapted from <https://learntla.com/topics/state-machines.html>.

---- MODULE Reply ----
EXTENDS TLC
VARIABLE state
vars == <<state>>

\* Dead (to us): we've deleted it locally, but we have to keep it around until it's confirmed
\* deleted remotely too.
Dead == {"DeletedLocally"}

AliveTerminalStates == {
    "Ready",

    "DecryptionFailed",
    "DownloadFailed",
    "SendFailed"
}

TerminalStates == AliveTerminalStates \union Dead

\* Alive: we haven't deleted it locally yet, nor has it been deleted remotely.
AliveStates == AliveTerminalStates \union {
    "SendPending",
    "Sending",

    "DownloadPending",
    "Downloading",
    "Downloaded"
}

\* Gone: either it was dead and now it's gone (confirmed deleted remotely); or it was just
\* deleted remotely.

States == AliveStates \union Dead

TopDown == [Alive |-> AliveStates] @@ [s \in States |-> {}]

RECURSIVE In(_, _)
In(s, p) ==
    \/ s = p
    \/ \E c \in TopDown[p]:
        In(s, c)

Trans(from, to) ==
    /\ In(state, from)
    /\ state' = to

Init ==
    \/ state = "SendPending"  \* type == "outgoing"
    \/ state = "DownloadPending"  \* type == "incoming"

Next ==
    \* Local deletion can occur at any time:
    \/ Trans("Alive", "DeletedLocally")

    \* Outgoing reply (we're sending):
    \/ Trans("SendPending", "Sending")  \* in SendReplyJob
    \/ Trans("Sending", "SendFailed")
    \/ Trans("Sending", "Ready")  \* sent

    \* Incoming reply (someone else sent; we're downloading):
    \/ Trans("DownloadPending", "Downloading")  \* in DownloadReplyJob
    \/ Trans("Downloading", "DownloadFailed")
    \/ Trans("Downloading", "Downloaded")
    \/ Trans("Downloaded", "DecryptionFailed")
    \/ Trans("Downloaded", "Ready")  \* decrypted

    \* Don't deadlock on terminal states.
    \/ /\ state \in TerminalStates
       /\ UNCHANGED state

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(Next)

\* Prove that the machine reaches a terminal state.  By contrast,
\* <>[](state \in AliveTerminalStates) does *not* hold, and TLA+ will warn us that the path (e.g.)
\* Send --> SendPending --> DeletedLocally violates it.
Termination == <>[](state \in TerminalStates)
====
