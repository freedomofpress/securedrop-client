## Introduction

This TLA+ module models (abstractions of) the following components of the
SecureDrop Client:

- the unified `securedrop_client.db.Reply` object proposed in
  freedomofpress/securedrop-engineering#8; and
- `securedrop_client.queue.RunnableQueue`, with respect to:
    - `securedrop_client.api_jobs.downloads.DownloadReplyJob`;
    - `securedrop_client.api_jobs.uploads.SendReplyJob`; and
    - `securedrop_client.api_jobs.sources.DeleteConversationJob` as it pertains
      to an individual `Reply` object.

Specifically, this module models the scenarios possible under the following
events, according to the parameters tunable in `Reply.cfg`:

1. The Client attempts to send one or more replies.

2. The Client attempts to download one or more replies, any of which may be a
   reply that the Client previously failed to send.

3. The Client attempts to delete one or more replies.

4. The Client learns that one or more replies has been deleted on the server.

Importantly, this model does not favor _desirable_ combinations or sequences of
these events.  Instead, the model defines the rules for what is possible at each
moment (tick) in time, and the resulting state-graph proves what is therefore
possible across time.  Desirable and undesirable sequences have equal
probabilistic weight[1], which lets the model check whether our rules---that is,
both our intentions and our assumptions, across components---are valid and
sufficient.

[1]: https://groups.google.com/g/tlaplus/c/ZDe9ogog6mE/m/Ute2kcaCAQAJ

---- MODULE Reply ----
EXTENDS FiniteSets, Naturals, Sequences, TLC
CONSTANTS
    JOB_RETRIES,
    NumReplies,
    ForLocalDeletion, ForRemoteDeletion

Replies == 0..(NumReplies - 1)


\* ---- HELPERS ----

\* Pythonically: {f[k] for k in f.keys()}, where f.keys() is equivalent to
\* DOMAIN f.
Range(f) == {f[x]: x \in DOMAIN f}

\* Pythonically: len(f.keys()), where f.keys() is as above.
Size(f) == Cardinality(DOMAIN f)

\* Pythonically: id in q.
Contains(q, id) == \E el \in Range(q): el.id = id


\* ---- TYPES ----

\* The unified Reply model proposed in freedomofpress/securedrop-engineering#8.
\* We have to build it up from primitive types...
Id == Nat
\* ...through unions of allowed values.  Note that we union Deletion
\* explicitly into both SharedStates and TerminalStates, because it's
\* a testable feature of this model, not a necessary constraint, that
\* the Deletion states are both shared (between incoming and outgoing replies)
\* and possibly terminal (meaning that their persistence is not considered
\* a stutter or deadlock).
Deletion == {"DeletedLocally"}
SharedStates == {"Ready"} \union Deletion
TerminalStates == {
    "Ready",
    "DownloadFailed",
    "DecryptionFailed",
    "SendFailed"
    } \union Deletion
\* ...and into typed structs, which TLA+ will let us enforce with invariants.
\* For example, a dead reply has only a type, nothing more, because we need
\* a way to show a reply is "gone" even though we can't remove it from a
\* function (mapping) once we've added it (https://stackoverflow.com/q/47115185)...
DeadReply == [type |-> "DEAD"]
\* ...while an incoming reply has both a type and set of possible states...
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
\* ...and an outgoing reply has both a type and a *different* (though
\* intersecting)  set of possible states.
OutReply ==
    [
        type: {"out"},
        state: {
            "SendPending",
            "Sending",
            "SendFailed"
        } \union SharedStates
    ]
\* Finally: incoming, outgoing, and dead replies all count as type Reply.
Reply == UNION {
    InReply,
    OutReply,
    {DeadReply}
}
VARIABLES
    \* The pool is our abstract database: the set of all Reply records we've
    \* known about in this model run.
    pool,
    \* Auxiliary: the set of IDs for which we've processed deletion operations
    \* in this model run.
    deleting

\* A reply is alive if it (a) exists and (b) is not dead.
IsAlive(id) ==
    /\ id \in DOMAIN pool
    /\ pool[id] \notin {DeadReply}

\* A reply is available if it (a) is alive and (b) has not been locally deleted.
IsAvailable(id) ==
    /\ IsAlive(id)
    /\ pool[id].state \notin Deletion

\* Check whether the reply is (a) alive and (b) in the from-state.
IsInState(id, from) ==
    /\ IsAlive(id)
    /\ pool[id].state = from

\* Copy pool to pool', but move the value at `id` to the to-state.
Set(id, to) == pool' = [pool EXCEPT ![id].state = to]

\* If the reply at `id` is in the from-state, move it to the to-state.
Trans(id, from, to) ==
    /\ IsInState(id, from)
    /\ Set(id, to)

\* Copy pool to pool', but replace the value at `id` with the dead reply.
Delete(id) == pool' = [pool EXCEPT ![id] = DeadReply]


\* Abstract API jobs.  Jobs have an `id` (like Reply.id), a `type`, and a
\* decrementing `ttl` for retry behavior.

\* DeleteJob is an abstraction of
\* securedrop_client.api_jobs.source.DeleteConversationJob to model its effects
\* on an individual Reply object, since this model does not include the concepts
\* of sources or conversations.
DeleteJob == [id: Id, type: {"Delete"}, ttl: Nat]
DownloadReplyJob == [id: Id, type: {"DownloadReply"}, ttl: Nat]
SendReplyJob == [id: Id, type: {"SendReply"}, ttl: Nat]
Job ==
    DeleteJob \union
    DownloadReplyJob \union
    SendReplyJob
VARIABLES
    \* The abstract RunnableQueue, sans prioritization
    \* (https://learntla.com/topics/message-queues.html).  The current job is
    \* Head(queue).
    queue,
    \* Auxiliary: completed jobs from `queue` are appended to `done`, so that we
    \* can prove what's happened to them in each model run.
    done

\* A job is expired if its `ttl` (remaining retries) reaches 0.
IsExpired(job) == job.ttl = 0


\* ---- INVARIANTS ----
\* By marking these operators as "INVARIANT" in "Reply.cfg", TLA+ will check
\* that they're *always* true: at every moment (tick) in the model.
\* Think of this as abstract runtime type-checking
\* (https://learntla.com/core/invariants.html).  We have one invariant for each
\* of our major data structures.

\* The pool contains only records enumerated in the constant set Replies and
\* of type Reply.
PoolTypeOK ==
    \E seen \in SUBSET Replies:
        pool \in [seen -> Reply]

\* Both queues are sequences of type Job.
QueueTypeOK ==
    /\ queue \in Seq(Job)
    /\ done \in Seq(Job)


\* ---- QUEUE ACTIONS ----
\* These are actions because they modify the value of some variable x' at the
\* next tick as well as check its value x at the current tick.

\* The user initiated deletion of a reply.  If it exists, and if we haven't
\* already started processing its deletion, enqueue a DeleteJob.
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

\* The server informed us of deletion of a reply.  If it's not dead and gone
\* already, it is now: remote deletion supervenes on *whatever* else we might
\* be doing, including local deletion.
RemoteDelete(id) ==
    /\ IsAlive(id)
    /\ Delete(id)
    /\ UNCHANGED<<deleting, done, queue>>

\* Create the job-record pair for `id`, chosen at random to be either an
\* incoming or an outgoing reply.  `pool` is updated via syntactic sugar
\* like <https://groups.google.com/g/tlaplus/c/-c7o7G9AS5M/m/Fi66-Um8CAAJ>.
Enqueue(id) ==
    \/ /\ queue' = Append(queue, [
                id |-> id,
                type |-> "DownloadReply",
                ttl |-> JOB_RETRIES
            ])
       /\ pool' = pool @@ (id :> [
                type |-> "in",
                state |-> "DownloadPending"
            ])
       /\ UNCHANGED done
    \/ /\ queue' = Append(queue, [
                id |-> id,
                type |-> "SendReply",
                ttl |-> JOB_RETRIES
            ])
       /\ pool' = pool @@ (id :> [
                type |-> "out",
                state |-> "SendPending"
            ])
       /\ UNCHANGED done

\* If `job` isn't expired, we can retry it by resetting Head(queue) to `job`.
Retry(job) ==
    /\ ~IsExpired(job)
    /\ queue' = <<[
        id |-> job.id,
        type |-> job.type,
        ttl |-> job.ttl - 1
        ]>> \o Tail(queue)
    /\ UNCHANGED<<done, pool>>

\* If Head(queue) succeeded, move it to `done` and advance `queue`.
QueueNext ==
    /\ done' = Append(done, Head(queue))
    /\ queue' = Tail(queue)


\* --- REPLY STATES ---
\* These actions reimplement the per-reply state machine first explicated in
\* <https://gist.github.com/cfm/2ca373e7ac5e5397550d7db98289dc3d>.  Each
\* state corresponds to an operator, which evaluates the conditions
\* that govern its possible transitions and then applies one.  A state
\* corresponding to an API job has an equal chance of succeeding versus failing
\* up to JOB_RETRIES times.

DeleteInterrupt(job) ==
    /\ Set(job.id, "DeletedLocally")
    /\ UNCHANGED<<done, queue>>

DeletedLocally(job) ==
    \/ /\ Delete(job.id)
       /\ QueueNext
    \/ Retry(job)
    \/ /\ IsExpired(job)
       /\ QueueNext
       /\ UNCHANGED pool

DownloadPending(job) ==
    /\ Trans(job.id, "DownloadPending", "Downloading")
    /\ UNCHANGED<<done, queue>>

\* DownloadReplyJob in progress:
Downloading(job) ==
    \/ /\ Trans(job.id, "Downloading", "Downloaded")
       /\ UNCHANGED<<done, queue>>
    \/ Retry(job)
    \/ /\ IsExpired(job)
       /\ Trans(job.id, "DownloadPending", "DownloadFailed")
       /\ QueueNext

Downloaded(job) ==
    /\ \/ Trans(job.id, "Downloaded", "Ready")
       \/ Trans(job.id, "Downloaded", "DecryptionFailed")
    /\ QueueNext

SendPending(job) ==
    /\ Trans(job.id, "SendPending", "Sending")
    /\ UNCHANGED<<done, queue>>

\* SendReplyJob in progress:
Sending(job) ==
    \/ /\ Trans(job.id, "Sending", "Ready")
       /\ QueueNext
    \/ Retry(job)
    \/ /\ IsExpired(job)
       /\ Trans(job.id, "Sending", "SendFailed")
       /\ QueueNext


\* ---- ACTIONS ----
\* These actions are the heart of the model: how the per-reply state machine
\* reimplemented above is processed for multiple replies, jobs, and their
\* interactions and failure modes.

vars == <<
    pool, deleting,
    queue, done
    >>

\* Invoked for some reply `id` that has (a) apparently failed to send but (b)
\* been reported by the server for downloading.  See also f0040bc and
\* <https://github.com/freedomofpress/securedrop-client/issues/1493#issuecomment-1130898792>.
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

\* Run the state machine for the reply `id` specified by the current
\* `job` at Head(queue).
ProcessJob ==
    LET job == Head(queue)
    IN
        IF IsAvailable(job.id) THEN
            CASE job \in DownloadReplyJob ->
                \/ DownloadPending(job)
                \/ Downloading(job)
                \/ Downloaded(job)
            [] job \in SendReplyJob ->
                \/ SendPending(job)
                \/ Sending(job)
            [] job \in DeleteJob ->
                \/ DeleteInterrupt(job)
                \/ DeletedLocally(job)
        ELSE
        /\ QueueNext
        /\ UNCHANGED pool

\* Process the queue when non-empty.
QueueRun ==
    \/ /\ queue # <<>>
       /\ ProcessJob
       /\ UNCHANGED deleting
    \/ UNCHANGED vars  \* nothing changes if there's nothing to do


\* ---- MODEL SETUP ----

Init ==
    /\ deleting = {}
    /\ pool = <<>>
    /\ queue = <<>>
    /\ done = <<>>

\* On every tick, do one of the following, with equal probability to maximize
\* the state-space:
Next ==
    \* (a) enqueue the next unprocessed reply enumerated in the constant set
    \* Replies
    \/ \E id \in Replies:
        /\ id = Size(pool)
        /\ Enqueue(id)
        /\ UNCHANGED deleting
    \* (b) (maybe) recover a reply that previously "failed" to send;
    \/ FailureRecovery
    \* (c) run the queue; or
    \/ QueueRun
    \* (d) initiate local or remote deletion from the constant sets
    \* {Local,Reply}Deletion.
    \/ \E id \in ForLocalDeletion: LocalDelete(id)
    \/ \E id \in ForRemoteDeletion: RemoteDelete(id)

\* Putting it all together, we start at Init and execute Next with weak fairness
\* over the set of `vars`.
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)


\* ---- PROPERTIES  ---
\* By marking these operators as "PROPERTIES" in "Reply.cfg", TLA+ will check
\* that they are true over the lifetime of the model run: the Temporal Logic of
\* our Actions (https://learntla.com/core/temporal-logic.html).  As with our
\* invariants, we have one property governing each of our major data structures.

\* It is eventually always (thereafter, without regression) true that all
\* replies are either dead or in a terminal state.
PoolLiveness ==
    <>[](\A r \in Range(pool):
        \/ r \in {DeadReply}
        \/ r.state \in TerminalStates
        )

\* It is eventually always (thereafter, without regression) true that all jobs
\* have been processed.
QueueLiveness == <>[](queue = <<>>)
====
## Appendix

The following property DeletionWins does *not* hold, for example under the
sequence SendReplyJob (fails) --> DeleteJob (succeeds) --> DownloadReplyJob
(succeeds).

ToBeDeleted == ForLocalDeletion \union ForRemoteDeletion

IsDeleted(id) ==
    \/ ~IsAlive(id)
    \/ ~IsAvailable(id)

DeletionWins ==
    <>[](\A id \in ToBeDeleted: IsDeleted(id))