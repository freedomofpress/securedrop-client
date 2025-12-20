# Data syncing / client-side writes

## Summary
Our client and server exchange data in batches, in a sync loop.

## Context
In creating a version 2 of the SecureDrop client, we must specify [how the client writes data](https://github.com/freedomofpress/securedrop-client/issues/2595) to the SecureDrop server. The communication between them must be secure, preserving source anonymity.

Note that the SecureDrop client may be out of contact with the server during some of the time that users are interacting with the client. Pending user interactions – such as replying to or deleting a message – may "pile up" during this time.

## Decision
Our client and server exchange data in batches. The client makes a sync request, transmitting a batch of data for the server's consideration. In response, the client receives a batch of data from the server. Thus the client and server are joined by a single write–read loop. This sync process may be triggered either by a timer or by user interaction.

The client has an "optimistic back end" which handles network delays and failures, allowing the front-end UI to behave as though user interaction was successfully completed. This back end must be idempotent, guaranteeing that a given client's write requests are safe to retry without creating duplicated data. The server needs a consistent mechanism for determining which update(s) to apply in the event of concurrent and conflicting requests. To these ends, clients will generate [Snowflakes](https://en.wikipedia.org/wiki/Snowflake_ID) on each write request to serve as an idempotency key and as a timestamp for the server to perform conflict resolution using LWW (last-write-wins).

The client will store a database table of events not yet accepted or rejected by the server. This is the only table written to upon a user action in the client. Other tables (sources and items) are only updated based on server responses. Thus the server is our authoritative source of truth. In the case of conflict between client and server data, the server always wins.

Here are [detailed diagrams of our implementation](https://github.com/freedomofpress/securedrop/blob/develop/API2.md) of this decision.

## Consequences
This decision introduces a layer of abstraction. It concentrates all sync-related problems in one spot where they must be solved in a generic way, rather than separately. With a single loop between the client and server we intend to avoid race conditions that might arise if there were multiple communication paths. Bulk actions, such as deleting many items, can be handled in a single sync.

## Alternatives considered
We considered an "optimistic front end" which would write local data directly and transmit user interactions immediately, using UI features for real-time feedback and browser features for recovery. This would have been a more direct and visible, less abstracted means of interacting with the server. It would have required a global metadata lock mechanism to avoid race conditions.
