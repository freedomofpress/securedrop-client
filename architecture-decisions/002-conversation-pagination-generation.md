# Conversation pagination generation

## Summary

Historical conversation traversal is bound to a database generation. If item ordering
or membership changes between pages, the database returns a fresh first page and the
renderer replaces the old traversal.

## Context

Conversation pages use `(interaction_count, uuid)` as a descending keyset cursor. The
cursor is complete for a stable dataset, but an unloaded item can become unreachable
if synchronization raises its interaction count above the cursor between page reads.
Local pending replies, item deletions, and conversation truncation can also change the
projected pagination dataset outside a metadata sync.

## Decision

SQLite triggers maintain one persisted generation for changes that can alter item
cursor order or membership. Item inserts and deletes advance it. Updates advance it
only when the physical UUID, metadata source UUID, or metadata interaction count
changes. Membership-changing pending events also advance it. Seen, read-state,
fetch-status, fetch-progress, and other metadata-only updates do not advance it because
they leave the cursor dataset unchanged.

Every page returns its generation. A continuation sends that generation with its
cursor. The database reads the generation and page in one transaction. On a mismatch,
it ignores the cursor and returns the current first page with a restart marker. The
renderer replaces its loaded items for that source and can continue from the new page.
Each renderer navigation starts a traversal epoch, and each continuation records its
request identity and requested generation. A continuation can merge or replace state
only while that source, epoch, request, and generation relationship are still current.
Stale continuations perform no seen write or source refresh; opening the conversation
already marks through the maximum interaction count, which covers every older page.

The generation is global rather than per source. A mutation in another source can
therefore cause an unnecessary restart, but it avoids per-source generation lifecycle
and trigger logic while preserving correctness.

## Rejected alternative

Making each item's `(interaction_count, uuid)` tuple immutable would keep cursors
stable, but `interaction_count` is authoritative server metadata that can be corrected
during sync. Rejecting such an update would abort a batch or retain stale metadata and
would require conflict and restart behavior at the sync boundary. Restarting a
generation-bound traversal preserves server authority and confines recovery to the UI
read path.
