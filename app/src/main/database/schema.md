## Source lifecycle versus `pending_events.source_uuid` foreign-key relationship

A source must exist locally before other events (including deletion) can be
created for it.

All events (including deletion) for a source will be deleted when the source is
deleted.

```mermaid
sequenceDiagram

box client database
participant sources
participant items
participant pending_events
end
participant server

server ->> sources: uuid
activate sources

Note over sources: ...
activate pending_events
pending_events -->> server: DeleteSource(uuid)
server ->> sources: DeleteSource(uuid)
deactivate sources
sources ->> pending_events: ON DELETE CASCADE
deactivate pending_events
```

## Item lifecycle versus `pending_events.item_uuid` foreign-key relationship

An item must exist locally (including via `ReplySent`) before other events
(including deletion) can be created for it.

All events (including deletion) for an item will be deleted when the item is
deleted.

```mermaid
sequenceDiagram

box client database
participant sources
participant items
participant pending_events
end
participant server

opt reply sent
pending_events -->> server: ReplySent(uuid)
server ->> pending_events: ReplySent(uuid)
end

server ->> items: uuid
activate items

Note over items: ...
activate pending_events
pending_events -->> server: DeleteItem(uuid)
server ->> items: DeleteItem(uuid)
deactivate items
items ->> pending_events: ON DELETE CASCADE
deactivate pending_events
```
