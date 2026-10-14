import {
  CircleHelp,
  Eye,
  Reply,
  Star,
  Trash,
  type LucideIcon,
} from "lucide-react";

import {
  EventStatus,
  FetchStatus,
  PendingEventType,
} from "../../../../../types";

// Icon and label key for each kind of queued change. Label keys match the
// PendingEventType values so a row can look its label up by type.
export const EVENT_PRESENTATION: Record<PendingEventType, LucideIcon> = {
  [PendingEventType.ReplySent]: Reply,
  [PendingEventType.ItemDeleted]: Trash,
  [PendingEventType.SourceDeleted]: Trash,
  [PendingEventType.SourceConversationTruncated]: Trash,
  [PendingEventType.Starred]: Star,
  [PendingEventType.Unstarred]: Star,
  [PendingEventType.SourceConversationSeen]: Eye,
  [PendingEventType.Undefined]: CircleHelp,
};

export const eventReasonKey = (status: EventStatus | null): string => {
  switch (status) {
    case EventStatus.BadRequest:
      return "syncSidebar.attentionReason.badRequest";
    case EventStatus.NotFound:
      return "syncSidebar.attentionReason.notFound";
    case EventStatus.Conflict:
      return "syncSidebar.attentionReason.conflict";
    case EventStatus.NotImplemented:
      return "syncSidebar.attentionReason.notImplemented";
    default:
      return "syncSidebar.attentionReason.eventFailed";
  }
};

export const downloadReasonKey = (status: FetchStatus): string => {
  switch (status) {
    case FetchStatus.FailedDownloadRetryable:
      return "syncSidebar.attentionReason.downloadRetrying";
    case FetchStatus.FailedDecryptionRetryable:
      return "syncSidebar.attentionReason.decryptionRetrying";
    default:
      return "syncSidebar.attentionReason.downloadFailed";
  }
};

// Percentage of the ciphertext transferred so far, or null when the server
// never reported a size to divide by.
export const downloadPercent = (
  fetchProgress: number | null,
  size: number | null,
): number | null => {
  if (fetchProgress === null || size === null || size <= 0) {
    return null;
  }
  return Math.min(100, Math.round((fetchProgress / size) * 100));
};
