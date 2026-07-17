import { memo, useState } from "react";
import {
  FetchStatus,
  ItemUpdateType,
  type Item,
  type ItemUpdate,
  type ReplyMetadata,
} from "../../../../../../types";
import { toTitleCase, formatJournalistName } from "../../../../../utils";
import Avatar from "../../../../../components/Avatar";
import TruncatedText from "../../../../../components/TruncatedText";
import { useTranslation } from "react-i18next";
import {
  Loader2,
  RotateCw,
  Trash,
  Clock,
  Check,
  CheckCheck,
} from "lucide-react";
import DoubleEncryptedBadge from "./DoubleEncryptedBadge";
import { Button, Tooltip, theme } from "antd";
import { ExclamationCircleTwoTone } from "@ant-design/icons";
import {
  getSessionState,
  SessionStatus,
} from "../../../../../features/session/sessionSlice";
import { getJournalistById } from "../../../../../features/journalists/journalistsSlice";
import { useAppSelector } from "../../../../../hooks";
import "../Item.css";
import "./Reply.css";

type ReplySyncState = "pending" | "sent" | "seen";

type MessageProps =
  | {
      kind: "message";
      item: Item;
      designation: string;
      onUpdate: (update: ItemUpdate) => void;
      onDelete: () => void;
      positionInConversation?: number;
      totalConversationItems?: number;
    }
  | {
      kind: "reply";
      item: Item;
      onDelete: () => void;
      positionInConversation?: number;
      totalConversationItems?: number;
    };

const Message = memo(function Message(props: MessageProps) {
  const { kind, item, onDelete } = props;
  const { t } = useTranslation("MainContent");
  const { token } = theme.useToken();
  const [isDeleteFocused, setIsDeleteFocused] = useState(false);
  const showDelete = isDeleteFocused;

  const sessionState = useAppSelector(getSessionState);
  const disableDelete = sessionState.status !== SessionStatus.Auth;

  const replyData = kind === "reply" ? (item.data as ReplyMetadata) : null;
  const syncState: ReplySyncState | null = replyData
    ? replyData.journalist_uuid === ""
      ? "pending"
      : replyData.is_deleted_by_source
        ? "seen"
        : "sent"
    : null;

  const journalist = useAppSelector((state) =>
    replyData && syncState !== "pending"
      ? getJournalistById(state, replyData.journalist_uuid)
      : undefined,
  );

  const retryFetch = () => {
    if (kind !== "message") {
      return;
    }
    props.onUpdate({
      item_uuid: item.uuid,
      type: ItemUpdateType.FetchStatus,
      fetch_status: FetchStatus.DownloadInProgress,
    });
  };

  const getAuthorDisplay = (): string => {
    if (kind === "message") {
      return toTitleCase(props.designation);
    }
    if (syncState === "pending") {
      return t("you");
    }
    if (sessionState.status !== SessionStatus.Auth || !sessionState.authData) {
      return journalist ? formatJournalistName(journalist.data) : t("unknown");
    }
    if (sessionState.authData.journalistUUID === replyData!.journalist_uuid) {
      return t("you");
    }
    return journalist ? formatJournalistName(journalist.data) : t("unknown");
  };

  const getStatusIcon = () => {
    switch (syncState) {
      case "pending":
        return {
          tooltip: t("pendingReplyTooltip"),
          icon: (
            <Clock
              data-testid="pending-reply-icon"
              className="reply-status-icon pending-reply-icon"
              size={14}
            />
          ),
        };
      case "sent":
        return {
          tooltip: t("successReplyTooltip"),
          icon: (
            <Check
              data-testid="sent-reply-icon"
              className="reply-status-icon sent-reply-icon"
              size={14}
            />
          ),
        };
      case "seen":
        return {
          tooltip: t("seenReplyTooltip"),
          icon: (
            <CheckCheck
              data-testid="seen-reply-icon"
              className="reply-status-icon seen-reply-icon"
              size={14}
            />
          ),
        };
      default:
        return null;
    }
  };

  const displayMessage = () => {
    if (item.plaintext) {
      return (
        <>
          <TruncatedText text={item.plaintext} />
          {item.doubleEncryptedKeyFingerprint !== null &&
            kind === "message" && (
              <DoubleEncryptedBadge
                keyFingerprint={item.doubleEncryptedKeyFingerprint!}
              />
            )}
        </>
      );
    }
    switch (item.fetch_status) {
      case FetchStatus.FailedDecryptionRetryable:
      case FetchStatus.FailedDownloadRetryable:
      case FetchStatus.FailedTerminal: {
        let errorMessage = t("messageFailed");
        if (item.fetch_status === FetchStatus.FailedDecryptionRetryable) {
          errorMessage = t("messageDecryptionFailed");
        }
        if (item.fetch_status === FetchStatus.FailedDownloadRetryable) {
          errorMessage = t("messageDownloadFailed");
        }
        return (
          <div className="flex items-center justify-between">
            <div className="flex items-center gap-2">
              <ExclamationCircleTwoTone
                twoToneColor={token.colorError}
                style={{ fontSize: 16 }}
              />
              <span className="italic text-gray-500">{errorMessage}</span>
            </div>
            <Tooltip title={t("retryFetch")}>
              <Button
                type="text"
                size="small"
                icon={<RotateCw size={14} />}
                onClick={retryFetch}
              />
            </Tooltip>
          </div>
        );
      }
      case FetchStatus.Initial:
      case FetchStatus.DownloadInProgress:
        return (
          <span className="italic text-gray-500 flex items-center gap-1">
            <Loader2 size={14} className="animate-spin" />
            {t("itemFetching")}
          </span>
        );
      default:
        return (
          <span className="italic text-gray-500">{t("itemEncrypted")}</span>
        );
    }
  };

  const authorDisplay = getAuthorDisplay();
  const statusIcon = getStatusIcon();
  const positionInConversation = props.positionInConversation;
  const totalConversationItems = props.totalConversationItems;

  const listItemAriaProps =
    positionInConversation && totalConversationItems
      ? {
          role: "listitem" as const,
          "aria-posinset": positionInConversation,
          "aria-setsize": totalConversationItems,
          "aria-label":
            kind === "reply"
              ? t("conversation.replyPositionAriaLabel", {
                  index: positionInConversation,
                  total: totalConversationItems,
                })
              : t("conversation.messagePositionAriaLabel", {
                  index: positionInConversation,
                  total: totalConversationItems,
                }),
        }
      : {};

  if (kind === "message") {
    return (
      <div
        className="flex items-start mb-4 justify-start group"
        data-testid={`item-${item.uuid}`}
        {...listItemAriaProps}
      >
        <Avatar designation={authorDisplay} isActive={false} />
        <div className="ml-3">
          <div className="flex items-center mb-1">
            <span className="author">{authorDisplay}</span>
          </div>
          <div className="flex items-center gap-1">
            <div className="message-box whitespace-pre-wrap overflow-hidden">
              {displayMessage()}
            </div>
            {!disableDelete && (
              <div
                className="flex-shrink-0 transition-opacity group-hover:opacity-100"
                style={{ opacity: showDelete ? 1 : 0 }}
              >
                <Button
                  type="text"
                  size="small"
                  danger
                  icon={<Trash size={16} />}
                  onClick={onDelete}
                  aria-label={t("deleteMessage")}
                  onFocus={() => setIsDeleteFocused(true)}
                  onBlur={() => setIsDeleteFocused(false)}
                />
              </div>
            )}
          </div>
        </div>
      </div>
    );
  }

  return (
    <div
      className="flex items-start mb-4 justify-end group"
      data-testid={`item-${item.uuid}`}
      {...listItemAriaProps}
    >
      <div>
        <div className="flex items-center justify-start mb-1 gap-1">
          <span className="author reply-author">{authorDisplay}</span>
        </div>
        <div className="flex items-center gap-1">
          {!disableDelete && (
            <div
              className="flex-shrink-0 transition-opacity group-hover:opacity-100"
              style={{ opacity: showDelete ? 1 : 0 }}
            >
              <Button
                type="text"
                size="small"
                danger
                icon={<Trash size={16} />}
                onClick={onDelete}
                aria-label={t("deleteReply")}
                onFocus={() => setIsDeleteFocused(true)}
                onBlur={() => setIsDeleteFocused(false)}
              />
            </div>
          )}
          <div className="reply-box whitespace-pre-wrap overflow-hidden relative with-status-icon">
            {displayMessage()}
            {statusIcon && (
              <Tooltip
                title={statusIcon.tooltip}
                placement="topRight"
                styles={{ root: { position: "fixed" } }}
              >
                {statusIcon.icon}
              </Tooltip>
            )}
          </div>
        </div>
      </div>
    </div>
  );
});

export default Message;
