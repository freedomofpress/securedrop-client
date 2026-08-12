import { useState, useEffect, useRef, useCallback, useMemo } from "react";
import { useNavigate } from "react-router";
import { useTranslation } from "react-i18next";
import { Modal, Button } from "antd";

import { useAppDispatch, useAppSelector } from "../hooks";
import {
  selectDeleteModal,
  closeDeleteModal,
  completeDeleteModal,
} from "../features/deleteModal/deleteModalSlice";
import {
  selectSources,
  selectActiveSourceUuid,
  fetchSources,
} from "../features/sources/sourcesSlice";
import { fetchConversation } from "../features/conversation/conversationSlice";
import { PendingEventType } from "../../types";

// Single, top-of-tree delete confirmation modal. Its visibility and target
// sources live in the deleteModal slice, so any component (source list, source
// menu, keyboard shortcut) can open it by dispatching `openDeleteModal`.
function DeleteSourceModal() {
  const { t } = useTranslation("Sidebar");
  const dispatch = useAppDispatch();
  const navigate = useNavigate();

  const { open, pendingSources, loading, counts } =
    useAppSelector(selectDeleteModal);
  const sources = useAppSelector(selectSources);
  const activeSourceUuid = useAppSelector(selectActiveSourceUuid);

  const titleRef = useRef<HTMLHeadingElement | null>(null);

  const pendingCount = pendingSources.length;
  const totalSourceCount = Object.keys(sources).length;
  const allSourcesPendingDelete =
    pendingCount > 0 && pendingCount === totalSourceCount;

  // Require a short countdown before the delete buttons are enabled when a
  // large number of sources is selected, guarding against accidental bulk
  // deletion.
  const shouldCountdown = open && pendingCount > 30;
  const [buttonCountdown, setButtonCountdown] = useState(
    shouldCountdown ? 5 : 0,
  );

  // (Re)start or clear the countdown when the modal opens/closes with a large
  // selection. We adjust state during render (guarded by the previous value)
  // rather than in an effect, so we never commit a frame with a stale
  // countdown. The decrementing timer below is a genuine side effect and stays
  // in an effect.
  const [prevShouldCountdown, setPrevShouldCountdown] =
    useState(shouldCountdown);
  if (shouldCountdown !== prevShouldCountdown) {
    setPrevShouldCountdown(shouldCountdown);
    setButtonCountdown(shouldCountdown ? 5 : 0);
  }

  useEffect(() => {
    if (buttonCountdown <= 0) {
      return;
    }

    const timer = setTimeout(() => {
      setButtonCountdown((prev) => prev - 1);
    }, 1000);

    return () => clearTimeout(timer);
  }, [buttonCountdown]);

  const handleCancel = useCallback(() => {
    dispatch(closeDeleteModal());
  }, [dispatch]);

  const handleDeleteAction = useCallback(
    async (eventType: PendingEventType) => {
      try {
        const events = pendingSources.map((sourceUuid) => {
          const sourceToDelete = sources[sourceUuid];
          return {
            sourceUuid,
            type: eventType,
            data:
              eventType === PendingEventType.SourceConversationTruncated
                ? { upper_bound: sourceToDelete?.lastInteractionCount ?? 0 }
                : undefined,
          };
        });
        await window.electronAPI.addPendingSourceEventBatch(events);
        // If we deleted an account and it was the currently active source, navigate away
        if (
          eventType === PendingEventType.SourceDeleted &&
          activeSourceUuid &&
          pendingSources.includes(activeSourceUuid)
        ) {
          navigate("/");
        }
        // If we deleted a conversation and there's an active source, refresh the conversation
        if (
          eventType === PendingEventType.SourceConversationTruncated &&
          activeSourceUuid
        ) {
          dispatch(fetchConversation(activeSourceUuid));
        }
        // Update local state immediately with projected changes.
        dispatch(fetchSources());
        // Close and signal completion so the source list drops the acted-on
        // sources from its checkbox selection. Visibility pruning handles the
        // "delete account" case (sources leave the store); this also covers
        // "delete conversation", where the source stays.
        dispatch(completeDeleteModal());
      } catch (error) {
        console.error("Failed to delete source(s):", error);
      }
    },
    [pendingSources, sources, activeSourceUuid, navigate, dispatch],
  );

  const title = useMemo(
    () =>
      pendingCount === 1
        ? t("sourcelist.deleteDialog.single.message")
        : t("sourcelist.deleteDialog.multiple.message", {
            count: pendingCount,
          }),
    [pendingCount, t],
  );

  const hasCounts =
    counts.messages > 0 || counts.files > 0 || counts.replies > 0;

  return (
    <Modal
      open={open}
      data-testid="delete-modal"
      closable={false}
      afterOpenChange={(isOpen) => {
        if (isOpen) {
          requestAnimationFrame(() => {
            titleRef.current?.focus();
          });
        }
      }}
      title={
        <h2 data-testid="delete-modal-title" tabIndex={-1} ref={titleRef}>
          {title}
        </h2>
      }
      getContainer={() => document.getElementById("root") || document.body}
      onCancel={handleCancel}
      footer={[
        <Button
          key="cancel"
          data-testid="delete-modal-cancel-button"
          onClick={handleCancel}
        >
          {t("sourcelist.deleteDialog.cancelButton")}
        </Button>,
        <Button
          key="deleteConversation"
          data-testid="delete-modal-delete-conversation-button"
          type="primary"
          disabled={buttonCountdown > 0}
          onClick={() =>
            handleDeleteAction(PendingEventType.SourceConversationTruncated)
          }
        >
          {allSourcesPendingDelete
            ? t("sourcelist.deleteDialog.all.keepAccountsButton")
            : pendingCount === 1
              ? t("sourcelist.deleteDialog.single.keepAccountButton")
              : t("sourcelist.deleteDialog.multiple.keepAccountsButton")}
        </Button>,
        <Button
          key="deleteAccount"
          data-testid="delete-modal-delete-account-button"
          type="primary"
          danger
          disabled={buttonCountdown > 0}
          onClick={() => handleDeleteAction(PendingEventType.SourceDeleted)}
        >
          {allSourcesPendingDelete
            ? t("sourcelist.deleteDialog.all.deleteAccountsButton")
            : pendingCount === 1
              ? t("sourcelist.deleteDialog.single.deleteAccountButton")
              : t("sourcelist.deleteDialog.multiple.deleteAccountsButton")}
        </Button>,
        <span key="countdown" className="text-sm text-gray-500 italic ml-2">
          {buttonCountdown > 0 && `${buttonCountdown}s`}
        </span>,
      ]}
    >
      <div
        data-testid="delete-modal-content"
        data-all-sources-selected={allSourcesPendingDelete}
      >
        <p>{t("sourcelist.deleteDialog.warning")}</p>
        {allSourcesPendingDelete && (
          <p className="font-semibold text-orange-600 mt-2">
            {t("sourcelist.deleteDialog.allSourcesWarning")}
          </p>
        )}
        {loading ? (
          <p className="text-gray-600 italic">
            {t("sourcelist.deleteDialog.countingItems")}
          </p>
        ) : (
          hasCounts && (
            <div className="mt-3">
              <p className="font-medium text-gray-800">
                {t("sourcelist.deleteDialog.itemCountsHeader")}
              </p>
              <ul className="mt-1 ml-4 list-none text-gray-700">
                {counts.messages > 0 && (
                  <li>
                    {t("sourcelist.deleteDialog.messageCount", {
                      count: counts.messages,
                    })}
                  </li>
                )}
                {counts.files > 0 && (
                  <li>
                    {t("sourcelist.deleteDialog.fileCount", {
                      count: counts.files,
                    })}
                  </li>
                )}
                {counts.replies > 0 && (
                  <li>
                    {t("sourcelist.deleteDialog.replyCount", {
                      count: counts.replies,
                    })}
                  </li>
                )}
              </ul>
            </div>
          )
        )}
      </div>
    </Modal>
  );
}

export default DeleteSourceModal;
