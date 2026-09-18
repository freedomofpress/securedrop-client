import { memo, useCallback, useRef, useState } from "react";
import { Alert, Button, Modal, Radio, Space } from "antd";
import type { RadioChangeEvent } from "antd";
import { TriangleAlert } from "lucide-react";
import { Trans, useTranslation } from "react-i18next";

import { PendingEventType, type SourceItemCounts } from "../../types";

// Which of the two deletions the user has chosen. Kept separate from
// PendingEventType so the radio state is independent of the event we dispatch.
type DeletionScope = "conversation" | "account";

const DEFAULT_SCOPE: DeletionScope = "conversation";

interface DeleteSourceModalProps {
  open: boolean;
  // How many sources are targeted for deletion.
  sourceCount: number;
  // Designation of the single targeted source, if there is exactly one.
  designation?: string;
  counts: SourceItemCounts;
  // True while the item counts are still being fetched.
  loading: boolean;
  // True when every source in the inbox is targeted.
  allSourcesSelected: boolean;
  // Seconds remaining before the delete button unlocks (0 = unlocked).
  countdown: number;
  onConfirm: (eventType: PendingEventType) => void;
  onCancel: () => void;
}

const DeleteSourceModal = memo(function DeleteSourceModal({
  open,
  sourceCount,
  designation,
  counts,
  loading,
  allSourcesSelected,
  countdown,
  onConfirm,
  onCancel,
}: DeleteSourceModalProps) {
  const { t } = useTranslation("Sidebar");
  const titleRef = useRef<HTMLHeadingElement | null>(null);
  const [scope, setScope] = useState<DeletionScope>(DEFAULT_SCOPE);
  const [wasOpen, setWasOpen] = useState(open);

  // Always reopen on the least destructive option: a sticky "account" choice
  // would let one deletion's intent carry silently into the next. This is the
  // "adjust state while rendering" pattern rather than an effect, so the reset
  // lands in the same render that opens the modal.
  if (open !== wasOpen) {
    setWasOpen(open);
    if (open) {
      setScope(DEFAULT_SCOPE);
    }
  }

  const handleScopeChange = useCallback((e: RadioChangeEvent) => {
    setScope(e.target.value as DeletionScope);
  }, []);

  const handleConfirm = useCallback(() => {
    onConfirm(
      scope === "account"
        ? PendingEventType.SourceDeleted
        : PendingEventType.SourceConversationTruncated,
    );
  }, [onConfirm, scope]);

  const isSingle = sourceCount === 1;

  const title =
    isSingle && designation
      ? t("sourcelist.deleteDialog.titleWithDesignation", { designation })
      : t("sourcelist.deleteDialog.title", { count: sourceCount });

  // The "this will delete" list. On the account branch the source accounts
  // themselves are the first thing deleted, so they lead the list.
  const itemLines = [
    ...(scope === "account"
      ? [
          t("sourcelist.deleteDialog.sourceAccountCount", {
            count: sourceCount,
          }),
        ]
      : []),
    ...(counts.messages > 0
      ? [t("sourcelist.deleteDialog.messageCount", { count: counts.messages })]
      : []),
    ...(counts.files > 0
      ? [t("sourcelist.deleteDialog.fileCount", { count: counts.files })]
      : []),
    ...(counts.replies > 0
      ? [t("sourcelist.deleteDialog.replyCount", { count: counts.replies })]
      : []),
  ];

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
      onCancel={onCancel}
      footer={[
        <Button
          key="cancel"
          data-testid="delete-modal-cancel-button"
          onClick={onCancel}
        >
          {t("sourcelist.deleteDialog.cancelButton")}
        </Button>,
        <Button
          key="confirm"
          data-testid="delete-modal-confirm-button"
          type="primary"
          danger
          disabled={countdown > 0}
          onClick={handleConfirm}
        >
          {t("sourcelist.deleteDialog.confirmButton")}
        </Button>,
        <span key="countdown" className="text-sm text-gray-500 italic ms-2">
          {countdown > 0 && `${countdown}s`}
        </span>,
      ]}
    >
      <div
        data-testid="delete-modal-content"
        data-all-sources-selected={allSourcesSelected}
      >
        <p>
          <Trans
            ns="Sidebar"
            i18nKey="sourcelist.deleteDialog.body.account"
            count={sourceCount}
            components={{ bold: <strong /> }}
          />
        </p>
        <p>
          {t("sourcelist.deleteDialog.body.accountEffect", {
            count: sourceCount,
          })}
        </p>
        <p>
          <Trans
            ns="Sidebar"
            i18nKey="sourcelist.deleteDialog.body.conversation"
            count={sourceCount}
            components={{ bold: <strong /> }}
          />
        </p>

        {/* The spacing lives on this wrapper, not on Radio.Group: antd's
            CSS-in-JS is unlayered and resets the group's margin to 0, which
            beats Tailwind v4's layered utilities. Space is antd's documented
            way to stack the options vertically, for the same reason. */}
        <div className="my-6">
          <Radio.Group
            aria-label={t("sourcelist.deleteDialog.scopeLabel")}
            value={scope}
            onChange={handleScopeChange}
          >
            <Space direction="vertical" size="middle">
              <Radio
                value="conversation"
                data-testid="delete-modal-scope-conversation"
              >
                {t("sourcelist.deleteDialog.scopeConversation", {
                  count: sourceCount,
                })}
              </Radio>
              <Radio value="account" data-testid="delete-modal-scope-account">
                {t("sourcelist.deleteDialog.scopeAccount", {
                  count: sourceCount,
                })}
              </Radio>
            </Space>
          </Radio.Group>
        </div>

        {/* Gap goes on the container: a margin utility on the Alerts would lose
            to antd's unlayered reset, same as on Radio.Group above. */}
        <div className="flex flex-col gap-3">
          {allSourcesSelected && (
            <Alert
              data-testid="delete-modal-all-sources-warning"
              type="error"
              showIcon
              message={t("sourcelist.deleteDialog.allSourcesWarning")}
            />
          )}

          <Alert
            data-testid="delete-modal-item-counts"
            type="warning"
            showIcon
            // antd's default warning icon is a filled circle; the design calls
            // for an outlined triangle.
            icon={<TriangleAlert size={20} />}
            message={
              loading
                ? t("sourcelist.deleteDialog.countingItems")
                : t("sourcelist.deleteDialog.itemCountsHeader")
            }
            description={
              loading ? undefined : (
                <ul className="list-none">
                  {itemLines.length > 0 ? (
                    itemLines.map((line) => <li key={line}>{line}</li>)
                  ) : (
                    <li>{t("sourcelist.deleteDialog.noItems")}</li>
                  )}
                </ul>
              )
            }
          />
        </div>
      </div>
    </Modal>
  );
});

export default DeleteSourceModal;
