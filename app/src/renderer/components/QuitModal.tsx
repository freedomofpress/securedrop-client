import { useEffect, useCallback } from "react";
import { Modal } from "antd";
import { useTranslation } from "react-i18next";
import { useAppSelector } from "../hooks";
import { setQuitHandler } from "./quitRequester";

function QuitModal() {
  const { t } = useTranslation("QuitModal");
  const drafts = useAppSelector((state) => state.drafts);
  const [modal, contextHolder] = Modal.useModal();

  const showQuitModal = useCallback(() => {
    modal.confirm({
      getContainer: false,
      autoFocusButton: "ok",
      title: t("title"),
      content: t(
        Object.keys(drafts.drafts).length > 0 ? "withDrafts" : "noDrafts",
      ),
      cancelText: t("cancel"),
      okText: t("ok"),
      onOk() {
        window.electronAPI.quitApp();
      },
      onCancel() {},
    });
  }, [modal, t, drafts.drafts]);

  // Expose showQuitModal for imperative calls (e.g. keyboard shortcut)
  useEffect(() => {
    setQuitHandler(showQuitModal);
    return () => {
      setQuitHandler(null);
    };
  }, [showQuitModal]);

  // Listen for quit-requested IPC from the main process
  useEffect(() => {
    const unsubscribe = window.electronAPI.onQuitRequested(() => {
      showQuitModal();
    });
    return () => {
      unsubscribe();
    };
  }, [showQuitModal]);

  return <>{contextHolder}</>;
}

export default QuitModal;
