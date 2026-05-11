import { useEffect, useState } from "react";
import { Modal } from "antd";
import { useTranslation } from "react-i18next";
import { useAppSelector } from "../hooks";
import { setQuitHandler } from "./quitRequester";

function QuitModal() {
  const { t } = useTranslation("QuitModal");
  const drafts = useAppSelector((state) => state.drafts);
  const [visible, setVisible] = useState(false);
  const hasDrafts = Object.keys(drafts.drafts).length > 0;

  // Expose showQuitModal for imperative calls (e.g. keyboard shortcut)
  useEffect(() => {
    setQuitHandler(() => setVisible(true));
    return () => {
      setQuitHandler(null);
    };
  }, [setVisible]);

  // Listen for quit-requested IPC from the main process
  useEffect(() => {
    const unsubscribe = window.electronAPI.onQuitRequested(() => {
      setVisible(true);
    });
    return () => {
      unsubscribe();
    };
  }, [setVisible]);

  return (
    <Modal
      open={visible}
      getContainer={false}
      title={t("title")}
      okText={t(hasDrafts ? "discardAndQuit" : "Quit")}
      okButtonProps={{ autoFocus: true }}
      cancelText={t("goBack")}
      onOk={() => {
        window.electronAPI.quitApp();
      }}
      onCancel={() => setVisible(false)}
    >
      {hasDrafts ? t("withDrafts") : ""}
    </Modal>
  );
}

export default QuitModal;
