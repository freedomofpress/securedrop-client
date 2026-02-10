import { useState, useEffect } from "react";
import { useTranslation } from "react-i18next";
import { Modal, Button } from "antd";
import type { FirstRunStatus } from "../../types";

export function FirstRunPopup() {
  const { t } = useTranslation("FirstRunPopup");
  const [open, setOpen] = useState(false);
  const [status, setStatus] = useState<FirstRunStatus>(null);

  useEffect(() => {
    window.electronAPI.getFirstRunStatus().then((firstRunStatus) => {
      if (firstRunStatus) {
        setStatus(firstRunStatus);
        setOpen(true);
      }
    });
  }, []);

  const handleClose = () => {
    setOpen(false);
  };

  if (!status) {
    return null;
  }

  return (
    <Modal
      open={open}
      onCancel={handleClose}
      getContainer={() => document.getElementById("root") || document.body}
      footer={
        <Button type="primary" onClick={handleClose}>
          {t("ok")}
        </Button>
      }
      title={status === "new_user" ? t("newUser.title") : t("migration.title")}
      width={500}
      centered
    >
      <p>{status === "new_user" ? t("newUser.body") : t("migration.body")}</p>
    </Modal>
  );
}
