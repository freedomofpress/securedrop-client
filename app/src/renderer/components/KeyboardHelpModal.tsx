import { useEffect, useCallback, useState } from "react";
import { Modal, Button } from "antd";
import { useTranslation } from "react-i18next";
import { setHelpHandler } from "./helpRequester";
import KeyboardHelp from "../views/Inbox/Sidebar/Account/KeyboardHelp";

function KeyboardHelpModal() {
  const { t } = useTranslation("Sidebar");
  const [isOpen, setIsOpen] = useState(false);

  const showModal = useCallback(() => {
    setIsOpen(true);
  }, []);

  useEffect(() => {
    setHelpHandler(showModal);
    return () => {
      setHelpHandler(null);
    };
  }, [showModal]);

  return (
    <Modal
      getContainer={() => document.getElementById("root") || document.body}
      wrapClassName="about-modal-container"
      className="about-modal-content"
      title=""
      closable={false}
      open={isOpen}
      onCancel={() => setIsOpen(false)}
      footer={[
        <Button key="back" onClick={() => setIsOpen(false)} type="primary">
          {t("account.aboutClose")}
        </Button>,
      ]}
    >
      <KeyboardHelp />
    </Modal>
  );
}

export default KeyboardHelpModal;
