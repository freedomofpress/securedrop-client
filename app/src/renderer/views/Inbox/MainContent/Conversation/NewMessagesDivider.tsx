import { forwardRef } from "react";
import { useTranslation } from "react-i18next";
import { Button } from "antd";
import "./NewMessagesDivider.css";

const NewMessagesDivider = forwardRef<HTMLDivElement>((_, ref) => {
  const { t } = useTranslation("MainContent");

  return (
    <div
      ref={ref}
      className="new-messages-divider"
      data-testid="new-messages-divider"
      role="separator"
      aria-label={t("conversation.newMessagesDivider")}
    >
      <span className="new-messages-divider__line" aria-hidden="true" />
      <Button
        type="default"
        size="small"
        disabled
        className="new-messages-divider__button"
      >
        {t("conversation.newMessagesDivider")}
      </Button>
      <span className="new-messages-divider__line" aria-hidden="true" />
    </div>
  );
});

NewMessagesDivider.displayName = "NewMessagesDivider";

export default NewMessagesDivider;
