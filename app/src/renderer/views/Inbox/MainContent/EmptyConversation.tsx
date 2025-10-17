import { useTranslation } from "react-i18next";

import emptyStateImage from "../../../../../resources/images/inbox-empty-state.svg";
import "./EmptyState.css";

function EmptyConversation() {
  const { t } = useTranslation("MainContent");

  return (
    <div className="text-center">
      {/* Empty conversation state */}
      <img src={emptyStateImage} alt="" className="w-32 h-32 mx-auto mb-4" />

      <p className="sd-text-tertiary empty-state-text">
        {t("emptyConversation")}
      </p>
    </div>
  );
}

export default EmptyConversation;
