import { Trans } from "react-i18next";

import emptyStateImage from "../../../../../resources/images/inbox-empty-state.svg";
import "./EmptyState.css";

function EmptyState() {
  return (
    <div className="text-center">
      {/* Empty state */}
      <img src={emptyStateImage} alt="" className="w-32 h-32 mx-auto mb-4" />

      <p className="sd-text-tertiary empty-state-text">
        <Trans
          ns="MainContent"
          i18nKey="emptyState"
          components={{
            bold: <strong />,
          }}
        />
      </p>
    </div>
  );
}

export default EmptyState;
