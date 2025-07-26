import emptyStateImage from "../../../../resources/images/inbox-empty-state.svg";
import "./MainContent.css";

function MainContent() {
  return (
    <div className="flex-1 flex flex-col h-full">
      <div className="sd-bg-primary sd-border-secondary border-b h-12">
        {/* Empty header for now */}
      </div>

      <div className="flex-1 flex items-center justify-center sd-bg-secondary">
        <div className="text-center">
          {/* Empty state */}
          <img
            src={emptyStateImage}
            alt="Empty inbox"
            className="w-32 h-32 mx-auto mb-4"
          />

          <p className="sd-text-tertiary empty-state-text">
            <strong>Select a source</strong> from the list to read messages,
            retrieve files, or send responses.
          </p>
        </div>
      </div>
    </div>
  );
}

export default MainContent;
