import emptyStateImage from "../../../resources/images/inbox-empty-state.svg";
import "./MainContent.css";

function MainContent() {
  return (
    <div className="flex-1 flex flex-col h-full">
      <div className="bg-white border-b border-gray-200 h-12">
        {/* Empty header for now */}
      </div>

      <div className="flex-1 flex items-center justify-center main-content-background">
        <div className="text-center">
          {/* Empty state */}
          <img
            src={emptyStateImage}
            alt="Empty inbox"
            className="w-32 h-32 mx-auto mb-4"
          />

          <p className="empty-state-text">
            <strong>Select a source</strong> from the list to read messages,
            retrieve files, or send responses.
          </p>
        </div>
      </div>
    </div>
  );
}

export default MainContent;
