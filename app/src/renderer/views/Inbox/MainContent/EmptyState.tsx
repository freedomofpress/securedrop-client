import emptyStateImage from "../../../../../resources/images/inbox-empty-state.svg";
import "./EmptyState.css";

function EmptyState() {
  return (
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
  );
}

export default EmptyState;
