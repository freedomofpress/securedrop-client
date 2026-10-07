import { memo, useCallback, useId, useState, type ReactNode } from "react";
import { useTranslation } from "react-i18next";
import { ChevronDown, ChevronUp } from "lucide-react";

interface ActivitySectionProps {
  title: string;
  testId: string;
  children: ReactNode;
}

const ActivitySection = memo(function ActivitySection({
  title,
  testId,
  children,
}: ActivitySectionProps) {
  const { t } = useTranslation("Sidebar");
  const [open, setOpen] = useState(true);
  const listId = useId();

  const handleToggle = useCallback(() => setOpen((wasOpen) => !wasOpen), []);

  const Chevron = open ? ChevronDown : ChevronUp;

  return (
    <section
      data-testid={testId}
      data-open={open}
      className="sd-border-secondary sd-bg-primary overflow-hidden rounded-lg border"
    >
      <h3>
        <button
          type="button"
          onClick={handleToggle}
          aria-expanded={open}
          aria-controls={listId}
          aria-label={t(
            open
              ? "syncSidebar.section.collapse"
              : "syncSidebar.section.expand",
            { section: title },
          )}
          data-testid={`${testId}-toggle`}
          className="flex w-full cursor-pointer items-center gap-2 px-3 py-2 text-start outline-0 hover:bg-gray-50 focus-visible:outline-2 focus-visible:outline-blue-300 focus-visible:-outline-offset-2"
        >
          <span className="flex-1 text-sm font-semibold">{title}</span>
          <Chevron size={16} strokeWidth={1.5} aria-hidden="true" />
        </button>
      </h3>
      <ul id={listId} hidden={!open} className="flex flex-col">
        {children}
      </ul>
    </section>
  );
});

export default ActivitySection;
