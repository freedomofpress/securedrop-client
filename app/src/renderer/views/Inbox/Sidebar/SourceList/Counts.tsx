import { memo, useMemo } from "react";
import { useTranslation } from "react-i18next";

interface CountsProps {
  totalCount: number;
  visibleCount: number;
  selectedCount: number;
  isFiltered: boolean;
}

const Counts = memo(function Counts({
  totalCount,
  visibleCount,
  selectedCount,
  isFiltered,
}: CountsProps) {
  const { t } = useTranslation("Sidebar");

  const text = useMemo(() => {
    const parts = [t("sourcelist.counts.total", { count: totalCount })];
    if (isFiltered) {
      parts.push(t("sourcelist.counts.visible", { count: visibleCount }));
    }
    if (selectedCount > 0) {
      parts.push(t("sourcelist.counts.selected", { count: selectedCount }));
    }
    return parts.join(", ");
  }, [t, totalCount, visibleCount, selectedCount, isFiltered]);

  return (
    <div className="px-4 py-2 text-xs text-gray-500 border-t border-gray-100 flex-shrink-0">
      {text}
    </div>
  );
});

export default Counts;
