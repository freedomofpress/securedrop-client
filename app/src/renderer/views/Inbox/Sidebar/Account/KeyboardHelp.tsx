import { useTranslation } from "react-i18next";

// Keyboard Shortcuts Modal Content
function KeyboardHelp() {
  const { t } = useTranslation("Sidebar");

  // TODO: This should be generated from actual defined shortcuts
  const shortcuts = [
    {
      heading: "Composing",
      items: [
        { desc: "Send reply", keys: [["Ctrl", "Enter"]] },
        { desc: "Discard draft and close compose", keys: [["Esc"]] },
      ],
    },
    {
      heading: "Files",
      items: [
        { desc: "Download all files in conversation", keys: [["Ctrl", "D"]] },
      ],
    },
    {
      heading: "Sources",
      items: [
        { desc: "Delete selected sources", keys: [["Ctrl", "Delete"]] },
        { desc: "Focus source search", keys: [["Ctrl", "F"]] },
      ],
    },
    {
      heading: "Navigation",
      items: [
        { desc: "Next source", keys: [["↓"]] },
        { desc: "Previous source", keys: [["↑"]] },
        { desc: "Move focus forward", keys: [["Tab"]] },
        { desc: "Move focus backward", keys: [["Shift", "Tab"]] },
      ],
    },
    {
      heading: "Application",
      items: [{ desc: "Quit SecureDrop", keys: [["Ctrl", "Q"]] }],
    },
  ];

  const renderKeys = (keyGroups: string[][]) => {
    return keyGroups.map((chord, ci) => (
      <span key={ci} className="flex items-center gap-[4px]">
        {chord.map((key, i) => (
          <span key={i} className="flex items-center gap-[4px]">
            <kbd className="inline-flex items-center justify-center min-w-[28px] h-[24px] px-[7px] bg-[#fafafa] border border-[#d9d9d9] border-b-2 rounded-[5px] text-[12px] font-mono font-medium text-[#181d27] leading-none shadow-[0_1px_1px_rgba(0,0,0,0.06)] select-none whitespace-nowrap">
              {key}
            </kbd>
            {i < chord.length - 1 && (
              <span className="text-[11px] text-[#8c8c8c] leading-none">+</span>
            )}
          </span>
        ))}
      </span>
    ));
  };

  return (
    <>
      {/* Header */}
      <div className="flex items-center gap-[8px] px-[24px] pt-[16px] pb-[12px] border-b border-[#f0f0f0]">
        {/* Keyboard icon */}
        <span className="text-[16px] font-semibold text-[#181d27]">
          {t("help.keyboardShortcutsTitle")}
        </span>
      </div>

      {/* Body */}
      <div className="px-[24px] pt-[16px] pb-[4px]">
        {shortcuts.map((group, gi) => (
          <div key={gi}>
            <div
              className={`text-[11px] font-bold uppercase tracking-[0.06em] text-[#8c8c8c] mb-[2px] ${gi > 0 ? "mt-[4px]" : ""}`}
            >
              {group.heading}
            </div>
            {group.items.map((item, ii) => (
              <div
                key={ii}
                className="flex items-center justify-between py-[5px]"
              >
                <span className="text-[13px] text-[#414651]">{item.desc}</span>
                <div className="flex items-center gap-[4px] shrink-0">
                  {renderKeys(item.keys)}
                </div>
              </div>
            ))}
            {gi < shortcuts.length - 1 && (
              <div className="h-[1px] bg-[#f0f0f0] my-[8px]"></div>
            )}
          </div>
        ))}
      </div>
    </>
  );
}

export default KeyboardHelp;
