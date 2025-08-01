import type { Item } from "../../../../../../types";
import { toTitleCase } from "../../../../../utils";
import Avatar from "../../../../../components/Avatar";
import "../Item.css";

interface FileProps {
  item: Item;
  designation: string;
}

function File({ item, designation }: FileProps) {
  const titleCaseDesignation = toTitleCase(designation);

  // TODO: Handle file content. For now, skip localization
  const fileContent = item.filename
    ? `Attachment: ${item.filename}`
    : "Attachment";

  return (
    <div
      className="flex items-start mb-4 justify-start"
      data-testid={`item-${item.uuid}`}
    >
      <Avatar designation={titleCaseDesignation} isActive={false} />
      <div className="ml-3">
        <div className="flex items-center mb-1">
          <span className="author">{titleCaseDesignation}</span>
        </div>
        <div className="bg-gray-50 border border-gray-200 rounded-lg px-4 py-2 text-gray-700 max-w-xl italic">
          {fileContent}
        </div>
      </div>
    </div>
  );
}

export default File;
