import { memo, useMemo } from "react";
import { getInitials } from "../utils";

interface AvatarProps {
  designation: string;
  isActive?: boolean;
  className?: string;
}

const Avatar = memo(function Avatar({
  designation,
  isActive,
  className = "",
}: AvatarProps) {
  const initials = useMemo(() => getInitials(designation), [designation]);

  return (
    <div
      className={`w-10 h-10 rounded-full border flex items-center justify-center font-medium text-sm flex-shrink-0 ${
        isActive
          ? "bg-blue-700 border-blue-700 text-white"
          : "bg-gray-100 border-gray-300 text-gray-600"
      } ${className}`}
    >
      {initials}
    </div>
  );
});

export default Avatar;
