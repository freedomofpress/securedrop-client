import { getInitials } from "../utils";

interface AvatarProps {
  designation: string;
  isActive?: boolean;
}

function Avatar({ designation, isActive }: AvatarProps) {
  const initials = getInitials(designation);

  return (
    <div
      className={`w-10 h-10 rounded-full border flex items-center justify-center font-medium text-sm flex-shrink-0 ${
        isActive
          ? "bg-blue-700 border-blue-700 text-white"
          : "bg-gray-100 border-gray-300 text-gray-600"
      }`}
    >
      {initials}
    </div>
  );
}

export default Avatar;
