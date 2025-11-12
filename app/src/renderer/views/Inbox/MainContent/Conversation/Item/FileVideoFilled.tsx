import { memo } from "react";

interface FileVideoFilledProps {
  size?: number;
  color?: string;
  className?: string;
  style?: React.CSSProperties;
}

const FileVideoFilled = memo(function FileVideoFilled({
  size,
  color,
  className,
  style,
}: FileVideoFilledProps) {
  // Support both custom props and Ant Design style prop
  const iconSize = size ?? (style?.fontSize as number) ?? 30;
  const iconColor = color ?? (style?.color as string) ?? "#FF4D4F";

  return (
    <svg
      width={iconSize}
      height={iconSize}
      viewBox="0 0 26 32"
      fill="none"
      xmlns="http://www.w3.org/2000/svg"
      className={className}
    >
      <path
        fillRule="evenodd"
        clipRule="evenodd"
        d="M24.8071 8.025C25.0214 8.23929 25.1429 8.52857 25.1429 8.83214V30.8571C25.1429 31.4893 24.6321 32 24 32H1.14286C0.510715 32 0 31.4893 0 30.8571V1.14286C0 0.510714 0.510715 0 1.14286 0H16.3107C16.6143 0 16.9071 0.121429 17.1214 0.335714L24.8071 8.025ZM22.5071 9.35714L15.7857 2.63571V9.35714H22.5071ZM17.6473 20.6202L9.95058 26.0119C9.76965 26.1387 9.52022 26.0948 9.39347 25.9138C9.34635 25.8466 9.32108 25.7665 9.32108 25.6843V14.9009C9.32108 14.68 9.50017 14.5009 9.72108 14.5009C9.8032 14.5009 9.88332 14.5262 9.95058 14.5733L17.6473 19.965C17.8283 20.0917 17.8722 20.3412 17.7454 20.5221C17.7187 20.5603 17.6855 20.5935 17.6473 20.6202Z"
        fill={iconColor}
      />
    </svg>
  );
});

export default FileVideoFilled;
