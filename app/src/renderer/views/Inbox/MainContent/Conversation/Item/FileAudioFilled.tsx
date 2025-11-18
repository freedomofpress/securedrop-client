import { memo } from "react";

interface FileAudioFilledProps {
  size?: number;
  color?: string;
  className?: string;
  style?: React.CSSProperties;
}

const FileAudioFilled = memo(function FileAudioFilled({
  size,
  color,
  className,
  style,
}: FileAudioFilledProps) {
  // Support both custom props and Ant Design style prop
  const iconSize = size ?? (style?.fontSize as number) ?? 30;
  const iconColor = color ?? (style?.color as string) ?? "#8C8C8C";

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
        d="M24.8071 8.025C25.0214 8.23929 25.1429 8.52857 25.1429 8.83214V30.8571C25.1429 31.4893 24.6321 32 24 32H1.14286C0.510715 32 0 31.4893 0 30.8571V1.14286C0 0.510714 0.510715 0 1.14286 0H16.3107C16.6143 0 16.9071 0.121429 17.1214 0.335714L24.8071 8.025ZM18.0346 14.2243C18.0571 14.303 18.0684 14.3844 18.0684 14.4662V16.1549C18.0683 16.5473 17.8081 16.8921 17.4308 17.0001L13.2311 18.1997V23.4144C13.2312 25.0734 11.9164 26.4341 10.2583 26.4909L10.1528 26.4927C8.82675 26.4927 7.64976 25.6434 7.23164 24.385C6.81353 23.1266 7.24827 21.7418 8.31062 20.9482C9.37297 20.1546 10.8242 20.1305 11.9123 20.8884L11.9118 15.4987H11.9404C12.0195 15.1984 12.2512 14.962 12.5499 14.8769L16.9475 13.6201C17.4146 13.4868 17.9012 13.7573 18.0346 14.2243ZM15.7857 2.63571L22.5071 9.35714H15.7857V2.63571Z"
        fill={iconColor}
      />
    </svg>
  );
});

export default FileAudioFilled;
