import { Hexagon } from "lucide-react";
import { memo } from "react";
import { useTranslation } from "react-i18next";
import { useAppSelector } from "../../../../hooks";
import { textDirection } from "../../../../i18n";
import { selectSyncStatus } from "../../../../features/sync/syncSlice";
import { mirrorPlacement } from "../../../../utils";
import { Tooltip } from "antd";

interface HexWithHaloProps {
  color?: string;
  size?: number;
  label?: string;
}

const HexWithHalo = memo(function HexWithHalo({
  color = "green",
  size = 16,
  label = "",
}: HexWithHaloProps) {
  const { t } = useTranslation("Sidebar");
  const direction = textDirection();

  return (
    <Tooltip
      title={t(label)}
      placement={mirrorPlacement("bottomRight", direction)}
    >
      <Hexagon
        style={{ filter: `drop-shadow(0px 0px 2px ${color})` }}
        fill={color}
        color={color}
        size={size}
        strokeWidth={0}
        className="sync-indicator"
        aria-label={t(label)}
        data-testid="sync-indicator"
      />
    </Tooltip>
  );
});

const GrayIcon = () => (
  <HexWithHalo color="gray" label="syncStatus.notloggedin" />
);

const GreenIcon = () => <HexWithHalo color="#0908" label="syncStatus.ok" />;

const AmberIcon = () => (
  <HexWithHalo color="orange" label="syncStatus.warning" />
);

const RedIcon = () => <HexWithHalo color="red" label="syncStatus.error" />;

function SyncDicator() {
  const session = useAppSelector((state) => state.session);
  const syncStatus = useAppSelector(selectSyncStatus);

  if (!session.authData) {
    return <GrayIcon />;
  } else {
    switch (syncStatus) {
      case "not_modified":
        return <GreenIcon />;
      case "updated":
        return <GreenIcon />;
      case "timeout":
        return <AmberIcon />;
      case "error":
        return <AmberIcon />;
      case "forbidden":
        return <RedIcon />;
      default:
        return <></>;
    }
  }
}

export default SyncDicator;
