import { Hexagon } from "lucide-react";
import { memo } from 'react';
import { useAppSelector } from "../../../../hooks";
import { selectSyncStatus } from "../../../../features/sync/syncSlice";

const HexWithHalo = memo(({ color = "green", size = 16 }) => {
  return (
    <Hexagon
      style={{ filter: `drop-shadow(0px 0px 2px ${color})` }}
      fill={color}
      color={color}
      size={size}
      strokeWidth={0}
    />
  );
});

const GrayIcon = () => <HexWithHalo color="gray" />;
const GreenIcon = () => <HexWithHalo color="#0908" />;
const AmberIcon = () => <HexWithHalo color="orange" />;
const RedIcon = () => <HexWithHalo color="red" />;

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
