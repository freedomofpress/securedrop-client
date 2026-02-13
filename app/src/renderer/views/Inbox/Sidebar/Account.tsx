import { useNavigate } from "react-router";
import { Button, Typography } from "antd";
import { User, LogIn, LogOut, RefreshCw } from "lucide-react";
import { useTranslation } from "react-i18next";

import { useAppDispatch, useAppSelector } from "../../../hooks";
import {
  setUnauth,
  SessionStatus,
} from "../../../features/session/sessionSlice";
import { syncMetadata } from "../../../features/sync/syncSlice";
import { getJournalistById } from "../../../features/journalists/journalistsSlice";
import { formatJournalistName } from "../../../utils";

function Account() {
  const { t } = useTranslation("Sidebar");
  const navigate = useNavigate();
  const session = useAppSelector((state) => state.session);
  const dispatch = useAppDispatch();

  // Get the current journalist
  const currentJournalist = useAppSelector((state) =>
    session.authData?.journalistUUID
      ? getJournalistById(state, session.authData.journalistUUID)
      : undefined,
  );

  // Get the current journalist's display name
  const getCurrentJournalistName = () => {
    if (currentJournalist) {
      return formatJournalistName(currentJournalist.data);
    }
    return t("account.signedIn");
  };

  const signOut = () => {
    console.log("signing out");
    dispatch(setUnauth(undefined));
    navigate("/");
  };

  const signIn = () => {
    console.log("navigating to sign in");
    navigate("/sign-in");
  };

  const sync = () => {
    if (!session.authData) {
      console.warn("Missing authenticated session; skipping sync");
      return;
    }

    console.log("syncing metadata");
    dispatch(syncMetadata(session.authData));
  };

  return (
    <div className="sd-border-secondary sd-bg-primary border-b p-2 h-12 flex items-center justify-between flex-shrink-0">
      {session.status == SessionStatus.Auth ? (
        <>
          <Typography.Text>
            <User size={20} className="mr-1.5 align-top" />
            {getCurrentJournalistName()}
          </Typography.Text>

          <Button
            type="text"
            icon={<RefreshCw size={18} />}
            size="small"
            onClick={sync}
            data-testid="sync-button"
          />

          <Button
            type="dashed"
            icon={<LogOut size={16} />}
            size="small"
            onClick={signOut}
          >
            {t("account.signOut")}
          </Button>
        </>
      ) : (
        <>
          <Typography.Text type="warning">
            {t("account.offlineMode")}
          </Typography.Text>

          <Button
            type="dashed"
            icon={<LogIn size={16} />}
            size="small"
            onClick={signIn}
            data-testid="signin-form-button"
          >
            {t("account.signIn")}
          </Button>
        </>
      )}
    </div>
  );
}

export default Account;
