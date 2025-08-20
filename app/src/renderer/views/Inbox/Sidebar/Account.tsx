import { useNavigate } from "react-router";
import { Button, Typography } from "antd";
import { User, LogIn, LogOut, RefreshCw } from "lucide-react";
import { useTranslation } from "react-i18next";

import { useAppDispatch, useAppSelector } from "../../../hooks";
import {
  setUnauth,
  SessionStatus,
} from "../../../features/session/sessionSlice";

function Account() {
  const { t } = useTranslation("Sidebar");
  const navigate = useNavigate();
  const session = useAppSelector((state) => state.session);
  const dispatch = useAppDispatch();

  const signOut = () => {
    console.log("signing out");
    dispatch(setUnauth());
    navigate("/");
  };

  const signIn = () => {
    console.log("navigating to sign in");
    navigate("/sign-in");
  };

  const sync = () => {
    console.log("syncing metadata");
    window.electronAPI.syncMetadata({
      authToken: session.authData?.token,
    });
  };

  return (
    <div className="sd-border-secondary sd-bg-primary border-b p-2 h-12 flex items-center justify-between flex-shrink-0">
      {session.status == SessionStatus.Auth ? (
        <>
          <Typography.Text>
            <User size={20} style={{ marginRight: 6, verticalAlign: "top" }} />
            {session.authData?.journalistFirstName ||
            session.authData?.journalistLastName
              ? `${session.authData?.journalistFirstName || ""} ${session.authData?.journalistLastName || ""}`.trim()
              : "Signed in"}
          </Typography.Text>

          <Button icon={<RefreshCw />} size="small" onClick={sync} />

          <Button
            type="dashed"
            icon={<LogOut size={16} style={{ verticalAlign: "middle" }} />}
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
            icon={<LogIn size={16} style={{ verticalAlign: "middle" }} />}
            size="small"
            onClick={signIn}
          >
            {t("account.signIn")}
          </Button>
        </>
      )}
    </div>
  );
}

export default Account;
