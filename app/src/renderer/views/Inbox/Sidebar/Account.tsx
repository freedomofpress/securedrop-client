import { useNavigate } from "react-router";
import { Button, Typography } from "antd";
import { UserOutlined, LoginOutlined, LogoutOutlined } from "@ant-design/icons";

import { useAppDispatch, useAppSelector } from "../../../hooks";
import {
  setUnauth,
  SessionStatus,
} from "../../../features/session/sessionSlice";

function Account() {
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

  return (
    <div className="sd-border-secondary sd-bg-primary border-b p-2 h-12 flex items-center justify-between">
      {session.status == SessionStatus.Auth ? (
        <>
          <Typography.Text>
            <UserOutlined style={{ marginRight: 6 }} />
            {session.authData?.journalistFirstName ||
            session.authData?.journalistLastName
              ? `${session.authData?.journalistFirstName || ""} ${session.authData?.journalistLastName || ""}`.trim()
              : "Signed in"}
          </Typography.Text>

          <Button
            type="dashed"
            icon={<LogoutOutlined />}
            size="small"
            onClick={signOut}
          >
            Sign out
          </Button>
        </>
      ) : (
        <>
          <Typography.Text type="warning">Offline Mode</Typography.Text>

          <Button
            type="dashed"
            icon={<LoginOutlined />}
            size="small"
            onClick={signIn}
          >
            Sign in
          </Button>
        </>
      )}
    </div>
  );
}

export default Account;
