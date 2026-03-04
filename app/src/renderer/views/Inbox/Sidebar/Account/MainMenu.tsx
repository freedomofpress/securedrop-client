import { useNavigate } from "react-router";
import { memo, useState } from "react";
import { useTranslation } from "react-i18next";
import { Typography, Space, Modal, MenuProps, Dropdown } from "antd";
import { ChevronDown, ChevronUp, User } from "lucide-react";

import { useAppDispatch, useAppSelector } from "../../../../hooks";
import { setUnauth } from "../../../../features/session/sessionSlice";
import { getJournalistById } from "../../../../features/journalists/journalistsSlice";
import { syncMetadata } from "../../../../features/sync/syncSlice";
import { formatJournalistName } from "../../../../utils";

const MainMenu = memo(function MainMenu() {
  const { t } = useTranslation("Sidebar");

  const navigate = useNavigate();
  const session = useAppSelector((state) => state.session);
  const dispatch = useAppDispatch();
  const confirm = Modal.confirm;

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

  // a little flair for the menu state - used to flip chevron when it's open
  const [isOpen, setIsOpen] = useState(false);

  const handleOpenState = (open: boolean) => {
    setIsOpen(open);
  };

  // menu action functions
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

  const closeApp = () => {
    confirm({
      title: t("account.quitModalTitle"),
      content: t("account.quitModalContent"),
      cancelText: t("account.quitModalCancel"),
      okText: t("account.quitModalOK"),
      onOk() {
        console.log("Closing application");
        window.electronAPI.quitApp();
      },
      onCancel() {
        console.log("Cancelling application close");
      },
    });

    return;
  };

  const handleMenuClick: MenuProps["onClick"] = async (e) => {
    switch (e.key) {
      case "signOut":
        signOut();
        break;
      case "signIn":
        signIn();
        break;
      case "syncNow":
        sync();
        break;
      case "closeApp":
        closeApp();
        break;
      default:
        console.warn(`Undefined menu key: ${e.key}`);
        break;
    }
  };

  const items: MenuProps["items"] = [
    {
      key: "syncNow",
      label: t("account.syncNow"),
      extra: "Ctrl+R",
      disabled: !session.authData,
    },
    {
      type: "divider",
    },
    {
      key: "aboutSubMenu",
      label: t("account.Help"),
      children: [
        {
          key: "helpHelp",
          label: t("account.getHelp"),
        },
        {
          key: "helpKeys",
          label: t("account.keyboardShortcuts"),
        },
        {
          key: "helpAbout",
          label: t("account.aboutSecureDrop"),
        },
      ],
    },
    {
      type: "divider",
    },

    session.authData
      ? {
          key: "signOut",
          label: t("account.signOut"),
          extra: "Ctrl+Shift+O",
        }
      : {
          key: "signIn",
          label: t("account.signIn"),
          extra: "Ctrl+Shift+I",
        },

    {
      key: "closeApp",
      label: t("account.Quit"),
      extra: "Ctrl+Shift+Q",
    },
  ];

  const menuProps = {
    items,
    onClick: handleMenuClick,
  };

  return (
    <>
      <Dropdown
        menu={menuProps}
        trigger={["click"]}
        onOpenChange={handleOpenState}
        open={isOpen}
      >
        <a onClick={(e) => e.preventDefault()}>
          <Space>
            {session.authData ? (
              <>
                <User />
                <Typography.Text>{getCurrentJournalistName()}</Typography.Text>
              </>
            ) : (
              <>
                <User color="#c0c0c0" />
                <Typography.Text type="warning">
                  {t("account.offlineMode")}
                </Typography.Text>
              </>
            )}
            {isOpen ? <ChevronUp size="16" /> : <ChevronDown size="16" />}
          </Space>
        </a>
      </Dropdown>
    </>
  );
});

export default MainMenu;
