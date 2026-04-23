import { useNavigate } from "react-router";
import { useState } from "react";
import { useTranslation } from "react-i18next";
import { Typography, Space, Modal, MenuProps, Dropdown, Button } from "antd";
import {
  RefreshCw,
  CircleQuestionMark,
  LogIn,
  LogOut,
  ChevronDown,
  ChevronUp,
  Power,
} from "lucide-react";

import { useAppDispatch, useAppSelector } from "../../../../hooks";
import { setUnauth } from "../../../../features/session/sessionSlice";
import { getJournalistById } from "../../../../features/journalists/journalistsSlice";
import { syncMetadata } from "../../../../features/sync/syncSlice";
import SyncDicator from "./SyncDicator";
import AboutHelp from "./AboutHelp";
import { requestQuit } from "../../../../components/quitRequester";
import { requestHelp } from "../../../../components/helpRequester";
import {
  getShortcut,
  formatDisplayKeys,
} from "../../../../shortcuts/shortcutDefinitions";

function MainMenu() {
  const { t } = useTranslation("Sidebar");

  const navigate = useNavigate();
  const session = useAppSelector((state) => state.session);
  const dispatch = useAppDispatch();
  const [isAboutModalOpen, setIsAboutModalOpen] = useState<boolean>(false);
  const [aboutModalContent, setAboutModalContent] =
    useState<React.ReactNode>(null);

  const aboutContent = <AboutHelp />;

  const showAboutModal = (content: React.ReactNode) => {
    setAboutModalContent(content);
    setIsAboutModalOpen(true);
  };

  // Get the current journalist
  const currentJournalist = useAppSelector((state) =>
    session.authData?.journalistUUID
      ? getJournalistById(state, session.authData.journalistUUID)
      : undefined,
  );

  // Get the current journalist's username
  const getCurrentJournalistName = () => {
    if (currentJournalist) {
      return currentJournalist.data.username;
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
    dispatch(setUnauth(undefined));
    navigate("/");
  };

  const signIn = () => {
    navigate("/sign-in");
  };

  const sync = () => {
    if (!session.authData) {
      return;
    }

    dispatch(syncMetadata(session.authData));
  };

  const closeApp = () => {
    requestQuit();
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
      case "helpKeys":
        requestHelp();
        break;
      case "helpAbout":
        showAboutModal(aboutContent);
        break;
      default:
        console.warn(`Undefined menu item: ${e.key}`);
        break;
    }
  };

  const items: MenuProps["items"] = [
    {
      key: "syncNow",
      label: t("account.syncNow"),
      extra: formatDisplayKeys(getShortcut("sync")),
      icon: <RefreshCw strokeWidth={1.5} />,
      disabled: !session.authData,
    },
    {
      type: "divider",
    },
    {
      key: "aboutSubMenu",
      label: t("account.Help"),
      icon: <CircleQuestionMark strokeWidth={1.5} />,
      children: [
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
          icon: <LogOut strokeWidth={1.5} />,
          extra: formatDisplayKeys(getShortcut("signOut")),
        }
      : {
          key: "signIn",
          label: t("account.signIn"),
          icon: <LogIn strokeWidth={1.5} />,
        },

    {
      key: "closeApp",
      label: t("account.Quit"),
      icon: <Power strokeWidth={1.5} />,
      extra: formatDisplayKeys(getShortcut("quit")),
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
        <Button
          type="text"
          onClick={(e) => e.preventDefault()}
          data-testid="journalist-menu"
        >
          <Space>
            {session.authData ? (
              <>
                <SyncDicator />
                <Typography.Text>{getCurrentJournalistName()}</Typography.Text>
              </>
            ) : (
              <>
                <SyncDicator />
                <Typography.Text type="warning">
                  {t("account.offlineMode")}
                </Typography.Text>
              </>
            )}
            {isOpen ? <ChevronUp size="16" /> : <ChevronDown size="16" />}
          </Space>
        </Button>
      </Dropdown>
      <Modal
        getContainer={() => document.getElementById("root") || document.body}
        wrapClassName="about-modal-container"
        className="about-modal-content"
        title=""
        closable={false}
        open={isAboutModalOpen}
        onCancel={() => setIsAboutModalOpen(false)}
        footer={[
          <Button
            key="back"
            onClick={() => setIsAboutModalOpen(false)}
            type="primary"
          >
            {t("account.aboutClose")}
          </Button>,
        ]}
      >
        {aboutModalContent}
      </Modal>
    </>
  );
}

export default MainMenu;
