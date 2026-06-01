import { useEffect, useCallback, useRef, useState } from "react";
import { useDispatch } from "react-redux";
import { useNavigate } from "react-router";
import { useTranslation } from "react-i18next";
import type { AppDispatch } from "../store";
import { fetchJournalists } from "../features/journalists/journalistsSlice";
import {
  syncMetadata,
  syncComplete,
  selectSyncStatus,
  clearStatus,
} from "../features/sync/syncSlice";
import { updateItem } from "../features/conversation/conversationSlice";
import { updateSource } from "../features/sources/sourcesSlice";
import { setUnauth } from "../features/session/sessionSlice";
import { SyncStatus, type Item, type Source } from "../../types";
import { useAppSelector } from "../hooks";
import Sidebar from "./Inbox/Sidebar";
import MainContent from "./Inbox/MainContent";
import { useGlobalShortcuts } from "../shortcuts";
import { requestQuit } from "../components/quitRequester";
import { requestHelp } from "../components/helpRequester";
import KeyboardHelpModal from "../components/KeyboardHelpModal";

export type FocusedPanel = "sidebar" | "mainContent";

function InboxView() {
  const dispatch = useDispatch<AppDispatch>();
  const navigate = useNavigate();
  const { t } = useTranslation("SignIn");
  const session = useAppSelector((state) => state.session);
  const syncStatus = useAppSelector(selectSyncStatus);

  const sidebarRef = useRef<HTMLDivElement>(null);
  const mainContentRef = useRef<HTMLDivElement>(null);
  const [focusedPanel, setFocusedPanel] = useState<FocusedPanel>("sidebar");

  const sync = useCallback(() => {
    if (session.authData && import.meta.env.MODE != "test") {
      dispatch(syncMetadata(session.authData));
    }
  }, [dispatch, session.authData]);

  useGlobalShortcuts({
    onQuit: useCallback(() => {
      requestQuit();
    }, []),
    onFocusSidebar: useCallback(() => {
      sidebarRef.current?.focus();
    }, []),
    onFocusMainContent: useCallback(() => {
      mainContentRef.current?.focus();
    }, []),
    onOpenHelp: useCallback(() => {
      requestHelp();
    }, []),
    onSync: useCallback(() => {
      sync();
    }, [sync]),
    onSignOut: useCallback(() => {
      if (session.authData) {
        dispatch(setUnauth(undefined));
        navigate("/");
      }
    }, [session.authData, dispatch, navigate]),
  });

  // Handle 403 Forbidden errors from sync
  useEffect(() => {
    if (syncStatus === SyncStatus.FORBIDDEN) {
      dispatch(setUnauth(t("errors.sessionExpired")));
      dispatch(clearStatus());
    }
  }, [syncStatus, dispatch, t]);

  useEffect(() => {
    dispatch(fetchJournalists());
  }, [dispatch]);

  // Register IPC listeners for real-time updates from the main process
  useEffect(() => {
    const unsubscribeItem = window.electronAPI.onItemUpdate((item: Item) => {
      dispatch(updateItem(item));
    });
    const unsubscribeSource = window.electronAPI.onSourceUpdate(
      (source: Source) => {
        dispatch(updateSource(source));
      },
    );
    const unsubscribeSync = window.electronAPI.onSyncComplete(
      (status: SyncStatus) => {
        dispatch(syncComplete(status));
      },
    );
    return () => {
      unsubscribeItem();
      unsubscribeSource();
      unsubscribeSync();
    };
  }, [dispatch]);

  // Handle focus via native focusin events
  useEffect(() => {
    const sidebar = sidebarRef.current;
    const mainContent = mainContentRef.current;

    const handleSidebarFocus = () => setFocusedPanel("sidebar");
    const handleMainContentFocus = () => setFocusedPanel("mainContent");

    sidebar?.addEventListener("focusin", handleSidebarFocus);
    mainContent?.addEventListener("focusin", handleMainContentFocus);

    return () => {
      sidebar?.removeEventListener("focusin", handleSidebarFocus);
      mainContent?.removeEventListener("focusin", handleMainContentFocus);
    };
  }, []);

  return (
    <div className="flex h-screen min-h-0">
      <div
        ref={sidebarRef}
        tabIndex={-1}
        className="h-full outline-0 focus:outline-2 focus:outline-blue-300 focus:-outline-offset-2"
        data-testid="sidebar-panel"
      >
        <Sidebar focusedPanel={focusedPanel} />
      </div>
      <div
        ref={mainContentRef}
        tabIndex={-1}
        className="flex-1 min-w-0 h-full outline-0 focus:outline-2 focus:outline-blue-300 focus:-outline-offset-2"
        data-testid="main-content-panel"
      >
        <MainContent />
      </div>
      <KeyboardHelpModal />
    </div>
  );
}

export default InboxView;
