import { Routes, Route, Navigate } from "react-router";

import InboxView from "./views/Inbox";
import SignInView from "./views/SignIn";
import { useAppSelector } from "./hooks";
import { SessionStatus } from "./features/session/sessionSlice";
import { useTranslation } from "react-i18next";
import { FirstRunPopup } from "./components/FirstRunPopup";
import QuitModal from "./components/QuitModal";

function App() {
  const { t } = useTranslation("MainContent");
  return (
    <>
      {!__IS_PRODUCTION__ && (
        <div className="fixed bottom-1 left-1 z-50 bg-red-700 text-white text-xs font-bold py-1 px-4 leading-tight rounded">
          {t("nonProduction")}
        </div>
      )}
      <QuitModal />
      <Routes>
        <Route
          index
          path="/"
          element={
            <ProtectedRoute>
              <InboxView />
            </ProtectedRoute>
          }
        />
        <Route
          path="/source/:sourceUuid"
          element={
            <ProtectedRoute>
              <InboxView />
            </ProtectedRoute>
          }
        />
        <Route path="/sign-in" element={<SignInView />} />
      </Routes>
    </>
  );
}

// Gate the routes that require authentication

type ProtectedRouteProps = {
  children: React.ReactNode;
};

const ProtectedRoute = ({ children }: ProtectedRouteProps) => {
  const session = useAppSelector((state) => state.session);

  if (
    session.status == SessionStatus.Auth ||
    session.status == SessionStatus.Offline
  ) {
    return (
      <>
        <FirstRunPopup />
        {children}
      </>
    );
  }

  return <Navigate to="/sign-in" replace />;
};

export default App;
