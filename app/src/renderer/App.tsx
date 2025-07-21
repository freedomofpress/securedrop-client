import { Routes, Route, Navigate } from "react-router";

import InboxView from "./views/Inbox";
import SignInView from "./views/SignIn";
import { useAppSelector } from "./hooks";
import { SessionStatus } from "./features/session/sessionSlice";

function App() {
  return (
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
      <Route path="/sign-in" element={<SignInView />} />
    </Routes>
  );
}

// Gate the routes that require authentication

type ProtectedRouteProps = {
  children: React.ReactNode;
};

const ProtectedRoute = ({ children }: ProtectedRouteProps) => {
  const session = useAppSelector((state) => state.session);

  if (
    session.status !== SessionStatus.Auth &&
    session.status !== SessionStatus.Offline
  ) {
    return <Navigate to="/sign-in" replace />;
  }

  return children;
};

export default App;
