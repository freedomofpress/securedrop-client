import { Routes, Route, useNavigate } from "react-router";
import { useEffect } from "react";

import InboxView from "./views/Inbox";
import SignInView from "./views/SignIn";
import { useAppDispatch, useAppSelector } from "./hooks";
import { clear, SessionStatus } from "./features/session/sessionSlice";

function App() {
  const session = useAppSelector((state) => state.session);
  const dispatch = useAppDispatch();
  const navigate = useNavigate();

  // If we're not in offline mode and there's no session, redirect to sign-in
  useEffect(() => {
    if (
      session.status !== SessionStatus.Offline &&
      !session.authData?.journalistUUID
    ) {
      console.log("No session found, redirecting to sign-in");
      dispatch(clear());
      navigate("/sign-in");
    }
  }, [session.status, session.authData?.journalistUUID, dispatch, navigate]);

  return (
    <Routes>
      <Route path="/" element={<InboxView />} />
      <Route path="/sign-in" element={<SignInView />} />
    </Routes>
  );
}

export default App;
