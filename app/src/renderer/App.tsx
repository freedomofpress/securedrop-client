import { Routes, Route, useNavigate } from "react-router";
import { useEffect } from "react";

import InboxView from "./views/Inbox";
import SignInView from "./views/SignIn";
import { useAppDispatch, useAppSelector } from "./hooks";
import { clear } from "./features/session/sessionSlice";

function App() {
  const session = useAppSelector((state) => state.session);
  const dispatch = useAppDispatch();
  const navigate = useNavigate();

  // Check if the session is valid and redirect if needed
  useEffect(() => {
    if (!session.journalist_uuid) {
      console.log("No session found, redirecting to sign-in");
      dispatch(clear());
      navigate("/sign-in");
    }
  }, [session.journalist_uuid, dispatch, navigate]);

  return (
    <Routes>
      <Route path="/" element={<InboxView />} />
      <Route path="/sign-in" element={<SignInView />} />
    </Routes>
  );
}

export default App;
