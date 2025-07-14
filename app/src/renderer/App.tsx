import { Routes, Route } from "react-router";

import InboxView from "./views/Inbox";
import SignInView from "./views/SignIn";

function App() {
  return (
    <Routes>
      <Route path="/" element={<InboxView />} />
      <Route path="/sign-in" element={<SignInView />} />
    </Routes>
  );
}

export default App;
