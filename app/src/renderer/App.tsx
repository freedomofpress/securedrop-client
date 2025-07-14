import { Routes, Route } from "react-router";

import InboxView from "./views/Inbox";

function App() {
  return (
    <Routes>
      <Route path="/" element={<InboxView />} />
    </Routes>
  );
}

export default App;
