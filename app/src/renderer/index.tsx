import { StrictMode } from "react";
import { createRoot } from "react-dom/client";
import { MemoryRouter } from "react-router";
import { Provider } from "react-redux";
import { ConfigProvider } from "antd";
import "@ant-design/v5-patch-for-react-19";

import "./i18n";
import "./index.css";
import App from "./App";
import { setupStore } from "./store";

const store = setupStore();

window.electronAPI.getCSPNonce().then((nonce) => {
  createRoot(document.getElementById("root")!).render(
    <StrictMode>
      <ConfigProvider csp={{ nonce }}>
        <Provider store={store}>
          <MemoryRouter initialEntries={["/"]}>
            <App />
          </MemoryRouter>
        </Provider>
      </ConfigProvider>
    </StrictMode>,
  );
});
