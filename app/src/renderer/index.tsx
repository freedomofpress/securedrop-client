import { StrictMode } from "react";
import { createRoot } from "react-dom/client";
import { MemoryRouter } from "react-router";
import { Provider } from "react-redux";
import { ConfigProvider } from "antd";

import "./i18n";
import "./index.css";
import App from "./App";
import { setupStore } from "./store";

const store = setupStore();

// Expose store to window for testing
if (typeof window !== "undefined") {
  // eslint-disable-next-line @typescript-eslint/no-explicit-any
  (window as any).__REDUX_STORE__ = store;
}

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
