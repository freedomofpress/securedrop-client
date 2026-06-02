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

// Expose store to window for testing
if (typeof window !== "undefined") {
  // eslint-disable-next-line @typescript-eslint/no-explicit-any
  (window as any).__REDUX_STORE__ = store;
}

window.electronAPI.getCSPNonce().then((nonce) => {
  createRoot(document.getElementById("root")!).render(
    <StrictMode>
      <ConfigProvider
        csp={{ nonce }}
        theme={{
          token: {
            // WCAG 2.2 requirement: this color on a white background
            // has a contrast ratio of 4.608:1
            colorTextPlaceholder: "#757575",
            // Keep disabled text readable (including disabled link buttons
            // like the conversation Send button) on light backgrounds
            colorTextDisabled: "#666666",
            // Raise default Ant focus contrast globally
            colorPrimaryBorder: "#3b82f6",
            colorPrimaryBorderHover: "#3b82f6",
            controlOutline: "#3b82f6",
            controlOutlineWidth: 2,
          },
        }}
      >
        <Provider store={store}>
          <MemoryRouter initialEntries={["/"]}>
            <App />
          </MemoryRouter>
        </Provider>
      </ConfigProvider>
    </StrictMode>,
  );
});
