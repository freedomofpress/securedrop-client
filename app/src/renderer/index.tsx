import { StrictMode } from "react";
import { createRoot } from "react-dom/client";
import { MemoryRouter } from "react-router";
import { Provider } from "react-redux";
import { ConfigProvider } from "antd";
import "@ant-design/v5-patch-for-react-19";

import { languageReady, textDirection } from "./i18n";
import "./index.css";
import App from "./App";
import { setupStore } from "./store";

const store = setupStore();

// Expose store to window for server tests
if (import.meta.env.MODE === "test") {
  // eslint-disable-next-line @typescript-eslint/no-explicit-any
  (window as any).__REDUX_STORE__ = store;
}

/* eslint-disable react-refresh/only-export-components -- renderer entry point: Root is mounted below rather than exported. */

// Hosts the providers, including Ant Design's writing direction.
// nosemgrep: react-component-missing-memo -- createRoot renders Root once, so there is no parent re-render for memo to skip.
function Root({ nonce }: { nonce: string }) {
  const direction = textDirection();

  return (
    <ConfigProvider
      csp={{ nonce }}
      direction={direction}
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
        components: {
          Input: {
            colorBorder: "#808080",
            hoverBorderColor: "#3b82f6",
            activeBorderColor: "#3b82f6",
          },
        },
      }}
    >
      <Provider store={store}>
        <MemoryRouter initialEntries={["/"]}>
          <App />
        </MemoryRouter>
      </Provider>
    </ConfigProvider>
  );
}

// Wait for the system language before the first render
Promise.all([window.electronAPI.getCSPNonce(), languageReady]).then(
  ([nonce]) => {
    createRoot(document.getElementById("root")!).render(
      <StrictMode>
        <Root nonce={nonce} />
      </StrictMode>,
    );
  },
);
