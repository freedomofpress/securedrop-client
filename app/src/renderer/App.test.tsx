import { screen, waitFor } from "@testing-library/react";
import { expect } from "vitest";
import App from "./App";
import { renderWithProviders } from "./test-component-setup";
import {
  unauthSessionState,
  SessionStatus,
} from "./features/session/sessionSlice";
import type { SessionState, AuthData } from "./features/session/sessionSlice";

// Mock the views components to make testing simpler
vi.mock("./views/Inbox", () => ({
  // eslint-disable-next-line i18next/no-literal-string
  default: () => <div data-testid="inbox-view">Inbox View</div>,
}));

vi.mock("./views/SignIn", () => ({
  // eslint-disable-next-line i18next/no-literal-string
  default: () => <div data-testid="signin-view">Sign In View</div>,
}));

describe("App Component", () => {
  it("renders inbox view when user has valid session and navigates to root", async () => {
    const validSession: SessionState = {
      status: SessionStatus.Auth,
      authData: {
        journalistUUID: "test-uuid-123",
        token: "valid-token",
        expiration: "2025-07-16T19:25:44.388054+00:00",
        journalistFirstName: "Test",
        journalistLastName: "User",
      } as AuthData,
    };

    renderWithProviders(<App />, {
      initialEntries: ["/"],
      preloadedState: { session: validSession },
    });

    // Should render the inbox view
    await waitFor(() => {
      expect(screen.getByTestId("inbox-view")).toBeInTheDocument();
      expect(screen.getByText("Inbox View")).toBeInTheDocument();
    });

    // Should not render the sign-in view
    expect(screen.queryByTestId("signin-view")).not.toBeInTheDocument();
  });

  it("renders inbox view when in offline mode", async () => {
    renderWithProviders(<App />, {
      initialEntries: ["/"],
      preloadedState: { session: { status: SessionStatus.Offline } },
    });

    // Should render the inbox view
    await waitFor(() => {
      expect(screen.getByTestId("inbox-view")).toBeInTheDocument();
      expect(screen.getByText("Inbox View")).toBeInTheDocument();
    });

    // Should not render the sign-in view
    expect(screen.queryByTestId("signin-view")).not.toBeInTheDocument();
  });

  it("redirects to sign-in when user has no session", async () => {
    renderWithProviders(<App />, {
      initialEntries: ["/"],
      preloadedState: { session: unauthSessionState },
    });

    // Should render the sign-in view (redirected from root)
    await waitFor(() => {
      expect(screen.getByTestId("signin-view")).toBeInTheDocument();
      expect(screen.getByText("Sign In View")).toBeInTheDocument();
    });

    // Should not render the inbox view
    expect(screen.queryByTestId("inbox-view")).not.toBeInTheDocument();
  });
});
