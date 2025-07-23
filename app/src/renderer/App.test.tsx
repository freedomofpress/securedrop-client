<<<<<<< HEAD
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
  default: () => <div data-testid="inbox-view">Inbox View</div>,
}));

vi.mock("./views/SignIn", () => ({
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
=======
import { render, screen } from "@testing-library/react";
import { vi, expect } from "vitest";
import userEvent from "@testing-library/user-event";
import App from "./App";

describe("App Component", () => {
  it('says the string "Hello world!"', () => {
    render(<App />);
    expect(screen.getByText("Hello world!")).toBeInTheDocument();
  });

  it("calls window.electronAPI.request when the button is clicked", async () => {
    // Mock IPC methods
    window.electronAPI = {
      request: vi.fn().mockResolvedValue({ data: "test" }),
      requestStream: vi.fn().mockResolvedValue({ sha256sum: "abc" }),
      syncMetadata: vi.fn().mockResolvedValue({}),
    };

    render(<App />);
    const dummyButton = screen.getByTestId("dummy-button");
    await userEvent.click(dummyButton);
    expect(window.electronAPI.request).toHaveBeenCalled();
>>>>>>> 9361964a ([app] implement initial client/server sync)
  });
});
