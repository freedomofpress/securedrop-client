import { screen, waitFor } from "@testing-library/react";
import { expect } from "vitest";
import App from "../../src/renderer/App";
import { renderWithProviders } from "../../src/renderer/test-component-setup";
import type { SessionState } from "../../src/renderer/features/session/sessionSlice";

// Mock the views components to make testing simpler
vi.mock("../../src/renderer/views/Inbox", () => ({
  default: () => <div data-testid="inbox-view">Inbox View</div>,
}));

vi.mock("../../src/renderer/views/SignIn", () => ({
  default: () => <div data-testid="signin-view">Sign In View</div>,
}));

describe("App Component", () => {
  it("renders inbox view when user has valid session and navigates to root", async () => {
    const validSession: SessionState = {
      journalist_uuid: "test-uuid-123",
      token: "valid-token",
      expiration: "2025-07-16T19:25:44.388054+00:00",
      journalist_first_name: "Test",
      journalist_last_name: "User",
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

  it("redirects to sign-in when user has no session", async () => {
    const invalidSession: SessionState = {
      journalist_uuid: undefined,
      token: undefined,
      expiration: undefined,
      journalist_first_name: undefined,
      journalist_last_name: undefined,
    };

    renderWithProviders(<App />, {
      initialEntries: ["/"],
      preloadedState: { session: invalidSession },
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
