import { screen, waitFor } from "@testing-library/react";
import { expect } from "vitest";
import userEvent from "@testing-library/user-event";
import SignInView from "./SignIn";
import {
  renderWithProviders,
  renderAndCheckA11y,
} from "../test-component-setup";
import { SessionStatus } from "../features/session/sessionSlice";

describe("SignInView accessibility", () => {
  it("has no axe violations on initial render", async () => {
    await renderAndCheckA11y(<SignInView />);
  });
});

describe("SignInView Component", () => {
  it("says title and version", async () => {
    renderWithProviders(<SignInView />);

    // Wait for the async useEffect to complete
    await waitFor(() => {
      expect(screen.getByText("Sign in to SecureDrop")).toBeInTheDocument();
      expect(
        screen.getByText("SecureDrop Inbox v6.6.6-test"),
      ).toBeInTheDocument();
    });
  });

  // Client-side validations

  it("client-side validates username", async () => {
    renderWithProviders(<SignInView />);

    const usernameItem = screen.getByTestId("username-form-item");
    const usernameInput = screen.getByTestId("username-input");
    const signInButton = screen.getByTestId("sign-in-button");

    // Empty username
    await userEvent.click(signInButton);
    await waitFor(() => {
      const errorText = screen.getByText("Please enter your username.");
      expect(usernameItem).toContainElement(errorText);
    });

    // Short username
    await userEvent.type(usernameInput, "ab");
    await userEvent.click(signInButton);
    await waitFor(() => {
      const errorText = screen.getByText(
        "That username won't work. It should be at least 3 characters long.",
      );
      expect(usernameItem).toContainElement(errorText);
    });
  });

  it("client-side validates passphrase", async () => {
    renderWithProviders(<SignInView />);

    const passphraseItem = screen.getByTestId("passphrase-form-item");
    const passphraseInput = screen.getByTestId("passphrase-input");
    const signInButton = screen.getByTestId("sign-in-button");

    // Empty passphrase
    await userEvent.click(signInButton);
    await waitFor(() => {
      const errorText = screen.getByText("Please enter your passphrase.");
      expect(passphraseItem).toContainElement(errorText);
    });

    // Short passphrase (less than 14 characters)
    await userEvent.clear(passphraseInput);
    await userEvent.type(passphraseInput, "short");
    await userEvent.click(signInButton);
    await waitFor(() => {
      const errorText = screen.getByText(
        "That passphrase won't work. It should be between 14 and 128 characters long.",
      );
      expect(passphraseItem).toContainElement(errorText);
    });

    // Long passphrase (more than 128 characters)
    await userEvent.clear(passphraseInput);
    await userEvent.type(passphraseInput, "a".repeat(129));
    await userEvent.click(signInButton);
    await waitFor(() => {
      const errorText = screen.getByText(
        "That passphrase won't work. It should be between 14 and 128 characters long.",
      );
      expect(passphraseItem).toContainElement(errorText);
    });
  });

  it("client-side validates one-time code", async () => {
    renderWithProviders(<SignInView />);

    const oneTimeCodeItem = screen.getByTestId("one-time-code-form-item");
    const oneTimeCodeInput = screen.getByTestId("one-time-code-input");
    const signInButton = screen.getByTestId("sign-in-button");

    // Ensure letter do not get typed in the one-time code input
    await userEvent.type(oneTimeCodeInput, "abc123");
    expect(oneTimeCodeInput).toHaveValue("123");

    // Ensure the one-time code input cannot have more than 6 digits
    await userEvent.clear(oneTimeCodeInput);
    await userEvent.type(oneTimeCodeInput, "123456789");
    expect(oneTimeCodeInput).toHaveValue("123456");

    // Empty one-time code
    await userEvent.clear(oneTimeCodeInput);
    await userEvent.click(signInButton);
    await waitFor(() => {
      const errorText = screen.getByText("Please enter your two-factor code.");
      expect(oneTimeCodeItem).toContainElement(errorText);
    });

    // Invalid one-time code (fewer than 6 digits)
    await userEvent.clear(oneTimeCodeInput);
    await userEvent.type(oneTimeCodeInput, "12345");
    await userEvent.click(signInButton);
    await waitFor(() => {
      const errorText = screen.getByText(
        "Your two-factor code must be exactly 6 digits.",
      );
      expect(oneTimeCodeItem).toContainElement(errorText);
    });
  });

  // Server-side validations

  it("fails when server is unreachable", async () => {
    // Mock window.electronAPI.login to return a network error
    (window as any).electronAPI.login.mockResolvedValue({
      success: false,
      errorType: "network",
    });

    renderWithProviders(<SignInView />);

    const usernameInput = screen.getByTestId("username-input");
    const passphraseInput = screen.getByTestId("passphrase-input");
    const oneTimeCodeInput = screen.getByTestId("one-time-code-input");
    const signInButton = screen.getByTestId("sign-in-button");

    // Fill in valid inputs
    await userEvent.type(usernameInput, "nelliebly");
    await userEvent.type(passphraseInput, "validPassphrase12345");
    await userEvent.type(oneTimeCodeInput, "123456");

    // Click sign-in button
    await userEvent.click(signInButton);

    // Wait for server response and check for error message
    await waitFor(() => {
      expect(
        screen.getByText("Could not reach the SecureDrop server."),
      ).toBeInTheDocument();
    });
  });

  it("fails when credentials are invalid", async () => {
    // Mock window.electronAPI.login to return a credentials error
    (window as any).electronAPI.login.mockResolvedValue({
      success: false,
      errorType: "credentials",
    });

    renderWithProviders(<SignInView />);

    const usernameInput = screen.getByTestId("username-input");
    const passphraseInput = screen.getByTestId("passphrase-input");
    const oneTimeCodeInput = screen.getByTestId("one-time-code-input");
    const signInButton = screen.getByTestId("sign-in-button");

    // Fill in valid inputs
    await userEvent.type(usernameInput, "nelliebly");
    await userEvent.type(passphraseInput, "validPassphrase12345");
    await userEvent.type(oneTimeCodeInput, "123456");

    // Click sign-in button
    await userEvent.click(signInButton);

    // Wait for server response and check for error message
    await waitFor(() => {
      expect(
        screen.getByText("Those credentials didn't work."),
      ).toBeInTheDocument();
    });
  });

  it("redirects to inbox on success", async () => {
    // Mock window.electronAPI.login to return success
    (window as any).electronAPI.login.mockResolvedValue({
      success: true,
      expiration: "2025-07-16T19:25:44.388054+00:00",
      journalistFirstName: null,
      journalistLastName: null,
      journalistUUID: "7f19192d-c8e3-4518-9d4a-26cb39bc8662",
      lastHintedVersion:
        "a1b2c3d4e5f6a1b2c3d4e5f6a1b2c3d4e5f6a1b2c3d4e5f6a1b2c3d4e5f6a1b2",
      lastHintedSources: 3,
      lastHintedItems: 10,
    });

    let currentLocation: any;
    const handleLocationChange = (location: any) => {
      currentLocation = location;
    };

    renderWithProviders(<SignInView />, {
      initialEntries: ["/inbox"],
      onLocationChange: handleLocationChange,
    });

    // Get initial location
    expect(currentLocation.pathname).toBe("/inbox");

    const usernameInput = screen.getByTestId("username-input");
    const passphraseInput = screen.getByTestId("passphrase-input");
    const oneTimeCodeInput = screen.getByTestId("one-time-code-input");
    const signInButton = screen.getByTestId("sign-in-button");

    // Fill in valid inputs
    await userEvent.type(usernameInput, "nelliebly");
    await userEvent.type(passphraseInput, "validPassphrase12345");
    await userEvent.type(oneTimeCodeInput, "123456");

    // Click sign-in button
    await userEvent.click(signInButton);

    await waitFor(() => {
      // Should have redirected to the inbox
      expect(currentLocation.pathname).toBe("/");
    });
  });

  it("sets offline mode and redirects to inbox when offline button is clicked", async () => {
    let currentLocation: any;
    const handleLocationChange = (location: any) => {
      currentLocation = location;
    };

    const { store } = renderWithProviders(<SignInView />, {
      initialEntries: ["/sign-in"],
      onLocationChange: handleLocationChange,
    });

    // Get initial location
    expect(currentLocation.pathname).toBe("/sign-in");

    const useOfflineButton = screen.getByTestId("use-offline-button");

    // Click use offline button
    await userEvent.click(useOfflineButton);

    await waitFor(() => {
      // Should have redirected to the inbox
      expect(currentLocation.pathname).toBe("/");

      // Should have set session status to offline
      const state = store.getState();
      expect(state.session.status).toBe(SessionStatus.Offline);
    });
  });
});
