/* eslint-disable @typescript-eslint/no-explicit-any */
import { screen, waitFor } from "@testing-library/react";
import { expect } from "vitest";
import userEvent from "@testing-library/user-event";
import SignInView from "../../../src/renderer/views/SignIn";
import { renderWithProviders } from "../../../src/renderer/test-component-setup";

describe("SignInView Component", () => {
  it("says title and version", async () => {
    renderWithProviders(<SignInView />);

    // Wait for the async useEffect to complete
    await waitFor(() => {
      expect(screen.getByText("Sign in to SecureDrop")).toBeInTheDocument();
      // getVersion is mocked to return "1.0.0"
      expect(screen.getByText("SecureDrop App v1.0.0")).toBeInTheDocument();
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
});
