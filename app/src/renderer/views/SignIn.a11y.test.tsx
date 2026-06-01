import { describe, it, expect } from "vitest";
import { screen, waitFor } from "@testing-library/react";
import userEvent from "@testing-library/user-event";
import SignInView from "./SignIn";
import {
  checkA11y,
  renderAndCheckA11y,
  renderWithProviders,
} from "../test-component-setup";

describe("SignIn accessibility", () => {
  it("has no axe violations on initial render", async () => {
    await renderAndCheckA11y(<SignInView />);
  });

  it("has no axe violations when showing client-side validation errors", async () => {
    const { container, getByTestId } = renderWithProviders(<SignInView />);

    // Submit empty form to trigger all three required-field errors at once
    await userEvent.click(getByTestId("sign-in-button"));

    await waitFor(() => {
      expect(
        screen.getByText("Please enter your username."),
      ).toBeInTheDocument();
    });

    const results = await checkA11y(container);
    expect(results).toHaveNoViolations();
  });

  it("has no axe violations when showing a credential error", async () => {
    (window as any).electronAPI.login.mockResolvedValue({
      success: false,
      errorType: "credentials",
    });

    const { container, getByTestId } = renderWithProviders(<SignInView />);

    await userEvent.type(getByTestId("username-input"), "nelliebly");
    await userEvent.type(
      getByTestId("passphrase-input"),
      "validPassphrase12345",
    );
    await userEvent.type(getByTestId("one-time-code-input"), "123456");
    await userEvent.click(getByTestId("sign-in-button"));

    await waitFor(() => {
      expect(
        screen.getByText("Those credentials didn't work."),
      ).toBeInTheDocument();
    });

    const results = await checkA11y(container);
    expect(results).toHaveNoViolations();
  });

  it("has no axe violations when showing a network error", async () => {
    (window as any).electronAPI.login.mockResolvedValue({
      success: false,
      errorType: "network",
    });

    const { container, getByTestId } = renderWithProviders(<SignInView />);

    await userEvent.type(getByTestId("username-input"), "nelliebly");
    await userEvent.type(
      getByTestId("passphrase-input"),
      "validPassphrase12345",
    );
    await userEvent.type(getByTestId("one-time-code-input"), "123456");
    await userEvent.click(getByTestId("sign-in-button"));

    await waitFor(() => {
      expect(
        screen.getByText("Could not reach the SecureDrop server."),
      ).toBeInTheDocument();
    });

    const results = await checkA11y(container);
    expect(results).toHaveNoViolations();
  });
});
