import { screen, waitFor } from "@testing-library/react";
import userEvent from "@testing-library/user-event";
import { expect, vi, beforeEach } from "vitest";
import { FirstRunPopup } from "./FirstRunPopup";
import {
  renderWithProviders,
  renderAndCheckA11y,
} from "../test-component-setup";

describe("FirstRunPopup accessibility", () => {
  it("has no axe violations when no popup is shown (null status)", async () => {
    window.electronAPI.getFirstRunStatus = vi.fn().mockResolvedValue(null);
    await renderAndCheckA11y(<FirstRunPopup />);
  });

  it("has no axe violations when the new-user popup is visible", async () => {
    window.electronAPI.getFirstRunStatus = vi
      .fn()
      .mockResolvedValue("new_user");
    const result = await renderAndCheckA11y(<FirstRunPopup />);
    // Wait for the async popup to appear and re-check
    await waitFor(() => {
      expect(
        result.getByText("Welcome to SecureDrop Inbox"),
      ).toBeInTheDocument();
    });
  });
});

describe("FirstRunPopup Component", () => {
  beforeEach(() => {
    vi.clearAllMocks();
  });

  it("shows new user popup when getFirstRunStatus returns 'new_user'", async () => {
    window.electronAPI.getFirstRunStatus = vi
      .fn()
      .mockResolvedValue("new_user");

    renderWithProviders(<FirstRunPopup />);

    await waitFor(() => {
      expect(
        screen.getByText("Welcome to SecureDrop Inbox"),
      ).toBeInTheDocument();
    });

    expect(
      screen.getByText(
        "Messages and documents sent to you via SecureDrop will show up here.",
        { exact: false, selector: "p" },
      ),
    ).toBeInTheDocument();
  });

  it("shows migration popup when getFirstRunStatus returns 'migration'", async () => {
    window.electronAPI.getFirstRunStatus = vi
      .fn()
      .mockResolvedValue("migration");

    renderWithProviders(<FirstRunPopup />);

    await waitFor(() => {
      expect(
        screen.getByText("Welcome to the new SecureDrop Inbox"),
      ).toBeInTheDocument();
    });

    expect(
      screen.getByText(
        "The application has been rewritten from the ground up to make it faster and to add long-requested features.",
        { exact: false, selector: "p" },
      ),
    ).toBeInTheDocument();
  });

  it("does not show popup when getFirstRunStatus returns null", async () => {
    window.electronAPI.getFirstRunStatus = vi.fn().mockResolvedValue(null);

    renderWithProviders(<FirstRunPopup />);

    // Wait for the async call to complete
    await waitFor(() => {
      expect(window.electronAPI.getFirstRunStatus).toHaveBeenCalled();
    });

    // Modal should not be visible
    expect(
      screen.queryByText("Welcome to SecureDrop Inbox"),
    ).not.toBeInTheDocument();
    expect(
      screen.queryByText("Welcome to the new SecureDrop Inbox"),
    ).not.toBeInTheDocument();
  });

  it("renders OK button that can be clicked", async () => {
    const user = userEvent.setup();
    window.electronAPI.getFirstRunStatus = vi
      .fn()
      .mockResolvedValue("new_user");

    renderWithProviders(<FirstRunPopup />);

    await waitFor(() => {
      expect(
        screen.getByText("Welcome to SecureDrop Inbox"),
      ).toBeInTheDocument();
    });

    const okButton = screen.getByRole("button", { name: "OK" });
    expect(okButton).toBeInTheDocument();

    // Click should not throw
    await user.click(okButton);
  });
});
