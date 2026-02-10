import { screen, waitFor } from "@testing-library/react";
import userEvent from "@testing-library/user-event";
import { expect, vi, beforeEach } from "vitest";
import { FirstRunPopup } from "./FirstRunPopup";
import { renderWithProviders } from "../test-component-setup";

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
      expect(screen.getByText("Welcome to SecureDrop")).toBeInTheDocument();
    });

    expect(
      screen.getByText("Placeholder text for new user instructions."),
    ).toBeInTheDocument();
  });

  it("shows migration popup when getFirstRunStatus returns 'migration'", async () => {
    window.electronAPI.getFirstRunStatus = vi
      .fn()
      .mockResolvedValue("migration");

    renderWithProviders(<FirstRunPopup />);

    await waitFor(() => {
      expect(screen.getByText("Migration Required")).toBeInTheDocument();
    });

    expect(
      screen.getByText("Placeholder text for migration instructions."),
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
    expect(screen.queryByText("Welcome to SecureDrop")).not.toBeInTheDocument();
    expect(screen.queryByText("Migration Required")).not.toBeInTheDocument();
  });

  it("renders OK button that can be clicked", async () => {
    const user = userEvent.setup();
    window.electronAPI.getFirstRunStatus = vi
      .fn()
      .mockResolvedValue("new_user");

    renderWithProviders(<FirstRunPopup />);

    await waitFor(() => {
      expect(screen.getByText("Welcome to SecureDrop")).toBeInTheDocument();
    });

    const okButton = screen.getByRole("button", { name: "OK" });
    expect(okButton).toBeInTheDocument();

    // Click should not throw
    await user.click(okButton);
  });
});
