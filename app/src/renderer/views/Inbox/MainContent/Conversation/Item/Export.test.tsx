import { screen, waitFor } from "@testing-library/react";
import { expect, describe, it, vi, beforeEach, afterEach } from "vitest";
import userEvent from "@testing-library/user-event";
import { ExportWizard } from "./Export";
import {
  ExportStatus,
  FetchStatus,
  DeviceErrorStatus,
  type Item,
} from "../../../../../../types";
import { renderWithProviders } from "../../../../../test-component-setup";

describe("ExportWizard Component", () => {
  const mockItem: Item = {
    uuid: "test-item-uuid",
    data: {
      uuid: "test-item-uuid",
      kind: "file",
      seen_by: [],
      size: 1024,
      source: "source-1",
      is_read: false,
      interaction_count: 0,
    },
    fetch_status: FetchStatus.Complete,
    filename: "/path/to/testfile.pdf",
  };

  const mockOnClose = vi.fn();

  const waitForPreflightComplete = async () => {
    await waitFor(
      () => {
        const continueButton = screen.getByRole("button", {
          name: /continue/i,
        });
        expect(continueButton).not.toBeDisabled();
      },
      { timeout: 2000 },
    );
  };

  const navigateToUnlockDevice = async () => {
    await waitForPreflightComplete();
    const continueButton = screen.getByRole("button", { name: /continue/i });
    await userEvent.click(continueButton);

    await waitFor(() => {
      expect(screen.getByLabelText("Passphrase")).toBeInTheDocument();
    });
  };

  const submitPassphrase = async (passphrase: string) => {
    const passphraseInput = screen.getByLabelText("Passphrase");
    await userEvent.type(passphraseInput, passphrase);

    const continueButton = screen.getByRole("button", { name: /continue/i });
    await userEvent.click(continueButton);
  };

  beforeEach(() => {
    vi.clearAllMocks();
  });

  afterEach(() => {
    vi.restoreAllMocks();
  });

  describe("Initial and Preflight State", () => {
    it("renders nothing when not open", () => {
      renderWithProviders(
        <ExportWizard item={mockItem} open={false} onClose={mockOnClose} />,
      );

      expect(screen.queryByRole("dialog")).not.toBeInTheDocument();
    });

    it("displays preflight state with warnings and disabled Continue button", async () => {
      renderWithProviders(
        <ExportWizard item={mockItem} open={true} onClose={mockOnClose} />,
      );

      await waitFor(() => {
        expect(screen.getByText("Preparing to export.")).toBeInTheDocument();
        expect(
          screen.getByText("Understand the risks before exporting files"),
        ).toBeInTheDocument();
        expect(screen.getByText("testfile.pdf")).toBeInTheDocument();

        const continueButton = screen.getByRole("button", {
          name: /continue/i,
        });
        expect(continueButton).toBeDisabled();
        expect(document.querySelector(".animate-spin")).toBeInTheDocument();
        expect(screen.queryByLabelText("Close")).not.toBeInTheDocument();
      });
    });

    it("automatically transitions to PREFLIGHT_COMPLETE and enables Continue button", async () => {
      renderWithProviders(
        <ExportWizard item={mockItem} open={true} onClose={mockOnClose} />,
      );

      await waitForPreflightComplete();

      expect(screen.getByText("Preparing to export.")).toBeInTheDocument();
      expect(
        screen.getByRole("button", { name: /continue/i }),
      ).not.toBeDisabled();
      expect(
        screen.getByRole("button", { name: /cancel/i }),
      ).toBeInTheDocument();
      expect(
        screen.queryByRole("button", { name: /back/i }),
      ).not.toBeInTheDocument();
    });

    it("handles preflight failure with error message", async () => {
      vi.mocked(window.electronAPI.initiateExport).mockRejectedValueOnce(
        new Error("Failed to connect to export device"),
      );

      renderWithProviders(
        <ExportWizard item={mockItem} open={true} onClose={mockOnClose} />,
      );

      await waitFor(() => {
        expect(document.querySelector(".animate-spin")).not.toBeInTheDocument();
        expect(screen.getByText(/Export Failed/i)).toBeInTheDocument();
        const closeButtons = screen.getAllByRole("button", { name: /close/i });
        expect(closeButtons.length).toBeGreaterThanOrEqual(1);
      });
    });

    it("transitions to UNLOCK_DEVICE when Continue clicked", async () => {
      renderWithProviders(
        <ExportWizard item={mockItem} open={true} onClose={mockOnClose} />,
      );

      await navigateToUnlockDevice();

      expect(
        screen.getByText("Enter passphrase for USB drive"),
      ).toBeInTheDocument();
    });
  });

  describe("Unlock Device State", () => {
    it("shows passphrase input with Continue disabled until passphrase entered", async () => {
      renderWithProviders(
        <ExportWizard item={mockItem} open={true} onClose={mockOnClose} />,
      );

      await navigateToUnlockDevice();

      const passphraseInput = screen.getByLabelText("Passphrase");
      expect(passphraseInput).toHaveAttribute("type", "password");
      expect(screen.getByRole("button", { name: /continue/i })).toBeDisabled();

      await userEvent.type(passphraseInput, "test-passphrase");

      expect(
        screen.getByRole("button", { name: /continue/i }),
      ).not.toBeDisabled();
    });

    it("navigates back to PREFLIGHT_COMPLETE when Back button clicked", async () => {
      renderWithProviders(
        <ExportWizard item={mockItem} open={true} onClose={mockOnClose} />,
      );

      await navigateToUnlockDevice();

      const backButton = screen.getByRole("button", { name: /back/i });
      await userEvent.click(backButton);

      await waitFor(() => {
        expect(screen.getByText("Preparing to export.")).toBeInTheDocument();
        expect(
          screen.getByRole("button", { name: /continue/i }),
        ).not.toBeDisabled();
      });
    });

    it("skips unlock state when device is already writable", async () => {
      vi.mocked(window.electronAPI.initiateExport).mockResolvedValueOnce(
        ExportStatus.DEVICE_WRITABLE,
      );

      renderWithProviders(
        <ExportWizard item={mockItem} open={true} onClose={mockOnClose} />,
      );

      await waitForPreflightComplete();

      const continueButton = screen.getByRole("button", { name: /continue/i });
      await userEvent.click(continueButton);

      await waitFor(() => {
        expect(
          screen.queryByText("Enter passphrase for USB drive"),
        ).not.toBeInTheDocument();
        expect(
          screen.queryByText("Please wait...") ||
            screen.queryByText("Export Successful"),
        ).toBeInTheDocument();
      });
    });
  });

  describe("Exporting and Success", () => {
    it("shows exporting state with no buttons during export", async () => {
      vi.mocked(window.electronAPI.export).mockImplementationOnce(
        () =>
          new Promise((resolve) =>
            setTimeout(() => resolve(ExportStatus.SUCCESS_EXPORT), 200),
          ),
      );

      renderWithProviders(
        <ExportWizard item={mockItem} open={true} onClose={mockOnClose} />,
      );

      await navigateToUnlockDevice();
      await submitPassphrase("test-passphrase");

      await waitFor(() => {
        expect(screen.getByText("Please wait...")).toBeInTheDocument();
        expect(
          screen.queryByRole("button", { name: /continue/i }),
        ).not.toBeInTheDocument();
        expect(screen.queryByLabelText("Close")).not.toBeInTheDocument();
      });
    });

    it("calls export API with correct parameters", async () => {
      const exportMock = vi.mocked(window.electronAPI.export);

      renderWithProviders(
        <ExportWizard item={mockItem} open={true} onClose={mockOnClose} />,
      );

      await navigateToUnlockDevice();
      const testPassphrase = "my-secure-passphrase-123";
      await submitPassphrase(testPassphrase);

      await waitFor(() => {
        expect(exportMock).toHaveBeenCalledWith(
          [mockItem.uuid],
          testPassphrase,
        );
      });
    });

    it("shows success state with Done button and closes on click", async () => {
      renderWithProviders(
        <ExportWizard item={mockItem} open={true} onClose={mockOnClose} />,
      );

      await navigateToUnlockDevice();
      await submitPassphrase("test-passphrase");

      await waitFor(() => {
        expect(screen.getByText("Export Successful")).toBeInTheDocument();
      });

      expect(screen.getByRole("button", { name: /done/i })).toBeInTheDocument();
      expect(
        screen.queryByRole("button", { name: /continue/i }),
      ).not.toBeInTheDocument();

      const doneButton = screen.getByRole("button", { name: /done/i });
      await userEvent.click(doneButton);

      expect(mockOnClose).toHaveBeenCalledTimes(1);
    });
  });

  describe("Cancel and Reset", () => {
    it("calls onClose and cancelExport IPC when Cancel button clicked", async () => {
      renderWithProviders(
        <ExportWizard item={mockItem} open={true} onClose={mockOnClose} />,
      );

      await waitForPreflightComplete();

      const cancelButton = screen.getByRole("button", { name: /cancel/i });
      await userEvent.click(cancelButton);

      expect(vi.mocked(window.electronAPI.cancelExport)).toHaveBeenCalledTimes(
        1,
      );
      expect(mockOnClose).toHaveBeenCalledTimes(1);
    });

    it("resets state when closed and reopened", async () => {
      const { rerender } = renderWithProviders(
        <ExportWizard item={mockItem} open={true} onClose={mockOnClose} />,
      );

      await navigateToUnlockDevice();

      rerender(
        <ExportWizard item={mockItem} open={false} onClose={mockOnClose} />,
      );
      rerender(
        <ExportWizard item={mockItem} open={true} onClose={mockOnClose} />,
      );

      await waitFor(() => {
        expect(screen.getByText("Preparing to export.")).toBeInTheDocument();
      });
    });
  });

  describe("Device Detection", () => {
    const deviceErrorTests = [
      {
        status: ExportStatus.NO_DEVICE_DETECTED,
        message: /No USB drives detected/i,
      },
      {
        status: ExportStatus.MULTI_DEVICE_DETECTED,
        message: /Too many USB drives detected/i,
      },
      {
        status: ExportStatus.INVALID_DEVICE_DETECTED,
        message: /Either the drive is not encrypted/i,
      },
    ];

    deviceErrorTests.forEach(({ status, message }) => {
      it(`shows error message for ${status}`, async () => {
        vi.mocked(window.electronAPI.initiateExport).mockResolvedValueOnce(
          status,
        );

        renderWithProviders(
          <ExportWizard item={mockItem} open={true} onClose={mockOnClose} />,
        );

        // Wait for preflight to complete
        await waitForPreflightComplete();

        // Click Continue to transition from PREFLIGHT_COMPLETE to INSERT_USB
        const continueButton = screen.getByRole("button", {
          name: /continue/i,
        });
        await userEvent.click(continueButton);

        // Now we should see the error message and retry button
        await waitFor(() => {
          expect(screen.getByText(message)).toBeInTheDocument();
          expect(
            screen.getByRole("button", { name: /retry/i }),
          ).toBeInTheDocument();
          expect(
            screen.queryByRole("button", { name: /continue/i }),
          ).not.toBeInTheDocument();
        });
      });
    });

    it("transitions to UNLOCK_DEVICE when device becomes available after retry", async () => {
      vi.mocked(window.electronAPI.initiateExport)
        .mockResolvedValueOnce(ExportStatus.NO_DEVICE_DETECTED)
        .mockResolvedValueOnce(ExportStatus.DEVICE_LOCKED);

      renderWithProviders(
        <ExportWizard item={mockItem} open={true} onClose={mockOnClose} />,
      );

      // Wait for preflight to complete
      await waitForPreflightComplete();

      // Click Continue to see the error message
      const continueButton = screen.getByRole("button", { name: /continue/i });
      await userEvent.click(continueButton);

      await waitFor(() => {
        expect(screen.getByText(/No USB drives detected/i)).toBeInTheDocument();
      });

      // Click retry - this should automatically transition to UNLOCK_DEVICE when device is detected
      const retryButton = screen.getByRole("button", { name: /retry/i });
      await userEvent.click(retryButton);

      // After retry succeeds with DEVICE_LOCKED, should transition directly to UNLOCK_DEVICE
      await waitFor(() => {
        expect(
          screen.getByText("Enter passphrase for USB drive"),
        ).toBeInTheDocument();
      });
    });
  });

  describe("Unlock Errors", () => {
    const unlockErrorTests = [
      {
        status: ExportStatus.ERROR_UNLOCK_LUKS,
        message: /The passphrase provided did not work/i,
      },
      {
        status: ExportStatus.ERROR_UNLOCK_GENERIC,
        message: /Failed to unlock the drive/i,
      },
    ];

    unlockErrorTests.forEach(({ status, message }) => {
      it(`shows error and stays in unlock state for ${status}`, async () => {
        vi.mocked(window.electronAPI.export).mockResolvedValueOnce(status);

        renderWithProviders(
          <ExportWizard item={mockItem} open={true} onClose={mockOnClose} />,
        );

        await navigateToUnlockDevice();
        await submitPassphrase("wrong-passphrase");

        await waitFor(() => {
          expect(screen.getByText(message)).toBeInTheDocument();
          expect(screen.getByLabelText("Passphrase")).toHaveValue("");
        });
      });
    });

    it("allows retry after unlock error and succeeds", async () => {
      vi.mocked(window.electronAPI.export)
        .mockResolvedValueOnce(ExportStatus.ERROR_UNLOCK_LUKS)
        .mockResolvedValueOnce(ExportStatus.SUCCESS_EXPORT);

      renderWithProviders(
        <ExportWizard item={mockItem} open={true} onClose={mockOnClose} />,
      );

      await navigateToUnlockDevice();
      await submitPassphrase("wrong-passphrase");

      await waitFor(() => {
        expect(
          screen.getByText(/The passphrase provided did not work/i),
        ).toBeInTheDocument();
      });

      await submitPassphrase("correct-passphrase");

      await waitFor(() => {
        expect(screen.getByText("Export Successful")).toBeInTheDocument();
      });
    });
  });

  describe("Export Errors", () => {
    const partialSuccessTests = [
      {
        status: ExportStatus.ERROR_EXPORT_CLEANUP,
        message: /some temporary files remain on disk/i,
      },
      {
        status: ExportStatus.ERROR_UNMOUNT_VOLUME_BUSY,
        message: /USB drive could not be unmounted/i,
      },
    ];

    partialSuccessTests.forEach(({ status, message }) => {
      it(`shows partial success warning for ${status}`, async () => {
        vi.mocked(window.electronAPI.export).mockResolvedValueOnce(status);

        renderWithProviders(
          <ExportWizard item={mockItem} open={true} onClose={mockOnClose} />,
        );

        await navigateToUnlockDevice();
        await submitPassphrase("test-passphrase");

        await waitFor(() => {
          expect(
            screen.getByText(/Export successful, but drive was not locked/i),
          ).toBeInTheDocument();
          expect(screen.getByText(message)).toBeInTheDocument();
          expect(
            screen.getByRole("button", { name: /done/i }),
          ).toBeInTheDocument();
        });
      });
    });

    const unrecoverableErrorTests = [
      { status: ExportStatus.ERROR_MOUNT, message: /Error mounting drive/i },
      { status: ExportStatus.ERROR_EXPORT, message: /Error during export/i },
      {
        status: DeviceErrorStatus.ERROR_MISSING_FILES,
        message: /Files were moved or missing/i,
      },
      {
        status: ExportStatus.DEVICE_ERROR,
        message: /Error encountered with this drive/i,
      },
      {
        status: DeviceErrorStatus.UNEXPECTED_RETURN_STATUS,
        message: /Error encountered. Please contact support/i,
      },
    ];

    unrecoverableErrorTests.forEach(({ status, message }) => {
      it(`shows fatal error for ${status}`, async () => {
        vi.mocked(window.electronAPI.export).mockResolvedValueOnce(status);

        renderWithProviders(
          <ExportWizard item={mockItem} open={true} onClose={mockOnClose} />,
        );

        await navigateToUnlockDevice();
        await submitPassphrase("test-passphrase");

        await waitFor(() => {
          expect(screen.getByText("Export Failed")).toBeInTheDocument();
          expect(screen.getByText(message)).toBeInTheDocument();
          const closeButtons = screen.getAllByRole("button", {
            name: /close/i,
          });
          expect(closeButtons.length).toBeGreaterThanOrEqual(1);
        });
      });
    });
  });
});
