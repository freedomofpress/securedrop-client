import { screen, waitFor } from "@testing-library/react";
import { expect, describe, it, vi, beforeEach, afterEach } from "vitest";
import userEvent from "@testing-library/user-event";
import { ExportWizard } from "./Export";
import { FetchStatus, type Item } from "../../../../../../types";
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

  beforeEach(() => {
    vi.clearAllMocks();
  });

  afterEach(() => {
    vi.restoreAllMocks();
  });

  describe("Initial State", () => {
    it("renders nothing when not open", () => {
      renderWithProviders(
        <ExportWizard item={mockItem} open={false} onClose={mockOnClose} />,
      );

      expect(screen.queryByRole("dialog")).not.toBeInTheDocument();
    });

    it("renders the modal when open", async () => {
      renderWithProviders(
        <ExportWizard item={mockItem} open={true} onClose={mockOnClose} />,
      );

      await waitFor(() => {
        expect(screen.getByRole("dialog")).toBeInTheDocument();
      });
    });

    it("displays preflight state with risk warnings on initial open", async () => {
      renderWithProviders(
        <ExportWizard item={mockItem} open={true} onClose={mockOnClose} />,
      );

      await waitFor(() => {
        expect(screen.getByText("Preparing to export.")).toBeInTheDocument();
        expect(
          screen.getByText("Understand the risks before exporting files"),
        ).toBeInTheDocument();
        expect(screen.getByText("Malware")).toBeInTheDocument();
        expect(screen.getByText("Anonymity")).toBeInTheDocument();
      });
    });

    it("displays the filename in preflight state", async () => {
      renderWithProviders(
        <ExportWizard item={mockItem} open={true} onClose={mockOnClose} />,
      );

      await waitFor(() => {
        expect(screen.getByText("testfile.pdf")).toBeInTheDocument();
      });
    });

    it("shows Continue and Cancel buttons in preflight state", async () => {
      renderWithProviders(
        <ExportWizard item={mockItem} open={true} onClose={mockOnClose} />,
      );

      await waitFor(() => {
        const continueButton = screen.getByRole("button", {
          name: /continue/i,
        });
        const cancelButton = screen.getByRole("button", { name: /cancel/i });

        expect(continueButton).toBeInTheDocument();
        expect(continueButton).toBeDisabled(); // Disabled during preflight
        expect(cancelButton).toBeInTheDocument();
      });
    });

    it("prevents modal from being closed during preflight state", async () => {
      renderWithProviders(
        <ExportWizard item={mockItem} open={true} onClose={mockOnClose} />,
      );

      await waitFor(() => {
        const dialog = screen.getByRole("dialog");
        expect(dialog).toBeInTheDocument();
      });

      // Modal should not have a close button during preflight
      const closeButton = screen.queryByRole("button", { name: /close/i });
      expect(closeButton).not.toBeInTheDocument();
    });
  });

  describe("Preflight State Machine", () => {
    it("automatically transitions from PREFLIGHT to PREFLIGHT_COMPLETE after delay", async () => {
      renderWithProviders(
        <ExportWizard item={mockItem} open={true} onClose={mockOnClose} />,
      );

      // Initially in PREFLIGHT state
      await waitFor(() => {
        expect(screen.getByText("Preparing to export.")).toBeInTheDocument();
      });

      // Wait for auto-transition (1.5 seconds + buffer)
      await waitFor(
        () => {
          const continueButton = screen.getByRole("button", {
            name: /continue/i,
          });
          expect(continueButton).not.toBeDisabled();
        },
        { timeout: 2000 },
      );
    });

    it("shows loading spinner during preflight", async () => {
      renderWithProviders(
        <ExportWizard item={mockItem} open={true} onClose={mockOnClose} />,
      );

      await waitFor(() => {
        // Check for spinner by checking if there's an element with animate-spin class
        const spinner = document.querySelector(".animate-spin");
        expect(spinner).toBeInTheDocument();
      });
    });
  });

  describe("Ready State", () => {
    it("transitions to READY state after preflight complete and clicking Continue", async () => {
      renderWithProviders(
        <ExportWizard item={mockItem} open={true} onClose={mockOnClose} />,
      );

      // Wait for preflight to complete
      await waitFor(
        () => {
          const continueButton = screen.getByRole("button", {
            name: /continue/i,
          });
          expect(continueButton).not.toBeDisabled();
        },
        { timeout: 2000 },
      );

      // Click Continue
      const continueButton = screen.getByRole("button", { name: /continue/i });
      await userEvent.click(continueButton);

      // Should now be in READY state
      await waitFor(() => {
        expect(screen.getByText("Ready to export.")).toBeInTheDocument();
        expect(
          screen.getByText(/Please insert one of the export drives/i),
        ).toBeInTheDocument();
      });
    });

    it("shows Back, Continue, and Cancel buttons in READY state", async () => {
      renderWithProviders(
        <ExportWizard item={mockItem} open={true} onClose={mockOnClose} />,
      );

      // Wait and click Continue to reach READY state
      await waitFor(
        async () => {
          const continueButton = screen.getByRole("button", {
            name: /continue/i,
          });
          expect(continueButton).not.toBeDisabled();
          await userEvent.click(continueButton);
        },
        { timeout: 2000 },
      );

      await waitFor(() => {
        expect(screen.getByText("Ready to export.")).toBeInTheDocument();
      });

      expect(screen.getByRole("button", { name: /back/i })).toBeInTheDocument();
      expect(
        screen.getByRole("button", { name: /continue/i }),
      ).toBeInTheDocument();
      expect(
        screen.getByRole("button", { name: /cancel/i }),
      ).toBeInTheDocument();
    });

    it("goes back to PREFLIGHT_COMPLETE when Back button is clicked in READY state", async () => {
      renderWithProviders(
        <ExportWizard item={mockItem} open={true} onClose={mockOnClose} />,
      );

      // Reach READY state
      await waitFor(
        async () => {
          const continueButton = screen.getByRole("button", {
            name: /continue/i,
          });
          expect(continueButton).not.toBeDisabled();
          await userEvent.click(continueButton);
        },
        { timeout: 2000 },
      );

      await waitFor(() => {
        expect(screen.getByText("Ready to export.")).toBeInTheDocument();
      });

      // Click Back
      const backButton = screen.getByRole("button", { name: /back/i });
      await userEvent.click(backButton);

      // Should be back at PREFLIGHT_COMPLETE (which shows same content as PREFLIGHT but enabled button)
      await waitFor(() => {
        expect(screen.getByText("Preparing to export.")).toBeInTheDocument();
      });
    });
  });

  describe("Unlock Device State", () => {
    it("transitions to UNLOCK_DEVICE state when Continue clicked in READY state", async () => {
      renderWithProviders(
        <ExportWizard item={mockItem} open={true} onClose={mockOnClose} />,
      );

      // Reach READY state
      await waitFor(
        async () => {
          const continueButton = screen.getByRole("button", {
            name: /continue/i,
          });
          expect(continueButton).not.toBeDisabled();
          await userEvent.click(continueButton);
        },
        { timeout: 2000 },
      );

      await waitFor(() => {
        expect(screen.getByText("Ready to export.")).toBeInTheDocument();
      });

      // Click Continue again to go to unlock
      const continueButton = screen.getByRole("button", { name: /continue/i });
      await userEvent.click(continueButton);

      // Should now be in UNLOCK_DEVICE state
      await waitFor(() => {
        expect(
          screen.getByText("Enter passphrase for USB drive"),
        ).toBeInTheDocument();
        expect(screen.getByLabelText("Passphrase")).toBeInTheDocument();
      });
    });

    it("displays passphrase input field in unlock state", async () => {
      renderWithProviders(
        <ExportWizard item={mockItem} open={true} onClose={mockOnClose} />,
      );

      // Navigate to UNLOCK_DEVICE state
      await waitFor(
        async () => {
          const continueButton = screen.getByRole("button", {
            name: /continue/i,
          });
          expect(continueButton).not.toBeDisabled();
          await userEvent.click(continueButton);
        },
        { timeout: 2000 },
      );

      await waitFor(async () => {
        const continueButton = screen.getByRole("button", {
          name: /continue/i,
        });
        await userEvent.click(continueButton);
      });

      await waitFor(async () => {
        const continueButton = screen.getByRole("button", {
          name: /continue/i,
        });
        await userEvent.click(continueButton);
      });

      await waitFor(() => {
        const passphraseInput = screen.getByLabelText("Passphrase");
        expect(passphraseInput).toBeInTheDocument();
        expect(passphraseInput).toHaveAttribute("type", "password");
      });
    });

    it("disables Continue button when passphrase is empty", async () => {
      renderWithProviders(
        <ExportWizard item={mockItem} open={true} onClose={mockOnClose} />,
      );

      // Navigate to UNLOCK_DEVICE state
      await waitFor(
        async () => {
          const continueButton = screen.getByRole("button", {
            name: /continue/i,
          });
          expect(continueButton).not.toBeDisabled();
          await userEvent.click(continueButton);
        },
        { timeout: 2000 },
      );

      await waitFor(async () => {
        const continueButton = screen.getByRole("button", {
          name: /continue/i,
        });
        await userEvent.click(continueButton);
      });

      await waitFor(async () => {
        const continueButton = screen.getByRole("button", {
          name: /continue/i,
        });
        await userEvent.click(continueButton);
      });

      await waitFor(() => {
        expect(
          screen.getByText("Enter passphrase for USB drive"),
        ).toBeInTheDocument();
      });

      const continueButton = screen.getByRole("button", { name: /continue/i });
      expect(continueButton).toBeDisabled();
    });

    it("enables Continue button when passphrase is entered", async () => {
      renderWithProviders(
        <ExportWizard item={mockItem} open={true} onClose={mockOnClose} />,
      );

      // Navigate to UNLOCK_DEVICE state
      await waitFor(
        async () => {
          const continueButton = screen.getByRole("button", {
            name: /continue/i,
          });
          expect(continueButton).not.toBeDisabled();
          await userEvent.click(continueButton);
        },
        { timeout: 2000 },
      );

      await waitFor(async () => {
        const continueButton = screen.getByRole("button", {
          name: /continue/i,
        });
        await userEvent.click(continueButton);
      });

      await waitFor(async () => {
        const continueButton = screen.getByRole("button", {
          name: /continue/i,
        });
        await userEvent.click(continueButton);
      });

      await waitFor(() => {
        expect(screen.getByLabelText("Passphrase")).toBeInTheDocument();
      });

      // Type passphrase
      const passphraseInput = screen.getByLabelText("Passphrase");
      await userEvent.type(passphraseInput, "test-passphrase-123");

      // Continue button should now be enabled
      const continueButton = screen.getByRole("button", { name: /continue/i });
      expect(continueButton).not.toBeDisabled();
    });

    it("goes back to READY state when Back button is clicked in UNLOCK_DEVICE state", async () => {
      renderWithProviders(
        <ExportWizard item={mockItem} open={true} onClose={mockOnClose} />,
      );

      // Navigate to UNLOCK_DEVICE state
      await waitFor(
        async () => {
          const continueButton = screen.getByRole("button", {
            name: /continue/i,
          });
          expect(continueButton).not.toBeDisabled();
          await userEvent.click(continueButton);
        },
        { timeout: 2000 },
      );

      await waitFor(async () => {
        const continueButton = screen.getByRole("button", {
          name: /continue/i,
        });
        await userEvent.click(continueButton);
      });

      await waitFor(async () => {
        const continueButton = screen.getByRole("button", {
          name: /continue/i,
        });
        await userEvent.click(continueButton);
      });

      await waitFor(() => {
        expect(screen.getByLabelText("Passphrase")).toBeInTheDocument();
      });

      // Click Back
      const backButton = screen.getByRole("button", { name: /back/i });
      await userEvent.click(backButton);

      // Should be back at READY state
      await waitFor(() => {
        expect(screen.getByText("Ready to export.")).toBeInTheDocument();
      });
    });
  });

  // TODO(vicki): add tests for EXPORTING state when API call is implemented

  describe("Success State", () => {
    it("transitions to SUCCESS state after successful export", async () => {
      renderWithProviders(
        <ExportWizard item={mockItem} open={true} onClose={mockOnClose} />,
      );

      // Navigate through all states to trigger export
      await waitFor(
        async () => {
          const continueButton = screen.getByRole("button", {
            name: /continue/i,
          });
          expect(continueButton).not.toBeDisabled();
          await userEvent.click(continueButton);
        },
        { timeout: 2000 },
      );

      await waitFor(async () => {
        const continueButton = screen.getByRole("button", {
          name: /continue/i,
        });
        await userEvent.click(continueButton);
      });

      await waitFor(async () => {
        const continueButton = screen.getByRole("button", {
          name: /continue/i,
        });
        await userEvent.click(continueButton);
      });

      await waitFor(() => {
        expect(screen.getByLabelText("Passphrase")).toBeInTheDocument();
      });

      const passphraseInput = screen.getByLabelText("Passphrase");
      await userEvent.type(passphraseInput, "test-passphrase");

      const continueButton = screen.getByRole("button", { name: /continue/i });
      await userEvent.click(continueButton);

      // Wait for success state
      await waitFor(() => {
        expect(screen.getByText("Export Successful")).toBeInTheDocument();
        expect(
          screen.getByText(
            /Remember to be careful when working with files outside/i,
          ),
        ).toBeInTheDocument();
      });
    });

    it("shows only Done button in success state", async () => {
      renderWithProviders(
        <ExportWizard item={mockItem} open={true} onClose={mockOnClose} />,
      );

      // Navigate to SUCCESS state
      await waitFor(
        async () => {
          const continueButton = screen.getByRole("button", {
            name: /continue/i,
          });
          expect(continueButton).not.toBeDisabled();
          await userEvent.click(continueButton);
        },
        { timeout: 2000 },
      );

      await waitFor(async () => {
        const continueButton = screen.getByRole("button", {
          name: /continue/i,
        });
        await userEvent.click(continueButton);
      });

      await waitFor(async () => {
        const continueButton = screen.getByRole("button", {
          name: /continue/i,
        });
        await userEvent.click(continueButton);
      });

      await waitFor(() => {
        expect(screen.getByLabelText("Passphrase")).toBeInTheDocument();
      });

      const passphraseInput = screen.getByLabelText("Passphrase");
      await userEvent.type(passphraseInput, "test-passphrase");

      const continueButton = screen.getByRole("button", { name: /continue/i });
      await userEvent.click(continueButton);

      await waitFor(() => {
        expect(screen.getByText("Export Successful")).toBeInTheDocument();
      });

      // Should only have Done button
      expect(screen.getByRole("button", { name: /done/i })).toBeInTheDocument();
      expect(
        screen.queryByRole("button", { name: /continue/i }),
      ).not.toBeInTheDocument();
      expect(
        screen.queryByRole("button", { name: /back/i }),
      ).not.toBeInTheDocument();
      expect(
        screen.queryByRole("button", { name: /cancel/i }),
      ).not.toBeInTheDocument();
    });

    it("calls onClose when Done button is clicked", async () => {
      renderWithProviders(
        <ExportWizard item={mockItem} open={true} onClose={mockOnClose} />,
      );

      // Navigate to SUCCESS state
      await waitFor(
        async () => {
          const continueButton = screen.getByRole("button", {
            name: /continue/i,
          });
          expect(continueButton).not.toBeDisabled();
          await userEvent.click(continueButton);
        },
        { timeout: 2000 },
      );

      await waitFor(async () => {
        const continueButton = screen.getByRole("button", {
          name: /continue/i,
        });
        await userEvent.click(continueButton);
      });

      await waitFor(async () => {
        const continueButton = screen.getByRole("button", {
          name: /continue/i,
        });
        await userEvent.click(continueButton);
      });

      await waitFor(() => {
        expect(screen.getByLabelText("Passphrase")).toBeInTheDocument();
      });

      const passphraseInput = screen.getByLabelText("Passphrase");
      await userEvent.type(passphraseInput, "test-passphrase");

      const continueButton = screen.getByRole("button", { name: /continue/i });
      await userEvent.click(continueButton);

      await waitFor(() => {
        expect(screen.getByText("Export Successful")).toBeInTheDocument();
      });

      const doneButton = screen.getByRole("button", { name: /done/i });
      await userEvent.click(doneButton);

      expect(mockOnClose).toHaveBeenCalledTimes(1);
    });
  });

  describe("Cancel Functionality", () => {
    it("calls onClose when Cancel button is clicked", async () => {
      renderWithProviders(
        <ExportWizard item={mockItem} open={true} onClose={mockOnClose} />,
      );

      // Wait for modal to open
      await waitFor(() => {
        expect(screen.getByRole("dialog")).toBeInTheDocument();
      });

      // Wait for preflight to complete
      await waitFor(
        () => {
          const continueButton = screen.getByRole("button", {
            name: /continue/i,
          });
          expect(continueButton).not.toBeDisabled();
        },
        { timeout: 2000 },
      );

      const cancelButton = screen.getByRole("button", { name: /cancel/i });
      await userEvent.click(cancelButton);

      expect(mockOnClose).toHaveBeenCalledTimes(1);
    });

    it("resets wizard state when modal is closed and reopened", async () => {
      const { rerender } = renderWithProviders(
        <ExportWizard item={mockItem} open={true} onClose={mockOnClose} />,
      );

      // Navigate to READY state
      await waitFor(
        async () => {
          const continueButton = screen.getByRole("button", {
            name: /continue/i,
          });
          expect(continueButton).not.toBeDisabled();
          await userEvent.click(continueButton);
        },
        { timeout: 2000 },
      );

      await waitFor(() => {
        expect(screen.getByText("Ready to export.")).toBeInTheDocument();
      });

      // Close the modal
      rerender(
        <ExportWizard item={mockItem} open={false} onClose={mockOnClose} />,
      );

      // Reopen the modal
      rerender(
        <ExportWizard item={mockItem} open={true} onClose={mockOnClose} />,
      );

      // Should be back at initial PREFLIGHT state
      await waitFor(() => {
        expect(screen.getByText("Preparing to export.")).toBeInTheDocument();
        expect(
          screen.getByText("Understand the risks before exporting files"),
        ).toBeInTheDocument();
      });
    });
  });

  describe("ElectronAPI Integration", () => {
    it("successfully completes export flow (stub implementation)", async () => {
      renderWithProviders(
        <ExportWizard item={mockItem} open={true} onClose={mockOnClose} />,
      );

      // Navigate through all states to trigger export
      await waitFor(
        async () => {
          const continueButton = screen.getByRole("button", {
            name: /continue/i,
          });
          expect(continueButton).not.toBeDisabled();
          await userEvent.click(continueButton);
        },
        { timeout: 2000 },
      );

      await waitFor(async () => {
        const continueButton = screen.getByRole("button", {
          name: /continue/i,
        });
        await userEvent.click(continueButton);
      });

      await waitFor(async () => {
        const continueButton = screen.getByRole("button", {
          name: /continue/i,
        });
        await userEvent.click(continueButton);
      });

      await waitFor(() => {
        expect(screen.getByLabelText("Passphrase")).toBeInTheDocument();
      });

      const passphraseInput = screen.getByLabelText("Passphrase");
      await userEvent.type(passphraseInput, "test-passphrase");

      const continueButton = screen.getByRole("button", { name: /continue/i });
      await userEvent.click(continueButton);

      // Wait for success state (export API call is TODO/stubbed currently)
      await waitFor(() => {
        expect(screen.getByText("Export Successful")).toBeInTheDocument();
      });
    });
  });
});
