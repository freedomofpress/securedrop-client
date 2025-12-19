import { screen, waitFor } from "@testing-library/react";
import { expect, describe, it, vi, beforeEach, afterEach } from "vitest";
import userEvent from "@testing-library/user-event";
import { PrintWizard } from "./Print";
import { PrintStatus, FetchStatus, type Item } from "../../../../../../types";
import { renderWithProviders } from "../../../../../test-component-setup";

describe("PrintWizard Component", () => {
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

  // Helper: Wait for preflight to complete and return continue button
  const waitForPreflightComplete = async () => {
    await waitFor(() => {
      const continueButton = screen.getByRole("button", { name: /continue/i });
      expect(continueButton).not.toBeDisabled();
    });
    return screen.getByRole("button", { name: /continue/i });
  };

  // Helper: Navigate through preflight and start printing
  const navigateToPrinting = async () => {
    const continueButton = await waitForPreflightComplete();
    await userEvent.click(continueButton);
  };

  beforeEach(() => {
    vi.clearAllMocks();
  });

  afterEach(() => {
    vi.restoreAllMocks();
  });

  describe("Initial State", () => {
    it("renders nothing when not open", () => {
      renderWithProviders(
        <PrintWizard item={mockItem} open={false} onClose={mockOnClose} />,
      );

      expect(screen.queryByRole("dialog")).not.toBeInTheDocument();
    });

    it("displays preflight state with all required content when open", async () => {
      renderWithProviders(
        <PrintWizard item={mockItem} open={true} onClose={mockOnClose} />,
      );

      await waitFor(() => {
        expect(screen.getByRole("dialog")).toBeInTheDocument();
        expect(screen.getByText("Preparing to print.")).toBeInTheDocument();
        expect(
          screen.getByText("Understand the risks before printing files"),
        ).toBeInTheDocument();
        expect(screen.getByText("Malware")).toBeInTheDocument();
        expect(screen.getByText("Anonymity")).toBeInTheDocument();
        expect(screen.getByText("testfile.pdf")).toBeInTheDocument();

        const continueButton = screen.getByRole("button", {
          name: /continue/i,
        });
        expect(continueButton).toBeDisabled();
        expect(
          screen.getByRole("button", { name: /cancel/i }),
        ).toBeInTheDocument();

        // Loading spinner should be visible during preflight
        expect(document.querySelector(".animate-spin")).toBeInTheDocument();
      });
    });

    it("prevents modal from being closed during preflight state", async () => {
      vi.mocked(window.electronAPI.initiatePrint).mockImplementationOnce(
        () =>
          new Promise((resolve) =>
            setTimeout(() => resolve(PrintStatus.PRINT_PREFLIGHT_SUCCESS), 100),
          ),
      );

      renderWithProviders(
        <PrintWizard item={mockItem} open={true} onClose={mockOnClose} />,
      );

      await waitFor(() => {
        expect(document.querySelector(".animate-spin")).toBeInTheDocument();
      });

      expect(screen.queryByLabelText("Close")).not.toBeInTheDocument();
    });
  });

  describe("Preflight State Machine", () => {
    it("automatically transitions to PREFLIGHT_COMPLETE on success", async () => {
      renderWithProviders(
        <PrintWizard item={mockItem} open={true} onClose={mockOnClose} />,
      );

      await waitFor(() => {
        expect(
          vi.mocked(window.electronAPI.initiatePrint),
        ).toHaveBeenCalledTimes(1);
      });

      const continueButton = await waitForPreflightComplete();
      expect(screen.getByText("Preparing to print.")).toBeInTheDocument();
      expect(
        screen.getByText("Understand the risks before printing files"),
      ).toBeInTheDocument();
      expect(continueButton).not.toBeDisabled();
      expect(
        screen.getByRole("button", { name: /cancel/i }),
      ).toBeInTheDocument();
    });

    it("transitions to CONNECT_PRINTER state when no printer found", async () => {
      vi.mocked(window.electronAPI.initiatePrint).mockResolvedValueOnce(
        PrintStatus.ERROR_PRINTER_NOT_FOUND,
      );

      renderWithProviders(
        <PrintWizard item={mockItem} open={true} onClose={mockOnClose} />,
      );

      // First show PREFLIGHT_COMPLETE state
      const continueButton = await waitForPreflightComplete();
      expect(continueButton).not.toBeDisabled();
      await userEvent.click(continueButton);

      // Now should show the CONNECT_PRINTER state
      await waitFor(() => {
        expect(screen.getByText("Ready to print.")).toBeInTheDocument();
        expect(
          screen.getByText(/Please connect a printer to continue/i),
        ).toBeInTheDocument();
        expect(screen.getByText(/No printer found/i)).toBeInTheDocument();
        expect(
          screen.getByRole("button", { name: /retry/i }),
        ).toBeInTheDocument();
      });
    });

    it("handles initiatePrint exception", async () => {
      vi.mocked(window.electronAPI.initiatePrint).mockRejectedValueOnce(
        new Error("Failed to connect to printer service"),
      );

      renderWithProviders(
        <PrintWizard item={mockItem} open={true} onClose={mockOnClose} />,
      );

      await waitFor(() => {
        expect(screen.getByText("Print Failed")).toBeInTheDocument();
      });
    });
  });

  describe("Printing State", () => {
    it("displays printing state and prevents modal close", async () => {
      vi.mocked(window.electronAPI.print).mockImplementationOnce(
        () =>
          new Promise((resolve) =>
            setTimeout(() => resolve(PrintStatus.PRINT_SUCCESS), 200),
          ),
      );

      renderWithProviders(
        <PrintWizard item={mockItem} open={true} onClose={mockOnClose} />,
      );

      await navigateToPrinting();

      await waitFor(() => {
        expect(screen.getByText("Please wait...")).toBeInTheDocument();
        expect(
          screen.getByText(/Remember to be careful when working with files/i),
        ).toBeInTheDocument();
      });

      // No buttons or close option during print
      expect(
        screen.queryByRole("button", { name: /continue/i }),
      ).not.toBeInTheDocument();
      expect(
        screen.queryByRole("button", { name: /cancel/i }),
      ).not.toBeInTheDocument();
      expect(screen.queryByLabelText("Close")).not.toBeInTheDocument();
    });

    it("calls print API with correct parameters", async () => {
      renderWithProviders(
        <PrintWizard item={mockItem} open={true} onClose={mockOnClose} />,
      );

      await navigateToPrinting();

      await waitFor(() => {
        expect(vi.mocked(window.electronAPI.print)).toHaveBeenCalledWith(
          mockItem.uuid,
        );
      });
    });
  });

  describe("Success State", () => {
    it("auto-closes modal on successful print", async () => {
      renderWithProviders(
        <PrintWizard item={mockItem} open={true} onClose={mockOnClose} />,
      );

      await navigateToPrinting();

      // Wait for success state and auto-close
      await waitFor(() => {
        expect(mockOnClose).toHaveBeenCalledTimes(1);
      });
    });
  });

  describe("Error State", () => {
    it.each([
      [PrintStatus.ERROR_PRINTER_NOT_FOUND, /No printer found/i],
      [PrintStatus.ERROR_PRINT, /An error occurred while printing the file/i],
      [PrintStatus.ERROR_UNPRINTABLE_TYPE, /This file type cannot be printed/i],
      [
        PrintStatus.ERROR_MIMETYPE_UNSUPPORTED,
        /The file format is not supported for printing/i,
      ],
      [
        PrintStatus.ERROR_MIMETYPE_DISCOVERY,
        /Could not determine the file type/i,
      ],
      [PrintStatus.ERROR_UNKNOWN, /An unknown error occurred while printing/i],
    ])(
      "displays correct error message for %s",
      async (errorStatus, expectedMessage) => {
        vi.mocked(window.electronAPI.print).mockResolvedValueOnce(errorStatus);

        renderWithProviders(
          <PrintWizard item={mockItem} open={true} onClose={mockOnClose} />,
        );

        await navigateToPrinting();

        await waitFor(() => {
          expect(screen.getByText("Print Failed")).toBeInTheDocument();
          expect(screen.getByText(expectedMessage)).toBeInTheDocument();
        });
      },
    );

    it("handles print exception", async () => {
      vi.mocked(window.electronAPI.print).mockRejectedValueOnce(
        new Error("Printer connection failed"),
      );

      renderWithProviders(
        <PrintWizard item={mockItem} open={true} onClose={mockOnClose} />,
      );

      await navigateToPrinting();

      await waitFor(() => {
        expect(screen.getByText("Print Failed")).toBeInTheDocument();
      });
    });

    it("shows Close button and closes modal on click", async () => {
      vi.mocked(window.electronAPI.print).mockResolvedValueOnce(
        PrintStatus.ERROR_PRINT,
      );

      renderWithProviders(
        <PrintWizard item={mockItem} open={true} onClose={mockOnClose} />,
      );

      await navigateToPrinting();

      await waitFor(() => {
        expect(screen.getByText("Print Failed")).toBeInTheDocument();
      });

      const closeButtons = screen.getAllByRole("button", { name: /close/i });
      expect(closeButtons.length).toBeGreaterThanOrEqual(1);

      await userEvent.click(closeButtons[0]);
      expect(mockOnClose).toHaveBeenCalledTimes(1);
    });
  });

  describe("Cancel and Reset", () => {
    it("calls onClose and cancelPrint IPC when Cancel button is clicked", async () => {
      renderWithProviders(
        <PrintWizard item={mockItem} open={true} onClose={mockOnClose} />,
      );

      await waitForPreflightComplete();
      await userEvent.click(screen.getByRole("button", { name: /cancel/i }));

      expect(vi.mocked(window.electronAPI.cancelPrint)).toHaveBeenCalledTimes(
        1,
      );
      expect(mockOnClose).toHaveBeenCalledTimes(1);
    });

    it("resets wizard state when modal is closed and reopened", async () => {
      vi.mocked(window.electronAPI.print).mockImplementationOnce(
        () =>
          new Promise((resolve) =>
            setTimeout(() => resolve(PrintStatus.PRINT_SUCCESS), 200),
          ),
      );

      const { rerender } = renderWithProviders(
        <PrintWizard item={mockItem} open={true} onClose={mockOnClose} />,
      );

      await navigateToPrinting();

      await waitFor(() => {
        expect(screen.getByText("Please wait...")).toBeInTheDocument();
      });

      // Close and reopen modal
      rerender(
        <PrintWizard item={mockItem} open={false} onClose={mockOnClose} />,
      );
      rerender(
        <PrintWizard item={mockItem} open={true} onClose={mockOnClose} />,
      );

      // Should be back at initial PREFLIGHT state
      await waitFor(() => {
        expect(screen.getByText("Preparing to print.")).toBeInTheDocument();
        expect(
          screen.getByText("Understand the risks before printing files"),
        ).toBeInTheDocument();
      });
    });
  });

  describe("Filename Handling", () => {
    it.each([
      ["/very/long/path/to/document.pdf", "document.pdf"],
      ["simple.pdf", "simple.pdf"],
      ["", ""],
    ])("displays filename correctly: %s -> %s", async (filename, expected) => {
      const itemWithFilename: Item = { ...mockItem, filename };

      renderWithProviders(
        <PrintWizard
          item={itemWithFilename}
          open={true}
          onClose={mockOnClose}
        />,
      );

      await waitFor(() => {
        expect(screen.getByRole("dialog")).toBeInTheDocument();
      });

      if (expected) {
        expect(screen.getByText(expected)).toBeInTheDocument();
      } else {
        expect(screen.queryByText("testfile.pdf")).not.toBeInTheDocument();
      }
    });
  });

  describe("Full Print Flow", () => {
    it("successfully completes entire print flow and auto-closes", async () => {
      const initiatePrintMock = vi.mocked(window.electronAPI.initiatePrint);
      const printMock = vi.mocked(window.electronAPI.print);

      renderWithProviders(
        <PrintWizard item={mockItem} open={true} onClose={mockOnClose} />,
      );

      // Verify preflight
      await waitFor(() => {
        expect(initiatePrintMock).toHaveBeenCalledTimes(1);
      });

      await navigateToPrinting();

      // Verify print was called and modal auto-closed
      await waitFor(() => {
        expect(printMock).toHaveBeenCalledWith(mockItem.uuid);
        expect(mockOnClose).toHaveBeenCalledTimes(1);
      });
    });
  });
});
