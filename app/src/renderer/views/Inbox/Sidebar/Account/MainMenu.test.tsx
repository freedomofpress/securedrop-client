import { screen, waitFor } from "@testing-library/react";
import { expect, describe, it, vi, beforeEach, afterEach } from "vitest";
import userEvent from "@testing-library/user-event";
import { renderWithProviders } from "../../../../test-component-setup";

import { SessionStatus } from "../../../../features/session/sessionSlice";
import { RootState } from "../../../../store";
import { SyncStatus, JournalistMetadata } from "../../../../../types";
import MainMenu from "./MainMenu";
import { requestHelp } from "../../../../components/helpRequester";

vi.mock("../../../../components/helpRequester", () => ({
  requestHelp: vi.fn(),
}));

// Mock useNavigate
const mockNavigate = vi.fn();
vi.mock("react-router", async (importOriginal) => {
  const actual = await importOriginal<typeof import("react-router")>();
  return {
    ...actual,
    useNavigate: () => mockNavigate,
  };
});

describe("Journalist Menu Component", () => {
  const mockJournalists: Array<{ uuid: string; data: JournalistMetadata }> = [
    {
      uuid: "journalist-1",
      data: {
        uuid: "journalist-1",
        username: "dellsberg",
        first_name: "Daniel",
        last_name: "Ellsberg",
      },
    },
    {
      uuid: "journalist-2",
      data: {
        uuid: "journalist-2",
        username: "journalist",
        first_name: null,
        last_name: null,
      },
    },
  ];

  beforeEach(() => {
    vi.clearAllMocks();
    mockNavigate.mockClear();
  });

  afterEach(() => {
    vi.restoreAllMocks();
  });

  describe("When journalist is not logged in", () => {
    const testState: Partial<RootState> = {
      session: {
        status: SessionStatus.Unauth,
        authData: undefined,
      },
    };
    it("should show the offline sync indicator and not show a journalist name", () => {
      renderWithProviders(<MainMenu />, { preloadedState: testState });
      expect(screen.getByText("Offline Mode")).toBeInTheDocument();
      const hexElement = screen.getByLabelText(/sync: not logged in/i);
      expect(hexElement).toBeInTheDocument();
    });

    it("The Sync Now menu item should be disabled and a sign in item should be displayed", async () => {
      renderWithProviders(<MainMenu />, { preloadedState: testState });
      const menuTrigger = screen.getByText("Offline Mode");
      expect(menuTrigger).toBeInTheDocument();
      await userEvent.click(menuTrigger);

      await waitFor(() => {
        const menu = screen.getByRole("menu");
        expect(menu).toBeInTheDocument();

        const syncNowItem = screen.getByRole("menuitem", {
          name: /^sync now/i,
        });
        expect(syncNowItem).toBeInTheDocument();
        expect(syncNowItem).toHaveClass("ant-dropdown-menu-item-disabled");

        const signoutItem = screen.queryByRole("menuitem", {
          name: /^sign out/i,
        });
        expect(signoutItem).not.toBeInTheDocument();
        const signinItem = screen.queryByRole("menuitem", {
          name: /^sign in/i,
        });
        expect(signinItem).toBeInTheDocument();
      });
    });

    it("Sign in should work", async () => {
      renderWithProviders(<MainMenu />, { preloadedState: testState });
      const menuTrigger = screen.getByText("Offline Mode");
      expect(menuTrigger).toBeInTheDocument();
      await userEvent.click(menuTrigger);

      await waitFor(() => {
        const menu = screen.getByRole("menu");
        expect(menu).toBeInTheDocument();

        const signinItem = screen.getByRole("menuitem", {
          name: /^sign in/i,
        });
        expect(signinItem).toBeInTheDocument();
      });
      const signinItem = screen.getByRole("menuitem", {
        name: /^sign in/i,
      });
      await userEvent.click(signinItem);
      expect(mockNavigate).toHaveBeenCalledWith("/sign-in");
    });
  });

  describe("When journalist is logged in and sync is working", () => {
    const authState: Partial<RootState> = {
      session: {
        status: SessionStatus.Auth,
        authData: {
          expiration: "2037-07-16T19:25:44.388054+00:00",
          token: "test-token-123",
          journalistUUID: "journalist-1",
          journalistFirstName: "Daniel",
          journalistLastName: "Ellsberg",
        },
      },
      journalists: {
        journalists: mockJournalists,
        loading: false,
        error: null,
      },
      sync: {
        error: null,
        status: SyncStatus.UPDATED,
        lastSyncStarted: null,
        lastSyncFinished: null,
      },
    };

    it("should show the green sync indicator and a journalist name", () => {
      renderWithProviders(<MainMenu />, { preloadedState: authState });
      expect(screen.getByText("dellsberg")).toBeInTheDocument();
      const hexElement = screen.getByLabelText(/sync: OK/i);
      expect(hexElement).toBeInTheDocument();
    });

    it("The menu should have sync enabled and have a sign out option", async () => {
      renderWithProviders(<MainMenu />, { preloadedState: authState });
      const menuTrigger = screen.getByText("dellsberg");
      expect(menuTrigger).toBeInTheDocument();
      await userEvent.click(menuTrigger);

      await waitFor(() => {
        const menu = screen.getByRole("menu");
        expect(menu).toBeInTheDocument();

        const syncNowItem = screen.getByRole("menuitem", {
          name: /^sync now/i,
        });
        expect(syncNowItem).toBeInTheDocument();
        expect(syncNowItem).not.toHaveClass("ant-dropdown-menu-item-disabled");

        const signoutItem = screen.getByRole("menuitem", {
          name: /^sign out/i,
        });
        expect(signoutItem).toBeInTheDocument();
        const signinItem = screen.queryByRole("menuitem", {
          name: /^sign in/i,
        });
        expect(signinItem).not.toBeInTheDocument();
      });
    });

    it("The about modal should be available", async () => {
      renderWithProviders(<MainMenu />, { preloadedState: authState });

      // we can open the menu
      const menuTrigger = screen.getByText("dellsberg");
      expect(menuTrigger).toBeInTheDocument();
      await userEvent.click(menuTrigger);

      await waitFor(() => {
        const menu = screen.getByRole("menu");
        expect(menu).toBeInTheDocument();

        const helpItem = screen.getByRole("menuitem", {
          name: /^help/i,
        });
        expect(helpItem).toBeInTheDocument();
      });

      // we can open the submenu
      const helpItem = screen.getByRole("menuitem", {
        name: /^help/i,
      });
      await userEvent.hover(helpItem);

      await waitFor(() => {
        const aboutItem = screen.getByRole("menuitem", {
          name: /^about securedrop/i,
        });
        expect(aboutItem).toBeInTheDocument();
      });

      // we can open the about modal
      const aboutItem = screen.getByRole("menuitem", {
        name: /^about securedrop/i,
      });
      await userEvent.click(aboutItem);

      await waitFor(() => {
        const aboutModal = screen.getByRole("dialog");
        const aboutModalContent = screen.getByText(/Aaron Swartz/i);
        expect(aboutModal).toBeInTheDocument();
        expect(aboutModalContent).toBeVisible();
      });
    });

    it("The help modal should be available", async () => {
      renderWithProviders(<MainMenu />, { preloadedState: authState });

      // we can open the menu
      const menuTrigger = screen.getByText("dellsberg");
      expect(menuTrigger).toBeInTheDocument();
      await userEvent.click(menuTrigger);

      await waitFor(() => {
        const menu = screen.getByRole("menu");
        expect(menu).toBeInTheDocument();

        const helpItem = screen.getByRole("menuitem", {
          name: /^help/i,
        });
        expect(helpItem).toBeInTheDocument();
      });

      // we can open the submenu
      const helpItem = screen.getByRole("menuitem", {
        name: /^help/i,
      });
      await userEvent.hover(helpItem);

      await waitFor(() => {
        const keebItem = screen.getByRole("menuitem", {
          name: /^keyboard shortcuts/i,
        });
        expect(keebItem).toBeInTheDocument();
      });

      // we can open the modal
      const keebItem = screen.getByRole("menuitem", {
        name: /^keyboard shortcuts/i,
      });
      await userEvent.click(keebItem);

      expect(requestHelp).toHaveBeenCalled();
    });

    it("Sign out should work", async () => {
      renderWithProviders(<MainMenu />, { preloadedState: authState });
      const menuTrigger = screen.getByText("dellsberg");
      expect(menuTrigger).toBeInTheDocument();
      await userEvent.click(menuTrigger);

      await waitFor(() => {
        const menu = screen.getByRole("menu");
        expect(menu).toBeInTheDocument();

        const signoutItem = screen.getByRole("menuitem", {
          name: /^sign out/i,
        });
        expect(signoutItem).toBeInTheDocument();
      });
      const signoutItem = screen.getByRole("menuitem", {
        name: /^sign out/i,
      });
      await userEvent.click(signoutItem);
      expect(mockNavigate).toHaveBeenCalledWith("/");
    });
  });
});
