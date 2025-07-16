/* eslint-disable @typescript-eslint/no-explicit-any */
import { screen } from "@testing-library/react";
import { expect } from "vitest";
import userEvent from "@testing-library/user-event";
import InboxView from "../../../src/renderer/views/Inbox";
import { renderWithProviders } from "../../../src/renderer/test-component-setup";

describe("InboxView Component", () => {
  it('says the string "Hello world!"', () => {
    renderWithProviders(<InboxView />);
    expect(screen.getByText("Hello world!")).toBeInTheDocument();
  });

  it("calls window.electronAPI.request when the button is clicked", async () => {
    renderWithProviders(<InboxView />);
    const dummyButton = screen.getByTestId("dummy-button");
    await userEvent.click(dummyButton);
    expect((window as any).electronAPI.request).toHaveBeenCalled();
  });

  it("navigates to root path when sign out button is clicked", async () => {
    let currentLocation: any;
    const handleLocationChange = (location: any) => {
      currentLocation = location;
    };

    renderWithProviders(<InboxView />, {
      initialEntries: ["/inbox"],
      onLocationChange: handleLocationChange,
    });

    // Get initial location
    expect(currentLocation.pathname).toBe("/inbox");

    const signOutButton = screen.getByTestId("sign-out-button");
    await userEvent.click(signOutButton);

    // Verify navigation to root path
    expect(currentLocation.pathname).toBe("/");
  });
});
