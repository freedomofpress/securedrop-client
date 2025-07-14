import { render, screen } from "@testing-library/react";
import { vi, expect } from "vitest";
import userEvent from "@testing-library/user-event";
import InboxView from "./Inbox";

describe("InboxView Component", () => {
  it('says the string "Hello world!"', () => {
    render(<InboxView />);
    expect(screen.getByText("Hello world!")).toBeInTheDocument();
  });

  it("calls window.electronAPI.request when the button is clicked", async () => {
    // Mock the electronAPI.request function
    window.electronAPI = {
      request: vi.fn().mockResolvedValue({ data: "test" }),
    };

    render(<InboxView />);
    const dummyButton = screen.getByTestId("dummy-button");
    await userEvent.click(dummyButton);
    expect(window.electronAPI.request).toHaveBeenCalled();
  });
});
