import { render, screen } from "@testing-library/react";
import { vi, expect } from "vitest";
import userEvent from "@testing-library/user-event";
import App from "./App";

describe("App Component", () => {
  it('says the string "Hello world!"', () => {
    render(<App />);
    expect(screen.getByText("Hello world!")).toBeInTheDocument();
  });

  it("calls window.electronAPI.request when the button is clicked", async () => {
    // Mock IPC methods
    window.electronAPI = {
      request: vi.fn().mockResolvedValue({ data: "test" }),
      requestStream: vi.fn().mockResolvedValue({ sha256sum: "abc" }),
    };

    render(<App />);
    const dummyButton = screen.getByTestId("dummy-button");
    await userEvent.click(dummyButton);
    expect(window.electronAPI.request).toHaveBeenCalled();
  });
});
