import { render, screen } from "@testing-library/react";
import { vi } from "vitest";
import userEvent from "@testing-library/user-event";
import App from "./App";

describe("App Component", () => {
  it('says the string "PRELOGIN!"', () => {
    render(<App />);
    expect(screen.getByText("PRELOGIN")).toBeInTheDocument();
  });

  it("calls window.electronAPI.request when the button is clicked", async () => {
    // Mock the electronAPI.request function
    window.electronAPI = {
      request: vi.fn().mockResolvedValue({ data: "test" }),
    };

    render(<App />);
    const dummyButton = screen.getByTestId("dummy-button");
    await userEvent.click(dummyButton);
    expect(window.electronAPI.request).toHaveBeenCalled();
  });
});
