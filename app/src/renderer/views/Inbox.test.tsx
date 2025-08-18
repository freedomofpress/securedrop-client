import { screen } from "@testing-library/react";
import { expect } from "vitest";
import InboxView from "./Inbox";
import { renderWithProviders } from "../test-component-setup";

describe("InboxView Component", () => {
  it('says the string "Select a source"', () => {
    renderWithProviders(<InboxView />);
    expect(screen.getByText("Select a source")).toBeInTheDocument();
  });
});
