/* eslint-disable @typescript-eslint/no-explicit-any */
import { screen } from "@testing-library/react";
import { expect } from "vitest";
import InboxView from "../../../src/renderer/views/Inbox";
import { renderWithProviders } from "../../../src/renderer/test-component-setup";

describe("InboxView Component", () => {
  it('says the string "Select a source"', () => {
    renderWithProviders(<InboxView />);
    expect(screen.getByText("Select a source")).toBeInTheDocument();
  });
});
