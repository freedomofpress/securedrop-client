import { screen } from "@testing-library/react";
import { expect } from "vitest";
import InboxView from "./Inbox";
import {
  renderWithProviders,
  renderAndCheckA11y,
} from "../test-component-setup";

describe("InboxView accessibility", () => {
  it("has no axe violations on initial render", async () => {
    // TODO(a11y): ARIA input field is missing an accessible name.
    await renderAndCheckA11y(<InboxView />, undefined, [
      "aria-input-field-name",
    ]);
  });
});

describe("InboxView Component", () => {
  it('says the string "Select a source"', () => {
    renderWithProviders(<InboxView />);
    expect(screen.getByText("Select a source")).toBeInTheDocument();
  });
});
