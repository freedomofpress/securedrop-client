/* eslint-disable @typescript-eslint/no-explicit-any */
import { screen, waitFor } from "@testing-library/react";
import { expect } from "vitest";
import SignInView from "../../../src/renderer/views/SignIn";
import { renderWithProviders } from "../../../src/renderer/test-component-setup";

describe("SignInView Component", () => {
  it("says title and version", async () => {
    renderWithProviders(<SignInView />);

    // Wait for the async useEffect to complete
    await waitFor(() => {
      expect(screen.getByText("Sign in to SecureDrop")).toBeInTheDocument();
      // getVersion is mocked to return "1.0.0"
      expect(screen.getByText("SecureDrop App v1.0.0")).toBeInTheDocument();
    });
  });
});
