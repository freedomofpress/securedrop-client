import { render, screen } from "@testing-library/react";
import { vi, expect, beforeEach } from "vitest";
import userEvent from "@testing-library/user-event";
import { MemoryRouter, useLocation } from "react-router";
import { Provider } from "react-redux";
import InboxView from "./Inbox";
import { setupStore } from "../store";

// Component to track location changes for testing
const LocationTracker = ({
  onLocationChange,
}: {
  onLocationChange: (location: any) => void;
}) => {
  const location = useLocation();
  onLocationChange(location);
  return null;
};

// Test wrapper component that provides Redux store and MemoryRouter context
const TestWrapper = ({
  children,
  initialEntries = ["/"],
  onLocationChange,
}: {
  children: React.ReactNode;
  initialEntries?: string[];
  onLocationChange?: (location: any) => void;
}) => {
  const store = setupStore();
  return (
    <Provider store={store}>
      <MemoryRouter initialEntries={initialEntries}>
        {onLocationChange && (
          <LocationTracker onLocationChange={onLocationChange} />
        )}
        {children}
      </MemoryRouter>
    </Provider>
  );
};

// Custom render function that wraps components with necessary providers
const renderWithProviders = (
  ui: React.ReactElement,
  options?: {
    initialEntries?: string[];
    onLocationChange?: (location: any) => void;
  },
) => {
  return render(ui, {
    wrapper: ({ children }) => (
      <TestWrapper
        initialEntries={options?.initialEntries}
        onLocationChange={options?.onLocationChange}
      >
        {children}
      </TestWrapper>
    ),
  });
};

describe("InboxView Component", () => {
  beforeEach(() => {
    // Mock the electronAPI before each test
    window.electronAPI = {
      getVersion: vi.fn().mockResolvedValue("1.0.0"),
      request: vi.fn().mockResolvedValue({ data: "test" }),
      requestStream: vi.fn().mockResolvedValue({ sha256sum: "abc" }),
    };
  });

  it('says the string "Hello world!"', () => {
    renderWithProviders(<InboxView />);
    expect(screen.getByText("Hello world!")).toBeInTheDocument();
  });

  it("calls window.electronAPI.request when the button is clicked", async () => {
    renderWithProviders(<InboxView />);
    const dummyButton = screen.getByTestId("dummy-button");
    await userEvent.click(dummyButton);
    expect(window.electronAPI.request).toHaveBeenCalled();
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
