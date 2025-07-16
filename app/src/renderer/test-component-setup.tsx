/* eslint-disable @typescript-eslint/no-explicit-any */
/* eslint-disable react-refresh/only-export-components */
import { expect, afterEach, beforeEach, vi } from "vitest";
import { cleanup, render } from "@testing-library/react";
import * as matchers from "@testing-library/jest-dom/matchers";
import { MemoryRouter, useLocation } from "react-router";
import { Provider } from "react-redux";
import React from "react";

import { setupStore } from "./store";

// extends Vitest's expect with jest-dom matchers
expect.extend(matchers);

afterEach(() => {
  cleanup();
});

beforeEach(() => {
  // Mock the electronAPI before each test
  (window as any).electronAPI = {
    getVersion: vi.fn().mockResolvedValue("1.0.0"),
    request: vi.fn().mockResolvedValue({ data: "test" }),
    requestStream: vi.fn().mockResolvedValue({ sha256sum: "abc" }),
  };
});

// Component to track react-router location changes for testing
export const LocationTracker = ({
  onLocationChange,
}: {
  onLocationChange: (location: any) => void;
}) => {
  const location = useLocation();
  onLocationChange(location);
  return null;
};

// Test wrapper component that provides Redux store and MemoryRouter context
export const TestWrapper = ({
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
export const renderWithProviders = (
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
