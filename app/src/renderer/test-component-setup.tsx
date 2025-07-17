/* eslint-disable @typescript-eslint/no-explicit-any */
/* eslint-disable react-refresh/only-export-components */
import { expect, afterEach, beforeEach, vi } from "vitest";
import { cleanup, render } from "@testing-library/react";
import * as matchers from "@testing-library/jest-dom/matchers";
import { MemoryRouter, useLocation } from "react-router";
import { Provider } from "react-redux";
import React from "react";

import { setupStore, type RootState } from "./store";

// Mock global variables
(global as any).__APP_VERSION__ = "6.6.6-test";

// extends Vitest's expect with jest-dom matchers
expect.extend(matchers);

// Mock window.matchMedia for Ant components
Object.defineProperty(window, "matchMedia", {
  writable: true,
  value: (query: string) => ({
    matches: false,
    media: query,
    onchange: null,
    addListener: () => {},
    removeListener: () => {},
    addEventListener: () => {},
    removeEventListener: () => {},
    dispatchEvent: () => {},
  }),
});

afterEach(() => {
  cleanup();
});

beforeEach(() => {
  // Mock the electronAPI before each test
  (window as any).electronAPI = {
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
  preloadedState,
}: {
  children: React.ReactNode;
  initialEntries?: string[];
  onLocationChange?: (location: any) => void;
  preloadedState?: Partial<RootState>;
}) => {
  const store = setupStore(preloadedState);
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
    preloadedState?: Partial<RootState>;
  },
) => {
  return render(ui, {
    wrapper: ({ children }) => (
      <TestWrapper
        initialEntries={options?.initialEntries}
        onLocationChange={options?.onLocationChange}
        preloadedState={options?.preloadedState}
      >
        {children}
      </TestWrapper>
    ),
  });
};
