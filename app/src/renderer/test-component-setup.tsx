/* eslint-disable @typescript-eslint/no-explicit-any */
/* eslint-disable react-refresh/only-export-components */
import { expect, afterEach, beforeEach, vi } from "vitest";
import { cleanup, render, type RenderResult } from "@testing-library/react";
import * as matchers from "@testing-library/jest-dom/matchers";
import { MemoryRouter, useLocation } from "react-router";
import { Provider } from "react-redux";
import React, { memo } from "react";

import { setupStore, type RootState } from "./store";
import "./i18n";
import type { ElectronAPI } from "../preload/index";

// Mock global variables
(global as any).__APP_VERSION__ = "6.6.6-test";
(global as any).__DEV_AUTO_LOGIN__ = false;

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
    getSystemLanguage: vi.fn().mockResolvedValue("en"),
    // TODO: we may want a real mock here
    syncMetadata: vi.fn().mockRejectedValue(new Error("mock not implemented")),
    updateFetchStatus: vi
      .fn()
      .mockRejectedValue(new Error("mock not implemented")),
    onItemUpdate: vi.fn().mockRejectedValue(new Error("mock not implemented")),
    getItem: vi.fn().mockRejectedValue(new Error("mock not implemented")),
    getSources: vi.fn().mockResolvedValue([
      {
        uuid: "source-1",
        data: {
          fingerprint: "ABCD1234EFGH5678IJKL9012MNOP3456QRST7890",
          is_starred: false,
          journalist_designation: "multiplicative conditionality",
          last_updated: "2024-01-15T10:30:00Z",
          public_key:
            "-----BEGIN PGP PUBLIC KEY BLOCK-----\nVersion: GnuPG v1\n...\n-----END PGP PUBLIC KEY BLOCK-----",
          uuid: "source-1",
        },
        isRead: false,
      },
      {
        uuid: "source-2",
        data: {
          fingerprint: "1234ABCD5678EFGH9012IJKL3456MNOP7890QRST",
          is_starred: true,
          journalist_designation: "piezoelectric crockery",
          last_updated: "2024-01-14T15:45:00Z",
          public_key:
            "-----BEGIN PGP PUBLIC KEY BLOCK-----\nVersion: GnuPG v1\n...\n-----END PGP PUBLIC KEY BLOCK-----",
          uuid: "source-2",
        },
        isRead: true,
      },
      {
        uuid: "source-3",
        data: {
          fingerprint: "5678EFGH9012IJKL3456MNOP7890QRST1234ABCD",
          is_starred: false,
          journalist_designation: "thyroid battle",
          last_updated: "2024-04-10T09:15:00Z",
          public_key:
            "-----BEGIN PGP PUBLIC KEY BLOCK-----\nVersion: GnuPG v1\n...\n-----END PGP PUBLIC KEY BLOCK-----",
          uuid: "source-3",
        },
        isRead: false,
      },
    ]),
    getSourceWithItems: vi.fn().mockResolvedValue({
      uuid: "source-1",
      data: {
        fingerprint: "ABCD1234EFGH5678IJKL9012MNOP3456QRST7890",
        is_starred: false,
        journalist_designation: "multiplicative conditionality",
        last_updated: "2024-01-15T10:30:00Z",
        public_key:
          "-----BEGIN PGP PUBLIC KEY BLOCK-----\nVersion: GnuPG v1\n...\n-----END PGP PUBLIC KEY BLOCK-----",
        uuid: "source-1",
      },
      items: [
        {
          uuid: "item-1",
          data: {
            uuid: "item-1",
            kind: "message",
            seenBy: [],
            size: 1024,
            source: "source-1",
            isRead: false,
          },
        },
        {
          uuid: "item-2",
          data: {
            uuid: "item-2",
            kind: "file",
            seenBy: [],
            size: 2048,
            source: "source-1",
            isRead: true,
          },
        },
      ],
    }),
    getJournalists: vi.fn().mockResolvedValue([
      {
        uuid: "journalist-1",
        data: {
          uuid: "journalist-1",
          username: "journalist",
          first_name: null,
          last_name: null,
        },
      },
      {
        uuid: "journalist-2",
        data: {
          uuid: "journalist-2",
          username: "dellsberg",
          first_name: "Daniel",
          last_name: "Ellsberg",
        },
      },
      {
        uuid: "journalist-3",
        data: {
          uuid: "journalist-3",
          username: "deleted",
          first_name: null,
          last_name: null,
        },
      },
    ]),
    addPendingSourceEvent: vi.fn().mockResolvedValue(BigInt(123)),
    addPendingReplySentEvent: vi.fn().mockResolvedValue(BigInt(456)),
    addPendingItemEvent: vi.fn().mockResolvedValue(BigInt(789)),
    shouldAutoLogin: vi.fn().mockResolvedValue(false),
  } as ElectronAPI;
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
  store: providedStore,
}: {
  children: React.ReactNode;
  initialEntries?: string[];
  onLocationChange?: (location: any) => void;
  preloadedState?: Partial<RootState>;
  store?: ReturnType<typeof setupStore>;
}) => {
  const store = providedStore || setupStore(preloadedState);
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
): RenderResult & { store: ReturnType<typeof setupStore> } => {
  const store = setupStore(options?.preloadedState);

  const renderResult = render(ui, {
    wrapper: ({ children }) => (
      <TestWrapper
        initialEntries={options?.initialEntries}
        onLocationChange={options?.onLocationChange}
        preloadedState={options?.preloadedState}
        store={store}
      >
        {children}
      </TestWrapper>
    ),
  });

  return {
    store,
    ...renderResult,
  };
};

// Generic function to create a memoized component wrapper that tracks render calls
export function createMockComponent<T extends Record<string, any>>(
  Component: React.ComponentType<T>,
) {
  const mockRenderCount = vi.fn();

  const MockComponent = memo((props: T) => {
    mockRenderCount(props);
    return React.createElement(Component, props);
  });

  return {
    MockComponent,
    mockRenderCount,
  };
}

// Data-driven memoization test helper
export function testMemoization<T extends Record<string, any>>(
  Component: React.ComponentType<T>,
  testCases: Array<[T, number]>,
) {
  return () => {
    const { MockComponent, mockRenderCount } = createMockComponent(Component);

    const { rerender } = renderWithProviders(
      <MockComponent {...testCases[0][0]} />,
    );
    expect(mockRenderCount).toHaveBeenCalledTimes(testCases[0][1]);

    for (let i = 1; i < testCases.length; i++) {
      const [props, expectedCount] = testCases[i];
      rerender(<MockComponent {...props} />);
      expect(mockRenderCount).toHaveBeenCalledTimes(expectedCount);
    }
  };
}
