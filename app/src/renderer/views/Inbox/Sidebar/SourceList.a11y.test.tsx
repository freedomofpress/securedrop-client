import { describe, it, vi } from "vitest";
import React from "react";
import { Routes, Route } from "react-router";
import SourceList from "./SourceList";
import type { Source as SourceType } from "../../../../types";
import { renderAndCheckA11y } from "../../../test-component-setup";

// Mirror the react-window mock from SourceList.test.tsx so the virtual list
// actually renders its rows instead of relying on DOM measurements.
// The Source child component is intentionally NOT mocked here — we want axe
// to analyse the real accessible markup produced by each source row.
vi.mock("react-window", () => ({
  List: <RowProps extends object>({
    rowComponent: RowComponent,
    rowCount,
    rowProps,
    className,
  }: {
    rowComponent: (
      props: { index: number; style: React.CSSProperties } & RowProps,
    ) => React.ReactNode;
    rowCount: number;
    rowHeight: number;
    rowProps: RowProps;
    className?: string;
  }) => (
    <div className={className}>
      {Array.from({ length: rowCount }, (_, index) => (
        <div key={index}>
          <RowComponent index={index} style={{}} {...rowProps} />
        </div>
      ))}
    </div>
  ),
  useListRef: () => ({ current: null }),
}));

const mockSources: Record<string, SourceType> = {
  "source-1": {
    uuid: "source-1",
    data: {
      fingerprint: "ABCD1234EFGH5678IJKL9012MNOP3456QRST7890",
      is_starred: false,
      is_seen: false,
      has_attachment: false,
      journalist_designation: "alice wonderland",
      last_updated: "2024-01-15T10:30:00Z",
      public_key: "key-1",
      uuid: "source-1",
    },
    isRead: false,
    hasAttachment: false,
    messagePreview: null,
    lastInteractionCount: 3,
  },
  "source-2": {
    uuid: "source-2",
    data: {
      fingerprint: "EFGH5678IJKL9012MNOP3456QRST7890ABCD1234",
      is_starred: true,
      is_seen: true,
      has_attachment: true,
      journalist_designation: "bob marley",
      last_updated: "2024-01-14T15:45:00Z",
      public_key: "key-2",
      uuid: "source-2",
    },
    isRead: true,
    hasAttachment: true,
    messagePreview: { kind: "message", plaintext: "Hello there" },
    lastInteractionCount: 1,
  },
};

// Shared preloaded state builder.
const sourcesState = (sources: Record<string, SourceType> = mockSources) => ({
  sources: {
    sources,
    activeSourceUuid: null,
    loading: false,
    error: null,
    conversationIndicators: {},
  },
});

// SourceList must live inside a router that provides :sourceUuid so that
// useParams works. renderAndCheckA11y wraps the given element in a
// MemoryRouter (via TestWrapper), so we just need Routes/Route inside it.
const sourceListUi = (
  <Routes>
    <Route path="/" element={<SourceList focusedPanel="sidebar" />} />
    <Route
      path="/source/:sourceUuid"
      element={<SourceList focusedPanel="sidebar" />}
    />
  </Routes>
);

describe("SourceList accessibility", () => {
  it("has no axe violations with a populated source list", async () => {
    await renderAndCheckA11y(sourceListUi, {
      preloadedState: sourcesState(),
    });
  });

  it("has no axe violations with an empty source list", async () => {
    await renderAndCheckA11y(sourceListUi, {
      preloadedState: sourcesState({}),
    });
  });

  it("has no axe violations with an active source selected", async () => {
    await renderAndCheckA11y(sourceListUi, {
      initialEntries: ["/source/source-1"],
      preloadedState: sourcesState(),
    });
  });
});
