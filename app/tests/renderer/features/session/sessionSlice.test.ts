import { describe, it, expect } from "vitest";
import sessionReducer, {
  clear,
  set,
  getSessionState,
  SessionState,
} from "../../../../src/renderer/features/session/sessionSlice";

describe("sessionSlice", () => {
  const emptyState: SessionState = {
    expiration: undefined,
    token: undefined,
    journalist_uuid: undefined,
    journalist_first_name: undefined,
    journalist_last_name: undefined,
  };

  const mockSessionState: SessionState = {
    expiration: "2025-07-16T19:25:44.388054+00:00",
    token: "test-token-123",
    journalist_uuid: "journalist-uuid-456",
    journalist_first_name: "John",
    journalist_last_name: "Doe",
  };

  it("should have the correct initial state", () => {
    const result = sessionReducer(undefined, { type: "unknown" });
    expect(result).toEqual(emptyState);
  });

  describe("clear action", () => {
    it("should clear the session state", () => {
      const result = sessionReducer(mockSessionState, clear());
      expect(result).toEqual(emptyState);
    });

    it("should return empty state when clearing already empty state", () => {
      const result = sessionReducer(emptyState, clear());
      expect(result).toEqual(emptyState);
    });
  });

  describe("set action", () => {
    it("should set a complete session state", () => {
      const result = sessionReducer(emptyState, set(mockSessionState));
      expect(result).toEqual(mockSessionState);
    });

    it("should replace existing session state", () => {
      const newSessionState: SessionState = {
        expiration: "2025-12-31T23:59:59.000000+00:00",
        token: "new-token-789",
        journalist_uuid: "new-uuid-123",
        journalist_first_name: "Jane",
        journalist_last_name: "Smith",
      };

      const result = sessionReducer(mockSessionState, set(newSessionState));
      expect(result).toEqual(newSessionState);
      expect(result).not.toEqual(mockSessionState);
    });
  });
});
