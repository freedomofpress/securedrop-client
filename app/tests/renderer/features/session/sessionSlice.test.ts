import { describe, it, expect } from "vitest";
import sessionReducer, {
  clear,
  set,
  type SessionState,
  type AuthData,
  SessionStatus,
  emptySessionState,
} from "../../../../src/renderer/features/session/sessionSlice";

describe("sessionSlice", () => {
  const mockSessionState: SessionState = {
    status: SessionStatus.Auth,
    authData: {
      expiration: "2025-07-16T19:25:44.388054+00:00",
      token: "test-token-123",
      journalistUUID: "journalist-uuid-456",
      journalistFirstName: "John",
      journalistLastName: "Doe",
    } as AuthData,
  };

  it("should have the correct initial state", () => {
    const result = sessionReducer(undefined, { type: "unknown" });
    expect(result).toEqual(emptySessionState);
  });

  describe("clear action", () => {
    it("should clear the session state", () => {
      const result = sessionReducer(mockSessionState, clear());
      expect(result).toEqual(emptySessionState);
    });

    it("should return empty state when clearing already empty state", () => {
      const result = sessionReducer(emptySessionState, clear());
      expect(result).toEqual(emptySessionState);
    });
  });

  describe("set action", () => {
    it("should set a complete session state", () => {
      const result = sessionReducer(emptySessionState, set(mockSessionState));
      expect(result).toEqual(mockSessionState);
    });

    it("should replace existing session state", () => {
      const newSessionState: SessionState = {
        status: SessionStatus.Auth,
        authData: {
          expiration: "2025-12-31T23:59:59.000000+00:00",
          token: "new-token-789",
          journalistUUID: "new-uuid-123",
          journalistFirstName: "Jane",
          journalistLastName: "Smith",
        } as AuthData,
      };

      const result = sessionReducer(mockSessionState, set(newSessionState));
      expect(result).toEqual(newSessionState);
      expect(result).not.toEqual(mockSessionState);
    });
  });
});
