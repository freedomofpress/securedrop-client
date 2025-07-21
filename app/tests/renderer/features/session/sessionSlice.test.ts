import { describe, it, expect } from "vitest";
import sessionReducer, {
  setAuth,
  setUnauth,
  setOffline,
  type SessionState,
  type AuthData,
  SessionStatus,
  unauthSessionState,
} from "../../../../src/renderer/features/session/sessionSlice";

describe("sessionSlice", () => {
  const mockAuthData: AuthData = {
    expiration: "2025-07-16T19:25:44.388054+00:00",
    token: "test-token-123",
    journalistUUID: "journalist-uuid-456",
    journalistFirstName: "John",
    journalistLastName: "Doe",
  };

  const mockSessionState: SessionState = {
    status: SessionStatus.Auth,
    authData: mockAuthData,
  };

  it("should have the correct initial state", () => {
    const result = sessionReducer(undefined, { type: "unknown" });
    expect(result).toEqual(unauthSessionState);
  });

  describe("setUnauth action", () => {
    it("should set the session state to unauth", () => {
      const result = sessionReducer(mockSessionState, setUnauth());
      expect(result).toEqual(unauthSessionState);
    });

    it("should return unauth state when clearing already empty state", () => {
      const result = sessionReducer(unauthSessionState, setUnauth());
      expect(result).toEqual(unauthSessionState);
    });
  });

  describe("setAuth action", () => {
    it("should set a complete session state", () => {
      const result = sessionReducer(unauthSessionState, setAuth(mockAuthData));
      expect(result).toEqual(mockSessionState);
    });

    it("should replace existing session state", () => {
      const newAuthData: AuthData = {
        expiration: "2025-12-31T23:59:59.000000+00:00",
        token: "new-token-789",
        journalistUUID: "new-uuid-123",
        journalistFirstName: "Jane",
        journalistLastName: "Smith",
      };

      const result = sessionReducer(mockSessionState, setAuth(newAuthData));
      expect(result).toEqual({ ...mockSessionState, authData: newAuthData });
      expect(result).not.toEqual(mockSessionState);
    });
  });

  describe("setOffline action", () => {
    it("should set the session state to offline", () => {
      const result = sessionReducer(unauthSessionState, setOffline());
      expect(result).toEqual({
        status: SessionStatus.Offline,
        authData: undefined,
      });
    });

    it("should clear auth data when setting offline from authenticated state", () => {
      const result = sessionReducer(mockSessionState, setOffline());
      expect(result).toEqual({
        status: SessionStatus.Offline,
        authData: undefined,
      });
      expect(result.authData).toBeUndefined();
    });

    it("should maintain offline status when already offline", () => {
      const offlineState: SessionState = {
        status: SessionStatus.Offline,
        authData: undefined,
      };
      const result = sessionReducer(offlineState, setOffline());
      expect(result).toEqual(offlineState);
    });
  });
});
