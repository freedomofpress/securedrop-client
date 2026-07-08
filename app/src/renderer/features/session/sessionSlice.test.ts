import { describe, it, expect, vi, beforeEach } from "vitest";
import { configureStore } from "@reduxjs/toolkit";
import sessionReducer, {
  setAuth,
  setUnauth,
  setOffline,
  type SessionState,
  type AuthData,
  SessionStatus,
  unauthSessionState,
} from "../../../../src/renderer/features/session/sessionSlice";

// Mock electronAPI so we can assert the signOut IPC is invoked
const mockElectronAPI = {
  signOut: vi.fn(),
};

Object.defineProperty(window, "electronAPI", {
  value: mockElectronAPI,
  writable: true,
});

describe("sessionSlice", () => {
  const mockAuthData: AuthData = {
    expiration: "2025-07-16T19:25:44.388054+00:00",
    journalistUUID: "journalist-uuid-456",
    journalistFirstName: "John",
    journalistLastName: "Doe",
  };

  const mockSessionState: SessionState = {
    status: SessionStatus.Auth,
    authData: mockAuthData,
    errorMessage: undefined,
  };

  it("should have the correct initial state", () => {
    const result = sessionReducer(undefined, { type: "unknown" });
    expect(result).toEqual(unauthSessionState);
  });

  describe("setUnauth action", () => {
    it("should set the session state to unauth", () => {
      const result = sessionReducer(
        mockSessionState,
        setUnauth.fulfilled(undefined, "", undefined),
      );
      expect(result).toEqual(unauthSessionState);
    });

    it("should return unauth state when clearing already empty state", () => {
      const result = sessionReducer(
        unauthSessionState,
        setUnauth.fulfilled(undefined, "", undefined),
      );
      expect(result).toEqual(unauthSessionState);
    });

    it("should set error message when provided", () => {
      const errorMsg = "Your session expired. Please log in again.";
      const result = sessionReducer(
        mockSessionState,
        setUnauth.fulfilled(errorMsg, "", errorMsg),
      );
      expect(result).toEqual({
        status: SessionStatus.Unauth,
        authData: undefined,
        errorMessage: errorMsg,
      });
    });
  });

  describe("setUnauth thunk", () => {
    beforeEach(() => {
      (window as any).electronAPI = mockElectronAPI;
      mockElectronAPI.signOut.mockReset();
    });

    const makeStore = () =>
      configureStore({ reducer: { session: sessionReducer } });

    it("calls the signOut IPC and clears the session when dispatched", async () => {
      mockElectronAPI.signOut.mockResolvedValue(null);
      const store = makeStore();

      const result = await store.dispatch(setUnauth(undefined));

      expect(mockElectronAPI.signOut).toHaveBeenCalledTimes(1);
      expect(result.type).toBe("session/setUnauth/fulfilled");
      expect(store.getState().session).toEqual(unauthSessionState);
    });

    it("propagates the error message through to the session state", async () => {
      mockElectronAPI.signOut.mockResolvedValue(null);
      const errorMsg = "Your session expired. Please log in again.";
      const store = makeStore();

      await store.dispatch(setUnauth(errorMsg));

      expect(mockElectronAPI.signOut).toHaveBeenCalledTimes(1);
      expect(store.getState().session).toEqual({
        status: SessionStatus.Unauth,
        authData: undefined,
        errorMessage: errorMsg,
      });
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
        errorMessage: undefined,
      });
    });

    it("should clear auth data when setting offline from authenticated state", () => {
      const result = sessionReducer(mockSessionState, setOffline());
      expect(result).toEqual({
        status: SessionStatus.Offline,
        authData: undefined,
        errorMessage: undefined,
      });
      expect(result.authData).toBeUndefined();
    });

    it("should maintain offline status when already offline", () => {
      const offlineState: SessionState = {
        status: SessionStatus.Offline,
        authData: undefined,
        errorMessage: undefined,
      };
      const result = sessionReducer(offlineState, setOffline());
      expect(result).toEqual(offlineState);
    });
  });
});
