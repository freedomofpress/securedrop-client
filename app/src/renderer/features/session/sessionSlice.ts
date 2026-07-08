import { createAsyncThunk, createSlice } from "@reduxjs/toolkit";
import type { PayloadAction } from "@reduxjs/toolkit";
import type { RootState } from "../../store";

enum SessionStatus {
  Unauth,
  Offline,
  Auth,
}

interface AuthData {
  expiration: string;
  journalistUUID: string;
  journalistFirstName: string | null;
  journalistLastName: string | null;
  lastHintedVersion?: string;
  lastHintedSources?: number;
  lastHintedItems?: number;
}

interface SessionState {
  status: SessionStatus;
  authData?: AuthData;
  errorMessage?: string;
}

const unauthState: SessionState = {
  status: SessionStatus.Unauth,
  authData: undefined,
  errorMessage: undefined,
};

export const setUnauth = createAsyncThunk(
  "session/setUnauth",
  async (errorMessage: string | undefined) => {
    void Promise.resolve(window.electronAPI?.signOut?.()).catch((e) => {
      console.error("Failed to sign out:", e);
    });
    return errorMessage;
  },
);

export const sessionSlice = createSlice({
  name: "session",
  initialState: unauthState,
  reducers: {
    setAuth: (state, action: PayloadAction<AuthData>) => {
      state.authData = action.payload;
      state.status = SessionStatus.Auth;
      state.errorMessage = undefined;
    },
    clearError: (state) => {
      state.errorMessage = undefined;
    },
    setOffline: (state) => {
      state.status = SessionStatus.Offline;
      state.authData = undefined;
      state.errorMessage = undefined;
    },
  },
  extraReducers: (builder) => {
    builder.addCase(setUnauth.fulfilled, (state, action) => {
      state.status = SessionStatus.Unauth;
      state.authData = undefined;
      state.errorMessage = action.payload;
    });
  },
});

export type { SessionState, AuthData };
export { SessionStatus };
export const unauthSessionState = unauthState;
export const { setAuth, clearError, setOffline } = sessionSlice.actions;
export const getSessionState = (state: RootState) => state.session;
export default sessionSlice.reducer;
