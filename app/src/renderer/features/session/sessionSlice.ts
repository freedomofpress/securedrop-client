import { createSlice } from "@reduxjs/toolkit";
import type { PayloadAction } from "@reduxjs/toolkit";
import type { RootState } from "../../store";

enum SessionStatus {
  Unauth,
  Offline,
  Auth,
}

interface AuthData {
  expiration: string;
  token: string;
  journalistUUID: string;
  journalistFirstName: string | null;
  journalistLastName: string | null;
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

export const sessionSlice = createSlice({
  name: "session",
  initialState: unauthState,
  reducers: {
    setAuth: (state, action: PayloadAction<AuthData>) => {
      state.authData = action.payload;
      state.status = SessionStatus.Auth;
      state.errorMessage = undefined;
    },
    setUnauth: (state, action: PayloadAction<string | undefined>) => {
      state.status = SessionStatus.Unauth;
      state.authData = undefined;
      state.errorMessage = action.payload;
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
});

export type { SessionState, AuthData };
export { SessionStatus };
export const unauthSessionState = unauthState;
export const { setAuth, setUnauth, clearError, setOffline } =
  sessionSlice.actions;
export const getSessionState = (state: RootState) => state.session;
export default sessionSlice.reducer;
