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
}

const unauthState: SessionState = {
  status: SessionStatus.Unauth,
  authData: undefined,
};

export const sessionSlice = createSlice({
  name: "session",
  initialState: unauthState,
  reducers: {
    setAuth: (state, action: PayloadAction<AuthData>) => {
      state.authData = action.payload;
      state.status = SessionStatus.Auth;
    },
    setUnauth: () => unauthState,
    setOffline: (state) => {
      state.status = SessionStatus.Offline;
      state.authData = undefined;
    },
  },
});

export type { SessionState, AuthData };
export { SessionStatus };
export const unauthSessionState = unauthState;
export const { setAuth, setUnauth, setOffline } = sessionSlice.actions;
export const getSessionState = (state: RootState) => state.session;
export default sessionSlice.reducer;
