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
  journalistFirstName: string;
  journalistLastName: string;
}

interface SessionState {
  status: SessionStatus;
  authData?: AuthData;
}

const emptyState: SessionState = {
  status: SessionStatus.Unauth,
  authData: undefined,
};

export const sessionSlice = createSlice({
  name: "session",
  initialState: emptyState,
  reducers: {
    clear: () => emptyState,
    set: (_state, action: PayloadAction<SessionState>) => action.payload,
  },
});

export type { SessionState, AuthData };
export { SessionStatus };
export const emptySessionState = emptyState;
export const { clear, set } = sessionSlice.actions;
export const getSessionState = (state: RootState) => state.session;
export default sessionSlice.reducer;
