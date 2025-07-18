import { createSlice } from "@reduxjs/toolkit";
import type { PayloadAction } from "@reduxjs/toolkit";
import type { RootState } from "../../store";

interface SessionState {
  offlineMode: boolean;
  expiration: string | undefined;
  token: string | undefined;
  journalistUuid: string | undefined;
  journalistFirstName: string | undefined;
  journalistLastName: string | undefined;
}

const emptyState: SessionState = {
  offlineMode: false,
  expiration: undefined,
  token: undefined,
  journalistUuid: undefined,
  journalistFirstName: undefined,
  journalistLastName: undefined,
};

export const sessionSlice = createSlice({
  name: "session",
  initialState: emptyState,
  reducers: {
    clear: () => emptyState,
    set: (_state, action: PayloadAction<SessionState>) => action.payload,
  },
});

export type { SessionState };
export const { clear, set } = sessionSlice.actions;
export const getSessionState = (state: RootState) => state.session;
export default sessionSlice.reducer;
