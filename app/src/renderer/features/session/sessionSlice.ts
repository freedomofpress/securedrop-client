/*
WARNING: This is not a real session!  It does not, and should not, provide a
real session that can be used for subsequent requests; use real session storage
for that.  It merely caches for demonstration purposes some information returned
by a successful authentication request.
*/

import { createSlice } from "@reduxjs/toolkit";
import type { PayloadAction } from "@reduxjs/toolkit";
import type { RootState } from "../../store";

// API response type
interface AuthorizationResponse {
  expiration: string; // ISO 8601 datetime string
  token: string;
  journalist_uuid: string;
  journalist_first_name: string;
  journalist_last_name: string;
}

interface SessionState {
  expiration: Date | undefined;
  token: string | undefined;
  journalist_uuid: string | undefined;
  journalist_first_name: string | undefined;
  journalist_last_name: string | undefined;
}

const emptyState: SessionState = {
  expiration: undefined,
  token: undefined,
  journalist_uuid: undefined,
  journalist_first_name: undefined,
  journalist_last_name: undefined,
};

export const sessionSlice = createSlice({
  name: "session",
  initialState: emptyState,
  reducers: {
    clear: () => emptyState,
    set: (_state, action: PayloadAction<SessionState>) => action.payload,
  },
});

export type { SessionState, AuthorizationResponse };
export const { clear, set } = sessionSlice.actions;
export const getSessionState = (state: RootState) => state.session;
export default sessionSlice.reducer;
