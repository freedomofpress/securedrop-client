/*
WARNING: This is not a real session!  It does not, and should not, provide a
real session that can be used for subsequent requests; use real session storage
for that.  It merely caches for demonstration purposes some information returned
by a successful authentication request.
*/

import { createSlice } from "@reduxjs/toolkit";
import type { PayloadAction } from "@reduxjs/toolkit";
import type { RootState } from "../../store";

interface SessionState {
  expiration: string | undefined; // FIXME: refine type
  journalist_uuid: string | undefined; // FIXME: refine type
  journalist_first_name: string | undefined;
  journalist_last_name: string | undefined;
}

const emptyState: SessionState = {
  expiration: undefined,
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

export type { SessionState };
export const { clear, set } = sessionSlice.actions;
export const getSessionState = (state: RootState) => state.session;
export default sessionSlice.reducer;
