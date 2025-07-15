import { createSlice } from "@reduxjs/toolkit";
import type { PayloadAction } from "@reduxjs/toolkit";
import type { RootState } from "../../store";

interface SessionState {
  expiration: string | undefined;
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

export type { SessionState };
export const { clear, set } = sessionSlice.actions;
export const getSessionState = (state: RootState) => state.session;
export default sessionSlice.reducer;
