import { createSlice } from "@reduxjs/toolkit";
import type { PayloadAction } from "@reduxjs/toolkit";
import type { RootState } from "../../store";

export interface DraftsState {
  drafts: Record<string, string>;
}

const initialState: DraftsState = {
  drafts: {},
};

export const draftsSlice = createSlice({
  name: "drafts",
  initialState,
  reducers: {
    setDraft: (
      state,
      action: PayloadAction<{ sourceUuid: string; content: string }>,
    ) => {
      const { sourceUuid, content } = action.payload;
      if (content) {
        state.drafts[sourceUuid] = content;
      } else {
        delete state.drafts[sourceUuid];
      }
    },
    clearDraft: (state, action: PayloadAction<string>) => {
      delete state.drafts[action.payload];
    },
  },
});

export const { setDraft, clearDraft } = draftsSlice.actions;

export const selectDraft = (sourceUuid: string) => (state: RootState) =>
  state.drafts.drafts[sourceUuid] ?? "";

export default draftsSlice.reducer;
