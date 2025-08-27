import { createSlice, createAsyncThunk } from "@reduxjs/toolkit";
import type { PayloadAction } from "@reduxjs/toolkit";
import type { RootState } from "../../store";
import type { Journalist } from "../../../types";

interface JournalistsState {
  journalists: Journalist[];
  loading: boolean;
  error: string | null;
}

const initialState: JournalistsState = {
  journalists: [],
  loading: false,
  error: null,
};

export const fetchJournalists = createAsyncThunk(
  "journalists/fetchJournalists",
  async () => {
    const journalists = await window.electronAPI.getJournalists();
    return journalists;
  },
);

export const journalistsSlice = createSlice({
  name: "journalists",
  initialState,
  reducers: {
    clearError: (state) => {
      state.error = null;
    },
  },
  extraReducers: (builder) => {
    builder
      .addCase(fetchJournalists.pending, (state) => {
        state.loading = true;
        state.error = null;
      })
      .addCase(
        fetchJournalists.fulfilled,
        (state, action: PayloadAction<Journalist[]>) => {
          state.loading = false;
          state.journalists = action.payload;
          state.error = null;
        },
      )
      .addCase(fetchJournalists.rejected, (state, action) => {
        state.loading = false;
        state.error = action.error.message || "Failed to fetch journalists";
      });
  },
});

export type { JournalistsState };
export const { clearError } = journalistsSlice.actions;
export const getJournalistsState = (state: RootState) => state.journalists;
export const getJournalists = (state: RootState) =>
  state.journalists.journalists;
export const getJournalistsLoading = (state: RootState) =>
  state.journalists.loading;
export const getJournalistsError = (state: RootState) =>
  state.journalists.error;
export default journalistsSlice.reducer;
