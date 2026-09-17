import {
  combineReducers,
  configureStore,
  type Reducer,
} from "@reduxjs/toolkit";
import sessionSlice from "./features/session/sessionSlice";
import journalistsSlice from "./features/journalists/journalistsSlice";
import sourcesSlice from "./features/sources/sourcesSlice";
import conversationSlice from "./features/conversation/conversationSlice";
import syncSlice from "./features/sync/syncSlice";
import draftsSlice from "./features/drafts/draftsSlice";

export const rootReducer = combineReducers({
  session: sessionSlice,
  journalists: journalistsSlice,
  sources: sourcesSlice,
  conversation: conversationSlice,
  sync: syncSlice,
  drafts: draftsSlice,
});

export type PreloadedRootState = {
  [K in keyof RootState]?: Partial<RootState[K]>;
};

// Not a real action type: reducers answer an unrecognized action with their own
// initial state, which is how the defaults are read back out of them here.
const PROBE = { type: "@@store/probe" };

export const defaultRootState = (): RootState => rootReducer(undefined, PROBE);

export const defaultSliceState = <S extends object>(
  reducer: Reducer<S>,
  overrides: Partial<S> = {},
): S => ({ ...reducer(undefined, PROBE), ...overrides });

// Fills a partial state out to a complete `RootState`, slice by slice.
export const makeRootState = (
  overrides: PreloadedRootState = {},
): RootState => {
  const base = defaultRootState();
  const merged = { ...base };
  for (const slice of Object.keys(overrides) as (keyof RootState)[]) {
    // Sound by construction: each override is a `Partial` of that slice.
    Object.assign(merged, { [slice]: { ...base[slice], ...overrides[slice] } });
  }
  return merged;
};

export const setupStore = (preloadedState?: PreloadedRootState) => {
  return configureStore({
    reducer: rootReducer,
    preloadedState: preloadedState && makeRootState(preloadedState),
  });
};

export type RootState = ReturnType<typeof rootReducer>;
export type AppStore = ReturnType<typeof setupStore>;
export type AppDispatch = AppStore["dispatch"];
