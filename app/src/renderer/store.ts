import { combineReducers, configureStore } from "@reduxjs/toolkit";
import sessionSlice from "./features/session/sessionSlice";
import journalistsSlice from "./features/journalists/journalistsSlice";
import sourcesSlice from "./features/sources/sourcesSlice";
import conversationSlice from "./features/conversation/conversationSlice";
import syncSlice from "./features/sync/syncSlice";
import draftsSlice from "./features/drafts/draftsSlice";

const rootReducer = combineReducers({
  session: sessionSlice,
  journalists: journalistsSlice,
  sources: sourcesSlice,
  conversation: conversationSlice,
  sync: syncSlice,
  drafts: draftsSlice,
});

export const setupStore = (preloadedState?: Partial<RootState>) => {
  return configureStore({
    reducer: rootReducer,
    preloadedState,
  });
};

export type RootState = ReturnType<typeof rootReducer>;
export type AppStore = ReturnType<typeof setupStore>;
export type AppDispatch = AppStore["dispatch"];
