import { combineReducers, configureStore } from "@reduxjs/toolkit";
import sessionSlice from "./features/session/sessionSlice";
import sourcesSlice from "./features/sources/sourcesSlice";
import conversationsSlice from "./features/conversations/conversationsSlice";

const rootReducer = combineReducers({
  session: sessionSlice,
  sources: sourcesSlice,
  conversations: conversationsSlice,
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
