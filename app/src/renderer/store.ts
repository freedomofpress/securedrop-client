import { combineReducers, configureStore } from "@reduxjs/toolkit";
import sessionSlice from "./features/session/sessionSlice";
import journalistsSlice from "./features/journalists/journalistsSlice";

const rootReducer = combineReducers({
  session: sessionSlice,
  journalists: journalistsSlice,
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
