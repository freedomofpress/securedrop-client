import { createMachine, assign } from "xstate";

interface AuthContext {
  errorMessage: string | null;
  authToken: string | null;
}

type AuthEvent =
  | {
      type: "LOGIN_ATTEMPT";
      username: string;
      password: string;
      twofactor: string;
    }
  | { type: "LOGIN_SUCCESS" }
  | { type: "LOGIN_FAILURE"; message: string }
  | { type: "LOGOUT" }
  | { type: "GO_ONLINE" }
  | { type: "GO_OFFLINE" };

type AuthState =
  | { value: "prelogin"; context: AuthContext }
  | { value: "loggingIn"; context: AuthContext }
  | { value: "loginFailure"; context: AuthContext }
  | { value: "onlineMode"; context: AuthContext }
  | { value: "offlineMode"; context: AuthContext };

export const authMachine = createMachine<AuthContext, AuthEvent, AuthState>({
  id: "auth",
  initial: "preLogin",
  context: {
    errorMessage: null,
    authToken: null,
  },
  states: {
    preLogin: {
      on: {
        LOGIN_ATTEMPT: {
          target: "loggingIn",
          actions: assign({ errorMessage: null }),
        },
        GO_OFFLINE: {
          target: "offlineMode",
          actions: assign({ errorMessage: null, authToken: null }),
        },
      },
    },

    loggingIn: {
      on: {
        LOGIN_SUCCESS: {
          target: "onlineMode",
          actions: assign({ errorMessage: null }),
        },
        LOGIN_FAILURE: {
          target: "loginFailure",
        },
      },
      /* Will get transitions down and come back to this
      invoke: {
        src: 'tryLogin',
        onDone: {
          target: 'onlineMode',
          actions: assign({ errorMessage: null }),
        },
        onError: {
          target: 'loginFailure',
          actions: assign({
            errorMessage: (context, event) => event.data.message,
          }),
        },
      },
      */
    },

    onlineMode: {
      on: {
        LOGOUT: {
          target: "preLogin",
          actions: assign({ authToken: null }),
        },
        GO_OFFLINE: {
          target: "offlineMode",
          actions: assign({ authToken: null }),
        },
      },
    },

    offlineMode: {
      on: {
        GO_ONLINE: "preLogin",
      },
    },

    loginFailure: {
      on: {
        LOGIN_ATTEMPT: {
          target: "loggingIn",
          actions: assign({ errorMessage: null }),
        },
      },
    },
  },

  services: {
    tryLogin: async (context, event) => {
      if (event.type !== "LOGIN_ATTEMPT") {
        throw new Error("Invalid event type for authentication service");
      }
      // Simulate API call for authentication
      return new Promise((resolve, reject) => {
        setTimeout(() => {
          if (
            event.twofactor === "123456" &&
            event.username === "u" &&
            event.password === "p"
          ) {
            resolve("successful!");
          } else {
            reject({ message: "Invalid credentials" });
          }
        }, 1000);
      });
    },
  },
});
