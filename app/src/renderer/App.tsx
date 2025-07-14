import React from "react";
import { Button } from "antd";
import { useMachine } from "@xstate/react";
import { authMachine } from "../machines/AuthMachine";

function App() {
  const [current, send] = useMachine(authMachine);

  const dummyRequest = async function () {
    console.log("sending dummy request");
    const res = await window.electronAPI.request({
      method: "GET",
      path_query: "/test",
      stream: false,
      headers: {},
    });
    console.log("received dummy response");
    console.log(res);
  };

  return (
    <div>
      {current.matches("preLogin") && (
        <div>
          <h2>PRELOGIN</h2>
          <div className="px-6 pt-4 pb-2">
            <Button
              type="primary"
              onClick={() => send({ type: "GO_OFFLINE" })}
              title="Work Offline"
              data-testid="offline-button"
            >
              Work Offline
            </Button>
            &nbsp;
            <Button
              type="primary"
              onClick={() => send({ type: "LOGIN_ATTEMPT" })}
              title="Work Online"
              data-testid="online-button"
            >
              Work Online
            </Button>
            <br />
            <br />
            <Button
              type="primary"
              onClick={() => dummyRequest()}
              title="Dummy Request"
              data-testid="dummy-button"
            >
              Dummy Request
            </Button>
          </div>
        </div>
      )}

      {current.matches("loggingIn") && (
        <div>
          <h2>LOGIN IN PROGRESS</h2>
          <div className="px-6 pt-4 pb-2">
            <Button
              type="primary"
              onClick={() => send({ type: "LOGIN_SUCCESS" })}
              title="FAKE_SUCESS"
              data-testid="offline-button"
            >
              it worked
            </Button>
            &nbsp;
            <Button
              type="primary"
              onClick={() => send({ type: "LOGIN_FAILURE" })}
              title="Work Online"
              data-testid="online-button"
            >
              it failed...
            </Button>
          </div>
        </div>
      )}

      {current.matches("loginFailure") && (
        <div>
          <h2>LOGIN FAILED</h2>
          <div className="px-6 pt-4 pb-2">
            <Button
              type="primary"
              onClick={() => send({ type: "LOGIN_ATTEMPT" })}
              title="Work Online"
              data-testid="online-button"
            >
              try again
            </Button>
          </div>
        </div>
      )}

      {current.matches("offlineMode") && (
        <div>
          <h2>Offline Mode Engaged</h2>
          <div className="px-6 pt-4 pb-2">
            <Button
              type="primary"
              onClick={() => send({ type: "GO_ONLINE" })}
              title="Work Online"
              data-testid="online-button"
            >
              Go Online
            </Button>
          </div>
        </div>
      )}

      {current.matches("onlineMode") && (
        <div className="max-w-sm rounded overflow-hidden shadow-lg">
          <div className="px-6 py-4">
            <div className="font-bold text-xl mb-2">
              Hello world! - We are online
            </div>
            <p className="text-gray-700 text-base">
              Lorem ipsum dolor sit amet, consectetur adipisicing elit.
              Voluptatibus quia, nulla! Maiores et perferendis eaque,
              exercitationem praesentium nihil.
            </p>
          </div>
          <div className="px-6 pt-4 pb-2">
            <Button
              type="primary"
              onClick={() => send({ type: "GO_OFFLINE" })}
              title="Dummy Request"
              data-testid="dummy-button"
            >
              Go Offline
            </Button>
          </div>
        </div>
      )}
    </div>
  );
}

export default App;
