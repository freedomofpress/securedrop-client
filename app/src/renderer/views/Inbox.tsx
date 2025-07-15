import { useNavigate } from "react-router";
import { Button } from "antd";

import { useAppDispatch } from "../hooks";
import { clear } from "../features/session/sessionSlice";

function InboxView() {
  const navigate = useNavigate();
  const dispatch = useAppDispatch();

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

  const signOut = () => {
    console.log("signing out");
    dispatch(clear());
    navigate("/");
  };

  return (
    <div>
      <div className="max-w-sm rounded overflow-hidden shadow-lg">
        <div className="px-6 py-4">
          <div className="font-bold text-xl mb-2">Hello world!</div>
          <p className="text-gray-700 text-base">
            Lorem ipsum dolor sit amet, consectetur adipisicing elit.
            Voluptatibus quia, nulla! Maiores et perferendis eaque,
            exercitationem praesentium nihil.
          </p>
        </div>
        <div className="px-6 pt-4 pb-2">
          <Button
            type="primary"
            onClick={() => dummyRequest()}
            title="Dummy Request"
            data-testid="dummy-button"
          >
            Dummy Request
          </Button>
        </div>
        <div className="px-6 pt-4 pb-2">
          <Button
            type="primary"
            onClick={() => signOut()}
            title="Sign Out"
            data-testid="sign-out-button"
          >
            Sign out
          </Button>
        </div>
      </div>
    </div>
  );
}

export default InboxView;
