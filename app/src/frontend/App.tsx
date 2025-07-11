import { Button } from "antd";

function App() {
  const dummyRequest = async function () {
    console.log("sending dummy request");
    const res = await window.electronAPI.request({
      method: "GET",
      path_query: "/json",
      headers: {},
      stream: false,
    });
    console.log("received dummy response");
    console.log(res);
  };

  const dummyStreamRequest = async function () {
    console.log("sending dummy stream request");
    const res = await window.electronAPI.requestStream(
      {
        method: "GET",
        path_query: "/html",
        headers: {},
        stream: true,
      },
      "/tmp/download",
    );
    console.log("received dummy stream response");
    console.log(res);
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

          <Button
            type="default"
            onClick={() => dummyStreamRequest()}
            title="Dummy Stream Request"
            data-testid="dummy-stream-button"
          >
            Dummy Stream Request
          </Button>
        </div>
      </div>
    </div>
  );
}

export default App;
