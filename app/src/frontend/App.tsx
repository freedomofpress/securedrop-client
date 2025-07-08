import { Button } from "antd";

function App() {
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
          >
            Dummy Request
          </Button>
        </div>
      </div>
    </div>
  );
}

export default App;
