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
    const res = await window.electronAPI.requestStream({
      method: "GET",
      path_query: "/html",
      headers: {},
      stream: true,
    }, "/tmp/download");
    console.log("received dummy stream response");
    console.log(res);
  };

  return (
    <div>
      <p>Hello world</p>
      <button onClick={() => dummyRequest()} title="Dummy Request">
        Dummy Request
      </button>
      <button onClick={() => dummyStreamRequest()} title="Dummy Stream Request">
        Dummy Stream Request
      </button>
    </div>
  );
}

export default App;
