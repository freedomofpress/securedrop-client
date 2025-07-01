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
      <p>Hello world</p>
      <button onClick={() => dummyRequest()} title="Dummy Request">
        Dummy Request
      </button>
    </div>
  );
}

export default App;
