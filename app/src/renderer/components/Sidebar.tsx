import { Button } from "antd";
import { UserOutlined } from "@ant-design/icons";

function Sidebar() {
  return (
    <div className="w-90 flex flex-col h-full border-r border-gray-200">
      <div className="bg-white border-b border-gray-200 p-2 h-12">
        <Button
          icon={<UserOutlined />}
          type="text"
          className="flex items-center gap-2"
        >
          Account
        </Button>
      </div>

      <div className="flex-1 overflow-y-auto bg-white"></div>
    </div>
  );
}

export default Sidebar;
