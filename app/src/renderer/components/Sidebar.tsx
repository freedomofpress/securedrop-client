import { Button } from "antd";
import { UserOutlined } from "@ant-design/icons";

function Sidebar() {
  return (
    <div className="sd-border-secondary w-90 flex flex-col h-full border-r">
      <div className="sd-border-secondary sd-bg-primary border-b p-2 h-12">
        <Button
          icon={<UserOutlined />}
          type="text"
          className="flex items-center gap-2"
        >
          Account
        </Button>
      </div>

      <div className="sd-bg-primary flex-1 overflow-y-auto"></div>
    </div>
  );
}

export default Sidebar;
