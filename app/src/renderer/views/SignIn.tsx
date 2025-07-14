import { Button, Input, Form } from "antd";
import { EyeInvisibleOutlined, EyeTwoTone } from "@ant-design/icons";

function SignInView() {
  const [form] = Form.useForm();

  const version = window.electronAPI.getVersion();

  const handleSubmit = (values: any) => {
    console.log("Form values:", values);
  };

  return (
    <div className="min-h-screen bg-gray-50 flex flex-col justify-center py-8 sm:px-6 lg:px-8">
      <div className="sm:mx-auto sm:w-full sm:max-w-md">
        <div className="flex justify-center mb-6">
          <img
            src="./resources/images/logo.png"
            alt="SecureDrop"
            className="w-16 h-16"
          />
        </div>

        <h1 className="text-2xl font-medium text-gray-900 text-center mb-6">
          Sign in to SecureDrop
        </h1>

        <div className="bg-white py-8 px-6 shadow-sm rounded-lg sm:px-10">
          <Form
            form={form}
            onFinish={handleSubmit}
            layout="vertical"
            className="space-y-6"
          >
            <Form.Item
              label={
                <span className="text-sm font-medium text-gray-700">
                  Username
                </span>
              }
              name="username"
              rules={[
                { required: true, message: "Please enter your username" },
              ]}
            >
              <Input
                placeholder="neliebly"
                className="h-10 text-sm"
                style={{ borderRadius: "6px" }}
              />
            </Form.Item>

            <Form.Item
              label={
                <span className="text-sm font-medium text-gray-700">
                  Passphrase
                </span>
              }
              name="passphrase"
              rules={[
                { required: true, message: "Please enter your passphrase" },
              ]}
            >
              <Input.Password
                placeholder="••••••••••••••••••••••••"
                className="h-10 text-sm"
                style={{ borderRadius: "6px" }}
                iconRender={(visible) =>
                  visible ? <EyeTwoTone /> : <EyeInvisibleOutlined />
                }
              />
            </Form.Item>

            <Form.Item
              label={
                <span className="text-sm font-medium text-gray-700">
                  Two-Factor Code
                </span>
              }
              name="twoFactorCode"
              rules={[
                {
                  required: true,
                  message: "Please enter your two-factor code",
                },
              ]}
            >
              <Input
                placeholder="338578"
                className="h-10 text-sm"
                style={{ borderRadius: "6px" }}
                maxLength={6}
              />
            </Form.Item>

            <Form.Item className="mb-0">
              <Button
                type="primary"
                htmlType="submit"
                className="w-full h-10 text-sm font-medium"
                style={{
                  borderRadius: "6px",
                  backgroundColor: "#4F46E5",
                  borderColor: "#4F46E5",
                }}
              >
                Sign in
              </Button>
            </Form.Item>
          </Form>
        </div>

        <div className="mt-8 text-center">
          <p className="text-sm text-gray-500">SecureDrop Client v{version}</p>
        </div>
      </div>
    </div>
  );
}

export default SignInView;
