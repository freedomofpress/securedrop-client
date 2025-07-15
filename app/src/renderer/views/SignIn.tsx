import { Button, Input, Form } from "antd";
import { EyeInvisibleOutlined, EyeTwoTone } from "@ant-design/icons";
import { useState, useEffect } from "react";

import type { ProxyRequest, ProxyResponse } from "../../types";
import { useAppDispatch, useAppSelector } from "../hooks";
import type { SessionState } from "../features/session/sessionSlice";
import { set, clear } from "../features/session/sessionSlice";
import logoImage from "../../../resources/images/logo.png";

type FormValues = {
  username: string;
  passphrase: string;
  oneTimeCode: string;
};

function SignInView() {
  const session = useAppSelector((state) => state.session);
  const dispatch = useAppDispatch();

  const [form] = Form.useForm();
  const [version, setVersion] = useState<string>("");

  // We cannot use the async function directly in the React component, so we need to get
  // the version in a useEffect hook.
  useEffect(() => {
    const getVersion = async () => {
      try {
        const appVersion = await window.electronAPI.getVersion();
        setVersion(appVersion);
      } catch (error) {
        console.error("Failed to get app version:", error);
        setVersion("Unknown");
      }
    };

    getVersion();
  }, []);

  const handleSubmit = async (values: FormValues) => {
    console.log("Form values:", values);

    // Authenticate to the API
    try {
      const res: ProxyResponse = await window.electronAPI.request({
        method: "POST",
        path_query: "/api/v1/token",
        stream: false,
        body: JSON.stringify({
          username: values.username,
          passphrase: values.passphrase,
          one_time_code: values.oneTimeCode,
        }),
        headers: {},
      } as ProxyRequest);

      if (res.status !== 200) {
        console.error("Authentication failed:", res.data);
        return;
      }

      try {
        dispatch(
          set({
            expiration: new Date(res.data.expiration as string),
            token: res.data.token,
            journalist_uuid: res.data.journalist_uuid,
            journalist_first_name: res.data.journalist_first_name,
            journalist_last_name: res.data.journalist_last_name,
          } as SessionState),
        );
      } catch (e) {
        console.error(e);
        dispatch(clear());
      }
    } catch (e) {
      console.error("Authentication failed:");
      console.log(e);
      dispatch(clear());
      return;
    }
  };

  return (
    <div className="min-h-screen bg-gray-50 flex flex-col justify-center py-8 sm:px-6 lg:px-8">
      <div className="sm:mx-auto sm:w-full sm:max-w-md">
        <div className="flex justify-center mb-6">
          <img src={logoImage} alt="SecureDrop" className="w-16 h-16" />
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
              name="oneTimeCode"
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
