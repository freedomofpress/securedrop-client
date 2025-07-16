import { Button, Input, Form } from "antd";
import { EyeInvisibleOutlined, EyeTwoTone } from "@ant-design/icons";
import { useState, useEffect } from "react";
import { useNavigate } from "react-router";

import type { ProxyRequest, ProxyJSONResponse } from "../../types";
import { useAppDispatch } from "../hooks";
import type { SessionState } from "../features/session/sessionSlice";
import { set, clear } from "../features/session/sessionSlice";
import logoImage from "../../../resources/images/logo.png";

type FormValues = {
  username: string;
  passphrase: string;
  oneTimeCode: string;
};

function SignInView() {
  const dispatch = useAppDispatch();
  const navigate = useNavigate();

  const errorMessageNetwork =
    "Could not reach the SecureDrop server. Please check your Internet and Tor connection and try again.";
  const errorMessageCredentials =
    "Those credentials didn't work. Please try again, and make sure to use a new two-factor code.";
  const errorMessageGeneric =
    "That didn't work. Please check everything and try again.";

  const [form] = Form.useForm();
  const [version, setVersion] = useState<string>("");
  const [authError, setAuthError] = useState<boolean>(false);
  const [authErrorMessage, setAuthErrorMessage] =
    useState<string>(errorMessageGeneric);
  const [isSubmitting, setIsSubmitting] = useState<boolean>(false);

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
    // Clear any previous errors and set loading state
    setAuthError(false);
    setIsSubmitting(true);

    // Authenticate to the API
    try {
      const res: ProxyJSONResponse = await window.electronAPI.request({
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

      // If the status is not 200, fail
      if (res.status !== 200) {
        console.error("Authentication failed:", res.data);
        setAuthErrorMessage(errorMessageCredentials);
        setAuthError(true);
        return;
      }

      try {
        // Update the session state
        dispatch(
          set({
            expiration: res.data.expiration,
            token: res.data.token,
            journalist_uuid: res.data.journalist_uuid,
            journalist_first_name: res.data.journalist_first_name,
            journalist_last_name: res.data.journalist_last_name,
          } as SessionState),
        );

        // Redirect to home
        navigate("/");
      } catch (e) {
        console.error("Failed to update session state:", e);
        dispatch(clear());

        setAuthErrorMessage(errorMessageGeneric);
        setAuthError(true);
      }
    } catch (e) {
      console.error("Proxy request failed:", e);
      dispatch(clear());

      setAuthErrorMessage(errorMessageNetwork);
      setAuthError(true);

      return;
    } finally {
      // Always re-enable the button when done
      setIsSubmitting(false);
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

        {authError && (
          <div className="mb-6 p-4 bg-red-50 border border-red-200 rounded-lg">
            <p className="text-sm text-red-700 text-center">
              {authErrorMessage}
            </p>
          </div>
        )}

        <div className="bg-white py-8 px-6 shadow-sm rounded-lg sm:px-10">
          <Form
            form={form}
            onFinish={handleSubmit}
            layout="vertical"
            className="space-y-6"
          >
            <Form.Item
              data-testid="username-form-item"
              label={
                <span className="text-sm font-medium text-gray-700">
                  Username
                </span>
              }
              name="username"
              rules={[
                { required: true, message: "Please enter your username." },
                {
                  min: 3,
                  message:
                    "That username won't work. It should be at least 3 characters long.",
                },
              ]}
            >
              <Input
                data-testid="username-input"
                placeholder="neliebly"
                className="h-10 text-sm"
                style={{ borderRadius: "6px" }}
              />
            </Form.Item>

            <Form.Item
              data-testid="passphrase-form-item"
              label={
                <span className="text-sm font-medium text-gray-700">
                  Passphrase
                </span>
              }
              name="passphrase"
              rules={[
                { required: true, message: "Please enter your passphrase." },
                {
                  min: 14,
                  message:
                    "That passphrase won't work. It should be between 14 and 128 characters long.",
                },
                {
                  max: 128,
                  message:
                    "That passphrase won't work. It should be between 14 and 128 characters long.",
                },
              ]}
            >
              <Input.Password
                data-testid="passphrase-input"
                placeholder="••••••••••••••••••••••••"
                className="h-10 text-sm"
                style={{ borderRadius: "6px" }}
                iconRender={(visible) =>
                  visible ? <EyeTwoTone /> : <EyeInvisibleOutlined />
                }
              />
            </Form.Item>

            <Form.Item
              data-testid="one-time-code-form-item"
              label={
                <span className="text-sm font-medium text-gray-700">
                  Two-Factor Code
                </span>
              }
              name="oneTimeCode"
              rules={[
                {
                  required: true,
                  message: "Please enter your two-factor code.",
                },
                {
                  pattern: /^\d{6}$/,
                  message: "Your two-factor code must be exactly 6 digits.",
                },
              ]}
            >
              <Input
                data-testid="one-time-code-input"
                placeholder="338578"
                className="h-10 text-sm"
                style={{ borderRadius: "6px" }}
                maxLength={6}
                onKeyPress={(e) => {
                  // Only allow numeric characters
                  if (!/[0-9]/.test(e.key)) {
                    e.preventDefault();
                  }
                }}
                onChange={(e) => {
                  // Remove any non-numeric characters
                  const numericValue = e.target.value.replace(/\D/g, "");
                  if (numericValue !== e.target.value) {
                    form.setFieldValue("oneTimeCode", numericValue);
                  }
                }}
              />
            </Form.Item>

            <Form.Item className="mb-0">
              <Button
                data-testid="sign-in-button"
                type="primary"
                htmlType="submit"
                loading={isSubmitting}
                disabled={isSubmitting}
                className="w-full h-10 text-sm font-medium"
                style={{
                  borderRadius: "6px",
                  backgroundColor: "#4F46E5",
                  borderColor: "#4F46E5",
                }}
              >
                {isSubmitting ? "Signing in..." : "Sign in"}
              </Button>
            </Form.Item>
          </Form>
        </div>

        <div className="mt-8 text-center">
          <p className="text-sm text-gray-500">SecureDrop App v{version}</p>
        </div>
      </div>
    </div>
  );
}

export default SignInView;
