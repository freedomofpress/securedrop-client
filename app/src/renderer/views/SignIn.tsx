import { Button, Input, Form } from "antd";
import type { FormProps } from "antd";
import { EyeInvisibleOutlined, EyeOutlined } from "@ant-design/icons";
import { useState } from "react";
import { useNavigate } from "react-router";

import type { ProxyRequest, ProxyJSONResponse } from "../../types";
import { useAppDispatch } from "../hooks";
import {
  setAuth,
  setUnauth,
  setOffline,
} from "../features/session/sessionSlice";
import type { AuthData } from "../features/session/sessionSlice";

import logoImage from "../../../resources/images/logo.png";
import backgroundImage from "../../../resources/images/sign-in-background.svg";
import "./SignIn.css";

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
  const [version, _setVersion] = useState<string>(__APP_VERSION__ || "Unknown");
  const [authError, setAuthError] = useState<boolean>(false);
  const [authErrorMessage, setAuthErrorMessage] =
    useState<string>(errorMessageGeneric);
  const [isSubmitting, setIsSubmitting] = useState<boolean>(false);

  const onFinish: FormProps<FormValues>["onFinish"] = async (
    values: FormValues,
  ) => {
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
          setAuth({
            expiration: res.data.expiration,
            token: res.data.token,
            journalistUUID: res.data.journalist_uuid,
            journalistFirstName: res.data.journalist_first_name,
            journalistLastName: res.data.journalist_last_name,
          } as AuthData),
        );

        // Redirect to home
        navigate("/");
      } catch (e) {
        console.error("Failed to update session state:", e);
        dispatch(setUnauth());

        setAuthErrorMessage(errorMessageGeneric);
        setAuthError(true);
      }
    } catch (e) {
      console.error("Proxy request failed:", e);
      dispatch(setUnauth());

      setAuthErrorMessage(errorMessageNetwork);
      setAuthError(true);

      return;
    } finally {
      // Always re-enable the button when done
      setIsSubmitting(false);
    }
  };

  const onValuesChange: FormProps<FormValues>["onValuesChange"] = async (
    _changedValues: Partial<FormValues>,
    _allValues: Partial<FormValues>,
  ) => {
    // Disable auth error
    if (authError) {
      setAuthError(false);
    }
    // Disable validation errors
    form.setFields([
      { name: "username", errors: [] },
      { name: "passphrase", errors: [] },
      { name: "oneTimeCode", errors: [] },
    ]);
  };

  const useOffline = () => {
    // Update the session state to offline mode
    dispatch(setOffline());

    // Redirect to home
    navigate("/");
  };

  return (
    <div
      className="min-h-screen bg-gray-50 flex flex-col justify-center py-8 sm:px-6 lg:px-8 sign-in-container"
      style={{
        backgroundImage: `url(${backgroundImage})`,
      }}
    >
      <div className="sm:mx-auto sm:w-full sm:max-w-md">
        <div className="relative mb-6">
          <div className="flex justify-center mb-6">
            <img src={logoImage} alt="SecureDrop" className="logo" />
          </div>

          <h1 className="mb-0">Sign in to SecureDrop</h1>

          {authError && (
            <div className="absolute top-14 left-0 right-0 p-4 bg-red-50 border border-red-200 rounded-lg shadow-lg z-10">
              <p className="text-sm text-red-700 text-center">
                {authErrorMessage}
              </p>
            </div>
          )}
        </div>

        <div className="bg-white py-6 px-8 shadow-sm rounded-lg">
          <Form
            form={form}
            onFinish={onFinish}
            onValuesChange={onValuesChange}
            layout="vertical"
            className="space-y-6"
            validateTrigger="onSubmit"
            requiredMark={false}
          >
            <Form.Item
              data-testid="username-form-item"
              label="Username"
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
              <Input data-testid="username-input" placeholder="neliebly" />
            </Form.Item>

            <Form.Item
              data-testid="passphrase-form-item"
              label="Passphrase"
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
                iconRender={(visible) =>
                  visible ? <EyeOutlined /> : <EyeInvisibleOutlined />
                }
              />
            </Form.Item>

            <Form.Item
              data-testid="one-time-code-form-item"
              label="Two-Factor Code"
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

            <Form.Item className="button-container">
              <Button
                data-testid="sign-in-button"
                type="primary"
                size="large"
                htmlType="submit"
                loading={isSubmitting}
                disabled={isSubmitting}
                className="w-full"
              >
                {isSubmitting ? "Signing in..." : "Sign in"}
              </Button>

              <Button
                data-testid="use-offline-button"
                type="text"
                color="primary"
                className="w-full mt-4 use-offline-button"
                onClick={useOffline}
              >
                Use offline
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
