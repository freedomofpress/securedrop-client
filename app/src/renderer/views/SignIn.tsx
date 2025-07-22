import { Button, Input, Form } from "antd";
import type { FormProps } from "antd";
import { EyeInvisibleOutlined, EyeOutlined } from "@ant-design/icons";
import { useState } from "react";
import { useNavigate } from "react-router";
import { useTranslation } from "react-i18next";

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
  const { t } = useTranslation("SignIn");

  const errorMessageNetwork = t("errors.network");
  const errorMessageCredentials = t("errors.credentials");
  const errorMessageGeneric = t("errors.generic");

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

          <h1 className="mb-6">{t("title")}</h1>
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
              label={t("username.label")}
              name="username"
              rules={[
                { required: true, message: t("username.required") },
                {
                  min: 3,
                  message: t("username.minLength"),
                },
              ]}
            >
              <Input data-testid="username-input" placeholder="neliebly" />
            </Form.Item>

            <Form.Item
              data-testid="passphrase-form-item"
              label={t("passphrase.label")}
              name="passphrase"
              rules={[
                { required: true, message: t("passphrase.required") },
                {
                  min: 14,
                  message: t("passphrase.invalidLength"),
                },
                {
                  max: 128,
                  message: t("passphrase.invalidLength"),
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
              label={t("twoFactorCode.label")}
              name="oneTimeCode"
              rules={[
                {
                  required: true,
                  message: t("twoFactorCode.required"),
                },
                {
                  pattern: /^\d{6}$/,
                  message: t("twoFactorCode.invalidFormat"),
                },
              ]}
            >
              <Input
                data-testid="one-time-code-input"
                placeholder="338578"
                maxLength={6}
                onKeyPress={(e) => {
                  // Allow Enter key for form submission
                  if (e.key === "Enter") {
                    return;
                  }
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
                {isSubmitting ? t("button.signingIn") : t("button.signIn")}
              </Button>

              <Button
                data-testid="use-offline-button"
                type="text"
                color="primary"
                className="w-full mt-4 use-offline-button"
                onClick={useOffline}
              >
                {t("button.useOffline")}
              </Button>
            </Form.Item>
          </Form>
        </div>

        <div className="mt-8 text-center">
          <p className="text-sm text-gray-500">{t("version", { version })}</p>
        </div>
      </div>
    </div>
  );
}

export default SignInView;
