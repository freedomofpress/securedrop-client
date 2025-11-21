import { Button, Input, Form } from "antd";
import type { FormProps } from "antd";
import { Eye, EyeOff } from "lucide-react";
import { useState, useEffect, useRef } from "react";
import { useNavigate } from "react-router";
import { useTranslation } from "react-i18next";

import type { ProxyRequest } from "../../types";
import { TokenResponseSchema } from "../../schemas";
import { useAppDispatch } from "../hooks";
import {
  setAuth,
  setUnauth,
  setOffline,
} from "../features/session/sessionSlice";
import type { AuthData } from "../features/session/sessionSlice";

import logoImage from "../../../resources/images/logo.png";
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
  const [hasValidationErrors, setHasValidationErrors] =
    useState<boolean>(false);

  const onFinish: FormProps<FormValues>["onFinish"] = async (
    values: FormValues,
  ) => {
    // Clear any previous errors and set loading state
    setAuthError(false);
    setHasValidationErrors(false);
    setIsSubmitting(true);

    // Authenticate to the API
    try {
      const res = await window.electronAPI.request({
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

      if (!res.data) {
        console.error("Authentication failed: no data received");
        setAuthErrorMessage(errorMessageGeneric);
        setAuthError(true);
        return;
      }

      try {
        const resp = TokenResponseSchema.parse(res.data);

        // Update the session state
        dispatch(
          setAuth({
            expiration: resp.expiration,
            token: resp.token,
            journalistUUID: resp.journalist_uuid,
            journalistFirstName: resp.journalist_first_name,
            journalistLastName: resp.journalist_last_name,
          } as AuthData),
        );

        // Clear the clipboard in case they pasted their password
        window.electronAPI.clearClipboard();

        // Redirect to home
        navigate("/");
      } catch (e) {
        console.error("Failed to validate or update session state:", e);
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

  const onFinishFailed: FormProps<FormValues>["onFinishFailed"] = () => {
    setHasValidationErrors(true);
  };

  const onValuesChange: FormProps<FormValues>["onValuesChange"] = async (
    _changedValues: Partial<FormValues>,
    _allValues: Partial<FormValues>,
  ) => {
    // Disable auth error
    if (authError) {
      setAuthError(false);
    }

    // Clear validation errors only if there are any, and only once per form submission cycle
    if (hasValidationErrors) {
      setHasValidationErrors(false);
      form.setFields([
        { name: "username", errors: [] },
        { name: "passphrase", errors: [] },
        { name: "oneTimeCode", errors: [] },
      ]);
    }
  };

  const useOffline = () => {
    // Update the session state to offline mode
    dispatch(setOffline());

    // Redirect to home
    navigate("/");
  };

  // Dev-only auto-login: will be compiled out in production builds
  if (__DEV_AUTO_LOGIN__) {
    // Track execution to prevent double-triggering in React Strict Mode
    // eslint-disable-next-line react-hooks/rules-of-hooks
    const autoLoginExecutedRef = useRef<boolean>(false);

    // eslint-disable-next-line react-hooks/rules-of-hooks
    useEffect(() => {
      if (!autoLoginExecutedRef.current) {
        autoLoginExecutedRef.current = true;
        import("./SignIn.dev").then(({ performAutoLogin }) => {
          performAutoLogin(form);
        });
      }
    }, [form]);
  }

  return (
    <div className="min-h-screen bg-gray-50 flex flex-col justify-center py-8 sm:px-6 lg:px-8 sign-in-container">
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
            onFinishFailed={onFinishFailed}
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
                  visible ? <Eye size={18} /> : <EyeOff size={18} />
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
