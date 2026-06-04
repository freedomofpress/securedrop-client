import { Button, Input, Form, theme } from "antd";
import type { FormProps, InputRef } from "antd";
import { Eye, EyeOff } from "lucide-react";
import { CloseOutlined, CloseCircleFilled } from "@ant-design/icons";
import { useState, useCallback, useEffect, useRef } from "react";
import { useNavigate } from "react-router";
import { useTranslation } from "react-i18next";

import { useAppDispatch, useAppSelector } from "../hooks";
import {
  setAuth,
  setUnauth,
  setOffline,
  clearError,
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
  const session = useAppSelector((state) => state.session);
  const { token } = theme.useToken();

  const errorMessageNetwork = {
    header: t("errors.network.header"),
    body: t("errors.network.body"),
  };
  const errorMessageCredentials = {
    header: t("errors.credentials.header"),
    body: t("errors.credentials.body"),
  };
  const errorMessageGeneric = {
    header: t("errors.generic.header"),
    body: t("errors.generic.body"),
  };

  const usernameInputRef = useRef<InputRef>(null);

  const [form] = Form.useForm();
  const [version, _setVersion] = useState<string>(__APP_VERSION__ || "Unknown");
  const [authError, setAuthError] = useState<boolean>(false);
  const [authErrorMessage, setAuthErrorMessage] = useState<{
    header: string;
    body: string;
  }>(errorMessageGeneric);
  const [isSubmitting, setIsSubmitting] = useState<boolean>(false);
  const [hasValidationErrors, setHasValidationErrors] =
    useState<boolean>(false);
  const [passwordVisible, setPasswordVisible] = useState<boolean>(false);

  const togglePasswordVisibility = useCallback(() => {
    setPasswordVisible((v) => !v);
  }, []);

  // Focus the username input on mount
  useEffect(() => {
    usernameInputRef.current?.focus();
  }, []);

  // Display error from session state (e.g., session expired)
  useEffect(() => {
    if (session.errorMessage) {
      setAuthError(true);
      setAuthErrorMessage({
        header: session.errorMessage,
        body: "",
      });
      // Clear the error from session state
      dispatch(clearError());
    }
  }, [session.errorMessage, dispatch]);

  const onFinish: FormProps<FormValues>["onFinish"] = async (
    values: FormValues,
  ) => {
    // Clear any previous errors and set loading state
    setAuthError(false);
    setHasValidationErrors(false);
    setIsSubmitting(true);

    // Authenticate to the API
    try {
      const result = await window.electronAPI.login({
        username: values.username,
        passphrase: values.passphrase,
        oneTimeCode: values.oneTimeCode,
      });

      if (!result.success) {
        console.error("Authentication failed:", result.errorType);
        if (result.errorType === "credentials") {
          setAuthErrorMessage(errorMessageCredentials);
        } else if (result.errorType === "network") {
          setAuthErrorMessage(errorMessageNetwork);
        } else {
          setAuthErrorMessage(errorMessageGeneric);
        }
        setAuthError(true);
        return;
      }

      try {
        // Update the session state
        dispatch(
          setAuth({
            expiration: result.expiration,
            journalistUUID: result.journalistUUID,
            journalistFirstName: result.journalistFirstName,
            journalistLastName: result.journalistLastName,
            lastHintedVersion: result.lastHintedVersion,
            lastHintedSources: result.lastHintedSources,
            lastHintedItems: result.lastHintedItems,
          } as AuthData),
        );

        // Clear the clipboard in case they pasted their password
        window.electronAPI.clearClipboard();

        // Redirect to home
        navigate("/");
      } catch (e) {
        console.error("Failed to update session state:", e);
        dispatch(setUnauth(undefined));

        setAuthErrorMessage(errorMessageGeneric);
        setAuthError(true);
      }
    } catch (e) {
      console.error("Login IPC failed:", e);
      dispatch(setUnauth(undefined));

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
            <div className="absolute top-14 -left-8 -right-8 p-4 bg-red-50 border border-red-200 rounded-lg z-10">
              <button
                onClick={() => setAuthError(false)}
                className="absolute top-3 right-3 text-gray-400 hover:text-gray-600"
                aria-label="Close error message"
              >
                <CloseOutlined style={{ fontSize: 14 }} />
              </button>
              <div className="flex gap-3 items-start">
                <CloseCircleFilled
                  style={{ fontSize: 24, color: token.colorError }}
                  className="flex-shrink-0"
                />
                <div>
                  <p
                    className="text-sm font-semibold"
                    style={{ color: token.colorText }}
                  >
                    {authErrorMessage.header}
                  </p>
                  <p
                    className="text-sm mt-1"
                    style={{ color: token.colorText }}
                  >
                    {authErrorMessage.body}
                  </p>
                </div>
              </div>
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
              <Input
                ref={usernameInputRef}
                data-testid="username-input"
                placeholder="nelliebly"
              />
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
              <Input
                data-testid="passphrase-input"
                type={passwordVisible ? "text" : "password"}
                placeholder="••••••••••••••••••••••••"
                suffix={
                  <button
                    type="button"
                    className="flex items-center text-gray-400 hover:text-gray-600 bg-transparent border-0 p-0 cursor-pointer rounded focus-visible:outline-none focus-visible:ring-1 focus-visible:ring-blue-500"
                    onClick={togglePasswordVisibility}
                    aria-pressed={passwordVisible}
                    aria-label={
                      passwordVisible
                        ? t("passphrase.hidePassphrase")
                        : t("passphrase.showPassphrase")
                    }
                  >
                    {passwordVisible ? <Eye size={18} /> : <EyeOff size={18} />}
                  </button>
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
