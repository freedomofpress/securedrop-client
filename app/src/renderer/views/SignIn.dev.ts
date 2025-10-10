/**
 * Development-only auto-login functionality.
 * This file is only imported in development builds and will not be included in production.
 */

import { TOTP } from "otpauth";
import type { FormInstance } from "antd";

type FormValues = {
  username: string;
  passphrase: string;
  oneTimeCode: string;
};

export async function performAutoLogin(
  form: FormInstance<FormValues>,
): Promise<void> {
  const autoLoginEnabled = await window.electronAPI.shouldAutoLogin();
  if (!autoLoginEnabled) {
    return;
  }

  console.log("Auto-login enabled, filling credentials...");

  const totp = new TOTP({
    secret: "JHCOGO7VCER3EJ4L",
  });
  const oneTimeCode = totp.generate();

  form.setFieldsValue({
    username: "journalist",
    passphrase: "correct horse battery staple profanity oil chewy",
    oneTimeCode: oneTimeCode,
  });

  // Submit the form after a brief delay to allow UI to update
  setTimeout(() => {
    form.submit();
  }, 1000);
}
