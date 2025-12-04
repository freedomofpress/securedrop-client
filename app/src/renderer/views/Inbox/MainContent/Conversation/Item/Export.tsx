import { memo, useReducer, useEffect } from "react";
import { type Item } from "../../../../../../types";
import "../Item.css";
import "./File.css";

import { useTranslation } from "react-i18next";
import { LoaderCircle, FileX2, Inbox, Unlock } from "lucide-react";
import { Button, Modal, Input } from "antd";

type ExportState =
  | "PREFLIGHT"
  | "PREFLIGHT_COMPLETE"
  | "READY"
  | "UNLOCK_DEVICE"
  | "EXPORTING"
  | "SUCCESS"
  | "ERROR";

type ExportAction =
  | { type: "PREFLIGHT_COMPLETE" }
  | { type: "START_EXPORT" }
  | { type: "UNLOCK_DEVICE"; payload: string }
  | { type: "SET_PASSPHRASE"; payload: string }
  | { type: "GO_BACK" }
  | { type: "EXPORT_SUCCESS" }
  | { type: "EXPORT_ERROR"; payload: string }
  | { type: "CANCEL" };

interface ExportContext {
  state: ExportState;
  filename: string;
  passphrase: string;
  errorMessage: string;
}

const initialContext: ExportContext = {
  state: "PREFLIGHT",
  filename: "",
  passphrase: "",
  errorMessage: "",
};

function exportReducer(
  context: ExportContext,
  action: ExportAction,
): ExportContext {
  switch (context.state) {
    case "PREFLIGHT":
      switch (action.type) {
        case "PREFLIGHT_COMPLETE":
          return {
            ...context,
            state: "PREFLIGHT_COMPLETE",
          };
        case "CANCEL":
          return initialContext;
        default:
          return context;
      }

    case "PREFLIGHT_COMPLETE":
      switch (action.type) {
        case "START_EXPORT":
          return {
            ...context,
            state: "READY",
          };
        case "CANCEL":
          return initialContext;
        default:
          return context;
      }

    case "READY":
      switch (action.type) {
        case "START_EXPORT":
          return { ...context, state: "UNLOCK_DEVICE" };
        case "GO_BACK":
          return { ...context, state: "PREFLIGHT_COMPLETE" };
        case "CANCEL":
          return initialContext;
        default:
          return context;
      }

    case "UNLOCK_DEVICE":
      switch (action.type) {
        case "SET_PASSPHRASE":
          return { ...context, passphrase: action.payload };
        case "UNLOCK_DEVICE":
          return { ...context, state: "EXPORTING" };
        case "GO_BACK":
          return { ...context, state: "READY", passphrase: "" };
        case "CANCEL":
          return initialContext;
        default:
          return context;
      }

    case "EXPORTING":
      switch (action.type) {
        case "EXPORT_SUCCESS":
          return { ...context, state: "SUCCESS" };
        case "EXPORT_ERROR":
          return {
            ...context,
            state: "ERROR",
            errorMessage: action.payload,
          };
        default:
          return context;
      }

    case "SUCCESS":
    case "ERROR":
      // Terminal states
      switch (action.type) {
        case "CANCEL":
          return initialContext;
        default:
          return context;
      }

    default:
      return context;
  }
}

interface StateComponentProps {
  context: ExportContext;
  dispatch: React.Dispatch<ExportAction>;
  filename: string;
  t: (key: string) => string;
}

const PreflightState = memo(function PreflightState({
  context,
  t,
}: StateComponentProps) {
  return (
    <div>
      <div className="flex items-center gap-3 mb-4">
        {context.state === "PREFLIGHT" ? (
          <LoaderCircle
            className={"animate-spin text-blue-500"}
            size={24}
            strokeWidth={1}
          />
        ) : (
          <Inbox size={24} className="text-blue-500" />
        )}
        <div className="ml-3">
          <h3 className="text-lg font-semibold">
            {t("exportWizard.preparingExport")}
          </h3>
          <p className="text-gray-600">{context.filename}</p>
        </div>
      </div>
      <hr className="my-4 border-gray-300" />
      <div className="space-y-4">
        <h3 className="text-md font-semibold">
          {t("exportWizard.understandRisks")}
        </h3>
        <div>
          <p className="font-semibold">{t("exportWizard.malwareTitle")}</p>
          <p className="text-gray-600">{t("exportWizard.malwareWarning")}</p>
        </div>
        <div>
          <p className="font-semibold">{t("exportWizard.anonymityTitle")}</p>
          <p className="text-gray-600">{t("exportWizard.anonymityWarning")}</p>
        </div>
      </div>
    </div>
  );
});

const ReadyState = memo(function ReadyState({
  context,
  t,
}: StateComponentProps) {
  return (
    <div>
      <div className="flex items-center gap-3 mb-4">
        <Inbox size={24} className="text-blue-500" />
        <div className="ml-3">
          <h3 className="text-lg font-semibold">
            {t("exportWizard.readyExport")}
          </h3>
          <p className="text-gray-600">{context.filename}</p>
        </div>
      </div>
      <hr className="my-4 border-gray-300" />
      <div className="space-y-4">
        <p>{t("exportWizard.exportInstructions")}</p>
      </div>
    </div>
  );
});

const UnlockDeviceState = memo(function UnlockDeviceState({
  context,
  dispatch,
  t,
}: StateComponentProps) {
  const handlePassphraseChange = (e: React.ChangeEvent<HTMLInputElement>) => {
    dispatch({ type: "SET_PASSPHRASE", payload: e.target.value });
  };

  return (
    <div>
      <div className="flex items-center gap-3 mb-4">
        <Unlock size={24} className="text-blue-500" />
        <div className="ml-3">
          <h3 className="text-lg font-semibold">{t("exportWizard.unlock")}</h3>
        </div>
      </div>
      <hr className="my-4 border-gray-300" />
      <div className="space-y-4">
        <div>
          <label htmlFor="passphrase" className="block font-medium mb-2">
            {t("exportWizard.passphrase")}
          </label>
          <Input.Password
            id="passphrase"
            value={context.passphrase}
            onChange={handlePassphraseChange}
            placeholder={t("exportWizard.passphrase")}
            autoFocus
          />
        </div>
      </div>
    </div>
  );
});

const ExportingState = memo(function ExportingState({
  t,
}: StateComponentProps) {
  return (
    <div>
      <div className="flex items-center gap-3 mb-4">
        <Inbox size={24} className="text-blue-500" />
        <div className="ml-3">
          <h3 className="text-lg font-semibold">
            {t("exportWizard.pleaseWait")}
          </h3>
        </div>
      </div>
      <hr className="my-4 border-gray-300" />
      <div className="space-y-4">
        <h3 className="text-md font-semibold">{t("exportWizard.beCareful")}</h3>
      </div>
    </div>
  );
});

const SuccessState = memo(function SuccessState({ t }: StateComponentProps) {
  return (
    <div>
      <div className="flex items-center gap-3 mb-4">
        <Inbox size={24} className="text-blue-500" />
        <div className="ml-3">
          <h3 className="text-lg font-semibold">
            {t("exportWizard.exportSuccess")}
          </h3>
        </div>
      </div>
      <hr className="my-4 border-gray-300" />
      <div className="space-y-4">
        <h3 className="text-md font-semibold">{t("exportWizard.beCareful")}</h3>
      </div>
    </div>
  );
});

const ErrorState = memo(function ErrorState({
  context,
  t,
}: StateComponentProps) {
  return (
    <div className="text-center py-8">
      <FileX2 className="mx-auto mb-4 text-red-500" size={48} strokeWidth={2} />
      <h3 className="text-lg font-semibold mb-2 text-red-600">
        {t("exportWizard.exportFailed")}
      </h3>
      <p className="text-gray-600">{context.errorMessage}</p>
    </div>
  );
});

interface ExportWizardProps {
  item: Item;
  open: boolean;
  onClose: () => void;
}

export const ExportWizard = memo(function ExportWizard({
  item,
  open,
  onClose,
}: ExportWizardProps) {
  const { t } = useTranslation("Item");
  const [context, dispatch] = useReducer(exportReducer, initialContext);

  const filename = item.filename
    ? item.filename.substring(item.filename.lastIndexOf("/") + 1)
    : "";
  context.filename = filename;

  // Reset state when wizard is closed
  useEffect(() => {
    if (!open) {
      dispatch({ type: "CANCEL" });
    }
  }, [open]);

  // TODO(vicki): remove once we trigger preflight for real
  // Simulate preflight progression
  useEffect(() => {
    if (context.state === "PREFLIGHT") {
      const timer = setTimeout(() => {
        dispatch({ type: "PREFLIGHT_COMPLETE" });
      }, 1500); // 1.5 second delay

      return () => clearTimeout(timer);
    }
    return;
  }, [context.state]);

  // Handle export logic
  useEffect(() => {
    if (context.state === "EXPORTING") {
      const performExport = async () => {
        try {
          // TODO(vicki): call export from backend
          dispatch({ type: "EXPORT_SUCCESS" });
        } catch (error) {
          console.error("Failed to export file:", error);
          const errorMessage =
            error instanceof Error
              ? error.message
              : t("exportWizard.unknownError");
          dispatch({ type: "EXPORT_ERROR", payload: errorMessage });
        }
      };
      performExport();
    }
  }, [context.state, item.uuid, t]);

  const handleClose = () => {
    dispatch({ type: "CANCEL" });
    onClose();
  };

  const renderStateComponent = () => {
    const stateProps = { context, dispatch, filename, t };

    switch (context.state) {
      case "PREFLIGHT":
        return <PreflightState {...stateProps} />;
      case "PREFLIGHT_COMPLETE":
        return <PreflightState {...stateProps} />;
      case "READY":
        return <ReadyState {...stateProps} />;
      case "UNLOCK_DEVICE":
        return <UnlockDeviceState {...stateProps} />;
      case "EXPORTING":
        return <ExportingState {...stateProps} />;
      case "SUCCESS":
        return <SuccessState {...stateProps} />;
      case "ERROR":
        return <ErrorState {...stateProps} />;
      default:
        return null;
    }
  };

  const renderFooter = () => {
    switch (context.state) {
      case "PREFLIGHT":
        return [
          <Button key="continue" type="primary" disabled>
            {t("exportWizard.continue")}
          </Button>,
          <Button key="cancel" onClick={handleClose}>
            {t("exportWizard.cancel")}
          </Button>,
        ];

      case "PREFLIGHT_COMPLETE":
        return [
          <Button
            key="continue"
            type="primary"
            onClick={() => {
              dispatch({ type: "START_EXPORT" });
            }}
          >
            {t("exportWizard.continue")}
          </Button>,
          <Button key="cancel" onClick={handleClose}>
            {t("exportWizard.cancel")}
          </Button>,
        ];

      case "READY":
        return [
          <Button key="back" onClick={() => dispatch({ type: "GO_BACK" })}>
            {t("exportWizard.back")}
          </Button>,
          <Button
            key="export"
            type="primary"
            onClick={() => dispatch({ type: "START_EXPORT" })}
          >
            {t("exportWizard.continue")}
          </Button>,
          <Button key="cancel" onClick={handleClose}>
            {t("exportWizard.cancel")}
          </Button>,
        ];

      case "UNLOCK_DEVICE":
        return [
          <Button key="back" onClick={() => dispatch({ type: "GO_BACK" })}>
            {t("exportWizard.back")}
          </Button>,
          <Button
            key="export"
            type="primary"
            disabled={!context.passphrase}
            onClick={() =>
              dispatch({ type: "UNLOCK_DEVICE", payload: context.passphrase })
            }
          >
            {t("exportWizard.continue")}
          </Button>,
          <Button key="cancel" onClick={handleClose}>
            {t("exportWizard.cancel")}
          </Button>,
        ];

      case "EXPORTING":
        // No buttons during export
        return null;

      case "SUCCESS":
        return [
          <Button key="close" onClick={handleClose}>
            {t("exportWizard.done")}
          </Button>,
        ];

      case "ERROR":
        return [
          <Button key="close" onClick={handleClose}>
            {t("exportWizard.close")}
          </Button>,
        ];

      default:
        return null;
    }
  };

  const isNonClosableState =
    context.state === "EXPORTING" || context.state === "PREFLIGHT";

  return (
    <Modal
      open={open}
      onCancel={handleClose}
      footer={renderFooter()}
      width={600}
      closable={!isNonClosableState}
      maskClosable={!isNonClosableState}
    >
      {renderStateComponent()}
    </Modal>
  );
});
