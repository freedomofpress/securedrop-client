import { memo, useReducer, useEffect, useRef } from "react";
import {
  type Item,
  DeviceStatus,
  ExportStatus,
  DeviceErrorStatus,
} from "../../../../../../types";
import "../Item.css";
import "./File.css";

import { useTranslation } from "react-i18next";
import { LoaderCircle, FileX2, Inbox, Unlock } from "lucide-react";
import { Button, Modal, Input } from "antd";

type ExportState =
  | "PREFLIGHT"
  | "PREFLIGHT_COMPLETE"
  | "PREFLIGHT_INSERT_USB"
  | "INSERT_USB"
  | "UNLOCK_DEVICE"
  | "EXPORTING"
  | "SUCCESS"
  | "PARTIAL_SUCCESS"
  | "ERROR";

type ExportAction =
  | { type: "RETRY_PREFLIGHT" }
  | { type: "PREFLIGHT_COMPLETE"; deviceStatus: DeviceStatus }
  | { type: "PREPARE_USB" }
  | { type: "UNLOCK_DEVICE"; payload: string }
  | { type: "SET_PASSPHRASE"; payload: string }
  | { type: "GO_BACK" }
  | { type: "START_EXPORT" }
  | { type: "EXPORT_COMPLETE"; deviceStatus: DeviceStatus }
  | { type: "EXPORT_ERROR"; payload: string; deviceStatus?: DeviceStatus }
  | { type: "CANCEL" };

interface ExportContext {
  state: ExportState;
  filename: string;
  passphrase: string;
  deviceLocked: boolean;
  errorMessage: string;
  deviceStatus?: DeviceStatus;
  unlockError: boolean;
}

const initialContext: ExportContext = {
  state: "PREFLIGHT",
  filename: "",
  passphrase: "",
  deviceLocked: true,
  errorMessage: "",
  deviceStatus: undefined,
  unlockError: false,
};

// Unrecoverable errors that should show error page
const UNRECOVERABLE_ERRORS: DeviceStatus[] = [
  ExportStatus.ERROR_MOUNT,
  ExportStatus.ERROR_EXPORT,
  ExportStatus.DEVICE_ERROR,
  DeviceErrorStatus.ERROR_MISSING_FILES,
  DeviceErrorStatus.CALLED_PROCESS_ERROR,
  DeviceErrorStatus.UNEXPECTED_RETURN_STATUS,
];

function getStateFromStatus(
  context: ExportContext,
  status: DeviceStatus | undefined,
): ExportContext {
  if (!status) {
    return {
      ...context,
      state: "ERROR",
      errorMessage: "Error getting device status",
    };
  }

  // On device detection error, show INSERT_USB page with instructions
  if (
    status === ExportStatus.NO_DEVICE_DETECTED ||
    status === ExportStatus.MULTI_DEVICE_DETECTED ||
    status === ExportStatus.INVALID_DEVICE_DETECTED ||
    status === ExportStatus.UNKNOWN_DEVICE_DETECTED
  ) {
    return {
      ...context,
      deviceStatus: status,
      state: "INSERT_USB",
    };
  }

  // Device is available: proceed to unlock or begin export
  if (status === ExportStatus.DEVICE_LOCKED) {
    return {
      ...context,
      deviceLocked: true,
      deviceStatus: status,
      state: "UNLOCK_DEVICE",
    };
  }
  if (status === ExportStatus.DEVICE_WRITABLE) {
    return {
      ...context,
      deviceLocked: false,
      deviceStatus: status,
      state: "EXPORTING",
    };
  }

  if (UNRECOVERABLE_ERRORS.includes(status)) {
    return {
      ...context,
      state: "ERROR",
      deviceStatus: status,
      errorMessage: `Error completing export preflight: ${status.toString()}`,
    };
  }
  // Any other DeviceStatus value is unexpected in this context;
  // treat it as an error to avoid silently ignoring new or unsupported statuses.
  return {
    ...context,
    state: "ERROR",
    deviceStatus: status,
    errorMessage: `Unexpected device status: ${status.toString()}`,
  };
}

function exportReducer(
  context: ExportContext,
  action: ExportAction,
): ExportContext {
  if (action.type === "EXPORT_ERROR") {
    return {
      ...context,
      state: "ERROR",
      errorMessage: action.payload,
      deviceStatus: action.deviceStatus,
      passphrase: "",
    };
  }
  if (action.type === "CANCEL") {
    return initialContext;
  }
  switch (context.state) {
    case "PREFLIGHT":
      switch (action.type) {
        case "PREFLIGHT_COMPLETE":
          return {
            ...context,
            deviceStatus: action.deviceStatus,
            state: "PREFLIGHT_COMPLETE",
          };
        default:
          return context;
      }
    case "PREFLIGHT_COMPLETE":
      switch (action.type) {
        case "PREPARE_USB":
          return getStateFromStatus(context, context.deviceStatus);
        default:
          return context;
      }

    case "PREFLIGHT_INSERT_USB":
    case "INSERT_USB":
      switch (action.type) {
        case "RETRY_PREFLIGHT":
          return {
            ...context,
            state: "PREFLIGHT_INSERT_USB",
          };
        case "PREFLIGHT_COMPLETE":
          return getStateFromStatus(context, action.deviceStatus);
        default:
          return context;
      }

    case "UNLOCK_DEVICE":
      switch (action.type) {
        case "SET_PASSPHRASE":
          return { ...context, passphrase: action.payload, unlockError: false };
        case "UNLOCK_DEVICE": {
          const passphrase = context.passphrase;
          if (
            typeof passphrase !== "string" ||
            passphrase.trim().length === 0
          ) {
            return { ...context, unlockError: true };
          }
          return { ...context, state: "EXPORTING", unlockError: false };
        }
        case "GO_BACK":
          return {
            ...context,
            state: "PREFLIGHT_COMPLETE",
            passphrase: "",
            unlockError: false,
          };
        default:
          return context;
      }

    case "EXPORTING":
      switch (action.type) {
        case "EXPORT_COMPLETE": {
          const exportStatus = action.deviceStatus;

          if (exportStatus === ExportStatus.SUCCESS_EXPORT) {
            return {
              ...context,
              state: "SUCCESS",
              deviceStatus: exportStatus,
              passphrase: "",
            };
          }

          // Partial success - export succeeded but cleanup issues
          if (
            exportStatus === ExportStatus.ERROR_EXPORT_CLEANUP ||
            exportStatus === ExportStatus.ERROR_UNMOUNT_VOLUME_BUSY
          ) {
            return {
              ...context,
              state: "PARTIAL_SUCCESS",
              deviceStatus: exportStatus,
              passphrase: "",
            };
          }

          // Retry unlock errors
          if (
            exportStatus === ExportStatus.ERROR_UNLOCK_LUKS ||
            exportStatus === ExportStatus.ERROR_UNLOCK_GENERIC
          ) {
            return {
              ...context,
              state: "UNLOCK_DEVICE",
              unlockError: true,
              passphrase: "",
              deviceStatus: exportStatus,
            };
          }

          // Unrecoverable errors
          if (UNRECOVERABLE_ERRORS.includes(exportStatus)) {
            return {
              ...context,
              state: "ERROR",
              deviceStatus: exportStatus,
              errorMessage: `Export failed: ${exportStatus.toString()}`,
              passphrase: "",
            };
          }

          // Other errors
          return {
            ...context,
            state: "ERROR",
            deviceStatus: exportStatus,
            errorMessage: `Export failed with status: ${exportStatus.toString()}`,
            passphrase: "",
          };
        }
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

const InsertUSBState = memo(function InsertUSBState({
  context,
  t,
}: StateComponentProps) {
  const getStatusMessage = () => {
    switch (context.deviceStatus) {
      case ExportStatus.NO_DEVICE_DETECTED:
        return t("exportWizard.noDeviceDetected");
      case ExportStatus.MULTI_DEVICE_DETECTED:
        return t("exportWizard.multiDeviceDetected");
      case ExportStatus.INVALID_DEVICE_DETECTED:
        return t("exportWizard.invalidDeviceDetected");
      case ExportStatus.UNKNOWN_DEVICE_DETECTED:
        return t("exportWizard.unknownDeviceDetected");
      default:
        return "";
    }
  };

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
        <p>{t("exportWizard.insertUSBInstructions")}</p>
        {context.deviceStatus && (
          <p className="text-red-800">{getStatusMessage()}</p>
        )}
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

  const getUnlockErrorMessage = () => {
    if (context.deviceStatus === ExportStatus.ERROR_UNLOCK_LUKS) {
      return t("exportWizard.errorUnlockLuks");
    }
    if (context.deviceStatus === ExportStatus.ERROR_UNLOCK_GENERIC) {
      return t("exportWizard.errorUnlockGeneric");
    }
    return "";
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
        {context.unlockError && (
          <p className="text-red-800">{getUnlockErrorMessage()}</p>
        )}
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

const PartialSuccessState = memo(function PartialSuccessState({
  context,
  t,
}: StateComponentProps) {
  const getWarningMessage = () => {
    if (context.deviceStatus === ExportStatus.ERROR_EXPORT_CLEANUP) {
      return t("exportWizard.errorExportCleanup");
    }
    if (context.deviceStatus === ExportStatus.ERROR_UNMOUNT_VOLUME_BUSY) {
      return t("exportWizard.errorUnmountVolumeBusy");
    }
    return "";
  };

  return (
    <div>
      <div className="flex items-center gap-3 mb-4">
        <Inbox size={24} className="text-blue-500" />
        <div className="ml-3">
          <h3 className="text-lg font-semibold">
            {t("exportWizard.exportSuccessWithWarning")}
          </h3>
        </div>
      </div>
      <hr className="my-4 border-gray-300" />
      <div className="space-y-4">
        <div>
          <p className="text-yellow-800">{getWarningMessage()}</p>
        </div>
        <p className="text-gray-600">{t("exportWizard.beCareful")}</p>
      </div>
    </div>
  );
});

const ErrorState = memo(function ErrorState({
  context,
  t,
}: StateComponentProps) {
  const getErrorMessage = () => {
    // If we have a device status, try to get a user-friendly message
    if (context.deviceStatus) {
      switch (context.deviceStatus) {
        case ExportStatus.ERROR_MOUNT:
          return t("exportWizard.errorMount");
        case ExportStatus.ERROR_EXPORT:
          return t("exportWizard.errorExport");
        case DeviceErrorStatus.ERROR_MISSING_FILES:
          return t("exportWizard.errorMissingFiles");
        case ExportStatus.DEVICE_ERROR:
          return t("exportWizard.deviceError");
        case DeviceErrorStatus.CALLED_PROCESS_ERROR:
        case DeviceErrorStatus.UNEXPECTED_RETURN_STATUS:
          return t("exportWizard.unexpectedError");
        default:
          return context.errorMessage || t("exportWizard.unknownError");
      }
    }
    return context.errorMessage || t("exportWizard.unknownError");
  };

  return (
    <div>
      <div className="flex items-center gap-3 mb-4">
        <FileX2 size={24} strokeWidth={2} className="text-red-500" />
        <div className="ml-3">
          <h3 className="text-lg font-semibold">
            {t("exportWizard.exportFailed")}
          </h3>
        </div>
      </div>
      <hr className="my-4 border-gray-300" />
      <div className="space-y-4">
        <p className="text-gray-600">{getErrorMessage()}</p>
      </div>
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
  const filename = item.filename
    ? item.filename.substring(item.filename.lastIndexOf("/") + 1)
    : "";
  const [context, dispatch] = useReducer(exportReducer, {
    ...initialContext,
    filename: filename,
  });

  // Refs to track in-progress operations
  const preflightInProgress = useRef(false);
  const exportInProgress = useRef(false);

  // Reset state when wizard is closed
  useEffect(() => {
    if (!open) {
      dispatch({ type: "CANCEL" });
      // Reset operation flags when closing
      preflightInProgress.current = false;
      exportInProgress.current = false;
    }
  }, [open]);

  // Initiate export preflight checks
  useEffect(() => {
    // Only run if we're in a preflight state, modal is open, and not already in progress
    if (
      !(
        context.state === "PREFLIGHT" ||
        context.state === "PREFLIGHT_INSERT_USB"
      ) ||
      !open ||
      preflightInProgress.current
    ) {
      return;
    }

    preflightInProgress.current = true;
    let isCancelled = false;

    const initiateExport = async () => {
      try {
        const deviceStatus = await window.electronAPI.initiateExport();
        // Only dispatch if operation hasn't been cancelled
        if (!isCancelled) {
          dispatch({ type: "PREFLIGHT_COMPLETE", deviceStatus: deviceStatus });
        }
      } catch (error) {
        if (!isCancelled) {
          console.error("Failed to initiate export during preflight:", error);
          const errorMessage = t("exportWizard.unknownError");
          dispatch({ type: "EXPORT_ERROR", payload: errorMessage });
        }
      } finally {
        preflightInProgress.current = false;
      }
    };

    initiateExport();

    // Cleanup function to mark operation as cancelled. This marks operation as
    // cancelled in the frontend, but does not cancel the async preflight operation
    // in the backend.
    return () => {
      isCancelled = true;
    };
  }, [open, context.state, t]);

  // Perform export
  useEffect(() => {
    // Only run if we're in EXPORTING state and not already in progress
    if (context.state !== "EXPORTING" || exportInProgress.current) {
      return;
    }

    exportInProgress.current = true;
    let isCancelled = false;

    const performExport = async () => {
      try {
        const deviceStatus = await window.electronAPI.export(
          [item.uuid],
          context.passphrase,
        );
        // Only dispatch if operation hasn't been cancelled
        if (!isCancelled) {
          dispatch({ type: "EXPORT_COMPLETE", deviceStatus: deviceStatus });
        }
      } catch {
        if (!isCancelled) {
          const errorMessage = t("exportWizard.unknownError");
          dispatch({ type: "EXPORT_ERROR", payload: errorMessage });
        }
      } finally {
        exportInProgress.current = false;
      }
    };

    performExport();

    // Cleanup function to mark operation as cancelled. This marks operation as
    // cancelled in the frontend, but does not cancel the async export operation
    // in the backend.
    return () => {
      isCancelled = true;
    };
  }, [context.state, item.uuid, context.passphrase, t]);

  const handleClose = () => {
    dispatch({ type: "CANCEL" });
    onClose();
  };

  const renderStateComponent = () => {
    const stateProps = { context, dispatch, filename, t };

    switch (context.state) {
      case "PREFLIGHT":
      case "PREFLIGHT_COMPLETE":
        return <PreflightState {...stateProps} />;
      case "PREFLIGHT_INSERT_USB":
      case "INSERT_USB":
        return <InsertUSBState {...stateProps} />;
      case "UNLOCK_DEVICE":
        return <UnlockDeviceState {...stateProps} />;
      case "EXPORTING":
        return <ExportingState {...stateProps} />;
      case "SUCCESS":
        return <SuccessState {...stateProps} />;
      case "PARTIAL_SUCCESS":
        return <PartialSuccessState {...stateProps} />;
      case "ERROR":
        return <ErrorState {...stateProps} />;
      default:
        return null;
    }
  };

  const renderFooter = () => {
    switch (context.state) {
      case "PREFLIGHT":
      case "PREFLIGHT_INSERT_USB":
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
              dispatch({ type: "PREPARE_USB" });
            }}
          >
            {t("exportWizard.continue")}
          </Button>,
          <Button key="cancel" onClick={handleClose}>
            {t("exportWizard.cancel")}
          </Button>,
        ];

      case "INSERT_USB":
        // Show cancel button - user needs to insert USB or cancel
        return [
          <Button
            key="continue"
            type="primary"
            onClick={() => {
              dispatch({ type: "RETRY_PREFLIGHT" });
            }}
          >
            {t("exportWizard.retry")}
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

      case "PARTIAL_SUCCESS":
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
      getContainer={() => document.getElementById("root") || document.body}
    >
      {renderStateComponent()}
    </Modal>
  );
});
