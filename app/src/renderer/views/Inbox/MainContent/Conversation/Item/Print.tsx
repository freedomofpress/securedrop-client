import { memo, useReducer, useEffect, useRef } from "react";
import {
  type DeviceStatus,
  PrintStatus,
  PrintPayload,
} from "../../../../../../types";
import "../Item.css";
import "./File.css";

import { useTranslation } from "react-i18next";
import { LoaderCircle, FileX2, Printer as PrinterIcon } from "lucide-react";
import { Button, Modal } from "antd";

type PrintState =
  | "PREFLIGHT"
  | "PREFLIGHT_COMPLETE"
  | "PREFLIGHT_CONNECT_PRINTER"
  | "CONNECT_PRINTER"
  | "PRINTING"
  | "SUCCESS"
  | "ERROR";

type PrintAction =
  | { type: "PREFLIGHT_COMPLETE"; deviceStatus: DeviceStatus }
  | { type: "RETRY_PREFLIGHT" }
  | { type: "CONNECT_PRINTER" }
  | { type: "START_PRINT" }
  | { type: "PRINT_COMPLETE"; deviceStatus: DeviceStatus }
  | { type: "PRINT_ERROR"; payload: string; deviceStatus?: DeviceStatus }
  | { type: "CANCEL" };

interface PrintContext {
  state: PrintState;
  errorMessage: string;
  deviceStatus?: DeviceStatus;
}

const initialContext: PrintContext = {
  state: "PREFLIGHT",
  errorMessage: "",
  deviceStatus: undefined,
};

function getStateFromPreflightComplete(
  context: PrintContext,
  printStatus: DeviceStatus | undefined,
): PrintContext {
  if (!printStatus) {
    return {
      ...context,
      state: "ERROR",
      errorMessage: "Error getting printer status",
    };
  }

  // If still no printer, stay in CONNECT_PRINTER state
  if (printStatus === PrintStatus.ERROR_PRINTER_NOT_FOUND) {
    return {
      ...context,
      state: "CONNECT_PRINTER",
      deviceStatus: printStatus,
    };
  }

  // If preflight successful and printer was found, proceed to print
  if (printStatus === PrintStatus.PRINT_PREFLIGHT_SUCCESS) {
    return {
      ...context,
      deviceStatus: printStatus,
      state: "PRINTING",
    };
  }

  // Any other status is an error
  return {
    ...context,
    state: "ERROR",
    deviceStatus: printStatus,
    errorMessage: `Print preflight failed with status: ${printStatus.toString()}`,
  };
}

function printReducer(
  context: PrintContext,
  action: PrintAction,
): PrintContext {
  if (action.type === "PRINT_ERROR") {
    return {
      ...context,
      state: "ERROR",
      errorMessage: action.payload,
      deviceStatus: action.deviceStatus,
    };
  }
  if (action.type === "CANCEL") {
    return initialContext;
  }
  switch (context.state) {
    case "PREFLIGHT":
      switch (action.type) {
        case "PREFLIGHT_COMPLETE": {
          return {
            ...context,
            deviceStatus: action.deviceStatus,
            state: "PREFLIGHT_COMPLETE",
          };
        }
        default:
          return context;
      }

    case "PREFLIGHT_COMPLETE":
      switch (action.type) {
        case "START_PRINT":
          return getStateFromPreflightComplete(context, context.deviceStatus);
        default:
          return context;
      }

    case "CONNECT_PRINTER":
      switch (action.type) {
        case "RETRY_PREFLIGHT":
          return {
            ...context,
            state: "PREFLIGHT_CONNECT_PRINTER",
          };
        default:
          return context;
      }

    case "PREFLIGHT_CONNECT_PRINTER":
      switch (action.type) {
        case "PREFLIGHT_COMPLETE":
          return getStateFromPreflightComplete(context, action.deviceStatus);
        default:
          return context;
      }

    case "PRINTING":
      switch (action.type) {
        case "PRINT_COMPLETE": {
          const printStatus = action.deviceStatus;

          if (printStatus === PrintStatus.PRINT_SUCCESS) {
            return { ...context, state: "SUCCESS", deviceStatus: printStatus };
          }

          // Otherwise we have an error state
          return {
            ...context,
            state: "ERROR",
            deviceStatus: printStatus,
            errorMessage: `Print failed with status: ${printStatus.toString()}`,
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
  context: PrintContext;
  dispatch: React.Dispatch<PrintAction>;
  filename: string;
  t: (key: string) => string;
}

const PreflightState = memo(function PreflightState({
  context,
  t,
  filename,
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
          <PrinterIcon size={24} className="text-blue-500" />
        )}
        <div className="ml-3">
          <h3 className="text-lg font-semibold">
            {t("printWizard.preparingPrint")}
          </h3>
          <p className="text-gray-600">{filename}</p>
        </div>
      </div>
      <hr className="my-4 border-gray-300" />
      <div className="space-y-4">
        <h3 className="text-md font-semibold">
          {t("printWizard.understandRisks")}
        </h3>
        <div>
          <p className="font-semibold">{t("wizard.malwareTitle")}</p>
          <p className="text-gray-600">{t("wizard.malwareWarning")}</p>
        </div>
        <div>
          <p className="font-semibold">{t("wizard.anonymityTitle")}</p>
          <p className="text-gray-600">{t("wizard.anonymityWarning")}</p>
        </div>
      </div>
    </div>
  );
});

const ConnectPrinterState = memo(function ConnectPrinterState({
  context,
  t,
  filename,
}: StateComponentProps) {
  return (
    <div>
      <div className="flex items-center gap-3 mb-4">
        {context.state === "PREFLIGHT_CONNECT_PRINTER" ? (
          <LoaderCircle
            className={"animate-spin text-blue-500"}
            size={24}
            strokeWidth={1}
          />
        ) : (
          <PrinterIcon size={24} className="text-blue-500" />
        )}
        <div className="ml-3">
          <h3 className="text-lg font-semibold">
            {t("printWizard.readyPrint")}
          </h3>
          <p className="text-gray-600">{filename}</p>
        </div>
      </div>
      <hr className="my-4 border-gray-300" />
      <div className="space-y-4">
        <p>{t("printWizard.connectPrinterInstructions")}</p>
        {context.deviceStatus === PrintStatus.ERROR_PRINTER_NOT_FOUND && (
          <p className="text-red-800">
            {t("printWizard.errorPrinterNotFound")}
          </p>
        )}
      </div>
    </div>
  );
});

const PrintingState = memo(function PrintingState({ t }: StateComponentProps) {
  return (
    <div>
      <div className="flex items-center gap-3 mb-4">
        <PrinterIcon size={24} className="text-blue-500" />
        <div className="ml-3">
          <h3 className="text-lg font-semibold">{t("wizard.pleaseWait")}</h3>
        </div>
      </div>
      <hr className="my-4 border-gray-300" />
      <div className="space-y-4">
        <h3 className="text-md font-semibold">{t("wizard.beCareful")}</h3>
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
        case PrintStatus.ERROR_PRINTER_NOT_FOUND:
          return t("printWizard.errorPrinterNotFound");
        case PrintStatus.ERROR_PRINT:
          return t("printWizard.errorPrint");
        case PrintStatus.ERROR_UNPRINTABLE_TYPE:
          return t("printWizard.errorUnprintableType");
        case PrintStatus.ERROR_MIMETYPE_UNSUPPORTED:
          return t("printWizard.errorMimetypeUnsupported");
        case PrintStatus.ERROR_MIMETYPE_DISCOVERY:
          return t("printWizard.errorMimetypeDiscovery");
        case PrintStatus.ERROR_UNKNOWN:
          return t("printWizard.errorUnknown");
        default:
          return context.errorMessage || t("wizard.unknownError");
      }
    }
    return context.errorMessage || t("wizard.unknownError");
  };

  return (
    <div>
      <div className="flex items-center gap-3 mb-4">
        <FileX2 size={24} strokeWidth={2} className="text-red-500" />
        <div className="ml-3">
          <h3 className="text-lg font-semibold">
            {t("printWizard.printFailed")}
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

interface PrintWizardProps {
  item: PrintPayload;
  open: boolean;
  onClose: () => void;
}

export const PrintWizard = memo(function PrintWizard({
  item,
  open,
  onClose,
}: PrintWizardProps) {
  const { t } = useTranslation("Item");

  let filename: string;
  switch (item.type) {
    case "file":
      filename = item.payload.filename
        ? item.payload.filename.substring(
            item.payload.filename.lastIndexOf("/") + 1,
          )
        : "";
      break;
    case "transcript":
      filename = "source transcript";
      break;
    default:
      filename = "";
      console.error("Unsupported print type: ", item);
      break;
  }
  const [context, dispatch] = useReducer(printReducer, {
    ...initialContext,
  });

  // Refs to track in-progress operations
  const preflightInProgress = useRef(false);
  const printInProgress = useRef(false);

  // Reset state when wizard is closed
  useEffect(() => {
    if (!open) {
      dispatch({ type: "CANCEL" });
      // Reset operation flags when closing
      preflightInProgress.current = false;
      printInProgress.current = false;
    }
  }, [open]);

  // Initiate print preflight checks on modal open or retry
  useEffect(() => {
    // Only run if we're in PREFLIGHT or PREFLIGHT_CONNECT_PRINTER state, modal is open, and not already in progress
    if (
      !(
        context.state === "PREFLIGHT" ||
        context.state === "PREFLIGHT_CONNECT_PRINTER"
      ) ||
      !open ||
      preflightInProgress.current
    ) {
      return;
    }

    preflightInProgress.current = true;
    let isCancelled = false;

    const initiatePrint = async () => {
      try {
        const deviceStatus = await window.electronAPI.initiatePrint();
        // Only dispatch if operation hasn't been cancelled
        if (!isCancelled) {
          dispatch({ type: "PREFLIGHT_COMPLETE", deviceStatus: deviceStatus });
        }
      } catch (error) {
        if (!isCancelled) {
          console.error("Failed to initiate print: ", error);
          const errorMessage =
            error instanceof Error ? error.message : t("wizard.unknownError");
          dispatch({ type: "PRINT_ERROR", payload: errorMessage });
        }
      } finally {
        preflightInProgress.current = false;
      }
    };

    initiatePrint();

    // Cleanup function to mark operation as cancelled. This marks operation as
    // cancelled in the frontend, but does not cancel the async preflight operation
    // in the backend.
    return () => {
      isCancelled = true;
    };
  }, [open, context.state, t]);

  // Perform print
  useEffect(() => {
    // Only run if we're in PRINTING state and not already in progress
    if (context.state !== "PRINTING" || printInProgress.current) {
      return;
    }

    printInProgress.current = true;
    let isCancelled = false;

    const performPrint = async () => {
      try {
        let deviceStatus: DeviceStatus;
        switch (item.type) {
          case "file":
            deviceStatus = await window.electronAPI.print(item.payload.uuid);
            break;
          case "transcript":
            deviceStatus = await window.electronAPI.printTranscript(
              item.payload.source_uuid,
            );
            break;
        }

        // Only dispatch if operation hasn't been cancelled
        if (!isCancelled) {
          dispatch({ type: "PRINT_COMPLETE", deviceStatus: deviceStatus });
        }
      } catch (error) {
        if (!isCancelled) {
          console.error("Failed to print file:", error);
          const errorMessage =
            error instanceof Error ? error.message : t("wizard.unknownError");
          dispatch({ type: "PRINT_ERROR", payload: errorMessage });
        }
      } finally {
        printInProgress.current = false;
      }
    };

    performPrint();

    // Cleanup function to mark operation as cancelled. This marks operation as
    // cancelled in the frontend, but does not cancel the async print operation
    // in the backend.
    return () => {
      isCancelled = true;
    };
  }, [context.state, item, t]);

  // Auto-close on success
  useEffect(() => {
    if (context.state === "SUCCESS") {
      // Auto-close the modal on successful print
      onClose();
    }
  }, [context.state, onClose]);

  const handleClose = () => {
    // Cancel any ongoing print operation
    window.electronAPI.cancelPrint();
    dispatch({ type: "CANCEL" });
    onClose();
  };

  const renderStateComponent = () => {
    const stateProps = { context, dispatch, filename, t };

    switch (context.state) {
      case "PREFLIGHT":
      case "PREFLIGHT_COMPLETE":
        return <PreflightState {...stateProps} />;
      case "PREFLIGHT_CONNECT_PRINTER":
      case "CONNECT_PRINTER":
        return <ConnectPrinterState {...stateProps} />;
      case "PRINTING":
        return <PrintingState {...stateProps} />;
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
            {t("wizard.continue")}
          </Button>,
          <Button key="cancel" onClick={handleClose}>
            {t("wizard.cancel")}
          </Button>,
        ];

      case "PREFLIGHT_COMPLETE":
        return [
          <Button
            key="continue"
            type="primary"
            onClick={() => {
              dispatch({ type: "START_PRINT" });
            }}
          >
            {t("wizard.continue")}
          </Button>,
          <Button key="cancel" onClick={handleClose}>
            {t("wizard.cancel")}
          </Button>,
        ];

      case "PREFLIGHT_CONNECT_PRINTER":
        return [
          <Button key="continue" type="primary" disabled>
            {t("wizard.continue")}
          </Button>,
          <Button key="cancel" onClick={handleClose}>
            {t("wizard.cancel")}
          </Button>,
        ];

      case "CONNECT_PRINTER":
        return [
          <Button
            key="retry"
            type="primary"
            onClick={() => {
              dispatch({ type: "RETRY_PREFLIGHT" });
            }}
          >
            {t("wizard.retry")}
          </Button>,
          <Button key="cancel" onClick={handleClose}>
            {t("wizard.cancel")}
          </Button>,
        ];

      case "PRINTING":
        // No buttons during print
        return null;

      case "SUCCESS":
        // Auto-closes, no footer needed
        return null;

      case "ERROR":
        return [
          <Button key="close" onClick={handleClose}>
            {t("wizard.close")}
          </Button>,
        ];

      default:
        return null;
    }
  };

  const isNonClosableState =
    context.state === "PRINTING" ||
    context.state === "PREFLIGHT" ||
    context.state === "PREFLIGHT_CONNECT_PRINTER";

  return (
    <Modal
      open={open}
      onCancel={handleClose}
      footer={renderFooter()}
      width={600}
      closable={false}
      maskClosable={!isNonClosableState}
      getContainer={() => document.getElementById("root") || document.body}
    >
      {renderStateComponent()}
    </Modal>
  );
});
