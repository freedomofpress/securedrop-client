import { memo, useReducer, useEffect, useRef } from "react";
import { type Item, DeviceStatus, PrintStatus } from "../../../../../../types";
import "../Item.css";
import "./File.css";

import { useTranslation } from "react-i18next";
import { LoaderCircle, FileX2, Printer as PrinterIcon } from "lucide-react";
import { Button, Modal } from "antd";

type PrintState =
  | "PREFLIGHT"
  | "PREFLIGHT_COMPLETE"
  | "PRINTING"
  | "SUCCESS"
  | "ERROR";

type PrintAction =
  | { type: "PREFLIGHT_COMPLETE" }
  | { type: "START_PRINT" }
  | { type: "PRINT_COMPLETE"; deviceStatus: DeviceStatus }
  | { type: "PRINT_ERROR"; payload: string; deviceStatus?: DeviceStatus }
  | { type: "CANCEL" };

interface PrintContext {
  state: PrintState;
  filename: string;
  errorMessage: string;
  deviceStatus?: DeviceStatus;
}

const initialContext: PrintContext = {
  state: "PREFLIGHT",
  filename: "",
  errorMessage: "",
  deviceStatus: undefined,
};

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
        case "PREFLIGHT_COMPLETE":
          return {
            ...context,
            state: "PREFLIGHT_COMPLETE",
          };
        default:
          return context;
      }

    case "PREFLIGHT_COMPLETE":
      switch (action.type) {
        case "START_PRINT":
          return { ...context, state: "PRINTING" };
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
          <p className="text-gray-600">{context.filename}</p>
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

const SuccessState = memo(function SuccessState({ t }: StateComponentProps) {
  return (
    <div>
      <div className="flex items-center gap-3 mb-4">
        <PrinterIcon size={24} className="text-blue-500" />
        <div className="ml-3">
          <h3 className="text-lg font-semibold">
            {t("printWizard.printSuccess")}
          </h3>
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
  item: Item;
  open: boolean;
  onClose: () => void;
}

export const PrintWizard = memo(function PrintWizard({
  item,
  open,
  onClose,
}: PrintWizardProps) {
  const { t } = useTranslation("Item");
  const filename = item.filename
    ? item.filename.substring(item.filename.lastIndexOf("/") + 1)
    : "";
  const [context, dispatch] = useReducer(printReducer, {
    ...initialContext,
    filename: filename,
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

  // Initiate print preflight checks on modal open
  useEffect(() => {
    // Only run if we're in PREFLIGHT state, modal is open, and not already in progress
    if (context.state !== "PREFLIGHT" || !open || preflightInProgress.current) {
      return;
    }

    preflightInProgress.current = true;
    let isCancelled = false;

    const initiatePrint = async () => {
      try {
        const deviceStatus = await window.electronAPI.initiatePrint();
        // Only dispatch if operation hasn't been cancelled
        if (!isCancelled) {
          if (deviceStatus === PrintStatus.PRINT_PREFLIGHT_SUCCESS) {
            dispatch({ type: "PREFLIGHT_COMPLETE" });
          } else {
            dispatch({
              type: "PRINT_ERROR",
              payload: `Print preflight failed: ${deviceStatus.toString()}`,
              deviceStatus: deviceStatus,
            });
          }
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
        const deviceStatus = await window.electronAPI.print([item.uuid]);
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
  }, [context.state, item.uuid, t]);

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
        return <PreflightState {...stateProps} />;
      case "PREFLIGHT_COMPLETE":
        return <PreflightState {...stateProps} />;
      case "PRINTING":
        return <PrintingState {...stateProps} />;
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

      case "PRINTING":
        // No buttons during print
        return null;

      case "SUCCESS":
        return [
          <Button key="close" onClick={handleClose}>
            {t("wizard.done")}
          </Button>,
        ];

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
    context.state === "PRINTING" || context.state === "PREFLIGHT";

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
