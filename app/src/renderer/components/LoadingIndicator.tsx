import { memo } from "react";

const LoadingIndicator = memo(function LoadingIndicator() {
  return <div className="flex items-center justify-center">Loading...</div>;
});

export default LoadingIndicator;
