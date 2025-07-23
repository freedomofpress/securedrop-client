import { useState, useEffect } from "react";

import type { Source } from "../../../types";

function Sources() {
  const [sources, setSources] = useState<Source[]>([]);

  useEffect(() => {
    const fetchSources = async () => {
      const sources = await window.electronAPI.getSources();
      setSources(sources);
    };
    fetchSources();
  }, []);

  return (
    <div className="sd-bg-primary flex-1 overflow-y-auto">
      {sources.map((source) => (
        <div key={source.uuid}>{source.data.journalist_designation}</div>
      ))}
    </div>
  );
}

export default Sources;
