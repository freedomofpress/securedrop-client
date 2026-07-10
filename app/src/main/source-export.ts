import fs from "fs";

import { FetchStatus } from "../types";
import { DB } from "./database";
import { writeTranscript } from "./transcriber";

export type PreparedSourceExport = {
  filepaths: [string, ...string[]];
  sourceName: string;
};

export async function prepareSourceExport(
  sourceUuid: string,
  db: DB,
): Promise<PreparedSourceExport> {
  const { filePath, sourceWithItems } = await writeTranscript(sourceUuid, db);
  const filepaths: [string, ...string[]] = [filePath];

  for (const item of sourceWithItems.items) {
    if (
      item.data.kind === "file" &&
      item.fetch_status === FetchStatus.Complete &&
      item.filename &&
      fs.existsSync(item.filename)
    ) {
      filepaths.push(item.filename);
    }
  }

  return {
    filepaths,
    sourceName: sourceWithItems.data.journalist_designation,
  };
}
