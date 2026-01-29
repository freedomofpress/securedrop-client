import { join } from "path";
import fs from "fs";
import { DB } from "./database";
import { Storage } from "./storage";
import { type SourceWithItems, Journalist } from "../types";

import { Liquid } from "liquidjs";

export async function renderTranscript(data: SourceWithItems, db: DB) {
  const engine = new Liquid({
    root: join(__dirname, "../../resources/templates"),
    extname: ".liquid",
  });

  engine.registerFilter("getJournalistName", function (uuid: string) {
    const db: DB = this.context.get(["db"]) as DB;
    try {
      const journalist: Journalist = db.getJournalistByID(uuid);
      return journalist.data.username || "Unknown journalist";
    } catch (error) {
      console.error("Error looking up journalist ", error);
      return "Unknown journalist";
    }
  });

  const renderContext = {
    d: data,
    db: db,
  };

  try {
    const output: string = await engine.renderFile(
      "transcript.txt.liquid",
      renderContext,
    );
    return output;
  } catch (error) {
    console.error("Error generating transcript: ", error);
    throw error;
  }
}

export async function writeTranscript(
  sourceUuid: string,
  db: DB,
): Promise<string> {
  const storage = new Storage();

  try {
    const sourceWithItems = db.getSourceWithItems(sourceUuid);
    const filePath: string = join(
      storage.sourceDirectory(sourceUuid).path,
      "transcript.txt",
    );

    const fileContent = await renderTranscript(sourceWithItems, db);
    fs.writeFileSync(filePath, fileContent, "utf-8");
    return filePath;
  } catch (error) {
    console.error(
      `Failed to write transcript for source: ${sourceUuid}:`,
      error,
    );
    throw error;
  }
}
