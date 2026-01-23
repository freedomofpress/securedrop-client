import { join } from "path";
import { DB } from "./database";
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
