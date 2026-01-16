import { join } from "path";
import { DB } from "./database";

import { type SourceWithItems } from "../types";

import { Liquid } from "liquidjs";

// TODO: add filters to get filename "properly" and get journalist account name
// from uuid in ReplyMetadata

const journalistNameFilter = (uuid: string, db: DB): string => {
  return db.getJournalistByID(uuid).data.username;
};

export class Transcriber {
  db: DB;
  private engine: Liquid;

  constructor(
    db: DB,
    templateRoot: string = join(__dirname, "../../resources/templates/"),
  ) {
    this.db = db;
    this.engine = new Liquid({
      root: templateRoot,
      extname: ".liquid",
    });
    this.engine.registerFilter("journalist_name", journalistNameFilter);
  }

  public async generateTranscript(data: SourceWithItems): Promise<string> {
    try {
      const output: string = await this.engine.renderFile(
        "transcript.txt.liquid",
        data,
      );
      return output;
    } catch (error) {
      console.error("Error generating transcript: ", error);
      throw error;
    }
  }
}
