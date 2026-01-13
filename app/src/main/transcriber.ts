import { join } from "path";

import { type SourceWithItems } from "../types";

import { Liquid } from "liquidjs";

// TODO: add filters to get filename "properly" and get journalist account name
// from uuid in ReplyMetadata

export class Transcriber {
  private engine: Liquid;

  constructor(
    templateRoot: string = join(__dirname, "../../resources/templates/"),
  ) {
    this.engine = new Liquid({
      root: templateRoot,
      extname: ".liquid",
    });
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
