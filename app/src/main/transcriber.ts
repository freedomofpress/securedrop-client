import { join } from "path";
import fs from "fs";
import { DB } from "./database";
import { Storage } from "./storage";
import { type SourceWithItems } from "../types";

import { Liquid } from "liquidjs";
import transcriptTemplateContent from "../../resources/templates/transcript.txt.liquid?raw";

export async function renderTranscript(data: SourceWithItems, db: DB) {
  const transcriptTemplateName = "transcript.txt.liquid";

  const engine = new Liquid({
    // Supplying templates as an in-memory map causes LiquidJS to replace its
    // default fs implementation with MapFS, which only performs map lookups.
    // The real filesystem is never accessible to the engine.
    templates: { [transcriptTemplateName]: transcriptTemplateContent },
    // Restrict property access to own properties only, preventing templates
    // from traversing the prototype chain on context objects.
    ownPropertyOnly: true,
    // Disable dynamic partials ({% include someVariable %}) — our template
    // does not use them, so there's no reason to leave that surface open.
    dynamicPartials: false,
    // Throw on unknown filters rather than silently skipping them.
    strictFilters: true,
    // Throw on undefined variables rather than silently rendering empty string.
    strictVariables: true,
    // Relax strictVariables inside if/unless/default so that a missing
    // variable evaluates to false/null instead of throwing. This is needed
    // for the template's {% if not item.plaintext %} guards and
    // | default: "..." fallbacks.
    lenientIf: true,
  });

  const journalists: Record<string, string> = {};
  for (const journalist of db.getJournalists()) {
    journalists[journalist.uuid] = journalist.data.username;
  }

  const renderContext = {
    d: data,
    journalists,
  };

  try {
    const output: string = await engine.renderFile(
      transcriptTemplateName,
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
