import * as fs from "fs";
import os from "os";
import { ItemMetadata } from "../types";
import { ItemFetchTask } from "./fetch/queue";
/**
 * Class that helps build filesystem paths in a
 * path-traversal safe way
 */
export class PathBuilder {
  path: string;

  constructor(path: string) {
    if (!path.startsWith("/")) {
      throw new Error("Root path must be absolute and start with /");
    }
    if (!path.endsWith("/")) {
      throw new Error("Root path must be a directory and end with /");
    }
    this.path = path;
  }

  validate(part: string) {
    // Stop any path traversal attempts
    if (part.includes("/") || part === ".." || part === "." || part === "") {
      throw new Error(`Invalid path component: ${part}`);
    }
  }

  getSubBuilder(...args: string[]): PathBuilder {
    let ret = this.path;
    for (const arg of args) {
      this.validate(arg);
      ret += `${arg}/`;
    }
    return new PathBuilder(ret);
  }

  join(...args: string[]): string {
    let ret = this.path;
    for (let i = 0; i < args.length; i++) {
      this.validate(args[i]);
      ret += args[i];
      // Add separator between args (but not after the last one)
      if (i < args.length - 1) {
        ret += "/";
      }
    }
    // Don't allow escape via symlinks
    if (fs.existsSync(ret)) {
      const absolute = fs.realpathSync(ret);
      if (!absolute.startsWith(this.path)) {
        throw new Error(`Path ${ret} escapes root ${this.path}`);
      }
    }
    return ret;
  }
}

export class Storage {
  private persistent: PathBuilder;
  private tmp: PathBuilder;

  constructor() {
    this.persistent = new PathBuilder(os.homedir() + "/").getSubBuilder(
      ".config",
      "SecureDrop",
      "files",
    );
    this.tmp = new PathBuilder(os.tmpdir() + "/");
  }

  /** We use a predictable path here so we can pick up if it crashes midway */
  downloadFilePath(metadata: ItemMetadata, item: ItemFetchTask): string {
    return this.tmp.join("download", metadata.source, item.id, "encrypted.gpg");
  }

  sourceDirectory(sourceID: string): PathBuilder {
    return this.persistent.getSubBuilder(sourceID);
  }

  itemDirectory(item: ItemMetadata): PathBuilder {
    return this.sourceDirectory(item.source).getSubBuilder(item.uuid);
  }

  createTempDir(prefix: string): PathBuilder {
    const tempDir = fs.mkdtempSync(this.tmp.join(prefix));
    return new PathBuilder(tempDir + "/");
  }
}
