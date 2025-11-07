import * as fs from "fs";
import os from "os";
import { ItemMetadata } from "../types";
import { ItemFetchTask } from "./fetch/queue";

/// Newtype for when we know a path component is potentially unsafe,
/// which prevents it from being used in anything except PathBuilder
export class UnsafePathComponent {
  path: string;

  constructor(path: string) {
    this.path = path;
  }
}

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

  validate(part: string | UnsafePathComponent): string {
    if (part instanceof UnsafePathComponent) {
      part = part.path;
    }
    // Stop any path traversal attempts
    if (part.includes("/") || part === ".." || part === "." || part === "") {
      throw new Error(`Invalid path component: ${part}`);
    }
    return part;
  }

  doesntEscape(path: string) {
    // Don't allow escape via symlinks
    if (fs.existsSync(path)) {
      const absolute = fs.realpathSync(path);
      if (!absolute.startsWith(this.path)) {
        throw new Error(`Path ${path} escapes root ${this.path}`);
      }
    }
  }

  getSubBuilder(...args: string[]): PathBuilder {
    let ret = this.path;
    for (const arg of args) {
      this.validate(arg);
      ret += `${arg}/`;
    }
    this.doesntEscape(ret);
    return new PathBuilder(ret);
  }

  join(...args: (string | UnsafePathComponent)[]): string {
    let ret = this.path;
    for (let i = 0; i < args.length; i++) {
      const validated = this.validate(args[i]);
      ret += validated;
      // Add separator between args (but not after the last one)
      if (i < args.length - 1) {
        ret += "/";
      }
    }
    this.doesntEscape(ret);
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
    // on macOS the tmpdir() is a symlink, so we need to resolve it first
    this.tmp = new PathBuilder(fs.realpathSync(os.tmpdir()) + "/");
  }

  /** We use a predictable path here so we can pick up if it crashes midway */
  downloadFilePath(metadata: ItemMetadata, item: ItemFetchTask): string {
    const dirPath = this.tmp.join("download", metadata.source, item.id);
    fs.mkdirSync(dirPath, { recursive: true });
    return this.tmp.join("download", metadata.source, item.id, "encrypted.gpg");
  }

  sourceDirectory(sourceID: string): PathBuilder {
    const dir = this.persistent.getSubBuilder(sourceID);
    fs.mkdirSync(dir.path, { recursive: true });
    return dir;
  }

  itemDirectory(item: ItemMetadata): PathBuilder {
    const dir = this.sourceDirectory(item.source).getSubBuilder(item.uuid);
    fs.mkdirSync(dir.path, { recursive: true });
    return dir;
  }

  createTempDir(prefix: string): PathBuilder {
    // This is a bit hacky because we are only validating the prefix,
    // and not the real name, but I think we can trust mkdtemp to generate
    // a unique name that doesn't introduce a path traversal.
    const tempDir = fs.mkdtempSync(this.tmp.join(prefix));
    return new PathBuilder(tempDir + "/");
  }
}
