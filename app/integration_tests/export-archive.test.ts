import { describe, it, expect, beforeEach, afterEach } from "vitest";
import * as fs from "fs";
import * as path from "path";
import * as os from "os";
import * as tar from "tar";
import { ArchiveExporter } from "../src/main/export";
import { execSync } from "child_process";

// Test Export Archive creation with securedrop_export
describe("Export Archive Tests", () => {
  let tmpDir: string;
  let archiveDir: string;

  beforeEach(() => {
    tmpDir = fs.mkdtempSync(path.join(os.tmpdir(), "tarball-test-"));
    archiveDir = path.join(tmpDir, "archives");
    fs.mkdirSync(archiveDir, { recursive: true });
  });

  afterEach(() => {
    if (fs.existsSync(tmpDir)) {
      fs.rmSync(tmpDir, { recursive: true, force: true });
    }
  });

  describe("Metadata validation", () => {
    it("should create tarball with metadata.json at root", async () => {
      const exporter = new ArchiveExporter();
      const metadata = { device: "disk", foo: "bar" };

      const archivePath = await exporter.createArchive({
        archiveDir,
        archiveFilename: "test.sd-export",
        metadata,
      });

      const extractDir = path.join(tmpDir, "extract");
      fs.mkdirSync(extractDir);
      await tar.x({ file: archivePath, cwd: extractDir });

      // Verify metadata.json exists at root
      const metadataPath = path.join(extractDir, "metadata.json");
      expect(fs.existsSync(metadataPath)).toBe(true);

      // Verify metadata content
      const content = JSON.parse(fs.readFileSync(metadataPath, "utf8"));
      expect(content).toEqual(metadata);
    });

    it("should include encryption_key in metadata when provided", async () => {
      const exporter = new ArchiveExporter();
      const passphrase = "test-passphrase-123";
      const metadata = {
        device: "disk",
        encryption_key: passphrase,
      };

      const archivePath = await exporter.createArchive({
        archiveDir,
        archiveFilename: "encrypted.sd-export",
        metadata,
      });

      const extractDir = path.join(tmpDir, "extract");
      fs.mkdirSync(extractDir);
      await tar.x({ file: archivePath, cwd: extractDir });

      const content = JSON.parse(
        fs.readFileSync(path.join(extractDir, "metadata.json"), "utf8"),
      );
      expect(content.encryption_key).toBe(passphrase);
    });
  });

  describe("File path structure", () => {
    it("should place single file under export_data/", async () => {
      const exporter = new ArchiveExporter();
      const testFile = path.join(archiveDir, "document.txt");
      fs.writeFileSync(testFile, "test content");

      const archivePath = await exporter.createArchive({
        archiveDir,
        archiveFilename: "single.sd-export",
        metadata: { device: "disk" },
        filepaths: [testFile],
      });

      const extractDir = path.join(tmpDir, "extract");
      fs.mkdirSync(extractDir);
      await tar.x({ file: archivePath, cwd: extractDir });

      // Single file should be at export_data/document.txt
      const extractedFile = path.join(
        extractDir,
        "export_data",
        "document.txt",
      );
      expect(fs.existsSync(extractedFile)).toBe(true);
      expect(fs.readFileSync(extractedFile, "utf8")).toBe("test content");
    });

    it("should organize multiple files with grandparent/parent structure", async () => {
      const exporter = new ArchiveExporter();

      // Create files with proper directory structure
      const sourceDir = path.join(tmpDir, "source");
      const grandparentDir = path.join(sourceDir, "journalist-1234");
      const parentDir = path.join(grandparentDir, "submission-5678");
      fs.mkdirSync(parentDir, { recursive: true });

      const file1 = path.join(parentDir, "document1.txt");
      const file2 = path.join(parentDir, "document2.txt");
      fs.writeFileSync(file1, "content1");
      fs.writeFileSync(file2, "content2");

      const archivePath = await exporter.createArchive({
        archiveDir,
        archiveFilename: "multiple.sd-export",
        metadata: { device: "disk" },
        filepaths: [file1, file2],
      });

      const extractDir = path.join(tmpDir, "extract");
      fs.mkdirSync(extractDir);
      await tar.x({ file: archivePath, cwd: extractDir });

      // Multiple files should include grandparent/parent in path
      const extracted1 = path.join(
        extractDir,
        "export_data",
        "journalist-1234",
        "submission-5678",
        "document1.txt",
      );
      const extracted2 = path.join(
        extractDir,
        "export_data",
        "journalist-1234",
        "submission-5678",
        "document2.txt",
      );

      expect(fs.existsSync(extracted1)).toBe(true);
      expect(fs.existsSync(extracted2)).toBe(true);
      expect(fs.readFileSync(extracted1, "utf8")).toBe("content1");
      expect(fs.readFileSync(extracted2, "utf8")).toBe("content2");
    });

    it("should handle transcript.txt special case", async () => {
      const exporter = new ArchiveExporter();

      // Create multiple files including transcript.txt
      const sourceDir = path.join(tmpDir, "source");
      const grandparentDir = path.join(sourceDir, "journalist-1234");
      const parentDir = path.join(grandparentDir, "submission-5678");
      fs.mkdirSync(parentDir, { recursive: true });

      const transcript = path.join(parentDir, "transcript.txt");
      const otherFile = path.join(parentDir, "document.txt");
      fs.writeFileSync(transcript, "transcript content");
      fs.writeFileSync(otherFile, "other content");

      const archivePath = await exporter.createArchive({
        archiveDir,
        archiveFilename: "transcript.sd-export",
        metadata: { device: "disk" },
        filepaths: [transcript, otherFile],
      });

      const extractDir = path.join(tmpDir, "extract");
      fs.mkdirSync(extractDir);
      await tar.x({ file: archivePath, cwd: extractDir });

      // transcript.txt should be at export_data/parent/transcript.txt (no grandparent)
      const extractedTranscript = path.join(
        extractDir,
        "export_data",
        "submission-5678",
        "transcript.txt",
      );
      expect(fs.existsSync(extractedTranscript)).toBe(true);
      expect(fs.readFileSync(extractedTranscript, "utf8")).toBe(
        "transcript content",
      );

      // Other file should have full path
      const extractedOther = path.join(
        extractDir,
        "export_data",
        "journalist-1234",
        "submission-5678",
        "document.txt",
      );
      expect(fs.existsSync(extractedOther)).toBe(true);
    });
  });

  describe("Path security validations (safe_extractall requirements)", () => {
    it("should only contain relative paths", async () => {
      const exporter = new ArchiveExporter();
      const testFile = path.join(archiveDir, "test.txt");
      fs.writeFileSync(testFile, "content");

      const archivePath = await exporter.createArchive({
        archiveDir,
        archiveFilename: "relative.sd-export",
        metadata: { device: "disk" },
        filepaths: [testFile],
      });

      // Read tarball and verify all paths are relative
      const members: tar.ReadEntry[] = [];
      await tar.t({
        file: archivePath,
        onentry: (entry) => {
          members.push(entry);
        },
      });

      for (const member of members) {
        // Paths should not be absolute
        expect(path.isAbsolute(member.path)).toBe(false);
        // Paths should not contain ".."
        expect(member.path).not.toMatch(/\.\./);
      }
    });

    it("should not contain path traversal sequences", async () => {
      const exporter = new ArchiveExporter();
      const testFile = path.join(archiveDir, "test.txt");
      fs.writeFileSync(testFile, "content");

      const archivePath = await exporter.createArchive({
        archiveDir,
        archiveFilename: "no-traversal.sd-export",
        metadata: { device: "disk" },
        filepaths: [testFile],
      });

      // Extract and verify no ".." in any paths
      const extractDir = path.join(tmpDir, "extract");
      fs.mkdirSync(extractDir);
      await tar.x({ file: archivePath, cwd: extractDir });

      // Walk the extracted directory
      const walkDir = (dir: string): string[] => {
        const files: string[] = [];
        const entries = fs.readdirSync(dir, { withFileTypes: true });
        for (const entry of entries) {
          const fullPath = path.join(dir, entry.name);
          const relativePath = path.relative(extractDir, fullPath);

          // Check for path traversal
          expect(relativePath).not.toMatch(/\.\./);
          expect(path.isAbsolute(relativePath)).toBe(false);

          files.push(relativePath);
          if (entry.isDirectory()) {
            files.push(...walkDir(fullPath));
          }
        }
        return files;
      };

      walkDir(extractDir);
    });

    it("should resolve to within extraction directory when extracted", async () => {
      const exporter = new ArchiveExporter();
      const testFile = path.join(archiveDir, "test.txt");
      fs.writeFileSync(testFile, "content");

      const archivePath = await exporter.createArchive({
        archiveDir,
        archiveFilename: "safe-paths.sd-export",
        metadata: { device: "disk" },
        filepaths: [testFile],
      });

      const extractDir = path.join(tmpDir, "extract");
      fs.mkdirSync(extractDir);
      await tar.x({ file: archivePath, cwd: extractDir });

      // Walk all extracted files and verify they resolve within extractDir
      const walkAndVerify = (dir: string) => {
        const entries = fs.readdirSync(dir, { withFileTypes: true });
        for (const entry of entries) {
          const fullPath = path.join(dir, entry.name);
          const resolved = fs.realpathSync(fullPath);

          // Resolved path must be within extractDir
          const relative = path.relative(extractDir, resolved);
          expect(relative).not.toMatch(/^\.\./);
          expect(path.isAbsolute(relative)).toBe(false);

          if (entry.isDirectory()) {
            walkAndVerify(fullPath);
          }
        }
      };

      walkAndVerify(extractDir);
    });
  });

  describe("File permissions", () => {
    it("should create tarball that extracts with proper permissions", async () => {
      const exporter = new ArchiveExporter();
      const testFile = path.join(archiveDir, "test.txt");
      fs.writeFileSync(testFile, "content");

      const archivePath = await exporter.createArchive({
        archiveDir,
        archiveFilename: "perms.sd-export",
        metadata: { device: "disk" },
        filepaths: [testFile],
      });

      const extractDir = path.join(tmpDir, "extract");
      fs.mkdirSync(extractDir);

      // Extract with tar module (which preserves permissions)
      await tar.x({ file: archivePath, cwd: extractDir });

      // Note: The tar npm module preserves permissions from the tarball.
      // The Python safe_extractall sets permissions during extraction (700 for dirs, 600 for files).
      // Here we verify the tarball structure is valid - the Python code will set final permissions.

      // Verify files can be read
      const extractedFile = path.join(extractDir, "export_data", "test.txt");
      expect(fs.existsSync(extractedFile)).toBe(true);
      expect(fs.readFileSync(extractedFile, "utf8")).toBe("content");
    });
  });

  describe("Python safe_extractall compatibility", () => {
    it("should successfully extract with Python safe_extractall", async () => {
      const exporter = new ArchiveExporter();
      const testFile = path.join(archiveDir, "document.txt");
      fs.writeFileSync(testFile, "test content");

      const archivePath = await exporter.createArchive({
        archiveDir,
        archiveFilename: "python-test.sd-export",
        metadata: { device: "disk", encryption_key: "test123" },
        filepaths: [testFile],
      });

      // Call Python safe_extractall
      const extractDir = path.join(tmpDir, "python-extract");
      fs.mkdirSync(extractDir);

      const pythonScript = `
import sys
sys.path.insert(0, '${path.join(process.cwd(), "..", "export")}')
from securedrop_export.directory import safe_extractall

safe_extractall('${archivePath}', '${extractDir}')
print('SUCCESS')
`;

      const scriptPath = path.join(tmpDir, "test_extract.py");
      fs.writeFileSync(scriptPath, pythonScript);

      try {
        const result = execSync(`python3 ${scriptPath}`, {
          encoding: "utf8",
          cwd: tmpDir,
        });
        expect(result.trim()).toBe("SUCCESS");

        // Verify extraction
        const extractedMeta = path.join(extractDir, "metadata.json");
        const extractedFile = path.join(
          extractDir,
          "export_data",
          "document.txt",
        );

        expect(fs.existsSync(extractedMeta)).toBe(true);
        expect(fs.existsSync(extractedFile)).toBe(true);

        // Verify permissions set by safe_extractall (700 for dirs, 600 for files)
        const metaStat = fs.statSync(extractedMeta);
        const fileStat = fs.statSync(extractedFile);
        const dirStat = fs.statSync(path.join(extractDir, "export_data"));

        // File should be 600 (readable/writable by owner only)
        expect(metaStat.mode & 0o777 & 0o077).toBe(0);
        expect(fileStat.mode & 0o777 & 0o077).toBe(0);

        // Directory should be 700 (rwx for owner only)
        expect(dirStat.mode & 0o777 & 0o077).toBe(0);
      } catch (error: any) {
        // If Python is not available or test fails, show the error
        console.error("Python test failed:", error.message);
        throw error;
      }
    });

    it("should extract multiple files with Python safe_extractall", async () => {
      const exporter = new ArchiveExporter();

      // Create multiple files
      const sourceDir = path.join(tmpDir, "source");
      const grandparentDir = path.join(sourceDir, "journalist-abc");
      const parentDir = path.join(grandparentDir, "submission-xyz");
      fs.mkdirSync(parentDir, { recursive: true });

      const file1 = path.join(parentDir, "doc1.txt");
      const file2 = path.join(parentDir, "doc2.txt");
      const transcript = path.join(parentDir, "transcript.txt");
      fs.writeFileSync(file1, "content1");
      fs.writeFileSync(file2, "content2");
      fs.writeFileSync(transcript, "conversation");

      const archivePath = await exporter.createArchive({
        archiveDir,
        archiveFilename: "multi-python.sd-export",
        metadata: { device: "disk" },
        filepaths: [file1, file2, transcript],
      });

      // Extract with Python
      const extractDir = path.join(tmpDir, "python-extract-multi");
      fs.mkdirSync(extractDir);

      const pythonScript = `
import sys
sys.path.insert(0, '${path.join(process.cwd(), "..", "export")}')
from securedrop_export.directory import safe_extractall

safe_extractall('${archivePath}', '${extractDir}')
print('SUCCESS')
`;

      const scriptPath = path.join(tmpDir, "test_extract_multi.py");
      fs.writeFileSync(scriptPath, pythonScript);

      try {
        const result = execSync(`python3 ${scriptPath}`, {
          encoding: "utf8",
          cwd: tmpDir,
        });
        expect(result.trim()).toBe("SUCCESS");

        // Verify all files extracted
        expect(fs.existsSync(path.join(extractDir, "metadata.json"))).toBe(
          true,
        );
        expect(
          fs.existsSync(
            path.join(
              extractDir,
              "export_data",
              "journalist-abc",
              "submission-xyz",
              "doc1.txt",
            ),
          ),
        ).toBe(true);
        expect(
          fs.existsSync(
            path.join(
              extractDir,
              "export_data",
              "journalist-abc",
              "submission-xyz",
              "doc2.txt",
            ),
          ),
        ).toBe(true);
        expect(
          fs.existsSync(
            path.join(
              extractDir,
              "export_data",
              "submission-xyz",
              "transcript.txt",
            ),
          ),
        ).toBe(true);
      } catch (error: any) {
        console.error("Python multi-file test failed:", error.message);
        throw error;
      }
    });
  });

  describe("Edge cases", () => {
    it("should handle files with special characters in names", async () => {
      const exporter = new ArchiveExporter();
      const testFile = path.join(archiveDir, "file with spaces.txt");
      fs.writeFileSync(testFile, "content");

      const archivePath = await exporter.createArchive({
        archiveDir,
        archiveFilename: "special-chars.sd-export",
        metadata: { device: "disk" },
        filepaths: [testFile],
      });

      const extractDir = path.join(tmpDir, "extract");
      fs.mkdirSync(extractDir);
      await tar.x({ file: archivePath, cwd: extractDir });

      const extractedFile = path.join(
        extractDir,
        "export_data",
        "file with spaces.txt",
      );
      expect(fs.existsSync(extractedFile)).toBe(true);
    });

    it("should create valid tarball with no files (metadata only)", async () => {
      const exporter = new ArchiveExporter();

      const archivePath = await exporter.createArchive({
        archiveDir,
        archiveFilename: "metadata-only.sd-export",
        metadata: { device: "usb-test" },
        filepaths: [],
      });

      const extractDir = path.join(tmpDir, "extract");
      fs.mkdirSync(extractDir);
      await tar.x({ file: archivePath, cwd: extractDir });

      // Should only have metadata.json
      const entries = fs.readdirSync(extractDir);
      expect(entries).toContain("metadata.json");

      const metadata = JSON.parse(
        fs.readFileSync(path.join(extractDir, "metadata.json"), "utf8"),
      );
      expect(metadata.device).toBe("usb-test");
    });
  });
});
