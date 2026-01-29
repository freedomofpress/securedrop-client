import { describe, expect, it, afterEach, vi } from "vitest";
import fs from "fs";
import path from "path";
import os from "os";
import { Journalist, SourceWithItems } from "../types";
import { renderTranscript, writeTranscript } from "./transcriber";
import { DB } from "./database";
import { setUmask } from "./umask";

describe("Transcriber Component Tests", () => {
  const testHomeDirPrefix = path.join(os.tmpdir(), "test-home");
  const testHomeDir: string = fs.mkdtempSync(testHomeDirPrefix);
  const originalHomedir = os.homedir;
  let originalUmask: number;

  beforeEach(() => {
    // Set umask for secure file permissions
    originalUmask = process.umask();
    setUmask();

    if (fs.existsSync(testHomeDir)) {
      fs.rmSync(testHomeDir, { recursive: true, force: true });
    }
    os.homedir = () => testHomeDir;
  });

  afterEach(() => {
    process.umask(originalUmask);
    os.homedir = originalHomedir;
    if (fs.existsSync(testHomeDir)) {
      fs.rmSync(testHomeDir, { recursive: true, force: true });
    }
  });

  // Test data
  const mockSourceWithItems: SourceWithItems = {
    uuid: "source-1",
    data: {
      uuid: "source-1",
      journalist_designation: "palpable disquiet",
      is_starred: false,
      is_seen: false,
      has_attachment: false,
      last_updated: "2026-01-22T10:00:00Z",
      public_key: "test-public-key",
      fingerprint: "test-fingerprint",
    },
    items: [
      {
        uuid: "message-1",
        plaintext: "sphinx of black quartz, judge my vow",
        data: {
          kind: "message",
          uuid: "message-1",
          source: "source-1",
          size: 1024,
          seen_by: [],
          is_read: false,
          interaction_count: 1,
        },
        fetch_progress: 1024,
        fetch_status: 3,
      },
      {
        uuid: "file-1",
        filename: "/error/error/filename.ext",
        data: {
          kind: "file",
          uuid: "file-1",
          source: "source-1",
          size: 1024,
          seen_by: [],
          is_read: false,
          interaction_count: 1,
        },
        fetch_progress: 1024,
        fetch_status: 3,
      },
      {
        uuid: "file-2",
        data: {
          kind: "file",
          uuid: "file-2",
          source: "source-1",
          size: 1024,
          seen_by: [],
          is_read: false,
          interaction_count: 1,
        },
        fetch_progress: 1024,
        fetch_status: 3,
      },
      {
        uuid: "reply-1",
        plaintext: "Interesting message there",
        data: {
          kind: "reply",
          uuid: "reply-1",
          source: "source-1",
          size: 1024,
          journalist_uuid: "journo-1",
          is_deleted_by_source: false,
          seen_by: [],
          interaction_count: 1,
        },
        fetch_progress: 1024,
        fetch_status: 3,
      },
    ],
  };

  const mockJournalist: Journalist = {
    uuid: "journo-1",
    data: {
      uuid: "journo-1",
      username: "notsuperman",
      first_name: "Clark",
      last_name: "Kent",
    },
  };

  function createMockDB() {
    return {
      getJournalistByID: vi.fn(),
    } as unknown as DB;
  }

  afterEach(() => {
    vi.restoreAllMocks();
  });

  it("should return a valid transcript with all message and replies", async () => {
    const db = createMockDB();

    db.getJournalistByID = vi.fn(() => mockJournalist);

    const expectedSource: string = "Source: palpable disquiet";
    const expectedTranscript: string = `Transcript:
-----------
Source wrote:
sphinx of black quartz, judge my vow

Source uploaded file: filename.ext

Source uploaded file: [encrypted file]

notsuperman replied:
Interesting message there
`;

    const output: string = await renderTranscript(mockSourceWithItems, db);
    expect(output).toContain(expectedSource);
    expect(output).toContain(expectedTranscript);
  });

  it("should gracefully handle  errors when looking up journalists", async () => {
    const db = createMockDB();

    db.getJournalistByID = vi.fn(() => {
      throw new Error("mocked error");
    });

    const expectedSource: string = "Source: palpable disquiet";
    const expectedTranscript: string = `Transcript:
-----------
Source wrote:
sphinx of black quartz, judge my vow

Source uploaded file: filename.ext

Source uploaded file: [encrypted file]

Unknown journalist replied:
Interesting message there
`;

    const output: string = await renderTranscript(mockSourceWithItems, db);
    expect(output).toContain(expectedSource);
    expect(output).toContain(expectedTranscript);
  });

  it("should write a valid transcript file", async () => {
    const db = createMockDB();

    db.getJournalistByID = vi.fn(() => {
      return mockJournalist;
    });
    db.getSourceWithItems = vi.fn(() => {
      return mockSourceWithItems;
    });

    const expectedSource: string = "Source: palpable disquiet";
    const expectedTranscript: string = `Transcript:
-----------
Source wrote:
sphinx of black quartz, judge my vow

Source uploaded file: filename.ext

Source uploaded file: [encrypted file]

notsuperman replied:
Interesting message there
`;

    const output: string = await writeTranscript(mockSourceWithItems.uuid, db);
    expect(output).toContain("transcript.txt");
    expect(fs.existsSync(output)).toBe(true);
    console.log(`BANANA: ${output}`);
    const fileContents = fs.readFileSync(output, "utf-8");
    expect(fileContents).toContain(expectedSource);
    expect(fileContents).toContain(expectedTranscript);
  });
});
