import { describe, it, expect, vi, beforeEach, afterEach } from "vitest";
import type { TFunction } from "i18next";
import {
  formatDateShort,
  formatDateLong,
  getInitials,
  toTitleCase,
  formatJournalistName,
  prettyPrintBytes,
  formatFilename,
} from "./utils";
import type { JournalistMetadata } from "../types";

describe("utils", () => {
  // Mock Date.now to ensure consistent test results
  let mockDate: Date;

  beforeEach(() => {
    mockDate = new Date("2024-01-15T12:00:00Z");
    vi.useFakeTimers();
    vi.setSystemTime(mockDate);
  });

  afterEach(() => {
    vi.useRealTimers();
  });

  describe("formatDateShort", () => {
    const mockT = vi.fn((key: string) => {
      switch (key) {
        case "yesterday":
          return "Yesterday";
        default:
          return key;
      }
    }) as unknown as TFunction;

    beforeEach(() => {
      vi.clearAllMocks();
    });

    describe("today formatting", () => {
      it("should format today's date as time only", () => {
        const todayDate = "2024-01-15T14:30:00Z";
        const result = formatDateShort(todayDate, "en-US", mockT);
        expect(result).toMatch(/\d{1,2}:\d{2}.*[AP]M/); // Matches time format like "2:30 PM"
      });

      it("should format today's date with different locale", () => {
        const todayDate = "2024-01-15T09:15:00Z";
        const result = formatDateShort(todayDate, "fr-FR", mockT);
        expect(result).toMatch(/\d{1,2}:\d{2}/); // French format without AM/PM
      });

      it("should handle today's date at midnight", () => {
        const midnightDate = "2024-01-15T00:00:00Z";
        const result = formatDateShort(midnightDate, "en-US", mockT);
        // Midnight UTC might be displayed as yesterday in local time
        expect(result).toMatch(/12:00.*AM|Yesterday/);
      });
    });

    describe("yesterday formatting", () => {
      it("should format yesterday's date as 'Yesterday'", () => {
        const yesterdayDate = "2024-01-14T15:30:00Z";
        const result = formatDateShort(yesterdayDate, "en-US", mockT);
        expect(result).toBe("Yesterday");
        expect(mockT).toHaveBeenCalledWith("yesterday");
      });

      it("should handle yesterday at different times", () => {
        const yesterdayMorning = "2024-01-14T08:00:00Z";
        const result = formatDateShort(yesterdayMorning, "en-US", mockT);
        expect(result).toBe("Yesterday");
      });
    });

    describe("this year formatting", () => {
      it("should format dates in current year as month and day", () => {
        const currentYearDate = "2024-03-10T10:00:00Z";
        const result = formatDateShort(currentYearDate, "en-US", mockT);
        expect(result).toBe("Mar 10");
      });

      it("should format dates with different locale", () => {
        const currentYearDate = "2024-12-25T10:00:00Z";
        const result = formatDateShort(currentYearDate, "fr-FR", mockT);
        expect(result).toMatch(/déc\.?\s*25|25\s*déc/i); // French format
      });

      it("should handle single digit days", () => {
        const singleDigitDay = "2024-05-05T10:00:00Z";
        const result = formatDateShort(singleDigitDay, "en-US", mockT);
        expect(result).toBe("May 5");
      });
    });

    describe("previous years formatting", () => {
      it("should format dates from previous years with year", () => {
        const previousYearDate = "2023-06-15T10:00:00Z";
        const result = formatDateShort(previousYearDate, "en-US", mockT);
        expect(result).toBe("Jun 15, 2023");
      });

      it("should format very old dates", () => {
        const oldDate = "2020-01-01T10:00:00Z";
        const result = formatDateShort(oldDate, "en-US", mockT);
        expect(result).toBe("Jan 1, 2020");
      });

      it("should handle different locale for previous years", () => {
        const previousYearDate = "2022-11-30T10:00:00Z";
        const result = formatDateShort(previousYearDate, "de-DE", mockT);
        // German format: "30. Nov. 2022"
        expect(result).toMatch(/30\.?\s*Nov\.?\s*2022/i);
      });
    });

    describe("locale normalization", () => {
      it("should handle POSIX locale format", () => {
        const result = formatDateShort(
          "2024-03-10T10:00:00Z",
          "en_US.UTF-8",
          mockT,
        );
        expect(result).toBe("Mar 10");
      });

      it("should handle locale with underscore", () => {
        const result = formatDateShort("2024-03-10T10:00:00Z", "fr_FR", mockT);
        expect(result).toMatch(/mars?\s*10|10\s*mars?/i);
      });

      it("should fallback to language code for invalid locale", () => {
        const result = formatDateShort(
          "2024-03-10T10:00:00Z",
          "invalid_LOCALE",
          mockT,
        );
        expect(result).toBeTruthy(); // Should not throw
      });

      it("should fallback to 'en' for completely invalid locale", () => {
        const result = formatDateShort("2024-03-10T10:00:00Z", "xxx", mockT);
        expect(result).toBeTruthy(); // Should fallback to English
      });

      it("should use browser default when locale is empty", () => {
        const result = formatDateShort("2024-03-10T10:00:00Z", "", mockT);
        expect(result).toBeTruthy();
      });

      it("should handle null/undefined locale", () => {
        // @ts-expect-error - Testing null locale
        const resultNull = formatDateShort("2024-03-10T10:00:00Z", null, mockT);
        expect(resultNull).toBeTruthy();

        const resultUndefined = formatDateShort(
          "2024-03-10T10:00:00Z",
          // @ts-expect-error - Testing undefined locale
          undefined,
          mockT,
        );
        expect(resultUndefined).toBeTruthy();
      });
    });

    describe("edge cases and error handling", () => {
      it("should handle invalid date strings gracefully", () => {
        const result = formatDateShort("invalid-date", "en-US", mockT);
        expect(result).toMatch(/Invalid Date|NaN/i);
      });

      it("should handle empty date string", () => {
        const result = formatDateShort("", "en-US", mockT);
        expect(result).toMatch(/Invalid Date|NaN/i);
      });

      it("should handle dates far in the future", () => {
        const futureDate = "2030-12-31T23:59:59Z";
        const result = formatDateShort(futureDate, "en-US", mockT);
        expect(result).toBe("Dec 31, 2030");
      });

      it("should handle leap year dates", () => {
        const leapYearDate = "2024-02-29T10:00:00Z";
        const result = formatDateShort(leapYearDate, "en-US", mockT);
        expect(result).toBe("Feb 29");
      });

      it("should handle different timezone inputs", () => {
        const utcDate = "2024-03-10T10:00:00Z";
        const offsetDate = "2024-03-10T10:00:00+05:00";

        const resultUTC = formatDateShort(utcDate, "en-US", mockT);
        const resultOffset = formatDateShort(offsetDate, "en-US", mockT);

        expect(resultUTC).toBeTruthy();
        expect(resultOffset).toBeTruthy();
      });
    });

    describe("UTC assumption", () => {
      it("should treat timestamp without timezone as UTC", () => {
        const timestampWithoutTZ = "2024-08-29T21:13:10.760877";
        const timestampWithTZ = "2024-08-29T21:13:10.760877Z";

        const resultWithoutTZ = formatDateShort(
          timestampWithoutTZ,
          "en-US",
          mockT,
        );
        const resultWithTZ = formatDateShort(timestampWithTZ, "en-US", mockT);

        // Both should produce the same result since we treat no-TZ as UTC
        expect(resultWithoutTZ).toBe(resultWithTZ);
      });
    });
  });

  describe("formatDateLong", () => {
    it("should format date with full timestamp including time and timezone", () => {
      const dateString = "2024-03-10T14:30:45Z";
      const result = formatDateLong(dateString, "en-US");

      // Should include year, month, day, time, and timezone
      expect(result).toMatch(/March.*10.*2024/); // Date parts with full month name
      expect(result).toMatch(/\d{1,2}:\d{2}(?!\d)/); // Time without seconds or leading zeros on hours
      expect(result).toMatch(/[AP]M/); // AM/PM
      expect(result).toMatch(/[A-Z]{3,4}/); // Timezone abbreviation
    });

    it("should format date with different locale", () => {
      const dateString = "2024-12-25T09:15:30Z";
      const result = formatDateLong(dateString, "fr-FR");

      // French format should have full month name
      expect(result).toMatch(/décembre|December/i); // French December (full name)
      expect(result).toMatch(/25/); // Day
      expect(result).toMatch(/2024/); // Year
      expect(result).toMatch(/\d{1,2}:\d{2}(?!\d)/); // Time without seconds
    });

    it("should handle POSIX locale format", () => {
      const dateString = "2024-06-15T18:45:12Z";
      const result = formatDateLong(dateString, "en_US.UTF-8");

      expect(result).toMatch(/June.*15.*2024/);
      expect(result).toMatch(/\d{1,2}:\d{2}(?!\d)/); // Time without seconds
    });

    it("should fallback gracefully for invalid locale", () => {
      const dateString = "2024-01-01T00:00:00Z";
      const result = formatDateLong(dateString, "invalid_locale");

      // Should still produce a valid date string (may show different date due to timezone conversion)
      expect(result).toMatch(/January.*1.*2024|December.*31.*2023/); // Could be either due to timezone (full month names)
      expect(result).toMatch(/\d{1,2}:\d{2}(?!\d)/); // Time without seconds
    });

    it("should handle different timezone inputs", () => {
      const utcDate = "2024-05-20T10:30:15Z";
      const offsetDate = "2024-05-20T10:30:15+02:00";

      const resultUTC = formatDateLong(utcDate, "en-US");
      const resultOffset = formatDateLong(offsetDate, "en-US");

      // Both should be valid timestamps (times will be converted to local timezone)
      expect(resultUTC).toMatch(/May.*20.*2024/);
      expect(resultUTC).toMatch(/\d{1,2}:\d{2}(?!\d)/);
      expect(resultOffset).toMatch(/May.*20.*2024/);
      expect(resultOffset).toMatch(/\d{1,2}:\d{2}(?!\d)/);
    });

    it("should handle edge case dates", () => {
      // New Year's Day (may show as Dec 31 in local timezone)
      const newYear = "2024-01-01T00:00:00Z";
      const result1 = formatDateLong(newYear, "en-US");
      expect(result1).toMatch(/January.*1.*2024|December.*31.*2023/); // Could be either due to timezone (full month names)
      expect(result1).toMatch(/\d{1,2}:\d{2}(?!\d)/);

      // Year end
      const yearEnd = "2024-12-31T23:59:59Z";
      const result2 = formatDateLong(yearEnd, "en-US");
      expect(result2).toMatch(/December.*31.*2024/);
      expect(result2).toMatch(/\d{1,2}:\d{2}(?!\d)/);
    });

    it("should handle invalid date strings", () => {
      const invalidDate = "invalid-date-string";
      const result = formatDateLong(invalidDate, "en-US");

      // Should contain "Invalid Date" or similar
      expect(result).toMatch(/Invalid Date/i);
    });

    it("should handle empty date string", () => {
      const result = formatDateLong("", "en-US");
      expect(result).toMatch(/Invalid Date/i);
    });

    it("should treat timestamp without timezone as UTC", () => {
      const timestampWithoutTZ = "2024-08-29T21:13:10.760877";
      const timestampWithTZ = "2024-08-29T21:13:10.760877Z";

      const resultWithoutTZ = formatDateLong(timestampWithoutTZ, "en-US");
      const resultWithTZ = formatDateLong(timestampWithTZ, "en-US");

      // Both should produce the same result since we treat no-TZ as UTC
      expect(resultWithoutTZ).toBe(resultWithTZ);
    });
  });

  describe("getInitials", () => {
    it("should extract initials from single word", () => {
      expect(getInitials("John")).toBe("J");
    });

    it("should extract initials from two words", () => {
      expect(getInitials("John Doe")).toBe("JD");
    });

    it("should extract initials from multiple words", () => {
      expect(getInitials("John Michael Doe")).toBe("JM");
    });

    it("should limit to 2 characters maximum", () => {
      expect(getInitials("John Michael Alexander Doe")).toBe("JM");
    });

    it("should handle lowercase names", () => {
      expect(getInitials("john doe")).toBe("JD");
    });

    it("should handle mixed case names", () => {
      expect(getInitials("JoHn DoE")).toBe("JD");
    });

    it("should handle names with extra spaces", () => {
      expect(getInitials("  John   Doe  ")).toBe("JD");
    });

    it("should handle single character words", () => {
      expect(getInitials("J D")).toBe("JD");
    });

    it("should handle empty string", () => {
      expect(getInitials("")).toBe("");
    });

    it("should handle string with only spaces", () => {
      expect(getInitials("   ")).toBe("");
    });

    it("should handle names with numbers", () => {
      expect(getInitials("John2 Doe3")).toBe("JD");
    });

    it("should handle names with special characters", () => {
      expect(getInitials("Jean-Pierre Marie")).toBe("JM");
    });

    it("should handle names with apostrophes", () => {
      expect(getInitials("O'Connor D'Angelo")).toBe("OD");
    });

    it("should handle non-English characters", () => {
      expect(getInitials("José María")).toBe("JM");
    });

    it("should handle very long single word", () => {
      expect(getInitials("Supercalifragilisticexpialidocious")).toBe("S");
    });

    describe("edge cases", () => {
      it("should handle null input", () => {
        // @ts-expect-error - Testing null input
        expect(() => getInitials(null)).toThrow();
      });

      it("should handle undefined input", () => {
        // @ts-expect-error - Testing undefined input
        expect(() => getInitials(undefined)).toThrow();
      });

      it("should handle unicode characters", () => {
        expect(getInitials("αβγ δεζ")).toBe("ΑΔ");
      });

      it("should handle emojis in names", () => {
        const result = getInitials("😀John 😊Doe");
        expect(result.length).toBeLessThanOrEqual(2);
        expect(result).toBeTruthy();
      });
    });
  });

  describe("toTitleCase", () => {
    it("should convert simple lowercase string to title case", () => {
      expect(toTitleCase("hello world")).toBe("Hello World");
    });

    it("should convert simple uppercase string to title case", () => {
      expect(toTitleCase("HELLO WORLD")).toBe("Hello World");
    });

    it("should convert mixed case string to title case", () => {
      expect(toTitleCase("hELLo WoRLd")).toBe("Hello World");
    });

    it("should handle single word", () => {
      expect(toTitleCase("hello")).toBe("Hello");
    });

    it("should handle single character", () => {
      expect(toTitleCase("a")).toBe("A");
    });

    it("should handle empty string", () => {
      expect(toTitleCase("")).toBe("");
    });

    it("should handle string with numbers", () => {
      expect(toTitleCase("hello123 world456")).toBe("Hello123 World456");
    });

    it("should handle string with punctuation", () => {
      expect(toTitleCase("hello, world!")).toBe("Hello, World!");
    });

    it("should handle strings with hyphens", () => {
      expect(toTitleCase("hello-world test-case")).toBe(
        "Hello-world Test-case",
      );
    });

    it("should handle strings with apostrophes", () => {
      expect(toTitleCase("don't can't won't")).toBe("Don't Can't Won't");
    });

    it("should handle strings with underscores", () => {
      expect(toTitleCase("hello_world test_case")).toBe(
        "Hello_world Test_case",
      );
    });

    it("should handle multiple spaces", () => {
      expect(toTitleCase("hello    world")).toBe("Hello    World");
    });

    it("should handle leading and trailing spaces", () => {
      expect(toTitleCase("  hello world  ")).toBe("  Hello World  ");
    });

    it("should handle strings with only spaces", () => {
      expect(toTitleCase("   ")).toBe("   ");
    });

    it("should handle special characters", () => {
      expect(toTitleCase("hello@world #test")).toBe("Hello@world #Test");
    });

    it("should handle non-English characters", () => {
      expect(toTitleCase("café naïve résumé")).toBe("Café Naïve Résumé");
    });

    it("should handle unicode characters", () => {
      const result = toTitleCase("αβγ δεζ");
      expect(result).toBeTruthy();
      expect(result).toContain("αβγ");
      expect(result).toContain("δεζ");
    });

    it("should handle mixed punctuation", () => {
      const result = toTitleCase("hello.world,test;case");
      expect(result).toMatch(/^Hello\.world,test;/);
      expect(result.split(/\s+/)).toHaveLength(1); // Should be one word with punctuation
    });

    describe("edge cases", () => {
      it("should handle null input", () => {
        // @ts-expect-error - Testing null input
        expect(() => toTitleCase(null)).toThrow();
      });

      it("should handle undefined input", () => {
        // @ts-expect-error - Testing undefined input
        expect(() => toTitleCase(undefined)).toThrow();
      });

      it("should handle very long strings", () => {
        const longString = "a".repeat(1000) + " " + "b".repeat(1000);
        const result = toTitleCase(longString);
        expect(result.startsWith("A")).toBe(true);
        expect(result.includes(" B")).toBe(true);
      });

      it("should handle strings with only numbers", () => {
        expect(toTitleCase("123 456")).toBe("123 456");
      });

      it("should handle strings with tabs and newlines", () => {
        const result = toTitleCase("hello\tworld\ntest");
        expect(result).toMatch(/^Hello\t/);
        expect(result).toContain("World");
        expect(result).toContain("Test");
      });

      it("should handle emojis", () => {
        const result = toTitleCase("😀hello 😊world");
        expect(result).toContain("😀");
        expect(result).toContain("😊");
        expect(result).toMatch(/Hello/);
        expect(result).toMatch(/World/);
      });
    });
  });

  describe("formatJournalistName", () => {
    it("should display full name when both first and last names are provided", () => {
      const journalist: JournalistMetadata = {
        uuid: "1",
        username: "dellsberg",
        first_name: "Daniel",
        last_name: "Ellsberg",
      };
      expect(formatJournalistName(journalist)).toBe("Daniel Ellsberg");
    });

    it("should display only first name when last name is null", () => {
      const journalist: JournalistMetadata = {
        uuid: "2",
        username: "john_user",
        first_name: "John",
        last_name: null,
      };
      expect(formatJournalistName(journalist)).toBe("John");
    });

    it("should display only last name when first name is null", () => {
      const journalist: JournalistMetadata = {
        uuid: "3",
        username: "smith_user",
        first_name: null,
        last_name: "Smith",
      };
      expect(formatJournalistName(journalist)).toBe("Smith");
    });

    it("should display username when both first and last names are null", () => {
      const journalist: JournalistMetadata = {
        uuid: "4",
        username: "journalist",
        first_name: null,
        last_name: null,
      };
      expect(formatJournalistName(journalist)).toBe("journalist");
    });

    it("should display username when both first and last names are empty strings", () => {
      const journalist: JournalistMetadata = {
        uuid: "5",
        username: "deleted",
        first_name: "",
        last_name: "",
      };
      expect(formatJournalistName(journalist)).toBe("deleted");
    });

    it("should handle names with spaces", () => {
      const journalist: JournalistMetadata = {
        uuid: "6",
        username: "van_der_berg",
        first_name: "Jan",
        last_name: "van der Berg",
      };
      expect(formatJournalistName(journalist)).toBe("Jan van der Berg");
    });

    it("should handle single character names", () => {
      const journalist: JournalistMetadata = {
        uuid: "7",
        username: "x_user",
        first_name: "X",
        last_name: "Y",
      };
      expect(formatJournalistName(journalist)).toBe("X Y");
    });
  });

  describe("prettyPrintBytes", () => {
    it("should format 0 bytes", () => {
      expect(prettyPrintBytes(0)).toBe("0 B");
    });

    it("should format bytes less than 1 KB", () => {
      expect(prettyPrintBytes(512)).toBe("512 B");
    });

    it("should format kilobytes", () => {
      expect(prettyPrintBytes(1024)).toBe("1 KB");
      expect(prettyPrintBytes(1536)).toBe("1.5 KB");
    });

    it("should format megabytes", () => {
      expect(prettyPrintBytes(1048576)).toBe("1 MB");
      expect(prettyPrintBytes(1572864)).toBe("1.5 MB");
    });

    it("should format gigabytes", () => {
      expect(prettyPrintBytes(1073741824)).toBe("1 GB");
    });

    it("should format terabytes", () => {
      expect(prettyPrintBytes(1099511627776)).toBe("1 TB");
    });

    it("should format petabytes", () => {
      expect(prettyPrintBytes(1125899906842624)).toBe("1 PB");
    });

    it("should round to two decimals", () => {
      expect(prettyPrintBytes(123456789)).toMatch(/\d+\.\d{1,2} MB/);
    });

    it("should handle negative numbers", () => {
      expect(prettyPrintBytes(-1024)).toBe("0 B");
    });
  });

  describe("formatFilename", () => {
    it("returns filename unchanged when within maxLength", () => {
      expect(formatFilename("report.pdf", 12, 6)).toBe("report.pdf");
      expect(formatFilename("short.txt", 20, 6)).toBe("short.txt");
    });

    it("truncates with ellipses in the middle when too long", () => {
      expect(formatFilename("very_long_filename_example.txt", 20, 5)).toBe(
        "very_lon...ample.txt",
      );
      expect(formatFilename("averyverylongfilenamewithoutdot", 20, 6)).toBe(
        "averyverylo...outdot",
      );
    });

    it("uses custom endLength correctly", () => {
      expect(formatFilename("very_long_filename_example.txt", 20, 3)).toBe(
        "very_long_...ple.txt",
      );
      expect(formatFilename("very_long_filename_example.txt", 20, 8)).toBe(
        "very_..._example.txt",
      );
    });

    it("retains file extension correctly", () => {
      expect(
        formatFilename("super_long_file_name_with_long_ext.extension", 25, 6),
      ).toBe("super_...ng_ext.extension");
      expect(formatFilename("super_long_name_archive.tar.gz", 15, 6)).toBe(
        "sup...ve.tar.gz",
      );
    });

    it("handles filenames with no extension", () => {
      expect(formatFilename("longfilenamewithoutdot", 15, 6)).toBe(
        "longfi...outdot",
      );
      expect(formatFilename("shortname", 10, 6)).toBe("shortname");
    });

    it("skips ellipses if namePart is shorter than or equal to endLength", () => {
      expect(formatFilename("tiny.pdf", 10, 6)).toBe("tiny.pdf");
      expect(formatFilename("small.doc", 12, 8)).toBe("small.doc");
    });

    it("handles extremely small maxLength gracefully", () => {
      expect(formatFilename("example.txt", 5, 6)).toBe("...txt");
      expect(formatFilename("short.txt", 5, 6)).toBe("...txt");
    });

    it("handles filenames with dots in the name", () => {
      expect(formatFilename("my.cool.project.file.js", 19, 6)).toBe(
        "my.cool...t.file.js",
      );
    });

    it("handles long extensions properly", () => {
      expect(formatFilename("filename.reallylongext", 20, 6)).toBe(
        "...reallylongext",
      );
    });
  });
});
