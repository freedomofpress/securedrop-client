import { describe, it, expect, vi, beforeEach, afterEach } from "vitest";
import type { TFunction } from "i18next";
import { formatDate, getInitials, toTitleCase } from "./utils";

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

  describe("formatDate", () => {
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
        const result = formatDate(todayDate, "en-US", mockT);
        expect(result).toMatch(/\d{1,2}:\d{2}.*[AP]M/); // Matches time format like "2:30 PM"
      });

      it("should format today's date with different locale", () => {
        const todayDate = "2024-01-15T09:15:00Z";
        const result = formatDate(todayDate, "fr-FR", mockT);
        expect(result).toMatch(/\d{1,2}:\d{2}/); // French format without AM/PM
      });

      it("should handle today's date at midnight", () => {
        const midnightDate = "2024-01-15T00:00:00Z";
        const result = formatDate(midnightDate, "en-US", mockT);
        // Midnight UTC might be displayed as yesterday in local time
        expect(result).toMatch(/12:00.*AM|Yesterday/);
      });
    });

    describe("yesterday formatting", () => {
      it("should format yesterday's date as 'Yesterday'", () => {
        const yesterdayDate = "2024-01-14T15:30:00Z";
        const result = formatDate(yesterdayDate, "en-US", mockT);
        expect(result).toBe("Yesterday");
        expect(mockT).toHaveBeenCalledWith("yesterday");
      });

      it("should handle yesterday at different times", () => {
        const yesterdayMorning = "2024-01-14T08:00:00Z";
        const result = formatDate(yesterdayMorning, "en-US", mockT);
        expect(result).toBe("Yesterday");
      });
    });

    describe("this year formatting", () => {
      it("should format dates in current year as month and day", () => {
        const currentYearDate = "2024-03-10T10:00:00Z";
        const result = formatDate(currentYearDate, "en-US", mockT);
        expect(result).toBe("Mar 10");
      });

      it("should format dates with different locale", () => {
        const currentYearDate = "2024-12-25T10:00:00Z";
        const result = formatDate(currentYearDate, "fr-FR", mockT);
        expect(result).toMatch(/déc\.?\s*25|25\s*déc/i); // French format
      });

      it("should handle single digit days", () => {
        const singleDigitDay = "2024-05-05T10:00:00Z";
        const result = formatDate(singleDigitDay, "en-US", mockT);
        expect(result).toBe("May 5");
      });
    });

    describe("previous years formatting", () => {
      it("should format dates from previous years with year", () => {
        const previousYearDate = "2023-06-15T10:00:00Z";
        const result = formatDate(previousYearDate, "en-US", mockT);
        expect(result).toBe("Jun 15, 2023");
      });

      it("should format very old dates", () => {
        const oldDate = "2020-01-01T10:00:00Z";
        const result = formatDate(oldDate, "en-US", mockT);
        expect(result).toBe("Jan 1, 2020");
      });

      it("should handle different locale for previous years", () => {
        const previousYearDate = "2022-11-30T10:00:00Z";
        const result = formatDate(previousYearDate, "de-DE", mockT);
        // German format: "30. Nov. 2022"
        expect(result).toMatch(/30\.?\s*Nov\.?\s*2022/i);
      });
    });

    describe("locale normalization", () => {
      it("should handle POSIX locale format", () => {
        const result = formatDate("2024-03-10T10:00:00Z", "en_US.UTF-8", mockT);
        expect(result).toBe("Mar 10");
      });

      it("should handle locale with underscore", () => {
        const result = formatDate("2024-03-10T10:00:00Z", "fr_FR", mockT);
        expect(result).toMatch(/mars?\s*10|10\s*mars?/i);
      });

      it("should fallback to language code for invalid locale", () => {
        const result = formatDate(
          "2024-03-10T10:00:00Z",
          "invalid_LOCALE",
          mockT,
        );
        expect(result).toBeTruthy(); // Should not throw
      });

      it("should fallback to 'en' for completely invalid locale", () => {
        const result = formatDate("2024-03-10T10:00:00Z", "xxx", mockT);
        expect(result).toBeTruthy(); // Should fallback to English
      });

      it("should use browser default when locale is empty", () => {
        const result = formatDate("2024-03-10T10:00:00Z", "", mockT);
        expect(result).toBeTruthy();
      });

      it("should handle null/undefined locale", () => {
        // @ts-expect-error - Testing null locale
        const resultNull = formatDate("2024-03-10T10:00:00Z", null, mockT);
        expect(resultNull).toBeTruthy();

        const resultUndefined = formatDate(
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
        const result = formatDate("invalid-date", "en-US", mockT);
        expect(result).toMatch(/Invalid Date|NaN/i);
      });

      it("should handle empty date string", () => {
        const result = formatDate("", "en-US", mockT);
        expect(result).toMatch(/Invalid Date|NaN/i);
      });

      it("should handle dates far in the future", () => {
        const futureDate = "2030-12-31T23:59:59Z";
        const result = formatDate(futureDate, "en-US", mockT);
        expect(result).toBe("Dec 31, 2030");
      });

      it("should handle leap year dates", () => {
        const leapYearDate = "2024-02-29T10:00:00Z";
        const result = formatDate(leapYearDate, "en-US", mockT);
        expect(result).toBe("Feb 29");
      });

      it("should handle different timezone inputs", () => {
        const utcDate = "2024-03-10T10:00:00Z";
        const offsetDate = "2024-03-10T10:00:00+05:00";

        const resultUTC = formatDate(utcDate, "en-US", mockT);
        const resultOffset = formatDate(offsetDate, "en-US", mockT);

        expect(resultUTC).toBeTruthy();
        expect(resultOffset).toBeTruthy();
      });
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
});
