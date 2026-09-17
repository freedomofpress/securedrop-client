import i18n from "i18next";
import { initReactI18next } from "react-i18next";
import { PSEUDO_RTL_LANGUAGE, resources } from "./locales";
import { normalizeLocale, type TextDirection } from "./utils";

export const directionFor = (language: string): TextDirection => {
  if (language === PSEUDO_RTL_LANGUAGE) {
    return "rtl";
  }
  return i18n.dir(language) as TextDirection;
};

const applyDocumentDirection = (language: string) => {
  const root = document.documentElement;
  root.lang = language;
  root.dir = directionFor(language);
};

export const textDirection = (): TextDirection => directionFor(i18n.language);

const initializeLanguage = async () => {
  try {
    const systemLanguage = await window.electronAPI.getSystemLanguage();
    if (!systemLanguage) {
      return;
    }
    const language = normalizeLocale(systemLanguage);
    if (language !== i18n.language) {
      await i18n.changeLanguage(language);
    }
  } catch (error) {
    console.warn("Could not get system language:", error);
  } finally {
    applyDocumentDirection(i18n.language);
  }
};

i18n.use(initReactI18next).init({
  resources,
  lng: "en", // This gets updated immediately to the system language
  fallbackLng: "en",
  defaultNS: "common",
  interpolation: {
    // react is already safe from xss
    escapeValue: false,
  },
});

applyDocumentDirection(i18n.language);

export const languageReady = initializeLanguage();

export default i18n;
