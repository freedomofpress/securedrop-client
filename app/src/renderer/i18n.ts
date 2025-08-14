import i18n from "i18next";
import { initReactI18next } from "react-i18next";
import { resources } from "./locales";

// Get system language and update i18n
const initializeLanguage = async () => {
  try {
    const systemLanguage = await window.electronAPI.getSystemLanguage();
    if (systemLanguage && systemLanguage !== i18n.language) {
      await i18n.changeLanguage(systemLanguage);
    }
  } catch (error) {
    console.warn("Could not get system language:", error);
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

// Initialize system language after i18n is ready
initializeLanguage();
export default i18n;
