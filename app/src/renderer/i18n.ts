import i18n from "i18next";
import { initReactI18next } from "react-i18next";
import { resources } from "./locales";

const initialLanguage = navigator.language || "en";

i18n.use(initReactI18next).init({
  resources,
  lng: initialLanguage,
  fallbackLng: "en",
  defaultNS: "common",
  interpolation: {
    // react is already safe from xss
    escapeValue: false,
  },
});

export default i18n;
