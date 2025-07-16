import i18n from "i18next";
import { initReactI18next } from "react-i18next";
import { resources } from "./locales";

i18n.use(initReactI18next).init({
  resources,
  lng: "en",
  fallbackLng: "en",
  defaultNS: "common",
  interpolation: {
    // react is already safe from xss
    escapeValue: false,
  },
});

export default i18n;
