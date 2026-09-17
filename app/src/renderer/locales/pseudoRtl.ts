// Generates the RTL pseudolocale ("en-XB") from the English source strings.

const RLE = "\u202B"; // RIGHT-TO-LEFT EMBEDDING
const PDF = "\u202C"; // POP DIRECTIONAL FORMATTING

type Translations = { [key: string]: string | Translations };

// Interpolation placeholders ({{count}}) and Trans markup (<bold>, <br>) are
// left untouched inside the wrapper, so they keep working as usual.
const wrap = (value: string): string =>
  value === "" ? value : `${RLE}[${value}]${PDF}`;

export function toPseudoRtl<T extends Translations>(resource: T): T {
  const pseudo: Translations = {};
  for (const [key, value] of Object.entries(resource)) {
    pseudo[key] = typeof value === "string" ? wrap(value) : toPseudoRtl(value);
  }
  return pseudo as T;
}
