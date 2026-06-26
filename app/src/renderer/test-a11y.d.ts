// Augments Vitest's Vi.Assertion with axe accessibility matchers so that
// expect(axeResults).toHaveNoViolations() is correctly typed everywhere in
// the renderer test compilation.
import "vitest-axe/extend-expect";
