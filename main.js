var uc = require(".");

// An unscoped duplication example
const code = `(
  {g} {y} let [A| g0, g1] = g; (g0 (g1 y))
  {f} {x} let [B| f0, f1] = f; (f0 (f1 x))
)`;
const term = uc.parse(code);
const {term: norm, stats} = uc.normalize(term);

console.log("- term:", uc.show(term));
console.log("- norm:", uc.show(norm));
console.log("- stat:", JSON.stringify(stats));
