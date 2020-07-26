var uc = require(".");

// Ultimate-Calculus example
var code = `(
  {As} {Az} let [A| As0, As1] = As; (As0 (As1 Az))
  {Bs} {Bz} let [B| Bs0, Bs1] = Bs; (Bs0 (Bs1 Bz))
)`;
var code = `(
  {k} let [A| k0, k1] = k; (k0 k1)
  {Bs} {Bz} let [B| Bs0, Bs1] = Bs; (Bs0 (Bs1 Bz))
)`;
//var code = `let [A| a, b] = #{x} x; [A| a, b]`;
var term = uc.parse(code);
var {term: norm, stat} = uc.normalize(term);
console.log("Ultimate-Calculus example");
console.log("- term:", uc.show(term));
console.log("- norm:", uc.show(norm));
console.log("- lamb:", uc.show(uc.ultimate_to_lambda(norm)));
console.log("- stat:", JSON.stringify(stat));
console.log("");

// Lambda-Calculus example
//console.log("Lambda-Calculus example");
//var lamb = uc.parse("({x}(x x) {f}{x}(f (f x)))");
//var ulti = uc.lambda_to_ultimate(lamb);
//console.log("- lamb-term:", uc.show(lamb));
//console.log("- ulti-term:", uc.show(ulti));
//var {term:norm, stat} = uc.normalize(ulti);
//console.log("- ulti-norm:", uc.show(norm));
//console.log("- stat:", JSON.stringify(stat));
