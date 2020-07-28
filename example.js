var uc = require(".");

// Ultimate-Calculus example
var code = `(
  λg. λy. let [A| g0, g1] = g; (g0 (g1 y))
  λf. λx. let [B| f0, f1] = f; (f0 (f1 x))
)`;
var term = uc.parse(code);
var {term: norm, stat} = uc.normalize(term);
console.log("Ultimate-Calculus example");
console.log("- term:", uc.show(term));
console.log("- norm:", uc.show(norm));
console.log("- stat:", JSON.stringify(stat));
console.log("");

// Lambda-Calculus example
console.log("Lambda-Calculus example");
var lamb = uc.parse("(λf.λx.(f (f x)) λf.λx.(f (f x)))");
var ulti = uc.lambda_to_ultimate(lamb);
console.log("- lamb-term:", uc.show(lamb));
console.log("- ulti-term:", uc.show(ulti));
var {term:norm, stat} = uc.normalize(ulti);
console.log("- ulti-norm:", uc.show(norm));
console.log("- lamb-norm:", uc.show(uc.ultimate_to_lambda(norm)));
console.log("- stat:", JSON.stringify(stat));
