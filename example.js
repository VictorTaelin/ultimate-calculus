var uc = require(".");

// Ultimate-Calculus example

var term = uc.parse(`λA. λB. let [K| A0, A1] = A; λx. λy. x`);
var type = uc.parse(`∀(A:*). ∀(B:*). let [K| A0, A1] = A; ∀(x: A0). ∀(y: B). A1`);
var env = {_rwts:0};

var {term: norm, stat} = uc.normalize(term);
console.log("Ultimate-Calculus example");
console.log("- term:", uc.show(term));
console.log("- norm:", uc.show(norm));
console.log("- lamb:", uc.show(uc.ultimate_to_lambda(norm)));
console.log("- stat:", JSON.stringify(stat));
console.log("");

var env = {_rwts:0};
var ctx = {_rwts:0};
try {
  console.log("- type:", uc.show(type));
  uc.typecheck(term, type, env, ctx);
} catch (e) {
  console.log(e);
}




// Lambda-Calculus example
//console.log("Lambda-Calculus example");
//var lamb = uc.parse("({x}(x x) {f}{x}(f (f x)))");
//var ulti = uc.lambda_to_ultimate(lamb);
//console.log("- lamb-term:", uc.show(lamb));
//console.log("- ulti-term:", uc.show(ulti));
//var {term:norm, stat} = uc.normalize(ulti);
//console.log("- ulti-norm:", uc.show(norm));
//console.log("- stat:", JSON.stringify(stat));
//
//var code = `(
  //{As} {Az} let [A| As0, As1] = As; (As0 (As1 Az))
  //{Bs} {Bz} let [B| Bs0, Bs1] = Bs; (Bs0 (Bs1 Bz))
//)`;
//var code = `
  //( {l} let [A| l0, l1] = l; (l0 #l1)
    //{Bs} {Bz} let [B| Bs0, Bs1] = Bs; (Bs0 (Bs1 Bz))
  //)
//)`;
//var code = `
//( 
  //{As} {Az} let [A|Aa,Ab] = (Ac (Ad [A|Ab,Az])); let [A|Ac,Ad] = As; Aa
  //{Bs} {Bz} let [B|Ba,Bb] = (Bc (Bd [B|Bb,Bz])); let [B|Bc,Bd] = Bs; Ba
//)`;
//var code = `
//( 
  //{As} {Az} let [A|Aa,Ab] = (Ac (Ad [A|Ab,Az])); let [A|Ac,Ad] = As; Aa
  //# {Bs} {Bz} let [A|Ba,Bb] = (Bc (Bd [A|Bb,Bz])); let [A|Bc,Bd] = Bs; Ba
//)`;
//var code = `let [A| a, b] = #{x} x; [A| a, b]`;
