// Tests
// -----

import {read, lambda_to_optimal, show_as_lambda, show_mem} from "./syntax.ts"
import {normal, get_gas, deref} from "./optimal_calculus.ts"
import {normal_ffi} from "./optimal_calculus_ffi.ts"

var code : string = `
  let Y      = ((λr:λf:(f (r r f))) (λr:λf:(f (r r f))))

  let succ   = λn: λz: λs: (s n)
  let zero   = λz: λs: z
  let double = (Y λdouble: λn: (n zero λpred:(succ (succ (double pred)))))

  let true   = λt: λf: t
  let false  = λt: λf: f
  let nand   = λa: (a λb:(b false true) λb:(b true true))

  let slow   = (Y λslow: λn: (n true λpred:(nand (slow pred) (slow pred))))

  λt: (t
    (slow (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ zero)))))))))))))))))))
    (slow (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ zero)))))))))))))))))))
  )
`;

var code : string = `
  @2(
    $0{$0{$0{$0{
    $0{$0{$0{$0{$0{$0{$0{$0{
    $0{$0{$0{$0{$0{$0{$0{$0{
    $0{$0{$0{$0{$0{$0{$0{$0{
      $2{}
    }}}}}}}}
    }}}}}}}}
    }}}}}}}}
    }}}}
  )
`;

var code : string = lambda_to_optimal(code);
console.log("term: " + code + "\n");

var MEM = read(code);

//var gas = normal(MEM, 0);
var gas = normal_ffi(MEM, 0);

console.log("cost: " + gas);
console.log("norm: " + show_as_lambda(MEM));
console.log("");

console.log(MEM.lnk.size);

// JS =  4m rwts/s
// C  = 56m rwts/s
//
// :)
//
// Will soon test with datatypes... and, then, threads!
