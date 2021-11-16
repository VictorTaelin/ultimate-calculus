// Tests
// -----

import {read, lambda_to_optimal, show_as_lambda} from "./syntax.ts"
import {MEM, normal, get_gas} from "./optimal_calculus.ts"

var code : string = `
  let Y      = ((λr:λf:(f (r r f))) (λr:λf:(f (r r f))))

  let succ   = λn: λz: λs: (s n)
  let zero   = λz: λs: z
  let double = (Y λdouble: λn: (n zero λpred:(succ (succ (double pred)))))

  let true   = λt: λf: t
  let false  = λt: λf: f
  let nand   = λa: (a λb:(b false true) λb:(b true true))

  let slow   = (Y λslow: λn: (n true λpred:(nand (slow pred) (slow pred))))

  (slow
    (succ (succ (succ (succ
    (succ (succ (succ (succ
    (succ (succ (succ (succ
    (succ (succ (succ (succ
      zero
    ))))
    ))))
    ))))
    ))))
  )
`;

var code : string = `
  @2(
    $0{$0{$0{$0{$0{$0{$0{$0{
    $0{$0{$0{$0{$0{$0{$0{$0{
    $0{$0{$0{$0{$0{$0{$0{$0{
      $2{}
    }}}}}}}}
    }}}}}}}}
    }}}}}}}}
  )
`;
  
var code : string = lambda_to_optimal(code);
console.log(code);

read(code);
var norm = normal(0);
console.log("cost: " + String(get_gas()));
console.log("norm: " + show_as_lambda(MEM[0]));
