var pc = require("./index.js");

// Applies not 4b times
const many_nots = `
  true        {t} {f} t
  false       {t} {f} f
  not         {b} {t} {f} ((b f) t)
  mul         {a} {b} {s} (a (b s))
  nZ          {s} {z} z
  nS          {n} {s} {z} let [sa,sb] = s; (sa ((n sb) z))
  1n          {s} {z} (s z)
  2n          {s} {z} let [sa,sb] = s; (sa (sb z))
  4n          ((mul 2n) 2n)
  16n         ((mul 4n) 4n)
  256n        ((mul 16n) 16n)
  65536n      ((mul 256n) 256n)
  4294967296n ((mul 65536n) 65536n)
  main        ((4294967296n not) true)
`;

// Doubles a Nat recursively
const recursion = `
  zero   {s} {z} z
  succ   {n} {s} {z} (s n)
  double {n} ((n {pred}(succ (succ (double pred)))) zero)
  main   (double (succ (succ zero)))
`;

// Performs a computation that would require inet book-keeping ("oracle")
const full_lambda = `
  c2   {s} {z} (s (s z))
  main (c2 c2)
`;

// An unscoped duplication example
const unscoped = `
  foo {x}{t}((t x) x)
  bar {k}((k u) {u}{y}y)
  main (foo bar)
`;

const run_example = (name, example) => {
  var env = pc.syntax.parse(example);
  console.log("Running", name);
  console.log("- norm:", pc.syntax.show(pc.core.reduce(env.main(), env)));
  console.log("- rwts:", env._rwts);
  console.log("- cpys:", env._cpys);
};

run_example("recursion", recursion);
run_example("many_nots", many_nots);
run_example("full_lambda", full_lambda);
run_example("unscoped", unscoped);
