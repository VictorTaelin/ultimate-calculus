The Ultimate Calculus
=====================

An optimal, **full** λ-calculus evaluator that doesn't rely on interaction
combinators and can be implemented in [150 lines](core.js).

Usage
-----

Install it with:

```
npm i -g ultimate-calculus
```

To evaluate an Ultimate Calculus term:

```
echo "({g} {y} let [A| g0, g1] = g; (g0 (g1 y)) {x} x)" >> main.ult
ult main.ult
```

To evaluate a Lambda Calculus term:

```
echo "({f}{x}(f (f x)) {f}{x}(f (f x)))" >> main.lam
ult main.lam
```

You can also use it as a library. Check `example.js`.

Wait, what?
-----------

It has been years since I started trying to implement a fast evaluator for
λ-calculus terms. After an extensive search, I judged the best solution to be
the ["abstract algorithm"](https://medium.com/@maiavictor/solving-the-mystery-behind-abstract-algorithms-magical-optimizations-144225164b07),
which compiles λ-terms to interaction nets, performes reductions, and then
decompiles back. It is fast and allows us to do some neat optimizations like
runtime fusion, but it has two main problems:

- It is only practical for a subset of the λ-calculus. That's because of the
  slow book-keeping mechanism that is necessary to evaluate certain λ-terms
  such as `(λs.λz.(s (s z)) λs.λz.(s (s z)))` soundly.

- Implementing interaction-net evaluation and compilation is annoying. While
  the implementation is [short](https://github.com/MaiaVictor/Elementary-Affine-Net-legacy/blob/master/javascript/ea-net.js),
  its massively parallel, mutable nature makes it hard to reason about, and
  awkward to implement in pure functional languages.

The Ultimate Calculus is a **superset** of the λ-calculus that can be fully
implemented in 150 lines of idiomatic Haskell. With it, you can still perform
optimal, parallel, O(1) reductions by manually decorating your λ-terms with
explicit duplications. If you don't, though, the algorithm gracefully falls
back to traditional sharing techniques, allowing you to have full λ-terms.

How it works?
-------------

The Ultimate Calculus works by first extending the λ-calculus with pairs and
`let`, which is very common, and then further extending it in two unusual ways:
first, by allowing λ-bound variables to occur outside of their scopes, and
second, by adding reduction rules to two undefined cases: "applying a pair to a
value" and "projecting the elements of a lambda". And that's it.

While those extensions sound "heretic" since they remove scope boundaries and
let us compute with intermediate values that aren't "real λ-terms", those terms
eventually "cancel out": when the computation completes, we get a normal λ-term
back. In a way, that is similar to how one must go outside the scope of real
numbers to have solutions to all single-variable polynomials. While both things
sound intuitively crazy, they're still mathematically meaningful.

The Ultimate Calculus is very similar to another system I published some time
ago, the [Symmetric Interaction Calculus](https://medium.com/@maiavictor/the-abstract-calculus-fe8c46bcf39c),
which started from the observation that interaction nets can be viewed as a
syntax for a λ-calculus superset where variables can scape their scopes. The
problem is that this system was still linear, so it couldn't be used for the
evaluation of arbitrary λ-terms. The perfect calculus allows variables to occur
more than once, giving us two copying options: with explicit duplications,
which allows us to explore optimal reductions, or with non-linear variables,
which falls back to (unspecified) traditional sharing techniques. 

Note this is not a solution to the problem of evaluating full λ-calculus terms
on interaction nets. It is merely a middle ground between interaction nets and
textual calculi, allowing you to have a little bit of both, with the benefit of
being implementable in traditional functional languages with a very small
amount of code.

Specification
-------------

Ultimate calculus terms are defined by the following grammar: 

```haskell
term ::=
| {x} term               -- lambda
| (term term)            -- application
| [term,term]            -- pair
| let [x,y] = term; term -- projection
| x                      -- variable
```

Its reduction rules are the following:


```haskell
(({x}f) a)
---------- (app-lam)
x <- a
f

([A|a,b] c)
----------- (app-par)
let [A|x0,x1] = c; [(a x0),(b x1)]

(let [A|x0,x1] = a; b c)
------------------------ (app-let)
let [A|x0,x1] = a; (b c)

let [A|r,s] = {x} f; t
---------------------- (let-lam)
r <- {x0} f0
s <- {x1} f1
x <- [A|x0,x1]
let [A|f0,f1] = f; t

let [A|x,y] = [B|a,b]; t
------------------------ (let-par)
if A == B then
  x <- a
  y <- b
  t
else
  x <- [B0|xA,xB]
  y <- [B1|yA,yB]
  let [A|xA,yA] = a; let [A|xB,yB] = b; t

let [A|x0,x1] = let [B|y0,y1] = a; b; c
--------------------------------------- (let-let)
let [B|y0,y1] = a; let [A|x0,x1] = b; c
```

Here, `x <- a` stands for global, capture-avoiding substitution of `x` by `a`.
As long as variables only occur once, all of those reduction rules are `O(1)`,
since they only perform a direct substitution of constructors and a single
pointer swapping. When variables are used more than once, they require a deep
copy of a term, replacing its variables with fresh names. That copy can then use
alternative sharing strategies such as closures or just direct copies.  This
allows us to maintain full λ-calculus compatibility.

The `let-lam` rule, which performs the "pair projection" in a lambda is key for
optimal reductions, since it splits the lambda in two separate, but "connected"
terms. This allows us to perform a lazy, granular copy of them, which, in turn,
allows us to express optimal sharing with careful placement of `let`s. Note that
it *can't* be used indiscriminately to copy values, since using `let` to copy a
term which itself has a `let` or a `pair` will be unsound w.r.t expected
λ-calculus semantics. In other words, `let` should be either added carefuly, or
by a compiler when it knows it is safe to do so. Of course, nothing prevents you
from just using the Ultimate Calculus as the reference, in which case you can
just ignore the expected λ-calculus semantics.

Summary
-------

If you want to implement an interpreter or evaluator for a functional language
or the λ-calculus, please consider using the Ultimate Calculus as a fundation
or compilation target. It is very simple to implement and can be drastically
faster than traditional reduction strategies such as Bruijn substitution or
even HOAS with careful placement of `let`s.
