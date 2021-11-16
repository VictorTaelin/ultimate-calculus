```
// About scope violations
// ----------------------
//
// The optimal calculus is, essentially, an optimized storage format for
// interaction net nodes of the sharing graphs used on optimal evaluators of the
// λ-calculus. The main optimization is that lambdas and application nodes store
// only two pointers, skipping the pointer to their own parents. This change
// requires us to 
//
// Scope violations are unavoidable when lazy copying lambdas. For example,
// consider the following reduction:
//
// let f = λx.(+ x 1); [(f 10) (f 20)] ~>
// let f = {x0 x1}; [(λx0.f 10) (λx1.f 20)] ~>
// [(λx0.x0 10) (λx1.x1 20)] ~>
// [10 20]
//
// Notice that, for a brief moment, the x0 and y0 variables bound by the two
// partially copied lambdas lived outside their scopes. That is unavoidable if
// we want optimal sharing (avoid duplicated computation) inside binders. This
// raises a problem when it comes to evaluation order, though. Consider the
// following reduction:
//
//   (t 1 (λt.0 λa.λb.a)) ~>
//   (λa.λb.a 1 0) ~>
//   1
//
// In this case, a recursive evaluator will pass through the `(t 1)`
// application, and apply `λt.0` to `λa.λb.a`, resulting in `0`, and replacing
// the earlier `t` by `λa.λb.a`. And that's the problem: the evaluator will not
// go back to `(λa.λb.a 1 0)`, so it will not reach normal form. We need to call
// normalize() again for that to happen. On interaction nets, that isn't the
// case, because the `λt.0` node has a pointer to the application node where its
// variable is used, so it can go back. This pointer doesn't exist in the
// optimal calculus.
//
// In practice, though, this situation shouldn't arise very often, and we can
// combine garbage-collection passes with normalization passes, until all terms
// are reduced.
// 
// About garbage collection
// ------------------------
// 
// Garbage collection is triggered when a value goes out of scope. For example:
//
// (λa.λb.b BIG b)
//
// This collects BIG, because it goes out of scope (since the lambda doesn't use
// the variable it would be bound to). The garbage collector will, though, stop
// at fan nodes, so, if the value is shared, it won't be collected. This can
// lead to memory leaks, though. For example, consider this term:
//
// λx.(λa.λb.b λt.(x x) λk.k)
//
// After one reduction, it becomes:
//
// λx.(λb.b λk.k)
//
// And the `λt.(x x)` sub-term will be freed, because `λa` is unbound. But now
// the `λx` lambda will be bound to a fan node with two erasure nodes, NOT an
// erasure node directly! So, if `λx` is applied to something, that thing won't
// be garbage collected, and we'll have a memory leak. Simpler visualization:
//
// ((λa. λb. let {x,y} = a; b) BIG λk.k)
// 
// Here, BIG will never be collected, because λa is not bound to an erasure
// node, but to a fan node that copies its argument, and then erases it, twice.
// In order to be garbage-free, we'd need to evaluate arguments eagerly, but
// then we'd waste a lot of computation and lose lazy evaluation. As such, we do
// let memory leaks occur in these cases, and supplement with a global garbage
// collector, but it is extremely efficient since most of the garbage is
// collected preemptively.
//
// Note also that the adoption of equational-notation rewrite nodes counter this
// problem very well. For example, consider the following function:
//
// let fn = λ(b:Bool). case b { true: "BIG_STRING", false: "cat" }
// fn(false)
//
// If we compiled that program to λ-encodings, we'd get the following:
//
// (λb.(b "BIG_STRING" "cat"))(λt.λf.f) ~>
// (λt.λf.f "BIG_STRING" "cat") ~>
// (λf.f "cat") ~>
// "cat"
//
// But, while doing so, "BIG_STRING" would be stuck on memory as garbage. This
// is a problem when we λ-encode everything: pattern-matching leaves a lot of
// garbage. But if we, instead, represented constructors as interaction net
// nodes, and expressed `fn` in the equational notation:
//
// fn true  = "BIG_STRING"
// fn false = "cat"
//
// Then we'd have the following, direct reduction:
//
// (fn false) ~>
// "cat"
```
