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

// The Optimal Calculus
// ====================

type MAP<T> = Record<string, T>;

const NIL : number = 0
const LAM : number = 1
const APP : number = 2
const PAR : number = 3
const DP0 : number = 4
const DP1 : number = 5
const VAR : number = 6
const LNK : number = 7

type Col = number
type Tag = number
type Ptr = number

// Utils
// -----

function pad(str : string, len : number) {
  while (str.length < len) {
    str = " " + str;
  }
  return str.slice(-len);
}

// Memory
// ------

var RE0 : Array<Ptr> = [];
var RE1 : Array<Ptr> = [];
var RE2 : Array<Ptr> = [];
var RE3 : Array<Ptr> = [];
var MEM : Array<Ptr> = [];
var GAS : number = 0;
var LIM : number = Infinity;

var MUL_A = Math.pow(2, 4);
var MUL_B = Math.pow(2, 12);

function ptr(tag: Tag, dest: number, col: Col = 0) : Ptr {
  return tag + (col * MUL_A) + (dest * MUL_B);
}

function get_tag(ptr: Ptr) : Tag {
  return ptr & 0xF;
}

function get_col(ptr: Ptr) : Tag {
  return Math.floor(ptr / MUL_A) & 0xFF;
}

function get_dest(ptr: Ptr) : number {
  return Math.floor(ptr / MUL_B);
}

function SET(dest: number, term: Ptr) {
  //if (IS_FREED[dest]) {
    //throw new Error("Setting freed " + dest);
  //}
  MEM[dest] = term;
  switch (get_tag(term)) {
    case VAR: MEM[get_dest(term)+0] = ptr(LNK,dest); break;
    case DP0: MEM[get_dest(term)+0] = ptr(LNK,dest); break;
    case DP1: MEM[get_dest(term)+1] = ptr(LNK,dest); break;
  }
}

function ARG(term: Ptr, idx: number) : Ptr {
  return MEM[get_dest(term) + idx];
}

function alloc(size: number) : number {
  var reuse;
  switch (size) {
    case 0: reuse = RE0.pop(); break;
    case 1: reuse = RE1.pop(); break;
    case 2: reuse = RE2.pop(); break;
    case 3: reuse = RE3.pop(); break;
  }
  if (reuse !== undefined) {
    //console.log("reuse", size, MEM.slice(reuse, reuse + size));
    //for (var k = 0; k < size; ++k) {
      //MEM[reuse + k] = 0;
    //}
    return reuse;
  } else {
    var dest = MEM.length;
    for (var k = 0; k < size; ++k) {
      MEM.push(0);
    }
    return dest;
  }
}

var IS_FREED : any = {};
function free(dest: number, size: number) {
  for (var k = dest; k < dest + size; ++k) {
    IS_FREED[k] = 1;
    MEM[k] = 0;
  }
  switch (size) {
    case 0: RE0.push(dest); break;
    case 1: RE1.push(dest); break;
    case 2: RE2.push(dest); break;
    case 3: RE3.push(dest); break;
  }
}

// Stringification
// ---------------

function show(term: Ptr) : string {
  var names : MAP<string> = {};
  var count = 0;
  var seen : MAP<boolean> = {};
  function name(term: Ptr, depth: number) {
    if (!seen[term]) {
      seen[term] = true;
      switch (get_tag(term)) {
        case LAM:
          if (get_tag(ARG(term,0)) !== NIL) {
            names[ptr(VAR,get_dest(term))] = "x" + (++count);
          }
          name(ARG(term,1), depth + 1);
          break;
        case APP:
          name(ARG(term,0), depth + 1);
          name(ARG(term,1), depth + 1);
          break;
        case PAR:
          name(ARG(term,0), depth + 1);
          name(ARG(term,1), depth + 1);
          break;
        case DP0:
          name(ARG(term,2), depth + 1);
          break;
        case DP1:
          name(ARG(term,2), depth + 1);
          break;
      }
    }
  }
  function go(term: Ptr, stacks: MAP<string>, seen: MAP<number>, depth: number) : string {
    if (seen[term]) {
      return "@";
      //return "(seen:" + Object.keys(seen).length + " | " + "depth:" + depth + ")";
    } else {
      //seen = {...seen, [term]: true};
      //console.log("go", stacks);
      //if (depth > 30) return "(...)";
      switch (get_tag(term)) {
        case LAM:
          var body = go(ARG(term,1), stacks, seen, depth + 1);
          if (get_tag(ARG(term,0)) !== NIL) {
            var name = names[ptr(VAR,get_dest(term))] || "?";
          } else {
            var name = "~";
          }
          return "λ" + name + "." + body;
        case APP:
          var func = go(ARG(term,0), stacks, seen, depth + 1);
          var argm = go(ARG(term,1), stacks, seen, depth + 1);
          return "(" + func + " " + argm + ")"
        case PAR:
          var col = get_col(term);
          if (!stacks[col]) {
            stacks[col] = "";
          }
          //console.log("par", col);
          if (stacks[col] !== undefined && stacks[col].length > 0) {
            if (stacks[col][0] === "0") {
              return go(ARG(term,0), {...stacks,[col]:stacks[col].slice(1)}, seen, depth + 1);
            } else {
              return go(ARG(term,1), {...stacks,[col]:stacks[col].slice(1)}, seen, depth + 1);
            }
          } else {
            var val0 = go(ARG(term,0), stacks, seen, depth + 1);
            var val1 = go(ARG(term,1), stacks, seen, depth + 1);
            return "{" + val0 + " " + val1 + "}"
          }
        case DP0:
          var col = get_col(term);
          return "" + go(ARG(term,2), {...stacks,[col]:"0"+stacks[col]}, seen, depth + 1);
        case DP1:
          var col = get_col(term);
          return "" + go(ARG(term,2), {...stacks,[col]:"1"+stacks[col]}, seen, depth + 1);
        case VAR:
          return names[term] || "^"+String(get_dest(term)) + "<" + show_ptr(MEM[get_dest(term)]) + ">";
        case LNK:
          return "!";
        case NIL:
          return "~";
      }
      return "?(" + get_tag(term) + ")";
    }
  }
  name(term, 0);
  return go(term, {}, {}, 0);
}

function show_tag(tag: Tag) {
  switch (tag) {
    case LAM: return "LAM";
    case APP: return "APP";
    case PAR: return "PAR";
    case DP0: return "DP0";
    case DP1: return "DP1";
    case VAR: return "VAR";
    case LNK: return "LNK";
    case NIL: return "NIL";
  }
}

function show_ptr(ptr: Ptr) {
  return show_tag(get_tag(ptr)) + ":" + get_dest(ptr) + (get_col(ptr) !== 0 ? "|" + get_col(ptr) : "");
}

function show_mem() {
  return MEM.map((x,i) => ("    "+i).slice(-3)+" "+show_ptr(x)).filter((x) => x.indexOf("NIL:0") === -1).join("\n");
}

function debug_mem() : string {
  var cover : any = {};
  var nodes : any = {};
  var count : any = 0;
  for (var i = 0; i < MEM.length; ++i) {
    let tag : any = get_tag(MEM[i]);
    let dest : any = get_dest(MEM[i]);
    switch (tag) {
      case LAM:
        nodes[dest] = "Lam";
        cover[dest+0] = 1;
        cover[dest+1] = 1;
        break;
      case APP:
        nodes[dest] = "App";
        cover[dest+0] = 1;
        cover[dest+1] = 1;
        break;
      case PAR:
        nodes[dest] = "Par";
        cover[dest+0] = 1;
        cover[dest+1] = 1;
        break;
      case DP0:
        nodes[dest] = "Let";
        cover[dest+0] = 1;
        cover[dest+1] = 1;
        cover[dest+2] = 1;
        break;
      case DP1:
        nodes[dest] = "Let";
        cover[dest+0] = 1;
        cover[dest+1] = 1;
        cover[dest+2] = 1;
        break;
    }
  }
  function show_down(ptr : any) {
    switch (get_tag(ptr)) {
      case DP0: return pad("a" + get_dest(ptr),4);
      case DP1: return pad("b" + get_dest(ptr),4);
      case VAR: return pad("x" + get_dest(ptr),4);
      default: return pad("" + get_dest(ptr), 4);
    }
  }
  function show_link(ptr : any) {
    if (get_tag(ptr) === NIL) {
      return pad("~", 4)
    } else {
      return pad(String(get_dest(ptr)), 4);
    }
  }
  var text = "";
  for (var dest = 0; dest < MEM.length; ++dest) {
    var loc = pad(String(dest), 3);
    if (!cover[dest] && MEM[dest]) {
      text += loc + " ? " + pad(show_ptr(MEM[dest]),9) + "\n";
    } else {
      switch (nodes[dest] || 0) {
        case "Lam":
          text += loc + " λ " + show_link(MEM[dest+0]) + " " + show_down(MEM[dest+1]) + "\n";
          break;
        case "App":
          text += loc + " @ " + show_down(MEM[dest+0]) + " " + show_down(MEM[dest+1]) + "\n";
          break;
        case "Par":
          text += loc + " & " + show_down(MEM[dest+0]) + " " + show_down(MEM[dest+1]) + "\n";
          break;
        case "Let":
          text += loc + " $ " + show_down(MEM[dest+2]) + "\n";
          break;
      }
    }
  }
  return text;
}

// Parsing
// -------

function read(code: string): Ptr {
  //PARSING = true;
  var lams  : MAP<number> = {};
  var let0s : MAP<number> = {};
  var let1s : MAP<number> = {};
  var tag0s : MAP<number> = {};
  var tag1s : MAP<number> = {};
  var vars  : Array<[string,number]> = [];

  function link() {
    for (var [var_name, var_dest] of vars) {
      //console.log("link", name);
      var lam = lams[var_name]
      if (lam !== undefined) {
        //console.log("- lam");
        SET(var_dest, ptr(VAR,lam));
      }
      var let0 = let0s[var_name]
      if (let0 !== undefined) {
        //console.log("- let0");
        SET(var_dest, ptr(DP0,let0,tag0s[var_name]||0));
      }
      var let1 = let1s[var_name]
      if (let1 !== undefined) {
        //console.log("- let1");
        SET(var_dest, ptr(DP1,let1,tag1s[var_name]||0));
      }
    }
  }

  function skip() {
    while (code[0] === " " || code[0] === "\n") {
      code = code.slice(1);
    }
  }

  function parse_name() : string {
    skip();
    var name = "";
    while ("a" <= code[0] && code[0] <= "z"
        || "A" <= code[0] && code[0] <= "Z"
        || "0" <= code[0] && code[0] <= "9"
        || "_" === code[0]
        || "~" === code[0]) {
      name += code[0];
      code = code.slice(1);
    }
    return name;
  }

  function parse_term(local: number) : Ptr {
    skip();
    var node = 0;
    switch (code[0]) {
      case "λ": 
        code = code.slice(1);
        node = alloc(2);
        var name = parse_name();
        code = code.slice(1);
        var body = parse_term(node + 1);
        SET(node+0, ptr(NIL,0));
        SET(node+1, body);
        lams[name] = node;
        return ptr(LAM, node);
      case "(":
        code = code.slice(1);
        node = alloc(2);
        var func = parse_term(node + 0);
        var argm = parse_term(node + 1);
        SET(node+0, func);
        SET(node+1, argm);
        skip();
        code = code.slice(1);
        return ptr(APP, node);
      case "{":
        code = code.slice(1);
        if (/[0-9]/.test(code[0])) {
          var num = "";
          while (/[0-9]/.test(code[0])) {
            num += code[0];
            code = code.slice(1);
          }
          var col = 0 + (Number(num) || 0);
        } else {
          var col = 1;
        }
        node = alloc(2);
        var val0 = parse_term(node + 0);
        var val1 = parse_term(node + 1);
        SET(node+0, val0);
        SET(node+1, val1);
        skip();
        code = code.slice(1);
        return ptr(PAR, node, col);
      case "$":
        code = code.slice(1);
        node = alloc(3);
        if (code[0] !== " ") {
          var num = "";
          while (/[0-9]/.test(code[0])) {
            num += code[0];
            code = code.slice(1);
          }
          var col = 0 + (Number(num) || 0);
        } else {
          var col = 1;
        }
        var nam0 = parse_name();
        var nam1 = parse_name();
        skip();
        code = code.slice(1);
        var expr = parse_term(node + 2);
        skip();
        code = code.slice(1);
        var body = parse_term(local);
        SET(node+0, ptr(NIL,0));
        SET(node+1, ptr(NIL,0));
        SET(node+2, expr);
        let0s[nam0] = node;
        tag0s[nam0] = col;
        let1s[nam1] = node;
        tag1s[nam1] = col;
        return body;
      default:
        var name = parse_name();
        var vari = ptr(NIL,0);
        vars.push([name, local]);
        return vari;
    }
  }
  MEM = [ptr(NIL,0)];
  SET(0, parse_term(0));
  link();
  //PARSING = false;
  return MEM[0];
}

// Debug
// -----

function sanity_check() {
  for (var i = 0; i < MEM.length; ++i) {
    //if (MEM[i] !== 0 && MEM[get_dest(MEM[i])] === 0) {
      //throw new Error("Pointing to void at " + i + ".");
    //}
    switch (get_tag(MEM[i])) {
      case VAR:
        if (get_dest(MEM[get_dest(MEM[i])]) !== i) {
          throw new Error("Bad var at " + i + ".");
        }
        break;
      case DP0:
        if (get_dest(MEM[get_dest(MEM[i])]) !== i) {
          throw new Error("Bad dp0 at " + i + ".");
        }
        break;
      case DP1:
        if (get_dest(MEM[get_dest(MEM[i])+1]) !== i) {
          throw new Error("Bad dp1 at " + i + ".");
        }
        break;
      case LAM:
        if (MEM[get_dest(MEM[i])+1] === 0) {
          throw new Error("Lambda pointing to nil body at " + i + ".");
        }
      //case PAR:
        //if (ARG(MEM[i],0) === MEM[i] || ARG(MEM[i],1) === MEM[i]) {
          //throw new Error("Self-referential pair at " + i + ".");
        //}
    }
  }
}

// Garbage Collection
// ------------------

// This function works fine. The problem is: when to call it? We could call it
// when a lambda with an unused variable is applied to an argument, i.e.,
// `((λx. a) b)` would erase `b` if `x` is not used (i.e., NIL). The problem is,
// not always `x` will be NIL if not used; it could be a fan node with two NILs
// instead, for example. So, doing that would not catch all situations where
// we'd want to call collect(). So I'd rather just not call it at all, and write
// a global garbage collector instead.
function collect(term: Ptr, host: null | number) {
  switch (get_tag(term)) {
    case LAM:
      if (get_tag(ARG(term,0)) !== NIL) {
        SET(get_dest(ARG(term,0)), ptr(NIL,0));
      }
      collect(ARG(term,1), get_dest(term) + 1);
      free(get_dest(term), 2);
      break;
    case APP:
      collect(ARG(term,0), get_dest(term) + 0);
      collect(ARG(term,1), get_dest(term) + 1);
      free(get_dest(term), 2);
      break;
    case PAR:
      //console.log("par");
      collect(ARG(term,0), get_dest(term) + 0);
      collect(ARG(term,1), get_dest(term) + 1);
      free(get_dest(term), 2);
      if (host) {
        SET(host, ptr(NIL,0));
      }
      break;
    case DP0:
      SET(get_dest(term) + 0, ptr(NIL,0));
      if (host) {
        free(host, 1);
      }
      break;
    case DP1:
      SET(get_dest(term) + 1, ptr(NIL,0));
      if (host) {
        free(host, 1);
      }
      break;
    case VAR:
      SET(get_dest(term) + 0, ptr(NIL,0));
      if (host) {
        free(host, 1);
      }
      break;
  }
}

// Reduction
// ---------

function subst(lnk: Ptr, val: Ptr) {
  if (get_tag(lnk) !== NIL) {
    SET(get_dest(lnk), val);
  } else {
    // Attempting to GC here is futile. See note above.
    collect(val, null);
  }
}

var depth = 0;
function reduce(term: Ptr, host: number, depth: number) : Ptr {
  //console.log("REDUCE", depth, show_ptr(term));
  //console.log(view_mem());
  switch (get_tag(term)) {
    case APP:
      let func = reduce(ARG(term, 0), get_dest(term) + 0, depth + 1);
      switch (get_tag(func)) {
        // (λx.b a)
        // --------- APP-LAM
        // x <- a
        case LAM: {
          if (GAS >= LIM) {
            return term;
          } else {
            ++GAS;
          }
          //console.log("[app-lam]", get_dest(term), get_dest(func));
          //sanity_check();
          subst(ARG(func,0), ARG(term,1));
          var done = ARG(func, 1);
          free(get_dest(term), 2);
          free(get_dest(func), 2);
          SET(host, done);
          //sanity_check();
          return reduce(done, host, depth + 1);
          //return ARG(func, 1);
        }
        // ({A a b} c)
        // ----------------- APP-PAR
        // let {A x0 x1} = c
        // {A (a x0) (b x1)}
        case PAR: {
          if (GAS >= LIM) {
            return term;
          } else {
            ++GAS;
          }
          //console.log("[app-par]", get_dest(term), get_dest(func));
          //sanity_check();
          var let0 = alloc(3);
          var app0 = alloc(2);
          var app1 = alloc(2);
          var par0 = alloc(2);
          SET(let0+2, ARG(term, 1));
          SET(app0+0, ARG(func, 0));
          SET(app0+1, ptr(DP0, let0, get_col(func)));
          SET(app1+0, ARG(func, 1));
          SET(app1+1, ptr(DP1, let0, get_col(func)));
          SET(par0+0, ptr(APP, app0));
          SET(par0+1, ptr(APP, app1));
          var done = ptr(PAR, par0, get_col(func));
          free(get_dest(term), 2);
          free(get_dest(func), 2);
          SET(host, done);
          //sanity_check();
          return done;
        }
      }
      break;
    case DP0:
    case DP1:
      let expr = reduce(ARG(term, 2), get_dest(term) + 2, depth + 1);
      switch (get_tag(expr)) {
        // let {A r s} = λx. f
        // ------------------- LET-LAM
        // r <- λx0. f0
        // s <- λx1. f1
        // x <- {A x0 x1}
        // let {A f0 f1} = f
        // ~
        case LAM: {
          if (GAS >= LIM) {
            return term;
          } else {
            ++GAS;
          }
          //console.log("[let-lam]", get_dest(term), get_dest(expr));
          //sanity_check();
          var lam0 = alloc(2);
          var lam1 = alloc(2);
          var par0 = alloc(2);
          var let0 = alloc(3);
          SET(lam0+1, ptr(DP0, let0, get_col(term)));
          SET(lam1+1, ptr(DP1, let0, get_col(term)));
          SET(par0+0, ptr(VAR, lam0));
          SET(par0+1, ptr(VAR, lam1));
          SET(let0+2, ARG(expr, 1));
          subst(ARG(term,0), ptr(LAM, lam0));
          subst(ARG(term,1), ptr(LAM, lam1));
          //console.log(debug_mem());
          subst(ARG(expr,0), ptr(PAR, par0, get_col(term)));
          var done = get_tag(term) === DP0 ? ptr(LAM,lam0) : ptr(LAM,lam1);
          free(get_dest(term), 3);
          free(get_dest(expr), 2);
          SET(host, done);
          //sanity_check();
          return reduce(done, host, depth + 1);
        }
        // let {A x y} = {B a b}
        // --------------------- LET-PAR
        // if A == B then
        //   x <- a
        //   y <- b
        //   ~
        // else
        //   x <- {B xA xB}
        //   y <- {B yA yB}
        //   let {A xA yA} = a
        //   let {A xB yB} = b
        //   ~
        case PAR: {
          if (GAS >= LIM) {
            return term;
          } else {
            ++GAS;
          }
          //console.log("[let-par]", get_dest(term), get_dest(expr));
          if (get_col(term) === get_col(expr)) {
            //sanity_check();
            subst(ARG(term,0), ARG(expr,0));
            subst(ARG(term,1), ARG(expr,1));
            var done = get_tag(term) === DP0 ? ARG(expr,0) : ARG(expr,1);
            free(get_dest(term), 3);
            free(get_dest(expr), 2);
            SET(host, done);
            //sanity_check();
            return reduce(done, host, depth + 1);
          } else {
            //sanity_check();
            var par0 = alloc(2);
            var par1 = alloc(2);
            var let0 = alloc(3);
            var let1 = alloc(3);
            SET(par0+0, ptr(DP0,let0,get_col(term)));
            SET(par0+1, ptr(DP0,let1,get_col(term)));
            SET(par1+0, ptr(DP1,let0,get_col(term)));
            SET(par1+1, ptr(DP1,let1,get_col(term)));
            SET(let0+2, ARG(expr,0));
            SET(let1+2, ARG(expr,1));
            subst(ARG(term,0), ptr(PAR,par0,get_col(expr)));
            subst(ARG(term,1), ptr(PAR,par1,get_col(expr)));
            var done = get_tag(term) === DP0 ? ptr(PAR,par0,get_col(expr)) : ptr(PAR,par1,get_col(expr));
            free(get_dest(term), 3);
            free(get_dest(expr), 2);
            SET(host, done);
            //sanity_check();
            return done;
          }
        }
      }
      break;
  }
  return term;
}

function normal(term: Ptr, host: number) : Ptr {
  var seen : MAP<boolean> = {};
  function go(term: Ptr, host: number) : Ptr {
    //console.log("normal", show(term));
    if (seen[get_dest(term)]) {
      return term;
    } else {
      term = reduce(term, host, 0);
      seen[get_dest(term)] = true;
      switch (get_tag(term)) {
        case LAM:
          SET(get_dest(term) + 1, go(MEM[get_dest(term) + 1], get_dest(term) + 1));
          return term;
        case APP:
          SET(get_dest(term) + 0, go(MEM[get_dest(term) + 0], get_dest(term) + 0));
          SET(get_dest(term) + 1, go(MEM[get_dest(term) + 1], get_dest(term) + 1));
          return term;
        case PAR:
          SET(get_dest(term) + 0, go(MEM[get_dest(term) + 0], get_dest(term) + 0));
          SET(get_dest(term) + 1, go(MEM[get_dest(term) + 1], get_dest(term) + 1));
          return term;
        case DP0:
          SET(get_dest(term) + 2, go(MEM[get_dest(term) + 2], get_dest(term) + 2));
          return term;
        case DP1:
          SET(get_dest(term) + 2, go(MEM[get_dest(term) + 2], get_dest(term) + 2));
          return term;
        default:
          return term;
      }
    }
  }
  return go(term, host);
}

// Tests
// -----

import {lambda_to_optimal} from "./lambda_to_optimal.ts"

var code : string = `
  let Y      = ((λr. λf. (f (r r f))) (λr. λf. (f (r r f))))

  let succ   = λn. λz. λs. (s n)
  let zero   = λz. λs. z
  let double = (Y λdouble. λn. (n zero λpred.(succ (succ (double pred)))))

  let true   = λt. λf. t
  let false  = λt. λf. f
  let nand   = λa. (a λb.(b false true) λb.(b true true))

  let slow   = (Y λslow. λn. (n true λpred.(nand (slow pred) (slow pred))))

  (slow
    (succ (succ
    (succ (succ (succ (succ
    (succ (succ (succ (succ
    (succ (succ (succ (succ
    (succ (succ (succ (succ
      zero
    ))))
    ))))
    ))))
    ))))
    ))
  )
`;

var code : string = lambda_to_optimal(code);

var term = read(code);

var norm = normal(MEM[0],0);
console.log("cost: " + String(GAS));
console.log("norm: " + show(MEM[0]));


