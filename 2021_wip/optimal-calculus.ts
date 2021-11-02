// late 2021 version

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

// Memory
// ------

var MEM : Array<Ptr> = [];

function ptr(tag: Tag, dest: number, col: Col = 0) : Ptr {
  return tag | (col << 4) | (dest << 8);
}

function get_tag(ptr: Ptr) : Tag {
  return ptr & 0xF;
}

function get_col(ptr: Ptr) : Tag {
  return (ptr >>> 4) & 0xF;
}

function get_dest(ptr: Ptr) : number {
  return ptr >>> 8;
}

function SET(dest: number, term: Ptr) {
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
  for (var k = 0; k < size; ++k) {
    MEM.push(0);
  }
  return MEM.length - size;
}

function free(dest: number, size: number) {
  //for (var k = dest; k < dest + size; ++k) {
    //MEM[k] = 0;
  //}
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
          names[ptr(VAR,get_dest(term))] = "x" + (++count);
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
  function go(term: Ptr, stack: string, depth: number) : string {
    //if (depth > 50) return "(...)";
    switch (get_tag(term)) {
      case LAM:
        var body = go(ARG(term,1), stack, depth + 1);
        return "λ" + (names[ptr(VAR,get_dest(term))]||"?") + "." + body;
      case APP:
        var func = go(ARG(term,0), stack, depth + 1);
        var argm = go(ARG(term,1), stack, depth + 1);
        return "(" + func + " " + argm + ")"
      case PAR:
        if (stack.length > 0) {
          if (stack[0] === "0") {
            return go(ARG(term,0), stack.slice(1), depth + 1);
          } else {
            return go(ARG(term,1), stack.slice(1), depth + 1);
          }
        } else {
          var val0 = go(ARG(term,0), stack, depth + 1);
          var val1 = go(ARG(term,1), stack, depth + 1);
          return "{" + val0 + " " + val1 + "}"
        }
      case DP0:
        return "" + go(ARG(term,2), "0"+stack, depth + 1);
      case DP1:
        return "" + go(ARG(term,2), "1"+stack, depth + 1);
      case VAR:
        return names[term] || "^";
      case LNK:
        return "!";
      case NIL:
        return "~";
    }
    return "?(" + get_tag(term) + ")";
  }
  name(term, 0);
  return go(term, "", 0);
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
  return MEM.map((x,i) => ("    "+i).slice(-2)+" "+show_ptr(x)).filter((x) => x.indexOf("NIL:0") === -1).join("\n");
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
    for (var [name,vur] of vars) {
      //console.log("link", name);
      var lam = lams[name]
      if (lam !== undefined) {
        //console.log("- lam");
        SET(vur + 0, ptr(VAR,lam));
      }
      var let0 = let0s[name]
      if (let0 !== undefined) {
        //console.log("- let0");
        SET(vur + 0, ptr(DP0,let0,tag0s[name]||0));
      }
      var let1 = let1s[name]
      if (let1 !== undefined) {
        //console.log("- let1");
        SET(vur + 0, ptr(DP1,let1,tag0s[name]||0));
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
        || "_" == code[0]) {
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
        skip();
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
          var col = Number(code[0]);
          code = code.slice(1);
        } else {
          var col = 0;
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
          var col = Number(code[0]) || 0;
          code = code.slice(1);
        } else {
          var col = 0;
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
    }
  }
}

// Reduction
// ---------

function reduce(term: Ptr) : Ptr {
  switch (get_tag(term)) {
    case APP:
      let func = reduce(ARG(term, 0));
      switch (get_tag(func)) {
        // (λx.b a)
        // --------- APP-LAM
        // x <- a
        case LAM: {
          //console.log("<<app-lam>>", get_dest(term), get_dest(func));
          //sanity_check();
          SET(get_dest(ARG(func,0)), ARG(term, 1));
          var done = ARG(func, 1);
          free(get_dest(term), 2);
          free(get_dest(func), 2);
          //sanity_check();
          return reduce(done);
          //return ARG(func, 1);
        }
        // ({A a b} c)
        // ----------------- APP-PAR
        // let {A x0 x1} = c
        // {A (a x0) (b x1)}
        case PAR: {
          //log("<<app-par>>");
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
          //sanity_check();
          return done;
        }
      }
      break;
    case DP0:
    case DP1:
      let expr = reduce(ARG(term, 2));
      switch (get_tag(expr)) {
        // let {A r s} = λx. f
        // ------------------- LET-LAM
        // r <- λx0. f0
        // s <- λx1. f1
        // x <- {A x0 x1}
        // let {A f0 f1} = f
        // ~
        case LAM: {
          //log("<<let-lam>>");
          //sanity_check();
          var lam0 = alloc(2);
          var lam1 = alloc(2);
          let par0 = alloc(2);
          let let0 = alloc(3);
          SET(get_dest(ARG(term,0)), ptr(LAM, lam0));
          SET(get_dest(ARG(term,1)), ptr(LAM, lam1));
          SET(get_dest(ARG(expr,0)), ptr(PAR, par0, get_col(term)));
          SET(lam0+1, ptr(DP0, let0, get_col(term)));
          SET(lam1+1, ptr(DP1, let0, get_col(term)));
          SET(par0+0, ptr(VAR, lam0));
          SET(par0+1, ptr(VAR, lam1));
          SET(let0+2, ARG(expr,1));
          var done = get_tag(term) === DP0 ? ptr(LAM,lam0) : ptr(LAM,lam1);
          free(get_dest(term), 3);
          free(get_dest(expr), 2);
          //sanity_check();
          return reduce(done);
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
          //log("<<let-par>>");
          if (get_col(term) === get_col(expr)) {
            SET(get_dest(ARG(term,0)), ARG(expr,0));
            SET(get_dest(ARG(term,1)), ARG(expr,1));
            var done = get_tag(term) === DP0 ? ARG(expr,0) : ARG(expr,1);
            free(get_dest(term), 3);
            free(get_dest(expr), 2);
            return reduce(done);
          } else {
            var par0 = alloc(2);
            var par1 = alloc(2);
            var let0 = alloc(3);
            var let1 = alloc(3);
            SET(get_dest(ARG(term,0)), ptr(PAR,par0,get_col(expr)));
            SET(get_dest(ARG(term,1)), ptr(PAR,par1,get_col(expr)));
            SET(par0+0, ptr(DP0,let0,get_col(term)));
            SET(par0+1, ptr(DP0,let1,get_col(term)));
            SET(par1+0, ptr(DP1,let0,get_col(term)));
            SET(par1+1, ptr(DP1,let1,get_col(term)));
            SET(let0+2, ARG(expr,0));
            SET(let1+2, ARG(expr,1));
            var done = get_tag(term) === DP0 ? ptr(PAR,par0,get_col(expr)) : ptr(PAR,par1,get_col(expr));
            free(get_dest(term), 3);
            free(get_dest(expr), 2);
            return done;
          }
        }
      }
      break;
  }
  return term;
}

function normal(term: Ptr) : Ptr {
  var seen : MAP<boolean> = {};
  function go(term: Ptr) : Ptr {
    //console.log("normal", show(term));
    if (seen[term]) {
      return term;
    } else {
      seen[term] = true;
      term = reduce(term);
      switch (get_tag(term)) {
        case LAM:
          SET(get_dest(term) + 1, go(MEM[get_dest(term) + 1]));
          return term;
        case APP:
          SET(get_dest(term) + 0, go(MEM[get_dest(term) + 0]));
          SET(get_dest(term) + 1, go(MEM[get_dest(term) + 1]));
          return term;
        case PAR:
          SET(get_dest(term) + 0, go(MEM[get_dest(term) + 0]));
          SET(get_dest(term) + 1, go(MEM[get_dest(term) + 1]));
          return term;
        case DP0:
          SET(get_dest(term) + 2, go(MEM[get_dest(term) + 2]));
          return term;
        case DP1:
          SET(get_dest(term) + 2, go(MEM[get_dest(term) + 2]));
          return term;
        default:
          return term;
      }
    }
  }
  return go(term);
}

// Tests
// -----

var term = read(`
  (
    λf. λx. $1 f0 f1 = f; $1 f2 f3 = f0; $1 f4 f5 = f1; (f2 (f3 (f4 (f5 x))))
    λg. λy. $3 g0 g1 = g; (g0 (g1 y))
  )`);
sanity_check();

//console.log(show_mem());
console.log(show(term));

SET(0, normal(MEM[0]));
SET(0, normal(MEM[0]));
SET(0, normal(MEM[0]));
SET(0, normal(MEM[0]));

//console.log("normal", show(MEM[0]));

console.log(show_mem());
console.log(show(MEM[0]));
