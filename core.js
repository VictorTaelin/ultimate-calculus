// Ultimate Calculus terms are defined by the following grammar:
//   term ::=
//   | {x} term               -- lambda
//   | (term term)            -- application
//   | [term,term]            -- pair
//   | let [x,y] = term; term -- projection
//   | x                      -- variable
//
// Its reduction rules are defined as follows, with `x <- a` standing for global
// name-capture-avoiding substitution:
// 
// (({x}f) a)
// ---------- (app-lam)
// x <- a
// f
// 
// ([A|a,b] c)
// ----------- (app-par)
// let [A|x0,x1] = c; [(a x0),(b x1)]
// 
// (let [A|x0,x1] = a; b c)
// ------------------------ (app-let)
// let [A|x0,x1] = a; (b c)
// 
// let [A|x,y] = {x} f; t
// ---------------------- (let-lam)
// p <- {x0} p
// q <- {x1} q
// x <- [A|x0,x1]
// let [A|x0,x1] = f; t
//
// let [A|x,y] = [B|a,b]; t
// ------------------------ (let-par)
// if A == B then
//   x <- a
//   y <- b
//   t
// else
//   x <- [B0|xA,xB]
//   y <- [B1|yA,yB]
//   let [A|xA,yA] = a; let [A|xB,yB] = b; t
//
// let [A|x0,x1] = let [B|y0,y1] = a; b; c
// --------------------------------------- (let-let)
// let [B|y0,y1] = a; let [A|x0,x1] = b; c

// Terms
const Lam = (name, body)                   => ({ctor: "Lam", name, body});
const App = (func, argm)                   => ({ctor: "App", func, argm});
const Par = (kind, val0, val1)             => ({ctor: "Par", kind, val0, val1});
const Let = (kind, nam0, nam1, expr, body) => ({ctor: "Let", kind, nam0, nam1, expr, body});
const Var = (name)                         => ({ctor: "Var", name});

// Reduces a term once
function reduce(term, env = null) {
  if (!env) env = {_rwts: 0};
  switch (term.ctor) {
    case "Lam":
      var body = reduce(term.body, env);
      return Lam(term.name, body);
    case "App":
      var func = reduce(term.func, env);
      // App-Lam
      if (func.ctor === "Lam") {
        env._rwts++;
        env[func.name] = term.argm;
        return reduce(func.body, env);
      // App-Par
      } else if (func.ctor === "Par") {
        env._rwts++;
        var x0 = fresh(env);
        var x1 = fresh(env);
        var a0 = App(func.val0, Var(x0));
        var a1 = App(func.val1, Var(x1));
        var ki = func.kind;
        return reduce(Let(ki, x0, x1, term.argm, Par(ki, a0, a1)), env);
      } else if (func.ctor === "Let") {
        env._rwts++;
        var done = App(func.body, term.argm);
        var done = Let(func.kind, func.nam0, func.nam1, func.expr, done);
        return reduce(done, env);
      } else {
        var argm = reduce(term.argm, env);
        return App(func, argm);
      }
    case "Par": 
      var kind = term.kind;
      var val0 = reduce(term.val0, env);
      var val1 = reduce(term.val1, env);
      return Par(kind, val0, val1);
    case "Let":
      var kind = term.kind;
      var expr = reduce(term.expr, env);
      // Let-Lam
      if (expr.ctor === "Lam") {
        env._rwts++;
        var n0 = fresh(env);
        var n1 = fresh(env);
        var x0 = fresh(env);
        var x1 = fresh(env);
        env[term.nam0] = Lam(x0, Var(n0));
        env[term.nam1] = Lam(x1, Var(n1));
        env[expr.name] = Par(kind, Var(x0), Var(x1));
        return reduce(Let(kind, n0, n1, expr.body, term.body), env);
      // Let-Par
      } else if (expr.ctor === "Par") {
        env._rwts++;
        if (term.kind === expr.kind) {
          env[term.nam0] = expr.val0;
          env[term.nam1] = expr.val1;
          return reduce(term.body, env);
        } else {
          var x0 = fresh(env);
          var x1 = fresh(env);
          var y0 = fresh(env);
          var y1 = fresh(env);
          env[term.nam0] = Par(expr.kind, Var(x0), Var(x1));
          env[term.nam1] = Par(expr.kind, Var(y0), Var(y1));
          var done = term.body;
          var done = Let(term.kind+"<", x1, y1, expr.val1, done);
          var done = Let(term.kind+">", x0, y0, expr.val0, done);
          return reduce(done, env);
        }
      // Let-Let
      } else if (expr.ctor === "Let") {
        env._rwts++;
        var done = term.body;
        var done = Let(term.kind, term.nam0, term.nam1, expr.body, done);
        var done = Let(expr.kind, expr.nam0, expr.nam1, expr.expr, done);
        return reduce(done, env);
      } else {
        var body = reduce(term.body, env);
        return Let(kind, term.nam0, term.nam1, expr, body);
      }
    case "Var":
      if (env[term.name]) {
        var value = env[term.name];
        delete env[term.name];
        return reduce(value, env);
      } else {
        return term;
      }
  };
};

// Reduces a term to normal form
function normalize(term, env = null) {
  if (!env) env = {_rwts: 0};
  var last_rwts = null;
  while (last_rwts !== env._rwts) {
    last_rwts = env._rwts;
    console.log("pass", show(term));
    term = reduce(term, env);
  };
  return {term, stats: {rewrites: env._wrts}};
};

// Creates a fresh name
function fresh(env) {
  return "x" + (env._size = (env._size || 0) + 1);
};

// Stringifier
function show(term) {
  switch (term.ctor) {
    case "Var":
      return term.name;
    case "Lam":
      var name = term.name;
      var body = show(term.body);
      return "{" + name + "} " + body;
    case "App":
      var func = show(term.func);
      var argm = show(term.argm);
      return "(" + func + " " + argm + ")";
    case "Par":
      var kind = term.kind;
      var val0 = show(term.val0);
      var val1 = show(term.val1);
      return "[" + kind + "|" + val0 + "," + val1 + "]";
    case "Let":
      var kind = term.kind;
      var nam0 = term.nam0;
      var nam1 = term.nam1;
      var expr = show(term.expr);
      var body = show(term.body);
      return "let [" + kind + "|" + nam0 + "," + nam1 + "] = " + expr + "; " + body;
  }
};

// Parser
function parse(code) {
  var idx = 0;

  const skip_spaces = () => {
    while (idx < code.length && /\s/.test(code[idx])) {
      idx++;
    }
  };

  const match = (str) => {
    skip_spaces();
    if (code.slice(idx, idx + str.length) === str) {
      idx += str.length;
      return true;
    }
    return false;
  };

  const consume = (str) => {
    skip_spaces();
    for (var i = 0; i < str.length; ++i) {
      if (code[idx + i] !== str[i]) {
        var found = code.slice(idx, idx+12).replace(/\n/g,"\\n");
        throw "Expected '" + str[i] + "', found '" + found + "...'.";
      }
    }
    idx += str.length;
  };

  const parse_name = () => {
    skip_spaces();
    var nm = "";
    while (idx < code.length && /\w/.test(code[idx])) {
      nm += code[idx++];
    }
    return nm;
  };

  const parse_lam = () => {
    if (match("{")) {
      var name = parse_name();
      var skip = consume("}");
      var body = parse_term();
      return Lam(name, body);
    }
  };

  const parse_app = () => {
    if (match("(")) {
      var func = parse_term();
      var argm = parse_term();
      var skip = consume(")");
      return App(func, argm);
    }
  };

  const parse_par = () => {
    if (match("[")) {
      var kind = parse_name();
      var skip = consume("|");
      var val0 = parse_term();
      var skip = consume(",");
      var val1 = parse_term();
      var skip = consume("]");
      return Par(kind, val0, val1);
    }
  };

  const parse_let = () => {
    if (match("let")) {
      var skip = consume("[");
      var kind = parse_name();
      var skip = consume("|");
      var nam0 = parse_name();
      var skip = consume(",");
      var nam1 = parse_name();
      var skip = consume("]");
      var skip = consume("=");
      var expr = parse_term();
      var skip = consume(";");
      var body = parse_term();
      return Let(kind, nam0, nam1, expr, body);
    }
  };

  const parse_var = () => {
    var name = parse_name();
    if (name.length !== 0) {
      return Var(name);
    }
  };

  const parse_term = () => {
    var term
      =  parse_lam()
      || parse_app()
      || parse_par()
      || parse_let()
      || parse_var();
    return term;
  };

  return parse_term();
};

module.exports = {
  Lam,
  App,
  Par,
  Let,
  Var,
  reduce,
  normalize,
  fresh,
  show,
  parse
};
