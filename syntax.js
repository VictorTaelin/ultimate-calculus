const {Var, Lam, App, Par, Let, reduce, fresh, copy} = require("./core.js");

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
      var val0 = show(term.val0);
      var val1 = show(term.val1);
      return "[" + val0 + "," + val1 + "]";
    case "Let":
      var nam0 = term.nam0;
      var nam1 = term.nam1;
      var expr = show(term.expr);
      var body = show(term.body);
      return "get [" + nam0 + "," + nam1 + "] = " + expr + "; " + body;
  }
};

// Parser
function parse(code) {
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
      var val0 = parse_term();
      var skip = consume(",");
      var val1 = parse_term();
      var skip = consume("]");
      return Par(val0, val1);
    }
  };

  const parse_let = () => {
    if (match("let")) {
      var skip = consume("[");
      var nam0 = parse_name();
      var skip = consume(",");
      var nam1 = parse_name();
      var skip = consume("]");
      var skip = consume("=");
      var expr = parse_term();
      var skip = consume(";");
      var body = parse_term();
      return Let(nam0, nam1, expr, body);
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

  const parse_env = () => {
    var name = parse_name();
    if (name.length > 0) {
      var term = parse_term();
      env[name] = () => copy(term, env);
      parse_env();
    };
    return env;
  };

  var idx = 0;
  var env = {};
  var nam = {};

  parse_env();

  env._cpys = 0;
  env._rwts = 0;

  return env;
};

module.exports = {show, parse};
