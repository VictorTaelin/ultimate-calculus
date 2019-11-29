const {Var, Lam, App, Par, Let, reduce, fresh, copy} = require("./core.js");

// Stringifier
function show(term) {
  switch (term.tag) {
    case Var: {
      return term.name;
    }
    case Lam: {
      const name = term.name;
      const body = show(term.body);
      return `{${name}} ${body}`;
    }
    case App: {
      const func = show(term.func);
      const argm = show(term.argm);
      return `(${func} ${argm})`;
    }
    case Par: {
      const val0 = show(term.val0);
      const val1 = show(term.val1);
      return `[${val0},${val1}]`;
    }
    case Let: {
      const nam0 = term.nam0;
      const nam1 = term.nam1;
      const expr = show(term.expr);
      const body = show(term.body);
      return `get [${nam0},${nam1}] = ${expr}; ${body}`;
    }
    default:
      return '<unknown term>';
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
    for (let i = 0; i < str.length; ++i) {
      if (code[idx + i] !== str[i]) {
        const found = code.slice(idx, idx + 12).replace(/\n/g,"\\n");
        throw "Expected '" + str[i] + "', found '" + found + "...'.";
      }
    }
    idx += str.length;
  };

  const parse_name = () => {
    skip_spaces();
    let nm = "";
    while (idx < code.length && /\w/.test(code[idx])) {
      nm += code[idx++];
    }
    return nm;
  };

  const parse_lam = () => {
    if (match("{")) {
      const name = parse_name();
      const skip = consume("}");
      const body = parse_term();
      return Lam(name, body);
    }
  };

  const parse_app = () => {
    if (match("(")) {
      const func = parse_term();
      const argm = parse_term();
      const skip = consume(")");
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
    const name = parse_name();
    if (name.length !== 0) {
      return Var(name);
    }
    return null;
  };

  const parse_term = () => {
    const term
      =  parse_lam()
      || parse_app()
      || parse_par()
      || parse_let()
      || parse_var();
    return term;
  };

  const parse_env = () => {
    const name = parse_name();
    if (name.length > 0) {
      const term = parse_term();
      env[name] = () => copy(term, env);
      parse_env();
    };
    return env;
  };

  let idx = 0;
  const env = {};
  const nam = {};

  parse_env();

  env._cpys = 0;
  env._rwts = 0;

  return env;
};

module.exports = {show, parse};
