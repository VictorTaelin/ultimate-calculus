function Lam(name: any, body: any): any {
  return {ctor: "Lam", name, body};
}

function App(func: any, argm: any): any {
  return {ctor: "App", func, argm};
}

function Var(name: any): any {
  return {ctor: "Var", name};
}

function Ctr(func: any, args: any) {
  return {ctor: "Ctr", func, args};
}

function Cal(func: any, args: any) {
  return {ctor: "Cal", func, args};
}

function Dup(kind: any, nam0: any, nam1: any, expr: any, body: any): any {
  return {ctor: "Dup", kind, nam0, nam1, expr, body};
}

// Parses a code
function parse(code: any): any {
  var idx = 0;

  const skip_spaces = () : any => {
    while (idx < code.length && /\s/.test(code[idx])) {
      idx++;
    }
  };

  const match = (str: any) : any => {
    skip_spaces();
    if (code.slice(idx, idx + str.length) === str) {
      idx += str.length;
      return true;
    }
    return false;
  };

  const consume = (str: any) : any => {
    skip_spaces();
    for (var i = 0; i < str.length; ++i) {
      if (code[idx + i] !== str[i]) {
        var found = code.slice(idx, idx+12).replace(/\n/g,"\\n");
        throw "Expected '" + str[i] + "', found '" + found + "...'.";
      }
    }
    idx += str.length;
  };

  const parse_name = () : any => {
    skip_spaces();
    var nm = "";
    while (idx < code.length && /[a-zA-Z0-9_.]/.test(code[idx])) {
      nm += code[idx++];
    }
    return nm;
  };

  const parse_lam = () : any => {
    if (match("λ")) {
      var name = parse_name();
      var skip = consume(":");
      var body = parse_term();
      return Lam(name, body);
    }
  };

  const parse_app = () : any => {
    if (match("(")) {
      var func = parse_term();
      while (!match(")")) {
        var argm = parse_term();
        var func = App(func, argm);
      }
      return func;
    }
  };

  const parse_let = () : any => {
    if (match("let")) {
      var name = parse_name();
      var skip = consume("=");
      var expr = parse_term();
      //var skip = consume(";");
      var body = parse_term();
      return App(Lam(name, body), expr);
    }
  };

  const parse_ctr = () : any => {
    if (match("$")) {
      var func = parse_name();
      var skip = consume("{");
      var args = [];
      while (!match("}")) {
        args.push(parse_term());
      }
      return {ctor: "Ctr", func, args};
    }
  };

  const parse_cal = () : any => {
    if (match("@")) {
      var func = parse_name();
      var skip = consume("(");
      var args = [];
      while (!match(")")) {
        args.push(parse_term());
      }
      return {ctor: "Cal", func, args};
    }
  };

  const parse_var = () : any => {
    var name = parse_name();
    if (name.length !== 0) {
      return Var(name);
    }
  };

  const parse_term = () : any => {
    var term
      =  parse_lam()
      || parse_app()
      || parse_let()
      || parse_ctr()
      || parse_cal()
      || parse_var();
    return term;
  };

  return parse_term();
};

function compile(term: any): any {
  var vars = 0;
  var lets = 0;

  function nth_name(n: any): any {
    var str = "";
    ++n;
    while (n > 0) {
      --n;
      str += String.fromCharCode(97 + n % 26);
      n = Math.floor(n / 26);
    }
    return str;
  };

  function go0(term: any, lams: any): any {
    switch (term.ctor) {
      case "Lam":
        var lamb = Lam(nth_name(vars++), null);
        var lams = {...lams, [term.name]: lamb};
        lamb.uses = 0;
        lamb.body = go0(term.body, lams);
        return lamb;
      case "App":
        var func = go0(term.func, lams);
        var argm = go0(term.argm, lams);
        return App(func, argm);
      case "Ctr":
        var func = term.func;
        var args = term.args.map((x:any) => go0(x, lams));
        return Ctr(func, args);
      case "Cal":
        var func = term.func;
        var args = term.args.map((x:any) => go0(x, lams));
        return Cal(func, args);
      case "Var":
        return Var(lams[term.name].name + (lams[term.name].uses++));
    }
  };

  function go1(term: any): any {
    switch (term.ctor) {
      case "Lam":
        var body = go1(term.body);
        if (term.uses > 1) {
          for (var i = 0; i < term.uses - 1; ++i) {
            var nam0 = term.name+(i*2+0);
            var nam1 = term.name+(i*2+1);
            var expr = Var(term.name + (i === term.uses-2 ? "" : (term.uses+i)));
            body = Dup(lets++, nam0, nam1, expr, body);
          };
        } else if (term.uses === 1) {
          term.name = term.name + "0";
        } else {
          term.name = "_";
        };
        return Lam(term.name, body);
      case "App":
        var func = go1(term.func);
        var argm = go1(term.argm);
        return App(func, argm);
      case "Ctr":
        var func = term.func;
        var args = term.args.map((x:any) => go1(x));
        return Ctr(func, args);
      case "Cal":
        var func = term.func;
        var args = term.args.map((x:any) => go1(x));
        return Cal(func, args);
      case "Var":
        return Var(term.name);
    }
  };

  return go1(go0(term, {}));
}

// Stringifies a term
function show(term: any): any {
  switch (term.ctor) {
    case "Var":
      return term.name;
    case "Lam":
      var name = term.name;
      var body = show(term.body);
      return "λ" + name + ":" + body;
    case "App":
      var func = show(term.func);
      var argm = show(term.argm);
      return "(" + func + " " + argm + ")";
    case "Ctr":
      var func = term.func;
      var size = term.args.length;
      var args = term.args.map((x:any) => show(x));
      return "$" + func + ":" + size + "{" + args.join(" ") + "}";
    case "Cal":
      var func = term.func;
      var size = term.args.length;
      var args = term.args.map((x:any) => show(x));
      return "@" + func + ":" + size + "(" + args.join(" ") + ")";
    case "Dup":
      var kind = term.kind;
      var nam0 = term.nam0;
      var nam1 = term.nam1;
      var expr = show(term.expr);
      var body = show(term.body);
      return "! <" + kind + " " + nam0 + " " + nam1 + "> = " + expr + "; " + body;
  }
}

export function lambda_to_optimal(str: any): any {
  return show(compile(parse(str)));
}
