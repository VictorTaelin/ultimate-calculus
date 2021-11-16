// Types
// -----

type Term
  = {ctor: "Var", name: string}
  | {ctor: "Dup", nam0: string, nam1: string, expr: Term, body: Term}
  | {ctor: "Lam", name: string, body: Term}
  | {ctor: "App", func: Term, argm: Term}
  | {ctor: "Ctr", func: number, args: Array<Term>}
  | {ctor: "Cal", func: number, args: Array<Term>}

type Func
  = {ctor: "Fun", name: number, args: Array<string>, body: Match}

type Match
  = {ctor: "Cse", expr: string, cses: Array<[Array<string>,Match]>}
  | {ctor: "Ret", expr: Term}

function Var(name: string) : Term {
  return {ctor: "Var", name};
}

function Dup(nam0: string, nam1: string, expr: Term, body: Term) : Term {
  return {ctor: "Dup", nam0, nam1, expr, body};
}

function Lam(name: string, body: Term) : Term {
  return {ctor: "Lam", name, body};
}

function App(func: Term, argm: Term) : Term {
  return {ctor: "App", func, argm};
}

function Ctr(func: number, args: Array<Term>) : Term {
  return {ctor: "Ctr", func, args};
}

function Cal(func: number, args: Array<Term>) : Term {
  return {ctor: "Cal", func, args};
}

function Cse(expr: string, cses: Array<[Array<string>,Match]>) : Match {
  return {ctor: "Cse", expr, cses};
}

function Ret(expr: Term) : Match {
  return {ctor: "Ret", expr};
}

function Fun(name: number, args: Array<string>, body: Match) : Func {
  return {ctor: "Fun", name, args, body};
}

// Parser
// ------

function parse(code: string): Array<Func> {
  var idx = 0;

  function skip_comment() : boolean {
    if (code.slice(idx, idx+2) === "//") {
      idx += 2;
      while (idx < code.length && !/\n/.test(code[idx])) {
        idx++;
      }
      return true;
    }
    return false;
  }

  function skip_spaces() : boolean {
    var skipped = false;
    while (idx < code.length && /\s/.test(code[idx])) {
      idx++;
      skipped = true;
    }
    return skipped;
  }

  function skip() {
    while (skip_comment() || skip_spaces()) {}
  }

  function match(str: string) : boolean {
    skip();
    if (code.slice(idx, idx + str.length) === str) {
      idx += str.length;
      return true;
    }
    return false;
  }

  function consume(str: string) {
    skip();
    for (var i = 0; i < str.length; ++i) {
      if (code[idx + i] !== str[i]) {
        var found = code.slice(idx, idx+12).replace(/\n/g,"\\n");
        throw "Expected '" + str[i] + "', found '" + found + "...'.";
      }
    }
    idx += str.length;
  }

  function parse_name() : string {
    skip();
    var nm = "";
    while (idx < code.length && /[a-zA-Z0-9_.]/.test(code[idx])) {
      nm += code[idx++];
    }
    return nm;
  }

  function parse_dup() : Term | null {
    if (match("dup ")) {
      var nam0 = parse_name();
      var nam1 = parse_name();
      var skip = consume("=");
      var expr = parse_term();
      var body = parse_term();
      return Dup(nam0, nam1, expr, body);
    }
    return null;
  }

  function parse_lam() : Term | null {
    if (match("λ")) {
      var name = parse_name();
      var skip = consume(":");
      var body = parse_term();
      return Lam(name, body);
    }
    return null;
  }

  function parse_app() : Term | null {
    if (match("(")) {
      var func = parse_term();
      while (!match(")")) {
        var argm = parse_term();
        var func = App(func, argm);
      }
      return func;
    }
    return null;
  }

  function parse_ctr() : Term | null {
    if (match("$")) {
      var func = Number(parse_name());
      var skip = consume("{");
      var args = [];
      while (!match("}")) {
        args.push(parse_term());
      }
      return {ctor: "Ctr", func, args};
    }
    return null;
  }

  function parse_cal() : Term | null {
    if (match("@")) {
      var func = Number(parse_name());
      var skip = consume("(");
      var args = [];
      while (!match(")")) {
        args.push(parse_term());
      }
      return {ctor: "Cal", func, args};
    }
    return null;
  }

  function parse_var() : Term | null {
    var name = parse_name();
    if (name.length !== 0) {
      return Var(name);
    }
    return null;
  }

  function parse_term() : Term {
    var term
      =  parse_dup()
      || parse_lam()
      || parse_app()
      || parse_ctr()
      || parse_cal()
      || parse_var();
    return term || Var("?");
  }

  function parse_match() : Match {
    if (match("case ")) {
      var expr = parse_name();
      var skip = consume("{");
      var cses : Array<[Array<string>,Match]> = [];
      while (match("$")) {
        var func = Number(parse_name());
        var skip = consume("{");
        var args = [];
        while (!match("}")) {
          args.push(parse_name());
        }
        var skip = consume(":");
        var body = parse_match();
        cses.push([args,body]);
      }
      var skip = consume("}");
      return Cse(expr, cses);
    } else {
      var term = parse_term();
      return Ret(term);
    }
  }

  function parse_func(numb: number) : Func | null {
    if (match("@")) {
      var skip = consume(String(numb));
      var skip = consume("(");
      var args = [];
      while (!match(")")) {
        args.push(parse_name());
      }
      var skip = consume(":");
      var body = parse_match();
      return Fun(numb, args, body);
    }
    return null;
  }

  function parse_defs() : Array<Func> {
    var defs : Array<Func> = [];
    var numb = 0;
    while (match("def ")) {
      var func = parse_func(numb++);
      if (func) {
        defs.push(func);
      }
    }
    return defs;
  }

  return parse_defs();
}

// Stringifier
// -----------

// Stringifies a term
function show_term(term: Term): string {
  switch (term.ctor) {
    case "Var": {
      return term.name;
    }
    case "Dup": {
      let nam0 = term.nam0;
      let nam1 = term.nam1;
      let expr = show_term(term.expr);
      let body = show_term(term.body);
      return "dup " + nam0 + " " + nam1 + " = " + expr + " " + body;
    }
    case "Lam": {
      let name = term.name;
      let body = show_term(term.body);
      return "λ" + name + ":" + body;
    }
    case "App": {
      let args = [];
      while (term.ctor === "App") {
        args.push(show_term(term.argm));
        term = term.func;
      }
      let func = show_term(term);
      return "(" + func + " " + args.reverse().join(" ") + ")";
    }
    case "Ctr": {
      let func = term.func;
      let args = term.args.map(show_term);
      return "$" + func + "{" + args.join(" ") + "}";
    }
    case "Cal": {
      let func = term.func;
      let args = term.args.map(show_term);
      return "@" + func + "(" + args.join(" ") + ")";
    }
  }
  return "?";
}

function show_match(match: Match): string {
  switch (match.ctor) {
    case "Cse": {
      let expr = match.expr;
      let cses = [];
      for (var i = 0; i < match.cses.length; ++i) {
        let [cse_args, cse_body] = match.cses[i];
        let body = show_match(cse_body);
        cses.push("$" + i + "{" + cse_args.join(" ") + "}:" + body);
      }
      return "case " + expr + " {" + cses.join(" ") + "}";
    }
    case "Ret": {
      return show_term(match.expr);
    }
  }
}

function show_func(func: Func): string {
  let args = func.args;
  let body = show_match(func.body);
  return "@" + func.name + "(" + args.join(" ") + "): " + body;
}

function show_defs(defs: Array<Func>): string {
  return defs.map(x => "def " + show_func(x)).join("\n");
}

// Compiler
// --------

function line(tab: number, text: string) {
  for (var i = 0; i < tab; ++i) {
    text = "  " + text;
  }
  return text + "\n";
}

function sanitize(func: Func): Func {
  var size = 0;
  function fresh() : string {
    return "x" + (size++);
  }

  function sanitize_func(func: Func): Func {
    var name = func.name;
    var table : {[key:string]:string} = {};
    for (var arg_name of func.args) {
      table[arg_name] = fresh();
    }
    var args = func.args.map(x => table[x] || x);
    var body = sanitize_match(func.body, table);
    return Fun(name, args, body);
  }

  function sanitize_match(match: Match, table: {[key:string]:string}): Match {
    switch (match.ctor) {
      case "Cse": {
        let expr = table[match.expr] || match.expr;
        let cses : Array<[Array<string>,Match]> = match.cses.map(([cse_vars, cse_body]) => {
          let new_table = {...table};
          for (let cse_var of cse_vars) {
            new_table[cse_var] = fresh();
          }
          let vars = cse_vars.map(x => new_table[x] || x);
          let body = sanitize_match(cse_body, new_table);
          return [vars, body];
        })
        return Cse(expr, cses);
      }
      case "Ret": {
        let expr = sanitize_term(match.expr, table); 
        return Ret(expr);
      }
    }
  }

  function sanitize_term(term: Term, table: {[key:string]:string}): Term {
    switch (term.ctor) {
      case "Var": {
        return Var(table[term.name] || term.name);
      }
      case "Dup": {
        let nam0 = fresh();
        let nam1 = fresh();
        let expr = sanitize_term(term.expr, table);
        let body = sanitize_term(term.body, {...table, [term.nam0]: nam0, [term.nam1]: nam1});
        return Dup(nam0, nam1, expr, body);
      }
      case "Lam": {
        let name = fresh();
        let body = sanitize_term(term.body, {...table, [term.name]: name});
        return Lam(name, body);
      }
      case "App": {
        let func = sanitize_term(term.func, table);
        let argm = sanitize_term(term.argm, table);
        return App(func, argm);
      }
      case "Ctr": {
        let func = term.func;
        let args = term.args.map(x => sanitize_term(x,table));
        return Ctr(func, args);
      }
      case "Cal": {
        let func = term.func;
        let args = term.args.map(x => sanitize_term(x, table));
        return Cal(func, args);
      }
    }
  }

  return sanitize_func(func);
}

function compile(func: Func, tab: number, target: string): string {
  if (target === "js") {
    var VAR = "var"; 
    var GAS = "++GAS";
  } else if (target === "c") {
    var VAR = "u64";
    var GAS = "+GAS";
  } else {
    throw "Unknown target: " + target;
  }
  
  function compile_func(func: Func, tab: number) {
    text += line(tab, "case " + func.name + ": {");
    for (var i = 0; i < func.args.length; ++i) {
      locs[func.args[i]] = define("loc", "get_loc(term, "+i+")", tab+1);
      args[func.args[i]] = define("arg", "get_lnk(MEM, term, "+i+")", tab+1);
    }
    var clear = ["clear(MEM, get_loc(term, 0), "+func.args.length+")"];
    compile_match(func.body, clear, tab + 1)
    //text += line(tab+1, "break;");
    text += line(tab, "}");
  }

  function compile_match(match: Match, clear: Array<string>, tab: number) {
    switch (match.ctor) {
      case "Cse":
        //console.log("get", match.expr, args);
        var expr_name = locs[match.expr] || "";
        text += line(tab, VAR+" " + expr_name + "$ = reduce(MEM, " + expr_name + ");");
        text += line(tab, "switch (get_tag("+expr_name+"$) == CTR ? get_ex0(" + expr_name + "$) : -1) {");
        for (var i = 0; i < match.cses.length; ++i) {
          text += line(tab+1, "case " + i + ": {");
          var cse = match.cses[i];
          for (var j = 0; j < cse[0].length; ++j) {
            locs[cse[0][j]] = define("fld_loc", "get_loc("+expr_name+"$, "+j+")", tab + 2);
            args[cse[0][j]] = define("fld_arg", "get_lnk(MEM, "+expr_name+"$, "+j+")", tab + 2);
          }
          var cse_clear = ["clear(MEM, get_loc("+expr_name+"$, 0), "+cse[0].length+")"].concat(clear);
          compile_match(cse[1], cse_clear, tab + 2);
          text += line(tab+1, "}");
        }
        text += line(tab, "}");
        break;
      case "Ret":
        if (GAS) {
          text += line(tab, "++GAS;");
        }
        var done = compile_term(match.expr, tab);
        text += line(tab, "link(MEM, host, " + done + ");"); 
        for (var eraser of clear) {
          text += line(tab, eraser + ";");
        }
        text += line(tab, "continue;");
        break;
    }
  }

  function compile_term(term: Term, tab: number) : string {
    switch (term.ctor) {
      case "Var":
        //console.log("->", term.name, args);
        return args[term.name] ? args[term.name] : "?";
      case "Dup":
        var name = fresh("dup");
        text += line(tab, VAR + " " + name + " = alloc(MEM, 3);");
        args[term.nam0] = "lnk(DP0, 127, 0, "+name+")"; // TODO
        args[term.nam1] = "lnk(DP1, 127, 0, "+name+")"; // TODO
        var expr = compile_term(term.expr, tab);
        text += line(tab, "link(MEM, "+name+"+2, "+expr+");");
        var body = compile_term(term.body, tab);
        return body;
      case "Lam":
        var name = fresh("lam");
        text += line(tab, VAR + " " + name + " = alloc(MEM, 2);");
        args[term.name] = "lnk(VAR, 0, 0, "+name+")";
        var body = compile_term(term.body, tab);
        return "lnk(LAM, 0, 0, " + name + ")";
      case "App":
        var name = fresh("app");
        var func = compile_term(term.func, tab);
        var argm = compile_term(term.argm, tab);
        text += line(tab, VAR + " " + name + " = alloc(MEM, 2);");
        text += line(tab, "link(MEM, " + name+"+0, " + func + ");");
        return "lnk(APP, 0, 0, " + name + ")";
      case "Ctr":
        var ctr_args : Array<string> = [];
        for (var i = 0; i < term.args.length; ++i) {
          ctr_args.push(compile_term(term.args[i], tab));
        }
        var name = fresh("ctr");
        text += line(tab, VAR + " " + name + " = alloc(MEM, " + ctr_args.length + ");");
        for (var i = 0; i < ctr_args.length; ++i) {
          text += line(tab, "link(MEM, " + name+"+"+i + ", " + ctr_args[i] + ");");
        }
        return "lnk(CTR, " + term.func + ", " + ctr_args.length + ", " + name + ")";
      case "Cal":
        var cal_args : Array<string> = [];
        for (var i = 0; i < term.args.length; ++i) {
          cal_args.push(compile_term(term.args[i], tab));
        }
        //console.log("cal_args:", cal_args);
        var name = fresh("cal");
        text += line(tab, VAR + " " + name + " = alloc(MEM, " + cal_args.length + ");");
        for (var i = 0; i < cal_args.length; ++i) {
          text += line(tab, "link(MEM, " + name+"+"+i + ", " + cal_args[i] + ");");
        }
        return "lnk(CAL, " + term.func + ", " + cal_args.length + ", " + name + ")";
    }
  }

  function fresh(prefix: string) : string {
    return prefix + "$" + (size++);
  }

  function define(prefix: string, expr: string, tab: number) : string {
    var name = fresh(prefix);
    text += line(tab, VAR + " " + name + " = " + expr + ";");
    return name;
  }

  var locs : {[name: string]: string} = {};
  var args : {[name: string]: string} = {};
  var uses : {[name: string]: number} = {};
  var text = "";
  var size = 0;
  //compile_func(func, tab);
  compile_func(sanitize(func), tab);
  return text;
}

// Tests
// -----

var code = `
def @0(x):
  case x {
    $0{pred}: $0{$0{} $1{pred}}
    $1{pred}: @1(@0(pred))
    $2{}: $0{$1{} $2{}}
  }

def @1(p):
  case p {
    $0{carry pred}: $0{carry $0{pred}}
  }

def @2(x):
  @3(@0(x))

def @3(x):
  case x {
    $0{carry next}: case carry { 
      $0{}: @2(next)
      $1{}: next
    }
  }
  
`;

//var code = `
//def @0(x):
  //case x {
    //$0{}: $1{}
    //$1{}: $0{}
  //}
//`;

var defs = parse(code);

//console.log(show_defs(defs));
console.log(show_defs(defs.map(sanitize)));
console.log("");

console.log("        {\n");
for (var def of defs) {
  console.log(compile(def,5,"c"));
}
console.log("        }");

//const ZERO = 0;
//const SUCC = 1;

//const MUL2 = 0;

//var test = Fun(MUL2, ["a"],
  //Cse("a", [
    //// zero:
    //[[], Ret(Ctr(ZERO,[]))],
    //// succ:
    //[["a_pred"], Ret(Ctr(SUCC,[Ctr(SUCC,[Cal(MUL2,[Var("a_pred")])])]))],
  //]));

//console.log(compile(test, 5));
