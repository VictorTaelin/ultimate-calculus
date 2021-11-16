import * as O from "./optimal_calculus.ts";
import {pad} from "./utils.ts";

// Stringification
// ---------------

export function show_tag(tag: O.Tag) {
  switch (tag) {
    case O.LAM: return "LAM";
    case O.APP: return "APP";
    case O.PAR: return "PAR";
    case O.DP0: return "DP0";
    case O.DP1: return "DP1";
    case O.VAR: return "VAR";
    case O.ARG: return "ARG";
    case O.NIL: return "NIL";
    case O.CTR: return "CTR";
    case O.CAL: return "CAL";
  }
}

export function show_lnk(lnk: O.Lnk) {
  return show_tag(O.get_tag(lnk)) + ":" + O.get_loc(lnk,0) + "[" + O.get_ex0(lnk) + "," + O.get_ex1(lnk) + "]";
}

export function show_mem(mem: O.Mem) {
  var text = "";
  for (var i = 0; i < mem.lnk.size; ++i) {
    var lnk = O.array_read(mem.lnk, i);
    if (lnk !== 0) {
      text += pad(String(i),4) + " | " + show_lnk(lnk) + "\n";
    }
  }
  return text;
}

export function show_term(MEM: O.Mem, term: O.Lnk) : string {
  var lets : {[key:string]:number} = {};
  var kinds : {[key:string]:number} = {};
  var names : {[key:string]:string} = {};
  var count = 0;
  function find_lets(term: O.Lnk) {
    switch (O.get_tag(term)) {
      case O.LAM:
        names[O.get_loc(term,0)] = String(++count);
        find_lets(O.get_lnk(MEM, term, 1));
        break;
      case O.APP:
        find_lets(O.get_lnk(MEM, term, 0));
        find_lets(O.get_lnk(MEM, term, 1));
        break;
      case O.PAR:
        find_lets(O.get_lnk(MEM, term, 0));
        find_lets(O.get_lnk(MEM, term, 1));
        break;
      case O.DP0:
        if (!lets[O.get_loc(term,0)]) {
          names[O.get_loc(term,0)] = String(++count);
          kinds[O.get_loc(term,0)] = O.get_ex0(term);
          lets[O.get_loc(term,0)] = O.get_loc(term,0);
          find_lets(O.get_lnk(MEM, term, 2));
        }
        break;
      case O.DP1:
        if (!lets[O.get_loc(term,0)]) {
          names[O.get_loc(term,0)] = String(++count);
          kinds[O.get_loc(term,0)] = O.get_ex0(term);
          lets[O.get_loc(term,0)] = O.get_loc(term,0);
          find_lets(O.get_lnk(MEM, term, 2));
        }
        break;
      case O.CTR:
      case O.CAL:
        var arity = O.get_ex1(term);
        for (var i = 0; i < arity; ++i) {
          find_lets(O.get_lnk(MEM, term,i));
        }
        break;
    }
  }
  function go(term: O.Lnk) : string {
    switch (O.get_tag(term)) {
      case O.LAM: {
        var name = "x" + (names[O.get_loc(term,0)] || "?");
        return "λ" + name + ":" + go(O.get_lnk(MEM, term, 1));
      }
      case O.APP: {
        let func = go(O.get_lnk(MEM, term, 0));
        let argm = go(O.get_lnk(MEM, term, 1));
        return "(" + func + " " + argm + ")";
      }
      case O.PAR: {
        let kind = O.get_ex0(term);
        let func = go(O.get_lnk(MEM, term, 0));
        let argm = go(O.get_lnk(MEM, term, 1));
        return "&" + kind + "<" + func + " " + argm + ">";
      }
      case O.CTR: {
        let func = O.get_ex0(term);
        let arit = O.get_ex1(term);
        let args = [];
        for (let i = 0; i < arit; ++i) {
          args.push(go(O.get_lnk(MEM, term, i)));
        }
        return "$" + func + ":" + arit + "{" + args.join(" ") + "}";
      }
      case O.CAL: {
        let func = O.get_ex0(term);
        let arit = O.get_ex1(term);
        let args = [];
        for (let i = 0; i < arit; ++i) {
          args.push(go(O.get_lnk(MEM, term, i)));
        }
        return "@" + func + ":" + arit + "(" + args.join(" ") + ")";
      }
      case O.DP0: {
        return "a" + (names[O.get_loc(term,0)] || "?");
      }
      case O.DP1: {
        return "b" + (names[O.get_loc(term,0)] || "?");
      }
      case O.VAR: {
        return "x" + (names[O.get_loc(term,0)] || "?");
      }
    }
    return "?" + show_lnk(term);
  }
  find_lets(term);
  var text = "";
  for (var key in lets) {
    var pos = lets[key];
    var kind = kinds[key] || 0;
    var name = names[pos] || "?";
    text += "!" + kind + "<a"+name+" b"+name+"> = " + go(O.deref(MEM, pos + 2)) + ";\n";
  }
  text += go(term);
  return text;
}

export function show_as_lambda(MEM: O.Mem, input_term: O.Lnk | null = null) : string {
  var term : O.Lnk = input_term ? input_term : O.deref(MEM, 0);
  var names : O.MAP<string> = {};
  var count : number = 0;
  var seen : O.MAP<boolean> = {};
  function name(term: O.Lnk, depth: number) {
    if (!seen[term]) {
      seen[term] = true;
      switch (O.get_tag(term)) {
        case O.LAM:
          if (O.get_tag(O.get_lnk(MEM, term, 0)) !== O.NIL) {
            names[O.lnk(O.VAR, 0, 0, O.get_loc(term,0))] = "x" + (++count);
          }
          name(O.get_lnk(MEM, term, 1), depth + 1);
          break;
        case O.APP:
          name(O.get_lnk(MEM, term, 0), depth + 1);
          name(O.get_lnk(MEM, term, 1), depth + 1);
          break;
        case O.PAR:
          name(O.get_lnk(MEM, term, 0), depth + 1);
          name(O.get_lnk(MEM, term, 1), depth + 1);
          break;
        case O.DP0:
          name(O.get_lnk(MEM, term, 2), depth + 1);
          break;
        case O.DP1:
          name(O.get_lnk(MEM, term, 2), depth + 1);
          break;
        case O.CTR:
          var arity = O.get_ex1(term);
          for (var i = 0; i < arity; ++i) {
            name(O.get_lnk(MEM, term, i), depth + 1);
          }
          break;
        case O.CAL:
          var arity = O.get_ex1(term);
          for (var i = 0; i < arity; ++i) {
            name(O.get_lnk(MEM, term, i), depth + 1);
          }
          break;
      }
    }
  }
  function go(term: O.Lnk, stacks: O.MAP<string>, seen: O.MAP<number>, depth: number) : string {
    if (seen[term]) {
      return "@";
      //return "(seen:" + Object.keys(seen).length + " | " + "depth:" + depth + ")";
    } else {
      //seen = {...seen, [term]: true};
      //if (depth > 30) return "(...)";
      switch (O.get_tag(term)) {
        case O.LAM: {
          let body = go(O.get_lnk(MEM, term, 1), stacks, seen, depth + 1);
          let name = "~";
          if (O.get_tag(O.get_lnk(MEM, term, 0)) !== O.NIL) {
            name = names[O.lnk(O.VAR, 0, 0, O.get_loc(term,0))] || "?";
          }
          return "λ" + name + ":" + body;
        }
        case O.APP: {
          let func = go(O.get_lnk(MEM, term, 0), stacks, seen, depth + 1);
          let argm = go(O.get_lnk(MEM, term, 1), stacks, seen, depth + 1);
          return "(" + func + " " + argm + ")"
        }
        case O.PAR: {
          let col = O.get_ex0(term);
          if (!stacks[col]) {
            stacks[col] = "";
          }
          if (stacks[col] !== undefined && stacks[col].length > 0) {
            if (stacks[col][0] === "0") {
              return go(O.get_lnk(MEM, term, 0), {...stacks,[col]:stacks[col].slice(1)}, seen, depth + 1);
            } else {
              return go(O.get_lnk(MEM, term, 1), {...stacks,[col]:stacks[col].slice(1)}, seen, depth + 1);
            }
          } else {
            let val0 = go(O.get_lnk(MEM, term, 0), stacks, seen, depth + 1);
            let val1 = go(O.get_lnk(MEM, term, 1), stacks, seen, depth + 1);
            return "{" + val0 + " " + val1 + "}"
          }
        }
        case O.DP0: {
          let col = O.get_ex0(term);
          return "" + go(O.get_lnk(MEM, term, 2), {...stacks,[col]:"0"+stacks[col]}, seen, depth + 1);
        }
        case O.DP1: {
          let col = O.get_ex0(term);
          return "" + go(O.get_lnk(MEM, term, 2), {...stacks,[col]:"1"+stacks[col]}, seen, depth + 1);
        }
        case O.CTR: {
          let func = O.get_ex0(term);
          var arit = O.get_ex1(term);
          let args = [];
          for (let i = 0; i < arit; ++i) {
            args.push(go(O.get_lnk(MEM, term, i), stacks, seen, depth + 1));
          }
          return "$" + String(func) + "{" + args.join(" ") + "}";
        }
        case O.CAL: {
          let func = O.get_ex0(term);
          var arit = O.get_ex1(term);
          let args = [];
          for (let i = 0; i < arit; ++i) {
            args.push(go(O.get_lnk(MEM, term, i), stacks, seen, depth + 1));
          }
          return "@" + String(func) + "{" + args.join(" ") + "}";
        }
        case O.VAR: {
          return names[term] || "^"+String(O.get_loc(term,0)) + "<" + show_lnk(O.deref(MEM, O.get_loc(term,0))) + ">";
        }
        case O.ARG: {
          return "!";
        }
        case O.NIL: {
          return "~";
        }
      }
      return "?(" + O.get_tag(term) + ")";
    }
  }
  name(term, 0);
  return go(term, {}, {}, 0);
}

// Parsing
// -------

export function read(code: string) : O.Mem {
  //O.PARSING = true;
  var lams  : O.MAP<number> = {};
  var let0s : O.MAP<number> = {};
  var let1s : O.MAP<number> = {};
  var tag0s : O.MAP<number> = {};
  var tag1s : O.MAP<number> = {};
  var vars  : Array<[string,number]> = [];

  function build() {
    for (var [var_name, var_pos] of vars) {
      var lam = lams[var_name]
      if (lam !== undefined) {
        O.link(MEM, var_pos, O.lnk(O.VAR,0,0,lam));
      }
      var let0 = let0s[var_name]
      if (let0 !== undefined) {
        O.link(MEM, var_pos, O.lnk(O.DP0,tag0s[var_name]||0,0,let0));
      }
      var let1 = let1s[var_name]
      if (let1 !== undefined) {
        O.link(MEM, var_pos, O.lnk(O.DP1,tag1s[var_name]||0,0,let1));
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
        || "." === code[0]) {
      name += code[0];
      code = code.slice(1);
    }
    return name;
  }

  function consume(str: string) {
    skip();
    if (code.slice(0, str.length) === str) {
      return code.slice(str.length);
    } else {
      throw "Bad parse: " + str;
    }
  }

  function parse_numb(): number {
    if (/[0-9]/.test(code[0])) {
      var num = "";
      while (/[0-9]/.test(code[0])) {
        num += code[0];
        code = code.slice(1);
      }
      return Number(num);
    } else {
      return Number(0);
    }
  }

  function parse_term(local: number) : O.Lnk {
    skip();
    var node = 0;
    switch (code[0]) {
      case "λ": 
        code = consume("λ");
        node = O.alloc(MEM, 2);
        var name = parse_name();
        code = consume(":");
        var body = parse_term(node + 1);
        O.link(MEM, node+0, O.lnk(O.NIL,0,0,0));
        O.link(MEM, node+1, body);
        lams[name] = node;
        return O.lnk(O.LAM, 0, 0, node);
      case "(":
        code = consume("(");
        node = O.alloc(MEM, 2);
        var func = parse_term(node + 0);
        var argm = parse_term(node + 1);
        code = consume(")");
        O.link(MEM, node+0, func);
        O.link(MEM, node+1, argm);
        return O.lnk(O.APP, 0, 0, node);
      case "&":
        code = consume("&");
        var col = parse_numb();
        code = consume("<");
        code = consume(">");
        node = O.alloc(MEM, 2);
        var val0 = parse_term(node + 0);
        var val1 = parse_term(node + 1);
        O.link(MEM, node+0, val0);
        O.link(MEM, node+1, val1);
        skip();
        return O.lnk(O.PAR, col, 0, node);
      case "!":
        code = consume("!");
        var col = parse_numb();
        code = consume("<");
        var nam0 = parse_name();
        var nam1 = parse_name();
        code = consume(">");
        code = consume("=");
        node = O.alloc(MEM, 3);
        var expr = parse_term(node + 2);
        code = consume(";");
        var body = parse_term(local);
        O.link(MEM, node+0, O.lnk(O.NIL, 0, 0, 0));
        O.link(MEM, node+1, O.lnk(O.NIL, 0, 0, 0));
        O.link(MEM, node+2, expr);
        let0s[nam0] = node;
        tag0s[nam0] = col;
        let1s[nam1] = node;
        tag1s[nam1] = col;
        return body;
      // $0{1 2 3}
      case "$":
        code = consume("$");
        var func = parse_numb();
        code = consume(":");
        var arit = parse_numb();
        code = consume("{");
        var node = O.alloc(MEM, arit);
        var args = [];
        for (var i = 0; i < arit; ++i) {
          args.push(parse_term(node + i));
        }
        code = consume("}");
        for (var i = 0; i < arit; ++i) {
          O.link(MEM, node+i, args[i]);
        }
        return O.lnk(O.CTR, func, arit, node);
      // @0(1 2 3)
      case "@":
        code = consume("@");
        var func = parse_numb();
        code = consume(":");
        var arit = parse_numb();
        code = consume("(");
        var node = O.alloc(MEM, arit);
        var args = [];
        for (var i = 0; i < arit; ++i) {
          args.push(parse_term(node + i));
        }
        code = consume(")");
        for (var i = 0; i < arit; ++i) {
          O.link(MEM, node+i, args[i]);
        }
        return O.lnk(O.CAL, func, arit, node);
      default:
        var name = parse_name();
        var vari = O.lnk(O.NIL,0,0,0);
        vars.push([name, local]);
        return vari;
    }
  }

  var MEM = O.init();
  var root = parse_term(0);
  O.link(MEM, 0, root);
  build();
  return MEM;
}

// Lambda to Optimal
// -----------------

// TODO: shorten, reuse lang term

export var lambda_to_optimal = (function lambda_to_optimal() {
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
        return "!" + kind + "<" + nam0 + " " + nam1 + "> = " + expr + "; " + body;
    }
  }

  return function lambda_to_optimal(str: any): any {
    return show(compile(parse(str)));
  }
})()
