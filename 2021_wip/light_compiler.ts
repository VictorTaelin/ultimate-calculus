// LAM
// APP
// CTR

type Term
  = {ctor: "Var", name: string}
  | {ctor: "Let", name: string, expr: Term, body: Term}
  | {ctor: "Lam", name: string, body: Term}
  | {ctor: "App", func: Term, argm: Term}
  | {ctor: "Ctr", numb: number, args: Array<Term>}
  | {ctor: "Cal", func: string, args: Array<Term>}

type Func
  = {ctor: "Fun", name: string, args: Array<string>, body: Match}

type Match
  = {ctor: "Cse", expr: string, cses: Array<[Array<string>,Match]>}
  | {ctor: "Ret", expr: Term}

// arg_name ~> [expr_name, expr_code]
type ArgInfo
  = {[arg_name: string]: string}

function Var(name: string) : Term {
  return {ctor: "Var", name};
}

function Lam(name: string, body: Term) : Term {
  return {ctor: "Lam", name, body};
}

function App(func: Term, argm: Term) : Term {
  return {ctor: "App", func, argm};
}

function Ctr(numb: number, args: Array<Term>) : Term {
  return {ctor: "Ctr", numb, args};
}

function Cal(func: string, args: Array<Term>) : Term {
  return {ctor: "Cal", func, args};
}

function Cse(expr: string, cses: Array<[Array<string>,Match]>) : Match {
  return {ctor: "Cse", expr, cses};
}

function Ret(expr: Term) : Match {
  return {ctor: "Ret", expr};
}

function Fun(name: string, args: Array<string>, body: Match) : Func {
  return {ctor: "Fun", name, args, body};
}

function line(tab: number, text: string) {
  for (var i = 0; i < tab; ++i) {
    text = "  " + text;
  }
  return text + "\n";
}

function compile(func: Func, tab: number): string {
  function compile_func(func: Func, tab: number) {
    var args : ArgInfo = {};
    for (var i = 0; i < func.args.length; ++i) {
      args[func.args[i]] = define("arg", "get_loc(term,"+i+")", tab);
    }
    text += line(tab, "case " + func.name.toUpperCase() + ":");
    compile_match(func.body, args, tab + 1)
    text += line(tab, "break;");
  }

  function compile_match(match: Match, args: ArgInfo, tab: number) {
    switch (match.ctor) {
      case "Cse":
        //console.log("get", match.expr, args);
        var expr_name = args[match.expr] || "";
        text += line(tab, "var " + expr_name + "$ = reduce(" + expr_name + ");");
        text += line(tab, "switch (get_tag("+expr_name+"$) === CTR ? get_col(" + expr_name + "$) : -1) {");
        for (var i = 0; i < match.cses.length; ++i) {
          text += line(tab+1, "case " + i + ":");
          var cse = match.cses[i];
          var cse_args : ArgInfo = {...args};
          for (var j = 0; j < cse[0].length; ++j) {
            cse_args[cse[0][j]] = define("fld", "get_loc("+expr_name+"$,"+j+")", tab + 2);
          }
          compile_match(cse[1], cse_args, tab + 2);
          text += line(tab+1, "break;");
        }
        text += line(tab, "}");
        break;
      case "Ret":
        var done = compile_term(match.expr, args, tab);
        text += line(tab, "return " + done + ";"); 
        break;
    }
  }

  function compile_term(term: Term, args: ArgInfo, tab: number) : string {
    switch (term.ctor) {
      case "Var":
        return args[term.name] ? args[term.name] : "?";
      case "Lam":
        var name = fresh("lam");
        var body = compile_term(term.body, {...args, [term.name]: "ptr(VAR, "+name+", 0)"}, tab);
        text += line(tab, "var " + name + " = alloc(2);");
        return "ptr(LAM, " + name + ", 0)";
      case "App":
        var name = fresh("app");
        var func = compile_term(term.func, args, tab);
        var argm = compile_term(term.argm, args, tab);
        text += line(tab, "var " + name + " = alloc(2);");
        text += line(tab, "link(" + name+"+0," + func + ");");
        return "ptr(APP, " + name + ", 0)";
      case "Ctr":
        var ctr_args : Array<string> = [];
        for (var i = 0; i < term.args.length; ++i) {
          ctr_args.push(compile_term(term.args[i], args, tab));
        }
        var name = fresh("ctr");
        text += line(tab, "var " + name + " = alloc(" + ctr_args.length + ");");
        for (var i = 0; i < ctr_args.length; ++i) {
          text += line(tab, "link(" + name+"+"+i + "," + ctr_args[i] + ");");
        }
        return "ptr(CTR, " + name + ", " + term.numb + ")";
      case "Cal":
        var cal_args : Array<string> = [];
        for (var i = 0; i < term.args.length; ++i) {
          cal_args.push(compile_term(term.args[i], args, tab));
        }
        //console.log("cal_args:", cal_args);
        var name = fresh("cal");
        text += line(tab, "var " + name + " = alloc(" + cal_args.length + ");");
        for (var i = 0; i < cal_args.length; ++i) {
          text += line(tab, "link(" + name+"+"+i + "," + cal_args[i] + ");");
        }
        return "ptr(CAL, " + name + ", " + term.func.toUpperCase() + ")";
      case "Let":
        return "?";
    }
  }

  function fresh(prefix: string) : string {
    return prefix + "$" + (++size);
  }

  function define(prefix: string, expr: string, tab: number) : string {
    var name = fresh(prefix);
    text += line(tab, "var " + name + " = " + expr + ";");
    return name;
  }

  var text = "";
  var size = 0;
  compile_func(func, 0);
  return text;
}

var test = Fun("Nat$equal", ["a","b"],
  Cse("a", [
    // zero:
    [[], Cse("b", [
      // zero:
      [[], Ret(Ctr(1,[]))],
      // succ:
      [["b_pred"], Ret(Ctr(0,[]))]
    ])],
    // succ:
    [["a_pred"], Cse("b", [
      // zero:
      [[], Ret(Ctr(0,[]))],
      // succ:
      [["b_pred"], Ret(Cal("Nat$equal",[Var("a_pred"),Var("b_pred")]))]
    ])]
  ]));

console.log(compile(test, 0));


//add(a, b)
  //case a {
    //zero: case b {
      //zero: zero
      //succ: succ(add(a,b.pred))
    //}
    //succ: case b{ 
      //zero: succ(add(a,b))
      //succ: succ(succ(add(a.pred,b.pred)))
    //}
  //}

//match_nat (zero)      case_zero case_succ = case_zero
//match_nat (succ pred) case_zero case_succ = (case_succ pred)

//half (zero)          = (zero)
//half (succ (succ x)) = (succ (half x))

//half n = case n {
  //zero: zero
  //succ: case n.pred {
    //zero: zero
    //succ: succ(half(n.pred.pred))
  //}
//}

// LAM_1
// LAM_2
// LAM_3
// LAM_4
// PAR_1
// PAR_2
// PAR_3
// PAR_4
// DUP_2_0
// DUP_2_1
// DUP_3_0
// DUP_3_1
// DUP_3_2
// DUP_4_0
// DUP_4_1
// DUP_4_2
// DUP_4_3
// CTR_0_0
// CTR_0_1
// CTR_0_2
// CTR_0_3
// CTR_0_4
// CTR_1_0
// CTR_1_1
// CTR_1_2
// CTR_1_3
// CTR_1_4
  


//// cse-par

//(case {a b} {foo: A, bar(x,y): B})
//----------------------------------
//let A0 A1 = A
//let B0 B1 = B
//let X0 X1 = {x0 x1}
//let Y0 Y1 = {y0 y1}
//{
  //(case a {foo: A0, bar(x0,y0): B0})
  //(case b {foo: A1, bar(x1,y1): B1})
//}

//// cse-ctr

//(case (bar a b) {foo: A0, bar(x0,y0): B0}) 
//------------------------------------------
//x0 <- a
//y0 <- b
//B0






//λa. λb. 
  //case a {
    //A: case b {
      //A: 
      //B(pred): _
    //}
    //B(pred): case b {
      //A: _
      //B(pred): _
    //}
  //}
