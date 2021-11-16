// The Optimal Calculus
// ====================

import {pad} from "./utils.ts"

export type MAP<T> = Record<string, T>;

export const NIL : number = 0
export const LAM : number = 1
export const APP : number = 2
export const PAR : number = 3
export const DP0 : number = 4 // ex0 = color
export const DP1 : number = 5 // ex0 = color
export const VAR : number = 6
export const LNK : number = 7
export const CTR : number = 8 // ex0 = function, ex1 = arity
export const CAL : number = 9 // ex0 = function, ex1 = arity

export type Tag = number // 4 bits
export type Ex0 = number // 8 bits
export type Ex1 = number // 8 bits
export type Pos = number // 32 bits

export type Ptr = number

// Memory
// ------

var GAS : number = 0;
var LIM : number = Infinity;

var RE0 : Array<Ptr> = [];
var RE1 : Array<Ptr> = [];
var RE2 : Array<Ptr> = [];
var RE3 : Array<Ptr> = [];

export var MEM : Array<Ptr> = [];

var MUL_A = Math.pow(2, 4);
var MUL_B = Math.pow(2, 12);
var MUL_C = Math.pow(2, 20);

export function ptr(tag: Tag, pos: number, ex0: Ex0 = 0, ex1: Ex1 = 0) : Ptr {
  return tag + (ex0 * MUL_A) + (ex1 * MUL_B) + (pos * MUL_C);
}

export function get_tag(ptr: Ptr) : Tag {
  return ptr & 0xF;
}

export function get_ex0(ptr: Ptr) : Ex0 {
  return Math.floor(ptr / MUL_A) & 0xFF;
}

export function get_ex1(ptr: Ptr) : Ex1 {
  return Math.floor(ptr / MUL_B) & 0xFF;
}

export function get_pos(ptr: Ptr) : number {
  return Math.floor(ptr / MUL_C);
}

export function get_loc(ptr: Ptr, arg: number) : number {
  return Math.floor(ptr / MUL_C) + arg;
}

export function get_arg(term: Ptr, idx: number) : Ptr {
  return MEM[get_loc(term,idx)];
}

export function link(pos: number, term: Ptr) {
  MEM[pos] = term;
  switch (get_tag(term)) {
    case VAR: MEM[get_loc(term,0)] = ptr(LNK,pos); break;
    case DP0: MEM[get_loc(term,0)] = ptr(LNK,pos); break;
    case DP1: MEM[get_loc(term,1)] = ptr(LNK,pos); break;
  }
}

export function set_mem(mem: Array<number>) {
  MEM = mem;
}

export function get_gas() : number {
  return GAS;
}

export function alloc(size: number) : number {
  var reuse;
  switch (size) {
    case 0: reuse = RE0.pop(); break;
    case 1: reuse = RE1.pop(); break;
    case 2: reuse = RE2.pop(); break;
    case 3: reuse = RE3.pop(); break;
  }
  if (reuse !== undefined) {
    return reuse;
  } else {
    if (size > 0) {
      var pos = MEM.length;
      for (var k = 0; k < size; ++k) {
        MEM.push(0);
      }
      return pos;
    } else {
      return 0;
    }
  }
}

//var IS_FREED : any = {};
export function free(pos: number, size: number) {
  for (var k = pos; k < pos + size; ++k) {
    //IS_FREED[k] = 1;
    MEM[k] = 0;
  }
  switch (size) {
    case 0: RE0.push(pos); break;
    case 1: RE1.push(pos); break;
    case 2: RE2.push(pos); break;
    case 3: RE3.push(pos); break;
  }
}

// Debug
// -----

export function sanity_check() {
  for (var i = 0; i < MEM.length; ++i) {
    //if (MEM[i] !== 0 && MEM[get_pos(MEM[i])] === 0) {
      //throw new Error("Pointing to void at " + i + ".");
    //}
    switch (get_tag(MEM[i])) {
      case VAR:
        if (get_loc(MEM[get_loc(MEM[i],0)],0) !== i) {
          throw new Error("Bad var at " + i + ".");
        }
        break;
      case DP0:
        if (get_loc(MEM[get_loc(MEM[i],0)],0) !== i) {
          throw new Error("Bad dp0 at " + i + ".");
        }
        break;
      case DP1:
        if (get_loc(MEM[get_loc(MEM[i],1)],0) !== i) {
          throw new Error("Bad dp1 at " + i + ".");
        }
        break;
      case LAM:
        if (MEM[get_loc(MEM[i],1)] === 0) {
          throw new Error("Lambda pointing to nil body at " + i + ".");
        }
      //case PAR:
        //if (get_arg(MEM[i],0) === MEM[i] || get_arg(MEM[i],1) === MEM[i]) {
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
export function collect(term: Ptr, host: null | number) {
  switch (get_tag(term)) {
    case LAM:
      if (get_tag(get_arg(term,0)) !== NIL) {
        link(get_loc(get_arg(term,0),0), ptr(NIL,0));
      }
      collect(get_arg(term,1), get_loc(term,1));
      free(get_loc(term,0), 2);
      break;
    case APP:
      collect(get_arg(term,0), get_loc(term,0));
      collect(get_arg(term,1), get_loc(term,1));
      free(get_loc(term,0), 2);
      break;
    case PAR:
      collect(get_arg(term,0), get_loc(term,0));
      collect(get_arg(term,1), get_loc(term,1));
      free(get_loc(term,0), 2);
      if (host) {
        link(host, ptr(NIL,0));
      }
      break;
    case DP0:
      link(get_loc(term,0), ptr(NIL,0));
      if (host) {
        free(host, 1);
      }
      break;
    case DP1:
      link(get_loc(term,1), ptr(NIL,0));
      if (host) {
        free(host, 1);
      }
      break;
    case CTR:
    case CAL:
      var arity = get_ex1(term);
      for (var i = 0; i < arity; ++i) {
        collect(get_arg(term,i), get_loc(term,i));
      }
      free(get_loc(term,0), arity);
      break;
    case VAR:
      link(get_loc(term,0), ptr(NIL,0));
      if (host) {
        free(host, 1);
      }
      break;
  }
}

// Reduction
// ---------

export function subst(lnk: Ptr, val: Ptr) {
  if (get_tag(lnk) !== NIL) {
    link(get_loc(lnk,0), val);
  } else {
    collect(val, null);
  }
}

export function reduce(host: number) : Ptr {
  while (true) {
    var term = MEM[host];
    //console.log("REDUCE", depth, show_ptr(term));
    switch (get_tag(term)) {
      case APP:
        let func = reduce(get_loc(term,0));
        switch (get_tag(func)) {
          // (λx:b a)
          // --------- APP-LAM
          // x <- a
          case LAM: {
            if (GAS >= LIM) { return term; } else { ++GAS; }
            //console.log("[app-lam]", get_pos(term), get_pos(func));
            //sanity_check();
            subst(get_arg(func,0), get_arg(term,1));
            link(host, get_arg(func, 1));
            free(get_loc(term,0), 2);
            free(get_loc(func,0), 2);
            //console.log(show_term(MEM[0]));
            continue;
          }
          // (&A<a b> c)
          // ----------------- APP-PAR
          // !A<x0 x1> = c
          // &A<(a x0) (b x1)>
          case PAR: {
            if (GAS >= LIM) { return term; } else { ++GAS; }
            //console.log("[app-par]", get_pos(term), get_pos(func));
            //sanity_check();
            var let0 = alloc(3);
            var app0 = alloc(2);
            var app1 = alloc(2);
            var par0 = alloc(2);
            link(let0+2, get_arg(term, 1));
            link(app0+0, get_arg(func, 0));
            link(app0+1, ptr(DP0, let0, get_ex0(func)));
            link(app1+0, get_arg(func, 1));
            link(app1+1, ptr(DP1, let0, get_ex0(func)));
            link(par0+0, ptr(APP, app0));
            link(par0+1, ptr(APP, app1));
            link(host, ptr(PAR, par0, get_ex0(func)));
            free(get_loc(term,0), 2);
            free(get_loc(func,0), 2);
            //sanity_check();
            //console.log(show_term(MEM[0]));
            return MEM[host];
          }
        }
        break;
      case DP0:
      case DP1:
        let expr = reduce(get_loc(term,2));
        switch (get_tag(expr)) {
          // !A<r s> = λx: f
          // --------------- LET-LAM
          // r <- λx0: f0
          // s <- λx1: f1
          // x <- &A<x0 x1>
          // !A<f0 f1> = f
          // ~
          case LAM: {
            if (GAS >= LIM) { return term; } else { ++GAS; }
            //console.log("[let-lam]", get_pos(term), get_pos(expr));
            //sanity_check();
            var lam0 = alloc(2);
            var lam1 = alloc(2);
            var par0 = alloc(2);
            var let0 = alloc(3);
            link(lam0+1, ptr(DP0, let0, get_ex0(term)));
            link(lam1+1, ptr(DP1, let0, get_ex0(term)));
            link(par0+0, ptr(VAR, lam0));
            link(par0+1, ptr(VAR, lam1));
            link(let0+2, get_arg(expr, 1));
            subst(get_arg(term,0), ptr(LAM, lam0));
            subst(get_arg(term,1), ptr(LAM, lam1));
            subst(get_arg(expr,0), ptr(PAR, par0, get_ex0(term)));
            link(host, ptr(LAM, get_tag(term) === DP0 ? lam0 : lam1));
            free(get_loc(term,0), 3);
            free(get_loc(expr,0), 2);
            //sanity_check();
            //console.log(show_term(MEM[0]));
            continue;
          }
          // !A<x y> = !B<a b>
          // ----------------- LET-PAR
          // if A == B then
          //   x <- a
          //   y <- b
          //   ~
          // else
          //   x <- !B<xA xB>
          //   y <- !B<yA yB>
          //   !A<xA yA> = a
          //   !A<xB yB> = b
          //   ~
          case PAR: {
            if (GAS >= LIM) { return term; } else { ++GAS; }
            //console.log("[let-par]", get_pos(term), get_pos(expr));
            if (get_ex0(term) === get_ex0(expr)) {
              //sanity_check();
              subst(get_arg(term,0), get_arg(expr,0));
              subst(get_arg(term,1), get_arg(expr,1));
              link(host, get_arg(expr, get_tag(term) === DP0 ? 0 : 1));
              free(get_loc(term,0), 3);
              free(get_loc(expr,0), 2);
              //sanity_check();
              //console.log(show_term(MEM[0]));
              continue;
            } else {
              //sanity_check();
              var par0 = alloc(2);
              var par1 = alloc(2);
              var let0 = alloc(3);
              var let1 = alloc(3);
              link(par0+0, ptr(DP0,let0,get_ex0(term)));
              link(par0+1, ptr(DP0,let1,get_ex0(term)));
              link(par1+0, ptr(DP1,let0,get_ex0(term)));
              link(par1+1, ptr(DP1,let1,get_ex0(term)));
              link(let0+2, get_arg(expr,0));
              link(let1+2, get_arg(expr,1));
              subst(get_arg(term,0), ptr(PAR,par0,get_ex0(expr)));
              subst(get_arg(term,1), ptr(PAR,par1,get_ex0(expr)));
              link(host, ptr(PAR, get_tag(term) === DP0 ? par0 : par1, get_ex0(expr)));
              free(get_loc(term,0), 3);
              free(get_loc(expr,0), 2);
              //sanity_check();
              //console.log(show_term(MEM[0]));
              return MEM[host];
            }
          }
          // !A<x y> = $V:L{a b c ...}
          // -------------------------
          // !A<a0 a1> = a
          // !A<b0 b1> = b
          // !A<c0 c1> = c
          // ...
          // x <- $V:L{a0 b0 c0 ...}
          // y <- $V:L{a1 b1 c1 ...}
          // ~
          case CTR: {
            if (GAS >= LIM) { return term; } else { ++GAS; }
            //console.log("[let-ctr]", get_pos(term), get_pos(expr));
            let func = get_ex0(expr);
            let arit = get_ex1(expr);
            let ctr0 = alloc(arit);
            let ctr1 = alloc(arit);
            for (let i = 0; i < arit; ++i) {
              let leti = alloc(3);
              link(ctr0+i, ptr(DP0, leti));
              link(ctr1+i, ptr(DP1, leti));
              link(leti+2, get_arg(expr,i));
            }
            subst(get_arg(term,0), ptr(CTR, ctr0, func, arit));
            subst(get_arg(term,1), ptr(CTR, ctr1, func, arit));
            link(host, ptr(CTR, get_tag(term) === DP0 ? ctr0 : ctr1, func, arit));
            free(get_loc(term,0), 3);
            free(get_loc(expr,0), arit);
            //console.log(show_term(MEM[0]));
            return MEM[host];
          }
        }
        break;
      case CAL: {
        //console.log("calling:", get_ex0(term));
        //console.log(show_term(MEM[0]));
        switch (get_ex0(term))

        // START GENERATED CODE
        {

          case 0: {
            var loc$0 = get_loc(term,0);
            var arg$1 = get_arg(term,0);
            var loc$0$ = reduce(loc$0);
            switch (get_tag(loc$0$) === CTR ? get_ex0(loc$0$) : -1) {
              case 0: {
                var fld_loc$2 = get_loc(loc$0$,0);
                var fld_arg$3 = get_arg(loc$0$,0);
                ++GAS;
                var ctr$4 = alloc(0);
                var ctr$5 = alloc(1);
                link(ctr$5+0, fld_arg$3);
                var ctr$6 = alloc(2);
                link(ctr$6+0, ptr(CTR, ctr$4, 0, 0));
                link(ctr$6+1, ptr(CTR, ctr$5, 1, 1));
                link(host, ptr(CTR, ctr$6, 0, 2));
                free(get_loc(loc$0$,0),1)
                free(get_loc(term,0),1)
                continue;
              }
              case 1: {
                var fld_loc$7 = get_loc(loc$0$,0);
                var fld_arg$8 = get_arg(loc$0$,0);
                ++GAS;
                var cal$9 = alloc(1);
                link(cal$9+0, fld_arg$8);
                var cal$10 = alloc(1);
                link(cal$10+0, ptr(CAL, cal$9, 0, 1));
                link(host, ptr(CAL, cal$10, 1, 1));
                free(get_loc(loc$0$,0),1)
                free(get_loc(term,0),1)
                continue;
              }
              case 2: {
                ++GAS;
                var ctr$11 = alloc(0);
                var ctr$12 = alloc(0);
                var ctr$13 = alloc(2);
                link(ctr$13+0, ptr(CTR, ctr$11, 1, 0));
                link(ctr$13+1, ptr(CTR, ctr$12, 2, 0));
                link(host, ptr(CTR, ctr$13, 0, 2));
                free(get_loc(loc$0$,0),0)
                free(get_loc(term,0),1)
                continue;
              }
            }
          }

          case 1: {
            var loc$0 = get_loc(term,0);
            var arg$1 = get_arg(term,0);
            var loc$0$ = reduce(loc$0);
            switch (get_tag(loc$0$) === CTR ? get_ex0(loc$0$) : -1) {
              case 0: {
                var fld_loc$2 = get_loc(loc$0$,0);
                var fld_arg$3 = get_arg(loc$0$,0);
                var fld_loc$4 = get_loc(loc$0$,1);
                var fld_arg$5 = get_arg(loc$0$,1);
                ++GAS;
                var ctr$6 = alloc(1);
                link(ctr$6+0, fld_arg$5);
                var ctr$7 = alloc(2);
                link(ctr$7+0, fld_arg$3);
                link(ctr$7+1, ptr(CTR, ctr$6, 0, 1));
                link(host, ptr(CTR, ctr$7, 0, 2));
                free(get_loc(loc$0$,0),2)
                free(get_loc(term,0),1)
                continue;
              }
            }
          }

          case 2: {
            var loc$0 = get_loc(term,0);
            var arg$1 = get_arg(term,0);
            ++GAS;
            var cal$2 = alloc(1);
            link(cal$2+0, arg$1);
            var cal$3 = alloc(1);
            link(cal$3+0, ptr(CAL, cal$2, 0, 1));
            link(host, ptr(CAL, cal$3, 3, 1));
            free(get_loc(term,0),1)
            continue;
          }

          case 3: {
            var loc$0 = get_loc(term,0);
            var arg$1 = get_arg(term,0);
            var loc$0$ = reduce(loc$0);
            switch (get_tag(loc$0$) === CTR ? get_ex0(loc$0$) : -1) {
              case 0: {
                var fld_loc$2 = get_loc(loc$0$,0);
                var fld_arg$3 = get_arg(loc$0$,0);
                var fld_loc$4 = get_loc(loc$0$,1);
                var fld_arg$5 = get_arg(loc$0$,1);
                var fld_loc$2$ = reduce(fld_loc$2);
                switch (get_tag(fld_loc$2$) === CTR ? get_ex0(fld_loc$2$) : -1) {
                  case 0: {
                    ++GAS;
                    var cal$6 = alloc(1);
                    link(cal$6+0, fld_arg$5);
                    link(host, ptr(CAL, cal$6, 2, 1));
                    free(get_loc(fld_loc$2$,0),0)
                    free(get_loc(loc$0$,0),2)
                    free(get_loc(term,0),1)
                    continue;
                  }
                  case 1: {
                    ++GAS;
                    link(host, fld_arg$5);
                    free(get_loc(fld_loc$2$,0),0)
                    free(get_loc(loc$0$,0),2)
                    free(get_loc(term,0),1)
                    continue;
                  }
                }
              }
            }
          }

        }
        // END GENERATED CODE
        
      }
    }
    return term;
  }
}

export function normal(host: number) : Ptr {
  var seen : MAP<boolean> = {};
  function go(host: number) : Ptr {
    var term = MEM[host];
    //console.log("normal", show(term));
    if (seen[get_loc(term,0)]) {
      return term;
    } else {
      term = reduce(host);
      seen[get_loc(term,0)] = true;
      switch (get_tag(term)) {
        case LAM:
          link(get_loc(term,1), go(get_loc(term,1)));
          return term;
        case APP:
          link(get_loc(term,0), go(get_loc(term,0)));
          link(get_loc(term,1), go(get_loc(term,1)));
          return term;
        case PAR:
          link(get_loc(term,0), go(get_loc(term,0)));
          link(get_loc(term,1), go(get_loc(term,1)));
          return term;
        case DP0:
          link(get_loc(term,2), go(get_loc(term,2)));
          return term;
        case DP1:
          link(get_loc(term,2), go(get_loc(term,2)));
          return term;
        case CAL:
        case CTR:
          var arity = get_ex1(term);
          for (var i = 0; i < arity; ++i) {
            link(get_loc(term,i), go(get_loc(term,i)));
          }
          return term;
        default:
          return term;
      }
    }
  }
  return go(host);
}
