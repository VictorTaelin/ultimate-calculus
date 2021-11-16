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
export const ARG : number = 7
export const CTR : number = 8 // ex0 = function, ex1 = arity
export const CAL : number = 9 // ex0 = function, ex1 = arity

export type Tag = number // 4 bits
export type Ex0 = number // 8 bits
export type Ex1 = number // 8 bits
export type Pos = number // 32 bits

export type Lnk = number
export type Loc = number

export type Arr = {size: number, data: Uint32Array};
export type Mem = {lnk: Arr, use: Array<Arr>};

// Uint64Array
// -----------

export function array_alloc(capacity: number) {
  return {
    size: 0,
    data: new Uint32Array(capacity * 2),
  }
}

export function array_write(arr: Arr, idx: number, val: number) {
  arr.data[idx * 2 + 1] = (val / 0x100000000) >>> 0;
  arr.data[idx * 2 + 0] = val >>> 0;
}

export function array_read(arr: Arr, idx: number) : number {
  return (arr.data[idx * 2 + 1] * 0x100000000) + arr.data[idx * 2 + 0];
}

export function array_push(arr: Arr, value: number) {
  array_write(arr, arr.size++, value);
}

export function array_pop(arr: Arr) : number | null {
  if (arr.size > 0) {
    return array_read(arr, --arr.size);
  } else {
    return null;
  }
}

const array_megabyte = 131072; // 64-bit elements that fit in a MB

// Memory
// ------

export var GAS : number = 0;
//export var MEM : Mem = null as unknown as Mem;

export function lnk(tag: Tag, ex0: Ex0, ex1: Ex1, pos: Loc) : Lnk {
  return tag + (ex0 * 0x10) + (ex1 * 0x1000) + (pos * 0x100000);
}

export function get_tag(lnk: Lnk) : Tag {
  return lnk & 0xF;
}

export function get_ex0(lnk: Lnk) : Ex0 {
  return Math.floor(lnk / 0x10) & 0xFF;
}

export function get_ex1(lnk: Lnk) : Ex1 {
  return Math.floor(lnk / 0x1000) & 0xFF;
}

export function get_loc(lnk: Lnk, arg: number) : Loc {
  return Math.floor(lnk / 0x100000) + arg;
}

export function get_lnk(MEM: Mem, term: Lnk, arg: number) : Lnk {
  return array_read(MEM.lnk, get_loc(term,arg));
}

export function deref(MEM: Mem, loc: Loc) : Lnk {
  return array_read(MEM.lnk, loc);
}

export function link(MEM: Mem, loc: Loc, link: Lnk) {
  array_write(MEM.lnk, loc, link);
  switch (get_tag(link)) {
    case VAR: array_write(MEM.lnk, get_loc(link,0), lnk(ARG,0,0,loc)); break;
    case DP0: array_write(MEM.lnk, get_loc(link,0), lnk(ARG,0,0,loc)); break;
    case DP1: array_write(MEM.lnk, get_loc(link,1), lnk(ARG,0,0,loc)); break;
  }
}

export function get_gas() : number {
  return GAS;
}

export function alloc(MEM: Mem, size: number) : Loc {
  if (size === 0) {
    return 0;
  } else {
    var reuse = array_pop(MEM.use[size]);
    if (reuse !== null) {
      return reuse;
    } else {
      var loc = MEM.lnk.size;
      for (var i = 0; i < size; ++i) {
        array_push(MEM.lnk, 0);
      }
      return loc;
    }
  }
}

export function clear(MEM: Mem, loc: Loc, size: number) {
  if (size > 0) {
    array_push(MEM.use[size], loc);
  }
}

export function init(capacity: number = 2048 * array_megabyte) {
  var MEM = {
    lnk: array_alloc(capacity),
    use: [
      array_alloc(128 * array_megabyte),
      array_alloc(128 * array_megabyte),
      array_alloc(128 * array_megabyte),
      array_alloc(128 * array_megabyte),
      array_alloc(128 * array_megabyte),
      array_alloc(128 * array_megabyte),
      array_alloc(128 * array_megabyte),
      array_alloc(128 * array_megabyte),
      array_alloc(128 * array_megabyte),
    ]
  }
  array_push(MEM.lnk, 0);
  return MEM;
}

// Garbage Collection
// ------------------

export function collect(MEM: Mem, term: Lnk, host: Loc) {
  switch (get_tag(term)) {
    case LAM: {
      if (get_tag(get_lnk(MEM,term,0)) !== NIL) {
        link(MEM, get_loc(get_lnk(MEM,term,0),0), lnk(NIL,0,0,0));
      }
      collect(MEM, get_lnk(MEM,term,1), get_loc(term,1));
      clear(MEM, get_loc(term,0), 2);
      break;
    }
    case APP: {
      collect(MEM, get_lnk(MEM,term,0), get_loc(term,0));
      collect(MEM, get_lnk(MEM,term,1), get_loc(term,1));
      clear(MEM, get_loc(term,0), 2);
      break;
    }
    case PAR: {
      collect(MEM, get_lnk(MEM,term,0), get_loc(term,0));
      collect(MEM, get_lnk(MEM,term,1), get_loc(term,1));
      clear(MEM, get_loc(term,0), 2);
      if (host) {
        link(MEM, host, lnk(NIL,0,0,0));
      }
      break;
    }
    case DP0: {
      link(MEM, get_loc(term,0), lnk(NIL,0,0,0));
      if (host) {
        clear(MEM, host, 1);
      }
      break;
    }
    case DP1: {
      link(MEM, get_loc(term,1), lnk(NIL,0,0,0));
      if (host) {
        clear(MEM, host, 1);
      }
      break;
    }
    case CTR:
    case CAL: {
      var arity = get_ex1(term);
      for (var i = 0; i < arity; ++i) {
        collect(MEM, get_lnk(MEM,term,i), get_loc(term,i));
      }
      clear(MEM, get_loc(term,0), arity);
      break;
    }
    case VAR: {
      link(MEM, get_loc(term,0), lnk(NIL,0,0,0));
      if (host) {
        clear(MEM, host, 1);
      }
      break;
    }
  }
}

// Reduction
// ---------

export function subst(MEM: Mem, lnk: Lnk, val: Lnk) {
  if (get_tag(lnk) !== NIL) {
    link(MEM, get_loc(lnk,0), val);
  } else {
    collect(MEM, val, 0);
  }
}

import {show_lnk, show_mem, show_term} from "./syntax.ts";

export function reduce(MEM: Mem, host: Loc) : Lnk {
  while (true) {
    var term = deref(MEM, host);
    switch (get_tag(term)) {
      case APP: {
        let func = reduce(MEM, get_loc(term,0));
        switch (get_tag(func)) {
          // (λx:b a)
          // --------- APP-LAM
          // x <- a
          case LAM: {
            ++GAS;
            //console.log("[app-lam] " + get_loc(term,0) + " " + get_loc(func,0));
            subst(MEM, get_lnk(MEM, func, 0), get_lnk(MEM, term, 1));
            link(MEM, host, get_lnk(MEM, func, 1));
            clear(MEM, get_loc(term,0), 2);
            clear(MEM, get_loc(func,0), 2);
            //console.log(show_term(MEM, deref(MEM, 0)));
            continue;
          }
          // (&A<a b> c)
          // ----------------- APP-PAR
          // !A<x0 x1> = c
          // &A<(a x0) (b x1)>
          case PAR: {
            ++GAS;
            //console.log("[app-par] " + get_loc(term,0) + " " + get_loc(func,0));
            var let0 = alloc(MEM, 3);
            var app0 = alloc(MEM, 2);
            var app1 = alloc(MEM, 2);
            var par0 = alloc(MEM, 2);
            link(MEM, let0+2, get_lnk(MEM, term, 1));
            link(MEM, app0+0, get_lnk(MEM, func, 0));
            link(MEM, app0+1, lnk(DP0, get_ex0(func), 0, let0));
            link(MEM, app1+0, get_lnk(MEM, func, 1));
            link(MEM, app1+1, lnk(DP1, get_ex0(func), 0, let0));
            link(MEM, par0+0, lnk(APP, 0, 0, app0));
            link(MEM, par0+1, lnk(APP, 0, 0, app1));
            link(MEM, host, lnk(PAR, get_ex0(func), 0, par0));
            clear(MEM, get_loc(term,0), 2);
            clear(MEM, get_loc(func,0), 2);
            //console.log(show_term(MEM, deref(MEM, 0)));
            return deref(MEM, host);
          }
        }
        break;
      }
      case DP0:
      case DP1: {
        let expr = reduce(MEM, get_loc(term,2));
        switch (get_tag(expr)) {
          // !A<r s> = λx: f
          // --------------- LET-LAM
          // r <- λx0: f0
          // s <- λx1: f1
          // x <- &A<x0 x1>
          // !A<f0 f1> = f
          // ~
          case LAM: {
            ++GAS;
            //console.log("[let-lam] " + get_loc(term,0) + " " + get_loc(expr,0));
            var lam0 = alloc(MEM, 2);
            var lam1 = alloc(MEM, 2);
            var par0 = alloc(MEM, 2);
            var let0 = alloc(MEM, 3);
            link(MEM, lam0+1, lnk(DP0, get_ex0(term), 0, let0));
            link(MEM, lam1+1, lnk(DP1, get_ex0(term), 0, let0));
            link(MEM, par0+0, lnk(VAR, 0, 0, lam0));
            link(MEM, par0+1, lnk(VAR, 0, 0, lam1));
            link(MEM, let0+2, get_lnk(MEM, expr, 1));
            subst(MEM, get_lnk(MEM,term,0), lnk(LAM, 0, 0, lam0));
            subst(MEM, get_lnk(MEM,term,1), lnk(LAM, 0, 0, lam1));
            subst(MEM, get_lnk(MEM,expr,0), lnk(PAR, get_ex0(term), 0, par0));
            link(MEM, host, lnk(LAM, 0, 0, get_tag(term) === DP0 ? lam0 : lam1));
            clear(MEM, get_loc(term,0), 3);
            clear(MEM, get_loc(expr,0), 2);
            //console.log(show_term(MEM, deref(MEM, 0)));
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
            ++GAS;
            //console.log("[let-par] " + get_loc(term,0) + " " + get_loc(expr,0));
            if (get_ex0(term) === get_ex0(expr)) {
              subst(MEM, get_lnk(MEM,term,0), get_lnk(MEM,expr,0));
              subst(MEM, get_lnk(MEM,term,1), get_lnk(MEM,expr,1));
              link(MEM, host, get_lnk(MEM, expr, get_tag(term) === DP0 ? 0 : 1));
              clear(MEM, get_loc(term,0), 3);
              clear(MEM, get_loc(expr,0), 2);
              //return deref(MEM, host);
              continue;
            } else {
              var par0 = alloc(MEM, 2);
              var par1 = alloc(MEM, 2);
              var let0 = alloc(MEM, 3);
              var let1 = alloc(MEM, 3);
              link(MEM, par0+0, lnk(DP0,get_ex0(term),0,let0));
              link(MEM, par0+1, lnk(DP0,get_ex0(term),0,let1));
              link(MEM, par1+0, lnk(DP1,get_ex0(term),0,let0));
              link(MEM, par1+1, lnk(DP1,get_ex0(term),0,let1));
              link(MEM, let0+2, get_lnk(MEM,expr,0));
              link(MEM, let1+2, get_lnk(MEM,expr,1));
              subst(MEM, get_lnk(MEM,term,0), lnk(PAR,get_ex0(expr),0,par0));
              subst(MEM, get_lnk(MEM,term,1), lnk(PAR,get_ex0(expr),0,par1));
              link(MEM, host, lnk(PAR, get_ex0(expr), 0, get_tag(term) === DP0 ? par0 : par1));
              clear(MEM, get_loc(term,0), 3);
              clear(MEM, get_loc(expr,0), 2);
              //console.log(show_term(MEM, deref(MEM, 0)));
              return deref(MEM, host);
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
            ++GAS;
            //console.log("[let-ctr] " + get_loc(term,0) + " " + get_loc(expr,0));
            let func = get_ex0(expr);
            let arit = get_ex1(expr);
            let ctr0 = alloc(MEM, arit);
            let ctr1 = alloc(MEM, arit);
            for (let i = 0; i < arit; ++i) {
              let leti = alloc(MEM, 3);
              link(MEM, ctr0+i, lnk(DP0, 0, 0, leti));
              link(MEM, ctr1+i, lnk(DP1, 0, 0, leti));
              link(MEM, leti+2, get_lnk(MEM,expr,i));
            }
            subst(MEM, get_lnk(MEM,term,0), lnk(CTR, ctr0, func, arit));
            subst(MEM, get_lnk(MEM,term,1), lnk(CTR, ctr1, func, arit));
            link(MEM, host, lnk(CTR, func, arit, get_tag(term) === DP0 ? ctr0 : ctr1));
            clear(MEM, get_loc(term,0), 3);
            clear(MEM, get_loc(expr,0), arit);
            //console.log(show_term(MEM, deref(MEM, 0)));
            return deref(MEM, host);
          }
        }
        break;
      }
      case CAL: {
        //console.log(show_term(MEM[0]));
        switch (get_ex0(term))

        // START GENERATED CODE
        {

          case 0: {
            var loc$0 = get_loc(term, 0);
            var arg$1 = get_lnk(MEM, term, 0);
            var loc$0$ = reduce(MEM, loc$0);
            switch (get_tag(loc$0$) == CTR ? get_ex0(loc$0$) : -1) {
              case 0: {
                var fld_loc$2 = get_loc(loc$0$, 0);
                var fld_arg$3 = get_lnk(MEM, loc$0$, 0);
                ++GAS;
                var ctr$4 = alloc(MEM, 0);
                var ctr$5 = alloc(MEM, 1);
                link(MEM, ctr$5+0, fld_arg$3);
                var ctr$6 = alloc(MEM, 2);
                link(MEM, ctr$6+0, lnk(CTR, 0, 0, ctr$4));
                link(MEM, ctr$6+1, lnk(CTR, 1, 1, ctr$5));
                link(MEM, host, lnk(CTR, 0, 2, ctr$6));
                clear(MEM, get_loc(loc$0$, 0), 1);
                clear(MEM, get_loc(term, 0), 1);
                continue;
              }
              case 1: {
                var fld_loc$7 = get_loc(loc$0$, 0);
                var fld_arg$8 = get_lnk(MEM, loc$0$, 0);
                ++GAS;
                var cal$9 = alloc(MEM, 1);
                link(MEM, cal$9+0, fld_arg$8);
                var cal$10 = alloc(MEM, 1);
                link(MEM, cal$10+0, lnk(CAL, 0, 1, cal$9));
                link(MEM, host, lnk(CAL, 1, 1, cal$10));
                clear(MEM, get_loc(loc$0$, 0), 1);
                clear(MEM, get_loc(term, 0), 1);
                continue;
              }
              case 2: {
                ++GAS;
                var ctr$11 = alloc(MEM, 0);
                var ctr$12 = alloc(MEM, 0);
                var ctr$13 = alloc(MEM, 2);
                link(MEM, ctr$13+0, lnk(CTR, 1, 0, ctr$11));
                link(MEM, ctr$13+1, lnk(CTR, 2, 0, ctr$12));
                link(MEM, host, lnk(CTR, 0, 2, ctr$13));
                clear(MEM, get_loc(loc$0$, 0), 0);
                clear(MEM, get_loc(term, 0), 1);
                continue;
              }
            }
          }

          case 1: {
            var loc$0 = get_loc(term, 0);
            var arg$1 = get_lnk(MEM, term, 0);
            var loc$0$ = reduce(MEM, loc$0);
            switch (get_tag(loc$0$) == CTR ? get_ex0(loc$0$) : -1) {
              case 0: {
                var fld_loc$2 = get_loc(loc$0$, 0);
                var fld_arg$3 = get_lnk(MEM, loc$0$, 0);
                var fld_loc$4 = get_loc(loc$0$, 1);
                var fld_arg$5 = get_lnk(MEM, loc$0$, 1);
                ++GAS;
                var ctr$6 = alloc(MEM, 1);
                link(MEM, ctr$6+0, fld_arg$5);
                var ctr$7 = alloc(MEM, 2);
                link(MEM, ctr$7+0, fld_arg$3);
                link(MEM, ctr$7+1, lnk(CTR, 0, 1, ctr$6));
                link(MEM, host, lnk(CTR, 0, 2, ctr$7));
                clear(MEM, get_loc(loc$0$, 0), 2);
                clear(MEM, get_loc(term, 0), 1);
                continue;
              }
            }
          }

          case 2: {
            var loc$0 = get_loc(term, 0);
            var arg$1 = get_lnk(MEM, term, 0);
            ++GAS;
            var cal$2 = alloc(MEM, 1);
            link(MEM, cal$2+0, arg$1);
            var cal$3 = alloc(MEM, 1);
            link(MEM, cal$3+0, lnk(CAL, 0, 1, cal$2));
            link(MEM, host, lnk(CAL, 3, 1, cal$3));
            clear(MEM, get_loc(term, 0), 1);
            continue;
          }

          case 3: {
            var loc$0 = get_loc(term, 0);
            var arg$1 = get_lnk(MEM, term, 0);
            var loc$0$ = reduce(MEM, loc$0);
            switch (get_tag(loc$0$) == CTR ? get_ex0(loc$0$) : -1) {
              case 0: {
                var fld_loc$2 = get_loc(loc$0$, 0);
                var fld_arg$3 = get_lnk(MEM, loc$0$, 0);
                var fld_loc$4 = get_loc(loc$0$, 1);
                var fld_arg$5 = get_lnk(MEM, loc$0$, 1);
                var fld_loc$2$ = reduce(MEM, fld_loc$2);
                switch (get_tag(fld_loc$2$) == CTR ? get_ex0(fld_loc$2$) : -1) {
                  case 0: {
                    ++GAS;
                    var cal$6 = alloc(MEM, 1);
                    link(MEM, cal$6+0, fld_arg$5);
                    link(MEM, host, lnk(CAL, 2, 1, cal$6));
                    clear(MEM, get_loc(fld_loc$2$, 0), 0);
                    clear(MEM, get_loc(loc$0$, 0), 2);
                    clear(MEM, get_loc(term, 0), 1);
                    continue;
                  }
                  case 1: {
                    ++GAS;
                    link(MEM, host, fld_arg$5);
                    clear(MEM, get_loc(fld_loc$2$, 0), 0);
                    clear(MEM, get_loc(loc$0$, 0), 2);
                    clear(MEM, get_loc(term, 0), 1);
                    continue;
                  }
                }
              }
            }
          }

        }

        // END GENERATED CODE
        
      }
      break;
    }
    return term;
  }
}

export function normal(MEM: Mem, host: Loc) : number {
  GAS = 0;
  normal_go(MEM, host, {});
  return GAS;
}

function normal_go(MEM: Mem, host: Loc, seen: MAP<boolean>) : Lnk {
  var term = deref(MEM, host);
  if (seen[get_loc(term,0)]) {
    return term;
  } else {
    term = reduce(MEM, host);
    seen[get_loc(term,0)] = true;
    switch (get_tag(term)) {
      case LAM: {
        link(MEM, get_loc(term,1), normal_go(MEM, get_loc(term,1), seen));
        return term;
      }
      case APP: {
        link(MEM, get_loc(term,0), normal_go(MEM, get_loc(term,0), seen));
        link(MEM, get_loc(term,1), normal_go(MEM, get_loc(term,1), seen));
        return term;
      }
      case PAR: {
        link(MEM, get_loc(term,0), normal_go(MEM, get_loc(term,0), seen));
        link(MEM, get_loc(term,1), normal_go(MEM, get_loc(term,1), seen));
        return term;
      }
      case DP0: {
        link(MEM, get_loc(term,2), normal_go(MEM, get_loc(term,2), seen));
        return term;
      }
      case DP1: {
        link(MEM, get_loc(term,2), normal_go(MEM, get_loc(term,2), seen));
        return term;
      }
      case CAL:
      case CTR: {
        var arity = get_ex1(term);
        for (var i = 0; i < arity; ++i) {
          link(MEM, get_loc(term,i), normal_go(MEM, get_loc(term,i), seen));
        }
        return term;
      }
      default: {
        return term;
      }
    }
  }
}
