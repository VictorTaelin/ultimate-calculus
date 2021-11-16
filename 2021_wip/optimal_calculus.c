#include <stdlib.h>
#include <stdio.h>

// Types
// -----

typedef unsigned char u8;
typedef unsigned int u32;
typedef unsigned long long int u64;

const u8 NIL = 0;
const u8 LAM = 1;
const u8 APP = 2;
const u8 PAR = 3;
const u8 DP0 = 4;
const u8 DP1 = 5;
const u8 VAR = 6;
const u8 ARG = 7;
const u8 CTR = 8;
const u8 CAL = 9;

typedef u8  Tag;
typedef u8  Ex0;
typedef u8  Ex1;
typedef u32 Pos;

typedef u64 Lnk;
typedef u64 Loc;

typedef struct {
  u64 size;
  u64* data;
} Arr;

typedef struct {
  Arr lnk;
  Arr use[9];
} Mem;

// Array
// -----

Arr array_alloc(u64 capacity) {
  Arr arr;
  arr.size = 0;
  arr.data = malloc(capacity * sizeof(u64));
  return arr;
}

void array_write(Arr* arr, u64 idx, u64 value) {
  arr->data[idx] = value;
}

u64 array_read(Arr* arr, u64 idx) {
  return arr->data[idx];
}

void array_push(Arr* arr, u64 value) {
  array_write(arr, arr->size++, value);
}

u64 array_pop(Arr* arr) {
  if (arr->size > 0) {
    return array_read(arr, --arr->size);
  } else {
    return -1;
  }
}

// Memory
// ------

Lnk lnk(Tag tag, Ex0 ex0, Ex1 ex1, Loc pos) {
  return tag | (ex0 << 4) | (ex1 << 12) | (pos << 20);
}

Tag get_tag(Lnk lnk) {
  return lnk & 0xF;
}

Ex0 get_ex0(Lnk lnk) {
  return (lnk >> 4) & 0xFF;
}

Ex1 get_ex1(Lnk lnk) {
  return (lnk >> 12) & 0xFF;
}

Loc get_loc(Lnk lnk, u8 arg) {
  return (lnk >> 20) + arg;
}

Lnk get_lnk(Mem* mem, Lnk lnk, u8 arg) {
  return array_read(&mem->lnk, get_loc(lnk, arg));
}

Lnk deref(Mem* mem, Loc loc) {
  return array_read(&mem->lnk, loc);
}

void link(Mem* mem, Loc loc, Lnk link) {
  array_write(&mem->lnk, loc, link);
  switch (get_tag(link)) {
    case VAR: array_write(&mem->lnk, get_loc(link,0), lnk(ARG,0,0,loc)); break;
    case DP0: array_write(&mem->lnk, get_loc(link,0), lnk(ARG,0,0,loc)); break;
    case DP1: array_write(&mem->lnk, get_loc(link,1), lnk(ARG,0,0,loc)); break;
  }
}

Loc alloc(Mem* mem, u64 size) {
  if (size == 0) {
    return 0;
  } else {
    u64 reuse = array_pop(&mem->use[size]);
    if (reuse != -1) {
      return reuse;
    } else {
      u64 loc = mem->lnk.size;
      for (u64 i = 0; i < size; ++i) {
        array_push(&mem->lnk, 0);
      }
      return loc;
    }
  }
}

void erase(Mem* mem, Loc loc, u64 size) {
  array_push(&mem->use[size], loc);
}

// Garbage Collection
// ------------------

void collect(Mem* mem, Lnk term, Loc host) {
  switch (get_tag(term)) {
    case LAM: {
      if (get_tag(get_lnk(mem,term,0)) != NIL) {
        link(mem, get_loc(get_lnk(mem,term,0),0), lnk(NIL,0,0,0));
      }
      collect(mem, get_lnk(mem,term,1), get_loc(term,1));
      erase(mem, get_loc(term,0), 2);
      break;
    }
    case APP: {
      collect(mem, get_lnk(mem,term,0), get_loc(term,0));
      collect(mem, get_lnk(mem,term,1), get_loc(term,1));
      erase(mem, get_loc(term,0), 2);
      break;
    }
    case PAR: {
      collect(mem, get_lnk(mem,term,0), get_loc(term,0));
      collect(mem, get_lnk(mem,term,1), get_loc(term,1));
      erase(mem, get_loc(term,0), 2);
      if (host) {
        link(mem, host, lnk(NIL,0,0,0));
      }
      break;
    }
    case DP0: {
      link(mem, get_loc(term,0), lnk(NIL,0,0,0));
      if (host) {
        erase(mem, host, 1);
      }
      break;
    }
    case DP1: {
      link(mem, get_loc(term,1), lnk(NIL,0,0,0));
      if (host) {
        erase(mem, host, 1);
      }
      break;
    }
    case CTR:
    case CAL: {
      Ex1 arity = get_ex1(term);
      for (u64 i = 0; i < arity; ++i) {
        collect(mem, get_lnk(mem,term,i), get_loc(term,i));
      }
      erase(mem, get_loc(term,0), arity);
      break;
    }
    case VAR: {
      link(mem, get_loc(term,0), lnk(NIL,0,0,0));
      if (host) {
        erase(mem, host, 1);
      }
      break;
    }
  }
}

// Reduction
// ---------

void subst(Mem* mem, Lnk lnk, Lnk val) {
  if (get_tag(lnk) != NIL) {
    link(mem, get_loc(lnk,0), val);
  } else {
    collect(mem, val, 0);
  }
}

Lnk reduce(Mem* MEM, Loc host) {
  while (1) {
    Loc term = deref(MEM, host);
    Tag tag = get_tag(term);
    switch (tag) {
      case APP: {
        Lnk func = reduce(MEM, get_loc(term,0));
        switch (get_tag(func)) {
          case LAM: {
            link(MEM, host, get_lnk(MEM, func, 1));
            subst(MEM, get_lnk(MEM,func,0), get_lnk(MEM,term,1));
            erase(MEM, get_loc(term,0), 2);
            erase(MEM, get_loc(func,0), 2);
            continue;
          }
          case PAR: {
            Lnk let0 = alloc(MEM, 3);
            Lnk app0 = alloc(MEM, 2);
            Lnk app1 = alloc(MEM, 2);
            Lnk par0 = alloc(MEM, 2);
            link(MEM, let0+2, get_lnk(MEM,term, 1));
            link(MEM, app0+0, get_lnk(MEM,func, 0));
            link(MEM, app0+1, lnk(DP0, get_ex0(func), 0, let0));
            link(MEM, app1+0, get_lnk(MEM,func, 1));
            link(MEM, app1+1, lnk(DP1, get_ex0(func), 0, let0));
            link(MEM, par0+0, lnk(APP, 0, 0, app0));
            link(MEM, par0+1, lnk(APP, 0, 0, app1));
            link(MEM, host, lnk(PAR, get_ex0(func), 0, par0));
            erase(MEM, get_loc(term,0), 2);
            erase(MEM, get_loc(func,0), 2);
            return deref(MEM, host);
          }
        }
        break;
      }
      case DP0:
      case DP1: {
        Lnk expr = reduce(MEM, get_loc(term,2));
        switch (get_tag(expr)) {
          case LAM: {
            Lnk lam0 = alloc(MEM, 2);
            Lnk lam1 = alloc(MEM, 2);
            Lnk par0 = alloc(MEM, 2);
            Lnk let0 = alloc(MEM, 3);
            link(MEM, lam0+1, lnk(DP0, get_ex0(term), 0, let0));
            link(MEM, lam1+1, lnk(DP1, get_ex0(term), 0, let0));
            link(MEM, par0+0, lnk(VAR, 0, 0, lam0));
            link(MEM, par0+1, lnk(VAR, 0, 0, lam1));
            link(MEM, let0+2, get_lnk(MEM, expr, 1));
            link(MEM, host, lnk(LAM, 0, 0, get_tag(term) == DP0 ? lam0 : lam1));
            subst(MEM, get_lnk(MEM,term,0), lnk(LAM, 0, 0, lam0));
            subst(MEM, get_lnk(MEM,term,1), lnk(LAM, 0, 0, lam1));
            subst(MEM, get_lnk(MEM,expr,0), lnk(PAR, get_ex0(term), 0, par0));
            erase(MEM, get_loc(term,0), 3);
            erase(MEM, get_loc(expr,0), 2);
            continue;
          }
          case PAR: {
            if (get_ex0(term) == get_ex0(expr)) {
              link(MEM, host, get_lnk(MEM,expr, get_tag(term) == DP0 ? 0 : 1));
              subst(MEM, get_lnk(MEM,term,0), get_lnk(MEM,expr,0));
              subst(MEM, get_lnk(MEM,term,1), get_lnk(MEM,expr,1));
              erase(MEM, get_loc(term,0), 3);
              erase(MEM, get_loc(expr,0), 2);
              continue;
            } else {
              Lnk par0 = alloc(MEM, 2);
              Lnk par1 = alloc(MEM, 2);
              Lnk let0 = alloc(MEM, 3);
              Lnk let1 = alloc(MEM, 3);
              link(MEM, par0+0, lnk(DP0,get_ex0(term),0,let0));
              link(MEM, par0+1, lnk(DP0,get_ex0(term),0,let1));
              link(MEM, par1+0, lnk(DP1,get_ex0(term),0,let0));
              link(MEM, par1+1, lnk(DP1,get_ex0(term),0,let1));
              link(MEM, let0+2, get_lnk(MEM,expr,0));
              link(MEM, let1+2, get_lnk(MEM,expr,1));
              link(MEM, host, lnk(PAR, get_ex0(expr), 0, get_tag(term) == DP0 ? par0 : par1));
              subst(MEM, get_lnk(MEM,term,0), lnk(PAR,get_ex0(expr),0,par0));
              subst(MEM, get_lnk(MEM,term,1), lnk(PAR,get_ex0(expr),0,par1));
              erase(MEM, get_loc(term,0), 3);
              erase(MEM, get_loc(expr,0), 2);
              continue;
            }
          }
        }
        break;
      }
    }
    return term;
  }
}

// sets the nth bit of a bit-array represented as a u64 array
void set_bit(u64* bits, u64 bit) {
    bits[bit >> 6] |= (1ULL << (bit & 0x3f));
}

// gets the nth bit of a bit-array represented as a u64 array
u8 get_bit(u64* bits, u8 bit) {
    return (bits[bit >> 6] >> (bit & 0x3F)) & 1;
}

Lnk normal_go(Mem* MEM, Loc host, u64* seen) {
  Lnk term = deref(MEM, host);
  if (get_bit(seen, get_loc(term,0))) {
    return term;
  } else {
    term = reduce(MEM, host);
    set_bit(seen, get_loc(term,0));
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
        u64 arity = (u64)get_ex1(term);
        for (u64 i = 0; i < arity; ++i) {
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

Lnk normal(Mem* MEM, Loc host) {
  const u64 size = 2097152; // uses 16 MB, covers heaps up to 1 GB
  static u64 seen[size]; 
  for (u64 i = 0; i < size; ++i) {
    seen[i] = 0;
  }
  return normal_go(MEM, host, seen);
}

void normal_ffi(
  u8* lnk_data, u32 lnk_size,
  u8* use0_data, u32 use0_size,
  u8* use1_data, u32 use1_size,
  u8* use2_data, u32 use2_size,
  u8* use3_data, u32 use3_size,
  u8* use4_data, u32 use4_size,
  u8* use5_data, u32 use5_size,
  u8* use6_data, u32 use6_size,
  u8* use7_data, u32 use7_size,
  u8* use8_data, u32 use8_size,
  u32 host
) {
  Mem mem;
  mem.lnk.data = (u64*)lnk_data;
  mem.lnk.size = (u64)lnk_size;
  mem.use[0].data = (u64*)use0_data;
  mem.use[0].size = (u64)use0_size;
  mem.use[1].data = (u64*)use1_data;
  mem.use[1].size = (u64)use1_size;
  mem.use[2].data = (u64*)use2_data;
  mem.use[2].size = (u64)use2_size;
  mem.use[3].data = (u64*)use3_data;
  mem.use[3].size = (u64)use3_size;
  mem.use[4].data = (u64*)use4_data;
  mem.use[4].size = (u64)use4_size;
  mem.use[5].data = (u64*)use5_data;
  mem.use[5].size = (u64)use5_size;
  mem.use[6].data = (u64*)use6_data;
  mem.use[6].size = (u64)use6_size;
  mem.use[7].data = (u64*)use7_data;
  mem.use[7].size = (u64)use7_size;
  mem.use[8].data = (u64*)use8_data;
  mem.use[8].size = (u64)use8_size;
  normal(&mem, (u64)host);
}
