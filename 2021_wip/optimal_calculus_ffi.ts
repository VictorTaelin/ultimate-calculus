import * as O from "./optimal_calculus.ts";

const lib_name = "./optimal_calculus.dylib";

// Open library and define exported symbols
const dylib = Deno.dlopen(lib_name, {
  "normal_ffi": {
    parameters: [
      "buffer", "u32",
      "buffer", "u32",
      "buffer", "u32",
      "buffer", "u32",
      "buffer", "u32",
      "buffer", "u32",
      "buffer", "u32",
      "buffer", "u32",
      "buffer", "u32",
      "buffer", "u32",
      "u32"
    ],
    result: "u32",
  },
});

function convert(arr: Uint32Array): Uint8Array {
  return new Uint8Array(arr.buffer);
}

export function normal_ffi(MEM: O.Mem, host: O.Loc): O.Lnk {
  return dylib.symbols.normal_ffi(
    convert(MEM.lnk.data), MEM.lnk.size,
    convert(MEM.use[0].data), MEM.use[0].size,
    convert(MEM.use[1].data), MEM.use[2].size,
    convert(MEM.use[2].data), MEM.use[2].size,
    convert(MEM.use[3].data), MEM.use[3].size,
    convert(MEM.use[4].data), MEM.use[4].size,
    convert(MEM.use[5].data), MEM.use[5].size,
    convert(MEM.use[6].data), MEM.use[6].size,
    convert(MEM.use[7].data), MEM.use[7].size,
    convert(MEM.use[8].data), MEM.use[8].size,
    host) as O.Lnk;
}
