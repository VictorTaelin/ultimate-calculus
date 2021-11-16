export function pad(str : string, len : number) {
  while (str.length < len) {
    str = " " + str;
  }
  return str.slice(-len);
}
