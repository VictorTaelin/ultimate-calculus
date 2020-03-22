#!/usr/bin/env node

var fs = require("fs");
var ult = require(".");
var name = process.argv[2];

if (!name) {
  console.log("Usage:");
  console.log("- ult <file>.ult : eval Ultimate-Calculus term");
  console.log("- ult <file>.lam : eval Lambda-Calculus term");
  process.exit();
};

try {
  var file = fs.readFileSync(name, "utf8");
} catch (e) {
  console.log("Couldn't open file: " + name);
  process.exit();
}

// Lambda mode
if (name.indexOf(".lam") !== -1) {
  var {term,stat} = ult.normalize(ult.parse_lambda(file));
  console.log(ult.show_lambda(term));
  console.log(JSON.stringify(stat));
} else {
  var {term,stat} = ult.normalize(ult.parse(file));
  console.log(ult.show(term));
  console.log(JSON.stringify(stat));
};
