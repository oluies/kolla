// Runs the kolla bundle under Node, so the differential platform can compare a
// JS run against a JVM run declaration by declaration.
//
//   node run.js <export-file> <profile>
//
// Output is the same JSON-per-declaration stream the command line writes with
// --json, which is what makes the two comparable.
const fs = require("fs");
const path = require("path");

require(path.join(__dirname, "main.js"));

const [file, profile] = process.argv.slice(2);
if (!file || !profile) {
  console.error("usage: node run.js <export-file> <profile>");
  process.exit(2);
}

const text = fs.readFileSync(file, "utf8");
const result = kolla.checkJson(text, profile, file, "js");
if (result.error) {
  console.error(result.error);
  process.exit(2);
}
// One write rather than one per line: a large corpus is hundreds of thousands
// of lines and a write syscall each would dominate the measurement.
process.stdout.write(result.lines.join("\n") + "\n");
