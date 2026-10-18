// A browser smoke test: loads the published page in a real browser, drives it
// the way a person would, and prints the same JSON stream the command line
// writes with --json.
//
//   node smoke.js <bundle-dir> <export-file> <profile>
//
// `difftest` parses the output and compares it to the JVM run declaration by
// declaration, so this is a comparison rather than an assertion that the page
// did not crash. Playwright is a development dependency, fetched with
// `npx playwright install chromium`; the test reports rather than fails when it
// is absent, because a machine without it has not found a bug.
//
// Exit codes: 0 when the page behaved, whatever the verdicts were, 1 when it
// did not, 2 on misuse, 3 when Playwright is missing. A rejected declaration is
// not a failure here — it is in the output, where difftest reads it.
const fs = require("fs");
const http = require("http");
const path = require("path");

const [bundleDir, exportFile, profile] = process.argv.slice(2);
if (!bundleDir || !exportFile || !profile) {
  console.error("usage: node smoke.js <bundle-dir> <export-file> <profile>");
  process.exit(2);
}

let chromium;
try {
  ({ chromium } = require("playwright"));
} catch (e) {
  console.error("playwright is not installed: npx playwright install chromium");
  process.exit(3);
}

const types = { ".html": "text/html", ".js": "text/javascript", ".map": "application/json" };

function serve(dir) {
  return new Promise(resolve => {
    const server = http.createServer((req, res) => {
      const name = req.url === "/" ? "/index.html" : req.url.split("?")[0];
      const file = path.join(dir, path.normalize(name).replace(/^(\.\.[/\\])+/, ""));
      fs.readFile(file, (err, body) => {
        if (err) { res.writeHead(404); res.end(); return; }
        res.writeHead(200, { "content-type": types[path.extname(file)] || "application/octet-stream" });
        res.end(body);
      });
    });
    server.listen(0, "127.0.0.1", () => resolve(server));
  });
}

(async () => {
  const server = await serve(bundleDir);
  const port = server.address().port;
  const browser = await chromium.launch();
  let code = 0;
  try {
    const page = await browser.newPage();
    const problems = [];
    page.on("pageerror", e => problems.push(`page error: ${e.message}`));
    page.on("console", m => { if (m.type() === "error") problems.push(`console: ${m.text()}`); });

    await page.goto(`http://127.0.0.1:${port}/index.html`, { waitUntil: "load" });

    const text = fs.readFileSync(exportFile, "utf8");

    // Drive the page itself, not just the exported function: fill the box,
    // pick the profile and press the button, then wait for the banner to
    // settle. This is what tells us the sliced loop terminates.
    await page.selectOption("#profile", profile);
    // Not page.fill: it types the value through the input pipeline, which takes
    // minutes for a multi-megabyte export. The page reads #source.value when
    // the button is pressed and listens for no input event, so assigning it is
    // the same thing to the code under test.
    await page.evaluate(t => { document.getElementById("source").value = t; }, text);
    await page.click("#check");
    await page.waitForFunction(
      () => !["running", "idle"].includes(document.getElementById("verdict").className),
      null,
      { timeout: 600000 }
    );

    const shown = await page.evaluate(() => ({
      verdict: document.getElementById("verdict").className,
      counts: document.getElementById("counts").textContent,
      status: document.getElementById("status").textContent,
    }));

    // The verdicts themselves, in the format difftest reads.
    const result = await page.evaluate(
      ([t, p, src]) => window.kolla.checkJson(t, p, src, "browser"),
      [text, profile, exportFile]
    );
    if (result.error) throw new Error(result.error);

    const summary = JSON.parse(result.lines[result.lines.length - 1]);
    // The page and the function have to agree, or the page is showing
    // something the checker did not conclude.
    const expected = `${summary.counts.accepted} accepted, ${summary.counts.rejected} rejected, ` +
      `${summary.counts.carriedOver} carried over, ${summary.counts.errored} errored`;
    if (shown.counts !== expected) {
      problems.push(`the page shows "${shown.counts}" but the checker returned "${expected}"`);
    }
    const wantVerdict = summary.ok ? "accepted" : "rejected";
    if (shown.verdict !== wantVerdict) {
      problems.push(`the page shows "${shown.verdict}" but the checker returned "${wantVerdict}"`);
    }

    if (problems.length > 0) {
      problems.forEach(p => console.error(p));
      code = 1;
    } else {
      process.stdout.write(result.lines.join("\n") + "\n");
    }
  } catch (e) {
    console.error(String(e && e.stack ? e.stack : e));
    code = 1;
  } finally {
    await browser.close();
    server.close();
  }
  process.exit(code);
})();
