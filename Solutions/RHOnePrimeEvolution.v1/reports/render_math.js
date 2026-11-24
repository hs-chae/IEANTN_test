// Build-time renderer only. Reports have native static MathML and no CDN/runtime dependency.
const fs = require('fs');
const katex = require(process.argv[2]);
const formulas = JSON.parse(fs.readFileSync(0, 'utf8'));
const out = {};
for (const [key, tex] of Object.entries(formulas)) {
  out[key] = katex.renderToString(tex, {
    output: 'mathml', displayMode: true, throwOnError: true,
    strict: 'error', trust: false
  });
}
process.stdout.write(JSON.stringify(out));
