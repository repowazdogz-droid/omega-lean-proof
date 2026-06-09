#!/usr/bin/env node
/**
 * NOT A SHIPPED ROOT — scratch recon for Phase 2 JCS bridge.
 * Run: node lean-proof/scratch/jcs-conformance-test.mjs
 * Requires: npm install in lean-proof/scratch (canonicalize@3.0.0)
 */
import { readFileSync, readdirSync, statSync } from 'node:fs';
import { join, relative } from 'node:path';
import { createHash } from 'node:crypto';
import { execFileSync } from 'node:child_process';
import { fileURLToPath } from 'node:url';
import canonicalize from 'canonicalize';

const __dirname = fileURLToPath(new URL('.', import.meta.url));
const TESTDATA = join(__dirname, 'jcs-testdata');
const OMEGA_CONTRACTS = join(__dirname, '../../omega-contracts');

function hexToUtf8(hexPath) {
  const raw = readFileSync(hexPath, 'utf8').replace(/\s+/g, '');
  return Buffer.from(raw, 'hex').toString('utf8');
}

function hexSha256(s) {
  return createHash('sha256').update(s, 'utf8').digest('hex');
}

function compareVector(name) {
  const input = JSON.parse(readFileSync(join(TESTDATA, `input-${name}.json`), 'utf8'));
  const expected = hexToUtf8(join(TESTDATA, `expected-${name}.hex`));
  const got = canonicalize(input);
  const pass = got === expected;
  return { name, pass, expected, got, expectedLen: expected.length, gotLen: got.length };
}

// --- RFC / cyberphone official vectors ---
const official = ['arrays', 'french', 'structures', 'unicode', 'values', 'weird'].map(compareVector);

// --- Custom probes (Step 1a–c) ---

function utf16KeySortProbe() {
  // Supplementary-plane key vs BMP: UTF-16 code-unit order matters.
  // U+1D400 (MATHEMATICAL BOLD CAPITAL A) = surrogate pair \uD835\uDC00
  // U+0100 (LATIN CAPITAL A WITH MACRON) = single unit \u0100
  // UTF-16: \u0100 (0x0100) < \uD835 (0xD835) because compare first code unit
  // Code-point order would differ for some pairs; this pair tests surrogate vs BMP.
  const obj = {
    '\u0100': 'bmp',
    '\uD835\uDC00': 'math-bold-A',
  };
  const got = canonicalize(obj);
  const utf16Order = canonicalize({ '\u0100': 'bmp', '\uD835\uDC00': 'math-bold-A' });
  const codePointOrder = canonicalize({ '\uD835\uDC00': 'math-bold-A', '\u0100': 'bmp' });
  const jsDefaultSort = Object.keys(obj).sort();
  return {
    name: 'utf16-key-sort-supplementary-vs-bmp',
    got,
    utf16Order,
    codePointOrder,
    jsDefaultSort,
    keysEqual: utf16Order === codePointOrder,
    note: 'RFC 8785 requires UTF-16 code-unit order; JS .sort() uses UTF-16 code units',
  };
}

function utf16FrenchKeysProbe() {
  // From RFC / french.json: locale must not affect order
  const input = JSON.parse(readFileSync(join(TESTDATA, 'input-french.json'), 'utf8'));
  const sortedKeys = Object.keys(input).sort();
  const sortedKeysLocale = Object.keys(input).sort((a, b) => a.localeCompare(b, 'fr'));
  return {
    name: 'french-key-sort-locale-vs-default',
    defaultSort: sortedKeys,
    localeFrSort: sortedKeysLocale,
    differ: sortedKeys.join('|') !== sortedKeysLocale.join('|'),
    canonical: canonicalize(input),
  };
}

function numberProbes() {
  const cases = [
    { label: '1e21', value: 1e21 },
    { label: '1e-7', value: 1e-7 },
    { label: '0.1+0.2', value: 0.1 + 0.2 },
    { label: '-0', value: -0 },
    { label: '9007199254740993', value: 9007199254740993 },
    { label: '9007199254740992', value: 9007199254740992 },
    { label: '333333333.33333329', value: 333333333.33333329 },
    { label: '1E30', value: 1E30 },
    { label: '4.50', value: 4.50 },
    { label: '2e-3', value: 2e-3 },
    { label: '1e-27', value: 1e-27 },
    { label: 'JSON.parse 9007199254740993', value: JSON.parse('9007199254740993') },
  ];
  return cases.map(({ label, value }) => ({
    label,
    input: value,
    jsonStringify: JSON.stringify(value),
    canonicalize: canonicalize(value),
    match: JSON.stringify(value) === canonicalize(value),
  }));
}

function stringEscapeProbes() {
  const cases = [
    { label: 'U+001F', value: '\u001f' },
    { label: 'U+000A newline', value: '\n' },
    { label: 'U+000D cr', value: '\r' },
    { label: 'quote', value: '"' },
    { label: 'backslash', value: '\\' },
    { label: 'slash', value: '/' },
    { label: 'euro U+20AC', value: '\u20ac' },
    { label: 'high surrogate alone', value: '\uD800' },
    { label: 'low surrogate alone', value: '\uDC00' },
    { label: 'lone surrogate in object key', key: '\uD800', value: 'lonely' },
  ];
  const results = [];
  for (const c of cases) {
    try {
      const v = c.key !== undefined ? { [c.key]: c.value } : c.value;
      const out = canonicalize(v);
      results.push({ label: c.label, pass: true, output: out });
    } catch (e) {
      results.push({ label: c.label, pass: false, error: String(e) });
    }
  }
  return results;
}

// --- Step 2: value-domain audit ---

const audit = {
  filesScanned: [],
  numbers: { integers: [], nonIntegers: [], above2p53: [], belowNeg2p53: [] },
  stringsNonAscii: [],
  keysNonAscii: [],
  maxDepth: 0,
  hasArrays: false,
  hasNull: false,
  hasBool: false,
};

const SAFE_INT = 9007199254740991; // 2^53 - 1

function walk(value, path, depth, keyIsAscii = true) {
  if (depth > audit.maxDepth) audit.maxDepth = depth;
  if (value === null) { audit.hasNull = true; return; }
  if (typeof value === 'boolean') { audit.hasBool = true; return; }
  if (typeof value === 'number') {
    if (!Number.isInteger(value)) audit.numbers.nonIntegers.push({ path, value });
    else audit.numbers.integers.push({ path, value });
    if (value > SAFE_INT || value < -SAFE_INT) audit.numbers.above2p53.push({ path, value });
    return;
  }
  if (typeof value === 'string') {
    if (!/^[\x00-\x7F]*$/.test(value)) audit.stringsNonAscii.push({ path, sample: value.slice(0, 40) });
    return;
  }
  if (Array.isArray(value)) {
    audit.hasArrays = true;
    value.forEach((v, i) => walk(v, `${path}[${i}]`, depth + 1));
    return;
  }
  if (typeof value === 'object') {
    for (const k of Object.keys(value)) {
      if (!/^[\x00-\x7F]*$/.test(k)) audit.keysNonAscii.push({ path: `${path}.${k}`, key: k });
      walk(value[k], `${path}.${JSON.stringify(k)}`, depth + 1, /^[\x00-\x7F]*$/.test(k));
    }
  }
}

function scanJsonFile(absPath) {
  try {
    const data = JSON.parse(readFileSync(absPath, 'utf8'));
    audit.filesScanned.push(relative(OMEGA_CONTRACTS, absPath));
    walk(data, relative(OMEGA_CONTRACTS, absPath), 0);
  } catch (e) {
    audit.filesScanned.push(`${relative(OMEGA_CONTRACTS, absPath)} (PARSE ERROR: ${e.message})`);
  }
}

function walkDir(dir) {
  for (const ent of readdirSync(dir)) {
    const p = join(dir, ent);
    const st = statSync(p);
    if (st.isDirectory()) walkDir(p);
    else if (ent.endsWith('.json')) scanJsonFile(p);
  }
}

walkDir(join(OMEGA_CONTRACTS, 'fixtures'));
walkDir(join(OMEGA_CONTRACTS, 'test'));

// omega-demo adapter test fixtures if present
const demoTest = join(__dirname, '../../omega-demo-record-adapter/test/adapter.test.js');
try {
  readFileSync(demoTest, 'utf8'); // existence check
  audit.filesScanned.push('omega-demo-record-adapter/test/adapter.test.js (JS — not JSON-scanned)');
} catch { /* optional */ }

// --- omega-contracts composition hash check ---
let compositionHash = null;
try {
  const { computeContentHash } = await import(join(OMEGA_CONTRACTS, 'dist/encoding.js'));
  const record = JSON.parse(readFileSync(join(OMEGA_CONTRACTS, 'fixtures/composition/expected_record.json'), 'utf8'));
  compositionHash = computeContentHash(record);
} catch (e) {
  compositionHash = `ERROR: ${e.message}`;
}

// --- Output report as JSON for JCS_RECON.md ingestion ---
const report = {
  package: {
    name: 'canonicalize',
    requested: '^3.0.0',
    resolved: '3.0.0',
    integrity: 'sha512-yYLfHyDMIXRyRqsKBRLX023riFLpXY2YOfdtqKXZRZy9qsfOJ9U+4F9YZL7MEzL5+ziN2x2nlBvY/Voi3EBljA==',
    lockfile: 'omega-contracts/package-lock.json',
  },
  officialVectors: official,
  officialPassCount: official.filter((v) => v.pass).length,
  officialFailCount: official.filter((v) => !v.pass).length,
  utf16KeySortProbe: utf16KeySortProbe(),
  utf16FrenchKeysProbe: utf16FrenchKeysProbe(),
  numberProbes: numberProbes(),
  stringEscapeProbes: stringEscapeProbes(),
  valueDomainAudit: {
    ...audit,
    nonIntegerCount: audit.numbers.nonIntegers.length,
    above2p53Count: audit.numbers.above2p53.length,
    nonAsciiStringCount: audit.stringsNonAscii.length,
    nonAsciiKeyCount: audit.keysNonAscii.length,
  },
  compositionHash,
  expectedCompositionHash: readFileSync(join(OMEGA_CONTRACTS, 'fixtures/composition/expected_content_hash.txt'), 'utf8').trim(),
};

// --- Step 6: integer-only corpus (Lean jcsDump vs npm) ---
function runCorpusConformance() {
  const casesDir = join(__dirname, 'jcs-cases');
  const jcsDump = join(__dirname, '..', '.lake/build/bin/jcsDump');
  const files = readdirSync(casesDir).filter((f) => f.endsWith('.json')).sort();
  const rows = [];
  for (const file of files) {
    const abs = join(casesDir, file);
    const obj = JSON.parse(readFileSync(abs, 'utf8'));
    const npm = canonicalize(obj);
    let lean = '';
    let leanError = null;
    try {
      lean = execFileSync(jcsDump, [abs], { encoding: 'utf8' }).replace(/\n$/, '');
    } catch (e) {
      leanError = String(e.stderr || e.message || e);
    }
    rows.push({
      case: file,
      match: !leanError && lean === npm,
      npmSha256: hexSha256(npm),
      leanSha256: leanError ? null : hexSha256(lean),
      leanError,
    });
  }
  const refundPath = join(casesDir, 'refund-escalation-stripped.json');
  const refundCanonical = canonicalize(JSON.parse(readFileSync(refundPath, 'utf8')));
  const refundHash = hexSha256(refundCanonical);
  return {
    passCount: rows.filter((r) => r.match).length,
    failCount: rows.filter((r) => !r.match).length,
    total: rows.length,
    refundHash,
    expectedRefundHash: 'e747c3fdcb2966c6f0fafa4ab3b51274e53c70f1bf44c51c662ff26749996c09',
    rows,
  };
}

report.corpusConformance = runCorpusConformance();

console.log(JSON.stringify(report, null, 2));
