#!/usr/bin/env node
/**
 * JCS corpus: byte-for-byte Lean `jcsEncode` vs npm `canonicalize@3.0.0`.
 * Run from repo root:
 *   cd lean-proof && lake build jcsDump && node scratch/jcs-corpus-conformance.mjs
 */
import { readFileSync, readdirSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import { createHash } from 'node:crypto';
import { execFileSync } from 'node:child_process';
import { fileURLToPath } from 'node:url';
import canonicalize from 'canonicalize';

const __dirname = fileURLToPath(new URL('.', import.meta.url));
const CASES = join(__dirname, 'jcs-cases');
const LEAN_ROOT = join(__dirname, '..');
const JCS_DUMP = join(LEAN_ROOT, '.lake/build/bin/jcsDump');

function sha256(s) {
  return createHash('sha256').update(s, 'utf8').digest('hex');
}

function leanEncode(absPath) {
  return execFileSync(JCS_DUMP, [absPath], {
    cwd: LEAN_ROOT,
    encoding: 'utf8',
    maxBuffer: 10 * 1024 * 1024,
  }).replace(/\n$/, '');
}

function npmEncode(obj) {
  return canonicalize(obj);
}

const files = readdirSync(CASES).filter((f) => f.endsWith('.json')).sort();
const results = [];
let passCount = 0;

for (const file of files) {
  const abs = join(CASES, file);
  const obj = JSON.parse(readFileSync(abs, 'utf8'));
  const npm = npmEncode(obj);
  let lean = '';
  let leanError = null;
  try {
    lean = leanEncode(abs);
  } catch (e) {
    leanError = String(e.stderr || e.message || e);
  }
  const match = leanError ? false : lean === npm;
  if (match) passCount += 1;
  results.push({
    case: file,
    match,
    leanError,
    npmSha256: sha256(npm),
    leanSha256: leanError ? null : sha256(lean),
    npmLen: npm.length,
    leanLen: lean?.length ?? 0,
  });
}

// Refund record content_hash gate (strip content_hash/signature like computeContentHash)
let refundHash = null;
try {
  const refundPath = join(CASES, 'refund-escalation-stripped.json');
  const record = JSON.parse(readFileSync(refundPath, 'utf8'));
  const canonical = npmEncode(record);
  refundHash = sha256(canonical);
} catch (e) {
  refundHash = `ERROR: ${e.message}`;
}

const report = {
  corpusPassCount: passCount,
  corpusFailCount: files.length - passCount,
  corpusTotal: files.length,
  refundContentHash: refundHash,
  expectedRefundHash: 'e747c3fdcb2966c6f0fafa4ab3b51274e53c70f1bf44c51c662ff26749996c09',
  refundHashMatch: refundHash === 'e747c3fdcb2966c6f0fafa4ab3b51274e53c70f1bf44c51c662ff26749996c09',
  results,
};

const outPath = join(__dirname, 'jcs-corpus-results.json');
writeFileSync(outPath, JSON.stringify(report, null, 2));
console.log(JSON.stringify(report, null, 2));
process.exit(report.corpusFailCount === 0 && report.refundHashMatch ? 0 : 1);
