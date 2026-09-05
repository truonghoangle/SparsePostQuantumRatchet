// Generates docs/report/report.pptx, the slide deck for docs/report/plan.md.
// Usage: npm run report-slides
import PptxGenJSImport from "pptxgenjs";
import { fileURLToPath } from "node:url";
import path from "node:path";

// Under NodeNext resolution pptxgenjs is typed as a CJS module namespace whose
// `default` is the class, and at runtime (tsx ESM interop) the default export
// is likewise nested. Resolve both the value and the types structurally.
type PptxModule = typeof PptxGenJSImport;
type PptxCtor = PptxModule extends { default: infer C } ? C : never;
type Pptx = InstanceType<PptxCtor>;
const PptxGenJS = ((PptxGenJSImport as unknown as { default?: unknown }).default ??
  PptxGenJSImport) as unknown as new () => Pptx;
type Slide = ReturnType<Pptx["addSlide"]>;
type TextProps = Extract<Parameters<Slide["addText"]>[0], unknown[]>[number];

const OUT = path.resolve(path.dirname(fileURLToPath(import.meta.url)), "../docs/report/report.pptx");

const NAVY = "1F3864";
const ACCENT = "2E75B6";
const GREY = "595959";
const GREEN = "548235";
const AMBER = "BF9000";
const FONT = "Calibri";
const MONO = "Consolas";

const pptx = new PptxGenJS();
pptx.layout = "LAYOUT_WIDE"; // 13.33 x 7.5 in
pptx.author = "The Beneficial AI Foundation";
pptx.title = "Formal Verification of SPQR in Lean 4";

// Master with title bar and footer.
pptx.defineSlideMaster({
  title: "MAIN",
  background: { color: "FFFFFF" },
  objects: [
    { rect: { x: 0, y: 0, w: "100%", h: 0.9, fill: { color: NAVY } } },
    { placeholder: { options: { name: "title", type: "title", x: 0.5, y: 0.1, w: 12.3, h: 0.7,
        fontFace: FONT, fontSize: 26, bold: true, color: "FFFFFF", valign: "middle" } } },
    { text: { text: "Verifying SPQR in Lean 4  |  snapshot 2026-09-05, main @ 5e77690",
        options: { x: 0.5, y: 7.05, w: 9, h: 0.35, fontFace: FONT, fontSize: 11, color: GREY } } },
  ],
  slideNumber: { x: 12.3, y: 7.05, w: 0.6, h: 0.35, fontFace: FONT, fontSize: 11, color: GREY },
});

type Item = string | { text: string; sub?: boolean; code?: boolean };
type Box = { x?: number; y?: number; w?: number; h?: number; size?: number };

function bullets(slide: Slide, items: Item[], opts: Box = {}) {
  const runs: TextProps[] = items.map((it) => {
    const o = typeof it === "string" ? { text: it } : it;
    return {
      text: o.text,
      options: {
        bullet: o.sub ? { indent: 20 } : true,
        indentLevel: o.sub ? 1 : 0,
        fontFace: o.code ? MONO : FONT,
        fontSize: (opts.size ?? 16) - (o.sub ? 2 : 0),
        color: "222222",
        paraSpaceAfter: 5,
        breakLine: true,
      },
    };
  });
  slide.addText(runs, { x: opts.x ?? 0.6, y: opts.y ?? 1.2, w: opts.w ?? 12.1, h: opts.h ?? 5.6, valign: "top" });
}

function table(slide: Slide, header: string[], rows: string[][], colW: number[],
    opts: { x?: number; y?: number; size?: number; monoCols?: number[] } = {}) {
  const size = opts.size ?? 12;
  const mono = opts.monoCols ?? [];
  const hdr = header.map((t) => ({ text: t, options: { bold: true, color: "FFFFFF", fill: { color: ACCENT }, fontFace: FONT, fontSize: size } }));
  const body = rows.map((r, i) =>
    r.map((t, c) => ({ text: t, options: { fontFace: mono.includes(c) ? MONO : FONT, fontSize: size - 1,
      fill: { color: i % 2 ? "F2F2F2" : "FFFFFF" }, color: "222222" } })));
  slide.addTable([hdr, ...body], { x: opts.x ?? 0.6, y: opts.y ?? 1.2, w: colW.reduce((a, b) => a + b, 0), colW,
    border: { type: "solid", pt: 0.5, color: "BFBFBF" }, valign: "middle" });
}

// Monospace code block.
function code(slide: Slide, lines: string[], box: Box) {
  slide.addText(lines.map((t) => ({ text: t, options: { breakLine: true } })),
    { x: box.x ?? 0.6, y: box.y ?? 1.2, w: box.w ?? 12.1, h: box.h ?? 2, fontFace: MONO, fontSize: box.size ?? 11,
      color: "1E1E1E", fill: { color: "F2F2F2" }, margin: 8, valign: "top" });
}

// One-line takeaway banner for non-experts, just under the title bar.
function takeaway(slide: Slide, text: string) {
  slide.addText(text, { x: 0.6, y: 0.98, w: 12.1, h: 0.42, fontFace: FONT, fontSize: 14, italic: true,
    color: NAVY, fill: { color: "DEEBF7" }, margin: 6, valign: "middle" });
}

// Small section heading inside a slide.
function heading(slide: Slide, text: string, x: number, y: number, w: number, color = ACCENT) {
  slide.addText(text, { x, y, w, h: 0.35, fontFace: FONT, fontSize: 14, bold: true, color });
}

// Plain paragraph.
function para(slide: Slide, text: string, box: Box) {
  slide.addText(text, { x: box.x ?? 0.6, y: box.y ?? 1.2, w: box.w ?? 12.1, h: box.h ?? 1, fontFace: FONT,
    fontSize: box.size ?? 13, color: "222222", valign: "top" });
}

// KPI tile.
function kpi(slide: Slide, value: string, label: string, x: number, y: number, w = 2.3, color = ACCENT) {
  slide.addShape("rect", { x, y, w, h: 1.05, fill: { color: "F2F2F2" }, line: { color, width: 1.5 } });
  slide.addText(value, { x, y: y + 0.05, w, h: 0.55, align: "center", fontFace: FONT, fontSize: 24, bold: true, color });
  slide.addText(label, { x, y: y + 0.58, w, h: 0.45, align: "center", fontFace: FONT, fontSize: 11, color: GREY });
}
// Growth chart built from primitive shapes (renders in every viewer).
// Bars = per-week additions (left axis), line = cumulative (right axis).
function drawGrowthChart(slide: Slide, labels: string[], added: number[], cum: number[],
    box: { x: number; y: number; w: number; h: number }) {
  const padL = 0.55, padR = 0.6, padT = 0.15, padB = 0.55;
  const px = box.x + padL, py = box.y + padT, pw = box.w - padL - padR, ph = box.h - padT - padB;
  const n = labels.length;
  const slot = pw / n;
  const barMax = 40, cumMax = 160;
  const yBar = (v: number) => py + ph - (v / barMax) * ph;
  const yCum = (v: number) => py + ph - (v / cumMax) * ph;

  slide.addShape("rect", { x: px, y: py, w: pw, h: ph, fill: { color: "FFFFFF" }, line: { color: "BFBFBF", width: 0.75 } });
  // gridlines + left/right axis labels
  for (let i = 0; i <= 4; i++) {
    const y = py + ph - (i / 4) * ph;
    if (i > 0) slide.addShape("line", { x: px, y, w: pw, h: 0, line: { color: "E0E0E0", width: 0.5 } });
    slide.addText(String((barMax * i) / 4), { x: box.x, y: y - 0.12, w: padL - 0.05, h: 0.24, align: "right", fontFace: FONT, fontSize: 9, color: ACCENT });
    slide.addText(String((cumMax * i) / 4), { x: px + pw + 0.05, y: y - 0.12, w: padR - 0.05, h: 0.24, align: "left", fontFace: FONT, fontSize: 9, color: NAVY });
  }
  // bars
  // Bars sit in the left 55 % of each slot; the cumulative dot sits at ~78 %, so
  // neither overlaps the other's label.
  const bw = slot * 0.5;
  added.forEach((v, i) => {
    if (v === 0) return;
    const x = px + i * slot + slot * 0.06;
    const h = py + ph - yBar(v);
    slide.addShape("rect", { x, y: yBar(v), w: bw, h, fill: { color: ACCENT }, line: { color: ACCENT } });
    // value at the foot of the bar (white on blue) so the line never crosses it
    if (h >= 0.3) {
      slide.addText(String(v), { x: x - 0.05, y: py + ph - 0.24, w: bw + 0.1, h: 0.22, align: "center", margin: 0, fontFace: FONT, fontSize: 7.5, bold: true, color: "FFFFFF" });
    } else {
      slide.addText(String(v), { x: x - 0.2, y: yBar(v) - 0.24, w: bw + 0.4, h: 0.22, align: "center", fontFace: FONT, fontSize: 8, color: ACCENT });
    }
  });
  // cumulative line
  const labelWeeks = new Set(["W16", "W21", "W23", "W28", "W31", "W32", "W34", "W36"]);
  const pts = cum.map((v, i) => ({ x: px + i * slot + slot * 0.78, y: yCum(v) }));
  for (let i = 1; i < pts.length; i++) {
    const a = pts[i - 1], b = pts[i];
    const goesDown = b.y > a.y; // in slide coords
    slide.addShape("line", {
      x: Math.min(a.x, b.x), y: Math.min(a.y, b.y), w: Math.abs(b.x - a.x), h: Math.abs(b.y - a.y),
      line: { color: NAVY, width: 2.25 }, flipV: !goesDown && a.y !== b.y ? true : false,
    });
  }
  pts.forEach((p, i) => {
    slide.addShape("ellipse", { x: p.x - 0.06, y: p.y - 0.06, w: 0.12, h: 0.12, fill: { color: NAVY }, line: { color: "FFFFFF", width: 1 } });
    // Label only the milestone weeks referenced in the side table, offset to the
    // upper-left of the dot so they never collide with the bar value labels.
    if (labelWeeks.has(labels[i])) {
      // label to the lower-right of the dot (the line rises to the upper-right, bars are to the left)
      const last = i === pts.length - 1;
      slide.addText(String(cum[i]), last
        ? { x: p.x - 0.3, y: p.y - 0.32, w: 0.6, h: 0.22, align: "center", margin: 0, fontFace: FONT, fontSize: 9, bold: true, color: NAVY }
        : { x: p.x + 0.05, y: p.y + 0.02, w: 0.5, h: 0.22, align: "left", margin: 0, fontFace: FONT, fontSize: 9, bold: true, color: NAVY });
    }
  });
  // x labels
  labels.forEach((l, i) => {
    slide.addText(l, { x: px + i * slot, y: py + ph + 0.03, w: slot, h: 0.22, align: "center", fontFace: FONT, fontSize: 8, color: GREY });
  });
  slide.addText("ISO week, 2026", { x: px, y: py + ph + 0.26, w: pw, h: 0.22, align: "center", fontFace: FONT, fontSize: 9, italic: true, color: GREY });
  // legend
  slide.addShape("rect", { x: px + 0.15, y: py + 0.12, w: 0.22, h: 0.14, fill: { color: ACCENT }, line: { color: ACCENT } });
  slide.addText("Rust functions verified that week (left axis)", { x: px + 0.42, y: py + 0.05, w: 4.2, h: 0.28, fontFace: FONT, fontSize: 9, color: "222222" });
  slide.addShape("line", { x: px + 0.15, y: py + 0.48, w: 0.22, h: 0, line: { color: NAVY, width: 2.25 } });
  slide.addShape("ellipse", { x: px + 0.21, y: py + 0.43, w: 0.1, h: 0.1, fill: { color: NAVY }, line: { color: NAVY } });
  slide.addText("Cumulative verified Rust functions (right axis)", { x: px + 0.42, y: py + 0.34, w: 4.2, h: 0.28, fontFace: FONT, fontSize: 9, color: "222222" });
}

// ---- Slide 0: Title -------------------------------------------------------
{
  const s = pptx.addSlide();
  s.background = { color: NAVY };
  s.addText("Formal Verification of SPQR in Lean 4", {
    x: 0.8, y: 1.5, w: 11.7, h: 1.3, fontFace: FONT, fontSize: 40, bold: true, color: "FFFFFF" });
  s.addText("Progress report: machine-checked proofs for Signal's Sparse Post-Quantum Ratchet",
    { x: 0.8, y: 2.8, w: 11.7, h: 0.6, fontFace: FONT, fontSize: 20, color: "BDD7EE" });
  s.addText("Rust  →  Charon  →  Aeneas  →  Lean 4 spec theorems  →  ✓",
    { x: 0.8, y: 3.8, w: 11.7, h: 0.8, fontFace: MONO, fontSize: 22, color: "FFFFFF", fill: { color: "2F4F7F" }, margin: 12, align: "center" });
  s.addText("Every slide starts with a one-line summary in plain language. The details below it are for the technical audience.",
    { x: 0.8, y: 4.9, w: 11.7, h: 0.5, fontFace: FONT, fontSize: 14, italic: true, color: "BDD7EE" });
  s.addText("The Beneficial AI Foundation  |  upstream: signalapp/SparsePostQuantumRatchet  |  data snapshot 2026-09-05",
    { x: 0.8, y: 6.5, w: 11.7, h: 0.4, fontFace: FONT, fontSize: 13, color: "BDD7EE" });
}

// ---- Slide 1: What is SPQR ------------------------------------------------
{
  const s = pptx.addSlide({ masterName: "MAIN" });
  s.addText("1 · What is SPQR, and what are we doing to it?", { placeholder: "title" });
  takeaway(s, "We are proving, with a computer-checked proof, that Signal's post-quantum code does what it is supposed to do.");

  heading(s, "In plain terms", 0.6, 1.5, 6);
  bullets(s, [
    "SPQR (Sparse Post-Quantum Ratchet) is the Rust library Signal uses to keep messages secret even against future quantum computers.",
    "The new quantum-safe keys are big. SPQR cuts them into 32-byte pieces and sends one piece per message. Thanks to a clever encoding, the receiver can rebuild the key even if some pieces are missing.",
    "Tests check a few inputs. A proof checks every possible input, so a whole class of bugs is ruled out for good.",
  ], { x: 0.6, y: 1.85, w: 6.0, h: 4.4, size: 14 });

  heading(s, "For the technical audience", 6.9, 1.5, 6);
  bullets(s, [
    "The Rust code is translated automatically into Lean 4 (Rust → Charon → Aeneas → SrcTranslated/). We never rewrite the code by hand.",
    "For each Rust function we write a theorem in Spqr/Specs/ saying what it must do. Shared math (the field GF(2¹⁶), Lagrange interpolation, …) lives in Spqr/Math/.",
    { text: "f args ⦃ result => postcondition ⦄   — the shape of every theorem; the step* tactic chains the theorems of the functions being called.", code: true },
    "What we trust: the Lean kernel, the Aeneas translation, and a few axioms for external crates (libcrux, prost, bytes).",
    "Project by the Beneficial AI Foundation. Our Lean is Apache-2.0; the Rust and its translation stay AGPL-3.",
  ], { x: 6.9, y: 1.85, w: 5.9, h: 4.4, size: 13 });

  // Pipeline strip
  const stages = ["Rust code (src/)", "Charon: read the code", "Aeneas: translate to Lean", "We write the theorems", "Lean checks the proofs ✓"];
  stages.forEach((t, i) => {
    const x = 0.6 + i * 2.45;
    s.addShape("rect", { x, y: 6.3, w: 2.2, h: 0.55, fill: { color: i === stages.length - 1 ? GREEN : ACCENT }, line: { color: "FFFFFF" } });
    s.addText(t, { x, y: 6.3, w: 2.2, h: 0.55, align: "center", valign: "middle", fontFace: FONT, fontSize: 11, bold: true, color: "FFFFFF" });
    if (i < stages.length - 1) s.addText("➜", { x: x + 2.2, y: 6.3, w: 0.25, h: 0.55, align: "center", valign: "middle", fontSize: 14, color: NAVY });
  });
}
// ---- Slide 2: Results (numbers) -------------------------------------------
{
  const s = pptx.addSlide({ masterName: "MAIN" });
  s.addText("2 · Results so far", { placeholder: "title" });
  takeaway(s, "About half of the functions in the code base are proved correct. The hardest part, the math core, is 100 % done.");

  // KPI row
  kpi(s, "312", "Rust functions to verify\n(tests not counted)", 0.6, 1.5);
  kpi(s, "147", "have a theorem\n(47 %)", 3.05, 1.5);
  kpi(s, "146 / 147", "theorems fully proved\n(no gaps)", 5.5, 1.5, 2.3, GREEN);
  kpi(s, "≈ 555", "Lean theorems and\nhelper lemmas written", 7.95, 1.5);
  kpi(s, "1", "assumption we added\n(the HKDF spec)", 10.4, 1.5, 2.3, AMBER);

  heading(s, "Rust side — what is covered", 0.6, 2.75, 6);
  table(s, ["What", "Numbers"], [
    ["Ordinary functions", "218 in total, 102 have a theorem (47 %)"],
    ["Loop bodies (the translator turns each loop into its own function)", "94 in total, 45 have a theorem"],
    ["The one theorem still with a gap", "decode_state — it calls generated protobuf code we cannot translate yet"],
    ["Not started yet", "165 functions: the v1 state machines, Chain::*, generated protobuf code"],
    ["Files 100 % done", "gf.rs 13/13 · polynomial.rs 32/32 · authenticator 8/8 · kdf · util · unchunked serialize 18/18"],
    ["Files in progress", "chain.rs 11/25 · lib.rs 7/16 · chunked states/serialize 7/9 · mlkem768 2/6"],
  ], [3.2, 3.2], { x: 0.6, y: 3.1, size: 11 });

  heading(s, "Lean side — what we wrote", 7.0, 2.75, 6);
  table(s, ["What", "Numbers"], [
    ["Theorem files / main theorems", "188 files / 312 theorems"],
    ["Small helper lemmas next to the theorems", "107"],
    ["Shared math library (Spqr/Math)", "32 files · 110 lemmas · 21 definitions"],
    ["Helpers for the translator's model and crypto", "18 lemmas"],
    ["Assumptions about external crates", "≈ 40 (libcrux, prost, bytes, core::fmt)"],
    ["Standard Lean axioms used", "propext · Quot.sound · Classical.choice"],
    ["Theorems that indirectly touch a gap", "9 (all via translated generated code)"],
    ["Longest proof file", "Gc.lean — 962 lines"],
  ], [3.1, 2.7], { x: 7.0, y: 3.1, size: 11 });

  para(s, "\"Proved\" means: a theorem about the real translated code, checked by the Lean kernel — not about a simplified model. " +
    "What is left is mostly the protocol state machines and the top-level send / recv functions.", { x: 0.6, y: 6.45, w: 12.1, h: 0.55, size: 12 });
}

// ---- Slide 3: Growth chart ------------------------------------------------
{
  const s = pptx.addSlide({ masterName: "MAIN" });
  s.addText("3 · Verified Rust functions over time (per ISO week)", { placeholder: "title" });
  takeaway(s, "Progress is steady and speeding up: 8 proved functions in mid-April, 147 in early September.");

  // Number of Rust functions whose spec theorem exists today, bucketed by the ISO
  // week in which the file declaring that theorem first entered git.
  // Source: python3 scripts/lib/verified_over_time.py status.json  (147 total).
  const weeks = ["W16", "W17", "W18", "W19", "W20", "W21", "W22", "W23", "W24", "W25", "W26", "W27", "W28", "W29", "W30", "W31", "W32", "W33", "W34", "W35", "W36"];
  const added = [8, 0, 0, 0, 2, 8, 0, 5, 8, 4, 2, 11, 19, 5, 5, 13, 30, 5, 11, 5, 6];
  const cum: number[] = [];
  added.reduce((acc, v) => { cum.push(acc + v); return acc + v; }, 0);

  // The chart is drawn with plain shapes rather than a native <c:chart>: Keynote,
  // QuickLook and other non-PowerPoint viewers drop pptxgenjs' native charts, and
  // this slide has to render everywhere.
  drawGrowthChart(s, weeks, added, cum, { x: 0.6, y: 1.5, w: 8.2, h: 4.9 });

  heading(s, "Milestones", 9.1, 1.5, 3.8);
  table(s, ["Wk", "Cum.", "Milestone"], [
    ["W16", "8", "First proofs: basic field arithmetic, Pt / Poly byte encoding"],
    ["W21", "18", "GF16 constants and constant-time operations"],
    ["W23", "23", "gf.rs finished (division, parallel multiply)"],
    ["W27–28", "67", "Lagrange interpolation core (Slide 5)"],
    ["W31", "90", "Polynomial decoder, chunk byte format"],
    ["W32", "120", "Polynomial encoder, add_chunk (Slide 6), protobuf round-trips, lib.rs API"],
    ["W34", "136", "Authenticator, ChainParams"],
    ["W35–36", "147", "KeyHistory, including gc (Slide 7)"],
  ], [0.7, 0.6, 2.5], { x: 9.1, y: 1.85, size: 10 });
  para(s, "How we counted: for each of the 147 functions that has a theorem today, we looked up the week its theorem file was first added to git. " +
    "The quiet weeks (W17–W19, W22) were spent on groundwork: setting up the translator and building the GF(2¹⁶) field in Lean. The W32 jump is the encoder and the protobuf round-trips landing together.",
    { x: 0.6, y: 6.45, w: 12.1, h: 0.55, size: 11 });
}
// ---- Slide 4: File-by-file ------------------------------------------------
{
  const s = pptx.addSlide({ masterName: "MAIN" });
  s.addText("4 · File-by-file report", { placeholder: "title" });
  takeaway(s, "Four areas: field arithmetic (done), polynomial coding (done), key chain (in progress), byte formats (mostly done).");

  function card(title: string, badge: string, color: string, items: string[], x: number, y: number, w: number, h: number) {
    s.addShape("rect", { x, y, w, h, fill: { color: "FAFAFA" }, line: { color: "BFBFBF", width: 0.75 } });
    s.addShape("rect", { x, y, w, h: 0.4, fill: { color } });
    s.addText(title, { x: x + 0.1, y, w: w - 2.1, h: 0.4, fontFace: MONO, fontSize: 12, bold: true, color: "FFFFFF", valign: "middle", fit: "shrink" });
    s.addText(badge, { x: x + w - 2.0, y, w: 1.85, h: 0.4, fontFace: FONT, fontSize: 11, bold: true, color: "FFFFFF", align: "right", valign: "middle" });
    bullets(s, items, { x: x + 0.05, y: y + 0.45, w: w - 0.1, h: h - 0.5, size: 11 });
  }

  const W = 5.95, H1 = 2.45, H2 = 2.55, X1 = 0.6, X2 = 6.75, Y1 = 1.5, Y2 = 4.05;
  card("src/encoding/gf.rs", "✅ 13 / 13", GREEN, [
    "What it does: add, multiply and divide 16-bit numbers in the finite field GF(2¹⁶). Everything else is built on this.",
    "What we proved: Lean knows this field as a real Mathlib Field. Every Rust operation is proved equal to the textbook field operation — including the 256-entry lookup table and the fast multiply tricks.",
    "Key theorems: reduce_bytes_spec (the whole table is right), div_impl_spec (division is really the inverse), mul2_u16_spec.",
  ], X1, Y1, W, H1);
  card("src/encoding/polynomial.rs  (+ encoding.rs)", "✅ 32 / 32", GREEN, [
    "What it does: the error-correcting code. The key is split into 16 streams of numbers; each stream defines a polynomial; chunk k is those 16 polynomials evaluated at x = k.",
    "What we proved: a math library of 110 lemmas about polynomials and Lagrange interpolation, and theorems for every function — encoder, decoder and the byte format.",
    "Key theorems: lagrange_interpolate (Slide 5), from_complete_points, PolyEncoder::chunk_at, PolyDecoder::add_chunk and its Option<T> wrapper (Slide 6).",
  ], X2, Y1, W, H1);
  card("src/chain.rs", "🟡 11 / 25 (44 %)", AMBER, [
    "What it does: derives the message keys, one after another, and keeps a small history of skipped keys so late messages can still be read. Old entries are garbage-collected.",
    "Done: all of ChainParams, and all of KeyHistory (new, add, remove, gc, get, clear).",
    "Next: ChainEpochDirection (next_key, key, protobuf conversion) and the top-level Chain (add_epoch, send_key, recv_key).",
    "Highlight: gc_spec proves the garbage collector keeps exactly the live keys, no more and no less (Slide 7).",
  ], X1, Y2, W, H2);
  card("serialize.rs · v1/**/serialize.rs · authenticator/serialize.rs", "🟢 32 / 39", ACCENT, [
    "What it does: turns state and messages into bytes and back — a small hand-written wire format plus protobuf conversions for every state struct.",
    "Done: varint and chunk encoding, Message serialize / deserialize, and all 18 protobuf conversions of the unchunked states.",
    "Remaining: 10 protobuf conversions for the chunked states, and the top-level States conversion.",
    "Typical theorem: decoding what you encoded gives back exactly what you started with, plus exact byte-length bounds.",
  ], X2, Y2, W, H2);
}
// ---- Slide 5: lagrange_interpolate ----------------------------------------
{
  const s = pptx.addSlide({ masterName: "MAIN" });
  s.addText("5 · A complex function in polynomial.rs: Poly::lagrange_interpolate", { placeholder: "title" });
  takeaway(s, "Left: the math. Right: the theorem Lean checked about the real Rust code. They say the same thing — through n given points there is exactly one polynomial, and the code finds it.");

  code(s, ["fn lagrange_interpolate(pts: &[Pt]) -> Poly   // \"return a Poly with f(pts[i].x) == pts[i].y for all i; O(N²) work, O(N) space\""],
    { x: 0.6, y: 1.5, w: 12.1, h: 0.4, size: 11 });

  heading(s, "The math, in words", 0.6, 2.0, 6);
  para(s, "Take n points (xᵢ, yᵢ) with different x values. There is exactly one polynomial of degree below n passing through all of them:", { x: 0.6, y: 2.35, w: 5.9, h: 0.45, size: 12 });
  code(s, ["L(x) = Σᵢ yᵢ · ℓᵢ(x),      ℓᵢ(x) = Πⱼ≠ᵢ (x − xⱼ) / (xᵢ − xⱼ)"], { x: 0.6, y: 2.8, w: 5.9, h: 0.4, size: 11 });
  para(s, "The Rust code gets there by a shortcut that avoids division and repeated work:", { x: 0.6, y: 3.25, w: 5.9, h: 0.35, size: 12 });
  bullets(s, [
    "Step 1 — Prepare. Multiply out T(x) = (x − x₀)(x − x₁)…(x − xₙ₋₁) once.",
    "Step 2 — For each point i. Copy T, divide out the factor (x − xᵢ), and scale by yᵢ times the inverse of Πⱼ≠ᵢ (xᵢ − xⱼ). (The inverse is computed as a power, because in this field a^(2¹⁶−2) = 1/a.) The buffer now holds x · yᵢ · ℓᵢ(x).",
    "Step 3 — Add up. Add the buffer into the answer, skipping its lowest coefficient — that skip is the \"divide by x\" for free.",
    "Result: n coefficients, equal to L(x). With no points you get the zero polynomial.",
  ], { x: 0.6, y: 3.6, w: 5.9, h: 3.3, size: 12 });

  heading(s, "The theorem in Lean  (Spqr/Specs/Encoding/Polynomial/Poly/LagrangeInterpolate.lean)", 6.75, 2.0, 6);
  code(s, [
    "@[step]",
    "theorem lagrange_interpolate_spec (pts : Slice Pt)",
    "    (h_len : pts.length + 1 ≤ Usize.max) :",
    "    lagrange_interpolate pts ⦃ (result : Poly) =>",
    "      result.degree = pts.length ∧",
    "      (pts.length = 0 → result.toGF216Poly = 0) ∧",
    "      result.toGF216Poly = lagrangeInterpolantSum pts pts.length ⦄",
    "",
    "-- Spqr/Math/Poly/Lagrange/",
    "def lagrangeInterpolantSum (pts : List Pt) : Nat → GF216[X]",
    "  | 0     => 0",
    "  | n + 1 => lagrangeInterpolantSum pts n +",
    "      (if h : n < pts.length",
    "       then C (lagrangeScaleGF216 (pts.get ⟨n, h⟩) pts) * lagrangeBasisPoly pts n",
    "       else 0)",
    "def lagrangeScaleGF216 (pi : Pt) (pts : List Pt) : GF216 :=",
    "  pi.y.toGF216 * (lagrangeDenomProd pi.x pts 0) ^ (2 ^ 16 - 2)",
    "def lagrangeBasisPoly (pts : List Pt) (i : Nat) : GF216[X] :=",
    "  if i < pts.length then prodLinearFactors pts 0 i * prodLinearFactors pts (i+1) pts.length else 1",
  ], { x: 6.75, y: 2.35, w: 5.95, h: 3.35, size: 9 });
  bullets(s, [
    "Reading the theorem: the list of numbers the Rust code returns, read as a polynomial (toGF216Poly), is exactly L(x) — every coefficient, not just the values at the given points.",
    "The proof follows the three steps of the code: one lemma for the inner loop, one for the outer loop (its invariant says the buffer really holds x · yᵢ · ℓᵢ(x)), then cancel the common factor.",
    "The only assumption is that the point count fits in a machine integer. The code's own hint 'at most 36 points' is not needed for correctness.",
  ], { x: 6.75, y: 5.75, w: 5.95, h: 1.3, size: 10 });
}
// ---- Slide 6: Option<T>::add_chunk 2x2 -----------------------------------
{
  const s = pptx.addSlide({ masterName: "MAIN" });
  s.addText("6 · Using polynomial.rs from encoding.rs: Option<T>::add_chunk", { placeholder: "title" });
  takeaway(s, "This function is just a wrapper: open the box, let the decoder inside do the work, close the box. We prove the wrapper once, for any decoder, then plug in the polynomial decoder.");

  code(s, [
    "impl<T: Decoder> Decoder for Option<T> {                       // src/encoding.rs",
    "    #[hax_lib::requires(self.is_some())]",
    "    fn add_chunk(&mut self, chunk: &Chunk) { let mut tmp = self.take().unwrap(); T::add_chunk(&mut tmp, chunk); *self = Some(tmp); } }",
  ], { x: 0.6, y: 1.47, w: 12.1, h: 0.72, size: 9 });

  const L = 0.6, R = 6.75, W = 5.95, Y1 = 2.25, Y2 = 3.75;
  heading(s, "Without polynomial.rs — works for any decoder T", L, Y1, W, GREY);
  heading(s, "With polynomial.rs — the decoder is PolyDecoder", R, Y1, W, GREEN);
  s.addText("plug in the PolyDecoder theorem ➜", { x: 6.05, y: 4.6, w: 1.2, h: 0.8, fontFace: FONT, fontSize: 8, italic: true, color: GREEN, align: "center", valign: "middle" });

  para(s, "In words: the box must not be empty. Take the decoder out, give it the chunk, put it back. " +
    "So afterwards the box is still full, and anything that is true about the decoder's result is also true about what is now in the box. " +
    "We do not need to know what the decoder actually does.", { x: L, y: Y1 + 0.35, w: W - 0.6, h: 1.15, size: 11 });
  para(s, "In words: now the decoder is the polynomial one. Each of the 16 pairs of bytes in the chunk becomes one point (x = chunk number, y = the two bytes) for polynomial number j. " +
    "The point is kept, in sorted order, only if it is still useful — either the chunk number is small, or that polynomial does not have enough points yet. Otherwise nothing changes. " +
    "The counters pts_needed and is_complete never change.", { x: R, y: Y1 + 0.35, w: W, h: 1.15, size: 11 });

  code(s, [
    "theorem add_chunk_spec_lift",
    "    {T : Type} (DecoderInst : encoding.Decoder T) (self : Option T)",
    "    (chunk : encoding.Chunk)",
    "    (h_some : self.isSome)",
    "    (P : T → Prop)",
    "    (h_inner : ∀ tmp, self = some tmp →",
    "        DecoderInst.add_chunk tmp chunk ⦃ (r : T) => P r ⦄) :",
    "    add_chunk DecoderInst self chunk ⦃ (result : Option T) =>",
    "      ∃ tmp', result = some tmp' ∧ P tmp' ⦄ := by",
    "  unfold add_chunk",
    "  simp only [Aeneas.Std.core.option.Option.take]",
    "  step with Aeneas.Std.core.option.Option.unwrap.spec as ⟨tmp, h_eq⟩",
    "  have h_post := h_inner tmp h_eq",
    "  step with h_post",
    "  grind",
    "",
    "-- P can be any property of the inner decoder.",
    "-- The wrapper simply passes it through, wrapped in `some`.",
  ], { x: L, y: Y2, w: W, h: 3.2, size: 8.5 });
  code(s, [
    "theorem add_chunk_spec_poly_decoder (pd0 : PolyDecoder) (chunk : encoding.Chunk)",
    "    (h_overflow : chunk.index * 16 + 16 ≤ Usize.max)",
    "    (h_push_cap : ∀ k < 16, (pd0.pts[k]!).length + 17 ≤ Usize.max) :",
    "    add_chunk PolyDecoder.Insts.SpqrEncodingDecoder (some pd0) chunk ⦃ result =>",
    "      ∃ pd, result = some pd ∧",
    "        pd.pts_needed = pd0.pts_needed ∧ pd.is_complete = pd0.is_complete ∧",
    "        ∃ selfs : Nat → PolyDecoder, selfs 0 = pd0 ∧ selfs 16 = pd ∧",
    "          ∀ j < 16,",
    "            let total_idx := chunk.index.val * 16 + j",
    "            let poly := total_idx % 16;  let poly_idx := total_idx / 16",
    "            let np := pd0.pts_needed.val / 16 + (if poly < pd0.pts_needed.val % 16 then 1 else 0)",
    "            (selfs (j+1)).pts_needed = pd0.pts_needed ∧ (selfs (j+1)).is_complete = pd0.is_complete ∧",
    "            poly < 16 ∧ poly_idx = chunk.index.val ∧",
    "            ∃ p : Pt, p.x.value.val = poly_idx ∧",
    "              p.y.value.val = chunk.data[j*2]! * 256 + chunk.data[j*2+1]! ∧",
    "              (if poly_idx < np ∨ ((selfs j).pts.val[poly]!).val.length < np then",
    "                 (∀ k ≠ poly, (selfs (j+1)).pts[k]! = (selfs j).pts.val[k]!) ∧",
    "                 IsSortedPushResult ((selfs j).pts.val[poly]!).val ((selfs (j+1)).pts.val[poly]!).val p",
    "               else selfs (j+1) = selfs j) ⦄ := by",
    "  apply add_chunk_spec_lift PolyDecoder.Insts.SpqrEncodingDecoder (some pd0) chunk (by simp)",
    "  intro tmp h_eq; simp only [Option.some.injEq] at h_eq; rw [h_eq] at h_push_cap; rw [h_eq]",
    "  exact PolyDecoder.Insts.SpqrEncodingDecoder.add_chunk_spec tmp chunk h_overflow h_push_cap",
  ], { x: R, y: Y2, w: W, h: 3.2, size: 7.5 });
}
// ---- Slide 7a: gc — what it does and why it is hard -----------------------
{
  const s = pptx.addSlide({ masterName: "MAIN" });
  s.addText("7 · Case study: specifying KeyHistory::gc in chain.rs  (1/2)", { placeholder: "title" });
  takeaway(s, "\"Delete the old keys\" is 20 lines of Rust and 962 lines of Lean. The previous verification tool (hax) had skipped this function as too hard.");

  heading(s, "Rust (src/chain.rs 145–168)", 0.6, 1.5, 6);
  code(s, [
    "#[hax_lib::opaque] // ordering of slices needed",
    "fn gc(&mut self, current_key: u32, params: &pqrpb::ChainParams) {",
    "  if self.data.len() >= params.trim_size() * Self::KEY_SIZE {",
    "    assert!(current_key >= params.max_ooo_keys_or_default());",
    "    let trim_horizon = &(current_key - params.max_ooo_keys_or_default())",
    "                          .to_be_bytes()[..];",
    "    let mut i = 0;",
    "    while i < self.data.len() {",
    "      if trim_horizon.cmp(&self.data[i..i + 4]) == Ordering::Greater {",
    "        self.remove(i, params);  // swap-remove: last record → slot i; i NOT advanced",
    "      } else { i += Self::KEY_SIZE; }",
    "} } }",
  ], { x: 0.6, y: 1.85, w: 6.0, h: 2.6, size: 9 });
  para(s, "In words: the history is one long byte array. Every 36 bytes is one record: a 4-byte key number followed by a 32-byte key. " +
    "When the array gets too long, every record whose number is older than current_key − max_ooo is thrown away.",
    { x: 0.6, y: 4.5, w: 6.0, h: 0.6, size: 11 });

  heading(s, "Why the theorem is hard to state", 6.9, 1.5, 6);
  bullets(s, [
    "Everything is bytes. The theorem cannot say \"key number ≥ horizon\"; it has to talk about every 36th position and compare 4 bytes at a time. The fact that comparing bytes is the same as comparing numbers must itself be proved.",
    "Deleting reorders the list. A record is deleted by moving the last record into its slot — and that moved record may itself be old. So a simple \"everything before position i is fine\" invariant is false.",
    "What does \"correct\" mean? Three things: (1) every kept record is still live, (2) every live record is kept, (3) nothing is duplicated. To state (3) we need an explicit one-to-one matching between old and new positions.",
    "Two loops, two platforms. One lemma per loop step, one for the whole loop (12 facts kept true at every step), and a top-level theorem for 32-bit and for 64-bit machines.",
  ], { x: 6.9, y: 1.85, w: 5.9, h: 3.3, size: 11 });

  heading(s, "Where the proof effort went", 0.6, 5.15, 12);
  bullets(s, [
    "The one-to-one matching has to be rebuilt after every deletion, and three small helper lemmas were needed just to go back and forth between \"these byte ranges are equal\" and \"these bytes are equal\".",
    "The byte comparison is a function that could, in principle, fail. A separate lemma shows it never does, so the proof can split on its three outcomes.",
    "Overflow arithmetic: the threshold is (max_ooo · 11 / 10 + 1) · 36, so max_ooo must be small enough — under about 108 million on 32-bit, under about 390 million on 64-bit (the bound the Rust code itself assumes).",
  ], { x: 0.6, y: 5.5, w: 12.1, h: 1.5, size: 11 });
}
// ---- Slide 7b: gc — spec history, flawed preconditions, examples ----------
{
  const s = pptx.addSlide({ masterName: "MAIN" });
  s.addText("7 · Case study: specifying KeyHistory::gc in chain.rs  (2/2)", { placeholder: "title" });
  takeaway(s, "The first version of the theorem was true, but its conditions were so strict it could never be used. The final version says exactly what the code guarantees — no more, no less.");

  heading(s, "How the theorem evolved (Spqr/Specs/Chain/KeyHistory/Gc.lean)", 0.6, 1.5, 12);
  table(s, ["Date", "Commit", "What the theorem assumed about current_key", "What it promised", "Size"], [
    ["Aug 25", "7886560 (draft)", "always: current_key ≥ max_ooo_keys AND current_key ≥ 2000", "kept records are live; each comes from somewhere", "~480 lines"],
    ["Aug 29", "201b82d", "same", "+ every live record is kept", "+108 / −31"],
    ["Aug 29", "036857f", "same", "+ a 64-bit version", "—"],
    ["Aug 31", "aa4962d · PR #491", "only when the history is long enough to be trimmed: current_key ≥ max_ooo", "+ one-to-one matching (no duplicates)", "962 lines"],
  ], [0.8, 1.7, 4.6, 3.6, 1.4], { x: 0.6, y: 1.85, size: 11, monoCols: [1] });

  heading(s, "What was wrong with the first conditions", 0.6, 3.75, 6, AMBER);
  bullets(s, [
    "The \"current_key ≥ 2000\" condition only made sense when the default setting is used (max_ooo_keys = 0 means 2000). But it was required always. With max_ooo_keys = 10 and current_key = 500 — perfectly valid — the theorem could not be used.",
    "The conditions were also required when gc does nothing. If the history is short, gc returns at once and never checks anything. But the theorem still demanded the bound, so it could not be used by the caller, which runs gc on every single key — starting from key 0.",
    "A concrete case: default settings, one stored key, current_key = 7. The Rust code returns immediately. The draft theorem needs 2000 ≤ 7, which is false — so the caller's proof is stuck.",
  ], { x: 0.6, y: 4.1, w: 6.0, h: 2.9, size: 11 });

  heading(s, "The fix — and why the one-to-one matching matters", 6.9, 3.75, 6, GREEN);
  code(s, [
    "(h_key_ge : let max_ooo := if 0#u32 < params.max_ooo_keys",
    "                            then params.max_ooo_keys.val else 2000",
    "            let trim_threshold := (max_ooo * 11 / 10 + 1) * 36",
    "            trim_threshold ≤ self.data.length → max_ooo ≤ current_key.val)",
  ], { x: 6.9, y: 4.1, w: 5.9, h: 0.95, size: 9 });
  bullets(s, [
    "The fix: ask for the bound only in the case where the code actually needs it — exactly like the assert! in the Rust code. The default value is folded into max_ooo, so one condition covers both settings.",
    "Why the matching matters: take records [A:5, B:1, C:9] and horizon 3. The loop deletes B by moving C into its slot, giving [A, C]. \"All kept are live\" and \"all live are kept\" would also accept the wrong answers [A, C, C] or [A, A]. Only the one-to-one matching rules those out — and that is what the later proof of get needs (\"a key is found exactly once\").",
  ], { x: 6.9, y: 5.1, w: 5.9, h: 1.9, size: 11 });
}

// ---- Slide 8: the bridge — top-level interface in src/lib.rs ---------------
{
  const s = pptx.addSlide({ masterName: "MAIN" });
  s.addText("8 · The bridge: the top-level interface in src/lib.rs", { placeholder: "title" });
  takeaway(s, "lib.rs is the only part an application talks to. Its small helpers are proved; the three big entry points — initial_state, send, recv — are next, and everything they call is already done.");

  // Left: what the interface is, in plain words.
  heading(s, "What the bridge does", 0.6, 1.5, 6);
  bullets(s, [
    "An application never sees chains, polynomials or key histories. It sees only bytes: a serialized state, a serialized message, and (sometimes) a secret.",
    "Three entry points do all the work: initial_state creates a state, send produces a message and a key, recv reads a message and returns the new state and key.",
    "Around them sit small helpers: reading the state bytes (decode_state), asking which protocol version is in use (current_version), and unpacking the returned secret (SecretOutput).",
    "This is the layer where every proved piece must fit together — a wrong bridge would make the rest of the proofs useless to the application.",
  ], { x: 0.6, y: 1.85, w: 6.0, h: 2.7, size: 12 });

  heading(s, "The public API (src/lib.rs)", 0.6, 4.45, 6);
  code(s, [
    "pub fn initial_state(params: Params) -> Result<SerializedState, Error>",
    "pub fn send<R: Rng + CryptoRng>(state: &SerializedState, rng: &mut R)",
    "                                        -> Result<Send, Error>",
    "pub fn recv(state: &SerializedState, msg: &SerializedMessage)",
    "                                        -> Result<Recv, Error>",
    "pub fn current_version(state: &SerializedState) -> Result<CurrentVersion, Error>",
    "pub fn empty_state() -> SerializedState",
  ], { x: 0.6, y: 4.8, w: 6.0, h: 1.45, size: 9 });

  // Right: status table.
  heading(s, "Status of lib.rs: 16 functions, 7 with theorems (tests excluded)", 6.9, 1.5, 6);
  table(s, ["Function", "Status", "What the theorem says"], [
    ["empty_state", "✅ proved", "returns the empty byte string"],
    ["SecretOutput::{send_secret, recv_secret, secret, has_secret}", "✅ proved (4)", "exactly which variant yields a secret"],
    ["current_version", "✅ proved", "empty → V0 and negotiation done; else the decoded state's version, or StateDecode"],
    ["decode_state", "🟡 1 sorry", "empty → default state; else decode/encode round-trip — blocked on prost code (#102)"],
    ["initial_state, init_inner", "⬜ next", "state bytes contain the right version, direction, chain params"],
    ["send, recv", "⬜ next", "the top-level correctness statements"],
    ["chain_from*, msg_version, state_version, Direction::switch", "⬜ next", "small helpers used by send / recv"],
  ], [2.5, 1.0, 2.5], { x: 6.9, y: 1.85, size: 9, monoCols: [0] });

  heading(s, "Why the big three are last", 6.9, 5.45, 6, AMBER);
  bullets(s, [
    "They depend on everything else: the chain (11/25 done), the v1 state machine, protobuf decoding, and the KEM. We verified bottom-up so each layer's theorem is ready when its caller needs it.",
    "The blocker is shared: protobuf encode/decode is generated code that the translator replaces with sorry. Specifying it once unblocks decode_state, initial_state, send and recv together.",
  ], { x: 6.9, y: 5.8, w: 5.9, h: 1.2, size: 11 });
}

// ---- Slide 9: closing — architecture & what's next -------------------------
{
  const s = pptx.addSlide({ masterName: "MAIN" });
  s.addText("9 · Closing: the bridge in context — architecture & what's next", { placeholder: "title" });
  takeaway(s, "The bridge is the capstone: every layer below is being proved so these five functions can carry machine-checked guarantees to the application.");

  // Left: layered architecture diagram built from stacked rounded rectangles.
  heading(s, "End-to-end architecture", 0.6, 1.5, 5.8);

  const layers: { label: string; detail: string; fill: string; textColor?: string }[] = [
    { label: "Application  (Signal app / FFI / language binding)", detail: "Sees only opaque byte vectors — never touches internals", fill: "DEEBF7" },
    { label: "src/lib.rs  —  5 public functions", detail: "initial_state · send · recv · current_version · empty_state", fill: ACCENT, textColor: "FFFFFF" },
    { label: "Internal modules  (47 % specified)", detail: "chain · v1 · authenticator · encoding · kdf · serialize · incremental_mlkem768", fill: "E2EFDA" },
    { label: "SrcTranslated/  (Aeneas-generated Lean 4 model)", detail: "Funs.lean · Types.lean — mechanically extracted from Rust via Charon → Aeneas", fill: "FFF2CC" },
    { label: "Spqr/Specs/ + Spqr/Math/  (hand-written proofs)", detail: "147 / 312 functions specified · 146 fully proved · 419 spec theorems + 110 math theorems", fill: NAVY, textColor: "FFFFFF" },
  ];

  const boxX = 0.8;
  const boxW = 5.4;
  const boxH = 0.72;
  const gap = 0.12;
  const startY = 1.95;

  layers.forEach((layer, i) => {
    const y = startY + i * (boxH + gap);
    s.addShape("roundRect" as any, { x: boxX, y, w: boxW, h: boxH, fill: { color: layer.fill },
      rectRadius: 0.08, line: { color: "BFBFBF", width: 0.75 } } as any);
    s.addText(layer.label, { x: boxX + 0.15, y, w: boxW - 0.3, h: boxH * 0.52,
      fontFace: FONT, fontSize: 12, bold: true, color: layer.textColor ?? "222222", valign: "bottom" });
    s.addText(layer.detail, { x: boxX + 0.15, y: y + boxH * 0.45, w: boxW - 0.3, h: boxH * 0.5,
      fontFace: FONT, fontSize: 9, color: layer.textColor ?? GREY, valign: "top" });
  });

  // Arrows between layers.
  for (let i = 0; i < layers.length - 1; i++) {
    const y1 = startY + i * (boxH + gap) + boxH;
    const y2 = y1 + gap;
    const midX = boxX + boxW / 2;
    s.addShape("line" as any, { x: midX, y: y1, w: 0, h: y2 - y1,
      line: { color: NAVY, width: 1.5, endArrowType: "triangle" } } as any);
  }

  // Right: what's next + key message.
  heading(s, "What's next", 6.9, 1.5, 5.5);
  table(s, ["Milestone", "Impact"], [
    ["Specify protobuf encode/decode\n(unblocks prost sorry — issue #102)", "Unblocks decode_state, initial_state, send, recv in one shot"],
    ["Specify initial_state", "Proves the session is created with correct version, direction, chain params"],
    ["Specify send + recv", "End-to-end: send/recv round-trip produces matching keys for all inputs"],
    ["Remaining chain functions\n(11 / 25 → 25 / 25)", "Complete the key-management layer; needed transitively by send/recv proofs"],
    ["v1/chunked/* specs", "Largest remaining module — erasure-code state machine"],
  ], [2.6, 3.3], { x: 6.9, y: 1.85, size: 10 });

  heading(s, "Key takeaway", 6.9, 5.2, 5.5, GREEN);
  bullets(s, [
    "The bridge is the last layer, not the first — by design. Bottom-up verification means each callee's theorem is ready when its caller needs it.",
    "Once the protobuf blocker is resolved, the three big entry points can be specified by composing the 146 theorems already proved below them.",
    "Goal: \"for all valid inputs, send then recv yields matching keys and a decodable successor state\" — a statement no amount of testing can make.",
  ], { x: 6.9, y: 5.55, w: 5.9, h: 1.6, size: 11 });
}

await pptx.writeFile({ fileName: OUT });

console.log(`Wrote ${OUT}`);
