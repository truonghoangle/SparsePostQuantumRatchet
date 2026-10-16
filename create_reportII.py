#!/usr/bin/env python3
"""Generate reportII.pptx: integrated 45-minute seminar deck
'From AI-Assisted Verification to Security Defect Discovery'.

Merges the pedagogical narrative of reportI.pptx (concepts, workflow,
takeaways) with the concrete SPQR evidence of report.pptx (figures,
defect data, D21 case study). Each conceptual slide is immediately
followed by the project evidence that illustrates it."""

from PIL import Image
from pptx import Presentation
from pptx.util import Inches, Pt
from pptx.dml.color import RGBColor
from pptx.enum.shapes import MSO_SHAPE
from pptx.enum.text import PP_ALIGN

NAVY = RGBColor(0x1F, 0x2A, 0x44)
ACCENT = RGBColor(0x2E, 0x86, 0xC1)
GREY = RGBColor(0x55, 0x55, 0x55)
LIGHT = RGBColor(0xF2, 0xF4, 0xF7)
WHITE = RGBColor(0xFF, 0xFF, 0xFF)
RED = RGBColor(0xC0, 0x39, 0x2B)
GREEN = RGBColor(0x1E, 0x84, 0x49)
PALE = RGBColor(0xBF, 0xD4, 0xEA)

FIGS = "/Users/hoangtruong/Documents/lean/Max/SparsePostQuantumRatchet/.tmp/figs"
OUT = "/Users/hoangtruong/Documents/lean/Max/SparsePostQuantumRatchet/reportII.pptx"
TOTAL = 23
DECK_TITLE = "From AI-Assisted Verification to Security Defect Discovery"

prs = Presentation()
prs.slide_width = Inches(13.333)
prs.slide_height = Inches(7.5)
BLANK = prs.slide_layouts[6]
W = prs.slide_width
_counter = [0]


# ----------------------------------------------------------------- helpers
def add_text(slide, x, y, w, h, text, size=18, bold=False, color=NAVY,
             align=PP_ALIGN.LEFT, font="Calibri"):
    tb = slide.shapes.add_textbox(x, y, w, h)
    tf = tb.text_frame
    tf.word_wrap = True
    lines = text if isinstance(text, list) else [text]
    lines = [part for line in lines for part in line.split("\n")]
    for i, line in enumerate(lines):
        p = tf.paragraphs[0] if i == 0 else tf.add_paragraph()
        p.alignment = align
        r = p.add_run()
        r.text = line
        r.font.size = Pt(size)
        r.font.bold = bold
        r.font.color.rgb = color
        r.font.name = font
    return tb


def add_bullets(slide, x, y, w, h, items, size=18, color=NAVY, numbered=False,
                bullet_color=None):
    tb = slide.shapes.add_textbox(x, y, w, h)
    tf = tb.text_frame
    tf.word_wrap = True
    for i, item in enumerate(items):
        p = tf.paragraphs[0] if i == 0 else tf.add_paragraph()
        prefix = f"{i + 1}. " if numbered else "•  "
        r0 = p.add_run()
        r0.text = prefix
        r0.font.size = Pt(size)
        r0.font.color.rgb = bullet_color or color
        r0.font.name = "Calibri"
        r = p.add_run()
        r.text = item
        r.font.size = Pt(size)
        r.font.color.rgb = color
        r.font.name = "Calibri"
        p.space_after = Pt(6)
    return tb


def add_box(slide, x, y, w, h, fill=LIGHT, line=None):
    shp = slide.shapes.add_shape(MSO_SHAPE.ROUNDED_RECTANGLE, x, y, w, h)
    shp.fill.solid()
    shp.fill.fore_color.rgb = fill
    if line is None:
        shp.line.fill.background()
    else:
        shp.line.color.rgb = line
    shp.adjustments[0] = 0.05
    shp.text_frame.text = ""
    return shp


def add_code(slide, x, y, w, h, code, size=14):
    box = add_box(slide, x, y, w, h, fill=RGBColor(0x2B, 0x2B, 0x2B))
    tf = box.text_frame
    tf.word_wrap = True
    tf.margin_left = tf.margin_right = Inches(0.2)
    for i, line in enumerate(code.split("\n")):
        p = tf.paragraphs[0] if i == 0 else tf.add_paragraph()
        p.alignment = PP_ALIGN.LEFT
        r = p.add_run()
        r.text = line
        r.font.size = Pt(size)
        r.font.name = "Courier New"
        r.font.color.rgb = RGBColor(0xE8, 0xE8, 0xE8)
    return box


def header(slide, title, tag=None):
    bar = slide.shapes.add_shape(MSO_SHAPE.RECTANGLE, 0, 0, W, Inches(1.1))
    bar.fill.solid()
    bar.fill.fore_color.rgb = NAVY
    bar.line.fill.background()
    size = 30 if len(title) <= 46 else 26
    add_text(slide, Inches(0.5), Inches(0.2), Inches(10.5), Inches(0.8),
             title, size=size, bold=True, color=WHITE)
    if tag:
        add_text(slide, Inches(9.3), Inches(0.35), Inches(3.6), Inches(0.5),
                 tag, size=13, color=PALE, align=PP_ALIGN.RIGHT)


def footer(slide):
    _counter[0] += 1
    add_text(slide, Inches(0.5), Inches(7.0), Inches(9), Inches(0.4),
             DECK_TITLE, size=10, color=GREY)
    add_text(slide, Inches(12.0), Inches(7.0), Inches(0.9), Inches(0.4),
             f"{_counter[0]} / {TOTAL}", size=10, color=GREY, align=PP_ALIGN.RIGHT)


def new_slide(title, tag=None):
    s = prs.slides.add_slide(BLANK)
    header(s, title, tag)
    footer(s)
    return s


def banner(slide, y, text, h=0.8, size=16):
    add_box(slide, Inches(0.6), Inches(y), Inches(12.2), Inches(h), fill=NAVY)
    add_text(slide, Inches(0.8), Inches(y + 0.12), Inches(11.8), Inches(h - 0.2),
             text, size=size, bold=True, color=WHITE, align=PP_ALIGN.CENTER)


def figslide(title, img, caption, tag=None, w=11.5, max_h=4.45):
    """Header-bar slide with a centred figure and a caption that always
    sits above the footer (image top 1.3in, caption bottom <= 6.9in)."""
    s = new_slide(title, tag)
    path = f"{FIGS}/{img}.png"
    iw, ih = Image.open(path).size
    h = w * ih / iw
    if h > max_h:
        h = max_h
        w = h * iw / ih
    left = (13.333 - w) / 2
    s.shapes.add_picture(path, Inches(left), Inches(1.3), Inches(w), Inches(h))
    add_text(s, Inches(0.6), Inches(1.4 + h), Inches(12.2), Inches(0.9),
             caption, size=14, color=GREY)
    return s


def dark_slide():
    s = prs.slides.add_slide(BLANK)
    bg = s.shapes.add_shape(MSO_SHAPE.RECTANGLE, 0, 0, W, prs.slide_height)
    bg.fill.solid(); bg.fill.fore_color.rgb = NAVY; bg.line.fill.background()
    _counter[0] += 1
    return s


# ================================================================= SLIDES
# ---------------------------------------------------------------- 1 Title
s = dark_slide()
add_text(s, Inches(0.8), Inches(0.8), Inches(11), Inches(0.5),
         "45-MINUTE SEMINAR", size=14, bold=True, color=PALE)
add_text(s, Inches(0.8), Inches(1.5), Inches(11.8), Inches(2.0),
         "From AI-Assisted Verification\nto Security Defect Discovery",
         size=44, bold=True, color=WHITE)
add_text(s, Inches(0.8), Inches(3.6), Inches(11.5), Inches(0.8),
         "How AI can help us reason about software—and find what can go wrong",
         size=22, color=RGBColor(0xDD, 0xE6, 0xF0))
add_text(s, Inches(0.8), Inches(4.35), Inches(11.5), Inches(0.6),
         "Case study: formally verifying Signal's Sparse Post-Quantum Ratchet (SPQR) in Lean 4  ·  "
         "Rust → Aeneas → Lean 4  ·  246 spec files  ·  63 defects",
         size=15, color=PALE)
add_text(s, Inches(0.8), Inches(5.05), Inches(11), Inches(0.9),
         ["Speaker: Hoàng Le Trường", "Friday, October 16, 2026 · 3:00 PM"],
         size=18, color=WHITE)
for i, lbl in enumerate(["Artificial Intelligence", "Formal Verification", "Software Security"]):
    b = add_box(s, Inches(0.8 + i * 3.3), Inches(6.1), Inches(3.0), Inches(0.6), fill=ACCENT)
    tf = b.text_frame
    tf.paragraphs[0].alignment = PP_ALIGN.CENTER
    r = tf.paragraphs[0].add_run(); r.text = lbl
    r.font.size = Pt(14); r.font.bold = True; r.font.color.rgb = WHITE; r.font.name = "Calibri"

# ---------------------------------------------------------------- 2 Roadmap
s = new_slide("Today’s Roadmap", "1 minute")
items = [
    ("01", "Can We Trust Software?", "5 minutes · Why software failures matter — and one real one (D1)"),
    ("02", "What Is Formal Verification?", "8 minutes · Testing, specifications, proofs, and the SPQR pipeline"),
    ("03", "How AI Assists Verification", "10 minutes · AI-generated proofs, their limits, and what fuzzing missed"),
    ("04", "Security Defect Discovery", "15 minutes · The SPQR case study: 63 defects, one deadlock (D21)"),
    ("05", "Lessons and Takeaways", "7 minutes · What a proof can and cannot guarantee"),
]
for i, (num, t, sub) in enumerate(items):
    y = Inches(1.4 + i * 1.08)
    add_box(s, Inches(0.7), y, Inches(11.9), Inches(0.95))
    add_text(s, Inches(0.9), y + Inches(0.12), Inches(1.2), Inches(0.7), num, size=28, bold=True, color=ACCENT)
    add_text(s, Inches(2.2), y + Inches(0.08), Inches(9), Inches(0.45), t, size=20, bold=True)
    add_text(s, Inches(2.2), y + Inches(0.5), Inches(10), Inches(0.4), sub, size=14, color=GREY)
# ================================================================ PART 1
# ---------------------------------------------------------------- 3
s = new_slide("Can We Trust Software?", "Part 1 · 5 minutes")
add_text(s, Inches(0.6), Inches(1.3), Inches(12), Inches(0.6),
         "A program can pass every test we try—and still contain a bug.", size=22, bold=True, color=ACCENT)
add_text(s, Inches(0.6), Inches(1.95), Inches(6.3), Inches(0.8),
         "Consider a simple program that checks whether a user is authorized to perform an operation.", size=16)
add_bullets(s, Inches(0.6), Inches(2.9), Inches(6.3), Inches(2.8), [
    "Ordinary cases behave correctly.",
    "Invalid inputs may follow an unexpected path.",
    "An attacker may deliberately search for an unusual sequence of operations.",
    "A rare failure can have a serious security impact.",
], size=16)
add_text(s, Inches(7.2), Inches(1.95), Inches(5.6), Inches(0.5),
         "Example: A simple authorization check", size=16, bold=True)
add_code(s, Inches(7.2), Inches(2.5), Inches(5.6), Inches(1.5),
         "if user_is_authorized:\n    perform_operation()\nelse:\n    reject_request()")
add_text(s, Inches(7.2), Inches(4.2), Inches(5.6), Inches(1.0),
         "Question: Is checking this condition enough to guarantee that the operation is secure?",
         size=15, color=RED)
banner(s, 5.7, "Testing finds failures in selected executions. Formal verification reasons about stated properties of program behavior.", h=1.0, size=16)

# ---------------------------------------------------------------- 4
figslide("A Real One: D1 — From Corrupted Blob to Panic", "fig_d1_flow",
         "Signal's SPQR passed its own tests and hax/F* proofs. Yet nothing between a stored blob and the assert "
         "re-checks next.len(); the hax contract is verified only at proof time, so a corrupted blob panics at run time.",
         tag="Part 1 · SPQR evidence")

# ================================================================ PART 2
# ---------------------------------------------------------------- 5
s = new_slide("Testing vs. Formal Verification", "Part 2 · 8 minutes")
for i, (t, q, col, pts) in enumerate([
    ("Testing", "What does the program do on these inputs?", RED, [
        "Run the program on selected inputs and observe behavior.",
        "Shows the presence of bugs, never their absence.",
        "SPQR: 40 000 forged messages → 0 panics.",
        "Missed every blob-path defect (D1, D19, D23 …)."]),
    ("Formal Verification", "Can we prove a stated property under explicit assumptions?", ACCENT, [
        "State a property for ALL inputs and prove it in a model.",
        "Every theorem names its hypotheses.",
        "SPQR: 246 Lean spec files, 0 sorry.",
        "A hypothesis the Rust never checks = a defect."]),
]):
    x = Inches(0.6 + i * 6.2)
    add_box(s, x, Inches(1.3), Inches(5.9), Inches(3.1))
    add_text(s, x + Inches(0.2), Inches(1.4), Inches(5.5), Inches(0.5), t, size=20, bold=True, color=col)
    add_text(s, x + Inches(0.2), Inches(1.85), Inches(5.5), Inches(0.5), q, size=14, color=GREY)
    add_bullets(s, x + Inches(0.2), Inches(2.4), Inches(5.5), Inches(2.0), pts, size=14, bullet_color=col)
add_text(s, Inches(0.6), Inches(4.55), Inches(12), Inches(0.4), "A tiny example", size=16, bold=True)
add_text(s, Inches(0.6), Inches(4.95), Inches(12.2), Inches(1.1), [
    "For  f(a, b) = a + b  we want:   ∀ a, b ∈ ℕ,  f(a, b) = a + b.",
    "Testing can evaluate selected pairs. A formal proof establishes the property for every pair — "
    "provided the implementation and statement are correctly formalized.",
], size=14)
banner(s, 6.15, "Testing samples executions; formal verification establishes specified properties within a model. The 63 SPQR defects came from asking what each proof had to assume.", h=0.75, size=14)
# ---------------------------------------------------------------- 6
s = new_slide("Specification, Implementation, and Proof", "Part 2 · 3 minutes")
for i, (t, d, ex) in enumerate([
    ("1. Specification — What should happen?", "A precise statement of the intended behavior.",
     "Example: An unauthenticated message must not advance the session state."),
    ("2. Implementation — What does the code do?",
     "The actual instructions, conditions, state transitions, and message-handling logic.", None),
    ("3. Proof — Why is the property true?",
     "A formal argument that the implementation satisfies the specification under stated assumptions.", None),
]):
    y = Inches(1.3 + i * 1.35)
    add_box(s, Inches(0.6), y, Inches(12.2), Inches(1.2))
    add_text(s, Inches(0.8), y + Inches(0.08), Inches(11.8), Inches(0.45), t, size=18, bold=True, color=ACCENT)
    lines = [d] + ([ex] if ex else [])
    add_text(s, Inches(0.8), y + Inches(0.5), Inches(11.8), Inches(0.7), lines, size=14)
add_text(s, Inches(0.6), Inches(5.45), Inches(12.2), Inches(0.5),
         "Important question: What if the specification itself is wrong or incomplete?", size=18, bold=True, color=RED)
add_text(s, Inches(0.6), Inches(6.0), Inches(12.2), Inches(0.8),
         "A proof may be mathematically valid while the system still fails to satisfy its real-world security requirements.",
         size=15)

# ---------------------------------------------------------------- 7
s = new_slide("What Is Lean, and Why Use It?", "Part 2 · 2 minutes")
add_text(s, Inches(0.6), Inches(1.3), Inches(6.2), Inches(0.6),
         "Lean is an interactive theorem prover and programming language.", size=18, bold=True)
add_text(s, Inches(0.6), Inches(1.95), Inches(6.2), Inches(0.4), "It allows us to:", size=15)
add_bullets(s, Inches(0.6), Inches(2.35), Inches(6.2), Inches(2.5), [
    "Express mathematical definitions and theorems precisely.",
    "Construct proofs using tactics and reusable lemmas.",
    "Encode properties of programs and mathematical structures.",
    "Check proof terms with Lean's trusted kernel.",
], size=15)
add_text(s, Inches(7.1), Inches(1.3), Inches(5.7), Inches(0.4), "A tiny Lean example", size=16, bold=True)
add_code(s, Inches(7.1), Inches(1.75), Inches(5.7), Inches(1.1),
         "theorem add_zero (n : Nat) : n + 0 = n := by\n  rfl")
add_text(s, Inches(7.1), Inches(2.95), Inches(5.7), Inches(0.6),
         "This theorem states that adding zero to a natural number leaves it unchanged.", size=13, color=GREY)
add_bullets(s, Inches(7.1), Inches(3.55), Inches(5.7), Inches(2.0), [
    "Nat represents natural numbers.",
    "theorem introduces a proposition to prove.",
    "by starts the proof.",
    "rfl proves the equality by definitional reduction.",
], size=13)
banner(s, 5.9, "The important idea: Lean checks whether the proof establishes the stated proposition — nothing more.", h=0.9, size=16)

# ---------------------------------------------------------------- 8
figslide("The SPQR Verification Pipeline: Rust → Aeneas → Lean 4", "fig_pipeline",
         "Funs.lean is generated from the Rust by Aeneas and trusted. The hand-written external models (dashed) are "
         "where an unsound model (D59) silently weakens every proof that depends on it.",
         tag="Part 2 · SPQR evidence")
# ================================================================ PART 3
# ---------------------------------------------------------------- 9
s = new_slide("How AI Assists Formal Verification", "Part 3 · 10 minutes")
cards = [
    ("1. Explain", "Explain unfamiliar code, definitions, and proof goals in natural language."),
    ("2. Suggest", "Recommend useful lemmas, tactics, and proof strategies."),
    ("3. Generate", "Draft Lean code, candidate proofs — and candidate counterexamples."),
    ("4. Explore", "Try alternative proof approaches and investigate why a proof gets stuck."),
]
for i, (t, d) in enumerate(cards):
    x = Inches(0.6 + (i % 2) * 6.2)
    y = Inches(1.4 + (i // 2) * 2.3)
    add_box(s, x, y, Inches(5.9), Inches(2.05))
    add_text(s, x + Inches(0.3), y + Inches(0.2), Inches(5.3), Inches(0.6), t, size=24, bold=True, color=ACCENT)
    add_text(s, x + Inches(0.3), y + Inches(0.9), Inches(5.3), Inches(1.1), d, size=16)
banner(s, 6.1, "In SPQR, AI drafted spec theorems, proposed the forged-message bytes, and summarized state transitions — Lean and cargo checked them.", h=0.75, size=14)

# ---------------------------------------------------------------- 10
s = new_slide("Why AI-Generated Proofs Need Checking", "Part 3 · 3 minutes")
fails = [
    ("Failure 1: Invalid Proof", "AI generates code that does not compile or does not prove the goal."),
    ("Failure 2: Wrong Property", "The proof establishes a weaker property than the one needed for security."),
    ("Failure 3: Missing Assumptions", "The formal model omits relevant system behavior or environmental conditions."),
    ("Failure 4: False Confidence", "A successful proof is interpreted as a guarantee that the whole system is secure."),
]
for i, (t, d) in enumerate(fails):
    x = Inches(0.6 + (i % 2) * 6.2)
    y = Inches(1.4 + (i // 2) * 2.1)
    add_box(s, x, y, Inches(5.9), Inches(1.85), fill=LIGHT, line=RED)
    add_text(s, x + Inches(0.3), y + Inches(0.2), Inches(5.3), Inches(0.5), t, size=20, bold=True, color=RED)
    add_text(s, x + Inches(0.3), y + Inches(0.8), Inches(5.3), Inches(1.0), d, size=15)
banner(s, 5.85, "AI output  →  Lean checks the proof  →  Humans check the specification and assumptions.", h=0.9, size=18)

# ---------------------------------------------------------------- 11
figslide("What Fuzzing Showed — and Didn't", "fig_harness",
         "Left: an AI-built harness fires 40 000 forged messages and nothing panics — yet D21 lives on the accepted (blue) path. "
         "Right: the Lean counter bound is a hypothesis a peer can exceed after ~156 K messages. Both checks passed; neither asked the right question.",
         tag="Part 3 · SPQR evidence")
# ================================================================ PART 4
# ---------------------------------------------------------------- 12
s = new_slide("The Project: Signal's SPQR, Re-verified in Lean 4", "Part 4 · 15 minutes")
for i, (k, v) in enumerate([
    ("What", "Sparse Post-Quantum Ratchet: the ML-KEM layer of Signal's Triple Ratchet (Rust crate spqr v1.5.0)"),
    ("Upstream", "Signal verifies it with hax → F*"),
    ("Ours", "Independent re-verification: Rust → Aeneas → Lean 4, 246 spec theorems, 0 sorry"),
    ("Result", "63 defects (D1–D63), each backed by a Lean proof or a runnable Rust counterexample"),
]):
    y = Inches(1.3 + i * 0.85)
    add_box(s, Inches(0.6), y, Inches(12.2), Inches(0.72))
    add_text(s, Inches(0.85), y + Inches(0.13), Inches(1.6), Inches(0.5), k, size=18, bold=True, color=ACCENT)
    add_text(s, Inches(2.5), y + Inches(0.14), Inches(10.1), Inches(0.5), v, size=15)
add_text(s, Inches(0.6), Inches(4.75), Inches(12), Inches(0.45), "Three root-cause patterns", size=18, bold=True, color=ACCENT)
for i, (t, ids) in enumerate([
    ("Authenticate after persist", "D16 D21 D22 D35 D36 D62"),
    ("from_pb copies without validating", "D1 D11–D14 D18 D19 D23 … D61"),
    ("assume! erased at run time", "D2 D3 D5 D8 D9 D25 D29 D37 D56 D57"),
]):
    x = Inches(0.6 + i * 4.15)
    add_box(s, x, Inches(5.25), Inches(3.9), Inches(1.4), fill=LIGHT, line=RED if i == 0 else None)
    add_text(s, x + Inches(0.2), Inches(5.35), Inches(3.5), Inches(0.5), t, size=15, bold=True,
             color=RED if i == 0 else NAVY)
    add_text(s, x + Inches(0.2), Inches(5.9), Inches(3.5), Inches(0.6), ids, size=12, color=GREY)

# ---------------------------------------------------------------- 13
figslide("63 Defects at a Glance", "fig_defects",
         "Left: fix status. Right: root-cause class — overflow and missing validation dominate by count; "
         "authentication ordering (red) is today's case study.",
         tag="Part 4 · SPQR evidence")

# ---------------------------------------------------------------- 14
s = new_slide("Case Study: When a Protocol Accepts the Wrong Message", "Part 4 · D21")
add_box(s, Inches(0.6), Inches(1.3), Inches(12.2), Inches(0.7), fill=LIGHT)
add_text(s, Inches(0.8), Inches(1.4), Inches(11.8), Inches(0.5),
         "Security goal: An unauthenticated control message must not cause an unauthorized state transition.",
         size=16, bold=True)
for i, (t, col, steps) in enumerate([
    ("Intended behavior", GREEN, [
        "Receive a control message.",
        "Verify the required authentication conditions.",
        "Validate the message's meaning and context.",
        "Apply the state transition only if all required checks succeed."]),
    ("What SPQR recv actually does (D21)", RED, [
        "Receive a control message.",
        "Advance the protocol state (epoch, keys) and persist it.",
        "Verify authentication.",
        "Reject the message if authentication fails — state already changed."]),
]):
    x = Inches(0.6 + i * 6.2)
    add_box(s, x, Inches(2.2), Inches(5.9), Inches(2.9), fill=LIGHT, line=col)
    add_text(s, x + Inches(0.2), Inches(2.3), Inches(5.5), Inches(0.5), t, size=18, bold=True, color=col)
    add_bullets(s, x + Inches(0.2), Inches(2.8), Inches(5.5), Inches(2.3), steps, size=14, numbered=True)
add_text(s, Inches(0.6), Inches(5.35), Inches(12.2), Inches(0.5), "The key question", size=18, bold=True, color=ACCENT)
add_text(s, Inches(0.6), Inches(5.85), Inches(12.2), Inches(0.9),
         "What happens if the message is rejected after the protocol state has already changed?", size=20, bold=True, color=RED)

# ---------------------------------------------------------------- 15
figslide("D21 as a Sequence Diagram", "fig_d21_sequence",
         "One unauthenticated 4-byte message moves Bob to epoch 2. Alice rejects all of Bob's messages; "
         "Bob ignores all of Alice's. Permanent deadlock — the answer to the key question.",
         tag="Part 4 · SPQR evidence", w=10.5)

# ---------------------------------------------------------------- 16
figslide("Where the MAC Is — and Isn't — Checked", "fig_state_machine",
         "Green: the only edges that call the MAC. Red: edges that persist state with no Authenticator call. "
         "D21 is the red back-edge; the same pattern explains D16, D22, D35, D36 and D62.",
         tag="Part 4 · SPQR evidence")

# ---------------------------------------------------------------- 17
figslide("Why Signal Is Safe From D21 — and Who Isn't", "fig_libsignal",
         "libsignal runs spqr::recv on a clone and commits only after the MAC passes. The protection lives outside SPQR; "
         "peers, other embedders and storage bypass it. Exploitability is a judgment about the whole system, not the crate.",
         tag="Part 4 · exploitability")

# ---------------------------------------------------------------- 18
s = new_slide("From Code Reading to a Validated Defect", "Part 4 · workflow")
steps = [
    ("Step 1 — Inspect", "AI summarizes control flow, message handling, and state transitions.",
     "D21: AI read recv and flagged that the epoch advances before the MAC check."),
    ("Step 2 — Hypothesize", "Identify a suspicious ordering, missing condition, or inconsistency with the security requirements.",
     "Hypothesis: an unauthenticated message can move a peer to a new epoch."),
    ("Step 3 — Construct", "Propose a message sequence, execution trace, or counterexample that could violate the property.",
     "AI proposed the 4-byte forged message."),
    ("Step 4 — Validate", "Reproduce the behavior and check it against implementation, model, tests, or formal properties.",
     "cargo test reproduces the deadlock; Lean proves it in ProtocolDoS.lean."),
]
for i, (t, d, ex) in enumerate(steps):
    x = Inches(0.6 + i * 3.1)
    add_box(s, x, Inches(1.4), Inches(2.9), Inches(4.6))
    add_text(s, x + Inches(0.2), Inches(1.5), Inches(2.5), Inches(0.5), t, size=18, bold=True, color=ACCENT)
    add_text(s, x + Inches(0.2), Inches(2.1), Inches(2.5), Inches(2.0), d, size=13)
    add_text(s, x + Inches(0.2), Inches(4.3), Inches(2.5), Inches(1.6), ex, size=12, color=RED)
    if i < 3:
        add_text(s, x + Inches(2.85), Inches(3.3), Inches(0.4), Inches(0.5), "→", size=24, bold=True, color=GREY)
banner(s, 6.15, "Report a defect only when the evidence is strong enough. Two agents agreeing is not evidence.", h=0.75, size=15)

# ---------------------------------------------------------------- 19
s = figslide("Three Complementary Roles, One Defect", "fig_roles",
             "No arrow is skippable: the forged bytes came from AI, the deadlock proof from cargo/Lean, "
             "the exploitability verdict from reading libsignal.",
             tag="Part 4 · method", w=8.0, max_h=3.9)
banner(s, 6.1, "AI proposes  ·  Formal tools check  ·  Humans evaluate specification quality, exploitability, and impact.", h=0.75, size=15)

# ================================================================ PART 5
# ---------------------------------------------------------------- 20
figslide("Why a Proof Is Not a Security Guarantee", "fig_proof_vs_security",
         "Everything in the blue ellipse is machine-checked. Every one of the 63 defects is a true statement about "
         "the green region that no theorem mentioned.",
         tag="Part 5 · 7 minutes")

# ---------------------------------------------------------------- 21
s = new_slide("Key Message", "Part 5")
add_box(s, Inches(0.8), Inches(1.5), Inches(11.7), Inches(4.9))
add_text(s, Inches(1.1), Inches(1.8), Inches(11.1), Inches(1.4),
         "Even a Lean proof accepted by the kernel establishes only\nthe formal proposition under its stated assumptions.",
         size=26, bold=True, align=PP_ALIGN.CENTER)
add_text(s, Inches(1.1), Inches(3.35), Inches(11.1), Inches(1.4),
         "It does not, by itself, establish that the specification captures\nevery security requirement of the real-world system.",
         size=24, color=RED, align=PP_ALIGN.CENTER)
add_text(s, Inches(1.1), Inches(4.95), Inches(11.1), Inches(1.3),
         "SPQR: 246 spec files, 0 sorry, ChainInv proved — and still 63 defects,\nfound precisely by asking what each proof had to assume.",
         size=18, color=GREY, align=PP_ALIGN.CENTER)

# ---------------------------------------------------------------- 22
s = new_slide("Lessons, Limitations, and Takeaways", "Part 5")
add_text(s, Inches(0.6), Inches(1.25), Inches(7), Inches(0.4), "Five takeaways", size=18, bold=True, color=ACCENT)
add_bullets(s, Inches(0.6), Inches(1.7), Inches(7.2), Inches(4.2), [
    "Testing is useful, but incomplete. 40 000 fuzzed messages missed D21.",
    "Formal verification gives precise guarantees — relative to the specification and its assumptions.",
    "AI accelerates exploration: drafting specs, proofs, harnesses, and counterexamples.",
    "Proof does not equal security. A valid proof may establish a property that is too weak or incomplete.",
    "Human judgment remains essential: the libsignal clone-and-commit verdict came from reading code, not a prover.",
], size=14, numbered=True)
add_box(s, Inches(8.1), Inches(1.25), Inches(4.7), Inches(4.6))
add_text(s, Inches(8.3), Inches(1.4), Inches(4.3), Inches(0.4), "Questions for discussion", size=18, bold=True, color=ACCENT)
add_bullets(s, Inches(8.3), Inches(1.9), Inches(4.3), Inches(3.8), [
    "If an AI-generated proof is accepted by Lean, what exactly have we established?",
    "Can a perfectly verified program still be insecure?",
    "Where should human judgment remain in an AI-assisted workflow?",
], size=14)
banner(s, 6.05, "Final message: Use AI to explore more possibilities — and use verification to check the claims.", h=0.8, size=17)

# ---------------------------------------------------------------- 23 Thank you
s = dark_slide()
add_text(s, Inches(1), Inches(2.4), Inches(11.3), Inches(1.2), "Thank You", size=44, bold=True, color=WHITE, align=PP_ALIGN.CENTER)
add_text(s, Inches(1), Inches(3.6), Inches(11.3), Inches(0.7), "Questions & Discussion", size=26, color=PALE, align=PP_ALIGN.CENTER)
add_text(s, Inches(1), Inches(4.7), Inches(11.3), Inches(1.2), [
    "docs/report.md · docs/listDefects.md · docs/classificationBug.md · docs/bugSecurityRemote.md",
    "Spqr/Specs/Bugs/ProtocolDoS.lean · Spqr/Specs/Bugs/CorruptedBlobs.lean · docs/protocol_driver_counterexamples.rs.txt",
], size=14, color=PALE, align=PP_ALIGN.CENTER)

assert _counter[0] == TOTAL == len(prs.slides), (_counter[0], len(prs.slides))
prs.save(OUT)
print("Saved", OUT, "with", len(prs.slides), "slides")
