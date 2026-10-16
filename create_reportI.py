#!/usr/bin/env python3
"""Generate reportI.pptx: 12-slide seminar deck
'From AI-Assisted Verification to Security Defect Discovery'.
Slide bodies are in English; Vietnamese presenter notes go into speaker notes."""

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

prs = Presentation()
prs.slide_width = Inches(13.333)
prs.slide_height = Inches(7.5)
BLANK = prs.slide_layouts[6]
W = prs.slide_width


def add_text(slide, x, y, w, h, text, size=18, bold=False, color=NAVY,
             align=PP_ALIGN.LEFT, font="Calibri"):
    tb = slide.shapes.add_textbox(x, y, w, h)
    tf = tb.text_frame
    tf.word_wrap = True
    lines = text if isinstance(text, list) else [text]
    # never put a raw newline inside a run: split into paragraphs instead
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


def add_bullets(slide, x, y, w, h, items, size=18, color=NAVY, numbered=False):
    tb = slide.shapes.add_textbox(x, y, w, h)
    tf = tb.text_frame
    tf.word_wrap = True
    for i, item in enumerate(items):
        p = tf.paragraphs[0] if i == 0 else tf.add_paragraph()
        prefix = f"{i + 1}. " if numbered else "•  "
        r = p.add_run()
        r.text = prefix + item
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
    add_text(slide, Inches(0.5), Inches(0.2), Inches(10.5), Inches(0.8),
             title, size=30, bold=True, color=WHITE)
    if tag:
        add_text(slide, Inches(9.3), Inches(0.35), Inches(3.6), Inches(0.5),
                 tag, size=13, color=RGBColor(0xBF, 0xD4, 0xEA), align=PP_ALIGN.RIGHT)


def footer(slide, n):
    add_text(slide, Inches(0.5), Inches(7.0), Inches(9), Inches(0.4),
             "From AI-Assisted Verification to Security Defect Discovery",
             size=10, color=GREY)
    add_text(slide, Inches(12.0), Inches(7.0), Inches(0.9), Inches(0.4),
             f"{n} / 12", size=10, color=GREY, align=PP_ALIGN.RIGHT)


def notes(slide, text):
    # Speaker notes intentionally omitted: slides are English-only.
    return


def new_slide(n, title, tag=None):
    s = prs.slides.add_slide(BLANK)
    header(s, title, tag)
    footer(s, n)
    return s


def banner(slide, y, text, h=0.8, size=16):
    add_box(slide, Inches(0.6), Inches(y), Inches(12.2), Inches(h), fill=NAVY)
    add_text(slide, Inches(0.8), Inches(y + 0.12), Inches(11.8), Inches(h - 0.2),
             text, size=size, bold=True, color=WHITE, align=PP_ALIGN.CENTER)

# === SLIDES ===

# ---------------------------------------------------------------- Slide 1
s = prs.slides.add_slide(BLANK)
bg = s.shapes.add_shape(MSO_SHAPE.RECTANGLE, 0, 0, W, prs.slide_height)
bg.fill.solid(); bg.fill.fore_color.rgb = NAVY; bg.line.fill.background()
add_text(s, Inches(0.8), Inches(0.8), Inches(11), Inches(0.5),
         "45-MINUTE SEMINAR", size=14, bold=True, color=RGBColor(0xBF, 0xD4, 0xEA))
add_text(s, Inches(0.8), Inches(1.5), Inches(11.8), Inches(2.0),
         "From AI-Assisted Verification\nto Security Defect Discovery",
         size=44, bold=True, color=WHITE)
add_text(s, Inches(0.8), Inches(3.6), Inches(11.5), Inches(0.8),
         "How AI can help us reason about software—and find what can go wrong",
         size=22, color=RGBColor(0xDD, 0xE6, 0xF0))
add_text(s, Inches(0.8), Inches(4.8), Inches(11), Inches(1.0),
         ["Speaker: Hoàng Le Trường", "Friday, October 16, 2026 · 3:00 PM"],
         size=18, color=WHITE)
for i, lbl in enumerate(["Artificial Intelligence", "Formal Verification", "Software Security"]):
    b = add_box(s, Inches(0.8 + i * 3.3), Inches(6.1), Inches(3.0), Inches(0.6), fill=ACCENT)
    tf = b.text_frame
    tf.paragraphs[0].alignment = PP_ALIGN.CENTER
    r = tf.paragraphs[0].add_run(); r.text = lbl
    r.font.size = Pt(14); r.font.bold = True; r.font.color.rgb = WHITE; r.font.name = "Calibri"
notes(s, """Thời lượng: 1 phút.

Mở đầu bằng một câu hỏi đơn giản:
"If an AI tells us that a program is correct, should we trust it?"

Giải thích rằng bài nói sẽ tìm hiểu cách AI hỗ trợ kiểm chứng phần mềm và phát hiện lỗi bảo mật, đồng thời xem xét tại sao AI đôi khi có thể sai và làm thế nào chúng ta kiểm tra kết quả của nó.

Không cần giới thiệu các thuật toán AI phức tạp ngay từ đầu.""")

# ---------------------------------------------------------------- Slide 2
s = new_slide(2, "Today’s Roadmap", "1 minute")
items = [
    ("01", "Can We Trust Software?", "5 minutes · Why software failures matter"),
    ("02", "What Is Formal Verification?", "8 minutes · Testing, specifications, and proofs"),
    ("03", "How AI Assists Verification", "10 minutes · AI-generated proofs and their limitations"),
    ("04", "Security Defect Discovery", "15 minutes · A practical case study"),
    ("05", "Lessons and Takeaways", "7 minutes · What AI can and cannot guarantee"),
]
for i, (num, t, sub) in enumerate(items):
    y = Inches(1.4 + i * 1.08)
    add_box(s, Inches(0.7), y, Inches(11.9), Inches(0.95))
    add_text(s, Inches(0.9), y + Inches(0.12), Inches(1.2), Inches(0.7), num, size=28, bold=True, color=ACCENT)
    add_text(s, Inches(2.2), y + Inches(0.08), Inches(9), Inches(0.45), t, size=20, bold=True)
    add_text(s, Inches(2.2), y + Inches(0.5), Inches(9), Inches(0.4), sub, size=14, color=GREY)
notes(s, """Thời lượng: 1 phút.

Nói rõ rằng người nghe không cần biết trước Lean hay mật mã học. Mục tiêu là hiểu cách tiếp cận, quy trình làm việc và ý nghĩa thực tiễn của việc kết hợp AI với các công cụ kiểm chứng.

Lưu ý: các thời lượng của năm phần cộng lại là 45 phút. Nếu cần phần hỏi đáp riêng, nên rút phần trình bày chính xuống 40 phút.""")

# ---------------------------------------------------------------- Slide 3
s = new_slide(3, "Can We Trust Software?", "Part 1 · 5 minutes")
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
notes(s, """Phần 1 · 5 phút cho cả phần mở đầu.

Giải thích rằng đoạn code trên chỉ là ví dụ đơn giản. Trong thực tế, vấn đề có thể nằm ở chỗ trạng thái xác thực đã bị thay đổi trước khi điều kiện được kiểm tra, hoặc quyền truy cập đã thay đổi giữa hai bước.

Phân biệt ba khái niệm:
- Bug: Chương trình không hoạt động như mong đợi.
- Security defect: Một lỗi có thể ảnh hưởng đến tính bảo mật, chẳng hạn quyền truy cập hoặc tính toàn vẹn của trạng thái.
- Vulnerability: Một điểm yếu có thể bị khai thác trong những điều kiện cụ thể.

Không phải mọi bug đều là vulnerability, và không phải mọi vulnerability đều có thể khai thác dễ dàng.""")


# ---------------------------------------------------------------- Slide 4
s = new_slide(4, "Testing vs. Formal Verification", "Part 2 · 8 minutes")
for i, (t, q, pts) in enumerate([
    ("Testing", "What does the program do on these inputs?", [
        "Run the program on selected inputs.", "Observe the outputs and behavior.",
        "Find bugs through test cases.", "Coverage depends on the tests performed."]),
    ("Formal Verification", "Can we prove a stated property under explicit assumptions?", [
        "Express requirements mathematically.", "Model relevant program behavior.",
        "Construct a machine-checkable proof.", "Establish a guarantee within the formal model."]),
]):
    x = Inches(0.6 + i * 6.2)
    add_box(s, x, Inches(1.3), Inches(5.9), Inches(3.0))
    add_text(s, x + Inches(0.2), Inches(1.4), Inches(5.5), Inches(0.5), t, size=20, bold=True, color=ACCENT)
    add_text(s, x + Inches(0.2), Inches(1.85), Inches(5.5), Inches(0.5), q, size=14, color=GREY)
    add_bullets(s, x + Inches(0.2), Inches(2.4), Inches(5.5), Inches(1.9), pts, size=14)
add_text(s, Inches(0.6), Inches(4.45), Inches(12), Inches(0.4), "Example", size=16, bold=True)
add_text(s, Inches(0.6), Inches(4.85), Inches(12.2), Inches(1.3), [
    "Suppose a function adds two natural numbers:   f(a, b) = a + b",
    "We want to establish the property:   ∀ a, b ∈ ℕ,  f(a, b) = a + b",
    "Testing can evaluate selected pairs. A formal proof can establish the property for every pair of natural numbers, "
    "provided the implementation and statement are correctly formalized.",
], size=14)
banner(s, 6.2, "Key distinction: Testing samples executions; formal verification establishes specified properties within a model.", h=0.7, size=15)
notes(s, """Phần 2 · 8 phút cho phần giới thiệu formal verification.

Ví dụ cộng hai số được chọn vì sinh viên chưa cần hiểu mật mã học.

Sau đó chuyển sang phần mềm bảo mật: thay vì chứng minh một hàm cộng đúng, ta có thể muốn chứng minh rằng một thông điệp chưa xác thực không thể làm thay đổi trạng thái của phiên giao tiếp.

Nhấn mạnh rằng formal verification không nhất thiết chứng minh toàn bộ chương trình. Nhiều hệ thống chỉ được kiểm chứng một số thuộc tính quan trọng.""")

# ---------------------------------------------------------------- Slide 5
s = new_slide(5, "Specification, Implementation, and Proof", "3 minutes")
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
notes(s, """Thời lượng gợi ý: 3 phút.

Đây là một trong những slide quan trọng nhất.

Ví dụ, nếu specification chỉ yêu cầu rằng một hàm trả về đúng giá trị khi đầu vào hợp lệ, nhưng không quy định cách xử lý đầu vào không hợp lệ, chứng minh có thể không bao phủ trường hợp mà kẻ tấn công quan tâm.

Ba câu hỏi nên được nhấn mạnh:
1. Ta muốn hệ thống làm gì?
2. Code có thực sự làm điều đó không?
3. Yêu cầu đã mô tả đầy đủ hành vi cần thiết chưa?""")


# ---------------------------------------------------------------- Slide 6
s = new_slide(6, "What Is Lean, and Why Use It?", "2 minutes")
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
banner(s, 5.9, "The important idea: Lean checks whether the proof establishes the stated proposition.", h=0.9, size=16)
notes(s, """Thời lượng gợi ý: 2 phút.

Không cần giảng sâu về cú pháp Lean. Chỉ cần giải thích rằng AI có thể đề xuất một đoạn chứng minh, nhưng Lean vẫn phải kiểm tra đoạn đó.

Phân biệt:
- AI nói rằng một chứng minh có vẻ đúng.
- Lean xác nhận rằng proof term có thể chứng minh mệnh đề đã khai báo.

Tuy nhiên, điều đó không tự bảo đảm rằng mệnh đề là yêu cầu bảo mật thích hợp, rằng toàn bộ hệ thống đã được mô hình hóa, hay rằng các giả thiết bên ngoài đều đúng.""")

# ---------------------------------------------------------------- Slide 7
s = new_slide(7, "How AI Assists Formal Verification", "Part 3 · 10 minutes")
cards = [
    ("1. Explain", "Explain unfamiliar code, definitions, and proof goals in natural language."),
    ("2. Suggest", "Recommend useful lemmas, tactics, and proof strategies."),
    ("3. Generate", "Draft Lean code and candidate proofs."),
    ("4. Explore", "Try alternative proof approaches and investigate why a proof gets stuck."),
]
for i, (t, d) in enumerate(cards):
    x = Inches(0.6 + (i % 2) * 6.2)
    y = Inches(1.5 + (i // 2) * 2.5)
    add_box(s, x, y, Inches(5.9), Inches(2.2))
    add_text(s, x + Inches(0.3), y + Inches(0.25), Inches(5.3), Inches(0.6), t, size=24, bold=True, color=ACCENT)
    add_text(s, x + Inches(0.3), y + Inches(0.95), Inches(5.3), Inches(1.1), d, size=16)
notes(s, """Phần 3 · 10 phút.

Giải thích rằng AI không chỉ sinh code từ đầu. Một tác dụng quan trọng là hỗ trợ người dùng hiểu code có sẵn và tìm hướng tiếp cận cho mục tiêu chứng minh.

Ví dụ, nếu Lean báo còn một mục tiêu chưa được giải quyết, AI có thể đề xuất một lemma trung gian hoặc gợi ý cách phân trường hợp. Người dùng chạy lại Lean để kiểm tra.

Nếu có thể, hãy trình diễn một ví dụ nhỏ trực tiếp trong Lean hoặc trình chiếu một đoạn hội thoại AI ngắn. Không nên dành quá nhiều thời gian cho một proof khó, vì người nghe chưa có nền tảng về Lean.""")

# ---------------------------------------------------------------- Slide 8
s = new_slide(8, "Why AI-Generated Proofs Need Checking", "3 minutes")
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
notes(s, """Thời lượng gợi ý: 3 phút.

Ví dụ dễ hiểu nhất là AI chứng minh một mệnh đề yếu hơn yêu cầu ban đầu.

Giả sử ta cần chứng minh:  Unauthenticated(m) ⇒ s' = s.
Nghĩa là nếu thông điệp m chưa được xác thực thì trạng thái mới s' phải bằng trạng thái cũ s.

Nếu ta chỉ chứng minh rằng một hàm xác thực trả về `false` đối với thông điệp không hợp lệ, điều đó chưa chứng minh rằng trạng thái giao thức không thay đổi.

Hai mệnh đề liên quan nhưng không tương đương. Đây là một ví dụ cho thấy cần xem xét đúng thuộc tính cần chứng minh, chứ không chỉ xem proof có qua Lean hay không.""")


# ---------------------------------------------------------------- Slide 9
s = new_slide(9, "Case Study: When a Protocol Accepts the Wrong Message", "Part 4 · 15 minutes")
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
    ("Potentially defective behavior", RED, [
        "Receive a control message.",
        "Advance the protocol state.",
        "Verify authentication.",
        "Reject the message if authentication fails."]),
]):
    x = Inches(0.6 + i * 6.2)
    add_box(s, x, Inches(2.2), Inches(5.9), Inches(2.9), fill=LIGHT, line=col)
    add_text(s, x + Inches(0.2), Inches(2.3), Inches(5.5), Inches(0.5), t, size=18, bold=True, color=col)
    add_bullets(s, x + Inches(0.2), Inches(2.8), Inches(5.5), Inches(2.3), steps, size=14, numbered=True)
add_text(s, Inches(0.6), Inches(5.35), Inches(12.2), Inches(0.5), "The key question", size=18, bold=True, color=ACCENT)
add_text(s, Inches(0.6), Inches(5.85), Inches(12.2), Inches(0.9),
         "What happens if the message is rejected after the protocol state has already changed?", size=20, bold=True, color=RED)
notes(s, """Phần 4 · 15 phút.

Đây là ví dụ minh họa về một kiểu lỗi thứ tự xử lý. Chỉ nên trình bày nó như một defect thực tế nếu bạn đã xác nhận rằng code trong dự án thực sự có hành vi đó.

Giải thích cho sinh viên:
- Giao thức thường có trạng thái như epoch, khóa hiện tại hoặc thông tin phiên.
- Một thông điệp điều khiển có thể yêu cầu thay đổi trạng thái.
- Nếu trạng thái thay đổi trước khi thông điệp được xác thực, một thông điệp không hợp lệ có thể gây ra trạng thái ngoài dự kiến.
- Tác động thực tế phụ thuộc vào cách giao thức xử lý lỗi, khả năng phục hồi trạng thái và các kiểm tra khác.

Không khẳng định rằng mọi lỗi xử lý trước xác thực đều có thể khai thác. Cần kiểm tra luồng thực thi đầy đủ và đánh giá tác động thực tế.""")

# ---------------------------------------------------------------- Slide 10
s = new_slide(10, "From Code Reading to a Validated Defect", "Part 4")
steps = [
    ("Step 1 — Inspect", "AI helps summarize control flow, message handling, and state transitions."),
    ("Step 2 — Hypothesize", "Identify a suspicious ordering, missing condition, or inconsistency with the security requirements."),
    ("Step 3 — Construct", "Propose a message sequence, execution trace, or counterexample that could violate the intended property."),
    ("Step 4 — Validate", "Reproduce the behavior and check the result against the implementation, model, tests, or formal properties."),
]
for i, (t, d) in enumerate(steps):
    x = Inches(0.6 + i * 3.1)
    add_box(s, x, Inches(1.7), Inches(2.9), Inches(4.3))
    add_text(s, x + Inches(0.2), Inches(1.85), Inches(2.5), Inches(0.9), t, size=18, bold=True, color=ACCENT)
    add_text(s, x + Inches(0.2), Inches(2.8), Inches(2.5), Inches(3.0), d, size=14)
    if i < 3:
        add_text(s, x + Inches(2.85), Inches(3.5), Inches(0.4), Inches(0.5), "→", size=24, bold=True, color=GREY)
add_text(s, Inches(0.6), Inches(6.2), Inches(12.2), Inches(0.6),
         "Report a defect only when the evidence is strong enough.", size=16, bold=True, color=NAVY, align=PP_ALIGN.CENTER)
notes(s, """Đây là nơi bạn nên nói về cách làm việc thực tế của mình, chẳng hạn khi phân tích một repository Lean hoặc code của giao thức bảo mật.

Một workflow hợp lý:
1. AI đọc code và tóm tắt chức năng.
2. AI xác định những giả thiết cần kiểm tra.
3. Một agent khác phản biện giả thuyết, tìm trường hợp biên hoặc xây dựng phản ví dụ.
4. Người nghiên cứu kiểm tra lại bằng code, test, mô hình hoặc proof phù hợp.
5. Chỉ báo cáo defect khi có bằng chứng đủ mạnh.

Nếu bạn thực sự dùng hai agent, hãy trình bày chúng như hai vai trò bổ sung:
- Proof agent: Tìm cách chứng minh thuộc tính dự kiến.
- Critic agent: Tìm giả thiết thiếu, trường hợp biên hoặc phản ví dụ.

Tuy nhiên, việc hai agent đồng ý với nhau không thay thế cho bằng chứng độc lập. Cả hai có thể mắc cùng một sai lầm.""")


# ---------------------------------------------------------------- Slide 11
s = new_slide(11, "Three Complementary Roles", "Part 4")
roles = [
    ("AI Proposes", ["Hypotheses", "Proof strategies", "Failure scenarios"]),
    ("Formal Tools Check", ["Proof validity", "Stated properties", "Model-specific counterexamples"]),
    ("Humans Evaluate", ["Specification quality", "Practical exploitability", "Security impact"]),
]
for i, (t, pts) in enumerate(roles):
    x = Inches(0.6 + i * 4.15)
    add_box(s, x, Inches(1.6), Inches(3.9), Inches(3.6))
    add_text(s, x + Inches(0.3), Inches(1.8), Inches(3.3), Inches(0.6), t, size=22, bold=True, color=ACCENT)
    add_bullets(s, x + Inches(0.3), Inches(2.6), Inches(3.3), Inches(2.5), pts, size=16)
banner(s, 5.6, "The strongest workflow combines AI exploration, machine-checkable evidence, and expert judgment.", h=1.0, size=17)
notes(s, """Phần này tổng kết phương pháp:
- AI rất hữu ích trong việc tạo giả thuyết và khám phá nhiều hướng.
- Công cụ hình thức kiểm tra các mệnh đề đã được biểu diễn chính xác.
- Chuyên gia xác định liệu mô hình có phản ánh đúng hệ thống thực tế và liệu lỗi có ý nghĩa về mặt bảo mật hay không.

Nên tránh trình bày AI như một công cụ tự động tìm ra mọi lỗ hổng. Vai trò của AI là tăng năng suất phân tích, không loại bỏ nhu cầu kiểm chứng.""")

# ---------------------------------------------------------------- Slide 12
s = new_slide(12, "Lessons, Limitations, and Takeaways", "Part 5 · 7 minutes")
add_text(s, Inches(0.6), Inches(1.25), Inches(7), Inches(0.4), "Five takeaways", size=18, bold=True, color=ACCENT)
add_bullets(s, Inches(0.6), Inches(1.7), Inches(7.2), Inches(4.2), [
    "Testing is useful, but incomplete. It examines selected executions.",
    "Formal verification provides precise guarantees. Those guarantees depend on the specification and assumptions.",
    "AI accelerates exploration. It can assist proof development and identify suspicious behavior.",
    "Proof does not equal security. A valid proof may establish a property that is too weak or incomplete.",
    "Human judgment remains essential. Real security analysis requires understanding the system and its threat model.",
], size=14, numbered=True)
add_box(s, Inches(8.1), Inches(1.25), Inches(4.7), Inches(4.6))
add_text(s, Inches(8.3), Inches(1.4), Inches(4.3), Inches(0.4), "Questions for discussion", size=18, bold=True, color=ACCENT)
add_bullets(s, Inches(8.3), Inches(1.9), Inches(4.3), Inches(3.8), [
    "If an AI-generated proof is accepted by Lean, what exactly have we established?",
    "Can a perfectly verified program still be insecure?",
    "Where should human judgment remain in an AI-assisted workflow?",
], size=14)
banner(s, 6.05, "Final message: Use AI to explore more possibilities—and use verification to check the claims.", h=0.8, size=17)
notes(s, """Phần 5 · 7 phút (rút còn 5 phút nếu cần tổng đúng 45 phút), bao gồm kết luận và trao đổi ngắn.

Kết thúc bằng câu hỏi thứ hai: "Can a perfectly verified program still be insecure?"

Câu trả lời là có, nếu specification không mô tả đúng yêu cầu bảo mật, nếu mô hình bỏ sót một phần quan trọng của hệ thống, hoặc nếu các giả thiết cần thiết không đúng trong môi trường thực tế.

Đây là thông điệp phù hợp nhất để kết nối AI, Lean và bảo mật.

Phân bổ thời gian tổng thể:
- Slide 1–2: Giới thiệu và lộ trình — 2 phút
- Slide 3: Vì sao cần kiểm chứng — 5 phút
- Slide 4–6: Formal verification và Lean — 8 phút
- Slide 7–8: AI hỗ trợ chứng minh và các giới hạn — 10 phút
- Slide 9–11: Case study và quy trình phát hiện defect — 15 phút
- Slide 12: Kết luận và thảo luận — 5 phút
- Tổng: 45 phút
Nếu muốn dành 5–7 phút hỏi đáp độc lập, hãy rút phần case study xuống khoảng 12 phút.

Đề xuất để bài báo cáo có sức thuyết phục hơn: bổ sung một ví dụ thật từ dự án bảo mật đang làm, chỉ chọn một defect đã được kiểm tra, gồm:
- Một đoạn code hoặc sơ đồ trạng thái trước khi phân tích.
- Giả thuyết do AI đưa ra.
- Phản biện hoặc phản ví dụ do agent thứ hai tìm thấy.
- Bằng chứng xác nhận: test tái hiện, trace thực thi, mô hình, hoặc proof phù hợp.
- Một câu giải thích về tác động bảo mật và giới hạn của kết luận.""")

OUT = "/Users/hoangtruong/Documents/lean/Max/SparsePostQuantumRatchet/reportI.pptx"
prs.save(OUT)
print("Saved", OUT, "with", len(prs.slides), "slides")

