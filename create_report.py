#!/usr/bin/env python3
from pptx import Presentation
from pptx.util import Inches, Pt
from pptx.dml.color import RGBColor
from pptx.enum.text import PP_ALIGN
from pptx.enum.shapes import MSO_SHAPE
prs = Presentation()
prs.slide_width, prs.slide_height = Inches(13.333), Inches(7.5)
# Simple palette: white bg, navy text, blue accent, red = defect, green = verified, grey = secondary
D=RGBColor(0xFF,0xFF,0xFF); S=RGBColor(0xF3,0xF5,0xF9)
A=RGBColor(0x1F,0x6F,0xEB); A2=RGBColor(0x1F,0x6F,0xEB)
A3=RGBColor(0xD7,0x26,0x3D); W=RGBColor(0x1F,0x2A,0x44)
L=RGBColor(0x3A,0x45,0x60); M=RGBColor(0x7A,0x82,0x99)
G=RGBColor(0x1E,0x8E,0x5A)
def bg(s,c): s.background.fill.solid(); s.background.fill.fore_color.rgb=c
def tb(s,l,t,w,h,tx,sz=18,c=W,b=False,a=PP_ALIGN.LEFT):
    tf=s.shapes.add_textbox(Inches(l),Inches(t),Inches(w),Inches(h)).text_frame
    tf.word_wrap=True;p=tf.paragraphs[0];p.text=tx;p.font.size=Pt(sz)
    p.font.color.rgb=c;p.font.bold=b;p.font.name="Calibri";p.alignment=a
def bl(s,l,t,w,h,items,sz=16,c=L,bc=A):
    tf=s.shapes.add_textbox(Inches(l),Inches(t),Inches(w),Inches(h)).text_frame
    tf.word_wrap=True
    for i,item in enumerate(items):
        p=tf.paragraphs[0] if i==0 else tf.add_paragraph()
        p.space_after=Pt(8);r=p.add_run();r.text=u"\u25b8 ";r.font.size=Pt(sz);r.font.color.rgb=bc;r.font.name="Calibri"
        r2=p.add_run();r2.text=item;r2.font.size=Pt(sz);r2.font.color.rgb=c;r2.font.name="Calibri"
def rc(s,l,t,w,h,fc):
    sh=s.shapes.add_shape(MSO_SHAPE.ROUNDED_RECTANGLE,Inches(l),Inches(t),Inches(w),Inches(h))
    sh.fill.solid();sh.fill.fore_color.rgb=fc;sh.line.fill.background()
def ln(s,l,t,w):
    sh=s.shapes.add_shape(MSO_SHAPE.RECTANGLE,Inches(l),Inches(t),Inches(w),Pt(4))
    sh.fill.solid();sh.fill.fore_color.rgb=A;sh.line.fill.background()
def code(s,l,t,w,h,tx,sz=13,c=RGBColor(0x1F,0x2A,0x44)):
    rc(s,l,t,w,h,RGBColor(0xEE,0xF1,0xF6))
    tf=s.shapes.add_textbox(Inches(l+0.15),Inches(t+0.1),Inches(w-0.3),Inches(h-0.2)).text_frame
    tf.word_wrap=True
    for i,line in enumerate(tx.split("\n")):
        p=tf.paragraphs[0] if i==0 else tf.add_paragraph()
        p.text=line;p.font.size=Pt(sz);p.font.color.rgb=c;p.font.name="Menlo"
def hdr(s,num,title,mins,cl):
    tb(s,0.8,0.3,1,0.7,num,36,cl,True);tb(s,1.7,0.33,11.2,0.7,title,30,W,True)
    ln(s,0.8,1.0,4);tb(s,0.8,1.05,10,0.4,mins,15,M)
def qa(s,l,t,w,q,a,sz=15):
    """Question heading + answer bullets, returns height used"""
    tb(s,l,t,w,0.4,q,17,A,True)
    bl(s,l,t+0.4,w,0.3*len(a)+0.3,a,sz)

FIGS="/Users/hoangtruong/Documents/lean/Max/SparsePostQuantumRatchet/.tmp/figs"
def figslide(s_title,img,cap,w=11.7):
    """Image slide; image capped at 4.6in so the caption always fits above 7.0in."""
    from PIL import Image
    s=prs.slides.add_slide(prs.slide_layouts[6]);bg(s,D)
    tsz=30 if len(s_title)<=42 else 26
    tb(s,0.8,0.3,11.7,0.7,s_title,tsz,W,True);ln(s,0.8,0.95,4)
    path=f"{FIGS}/{img}.png"
    iw,ih=Image.open(path).size
    h=w*ih/iw
    if h>4.6: h=4.6; w=h*iw/ih
    left=(13.333-w)/2
    s.shapes.add_picture(path,Inches(left),Inches(1.15),Inches(w),Inches(h))
    tb(s,0.8,1.3+h,11.7,0.8,cap,15,L)

# S1 Title
s=prs.slides.add_slide(prs.slide_layouts[6]);bg(s,D)
ln(s,1.5,2.2,10.3)
tb(s,1.5,2.4,10.3,1.8,"From AI-Assisted Verification\nto Security Defect Discovery",42,W,True)
tb(s,1.5,4.4,10.3,0.9,"Case study: formally verifying Signal's Sparse Post-Quantum Ratchet (SPQR) in Lean 4",22,L)
tb(s,1.5,5.4,10.3,0.6,"Rust \u2192 Aeneas \u2192 Lean 4  \u00b7  246 spec files  \u00b7  63 defects (D1\u2013D63)",20,A)
tb(s,1.5,6.1,10.3,0.5,"October 2026",18,M)

# S2 Agenda
s=prs.slides.add_slide(prs.slide_layouts[6]);bg(s,D)
tb(s,0.8,0.4,11,0.8,"Seminar Structure (45 min)",36,W,True);ln(s,0.8,1.15,4)
for i,(n,ti,d,cl) in enumerate([("01","The Challenge: Can We Trust Software?","5 min",A),("02","What Is Formal Verification?","8 min",A2),("03","How AI Assists Formal Verification","10 min",A),("04","From Verification to Security Defect Discovery","15 min",A3),("05","Lessons, Limitations, and Takeaways","7 min",A2)]):
    y=1.7+i*1.05;rc(s,0.8,y,11.5,0.85,S);tb(s,1.1,y+0.08,0.8,0.6,n,30,cl,True);tb(s,2.0,y+0.15,8.2,0.6,ti,22,W);tb(s,10.3,y+0.17,1.7,0.6,d,20,M,a=PP_ALIGN.RIGHT)




# ===== PART 1 =====
figslide(s_title="D1: From Corrupted Blob to Panic",img="fig_d1_flow",cap="Nothing between the blob and the assert re-checks next.len(); the hax contract is verified only at proof time.")

# ===== PART 2 =====
s=prs.slides.add_slide(prs.slide_layouts[6]);bg(s,D)
hdr(s,"02","Testing vs. Formal Verification","8 minutes",A)
rc(s,0.8,1.6,5.7,4.6,S);tb(s,1.1,1.75,5.2,0.5,"Testing",24,A3,True)
bl(s,1.1,2.4,5.2,4,["Runs the program on chosen inputs","40 000 forged messages: 0 panics","Shows presence of bugs, never absence","Missed every blob-path defect (D1, D19, D23 ...)"],18,L,A3)
rc(s,6.9,1.6,5.7,4.6,S);tb(s,7.2,1.75,5.2,0.5,"Formal verification",24,A,True)
bl(s,7.2,2.4,5.2,4,["States a property for ALL inputs and proves it","246 Lean spec files, 0 sorry","Every theorem names its hypotheses","A hypothesis the Rust never checks = a defect"],18,L,A)
tb(s,0.8,6.4,11.7,0.6,"Signal's own tests and hax/F* proofs passed. The 63 defects were found by asking what each proof had to assume.",15,M)

figslide(s_title="The Verification Pipeline",img="fig_pipeline",cap="Funs.lean is generated and trusted. The hand-written external models (dashed) are where an unsound model (D59) silently weakens proofs.")
figslide(s_title="What Fuzzing Showed \u2014 and Didn't",img="fig_harness",cap="Left: nothing panics, yet D21 lives on the accepted (blue) path. Right: the Lean counter bound is a hypothesis a peer can exceed after ~156 K messages.")
# ===== PART 3 =====
# ===== PART 4 =====
s=prs.slides.add_slide(prs.slide_layouts[6]);bg(s,D)
hdr(s,"04","The Project: Signal's SPQR, Re-verified in Lean 4","15 minutes",A3)
for i,(k,v) in enumerate([("What","Sparse Post-Quantum Ratchet: the ML-KEM layer of Signal's Triple Ratchet (Rust crate spqr v1.5.0)"),("Upstream","Signal verifies it with hax \u2192 F*"),("Ours","Independent re-verification: Rust \u2192 Aeneas \u2192 Lean 4, 246 spec theorems"),("Result","63 defects (D1\u2013D63), each backed by a Lean proof or a runnable Rust counterexample")]):
    y=1.55+i*0.95;rc(s,0.8,y,11.7,0.8,S);tb(s,1.1,y+0.15,1.6,0.5,k,18,A,True);tb(s,2.7,y+0.15,9.6,0.6,v,16,L)
tb(s,0.8,5.4,11.7,0.5,"Three root-cause patterns",19,A,True)
for i,(t,ids) in enumerate([("Authenticate after persist","D16 D21 D22 D35 D36 D62"),("from_pb copies without validating","D1 D11\u2013D14 D18 D19 D23 ... D61"),("assume! erased at run time","D2 D3 D5 D8 D9 D25 D29 D37 D56 D57")]):
    x=0.8+i*3.95;rc(s,x,5.9,3.75,1.0,S);tb(s,x+0.2,5.95,3.4,0.45,t,14,W,True);tb(s,x+0.2,6.4,3.4,0.4,ids,12,M)

figslide(s_title="63 Defects at a Glance",img="fig_defects",cap="Left: fix status. Right: root-cause class \u2014 overflow and missing validation dominate by count; authentication ordering (red) is today's case study.")
figslide(s_title="D21 as a Sequence Diagram",img="fig_d21_sequence",cap="One unauthenticated 4-byte message moves Bob to epoch 2. Alice rejects all of Bob's messages; Bob ignores all of Alice's. Permanent deadlock.",w=10.5)
figslide(s_title="Where the MAC Is \u2014 and Isn't \u2014 Checked",img="fig_state_machine",cap="Green: the only edges that call the MAC. Red: edges that persist state with no Authenticator call. D21 is the red back-edge.")

figslide(s_title="Why Signal Is Safe From D21 \u2014 and Who Isn't",img="fig_libsignal",cap="libsignal runs spqr::recv on a clone and commits only after the MAC passes. The protection lives outside SPQR; peers, other embedders and storage bypass it.")

figslide(s_title="Three Roles, One Defect",img="fig_roles",cap="No arrow is skippable: the forged bytes came from AI, the deadlock proof from cargo/Lean, the exploitability verdict from reading libsignal.",w=8.5)

figslide(s_title="Why a Proof Is Not a Security Guarantee",img="fig_proof_vs_security",cap="Everything in the blue ellipse is machine-checked. Every defect is a true statement about the green region that no theorem mentioned.")

# ===== Key message =====
s=prs.slides.add_slide(prs.slide_layouts[6]);bg(s,D)
tb(s,0.8,0.4,10,0.7,"Key Message",36,W,True);ln(s,0.8,1.05,3)
rc(s,1.0,1.6,11.3,4.8,S)
tb(s,1.3,1.85,10.7,1.4,"Even a Lean proof accepted by the kernel establishes only\nthe formal proposition under its stated assumptions.",26,W,True,PP_ALIGN.CENTER)
tb(s,1.3,3.35,10.7,1.4,"It does not, by itself, establish that the specification captures\nevery security requirement of the real-world system.",24,A3,a=PP_ALIGN.CENTER)
tb(s,1.3,4.9,10.7,1.3,"SPQR: 246 spec files, 0 sorry, ChainInv proved \u2014 and still 63 defects,\nfound precisely by asking what each proof had to assume.",20,M,a=PP_ALIGN.CENTER)

# ===== Thank you =====
s=prs.slides.add_slide(prs.slide_layouts[6]);bg(s,D)
ln(s,4,2.8,5.3)
tb(s,2,3.1,9.3,1,"Thank You",44,W,True,PP_ALIGN.CENTER)
tb(s,2,4.3,9.3,0.6,"Questions & Discussion",26,M,a=PP_ALIGN.CENTER)
tb(s,2,5.0,9.3,0.8,"docs/report.md \u00b7 docs/listDefects.md \u00b7 docs/classificationBug.md \u00b7 docs/bugSecurityRemote.md\nSpqr/Specs/Bugs/ProtocolDoS.lean \u00b7 Spqr/Specs/Bugs/CorruptedBlobs.lean \u00b7 docs/protocol_driver_counterexamples.rs.txt",15,M,a=PP_ALIGN.CENTER)

prs.save("/Users/hoangtruong/Documents/lean/Max/SparsePostQuantumRatchet/report.pptx")
print("Done! slides:",len(prs.slides))

