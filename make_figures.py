#!/usr/bin/env python3
"""Generate PNG figures for report.pptx into .tmp/figs/."""
import os
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.patches import FancyBboxPatch, FancyArrowPatch, Rectangle

OUT = "/Users/hoangtruong/Documents/lean/Max/SparsePostQuantumRatchet/.tmp/figs"
os.makedirs(OUT, exist_ok=True)
# Simple palette: white bg, navy text, blue = neutral/structure, red = defect, green = verified, grey = secondary
BG = "#FFFFFF"; CARD = "#F3F5F9"; W = "#1F2A44"; LG = "#3A4560"; MU = "#7A8299"
A = "#1F6FEB"; A2 = "#1F6FEB"; A3 = "#D7263D"; G = "#1E8E5A"; Y = "#7A8299"
RED_FILL = "#FBE9EB"
plt.rcParams.update({"font.family": "DejaVu Sans", "text.color": W, "axes.edgecolor": MU,
                     "axes.labelcolor": LG, "xtick.color": LG, "ytick.color": LG})

def fig(w, h):
    f, ax = plt.subplots(figsize=(w, h), dpi=200); f.patch.set_facecolor(BG); ax.set_facecolor(BG); return f, ax

def box(ax, x, y, w, h, text, fc=CARD, ec=A, fs=12, tc=W, bold=False, lw=1.5):
    ax.add_patch(FancyBboxPatch((x, y), w, h, boxstyle="round,pad=0.02,rounding_size=0.08", fc=fc, ec=ec, lw=lw))
    ax.text(x + w / 2, y + h / 2, text, ha="center", va="center", fontsize=fs, color=tc, fontweight="bold" if bold else "normal", wrap=True)

def arrow(ax, x1, y1, x2, y2, c=A, lw=1.8, style="-|>", ls="-"):
    ax.add_patch(FancyArrowPatch((x1, y1), (x2, y2), arrowstyle=style, color=c, lw=lw, mutation_scale=14, linestyle=ls))

def save(f, name):
    f.savefig(f"{OUT}/{name}.png", facecolor=BG, bbox_inches="tight", pad_inches=0.05); plt.close(f); print("wrote", name)

# ---------- 1. Defect status donut + severity bars ----------
f, (ax1, ax2) = plt.subplots(1, 2, figsize=(14, 6.0), dpi=200, gridspec_kw={"width_ratios": [1, 1.1]}); f.patch.set_facecolor(BG)
for ax in (ax1, ax2): ax.set_facecolor(BG)
vals = [27, 4, 15, 13, 2]; labels = ["Unfixed in SPQR", "Unfixed, mitigated by libsignal", "Confirmed by Lean proof (unfixed)", "Fixed (docs / Lean models)", "Latent, no fix needed"]
cols = [A3, "#F08A8A", A, G, MU]
wedges, _ = ax1.pie(vals, colors=cols, startangle=90, wedgeprops=dict(width=0.38, edgecolor=BG, linewidth=2))
ax1.text(0, 0.08, "63", ha="center", va="center", fontsize=36, fontweight="bold", color=W)
ax1.text(0, -0.24, "defects D1–D63", ha="center", va="center", fontsize=14, color=LG)
ax1.legend(wedges, [f"{l}  ({v})" for l, v in zip(labels, vals)], loc="upper center", bbox_to_anchor=(0.5, -0.02), fontsize=13, frameon=False, labelcolor=LG, ncol=1)
ax1.set_title("Fix status (REPORT_EXECUTIVE.md)", color=W, fontsize=16, fontweight="bold")
cats = ["Integer overflow", "Refinement / validation", "Authentication ordering", "Key erasure", "Spec–impl mismatch", "State-machine liveness", "Model soundness", "Constant-time", "Domain separation"]
cnt = [12, 8, 5, 4, 4, 3, 3, 2, 1]
bc = [MU, MU, A3, MU, MU, MU, MU, MU, MU]
ax2.barh(cats, cnt, color=bc, height=0.65)
for i, v in enumerate(cnt): ax2.text(v + 0.2, i, str(v), va="center", color=W, fontsize=13, fontweight="bold")
ax2.invert_yaxis(); ax2.set_xlim(0, 14); ax2.tick_params(labelsize=12); ax2.set_xticks([])
for sp in ax2.spines.values(): sp.set_visible(False)
ax2.set_title("Root-cause class (report.md §15)", color=W, fontsize=16, fontweight="bold")
ax2.text(13.8, 2, "← today's\n   case study", fontsize=12, color=A3, va="center", ha="right")
f.tight_layout(); save(f, "fig_defects")

# ---------- 2. Pipeline Rust -> Aeneas -> Lean ----------
f, ax = fig(14, 4.2); ax.set_xlim(0, 14); ax.set_ylim(0, 4.2); ax.axis("off")
stages = [("Rust source\nsrc/ (39 files)\nspqr v1.5.0", MU), ("Charon\nMIR → LLBC\nspqr.llbc (25 MB)", MU), ("Aeneas\nLLBC → Lean\nFuns.lean, 3 807 lines\n(never hand-edited)", A),
          ("Spec theorems\nSpqr/Specs/, 246 files\nhypotheses explicit", A), ("Lean 4 kernel\nlake build\n0 sorry", G)]
for i, (t, c) in enumerate(stages):
    x = 0.2 + i * 2.8; box(ax, x, 1.7, 2.5, 1.8, t, ec=c, fs=12.5)
    if i < 4: arrow(ax, x + 2.55, 2.6, x + 2.75, 2.6, c=LG)
box(ax, 2.0, 0.25, 7.5, 0.75, "hand-written models: TypesExternal / FunsExternal (VecDeque, HKDF, HMAC)", ec=MU, fs=12, tc=LG)
arrow(ax, 6.3, 1.03, 6.8, 1.68, c=MU, ls="--")
ax.text(13.6, 0.6, "a hypothesis the Rust\nnever checks ⇒ a defect", ha="right", fontsize=13, color=A3, fontweight="bold")
save(f, "fig_pipeline")

# ---------- 3. D1 blob -> panic flow ----------
f, ax = fig(14, 4.8); ax.set_xlim(0, 14); ax.set_ylim(0, 4.8); ax.axis("off")
ax.text(0.2, 4.45, "D1 — corrupted blob to panic (SPQR v1.5.0, src/chain.rs)", fontsize=14, color=W, fontweight="bold")
box(ax, 0.2, 2.2, 2.7, 1.5, "Persisted blob\n(protobuf bytes)\nnext.len() = 31", ec=MU, fs=12.5)
arrow(ax, 2.95, 2.95, 3.35, 2.95, c=LG)
box(ax, 3.4, 2.2, 3.1, 1.5, "from_pb  (L307)\ncopies fields verbatim,\nalways returns Ok(..)", ec=A3, fs=12.5)
arrow(ax, 6.55, 2.95, 6.95, 2.95, c=LG)
box(ax, 7.0, 2.2, 3.1, 1.5, "ChainEpochDirection\nnext.len() = 31\n(invariant I1 broken)", ec=A3, fs=12.5)
arrow(ax, 10.15, 2.95, 10.55, 2.95, c=LG)
box(ax, 10.6, 2.2, 3.2, 1.5, "next_key_internal (L230)\nassert_eq!(next.len(), 32)\n→ PANIC", fc=RED_FILL, ec=A3, fs=12.5, bold=True)
box(ax, 3.4, 1.15, 10.4, 0.75, "#[hax_lib::requires(next.len() == 32)]  — checked at PROOF time only; erased at run time", ec=MU, fs=12, tc=LG)
ax.text(0.2, 1.5, "App reopens session →\nloads blob → panics →\ncrash-loop (bricked)", fontsize=12, color=A3, va="center")
ax.text(0.2, 0.55, "Also proved (CorruptedBlobs.lean):   prev.len() % 36 ≠ 0 → get_never_ok      prev large & ctr < max_ooo → gc_never_ok", fontsize=12, color=LG)
save(f, "fig_d1_flow")

# ---------- 4. D21 sequence diagram ----------
f, ax = fig(13, 5.4); ax.set_xlim(0, 13); ax.set_ylim(0, 5.4); ax.axis("off")
xa, xb, xm = 1.8, 11.2, 6.5
for x, n, c in [(xa, "Alice", A), (xb, "Bob", A2), (xm, "Attacker\n(network only)", A3)]:
    box(ax, x - 0.8, 4.5, 1.6, 0.6, n, ec=c, fs=12, bold=True); ax.plot([x, x], [0.3, 4.5], color=MU, lw=1, ls="--")
def msg(y, x1, x2, t, c=LG):
    arrow(ax, x1, y, x2, y, c=c); ax.text((x1 + x2) / 2, y + 0.08, t, ha="center", fontsize=11, color=c)
msg(4.1, xa, xb, "honest ping-pong until Bob ∈ Ct2Sampled, epoch 1")
msg(3.75, xb, xa, "…")
ax.text(xa, 3.45, "epoch 1", ha="center", fontsize=11, color=A); ax.text(xb, 3.45, "epoch 1 · Ct2Sampled", ha="center", fontsize=11, color=A2)
msg(3.0, xm, xb, "[1, 2, 1, 0]   version=1 · epoch=2 · index=1 · type=None", c=A3)
box(ax, xb - 1.75, 2.15, 3.5, 0.7, "recv: epoch == 1+1 → KeysUnsampled(2)\nno mac_hdr; a DR key is returned", fc=RED_FILL, ec=A3, fs=11)
ax.text(xb, 1.9, "epoch 2", ha="center", fontsize=11.5, color=A3, fontweight="bold")
msg(1.55, xb, xa, "epoch-2 message", c=A2)
box(ax, xa - 1.6, 0.85, 3.2, 0.55, "Err(EpochOutOfRange(2))", fc=RED_FILL, ec=A3, fs=11.5)
msg(0.6, xa, xb, "epoch-1 message → Bob ignores (Ordering::Less)", c=A)
ax.text(6.5, 0.15, "× 50 rounds in d24_unauthenticated_epoch_advance_deadlocks_ratchet  →  permanent bidirectional deadlock", ha="center", fontsize=11.5, color=A3, fontweight="bold")
save(f, "fig_d21_sequence")

# ---------- 5. State machine: where the MAC is / isn't ----------
f, ax = fig(12, 4.6); ax.set_xlim(0, 12); ax.set_ylim(0, 4.6); ax.axis("off")
st = [("KeysUnsampled", 0.3), ("KeysSampled /\nHeaderSent", 2.6), ("Ct1Sent /\nNoHeaderReceived", 4.9), ("Ct1Acknowledged", 7.2), ("Ct2Sampled", 9.5)]
for n, x in st: box(ax, x, 2.2, 2.0, 0.9, n, ec=A2, fs=11)
for i in range(4): arrow(ax, st[i][1] + 2.05, 2.65, st[i + 1][1] - 0.05, 2.65, c=LG)
ax.text(0.3, 4.35, "src/v1/chunked/states.rs L275–533 — per-epoch state machine (send_ct side)", fontsize=12, color=W, fontweight="bold")
ax.text(9.5, 3.5, "MAC checked here ONLY when\ndecoded_message = Some(..)", fontsize=11, color=G)
arrow(ax, 9.4, 3.5, 8.3, 3.15, c=G)
box(ax, 3.9, 3.35, 3.9, 0.55, "StillReceiving: add_chunk → persist, NO MAC  (D16 poisoning)", fc=RED_FILL, ec=A3, fs=10.5)
arrow(ax, 5.9, 3.12, 5.9, 3.33, c=A3)
ax.add_patch(FancyArrowPatch((10.5, 2.18), (1.3, 2.18), connectionstyle="arc3,rad=-0.3", arrowstyle="-|>", color=A3, lw=2.2, mutation_scale=14))
ax.text(5.9, 0.35, "msg.epoch == epoch+1 → recv_next_epoch  —  NO Authenticator call   (D21)", ha="center", fontsize=12, color=A3, fontweight="bold")
save(f, "fig_state_machine")

# ---------- 6. libsignal clone-then-commit ----------
f, ax = fig(14, 5.4); ax.set_xlim(0, 14); ax.set_ylim(0, 5.4); ax.axis("off")
ax.text(0.2, 5.05, "libsignal a47ba487 · session_cipher.rs · decrypt_message_with_state", fontsize=14, color=W, fontweight="bold")
steps = [("1  clone session\nstate\nL455 / L475", MU), ("2  spqr::recv\non the CLONE\nL633 ← D21 fires", A3), ("3  Double-Ratchet\ndecrypt on clone\nL640–655", MU), ("4  verify\nenvelope MAC\nL657–661", A)]
for i, (t, c) in enumerate(steps):
    x = 0.2 + i * 2.6; box(ax, x, 3.0, 2.3, 1.6, t, ec=c, fs=12.5)
    if i < 3: arrow(ax, x + 2.35, 3.8, x + 2.55, 3.8, c=LG)
arrow(ax, 10.6, 4.1, 11.0, 4.4, c=G); box(ax, 11.05, 4.05, 2.8, 0.75, "MAC ok → commit clone\nL670–680", ec=G, fs=12)
arrow(ax, 10.6, 3.5, 11.0, 3.2, c=A3); box(ax, 11.05, 2.8, 2.8, 0.75, "MAC bad → drop clone", ec=A3, fs=12)
ax.text(0.2, 2.45, "Who is protected by this pattern?", fontsize=13.5, color=W, fontweight="bold")
tbl = [("Network-only forger", "clone dropped — protected", G), ("Authenticated but malicious peer", "MAC passes → mutated clone committed", A3),
       ("Any other embedder of the spqr crate", "no clone pattern → mutation persisted", A3), ("Corrupted storage (blob path)", "from_pb runs before any MAC — not covered", A3)]
for i, (k, v, c) in enumerate(tbl):
    y = 1.95 - i * 0.5
    ax.text(0.3, y, f"{k}", fontsize=12.5, color=LG, va="center"); ax.text(5.6, y, v, fontsize=12.5, color=c, fontweight="bold", va="center")
save(f, "fig_libsignal")


# ---------- 7. Harness numbers ----------
f, (ax1, ax2) = plt.subplots(1, 2, figsize=(14, 4.6), dpi=200, gridspec_kw={"width_ratios": [1.15, 1]}); f.patch.set_facecolor(BG)
for ax in (ax1, ax2): ax.set_facecolor(BG)
vals = [22508, 17379, 121, 0]
ax1.bar(["Err\n(rejected)", "Ok\n(accepted)", "Ok + DR key\nreturned", "Panics"], vals, color=[G, A, A3, MU])
for i, v in enumerate(vals): ax1.text(i, v + 500, f"{v:,}", ha="center", color=W, fontsize=14, fontweight="bold")
ax1.set_ylim(0, 27000); ax1.set_title("Fuzzing: 200 states × 200 forged messages", color=W, fontsize=14, fontweight="bold")
for sp in ax1.spines.values(): sp.set_visible(False)
ax1.tick_params(labelsize=12); ax1.set_yticks([])
ax1.text(2.0, 22500, "0 panics — true.\nD21 lives in the blue 'Ok' bar.", ha="center", fontsize=13, color=A3)
labels = ["Lean hypothesis\nctr ≤ u32::MAX − 390 451 572", "Rust limit\nu32::MAX"]
ax2.barh(labels, [3904515723 / 1e9, 4294967295 / 1e9], color=[A, A3], height=0.55)
ax2.text(3.904515723 + 0.05, 0, "3.90 ×10⁹", va="center", fontsize=12, color=W)
ax2.text(4.294967295 + 0.05, 1, "4.29 ×10⁹", va="center", fontsize=12, color=W)
ax2.set_xlim(0, 5.3); ax2.set_xlabel("counter value", fontsize=12); ax2.tick_params(labelsize=12); ax2.set_xticks([])
for sp in ax2.spines.values(): sp.set_visible(False)
ax2.set_title("The counter bound is fuel, not an invariant", color=W, fontsize=14, fontweight="bold")
ax2.text(0.1, -0.75, "An authenticated peer can raise ctr by ≤ max_jump per message;\nafter ~156 K messages no spec applies (L4-1 / D57).", fontsize=12, color=LG, va="top")
ax2.set_ylim(-1.3, 1.6)
f.tight_layout(); save(f, "fig_harness")

# ---------- 8. Three roles triangle ----------
f, ax = fig(9, 5); ax.set_xlim(0, 9); ax.set_ylim(0, 5); ax.axis("off")
pts = {"AI proposes": (4.5, 4.3, A2), "Formal tools check": (1.2, 0.9, A), "Human evaluates": (7.8, 0.9, G)}
for n, (x, y, c) in pts.items(): box(ax, x - 1.1, y - 0.35, 2.2, 0.7, n, ec=c, fs=13, bold=True)
arrow(ax, 3.6, 3.9, 1.9, 1.3, c=A2); ax.text(2.0, 2.9, "proof skeleton,\nharness, [1,2,1,0]", fontsize=11, color=LG, ha="center")
arrow(ax, 2.3, 0.9, 6.7, 0.9, c=A); ax.text(4.5, 0.5, "lake build ok · cargo test green · 0 sorry", fontsize=11, color=LG, ha="center")
arrow(ax, 7.2, 1.3, 5.4, 3.9, c=G); ax.text(7.1, 2.9, "spec, severity,\nexploitability", fontsize=11, color=LG, ha="center")
ax.text(4.5, 2.4, "D21", fontsize=25, color=W, ha="center", fontweight="bold")
ax.text(4.5, 1.95, "HIGH · mitigated by host · fix = reorder auth", fontsize=11, color=A3, ha="center")
save(f, "fig_roles")

# ---------- 9. Proof vs security ----------
from matplotlib.patches import Ellipse
f, ax = fig(14, 5.2); ax.set_xlim(0, 14); ax.set_ylim(0, 5.2); ax.axis("off")
ax.add_patch(Ellipse((6.6, 2.5), 12.8, 4.6, fc="#E8F5EE", ec=G, lw=2.5))
ax.add_patch(Ellipse((3.3, 2.4), 4.9, 3.0, fc="#E3EEFC", ec=A, lw=2.5))
ax.text(3.3, 3.35, "What Lean PROVED", fontsize=15, color=A, ha="center", fontweight="bold")
ax.text(3.3, 2.1, "ChainInv preserved by\nnew / send_key / recv_key\n\nkey_spec under the ctr bound\n\nrecv_hdr_chunk returns Ok", fontsize=12, color=LG, ha="center", va="center")
ax.text(9.0, 4.35, "What the system NEEDS", fontsize=15, color=G, ha="center", fontweight="bold")
ax.text(6.2, 2.5, "from_pb re-establishes ChainInv    ✗ D1\nctr never exceeds the bound        ✗ D57\nstate persisted only after MAC     ✗ D21\nVecDeque model is sound            ✗ D59", fontsize=13, color=A3, ha="left", va="center", family="DejaVu Sans Mono")
ax.text(12.6, 0.75, "63 defects live in\nthe green-minus-blue region", fontsize=12.5, color=W, ha="right")
save(f, "fig_proof_vs_security")
