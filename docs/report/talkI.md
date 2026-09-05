# Talk Script (Simple Version) — Formal Verification of SPQR in Lean 4

**Duration:** 15 minutes (≈ 1 min 40 s per slide × 9 slides)
**Companion deck:** [`report.pptx`](./report.pptx)
**Style:** Short sentences. Plain words. Speak slowly.

---

## Slide 1 — What is SPQR and what are we doing to it?

*≈ 1 min 40 s*

Hi everyone. Thank you for being here.

Today I want to tell you about a project called SPQR. The letters stand for Sparse Post-Quantum Ratchet. It is a piece of software made by Signal — the private messaging app many of you probably use.

So what does SPQR do? When you send a message on Signal, your message is locked with a secret key. Right now, that key is safe. But one day, quantum computers may be able to break it. SPQR adds a second layer of protection — a quantum-resistant lock — so your messages stay private even in that future.

Here is the clever part. That quantum-resistant lock is big. Too big to send in one message. So SPQR cuts it into small pieces and spreads them across many messages. Even if some pieces are lost, the other side can still put the lock back together. Think of it like a jigsaw puzzle where you only need most of the pieces, not all of them.

Now, our job is not to build SPQR. Signal already built it. Our job is to *prove* it is correct. Not by testing — testing only checks some examples. We write mathematical proofs that cover *every possible case*. A computer checks those proofs for us, so there is no room for human error. If the proof passes, the code is correct. Period.

We do this using a tool called Lean. Lean is a proof checker. We translate the original code into Lean, and then we write and verify our proofs there.

---

## Slide 2 — Results so far (numbers)

*≈ 1 min 40 s*

Let me share where we stand today.

The SPQR codebase has 312 functions that we can verify. So far, we have written proofs for 147 of them. That is about half — 47 percent. And out of those 147, all but one are completely finished. The one that is not finished is waiting on a technical roadblock I will explain later.

Let me put that in perspective. We have written over 550 mathematical statements in total. These are not comments or notes — they are machine-checked facts about the actual code. The computer verified every single one.

The hardest part — the math at the core, the puzzle-piece logic — is 100 percent done. What is left is mostly the higher-level control flow: how the system starts a session, sends a message, and receives a message. Those are next.

One important thing: when I say "verified," I mean we proved things about the *real* code, not a simplified copy. We translated the actual Rust source into Lean and proved facts about that translation. This is as close to the real thing as formal verification gets.

---

## Slide 3 — Growth over time

*≈ 1 min 30 s*

This chart shows how fast we have been moving, week by week, since April.

In the beginning, progress was slow. That is normal. We were building tools — setting up the translation from Rust to Lean, writing helper tactics, and building a math library from scratch.

But that early investment paid off. Once the tools were ready, we started moving much faster. You can see a big jump around weeks 31 and 32 — that is when we verified 30 functions in a single week.

Think of it like building a house. The foundation takes a long time and you cannot see much happening. But once the foundation is solid, the walls go up quickly.

The most recent milestone was last week — we finished the proof for a function called "garbage collection." I will show you that story in Slide 7. It is our single largest proof: 962 lines of Lean for just 20 lines of Rust.

---

## Slide 4 — File-by-file report

*≈ 1 min 50 s*

Let me break this down by area. You are looking at four cards on the slide.

The first card is the number system — the special arithmetic SPQR uses. Think of it as the math behind the puzzle pieces. All 13 functions: done. 100 percent.

The second card is the puzzle logic itself — how pieces are created, split, and reassembled. All 32 functions: done. 100 percent.

The third card is the key chain — the part that manages your secret keys over time. It keeps track of which keys have been used and cleans up old ones. We are at 44 percent here. The basic building blocks are done, but the top-level functions still need work.

The fourth card is how data is packed and unpacked for sending over the network. 32 out of 39 functions are done. The remaining seven involve some tricky loops that we are still working through.

So the pattern is clear: the deep math is fully verified. The middle layer is mostly done. The outer layer — the part the application touches — is next.

---

## Slide 5 — A real example: proving the puzzle-piece math

*≈ 2 min*

Let me show you what one of these proofs actually looks like. This is the most important function in the codebase. It is called "Lagrange interpolate."

Here is the idea in plain English. Imagine you have several dots on a graph. There is exactly one smooth curve that passes through all of them. This function finds that curve. SPQR uses it to reconstruct the big quantum-resistant key from the small pieces that arrived in different messages.

The textbook way to find this curve is straightforward but slow. The Rust code uses a shortcut — a three-step trick that is much faster. Step one: build a template. Step two: adjust the template for each dot. Step three: combine the results.

Our proof says: the output of this fast shortcut is *exactly the same* as the textbook answer. Not "close enough" — exactly the same, coefficient by coefficient. The computer checked this. So we know the fast code and the math agree perfectly.

This proof took several weeks. But now it is done, and every function that uses this one can build on top of it. That is the power of this approach — once you prove something, you never have to prove it again.

---

## Slide 6 — How proofs build on each other

*≈ 1 min 40 s*

This slide shows something I think is really beautiful about formal verification: proofs compose.

Here is a simple example. There is a small wrapper function that checks "do I have a decoder?" If yes, it feeds a new piece of data into that decoder. If no, it does nothing. Three lines of code.

We proved this wrapper works correctly — for any decoder, not just one specific type. The proof says: if you started with a decoder, you still have one afterward, and the data was fed in correctly.

Then we plugged in the specific puzzle-piece decoder from Slide 5. The combined result says: after calling this wrapper, the puzzle-piece decoder inside has correctly absorbed the new piece. Its list of received pieces grew by one, with the right values.

The proof of this combined fact is just four lines of Lean. We reuse the wrapper proof, plug in the decoder proof from Slide 5, and we are done.


---

## Slide 7 (1/2) — The hardest proof: cleaning up old keys

*≈ 1 min 50 s*

Now let me tell you about the hardest proof in the whole project.

SPQR keeps a list of old keys so it can handle messages that arrive out of order. But that list cannot grow forever — it would use too much memory. So there is a cleanup function called "gc," short for garbage collection. It scans the list and deletes keys that are too old.

Sounds simple, right? Twenty lines of code. But proving it correct took 962 lines of proof. A previous team tried to verify this function with a different tool and gave up. Let me explain why it is so hard.

First, the keys are stored as raw bytes — just numbers in memory. To compare them, we have to prove that comparing the bytes gives the same answer as comparing the actual key numbers. That is not obvious when you are dealing with four-byte sequences.

Second, when the code deletes a key, it does not shift everything down. Instead, it copies the last key into the empty spot. That is fast, but it scrambles the order. A key that was at the end is now in the middle. And that moved key might itself be old and need to be deleted next. So you cannot just say "everything before position X is fine."

Third, what does "correct" even mean here? We need to say three things. One: every key that survived is young enough to keep. Two: every key that was young enough to keep did survive. Three: nothing got duplicated or lost in the shuffle. For that third part, we need a precise map showing where each surviving key came from.

---

## Slide 7 (2/2) — Getting the proof right

*≈ 1 min 30 s*

This table shows how the proof evolved over about a week — four versions.

The first version was technically true. It described the function correctly. But it had a fatal flaw: it demanded conditions that were way too strict. For example, it required the current key number to be at least 2000. That works with the default settings, but not with smaller settings that are perfectly valid.

Here is a concrete example. Imagine the current key is number 7, and the list has just one old key in it. The code looks at the list, sees it is tiny, and returns immediately — nothing to clean up. But the first version of our proof required key number 2000 or higher. Seven is less than 2000, so the proof cannot even start. The caller is stuck.

The final version, finished on August 31st, fixed this. It only requires the strict conditions when the code actually does some cleaning. If the list is small and the code returns early, no extra conditions are needed.

We also added the precise map I mentioned — showing exactly where each surviving key came from in the original list. That map is what the next proof up the chain needs.


---

## Slide 8 — The front door: what the app actually sees

*≈ 1 min 40 s*

Now let me zoom out. Everything I have shown you so far — the math, the puzzle pieces, the key cleanup — those are all internal. The application never sees them.

The application sees just one file: lib.rs. Think of it as the front door. Behind that door is a big building with many rooms, but the visitor only interacts with the door.

That door has five buttons. "Start a session." "Send a message." "Receive a message." "Check the protocol version." And "turn it off." That is it. Everything going in and out is just a list of bytes — simple data, nothing complicated.

Seven out of sixteen functions in this file already have proofs. The small helper functions are done. What is not done yet are the three big ones: start, send, and receive.

Why are those last? Because they call everything else. "Send" uses the key chain, the puzzle-piece encoder, the data packer, and more. We cannot prove "send" until we have proved all the things it depends on.

This is the bottom-up approach. We started at the deepest layer — the math. Then we moved up to the puzzle logic. Then the key management. And now we are approaching the top — the front door. Each layer builds on the one below it.

There is one shared roadblock: the data format library. Once we handle that, the three big functions can all be proved, because everything they call will already be verified.

---

## Slide 9 — The big picture and what comes next

*≈ 1 min 40 s*

Let me close with the full picture. On the left side of this slide, you see our architecture — five layers, top to bottom.

At the very top: the application. Signal's app. It only sees simple data going in and out.

One layer down: the front door — five public functions. This is the only part the app talks to.

Below that: the internal modules — key chains, encoders, decoders, and more. We have proved about half of these so far.

Below that: the translated code. We used automated tools to convert the original Rust code into Lean, the language our proof checker understands.

And at the bottom: our hand-written proofs. 147 functions specified. 146 fully proved. Over 500 theorems total.

On the right side, you see what comes next. The first priority is handling the data format library — that one fix unblocks four functions at once. Then we prove the three big entry points: start, send, and receive. The goal is an end-to-end statement: "for every valid input, if one side sends and the other receives, they get the same key, and the system stays in a valid state."

That is a statement no amount of testing can make. Testing checks examples. We check *all cases*.

The bridge — the front door — is the last thing we prove, not the first. And that is by design. By the time we get there, every piece underneath is already verified. The capstone just clicks into place.

Thank you very much. I am happy to take any questions.

