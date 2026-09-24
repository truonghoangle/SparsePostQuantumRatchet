#!/usr/bin/env python3
"""Arithmetic model of `ChainEpochDirection::key` / `KeyHistory::{add, gc}` from `src/chain.rs`.

Purpose: exhibit a concrete counterexample to the bound claimed by the `hax_lib::requires`
annotation on `KeyHistory::add` / `KeyHistory::remove` and by the `hax_lib::assume!` inside
`ChainEpochDirection::key`:

    self.data.len() <= KeyHistory::KEY_SIZE * params.trim_size()

and to the struct comment on `KeyHistory::data`:

    // data.len() <= KEY_SIZE*TRIM_SIZE

The model tracks only key *indices* (the 32-byte payloads are irrelevant to the length
arithmetic), and mirrors the control flow of the Rust code line by line.  See
`docs/defects.md` (finding 10) for the write-up.
"""

KEY_SIZE = 36


def trim_size(max_ooo: int) -> int:
    # chain.rs L84-88
    return max_ooo * 11 // 10 + 1


class CED:
    """ChainEpochDirection restricted to `ctr` and the list of stored key indices."""

    def __init__(self) -> None:
        self.ctr = 0
        self.prev: list[int] = []

    def key(self, at: int, max_ooo: int, max_jump: int, log: list) -> int:
        """Mirror of `ChainEpochDirection::key` for the `at > ctr` branch.

        Returns the number of records held *immediately before* `gc` runs and appends one
        `(ctr, records_before_add, precondition_ok)` triple to `log` for every `add` call.
        """
        assert at > self.ctr
        assert at - self.ctr <= max_jump  # otherwise Err(KeyJump)
        if at > self.ctr + max_ooo:  # L265-269
            self.prev = []
        while at > self.ctr + 1:  # L270
            self.ctr += 1  # next_key_internal
            if self.ctr + max_ooo >= at:  # L279
                # Claimed precondition of `KeyHistory::add` (L138) / assume! (L281-282):
                pre_ok = len(self.prev) * KEY_SIZE <= KEY_SIZE * trim_size(max_ooo)
                log.append((self.ctr, len(self.prev), pre_ok))
                self.prev.append(self.ctr)  # add
        pre_gc = len(self.prev)
        # gc(self.ctr, params)  (L144-168)
        if len(self.prev) * KEY_SIZE >= trim_size(max_ooo) * KEY_SIZE:
            assert self.ctr >= max_ooo
            horizon = self.ctr - max_ooo
            self.prev = [k for k in self.prev if not horizon > k]
        self.ctr += 1  # final next_key_internal
        return pre_gc


def main() -> None:
    max_ooo, max_jump = 10, 100
    t = trim_size(max_ooo)
    print(f"max_ooo={max_ooo}  trim_size={t}  claimed max bytes = {KEY_SIZE * t}")
    c = CED()
    for at in (11, 14, 24):
        log: list = []
        pre_gc = c.key(at, max_ooo, max_jump, log)
        viol = [(ctr, n) for ctr, n, ok in log if not ok]
        print(
            f"key({at:2d}): adds={len(log):2d}  pre-GC records={pre_gc:2d} "
            f"({pre_gc * KEY_SIZE} B)  post-GC: ctr={c.ctr} prev={c.prev}"
        )
        if viol:
            print("        add() precondition VIOLATED at (ctr, records_before_add):", viol)

    # Randomised search for the worst pre-GC size and check of the corrected at-rest bound.
    import random

    random.seed(1)
    worst = 0
    rest_ok = True
    for _ in range(2000):
        c = CED()
        for _ in range(30):
            j = random.randint(0, max_ooo)
            worst = max(worst, c.key(c.ctr + 1 + j, max_ooo, max_jump, []))
            rest_ok &= len(c.prev) < t
    print(f"max pre-GC records observed = {worst}; "
          f"predicted (trim_size - 1) + (max_ooo - 1) = {(t - 1) + (max_ooo - 1)}")
    print("at-rest invariant  records < trim_size  always held:", rest_ok)
    d = 2000
    print(f"defaults (max_ooo={d}): claimed max records = {trim_size(d)}, "
          f"actual pre-GC max = {trim_size(d) - 1 + d - 1}")


if __name__ == "__main__":
    main()
