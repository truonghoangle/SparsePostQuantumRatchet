// Copyright 2025 Signal Messenger, LLC
// SPDX-License-Identifier: AGPL-3.0-only

use super::{Direction, Epoch, EpochSecret, Error};
use crate::kdf;
use crate::proto::pq_ratchet as pqrpb;
use crate::proto::pq_ratchet::ChainParams as ChainParamsPB;
use std::cmp::Ordering;
use std::collections::VecDeque;

/// Parameters for controlling the behavior of PQR key chains.
/// It's recommended to use the Default API for overriding values,
/// as future values may be added to this struct, and Default allows
/// them to be added in a backwards-compatible fashion.
/// IE:  let params = ChainParams{max_jump: 10, ..Default::default()};
#[derive(Clone, Copy)]
pub struct ChainParams {
    /// Disallow requesting a key that is more than MAX_JUMP ahead of `ctr`.
    /// If zero, defaults to the current library-compiled default value.
    pub max_jump: u32,
    /// Keep around keys back to at least `ctr - MAX_OOO_KEYS`, in case an out-of-order
    /// message comes in.  Messages older than this that arrive out-of-order
    /// will not be able to be decrypted and will return Error::KeyTrimmed.
    /// If zero, defaults to the current library-compiled default value.
    pub max_ooo_keys: u32,
}

impl Default for ChainParams {
    fn default() -> Self {
        DEFAULT_CHAIN_PARAMS
    }
}

const DEFAULT_CHAIN_PARAMS: ChainParams = ChainParams {
    max_jump: 25_000,
    max_ooo_keys: 2_000,
};

impl ChainParams {
    pub(crate) fn into_pb(self) -> ChainParamsPB {
        ChainParamsPB {
            max_jump: if self.max_jump == DEFAULT_CHAIN_PARAMS.max_jump {
                0
            } else {
                self.max_jump
            },
            max_ooo_keys: if self.max_ooo_keys == DEFAULT_CHAIN_PARAMS.max_ooo_keys {
                0
            } else {
                self.max_ooo_keys
            },
        }
    }

    /// Public wrapper for test utilities and benchmarks.
    /// For internal use, call `into_pb` directly.
    #[cfg(feature = "test-utils")]
    pub fn into_pb_test(self) -> ChainParamsPB {
        self.into_pb()
    }
}

impl ChainParamsPB {
    // The Default for protobufs is to have everything be zeros.  Therefore,
    // we use some getter functions locally to apply sane defaults to values that
    // are not explicitly set.

    fn max_jump_or_default(&self) -> u32 {
        if self.max_jump > 0 {
            self.max_jump
        } else {
            DEFAULT_CHAIN_PARAMS.max_jump
        }
    }
    fn max_ooo_keys_or_default(&self) -> u32 {
        if self.max_ooo_keys > 0 {
            self.max_ooo_keys
        } else {
            DEFAULT_CHAIN_PARAMS.max_ooo_keys
        }
    }
    /// When the size of our key history exceeds this amount, we run a
    /// garbage collection on it.
    fn trim_size(&self) -> usize {
        let max_ooo = self.max_ooo_keys_or_default() as usize;
        hax_lib::assume!(max_ooo < 390451572);
        max_ooo * 11 / 10 + 1
    }
}

struct KeyHistory {
    // Keys are stored as [u8; 4][u8; 32], where the first is the index as a BE32
    // and the second is the key.
    // data.len() <= KEY_SIZE*TRIM_SIZE
    data: Vec<u8>,
}

/// ChainEpochDirection keeps track of keys related to either half of send/recv.
struct ChainEpochDirection {
    ctr: u32,
    // next.len() == 32
    next: Vec<u8>,
    prev: KeyHistory,
}

/// ChainEpoch keeps state on a single epoch's keys.
struct ChainEpoch {
    send: ChainEpochDirection,
    recv: ChainEpochDirection,
}

/// Chain keeps track of keys for all epochs.
pub struct Chain {
    dir: Direction,
    current_epoch: Epoch,
    send_epoch: Epoch,
    links: VecDeque<ChainEpoch>, // stores [link[current_epoch-N] .. link[current_epoch]]
    // next_root.len() == 32
    next_root: Vec<u8>,
    params: pqrpb::ChainParams,
}

/// We keep around this many epochs to keep prior to the current send epoch.
/// We'll always keep the send epoch and any subsequent epochs.
const EPOCHS_TO_KEEP_PRIOR_TO_SEND_EPOCH: usize = 1;

#[hax_lib::attributes]
impl KeyHistory {
    /// Size in bytes of a single key stored within a KeyHistory.
    const KEY_SIZE: usize = 4 + 32;

    fn new() -> Self {
        Self {
            data: Vec::with_capacity(Self::KEY_SIZE * 2),
        }
    }

    #[hax_lib::requires(_params.trim_size() < 119304647 && self.data.len() <= KeyHistory::KEY_SIZE * _params.trim_size())]
    fn add(&mut self, k: (u32, [u8; 32]), _params: &pqrpb::ChainParams) {
        self.data.extend_from_slice(&k.0.to_be_bytes()[..]);
        self.data.extend_from_slice(&k.1[..]);
    }

    #[hax_lib::opaque] // ordering of slices needed
    fn gc(&mut self, current_key: u32, params: &pqrpb::ChainParams) {
        if self.data.len() >= params.trim_size() * Self::KEY_SIZE {
            // We assume that k.0 is the highest key index we've ever seen, and base
            // our trimming on that.
            assert!(current_key >= params.max_ooo_keys_or_default());
            let trim_horizon = &(current_key - params.max_ooo_keys_or_default()).to_be_bytes()[..];

            // This does a single O(n) pass over our list, dropping all keys less than
            // our computed trim horizon.
            let mut i: usize = 0;
            while i < self.data.len() {
                if matches!(
                    trim_horizon.cmp(&self.data[i..i + 4]),
                    std::cmp::Ordering::Greater
                ) {
                    self.remove(i, params);
                    // Don't advance i here; we could have replaced the value there-in
                    // with another old key.
                } else {
                    i += Self::KEY_SIZE;
                }
            }
        }
    }

    fn clear(&mut self) {
        self.data.clear();
    }

    #[hax_lib::requires(my_array_index <= self.data.len() && _params.trim_size() < 119304647 && self.data.len() <= KeyHistory::KEY_SIZE * _params.trim_size())]
    fn remove(&mut self, mut my_array_index: usize, _params: &pqrpb::ChainParams) {
        if my_array_index + Self::KEY_SIZE < self.data.len() {
            let new_end = self.data.len() - Self::KEY_SIZE;
            self.data.copy_within(new_end.., my_array_index);
            my_array_index = new_end;
        }
        self.data.truncate(my_array_index);
    }

    #[hax_lib::opaque] // needs a model of step_by loop with return
    fn get(
        &mut self,
        at: u32,
        current_ctr: u32,
        params: &pqrpb::ChainParams,
    ) -> Result<Vec<u8>, Error> {
        assert_eq!(self.data.len() % Self::KEY_SIZE, 0);
        if at + (params.max_ooo_keys_or_default()) < current_ctr {
            // We've already discarded this because it's too old.
            return Err(Error::KeyTrimmed(at));
        }
        let want = at.to_be_bytes();
        for i in (0..self.data.len()).step_by(Self::KEY_SIZE) {
            if self.data[i..i + 4] == want {
                let out = self.data[i + 4..i + Self::KEY_SIZE].to_vec();
                self.remove(i, params);
                return Ok(out);
            }
        }
        // This is a key we should have and we don't, so it must have already
        // been requested.
        Err(Error::KeyAlreadyRequested(at))
    }
}

#[hax_lib::attributes]
impl ChainEpochDirection {
    fn new(k: &[u8]) -> Self {
        Self {
            ctr: 0,
            prev: KeyHistory::new(),
            next: k.to_vec(),
        }
    }

    #[hax_lib::requires(self.next.len() > 0 && self.ctr < u32::MAX)]
    fn next_key(&mut self) -> (u32, Vec<u8>) {
        let (idx, key) = Self::next_key_internal(&mut self.next, &mut self.ctr);
        (idx, key.to_vec())
    }

    #[hax_lib::requires(next.len() > 0 && *ctr < u32::MAX)]
    #[hax_lib::ensures(|_| *future(ctr) == ctr + 1)]
    fn next_key_internal(next: &mut [u8], ctr: &mut u32) -> (u32, [u8; 32]) {
        assert!(!next.is_empty());
        *ctr += 1;
        let mut genr8r = [0u8; 64];
        kdf::hkdf_to_slice(
            &[0u8; 32], // 32 is the hash output length
            &*next,
            [
                ctr.to_be_bytes().as_slice(),
                b"Signal PQ Ratchet V1 Chain Next",
            ]
            .concat()
            .as_slice(),
            &mut genr8r,
        );
        next.copy_from_slice(&genr8r[..32]);
        (*ctr, genr8r[32..].try_into().expect("correct size"))
    }

    fn key(&mut self, at: u32, params: &pqrpb::ChainParams) -> Result<Vec<u8>, Error> {
        match at.cmp(&self.ctr) {
            Ordering::Greater => {
                if at - self.ctr > params.max_jump_or_default() {
                    return Err(Error::KeyJump(self.ctr, at));
                }
            }
            Ordering::Less => {
                return self.prev.get(at, self.ctr, params);
            }
            Ordering::Equal => {
                // We've already returned this key once, we won't do it again.
                return Err(Error::KeyAlreadyRequested(at));
            }
        }
        hax_lib::assume!(
            params.max_ooo_keys_or_default() < 390451572 && self.ctr <= u32::MAX - 390451572
        );
        if at > self.ctr + params.max_ooo_keys_or_default() {
            // We're about to make all currently-held keys obsolete - just remove
            // them all.
            self.prev.clear();
        }
        while at > self.ctr + 1 {
            hax_lib::loop_invariant!(self.ctr < u32::MAX);
            hax_lib::loop_decreases!(u32::MAX - self.ctr);
            hax_lib::assume!(self.next.len() > 0);
            let k = Self::next_key_internal(&mut self.next, &mut self.ctr);
            hax_lib::assume!(
                params.max_ooo_keys_or_default() < 390451572 && self.ctr <= u32::MAX - 390451572
            );
            // Only add keys into our history if we're not going to immediately GC them.
            if self.ctr + params.max_ooo_keys_or_default() >= at {
                hax_lib::assume!(
                    params.trim_size() < 119304647
                        && self.prev.data.len() <= KeyHistory::KEY_SIZE * params.trim_size()
                );
                self.prev.add(k, params);
            }
        }
        // After we've potentially added some new keys, see if there's any we
        // want to throw away.
        self.prev.gc(self.ctr, params);

        hax_lib::assume!(self.next.len() > 0);

        Ok(Self::next_key_internal(&mut self.next, &mut self.ctr)
            .1
            .to_vec())
    }

    fn into_pb(self) -> pqrpb::chain::epoch::EpochDirection {
        pqrpb::chain::epoch::EpochDirection {
            ctr: self.ctr,
            next: self.next,
            prev: self.prev.data,
        }
    }

    fn from_pb(pb: pqrpb::chain::epoch::EpochDirection) -> Result<Self, Error> {
        Ok(Self {
            ctr: pb.ctr,
            next: pb.next,
            prev: KeyHistory { data: pb.prev },
        })
    }

    fn clear_next(&mut self) {
        self.next.clear();
    }
}

#[hax_lib::attributes]
impl Chain {
    #[hax_lib::requires(genr8r.len() == 96)]
    fn ced_for_direction(genr8r: &[u8], dir: &Direction) -> ChainEpochDirection {
        ChainEpochDirection::new(match dir {
            Direction::A2B => &genr8r[32..64],
            Direction::B2A => &genr8r[64..96],
        })
    }

    pub fn new(initial_key: &[u8], dir: Direction, params: ChainParamsPB) -> Result<Self, Error> {
        let mut genr8r = [0u8; 96];
        kdf::hkdf_to_slice(
            &[0u8; 32],
            initial_key,
            b"Signal PQ Ratchet V1 Chain  Start",
            &mut genr8r,
        );
        Ok(Self {
            dir,
            current_epoch: 0,
            send_epoch: 0,
            links: VecDeque::from([ChainEpoch {
                send: Self::ced_for_direction(&genr8r, &dir),
                recv: Self::ced_for_direction(&genr8r, &dir.switch()),
            }]),
            next_root: genr8r[0..32].to_vec(),
            params,
        })
    }

    pub fn add_epoch(&mut self, epoch_secret: EpochSecret) {
        // This assume could be turned into a precondition but it uses private fields
        hax_lib::assume!(
            self.current_epoch < u64::MAX && epoch_secret.epoch == self.current_epoch + 1
        );
        assert!(epoch_secret.epoch == self.current_epoch + 1);
        let mut genr8r = [0u8; 96];
        kdf::hkdf_to_slice(
            &self.next_root,
            &epoch_secret.secret,
            b"Signal PQ Ratchet V1 Chain Add Epoch",
            &mut genr8r,
        );
        self.current_epoch = epoch_secret.epoch;
        self.next_root = genr8r[0..32].to_vec();
        self.links.push_back(ChainEpoch {
            send: Self::ced_for_direction(&genr8r, &self.dir),
            recv: Self::ced_for_direction(&genr8r, &self.dir.switch()),
        });
    }

    #[hax_lib::ensures(|res| if let Ok(v) = res {v < self.links.len()} else {true})]
    fn epoch_idx(&mut self, epoch: Epoch) -> Result<usize, Error> {
        if epoch > self.current_epoch {
            return Err(Error::EpochOutOfRange(epoch));
        }
        let back = (self.current_epoch - epoch) as usize;
        let links = self.links.len();
        if back >= links {
            return Err(Error::EpochOutOfRange(epoch));
        }
        Ok(links - 1 - back)
    }

    pub fn send_key(&mut self, epoch: Epoch) -> Result<(u32, Vec<u8>), Error> {
        if epoch < self.send_epoch {
            return Err(Error::SendKeyEpochDecreased(self.send_epoch, epoch));
        }
        let mut epoch_index = self.epoch_idx(epoch)?;
        if self.send_epoch != epoch {
            self.send_epoch = epoch;
            while epoch_index > EPOCHS_TO_KEEP_PRIOR_TO_SEND_EPOCH {
                hax_lib::loop_decreases!(epoch_index);
                self.links.pop_front();
                epoch_index -= 1;
            }
            for i in 0..epoch_index {
                hax_lib::assume!(i < self.links.len());
                self.links[i].send.clear_next();
            }
        }
        hax_lib::assume!(
            epoch_index < self.links.len()
                && self.links[epoch_index].send.next.len() > 0
                && self.links[epoch_index].send.ctr < u32::MAX
        );
        Ok(self.links[epoch_index].send.next_key())
    }

    pub fn recv_key(&mut self, epoch: Epoch, index: u32) -> Result<Vec<u8>, Error> {
        let epoch_index = self.epoch_idx(epoch)?;
        self.links[epoch_index].recv.key(index, &self.params)
    }

    #[hax_lib::opaque] // into_iter and map
    pub(crate) fn into_pb(self) -> pqrpb::Chain {
        pqrpb::Chain {
            direction: self.dir.into(),
            current_epoch: self.current_epoch,
            send_epoch: self.send_epoch,
            links: self
                .links
                .into_iter()
                .map(|link| pqrpb::chain::Epoch {
                    send: Some(link.send.into_pb()),
                    recv: Some(link.recv.into_pb()),
                })
                .collect::<Vec<_>>(),
            next_root: self.next_root,
            params: Some(self.params),
        }
    }

    #[hax_lib::opaque] // into_iter and map
    pub(crate) fn from_pb(pb: pqrpb::Chain) -> Result<Self, Error> {
        Ok(Self {
            dir: pb.direction.try_into().map_err(|_| Error::StateDecode)?,
            current_epoch: pb.current_epoch,
            send_epoch: pb.send_epoch,
            next_root: pb.next_root,
            links: pb
                .links
                .into_iter()
                .map(|link| {
                    Ok::<ChainEpoch, Error>(ChainEpoch {
                        send: ChainEpochDirection::from_pb(link.send.ok_or(Error::StateDecode)?)?,
                        recv: ChainEpochDirection::from_pb(link.recv.ok_or(Error::StateDecode)?)?,
                    })
                })
                .collect::<Result<VecDeque<_>, _>>()?,
            params: pb.params.ok_or(Error::StateDecode)?,
        })
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::{Direction, EpochSecret, Error};
    use proptest::prelude::*;
    use rand::TryRngCore;
    use rand::seq::SliceRandom;

    /// TEMPORARY PROBE (§16 review): can message-controlled `index` alone push the
    /// persisted `recv.ctr` past `h_ctr_bound` (u32::MAX - 390451572) with no blob mutation?
    /// ~156K recv_key calls × 25_000 HKDFs ≈ 4·10^9 HKDFs: ~25 min in release, hours in
    /// debug. Run explicitly: `cargo test --release --lib q16_probe -- --ignored --nocapture`.
    #[test]
    #[ignore]
    fn q16_probe_remote_index_drives_ctr_past_bound() {
        let bound = u32::MAX - 390_451_572;
        let mut c = Chain::new(b"1", Direction::B2A, ChainParams::default().into_pb()).unwrap();
        let max_jump = DEFAULT_CHAIN_PARAMS.max_jump; // 25_000 per call
        // Phase 1: honest-looking, in-range jumps. Each recv_key(0, ctr+max_jump) is Ok
        // (max_jump > max_ooo so prev is cleared each time; the KDF loop is the cost).
        let mut ctr: u32 = 0;
        let mut calls = 0u64;
        while ctr < bound + 1 {
            let at = ctr.saturating_add(max_jump);
            c.recv_key(0, at).expect("in-range jump must be Ok");
            ctr = at;
            calls += 1;
        }
        eprintln!("reached ctr={ctr} (> bound {bound}) after {calls} recv_key calls");
        // Phase 2: persist and reload — this is what the host would store.
        let pb = c.into_pb();
        let persisted_ctr = pb.links[0].recv.as_ref().unwrap().ctr;
        assert!(persisted_ctr > bound, "persisted ctr {persisted_ctr} exceeds h_ctr_bound");
        let mut c2 = Chain::from_pb(pb).expect("from_pb accepts it");
        // Phase 3: one more message. index = ctr + 1 is a perfectly ordinary in-order
        // message, yet the addition at L265 overflows in debug builds.
        // CORRECTION (§16.9): `h_ctr_bound` is a *proof-side slack* bound, not the runtime
        // overflow threshold. L265 computes `ctr + max_ooo_keys` (2_000 by default), which
        // overflows only when ctr > u32::MAX - 2_000. At ctr ≈ bound + max_jump the addition
        // fits, so this call returns Ok in BOTH profiles. The state is Lean-invalid
        // (recvKeyPre unsatisfiable) but runtime-benign. See q16b_* for the real thresholds.
        let next_index = persisted_ctr + 1;
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            c2.recv_key(0, next_index)
        }));
        let inner = result.expect("no overflow yet: ctr + max_ooo fits in u32");
        assert!(inner.is_ok(), "in-order key after Lean bound is still Ok");
        eprintln!("Phase 3: recv_key Ok in both profiles; Lean I4 violated, no runtime fault yet");
    }

    // ---------------------------------------------------------------------------------
    // §16.9 probes. Each seeds the *exact state* a malicious authenticated peer would
    // reach by steering `ctr` (only `ctr`/`prev`/`next` matter to `key()`, and `prev` is
    // empty after any jump > max_ooo), so the 4·10^9-HKDF steering loop is not needed.
    // Run: cargo test --lib q16b_ -- --nocapture --test-threads=1   (and --release)
    // ---------------------------------------------------------------------------------

    const LEAN_CTR_BOUND: u32 = u32::MAX - 390_451_572;

    fn chain_with_recv_ctr(ctr: u32, params: pqrpb::ChainParams) -> Chain {
        let c = Chain::new(b"1", Direction::B2A, params).unwrap();
        let mut pb = c.into_pb();
        pb.links[0].recv.as_mut().unwrap().ctr = ctr;
        pb.links[0].recv.as_mut().unwrap().prev = vec![];
        Chain::from_pb(pb).expect("from_pb accepts any ctr")
    }

    fn chain_with_recv_ctr_and_stored(ctr: u32, stored: u32, params: pqrpb::ChainParams) -> Chain {
        let c = Chain::new(b"1", Direction::B2A, params).unwrap();
        let mut pb = c.into_pb();
        let d = pb.links[0].recv.as_mut().unwrap();
        d.ctr = ctr;
        d.prev = stored.to_be_bytes().to_vec();
        d.prev.extend_from_slice(&[7u8; 32]);
        Chain::from_pb(pb).expect("from_pb accepts any ctr")
    }

    fn recv_prev_len(c: Chain) -> usize {
        c.into_pb().links[0].recv.as_ref().unwrap().prev.len()
    }

    /// S1: the Lean bound is not the runtime threshold. Any ctr in
    /// (LEAN_CTR_BOUND, u32::MAX - max_ooo] is Lean-invalid but every in-order and
    /// max_jump key request is Ok in both profiles.
    #[test]
    fn q16b_probe_lean_bound_is_not_runtime_threshold() {
        let params = ChainParams::default().into_pb();
        for ctr in [LEAN_CTR_BOUND + 1, LEAN_CTR_BOUND + 25_000, u32::MAX - 2_000 - 25_001] {
            let mut c = chain_with_recv_ctr(ctr, params);
            c.recv_key(0, ctr + 1).expect("in-order Ok");
            c.recv_key(0, ctr + 1 + 25_000).expect("max_jump Ok");
        }
        // Exact threshold: ctr = u32::MAX - max_ooo is the last ctr for which L265 fits.
        let mut c = chain_with_recv_ctr(u32::MAX - 2_000, params);
        c.recv_key(0, u32::MAX - 1_999).expect("ctr + max_ooo == u32::MAX still fits");
        eprintln!("S1: ctr in (Lean bound, u32::MAX - max_ooo] → all Ok in both profiles");
    }

    /// S2: L265 overflow. First ctr for which `ctr + max_ooo` overflows is
    /// u32::MAX - max_ooo + 1. Debug: panic. Release: wrap → `at > tiny` is true →
    /// spurious `prev.clear()` — every stored OOO key of the epoch is discarded.
    #[test]
    fn q16b_probe_l265_threshold_and_spurious_clear() {
        let params = ChainParams::default().into_pb();
        let ctr = u32::MAX - 1_999;
        let mut c = chain_with_recv_ctr_and_stored(ctr, ctr - 1, params);
        let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| c.recv_key(0, ctr + 1)));
        if cfg!(debug_assertions) {
            assert!(r.is_err(), "debug: attempt to add with overflow at L265");
            eprintln!("S2 debug: panic at L265 for ctr = u32::MAX - max_ooo + 1");
        } else {
            r.unwrap().expect("release: Ok");
            // Honest semantics: at = ctr+1 <= ctr+max_ooo, prev must be untouched (36 B).
            assert_eq!(recv_prev_len(c), 0, "release: wrap took the prev.clear() arm");
            eprintln!("S2 release: Ok, but prev.clear() fired spuriously (36 → 0 bytes)");
        }
    }

    /// S3: L279 overflow *inside* the KDF loop, reached during steering itself (no
    /// reload needed). ctr = u32::MAX - 3000, index = u32::MAX - 1000 (jump 2000 ≤ max_jump).
    /// Honest semantics: store 1999 skipped keys (u32::MAX-2999 .. u32::MAX-1001).
    /// Debug: panic when ctr reaches u32::MAX - 1999. Release: keys with
    /// ctr > u32::MAX - 2000 are silently NOT stored → 1000 stored, 999 lost.
    #[test]
    fn q16b_probe_l279_midloop_overflow_drops_keys() {
        let params = ChainParams::default().into_pb();
        let ctr = u32::MAX - 3_000;
        let at = u32::MAX - 1_000;
        let mut c = chain_with_recv_ctr(ctr, params);
        let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| c.recv_key(0, at)));
        if cfg!(debug_assertions) {
            assert!(r.is_err(), "debug: overflow at L279");
            eprintln!("S3 debug: panic at L279 mid-loop (remote-triggerable while steering)");
        } else {
            r.unwrap().expect("release Ok");
            // Keys stored: indices ctr+1 ..= u32::MAX-2000  → 1000 records.
            let stored = recv_prev_len(c) / 36;
            assert_eq!(stored, 1_000, "release: wrap drops keys > u32::MAX - max_ooo");
            eprintln!("S3 release: Ok, stored {stored}/1999 skipped keys — 999 silently lost");
        }
    }

    /// S4: I12 (`index + max_ooo` at L192) is remotely reachable once ctr is steered
    /// high. index = u32::MAX - 1500 < ctr = u32::MAX - 1000, key legitimately stored.
    /// Debug: panic at L192. Release: wrap → `tiny < ctr` → Err(KeyTrimmed) for a key
    /// that IS in prev — message undecryptable.
    #[test]
    fn q16b_probe_l192_get_overflow_misreports_trimmed() {
        let params = ChainParams::default().into_pb();
        let ctr = u32::MAX - 1_000;
        let want = u32::MAX - 1_500;
        let mut c = chain_with_recv_ctr_and_stored(ctr, want, params);
        let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| c.recv_key(0, want)));
        if cfg!(debug_assertions) {
            assert!(r.is_err(), "debug: overflow at L192");
            eprintln!("S4 debug: panic at L192 (get) on OOO index near u32::MAX");
        } else {
            let res = r.unwrap();
            assert!(matches!(res, Err(Error::KeyTrimmed(x)) if x == want));
            eprintln!("S4 release: Err(KeyTrimmed) although the key is present in prev");
        }
    }

    /// S5: counter exhaustion is a per-direction hard stop. Once ctr == u32::MAX no
    /// index is > ctr, so the recv direction of this epoch returns only
    /// KeyAlreadyRequested / KeyTrimmed forever (until an epoch advance).
    #[test]
    fn q16b_probe_counter_exhaustion_hard_stop() {
        let params = ChainParams::default().into_pb();
        // Reaching u32::MAX itself needs the L265 wrap (release) — seed post-wrap state.
        let mut c = chain_with_recv_ctr(u32::MAX, params);
        assert!(matches!(c.recv_key(0, u32::MAX), Err(Error::KeyAlreadyRequested(_))));
        let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| c.recv_key(0, 5)));
        // at=5 < ctr → get(); `5 + 2000 < u32::MAX` fits → KeyTrimmed in both profiles.
        assert!(matches!(r.unwrap(), Err(Error::KeyTrimmed(5))));
        // recv_key can never call next_key_internal here (needs at > ctr), so the
        // `*ctr += 1` at L230 is unreachable through recv — no panic, permanent Err.
        eprintln!("S5: ctr == u32::MAX → recv direction permanently Err (self-DoS only)");
    }

    /// S6: remote CPU amplification. One message with index = ctr + max_jump costs the
    /// victim max_jump HKDF invocations. Err(KeyJump) for index > ctr + max_jump costs
    /// nothing and leaves the state byte-identical.
    #[test]
    fn q16b_probe_key_jump_cpu_cost_and_err_is_pure() {
        let params = ChainParams::default().into_pb();
        let mut c = Chain::new(b"1", Direction::B2A, params).unwrap();
        let t = std::time::Instant::now();
        c.recv_key(0, 25_000).expect("max_jump Ok");
        let dt = t.elapsed();
        eprintln!("S6: one max_jump message = 25_000 HKDFs in {dt:?}");
        let before = c.into_pb();
        let mut c = Chain::from_pb(before.clone()).unwrap();
        assert!(matches!(c.recv_key(0, 25_000 + 25_001), Err(Error::KeyJump(25_000, 50_001))));
        assert_eq!(c.into_pb(), before, "KeyJump path does not mutate state");
        // prev is bounded by trim_size regardless of how many keys are skipped.
        let mut c = Chain::from_pb(before).unwrap();
        for i in 1..=60u32 {
            c.recv_key(0, 25_000 + i * 1_999).unwrap();
        }
        let len = recv_prev_len(c);
        assert!(len <= 36 * 2_201, "prev bounded by GC: {len}");
        eprintln!("S6: after 60 near-max_ooo jumps prev.len() = {len} ≤ {}", 36 * 2_201);
    }

    /// S7: non-default params shrink the steering cost. With max_ooo_keys large the
    /// overflow threshold u32::MAX - max_ooo drops; with max_jump large one message
    /// suffices. Here max_ooo = 2^31: threshold ctr > 2^31 - 1 (~2048 messages of 2^20).
    #[test]
    fn q16b_probe_nondefault_params_lower_threshold() {
        let params = pqrpb::ChainParams {
            max_jump: 1 << 20,
            max_ooo_keys: 1 << 31,
        };
        let ctr = (1u32 << 31) - 1;
        let mut c = chain_with_recv_ctr(ctr, params);
        c.recv_key(0, ctr + 1).expect("ctr + max_ooo == u32::MAX fits");
        let mut c = chain_with_recv_ctr(ctr + 1, params);
        let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| c.recv_key(0, ctr + 2)));
        if cfg!(debug_assertions) {
            assert!(r.is_err(), "debug: L265 overflow at ctr = 2^31");
            eprintln!("S7 debug: max_ooo = 2^31 → L265 overflow already at ctr = 2^31");
        } else {
            r.unwrap().expect("release Ok (wrap)");
            eprintln!("S7 release: silent wrap at ctr = 2^31");
        }
    }

    /// S8: KDF-derived invariants I1–I3 are preserved by every Ok `key()` call, so a
    /// remote peer cannot steer them. Random walk of in-range indices, then check.
    #[test]
    fn q16b_probe_steering_preserves_i1_i2_i3() {
        let params = pqrpb::ChainParams {
            max_jump: 50,
            max_ooo_keys: 10,
        };
        let mut c = Chain::new(b"1", Direction::B2A, params).unwrap();
        let mut ctr = 0u32;
        let mut seed = 0x9E37_79B9u32;
        let mut stored: Vec<u32> = vec![];
        for _ in 0..2_000 {
            seed ^= seed << 13;
            seed ^= seed >> 17;
            seed ^= seed << 5;
            if seed % 4 == 0 && !stored.is_empty() {
                let k = stored.swap_remove((seed as usize / 4) % stored.len());
                let _ = c.recv_key(0, k); // Ok or KeyTrimmed, both fine
            } else {
                let jump = 1 + seed % 50;
                for a in ctr + 1..ctr + jump {
                    stored.push(a);
                }
                ctr += jump;
                c.recv_key(0, ctr).unwrap();
            }
        }
        let pb = c.into_pb();
        let d = pb.links[0].recv.as_ref().unwrap();
        assert_eq!(d.next.len(), 32, "I1");
        assert_eq!(d.prev.len() % 36, 0, "I2");
        assert!(d.prev.len() <= 36 * d.ctr as usize, "I3");
        assert!(d.prev.len() <= 36 * 12, "GC bound (trim_size = 12)");
        eprintln!("S8: after 2000 steered calls ctr={} prev={} B — I1–I3 hold", d.ctr, d.prev.len());
    }

    // --- D18 probes: Chain::from_pb admits corrupted next_root/links/epoch ---

    /// D18-1: `from_pb` accepts `next_root` with length ≠ 32 (e.g. 16 bytes).
    /// The corrupted next_root survives round-trip and will cause silent key divergence
    /// when used as HKDF salt in `add_epoch`.
    #[test]
    fn d18_from_pb_admits_wrong_next_root_length() {
        let mut pb = Chain::new(b"1", Direction::A2B, ChainParams::default().into_pb()).unwrap().into_pb();
        pb.next_root = vec![0u8; 16]; // should be 32
        let c = Chain::from_pb(pb.clone())
            .expect("from_pb should reject but accepts bad next_root");
        assert_eq!(c.next_root.len(), 16, "corrupted next_root survives from_pb");
        let pb2 = c.into_pb();
        assert_eq!(pb, pb2, "corruption round-trips through into_pb");
        eprintln!("D18-1: from_pb accepts next_root.len()=16 (should require 32)");
    }

    /// D18-2: `from_pb` accepts empty `links` (no epochs).
    /// Empty links means every `send_key` and `recv_key` returns `EpochOutOfRange` —
    /// the chain is permanently unusable for any epoch.
    #[test]
    fn d18_from_pb_admits_empty_links() {
        let mut pb = Chain::new(b"1", Direction::A2B, ChainParams::default().into_pb()).unwrap().into_pb();
        pb.links.clear(); // empty
        let mut c = Chain::from_pb(pb).expect("from_pb should reject but accepts empty links");
        assert_eq!(c.links.len(), 0, "empty links survives from_pb");
        // Every send_key and recv_key fails — the chain is permanently stuck.
        assert!(matches!(c.send_key(0), Err(Error::EpochOutOfRange(0))),
            "send_key(0) fails on empty links");
        assert!(matches!(c.recv_key(0, 1), Err(Error::EpochOutOfRange(0))),
            "recv_key(0,1) fails on empty links");
        // Round-trip preserves the corruption.
        let pb2 = c.into_pb();
        assert!(pb2.links.is_empty(), "empty links round-trips");
        eprintln!("D18-2: from_pb accepts links=[] → chain permanently stuck (all ops fail)");
    }

    /// D18-3: `from_pb` accepts `send_epoch > current_epoch`.
    /// This makes every `send_key` fail because epoch_idx underflows, permanently
    /// stalling the chain.
    #[test]
    fn d18_from_pb_admits_epoch_inversion() {
        let mut pb = Chain::new(b"1", Direction::A2B, ChainParams::default().into_pb()).unwrap().into_pb();
        pb.send_epoch = 7; // current_epoch is 0
        let mut c = Chain::from_pb(pb)
            .expect("from_pb should reject but accepts send_epoch > current_epoch");
        assert!(c.send_epoch > c.current_epoch, "epoch inversion survives from_pb");
        // send_key fails for the inverted epoch (7 > current 0).
        let r = c.send_key(7);
        assert!(r.is_err(), "send_key fails with inverted epoch: {:?}", r);
        // send_key also fails for epoch 0 because send_epoch has been set to 7.
        let r2 = c.send_key(0);
        assert!(r2.is_err(), "send_key(0) also fails: {:?}", r2);
        eprintln!("D18-3: from_pb accepts send_epoch(7) > current_epoch(0) → chain stuck");
    }

    // --- END D18 probes ---

    #[test]
    fn directions_match() {
        let mut a2b = Chain::new(b"1", Direction::A2B, ChainParams::default().into_pb()).unwrap();
        let mut b2a = Chain::new(b"1", Direction::B2A, ChainParams::default().into_pb()).unwrap();
        let sk1 = a2b.send_key(0).unwrap();
        assert_eq!(sk1.0, 1);
        assert_eq!(sk1.1, b2a.recv_key(0, 1).unwrap());
        a2b.add_epoch(EpochSecret {
            epoch: 1,
            secret: vec![2],
        });
        b2a.add_epoch(EpochSecret {
            epoch: 1,
            secret: vec![2],
        });
        let sk2 = a2b.send_key(1).unwrap();
        assert_eq!(sk2.0, 1);
        assert_eq!(sk2.1, b2a.recv_key(1, 1).unwrap());
        for _i in 2..10 {
            a2b.send_key(1).unwrap();
        }
        let sk3 = a2b.send_key(1).unwrap();
        assert_eq!(sk3.0, 10);
        assert_eq!(sk3.1, b2a.recv_key(1, 10).unwrap());
    }

    #[test]
    fn previously_returned_key() {
        let mut a2b = Chain::new(b"1", Direction::A2B, ChainParams::default().into_pb()).unwrap();
        a2b.recv_key(0, 2).expect("should get key first time");
        assert!(matches!(
            a2b.recv_key(0, 2),
            Err(Error::KeyAlreadyRequested(2))
        ));
    }

    #[test]
    fn very_old_keys_are_trimmed() {
        let params = ChainParams {
            max_jump: 10,
            max_ooo_keys: 10,
        }
        .into_pb();
        let mut a2b = Chain::new(b"1", Direction::A2B, params).unwrap();
        a2b.recv_key(0, 10).expect("should allow this jump");
        a2b.recv_key(0, 12).expect("should allow progression");
        assert!(matches!(a2b.recv_key(0, 1), Err(Error::KeyTrimmed(1))));
    }

    #[test]
    fn out_of_order_keys() {
        let max_ooo = DEFAULT_CHAIN_PARAMS.max_ooo_keys;
        let mut a2b = Chain::new(b"1", Direction::A2B, ChainParams::default().into_pb()).unwrap();
        let mut b2a = Chain::new(b"1", Direction::B2A, ChainParams::default().into_pb()).unwrap();
        let mut keys = Vec::with_capacity(max_ooo as usize);
        for _i in 0..(max_ooo as usize) {
            keys.push(a2b.send_key(0).unwrap());
        }
        let mut rng = rand::rngs::OsRng.unwrap_err();
        keys.shuffle(&mut rng);
        for (idx, key) in keys {
            assert_eq!(b2a.recv_key(0, idx).unwrap(), key);
        }
    }

    #[test]
    fn clear_old_send_keys() {
        let mut a2b = Chain::new(b"1", Direction::A2B, ChainParams::default().into_pb()).unwrap();
        a2b.send_key(0).unwrap();
        a2b.send_key(0).unwrap();
        a2b.add_epoch(EpochSecret {
            epoch: 1,
            secret: vec![2],
        });
        a2b.send_key(1).unwrap();
        assert!(matches!(
            a2b.send_key(0).unwrap_err(),
            Error::SendKeyEpochDecreased(1, 0)
        ));
    }

    #[derive(Clone, Debug)]
    enum KeyHistoryAction {
        AddNewNext,
        AddNewSkip,
        RequestStored(usize),
        RequestNotStored(usize),
        GarbageCollect,
    }

    impl KeyHistoryAction {
        fn strategy() -> impl Strategy<Value = Self> {
            proptest::prop_oneof![
                Just(Self::AddNewNext),
                Just(Self::AddNewSkip),
                any::<usize>().prop_map(Self::RequestStored),
                any::<usize>().prop_map(Self::RequestNotStored),
                Just(Self::GarbageCollect),
            ]
        }
    }

    #[test]
    fn key_history_prop_test() {
        let _ = env_logger::builder().is_test(true).try_init();
        proptest!(|(actions in proptest::collection::vec(KeyHistoryAction::strategy(), ..25))| {
            let mut kh = KeyHistory::new();
            let mut stored = vec![];
            let mut not_stored = vec![];
            let mut ctr = 0u32;
            let params = pqrpb::ChainParams {
                max_ooo_keys: 3u32,
                max_jump: 5u32,
            };
            log::debug!("========= STARTING =========");
            for action in actions {
                match action {
                    KeyHistoryAction::AddNewNext => {
                        log::debug!("adding {}", ctr);
                        kh.add((ctr, [1u8; 32]), &params);
                        stored.push(ctr);
                        ctr += 1;
                    }
                    KeyHistoryAction::AddNewSkip => {
                        log::debug!("skipping {}", ctr);
                        not_stored.push(ctr);
                        ctr += 1;
                    }
                    KeyHistoryAction::RequestStored(i) => {
                        if !stored.is_empty() {
                            let k = stored.swap_remove(i % stored.len());
                            log::debug!("requesting stored {}", k);
                            kh.get(k, ctr, &params).unwrap();
                            not_stored.push(k);
                        }
                    }
                    KeyHistoryAction::RequestNotStored(i) => {
                        if !not_stored.is_empty() {
                            let k = not_stored.swap_remove(i % not_stored.len());
                            log::debug!("requesting not stored {}", k);
                            kh.get(k, ctr, &params).unwrap_err();
                        }
                    }
                    KeyHistoryAction::GarbageCollect => {
                        log::debug!("gc at {}", ctr);
                        kh.gc(ctr, &params);
                    }
                }
                let (fell_off, stored_new): (Vec<_>, _) = stored.into_iter().partition(
                    |n| n + params.max_ooo_keys < ctr);
                stored = stored_new;
                if !fell_off.is_empty() {
                    log::debug!("fell off: {:?}", fell_off);
                }
                not_stored.extend(fell_off.into_iter());
            }
        });
    }

    #[derive(Clone, Debug)]
    enum CEDAction {
        NextKey,
        NextKeyAt(u32),
        RequestStored(usize),
        RequestNotStored(usize),
        TooHigh,
    }

    impl CEDAction {
        fn strategy() -> impl Strategy<Value = Self> {
            proptest::prop_oneof![
                Just(Self::NextKey),
                any::<u32>().prop_map(Self::NextKeyAt),
                any::<usize>().prop_map(Self::RequestStored),
                any::<usize>().prop_map(Self::RequestNotStored),
                Just(Self::TooHigh),
            ]
        }
    }

    #[test]
    fn ced_prop_test() {
        let _ = env_logger::builder().is_test(true).try_init();
        proptest!(|(actions in proptest::collection::vec(CEDAction::strategy(), ..25))| {
            let mut ced = ChainEpochDirection::new(&[1u8; 32]);
            let mut stored = vec![];
            let mut not_stored = vec![0];
            let mut ctr = 0u32;
            let params = pqrpb::ChainParams {
                max_ooo_keys: 3u32,
                max_jump: 5u32,
            };
            log::debug!("========= STARTING =========");
            for action in actions {
                match action {
                    CEDAction::NextKey => {
                        ctr += 1;
                        log::debug!("next_key {}", ctr);
                        let k = ced.next_key().0;
                        not_stored.push(k);
                    }
                    CEDAction::NextKeyAt(i) => {
                        let jump = i % params.max_jump;
                        ctr += 1;
                        for at in ctr..ctr+jump {
                            stored.push(at);
                        }
                        ctr += jump;
                        log::debug!("next_key_at {}", ctr);
                        ced.key(ctr, &params).unwrap();
                        not_stored.push(ctr);
                    }
                    CEDAction::RequestStored(i) => {
                        if !stored.is_empty() {
                            let k = stored.swap_remove(i % stored.len());
                            log::debug!("requesting stored {}", k);
                            ced.key(k, &params).unwrap();
                            not_stored.push(k);
                        }
                    }
                    CEDAction::RequestNotStored(i) => {
                        if !not_stored.is_empty() {
                            let k = not_stored.swap_remove(i % not_stored.len());
                            log::debug!("requesting not stored {}", k);
                            ced.key(k, &params).unwrap_err();
                        }
                    }
                    CEDAction::TooHigh => {
                        let high = ctr + params.max_jump + 1;
                        log::debug!("too high {}", high);
                        ced.key(high, &params).unwrap_err();
                    }
                }
                let (fell_off, stored_new): (Vec<_>, _) = stored.into_iter().partition(
                    |n| n + params.max_ooo_keys < ctr);
                stored = stored_new;
                if !fell_off.is_empty() {
                    log::debug!("fell off: {:?}", fell_off);
                }
                not_stored.extend(fell_off.into_iter());
            }
        });
    }
}
