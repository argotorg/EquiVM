import Benchmarks.Dss.Cat.BiteConnect
import Benchmarks.Dss.Cat.BiteBodyMem

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

namespace Benchmarks.Dss.Cat

/-! # Cat `bite` — concrete-memory grab/fess/kick reach path (`catBiteBody` support)

The frozen `catBiteReach{Grab,Fess}Region` wrappers abstract their post-call memory (`∃ mem'`), so a
carried memory word (the `milk.chop` field re-read at pc 2349, `catBiteReach2300to2383`'s `hChop`)
cannot be threaded through them.  This file builds the *concrete*-memory grab/fess reach (the void
`CALL`s have `outSize = 0`, so `RD.call`'s return copy is a no-op and the pre-call calldata memory
survives verbatim) plus the "read below the free pointer `p`" seams that recover `milk.chop` from the
`grab`/`fess` calldata overlay (`chop@(q+32) = 256 < p = q+96 = 320`). -/

/-! ## Read-below-`p` seams: `grab`/`fess` calldata writes at `[p, …)` preserve reads at `off + 32 ≤ p` -/

/-- The 7 `grab` calldata writes (at `p, p+4, …, p+164`) leave any word strictly below `p` unchanged
(generic-offset clone of `catBiteGrabCalldataMemP_read64`). -/
theorem catBiteGrabCalldataMemP_readBelow (p ilk urn thisW vowRaw dink dart : UInt256)
    {mem : ByteArray} (off : ℕ) (hoff : off + 32 ≤ p.toNat) (hpmem : p.toNat ≤ mem.size)
    (hpsz : p.toNat + 196 < UInt256.size) :
    (catBiteGrabCalldataMemP p ilk urn thisW vowRaw dink dart mem).readWithPadding off 32
      = mem.readWithPadding off 32 := by
  have e4 : (p + ⟨4⟩).toNat = p.toNat + 4 := by
    rw [uadd_toNat, show (⟨4⟩ : UInt256).toNat = 4 from by decide, Nat.mod_eq_of_lt (by omega)]
  have e36 : (p + ⟨36⟩).toNat = p.toNat + 36 := by
    rw [uadd_toNat, show (⟨36⟩ : UInt256).toNat = 36 from by decide, Nat.mod_eq_of_lt (by omega)]
  have e68 : (p + ⟨68⟩).toNat = p.toNat + 68 := by
    rw [uadd_toNat, show (⟨68⟩ : UInt256).toNat = 68 from by decide, Nat.mod_eq_of_lt (by omega)]
  have e100 : (p + ⟨100⟩).toNat = p.toNat + 100 := by
    rw [uadd_toNat, show (⟨100⟩ : UInt256).toNat = 100 from by decide, Nat.mod_eq_of_lt (by omega)]
  have e132 : (p + ⟨132⟩).toNat = p.toNat + 132 := by
    rw [uadd_toNat, show (⟨132⟩ : UInt256).toNat = 132 from by decide, Nat.mod_eq_of_lt (by omega)]
  have e164 : (p + ⟨164⟩).toNat = p.toNat + 164 := by
    rw [uadd_toNat, show (⟨164⟩ : UInt256).toNat = 164 from by decide, Nat.mod_eq_of_lt (by omega)]
  have hsSel := catBiteGrabSelMemP_size p hpmem
  have hsIlk := catBiteGrabIlkMemP_size p ilk hpmem hpsz
  have hsUrn := catBiteGrabUrnMemP_size p ilk urn hpmem hpsz
  have hsThis := catBiteGrabThisMemP_size p ilk urn thisW hpmem hpsz
  have hsVow := catBiteGrabVowMemP_size p ilk urn thisW vowRaw hpmem hpsz
  have hsDink := catBiteGrabDinkMemP_size p ilk urn thisW vowRaw dink hpmem hpsz
  unfold catBiteGrabCalldataMemP
  rw [write32_read_below _ _ (p + ⟨164⟩).toNat off (by rw [toByteArray_size]) (by omega) (by omega)]
  unfold catBiteGrabDinkMemP
  rw [write32_read_below _ _ (p + ⟨132⟩).toNat off (by rw [toByteArray_size]) (by omega) (by omega)]
  unfold catBiteGrabVowMemP
  rw [write32_read_below _ _ (p + ⟨100⟩).toNat off (by rw [toByteArray_size]) (by omega) (by omega)]
  unfold catBiteGrabThisMemP
  rw [write32_read_below _ _ (p + ⟨68⟩).toNat off (by rw [toByteArray_size]) (by omega) (by omega)]
  unfold catBiteGrabUrnMemP
  rw [write32_read_below _ _ (p + ⟨36⟩).toNat off (by rw [toByteArray_size]) (by omega) (by omega)]
  unfold catBiteGrabIlkMemP
  rw [write32_read_below _ _ (p + ⟨4⟩).toNat off (by rw [toByteArray_size]) (by omega) (by omega)]
  unfold catBiteGrabSelMemP
  rw [write32_read_below _ _ p.toNat off (by rw [toByteArray_size]) hpmem (by omega)]

/-- The 2 `fess` calldata writes (at `p2, p2+4`) leave any word strictly below `p2` unchanged
(generic-offset clone of `catBiteFessCalldataMemP_read64`). -/
theorem catBiteFessCalldataMemP_readBelow (p2 dartRate : UInt256) {mem : ByteArray}
    (off : ℕ) (hoff : off + 32 ≤ p2.toNat) (hpmem : p2.toNat ≤ mem.size)
    (hpsz : p2.toNat + 36 < UInt256.size) :
    (catBiteFessCalldataMemP p2 dartRate mem).readWithPadding off 32 = mem.readWithPadding off 32 := by
  have e4 : (⟨4⟩ + p2).toNat = p2.toNat + 4 := by
    rw [uadd_toNat, show (⟨4⟩ : UInt256).toNat = 4 from by decide, Nat.add_comm,
      Nat.mod_eq_of_lt (by omega)]
  have hs := catBiteFessSelMemP_size p2 hpmem
  unfold catBiteFessCalldataMemP
  rw [write32_read_below _ _ (⟨4⟩ + p2).toNat off (by rw [toByteArray_size]) (by omega) (by omega)]
  unfold catBiteFessSelMemP
  rw [write32_read_below _ _ p2.toNat off (by rw [toByteArray_size]) hpmem (by omega)]

end Benchmarks.Dss.Cat
