import Benchmarks.Auction.CopyMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Auction

def returnSelector (out : ByteArray) : UInt256 :=
  if 4 ≤ out.size then UInt256.shiftRight (calldataWord out 0) ⟨224⟩ else ⟨0⟩

noncomputable def errorSelectorMem (mem out : ByteArray) : ByteArray :=
  if 4 ≤ out.size then out.write 0 mem 0 4 else mem

def errorSelectorWords (aw : UInt256) (out : ByteArray) : UInt256 :=
  if 4 ≤ out.size then expandedWords (expandedWords aw ⟨0⟩ ⟨4⟩) ⟨0⟩ ⟨32⟩ else aw

theorem copiedSelector {mem aw out} (hm : 96 ≤ mem.size) (ha : ActiveWords aw)
    (hl : 4 ≤ out.size) :
    UInt256.shiftRight (loadedWord (out.write 0 mem 0 4) aw ⟨0⟩) ⟨224⟩ =
      UInt256.shiftRight (calldataWord out 0) ⟨224⟩ := by
  have hsz : 96 ≤ (out.write 0 mem 0 4).size := by
    rw [copyWindow_size out mem 0 0 4 (by decide) hl (by omega)]
    omega
  rw [loadedWord_zero ha (by omega)]
  apply u256_inj
  rw [selector_toNat _ (by omega), selector_toNat out hl]
  have hx := copyWindow_extract out mem 0 0 4 0 4 (by decide) hl (by omega) (by decide)
  have ht := congrArg (fun b : ByteArray ↦ b.data.toList) hx
  simpa only [ByteArray.data_extract, Array.toList_extract, List.extract_eq_take_drop,
    List.drop_zero] using congrArg fromBytesBigEndian ht

theorem errorSelectorHeap {mem aw ptr} (hm : HeapMemory mem aw ptr) (out : ByteArray) :
    HeapMemory (errorSelectorMem mem out) (errorSelectorWords aw out) ptr := by
  unfold errorSelectorMem errorSelectorWords
  split
  · rename_i hl
    have hsz : (out.write 0 mem 0 4).size = mem.size := by
      rw [copyWindow_size out mem 0 0 4 (by decide) hl (by omega)]
      have hs := hm.size
      omega
    refine ⟨by rw [hsz]; exact hm.size, ?_, hm.lower, by rw [hsz]; exact hm.gap, ?_⟩
    · rw [copyWindow_read_preserved out mem 0 0 4 64 (by decide) hl (by omega)
        hm.size (Or.inr (by decide)), hm.free]
    · exact activeWords_expand32 (activeWords_expand hm.active (by decide)) (by decide)
  · exact hm

theorem errorSelectorPrefix {mem aw ptr} (_hm : HeapMemory mem aw ptr) (out : ByteArray) :
    MemoryPrefix mem (errorSelectorMem mem out) ptr.toNat := by
  unfold errorSelectorMem
  split
  · rename_i hl
    exact copyWindow_prefix out mem 0 0 4 ptr.toNat (by decide) hl (by omega)
      (Or.inr (by decide))
  · exact MemoryPrefix.refl _ _

theorem returnSelector_match (out : ByteArray) :
    returnSelector out = ⟨0x08c379a0⟩ ↔ out.extract 0 4 = errorStringSelector := by
  by_cases hl : 4 ≤ out.size
  · rw [returnSelector, if_pos hl]
    have hd := evmSelectorDecode hl 0x08 0xc3 0x79 0xa0 ⟨0x08c379a0⟩ (by native_decide)
    change UInt256.eq ⟨0x08c379a0⟩ (UInt256.shiftRight (calldataWord out 0) ⟨224⟩) =
      (if errorStringSelector == out.extract 0 4 then ⟨1⟩ else ⟨0⟩) at hd
    by_cases he : out.extract 0 4 = errorStringSelector
    · have hb : (errorStringSelector == out.extract 0 4) = true := by
        change (errorStringSelector.data == (out.extract 0 4).data) = true
        exact beq_iff_eq.mpr (congrArg ByteArray.data he.symm)
      rw [if_pos hb] at hd
      exact ⟨fun _ ↦ he, fun _ ↦ (uInt256_eq_one_eq hd).symm⟩
    · have hb : ¬ (errorStringSelector == out.extract 0 4) = true := by
        intro hbe
        change (errorStringSelector.data == (out.extract 0 4).data) = true at hbe
        exact he (ByteArray.ext (beq_iff_eq.mp hbe)).symm
      rw [if_neg hb] at hd
      constructor
      · intro hw
        rw [hw, u256_eq_refl] at hd
        exact False.elim ((by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩) hd)
      · exact fun hf ↦ False.elim (he hf)
  · rw [returnSelector, if_neg hl]
    constructor
    · intro hf
      exact False.elim ((by decide : (⟨0⟩ : UInt256) ≠ ⟨0x08c379a0⟩) hf)
    · intro hf
      have hsz := congrArg ByteArray.size hf
      rw [ByteArray.size_extract] at hsz
      change min 4 out.size - 0 = 4 at hsz
      omega

end Auction
