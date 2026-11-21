import Benchmarks.Midnight.SafeTransferPost
import Benchmarks.Midnight.SafeTransferSourceTail

/-! Agreement between the transfer return-data predicate and the bytecode decoder. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

theorem safeTransferDecodeDifference (ptr size : UInt256) :
    UInt256.sub ((ptr + size) + UInt256.ofNat 32) (ptr + UInt256.ofNat 32) = size := by
  rw [uadd_assoc, u256_add_comm size, ← uadd_assoc, word_add_sub_left]

theorem safeTransferPostResultCharge (isFrom : Bool) {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem out : ByteArray} {aw ptr ret : UInt256} {σ : AccountMap} {k C : Nat}
    {R : List UInt256} (hstack : R.length + 7 ≤ 1024) (hb : out.size < 2 ^ 64)
    (hsize : memLoad ptr mem = UInt256.ofNat out.size)
    (hword : 32 ≤ out.size → memLoad (ptr + UInt256.ofNat 32) mem = calldataWord out 0)
    (hret : (D_J midnightBytecode 0).contains ret = true)
    (rd : RD midnightBytecode I g s0 (safeTransferLengthPC isFrom)
      (ptr :: ret :: R) mem aw out σ k C) :
    ((out.size = 0 ∨ config.externalABI.decodeValue? abiBool out = some (.bool true)) ∧
      ∃ aw' k' C', MemoryCharge 0 aw aw' C C' ∧ RD midnightBytecode I g s0 ret R mem aw' out σ k' C') ∨
    (out.size ≠ 0 ∧
      (config.externalABI.decodeValue? abiBool out = none ∨
        config.externalABI.decodeValue? abiBool out = some (.bool false)) ∧
      RDrev midnightBytecode g s0) := by
  by_cases hempty : out.size = 0
  · exact Or.inl ⟨Or.inl hempty, safeTransferPostEmptyCharge isFrom (by omega)
      (by rw [hsize, hempty]; rfl) hret rd⟩
  have hn : UInt256.ofNat out.size ≠ (⟨0⟩ : UInt256) := by
    intro he
    have he := congrArg UInt256.toNat he
    rw [UInt256.toNat_ofNat_of_lt (by change out.size < 2 ^ 256; omega)] at he
    exact hempty he
  have hhi : out.size < 2 ^ 255 := by omega
  obtain ⟨aw1, k1, C1, hc1, rd1⟩ := safeTransferPostNonemptyCharge isFrom
    (by simp only [List.length_cons]; omega) hsize hn rd
  have hdecodeRet : (D_J midnightBytecode 0).contains (safeTransferDecodeReturnPC isFrom) = true :=
    by cases isFrom <;> jump_dest
  by_cases hlen : 32 ≤ out.size
  · have hc : UInt256.slt (UInt256.sub ((ptr + UInt256.ofNat out.size) + UInt256.ofNat 32)
        (ptr + UInt256.ofNat 32)) (UInt256.ofNat 32) = ⟨0⟩ := by
      rw [safeTransferDecodeDifference]
      exact slt_ofNat_lit_zero (by decide) hlen hhi
    have hw := hword hlen
    have hd := decodeReturnBool_long hlen hhi
    by_cases hz : calldataWord out 0 = ⟨0⟩
    · have hload : memLoad (ptr + UInt256.ofNat 32) mem = ⟨0⟩ := hw.trans hz
      obtain ⟨aw2, k2, C2, hc2, rd2⟩ := midnightBoolMemory_cleanCharge
        (by simp only [List.length_cons]; omega) hc (Or.inl hload) hdecodeRet rd1
      rw [hload] at rd2
      refine Or.inr ⟨hempty, Or.inr ?_, safeTransferPostFalse isFrom
        (by simp only [List.length_cons]; omega) rd2⟩
      change ABI.decodeReturnValue? abiBool out = _
      rw [hd, if_pos hz]
    · by_cases ho : calldataWord out 0 = ⟨1⟩
      · have hload : memLoad (ptr + UInt256.ofNat 32) mem = ⟨1⟩ := hw.trans ho
        obtain ⟨aw2, k2, C2, hc2, rd2⟩ := midnightBoolMemory_cleanCharge
          (by simp only [List.length_cons]; omega) hc (Or.inr hload) hdecodeRet rd1
        rw [hload] at rd2
        obtain ⟨k3, C3, hc3, rd3⟩ := safeTransferPostTrueCharge isFrom (by omega) (by decide) hret rd2
        refine Or.inl ⟨Or.inr ?_, aw2, k3, C3, by simpa using (hc1.trans hc2).trans hc3, rd3⟩
        change ABI.decodeReturnValue? abiBool out = _
        rw [hd, if_neg hz, if_pos ho]
      · refine Or.inr ⟨hempty, Or.inl ?_, midnightBoolMemory_dirty
          (by simp only [List.length_cons]; omega) hc ?_ rd1⟩
        · change ABI.decodeReturnValue? abiBool out = _
          rw [hd, if_neg hz, if_neg ho]
        · rw [hw]
          exact not_or.mpr ⟨hz, ho⟩
  · have hc : UInt256.slt (UInt256.sub ((ptr + UInt256.ofNat out.size) + UInt256.ofNat 32)
        (ptr + UInt256.ofNat 32)) (UInt256.ofNat 32) ≠ ⟨0⟩ := by
      rw [safeTransferDecodeDifference, slt_ofNat_lit_one_low (by decide) (by omega)]
      decide
    exact Or.inr ⟨hempty, Or.inl (decodeReturnBool_short (by omega)),
      midnightBoolMemory_short (by simp only [List.length_cons]; omega) hc rd1⟩

theorem safeTransferPostResult (isFrom : Bool) {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem out : ByteArray} {aw ptr ret : UInt256} {σ : AccountMap} {k C : Nat}
    {R : List UInt256} (hstack : R.length + 7 ≤ 1024) (hb : out.size < 2 ^ 64)
    (hsize : memLoad ptr mem = UInt256.ofNat out.size)
    (hword : 32 ≤ out.size → memLoad (ptr + UInt256.ofNat 32) mem = calldataWord out 0)
    (hret : (D_J midnightBytecode 0).contains ret = true)
    (rd : RD midnightBytecode I g s0 (safeTransferLengthPC isFrom)
      (ptr :: ret :: R) mem aw out σ k C) :
    ((out.size = 0 ∨ config.externalABI.decodeValue? abiBool out = some (.bool true)) ∧
      ∃ aw' k' C', RD midnightBytecode I g s0 ret R mem aw' out σ k' C') ∨
    (out.size ≠ 0 ∧
      (config.externalABI.decodeValue? abiBool out = none ∨
        config.externalABI.decodeValue? abiBool out = some (.bool false)) ∧
      RDrev midnightBytecode g s0) := by
  rcases safeTransferPostResultCharge isFrom hstack hb hsize hword hret rd with
    ⟨hg, aw', k', C', _, rd'⟩ | hbad
  · exact Or.inl ⟨hg, aw', k', C', rd'⟩
  · exact Or.inr hbad

end Benchmarks.Midnight
