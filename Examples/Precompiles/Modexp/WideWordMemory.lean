import Examples.Precompiles.Modexp.Operands
import Examples.Precompiles.Modexp.OneLimbModel

/-!
# Memory vocabulary for the arbitrary-input, single-word-modulus helper

The helper only performs already-allocated memory accesses until its final result write.  These
definitions and rules expose the exact word loaded by `MLOAD` while proving that such accesses add
no memory-expansion gas.  They are operational vocabulary; the operand-buffer theorems later
identify these words and bytes with slices of the unchanged trusted model.
-/

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Modexp

set_option maxRecDepth 30000
set_option maxHeartbeats 0

/-- The value pushed by `MLOAD`, including the EVM's zero result for an address outside concrete
memory or beyond the active-memory frontier. -/
def wideLoadWord (mem : ByteArray) (aw off : UInt256) : UInt256 :=
  if off.toNat ≥ mem.size ∨ off ≥ aw * ⟨32⟩ then ⟨0⟩
  else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding off.toNat 32))

theorem wideLoadWord_eq_of_read {mem : ByteArray} {aw off value : UInt256}
    (hmem : off.toNat < mem.size) (haw : ¬ off ≥ aw * ⟨32⟩)
    (hread : mem.readWithPadding off.toNat 32 = UInt256.toByteArray value) :
    wideLoadWord mem aw off = value := by
  unfold wideLoadWord
  exact mloadWordValue_of_readWithPadding hmem haw hread

private theorem operandWordsBound
    {baseSize exponentSize modulusSize : Nat}
    (hb : baseSize ≤ 1024) (he : exponentSize ≤ 1024) (hm : modulusSize ≤ 1024) :
    operandModulusWords baseSize exponentSize modulusSize < UInt256.size := by
  apply lt_of_le_of_lt
    (show operandModulusWords baseSize exponentSize modulusSize ≤ 103 by
      unfold operandModulusWords operandExponentWords operandBaseWords bytesAllocationWords
      omega)
  decide

private theorem operandActiveMul32_toNat
    {baseSize exponentSize modulusSize : Nat}
    (hb : baseSize ≤ 1024) (he : exponentSize ≤ 1024) (hm : modulusSize ≤ 1024) :
    (operandModulusActiveWords baseSize exponentSize modulusSize * ⟨32⟩).toNat =
      32 * operandModulusWords baseSize exponentSize modulusSize := by
  rw [umul_toNat]
  · rw [show (⟨32⟩ : UInt256).toNat = 32 from by decide]
    unfold operandModulusActiveWords
    rw [UInt256.toNat_ofNat_of_lt (operandWordsBound hb he hm)]
    omega
  · rw [show (⟨32⟩ : UInt256).toNat = 32 from by decide]
    unfold operandModulusActiveWords
    rw [UInt256.toNat_ofNat_of_lt (operandWordsBound hb he hm)]
    apply lt_of_le_of_lt
      (show operandModulusWords baseSize exponentSize modulusSize * 32 ≤ 3296 by
        have := operandWordsBound hb he hm
        unfold operandModulusWords operandExponentWords operandBaseWords bytesAllocationWords at *
        omega)
    decide

private theorem operandHeaderBelowActive
    {baseSize exponentSize modulusSize ptr : Nat}
    (hb : baseSize ≤ 1024) (he : exponentSize ≤ 1024) (hm : modulusSize ≤ 1024)
    (hptr : ptr + 32 ≤ 32 * operandModulusWords baseSize exponentSize modulusSize)
    (hptr256 : ptr < UInt256.size) :
    ¬ UInt256.ofNat ptr ≥
      operandModulusActiveWords baseSize exponentSize modulusSize * ⟨32⟩ := by
  intro h
  change (operandModulusActiveWords baseSize exponentSize modulusSize * ⟨32⟩).toNat ≤
    (UInt256.ofNat ptr).toNat at h
  rw [operandActiveMul32_toNat hb he hm,
    UInt256.toNat_ofNat_of_lt hptr256] at h
  omega

theorem operandCopiedWideLoadBaseLength (I : ExecutionEnv)
    (baseSize exponentSize modulusSize : Nat)
    (hb : baseSize ≤ 1024) (he : exponentSize ≤ 1024) (hm : modulusSize ≤ 1024) :
    wideLoadWord (operandCopiedMemory I baseSize exponentSize modulusSize)
      (operandModulusActiveWords baseSize exponentSize modulusSize)
      (UInt256.ofNat operandBasePtr) = UInt256.ofNat baseSize := by
  apply wideLoadWord_eq_of_read
  · rw [UInt256.toNat_ofNat_of_lt (by unfold operandBasePtr; decide)]
    have hs := operandCopiedMemory_size_ge I baseSize exponentSize modulusSize hb he
    unfold operandModulusPtr operandExponentPtr operandBasePtr bytesAllocationSize at hs
    unfold operandBasePtr
    omega
  · apply operandHeaderBelowActive hb he hm
    · unfold operandModulusWords operandExponentWords operandBaseWords operandBasePtr
        bytesAllocationWords
      omega
    · unfold operandBasePtr
      decide
  · rw [UInt256.toNat_ofNat_of_lt (by unfold operandBasePtr; decide)]
    exact operandCopiedMemory_readBaseLength I baseSize exponentSize modulusSize hb he

theorem operandCopiedWideLoadExponentLength (I : ExecutionEnv)
    (baseSize exponentSize modulusSize : Nat)
    (hb : baseSize ≤ 1024) (he : exponentSize ≤ 1024) (hm : modulusSize ≤ 1024) :
    wideLoadWord (operandCopiedMemory I baseSize exponentSize modulusSize)
      (operandModulusActiveWords baseSize exponentSize modulusSize)
      (UInt256.ofNat (operandExponentPtr baseSize)) = UInt256.ofNat exponentSize := by
  have hptr256 : operandExponentPtr baseSize < UInt256.size := by
    apply lt_of_le_of_lt
      (show operandExponentPtr baseSize ≤ 1184 by
        unfold operandExponentPtr operandBasePtr bytesAllocationSize
        omega)
    decide
  apply wideLoadWord_eq_of_read
  · rw [UInt256.toNat_ofNat_of_lt hptr256]
    have hs := operandCopiedMemory_size_ge I baseSize exponentSize modulusSize hb he
    unfold operandModulusPtr operandExponentPtr operandBasePtr bytesAllocationSize at hs
    unfold operandExponentPtr operandBasePtr bytesAllocationSize
    omega
  · apply operandHeaderBelowActive hb he hm
    · rw [operandExponentPtr_eq]
      unfold operandModulusWords operandExponentWords bytesAllocationWords
      omega
    · exact hptr256
  · rw [UInt256.toNat_ofNat_of_lt hptr256]
    exact operandCopiedMemory_readExponentLength I baseSize exponentSize modulusSize hb he

theorem operandCopiedWideLoadModulusLength (I : ExecutionEnv)
    (baseSize exponentSize modulusSize : Nat)
    (hb : baseSize ≤ 1024) (he : exponentSize ≤ 1024) (hm : modulusSize ≤ 1024) :
    wideLoadWord (operandCopiedMemory I baseSize exponentSize modulusSize)
      (operandModulusActiveWords baseSize exponentSize modulusSize)
      (UInt256.ofNat (operandModulusPtr baseSize exponentSize)) =
        UInt256.ofNat modulusSize := by
  have hptr256 : operandModulusPtr baseSize exponentSize < UInt256.size := by
    apply lt_of_le_of_lt
      (show operandModulusPtr baseSize exponentSize ≤ 2240 by
        unfold operandModulusPtr operandExponentPtr operandBasePtr bytesAllocationSize
        omega)
    decide
  apply wideLoadWord_eq_of_read
  · rw [UInt256.toNat_ofNat_of_lt hptr256]
    have hs := operandCopiedMemory_size_ge I baseSize exponentSize modulusSize hb he
    omega
  · apply operandHeaderBelowActive hb he hm
    · rw [operandModulusPtr_eq]
      unfold operandModulusWords bytesAllocationWords
      omega
    · exact hptr256
  · rw [UInt256.toNat_ofNat_of_lt hptr256]
    exact operandCopiedMemory_readModulusLength I baseSize exponentSize modulusSize hb he

theorem machineM_eq_of_access {aw off len : Nat}
    (haccess : off + len ≤ 32 * aw) : MachineState.M aw off len = aw := by
  cases len with
  | zero => rfl
  | succ len =>
      simp only [MachineState.M]
      apply max_eq_left
      rw [Nat.div_le_iff_le_mul (by decide : 0 < 32)]
      omega

/-- Exact `MLOAD` at an address whose 32-byte window is already active. -/
theorem RDx.mloadWithin
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc off : UInt256} {t : List UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat}
    (h : RDx code ee g s0 pc (off :: t) mem aw rdata acc k C)
    (hdec : decode code pc = some (.MLOAD, .none))
    (haccess : off.toNat + 32 ≤ 32 * aw.toNat)
    (hov : t.length + 1 ≤ 1024) :
    RDx code ee g s0 (pc + ⟨1⟩) (wideLoadWord mem aw off :: t)
      mem aw rdata acc (k + 1) (C + 3) := by
  apply RDx.mload 0 (wideLoadWord mem aw off) aw h hdec
  · intro s hsaw hstk
    simp [memoryExpansionCost, memoryExpansionCost.μᵢ', hstk, hsaw,
      machineM_eq_of_access haccess]
    rw [u256_ofNat_toNat]
    omega
  · rfl
  · rw [machineM_eq_of_access haccess, u256_ofNat_toNat]
  · exact hov

/-- Exact `MLOAD` at any address.  The loaded value is computed using the pre-instruction active
word frontier, and the output active word / gas cost account for any expansion caused by the
access. -/
theorem RDx.mloadAny
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc off : UInt256} {t : List UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat}
    (h : RDx code ee g s0 pc (off :: t) mem aw rdata acc k C)
    (hdec : decode code pc = some (.MLOAD, .none))
    (hov : t.length + 1 ≤ 1024) :
    RDx code ee g s0 (pc + ⟨1⟩) (wideLoadWord mem aw off :: t)
      mem (UInt256.ofNat (MachineState.M aw.toNat off.toNat 32)) rdata acc
      (k + 1)
      (C + ((Cₘ (UInt256.ofNat (MachineState.M aw.toNat off.toNat 32)) - Cₘ aw) + 3)) := by
  apply RDx.mload
      (Cₘ (UInt256.ofNat (MachineState.M aw.toNat off.toNat 32)) - Cₘ aw)
      (wideLoadWord mem aw off)
      (UInt256.ofNat (MachineState.M aw.toNat off.toNat 32))
      h hdec
  · intro s hsaw hstk
    simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', hstk, hsaw,
      List.getElem!_cons_zero]
  · rfl
  · rfl
  · exact hov

theorem ofNat_toNat_bounded {n : Nat} (hn : n < UInt256.size) :
    (UInt256.ofNat n).toNat = n := UInt256.toNat_ofNat_of_lt hn

theorem ofNat_add_bounded {a b : Nat} (h : a + b < UInt256.size) :
    UInt256.ofNat a + UInt256.ofNat b = UInt256.ofNat (a + b) := by
  apply u256_inj
  rw [uadd_toNat, UInt256.toNat_ofNat_of_lt (by omega),
    UInt256.toNat_ofNat_of_lt (by omega), UInt256.toNat_ofNat_of_lt h,
    Nat.mod_eq_of_lt h]

theorem ofNat_sub_bounded {a b : Nat} (hba : b ≤ a) (ha : a < UInt256.size) :
    UInt256.sub (UInt256.ofNat a) (UInt256.ofNat b) = UInt256.ofNat (a - b) := by
  apply u256_inj
  rw [usub_ofNat_lit_toNat hba ha,
    UInt256.toNat_ofNat_of_lt (lt_of_le_of_lt (Nat.sub_le _ _) ha)]

end Modexp
