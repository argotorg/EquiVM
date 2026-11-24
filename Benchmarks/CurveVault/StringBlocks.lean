import Benchmarks.CurveVault.StringSource
import Benchmarks.CurveVault.RuntimeBlocks_023
import Benchmarks.CurveVault.RuntimeBlocks_031

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch
namespace Benchmarks.CurveVault

def vaultStringPc (isName : Bool) (namePc : Nat) : UInt256 :=
  UInt256.ofNat (if isName then namePc else namePc + 107)

def vaultStringCopyWord (I : ExecutionEnv) (σ : AccountMap) (slot index : UInt256) (mem : ByteArray) : ByteArray :=
  (codeOwnerStorageWord I σ (slot + index)).toByteArray.write 0 mem
    (UInt256.ofNat 96 + UInt256.shiftLeft index (UInt256.ofNat 5)).toNat 32

theorem vaultStringEntryPass {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {R : List UInt256} (isName : Bool)
    (hstack : R.length + 7 ≤ 1024)
    (hcond : UInt256.gt (vyperStringWords (codeOwnerStorageWord I σ (vaultStringSlot isName))) ⟨3⟩ = ⟨0⟩)
    (h : RD fork vaultBytecode I g s0 (vaultStringPc isName 6437) R mem aw rdata σ k C) :
    ∃ aw' k' C', RD fork vaultBytecode I g s0 (vaultStringPc isName 6470)
      (vyperStringWords (codeOwnerStorageWord I σ (vaultStringSlot isName)) :: ⟨0⟩ ::
        (codeOwnerStorageWord I σ (vaultStringSlot isName) + ⟨32⟩) :: ⟨96⟩ :: ⟨32⟩ :: R)
      ((⟨32⟩ : UInt256).toByteArray.write 0 mem 64 32) aw' rdata σ k' C' := by
  cases isName with
  | false => exact vaultBlocks.vault_block_6544_fallthrough_packed hstack hcond h
  | true => exact vaultBlocks.vault_block_6437_fallthrough_packed hstack hcond h

theorem vaultStringEntryRevert {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {R : List UInt256} (isName : Bool)
    (hstack : R.length + 7 ≤ 1024)
    (hcond : UInt256.gt (vyperStringWords (codeOwnerStorageWord I σ (vaultStringSlot isName))) ⟨3⟩ ≠ ⟨0⟩)
    (h : RD fork vaultBytecode I g s0 (vaultStringPc isName 6437) R mem aw rdata σ k C) :
    RDrev fork vaultBytecode g s0 := by
  cases isName with
  | false =>
      obtain ⟨_, _, rdFail⟩ := vaultBlocks.vault_block_6544_taken hstack hcond (by native_decide) h
      exact vaultBlocks.vault_block_8284
        (by simp only [vaultBlocks.vault_block_6544_taken_stack, List.length_cons]; omega) rdFail
  | true =>
      obtain ⟨_, _, rdFail⟩ := vaultBlocks.vault_block_6437_taken hstack hcond (by native_decide) h
      exact vaultBlocks.vault_block_8284
        (by simp only [vaultBlocks.vault_block_6437_taken_stack, List.length_cons]; omega) rdFail

theorem vaultStringCopySkip {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {saved : UInt256} {R : List UInt256} (isName : Bool)
    (hstack : R.length + 7 ≤ 1024)
    (h : RD fork vaultBytecode I g s0 (vaultStringPc isName 6470)
      (⟨0⟩ :: ⟨0⟩ :: saved :: ⟨96⟩ :: ⟨32⟩ :: R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD fork vaultBytecode I g s0 (vaultStringPc isName 6500)
      (⟨0⟩ :: ⟨0⟩ :: saved :: ⟨96⟩ :: ⟨32⟩ :: R) mem aw' rdata σ k' C' := by
  cases isName with
  | false =>
      exact vaultBlocks.vault_block_6577_taken_packed
        (by simp only [List.length_cons]; omega) (by decide +kernel) (by native_decide) h
  | true =>
      exact vaultBlocks.vault_block_6470_taken_packed
        (by simp only [List.length_cons]; omega) (by decide +kernel) (by native_decide) h

theorem vaultStringCopyStart {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {count saved : UInt256} {R : List UInt256} (isName : Bool)
    (hstack : R.length + 7 ≤ 1024) (hnz : count ≠ ⟨0⟩)
    (h : RD fork vaultBytecode I g s0 (vaultStringPc isName 6470)
      (count :: ⟨0⟩ :: saved :: ⟨96⟩ :: ⟨32⟩ :: R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD fork vaultBytecode I g s0 (vaultStringPc isName 6477)
      (⟨0⟩ :: count :: saved :: ⟨96⟩ :: ⟨32⟩ :: R) mem aw' rdata σ k' C' := by
  cases isName with
  | false =>
      have rdStart := vaultBlocks.vault_block_6577_fallthrough
        (by simp only [List.length_cons]; omega) (isZero_eq_zero_of_ne hnz) h
      exact vaultBlocks.vault_block_6583_packed (by simp only [List.length_cons]; omega) rdStart
  | true =>
      have rdStart := vaultBlocks.vault_block_6470_fallthrough
        (by simp only [List.length_cons]; omega) (isZero_eq_zero_of_ne hnz) h
      exact vaultBlocks.vault_block_6476_packed (by simp only [List.length_cons]; omega) rdStart

theorem vaultStringCopyStep {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {index count saved : UInt256} {R : List UInt256} (isName : Bool)
    (hstack : R.length + 8 ≤ 1024) (hmore : ⟨1⟩ + index ≠ count)
    (h : RD fork vaultBytecode I g s0 (vaultStringPc isName 6477)
      (index :: count :: saved :: ⟨96⟩ :: ⟨32⟩ :: R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD fork vaultBytecode I g s0 (vaultStringPc isName 6477)
      ((⟨1⟩ + index) :: count :: saved :: ⟨96⟩ :: ⟨32⟩ :: R)
      (vaultStringCopyWord I σ (vaultStringSlot isName) index mem) aw' rdata σ k' C' := by
  cases isName with
  | false =>
      exact vaultBlocks.vault_block_6584_taken_packed
        (by simp only [List.length_cons]; omega) (u256_xor_ne_zero_of_ne hmore) (by native_decide) h
  | true =>
      exact vaultBlocks.vault_block_6477_taken_packed
        (by simp only [List.length_cons]; omega) (u256_xor_ne_zero_of_ne hmore) (by native_decide) h

theorem vaultStringCopyLast {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {index count saved : UInt256} {R : List UInt256} (isName : Bool)
    (hstack : R.length + 8 ≤ 1024) (hdone : ⟨1⟩ + index = count)
    (h : RD fork vaultBytecode I g s0 (vaultStringPc isName 6477)
      (index :: count :: saved :: ⟨96⟩ :: ⟨32⟩ :: R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD fork vaultBytecode I g s0 (vaultStringPc isName 6500)
      (count :: count :: saved :: ⟨96⟩ :: ⟨32⟩ :: R)
      (vaultStringCopyWord I σ (vaultStringSlot isName) index mem) aw' rdata σ k' C' := by
  change UInt256.ofNat 1 + index = count at hdone
  have hcond : UInt256.xor (UInt256.ofNat 1 + index) count = UInt256.ofNat 0 := by rw [hdone, u256_xor_self]; rfl
  cases isName with
  | false =>
      obtain ⟨aw', k', C', rdNext⟩ := vaultBlocks.vault_block_6584_fallthrough_packed
        (by simp only [List.length_cons]; omega) hcond h
      dsimp only [vaultBlocks.vault_block_6584_fallthrough_stack] at rdNext
      rw [hdone] at rdNext
      exact ⟨aw', k', C', rdNext⟩
  | true =>
      obtain ⟨aw', k', C', rdNext⟩ := vaultBlocks.vault_block_6477_fallthrough_packed
        (by simp only [List.length_cons]; omega) hcond h
      dsimp only [vaultBlocks.vault_block_6477_fallthrough_stack] at rdNext
      rw [hdone] at rdNext
      exact ⟨aw', k', C', rdNext⟩

def vaultStringPaddedMem (I : ExecutionEnv) (mem : ByteArray) : ByteArray :=
  I.calldata.write (UInt256.ofNat I.calldata.size).toNat mem
    (UInt256.ofNat 128 + memLoad ⟨96⟩ mem).toNat
    (UInt256.land (UInt256.sub ⟨0⟩ (memLoad ⟨96⟩ mem)) ⟨31⟩).toNat

def vaultStringOutput (I : ExecutionEnv) (mem : ByteArray) : ByteArray :=
  (vaultStringPaddedMem I mem).readWithPadding 64
    ((⟨32⟩ : UInt256) + UInt256.land (⟨32⟩ + memLoad ⟨96⟩ (vaultStringPaddedMem I mem) + ⟨31⟩) (UInt256.lnot ⟨31⟩)).toNat

theorem vaultStringFinish {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {unused0 unused1 unused2 : UInt256} {R : List UInt256} (isName : Bool)
    (hstack : R.length + 7 ≤ 1024)
    (h : RD fork vaultBytecode I g s0 (vaultStringPc isName 6500)
      (unused0 :: unused1 :: unused2 :: ⟨96⟩ :: ⟨32⟩ :: R) mem aw rdata σ k C) :
    RDret fork vaultBytecode g s0 σ (vaultStringOutput I mem) := by
  cases isName with
  | false => exact vaultBlocks.vault_block_6607 hstack h
  | true => exact vaultBlocks.vault_block_6500 hstack h

end Benchmarks.CurveVault
