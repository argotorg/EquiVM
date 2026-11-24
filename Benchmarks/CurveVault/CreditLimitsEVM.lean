import Benchmarks.CurveVault.Arithmetic
import Benchmarks.CurveVault.RuntimeBlocks_010
import Benchmarks.CurveVault.RuntimeBlocks_011
import Benchmarks.CurveVault.RuntimeBlocks_013
import Benchmarks.CurveVault.RuntimeBlocks_014
import Benchmarks.CurveVault.RuntimeBlocks_031

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch
namespace Benchmarks.CurveVault

def vaultCreditLimitsEntry (isDeposit : Bool) : Nat := if isDeposit then 2190 else 3359
def vaultCreditLimitsNext (isDeposit : Bool) : Nat := if isDeposit then 2498 else 3669
def vaultCreditMinimumPc (isDeposit : Bool) : Nat := if isDeposit then 2219 else 3389
def vaultCreditCapacityPc (isDeposit : Bool) : Nat := if isDeposit then 2348 else 3518
def vaultCreditMaximumPc (isDeposit : Bool) : Nat := if isDeposit then 2369 else 3540
def vaultCreditLimitsMemory (isDeposit : Bool) (mem : ByteArray) : ByteArray :=
  if isDeposit then (memLoad (UInt256.ofNat 672) mem).toByteArray.write 0 mem 640 32
  else (memLoad (UInt256.ofNat 704) mem).toByteArray.write 0 mem 672 32
def vaultCreditLimitsAssets (isDeposit : Bool) (I : ExecutionEnv) (mem : ByteArray) : UInt256 :=
  if isDeposit then calldataWord I.calldata 4 else memLoad (UInt256.ofNat 672) mem

theorem vaultCreditLimitsEVM (isDeposit : Bool) {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {total assets : UInt256} {R : List UInt256}
    (hmt : memLoad (UInt256.ofNat 640) (vaultCreditLimitsMemory isDeposit mem) = total)
    (hma : vaultCreditLimitsAssets isDeposit I (vaultCreditLimitsMemory isDeposit mem) = assets)
    (hstack : R.length + 8 ≤ 1024)
    (h : RD fork vaultBytecode I g s0 (UInt256.ofNat (vaultCreditLimitsEntry isDeposit)) R mem aw rdata σ k C) :
    (total.toNat + assets.toNat < UInt256.size ∧ 10000 ≤ (total + assets).toNat ∧
      (total + assets).toNat ≤ (codeOwnerStorageWord I σ ⟨5⟩).toNat ∧
      ∃ aw' k' C', RD fork vaultBytecode I g s0 (UInt256.ofNat (vaultCreditLimitsNext isDeposit)) R
        (vaultCreditLimitsMemory isDeposit mem) aw' rdata σ k' C') ∨
    (UInt256.size ≤ total.toNat + assets.toNat ∧ RDrev fork vaultBytecode g s0) ∨
    (total.toNat + assets.toNat < UInt256.size ∧ (total + assets).toNat < 10000 ∧ RDrev fork vaultBytecode g s0) ∨
    (total.toNat + assets.toNat < UInt256.size ∧ 10000 ≤ (total + assets).toNat ∧
      (codeOwnerStorageWord I σ ⟨5⟩).toNat < (total + assets).toNat ∧ RDrev fork vaultBytecode g s0) := by
  let prepared := vaultCreditLimitsMemory isDeposit mem
  let limit := codeOwnerStorageWord I σ ⟨5⟩
  by_cases hfit : total.toNat + assets.toNat < UInt256.size
  swap
  · have hover : UInt256.size ≤ total.toNat + assets.toNat := by omega
    have hcond : UInt256.lt (total + assets) total ≠ ⟨0⟩ := by
      rw [u256_add_overflow_lt _ _ hover]; decide +kernel
    have hrev : RDrev fork vaultBytecode g s0 := by
      cases isDeposit with
      | false =>
        change memLoad (UInt256.ofNat 640) prepared = total at hmt
        change memLoad (UInt256.ofNat 672) prepared = assets at hma
        obtain ⟨_, _, _, rdFail⟩ := vaultBlocks.vault_block_3359_taken_packed (by omega)
          (by
            change UInt256.lt (memLoad (UInt256.ofNat 640) prepared + memLoad (UInt256.ofNat 672) prepared)
              (memLoad (UInt256.ofNat 640) prepared) ≠ _
            rw [hmt, hma]; exact hcond) (by native_decide) h
        exact vaultBlocks.vault_block_8284
          (by simp only [vaultBlocks.vault_block_3359_taken_stack, List.length_cons]; omega) rdFail
      | true =>
        change memLoad (UInt256.ofNat 640) prepared = total at hmt
        change calldataWord I.calldata 4 = assets at hma
        obtain ⟨_, _, _, rdFail⟩ := vaultBlocks.vault_block_2190_taken_packed (by omega)
          (by
            change UInt256.lt (memLoad (UInt256.ofNat 640) prepared + calldataWord I.calldata 4)
              (memLoad (UInt256.ofNat 640) prepared) ≠ _
            rw [hmt, hma]; exact hcond)
          (by native_decide) h
        exact vaultBlocks.vault_block_8284
          (by simp only [vaultBlocks.vault_block_2190_taken_stack, List.length_cons]; omega) rdFail
    exact Or.inr (Or.inl ⟨hover, hrev⟩)
  have hno : UInt256.lt (total + assets) total = ⟨0⟩ :=
    ult_zero (by rw [uadd_toNat, Nat.mod_eq_of_lt hfit]; omega)
  have rdMinimum : ∃ aw' k' C', RD fork vaultBytecode I g s0 (UInt256.ofNat (vaultCreditMinimumPc isDeposit))
      ((total + assets) :: assets :: total :: UInt256.ofNat 10000 :: R) prepared aw' rdata σ k' C' := by
    cases isDeposit with
    | false =>
      change memLoad (UInt256.ofNat 640) prepared = total at hmt
      change memLoad (UInt256.ofNat 672) prepared = assets at hma
      obtain ⟨aw', k', C', rd⟩ := vaultBlocks.vault_block_3359_fallthrough_packed (by omega)
        (by
          change UInt256.lt (memLoad (UInt256.ofNat 640) prepared + memLoad (UInt256.ofNat 672) prepared)
            (memLoad (UInt256.ofNat 640) prepared) = _
          rw [hmt, hma]; exact hno) h
      change RD fork vaultBytecode I g s0 (UInt256.ofNat 3389)
        ((memLoad (UInt256.ofNat 640) prepared + memLoad (UInt256.ofNat 672) prepared) ::
          memLoad (UInt256.ofNat 672) prepared :: memLoad (UInt256.ofNat 640) prepared ::
          UInt256.ofNat 10000 :: R) prepared aw' rdata σ k' C' at rd
      rw [hmt, hma] at rd
      exact ⟨_, _, _, rd⟩
    | true =>
      change memLoad (UInt256.ofNat 640) prepared = total at hmt
      change calldataWord I.calldata 4 = assets at hma
      obtain ⟨aw', k', C', rd⟩ := vaultBlocks.vault_block_2190_fallthrough_packed (by omega)
        (by
          change UInt256.lt (memLoad (UInt256.ofNat 640) prepared + calldataWord I.calldata 4)
            (memLoad (UInt256.ofNat 640) prepared) = _
          rw [hmt, hma]; exact hno) h
      change RD fork vaultBytecode I g s0 (UInt256.ofNat 2219)
        ((memLoad (UInt256.ofNat 640) prepared + calldataWord I.calldata 4) :: calldataWord I.calldata 4 ::
          memLoad (UInt256.ofNat 640) prepared :: UInt256.ofNat 10000 :: R) prepared aw' rdata σ k' C' at rd
      rw [hmt, hma] at rd
      exact ⟨_, _, _, rd⟩
  obtain ⟨aw0, k0, C0, rdMinimum⟩ := rdMinimum
  by_cases hmin : 10000 ≤ (total + assets).toNat
  swap
  · have hlt : (total + assets).toNat < 10000 := by omega
    have hcond : UInt256.isZero (UInt256.lt (total + assets) (UInt256.ofNat 10000)) = ⟨0⟩ := by
      rw [ult_one (by exact hlt)]; decide +kernel
    have hrev : RDrev fork vaultBytecode g s0 := by
      cases isDeposit with
      | false =>
        obtain ⟨_, _, _, rdFail⟩ := vaultBlocks.vault_block_3389_fallthrough_packed (by omega) hcond rdMinimum
        exact vaultBlocks.vault_block_3399 hstack rdFail
      | true =>
        obtain ⟨_, _, _, rdFail⟩ := vaultBlocks.vault_block_2219_fallthrough_packed (by omega) hcond rdMinimum
        exact vaultBlocks.vault_block_2229 hstack rdFail
    exact Or.inr (Or.inr (Or.inl ⟨hfit, hlt, hrev⟩))
  have hminCond : UInt256.isZero (UInt256.lt (total + assets) (UInt256.ofNat 10000)) ≠ ⟨0⟩ := by
    rw [ult_zero (by exact hmin)]; decide +kernel
  have rdCapacity : ∃ aw' k' C', RD fork vaultBytecode I g s0 (UInt256.ofNat (vaultCreditCapacityPc isDeposit))
      R prepared aw' rdata σ k' C' := by
    cases isDeposit
    · exact vaultBlocks.vault_block_3389_taken_packed (by omega) hminCond (by native_decide) rdMinimum
    · exact vaultBlocks.vault_block_2219_taken_packed (by omega) hminCond (by native_decide) rdMinimum
  obtain ⟨aw1, k1, C1, rdCapacity⟩ := rdCapacity
  have rdMaximum : ∃ aw' k' C', RD fork vaultBytecode I g s0 (UInt256.ofNat (vaultCreditMaximumPc isDeposit))
      ((total + assets) :: assets :: total :: limit :: R) prepared aw' rdata σ k' C' := by
    cases isDeposit with
    | false =>
      change memLoad (UInt256.ofNat 640) prepared = total at hmt
      change memLoad (UInt256.ofNat 672) prepared = assets at hma
      obtain ⟨aw', k', C', rd⟩ := vaultBlocks.vault_block_3518_fallthrough_packed (by omega)
        (by
          change UInt256.lt (memLoad (UInt256.ofNat 640) prepared + memLoad (UInt256.ofNat 672) prepared)
            (memLoad (UInt256.ofNat 640) prepared) = _
          rw [hmt, hma]; exact hno) rdCapacity
      dsimp only [vaultBlocks.vault_block_3518_fallthrough_stack] at rd
      rw [hmt, hma] at rd
      exact ⟨_, _, _, rd⟩
    | true =>
      change memLoad (UInt256.ofNat 640) prepared = total at hmt
      change calldataWord I.calldata 4 = assets at hma
      obtain ⟨aw', k', C', rd⟩ := vaultBlocks.vault_block_2348_fallthrough_packed (by omega)
        (by
          change UInt256.lt (memLoad (UInt256.ofNat 640) prepared + calldataWord I.calldata 4)
            (memLoad (UInt256.ofNat 640) prepared) = _
          rw [hmt, hma]; exact hno) rdCapacity
      change RD fork vaultBytecode I g s0 (UInt256.ofNat 2369)
        ((memLoad (UInt256.ofNat 640) prepared + calldataWord I.calldata 4) :: calldataWord I.calldata 4 ::
          memLoad (UInt256.ofNat 640) prepared :: limit :: R) prepared aw' rdata σ k' C' at rd
      rw [hmt, hma] at rd
      exact ⟨_, _, _, rd⟩
  obtain ⟨aw2, k2, C2, rdMaximum⟩ := rdMaximum
  by_cases hmax : (total + assets).toNat ≤ limit.toNat
  · have hcond : UInt256.isZero (UInt256.gt (total + assets) limit) ≠ ⟨0⟩ := by
      rw [ugt_zero hmax]; decide +kernel
    refine Or.inl ⟨hfit, hmin, hmax, ?_⟩
    cases isDeposit
    · exact vaultBlocks.vault_block_3540_taken_packed (by omega) hcond (by native_decide) rdMaximum
    · exact vaultBlocks.vault_block_2369_taken_packed (by omega) hcond (by native_decide) rdMaximum
  · have hlt : limit.toNat < (total + assets).toNat := by omega
    have hcond : UInt256.isZero (UInt256.gt (total + assets) limit) = ⟨0⟩ := by
      rw [ugt_one hlt]; decide +kernel
    have hrev : RDrev fork vaultBytecode g s0 := by
      cases isDeposit with
      | false =>
        obtain ⟨_, _, _, rdFail⟩ := vaultBlocks.vault_block_3540_fallthrough_packed (by omega) hcond rdMaximum
        exact vaultBlocks.vault_block_3550 hstack rdFail
      | true =>
        obtain ⟨_, _, _, rdFail⟩ := vaultBlocks.vault_block_2369_fallthrough_packed (by omega) hcond rdMaximum
        exact vaultBlocks.vault_block_2379 hstack rdFail
    exact Or.inr (Or.inr (Or.inr ⟨hfit, hmin, hlt, hrev⟩))

end Benchmarks.CurveVault
