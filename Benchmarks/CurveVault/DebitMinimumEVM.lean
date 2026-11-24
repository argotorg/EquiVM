import Benchmarks.CurveVault.Arithmetic
import Benchmarks.CurveVault.RuntimeBlocks_015
import Benchmarks.CurveVault.RuntimeBlocks_016
import Benchmarks.CurveVault.RuntimeBlocks_019
import Benchmarks.CurveVault.RuntimeBlocks_031

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch
namespace Benchmarks.CurveVault

def vaultDebitMinimumEntry (isWithdraw : Bool) : Nat := if isWithdraw then 4202 else 5272
def vaultDebitMinimumCompare (isWithdraw : Bool) : Nat := if isWithdraw then 4231 else 5302
def vaultDebitMinimumRequire (isWithdraw : Bool) : Nat := if isWithdraw then 4257 else 5329
def vaultDebitMinimumNext (isWithdraw : Bool) : Nat := if isWithdraw then 4381 else 5453
def vaultDebitMinimumMemory (isWithdraw : Bool) (mem : ByteArray) : ByteArray :=
  if isWithdraw then (memLoad (UInt256.ofNat 672) mem).toByteArray.write 0 mem 640 32
  else (memLoad (UInt256.ofNat 704) mem).toByteArray.write 0 mem 672 32
def vaultDebitMinimumAssets (isWithdraw : Bool) (I : ExecutionEnv) (mem : ByteArray) : UInt256 :=
  if isWithdraw then calldataWord I.calldata 4 else memLoad (UInt256.ofNat 672) mem

theorem vaultDebitMinimumEVM (isWithdraw : Bool) {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {total assets : UInt256} {R : List UInt256}
    (hmt : memLoad (UInt256.ofNat 640) (vaultDebitMinimumMemory isWithdraw mem) = total)
    (hma : vaultDebitMinimumAssets isWithdraw I (vaultDebitMinimumMemory isWithdraw mem) = assets)
    (hstack : R.length + 8 ≤ 1024)
    (h : RD fork vaultBytecode I g s0 (UInt256.ofNat (vaultDebitMinimumEntry isWithdraw)) R mem aw rdata σ k C) :
    (assets.toNat ≤ total.toNat ∧ (10000 ≤ (UInt256.sub total assets).toNat ∨ total = assets) ∧
      ∃ aw' k' C', RD fork vaultBytecode I g s0 (UInt256.ofNat (vaultDebitMinimumNext isWithdraw)) R
        (vaultDebitMinimumMemory isWithdraw mem) aw' rdata σ k' C') ∨
    (total.toNat < assets.toNat ∧ RDrev fork vaultBytecode g s0) ∨
    (assets.toNat ≤ total.toNat ∧ (UInt256.sub total assets).toNat < 10000 ∧ total ≠ assets ∧ RDrev fork vaultBytecode g s0) := by
  let prepared := vaultDebitMinimumMemory isWithdraw mem
  by_cases hsub : assets.toNat ≤ total.toNat
  swap
  · have hlt : total.toNat < assets.toNat := by omega
    refine Or.inr (Or.inl ⟨hlt, ?_⟩)
    have hcond : UInt256.gt (UInt256.sub total assets) total ≠ ⟨0⟩ := by
      rw [u256_sub_underflow_gt _ _ hlt]; decide +kernel
    cases isWithdraw with
    | false =>
      change memLoad (UInt256.ofNat 640) prepared = total at hmt
      change memLoad (UInt256.ofNat 672) prepared = assets at hma
      obtain ⟨_, _, _, rdFail⟩ := vaultBlocks.vault_block_5272_taken_packed (by omega)
        (by
          change UInt256.gt (UInt256.sub (memLoad (UInt256.ofNat 640) prepared) (memLoad (UInt256.ofNat 672) prepared))
            (memLoad (UInt256.ofNat 640) prepared) ≠ _
          rw [hmt, hma]; exact hcond) (by native_decide) h
      exact vaultBlocks.vault_block_8284
        (by simp only [vaultBlocks.vault_block_5272_taken_stack, List.length_cons]; omega) rdFail
    | true =>
      change memLoad (UInt256.ofNat 640) prepared = total at hmt
      change calldataWord I.calldata 4 = assets at hma
      obtain ⟨_, _, _, rdFail⟩ := vaultBlocks.vault_block_4202_taken_packed (by omega)
        (by
          change UInt256.gt (UInt256.sub (memLoad (UInt256.ofNat 640) prepared) (calldataWord I.calldata 4))
            (memLoad (UInt256.ofNat 640) prepared) ≠ _
          rw [hmt, hma]; exact hcond) (by native_decide) h
      exact vaultBlocks.vault_block_8284
        (by simp only [vaultBlocks.vault_block_4202_taken_stack, List.length_cons]; omega) rdFail
  have hno : UInt256.gt (UInt256.sub total assets) total = ⟨0⟩ :=
    ugt_zero (by rw [usub_toNat hsub]; omega)
  have rdCompare : ∃ aw' k' C', RD fork vaultBytecode I g s0 (UInt256.ofNat (vaultDebitMinimumCompare isWithdraw))
      (UInt256.sub total assets :: assets :: total :: UInt256.ofNat 10000 :: R) prepared aw' rdata σ k' C' := by
    cases isWithdraw with
    | false =>
      change memLoad (UInt256.ofNat 640) prepared = total at hmt
      change memLoad (UInt256.ofNat 672) prepared = assets at hma
      obtain ⟨aw', k', C', rd⟩ := vaultBlocks.vault_block_5272_fallthrough_packed (by omega)
        (by
          change UInt256.gt (UInt256.sub (memLoad (UInt256.ofNat 640) prepared) (memLoad (UInt256.ofNat 672) prepared))
            (memLoad (UInt256.ofNat 640) prepared) = _
          rw [hmt, hma]; exact hno) h
      change RD fork vaultBytecode I g s0 (UInt256.ofNat 5302)
        (UInt256.sub (memLoad (UInt256.ofNat 640) prepared) (memLoad (UInt256.ofNat 672) prepared) :: memLoad (UInt256.ofNat 672) prepared ::
          memLoad (UInt256.ofNat 640) prepared :: UInt256.ofNat 10000 :: R) prepared aw' rdata σ k' C' at rd
      rw [hmt, hma] at rd
      exact ⟨aw', k', C', rd⟩
    | true =>
      change memLoad (UInt256.ofNat 640) prepared = total at hmt
      change calldataWord I.calldata 4 = assets at hma
      obtain ⟨aw', k', C', rd⟩ := vaultBlocks.vault_block_4202_fallthrough_packed (by omega)
        (by
          change UInt256.gt (UInt256.sub (memLoad (UInt256.ofNat 640) prepared) (calldataWord I.calldata 4))
            (memLoad (UInt256.ofNat 640) prepared) = _
          rw [hmt, hma]; exact hno) h
      change RD fork vaultBytecode I g s0 (UInt256.ofNat 4231)
        (UInt256.sub (memLoad (UInt256.ofNat 640) prepared) (calldataWord I.calldata 4) :: calldataWord I.calldata 4 ::
          memLoad (UInt256.ofNat 640) prepared :: UInt256.ofNat 10000 :: R) prepared aw' rdata σ k' C' at rd
      rw [hmt, hma] at rd
      exact ⟨aw', k', C', rd⟩
  obtain ⟨aw0, k0, C0, rdCompare⟩ := rdCompare
  by_cases hmin : 10000 ≤ (UInt256.sub total assets).toNat
  · have hcond : UInt256.isZero (UInt256.lt (UInt256.sub total assets) (UInt256.ofNat 10000)) ≠ ⟨0⟩ := by
      rw [ult_zero (by exact hmin)]; decide +kernel
    have hrd : ∃ aw' k' C', RD fork vaultBytecode I g s0 (UInt256.ofNat (vaultDebitMinimumRequire isWithdraw))
        (⟨1⟩ :: R) prepared aw' rdata σ k' C' := by
      cases isWithdraw
      · obtain ⟨aw1, k1, C1, rdTrue⟩ := vaultBlocks.vault_block_5302_taken_packed (by omega) hcond (by native_decide) rdCompare
        exact vaultBlocks.vault_block_5326_packed (by omega) rdTrue
      · obtain ⟨aw1, k1, C1, rdTrue⟩ := vaultBlocks.vault_block_4231_taken_packed (by omega) hcond (by native_decide) rdCompare
        exact vaultBlocks.vault_block_4254_packed (by omega) rdTrue
    obtain ⟨aw1, k1, C1, rdRequire⟩ := hrd
    refine Or.inl ⟨hsub, Or.inl hmin, ?_⟩
    cases isWithdraw
    · exact vaultBlocks.vault_block_5329_taken_packed (by omega) (by decide +kernel) (by native_decide) rdRequire
    · exact vaultBlocks.vault_block_4257_taken_packed (by omega) (by decide +kernel) (by native_decide) rdRequire
  have hlt : (UInt256.sub total assets).toNat < 10000 := by omega
  have hcond : UInt256.isZero (UInt256.lt (UInt256.sub total assets) (UInt256.ofNat 10000)) = ⟨0⟩ := by
    rw [ult_one (by exact hlt)]; decide +kernel
  have hrd : ∃ aw' k' C', RD fork vaultBytecode I g s0 (UInt256.ofNat (vaultDebitMinimumRequire isWithdraw))
      (UInt256.isZero (UInt256.xor total assets) :: R) prepared aw' rdata σ k' C' := by
    cases isWithdraw with
    | false =>
      change memLoad (UInt256.ofNat 640) prepared = total at hmt
      change memLoad (UInt256.ofNat 672) prepared = assets at hma
      obtain ⟨aw1, k1, C1, rdEqual⟩ := vaultBlocks.vault_block_5302_fallthrough_packed (by omega) hcond rdCompare
      obtain ⟨aw2, k2, C2, rdRequire⟩ := vaultBlocks.vault_block_5312_packed (by change R.length + 2 ≤ 1024; omega) (by native_decide) rdEqual
      change RD fork vaultBytecode I g s0 (UInt256.ofNat 5329)
        (UInt256.isZero (UInt256.xor (memLoad (UInt256.ofNat 640) prepared) (memLoad (UInt256.ofNat 672) prepared)) :: R)
        prepared aw2 rdata σ k2 C2 at rdRequire
      rw [hmt, hma] at rdRequire
      exact ⟨aw2, k2, C2, rdRequire⟩
    | true =>
      change memLoad (UInt256.ofNat 640) prepared = total at hmt
      change calldataWord I.calldata 4 = assets at hma
      obtain ⟨aw1, k1, C1, rdEqual⟩ := vaultBlocks.vault_block_4231_fallthrough_packed (by omega) hcond rdCompare
      obtain ⟨aw2, k2, C2, rdRequire⟩ := vaultBlocks.vault_block_4241_packed (by change R.length + 2 ≤ 1024; omega) (by native_decide) rdEqual
      change RD fork vaultBytecode I g s0 (UInt256.ofNat 4257)
        (UInt256.isZero (UInt256.xor (memLoad (UInt256.ofNat 640) prepared) (calldataWord I.calldata 4)) :: R)
        prepared aw2 rdata σ k2 C2 at rdRequire
      rw [hmt, hma] at rdRequire
      exact ⟨aw2, k2, C2, rdRequire⟩
  obtain ⟨aw1, k1, C1, rdRequire⟩ := hrd
  by_cases heq : total = assets
  · refine Or.inl ⟨hsub, Or.inr heq, ?_⟩
    cases isWithdraw
    · exact vaultBlocks.vault_block_5329_taken_packed (by omega) (isZero_xor_ne_zero_of_eq heq) (by native_decide) rdRequire
    · exact vaultBlocks.vault_block_4257_taken_packed (by omega) (isZero_xor_ne_zero_of_eq heq) (by native_decide) rdRequire
  refine Or.inr (Or.inr ⟨hsub, hlt, heq, ?_⟩)
  cases isWithdraw
  · obtain ⟨_, _, _, rdFail⟩ := vaultBlocks.vault_block_5329_fallthrough_packed (by omega) (isZero_xor_eq_zero_of_ne heq) rdRequire
    exact vaultBlocks.vault_block_5334 hstack rdFail
  · obtain ⟨_, _, _, rdFail⟩ := vaultBlocks.vault_block_4257_fallthrough_packed (by omega) (isZero_xor_eq_zero_of_ne heq) rdRequire
    exact vaultBlocks.vault_block_4262 hstack rdFail

end Benchmarks.CurveVault
