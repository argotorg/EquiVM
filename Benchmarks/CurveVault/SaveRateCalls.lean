import Benchmarks.CurveVault.VoidCalls
import Benchmarks.CurveVault.MutationSites
import Benchmarks.CurveVault.RuntimeBlocks_011
import Benchmarks.CurveVault.RuntimeBlocks_014
import Benchmarks.CurveVault.RuntimeBlocks_017
import Benchmarks.CurveVault.RuntimeBlocks_019
import Benchmarks.CurveVault.RuntimeBlocks_020
import Benchmarks.CurveVault.RuntimeBlocks_031

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch Reasoning.VyperCalls
namespace Benchmarks.CurveVault

def vaultSaveRateMemory (flow : VaultFlow) (mem : ByteArray) : ByteArray :=
  (UInt256.ofNat 1774616654).toByteArray.write 0 mem flow.callOffset 32

theorem vaultSaveRateCall (flow : VaultFlow) {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {target : UInt256} {R : List UInt256} {locals : Store} {retVar : Ident}
    (hs : SourceState s0 I σ evm)
    (htarget : locals.get? "controller" = some (.address (AccountAddress.ofUInt256 target)))
    (hload : memLoad (UInt256.ofNat flow.controllerOffset) mem = target)
    (hstack : R.length + 8 ≤ 1024)
    (h : RD fork vaultBytecode I g s0 (UInt256.ofNat flow.saveEntry) R mem aw rdata σ k C) :
    (∃ (evm' : State) (σ' : AccountMap) (out : ByteArray) (aw' : UInt256) (k' C' : Nat),
      ExecBlock fork config {contract := contract, locals := locals} evm
        [.require (.binary .gt (.extCodeSize (.var "controller")) (.intLit 0)),
          .externalCall (.var "controller") "save_rate" (.intLit 0) [] retVar]
        (.ok {contract := contract, locals := locals.insert retVar (collapseReturns [])} evm') ∧
      SourceState s0 I σ' evm' ∧ RD fork vaultBytecode I g s0 (UInt256.ofNat flow.saveNext)
        (target :: R) (vaultSaveRateMemory flow mem) aw' out σ' k' C') ∨
    (ExecBlock fork config {contract := contract, locals := locals} evm
      [.require (.binary .gt (.extCodeSize (.var "controller")) (.intLit 0)),
        .externalCall (.var "controller") "save_rate" (.intLit 0) [] retVar] .reverted ∧ RDrev fork vaultBytecode g s0) := by
  have hr : evalExpr? config {contract := contract, locals := locals} evm (.var "controller") =
      .ok (.address (AccountAddress.ofUInt256 target)) := by
    rw [evalExpr?]; simp only [htarget, EvalResult.ofOption]
  have hcd : config.externalABI.encode? "save_rate" [] =
      some ((vaultSaveRateMemory flow mem).readWithPadding (flow.callOffset + 28) 4) := by
    exact vyperNullaryCallData (UInt256.ofNat 1774616654) (selectorBytes 0x69 0xc6 0x80 0x4e) mem flow.callOffset
      (by native_decide) (lt_of_le_of_lt (Nat.sub_le _ _) (by cases flow <;> exact lt_usize _ (by decide +kernel)))
  apply checkedVoidCallBridge (pc := UInt256.ofNat flow.saveCall) (argVals := [])
    (R := target :: R) (nextStack := target :: R)
    (inOffset := UInt256.ofNat (flow.callOffset + 28)) (inSize := UInt256.ofNat 4)
    (outOffset := UInt256.ofNat flow.callOffset) hs hr (by simp [evalExprs?, pure])
    (by simpa only [ulit_toNat' _ (show flow.callOffset + 28 < UInt256.size by cases flow <;> decide +kernel)] using hcd)
    (fun _ => rfl) (by cases flow <;> native_decide) (by decide +kernel)
    (by simp only [List.length_cons]; omega)
  · intro hcode
    cases flow with
    | deposit =>
      change memLoad (UInt256.ofNat 608) mem = target at hload
      obtain ⟨aw0, k0, C0, rdReady⟩ := vaultBlocks.vault_block_2771_fallthrough_packed
        (by omega) (by rw [hload]; exact isZero_eq_zero_of_ne hcode) h
      obtain ⟨aw1, k1, C1, rdCall⟩ := vaultBlocks.vault_block_2792_packed (by omega) rdReady
      dsimp only [vaultBlocks.vault_block_2792_stack, vaultBlocks.vault_block_2771_fallthrough_stack] at rdCall
      rw [hload] at rdCall
      exact ⟨_, aw1, k1, C1, rdCall⟩
    | mint =>
      change memLoad (UInt256.ofNat 608) mem = target at hload
      obtain ⟨aw0, k0, C0, rdReady⟩ := vaultBlocks.vault_block_3775_fallthrough_packed
        (by omega) (by rw [hload]; exact isZero_eq_zero_of_ne hcode) h
      obtain ⟨aw1, k1, C1, rdCall⟩ := vaultBlocks.vault_block_3796_packed (by omega) rdReady
      dsimp only [vaultBlocks.vault_block_3796_stack, vaultBlocks.vault_block_3775_fallthrough_stack] at rdCall
      rw [hload] at rdCall
      exact ⟨_, aw1, k1, C1, rdCall⟩
    | withdraw =>
      change memLoad (UInt256.ofNat 704) mem = target at hload
      obtain ⟨aw0, k0, C0, rdReady⟩ := vaultBlocks.vault_block_4664_fallthrough_packed
        (by omega) (by rw [hload]; exact isZero_eq_zero_of_ne hcode) h
      obtain ⟨aw1, k1, C1, rdCall⟩ := vaultBlocks.vault_block_4685_packed (by omega) rdReady
      dsimp only [vaultBlocks.vault_block_4685_stack, vaultBlocks.vault_block_4664_fallthrough_stack] at rdCall
      rw [hload] at rdCall
      exact ⟨_, aw1, k1, C1, rdCall⟩
    | redeem =>
      change memLoad (UInt256.ofNat 704) mem = target at hload
      obtain ⟨aw0, k0, C0, rdReady⟩ := vaultBlocks.vault_block_5569_fallthrough_packed
        (by omega) (by rw [hload]; exact isZero_eq_zero_of_ne hcode) h
      obtain ⟨aw1, k1, C1, rdCall⟩ := vaultBlocks.vault_block_5590_packed (by omega) rdReady
      dsimp only [vaultBlocks.vault_block_5590_stack, vaultBlocks.vault_block_5569_fallthrough_stack] at rdCall
      rw [hload] at rdCall
      exact ⟨_, aw1, k1, C1, rdCall⟩
  · intro hcode
    cases flow with
    | deposit =>
      change memLoad (UInt256.ofNat 608) mem = target at hload
      obtain ⟨_, _, _, rdFail⟩ := vaultBlocks.vault_block_2771_taken_packed
        (by omega) (by rw [hload, hcode]; decide +kernel) (by native_decide) h
      exact vaultBlocks.vault_block_8284
        (by simp only [vaultBlocks.vault_block_2771_taken_stack, List.length_cons]; omega) rdFail
    | mint =>
      change memLoad (UInt256.ofNat 608) mem = target at hload
      obtain ⟨_, _, _, rdFail⟩ := vaultBlocks.vault_block_3775_taken_packed
        (by omega) (by rw [hload, hcode]; decide +kernel) (by native_decide) h
      exact vaultBlocks.vault_block_8284
        (by simp only [vaultBlocks.vault_block_3775_taken_stack, List.length_cons]; omega) rdFail
    | withdraw =>
      change memLoad (UInt256.ofNat 704) mem = target at hload
      obtain ⟨_, _, _, rdFail⟩ := vaultBlocks.vault_block_4664_taken_packed
        (by omega) (by rw [hload, hcode]; decide +kernel) (by native_decide) h
      exact vaultBlocks.vault_block_8284
        (by simp only [vaultBlocks.vault_block_4664_taken_stack, List.length_cons]; omega) rdFail
    | redeem =>
      change memLoad (UInt256.ofNat 704) mem = target at hload
      obtain ⟨_, _, _, rdFail⟩ := vaultBlocks.vault_block_5569_taken_packed
        (by omega) (by rw [hload, hcode]; decide +kernel) (by native_decide) h
      exact vaultBlocks.vault_block_8284
        (by simp only [vaultBlocks.vault_block_5569_taken_stack, List.length_cons]; omega) rdFail
  · intro aw' out σ' k' C' rdPost
    cases flow with
    | deposit =>
      exact vaultBlocks.vault_block_2805_taken_packed
        (by simp only [List.length_cons]; omega) (by decide +kernel) (by native_decide) rdPost
    | mint =>
      exact vaultBlocks.vault_block_3809_taken_packed
        (by simp only [List.length_cons]; omega) (by decide +kernel) (by native_decide) rdPost
    | withdraw =>
      exact vaultBlocks.vault_block_4698_taken_packed
        (by simp only [List.length_cons]; omega) (by decide +kernel) (by native_decide) rdPost
    | redeem =>
      exact vaultBlocks.vault_block_5603_taken_packed
        (by simp only [List.length_cons]; omega) (by decide +kernel) (by native_decide) rdPost
  · intro aw' out σ' k' C' rdPost
    cases flow with
    | deposit =>
      have rdFail := vaultBlocks.vault_block_2805_fallthrough
        (by simp only [List.length_cons]; omega) rfl rdPost
      exact vaultBlocks.vault_block_2809
        (by simp only [vaultBlocks.vault_block_2805_fallthrough_stack, List.length_cons]; omega) rdFail
    | mint =>
      have rdFail := vaultBlocks.vault_block_3809_fallthrough
        (by simp only [List.length_cons]; omega) rfl rdPost
      exact vaultBlocks.vault_block_3813
        (by simp only [vaultBlocks.vault_block_3809_fallthrough_stack, List.length_cons]; omega) rdFail
    | withdraw =>
      have rdFail := vaultBlocks.vault_block_4698_fallthrough
        (by simp only [List.length_cons]; omega) rfl rdPost
      exact vaultBlocks.vault_block_4702
        (by simp only [vaultBlocks.vault_block_4698_fallthrough_stack, List.length_cons]; omega) rdFail
    | redeem =>
      have rdFail := vaultBlocks.vault_block_5603_fallthrough
        (by simp only [List.length_cons]; omega) rfl rdPost
      exact vaultBlocks.vault_block_5607
        (by simp only [vaultBlocks.vault_block_5603_fallthrough_stack, List.length_cons]; omega) rdFail

end Benchmarks.CurveVault

