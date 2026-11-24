import Benchmarks.CurveVault.VoidCalls
import Benchmarks.CurveVault.HookLayout
import Benchmarks.CurveVault.RuntimeBlocks_011
import Benchmarks.CurveVault.RuntimeBlocks_013
import Benchmarks.CurveVault.RuntimeBlocks_014
import Benchmarks.CurveVault.RuntimeBlocks_016
import Benchmarks.CurveVault.RuntimeBlocks_017
import Benchmarks.CurveVault.RuntimeBlocks_019
import Benchmarks.CurveVault.RuntimeBlocks_031

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch Reasoning.VyperCalls
namespace Benchmarks.CurveVault

theorem vaultHookCall (flow : VaultFlow) {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {target amount : UInt256} {R : List UInt256} {locals : Store} {retVar : Ident} {arg : Expr}
    (hs : SourceState s0 I σ evm) (hsize : 704 ≤ mem.size)
    (htarget : locals.get? "controller" = some (.address (AccountAddress.ofUInt256 target)))
    (harg : evalExpr? config {contract := contract, locals := locals} evm arg = .ok (.int (Int.ofNat amount.toNat)))
    (hload : memLoad (UInt256.ofNat flow.controllerOffset) (vaultHookCachedMemory flow I σ mem) = target)
    (hamount : vaultHookAmount flow I mem = amount) (hstack : R.length + 8 ≤ 1024)
    (h : RD fork vaultBytecode I g s0 (UInt256.ofNat flow.hookEntry) R mem aw rdata σ k C) :
    (∃ (evm' : State) (σ' : AccountMap) (out : ByteArray) (aw' : UInt256) (k' C' : Nat),
      ExecBlock fork config {contract := contract, locals := locals} evm
        [.require (.binary .gt (.extCodeSize (.var "controller")) (.intLit 0)),
          .externalCall (.var "controller") flow.hookName (.intLit 0) [arg] retVar]
        (.ok {contract := contract, locals := locals.insert retVar (collapseReturns [])} evm') ∧
      SourceState s0 I σ' evm' ∧ RD fork vaultBytecode I g s0 (UInt256.ofNat flow.hookNext)
        (target :: R) (vaultHookCallMemory flow I σ mem amount) aw' out σ' k' C') ∨
    (ExecBlock fork config {contract := contract, locals := locals} evm
      [.require (.binary .gt (.extCodeSize (.var "controller")) (.intLit 0)),
        .externalCall (.var "controller") flow.hookName (.intLit 0) [arg] retVar] .reverted ∧ RDrev fork vaultBytecode g s0) := by
  have hr : evalExpr? config {contract := contract, locals := locals} evm (.var "controller") =
      .ok (.address (AccountAddress.ofUInt256 target)) := by
    rw [evalExpr?]; simp only [htarget, EvalResult.ofOption]
  have hloaded : vaultHookLoadedValue flow I σ mem = amount :=
    (vaultHookLoadedValue_eq flow I σ mem hsize).trans hamount
  have hcd := vaultHookCallMemory_encode flow I σ mem amount
  apply checkedVoidCallBridge (pc := UInt256.ofNat flow.hookCall)
    (argVals := [.int (Int.ofNat amount.toNat)]) (R := target :: R) (nextStack := target :: R)
    (inOffset := UInt256.ofNat (flow.callOffset + 28)) (inSize := UInt256.ofNat 36)
    (outOffset := UInt256.ofNat flow.callOffset) hs hr (evalExprs?_singleton harg)
    (by simpa only [ulit_toNat' _ (show flow.callOffset + 28 < UInt256.size by cases flow <;> decide +kernel)] using hcd)
    (by intro out; cases flow <;> rfl) (by cases flow <;> native_decide) (by decide +kernel)
    (by simp only [List.length_cons]; omega)
  · intro hcode
    cases flow with
    | deposit =>
      change memLoad (UInt256.ofNat 608) (vaultHookCachedMemory .deposit I σ mem) = target at hload
      obtain ⟨aw0, k0, C0, rdReady⟩ := vaultBlocks.vault_block_2666_fallthrough_packed
        (by omega) (by
          change UInt256.isZero (extCodeSizeWord σ
            (memLoad (UInt256.ofNat 608) (vaultHookCachedMemory .deposit I σ mem))) = _
          rw [hload]; exact isZero_eq_zero_of_ne hcode) h
      obtain ⟨aw1, k1, C1, rdCall⟩ := vaultBlocks.vault_block_2694_packed (by omega) rdReady
      change RD fork vaultBytecode I g s0 (UInt256.ofNat VaultFlow.deposit.hookCall)
        (_ :: memLoad (UInt256.ofNat 608) (vaultHookCachedMemory .deposit I σ mem) :: ⟨0⟩ ::
          UInt256.ofNat 732 :: UInt256.ofNat 36 :: UInt256.ofNat 704 :: ⟨0⟩ ::
          memLoad (UInt256.ofNat 608) (vaultHookCachedMemory .deposit I σ mem) :: R)
        (vaultHookCallMemory .deposit I σ mem (vaultHookLoadedValue .deposit I σ mem)) aw1 rdata σ k1 C1 at rdCall
      rw [hload, hloaded] at rdCall
      exact ⟨_, aw1, k1, C1, rdCall⟩
    | mint =>
      change memLoad (UInt256.ofNat 608) (vaultHookCachedMemory .mint I σ mem) = target at hload
      obtain ⟨aw0, k0, C0, rdReady⟩ := vaultBlocks.vault_block_3669_fallthrough_packed
        (by omega) (by
          change UInt256.isZero (extCodeSizeWord σ
            (memLoad (UInt256.ofNat 608) (vaultHookCachedMemory .mint I σ mem))) = _
          rw [hload]; exact isZero_eq_zero_of_ne hcode) h
      obtain ⟨aw1, k1, C1, rdCall⟩ := vaultBlocks.vault_block_3698_packed (by omega) rdReady
      change RD fork vaultBytecode I g s0 (UInt256.ofNat VaultFlow.mint.hookCall)
        (_ :: memLoad (UInt256.ofNat 608) (vaultHookCachedMemory .mint I σ mem) :: ⟨0⟩ ::
          UInt256.ofNat 732 :: UInt256.ofNat 36 :: UInt256.ofNat 704 :: ⟨0⟩ ::
          memLoad (UInt256.ofNat 608) (vaultHookCachedMemory .mint I σ mem) :: R)
        (vaultHookCallMemory .mint I σ mem (vaultHookLoadedValue .mint I σ mem)) aw1 rdata σ k1 C1 at rdCall
      rw [hload, hloaded] at rdCall
      exact ⟨_, aw1, k1, C1, rdCall⟩
    | withdraw =>
      change memLoad (UInt256.ofNat 704) (vaultHookCachedMemory .withdraw I σ mem) = target at hload
      obtain ⟨aw0, k0, C0, rdReady⟩ := vaultBlocks.vault_block_4578_fallthrough_packed
        (by omega) (by
          change UInt256.isZero (extCodeSizeWord σ
            (memLoad (UInt256.ofNat 704) (vaultHookCachedMemory .withdraw I σ mem))) = _
          rw [hload]; exact isZero_eq_zero_of_ne hcode) h
      obtain ⟨aw1, k1, C1, rdCall⟩ := vaultBlocks.vault_block_4606_packed (by omega) rdReady
      change RD fork vaultBytecode I g s0 (UInt256.ofNat VaultFlow.withdraw.hookCall)
        (_ :: memLoad (UInt256.ofNat 704) (vaultHookCachedMemory .withdraw I σ mem) :: ⟨0⟩ ::
          UInt256.ofNat 764 :: UInt256.ofNat 36 :: UInt256.ofNat 736 :: ⟨0⟩ ::
          memLoad (UInt256.ofNat 704) (vaultHookCachedMemory .withdraw I σ mem) :: R)
        (vaultHookCallMemory .withdraw I σ mem (vaultHookLoadedValue .withdraw I σ mem)) aw1 rdata σ k1 C1 at rdCall
      rw [hload, hloaded] at rdCall
      exact ⟨_, aw1, k1, C1, rdCall⟩
    | redeem =>
      change memLoad (UInt256.ofNat 704) (vaultHookCachedMemory .redeem I σ mem) = target at hload
      obtain ⟨aw0, k0, C0, rdReady⟩ := vaultBlocks.vault_block_5474_fallthrough_packed
        (by omega) (by
          change UInt256.isZero (extCodeSizeWord σ
            (memLoad (UInt256.ofNat 704) (vaultHookCachedMemory .redeem I σ mem))) = _
          rw [hload]; exact isZero_eq_zero_of_ne hcode) h
      obtain ⟨aw1, k1, C1, rdCall⟩ := vaultBlocks.vault_block_5510_packed (by omega) rdReady
      change RD fork vaultBytecode I g s0 (UInt256.ofNat VaultFlow.redeem.hookCall)
        (_ :: memLoad (UInt256.ofNat 704) (vaultHookCachedMemory .redeem I σ mem) :: ⟨0⟩ ::
          UInt256.ofNat 764 :: UInt256.ofNat 36 :: UInt256.ofNat 736 :: ⟨0⟩ ::
          memLoad (UInt256.ofNat 704) (vaultHookCachedMemory .redeem I σ mem) :: R)
        (vaultHookCallMemory .redeem I σ mem (vaultHookLoadedValue .redeem I σ mem)) aw1 rdata σ k1 C1 at rdCall
      rw [hload, hloaded] at rdCall
      exact ⟨_, aw1, k1, C1, rdCall⟩
  · intro hcode
    cases flow with
    | deposit =>
      change memLoad (UInt256.ofNat 608) (vaultHookCachedMemory .deposit I σ mem) = target at hload
      obtain ⟨_, _, _, rdFail⟩ := vaultBlocks.vault_block_2666_taken_packed
        (by omega) (by
          change UInt256.isZero (extCodeSizeWord σ
            (memLoad (UInt256.ofNat 608) (vaultHookCachedMemory .deposit I σ mem))) ≠ _
          rw [hload, hcode]; decide +kernel) (by native_decide) h
      exact vaultBlocks.vault_block_8284
        (by simp only [vaultBlocks.vault_block_2666_taken_stack, List.length_cons]; omega) rdFail
    | mint =>
      change memLoad (UInt256.ofNat 608) (vaultHookCachedMemory .mint I σ mem) = target at hload
      obtain ⟨_, _, _, rdFail⟩ := vaultBlocks.vault_block_3669_taken_packed
        (by omega) (by
          change UInt256.isZero (extCodeSizeWord σ
            (memLoad (UInt256.ofNat 608) (vaultHookCachedMemory .mint I σ mem))) ≠ _
          rw [hload, hcode]; decide +kernel) (by native_decide) h
      exact vaultBlocks.vault_block_8284
        (by simp only [vaultBlocks.vault_block_3669_taken_stack, List.length_cons]; omega) rdFail
    | withdraw =>
      change memLoad (UInt256.ofNat 704) (vaultHookCachedMemory .withdraw I σ mem) = target at hload
      obtain ⟨_, _, _, rdFail⟩ := vaultBlocks.vault_block_4578_taken_packed
        (by omega) (by
          change UInt256.isZero (extCodeSizeWord σ
            (memLoad (UInt256.ofNat 704) (vaultHookCachedMemory .withdraw I σ mem))) ≠ _
          rw [hload, hcode]; decide +kernel) (by native_decide) h
      exact vaultBlocks.vault_block_8284
        (by simp only [vaultBlocks.vault_block_4578_taken_stack, List.length_cons]; omega) rdFail
    | redeem =>
      change memLoad (UInt256.ofNat 704) (vaultHookCachedMemory .redeem I σ mem) = target at hload
      obtain ⟨_, _, _, rdFail⟩ := vaultBlocks.vault_block_5474_taken_packed
        (by omega) (by
          change UInt256.isZero (extCodeSizeWord σ
            (memLoad (UInt256.ofNat 704) (vaultHookCachedMemory .redeem I σ mem))) ≠ _
          rw [hload, hcode]; decide +kernel) (by native_decide) h
      exact vaultBlocks.vault_block_8284
        (by simp only [vaultBlocks.vault_block_5474_taken_stack, List.length_cons]; omega) rdFail
  · intro aw' out σ' k' C' rdPost
    cases flow with
    | deposit =>
      exact vaultBlocks.vault_block_2707_taken_packed
        (by simp only [List.length_cons]; omega) (by decide +kernel) (by native_decide) rdPost
    | mint =>
      exact vaultBlocks.vault_block_3711_taken_packed
        (by simp only [List.length_cons]; omega) (by decide +kernel) (by native_decide) rdPost
    | withdraw =>
      exact vaultBlocks.vault_block_4619_taken_packed
        (by simp only [List.length_cons]; omega) (by decide +kernel) (by native_decide) rdPost
    | redeem =>
      exact vaultBlocks.vault_block_5523_taken_packed
        (by simp only [List.length_cons]; omega) (by decide +kernel) (by native_decide) rdPost
  · intro aw' out σ' k' C' rdPost
    cases flow with
    | deposit =>
      have rdFail := vaultBlocks.vault_block_2707_fallthrough
        (by simp only [List.length_cons]; omega) rfl rdPost
      exact vaultBlocks.vault_block_2711
        (by simp only [vaultBlocks.vault_block_2707_fallthrough_stack, List.length_cons]; omega) rdFail
    | mint =>
      have rdFail := vaultBlocks.vault_block_3711_fallthrough
        (by simp only [List.length_cons]; omega) rfl rdPost
      exact vaultBlocks.vault_block_3715
        (by simp only [vaultBlocks.vault_block_3711_fallthrough_stack, List.length_cons]; omega) rdFail
    | withdraw =>
      have rdFail := vaultBlocks.vault_block_4619_fallthrough
        (by simp only [List.length_cons]; omega) rfl rdPost
      exact vaultBlocks.vault_block_4623
        (by simp only [vaultBlocks.vault_block_4619_fallthrough_stack, List.length_cons]; omega) rdFail
    | redeem =>
      have rdFail := vaultBlocks.vault_block_5523_fallthrough
        (by simp only [List.length_cons]; omega) rfl rdPost
      exact vaultBlocks.vault_block_5527
        (by simp only [vaultBlocks.vault_block_5523_fallthrough_stack, List.length_cons]; omega) rdFail

end Benchmarks.CurveVault

