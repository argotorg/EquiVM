import Benchmarks.UniswapV4PoolManager.Storage
import Benchmarks.UniswapV4PoolManager.EntryTrace
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_035

/-! Owner authorization in source and bytecode. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables

namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 2000000

def ownerAuthorized (evm : EVM.State) : Prop :=
  accountWord evm.executionEnv.source =
    UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩) solcAddrMask

instance (evm : EVM.State) : Decidable (ownerAuthorized evm) := inferInstanceAs (Decidable (_ = _))

theorem ownerGuard_eval {f : Frame} {evm : EVM.State}
    (hf : f.contract = contract) (hbase : f.locals.get? "owner" = none) :
    evalExpr? config f evm (.binary .eq (.env .caller) (.storage {base := "owner"})) =
      .ok (.bool (decide (ownerAuthorized evm))) := by
  have hread := addressScalarRead (evm := evm) hf hbase (slot := ⟨0⟩) (by decide +kernel) rfl
  have he := evalEqAddress (rhs := .storage {base := "owner"})
    (by simp only [evalExpr?, envValue, pure] : evalExpr? config f evm (.env .caller) = .ok (.address evm.executionEnv.source)) hread
  simpa only [accountWord_eq_iff _ _ (solcAddrMask_result_canonical _)] using he

theorem ownerGuardReverts (evm : EVM.State) (locals imms : Store) (rest : List Stmt)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < calldataLimit)
    (hbase : locals.get? "owner" = none) (hauth : ¬ ownerAuthorized evm) :
    ExecTransitionBody config contract evm locals
      (nonpayableCalldataPrefix ++ .require (.binary .eq (.env .caller) (.storage {base := "owner"})) :: rest)
      .reverted imms := by
  apply ExecFuncBody.execBlockRevert
  apply nonpayableCalldataBlock hwv hhi
  apply ExecBlock.consRevert
  apply ExecStmt.requireFalse
  exact (ownerGuard_eval rfl ((store_get_ne locals _ (by decide : ("__calldata" == "owner") = false)).trans hbase)).trans
    (by rw [decide_eq_false hauth])

theorem requireAuthorizedPass {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw ret a b : UInt256} {σ : AccountMap} {k C : Nat}
    {R : List UInt256} (v : PoolManagerImmutables)
    (hstack : R.length + 3 ≤ 1024) (hauth : a = b)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) I g s0 ⟨12295⟩
      (UInt256.eq a b :: ret :: R) mem aw rdata σ k C) :
    ∃ k' C', RD (deployedRuntime v) I g s0 ret R mem aw rdata σ k' C' := by
  have hcond : UInt256.isZero (UInt256.eq a b) = ⟨0⟩ := by rw [hauth, uInt256_eq_self]; decide
  have rdReturn := poolManagerBlocks.poolManager_block_12295_fallthrough
    (by simpa only [List.length_cons] using hstack) hcond h
  have rdDone := poolManagerBlocks.poolManager_block_12301 (by omega) hret rdReturn
  exact ⟨_, _, rdDone⟩

theorem requireAuthorizedReverts {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw a b : UInt256} {σ : AccountMap} {k C : Nat}
    {R : List UInt256} (v : PoolManagerImmutables)
    (hstack : R.length + 5 ≤ 1024) (hauth : a ≠ b)
    (h : RD (deployedRuntime v) I g s0 ⟨12295⟩
      (UInt256.eq a b :: R) mem aw rdata σ k C) :
    RDrev (deployedRuntime v) g s0 := by
  have heq : UInt256.eq a b = ⟨0⟩ := uInt256_eq_zero_of_ne (fun h => hauth (uInt256_eq_one_eq h))
  have hcond : UInt256.isZero (UInt256.eq a b) ≠ ⟨0⟩ := by rw [heq]; decide
  have hjump : (D_J (deployedRuntime v) 0).contains (UInt256.ofNat 12302) = true := by
    rw [deployedRuntime_jumps v]; jump_dest
  have rdRevert := poolManagerBlocks.poolManager_block_12295_taken (by omega) hcond hjump h
  exact poolManagerBlocks.poolManager_block_12302 hstack rdRevert

end Benchmarks.UniswapV4PoolManager
