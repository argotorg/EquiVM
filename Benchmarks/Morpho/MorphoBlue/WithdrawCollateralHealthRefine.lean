import Benchmarks.Morpho.MorphoBlue.WithdrawCollateralUpdateRefine
import Benchmarks.Morpho.MorphoBlue.HealthyCallerSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

theorem CollateralTransferLocals.healthyCapture {p assets account receiver locals}
    (hl : CollateralTransferLocals p assets account receiver locals) (base : Nat) (word : UInt256) :
    CollateralTransferLocals p assets account receiver (healthyCapturedLocals locals base word) := by
  unfold healthyCapturedLocals
  split
  · exact hl
  · exact hl.insert _ _ (by decide) (by decide)

theorem collateralTransferHealthy_args {p assets account receiver locals}
    (hl : CollateralTransferLocals p assets account receiver locals) (imms : Store) (evm : EVM.State) :
    evalExprs? config { contract := contract, locals := locals, immutables := imms } evm
      [.var "marketParams", .var "id", .var "onBehalf"] =
      .ok [p.value, .fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE p.id),
        .address (AccountAddress.ofNat account.toNat)] := by
  simp only [evalExprs?, hl.evalParams imms evm, hl.evalId imms evm, hl.evalAccount imms evm,
    pure, bind, EvalResult.bind]
theorem CollateralTransferLocals.evalPositionBorrowShares {p assets account receiver locals}
    (hl : CollateralTransferLocals p assets account receiver locals) (imms : Store) (evm : EVM.State)
    (ha : account.toNat < EVM.addressModulus) :
    evalExpr? config { contract := contract, locals := locals, immutables := imms } evm
      (.storage ⟨"position", [.mindex (.var "id"), .mindex (.var "onBehalf"), .field "borrowShares"]⟩) =
      .ok (.int (Int.ofNat (positionFieldWord evm.accountMap evm.executionEnv p.id account 1).toNat)) :=
  evalMorphoPositionField evm locals imms _ _ p.id account 1 hl.position
    (hl.evalId imms evm) (hl.evalAccount imms evm) ha

inductive WithdrawCollateralHealthRefines (v : MorphoImmutables) (ee : ExecutionEnv) (g : Sat256) (s0 : State)
    (p : MarketParamsWords) (assets account receiver : UInt256)
    (locals imms : Store) (evm : EVM.State) (mem : ByteArray) (fp : UInt256) (R : List UInt256) : Prop where
  | reverted : ExecBlock config { contract := contract, locals := locals, immutables := imms }
      evm (withdrawCollateralTransition.body.drop 14) .reverted → RDrev (deployedRuntime v) g s0 →
      WithdrawCollateralHealthRefines v ee g s0 p assets account receiver locals imms evm mem fp R
  | ok {locals' evm' σ' mem' fp' aw' out' k' C'} (z : Bool) :
      StateBlock config { contract := contract, locals := locals, immutables := imms }
        evm (withdrawCollateralTransition.body.drop 14) { contract := contract, locals := locals', immutables := imms }
        evm' (withdrawCollateralTransition.body.drop 16) → CollateralTransferLocals p assets account receiver locals' →
      locals'.get? "__memory" = some (.int (Int.ofNat (fp'.toNat + 64))) →
      locals'.get? "__c4" = some (.bool z) → SourceState s0 ee σ' evm' → MorphoHeap mem' fp' 320 →
      HeapAdvance mem fp mem' fp' (healthyMemoryCost p account evm) →
      RD (deployedRuntime v) ee g s0 (UInt256.ofNat 5693)
        ((if z then UInt256.ofNat 1 else UInt256.ofNat 0) :: UInt256.ofNat 5701 :: withdrawCollateralHealthTail p.id assets account receiver R)
        mem' aw' out' σ' k' C' → WithdrawCollateralHealthRefines v ee g s0 p assets account receiver locals imms evm mem fp R

theorem morphoWithdrawCollateralHealthRefine {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256}
    {s0 evm : State} {aw fp assets account receiver : UInt256} {out mem : ByteArray}
    {σ : AccountMap} {k C : Nat} {R : List UInt256} (p : MarketParamsWords)
    (locals imms : Store) (hstack : R.length + 50 ≤ 1024) (ha : account.toNat < EVM.addressModulus) (hc : p.Canonical)
    (hl : CollateralTransferLocals p assets account receiver locals) (hs : SourceState s0 ee σ evm)
    (hm : MorphoHeap mem fp 352) (hmem : locals.get? "__memory" = some (.int (Int.ofNat (fp.toNat + 64))))
    (hparams : p.InMemory (UInt256.ofNat 128) mem) (hsize : 288 ≤ mem.size) (hbefore : 288 ≤ fp.toNat)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 5686)
      (withdrawCollateralUpdateTail p.id assets account receiver R)
      mem aw out σ k C) :
    WithdrawCollateralHealthRefines v ee g s0 p assets account receiver locals imms evm mem fp R := by
  have rd0 := morphoBlocks.morpho_block_5686 (immWords := wordsOf (immStore v))
    (by change R.length + 6 + 10 ≤ 1024; omega)
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) h
  let word := positionFieldWord evm.accountMap evm.executionEnv p.id account 1
  let l1 := healthyCapturedLocals locals (fp.toNat + 64) word
  have hl1 : CollateralTransferLocals p assets account receiver l1 := hl.healthyCapture _ _
  have hecap := healthyCaptureMemory (hl.evalPositionBorrowShares imms evm ha) hmem
  have ab : StateBlock config { contract := contract, locals := locals, immutables := imms }
      evm (withdrawCollateralTransition.body.drop 14) { contract := contract, locals := l1, immutables := imms }
      evm (withdrawCollateralTransition.body.drop 15) := StateBlock.start.step hecap
  have hm1 : l1.get? "__memory" = some (.int (Int.ofNat (fp.toNat + 64 + healthyMemoryCost p account evm))) :=
    healthyCapturedLocals_get word hmem
  have heargs := collateralTransferHealthy_args hl1 imms evm
  have hf := morphoHealthyFunctionRefine (v := v) p imms
    (by change R.length + 11 + 33 ≤ 1024; omega) ha hc hs hm (by decide) hparams hsize hbefore
    (by rw [morphoPatchedValidJumps v]; jump_dest) rd0
  cases hf with
  | reverted he hr =>
    exact .reverted (ab.reverts (internalCallFunctionRevert (callee := healthyFunction) heargs rfl rfl he)) hr
  | @ok frame' evm' σ' mem' fp' aw' out' k' C' z he hs' hm' had hr =>
    have hecall := internalCallFunctionReturn (callee := healthyFunction) (name := "_isHealthy") (retVar := "__c4") heargs rfl rfl he
    refine .ok z (ab.step hecall) (hl1.insert _ _ (by decide) (by decide)) ?_
      (store_get_self _ _ _) hs' hm' had hr
    rw [store_get_ne _ _ (by decide), hm1]
    congr 3
    have hh := had.cursor
    omega

end Benchmarks.Morpho.MorphoBlue
