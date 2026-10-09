import Benchmarks.Morpho.MorphoBlue.BorrowMarketRefine
import Benchmarks.Morpho.MorphoBlue.HealthyCallerSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

inductive BorrowHealthRefines (v : MorphoImmutables) (ee : ExecutionEnv) (g : Sat256) (s0 : State)
    (p : MarketParamsWords) (assets shares account receiver : UInt256)
    (locals imms : Store) (evm : EVM.State) (mem : ByteArray) (fp : UInt256) (R : List UInt256) : Prop where
  | reverted : ExecBlock config { contract := contract, locals := locals, immutables := imms }
      evm (borrowTransition.body.drop 20) .reverted → RDrev (deployedRuntime v) g s0 →
      BorrowHealthRefines v ee g s0 p assets shares account receiver locals imms evm mem fp R
  | ok {locals' evm' σ' mem' fp' aw' out' k' C'} (z : Bool) :
      StateBlock config { contract := contract, locals := locals, immutables := imms }
        evm (borrowTransition.body.drop 20) { contract := contract, locals := locals', immutables := imms }
        evm' (borrowTransition.body.drop 22) → MarketTransferLocals p assets shares account receiver locals' →
      locals'.get? "__memory" = some (.int (Int.ofNat (fp'.toNat + 128))) →
      locals'.get? "__c9" = some (.bool z) → SourceState s0 ee σ' evm' → MorphoHeap mem' fp' 192 →
      HeapAdvance mem fp mem' fp' (healthyMemoryCost p account evm) →
      RD (deployedRuntime v) ee g s0 (UInt256.ofNat 8794)
        ((if z then UInt256.ofNat 1 else UInt256.ofNat 0) :: borrowHealthTail p.id assets shares account receiver R)
        mem' aw' out' σ' k' C' → BorrowHealthRefines v ee g s0 p assets shares account receiver locals imms evm mem fp R

theorem morphoBorrowHealthRefine {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256}
    {s0 evm : State} {aw fp assets shares account receiver : UInt256} {out mem : ByteArray}
    {σ : AccountMap} {k C : Nat} {R : List UInt256} (p : MarketParamsWords)
    (locals imms : Store) (hstack : R.length + 50 ≤ 1024) (ha : account.toNat < EVM.addressModulus) (hc : p.Canonical)
    (hl : MarketTransferLocals p assets shares account receiver locals) (hs : SourceState s0 ee σ evm)
    (hm : MorphoHeap mem fp 224) (hmem : locals.get? "__memory" = some (.int (Int.ofNat (fp.toNat + 128))))
    (hparams : p.InMemory (UInt256.ofNat 128) mem) (hsize : 288 ≤ mem.size) (hbefore : 288 ≤ fp.toNat)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 13948)
      ([UInt256.ofNat 128, p.id, account, UInt256.ofNat 8794] ++ borrowHealthTail p.id assets shares account receiver R)
      mem aw out σ k C) :
    BorrowHealthRefines v ee g s0 p assets shares account receiver locals imms evm mem fp R := by
  let word := positionFieldWord evm.accountMap evm.executionEnv p.id account 1
  let l1 := healthyCapturedLocals locals (fp.toNat + 128) word
  have hl1 : MarketTransferLocals p assets shares account receiver l1 := hl.healthyCapture _ _
  have hecap := healthyCaptureMemory (hl.evalPositionBorrowShares imms evm ha) hmem
  have ab : StateBlock config { contract := contract, locals := locals, immutables := imms }
      evm (borrowTransition.body.drop 20) { contract := contract, locals := l1, immutables := imms }
      evm (borrowTransition.body.drop 21) := StateBlock.start.step hecap
  have hm1 : l1.get? "__memory" = some (.int (Int.ofNat (fp.toNat + 128 + healthyMemoryCost p account evm))) :=
    healthyCapturedLocals_get word hmem
  have heargs := marketTransferHealthy_args hl1 imms evm
  have hf := morphoHealthyFunctionRefine (v := v) p imms
    (by change R.length + 13 + 33 ≤ 1024; omega) ha hc hs hm (by decide) hparams hsize hbefore
    (by rw [morphoPatchedValidJumps v]; jump_dest) h
  cases hf with
  | reverted he hr =>
    exact .reverted (ab.reverts (internalCallFunctionRevert (callee := healthyFunction) heargs rfl rfl he)) hr
  | @ok frame' evm' σ' mem' fp' aw' out' k' C' z he hs' hm' had hr =>
    have hecall := internalCallFunctionReturn (callee := healthyFunction) (name := "_isHealthy") (retVar := "__c9") heargs rfl rfl he
    refine .ok z (ab.step hecall) (hl1.insert _ _ (by decide) (by decide)) ?_
      (store_get_self _ _ _) hs' hm' had hr
    rw [store_get_ne _ _ (by decide), hm1]
    congr 3
    have hh := had.cursor
    omega

end Benchmarks.Morpho.MorphoBlue
