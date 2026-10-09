import Benchmarks.Morpho.MorphoBlue.SupplyAccrueRefine
import Benchmarks.Morpho.MorphoBlue.WithdrawCollateralGuards
import Benchmarks.Morpho.MorphoBlue.WithdrawCollateralSourceStart

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

inductive WithdrawCollateralAccrueRefines (v : MorphoImmutables) (ee : ExecutionEnv) (g : Sat256) (s0 : State)
    (p : MarketParamsWords) (assets account receiver : UInt256)
    (locals imms : Store) (evm : EVM.State) (R : List UInt256) : Prop where
  | reverted : ExecBlock config { contract := contract, locals := locals, immutables := imms }
      evm (withdrawCollateralTransition.body.drop 10) .reverted → RDrev (deployedRuntime v) g s0 →
      WithdrawCollateralAccrueRefines v ee g s0 p assets account receiver locals imms evm R
  | static : ExecBlock config { contract := contract, locals := locals, immutables := imms }
      evm (withdrawCollateralTransition.body.drop 10) .staticViolation → RDstatic (deployedRuntime v) g s0 →
      WithdrawCollateralAccrueRefines v ee g s0 p assets account receiver locals imms evm R
  | ok {locals' evm' σ' mem' fp' aw' out' k' C'} :
      StateBlock config { contract := contract, locals := locals, immutables := imms }
        evm (withdrawCollateralTransition.body.drop 10) { contract := contract, locals := locals', immutables := imms }
        evm' (withdrawCollateralTransition.body.drop 12) →
      CollateralTransferLocals p assets account receiver locals' →
      locals'.get? "__memory" = some (.int (Int.ofNat (fp'.toNat + 128))) →
      SourceState s0 ee σ' evm' → MorphoHeap mem' fp' 416 → 544 ≤ fp'.toNat →
      544 ≤ mem'.size → p.InMemory (UInt256.ofNat 128) mem' →
      memLoad (UInt256.ofNat 96) mem' = UInt256.ofNat 0 →
      RD (deployedRuntime v) ee g s0 (UInt256.ofNat 5630)
        (withdrawCollateralGuardTail p.id assets account receiver R) mem' aw' out' σ' k' C' →
      WithdrawCollateralAccrueRefines v ee g s0 p assets account receiver locals imms evm R

theorem morphoWithdrawCollateralAccrueRefine {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256}
    {s0 evm : State} {aw assets account receiver : UInt256} {out : ByteArray}
    {σ : AccountMap} {k C : Nat} {R : List UInt256} (p : MarketParamsWords)
    (locals imms : Store) (hstack : R.length + 58 ≤ 1024) (hc : p.Canonical)
    (hl : CollateralTransferLocals p assets account receiver locals)
    (ha : locals.get? "__accrued" = some (.bool (accrueActive p evm)))
    (hs : SourceState s0 ee σ evm)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 5620)
      (withdrawCollateralGuardTail p.id assets account receiver R) (withdrawCollateralGuardMem p ee account) aw out σ k C) :
    WithdrawCollateralAccrueRefines v ee g s0 p assets account receiver locals imms evm R := by
  have rd1 := morphoBlocks.morpho_block_5620 (immWords := wordsOf (immStore v))
    (by simp only [withdrawCollateralGuardTail, List.length_append, List.length_cons, List.length_nil, List.append]; omega)
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) h
  have hm := (withdrawCollateralGuardHeap p ee account).1
  have hf := morphoAccrueFunctionRefineWithMemory (v := v) p imms hc
    (by simp only [withdrawCollateralGuardTail, List.length_append, List.length_cons, List.length_nil, List.append]; omega) hs
    (createMarketHeap_morpho hm (by decide) 640 (by decide) (lt_usize _ (by decide)))
    (by decide) hm.params (by decide) (by rw [hm.size]; decide) (by decide)
    (by rw [morphoPatchedValidJumps v]; jump_dest) rd1
  cases hf with
  | reverted he hr =>
    exact .reverted (ExecBlock.consRevert (morphoAccrueInternalRevert p locals imms evm _ _ "__c2"
      (hl.evalParams imms evm) (hl.evalId imms evm) he)) hr
  | static he hr =>
    exact .static (ExecBlock.consStatic (morphoAccrueInternalStatic p locals imms evm _ _ "__c2"
      (hl.evalParams imms evm) (hl.evalId imms evm) he)) hr
  | @ok frame' evm' value σ' mem' fp' aw' out' k' C' he hv hs' hm' had hr =>
    have he1 := morphoAccrueInternalOk p locals imms evm evm' frame' value _ _ "__c2"
      (hl.evalParams imms evm) (hl.evalId imms evm) he
    have hecall : ExecStmt config { contract := contract, locals := locals, immutables := imms }
        evm withdrawCollateralTransition.body[10]!
        (.ok { contract := contract, locals := locals.insert "__c2" .unit, immutables := imms } evm') := by
      rcases hv with rfl | rfl <;> exact he1
    have hl1 := hl.insert "__c2" .unit (by decide) (by decide)
    have hac : (locals.insert "__c2" .unit).get? "__accrued" = some (.bool (accrueActive p evm)) := by
      rw [store_get_ne _ _ (by decide)]; exact ha
    have he2 := morphoAfterAccrueCapturedCall p 672 evm evm' _ imms hl1.toMarketLocals hac
    have hadc : fp'.toNat = 544 + accrueMemoryCost p evm evm' := had.cursor
    have heq : 672 + accrueMemoryCost p evm evm' = fp'.toNat + 128 := by omega
    rw [heq] at he2
    refine .ok ((StateBlock.start.step hecall).step he2)
      (hl1.insert "__memory" _ (by decide) (by decide)) (store_get_self _ _ _) hs' hm'
      (by omega) (by have hz := had.preserves.size; rw [hm.size] at hz; exact hz) ?_ ?_ hr
    · exact hm.params.ofPrefix had.preserves (by decide) (by decide) (by rw [hm.size]; decide) (by decide)
    · rw [memoryPrefix_memLoad had.preserves _ (by decide) (by decide) (by rw [hm.size]; decide)]
      exact withdrawCollateralGuardMem_zero96 p ee account

end Benchmarks.Morpho.MorphoBlue
