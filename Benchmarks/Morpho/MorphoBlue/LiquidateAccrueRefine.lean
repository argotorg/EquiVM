import Benchmarks.Morpho.MorphoBlue.SupplyAccrueRefine
import Benchmarks.Morpho.MorphoBlue.LiquidateGuards
import Benchmarks.Morpho.MorphoBlue.LiquidateSourceStart

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

inductive LiquidateAccrueRefines (v : MorphoImmutables) (ee : ExecutionEnv) (g : Sat256) (s0 : State)
    (p : MarketParamsWords) (account seized shares srcOff len : UInt256) (data : ByteArray)
    (locals imms : Store) (evm : EVM.State) (R : List UInt256) : Prop where
  | reverted : ExecBlock config { contract := contract, locals := locals, immutables := imms }
      evm (liquidateTransition.body.drop 8) .reverted → RDrev (deployedRuntime v) g s0 →
      LiquidateAccrueRefines v ee g s0 p account seized shares srcOff len data locals imms evm R
  | static : ExecBlock config { contract := contract, locals := locals, immutables := imms }
      evm (liquidateTransition.body.drop 8) .staticViolation → RDstatic (deployedRuntime v) g s0 →
      LiquidateAccrueRefines v ee g s0 p account seized shares srcOff len data locals imms evm R
  | ok {locals' evm' σ' mem' fp' aw' out' k' C'} :
      StateBlock config { contract := contract, locals := locals, immutables := imms }
        evm (liquidateTransition.body.drop 8) { contract := contract, locals := locals', immutables := imms }
        evm' (liquidateTransition.body.drop 10) →
      LiquidateLocals p account seized shares data locals' →
      locals'.get? "__memory" = some (.int (Int.ofNat (fp'.toNat + 352))) →
      SourceState s0 ee σ' evm' → MorphoHeap mem' fp' 928 → 416 ≤ fp'.toNat →
      416 ≤ mem'.size → p.InMemory (UInt256.ofNat 128) mem' →
      memLoad (UInt256.ofNat 96) mem' = UInt256.ofNat 0 →
      RD (deployedRuntime v) ee g s0 (UInt256.ofNat 1470)
        (liquidateGuardTail p.id seized shares srcOff len R) mem' aw' out' σ' k' C' →
      LiquidateAccrueRefines v ee g s0 p account seized shares srcOff len data locals imms evm R

theorem morphoLiquidateAccrueRefine {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256}
    {s0 evm : State} {aw account seized shares srcOff len : UInt256} {out data : ByteArray}
    {σ : AccountMap} {k C : Nat} {R : List UInt256} (p : MarketParamsWords)
    (locals imms : Store) (hstack : R.length + 58 ≤ 1024) (hc : p.Canonical)
    (hl : LiquidateLocals p account seized shares data locals)
    (ha : locals.get? "__accrued" = some (.bool (accrueActive p evm)))
    (hs : SourceState s0 ee σ evm)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 1460)
      (liquidateGuardTail p.id seized shares srcOff len R) (supplyInputMem p) aw out σ k C) :
    LiquidateAccrueRefines v ee g s0 p account seized shares srcOff len data locals imms evm R := by
  have rd1 := morphoBlocks.morpho_block_1460 (immWords := wordsOf (immStore v))
    (by simp only [liquidateGuardTail, List.length_append, List.length_cons, List.length_nil, List.append]; omega)
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) h
  have hm := (supplyInputHeap p).1
  have hf := morphoAccrueFunctionRefineWithMemory (v := v) p imms hc
    (by simp only [liquidateGuardTail, List.length_append, List.length_cons, List.length_nil, List.append]; omega) hs
    (createMarketHeap_morpho hm (by decide) 1152 (by decide) (lt_usize _ (by decide)))
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
        evm liquidateTransition.body[8]!
        (.ok { contract := contract, locals := locals.insert "__c2" .unit, immutables := imms } evm') := by
      rcases hv with rfl | rfl <;> exact he1
    have hl1 := hl.insert "__c2" .unit (by decide) (by decide)
    have hac : (locals.insert "__c2" .unit).get? "__accrued" = some (.bool (accrueActive p evm)) := by
      rw [store_get_ne _ _ (by decide)]; exact ha
    have he2 := morphoAfterAccrueCapturedCall p 768 evm evm' _ imms hl1.toMarketLocals hac
    have hadc : fp'.toNat = 416 + accrueMemoryCost p evm evm' := had.cursor
    have heq : 768 + accrueMemoryCost p evm evm' = fp'.toNat + 352 := by omega
    rw [heq] at he2
    refine .ok ((StateBlock.start.step hecall).step he2)
      (hl1.insert "__memory" _ (by decide) (by decide)) (store_get_self _ _ _) hs' hm'
      (by omega) (by have hz := had.preserves.size; rw [hm.size] at hz; exact hz) ?_ ?_ hr
    · exact hm.params.ofPrefix had.preserves (by decide) (by decide) (by rw [hm.size]; decide) (by decide)
    · rw [memoryPrefix_memLoad had.preserves _ (by decide) (by decide) (by rw [hm.size]; decide)]
      have hz := supplyGuardMem_zero96 p
      rw [supplyGuardMem, morphoZeroAddressMem,
        (supplyInputHeap p).1.messageLoad (by decide) (by decide) _ _ _ (by decide) (by decide)] at hz
      exact hz

end Benchmarks.Morpho.MorphoBlue
