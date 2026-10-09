import Benchmarks.Morpho.MorphoBlue.SupplySourceStart
import Benchmarks.Morpho.MorphoBlue.MarketMemoryPrefix

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

theorem supplyGuardMem_zero96 (p : MarketParamsWords) :
    memLoad (UInt256.ofNat 96) (supplyGuardMem p) = UInt256.ofNat 0 := by
  rw [supplyGuardMem, morphoZeroAddressMem,
    (supplyInputHeap p).1.messageLoad (by decide) (by decide) _ _ _ (by decide) (by decide)]
  rw [supplyInputMem, morphoInconsistentInputMem,
    (accruePublicMemory p).1.messageLoad (by decide) (by decide) _ _ _ (by decide) (by decide)]
  rw [accruePublicMem, marketCreatedErrorMem,
    ((createMarketDecodedHeap p).hash (by decide) p.id (UInt256.ofNat 3)).messageLoad
      (by decide) (by decide) _ _ _ (by decide) (by decide)]
  rw [twoWordHashMem_memLoad_above64 _ _ _ (by decide) (by rw [(createMarketDecodedHeap p).size]; decide)]
  exact createMarketDecodedMem_zero96 p

inductive SupplyAccrueRefines (v : MorphoImmutables) (ee : ExecutionEnv) (g : Sat256) (s0 : State)
    (p : MarketParamsWords) (assets shares account srcOff len : UInt256) (data : ByteArray)
    (locals imms : Store) (evm : EVM.State) (R : List UInt256) : Prop where
  | reverted : ExecBlock config { contract := contract, locals := locals, immutables := imms }
      evm (supplyTransition.body.drop 9) .reverted → RDrev (deployedRuntime v) g s0 →
      SupplyAccrueRefines v ee g s0 p assets shares account srcOff len data locals imms evm R
  | static : ExecBlock config { contract := contract, locals := locals, immutables := imms }
      evm (supplyTransition.body.drop 9) .staticViolation → RDstatic (deployedRuntime v) g s0 →
      SupplyAccrueRefines v ee g s0 p assets shares account srcOff len data locals imms evm R
  | ok {locals' evm' σ' mem' fp' aw' out' k' C'} :
      StateBlock config { contract := contract, locals := locals, immutables := imms }
        evm (supplyTransition.body.drop 9) { contract := contract, locals := locals', immutables := imms }
        evm' (supplyTransition.body.drop 11) →
      SupplyLocals p assets shares account data locals' →
      locals'.get? "__memory" = some (.int (Int.ofNat (fp'.toNat + 128))) →
      SourceState s0 ee σ' evm' → MorphoHeap mem' fp' 288 → 480 ≤ fp'.toNat →
      480 ≤ mem'.size → p.InMemory (UInt256.ofNat 128) mem' →
      memLoad (UInt256.ofNat 96) mem' = UInt256.ofNat 0 →
      RD (deployedRuntime v) ee g s0 (UInt256.ofNat 3948)
        (supplyAccrueTail p.id assets shares account srcOff len R) mem' aw' out' σ' k' C' →
      SupplyAccrueRefines v ee g s0 p assets shares account srcOff len data locals imms evm R

theorem morphoSupplyAccrueRefine {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256}
    {s0 evm : State} {aw assets shares account srcOff len : UInt256} {out : ByteArray}
    {σ : AccountMap} {k C : Nat} {R : List UInt256} (p : MarketParamsWords) (data : ByteArray)
    (locals imms : Store) (hstack : R.length + 53 ≤ 1024) (hc : p.Canonical)
    (hl : SupplyLocals p assets shares account data locals)
    (ha : locals.get? "__accrued" = some (.bool (accrueActive p evm)))
    (hs : SourceState s0 ee σ evm)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 3938)
      (supplyAccrueTail p.id assets shares account srcOff len R) (supplyGuardMem p) aw out σ k C) :
    SupplyAccrueRefines v ee g s0 p assets shares account srcOff len data locals imms evm R := by
  have rd1 := morphoBlocks.morpho_block_3938 (immWords := wordsOf (immStore v))
    (by change R.length + 4 + 13 ≤ 1024; omega)
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) h
  have hm := (supplyGuardHeap p).1
  have hf := morphoAccrueFunctionRefineWithMemory (v := v) p imms hc
    (by change R.length + 13 + 40 ≤ 1024; omega) hs
    (createMarketHeap_morpho hm (by decide) 512 (by decide) (lt_usize _ (by decide)))
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
        evm supplyTransition.body[9]!
        (.ok { contract := contract, locals := locals.insert "__c2" .unit, immutables := imms } evm') := by
      rcases hv with rfl | rfl <;> exact he1
    have hl1 := hl.insert "__c2" .unit (by decide) (by decide)
    have hac : (locals.insert "__c2" .unit).get? "__accrued" = some (.bool (accrueActive p evm)) := by
      rw [store_get_ne _ _ (by decide)]; exact ha
    have he2 := morphoAfterAccrueCapturedCall p 608 evm evm' _ imms hl1.toMarketLocals hac
    have hadc : fp'.toNat = 480 + accrueMemoryCost p evm evm' := had.cursor
    have heq : 608 + accrueMemoryCost p evm evm' = fp'.toNat + 128 := by omega
    rw [heq] at he2
    refine .ok ((StateBlock.start.step hecall).step he2)
      (hl1.insert "__memory" _ (by decide) (by decide)) (store_get_self _ _ _) hs' hm'
      (by omega) (by have hz := had.preserves.size; rw [hm.size] at hz; exact hz) ?_ ?_ hr
    · exact hm.params.ofPrefix had.preserves (by decide) (by decide) (by rw [hm.size]; decide) (by decide)
    · rw [memoryPrefix_memLoad had.preserves _ (by decide) (by decide) (by rw [hm.size]; decide)]
      exact supplyGuardMem_zero96 p

end Benchmarks.Morpho.MorphoBlue
