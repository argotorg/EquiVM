import Benchmarks.Morpho.MorphoBlue.SupplyCollateralUpdateRefine
import Benchmarks.Morpho.MorphoBlue.FinalizeVoid

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

def supplyCollateralEventMem (p : MarketParamsWords) (account assets : UInt256) : ByteArray :=
  writeWord (supplyCollateralPositionMem p account) 544 assets

theorem supplyCollateralEventMem_facts (p : MarketParamsWords) (account assets : UInt256) :
    MorphoHeap (supplyCollateralEventMem p account assets) (UInt256.ofNat 544) 0 ∧
    (supplyCollateralEventMem p account assets).size = 576 ∧
    memLoad (UInt256.ofNat 96) (supplyCollateralEventMem p account assets) = UInt256.ofNat 0 ∧
    p.InMemory (UInt256.ofNat 128) (supplyCollateralEventMem p account assets) := by
  have hp := supplyCollateralPositionHeap p account
  have hg : 544 - (supplyCollateralPositionMem p account).size < USize.size := by rw [hp.size]; exact USize.size_pos
  have hs : (supplyCollateralEventMem p account assets).size = 576 := by
    rw [supplyCollateralEventMem, writeWord_size _ _ _ hg, hp.size]; rfl
  have h64 : memLoad (UInt256.ofNat 64) (supplyCollateralEventMem p account assets) = UInt256.ofNat 544 := by
    rw [supplyCollateralEventMem, memLoad_writeWord_disjoint _ _ _ _ hg (by rw [hp.size]; decide) (Or.inl (by decide))]
    exact hp.freePtr
  refine ⟨⟨by rw [hs]; decide, h64, by decide, by rw [hs]; exact USize.size_pos, by decide⟩, hs, ?_, ?_⟩
  · rw [supplyCollateralEventMem, memLoad_writeWord_disjoint _ _ _ _ hg (by rw [hp.size]; decide) (Or.inl (by decide))]
    rw [supplyCollateralPositionMem,
      twoWordHashMem_memLoad_above64 _ _ _ (by decide)
        (by rw [((supplyCollateralCastHeap p).1.hash (by decide) p.id (UInt256.ofNat 2)).size]; decide),
      twoWordHashMem_memLoad_above64 _ _ _ (by decide) (by rw [(supplyCollateralCastHeap p).1.size]; decide)]
    exact supplyCollateralCastMem_zero96 p
  · exact hp.params.writeWord 544 assets (by decide) (by rw [hp.size]; decide) hg (Or.inl (by decide))

-- The event has no state effect in Solm; its arguments are still evaluated.
theorem supplyCollateralEmit (p : MarketParamsWords) (assets account : UInt256) (data : ByteArray)
    (locals imms : Store) (evm : EVM.State) (hl : SupplyCollateralLocals p assets account data locals) :
    ExecStmt config { contract := contract, locals := locals, immutables := imms } evm
      supplyCollateralTransition.body[9]! (.ok { contract := contract, locals := locals, immutables := imms } evm) := by
  apply ExecStmt.emit
  change evalExprs? config _ _ [.var "id", .env .caller, .var "onBehalf", .var "assets"] = _
  simp only [evalExprs?, hl.evalId imms evm, hl.evalAccount imms evm, hl.evalAssets imms evm,
    evalExpr?, envValue, EvalResult.bind, bind, pure]
  rfl

section Event
variable {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
  {aw assets account srcOff len : UInt256} {out : ByteArray} {σ : AccountMap} {k C : Nat} {R : List UInt256}

theorem morphoSupplyCollateralEvent (p : MarketParamsWords) (hstack : R.length + 28 ≤ 1024)
    (hp : ee.perm = true)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 10235)
      (supplyCollateralUpdateTail p.id assets account srcOff len R) (supplyCollateralPositionMem p account) aw out σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 (if len = UInt256.ofNat 0 then UInt256.ofNat 10286 else UInt256.ofNat 10307)
      ([srcOff, len, solcAddrMask, assets, UInt256.ofNat 0, UInt256.ofNat 128] ++ R)
      (supplyCollateralEventMem p account assets) aw' out σ k' C' := by
  by_cases hz : len = UInt256.ofNat 0
  · rw [if_pos hz]
    obtain ⟨a, k, C, rd⟩ := morphoBlocks.morpho_block_10235_fallthrough_packed
      (immWords := wordsOf (immStore v)) (by change R.length + 2 + 10 ≤ 1024; omega) hp hz h
    dsimp only [morphoBlocks.morpho_block_10235_fallthrough_memory] at rd
    rw [(supplyCollateralPositionHeap p account).freePtr] at rd
    exact ⟨a, k, C, rd⟩
  · rw [if_neg hz]
    obtain ⟨a, k, C, rd⟩ := morphoBlocks.morpho_block_10235_taken_packed
      (immWords := wordsOf (immStore v)) (by change R.length + 2 + 10 ≤ 1024; omega) hp hz
      (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) h
    dsimp only [morphoBlocks.morpho_block_10235_taken_memory] at rd
    rw [(supplyCollateralPositionHeap p account).freePtr] at rd
    exact ⟨a, k, C, rd⟩

end Event
end Benchmarks.Morpho.MorphoBlue
