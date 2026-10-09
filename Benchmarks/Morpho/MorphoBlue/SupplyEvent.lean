import Benchmarks.Morpho.MorphoBlue.SupplyMarketRefine
import Benchmarks.Morpho.MorphoBlue.HeapWordWrites

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

def supplyCallbackTail (assets shares srcOff len : UInt256) (R : List UInt256) : List UInt256 :=
  [srcOff, len, UInt256.ofNat 0, UInt256.ofNat 128, UInt256.ofNat 32, shares, assets, solcAddrMask] ++ R

theorem supplyEmit (p : MarketParamsWords) (assets shares account : UInt256) (data : ByteArray)
    (locals imms : Store) (evm : EVM.State) (hl : SupplyLocals p assets shares account data locals) :
    ExecStmt config { contract := contract, locals := locals, immutables := imms } evm
      supplyTransition.body[17]! (.ok { contract := contract, locals := locals, immutables := imms } evm) := by
  apply ExecStmt.emit
  change evalExprs? config _ _ [.var "id", .env .caller, .var "onBehalf", .var "assets", .var "shares"] = _
  simp only [evalExprs?, hl.evalId imms evm, hl.evalAccount imms evm, hl.evalAssets imms evm,
    hl.evalShares imms evm, evalExpr?, envValue, EvalResult.bind, bind, pure]
  rfl

theorem morphoSupplyStoreEvent {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {aw fp id assets shares account srcOff len : UInt256} {out mem : ByteArray}
    {σ : AccountMap} {k C : Nat} {R : List UInt256} (hstack : R.length + 24 ≤ 1024)
    (hperm : ee.perm = true) (hfree : memLoad (UInt256.ofNat 64) mem = fp)
    (hc : (marketFieldWord σ ee id 0 + assets).toNat < 2 ^ 128)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 4124)
      ((marketFieldWord σ ee id 0 + assets) :: supplyStoreTail σ ee id assets shares account srcOff len R)
      mem aw out σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0
      (if len = UInt256.ofNat 0 then UInt256.ofNat 4186 else UInt256.ofNat 4218)
      (supplyCallbackTail assets shares srcOff len R) (twoWordEventMem mem fp assets shares) aw' out
      (storeMarketFieldAccounts σ ee id ⟨0, by decide⟩ (marketFieldWord σ ee id 0 + assets)) k' C' := by
  have hc' : UInt256.land (marketFieldWord σ ee id 0 + assets) uint128Mask = marketFieldWord σ ee id 0 + assets :=
    halfWord_low_clean _ hc
  by_cases hz : len = UInt256.ofNat 0
  · rw [if_pos hz]
    obtain ⟨a1, k1, C1, rd1⟩ := morphoBlocks.morpho_block_4124_fallthrough_packed
      (immWords := wordsOf (immStore v)) (by change R.length + 1 + 14 ≤ 1024; omega) hperm hz h
    dsimp only [morphoBlocks.morpho_block_4124_fallthrough_memory] at rd1
    rw [hfree, hc'] at rd1
    exact ⟨a1, k1, C1, rd1⟩
  · rw [if_neg hz]
    obtain ⟨a1, k1, C1, rd1⟩ := morphoBlocks.morpho_block_4124_taken_packed
      (immWords := wordsOf (immStore v)) (by change R.length + 1 + 14 ≤ 1024; omega) hperm hz
      (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) h
    dsimp only [morphoBlocks.morpho_block_4124_taken_memory] at rd1
    rw [hfree, hc'] at rd1
    exact ⟨a1, k1, C1, rd1⟩

end Benchmarks.Morpho.MorphoBlue
