import Benchmarks.Morpho.MorphoBlue.RepayMarketRefine
import Benchmarks.Morpho.MorphoBlue.SupplyEvent
import Benchmarks.Morpho.MorphoBlue.HeapWordWrites

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

theorem repayEmit (p : MarketParamsWords) (assets shares account : UInt256) (data : ByteArray)
    (locals imms : Store) (evm : EVM.State) (hl : SupplyLocals p assets shares account data locals) :
    ExecStmt config { contract := contract, locals := locals, immutables := imms } evm
      repayTransition.body[19]! (.ok { contract := contract, locals := locals, immutables := imms } evm) := by
  apply ExecStmt.emit
  change evalExprs? config _ _ [.var "id", .env .caller, .var "onBehalf", .var "assets", .var "shares"] = _
  simp only [evalExprs?, hl.evalId imms evm, hl.evalAccount imms evm, hl.evalAssets imms evm,
    hl.evalShares imms evm, evalExpr?, envValue, EvalResult.bind, bind, pure]
  rfl

theorem morphoRepayStoreEvent {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {aw fp id assets shares account srcOff len debt : UInt256} {out mem : ByteArray}
    {σ : AccountMap} {k C : Nat} {R : List UInt256} (hstack : R.length + 24 ≤ 1024)
    (hperm : ee.perm = true) (hfree : memLoad (UInt256.ofNat 64) (twoWordHashMem id (UInt256.ofNat 3) mem) = fp)
    (hc : debt.toNat < 2 ^ 128)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 10767)
      (debt :: repayMarketTail id assets shares account srcOff len R)
      mem aw out σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0
      (if len = UInt256.ofNat 0 then UInt256.ofNat 10845 else UInt256.ofNat 10866)
      (supplyCallbackTail assets shares srcOff len R) (twoWordEventMem (twoWordHashMem id (UInt256.ofNat 3) mem) fp assets shares) aw' out
      (storeMarketFieldAccounts σ ee id ⟨2, by decide⟩ debt) k' C' := by
  have hc' : UInt256.land debt uint128Mask = debt :=
    halfWord_low_clean _ hc
  have hh : keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
      (twoWordHashMem id (UInt256.ofNat 3) mem) + UInt256.ofNat 1 = marketFieldSlot id 2 :=
    marketBorrowSlot_hash id mem
  by_cases hz : len = UInt256.ofNat 0
  · rw [if_pos hz]
    obtain ⟨a1, k1, C1, rd1⟩ := morphoBlocks.morpho_block_10767_fallthrough_packed
      (immWords := wordsOf (immStore v)) (by change R.length + 1 + 15 ≤ 1024; omega) hperm hz h
    dsimp only [morphoBlocks.morpho_block_10767_fallthrough_memory] at rd1
    change RD _ _ _ _ _ _
      (twoWordEventMem (twoWordHashMem id (UInt256.ofNat 3) mem)
        (memLoad (UInt256.ofNat 64) (twoWordHashMem id (UInt256.ofNat 3) mem)) assets shares)
      _ _ (sstoreAccountMap ee.codeOwner σ
        (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) (twoWordHashMem id (UInt256.ofNat 3) mem) + UInt256.ofNat 1)
        (UInt256.lor (UInt256.land (solcSlotWordAt (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
          (twoWordHashMem id (UInt256.ofNat 3) mem) + UInt256.ofNat 1) σ ee) (UInt256.lnot uint128Mask))
          (UInt256.land debt uint128Mask))) _ _ at rd1
    rw [hfree, hh, hc'] at rd1
    exact ⟨a1, k1, C1, rd1⟩
  · rw [if_neg hz]
    obtain ⟨a1, k1, C1, rd1⟩ := morphoBlocks.morpho_block_10767_taken_packed
      (immWords := wordsOf (immStore v)) (by change R.length + 1 + 15 ≤ 1024; omega) hperm hz
      (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) h
    dsimp only [morphoBlocks.morpho_block_10767_taken_memory] at rd1
    change RD _ _ _ _ _ _
      (twoWordEventMem (twoWordHashMem id (UInt256.ofNat 3) mem)
        (memLoad (UInt256.ofNat 64) (twoWordHashMem id (UInt256.ofNat 3) mem)) assets shares)
      _ _ (sstoreAccountMap ee.codeOwner σ
        (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) (twoWordHashMem id (UInt256.ofNat 3) mem) + UInt256.ofNat 1)
        (UInt256.lor (UInt256.land (solcSlotWordAt (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
          (twoWordHashMem id (UInt256.ofNat 3) mem) + UInt256.ofNat 1) σ ee) (UInt256.lnot uint128Mask))
          (UInt256.land debt uint128Mask))) _ _ at rd1
    rw [hfree, hh, hc'] at rd1
    exact ⟨a1, k1, C1, rd1⟩

end Benchmarks.Morpho.MorphoBlue
