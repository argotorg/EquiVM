import Benchmarks.Morpho.MorphoBlue.LiquidateBadDebtRefine
import Benchmarks.Morpho.MorphoBlue.HeapWordSequence
import Benchmarks.Morpho.MorphoBlue.SafeTransferInternal

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

def liquidateEventMem (mem : ByteArray) (fp assets shares seized badAssets badShares : UInt256) : ByteArray :=
  writeCascade mem (returnWordWrites fp.toNat [assets, shares, seized, badAssets, badShares])

def liquidateTransferTail (assets seized srcOff len : UInt256) (R : List UInt256) : List UInt256 :=
  [srcOff, len, UInt256.ofNat 0, assets, seized, UInt256.ofNat 128] ++ R

theorem liquidateEmit (p : MarketParamsWords) (assets seized shares account badAssets badShares : UInt256)
    (data : ByteArray) (locals imms : Store) (evm : EVM.State)
    (hl : LiquidateEventLocals p account seized shares data assets badAssets badShares locals) :
    ExecStmt config { contract := contract, locals := locals, immutables := imms } evm
      liquidateTransition.body[31]! (.ok { contract := contract, locals := locals, immutables := imms } evm) := by
  apply ExecStmt.emit
  change evalExprs? config _ _ [.var "id", .env .caller, .var "borrower", .var "repaidAssets",
    .var "repaidShares", .var "seizedAssets", .var "badDebtAssets", .var "badDebtShares"] = _
  simp only [evalExprs?, hl.evalId imms evm, hl.evalBorrower imms evm, hl.evalAssets imms evm,
    hl.evalShares imms evm, hl.evalSeized imms evm, hl.evalBadAssets imms evm, hl.evalBadShares imms evm,
    evalExpr?, envValue, EvalResult.bind, bind, pure]
  rfl

theorem liquidateEvent_heap {mem : ByteArray} {fp : UInt256} {spare : Nat}
    (hm : MorphoHeap mem fp spare) (hb : 160 ≤ spare) (assets shares seized badAssets badShares : UInt256) :
    MorphoHeap (liquidateEventMem mem fp assets shares seized badAssets badShares) fp spare ∧
      MemoryPrefix mem (liquidateEventMem mem fp assets shares seized badAssets badShares) fp.toNat :=
  hm.wordWrites [assets, shares, seized, badAssets, badShares] fp.toNat le_rfl
    (by change fp.toNat + 160 ≤ fp.toNat + spare; omega)

theorem morphoLiquidateEvent {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {aw fp trash id assets seized shares badAssets badShares srcOff len : UInt256} {out mem : ByteArray}
    {σ : AccountMap} {k C spare : Nat} {R : List UInt256} (hstack : R.length + 32 ≤ 1024)
    (hperm : ee.perm = true) (hm : MorphoHeap mem fp spare) :
    RD (deployedRuntime v) ee g s0 (UInt256.ofNat 2574)
      (liquidateEventTail trash id assets seized shares badAssets badShares srcOff len R) mem aw out σ k C →
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 (UInt256.ofNat 14666)
      ([UInt256.land (memLoad (UInt256.ofNat 160) (liquidateEventMem mem fp assets shares seized badAssets badShares)) solcAddrMask,
        UInt256.ofNat ee.source.val, seized, UInt256.ofNat 2704] ++ liquidateTransferTail assets seized srcOff len R)
      (liquidateEventMem mem fp assets shares seized badAssets badShares) aw' out σ k' C' := by
  intro h
  obtain ⟨a1, k1, C1, rd1⟩ := morphoBlocks.morpho_block_2574_packed (immWords := wordsOf (immStore v))
    (by change R.length + 13 ≤ 1024; omega) hperm (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) h
  dsimp only [morphoBlocks.morpho_block_2574_stack, morphoBlocks.morpho_block_2574_memory] at rd1
  rw [hm.free] at rd1
  have hadd (n : Nat) (hn : n ≤ 128) : (fp + UInt256.ofNat n).toNat = fp.toNat + n :=
    uadd_word_ofNat_toNat _ _ (by have hh := hm.space; change _ < 2 ^ 256; omega)
  rw [hadd 32 (by decide), hadd 64 (by decide), hadd 96 (by decide), hadd 128 (by decide)] at rd1
  exact ⟨a1, k1, C1, rd1⟩

end Benchmarks.Morpho.MorphoBlue
