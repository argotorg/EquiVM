import Benchmarks.Morpho.MorphoBlue.LoanTransferPair
import Benchmarks.Morpho.MorphoBlue.SupplyEvent
import Benchmarks.Morpho.MorphoBlue.SafeTransferInternal

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

theorem morphoSupplyTransfer {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256}
    {s0 evm : State} {mem out data : ByteArray} {aw assets shares account x0 x1 ptr : UInt256} {σ : AccountMap}
    {k C : Nat} (p : MarketParamsWords) (locals imms : Store) (hc : p.Canonical)
    (hl : SupplyLocals p assets shares account data locals) (hs : SourceState s0 ee σ evm)
    (hm : MorphoHeap mem ptr 0) (hsize : 160 ≤ mem.size) (hptr : 160 ≤ ptr.toNat)
    (hget : locals.get? "__memory" = some (.int (Int.ofNat ptr.toNat)))
    (hzero : memLoad (UInt256.ofNat 96) mem = UInt256.ofNat 0)
    (htoken : memLoad (UInt256.ofNat 128) mem = p.loanToken)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 4186)
      (supplyCallbackTail assets shares x0 x1 []) mem aw out σ k C) :
    ReturnBlockRefines config (deployedRuntime v) ee g s0
      { contract := contract, locals := locals, immutables := imms } evm
      (supplyTransition.body.drop 19) supplyTransition.returnType := by
  exact morphoLoanTransferPairAt p locals imms "__c8" (by decide) (by decide) hc hl hs hm hsize hptr
    hget hzero htoken (Or.inl rfl) h

end Benchmarks.Morpho.MorphoBlue
