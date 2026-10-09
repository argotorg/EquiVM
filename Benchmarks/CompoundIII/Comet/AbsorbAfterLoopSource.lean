import Benchmarks.CompoundIII.Comet.AbsorbAfterLoopModel
import Benchmarks.CompoundIII.Comet.AbsorbBalanceFrame
import Benchmarks.CompoundIII.Comet.AbsorbBalanceSource
import Benchmarks.CompoundIII.Comet.AbsorbFinishSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.CompoundIII.Comet.Immutables

namespace Benchmarks.CompoundIII.Comet

theorem absorbAfterLoop_source {v : CometWithExtendedAssetListImmutables}
    {absorber account : AccountAddress} {basic : UserBasicData} {old delta price : UInt256}
    {evm : State} {result : InternalOutcome}
    (ht : AbsorbAfterLoopTrace v account basic old delta price evm result)
    (frame : Frame) {i : Nat} (hf : AbsorbLoopFrame v absorber account basic old price i delta frame) :
    internalBlockResult config frame evm absorbAfterLoopBlock result := by
  have hb := absorbBalance_source frame evm v old delta price hf.contract hf.immutables
    hf.oldBalance hf.delta hf.basePrice
  cases ht with
  | balanceReverted hv =>
      rw [if_neg hv] at hb
      exact execBlock_reverted_append hb
  | finished hv ht =>
      rw [if_pos hv] at hb
      have hf' := hf.balance
      have hh := absorbFinish_source _ v evm absorber account basic old
        (absorbBalanceWord v old delta price) price ht hf'.contract hf'.immutables
        hf'.absorber hf'.account hf'.accountUser hf'.oldBalance
        (absorbBalanceFrame_newBalance frame v old delta price) hf'.basePrice hf'.oldPrincipal
        hf'.userBasic hf'.supplyBase hf'.borrowBase hf'.supplyIndex
        (absorbBalanceWord_lt v old delta price)
      exact hh.prependBlock hb

end Benchmarks.CompoundIII.Comet
