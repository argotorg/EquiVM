import Benchmarks.CompoundIII.Comet.AbsorbLoopTailModel
import Benchmarks.CompoundIII.Comet.AbsorbLoopSource
import Benchmarks.CompoundIII.Comet.AbsorbAfterLoopSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.CompoundIII.Comet.Immutables

namespace Benchmarks.CompoundIII.Comet

theorem absorbLoopTail_source {v : CometWithExtendedAssetListImmutables}
    {absorber account : AccountAddress} {basic : UserBasicData} {old price delta : UInt256}
    {i : Nat} {evm : State} {result : InternalOutcome}
    (ht : AbsorbLoopTailTrace v account basic old price i delta evm result)
    (frame : Frame) (hf : AbsorbLoopFrame v absorber account basic old price i delta frame)
    (hi : i ≤ v.numAssets.toNat) :
    internalBlockResult config frame evm absorbLoopTailBlock result := by
  cases ht with
  | loopReverted ht =>
      exact execBlock_reverted_append (absorbLoop_source ht frame hf hi)
  | loopStatic ht =>
      exact execBlock_append_term (absorbLoop_source ht frame hf hi) (by intro _ _ he; cases he)
  | finished ht hfinish =>
      obtain ⟨afterLoop, hb, hf'⟩ := absorbLoop_source ht frame hf hi
      exact (absorbAfterLoop_source hfinish afterLoop hf').prependBlock hb

end Benchmarks.CompoundIII.Comet
