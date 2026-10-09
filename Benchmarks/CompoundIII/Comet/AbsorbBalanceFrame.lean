import Benchmarks.CompoundIII.Comet.AbsorbLoopFrame
import Benchmarks.CompoundIII.Comet.AbsorbBalanceModel

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.CompoundIII.Comet.Immutables

namespace Benchmarks.CompoundIII.Comet

theorem AbsorbLoopFrame.balance {v absorber account basic old price i delta frame}
    (hf : AbsorbLoopFrame v absorber account basic old price i delta frame) :
    AbsorbLoopFrame v absorber account basic old price i delta
      (absorbBalanceFrame frame v old delta price) := by
  dsimp only [absorbBalanceFrame]
  split <;> cases hf <;> constructor <;>
    simp_all only [absorbBalanceSignedFrame, absorbBalanceDivFrame,
      Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert] <;> rfl

theorem absorbBalanceFrame_newBalance (frame : Frame) (v : CometWithExtendedAssetListImmutables)
    (old delta price : UInt256) :
    (absorbBalanceFrame frame v old delta price).locals.get? "newBalance" =
      some (.int (signedWord (absorbBalanceWord v old delta price))) := by
  dsimp only [absorbBalanceFrame, absorbBalanceWord]
  split_ifs <;> simp only [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert] <;> rfl

end Benchmarks.CompoundIII.Comet
