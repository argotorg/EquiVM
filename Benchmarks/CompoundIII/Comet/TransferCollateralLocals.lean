import Benchmarks.CompoundIII.Comet.TransferCollateralFrames

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

structure TransferCollateralBalances (frame : Frame)
    (srcBalance srcNext dstBalance dstNext : UInt256) : Prop where
  src : frame.locals.get? "srcCollateral" = some (.int srcBalance.toNat)
  srcNext : frame.locals.get? "srcCollateralNew" = some (.int srcNext.toNat)
  dst : frame.locals.get? "dstCollateral" = some (.int dstBalance.toNat)
  dstNext : frame.locals.get? "dstCollateralNew" = some (.int dstNext.toNat)

theorem TransferCollateralBalances.insert {frame srcBalance srcNext dstBalance dstNext}
    (hf : TransferCollateralBalances frame srcBalance srcNext dstBalance dstNext)
    (name : Ident) (value : Value)
    (hn : name ∉ ["srcCollateral", "srcCollateralNew", "dstCollateral", "dstCollateralNew"]) :
    TransferCollateralBalances { frame with locals := frame.locals.insert name value }
      srcBalance srcNext dstBalance dstNext := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hn
  constructor
  · simpa [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert, hn.1, Ne.symm hn.1]
      using hf.src
  · simpa [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert, hn.2.1, Ne.symm hn.2.1]
      using hf.srcNext
  · simpa [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert, hn.2.2.1, Ne.symm hn.2.2.1]
      using hf.dst
  · simpa [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert, hn.2.2.2, Ne.symm hn.2.2.2]
      using hf.dstNext

theorem transferCollateralReady_balances (frame evm src dst asset amount) :
    TransferCollateralBalances (transferCollateralReadyFrame frame evm src dst asset amount)
      (withdrawCollateralBalance evm src asset) (transferCollateralSrcNext evm src asset amount)
      (withdrawCollateralBalance evm dst asset) (transferCollateralDstNext evm dst asset amount) := by
  constructor <;> simp only [transferCollateralReadyFrame, Std.HashMap.get?_eq_getElem?,
    Std.HashMap.getElem?_insert] <;> rfl

end Benchmarks.CompoundIII.Comet
