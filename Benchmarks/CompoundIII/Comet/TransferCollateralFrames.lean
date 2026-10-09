import Benchmarks.CompoundIII.Comet.TransferCollateralModel

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.CompoundIII.Comet.Immutables

namespace Benchmarks.CompoundIII.Comet

structure TransferCollateralArgs (frame : Frame) (v : CometWithExtendedAssetListImmutables)
    (src dst asset : AccountAddress) (amount : UInt256) : Prop where
  contract : frame.contract = Comet.contract
  immutables : frame.immutables = immStore v
  src : frame.locals.get? "src" = some (.address src)
  dst : frame.locals.get? "dst" = some (.address dst)
  asset : frame.locals.get? "asset" = some (.address asset)
  amount : frame.locals.get? "amount" = some (.int amount.toNat)
  user : frame.locals.get? "userCollateral" = none

theorem TransferCollateralArgs.insert {frame v src dst asset amount}
    (hf : TransferCollateralArgs frame v src dst asset amount) (name : Ident) (value : Value)
    (hn : name ∉ ["src", "dst", "asset", "amount", "userCollateral"]) :
    TransferCollateralArgs { frame with locals := frame.locals.insert name value }
      v src dst asset amount := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hn
  refine ⟨hf.contract, hf.immutables, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert, hn.1, Ne.symm hn.1]
      using hf.src
  · simpa [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert, hn.2.1, Ne.symm hn.2.1]
      using hf.dst
  · simpa [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert, hn.2.2.1, Ne.symm hn.2.2.1]
      using hf.asset
  · simpa [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert,
      hn.2.2.2.1, Ne.symm hn.2.2.2.1]
      using hf.amount
  · simpa [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert,
      hn.2.2.2.2, Ne.symm hn.2.2.2.2]
      using hf.user

theorem TransferCollateralArgs.ready {frame v src dst asset amount}
    (hf : TransferCollateralArgs frame v src dst asset amount) (evm : EVM.State) :
    TransferCollateralArgs (transferCollateralReadyFrame frame evm src dst asset amount)
      v src dst asset amount :=
  (((hf.insert "srcCollateral" _ (by decide)).insert "dstCollateral" _ (by decide)).insert
    "srcCollateralNew" _ (by decide)).insert "dstCollateralNew" _ (by decide)

end Benchmarks.CompoundIII.Comet
