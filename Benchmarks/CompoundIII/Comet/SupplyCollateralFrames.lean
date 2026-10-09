import Benchmarks.CompoundIII.Comet.SupplyCollateralModel

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

structure SupplyCollateralArgs (frame : Frame) (sender dst asset : AccountAddress)
    (amount : UInt256) (out : ByteArray) : Prop where
  contract : frame.contract = contract
  sender : frame.locals.get? "from" = some (.address sender)
  dst : frame.locals.get? "dst" = some (.address dst)
  asset : frame.locals.get? "asset" = some (.address asset)
  amount : frame.locals.get? "amount" = some (.int amount.toNat)
  info : frame.locals.get? "assetInfo" = some (assetValue out)
  totals : frame.locals.get? "totalsCollateral" = none
  user : frame.locals.get? "userCollateral" = none

theorem SupplyCollateralArgs.insert {frame sender dst asset amount out}
    (hf : SupplyCollateralArgs frame sender dst asset amount out) (key : Ident) (value : Value)
    (hk : key ∉ ["from", "dst", "asset", "amount", "assetInfo", "totalsCollateral", "userCollateral"]) :
    SupplyCollateralArgs { frame with locals := frame.locals.insert key value }
      sender dst asset amount out := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hk
  refine ⟨hf.contract, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert,
      beq_iff_eq, if_neg hk.1] using hf.sender
  · simpa only [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert,
      beq_iff_eq, if_neg hk.2.1] using hf.dst
  · simpa only [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert,
      beq_iff_eq, if_neg hk.2.2.1] using hf.asset
  · simpa only [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert,
      beq_iff_eq, if_neg hk.2.2.2.1] using hf.amount
  · simpa only [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert,
      beq_iff_eq, if_neg hk.2.2.2.2.1] using hf.info
  · simpa only [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert,
      beq_iff_eq, if_neg hk.2.2.2.2.2.1] using hf.totals
  · simpa only [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert,
      beq_iff_eq, if_neg hk.2.2.2.2.2.2] using hf.user

theorem SupplyCollateralArgs.totalsFrame {frame sender dst asset amount out}
    (hf : SupplyCollateralArgs frame sender dst asset amount out) (evm : EVM.State) :
    SupplyCollateralArgs (supplyCollateralTotalsFrame frame evm asset amount)
      sender dst asset amount out :=
  (hf.insert "totals" _ (by decide)).insert "totals" _ (by decide)

theorem SupplyCollateralArgs.ready {frame sender dst asset amount out}
    (hf : SupplyCollateralArgs frame sender dst asset amount out) (evm : EVM.State) :
    SupplyCollateralArgs (supplyCollateralReadyFrame frame evm dst asset amount)
      sender dst asset amount out :=
  ((hf.totalsFrame evm).insert "dstCollateral" _ (by decide)).insert
    "dstCollateralNew" _ (by decide)

end Benchmarks.CompoundIII.Comet
