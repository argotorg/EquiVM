import Benchmarks.CompoundIII.Comet.CollateralLoopWords

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.CompoundIII.Comet.Immutables

namespace Benchmarks.CompoundIII.Comet

structure CollateralLoopFrame (v : CometWithExtendedAssetListImmutables)
    (account : AccountAddress) (assets reserved : UInt256) (i : Nat) (liquidity : UInt256)
    (frame : Frame) : Prop where
  contract : frame.contract = Comet.contract
  immutables : frame.immutables = immStore v
  account : frame.locals.get? "account" = some (.address account)
  assets : frame.locals.get? "assetsIn" = some (.int assets.toNat)
  reserved : frame.locals.get? "_reserved" = some (.int reserved.toNat)
  index : frame.locals.get? "i" = some (.int i)
  liquidity : frame.locals.get? "liquidity" = some (.int (signedWord liquidity))
  storage : frame.locals.get? "userCollateral" = none

def collateralMemberFrame (frame : Frame) (member : Bool) : Frame :=
  { frame with locals := frame.locals.insert "__c3" (.bool member) }

def collateralNextFrame (frame : Frame) (i : Nat) : Frame :=
  { frame with locals := frame.locals.insert "i" (.int (i + 1)) }

def collateralAddFrame (frame : Frame) (liquidity value : UInt256) : Frame :=
  { frame with locals := frame.locals.insert "liquidity" (.int (signedWord (liquidity + value))) }

theorem CollateralLoopFrame.member {v account assets reserved i liquidity frame}
    (hf : CollateralLoopFrame v account assets reserved i liquidity frame) (member : Bool) :
    CollateralLoopFrame v account assets reserved i liquidity
      (collateralMemberFrame frame member) := by
  obtain ⟨hc, him, ha, hb, hr, hi, hl, hu⟩ := hf
  constructor
  · exact hc
  · exact him
  · simpa [collateralMemberFrame, Std.HashMap.getElem?_insert] using ha
  · simpa [collateralMemberFrame, Std.HashMap.getElem?_insert] using hb
  · simpa [collateralMemberFrame, Std.HashMap.getElem?_insert] using hr
  · simpa [collateralMemberFrame, Std.HashMap.getElem?_insert] using hi
  · simpa [collateralMemberFrame, Std.HashMap.getElem?_insert] using hl
  · simpa [collateralMemberFrame, Std.HashMap.getElem?_insert] using hu

theorem CollateralLoopFrame.next {v account assets reserved i liquidity frame}
    (hf : CollateralLoopFrame v account assets reserved i liquidity frame) :
    CollateralLoopFrame v account assets reserved (i + 1) liquidity
      (collateralNextFrame frame i) := by
  obtain ⟨hc, him, ha, hb, hr, hi, hl, hu⟩ := hf
  constructor
  · exact hc
  · exact him
  · simpa [collateralNextFrame, Std.HashMap.getElem?_insert] using ha
  · simpa [collateralNextFrame, Std.HashMap.getElem?_insert] using hb
  · simpa [collateralNextFrame, Std.HashMap.getElem?_insert] using hr
  · simp [collateralNextFrame]
  · simpa [collateralNextFrame, Std.HashMap.getElem?_insert] using hl
  · simpa [collateralNextFrame, Std.HashMap.getElem?_insert] using hu

theorem CollateralLoopFrame.value {v account assets reserved i liquidity frame}
    (hf : CollateralLoopFrame v account assets reserved i liquidity frame)
    (borrow : Bool) (d : CollateralValueData) :
    CollateralLoopFrame v account assets reserved i liquidity
      (collateralValueFrame frame borrow d) := by
  dsimp only [collateralValueFrame, collateralMathFinal, collateralPriceFrame,
    collateralBalanceFrame, collateralAssetFrame]
  obtain ⟨hc, him, ha, hb, hr, hi, hl, hu⟩ := hf
  constructor
  · exact hc
  · exact him
  · simpa [Std.HashMap.getElem?_insert] using ha
  · simpa [Std.HashMap.getElem?_insert] using hb
  · simpa [Std.HashMap.getElem?_insert] using hr
  · simpa [Std.HashMap.getElem?_insert] using hi
  · simpa [Std.HashMap.getElem?_insert] using hl
  · simpa [Std.HashMap.getElem?_insert] using hu

theorem CollateralLoopFrame.add {v account assets reserved i liquidity frame}
    (hf : CollateralLoopFrame v account assets reserved i liquidity frame) (value : UInt256) :
    CollateralLoopFrame v account assets reserved i (liquidity + value)
      (collateralAddFrame frame liquidity value) := by
  obtain ⟨hc, him, ha, hb, hr, hi, hl, hu⟩ := hf
  constructor
  · exact hc
  · exact him
  · simpa [collateralAddFrame, Std.HashMap.getElem?_insert] using ha
  · simpa [collateralAddFrame, Std.HashMap.getElem?_insert] using hb
  · simpa [collateralAddFrame, Std.HashMap.getElem?_insert] using hr
  · simpa [collateralAddFrame, Std.HashMap.getElem?_insert] using hi
  · simp [collateralAddFrame]
  · simpa [collateralAddFrame, Std.HashMap.getElem?_insert] using hu

theorem collateralSolvent_eval {frame : Frame} {evm : EVM.State} {liquidity : UInt256}
    (hl : frame.locals.get? "liquidity" = some (.int (signedWord liquidity))) :
    evalExpr? config frame evm collateralSolventExpr =
      .ok (.bool (decide (0 ≤ signedWord liquidity))) := by
  simp only [collateralSolventExpr, evalExpr?, hl, EvalResult.ofOption,
    bind, EvalResult.bind, pure, evalBinaryOp?]

theorem collateralResult_eval {frame : Frame} {evm : EVM.State} {liquidity : UInt256}
    (borrow : Bool) (hl : frame.locals.get? "liquidity" = some (.int (signedWord liquidity))) :
    evalExpr? config frame evm (collateralResultExpr borrow) =
      .ok (.bool (collateralResultBool borrow liquidity)) := by
  cases borrow
  · simp only [collateralResultExpr, collateralResultBool, Bool.false_eq_true, if_false,
      evalExpr?, hl, EvalResult.ofOption, bind, EvalResult.bind, pure, evalBinaryOp?]
  · exact collateralSolvent_eval hl

theorem collateralAdd_exec {frame : Frame} {evm : EVM.State} {liquidity value : UInt256}
    (hf : frame.locals.get? "liquidity" = some (.int (signedWord liquidity)))
    (he : frame.locals.get? "__c8" = some (.int value.toNat))
    (hl : signedWord liquidity < 0) (hv : value.toNat < 2^255) :
    ExecStmt config frame evm collateralAddStmt
      (.ok (collateralAddFrame frame liquidity value) evm) := by
  obtain ⟨hlo, hhi⟩ := collateralSum_bounds hl hv
  have hsum := signedWord_add_of_range hlo hhi
  apply ExecStmt.assign (value := .int (signedWord (liquidity + value)))
  · rw [hsum]
    apply signedRangeSourceOk ?_ hlo hhi
    simp only [evalExpr?, hf, he, EvalResult.ofOption, bind, EvalResult.bind,
      evalBinaryOp_add_int_ok, Int.ofNat_eq_natCast]
  · simp only [assignStorageRef?, hf, updateLocalPath?, pure, bind, EvalResult.bind]
    rfl

end Benchmarks.CompoundIII.Comet
