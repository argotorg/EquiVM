import Benchmarks.Morpho.MorphoBlue.BodyCommon

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.Morpho.MorphoBlue

-- LIBRARY CANDIDATE: a selector prefix determines each in-bounds selector byte.
theorem selectorPrefix_get {cd sel : ByteArray} {i : Nat} (hi : i < 4)
    (hs : 4 ≤ cd.size) (he : cd.extract 0 4 = sel) :
    cd[i] = sel[i]'(by rw [← he, ByteArray.size_extract]; omega) := by
  have hx : (cd.extract 0 4)[i]'(by rw [ByteArray.size_extract]; omega) = cd[i] := by
    simp only [ByteArray.getElem_extract, Nat.zero_add]
  simpa only [he] using hx.symm

-- LIBRARY CANDIDATE: compare raw-calldata length with a fixed lower bound.
theorem evalCalldataLengthGe {cfg : Config} {frame : Frame} {evm : EVM.State}
    {cd : ByteArray} (n : Nat) (hg : frame.locals.get? "__calldata" = some (.bytes cd)) :
    evalExpr? cfg frame evm
      (.binary .ge (.arrayLength .localVar ⟨"__calldata", []⟩) (.intLit (Int.ofNat n))) =
      .ok (.bool (decide (n ≤ cd.size))) := by
  simp only [evalExpr?, hg, readLocalPath?, evalBinaryOp?, pure, bind, EvalResult.bind]
  simp

-- LIBRARY CANDIDATE: evaluate a raw-calldata slice in a frame preserving that argument.
theorem evalCalldataSlice {cfg : Config} {frame : Frame} {evm : EVM.State}
    {cd : ByteArray} {start stop : Nat} (hg : frame.locals.get? "__calldata" = some (.bytes cd))
    (hs : start ≤ stop) (he : stop ≤ cd.size) :
    evalExpr? cfg frame evm (.bytesSlice (.var "__calldata")
      (.intLit (Int.ofNat start)) (.intLit (Int.ofNat stop))) =
      .ok (.bytes (cd.extract start stop)) := by
  simp only [evalExpr?, hg, EvalResult.ofOption, pure, bind, EvalResult.bind]
  exact sliceBytes_nat hs he

end Benchmarks.Morpho.MorphoBlue
