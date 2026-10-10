import Benchmarks.Morpho.MetaMorphoV1_1.AllocationSource
import Benchmarks.Morpho.MetaMorphoV1_1.UpdateWithdrawQueueAllocationSyntax
import Benchmarks.EAS.Attester.WordHelpers

/-! Size arithmetic and source calls for allocating arrays of one-word elements. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

-- LIBRARY CANDIDATE: a bounded word-array allocation has no arithmetic wrap or padding.
theorem wordArraySize_lt {n : Nat} (hn : n ≤ solcMaxU64) : 32 + 32 * n < UInt256.size := by
  change n ≤ 18446744073709551615 at hn
  change _ < 2 ^ 256
  omega

theorem wordArraySize_rounded {n : Nat} (hn : n ≤ solcMaxU64) :
    roundedSize (UInt256.ofNat (32 + 32 * n)) = UInt256.ofNat (32 + 32 * n) := by
  apply u256_inj
  rw [roundedSize_toNat, UInt256.toNat_ofNat_of_lt (wordArraySize_lt hn)]
  have hfit : 32 + 32 * n + 31 < UInt256.size := by
    change n ≤ 18446744073709551615 at hn
    change _ < 2 ^ 256
    omega
  rw [Nat.mod_eq_of_lt hfit]
  omega

theorem wordArrayDataSize {n : Nat} (hn : n ≤ solcMaxU64) :
    (UInt256.ofNat (32 + 32 * n) + UInt256.lnot ⟨31⟩).toNat = 32 * n := by
  rw [uadd_toNat, UInt256.toNat_ofNat_of_lt (wordArraySize_lt hn), lnot31_toNat]
  have hs : UInt256.size = 2 ^ 256 := by decide +kernel
  rw [hs]
  have hm := wordArraySize_lt hn
  rw [hs] at hm
  omega

theorem wordArrayAllocationFits (ptr : UInt256) {n : Nat} (hn : n ≤ solcMaxU64) :
    allocationFits ptr (UInt256.ofNat (32 + 32 * n)) ↔
      ptr.toNat + 32 + 32 * n < 2 ^ 64 := by
  rw [allocationFits_iff_sum_lt, wordArraySize_rounded hn,
    UInt256.toNat_ofNat_of_lt (wordArraySize_lt hn)]
  omega

theorem wordArrayNextCursor (ptr : UInt256) {n : Nat} (hn : n ≤ solcMaxU64) :
    nextCursor ptr (UInt256.ofNat (32 + 32 * n)) =
      UInt256.ofNat (ptr.toNat + 32 + 32 * n) := by
  rw [nextCursor, wordArraySize_rounded hn]
  conv_lhs => lhs; rw [← u256_ofNat_toNat ptr]
  rw [ofNat_add_words]
  congr 1
  omega

theorem reserveWordArraySizeSource {frame : Frame} {evm : State} {name : Ident} {n : Nat}
    (hget : frame.locals.get? name = some (.int (Int.ofNat n))) (hn : n ≤ solcMaxU64) :
    evalExpr? config frame evm
      (.binary .add (.intLit 32) (.binary .mul (.intLit 32) (.var name))) =
      .ok (uint256Value (UInt256.ofNat (32 + 32 * n))) := by
  simp only [evalExpr?, hget, EvalResult.ofOption, bind, EvalResult.bind, pure,
    evalBinaryOp?, uint256Value, UInt256.toNat_ofNat_of_lt (wordArraySize_lt hn),
    Int.ofNat_eq_natCast, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]

theorem reserveWordArrayReturns {frame : Frame} {evm : State} {name : Ident}
    {n : Nat} {ptr : UInt256}
    (hc : frame.contract = contract)
    (hp : frame.locals.get? cursorName = some (uint256Value ptr))
    (hn : frame.locals.get? name = some (.int (Int.ofNat n))) (hbound : n ≤ solcMaxU64)
    (hfit : ptr.toNat + 32 + 32 * n < 2 ^ 64) :
    ExecStmt config frame evm (reserveWordArray name)
      (.ok { frame with
        locals := frame.locals.insert cursorName
          (uint256Value (UInt256.ofNat (ptr.toNat + 32 + 32 * n))) } evm) := by
  have h := allocateCallReturns (frame := frame) (evm := evm)
    (ptrExpr := .var cursorName) cursorName
    (by rw [hc]; exact allocateFunction_lookup)
    (by simp only [evalExpr?, hp, EvalResult.ofOption])
    (reserveWordArraySizeSource hn hbound) ((wordArrayAllocationFits ptr hbound).mpr hfit)
  simpa only [wordArrayNextCursor ptr hbound] using h

theorem reserveWordArrayReverts {frame : Frame} {evm : State} {name : Ident}
    {n : Nat} {ptr : UInt256}
    (hc : frame.contract = contract)
    (hp : frame.locals.get? cursorName = some (uint256Value ptr))
    (hn : frame.locals.get? name = some (.int (Int.ofNat n))) (hbound : n ≤ solcMaxU64)
    (hfit : ¬ ptr.toNat + 32 + 32 * n < 2 ^ 64) :
    ExecStmt config frame evm (reserveWordArray name) .reverted := by
  exact allocateCallReverts cursorName
    (by rw [hc]; exact allocateFunction_lookup)
    (by simp only [evalExpr?, hp, EvalResult.ofOption])
    (reserveWordArraySizeSource hn hbound) (fun h ↦ hfit ((wordArrayAllocationFits ptr hbound).mp h))

-- GENERALIZES evalExpr_newSingleton to an arbitrary natural length and length expression.
theorem evalExpr_newArrayNat {cfg : Config} {frame : Frame} {evm : State}
    {ty : StorageType} {value : Value} {expr : Expr} {n : Nat}
    (hn : evalExpr? cfg frame evm expr = .ok (.int (Int.ofNat n)))
    (hdefault : defaultValue? ty = .ok value) :
    evalExpr? cfg frame evm (.newArray ty expr) = .ok (.array (List.replicate n value)) := by
  simp only [evalExpr?, hn, bind, EvalResult.bind, Int.ofNat_eq_natCast,
    show ¬ (n : Int) < 0 by omega, ↓reduceIte, hdefault, Int.toNat_natCast, pure]

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
