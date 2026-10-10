import Benchmarks.UniswapV4PoolManager.WordNotSource
import Benchmarks.UniswapV4PoolManager.WordWrappingSource
import Benchmarks.UniswapV4PoolManager.WordShiftSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def tickScanMask (bit : UInt256) (lte : Bool) : UInt256 :=
  if lte then UInt256.shiftRight (UInt256.ofNat 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)
    (UInt256.sub (UInt256.ofNat 255) bit)
  else UInt256.lnot (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) bit) (UInt256.ofNat 1))

def tickScanMaskExpr (lte : Bool) : Expr :=
  if lte then .binary (.shr (.uint ⟨256, by decide⟩))
    (.intLit 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)
    (.binary .sub (.intLit 255) (.var "bitPos"))
  else .unary (.bitNot (.uint ⟨256, by decide⟩))
    (.cast (.binary .sub (.binary (.shl (.uint ⟨256, by decide⟩)) (.intLit 1) (.var "bitPos"))
      (.intLit 1)) (.elem (.int (.uint ⟨256, by decide⟩))))

theorem tickScanMax_toNat : (UInt256.ofNat 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff).toNat =
    0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff := by decide +kernel

theorem tickScanMax_eval {cfg : Config} {f : Frame} {evm : EVM.State} :
    evalExpr? cfg f evm (.intLit 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff) =
      .ok (.int (Int.ofNat (UInt256.ofNat 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff).toNat)) := by
  rw [tickScanMax_toNat]
  simp only [evalExpr?, pure]
  rfl

theorem tickScanMask_left_eval {f : Frame} {evm : EVM.State} {bit : UInt256}
    (hb : bit.toNat < 256) (he : f.locals.get? "bitPos" = some (.int (Int.ofNat bit.toNat))) :
    evalExpr? config f evm (tickScanMaskExpr true) = .ok (.int (Int.ofNat (tickScanMask bit true).toNat)) := by
  simp only [tickScanMaskExpr, tickScanMask, ↓reduceIte]
  have h255 : evalExpr? config f evm (.intLit 255) =
      .ok (.int (Int.ofNat (UInt256.ofNat 255).toNat)) := by simp only [evalExpr?, pure]; rfl
  have hsub := subSourceOk h255 (evalLocalValue he) (by change bit.toNat ≤ 255; omega)
  exact evalWordShrWord tickScanMax_eval hsub

theorem tickScanMask_right_eval {f : Frame} {evm : EVM.State} {bit : UInt256}
    (hb : bit.toNat < 256) (he : f.locals.get? "bitPos" = some (.int (Int.ofNat bit.toNat))) :
    evalExpr? config f evm (tickScanMaskExpr false) = .ok (.int (Int.ofNat (tickScanMask bit false).toNat)) := by
  have hshift := evalWordShl (n := bit.toNat) hb
      (show evalExpr? config f evm (.intLit 1) = .ok (.int (Int.ofNat (UInt256.ofNat 1).toNat)) by
        simp only [evalExpr?, pure]; rfl) (evalLocalValue he)
  simp only [u256_ofNat_toNat] at hshift
  exact evalWordNot (evalWordSub hshift
      (show evalExpr? config f evm (.intLit 1) = .ok (.int (Int.ofNat (UInt256.ofNat 1).toNat)) by
        simp only [evalExpr?, pure]; rfl))

theorem tickScanMask_eval {f : Frame} {evm : EVM.State} {bit : UInt256} (lte : Bool)
    (hb : bit.toNat < 256) (he : f.locals.get? "bitPos" = some (.int (Int.ofNat bit.toNat))) :
    evalExpr? config f evm (tickScanMaskExpr lte) = .ok (.int (Int.ofNat (tickScanMask bit lte).toNat)) := by
  cases lte with
  | true => exact tickScanMask_left_eval hb he
  | false => exact tickScanMask_right_eval hb he

theorem tickScanMask_compiled_right (bit : UInt256) :
    UInt256.lnot (UInt256.shiftLeft (UInt256.ofNat 1) bit + UInt256.ofNat (2^256-1)) =
      tickScanMask bit false := by
  change UInt256.lnot (UInt256.shiftLeft (UInt256.ofNat 1) bit + UInt256.lnot ⟨0⟩) = _
  rw [u256_add_lnot_zero_eq_sub_one]
  rfl

theorem tickScanMask_compiled_left (bit : UInt256) :
    UInt256.shiftRight (UInt256.ofNat 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)
      (UInt256.sub (UInt256.ofNat 255) bit) = tickScanMask bit true := by
  simp only [tickScanMask, if_true]

end Benchmarks.UniswapV4PoolManager
