import Benchmarks.Morpho.MetaMorphoV1_1.Arithmetic

/-! Exact decimal scaling and its uint256 overflow boundary. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables

namespace Benchmarks.Morpho.MetaMorphoV1_1

set_option autoImplicit false

def decimalScale (offset : UInt256) : UInt256 := UInt256.ofNat (10 ^ offset.toNat)

theorem decimalPower_fits {n : Nat} (hn : n ≤ 77) : 10 ^ n < UInt256.size :=
  lt_of_le_of_lt (Nat.pow_le_pow_right (by decide) hn) (by decide +kernel)

theorem decimalPower_overflow {n : Nat} (hn : 77 < n) : UInt256.size ≤ 10 ^ n :=
  le_trans (by decide +kernel : UInt256.size ≤ 10 ^ 78)
    (Nat.pow_le_pow_right (by decide) (by omega))

theorem decimalScale_toNat {offset : UInt256} (ho : offset.toNat ≤ 77) :
    (decimalScale offset).toNat = 10 ^ offset.toNat :=
  UInt256.toNat_ofNat_of_lt (decimalPower_fits ho)

theorem decimalScale_exp {offset : UInt256} (ho : offset.toNat ≤ 77) :
    UInt256.exp ⟨10⟩ offset = decimalScale offset := by
  have h : ∀ n : Fin 78, UInt256.exp ⟨10⟩ (UInt256.ofNat n.val) =
      UInt256.ofNat (10 ^ n.val) := by decide +kernel
  have hs := h ⟨offset.toNat, by omega⟩
  simpa only [u256_ofNat_toNat] using hs

theorem naturalPowerSource {cfg : Config} {frame : Frame} {evm : State}
    {base exponent : Expr} {a n : Nat}
    (ha : evalExpr? cfg frame evm base = .ok (.int (Int.ofNat a)))
    (hn : evalExpr? cfg frame evm exponent = .ok (.int (Int.ofNat n))) :
    evalExpr? cfg frame evm (.binary .exp base exponent) =
      .ok (.int (Int.ofNat (a ^ n))) := by
  have hz : ¬ (n : Int) < 0 := by omega
  simp only [evalExpr?, ha, hn, bind, EvalResult.bind, evalBinaryOp?,
    Int.ofNat_eq_natCast, hz, if_false, Int.toNat_natCast,
    Int.natCast_pow]

def decimalScaleExpr (exponent : Expr) : Expr :=
  .inRange (.uint ⟨256, by decide⟩) (.binary .exp (.intLit 10) exponent)

theorem decimalScaleSource {cfg : Config} {frame : Frame} {evm : State}
    {exponent : Expr} {offset : UInt256}
    (ho : evalExpr? cfg frame evm exponent = .ok (uint256Value offset))
    (hfit : offset.toNat ≤ 77) :
    evalExpr? cfg frame evm (decimalScaleExpr exponent) =
      .ok (uint256Value (decimalScale offset)) := by
  have hp := naturalPowerSource (show evalExpr? cfg frame evm (.intLit 10) =
    .ok (.int (Int.ofNat 10)) by simp only [evalExpr?, pure]; rfl) ho
  have hr := evalExpr_uintInRange ⟨256, by decide⟩ hp (decimalPower_fits hfit)
  simpa only [uint256Value, decimalScale_toNat hfit] using hr

theorem decimalScaleSourceRevert {cfg : Config} {frame : Frame} {evm : State}
    {exponent : Expr} {offset : UInt256}
    (ho : evalExpr? cfg frame evm exponent = .ok (uint256Value offset))
    (hbad : 77 < offset.toNat) :
    evalExpr? cfg frame evm (decimalScaleExpr exponent) = .revert := by
  exact evalExpr_uintInRange_revert ⟨256, by decide⟩
    (naturalPowerSource (show evalExpr? cfg frame evm (.intLit 10) =
      .ok (.int (Int.ofNat 10)) by simp only [evalExpr?, pure]; rfl) ho)
    (decimalPower_overflow hbad)

theorem decimalsOffsetCall (v : MetaMorphoV1_1Immutables) (locals : Store) (evm : State)
    (ret : Ident) :
    ExecStmt config { contract := contract, locals := locals, immutables := immStore v } evm
      (.internalCall "_decimalsOffset" [] ret)
      (.ok
        { contract := contract
          locals := locals.insert ret (uint256Value v.DECIMALS_OFFSET)
          immutables := immStore v } evm) := by
  exact internalCallReturnExpr rfl (evalImmutable_DECIMALS_OFFSET _ _ _ _ v)

end Benchmarks.Morpho.MetaMorphoV1_1
