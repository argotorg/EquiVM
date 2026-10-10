import Benchmarks.Morpho.MetaMorphoV1_1.MathMulDivDownSource

/-! The rounded-up quotient and the checked increment required for a nonzero remainder. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Morpho.MetaMorphoV1_1

set_option autoImplicit false

def mulDivRemainder (a b d : UInt256) : Nat := (a.toNat * b.toNat) % d.toNat

def mathMulDivUpWord (a b d : UInt256) : UInt256 :=
  if mulDivRemainder a b d = 0 then fullMulDivWord a b d else fullMulDivWord a b d + ⟨1⟩

def mathMulDivUpFits (a b d : UInt256) : Prop :=
  fullMulDivFits a b d ∧
    (mulDivRemainder a b d ≠ 0 → (fullMulDivWord a b d).toNat + 1 < UInt256.size)

-- LIBRARY CANDIDATE: natural-number multiplication followed by the nonzero modulus operation.
theorem naturalMulModSource {cfg : Config} {frame : Frame} {evm : State}
    {x y den : Expr} {a b d : UInt256}
    (ha : evalExpr? cfg frame evm x = .ok (uint256Value a))
    (hb : evalExpr? cfg frame evm y = .ok (uint256Value b))
    (hd : evalExpr? cfg frame evm den = .ok (uint256Value d)) (hn : d ≠ ⟨0⟩) :
    evalExpr? cfg frame evm (.binary .mod (.binary .mul x y) den) =
      .ok (.int (Int.ofNat ((a.toNat * b.toNat) % d.toNat))) := by
  have hz : (d.toNat : Int) ≠ 0 := by
    intro h
    exact hn (uint256_toNat_eq_zero (by omega))
  simp only [evalExpr?, ha, hb, hd, uint256Value, bind, EvalResult.bind, evalBinaryOp?,
    Int.ofNat_eq_natCast, ← Int.natCast_mul, hz, if_false, Int.natCast_emod]

theorem mulDivRemainder_zero_iff (a b d : UInt256) (hd : d ≠ ⟨0⟩) :
    mulDivRemainder a b d = 0 ↔ UInt256.mulMod a b d = ⟨0⟩ := by
  rw [mulDivRemainder, ← wordMulMod_toNat a b d hd]
  exact ⟨uint256_toNat_eq_zero, fun h ↦ by rw [h]; rfl⟩

end Benchmarks.Morpho.MetaMorphoV1_1
