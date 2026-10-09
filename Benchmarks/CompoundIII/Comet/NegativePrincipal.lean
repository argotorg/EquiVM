import Benchmarks.CompoundIII.Comet.PrincipalWords
import Benchmarks.CompoundIII.Comet.NarrowArithmetic

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 10000

theorem signed104_slt_neg {w : UInt256} (hp : signed104 w < 0) :
    UInt256.slt (UInt256.signextend ⟨12⟩ w) ⟨0⟩ ≠ ⟨0⟩ := by
  intro h
  have hb := signed104_bounds w
  have hn := int_nonneg_of_word_slt_zero (by omega) (by omega) (signed104_mod w) h
  omega

theorem signed104_slt_nonneg {w : UInt256} (hp : 0 ≤ signed104 w) :
    UInt256.slt (UInt256.signextend ⟨12⟩ w) ⟨0⟩ = ⟨0⟩ := by
  by_contra h
  have hb := signed104_bounds w
  have hn := int_neg_of_word_slt_ne_zero (by omega) (by omega) (signed104_mod w) h
  omega

def negativePrincipal (w : UInt256) : UInt256 := UInt256.ofNat (-signed104 w).toNat

theorem negativePrincipal_toNat (w : UInt256) :
    (negativePrincipal w).toNat = (-signed104 w).toNat := by
  apply UInt256.toNat_ofNat_of_lt
  have hb := signed104_bounds w
  change (-signed104 w).toNat < 2^256
  omega

theorem negativePrincipal_int {w : UInt256} (hp : signed104 w ≤ 0) :
    Int.ofNat (negativePrincipal w).toNat = -signed104 w := by
  rw [negativePrincipal_toNat]
  exact Int.toNat_of_nonneg (by omega)

theorem negativePrincipal_lt {w : UInt256} (hmin : -(2^103 : Int) < signed104 w) :
    (negativePrincipal w).toNat < 2^103 := by
  rw [negativePrincipal_toNat]
  omega

-- LIBRARY CANDIDATE: sign extension is idempotent at the same byte boundary.
theorem signextend104_idem (w : UInt256) :
    UInt256.signextend (UInt256.ofNat 12) (UInt256.signextend (UInt256.ofNat 12) w) =
      UInt256.signextend (UInt256.ofNat 12) w := by
  have hw (x : UInt256) : UInt256.signextend (UInt256.ofNat 12) x =
      ⟨(((⟨x.val⟩ : BitVec 256).setWidth 104).signExtend 256).toFin⟩ :=
    congrArg UInt256.mk (signextend104_bitvec (⟨x.val⟩ : BitVec 256))
  rw [hw w, hw]
  have hb (x : BitVec 256) :
      ((x.setWidth 104).signExtend 256 |>.setWidth 104).signExtend 256 =
        (x.setWidth 104).signExtend 256 := by bv_decide
  exact congrArg (fun x : BitVec 256 ↦ (⟨x.toFin⟩ : UInt256)) (hb ⟨w.val⟩)

-- LIBRARY CANDIDATE: decoding a signed field is unchanged by canonical sign extension.
theorem signed104_signextend (w : UInt256) :
    signed104 (UInt256.signextend (UInt256.ofNat 12) w) = signed104 w := by
  rw [signed104_bitvec, signed104_bitvec]
  have hw : UInt256.signextend (UInt256.ofNat 12) w =
      ⟨(((⟨w.val⟩ : BitVec 256).setWidth 104).signExtend 256).toFin⟩ :=
    congrArg UInt256.mk (signextend104_bitvec (⟨w.val⟩ : BitVec 256))
  rw [hw]
  have hb (x : BitVec 256) :
      ((x.setWidth 104).signExtend 256).setWidth 104 = x.setWidth 104 := by bv_decide
  exact congrArg BitVec.toInt (hb ⟨w.val⟩)

-- LIBRARY CANDIDATE: the additive inverse in the EVM word ring is involutive.
theorem wordZeroSubZeroSub (w : UInt256) :
    UInt256.sub (UInt256.ofNat 0) (UInt256.sub (UInt256.ofNat 0) w) = w := by
  apply u256_inj
  change (0 - (0 - w.val)).val = w.val.val
  rw [zero_sub, zero_sub, neg_neg]

theorem negativePrincipal_sub {w : UInt256} (hp : signed104 w ≤ 0) :
    UInt256.sub (UInt256.ofNat 0) (UInt256.signextend (UInt256.ofNat 12) w) =
      negativePrincipal w := by
  have henc : UInt256.signextend (UInt256.ofNat 12) w =
      UInt256.sub (UInt256.ofNat 0) (negativePrincipal w) := by
    change UInt256.signextend ⟨12⟩ w = _
    rw [← signed104_word]
    have he : signed104 w = -(Int.ofNat (negativePrincipal w).toNat) := by
      rw [negativePrincipal_int hp]
      omega
    rw [he]
    exact wordOfInt_neg_natCast_eq_sub_zero _
  rw [henc, wordZeroSubZeroSub]

def int104MinWord : UInt256 :=
  UInt256.lnot (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 103))
    (UInt256.ofNat 1))

theorem int104MinWord_toNat : int104MinWord.toNat = 2^256 - 2^103 := by decide

theorem signextend104_eq_min_iff (w : UInt256) :
    UInt256.signextend (UInt256.ofNat 12) w = int104MinWord ↔ signed104 w = -(2^103 : Int) := by
  have hm := signed104_mod w
  have hb := signed104_bounds w
  constructor
  · intro he
    change signed104 w % Int.ofNat EVM.wordModulus =
      Int.ofNat (UInt256.signextend (UInt256.ofNat 12) w).toNat at hm
    rw [he, int104MinWord_toNat] at hm
    norm_num [EVM.wordModulus, EVM.twoPow] at hm
    omega
  · intro he
    apply u256_inj
    rw [int104MinWord_toNat]
    change signed104 w % Int.ofNat EVM.wordModulus =
      Int.ofNat (UInt256.signextend (UInt256.ofNat 12) w).toNat at hm
    rw [he] at hm
    change (2^256 - 2^103 : Int) = Int.ofNat _ at hm
    simp only [Int.ofNat_eq_natCast] at hm
    omega

-- LIBRARY CANDIDATE: checked negation of a bounded signed integer.
theorem checkedPrincipalNegSource {cfg solm evm expr w}
    (he : evalExpr? cfg solm evm expr = .ok (.int (signed104 w)))
    (hp : signed104 w < 0) (hmin : -(2^103 : Int) < signed104 w) :
    evalExpr? cfg solm evm
      (.inRange (.sint ⟨104, by decide⟩) (.binary .sub (.intLit 0) expr)) =
      .ok (.int (negativePrincipal w).toNat) := by
  have h0 : ¬ (0 - signed104 w) < -(2^103 : Int) := by omega
  have h1 : ¬ (0 - signed104 w) ≥ (2^103 : Int) := by omega
  simp only [evalExpr?, he, pure, bind, EvalResult.bind, evalBinaryOp?, h0, h1,
    decide_false, Bool.or_self, Bool.false_eq_true, if_false]
  apply congrArg EvalResult.ok
  apply congrArg Value.int
  change 0 - signed104 w = Int.ofNat (negativePrincipal w).toNat
  rw [negativePrincipal_int (le_of_lt hp)]
  omega

theorem checkedPrincipalNegSource_revert {cfg solm evm expr w}
    (he : evalExpr? cfg solm evm expr = .ok (.int (signed104 w)))
    (hmin : signed104 w = -(2^103 : Int)) :
    evalExpr? cfg solm evm
      (.inRange (.sint ⟨104, by decide⟩) (.binary .sub (.intLit 0) expr)) = .revert := by
  simp only [evalExpr?, he, pure, bind, EvalResult.bind, evalBinaryOp?, hmin]
  rfl

end Benchmarks.CompoundIII.Comet
