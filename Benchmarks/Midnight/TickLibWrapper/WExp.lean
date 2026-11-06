import Benchmarks.Midnight.TickLibWrapper.Dispatch
import Reasoning.SteleBody
import Reasoning.WordArithmetic

/-!
# TickLibWrapper `wExp(int256)`

Per-function proof: calldata decode facts, the EVM trace from the dispatcher arm through the
internal `wExp` routine (pc 591 → 636 → 123; negative inputs round-trip through 600/610/617;
`x = -2^255` never terminates — the spec's `require(x != -2^255)` reverts, matched by
`execResultsEquiv.stackOverflowHalt`/`outOfGas`), and the `…Body` theorem `Correct.lean` consumes.
Dispatcher arm entry: pc 93; reach lemma `tickLibWrapperReachWExpBody`.
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight.TickLibWrapper

set_option maxRecDepth 2000000

/-! ## Model (Int-level, matching `wExp_body` including the `int256`/`uint256` casts) -/

private abbrev sint256I : IntType := .sint ⟨256, by decide⟩
private abbrev uint256I : IntType := .uint ⟨256, by decide⟩
private abbrev sint256S : StorageType := .elem (.int sint256I)
private abbrev uint256S : StorageType := .elem (.int uint256I)

private abbrev LN2I : Int := 693147180559945309
private abbrev OFFI : Int := 322611214989459870
private abbrev WADI : Int := 1000000000000000000
private abbrev ONE36I : Int := 1000000000000000000000000000000000000
private abbrev MINI : Int :=
  -(57896044618658097711785492504343953926634992332820282019728792003956564819968)

/-- `q = int256(sdiv(int256(x + OFFSET), LN2))` as the spec computes it. -/
def wExpQ (x : Int) : Int :=
  normalizeInt sint256I (Int.tdiv (normalizeInt sint256I (x + OFFI)) LN2I)

/-- `r = int256(x - int256(q * LN2))`. -/
def wExpR (x : Int) : Int :=
  normalizeInt sint256I (x - normalizeInt sint256I (wExpQ x * LN2I))

/-- `secondTerm = int256(sdiv(int256(r * r), 2e18))`. -/
def wExpS (x : Int) : Int :=
  normalizeInt sint256I (Int.tdiv (normalizeInt sint256I (wExpR x * wExpR x)) (2 * WADI))

/-- `thirdTerm = int256(sdiv(int256(secondTerm * r), 3e18))`. -/
def wExpT (x : Int) : Int :=
  normalizeInt sint256I (Int.tdiv (normalizeInt sint256I (wExpS x * wExpR x)) (3 * WADI))

/-- `expR = int256(int256(int256(1e18 + r) + secondTerm) + thirdTerm)`. -/
def wExpE (x : Int) : Int :=
  normalizeInt sint256I
    (normalizeInt sint256I (normalizeInt sint256I (WADI + wExpR x) + wExpS x) + wExpT x)

/-- `uint256(expR) <<[uint256] uint256(q)` — the `.shl` result, `0` when `q ≥ 256`. -/
def wExpPos (x : Int) : Int :=
  let s := normalizeInt uint256I (wExpQ x)
  if (256 : Int) ≤ s then 0
  else normalizeInt uint256I
    (normalizeInt uint256I (wExpE x) * Int.ofNat (EVM.twoPow s.toNat))

/-- The full `wExp_body` result: the negative branch divides `1e36` by the positive-branch
    value of `-x` (revert when that is `0`). -/
def wExpVal (x : Int) : Int :=
  if x < 0 then ONE36I / wExpPos (-x) else wExpPos x


/-! ## Word-level bridges (local; `Reasoning/` has `wordOfInt_add_words`/`_sub_toUInt256` only for
    `ofNat` arguments — these cover arbitrary `Int` operations) -/

theorem mod_pred_of_succ_mod_eq_zero {n M : Nat} (hM : 0 < M) (h : (n + 1) % M = 0) :
    n % M = M - 1 := by
  obtain ⟨k, hk⟩ := Nat.dvd_of_mod_eq_zero h
  rcases k with _ | k'
  · simp at hk
  · rw [Nat.mul_succ] at hk
    have hn : n = k' * M + (M - 1) := by
      rw [Nat.mul_comm M k'] at hk; omega
    rw [hn, Nat.add_comm, Nat.mul_comm k' M, Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt (by omega)]

theorem mod_succ_of_succ_mod_ne_zero {n M : Nat} (hM : 0 < M) (h : (n + 1) % M ≠ 0) :
    (n + 1) % M = n % M + 1 := by
  have hlt : n % M < M := Nat.mod_lt _ hM
  have hne : n % M + 1 ≠ M := by
    intro he
    have hd := Nat.div_add_mod n M
    have h1 : (n + 1) % M = 0 := by
      have h2 : n + 1 = (n / M + 1) * M := by
        rw [Nat.add_mul, Nat.one_mul]
        rw [Nat.mul_comm] at hd
        omega
      rw [h2]
      exact Nat.mod_eq_zero_of_dvd ⟨n / M + 1, by rw [Nat.mul_comm]⟩
    exact h h1
  have hlt1 : n % M + 1 < M := by omega
  have h2 : n + 1 = (n / M) * M + (n % M + 1) := by
    have hd := Nat.div_add_mod n M
    rw [Nat.mul_comm] at hd
    omega
  rw [h2, Nat.add_comm, Nat.mul_comm (n / M) M, Nat.add_mul_mod_self_left,
    Nat.mod_eq_of_lt hlt1]

theorem wordOfInt_toNat (i : Int) :
    (EVM.wordOfInt i).toNat = Int.toNat (i % Int.ofNat EVM.wordModulus) := by
  rcases i with n | n
  · have h0 : EVM.wordOfInt (Int.ofNat n) = EVM.word n := by
      unfold EVM.wordOfInt; simp
    rw [h0]; rfl
  · have hnn : (Int.negSucc n).natAbs = n + 1 := rfl
    have hMpos : (0:Int) < Int.ofNat EVM.wordModulus := by
      norm_num [EVM.wordModulus, EVM.twoPow]
    have hMn : (0:Nat) < EVM.wordModulus := by norm_num [EVM.wordModulus, EVM.twoPow]
    rcases eq_or_ne ((n + 1) % EVM.wordModulus) 0 with hr | hr
    · have h0 : EVM.wordOfInt (Int.negSucc n) = ⟨0⟩ := by
        simp only [EVM.wordOfInt, if_pos (Int.negSucc_lt_zero n), hnn, hr, if_true]
      rw [h0]
      have hnm : n % EVM.wordModulus = EVM.wordModulus - 1 :=
        mod_pred_of_succ_mod_eq_zero hMn hr
      have hmod : Int.negSucc n % Int.ofNat EVM.wordModulus = 0 := by
        rw [Int.negSucc_emod _ hMpos]
        show Int.ofNat EVM.wordModulus - 1 - (Int.ofNat n % Int.ofNat EVM.wordModulus) = 0
        have hcast : Int.ofNat n % Int.ofNat EVM.wordModulus =
            Int.ofNat (EVM.wordModulus - 1) := by
          have hrfl : Int.ofNat n % Int.ofNat EVM.wordModulus =
              Int.ofNat (n % EVM.wordModulus) := rfl
          rw [hrfl, hnm]
        rw [hcast]
        norm_num [EVM.wordModulus, EVM.twoPow]
      rw [hmod]
      rfl
    · have h0 : EVM.wordOfInt (Int.negSucc n) =
          EVM.word (EVM.wordModulus - (n + 1) % EVM.wordModulus) := by
        simp only [EVM.wordOfInt, if_pos (Int.negSucc_lt_zero n), hnn, hr, if_false]
      rw [h0, EVM.word]
      have hnm : (n + 1) % EVM.wordModulus = n % EVM.wordModulus + 1 :=
        mod_succ_of_succ_mod_ne_zero hMn hr
      have hk1 : n % EVM.wordModulus + 1 ≤ EVM.wordModulus := by
        have hlt1 := Nat.mod_lt (n + 1) hMn
        omega
      have hmod : Int.negSucc n % Int.ofNat EVM.wordModulus =
          Int.ofNat (EVM.wordModulus - (n + 1) % EVM.wordModulus) := by
        rw [Int.negSucc_emod _ hMpos, hnm]
        show Int.ofNat EVM.wordModulus - 1 - (Int.ofNat n % Int.ofNat EVM.wordModulus) = _
        have hcast : Int.ofNat n % Int.ofNat EVM.wordModulus =
            Int.ofNat (n % EVM.wordModulus) := rfl
        rw [hcast]
        simp only [Int.ofNat_eq_natCast]
        push_cast
        omega
      rw [hmod]
      have hltX : EVM.wordModulus - (n + 1) % EVM.wordModulus < EVM.twoPow 256 := by
        have : EVM.twoPow 256 = EVM.wordModulus := rfl
        omega
      have h1 : (EVM.word (EVM.wordModulus - (n + 1) % EVM.wordModulus)).toNat =
          EVM.wordModulus - (n + 1) % EVM.wordModulus := by
        rw [show (EVM.word (EVM.wordModulus - (n + 1) % EVM.wordModulus)).toNat =
            (EVM.wordModulus - (n + 1) % EVM.wordModulus) % EVM.twoPow 256 from rfl]
        exact Nat.mod_eq_of_lt hltX
      have h2 : (EVM.word (EVM.wordModulus - (n + 1) % EVM.wordModulus)) =
          { val := EVM.uintN 256 (EVM.wordModulus - (n + 1) % EVM.wordModulus) } := rfl
      rw [← h2, h1]
      rfl

theorem wordOfInt_emod (i : Int) :
    EVM.wordOfInt (i % Int.ofNat EVM.wordModulus) = EVM.wordOfInt i := by
  apply Reasoning.Theory.u256_inj
  rw [wordOfInt_toNat, wordOfInt_toNat]
  rw [Int.emod_emod]

theorem wordOfInt_add (a b : Int) :
    EVM.wordOfInt (a + b) = EVM.wordOfInt a + EVM.wordOfInt b := by
  apply Reasoning.Theory.u256_inj
  rw [show (EVM.wordOfInt a + EVM.wordOfInt b).toNat =
      ((EVM.wordOfInt a).toNat + (EVM.wordOfInt b).toNat) % UInt256.size from rfl]
  rw [wordOfInt_toNat, wordOfInt_toNat, wordOfInt_toNat]
  have hM : UInt256.size = EVM.wordModulus := rfl
  rw [hM]
  have hMpos : (0:Int) < Int.ofNat EVM.wordModulus := by norm_num [EVM.wordModulus, EVM.twoPow]
  have ha := Int.emod_nonneg a (ne_of_gt hMpos)
  have hb := Int.emod_nonneg b (ne_of_gt hMpos)
  have e1 : (a + b) % Int.ofNat EVM.wordModulus =
      Int.ofNat ((Int.toNat (a % Int.ofNat EVM.wordModulus) +
        Int.toNat (b % Int.ofNat EVM.wordModulus)) % EVM.wordModulus) := by
    rw [Int.add_emod, ← Int.toNat_of_nonneg ha, ← Int.toNat_of_nonneg hb]
    rfl
  rw [e1]; rfl

theorem wordOfInt_mul (a b : Int) :
    EVM.wordOfInt (a * b) = EVM.wordOfInt a * EVM.wordOfInt b := by
  apply Reasoning.Theory.u256_inj
  rw [show (EVM.wordOfInt a * EVM.wordOfInt b).toNat =
      ((EVM.wordOfInt a).toNat * (EVM.wordOfInt b).toNat) % UInt256.size from rfl]
  rw [wordOfInt_toNat, wordOfInt_toNat, wordOfInt_toNat]
  have hM : UInt256.size = EVM.wordModulus := rfl
  rw [hM]
  have hMpos : (0:Int) < Int.ofNat EVM.wordModulus := by norm_num [EVM.wordModulus, EVM.twoPow]
  have ha := Int.emod_nonneg a (ne_of_gt hMpos)
  have hb := Int.emod_nonneg b (ne_of_gt hMpos)
  have e1 : (a * b) % Int.ofNat EVM.wordModulus =
      Int.ofNat ((Int.toNat (a % Int.ofNat EVM.wordModulus) *
        Int.toNat (b % Int.ofNat EVM.wordModulus)) % EVM.wordModulus) := by
    rw [Int.mul_emod, ← Int.toNat_of_nonneg ha, ← Int.toNat_of_nonneg hb]
    rfl
  rw [e1]; rfl


theorem wordOfInt_sintNorm (i : Int) :
    EVM.wordOfInt (normalizeInt (.sint ⟨256, by decide⟩) i) = EVM.wordOfInt i := by
  apply Reasoning.Theory.u256_inj
  rw [wordOfInt_toNat, wordOfInt_toNat]
  have hunf : normalizeInt (.sint ⟨256, by decide⟩) i =
      (if (i % Int.ofNat (EVM.twoPow 256)) < Int.ofNat (EVM.twoPow 255)
        then i % Int.ofNat (EVM.twoPow 256)
        else i % Int.ofNat (EVM.twoPow 256) - Int.ofNat (EVM.twoPow 256)) := rfl
  rw [hunf]
  have hM : Int.ofNat (EVM.twoPow 256) = Int.ofNat EVM.wordModulus := rfl
  rw [hM]
  split
  · rw [Int.emod_emod]
  · rw [Int.sub_emod_right, Int.emod_emod]

theorem wordOfInt_uintNorm (i : Int) :
    EVM.wordOfInt (normalizeInt (.uint ⟨256, by decide⟩) i) = EVM.wordOfInt i := by
  have hunf : normalizeInt (.uint ⟨256, by decide⟩) i =
      i % Int.ofNat (EVM.twoPow 256) := rfl
  rw [hunf]
  have hM : Int.ofNat (EVM.twoPow 256) = Int.ofNat EVM.wordModulus := rfl
  rw [hM]
  exact wordOfInt_emod i

theorem signed_of_lt (w : UInt256) (h : w.toNat < EVM.signBit) :
    EVM.signed w = Int.ofNat w.toNat := by
  show (if ↑w.val < EVM.signBit then Int.ofNat ↑w.val else Int.ofNat ↑w.val - Int.ofNat EVM.wordModulus) = Int.ofNat w.toNat
  rw [if_pos (show ↑w.val < EVM.signBit from h)]
  rfl

theorem signed_of_ge (w : UInt256) (h : EVM.signBit ≤ w.toNat) :
    EVM.signed w = Int.ofNat w.toNat - Int.ofNat EVM.wordModulus := by
  show (if ↑w.val < EVM.signBit then Int.ofNat ↑w.val else Int.ofNat ↑w.val - Int.ofNat EVM.wordModulus) = _
  rw [if_neg (show ¬ ↑w.val < EVM.signBit from not_lt.mpr h)]
  congr 2

theorem wordOfInt_signed (w : UInt256) :
    EVM.wordOfInt (EVM.signed w) = w := by
  apply Reasoning.Theory.u256_inj
  rw [wordOfInt_toNat]
  have hlt' : w.toNat < EVM.wordModulus := w.val.isLt
  rcases lt_or_ge w.toNat EVM.signBit with hlt | hge
  · rw [signed_of_lt w hlt]
    have hrw : (Int.ofNat w.toNat) % Int.ofNat EVM.wordModulus =
        Int.ofNat w.toNat := by
      rw [show (Int.ofNat w.toNat) % Int.ofNat EVM.wordModulus =
          Int.ofNat (w.toNat % EVM.wordModulus) from rfl]
      rw [Nat.mod_eq_of_lt hlt']
    rw [hrw]; rfl
  · rw [signed_of_ge w hge]
    have hrw : (Int.ofNat w.toNat - Int.ofNat EVM.wordModulus) % Int.ofNat EVM.wordModulus =
        Int.ofNat w.toNat := by
      rw [Int.sub_emod_right]
      rw [show (Int.ofNat w.toNat) % Int.ofNat EVM.wordModulus =
          Int.ofNat (w.toNat % EVM.wordModulus) from rfl]
      rw [Nat.mod_eq_of_lt hlt']
    rw [hrw]; rfl

theorem wordOfInt_sub (a b : Int) :
    EVM.wordOfInt (a - b) = EVM.wordOfInt a - EVM.wordOfInt b := by
  apply Reasoning.Theory.u256_inj
  rw [show (EVM.wordOfInt a - EVM.wordOfInt b).toNat =
      ((UInt256.size - (EVM.wordOfInt b).toNat) + (EVM.wordOfInt a).toNat) %
        UInt256.size from rfl]
  rw [wordOfInt_toNat, wordOfInt_toNat, wordOfInt_toNat]
  have hM : UInt256.size = EVM.wordModulus := rfl
  rw [hM]
  have hMpos : (0:Int) < Int.ofNat EVM.wordModulus := by norm_num [EVM.wordModulus, EVM.twoPow]
  have ha := Int.emod_nonneg a (ne_of_gt hMpos)
  have hb := Int.emod_nonneg b (ne_of_gt hMpos)
  have e1 : (a - b) % Int.ofNat EVM.wordModulus =
      Int.ofNat (((EVM.wordModulus - Int.toNat (b % Int.ofNat EVM.wordModulus)) +
        Int.toNat (a % Int.ofNat EVM.wordModulus)) % EVM.wordModulus) := by
    have hbM : (b % Int.ofNat EVM.wordModulus).toNat ≤ EVM.wordModulus := by
      have h2 := Int.emod_lt_of_pos b hMpos
      have h2' := Int.emod_nonneg b (ne_of_gt hMpos)
      have h3 : (b % Int.ofNat EVM.wordModulus).toNat < EVM.wordModulus := by
        rw [Int.toNat_lt h2']
        exact h2
      omega
    have hbM' : (b % ↑EVM.wordModulus).toNat ≤ EVM.wordModulus := hbM
    have hsub : (a - b) % Int.ofNat EVM.wordModulus =
        (a % Int.ofNat EVM.wordModulus - b % Int.ofNat EVM.wordModulus) %
          Int.ofNat EVM.wordModulus := by
      rw [Int.emod_sub_emod, Int.sub_emod_emod]
    rw [hsub]
    have hA : a % Int.ofNat EVM.wordModulus = Int.ofNat (Int.toNat (a % Int.ofNat EVM.wordModulus)) :=
      (Int.toNat_of_nonneg ha).symm
    have hB : b % Int.ofNat EVM.wordModulus = Int.ofNat (Int.toNat (b % Int.ofNat EVM.wordModulus)) :=
      (Int.toNat_of_nonneg hb).symm
    conv_lhs => rw [hA, hB]
    rw [show Int.ofNat (Int.toNat (a % Int.ofNat EVM.wordModulus)) -
          Int.ofNat (Int.toNat (b % Int.ofNat EVM.wordModulus)) =
        (Int.ofNat (Int.toNat (a % Int.ofNat EVM.wordModulus)) +
          Int.ofNat EVM.wordModulus - Int.ofNat (Int.toNat (b % Int.ofNat EVM.wordModulus))) -
          Int.ofNat EVM.wordModulus from by omega]
    rw [Int.sub_emod_right]
    rw [show Int.ofNat (Int.toNat (a % Int.ofNat EVM.wordModulus)) +
        Int.ofNat EVM.wordModulus - Int.ofNat (Int.toNat (b % Int.ofNat EVM.wordModulus)) =
        Int.ofNat (Int.toNat (a % Int.ofNat EVM.wordModulus) +
          (EVM.wordModulus - Int.toNat (b % Int.ofNat EVM.wordModulus))) from by
      have e : Int.ofNat (Int.toNat (a % Int.ofNat EVM.wordModulus)) + Int.ofNat EVM.wordModulus =
          Int.ofNat (Int.toNat (a % Int.ofNat EVM.wordModulus) + EVM.wordModulus) := rfl
      rw [e]
      simp only [Int.ofNat_eq_natCast]
      rw [← Nat.cast_sub]
      · congr 1
        omega
      · have hbM'' : (b % ↑EVM.wordModulus).toNat ≤
            Int.toNat (a % ↑EVM.wordModulus) + EVM.wordModulus := by omega
        omega]
    rw [show Int.ofNat (Int.toNat (a % Int.ofNat EVM.wordModulus) +
          (EVM.wordModulus - Int.toNat (b % Int.ofNat EVM.wordModulus))) %
          Int.ofNat EVM.wordModulus =
        Int.ofNat ((Int.toNat (a % Int.ofNat EVM.wordModulus) +
          (EVM.wordModulus - Int.toNat (b % Int.ofNat EVM.wordModulus))) %
            EVM.wordModulus) from rfl]
    rw [Nat.add_comm (EVM.wordModulus - Int.toNat (b % Int.ofNat EVM.wordModulus))]
  rw [e1]
  rfl

theorem mul_sub_one_decomp (x s : Nat) (hx : 1 ≤ x) (h2 : x ≤ s) :
    x * (s - 1) = (x - 1) * s + (s - x) := by
  have e : (x - 1) * s + s - x = (x - 1) * s + (s - x) := Nat.add_sub_assoc h2 _
  rw [← e]
  have e2 : (x - 1) * s + s = x * s := by
    rw [← Nat.succ_mul (x - 1) s]
    congr 1
    omega
  rw [e2]
  rw [Nat.mul_sub, Nat.mul_one]

theorem finMulNeg_toNat' (x : UInt256) :
    (x.val * -1).val = if x.toNat = 0 then 0 else UInt256.size - x.toNat := by
  by_cases h : x.toNat = 0
  · rw [if_pos h]
    have hx : x.val = ⟨0, by have := x.val.isLt; omega⟩ := Fin.ext h
    rw [hx]
    show ((0 : Nat) * ((UInt256.size - 1) % UInt256.size)) % UInt256.size = 0
    rfl
  · rw [if_neg h]
    have hsize : 0 < UInt256.size := by norm_num [UInt256.size]
    have h1 : (x.val * -1).val = (x.val.val * ((UInt256.size - 1) % UInt256.size)) % UInt256.size := rfl
    rw [h1, Nat.mod_eq_of_lt (by omega : UInt256.size - 1 < UInt256.size)]
    have hxv : x.val.val = x.toNat := rfl
    have hlt : x.toNat < UInt256.size := x.val.isLt
    rw [hxv, mul_sub_one_decomp _ _ (Nat.pos_of_ne_zero h) hlt.le]
    rw [Nat.add_comm, Nat.mul_comm (x.toNat - 1) _, Nat.add_mul_mod_self_left]
    exact Nat.mod_eq_of_lt (by omega)


theorem wordOfInt_sdiv_pos (a b : UInt256) (hb : b.toNat < EVM.signBit) :
    UInt256.sdiv a b =
      EVM.wordOfInt (Int.tdiv (EVM.signed a) (EVM.signed b)) := by
  rcases lt_or_ge a.toNat EVM.signBit with ha | ha
  · rw [signed_of_lt _ ha, signed_of_lt _ hb]
    have ht : Int.tdiv (Int.ofNat a.toNat) (Int.ofNat b.toNat) =
        Int.ofNat (a.toNat / b.toNat) := rfl
    rw [ht]
    apply Reasoning.Theory.u256_inj
    rw [wordOfInt_toNat]
    unfold UInt256.sdiv
    rw [if_neg (not_le_of_gt (show a.toNat < 2 ^ 255 from ha)),
        if_neg (not_le_of_gt (show b.toNat < 2 ^ 255 from hb))]
    have hud : (a / b).toNat = a.toNat / b.toNat := rfl
    rw [hud]
    rw [show (Int.ofNat (a.toNat / b.toNat)) % Int.ofNat EVM.wordModulus =
        Int.ofNat ((a.toNat / b.toNat) % EVM.wordModulus) from rfl]
    show a.toNat / b.toNat = (a.toNat / b.toNat) % EVM.wordModulus
    exact (Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.div_le_self _ _) a.val.isLt)).symm
  · rw [signed_of_ge _ ha, signed_of_lt _ hb]
    have hMpos : (0:Int) < Int.ofNat EVM.wordModulus := by norm_num [EVM.wordModulus, EVM.twoPow]
    have hsb2 : EVM.signBit = 2 ^ 255 := rfl
    rw [hsb2] at ha
    have haM : a.toNat < EVM.wordModulus := a.val.isLt
    have hsa' : Int.ofNat a.toNat - Int.ofNat EVM.wordModulus =
        -Int.ofNat (EVM.wordModulus - a.toNat) := by
      rw [show Int.ofNat (EVM.wordModulus - a.toNat) =
          Int.ofNat EVM.wordModulus - Int.ofNat a.toNat from by
        simp only [Int.ofNat_eq_natCast]
        exact Nat.cast_sub (by omega : a.toNat ≤ EVM.wordModulus)]
      ring
    rw [hsa', Int.neg_tdiv]
    have ht : Int.tdiv (Int.ofNat (EVM.wordModulus - a.toNat)) (Int.ofNat b.toNat) =
        Int.ofNat ((EVM.wordModulus - a.toNat) / b.toNat) := rfl
    rw [ht]
    unfold UInt256.sdiv
    rw [if_pos ha, if_neg (not_le_of_gt (show b.toNat < 2 ^ 255 from hb))]
    apply Reasoning.Theory.u256_inj
    rw [wordOfInt_toNat]
    -- `(⟨(abs a / b).val * -1⟩).toNat = if j = 0 then 0 else M - j`
    have habs : (UInt256.abs a).toNat = EVM.wordModulus - a.toNat := by
      unfold UInt256.abs
      rw [if_pos ha]
      have h1 : (a.val * -1).val = if a.toNat = 0 then 0 else UInt256.size - a.toNat :=
        finMulNeg_toNat' a
      rw [UInt256.toNat]
      rw [h1, if_neg (by omega : a.toNat ≠ 0)]
      rfl
    have hdiv : (UInt256.abs a / b).toNat = (EVM.wordModulus - a.toNat) / b.toNat := by
      rw [show (UInt256.abs a / b).toNat = (UInt256.abs a).toNat / b.toNat from rfl, habs]
    have hl : (⟨(UInt256.abs a / b).val * -1⟩ : UInt256).toNat =
        if (UInt256.abs a / b).toNat = 0 then 0
        else UInt256.size - (UInt256.abs a / b).toNat := by
      rw [UInt256.toNat]
      exact finMulNeg_toNat' (UInt256.abs a / b)
    rw [hl, hdiv]
    -- `wordOfInt (-ofNat j).toNat = if j = 0 then 0 else M - j`
    have hjM : (EVM.wordModulus - a.toNat) / b.toNat ≤ EVM.wordModulus := by
      have h1 : (EVM.wordModulus - a.toNat) / b.toNat ≤ EVM.wordModulus - a.toNat :=
        Nat.div_le_self _ _
      omega
    have hjlt : (EVM.wordModulus - a.toNat) / b.toNat < EVM.wordModulus := by
      have h1 : (EVM.wordModulus - a.toNat) / b.toNat ≤ EVM.wordModulus - a.toNat :=
        Nat.div_le_self _ _
      omega
    have hneg : (-Int.ofNat ((EVM.wordModulus - a.toNat) / b.toNat)) %
        Int.ofNat EVM.wordModulus =
        if (EVM.wordModulus - a.toNat) / b.toNat = 0 then (0:Int)
        else Int.ofNat (EVM.wordModulus - (EVM.wordModulus - a.toNat) / b.toNat) := by
      rw [Int.neg_emod]
      rcases eq_or_ne ((EVM.wordModulus - a.toNat) / b.toNat) 0 with h | h
      · rw [h, if_pos rfl]
        norm_num
      · rw [if_neg h]
        have hnotdvd : ¬ Int.ofNat EVM.wordModulus ∣
            Int.ofNat ((EVM.wordModulus - a.toNat) / b.toNat) := by
          intro hd
          have hd' : EVM.wordModulus ∣ (EVM.wordModulus - a.toNat) / b.toNat :=
            Int.ofNat_dvd.mp hd
          have hle := Nat.le_of_dvd (Nat.pos_of_ne_zero h) hd'
          omega
        rw [if_neg hnotdvd]
        rw [show Int.ofNat ((EVM.wordModulus - a.toNat) / b.toNat) %
            Int.ofNat EVM.wordModulus =
            Int.ofNat (((EVM.wordModulus - a.toNat) / b.toNat) %
              EVM.wordModulus) from rfl]
        rw [Nat.mod_eq_of_lt hjlt]
        rw [show Int.natAbs (Int.ofNat EVM.wordModulus) = EVM.wordModulus from rfl]
        simp only [Int.ofNat_eq_natCast]
        rw [← Nat.cast_sub hjM]
    rw [hneg]
    rcases eq_or_ne ((EVM.wordModulus - a.toNat) / b.toNat) 0 with h | h
    · rw [h, if_pos rfl, if_pos rfl]
      rfl
    · rw [if_neg h, if_neg h]
      rfl

theorem wordOfInt_shiftLeft (x s : Int) (hs : 0 ≤ s) (hs' : s < Int.ofNat EVM.wordModulus) :
    UInt256.shiftLeft (EVM.wordOfInt x) (EVM.wordOfInt s) =
      EVM.wordOfInt
        (if (256 : Int) ≤ s then 0
         else normalizeInt (.uint ⟨256, by decide⟩)
           (x * Int.ofNat (EVM.twoPow s.toNat))) := by
  rcases lt_or_ge s 256 with hsL | hsL
  · have hsn : s.toNat < 256 := by omega
    have hwv : (EVM.wordOfInt s).toNat = s.toNat := by
      rw [wordOfInt_toNat, Int.emod_eq_of_lt hs hs']
    have hlt : (EVM.wordOfInt s).val.val < 256 := by
      show (EVM.wordOfInt s).toNat < 256
      rw [hwv]; exact hsn
    unfold UInt256.shiftLeft
    rw [if_neg (show ¬ (EVM.wordOfInt s).val >= 256 from by
      intro hc; exact absurd hlt (not_lt.mpr hc))]
    rw [if_neg (show ¬ (256 : Int) ≤ s from by omega)]
    rw [wordOfInt_uintNorm]
    apply Reasoning.Theory.u256_inj
    rw [wordOfInt_toNat]
    rw [show (⟨(EVM.wordOfInt x).val <<< (EVM.wordOfInt s).val⟩ : UInt256).toNat =
        ((EVM.wordOfInt x).toNat <<< (EVM.wordOfInt s).toNat) % UInt256.size from rfl]
    rw [hwv, Nat.shiftLeft_eq]
    have hMpos : (0:Int) < Int.ofNat EVM.wordModulus := by norm_num [EVM.wordModulus, EVM.twoPow]
    have hM : UInt256.size = EVM.wordModulus := rfl
    rw [hM]
    rw [wordOfInt_toNat]
    rw [show (x * Int.ofNat (EVM.twoPow s.toNat)) % Int.ofNat EVM.wordModulus =
        Int.ofNat (((x % Int.ofNat EVM.wordModulus).toNat * EVM.twoPow s.toNat) %
          EVM.wordModulus) from by
      rw [Int.mul_emod]
      have hx : x % Int.ofNat EVM.wordModulus =
          Int.ofNat (x % Int.ofNat EVM.wordModulus).toNat :=
        (Int.toNat_of_nonneg (Int.emod_nonneg x (ne_of_gt hMpos))).symm
      conv_lhs => rw [hx]
      rw [show Int.ofNat (EVM.twoPow s.toNat) % Int.ofNat EVM.wordModulus =
          Int.ofNat (EVM.twoPow s.toNat % EVM.wordModulus) from rfl]
      rw [Nat.mod_eq_of_lt (by
        have h1 : EVM.twoPow s.toNat < EVM.twoPow 256 :=
          Nat.pow_lt_pow_right (by decide) hsn
        have h2 : EVM.twoPow 256 = EVM.wordModulus := rfl
        omega)]
      rfl]
    rfl
  · have hge : s.toNat ≥ 256 := by omega
    have hwv : (EVM.wordOfInt s).toNat = s.toNat := by
      rw [wordOfInt_toNat, Int.emod_eq_of_lt hs hs']
    have hge' : (EVM.wordOfInt s).val.val ≥ 256 := by
      show (EVM.wordOfInt s).toNat ≥ 256
      rw [hwv]; exact hge
    unfold UInt256.shiftLeft
    rw [if_pos (show (EVM.wordOfInt s).val >= 256 from hge')]
    rw [if_pos hsL]
    exact wordOfInt_zero.symm


theorem signed_wordOfInt (i : Int) :
    EVM.signed (EVM.wordOfInt i) = normalizeInt sint256I i := by
  have hnn : 0 ≤ i % (2^256 : Int) := Int.emod_nonneg _ (by decide)
  have hM : Int.ofNat EVM.wordModulus = (2^256 : Int) := rfl
  have hSB : EVM.signBit = (2^255 : Nat) := rfl
  have hw : (EVM.wordOfInt i).val = (i % (2^256 : Int)).toNat := by
    rw [← UInt256.toNat, wordOfInt_toNat, hM]
  simp only [EVM.signed]
  unfold normalizeInt sint256I
  simp only
  rw [show Int.ofNat (EVM.twoPow 256) = (2^256 : Int) from rfl,
      show Int.ofNat (EVM.twoPow (256 - 1)) = (2^255 : Int) from rfl, hM]
  rw [hSB, hw]
  rw [show Int.ofNat (i % (2^256 : Int)).toNat = i % (2^256 : Int) from
    Int.toNat_of_nonneg hnn]
  by_cases hc : i % (2^256 : Int) < 2^255
  · rw [if_pos hc, if_pos (show (i % (2^256 : Int)).toNat < 2^255 from by omega)]
  · rw [if_neg hc, if_neg (show ¬ (i % (2^256 : Int)).toNat < 2^255 from by omega)]

/-- `sintNorm` is `≡ mod 2^256`-congruence-invariant in its first arg. -/
theorem sintNorm_cong (a b : Int) (h : a % 2^256 = b % 2^256) :
    normalizeInt sint256I a = normalizeInt sint256I b := by
  unfold normalizeInt sint256I
  simp only
  rw [show Int.ofNat (EVM.twoPow 256) = 2^256 from rfl,
      show Int.ofNat (EVM.twoPow (256 - 1)) = 2^255 from rfl, h]

/-! ## Stele-side body evaluation

`wExp_body` is an `internal` function; `wExpBodyStele` evaluates it for an arbitrary
`.int xv` parameter (locals `x ↦ .int xv`), splitting on the three cases of the
`require`/`ite` guard: `xv = -2^255` (revert), `xv ≥ 0` (approximation path),
`xv < 0` (recursive internal call on `-xv` then `1e36 / r`). -/

/-- The `wExp_body` internal `FunctionDecl` (first in `contract.functions`). -/
abbrev wExpBodyDecl : FunctionDecl := contract.functions[0]!

private abbrev minLit : Int :=
  57896044618658097711785492504343953926634992332820282019728792003956564819968

theorem evalVar_int (cfg : Config) (stele : Frame) (evm : EVM.State)
    {n : Ident} {i : Int} (h : stele.locals.get? n = some (.int i)) :
    evalExpr? cfg stele evm (.var n) = .ok (.int i) := by
  simp only [evalExpr?, h, EvalResult.ofOption]

/-- `sintNorm` of an already-in-range value is the identity. -/
theorem sintNorm_of_mem (i : Int) (h : -2^255 ≤ i) (h2 : i < 2^255) :
    normalizeInt sint256I i = i := by
  unfold normalizeInt sint256I
  simp only
  have hM : Int.ofNat (EVM.twoPow 256) = 2^256 := rfl
  have hS : Int.ofNat (EVM.twoPow (256 - 1)) = 2^255 := rfl
  rw [hM, hS]
  set residue := i % 2^256
  rcases lt_or_ge residue (2^255) with hr | hr
  · rw [if_pos hr]
    omega
  · rw [if_neg (not_lt.mpr hr)]
    have hri : i % 2^256 = i + 2^256 := by omega
    rw [show residue = i + 2^256 from hri]
    ring

/-- The `wExp_body` `require` guard passes for `xv ≠ -2^255`. -/
theorem wExpRequire_ok (cfg : Config) (stele : Frame) (evm : EVM.State) (xv : Int)
    (hxv : xv ≠ MINI) (hxloc : stele.locals.get? "x" = some (.int xv)) :
    evalExpr? cfg stele evm
      (.binary .ne (.var "x") (.unary .neg (.intLit minLit))) =
      .ok (.bool true) := by
  have hxv' : xv ≠ -minLit := hxv
  simp only [evalExpr?, hxloc, evalBinaryOp?, evalUnaryOp?,
    EvalResult.bind, bind, EvalResult.ofOption]
  simp [hxv']

/-- `wExp_body` at `xv ≥ 0`: require passes, `ite` takes the empty else-branch,
the five `letDecl`s evaluate to the model values, and `return` produces
`wExpPos xv` via the `.shl` semantics. -/
theorem wExpBodyStele_nonneg (cfg : Config) (caller : Frame) (evm : EVM.State)
    (xv : Int) (hpos : 0 ≤ xv)
    (hxloc : caller.locals.get? "x" = some (.int xv)) :
    ∃ stele', ExecFuncBody cfg caller evm wExpBodyDecl.body
      (.returned stele' evm (some [Value.int (wExpPos xv)])) := by
  have hreq := wExpRequire_ok cfg caller evm xv (by
    have hM : MINI = -2^255 := rfl
    omega : xv ≠ MINI) hxloc
  have hlt : evalExpr? cfg caller evm
      (.binary .lt (.var "x") (.intLit 0)) = .ok (.bool false) := by
    simp only [evalExpr?, hxloc, evalBinaryOp?,
      EvalResult.bind, bind, EvalResult.ofOption]
    simp [hpos]
  -- eval chain for `q := int256(sdiv(int256(x + OFFI), LN2I))`
  have hq : evalExpr? cfg caller evm
      (.cast (.binary .sdiv
        (.cast (.binary .add (.var "x") (.intLit OFFI)) sint256S)
        (.intLit LN2I)) sint256S) =
      .ok (.int (wExpQ xv)) := by
    unfold wExpQ OFFI LN2I
    simp only [evalExpr?, hxloc, evalBinaryOp?, castValue_int,
      EvalResult.bind, bind, EvalResult.ofOption]
    rw [if_neg (by decide)]
    simp only [EvalResult.bind, bind, castValue_int, EvalResult.ofOption]
  -- `r := int256(x - int256(q * LN2I))` — `q` now in scope.
  let caller1 := {caller with locals := caller.locals.insert "q" (.int (wExpQ xv))}
  have hqx : caller1.locals.get? "x" = some (.int xv) := by
    show (caller.locals.insert "q" _).get? "x" = _
    rw [store_get_ne _ _ (by decide : ("q" == "x") = false), hxloc]
  have hqq : caller1.locals.get? "q" = some (.int (wExpQ xv)) := store_get_self _ _ _
  have hr : evalExpr? cfg caller1 evm
      (.cast (.binary .sub (.var "x")
        (.cast (.binary .mul (.var "q") (.intLit LN2I)) sint256S)) sint256S) =
      .ok (.int (wExpR xv)) := by
    unfold wExpR LN2I
    simp only [evalExpr?, hqx, hqq, evalBinaryOp?, castValue_int,
      EvalResult.bind, bind, EvalResult.ofOption]
  -- `secondTerm := int256(sdiv(int256(r*r), 2e18))`
  let caller2 := {caller1 with locals := caller1.locals.insert "r" (.int (wExpR xv))}
  have hrr : caller2.locals.get? "r" = some (.int (wExpR xv)) := store_get_self _ _ _
  have hs : evalExpr? cfg caller2 evm
      (.cast (.binary .sdiv
        (.cast (.binary .mul (.var "r") (.var "r")) sint256S)
        (.intLit (2 * WADI))) sint256S) =
      .ok (.int (wExpS xv)) := by
    unfold wExpS WADI
    simp only [evalExpr?, hrr, evalBinaryOp?, castValue_int,
      EvalResult.bind, bind, EvalResult.ofOption]
    rw [if_neg (by decide)]
    simp only [EvalResult.bind, bind, castValue_int, EvalResult.ofOption]
  -- `thirdTerm := int256(sdiv(int256(secondTerm*r), 3e18))`
  let caller3 := {caller2 with locals := caller2.locals.insert "secondTerm" (.int (wExpS xv))}
  have hsr : caller3.locals.get? "r" = some (.int (wExpR xv)) := by
    show (caller2.locals.insert "secondTerm" _).get? "r" = _
    rw [store_get_ne _ _ (by decide : ("secondTerm" == "r") = false), hrr]
  have hss : caller3.locals.get? "secondTerm" = some (.int (wExpS xv)) := store_get_self _ _ _
  have ht : evalExpr? cfg caller3 evm
      (.cast (.binary .sdiv
        (.cast (.binary .mul (.var "secondTerm") (.var "r")) sint256S)
        (.intLit (3 * WADI))) sint256S) =
      .ok (.int (wExpT xv)) := by
    unfold wExpT WADI
    simp only [evalExpr?, hsr, hss, evalBinaryOp?, castValue_int,
      EvalResult.bind, bind, EvalResult.ofOption]
    rw [if_neg (by decide)]
    simp only [EvalResult.bind, bind, castValue_int, EvalResult.ofOption]
  -- `expR := int256(int256(int256(1e18 + r) + secondTerm) + thirdTerm)`
  let caller4 := {caller3 with locals := caller3.locals.insert "thirdTerm" (.int (wExpT xv))}
  have htr : caller4.locals.get? "r" = some (.int (wExpR xv)) := by
    show (caller3.locals.insert "thirdTerm" _).get? "r" = _
    rw [store_get_ne _ _ (by decide : ("thirdTerm" == "r") = false), hsr]
  have hts : caller4.locals.get? "secondTerm" = some (.int (wExpS xv)) := by
    show (caller3.locals.insert "thirdTerm" _).get? "secondTerm" = _
    rw [store_get_ne _ _ (by decide : ("thirdTerm" == "secondTerm") = false), hss]
  have htt : caller4.locals.get? "thirdTerm" = some (.int (wExpT xv)) := store_get_self _ _ _
  have he : evalExpr? cfg caller4 evm
      (.cast (.binary .add
        (.cast (.binary .add
          (.cast (.binary .add (.intLit WADI) (.var "r")) sint256S)
          (.var "secondTerm")) sint256S)
        (.var "thirdTerm")) sint256S) =
      .ok (.int (wExpE xv)) := by
    unfold wExpE WADI
    simp only [evalExpr?, htr, hts, htt, evalBinaryOp?, castValue_int,
      EvalResult.bind, bind, EvalResult.ofOption]
  -- final `return uint256(expR) <<[uint256] uint256(q)`
  let caller5 := {caller4 with locals := caller4.locals.insert "expR" (.int (wExpE xv))}
  have heq : caller5.locals.get? "q" = some (.int (wExpQ xv)) := by
    show (caller4.locals.insert "expR" _).get? "q" = _
    rw [store_get_ne _ _ (by decide : ("expR" == "q") = false)]
    show caller4.locals.get? "q" = _
    show ((((caller.locals.insert "q" _).insert "r" _).insert "secondTerm" _).insert "thirdTerm" _).get? "q" = _
    rw [store_get_ne _ _ (by decide : ("thirdTerm" == "q") = false)]
    rw [store_get_ne _ _ (by decide : ("secondTerm" == "q") = false)]
    rw [store_get_ne _ _ (by decide : ("r" == "q") = false), hqq]
  have hee : caller5.locals.get? "expR" = some (.int (wExpE xv)) := store_get_self _ _ _
  have hret : evalExpr? cfg caller5 evm
      (.binary (.shl (.uint ⟨256, by decide⟩))
        (.cast (.var "expR") uint256S) (.cast (.var "q") uint256S)) =
      .ok (.int (wExpPos xv)) := by
    set s := normalizeInt uint256I (wExpQ xv)
    have hsn : 0 ≤ s := by
      show 0 ≤ normalizeInt uint256I (wExpQ xv)
      unfold normalizeInt
      apply Int.emod_nonneg
      norm_num [EVM.twoPow]
    have hstn : s.toNat = s := Int.toNat_of_nonneg hsn
    simp only [evalExpr?, hee, heq, evalBinaryOp?, castValue_int,
      EvalResult.bind, bind, EvalResult.ofOption]
    rw [if_neg (by omega : ¬ s < 0)]
    show _ = EvalResult.ok (Value.int (wExpPos xv))
    have hbw : (ABI.IntType.uint ⟨256, by decide⟩).bitWidth.val = 256 := rfl
    rcases lt_or_ge s 256 with hlt256 | hge256
    · rw [if_neg (show ¬ (ABI.IntType.uint ⟨256, by decide⟩).bitWidth.val ≤ s.toNat from by
        rw [hbw]; omega)]
      rw [show wExpPos xv =
          normalizeInt uint256I
            (normalizeInt uint256I (wExpE xv) * Int.ofNat (EVM.twoPow s.toNat)) from by
        simp only [wExpPos]
        rw [if_neg (by omega : ¬ (256 : Int) ≤ s)]]
    · rw [if_pos (show (ABI.IntType.uint ⟨256, by decide⟩).bitWidth.val ≤ s.toNat from by
        rw [hbw]; omega)]
      rw [show wExpPos xv = 0 from by
        simp only [wExpPos]
        rw [if_pos hge256]]
  -- chain the ABlock
  refine ⟨caller5, ExecFuncBody.execBlockRet ?_⟩
  have b0 := ABlock.requireStep (ABlock.start (cfg := cfg) (evm := evm)
    (stele := caller) (stmts := wExpBodyDecl.body)) hreq
  -- `.ite` consumes the `x < 0` guard: `iteFalse` on `[]` → `.ok`.
  have b1 : ABlock cfg evm caller wExpBodyDecl.body caller _ :=
    ⟨fun h => b0.run (ExecBlock.consNormal (ExecStmt.iteFalse hlt ExecBlock.nil) h)⟩
  have b2 := ABlock.letStep b1 hq
  have b3 := ABlock.letStep b2 hr
  have b4 := ABlock.letStep b3 hs
  have b5 := ABlock.letStep b4 ht
  have b6 := ABlock.letStep b5 he
  exact ABlock.returns b6 hret

theorem wExpBodyStele (cfg : Config) (caller : Frame) (evm : EVM.State)
    (xv : Int) (hxv : xv ≠ MINI) (hxrng : -2^255 < xv)
    (hcontract : caller.contract = contract)
    (hxloc : caller.locals.get? "x" = some (.int xv))
    (hbound : xv < 0 → wExpPos (-xv) ≠ 0) :
    ∃ stele', ExecFuncBody cfg caller evm wExpBodyDecl.body
      (.returned stele' evm (some [Value.int (wExpVal xv)])) := by
  rcases lt_or_ge xv 0 with hneg | hpos
  · -- `xv < 0`: `.ite` takes the then-branch: `internalCall wExp_body(int256(-x))`,
    -- then `return 1e36 / __c0`.
    have hpos' : 0 < -xv := by omega
    have hbound' : wExpPos (-xv) ≠ 0 := hbound hneg
    have hnegxv : -xv < 2^255 := by omega
    have hreq := wExpRequire_ok cfg caller evm xv hxv hxloc
    have hlt : evalExpr? cfg caller evm
        (.binary .lt (.var "x") (.intLit 0)) = .ok (.bool true) := by
      simp only [evalExpr?, hxloc, evalBinaryOp?,
        EvalResult.bind, bind, EvalResult.ofOption]
      simp [hneg]
    -- the recursive call's argument `int256(-x)` evaluates to `.int (sintNorm(-xv)) = .int (-xv)`
    have hnorm : normalizeInt sint256I (-xv) = -xv := sintNorm_of_mem _ (by omega) hnegxv
    have hargs : evalExprs? cfg caller evm
        [.cast (.unary .neg (.var "x")) sint256S] = .ok [.int (-xv)] := by
      simp only [evalExprs?, evalExpr?, hxloc, evalUnaryOp?, castValue_int, hnorm,
        EvalResult.bind, bind, EvalResult.ofOption, pure]
    have hlookup : lookupCallable? caller.contract "wExp_body" =
        some wExpBodyDecl.toCallable := by
      rw [hcontract]
      rfl
    -- `bindParams?` produces `{x ↦ .int (-xv)}` — write `locals` for it.
    have hbind : bindParams? wExpBodyDecl.params [.int (-xv)] =
        some ((∅ : Store).insert "x" (.int (-xv))) := rfl
    have hloc' : ({caller with locals := (∅ : Store).insert "x" (.int (-xv))} : Frame).locals.get? "x" =
        some (.int (-xv)) := store_get_self _ _ _
    obtain ⟨calleeStele, hcallee⟩ :=
      wExpBodyStele_nonneg cfg {caller with locals := (∅ : Store).insert "x" (.int (-xv))}
        evm (-xv) (le_of_lt hpos') hloc'
    -- resume: `__c0 ↦ wExpPos (-xv)`; `return 1e36 / __c0`.
    let resumed : Frame := resumeAfterInternalCall caller "__c0" (some [.int (wExpPos (-xv))])
    have hres : resumed.locals.get? "__c0" = some (.int (wExpPos (-xv))) := by
      show (caller.locals.insert "__c0" (collapseReturns [.int (wExpPos (-xv))])).get? "__c0" = _
      rw [show collapseReturns [.int (wExpPos (-xv))] = .int (wExpPos (-xv)) from rfl]
      exact store_get_self _ _ _
    have hdiv : evalExpr? cfg resumed evm
        (.binary .div (.intLit ONE36I) (.var "__c0")) =
        .ok (.int (ONE36I / wExpPos (-xv))) := by
      simp only [evalExpr?, hres, evalBinaryOp?,
        EvalResult.bind, bind, EvalResult.ofOption]
      rw [if_neg hbound']
    have hic := internalCallFunctionReturn (name := "wExp_body") (retVar := "__c0")
      (args := [.cast (.unary .neg (.var "x")) sint256S]) (argVals := [.int (-xv)])
      (locals := (∅ : Store).insert "x" (.int (-xv))) (callee := wExpBodyDecl)
      hargs hlookup hbind hcallee
    -- `.ite`'s then-block: `internalCall` then `return`.
    refine ⟨{ caller with locals := resumed.locals }, ExecFuncBody.execBlockRet ?_⟩
    have b0 := ABlock.requireStep (ABlock.start (cfg := cfg) (evm := evm)
      (stele := caller) (stmts := wExpBodyDecl.body)) hreq
    -- block on the ite's then-stmts: [internalCall, return]
    have blk : ExecBlock cfg caller evm
        [Stmt.internalCall "wExp_body" [.cast (.unary .neg (.var "x")) sint256S] "__c0",
         Stmt.return [.binary .div (.intLit ONE36I) (.var "__c0")]]
        (.returned resumed evm (some [.int (ONE36I / wExpPos (-xv))])) :=
      ExecBlock.consNormal hic
        (ExecBlock.consReturn (ExecStmt.return (evalExprs?_singleton hdiv)))
    -- wrap: require-step then ite-consReturn
    have b1 : ExecBlock cfg caller evm wExpBodyDecl.body
        (.returned resumed evm (some [.int (ONE36I / wExpPos (-xv))])) :=
      b0.run (ExecBlock.consReturn (ExecStmt.iteTrue hlt blk))
    have hval : wExpVal xv = ONE36I / wExpPos (-xv) := by
      unfold wExpVal ONE36I; rw [if_pos hneg]
    rw [hval]
    exact b1
  · obtain ⟨stele', hbody⟩ :=
      wExpBodyStele_nonneg cfg caller evm xv hpos hxloc
    refine ⟨stele', ?_⟩
    rw [show wExpVal xv = wExpPos xv from by
      unfold wExpVal; rw [if_neg (not_lt.mpr hpos)]]
    exact hbody

theorem wExpBodyStele_minInt (cfg : Config) (caller : Frame) (evm : EVM.State)
    (xv : Int) (hxv : xv = MINI)
    (hxloc : caller.locals.get? "x" = some (.int xv)) :
    ExecFuncBody cfg caller evm wExpBodyDecl.body .reverted := by
  apply ExecFuncBody.execBlockRevert
  refine ABlock.requireRevert ABlock.start ?_
  simp only [evalExpr?, hxloc, evalBinaryOp?, evalUnaryOp?,
    EvalResult.bind, bind, EvalResult.ofOption]
  have hxv' : xv = -minLit := hxv
  simp [hxv']

theorem wExpBodyStele_divZero (cfg : Config) (caller : Frame) (evm : EVM.State)
    (xv : Int) (hneg : xv < 0) (hxv : xv ≠ MINI) (hxrng : -2^255 < xv)
    (hcontract : caller.contract = contract)
    (hxloc : caller.locals.get? "x" = some (.int xv))
    (hbound : wExpPos (-xv) = 0) :
    ExecFuncBody cfg caller evm wExpBodyDecl.body .reverted := by
  have hpos' : 0 < -xv := by omega
  have hnegxv : -xv < 2^255 := by
    have hne : xv ≠ -2^255 := hxv
    omega
  have hreq := wExpRequire_ok cfg caller evm xv hxv hxloc
  have hlt : evalExpr? cfg caller evm
      (.binary .lt (.var "x") (.intLit 0)) = .ok (.bool true) := by
    simp only [evalExpr?, hxloc, evalBinaryOp?,
      EvalResult.bind, bind, EvalResult.ofOption]
    simp [hneg]
  have hnorm : normalizeInt sint256I (-xv) = -xv := sintNorm_of_mem _ (by omega) hnegxv
  have hargs : evalExprs? cfg caller evm
      [.cast (.unary .neg (.var "x")) sint256S] = .ok [.int (-xv)] := by
    simp only [evalExprs?, evalExpr?, hxloc, evalUnaryOp?, castValue_int, hnorm,
      EvalResult.bind, bind, EvalResult.ofOption, pure]
  have hlookup : lookupCallable? caller.contract "wExp_body" =
      some wExpBodyDecl.toCallable := by
    rw [hcontract]
    rfl
  have hbind : bindParams? wExpBodyDecl.params [.int (-xv)] =
      some ((∅ : Store).insert "x" (.int (-xv))) := rfl
  have hloc' : ({caller with locals := (∅ : Store).insert "x" (.int (-xv))} : Frame).locals.get? "x" =
      some (.int (-xv)) := store_get_self _ _ _
  obtain ⟨calleeStele, hcallee⟩ :=
    wExpBodyStele_nonneg cfg {caller with locals := (∅ : Store).insert "x" (.int (-xv))}
      evm (-xv) (le_of_lt hpos') hloc'
  let resumed : Frame := resumeAfterInternalCall caller "__c0" (some [.int (wExpPos (-xv))])
  have hres : resumed.locals.get? "__c0" = some (.int (wExpPos (-xv))) := by
    show (caller.locals.insert "__c0" (collapseReturns [.int (wExpPos (-xv))])).get? "__c0" = _
    rw [show collapseReturns [.int (wExpPos (-xv))] = .int (wExpPos (-xv)) from rfl]
    exact store_get_self _ _ _
  have hdiv : evalExpr? cfg resumed evm
      (.binary .div (.intLit ONE36I) (.var "__c0")) = .revert := by
    simp only [evalExpr?, hres, evalBinaryOp?,
      EvalResult.bind, bind, EvalResult.ofOption]
    rw [if_pos hbound]
  have hdivs : evalExprs? cfg resumed evm
      [.binary .div (.intLit ONE36I) (.var "__c0")] = .revert := by
    simp only [evalExprs?, hdiv, EvalResult.bind, bind]
  have hic := internalCallFunctionReturn (name := "wExp_body") (retVar := "__c0")
    (args := [.cast (.unary .neg (.var "x")) sint256S]) (argVals := [.int (-xv)])
    (locals := (∅ : Store).insert "x" (.int (-xv))) (callee := wExpBodyDecl)
    hargs hlookup hbind hcallee
  apply ExecFuncBody.execBlockRevert
  have b0 := ABlock.requireStep (ABlock.start (cfg := cfg) (evm := evm)
    (stele := caller) (stmts := wExpBodyDecl.body)) hreq
  have blk : ExecBlock cfg caller evm
      [Stmt.internalCall "wExp_body" [.cast (.unary .neg (.var "x")) sint256S] "__c0",
       Stmt.return [.binary .div (.intLit ONE36I) (.var "__c0")]]
      .reverted :=
    ExecBlock.consNormal hic
      (ExecBlock.consRevert (ExecStmt.returnRevert hdivs))
  exact b0.run (ExecBlock.consRevert (ExecStmt.iteTrue hlt blk))

/-! ## EVM-side bridges

`EVM.signed` is `sintNorm` of the word's natural value, plus the congruence forms needed to
read the `SDIV`/`MUL`/`SUB` chains of block 636 back to the spec's `Int` model. -/

theorem signed_eq_sintNorm (w : UInt256) :
    EVM.signed w = normalizeInt sint256I (Int.ofNat w.toNat) := by
  have hlt : ↑w.val < EVM.wordModulus := w.val.isLt
  have hmod : Int.ofNat w.toNat % Int.ofNat EVM.wordModulus = Int.ofNat w.toNat := by
    rw [show Int.ofNat w.toNat % Int.ofNat EVM.wordModulus =
        Int.ofNat (w.toNat % EVM.wordModulus) from rfl]
    exact congrArg Int.ofNat (Nat.mod_eq_of_lt hlt)
  show (if ↑w.val < EVM.signBit then Int.ofNat ↑w.val
      else Int.ofNat ↑w.val - Int.ofNat EVM.wordModulus) = _
  unfold normalizeInt sint256I
  simp only
  rw [show Int.ofNat (EVM.twoPow 256) = Int.ofNat EVM.wordModulus from rfl,
      show Int.ofNat (EVM.twoPow (256 - 1)) = Int.ofNat EVM.signBit from rfl, hmod]
  by_cases hc : (w.val : Nat) < EVM.signBit
  · rw [if_pos hc,
        if_pos (show Int.ofNat w.toNat < Int.ofNat EVM.signBit from Int.ofNat_lt.mpr hc)]
    rfl
  · rw [if_neg hc,
        if_neg (show ¬ Int.ofNat w.toNat < Int.ofNat EVM.signBit from
          not_lt.mpr (Int.ofNat_le.mpr (le_of_not_gt hc)))]
    rfl

theorem signed_emod (w : UInt256) :
    EVM.signed w % Int.ofNat EVM.wordModulus = Int.ofNat w.toNat := by
  have hlt : ↑w.val < EVM.wordModulus := w.val.isLt
  show (if ↑w.val < EVM.signBit then Int.ofNat ↑w.val
      else Int.ofNat ↑w.val - Int.ofNat EVM.wordModulus) % _ = _
  by_cases hc : (w.val : Nat) < EVM.signBit
  · rw [if_pos hc,
        show Int.ofNat ↑w.val % Int.ofNat EVM.wordModulus =
          Int.ofNat (↑w.val % EVM.wordModulus) from rfl,
        Nat.mod_eq_of_lt hlt]
    rfl
  · rw [if_neg hc, Int.sub_emod_right,
        show Int.ofNat ↑w.val % Int.ofNat EVM.wordModulus =
          Int.ofNat (↑w.val % EVM.wordModulus) from rfl,
        Nat.mod_eq_of_lt hlt]
    rfl

/-- `signed (w + ofNat c) = sintNorm (signed w + c)` — sign-extended addition on the word. -/
theorem signed_add_ofNat (w : UInt256) (c : Nat) (hc : c < UInt256.size) :
    EVM.signed (w + UInt256.ofNat c) =
      normalizeInt sint256I (EVM.signed w + Int.ofNat c) := by
  rw [signed_eq_sintNorm]
  rw [uadd_toNat w _, ulit_toNat' c hc]
  have hsz : UInt256.size = EVM.wordModulus := rfl
  apply sintNorm_cong
  have hcof : Int.ofNat c % Int.ofNat EVM.wordModulus = Int.ofNat c := by
    rw [show Int.ofNat c % Int.ofNat EVM.wordModulus =
        Int.ofNat (c % EVM.wordModulus) from rfl]
    rw [Nat.mod_eq_of_lt (by omega : c < EVM.wordModulus)]
  rw [Int.add_emod]
  rw [show (2 ^ 256 : Int) = Int.ofNat EVM.wordModulus from rfl, signed_emod, hcof]
  rw [show Int.ofNat w.toNat + Int.ofNat c = Int.ofNat (w.toNat + c) from rfl]
  rw [show Int.ofNat (w.toNat + c) % Int.ofNat EVM.wordModulus =
      Int.ofNat ((w.toNat + c) % EVM.wordModulus) from rfl]
  rw [show Int.ofNat ((w.toNat + c) % UInt256.size) % Int.ofNat EVM.wordModulus =
      Int.ofNat (((w.toNat + c) % UInt256.size) % EVM.wordModulus) from rfl]
  rw [hsz, Nat.mod_mod]

/-- `wordOfInt` is `≡ mod 2^256`-congruence-invariant. -/
theorem wordOfInt_cong {a b : Int}
    (h : a % Int.ofNat EVM.wordModulus = b % Int.ofNat EVM.wordModulus) :
    EVM.wordOfInt a = EVM.wordOfInt b := by
  rw [← wordOfInt_emod a, ← wordOfInt_emod b, h]

/-- `sintNorm` in an addend is invisible to `wordOfInt`. -/
theorem wordOfInt_add_sintNorm (a b : Int) :
    EVM.wordOfInt (a + normalizeInt sint256I b) = EVM.wordOfInt (a + b) := by
  rw [wordOfInt_add, wordOfInt_sintNorm, wordOfInt_add]

/-- `sintNorm` in a subtrahend is invisible to `wordOfInt`. -/
theorem wordOfInt_sub_sintNorm (a b : Int) :
    EVM.wordOfInt (a - normalizeInt sint256I b) = EVM.wordOfInt (a - b) := by
  rw [wordOfInt_sub, wordOfInt_sintNorm, wordOfInt_sub]

/-- `wExpPos` never goes negative (the `else` branch is a `uintNorm` residue). -/
theorem wExpPos_nonneg (x : Int) : 0 ≤ wExpPos x := by
  show 0 ≤ if 256 ≤ normalizeInt uint256I (wExpQ x) then 0
    else normalizeInt uint256I
      (normalizeInt uint256I (wExpE x) *
        Int.ofNat (EVM.twoPow (normalizeInt uint256I (wExpQ x)).toNat))
  split
  · norm_num
  · unfold normalizeInt
    apply Int.emod_nonneg
    norm_num [EVM.twoPow]

/-- `wExpPos` stays below the word modulus. -/
theorem wExpPos_lt_mod (x : Int) : wExpPos x < Int.ofNat EVM.wordModulus := by
  show (if 256 ≤ normalizeInt uint256I (wExpQ x) then 0
    else normalizeInt uint256I
      (normalizeInt uint256I (wExpE x) *
        Int.ofNat (EVM.twoPow (normalizeInt uint256I (wExpQ x)).toNat))) < _
  split
  · norm_num [EVM.wordModulus, EVM.twoPow]
  · unfold normalizeInt
    apply Int.emod_lt_of_pos
    norm_num [EVM.twoPow]

/-- `wordOfInt`-merge lemmas in the generated code's named-`UInt256.op` form. -/
theorem wordOfInt_mul_of (a b : Int) :
    UInt256.mul (EVM.wordOfInt a) (EVM.wordOfInt b) = EVM.wordOfInt (a * b) :=
  (wordOfInt_mul a b).symm

theorem wordOfInt_sub_of (a b : Int) :
    UInt256.sub (EVM.wordOfInt a) (EVM.wordOfInt b) = EVM.wordOfInt (a - b) :=
  (wordOfInt_sub a b).symm

theorem wordOfInt_add_of (a b : Int) :
    UInt256.add (EVM.wordOfInt a) (EVM.wordOfInt b) = EVM.wordOfInt (a + b) :=
  (wordOfInt_add a b).symm

/-- `sintNorm` of a small positive literal is the literal's word. -/
theorem signed_ofNat_lt (c : Nat) (hc : c < 2 ^ 255) :
    EVM.signed (UInt256.ofNat c) = Int.ofNat c := by
  have htn : (UInt256.ofNat c).toNat = c :=
    ulit_toNat' c (lt_trans hc (by decide : 2 ^ 255 < UInt256.size))
  rw [signed_of_lt _ (by rw [htn]; exact hc), htn]

/-- The block-636 word-level polynomial + shift equals `wordOfInt (wExpPos (signed x0))`. -/
theorem wExp636_stack (x0 : UInt256) (R : List UInt256) :
    tickLibWrapperBlocks.tickLibWrapper_block_636_stack (x0 := x0) (R := R) =
      EVM.wordOfInt (wExpPos (EVM.signed x0)) :: R := by
  simp only [tickLibWrapperBlocks.tickLibWrapper_block_636_stack]
  rw [List.cons.injEq]
  refine ⟨?_, rfl⟩
  set xv := EVM.signed x0
  have hx0 : x0 = EVM.wordOfInt xv := (wordOfInt_signed x0).symm
  set Qw := UInt256.sdiv (x0 + UInt256.ofNat 322611214989459870)
    (UInt256.ofNat 693147180559945309) with hQw
  have hQ : Qw = EVM.wordOfInt (wExpQ xv) := by
    rw [hQw, wordOfInt_sdiv_pos _ _ (by
      rw [ulit_toNat' _ (by decide : (693147180559945309 : Nat) < UInt256.size)]
      decide)]
    rw [signed_add_ofNat x0 322611214989459870 (by decide),
        signed_ofNat_lt 693147180559945309 (by decide)]
    show EVM.wordOfInt (Int.tdiv (normalizeInt sint256I (xv + Int.ofNat 322611214989459870))
        (Int.ofNat 693147180559945309)) = _
    rw [← wordOfInt_sintNorm]
    rfl
  set Rw := UInt256.sub x0 (UInt256.mul Qw (UInt256.ofNat 693147180559945309)) with hRw
  have hR : Rw = EVM.wordOfInt (wExpR xv) := by
    rw [hRw, hQ, hx0,
        show (UInt256.ofNat 693147180559945309 : UInt256) =
          EVM.wordOfInt (Int.ofNat 693147180559945309) from
          (wordOfInt_ofNat_toNat_gen _).symm,
        wordOfInt_mul_of, wordOfInt_sub_of]
    show EVM.wordOfInt (xv - wExpQ xv * Int.ofNat 693147180559945309) = _
    rw [show wExpR xv =
        normalizeInt sint256I (xv - normalizeInt sint256I
          (wExpQ xv * Int.ofNat 693147180559945309)) from rfl]
    rw [wordOfInt_sintNorm, wordOfInt_sub_sintNorm]
  set Sw := UInt256.sdiv (UInt256.mul Rw Rw) (UInt256.ofNat 2000000000000000000) with hSw
  have hS : Sw = EVM.wordOfInt (wExpS xv) := by
    rw [hSw, wordOfInt_sdiv_pos _ _ (by
      rw [ulit_toNat' _ (by decide : (2000000000000000000 : Nat) < UInt256.size)]
      decide)]
    rw [signed_ofNat_lt 2000000000000000000 (by decide), hR, wordOfInt_mul_of,
        signed_wordOfInt]
    show EVM.wordOfInt (Int.tdiv
        (normalizeInt sint256I (wExpR xv * wExpR xv)) (Int.ofNat 2000000000000000000)) = _
    rw [show wExpS xv =
        normalizeInt sint256I (Int.tdiv
          (normalizeInt sint256I (wExpR xv * wExpR xv)) (2 * WADI)) from rfl,
        show (2 * WADI) = Int.ofNat 2000000000000000000 from rfl,
        ← wordOfInt_sintNorm]
  set Tw := UInt256.sdiv (UInt256.mul Sw Rw) (UInt256.ofNat 3000000000000000000) with hTw
  have hT : Tw = EVM.wordOfInt (wExpT xv) := by
    rw [hTw, wordOfInt_sdiv_pos _ _ (by
      rw [ulit_toNat' _ (by decide : (3000000000000000000 : Nat) < UInt256.size)]
      decide)]
    rw [signed_ofNat_lt 3000000000000000000 (by decide), hS, hR, wordOfInt_mul_of,
        signed_wordOfInt]
    show EVM.wordOfInt (Int.tdiv
        (normalizeInt sint256I (wExpS xv * wExpR xv)) (Int.ofNat 3000000000000000000)) = _
    rw [show wExpT xv =
        normalizeInt sint256I (Int.tdiv
          (normalizeInt sint256I (wExpS xv * wExpR xv)) (3 * WADI)) from rfl,
        show (3 * WADI) = Int.ofNat 3000000000000000000 from rfl,
        ← wordOfInt_sintNorm]
  have hE : (((Rw + Sw) + Tw) + UInt256.ofNat 1000000000000000000) =
      EVM.wordOfInt (wExpE xv) := by
    rw [hR, hS, hT,
        show (UInt256.ofNat 1000000000000000000 : UInt256) =
          EVM.wordOfInt WADI from (wordOfInt_ofNat_toNat_gen _).symm]
    have hexp : wExpE xv = normalizeInt sint256I
        (normalizeInt sint256I (normalizeInt sint256I (WADI + wExpR xv) + wExpS xv)
          + wExpT xv) := rfl
    rw [hexp]
    rw [wordOfInt_sintNorm, wordOfInt_add, wordOfInt_sintNorm, wordOfInt_add,
        wordOfInt_sintNorm, wordOfInt_add]
    rw [← wordOfInt_add, ← wordOfInt_add, ← wordOfInt_add,
        ← wordOfInt_add, ← wordOfInt_add, ← wordOfInt_add]
    apply wordOfInt_cong
    have hlin : wExpR xv + wExpS xv + wExpT xv + WADI =
        WADI + wExpR xv + wExpS xv + wExpT xv := by ring
    rw [hlin]
  set s' := normalizeInt uint256I (wExpQ xv) with hs'def
  have hs0 : 0 ≤ s' := by
    show 0 ≤ normalizeInt uint256I (wExpQ xv)
    unfold normalizeInt
    apply Int.emod_nonneg
    norm_num [EVM.twoPow]
  have hsM : s' < Int.ofNat EVM.wordModulus := by
    show normalizeInt uint256I (wExpQ xv) < Int.ofNat EVM.wordModulus
    show wExpQ xv % Int.ofNat (EVM.twoPow 256) < Int.ofNat EVM.wordModulus
    rw [show Int.ofNat (EVM.twoPow 256) = Int.ofNat EVM.wordModulus from rfl]
    exact Int.emod_lt_of_pos _ (by norm_num [EVM.wordModulus, EVM.twoPow])
  have hQ' : Qw = EVM.wordOfInt s' := by
    rw [hQ, hs'def, ← wordOfInt_uintNorm]
  rw [hE, hQ', wordOfInt_shiftLeft (wExpE xv) s' hs0 hsM]
  show EVM.wordOfInt
      (if (256 : Int) ≤ s' then 0
       else normalizeInt uint256I (wExpE xv * Int.ofNat (EVM.twoPow s'.toNat))) =
    EVM.wordOfInt
      (if (256 : Int) ≤ s' then 0
       else normalizeInt uint256I
         (normalizeInt uint256I (wExpE xv) * Int.ofNat (EVM.twoPow s'.toNat)))
  by_cases hsc : (256 : Int) ≤ s'
  · rw [if_pos hsc, if_pos hsc]
  · rw [if_neg hsc, if_neg hsc, wordOfInt_uintNorm, wordOfInt_uintNorm,
        wordOfInt_mul, wordOfInt_mul, wordOfInt_uintNorm]

/-- `wordOfInt (wExpPos x)` is the zero word iff `wExpPos x = 0`. -/
theorem wordOfInt_wExpPos_eq_zero_iff (x : Int) :
    EVM.wordOfInt (wExpPos x) = ⟨0⟩ ↔ wExpPos x = 0 := by
  constructor
  · intro h
    have ht := congrArg UInt256.toNat h
    rw [wordOfInt_toNat] at ht
    have hmod : wExpPos x % Int.ofNat EVM.wordModulus = wExpPos x :=
      Int.emod_eq_of_lt (wExpPos_nonneg x) (wExpPos_lt_mod x)
    rw [hmod] at ht
    have hnn := wExpPos_nonneg x
    have h0 : (⟨0⟩ : UInt256).toNat = 0 := rfl
    rw [h0] at ht
    omega
  · intro h; rw [h]; rfl

/-- `sintNorm` is the identity on in-range nonnegatives. -/
theorem sintNorm_eq_of_nonneg_lt (i : Int) (h0 : 0 ≤ i) (h : i < (2 ^ 255 : Int)) :
    normalizeInt sint256I i = i := by
  unfold normalizeInt sint256I
  simp only
  rw [show Int.ofNat (EVM.twoPow 256) = (2 ^ 256 : Int) from rfl,
      show Int.ofNat (EVM.twoPow (256 - 1)) = (2 ^ 255 : Int) from rfl,
      Int.emod_eq_of_lt h0 (by omega : i < 2 ^ 256)]
  exact if_pos h

/-- `signed w ≥ 0` iff `w.toNat < 2^255`. -/
theorem toNat_lt_2pow255_of_signed_nonneg {w : UInt256}
    (h : 0 ≤ EVM.signed w) : w.toNat < 2 ^ 255 := by
  by_contra hc
  have hge : EVM.signed w = Int.ofNat w.toNat - Int.ofNat EVM.wordModulus :=
    signed_of_ge w (by show (2 ^ 255 : Nat) ≤ w.toNat; omega)
  rw [hge, show Int.ofNat EVM.wordModulus = (2 ^ 256 : Int) from rfl] at h
  have hlt : Int.ofNat w.toNat < (2 ^ 256 : Int) := by
    show Int.ofNat w.toNat < Int.ofNat EVM.wordModulus
    exact Int.ofNat_lt.mpr w.val.isLt
  omega

/-- `signed w < 0` iff `w.toNat ≥ 2^255`. -/
theorem toNat_ge_2pow255_of_signed_neg {w : UInt256}
    (h : EVM.signed w < 0) : 2 ^ 255 ≤ w.toNat := by
  by_contra hc
  have hlt : EVM.signed w = Int.ofNat w.toNat :=
    signed_of_lt w (by show w.toNat < (2 ^ 255 : Nat); omega)
  rw [hlt] at h
  exact absurd h (not_lt.mpr (Int.ofNat_nonneg _))

/-- `signed w ≥ 0` when `w.toNat < 2^255`. -/
theorem signed_nonneg_of_toNat_lt {w : UInt256} (h : w.toNat < 2 ^ 255) :
    0 ≤ EVM.signed w := by
  rw [signed_of_lt w (by show w.toNat < (2 ^ 255 : Nat); exact h)]
  exact Int.ofNat_nonneg _

/-- `signed w < 0` when `w.toNat ≥ 2^255`. -/
theorem signed_neg_of_toNat_ge {w : UInt256} (h : 2 ^ 255 ≤ w.toNat) :
    EVM.signed w < 0 := by
  rw [signed_of_ge w (by show (2 ^ 255 : Nat) ≤ w.toNat; exact h),
      show Int.ofNat EVM.wordModulus = (2 ^ 256 : Int) from rfl]
  have hlt : Int.ofNat w.toNat < (2 ^ 256 : Int) := by
    show Int.ofNat w.toNat < Int.ofNat EVM.wordModulus
    exact Int.ofNat_lt.mpr w.val.isLt
  omega

/-- `wExpVal` is nonnegative in both branches. -/
theorem wExpVal_nonneg (xv : Int) : 0 ≤ wExpVal xv := by
  unfold wExpVal
  split
  · unfold ONE36I
    rcases lt_or_eq_of_le (wExpPos_nonneg (-xv)) with hpos | hz
    · exact Int.ediv_nonneg (Int.ofNat_nonneg _) (le_of_lt hpos)
    · rw [← hz]
      show 0 ≤ Int.ofNat 1000000000000000000000000000000000000 / (0 : Int)
      rw [Int.ediv_zero]
  · exact wExpPos_nonneg xv

/-- `wExpVal` is below the word modulus. -/
theorem wExpVal_lt_mod (xv : Int) : wExpVal xv < Int.ofNat EVM.wordModulus := by
  unfold wExpVal
  split
  · unfold ONE36I
    rcases lt_or_eq_of_le (wExpPos_nonneg (-xv)) with hpos | hz
    · have hle : Int.ofNat 1000000000000000000000000000000000000 / wExpPos (-xv) ≤
          Int.ofNat 1000000000000000000000000000000000000 := by
        have he : Int.ofNat 1000000000000000000000000000000000000 / wExpPos (-xv) =
            Int.ofNat (1000000000000000000000000000000000000 /
              (wExpPos (-xv)).toNat) := by
          rw [show wExpPos (-xv) = Int.ofNat (wExpPos (-xv)).toNat from
              (Int.toNat_of_nonneg (wExpPos_nonneg _)).symm]
          exact Int.ofNat_ediv_ofNat
        rw [he]
        exact Int.ofNat_le.mpr (Nat.div_le_self _ _)
      exact lt_of_le_of_lt hle (by
        show Int.ofNat 1000000000000000000000000000000000000 < Int.ofNat EVM.wordModulus
        decide)
    · rw [← hz]
      show Int.ofNat 1000000000000000000000000000000000000 / (0 : Int) <
          Int.ofNat EVM.wordModulus
      rw [Int.ediv_zero]
      decide
  · exact wExpPos_lt_mod xv

/-- `wExpVal` reads back through `wordOfInt.toNat`. -/
theorem wExpVal_toNat (xv : Int) :
    Int.ofNat (EVM.wordOfInt (wExpVal xv)).toNat = wExpVal xv := by
  rw [wordOfInt_toNat,
      Int.emod_eq_of_lt (wExpVal_nonneg xv) (wExpVal_lt_mod xv)]
  exact Int.toNat_of_nonneg (wExpVal_nonneg xv)

/-- The `1e36 / wExpPos (-xv)` word-division matches `wExpVal xv` for `xv < 0`. -/
theorem wExpVal_div_word (xv : Int) (hneg : xv < 0) :
    UInt256.div (UInt256.ofNat 1000000000000000000000000000000000000)
        (EVM.wordOfInt (wExpPos (-xv))) =
      EVM.wordOfInt (wExpVal xv) := by
  have hval : wExpVal xv = ONE36I / wExpPos (-xv) := by
    unfold wExpVal; rw [if_pos hneg]
  apply Reasoning.Theory.u256_inj
  rw [udiv_toNat, wordOfInt_toNat,
      Int.emod_eq_of_lt (wExpPos_nonneg _) (wExpPos_lt_mod _),
      wordOfInt_toNat, Int.emod_eq_of_lt (wExpVal_nonneg _) (wExpVal_lt_mod _)]
  rw [ulit_toNat' 1000000000000000000000000000000000000
      (by decide : (1000000000000000000000000000000000000 : Nat) < UInt256.size),
      hval]
  show 1000000000000000000000000000000000000 / (wExpPos (-xv)).toNat =
      Int.toNat (ONE36I / wExpPos (-xv))
  have h1 : ONE36I / wExpPos (-xv) =
      Int.ofNat (1000000000000000000000000000000000000 / (wExpPos (-xv)).toNat) := by
    show Int.ofNat 1000000000000000000000000000000000000 / wExpPos (-xv) =
        Int.ofNat (1000000000000000000000000000000000000 / (wExpPos (-xv)).toNat)
    rw [show wExpPos (-xv) = Int.ofNat (wExpPos (-xv)).toNat from
        (Int.toNat_of_nonneg (wExpPos_nonneg _)).symm]
    exact Int.ofNat_ediv_ofNat
  rw [h1]
  rfl

/-- `wExp`'s transition body as written in the spec. -/

theorem wExpBody_eq : wExpTransition.body =
    [.require (.binary .eq (.env .callvalue) (.intLit 0)),
     .letDecl "__calldata" (some .bytes) (.env .msgData),
     .require (.binary .lt
        (.arrayLength .localVar { base := "__calldata", steps := [] })
        (.intLit 57896044618658097711785492504343953926634992332820282019728792003956564819972)),
     .internalCall "wExp_body" [.var "x"] "__r",
     .return [.var "__r"]] := rfl

/-! ## EVM-side execution

RD traces from the dispatcher arm (pc 93: nonpayable + calldata-size guards, pc 111 decode)
to the wExp body block (pc 591), then either
  * `xv ≥ 0`           : pc 591 → 636 → 123 (return `wordOfInt (wExpPos xv)`)
  * `xv < 0, xv ≠ MINI`: pc 591 → 600 → 591` (once) → 636 → 123 (return `1e36 / wExpPos (-xv)`)
  * `xv = MINI`        : the `600 → 591` loop repeats, pushing `(-x, 610)` pairs each round
                         until the stack hits 1024 entries → `.error .StackOverflow`,
                         matched to the spec's `require`-revert by
                         `execResultsEquiv.stackOverflowHalt`. -/

/-! ### Selector arm: decode lemmas -/

/-- One `int256` scalar word decodes to `signed` of the big-endian word. -/
theorem decodeScalarWord_sint256 {bytes : List UInt8}
    (hlen : (bytes.take 32).length = 32) :
    decodeScalarWord? (.elem (.int (.sint ⟨256, by decide⟩))) bytes 0 =
      some (.int (EVM.signed (ABI.bytesToWord (bytes.take 32))), 32) := by
  have hrw : readWord? bytes 0 = some (ABI.bytesToWord (bytes.take 32)) := by
    unfold readWord? readBytes?
    rw [List.drop_zero, if_pos hlen]
    rfl
  have habi : decodeABIWord? (.elem (.int (.sint ⟨256, by decide⟩)))
        (ABI.bytesToWord (bytes.take 32)) =
      some (.int (EVM.signed (ABI.bytesToWord (bytes.take 32)))) := by
    unfold decodeABIWord?
    show (if (256 : ℕ) = 0 then (none : Option Stele.Value)
        else if (↑(ABI.bytesToWord (bytes.take 32)).val : ℕ) < EVM.twoPow 255 then
          some (Stele.Value.int (Int.ofNat ↑(ABI.bytesToWord (bytes.take 32)).val))
        else if EVM.wordModulus - EVM.twoPow 255 ≤
            ↑(ABI.bytesToWord (bytes.take 32)).val then
          some (Stele.Value.int (Int.ofNat ↑(ABI.bytesToWord (bytes.take 32)).val -
              Int.ofNat EVM.wordModulus))
        else (none : Option Stele.Value)) = _
    rw [if_neg (by decide : ¬ (256 : ℕ) = 0)]
    by_cases hnn : (↑(ABI.bytesToWord (bytes.take 32)).val : ℕ) < EVM.twoPow 255
    · rw [if_pos hnn]
      congr 2
      exact (signed_of_lt _ hnn).symm
    · rw [if_neg hnn, if_pos (by
          show (2 ^ 255 : Nat) ≤ ↑(ABI.bytesToWord (bytes.take 32)).val
          exact le_of_not_gt hnn)]
      congr 2
      exact (signed_of_ge _ (show EVM.signBit ≤
        (ABI.bytesToWord (bytes.take 32)).toNat from le_of_not_gt hnn)).symm
  unfold decodeScalarWord?
  rw [hrw]
  simp only [bind, Option.bind]
  rw [habi]

/-- The one-element `decodeScalarWords?` list form of `decodeScalarWord_sint256`. -/
theorem decodeScalarWords_sint256 {bytes : List UInt8}
    (hlen : (bytes.take 32).length = 32) :
    decodeScalarWords? [.elem (.int (.sint ⟨256, by decide⟩))] bytes 0 =
      some [.int (EVM.signed (ABI.bytesToWord (bytes.take 32)))] := by
  simp only [decodeScalarWords?]
  rw [decodeScalarWord_sint256 hlen]
  rfl

/-- The `int256` scalar decode fails when the word can't be read. -/
theorem decodeScalarWord_sint256_none_short {bytes : List UInt8}
    (hshort : ¬ (bytes.take 32).length = 32) :
    decodeScalarWord? (.elem (.int (.sint ⟨256, by decide⟩))) bytes 0 = none := by
  simp only [decodeScalarWord?, readWord?, readBytes?, decodeABIWord?, bind, Option.bind]
  rw [if_neg (by rw [List.drop_zero]; exact hshort)]

/-- The `int256` `decodeScalarWords?` fails when the word can't be read. -/
theorem decodeScalarWords_sint256_none_short {bytes : List UInt8}
    (hshort : bytes.length < 32) :
    decodeScalarWords? [.elem (.int (.sint ⟨256, by decide⟩))] bytes 0 = none := by
  simp only [decodeScalarWords?]
  have htake0n : ¬ (bytes.take 32).length = 32 := by
    rw [List.length_take]; omega
  rw [decodeScalarWord_sint256_none_short htake0n]
  simp only [Option.bind, bind]

theorem wExpDecode_ok {cd : ByteArray} (hsz36 : 36 ≤ cd.size) (hmax : cd.size < 2 ^ 255 + 4) :
    decodeCalldataWithMode .modern ["x"] [.elem (.int (.sint ⟨256, by decide⟩))] cd =
      some ((∅ : Store).insert "x" (.int (EVM.signed (calldataWord cd 4)))) := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  have htake : ((cd.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]; omega
  have hword4 : ABI.bytesToWord ((cd.toList.drop 4).take 32) = calldataWord cd 4 :=
    decode_word_at_eq cd 4 (by omega) (by norm_num)
  change decodeCalldata ["x"] [.elem (.int (.sint ⟨256, by decide⟩))] cd = _
  rw [decodeCalldata_scalarWords_eq (by decide)]
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  rw [if_neg (fun h => (by rw [List.length_drop, htlen]; omega :
      ¬ (2 ^ 255 ≤ (cd.toList.drop 4).length)) h.2)]
  rw [decodeScalarWords_sint256 (bytes := cd.toList.drop 4) htake]
  change decodeCalldata.insertValues ["x"]
      [.int (EVM.signed (ABI.bytesToWord ((cd.toList.drop 4).take 32)))] ∅ =
    some ((∅ : Store).insert "x" (.int (EVM.signed (calldataWord cd 4))))
  simp [decodeCalldata.insertValues]
  rw [hword4]

theorem wExpDecode_none {cd : ByteArray} (hsz4 : 4 ≤ cd.size)
    (h : cd.size < 36 ∨ 2 ^ 255 + 4 ≤ cd.size) :
    decodeCalldataWithMode .modern ["x"] [.elem (.int (.sint ⟨256, by decide⟩))] cd =
      none := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  change decodeCalldata ["x"] [.elem (.int (.sint ⟨256, by decide⟩))] cd = _
  rw [decodeCalldata_scalarWords_eq (by decide)]
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  rcases h with hshort | hbig
  · rw [if_neg (fun h' => (by rw [List.length_drop, htlen]; omega :
        ¬ (2 ^ 255 ≤ (cd.toList.drop 4).length)) h'.2)]
    rw [decodeScalarWords_sint256_none_short (bytes := cd.toList.drop 4) (by
      rw [List.length_drop, htlen]; omega)]
  · rw [if_pos ⟨by decide, by rw [List.length_drop, htlen]; omega⟩]

/-! ### Stele-side transition execution -/

/-- The `__calldata` length require evaluates to `true` under the signed bound. -/
theorem evalCalldataLen_true {evm : EVM.State} {cd : ByteArray}
    {frame : Frame} (hb : frame.locals.get? "__calldata" = some (.bytes cd))
    (hlen : cd.size < 2 ^ 255 + 4) :
    evalExpr? config frame evm
      (.binary .lt (.arrayLength .localVar { base := "__calldata", steps := [] })
        (.intLit 57896044618658097711785492504343953926634992332820282019728792003956564819972)) =
      .ok (.bool true) := by
  simp only [evalExpr?, EvalResult.bind, bind, pure]
  rw [hb]
  simp only [readLocalPath?, evalBinaryOp?, Int.ofNat_eq_natCast]
  rw [decide_eq_true (by omega : (cd.size : Int) <
    57896044618658097711785492504343953926634992332820282019728792003956564819972)]

/-- The `__calldata` length require evaluates to `false` past the signed bound. -/
theorem evalCalldataLen_false {evm : EVM.State} {cd : ByteArray}
    {frame : Frame} (hb : frame.locals.get? "__calldata" = some (.bytes cd))
    (hlen : 2 ^ 255 + 4 ≤ cd.size) :
    evalExpr? config frame evm
      (.binary .lt (.arrayLength .localVar { base := "__calldata", steps := [] })
        (.intLit 57896044618658097711785492504343953926634992332820282019728792003956564819972)) =
      .ok (.bool false) := by
  simp only [evalExpr?, EvalResult.bind, bind, pure]
  rw [hb]
  simp only [readLocalPath?, evalBinaryOp?, Int.ofNat_eq_natCast]
  rw [decide_eq_false (by omega : ¬ (cd.size : Int) <
    57896044618658097711785492504343953926634992332820282019728792003956564819972)]

/-- The dispatcher memory's free pointer word: `mem[0x40] = 0x80`. -/
theorem dispatchMemLoad64 :
    memLoad (UInt256.ofNat 64)
      ((UInt256.ofNat 128).toByteArray.write 0 ByteArray.empty 64 32) = ⟨128⟩ := by
  unfold memLoad
  rw [ulit_toNat' 64 (by decide),
    if_neg (by rw [toByteArray_write32_size_of_ge _ _ 64 0 96 (by decide) (by omega)
        (lt_usize _ (by decide)) (by decide)]; omega),
    toByteArray_write_read_back_of_gap _ _ 64 (lt_usize _ (by decide)),
    fromByteArrayBigEndian_toByteArray]
  exact u256_ofNat_toNat ⟨128⟩

theorem wExpTransitionReturns (evm : EVM.State) (xv : Int) (callargs : Store)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hlen : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (hxv : xv ≠ MINI) (hxrng : -2 ^ 255 < xv)
    (hbound : xv < 0 → wExpPos (-xv) ≠ 0)
    (hx : callargs.get? "x" = some (.int xv)) :
    ∃ cs, ExecTransitionBody config contract evm callargs wExpTransition.body
      (.returned cs evm (some [.int (wExpVal xv)])) := by
  rw [wExpBody_eq]
  -- the caller frame after `let __calldata = msg.data`
  let cd : ByteArray := evm.executionEnv.calldata
  have hx' : (callargs.insert "__calldata" (.bytes cd)).get? "x" = some (.int xv) := by
    rw [store_get_ne _ (.bytes cd) (by decide : ("__calldata" == "x") = false)]
    exact hx
  have hargs : evalExprs? config
      { contract := contract,
        locals := callargs.insert "__calldata" (.bytes cd), immutables := ∅ } evm
      [.var "x"] = .ok [.int xv] := by
    simp only [evalExprs?, evalExpr?, hx', EvalResult.bind, bind, EvalResult.ofOption, pure]
  have hlookup : lookupCallable? contract "wExp_body" = some wExpBodyDecl.toCallable := rfl
  have hbind : bindParams? wExpBodyDecl.params [.int xv] =
      some ((∅ : Store).insert "x" (.int xv)) := rfl
  have hloc' : (⟨contract, (∅ : Store).insert "x" (.int xv), ∅⟩ : Frame).locals.get? "x" =
      some (.int xv) :=
    store_get_self _ _ _
  obtain ⟨calleeStele, hcallee⟩ := wExpBodyStele config
      ⟨contract, (∅ : Store).insert "x" (.int xv), ∅⟩
      evm xv hxv hxrng rfl hloc' hbound
  have hic := internalCallFunctionReturn (name := "wExp_body") (retVar := "__r")
      (args := [.var "x"]) (argVals := [.int xv])
      (locals := (∅ : Store).insert "x" (.int xv)) (callee := wExpBodyDecl)
      hargs hlookup hbind hcallee
  let resumed : Frame := resumeAfterInternalCall
      { contract := contract,
        locals := callargs.insert "__calldata" (.bytes cd), immutables := ∅ } "__r"
      (some [.int (wExpVal xv)])
  have hres : resumed.locals.get? "__r" = some (.int (wExpVal xv)) := by
    show ((callargs.insert "__calldata" (.bytes cd)).insert "__r"
        (collapseReturns [.int (wExpVal xv)])).get? "__r" = _
    rw [show collapseReturns [.int (wExpVal xv)] = .int (wExpVal xv) from rfl]
    exact store_get_self _ _ _
  have hret : evalExpr? config resumed evm (.var "__r") = .ok (.int (wExpVal xv)) := by
    simp only [evalExpr?, hres, EvalResult.bind, bind, EvalResult.ofOption, pure]
  refine ⟨{ contract := contract, locals := resumed.locals, immutables := ∅ },
    ExecFuncBody.execBlockRet ?_⟩
  have blk : ExecBlock config
      { contract := contract,
        locals := callargs.insert "__calldata" (.bytes cd), immutables := ∅ }
      evm [Stmt.internalCall "wExp_body" [.var "x"] "__r", Stmt.return [.var "__r"]]
      (.returned resumed evm (some [.int (wExpVal xv)])) :=
    ExecBlock.consNormal hic
      (ExecBlock.consReturn (ExecStmt.return (evalExprs?_singleton hret)))
  exact (ABlock.start.requireStep (evalCallvalueEq_true hwv)).letStep
      (by simp only [evalExpr?, envValue, pure]) |>.requireStep
      (evalCalldataLen_true (store_get_self _ "__calldata"
        (.bytes evm.executionEnv.calldata)) hlen) |>.run blk

theorem wExpTransitionReverts_call (evm : EVM.State) (xv : Int) (callargs : Store)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hlen : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (hrev : ExecFuncBody config
        { contract := contract, locals := (∅ : Store).insert "x" (.int xv),
          immutables := ∅ }
        evm wExpBodyDecl.body .reverted)
    (hx : callargs.get? "x" = some (.int xv)) :
    ExecTransitionBody config contract evm callargs wExpTransition.body .reverted := by
  rw [wExpBody_eq]
  let cd : ByteArray := evm.executionEnv.calldata
  have hx' : (callargs.insert "__calldata" (.bytes cd)).get? "x" = some (.int xv) := by
    rw [store_get_ne _ (.bytes cd) (by decide : ("__calldata" == "x") = false)]
    exact hx
  have hargs : evalExprs? config
      { contract := contract,
        locals := callargs.insert "__calldata" (.bytes cd), immutables := ∅ } evm
      [.var "x"] = .ok [.int xv] := by
    simp only [evalExprs?, evalExpr?, hx', EvalResult.bind, bind, EvalResult.ofOption, pure]
  have hlookup : lookupCallable? contract "wExp_body" = some wExpBodyDecl.toCallable := rfl
  have hbind : bindParams? wExpBodyDecl.params [.int xv] =
      some ((∅ : Store).insert "x" (.int xv)) := rfl
  have hic := internalCallFunctionRevert (name := "wExp_body") (retVar := "__r")
      (args := [.var "x"]) (argVals := [.int xv])
      (locals := (∅ : Store).insert "x" (.int xv)) (callee := wExpBodyDecl)
      hargs hlookup hbind hrev
  refine ExecFuncBody.execBlockRevert ?_
  have blk : ExecBlock config
      { contract := contract,
        locals := callargs.insert "__calldata" (.bytes cd), immutables := ∅ }
      evm [Stmt.internalCall "wExp_body" [.var "x"] "__r", Stmt.return [.var "__r"]]
      .reverted := ExecBlock.consRevert hic
  exact (ABlock.start.requireStep (evalCallvalueEq_true hwv)).letStep
      (by simp only [evalExpr?, envValue, pure]) |>.requireStep
      (evalCalldataLen_true (store_get_self _ "__calldata"
        (.bytes evm.executionEnv.calldata)) hlen) |>.run blk

theorem wExpTransitionReverts_len (evm : EVM.State) (callargs : Store)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hlen : 2 ^ 255 + 4 ≤ evm.executionEnv.calldata.size) :
    ExecTransitionBody config contract evm callargs wExpTransition.body .reverted := by
  rw [wExpBody_eq]
  refine ExecFuncBody.execBlockRevert ?_
  exact (ABlock.start.requireStep (evalCallvalueEq_true hwv)).letStep
      (by simp only [evalExpr?, envValue, pure]) |>.requireRevert
      (evalCalldataLen_false (store_get_self _ "__calldata"
        (.bytes evm.executionEnv.calldata)) hlen)

/-! ### EVM-side traces -/

theorem wExpX_pos {σ σ₀ A I} {g : Sat256} {xv : Int}
    (hcode : I.code = tickLibWrapperBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hbig : I.calldata.size < 2 ^ 255 + 4) (h36 : 36 ≤ I.calldata.size)
    (hsel : selIs I (tickLibWrapperSelBytes 5))
    (hxv : xv = EVM.signed (calldataWord I.calldata 4)) (hpos : 0 ≤ xv) :
    RDret tickLibWrapperBytecode g (initState σ σ₀ g A I) σ
      (EVM.wordOfInt (wExpVal xv)).toByteArray := by
  subst hxv
  have hslt : UInt256.slt ((UInt256.lnot ⟨3⟩) + UInt256.ofNat I.calldata.size) ⟨32⟩ =
      ⟨0⟩ := by
    rw [lnot3_add_returnSize hsz4 hsize]
    show UInt256.slt (UInt256.ofNat (I.calldata.size - 4)) (UInt256.ofNat 32) = ⟨0⟩
    exact slt_ofNat_lit_zero (by norm_num) (by omega) (by omega)
  obtain ⟨_, _, rd⟩ := tickLibWrapperReachWExpBody (σ := σ) (σ₀ := σ₀) (A := A) (g := g)
    hcode hsz4 hsize hsel
  have rd1 := tickLibWrapperBlocks.tickLibWrapper_block_93_fallthrough (by simp) hwv rd
  have rd2 := tickLibWrapperBlocks.tickLibWrapper_block_99_fallthrough (by simp) hslt rd1
  have rd3 := tickLibWrapperBlocks.tickLibWrapper_block_111 (by simp) (by jump_dest) rd2
  -- `block_111_stack = [argw, 123, 32]` with `argw = uInt256OfByteArray (readBytes 4 32)`
  simp only [tickLibWrapperBlocks.tickLibWrapper_block_111_stack,
    show uInt256OfByteArray (I.calldata.readBytes (UInt256.ofNat 4).toNat 32) =
        calldataWord I.calldata 4 from rfl] at rd3
  have hcond : UInt256.isZero (UInt256.slt (calldataWord I.calldata 4) ⟨0⟩) ≠ ⟨0⟩ := by
    have hnn : (calldataWord I.calldata 4).toNat < 2 ^ 255 :=
      toNat_lt_2pow255_of_signed_nonneg hpos
    have hs0 : UInt256.slt (calldataWord I.calldata 4) ⟨0⟩ = ⟨0⟩ := by
      show UInt256.slt (calldataWord I.calldata 4) (UInt256.ofNat 0) = ⟨0⟩
      exact slt_lit_zero (a := calldataWord I.calldata 4) (m := 0) (by norm_num)
        (Nat.zero_le _) hnn
    rw [hs0]
    decide
  have rd4 := tickLibWrapperBlocks.tickLibWrapper_block_591_taken (by simp) hcond
    (by jump_dest) rd3
  have rd5 := tickLibWrapperBlocks.tickLibWrapper_block_636 (by simp) (by jump_dest) rd4
  rw [wExp636_stack] at rd5
  -- `block_636_stack` head = `wordOfInt (wExpPos xv)`; `wExpPos = wExpVal` for `xv ≥ 0`
  rw [show wExpVal (EVM.signed (calldataWord I.calldata 4)) =
      wExpPos (EVM.signed (calldataWord I.calldata 4)) from by
    unfold wExpVal; rw [if_neg (not_lt.mpr hpos)]] at ⊢
  have hmemsize : ((UInt256.ofNat 128).toByteArray.write 0 ByteArray.empty 64 32).size =
      96 := toByteArray_write32_size_of_ge _ _ 64 0 96 (by decide) (by omega)
      (lt_usize _ (by decide)) (by decide)
  have rd6 := tickLibWrapperBlocks.tickLibWrapper_block_123 (by simp) rd5
  rw [show (UInt256.ofNat 64).toNat = 64 from by decide, dispatchMemLoad64] at rd6
  rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide,
      show (UInt256.ofNat 32).toNat = 32 from by decide] at rd6
  rw [toByteArray_write_read_back_of_gap _ _ 128
      (by rw [hmemsize]; exact lt_usize _ (by decide))] at rd6
  exact rd6

theorem wExpX_neg {σ σ₀ A I} {g : Sat256} {xv : Int}
    (hcode : I.code = tickLibWrapperBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hbig : I.calldata.size < 2 ^ 255 + 4) (h36 : 36 ≤ I.calldata.size)
    (hsel : selIs I (tickLibWrapperSelBytes 5))
    (hxv : xv = EVM.signed (calldataWord I.calldata 4)) (hneg : xv < 0)
    (hmin : xv ≠ MINI) (hbound : wExpPos (-xv) ≠ 0) :
    RDret tickLibWrapperBytecode g (initState σ σ₀ g A I) σ
      (EVM.wordOfInt (wExpVal xv)).toByteArray := by
  have hslt : UInt256.slt ((UInt256.lnot ⟨3⟩) + UInt256.ofNat I.calldata.size) ⟨32⟩ =
      ⟨0⟩ := by
    rw [lnot3_add_returnSize hsz4 hsize]
    show UInt256.slt (UInt256.ofNat (I.calldata.size - 4)) (UInt256.ofNat 32) = ⟨0⟩
    exact slt_ofNat_lit_zero (by norm_num) (by omega) (by omega)
  obtain ⟨_, _, rd⟩ := tickLibWrapperReachWExpBody (σ := σ) (σ₀ := σ₀) (A := A) (g := g)
    hcode hsz4 hsize hsel
  have rd1 := tickLibWrapperBlocks.tickLibWrapper_block_93_fallthrough (by simp) hwv rd
  have rd2 := tickLibWrapperBlocks.tickLibWrapper_block_99_fallthrough (by simp) hslt rd1
  have rd3 := tickLibWrapperBlocks.tickLibWrapper_block_111 (by simp) (by jump_dest) rd2
  simp only [tickLibWrapperBlocks.tickLibWrapper_block_111_stack,
    show uInt256OfByteArray (I.calldata.readBytes (UInt256.ofNat 4).toNat 32) =
        calldataWord I.calldata 4 from rfl] at rd3
  have hwt : calldataWord I.calldata 4 = EVM.wordOfInt xv :=
    (wordOfInt_signed _).symm.trans (congrArg EVM.wordOfInt hxv.symm)
  have hxlb : -2 ^ 255 ≤ xv := by
    rw [hxv]
    show -2 ^ 255 ≤ EVM.signed (calldataWord I.calldata 4)
    by_cases hsgn : (calldataWord I.calldata 4).toNat < EVM.signBit
    · rw [signed_of_lt _ hsgn]; exact Int.ofNat_nonneg _
    · have hge : EVM.signBit ≤ (calldataWord I.calldata 4).toNat := le_of_not_gt hsgn
      have hge' : (2 ^ 255 : Int) ≤ Int.ofNat (calldataWord I.calldata 4).toNat :=
        Int.ofNat_le.mpr hge
      rw [signed_of_ge _ hge,
          show Int.ofNat EVM.wordModulus = (2 ^ 256 : Int) from rfl]
      omega
  have hcond : UInt256.isZero (UInt256.slt (calldataWord I.calldata 4) ⟨0⟩) = ⟨0⟩ := by
    have hng : 2 ^ 255 ≤ (calldataWord I.calldata 4).toNat :=
      toNat_ge_2pow255_of_signed_neg (hxv ▸ hneg)
    have hs0 : UInt256.slt (calldataWord I.calldata 4) ⟨0⟩ = ⟨1⟩ := by
      show UInt256.slt (calldataWord I.calldata 4) (UInt256.ofNat 0) = ⟨1⟩
      exact slt_lit_one_high (a := calldataWord I.calldata 4) (m := 0) (by norm_num) hng
    rw [hs0]
    exact isZero_eq_zero_of_ne (by decide)
  have rd4 := tickLibWrapperBlocks.tickLibWrapper_block_591_fallthrough (by simp) hcond rd3
  have rd5 := tickLibWrapperBlocks.tickLibWrapper_block_600 (by simp) (by jump_dest) rd4
  simp only [tickLibWrapperBlocks.tickLibWrapper_block_600_stack] at rd5
  -- `0 - argw = wordOfInt (-xv)`; `signed` of it is `-xv ≥ 0`
  have hw' : UInt256.sub ⟨0⟩ (calldataWord I.calldata 4) =
      EVM.wordOfInt (-xv) := by
    rw [hwt]
    show UInt256.sub (EVM.wordOfInt 0) (EVM.wordOfInt xv) = EVM.wordOfInt (-xv)
    rw [wordOfInt_sub_of]
    exact wordOfInt_cong (by
      show (0 - xv) % Int.ofNat EVM.wordModulus = (-xv) % Int.ofNat EVM.wordModulus
      rw [show Int.ofNat EVM.wordModulus = (2 ^ 256 : Int) from rfl]; omega)
  rw [hw'] at rd5
  have hcond' : UInt256.isZero (UInt256.slt (EVM.wordOfInt (-xv)) ⟨0⟩) ≠ ⟨0⟩ := by
    have hnn : (EVM.wordOfInt (-xv)).toNat < 2 ^ 255 := by
      rw [wordOfInt_toNat,
          Int.emod_eq_of_lt (by omega : 0 ≤ -xv) (by
            show -xv < (2 ^ 256 : Int)
            have hM : MINI = -2 ^ 255 := rfl; omega)]
      show (Int.toNat (-xv) : Nat) < 2 ^ 255
      have hnv : -xv < 2 ^ 255 := by
        have hM : MINI = -2 ^ 255 := rfl
        omega
      omega
    have hs0 : UInt256.slt (EVM.wordOfInt (-xv)) ⟨0⟩ = ⟨0⟩ := by
      show UInt256.slt (EVM.wordOfInt (-xv)) (UInt256.ofNat 0) = ⟨0⟩
      exact slt_lit_zero (a := EVM.wordOfInt (-xv)) (m := 0) (by norm_num) (Nat.zero_le _)
        hnn
    rw [hs0]
    decide
  have rd6 := tickLibWrapperBlocks.tickLibWrapper_block_591_taken (by simp) hcond'
    (by jump_dest) rd5
  have rd7 := tickLibWrapperBlocks.tickLibWrapper_block_636 (by simp) (by jump_dest) rd6
  rw [wExp636_stack, signed_wordOfInt,
      show normalizeInt sint256I (-xv) = -xv from
        sintNorm_eq_of_nonneg_lt _ (by omega) (by
          have hM : MINI = -2 ^ 255 := rfl; omega)] at rd7
  -- stack: `wordOfInt (wExpPos (-xv)) :: [123, 32]` at pc 610
  have hcond2 : UInt256.isZero (EVM.wordOfInt (wExpPos (-xv))) = ⟨0⟩ := by
    exact isZero_eq_zero_of_ne (fun hz' =>
      hbound ((wordOfInt_wExpPos_eq_zero_iff _).mp hz'))
  have rd8 := tickLibWrapperBlocks.tickLibWrapper_block_610_fallthrough (by simp) hcond2 rd7
  have rd9 := tickLibWrapperBlocks.tickLibWrapper_block_617 (by simp) (by jump_dest) rd8
  simp only [tickLibWrapperBlocks.tickLibWrapper_block_617_stack,
    wExpVal_div_word _ hneg] at rd9
  have hmemsize : ((UInt256.ofNat 128).toByteArray.write 0 ByteArray.empty 64 32).size =
      96 := toByteArray_write32_size_of_ge _ _ 64 0 96 (by decide) (by omega)
      (lt_usize _ (by decide)) (by decide)
  have rd10 := tickLibWrapperBlocks.tickLibWrapper_block_123 (by simp) rd9
  rw [show (UInt256.ofNat 64).toNat = 64 from by decide, dispatchMemLoad64] at rd10
  rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide,
      show (UInt256.ofNat 32).toNat = 32 from by decide] at rd10
  rw [toByteArray_write_read_back_of_gap _ _ 128
      (by rw [hmemsize]; exact lt_usize _ (by decide))] at rd10
  exact rd10

theorem wExpX_neg_rev {σ σ₀ A I} {g : Sat256} {xv : Int}
    (hcode : I.code = tickLibWrapperBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hbig : I.calldata.size < 2 ^ 255 + 4) (h36 : 36 ≤ I.calldata.size)
    (hsel : selIs I (tickLibWrapperSelBytes 5))
    (hxv : xv = EVM.signed (calldataWord I.calldata 4)) (hneg : xv < 0)
    (hmin : xv ≠ MINI) (hbound : wExpPos (-xv) = 0) :
    RDrev tickLibWrapperBytecode g (initState σ σ₀ g A I) := by
  have hslt : UInt256.slt ((UInt256.lnot ⟨3⟩) + UInt256.ofNat I.calldata.size) ⟨32⟩ =
      ⟨0⟩ := by
    rw [lnot3_add_returnSize hsz4 hsize]
    show UInt256.slt (UInt256.ofNat (I.calldata.size - 4)) (UInt256.ofNat 32) = ⟨0⟩
    exact slt_ofNat_lit_zero (by norm_num) (by omega) (by omega)
  obtain ⟨_, _, rd⟩ := tickLibWrapperReachWExpBody (σ := σ) (σ₀ := σ₀) (A := A) (g := g)
    hcode hsz4 hsize hsel
  have rd1 := tickLibWrapperBlocks.tickLibWrapper_block_93_fallthrough (by simp) hwv rd
  have rd2 := tickLibWrapperBlocks.tickLibWrapper_block_99_fallthrough (by simp) hslt rd1
  have rd3 := tickLibWrapperBlocks.tickLibWrapper_block_111 (by simp) (by jump_dest) rd2
  simp only [tickLibWrapperBlocks.tickLibWrapper_block_111_stack,
    show uInt256OfByteArray (I.calldata.readBytes (UInt256.ofNat 4).toNat 32) =
        calldataWord I.calldata 4 from rfl] at rd3
  have hwt : calldataWord I.calldata 4 = EVM.wordOfInt xv :=
    (wordOfInt_signed _).symm.trans (congrArg EVM.wordOfInt hxv.symm)
  have hxlb : -2 ^ 255 ≤ xv := by
    rw [hxv]
    show -2 ^ 255 ≤ EVM.signed (calldataWord I.calldata 4)
    by_cases hsgn : (calldataWord I.calldata 4).toNat < EVM.signBit
    · rw [signed_of_lt _ hsgn]; exact Int.ofNat_nonneg _
    · have hge : EVM.signBit ≤ (calldataWord I.calldata 4).toNat := le_of_not_gt hsgn
      have hge' : (2 ^ 255 : Int) ≤ Int.ofNat (calldataWord I.calldata 4).toNat :=
        Int.ofNat_le.mpr hge
      rw [signed_of_ge _ hge,
          show Int.ofNat EVM.wordModulus = (2 ^ 256 : Int) from rfl]
      omega
  have hcond : UInt256.isZero (UInt256.slt (calldataWord I.calldata 4) ⟨0⟩) = ⟨0⟩ := by
    have hng : 2 ^ 255 ≤ (calldataWord I.calldata 4).toNat :=
      toNat_ge_2pow255_of_signed_neg (hxv ▸ hneg)
    have hs0 : UInt256.slt (calldataWord I.calldata 4) ⟨0⟩ = ⟨1⟩ := by
      show UInt256.slt (calldataWord I.calldata 4) (UInt256.ofNat 0) = ⟨1⟩
      exact slt_lit_one_high (a := calldataWord I.calldata 4) (m := 0) (by norm_num) hng
    rw [hs0]
    exact isZero_eq_zero_of_ne (by decide)
  have rd4 := tickLibWrapperBlocks.tickLibWrapper_block_591_fallthrough (by simp) hcond rd3
  have rd5 := tickLibWrapperBlocks.tickLibWrapper_block_600 (by simp) (by jump_dest) rd4
  simp only [tickLibWrapperBlocks.tickLibWrapper_block_600_stack] at rd5
  have hw' : UInt256.sub ⟨0⟩ (calldataWord I.calldata 4) =
      EVM.wordOfInt (-xv) := by
    rw [hwt]
    show UInt256.sub (EVM.wordOfInt 0) (EVM.wordOfInt xv) = EVM.wordOfInt (-xv)
    rw [wordOfInt_sub_of]
    exact wordOfInt_cong (by
      show (0 - xv) % Int.ofNat EVM.wordModulus = (-xv) % Int.ofNat EVM.wordModulus
      rw [show Int.ofNat EVM.wordModulus = (2 ^ 256 : Int) from rfl]; omega)
  rw [hw'] at rd5
  have hcond' : UInt256.isZero (UInt256.slt (EVM.wordOfInt (-xv)) ⟨0⟩) ≠ ⟨0⟩ := by
    have hnn : (EVM.wordOfInt (-xv)).toNat < 2 ^ 255 := by
      rw [wordOfInt_toNat,
          Int.emod_eq_of_lt (by omega : 0 ≤ -xv) (by
            show -xv < (2 ^ 256 : Int)
            have hM : MINI = -2 ^ 255 := rfl; omega)]
      show (Int.toNat (-xv) : Nat) < 2 ^ 255
      have hnv : -xv < 2 ^ 255 := by
        have hM : MINI = -2 ^ 255 := rfl
        omega
      omega
    have hs0 : UInt256.slt (EVM.wordOfInt (-xv)) ⟨0⟩ = ⟨0⟩ := by
      show UInt256.slt (EVM.wordOfInt (-xv)) (UInt256.ofNat 0) = ⟨0⟩
      exact slt_lit_zero (a := EVM.wordOfInt (-xv)) (m := 0) (by norm_num) (Nat.zero_le _)
        hnn
    rw [hs0]
    decide
  have rd6 := tickLibWrapperBlocks.tickLibWrapper_block_591_taken (by simp) hcond'
    (by jump_dest) rd5
  have rd7 := tickLibWrapperBlocks.tickLibWrapper_block_636 (by simp) (by jump_dest) rd6
  rw [wExp636_stack, signed_wordOfInt,
      show normalizeInt sint256I (-xv) = -xv from
        sintNorm_eq_of_nonneg_lt _ (by omega) (by
          have hM : MINI = -2 ^ 255 := rfl; omega)] at rd7
  have hcond2 : UInt256.isZero (EVM.wordOfInt (wExpPos (-xv))) ≠ ⟨0⟩ := by
    rw [show EVM.wordOfInt (wExpPos (-xv)) = ⟨0⟩ from
      (wordOfInt_wExpPos_eq_zero_iff _).mpr hbound]
    decide
  have rd8 := tickLibWrapperBlocks.tickLibWrapper_block_610_taken (by simp) hcond2
    (by jump_dest) rd7
  exact tickLibWrapperBlocks.tickLibWrapper_block_456 (by simp) rd8

/-! ### `x = -2^255`: the recursion overflows the EVM stack -/

/-- After `n` recursive `591 → 600` rounds the stack is
    `w :: replicate n 610 ++ [123, 32]`; drive it to `n = 1020` (1024 entries), where the
    next `DUP2` hits the 1024-entry limit and emits `.error .StackOverflow`. -/
theorem wExpMinIntLoop {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray}
    {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {w : UInt256}
    (hslt : UInt256.isZero (UInt256.slt w ⟨0⟩) = ⟨0⟩)
    (hneg : UInt256.sub ⟨0⟩ w = w)
    (d n : ℕ) (hdn : n + d = 1020)
    {k C : ℕ}
    (h : RD tickLibWrapperBytecode ee g s0 (UInt256.ofNat 591)
           (w :: List.replicate n (UInt256.ofNat 610) ++
             [UInt256.ofNat 123, UInt256.ofNat 32])
           mem aw rdata σ k C) :
    ∃ k' C', RD tickLibWrapperBytecode ee g s0 (UInt256.ofNat 591)
           (w :: List.replicate 1020 (UInt256.ofNat 610) ++
             [UInt256.ofNat 123, UInt256.ofNat 32])
           mem aw rdata σ k' C' := by
  induction d generalizing n k C with
  | zero =>
      rw [show n = 1020 from by omega] at h
      exact ⟨_, _, h⟩
  | succ d ih =>
      have hn : n ≤ 1019 := by omega
      have hstk : (List.replicate n (UInt256.ofNat 610) ++
          [UInt256.ofNat 123, UInt256.ofNat 32]).length + 3 ≤ 1024 := by
        rw [List.length_append, List.length_replicate]; simp; omega
      have rd1 := tickLibWrapperBlocks.tickLibWrapper_block_591_fallthrough hstk hslt h
      have rd2 := tickLibWrapperBlocks.tickLibWrapper_block_600 hstk (by jump_dest) rd1
      simp only [tickLibWrapperBlocks.tickLibWrapper_block_600_stack] at rd2
      rw [hneg] at rd2
      have hs : w :: (UInt256.ofNat 610) ::
            (List.replicate n (UInt256.ofNat 610) ++
              [UInt256.ofNat 123, UInt256.ofNat 32]) =
          w :: List.replicate (n + 1) (UInt256.ofNat 610) ++
            [UInt256.ofNat 123, UInt256.ofNat 32] := rfl
      rw [hs] at rd2
      obtain ⟨k', C', h'⟩ := ih (n := n + 1) (hdn := by omega) rd2
      exact ⟨k', C', h'⟩

/-- The decode/guard-failure paths end at the generic dispatcher revert (pc 131). -/
theorem wExpX_revert {σ σ₀ A I} {g : Sat256}
    (hcode : I.code = tickLibWrapperBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 36 ∨ 2 ^ 255 + 4 ≤ I.calldata.size)
    (hsel : selIs I (tickLibWrapperSelBytes 5)) :
    RDrev tickLibWrapperBytecode g (initState σ σ₀ g A I) := by
  have hslt : UInt256.slt ((UInt256.lnot ⟨3⟩) + UInt256.ofNat I.calldata.size) ⟨32⟩ ≠
      ⟨0⟩ := by
    rw [lnot3_add_returnSize hsz4 hsize]
    show UInt256.slt (UInt256.ofNat (I.calldata.size - 4)) (UInt256.ofNat 32) ≠ ⟨0⟩
    rcases hshort with hs | hb
    · rw [slt_ofNat_lit_one_low (by norm_num) (by omega : I.calldata.size - 4 < 32)]
      decide
    · rw [slt_lit_one_high (a := UInt256.ofNat (I.calldata.size - 4)) (m := 32)
        (by norm_num) (by rw [ulit_toNat' _ (by omega : I.calldata.size - 4 <
          UInt256.size)]; omega)]
      decide
  obtain ⟨_, _, rd⟩ := tickLibWrapperReachWExpBody (σ := σ) (σ₀ := σ₀) (A := A) (g := g)
    hcode hsz4 hsize hsel
  have rd1 := tickLibWrapperBlocks.tickLibWrapper_block_93_fallthrough (by simp) hwv rd
  have rd2 := tickLibWrapperBlocks.tickLibWrapper_block_99_taken (by simp) hslt
    (by jump_dest) rd1
  exact tickLibWrapperBlocks.tickLibWrapper_block_131 (by simp) rd2

/-- Nonpayable calls take the `callvalue`-guard revert branch (pc 93 → 131). -/
theorem wExpX_revert_pay {σ σ₀ A I} {g : Sat256}
    (hcode : I.code = tickLibWrapperBytecode) (hwv : I.weiValue ≠ ⟨0⟩)
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (tickLibWrapperSelBytes 5)) :
    RDrev tickLibWrapperBytecode g (initState σ σ₀ g A I) := by
  obtain ⟨_, _, rd⟩ := tickLibWrapperReachWExpBody (σ := σ) (σ₀ := σ₀) (A := A) (g := g)
    hcode hsz4 hsize hsel
  have rd1 := tickLibWrapperBlocks.tickLibWrapper_block_93_taken (by simp) hwv
    (by jump_dest) rd
  exact tickLibWrapperBlocks.tickLibWrapper_block_131 (by simp) rd1

/-- At the 1024-entry stack the next `DUP2` either runs out of gas or overflows. -/
theorem wExpMinIntTerminal {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray}
    {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {w : UInt256} {k C : ℕ}
    (h : RD tickLibWrapperBytecode ee g s0 ⟨591⟩
           (w :: List.replicate 1020 (UInt256.ofNat 610) ++
             [UInt256.ofNat 123, UInt256.ofNat 32]) mem aw rdata σ k C) :
    X (g.toNat + 1) (D_J tickLibWrapperBytecode 0) s0 = .error .StackOverflow ∨
      X (g.toNat + 1) (D_J tickLibWrapperBytecode 0) s0 = .error .OutOfGass := by
  have r1 := h.jumpdest (by native_decide) (by simp)
  have r2 := r1.push0 (by native_decide) (by simp)
  rcases r2 with hoog | ⟨s, hX, hcode, hpc, hstk2, hgas, hk2, hC2, hmem, haw, hrdata, hacc,
      hee, hσ₀⟩
  · exact Or.inr hoog
  · have hd : decode s.executionEnv.code s.machineState.pc = some (.DUP2, .none) := by
      rw [hcode, hpc]; native_decide
    rw [hX]
    by_cases hg : s.machineState.gasAvailable.toNat < GasConstants.Gverylow
    · have hs2 : Xstep (D_J tickLibWrapperBytecode 0) s = .error .OutOfGass := by
        rw [← hcode, step_dup2 s hd, hstk2]
        simp [hg]
      have hf : g.toNat + 1 - (k + 2) = (g.toNat - k - 2) + 1 := by
        have : k + 2 ≤ g.toNat := by omega
        omega
      rw [hf]
      exact Or.inr (Xstep_X_X_except _ s _ .OutOfGass hs2)
    · have hs2 : Xstep (D_J tickLibWrapperBytecode 0) s = .error .StackOverflow := by
        rw [← hcode, step_dup2 s hd, hstk2]
        simp [hg]
      have hf : g.toNat + 1 - (k + 2) = (g.toNat - k - 2) + 1 := by
        have : k + 2 ≤ g.toNat := by omega
        omega
      rw [hf]
      exact Or.inl (Xstep_X_X_except _ s _ .StackOverflow hs2)

theorem wExpX_min {σ σ₀ A I} {g : Sat256} {xv : Int}
    (hcode : I.code = tickLibWrapperBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hbig : I.calldata.size < 2 ^ 255 + 4) (h36 : 36 ≤ I.calldata.size)
    (hsel : selIs I (tickLibWrapperSelBytes 5))
    (hxv : xv = EVM.signed (calldataWord I.calldata 4)) (hmin : xv = MINI) :
    X (g.toNat + 1) (D_J tickLibWrapperBytecode 0) (initState σ σ₀ g A I) =
        .error .StackOverflow ∨
      X (g.toNat + 1) (D_J tickLibWrapperBytecode 0) (initState σ σ₀ g A I) =
        .error .OutOfGass := by
  subst hxv
  have hslt : UInt256.slt ((UInt256.lnot ⟨3⟩) + UInt256.ofNat I.calldata.size) ⟨32⟩ =
      ⟨0⟩ := by
    rw [lnot3_add_returnSize hsz4 hsize]
    show UInt256.slt (UInt256.ofNat (I.calldata.size - 4)) (UInt256.ofNat 32) = ⟨0⟩
    exact slt_ofNat_lit_zero (by norm_num) (by omega) (by omega)
  obtain ⟨_, _, rd⟩ := tickLibWrapperReachWExpBody (σ := σ) (σ₀ := σ₀) (A := A) (g := g)
    hcode hsz4 hsize hsel
  have rd1 := tickLibWrapperBlocks.tickLibWrapper_block_93_fallthrough (by simp) hwv rd
  have rd2 := tickLibWrapperBlocks.tickLibWrapper_block_99_fallthrough (by simp) hslt rd1
  have rd3 := tickLibWrapperBlocks.tickLibWrapper_block_111 (by simp) (by jump_dest) rd2
  simp only [tickLibWrapperBlocks.tickLibWrapper_block_111_stack,
    show uInt256OfByteArray (I.calldata.readBytes (UInt256.ofNat 4).toNat 32) =
        calldataWord I.calldata 4 from rfl] at rd3
  -- `xv = MINI` means the decoded word is `wordOfInt MINI` with `toNat = 2^255`
  have hwt : (calldataWord I.calldata 4) = EVM.wordOfInt MINI :=
    (wordOfInt_signed _).symm.trans (congrArg EVM.wordOfInt hmin)
  have hcond : UInt256.isZero (UInt256.slt (calldataWord I.calldata 4) ⟨0⟩) = ⟨0⟩ := by
    have hng : 2 ^ 255 ≤ (calldataWord I.calldata 4).toNat := by
      rw [hwt, wordOfInt_toNat]
      show 2 ^ 255 ≤ (MINI % Int.ofNat EVM.wordModulus).toNat
      rw [show MINI % Int.ofNat EVM.wordModulus = Int.ofNat (2 ^ 255) from by
        show (MINI : Int) % Int.ofNat EVM.wordModulus = Int.ofNat (2 ^ 255)
        have hM : Int.ofNat EVM.wordModulus = (2 ^ 256 : Int) := rfl
        rw [hM]
        norm_num [MINI]]
      show 2 ^ 255 ≤ (Int.ofNat (2 ^ 255)).toNat
      exact le_refl _
    have hs0 : UInt256.slt (calldataWord I.calldata 4) ⟨0⟩ = ⟨1⟩ := by
      show UInt256.slt (calldataWord I.calldata 4) (UInt256.ofNat 0) = ⟨1⟩
      exact slt_lit_one_high (a := calldataWord I.calldata 4) (m := 0) (by norm_num) hng
    rw [hs0]
    exact isZero_eq_zero_of_ne (by decide)
  have hneg : UInt256.sub ⟨0⟩ (calldataWord I.calldata 4) = calldataWord I.calldata 4 := by
    rw [hwt]
    show UInt256.sub (EVM.wordOfInt 0) (EVM.wordOfInt MINI) = EVM.wordOfInt MINI
    rw [wordOfInt_sub_of]
    exact wordOfInt_cong (by
      show (0 - MINI) % Int.ofNat EVM.wordModulus = MINI % Int.ofNat EVM.wordModulus
      rw [show Int.ofNat EVM.wordModulus = (2 ^ 256 : Int) from rfl]
      native_decide)
  obtain ⟨k', C', rd'⟩ := wExpMinIntLoop hcond hneg 1020 0 (by omega) rd3
  exact wExpMinIntTerminal rd'

theorem tickLibWrapperWExpBody {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = tickLibWrapperBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (tickLibWrapperSelBytes 5)) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (tickLibWrapperSelBytes 5)
    rfl hsel
  have h0 : ¬ selIs I (tickLibWrapperSelBytes 0) := by
    intro h
    exact absurd ((byteArray_eq_of_beq h).trans (byteArray_eq_of_beq hsel).symm) (by decide)
  have h1 : ¬ selIs I (tickLibWrapperSelBytes 1) := by
    intro h
    exact absurd ((byteArray_eq_of_beq h).trans (byteArray_eq_of_beq hsel).symm) (by decide)
  have h2 : ¬ selIs I (tickLibWrapperSelBytes 2) := by
    intro h
    exact absurd ((byteArray_eq_of_beq h).trans (byteArray_eq_of_beq hsel).symm) (by decide)
  have h3 : ¬ selIs I (tickLibWrapperSelBytes 3) := by
    intro h
    exact absurd ((byteArray_eq_of_beq h).trans (byteArray_eq_of_beq hsel).symm) (by decide)
  have h4 : ¬ selIs I (tickLibWrapperSelBytes 4) := by
    intro h
    exact absurd ((byteArray_eq_of_beq h).trans (byteArray_eq_of_beq hsel).symm) (by decide)
  have hd : dispatchMsg contract I.calldata = some wExpTransition :=
    tickLibWrapperDispatch_wExp h0 h1 h2 h3 h4 hsel
  by_cases hwv : I.weiValue = ⟨0⟩
  · by_cases hbig : I.calldata.size < 2 ^ 255 + 4
    · by_cases h36 : 36 ≤ I.calldata.size
      · -- `36 ≤ size < 2^255 + 4`: decode succeeds, run the body.
        have hdec := wExpDecode_ok h36 hbig
        set xv := EVM.signed (calldataWord I.calldata 4) with hxv
        have hxlb : -2 ^ 255 ≤ xv := by
          rw [hxv]
          show -2 ^ 255 ≤ EVM.signed (calldataWord I.calldata 4)
          by_cases hsgn : (calldataWord I.calldata 4).toNat < EVM.signBit
          · rw [signed_of_lt _ hsgn]; exact Int.ofNat_nonneg _
          · have hge : EVM.signBit ≤ (calldataWord I.calldata 4).toNat :=
              le_of_not_gt hsgn
            have hge' : (2 ^ 255 : Int) ≤ Int.ofNat (calldataWord I.calldata 4).toNat :=
              Int.ofNat_le.mpr hge
            rw [signed_of_ge _ hge,
                show Int.ofNat EVM.wordModulus = (2 ^ 256 : Int) from rfl]
            omega
        rcases lt_or_ge xv 0 with hneg | hpos
        · by_cases hmin : xv = MINI
          · -- `x = -2^255`: spec reverts at `require`, EVM overflows the stack or the gas.
            have hbody : ExecTransitionBody config contract
                (initState σ σ₀ (Sat256.ofUInt256 g) A I)
                ((∅ : Store).insert "x" (.int xv)) wExpTransition.body .reverted := by
              have hb := wExpTransitionReverts_call
                (initState σ σ₀ (Sat256.ofUInt256 g) A I) xv
                ((∅ : Store).insert "x" (.int xv))
                (by simp only [initState]; exact hwv)
                (by simp only [initState]; exact hbig)
                (wExpBodyStele_minInt config
                  { contract := contract,
                    locals := (∅ : Store).insert "x" (.int xv), immutables := ∅ }
                  _ xv hmin (store_get_self _ _ _))
                (store_get_self _ _ _)
              exact hb
            have hX : X ((Sat256.ofUInt256 g).toNat + 1) (D_J tickLibWrapperBytecode 0)
                (initState σ σ₀ (Sat256.ofUInt256 g) A I) = .error .StackOverflow ∨
              X ((Sat256.ofUInt256 g).toNat + 1) (D_J tickLibWrapperBytecode 0)
                (initState σ σ₀ (Sat256.ofUInt256 g) A I) = .error .OutOfGass :=
              wExpX_min (g := Sat256.ofUInt256 g) hcode hwv hsz hsize hbig h36 hsel
                rfl hmin
            rcases hX with hSO | hOOG
            · rw [← hcode] at hSO
              have hΞ := Xi_error_of_X (g := g) (by
                simpa [Sat256.ofUInt256_toNat] using hSO)
              exact reEquiv_execution hd hdec hbody
                (execResultsEquiv.stackOverflowHalt hΞ rfl)
            · rw [← hcode] at hOOG
              exact reEquiv_outOfGas (Xi_error_of_X (g := g) (by
                simpa [Sat256.ofUInt256_toNat] using hOOG))
          · by_cases hz : wExpPos (-xv) = 0
            · -- `1e36 / 0` reverts at block 456; spec's div-revert.
              have hbody : ExecTransitionBody config contract
                  (initState σ σ₀ (Sat256.ofUInt256 g) A I)
                  ((∅ : Store).insert "x" (.int xv)) wExpTransition.body .reverted := by
                have hb := wExpTransitionReverts_call
                  (initState σ σ₀ (Sat256.ofUInt256 g) A I) xv
                  ((∅ : Store).insert "x" (.int xv))
                  (by simp only [initState]; exact hwv)
                  (by simp only [initState]; exact hbig)
                  (wExpBodyStele_divZero config
                    { contract := contract,
                      locals := (∅ : Store).insert "x" (.int xv), immutables := ∅ }
                    _ xv hneg hmin (by have hM : MINI = -2^255 := rfl; omega) rfl
                    (store_get_self _ _ _) hz)
                  (store_get_self _ _ _)
                exact hb
              exact (wExpX_neg_rev (g := Sat256.ofUInt256 g) hcode hwv hsz hsize hbig h36
                  hsel rfl hneg hmin hz)
                |>.reEquivExecutionRevert hcode hd hdec hbody
            · -- ordinary negative: recursive return then `1e36 / wExpPos (-xv)`.
              obtain ⟨cs, hb⟩ := wExpTransitionReturns
                (initState σ σ₀ (Sat256.ofUInt256 g) A I) xv
                ((∅ : Store).insert "x" (.int xv))
                (by simp only [initState]; exact hwv)
                (by simp only [initState]; exact hbig)
                hmin (by have hM : MINI = -2^255 := rfl; omega) (fun h => hz)
                (store_get_self ∅ "x" (.int xv))
              exact (wExpX_neg (g := Sat256.ofUInt256 g) hcode hwv hsz hsize hbig h36
                  hsel rfl hneg hmin hz)
                |>.reEquivExecution hcode hd hdec hb
                  (returnEquiv_of_encode (by
                    have henc := uint256ReturnEncoding (EVM.wordOfInt (wExpVal xv))
                    rw [wExpVal_toNat xv] at henc
                    exact henc))
        · -- `xv ≥ 0`: positive path.
          obtain ⟨cs, hb⟩ := wExpTransitionReturns
            (initState σ σ₀ (Sat256.ofUInt256 g) A I) xv
            ((∅ : Store).insert "x" (.int xv))
            (by simp only [initState]; exact hwv)
            (by simp only [initState]; exact hbig)
            (by
              intro he
              rw [he] at hpos
              exact absurd hpos (by decide))
            (by omega) (fun h => absurd h (by omega))
            (store_get_self ∅ "x" (.int xv))
          exact (wExpX_pos (g := Sat256.ofUInt256 g) hcode hwv hsz hsize hbig h36
              hsel rfl hpos)
            |>.reEquivExecution hcode hd hdec hb
              (returnEquiv_of_encode (by
                have henc := uint256ReturnEncoding (EVM.wordOfInt (wExpVal xv))
                rw [wExpVal_toNat xv] at henc
                exact henc))
      · -- `4 ≤ size < 36`: decode fails (not enough args bytes) → revert at 131.
        have hdec : config.externalABI.decodeCalldata?
            (wExpTransition.params.map Param.name)
            (transitionSignature wExpTransition).paramTypes I.calldata = none := by
          show decodeCalldataWithMode .modern _ _ I.calldata = none
          exact wExpDecode_none hsz (Or.inl (by omega))
        have hrd : RDrev tickLibWrapperBytecode (Sat256.ofUInt256 g)
            (initState σ σ₀ (Sat256.ofUInt256 g) A I) :=
          wExpX_revert hcode hwv hsz hsize (Or.inl (by omega)) hsel
        rcases hrd with hOOG | ⟨g', o, hrev⟩
        · rw [← hcode] at hOOG
          exact reEquiv_outOfGas (Xi_error_of_X (g := g) (by
            simpa [Sat256.ofUInt256_toNat] using hOOG))
        · rw [← hcode] at hrev
          exact reEquiv_decodingFailed hd hdec (Xi_revert_of_X (g := g) (by
            simpa [Sat256.ofUInt256_toNat] using hrev))
    · -- `size ≥ 2^255 + 4`: decode fails (huge args) → revert at 131.
      have hdec : config.externalABI.decodeCalldata?
          (wExpTransition.params.map Param.name)
          (transitionSignature wExpTransition).paramTypes I.calldata = none := by
        show decodeCalldataWithMode .modern _ _ I.calldata = none
        exact wExpDecode_none hsz (Or.inr (by omega))
      have hrd : RDrev tickLibWrapperBytecode (Sat256.ofUInt256 g)
          (initState σ σ₀ (Sat256.ofUInt256 g) A I) :=
        wExpX_revert hcode hwv hsz hsize (Or.inr (by omega)) hsel
      rcases hrd with hOOG | ⟨g', o, hrev⟩
      · rw [← hcode] at hOOG
        exact reEquiv_outOfGas (Xi_error_of_X (g := g) (by
          simpa [Sat256.ofUInt256_toNat] using hOOG))
      · rw [← hcode] at hrev
        exact reEquiv_decodingFailed hd hdec (Xi_revert_of_X (g := g) (by
          simpa [Sat256.ofUInt256_toNat] using hrev))
  · -- nonpayable: revert at 131 on both sides.
    have hrd : RDrev tickLibWrapperBytecode (Sat256.ofUInt256 g)
        (initState σ σ₀ (Sat256.ofUInt256 g) A I) :=
      wExpX_revert_pay hcode hwv hsz hsize hsel
    rcases hrd with hOOG | ⟨g', o, hrev⟩
    · rw [← hcode] at hOOG
      exact reEquiv_outOfGas (Xi_error_of_X (g := g) (by
        simpa [Sat256.ofUInt256_toNat] using hOOG))
    · rw [← hcode] at hrev
      have hΞ : Ξ σ σ₀ g A I = .ok (.revert g' o) :=
        Xi_revert_of_X (g := g) (by simpa [Sat256.ofUInt256_toNat] using hrev)
      by_cases hbig : I.calldata.size < 2 ^ 255 + 4
      · by_cases h36 : 36 ≤ I.calldata.size
        · have hdec := wExpDecode_ok h36 hbig
          have hbody : ExecTransitionBody config contract
              (initState σ σ₀ (Sat256.ofUInt256 g) A I)
              ((∅ : Store).insert "x" (.int (EVM.signed (calldataWord I.calldata 4))))
              wExpTransition.body .reverted := by
            rw [wExpBody_eq]
            exact bodyReverts_nonPayable (by simp only [initState]; exact hwv)
          exact reEquiv_execution hd hdec hbody (execResultsEquiv.revert hΞ rfl)
        · have hdec : config.externalABI.decodeCalldata?
              (wExpTransition.params.map Param.name)
              (transitionSignature wExpTransition).paramTypes I.calldata = none := by
            show decodeCalldataWithMode .modern _ _ I.calldata = none
            exact wExpDecode_none hsz (Or.inl (by omega))
          exact reEquiv_decodingFailed hd hdec hΞ
      · have hdec : config.externalABI.decodeCalldata?
            (wExpTransition.params.map Param.name)
            (transitionSignature wExpTransition).paramTypes I.calldata = none := by
          show decodeCalldataWithMode .modern _ _ I.calldata = none
          exact wExpDecode_none hsz (Or.inr (by omega))
        exact reEquiv_decodingFailed hd hdec hΞ

end Benchmarks.Midnight.TickLibWrapper
