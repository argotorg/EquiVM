import Benchmarks.UniswapV3.Pool.SourceSignedBits
import Benchmarks.UniswapV3.Pool.SignedComparison

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 1000

-- GENERALIZES the binary arithmetic stepping lemmas to signed remainder.
theorem smod_xstep {s : EVM.State} {code : ByteArray} {pcv a b : UInt256} {t : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = pcv)
    (hdec : decode code pcv = some (.SMOD, .none))
    (hstk : s.machineState.stack = a :: b :: t) (hov : t.length + 1 ≤ 1024) :
    Xstep (D_J code 0) s =
      if s.machineState.gasAvailable.toNat < 5 then .error .OutOfGass
      else .ok (stBinop5 s (UInt256.smod a b) t, .none) := by
  have hd : decode s.executionEnv.code s.machineState.pc = some (.SMOD, .none) := by
    rw [hcode, hpc]
    exact hdec
  rw [← hcode, step_smod s hd, hstk]
  have hov' : ¬ ((a :: b :: t).length - 2 + 1 > 1024) := by
    simp only [List.length_cons]
    omega
  simp only [if_neg hov', GasConstants.Glow, stBinop5]

theorem RD.smod {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : EVM.State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : AccountMap} {k C : Nat} {a b : UInt256} {t : List UInt256}
    (h : RD code ee g s0 pc (a :: b :: t) mem aw rdata acc k C)
    (hdec : decode code pc = some (.SMOD, .none)) (hov : t.length + 1 ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩) (UInt256.smod a b :: t) mem aw rdata acc
      (k + 1) (C + 5) :=
  RD.stepBinop5 h (fun _ hc hp hs ↦ smod_xstep hc hp hdec hs hov)

-- LIBRARY CANDIDATE: the machine sign and magnitude of a bounded signed integer.
theorem wordOfInt_sign_magnitude (i : Int)
    (hlo : -(2 ^ 255 : Int) ≤ i) (hhi : i < 2 ^ 255) :
    (UInt256.abs (EVM.wordOfInt i)).toNat = i.natAbs ∧
      UInt256.sgn (EVM.wordOfInt i) = i.sign := by
  by_cases hn : i < 0
  · have hi : i = -(Int.ofNat i.natAbs) := Int.eq_neg_natAbs_of_nonpos (le_of_lt hn)
    have hw := wordOfInt_toNat_of_neg_of_abs_lt i hn
      (show i.natAbs < EVM.wordModulus by change _ < 2 ^ 256; omega)
    have hh : 2 ^ 255 ≤ (EVM.wordOfInt i).toNat := by
      rw [hw]
      change 2 ^ 255 ≤ 2 ^ 256 - i.natAbs
      omega
    constructor
    · rw [u256_abs_high_toNat hh (by omega), hw]
      change 2 ^ 256 - (2 ^ 256 - i.natAbs) = i.natAbs
      omega
    · rw [UInt256.sgn, if_pos hh, Int.sign_eq_neg_one_of_neg hn]
  · have hi0 : 0 ≤ i := by omega
    have hw : (EVM.wordOfInt i).toNat = i.toNat := by
      rw [wordOfInt_nonneg i hi0]
      exact ulit_toNat' _ (by change _ < 2 ^ 256; omega)
    have hh : ¬ 2 ^ 255 ≤ (EVM.wordOfInt i).toNat := by rw [hw]; omega
    constructor
    · rw [UInt256.abs, if_neg hh, hw]
      omega
    · by_cases hz : i = 0
      · subst i
        rfl
      · have hnz : EVM.wordOfInt i ≠ (⟨0⟩ : UInt256) := by
          intro he
          have hz' := congrArg UInt256.toNat he
          rw [hw] at hz'
          change i.toNat = 0 at hz'
          omega
        simp only [UInt256.sgn, if_neg hh, UInt256.eq0, beq_iff_eq, if_neg hnz]
        exact (Int.sign_eq_one_of_pos (by omega)).symm

-- LIBRARY CANDIDATE: the EVM signed conversion agrees with modular encoding on signed values.
theorem toSigned_eq_wordOfInt (i : Int) (hlo : -(2 ^ 255 : Int) ≤ i) :
    UInt256.toSigned i = EVM.wordOfInt i := by
  cases i with
  | ofNat n => exact (wordOfInt_ofNat_eq n).symm
  | negSucc n =>
      have hi : Int.negSucc n < 0 := by omega
      have hn : n + 1 < UInt256.size := by change n + 1 < 2 ^ 256; omega
      apply u256_inj
      rw [wordOfInt_toNat_of_neg_of_abs_lt _ hi (by exact hn)]
      change (UInt256.ofNat (UInt256.size - 1 - n)).toNat = UInt256.size - (n + 1)
      rw [ulit_toNat' _ (by omega)]
      omega

-- LIBRARY CANDIDATE: truncating remainder preserves the Euclidean residue.
theorem tmod_emod (i j : Int) : (i.tmod j) % j = i % j := by
  rw [Int.tmod_def, Int.sub_mul_emod_self_left]

-- LIBRARY CANDIDATE: a nonzero word divisor makes EVM MOD the natural remainder.
theorem word_mod_toNat (a b : UInt256) (hb : b.toNat ≠ 0) :
    (a % b).toNat = a.toNat % b.toNat := by
  have hv : b.val ≠ 0 := by
    intro he
    exact hb (congrArg Fin.val he)
  change (UInt256.mod a b).toNat = _
  rw [UInt256.mod, if_neg (by simpa only [beq_iff_eq] using hv)]
  rfl

-- LIBRARY CANDIDATE: signed remainder is its dividend's sign times the unsigned remainder.
theorem tmod_sign_magnitude (i j : Int) :
    i.tmod j = i.sign * Int.ofNat (i.natAbs % j.natAbs) := by
  cases i with
  | ofNat n =>
      cases n with
      | zero => cases j <;> rfl
      | succ n => cases j <;> simp only [Int.tmod, Int.sign, Int.natAbs, Int.one_mul]
  | negSucc n => cases j <;> simp only [Int.tmod, Int.sign, Int.natAbs, Int.neg_one_mul]

-- LIBRARY CANDIDATE: EVM SMOD agrees with truncating signed integer remainder.
theorem wordOfInt_smod (i j : Int)
    (hilo : -(2 ^ 255 : Int) ≤ i) (hihi : i < 2 ^ 255)
    (hjlo : -(2 ^ 255 : Int) ≤ j) (hjhi : j < 2 ^ 255) (hjn : j ≠ 0) :
    UInt256.smod (EVM.wordOfInt i) (EVM.wordOfInt j) = EVM.wordOfInt (i.tmod j) := by
  obtain ⟨hai, hsi⟩ := wordOfInt_sign_magnitude i hilo hihi
  obtain ⟨haj, hsj⟩ := wordOfInt_sign_magnitude j hjlo hjhi
  have hmodulus : (UInt256.abs (EVM.wordOfInt j)).toNat ≠ 0 := by rw [haj]; omega
  have hjw : (EVM.wordOfInt j).toNat ≠ 0 := by
    intro hz
    have he := uint256_toNat_eq_zero hz
    rw [he] at haj
    change 0 = j.natAbs at haj
    omega
  have hrlo : -(2 ^ 255 : Int) ≤ i.tmod j := by
    have hm := Nat.mod_le i.natAbs j.natAbs
    have hab := Int.natAbs_tmod i j
    omega
  rw [UInt256.smod, if_neg (by simpa only [beq_iff_eq] using hjw),
    word_mod_toNat _ _ hmodulus, hai, haj, hsi]
  change UInt256.toSigned (i.sign * Int.ofNat (i.natAbs % j.natAbs)) = _
  rw [← tmod_sign_magnitude]
  exact toSigned_eq_wordOfInt _ hrlo

end Benchmarks.UniswapV3.Pool
