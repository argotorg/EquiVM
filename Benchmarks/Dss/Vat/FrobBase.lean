import Benchmarks.Dss.Vat.Fork
import Benchmarks.Dss.Vat.Grab
import Benchmarks.Dss.Vat.Signed
import Mathlib.Tactic.SuppressCompilation

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Reasoning.Theory

suppress_compilation

theorem dup12_xstep {s : State} {code : ByteArray}
    {pcv a b c d e f gg hh ii jj kk ll : UInt256} {t : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = pcv)
    (hdec : decode code pcv = some (.DUP12, .none))
    (hstk : s.machineState.stack =
      a :: b :: c :: d :: e :: f :: gg :: hh :: ii :: jj :: kk :: ll :: t)
    (hov : t.length + 13 ≤ 1024) :
    Xstep (D_J code 0) s
      = (if s.machineState.gasAvailable.toNat < 3 then .error .OutOfGass
         else .ok
          (stSwap s
            (ll :: a :: b :: c :: d :: e :: f :: gg :: hh :: ii :: jj :: kk :: ll :: t),
            .none)) := by
  have hd : decode s.executionEnv.code s.machineState.pc = some (.DUP12, .none) := by
    rw [hcode, hpc]; exact hdec
  rw [← hcode, step_dup12 s hd, hstk]
  have hov' :
      ¬ ((a :: b :: c :: d :: e :: f :: gg :: hh :: ii :: jj :: kk :: ll :: t).length -
          12 + 13 > 1024) := by
    simp only [List.length_cons]; omega
  simp only [if_neg hov', GasConstants.Gverylow, stSwap]

theorem swap13_xstep {s : State} {code : ByteArray}
    {pcv a b c d e f gg hh ii jj kk ll mm nn : UInt256} {t : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = pcv)
    (hdec : decode code pcv = some (.SWAP13, .none))
    (hstk : s.machineState.stack =
      a :: b :: c :: d :: e :: f :: gg :: hh :: ii :: jj :: kk :: ll :: mm :: nn :: t)
    (hov : t.length + 14 ≤ 1024) :
    Xstep (D_J code 0) s
      = (if s.machineState.gasAvailable.toNat < 3 then .error .OutOfGass
         else .ok
          (stSwap s
            (nn :: b :: c :: d :: e :: f :: gg :: hh :: ii :: jj :: kk :: ll :: mm :: a :: t),
            .none)) := by
  have hd : decode s.executionEnv.code s.machineState.pc = some (.SWAP13, .none) := by
    rw [hcode, hpc]; exact hdec
  rw [← hcode, step_swap13 s hd, hstk]
  have hov' :
      ¬ ((a :: b :: c :: d :: e :: f :: gg :: hh :: ii :: jj :: kk :: ll :: mm :: nn :: t).length -
          14 + 14 > 1024) := by
    simp only [List.length_cons]; omega
  simp only [if_neg hov', GasConstants.Gverylow, stSwap]

end Reasoning.Theory

namespace Reasoning.Reach

theorem RD.dup12 {code : ByteArray} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a b c d e f gg hh ii jj kk ll : UInt256} {t : List UInt256}
    (h : RD code ee g s0 pc
      (a :: b :: c :: d :: e :: f :: gg :: hh :: ii :: jj :: kk :: ll :: t)
      mem aw rdata acc k C)
    (hdec : decode code pc = some (.DUP12, .none)) (hov : t.length + 13 ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩)
      (ll :: a :: b :: c :: d :: e :: f :: gg :: hh :: ii :: jj :: kk :: ll :: t)
      mem aw rdata acc (k + 1) (C + 3) :=
  h.stepSwap (fun _ hc hp hs => Reasoning.Theory.dup12_xstep hc hp hdec hs hov)

theorem RD.swap13 {code : ByteArray} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a b c d e f gg hh ii jj kk ll mm nn : UInt256} {t : List UInt256}
    (h : RD code ee g s0 pc
      (a :: b :: c :: d :: e :: f :: gg :: hh :: ii :: jj :: kk :: ll :: mm :: nn :: t)
      mem aw rdata acc k C)
    (hdec : decode code pc = some (.SWAP13, .none)) (hov : t.length + 14 ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩)
      (nn :: b :: c :: d :: e :: f :: gg :: hh :: ii :: jj :: kk :: ll :: mm :: a :: t)
      mem aw rdata acc (k + 1) (C + 3) :=
  h.stepSwap (fun _ hc hp hs => Reasoning.Theory.swap13_xstep hc hp hdec hs hov)

end Reasoning.Reach

namespace Benchmarks.Dss.Vat

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

/-! ## `frob(bytes32,address,address,address,int256,int256)` -/

theorem sstoreAccountMap_storage_findD_self_present
    (σ : AccountMap) (a : AccountAddress) {acc : Account}
    (hacc : σ.find? a = some acc) (slot val : UInt256) :
    (((sstoreAccountMap a σ slot val).find? a).option (default : UInt256)
        (fun acc => acc.storage.findD slot (default : UInt256))) = val := by
  unfold sstoreAccountMap
  rw [hacc]
  simp only [Option.option]
  rw [accountMap_find_insert_self]
  by_cases hzero : (val == (default : UInt256)) = true
  · have hval : val = (default : UInt256) := eq_of_beq hzero
    subst val
    simp
    exact storage_findD_erase_self acc.storage slot (default : UInt256)
  · simp [hzero]
    exact storage_findD_insert_self acc.storage slot val (default : UInt256)

abbrev frobIWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 4

abbrev frobUWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 36

abbrev frobVWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 68

abbrev frobWWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 100

abbrev frobUMaskedWord (I : ExecutionEnv) : UInt256 :=
  UInt256.land solcAddrMask (frobUWord I)

abbrev frobVMaskedWord (I : ExecutionEnv) : UInt256 :=
  UInt256.land solcAddrMask (frobVWord I)

abbrev frobWMaskedWord (I : ExecutionEnv) : UInt256 :=
  UInt256.land solcAddrMask (frobWWord I)

abbrev frobDinkWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 132

abbrev frobDartWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 164

abbrev frobDinkInt (I : ExecutionEnv) : Int :=
  if (frobDinkWord I).toNat < EVM.twoPow 255 then
    Int.ofNat (frobDinkWord I).toNat
  else
    Int.ofNat (frobDinkWord I).toNat - Int.ofNat EVM.wordModulus

abbrev frobDartInt (I : ExecutionEnv) : Int :=
  if (frobDartWord I).toNat < EVM.twoPow 255 then
    Int.ofNat (frobDartWord I).toNat
  else
    Int.ofNat (frobDartWord I).toNat - Int.ofNat EVM.wordModulus

theorem frobDinkInt_mod_word (I : ExecutionEnv) :
    frobDinkInt I % (Int.ofNat EVM.wordModulus) =
      Int.ofNat (frobDinkWord I).toNat := by
  have hltMod :
      Int.ofNat (frobDinkWord I).toNat < Int.ofNat EVM.wordModulus := by
    exact Int.ofNat_lt.mpr (by
      change (frobDinkWord I).val.val < EVM.twoPow 256
      exact (frobDinkWord I).val.isLt)
  have hbase :
      Int.ofNat (frobDinkWord I).toNat % Int.ofNat EVM.wordModulus =
        Int.ofNat (frobDinkWord I).toNat :=
    Int.emod_eq_of_lt (Int.natCast_nonneg _) hltMod
  unfold frobDinkInt
  split
  · exact hbase
  · rw [← Int.emod_eq_sub_self_emod]
    exact hbase

theorem frobDartInt_mod_word (I : ExecutionEnv) :
    frobDartInt I % (Int.ofNat EVM.wordModulus) =
      Int.ofNat (frobDartWord I).toNat := by
  have hltMod :
      Int.ofNat (frobDartWord I).toNat < Int.ofNat EVM.wordModulus := by
    exact Int.ofNat_lt.mpr (by
      change (frobDartWord I).val.val < EVM.twoPow 256
      exact (frobDartWord I).val.isLt)
  have hbase :
      Int.ofNat (frobDartWord I).toNat % Int.ofNat EVM.wordModulus =
        Int.ofNat (frobDartWord I).toNat :=
    Int.emod_eq_of_lt (Int.natCast_nonneg _) hltMod
  unfold frobDartInt
  split
  · exact hbase
  · rw [← Int.emod_eq_sub_self_emod]
    exact hbase

theorem frobDartInt_lo (I : ExecutionEnv) :
    -((2 : Int) ^ 255) ≤ frobDartInt I := by
  unfold frobDartInt
  by_cases h : (frobDartWord I).toNat < EVM.twoPow 255
  · rw [if_pos h]
    have hnonneg : (0 : Int) ≤ Int.ofNat (frobDartWord I).toNat :=
      Int.natCast_nonneg _
    have hpowNonneg : (0 : Int) ≤ (2 : Int) ^ 255 := by norm_num
    omega
  · rw [if_neg h]
    have hge : EVM.twoPow 255 ≤ (frobDartWord I).toNat := not_lt.mp h
    have hM : Int.ofNat EVM.wordModulus = (2 : Int) ^ 255 + (2 : Int) ^ 255 := by
      norm_num [EVM.wordModulus, EVM.twoPow]
    have hgeInt : (2 : Int) ^ 255 ≤ Int.ofNat (frobDartWord I).toNat := by
      change Int.ofNat (EVM.twoPow 255) ≤ Int.ofNat (frobDartWord I).toNat
      exact Int.ofNat_le.mpr hge
    rw [hM]
    omega

theorem frobDartInt_hi (I : ExecutionEnv) :
    frobDartInt I < (2 : Int) ^ 255 := by
  unfold frobDartInt
  by_cases h : (frobDartWord I).toNat < EVM.twoPow 255
  · rw [if_pos h]
    change Int.ofNat (frobDartWord I).toNat < Int.ofNat (EVM.twoPow 255)
    exact Int.ofNat_lt.mpr h
  · rw [if_neg h]
    have hlt : (frobDartWord I).toNat < EVM.wordModulus := by
      change (frobDartWord I).val.val < EVM.twoPow 256
      exact (frobDartWord I).val.isLt
    have hltInt : Int.ofNat (frobDartWord I).toNat < Int.ofNat EVM.wordModulus := by
      exact Int.ofNat_lt.mpr hlt
    have hpowPos : (0 : Int) < (2 : Int) ^ 255 := by norm_num
    omega

theorem frobDtab_mod_word (I : ExecutionEnv) (rate : UInt256) :
    (Int.ofNat rate.toNat * frobDartInt I) % (Int.ofNat EVM.wordModulus) =
      Int.ofNat (UInt256.mul (frobDartWord I) rate).toNat := by
  have hrateLt : rate.toNat < EVM.wordModulus := by
    change rate.val.val < EVM.twoPow 256
    exact rate.val.isLt
  calc
    (Int.ofNat rate.toNat * frobDartInt I) % (Int.ofNat EVM.wordModulus)
        = (Int.ofNat rate.toNat % Int.ofNat EVM.wordModulus *
            (frobDartInt I % Int.ofNat EVM.wordModulus)) %
            Int.ofNat EVM.wordModulus := by
          rw [Int.mul_emod]
    _ = (Int.ofNat rate.toNat * Int.ofNat (frobDartWord I).toNat) %
            Int.ofNat EVM.wordModulus := by
          rw [frobDartInt_mod_word]
          have hrateMod :
              Int.ofNat rate.toNat % Int.ofNat EVM.wordModulus =
                Int.ofNat rate.toNat :=
            Int.emod_eq_of_lt (Int.natCast_nonneg _) (Int.ofNat_lt.mpr hrateLt)
          rw [hrateMod]
    _ = Int.ofNat ((rate.toNat * (frobDartWord I).toNat) % EVM.wordModulus) := by
          change Int.ofNat (rate.toNat * (frobDartWord I).toNat) %
              Int.ofNat EVM.wordModulus =
            Int.ofNat ((rate.toNat * (frobDartWord I).toNat) % EVM.wordModulus)
          exact (Int.natCast_emod (rate.toNat * (frobDartWord I).toNat)
            EVM.wordModulus).symm
    _ = Int.ofNat (UInt256.mul (frobDartWord I) rate).toNat := by
          rw [u256_mul_toNat]
          rw [Nat.mul_comm rate.toNat (frobDartWord I).toNat]
          rw [show EVM.wordModulus = UInt256.size by rfl]

theorem frobDartInt_eq_of_low (I : ExecutionEnv)
    (hlow : (frobDartWord I).toNat < EVM.twoPow 255) :
    frobDartInt I = Int.ofNat (frobDartWord I).toNat := by
  unfold frobDartInt
  rw [if_pos hlow]

theorem frobDartInt_eq_of_high (I : ExecutionEnv)
    (hhigh : EVM.twoPow 255 ≤ (frobDartWord I).toNat) :
    frobDartInt I =
      Int.ofNat (frobDartWord I).toNat - Int.ofNat EVM.wordModulus := by
  unfold frobDartInt
  rw [if_neg (by simpa [EVM.twoPow] using not_lt.mpr hhigh)]

theorem frobDartInt_zero_of_word_zero (I : ExecutionEnv)
    (hword : frobDartWord I = ⟨0⟩) :
    frobDartInt I = 0 := by
  unfold frobDartInt
  rw [hword]
  simp [EVM.twoPow]

theorem frobDartInt_neg_of_high (I : ExecutionEnv)
    (hhigh : EVM.twoPow 255 ≤ (frobDartWord I).toNat) :
    frobDartInt I < 0 := by
  rw [frobDartInt_eq_of_high I hhigh]
  have hlt : Int.ofNat (frobDartWord I).toNat < Int.ofNat EVM.wordModulus := by
    have hltNat : (frobDartWord I).toNat < EVM.wordModulus := by
      change (frobDartWord I).val.val < EVM.twoPow 256
      exact (frobDartWord I).val.isLt
    exact Int.ofNat_lt.mpr hltNat
  exact sub_neg.mpr hlt

theorem frobDartInt_ne_zero_of_word_ne (I : ExecutionEnv)
    (hword : frobDartWord I ≠ ⟨0⟩) :
    frobDartInt I ≠ 0 := by
  by_cases hlow : (frobDartWord I).toNat < EVM.twoPow 255
  · rw [frobDartInt_eq_of_low I hlow]
    intro hzero
    apply hword
    apply uint256_toNat_eq_zero
    exact Int.ofNat_eq_zero.mp hzero
  · have hhigh : EVM.twoPow 255 ≤ (frobDartWord I).toNat := not_lt.mp hlow
    have hneg := frobDartInt_neg_of_high I hhigh
    omega

theorem frob_dtab_product_range_of_guard
    (I : ExecutionEnv) {rate : UInt256}
    (hrateLow : rate.toNat < EVM.twoPow 255)
    (hguard :
      frobDartWord I = ⟨0⟩ ∨
        UInt256.sdiv (UInt256.mul (frobDartWord I) rate) (frobDartWord I) = rate) :
    -((2 : Int) ^ 255) ≤ Int.ofNat rate.toNat * frobDartInt I ∧
      Int.ofNat rate.toNat * frobDartInt I < (2 : Int) ^ 255 := by
  have hguard' :
      grabDartWord I = ⟨0⟩ ∨
        UInt256.sdiv (UInt256.mul (grabDartWord I) rate) (grabDartWord I) = rate := by
    cases hguard with
    | inl hzero =>
        exact Or.inl (by simpa [grabDartWord, frobDartWord] using hzero)
    | inr hdiv =>
        exact Or.inr (by simpa [grabDartWord, frobDartWord] using hdiv)
  have h := grab_dtab_product_range_of_guard I (rate := rate) hrateLow hguard'
  change
    -((2 : Int) ^ 255) ≤ Int.ofNat rate.toNat * grabDartInt I ∧
      Int.ofNat rate.toNat * grabDartInt I < (2 : Int) ^ 255
  exact h

theorem uintCheckedMulGuard_to_fit_and_source_guard {a b : UInt256}
    (hguard :
      b = ⟨0⟩ ∨
        UInt256.eq (UInt256.div (UInt256.mul a b) b) a ≠ ⟨0⟩) :
    a.toNat * b.toNat < UInt256.size ∧
      (b.toNat = 0 ∨ (UInt256.mul a b).toNat / b.toNat = a.toNat) := by
  let prod := UInt256.mul a b
  by_cases hbzeroNat : b.toNat = 0
  · constructor
    · rw [hbzeroNat, Nat.mul_zero]
      native_decide
    · exact Or.inl hbzeroNat
  · have hbzeroWord : b ≠ ⟨0⟩ := by
      intro hzero
      exact hbzeroNat (by rw [hzero]; rfl)
    have hdivWord : UInt256.div prod b = a := by
      cases hguard with
      | inl hzero => exact False.elim (hbzeroWord hzero)
      | inr heq =>
          exact u256_eq_ne_zero_to_eq (by simpa [prod] using heq)
    have hdivNat : prod.toNat / b.toNat = a.toNat := by
      have h := congrArg UInt256.toNat hdivWord
      simpa [prod, udiv_toNat] using h
    have hleDiv : a.toNat ≤ prod.toNat / b.toNat := by
      rw [hdivNat]
    have hprodLe : a.toNat * b.toNat ≤ prod.toNat := by
      have hle := Nat.mul_le_of_le_div b.toNat a.toNat prod.toNat hleDiv
      simpa [Nat.mul_comm] using hle
    constructor
    · exact lt_of_le_of_lt hprodLe prod.val.isLt
    · exact Or.inr hdivNat

theorem uintCheckedMulFail_to_overflow {a b : UInt256}
    (hfail :
      ¬ (b = ⟨0⟩ ∨
        UInt256.eq (UInt256.div (UInt256.mul a b) b) a ≠ ⟨0⟩)) :
    UInt256.size ≤ a.toNat * b.toNat := by
  by_contra hnot
  have hfit : a.toNat * b.toNat < UInt256.size := by omega
  by_cases hbzeroNat : b.toNat = 0
  · exact hfail (Or.inl (uint256_toNat_eq_zero hbzeroNat))
  · have hbpos : 0 < b.toNat := Nat.pos_of_ne_zero hbzeroNat
    let prod := UInt256.mul a b
    have hprodNat : prod.toNat = a.toNat * b.toNat := by
      dsimp [prod]
      rw [u256_mul_toNat, Nat.mod_eq_of_lt hfit]
    have hdivNat : (UInt256.div prod b).toNat = a.toNat := by
      rw [udiv_toNat, hprodNat]
      simpa [Nat.mul_comm] using Nat.mul_div_right a.toNat hbpos
    have hdivWord : UInt256.div prod b = a := by
      rw [← u256_ofNat_toNat (UInt256.div prod b), hdivNat, u256_ofNat_toNat]
    have heq : UInt256.eq (UInt256.div (UInt256.mul a b) b) a ≠ ⟨0⟩ := by
      rw [show UInt256.div (UInt256.mul a b) b = a by simpa [prod] using hdivWord]
      rw [uInt256_eq_self]
      exact one_ne_zero_uint
    exact hfail (Or.inr heq)

theorem frobSignedAddGuardNegCond_of_not {i : Int} {old new : Nat}
    (h : ¬ (0 ≤ i ∨ new ≤ old)) :
    i < 0 ∧ old < new := by
  omega

theorem frobSignedAddGuardPosCond_of_not {i : Int} {old new : Nat}
    (h : ¬ (i ≤ 0 ∨ old ≤ new)) :
    0 < i ∧ new < old := by
  omega

theorem frobDinkAddGuardNegCond {I : ExecutionEnv} {old new : UInt256}
    (h :
      UInt256.slt (frobDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.gt new old = ⟨0⟩) :
    0 ≤ frobDinkInt I ∨ new.toNat ≤ old.toNat := by
  cases h with
  | inl hslt =>
      exact Or.inl (slt_zero_eq_zero_to_nonneg (frobDinkWord I) hslt)
  | inr hgt =>
      exact Or.inr (ugt_eq_zero_to_le hgt)

theorem frobDinkAddGuardPosCond {I : ExecutionEnv} {old new : UInt256}
    (h :
      UInt256.sgt (frobDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.lt new old = ⟨0⟩) :
    frobDinkInt I ≤ 0 ∨ old.toNat ≤ new.toNat := by
  cases h with
  | inl hsgt =>
      exact Or.inl (sgt_zero_eq_zero_to_nonpos (frobDinkWord I) hsgt)
  | inr hlt =>
      exact Or.inr (ult_eq_zero_to_le hlt)

theorem frobDartAddGuardNegCond {I : ExecutionEnv} {old new : UInt256}
    (h :
      UInt256.slt (frobDartWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.gt new old = ⟨0⟩) :
    0 ≤ frobDartInt I ∨ new.toNat ≤ old.toNat := by
  cases h with
  | inl hslt =>
      exact Or.inl (slt_zero_eq_zero_to_nonneg (frobDartWord I) hslt)
  | inr hgt =>
      exact Or.inr (ugt_eq_zero_to_le hgt)

theorem frobDartAddGuardPosCond {I : ExecutionEnv} {old new : UInt256}
    (h :
      UInt256.sgt (frobDartWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.lt new old = ⟨0⟩) :
    frobDartInt I ≤ 0 ∨ old.toNat ≤ new.toNat := by
  cases h with
  | inl hsgt =>
      exact Or.inl (sgt_zero_eq_zero_to_nonpos (frobDartWord I) hsgt)
  | inr hlt =>
      exact Or.inr (ult_eq_zero_to_le hlt)

theorem frobDinkAddGuardNegFailCond {I : ExecutionEnv} {old new : UInt256}
    (h :
      ¬ (UInt256.slt (frobDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.gt new old = ⟨0⟩)) :
    frobDinkInt I < 0 ∧ old.toNat < new.toNat := by
  constructor
  · exact slt_zero_ne_zero_to_neg (frobDinkWord I) (by
      intro hslt
      exact h (Or.inl hslt))
  · exact ugt_ne_zero_to_gt (by
      intro hgt
      exact h (Or.inr hgt))

theorem frobDinkAddGuardPosFailCond {I : ExecutionEnv} {old new : UInt256}
    (h :
      ¬ (UInt256.sgt (frobDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.lt new old = ⟨0⟩)) :
    0 < frobDinkInt I ∧ new.toNat < old.toNat := by
  constructor
  · exact sgt_zero_ne_zero_to_pos (frobDinkWord I) (by
      intro hsgt
      exact h (Or.inl hsgt))
  · exact ult_ne_zero_to_lt (by
      intro hlt
      exact h (Or.inr hlt))

theorem frobDartAddGuardNegFailCond {I : ExecutionEnv} {old new : UInt256}
    (h :
      ¬ (UInt256.slt (frobDartWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.gt new old = ⟨0⟩)) :
    frobDartInt I < 0 ∧ old.toNat < new.toNat := by
  constructor
  · exact slt_zero_ne_zero_to_neg (frobDartWord I) (by
      intro hslt
      exact h (Or.inl hslt))
  · exact ugt_ne_zero_to_gt (by
      intro hgt
      exact h (Or.inr hgt))

theorem frobDartAddGuardPosFailCond {I : ExecutionEnv} {old new : UInt256}
    (h :
      ¬ (UInt256.sgt (frobDartWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.lt new old = ⟨0⟩)) :
    0 < frobDartInt I ∧ new.toNat < old.toNat := by
  constructor
  · exact sgt_zero_ne_zero_to_pos (frobDartWord I) (by
      intro hsgt
      exact h (Or.inl hsgt))
  · exact ult_ne_zero_to_lt (by
      intro hlt
      exact h (Or.inr hlt))

abbrev frobIValue (I : ExecutionEnv) : Value :=
  .fixedBytes bytes32Width ((I.calldata.toList.drop 4).take 32)

abbrev frobUValue (I : ExecutionEnv) : Value :=
  .address (AccountAddress.ofNat (frobUWord I).toNat)

abbrev frobVValue (I : ExecutionEnv) : Value :=
  .address (AccountAddress.ofNat (frobVWord I).toNat)

abbrev frobWValue (I : ExecutionEnv) : Value :=
  .address (AccountAddress.ofNat (frobWWord I).toNat)

abbrev frobDinkValue (I : ExecutionEnv) : Value :=
  .int (frobDinkInt I)

abbrev frobDartValue (I : ExecutionEnv) : Value :=
  .int (frobDartInt I)

abbrev frobStore (I : ExecutionEnv) : Store :=
  ((((((∅ : Store).insert "i" (frobIValue I)).insert "u" (frobUValue I)).insert
    "v" (frobVValue I)).insert "w" (frobWValue I)).insert "dink" (frobDinkValue I)).insert
    "dart" (frobDartValue I)

theorem frobStore_get_live (I : ExecutionEnv) :
    (frobStore I).get? "live" = none := by
  simp [frobStore]

abbrev frobIKey (I : ExecutionEnv) : KeyValue :=
  .fixedBytes bytes32Width ((I.calldata.toList.drop 4).take 32)

abbrev frobUKey (I : ExecutionEnv) : KeyValue :=
  .address (AccountAddress.ofNat (frobUWord I).toNat)

abbrev frobVKey (I : ExecutionEnv) : KeyValue :=
  .address (AccountAddress.ofNat (frobVWord I).toNat)

abbrev frobWKey (I : ExecutionEnv) : KeyValue :=
  .address (AccountAddress.ofNat (frobWWord I).toNat)

abbrev frobSourceKey (I : ExecutionEnv) : KeyValue :=
  .address I.source

def frobUrnSourceBase (I : ExecutionEnv) : UInt256 :=
  urnsBase (frobIKey I) (frobUKey I)

def frobUrnInkSourceSlot (I : ExecutionEnv) : UInt256 :=
  frobUrnSourceBase I

def frobUrnArtSourceSlot (I : ExecutionEnv) : UInt256 :=
  frobUrnSourceBase I + ⟨1⟩

def frobIlkSourceBase (I : ExecutionEnv) : UInt256 :=
  ilksBase (frobIKey I)

def frobIlkArtSourceSlot (I : ExecutionEnv) : UInt256 :=
  frobIlkSourceBase I

def frobIlkRateSourceSlot (I : ExecutionEnv) : UInt256 :=
  frobIlkSourceBase I + ⟨1⟩

def frobIlkSpotSourceSlot (I : ExecutionEnv) : UInt256 :=
  frobIlkSourceBase I + ⟨2⟩

def frobIlkLineSourceSlot (I : ExecutionEnv) : UInt256 :=
  frobIlkSourceBase I + ⟨3⟩

def frobIlkDustSourceSlot (I : ExecutionEnv) : UInt256 :=
  frobIlkSourceBase I + ⟨4⟩

def frobGemVSourceSlot (I : ExecutionEnv) : UInt256 :=
  gemSlot (frobIKey I) (frobVKey I)

def frobDaiWSourceSlot (I : ExecutionEnv) : UInt256 :=
  daiSlot (frobWKey I)

def frobUrnBase (I : ExecutionEnv) : UInt256 :=
  solcMappingSlot (solcMappingSlot ⟨3⟩ (frobIWord I)) (frobUMaskedWord I)

def frobUrnInkSlot (I : ExecutionEnv) : UInt256 :=
  frobUrnBase I

def frobUrnArtSlot (I : ExecutionEnv) : UInt256 :=
  frobUrnBase I + ⟨1⟩

def frobIlkBase (I : ExecutionEnv) : UInt256 :=
  solcMappingSlot ⟨2⟩ (frobIWord I)

def frobIlkArtSlot (I : ExecutionEnv) : UInt256 :=
  frobIlkBase I

def frobIlkRateSlot (I : ExecutionEnv) : UInt256 :=
  frobIlkBase I + ⟨1⟩

def frobIlkSpotSlot (I : ExecutionEnv) : UInt256 :=
  frobIlkBase I + ⟨2⟩

def frobIlkLineSlot (I : ExecutionEnv) : UInt256 :=
  frobIlkBase I + ⟨3⟩

def frobIlkDustSlot (I : ExecutionEnv) : UInt256 :=
  frobIlkBase I + ⟨4⟩

def frobGemVSlot (I : ExecutionEnv) : UInt256 :=
  solcMappingSlot (solcMappingSlot ⟨4⟩ (frobIWord I)) (frobVMaskedWord I)

def frobDaiWSlot (I : ExecutionEnv) : UInt256 :=
  solcMappingSlot ⟨5⟩ (frobWMaskedWord I)

def frobUWishSlot (I : ExecutionEnv) : UInt256 :=
  solcMappingSlot (solcMappingSlot ⟨1⟩ (frobUMaskedWord I)) (hopeSourceWord I)

def frobVWishSlot (I : ExecutionEnv) : UInt256 :=
  solcMappingSlot (solcMappingSlot ⟨1⟩ (frobVMaskedWord I)) (hopeSourceWord I)

def frobWWishSlot (I : ExecutionEnv) : UInt256 :=
  solcMappingSlot (solcMappingSlot ⟨1⟩ (frobWMaskedWord I)) (hopeSourceWord I)

def frobUrnInkNew (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  frobDinkWord I + solcSlotWord σ I (frobUrnInkSlot I)

def frobUrnArtNew (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  frobDartWord I + solcSlotWord σ I (frobUrnArtSlot I)

def frobIlkArtNew (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  frobDartWord I + solcSlotWord σ I (frobIlkArtSlot I)

def frobDtabWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.mul (frobDartWord I) (solcSlotWord σ I (frobIlkRateSlot I))

def frobTabWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.mul (solcSlotWord σ I (frobIlkRateSlot I)) (frobUrnArtNew σ I)

def frobDebtNew (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  frobDtabWord σ I + solcSlotWord σ I foldDebtSlot

def frobAfterDebt (σ : AccountMap) (I : ExecutionEnv) : AccountMap :=
  sstoreAccountMap I.codeOwner σ foldDebtSlot (frobDebtNew σ I)

def frobGemNew (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.sub (solcSlotWord (frobAfterDebt σ I) I (frobGemVSlot I)) (frobDinkWord I)

def frobDaiNew (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  frobDtabWord σ I +
    solcSlotWord
      (sstoreAccountMap I.codeOwner (frobAfterDebt σ I) (frobGemVSlot I) (frobGemNew σ I))
      I (frobDaiWSlot I)

def frobAfterGem (σ : AccountMap) (I : ExecutionEnv) : AccountMap :=
  sstoreAccountMap I.codeOwner (frobAfterDebt σ I) (frobGemVSlot I) (frobGemNew σ I)

def frobAfterDai (σ : AccountMap) (I : ExecutionEnv) : AccountMap :=
  sstoreAccountMap I.codeOwner (frobAfterGem σ I) (frobDaiWSlot I) (frobDaiNew σ I)

def frobAfterSourceFinal (σ : AccountMap) (I : ExecutionEnv) : AccountMap :=
  sstoreAccountMap I.codeOwner
    (sstoreAccountMap I.codeOwner
      (sstoreAccountMap I.codeOwner (frobAfterDai σ I)
        (frobUrnInkSlot I) (frobUrnInkNew σ I))
      (frobUrnArtSlot I) (frobUrnArtNew σ I))
    (frobIlkArtSlot I) (frobIlkArtNew σ I)

def frobAfterRuntimeFinal (σ : AccountMap) (I : ExecutionEnv) : AccountMap :=
  sstoreAccountMap I.codeOwner
    (sstoreAccountMap I.codeOwner
      (sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner (frobAfterSourceFinal σ I)
          (frobIlkRateSlot I) (solcSlotWord σ I (frobIlkRateSlot I)))
        (frobIlkSpotSlot I) (solcSlotWord σ I (frobIlkSpotSlot I)))
      (frobIlkLineSlot I) (solcSlotWord σ I (frobIlkLineSlot I)))
    (frobIlkDustSlot I) (solcSlotWord σ I (frobIlkDustSlot I))

def frobSourceFinalState
    (cA : Batteries.RBSet AccountAddress compare) (gh : BlockHeader)
    (bl : ProcessedBlocks) (σ σ₀ : AccountMap) (A : Substate)
    (I : ExecutionEnv) (g : UInt256)
    (urnInkNew urnArtNew ilkArtNew gemNew daiNew : UInt256) : State :=
  let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
  let evmDebt := Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner
    foldDebtSlot (frobDebtNew σ I)
  let evmGem := Solm.EVM.storageStore evmDebt evmDebt.executionEnv.codeOwner
    (frobGemVSourceSlot I) gemNew
  let evmDai := Solm.EVM.storageStore evmGem evmGem.executionEnv.codeOwner
    (frobDaiWSourceSlot I) daiNew
  let evmInk := Solm.EVM.storageStore evmDai evmDai.executionEnv.codeOwner
    (frobUrnInkSourceSlot I) urnInkNew
  let evmArt := Solm.EVM.storageStore evmInk evmInk.executionEnv.codeOwner
    (frobUrnArtSourceSlot I) urnArtNew
  let evmIlk := Solm.EVM.storageStore evmArt evmArt.executionEnv.codeOwner
    (frobIlkArtSourceSlot I) ilkArtNew
  let evmRate := Solm.EVM.storageStore evmIlk evmIlk.executionEnv.codeOwner
    (frobIlkRateSourceSlot I) (solcSlotWord σ I (frobIlkRateSlot I))
  let evmSpot := Solm.EVM.storageStore evmRate evmRate.executionEnv.codeOwner
    (frobIlkSpotSourceSlot I) (solcSlotWord σ I (frobIlkSpotSlot I))
  let evmLine := Solm.EVM.storageStore evmSpot evmSpot.executionEnv.codeOwner
    (frobIlkLineSourceSlot I) (solcSlotWord σ I (frobIlkLineSlot I))
  Solm.EVM.storageStore evmLine evmLine.executionEnv.codeOwner
    (frobIlkDustSourceSlot I) (solcSlotWord σ I (frobIlkDustSlot I))

theorem frobDinkSubGuardNegCond {I : ExecutionEnv} {old new : UInt256}
    (h :
      UInt256.sgt (frobDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.gt new old = ⟨0⟩) :
    frobDinkInt I ≤ 0 ∨ new.toNat ≤ old.toNat := by
  cases h with
  | inl hsgt =>
      exact Or.inl (sgt_zero_eq_zero_to_nonpos (frobDinkWord I) hsgt)
  | inr hgt =>
      exact Or.inr (ugt_eq_zero_to_le hgt)

theorem frobDinkSubGuardPosCond {I : ExecutionEnv} {old new : UInt256}
    (h :
      UInt256.slt (frobDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.lt new old = ⟨0⟩) :
    0 ≤ frobDinkInt I ∨ old.toNat ≤ new.toNat := by
  cases h with
  | inl hslt =>
      exact Or.inl (slt_zero_eq_zero_to_nonneg (frobDinkWord I) hslt)
  | inr hlt =>
      exact Or.inr (ult_eq_zero_to_le hlt)

theorem frobDinkSubGuardNegFailCond {I : ExecutionEnv} {old new : UInt256}
    (h :
      ¬ (UInt256.sgt (frobDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.gt new old = ⟨0⟩)) :
    0 < frobDinkInt I ∧ old.toNat < new.toNat := by
  constructor
  · exact sgt_zero_ne_zero_to_pos (frobDinkWord I) (by
      intro hsgt
      exact h (Or.inl hsgt))
  · exact ugt_ne_zero_to_gt (by
      intro hgt
      exact h (Or.inr hgt))

theorem frobDinkSubGuardPosFailCond {I : ExecutionEnv} {old new : UInt256}
    (h :
      ¬ (UInt256.slt (frobDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.lt new old = ⟨0⟩)) :
    frobDinkInt I < 0 ∧ new.toNat < old.toNat := by
  constructor
  · exact slt_zero_ne_zero_to_neg (frobDinkWord I) (by
      intro hslt
      exact h (Or.inl hslt))
  · exact ult_ne_zero_to_lt (by
      intro hlt
      exact h (Or.inr hlt))

theorem accountMapEquiv_frobAfterDebt {σ τ : AccountMap} {I : ExecutionEnv}
    (hAccounts : accountMapEquiv σ τ) :
    accountMapEquiv (frobAfterDebt σ I) (frobAfterDebt τ I) := by
  have hDebtOld :
      solcSlotWord σ I foldDebtSlot = solcSlotWord τ I foldDebtSlot :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner foldDebtSlot ⟨0⟩
  have hRateOld :
      solcSlotWord σ I (frobIlkRateSlot I) =
        solcSlotWord τ I (frobIlkRateSlot I) :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner (frobIlkRateSlot I) ⟨0⟩
  have hDebtNew : frobDebtNew σ I = frobDebtNew τ I := by
    simp [frobDebtNew, frobDtabWord, hRateOld, hDebtOld]
  simp [frobAfterDebt, hDebtNew,
    accountMapEquiv_sstoreAccountMap I.codeOwner foldDebtSlot (frobDebtNew τ I)
      hAccounts]

theorem accountMapEquiv_frobAfterGem {σ τ : AccountMap} {I : ExecutionEnv}
    (hAccounts : accountMapEquiv σ τ) :
    accountMapEquiv (frobAfterGem σ I) (frobAfterGem τ I) := by
  have hDebt := accountMapEquiv_frobAfterDebt (I := I) hAccounts
  have hGemOld :
      solcSlotWord (frobAfterDebt σ I) I (frobGemVSlot I) =
        solcSlotWord (frobAfterDebt τ I) I (frobGemVSlot I) :=
    accountMapEquiv_storage_findD hDebt I.codeOwner (frobGemVSlot I) ⟨0⟩
  have hGemNew : frobGemNew σ I = frobGemNew τ I := by
    simp [frobGemNew, hGemOld]
  simp [frobAfterGem, hGemNew,
    accountMapEquiv_sstoreAccountMap I.codeOwner (frobGemVSlot I)
      (frobGemNew τ I) hDebt]

set_option maxHeartbeats 0 in
theorem accountMapEquiv_frobAfterRuntimeFinal {σ τ : AccountMap} {I : ExecutionEnv}
    (hAccounts : accountMapEquiv σ τ) :
    accountMapEquiv (frobAfterRuntimeFinal σ I) (frobAfterRuntimeFinal τ I) := by
  have hDebtOld :
      solcSlotWord σ I foldDebtSlot = solcSlotWord τ I foldDebtSlot :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner foldDebtSlot ⟨0⟩
  have hRateOld :
      solcSlotWord σ I (frobIlkRateSlot I) =
        solcSlotWord τ I (frobIlkRateSlot I) :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner (frobIlkRateSlot I) ⟨0⟩
  have hDebtNew : frobDebtNew σ I = frobDebtNew τ I := by
    simp [frobDebtNew, frobDtabWord, hRateOld, hDebtOld]
  have hDebt :
      accountMapEquiv (frobAfterDebt σ I) (frobAfterDebt τ I) := by
    simp [frobAfterDebt, hDebtNew,
      accountMapEquiv_sstoreAccountMap I.codeOwner foldDebtSlot (frobDebtNew τ I)
        hAccounts]
  have hGemOld :
      solcSlotWord (frobAfterDebt σ I) I (frobGemVSlot I) =
        solcSlotWord (frobAfterDebt τ I) I (frobGemVSlot I) :=
    accountMapEquiv_storage_findD hDebt I.codeOwner (frobGemVSlot I) ⟨0⟩
  have hGemNew : frobGemNew σ I = frobGemNew τ I := by
    simp [frobGemNew, hGemOld]
  have hGem :
      accountMapEquiv (frobAfterGem σ I) (frobAfterGem τ I) := by
    simp [frobAfterGem, hGemNew,
      accountMapEquiv_sstoreAccountMap I.codeOwner (frobGemVSlot I)
        (frobGemNew τ I) hDebt]
  have hDaiOld :
      solcSlotWord (frobAfterGem σ I) I (frobDaiWSlot I) =
        solcSlotWord (frobAfterGem τ I) I (frobDaiWSlot I) :=
    accountMapEquiv_storage_findD hGem I.codeOwner (frobDaiWSlot I) ⟨0⟩
  have hDtab : frobDtabWord σ I = frobDtabWord τ I := by
    simp [frobDtabWord, hRateOld]
  have hDaiOldInline :
      solcSlotWord
          (sstoreAccountMap I.codeOwner (frobAfterDebt σ I) (frobGemVSlot I)
            (frobGemNew σ I)) I (frobDaiWSlot I) =
        solcSlotWord
          (sstoreAccountMap I.codeOwner (frobAfterDebt τ I) (frobGemVSlot I)
            (frobGemNew τ I)) I (frobDaiWSlot I) := by
    simpa [frobAfterGem] using hDaiOld
  have hDaiNew : frobDaiNew σ I = frobDaiNew τ I := by
    simp [frobDaiNew, hDtab, hDaiOldInline]
  have hDai :
      accountMapEquiv (frobAfterDai σ I) (frobAfterDai τ I) := by
    simp [frobAfterDai, hDaiNew,
      accountMapEquiv_sstoreAccountMap I.codeOwner (frobDaiWSlot I)
        (frobDaiNew τ I) hGem]
  have hInkOld :
      solcSlotWord σ I (frobUrnInkSlot I) =
        solcSlotWord τ I (frobUrnInkSlot I) :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner (frobUrnInkSlot I) ⟨0⟩
  have hArtOld :
      solcSlotWord σ I (frobUrnArtSlot I) =
        solcSlotWord τ I (frobUrnArtSlot I) :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner (frobUrnArtSlot I) ⟨0⟩
  have hIlkArtOld :
      solcSlotWord σ I (frobIlkArtSlot I) =
        solcSlotWord τ I (frobIlkArtSlot I) :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner (frobIlkArtSlot I) ⟨0⟩
  have hInkNew : frobUrnInkNew σ I = frobUrnInkNew τ I := by
    simp [frobUrnInkNew, hInkOld]
  have hArtNew : frobUrnArtNew σ I = frobUrnArtNew τ I := by
    simp [frobUrnArtNew, hArtOld]
  have hIlkArtNew : frobIlkArtNew σ I = frobIlkArtNew τ I := by
    simp [frobIlkArtNew, hIlkArtOld]
  have hSource :
      accountMapEquiv (frobAfterSourceFinal σ I) (frobAfterSourceFinal τ I) := by
    simpa [frobAfterSourceFinal, hInkNew, hArtNew, hIlkArtNew] using
      accountMapEquiv_sstoreAccountMap_three I.codeOwner I.codeOwner I.codeOwner
        (frobUrnInkSlot I) (frobUrnInkNew τ I)
        (frobUrnArtSlot I) (frobUrnArtNew τ I)
        (frobIlkArtSlot I) (frobIlkArtNew τ I) hDai
  have hSpotOld :
      solcSlotWord σ I (frobIlkSpotSlot I) =
        solcSlotWord τ I (frobIlkSpotSlot I) :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner (frobIlkSpotSlot I) ⟨0⟩
  have hLineOld :
      solcSlotWord σ I (frobIlkLineSlot I) =
        solcSlotWord τ I (frobIlkLineSlot I) :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner (frobIlkLineSlot I) ⟨0⟩
  have hDustOld :
      solcSlotWord σ I (frobIlkDustSlot I) =
        solcSlotWord τ I (frobIlkDustSlot I) :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner (frobIlkDustSlot I) ⟨0⟩
  simpa [frobAfterRuntimeFinal, hRateOld, hSpotOld, hLineOld, hDustOld] using
    accountMapEquiv_sstoreAccountMap I.codeOwner (frobIlkDustSlot I)
      (solcSlotWord τ I (frobIlkDustSlot I))
      (accountMapEquiv_sstoreAccountMap I.codeOwner (frobIlkLineSlot I)
        (solcSlotWord τ I (frobIlkLineSlot I))
        (accountMapEquiv_sstoreAccountMap I.codeOwner (frobIlkSpotSlot I)
          (solcSlotWord τ I (frobIlkSpotSlot I))
          (accountMapEquiv_sstoreAccountMap I.codeOwner (frobIlkRateSlot I)
            (solcSlotWord τ I (frobIlkRateSlot I)) hSource)))

theorem frobUWishSourceSlot_eq (I : ExecutionEnv) :
    canSlot (frobUKey I) (frobSourceKey I) = frobUWishSlot I := by
  unfold canSlot canOwnerSlot frobUKey frobSourceKey frobUWishSlot frobUMaskedWord
    hopeSourceWord mapSlot solcMappingSlot
  rw [keyValueToWord_address_ofNat_mask, keyValueToWord_address]

theorem frobVWishSourceSlot_eq (I : ExecutionEnv) :
    canSlot (frobVKey I) (frobSourceKey I) = frobVWishSlot I := by
  unfold canSlot canOwnerSlot frobVKey frobSourceKey frobVWishSlot frobVMaskedWord
    hopeSourceWord mapSlot solcMappingSlot
  rw [keyValueToWord_address_ofNat_mask, keyValueToWord_address]

theorem frobWWishSourceSlot_eq (I : ExecutionEnv) :
    canSlot (frobWKey I) (frobSourceKey I) = frobWWishSlot I := by
  unfold canSlot canOwnerSlot frobWKey frobSourceKey frobWWishSlot frobWMaskedWord
    hopeSourceWord mapSlot solcMappingSlot
  rw [keyValueToWord_address_ofNat_mask, keyValueToWord_address]

abbrev frobStoreUrnInk (I : ExecutionEnv) (urnInk : UInt256) : Store :=
  (frobStore I).insert "urnInk" (.int (Int.ofNat urnInk.toNat))

abbrev frobStoreUrnArt (I : ExecutionEnv) (urnInk urnArt : UInt256) : Store :=
  (frobStoreUrnInk I urnInk).insert "urnArt" (.int (Int.ofNat urnArt.toNat))

abbrev frobStoreIlkArt (I : ExecutionEnv) (urnInk urnArt ilkArt : UInt256) : Store :=
  (frobStoreUrnArt I urnInk urnArt).insert "ilkArt" (.int (Int.ofNat ilkArt.toNat))

abbrev frobStoreIlkRate (I : ExecutionEnv) (urnInk urnArt ilkArt ilkRate : UInt256) :
    Store :=
  (frobStoreIlkArt I urnInk urnArt ilkArt).insert "ilkRate"
    (.int (Int.ofNat ilkRate.toNat))

abbrev frobStoreIlkSpot (I : ExecutionEnv)
    (urnInk urnArt ilkArt ilkRate ilkSpot : UInt256) : Store :=
  (frobStoreIlkRate I urnInk urnArt ilkArt ilkRate).insert "ilkSpot"
    (.int (Int.ofNat ilkSpot.toNat))

abbrev frobStoreIlkLine (I : ExecutionEnv)
    (urnInk urnArt ilkArt ilkRate ilkSpot ilkLine : UInt256) : Store :=
  (frobStoreIlkSpot I urnInk urnArt ilkArt ilkRate ilkSpot).insert "ilkLine"
    (.int (Int.ofNat ilkLine.toNat))

abbrev frobStoreIlkDust (I : ExecutionEnv)
    (urnInk urnArt ilkArt ilkRate ilkSpot ilkLine ilkDust : UInt256) : Store :=
  (frobStoreIlkLine I urnInk urnArt ilkArt ilkRate ilkSpot ilkLine).insert "ilkDust"
    (.int (Int.ofNat ilkDust.toNat))

abbrev frobUrnInkEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "urns", steps := [.mindex (frobIKey I), .mindex (frobUKey I), .field "ink"] }

abbrev frobUrnArtEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "urns", steps := [.mindex (frobIKey I), .mindex (frobUKey I), .field "art"] }

abbrev frobIlkFieldEvaledRef (I : ExecutionEnv) (field : Ident) : EvaledStorageRef :=
  { base := "ilks", steps := [.mindex (frobIKey I), .field field] }

abbrev frobWishEvaledRef (usr : KeyValue) (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "can", steps := [.mindex usr, .mindex (frobSourceKey I)] }

abbrev frobGemVEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "gem", steps := [.mindex (frobIKey I), .mindex (frobVKey I)] }

abbrev frobDaiWEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "dai", steps := [.mindex (frobWKey I)] }

theorem frobStore_get_i (I : ExecutionEnv) :
    (frobStore I).get? "i" = some (frobIValue I) := by
  unfold frobStore
  repeat rw [store_get_ne _ _ (by decide)]
  rw [store_get_self]

theorem frobStore_get_u (I : ExecutionEnv) :
    (frobStore I).get? "u" = some (frobUValue I) := by
  unfold frobStore
  repeat rw [store_get_ne _ _ (by decide)]
  rw [store_get_self]

theorem frobStore_get_v (I : ExecutionEnv) :
    (frobStore I).get? "v" = some (frobVValue I) := by
  unfold frobStore
  repeat rw [store_get_ne _ _ (by decide)]
  rw [store_get_self]

theorem frobStore_get_w (I : ExecutionEnv) :
    (frobStore I).get? "w" = some (frobWValue I) := by
  unfold frobStore
  repeat rw [store_get_ne _ _ (by decide)]
  rw [store_get_self]

theorem frobStore_get_dink (I : ExecutionEnv) :
    (frobStore I).get? "dink" = some (frobDinkValue I) := by
  unfold frobStore
  rw [store_get_ne _ _ (by decide)]
  rw [store_get_self]

theorem frobStore_get_dart (I : ExecutionEnv) :
    (frobStore I).get? "dart" = some (frobDartValue I) := by
  unfold frobStore
  rw [store_get_self]

theorem frobStore_urns (I : ExecutionEnv) :
    (frobStore I).get? "urns" = none := by
  simp [frobStore]

theorem frobStore_ilks (I : ExecutionEnv) :
    (frobStore I).get? "ilks" = none := by
  simp [frobStore]

theorem frobStoreUrnInk_get_i (I : ExecutionEnv) (urnInk : UInt256) :
    (frobStoreUrnInk I urnInk).get? "i" = some (frobIValue I) := by
  unfold frobStoreUrnInk
  rw [store_get_ne _ _ (by decide)]
  exact frobStore_get_i I

theorem frobStoreUrnInk_get_u (I : ExecutionEnv) (urnInk : UInt256) :
    (frobStoreUrnInk I urnInk).get? "u" = some (frobUValue I) := by
  unfold frobStoreUrnInk
  rw [store_get_ne _ _ (by decide)]
  exact frobStore_get_u I

theorem frobStoreUrnInk_urns (I : ExecutionEnv) (urnInk : UInt256) :
    (frobStoreUrnInk I urnInk).get? "urns" = none := by
  unfold frobStoreUrnInk
  rw [store_get_ne _ _ (by decide)]
  exact frobStore_urns I

theorem frobStoreUrnArt_get_i (I : ExecutionEnv) (urnInk urnArt : UInt256) :
    (frobStoreUrnArt I urnInk urnArt).get? "i" = some (frobIValue I) := by
  unfold frobStoreUrnArt
  rw [store_get_ne _ _ (by decide)]
  exact frobStoreUrnInk_get_i I urnInk

theorem frobStoreUrnArt_ilks (I : ExecutionEnv) (urnInk urnArt : UInt256) :
    (frobStoreUrnArt I urnInk urnArt).get? "ilks" = none := by
  unfold frobStoreUrnArt frobStoreUrnInk
  rw [store_get_ne _ _ (by decide)]
  rw [store_get_ne _ _ (by decide)]
  exact frobStore_ilks I

theorem frobStoreIlkArt_get_i (I : ExecutionEnv) (urnInk urnArt ilkArt : UInt256) :
    (frobStoreIlkArt I urnInk urnArt ilkArt).get? "i" = some (frobIValue I) := by
  unfold frobStoreIlkArt
  rw [store_get_ne _ _ (by decide)]
  exact frobStoreUrnArt_get_i I urnInk urnArt

theorem frobStoreIlkArt_ilks (I : ExecutionEnv) (urnInk urnArt ilkArt : UInt256) :
    (frobStoreIlkArt I urnInk urnArt ilkArt).get? "ilks" = none := by
  unfold frobStoreIlkArt
  rw [store_get_ne _ _ (by decide)]
  exact frobStoreUrnArt_ilks I urnInk urnArt

theorem frobStoreIlkRate_get_i (I : ExecutionEnv)
    (urnInk urnArt ilkArt ilkRate : UInt256) :
    (frobStoreIlkRate I urnInk urnArt ilkArt ilkRate).get? "i" =
      some (frobIValue I) := by
  unfold frobStoreIlkRate
  rw [store_get_ne _ _ (by decide)]
  exact frobStoreIlkArt_get_i I urnInk urnArt ilkArt

theorem frobStoreIlkRate_ilks (I : ExecutionEnv)
    (urnInk urnArt ilkArt ilkRate : UInt256) :
    (frobStoreIlkRate I urnInk urnArt ilkArt ilkRate).get? "ilks" = none := by
  unfold frobStoreIlkRate
  rw [store_get_ne _ _ (by decide)]
  exact frobStoreIlkArt_ilks I urnInk urnArt ilkArt

theorem frobStoreIlkSpot_get_i (I : ExecutionEnv)
    (urnInk urnArt ilkArt ilkRate ilkSpot : UInt256) :
    (frobStoreIlkSpot I urnInk urnArt ilkArt ilkRate ilkSpot).get? "i" =
      some (frobIValue I) := by
  unfold frobStoreIlkSpot
  rw [store_get_ne _ _ (by decide)]
  exact frobStoreIlkRate_get_i I urnInk urnArt ilkArt ilkRate

theorem frobStoreIlkSpot_ilks (I : ExecutionEnv)
    (urnInk urnArt ilkArt ilkRate ilkSpot : UInt256) :
    (frobStoreIlkSpot I urnInk urnArt ilkArt ilkRate ilkSpot).get? "ilks" = none := by
  unfold frobStoreIlkSpot
  rw [store_get_ne _ _ (by decide)]
  exact frobStoreIlkRate_ilks I urnInk urnArt ilkArt ilkRate

theorem frobStoreIlkLine_get_i (I : ExecutionEnv)
    (urnInk urnArt ilkArt ilkRate ilkSpot ilkLine : UInt256) :
    (frobStoreIlkLine I urnInk urnArt ilkArt ilkRate ilkSpot ilkLine).get? "i" =
      some (frobIValue I) := by
  unfold frobStoreIlkLine
  rw [store_get_ne _ _ (by decide)]
  exact frobStoreIlkSpot_get_i I urnInk urnArt ilkArt ilkRate ilkSpot

theorem frobStoreIlkLine_ilks (I : ExecutionEnv)
    (urnInk urnArt ilkArt ilkRate ilkSpot ilkLine : UInt256) :
    (frobStoreIlkLine I urnInk urnArt ilkArt ilkRate ilkSpot ilkLine).get? "ilks" =
      none := by
  unfold frobStoreIlkLine
  rw [store_get_ne _ _ (by decide)]
  exact frobStoreIlkSpot_ilks I urnInk urnArt ilkArt ilkRate ilkSpot

theorem frobStoreIlkDust_get_rate (I : ExecutionEnv)
    (urnInk urnArt ilkArt ilkRate ilkSpot ilkLine ilkDust : UInt256) :
    (frobStoreIlkDust I urnInk urnArt ilkArt ilkRate ilkSpot ilkLine ilkDust).get?
      "ilkRate" = some (.int (Int.ofNat ilkRate.toNat)) := by
  unfold frobStoreIlkDust frobStoreIlkLine frobStoreIlkSpot frobStoreIlkRate
  rw [store_get_ne _ _ (by decide)]
  rw [store_get_ne _ _ (by decide)]
  rw [store_get_ne _ _ (by decide)]
  rw [store_get_self]

theorem frobStoreIlkDust_get_spot (I : ExecutionEnv)
    (urnInk urnArt ilkArt ilkRate ilkSpot ilkLine ilkDust : UInt256) :
    (frobStoreIlkDust I urnInk urnArt ilkArt ilkRate ilkSpot ilkLine ilkDust).get?
      "ilkSpot" = some (.int (Int.ofNat ilkSpot.toNat)) := by
  unfold frobStoreIlkDust frobStoreIlkLine frobStoreIlkSpot
  rw [store_get_ne _ _ (by decide)]
  rw [store_get_ne _ _ (by decide)]
  rw [store_get_self]

theorem frobStoreIlkDust_get_line (I : ExecutionEnv)
    (urnInk urnArt ilkArt ilkRate ilkSpot ilkLine ilkDust : UInt256) :
    (frobStoreIlkDust I urnInk urnArt ilkArt ilkRate ilkSpot ilkLine ilkDust).get?
      "ilkLine" = some (.int (Int.ofNat ilkLine.toNat)) := by
  unfold frobStoreIlkDust frobStoreIlkLine
  rw [store_get_ne _ _ (by decide)]
  rw [store_get_self]

theorem frobStoreIlkDust_get_urnInk (I : ExecutionEnv)
    (urnInk urnArt ilkArt ilkRate ilkSpot ilkLine ilkDust : UInt256) :
    (frobStoreIlkDust I urnInk urnArt ilkArt ilkRate ilkSpot ilkLine ilkDust).get?
      "urnInk" = some (.int (Int.ofNat urnInk.toNat)) := by
  unfold frobStoreIlkDust frobStoreIlkLine frobStoreIlkSpot frobStoreIlkRate
    frobStoreIlkArt frobStoreUrnArt frobStoreUrnInk
  repeat rw [store_get_ne _ _ (by decide)]
  rw [store_get_self]

theorem frobStoreIlkDust_get_urnArt (I : ExecutionEnv)
    (urnInk urnArt ilkArt ilkRate ilkSpot ilkLine ilkDust : UInt256) :
    (frobStoreIlkDust I urnInk urnArt ilkArt ilkRate ilkSpot ilkLine ilkDust).get?
      "urnArt" = some (.int (Int.ofNat urnArt.toNat)) := by
  unfold frobStoreIlkDust
  rw [store_get_ne _ _ (by decide)]
  unfold frobStoreIlkLine
  rw [store_get_ne _ _ (by decide)]
  unfold frobStoreIlkSpot
  rw [store_get_ne _ _ (by decide)]
  unfold frobStoreIlkRate
  rw [store_get_ne _ _ (by decide)]
  unfold frobStoreIlkArt
  rw [store_get_ne _ _ (by decide)]
  unfold frobStoreUrnArt
  rw [store_get_self]

theorem frobStoreIlkDust_get_ilkArt (I : ExecutionEnv)
    (urnInk urnArt ilkArt ilkRate ilkSpot ilkLine ilkDust : UInt256) :
    (frobStoreIlkDust I urnInk urnArt ilkArt ilkRate ilkSpot ilkLine ilkDust).get?
      "ilkArt" = some (.int (Int.ofNat ilkArt.toNat)) := by
  unfold frobStoreIlkDust
  rw [store_get_ne _ _ (by decide)]
  unfold frobStoreIlkLine
  rw [store_get_ne _ _ (by decide)]
  unfold frobStoreIlkSpot
  rw [store_get_ne _ _ (by decide)]
  unfold frobStoreIlkRate
  rw [store_get_ne _ _ (by decide)]
  unfold frobStoreIlkArt
  rw [store_get_self]

theorem frobStoreIlkDust_get_dink (I : ExecutionEnv)
    (urnInk urnArt ilkArt ilkRate ilkSpot ilkLine ilkDust : UInt256) :
    (frobStoreIlkDust I urnInk urnArt ilkArt ilkRate ilkSpot ilkLine ilkDust).get?
      "dink" = some (frobDinkValue I) := by
  unfold frobStoreIlkDust
  rw [store_get_ne _ _ (by decide)]
  unfold frobStoreIlkLine
  rw [store_get_ne _ _ (by decide)]
  unfold frobStoreIlkSpot
  rw [store_get_ne _ _ (by decide)]
  unfold frobStoreIlkRate
  rw [store_get_ne _ _ (by decide)]
  unfold frobStoreIlkArt
  rw [store_get_ne _ _ (by decide)]
  unfold frobStoreUrnArt
  rw [store_get_ne _ _ (by decide)]
  unfold frobStoreUrnInk
  rw [store_get_ne _ _ (by decide)]
  exact frobStore_get_dink I

theorem frobStoreIlkDust_get_dart (I : ExecutionEnv)
    (urnInk urnArt ilkArt ilkRate ilkSpot ilkLine ilkDust : UInt256) :
    (frobStoreIlkDust I urnInk urnArt ilkArt ilkRate ilkSpot ilkLine ilkDust).get?
      "dart" = some (frobDartValue I) := by
  unfold frobStoreIlkDust
  rw [store_get_ne _ _ (by decide)]
  unfold frobStoreIlkLine
  rw [store_get_ne _ _ (by decide)]
  unfold frobStoreIlkSpot
  rw [store_get_ne _ _ (by decide)]
  unfold frobStoreIlkRate
  rw [store_get_ne _ _ (by decide)]
  unfold frobStoreIlkArt
  rw [store_get_ne _ _ (by decide)]
  unfold frobStoreUrnArt
  rw [store_get_ne _ _ (by decide)]
  unfold frobStoreUrnInk
  rw [store_get_ne _ _ (by decide)]
  exact frobStore_get_dart I

theorem frobStoreIlkDust_get_u (I : ExecutionEnv)
    (urnInk urnArt ilkArt ilkRate ilkSpot ilkLine ilkDust : UInt256) :
    (frobStoreIlkDust I urnInk urnArt ilkArt ilkRate ilkSpot ilkLine ilkDust).get?
      "u" = some (frobUValue I) := by
  unfold frobStoreIlkDust
  rw [store_get_ne _ _ (by decide)]
  unfold frobStoreIlkLine
  rw [store_get_ne _ _ (by decide)]
  unfold frobStoreIlkSpot
  rw [store_get_ne _ _ (by decide)]
  unfold frobStoreIlkRate
  rw [store_get_ne _ _ (by decide)]
  unfold frobStoreIlkArt
  rw [store_get_ne _ _ (by decide)]
  unfold frobStoreUrnArt
  rw [store_get_ne _ _ (by decide)]
  unfold frobStoreUrnInk
  rw [store_get_ne _ _ (by decide)]
  exact frobStore_get_u I

theorem frobStoreIlkDust_get_v (I : ExecutionEnv)
    (urnInk urnArt ilkArt ilkRate ilkSpot ilkLine ilkDust : UInt256) :
    (frobStoreIlkDust I urnInk urnArt ilkArt ilkRate ilkSpot ilkLine ilkDust).get?
      "v" = some (frobVValue I) := by
  unfold frobStoreIlkDust
  rw [store_get_ne _ _ (by decide)]
  unfold frobStoreIlkLine
  rw [store_get_ne _ _ (by decide)]
  unfold frobStoreIlkSpot
  rw [store_get_ne _ _ (by decide)]
  unfold frobStoreIlkRate
  rw [store_get_ne _ _ (by decide)]
  unfold frobStoreIlkArt
  rw [store_get_ne _ _ (by decide)]
  unfold frobStoreUrnArt
  rw [store_get_ne _ _ (by decide)]
  unfold frobStoreUrnInk
  rw [store_get_ne _ _ (by decide)]
  exact frobStore_get_v I

theorem frobStoreIlkDust_get_w (I : ExecutionEnv)
    (urnInk urnArt ilkArt ilkRate ilkSpot ilkLine ilkDust : UInt256) :
    (frobStoreIlkDust I urnInk urnArt ilkArt ilkRate ilkSpot ilkLine ilkDust).get?
      "w" = some (frobWValue I) := by
  unfold frobStoreIlkDust
  rw [store_get_ne _ _ (by decide)]
  unfold frobStoreIlkLine
  rw [store_get_ne _ _ (by decide)]
  unfold frobStoreIlkSpot
  rw [store_get_ne _ _ (by decide)]
  unfold frobStoreIlkRate
  rw [store_get_ne _ _ (by decide)]
  unfold frobStoreIlkArt
  rw [store_get_ne _ _ (by decide)]
  unfold frobStoreUrnArt
  rw [store_get_ne _ _ (by decide)]
  unfold frobStoreUrnInk
  rw [store_get_ne _ _ (by decide)]
  exact frobStore_get_w I

theorem vatEvalExpr_ne_uint256_zero_false {evm : EVM.State} {locals : Store}
    {x : Expr} {a : UInt256}
    (hx : evalExpr? config { contract := contract, locals := locals } evm x =
      .ok (.int (Int.ofNat a.toNat)))
    (hzero : a.toNat = 0) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.binary .ne x (.intLit 0)) = .ok (.bool false) := by
  simp [evalExpr?, EvalResult.bind, bind, hx, evalBinaryOp?, hzero]

theorem vatEvalExpr_ne_uint256_zero_true {evm : EVM.State} {locals : Store}
    {x : Expr} {a : UInt256}
    (hx : evalExpr? config { contract := contract, locals := locals } evm x =
      .ok (.int (Int.ofNat a.toNat)))
    (hpos : 0 < a.toNat) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.binary .ne x (.intLit 0)) = .ok (.bool true) := by
  simp [evalExpr?, EvalResult.bind, bind, hx, evalBinaryOp?]
  omega

private theorem frobIBytes_len (I : ExecutionEnv) (hsz196 : 196 ≤ I.calldata.size) :
    ((I.calldata.toList.drop 4).take 32).length = ↑bytes32Width + 1 := by
  have htlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  rw [List.length_take, List.length_drop, htlen]
  simp [bytes32Width]
  omega

theorem frobUMaskedWord_clean (I : ExecutionEnv) :
    UInt256.land (frobUMaskedWord I) solcAddrMask = frobUMaskedWord I := by
  unfold frobUMaskedWord
  rw [u256_land_comm solcAddrMask (frobUWord I)]
  exact solcAddrMask_clean (solcAddrMask_result_canonical (frobUWord I))

set_option maxHeartbeats 1000000 in
theorem frobUMaskedWord_canonical (I : ExecutionEnv) :
    (frobUMaskedWord I).toNat < EVM.addressModulus := by
  unfold frobUMaskedWord
  rw [u256_land_comm solcAddrMask (frobUWord I)]
  exact solcAddrMask_result_canonical (frobUWord I)

theorem frobVMaskedWord_clean (I : ExecutionEnv) :
    UInt256.land (frobVMaskedWord I) solcAddrMask = frobVMaskedWord I := by
  unfold frobVMaskedWord
  rw [u256_land_comm solcAddrMask (frobVWord I)]
  exact solcAddrMask_clean (solcAddrMask_result_canonical (frobVWord I))

set_option maxHeartbeats 1000000 in
theorem frobVMaskedWord_canonical (I : ExecutionEnv) :
    (frobVMaskedWord I).toNat < EVM.addressModulus := by
  unfold frobVMaskedWord
  rw [u256_land_comm solcAddrMask (frobVWord I)]
  exact solcAddrMask_result_canonical (frobVWord I)

theorem frobWMaskedWord_clean (I : ExecutionEnv) :
    UInt256.land (frobWMaskedWord I) solcAddrMask = frobWMaskedWord I := by
  unfold frobWMaskedWord
  rw [u256_land_comm solcAddrMask (frobWWord I)]
  exact solcAddrMask_clean (solcAddrMask_result_canonical (frobWWord I))

set_option maxHeartbeats 1000000 in
theorem frobWMaskedWord_canonical (I : ExecutionEnv) :
    (frobWMaskedWord I).toNat < EVM.addressModulus := by
  unfold frobWMaskedWord
  rw [u256_land_comm solcAddrMask (frobWWord I)]
  exact solcAddrMask_result_canonical (frobWWord I)

theorem frobHopeSource_ofNat (I : ExecutionEnv) :
    AccountAddress.ofNat (hopeSourceWord I).toNat = I.source := by
  apply Fin.ext
  unfold AccountAddress.ofNat
  rw [hopeSourceWord_toNat, Fin.val_ofNat]
  exact Nat.mod_eq_of_lt I.source.isLt

theorem frobIKeyWord_eq (I : ExecutionEnv) (hsz36 : 36 ≤ I.calldata.size) :
    keyValueToWord (frobIKey I) = frobIWord I := by
  have hword : ABI.bytesToWord ((I.calldata.toList.drop 4).take 32) =
      uInt256OfByteArray (I.calldata.readBytes 4 32) :=
    decode_word_at_eq I.calldata 4 (by omega) (by norm_num)
  simp [keyValueToWord, bytes32Width, ABI.bytesToWord, fromByteArrayBigEndian,
    byteArray_toList_eq, show 32 ≤ I.calldata.size - 4 by omega] at hword ⊢
  exact hword

theorem frobUrnSourceBase_eq (I : ExecutionEnv) (hsz196 : 196 ≤ I.calldata.size) :
    frobUrnSourceBase I = frobUrnBase I := by
  unfold frobUrnSourceBase frobUrnBase urnsBase urnsIlkSlot frobIKey frobUKey
    frobUMaskedWord mapSlot solcMappingSlot
  rw [frobIKeyWord_eq I (by omega), keyValueToWord_address_ofNat_mask]

theorem frobUrnInkSourceSlot_eq (I : ExecutionEnv) (hsz196 : 196 ≤ I.calldata.size) :
    frobUrnInkSourceSlot I = frobUrnInkSlot I := by
  simp [frobUrnInkSourceSlot, frobUrnInkSlot, frobUrnSourceBase_eq I hsz196]

theorem frobUrnArtSourceSlot_eq (I : ExecutionEnv) (hsz196 : 196 ≤ I.calldata.size) :
    frobUrnArtSourceSlot I = frobUrnArtSlot I := by
  simp [frobUrnArtSourceSlot, frobUrnArtSlot, frobUrnSourceBase_eq I hsz196]

theorem frobIlkSourceBase_eq (I : ExecutionEnv) (hsz196 : 196 ≤ I.calldata.size) :
    frobIlkSourceBase I = frobIlkBase I := by
  unfold frobIlkSourceBase frobIlkBase ilksBase frobIKey mapSlot solcMappingSlot
  rw [frobIKeyWord_eq I (by omega)]

theorem frobIlkArtSourceSlot_eq (I : ExecutionEnv) (hsz196 : 196 ≤ I.calldata.size) :
    frobIlkArtSourceSlot I = frobIlkArtSlot I := by
  simp [frobIlkArtSourceSlot, frobIlkArtSlot, frobIlkSourceBase_eq I hsz196]

theorem frobIlkRateSourceSlot_eq (I : ExecutionEnv) (hsz196 : 196 ≤ I.calldata.size) :
    frobIlkRateSourceSlot I = frobIlkRateSlot I := by
  simp [frobIlkRateSourceSlot, frobIlkRateSlot, frobIlkSourceBase_eq I hsz196]

theorem frobIlkSpotSourceSlot_eq (I : ExecutionEnv) (hsz196 : 196 ≤ I.calldata.size) :
    frobIlkSpotSourceSlot I = frobIlkSpotSlot I := by
  simp [frobIlkSpotSourceSlot, frobIlkSpotSlot, frobIlkSourceBase_eq I hsz196]

theorem frobIlkLineSourceSlot_eq (I : ExecutionEnv) (hsz196 : 196 ≤ I.calldata.size) :
    frobIlkLineSourceSlot I = frobIlkLineSlot I := by
  simp [frobIlkLineSourceSlot, frobIlkLineSlot, frobIlkSourceBase_eq I hsz196]

theorem frobIlkDustSourceSlot_eq (I : ExecutionEnv) (hsz196 : 196 ≤ I.calldata.size) :
    frobIlkDustSourceSlot I = frobIlkDustSlot I := by
  simp [frobIlkDustSourceSlot, frobIlkDustSlot, frobIlkSourceBase_eq I hsz196]

theorem frobGemVSourceSlot_eq (I : ExecutionEnv) (hsz196 : 196 ≤ I.calldata.size) :
    frobGemVSourceSlot I = frobGemVSlot I := by
  unfold frobGemVSourceSlot frobGemVSlot gemSlot gemIlkSlot frobIKey frobVKey
    frobVMaskedWord mapSlot solcMappingSlot
  rw [frobIKeyWord_eq I (by omega), keyValueToWord_address_ofNat_mask]

theorem frobDaiWSourceSlot_eq (I : ExecutionEnv) :
    frobDaiWSourceSlot I = frobDaiWSlot I := by
  unfold frobDaiWSourceSlot frobDaiWSlot daiSlot frobWKey frobWMaskedWord mapSlot
    solcMappingSlot
  rw [keyValueToWord_address_ofNat_mask]

set_option maxHeartbeats 1000000 in
theorem accountMapEquiv_frobSourceFinal
    {cA gh bl σ σ₀ A I} {g : UInt256}
    (hsz196 : 196 ≤ I.calldata.size)
    (urnInkNew urnArtNew ilkArtNew gemNew daiNew : UInt256)
    (hInk : urnInkNew = frobUrnInkNew σ I)
    (hArt : urnArtNew = frobUrnArtNew σ I)
    (hIlk : ilkArtNew = frobIlkArtNew σ I)
    (hGem : gemNew = frobGemNew σ I)
    (hDai : daiNew = frobDaiNew σ I) :
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    let evmDebt := Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner
      foldDebtSlot (frobDebtNew σ I)
    let evmGem := Solm.EVM.storageStore evmDebt evmDebt.executionEnv.codeOwner
      (frobGemVSourceSlot I) gemNew
    let evmDai := Solm.EVM.storageStore evmGem evmGem.executionEnv.codeOwner
      (frobDaiWSourceSlot I) daiNew
    let evmInk := Solm.EVM.storageStore evmDai evmDai.executionEnv.codeOwner
      (frobUrnInkSourceSlot I) urnInkNew
    let evmArt := Solm.EVM.storageStore evmInk evmInk.executionEnv.codeOwner
      (frobUrnArtSourceSlot I) urnArtNew
    let evmIlk := Solm.EVM.storageStore evmArt evmArt.executionEnv.codeOwner
      (frobIlkArtSourceSlot I) ilkArtNew
    let evmRate := Solm.EVM.storageStore evmIlk evmIlk.executionEnv.codeOwner
      (frobIlkRateSourceSlot I) (solcSlotWord σ I (frobIlkRateSlot I))
    let evmSpot := Solm.EVM.storageStore evmRate evmRate.executionEnv.codeOwner
      (frobIlkSpotSourceSlot I) (solcSlotWord σ I (frobIlkSpotSlot I))
    let evmLine := Solm.EVM.storageStore evmSpot evmSpot.executionEnv.codeOwner
      (frobIlkLineSourceSlot I) (solcSlotWord σ I (frobIlkLineSlot I))
    let evmDust := Solm.EVM.storageStore evmLine evmLine.executionEnv.codeOwner
      (frobIlkDustSourceSlot I) (solcSlotWord σ I (frobIlkDustSlot I))
    accountMapEquiv (frobAfterRuntimeFinal σ I) evmDust.accountMap := by
  intro evm0 evmDebt evmGem evmDai evmInk evmArt evmIlk evmRate evmSpot evmLine evmDust
  have h0 : accountMapEquiv (frobAfterDebt σ I) evmDebt.accountMap := by
    simpa [evmDebt, evm0, initState, storageStore_accountMap, frobAfterDebt] using
      accountMapEquiv_sstoreAccountMap I.codeOwner foldDebtSlot (frobDebtNew σ I)
        (accountMapEquiv_refl σ)
  have hGemMap : accountMapEquiv (frobAfterGem σ I) evmGem.accountMap := by
    simpa [evmGem, evmDebt, evm0, initState, storageStore_accountMap,
      storageStore_executionEnv, frobAfterGem,
      frobGemVSourceSlot_eq I hsz196, hGem] using
      accountMapEquiv_sstoreAccountMap I.codeOwner (frobGemVSlot I)
        (frobGemNew σ I) h0
  have hDaiMap : accountMapEquiv (frobAfterDai σ I) evmDai.accountMap := by
    simpa [evmDai, evmGem, evmDebt, evm0, initState, storageStore_accountMap,
      storageStore_executionEnv, frobAfterDai, frobDaiWSourceSlot_eq I, hDai] using
      accountMapEquiv_sstoreAccountMap I.codeOwner (frobDaiWSlot I)
        (frobDaiNew σ I) hGemMap
  have hInkMap :
      accountMapEquiv
        (sstoreAccountMap I.codeOwner (frobAfterDai σ I)
          (frobUrnInkSlot I) (frobUrnInkNew σ I))
        evmInk.accountMap := by
    simpa [evmInk, evmDai, evmGem, evmDebt, evm0, initState, storageStore_accountMap,
      storageStore_executionEnv, frobUrnInkSourceSlot_eq I hsz196, hInk] using
      accountMapEquiv_sstoreAccountMap I.codeOwner (frobUrnInkSlot I)
        (frobUrnInkNew σ I) hDaiMap
  have hArtMap :
      accountMapEquiv
        (sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner (frobAfterDai σ I)
            (frobUrnInkSlot I) (frobUrnInkNew σ I))
          (frobUrnArtSlot I) (frobUrnArtNew σ I))
        evmArt.accountMap := by
    simpa [evmArt, evmInk, evmDai, evmGem, evmDebt, evm0, initState,
      storageStore_accountMap,
      storageStore_executionEnv, frobUrnArtSourceSlot_eq I hsz196, hArt] using
      accountMapEquiv_sstoreAccountMap I.codeOwner (frobUrnArtSlot I)
        (frobUrnArtNew σ I) hInkMap
  have hIlkMap : accountMapEquiv (frobAfterSourceFinal σ I) evmIlk.accountMap := by
    simpa [evmIlk, evmArt, evmInk, evmDai, evmGem, evmDebt, evm0, initState,
      storageStore_accountMap, storageStore_executionEnv, frobAfterSourceFinal,
      frobIlkArtSourceSlot_eq I hsz196, hIlk] using
      accountMapEquiv_sstoreAccountMap I.codeOwner (frobIlkArtSlot I)
        (frobIlkArtNew σ I) hArtMap
  have hRateMap :
      accountMapEquiv
        (sstoreAccountMap I.codeOwner (frobAfterSourceFinal σ I)
          (frobIlkRateSlot I) (solcSlotWord σ I (frobIlkRateSlot I)))
        evmRate.accountMap := by
    simpa [evmRate, evmIlk, evmArt, evmInk, evmDai, evmGem, evmDebt, evm0, initState,
      storageStore_accountMap, storageStore_executionEnv,
      frobIlkRateSourceSlot_eq I hsz196] using
      accountMapEquiv_sstoreAccountMap I.codeOwner (frobIlkRateSlot I)
        (solcSlotWord σ I (frobIlkRateSlot I)) hIlkMap
  have hSpotMap :
      accountMapEquiv
        (sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner (frobAfterSourceFinal σ I)
            (frobIlkRateSlot I) (solcSlotWord σ I (frobIlkRateSlot I)))
          (frobIlkSpotSlot I) (solcSlotWord σ I (frobIlkSpotSlot I)))
        evmSpot.accountMap := by
    simpa [evmSpot, evmRate, evmIlk, evmArt, evmInk, evmDai, evmGem, evmDebt, evm0,
      initState, storageStore_accountMap, storageStore_executionEnv,
      frobIlkSpotSourceSlot_eq I hsz196] using
      accountMapEquiv_sstoreAccountMap I.codeOwner (frobIlkSpotSlot I)
        (solcSlotWord σ I (frobIlkSpotSlot I)) hRateMap
  have hLineMap :
      accountMapEquiv
        (sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner
            (sstoreAccountMap I.codeOwner (frobAfterSourceFinal σ I)
              (frobIlkRateSlot I) (solcSlotWord σ I (frobIlkRateSlot I)))
            (frobIlkSpotSlot I) (solcSlotWord σ I (frobIlkSpotSlot I)))
          (frobIlkLineSlot I) (solcSlotWord σ I (frobIlkLineSlot I)))
        evmLine.accountMap := by
    simpa [evmLine, evmSpot, evmRate, evmIlk, evmArt, evmInk, evmDai, evmGem, evmDebt,
      evm0, initState, storageStore_accountMap, storageStore_executionEnv,
      frobIlkLineSourceSlot_eq I hsz196] using
      accountMapEquiv_sstoreAccountMap I.codeOwner (frobIlkLineSlot I)
        (solcSlotWord σ I (frobIlkLineSlot I)) hSpotMap
  simpa [evmDust, evmLine, evmSpot, evmRate, evmIlk, evmArt, evmInk, evmDai,
    evmGem, evmDebt, evm0, initState, storageStore_accountMap, storageStore_executionEnv,
    frobAfterRuntimeFinal, frobIlkDustSourceSlot_eq I hsz196] using
    accountMapEquiv_sstoreAccountMap I.codeOwner (frobIlkDustSlot I)
      (solcSlotWord σ I (frobIlkDustSlot I)) hLineMap

theorem frobSourceFinal_createdAccounts
    {cA gh bl σ σ₀ A I} {g : UInt256}
    (urnInkNew urnArtNew ilkArtNew gemNew daiNew : UInt256) :
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    let evmDebt := Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner
      foldDebtSlot (frobDebtNew σ I)
    let evmGem := Solm.EVM.storageStore evmDebt evmDebt.executionEnv.codeOwner
      (frobGemVSourceSlot I) gemNew
    let evmDai := Solm.EVM.storageStore evmGem evmGem.executionEnv.codeOwner
      (frobDaiWSourceSlot I) daiNew
    let evmInk := Solm.EVM.storageStore evmDai evmDai.executionEnv.codeOwner
      (frobUrnInkSourceSlot I) urnInkNew
    let evmArt := Solm.EVM.storageStore evmInk evmInk.executionEnv.codeOwner
      (frobUrnArtSourceSlot I) urnArtNew
    let evmIlk := Solm.EVM.storageStore evmArt evmArt.executionEnv.codeOwner
      (frobIlkArtSourceSlot I) ilkArtNew
    let evmRate := Solm.EVM.storageStore evmIlk evmIlk.executionEnv.codeOwner
      (frobIlkRateSourceSlot I) (solcSlotWord σ I (frobIlkRateSlot I))
    let evmSpot := Solm.EVM.storageStore evmRate evmRate.executionEnv.codeOwner
      (frobIlkSpotSourceSlot I) (solcSlotWord σ I (frobIlkSpotSlot I))
    let evmLine := Solm.EVM.storageStore evmSpot evmSpot.executionEnv.codeOwner
      (frobIlkLineSourceSlot I) (solcSlotWord σ I (frobIlkLineSlot I))
    let evmDust := Solm.EVM.storageStore evmLine evmLine.executionEnv.codeOwner
      (frobIlkDustSourceSlot I) (solcSlotWord σ I (frobIlkDustSlot I))
    (cA, frobAfterRuntimeFinal σ I).1 = evmDust.createdAccounts := by
  intro evm0 evmDebt evmGem evmDai evmInk evmArt evmIlk evmRate evmSpot evmLine evmDust
  simp [evmDust, evmLine, evmSpot, evmRate, evmIlk, evmArt, evmInk, evmDai,
    evmGem, evmDebt, evm0, initState, storageStore_createdAccounts]

theorem frobSourceFinalState_createdAccounts
    {cA gh bl σ σ₀ A I} {g : UInt256}
    (urnInkNew urnArtNew ilkArtNew gemNew daiNew : UInt256) :
    (cA, frobAfterRuntimeFinal σ I).1 =
      (frobSourceFinalState cA gh bl σ σ₀ A I g
        urnInkNew urnArtNew ilkArtNew gemNew daiNew).createdAccounts := by
  unfold frobSourceFinalState
  exact frobSourceFinal_createdAccounts
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g)
    urnInkNew urnArtNew ilkArtNew gemNew daiNew

theorem accountMapEquiv_frobSourceFinalState
    {cA gh bl σ σ₀ A I} {g : UInt256}
    (hsz196 : 196 ≤ I.calldata.size)
    (urnInkNew urnArtNew ilkArtNew gemNew daiNew : UInt256)
    (hInk : urnInkNew = frobUrnInkNew σ I)
    (hArt : urnArtNew = frobUrnArtNew σ I)
    (hIlk : ilkArtNew = frobIlkArtNew σ I)
    (hGem : gemNew = frobGemNew σ I)
    (hDai : daiNew = frobDaiNew σ I) :
    accountMapEquiv (frobAfterRuntimeFinal σ I)
      (frobSourceFinalState cA gh bl σ σ₀ A I g
        urnInkNew urnArtNew ilkArtNew gemNew daiNew).accountMap := by
  unfold frobSourceFinalState
  exact accountMapEquiv_frobSourceFinal
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g)
    hsz196 urnInkNew urnArtNew ilkArtNew gemNew daiNew
    hInk hArt hIlk hGem hDai

theorem frobSourceLoad_urnInk {cA gh bl σ σ₀ A I} {g : UInt256}
    (hsz196 : 196 ≤ I.calldata.size) :
    Solm.EVM.storageLoad (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
        (frobUrnInkSourceSlot I) =
      vatSlotWord (frobUrnInkSlot I) σ I := by
  simp [initState, Solm.EVM.storageLoad, vatSlotWord, solcSlotWord,
    State.lookupAccount, Account.lookupStorage, frobUrnInkSourceSlot_eq I hsz196]

theorem frobSourceLoad_urnArt {cA gh bl σ σ₀ A I} {g : UInt256}
    (hsz196 : 196 ≤ I.calldata.size) :
    Solm.EVM.storageLoad (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
        (frobUrnArtSourceSlot I) =
      vatSlotWord (frobUrnArtSlot I) σ I := by
  simp [initState, Solm.EVM.storageLoad, vatSlotWord, solcSlotWord,
    State.lookupAccount, Account.lookupStorage, frobUrnArtSourceSlot_eq I hsz196]

theorem frobSourceLoad_ilkArt {cA gh bl σ σ₀ A I} {g : UInt256}
    (hsz196 : 196 ≤ I.calldata.size) :
    Solm.EVM.storageLoad (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
        (frobIlkArtSourceSlot I) =
      vatSlotWord (frobIlkArtSlot I) σ I := by
  simp [initState, Solm.EVM.storageLoad, vatSlotWord, solcSlotWord,
    State.lookupAccount, Account.lookupStorage, frobIlkArtSourceSlot_eq I hsz196]

theorem frobSourceLoad_gemV {cA gh bl σ σ₀ A I} {g : UInt256}
    (hsz196 : 196 ≤ I.calldata.size) :
    Solm.EVM.storageLoad (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
        (frobGemVSourceSlot I) =
      vatSlotWord (frobGemVSlot I) σ I := by
  simp [initState, Solm.EVM.storageLoad, vatSlotWord, solcSlotWord,
    State.lookupAccount, Account.lookupStorage, frobGemVSourceSlot_eq I hsz196]

theorem frobSourceLoad_daiW {cA gh bl σ σ₀ A I} {g : UInt256} :
    Solm.EVM.storageLoad (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
        (frobDaiWSourceSlot I) =
      vatSlotWord (frobDaiWSlot I) σ I := by
  simp [initState, Solm.EVM.storageLoad, vatSlotWord, solcSlotWord,
    State.lookupAccount, Account.lookupStorage, frobDaiWSourceSlot_eq I]

theorem frobSourceLoad_ilkRate {cA gh bl σ σ₀ A I} {g : UInt256}
    (hsz196 : 196 ≤ I.calldata.size) :
    Solm.EVM.storageLoad (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
        (frobIlkRateSourceSlot I) =
      vatSlotWord (frobIlkRateSlot I) σ I := by
  simp [initState, Solm.EVM.storageLoad, vatSlotWord, solcSlotWord,
    State.lookupAccount, Account.lookupStorage, frobIlkRateSourceSlot_eq I hsz196]

theorem frobSourceLoad_ilkSpot {cA gh bl σ σ₀ A I} {g : UInt256}
    (hsz196 : 196 ≤ I.calldata.size) :
    Solm.EVM.storageLoad (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
        (frobIlkSpotSourceSlot I) =
      vatSlotWord (frobIlkSpotSlot I) σ I := by
  simp [initState, Solm.EVM.storageLoad, vatSlotWord, solcSlotWord,
    State.lookupAccount, Account.lookupStorage, frobIlkSpotSourceSlot_eq I hsz196]

theorem frobSourceLoad_ilkLine {cA gh bl σ σ₀ A I} {g : UInt256}
    (hsz196 : 196 ≤ I.calldata.size) :
    Solm.EVM.storageLoad (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
        (frobIlkLineSourceSlot I) =
      vatSlotWord (frobIlkLineSlot I) σ I := by
  simp [initState, Solm.EVM.storageLoad, vatSlotWord, solcSlotWord,
    State.lookupAccount, Account.lookupStorage, frobIlkLineSourceSlot_eq I hsz196]

theorem frobSourceLoad_ilkDust {cA gh bl σ σ₀ A I} {g : UInt256}
    (hsz196 : 196 ≤ I.calldata.size) :
    Solm.EVM.storageLoad (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
        (frobIlkDustSourceSlot I) =
      vatSlotWord (frobIlkDustSlot I) σ I := by
  simp [initState, Solm.EVM.storageLoad, vatSlotWord, solcSlotWord,
    State.lookupAccount, Account.lookupStorage, frobIlkDustSourceSlot_eq I hsz196]

def writeWordMem (off : Nat) (word : UInt256) (mem : ByteArray) :
    ByteArray :=
  (UInt256.toByteArray word).write 0 mem off 32

def frobAlloc2Mem (mem : ByteArray) : ByteArray :=
  writeWordMem 160 ⟨0⟩ (writeWordMem 128 ⟨0⟩ (writeWordMem 64 ⟨192⟩ mem))

def frobAlloc5Mem (mem : ByteArray) : ByteArray :=
  writeWordMem 384 ⟨0⟩
    (writeWordMem 352 ⟨0⟩
      (writeWordMem 320 ⟨0⟩
        (writeWordMem 288 ⟨0⟩
          (writeWordMem 256 ⟨0⟩ (writeWordMem 64 ⟨416⟩ mem)))))

noncomputable def frobUrnHashMem (I : ExecutionEnv) : ByteArray :=
  twoWordHashMem (frobIWord I) ⟨3⟩ (frobAlloc2Mem solcFreePtrMem)

noncomputable def frobUrnBaseMem (I : ExecutionEnv) : ByteArray :=
  twoWordHashMem (frobUMaskedWord I) (solcMappingSlot ⟨3⟩ (frobIWord I))
    (frobUrnHashMem I)

noncomputable def frobUrnLoadedMem (σ : AccountMap) (I : ExecutionEnv) : ByteArray :=
  writeWordMem 224 (solcSlotWord σ I (frobUrnArtSlot I))
    (writeWordMem 192 (solcSlotWord σ I (frobUrnInkSlot I))
      (writeWordMem 64 ⟨256⟩ (frobUrnBaseMem I)))

noncomputable def frobIlkHashMem (σ : AccountMap) (I : ExecutionEnv) : ByteArray :=
  twoWordHashMem (frobIWord I) ⟨2⟩ (frobAlloc5Mem (frobUrnLoadedMem σ I))

noncomputable def frobIlkLoadedMem (σ : AccountMap) (I : ExecutionEnv) : ByteArray :=
  writeWordMem 544 (solcSlotWord σ I (frobIlkDustSlot I))
    (writeWordMem 512 (solcSlotWord σ I (frobIlkLineSlot I))
      (writeWordMem 480 (solcSlotWord σ I (frobIlkSpotSlot I))
        (writeWordMem 448 (solcSlotWord σ I (frobIlkRateSlot I))
          (writeWordMem 416 (solcSlotWord σ I (frobIlkArtSlot I))
            (writeWordMem 64 ⟨576⟩ (frobIlkHashMem σ I))))))

noncomputable def frobUrnInkUpdatedMem (σ : AccountMap) (I : ExecutionEnv) (urnInkNew : UInt256) :
    ByteArray :=
  writeWordMem 192 urnInkNew (frobIlkLoadedMem σ I)

noncomputable def frobUrnArtUpdatedMem (σ : AccountMap) (I : ExecutionEnv)
    (urnInkNew urnArtNew : UInt256) : ByteArray :=
  writeWordMem 224 urnArtNew (frobUrnInkUpdatedMem σ I urnInkNew)

noncomputable def frobIlkArtUpdatedMem (σ : AccountMap) (I : ExecutionEnv)
    (urnInkNew urnArtNew ilkArtNew : UInt256) : ByteArray :=
  writeWordMem 416 ilkArtNew (frobUrnArtUpdatedMem σ I urnInkNew urnArtNew)

theorem writeWordMem_size_of_contains {mem : ByteArray} {off : Nat} {word : UInt256}
    (hcontains : off + 32 ≤ mem.size) :
    (writeWordMem off word mem).size = mem.size := by
  unfold writeWordMem
  rw [write32_eq _ _ _ (by rw [toByteArray_size]) (by omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract, toByteArray_size]
  omega

theorem writeWordMem_size_at_end {mem : ByteArray} {off : Nat} {word : UInt256}
    (hend : mem.size = off) :
    (writeWordMem off word mem).size = off + 32 := by
  unfold writeWordMem
  have hgap : off - mem.size < USize.size := by
    rw [hend, Nat.sub_self]
    native_decide
  rw [toByteArray_write_eq _ _ _ (by omega) hgap,
    ByteArray.size_append, ByteArray.size_append, ByteArray_zeroes_size,
    toByteArray_size]
  have hzero : (USize.ofNat (off - mem.size)).toNat = 0 := by
    rw [hend, Nat.sub_self]
    native_decide
  rw [hzero]
  omega

theorem writeWordMem_read64_below {mem : ByteArray} {off : Nat} {word : UInt256}
    (hcontains : 64 + 32 ≤ mem.size) (hsep : 64 + 32 ≤ off)
    (hgap : off - mem.size < USize.size) :
    (writeWordMem off word mem).readWithPadding 64 32 =
      mem.readWithPadding 64 32 := by
  unfold writeWordMem
  exact toByteArray_write_read_below_of_gap word mem off 64 hcontains hsep hgap

theorem writeWordMem_read32_below {mem : ByteArray} {off readOff : Nat} {word : UInt256}
    (hcontains : readOff + 32 ≤ mem.size) (hsep : readOff + 32 ≤ off)
    (hgap : off - mem.size < USize.size) :
    (writeWordMem off word mem).readWithPadding readOff 32 =
      mem.readWithPadding readOff 32 := by
  unfold writeWordMem
  exact toByteArray_write_read_below_of_gap word mem off readOff hcontains hsep hgap

theorem writeWordMem_read32_above {mem : ByteArray} {off readOff : Nat} {word : UInt256}
    (hlo : off ≤ mem.size) (habove : off + 32 ≤ readOff)
    (hin : readOff + 32 ≤ mem.size) :
    (writeWordMem off word mem).readWithPadding readOff 32 =
      mem.readWithPadding readOff 32 := by
  unfold writeWordMem
  exact write32_read_above _ _ off readOff (by rw [toByteArray_size]) hlo habove hin

theorem frobAlloc2Mem_solc_size :
    (frobAlloc2Mem solcFreePtrMem).size = 192 := by
  native_decide

theorem frobAlloc2Mem_solc_read64 :
    (frobAlloc2Mem solcFreePtrMem).readWithPadding 64 32 =
      UInt256.toByteArray ⟨192⟩ := by
  native_decide

theorem wordAt0Mem_size_of_ge32 {mem : ByteArray} (word : UInt256)
    (hmem : 32 ≤ mem.size) :
    (wordAt0Mem word mem).size = mem.size := by
  unfold wordAt0Mem
  rw [write32_eq _ _ _ (by rw [toByteArray_size]) (by omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract, toByteArray_size]
  omega

theorem wordAt32Mem_size_of_ge64 {mem : ByteArray} (word : UInt256)
    (hmem : 64 ≤ mem.size) :
    (wordAt32Mem word mem).size = mem.size := by
  unfold wordAt32Mem
  rw [write32_eq _ _ _ (by rw [toByteArray_size]) (by omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract, toByteArray_size]
  omega

theorem twoWordHashMem_size_of_ge64 {mem : ByteArray} (key slot : UInt256)
    (hmem : 64 ≤ mem.size) :
    (twoWordHashMem key slot mem).size = mem.size := by
  unfold twoWordHashMem
  rw [wordAt32Mem_size_of_ge64 slot (by
    rw [wordAt0Mem_size_of_ge32 key (by omega)]
    omega)]
  exact wordAt0Mem_size_of_ge32 key (by omega)

theorem twoWordHashMem_read0_of_ge64 {mem : ByteArray} (key slot : UInt256)
    (hmem : 64 ≤ mem.size) :
    (twoWordHashMem key slot mem).readWithPadding 0 32 =
      UInt256.toByteArray key := by
  unfold twoWordHashMem wordAt32Mem
  rw [write32_read_below _ _ 32 0 (by rw [toByteArray_size])
      (by rw [wordAt0Mem_size_of_ge32 key (by omega)]; omega) (by omega)]
  unfold wordAt0Mem
  rw [write32_read_back _ _ _ (by rw [toByteArray_size]) (by omega)]
  rw [toByteArray_extract_all]

theorem twoWordHashMem_read32_of_ge64 {mem : ByteArray} (key slot : UInt256)
    (hmem : 64 ≤ mem.size) :
    (twoWordHashMem key slot mem).readWithPadding 32 32 =
      UInt256.toByteArray slot := by
  unfold twoWordHashMem wordAt32Mem
  rw [write32_read_back _ _ _ (by rw [toByteArray_size])
      (by rw [wordAt0Mem_size_of_ge32 key (by omega)]; omega)]
  rw [toByteArray_extract_all]

theorem twoWordHashMem_read0_64_of_ge64 {mem : ByteArray} (key slot : UInt256)
    (hmem : 64 ≤ mem.size) :
    (twoWordHashMem key slot mem).readWithPadding 0 64 =
      UInt256.toByteArray key ++ UInt256.toByteArray slot := by
  rw [readWithPadding_eq_extract' _ 0 64 (by norm_num) (by norm_num)
      (by rw [twoWordHashMem_size_of_ge64 key slot hmem]; omega)]
  have hleft :
      (twoWordHashMem key slot mem).extract 0 32 = UInt256.toByteArray key := by
    rw [← readWithPadding_eq_extract _ 0
        (by rw [twoWordHashMem_size_of_ge64 key slot hmem]; omega),
      twoWordHashMem_read0_of_ge64 key slot hmem]
  have hright :
      (twoWordHashMem key slot mem).extract 32 64 = UInt256.toByteArray slot := by
    rw [← readWithPadding_eq_extract _ 32
        (by rw [twoWordHashMem_size_of_ge64 key slot hmem]; omega),
      twoWordHashMem_read32_of_ge64 key slot hmem]
  rw [show (twoWordHashMem key slot mem).extract 0 64 =
      (twoWordHashMem key slot mem).extract 0 32 ++
        (twoWordHashMem key slot mem).extract 32 64 by
      rw [ByteArray.extract_append_extract]
      norm_num]
  rw [hleft, hright]

theorem twoWordHashMem_solcMappingSlot_of_ge64 (baseSlot key : UInt256)
    {mem : ByteArray} (hmem : 64 ≤ mem.size) :
    UInt256.ofNat
        (fromByteArrayBigEndian (ffi.KEC ((twoWordHashMem key baseSlot mem).readWithPadding 0 64))) =
      solcMappingSlot baseSlot key := by
  rw [twoWordHashMem_read0_64_of_ge64 key baseSlot hmem]
  unfold solcMappingSlot
  exact mappingSlot_single key baseSlot

theorem twoWordHashMem_read64_of_ge96 {mem : ByteArray} (key slot : UInt256)
    (hmem : 96 ≤ mem.size) :
    (twoWordHashMem key slot mem).readWithPadding 64 32 =
      mem.readWithPadding 64 32 := by
  unfold twoWordHashMem wordAt32Mem
  rw [write32_read_above _ _ 32 64 (by rw [toByteArray_size])
      (by rw [wordAt0Mem_size_of_ge32 key (by omega)]; omega) (by omega)
      (by rw [wordAt0Mem_size_of_ge32 key (by omega)]; omega)]
  unfold wordAt0Mem
  rw [write32_read_above _ _ 0 64 (by rw [toByteArray_size])
      (by omega) (by omega) (by omega)]

theorem twoWordHashMem_read64_of_size576 {mem : ByteArray} (key slot : UInt256)
    (hmem : mem.size = 576)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨576⟩) :
    (twoWordHashMem key slot mem).readWithPadding 64 32 =
      UInt256.toByteArray ⟨576⟩ := by
  rw [twoWordHashMem_read64_of_ge96]
  · exact hread64
  · rw [hmem]
    omega

theorem twoWordHashMem_read32_above64 {mem : ByteArray} (key slot : UInt256)
    {readOff : Nat} (habove : 64 ≤ readOff) (hin : readOff + 32 ≤ mem.size) :
    (twoWordHashMem key slot mem).readWithPadding readOff 32 =
      mem.readWithPadding readOff 32 := by
  have hmem32 : 32 ≤ mem.size := by omega
  unfold twoWordHashMem wordAt32Mem
  rw [write32_read_above _ _ 32 readOff (by rw [toByteArray_size])
      (by rw [wordAt0Mem_size_of_ge32 key hmem32]; omega)
      (by omega)
      (by rw [wordAt0Mem_size_of_ge32 key hmem32]; omega)]
  unfold wordAt0Mem
  rw [write32_read_above _ _ 0 readOff (by rw [toByteArray_size])
      (by omega) (by omega) (by omega)]

theorem twoWordHashMem_size_576 {mem : ByteArray} (key slot : UInt256)
    (hmem : mem.size = 576) :
    (twoWordHashMem key slot mem).size = 576 := by
  rw [twoWordHashMem_size_of_ge64]
  · exact hmem
  · rw [hmem]
    omega

theorem twoWordHashMem_twoWordHashMem_ge64 {mem : ByteArray}
    (key₁ slot₁ key₂ slot₂ : UInt256) (hmem : 64 ≤ mem.size) :
    64 ≤ (twoWordHashMem key₁ slot₁ (twoWordHashMem key₂ slot₂ mem)).size := by
  have hinner : 64 ≤ (twoWordHashMem key₂ slot₂ mem).size := by
    rw [twoWordHashMem_size_of_ge64 key₂ slot₂ hmem]
    exact hmem
  rw [twoWordHashMem_size_of_ge64 key₁ slot₁ hinner]
  exact hinner

theorem twoWordHashMem_read32_above64_of_size576 {mem : ByteArray}
    (key slot : UInt256) {readOff : Nat} {word : UInt256}
    (habove : 64 ≤ readOff) (hin : readOff + 32 ≤ 576) (hmem : mem.size = 576)
    (hread : mem.readWithPadding readOff 32 = UInt256.toByteArray word) :
    (twoWordHashMem key slot mem).readWithPadding readOff 32 =
      UInt256.toByteArray word := by
  rw [twoWordHashMem_read32_above64 key slot habove]
  · exact hread
  · rw [hmem]
    exact hin

theorem frobUrnHashMem_size (I : ExecutionEnv) :
    (frobUrnHashMem I).size = 192 := by
  unfold frobUrnHashMem
  rw [twoWordHashMem_size_of_ge64]
  · exact frobAlloc2Mem_solc_size
  · rw [frobAlloc2Mem_solc_size]
    omega

theorem frobUrnBaseMem_size (I : ExecutionEnv) :
    (frobUrnBaseMem I).size = 192 := by
  unfold frobUrnBaseMem
  rw [twoWordHashMem_size_of_ge64]
  · exact frobUrnHashMem_size I
  · rw [frobUrnHashMem_size I]
    omega

theorem frobUrnBaseMem_read64 (I : ExecutionEnv) :
    (frobUrnBaseMem I).readWithPadding 64 32 =
      UInt256.toByteArray ⟨192⟩ := by
  unfold frobUrnBaseMem frobUrnHashMem
  rw [twoWordHashMem_read64_of_ge96]
  · rw [twoWordHashMem_read64_of_ge96]
    · exact frobAlloc2Mem_solc_read64
    · rw [frobAlloc2Mem_solc_size]
      omega
  · simpa [frobUrnHashMem] using (by rw [frobUrnHashMem_size I]; omega :
      96 ≤ (frobUrnHashMem I).size)

theorem frobUrnLoadedMem_size (σ : AccountMap) (I : ExecutionEnv) :
    (frobUrnLoadedMem σ I).size = 256 := by
  let memFree := writeWordMem 64 ⟨256⟩ (frobUrnBaseMem I)
  let memInk := writeWordMem 192 (solcSlotWord σ I (frobUrnInkSlot I)) memFree
  have hfree : memFree.size = 192 := by
    unfold memFree
    rw [writeWordMem_size_of_contains (word := (⟨256⟩ : UInt256))]
    · exact frobUrnBaseMem_size I
    · rw [frobUrnBaseMem_size I]
      omega
  have hink : memInk.size = 224 := by
    unfold memInk
    exact writeWordMem_size_at_end hfree
  have hart :
      (writeWordMem 224 (solcSlotWord σ I (frobUrnArtSlot I))
        (writeWordMem 192 (solcSlotWord σ I (frobUrnInkSlot I))
          (writeWordMem 64 ⟨256⟩ (frobUrnBaseMem I)))).size = 256 :=
    writeWordMem_size_at_end hink
  simpa [frobUrnLoadedMem] using hart

theorem frobUrnLoadedMem_read64 (σ : AccountMap) (I : ExecutionEnv) :
    (frobUrnLoadedMem σ I).readWithPadding 64 32 =
      UInt256.toByteArray ⟨256⟩ := by
  unfold frobUrnLoadedMem writeWordMem
  have hfree : (writeWordMem 64 ⟨256⟩ (frobUrnBaseMem I)).size = 192 := by
    rw [writeWordMem_size_of_contains (word := (⟨256⟩ : UInt256))]
    · exact frobUrnBaseMem_size I
    · rw [frobUrnBaseMem_size I]; omega
  have hink :
      (writeWordMem 192 (solcSlotWord σ I (frobUrnInkSlot I))
        (writeWordMem 64 ⟨256⟩ (frobUrnBaseMem I))).size = 224 := by
    exact writeWordMem_size_at_end hfree
  rw [toByteArray_write_read_below_of_gap (solcSlotWord σ I (frobUrnArtSlot I)) _ 224 64
    (by simpa [writeWordMem] using (by rw [hink]; omega :
      64 + 32 ≤ (writeWordMem 192 (solcSlotWord σ I (frobUrnInkSlot I))
        (writeWordMem 64 ⟨256⟩ (frobUrnBaseMem I))).size))
    (by omega) (by simpa [writeWordMem] using (by rw [hink]; native_decide :
      224 - (writeWordMem 192 (solcSlotWord σ I (frobUrnInkSlot I))
        (writeWordMem 64 ⟨256⟩ (frobUrnBaseMem I))).size < USize.size))]
  rw [toByteArray_write_read_below_of_gap (solcSlotWord σ I (frobUrnInkSlot I)) _ 192 64
    (by simpa [writeWordMem] using (by rw [hfree]; omega :
      64 + 32 ≤ (writeWordMem 64 ⟨256⟩ (frobUrnBaseMem I)).size))
    (by omega) (by simpa [writeWordMem] using (by rw [hfree]; native_decide :
      192 - (writeWordMem 64 ⟨256⟩ (frobUrnBaseMem I)).size < USize.size))]
  exact toByteArray_write32_read_back (frobUrnBaseMem I) (⟨256⟩ : UInt256) 64
    (by rw [frobUrnBaseMem_size I]; omega)

theorem frobUrnLoadedMem_read192 (σ : AccountMap) (I : ExecutionEnv) :
    (frobUrnLoadedMem σ I).readWithPadding 192 32 =
      UInt256.toByteArray (solcSlotWord σ I (frobUrnInkSlot I)) := by
  let memFree := writeWordMem 64 ⟨256⟩ (frobUrnBaseMem I)
  let memInk := writeWordMem 192 (solcSlotWord σ I (frobUrnInkSlot I)) memFree
  have hfreeSize : memFree.size = 192 := by
    unfold memFree
    rw [writeWordMem_size_of_contains (word := (⟨256⟩ : UInt256))]
    · exact frobUrnBaseMem_size I
    · rw [frobUrnBaseMem_size I]; omega
  have hinkSize : memInk.size = 224 := by
    unfold memInk
    exact writeWordMem_size_at_end hfreeSize
  have hinkRead :
      memInk.readWithPadding 192 32 =
        UInt256.toByteArray (solcSlotWord σ I (frobUrnInkSlot I)) := by
    unfold memInk
    exact toByteArray_write_read_back_of_gap
      (solcSlotWord σ I (frobUrnInkSlot I)) memFree 192
      (by rw [hfreeSize]; native_decide)
  change (writeWordMem 224 (solcSlotWord σ I (frobUrnArtSlot I)) memInk).readWithPadding
    192 32 = UInt256.toByteArray (solcSlotWord σ I (frobUrnInkSlot I))
  rw [writeWordMem_read32_below (mem := memInk) (off := 224) (readOff := 192)
    (word := solcSlotWord σ I (frobUrnArtSlot I))
    (by rw [hinkSize]) (by omega)
    (by
      rw [hinkSize]
      change 0 < USize.size
      native_decide)]
  exact hinkRead

theorem frobUrnLoadedMem_read224 (σ : AccountMap) (I : ExecutionEnv) :
    (frobUrnLoadedMem σ I).readWithPadding 224 32 =
      UInt256.toByteArray (solcSlotWord σ I (frobUrnArtSlot I)) := by
  let memFree := writeWordMem 64 ⟨256⟩ (frobUrnBaseMem I)
  let memInk := writeWordMem 192 (solcSlotWord σ I (frobUrnInkSlot I)) memFree
  have hfreeSize : memFree.size = 192 := by
    unfold memFree
    rw [writeWordMem_size_of_contains (word := (⟨256⟩ : UInt256))]
    · exact frobUrnBaseMem_size I
    · rw [frobUrnBaseMem_size I]; omega
  have hinkSize : memInk.size = 224 := by
    unfold memInk
    exact writeWordMem_size_at_end hfreeSize
  change (writeWordMem 224 (solcSlotWord σ I (frobUrnArtSlot I)) memInk).readWithPadding
    224 32 = UInt256.toByteArray (solcSlotWord σ I (frobUrnArtSlot I))
  exact toByteArray_write_read_back_of_gap
    (solcSlotWord σ I (frobUrnArtSlot I)) memInk 224
    (by
      rw [hinkSize]
      change 0 < USize.size
      native_decide)

theorem frobAlloc5Mem_frobUrnLoaded_size (σ : AccountMap) (I : ExecutionEnv) :
    (frobAlloc5Mem (frobUrnLoadedMem σ I)).size = 416 := by
  let memFree := writeWordMem 64 ⟨416⟩ (frobUrnLoadedMem σ I)
  let mem0 := writeWordMem 256 ⟨0⟩ memFree
  let mem1 := writeWordMem 288 ⟨0⟩ mem0
  let mem2 := writeWordMem 320 ⟨0⟩ mem1
  let mem3 := writeWordMem 352 ⟨0⟩ mem2
  have hfree : memFree.size = 256 := by
    unfold memFree
    rw [writeWordMem_size_of_contains (word := (⟨416⟩ : UInt256))]
    · exact frobUrnLoadedMem_size σ I
    · rw [frobUrnLoadedMem_size σ I]
      omega
  have h0 : mem0.size = 288 := by
    unfold mem0
    exact writeWordMem_size_at_end hfree
  have h1 : mem1.size = 320 := by
    unfold mem1
    exact writeWordMem_size_at_end h0
  have h2 : mem2.size = 352 := by
    unfold mem2
    exact writeWordMem_size_at_end h1
  have h3 : mem3.size = 384 := by
    unfold mem3
    exact writeWordMem_size_at_end h2
  change (writeWordMem 384 (⟨0⟩ : UInt256) mem3).size = 416
  exact writeWordMem_size_at_end h3

theorem frobAlloc5Mem_frobUrnLoaded_read64 (σ : AccountMap) (I : ExecutionEnv) :
    (frobAlloc5Mem (frobUrnLoadedMem σ I)).readWithPadding 64 32 =
      UInt256.toByteArray ⟨416⟩ := by
  let memFree := writeWordMem 64 ⟨416⟩ (frobUrnLoadedMem σ I)
  let mem0 := writeWordMem 256 ⟨0⟩ memFree
  let mem1 := writeWordMem 288 ⟨0⟩ mem0
  let mem2 := writeWordMem 320 ⟨0⟩ mem1
  let mem3 := writeWordMem 352 ⟨0⟩ mem2
  have hfreeSize : memFree.size = 256 := by
    unfold memFree
    rw [writeWordMem_size_of_contains (word := (⟨416⟩ : UInt256))]
    · exact frobUrnLoadedMem_size σ I
    · rw [frobUrnLoadedMem_size σ I]
      omega
  have h0Size : mem0.size = 288 := by
    unfold mem0
    exact writeWordMem_size_at_end hfreeSize
  have h1Size : mem1.size = 320 := by
    unfold mem1
    exact writeWordMem_size_at_end h0Size
  have h2Size : mem2.size = 352 := by
    unfold mem2
    exact writeWordMem_size_at_end h1Size
  have h3Size : mem3.size = 384 := by
    unfold mem3
    exact writeWordMem_size_at_end h2Size
  have hfreeRead : memFree.readWithPadding 64 32 = UInt256.toByteArray ⟨416⟩ := by
    unfold memFree
    exact toByteArray_write32_read_back (frobUrnLoadedMem σ I) (⟨416⟩ : UInt256) 64
      (by rw [frobUrnLoadedMem_size σ I]; omega)
  have h0Read : mem0.readWithPadding 64 32 = UInt256.toByteArray ⟨416⟩ := by
    unfold mem0
    rw [writeWordMem_read64_below]
    · exact hfreeRead
    · rw [hfreeSize]; omega
    · omega
    · rw [hfreeSize]; native_decide
  have h1Read : mem1.readWithPadding 64 32 = UInt256.toByteArray ⟨416⟩ := by
    unfold mem1
    rw [writeWordMem_read64_below]
    · exact h0Read
    · rw [h0Size]; omega
    · omega
    · rw [h0Size]; native_decide
  have h2Read : mem2.readWithPadding 64 32 = UInt256.toByteArray ⟨416⟩ := by
    unfold mem2
    rw [writeWordMem_read64_below]
    · exact h1Read
    · rw [h1Size]; omega
    · omega
    · rw [h1Size]; native_decide
  have h3Read : mem3.readWithPadding 64 32 = UInt256.toByteArray ⟨416⟩ := by
    unfold mem3
    rw [writeWordMem_read64_below]
    · exact h2Read
    · rw [h2Size]; omega
    · omega
    · rw [h2Size]; native_decide
  change (writeWordMem 384 (⟨0⟩ : UInt256) mem3).readWithPadding 64 32 =
    UInt256.toByteArray ⟨416⟩
  rw [writeWordMem_read64_below]
  · exact h3Read
  · rw [h3Size]; omega
  · omega
  · rw [h3Size]; native_decide

theorem frobAlloc5Mem_frobUrnLoaded_read192 (σ : AccountMap) (I : ExecutionEnv) :
    (frobAlloc5Mem (frobUrnLoadedMem σ I)).readWithPadding 192 32 =
      UInt256.toByteArray (solcSlotWord σ I (frobUrnInkSlot I)) := by
  let memFree := writeWordMem 64 ⟨416⟩ (frobUrnLoadedMem σ I)
  let mem0 := writeWordMem 256 ⟨0⟩ memFree
  let mem1 := writeWordMem 288 ⟨0⟩ mem0
  let mem2 := writeWordMem 320 ⟨0⟩ mem1
  let mem3 := writeWordMem 352 ⟨0⟩ mem2
  have hfreeSize : memFree.size = 256 := by
    unfold memFree
    rw [writeWordMem_size_of_contains (word := (⟨416⟩ : UInt256))]
    · exact frobUrnLoadedMem_size σ I
    · rw [frobUrnLoadedMem_size σ I]; omega
  have hfreeRead :
      memFree.readWithPadding 192 32 =
        UInt256.toByteArray (solcSlotWord σ I (frobUrnInkSlot I)) := by
    unfold memFree
    rw [writeWordMem_read32_above]
    · exact frobUrnLoadedMem_read192 σ I
    · rw [frobUrnLoadedMem_size σ I]; omega
    · omega
    · rw [frobUrnLoadedMem_size σ I]; omega
  have h0Size : mem0.size = 288 := by
    unfold mem0
    exact writeWordMem_size_at_end hfreeSize
  have h0Read :
      mem0.readWithPadding 192 32 =
        UInt256.toByteArray (solcSlotWord σ I (frobUrnInkSlot I)) := by
    unfold mem0
    rw [writeWordMem_read32_below]
    · exact hfreeRead
    · rw [hfreeSize]; omega
    · omega
    · rw [hfreeSize]; native_decide
  have h1Size : mem1.size = 320 := by
    unfold mem1
    exact writeWordMem_size_at_end h0Size
  have h1Read :
      mem1.readWithPadding 192 32 =
        UInt256.toByteArray (solcSlotWord σ I (frobUrnInkSlot I)) := by
    unfold mem1
    rw [writeWordMem_read32_below]
    · exact h0Read
    · rw [h0Size]; omega
    · omega
    · rw [h0Size]; native_decide
  have h2Size : mem2.size = 352 := by
    unfold mem2
    exact writeWordMem_size_at_end h1Size
  have h2Read :
      mem2.readWithPadding 192 32 =
        UInt256.toByteArray (solcSlotWord σ I (frobUrnInkSlot I)) := by
    unfold mem2
    rw [writeWordMem_read32_below]
    · exact h1Read
    · rw [h1Size]; omega
    · omega
    · rw [h1Size]; native_decide
  have h3Size : mem3.size = 384 := by
    unfold mem3
    exact writeWordMem_size_at_end h2Size
  have h3Read :
      mem3.readWithPadding 192 32 =
        UInt256.toByteArray (solcSlotWord σ I (frobUrnInkSlot I)) := by
    unfold mem3
    rw [writeWordMem_read32_below]
    · exact h2Read
    · rw [h2Size]; omega
    · omega
    · rw [h2Size]; native_decide
  change (writeWordMem 384 (⟨0⟩ : UInt256) mem3).readWithPadding 192 32 =
    UInt256.toByteArray (solcSlotWord σ I (frobUrnInkSlot I))
  rw [writeWordMem_read32_below]
  · exact h3Read
  · rw [h3Size]; omega
  · omega
  · rw [h3Size]; native_decide

theorem frobAlloc5Mem_frobUrnLoaded_read224 (σ : AccountMap) (I : ExecutionEnv) :
    (frobAlloc5Mem (frobUrnLoadedMem σ I)).readWithPadding 224 32 =
      UInt256.toByteArray (solcSlotWord σ I (frobUrnArtSlot I)) := by
  let memFree := writeWordMem 64 ⟨416⟩ (frobUrnLoadedMem σ I)
  let mem0 := writeWordMem 256 ⟨0⟩ memFree
  let mem1 := writeWordMem 288 ⟨0⟩ mem0
  let mem2 := writeWordMem 320 ⟨0⟩ mem1
  let mem3 := writeWordMem 352 ⟨0⟩ mem2
  have hfreeSize : memFree.size = 256 := by
    unfold memFree
    rw [writeWordMem_size_of_contains (word := (⟨416⟩ : UInt256))]
    · exact frobUrnLoadedMem_size σ I
    · rw [frobUrnLoadedMem_size σ I]; omega
  have hfreeRead :
      memFree.readWithPadding 224 32 =
        UInt256.toByteArray (solcSlotWord σ I (frobUrnArtSlot I)) := by
    unfold memFree
    rw [writeWordMem_read32_above (mem := frobUrnLoadedMem σ I) (off := 64)
      (readOff := 224) (word := (⟨416⟩ : UInt256))
      (by rw [frobUrnLoadedMem_size σ I]; omega) (by omega)
      (by rw [frobUrnLoadedMem_size σ I])]
    exact frobUrnLoadedMem_read224 σ I
  have h0Size : mem0.size = 288 := by
    unfold mem0
    exact writeWordMem_size_at_end hfreeSize
  have h0Read :
      mem0.readWithPadding 224 32 =
        UInt256.toByteArray (solcSlotWord σ I (frobUrnArtSlot I)) := by
    unfold mem0
    rw [writeWordMem_read32_below (mem := memFree) (off := 256) (readOff := 224)
      (word := (⟨0⟩ : UInt256))
      (by rw [hfreeSize]) (by omega) (by rw [hfreeSize]; native_decide)]
    exact hfreeRead
  have h1Size : mem1.size = 320 := by
    unfold mem1
    exact writeWordMem_size_at_end h0Size
  have h1Read :
      mem1.readWithPadding 224 32 =
        UInt256.toByteArray (solcSlotWord σ I (frobUrnArtSlot I)) := by
    unfold mem1
    rw [writeWordMem_read32_below]
    · exact h0Read
    · rw [h0Size]; omega
    · omega
    · rw [h0Size]; native_decide
  have h2Size : mem2.size = 352 := by
    unfold mem2
    exact writeWordMem_size_at_end h1Size
  have h2Read :
      mem2.readWithPadding 224 32 =
        UInt256.toByteArray (solcSlotWord σ I (frobUrnArtSlot I)) := by
    unfold mem2
    rw [writeWordMem_read32_below]
    · exact h1Read
    · rw [h1Size]; omega
    · omega
    · rw [h1Size]; native_decide
  have h3Size : mem3.size = 384 := by
    unfold mem3
    exact writeWordMem_size_at_end h2Size
  have h3Read :
      mem3.readWithPadding 224 32 =
        UInt256.toByteArray (solcSlotWord σ I (frobUrnArtSlot I)) := by
    unfold mem3
    rw [writeWordMem_read32_below]
    · exact h2Read
    · rw [h2Size]; omega
    · omega
    · rw [h2Size]; native_decide
  change (writeWordMem 384 (⟨0⟩ : UInt256) mem3).readWithPadding 224 32 =
    UInt256.toByteArray (solcSlotWord σ I (frobUrnArtSlot I))
  rw [writeWordMem_read32_below]
  · exact h3Read
  · rw [h3Size]; omega
  · omega
  · rw [h3Size]; native_decide

theorem frobIlkHashMem_size (σ : AccountMap) (I : ExecutionEnv) :
    (frobIlkHashMem σ I).size = 416 := by
  unfold frobIlkHashMem
  rw [twoWordHashMem_size_of_ge64]
  · exact frobAlloc5Mem_frobUrnLoaded_size σ I
  · rw [frobAlloc5Mem_frobUrnLoaded_size σ I]
    omega

theorem frobIlkHashMem_read64 (σ : AccountMap) (I : ExecutionEnv) :
    (frobIlkHashMem σ I).readWithPadding 64 32 =
      UInt256.toByteArray ⟨416⟩ := by
  unfold frobIlkHashMem
  rw [twoWordHashMem_read64_of_ge96]
  · exact frobAlloc5Mem_frobUrnLoaded_read64 σ I
  · rw [frobAlloc5Mem_frobUrnLoaded_size σ I]
    omega

theorem frobIlkHashMem_read192 (σ : AccountMap) (I : ExecutionEnv) :
    (frobIlkHashMem σ I).readWithPadding 192 32 =
      UInt256.toByteArray (solcSlotWord σ I (frobUrnInkSlot I)) := by
  have hallocSize : (frobAlloc5Mem (frobUrnLoadedMem σ I)).size = 416 :=
    frobAlloc5Mem_frobUrnLoaded_size σ I
  have hword0Size :
      (wordAt0Mem (frobIWord I) (frobAlloc5Mem (frobUrnLoadedMem σ I))).size = 416 := by
    rw [wordAt0Mem_size_of_ge32 _ (by rw [hallocSize]; omega), hallocSize]
  unfold frobIlkHashMem twoWordHashMem wordAt32Mem
  rw [write32_read_above _ _ 32 192 (by rw [toByteArray_size])
    (by rw [hword0Size]; omega)
    (by omega)
    (by rw [hword0Size]; omega)]
  unfold wordAt0Mem
  rw [write32_read_above _ _ 0 192 (by rw [toByteArray_size])
    (by rw [hallocSize]; omega) (by omega) (by rw [hallocSize]; omega)]
  exact frobAlloc5Mem_frobUrnLoaded_read192 σ I

theorem frobIlkHashMem_read224 (σ : AccountMap) (I : ExecutionEnv) :
    (frobIlkHashMem σ I).readWithPadding 224 32 =
      UInt256.toByteArray (solcSlotWord σ I (frobUrnArtSlot I)) := by
  have hallocSize : (frobAlloc5Mem (frobUrnLoadedMem σ I)).size = 416 :=
    frobAlloc5Mem_frobUrnLoaded_size σ I
  have hword0Size :
      (wordAt0Mem (frobIWord I) (frobAlloc5Mem (frobUrnLoadedMem σ I))).size = 416 := by
    rw [wordAt0Mem_size_of_ge32 _ (by rw [hallocSize]; omega), hallocSize]
  unfold frobIlkHashMem twoWordHashMem wordAt32Mem
  rw [write32_read_above _ _ 32 224 (by rw [toByteArray_size])
    (by rw [hword0Size]; omega)
    (by omega)
    (by rw [hword0Size]; omega)]
  unfold wordAt0Mem
  rw [write32_read_above _ _ 0 224 (by rw [toByteArray_size])
    (by rw [hallocSize]; omega) (by omega) (by rw [hallocSize]; omega)]
  exact frobAlloc5Mem_frobUrnLoaded_read224 σ I

theorem frobIlkLoadedMem_size (σ : AccountMap) (I : ExecutionEnv) :
    (frobIlkLoadedMem σ I).size = 576 := by
  let memFree := writeWordMem 64 ⟨576⟩ (frobIlkHashMem σ I)
  let memArt := writeWordMem 416 (solcSlotWord σ I (frobIlkArtSlot I)) memFree
  let memRate := writeWordMem 448 (solcSlotWord σ I (frobIlkRateSlot I)) memArt
  let memSpot := writeWordMem 480 (solcSlotWord σ I (frobIlkSpotSlot I)) memRate
  let memLine := writeWordMem 512 (solcSlotWord σ I (frobIlkLineSlot I)) memSpot
  have hfree : memFree.size = 416 := by
    unfold memFree
    rw [writeWordMem_size_of_contains (word := (⟨576⟩ : UInt256))]
    · exact frobIlkHashMem_size σ I
    · rw [frobIlkHashMem_size σ I]
      omega
  have hart : memArt.size = 448 := by
    unfold memArt
    exact writeWordMem_size_at_end hfree
  have hrate : memRate.size = 480 := by
    unfold memRate
    exact writeWordMem_size_at_end hart
  have hspot : memSpot.size = 512 := by
    unfold memSpot
    exact writeWordMem_size_at_end hrate
  have hline : memLine.size = 544 := by
    unfold memLine
    exact writeWordMem_size_at_end hspot
  change (writeWordMem 544 (solcSlotWord σ I (frobIlkDustSlot I)) memLine).size = 576
  exact writeWordMem_size_at_end hline

theorem frobUrnInkUpdatedMem_size (σ : AccountMap) (I : ExecutionEnv)
    (urnInkNew : UInt256) :
    (frobUrnInkUpdatedMem σ I urnInkNew).size = 576 := by
  unfold frobUrnInkUpdatedMem
  rw [writeWordMem_size_of_contains]
  · exact frobIlkLoadedMem_size σ I
  · rw [frobIlkLoadedMem_size σ I]; omega

theorem frobUrnArtUpdatedMem_size (σ : AccountMap) (I : ExecutionEnv)
    (urnInkNew urnArtNew : UInt256) :
    (frobUrnArtUpdatedMem σ I urnInkNew urnArtNew).size = 576 := by
  unfold frobUrnArtUpdatedMem
  rw [writeWordMem_size_of_contains]
  · exact frobUrnInkUpdatedMem_size σ I urnInkNew
  · rw [frobUrnInkUpdatedMem_size σ I urnInkNew]; omega

theorem frobIlkArtUpdatedMem_size (σ : AccountMap) (I : ExecutionEnv)
    (urnInkNew urnArtNew ilkArtNew : UInt256) :
    (frobIlkArtUpdatedMem σ I urnInkNew urnArtNew ilkArtNew).size = 576 := by
  unfold frobIlkArtUpdatedMem
  rw [writeWordMem_size_of_contains]
  · exact frobUrnArtUpdatedMem_size σ I urnInkNew urnArtNew
  · rw [frobUrnArtUpdatedMem_size σ I urnInkNew urnArtNew]; omega

theorem frobIlkArtUpdatedMem_ge64 (σ : AccountMap) (I : ExecutionEnv)
    (urnInkNew urnArtNew ilkArtNew : UInt256) :
    64 ≤ (frobIlkArtUpdatedMem σ I urnInkNew urnArtNew ilkArtNew).size := by
  rw [frobIlkArtUpdatedMem_size σ I urnInkNew urnArtNew ilkArtNew]
  omega

theorem frobIlkLoadedMem_read64 (σ : AccountMap) (I : ExecutionEnv) :
    (frobIlkLoadedMem σ I).readWithPadding 64 32 =
      UInt256.toByteArray ⟨576⟩ := by
  let memFree := writeWordMem 64 ⟨576⟩ (frobIlkHashMem σ I)
  let memArt := writeWordMem 416 (solcSlotWord σ I (frobIlkArtSlot I)) memFree
  let memRate := writeWordMem 448 (solcSlotWord σ I (frobIlkRateSlot I)) memArt
  let memSpot := writeWordMem 480 (solcSlotWord σ I (frobIlkSpotSlot I)) memRate
  let memLine := writeWordMem 512 (solcSlotWord σ I (frobIlkLineSlot I)) memSpot
  have hfreeSize : memFree.size = 416 := by
    unfold memFree
    rw [writeWordMem_size_of_contains (word := (⟨576⟩ : UInt256))]
    · exact frobIlkHashMem_size σ I
    · rw [frobIlkHashMem_size σ I]
      omega
  have hartSize : memArt.size = 448 := by
    unfold memArt
    exact writeWordMem_size_at_end hfreeSize
  have hrateSize : memRate.size = 480 := by
    unfold memRate
    exact writeWordMem_size_at_end hartSize
  have hspotSize : memSpot.size = 512 := by
    unfold memSpot
    exact writeWordMem_size_at_end hrateSize
  have hlineSize : memLine.size = 544 := by
    unfold memLine
    exact writeWordMem_size_at_end hspotSize
  have hfreeRead : memFree.readWithPadding 64 32 = UInt256.toByteArray ⟨576⟩ := by
    unfold memFree
    exact toByteArray_write32_read_back (frobIlkHashMem σ I) (⟨576⟩ : UInt256) 64
      (by rw [frobIlkHashMem_size σ I]; omega)
  have hartRead : memArt.readWithPadding 64 32 = UInt256.toByteArray ⟨576⟩ := by
    unfold memArt
    rw [writeWordMem_read64_below]
    · exact hfreeRead
    · rw [hfreeSize]; omega
    · omega
    · rw [hfreeSize]; native_decide
  have hrateRead : memRate.readWithPadding 64 32 = UInt256.toByteArray ⟨576⟩ := by
    unfold memRate
    rw [writeWordMem_read64_below]
    · exact hartRead
    · rw [hartSize]; omega
    · omega
    · rw [hartSize]; native_decide
  have hspotRead : memSpot.readWithPadding 64 32 = UInt256.toByteArray ⟨576⟩ := by
    unfold memSpot
    rw [writeWordMem_read64_below]
    · exact hrateRead
    · rw [hrateSize]; omega
    · omega
    · rw [hrateSize]; native_decide
  have hlineRead : memLine.readWithPadding 64 32 = UInt256.toByteArray ⟨576⟩ := by
    unfold memLine
    rw [writeWordMem_read64_below]
    · exact hspotRead
    · rw [hspotSize]; omega
    · omega
    · rw [hspotSize]; native_decide
  change (writeWordMem 544 (solcSlotWord σ I (frobIlkDustSlot I)) memLine).readWithPadding 64 32 =
    UInt256.toByteArray ⟨576⟩
  rw [writeWordMem_read64_below]
  · exact hlineRead
  · rw [hlineSize]; omega
  · omega
  · rw [hlineSize]; native_decide

theorem frobIlkArtUpdatedMem_read64 (σ : AccountMap) (I : ExecutionEnv)
    (urnInkNew urnArtNew ilkArtNew : UInt256) :
    (frobIlkArtUpdatedMem σ I urnInkNew urnArtNew ilkArtNew).readWithPadding 64 32 =
      UInt256.toByteArray ⟨576⟩ := by
  unfold frobIlkArtUpdatedMem frobUrnArtUpdatedMem frobUrnInkUpdatedMem
  rw [writeWordMem_read64_below]
  · rw [writeWordMem_read64_below]
    · rw [writeWordMem_read64_below]
      · exact frobIlkLoadedMem_read64 σ I
      · rw [frobIlkLoadedMem_size σ I]; omega
      · omega
      · rw [frobIlkLoadedMem_size σ I]; native_decide
    · rw [writeWordMem_size_of_contains]
      · rw [frobIlkLoadedMem_size σ I]; omega
      · rw [frobIlkLoadedMem_size σ I]; omega
    · omega
    · rw [writeWordMem_size_of_contains]
      · rw [frobIlkLoadedMem_size σ I]; native_decide
      · rw [frobIlkLoadedMem_size σ I]; omega
  · rw [writeWordMem_size_of_contains]
    · rw [writeWordMem_size_of_contains]
      · rw [frobIlkLoadedMem_size σ I]; omega
      · rw [frobIlkLoadedMem_size σ I]; omega
    · rw [writeWordMem_size_of_contains]
      · rw [frobIlkLoadedMem_size σ I]; omega
      · rw [frobIlkLoadedMem_size σ I]; omega
  · omega
  · rw [writeWordMem_size_of_contains]
    · rw [writeWordMem_size_of_contains]
      · rw [frobIlkLoadedMem_size σ I]; native_decide
      · rw [frobIlkLoadedMem_size σ I]; omega
    · rw [writeWordMem_size_of_contains]
      · rw [frobIlkLoadedMem_size σ I]; omega
      · rw [frobIlkLoadedMem_size σ I]; omega

theorem frobIlkLoadedMem_read192 (σ : AccountMap) (I : ExecutionEnv) :
    (frobIlkLoadedMem σ I).readWithPadding 192 32 =
      UInt256.toByteArray (solcSlotWord σ I (frobUrnInkSlot I)) := by
  let memFree := writeWordMem 64 ⟨576⟩ (frobIlkHashMem σ I)
  let memArt := writeWordMem 416 (solcSlotWord σ I (frobIlkArtSlot I)) memFree
  let memRate := writeWordMem 448 (solcSlotWord σ I (frobIlkRateSlot I)) memArt
  let memSpot := writeWordMem 480 (solcSlotWord σ I (frobIlkSpotSlot I)) memRate
  let memLine := writeWordMem 512 (solcSlotWord σ I (frobIlkLineSlot I)) memSpot
  have hfreeSize : memFree.size = 416 := by
    unfold memFree
    rw [writeWordMem_size_of_contains (word := (⟨576⟩ : UInt256))]
    · exact frobIlkHashMem_size σ I
    · rw [frobIlkHashMem_size σ I]; omega
  have hfreeRead :
      memFree.readWithPadding 192 32 =
        UInt256.toByteArray (solcSlotWord σ I (frobUrnInkSlot I)) := by
    unfold memFree
    rw [writeWordMem_read32_above]
    · exact frobIlkHashMem_read192 σ I
    · rw [frobIlkHashMem_size σ I]; omega
    · omega
    · rw [frobIlkHashMem_size σ I]; omega
  have hartSize : memArt.size = 448 := by
    unfold memArt
    exact writeWordMem_size_at_end hfreeSize
  have hartRead :
      memArt.readWithPadding 192 32 =
        UInt256.toByteArray (solcSlotWord σ I (frobUrnInkSlot I)) := by
    unfold memArt
    rw [writeWordMem_read32_below]
    · exact hfreeRead
    · rw [hfreeSize]; omega
    · omega
    · rw [hfreeSize]; native_decide
  have hrateSize : memRate.size = 480 := by
    unfold memRate
    exact writeWordMem_size_at_end hartSize
  have hrateRead :
      memRate.readWithPadding 192 32 =
        UInt256.toByteArray (solcSlotWord σ I (frobUrnInkSlot I)) := by
    unfold memRate
    rw [writeWordMem_read32_below]
    · exact hartRead
    · rw [hartSize]; omega
    · omega
    · rw [hartSize]; native_decide
  have hspotSize : memSpot.size = 512 := by
    unfold memSpot
    exact writeWordMem_size_at_end hrateSize
  have hspotRead :
      memSpot.readWithPadding 192 32 =
        UInt256.toByteArray (solcSlotWord σ I (frobUrnInkSlot I)) := by
    unfold memSpot
    rw [writeWordMem_read32_below]
    · exact hrateRead
    · rw [hrateSize]; omega
    · omega
    · rw [hrateSize]; native_decide
  have hlineSize : memLine.size = 544 := by
    unfold memLine
    exact writeWordMem_size_at_end hspotSize
  have hlineRead :
      memLine.readWithPadding 192 32 =
        UInt256.toByteArray (solcSlotWord σ I (frobUrnInkSlot I)) := by
    unfold memLine
    rw [writeWordMem_read32_below]
    · exact hspotRead
    · rw [hspotSize]; omega
    · omega
    · rw [hspotSize]; native_decide
  change (writeWordMem 544 (solcSlotWord σ I (frobIlkDustSlot I)) memLine).readWithPadding
    192 32 = UInt256.toByteArray (solcSlotWord σ I (frobUrnInkSlot I))
  rw [writeWordMem_read32_below]
  · exact hlineRead
  · rw [hlineSize]; omega
  · omega
  · rw [hlineSize]; native_decide

theorem frobIlkLoadedMem_read224 (σ : AccountMap) (I : ExecutionEnv) :
    (frobIlkLoadedMem σ I).readWithPadding 224 32 =
      UInt256.toByteArray (solcSlotWord σ I (frobUrnArtSlot I)) := by
  let memFree := writeWordMem 64 ⟨576⟩ (frobIlkHashMem σ I)
  let memArt := writeWordMem 416 (solcSlotWord σ I (frobIlkArtSlot I)) memFree
  let memRate := writeWordMem 448 (solcSlotWord σ I (frobIlkRateSlot I)) memArt
  let memSpot := writeWordMem 480 (solcSlotWord σ I (frobIlkSpotSlot I)) memRate
  let memLine := writeWordMem 512 (solcSlotWord σ I (frobIlkLineSlot I)) memSpot
  have hfreeSize : memFree.size = 416 := by
    unfold memFree
    rw [writeWordMem_size_of_contains (word := (⟨576⟩ : UInt256))]
    · exact frobIlkHashMem_size σ I
    · rw [frobIlkHashMem_size σ I]; omega
  have hfreeRead :
      memFree.readWithPadding 224 32 =
        UInt256.toByteArray (solcSlotWord σ I (frobUrnArtSlot I)) := by
    unfold memFree
    rw [writeWordMem_read32_above]
    · exact frobIlkHashMem_read224 σ I
    · rw [frobIlkHashMem_size σ I]; omega
    · omega
    · rw [frobIlkHashMem_size σ I]; omega
  have hartSize : memArt.size = 448 := by
    unfold memArt
    exact writeWordMem_size_at_end hfreeSize
  have hartRead :
      memArt.readWithPadding 224 32 =
        UInt256.toByteArray (solcSlotWord σ I (frobUrnArtSlot I)) := by
    unfold memArt
    rw [writeWordMem_read32_below]
    · exact hfreeRead
    · rw [hfreeSize]; omega
    · omega
    · rw [hfreeSize]; native_decide
  have hrateSize : memRate.size = 480 := by
    unfold memRate
    exact writeWordMem_size_at_end hartSize
  have hrateRead :
      memRate.readWithPadding 224 32 =
        UInt256.toByteArray (solcSlotWord σ I (frobUrnArtSlot I)) := by
    unfold memRate
    rw [writeWordMem_read32_below]
    · exact hartRead
    · rw [hartSize]; omega
    · omega
    · rw [hartSize]; native_decide
  have hspotSize : memSpot.size = 512 := by
    unfold memSpot
    exact writeWordMem_size_at_end hrateSize
  have hspotRead :
      memSpot.readWithPadding 224 32 =
        UInt256.toByteArray (solcSlotWord σ I (frobUrnArtSlot I)) := by
    unfold memSpot
    rw [writeWordMem_read32_below]
    · exact hrateRead
    · rw [hrateSize]; omega
    · omega
    · rw [hrateSize]; native_decide
  have hlineSize : memLine.size = 544 := by
    unfold memLine
    exact writeWordMem_size_at_end hspotSize
  have hlineRead :
      memLine.readWithPadding 224 32 =
        UInt256.toByteArray (solcSlotWord σ I (frobUrnArtSlot I)) := by
    unfold memLine
    rw [writeWordMem_read32_below]
    · exact hspotRead
    · rw [hspotSize]; omega
    · omega
    · rw [hspotSize]; native_decide
  change (writeWordMem 544 (solcSlotWord σ I (frobIlkDustSlot I)) memLine).readWithPadding
    224 32 = UInt256.toByteArray (solcSlotWord σ I (frobUrnArtSlot I))
  rw [writeWordMem_read32_below]
  · exact hlineRead
  · rw [hlineSize]; omega
  · omega
  · rw [hlineSize]; native_decide

theorem frobUrnInkUpdatedMem_read224 (σ : AccountMap) (I : ExecutionEnv)
    (urnInkNew : UInt256) :
    (frobUrnInkUpdatedMem σ I urnInkNew).readWithPadding 224 32 =
      UInt256.toByteArray (solcSlotWord σ I (frobUrnArtSlot I)) := by
  unfold frobUrnInkUpdatedMem
  rw [writeWordMem_read32_above (mem := frobIlkLoadedMem σ I) (off := 192)
    (readOff := 224) (word := urnInkNew)
    (by rw [frobIlkLoadedMem_size σ I]; omega) (by omega)
    (by rw [frobIlkLoadedMem_size σ I]; omega)]
  exact frobIlkLoadedMem_read224 σ I

theorem frobIlkLoadedMem_read416 (σ : AccountMap) (I : ExecutionEnv) :
    (frobIlkLoadedMem σ I).readWithPadding 416 32 =
      UInt256.toByteArray (solcSlotWord σ I (frobIlkArtSlot I)) := by
  let memFree := writeWordMem 64 ⟨576⟩ (frobIlkHashMem σ I)
  let memArt := writeWordMem 416 (solcSlotWord σ I (frobIlkArtSlot I)) memFree
  let memRate := writeWordMem 448 (solcSlotWord σ I (frobIlkRateSlot I)) memArt
  let memSpot := writeWordMem 480 (solcSlotWord σ I (frobIlkSpotSlot I)) memRate
  let memLine := writeWordMem 512 (solcSlotWord σ I (frobIlkLineSlot I)) memSpot
  have hfreeSize : memFree.size = 416 := by
    unfold memFree
    rw [writeWordMem_size_of_contains (word := (⟨576⟩ : UInt256))]
    · exact frobIlkHashMem_size σ I
    · rw [frobIlkHashMem_size σ I]; omega
  have hartSize : memArt.size = 448 := by
    unfold memArt
    exact writeWordMem_size_at_end hfreeSize
  have hartRead :
      memArt.readWithPadding 416 32 =
        UInt256.toByteArray (solcSlotWord σ I (frobIlkArtSlot I)) := by
    unfold memArt
    exact toByteArray_write_read_back_of_gap
      (solcSlotWord σ I (frobIlkArtSlot I)) memFree 416
      (by
        rw [hfreeSize]
        change 0 < USize.size
        native_decide)
  have hrateSize : memRate.size = 480 := by
    unfold memRate
    exact writeWordMem_size_at_end hartSize
  have hrateRead :
      memRate.readWithPadding 416 32 =
        UInt256.toByteArray (solcSlotWord σ I (frobIlkArtSlot I)) := by
    unfold memRate
    rw [writeWordMem_read32_below]
    · exact hartRead
    · rw [hartSize]
    · omega
    · rw [hartSize]; native_decide
  have hspotSize : memSpot.size = 512 := by
    unfold memSpot
    exact writeWordMem_size_at_end hrateSize
  have hspotRead :
      memSpot.readWithPadding 416 32 =
        UInt256.toByteArray (solcSlotWord σ I (frobIlkArtSlot I)) := by
    unfold memSpot
    rw [writeWordMem_read32_below]
    · exact hrateRead
    · rw [hrateSize]; omega
    · omega
    · rw [hrateSize]; native_decide
  have hlineSize : memLine.size = 544 := by
    unfold memLine
    exact writeWordMem_size_at_end hspotSize
  have hlineRead :
      memLine.readWithPadding 416 32 =
        UInt256.toByteArray (solcSlotWord σ I (frobIlkArtSlot I)) := by
    unfold memLine
    rw [writeWordMem_read32_below]
    · exact hspotRead
    · rw [hspotSize]; omega
    · omega
    · rw [hspotSize]; native_decide
  change (writeWordMem 544 (solcSlotWord σ I (frobIlkDustSlot I)) memLine).readWithPadding
    416 32 = UInt256.toByteArray (solcSlotWord σ I (frobIlkArtSlot I))
  rw [writeWordMem_read32_below]
  · exact hlineRead
  · rw [hlineSize]; omega
  · omega
  · rw [hlineSize]; native_decide

theorem frobUrnArtUpdatedMem_read416 (σ : AccountMap) (I : ExecutionEnv)
    (urnInkNew urnArtNew : UInt256) :
    (frobUrnArtUpdatedMem σ I urnInkNew urnArtNew).readWithPadding 416 32 =
      UInt256.toByteArray (solcSlotWord σ I (frobIlkArtSlot I)) := by
  unfold frobUrnArtUpdatedMem frobUrnInkUpdatedMem
  rw [writeWordMem_read32_above (mem := writeWordMem 192 urnInkNew (frobIlkLoadedMem σ I))
    (off := 224) (readOff := 416) (word := urnArtNew)]
  · rw [writeWordMem_read32_above (mem := frobIlkLoadedMem σ I) (off := 192)
      (readOff := 416) (word := urnInkNew)]
    · exact frobIlkLoadedMem_read416 σ I
    · rw [frobIlkLoadedMem_size σ I]; omega
    · omega
    · rw [frobIlkLoadedMem_size σ I]; omega
  · rw [writeWordMem_size_of_contains]
    · rw [frobIlkLoadedMem_size σ I]; omega
    · rw [frobIlkLoadedMem_size σ I]; omega
  · omega
  · rw [writeWordMem_size_of_contains]
    · rw [frobIlkLoadedMem_size σ I]; omega
    · rw [frobIlkLoadedMem_size σ I]; omega

theorem frobIlkArtUpdatedMem_read416 (σ : AccountMap) (I : ExecutionEnv)
    (urnInkNew urnArtNew ilkArtNew : UInt256) :
    (frobIlkArtUpdatedMem σ I urnInkNew urnArtNew ilkArtNew).readWithPadding 416 32 =
      UInt256.toByteArray ilkArtNew := by
  have hbase : (frobUrnArtUpdatedMem σ I urnInkNew urnArtNew).size = 576 := by
    unfold frobUrnArtUpdatedMem frobUrnInkUpdatedMem
    rw [writeWordMem_size_of_contains]
    · rw [writeWordMem_size_of_contains]
      · exact frobIlkLoadedMem_size σ I
      · rw [frobIlkLoadedMem_size σ I]; omega
    · rw [writeWordMem_size_of_contains]
      · rw [frobIlkLoadedMem_size σ I]; omega
      · rw [frobIlkLoadedMem_size σ I]; omega
  unfold frobIlkArtUpdatedMem
  exact toByteArray_write_read_back_of_gap ilkArtNew
    (frobUrnArtUpdatedMem σ I urnInkNew urnArtNew) 416
    (by rw [hbase]; native_decide)

theorem frobIlkLoadedMem_read448 (σ : AccountMap) (I : ExecutionEnv) :
    (frobIlkLoadedMem σ I).readWithPadding 448 32 =
      UInt256.toByteArray (solcSlotWord σ I (frobIlkRateSlot I)) := by
  let memFree := writeWordMem 64 ⟨576⟩ (frobIlkHashMem σ I)
  let memArt := writeWordMem 416 (solcSlotWord σ I (frobIlkArtSlot I)) memFree
  let memRate := writeWordMem 448 (solcSlotWord σ I (frobIlkRateSlot I)) memArt
  let memSpot := writeWordMem 480 (solcSlotWord σ I (frobIlkSpotSlot I)) memRate
  let memLine := writeWordMem 512 (solcSlotWord σ I (frobIlkLineSlot I)) memSpot
  have hfreeSize : memFree.size = 416 := by
    unfold memFree
    rw [writeWordMem_size_of_contains (word := (⟨576⟩ : UInt256))]
    · exact frobIlkHashMem_size σ I
    · rw [frobIlkHashMem_size σ I]; omega
  have hartSize : memArt.size = 448 := by
    unfold memArt
    exact writeWordMem_size_at_end hfreeSize
  have hrateSize : memRate.size = 480 := by
    unfold memRate
    exact writeWordMem_size_at_end hartSize
  have hrateRead :
      memRate.readWithPadding 448 32 =
        UInt256.toByteArray (solcSlotWord σ I (frobIlkRateSlot I)) := by
    unfold memRate
    exact toByteArray_write_read_back_of_gap
      (solcSlotWord σ I (frobIlkRateSlot I)) memArt 448
      (by
        rw [hartSize]
        change 0 < USize.size
        native_decide)
  have hspotSize : memSpot.size = 512 := by
    unfold memSpot
    exact writeWordMem_size_at_end hrateSize
  have hspotRead :
      memSpot.readWithPadding 448 32 =
        UInt256.toByteArray (solcSlotWord σ I (frobIlkRateSlot I)) := by
    unfold memSpot
    rw [writeWordMem_read32_below]
    · exact hrateRead
    · rw [hrateSize]
    · omega
    · rw [hrateSize]; native_decide
  have hlineSize : memLine.size = 544 := by
    unfold memLine
    exact writeWordMem_size_at_end hspotSize
  have hlineRead :
      memLine.readWithPadding 448 32 =
        UInt256.toByteArray (solcSlotWord σ I (frobIlkRateSlot I)) := by
    unfold memLine
    rw [writeWordMem_read32_below]
    · exact hspotRead
    · rw [hspotSize]; omega
    · omega
    · rw [hspotSize]; native_decide
  change (writeWordMem 544 (solcSlotWord σ I (frobIlkDustSlot I)) memLine).readWithPadding
    448 32 = UInt256.toByteArray (solcSlotWord σ I (frobIlkRateSlot I))
  rw [writeWordMem_read32_below]
  · exact hlineRead
  · rw [hlineSize]; omega
  · omega
  · rw [hlineSize]; native_decide

theorem frobIlkArtUpdatedMem_read448 (σ : AccountMap) (I : ExecutionEnv)
    (urnInkNew urnArtNew ilkArtNew : UInt256) :
    (frobIlkArtUpdatedMem σ I urnInkNew urnArtNew ilkArtNew).readWithPadding 448 32 =
      UInt256.toByteArray (solcSlotWord σ I (frobIlkRateSlot I)) := by
  unfold frobIlkArtUpdatedMem frobUrnArtUpdatedMem frobUrnInkUpdatedMem
  rw [writeWordMem_read32_above
    (mem := writeWordMem 224 urnArtNew (writeWordMem 192 urnInkNew (frobIlkLoadedMem σ I)))
    (off := 416) (readOff := 448) (word := ilkArtNew)]
  · rw [writeWordMem_read32_above (mem := writeWordMem 192 urnInkNew (frobIlkLoadedMem σ I))
      (off := 224) (readOff := 448) (word := urnArtNew)]
    · rw [writeWordMem_read32_above (mem := frobIlkLoadedMem σ I) (off := 192)
        (readOff := 448) (word := urnInkNew)]
      · exact frobIlkLoadedMem_read448 σ I
      · rw [frobIlkLoadedMem_size σ I]; omega
      · omega
      · rw [frobIlkLoadedMem_size σ I]; omega
    · rw [writeWordMem_size_of_contains]
      · rw [frobIlkLoadedMem_size σ I]; omega
      · rw [frobIlkLoadedMem_size σ I]; omega
    · omega
    · rw [writeWordMem_size_of_contains]
      · rw [frobIlkLoadedMem_size σ I]; omega
      · rw [frobIlkLoadedMem_size σ I]; omega
  · rw [writeWordMem_size_of_contains]
    · rw [writeWordMem_size_of_contains]
      · rw [frobIlkLoadedMem_size σ I]; omega
      · rw [frobIlkLoadedMem_size σ I]; omega
    · rw [writeWordMem_size_of_contains]
      · rw [frobIlkLoadedMem_size σ I]; omega
      · rw [frobIlkLoadedMem_size σ I]; omega
  · omega
  · rw [writeWordMem_size_of_contains]
    · rw [writeWordMem_size_of_contains]
      · rw [frobIlkLoadedMem_size σ I]; omega
      · rw [frobIlkLoadedMem_size σ I]; omega
    · rw [writeWordMem_size_of_contains]
      · rw [frobIlkLoadedMem_size σ I]; omega
      · rw [frobIlkLoadedMem_size σ I]; omega

theorem frobIlkArtUpdatedMem_read192 (σ : AccountMap) (I : ExecutionEnv)
    (urnInkNew urnArtNew ilkArtNew : UInt256) :
    (frobIlkArtUpdatedMem σ I urnInkNew urnArtNew ilkArtNew).readWithPadding 192 32 =
      UInt256.toByteArray urnInkNew := by
  have hLoadedSize : (frobIlkLoadedMem σ I).size = 576 := frobIlkLoadedMem_size σ I
  have hInkSize : (frobUrnInkUpdatedMem σ I urnInkNew).size = 576 := by
    unfold frobUrnInkUpdatedMem
    rw [writeWordMem_size_of_contains]
    · exact hLoadedSize
    · rw [hLoadedSize]; omega
  have hInkRead :
      (frobUrnInkUpdatedMem σ I urnInkNew).readWithPadding 192 32 =
        UInt256.toByteArray urnInkNew := by
    unfold frobUrnInkUpdatedMem
    exact toByteArray_write_read_back_of_gap urnInkNew (frobIlkLoadedMem σ I) 192
      (by rw [hLoadedSize]; native_decide)
  unfold frobIlkArtUpdatedMem frobUrnArtUpdatedMem
  rw [writeWordMem_read32_below]
  · rw [writeWordMem_read32_below]
    · exact hInkRead
    · rw [hInkSize]; omega
    · omega
    · rw [hInkSize]; native_decide
  · rw [writeWordMem_size_of_contains]
    · rw [hInkSize]; omega
    · rw [hInkSize]; omega
  · omega
  · rw [writeWordMem_size_of_contains]
    · rw [hInkSize]; native_decide
    · rw [hInkSize]; omega

theorem frobIlkLoadedMem_read480 (σ : AccountMap) (I : ExecutionEnv) :
    (frobIlkLoadedMem σ I).readWithPadding 480 32 =
      UInt256.toByteArray (solcSlotWord σ I (frobIlkSpotSlot I)) := by
  let memFree := writeWordMem 64 ⟨576⟩ (frobIlkHashMem σ I)
  let memArt := writeWordMem 416 (solcSlotWord σ I (frobIlkArtSlot I)) memFree
  let memRate := writeWordMem 448 (solcSlotWord σ I (frobIlkRateSlot I)) memArt
  let memSpot := writeWordMem 480 (solcSlotWord σ I (frobIlkSpotSlot I)) memRate
  let memLine := writeWordMem 512 (solcSlotWord σ I (frobIlkLineSlot I)) memSpot
  have hfreeSize : memFree.size = 416 := by
    unfold memFree
    rw [writeWordMem_size_of_contains (word := (⟨576⟩ : UInt256))]
    · exact frobIlkHashMem_size σ I
    · rw [frobIlkHashMem_size σ I]; omega
  have hartSize : memArt.size = 448 := by
    unfold memArt
    exact writeWordMem_size_at_end hfreeSize
  have hrateSize : memRate.size = 480 := by
    unfold memRate
    exact writeWordMem_size_at_end hartSize
  have hspotSize : memSpot.size = 512 := by
    unfold memSpot
    exact writeWordMem_size_at_end hrateSize
  have hspotRead :
      memSpot.readWithPadding 480 32 =
        UInt256.toByteArray (solcSlotWord σ I (frobIlkSpotSlot I)) := by
    unfold memSpot
    exact toByteArray_write_read_back_of_gap
      (solcSlotWord σ I (frobIlkSpotSlot I)) memRate 480
      (by
        rw [hrateSize]
        change 0 < USize.size
        native_decide)
  have hlineRead :
      memLine.readWithPadding 480 32 =
        UInt256.toByteArray (solcSlotWord σ I (frobIlkSpotSlot I)) := by
    unfold memLine
    rw [writeWordMem_read32_below
      (mem := memSpot) (off := 512) (readOff := 480)
      (word := solcSlotWord σ I (frobIlkLineSlot I))
      (by rw [hspotSize]) (by omega) (by rw [hspotSize]; native_decide)]
    exact hspotRead
  change (writeWordMem 544 (solcSlotWord σ I (frobIlkDustSlot I)) memLine).readWithPadding
    480 32 = UInt256.toByteArray (solcSlotWord σ I (frobIlkSpotSlot I))
  rw [writeWordMem_read32_below]
  · exact hlineRead
  · rw [show memLine.size = 544 by
      unfold memLine
      exact writeWordMem_size_at_end hspotSize]
    omega
  · omega
  · rw [show memLine.size = 544 by
      unfold memLine
      exact writeWordMem_size_at_end hspotSize]
    native_decide

theorem frobIlkArtUpdatedMem_read480 (σ : AccountMap) (I : ExecutionEnv)
    (urnInkNew urnArtNew ilkArtNew : UInt256) :
    (frobIlkArtUpdatedMem σ I urnInkNew urnArtNew ilkArtNew).readWithPadding 480 32 =
      UInt256.toByteArray (solcSlotWord σ I (frobIlkSpotSlot I)) := by
  unfold frobIlkArtUpdatedMem frobUrnArtUpdatedMem frobUrnInkUpdatedMem
  rw [writeWordMem_read32_above
    (mem := writeWordMem 224 urnArtNew (writeWordMem 192 urnInkNew (frobIlkLoadedMem σ I)))
    (off := 416) (readOff := 480) (word := ilkArtNew)]
  · rw [writeWordMem_read32_above (mem := writeWordMem 192 urnInkNew (frobIlkLoadedMem σ I))
      (off := 224) (readOff := 480) (word := urnArtNew)]
    · rw [writeWordMem_read32_above (mem := frobIlkLoadedMem σ I) (off := 192)
        (readOff := 480) (word := urnInkNew)]
      · exact frobIlkLoadedMem_read480 σ I
      · rw [frobIlkLoadedMem_size σ I]; omega
      · omega
      · rw [frobIlkLoadedMem_size σ I]; omega
    · rw [writeWordMem_size_of_contains]
      · rw [frobIlkLoadedMem_size σ I]; omega
      · rw [frobIlkLoadedMem_size σ I]; omega
    · omega
    · rw [writeWordMem_size_of_contains]
      · rw [frobIlkLoadedMem_size σ I]; omega
      · rw [frobIlkLoadedMem_size σ I]; omega
  · rw [writeWordMem_size_of_contains]
    · rw [writeWordMem_size_of_contains]
      · rw [frobIlkLoadedMem_size σ I]; omega
      · rw [frobIlkLoadedMem_size σ I]; omega
    · rw [writeWordMem_size_of_contains]
      · rw [frobIlkLoadedMem_size σ I]; omega
      · rw [frobIlkLoadedMem_size σ I]; omega
  · omega
  · rw [writeWordMem_size_of_contains]
    · rw [writeWordMem_size_of_contains]
      · rw [frobIlkLoadedMem_size σ I]; omega
      · rw [frobIlkLoadedMem_size σ I]; omega
    · rw [writeWordMem_size_of_contains]
      · rw [frobIlkLoadedMem_size σ I]; omega
      · rw [frobIlkLoadedMem_size σ I]; omega

theorem frobIlkLoadedMem_read512 (σ : AccountMap) (I : ExecutionEnv) :
    (frobIlkLoadedMem σ I).readWithPadding 512 32 =
      UInt256.toByteArray (solcSlotWord σ I (frobIlkLineSlot I)) := by
  let memFree := writeWordMem 64 ⟨576⟩ (frobIlkHashMem σ I)
  let memArt := writeWordMem 416 (solcSlotWord σ I (frobIlkArtSlot I)) memFree
  let memRate := writeWordMem 448 (solcSlotWord σ I (frobIlkRateSlot I)) memArt
  let memSpot := writeWordMem 480 (solcSlotWord σ I (frobIlkSpotSlot I)) memRate
  let memLine := writeWordMem 512 (solcSlotWord σ I (frobIlkLineSlot I)) memSpot
  have hfreeSize : memFree.size = 416 := by
    unfold memFree
    rw [writeWordMem_size_of_contains (word := (⟨576⟩ : UInt256))]
    · exact frobIlkHashMem_size σ I
    · rw [frobIlkHashMem_size σ I]; omega
  have hartSize : memArt.size = 448 := by
    unfold memArt
    exact writeWordMem_size_at_end hfreeSize
  have hrateSize : memRate.size = 480 := by
    unfold memRate
    exact writeWordMem_size_at_end hartSize
  have hspotSize : memSpot.size = 512 := by
    unfold memSpot
    exact writeWordMem_size_at_end hrateSize
  have hlineRead :
      memLine.readWithPadding 512 32 =
        UInt256.toByteArray (solcSlotWord σ I (frobIlkLineSlot I)) := by
    unfold memLine
    exact toByteArray_write_read_back_of_gap
      (solcSlotWord σ I (frobIlkLineSlot I)) memSpot 512
      (by
        rw [hspotSize]
        change 0 < USize.size
        native_decide)
  change (writeWordMem 544 (solcSlotWord σ I (frobIlkDustSlot I)) memLine).readWithPadding
    512 32 = UInt256.toByteArray (solcSlotWord σ I (frobIlkLineSlot I))
  rw [writeWordMem_read32_below]
  · exact hlineRead
  · rw [show memLine.size = 544 by
      unfold memLine
      exact writeWordMem_size_at_end hspotSize]
  · omega
  · rw [show memLine.size = 544 by
      unfold memLine
      exact writeWordMem_size_at_end hspotSize]
    native_decide

theorem frobIlkLoadedMem_read544 (σ : AccountMap) (I : ExecutionEnv) :
    (frobIlkLoadedMem σ I).readWithPadding 544 32 =
      UInt256.toByteArray (solcSlotWord σ I (frobIlkDustSlot I)) := by
  let memFree := writeWordMem 64 ⟨576⟩ (frobIlkHashMem σ I)
  let memArt := writeWordMem 416 (solcSlotWord σ I (frobIlkArtSlot I)) memFree
  let memRate := writeWordMem 448 (solcSlotWord σ I (frobIlkRateSlot I)) memArt
  let memSpot := writeWordMem 480 (solcSlotWord σ I (frobIlkSpotSlot I)) memRate
  let memLine := writeWordMem 512 (solcSlotWord σ I (frobIlkLineSlot I)) memSpot
  have hfreeSize : memFree.size = 416 := by
    unfold memFree
    rw [writeWordMem_size_of_contains (word := (⟨576⟩ : UInt256))]
    · exact frobIlkHashMem_size σ I
    · rw [frobIlkHashMem_size σ I]; omega
  have hartSize : memArt.size = 448 := by
    unfold memArt
    exact writeWordMem_size_at_end hfreeSize
  have hrateSize : memRate.size = 480 := by
    unfold memRate
    exact writeWordMem_size_at_end hartSize
  have hspotSize : memSpot.size = 512 := by
    unfold memSpot
    exact writeWordMem_size_at_end hrateSize
  have hlineSize : memLine.size = 544 := by
    unfold memLine
    exact writeWordMem_size_at_end hspotSize
  change (writeWordMem 544 (solcSlotWord σ I (frobIlkDustSlot I)) memLine).readWithPadding
    544 32 = UInt256.toByteArray (solcSlotWord σ I (frobIlkDustSlot I))
  exact toByteArray_write_read_back_of_gap
    (solcSlotWord σ I (frobIlkDustSlot I)) memLine 544
    (by rw [hlineSize]; native_decide)

theorem frobIlkArtUpdatedMem_read512 (σ : AccountMap) (I : ExecutionEnv)
    (urnInkNew urnArtNew ilkArtNew : UInt256) :
    (frobIlkArtUpdatedMem σ I urnInkNew urnArtNew ilkArtNew).readWithPadding 512 32 =
      UInt256.toByteArray (solcSlotWord σ I (frobIlkLineSlot I)) := by
  unfold frobIlkArtUpdatedMem frobUrnArtUpdatedMem frobUrnInkUpdatedMem
  rw [writeWordMem_read32_above
    (mem := writeWordMem 224 urnArtNew (writeWordMem 192 urnInkNew (frobIlkLoadedMem σ I)))
    (off := 416) (readOff := 512) (word := ilkArtNew)]
  · rw [writeWordMem_read32_above (mem := writeWordMem 192 urnInkNew (frobIlkLoadedMem σ I))
      (off := 224) (readOff := 512) (word := urnArtNew)]
    · rw [writeWordMem_read32_above (mem := frobIlkLoadedMem σ I) (off := 192)
        (readOff := 512) (word := urnInkNew)]
      · exact frobIlkLoadedMem_read512 σ I
      · rw [frobIlkLoadedMem_size σ I]; omega
      · omega
      · rw [frobIlkLoadedMem_size σ I]; omega
    · rw [writeWordMem_size_of_contains]
      · rw [frobIlkLoadedMem_size σ I]; omega
      · rw [frobIlkLoadedMem_size σ I]; omega
    · omega
    · rw [writeWordMem_size_of_contains]
      · rw [frobIlkLoadedMem_size σ I]; omega
      · rw [frobIlkLoadedMem_size σ I]; omega
  · rw [writeWordMem_size_of_contains]
    · rw [writeWordMem_size_of_contains]
      · rw [frobIlkLoadedMem_size σ I]; omega
      · rw [frobIlkLoadedMem_size σ I]; omega
    · rw [writeWordMem_size_of_contains]
      · rw [frobIlkLoadedMem_size σ I]; omega
      · rw [frobIlkLoadedMem_size σ I]; omega
  · omega
  · rw [writeWordMem_size_of_contains]
    · rw [writeWordMem_size_of_contains]
      · rw [frobIlkLoadedMem_size σ I]; omega
      · rw [frobIlkLoadedMem_size σ I]; omega
    · rw [writeWordMem_size_of_contains]
      · rw [frobIlkLoadedMem_size σ I]; omega
      · rw [frobIlkLoadedMem_size σ I]; omega

theorem frobIlkArtUpdatedMem_read544 (σ : AccountMap) (I : ExecutionEnv)
    (urnInkNew urnArtNew ilkArtNew : UInt256) :
    (frobIlkArtUpdatedMem σ I urnInkNew urnArtNew ilkArtNew).readWithPadding 544 32 =
      UInt256.toByteArray (solcSlotWord σ I (frobIlkDustSlot I)) := by
  unfold frobIlkArtUpdatedMem frobUrnArtUpdatedMem frobUrnInkUpdatedMem
  rw [writeWordMem_read32_above
    (mem := writeWordMem 224 urnArtNew (writeWordMem 192 urnInkNew (frobIlkLoadedMem σ I)))
    (off := 416) (readOff := 544) (word := ilkArtNew)]
  · rw [writeWordMem_read32_above (mem := writeWordMem 192 urnInkNew (frobIlkLoadedMem σ I))
      (off := 224) (readOff := 544) (word := urnArtNew)]
    · rw [writeWordMem_read32_above (mem := frobIlkLoadedMem σ I) (off := 192)
        (readOff := 544) (word := urnInkNew)]
      · exact frobIlkLoadedMem_read544 σ I
      · rw [frobIlkLoadedMem_size σ I]; omega
      · omega
      · rw [frobIlkLoadedMem_size σ I]
    · rw [writeWordMem_size_of_contains]
      · rw [frobIlkLoadedMem_size σ I]; omega
      · rw [frobIlkLoadedMem_size σ I]; omega
    · omega
    · rw [writeWordMem_size_of_contains]
      · rw [frobIlkLoadedMem_size σ I]
      · rw [frobIlkLoadedMem_size σ I]; omega
  · rw [writeWordMem_size_of_contains]
    · rw [writeWordMem_size_of_contains]
      · rw [frobIlkLoadedMem_size σ I]; omega
      · rw [frobIlkLoadedMem_size σ I]; omega
    · rw [writeWordMem_size_of_contains]
      · rw [frobIlkLoadedMem_size σ I]; omega
      · rw [frobIlkLoadedMem_size σ I]; omega
  · omega
  · rw [writeWordMem_size_of_contains]
    · rw [writeWordMem_size_of_contains]
      · rw [frobIlkLoadedMem_size σ I]
      · rw [frobIlkLoadedMem_size σ I]; omega
    · rw [writeWordMem_size_of_contains]
      · rw [frobIlkLoadedMem_size σ I]; omega
      · rw [frobIlkLoadedMem_size σ I]; omega

theorem frobIlkArtUpdatedMem_read224 (σ : AccountMap) (I : ExecutionEnv)
    (urnInkNew urnArtNew ilkArtNew : UInt256) :
    (frobIlkArtUpdatedMem σ I urnInkNew urnArtNew ilkArtNew).readWithPadding 224 32 =
      UInt256.toByteArray urnArtNew := by
  have hInkSize : (frobUrnInkUpdatedMem σ I urnInkNew).size = 576 := by
    unfold frobUrnInkUpdatedMem
    rw [writeWordMem_size_of_contains]
    · exact frobIlkLoadedMem_size σ I
    · rw [frobIlkLoadedMem_size σ I]; omega
  unfold frobIlkArtUpdatedMem frobUrnArtUpdatedMem
  rw [writeWordMem_read32_below]
  · exact toByteArray_write_read_back_of_gap urnArtNew
      (frobUrnInkUpdatedMem σ I urnInkNew) 224
      (by rw [hInkSize]; native_decide)
  · rw [writeWordMem_size_of_contains]
    · rw [hInkSize]; omega
    · rw [hInkSize]; omega
  · omega
  · rw [writeWordMem_size_of_contains]
    · rw [hInkSize]; native_decide
    · rw [hInkSize]; native_decide

theorem RD.vatFrobAlloc2
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {k C : ℕ} {ret : UInt256} {R : List UInt256}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD vatBytecode ee g s0 ⟨6847⟩ (ret :: R) solcFreePtrMem (UInt256.ofNat 3)
      rdata acc k C)
    (hret : (D_J vatBytecode 0).contains ret = true)
    (hov : R.length + 5 ≤ 1024) :
    ∃ k' C', RD vatBytecode ee g s0 ret (⟨128⟩ :: R) (frobAlloc2Mem solcFreePtrMem)
      (UInt256.ofNat 6) rdata acc k' C' := by
  have rd6848 := h.jumpdest (by native_decide) (by evm_ov)
  have rd6850 := rd6848.push1 ⟨64⟩ (by native_decide) (by evm_ov)
  have rd6851 := rd6850.mload 0 ⟨128⟩ (UInt256.ofNat 3) (by native_decide)
    mem_cost solcFreePtrMem_mload64 (by native_decide) (by evm_ov)
  have rd6852 := rd6851.dup1 (by native_decide) (by evm_ov)
  have rd6854 := rd6852.push1 ⟨64⟩ (by native_decide) (by evm_ov)
  have rd6855 := rd6854.add (by native_decide) (by evm_ov)
  have rd6857 := rd6855.push1 ⟨64⟩ (by native_decide) (by evm_ov)
  have rd6858 := rd6857.mstore 0 (writeWordMem 64 ⟨192⟩ solcFreePtrMem)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd6859 := rd6858.dup1 (by native_decide) (by evm_ov)
  have rd6861 := rd6859.push1 ⟨0⟩ (by native_decide) (by evm_ov)
  have rd6862 := rd6861.dup2 (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rd6863 := rd6862.mstore 6 (writeWordMem 128 ⟨0⟩
      (writeWordMem 64 ⟨192⟩ solcFreePtrMem))
    (UInt256.ofNat 5) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd6865 := rd6863.push1 ⟨32⟩ (by native_decide) (by evm_ov)
  have rd6866 := rd6865.add (by native_decide) (by evm_ov)
  have rd6868 := rd6866.push1 ⟨0⟩ (by native_decide) (by evm_ov)
  have rd6869 := rd6868.dup2 (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rd6870 := rd6869.mstore 3 (frobAlloc2Mem solcFreePtrMem)
    (UInt256.ofNat 6) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd6871 := rd6870.pop (by native_decide) (by evm_ov)
  have rd6872 := rd6871.swap1 (by native_decide) (by evm_ov)
  exact ⟨_, _, rd6872.jump (by native_decide) hret (by evm_ov)⟩

theorem RD.vatFrobAlloc5
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {k C : ℕ} {ret : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD vatBytecode ee g s0 ⟨6873⟩ (ret :: R) mem (UInt256.ofNat 8)
      rdata acc k C)
    (hmemLt : 64 < mem.size)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨256⟩)
    (hret : (D_J vatBytecode 0).contains ret = true)
    (hov : R.length + 5 ≤ 1024) :
    ∃ k' C', RD vatBytecode ee g s0 ret (⟨256⟩ :: R) (frobAlloc5Mem mem)
      (UInt256.ofNat 13) rdata acc k' C' := by
  have hmload :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 8 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨256⟩ := by
    exact mloadWordValue_of_readWithPadding
      (by simpa [show (⟨64⟩ : UInt256).toNat = 64 from by decide] using hmemLt)
      (by native_decide)
      (by simpa [show (⟨64⟩ : UInt256).toNat = 64 from by decide] using hread64)
  have rd6874 := h.jumpdest (by native_decide) (by evm_ov)
  have rd6876 := rd6874.push1 ⟨64⟩ (by native_decide) (by evm_ov)
  have rd6877 := rd6876.mload 0 ⟨256⟩ (UInt256.ofNat 8) (by native_decide)
    mem_cost hmload (by native_decide) (by evm_ov)
  have rd6878 := rd6877.dup1 (by native_decide) (by evm_ov)
  have rd6880 := rd6878.push1 ⟨160⟩ (by native_decide) (by evm_ov)
  have rd6881 := rd6880.add (by native_decide) (by evm_ov)
  have rd6883 := rd6881.push1 ⟨64⟩ (by native_decide) (by evm_ov)
  have rd6884 := rd6883.mstore 0 (writeWordMem 64 ⟨416⟩ mem)
    (UInt256.ofNat 8) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd6885 := rd6884.dup1 (by native_decide) (by evm_ov)
  have rd6887 := rd6885.push1 ⟨0⟩ (by native_decide) (by evm_ov)
  have rd6888 := rd6887.dup2 (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rd6889 := rd6888.mstore 3 (writeWordMem 256 ⟨0⟩ (writeWordMem 64 ⟨416⟩ mem))
    (UInt256.ofNat 9) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd6891 := rd6889.push1 ⟨32⟩ (by native_decide) (by evm_ov)
  have rd6892 := rd6891.add (by native_decide) (by evm_ov)
  have rd6894 := rd6892.push1 ⟨0⟩ (by native_decide) (by evm_ov)
  have rd6895 := rd6894.dup2 (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rd6896 := rd6895.mstore 3
    (writeWordMem 288 ⟨0⟩ (writeWordMem 256 ⟨0⟩ (writeWordMem 64 ⟨416⟩ mem)))
    (UInt256.ofNat 10) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd6898 := rd6896.push1 ⟨32⟩ (by native_decide) (by evm_ov)
  have rd6899 := rd6898.add (by native_decide) (by evm_ov)
  have rd6901 := rd6899.push1 ⟨0⟩ (by native_decide) (by evm_ov)
  have rd6902 := rd6901.dup2 (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rd6903 := rd6902.mstore 3
    (writeWordMem 320 ⟨0⟩
      (writeWordMem 288 ⟨0⟩ (writeWordMem 256 ⟨0⟩ (writeWordMem 64 ⟨416⟩ mem))))
    (UInt256.ofNat 11) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd6905 := rd6903.push1 ⟨32⟩ (by native_decide) (by evm_ov)
  have rd6906 := rd6905.add (by native_decide) (by evm_ov)
  have rd6908 := rd6906.push1 ⟨0⟩ (by native_decide) (by evm_ov)
  have rd6909 := rd6908.dup2 (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rd6910 := rd6909.mstore 3
    (writeWordMem 352 ⟨0⟩
      (writeWordMem 320 ⟨0⟩
        (writeWordMem 288 ⟨0⟩
          (writeWordMem 256 ⟨0⟩ (writeWordMem 64 ⟨416⟩ mem)))))
    (UInt256.ofNat 12) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd6912 := rd6910.push1 ⟨32⟩ (by native_decide) (by evm_ov)
  have rd6913 := rd6912.add (by native_decide) (by evm_ov)
  have rd6915 := rd6913.push1 ⟨0⟩ (by native_decide) (by evm_ov)
  have rd6916 := rd6915.dup2 (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rd6917 := rd6916.mstore 3 (frobAlloc5Mem mem)
    (UInt256.ofNat 13) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd6918 := rd6917.pop (by native_decide) (by evm_ov)
  have rd6919 := rd6918.swap1 (by native_decide) (by evm_ov)
  exact ⟨_, _, rd6919.jump (by native_decide) hret (by evm_ov)⟩

theorem RD.vatFrobUrnLoads
    {cA gh bl σ σ₀ A I} {g : Sat256} {k C : ℕ} {sel : UInt256}
    (h : RD vatBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3045⟩
      [frobDartWord I, frobDinkWord I, frobWMaskedWord I, frobVMaskedWord I,
        frobUMaskedWord I, frobIWord I, ⟨524⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD vatBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3119⟩
      [⟨192⟩, frobDartWord I, frobDinkWord I, frobWMaskedWord I,
        frobVMaskedWord I, frobUMaskedWord I, frobIWord I, ⟨524⟩, sel]
      (frobAlloc5Mem (frobUrnLoadedMem σ I)) (UInt256.ofNat 13)
      ByteArray.empty (cA, σ) k' C' := by
  let urnsIlk := solcMappingSlot ⟨3⟩ (frobIWord I)
  let urnBase := solcMappingSlot urnsIlk (frobUMaskedWord I)
  let urnInkOld := solcSlotWord σ I urnBase
  let urnArtOld := solcSlotWord σ I (urnBase + ⟨1⟩)
  have rd3046 := h.jumpdest (by native_decide) (by evm_ov)
  have rd3049 := rd3046.push2 ⟨3053⟩ (by native_decide) (by evm_ov)
  have rd3052 := rd3049.push2 ⟨6847⟩ (by native_decide) (by evm_ov)
  have rd6847 := rd3052.jump (by native_decide) (by jump_dest) (by evm_ov)
  obtain ⟨_, _, rd3053raw⟩ := RD.vatFrobAlloc2 rd6847 (by jump_dest) (by simp)
  have rd3054pre := rd3053raw.jumpdest (by native_decide) (by evm_ov)
  have rd3055 := rd3054pre.pop (by native_decide) (by evm_ov)
  have rd3057 := rd3055.push1 ⟨0⟩ (by native_decide) (by evm_ov)
  have rd3058 := rd3057.dup7 (by native_decide) (by evm_ov)
  have rd3059 := rd3058.dup2 (by native_decide) (by evm_ov)
  have rd3060 := rd3059.mstore 0
    (wordAt0Mem (frobIWord I) (frobAlloc2Mem solcFreePtrMem))
    (UInt256.ofNat 6) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd3062 := rd3060.push1 ⟨3⟩ (by native_decide) (by evm_ov)
  have rd3064 := rd3062.push1 ⟨32⟩ (by native_decide) (by evm_ov)
  have rd3065 := rd3064.swap1 (by native_decide) (by evm_ov)
  have rd3066 := rd3065.dup2 (by native_decide) (by evm_ov)
  have rd3067 := rd3066.mstore 0 (frobUrnHashMem I)
    (UInt256.ofNat 6) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd3069 := rd3067.push1 ⟨64⟩ (by native_decide) (by evm_ov)
  have rd3070 := rd3069.dup1 (by native_decide) (by evm_ov)
  have rd3071 := rd3070.dup4 (by native_decide) (by evm_ov)
  have hurnsIlk :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((frobUrnHashMem I).readWithPadding 0 64))) = urnsIlk := by
    simpa [frobUrnHashMem, urnsIlk] using
      twoWordHashMem_solcMappingSlot_of_ge64 ⟨3⟩ (frobIWord I)
        (by rw [frobAlloc2Mem_solc_size]; omega)
  have rd3072 := rd3071.keccak256 0 urnsIlk (UInt256.ofNat 6)
    (by native_decide) mem_cost hurnsIlk (by native_decide) (by evm_ov)
  have rd3074 := rd3072.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  have rd3076 := rd3074.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  have rd3078 := rd3076.push1 ⟨160⟩ (by native_decide) (by evm_ov)
  have rd3079 := rd3078.shl (by native_decide) (by evm_ov)
  have rd3080 := rd3079.sub (by native_decide) (by evm_ov)
  have rd3081 := rd3080.dup10 (by native_decide) (by evm_ov)
  have rd3082raw := rd3081.and (by native_decide) (by evm_ov)
  have hmask :
      UInt256.land (frobUMaskedWord I)
        (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩) =
        frobUMaskedWord I := by
    rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by decide]
    exact frobUMaskedWord_clean I
  have rd3082 := rd3082raw
  rw [hmask] at rd3082
  have rd3083 := rd3082.dup5 (by native_decide) (by evm_ov)
  have rd3084 := rd3083.mstore 0
    (wordAt0Mem (frobUMaskedWord I) (frobUrnHashMem I))
    (UInt256.ofNat 6) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd3085 := rd3084.dup3 (by native_decide) (by evm_ov)
  have rd3086 := rd3085.mstore 0 (frobUrnBaseMem I)
    (UInt256.ofNat 6) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd3087 := rd3086.swap2 (by native_decide) (by evm_ov)
  have rd3088 := rd3087.dup3 (by native_decide) (by evm_ov)
  have rd3089 := rd3088.swap1 (by native_decide) (by evm_ov)
  have hurnBase :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((frobUrnBaseMem I).readWithPadding 0 64))) = urnBase := by
    simpa [frobUrnBaseMem, urnBase, urnsIlk] using
      twoWordHashMem_solcMappingSlot_of_ge64 urnsIlk (frobUMaskedWord I)
        (by rw [frobUrnHashMem_size I]; omega)
  have rd3090 := rd3089.keccak256 0 urnBase (UInt256.ofNat 6)
    (by native_decide) mem_cost hurnBase (by native_decide) (by evm_ov)
  have rd3091pre := rd3090.dup3 (by native_decide) (by evm_ov)
  have h64ToNat : (⟨64⟩ : UInt256).toNat = 64 := by decide
  have hmload192 :
      (if (⟨64⟩ : UInt256).toNat ≥ (frobUrnBaseMem I).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
          ((frobUrnBaseMem I).readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨192⟩ := by
    exact mloadWordValue_of_readWithPadding
      (by rw [h64ToNat, frobUrnBaseMem_size I]; omega)
      (by native_decide)
      (by simpa [h64ToNat] using frobUrnBaseMem_read64 I)
  have rd3092 := rd3091pre.mload 0 ⟨192⟩ (UInt256.ofNat 6)
    (by native_decide) mem_cost hmload192 (by native_decide) (by evm_ov)
  have rd3093 := rd3092.dup1 (by native_decide) (by evm_ov)
  have rd3094 := rd3093.dup5 (by native_decide) (by evm_ov)
  have rd3095 := rd3094.add (by native_decide) (by evm_ov)
  have rd3096 := rd3095.swap1 (by native_decide) (by evm_ov)
  have rd3097 := rd3096.swap4 (by native_decide) (by evm_ov)
  have rd3098 := rd3097.mstore 0
    (writeWordMem 64 ⟨256⟩ (frobUrnBaseMem I))
    (UInt256.ofNat 6) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd3099pre := rd3098.dup1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd3100raw⟩ := rd3099pre.sload (by native_decide) (by evm_ov)
  have hInkRaw :
      (σ.find? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD urnBase ⟨0⟩)) = urnInkOld := by
    simp [urnInkOld, solcSlotWord]
  have rd3100 := rd3100raw
  rw [hInkRaw] at rd3100
  have rd3101pre := rd3100.dup4 (by native_decide) (by evm_ov)
  have rd3102 := rd3101pre.mstore 3
    (writeWordMem 192 urnInkOld (writeWordMem 64 ⟨256⟩ (frobUrnBaseMem I)))
    (UInt256.ofNat 7) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd3104 := rd3102.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  have rd3105pre := rd3104.add (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd3106raw⟩ := rd3105pre.sload (by native_decide) (by evm_ov)
  have hArtRaw :
      (σ.find? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD (⟨1⟩ + urnBase) ⟨0⟩)) = urnArtOld := by
    simp [urnArtOld, solcSlotWord, u256_add_comm (⟨1⟩ : UInt256) urnBase]
  have rd3106 := rd3106raw
  rw [hArtRaw] at rd3106
  have rd3107 := rd3106.swap1 (by native_decide) (by evm_ov)
  have rd3108 := rd3107.dup3 (by native_decide) (by evm_ov)
  have rd3109pre := rd3108.add (by native_decide) (by evm_ov)
  have rd3110 := rd3109pre.mstore 3
    (frobUrnLoadedMem σ I) (UInt256.ofNat 8)
    (by native_decide) mem_cost
    (by
      rw [show ((⟨192⟩ : UInt256) + ⟨32⟩).toNat = 224 from by native_decide]
      simp [writeWordMem, frobUrnLoadedMem, urnInkOld, urnArtOld, frobUrnInkSlot,
        frobUrnArtSlot, frobUrnBase, urnBase, urnsIlk])
    (by native_decide) (by evm_ov)
  have rd3113 := rd3110.push2 ⟨3117⟩ (by native_decide) (by evm_ov)
  have rd3116 := rd3113.push2 ⟨6873⟩ (by native_decide) (by evm_ov)
  have rd6873 := rd3116.jump (by native_decide) (by jump_dest) (by evm_ov)
  obtain ⟨_, _, rd3117raw⟩ := RD.vatFrobAlloc5 rd6873
    (by rw [frobUrnLoadedMem_size σ I]; omega)
    (frobUrnLoadedMem_read64 σ I) (by jump_dest) (by simp)
  have rd3118 := rd3117raw.jumpdest (by native_decide) (by evm_ov)
  have rd3119 := rd3118.pop (by native_decide) (by evm_ov)
  exact ⟨_, _, by
    simpa [urnsIlk, urnBase, urnInkOld, urnArtOld, frobUrnInkSlot,
      frobUrnArtSlot, frobUrnBase, u256_add_comm (⟨1⟩ : UInt256) urnBase]
      using rd3119⟩

abbrev vatNotInitRawWord : UInt256 :=
  ⟨28704904237161325316230594861668735581⟩

noncomputable def frobNotInitErrorMem0 (mem : ByteArray) : ByteArray :=
  writeWordMem 576 solcErrorStringSelector mem

noncomputable def frobNotInitErrorMem1 (mem : ByteArray) : ByteArray :=
  writeWordMem 580 ⟨32⟩ (frobNotInitErrorMem0 mem)

noncomputable def frobNotInitErrorMem2 (mem : ByteArray) : ByteArray :=
  writeWordMem 612 ⟨16⟩ (frobNotInitErrorMem1 mem)

noncomputable def frobNotInitErrorMem3 (mem : ByteArray) : ByteArray :=
  writeWordMem 644 (UInt256.shiftLeft vatNotInitRawWord ⟨130⟩)
    (frobNotInitErrorMem2 mem)

theorem frobNotInitErrorMem0_size {mem : ByteArray} (hmem : mem.size = 576) :
    (frobNotInitErrorMem0 mem).size = 608 := by
  unfold frobNotInitErrorMem0 writeWordMem
  rw [toByteArray_write32_size_of_ge mem solcErrorStringSelector 576 576 608
    hmem (by omega) (by native_decide) (by omega)]

theorem frobNotInitErrorMem1_size {mem : ByteArray} (hmem : mem.size = 576) :
    (frobNotInitErrorMem1 mem).size = 612 := by
  unfold frobNotInitErrorMem1 writeWordMem
  rw [toByteArray_write32_size_of_le (frobNotInitErrorMem0 mem) (⟨32⟩ : UInt256)
    580 608 612 (frobNotInitErrorMem0_size hmem)
    (by rw [frobNotInitErrorMem0_size hmem]; omega) (by omega)]

theorem frobNotInitErrorMem2_size {mem : ByteArray} (hmem : mem.size = 576) :
    (frobNotInitErrorMem2 mem).size = 644 := by
  unfold frobNotInitErrorMem2 writeWordMem
  rw [toByteArray_write32_size_of_ge (frobNotInitErrorMem1 mem) (⟨16⟩ : UInt256)
    612 612 644 (frobNotInitErrorMem1_size hmem) (by omega)
    (by native_decide) (by omega)]

theorem frobNotInitErrorMem3_size {mem : ByteArray} (hmem : mem.size = 576) :
    (frobNotInitErrorMem3 mem).size = 676 := by
  unfold frobNotInitErrorMem3 writeWordMem
  rw [toByteArray_write32_size_of_ge (frobNotInitErrorMem2 mem)
    (UInt256.shiftLeft vatNotInitRawWord ⟨130⟩) 644 644 676
    (frobNotInitErrorMem2_size hmem) (by omega)
    (by native_decide) (by omega)]

theorem frobNotInitErrorMem3_read64 {mem : ByteArray}
    (hmem : mem.size = 576)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨576⟩) :
    (frobNotInitErrorMem3 mem).readWithPadding 64 32 =
      UInt256.toByteArray ⟨576⟩ := by
  let err0 := frobNotInitErrorMem0 mem
  let err1 := frobNotInitErrorMem1 mem
  let err2 := frobNotInitErrorMem2 mem
  have herr0Size : err0.size = 608 := by
    unfold err0
    exact frobNotInitErrorMem0_size hmem
  have herr1Size : err1.size = 612 := by
    unfold err1
    exact frobNotInitErrorMem1_size hmem
  have herr2Size : err2.size = 644 := by
    unfold err2
    exact frobNotInitErrorMem2_size hmem
  have herr0Read : err0.readWithPadding 64 32 = UInt256.toByteArray ⟨576⟩ := by
    unfold err0 frobNotInitErrorMem0
    rw [writeWordMem_read64_below]
    · exact hread64
    · rw [hmem]; omega
    · omega
    · rw [hmem]; native_decide
  have herr1Read : err1.readWithPadding 64 32 = UInt256.toByteArray ⟨576⟩ := by
    unfold err1 frobNotInitErrorMem1
    change (writeWordMem 580 (⟨32⟩ : UInt256) err0).readWithPadding 64 32 =
      UInt256.toByteArray ⟨576⟩
    rw [writeWordMem_read64_below]
    · exact herr0Read
    · rw [herr0Size]; omega
    · omega
    · rw [herr0Size]; native_decide
  have herr2Read : err2.readWithPadding 64 32 = UInt256.toByteArray ⟨576⟩ := by
    unfold err2 frobNotInitErrorMem2
    change (writeWordMem 612 (⟨16⟩ : UInt256) err1).readWithPadding 64 32 =
      UInt256.toByteArray ⟨576⟩
    rw [writeWordMem_read64_below]
    · exact herr1Read
    · rw [herr1Size]; omega
    · omega
    · rw [herr1Size]; native_decide
  unfold frobNotInitErrorMem3
  change (writeWordMem 644 (UInt256.shiftLeft vatNotInitRawWord ⟨130⟩) err2).readWithPadding 64 32 =
    UInt256.toByteArray ⟨576⟩
  rw [writeWordMem_read64_below]
  · exact herr2Read
  · rw [herr2Size]; omega
  · omega
  · rw [herr2Size]; native_decide

noncomputable def frobErrorStringMem0 (mem : ByteArray) : ByteArray :=
  writeWordMem 576 solcErrorStringSelector mem

noncomputable def frobErrorStringMem1 (mem : ByteArray) : ByteArray :=
  writeWordMem 580 (⟨32⟩ : UInt256) (frobErrorStringMem0 mem)

noncomputable def frobErrorStringMem2 (len : UInt256) (mem : ByteArray) : ByteArray :=
  writeWordMem 612 len (frobErrorStringMem1 mem)

noncomputable def frobErrorStringMem3 (len word : UInt256) (mem : ByteArray) : ByteArray :=
  writeWordMem 644 word (frobErrorStringMem2 len mem)

theorem frobErrorStringMem0_size {mem : ByteArray} (hmem : mem.size = 576) :
    (frobErrorStringMem0 mem).size = 608 := by
  unfold frobErrorStringMem0 writeWordMem
  rw [toByteArray_write32_size_of_ge mem solcErrorStringSelector 576 576 608
    hmem (by omega) (by native_decide) (by omega)]

theorem frobErrorStringMem1_size {mem : ByteArray} (hmem : mem.size = 576) :
    (frobErrorStringMem1 mem).size = 612 := by
  unfold frobErrorStringMem1 writeWordMem
  rw [toByteArray_write32_size_of_le (frobErrorStringMem0 mem) (⟨32⟩ : UInt256)
    580 608 612 (frobErrorStringMem0_size hmem)
    (by rw [frobErrorStringMem0_size hmem]; omega) (by omega)]

theorem frobErrorStringMem2_size (len : UInt256) {mem : ByteArray}
    (hmem : mem.size = 576) :
    (frobErrorStringMem2 len mem).size = 644 := by
  unfold frobErrorStringMem2 writeWordMem
  rw [toByteArray_write32_size_of_ge (frobErrorStringMem1 mem) len
    612 612 644 (frobErrorStringMem1_size hmem) (by omega)
    (by native_decide) (by omega)]

theorem frobErrorStringMem3_size (len word : UInt256) {mem : ByteArray}
    (hmem : mem.size = 576) :
    (frobErrorStringMem3 len word mem).size = 676 := by
  unfold frobErrorStringMem3 writeWordMem
  rw [toByteArray_write32_size_of_ge (frobErrorStringMem2 len mem) word
    644 644 676 (frobErrorStringMem2_size len hmem) (by omega)
    (by native_decide) (by omega)]

theorem frobErrorStringMem3_read64 (len word : UInt256) {mem : ByteArray}
    (hmem : mem.size = 576)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨576⟩) :
    (frobErrorStringMem3 len word mem).readWithPadding 64 32 =
      UInt256.toByteArray ⟨576⟩ := by
  let err0 := frobErrorStringMem0 mem
  let err1 := frobErrorStringMem1 mem
  let err2 := frobErrorStringMem2 len mem
  have herr0Size : err0.size = 608 := by
    unfold err0
    exact frobErrorStringMem0_size hmem
  have herr1Size : err1.size = 612 := by
    unfold err1
    exact frobErrorStringMem1_size hmem
  have herr2Size : err2.size = 644 := by
    unfold err2
    exact frobErrorStringMem2_size len hmem
  have herr0Read : err0.readWithPadding 64 32 = UInt256.toByteArray ⟨576⟩ := by
    unfold err0 frobErrorStringMem0
    rw [writeWordMem_read64_below]
    · exact hread64
    · rw [hmem]; omega
    · omega
    · rw [hmem]; native_decide
  have herr1Read : err1.readWithPadding 64 32 = UInt256.toByteArray ⟨576⟩ := by
    unfold err1 frobErrorStringMem1
    change (writeWordMem 580 (⟨32⟩ : UInt256) err0).readWithPadding 64 32 =
      UInt256.toByteArray ⟨576⟩
    rw [writeWordMem_read64_below]
    · exact herr0Read
    · rw [herr0Size]; omega
    · omega
    · rw [herr0Size]; native_decide
  have herr2Read : err2.readWithPadding 64 32 = UInt256.toByteArray ⟨576⟩ := by
    unfold err2 frobErrorStringMem2
    change (writeWordMem 612 len err1).readWithPadding 64 32 =
      UInt256.toByteArray ⟨576⟩
    rw [writeWordMem_read64_below]
    · exact herr1Read
    · rw [herr1Size]; omega
    · omega
    · rw [herr1Size]; native_decide
  unfold frobErrorStringMem3
  change (writeWordMem 644 word err2).readWithPadding 64 32 =
    UInt256.toByteArray ⟨576⟩
  rw [writeWordMem_read64_below]
  · exact herr2Read
  · rw [herr2Size]; omega
  · omega
  · rw [herr2Size]; native_decide

set_option maxHeartbeats 1000000 in
theorem RD.solcErrorStringRevertTail576 {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {pc len rawWord shift word : UInt256}
    {op : Operation.POp} {width : ℕ}
    {stk : List UInt256} {mem rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD code ee g s0 pc stk mem (UInt256.ofNat 18) rdata acc k C)
    (hwf : solcErrorStringRevertTailWf code pc len rawWord shift op width)
    (hpush : op ≠ .PUSH0)
    (hword : UInt256.shiftLeft rawWord shift = word)
    (hmem : mem.size = 576)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨576⟩)
    (hov : stk.length + 5 ≤ 1024) :
    RDrev code g s0 := by
  rcases hwf with
    ⟨hd0, hd2, hd3, hd4, hd8, hd10, hd11, hd12, hd13, hd15, hd17, hd18,
      hd19, hd20, hd22, hd24, hd25, hd26, hd27, hdRawOut, hdShl, hd68,
      hdDup3, hdAdd, hdMstore3, hdSwap, hdMload, hdSwap2, hdDup2, hdSwap3,
      hdSub, hd100, hdAdd2, hdSwap4, hdRev⟩
  have rd3199 := h.push1 ⟨64⟩ hd0 (by evm_ov)
  have rd3200 := rd3199.dup1 hd2 (by evm_ov)
  have hmload576 :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 18 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
          (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨576⟩ := by
    exact mloadWordValue_of_readWithPadding
      (by rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide, hmem]; omega)
      (by native_decide)
      (by simpa [show (⟨64⟩ : UInt256).toNat = 64 from by decide] using hread64)
  have rd3201 := rd3200.mload 0 ⟨576⟩ (UInt256.ofNat 18)
    hd3 mem_cost hmload576 (by native_decide) (by evm_ov)
  have rd3205 := rd3201.pushConst (⟨4594637⟩ : UInt256)
    (width := 3) (op := .PUSH3) (by decide) hd4 (by simp only [List.length_cons]; omega)
  have rd3207 := rd3205.push1 ⟨229⟩ hd8 (by evm_ov)
  have rd3208 := rd3207.shl hd10 (by evm_ov)
  have rd3209 := rd3208.dup2 hd11 (by evm_ov)
  have rd3210 := rd3209.mstore 3 (frobErrorStringMem0 mem)
    (UInt256.ofNat 19) hd12 mem_cost
    (by rw [show (⟨576⟩ : UInt256).toNat = 576 from by native_decide]
        simp [frobErrorStringMem0, writeWordMem, solcErrorStringSelector])
    (by native_decide) (by evm_ov)
  have rd3212 := rd3210.push1 ⟨32⟩ hd13 (by evm_ov)
  have rd3214 := rd3212.push1 ⟨4⟩ hd15 (by evm_ov)
  have rd3215 := rd3214.dup3 hd17 (by evm_ov)
  have rd3216 := rd3215.add hd18 (by evm_ov)
  have rd3217 := rd3216.mstore 3 (frobErrorStringMem1 mem)
    (UInt256.ofNat 20) hd19 mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd3219 := rd3217.push1 len hd20 (by evm_ov)
  have rd3221 := rd3219.push1 ⟨36⟩ hd22 (by evm_ov)
  have rd3222 := rd3221.dup3 hd24 (by evm_ov)
  have rd3223 := rd3222.add hd25 (by evm_ov)
  have rd3224 := rd3223.mstore 3 (frobErrorStringMem2 len mem)
    (UInt256.ofNat 21) hd26 mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rdRaw := rd3224.pushConst rawWord
    (width := width) (op := op) hpush hd27 (by simp only [List.length_cons]; omega)
  have rdShift := rdRaw.push1 shift hdRawOut (by evm_ov)
  have rdWordRaw := rdShift.shl hdShl (by evm_ov)
  have rdWord := rdWordRaw
  rw [hword] at rdWord
  have rd3246 := rdWord.push1 ⟨68⟩ hd68 (by evm_ov)
  have rd3247 := rd3246.dup3 hdDup3 (by evm_ov)
  have rd3248 := rd3247.add hdAdd (by evm_ov)
  have rd3249 := rd3248.mstore 3 (frobErrorStringMem3 len word mem)
    (UInt256.ofNat 22) hdMstore3 mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd3250 := rd3249.swap1 hdSwap (by evm_ov)
  have herrMload64 :
    (if (⟨64⟩ : UInt256).toNat ≥ (frobErrorStringMem3 len word mem).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 22 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((frobErrorStringMem3 len word mem).readWithPadding
          (⟨64⟩ : UInt256).toNat 32))) =
      ⟨576⟩ := by
    exact mloadWordValue_of_readWithPadding
      (by
        rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide,
          frobErrorStringMem3_size len word hmem]
        omega)
      (by native_decide)
      (by
        simpa [show (⟨64⟩ : UInt256).toNat = 64 from by decide] using
          frobErrorStringMem3_read64 len word hmem hread64)
  have rd3251 := rd3250.mload 0 ⟨576⟩ (UInt256.ofNat 22)
    hdMload mem_cost herrMload64 (by native_decide) (by evm_ov)
  have rd3252 := rd3251.swap1 hdSwap2 (by evm_ov)
  have rd3253 := rd3252.dup2 hdDup2 (by evm_ov)
  have rd3254 := rd3253.swap1 hdSwap3 (by evm_ov)
  have rd3255 := rd3254.sub hdSub (by evm_ov)
  have rd3257 := rd3255.push1 ⟨100⟩ hd100 (by evm_ov)
  have rd3258 := rd3257.add hdAdd2 (by evm_ov)
  have rd3259 := rd3258.swap1 hdSwap4 (by evm_ov)
  exact rd3259.rev 0 hdRev mem_cost (by evm_ov)

theorem vatFrobUWishNotAllowedTailWf :
    solcErrorStringRevertTailWf vatBytecode ⟨3641⟩ ⟨17⟩
      ⟨29393821939250277271513265368272845679989⟩ ⟨120⟩ .PUSH17 17 := by
  unfold solcErrorStringRevertTailWf
  repeat' first | apply And.intro | native_decide

set_option maxHeartbeats 1000000 in
theorem RD.vatFrobIlkLoadsRateZero
    {cA gh bl σ σ₀ A I} {g : Sat256} {k C : ℕ} {sel : UInt256}
    (h : RD vatBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3119⟩
      [⟨192⟩, frobDartWord I, frobDinkWord I, frobWMaskedWord I,
        frobVMaskedWord I, frobUMaskedWord I, frobIWord I, ⟨524⟩, sel]
      (frobAlloc5Mem (frobUrnLoadedMem σ I)) (UInt256.ofNat 13)
      ByteArray.empty (cA, σ) k C)
    (hrateZero : solcSlotWord σ I (frobIlkRateSlot I) = ⟨0⟩) :
    RDrev vatBytecode g (initState cA gh bl σ σ₀ g A I) := by
  let ilkBase := solcMappingSlot ⟨2⟩ (frobIWord I)
  let ilkArtOld := solcSlotWord σ I ilkBase
  let ilkRateOld := solcSlotWord σ I (ilkBase + ⟨1⟩)
  let ilkSpotOld := solcSlotWord σ I (ilkBase + ⟨2⟩)
  let ilkLineOld := solcSlotWord σ I (ilkBase + ⟨3⟩)
  let ilkDustOld := solcSlotWord σ I (ilkBase + ⟨4⟩)
  have rd3121 := h.push1 ⟨0⟩ (by native_decide) (by evm_ov)
  have rd3122 := rd3121.dup8 (by native_decide) (by evm_ov)
  have rd3123pre := rd3122.dup2 (by native_decide) (by evm_ov)
  have rd3124 := rd3123pre.mstore 0
    (wordAt0Mem (frobIWord I) (frobAlloc5Mem (frobUrnLoadedMem σ I)))
    (UInt256.ofNat 13) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd3126 := rd3124.push1 ⟨2⟩ (by native_decide) (by evm_ov)
  have rd3128 := rd3126.push1 ⟨32⟩ (by native_decide) (by evm_ov)
  have rd3129 := rd3128.dup2 (by native_decide) (by evm_ov)
  have rd3130pre := rd3129.dup2 (by native_decide) (by evm_ov)
  have rd3131 := rd3130pre.mstore 0 (frobIlkHashMem σ I)
    (UInt256.ofNat 13) (by native_decide) mem_cost
    (by
      rw [show (⟨32⟩ : UInt256).toNat = 32 from by native_decide]
      simp [frobIlkHashMem, twoWordHashMem, wordAt32Mem])
    (by native_decide) (by evm_ov)
  have rd3133 := rd3131.push1 ⟨64⟩ (by native_decide) (by evm_ov)
  have rd3134 := rd3133.swap3 (by native_decide) (by evm_ov)
  have rd3135 := rd3134.dup4 (by native_decide) (by evm_ov)
  have rd3136pre := rd3135.swap1 (by native_decide) (by evm_ov)
  have hilkBase :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((frobIlkHashMem σ I).readWithPadding 0 64))) = ilkBase := by
    simpa [frobIlkHashMem, ilkBase] using
      twoWordHashMem_solcMappingSlot_of_ge64 ⟨2⟩ (frobIWord I)
        (by rw [frobAlloc5Mem_frobUrnLoaded_size σ I]; omega)
  have rd3137 := rd3136pre.keccak256 0 ilkBase (UInt256.ofNat 13)
    (by native_decide) mem_cost hilkBase (by native_decide) (by evm_ov)
  have rd3138pre := rd3137.dup4 (by native_decide) (by evm_ov)
  have hmload416 :
      (if (⟨64⟩ : UInt256).toNat ≥ (frobIlkHashMem σ I).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 13 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
          ((frobIlkHashMem σ I).readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨416⟩ := by
    exact mloadWordValue_of_readWithPadding
      (by rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide,
        frobIlkHashMem_size σ I]; omega)
      (by native_decide)
      (by simpa [show (⟨64⟩ : UInt256).toNat = 64 from by decide]
        using frobIlkHashMem_read64 σ I)
  have rd3139 := rd3138pre.mload 0 ⟨416⟩ (UInt256.ofNat 13)
    (by native_decide) mem_cost hmload416 (by native_decide) (by evm_ov)
  have rd3141 := rd3139.push1 ⟨160⟩ (by native_decide) (by evm_ov)
  have rd3142 := rd3141.dup2 (by native_decide) (by evm_ov)
  have rd3143 := rd3142.add (by native_decide) (by evm_ov)
  have rd3144pre := rd3143.dup6 (by native_decide) (by evm_ov)
  have rd3145 := rd3144pre.mstore 0
    (writeWordMem 64 ⟨576⟩ (frobIlkHashMem σ I))
    (UInt256.ofNat 13) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd3146pre := rd3145.dup2 (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd3147raw⟩ := rd3146pre.sload (by native_decide) (by evm_ov)
  have hArtRaw :
      (σ.find? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD ilkBase ⟨0⟩)) = ilkArtOld := by
    simp [ilkArtOld, solcSlotWord]
  have rd3147 := rd3147raw
  rw [hArtRaw] at rd3147
  have rd3148pre := rd3147.dup2 (by native_decide) (by evm_ov)
  have rd3149 := rd3148pre.mstore 3
    (writeWordMem 416 ilkArtOld (writeWordMem 64 ⟨576⟩ (frobIlkHashMem σ I)))
    (UInt256.ofNat 14) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd3151 := rd3149.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  have rd3152 := rd3151.dup3 (by native_decide) (by evm_ov)
  have rd3153pre := rd3152.add (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd3154raw⟩ := rd3153pre.sload (by native_decide) (by evm_ov)
  have hRateRaw :
      (σ.find? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD (ilkBase + ⟨1⟩) ⟨0⟩)) = ilkRateOld := by
    simp [ilkRateOld, solcSlotWord]
  have rd3154 := rd3154raw
  rw [hRateRaw] at rd3154
  have rd3155 := rd3154.swap3 (by native_decide) (by evm_ov)
  have rd3156 := rd3155.dup2 (by native_decide) (by evm_ov)
  have rd3157 := rd3156.add (by native_decide) (by evm_ov)
  have rd3158 := rd3157.dup4 (by native_decide) (by evm_ov)
  have rd3159pre := rd3158.swap1 (by native_decide) (by evm_ov)
  have rd3160 := rd3159pre.mstore 3
    (writeWordMem 448 ilkRateOld
      (writeWordMem 416 ilkArtOld (writeWordMem 64 ⟨576⟩ (frobIlkHashMem σ I))))
    (UInt256.ofNat 15) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd3161 := rd3160.swap3 (by native_decide) (by evm_ov)
  have rd3162 := rd3161.dup2 (by native_decide) (by evm_ov)
  have rd3163pre := rd3162.add (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd3164raw⟩ := rd3163pre.sload (by native_decide) (by evm_ov)
  have hSpotRaw :
      (σ.find? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD (ilkBase + ⟨2⟩) ⟨0⟩)) = ilkSpotOld := by
    simp [ilkSpotOld, solcSlotWord]
  have rd3164 := rd3164raw
  rw [hSpotRaw] at rd3164
  have rd3165 := rd3164.swap4 (by native_decide) (by evm_ov)
  have rd3166 := rd3165.dup4 (by native_decide) (by evm_ov)
  have rd3167 := rd3166.add (by native_decide) (by evm_ov)
  have rd3168 := rd3167.swap4 (by native_decide) (by evm_ov)
  have rd3169 := rd3168.swap1 (by native_decide) (by evm_ov)
  have rd3170pre := rd3169.swap4 (by native_decide) (by evm_ov)
  have rd3171 := rd3170pre.mstore 3
    (writeWordMem 480 ilkSpotOld
      (writeWordMem 448 ilkRateOld
        (writeWordMem 416 ilkArtOld (writeWordMem 64 ⟨576⟩ (frobIlkHashMem σ I)))))
    (UInt256.ofNat 16) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd3173 := rd3171.push1 ⟨3⟩ (by native_decide) (by evm_ov)
  have rd3174 := rd3173.dup4 (by native_decide) (by evm_ov)
  have rd3175pre := rd3174.add (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd3176raw⟩ := rd3175pre.sload (by native_decide) (by evm_ov)
  have hLineRaw :
      (σ.find? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD (ilkBase + ⟨3⟩) ⟨0⟩)) = ilkLineOld := by
    simp [ilkLineOld, solcSlotWord]
  have rd3176 := rd3176raw
  rw [hLineRaw] at rd3176
  have rd3178 := rd3176.push1 ⟨96⟩ (by native_decide) (by evm_ov)
  have rd3179 := rd3178.dup4 (by native_decide) (by evm_ov)
  have rd3180pre := rd3179.add (by native_decide) (by evm_ov)
  have rd3181 := rd3180pre.mstore 3
    (writeWordMem 512 ilkLineOld
      (writeWordMem 480 ilkSpotOld
        (writeWordMem 448 ilkRateOld
          (writeWordMem 416 ilkArtOld (writeWordMem 64 ⟨576⟩ (frobIlkHashMem σ I))))))
    (UInt256.ofNat 17) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd3183 := rd3181.push1 ⟨4⟩ (by native_decide) (by evm_ov)
  have rd3184 := rd3183.swap1 (by native_decide) (by evm_ov)
  have rd3185 := rd3184.swap3 (by native_decide) (by evm_ov)
  have rd3186pre := rd3185.add (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd3187raw⟩ := rd3186pre.sload (by native_decide) (by evm_ov)
  have hDustRaw :
      (σ.find? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD (ilkBase + ⟨4⟩) ⟨0⟩)) = ilkDustOld := by
    simp [ilkDustOld, solcSlotWord]
  have rd3187 := rd3187raw
  rw [hDustRaw] at rd3187
  have rd3189 := rd3187.push1 ⟨128⟩ (by native_decide) (by evm_ov)
  have rd3190 := rd3189.dup3 (by native_decide) (by evm_ov)
  have rd3191pre := rd3190.add (by native_decide) (by evm_ov)
  have rd3192 := rd3191pre.mstore 3 (frobIlkLoadedMem σ I)
    (UInt256.ofNat 18) (by native_decide) mem_cost
    (by
      rw [show ((⟨416⟩ : UInt256) + ⟨128⟩).toNat = 544 from by native_decide]
      simp [writeWordMem, frobIlkLoadedMem, ilkArtOld, ilkRateOld, ilkSpotOld,
        ilkLineOld, ilkDustOld, frobIlkArtSlot, frobIlkRateSlot, frobIlkSpotSlot,
        frobIlkLineSlot, frobIlkDustSlot, frobIlkBase, ilkBase])
    (by native_decide) (by evm_ov)
  have rd3193 := rd3192.swap1 (by native_decide) (by evm_ov)
  have rd3196 := rd3193.push2 ⟨3260⟩ (by native_decide) (by evm_ov)
  have hrateZero' : ilkRateOld = ⟨0⟩ := by
    simpa [ilkRateOld, frobIlkRateSlot, frobIlkBase, ilkBase] using hrateZero
  have rd3197pre := rd3196
  rw [hrateZero'] at rd3197pre
  have rd3197 := rd3197pre.jumpiNT (by native_decide)
    (by decide : (⟨0⟩ : UInt256) = ⟨0⟩) (by evm_ov)
  have rd3199 := rd3197.push1 ⟨64⟩ (by native_decide) (by evm_ov)
  have rd3200 := rd3199.dup1 (by native_decide) (by evm_ov)
  have hmload576 :
      (if (⟨64⟩ : UInt256).toNat ≥ (frobIlkLoadedMem σ I).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 18 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
          ((frobIlkLoadedMem σ I).readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨576⟩ := by
    exact mloadWordValue_of_readWithPadding
      (by rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide,
        frobIlkLoadedMem_size σ I]; omega)
      (by native_decide)
      (by simpa [show (⟨64⟩ : UInt256).toNat = 64 from by decide]
        using frobIlkLoadedMem_read64 σ I)
  have rd3201 := rd3200.mload 0 ⟨576⟩ (UInt256.ofNat 18)
    (by native_decide) mem_cost hmload576 (by native_decide) (by evm_ov)
  have rd3205 := rd3201.pushConst (⟨4594637⟩ : UInt256)
    (width := 3) (op := .PUSH3) (by decide) (by native_decide) (by evm_ov)
  have rd3207 := rd3205.push1 ⟨229⟩ (by native_decide) (by evm_ov)
  have rd3208 := rd3207.shl (by native_decide) (by evm_ov)
  have rd3209 := rd3208.dup2 (by native_decide) (by evm_ov)
  have rd3210 := rd3209.mstore 3 (frobNotInitErrorMem0 (frobIlkLoadedMem σ I))
    (UInt256.ofNat 19) (by native_decide) mem_cost
    (by rw [show (⟨576⟩ : UInt256).toNat = 576 from by native_decide]
        simp [frobNotInitErrorMem0, writeWordMem, solcErrorStringSelector])
    (by native_decide) (by evm_ov)
  have rd3212 := rd3210.push1 ⟨32⟩ (by native_decide) (by evm_ov)
  have rd3214 := rd3212.push1 ⟨4⟩ (by native_decide) (by evm_ov)
  have rd3215 := rd3214.dup3 (by native_decide) (by evm_ov)
  have rd3216 := rd3215.add (by native_decide) (by evm_ov)
  have rd3217 := rd3216.mstore 3 (frobNotInitErrorMem1 (frobIlkLoadedMem σ I))
    (UInt256.ofNat 20) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd3219 := rd3217.push1 ⟨16⟩ (by native_decide) (by evm_ov)
  have rd3221 := rd3219.push1 ⟨36⟩ (by native_decide) (by evm_ov)
  have rd3222 := rd3221.dup3 (by native_decide) (by evm_ov)
  have rd3223 := rd3222.add (by native_decide) (by evm_ov)
  have rd3224 := rd3223.mstore 3 (frobNotInitErrorMem2 (frobIlkLoadedMem σ I))
    (UInt256.ofNat 21) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd3241 := rd3224.pushConst vatNotInitRawWord
    (width := 16) (op := .PUSH16) (by decide) (by native_decide) (by evm_ov)
  have rd3243 := rd3241.push1 ⟨130⟩ (by native_decide) (by evm_ov)
  have rd3244raw := rd3243.shl (by native_decide) (by evm_ov)
  have rd3244 := rd3244raw
  rw [show UInt256.shiftLeft vatNotInitRawWord ⟨130⟩ =
    UInt256.shiftLeft vatNotInitRawWord ⟨130⟩ from rfl] at rd3244
  have rd3246 := rd3244.push1 ⟨68⟩ (by native_decide) (by evm_ov)
  have rd3247 := rd3246.dup3 (by native_decide) (by evm_ov)
  have rd3248 := rd3247.add (by native_decide) (by evm_ov)
  have rd3249 := rd3248.mstore 3 (frobNotInitErrorMem3 (frobIlkLoadedMem σ I))
    (UInt256.ofNat 22) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd3250 := rd3249.swap1 (by native_decide) (by evm_ov)
  have herrMload64 :
    (if (⟨64⟩ : UInt256).toNat ≥
        (frobNotInitErrorMem3 (frobIlkLoadedMem σ I)).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 22 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((frobNotInitErrorMem3 (frobIlkLoadedMem σ I)).readWithPadding
          (⟨64⟩ : UInt256).toNat 32))) =
      ⟨576⟩ := by
    exact mloadWordValue_of_readWithPadding
      (by
        rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide,
          frobNotInitErrorMem3_size (frobIlkLoadedMem_size σ I)]
        omega)
      (by native_decide)
      (by
        simpa [show (⟨64⟩ : UInt256).toNat = 64 from by decide] using
          frobNotInitErrorMem3_read64 (frobIlkLoadedMem_size σ I)
          (frobIlkLoadedMem_read64 σ I))
  have rd3251 := rd3250.mload 0 ⟨576⟩ (UInt256.ofNat 22)
    (by native_decide) mem_cost herrMload64 (by native_decide) (by evm_ov)
  have rd3252 := rd3251.swap1 (by native_decide) (by evm_ov)
  have rd3253 := rd3252.dup2 (by native_decide) (by evm_ov)
  have rd3254 := rd3253.swap1 (by native_decide) (by evm_ov)
  have rd3255 := rd3254.sub (by native_decide) (by evm_ov)
  have rd3257 := rd3255.push1 ⟨100⟩ (by native_decide) (by evm_ov)
  have rd3258 := rd3257.add (by native_decide) (by evm_ov)
  have rd3259 := rd3258.swap1 (by native_decide) (by evm_ov)
  exact rd3259.rev 0 (by native_decide) mem_cost (by evm_ov)

set_option maxHeartbeats 1000000 in
theorem RD.vatFrobIlkLoadsRateNonzero
    {cA gh bl σ σ₀ A I} {g : Sat256} {k C : ℕ} {sel : UInt256}
    (h : RD vatBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3119⟩
      [⟨192⟩, frobDartWord I, frobDinkWord I, frobWMaskedWord I,
        frobVMaskedWord I, frobUMaskedWord I, frobIWord I, ⟨524⟩, sel]
      (frobAlloc5Mem (frobUrnLoadedMem σ I)) (UInt256.ofNat 13)
      ByteArray.empty (cA, σ) k C)
    (hrateNonzero : solcSlotWord σ I (frobIlkRateSlot I) ≠ ⟨0⟩) :
    ∃ k' C',
      RD vatBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3260⟩
        [⟨416⟩, ⟨192⟩, frobDartWord I, frobDinkWord I, frobWMaskedWord I,
          frobVMaskedWord I, frobUMaskedWord I, frobIWord I, ⟨524⟩, sel]
        (frobIlkLoadedMem σ I) (UInt256.ofNat 18) ByteArray.empty (cA, σ) k' C' := by
  let ilkBase := solcMappingSlot ⟨2⟩ (frobIWord I)
  let ilkArtOld := solcSlotWord σ I ilkBase
  let ilkRateOld := solcSlotWord σ I (ilkBase + ⟨1⟩)
  let ilkSpotOld := solcSlotWord σ I (ilkBase + ⟨2⟩)
  let ilkLineOld := solcSlotWord σ I (ilkBase + ⟨3⟩)
  let ilkDustOld := solcSlotWord σ I (ilkBase + ⟨4⟩)
  have rd3121 := h.push1 ⟨0⟩ (by native_decide) (by evm_ov)
  have rd3122 := rd3121.dup8 (by native_decide) (by evm_ov)
  have rd3123pre := rd3122.dup2 (by native_decide) (by evm_ov)
  have rd3124 := rd3123pre.mstore 0
    (wordAt0Mem (frobIWord I) (frobAlloc5Mem (frobUrnLoadedMem σ I)))
    (UInt256.ofNat 13) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd3126 := rd3124.push1 ⟨2⟩ (by native_decide) (by evm_ov)
  have rd3128 := rd3126.push1 ⟨32⟩ (by native_decide) (by evm_ov)
  have rd3129 := rd3128.dup2 (by native_decide) (by evm_ov)
  have rd3130pre := rd3129.dup2 (by native_decide) (by evm_ov)
  have rd3131 := rd3130pre.mstore 0 (frobIlkHashMem σ I)
    (UInt256.ofNat 13) (by native_decide) mem_cost
    (by
      rw [show (⟨32⟩ : UInt256).toNat = 32 from by native_decide]
      simp [frobIlkHashMem, twoWordHashMem, wordAt32Mem])
    (by native_decide) (by evm_ov)
  have rd3133 := rd3131.push1 ⟨64⟩ (by native_decide) (by evm_ov)
  have rd3134 := rd3133.swap3 (by native_decide) (by evm_ov)
  have rd3135 := rd3134.dup4 (by native_decide) (by evm_ov)
  have rd3136pre := rd3135.swap1 (by native_decide) (by evm_ov)
  have hilkBase :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((frobIlkHashMem σ I).readWithPadding 0 64))) = ilkBase := by
    simpa [frobIlkHashMem, ilkBase] using
      twoWordHashMem_solcMappingSlot_of_ge64 ⟨2⟩ (frobIWord I)
        (by rw [frobAlloc5Mem_frobUrnLoaded_size σ I]; omega)
  have rd3137 := rd3136pre.keccak256 0 ilkBase (UInt256.ofNat 13)
    (by native_decide) mem_cost hilkBase (by native_decide) (by evm_ov)
  have rd3138pre := rd3137.dup4 (by native_decide) (by evm_ov)
  have hmload416 :
      (if (⟨64⟩ : UInt256).toNat ≥ (frobIlkHashMem σ I).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 13 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
          ((frobIlkHashMem σ I).readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨416⟩ := by
    exact mloadWordValue_of_readWithPadding
      (by rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide,
        frobIlkHashMem_size σ I]; omega)
      (by native_decide)
      (by simpa [show (⟨64⟩ : UInt256).toNat = 64 from by decide]
        using frobIlkHashMem_read64 σ I)
  have rd3139 := rd3138pre.mload 0 ⟨416⟩ (UInt256.ofNat 13)
    (by native_decide) mem_cost hmload416 (by native_decide) (by evm_ov)
  have rd3141 := rd3139.push1 ⟨160⟩ (by native_decide) (by evm_ov)
  have rd3142 := rd3141.dup2 (by native_decide) (by evm_ov)
  have rd3143 := rd3142.add (by native_decide) (by evm_ov)
  have rd3144pre := rd3143.dup6 (by native_decide) (by evm_ov)
  have rd3145 := rd3144pre.mstore 0
    (writeWordMem 64 ⟨576⟩ (frobIlkHashMem σ I))
    (UInt256.ofNat 13) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd3146pre := rd3145.dup2 (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd3147raw⟩ := rd3146pre.sload (by native_decide) (by evm_ov)
  have hArtRaw :
      (σ.find? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD ilkBase ⟨0⟩)) = ilkArtOld := by
    simp [ilkArtOld, solcSlotWord]
  have rd3147 := rd3147raw
  rw [hArtRaw] at rd3147
  have rd3148pre := rd3147.dup2 (by native_decide) (by evm_ov)
  have rd3149 := rd3148pre.mstore 3
    (writeWordMem 416 ilkArtOld (writeWordMem 64 ⟨576⟩ (frobIlkHashMem σ I)))
    (UInt256.ofNat 14) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd3151 := rd3149.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  have rd3152 := rd3151.dup3 (by native_decide) (by evm_ov)
  have rd3153pre := rd3152.add (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd3154raw⟩ := rd3153pre.sload (by native_decide) (by evm_ov)
  have hRateRaw :
      (σ.find? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD (ilkBase + ⟨1⟩) ⟨0⟩)) = ilkRateOld := by
    simp [ilkRateOld, solcSlotWord]
  have rd3154 := rd3154raw
  rw [hRateRaw] at rd3154
  have rd3155 := rd3154.swap3 (by native_decide) (by evm_ov)
  have rd3156 := rd3155.dup2 (by native_decide) (by evm_ov)
  have rd3157 := rd3156.add (by native_decide) (by evm_ov)
  have rd3158 := rd3157.dup4 (by native_decide) (by evm_ov)
  have rd3159pre := rd3158.swap1 (by native_decide) (by evm_ov)
  have rd3160 := rd3159pre.mstore 3
    (writeWordMem 448 ilkRateOld
      (writeWordMem 416 ilkArtOld (writeWordMem 64 ⟨576⟩ (frobIlkHashMem σ I))))
    (UInt256.ofNat 15) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd3161 := rd3160.swap3 (by native_decide) (by evm_ov)
  have rd3162 := rd3161.dup2 (by native_decide) (by evm_ov)
  have rd3163pre := rd3162.add (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd3164raw⟩ := rd3163pre.sload (by native_decide) (by evm_ov)
  have hSpotRaw :
      (σ.find? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD (ilkBase + ⟨2⟩) ⟨0⟩)) = ilkSpotOld := by
    simp [ilkSpotOld, solcSlotWord]
  have rd3164 := rd3164raw
  rw [hSpotRaw] at rd3164
  have rd3165 := rd3164.swap4 (by native_decide) (by evm_ov)
  have rd3166 := rd3165.dup4 (by native_decide) (by evm_ov)
  have rd3167 := rd3166.add (by native_decide) (by evm_ov)
  have rd3168 := rd3167.swap4 (by native_decide) (by evm_ov)
  have rd3169 := rd3168.swap1 (by native_decide) (by evm_ov)
  have rd3170pre := rd3169.swap4 (by native_decide) (by evm_ov)
  have rd3171 := rd3170pre.mstore 3
    (writeWordMem 480 ilkSpotOld
      (writeWordMem 448 ilkRateOld
        (writeWordMem 416 ilkArtOld (writeWordMem 64 ⟨576⟩ (frobIlkHashMem σ I)))))
    (UInt256.ofNat 16) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd3173 := rd3171.push1 ⟨3⟩ (by native_decide) (by evm_ov)
  have rd3174 := rd3173.dup4 (by native_decide) (by evm_ov)
  have rd3175pre := rd3174.add (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd3176raw⟩ := rd3175pre.sload (by native_decide) (by evm_ov)
  have hLineRaw :
      (σ.find? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD (ilkBase + ⟨3⟩) ⟨0⟩)) = ilkLineOld := by
    simp [ilkLineOld, solcSlotWord]
  have rd3176 := rd3176raw
  rw [hLineRaw] at rd3176
  have rd3178 := rd3176.push1 ⟨96⟩ (by native_decide) (by evm_ov)
  have rd3179 := rd3178.dup4 (by native_decide) (by evm_ov)
  have rd3180pre := rd3179.add (by native_decide) (by evm_ov)
  have rd3181 := rd3180pre.mstore 3
    (writeWordMem 512 ilkLineOld
      (writeWordMem 480 ilkSpotOld
        (writeWordMem 448 ilkRateOld
          (writeWordMem 416 ilkArtOld (writeWordMem 64 ⟨576⟩ (frobIlkHashMem σ I))))))
    (UInt256.ofNat 17) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd3183 := rd3181.push1 ⟨4⟩ (by native_decide) (by evm_ov)
  have rd3184 := rd3183.swap1 (by native_decide) (by evm_ov)
  have rd3185 := rd3184.swap3 (by native_decide) (by evm_ov)
  have rd3186pre := rd3185.add (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd3187raw⟩ := rd3186pre.sload (by native_decide) (by evm_ov)
  have hDustRaw :
      (σ.find? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD (ilkBase + ⟨4⟩) ⟨0⟩)) = ilkDustOld := by
    simp [ilkDustOld, solcSlotWord]
  have rd3187 := rd3187raw
  rw [hDustRaw] at rd3187
  have rd3189 := rd3187.push1 ⟨128⟩ (by native_decide) (by evm_ov)
  have rd3190 := rd3189.dup3 (by native_decide) (by evm_ov)
  have rd3191pre := rd3190.add (by native_decide) (by evm_ov)
  have rd3192 := rd3191pre.mstore 3 (frobIlkLoadedMem σ I)
    (UInt256.ofNat 18) (by native_decide) mem_cost
    (by
      rw [show ((⟨416⟩ : UInt256) + ⟨128⟩).toNat = 544 from by native_decide]
      simp [writeWordMem, frobIlkLoadedMem, ilkArtOld, ilkRateOld, ilkSpotOld,
        ilkLineOld, ilkDustOld, frobIlkArtSlot, frobIlkRateSlot, frobIlkSpotSlot,
        frobIlkLineSlot, frobIlkDustSlot, frobIlkBase, ilkBase])
    (by native_decide) (by evm_ov)
  have rd3193 := rd3192.swap1 (by native_decide) (by evm_ov)
  have rd3196 := rd3193.push2 ⟨3260⟩ (by native_decide) (by evm_ov)
  have hrateNonzero' : ilkRateOld ≠ ⟨0⟩ := by
    intro hzero
    apply hrateNonzero
    simpa [ilkRateOld, frobIlkRateSlot, frobIlkBase, ilkBase] using hzero
  have rd3260 := rd3196.jumpiT (by native_decide) hrateNonzero' (by jump_dest)
    (by evm_ov)
  exact ⟨_, _, by
    simpa [ilkBase, ilkRateOld, frobIlkRateSlot, frobIlkBase] using rd3260⟩

theorem RD.vatFrobUrnInkAddSuccess
    {cA gh bl σ σ₀ A I} {g : Sat256} {k C : ℕ} {sel : UInt256}
    (h : RD vatBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3260⟩
      [⟨416⟩, ⟨192⟩, frobDartWord I, frobDinkWord I, frobWMaskedWord I,
        frobVMaskedWord I, frobUMaskedWord I, frobIWord I, ⟨524⟩, sel]
      (frobIlkLoadedMem σ I) (UInt256.ofNat 18) ByteArray.empty (cA, σ) k C)
    (hneg :
      UInt256.slt (frobDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.gt (frobDinkWord I + solcSlotWord σ I (frobUrnInkSlot I))
          (solcSlotWord σ I (frobUrnInkSlot I)) = ⟨0⟩)
    (hpos :
      UInt256.sgt (frobDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.lt (frobDinkWord I + solcSlotWord σ I (frobUrnInkSlot I))
          (solcSlotWord σ I (frobUrnInkSlot I)) = ⟨0⟩) :
    ∃ k' C',
      RD vatBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3272⟩
        [frobDinkWord I + solcSlotWord σ I (frobUrnInkSlot I), ⟨416⟩, ⟨192⟩,
          frobDartWord I, frobDinkWord I, frobWMaskedWord I, frobVMaskedWord I,
          frobUMaskedWord I, frobIWord I, ⟨524⟩, sel]
        (frobIlkLoadedMem σ I) (UInt256.ofNat 18) ByteArray.empty (cA, σ) k' C' := by
  let urnInkOld := solcSlotWord σ I (frobUrnInkSlot I)
  have rd3261 := h.jumpdest (by native_decide) (by evm_ov)
  have rd3262pre := rd3261.dup2 (by native_decide) (by evm_ov)
  have hmload192 :
      (if (⟨192⟩ : UInt256).toNat ≥ (frobIlkLoadedMem σ I).size
          ∨ (⟨192⟩ : UInt256) ≥ UInt256.ofNat 18 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
          ((frobIlkLoadedMem σ I).readWithPadding (⟨192⟩ : UInt256).toNat 32))) =
        urnInkOld := by
    exact mloadWordValue_of_readWithPadding
      (by rw [show (⟨192⟩ : UInt256).toNat = 192 from by decide,
        frobIlkLoadedMem_size σ I]; omega)
      (by native_decide)
      (by
        simpa [show (⟨192⟩ : UInt256).toNat = 192 from by decide, urnInkOld]
          using frobIlkLoadedMem_read192 σ I)
  have rd3263 := rd3262pre.mload 0 urnInkOld (UInt256.ofNat 18)
    (by native_decide) mem_cost hmload192 (by native_decide) (by evm_ov)
  have rd3266 := rd3263.push2 ⟨3272⟩ (by native_decide) (by evm_ov)
  have rd3267 := rd3266.swap1 (by native_decide) (by evm_ov)
  have rd3268 := rd3267.dup6 (by native_decide) (by evm_ov)
  have rd3271 := rd3268.push2 ⟨6653⟩ (by native_decide) (by evm_ov)
  have rd6653 := rd3271.jump (by native_decide) (by jump_dest) (by evm_ov)
  obtain ⟨_, _, rd3272⟩ := RD.vatSignedAddOk
    (x := urnInkOld) (y := frobDinkWord I) (ret := ⟨3272⟩)
    (R := (⟨416⟩ : UInt256) :: (⟨192⟩ : UInt256) :: frobDartWord I ::
      frobDinkWord I :: frobWMaskedWord I :: frobVMaskedWord I ::
      frobUMaskedWord I :: frobIWord I :: ⟨524⟩ :: sel :: [])
    rd6653
    (by simpa [urnInkOld] using hneg)
    (by simpa [urnInkOld] using hpos)
    (by jump_dest) (by simp)
  exact ⟨_, _, by simpa [urnInkOld] using rd3272⟩

theorem RD.vatFrobUrnInkAddRevert
    {cA gh bl σ σ₀ A I} {g : Sat256} {k C : ℕ} {sel : UInt256}
    (h : RD vatBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3260⟩
      [⟨416⟩, ⟨192⟩, frobDartWord I, frobDinkWord I, frobWMaskedWord I,
        frobVMaskedWord I, frobUMaskedWord I, frobIWord I, ⟨524⟩, sel]
      (frobIlkLoadedMem σ I) (UInt256.ofNat 18) ByteArray.empty (cA, σ) k C)
    (hfail :
      ¬ (UInt256.slt (frobDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.gt (frobDinkWord I + solcSlotWord σ I (frobUrnInkSlot I))
          (solcSlotWord σ I (frobUrnInkSlot I)) = ⟨0⟩) ∨
      (UInt256.slt (frobDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.gt (frobDinkWord I + solcSlotWord σ I (frobUrnInkSlot I))
          (solcSlotWord σ I (frobUrnInkSlot I)) = ⟨0⟩) ∧
        ¬ (UInt256.sgt (frobDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
          UInt256.lt (frobDinkWord I + solcSlotWord σ I (frobUrnInkSlot I))
            (solcSlotWord σ I (frobUrnInkSlot I)) = ⟨0⟩)) :
    RDrev vatBytecode g (initState cA gh bl σ σ₀ g A I) := by
  let urnInkOld := solcSlotWord σ I (frobUrnInkSlot I)
  have rd3261 := h.jumpdest (by native_decide) (by evm_ov)
  have rd3262pre := rd3261.dup2 (by native_decide) (by evm_ov)
  have hmload192 :
      (if (⟨192⟩ : UInt256).toNat ≥ (frobIlkLoadedMem σ I).size
          ∨ (⟨192⟩ : UInt256) ≥ UInt256.ofNat 18 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
          ((frobIlkLoadedMem σ I).readWithPadding (⟨192⟩ : UInt256).toNat 32))) =
        urnInkOld := by
    exact mloadWordValue_of_readWithPadding
      (by rw [show (⟨192⟩ : UInt256).toNat = 192 from by decide,
        frobIlkLoadedMem_size σ I]; omega)
      (by native_decide)
      (by
        simpa [show (⟨192⟩ : UInt256).toNat = 192 from by decide, urnInkOld]
          using frobIlkLoadedMem_read192 σ I)
  have rd3263 := rd3262pre.mload 0 urnInkOld (UInt256.ofNat 18)
    (by native_decide) mem_cost hmload192 (by native_decide) (by evm_ov)
  have rd3266 := rd3263.push2 ⟨3272⟩ (by native_decide) (by evm_ov)
  have rd3267 := rd3266.swap1 (by native_decide) (by evm_ov)
  have rd3268 := rd3267.dup6 (by native_decide) (by evm_ov)
  have rd3271 := rd3268.push2 ⟨6653⟩ (by native_decide) (by evm_ov)
  have rd6653 := rd3271.jump (by native_decide) (by jump_dest) (by evm_ov)
  exact RD.vatSignedAddRevert
    (x := urnInkOld) (y := frobDinkWord I) (ret := ⟨3272⟩)
    (R := (⟨416⟩ : UInt256) :: (⟨192⟩ : UInt256) :: frobDartWord I ::
      frobDinkWord I :: frobWMaskedWord I :: frobVMaskedWord I ::
      frobUMaskedWord I :: frobIWord I :: ⟨524⟩ :: sel :: [])
    rd6653
    (by simpa [urnInkOld] using hfail)
    (by simp)

theorem RD.vatFrobUrnArtAddSuccess
    {cA gh bl σ σ₀ A I} {g : Sat256} {k C : ℕ} {sel urnInkNew : UInt256}
    (h : RD vatBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3272⟩
      [urnInkNew, ⟨416⟩, ⟨192⟩, frobDartWord I, frobDinkWord I, frobWMaskedWord I,
        frobVMaskedWord I, frobUMaskedWord I, frobIWord I, ⟨524⟩, sel]
      (frobIlkLoadedMem σ I) (UInt256.ofNat 18) ByteArray.empty (cA, σ) k C)
    (hneg :
      UInt256.slt (frobDartWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.gt (frobDartWord I + solcSlotWord σ I (frobUrnArtSlot I))
          (solcSlotWord σ I (frobUrnArtSlot I)) = ⟨0⟩)
    (hpos :
      UInt256.sgt (frobDartWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.lt (frobDartWord I + solcSlotWord σ I (frobUrnArtSlot I))
          (solcSlotWord σ I (frobUrnArtSlot I)) = ⟨0⟩) :
    ∃ k' C',
      RD vatBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3289⟩
        [frobDartWord I + solcSlotWord σ I (frobUrnArtSlot I), ⟨416⟩, ⟨192⟩,
          frobDartWord I, frobDinkWord I, frobWMaskedWord I, frobVMaskedWord I,
          frobUMaskedWord I, frobIWord I, ⟨524⟩, sel]
        (frobUrnInkUpdatedMem σ I urnInkNew) (UInt256.ofNat 18)
        ByteArray.empty (cA, σ) k' C' := by
  let urnArtOld := solcSlotWord σ I (frobUrnArtSlot I)
  have rd3273 := h.jumpdest (by native_decide) (by evm_ov)
  have rd3274pre := rd3273.dup3 (by native_decide) (by evm_ov)
  have rd3275 := rd3274pre.mstore 0 (frobUrnInkUpdatedMem σ I urnInkNew)
    (UInt256.ofNat 18) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd3277 := rd3275.push1 ⟨32⟩ (by native_decide) (by evm_ov)
  have rd3278pre := rd3277.dup3 (by native_decide) (by evm_ov)
  have rd3279raw := rd3278pre.add (by native_decide) (by evm_ov)
  have hoff : (⟨192⟩ : UInt256) + ⟨32⟩ = ⟨224⟩ := by native_decide
  have hmload224 :
      (if ((⟨192⟩ : UInt256) + ⟨32⟩).toNat ≥
            (frobUrnInkUpdatedMem σ I urnInkNew).size
          ∨ ((⟨192⟩ : UInt256) + ⟨32⟩) ≥ UInt256.ofNat 18 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
          ((frobUrnInkUpdatedMem σ I urnInkNew).readWithPadding
            (((⟨192⟩ : UInt256) + ⟨32⟩).toNat) 32))) =
        urnArtOld := by
    rw [hoff]
    exact mloadWordValue_of_readWithPadding
      (by
        rw [show (⟨224⟩ : UInt256).toNat = 224 from by decide]
        unfold frobUrnInkUpdatedMem
        rw [writeWordMem_size_of_contains]
        · rw [frobIlkLoadedMem_size σ I]; omega
        · rw [frobIlkLoadedMem_size σ I]; omega)
      (by native_decide)
      (by
        simpa [show (⟨224⟩ : UInt256).toNat = 224 from by decide, urnArtOld]
          using frobUrnInkUpdatedMem_read224 σ I urnInkNew)
  have rd3280raw := rd3279raw.mload 0 urnArtOld (UInt256.ofNat 18)
    (by native_decide) mem_cost hmload224 (by native_decide) (by evm_ov)
  have rd3280 := by
    simpa [hoff] using rd3280raw
  have rd3283 := rd3280.push2 ⟨3289⟩ (by native_decide) (by evm_ov)
  have rd3284 := rd3283.swap1 (by native_decide) (by evm_ov)
  have rd3285 := rd3284.dup5 (by native_decide) (by evm_ov)
  have rd3288 := rd3285.push2 ⟨6653⟩ (by native_decide) (by evm_ov)
  have rd6653 := rd3288.jump (by native_decide) (by jump_dest) (by evm_ov)
  obtain ⟨_, _, rd3289⟩ := RD.vatSignedAddOk
    (x := urnArtOld) (y := frobDartWord I) (ret := ⟨3289⟩)
    (R := (⟨416⟩ : UInt256) :: (⟨192⟩ : UInt256) :: frobDartWord I ::
      frobDinkWord I :: frobWMaskedWord I :: frobVMaskedWord I ::
      frobUMaskedWord I :: frobIWord I :: ⟨524⟩ :: sel :: [])
    rd6653
    (by simpa [urnArtOld] using hneg)
    (by simpa [urnArtOld] using hpos)
    (by jump_dest) (by simp)
  exact ⟨_, _, by simpa [urnArtOld] using rd3289⟩

theorem RD.vatFrobUrnArtAddRevert
    {cA gh bl σ σ₀ A I} {g : Sat256} {k C : ℕ} {sel urnInkNew : UInt256}
    (h : RD vatBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3272⟩
      [urnInkNew, ⟨416⟩, ⟨192⟩, frobDartWord I, frobDinkWord I, frobWMaskedWord I,
        frobVMaskedWord I, frobUMaskedWord I, frobIWord I, ⟨524⟩, sel]
      (frobIlkLoadedMem σ I) (UInt256.ofNat 18) ByteArray.empty (cA, σ) k C)
    (hfail :
      ¬ (UInt256.slt (frobDartWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.gt (frobDartWord I + solcSlotWord σ I (frobUrnArtSlot I))
          (solcSlotWord σ I (frobUrnArtSlot I)) = ⟨0⟩) ∨
      (UInt256.slt (frobDartWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.gt (frobDartWord I + solcSlotWord σ I (frobUrnArtSlot I))
          (solcSlotWord σ I (frobUrnArtSlot I)) = ⟨0⟩) ∧
        ¬ (UInt256.sgt (frobDartWord I) ⟨0⟩ = ⟨0⟩ ∨
          UInt256.lt (frobDartWord I + solcSlotWord σ I (frobUrnArtSlot I))
            (solcSlotWord σ I (frobUrnArtSlot I)) = ⟨0⟩)) :
    RDrev vatBytecode g (initState cA gh bl σ σ₀ g A I) := by
  let urnArtOld := solcSlotWord σ I (frobUrnArtSlot I)
  have rd3273 := h.jumpdest (by native_decide) (by evm_ov)
  have rd3274pre := rd3273.dup3 (by native_decide) (by evm_ov)
  have rd3275 := rd3274pre.mstore 0 (frobUrnInkUpdatedMem σ I urnInkNew)
    (UInt256.ofNat 18) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd3277 := rd3275.push1 ⟨32⟩ (by native_decide) (by evm_ov)
  have rd3278pre := rd3277.dup3 (by native_decide) (by evm_ov)
  have rd3279raw := rd3278pre.add (by native_decide) (by evm_ov)
  have hoff : (⟨192⟩ : UInt256) + ⟨32⟩ = ⟨224⟩ := by native_decide
  have hmload224 :
      (if ((⟨192⟩ : UInt256) + ⟨32⟩).toNat ≥
            (frobUrnInkUpdatedMem σ I urnInkNew).size
          ∨ ((⟨192⟩ : UInt256) + ⟨32⟩) ≥ UInt256.ofNat 18 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
          ((frobUrnInkUpdatedMem σ I urnInkNew).readWithPadding
            (((⟨192⟩ : UInt256) + ⟨32⟩).toNat) 32))) =
        urnArtOld := by
    rw [hoff]
    exact mloadWordValue_of_readWithPadding
      (by
        rw [show (⟨224⟩ : UInt256).toNat = 224 from by decide]
        unfold frobUrnInkUpdatedMem
        rw [writeWordMem_size_of_contains]
        · rw [frobIlkLoadedMem_size σ I]; omega
        · rw [frobIlkLoadedMem_size σ I]; omega)
      (by native_decide)
      (by
        simpa [show (⟨224⟩ : UInt256).toNat = 224 from by decide, urnArtOld]
          using frobUrnInkUpdatedMem_read224 σ I urnInkNew)
  have rd3280raw := rd3279raw.mload 0 urnArtOld (UInt256.ofNat 18)
    (by native_decide) mem_cost hmload224 (by native_decide) (by evm_ov)
  have rd3280 := by
    simpa [hoff] using rd3280raw
  have rd3283 := rd3280.push2 ⟨3289⟩ (by native_decide) (by evm_ov)
  have rd3284 := rd3283.swap1 (by native_decide) (by evm_ov)
  have rd3285 := rd3284.dup5 (by native_decide) (by evm_ov)
  have rd3288 := rd3285.push2 ⟨6653⟩ (by native_decide) (by evm_ov)
  have rd6653 := rd3288.jump (by native_decide) (by jump_dest) (by evm_ov)
  exact RD.vatSignedAddRevert
    (x := urnArtOld) (y := frobDartWord I) (ret := ⟨3289⟩)
    (R := (⟨416⟩ : UInt256) :: (⟨192⟩ : UInt256) :: frobDartWord I ::
      frobDinkWord I :: frobWMaskedWord I :: frobVMaskedWord I ::
      frobUMaskedWord I :: frobIWord I :: ⟨524⟩ :: sel :: [])
    rd6653
    (by simpa [urnArtOld] using hfail)
    (by simp)

theorem RD.vatFrobIlkArtAddSuccess
    {cA gh bl σ σ₀ A I} {g : Sat256} {k C : ℕ}
    {sel urnInkNew urnArtNew : UInt256}
    (h : RD vatBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3289⟩
      [urnArtNew, ⟨416⟩, ⟨192⟩, frobDartWord I, frobDinkWord I, frobWMaskedWord I,
        frobVMaskedWord I, frobUMaskedWord I, frobIWord I, ⟨524⟩, sel]
      (frobUrnInkUpdatedMem σ I urnInkNew) (UInt256.ofNat 18) ByteArray.empty
      (cA, σ) k C)
    (hneg :
      UInt256.slt (frobDartWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.gt (frobDartWord I + solcSlotWord σ I (frobIlkArtSlot I))
          (solcSlotWord σ I (frobIlkArtSlot I)) = ⟨0⟩)
    (hpos :
      UInt256.sgt (frobDartWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.lt (frobDartWord I + solcSlotWord σ I (frobIlkArtSlot I))
          (solcSlotWord σ I (frobIlkArtSlot I)) = ⟨0⟩) :
    ∃ k' C',
      RD vatBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3306⟩
        [frobDartWord I + solcSlotWord σ I (frobIlkArtSlot I), ⟨416⟩, ⟨192⟩,
          frobDartWord I, frobDinkWord I, frobWMaskedWord I, frobVMaskedWord I,
          frobUMaskedWord I, frobIWord I, ⟨524⟩, sel]
        (frobUrnArtUpdatedMem σ I urnInkNew urnArtNew) (UInt256.ofNat 18)
        ByteArray.empty (cA, σ) k' C' := by
  let ilkArtOld := solcSlotWord σ I (frobIlkArtSlot I)
  have rd3290 := h.jumpdest (by native_decide) (by evm_ov)
  have rd3292 := rd3290.push1 ⟨32⟩ (by native_decide) (by evm_ov)
  have rd3293pre := rd3292.dup4 (by native_decide) (by evm_ov)
  have rd3294raw := rd3293pre.add (by native_decide) (by evm_ov)
  have hoff : (⟨192⟩ : UInt256) + ⟨32⟩ = ⟨224⟩ := by native_decide
  have rd3295pre := by
    have hmem :
        urnArtNew.toByteArray.write 0 (frobUrnInkUpdatedMem σ I urnInkNew)
          (((⟨192⟩ : UInt256) + ⟨32⟩).toNat) 32 =
          frobUrnArtUpdatedMem σ I urnInkNew urnArtNew := by
      rw [hoff]
      rfl
    exact rd3294raw.mstore 0 (frobUrnArtUpdatedMem σ I urnInkNew urnArtNew)
      (UInt256.ofNat 18) (by native_decide) mem_cost hmem (by native_decide)
      (by evm_ov)
  have rd3295 := by
    simpa [hoff] using rd3295pre
  have rd3296pre := rd3295.dup1 (by native_decide) (by evm_ov)
  have hmload416 :
      (if (⟨416⟩ : UInt256).toNat ≥
            (frobUrnArtUpdatedMem σ I urnInkNew urnArtNew).size
          ∨ (⟨416⟩ : UInt256) ≥ UInt256.ofNat 18 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
          ((frobUrnArtUpdatedMem σ I urnInkNew urnArtNew).readWithPadding
            (⟨416⟩ : UInt256).toNat 32))) =
        ilkArtOld := by
    exact mloadWordValue_of_readWithPadding
      (by
        rw [show (⟨416⟩ : UInt256).toNat = 416 from by decide]
        unfold frobUrnArtUpdatedMem frobUrnInkUpdatedMem
        rw [writeWordMem_size_of_contains]
        · rw [writeWordMem_size_of_contains]
          · rw [frobIlkLoadedMem_size σ I]; omega
          · rw [frobIlkLoadedMem_size σ I]; omega
        · rw [writeWordMem_size_of_contains]
          · rw [frobIlkLoadedMem_size σ I]; omega
          · rw [frobIlkLoadedMem_size σ I]; omega)
      (by native_decide)
      (by
        simpa [show (⟨416⟩ : UInt256).toNat = 416 from by decide, ilkArtOld]
          using frobUrnArtUpdatedMem_read416 σ I urnInkNew urnArtNew)
  have rd3297 := rd3296pre.mload 0 ilkArtOld (UInt256.ofNat 18)
    (by native_decide) mem_cost hmload416 (by native_decide) (by evm_ov)
  have rd3300 := rd3297.push2 ⟨3306⟩ (by native_decide) (by evm_ov)
  have rd3301 := rd3300.swap1 (by native_decide) (by evm_ov)
  have rd3302 := rd3301.dup5 (by native_decide) (by evm_ov)
  have rd3305 := rd3302.push2 ⟨6653⟩ (by native_decide) (by evm_ov)
  have rd6653 := rd3305.jump (by native_decide) (by jump_dest) (by evm_ov)
  obtain ⟨_, _, rd3306⟩ := RD.vatSignedAddOk
    (x := ilkArtOld) (y := frobDartWord I) (ret := ⟨3306⟩)
    (R := (⟨416⟩ : UInt256) :: (⟨192⟩ : UInt256) :: frobDartWord I ::
      frobDinkWord I :: frobWMaskedWord I :: frobVMaskedWord I ::
      frobUMaskedWord I :: frobIWord I :: ⟨524⟩ :: sel :: [])
    rd6653
    (by simpa [ilkArtOld] using hneg)
    (by simpa [ilkArtOld] using hpos)
    (by jump_dest) (by simp)
  exact ⟨_, _, by simpa [ilkArtOld] using rd3306⟩

theorem RD.vatFrobIlkArtAddRevert
    {cA gh bl σ σ₀ A I} {g : Sat256} {k C : ℕ}
    {sel urnInkNew urnArtNew : UInt256}
    (h : RD vatBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3289⟩
      [urnArtNew, ⟨416⟩, ⟨192⟩, frobDartWord I, frobDinkWord I, frobWMaskedWord I,
        frobVMaskedWord I, frobUMaskedWord I, frobIWord I, ⟨524⟩, sel]
      (frobUrnInkUpdatedMem σ I urnInkNew) (UInt256.ofNat 18) ByteArray.empty
      (cA, σ) k C)
    (hfail :
      ¬ (UInt256.slt (frobDartWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.gt (frobDartWord I + solcSlotWord σ I (frobIlkArtSlot I))
          (solcSlotWord σ I (frobIlkArtSlot I)) = ⟨0⟩) ∨
      (UInt256.slt (frobDartWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.gt (frobDartWord I + solcSlotWord σ I (frobIlkArtSlot I))
          (solcSlotWord σ I (frobIlkArtSlot I)) = ⟨0⟩) ∧
        ¬ (UInt256.sgt (frobDartWord I) ⟨0⟩ = ⟨0⟩ ∨
          UInt256.lt (frobDartWord I + solcSlotWord σ I (frobIlkArtSlot I))
            (solcSlotWord σ I (frobIlkArtSlot I)) = ⟨0⟩)) :
    RDrev vatBytecode g (initState cA gh bl σ σ₀ g A I) := by
  let ilkArtOld := solcSlotWord σ I (frobIlkArtSlot I)
  have rd3290 := h.jumpdest (by native_decide) (by evm_ov)
  have rd3292 := rd3290.push1 ⟨32⟩ (by native_decide) (by evm_ov)
  have rd3293pre := rd3292.dup4 (by native_decide) (by evm_ov)
  have rd3294raw := rd3293pre.add (by native_decide) (by evm_ov)
  have hoff : (⟨192⟩ : UInt256) + ⟨32⟩ = ⟨224⟩ := by native_decide
  have rd3295pre := by
    have hmem :
        urnArtNew.toByteArray.write 0 (frobUrnInkUpdatedMem σ I urnInkNew)
          (((⟨192⟩ : UInt256) + ⟨32⟩).toNat) 32 =
          frobUrnArtUpdatedMem σ I urnInkNew urnArtNew := by
      rw [hoff]
      rfl
    exact rd3294raw.mstore 0 (frobUrnArtUpdatedMem σ I urnInkNew urnArtNew)
      (UInt256.ofNat 18) (by native_decide) mem_cost hmem (by native_decide)
      (by evm_ov)
  have rd3295 := by
    simpa [hoff] using rd3295pre
  have rd3296pre := rd3295.dup1 (by native_decide) (by evm_ov)
  have hmload416 :
      (if (⟨416⟩ : UInt256).toNat ≥
            (frobUrnArtUpdatedMem σ I urnInkNew urnArtNew).size
          ∨ (⟨416⟩ : UInt256) ≥ UInt256.ofNat 18 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
          ((frobUrnArtUpdatedMem σ I urnInkNew urnArtNew).readWithPadding
            (⟨416⟩ : UInt256).toNat 32))) =
        ilkArtOld := by
    exact mloadWordValue_of_readWithPadding
      (by
        rw [show (⟨416⟩ : UInt256).toNat = 416 from by decide]
        unfold frobUrnArtUpdatedMem frobUrnInkUpdatedMem
        rw [writeWordMem_size_of_contains]
        · rw [writeWordMem_size_of_contains]
          · rw [frobIlkLoadedMem_size σ I]; omega
          · rw [frobIlkLoadedMem_size σ I]; omega
        · rw [writeWordMem_size_of_contains]
          · rw [frobIlkLoadedMem_size σ I]; omega
          · rw [frobIlkLoadedMem_size σ I]; omega)
      (by native_decide)
      (by
        simpa [show (⟨416⟩ : UInt256).toNat = 416 from by decide, ilkArtOld]
          using frobUrnArtUpdatedMem_read416 σ I urnInkNew urnArtNew)
  have rd3297 := rd3296pre.mload 0 ilkArtOld (UInt256.ofNat 18)
    (by native_decide) mem_cost hmload416 (by native_decide) (by evm_ov)
  have rd3300 := rd3297.push2 ⟨3306⟩ (by native_decide) (by evm_ov)
  have rd3301 := rd3300.swap1 (by native_decide) (by evm_ov)
  have rd3302 := rd3301.dup5 (by native_decide) (by evm_ov)
  have rd3305 := rd3302.push2 ⟨6653⟩ (by native_decide) (by evm_ov)
  have rd6653 := rd3305.jump (by native_decide) (by jump_dest) (by evm_ov)
  exact RD.vatSignedAddRevert
    (x := ilkArtOld) (y := frobDartWord I) (ret := ⟨3306⟩)
    (R := (⟨416⟩ : UInt256) :: (⟨192⟩ : UInt256) :: frobDartWord I ::
      frobDinkWord I :: frobWMaskedWord I :: frobVMaskedWord I ::
      frobUMaskedWord I :: frobIWord I :: ⟨524⟩ :: sel :: [])
    rd6653
    (by simpa [ilkArtOld] using hfail)
    (by simp)

theorem RD.vatFrobDtabMulSuccess
    {cA gh bl σ σ₀ A I} {g : Sat256} {k C : ℕ}
    {sel urnInkNew urnArtNew ilkArtNew : UInt256}
    (h : RD vatBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3306⟩
      [ilkArtNew, ⟨416⟩, ⟨192⟩, frobDartWord I, frobDinkWord I, frobWMaskedWord I,
        frobVMaskedWord I, frobUMaskedWord I, frobIWord I, ⟨524⟩, sel]
      (frobUrnArtUpdatedMem σ I urnInkNew urnArtNew) (UInt256.ofNat 18)
      ByteArray.empty (cA, σ) k C)
    (hmax : UInt256.slt (solcSlotWord σ I (frobIlkRateSlot I)) ⟨0⟩ = ⟨0⟩)
    (hmul :
      frobDartWord I = ⟨0⟩ ∨
        UInt256.eq
          (UInt256.sdiv
            (UInt256.mul (frobDartWord I) (solcSlotWord σ I (frobIlkRateSlot I)))
            (frobDartWord I))
          (solcSlotWord σ I (frobIlkRateSlot I)) ≠ ⟨0⟩) :
    ∃ k' C',
      RD vatBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3329⟩
        [UInt256.mul (frobDartWord I) (solcSlotWord σ I (frobIlkRateSlot I)),
          ⟨416⟩, ⟨192⟩, frobDartWord I, frobDinkWord I, frobWMaskedWord I,
          frobVMaskedWord I, frobUMaskedWord I, frobIWord I, ⟨524⟩, sel]
        (frobIlkArtUpdatedMem σ I urnInkNew urnArtNew ilkArtNew) (UInt256.ofNat 18)
        ByteArray.empty (cA, σ) k' C' := by
  let rateOld := solcSlotWord σ I (frobIlkRateSlot I)
  have rd3307 := h.jumpdest (by native_decide) (by evm_ov)
  have rd3308pre := rd3307.dup2 (by native_decide) (by evm_ov)
  have rd3309 := rd3308pre.mstore 0
    (frobIlkArtUpdatedMem σ I urnInkNew urnArtNew ilkArtNew)
    (UInt256.ofNat 18) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd3311 := rd3309.push1 ⟨32⟩ (by native_decide) (by evm_ov)
  have rd3312pre := rd3311.dup2 (by native_decide) (by evm_ov)
  have rd3313raw := rd3312pre.add (by native_decide) (by evm_ov)
  have hoff : (⟨416⟩ : UInt256) + ⟨32⟩ = ⟨448⟩ := by native_decide
  have hmload448 :
      (if ((⟨416⟩ : UInt256) + ⟨32⟩).toNat ≥
            (frobIlkArtUpdatedMem σ I urnInkNew urnArtNew ilkArtNew).size
          ∨ ((⟨416⟩ : UInt256) + ⟨32⟩) ≥ UInt256.ofNat 18 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
          ((frobIlkArtUpdatedMem σ I urnInkNew urnArtNew ilkArtNew).readWithPadding
            (((⟨416⟩ : UInt256) + ⟨32⟩).toNat) 32))) =
        rateOld := by
    rw [hoff]
    exact mloadWordValue_of_readWithPadding
      (by
        rw [show (⟨448⟩ : UInt256).toNat = 448 from by decide]
        unfold frobIlkArtUpdatedMem frobUrnArtUpdatedMem frobUrnInkUpdatedMem
        rw [writeWordMem_size_of_contains]
        · rw [writeWordMem_size_of_contains]
          · rw [writeWordMem_size_of_contains]
            · rw [frobIlkLoadedMem_size σ I]; omega
            · rw [frobIlkLoadedMem_size σ I]; omega
          · rw [writeWordMem_size_of_contains]
            · rw [frobIlkLoadedMem_size σ I]; omega
            · rw [frobIlkLoadedMem_size σ I]; omega
        · rw [writeWordMem_size_of_contains]
          · rw [writeWordMem_size_of_contains]
            · rw [frobIlkLoadedMem_size σ I]; omega
            · rw [frobIlkLoadedMem_size σ I]; omega
          · rw [writeWordMem_size_of_contains]
            · rw [frobIlkLoadedMem_size σ I]; omega
            · rw [frobIlkLoadedMem_size σ I]; omega)
      (by native_decide)
      (by
        simpa [show (⟨448⟩ : UInt256).toNat = 448 from by decide, rateOld]
          using frobIlkArtUpdatedMem_read448 σ I urnInkNew urnArtNew ilkArtNew)
  have rd3314raw := rd3313raw.mload 0 rateOld (UInt256.ofNat 18)
    (by native_decide) mem_cost hmload448 (by native_decide) (by evm_ov)
  have rd3314 := by
    simpa [hoff] using rd3314raw
  have rd3316 := rd3314.push1 ⟨0⟩ (by native_decide) (by evm_ov)
  have rd3317 := rd3316.swap1 (by native_decide) (by evm_ov)
  have rd3320 := rd3317.push2 ⟨3326⟩ (by native_decide) (by evm_ov)
  have rd3321 := rd3320.swap1 (by native_decide) (by evm_ov)
  have rd3322 := rd3321.dup6 (by native_decide) (by evm_ov)
  have rd3325 := rd3322.push2 ⟨6706⟩ (by native_decide) (by evm_ov)
  have rd6706 := rd3325.jump (by native_decide) (by jump_dest) (by evm_ov)
  obtain ⟨_, _, rd3326⟩ := RD.vatSignedMulOk
    (x := rateOld) (y := frobDartWord I) (ret := ⟨3326⟩)
    (R := (⟨0⟩ : UInt256) :: (⟨416⟩ : UInt256) :: (⟨192⟩ : UInt256) ::
      frobDartWord I :: frobDinkWord I :: frobWMaskedWord I ::
      frobVMaskedWord I :: frobUMaskedWord I :: frobIWord I :: ⟨524⟩ :: sel :: [])
    rd6706 (by simpa [rateOld] using hmax) (by simpa [rateOld] using hmul)
    (by jump_dest) (by simp)
  have rd3327 := rd3326.jumpdest (by native_decide) (by evm_ov)
  have rd3328 := rd3327.swap1 (by native_decide) (by evm_ov)
  have rd3329 := rd3328.pop (by native_decide) (by evm_ov)
  exact ⟨_, _, by simpa [rateOld] using rd3329⟩

theorem RD.vatFrobDtabMulRevert
    {cA gh bl σ σ₀ A I} {g : Sat256} {k C : ℕ}
    {sel urnInkNew urnArtNew ilkArtNew : UInt256}
    (h : RD vatBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3306⟩
      [ilkArtNew, ⟨416⟩, ⟨192⟩, frobDartWord I, frobDinkWord I, frobWMaskedWord I,
        frobVMaskedWord I, frobUMaskedWord I, frobIWord I, ⟨524⟩, sel]
      (frobUrnArtUpdatedMem σ I urnInkNew urnArtNew) (UInt256.ofNat 18)
      ByteArray.empty (cA, σ) k C)
    (hfail :
      ¬ UInt256.slt (solcSlotWord σ I (frobIlkRateSlot I)) ⟨0⟩ = ⟨0⟩ ∨
      UInt256.slt (solcSlotWord σ I (frobIlkRateSlot I)) ⟨0⟩ = ⟨0⟩ ∧
        ¬ (frobDartWord I = ⟨0⟩ ∨
          UInt256.eq
            (UInt256.sdiv
              (UInt256.mul (frobDartWord I) (solcSlotWord σ I (frobIlkRateSlot I)))
              (frobDartWord I))
            (solcSlotWord σ I (frobIlkRateSlot I)) ≠ ⟨0⟩)) :
    RDrev vatBytecode g (initState cA gh bl σ σ₀ g A I) := by
  let rateOld := solcSlotWord σ I (frobIlkRateSlot I)
  have rd3307 := h.jumpdest (by native_decide) (by evm_ov)
  have rd3308pre := rd3307.dup2 (by native_decide) (by evm_ov)
  have rd3309 := rd3308pre.mstore 0
    (frobIlkArtUpdatedMem σ I urnInkNew urnArtNew ilkArtNew)
    (UInt256.ofNat 18) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd3311 := rd3309.push1 ⟨32⟩ (by native_decide) (by evm_ov)
  have rd3312pre := rd3311.dup2 (by native_decide) (by evm_ov)
  have rd3313raw := rd3312pre.add (by native_decide) (by evm_ov)
  have hoff : (⟨416⟩ : UInt256) + ⟨32⟩ = ⟨448⟩ := by native_decide
  have hmload448 :
      (if ((⟨416⟩ : UInt256) + ⟨32⟩).toNat ≥
            (frobIlkArtUpdatedMem σ I urnInkNew urnArtNew ilkArtNew).size
          ∨ ((⟨416⟩ : UInt256) + ⟨32⟩) ≥ UInt256.ofNat 18 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
          ((frobIlkArtUpdatedMem σ I urnInkNew urnArtNew ilkArtNew).readWithPadding
            (((⟨416⟩ : UInt256) + ⟨32⟩).toNat) 32))) =
        rateOld := by
    rw [hoff]
    exact mloadWordValue_of_readWithPadding
      (by
        rw [show (⟨448⟩ : UInt256).toNat = 448 from by decide]
        unfold frobIlkArtUpdatedMem frobUrnArtUpdatedMem frobUrnInkUpdatedMem
        rw [writeWordMem_size_of_contains]
        · rw [writeWordMem_size_of_contains]
          · rw [writeWordMem_size_of_contains]
            · rw [frobIlkLoadedMem_size σ I]; omega
            · rw [frobIlkLoadedMem_size σ I]; omega
          · rw [writeWordMem_size_of_contains]
            · rw [frobIlkLoadedMem_size σ I]; omega
            · rw [frobIlkLoadedMem_size σ I]; omega
        · rw [writeWordMem_size_of_contains]
          · rw [writeWordMem_size_of_contains]
            · rw [frobIlkLoadedMem_size σ I]; omega
            · rw [frobIlkLoadedMem_size σ I]; omega
          · rw [writeWordMem_size_of_contains]
            · rw [frobIlkLoadedMem_size σ I]; omega
            · rw [frobIlkLoadedMem_size σ I]; omega)
      (by native_decide)
      (by
        simpa [show (⟨448⟩ : UInt256).toNat = 448 from by decide, rateOld]
          using frobIlkArtUpdatedMem_read448 σ I urnInkNew urnArtNew ilkArtNew)
  have rd3314raw := rd3313raw.mload 0 rateOld (UInt256.ofNat 18)
    (by native_decide) mem_cost hmload448 (by native_decide) (by evm_ov)
  have rd3314 := by
    simpa [hoff] using rd3314raw
  have rd3316 := rd3314.push1 ⟨0⟩ (by native_decide) (by evm_ov)
  have rd3317 := rd3316.swap1 (by native_decide) (by evm_ov)
  have rd3320 := rd3317.push2 ⟨3326⟩ (by native_decide) (by evm_ov)
  have rd3321 := rd3320.swap1 (by native_decide) (by evm_ov)
  have rd3322 := rd3321.dup6 (by native_decide) (by evm_ov)
  have rd3325 := rd3322.push2 ⟨6706⟩ (by native_decide) (by evm_ov)
  have rd6706 := rd3325.jump (by native_decide) (by jump_dest) (by evm_ov)
  exact RD.vatSignedMulRevert
    (x := rateOld) (y := frobDartWord I) (ret := ⟨3326⟩)
    (R := (⟨0⟩ : UInt256) :: (⟨416⟩ : UInt256) :: (⟨192⟩ : UInt256) ::
      frobDartWord I :: frobDinkWord I :: frobWMaskedWord I ::
      frobVMaskedWord I :: frobUMaskedWord I :: frobIWord I :: ⟨524⟩ :: sel :: [])
    rd6706 (by simpa [rateOld] using hfail) (by simp)

theorem RD.vatFrobTabMulSuccess
    {cA gh bl σ σ₀ A I} {g : Sat256} {k C : ℕ}
    {sel urnInkNew urnArtNew ilkArtNew dtabWord : UInt256}
    (h : RD vatBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3329⟩
      [dtabWord, ⟨416⟩, ⟨192⟩, frobDartWord I, frobDinkWord I, frobWMaskedWord I,
        frobVMaskedWord I, frobUMaskedWord I, frobIWord I, ⟨524⟩, sel]
      (frobIlkArtUpdatedMem σ I urnInkNew urnArtNew ilkArtNew) (UInt256.ofNat 18)
      ByteArray.empty (cA, σ) k C)
    (hok :
      urnArtNew = ⟨0⟩ ∨
        UInt256.eq
          (UInt256.div
            (UInt256.mul (solcSlotWord σ I (frobIlkRateSlot I)) urnArtNew)
            urnArtNew)
          (solcSlotWord σ I (frobIlkRateSlot I)) ≠ ⟨0⟩) :
    ∃ k' C',
      RD vatBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3351⟩
        [UInt256.mul (solcSlotWord σ I (frobIlkRateSlot I)) urnArtNew,
          dtabWord, ⟨416⟩, ⟨192⟩, frobDartWord I, frobDinkWord I, frobWMaskedWord I,
          frobVMaskedWord I, frobUMaskedWord I, frobIWord I, ⟨524⟩, sel]
        (frobIlkArtUpdatedMem σ I urnInkNew urnArtNew ilkArtNew) (UInt256.ofNat 18)
        ByteArray.empty (cA, σ) k' C' := by
  let rateOld := solcSlotWord σ I (frobIlkRateSlot I)
  let mem := frobIlkArtUpdatedMem σ I urnInkNew urnArtNew ilkArtNew
  have rd3330 := h.push1 ⟨0⟩ (by native_decide) (by evm_ov)
  have rd3333 := rd3330.push2 ⟨3348⟩ (by native_decide) (by evm_ov)
  have rd3334 := rd3333.dup4 (by native_decide) (by evm_ov)
  have rd3336 := rd3334.push1 ⟨32⟩ (by native_decide) (by evm_ov)
  have rd3337raw := rd3336.add (by native_decide) (by evm_ov)
  have hoff416 : (⟨416⟩ : UInt256) + ⟨32⟩ = ⟨448⟩ := by native_decide
  have hmload448 :
      (if ((⟨416⟩ : UInt256) + ⟨32⟩).toNat ≥ mem.size
          ∨ ((⟨416⟩ : UInt256) + ⟨32⟩) ≥ UInt256.ofNat 18 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
          (mem.readWithPadding (((⟨416⟩ : UInt256) + ⟨32⟩).toNat) 32))) =
        rateOld := by
    rw [hoff416]
    exact mloadWordValue_of_readWithPadding
      (by
        rw [show (⟨448⟩ : UInt256).toNat = 448 from by decide]
        unfold mem frobIlkArtUpdatedMem frobUrnArtUpdatedMem frobUrnInkUpdatedMem
        rw [writeWordMem_size_of_contains]
        · rw [writeWordMem_size_of_contains]
          · rw [writeWordMem_size_of_contains]
            · rw [frobIlkLoadedMem_size σ I]; omega
            · rw [frobIlkLoadedMem_size σ I]; omega
          · rw [writeWordMem_size_of_contains]
            · rw [frobIlkLoadedMem_size σ I]; omega
            · rw [frobIlkLoadedMem_size σ I]; omega
        · rw [writeWordMem_size_of_contains]
          · rw [writeWordMem_size_of_contains]
            · rw [frobIlkLoadedMem_size σ I]; omega
            · rw [frobIlkLoadedMem_size σ I]; omega
          · rw [writeWordMem_size_of_contains]
            · rw [frobIlkLoadedMem_size σ I]; omega
            · rw [frobIlkLoadedMem_size σ I]; omega)
      (by native_decide)
      (by
        simpa [show (⟨448⟩ : UInt256).toNat = 448 from by decide, mem, rateOld]
          using frobIlkArtUpdatedMem_read448 σ I urnInkNew urnArtNew ilkArtNew)
  have rd3338raw := rd3337raw.mload 0 rateOld (UInt256.ofNat 18)
    (by native_decide) mem_cost hmload448 (by native_decide) (by evm_ov)
  have rd3338 := by
    simpa [hoff416] using rd3338raw
  have rd3339 := rd3338.dup6 (by native_decide) (by evm_ov)
  have rd3341 := rd3339.push1 ⟨32⟩ (by native_decide) (by evm_ov)
  have rd3342raw := rd3341.add (by native_decide) (by evm_ov)
  have hoff192 : (⟨192⟩ : UInt256) + ⟨32⟩ = ⟨224⟩ := by native_decide
  have hmload224 :
      (if ((⟨192⟩ : UInt256) + ⟨32⟩).toNat ≥ mem.size
          ∨ ((⟨192⟩ : UInt256) + ⟨32⟩) ≥ UInt256.ofNat 18 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
          (mem.readWithPadding (((⟨192⟩ : UInt256) + ⟨32⟩).toNat) 32))) =
        urnArtNew := by
    rw [hoff192]
    exact mloadWordValue_of_readWithPadding
      (by
        rw [show (⟨224⟩ : UInt256).toNat = 224 from by decide]
        unfold mem frobIlkArtUpdatedMem frobUrnArtUpdatedMem frobUrnInkUpdatedMem
        rw [writeWordMem_size_of_contains]
        · rw [writeWordMem_size_of_contains]
          · rw [writeWordMem_size_of_contains]
            · rw [frobIlkLoadedMem_size σ I]; omega
            · rw [frobIlkLoadedMem_size σ I]; omega
          · rw [writeWordMem_size_of_contains]
            · rw [frobIlkLoadedMem_size σ I]; omega
            · rw [frobIlkLoadedMem_size σ I]; omega
        · rw [writeWordMem_size_of_contains]
          · rw [writeWordMem_size_of_contains]
            · rw [frobIlkLoadedMem_size σ I]; omega
            · rw [frobIlkLoadedMem_size σ I]; omega
          · rw [writeWordMem_size_of_contains]
            · rw [frobIlkLoadedMem_size σ I]; omega
            · rw [frobIlkLoadedMem_size σ I]; omega)
      (by native_decide)
      (by
        simpa [show (⟨224⟩ : UInt256).toNat = 224 from by decide, mem]
          using frobIlkArtUpdatedMem_read224 σ I urnInkNew urnArtNew ilkArtNew)
  have rd3343raw := rd3342raw.mload 0 urnArtNew (UInt256.ofNat 18)
    (by native_decide) mem_cost hmload224 (by native_decide) (by evm_ov)
  have rd3343 := by
    simpa [hoff192] using rd3343raw
  have rd3346 := rd3343.push2 ⟨6752⟩ (by native_decide) (by evm_ov)
  have rd6752 := rd3346.jump (by native_decide) (by jump_dest) (by evm_ov)
  obtain ⟨_, _, rd3348⟩ := Benchmarks.Dss.Vat.RD.vatCheckedMulUintOk
    (x := urnArtNew) (y := rateOld) (ret := ⟨3348⟩)
    (R := (⟨0⟩ : UInt256) :: dtabWord :: (⟨416⟩ : UInt256) ::
      (⟨192⟩ : UInt256) :: frobDartWord I :: frobDinkWord I ::
      frobWMaskedWord I :: frobVMaskedWord I :: frobUMaskedWord I ::
      frobIWord I :: ⟨524⟩ :: sel :: [])
    rd6752 (by simpa [rateOld] using hok) (by jump_dest) (by simp)
  have rd3349 := rd3348.jumpdest (by native_decide) (by evm_ov)
  have rd3350 := rd3349.swap1 (by native_decide) (by evm_ov)
  have rd3351 := rd3350.pop (by native_decide) (by evm_ov)
  exact ⟨_, _, by simpa [rateOld, mem] using rd3351⟩

theorem RD.vatFrobTabMulRevert
    {cA gh bl σ σ₀ A I} {g : Sat256} {k C : ℕ}
    {sel urnInkNew urnArtNew ilkArtNew dtabWord : UInt256}
    (h : RD vatBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3329⟩
      [dtabWord, ⟨416⟩, ⟨192⟩, frobDartWord I, frobDinkWord I, frobWMaskedWord I,
        frobVMaskedWord I, frobUMaskedWord I, frobIWord I, ⟨524⟩, sel]
      (frobIlkArtUpdatedMem σ I urnInkNew urnArtNew ilkArtNew) (UInt256.ofNat 18)
      ByteArray.empty (cA, σ) k C)
    (hfail :
      ¬ (urnArtNew = ⟨0⟩ ∨
        UInt256.eq
          (UInt256.div
            (UInt256.mul (solcSlotWord σ I (frobIlkRateSlot I)) urnArtNew)
            urnArtNew)
          (solcSlotWord σ I (frobIlkRateSlot I)) ≠ ⟨0⟩)) :
    RDrev vatBytecode g (initState cA gh bl σ σ₀ g A I) := by
  let rateOld := solcSlotWord σ I (frobIlkRateSlot I)
  let mem := frobIlkArtUpdatedMem σ I urnInkNew urnArtNew ilkArtNew
  have rd3330 := h.push1 ⟨0⟩ (by native_decide) (by evm_ov)
  have rd3333 := rd3330.push2 ⟨3348⟩ (by native_decide) (by evm_ov)
  have rd3334 := rd3333.dup4 (by native_decide) (by evm_ov)
  have rd3336 := rd3334.push1 ⟨32⟩ (by native_decide) (by evm_ov)
  have rd3337raw := rd3336.add (by native_decide) (by evm_ov)
  have hoff416 : (⟨416⟩ : UInt256) + ⟨32⟩ = ⟨448⟩ := by native_decide
  have hmload448 :
      (if ((⟨416⟩ : UInt256) + ⟨32⟩).toNat ≥ mem.size
          ∨ ((⟨416⟩ : UInt256) + ⟨32⟩) ≥ UInt256.ofNat 18 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
          (mem.readWithPadding (((⟨416⟩ : UInt256) + ⟨32⟩).toNat) 32))) =
        rateOld := by
    rw [hoff416]
    exact mloadWordValue_of_readWithPadding
      (by
        rw [show (⟨448⟩ : UInt256).toNat = 448 from by decide]
        unfold mem frobIlkArtUpdatedMem frobUrnArtUpdatedMem frobUrnInkUpdatedMem
        rw [writeWordMem_size_of_contains]
        · rw [writeWordMem_size_of_contains]
          · rw [writeWordMem_size_of_contains]
            · rw [frobIlkLoadedMem_size σ I]; omega
            · rw [frobIlkLoadedMem_size σ I]; omega
          · rw [writeWordMem_size_of_contains]
            · rw [frobIlkLoadedMem_size σ I]; omega
            · rw [frobIlkLoadedMem_size σ I]; omega
        · rw [writeWordMem_size_of_contains]
          · rw [writeWordMem_size_of_contains]
            · rw [frobIlkLoadedMem_size σ I]; omega
            · rw [frobIlkLoadedMem_size σ I]; omega
          · rw [writeWordMem_size_of_contains]
            · rw [frobIlkLoadedMem_size σ I]; omega
            · rw [frobIlkLoadedMem_size σ I]; omega)
      (by native_decide)
      (by
        simpa [show (⟨448⟩ : UInt256).toNat = 448 from by decide, mem, rateOld]
          using frobIlkArtUpdatedMem_read448 σ I urnInkNew urnArtNew ilkArtNew)
  have rd3338raw := rd3337raw.mload 0 rateOld (UInt256.ofNat 18)
    (by native_decide) mem_cost hmload448 (by native_decide) (by evm_ov)
  have rd3338 := by
    simpa [hoff416] using rd3338raw
  have rd3339 := rd3338.dup6 (by native_decide) (by evm_ov)
  have rd3341 := rd3339.push1 ⟨32⟩ (by native_decide) (by evm_ov)
  have rd3342raw := rd3341.add (by native_decide) (by evm_ov)
  have hoff192 : (⟨192⟩ : UInt256) + ⟨32⟩ = ⟨224⟩ := by native_decide
  have hmload224 :
      (if ((⟨192⟩ : UInt256) + ⟨32⟩).toNat ≥ mem.size
          ∨ ((⟨192⟩ : UInt256) + ⟨32⟩) ≥ UInt256.ofNat 18 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
          (mem.readWithPadding (((⟨192⟩ : UInt256) + ⟨32⟩).toNat) 32))) =
        urnArtNew := by
    rw [hoff192]
    exact mloadWordValue_of_readWithPadding
      (by
        rw [show (⟨224⟩ : UInt256).toNat = 224 from by decide]
        unfold mem frobIlkArtUpdatedMem frobUrnArtUpdatedMem frobUrnInkUpdatedMem
        rw [writeWordMem_size_of_contains]
        · rw [writeWordMem_size_of_contains]
          · rw [writeWordMem_size_of_contains]
            · rw [frobIlkLoadedMem_size σ I]; omega
            · rw [frobIlkLoadedMem_size σ I]; omega
          · rw [writeWordMem_size_of_contains]
            · rw [frobIlkLoadedMem_size σ I]; omega
            · rw [frobIlkLoadedMem_size σ I]; omega
        · rw [writeWordMem_size_of_contains]
          · rw [writeWordMem_size_of_contains]
            · rw [frobIlkLoadedMem_size σ I]; omega
            · rw [frobIlkLoadedMem_size σ I]; omega
          · rw [writeWordMem_size_of_contains]
            · rw [frobIlkLoadedMem_size σ I]; omega
            · rw [frobIlkLoadedMem_size σ I]; omega)
      (by native_decide)
      (by
        simpa [show (⟨224⟩ : UInt256).toNat = 224 from by decide, mem]
          using frobIlkArtUpdatedMem_read224 σ I urnInkNew urnArtNew ilkArtNew)
  have rd3343raw := rd3342raw.mload 0 urnArtNew (UInt256.ofNat 18)
    (by native_decide) mem_cost hmload224 (by native_decide) (by evm_ov)
  have rd3343 := by
    simpa [hoff192] using rd3343raw
  have rd3346 := rd3343.push2 ⟨6752⟩ (by native_decide) (by evm_ov)
  have rd6752 := rd3346.jump (by native_decide) (by jump_dest) (by evm_ov)
  exact RD.vatCheckedMulUintRevert
    (x := urnArtNew) (y := rateOld) (ret := ⟨3348⟩)
    (R := (⟨0⟩ : UInt256) :: dtabWord :: (⟨416⟩ : UInt256) ::
      (⟨192⟩ : UInt256) :: frobDartWord I :: frobDinkWord I ::
      frobWMaskedWord I :: frobVMaskedWord I :: frobUMaskedWord I ::
      frobIWord I :: ⟨524⟩ :: sel :: [])
    rd6752 (by simpa [rateOld] using hfail) (by simp)

theorem RD.vatFrobDebtAddStoreSuccess
    {cA gh bl σ σ₀ A I} {g : Sat256} {k C : ℕ}
    {sel tab dtabWord urnInkNew urnArtNew ilkArtNew : UInt256}
    (h : RD vatBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3351⟩
      [tab, dtabWord, ⟨416⟩, ⟨192⟩, frobDartWord I, frobDinkWord I,
        frobWMaskedWord I, frobVMaskedWord I, frobUMaskedWord I, frobIWord I,
        ⟨524⟩, sel]
      (frobIlkArtUpdatedMem σ I urnInkNew urnArtNew ilkArtNew) (UInt256.ofNat 18)
      ByteArray.empty (cA, σ) k C)
    (hperm : I.perm = true)
    (hneg :
      UInt256.slt dtabWord ⟨0⟩ = ⟨0⟩ ∨
        UInt256.gt (dtabWord + solcSlotWord σ I foldDebtSlot)
          (solcSlotWord σ I foldDebtSlot) = ⟨0⟩)
    (hpos :
      UInt256.sgt dtabWord ⟨0⟩ = ⟨0⟩ ∨
        UInt256.lt (dtabWord + solcSlotWord σ I foldDebtSlot)
          (solcSlotWord σ I foldDebtSlot) = ⟨0⟩) :
    ∃ k' C',
      RD vatBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3369⟩
        [tab, dtabWord, ⟨416⟩, ⟨192⟩, frobDartWord I, frobDinkWord I,
          frobWMaskedWord I, frobVMaskedWord I, frobUMaskedWord I, frobIWord I,
          ⟨524⟩, sel]
        (frobIlkArtUpdatedMem σ I urnInkNew urnArtNew ilkArtNew) (UInt256.ofNat 18)
        ByteArray.empty
        (cA, sstoreAccountMap I.codeOwner σ foldDebtSlot
          (dtabWord + solcSlotWord σ I foldDebtSlot)) k' C' := by
  let debtOld := solcSlotWord σ I foldDebtSlot
  let debtNew := dtabWord + debtOld
  let mem := frobIlkArtUpdatedMem σ I urnInkNew urnArtNew ilkArtNew
  have rd3354 := h.push2 ⟨3362⟩ (by native_decide) (by evm_ov)
  have rd3356 := rd3354.push1 ⟨7⟩ (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd3357raw⟩ := rd3356.sload (by native_decide) (by evm_ov)
  have hload :
      (σ.find? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD (⟨7⟩ : UInt256) ⟨0⟩)) = debtOld := by
    simp [debtOld, foldDebtSlot, solcSlotWord]
  have rd3357 := rd3357raw
  rw [hload] at rd3357
  have rd3358 := rd3357.dup4 (by native_decide) (by evm_ov)
  have rd3361 := rd3358.push2 ⟨6653⟩ (by native_decide) (by evm_ov)
  have rd6653 := rd3361.jump (by native_decide) (by jump_dest) (by evm_ov)
  obtain ⟨_, _, rd3362⟩ := RD.vatSignedAddOk
    (x := debtOld) (y := dtabWord) (ret := ⟨3362⟩)
    (R := tab :: dtabWord :: (⟨416⟩ : UInt256) :: (⟨192⟩ : UInt256) ::
      frobDartWord I :: frobDinkWord I :: frobWMaskedWord I ::
      frobVMaskedWord I :: frobUMaskedWord I :: frobIWord I :: ⟨524⟩ :: sel :: [])
    rd6653
    (by simpa [debtOld, debtNew] using hneg)
    (by simpa [debtOld, debtNew] using hpos)
    (by jump_dest) (by simp)
  have rd3363 := rd3362.jumpdest (by native_decide) (by evm_ov)
  have rd3365 := rd3363.push1 ⟨7⟩ (by native_decide) (by evm_ov)
  have rd3366 := rd3365.dup2 (by native_decide) (by evm_ov)
  have rd3367pre := rd3366.swap1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd3368⟩ := rd3367pre.sstore hperm (by native_decide) (by evm_ov)
  have rd3369 := rd3368.pop (by native_decide) (by evm_ov)
  exact ⟨_, _, by simpa [debtOld, debtNew, mem, foldDebtSlot] using rd3369⟩

theorem RD.vatFrobDebtAddStoreRevert
    {cA gh bl σ σ₀ A I} {g : Sat256} {k C : ℕ}
    {sel tab dtabWord urnInkNew urnArtNew ilkArtNew : UInt256}
    (h : RD vatBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3351⟩
      [tab, dtabWord, ⟨416⟩, ⟨192⟩, frobDartWord I, frobDinkWord I,
        frobWMaskedWord I, frobVMaskedWord I, frobUMaskedWord I, frobIWord I,
        ⟨524⟩, sel]
      (frobIlkArtUpdatedMem σ I urnInkNew urnArtNew ilkArtNew) (UInt256.ofNat 18)
      ByteArray.empty (cA, σ) k C)
    (hfail :
      ¬ (UInt256.slt dtabWord ⟨0⟩ = ⟨0⟩ ∨
        UInt256.gt (dtabWord + solcSlotWord σ I foldDebtSlot)
          (solcSlotWord σ I foldDebtSlot) = ⟨0⟩) ∨
      (UInt256.slt dtabWord ⟨0⟩ = ⟨0⟩ ∨
        UInt256.gt (dtabWord + solcSlotWord σ I foldDebtSlot)
          (solcSlotWord σ I foldDebtSlot) = ⟨0⟩) ∧
        ¬ (UInt256.sgt dtabWord ⟨0⟩ = ⟨0⟩ ∨
          UInt256.lt (dtabWord + solcSlotWord σ I foldDebtSlot)
            (solcSlotWord σ I foldDebtSlot) = ⟨0⟩)) :
    RDrev vatBytecode g (initState cA gh bl σ σ₀ g A I) := by
  let debtOld := solcSlotWord σ I foldDebtSlot
  let debtNew := dtabWord + debtOld
  have rd3354 := h.push2 ⟨3362⟩ (by native_decide) (by evm_ov)
  have rd3356 := rd3354.push1 ⟨7⟩ (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd3357raw⟩ := rd3356.sload (by native_decide) (by evm_ov)
  have hload :
      (σ.find? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD (⟨7⟩ : UInt256) ⟨0⟩)) = debtOld := by
    simp [debtOld, foldDebtSlot, solcSlotWord]
  have rd3357 := rd3357raw
  rw [hload] at rd3357
  have rd3358 := rd3357.dup4 (by native_decide) (by evm_ov)
  have rd3361 := rd3358.push2 ⟨6653⟩ (by native_decide) (by evm_ov)
  have rd6653 := rd3361.jump (by native_decide) (by jump_dest) (by evm_ov)
  exact RD.vatSignedAddRevert
    (x := debtOld) (y := dtabWord) (ret := ⟨3362⟩)
    (R := tab :: dtabWord :: (⟨416⟩ : UInt256) :: (⟨192⟩ : UInt256) ::
      frobDartWord I :: frobDinkWord I :: frobWMaskedWord I ::
      frobVMaskedWord I :: frobUMaskedWord I :: frobIWord I :: ⟨524⟩ :: sel :: [])
    rd6653
    (by simpa [debtOld, debtNew] using hfail)
    (by simp)

theorem RD.vatFrobCeilingCheckSuccess
    {cA gh bl σ σ₀ A I} {g : Sat256} {k C : ℕ}
    {sel tab dtabWord urnInkNew urnArtNew ilkArtNew debtNew : UInt256}
    (h : RD vatBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3369⟩
      [tab, dtabWord, ⟨416⟩, ⟨192⟩, frobDartWord I, frobDinkWord I,
        frobWMaskedWord I, frobVMaskedWord I, frobUMaskedWord I, frobIWord I,
        ⟨524⟩, sel]
      (frobIlkArtUpdatedMem σ I urnInkNew urnArtNew ilkArtNew) (UInt256.ofNat 18)
      ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ foldDebtSlot debtNew) k C)
    (hok :
      solcSlotWord σ I (frobIlkRateSlot I) = ⟨0⟩ ∨
        UInt256.eq
          (UInt256.div
            (UInt256.mul ilkArtNew (solcSlotWord σ I (frobIlkRateSlot I)))
            (solcSlotWord σ I (frobIlkRateSlot I)))
          ilkArtNew ≠ ⟨0⟩)
    (hceiling :
      UInt256.lor
        (UInt256.land
          (UInt256.isZero
            (UInt256.gt debtNew (solcSlotWord σ I ⟨9⟩)))
          (UInt256.isZero
            (UInt256.gt
              (UInt256.mul ilkArtNew (solcSlotWord σ I (frobIlkRateSlot I)))
              (solcSlotWord σ I (frobIlkLineSlot I)))))
        (UInt256.isZero (UInt256.sgt (frobDartWord I) ⟨0⟩)) ≠ ⟨0⟩) :
    ((sstoreAccountMap I.codeOwner σ foldDebtSlot debtNew).find? I.codeOwner |>.option ⟨0⟩
      (fun acc => acc.storage.findD (⟨7⟩ : UInt256) ⟨0⟩)) = debtNew →
    ∃ k' C',
      RD vatBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3494⟩
        [tab, dtabWord, ⟨416⟩, ⟨192⟩, frobDartWord I, frobDinkWord I,
          frobWMaskedWord I, frobVMaskedWord I, frobUMaskedWord I, frobIWord I,
          ⟨524⟩, sel]
        (frobIlkArtUpdatedMem σ I urnInkNew urnArtNew ilkArtNew) (UInt256.ofNat 18)
        ByteArray.empty
        (cA, sstoreAccountMap I.codeOwner σ foldDebtSlot debtNew) k' C' := by
  intro hdebtLoadStore
  let σDebt := sstoreAccountMap I.codeOwner σ foldDebtSlot debtNew
  let mem := frobIlkArtUpdatedMem σ I urnInkNew urnArtNew ilkArtNew
  let rateOld := solcSlotWord σ I (frobIlkRateSlot I)
  let ilkLine := solcSlotWord σ I (frobIlkLineSlot I)
  let Line := solcSlotWord σ I ⟨9⟩
  let ceilingDebt := UInt256.mul rateOld ilkArtNew
  have rd3372 := h.push2 ⟨3422⟩ (by native_decide) (by evm_ov)
  have rd3374 := rd3372.push1 ⟨0⟩ (by native_decide) (by evm_ov)
  have rd3375 := rd3374.dup7 (by native_decide) (by evm_ov)
  have rd3376 := rd3375.sgt (by native_decide) (by evm_ov)
  have rd3377 := rd3376.iszero (by native_decide) (by evm_ov)
  have rd3380 := rd3377.push2 ⟨3417⟩ (by native_decide) (by evm_ov)
  have rd3381 := rd3380.dup6 (by native_decide) (by evm_ov)
  have rd3383 := rd3381.push1 ⟨96⟩ (by native_decide) (by evm_ov)
  have rd3384raw := rd3383.add (by native_decide) (by evm_ov)
  have hoff512 : (⟨416⟩ : UInt256) + ⟨96⟩ = ⟨512⟩ := by native_decide
  have hmload512 :
      (if ((⟨416⟩ : UInt256) + ⟨96⟩).toNat ≥ mem.size
          ∨ ((⟨416⟩ : UInt256) + ⟨96⟩) ≥ UInt256.ofNat 18 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
          (mem.readWithPadding (((⟨416⟩ : UInt256) + ⟨96⟩).toNat) 32))) =
        ilkLine := by
    rw [hoff512]
    exact mloadWordValue_of_readWithPadding
      (by
        rw [show (⟨512⟩ : UInt256).toNat = 512 from by decide]
        unfold mem frobIlkArtUpdatedMem frobUrnArtUpdatedMem frobUrnInkUpdatedMem
        rw [writeWordMem_size_of_contains]
        · rw [writeWordMem_size_of_contains]
          · rw [writeWordMem_size_of_contains]
            · rw [frobIlkLoadedMem_size σ I]; omega
            · rw [frobIlkLoadedMem_size σ I]; omega
          · rw [writeWordMem_size_of_contains]
            · rw [frobIlkLoadedMem_size σ I]; omega
            · rw [frobIlkLoadedMem_size σ I]; omega
        · rw [writeWordMem_size_of_contains]
          · rw [writeWordMem_size_of_contains]
            · rw [frobIlkLoadedMem_size σ I]; omega
            · rw [frobIlkLoadedMem_size σ I]; omega
          · rw [writeWordMem_size_of_contains]
            · rw [frobIlkLoadedMem_size σ I]; omega
            · rw [frobIlkLoadedMem_size σ I]; omega)
      (by native_decide)
      (by
        simpa [show (⟨512⟩ : UInt256).toNat = 512 from by decide, mem, ilkLine]
          using frobIlkArtUpdatedMem_read512 σ I urnInkNew urnArtNew ilkArtNew)
  have rd3384raw' := rd3384raw.mload 0 ilkLine (UInt256.ofNat 18)
    (by native_decide) mem_cost hmload512 (by native_decide) (by evm_ov)
  have rd3384 := by
    simpa [hoff512] using rd3384raw'
  have rd3388 := rd3384.push2 ⟨3402⟩ (by native_decide) (by evm_ov)
  have rd3389 := rd3388.dup8 (by native_decide) (by evm_ov)
  have rd3391 := rd3389.push1 ⟨0⟩ (by native_decide) (by evm_ov)
  have rd3392raw := rd3391.add (by native_decide) (by evm_ov)
  have hoff416 : (⟨416⟩ : UInt256) + ⟨0⟩ = ⟨416⟩ := by native_decide
  have hmload416 :
      (if ((⟨416⟩ : UInt256) + ⟨0⟩).toNat ≥ mem.size
          ∨ ((⟨416⟩ : UInt256) + ⟨0⟩) ≥ UInt256.ofNat 18 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
          (mem.readWithPadding (((⟨416⟩ : UInt256) + ⟨0⟩).toNat) 32))) =
        ilkArtNew := by
    rw [hoff416]
    exact mloadWordValue_of_readWithPadding
      (by
        rw [show (⟨416⟩ : UInt256).toNat = 416 from by decide]
        unfold mem frobIlkArtUpdatedMem
        rw [writeWordMem_size_of_contains]
        · unfold frobUrnArtUpdatedMem frobUrnInkUpdatedMem
          rw [writeWordMem_size_of_contains]
          · rw [writeWordMem_size_of_contains]
            · rw [frobIlkLoadedMem_size σ I]; omega
            · rw [frobIlkLoadedMem_size σ I]; omega
          · rw [writeWordMem_size_of_contains]
            · rw [frobIlkLoadedMem_size σ I]; omega
            · rw [frobIlkLoadedMem_size σ I]; omega
        · unfold frobUrnArtUpdatedMem frobUrnInkUpdatedMem
          rw [writeWordMem_size_of_contains]
          · rw [writeWordMem_size_of_contains]
            · rw [frobIlkLoadedMem_size σ I]; omega
            · rw [frobIlkLoadedMem_size σ I]; omega
          · rw [writeWordMem_size_of_contains]
            · rw [frobIlkLoadedMem_size σ I]; omega
            · rw [frobIlkLoadedMem_size σ I]; omega)
      (by native_decide)
      (by
        simpa [show (⟨416⟩ : UInt256).toNat = 416 from by decide, mem]
          using frobIlkArtUpdatedMem_read416 σ I urnInkNew urnArtNew ilkArtNew)
  have rd3392raw' := rd3392raw.mload 0 ilkArtNew (UInt256.ofNat 18)
    (by native_decide) mem_cost hmload416 (by native_decide) (by evm_ov)
  have rd3392 := by
    simpa [hoff416] using rd3392raw'
  have rd3393 := rd3392.dup9 (by native_decide) (by evm_ov)
  have rd3396 := rd3393.push1 ⟨32⟩ (by native_decide) (by evm_ov)
  have rd3397raw := rd3396.add (by native_decide) (by evm_ov)
  have hoff448 : (⟨416⟩ : UInt256) + ⟨32⟩ = ⟨448⟩ := by native_decide
  have hmload448 :
      (if ((⟨416⟩ : UInt256) + ⟨32⟩).toNat ≥ mem.size
          ∨ ((⟨416⟩ : UInt256) + ⟨32⟩) ≥ UInt256.ofNat 18 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
          (mem.readWithPadding (((⟨416⟩ : UInt256) + ⟨32⟩).toNat) 32))) =
        rateOld := by
    rw [hoff448]
    exact mloadWordValue_of_readWithPadding
      (by
        rw [show (⟨448⟩ : UInt256).toNat = 448 from by decide]
        unfold mem frobIlkArtUpdatedMem frobUrnArtUpdatedMem frobUrnInkUpdatedMem
        rw [writeWordMem_size_of_contains]
        · rw [writeWordMem_size_of_contains]
          · rw [writeWordMem_size_of_contains]
            · rw [frobIlkLoadedMem_size σ I]; omega
            · rw [frobIlkLoadedMem_size σ I]; omega
          · rw [writeWordMem_size_of_contains]
            · rw [frobIlkLoadedMem_size σ I]; omega
            · rw [frobIlkLoadedMem_size σ I]; omega
        · rw [writeWordMem_size_of_contains]
          · rw [writeWordMem_size_of_contains]
            · rw [frobIlkLoadedMem_size σ I]; omega
            · rw [frobIlkLoadedMem_size σ I]; omega
          · rw [writeWordMem_size_of_contains]
            · rw [frobIlkLoadedMem_size σ I]; omega
            · rw [frobIlkLoadedMem_size σ I]; omega)
      (by native_decide)
      (by
        simpa [show (⟨448⟩ : UInt256).toNat = 448 from by decide, mem, rateOld]
          using frobIlkArtUpdatedMem_read448 σ I urnInkNew urnArtNew ilkArtNew)
  have rd3397raw' := rd3397raw.mload 0 rateOld (UInt256.ofNat 18)
    (by native_decide) mem_cost hmload448 (by native_decide) (by evm_ov)
  have rd3397 := by
    simpa [hoff448] using rd3397raw'
  have rd3401 := rd3397.push2 ⟨6752⟩ (by native_decide) (by evm_ov)
  have rd6752 := rd3401.jump (by native_decide) (by jump_dest) (by evm_ov)
  obtain ⟨_, _, rd3402raw⟩ := RD.vatCheckedMulUintOk
    (x := rateOld) (y := ilkArtNew) (ret := ⟨3402⟩)
    (R := ilkLine :: (⟨3417⟩ : UInt256) ::
      UInt256.isZero (UInt256.sgt (frobDartWord I) ⟨0⟩) :: (⟨3422⟩ : UInt256) ::
      tab :: dtabWord :: (⟨416⟩ : UInt256) :: (⟨192⟩ : UInt256) ::
      frobDartWord I :: frobDinkWord I :: frobWMaskedWord I ::
      frobVMaskedWord I :: frobUMaskedWord I :: frobIWord I :: ⟨524⟩ :: sel :: [])
    rd6752 (by simpa [rateOld] using hok) (by jump_dest) (by simp)
  have rd3402 := rd3402raw.jumpdest (by native_decide) (by evm_ov)
  have rd3403 := rd3402.gt (by native_decide) (by evm_ov)
  have rd3404 := rd3403.iszero (by native_decide) (by evm_ov)
  have rd3407 := rd3404.push1 ⟨9⟩ (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd3408raw⟩ := rd3407.sload (by native_decide) (by evm_ov)
  have hLineLoad :
      (σDebt.find? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD (⟨9⟩ : UInt256) ⟨0⟩)) = Line := by
    have hne : (⟨9⟩ : UInt256) ≠ foldDebtSlot := by
      simp [foldDebtSlot]
    simpa [σDebt, Line, solcSlotWord] using
      solcSlotWord_sstore_ne σ I ⟨9⟩ foldDebtSlot debtNew hne
  have rd3408 := rd3408raw
  rw [hLineLoad] at rd3408
  have rd3410 := rd3408.push1 ⟨7⟩ (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd3411raw⟩ := rd3410.sload (by native_decide) (by evm_ov)
  have hDebtLoad :
      (σDebt.find? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD (⟨7⟩ : UInt256) ⟨0⟩)) = debtNew := by
    simpa [σDebt, foldDebtSlot] using hdebtLoadStore
  have rd3411 := rd3411raw
  rw [hDebtLoad] at rd3411
  have rd3412 := rd3411.gt (by native_decide) (by evm_ov)
  have rd3413 := rd3412.iszero (by native_decide) (by evm_ov)
  have rd3416 := rd3413.push2 ⟨6787⟩ (by native_decide) (by evm_ov)
  have rd6787 := rd3416.jump (by native_decide) (by jump_dest) (by evm_ov)
  have rd3417 := evm_run rd6787 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw jump (by native_decide) (by jump_dest) (by evm_ov)]
  have rd3421 := evm_run rd3417 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push2 ⟨6791⟩ (by native_decide) (by evm_ov),
    raw jump (by native_decide) (by jump_dest) (by evm_ov)]
  have rd3422 := evm_run rd3421 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw lor (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw jump (by native_decide) (by jump_dest) (by evm_ov)]
  have rd3426 := evm_run rd3422 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push2 ⟨3494⟩ (by native_decide) (by evm_ov)]
  exact ⟨_, _, by
    simpa [σDebt, mem, rateOld, ilkLine, Line, ceilingDebt] using
      rd3426.jumpiT (by native_decide) hceiling (by jump_dest) (by evm_ov)⟩

theorem RD.vatFrobCeilingCheckRevert
    {cA gh bl σ σ₀ A I} {g : Sat256} {k C : ℕ}
    {sel tab dtabWord urnInkNew urnArtNew ilkArtNew debtNew : UInt256}
    (h : RD vatBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3369⟩
      [tab, dtabWord, ⟨416⟩, ⟨192⟩, frobDartWord I, frobDinkWord I,
        frobWMaskedWord I, frobVMaskedWord I, frobUMaskedWord I, frobIWord I,
        ⟨524⟩, sel]
      (frobIlkArtUpdatedMem σ I urnInkNew urnArtNew ilkArtNew) (UInt256.ofNat 18)
      ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ foldDebtSlot debtNew) k C)
    (hok :
      solcSlotWord σ I (frobIlkRateSlot I) = ⟨0⟩ ∨
        UInt256.eq
          (UInt256.div
            (UInt256.mul ilkArtNew (solcSlotWord σ I (frobIlkRateSlot I)))
            (solcSlotWord σ I (frobIlkRateSlot I)))
          ilkArtNew ≠ ⟨0⟩)
    (hceiling :
      UInt256.lor
        (UInt256.land
          (UInt256.isZero
            (UInt256.gt debtNew (solcSlotWord σ I ⟨9⟩)))
          (UInt256.isZero
            (UInt256.gt
              (UInt256.mul ilkArtNew (solcSlotWord σ I (frobIlkRateSlot I)))
              (solcSlotWord σ I (frobIlkLineSlot I)))))
        (UInt256.isZero (UInt256.sgt (frobDartWord I) ⟨0⟩)) = ⟨0⟩)
    (hdebtLoadStore :
      ((sstoreAccountMap I.codeOwner σ foldDebtSlot debtNew).find? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD (⟨7⟩ : UInt256) ⟨0⟩)) = debtNew) :
    RDrev vatBytecode g (initState cA gh bl σ σ₀ g A I) := by
  let σDebt := sstoreAccountMap I.codeOwner σ foldDebtSlot debtNew
  let mem := frobIlkArtUpdatedMem σ I urnInkNew urnArtNew ilkArtNew
  let rateOld := solcSlotWord σ I (frobIlkRateSlot I)
  let ilkLine := solcSlotWord σ I (frobIlkLineSlot I)
  let Line := solcSlotWord σ I ⟨9⟩
  let ceilingDebt := UInt256.mul rateOld ilkArtNew
  have rd3372 := h.push2 ⟨3422⟩ (by native_decide) (by evm_ov)
  have rd3374 := rd3372.push1 ⟨0⟩ (by native_decide) (by evm_ov)
  have rd3375 := rd3374.dup7 (by native_decide) (by evm_ov)
  have rd3376 := rd3375.sgt (by native_decide) (by evm_ov)
  have rd3377 := rd3376.iszero (by native_decide) (by evm_ov)
  have rd3380 := rd3377.push2 ⟨3417⟩ (by native_decide) (by evm_ov)
  have rd3381 := rd3380.dup6 (by native_decide) (by evm_ov)
  have rd3383 := rd3381.push1 ⟨96⟩ (by native_decide) (by evm_ov)
  have rd3384raw := rd3383.add (by native_decide) (by evm_ov)
  have hoff512 : (⟨416⟩ : UInt256) + ⟨96⟩ = ⟨512⟩ := by native_decide
  have hmload512 :
      (if ((⟨416⟩ : UInt256) + ⟨96⟩).toNat ≥ mem.size
          ∨ ((⟨416⟩ : UInt256) + ⟨96⟩) ≥ UInt256.ofNat 18 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
          (mem.readWithPadding (((⟨416⟩ : UInt256) + ⟨96⟩).toNat) 32))) =
        ilkLine := by
    rw [hoff512]
    exact mloadWordValue_of_readWithPadding
      (by
        rw [show (⟨512⟩ : UInt256).toNat = 512 from by decide]
        unfold mem frobIlkArtUpdatedMem frobUrnArtUpdatedMem frobUrnInkUpdatedMem
        rw [writeWordMem_size_of_contains]
        · rw [writeWordMem_size_of_contains]
          · rw [writeWordMem_size_of_contains]
            · rw [frobIlkLoadedMem_size σ I]; omega
            · rw [frobIlkLoadedMem_size σ I]; omega
          · rw [writeWordMem_size_of_contains]
            · rw [frobIlkLoadedMem_size σ I]; omega
            · rw [frobIlkLoadedMem_size σ I]; omega
        · rw [writeWordMem_size_of_contains]
          · rw [writeWordMem_size_of_contains]
            · rw [frobIlkLoadedMem_size σ I]; omega
            · rw [frobIlkLoadedMem_size σ I]; omega
          · rw [writeWordMem_size_of_contains]
            · rw [frobIlkLoadedMem_size σ I]; omega
            · rw [frobIlkLoadedMem_size σ I]; omega)
      (by native_decide)
      (by
        simpa [show (⟨512⟩ : UInt256).toNat = 512 from by decide, mem, ilkLine]
          using frobIlkArtUpdatedMem_read512 σ I urnInkNew urnArtNew ilkArtNew)
  have rd3384raw' := rd3384raw.mload 0 ilkLine (UInt256.ofNat 18)
    (by native_decide) mem_cost hmload512 (by native_decide) (by evm_ov)
  have rd3384 := by
    simpa [hoff512] using rd3384raw'
  have rd3388 := rd3384.push2 ⟨3402⟩ (by native_decide) (by evm_ov)
  have rd3389 := rd3388.dup8 (by native_decide) (by evm_ov)
  have rd3391 := rd3389.push1 ⟨0⟩ (by native_decide) (by evm_ov)
  have rd3392raw := rd3391.add (by native_decide) (by evm_ov)
  have hoff416 : (⟨416⟩ : UInt256) + ⟨0⟩ = ⟨416⟩ := by native_decide
  have hmload416 :
      (if ((⟨416⟩ : UInt256) + ⟨0⟩).toNat ≥ mem.size
          ∨ ((⟨416⟩ : UInt256) + ⟨0⟩) ≥ UInt256.ofNat 18 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
          (mem.readWithPadding (((⟨416⟩ : UInt256) + ⟨0⟩).toNat) 32))) =
        ilkArtNew := by
    rw [hoff416]
    exact mloadWordValue_of_readWithPadding
      (by
        rw [show (⟨416⟩ : UInt256).toNat = 416 from by decide]
        unfold mem frobIlkArtUpdatedMem
        rw [writeWordMem_size_of_contains]
        · unfold frobUrnArtUpdatedMem frobUrnInkUpdatedMem
          rw [writeWordMem_size_of_contains]
          · rw [writeWordMem_size_of_contains]
            · rw [frobIlkLoadedMem_size σ I]; omega
            · rw [frobIlkLoadedMem_size σ I]; omega
          · rw [writeWordMem_size_of_contains]
            · rw [frobIlkLoadedMem_size σ I]; omega
            · rw [frobIlkLoadedMem_size σ I]; omega
        · unfold frobUrnArtUpdatedMem frobUrnInkUpdatedMem
          rw [writeWordMem_size_of_contains]
          · rw [writeWordMem_size_of_contains]
            · rw [frobIlkLoadedMem_size σ I]; omega
            · rw [frobIlkLoadedMem_size σ I]; omega
          · rw [writeWordMem_size_of_contains]
            · rw [frobIlkLoadedMem_size σ I]; omega
            · rw [frobIlkLoadedMem_size σ I]; omega)
      (by native_decide)
      (by
        simpa [show (⟨416⟩ : UInt256).toNat = 416 from by decide, mem]
          using frobIlkArtUpdatedMem_read416 σ I urnInkNew urnArtNew ilkArtNew)
  have rd3392raw' := rd3392raw.mload 0 ilkArtNew (UInt256.ofNat 18)
    (by native_decide) mem_cost hmload416 (by native_decide) (by evm_ov)
  have rd3392 := by
    simpa [hoff416] using rd3392raw'
  have rd3393 := rd3392.dup9 (by native_decide) (by evm_ov)
  have rd3396 := rd3393.push1 ⟨32⟩ (by native_decide) (by evm_ov)
  have rd3397raw := rd3396.add (by native_decide) (by evm_ov)
  have hoff448 : (⟨416⟩ : UInt256) + ⟨32⟩ = ⟨448⟩ := by native_decide
  have hmload448 :
      (if ((⟨416⟩ : UInt256) + ⟨32⟩).toNat ≥ mem.size
          ∨ ((⟨416⟩ : UInt256) + ⟨32⟩) ≥ UInt256.ofNat 18 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
          (mem.readWithPadding (((⟨416⟩ : UInt256) + ⟨32⟩).toNat) 32))) =
        rateOld := by
    rw [hoff448]
    exact mloadWordValue_of_readWithPadding
      (by
        rw [show (⟨448⟩ : UInt256).toNat = 448 from by decide]
        unfold mem frobIlkArtUpdatedMem frobUrnArtUpdatedMem frobUrnInkUpdatedMem
        rw [writeWordMem_size_of_contains]
        · rw [writeWordMem_size_of_contains]
          · rw [writeWordMem_size_of_contains]
            · rw [frobIlkLoadedMem_size σ I]; omega
            · rw [frobIlkLoadedMem_size σ I]; omega
          · rw [writeWordMem_size_of_contains]
            · rw [frobIlkLoadedMem_size σ I]; omega
            · rw [frobIlkLoadedMem_size σ I]; omega
        · rw [writeWordMem_size_of_contains]
          · rw [writeWordMem_size_of_contains]
            · rw [frobIlkLoadedMem_size σ I]; omega
            · rw [frobIlkLoadedMem_size σ I]; omega
          · rw [writeWordMem_size_of_contains]
            · rw [frobIlkLoadedMem_size σ I]; omega
            · rw [frobIlkLoadedMem_size σ I]; omega)
      (by native_decide)
      (by
        simpa [show (⟨448⟩ : UInt256).toNat = 448 from by decide, mem, rateOld]
          using frobIlkArtUpdatedMem_read448 σ I urnInkNew urnArtNew ilkArtNew)
  have rd3397raw' := rd3397raw.mload 0 rateOld (UInt256.ofNat 18)
    (by native_decide) mem_cost hmload448 (by native_decide) (by evm_ov)
  have rd3397 := by
    simpa [hoff448] using rd3397raw'
  have rd3401 := rd3397.push2 ⟨6752⟩ (by native_decide) (by evm_ov)
  have rd6752 := rd3401.jump (by native_decide) (by jump_dest) (by evm_ov)
  obtain ⟨_, _, rd3402raw⟩ := RD.vatCheckedMulUintOk
    (x := rateOld) (y := ilkArtNew) (ret := ⟨3402⟩)
    (R := ilkLine :: (⟨3417⟩ : UInt256) ::
      UInt256.isZero (UInt256.sgt (frobDartWord I) ⟨0⟩) :: (⟨3422⟩ : UInt256) ::
      tab :: dtabWord :: (⟨416⟩ : UInt256) :: (⟨192⟩ : UInt256) ::
      frobDartWord I :: frobDinkWord I :: frobWMaskedWord I ::
      frobVMaskedWord I :: frobUMaskedWord I :: frobIWord I :: ⟨524⟩ :: sel :: [])
    rd6752 (by simpa [rateOld] using hok) (by jump_dest) (by simp)
  have rd3402 := rd3402raw.jumpdest (by native_decide) (by evm_ov)
  have rd3403 := rd3402.gt (by native_decide) (by evm_ov)
  have rd3404 := rd3403.iszero (by native_decide) (by evm_ov)
  have rd3407 := rd3404.push1 ⟨9⟩ (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd3408raw⟩ := rd3407.sload (by native_decide) (by evm_ov)
  have hLineLoad :
      (σDebt.find? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD (⟨9⟩ : UInt256) ⟨0⟩)) = Line := by
    have hne : (⟨9⟩ : UInt256) ≠ foldDebtSlot := by
      simp [foldDebtSlot]
    simpa [σDebt, Line, solcSlotWord] using
      solcSlotWord_sstore_ne σ I ⟨9⟩ foldDebtSlot debtNew hne
  have rd3408 := rd3408raw
  rw [hLineLoad] at rd3408
  have rd3410 := rd3408.push1 ⟨7⟩ (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd3411raw⟩ := rd3410.sload (by native_decide) (by evm_ov)
  have hDebtLoad :
      (σDebt.find? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD (⟨7⟩ : UInt256) ⟨0⟩)) = debtNew := by
    simpa [σDebt, foldDebtSlot] using hdebtLoadStore
  have rd3411 := rd3411raw
  rw [hDebtLoad] at rd3411
  have rd3412 := rd3411.gt (by native_decide) (by evm_ov)
  have rd3413 := rd3412.iszero (by native_decide) (by evm_ov)
  have rd3416 := rd3413.push2 ⟨6787⟩ (by native_decide) (by evm_ov)
  have rd6787 := rd3416.jump (by native_decide) (by jump_dest) (by evm_ov)
  have rd3417 := evm_run rd6787 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw jump (by native_decide) (by jump_dest) (by evm_ov)]
  have rd3421 := evm_run rd3417 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push2 ⟨6791⟩ (by native_decide) (by evm_ov),
    raw jump (by native_decide) (by jump_dest) (by evm_ov)]
  have rd3422 := evm_run rd3421 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw lor (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw jump (by native_decide) (by jump_dest) (by evm_ov)]
  have rd3426 := evm_run rd3422 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push2 ⟨3494⟩ (by native_decide) (by evm_ov)]
  have rdFall := by
    simpa [σDebt, mem, rateOld, ilkLine, Line, ceilingDebt] using
      rd3426.jumpiNT (by native_decide) hceiling (by evm_ov)
  exact RD.solcErrorStringRevertTail576
    (code := vatBytecode) (pc := ⟨3427⟩) (len := ⟨20⟩)
    (rawWord := ⟨123286624931416782702299037100121319580670433625⟩)
    (shift := ⟨98⟩)
    (word := UInt256.shiftLeft
      ⟨123286624931416782702299037100121319580670433625⟩ ⟨98⟩)
    (op := .PUSH20) (width := 20) rdFall
    (by unfold solcErrorStringRevertTailWf; repeat' first | apply And.intro | native_decide)
    (by native_decide) rfl
    (by exact frobIlkArtUpdatedMem_size σ I urnInkNew urnArtNew ilkArtNew)
    (by exact frobIlkArtUpdatedMem_read64 σ I urnInkNew urnArtNew ilkArtNew)
    (by simp only [List.length_cons, List.length_nil]; omega)



theorem RD.vatFrobCeilingMulRevert
    {cA gh bl σ σ₀ A I} {g : Sat256} {k C : ℕ}
    {sel tab dtabWord urnInkNew urnArtNew ilkArtNew debtNew : UInt256}
    (h : RD vatBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3369⟩
      [tab, dtabWord, ⟨416⟩, ⟨192⟩, frobDartWord I, frobDinkWord I,
        frobWMaskedWord I, frobVMaskedWord I, frobUMaskedWord I, frobIWord I,
        ⟨524⟩, sel]
      (frobIlkArtUpdatedMem σ I urnInkNew urnArtNew ilkArtNew) (UInt256.ofNat 18)
      ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ foldDebtSlot debtNew) k C)
    (hfail :
      ¬ (solcSlotWord σ I (frobIlkRateSlot I) = ⟨0⟩ ∨
        UInt256.eq
          (UInt256.div
            (UInt256.mul ilkArtNew (solcSlotWord σ I (frobIlkRateSlot I)))
            (solcSlotWord σ I (frobIlkRateSlot I)))
          ilkArtNew ≠ ⟨0⟩)) :
    RDrev vatBytecode g (initState cA gh bl σ σ₀ g A I) := by
  let σDebt := sstoreAccountMap I.codeOwner σ foldDebtSlot debtNew
  let mem := frobIlkArtUpdatedMem σ I urnInkNew urnArtNew ilkArtNew
  let rateOld := solcSlotWord σ I (frobIlkRateSlot I)
  let ilkLine := solcSlotWord σ I (frobIlkLineSlot I)
  have rd3372 := h.push2 ⟨3422⟩ (by native_decide) (by evm_ov)
  have rd3374 := rd3372.push1 ⟨0⟩ (by native_decide) (by evm_ov)
  have rd3375 := rd3374.dup7 (by native_decide) (by evm_ov)
  have rd3376 := rd3375.sgt (by native_decide) (by evm_ov)
  have rd3377 := rd3376.iszero (by native_decide) (by evm_ov)
  have rd3380 := rd3377.push2 ⟨3417⟩ (by native_decide) (by evm_ov)
  have rd3381 := rd3380.dup6 (by native_decide) (by evm_ov)
  have rd3383 := rd3381.push1 ⟨96⟩ (by native_decide) (by evm_ov)
  have rd3384raw := rd3383.add (by native_decide) (by evm_ov)
  have hoff512 : (⟨416⟩ : UInt256) + ⟨96⟩ = ⟨512⟩ := by native_decide
  have hmload512 :
      (if ((⟨416⟩ : UInt256) + ⟨96⟩).toNat ≥ mem.size
          ∨ ((⟨416⟩ : UInt256) + ⟨96⟩) ≥ UInt256.ofNat 18 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
          (mem.readWithPadding (((⟨416⟩ : UInt256) + ⟨96⟩).toNat) 32))) =
        ilkLine := by
    rw [hoff512]
    exact mloadWordValue_of_readWithPadding
      (by
        rw [show (⟨512⟩ : UInt256).toNat = 512 from by decide]
        unfold mem frobIlkArtUpdatedMem frobUrnArtUpdatedMem frobUrnInkUpdatedMem
        rw [writeWordMem_size_of_contains]
        · rw [writeWordMem_size_of_contains]
          · rw [writeWordMem_size_of_contains]
            · rw [frobIlkLoadedMem_size σ I]; omega
            · rw [frobIlkLoadedMem_size σ I]; omega
          · rw [writeWordMem_size_of_contains]
            · rw [frobIlkLoadedMem_size σ I]; omega
            · rw [frobIlkLoadedMem_size σ I]; omega
        · rw [writeWordMem_size_of_contains]
          · rw [writeWordMem_size_of_contains]
            · rw [frobIlkLoadedMem_size σ I]; omega
            · rw [frobIlkLoadedMem_size σ I]; omega
          · rw [writeWordMem_size_of_contains]
            · rw [frobIlkLoadedMem_size σ I]; omega
            · rw [frobIlkLoadedMem_size σ I]; omega)
      (by native_decide)
      (by
        simpa [show (⟨512⟩ : UInt256).toNat = 512 from by decide, mem, ilkLine]
          using frobIlkArtUpdatedMem_read512 σ I urnInkNew urnArtNew ilkArtNew)
  have rd3384raw' := rd3384raw.mload 0 ilkLine (UInt256.ofNat 18)
    (by native_decide) mem_cost hmload512 (by native_decide) (by evm_ov)
  have rd3384 := by
    simpa [hoff512] using rd3384raw'
  have rd3388 := rd3384.push2 ⟨3402⟩ (by native_decide) (by evm_ov)
  have rd3389 := rd3388.dup8 (by native_decide) (by evm_ov)
  have rd3391 := rd3389.push1 ⟨0⟩ (by native_decide) (by evm_ov)
  have rd3392raw := rd3391.add (by native_decide) (by evm_ov)
  have hoff416 : (⟨416⟩ : UInt256) + ⟨0⟩ = ⟨416⟩ := by native_decide
  have hmload416 :
      (if ((⟨416⟩ : UInt256) + ⟨0⟩).toNat ≥ mem.size
          ∨ ((⟨416⟩ : UInt256) + ⟨0⟩) ≥ UInt256.ofNat 18 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
          (mem.readWithPadding (((⟨416⟩ : UInt256) + ⟨0⟩).toNat) 32))) =
        ilkArtNew := by
    rw [hoff416]
    exact mloadWordValue_of_readWithPadding
      (by
        rw [show (⟨416⟩ : UInt256).toNat = 416 from by decide]
        unfold mem frobIlkArtUpdatedMem
        rw [writeWordMem_size_of_contains]
        · unfold frobUrnArtUpdatedMem frobUrnInkUpdatedMem
          rw [writeWordMem_size_of_contains]
          · rw [writeWordMem_size_of_contains]
            · rw [frobIlkLoadedMem_size σ I]; omega
            · rw [frobIlkLoadedMem_size σ I]; omega
          · rw [writeWordMem_size_of_contains]
            · rw [frobIlkLoadedMem_size σ I]; omega
            · rw [frobIlkLoadedMem_size σ I]; omega
        · unfold frobUrnArtUpdatedMem frobUrnInkUpdatedMem
          rw [writeWordMem_size_of_contains]
          · rw [writeWordMem_size_of_contains]
            · rw [frobIlkLoadedMem_size σ I]; omega
            · rw [frobIlkLoadedMem_size σ I]; omega
          · rw [writeWordMem_size_of_contains]
            · rw [frobIlkLoadedMem_size σ I]; omega
            · rw [frobIlkLoadedMem_size σ I]; omega)
      (by native_decide)
      (by
        simpa [show (⟨416⟩ : UInt256).toNat = 416 from by decide, mem]
          using frobIlkArtUpdatedMem_read416 σ I urnInkNew urnArtNew ilkArtNew)
  have rd3392raw' := rd3392raw.mload 0 ilkArtNew (UInt256.ofNat 18)
    (by native_decide) mem_cost hmload416 (by native_decide) (by evm_ov)
  have rd3392 := by
    simpa [hoff416] using rd3392raw'
  have rd3393 := rd3392.dup9 (by native_decide) (by evm_ov)
  have rd3396 := rd3393.push1 ⟨32⟩ (by native_decide) (by evm_ov)
  have rd3397raw := rd3396.add (by native_decide) (by evm_ov)
  have hoff448 : (⟨416⟩ : UInt256) + ⟨32⟩ = ⟨448⟩ := by native_decide
  have hmload448 :
      (if ((⟨416⟩ : UInt256) + ⟨32⟩).toNat ≥ mem.size
          ∨ ((⟨416⟩ : UInt256) + ⟨32⟩) ≥ UInt256.ofNat 18 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
          (mem.readWithPadding (((⟨416⟩ : UInt256) + ⟨32⟩).toNat) 32))) =
        rateOld := by
    rw [hoff448]
    exact mloadWordValue_of_readWithPadding
      (by
        rw [show (⟨448⟩ : UInt256).toNat = 448 from by decide]
        unfold mem frobIlkArtUpdatedMem frobUrnArtUpdatedMem frobUrnInkUpdatedMem
        rw [writeWordMem_size_of_contains]
        · rw [writeWordMem_size_of_contains]
          · rw [writeWordMem_size_of_contains]
            · rw [frobIlkLoadedMem_size σ I]; omega
            · rw [frobIlkLoadedMem_size σ I]; omega
          · rw [writeWordMem_size_of_contains]
            · rw [frobIlkLoadedMem_size σ I]; omega
            · rw [frobIlkLoadedMem_size σ I]; omega
        · rw [writeWordMem_size_of_contains]
          · rw [writeWordMem_size_of_contains]
            · rw [frobIlkLoadedMem_size σ I]; omega
            · rw [frobIlkLoadedMem_size σ I]; omega
          · rw [writeWordMem_size_of_contains]
            · rw [frobIlkLoadedMem_size σ I]; omega
            · rw [frobIlkLoadedMem_size σ I]; omega)
      (by native_decide)
      (by
        simpa [show (⟨448⟩ : UInt256).toNat = 448 from by decide, mem, rateOld]
          using frobIlkArtUpdatedMem_read448 σ I urnInkNew urnArtNew ilkArtNew)
  have rd3397raw' := rd3397raw.mload 0 rateOld (UInt256.ofNat 18)
    (by native_decide) mem_cost hmload448 (by native_decide) (by evm_ov)
  have rd3397 := by
    simpa [hoff448] using rd3397raw'
  have rd3401 := rd3397.push2 ⟨6752⟩ (by native_decide) (by evm_ov)
  have rd6752 := rd3401.jump (by native_decide) (by jump_dest) (by evm_ov)
  exact RD.vatCheckedMulUintRevert
    (x := rateOld) (y := ilkArtNew) (ret := ⟨3402⟩)
    (R := ilkLine :: (⟨3417⟩ : UInt256) ::
      UInt256.isZero (UInt256.sgt (frobDartWord I) ⟨0⟩) :: (⟨3422⟩ : UInt256) ::
      tab :: dtabWord :: (⟨416⟩ : UInt256) :: (⟨192⟩ : UInt256) ::
      frobDartWord I :: frobDinkWord I :: frobWMaskedWord I ::
      frobVMaskedWord I :: frobUMaskedWord I :: frobIWord I :: ⟨524⟩ :: sel :: [])
    rd6752 (by simpa [rateOld] using hfail) (by simp)

theorem RD.vatFrobSafetyCheckSuccess
    {cA gh bl σ σ₀ A I} {g : Sat256} {k C : ℕ}
    {sel tab dtabWord urnInkNew urnArtNew ilkArtNew debtNew : UInt256}
    (h : RD vatBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3494⟩
      [tab, dtabWord, ⟨416⟩, ⟨192⟩, frobDartWord I, frobDinkWord I,
        frobWMaskedWord I, frobVMaskedWord I, frobUMaskedWord I, frobIWord I,
        ⟨524⟩, sel]
      (frobIlkArtUpdatedMem σ I urnInkNew urnArtNew ilkArtNew) (UInt256.ofNat 18)
      ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ foldDebtSlot debtNew) k C)
    (hok :
      solcSlotWord σ I (frobIlkSpotSlot I) = ⟨0⟩ ∨
        UInt256.eq
          (UInt256.div
            (UInt256.mul urnInkNew (solcSlotWord σ I (frobIlkSpotSlot I)))
            (solcSlotWord σ I (frobIlkSpotSlot I)))
          urnInkNew ≠ ⟨0⟩)
    (hsafe :
      UInt256.lor
        (UInt256.isZero
          (UInt256.gt tab
            (UInt256.mul urnInkNew (solcSlotWord σ I (frobIlkSpotSlot I)))))
        (UInt256.land
          (UInt256.isZero (UInt256.slt (frobDinkWord I) ⟨0⟩))
          (UInt256.isZero (UInt256.sgt (frobDartWord I) ⟨0⟩))) ≠ ⟨0⟩) :
    ∃ k' C',
      RD vatBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3605⟩
        [tab, dtabWord, ⟨416⟩, ⟨192⟩, frobDartWord I, frobDinkWord I,
          frobWMaskedWord I, frobVMaskedWord I, frobUMaskedWord I, frobIWord I,
          ⟨524⟩, sel]
        (frobIlkArtUpdatedMem σ I urnInkNew urnArtNew ilkArtNew) (UInt256.ofNat 18)
        ByteArray.empty
        (cA, sstoreAccountMap I.codeOwner σ foldDebtSlot debtNew) k' C' := by
  let σDebt := sstoreAccountMap I.codeOwner σ foldDebtSlot debtNew
  let mem := frobIlkArtUpdatedMem σ I urnInkNew urnArtNew ilkArtNew
  let ilkSpot := solcSlotWord σ I (frobIlkSpotSlot I)
  let inkSpot := UInt256.mul urnInkNew ilkSpot
  have rd3495 := h.jumpdest (by native_decide) (by evm_ov)
  have rd3498 := rd3495.push2 ⟨3541⟩ (by native_decide) (by evm_ov)
  have rd3501 := rd3498.push2 ⟨3515⟩ (by native_decide) (by evm_ov)
  have rd3503 := rd3501.push1 ⟨0⟩ (by native_decide) (by evm_ov)
  have rd3504 := rd3503.dup8 (by native_decide) (by evm_ov)
  have rd3505 := rd3504.sgt (by native_decide) (by evm_ov)
  have rd3506 := rd3505.iszero (by native_decide) (by evm_ov)
  have rd3508 := rd3506.push1 ⟨0⟩ (by native_decide) (by evm_ov)
  have rd3509 := rd3508.dup10 (by native_decide) (by evm_ov)
  have rd3510 := rd3509.slt (by native_decide) (by evm_ov)
  have rd3511 := rd3510.iszero (by native_decide) (by evm_ov)
  have rd3514 := rd3511.push2 ⟨6787⟩ (by native_decide) (by evm_ov)
  have rd6787 := rd3514.jump (by native_decide) (by jump_dest) (by evm_ov)
  have rd3515 := evm_run rd6787 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw jump (by native_decide) (by jump_dest) (by evm_ov)]
  have rd3516 := rd3515.jumpdest (by native_decide) (by evm_ov)
  have rd3519 := rd3516.push2 ⟨3533⟩ (by native_decide) (by evm_ov)
  have rd3520 := rd3519.dup7 (by native_decide) (by evm_ov)
  have rd3522 := rd3520.push1 ⟨0⟩ (by native_decide) (by evm_ov)
  have rd3523raw := rd3522.add (by native_decide) (by evm_ov)
  have hoff192 : (⟨192⟩ : UInt256) + ⟨0⟩ = ⟨192⟩ := by native_decide
  have hmload192 :
      (if ((⟨192⟩ : UInt256) + ⟨0⟩).toNat ≥ mem.size
          ∨ ((⟨192⟩ : UInt256) + ⟨0⟩) ≥ UInt256.ofNat 18 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
          (mem.readWithPadding (((⟨192⟩ : UInt256) + ⟨0⟩).toNat) 32))) =
        urnInkNew := by
    rw [hoff192]
    exact mloadWordValue_of_readWithPadding
      (by
        rw [show (⟨192⟩ : UInt256).toNat = 192 from by decide]
        unfold mem frobIlkArtUpdatedMem frobUrnArtUpdatedMem frobUrnInkUpdatedMem
        rw [writeWordMem_size_of_contains]
        · rw [writeWordMem_size_of_contains]
          · rw [writeWordMem_size_of_contains]
            · rw [frobIlkLoadedMem_size σ I]; omega
            · rw [frobIlkLoadedMem_size σ I]; omega
          · rw [writeWordMem_size_of_contains]
            · rw [frobIlkLoadedMem_size σ I]; omega
            · rw [frobIlkLoadedMem_size σ I]; omega
        · rw [writeWordMem_size_of_contains]
          · rw [writeWordMem_size_of_contains]
            · rw [frobIlkLoadedMem_size σ I]; omega
            · rw [frobIlkLoadedMem_size σ I]; omega
          · rw [writeWordMem_size_of_contains]
            · rw [frobIlkLoadedMem_size σ I]; omega
            · rw [frobIlkLoadedMem_size σ I]; omega)
      (by native_decide)
      (by
        simpa [show (⟨192⟩ : UInt256).toNat = 192 from by decide, mem]
          using frobIlkArtUpdatedMem_read192 σ I urnInkNew urnArtNew ilkArtNew)
  have rd3523raw' := rd3523raw.mload 0 urnInkNew (UInt256.ofNat 18)
    (by native_decide) mem_cost hmload192 (by native_decide) (by evm_ov)
  have rd3523 := by
    simpa [hoff192] using rd3523raw'
  have rd3524 := rd3523.dup7 (by native_decide) (by evm_ov)
  have rd3527 := rd3524.push1 ⟨64⟩ (by native_decide) (by evm_ov)
  have rd3528raw := rd3527.add (by native_decide) (by evm_ov)
  have hoff480 : (⟨416⟩ : UInt256) + ⟨64⟩ = ⟨480⟩ := by native_decide
  have hmload480 :
      (if ((⟨416⟩ : UInt256) + ⟨64⟩).toNat ≥ mem.size
          ∨ ((⟨416⟩ : UInt256) + ⟨64⟩) ≥ UInt256.ofNat 18 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
          (mem.readWithPadding (((⟨416⟩ : UInt256) + ⟨64⟩).toNat) 32))) =
        ilkSpot := by
    rw [hoff480]
    exact mloadWordValue_of_readWithPadding
      (by
        rw [show (⟨480⟩ : UInt256).toNat = 480 from by decide]
        unfold mem frobIlkArtUpdatedMem frobUrnArtUpdatedMem frobUrnInkUpdatedMem
        rw [writeWordMem_size_of_contains]
        · rw [writeWordMem_size_of_contains]
          · rw [writeWordMem_size_of_contains]
            · rw [frobIlkLoadedMem_size σ I]; omega
            · rw [frobIlkLoadedMem_size σ I]; omega
          · rw [writeWordMem_size_of_contains]
            · rw [frobIlkLoadedMem_size σ I]; omega
            · rw [frobIlkLoadedMem_size σ I]; omega
        · rw [writeWordMem_size_of_contains]
          · rw [writeWordMem_size_of_contains]
            · rw [frobIlkLoadedMem_size σ I]; omega
            · rw [frobIlkLoadedMem_size σ I]; omega
          · rw [writeWordMem_size_of_contains]
            · rw [frobIlkLoadedMem_size σ I]; omega
            · rw [frobIlkLoadedMem_size σ I]; omega)
      (by native_decide)
      (by
        simpa [show (⟨480⟩ : UInt256).toNat = 480 from by decide, mem, ilkSpot]
          using frobIlkArtUpdatedMem_read480 σ I urnInkNew urnArtNew ilkArtNew)
  have rd3528raw' := rd3528raw.mload 0 ilkSpot (UInt256.ofNat 18)
    (by native_decide) mem_cost hmload480 (by native_decide) (by evm_ov)
  have rd3528 := by
    simpa [hoff480] using rd3528raw'
  have rd3532 := rd3528.push2 ⟨6752⟩ (by native_decide) (by evm_ov)
  have rd6752 := rd3532.jump (by native_decide) (by jump_dest) (by evm_ov)
  obtain ⟨_, _, rd3533raw⟩ := RD.vatCheckedMulUintOk
    (x := ilkSpot) (y := urnInkNew) (ret := ⟨3533⟩)
    (R := UInt256.land
      (UInt256.isZero (UInt256.slt (frobDinkWord I) ⟨0⟩))
      (UInt256.isZero (UInt256.sgt (frobDartWord I) ⟨0⟩)) ::
      (⟨3541⟩ : UInt256) :: tab :: dtabWord :: (⟨416⟩ : UInt256) ::
      (⟨192⟩ : UInt256) :: frobDartWord I :: frobDinkWord I ::
      frobWMaskedWord I :: frobVMaskedWord I :: frobUMaskedWord I ::
      frobIWord I :: ⟨524⟩ :: sel :: [])
    rd6752 (by simpa [ilkSpot] using hok) (by jump_dest) (by simp)
  have rd3533 := rd3533raw.jumpdest (by native_decide) (by evm_ov)
  have rd3534 := rd3533.dup4 (by native_decide) (by evm_ov)
  have rd3535 := rd3534.gt (by native_decide) (by evm_ov)
  have rd3536 := rd3535.iszero (by native_decide) (by evm_ov)
  have rd3540 := rd3536.push2 ⟨6791⟩ (by native_decide) (by evm_ov)
  have rd6791 := rd3540.jump (by native_decide) (by jump_dest) (by evm_ov)
  have rd3541 := evm_run rd6791 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw lor (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw jump (by native_decide) (by jump_dest) (by evm_ov)]
  have rd3545 := evm_run rd3541 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push2 ⟨3605⟩ (by native_decide) (by evm_ov)]
  exact ⟨_, _, by
    simpa [σDebt, mem, ilkSpot, inkSpot] using
      rd3545.jumpiT (by native_decide) hsafe (by jump_dest) (by evm_ov)⟩

theorem RD.vatFrobSafetyCheckRevert
    {cA gh bl σ σ₀ A I} {g : Sat256} {k C : ℕ}
    {sel tab dtabWord urnInkNew urnArtNew ilkArtNew debtNew : UInt256}
    (h : RD vatBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3494⟩
      [tab, dtabWord, ⟨416⟩, ⟨192⟩, frobDartWord I, frobDinkWord I,
        frobWMaskedWord I, frobVMaskedWord I, frobUMaskedWord I, frobIWord I,
        ⟨524⟩, sel]
      (frobIlkArtUpdatedMem σ I urnInkNew urnArtNew ilkArtNew) (UInt256.ofNat 18)
      ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ foldDebtSlot debtNew) k C)
    (hok :
      solcSlotWord σ I (frobIlkSpotSlot I) = ⟨0⟩ ∨
        UInt256.eq
          (UInt256.div
            (UInt256.mul urnInkNew (solcSlotWord σ I (frobIlkSpotSlot I)))
            (solcSlotWord σ I (frobIlkSpotSlot I)))
          urnInkNew ≠ ⟨0⟩)
    (hsafe :
      UInt256.lor
        (UInt256.isZero
          (UInt256.gt tab
            (UInt256.mul urnInkNew (solcSlotWord σ I (frobIlkSpotSlot I)))))
        (UInt256.land
          (UInt256.isZero (UInt256.slt (frobDinkWord I) ⟨0⟩))
          (UInt256.isZero (UInt256.sgt (frobDartWord I) ⟨0⟩))) = ⟨0⟩) :
    RDrev vatBytecode g (initState cA gh bl σ σ₀ g A I) := by
  let σDebt := sstoreAccountMap I.codeOwner σ foldDebtSlot debtNew
  let mem := frobIlkArtUpdatedMem σ I urnInkNew urnArtNew ilkArtNew
  let ilkSpot := solcSlotWord σ I (frobIlkSpotSlot I)
  let inkSpot := UInt256.mul urnInkNew ilkSpot
  have rd3495 := h.jumpdest (by native_decide) (by evm_ov)
  have rd3498 := rd3495.push2 ⟨3541⟩ (by native_decide) (by evm_ov)
  have rd3501 := rd3498.push2 ⟨3515⟩ (by native_decide) (by evm_ov)
  have rd3503 := rd3501.push1 ⟨0⟩ (by native_decide) (by evm_ov)
  have rd3504 := rd3503.dup8 (by native_decide) (by evm_ov)
  have rd3505 := rd3504.sgt (by native_decide) (by evm_ov)
  have rd3506 := rd3505.iszero (by native_decide) (by evm_ov)
  have rd3508 := rd3506.push1 ⟨0⟩ (by native_decide) (by evm_ov)
  have rd3509 := rd3508.dup10 (by native_decide) (by evm_ov)
  have rd3510 := rd3509.slt (by native_decide) (by evm_ov)
  have rd3511 := rd3510.iszero (by native_decide) (by evm_ov)
  have rd3514 := rd3511.push2 ⟨6787⟩ (by native_decide) (by evm_ov)
  have rd6787 := rd3514.jump (by native_decide) (by jump_dest) (by evm_ov)
  have rd3515 := evm_run rd6787 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw jump (by native_decide) (by jump_dest) (by evm_ov)]
  have rd3516 := rd3515.jumpdest (by native_decide) (by evm_ov)
  have rd3519 := rd3516.push2 ⟨3533⟩ (by native_decide) (by evm_ov)
  have rd3520 := rd3519.dup7 (by native_decide) (by evm_ov)
  have rd3522 := rd3520.push1 ⟨0⟩ (by native_decide) (by evm_ov)
  have rd3523raw := rd3522.add (by native_decide) (by evm_ov)
  have hoff192 : (⟨192⟩ : UInt256) + ⟨0⟩ = ⟨192⟩ := by native_decide
  have hmload192 :
      (if ((⟨192⟩ : UInt256) + ⟨0⟩).toNat ≥ mem.size
          ∨ ((⟨192⟩ : UInt256) + ⟨0⟩) ≥ UInt256.ofNat 18 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
          (mem.readWithPadding (((⟨192⟩ : UInt256) + ⟨0⟩).toNat) 32))) =
        urnInkNew := by
    rw [hoff192]
    exact mloadWordValue_of_readWithPadding
      (by
        rw [show (⟨192⟩ : UInt256).toNat = 192 from by decide]
        unfold mem frobIlkArtUpdatedMem frobUrnArtUpdatedMem frobUrnInkUpdatedMem
        rw [writeWordMem_size_of_contains]
        · rw [writeWordMem_size_of_contains]
          · rw [writeWordMem_size_of_contains]
            · rw [frobIlkLoadedMem_size σ I]; omega
            · rw [frobIlkLoadedMem_size σ I]; omega
          · rw [writeWordMem_size_of_contains]
            · rw [frobIlkLoadedMem_size σ I]; omega
            · rw [frobIlkLoadedMem_size σ I]; omega
        · rw [writeWordMem_size_of_contains]
          · rw [writeWordMem_size_of_contains]
            · rw [frobIlkLoadedMem_size σ I]; omega
            · rw [frobIlkLoadedMem_size σ I]; omega
          · rw [writeWordMem_size_of_contains]
            · rw [frobIlkLoadedMem_size σ I]; omega
            · rw [frobIlkLoadedMem_size σ I]; omega)
      (by native_decide)
      (by
        simpa [show (⟨192⟩ : UInt256).toNat = 192 from by decide, mem]
          using frobIlkArtUpdatedMem_read192 σ I urnInkNew urnArtNew ilkArtNew)
  have rd3523raw' := rd3523raw.mload 0 urnInkNew (UInt256.ofNat 18)
    (by native_decide) mem_cost hmload192 (by native_decide) (by evm_ov)
  have rd3523 := by
    simpa [hoff192] using rd3523raw'
  have rd3524 := rd3523.dup7 (by native_decide) (by evm_ov)
  have rd3527 := rd3524.push1 ⟨64⟩ (by native_decide) (by evm_ov)
  have rd3528raw := rd3527.add (by native_decide) (by evm_ov)
  have hoff480 : (⟨416⟩ : UInt256) + ⟨64⟩ = ⟨480⟩ := by native_decide
  have hmload480 :
      (if ((⟨416⟩ : UInt256) + ⟨64⟩).toNat ≥ mem.size
          ∨ ((⟨416⟩ : UInt256) + ⟨64⟩) ≥ UInt256.ofNat 18 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
          (mem.readWithPadding (((⟨416⟩ : UInt256) + ⟨64⟩).toNat) 32))) =
        ilkSpot := by
    rw [hoff480]
    exact mloadWordValue_of_readWithPadding
      (by
        rw [show (⟨480⟩ : UInt256).toNat = 480 from by decide]
        unfold mem frobIlkArtUpdatedMem frobUrnArtUpdatedMem frobUrnInkUpdatedMem
        rw [writeWordMem_size_of_contains]
        · rw [writeWordMem_size_of_contains]
          · rw [writeWordMem_size_of_contains]
            · rw [frobIlkLoadedMem_size σ I]; omega
            · rw [frobIlkLoadedMem_size σ I]; omega
          · rw [writeWordMem_size_of_contains]
            · rw [frobIlkLoadedMem_size σ I]; omega
            · rw [frobIlkLoadedMem_size σ I]; omega
        · rw [writeWordMem_size_of_contains]
          · rw [writeWordMem_size_of_contains]
            · rw [frobIlkLoadedMem_size σ I]; omega
            · rw [frobIlkLoadedMem_size σ I]; omega
          · rw [writeWordMem_size_of_contains]
            · rw [frobIlkLoadedMem_size σ I]; omega
            · rw [frobIlkLoadedMem_size σ I]; omega)
      (by native_decide)
      (by
        simpa [show (⟨480⟩ : UInt256).toNat = 480 from by decide, mem, ilkSpot]
          using frobIlkArtUpdatedMem_read480 σ I urnInkNew urnArtNew ilkArtNew)
  have rd3528raw' := rd3528raw.mload 0 ilkSpot (UInt256.ofNat 18)
    (by native_decide) mem_cost hmload480 (by native_decide) (by evm_ov)
  have rd3528 := by
    simpa [hoff480] using rd3528raw'
  have rd3532 := rd3528.push2 ⟨6752⟩ (by native_decide) (by evm_ov)
  have rd6752 := rd3532.jump (by native_decide) (by jump_dest) (by evm_ov)
  obtain ⟨_, _, rd3533raw⟩ := RD.vatCheckedMulUintOk
    (x := ilkSpot) (y := urnInkNew) (ret := ⟨3533⟩)
    (R := UInt256.land
      (UInt256.isZero (UInt256.slt (frobDinkWord I) ⟨0⟩))
      (UInt256.isZero (UInt256.sgt (frobDartWord I) ⟨0⟩)) ::
      (⟨3541⟩ : UInt256) :: tab :: dtabWord :: (⟨416⟩ : UInt256) ::
      (⟨192⟩ : UInt256) :: frobDartWord I :: frobDinkWord I ::
      frobWMaskedWord I :: frobVMaskedWord I :: frobUMaskedWord I ::
      frobIWord I :: ⟨524⟩ :: sel :: [])
    rd6752 (by simpa [ilkSpot] using hok) (by jump_dest) (by simp)
  have rd3533 := rd3533raw.jumpdest (by native_decide) (by evm_ov)
  have rd3534 := rd3533.dup4 (by native_decide) (by evm_ov)
  have rd3535 := rd3534.gt (by native_decide) (by evm_ov)
  have rd3536 := rd3535.iszero (by native_decide) (by evm_ov)
  have rd3540 := rd3536.push2 ⟨6791⟩ (by native_decide) (by evm_ov)
  have rd6791 := rd3540.jump (by native_decide) (by jump_dest) (by evm_ov)
  have rd3541 := evm_run rd6791 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw lor (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw jump (by native_decide) (by jump_dest) (by evm_ov)]
  have rd3545 := evm_run rd3541 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push2 ⟨3605⟩ (by native_decide) (by evm_ov)]
  have rdFall := by
    simpa [σDebt, mem, ilkSpot, inkSpot] using
      rd3545.jumpiNT (by native_decide) hsafe (by evm_ov)
  exact RD.solcErrorStringRevertTail576
    (code := vatBytecode) (pc := ⟨3546⟩) (len := ⟨12⟩)
    (rawWord := ⟨26733525318604986088616453733⟩) (shift := ⟨160⟩)
    (word := UInt256.shiftLeft ⟨26733525318604986088616453733⟩ ⟨160⟩)
    (op := .PUSH12) (width := 12) rdFall
    (by unfold solcErrorStringRevertTailWf; repeat' first | apply And.intro | native_decide)
    (by native_decide) rfl
    (by exact frobIlkArtUpdatedMem_size σ I urnInkNew urnArtNew ilkArtNew)
    (by exact frobIlkArtUpdatedMem_read64 σ I urnInkNew urnArtNew ilkArtNew)
    (by simp only [List.length_cons, List.length_nil]; omega)



theorem RD.vatFrobInkSpotMulRevert
    {cA gh bl σ σ₀ A I} {g : Sat256} {k C : ℕ}
    {sel tab dtabWord urnInkNew urnArtNew ilkArtNew debtNew : UInt256}
    (h : RD vatBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3494⟩
      [tab, dtabWord, ⟨416⟩, ⟨192⟩, frobDartWord I, frobDinkWord I,
        frobWMaskedWord I, frobVMaskedWord I, frobUMaskedWord I, frobIWord I,
        ⟨524⟩, sel]
      (frobIlkArtUpdatedMem σ I urnInkNew urnArtNew ilkArtNew) (UInt256.ofNat 18)
      ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ foldDebtSlot debtNew) k C)
    (hfail :
      ¬ (solcSlotWord σ I (frobIlkSpotSlot I) = ⟨0⟩ ∨
        UInt256.eq
          (UInt256.div
            (UInt256.mul urnInkNew (solcSlotWord σ I (frobIlkSpotSlot I)))
            (solcSlotWord σ I (frobIlkSpotSlot I)))
          urnInkNew ≠ ⟨0⟩)) :
    RDrev vatBytecode g (initState cA gh bl σ σ₀ g A I) := by
  let mem := frobIlkArtUpdatedMem σ I urnInkNew urnArtNew ilkArtNew
  let ilkSpot := solcSlotWord σ I (frobIlkSpotSlot I)
  have rd3495 := h.jumpdest (by native_decide) (by evm_ov)
  have rd3498 := rd3495.push2 ⟨3541⟩ (by native_decide) (by evm_ov)
  have rd3501 := rd3498.push2 ⟨3515⟩ (by native_decide) (by evm_ov)
  have rd3503 := rd3501.push1 ⟨0⟩ (by native_decide) (by evm_ov)
  have rd3504 := rd3503.dup8 (by native_decide) (by evm_ov)
  have rd3505 := rd3504.sgt (by native_decide) (by evm_ov)
  have rd3506 := rd3505.iszero (by native_decide) (by evm_ov)
  have rd3508 := rd3506.push1 ⟨0⟩ (by native_decide) (by evm_ov)
  have rd3509 := rd3508.dup10 (by native_decide) (by evm_ov)
  have rd3510 := rd3509.slt (by native_decide) (by evm_ov)
  have rd3511 := rd3510.iszero (by native_decide) (by evm_ov)
  have rd3514 := rd3511.push2 ⟨6787⟩ (by native_decide) (by evm_ov)
  have rd6787 := rd3514.jump (by native_decide) (by jump_dest) (by evm_ov)
  have rd3515 := evm_run rd6787 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw jump (by native_decide) (by jump_dest) (by evm_ov)]
  have rd3516 := rd3515.jumpdest (by native_decide) (by evm_ov)
  have rd3519 := rd3516.push2 ⟨3533⟩ (by native_decide) (by evm_ov)
  have rd3520 := rd3519.dup7 (by native_decide) (by evm_ov)
  have rd3522 := rd3520.push1 ⟨0⟩ (by native_decide) (by evm_ov)
  have rd3523raw := rd3522.add (by native_decide) (by evm_ov)
  have hoff192 : (⟨192⟩ : UInt256) + ⟨0⟩ = ⟨192⟩ := by native_decide
  have hmload192 :
      (if ((⟨192⟩ : UInt256) + ⟨0⟩).toNat ≥ mem.size
          ∨ ((⟨192⟩ : UInt256) + ⟨0⟩) ≥ UInt256.ofNat 18 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
          (mem.readWithPadding (((⟨192⟩ : UInt256) + ⟨0⟩).toNat) 32))) =
        urnInkNew := by
    rw [hoff192]
    exact mloadWordValue_of_readWithPadding
      (by
        rw [show (⟨192⟩ : UInt256).toNat = 192 from by decide]
        unfold mem frobIlkArtUpdatedMem frobUrnArtUpdatedMem frobUrnInkUpdatedMem
        rw [writeWordMem_size_of_contains]
        · rw [writeWordMem_size_of_contains]
          · rw [writeWordMem_size_of_contains]
            · rw [frobIlkLoadedMem_size σ I]; omega
            · rw [frobIlkLoadedMem_size σ I]; omega
          · rw [writeWordMem_size_of_contains]
            · rw [frobIlkLoadedMem_size σ I]; omega
            · rw [frobIlkLoadedMem_size σ I]; omega
        · rw [writeWordMem_size_of_contains]
          · rw [writeWordMem_size_of_contains]
            · rw [frobIlkLoadedMem_size σ I]; omega
            · rw [frobIlkLoadedMem_size σ I]; omega
          · rw [writeWordMem_size_of_contains]
            · rw [frobIlkLoadedMem_size σ I]; omega
            · rw [frobIlkLoadedMem_size σ I]; omega)
      (by native_decide)
      (by
        simpa [show (⟨192⟩ : UInt256).toNat = 192 from by decide, mem]
          using frobIlkArtUpdatedMem_read192 σ I urnInkNew urnArtNew ilkArtNew)
  have rd3523raw' := rd3523raw.mload 0 urnInkNew (UInt256.ofNat 18)
    (by native_decide) mem_cost hmload192 (by native_decide) (by evm_ov)
  have rd3523 := by
    simpa [hoff192] using rd3523raw'
  have rd3524 := rd3523.dup7 (by native_decide) (by evm_ov)
  have rd3527 := rd3524.push1 ⟨64⟩ (by native_decide) (by evm_ov)
  have rd3528raw := rd3527.add (by native_decide) (by evm_ov)
  have hoff480 : (⟨416⟩ : UInt256) + ⟨64⟩ = ⟨480⟩ := by native_decide
  have hmload480 :
      (if ((⟨416⟩ : UInt256) + ⟨64⟩).toNat ≥ mem.size
          ∨ ((⟨416⟩ : UInt256) + ⟨64⟩) ≥ UInt256.ofNat 18 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
          (mem.readWithPadding (((⟨416⟩ : UInt256) + ⟨64⟩).toNat) 32))) =
        ilkSpot := by
    rw [hoff480]
    exact mloadWordValue_of_readWithPadding
      (by
        rw [show (⟨480⟩ : UInt256).toNat = 480 from by decide]
        unfold mem frobIlkArtUpdatedMem frobUrnArtUpdatedMem frobUrnInkUpdatedMem
        rw [writeWordMem_size_of_contains]
        · rw [writeWordMem_size_of_contains]
          · rw [writeWordMem_size_of_contains]
            · rw [frobIlkLoadedMem_size σ I]; omega
            · rw [frobIlkLoadedMem_size σ I]; omega
          · rw [writeWordMem_size_of_contains]
            · rw [frobIlkLoadedMem_size σ I]; omega
            · rw [frobIlkLoadedMem_size σ I]; omega
        · rw [writeWordMem_size_of_contains]
          · rw [writeWordMem_size_of_contains]
            · rw [frobIlkLoadedMem_size σ I]; omega
            · rw [frobIlkLoadedMem_size σ I]; omega
          · rw [writeWordMem_size_of_contains]
            · rw [frobIlkLoadedMem_size σ I]; omega
            · rw [frobIlkLoadedMem_size σ I]; omega)
      (by native_decide)
      (by
        simpa [show (⟨480⟩ : UInt256).toNat = 480 from by decide, mem, ilkSpot]
          using frobIlkArtUpdatedMem_read480 σ I urnInkNew urnArtNew ilkArtNew)
  have rd3528raw' := rd3528raw.mload 0 ilkSpot (UInt256.ofNat 18)
    (by native_decide) mem_cost hmload480 (by native_decide) (by evm_ov)
  have rd3528 := by
    simpa [hoff480] using rd3528raw'
  have rd3532 := rd3528.push2 ⟨6752⟩ (by native_decide) (by evm_ov)
  have rd6752 := rd3532.jump (by native_decide) (by jump_dest) (by evm_ov)
  exact RD.vatCheckedMulUintRevert
    (x := ilkSpot) (y := urnInkNew) (ret := ⟨3533⟩)
    (R := UInt256.land
      (UInt256.isZero (UInt256.slt (frobDinkWord I) ⟨0⟩))
      (UInt256.isZero (UInt256.sgt (frobDartWord I) ⟨0⟩)) ::
      (⟨3541⟩ : UInt256) :: tab :: dtabWord :: (⟨416⟩ : UInt256) ::
      (⟨192⟩ : UInt256) :: frobDartWord I :: frobDinkWord I ::
      frobWMaskedWord I :: frobVMaskedWord I :: frobUMaskedWord I ::
      frobIWord I :: ⟨524⟩ :: sel :: [])
    rd6752 (by simpa [ilkSpot] using hfail) (by simp)

set_option maxHeartbeats 1000000 in
theorem RD.vatWishLoadedAt6557
    {cA gh bl σ σ₀ A I} {g : Sat256} {k C : ℕ}
    {σacc : AccountMap}
    {usr slot ret : UInt256} {R : List UInt256} {mem : ByteArray}
    (h : RD vatBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨6557⟩
      (UInt256.ofNat I.source.val :: usr :: ret :: R)
      mem (UInt256.ofNat 18) ByteArray.empty (cA, σacc) k C)
    (hmem64 : 64 ≤ mem.size)
    (hclean : UInt256.land solcAddrMask usr = usr)
    (hslot : slot = solcMappingSlot (solcMappingSlot ⟨1⟩ usr) (hopeSourceWord I))
    (hov : R.length + 12 ≤ 1024) :
    ∃ k' C', RD vatBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨6599⟩
      (vatSlotWord slot σacc I :: ⟨1⟩ :: ⟨0⟩ :: usr :: hopeSourceWord I ::
        UInt256.ofNat I.source.val :: usr :: ret :: R)
      (twoWordHashMem (hopeSourceWord I) (solcMappingSlot ⟨1⟩ usr)
        (twoWordHashMem usr ⟨1⟩ mem))
      (UInt256.ofNat 18) ByteArray.empty (cA, σacc) k' C' := by
  have rd6568raw := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov)]
  have hmask :
      UInt256.land
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩)
          usr =
        usr := by
    rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by decide]
    exact hclean
  have rd6568 := rd6568raw
  rw [hmask] at rd6568
  have rd6573pre := evm_run rd6568 with [
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd6573 := rd6573pre.mstore 0 (wordAt0Mem usr mem)
    (UInt256.ofNat 18) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd6580pre := evm_run rd6573 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd6580 := rd6580pre.mstore 0
    (twoWordHashMem usr ⟨1⟩ mem)
    (UInt256.ofNat 18) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd6585pre := evm_run rd6580 with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw dup5 (by native_decide) (by evm_ov)]
  have hinner :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((twoWordHashMem usr ⟨1⟩ mem)
            |>.readWithPadding 0 64))) =
        solcMappingSlot ⟨1⟩ usr :=
    twoWordHashMem_solcMappingSlot_of_ge64 ⟨1⟩ usr hmem64
  have rd6585 := rd6585pre.keccak256 0
    (solcMappingSlot ⟨1⟩ usr) (UInt256.ofNat 18)
    (by native_decide) mem_cost hinner (by native_decide) (by evm_ov)
  have rd6588raw := evm_run rd6585 with [
    raw swap6 (by native_decide) (by evm_ov),
    raw dup8 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov)]
  have hcallerMask :
      UInt256.land (UInt256.ofNat I.source.val)
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩) =
        hopeSourceWord I := by
    rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by decide]
    rw [u256_land_comm]
    change UInt256.land solcAddrMask (hopeSourceWord I) = hopeSourceWord I
    exact solcAddrMask_clean_left (by
      rw [hopeSourceWord_toNat]
      exact I.source.isLt)
  have rd6588 := rd6588raw
  rw [hcallerMask] at rd6588
  have rd6591pre := evm_run rd6588 with [
    raw dup1 (by native_decide) (by evm_ov),
    raw dup6 (by native_decide) (by evm_ov)]
  have rd6591 := rd6591pre.mstore 0
    (wordAt0Mem (hopeSourceWord I)
      (twoWordHashMem usr ⟨1⟩ mem))
    (UInt256.ofNat 18) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd6595pre := evm_run rd6591 with [
    raw swap6 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov)]
  have rd6595 := rd6595pre.mstore 0
    (twoWordHashMem (hopeSourceWord I) (solcMappingSlot ⟨1⟩ usr)
      (twoWordHashMem usr ⟨1⟩ mem))
    (UInt256.ofNat 18) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd6597pre := evm_run rd6595 with [
    raw dup3 (by native_decide) (by evm_ov)]
  have houter :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((twoWordHashMem (hopeSourceWord I)
            (solcMappingSlot ⟨1⟩ usr)
            (twoWordHashMem usr ⟨1⟩ mem)).readWithPadding 0 64))) =
        slot := by
    rw [hslot]
    exact twoWordHashMem_solcMappingSlot_of_ge64 (solcMappingSlot ⟨1⟩ usr)
      (hopeSourceWord I)
      (by rw [twoWordHashMem_size_of_ge64 usr ⟨1⟩ hmem64]; omega)
  have rd6597 := rd6597pre.keccak256 0 slot (UInt256.ofNat 18)
    (by native_decide) mem_cost houter (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd6599raw⟩ := rd6597.sload (by native_decide) (by evm_ov)
  exact ⟨_, _, by simpa [vatSlotWord, solcSlotWord] using rd6599raw⟩

set_option maxHeartbeats 1000000 in
theorem RD.vatWishReturnOk
    {cA gh bl σ σ₀ A I} {g : Sat256} {k C : ℕ}
    {σacc : AccountMap}
    {usr slot ret activeWords : UInt256} {R : List UInt256} {mem : ByteArray}
    (h : RD vatBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨6599⟩
      (vatSlotWord slot σacc I :: ⟨1⟩ :: ⟨0⟩ :: usr :: hopeSourceWord I ::
        UInt256.ofNat I.source.val :: usr :: ret :: R)
      mem activeWords ByteArray.empty (cA, σacc) k C)
    (hret : (D_J vatBytecode 0).contains ret = true)
    (hov : R.length + 9 ≤ 1024) :
    ∃ k' C', RD vatBytecode I g (initState cA gh bl σ σ₀ g A I) ret
      (UInt256.lor
        (UInt256.eq (vatSlotWord slot σacc I) ⟨1⟩)
        (UInt256.eq usr (hopeSourceWord I)) :: R)
      mem activeWords ByteArray.empty (cA, σacc) k' C' := by
  have rd6608pre := evm_run h with [
    raw swap2 (by native_decide) (by evm_ov),
    raw swap4 (by native_decide) (by evm_ov),
    raw push2 ⟨6612⟩ (by native_decide) (by evm_ov),
    raw swap4 (by native_decide) (by evm_ov)]
  have rd6605 := rd6608pre.eq (by native_decide) (by evm_ov)
  have rd6608mid := evm_run rd6605 with [
    raw swap2 (by native_decide) (by evm_ov)]
  have rd6608 := rd6608mid.eq (by native_decide) (by evm_ov)
  have rd6791 := evm_run rd6608 with [
    raw push2 ⟨6791⟩ (by native_decide) (by evm_ov),
    raw jump (by native_decide) (by jump_dest) (by evm_ov)]
  have rd6792 := evm_run rd6791 with [
    raw jumpdest (by native_decide) (by evm_ov)]
  have rd6793 := rd6792.lor (by native_decide) (by evm_ov)
  have rd6612raw := evm_run rd6793 with [
    raw swap1 (by native_decide) (by evm_ov),
    raw jump (by native_decide) (by jump_dest) (by evm_ov)]
  have rd6620 := evm_run rd6612raw with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw jumpdest (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov)]
  exact ⟨_, _, rd6620.jump (by native_decide) hret (by evm_ov)⟩

set_option maxHeartbeats 1000000 in
theorem RD.vatFrobUWishCheckSuccess
    {cA gh bl σ σ₀ A I} {g : Sat256} {k C : ℕ}
    {sel tab dtabWord urnInkNew urnArtNew ilkArtNew debtNew : UInt256}
    (h : RD vatBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3605⟩
      [tab, dtabWord, ⟨416⟩, ⟨192⟩, frobDartWord I, frobDinkWord I,
        frobWMaskedWord I, frobVMaskedWord I, frobUMaskedWord I, frobIWord I,
        ⟨524⟩, sel]
      (frobIlkArtUpdatedMem σ I urnInkNew urnArtNew ilkArtNew) (UInt256.ofNat 18)
      ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ foldDebtSlot debtNew) k C)
    (hwish :
      UInt256.lor
        (UInt256.lor
          (UInt256.eq (vatSlotWord (frobUWishSlot I)
            (sstoreAccountMap I.codeOwner σ foldDebtSlot debtNew) I) ⟨1⟩)
          (UInt256.eq (frobUMaskedWord I) (hopeSourceWord I)))
        (UInt256.land
          (UInt256.isZero (UInt256.slt (frobDinkWord I) ⟨0⟩))
          (UInt256.isZero (UInt256.sgt (frobDartWord I) ⟨0⟩))) ≠ ⟨0⟩) :
    ∃ k' C',
      RD vatBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3705⟩
        [tab, dtabWord, ⟨416⟩, ⟨192⟩, frobDartWord I, frobDinkWord I,
          frobWMaskedWord I, frobVMaskedWord I, frobUMaskedWord I, frobIWord I,
          ⟨524⟩, sel]
        (twoWordHashMem (hopeSourceWord I) (solcMappingSlot ⟨1⟩ (frobUMaskedWord I))
          (twoWordHashMem (frobUMaskedWord I) ⟨1⟩
            (frobIlkArtUpdatedMem σ I urnInkNew urnArtNew ilkArtNew)))
        (UInt256.ofNat 18) ByteArray.empty
        (cA, sstoreAccountMap I.codeOwner σ foldDebtSlot debtNew) k' C' := by
  let σDebt := sstoreAccountMap I.codeOwner σ foldDebtSlot debtNew
  let mem := frobIlkArtUpdatedMem σ I urnInkNew urnArtNew ilkArtNew
  let both :=
    UInt256.land
      (UInt256.isZero (UInt256.slt (frobDinkWord I) ⟨0⟩))
      (UInt256.isZero (UInt256.sgt (frobDartWord I) ⟨0⟩))
  let wish :=
    UInt256.lor
      (UInt256.eq (vatSlotWord (frobUWishSlot I) σDebt I) ⟨1⟩)
      (UInt256.eq (frobUMaskedWord I) (hopeSourceWord I))
  have rd3606 := h.jumpdest (by native_decide) (by evm_ov)
  have rd3609 := rd3606.push2 ⟨3636⟩ (by native_decide) (by evm_ov)
  have rd3612 := rd3609.push2 ⟨3626⟩ (by native_decide) (by evm_ov)
  have rd3614 := rd3612.push1 ⟨0⟩ (by native_decide) (by evm_ov)
  have rd3615 := rd3614.dup8 (by native_decide) (by evm_ov)
  have rd3616 := rd3615.sgt (by native_decide) (by evm_ov)
  have rd3617 := rd3616.iszero (by native_decide) (by evm_ov)
  have rd3619 := rd3617.push1 ⟨0⟩ (by native_decide) (by evm_ov)
  have rd3620 := rd3619.dup10 (by native_decide) (by evm_ov)
  have rd3621 := rd3620.slt (by native_decide) (by evm_ov)
  have rd3622 := rd3621.iszero (by native_decide) (by evm_ov)
  have rd3625 := rd3622.push2 ⟨6787⟩ (by native_decide) (by evm_ov)
  have rd6787 := rd3625.jump (by native_decide) (by jump_dest) (by evm_ov)
  have rd3626 := evm_run rd6787 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw jump (by native_decide) (by jump_dest) (by evm_ov),
    raw jumpdest (by native_decide) (by evm_ov)]
  have rd3627 := rd3626.push2 ⟨3417⟩ (by native_decide) (by evm_ov)
  have rd6557 := evm_run rd3627 with [
    raw dup12 (by native_decide) (by evm_ov),
    raw caller (by native_decide) (by evm_ov),
    raw push2 ⟨6557⟩ (by native_decide) (by evm_ov),
    raw jump (by native_decide) (by jump_dest) (by evm_ov)]
  obtain ⟨_, _, rd6599⟩ := RD.vatWishLoadedAt6557
    (σacc := σDebt)
    (usr := frobUMaskedWord I) (slot := frobUWishSlot I) (ret := ⟨3417⟩)
    (R := both :: (⟨3636⟩ : UInt256) :: tab :: dtabWord :: (⟨416⟩ : UInt256) ::
      (⟨192⟩ : UInt256) :: frobDartWord I :: frobDinkWord I ::
      frobWMaskedWord I :: frobVMaskedWord I :: frobUMaskedWord I ::
      frobIWord I :: ⟨524⟩ :: sel :: [])
    (mem := mem) (by simpa [mem, both] using rd6557)
    (by exact frobIlkArtUpdatedMem_ge64 σ I urnInkNew urnArtNew ilkArtNew)
    (by rw [u256_land_comm]; exact frobUMaskedWord_clean I)
    (by rfl) (by simp)
  obtain ⟨_, _, rd3417⟩ := RD.vatWishReturnOk
    (σacc := σDebt)
    (usr := frobUMaskedWord I) (slot := frobUWishSlot I) (ret := ⟨3417⟩)
    (activeWords := UInt256.ofNat 18)
    (R := both :: (⟨3636⟩ : UInt256) :: tab :: dtabWord :: (⟨416⟩ : UInt256) ::
      (⟨192⟩ : UInt256) :: frobDartWord I :: frobDinkWord I ::
      frobWMaskedWord I :: frobVMaskedWord I :: frobUMaskedWord I ::
      frobIWord I :: ⟨524⟩ :: sel :: [])
    rd6599 (by jump_dest) (by simp)
  have rd3636 := evm_run rd3417 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push2 ⟨6791⟩ (by native_decide) (by evm_ov),
    raw jump (by native_decide) (by jump_dest) (by evm_ov),
    raw jumpdest (by native_decide) (by evm_ov),
    raw lor (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw jump (by native_decide) (by jump_dest) (by evm_ov)]
  have rd3640 := evm_run rd3636 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push2 ⟨3705⟩ (by native_decide) (by evm_ov)]
  exact ⟨_, _, by
    simpa [σDebt, mem, both, wish, frobUWishSlot] using
      rd3640.jumpiT (by native_decide) hwish (by jump_dest) (by evm_ov)⟩

set_option maxRecDepth 4096 in
set_option maxHeartbeats 5000000 in
theorem RD.vatFrobUWishCheckRevertFall
    {cA gh bl σ σ₀ A I} {g : Sat256} {k C : ℕ}
    {sel tab dtabWord urnInkNew urnArtNew ilkArtNew debtNew : UInt256}
    {σDebt : AccountMap} {mem : ByteArray}
    (hσDebt : σDebt = sstoreAccountMap I.codeOwner σ foldDebtSlot debtNew)
    (hmem : mem = frobIlkArtUpdatedMem σ I urnInkNew urnArtNew ilkArtNew)
    (h : RD vatBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3605⟩
      [tab, dtabWord, ⟨416⟩, ⟨192⟩, frobDartWord I, frobDinkWord I,
        frobWMaskedWord I, frobVMaskedWord I, frobUMaskedWord I, frobIWord I,
        ⟨524⟩, sel]
      mem (UInt256.ofNat 18) ByteArray.empty (cA, σDebt) k C)
    (hwish :
      UInt256.lor
        (UInt256.lor
          (UInt256.eq (vatSlotWord (frobUWishSlot I) σDebt I) ⟨1⟩)
          (UInt256.eq (frobUMaskedWord I) (hopeSourceWord I)))
        (UInt256.land
          (UInt256.isZero (UInt256.slt (frobDinkWord I) ⟨0⟩))
          (UInt256.isZero (UInt256.sgt (frobDartWord I) ⟨0⟩))) = ⟨0⟩) :
    ∃ k' C',
      RD vatBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3641⟩
        [tab, dtabWord, ⟨416⟩, ⟨192⟩, frobDartWord I,
          frobDinkWord I, frobWMaskedWord I, frobVMaskedWord I,
          frobUMaskedWord I, frobIWord I, ⟨524⟩, sel]
        (twoWordHashMem (hopeSourceWord I) (solcMappingSlot ⟨1⟩ (frobUMaskedWord I))
          (twoWordHashMem (frobUMaskedWord I) ⟨1⟩ mem))
        (UInt256.ofNat 18) ByteArray.empty (cA, σDebt) k' C' := by
  let both :=
    UInt256.land
      (UInt256.isZero (UInt256.slt (frobDinkWord I) ⟨0⟩))
      (UInt256.isZero (UInt256.sgt (frobDartWord I) ⟨0⟩))
  let wish :=
    UInt256.lor
      (UInt256.eq (vatSlotWord (frobUWishSlot I) σDebt I) ⟨1⟩)
      (UInt256.eq (frobUMaskedWord I) (hopeSourceWord I))
  have rd3606 := h.jumpdest (by native_decide) (by evm_ov)
  have rd3609 := rd3606.push2 ⟨3636⟩ (by native_decide) (by evm_ov)
  have rd3612 := rd3609.push2 ⟨3626⟩ (by native_decide) (by evm_ov)
  have rd3614 := rd3612.push1 ⟨0⟩ (by native_decide) (by evm_ov)
  have rd3615 := rd3614.dup8 (by native_decide) (by evm_ov)
  have rd3616 := rd3615.sgt (by native_decide) (by evm_ov)
  have rd3617 := rd3616.iszero (by native_decide) (by evm_ov)
  have rd3619 := rd3617.push1 ⟨0⟩ (by native_decide) (by evm_ov)
  have rd3620 := rd3619.dup10 (by native_decide) (by evm_ov)
  have rd3621 := rd3620.slt (by native_decide) (by evm_ov)
  have rd3622 := rd3621.iszero (by native_decide) (by evm_ov)
  have rd3625 := rd3622.push2 ⟨6787⟩ (by native_decide) (by evm_ov)
  have rd6787 := rd3625.jump (by native_decide) (by jump_dest) (by evm_ov)
  have rd3626 := evm_run rd6787 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw jump (by native_decide) (by jump_dest) (by evm_ov),
    raw jumpdest (by native_decide) (by evm_ov)]
  have rd3627 := rd3626.push2 ⟨3417⟩ (by native_decide) (by evm_ov)
  have rd6557 := evm_run rd3627 with [
    raw dup12 (by native_decide) (by evm_ov),
    raw caller (by native_decide) (by evm_ov),
    raw push2 ⟨6557⟩ (by native_decide) (by evm_ov),
    raw jump (by native_decide) (by jump_dest) (by evm_ov)]
  obtain ⟨_, _, rd6599⟩ := RD.vatWishLoadedAt6557
    (σacc := σDebt)
    (usr := frobUMaskedWord I) (slot := frobUWishSlot I) (ret := ⟨3417⟩)
    (R := both :: (⟨3636⟩ : UInt256) :: tab :: dtabWord :: (⟨416⟩ : UInt256) ::
      (⟨192⟩ : UInt256) :: frobDartWord I :: frobDinkWord I ::
      frobWMaskedWord I :: frobVMaskedWord I :: frobUMaskedWord I ::
      frobIWord I :: ⟨524⟩ :: sel :: [])
    (mem := mem) (by simpa [both] using rd6557)
    (by rw [hmem]; exact frobIlkArtUpdatedMem_ge64 σ I urnInkNew urnArtNew ilkArtNew)
    (by rw [u256_land_comm]; exact frobUMaskedWord_clean I)
    (by rfl) (by simp)
  obtain ⟨_, _, rd3417⟩ := RD.vatWishReturnOk
    (σacc := σDebt)
    (usr := frobUMaskedWord I) (slot := frobUWishSlot I) (ret := ⟨3417⟩)
    (activeWords := UInt256.ofNat 18)
    (R := both :: (⟨3636⟩ : UInt256) :: tab :: dtabWord :: (⟨416⟩ : UInt256) ::
      (⟨192⟩ : UInt256) :: frobDartWord I :: frobDinkWord I ::
      frobWMaskedWord I :: frobVMaskedWord I :: frobUMaskedWord I ::
      frobIWord I :: ⟨524⟩ :: sel :: [])
    rd6599 (by jump_dest) (by simp)
  have rd3636 := evm_run rd3417 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push2 ⟨6791⟩ (by native_decide) (by evm_ov),
    raw jump (by native_decide) (by jump_dest) (by evm_ov),
    raw jumpdest (by native_decide) (by evm_ov),
    raw lor (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw jump (by native_decide) (by jump_dest) (by evm_ov)]
  have rd3640 := evm_run rd3636 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push2 ⟨3705⟩ (by native_decide) (by evm_ov)]
  have rdFall := by
    simpa [both, wish, frobUWishSlot] using
      rd3640.jumpiNT (by native_decide) hwish (by evm_ov)
  exact ⟨_, _, rdFall⟩

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem RD.vatFrobUWishCheckRevert
    {cA gh bl σ σ₀ A I} {g : Sat256} {k C : ℕ}
    {sel tab dtabWord urnInkNew urnArtNew ilkArtNew debtNew : UInt256}
    (h : RD vatBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3605⟩
      [tab, dtabWord, ⟨416⟩, ⟨192⟩, frobDartWord I, frobDinkWord I,
        frobWMaskedWord I, frobVMaskedWord I, frobUMaskedWord I, frobIWord I,
        ⟨524⟩, sel]
      (frobIlkArtUpdatedMem σ I urnInkNew urnArtNew ilkArtNew) (UInt256.ofNat 18)
      ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ foldDebtSlot debtNew) k C)
    (hwish :
      UInt256.lor
        (UInt256.lor
          (UInt256.eq (vatSlotWord (frobUWishSlot I)
            (sstoreAccountMap I.codeOwner σ foldDebtSlot debtNew) I) ⟨1⟩)
          (UInt256.eq (frobUMaskedWord I) (hopeSourceWord I)))
        (UInt256.land
          (UInt256.isZero (UInt256.slt (frobDinkWord I) ⟨0⟩))
          (UInt256.isZero (UInt256.sgt (frobDartWord I) ⟨0⟩))) = ⟨0⟩) :
    RDrev vatBytecode g (initState cA gh bl σ σ₀ g A I) := by
  let σDebt := sstoreAccountMap I.codeOwner σ foldDebtSlot debtNew
  let mem := frobIlkArtUpdatedMem σ I urnInkNew urnArtNew ilkArtNew
  let memU :=
    twoWordHashMem (hopeSourceWord I) (solcMappingSlot ⟨1⟩ (frobUMaskedWord I))
      (twoWordHashMem (frobUMaskedWord I) ⟨1⟩ mem)
  have h' :
      RD vatBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3605⟩
        [tab, dtabWord, ⟨416⟩, ⟨192⟩, frobDartWord I, frobDinkWord I,
          frobWMaskedWord I, frobVMaskedWord I, frobUMaskedWord I, frobIWord I,
          ⟨524⟩, sel]
        mem (UInt256.ofNat 18) ByteArray.empty (cA, σDebt) k C := by
    simpa [σDebt, mem] using h
  have hwish' :
      UInt256.lor
        (UInt256.lor
          (UInt256.eq (vatSlotWord (frobUWishSlot I) σDebt I) ⟨1⟩)
          (UInt256.eq (frobUMaskedWord I) (hopeSourceWord I)))
        (UInt256.land
          (UInt256.isZero (UInt256.slt (frobDinkWord I) ⟨0⟩))
          (UInt256.isZero (UInt256.sgt (frobDartWord I) ⟨0⟩))) = ⟨0⟩ := by
    simpa [σDebt] using hwish
  obtain ⟨_, _, rdFall⟩ := RD.vatFrobUWishCheckRevertFall
    (hσDebt := rfl) (hmem := rfl) h' hwish'
  have hmemBase576 : mem.size = 576 := by
    simpa [mem] using frobIlkArtUpdatedMem_size σ I urnInkNew urnArtNew ilkArtNew
  have hreadBase64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨576⟩ := by
    simpa [mem] using frobIlkArtUpdatedMem_read64 σ I urnInkNew urnArtNew ilkArtNew
  have hmem576 : memU.size = 576 := by
    dsimp [memU]
    exact twoWordHashMem_size_576 (hopeSourceWord I)
      (solcMappingSlot ⟨1⟩ (frobUMaskedWord I))
      (twoWordHashMem_size_576 (frobUMaskedWord I) ⟨1⟩ hmemBase576)
  have hread64 : memU.readWithPadding 64 32 = UInt256.toByteArray ⟨576⟩ := by
    dsimp [memU]
    exact twoWordHashMem_read64_of_size576 (hopeSourceWord I)
      (solcMappingSlot ⟨1⟩ (frobUMaskedWord I))
      (twoWordHashMem_size_576 (frobUMaskedWord I) ⟨1⟩ hmemBase576)
      (twoWordHashMem_read64_of_size576 (frobUMaskedWord I) ⟨1⟩
        hmemBase576 hreadBase64)
  exact RD.solcErrorStringRevertTail576
    (code := vatBytecode) (ee := I) (g := g)
    (s0 := initState cA gh bl σ σ₀ g A I)
    (stk := [tab, dtabWord, ⟨416⟩, ⟨192⟩, frobDartWord I,
      frobDinkWord I, frobWMaskedWord I, frobVMaskedWord I,
      frobUMaskedWord I, frobIWord I, ⟨524⟩, sel])
    (mem := memU) (rdata := ByteArray.empty) (acc := (cA, σDebt))
    (pc := ⟨3641⟩) (len := ⟨17⟩)
    (rawWord := ⟨29393821939250277271513265368272845679989⟩) (shift := ⟨120⟩)
    (word := UInt256.shiftLeft ⟨29393821939250277271513265368272845679989⟩ ⟨120⟩)
    (op := .PUSH17) (width := 17) rdFall
    vatFrobUWishNotAllowedTailWf
    (by decide) rfl
    hmem576
    hread64
    (by simp only [List.length_cons, List.length_nil]; omega)

set_option maxHeartbeats 1000000 in
theorem RD.vatFrobVWishCheckSuccess
    {cA gh bl σ σ₀ A I} {g : Sat256} {k C : ℕ}
    {sel tab dtabWord urnInkNew urnArtNew ilkArtNew debtNew : UInt256}
    (h : RD vatBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3705⟩
      [tab, dtabWord, ⟨416⟩, ⟨192⟩, frobDartWord I, frobDinkWord I,
        frobWMaskedWord I, frobVMaskedWord I, frobUMaskedWord I, frobIWord I,
        ⟨524⟩, sel]
      (twoWordHashMem (hopeSourceWord I) (solcMappingSlot ⟨1⟩ (frobUMaskedWord I))
        (twoWordHashMem (frobUMaskedWord I) ⟨1⟩
          (frobIlkArtUpdatedMem σ I urnInkNew urnArtNew ilkArtNew)))
      (UInt256.ofNat 18) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ foldDebtSlot debtNew) k C)
    (hwish :
      UInt256.lor
        (UInt256.lor
          (UInt256.eq (vatSlotWord (frobVWishSlot I)
            (sstoreAccountMap I.codeOwner σ foldDebtSlot debtNew) I) ⟨1⟩)
          (UInt256.eq (frobVMaskedWord I) (hopeSourceWord I)))
        (UInt256.isZero (UInt256.sgt (frobDinkWord I) ⟨0⟩)) ≠ ⟨0⟩) :
    ∃ k' C',
      RD vatBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3792⟩
        [tab, dtabWord, ⟨416⟩, ⟨192⟩, frobDartWord I, frobDinkWord I,
          frobWMaskedWord I, frobVMaskedWord I, frobUMaskedWord I, frobIWord I,
          ⟨524⟩, sel]
        (twoWordHashMem (hopeSourceWord I) (solcMappingSlot ⟨1⟩ (frobVMaskedWord I))
          (twoWordHashMem (frobVMaskedWord I) ⟨1⟩
            (twoWordHashMem (hopeSourceWord I) (solcMappingSlot ⟨1⟩ (frobUMaskedWord I))
              (twoWordHashMem (frobUMaskedWord I) ⟨1⟩
                (frobIlkArtUpdatedMem σ I urnInkNew urnArtNew ilkArtNew)))))
        (UInt256.ofNat 18) ByteArray.empty
        (cA, sstoreAccountMap I.codeOwner σ foldDebtSlot debtNew) k' C' := by
  let σDebt := sstoreAccountMap I.codeOwner σ foldDebtSlot debtNew
  let memBase := frobIlkArtUpdatedMem σ I urnInkNew urnArtNew ilkArtNew
  let memU :=
    twoWordHashMem (hopeSourceWord I) (solcMappingSlot ⟨1⟩ (frobUMaskedWord I))
      (twoWordHashMem (frobUMaskedWord I) ⟨1⟩ memBase)
  let shortcut := UInt256.isZero (UInt256.sgt (frobDinkWord I) ⟨0⟩)
  let wish :=
    UInt256.lor
      (UInt256.eq (vatSlotWord (frobVWishSlot I) σDebt I) ⟨1⟩)
      (UInt256.eq (frobVMaskedWord I) (hopeSourceWord I))
  have rd3706 := h.jumpdest (by native_decide) (by evm_ov)
  have rd3709 := rd3706.push2 ⟨3723⟩ (by native_decide) (by evm_ov)
  have rd3711 := rd3709.push1 ⟨0⟩ (by native_decide) (by evm_ov)
  have rd3712 := rd3711.dup8 (by native_decide) (by evm_ov)
  have rd3713 := rd3712.sgt (by native_decide) (by evm_ov)
  have rd3714 := rd3713.iszero (by native_decide) (by evm_ov)
  have rd3717 := rd3714.push2 ⟨3417⟩ (by native_decide) (by evm_ov)
  have rd6557 := evm_run rd3717 with [
    raw dup11 (by native_decide) (by evm_ov),
    raw caller (by native_decide) (by evm_ov),
    raw push2 ⟨6557⟩ (by native_decide) (by evm_ov),
    raw jump (by native_decide) (by jump_dest) (by evm_ov)]
  have hmemBase : 64 ≤ memBase.size := by
    exact frobIlkArtUpdatedMem_ge64 σ I urnInkNew urnArtNew ilkArtNew
  have hmemU : 64 ≤ memU.size := by
    dsimp [memU]
    rw [twoWordHashMem_size_of_ge64]
    · rw [twoWordHashMem_size_of_ge64]
      · exact hmemBase
      · exact hmemBase
    · rw [twoWordHashMem_size_of_ge64]
      · exact hmemBase
      · exact hmemBase
  obtain ⟨_, _, rd6599⟩ := RD.vatWishLoadedAt6557
    (σacc := σDebt)
    (usr := frobVMaskedWord I) (slot := frobVWishSlot I) (ret := ⟨3417⟩)
    (R := shortcut :: (⟨3723⟩ : UInt256) :: tab :: dtabWord :: (⟨416⟩ : UInt256) ::
      (⟨192⟩ : UInt256) :: frobDartWord I :: frobDinkWord I ::
      frobWMaskedWord I :: frobVMaskedWord I :: frobUMaskedWord I ::
      frobIWord I :: ⟨524⟩ :: sel :: [])
    (mem := memU) (by simpa [memU, shortcut] using rd6557)
    hmemU
    (by rw [u256_land_comm]; exact frobVMaskedWord_clean I)
    (by rfl) (by simp)
  obtain ⟨_, _, rd3417⟩ := RD.vatWishReturnOk
    (σacc := σDebt)
    (usr := frobVMaskedWord I) (slot := frobVWishSlot I) (ret := ⟨3417⟩)
    (activeWords := UInt256.ofNat 18)
    (R := shortcut :: (⟨3723⟩ : UInt256) :: tab :: dtabWord :: (⟨416⟩ : UInt256) ::
      (⟨192⟩ : UInt256) :: frobDartWord I :: frobDinkWord I ::
      frobWMaskedWord I :: frobVMaskedWord I :: frobUMaskedWord I ::
      frobIWord I :: ⟨524⟩ :: sel :: [])
    rd6599 (by jump_dest) (by simp)
  have rd3723 := evm_run rd3417 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push2 ⟨6791⟩ (by native_decide) (by evm_ov),
    raw jump (by native_decide) (by jump_dest) (by evm_ov),
    raw jumpdest (by native_decide) (by evm_ov),
    raw lor (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw jump (by native_decide) (by jump_dest) (by evm_ov)]
  have rd3727 := evm_run rd3723 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push2 ⟨3792⟩ (by native_decide) (by evm_ov)]
  exact ⟨_, _, by
    simpa [σDebt, memBase, memU, shortcut, wish, frobVWishSlot] using
      rd3727.jumpiT (by native_decide) hwish (by jump_dest) (by evm_ov)⟩

set_option maxHeartbeats 1000000 in
theorem RD.vatFrobVWishCheckRevert
    {cA gh bl σ σ₀ A I} {g : Sat256} {k C : ℕ}
    {sel tab dtabWord urnInkNew urnArtNew ilkArtNew debtNew : UInt256}
    (h : RD vatBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3705⟩
      [tab, dtabWord, ⟨416⟩, ⟨192⟩, frobDartWord I, frobDinkWord I,
        frobWMaskedWord I, frobVMaskedWord I, frobUMaskedWord I, frobIWord I,
        ⟨524⟩, sel]
      (twoWordHashMem (hopeSourceWord I) (solcMappingSlot ⟨1⟩ (frobUMaskedWord I))
        (twoWordHashMem (frobUMaskedWord I) ⟨1⟩
          (frobIlkArtUpdatedMem σ I urnInkNew urnArtNew ilkArtNew)))
      (UInt256.ofNat 18) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ foldDebtSlot debtNew) k C)
    (hwish :
      UInt256.lor
        (UInt256.lor
          (UInt256.eq (vatSlotWord (frobVWishSlot I)
            (sstoreAccountMap I.codeOwner σ foldDebtSlot debtNew) I) ⟨1⟩)
          (UInt256.eq (frobVMaskedWord I) (hopeSourceWord I)))
        (UInt256.isZero (UInt256.sgt (frobDinkWord I) ⟨0⟩)) = ⟨0⟩) :
    RDrev vatBytecode g (initState cA gh bl σ σ₀ g A I) := by
  let σDebt := sstoreAccountMap I.codeOwner σ foldDebtSlot debtNew
  let memBase := frobIlkArtUpdatedMem σ I urnInkNew urnArtNew ilkArtNew
  let memU :=
    twoWordHashMem (hopeSourceWord I) (solcMappingSlot ⟨1⟩ (frobUMaskedWord I))
      (twoWordHashMem (frobUMaskedWord I) ⟨1⟩ memBase)
  let shortcut := UInt256.isZero (UInt256.sgt (frobDinkWord I) ⟨0⟩)
  let wish :=
    UInt256.lor
      (UInt256.eq (vatSlotWord (frobVWishSlot I) σDebt I) ⟨1⟩)
      (UInt256.eq (frobVMaskedWord I) (hopeSourceWord I))
  have rd3706 := h.jumpdest (by native_decide) (by evm_ov)
  have rd3709 := rd3706.push2 ⟨3723⟩ (by native_decide) (by evm_ov)
  have rd3711 := rd3709.push1 ⟨0⟩ (by native_decide) (by evm_ov)
  have rd3712 := rd3711.dup8 (by native_decide) (by evm_ov)
  have rd3713 := rd3712.sgt (by native_decide) (by evm_ov)
  have rd3714 := rd3713.iszero (by native_decide) (by evm_ov)
  have rd3717 := rd3714.push2 ⟨3417⟩ (by native_decide) (by evm_ov)
  have rd6557 := evm_run rd3717 with [
    raw dup11 (by native_decide) (by evm_ov),
    raw caller (by native_decide) (by evm_ov),
    raw push2 ⟨6557⟩ (by native_decide) (by evm_ov),
    raw jump (by native_decide) (by jump_dest) (by evm_ov)]
  have hmemBase : 64 ≤ memBase.size := by
    exact frobIlkArtUpdatedMem_ge64 σ I urnInkNew urnArtNew ilkArtNew
  have hmemU : 64 ≤ memU.size := by
    dsimp [memU]
    rw [twoWordHashMem_size_of_ge64]
    · rw [twoWordHashMem_size_of_ge64]
      · exact hmemBase
      · exact hmemBase
    · rw [twoWordHashMem_size_of_ge64]
      · exact hmemBase
      · exact hmemBase
  obtain ⟨_, _, rd6599⟩ := RD.vatWishLoadedAt6557
    (σacc := σDebt)
    (usr := frobVMaskedWord I) (slot := frobVWishSlot I) (ret := ⟨3417⟩)
    (R := shortcut :: (⟨3723⟩ : UInt256) :: tab :: dtabWord :: (⟨416⟩ : UInt256) ::
      (⟨192⟩ : UInt256) :: frobDartWord I :: frobDinkWord I ::
      frobWMaskedWord I :: frobVMaskedWord I :: frobUMaskedWord I ::
      frobIWord I :: ⟨524⟩ :: sel :: [])
    (mem := memU) (by simpa [memU, shortcut] using rd6557)
    hmemU
    (by rw [u256_land_comm]; exact frobVMaskedWord_clean I)
    (by rfl) (by simp)
  obtain ⟨_, _, rd3417⟩ := RD.vatWishReturnOk
    (σacc := σDebt)
    (usr := frobVMaskedWord I) (slot := frobVWishSlot I) (ret := ⟨3417⟩)
    (activeWords := UInt256.ofNat 18)
    (R := shortcut :: (⟨3723⟩ : UInt256) :: tab :: dtabWord :: (⟨416⟩ : UInt256) ::
      (⟨192⟩ : UInt256) :: frobDartWord I :: frobDinkWord I ::
      frobWMaskedWord I :: frobVMaskedWord I :: frobUMaskedWord I ::
      frobIWord I :: ⟨524⟩ :: sel :: [])
    rd6599 (by jump_dest) (by simp)
  have rd3723 := evm_run rd3417 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push2 ⟨6791⟩ (by native_decide) (by evm_ov),
    raw jump (by native_decide) (by jump_dest) (by evm_ov),
    raw jumpdest (by native_decide) (by evm_ov),
    raw lor (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw jump (by native_decide) (by jump_dest) (by evm_ov)]
  have rd3727 := evm_run rd3723 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push2 ⟨3792⟩ (by native_decide) (by evm_ov)]
  have rdFall := by
    simpa [σDebt, memBase, memU, shortcut, wish, frobVWishSlot] using
      rd3727.jumpiNT (by native_decide) hwish (by evm_ov)
  exact RD.solcErrorStringRevertTail576
    (code := vatBytecode) (pc := ⟨3728⟩) (len := ⟨17⟩)
    (rawWord := ⟨14696910969625138635756632684136422839995⟩) (shift := ⟨121⟩)
    (word := UInt256.shiftLeft ⟨14696910969625138635756632684136422839995⟩ ⟨121⟩)
    (op := .PUSH17) (width := 17) rdFall
    (by unfold solcErrorStringRevertTailWf; repeat' first | apply And.intro | native_decide)
    (by native_decide) rfl
    (by
      exact twoWordHashMem_size_576 (hopeSourceWord I)
        (solcMappingSlot ⟨1⟩ (frobVMaskedWord I))
        (twoWordHashMem_size_576 (frobVMaskedWord I) ⟨1⟩
          (twoWordHashMem_size_576 (hopeSourceWord I)
            (solcMappingSlot ⟨1⟩ (frobUMaskedWord I))
            (twoWordHashMem_size_576 (frobUMaskedWord I) ⟨1⟩
              (frobIlkArtUpdatedMem_size σ I urnInkNew urnArtNew ilkArtNew)))))
    (by
      exact twoWordHashMem_read64_of_size576 (hopeSourceWord I)
        (solcMappingSlot ⟨1⟩ (frobVMaskedWord I))
        (twoWordHashMem_size_576 (frobVMaskedWord I) ⟨1⟩
          (twoWordHashMem_size_576 (hopeSourceWord I)
            (solcMappingSlot ⟨1⟩ (frobUMaskedWord I))
            (twoWordHashMem_size_576 (frobUMaskedWord I) ⟨1⟩
              (frobIlkArtUpdatedMem_size σ I urnInkNew urnArtNew ilkArtNew))))
        (twoWordHashMem_read64_of_size576 (frobVMaskedWord I) ⟨1⟩
          (twoWordHashMem_size_576 (hopeSourceWord I)
            (solcMappingSlot ⟨1⟩ (frobUMaskedWord I))
            (twoWordHashMem_size_576 (frobUMaskedWord I) ⟨1⟩
              (frobIlkArtUpdatedMem_size σ I urnInkNew urnArtNew ilkArtNew)))
          (twoWordHashMem_read64_of_size576 (hopeSourceWord I)
            (solcMappingSlot ⟨1⟩ (frobUMaskedWord I))
            (twoWordHashMem_size_576 (frobUMaskedWord I) ⟨1⟩
              (frobIlkArtUpdatedMem_size σ I urnInkNew urnArtNew ilkArtNew))
            (twoWordHashMem_read64_of_size576 (frobUMaskedWord I) ⟨1⟩
              (frobIlkArtUpdatedMem_size σ I urnInkNew urnArtNew ilkArtNew)
              (frobIlkArtUpdatedMem_read64 σ I urnInkNew urnArtNew ilkArtNew)))))
    (by simp only [List.length_cons, List.length_nil]; omega)

set_option maxHeartbeats 1000000 in
theorem RD.vatFrobWWishCheckSuccess
    {cA gh bl σ σ₀ A I} {g : Sat256} {k C : ℕ}
    {sel tab dtabWord urnInkNew urnArtNew ilkArtNew debtNew : UInt256}
    (h : RD vatBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3792⟩
      [tab, dtabWord, ⟨416⟩, ⟨192⟩, frobDartWord I, frobDinkWord I,
        frobWMaskedWord I, frobVMaskedWord I, frobUMaskedWord I, frobIWord I,
        ⟨524⟩, sel]
      (twoWordHashMem (hopeSourceWord I) (solcMappingSlot ⟨1⟩ (frobVMaskedWord I))
        (twoWordHashMem (frobVMaskedWord I) ⟨1⟩
          (twoWordHashMem (hopeSourceWord I) (solcMappingSlot ⟨1⟩ (frobUMaskedWord I))
            (twoWordHashMem (frobUMaskedWord I) ⟨1⟩
              (frobIlkArtUpdatedMem σ I urnInkNew urnArtNew ilkArtNew)))))
      (UInt256.ofNat 18) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ foldDebtSlot debtNew) k C)
    (hwish :
      UInt256.lor
        (UInt256.lor
          (UInt256.eq (vatSlotWord (frobWWishSlot I)
            (sstoreAccountMap I.codeOwner σ foldDebtSlot debtNew) I) ⟨1⟩)
          (UInt256.eq (frobWMaskedWord I) (hopeSourceWord I)))
        (UInt256.isZero (UInt256.slt (frobDartWord I) ⟨0⟩)) ≠ ⟨0⟩) :
    ∃ k' C',
      RD vatBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3879⟩
        [tab, dtabWord, ⟨416⟩, ⟨192⟩, frobDartWord I, frobDinkWord I,
          frobWMaskedWord I, frobVMaskedWord I, frobUMaskedWord I, frobIWord I,
          ⟨524⟩, sel]
        (twoWordHashMem (hopeSourceWord I) (solcMappingSlot ⟨1⟩ (frobWMaskedWord I))
          (twoWordHashMem (frobWMaskedWord I) ⟨1⟩
            (twoWordHashMem (hopeSourceWord I) (solcMappingSlot ⟨1⟩ (frobVMaskedWord I))
              (twoWordHashMem (frobVMaskedWord I) ⟨1⟩
                (twoWordHashMem (hopeSourceWord I) (solcMappingSlot ⟨1⟩ (frobUMaskedWord I))
                  (twoWordHashMem (frobUMaskedWord I) ⟨1⟩
                    (frobIlkArtUpdatedMem σ I urnInkNew urnArtNew ilkArtNew)))))))
        (UInt256.ofNat 18) ByteArray.empty
        (cA, sstoreAccountMap I.codeOwner σ foldDebtSlot debtNew) k' C' := by
  let σDebt := sstoreAccountMap I.codeOwner σ foldDebtSlot debtNew
  let memBase := frobIlkArtUpdatedMem σ I urnInkNew urnArtNew ilkArtNew
  let memU :=
    twoWordHashMem (hopeSourceWord I) (solcMappingSlot ⟨1⟩ (frobUMaskedWord I))
      (twoWordHashMem (frobUMaskedWord I) ⟨1⟩ memBase)
  let memV :=
    twoWordHashMem (hopeSourceWord I) (solcMappingSlot ⟨1⟩ (frobVMaskedWord I))
      (twoWordHashMem (frobVMaskedWord I) ⟨1⟩ memU)
  let shortcut := UInt256.isZero (UInt256.slt (frobDartWord I) ⟨0⟩)
  let wish :=
    UInt256.lor
      (UInt256.eq (vatSlotWord (frobWWishSlot I) σDebt I) ⟨1⟩)
      (UInt256.eq (frobWMaskedWord I) (hopeSourceWord I))
  have rd3793 := h.jumpdest (by native_decide) (by evm_ov)
  have rd3796 := rd3793.push2 ⟨3810⟩ (by native_decide) (by evm_ov)
  have rd3798 := rd3796.push1 ⟨0⟩ (by native_decide) (by evm_ov)
  have rd3799 := rd3798.dup7 (by native_decide) (by evm_ov)
  have rd3800 := rd3799.slt (by native_decide) (by evm_ov)
  have rd3801 := rd3800.iszero (by native_decide) (by evm_ov)
  have rd3804 := rd3801.push2 ⟨3417⟩ (by native_decide) (by evm_ov)
  have rd6557 := evm_run rd3804 with [
    raw dup10 (by native_decide) (by evm_ov),
    raw caller (by native_decide) (by evm_ov),
    raw push2 ⟨6557⟩ (by native_decide) (by evm_ov),
    raw jump (by native_decide) (by jump_dest) (by evm_ov)]
  have hmemBase : 64 ≤ memBase.size := by
    exact frobIlkArtUpdatedMem_ge64 σ I urnInkNew urnArtNew ilkArtNew
  have hmemU : 64 ≤ memU.size := by
    dsimp [memU]
    rw [twoWordHashMem_size_of_ge64]
    · rw [twoWordHashMem_size_of_ge64]
      · exact hmemBase
      · exact hmemBase
    · rw [twoWordHashMem_size_of_ge64]
      · exact hmemBase
      · exact hmemBase
  have hmemV : 64 ≤ memV.size := by
    dsimp [memV]
    rw [twoWordHashMem_size_of_ge64]
    · rw [twoWordHashMem_size_of_ge64]
      · exact hmemU
      · exact hmemU
    · rw [twoWordHashMem_size_of_ge64]
      · exact hmemU
      · exact hmemU
  obtain ⟨_, _, rd6599⟩ := RD.vatWishLoadedAt6557
    (σacc := σDebt)
    (usr := frobWMaskedWord I) (slot := frobWWishSlot I) (ret := ⟨3417⟩)
    (R := shortcut :: (⟨3810⟩ : UInt256) :: tab :: dtabWord :: (⟨416⟩ : UInt256) ::
      (⟨192⟩ : UInt256) :: frobDartWord I :: frobDinkWord I ::
      frobWMaskedWord I :: frobVMaskedWord I :: frobUMaskedWord I ::
      frobIWord I :: ⟨524⟩ :: sel :: [])
    (mem := memV) (by simpa [memV, shortcut] using rd6557)
    hmemV
    (by rw [u256_land_comm]; exact frobWMaskedWord_clean I)
    (by rfl) (by simp)
  obtain ⟨_, _, rd3417⟩ := RD.vatWishReturnOk
    (σacc := σDebt)
    (usr := frobWMaskedWord I) (slot := frobWWishSlot I) (ret := ⟨3417⟩)
    (activeWords := UInt256.ofNat 18)
    (R := shortcut :: (⟨3810⟩ : UInt256) :: tab :: dtabWord :: (⟨416⟩ : UInt256) ::
      (⟨192⟩ : UInt256) :: frobDartWord I :: frobDinkWord I ::
      frobWMaskedWord I :: frobVMaskedWord I :: frobUMaskedWord I ::
      frobIWord I :: ⟨524⟩ :: sel :: [])
    rd6599 (by jump_dest) (by simp)
  have rd3810 := evm_run rd3417 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push2 ⟨6791⟩ (by native_decide) (by evm_ov),
    raw jump (by native_decide) (by jump_dest) (by evm_ov),
    raw jumpdest (by native_decide) (by evm_ov),
    raw lor (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw jump (by native_decide) (by jump_dest) (by evm_ov)]
  have rd3814 := evm_run rd3810 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push2 ⟨3879⟩ (by native_decide) (by evm_ov)]
  exact ⟨_, _, by
    simpa [σDebt, memBase, memU, memV, shortcut, wish, frobWWishSlot] using
      rd3814.jumpiT (by native_decide) hwish (by jump_dest) (by evm_ov)⟩

set_option maxHeartbeats 1000000 in
theorem RD.vatFrobWWishCheckRevert
    {cA gh bl σ σ₀ A I} {g : Sat256} {k C : ℕ}
    {sel tab dtabWord urnInkNew urnArtNew ilkArtNew debtNew : UInt256}
    (h : RD vatBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3792⟩
      [tab, dtabWord, ⟨416⟩, ⟨192⟩, frobDartWord I, frobDinkWord I,
        frobWMaskedWord I, frobVMaskedWord I, frobUMaskedWord I, frobIWord I,
        ⟨524⟩, sel]
      (twoWordHashMem (hopeSourceWord I) (solcMappingSlot ⟨1⟩ (frobVMaskedWord I))
        (twoWordHashMem (frobVMaskedWord I) ⟨1⟩
          (twoWordHashMem (hopeSourceWord I) (solcMappingSlot ⟨1⟩ (frobUMaskedWord I))
            (twoWordHashMem (frobUMaskedWord I) ⟨1⟩
              (frobIlkArtUpdatedMem σ I urnInkNew urnArtNew ilkArtNew)))))
      (UInt256.ofNat 18) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ foldDebtSlot debtNew) k C)
    (hwish :
      UInt256.lor
        (UInt256.lor
          (UInt256.eq (vatSlotWord (frobWWishSlot I)
            (sstoreAccountMap I.codeOwner σ foldDebtSlot debtNew) I) ⟨1⟩)
          (UInt256.eq (frobWMaskedWord I) (hopeSourceWord I)))
        (UInt256.isZero (UInt256.slt (frobDartWord I) ⟨0⟩)) = ⟨0⟩) :
    RDrev vatBytecode g (initState cA gh bl σ σ₀ g A I) := by
  let σDebt := sstoreAccountMap I.codeOwner σ foldDebtSlot debtNew
  let memBase := frobIlkArtUpdatedMem σ I urnInkNew urnArtNew ilkArtNew
  let memU :=
    twoWordHashMem (hopeSourceWord I) (solcMappingSlot ⟨1⟩ (frobUMaskedWord I))
      (twoWordHashMem (frobUMaskedWord I) ⟨1⟩ memBase)
  let memV :=
    twoWordHashMem (hopeSourceWord I) (solcMappingSlot ⟨1⟩ (frobVMaskedWord I))
      (twoWordHashMem (frobVMaskedWord I) ⟨1⟩ memU)
  let shortcut := UInt256.isZero (UInt256.slt (frobDartWord I) ⟨0⟩)
  let wish :=
    UInt256.lor
      (UInt256.eq (vatSlotWord (frobWWishSlot I) σDebt I) ⟨1⟩)
      (UInt256.eq (frobWMaskedWord I) (hopeSourceWord I))
  have rd3793 := h.jumpdest (by native_decide) (by evm_ov)
  have rd3796 := rd3793.push2 ⟨3810⟩ (by native_decide) (by evm_ov)
  have rd3798 := rd3796.push1 ⟨0⟩ (by native_decide) (by evm_ov)
  have rd3799 := rd3798.dup7 (by native_decide) (by evm_ov)
  have rd3800 := rd3799.slt (by native_decide) (by evm_ov)
  have rd3801 := rd3800.iszero (by native_decide) (by evm_ov)
  have rd3804 := rd3801.push2 ⟨3417⟩ (by native_decide) (by evm_ov)
  have rd6557 := evm_run rd3804 with [
    raw dup10 (by native_decide) (by evm_ov),
    raw caller (by native_decide) (by evm_ov),
    raw push2 ⟨6557⟩ (by native_decide) (by evm_ov),
    raw jump (by native_decide) (by jump_dest) (by evm_ov)]
  have hmemBase : 64 ≤ memBase.size := by
    exact frobIlkArtUpdatedMem_ge64 σ I urnInkNew urnArtNew ilkArtNew
  have hmemU : 64 ≤ memU.size := by
    dsimp [memU]
    rw [twoWordHashMem_size_of_ge64]
    · rw [twoWordHashMem_size_of_ge64]
      · exact hmemBase
      · exact hmemBase
    · rw [twoWordHashMem_size_of_ge64]
      · exact hmemBase
      · exact hmemBase
  have hmemV : 64 ≤ memV.size := by
    dsimp [memV]
    rw [twoWordHashMem_size_of_ge64]
    · rw [twoWordHashMem_size_of_ge64]
      · exact hmemU
      · exact hmemU
    · rw [twoWordHashMem_size_of_ge64]
      · exact hmemU
      · exact hmemU
  obtain ⟨_, _, rd6599⟩ := RD.vatWishLoadedAt6557
    (σacc := σDebt)
    (usr := frobWMaskedWord I) (slot := frobWWishSlot I) (ret := ⟨3417⟩)
    (R := shortcut :: (⟨3810⟩ : UInt256) :: tab :: dtabWord :: (⟨416⟩ : UInt256) ::
      (⟨192⟩ : UInt256) :: frobDartWord I :: frobDinkWord I ::
      frobWMaskedWord I :: frobVMaskedWord I :: frobUMaskedWord I ::
      frobIWord I :: ⟨524⟩ :: sel :: [])
    (mem := memV) (by simpa [memV, shortcut] using rd6557)
    hmemV
    (by rw [u256_land_comm]; exact frobWMaskedWord_clean I)
    (by rfl) (by simp)
  obtain ⟨_, _, rd3417⟩ := RD.vatWishReturnOk
    (σacc := σDebt)
    (usr := frobWMaskedWord I) (slot := frobWWishSlot I) (ret := ⟨3417⟩)
    (activeWords := UInt256.ofNat 18)
    (R := shortcut :: (⟨3810⟩ : UInt256) :: tab :: dtabWord :: (⟨416⟩ : UInt256) ::
      (⟨192⟩ : UInt256) :: frobDartWord I :: frobDinkWord I ::
      frobWMaskedWord I :: frobVMaskedWord I :: frobUMaskedWord I ::
      frobIWord I :: ⟨524⟩ :: sel :: [])
    rd6599 (by jump_dest) (by simp)
  have rd3810 := evm_run rd3417 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push2 ⟨6791⟩ (by native_decide) (by evm_ov),
    raw jump (by native_decide) (by jump_dest) (by evm_ov),
    raw jumpdest (by native_decide) (by evm_ov),
    raw lor (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw jump (by native_decide) (by jump_dest) (by evm_ov)]
  have rd3814 := evm_run rd3810 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push2 ⟨3879⟩ (by native_decide) (by evm_ov)]
  have rdFall := by
    simpa [σDebt, memBase, memU, memV, shortcut, wish, frobWWishSlot] using
      rd3814.jumpiNT (by native_decide) hwish (by evm_ov)
  exact RD.solcErrorStringRevertTail576
    (code := vatBytecode) (pc := ⟨3815⟩) (len := ⟨17⟩)
    (rawWord := ⟨29393821939250277271513265368272845679991⟩) (shift := ⟨120⟩)
    (word := UInt256.shiftLeft ⟨29393821939250277271513265368272845679991⟩ ⟨120⟩)
    (op := .PUSH17) (width := 17) rdFall
    (by unfold solcErrorStringRevertTailWf; repeat' first | apply And.intro | native_decide)
    (by native_decide) rfl
    (by
      exact twoWordHashMem_size_576 (hopeSourceWord I)
        (solcMappingSlot ⟨1⟩ (frobWMaskedWord I))
        (twoWordHashMem_size_576 (frobWMaskedWord I) ⟨1⟩
          (twoWordHashMem_size_576 (hopeSourceWord I)
            (solcMappingSlot ⟨1⟩ (frobVMaskedWord I))
            (twoWordHashMem_size_576 (frobVMaskedWord I) ⟨1⟩
              (twoWordHashMem_size_576 (hopeSourceWord I)
                (solcMappingSlot ⟨1⟩ (frobUMaskedWord I))
                (twoWordHashMem_size_576 (frobUMaskedWord I) ⟨1⟩
                  (frobIlkArtUpdatedMem_size σ I urnInkNew urnArtNew ilkArtNew)))))))
    (by
      exact twoWordHashMem_read64_of_size576 (hopeSourceWord I)
        (solcMappingSlot ⟨1⟩ (frobWMaskedWord I))
        (twoWordHashMem_size_576 (frobWMaskedWord I) ⟨1⟩
          (twoWordHashMem_size_576 (hopeSourceWord I)
            (solcMappingSlot ⟨1⟩ (frobVMaskedWord I))
            (twoWordHashMem_size_576 (frobVMaskedWord I) ⟨1⟩
              (twoWordHashMem_size_576 (hopeSourceWord I)
                (solcMappingSlot ⟨1⟩ (frobUMaskedWord I))
                (twoWordHashMem_size_576 (frobUMaskedWord I) ⟨1⟩
                  (frobIlkArtUpdatedMem_size σ I urnInkNew urnArtNew ilkArtNew))))))
        (twoWordHashMem_read64_of_size576 (frobWMaskedWord I) ⟨1⟩
          (twoWordHashMem_size_576 (hopeSourceWord I)
            (solcMappingSlot ⟨1⟩ (frobVMaskedWord I))
            (twoWordHashMem_size_576 (frobVMaskedWord I) ⟨1⟩
              (twoWordHashMem_size_576 (hopeSourceWord I)
                (solcMappingSlot ⟨1⟩ (frobUMaskedWord I))
                (twoWordHashMem_size_576 (frobUMaskedWord I) ⟨1⟩
                  (frobIlkArtUpdatedMem_size σ I urnInkNew urnArtNew ilkArtNew)))))
          (twoWordHashMem_read64_of_size576 (hopeSourceWord I)
            (solcMappingSlot ⟨1⟩ (frobVMaskedWord I))
            (twoWordHashMem_size_576 (frobVMaskedWord I) ⟨1⟩
              (twoWordHashMem_size_576 (hopeSourceWord I)
                (solcMappingSlot ⟨1⟩ (frobUMaskedWord I))
                (twoWordHashMem_size_576 (frobUMaskedWord I) ⟨1⟩
                  (frobIlkArtUpdatedMem_size σ I urnInkNew urnArtNew ilkArtNew))))
            (twoWordHashMem_read64_of_size576 (frobVMaskedWord I) ⟨1⟩
              (twoWordHashMem_size_576 (hopeSourceWord I)
                (solcMappingSlot ⟨1⟩ (frobUMaskedWord I))
                (twoWordHashMem_size_576 (frobUMaskedWord I) ⟨1⟩
                  (frobIlkArtUpdatedMem_size σ I urnInkNew urnArtNew ilkArtNew)))
              (twoWordHashMem_read64_of_size576 (hopeSourceWord I)
                (solcMappingSlot ⟨1⟩ (frobUMaskedWord I))
                (twoWordHashMem_size_576 (frobUMaskedWord I) ⟨1⟩
                  (frobIlkArtUpdatedMem_size σ I urnInkNew urnArtNew ilkArtNew))
                (twoWordHashMem_read64_of_size576 (frobUMaskedWord I) ⟨1⟩
                  (frobIlkArtUpdatedMem_size σ I urnInkNew urnArtNew ilkArtNew)
                  (frobIlkArtUpdatedMem_read64 σ I urnInkNew urnArtNew ilkArtNew)))))))
    (by simp only [List.length_cons, List.length_nil]; omega)

set_option maxHeartbeats 1000000 in
theorem RD.vatFrobDustCheckSuccess
    {cA gh bl σ σ₀ A I} {g : Sat256} {k C : ℕ}
    {sel tab dtabWord urnInkNew urnArtNew ilkArtNew debtNew : UInt256}
    (h : RD vatBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3879⟩
      [tab, dtabWord, ⟨416⟩, ⟨192⟩, frobDartWord I, frobDinkWord I,
        frobWMaskedWord I, frobVMaskedWord I, frobUMaskedWord I, frobIWord I,
        ⟨524⟩, sel]
      (twoWordHashMem (hopeSourceWord I) (solcMappingSlot ⟨1⟩ (frobWMaskedWord I))
        (twoWordHashMem (frobWMaskedWord I) ⟨1⟩
          (twoWordHashMem (hopeSourceWord I) (solcMappingSlot ⟨1⟩ (frobVMaskedWord I))
            (twoWordHashMem (frobVMaskedWord I) ⟨1⟩
              (twoWordHashMem (hopeSourceWord I) (solcMappingSlot ⟨1⟩ (frobUMaskedWord I))
                (twoWordHashMem (frobUMaskedWord I) ⟨1⟩
                  (frobIlkArtUpdatedMem σ I urnInkNew urnArtNew ilkArtNew)))))))
      (UInt256.ofNat 18) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ foldDebtSlot debtNew) k C)
    (hdust :
      UInt256.lor
        (UInt256.isZero
          (UInt256.lt tab (solcSlotWord σ I (frobIlkDustSlot I))))
        (UInt256.eq ⟨0⟩ urnArtNew) ≠ ⟨0⟩) :
    ∃ k' C',
      RD vatBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3963⟩
        [tab, dtabWord, ⟨416⟩, ⟨192⟩, frobDartWord I, frobDinkWord I,
          frobWMaskedWord I, frobVMaskedWord I, frobUMaskedWord I, frobIWord I,
          ⟨524⟩, sel]
        (twoWordHashMem (hopeSourceWord I) (solcMappingSlot ⟨1⟩ (frobWMaskedWord I))
          (twoWordHashMem (frobWMaskedWord I) ⟨1⟩
            (twoWordHashMem (hopeSourceWord I) (solcMappingSlot ⟨1⟩ (frobVMaskedWord I))
              (twoWordHashMem (frobVMaskedWord I) ⟨1⟩
                (twoWordHashMem (hopeSourceWord I) (solcMappingSlot ⟨1⟩ (frobUMaskedWord I))
                  (twoWordHashMem (frobUMaskedWord I) ⟨1⟩
                    (frobIlkArtUpdatedMem σ I urnInkNew urnArtNew ilkArtNew)))))))
        (UInt256.ofNat 18) ByteArray.empty
        (cA, sstoreAccountMap I.codeOwner σ foldDebtSlot debtNew) k' C' := by
  let memBase := frobIlkArtUpdatedMem σ I urnInkNew urnArtNew ilkArtNew
  let memU :=
    twoWordHashMem (hopeSourceWord I) (solcMappingSlot ⟨1⟩ (frobUMaskedWord I))
      (twoWordHashMem (frobUMaskedWord I) ⟨1⟩ memBase)
  let memV :=
    twoWordHashMem (hopeSourceWord I) (solcMappingSlot ⟨1⟩ (frobVMaskedWord I))
      (twoWordHashMem (frobVMaskedWord I) ⟨1⟩ memU)
  let memW :=
    twoWordHashMem (hopeSourceWord I) (solcMappingSlot ⟨1⟩ (frobWMaskedWord I))
      (twoWordHashMem (frobWMaskedWord I) ⟨1⟩ memV)
  let dust := solcSlotWord σ I (frobIlkDustSlot I)
  have hmemBaseSize : memBase.size = 576 := by
    dsimp [memBase]
    exact frobIlkArtUpdatedMem_size σ I urnInkNew urnArtNew ilkArtNew
  have hmemUSize : memU.size = 576 := by
    dsimp [memU]
    rw [twoWordHashMem_size_of_ge64]
    · rw [twoWordHashMem_size_of_ge64]
      · exact hmemBaseSize
      · rw [hmemBaseSize]; omega
    · rw [twoWordHashMem_size_of_ge64]
      · rw [hmemBaseSize]; omega
      · rw [hmemBaseSize]; omega
  have hmemVSize : memV.size = 576 := by
    dsimp [memV]
    rw [twoWordHashMem_size_of_ge64]
    · rw [twoWordHashMem_size_of_ge64]
      · exact hmemUSize
      · rw [hmemUSize]; omega
    · rw [twoWordHashMem_size_of_ge64]
      · rw [hmemUSize]; omega
      · rw [hmemUSize]; omega
  have hmemWSize : memW.size = 576 := by
    dsimp [memW]
    rw [twoWordHashMem_size_of_ge64]
    · rw [twoWordHashMem_size_of_ge64]
      · exact hmemVSize
      · rw [hmemVSize]; omega
    · rw [twoWordHashMem_size_of_ge64]
      · rw [hmemVSize]; omega
      · rw [hmemVSize]; omega
  have hread224 :
      memW.readWithPadding 224 32 = UInt256.toByteArray urnArtNew := by
    dsimp [memW, memV, memU, memBase]
    rw [twoWordHashMem_read32_above64 (readOff := 224)]
    · rw [twoWordHashMem_read32_above64 (readOff := 224)]
      · rw [twoWordHashMem_read32_above64 (readOff := 224)]
        · rw [twoWordHashMem_read32_above64 (readOff := 224)]
          · rw [twoWordHashMem_read32_above64 (readOff := 224)]
            · rw [twoWordHashMem_read32_above64 (readOff := 224)]
              · exact frobIlkArtUpdatedMem_read224 σ I urnInkNew urnArtNew ilkArtNew
              · omega
              · rw [hmemBaseSize]; omega
            · omega
            · rw [twoWordHashMem_size_of_ge64]
              · rw [hmemBaseSize]; omega
              · rw [hmemBaseSize]; omega
          · omega
          · rw [hmemUSize]; omega
        · omega
        · rw [twoWordHashMem_size_of_ge64]
          · rw [hmemUSize]; omega
          · rw [hmemUSize]; omega
      · omega
      · rw [hmemVSize]; omega
    · omega
    · rw [twoWordHashMem_size_of_ge64]
      · rw [hmemVSize]; omega
      · rw [hmemVSize]; omega
  have hread544 :
      memW.readWithPadding 544 32 = UInt256.toByteArray dust := by
    dsimp [memW, memV, memU, memBase, dust]
    rw [twoWordHashMem_read32_above64 (readOff := 544)]
    · rw [twoWordHashMem_read32_above64 (readOff := 544)]
      · rw [twoWordHashMem_read32_above64 (readOff := 544)]
        · rw [twoWordHashMem_read32_above64 (readOff := 544)]
          · rw [twoWordHashMem_read32_above64 (readOff := 544)]
            · rw [twoWordHashMem_read32_above64 (readOff := 544)]
              · exact frobIlkArtUpdatedMem_read544 σ I urnInkNew urnArtNew ilkArtNew
              · omega
              · rw [hmemBaseSize]
            · omega
            · rw [twoWordHashMem_size_of_ge64]
              · rw [hmemBaseSize]
              · rw [hmemBaseSize]; omega
          · omega
          · rw [hmemUSize]
        · omega
        · rw [twoWordHashMem_size_of_ge64]
          · rw [hmemUSize]
          · rw [hmemUSize]; omega
      · omega
      · rw [hmemVSize]
    · omega
    · rw [twoWordHashMem_size_of_ge64]
      · rw [hmemVSize]
      · rw [hmemVSize]; omega
  have rd3880 := h.jumpdest (by native_decide) (by evm_ov)
  have rd3883 := rd3880.push2 ⟨3903⟩ (by native_decide) (by evm_ov)
  have rd3884 := rd3883.dup5 (by native_decide) (by evm_ov)
  have rd3886 := rd3884.push1 ⟨32⟩ (by native_decide) (by evm_ov)
  have rd3887raw := rd3886.add (by native_decide) (by evm_ov)
  have hoff224 : (⟨192⟩ : UInt256) + ⟨32⟩ = ⟨224⟩ := by native_decide
  have hmload224 :
      (if ((⟨192⟩ : UInt256) + ⟨32⟩).toNat ≥ memW.size
          ∨ ((⟨192⟩ : UInt256) + ⟨32⟩) ≥ UInt256.ofNat 18 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
          (memW.readWithPadding (((⟨192⟩ : UInt256) + ⟨32⟩).toNat) 32))) =
        urnArtNew := by
    rw [hoff224]
    exact mloadWordValue_of_readWithPadding
      (by rw [show (⟨224⟩ : UInt256).toNat = 224 from by decide, hmemWSize]; omega)
      (by native_decide)
      (by
        simpa [show (⟨224⟩ : UInt256).toNat = 224 from by decide] using hread224)
  have rd3887raw' := rd3887raw.mload 0 urnArtNew (UInt256.ofNat 18)
    (by native_decide) mem_cost hmload224 (by native_decide) (by evm_ov)
  have rd3887 := by
    simpa [hoff224, memW] using rd3887raw'
  have rd3888 := rd3887.push1 ⟨0⟩ (by native_decide) (by evm_ov)
  have rd3890 := rd3888.eq (by native_decide) (by evm_ov)
  have rd3891 := rd3890.dup5 (by native_decide) (by evm_ov)
  have rd3892 := rd3891.push1 ⟨128⟩ (by native_decide) (by evm_ov)
  have rd3895raw := rd3892.add (by native_decide) (by evm_ov)
  have hoff544 : (⟨416⟩ : UInt256) + ⟨128⟩ = ⟨544⟩ := by native_decide
  have hmload544 :
      (if ((⟨416⟩ : UInt256) + ⟨128⟩).toNat ≥ memW.size
          ∨ ((⟨416⟩ : UInt256) + ⟨128⟩) ≥ UInt256.ofNat 18 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
          (memW.readWithPadding (((⟨416⟩ : UInt256) + ⟨128⟩).toNat) 32))) =
        dust := by
    rw [hoff544]
    exact mloadWordValue_of_readWithPadding
      (by rw [show (⟨544⟩ : UInt256).toNat = 544 from by decide, hmemWSize]; omega)
      (by native_decide)
      (by
        simpa [show (⟨544⟩ : UInt256).toNat = 544 from by decide] using hread544)
  have rd3895raw' := rd3895raw.mload 0 dust (UInt256.ofNat 18)
    (by native_decide) mem_cost hmload544 (by native_decide) (by evm_ov)
  have rd3895 := by
    simpa [hoff544, memW] using rd3895raw'
  have rd3896 := rd3895.dup4 (by native_decide) (by evm_ov)
  have rd3897 := rd3896.lt (by native_decide) (by evm_ov)
  have rd3898 := rd3897.iszero (by native_decide) (by evm_ov)
  have rd3902 := rd3898.push2 ⟨6791⟩ (by native_decide) (by evm_ov)
  have rd6791 := rd3902.jump (by native_decide) (by jump_dest) (by evm_ov)
  have rd3903 := evm_run rd6791 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw lor (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw jump (by native_decide) (by jump_dest) (by evm_ov)]
  have rd3907 := evm_run rd3903 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push2 ⟨3963⟩ (by native_decide) (by evm_ov)]
  exact ⟨_, _, by
    simpa [memW, dust] using
      rd3907.jumpiT (by native_decide) hdust (by jump_dest) (by evm_ov)⟩

set_option maxHeartbeats 1000000 in
theorem RD.vatFrobDustCheckRevert
    {cA gh bl σ σ₀ A I} {g : Sat256} {k C : ℕ}
    {sel tab dtabWord urnInkNew urnArtNew ilkArtNew debtNew : UInt256}
    (h : RD vatBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3879⟩
      [tab, dtabWord, ⟨416⟩, ⟨192⟩, frobDartWord I, frobDinkWord I,
        frobWMaskedWord I, frobVMaskedWord I, frobUMaskedWord I, frobIWord I,
        ⟨524⟩, sel]
      (twoWordHashMem (hopeSourceWord I) (solcMappingSlot ⟨1⟩ (frobWMaskedWord I))
        (twoWordHashMem (frobWMaskedWord I) ⟨1⟩
          (twoWordHashMem (hopeSourceWord I) (solcMappingSlot ⟨1⟩ (frobVMaskedWord I))
            (twoWordHashMem (frobVMaskedWord I) ⟨1⟩
              (twoWordHashMem (hopeSourceWord I) (solcMappingSlot ⟨1⟩ (frobUMaskedWord I))
                (twoWordHashMem (frobUMaskedWord I) ⟨1⟩
                  (frobIlkArtUpdatedMem σ I urnInkNew urnArtNew ilkArtNew)))))))
      (UInt256.ofNat 18) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ foldDebtSlot debtNew) k C)
    (hdust :
      UInt256.lor
        (UInt256.isZero
          (UInt256.lt tab (solcSlotWord σ I (frobIlkDustSlot I))))
        (UInt256.eq ⟨0⟩ urnArtNew) = ⟨0⟩) :
    RDrev vatBytecode g (initState cA gh bl σ σ₀ g A I) := by
  let memBase := frobIlkArtUpdatedMem σ I urnInkNew urnArtNew ilkArtNew
  let memU :=
    twoWordHashMem (hopeSourceWord I) (solcMappingSlot ⟨1⟩ (frobUMaskedWord I))
      (twoWordHashMem (frobUMaskedWord I) ⟨1⟩ memBase)
  let memV :=
    twoWordHashMem (hopeSourceWord I) (solcMappingSlot ⟨1⟩ (frobVMaskedWord I))
      (twoWordHashMem (frobVMaskedWord I) ⟨1⟩ memU)
  let memW :=
    twoWordHashMem (hopeSourceWord I) (solcMappingSlot ⟨1⟩ (frobWMaskedWord I))
      (twoWordHashMem (frobWMaskedWord I) ⟨1⟩ memV)
  let dust := solcSlotWord σ I (frobIlkDustSlot I)
  have hmemBaseSize : memBase.size = 576 := by
    dsimp [memBase]
    exact frobIlkArtUpdatedMem_size σ I urnInkNew urnArtNew ilkArtNew
  have hmemUSize : memU.size = 576 := by
    dsimp [memU]
    rw [twoWordHashMem_size_of_ge64]
    · rw [twoWordHashMem_size_of_ge64]
      · exact hmemBaseSize
      · rw [hmemBaseSize]; omega
    · rw [twoWordHashMem_size_of_ge64]
      · rw [hmemBaseSize]; omega
      · rw [hmemBaseSize]; omega
  have hmemVSize : memV.size = 576 := by
    dsimp [memV]
    rw [twoWordHashMem_size_of_ge64]
    · rw [twoWordHashMem_size_of_ge64]
      · exact hmemUSize
      · rw [hmemUSize]; omega
    · rw [twoWordHashMem_size_of_ge64]
      · rw [hmemUSize]; omega
      · rw [hmemUSize]; omega
  have hmemWSize : memW.size = 576 := by
    dsimp [memW]
    rw [twoWordHashMem_size_of_ge64]
    · rw [twoWordHashMem_size_of_ge64]
      · exact hmemVSize
      · rw [hmemVSize]; omega
    · rw [twoWordHashMem_size_of_ge64]
      · rw [hmemVSize]; omega
      · rw [hmemVSize]; omega
  have hread224 :
      memW.readWithPadding 224 32 = UInt256.toByteArray urnArtNew := by
    dsimp [memW, memV, memU, memBase]
    rw [twoWordHashMem_read32_above64 (readOff := 224)]
    · rw [twoWordHashMem_read32_above64 (readOff := 224)]
      · rw [twoWordHashMem_read32_above64 (readOff := 224)]
        · rw [twoWordHashMem_read32_above64 (readOff := 224)]
          · rw [twoWordHashMem_read32_above64 (readOff := 224)]
            · rw [twoWordHashMem_read32_above64 (readOff := 224)]
              · exact frobIlkArtUpdatedMem_read224 σ I urnInkNew urnArtNew ilkArtNew
              · omega
              · rw [hmemBaseSize]; omega
            · omega
            · rw [twoWordHashMem_size_of_ge64]
              · rw [hmemBaseSize]; omega
              · rw [hmemBaseSize]; omega
          · omega
          · rw [hmemUSize]; omega
        · omega
        · rw [twoWordHashMem_size_of_ge64]
          · rw [hmemUSize]; omega
          · rw [hmemUSize]; omega
      · omega
      · rw [hmemVSize]; omega
    · omega
    · rw [twoWordHashMem_size_of_ge64]
      · rw [hmemVSize]; omega
      · rw [hmemVSize]; omega
  have hread544 :
      memW.readWithPadding 544 32 = UInt256.toByteArray dust := by
    dsimp [memW, memV, memU, memBase, dust]
    rw [twoWordHashMem_read32_above64 (readOff := 544)]
    · rw [twoWordHashMem_read32_above64 (readOff := 544)]
      · rw [twoWordHashMem_read32_above64 (readOff := 544)]
        · rw [twoWordHashMem_read32_above64 (readOff := 544)]
          · rw [twoWordHashMem_read32_above64 (readOff := 544)]
            · rw [twoWordHashMem_read32_above64 (readOff := 544)]
              · exact frobIlkArtUpdatedMem_read544 σ I urnInkNew urnArtNew ilkArtNew
              · omega
              · rw [hmemBaseSize]
            · omega
            · rw [twoWordHashMem_size_of_ge64]
              · rw [hmemBaseSize]
              · rw [hmemBaseSize]; omega
          · omega
          · rw [hmemUSize]
        · omega
        · rw [twoWordHashMem_size_of_ge64]
          · rw [hmemUSize]
          · rw [hmemUSize]; omega
      · omega
      · rw [hmemVSize]
    · omega
    · rw [twoWordHashMem_size_of_ge64]
      · rw [hmemVSize]
      · rw [hmemVSize]; omega
  have rd3880 := h.jumpdest (by native_decide) (by evm_ov)
  have rd3883 := rd3880.push2 ⟨3903⟩ (by native_decide) (by evm_ov)
  have rd3884 := rd3883.dup5 (by native_decide) (by evm_ov)
  have rd3886 := rd3884.push1 ⟨32⟩ (by native_decide) (by evm_ov)
  have rd3887raw := rd3886.add (by native_decide) (by evm_ov)
  have hoff224 : (⟨192⟩ : UInt256) + ⟨32⟩ = ⟨224⟩ := by native_decide
  have hmload224 :
      (if ((⟨192⟩ : UInt256) + ⟨32⟩).toNat ≥ memW.size
          ∨ ((⟨192⟩ : UInt256) + ⟨32⟩) ≥ UInt256.ofNat 18 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
          (memW.readWithPadding (((⟨192⟩ : UInt256) + ⟨32⟩).toNat) 32))) =
        urnArtNew := by
    rw [hoff224]
    exact mloadWordValue_of_readWithPadding
      (by rw [show (⟨224⟩ : UInt256).toNat = 224 from by decide, hmemWSize]; omega)
      (by native_decide)
      (by
        simpa [show (⟨224⟩ : UInt256).toNat = 224 from by decide] using hread224)
  have rd3887raw' := rd3887raw.mload 0 urnArtNew (UInt256.ofNat 18)
    (by native_decide) mem_cost hmload224 (by native_decide) (by evm_ov)
  have rd3887 := by
    simpa [hoff224, memW] using rd3887raw'
  have rd3888 := rd3887.push1 ⟨0⟩ (by native_decide) (by evm_ov)
  have rd3890 := rd3888.eq (by native_decide) (by evm_ov)
  have rd3891 := rd3890.dup5 (by native_decide) (by evm_ov)
  have rd3892 := rd3891.push1 ⟨128⟩ (by native_decide) (by evm_ov)
  have rd3895raw := rd3892.add (by native_decide) (by evm_ov)
  have hoff544 : (⟨416⟩ : UInt256) + ⟨128⟩ = ⟨544⟩ := by native_decide
  have hmload544 :
      (if ((⟨416⟩ : UInt256) + ⟨128⟩).toNat ≥ memW.size
          ∨ ((⟨416⟩ : UInt256) + ⟨128⟩) ≥ UInt256.ofNat 18 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
          (memW.readWithPadding (((⟨416⟩ : UInt256) + ⟨128⟩).toNat) 32))) =
        dust := by
    rw [hoff544]
    exact mloadWordValue_of_readWithPadding
      (by rw [show (⟨544⟩ : UInt256).toNat = 544 from by decide, hmemWSize]; omega)
      (by native_decide)
      (by
        simpa [show (⟨544⟩ : UInt256).toNat = 544 from by decide] using hread544)
  have rd3895raw' := rd3895raw.mload 0 dust (UInt256.ofNat 18)
    (by native_decide) mem_cost hmload544 (by native_decide) (by evm_ov)
  have rd3895 := by
    simpa [hoff544, memW] using rd3895raw'
  have rd3896 := rd3895.dup4 (by native_decide) (by evm_ov)
  have rd3897 := rd3896.lt (by native_decide) (by evm_ov)
  have rd3898 := rd3897.iszero (by native_decide) (by evm_ov)
  have rd3902 := rd3898.push2 ⟨6791⟩ (by native_decide) (by evm_ov)
  have rd6791 := rd3902.jump (by native_decide) (by jump_dest) (by evm_ov)
  have rd3903 := evm_run rd6791 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw lor (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw jump (by native_decide) (by jump_dest) (by evm_ov)]
  have rd3907 := evm_run rd3903 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push2 ⟨3963⟩ (by native_decide) (by evm_ov)]
  have rdFall := by
    simpa [memW, dust] using
      rd3907.jumpiNT (by native_decide) hdust (by evm_ov)
  exact RD.solcErrorStringRevertTail576
    (code := vatBytecode) (pc := ⟨3908⟩) (len := ⟨8⟩)
    (rawWord := ⟨1556095976725109981⟩) (shift := ⟨194⟩)
    (word := UInt256.shiftLeft ⟨1556095976725109981⟩ ⟨194⟩)
    (op := .PUSH8) (width := 8) rdFall
    (by unfold solcErrorStringRevertTailWf; repeat' first | apply And.intro | native_decide)
    (by native_decide) rfl
    hmemWSize
    (by
      exact twoWordHashMem_read64_of_size576 (hopeSourceWord I)
        (solcMappingSlot ⟨1⟩ (frobWMaskedWord I))
        (twoWordHashMem_size_576 (frobWMaskedWord I) ⟨1⟩
          (twoWordHashMem_size_576 (hopeSourceWord I)
            (solcMappingSlot ⟨1⟩ (frobVMaskedWord I))
            (twoWordHashMem_size_576 (frobVMaskedWord I) ⟨1⟩
              (twoWordHashMem_size_576 (hopeSourceWord I)
                (solcMappingSlot ⟨1⟩ (frobUMaskedWord I))
                (twoWordHashMem_size_576 (frobUMaskedWord I) ⟨1⟩
                  (frobIlkArtUpdatedMem_size σ I urnInkNew urnArtNew ilkArtNew))))))
        (twoWordHashMem_read64_of_size576 (frobWMaskedWord I) ⟨1⟩
          (twoWordHashMem_size_576 (hopeSourceWord I)
            (solcMappingSlot ⟨1⟩ (frobVMaskedWord I))
            (twoWordHashMem_size_576 (frobVMaskedWord I) ⟨1⟩
              (twoWordHashMem_size_576 (hopeSourceWord I)
                (solcMappingSlot ⟨1⟩ (frobUMaskedWord I))
                (twoWordHashMem_size_576 (frobUMaskedWord I) ⟨1⟩
                  (frobIlkArtUpdatedMem_size σ I urnInkNew urnArtNew ilkArtNew)))))
          (twoWordHashMem_read64_of_size576 (hopeSourceWord I)
            (solcMappingSlot ⟨1⟩ (frobVMaskedWord I))
            (twoWordHashMem_size_576 (frobVMaskedWord I) ⟨1⟩
              (twoWordHashMem_size_576 (hopeSourceWord I)
                (solcMappingSlot ⟨1⟩ (frobUMaskedWord I))
                (twoWordHashMem_size_576 (frobUMaskedWord I) ⟨1⟩
                  (frobIlkArtUpdatedMem_size σ I urnInkNew urnArtNew ilkArtNew))))
            (twoWordHashMem_read64_of_size576 (frobVMaskedWord I) ⟨1⟩
              (twoWordHashMem_size_576 (hopeSourceWord I)
                (solcMappingSlot ⟨1⟩ (frobUMaskedWord I))
                (twoWordHashMem_size_576 (frobUMaskedWord I) ⟨1⟩
                  (frobIlkArtUpdatedMem_size σ I urnInkNew urnArtNew ilkArtNew)))
              (twoWordHashMem_read64_of_size576 (hopeSourceWord I)
                (solcMappingSlot ⟨1⟩ (frobUMaskedWord I))
                (twoWordHashMem_size_576 (frobUMaskedWord I) ⟨1⟩
                  (frobIlkArtUpdatedMem_size σ I urnInkNew urnArtNew ilkArtNew))
                (twoWordHashMem_read64_of_size576 (frobUMaskedWord I) ⟨1⟩
                  (frobIlkArtUpdatedMem_size σ I urnInkNew urnArtNew ilkArtNew)
                  (frobIlkArtUpdatedMem_read64 σ I urnInkNew urnArtNew ilkArtNew)))))))
    (by simp only [List.length_cons, List.length_nil]; omega)

set_option maxHeartbeats 1000000 in
theorem RD.vatFrobAuthorizationDustChecksSuccess
    {cA gh bl σ σ₀ A I} {g : Sat256} {k C : ℕ}
    {sel tab dtabWord urnInkNew urnArtNew ilkArtNew debtNew : UInt256}
    (h : RD vatBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3605⟩
      [tab, dtabWord, ⟨416⟩, ⟨192⟩, frobDartWord I, frobDinkWord I,
        frobWMaskedWord I, frobVMaskedWord I, frobUMaskedWord I, frobIWord I,
        ⟨524⟩, sel]
      (frobIlkArtUpdatedMem σ I urnInkNew urnArtNew ilkArtNew) (UInt256.ofNat 18)
      ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ foldDebtSlot debtNew) k C)
    (hu :
      UInt256.lor
        (UInt256.lor
          (UInt256.eq (vatSlotWord (frobUWishSlot I)
            (sstoreAccountMap I.codeOwner σ foldDebtSlot debtNew) I) ⟨1⟩)
          (UInt256.eq (frobUMaskedWord I) (hopeSourceWord I)))
        (UInt256.land
          (UInt256.isZero (UInt256.slt (frobDinkWord I) ⟨0⟩))
          (UInt256.isZero (UInt256.sgt (frobDartWord I) ⟨0⟩))) ≠ ⟨0⟩)
    (hv :
      UInt256.lor
        (UInt256.lor
          (UInt256.eq (vatSlotWord (frobVWishSlot I)
            (sstoreAccountMap I.codeOwner σ foldDebtSlot debtNew) I) ⟨1⟩)
          (UInt256.eq (frobVMaskedWord I) (hopeSourceWord I)))
        (UInt256.isZero (UInt256.sgt (frobDinkWord I) ⟨0⟩)) ≠ ⟨0⟩)
    (hw :
      UInt256.lor
        (UInt256.lor
          (UInt256.eq (vatSlotWord (frobWWishSlot I)
            (sstoreAccountMap I.codeOwner σ foldDebtSlot debtNew) I) ⟨1⟩)
          (UInt256.eq (frobWMaskedWord I) (hopeSourceWord I)))
        (UInt256.isZero (UInt256.slt (frobDartWord I) ⟨0⟩)) ≠ ⟨0⟩)
    (hdust :
      UInt256.lor
        (UInt256.isZero
          (UInt256.lt tab (solcSlotWord σ I (frobIlkDustSlot I))))
        (UInt256.eq ⟨0⟩ urnArtNew) ≠ ⟨0⟩) :
    ∃ k' C',
      RD vatBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3963⟩
        [tab, dtabWord, ⟨416⟩, ⟨192⟩, frobDartWord I, frobDinkWord I,
          frobWMaskedWord I, frobVMaskedWord I, frobUMaskedWord I, frobIWord I,
          ⟨524⟩, sel]
        (twoWordHashMem (hopeSourceWord I) (solcMappingSlot ⟨1⟩ (frobWMaskedWord I))
          (twoWordHashMem (frobWMaskedWord I) ⟨1⟩
            (twoWordHashMem (hopeSourceWord I) (solcMappingSlot ⟨1⟩ (frobVMaskedWord I))
              (twoWordHashMem (frobVMaskedWord I) ⟨1⟩
                (twoWordHashMem (hopeSourceWord I) (solcMappingSlot ⟨1⟩ (frobUMaskedWord I))
                  (twoWordHashMem (frobUMaskedWord I) ⟨1⟩
                    (frobIlkArtUpdatedMem σ I urnInkNew urnArtNew ilkArtNew)))))))
        (UInt256.ofNat 18) ByteArray.empty
        (cA, sstoreAccountMap I.codeOwner σ foldDebtSlot debtNew) k' C' := by
  obtain ⟨_, _, hU⟩ := RD.vatFrobUWishCheckSuccess (h := h) hu
  obtain ⟨_, _, hV⟩ := RD.vatFrobVWishCheckSuccess (h := hU) hv
  obtain ⟨_, _, hW⟩ := RD.vatFrobWWishCheckSuccess (h := hV) hw
  exact RD.vatFrobDustCheckSuccess (h := hW) hdust

theorem RD.vatFrobGemSubSuccess
    {cA gh bl σInit σ σ₀ A I} {g : Sat256} {k C : ℕ}
    {sel tab dtabWord : UInt256} {mem : ByteArray}
    (h : RD vatBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨3963⟩
      [tab, dtabWord, ⟨416⟩, ⟨192⟩, frobDartWord I, frobDinkWord I,
        frobWMaskedWord I, frobVMaskedWord I, frobUMaskedWord I, frobIWord I,
        ⟨524⟩, sel]
      mem (UInt256.ofNat 18) ByteArray.empty (cA, σ) k C)
    (hmem : 64 ≤ mem.size)
    (hpos :
      UInt256.sgt (frobDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.gt
          (UInt256.sub (solcSlotWord σ I (frobGemVSlot I)) (frobDinkWord I))
          (solcSlotWord σ I (frobGemVSlot I)) = ⟨0⟩)
    (hneg :
      UInt256.slt (frobDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.lt
          (UInt256.sub (solcSlotWord σ I (frobGemVSlot I)) (frobDinkWord I))
          (solcSlotWord σ I (frobGemVSlot I)) = ⟨0⟩) :
    ∃ k' C',
      RD vatBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨4008⟩
        [UInt256.sub (solcSlotWord σ I (frobGemVSlot I)) (frobDinkWord I),
          tab, dtabWord, ⟨416⟩, ⟨192⟩, frobDartWord I, frobDinkWord I,
          frobWMaskedWord I, frobVMaskedWord I, frobUMaskedWord I, frobIWord I,
          ⟨524⟩, sel]
        (twoWordHashMem (frobVMaskedWord I) (solcMappingSlot ⟨4⟩ (frobIWord I))
          (twoWordHashMem (frobIWord I) ⟨4⟩ mem))
        (UInt256.ofNat 18) ByteArray.empty (cA, σ) k' C' := by
  let gemBase := solcMappingSlot ⟨4⟩ (frobIWord I)
  let gemSlot := frobGemVSlot I
  let gemOld := solcSlotWord σ I gemSlot
  have rd3964 := h.jumpdest (by native_decide) (by evm_ov)
  have rd3966 := rd3964.push1 ⟨0⟩ (by native_decide) (by evm_ov)
  have rd3967 := rd3966.dup11 (by native_decide) (by evm_ov)
  have rd3968 := rd3967.dup2 (by native_decide) (by evm_ov)
  have rd3969 := rd3968.mstore 0 (wordAt0Mem (frobIWord I) mem)
    (UInt256.ofNat 18) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd3971 := rd3969.push1 ⟨4⟩ (by native_decide) (by evm_ov)
  have rd3973 := rd3971.push1 ⟨32⟩ (by native_decide) (by evm_ov)
  have rd3974 := rd3973.swap1 (by native_decide) (by evm_ov)
  have rd3975 := rd3974.dup2 (by native_decide) (by evm_ov)
  have rd3976 := rd3975.mstore 0 (twoWordHashMem (frobIWord I) ⟨4⟩ mem)
    (UInt256.ofNat 18) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd3978 := rd3976.push1 ⟨64⟩ (by native_decide) (by evm_ov)
  have rd3979 := rd3978.dup1 (by native_decide) (by evm_ov)
  have rd3980 := rd3979.dup4 (by native_decide) (by evm_ov)
  have hgemBase :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((twoWordHashMem (frobIWord I) ⟨4⟩ mem).readWithPadding 0 64))) =
        gemBase := by
    exact twoWordHashMem_solcMappingSlot_of_ge64 ⟨4⟩ (frobIWord I) hmem
  have rd3981 := rd3980.keccak256 0 gemBase (UInt256.ofNat 18) (by native_decide)
    mem_cost hgemBase (by native_decide) (by evm_ov)
  have rd3983 := rd3981.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  have rd3985 := rd3983.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  have rd3987 := rd3985.push1 ⟨160⟩ (by native_decide) (by evm_ov)
  have rd3988 := rd3987.shl (by native_decide) (by evm_ov)
  have rd3989 := rd3988.sub (by native_decide) (by evm_ov)
  have rd3990 := rd3989.dup13 (by native_decide) (by evm_ov)
  have rd3991pre := rd3990.and (by native_decide) (by evm_ov)
  have hmask :
      UInt256.land (frobVMaskedWord I)
        (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩) =
        frobVMaskedWord I := by
    rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by decide]
    exact frobVMaskedWord_clean I
  rw [hmask] at rd3991pre
  have rd3992 := rd3991pre.dup5 (by native_decide) (by evm_ov)
  have rd3993 := rd3992.mstore 0
    (wordAt0Mem (frobVMaskedWord I) (twoWordHashMem (frobIWord I) ⟨4⟩ mem))
    (UInt256.ofNat 18) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd3994 := rd3993.swap1 (by native_decide) (by evm_ov)
  have rd3995 := rd3994.swap2 (by native_decide) (by evm_ov)
  have rd3996 := rd3995.mstore 0
    (twoWordHashMem (frobVMaskedWord I) gemBase
      (twoWordHashMem (frobIWord I) ⟨4⟩ mem))
    (UInt256.ofNat 18) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd3997 := rd3996.swap1 (by native_decide) (by evm_ov)
  have hmemGemBase :
      64 ≤ (twoWordHashMem (frobIWord I) ⟨4⟩ mem).size := by
    rw [twoWordHashMem_size_of_ge64]
    · exact hmem
    · exact hmem
  have hgemSlot :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((twoWordHashMem (frobVMaskedWord I) gemBase
            (twoWordHashMem (frobIWord I) ⟨4⟩ mem)).readWithPadding 0 64))) =
        gemSlot := by
    simpa [gemSlot, frobGemVSlot, gemBase] using
      twoWordHashMem_solcMappingSlot_of_ge64 gemBase (frobVMaskedWord I) hmemGemBase
  have rd3998 := rd3997.keccak256 0 gemSlot (UInt256.ofNat 18)
    (by native_decide) mem_cost hgemSlot (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd3999raw⟩ := rd3998.sload (by native_decide) (by evm_ov)
  have hrd3999 :
      ∃ k' C', RD vatBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨3999⟩
        [gemOld, tab, dtabWord, ⟨416⟩, ⟨192⟩, frobDartWord I, frobDinkWord I,
          frobWMaskedWord I, frobVMaskedWord I, frobUMaskedWord I, frobIWord I,
          ⟨524⟩, sel]
        (twoWordHashMem (frobVMaskedWord I) gemBase
          (twoWordHashMem (frobIWord I) ⟨4⟩ mem))
        (UInt256.ofNat 18) ByteArray.empty (cA, σ) k' C' := by
    exact ⟨_, _, by simpa [gemOld, gemSlot, solcSlotWord] using rd3999raw⟩
  obtain ⟨_, _, rd3999⟩ := hrd3999
  have rd4002 := rd3999.push2 ⟨4008⟩ (by native_decide) (by evm_ov)
  have rd4003 := rd4002.swap1 (by native_decide) (by evm_ov)
  have rd4004 := rd4003.dup8 (by native_decide) (by evm_ov)
  have rd4007 := rd4004.push2 ⟨6795⟩ (by native_decide) (by evm_ov)
  have rd6795 := rd4007.jump (by native_decide) (by jump_dest) (by evm_ov)
  obtain ⟨_, _, rd4008⟩ := RD.vatSignedSubOk
    (x := gemOld) (y := frobDinkWord I) (ret := ⟨4008⟩)
    (R := tab :: dtabWord :: (⟨416⟩ : UInt256) :: (⟨192⟩ : UInt256) ::
      frobDartWord I :: frobDinkWord I :: frobWMaskedWord I ::
      frobVMaskedWord I :: frobUMaskedWord I :: frobIWord I :: ⟨524⟩ :: sel :: [])
    rd6795
    (by simpa [gemOld, gemSlot] using hpos)
    (by simpa [gemOld, gemSlot] using hneg)
    (by jump_dest) (by simp)
  exact ⟨_, _, by
    simpa [gemOld, gemSlot, gemBase] using rd4008⟩

theorem RD.vatFrobGemSubRevert
    {cA gh bl σInit σ σ₀ A I} {g : Sat256} {k C : ℕ}
    {sel tab dtabWord : UInt256} {mem : ByteArray}
    (h : RD vatBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨3963⟩
      [tab, dtabWord, ⟨416⟩, ⟨192⟩, frobDartWord I, frobDinkWord I,
        frobWMaskedWord I, frobVMaskedWord I, frobUMaskedWord I, frobIWord I,
        ⟨524⟩, sel]
      mem (UInt256.ofNat 18) ByteArray.empty (cA, σ) k C)
    (hmem : 64 ≤ mem.size)
    (hfail :
      ¬ (UInt256.sgt (frobDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.gt
          (UInt256.sub (solcSlotWord σ I (frobGemVSlot I)) (frobDinkWord I))
          (solcSlotWord σ I (frobGemVSlot I)) = ⟨0⟩) ∨
      (UInt256.sgt (frobDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.gt
          (UInt256.sub (solcSlotWord σ I (frobGemVSlot I)) (frobDinkWord I))
          (solcSlotWord σ I (frobGemVSlot I)) = ⟨0⟩) ∧
        ¬ (UInt256.slt (frobDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
          UInt256.lt
            (UInt256.sub (solcSlotWord σ I (frobGemVSlot I)) (frobDinkWord I))
            (solcSlotWord σ I (frobGemVSlot I)) = ⟨0⟩)) :
    RDrev vatBytecode g (initState cA gh bl σInit σ₀ g A I) := by
  let gemBase := solcMappingSlot ⟨4⟩ (frobIWord I)
  let gemSlot := frobGemVSlot I
  let gemOld := solcSlotWord σ I gemSlot
  have rd3964 := h.jumpdest (by native_decide) (by evm_ov)
  have rd3966 := rd3964.push1 ⟨0⟩ (by native_decide) (by evm_ov)
  have rd3967 := rd3966.dup11 (by native_decide) (by evm_ov)
  have rd3968 := rd3967.dup2 (by native_decide) (by evm_ov)
  have rd3969 := rd3968.mstore 0 (wordAt0Mem (frobIWord I) mem)
    (UInt256.ofNat 18) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd3971 := rd3969.push1 ⟨4⟩ (by native_decide) (by evm_ov)
  have rd3973 := rd3971.push1 ⟨32⟩ (by native_decide) (by evm_ov)
  have rd3974 := rd3973.swap1 (by native_decide) (by evm_ov)
  have rd3975 := rd3974.dup2 (by native_decide) (by evm_ov)
  have rd3976 := rd3975.mstore 0 (twoWordHashMem (frobIWord I) ⟨4⟩ mem)
    (UInt256.ofNat 18) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd3978 := rd3976.push1 ⟨64⟩ (by native_decide) (by evm_ov)
  have rd3979 := rd3978.dup1 (by native_decide) (by evm_ov)
  have rd3980 := rd3979.dup4 (by native_decide) (by evm_ov)
  have hgemBase :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((twoWordHashMem (frobIWord I) ⟨4⟩ mem).readWithPadding 0 64))) =
        gemBase := by
    exact twoWordHashMem_solcMappingSlot_of_ge64 ⟨4⟩ (frobIWord I) hmem
  have rd3981 := rd3980.keccak256 0 gemBase (UInt256.ofNat 18)
    (by native_decide) mem_cost hgemBase (by native_decide) (by evm_ov)
  have rd3983 := rd3981.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  have rd3985 := rd3983.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  have rd3987 := rd3985.push1 ⟨160⟩ (by native_decide) (by evm_ov)
  have rd3988 := rd3987.shl (by native_decide) (by evm_ov)
  have rd3989 := rd3988.sub (by native_decide) (by evm_ov)
  have rd3990 := rd3989.dup13 (by native_decide) (by evm_ov)
  have rd3991pre := rd3990.and (by native_decide) (by evm_ov)
  have hmask :
      UInt256.land (frobVMaskedWord I)
        (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩) =
        frobVMaskedWord I := by
    rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by decide]
    exact frobVMaskedWord_clean I
  rw [hmask] at rd3991pre
  have rd3992 := rd3991pre.dup5 (by native_decide) (by evm_ov)
  have rd3993 := rd3992.mstore 0
    (wordAt0Mem (frobVMaskedWord I) (twoWordHashMem (frobIWord I) ⟨4⟩ mem))
    (UInt256.ofNat 18) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd3994 := rd3993.swap1 (by native_decide) (by evm_ov)
  have rd3995 := rd3994.swap2 (by native_decide) (by evm_ov)
  have rd3996 := rd3995.mstore 0
    (twoWordHashMem (frobVMaskedWord I) gemBase
      (twoWordHashMem (frobIWord I) ⟨4⟩ mem))
    (UInt256.ofNat 18) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd3997 := rd3996.swap1 (by native_decide) (by evm_ov)
  have hmemGemBase :
      64 ≤ (twoWordHashMem (frobIWord I) ⟨4⟩ mem).size := by
    rw [twoWordHashMem_size_of_ge64]
    · exact hmem
    · exact hmem
  have hgemSlot :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((twoWordHashMem (frobVMaskedWord I) gemBase
            (twoWordHashMem (frobIWord I) ⟨4⟩ mem)).readWithPadding 0 64))) =
        gemSlot := by
    simpa [gemSlot, frobGemVSlot, gemBase] using
      twoWordHashMem_solcMappingSlot_of_ge64 gemBase (frobVMaskedWord I) hmemGemBase
  have rd3998 := rd3997.keccak256 0 gemSlot (UInt256.ofNat 18)
    (by native_decide) mem_cost hgemSlot (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd3999raw⟩ := rd3998.sload (by native_decide) (by evm_ov)
  have hrd3999 :
      ∃ k' C', RD vatBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨3999⟩
        [gemOld, tab, dtabWord, ⟨416⟩, ⟨192⟩, frobDartWord I, frobDinkWord I,
          frobWMaskedWord I, frobVMaskedWord I, frobUMaskedWord I, frobIWord I,
          ⟨524⟩, sel]
        (twoWordHashMem (frobVMaskedWord I) gemBase
          (twoWordHashMem (frobIWord I) ⟨4⟩ mem))
        (UInt256.ofNat 18) ByteArray.empty (cA, σ) k' C' := by
    exact ⟨_, _, by simpa [gemOld, gemSlot, solcSlotWord] using rd3999raw⟩
  obtain ⟨_, _, rd3999⟩ := hrd3999
  have rd4002 := rd3999.push2 ⟨4008⟩ (by native_decide) (by evm_ov)
  have rd4003 := rd4002.swap1 (by native_decide) (by evm_ov)
  have rd4004 := rd4003.dup8 (by native_decide) (by evm_ov)
  have rd4007 := rd4004.push2 ⟨6795⟩ (by native_decide) (by evm_ov)
  have rd6795 := rd4007.jump (by native_decide) (by jump_dest) (by evm_ov)
  exact RD.vatSignedSubRevert
    (x := gemOld) (y := frobDinkWord I) (ret := ⟨4008⟩)
    (R := tab :: dtabWord :: (⟨416⟩ : UInt256) :: (⟨192⟩ : UInt256) ::
      frobDartWord I :: frobDinkWord I :: frobWMaskedWord I ::
      frobVMaskedWord I :: frobUMaskedWord I :: frobIWord I :: ⟨524⟩ :: sel :: [])
    rd6795
    (by simpa [gemOld, gemSlot] using hfail)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem RD.vatFrobGemStoreDaiAddSuccess
    {cA gh bl σInit σ σ₀ A I} {g : Sat256} {k C : ℕ}
    {sel tab dtabWord gemNew : UInt256} {mem : ByteArray}
    (h : RD vatBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨4008⟩
      [gemNew, tab, dtabWord, ⟨416⟩, ⟨192⟩, frobDartWord I, frobDinkWord I,
        frobWMaskedWord I, frobVMaskedWord I, frobUMaskedWord I, frobIWord I,
        ⟨524⟩, sel]
      mem (UInt256.ofNat 18) ByteArray.empty (cA, σ) k C)
    (hmem : 64 ≤ mem.size)
    (hperm : I.perm = true)
    (hneg :
      UInt256.slt dtabWord ⟨0⟩ = ⟨0⟩ ∨
        UInt256.gt
          (dtabWord +
            solcSlotWord (sstoreAccountMap I.codeOwner σ (frobGemVSlot I) gemNew)
              I (frobDaiWSlot I))
          (solcSlotWord (sstoreAccountMap I.codeOwner σ (frobGemVSlot I) gemNew)
            I (frobDaiWSlot I)) = ⟨0⟩)
    (hpos :
      UInt256.sgt dtabWord ⟨0⟩ = ⟨0⟩ ∨
        UInt256.lt
          (dtabWord +
            solcSlotWord (sstoreAccountMap I.codeOwner σ (frobGemVSlot I) gemNew)
              I (frobDaiWSlot I))
          (solcSlotWord (sstoreAccountMap I.codeOwner σ (frobGemVSlot I) gemNew)
            I (frobDaiWSlot I)) = ⟨0⟩) :
    ∃ k' C',
      RD vatBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨4069⟩
        [dtabWord +
            solcSlotWord (sstoreAccountMap I.codeOwner σ (frobGemVSlot I) gemNew)
              I (frobDaiWSlot I),
          tab, dtabWord, ⟨416⟩, ⟨192⟩, frobDartWord I, frobDinkWord I,
          frobWMaskedWord I, frobVMaskedWord I, frobUMaskedWord I, frobIWord I,
          ⟨524⟩, sel]
        (twoWordHashMem (frobWMaskedWord I) ⟨5⟩
          (twoWordHashMem (frobVMaskedWord I) (solcMappingSlot ⟨4⟩ (frobIWord I))
            (twoWordHashMem (frobIWord I) ⟨4⟩ mem)))
        (UInt256.ofNat 18) ByteArray.empty
        (cA, sstoreAccountMap I.codeOwner σ (frobGemVSlot I) gemNew) k' C' := by
  let gemBase := solcMappingSlot ⟨4⟩ (frobIWord I)
  let gemSlot := frobGemVSlot I
  let σGem := sstoreAccountMap I.codeOwner σ gemSlot gemNew
  let daiSlot := frobDaiWSlot I
  let daiOld := solcSlotWord σGem I daiSlot
  let daiNew := dtabWord + daiOld
  have rd4009 := h.jumpdest (by native_decide) (by evm_ov)
  have rd4011 := rd4009.push1 ⟨0⟩ (by native_decide) (by evm_ov)
  have rd4012 := rd4011.dup12 (by native_decide) (by evm_ov)
  have rd4013 := rd4012.dup2 (by native_decide) (by evm_ov)
  have rd4014 := rd4013.mstore 0 (wordAt0Mem (frobIWord I) mem)
    (UInt256.ofNat 18) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd4016 := rd4014.push1 ⟨4⟩ (by native_decide) (by evm_ov)
  have rd4018 := rd4016.push1 ⟨32⟩ (by native_decide) (by evm_ov)
  have rd4019 := rd4018.swap1 (by native_decide) (by evm_ov)
  have rd4020 := rd4019.dup2 (by native_decide) (by evm_ov)
  have rd4021 := rd4020.mstore 0 (twoWordHashMem (frobIWord I) ⟨4⟩ mem)
    (UInt256.ofNat 18) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd4023 := rd4021.push1 ⟨64⟩ (by native_decide) (by evm_ov)
  have rd4024 := rd4023.dup1 (by native_decide) (by evm_ov)
  have rd4025 := rd4024.dup4 (by native_decide) (by evm_ov)
  have hgemBase :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((twoWordHashMem (frobIWord I) ⟨4⟩ mem).readWithPadding 0 64))) =
        gemBase := by
    exact twoWordHashMem_solcMappingSlot_of_ge64 ⟨4⟩ (frobIWord I) hmem
  have rd4026 := rd4025.keccak256 0 gemBase (UInt256.ofNat 18) (by native_decide)
    mem_cost hgemBase (by native_decide) (by evm_ov)
  have rd4028 := rd4026.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  have rd4030 := rd4028.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  have rd4032 := rd4030.push1 ⟨160⟩ (by native_decide) (by evm_ov)
  have rd4033 := rd4032.shl (by native_decide) (by evm_ov)
  have rd4034 := rd4033.sub (by native_decide) (by evm_ov)
  have rd4035 := rd4034.dup1 (by native_decide) (by evm_ov)
  have rd4036 := rd4035.dup15 (by native_decide) (by evm_ov)
  have rd4037pre := rd4036.and (by native_decide) (by evm_ov)
  have hmaskV :
      UInt256.land (frobVMaskedWord I)
        (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩) =
        frobVMaskedWord I := by
    rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by decide]
    exact frobVMaskedWord_clean I
  rw [hmaskV] at rd4037pre
  have rd4038 := rd4037pre.dup6 (by native_decide) (by evm_ov)
  have rd4039 := rd4038.mstore 0
    (wordAt0Mem (frobVMaskedWord I) (twoWordHashMem (frobIWord I) ⟨4⟩ mem))
    (UInt256.ofNat 18) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd4040 := rd4039.swap1 (by native_decide) (by evm_ov)
  have rd4041 := rd4040.dup4 (by native_decide) (by evm_ov)
  have rd4042 := rd4041.mstore 0
    (twoWordHashMem (frobVMaskedWord I) gemBase
      (twoWordHashMem (frobIWord I) ⟨4⟩ mem))
    (UInt256.ofNat 18) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd4043 := rd4042.dup2 (by native_decide) (by evm_ov)
  have rd4044 := rd4043.dup5 (by native_decide) (by evm_ov)
  have hmemGemBase :
      64 ≤ (twoWordHashMem (frobIWord I) ⟨4⟩ mem).size := by
    rw [twoWordHashMem_size_of_ge64]
    · exact hmem
    · exact hmem
  have hgemSlot :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((twoWordHashMem (frobVMaskedWord I) gemBase
            (twoWordHashMem (frobIWord I) ⟨4⟩ mem)).readWithPadding 0 64))) =
        gemSlot := by
    simpa [gemSlot, frobGemVSlot, gemBase] using
      twoWordHashMem_solcMappingSlot_of_ge64 gemBase (frobVMaskedWord I) hmemGemBase
  have rd4045 := rd4044.keccak256 0 gemSlot (UInt256.ofNat 18)
    (by native_decide) mem_cost hgemSlot (by native_decide) (by evm_ov)
  have rd4046 := rd4045.swap5 (by native_decide) (by evm_ov)
  have rd4047 := rd4046.swap1 (by native_decide) (by evm_ov)
  have rd4048pre := rd4047.swap5 (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd4049raw⟩ := rd4048pre.sstore hperm (by native_decide) (by evm_ov)
  have rd4049 :
      ∃ k' C', RD vatBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨4049⟩
        [⟨64⟩, ⟨32⟩, ⟨0⟩,
          UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩,
          tab, dtabWord, ⟨416⟩, ⟨192⟩,
          frobDartWord I, frobDinkWord I,
          frobWMaskedWord I, frobVMaskedWord I, frobUMaskedWord I, frobIWord I,
          ⟨524⟩, sel]
        (twoWordHashMem (frobVMaskedWord I) gemBase
          (twoWordHashMem (frobIWord I) ⟨4⟩ mem))
        (UInt256.ofNat 18) ByteArray.empty (cA, σGem) k' C' := by
    exact ⟨_, _, by simpa [σGem, gemSlot, gemBase] using rd4049raw⟩
  obtain ⟨_, _, rd4049'⟩ := rd4049
  have rd4050 := rd4049'.swap3 (by native_decide) (by evm_ov)
  have rd4051 := rd4050.dup11 (by native_decide) (by evm_ov)
  have rd4052pre := rd4051.and (by native_decide) (by evm_ov)
  have hmaskW :
      UInt256.land (frobWMaskedWord I)
        (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩) =
        frobWMaskedWord I := by
    rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by decide]
    exact frobWMaskedWord_clean I
  rw [hmaskW] at rd4052pre
  have rd4053 := rd4052pre.dup3 (by native_decide) (by evm_ov)
  have rd4054 := rd4053.mstore 0
    (wordAt0Mem (frobWMaskedWord I)
      (twoWordHashMem (frobVMaskedWord I) gemBase
        (twoWordHashMem (frobIWord I) ⟨4⟩ mem)))
    (UInt256.ofNat 18) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd4056 := rd4054.push1 ⟨5⟩ (by native_decide) (by evm_ov)
  have rd4057 := rd4056.swap1 (by native_decide) (by evm_ov)
  have rd4058 := rd4057.mstore 0
    (twoWordHashMem (frobWMaskedWord I) ⟨5⟩
      (twoWordHashMem (frobVMaskedWord I) gemBase
        (twoWordHashMem (frobIWord I) ⟨4⟩ mem)))
    (UInt256.ofNat 18) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have hmemGem :
      64 ≤ (twoWordHashMem (frobVMaskedWord I) gemBase
        (twoWordHashMem (frobIWord I) ⟨4⟩ mem)).size := by
    rw [twoWordHashMem_size_of_ge64]
    · exact hmemGemBase
    · exact hmemGemBase
  have hdaiSlot :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((twoWordHashMem (frobWMaskedWord I) ⟨5⟩
            (twoWordHashMem (frobVMaskedWord I) gemBase
              (twoWordHashMem (frobIWord I) ⟨4⟩ mem))).readWithPadding 0 64))) =
        daiSlot := by
    simpa [daiSlot, frobDaiWSlot] using
      twoWordHashMem_solcMappingSlot_of_ge64 ⟨5⟩ (frobWMaskedWord I) hmemGem
  have rd4059 := rd4058.keccak256 0 daiSlot (UInt256.ofNat 18)
    (by native_decide) mem_cost hdaiSlot (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd4060raw⟩ := rd4059.sload (by native_decide) (by evm_ov)
  have hrd4060 :
      ∃ k' C', RD vatBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨4060⟩
        [daiOld, tab, dtabWord, ⟨416⟩, ⟨192⟩, frobDartWord I,
          frobDinkWord I, frobWMaskedWord I, frobVMaskedWord I,
          frobUMaskedWord I, frobIWord I, ⟨524⟩, sel]
        (twoWordHashMem (frobWMaskedWord I) ⟨5⟩
          (twoWordHashMem (frobVMaskedWord I) gemBase
            (twoWordHashMem (frobIWord I) ⟨4⟩ mem)))
        (UInt256.ofNat 18) ByteArray.empty (cA, σGem) k' C' := by
    exact ⟨_, _, by simpa [daiOld, daiSlot, solcSlotWord] using rd4060raw⟩
  obtain ⟨_, _, rd4060⟩ := hrd4060
  have rd4063 := rd4060.push2 ⟨4069⟩ (by native_decide) (by evm_ov)
  have rd4064 := rd4063.swap1 (by native_decide) (by evm_ov)
  have rd4065 := rd4064.dup4 (by native_decide) (by evm_ov)
  have rd4068 := rd4065.push2 ⟨6653⟩ (by native_decide) (by evm_ov)
  have rd6653 := rd4068.jump (by native_decide) (by jump_dest) (by evm_ov)
  obtain ⟨_, _, rd4069⟩ := RD.vatSignedAddOk
    (x := daiOld) (y := dtabWord) (ret := ⟨4069⟩)
    (R := tab :: dtabWord :: (⟨416⟩ : UInt256) :: (⟨192⟩ : UInt256) ::
      frobDartWord I :: frobDinkWord I :: frobWMaskedWord I ::
      frobVMaskedWord I :: frobUMaskedWord I :: frobIWord I :: ⟨524⟩ :: sel :: [])
    rd6653
    (by simpa [daiOld, daiNew, σGem, gemSlot, daiSlot] using hneg)
    (by simpa [daiOld, daiNew, σGem, gemSlot, daiSlot] using hpos)
    (by jump_dest) (by simp)
  exact ⟨_, _, by
    simpa [daiOld, daiNew, σGem, gemSlot, daiSlot, gemBase] using rd4069⟩

theorem RD.vatFrobGemStoreDaiAddRevert
    {cA gh bl σInit σ σ₀ A I} {g : Sat256} {k C : ℕ}
    {sel tab dtabWord gemNew : UInt256} {mem : ByteArray}
    (h : RD vatBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨4008⟩
      [gemNew, tab, dtabWord, ⟨416⟩, ⟨192⟩, frobDartWord I, frobDinkWord I,
        frobWMaskedWord I, frobVMaskedWord I, frobUMaskedWord I, frobIWord I,
        ⟨524⟩, sel]
      mem (UInt256.ofNat 18) ByteArray.empty (cA, σ) k C)
    (hmem : 64 ≤ mem.size)
    (hperm : I.perm = true)
    (hfail :
      ¬ (UInt256.slt dtabWord ⟨0⟩ = ⟨0⟩ ∨
        UInt256.gt
          (dtabWord +
            solcSlotWord (sstoreAccountMap I.codeOwner σ (frobGemVSlot I) gemNew)
              I (frobDaiWSlot I))
          (solcSlotWord (sstoreAccountMap I.codeOwner σ (frobGemVSlot I) gemNew)
            I (frobDaiWSlot I)) = ⟨0⟩) ∨
      (UInt256.slt dtabWord ⟨0⟩ = ⟨0⟩ ∨
        UInt256.gt
          (dtabWord +
            solcSlotWord (sstoreAccountMap I.codeOwner σ (frobGemVSlot I) gemNew)
              I (frobDaiWSlot I))
          (solcSlotWord (sstoreAccountMap I.codeOwner σ (frobGemVSlot I) gemNew)
            I (frobDaiWSlot I)) = ⟨0⟩) ∧
        ¬ (UInt256.sgt dtabWord ⟨0⟩ = ⟨0⟩ ∨
          UInt256.lt
            (dtabWord +
              solcSlotWord (sstoreAccountMap I.codeOwner σ (frobGemVSlot I) gemNew)
                I (frobDaiWSlot I))
            (solcSlotWord (sstoreAccountMap I.codeOwner σ (frobGemVSlot I) gemNew)
              I (frobDaiWSlot I)) = ⟨0⟩)) :
    RDrev vatBytecode g (initState cA gh bl σInit σ₀ g A I) := by
  let gemBase := solcMappingSlot ⟨4⟩ (frobIWord I)
  let gemSlot := frobGemVSlot I
  let σGem := sstoreAccountMap I.codeOwner σ gemSlot gemNew
  let daiSlot := frobDaiWSlot I
  let daiOld := solcSlotWord σGem I daiSlot
  let daiNew := dtabWord + daiOld
  have rd4009 := h.jumpdest (by native_decide) (by evm_ov)
  have rd4011 := rd4009.push1 ⟨0⟩ (by native_decide) (by evm_ov)
  have rd4012 := rd4011.dup12 (by native_decide) (by evm_ov)
  have rd4013 := rd4012.dup2 (by native_decide) (by evm_ov)
  have rd4014 := rd4013.mstore 0 (wordAt0Mem (frobIWord I) mem)
    (UInt256.ofNat 18) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd4016 := rd4014.push1 ⟨4⟩ (by native_decide) (by evm_ov)
  have rd4018 := rd4016.push1 ⟨32⟩ (by native_decide) (by evm_ov)
  have rd4019 := rd4018.swap1 (by native_decide) (by evm_ov)
  have rd4020 := rd4019.dup2 (by native_decide) (by evm_ov)
  have rd4021 := rd4020.mstore 0 (twoWordHashMem (frobIWord I) ⟨4⟩ mem)
    (UInt256.ofNat 18) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd4023 := rd4021.push1 ⟨64⟩ (by native_decide) (by evm_ov)
  have rd4024 := rd4023.dup1 (by native_decide) (by evm_ov)
  have rd4025 := rd4024.dup4 (by native_decide) (by evm_ov)
  have hgemBase :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((twoWordHashMem (frobIWord I) ⟨4⟩ mem).readWithPadding 0 64))) =
        gemBase := by
    exact twoWordHashMem_solcMappingSlot_of_ge64 ⟨4⟩ (frobIWord I) hmem
  have rd4026 := rd4025.keccak256 0 gemBase (UInt256.ofNat 18) (by native_decide)
    mem_cost hgemBase (by native_decide) (by evm_ov)
  have rd4028 := rd4026.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  have rd4030 := rd4028.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  have rd4032 := rd4030.push1 ⟨160⟩ (by native_decide) (by evm_ov)
  have rd4033 := rd4032.shl (by native_decide) (by evm_ov)
  have rd4034 := rd4033.sub (by native_decide) (by evm_ov)
  have rd4035 := rd4034.dup1 (by native_decide) (by evm_ov)
  have rd4036 := rd4035.dup15 (by native_decide) (by evm_ov)
  have rd4037pre := rd4036.and (by native_decide) (by evm_ov)
  have hmaskV :
      UInt256.land (frobVMaskedWord I)
        (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩) =
        frobVMaskedWord I := by
    rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by decide]
    exact frobVMaskedWord_clean I
  rw [hmaskV] at rd4037pre
  have rd4038 := rd4037pre.dup6 (by native_decide) (by evm_ov)
  have rd4039 := rd4038.mstore 0
    (wordAt0Mem (frobVMaskedWord I) (twoWordHashMem (frobIWord I) ⟨4⟩ mem))
    (UInt256.ofNat 18) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd4040 := rd4039.swap1 (by native_decide) (by evm_ov)
  have rd4041 := rd4040.dup4 (by native_decide) (by evm_ov)
  have rd4042 := rd4041.mstore 0
    (twoWordHashMem (frobVMaskedWord I) gemBase
      (twoWordHashMem (frobIWord I) ⟨4⟩ mem))
    (UInt256.ofNat 18) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd4043 := rd4042.dup2 (by native_decide) (by evm_ov)
  have rd4044 := rd4043.dup5 (by native_decide) (by evm_ov)
  have hmemGemBase :
      64 ≤ (twoWordHashMem (frobIWord I) ⟨4⟩ mem).size := by
    rw [twoWordHashMem_size_of_ge64]
    · exact hmem
    · exact hmem
  have hgemSlot :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((twoWordHashMem (frobVMaskedWord I) gemBase
            (twoWordHashMem (frobIWord I) ⟨4⟩ mem)).readWithPadding 0 64))) =
        gemSlot := by
    simpa [gemSlot, frobGemVSlot, gemBase] using
      twoWordHashMem_solcMappingSlot_of_ge64 gemBase (frobVMaskedWord I) hmemGemBase
  have rd4045 := rd4044.keccak256 0 gemSlot (UInt256.ofNat 18)
    (by native_decide) mem_cost hgemSlot (by native_decide) (by evm_ov)
  have rd4046 := rd4045.swap5 (by native_decide) (by evm_ov)
  have rd4047 := rd4046.swap1 (by native_decide) (by evm_ov)
  have rd4048pre := rd4047.swap5 (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd4049raw⟩ := rd4048pre.sstore hperm (by native_decide) (by evm_ov)
  have rd4049 :
      ∃ k' C', RD vatBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨4049⟩
        [⟨64⟩, ⟨32⟩, ⟨0⟩,
          UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩,
          tab, dtabWord, ⟨416⟩, ⟨192⟩,
          frobDartWord I, frobDinkWord I,
          frobWMaskedWord I, frobVMaskedWord I, frobUMaskedWord I, frobIWord I,
          ⟨524⟩, sel]
        (twoWordHashMem (frobVMaskedWord I) gemBase
          (twoWordHashMem (frobIWord I) ⟨4⟩ mem))
        (UInt256.ofNat 18) ByteArray.empty (cA, σGem) k' C' := by
    exact ⟨_, _, by simpa [σGem, gemSlot, gemBase] using rd4049raw⟩
  obtain ⟨_, _, rd4049'⟩ := rd4049
  have rd4050 := rd4049'.swap3 (by native_decide) (by evm_ov)
  have rd4051 := rd4050.dup11 (by native_decide) (by evm_ov)
  have rd4052pre := rd4051.and (by native_decide) (by evm_ov)
  have hmaskW :
      UInt256.land (frobWMaskedWord I)
        (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩) =
        frobWMaskedWord I := by
    rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by decide]
    exact frobWMaskedWord_clean I
  rw [hmaskW] at rd4052pre
  have rd4053 := rd4052pre.dup3 (by native_decide) (by evm_ov)
  have rd4054 := rd4053.mstore 0
    (wordAt0Mem (frobWMaskedWord I)
      (twoWordHashMem (frobVMaskedWord I) gemBase
        (twoWordHashMem (frobIWord I) ⟨4⟩ mem)))
    (UInt256.ofNat 18) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd4056 := rd4054.push1 ⟨5⟩ (by native_decide) (by evm_ov)
  have rd4057 := rd4056.swap1 (by native_decide) (by evm_ov)
  have rd4058 := rd4057.mstore 0
    (twoWordHashMem (frobWMaskedWord I) ⟨5⟩
      (twoWordHashMem (frobVMaskedWord I) gemBase
        (twoWordHashMem (frobIWord I) ⟨4⟩ mem)))
    (UInt256.ofNat 18) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have hmemGem :
      64 ≤ (twoWordHashMem (frobVMaskedWord I) gemBase
        (twoWordHashMem (frobIWord I) ⟨4⟩ mem)).size := by
    rw [twoWordHashMem_size_of_ge64]
    · exact hmemGemBase
    · exact hmemGemBase
  have hdaiSlot :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((twoWordHashMem (frobWMaskedWord I) ⟨5⟩
            (twoWordHashMem (frobVMaskedWord I) gemBase
              (twoWordHashMem (frobIWord I) ⟨4⟩ mem))).readWithPadding 0 64))) =
        daiSlot := by
    simpa [daiSlot, frobDaiWSlot] using
      twoWordHashMem_solcMappingSlot_of_ge64 ⟨5⟩ (frobWMaskedWord I) hmemGem
  have rd4059 := rd4058.keccak256 0 daiSlot (UInt256.ofNat 18)
    (by native_decide) mem_cost hdaiSlot (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd4060raw⟩ := rd4059.sload (by native_decide) (by evm_ov)
  have hrd4060 :
      ∃ k' C', RD vatBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨4060⟩
        [daiOld, tab, dtabWord, ⟨416⟩, ⟨192⟩, frobDartWord I,
          frobDinkWord I, frobWMaskedWord I, frobVMaskedWord I,
          frobUMaskedWord I, frobIWord I, ⟨524⟩, sel]
        (twoWordHashMem (frobWMaskedWord I) ⟨5⟩
          (twoWordHashMem (frobVMaskedWord I) gemBase
            (twoWordHashMem (frobIWord I) ⟨4⟩ mem)))
        (UInt256.ofNat 18) ByteArray.empty (cA, σGem) k' C' := by
    exact ⟨_, _, by simpa [daiOld, daiSlot, solcSlotWord] using rd4060raw⟩
  obtain ⟨_, _, rd4060⟩ := hrd4060
  have rd4063 := rd4060.push2 ⟨4069⟩ (by native_decide) (by evm_ov)
  have rd4064 := rd4063.swap1 (by native_decide) (by evm_ov)
  have rd4065 := rd4064.dup4 (by native_decide) (by evm_ov)
  have rd4068 := rd4065.push2 ⟨6653⟩ (by native_decide) (by evm_ov)
  have rd6653 := rd4068.jump (by native_decide) (by jump_dest) (by evm_ov)
  exact RD.vatSignedAddRevert
    (x := daiOld) (y := dtabWord) (ret := ⟨4069⟩)
    (R := tab :: dtabWord :: (⟨416⟩ : UInt256) :: (⟨192⟩ : UInt256) ::
      frobDartWord I :: frobDinkWord I :: frobWMaskedWord I ::
      frobVMaskedWord I :: frobUMaskedWord I :: frobIWord I :: ⟨524⟩ :: sel :: [])
    rd6653
    (by simpa [daiOld, daiNew, σGem, gemSlot, daiSlot] using hfail)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem RD.vatFrobDaiStoreSuccess
    {cA gh bl σInit σ σ₀ A I} {g : Sat256} {k C : ℕ}
    {sel tab dtabWord daiNew : UInt256} {mem : ByteArray}
    (h : RD vatBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨4069⟩
      [daiNew, tab, dtabWord, ⟨416⟩, ⟨192⟩, frobDartWord I, frobDinkWord I,
        frobWMaskedWord I, frobVMaskedWord I, frobUMaskedWord I, frobIWord I,
        ⟨524⟩, sel]
      mem (UInt256.ofNat 18) ByteArray.empty (cA, σ) k C)
    (hmem : 64 ≤ mem.size)
    (hperm : I.perm = true) :
    ∃ k' C',
      RD vatBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨4102⟩
        [⟨32⟩, ⟨0⟩, ⟨64⟩, tab, dtabWord, ⟨416⟩, ⟨192⟩,
          frobDartWord I, frobDinkWord I,
          UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩,
          frobVMaskedWord I, frobUMaskedWord I, frobIWord I, ⟨524⟩, sel]
        (twoWordHashMem (frobWMaskedWord I) ⟨5⟩ mem)
        (UInt256.ofNat 18) ByteArray.empty
        (cA, sstoreAccountMap I.codeOwner σ (frobDaiWSlot I) daiNew) k' C' := by
  let daiSlot := frobDaiWSlot I
  let σDai := sstoreAccountMap I.codeOwner σ daiSlot daiNew
  have rd4070 := h.jumpdest (by native_decide) (by evm_ov)
  have rd4072 := rd4070.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  have rd4074 := rd4072.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  have rd4076 := rd4074.push1 ⟨160⟩ (by native_decide) (by evm_ov)
  have rd4077 := rd4076.shl (by native_decide) (by evm_ov)
  have rd4078 := rd4077.sub (by native_decide) (by evm_ov)
  have rd4079 := rd4078.swap8 (by native_decide) (by evm_ov)
  have rd4080 := rd4079.dup9 (by native_decide) (by evm_ov)
  have rd4081pre := rd4080.and (by native_decide) (by evm_ov)
  have hmaskW :
      UInt256.land
        (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩)
        (frobWMaskedWord I) =
        frobWMaskedWord I := by
    rw [u256_land_comm]
    rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by decide]
    exact frobWMaskedWord_clean I
  rw [hmaskW] at rd4081pre
  have rd4083 := rd4081pre.push1 ⟨0⟩ (by native_decide) (by evm_ov)
  have rd4084 := rd4083.swap1 (by native_decide) (by evm_ov)
  have rd4085 := rd4084.dup2 (by native_decide) (by evm_ov)
  have rd4086 := rd4085.mstore 0 (wordAt0Mem (frobWMaskedWord I) mem)
    (UInt256.ofNat 18) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd4088 := rd4086.push1 ⟨5⟩ (by native_decide) (by evm_ov)
  have rd4090 := rd4088.push1 ⟨32⟩ (by native_decide) (by evm_ov)
  have rd4091 := rd4090.swap1 (by native_decide) (by evm_ov)
  have rd4092 := rd4091.dup2 (by native_decide) (by evm_ov)
  have rd4093 := rd4092.mstore 0 (twoWordHashMem (frobWMaskedWord I) ⟨5⟩ mem)
    (UInt256.ofNat 18) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd4095 := rd4093.push1 ⟨64⟩ (by native_decide) (by evm_ov)
  have rd4096 := rd4095.dup1 (by native_decide) (by evm_ov)
  have rd4097 := rd4096.dup4 (by native_decide) (by evm_ov)
  have hdaiSlot :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((twoWordHashMem (frobWMaskedWord I) ⟨5⟩ mem).readWithPadding
            0 64))) =
        daiSlot := by
    simpa [daiSlot, frobDaiWSlot] using
      twoWordHashMem_solcMappingSlot_of_ge64 ⟨5⟩ (frobWMaskedWord I) hmem
  have rd4098 := rd4097.keccak256 0 daiSlot (UInt256.ofNat 18)
    (by native_decide) mem_cost hdaiSlot (by native_decide) (by evm_ov)
  have rd4099 := rd4098.swap4 (by native_decide) (by evm_ov)
  have rd4100 := rd4099.swap1 (by native_decide) (by evm_ov)
  have rd4101pre := rd4100.swap4 (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd4102raw⟩ := rd4101pre.sstore hperm (by native_decide) (by evm_ov)
  exact ⟨_, _, by
    simpa [σDai, daiSlot] using rd4102raw⟩

theorem RD.vatFrobFinalUrnInkStoreSuccess
    {cA gh bl σInit σ σ₀ A I} {g : Sat256} {k C : ℕ}
    {sel tab dtabWord urnInkNew : UInt256} {mem : ByteArray}
    (h : RD vatBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨4102⟩
      [⟨32⟩, ⟨0⟩, ⟨64⟩, tab, dtabWord, ⟨416⟩, ⟨192⟩,
        frobDartWord I, frobDinkWord I,
        UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩,
        frobVMaskedWord I, frobUMaskedWord I, frobIWord I, ⟨524⟩, sel]
      mem (UInt256.ofNat 18) ByteArray.empty (cA, σ) k C)
    (hmemSize : mem.size = 576)
    (hread192 : mem.readWithPadding 192 32 = UInt256.toByteArray urnInkNew)
    (hperm : I.perm = true) :
    ∃ k' C',
      RD vatBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨4129⟩
        [frobUrnInkSlot I, ⟨0⟩, ⟨64⟩, tab, dtabWord, ⟨416⟩, ⟨192⟩,
          frobDartWord I, frobDinkWord I, ⟨3⟩, frobVMaskedWord I, ⟨32⟩,
          frobIWord I, ⟨524⟩, sel]
        (twoWordHashMem (frobUMaskedWord I) (solcMappingSlot ⟨3⟩ (frobIWord I))
          (twoWordHashMem (frobIWord I) ⟨3⟩ mem))
        (UInt256.ofNat 18) ByteArray.empty
        (cA, sstoreAccountMap I.codeOwner σ (frobUrnInkSlot I) urnInkNew) k' C' := by
  let urnInner := solcMappingSlot ⟨3⟩ (frobIWord I)
  let urnSlot := frobUrnInkSlot I
  let memUrn := twoWordHashMem (frobUMaskedWord I) urnInner
    (twoWordHashMem (frobIWord I) ⟨3⟩ mem)
  have rd4103 := h.dup13 (by native_decide) (by evm_ov)
  have rd4104 := rd4103.dup3 (by native_decide) (by evm_ov)
  have rd4105 := rd4104.mstore 0 (wordAt0Mem (frobIWord I) mem)
    (UInt256.ofNat 18) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd4107 := rd4105.push1 ⟨3⟩ (by native_decide) (by evm_ov)
  have rd4108 := rd4107.dup1 (by native_decide) (by evm_ov)
  have rd4109 := rd4108.dup3 (by native_decide) (by evm_ov)
  have rd4110 := rd4109.mstore 0 (twoWordHashMem (frobIWord I) ⟨3⟩ mem)
    (UInt256.ofNat 18) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd4111 := rd4110.dup4 (by native_decide) (by evm_ov)
  have rd4112 := rd4111.dup4 (by native_decide) (by evm_ov)
  have hinner :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((twoWordHashMem (frobIWord I) ⟨3⟩ mem).readWithPadding 0 64))) =
        urnInner := by
    have hmem64 : 64 ≤ mem.size := by rw [hmemSize]; omega
    exact twoWordHashMem_solcMappingSlot_of_ge64 ⟨3⟩ (frobIWord I) hmem64
  have hrd4113 :
      ∃ k' C', RD vatBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨4113⟩
        [urnInner, ⟨3⟩, ⟨32⟩, ⟨0⟩, ⟨64⟩, tab, dtabWord, ⟨416⟩,
          ⟨192⟩, frobDartWord I, frobDinkWord I,
          UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩,
          frobVMaskedWord I, frobUMaskedWord I, frobIWord I, ⟨524⟩, sel]
        (twoWordHashMem (frobIWord I) ⟨3⟩ mem) (UInt256.ofNat 18)
        ByteArray.empty (cA, σ) k' C' := by
    exact ⟨_, _, by
      simpa using rd4112.keccak256 0 urnInner (UInt256.ofNat 18)
        (by native_decide) mem_cost hinner (by native_decide) (by evm_ov)⟩
  obtain ⟨k4113, C4113, rd4113⟩ := hrd4113
  have rd4113' :
      RD vatBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨4113⟩
        [urnInner, ⟨3⟩, ⟨32⟩, ⟨0⟩, ⟨64⟩, tab, dtabWord, ⟨416⟩,
          ⟨192⟩, frobDartWord I, frobDinkWord I,
          UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩,
          frobVMaskedWord I, frobUMaskedWord I, frobIWord I, ⟨524⟩, sel]
        (twoWordHashMem (frobIWord I) ⟨3⟩ mem) (UInt256.ofNat 18)
        ByteArray.empty (cA, σ) k4113 C4113 := rd4113
  have rd4114 := rd4113'.swap13 (by native_decide) (by evm_ov)
  have rd4115 := rd4114.swap1 (by native_decide) (by evm_ov)
  have rd4116 := rd4115.swap11 (by native_decide) (by evm_ov)
  have rd4117pre := rd4116.and (by native_decide) (by evm_ov)
  have hmaskU :
      UInt256.land
        (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩)
        (frobUMaskedWord I) =
        frobUMaskedWord I := by
    rw [u256_land_comm]
    rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by decide]
    exact frobUMaskedWord_clean I
  rw [hmaskU] at rd4117pre
  have rd4118 := rd4117pre.dup3 (by native_decide) (by evm_ov)
  have rd4119 := rd4118.mstore 0
    (wordAt0Mem (frobUMaskedWord I) (twoWordHashMem (frobIWord I) ⟨3⟩ mem))
    (UInt256.ofNat 18) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd4120 := rd4119.swap11 (by native_decide) (by evm_ov)
  have rd4121 := rd4120.dup12 (by native_decide) (by evm_ov)
  have rd4122 := rd4121.mstore 0 memUrn
    (UInt256.ofNat 18) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd4123 := rd4122.dup2 (by native_decide) (by evm_ov)
  have rd4124 := rd4123.dup2 (by native_decide) (by evm_ov)
  have hslot :
      UInt256.ofNat (fromByteArrayBigEndian (ffi.KEC (memUrn.readWithPadding 0 64))) =
        urnSlot := by
    have hmemInner : 64 ≤ (twoWordHashMem (frobIWord I) ⟨3⟩ mem).size := by
      rw [twoWordHashMem_size_of_ge64]
      · rw [hmemSize]; omega
      · rw [hmemSize]; omega
    simpa [memUrn, urnSlot, frobUrnInkSlot, frobUrnBase, urnInner] using
      twoWordHashMem_solcMappingSlot_of_ge64 urnInner (frobUMaskedWord I) hmemInner
  have rd4125 := rd4124.keccak256 0 urnSlot (UInt256.ofNat 18)
    (by native_decide) mem_cost hslot (by native_decide) (by evm_ov)
  have rd4126 := rd4125.dup7 (by native_decide) (by evm_ov)
  have hmload192 :
      (if (⟨192⟩ : UInt256).toNat ≥ memUrn.size
          ∨ (⟨192⟩ : UInt256) ≥ UInt256.ofNat 18 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (memUrn.readWithPadding (⟨192⟩ : UInt256).toNat 32))) =
        urnInkNew := by
    exact mloadWordValue_of_readWithPadding
      (by
        rw [show (⟨192⟩ : UInt256).toNat = 192 from by decide]
        dsimp [memUrn]
        rw [twoWordHashMem_size_of_ge64]
        · rw [twoWordHashMem_size_of_ge64]
          · rw [hmemSize]; omega
          · rw [hmemSize]; omega
        · rw [twoWordHashMem_size_of_ge64]
          · rw [hmemSize]; omega
          · rw [hmemSize]; omega)
      (by native_decide)
      (by
        rw [show (⟨192⟩ : UInt256).toNat = 192 from by decide]
        dsimp [memUrn]
        rw [twoWordHashMem_read32_above64 (readOff := 192)]
        · rw [twoWordHashMem_read32_above64 (readOff := 192)]
          · exact hread192
          · omega
          · rw [hmemSize]; omega
        · omega
        · rw [twoWordHashMem_size_of_ge64]
          · rw [hmemSize]; omega
          · rw [hmemSize]; omega)
  have rd4127 := rd4126.mload 0 urnInkNew (UInt256.ofNat 18)
    (by native_decide) mem_cost hmload192 (by native_decide) (by evm_ov)
  have rd4128 := rd4127.dup2 (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd4129raw⟩ := rd4128.sstore hperm (by native_decide) (by evm_ov)
  exact ⟨_, _, by
    simpa [memUrn, urnSlot, frobUrnInkSlot, frobUrnBase] using rd4129raw⟩

theorem RD.vatFrobFinalUrnArtStoreSuccess
    {cA gh bl σInit σ σ₀ A I} {g : Sat256} {k C : ℕ}
    {sel tab dtabWord urnArtNew : UInt256} {mem : ByteArray}
    (h : RD vatBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨4129⟩
      [frobUrnInkSlot I, ⟨0⟩, ⟨64⟩, tab, dtabWord, ⟨416⟩, ⟨192⟩,
        frobDartWord I, frobDinkWord I, ⟨3⟩, frobVMaskedWord I, ⟨32⟩,
        frobIWord I, ⟨524⟩, sel]
      mem (UInt256.ofNat 18) ByteArray.empty (cA, σ) k C)
    (hmemSize : mem.size = 576)
    (hread224 : mem.readWithPadding 224 32 = UInt256.toByteArray urnArtNew)
    (hperm : I.perm = true) :
    ∃ k' C',
      RD vatBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨4139⟩
        [⟨0⟩, ⟨64⟩, tab, dtabWord, ⟨416⟩, ⟨1⟩,
          frobDartWord I, frobDinkWord I, ⟨3⟩, frobVMaskedWord I, ⟨32⟩,
          frobIWord I, ⟨524⟩, sel]
        mem (UInt256.ofNat 18) ByteArray.empty
        (cA, sstoreAccountMap I.codeOwner σ (frobUrnArtSlot I) urnArtNew) k' C' := by
  have rd4130 := h.swap6 (by native_decide) (by evm_ov)
  have rd4131 := rd4130.dup12 (by native_decide) (by evm_ov)
  have rd4132pre := rd4131.add (by native_decide) (by evm_ov)
  have hoff :
      (⟨32⟩ : UInt256) + (⟨192⟩ : UInt256) = ⟨224⟩ := by native_decide
  rw [hoff] at rd4132pre
  have hmload224 :
      (if (⟨224⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨224⟩ : UInt256) ≥ UInt256.ofNat 18 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (mem.readWithPadding (⟨224⟩ : UInt256).toNat 32))) =
        urnArtNew := by
    exact mloadWordValue_of_readWithPadding
      (by
        rw [show (⟨224⟩ : UInt256).toNat = 224 from by decide]
        rw [hmemSize]
        omega)
      (by native_decide)
      (by
        rw [show (⟨224⟩ : UInt256).toNat = 224 from by decide]
        exact hread224)
  have rd4133 := rd4132pre.mload 0 urnArtNew (UInt256.ofNat 18)
    (by native_decide) mem_cost hmload224 (by native_decide) (by evm_ov)
  have rd4135 := rd4133.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  have rd4136 := rd4135.swap7 (by native_decide) (by evm_ov)
  have rd4137 := rd4136.dup8 (by native_decide) (by evm_ov)
  have rd4138pre := rd4137.add (by native_decide) (by evm_ov)
  have hslot :
      (⟨1⟩ : UInt256) + frobUrnInkSlot I = frobUrnArtSlot I := by
    rw [u256_add_comm]
    rfl
  rw [hslot] at rd4138pre
  obtain ⟨_, _, rd4139raw⟩ := rd4138pre.sstore hperm (by native_decide) (by evm_ov)
  exact ⟨_, _, by
    simpa using rd4139raw⟩

theorem RD.vatFrobFinalIlkArtStoreSuccess
    {cA gh bl σInit σ σ₀ A I} {g : Sat256} {k C : ℕ}
    {sel tab dtabWord ilkArtNew : UInt256} {mem : ByteArray}
    (h : RD vatBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨4139⟩
      [⟨0⟩, ⟨64⟩, tab, dtabWord, ⟨416⟩, ⟨1⟩,
        frobDartWord I, frobDinkWord I, ⟨3⟩, frobVMaskedWord I, ⟨32⟩,
        frobIWord I, ⟨524⟩, sel]
      mem (UInt256.ofNat 18) ByteArray.empty (cA, σ) k C)
    (hmemSize : mem.size = 576)
    (hread416 : mem.readWithPadding 416 32 = UInt256.toByteArray ilkArtNew)
    (hperm : I.perm = true) :
    ∃ k' C',
      RD vatBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨4155⟩
        [frobIlkArtSlot I, ⟨64⟩, tab, dtabWord, ⟨416⟩, ⟨1⟩,
          frobDartWord I, frobDinkWord I, ⟨3⟩, frobVMaskedWord I, ⟨32⟩,
          ⟨2⟩, ⟨524⟩, sel]
        (twoWordHashMem (frobIWord I) ⟨2⟩ mem)
        (UInt256.ofNat 18) ByteArray.empty
        (cA, sstoreAccountMap I.codeOwner σ (frobIlkArtSlot I) ilkArtNew) k' C' := by
  let ilkSlot := frobIlkArtSlot I
  let memIlk := twoWordHashMem (frobIWord I) ⟨2⟩ mem
  have rd4140 := h.swap11 (by native_decide) (by evm_ov)
  have rd4141 := rd4140.dup12 (by native_decide) (by evm_ov)
  have rd4142 := rd4141.mstore 0 (wordAt0Mem (frobIWord I) mem)
    (UInt256.ofNat 18) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd4144 := rd4142.push1 ⟨2⟩ (by native_decide) (by evm_ov)
  have rd4145 := rd4144.dup1 (by native_decide) (by evm_ov)
  have rd4146 := rd4145.dup12 (by native_decide) (by evm_ov)
  have rd4147 := rd4146.mstore 0 memIlk
    (UInt256.ofNat 18) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd4148 := rd4147.swap11 (by native_decide) (by evm_ov)
  have rd4149 := rd4148.dup2 (by native_decide) (by evm_ov)
  have rd4150 := rd4149.swap1 (by native_decide) (by evm_ov)
  have hilkSlot :
      UInt256.ofNat (fromByteArrayBigEndian (ffi.KEC (memIlk.readWithPadding 0 64))) =
        ilkSlot := by
    have hmem64 : 64 ≤ mem.size := by rw [hmemSize]; omega
    simpa [memIlk, ilkSlot, frobIlkArtSlot, frobIlkBase] using
      twoWordHashMem_solcMappingSlot_of_ge64 ⟨2⟩ (frobIWord I) hmem64
  have rd4151 := rd4150.keccak256 0 ilkSlot (UInt256.ofNat 18)
    (by native_decide) mem_cost hilkSlot (by native_decide) (by evm_ov)
  have rd4152 := rd4151.dup5 (by native_decide) (by evm_ov)
  have hmload416 :
      (if (⟨416⟩ : UInt256).toNat ≥ memIlk.size
          ∨ (⟨416⟩ : UInt256) ≥ UInt256.ofNat 18 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (memIlk.readWithPadding (⟨416⟩ : UInt256).toNat 32))) =
        ilkArtNew := by
    exact mloadWordValue_of_readWithPadding
      (by
        rw [show (⟨416⟩ : UInt256).toNat = 416 from by decide]
        dsimp [memIlk]
        rw [twoWordHashMem_size_of_ge64]
        · rw [hmemSize]; omega
        · rw [hmemSize]; omega)
      (by native_decide)
      (by
        rw [show (⟨416⟩ : UInt256).toNat = 416 from by decide]
        dsimp [memIlk]
        rw [twoWordHashMem_read32_above64 (readOff := 416)]
        · exact hread416
        · omega
        · rw [hmemSize]; omega)
  have rd4153 := rd4152.mload 0 ilkArtNew (UInt256.ofNat 18)
    (by native_decide) mem_cost hmload416 (by native_decide) (by evm_ov)
  have rd4154 := rd4153.dup2 (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd4155raw⟩ := rd4154.sstore hperm (by native_decide) (by evm_ov)
  exact ⟨_, _, by
    simpa [memIlk, ilkSlot, frobIlkArtSlot, frobIlkBase] using rd4155raw⟩

theorem RD.vatFrobFinalIlkTailReturnSuccess
    {cA gh bl σInit σ σ₀ A I} {g : Sat256} {k C : ℕ}
    {sel tab dtabWord rate spot line dust : UInt256} {mem : ByteArray}
    (h : RD vatBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨4155⟩
      [frobIlkArtSlot I, ⟨64⟩, tab, dtabWord, ⟨416⟩, ⟨1⟩,
        frobDartWord I, frobDinkWord I, ⟨3⟩, frobVMaskedWord I, ⟨32⟩,
        ⟨2⟩, ⟨524⟩, sel]
      mem (UInt256.ofNat 18) ByteArray.empty (cA, σ) k C)
    (hmemSize : mem.size = 576)
    (hread448 : mem.readWithPadding 448 32 = UInt256.toByteArray rate)
    (hread480 : mem.readWithPadding 480 32 = UInt256.toByteArray spot)
    (hread512 : mem.readWithPadding 512 32 = UInt256.toByteArray line)
    (hread544 : mem.readWithPadding 544 32 = UInt256.toByteArray dust)
    (hperm : I.perm = true) :
    RDret vatBytecode g (initState cA gh bl σInit σ₀ g A I)
      (cA,
        sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner
            (sstoreAccountMap I.codeOwner
              (sstoreAccountMap I.codeOwner σ (frobIlkRateSlot I) rate)
              (frobIlkSpotSlot I) spot)
            (frobIlkLineSlot I) line)
          (frobIlkDustSlot I) dust)
      ByteArray.empty := by
  let σRate := sstoreAccountMap I.codeOwner σ (frobIlkRateSlot I) rate
  let σSpot := sstoreAccountMap I.codeOwner σRate (frobIlkSpotSlot I) spot
  let σLine := sstoreAccountMap I.codeOwner σSpot (frobIlkLineSlot I) line
  let σDust := sstoreAccountMap I.codeOwner σLine (frobIlkDustSlot I) dust
  have rd4156 := h.swap10 (by native_decide) (by evm_ov)
  have rd4157 := rd4156.dup5 (by native_decide) (by evm_ov)
  have rd4158pre := rd4157.add (by native_decide) (by evm_ov)
  have hoff448 : (⟨416⟩ : UInt256) + ⟨64⟩ = ⟨480⟩ := by native_decide
  have hoffRate : (⟨416⟩ : UInt256) + ⟨32⟩ = ⟨448⟩ := by native_decide
  rw [hoffRate] at rd4158pre
  have hmload448 :
      (if (⟨448⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨448⟩ : UInt256) ≥ UInt256.ofNat 18 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (mem.readWithPadding (⟨448⟩ : UInt256).toNat 32))) =
        rate := by
    exact mloadWordValue_of_readWithPadding
      (by
        rw [show (⟨448⟩ : UInt256).toNat = 448 from by decide]
        rw [hmemSize]
        omega)
      (by native_decide)
      (by
        rw [show (⟨448⟩ : UInt256).toNat = 448 from by decide]
        exact hread448)
  have rd4159 := rd4158pre.mload 0 rate (UInt256.ofNat 18)
    (by native_decide) mem_cost hmload448 (by native_decide) (by evm_ov)
  have rd4160 := rd4159.swap5 (by native_decide) (by evm_ov)
  have rd4161 := rd4160.dup11 (by native_decide) (by evm_ov)
  have rd4162pre := rd4161.add (by native_decide) (by evm_ov)
  have hslotRate :
      frobIlkArtSlot I + (⟨1⟩ : UInt256) = frobIlkRateSlot I := by
    rfl
  rw [hslotRate] at rd4162pre
  have rd4163 := rd4162pre.swap5 (by native_decide) (by evm_ov)
  have rd4164 := rd4163.swap1 (by native_decide) (by evm_ov)
  have rd4165pre := rd4164.swap5 (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd4165raw⟩ := rd4165pre.sstore hperm (by native_decide) (by evm_ov)
  have hrd4165 :
      ∃ k' C', RD vatBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨4166⟩
        [tab, dtabWord, ⟨416⟩, ⟨64⟩, frobDartWord I, frobDinkWord I, ⟨3⟩,
          frobVMaskedWord I, frobIlkArtSlot I, ⟨2⟩, ⟨524⟩, sel]
        mem (UInt256.ofNat 18) ByteArray.empty (cA, σRate) k' C' := by
    exact ⟨_, _, by simpa [σRate] using rd4165raw⟩
  obtain ⟨_, _, rd4165⟩ := hrd4165
  have rd4166 := rd4165.pop (by native_decide) (by evm_ov)
  have rd4167 := rd4166.pop (by native_decide) (by evm_ov)
  have rd4168 := rd4167.swap1 (by native_decide) (by evm_ov)
  have rd4169 := rd4168.dup2 (by native_decide) (by evm_ov)
  have rd4170pre := rd4169.add (by native_decide) (by evm_ov)
  rw [hoff448] at rd4170pre
  have hmload480 :
      (if (⟨480⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨480⟩ : UInt256) ≥ UInt256.ofNat 18 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (mem.readWithPadding (⟨480⟩ : UInt256).toNat 32))) =
        spot := by
    exact mloadWordValue_of_readWithPadding
      (by
        rw [show (⟨480⟩ : UInt256).toNat = 480 from by decide]
        rw [hmemSize]
        omega)
      (by native_decide)
      (by
        rw [show (⟨480⟩ : UInt256).toNat = 480 from by decide]
        exact hread480)
  have rd4171 := rd4170pre.mload 0 spot (UInt256.ofNat 18)
    (by native_decide) mem_cost hmload480 (by native_decide) (by evm_ov)
  have rd4172 := rd4171.swap7 (by native_decide) (by evm_ov)
  have rd4173 := rd4172.dup7 (by native_decide) (by evm_ov)
  have rd4174pre := rd4173.add (by native_decide) (by evm_ov)
  have hslotSpot :
      frobIlkArtSlot I + (⟨2⟩ : UInt256) = frobIlkSpotSlot I := by
    rfl
  rw [hslotSpot] at rd4174pre
  have rd4175 := rd4174pre.swap7 (by native_decide) (by evm_ov)
  have rd4176 := rd4175.swap1 (by native_decide) (by evm_ov)
  have rd4177 := rd4176.swap7 (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd4178raw⟩ := rd4177.sstore hperm (by native_decide) (by evm_ov)
  have hrd4178 :
      ∃ k' C', RD vatBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨4179⟩
        [frobDartWord I, frobDinkWord I, ⟨3⟩, frobVMaskedWord I, frobIlkArtSlot I,
          ⟨416⟩, ⟨524⟩, sel]
        mem (UInt256.ofNat 18) ByteArray.empty (cA, σSpot) k' C' := by
    exact ⟨_, _, by simpa [σRate, σSpot] using rd4178raw⟩
  obtain ⟨_, _, rd4178⟩ := hrd4178
  have rd4179 := rd4178.pop (by native_decide) (by evm_ov)
  have rd4180 := rd4179.pop (by native_decide) (by evm_ov)
  have rd4183 := rd4180.push1 ⟨96⟩ (by native_decide) (by evm_ov)
  have rd4184 := rd4183.dup5 (by native_decide) (by evm_ov)
  have rd4185pre := rd4184.add (by native_decide) (by evm_ov)
  have hoff512 : (⟨416⟩ : UInt256) + ⟨96⟩ = ⟨512⟩ := by native_decide
  rw [hoff512] at rd4185pre
  have hmload512 :
      (if (⟨512⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨512⟩ : UInt256) ≥ UInt256.ofNat 18 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (mem.readWithPadding (⟨512⟩ : UInt256).toNat 32))) =
        line := by
    exact mloadWordValue_of_readWithPadding
      (by
        rw [show (⟨512⟩ : UInt256).toNat = 512 from by decide]
        rw [hmemSize]
        omega)
      (by native_decide)
      (by
        rw [show (⟨512⟩ : UInt256).toNat = 512 from by decide]
        exact hread512)
  have rd4186 := rd4185pre.mload 0 line (UInt256.ofNat 18)
    (by native_decide) mem_cost hmload512 (by native_decide) (by evm_ov)
  have rd4187 := rd4186.swap1 (by native_decide) (by evm_ov)
  have rd4188 := rd4187.dup4 (by native_decide) (by evm_ov)
  have rd4189pre := rd4188.add (by native_decide) (by evm_ov)
  have hslotLine :
      frobIlkArtSlot I + (⟨3⟩ : UInt256) = frobIlkLineSlot I := by
    rfl
  rw [hslotLine] at rd4189pre
  obtain ⟨_, _, rd4189raw⟩ := rd4189pre.sstore hperm (by native_decide) (by evm_ov)
  have hrd4189 :
      ∃ k' C', RD vatBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨4190⟩
        [frobVMaskedWord I, frobIlkArtSlot I, ⟨416⟩, ⟨524⟩, sel]
        mem (UInt256.ofNat 18) ByteArray.empty (cA, σLine) k' C' := by
    exact ⟨_, _, by simpa [σRate, σSpot, σLine] using rd4189raw⟩
  obtain ⟨_, _, rd4189⟩ := hrd4189
  have rd4190 := rd4189.pop (by native_decide) (by evm_ov)
  have rd4193 := rd4190.push1 ⟨128⟩ (by native_decide) (by evm_ov)
  have rd4194 := rd4193.swap1 (by native_decide) (by evm_ov)
  have rd4195 := rd4194.swap2 (by native_decide) (by evm_ov)
  have rd4196pre := rd4195.add (by native_decide) (by evm_ov)
  have hoff544 : (⟨416⟩ : UInt256) + ⟨128⟩ = ⟨544⟩ := by native_decide
  rw [hoff544] at rd4196pre
  have hmload544 :
      (if (⟨544⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨544⟩ : UInt256) ≥ UInt256.ofNat 18 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (mem.readWithPadding (⟨544⟩ : UInt256).toNat 32))) =
        dust := by
    exact mloadWordValue_of_readWithPadding
      (by
        rw [show (⟨544⟩ : UInt256).toNat = 544 from by decide]
        rw [hmemSize]
        omega)
      (by native_decide)
      (by
        rw [show (⟨544⟩ : UInt256).toNat = 544 from by decide]
        exact hread544)
  have rd4197 := rd4196pre.mload 0 dust (UInt256.ofNat 18)
    (by native_decide) mem_cost hmload544 (by native_decide) (by evm_ov)
  have rd4199 := rd4197.push1 ⟨4⟩ (by native_decide) (by evm_ov)
  have rd4200 := rd4199.swap1 (by native_decide) (by evm_ov)
  have rd4201 := rd4200.swap2 (by native_decide) (by evm_ov)
  have rd4202pre := rd4201.add (by native_decide) (by evm_ov)
  have hslotDust :
      frobIlkArtSlot I + (⟨4⟩ : UInt256) = frobIlkDustSlot I := by
    rfl
  rw [hslotDust] at rd4202pre
  obtain ⟨_, _, rd4202raw⟩ := rd4202pre.sstore hperm (by native_decide) (by evm_ov)
  have hrd4202 :
      ∃ k' C', RD vatBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨4203⟩
        [⟨524⟩, sel]
        mem (UInt256.ofNat 18) ByteArray.empty (cA, σDust) k' C' := by
    exact ⟨_, _, by simpa [σRate, σSpot, σLine, σDust] using rd4202raw⟩
  obtain ⟨_, _, rd4202⟩ := hrd4202
  have rd524 := rd4202.jump (by native_decide) (by jump_dest) (by evm_ov)
  have rd525 := rd524.jumpdest (by native_decide) (by evm_ov)
  simpa [σRate, σSpot, σLine, σDust] using RD.stop rd525 (by native_decide) (by simp)

set_option maxHeartbeats 2000000 in
theorem RD.vatFrobStoreSuccess
    {cA gh bl σInit σ σ₀ A I} {g : Sat256} {k C : ℕ} {sel : UInt256}
    (h :
      let memBase :=
        frobIlkArtUpdatedMem σ I (frobUrnInkNew σ I) (frobUrnArtNew σ I)
          (frobIlkArtNew σ I)
      let memU :=
        twoWordHashMem (hopeSourceWord I) (solcMappingSlot ⟨1⟩ (frobUMaskedWord I))
          (twoWordHashMem (frobUMaskedWord I) ⟨1⟩ memBase)
      let memV :=
        twoWordHashMem (hopeSourceWord I) (solcMappingSlot ⟨1⟩ (frobVMaskedWord I))
          (twoWordHashMem (frobVMaskedWord I) ⟨1⟩ memU)
      let memDust :=
        twoWordHashMem (hopeSourceWord I) (solcMappingSlot ⟨1⟩ (frobWMaskedWord I))
          (twoWordHashMem (frobWMaskedWord I) ⟨1⟩ memV)
      RD vatBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨3963⟩
        [frobTabWord σ I, frobDtabWord σ I, ⟨416⟩, ⟨192⟩,
          frobDartWord I, frobDinkWord I, frobWMaskedWord I, frobVMaskedWord I,
          frobUMaskedWord I, frobIWord I, ⟨524⟩, sel]
        memDust (UInt256.ofNat 18) ByteArray.empty (cA, frobAfterDebt σ I) k C)
    (hperm : I.perm = true)
    (hGemPos :
      UInt256.sgt (frobDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.gt (frobGemNew σ I)
          (solcSlotWord (frobAfterDebt σ I) I (frobGemVSlot I)) = ⟨0⟩)
    (hGemNeg :
      UInt256.slt (frobDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.lt (frobGemNew σ I)
          (solcSlotWord (frobAfterDebt σ I) I (frobGemVSlot I)) = ⟨0⟩)
    (hDaiNeg :
      UInt256.slt (frobDtabWord σ I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.gt (frobDaiNew σ I)
          (solcSlotWord (frobAfterGem σ I) I (frobDaiWSlot I)) = ⟨0⟩)
    (hDaiPos :
      UInt256.sgt (frobDtabWord σ I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.lt (frobDaiNew σ I)
          (solcSlotWord (frobAfterGem σ I) I (frobDaiWSlot I)) = ⟨0⟩) :
    RDret vatBytecode g (initState cA gh bl σInit σ₀ g A I)
      (cA, frobAfterRuntimeFinal σ I) ByteArray.empty := by
  let urnInkNew := frobUrnInkNew σ I
  let urnArtNew := frobUrnArtNew σ I
  let ilkArtNew := frobIlkArtNew σ I
  let dtabWord := frobDtabWord σ I
  let tabWord := frobTabWord σ I
  let gemNew := frobGemNew σ I
  let daiNew := frobDaiNew σ I
  let memBase := frobIlkArtUpdatedMem σ I urnInkNew urnArtNew ilkArtNew
  let memU0 := twoWordHashMem (frobUMaskedWord I) ⟨1⟩ memBase
  let memU :=
    twoWordHashMem (hopeSourceWord I) (solcMappingSlot ⟨1⟩ (frobUMaskedWord I))
      memU0
  let memV0 := twoWordHashMem (frobVMaskedWord I) ⟨1⟩ memU
  let memV :=
    twoWordHashMem (hopeSourceWord I) (solcMappingSlot ⟨1⟩ (frobVMaskedWord I))
      memV0
  let memW0 := twoWordHashMem (frobWMaskedWord I) ⟨1⟩ memV
  let memDust :=
    twoWordHashMem (hopeSourceWord I) (solcMappingSlot ⟨1⟩ (frobWMaskedWord I))
      memW0
  let memGem0 := twoWordHashMem (frobIWord I) ⟨4⟩ memDust
  let memGem :=
    twoWordHashMem (frobVMaskedWord I) (solcMappingSlot ⟨4⟩ (frobIWord I))
      memGem0
  let memDai0 := twoWordHashMem (frobIWord I) ⟨4⟩ memGem
  let memDai1 :=
    twoWordHashMem (frobVMaskedWord I) (solcMappingSlot ⟨4⟩ (frobIWord I))
      memDai0
  let memDai :=
    twoWordHashMem (frobWMaskedWord I) ⟨5⟩ memDai1
  let memDaiStored :=
    twoWordHashMem (frobWMaskedWord I) ⟨5⟩ memDai
  let memUrn0 := twoWordHashMem (frobIWord I) ⟨3⟩ memDaiStored
  let memUrnInk :=
    twoWordHashMem (frobUMaskedWord I)
      (solcMappingSlot (⟨3⟩ : UInt256) (frobIWord I))
      memUrn0
  let memIlk :=
    twoWordHashMem (frobIWord I) ⟨2⟩ memUrnInk
  have h0 :
      RD vatBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨3963⟩
        [tabWord, dtabWord, ⟨416⟩, ⟨192⟩, frobDartWord I, frobDinkWord I,
          frobWMaskedWord I, frobVMaskedWord I, frobUMaskedWord I, frobIWord I,
          ⟨524⟩, sel]
        memDust (UInt256.ofNat 18) ByteArray.empty (cA, frobAfterDebt σ I) k C := by
    simpa [memDust, memW0, memV, memV0, memU, memU0, memBase, tabWord, dtabWord,
      urnInkNew, urnArtNew, ilkArtNew] using h
  have hmemBase : memBase.size = 576 := by
    simpa [memBase, urnInkNew, urnArtNew, ilkArtNew] using
      frobIlkArtUpdatedMem_size σ I urnInkNew urnArtNew ilkArtNew
  have hmemU0 : memU0.size = 576 := by
    dsimp [memU0]
    exact twoWordHashMem_size_576 (frobUMaskedWord I) ⟨1⟩ hmemBase
  have hmemU : memU.size = 576 := by
    dsimp [memU]
    exact twoWordHashMem_size_576 (hopeSourceWord I)
      (solcMappingSlot ⟨1⟩ (frobUMaskedWord I)) hmemU0
  have hmemV0 : memV0.size = 576 := by
    dsimp [memV0]
    exact twoWordHashMem_size_576 (frobVMaskedWord I) ⟨1⟩ hmemU
  have hmemV : memV.size = 576 := by
    dsimp [memV]
    exact twoWordHashMem_size_576 (hopeSourceWord I)
      (solcMappingSlot ⟨1⟩ (frobVMaskedWord I)) hmemV0
  have hmemW0 : memW0.size = 576 := by
    dsimp [memW0]
    exact twoWordHashMem_size_576 (frobWMaskedWord I) ⟨1⟩ hmemV
  have hmemDust : memDust.size = 576 := by
    dsimp [memDust]
    exact twoWordHashMem_size_576 (hopeSourceWord I)
      (solcMappingSlot ⟨1⟩ (frobWMaskedWord I)) hmemW0
  obtain ⟨_, _, hGem⟩ := RD.vatFrobGemSubSuccess
    (h := by simpa [tabWord, dtabWord, memDust] using h0)
    (by rw [hmemDust]; omega)
    (by simpa [gemNew] using hGemPos)
    (by simpa [gemNew] using hGemNeg)
  have hmemGem0 : memGem0.size = 576 := by
    dsimp [memGem0]
    exact twoWordHashMem_size_576 (frobIWord I) ⟨4⟩ hmemDust
  have hmemGem : memGem.size = 576 := by
    dsimp [memGem]
    exact twoWordHashMem_size_576 (frobVMaskedWord I)
      (solcMappingSlot ⟨4⟩ (frobIWord I)) hmemGem0
  obtain ⟨_, _, hDaiAdd⟩ := RD.vatFrobGemStoreDaiAddSuccess
    (h := by simpa [memGem, gemNew, dtabWord, tabWord] using hGem)
    (by rw [hmemGem]; omega) hperm
    (by simpa [daiNew, dtabWord, gemNew, frobAfterGem] using hDaiNeg)
    (by simpa [daiNew, dtabWord, gemNew, frobAfterGem] using hDaiPos)
  have hmemDai0 : memDai0.size = 576 := by
    dsimp [memDai0]
    exact twoWordHashMem_size_576 (frobIWord I) ⟨4⟩ hmemGem
  have hmemDai1 : memDai1.size = 576 := by
    dsimp [memDai1]
    exact twoWordHashMem_size_576 (frobVMaskedWord I)
      (solcMappingSlot ⟨4⟩ (frobIWord I)) hmemDai0
  have hmemDai : memDai.size = 576 := by
    dsimp [memDai]
    exact twoWordHashMem_size_576 (frobWMaskedWord I) ⟨5⟩ hmemDai1
  obtain ⟨_, _, hDaiStore⟩ := RD.vatFrobDaiStoreSuccess
    (h := by simpa [memDai, daiNew, dtabWord, tabWord, frobAfterGem] using hDaiAdd)
    (by rw [hmemDai]; omega) hperm
  have hmemDaiStored : memDaiStored.size = 576 := by
    dsimp [memDaiStored]
    exact twoWordHashMem_size_576 (frobWMaskedWord I) ⟨5⟩ hmemDai
  have preserveRead {m : ByteArray} (key slot : UInt256) {off : Nat} {word : UInt256}
      (habove : 64 ≤ off) (hin : off + 32 ≤ 576) (hsize : m.size = 576)
      (hread : m.readWithPadding off 32 = UInt256.toByteArray word) :
      (twoWordHashMem key slot m).readWithPadding off 32 = UInt256.toByteArray word :=
    twoWordHashMem_read32_above64_of_size576 key slot habove hin hsize hread
  have readMemDaiStored {off : Nat} {word : UInt256}
      (habove : 64 ≤ off) (hin : off + 32 ≤ 576)
      (hreadBase : memBase.readWithPadding off 32 = UInt256.toByteArray word) :
      memDaiStored.readWithPadding off 32 = UInt256.toByteArray word := by
    have rU0 : memU0.readWithPadding off 32 = UInt256.toByteArray word := by
      simpa [memU0] using
        preserveRead (frobUMaskedWord I) ⟨1⟩ habove hin hmemBase hreadBase
    have rU : memU.readWithPadding off 32 = UInt256.toByteArray word := by
      simpa [memU] using
        preserveRead (hopeSourceWord I) (solcMappingSlot ⟨1⟩ (frobUMaskedWord I))
          habove hin hmemU0 rU0
    have rV0 : memV0.readWithPadding off 32 = UInt256.toByteArray word := by
      simpa [memV0] using
        preserveRead (frobVMaskedWord I) ⟨1⟩ habove hin hmemU rU
    have rV : memV.readWithPadding off 32 = UInt256.toByteArray word := by
      simpa [memV] using
        preserveRead (hopeSourceWord I) (solcMappingSlot ⟨1⟩ (frobVMaskedWord I))
          habove hin hmemV0 rV0
    have rW0 : memW0.readWithPadding off 32 = UInt256.toByteArray word := by
      simpa [memW0] using
        preserveRead (frobWMaskedWord I) ⟨1⟩ habove hin hmemV rV
    have rDust : memDust.readWithPadding off 32 = UInt256.toByteArray word := by
      simpa [memDust] using
        preserveRead (hopeSourceWord I) (solcMappingSlot ⟨1⟩ (frobWMaskedWord I))
          habove hin hmemW0 rW0
    have rGem0 : memGem0.readWithPadding off 32 = UInt256.toByteArray word := by
      simpa [memGem0] using
        preserveRead (frobIWord I) ⟨4⟩ habove hin hmemDust rDust
    have rGem : memGem.readWithPadding off 32 = UInt256.toByteArray word := by
      simpa [memGem] using
        preserveRead (frobVMaskedWord I) (solcMappingSlot ⟨4⟩ (frobIWord I))
          habove hin hmemGem0 rGem0
    have rDai0 : memDai0.readWithPadding off 32 = UInt256.toByteArray word := by
      simpa [memDai0] using
        preserveRead (frobIWord I) ⟨4⟩ habove hin hmemGem rGem
    have rDai1 : memDai1.readWithPadding off 32 = UInt256.toByteArray word := by
      simpa [memDai1] using
        preserveRead (frobVMaskedWord I) (solcMappingSlot ⟨4⟩ (frobIWord I))
          habove hin hmemDai0 rDai0
    have rDai : memDai.readWithPadding off 32 = UInt256.toByteArray word := by
      simpa [memDai] using
        preserveRead (frobWMaskedWord I) ⟨5⟩ habove hin hmemDai1 rDai1
    simpa [memDaiStored] using
      preserveRead (frobWMaskedWord I) ⟨5⟩ habove hin hmemDai rDai
  have hread192 :
      memDaiStored.readWithPadding 192 32 = UInt256.toByteArray urnInkNew := by
    exact readMemDaiStored (by omega) (by native_decide)
      (by
        simpa [memBase] using
          frobIlkArtUpdatedMem_read192 σ I urnInkNew urnArtNew ilkArtNew)
  obtain ⟨_, _, hUrnInk⟩ := RD.vatFrobFinalUrnInkStoreSuccess
    (h := by simpa [memDaiStored, dtabWord, tabWord, frobAfterDai, daiNew,
      frobAfterGem] using hDaiStore)
    hmemDaiStored hread192 hperm
  have hmemUrn0 : memUrn0.size = 576 := by
    dsimp [memUrn0]
    exact twoWordHashMem_size_576 (frobIWord I) ⟨3⟩ hmemDaiStored
  have hmemUrnInk : memUrnInk.size = 576 := by
    dsimp [memUrnInk]
    exact twoWordHashMem_size_576 (frobUMaskedWord I)
      (solcMappingSlot (⟨3⟩ : UInt256) (frobIWord I)) hmemUrn0
  have readMemUrnInk {off : Nat} {word : UInt256}
      (habove : 64 ≤ off) (hin : off + 32 ≤ 576)
      (hreadBase : memBase.readWithPadding off 32 = UInt256.toByteArray word) :
      memUrnInk.readWithPadding off 32 = UInt256.toByteArray word := by
    have rDaiStored := readMemDaiStored habove hin hreadBase
    have rUrn0 : memUrn0.readWithPadding off 32 = UInt256.toByteArray word := by
      simpa [memUrn0] using
        preserveRead (frobIWord I) ⟨3⟩ habove hin hmemDaiStored rDaiStored
    simpa [memUrnInk] using
      preserveRead (frobUMaskedWord I)
        (solcMappingSlot (⟨3⟩ : UInt256) (frobIWord I)) habove hin hmemUrn0 rUrn0
  have hread224 :
      memUrnInk.readWithPadding 224 32 = UInt256.toByteArray urnArtNew := by
    exact readMemUrnInk (by omega) (by native_decide)
      (by
        simpa [memBase] using
          frobIlkArtUpdatedMem_read224 σ I urnInkNew urnArtNew ilkArtNew)
  obtain ⟨_, _, hUrnArt⟩ := RD.vatFrobFinalUrnArtStoreSuccess
    (h := by simpa [memUrnInk, dtabWord, tabWord, urnInkNew, frobAfterDai,
      frobAfterSourceFinal] using hUrnInk)
    hmemUrnInk hread224 hperm
  have hread416 :
      memUrnInk.readWithPadding 416 32 = UInt256.toByteArray ilkArtNew := by
    exact readMemUrnInk (by omega) (by native_decide)
      (by
        simpa [memBase] using
          frobIlkArtUpdatedMem_read416 σ I urnInkNew urnArtNew ilkArtNew)
  obtain ⟨_, _, hIlkArt⟩ := RD.vatFrobFinalIlkArtStoreSuccess
    (h := by simpa [memUrnInk, dtabWord, tabWord, urnInkNew, urnArtNew,
      frobAfterSourceFinal] using hUrnArt)
    hmemUrnInk hread416 hperm
  have hmemIlk : memIlk.size = 576 := by
    dsimp [memIlk]
    exact twoWordHashMem_size_576 (frobIWord I) ⟨2⟩ hmemUrnInk
  have readMemIlk {off : Nat} {word : UInt256}
      (habove : 64 ≤ off) (hin : off + 32 ≤ 576)
      (hreadBase : memBase.readWithPadding off 32 = UInt256.toByteArray word) :
      memIlk.readWithPadding off 32 = UInt256.toByteArray word := by
    have rUrnInk := readMemUrnInk habove hin hreadBase
    simpa [memIlk] using
      preserveRead (frobIWord I) ⟨2⟩ habove hin hmemUrnInk rUrnInk
  have hread448 :
      memIlk.readWithPadding 448 32 =
        UInt256.toByteArray (solcSlotWord σ I (frobIlkRateSlot I)) := by
    exact readMemIlk (by omega) (by native_decide)
      (by
        simpa [memBase] using
          frobIlkArtUpdatedMem_read448 σ I urnInkNew urnArtNew ilkArtNew)
  have hread480 :
      memIlk.readWithPadding 480 32 =
        UInt256.toByteArray (solcSlotWord σ I (frobIlkSpotSlot I)) := by
    exact readMemIlk (by omega) (by native_decide)
      (by
        simpa [memBase] using
          frobIlkArtUpdatedMem_read480 σ I urnInkNew urnArtNew ilkArtNew)
  have hread512 :
      memIlk.readWithPadding 512 32 =
        UInt256.toByteArray (solcSlotWord σ I (frobIlkLineSlot I)) := by
    exact readMemIlk (by omega) (by native_decide)
      (by
        simpa [memBase] using
          frobIlkArtUpdatedMem_read512 σ I urnInkNew urnArtNew ilkArtNew)
  have hread544 :
      memIlk.readWithPadding 544 32 =
        UInt256.toByteArray (solcSlotWord σ I (frobIlkDustSlot I)) := by
    exact readMemIlk (by omega) (by native_decide)
      (by
        simpa [memBase] using
          frobIlkArtUpdatedMem_read544 σ I urnInkNew urnArtNew ilkArtNew)
  simpa [memIlk, dtabWord, tabWord, urnInkNew, urnArtNew, ilkArtNew,
    frobAfterRuntimeFinal, frobAfterSourceFinal, frobAfterDai, frobAfterGem,
    frobAfterDebt, gemNew, daiNew] using
    RD.vatFrobFinalIlkTailReturnSuccess
      (h := by simpa [memIlk, dtabWord, tabWord, frobAfterSourceFinal] using hIlkArt)
      hmemIlk hread448 hread480 hread512 hread544 hperm

theorem frobStorageType_urn_ink (I : ExecutionEnv) :
    storageTypeAt? contract.storage (frobUrnInkEvaledRef I) =
      some (.elem (.int uint256Int)) := by
  simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, UrnStructTy, uint256St]

theorem frobStorageType_urn_art (I : ExecutionEnv) :
    storageTypeAt? contract.storage (frobUrnArtEvaledRef I) =
      some (.elem (.int uint256Int)) := by
  simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, UrnStructTy, uint256St]

theorem frobStorageType_ilk_art (I : ExecutionEnv) :
    storageTypeAt? contract.storage (frobIlkFieldEvaledRef I "Art") =
      some (.elem (.int uint256Int)) := by
  simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, IlkStructTy, uint256St]

theorem frobStorageType_ilk_rate (I : ExecutionEnv) :
    storageTypeAt? contract.storage (frobIlkFieldEvaledRef I "rate") =
      some (.elem (.int uint256Int)) := by
  simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, IlkStructTy, uint256St]

theorem frobStorageType_ilk_spot (I : ExecutionEnv) :
    storageTypeAt? contract.storage (frobIlkFieldEvaledRef I "spot") =
      some (.elem (.int uint256Int)) := by
  simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, IlkStructTy, uint256St]

theorem frobStorageType_ilk_line (I : ExecutionEnv) :
    storageTypeAt? contract.storage (frobIlkFieldEvaledRef I "line") =
      some (.elem (.int uint256Int)) := by
  simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, IlkStructTy, uint256St]

theorem frobStorageType_ilk_dust (I : ExecutionEnv) :
    storageTypeAt? contract.storage (frobIlkFieldEvaledRef I "dust") =
      some (.elem (.int uint256Int)) := by
  simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, IlkStructTy, uint256St]

theorem frobStorageType_can (usr : KeyValue) (I : ExecutionEnv) :
    storageTypeAt? contract.storage (frobWishEvaledRef usr I) =
      some (.elem (.int uint256Int)) := by
  simp [frobWishEvaledRef, storageTypeAt?, storageTypeStep?, contract, storageDecls,
    uint256St]

theorem frobStorageType_gem_v (I : ExecutionEnv) :
    storageTypeAt? contract.storage (frobGemVEvaledRef I) =
      some (.elem (.int uint256Int)) := by
  simp [frobGemVEvaledRef, storageTypeAt?, storageTypeStep?, contract, storageDecls,
    uint256St]

theorem frobStorageType_dai_w (I : ExecutionEnv) :
    storageTypeAt? contract.storage (frobDaiWEvaledRef I) =
      some (.elem (.int uint256Int)) := by
  simp [frobDaiWEvaledRef, storageTypeAt?, storageTypeStep?, contract, storageDecls,
    uint256St]

theorem frobStorageLayout_urn_ink_source (I : ExecutionEnv) :
    config.storage.layout (frobUrnInkEvaledRef I) =
      fun _ => some (wordLoc (frobUrnInkSourceSlot I)) := by
  funext evm
  change storageLayoutRaw (frobUrnInkEvaledRef I) evm =
    some (wordLoc (frobUrnInkSourceSlot I))
  simp [storageLayoutRaw, frobUrnInkEvaledRef, frobUrnInkSourceSlot, frobUrnSourceBase]

theorem frobStorageLayout_urn_art_source (I : ExecutionEnv) :
    config.storage.layout (frobUrnArtEvaledRef I) =
      fun _ => some (wordLoc (frobUrnArtSourceSlot I)) := by
  funext evm
  change storageLayoutRaw (frobUrnArtEvaledRef I) evm =
    some (wordLoc (frobUrnArtSourceSlot I))
  simp [storageLayoutRaw, frobUrnArtEvaledRef, frobUrnArtSourceSlot, frobUrnSourceBase]

theorem frobStorageLayout_ilk_art_source (I : ExecutionEnv) :
    config.storage.layout (frobIlkFieldEvaledRef I "Art") =
      fun _ => some (wordLoc (frobIlkArtSourceSlot I)) := by
  funext evm
  change storageLayoutRaw (frobIlkFieldEvaledRef I "Art") evm =
    some (wordLoc (frobIlkArtSourceSlot I))
  simp [storageLayoutRaw, frobIlkFieldEvaledRef, frobIlkArtSourceSlot, frobIlkSourceBase]

theorem frobStorageLayout_ilk_rate_source (I : ExecutionEnv) :
    config.storage.layout (frobIlkFieldEvaledRef I "rate") =
      fun _ => some (wordLoc (frobIlkRateSourceSlot I)) := by
  funext evm
  change storageLayoutRaw (frobIlkFieldEvaledRef I "rate") evm =
    some (wordLoc (frobIlkRateSourceSlot I))
  simp [storageLayoutRaw, frobIlkFieldEvaledRef, frobIlkRateSourceSlot, frobIlkSourceBase]

theorem frobStorageLayout_ilk_spot_source (I : ExecutionEnv) :
    config.storage.layout (frobIlkFieldEvaledRef I "spot") =
      fun _ => some (wordLoc (frobIlkSpotSourceSlot I)) := by
  funext evm
  change storageLayoutRaw (frobIlkFieldEvaledRef I "spot") evm =
    some (wordLoc (frobIlkSpotSourceSlot I))
  simp [storageLayoutRaw, frobIlkFieldEvaledRef, frobIlkSpotSourceSlot, frobIlkSourceBase]

theorem frobStorageLayout_ilk_line_source (I : ExecutionEnv) :
    config.storage.layout (frobIlkFieldEvaledRef I "line") =
      fun _ => some (wordLoc (frobIlkLineSourceSlot I)) := by
  funext evm
  change storageLayoutRaw (frobIlkFieldEvaledRef I "line") evm =
    some (wordLoc (frobIlkLineSourceSlot I))
  simp [storageLayoutRaw, frobIlkFieldEvaledRef, frobIlkLineSourceSlot, frobIlkSourceBase]

theorem frobStorageLayout_ilk_dust_source (I : ExecutionEnv) :
    config.storage.layout (frobIlkFieldEvaledRef I "dust") =
      fun _ => some (wordLoc (frobIlkDustSourceSlot I)) := by
  funext evm
  change storageLayoutRaw (frobIlkFieldEvaledRef I "dust") evm =
    some (wordLoc (frobIlkDustSourceSlot I))
  simp [storageLayoutRaw, frobIlkFieldEvaledRef, frobIlkDustSourceSlot, frobIlkSourceBase]

theorem frobStorageLayout_can (usr : KeyValue) (I : ExecutionEnv) :
    config.storage.layout (frobWishEvaledRef usr I) =
      fun _ => some (wordLoc (canSlot usr (frobSourceKey I))) := by
  funext evm
  change storageLayoutRaw (frobWishEvaledRef usr I) evm =
    some (wordLoc (canSlot usr (frobSourceKey I)))
  simp [storageLayoutRaw, frobWishEvaledRef, canSlot]

theorem frobStorageLayout_gem_v_source (I : ExecutionEnv) :
    config.storage.layout (frobGemVEvaledRef I) =
      fun _ => some (wordLoc (frobGemVSourceSlot I)) := by
  funext evm
  change storageLayoutRaw (frobGemVEvaledRef I) evm =
    some (wordLoc (frobGemVSourceSlot I))
  simp [storageLayoutRaw, frobGemVEvaledRef, frobGemVSourceSlot]

theorem frobStorageLayout_dai_w_source (I : ExecutionEnv) :
    config.storage.layout (frobDaiWEvaledRef I) =
      fun _ => some (wordLoc (frobDaiWSourceSlot I)) := by
  funext evm
  change storageLayoutRaw (frobDaiWEvaledRef I) evm =
    some (wordLoc (frobDaiWSourceSlot I))
  simp [storageLayoutRaw, frobDaiWEvaledRef, frobDaiWSourceSlot]

set_option linter.unusedSimpArgs false in
theorem evalStorageRef_frob_urn_ink_locals (evm : EVM.State) (I : ExecutionEnv)
    (locals : Store) (hsz196 : 196 ≤ I.calldata.size)
    (hi : locals.get? "i" = some (frobIValue I))
    (hu : locals.get? "u" = some (frobUValue I)) :
    evalStorageRef config { contract := contract, locals := locals } evm
      (urnsF (.var "i") (.var "u") "ink") = .ok (frobUrnInkEvaledRef I) := by
  simp [frobUrnInkEvaledRef, frobIValue, frobUValue, frobIKey, frobUKey,
    urnsF, evalStorageRef, evalStorageRefSteps, evalStorageRefStep, evalExpr?,
    valueToKey?, EvalResult.ofOption, EvalResult.bind, bind, pure,
    ← Std.HashMap.get?_eq_getElem?, hi, hu, frobIBytes_len I hsz196]

set_option linter.unusedSimpArgs false in
theorem evalStorageRef_frob_urn_art_locals (evm : EVM.State) (I : ExecutionEnv)
    (locals : Store) (hsz196 : 196 ≤ I.calldata.size)
    (hi : locals.get? "i" = some (frobIValue I))
    (hu : locals.get? "u" = some (frobUValue I)) :
    evalStorageRef config { contract := contract, locals := locals } evm
      (urnsF (.var "i") (.var "u") "art") = .ok (frobUrnArtEvaledRef I) := by
  simp [frobUrnArtEvaledRef, frobIValue, frobUValue, frobIKey, frobUKey,
    urnsF, evalStorageRef, evalStorageRefSteps, evalStorageRefStep, evalExpr?,
    valueToKey?, EvalResult.ofOption, EvalResult.bind, bind, pure,
    ← Std.HashMap.get?_eq_getElem?, hi, hu, frobIBytes_len I hsz196]

set_option linter.unusedSimpArgs false in
theorem evalStorageRef_frob_ilk_art_locals (evm : EVM.State) (I : ExecutionEnv)
    (locals : Store) (hsz196 : 196 ≤ I.calldata.size)
    (hi : locals.get? "i" = some (frobIValue I)) :
    evalStorageRef config { contract := contract, locals := locals } evm
      (ilksF (.var "i") "Art") = .ok (frobIlkFieldEvaledRef I "Art") := by
  simp [frobIlkFieldEvaledRef, frobIValue, frobIKey, ilksF, evalStorageRef,
    evalStorageRefSteps, evalStorageRefStep, evalExpr?, valueToKey?,
    EvalResult.ofOption, EvalResult.bind, bind, pure, ← Std.HashMap.get?_eq_getElem?,
    hi, frobIBytes_len I hsz196]

set_option linter.unusedSimpArgs false in
theorem evalStorageRef_frob_ilk_rate_locals (evm : EVM.State) (I : ExecutionEnv)
    (locals : Store) (hsz196 : 196 ≤ I.calldata.size)
    (hi : locals.get? "i" = some (frobIValue I)) :
    evalStorageRef config { contract := contract, locals := locals } evm
      (ilksF (.var "i") "rate") = .ok (frobIlkFieldEvaledRef I "rate") := by
  simp [frobIlkFieldEvaledRef, frobIValue, frobIKey, ilksF, evalStorageRef,
    evalStorageRefSteps, evalStorageRefStep, evalExpr?, valueToKey?,
    EvalResult.ofOption, EvalResult.bind, bind, pure, ← Std.HashMap.get?_eq_getElem?,
    hi, frobIBytes_len I hsz196]

set_option linter.unusedSimpArgs false in
theorem evalStorageRef_frob_ilk_spot_locals (evm : EVM.State) (I : ExecutionEnv)
    (locals : Store) (hsz196 : 196 ≤ I.calldata.size)
    (hi : locals.get? "i" = some (frobIValue I)) :
    evalStorageRef config { contract := contract, locals := locals } evm
      (ilksF (.var "i") "spot") = .ok (frobIlkFieldEvaledRef I "spot") := by
  simp [frobIlkFieldEvaledRef, frobIValue, frobIKey, ilksF, evalStorageRef,
    evalStorageRefSteps, evalStorageRefStep, evalExpr?, valueToKey?,
    EvalResult.ofOption, EvalResult.bind, bind, pure, ← Std.HashMap.get?_eq_getElem?,
    hi, frobIBytes_len I hsz196]

set_option linter.unusedSimpArgs false in
theorem evalStorageRef_frob_ilk_line_locals (evm : EVM.State) (I : ExecutionEnv)
    (locals : Store) (hsz196 : 196 ≤ I.calldata.size)
    (hi : locals.get? "i" = some (frobIValue I)) :
    evalStorageRef config { contract := contract, locals := locals } evm
      (ilksF (.var "i") "line") = .ok (frobIlkFieldEvaledRef I "line") := by
  simp [frobIlkFieldEvaledRef, frobIValue, frobIKey, ilksF, evalStorageRef,
    evalStorageRefSteps, evalStorageRefStep, evalExpr?, valueToKey?,
    EvalResult.ofOption, EvalResult.bind, bind, pure, ← Std.HashMap.get?_eq_getElem?,
    hi, frobIBytes_len I hsz196]

set_option linter.unusedSimpArgs false in
theorem evalStorageRef_frob_ilk_dust_locals (evm : EVM.State) (I : ExecutionEnv)
    (locals : Store) (hsz196 : 196 ≤ I.calldata.size)
    (hi : locals.get? "i" = some (frobIValue I)) :
    evalStorageRef config { contract := contract, locals := locals } evm
      (ilksF (.var "i") "dust") = .ok (frobIlkFieldEvaledRef I "dust") := by
  simp [frobIlkFieldEvaledRef, frobIValue, frobIKey, ilksF, evalStorageRef,
    evalStorageRefSteps, evalStorageRefStep, evalExpr?, valueToKey?,
    EvalResult.ofOption, EvalResult.bind, bind, pure, ← Std.HashMap.get?_eq_getElem?,
    hi, frobIBytes_len I hsz196]

set_option linter.unusedSimpArgs false in
theorem evalStorageRef_frob_can_u_locals (evm : EVM.State) (I : ExecutionEnv)
    (locals : Store)
    (hsrc : evm.executionEnv.source = I.source)
    (hu : locals.get? "u" = some (frobUValue I)) :
    evalStorageRef config { contract := contract, locals := locals } evm
      (canRef (.var "u") sender) = .ok (frobWishEvaledRef (frobUKey I) I) := by
  simp [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, canRef, sender,
    envValue, frobWishEvaledRef, frobUValue, frobUKey, frobSourceKey, hsrc,
    valueToKey?, EvalResult.bind, EvalResult.ofOption, bind, pure, evalExpr?,
    ← Std.HashMap.get?_eq_getElem?, hu]

set_option linter.unusedSimpArgs false in
theorem evalStorageRef_frob_can_v_locals (evm : EVM.State) (I : ExecutionEnv)
    (locals : Store)
    (hsrc : evm.executionEnv.source = I.source)
    (hv : locals.get? "v" = some (frobVValue I)) :
    evalStorageRef config { contract := contract, locals := locals } evm
      (canRef (.var "v") sender) = .ok (frobWishEvaledRef (frobVKey I) I) := by
  simp [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, canRef, sender,
    envValue, frobWishEvaledRef, frobVValue, frobVKey, frobSourceKey, hsrc,
    valueToKey?, EvalResult.bind, EvalResult.ofOption, bind, pure, evalExpr?,
    ← Std.HashMap.get?_eq_getElem?, hv]

set_option linter.unusedSimpArgs false in
theorem evalStorageRef_frob_can_w_locals (evm : EVM.State) (I : ExecutionEnv)
    (locals : Store)
    (hsrc : evm.executionEnv.source = I.source)
    (hw : locals.get? "w" = some (frobWValue I)) :
    evalStorageRef config { contract := contract, locals := locals } evm
      (canRef (.var "w") sender) = .ok (frobWishEvaledRef (frobWKey I) I) := by
  simp [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, canRef, sender,
    envValue, frobWishEvaledRef, frobWValue, frobWKey, frobSourceKey, hsrc,
    valueToKey?, EvalResult.bind, EvalResult.ofOption, bind, pure, evalExpr?,
    ← Std.HashMap.get?_eq_getElem?, hw]

set_option linter.unusedSimpArgs false in
theorem evalStorageRef_frob_gem_v_locals (evm : EVM.State) (I : ExecutionEnv)
    (locals : Store) (hsz196 : 196 ≤ I.calldata.size)
    (hi : locals.get? "i" = some (frobIValue I))
    (hv : locals.get? "v" = some (frobVValue I)) :
    evalStorageRef config { contract := contract, locals := locals } evm
      (gemRef (.var "i") (.var "v")) = .ok (frobGemVEvaledRef I) := by
  simp [frobGemVEvaledRef, frobIValue, frobVValue, frobIKey, frobVKey, gemRef,
    evalStorageRef, evalStorageRefSteps, evalStorageRefStep, evalExpr?,
    valueToKey?, EvalResult.ofOption, EvalResult.bind, bind, pure,
    ← Std.HashMap.get?_eq_getElem?, hi, hv, frobIBytes_len I hsz196]

set_option linter.unusedSimpArgs false in
theorem evalStorageRef_frob_dai_w_locals (evm : EVM.State) (I : ExecutionEnv)
    (locals : Store)
    (hw : locals.get? "w" = some (frobWValue I)) :
    evalStorageRef config { contract := contract, locals := locals } evm
      (daiRef (.var "w")) = .ok (frobDaiWEvaledRef I) := by
  simp [frobDaiWEvaledRef, frobWValue, frobWKey, daiRef, evalStorageRef,
    evalStorageRefSteps, evalStorageRefStep, evalExpr?, valueToKey?,
    EvalResult.ofOption, EvalResult.bind, bind, pure,
    ← Std.HashMap.get?_eq_getElem?, hw]

theorem evalExpr_frob_urn_ink_locals {evm : EVM.State} {I : ExecutionEnv}
    (locals : Store) (hsz196 : 196 ≤ I.calldata.size)
    (hi : locals.get? "i" = some (frobIValue I))
    (hu : locals.get? "u" = some (frobUValue I))
    (hbase : locals.get? "urns" = none) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.storage (urnsF (.var "i") (.var "u") "ink")) =
      .ok (.int (Int.ofNat
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
          (frobUrnInkSourceSlot I)).toNat)) := by
  exact evalExpr_storage_scalar_value
    (hbase := hbase)
    (her := evalStorageRef_frob_urn_ink_locals evm I locals hsz196 hi hu)
    (hty := frobStorageType_urn_ink I)
    (hloc := frobStorageLayout_urn_ink_source I)
    (hload := vatStorageLocLoad_uint256 evm (frobUrnInkSourceSlot I))

theorem evalExpr_frob_urn_art_locals {evm : EVM.State} {I : ExecutionEnv}
    (locals : Store) (hsz196 : 196 ≤ I.calldata.size)
    (hi : locals.get? "i" = some (frobIValue I))
    (hu : locals.get? "u" = some (frobUValue I))
    (hbase : locals.get? "urns" = none) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.storage (urnsF (.var "i") (.var "u") "art")) =
      .ok (.int (Int.ofNat
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
          (frobUrnArtSourceSlot I)).toNat)) := by
  exact evalExpr_storage_scalar_value
    (hbase := hbase)
    (her := evalStorageRef_frob_urn_art_locals evm I locals hsz196 hi hu)
    (hty := frobStorageType_urn_art I)
    (hloc := frobStorageLayout_urn_art_source I)
    (hload := vatStorageLocLoad_uint256 evm (frobUrnArtSourceSlot I))

theorem evalExpr_frob_ilk_art_locals {evm : EVM.State} {I : ExecutionEnv}
    (locals : Store) (hsz196 : 196 ≤ I.calldata.size)
    (hi : locals.get? "i" = some (frobIValue I))
    (hbase : locals.get? "ilks" = none) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.storage (ilksF (.var "i") "Art")) =
      .ok (.int (Int.ofNat
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
          (frobIlkArtSourceSlot I)).toNat)) := by
  exact evalExpr_storage_scalar_value
    (hbase := hbase)
    (her := evalStorageRef_frob_ilk_art_locals evm I locals hsz196 hi)
    (hty := frobStorageType_ilk_art I)
    (hloc := frobStorageLayout_ilk_art_source I)
    (hload := vatStorageLocLoad_uint256 evm (frobIlkArtSourceSlot I))

theorem evalExpr_frob_ilk_rate_locals {evm : EVM.State} {I : ExecutionEnv}
    (locals : Store) (hsz196 : 196 ≤ I.calldata.size)
    (hi : locals.get? "i" = some (frobIValue I))
    (hbase : locals.get? "ilks" = none) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.storage (ilksF (.var "i") "rate")) =
      .ok (.int (Int.ofNat
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
          (frobIlkRateSourceSlot I)).toNat)) := by
  exact evalExpr_storage_scalar_value
    (hbase := hbase)
    (her := evalStorageRef_frob_ilk_rate_locals evm I locals hsz196 hi)
    (hty := frobStorageType_ilk_rate I)
    (hloc := frobStorageLayout_ilk_rate_source I)
    (hload := vatStorageLocLoad_uint256 evm (frobIlkRateSourceSlot I))

theorem evalExpr_frob_ilk_spot_locals {evm : EVM.State} {I : ExecutionEnv}
    (locals : Store) (hsz196 : 196 ≤ I.calldata.size)
    (hi : locals.get? "i" = some (frobIValue I))
    (hbase : locals.get? "ilks" = none) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.storage (ilksF (.var "i") "spot")) =
      .ok (.int (Int.ofNat
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
          (frobIlkSpotSourceSlot I)).toNat)) := by
  exact evalExpr_storage_scalar_value
    (hbase := hbase)
    (her := evalStorageRef_frob_ilk_spot_locals evm I locals hsz196 hi)
    (hty := frobStorageType_ilk_spot I)
    (hloc := frobStorageLayout_ilk_spot_source I)
    (hload := vatStorageLocLoad_uint256 evm (frobIlkSpotSourceSlot I))

theorem evalExpr_frob_ilk_line_locals {evm : EVM.State} {I : ExecutionEnv}
    (locals : Store) (hsz196 : 196 ≤ I.calldata.size)
    (hi : locals.get? "i" = some (frobIValue I))
    (hbase : locals.get? "ilks" = none) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.storage (ilksF (.var "i") "line")) =
      .ok (.int (Int.ofNat
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
          (frobIlkLineSourceSlot I)).toNat)) := by
  exact evalExpr_storage_scalar_value
    (hbase := hbase)
    (her := evalStorageRef_frob_ilk_line_locals evm I locals hsz196 hi)
    (hty := frobStorageType_ilk_line I)
    (hloc := frobStorageLayout_ilk_line_source I)
    (hload := vatStorageLocLoad_uint256 evm (frobIlkLineSourceSlot I))

theorem evalExpr_frob_ilk_dust_locals {evm : EVM.State} {I : ExecutionEnv}
    (locals : Store) (hsz196 : 196 ≤ I.calldata.size)
    (hi : locals.get? "i" = some (frobIValue I))
    (hbase : locals.get? "ilks" = none) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.storage (ilksF (.var "i") "dust")) =
      .ok (.int (Int.ofNat
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
          (frobIlkDustSourceSlot I)).toNat)) := by
  exact evalExpr_storage_scalar_value
    (hbase := hbase)
    (her := evalStorageRef_frob_ilk_dust_locals evm I locals hsz196 hi)
    (hty := frobStorageType_ilk_dust I)
    (hloc := frobStorageLayout_ilk_dust_source I)
    (hload := vatStorageLocLoad_uint256 evm (frobIlkDustSourceSlot I))

theorem evalExpr_frob_can_u_locals {evm : EVM.State} {I : ExecutionEnv}
    (locals : Store)
    (hsrc : evm.executionEnv.source = I.source)
    (hu : locals.get? "u" = some (frobUValue I))
    (hbase : locals.get? "can" = none) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.storage (canRef (.var "u") sender)) =
      .ok (.int (Int.ofNat
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
          (frobUWishSlot I)).toNat)) := by
  have h := evalExpr_storage_scalar_value
    (hbase := hbase)
    (her := evalStorageRef_frob_can_u_locals evm I locals hsrc hu)
    (hty := frobStorageType_can (frobUKey I) I)
    (hloc := frobStorageLayout_can (frobUKey I) I)
    (hload := vatStorageLocLoad_uint256 evm (canSlot (frobUKey I) (frobSourceKey I)))
  simpa [frobUWishSourceSlot_eq I] using h

theorem evalExpr_frob_can_v_locals {evm : EVM.State} {I : ExecutionEnv}
    (locals : Store)
    (hsrc : evm.executionEnv.source = I.source)
    (hv : locals.get? "v" = some (frobVValue I))
    (hbase : locals.get? "can" = none) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.storage (canRef (.var "v") sender)) =
      .ok (.int (Int.ofNat
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
          (frobVWishSlot I)).toNat)) := by
  have h := evalExpr_storage_scalar_value
    (hbase := hbase)
    (her := evalStorageRef_frob_can_v_locals evm I locals hsrc hv)
    (hty := frobStorageType_can (frobVKey I) I)
    (hloc := frobStorageLayout_can (frobVKey I) I)
    (hload := vatStorageLocLoad_uint256 evm (canSlot (frobVKey I) (frobSourceKey I)))
  simpa [frobVWishSourceSlot_eq I] using h

theorem evalExpr_frob_can_w_locals {evm : EVM.State} {I : ExecutionEnv}
    (locals : Store)
    (hsrc : evm.executionEnv.source = I.source)
    (hw : locals.get? "w" = some (frobWValue I))
    (hbase : locals.get? "can" = none) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.storage (canRef (.var "w") sender)) =
      .ok (.int (Int.ofNat
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
          (frobWWishSlot I)).toNat)) := by
  have h := evalExpr_storage_scalar_value
    (hbase := hbase)
    (her := evalStorageRef_frob_can_w_locals evm I locals hsrc hw)
    (hty := frobStorageType_can (frobWKey I) I)
    (hloc := frobStorageLayout_can (frobWKey I) I)
    (hload := vatStorageLocLoad_uint256 evm (canSlot (frobWKey I) (frobSourceKey I)))
  simpa [frobWWishSourceSlot_eq I] using h

theorem evalExpr_frob_can_u_eq_true {evm : EVM.State} {I : ExecutionEnv}
    (locals : Store)
    (hsrc : evm.executionEnv.source = I.source)
    (hu : locals.get? "u" = some (frobUValue I))
    (hbase : locals.get? "can" = none)
    (hcan : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (frobUWishSlot I) = ⟨1⟩) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.binary .eq (.storage (canRef (.var "u") sender)) (.intLit 1)) =
      .ok (.bool true) := by
  simp [evalExpr?, EvalResult.bind, bind, pure, evalBinaryOp?,
    evalExpr_frob_can_u_locals (evm := evm) (I := I) locals hsrc hu hbase,
    hcan, show (⟨1⟩ : UInt256).toNat = 1 by decide]

theorem evalExpr_frob_can_v_eq_true {evm : EVM.State} {I : ExecutionEnv}
    (locals : Store)
    (hsrc : evm.executionEnv.source = I.source)
    (hv : locals.get? "v" = some (frobVValue I))
    (hbase : locals.get? "can" = none)
    (hcan : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (frobVWishSlot I) = ⟨1⟩) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.binary .eq (.storage (canRef (.var "v") sender)) (.intLit 1)) =
      .ok (.bool true) := by
  simp [evalExpr?, EvalResult.bind, bind, pure, evalBinaryOp?,
    evalExpr_frob_can_v_locals (evm := evm) (I := I) locals hsrc hv hbase,
    hcan, show (⟨1⟩ : UInt256).toNat = 1 by decide]

theorem evalExpr_frob_can_w_eq_true {evm : EVM.State} {I : ExecutionEnv}
    (locals : Store)
    (hsrc : evm.executionEnv.source = I.source)
    (hw : locals.get? "w" = some (frobWValue I))
    (hbase : locals.get? "can" = none)
    (hcan : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (frobWWishSlot I) = ⟨1⟩) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.binary .eq (.storage (canRef (.var "w") sender)) (.intLit 1)) =
      .ok (.bool true) := by
  simp [evalExpr?, EvalResult.bind, bind, pure, evalBinaryOp?,
    evalExpr_frob_can_w_locals (evm := evm) (I := I) locals hsrc hw hbase,
    hcan, show (⟨1⟩ : UInt256).toNat = 1 by decide]

theorem evalExpr_frob_can_u_eq_false {evm : EVM.State} {I : ExecutionEnv}
    (locals : Store)
    (hsrc : evm.executionEnv.source = I.source)
    (hu : locals.get? "u" = some (frobUValue I))
    (hbase : locals.get? "can" = none)
    (hcan : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (frobUWishSlot I) ≠ ⟨1⟩) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.binary .eq (.storage (canRef (.var "u") sender)) (.intLit 1)) =
      .ok (.bool false) := by
  have hneNat :
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (frobUWishSlot I)).toNat ≠ 1 := by
    intro hnat
    apply hcan
    apply u256_inj
    rw [hnat]
    decide
  simp [evalExpr?, EvalResult.bind, bind, pure, evalBinaryOp?,
    evalExpr_frob_can_u_locals (evm := evm) (I := I) locals hsrc hu hbase, hneNat]

theorem evalExpr_frob_can_v_eq_false {evm : EVM.State} {I : ExecutionEnv}
    (locals : Store)
    (hsrc : evm.executionEnv.source = I.source)
    (hv : locals.get? "v" = some (frobVValue I))
    (hbase : locals.get? "can" = none)
    (hcan : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (frobVWishSlot I) ≠ ⟨1⟩) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.binary .eq (.storage (canRef (.var "v") sender)) (.intLit 1)) =
      .ok (.bool false) := by
  have hneNat :
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (frobVWishSlot I)).toNat ≠ 1 := by
    intro hnat
    apply hcan
    apply u256_inj
    rw [hnat]
    decide
  simp [evalExpr?, EvalResult.bind, bind, pure, evalBinaryOp?,
    evalExpr_frob_can_v_locals (evm := evm) (I := I) locals hsrc hv hbase, hneNat]

theorem evalExpr_frob_can_w_eq_false {evm : EVM.State} {I : ExecutionEnv}
    (locals : Store)
    (hsrc : evm.executionEnv.source = I.source)
    (hw : locals.get? "w" = some (frobWValue I))
    (hbase : locals.get? "can" = none)
    (hcan : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (frobWWishSlot I) ≠ ⟨1⟩) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.binary .eq (.storage (canRef (.var "w") sender)) (.intLit 1)) =
      .ok (.bool false) := by
  have hneNat :
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (frobWWishSlot I)).toNat ≠ 1 := by
    intro hnat
    apply hcan
    apply u256_inj
    rw [hnat]
    decide
  simp [evalExpr?, EvalResult.bind, bind, pure, evalBinaryOp?,
    evalExpr_frob_can_w_locals (evm := evm) (I := I) locals hsrc hw hbase, hneNat]

theorem evalExpr_frob_gem_v_locals {evm : EVM.State} {I : ExecutionEnv}
    (locals : Store) (hsz196 : 196 ≤ I.calldata.size)
    (hi : locals.get? "i" = some (frobIValue I))
    (hv : locals.get? "v" = some (frobVValue I))
    (hbase : locals.get? "gem" = none) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.storage (gemRef (.var "i") (.var "v"))) =
      .ok (.int (Int.ofNat
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
          (frobGemVSourceSlot I)).toNat)) := by
  exact evalExpr_storage_scalar_value
    (hbase := hbase)
    (her := evalStorageRef_frob_gem_v_locals evm I locals hsz196 hi hv)
    (hty := frobStorageType_gem_v I)
    (hloc := frobStorageLayout_gem_v_source I)
    (hload := vatStorageLocLoad_uint256 evm (frobGemVSourceSlot I))

theorem evalExpr_frob_dai_w_locals {evm : EVM.State} {I : ExecutionEnv}
    (locals : Store)
    (hw : locals.get? "w" = some (frobWValue I))
    (hbase : locals.get? "dai" = none) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.storage (daiRef (.var "w"))) =
      .ok (.int (Int.ofNat
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
          (frobDaiWSourceSlot I)).toNat)) := by
  exact evalExpr_storage_scalar_value
    (hbase := hbase)
    (her := evalStorageRef_frob_dai_w_locals evm I locals hw)
    (hty := frobStorageType_dai_w I)
    (hloc := frobStorageLayout_dai_w_source I)
    (hload := vatStorageLocLoad_uint256 evm (frobDaiWSourceSlot I))

theorem evalExpr_frob_u_sender_eq_true {evm : EVM.State} {I : ExecutionEnv}
    (locals : Store)
    (hsrc : evm.executionEnv.source = I.source)
    (hu : locals.get? "u" = some (frobUValue I))
    (heq : frobUMaskedWord I = hopeSourceWord I) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.binary .eq (.var "u") sender) = .ok (.bool true) := by
  have hvalue : frobUValue I = .address evm.executionEnv.source := by
    rw [frobUValue, solcAddressValue_masked (frobUWord I)]
    change Value.address (AccountAddress.ofNat (frobUMaskedWord I).toNat) =
      Value.address evm.executionEnv.source
    rw [heq]
    rw [frobHopeSource_ofNat I, ← hsrc]
  simp only [evalExpr?, sender, envValue, EvalResult.bind, EvalResult.ofOption, bind, pure]
  rw [hu, hvalue]
  simp [evalBinaryOp?]

theorem evalExpr_frob_v_sender_eq_true {evm : EVM.State} {I : ExecutionEnv}
    (locals : Store)
    (hsrc : evm.executionEnv.source = I.source)
    (hv : locals.get? "v" = some (frobVValue I))
    (heq : frobVMaskedWord I = hopeSourceWord I) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.binary .eq (.var "v") sender) = .ok (.bool true) := by
  have hvalue : frobVValue I = .address evm.executionEnv.source := by
    rw [frobVValue, solcAddressValue_masked (frobVWord I)]
    change Value.address (AccountAddress.ofNat (frobVMaskedWord I).toNat) =
      Value.address evm.executionEnv.source
    rw [heq]
    rw [frobHopeSource_ofNat I, ← hsrc]
  simp only [evalExpr?, sender, envValue, EvalResult.bind, EvalResult.ofOption, bind, pure]
  rw [hv, hvalue]
  simp [evalBinaryOp?]

theorem evalExpr_frob_w_sender_eq_true {evm : EVM.State} {I : ExecutionEnv}
    (locals : Store)
    (hsrc : evm.executionEnv.source = I.source)
    (hw : locals.get? "w" = some (frobWValue I))
    (heq : frobWMaskedWord I = hopeSourceWord I) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.binary .eq (.var "w") sender) = .ok (.bool true) := by
  have hvalue : frobWValue I = .address evm.executionEnv.source := by
    rw [frobWValue, solcAddressValue_masked (frobWWord I)]
    change Value.address (AccountAddress.ofNat (frobWMaskedWord I).toNat) =
      Value.address evm.executionEnv.source
    rw [heq]
    rw [frobHopeSource_ofNat I, ← hsrc]
  simp only [evalExpr?, sender, envValue, EvalResult.bind, EvalResult.ofOption, bind, pure]
  rw [hw, hvalue]
  simp [evalBinaryOp?]

theorem evalExpr_frob_u_sender_eq_false {evm : EVM.State} {I : ExecutionEnv}
    (locals : Store)
    (hsrc : evm.executionEnv.source = I.source)
    (hu : locals.get? "u" = some (frobUValue I))
    (hne : frobUMaskedWord I ≠ hopeSourceWord I) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.binary .eq (.var "u") sender) = .ok (.bool false) := by
  have hneValue : frobUValue I ≠ .address evm.executionEnv.source := by
    intro hval
    have hmasked :
        Value.address (AccountAddress.ofNat (frobUMaskedWord I).toNat) =
        Value.address evm.executionEnv.source := by
      rw [← solcAddressValue_masked (frobUWord I), ← hval]
    have hword : frobUMaskedWord I = hopeSourceWord I := by
      apply u256_inj
      have haddrs :
          AccountAddress.ofNat (frobUMaskedWord I).toNat = evm.executionEnv.source := by
        injection hmasked with haddr
      have hnat := congrArg Fin.val haddrs
      unfold AccountAddress.ofNat at hnat
      change (frobUMaskedWord I).toNat % EVM.addressModulus =
        evm.executionEnv.source.val at hnat
      rw [Nat.mod_eq_of_lt (frobUMaskedWord_canonical I)] at hnat
      rw [hopeSourceWord_toNat, ← hsrc]
      exact hnat
    exact hne hword
  have hbeq : (frobUValue I == Value.address evm.executionEnv.source) = false := by
    rw [Bool.eq_false_iff]
    intro hb
    exact hneValue (beq_iff_eq.mp hb)
  simp only [evalExpr?, sender, envValue, EvalResult.bind, EvalResult.ofOption, bind, pure]
  rw [hu]
  simp [evalBinaryOp?, hbeq]

theorem evalExpr_frob_v_sender_eq_false {evm : EVM.State} {I : ExecutionEnv}
    (locals : Store)
    (hsrc : evm.executionEnv.source = I.source)
    (hv : locals.get? "v" = some (frobVValue I))
    (hne : frobVMaskedWord I ≠ hopeSourceWord I) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.binary .eq (.var "v") sender) = .ok (.bool false) := by
  have hneValue : frobVValue I ≠ .address evm.executionEnv.source := by
    intro hval
    have hmasked :
        Value.address (AccountAddress.ofNat (frobVMaskedWord I).toNat) =
        Value.address evm.executionEnv.source := by
      rw [← solcAddressValue_masked (frobVWord I), ← hval]
    have hword : frobVMaskedWord I = hopeSourceWord I := by
      apply u256_inj
      have haddrs :
          AccountAddress.ofNat (frobVMaskedWord I).toNat = evm.executionEnv.source := by
        injection hmasked with haddr
      have hnat := congrArg Fin.val haddrs
      unfold AccountAddress.ofNat at hnat
      change (frobVMaskedWord I).toNat % EVM.addressModulus =
        evm.executionEnv.source.val at hnat
      rw [Nat.mod_eq_of_lt (frobVMaskedWord_canonical I)] at hnat
      rw [hopeSourceWord_toNat, ← hsrc]
      exact hnat
    exact hne hword
  have hbeq : (frobVValue I == Value.address evm.executionEnv.source) = false := by
    rw [Bool.eq_false_iff]
    intro hb
    exact hneValue (beq_iff_eq.mp hb)
  simp only [evalExpr?, sender, envValue, EvalResult.bind, EvalResult.ofOption, bind, pure]
  rw [hv]
  simp [evalBinaryOp?, hbeq]

theorem evalExpr_frob_w_sender_eq_false {evm : EVM.State} {I : ExecutionEnv}
    (locals : Store)
    (hsrc : evm.executionEnv.source = I.source)
    (hw : locals.get? "w" = some (frobWValue I))
    (hne : frobWMaskedWord I ≠ hopeSourceWord I) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.binary .eq (.var "w") sender) = .ok (.bool false) := by
  have hneValue : frobWValue I ≠ .address evm.executionEnv.source := by
    intro hval
    have hmasked :
        Value.address (AccountAddress.ofNat (frobWMaskedWord I).toNat) =
        Value.address evm.executionEnv.source := by
      rw [← solcAddressValue_masked (frobWWord I), ← hval]
    have hword : frobWMaskedWord I = hopeSourceWord I := by
      apply u256_inj
      have haddrs :
          AccountAddress.ofNat (frobWMaskedWord I).toNat = evm.executionEnv.source := by
        injection hmasked with haddr
      have hnat := congrArg Fin.val haddrs
      unfold AccountAddress.ofNat at hnat
      change (frobWMaskedWord I).toNat % EVM.addressModulus =
        evm.executionEnv.source.val at hnat
      rw [Nat.mod_eq_of_lt (frobWMaskedWord_canonical I)] at hnat
      rw [hopeSourceWord_toNat, ← hsrc]
      exact hnat
    exact hne hword
  have hbeq : (frobWValue I == Value.address evm.executionEnv.source) = false := by
    rw [Bool.eq_false_iff]
    intro hb
    exact hneValue (beq_iff_eq.mp hb)
  simp only [evalExpr?, sender, envValue, EvalResult.bind, EvalResult.ofOption, bind, pure]
  rw [hw]
  simp [evalBinaryOp?, hbeq]

theorem evalExpr_frob_wish_u_true_src {evm : EVM.State} {I : ExecutionEnv}
    (locals : Store)
    (hsrc : evm.executionEnv.source = I.source)
    (hu : locals.get? "u" = some (frobUValue I))
    (heq : frobUMaskedWord I = hopeSourceWord I) :
    evalExpr? config { contract := contract, locals := locals } evm
      (wishExpr (.var "u") sender) = .ok (.bool true) := by
  exact vatEvalExpr_or_true_left
    (lhs := .binary .eq (.var "u") sender)
    (rhs := .binary .eq (.storage (canRef (.var "u") sender)) (.intLit 1))
    (evalExpr_frob_u_sender_eq_true (evm := evm) (I := I) locals hsrc hu heq)

theorem evalExpr_frob_wish_v_true_src {evm : EVM.State} {I : ExecutionEnv}
    (locals : Store)
    (hsrc : evm.executionEnv.source = I.source)
    (hv : locals.get? "v" = some (frobVValue I))
    (heq : frobVMaskedWord I = hopeSourceWord I) :
    evalExpr? config { contract := contract, locals := locals } evm
      (wishExpr (.var "v") sender) = .ok (.bool true) := by
  exact vatEvalExpr_or_true_left
    (lhs := .binary .eq (.var "v") sender)
    (rhs := .binary .eq (.storage (canRef (.var "v") sender)) (.intLit 1))
    (evalExpr_frob_v_sender_eq_true (evm := evm) (I := I) locals hsrc hv heq)

theorem evalExpr_frob_wish_w_true_src {evm : EVM.State} {I : ExecutionEnv}
    (locals : Store)
    (hsrc : evm.executionEnv.source = I.source)
    (hw : locals.get? "w" = some (frobWValue I))
    (heq : frobWMaskedWord I = hopeSourceWord I) :
    evalExpr? config { contract := contract, locals := locals } evm
      (wishExpr (.var "w") sender) = .ok (.bool true) := by
  exact vatEvalExpr_or_true_left
    (lhs := .binary .eq (.var "w") sender)
    (rhs := .binary .eq (.storage (canRef (.var "w") sender)) (.intLit 1))
    (evalExpr_frob_w_sender_eq_true (evm := evm) (I := I) locals hsrc hw heq)

theorem evalExpr_frob_wish_u_true_can {evm : EVM.State} {I : ExecutionEnv}
    (locals : Store)
    (hsrc : evm.executionEnv.source = I.source)
    (hu : locals.get? "u" = some (frobUValue I))
    (hbase : locals.get? "can" = none)
    (hne : frobUMaskedWord I ≠ hopeSourceWord I)
    (hcan : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (frobUWishSlot I) = ⟨1⟩) :
    evalExpr? config { contract := contract, locals := locals } evm
      (wishExpr (.var "u") sender) = .ok (.bool true) := by
  exact vatEvalExpr_or_false_right
    (lhs := .binary .eq (.var "u") sender)
    (rhs := .binary .eq (.storage (canRef (.var "u") sender)) (.intLit 1))
    (evalExpr_frob_u_sender_eq_false (evm := evm) (I := I) locals hsrc hu hne)
    (evalExpr_frob_can_u_eq_true (evm := evm) (I := I) locals hsrc hu hbase hcan)

theorem evalExpr_frob_wish_v_true_can {evm : EVM.State} {I : ExecutionEnv}
    (locals : Store)
    (hsrc : evm.executionEnv.source = I.source)
    (hv : locals.get? "v" = some (frobVValue I))
    (hbase : locals.get? "can" = none)
    (hne : frobVMaskedWord I ≠ hopeSourceWord I)
    (hcan : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (frobVWishSlot I) = ⟨1⟩) :
    evalExpr? config { contract := contract, locals := locals } evm
      (wishExpr (.var "v") sender) = .ok (.bool true) := by
  exact vatEvalExpr_or_false_right
    (lhs := .binary .eq (.var "v") sender)
    (rhs := .binary .eq (.storage (canRef (.var "v") sender)) (.intLit 1))
    (evalExpr_frob_v_sender_eq_false (evm := evm) (I := I) locals hsrc hv hne)
    (evalExpr_frob_can_v_eq_true (evm := evm) (I := I) locals hsrc hv hbase hcan)

theorem evalExpr_frob_wish_w_true_can {evm : EVM.State} {I : ExecutionEnv}
    (locals : Store)
    (hsrc : evm.executionEnv.source = I.source)
    (hw : locals.get? "w" = some (frobWValue I))
    (hbase : locals.get? "can" = none)
    (hne : frobWMaskedWord I ≠ hopeSourceWord I)
    (hcan : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (frobWWishSlot I) = ⟨1⟩) :
    evalExpr? config { contract := contract, locals := locals } evm
      (wishExpr (.var "w") sender) = .ok (.bool true) := by
  exact vatEvalExpr_or_false_right
    (lhs := .binary .eq (.var "w") sender)
    (rhs := .binary .eq (.storage (canRef (.var "w") sender)) (.intLit 1))
    (evalExpr_frob_w_sender_eq_false (evm := evm) (I := I) locals hsrc hw hne)
    (evalExpr_frob_can_w_eq_true (evm := evm) (I := I) locals hsrc hw hbase hcan)

theorem evalExpr_frob_wish_u_false {evm : EVM.State} {I : ExecutionEnv}
    (locals : Store)
    (hsrc : evm.executionEnv.source = I.source)
    (hu : locals.get? "u" = some (frobUValue I))
    (hbase : locals.get? "can" = none)
    (hne : frobUMaskedWord I ≠ hopeSourceWord I)
    (hcan : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (frobUWishSlot I) ≠ ⟨1⟩) :
    evalExpr? config { contract := contract, locals := locals } evm
      (wishExpr (.var "u") sender) = .ok (.bool false) := by
  exact vatEvalExpr_or_false_right
    (lhs := .binary .eq (.var "u") sender)
    (rhs := .binary .eq (.storage (canRef (.var "u") sender)) (.intLit 1))
    (evalExpr_frob_u_sender_eq_false (evm := evm) (I := I) locals hsrc hu hne)
    (evalExpr_frob_can_u_eq_false (evm := evm) (I := I) locals hsrc hu hbase hcan)

theorem evalExpr_frob_wish_v_false {evm : EVM.State} {I : ExecutionEnv}
    (locals : Store)
    (hsrc : evm.executionEnv.source = I.source)
    (hv : locals.get? "v" = some (frobVValue I))
    (hbase : locals.get? "can" = none)
    (hne : frobVMaskedWord I ≠ hopeSourceWord I)
    (hcan : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (frobVWishSlot I) ≠ ⟨1⟩) :
    evalExpr? config { contract := contract, locals := locals } evm
      (wishExpr (.var "v") sender) = .ok (.bool false) := by
  exact vatEvalExpr_or_false_right
    (lhs := .binary .eq (.var "v") sender)
    (rhs := .binary .eq (.storage (canRef (.var "v") sender)) (.intLit 1))
    (evalExpr_frob_v_sender_eq_false (evm := evm) (I := I) locals hsrc hv hne)
    (evalExpr_frob_can_v_eq_false (evm := evm) (I := I) locals hsrc hv hbase hcan)

theorem evalExpr_frob_wish_w_false {evm : EVM.State} {I : ExecutionEnv}
    (locals : Store)
    (hsrc : evm.executionEnv.source = I.source)
    (hw : locals.get? "w" = some (frobWValue I))
    (hbase : locals.get? "can" = none)
    (hne : frobWMaskedWord I ≠ hopeSourceWord I)
    (hcan : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (frobWWishSlot I) ≠ ⟨1⟩) :
    evalExpr? config { contract := contract, locals := locals } evm
      (wishExpr (.var "w") sender) = .ok (.bool false) := by
  exact vatEvalExpr_or_false_right
    (lhs := .binary .eq (.var "w") sender)
    (rhs := .binary .eq (.storage (canRef (.var "w") sender)) (.intLit 1))
    (evalExpr_frob_w_sender_eq_false (evm := evm) (I := I) locals hsrc hw hne)
    (evalExpr_frob_can_w_eq_false (evm := evm) (I := I) locals hsrc hw hbase hcan)

theorem evalExpr_frob_dart_le_zero_true {evm : EVM.State} {I : ExecutionEnv}
    {locals : Store}
    (hdart : locals.get? "dart" = some (frobDartValue I))
    (hsgt : UInt256.sgt (frobDartWord I) ⟨0⟩ = ⟨0⟩) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.binary .le (.var "dart") (.intLit 0)) = .ok (.bool true) := by
  have hdartEval :
      evalExpr? config { contract := contract, locals := locals } evm (.var "dart") =
        .ok (.int (frobDartInt I)) :=
    vatEvalExpr_varInt (by simpa [frobDartValue] using hdart)
  exact vatEvalExpr_le_int_true hdartEval (by simp [evalExpr?, pure])
    (sgt_zero_eq_zero_to_nonpos (frobDartWord I) hsgt)

theorem evalExpr_frob_dart_ge_zero_true {evm : EVM.State} {I : ExecutionEnv}
    {locals : Store}
    (hdart : locals.get? "dart" = some (frobDartValue I))
    (hslt : UInt256.slt (frobDartWord I) ⟨0⟩ = ⟨0⟩) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.binary .ge (.var "dart") (.intLit 0)) = .ok (.bool true) := by
  have hdartEval :
      evalExpr? config { contract := contract, locals := locals } evm (.var "dart") =
        .ok (.int (frobDartInt I)) :=
    vatEvalExpr_varInt (by simpa [frobDartValue] using hdart)
  exact vatEvalExpr_ge_int_true hdartEval (by simp [evalExpr?, pure])
    (slt_zero_eq_zero_to_nonneg (frobDartWord I) hslt)

theorem evalExpr_frob_dink_le_zero_true {evm : EVM.State} {I : ExecutionEnv}
    {locals : Store}
    (hdink : locals.get? "dink" = some (frobDinkValue I))
    (hsgt : UInt256.sgt (frobDinkWord I) ⟨0⟩ = ⟨0⟩) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.binary .le (.var "dink") (.intLit 0)) = .ok (.bool true) := by
  have hdinkEval :
      evalExpr? config { contract := contract, locals := locals } evm (.var "dink") =
        .ok (.int (frobDinkInt I)) :=
    vatEvalExpr_varInt (by simpa [frobDinkValue] using hdink)
  exact vatEvalExpr_le_int_true hdinkEval (by simp [evalExpr?, pure])
    (sgt_zero_eq_zero_to_nonpos (frobDinkWord I) hsgt)

theorem evalExpr_frob_dink_ge_zero_true {evm : EVM.State} {I : ExecutionEnv}
    {locals : Store}
    (hdink : locals.get? "dink" = some (frobDinkValue I))
    (hslt : UInt256.slt (frobDinkWord I) ⟨0⟩ = ⟨0⟩) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.binary .ge (.var "dink") (.intLit 0)) = .ok (.bool true) := by
  have hdinkEval :
      evalExpr? config { contract := contract, locals := locals } evm (.var "dink") =
        .ok (.int (frobDinkInt I)) :=
    vatEvalExpr_varInt (by simpa [frobDinkValue] using hdink)
  exact vatEvalExpr_ge_int_true hdinkEval (by simp [evalExpr?, pure])
    (slt_zero_eq_zero_to_nonneg (frobDinkWord I) hslt)

theorem evalExpr_frob_LineRef {evm : EVM.State} {locals : Store}
    (hbase : locals.get? "Line" = none) :
    evalExpr? config { contract := contract, locals := locals } evm (.storage LineRef) =
      .ok (.int (Int.ofNat
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨9⟩).toNat)) := by
  rw [evalExpr_storage_scalar
    (er := ({ base := "Line", steps := [] } : EvaledStorageRef))
    (t := .int uint256Int) (hbase := hbase)
    (her := by
      simp [evalStorageRef, evalStorageRefSteps, LineRef, EvalResult.bind, pure, bind])
    (hty := by simp [storageTypeAt?, contract, storageDecls, uint256St])
    (hloc := by
      funext evm
      change storageLayoutRaw ({ base := "Line", steps := [] } : EvaledStorageRef) evm =
        some (wordLoc ⟨9⟩)
      simp [storageLayoutRaw])]
  exact congrArg EvalResult.ok (vatStorageLocLoad_uint256 evm ⟨9⟩)

theorem u256_isZero_ne_zero_to_eq_zero {a : UInt256}
    (h : UInt256.isZero a ≠ ⟨0⟩) :
    a = ⟨0⟩ := by
  by_contra hne
  have hz : UInt256.isZero a = ⟨0⟩ := isZero_eq_zero_of_ne hne
  exact h hz

theorem u256_lor_left_ne_zero_of_lor_ne_zero_right_zero {a b : UInt256}
    (h : UInt256.lor a b ≠ ⟨0⟩) (hb : b = ⟨0⟩) :
    a ≠ ⟨0⟩ := by
  rw [hb, u256_lor_zero] at h
  exact h

theorem nat_lor_lt_two_pow {a b k : ℕ} (ha : a < 2 ^ k) (hb : b < 2 ^ k) :
    Nat.lor a b < 2 ^ k := by
  refine Nat.lt_of_testBit k ?_ ?_ ?_
  · change (a ||| b).testBit k = false
    rw [Nat.testBit_lor]
    rw [Nat.testBit_eq_false_of_lt ha, Nat.testBit_eq_false_of_lt hb]
    rfl
  · simp
  · intro j hj
    change (a ||| b).testBit j = (2 ^ k).testBit j
    rw [Nat.testBit_lor]
    have ha' : a < 2 ^ j := lt_of_lt_of_le ha (Nat.pow_le_pow_right (by omega) (le_of_lt hj))
    have hb' : b < 2 ^ j := lt_of_lt_of_le hb (Nat.pow_le_pow_right (by omega) (le_of_lt hj))
    rw [Nat.testBit_eq_false_of_lt ha', Nat.testBit_eq_false_of_lt hb']
    symm
    exact Nat.testBit_two_pow_of_ne (show k ≠ j by omega)

theorem frob_u256_lor_one_ne_zero (w : UInt256) :
    UInt256.lor (⟨1⟩ : UInt256) w ≠ ⟨0⟩ := by
  intro h
  have hbit := congrArg (fun x : UInt256 => x.toNat % 2) h
  simp [UInt256.lor, Fin.lor, UInt256.size] at hbit
  change (Nat.lor 1 w.toNat % UInt256.size) % 2 = 0 at hbit
  rw [Nat.mod_mod_of_dvd _ (by norm_num [UInt256.size] : 2 ∣ UInt256.size)] at hbit
  have hlorOdd : Nat.lor 1 w.toNat % 2 = 1 := by
    have htest : Nat.testBit (Nat.lor 1 w.toNat) 0 = true := by
      change (1 ||| w.toNat).testBit 0 = true
      rw [Nat.testBit_lor]
      simp
    exact Nat.mod_two_eq_one_iff_testBit_zero.mpr htest
  omega

theorem u256_lor_eq_zero_left {a b : UInt256}
    (h : UInt256.lor a b = ⟨0⟩) :
    a = ⟨0⟩ := by
  have hlorLt :
      Nat.lor a.toNat b.toNat < UInt256.size := by
    simpa [UInt256.size] using
      nat_lor_lt_two_pow
        (a := a.toNat) (b := b.toNat) (k := 256)
        (by change a.val.val < UInt256.size; exact a.val.isLt)
        (by change b.val.val < UInt256.size; exact b.val.isLt)
  have hlorZero : Nat.lor a.toNat b.toNat = 0 := by
    have hnat := congrArg UInt256.toNat h
    change (Nat.lor a.toNat b.toNat % UInt256.size) = 0 at hnat
    rwa [Nat.mod_eq_of_lt hlorLt] at hnat
  apply u256_inj
  have hbit : ∀ i, Nat.testBit a.toNat i = false := by
    intro i
    have hcongr : Nat.testBit (Nat.lor a.toNat b.toNat) i = false := by
      rw [hlorZero]
      simp
    change (a.toNat ||| b.toNat).testBit i = false at hcongr
    rw [Nat.testBit_lor] at hcongr
    cases ha : Nat.testBit a.toNat i
    · rfl
    · cases hb : Nat.testBit b.toNat i <;> simp [ha, hb] at hcongr
  have haNat : a.toNat = 0 := Nat.zero_of_testBit_eq_false hbit
  simpa [haNat]

theorem u256_lor_eq_zero_right {a b : UInt256}
    (h : UInt256.lor a b = ⟨0⟩) :
    b = ⟨0⟩ := by
  have hcomm : UInt256.lor b a = ⟨0⟩ := by
    rw [u256_lor_comm]
    exact h
  exact u256_lor_eq_zero_left hcomm

theorem u256_land_left_ne_zero_of_land_ne_zero {a b : UInt256}
    (h : UInt256.land a b ≠ ⟨0⟩) :
    a ≠ ⟨0⟩ := by
  intro ha
  apply h
  rw [ha]
  exact fork_u256_land_zero_left b

theorem u256_land_right_ne_zero_of_land_ne_zero {a b : UInt256}
    (h : UInt256.land a b ≠ ⟨0⟩) :
    b ≠ ⟨0⟩ := by
  intro hb
  apply h
  rw [hb]
  exact fork_u256_land_zero_right a

theorem frobCeilingSourceCond_of_evm {I : ExecutionEnv}
    {ceilingDebt debtNew ilkLine Line : UInt256}
    (h :
      UInt256.lor
        (UInt256.land
          (UInt256.isZero (UInt256.gt debtNew Line))
          (UInt256.isZero (UInt256.gt ceilingDebt ilkLine)))
        (UInt256.isZero (UInt256.sgt (frobDartWord I) ⟨0⟩)) ≠ ⟨0⟩) :
    frobDartInt I ≤ 0 ∨
      (ceilingDebt.toNat ≤ ilkLine.toNat ∧ debtNew.toNat ≤ Line.toNat) := by
  by_cases hsgt : UInt256.sgt (frobDartWord I) ⟨0⟩ = ⟨0⟩
  · exact Or.inl (sgt_zero_eq_zero_to_nonpos (frobDartWord I) hsgt)
  · have hright :
        UInt256.isZero (UInt256.sgt (frobDartWord I) ⟨0⟩) = ⟨0⟩ :=
      isZero_eq_zero_of_ne hsgt
    have hland :
        UInt256.land
          (UInt256.isZero (UInt256.gt debtNew Line))
          (UInt256.isZero (UInt256.gt ceilingDebt ilkLine)) ≠ ⟨0⟩ :=
      u256_lor_left_ne_zero_of_lor_ne_zero_right_zero h hright
    have hdebtIsZero :
        UInt256.isZero (UInt256.gt debtNew Line) ≠ ⟨0⟩ :=
      u256_land_left_ne_zero_of_land_ne_zero hland
    have hceilingIsZero :
        UInt256.isZero (UInt256.gt ceilingDebt ilkLine) ≠ ⟨0⟩ :=
      u256_land_right_ne_zero_of_land_ne_zero hland
    have hdebtGt : UInt256.gt debtNew Line = ⟨0⟩ :=
      u256_isZero_ne_zero_to_eq_zero hdebtIsZero
    have hceilingGt : UInt256.gt ceilingDebt ilkLine = ⟨0⟩ :=
      u256_isZero_ne_zero_to_eq_zero hceilingIsZero
    exact Or.inr ⟨ugt_eq_zero_to_le hceilingGt, ugt_eq_zero_to_le hdebtGt⟩

theorem frobCeilingSourceFalseCond_of_evm {I : ExecutionEnv}
    {ceilingDebt debtNew ilkLine Line : UInt256}
    (h :
      UInt256.lor
        (UInt256.land
          (UInt256.isZero (UInt256.gt debtNew Line))
          (UInt256.isZero (UInt256.gt ceilingDebt ilkLine)))
        (UInt256.isZero (UInt256.sgt (frobDartWord I) ⟨0⟩)) = ⟨0⟩) :
    0 < frobDartInt I ∧
      ¬ (ceilingDebt.toNat ≤ ilkLine.toNat ∧ debtNew.toNat ≤ Line.toNat) := by
  let bounds :=
    UInt256.land
      (UInt256.isZero (UInt256.gt debtNew Line))
      (UInt256.isZero (UInt256.gt ceilingDebt ilkLine))
  have hdartSgtNe : UInt256.sgt (frobDartWord I) ⟨0⟩ ≠ ⟨0⟩ := by
    intro hdartSgtZero
    have hlorNe :
        UInt256.lor bounds (UInt256.isZero (UInt256.sgt (frobDartWord I) ⟨0⟩)) ≠
          ⟨0⟩ := by
      rw [hdartSgtZero]
      change UInt256.lor bounds (UInt256.isZero (⟨0⟩ : UInt256)) ≠ ⟨0⟩
      rw [u256_lor_comm]
      exact frob_u256_lor_one_ne_zero bounds
    exact hlorNe (by simpa [bounds] using h)
  have hdartPos : 0 < frobDartInt I :=
    sgt_zero_ne_zero_to_pos (frobDartWord I) hdartSgtNe
  constructor
  · exact hdartPos
  · intro hbounds
    have hdebtGtZero : UInt256.gt debtNew Line = ⟨0⟩ :=
      ugt_zero (by omega)
    have hceilingGtZero : UInt256.gt ceilingDebt ilkLine = ⟨0⟩ :=
      ugt_zero (by omega)
    have hboundsOne : bounds = ⟨1⟩ := by
      rw [show bounds = UInt256.land (UInt256.isZero (UInt256.gt debtNew Line))
        (UInt256.isZero (UInt256.gt ceilingDebt ilkLine)) from rfl]
      rw [hdebtGtZero, hceilingGtZero]
      native_decide
    have hlorNe :
        UInt256.lor bounds (UInt256.isZero (UInt256.sgt (frobDartWord I) ⟨0⟩)) ≠
          ⟨0⟩ := by
      rw [hboundsOne]
      exact frob_u256_lor_one_ne_zero
        (UInt256.isZero (UInt256.sgt (frobDartWord I) ⟨0⟩))
    exact hlorNe (by simpa [bounds] using h)

theorem frobSafetySourceCond_of_evm {I : ExecutionEnv} {tab inkSpot : UInt256}
    (h :
      UInt256.lor
        (UInt256.isZero (UInt256.gt tab inkSpot))
        (UInt256.land
          (UInt256.isZero (UInt256.slt (frobDinkWord I) ⟨0⟩))
          (UInt256.isZero (UInt256.sgt (frobDartWord I) ⟨0⟩))) ≠ ⟨0⟩) :
    (frobDartInt I ≤ 0 ∧ 0 ≤ frobDinkInt I) ∨
      tab.toNat ≤ inkSpot.toNat := by
  by_cases hgt : UInt256.gt tab inkSpot = ⟨0⟩
  · exact Or.inr (ugt_eq_zero_to_le hgt)
  · have hleft : UInt256.isZero (UInt256.gt tab inkSpot) = ⟨0⟩ :=
      isZero_eq_zero_of_ne hgt
    have hcomm := h
    rw [u256_lor_comm] at hcomm
    have hland :
        UInt256.land
          (UInt256.isZero (UInt256.slt (frobDinkWord I) ⟨0⟩))
          (UInt256.isZero (UInt256.sgt (frobDartWord I) ⟨0⟩)) ≠ ⟨0⟩ :=
      u256_lor_left_ne_zero_of_lor_ne_zero_right_zero hcomm hleft
    have hdinkIsZero :
        UInt256.isZero (UInt256.slt (frobDinkWord I) ⟨0⟩) ≠ ⟨0⟩ :=
      u256_land_left_ne_zero_of_land_ne_zero hland
    have hdartIsZero :
        UInt256.isZero (UInt256.sgt (frobDartWord I) ⟨0⟩) ≠ ⟨0⟩ :=
      u256_land_right_ne_zero_of_land_ne_zero hland
    have hdinkSlt : UInt256.slt (frobDinkWord I) ⟨0⟩ = ⟨0⟩ :=
      u256_isZero_ne_zero_to_eq_zero hdinkIsZero
    have hdartSgt : UInt256.sgt (frobDartWord I) ⟨0⟩ = ⟨0⟩ :=
      u256_isZero_ne_zero_to_eq_zero hdartIsZero
    exact Or.inl
      ⟨sgt_zero_eq_zero_to_nonpos (frobDartWord I) hdartSgt,
        slt_zero_eq_zero_to_nonneg (frobDinkWord I) hdinkSlt⟩

theorem frobSafetySourceFalseCond_of_evm {I : ExecutionEnv} {tab inkSpot : UInt256}
    (h :
      UInt256.lor
        (UInt256.isZero (UInt256.gt tab inkSpot))
        (UInt256.land
          (UInt256.isZero (UInt256.slt (frobDinkWord I) ⟨0⟩))
          (UInt256.isZero (UInt256.sgt (frobDartWord I) ⟨0⟩))) = ⟨0⟩) :
    ¬ (frobDartInt I ≤ 0 ∧ 0 ≤ frobDinkInt I) ∧
      inkSpot.toNat < tab.toNat := by
  let shortcut :=
    UInt256.land
      (UInt256.isZero (UInt256.slt (frobDinkWord I) ⟨0⟩))
      (UInt256.isZero (UInt256.sgt (frobDartWord I) ⟨0⟩))
  have hgtNe : UInt256.gt tab inkSpot ≠ ⟨0⟩ := by
    intro hgtZero
    have hlorNe :
        UInt256.lor (UInt256.isZero (UInt256.gt tab inkSpot)) shortcut ≠ ⟨0⟩ := by
      simpa [shortcut, hgtZero] using frob_u256_lor_one_ne_zero shortcut
    exact hlorNe (by simpa [shortcut] using h)
  have htabGt : inkSpot.toNat < tab.toNat := ugt_ne_zero_to_gt hgtNe
  constructor
  · intro hboth
    have hdinkSlt : UInt256.slt (frobDinkWord I) ⟨0⟩ = ⟨0⟩ := by
      by_contra hne
      have hneg : frobDinkInt I < 0 :=
        slt_zero_ne_zero_to_neg (frobDinkWord I) hne
      omega
    have hdartSgt : UInt256.sgt (frobDartWord I) ⟨0⟩ = ⟨0⟩ := by
      by_contra hne
      have hpos : 0 < frobDartInt I :=
        sgt_zero_ne_zero_to_pos (frobDartWord I) hne
      omega
    have hshortcutOne : shortcut = ⟨1⟩ := by
      rw [show shortcut = UInt256.land
        (UInt256.isZero (UInt256.slt (frobDinkWord I) ⟨0⟩))
        (UInt256.isZero (UInt256.sgt (frobDartWord I) ⟨0⟩)) from rfl]
      rw [hdinkSlt, hdartSgt]
      native_decide
    have hlorNe :
        UInt256.lor (UInt256.isZero (UInt256.gt tab inkSpot)) shortcut ≠ ⟨0⟩ := by
      rw [hshortcutOne, u256_lor_comm]
      exact frob_u256_lor_one_ne_zero (UInt256.isZero (UInt256.gt tab inkSpot))
    exact hlorNe (by simpa [shortcut] using h)
  · exact htabGt

theorem frobAuthUSourceCond_of_evm {I : ExecutionEnv} {uWish : UInt256}
    (h :
      UInt256.lor
        (UInt256.lor (UInt256.eq uWish ⟨1⟩)
          (UInt256.eq (frobUMaskedWord I) (hopeSourceWord I)))
        (UInt256.land
          (UInt256.isZero (UInt256.slt (frobDinkWord I) ⟨0⟩))
          (UInt256.isZero (UInt256.sgt (frobDartWord I) ⟨0⟩))) ≠ ⟨0⟩) :
    (frobDartInt I ≤ 0 ∧ 0 ≤ frobDinkInt I) ∨
      (uWish = ⟨1⟩ ∨ frobUMaskedWord I = hopeSourceWord I) := by
  by_cases hland :
      UInt256.land
        (UInt256.isZero (UInt256.slt (frobDinkWord I) ⟨0⟩))
        (UInt256.isZero (UInt256.sgt (frobDartWord I) ⟨0⟩)) = ⟨0⟩
  · have hwish :
        UInt256.lor (UInt256.eq uWish ⟨1⟩)
          (UInt256.eq (frobUMaskedWord I) (hopeSourceWord I)) ≠ ⟨0⟩ :=
      u256_lor_left_ne_zero_of_lor_ne_zero_right_zero h hland
    by_cases hsrc : UInt256.eq (frobUMaskedWord I) (hopeSourceWord I) = ⟨0⟩
    · have hcan : UInt256.eq uWish ⟨1⟩ ≠ ⟨0⟩ :=
        u256_lor_left_ne_zero_of_lor_ne_zero_right_zero hwish hsrc
      exact Or.inr (Or.inl (u256_eq_ne_zero_to_eq hcan))
    · exact Or.inr (Or.inr (u256_eq_ne_zero_to_eq hsrc))
  · have hdinkIsZero :
        UInt256.isZero (UInt256.slt (frobDinkWord I) ⟨0⟩) ≠ ⟨0⟩ :=
      u256_land_left_ne_zero_of_land_ne_zero hland
    have hdartIsZero :
        UInt256.isZero (UInt256.sgt (frobDartWord I) ⟨0⟩) ≠ ⟨0⟩ :=
      u256_land_right_ne_zero_of_land_ne_zero hland
    have hdinkSlt : UInt256.slt (frobDinkWord I) ⟨0⟩ = ⟨0⟩ :=
      u256_isZero_ne_zero_to_eq_zero hdinkIsZero
    have hdartSgt : UInt256.sgt (frobDartWord I) ⟨0⟩ = ⟨0⟩ :=
      u256_isZero_ne_zero_to_eq_zero hdartIsZero
    exact Or.inl
      ⟨sgt_zero_eq_zero_to_nonpos (frobDartWord I) hdartSgt,
        slt_zero_eq_zero_to_nonneg (frobDinkWord I) hdinkSlt⟩

theorem frobAuthVSourceCond_of_evm {I : ExecutionEnv} {vWish : UInt256}
    (h :
      UInt256.lor
        (UInt256.lor (UInt256.eq vWish ⟨1⟩)
          (UInt256.eq (frobVMaskedWord I) (hopeSourceWord I)))
        (UInt256.isZero (UInt256.sgt (frobDinkWord I) ⟨0⟩)) ≠ ⟨0⟩) :
    frobDinkInt I ≤ 0 ∨
      (vWish = ⟨1⟩ ∨ frobVMaskedWord I = hopeSourceWord I) := by
  by_cases hsgt : UInt256.sgt (frobDinkWord I) ⟨0⟩ = ⟨0⟩
  · exact Or.inl (sgt_zero_eq_zero_to_nonpos (frobDinkWord I) hsgt)
  · have hright : UInt256.isZero (UInt256.sgt (frobDinkWord I) ⟨0⟩) = ⟨0⟩ :=
      isZero_eq_zero_of_ne hsgt
    have hwish :
        UInt256.lor (UInt256.eq vWish ⟨1⟩)
          (UInt256.eq (frobVMaskedWord I) (hopeSourceWord I)) ≠ ⟨0⟩ :=
      u256_lor_left_ne_zero_of_lor_ne_zero_right_zero h hright
    by_cases hsrc : UInt256.eq (frobVMaskedWord I) (hopeSourceWord I) = ⟨0⟩
    · have hcan : UInt256.eq vWish ⟨1⟩ ≠ ⟨0⟩ :=
        u256_lor_left_ne_zero_of_lor_ne_zero_right_zero hwish hsrc
      exact Or.inr (Or.inl (u256_eq_ne_zero_to_eq hcan))
    · exact Or.inr (Or.inr (u256_eq_ne_zero_to_eq hsrc))

theorem frobAuthWSourceCond_of_evm {I : ExecutionEnv} {wWish : UInt256}
    (h :
      UInt256.lor
        (UInt256.lor (UInt256.eq wWish ⟨1⟩)
          (UInt256.eq (frobWMaskedWord I) (hopeSourceWord I)))
        (UInt256.isZero (UInt256.slt (frobDartWord I) ⟨0⟩)) ≠ ⟨0⟩) :
    0 ≤ frobDartInt I ∨
      (wWish = ⟨1⟩ ∨ frobWMaskedWord I = hopeSourceWord I) := by
  by_cases hslt : UInt256.slt (frobDartWord I) ⟨0⟩ = ⟨0⟩
  · exact Or.inl (slt_zero_eq_zero_to_nonneg (frobDartWord I) hslt)
  · have hright : UInt256.isZero (UInt256.slt (frobDartWord I) ⟨0⟩) = ⟨0⟩ :=
      isZero_eq_zero_of_ne hslt
    have hwish :
        UInt256.lor (UInt256.eq wWish ⟨1⟩)
          (UInt256.eq (frobWMaskedWord I) (hopeSourceWord I)) ≠ ⟨0⟩ :=
      u256_lor_left_ne_zero_of_lor_ne_zero_right_zero h hright
    by_cases hsrc : UInt256.eq (frobWMaskedWord I) (hopeSourceWord I) = ⟨0⟩
    · have hcan : UInt256.eq wWish ⟨1⟩ ≠ ⟨0⟩ :=
        u256_lor_left_ne_zero_of_lor_ne_zero_right_zero hwish hsrc
      exact Or.inr (Or.inl (u256_eq_ne_zero_to_eq hcan))
    · exact Or.inr (Or.inr (u256_eq_ne_zero_to_eq hsrc))

theorem frobDustSourceCond_of_evm {urnArtNew tab ilkDust : UInt256}
    (h :
      UInt256.lor
        (UInt256.isZero (UInt256.lt tab ilkDust))
        (UInt256.eq ⟨0⟩ urnArtNew) ≠ ⟨0⟩) :
    urnArtNew.toNat = 0 ∨ ilkDust.toNat ≤ tab.toNat := by
  by_cases hzero : UInt256.eq ⟨0⟩ urnArtNew = ⟨0⟩
  · have hltIsZero : UInt256.isZero (UInt256.lt tab ilkDust) ≠ ⟨0⟩ :=
      u256_lor_left_ne_zero_of_lor_ne_zero_right_zero h hzero
    have hlt : UInt256.lt tab ilkDust = ⟨0⟩ :=
      u256_isZero_ne_zero_to_eq_zero hltIsZero
    exact Or.inr (ult_eq_zero_to_le hlt)
  · have heq : (⟨0⟩ : UInt256) = urnArtNew :=
      u256_eq_ne_zero_to_eq hzero
    exact Or.inl (by rw [← heq]; rfl)

theorem vatSlotWord_debtStore_accountMapEquiv {σ_evm σ_solm : AccountMap}
    {I : ExecutionEnv} (hAccounts : accountMapEquiv σ_evm σ_solm)
    (slot debtNew : UInt256) :
    vatSlotWord slot (sstoreAccountMap I.codeOwner σ_evm foldDebtSlot debtNew) I =
      vatSlotWord slot (sstoreAccountMap I.codeOwner σ_solm foldDebtSlot debtNew) I := by
  simpa [vatSlotWord] using
    accountMapEquiv_storage_findD
      (accountMapEquiv_sstoreAccountMap I.codeOwner foldDebtSlot debtNew hAccounts)
      I.codeOwner slot ⟨0⟩

theorem evalExpr_frob_dust_req_true {evm : EVM.State} {locals : Store}
    (urnArtNew tab ilkDust : UInt256)
    (hurnArtNew :
      locals.get? "urnArtNew" = some (.int (Int.ofNat urnArtNew.toNat)))
    (htab : locals.get? "tab" = some (.int (Int.ofNat tab.toNat)))
    (hilkDust : locals.get? "ilkDust" = some (.int (Int.ofNat ilkDust.toNat)))
    (hok : urnArtNew.toNat = 0 ∨ ilkDust.toNat ≤ tab.toNat) :
    evalExpr? config { contract := contract, locals := locals } evm
      (eitherExpr (.binary .eq (.var "urnArtNew") (.intLit 0))
        (.binary .ge (.var "tab") (.var "ilkDust"))) =
      .ok (.bool true) := by
  have hurnArtNewEval :
      evalExpr? config { contract := contract, locals := locals } evm (.var "urnArtNew") =
        .ok (.int (Int.ofNat urnArtNew.toNat)) :=
    vatEvalExpr_varUInt256 hurnArtNew
  have htabEval :
      evalExpr? config { contract := contract, locals := locals } evm (.var "tab") =
        .ok (.int (Int.ofNat tab.toNat)) :=
    vatEvalExpr_varUInt256 htab
  have hilkDustEval :
      evalExpr? config { contract := contract, locals := locals } evm (.var "ilkDust") =
        .ok (.int (Int.ofNat ilkDust.toNat)) :=
    vatEvalExpr_varUInt256 hilkDust
  cases hok with
  | inl hzero =>
      have hleft :
          evalExpr? config { contract := contract, locals := locals } evm
            (.binary .eq (.var "urnArtNew") (.intLit 0)) = .ok (.bool true) := by
        simp [evalExpr?, EvalResult.bind, bind, hurnArtNewEval, evalBinaryOp?, hzero]
      exact vatEvalExpr_or_true_left hleft
  | inr hge =>
      by_cases hzero : urnArtNew.toNat = 0
      · have hleft :
            evalExpr? config { contract := contract, locals := locals } evm
              (.binary .eq (.var "urnArtNew") (.intLit 0)) = .ok (.bool true) := by
          simp [evalExpr?, EvalResult.bind, bind, hurnArtNewEval, evalBinaryOp?, hzero]
        exact vatEvalExpr_or_true_left hleft
      · have hleft :
            evalExpr? config { contract := contract, locals := locals } evm
              (.binary .eq (.var "urnArtNew") (.intLit 0)) = .ok (.bool false) := by
          simp [evalExpr?, EvalResult.bind, bind, hurnArtNewEval, evalBinaryOp?, hzero]
        exact vatEvalExpr_or_false_right hleft
          (vatEvalExpr_ge_uint256_true htabEval hilkDustEval hge)

theorem evalExpr_frob_auth_u_req_true {evm : EVM.State} {I : ExecutionEnv}
    {locals : Store}
    (uWish : UInt256)
    (hdart : locals.get? "dart" = some (frobDartValue I))
    (hdink : locals.get? "dink" = some (frobDinkValue I))
    (hu : locals.get? "u" = some (frobUValue I))
    (hbase : locals.get? "can" = none)
    (hsrc : evm.executionEnv.source = I.source)
    (hcanLoad :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (frobUWishSlot I) = uWish)
    (hok :
      (frobDartInt I ≤ 0 ∧ 0 ≤ frobDinkInt I) ∨
        (uWish = ⟨1⟩ ∨ frobUMaskedWord I = hopeSourceWord I)) :
    evalExpr? config { contract := contract, locals := locals } evm
      (eitherExpr
        (bothExpr
          (.binary .le (.var "dart") (.intLit 0))
          (.binary .ge (.var "dink") (.intLit 0)))
        (wishExpr (.var "u") sender)) =
      .ok (.bool true) := by
  cases hok with
  | inl hsign =>
      have hdartEval :
          evalExpr? config { contract := contract, locals := locals } evm (.var "dart") =
            .ok (.int (frobDartInt I)) :=
        vatEvalExpr_varInt (by simpa [frobDartValue] using hdart)
      have hdinkEval :
          evalExpr? config { contract := contract, locals := locals } evm (.var "dink") =
            .ok (.int (frobDinkInt I)) :=
        vatEvalExpr_varInt (by simpa [frobDinkValue] using hdink)
      have hleft :
          evalExpr? config { contract := contract, locals := locals } evm
            (bothExpr
              (.binary .le (.var "dart") (.intLit 0))
              (.binary .ge (.var "dink") (.intLit 0))) = .ok (.bool true) := by
        exact vatEvalExpr_and_true
          (vatEvalExpr_le_int_true hdartEval (by simp [evalExpr?, pure]) hsign.1)
          (vatEvalExpr_ge_int_true hdinkEval (by simp [evalExpr?, pure]) hsign.2)
      exact vatEvalExpr_or_true_left hleft
  | inr hwish =>
      have hdartEval :
          evalExpr? config { contract := contract, locals := locals } evm (.var "dart") =
            .ok (.int (frobDartInt I)) :=
        vatEvalExpr_varInt (by simpa [frobDartValue] using hdart)
      by_cases hdartNonpos : frobDartInt I ≤ 0
      · have hdinkEval :
            evalExpr? config { contract := contract, locals := locals } evm (.var "dink") =
              .ok (.int (frobDinkInt I)) :=
          vatEvalExpr_varInt (by simpa [frobDinkValue] using hdink)
        by_cases hdinkNonneg : 0 ≤ frobDinkInt I
        · have hleft :
              evalExpr? config { contract := contract, locals := locals } evm
                (bothExpr
                  (.binary .le (.var "dart") (.intLit 0))
                  (.binary .ge (.var "dink") (.intLit 0))) = .ok (.bool true) := by
            exact vatEvalExpr_and_true
              (vatEvalExpr_le_int_true hdartEval (by simp [evalExpr?, pure]) hdartNonpos)
              (vatEvalExpr_ge_int_true hdinkEval (by simp [evalExpr?, pure]) hdinkNonneg)
          exact vatEvalExpr_or_true_left hleft
        · have hleftTrue :
              evalExpr? config { contract := contract, locals := locals } evm
                (.binary .le (.var "dart") (.intLit 0)) = .ok (.bool true) :=
            vatEvalExpr_le_int_true hdartEval (by simp [evalExpr?, pure]) hdartNonpos
          have hrightFalse :
              evalExpr? config { contract := contract, locals := locals } evm
                (.binary .ge (.var "dink") (.intLit 0)) = .ok (.bool false) :=
            vatEvalExpr_ge_int_false hdinkEval (by simp [evalExpr?, pure])
              (not_le.mp hdinkNonneg)
          have hleft :
              evalExpr? config { contract := contract, locals := locals } evm
                (bothExpr
                  (.binary .le (.var "dart") (.intLit 0))
                  (.binary .ge (.var "dink") (.intLit 0))) = .ok (.bool false) :=
            vatEvalExpr_and_true_false_right hleftTrue hrightFalse
          exact vatEvalExpr_or_false_right hleft (by
            cases hwish with
            | inl hcan =>
                by_cases hsource : frobUMaskedWord I = hopeSourceWord I
                · exact evalExpr_frob_wish_u_true_src (evm := evm) (I := I) locals
                    hsrc hu hsource
                · exact evalExpr_frob_wish_u_true_can (evm := evm) (I := I) locals
                    hsrc hu hbase hsource (by rw [hcanLoad, hcan])
            | inr hsource =>
                exact evalExpr_frob_wish_u_true_src (evm := evm) (I := I) locals
                  hsrc hu hsource)
      · have hleft :
            evalExpr? config { contract := contract, locals := locals } evm
              (bothExpr
                (.binary .le (.var "dart") (.intLit 0))
                (.binary .ge (.var "dink") (.intLit 0))) = .ok (.bool false) := by
          exact vatEvalExpr_and_false_left
            (vatEvalExpr_le_int_false hdartEval (by simp [evalExpr?, pure])
              (not_le.mp hdartNonpos))
        exact vatEvalExpr_or_false_right hleft (by
          cases hwish with
          | inl hcan =>
              by_cases hsource : frobUMaskedWord I = hopeSourceWord I
              · exact evalExpr_frob_wish_u_true_src (evm := evm) (I := I) locals
                  hsrc hu hsource
              · exact evalExpr_frob_wish_u_true_can (evm := evm) (I := I) locals
                  hsrc hu hbase hsource (by rw [hcanLoad, hcan])
          | inr hsource =>
              exact evalExpr_frob_wish_u_true_src (evm := evm) (I := I) locals
                hsrc hu hsource)

theorem frobAuthUSourceFalseCond_of_evm {I : ExecutionEnv} {uWish : UInt256}
    (h :
      UInt256.lor
        (UInt256.lor (UInt256.eq uWish ⟨1⟩)
          (UInt256.eq (frobUMaskedWord I) (hopeSourceWord I)))
        (UInt256.land
          (UInt256.isZero (UInt256.slt (frobDinkWord I) ⟨0⟩))
          (UInt256.isZero (UInt256.sgt (frobDartWord I) ⟨0⟩))) = ⟨0⟩) :
    ¬ (frobDartInt I ≤ 0 ∧ 0 ≤ frobDinkInt I) ∧
      uWish ≠ ⟨1⟩ ∧ frobUMaskedWord I ≠ hopeSourceWord I := by
  let both :=
    UInt256.land
      (UInt256.isZero (UInt256.slt (frobDinkWord I) ⟨0⟩))
      (UInt256.isZero (UInt256.sgt (frobDartWord I) ⟨0⟩))
  constructor
  · intro hboth
    have hdinkSlt : UInt256.slt (frobDinkWord I) ⟨0⟩ = ⟨0⟩ := by
      by_contra hne
      have hneg : frobDinkInt I < 0 :=
        slt_zero_ne_zero_to_neg (frobDinkWord I) hne
      omega
    have hdartSgt : UInt256.sgt (frobDartWord I) ⟨0⟩ = ⟨0⟩ := by
      by_contra hne
      have hpos : 0 < frobDartInt I :=
        sgt_zero_ne_zero_to_pos (frobDartWord I) hne
      omega
    have hbothOne : both = ⟨1⟩ := by
      rw [show both = UInt256.land
        (UInt256.isZero (UInt256.slt (frobDinkWord I) ⟨0⟩))
        (UInt256.isZero (UInt256.sgt (frobDartWord I) ⟨0⟩)) from rfl]
      rw [hdinkSlt, hdartSgt]
      native_decide
    have hlorNe :
        UInt256.lor
          (UInt256.lor (UInt256.eq uWish ⟨1⟩)
            (UInt256.eq (frobUMaskedWord I) (hopeSourceWord I))) both ≠ ⟨0⟩ := by
      rw [hbothOne, u256_lor_comm]
      exact frob_u256_lor_one_ne_zero
        (UInt256.lor (UInt256.eq uWish ⟨1⟩)
          (UInt256.eq (frobUMaskedWord I) (hopeSourceWord I)))
    exact hlorNe (by simpa [both] using h)
  · constructor
    · intro hu
      have houterLeft :
          UInt256.lor (UInt256.eq uWish ⟨1⟩)
            (UInt256.eq (frobUMaskedWord I) (hopeSourceWord I)) = ⟨0⟩ :=
        u256_lor_eq_zero_left (by simpa [both] using h)
      have hcanZero : UInt256.eq uWish ⟨1⟩ = ⟨0⟩ :=
        u256_lor_eq_zero_left houterLeft
      have hcanOne : UInt256.eq uWish ⟨1⟩ = ⟨1⟩ := by
        rw [hu]
        rw [uInt256_eq_self]
      rw [hcanOne] at hcanZero
      exact one_ne_zero_uint hcanZero
    · intro hsrc
      have houterLeft :
          UInt256.lor (UInt256.eq uWish ⟨1⟩)
            (UInt256.eq (frobUMaskedWord I) (hopeSourceWord I)) = ⟨0⟩ :=
        u256_lor_eq_zero_left (by simpa [both] using h)
      have hsrcZero : UInt256.eq (frobUMaskedWord I) (hopeSourceWord I) = ⟨0⟩ :=
        u256_lor_eq_zero_right houterLeft
      have hsrcOne : UInt256.eq (frobUMaskedWord I) (hopeSourceWord I) = ⟨1⟩ := by
        rw [hsrc]
        rw [uInt256_eq_self]
      rw [hsrcOne] at hsrcZero
      exact one_ne_zero_uint hsrcZero

theorem evalExpr_frob_auth_u_req_false {evm : EVM.State} {I : ExecutionEnv}
    {locals : Store}
    (uWish : UInt256)
    (hdart : locals.get? "dart" = some (frobDartValue I))
    (hdink : locals.get? "dink" = some (frobDinkValue I))
    (hu : locals.get? "u" = some (frobUValue I))
    (hbase : locals.get? "can" = none)
    (hsrc : evm.executionEnv.source = I.source)
    (hcanLoad :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (frobUWishSlot I) = uWish)
    (hbad :
      ¬ (frobDartInt I ≤ 0 ∧ 0 ≤ frobDinkInt I) ∧
        uWish ≠ ⟨1⟩ ∧ frobUMaskedWord I ≠ hopeSourceWord I) :
    evalExpr? config { contract := contract, locals := locals } evm
      (eitherExpr
        (bothExpr
          (.binary .le (.var "dart") (.intLit 0))
          (.binary .ge (.var "dink") (.intLit 0)))
        (wishExpr (.var "u") sender)) =
      .ok (.bool false) := by
  have hdartEval :
      evalExpr? config { contract := contract, locals := locals } evm (.var "dart") =
        .ok (.int (frobDartInt I)) :=
    vatEvalExpr_varInt (by simpa [frobDartValue] using hdart)
  have hdinkEval :
      evalExpr? config { contract := contract, locals := locals } evm (.var "dink") =
        .ok (.int (frobDinkInt I)) :=
    vatEvalExpr_varInt (by simpa [frobDinkValue] using hdink)
  have hleft :
      evalExpr? config { contract := contract, locals := locals } evm
        (bothExpr
          (.binary .le (.var "dart") (.intLit 0))
          (.binary .ge (.var "dink") (.intLit 0))) =
      .ok (.bool false) := by
    by_cases hdartNonpos : frobDartInt I ≤ 0
    · have hdinkNeg : frobDinkInt I < 0 := by
        have hdinkNot : ¬ 0 ≤ frobDinkInt I := by
          intro hdinkNonneg
          exact hbad.1 ⟨hdartNonpos, hdinkNonneg⟩
        exact lt_of_not_ge hdinkNot
      exact vatEvalExpr_and_true_false_right
        (vatEvalExpr_le_int_true hdartEval (by simp [evalExpr?, pure]) hdartNonpos)
        (vatEvalExpr_ge_int_false hdinkEval (by simp [evalExpr?, pure]) hdinkNeg)
    · exact vatEvalExpr_and_false_left
        (vatEvalExpr_le_int_false hdartEval (by simp [evalExpr?, pure])
          (lt_of_not_ge hdartNonpos))
  exact vatEvalExpr_or_false_right hleft
    (evalExpr_frob_wish_u_false (evm := evm) (I := I) locals hsrc hu hbase hbad.2.2
      (by rw [hcanLoad]; exact hbad.2.1))

theorem evalExpr_frob_auth_v_req_true {evm : EVM.State} {I : ExecutionEnv}
    {locals : Store}
    (vWish : UInt256)
    (hdink : locals.get? "dink" = some (frobDinkValue I))
    (hv : locals.get? "v" = some (frobVValue I))
    (hbase : locals.get? "can" = none)
    (hsrc : evm.executionEnv.source = I.source)
    (hcanLoad :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (frobVWishSlot I) = vWish)
    (hok :
      frobDinkInt I ≤ 0 ∨
        (vWish = ⟨1⟩ ∨ frobVMaskedWord I = hopeSourceWord I)) :
    evalExpr? config { contract := contract, locals := locals } evm
      (eitherExpr (.binary .le (.var "dink") (.intLit 0)) (wishExpr (.var "v") sender)) =
      .ok (.bool true) := by
  have hdinkEval :
      evalExpr? config { contract := contract, locals := locals } evm (.var "dink") =
        .ok (.int (frobDinkInt I)) :=
    vatEvalExpr_varInt (by simpa [frobDinkValue] using hdink)
  cases hok with
  | inl hle =>
      exact vatEvalExpr_or_true_left
        (vatEvalExpr_le_int_true hdinkEval (by simp [evalExpr?, pure]) hle)
  | inr hwish =>
      by_cases hle : frobDinkInt I ≤ 0
      · exact vatEvalExpr_or_true_left
          (vatEvalExpr_le_int_true hdinkEval (by simp [evalExpr?, pure]) hle)
      · exact vatEvalExpr_or_false_right
          (vatEvalExpr_le_int_false hdinkEval (by simp [evalExpr?, pure]) (not_le.mp hle))
          (by
            cases hwish with
            | inl hcan =>
                by_cases hsource : frobVMaskedWord I = hopeSourceWord I
                · exact evalExpr_frob_wish_v_true_src (evm := evm) (I := I) locals
                    hsrc hv hsource
                · exact evalExpr_frob_wish_v_true_can (evm := evm) (I := I) locals
                    hsrc hv hbase hsource (by rw [hcanLoad, hcan])
            | inr hsource =>
                exact evalExpr_frob_wish_v_true_src (evm := evm) (I := I) locals
                  hsrc hv hsource)

theorem frobAuthVSourceFalseCond_of_evm {I : ExecutionEnv} {vWish : UInt256}
    (h :
      UInt256.lor
        (UInt256.lor (UInt256.eq vWish ⟨1⟩)
          (UInt256.eq (frobVMaskedWord I) (hopeSourceWord I)))
        (UInt256.isZero (UInt256.sgt (frobDinkWord I) ⟨0⟩)) = ⟨0⟩) :
    ¬ frobDinkInt I ≤ 0 ∧
      vWish ≠ ⟨1⟩ ∧ frobVMaskedWord I ≠ hopeSourceWord I := by
  constructor
  · intro hdinkNonpos
    have hrightZero :
        UInt256.isZero (UInt256.sgt (frobDinkWord I) ⟨0⟩) = ⟨0⟩ :=
      u256_lor_eq_zero_right h
    have hsgtZero : UInt256.sgt (frobDinkWord I) ⟨0⟩ = ⟨0⟩ := by
      by_contra hne
      have hpos : 0 < frobDinkInt I :=
        sgt_zero_ne_zero_to_pos (frobDinkWord I) hne
      omega
    have hrightOne :
        UInt256.isZero (UInt256.sgt (frobDinkWord I) ⟨0⟩) = ⟨1⟩ := by
      rw [hsgtZero]
      native_decide
    rw [hrightOne] at hrightZero
    exact one_ne_zero_uint hrightZero
  · constructor
    · intro hv
      have houterLeft :
          UInt256.lor (UInt256.eq vWish ⟨1⟩)
            (UInt256.eq (frobVMaskedWord I) (hopeSourceWord I)) = ⟨0⟩ :=
        u256_lor_eq_zero_left h
      have hcanZero : UInt256.eq vWish ⟨1⟩ = ⟨0⟩ :=
        u256_lor_eq_zero_left houterLeft
      have hcanOne : UInt256.eq vWish ⟨1⟩ = ⟨1⟩ := by
        rw [hv]
        rw [uInt256_eq_self]
      rw [hcanOne] at hcanZero
      exact one_ne_zero_uint hcanZero
    · intro hsrc
      have houterLeft :
          UInt256.lor (UInt256.eq vWish ⟨1⟩)
            (UInt256.eq (frobVMaskedWord I) (hopeSourceWord I)) = ⟨0⟩ :=
        u256_lor_eq_zero_left h
      have hsrcZero : UInt256.eq (frobVMaskedWord I) (hopeSourceWord I) = ⟨0⟩ :=
        u256_lor_eq_zero_right houterLeft
      have hsrcOne : UInt256.eq (frobVMaskedWord I) (hopeSourceWord I) = ⟨1⟩ := by
        rw [hsrc]
        rw [uInt256_eq_self]
      rw [hsrcOne] at hsrcZero
      exact one_ne_zero_uint hsrcZero

theorem evalExpr_frob_auth_v_req_false {evm : EVM.State} {I : ExecutionEnv}
    {locals : Store}
    (vWish : UInt256)
    (hdink : locals.get? "dink" = some (frobDinkValue I))
    (hv : locals.get? "v" = some (frobVValue I))
    (hbase : locals.get? "can" = none)
    (hsrc : evm.executionEnv.source = I.source)
    (hcanLoad :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (frobVWishSlot I) = vWish)
    (hbad :
      ¬ frobDinkInt I ≤ 0 ∧
        vWish ≠ ⟨1⟩ ∧ frobVMaskedWord I ≠ hopeSourceWord I) :
    evalExpr? config { contract := contract, locals := locals } evm
      (eitherExpr (.binary .le (.var "dink") (.intLit 0)) (wishExpr (.var "v") sender)) =
      .ok (.bool false) := by
  have hdinkEval :
      evalExpr? config { contract := contract, locals := locals } evm (.var "dink") =
        .ok (.int (frobDinkInt I)) :=
    vatEvalExpr_varInt (by simpa [frobDinkValue] using hdink)
  exact vatEvalExpr_or_false_right
    (vatEvalExpr_le_int_false hdinkEval (by simp [evalExpr?, pure])
      (lt_of_not_ge hbad.1))
    (evalExpr_frob_wish_v_false (evm := evm) (I := I) locals hsrc hv hbase hbad.2.2
      (by rw [hcanLoad]; exact hbad.2.1))

theorem evalExpr_frob_auth_w_req_true {evm : EVM.State} {I : ExecutionEnv}
    {locals : Store}
    (wWish : UInt256)
    (hdart : locals.get? "dart" = some (frobDartValue I))
    (hw : locals.get? "w" = some (frobWValue I))
    (hbase : locals.get? "can" = none)
    (hsrc : evm.executionEnv.source = I.source)
    (hcanLoad :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (frobWWishSlot I) = wWish)
    (hok :
      0 ≤ frobDartInt I ∨
        (wWish = ⟨1⟩ ∨ frobWMaskedWord I = hopeSourceWord I)) :
    evalExpr? config { contract := contract, locals := locals } evm
      (eitherExpr (.binary .ge (.var "dart") (.intLit 0)) (wishExpr (.var "w") sender)) =
      .ok (.bool true) := by
  have hdartEval :
      evalExpr? config { contract := contract, locals := locals } evm (.var "dart") =
        .ok (.int (frobDartInt I)) :=
    vatEvalExpr_varInt (by simpa [frobDartValue] using hdart)
  cases hok with
  | inl hge =>
      exact vatEvalExpr_or_true_left
        (vatEvalExpr_ge_int_true hdartEval (by simp [evalExpr?, pure]) hge)
  | inr hwish =>
      by_cases hge : 0 ≤ frobDartInt I
      · exact vatEvalExpr_or_true_left
          (vatEvalExpr_ge_int_true hdartEval (by simp [evalExpr?, pure]) hge)
      · exact vatEvalExpr_or_false_right
          (vatEvalExpr_ge_int_false hdartEval (by simp [evalExpr?, pure]) (not_le.mp hge))
          (by
            cases hwish with
            | inl hcan =>
                by_cases hsource : frobWMaskedWord I = hopeSourceWord I
                · exact evalExpr_frob_wish_w_true_src (evm := evm) (I := I) locals
                    hsrc hw hsource
                · exact evalExpr_frob_wish_w_true_can (evm := evm) (I := I) locals
                    hsrc hw hbase hsource (by rw [hcanLoad, hcan])
            | inr hsource =>
                exact evalExpr_frob_wish_w_true_src (evm := evm) (I := I) locals
                  hsrc hw hsource)

theorem frobAuthWSourceFalseCond_of_evm {I : ExecutionEnv} {wWish : UInt256}
    (h :
      UInt256.lor
        (UInt256.lor (UInt256.eq wWish ⟨1⟩)
          (UInt256.eq (frobWMaskedWord I) (hopeSourceWord I)))
        (UInt256.isZero (UInt256.slt (frobDartWord I) ⟨0⟩)) = ⟨0⟩) :
    ¬ 0 ≤ frobDartInt I ∧
      wWish ≠ ⟨1⟩ ∧ frobWMaskedWord I ≠ hopeSourceWord I := by
  constructor
  · intro hdartNonneg
    have hrightZero :
        UInt256.isZero (UInt256.slt (frobDartWord I) ⟨0⟩) = ⟨0⟩ :=
      u256_lor_eq_zero_right h
    have hsltZero : UInt256.slt (frobDartWord I) ⟨0⟩ = ⟨0⟩ := by
      by_contra hne
      have hneg : frobDartInt I < 0 :=
        slt_zero_ne_zero_to_neg (frobDartWord I) hne
      omega
    have hrightOne :
        UInt256.isZero (UInt256.slt (frobDartWord I) ⟨0⟩) = ⟨1⟩ := by
      rw [hsltZero]
      native_decide
    rw [hrightOne] at hrightZero
    exact one_ne_zero_uint hrightZero
  · constructor
    · intro hw
      have houterLeft :
          UInt256.lor (UInt256.eq wWish ⟨1⟩)
            (UInt256.eq (frobWMaskedWord I) (hopeSourceWord I)) = ⟨0⟩ :=
        u256_lor_eq_zero_left h
      have hcanZero : UInt256.eq wWish ⟨1⟩ = ⟨0⟩ :=
        u256_lor_eq_zero_left houterLeft
      have hcanOne : UInt256.eq wWish ⟨1⟩ = ⟨1⟩ := by
        rw [hw]
        rw [uInt256_eq_self]
      rw [hcanOne] at hcanZero
      exact one_ne_zero_uint hcanZero
    · intro hsrc
      have houterLeft :
          UInt256.lor (UInt256.eq wWish ⟨1⟩)
            (UInt256.eq (frobWMaskedWord I) (hopeSourceWord I)) = ⟨0⟩ :=
        u256_lor_eq_zero_left h
      have hsrcZero : UInt256.eq (frobWMaskedWord I) (hopeSourceWord I) = ⟨0⟩ :=
        u256_lor_eq_zero_right houterLeft
      have hsrcOne : UInt256.eq (frobWMaskedWord I) (hopeSourceWord I) = ⟨1⟩ := by
        rw [hsrc]
        rw [uInt256_eq_self]
      rw [hsrcOne] at hsrcZero
      exact one_ne_zero_uint hsrcZero

theorem evalExpr_frob_auth_w_req_false {evm : EVM.State} {I : ExecutionEnv}
    {locals : Store}
    (wWish : UInt256)
    (hdart : locals.get? "dart" = some (frobDartValue I))
    (hw : locals.get? "w" = some (frobWValue I))
    (hbase : locals.get? "can" = none)
    (hsrc : evm.executionEnv.source = I.source)
    (hcanLoad :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (frobWWishSlot I) = wWish)
    (hbad :
      ¬ 0 ≤ frobDartInt I ∧
        wWish ≠ ⟨1⟩ ∧ frobWMaskedWord I ≠ hopeSourceWord I) :
    evalExpr? config { contract := contract, locals := locals } evm
      (eitherExpr (.binary .ge (.var "dart") (.intLit 0)) (wishExpr (.var "w") sender)) =
      .ok (.bool false) := by
  have hdartEval :
      evalExpr? config { contract := contract, locals := locals } evm (.var "dart") =
        .ok (.int (frobDartInt I)) :=
    vatEvalExpr_varInt (by simpa [frobDartValue] using hdart)
  exact vatEvalExpr_or_false_right
    (vatEvalExpr_ge_int_false hdartEval (by simp [evalExpr?, pure])
      (lt_of_not_ge hbad.1))
    (evalExpr_frob_wish_w_false (evm := evm) (I := I) locals hsrc hw hbase hbad.2.2
      (by rw [hcanLoad]; exact hbad.2.1))

theorem frobDustSourceFalseCond_of_evm {urnArtNew tab ilkDust : UInt256}
    (h :
      UInt256.lor
        (UInt256.isZero (UInt256.lt tab ilkDust))
        (UInt256.eq ⟨0⟩ urnArtNew) = ⟨0⟩) :
    tab.toNat < ilkDust.toNat ∧ 0 < urnArtNew.toNat := by
  have hcomm :
      UInt256.lor
        (UInt256.eq ⟨0⟩ urnArtNew)
        (UInt256.isZero (UInt256.lt tab ilkDust)) = ⟨0⟩ := by
    simpa [u256_lor_comm] using h
  exact forkDustSourceCond_false_of_evm hcomm

theorem evalExpr_frob_dust_req_false {evm : EVM.State} {locals : Store}
    (urnArtNew tab ilkDust : UInt256)
    (hurnArtNew :
      locals.get? "urnArtNew" = some (.int (Int.ofNat urnArtNew.toNat)))
    (htab : locals.get? "tab" = some (.int (Int.ofNat tab.toNat)))
    (hilkDust : locals.get? "ilkDust" = some (.int (Int.ofNat ilkDust.toNat)))
    (hbad : tab.toNat < ilkDust.toNat ∧ 0 < urnArtNew.toNat) :
    evalExpr? config { contract := contract, locals := locals } evm
      (eitherExpr (.binary .eq (.var "urnArtNew") (.intLit 0))
        (.binary .ge (.var "tab") (.var "ilkDust"))) =
      .ok (.bool false) := by
  have hurnArtNewEval :
      evalExpr? config { contract := contract, locals := locals } evm (.var "urnArtNew") =
        .ok (.int (Int.ofNat urnArtNew.toNat)) :=
    vatEvalExpr_varUInt256 hurnArtNew
  have htabEval :
      evalExpr? config { contract := contract, locals := locals } evm (.var "tab") =
        .ok (.int (Int.ofNat tab.toNat)) :=
    vatEvalExpr_varUInt256 htab
  have hilkDustEval :
      evalExpr? config { contract := contract, locals := locals } evm (.var "ilkDust") =
        .ok (.int (Int.ofNat ilkDust.toNat)) :=
    vatEvalExpr_varUInt256 hilkDust
  exact vatEvalExpr_or_false_right
    (vatEvalExpr_eq_uint256_zero_false hurnArtNewEval hbad.2)
    (vatEvalExpr_ge_uint256_false htabEval hilkDustEval hbad.1)

theorem evalExpr_frob_ceiling_req_true {evm : EVM.State} {I : ExecutionEnv}
    {locals : Store}
    (ceilingDebt ilkLine debtNew Line : UInt256)
    (hdart : locals.get? "dart" = some (frobDartValue I))
    (hceilingDebt :
      locals.get? "ceilingDebt" = some (.int (Int.ofNat ceilingDebt.toNat)))
    (hilkLine : locals.get? "ilkLine" = some (.int (Int.ofNat ilkLine.toNat)))
    (hdebtNew : locals.get? "debtNew" = some (.int (Int.ofNat debtNew.toNat)))
    (hbaseLine : locals.get? "Line" = none)
    (hlineLoad : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨9⟩ = Line)
    (hok :
      frobDartInt I ≤ 0 ∨
        (ceilingDebt.toNat ≤ ilkLine.toNat ∧ debtNew.toNat ≤ Line.toNat)) :
    evalExpr? config { contract := contract, locals := locals } evm
      (eitherExpr
        (.binary .le (.var "dart") (.intLit 0))
        (bothExpr
          (.binary .le (.var "ceilingDebt") (.var "ilkLine"))
          (.binary .le (.var "debtNew") (.storage LineRef)))) =
      .ok (.bool true) := by
  have hdartEval :
      evalExpr? config { contract := contract, locals := locals } evm (.var "dart") =
        .ok (.int (frobDartInt I)) :=
    vatEvalExpr_varInt (by simpa [frobDartValue] using hdart)
  have hceilingEval :
      evalExpr? config { contract := contract, locals := locals } evm (.var "ceilingDebt") =
        .ok (.int (Int.ofNat ceilingDebt.toNat)) :=
    vatEvalExpr_varUInt256 hceilingDebt
  have hilkLineEval :
      evalExpr? config { contract := contract, locals := locals } evm (.var "ilkLine") =
        .ok (.int (Int.ofNat ilkLine.toNat)) :=
    vatEvalExpr_varUInt256 hilkLine
  have hdebtNewEval :
      evalExpr? config { contract := contract, locals := locals } evm (.var "debtNew") =
        .ok (.int (Int.ofNat debtNew.toNat)) :=
    vatEvalExpr_varUInt256 hdebtNew
  have hLineEval :
      evalExpr? config { contract := contract, locals := locals } evm (.storage LineRef) =
        .ok (.int (Int.ofNat Line.toNat)) := by
    rw [evalExpr_frob_LineRef hbaseLine, hlineLoad]
  cases hok with
  | inl hdartNonpos =>
      have hleft :
          evalExpr? config { contract := contract, locals := locals } evm
            (.binary .le (.var "dart") (.intLit 0)) = .ok (.bool true) :=
        vatEvalExpr_le_int_true hdartEval (by simp [evalExpr?, pure]) hdartNonpos
      exact vatEvalExpr_or_true_left hleft
  | inr hboth =>
      by_cases hdartNonpos : frobDartInt I ≤ 0
      · have hleft :
            evalExpr? config { contract := contract, locals := locals } evm
              (.binary .le (.var "dart") (.intLit 0)) = .ok (.bool true) :=
          vatEvalExpr_le_int_true hdartEval (by simp [evalExpr?, pure]) hdartNonpos
        exact vatEvalExpr_or_true_left hleft
      · have hleft :
            evalExpr? config { contract := contract, locals := locals } evm
              (.binary .le (.var "dart") (.intLit 0)) = .ok (.bool false) :=
          vatEvalExpr_le_int_false hdartEval (by simp [evalExpr?, pure])
            (lt_of_not_ge hdartNonpos)
        have hright :
            evalExpr? config { contract := contract, locals := locals } evm
              (bothExpr
                (.binary .le (.var "ceilingDebt") (.var "ilkLine"))
                (.binary .le (.var "debtNew") (.storage LineRef))) =
            .ok (.bool true) := by
          exact vatEvalExpr_and_true
            (vatEvalExpr_le_uint256_true hceilingEval hilkLineEval hboth.1)
            (vatEvalExpr_le_uint256_true hdebtNewEval hLineEval hboth.2)
        exact vatEvalExpr_or_false_right hleft hright

theorem evalExpr_frob_ceiling_req_false {evm : EVM.State} {I : ExecutionEnv}
    {locals : Store}
    (ceilingDebt ilkLine debtNew Line : UInt256)
    (hdart : locals.get? "dart" = some (frobDartValue I))
    (hceilingDebt :
      locals.get? "ceilingDebt" = some (.int (Int.ofNat ceilingDebt.toNat)))
    (hilkLine : locals.get? "ilkLine" = some (.int (Int.ofNat ilkLine.toNat)))
    (hdebtNew : locals.get? "debtNew" = some (.int (Int.ofNat debtNew.toNat)))
    (hbaseLine : locals.get? "Line" = none)
    (hlineLoad : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨9⟩ = Line)
    (hdartPos : 0 < frobDartInt I)
    (hbad :
      ¬ (ceilingDebt.toNat ≤ ilkLine.toNat ∧ debtNew.toNat ≤ Line.toNat)) :
    evalExpr? config { contract := contract, locals := locals } evm
      (eitherExpr
        (.binary .le (.var "dart") (.intLit 0))
        (bothExpr
          (.binary .le (.var "ceilingDebt") (.var "ilkLine"))
          (.binary .le (.var "debtNew") (.storage LineRef)))) =
      .ok (.bool false) := by
  have hdartEval :
      evalExpr? config { contract := contract, locals := locals } evm (.var "dart") =
        .ok (.int (frobDartInt I)) :=
    vatEvalExpr_varInt (by simpa [frobDartValue] using hdart)
  have hceilingEval :
      evalExpr? config { contract := contract, locals := locals } evm (.var "ceilingDebt") =
        .ok (.int (Int.ofNat ceilingDebt.toNat)) :=
    vatEvalExpr_varUInt256 hceilingDebt
  have hilkLineEval :
      evalExpr? config { contract := contract, locals := locals } evm (.var "ilkLine") =
        .ok (.int (Int.ofNat ilkLine.toNat)) :=
    vatEvalExpr_varUInt256 hilkLine
  have hdebtNewEval :
      evalExpr? config { contract := contract, locals := locals } evm (.var "debtNew") =
        .ok (.int (Int.ofNat debtNew.toNat)) :=
    vatEvalExpr_varUInt256 hdebtNew
  have hLineEval :
      evalExpr? config { contract := contract, locals := locals } evm (.storage LineRef) =
        .ok (.int (Int.ofNat Line.toNat)) := by
    rw [evalExpr_frob_LineRef hbaseLine, hlineLoad]
  have hleft :
      evalExpr? config { contract := contract, locals := locals } evm
        (.binary .le (.var "dart") (.intLit 0)) = .ok (.bool false) :=
    vatEvalExpr_le_int_false hdartEval (by simp [evalExpr?, pure]) hdartPos
  have hright :
      evalExpr? config { contract := contract, locals := locals } evm
        (bothExpr
          (.binary .le (.var "ceilingDebt") (.var "ilkLine"))
          (.binary .le (.var "debtNew") (.storage LineRef))) =
      .ok (.bool false) := by
    by_cases hceilLe : ceilingDebt.toNat ≤ ilkLine.toNat
    · have hdebtGt : Line.toNat < debtNew.toNat := by
        have hnot : ¬ debtNew.toNat ≤ Line.toNat := by
          intro hdebtLe
          exact hbad ⟨hceilLe, hdebtLe⟩
        exact Nat.lt_of_not_ge hnot
      exact vatEvalExpr_and_true_false_right
        (vatEvalExpr_le_uint256_true hceilingEval hilkLineEval hceilLe)
        (vatEvalExpr_le_uint256_false hdebtNewEval hLineEval hdebtGt)
    · have hceilGt : ilkLine.toNat < ceilingDebt.toNat := Nat.lt_of_not_ge hceilLe
      exact vatEvalExpr_and_false_left
        (vatEvalExpr_le_uint256_false hceilingEval hilkLineEval hceilGt)
  exact vatEvalExpr_or_false_right hleft hright

theorem evalExpr_frob_safety_req_true {evm : EVM.State} {I : ExecutionEnv}
    {locals : Store}
    (tab inkSpot : UInt256)
    (hdart : locals.get? "dart" = some (frobDartValue I))
    (hdink : locals.get? "dink" = some (frobDinkValue I))
    (htab : locals.get? "tab" = some (.int (Int.ofNat tab.toNat)))
    (hinkSpot : locals.get? "inkSpot" = some (.int (Int.ofNat inkSpot.toNat)))
    (hok :
      (frobDartInt I ≤ 0 ∧ 0 ≤ frobDinkInt I) ∨ tab.toNat ≤ inkSpot.toNat) :
    evalExpr? config { contract := contract, locals := locals } evm
      (eitherExpr
        (bothExpr
          (.binary .le (.var "dart") (.intLit 0))
          (.binary .ge (.var "dink") (.intLit 0)))
        (.binary .le (.var "tab") (.var "inkSpot"))) =
      .ok (.bool true) := by
  have hdartEval :
      evalExpr? config { contract := contract, locals := locals } evm (.var "dart") =
        .ok (.int (frobDartInt I)) :=
    vatEvalExpr_varInt (by simpa [frobDartValue] using hdart)
  have hdinkEval :
      evalExpr? config { contract := contract, locals := locals } evm (.var "dink") =
        .ok (.int (frobDinkInt I)) :=
    vatEvalExpr_varInt (by simpa [frobDinkValue] using hdink)
  have htabEval :
      evalExpr? config { contract := contract, locals := locals } evm (.var "tab") =
        .ok (.int (Int.ofNat tab.toNat)) :=
    vatEvalExpr_varUInt256 htab
  have hinkSpotEval :
      evalExpr? config { contract := contract, locals := locals } evm (.var "inkSpot") =
        .ok (.int (Int.ofNat inkSpot.toNat)) :=
    vatEvalExpr_varUInt256 hinkSpot
  cases hok with
  | inl hboth =>
      have hleft :
          evalExpr? config { contract := contract, locals := locals } evm
            (bothExpr
              (.binary .le (.var "dart") (.intLit 0))
              (.binary .ge (.var "dink") (.intLit 0))) =
          .ok (.bool true) := by
        exact vatEvalExpr_and_true
          (vatEvalExpr_le_int_true hdartEval (by simp [evalExpr?, pure]) hboth.1)
          (vatEvalExpr_ge_int_true hdinkEval (by simp [evalExpr?, pure]) hboth.2)
      exact vatEvalExpr_or_true_left hleft
  | inr hle =>
      by_cases hleftOk : frobDartInt I ≤ 0 ∧ 0 ≤ frobDinkInt I
      · have hleft :
            evalExpr? config { contract := contract, locals := locals } evm
              (bothExpr
                (.binary .le (.var "dart") (.intLit 0))
                (.binary .ge (.var "dink") (.intLit 0))) =
            .ok (.bool true) := by
          exact vatEvalExpr_and_true
            (vatEvalExpr_le_int_true hdartEval (by simp [evalExpr?, pure]) hleftOk.1)
            (vatEvalExpr_ge_int_true hdinkEval (by simp [evalExpr?, pure]) hleftOk.2)
        exact vatEvalExpr_or_true_left hleft
      · have hleft :
            evalExpr? config { contract := contract, locals := locals } evm
              (bothExpr
                (.binary .le (.var "dart") (.intLit 0))
                (.binary .ge (.var "dink") (.intLit 0))) =
            .ok (.bool false) := by
          by_cases hdartNonpos : frobDartInt I ≤ 0
          · have hdinkNeg : frobDinkInt I < 0 := by omega
            exact vatEvalExpr_and_true_false_right
              (vatEvalExpr_le_int_true hdartEval (by simp [evalExpr?, pure]) hdartNonpos)
              (vatEvalExpr_ge_int_false hdinkEval (by simp [evalExpr?, pure]) hdinkNeg)
          · exact vatEvalExpr_and_false_left
              (vatEvalExpr_le_int_false hdartEval (by simp [evalExpr?, pure])
                (lt_of_not_ge hdartNonpos))
        exact vatEvalExpr_or_false_right hleft
          (vatEvalExpr_le_uint256_true htabEval hinkSpotEval hle)

theorem evalExpr_frob_safety_req_false {evm : EVM.State} {I : ExecutionEnv}
    {locals : Store}
    (tab inkSpot : UInt256)
    (hdart : locals.get? "dart" = some (frobDartValue I))
    (hdink : locals.get? "dink" = some (frobDinkValue I))
    (htab : locals.get? "tab" = some (.int (Int.ofNat tab.toNat)))
    (hinkSpot : locals.get? "inkSpot" = some (.int (Int.ofNat inkSpot.toNat)))
    (hleftBad : ¬ (frobDartInt I ≤ 0 ∧ 0 ≤ frobDinkInt I))
    (htabGt : inkSpot.toNat < tab.toNat) :
    evalExpr? config { contract := contract, locals := locals } evm
      (eitherExpr
        (bothExpr
          (.binary .le (.var "dart") (.intLit 0))
          (.binary .ge (.var "dink") (.intLit 0)))
        (.binary .le (.var "tab") (.var "inkSpot"))) =
      .ok (.bool false) := by
  have hdartEval :
      evalExpr? config { contract := contract, locals := locals } evm (.var "dart") =
        .ok (.int (frobDartInt I)) :=
    vatEvalExpr_varInt (by simpa [frobDartValue] using hdart)
  have hdinkEval :
      evalExpr? config { contract := contract, locals := locals } evm (.var "dink") =
        .ok (.int (frobDinkInt I)) :=
    vatEvalExpr_varInt (by simpa [frobDinkValue] using hdink)
  have htabEval :
      evalExpr? config { contract := contract, locals := locals } evm (.var "tab") =
        .ok (.int (Int.ofNat tab.toNat)) :=
    vatEvalExpr_varUInt256 htab
  have hinkSpotEval :
      evalExpr? config { contract := contract, locals := locals } evm (.var "inkSpot") =
        .ok (.int (Int.ofNat inkSpot.toNat)) :=
    vatEvalExpr_varUInt256 hinkSpot
  have hleft :
      evalExpr? config { contract := contract, locals := locals } evm
        (bothExpr
          (.binary .le (.var "dart") (.intLit 0))
          (.binary .ge (.var "dink") (.intLit 0))) =
      .ok (.bool false) := by
    by_cases hdartNonpos : frobDartInt I ≤ 0
    · have hdinkNeg : frobDinkInt I < 0 := by
        have hdinkNot : ¬ 0 ≤ frobDinkInt I := by
          intro hdinkNonneg
          exact hleftBad ⟨hdartNonpos, hdinkNonneg⟩
        exact lt_of_not_ge hdinkNot
      exact vatEvalExpr_and_true_false_right
        (vatEvalExpr_le_int_true hdartEval (by simp [evalExpr?, pure]) hdartNonpos)
        (vatEvalExpr_ge_int_false hdinkEval (by simp [evalExpr?, pure]) hdinkNeg)
    · exact vatEvalExpr_and_false_left
        (vatEvalExpr_le_int_false hdartEval (by simp [evalExpr?, pure])
          (lt_of_not_ge hdartNonpos))
  exact vatEvalExpr_or_false_right hleft
    (vatEvalExpr_le_uint256_false htabEval hinkSpotEval htabGt)

theorem vatFrobSourceBodyRateZero {cA gh bl σ σ₀ A I} {g : UInt256}
    {urnInk urnArt ilkArt ilkRate ilkSpot ilkLine ilkDust : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hsz196 : 196 ≤ I.calldata.size)
    (hlive : vatSlotWord ⟨10⟩ σ I = ⟨1⟩)
    (hloadUrnInk :
      Solm.EVM.storageLoad
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
        (frobUrnInkSourceSlot I) = urnInk)
    (hloadUrnArt :
      Solm.EVM.storageLoad
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
        (frobUrnArtSourceSlot I) = urnArt)
    (hloadIlkArt :
      Solm.EVM.storageLoad
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
        (frobIlkArtSourceSlot I) = ilkArt)
    (hloadIlkRate :
      Solm.EVM.storageLoad
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
        (frobIlkRateSourceSlot I) = ilkRate)
    (hloadIlkSpot :
      Solm.EVM.storageLoad
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
        (frobIlkSpotSourceSlot I) = ilkSpot)
    (hloadIlkLine :
      Solm.EVM.storageLoad
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
        (frobIlkLineSourceSlot I) = ilkLine)
    (hloadIlkDust :
      Solm.EVM.storageLoad
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
        (frobIlkDustSourceSlot I) = ilkDust)
    (hrateZero : ilkRate.toNat = 0) :
    let locals := frobStore I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 locals frobTransition.body .reverted := by
  intro locals evm0
  have hguardLive := vatLiveGuardEval_true (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := Sat256.ofUInt256 g) (locals := locals)
    (by change (frobStore I).get? "live" = none; exact frobStore_get_live I)
    hlive
  have hurnInk :
      evalExpr? config { contract := contract, locals := frobStore I } evm0
        (.storage (urnsF (.var "i") (.var "u") "ink")) =
        .ok (.int (Int.ofNat urnInk.toNat)) := by
    rw [evalExpr_frob_urn_ink_locals (evm := evm0) (I := I) (frobStore I)
      hsz196 (frobStore_get_i I) (frobStore_get_u I) (frobStore_urns I)]
    simpa [evm0] using congrArg
      (fun w : UInt256 => (.ok (.int (Int.ofNat w.toNat)) : EvalResult Value)) hloadUrnInk
  have hurnArt :
      evalExpr? config { contract := contract, locals := frobStoreUrnInk I urnInk } evm0
        (.storage (urnsF (.var "i") (.var "u") "art")) =
        .ok (.int (Int.ofNat urnArt.toNat)) := by
    rw [evalExpr_frob_urn_art_locals (evm := evm0) (I := I)
      (frobStoreUrnInk I urnInk) hsz196 (frobStoreUrnInk_get_i I urnInk)
      (frobStoreUrnInk_get_u I urnInk) (frobStoreUrnInk_urns I urnInk)]
    simpa [evm0] using congrArg
      (fun w : UInt256 => (.ok (.int (Int.ofNat w.toNat)) : EvalResult Value)) hloadUrnArt
  have hilkArt :
      evalExpr? config { contract := contract, locals := frobStoreUrnArt I urnInk urnArt }
        evm0 (.storage (ilksF (.var "i") "Art")) =
        .ok (.int (Int.ofNat ilkArt.toNat)) := by
    rw [evalExpr_frob_ilk_art_locals (evm := evm0) (I := I)
      (frobStoreUrnArt I urnInk urnArt) hsz196
      (frobStoreUrnArt_get_i I urnInk urnArt) (frobStoreUrnArt_ilks I urnInk urnArt)]
    simpa [evm0] using congrArg
      (fun w : UInt256 => (.ok (.int (Int.ofNat w.toNat)) : EvalResult Value)) hloadIlkArt
  have hilkRate :
      evalExpr? config
        { contract := contract, locals := frobStoreIlkArt I urnInk urnArt ilkArt } evm0
        (.storage (ilksF (.var "i") "rate")) =
        .ok (.int (Int.ofNat ilkRate.toNat)) := by
    rw [evalExpr_frob_ilk_rate_locals (evm := evm0) (I := I)
      (frobStoreIlkArt I urnInk urnArt ilkArt) hsz196
      (frobStoreIlkArt_get_i I urnInk urnArt ilkArt)
      (frobStoreIlkArt_ilks I urnInk urnArt ilkArt)]
    simpa [evm0] using congrArg
      (fun w : UInt256 => (.ok (.int (Int.ofNat w.toNat)) : EvalResult Value)) hloadIlkRate
  have hilkSpot :
      evalExpr? config
        { contract := contract, locals := frobStoreIlkRate I urnInk urnArt ilkArt ilkRate }
        evm0 (.storage (ilksF (.var "i") "spot")) =
        .ok (.int (Int.ofNat ilkSpot.toNat)) := by
    rw [evalExpr_frob_ilk_spot_locals (evm := evm0) (I := I)
      (frobStoreIlkRate I urnInk urnArt ilkArt ilkRate) hsz196
      (frobStoreIlkRate_get_i I urnInk urnArt ilkArt ilkRate)
      (frobStoreIlkRate_ilks I urnInk urnArt ilkArt ilkRate)]
    simpa [evm0] using congrArg
      (fun w : UInt256 => (.ok (.int (Int.ofNat w.toNat)) : EvalResult Value)) hloadIlkSpot
  have hilkLine :
      evalExpr? config
        { contract := contract,
          locals := frobStoreIlkSpot I urnInk urnArt ilkArt ilkRate ilkSpot } evm0
        (.storage (ilksF (.var "i") "line")) =
        .ok (.int (Int.ofNat ilkLine.toNat)) := by
    rw [evalExpr_frob_ilk_line_locals (evm := evm0) (I := I)
      (frobStoreIlkSpot I urnInk urnArt ilkArt ilkRate ilkSpot) hsz196
      (frobStoreIlkSpot_get_i I urnInk urnArt ilkArt ilkRate ilkSpot)
      (frobStoreIlkSpot_ilks I urnInk urnArt ilkArt ilkRate ilkSpot)]
    simpa [evm0] using congrArg
      (fun w : UInt256 => (.ok (.int (Int.ofNat w.toNat)) : EvalResult Value)) hloadIlkLine
  have hilkDust :
      evalExpr? config
        { contract := contract,
          locals := frobStoreIlkLine I urnInk urnArt ilkArt ilkRate ilkSpot ilkLine } evm0
        (.storage (ilksF (.var "i") "dust")) =
        .ok (.int (Int.ofNat ilkDust.toNat)) := by
    rw [evalExpr_frob_ilk_dust_locals (evm := evm0) (I := I)
      (frobStoreIlkLine I urnInk urnArt ilkArt ilkRate ilkSpot ilkLine) hsz196
      (frobStoreIlkLine_get_i I urnInk urnArt ilkArt ilkRate ilkSpot ilkLine)
      (frobStoreIlkLine_ilks I urnInk urnArt ilkArt ilkRate ilkSpot ilkLine)]
    simpa [evm0] using congrArg
      (fun w : UInt256 => (.ok (.int (Int.ofNat w.toNat)) : EvalResult Value)) hloadIlkDust
  have hrateGuard :
      evalExpr? config
        { contract := contract,
          locals := frobStoreIlkDust I urnInk urnArt ilkArt ilkRate ilkSpot ilkLine ilkDust }
        evm0 (.binary .ne (.var "ilkRate") (.intLit 0)) = .ok (.bool false) := by
    exact vatEvalExpr_ne_uint256_zero_false
      (vatEvalExpr_varUInt256
        (frobStoreIlkDust_get_rate I urnInk urnArt ilkArt ilkRate ilkSpot ilkLine ilkDust))
      hrateZero
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0 frobTransition.body
        .reverted := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguardLive) ?_
    refine ExecBlock.consNormal (ExecStmt.letDecl hurnInk) ?_
    refine ExecBlock.consNormal (ExecStmt.letDecl hurnArt) ?_
    refine ExecBlock.consNormal (ExecStmt.letDecl hilkArt) ?_
    refine ExecBlock.consNormal (ExecStmt.letDecl hilkRate) ?_
    refine ExecBlock.consNormal (ExecStmt.letDecl hilkSpot) ?_
    refine ExecBlock.consNormal (ExecStmt.letDecl hilkLine) ?_
    refine ExecBlock.consNormal (ExecStmt.letDecl hilkDust) ?_
    exact ExecBlock.consRevert (ExecStmt.requireFalse hrateGuard)
  simpa [ExecTransitionBody, frobTransition, nonpayable, requireLive, evm0, locals] using
    ExecFuncBody.execBlockRevert hblock

theorem vatFrobSourceRateNonzeroPrefix {cA gh bl σ σ₀ A I} {g : UInt256}
    {urnInk urnArt ilkArt ilkRate ilkSpot ilkLine ilkDust : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hsz196 : 196 ≤ I.calldata.size)
    (hlive : vatSlotWord ⟨10⟩ σ I = ⟨1⟩)
    (hloadUrnInk :
      Solm.EVM.storageLoad
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
        (frobUrnInkSourceSlot I) = urnInk)
    (hloadUrnArt :
      Solm.EVM.storageLoad
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
        (frobUrnArtSourceSlot I) = urnArt)
    (hloadIlkArt :
      Solm.EVM.storageLoad
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
        (frobIlkArtSourceSlot I) = ilkArt)
    (hloadIlkRate :
      Solm.EVM.storageLoad
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
        (frobIlkRateSourceSlot I) = ilkRate)
    (hloadIlkSpot :
      Solm.EVM.storageLoad
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
        (frobIlkSpotSourceSlot I) = ilkSpot)
    (hloadIlkLine :
      Solm.EVM.storageLoad
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
        (frobIlkLineSourceSlot I) = ilkLine)
    (hloadIlkDust :
      Solm.EVM.storageLoad
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
        (frobIlkDustSourceSlot I) = ilkDust)
    (hratePos : 0 < ilkRate.toNat) :
    let locals := frobStore I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecBlock config { contract := contract, locals := locals } evm0
      (nonpayable ++ requireLive ++
        [ .letDecl "urnInk" (some uint256) (.storage (urnsF (.var "i") (.var "u") "ink")),
          .letDecl "urnArt" (some uint256) (.storage (urnsF (.var "i") (.var "u") "art")),
          .letDecl "ilkArt" (some uint256) (.storage (ilksF (.var "i") "Art")),
          .letDecl "ilkRate" (some uint256) (.storage (ilksF (.var "i") "rate")),
          .letDecl "ilkSpot" (some uint256) (.storage (ilksF (.var "i") "spot")),
          .letDecl "ilkLine" (some uint256) (.storage (ilksF (.var "i") "line")),
          .letDecl "ilkDust" (some uint256) (.storage (ilksF (.var "i") "dust")),
          .require (.binary .ne (.var "ilkRate") (.intLit 0)) ])
      (.ok
        { contract := contract,
          locals := frobStoreIlkDust I urnInk urnArt ilkArt ilkRate ilkSpot ilkLine ilkDust }
        evm0) := by
  intro locals evm0
  have hguardLive := vatLiveGuardEval_true (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := Sat256.ofUInt256 g) (locals := locals)
    (by change (frobStore I).get? "live" = none; exact frobStore_get_live I)
    hlive
  have hurnInk :
      evalExpr? config { contract := contract, locals := frobStore I } evm0
        (.storage (urnsF (.var "i") (.var "u") "ink")) =
        .ok (.int (Int.ofNat urnInk.toNat)) := by
    rw [evalExpr_frob_urn_ink_locals (evm := evm0) (I := I) (frobStore I)
      hsz196 (frobStore_get_i I) (frobStore_get_u I) (frobStore_urns I)]
    simpa [evm0] using congrArg
      (fun w : UInt256 => (.ok (.int (Int.ofNat w.toNat)) : EvalResult Value)) hloadUrnInk
  have hurnArt :
      evalExpr? config { contract := contract, locals := frobStoreUrnInk I urnInk } evm0
        (.storage (urnsF (.var "i") (.var "u") "art")) =
        .ok (.int (Int.ofNat urnArt.toNat)) := by
    rw [evalExpr_frob_urn_art_locals (evm := evm0) (I := I)
      (frobStoreUrnInk I urnInk) hsz196 (frobStoreUrnInk_get_i I urnInk)
      (frobStoreUrnInk_get_u I urnInk) (frobStoreUrnInk_urns I urnInk)]
    simpa [evm0] using congrArg
      (fun w : UInt256 => (.ok (.int (Int.ofNat w.toNat)) : EvalResult Value)) hloadUrnArt
  have hilkArt :
      evalExpr? config { contract := contract, locals := frobStoreUrnArt I urnInk urnArt }
        evm0 (.storage (ilksF (.var "i") "Art")) =
        .ok (.int (Int.ofNat ilkArt.toNat)) := by
    rw [evalExpr_frob_ilk_art_locals (evm := evm0) (I := I)
      (frobStoreUrnArt I urnInk urnArt) hsz196
      (frobStoreUrnArt_get_i I urnInk urnArt) (frobStoreUrnArt_ilks I urnInk urnArt)]
    simpa [evm0] using congrArg
      (fun w : UInt256 => (.ok (.int (Int.ofNat w.toNat)) : EvalResult Value)) hloadIlkArt
  have hilkRate :
      evalExpr? config
        { contract := contract, locals := frobStoreIlkArt I urnInk urnArt ilkArt } evm0
        (.storage (ilksF (.var "i") "rate")) =
        .ok (.int (Int.ofNat ilkRate.toNat)) := by
    rw [evalExpr_frob_ilk_rate_locals (evm := evm0) (I := I)
      (frobStoreIlkArt I urnInk urnArt ilkArt) hsz196
      (frobStoreIlkArt_get_i I urnInk urnArt ilkArt)
      (frobStoreIlkArt_ilks I urnInk urnArt ilkArt)]
    simpa [evm0] using congrArg
      (fun w : UInt256 => (.ok (.int (Int.ofNat w.toNat)) : EvalResult Value)) hloadIlkRate
  have hilkSpot :
      evalExpr? config
        { contract := contract, locals := frobStoreIlkRate I urnInk urnArt ilkArt ilkRate }
        evm0 (.storage (ilksF (.var "i") "spot")) =
        .ok (.int (Int.ofNat ilkSpot.toNat)) := by
    rw [evalExpr_frob_ilk_spot_locals (evm := evm0) (I := I)
      (frobStoreIlkRate I urnInk urnArt ilkArt ilkRate) hsz196
      (frobStoreIlkRate_get_i I urnInk urnArt ilkArt ilkRate)
      (frobStoreIlkRate_ilks I urnInk urnArt ilkArt ilkRate)]
    simpa [evm0] using congrArg
      (fun w : UInt256 => (.ok (.int (Int.ofNat w.toNat)) : EvalResult Value)) hloadIlkSpot
  have hilkLine :
      evalExpr? config
        { contract := contract,
          locals := frobStoreIlkSpot I urnInk urnArt ilkArt ilkRate ilkSpot } evm0
        (.storage (ilksF (.var "i") "line")) =
        .ok (.int (Int.ofNat ilkLine.toNat)) := by
    rw [evalExpr_frob_ilk_line_locals (evm := evm0) (I := I)
      (frobStoreIlkSpot I urnInk urnArt ilkArt ilkRate ilkSpot) hsz196
      (frobStoreIlkSpot_get_i I urnInk urnArt ilkArt ilkRate ilkSpot)
      (frobStoreIlkSpot_ilks I urnInk urnArt ilkArt ilkRate ilkSpot)]
    simpa [evm0] using congrArg
      (fun w : UInt256 => (.ok (.int (Int.ofNat w.toNat)) : EvalResult Value)) hloadIlkLine
  have hilkDust :
      evalExpr? config
        { contract := contract,
          locals := frobStoreIlkLine I urnInk urnArt ilkArt ilkRate ilkSpot ilkLine } evm0
        (.storage (ilksF (.var "i") "dust")) =
        .ok (.int (Int.ofNat ilkDust.toNat)) := by
    rw [evalExpr_frob_ilk_dust_locals (evm := evm0) (I := I)
      (frobStoreIlkLine I urnInk urnArt ilkArt ilkRate ilkSpot ilkLine) hsz196
      (frobStoreIlkLine_get_i I urnInk urnArt ilkArt ilkRate ilkSpot ilkLine)
      (frobStoreIlkLine_ilks I urnInk urnArt ilkArt ilkRate ilkSpot ilkLine)]
    simpa [evm0] using congrArg
      (fun w : UInt256 => (.ok (.int (Int.ofNat w.toNat)) : EvalResult Value)) hloadIlkDust
  have hrateGuard :
      evalExpr? config
        { contract := contract,
          locals := frobStoreIlkDust I urnInk urnArt ilkArt ilkRate ilkSpot ilkLine ilkDust }
        evm0 (.binary .ne (.var "ilkRate") (.intLit 0)) = .ok (.bool true) := by
    exact vatEvalExpr_ne_uint256_zero_true
      (vatEvalExpr_varUInt256
        (frobStoreIlkDust_get_rate I urnInk urnArt ilkArt ilkRate ilkSpot ilkLine ilkDust))
      hratePos
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0
        [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
          .require (.binary .eq (.storage liveRef) (.intLit 1)),
          .letDecl "urnInk" (some uint256) (.storage (urnsF (.var "i") (.var "u") "ink")),
          .letDecl "urnArt" (some uint256) (.storage (urnsF (.var "i") (.var "u") "art")),
          .letDecl "ilkArt" (some uint256) (.storage (ilksF (.var "i") "Art")),
          .letDecl "ilkRate" (some uint256) (.storage (ilksF (.var "i") "rate")),
          .letDecl "ilkSpot" (some uint256) (.storage (ilksF (.var "i") "spot")),
          .letDecl "ilkLine" (some uint256) (.storage (ilksF (.var "i") "line")),
          .letDecl "ilkDust" (some uint256) (.storage (ilksF (.var "i") "dust")),
          .require (.binary .ne (.var "ilkRate") (.intLit 0)) ]
        (.ok
          { contract := contract,
            locals := frobStoreIlkDust I urnInk urnArt ilkArt ilkRate ilkSpot ilkLine ilkDust }
          evm0) := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguardLive) ?_
    refine ExecBlock.consNormal (ExecStmt.letDecl hurnInk) ?_
    refine ExecBlock.consNormal (ExecStmt.letDecl hurnArt) ?_
    refine ExecBlock.consNormal (ExecStmt.letDecl hilkArt) ?_
    refine ExecBlock.consNormal (ExecStmt.letDecl hilkRate) ?_
    refine ExecBlock.consNormal (ExecStmt.letDecl hilkSpot) ?_
    refine ExecBlock.consNormal (ExecStmt.letDecl hilkLine) ?_
    refine ExecBlock.consNormal (ExecStmt.letDecl hilkDust) ?_
    exact ExecBlock.consNormal (ExecStmt.requireTrue hrateGuard) ExecBlock.nil
  simpa [nonpayable, requireLive, locals] using hblock

theorem execFrobUrnInkAddOk {evm : EVM.State} {I : ExecutionEnv}
    (locals : Store) (urnInk urnInkNew : UInt256)
    (hurnInk : locals.get? "urnInk" = some (.int (Int.ofNat urnInk.toNat)))
    (hdink : locals.get? "dink" = some (frobDinkValue I))
    (hnew : urnInkNew = frobDinkWord I + urnInk)
    (hguardNeg : 0 ≤ frobDinkInt I ∨ urnInkNew.toNat ≤ urnInk.toNat)
    (hguardPos : frobDinkInt I ≤ 0 ∨ urnInk.toNat ≤ urnInkNew.toNat) :
    ExecBlock config { contract := contract, locals := locals } evm
      (checkedAddSignedInto "urnInkNew" (.var "urnInk") (.var "dink"))
      (.ok
        { contract := contract,
          locals := locals.insert "urnInkNew" (.int (Int.ofNat urnInkNew.toNat)) }
        evm) := by
  let locals' := locals.insert "urnInkNew" (.int (Int.ofNat urnInkNew.toNat))
  have hurnInkEval :
      evalExpr? config { contract := contract, locals := locals } evm (.var "urnInk") =
        .ok (.int (Int.ofNat urnInk.toNat)) :=
    vatEvalExpr_varUInt256 hurnInk
  have hdinkEval :
      evalExpr? config { contract := contract, locals := locals } evm (.var "dink") =
        .ok (.int (frobDinkInt I)) :=
    vatEvalExpr_varInt (by simpa [frobDinkValue] using hdink)
  have hlet :
      evalExpr? config { contract := contract, locals := locals } evm
        (wordWrap256 (.binary .add (.var "urnInk") (.var "dink"))) =
        .ok (.int (Int.ofNat urnInkNew.toNat)) := by
    exact evalExpr_fold_wordWrapAdd_ok hurnInkEval hdinkEval (frobDinkInt_mod_word I) hnew
  have hnewEval :
      evalExpr? config { contract := contract, locals := locals' } evm (.var "urnInkNew") =
        .ok (.int (Int.ofNat urnInkNew.toNat)) := by
    exact vatEvalExpr_varUInt256 (by simp [locals'])
  have hdinkAfter :
      evalExpr? config { contract := contract, locals := locals' } evm (.var "dink") =
        .ok (.int (frobDinkInt I)) := by
    exact vatEvalExpr_varInt (by
      change (locals.insert "urnInkNew" (.int (Int.ofNat urnInkNew.toNat))).get? "dink" =
        some (.int (frobDinkInt I))
      rw [store_get_ne _ _ (by decide)]
      simpa [frobDinkValue] using hdink)
  have hurnInkAfter :
      evalExpr? config { contract := contract, locals := locals' } evm (.var "urnInk") =
        .ok (.int (Int.ofNat urnInk.toNat)) := by
    exact vatEvalExpr_varUInt256 (by
      change (locals.insert "urnInkNew" (.int (Int.ofNat urnInkNew.toNat))).get? "urnInk" =
        some (.int (Int.ofNat urnInk.toNat))
      rw [store_get_ne _ _ (by decide)]
      exact hurnInk)
  have hguardNegEval :
      evalExpr? config { contract := contract, locals := locals' } evm
        (eitherExpr (.binary .ge (.var "dink") (.intLit 0))
          (.binary .le (.var "urnInkNew") (.var "urnInk"))) =
        .ok (.bool true) :=
    evalSignedAddGuardNeg_true hdinkAfter hnewEval hurnInkAfter hguardNeg
  have hguardPosEval :
      evalExpr? config { contract := contract, locals := locals' } evm
        (eitherExpr (.binary .le (.var "dink") (.intLit 0))
          (.binary .ge (.var "urnInkNew") (.var "urnInk"))) =
        .ok (.bool true) :=
    evalSignedAddGuardPos_true hdinkAfter hnewEval hurnInkAfter hguardPos
  change ExecBlock config { contract := contract, locals := locals } evm
    [ .letDecl "urnInkNew" (some uint256)
        (wordWrap256 (.binary .add (.var "urnInk") (.var "dink"))),
      .require
        (eitherExpr (.binary .ge (.var "dink") (.intLit 0))
          (.binary .le (.var "urnInkNew") (.var "urnInk"))),
      .require
        (eitherExpr (.binary .le (.var "dink") (.intLit 0))
          (.binary .ge (.var "urnInkNew") (.var "urnInk"))) ]
    (.ok { contract := contract, locals := locals' } evm)
  refine ExecBlock.consNormal (ExecStmt.letDecl hlet) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue hguardNegEval) ?_
  exact ExecBlock.consNormal (ExecStmt.requireTrue hguardPosEval) ExecBlock.nil

theorem execFrobCheckedAddVarOk {evm : EVM.State}
    (locals : Store) (name oldName addName : Ident)
    (old new addWord : UInt256) (addInt : Int)
    (hnameOld : (name == oldName) = false)
    (hnameAdd : (name == addName) = false)
    (hold : locals.get? oldName = some (.int (Int.ofNat old.toNat)))
    (hadd : locals.get? addName = some (.int addInt))
    (haddMod : addInt % (Int.ofNat EVM.wordModulus) = Int.ofNat addWord.toNat)
    (hnew : new = addWord + old)
    (hguardNeg : 0 ≤ addInt ∨ new.toNat ≤ old.toNat)
    (hguardPos : addInt ≤ 0 ∨ old.toNat ≤ new.toNat) :
    ExecBlock config { contract := contract, locals := locals } evm
      (checkedAddSignedInto name (.var oldName) (.var addName))
      (.ok
        { contract := contract,
          locals := locals.insert name (.int (Int.ofNat new.toNat)) }
        evm) := by
  let locals' := locals.insert name (.int (Int.ofNat new.toNat))
  have holdEval :
      evalExpr? config { contract := contract, locals := locals } evm (.var oldName) =
        .ok (.int (Int.ofNat old.toNat)) :=
    vatEvalExpr_varUInt256 hold
  have haddEval :
      evalExpr? config { contract := contract, locals := locals } evm (.var addName) =
        .ok (.int addInt) :=
    vatEvalExpr_varInt hadd
  have hlet :
      evalExpr? config { contract := contract, locals := locals } evm
        (wordWrap256 (.binary .add (.var oldName) (.var addName))) =
        .ok (.int (Int.ofNat new.toNat)) := by
    exact evalExpr_fold_wordWrapAdd_ok holdEval haddEval haddMod hnew
  have hnewEval :
      evalExpr? config { contract := contract, locals := locals' } evm (.var name) =
        .ok (.int (Int.ofNat new.toNat)) := by
    exact vatEvalExpr_varUInt256 (by simp [locals'])
  have haddAfter :
      evalExpr? config { contract := contract, locals := locals' } evm (.var addName) =
        .ok (.int addInt) := by
    exact vatEvalExpr_varInt (by
      change (locals.insert name (.int (Int.ofNat new.toNat))).get? addName =
        some (.int addInt)
      rw [store_get_ne _ _ hnameAdd]
      exact hadd)
  have holdAfter :
      evalExpr? config { contract := contract, locals := locals' } evm (.var oldName) =
        .ok (.int (Int.ofNat old.toNat)) := by
    exact vatEvalExpr_varUInt256 (by
      change (locals.insert name (.int (Int.ofNat new.toNat))).get? oldName =
        some (.int (Int.ofNat old.toNat))
      rw [store_get_ne _ _ hnameOld]
      exact hold)
  have hguardNegEval :
      evalExpr? config { contract := contract, locals := locals' } evm
        (eitherExpr (.binary .ge (.var addName) (.intLit 0))
          (.binary .le (.var name) (.var oldName))) =
        .ok (.bool true) :=
    evalSignedAddGuardNeg_true haddAfter hnewEval holdAfter hguardNeg
  have hguardPosEval :
      evalExpr? config { contract := contract, locals := locals' } evm
        (eitherExpr (.binary .le (.var addName) (.intLit 0))
          (.binary .ge (.var name) (.var oldName))) =
        .ok (.bool true) :=
    evalSignedAddGuardPos_true haddAfter hnewEval holdAfter hguardPos
  change ExecBlock config { contract := contract, locals := locals } evm
    [ .letDecl name (some uint256)
        (wordWrap256 (.binary .add (.var oldName) (.var addName))),
      .require
        (eitherExpr (.binary .ge (.var addName) (.intLit 0))
          (.binary .le (.var name) (.var oldName))),
      .require
        (eitherExpr (.binary .le (.var addName) (.intLit 0))
          (.binary .ge (.var name) (.var oldName))) ]
    (.ok { contract := contract, locals := locals' } evm)
  refine ExecBlock.consNormal (ExecStmt.letDecl hlet) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue hguardNegEval) ?_
  exact ExecBlock.consNormal (ExecStmt.requireTrue hguardPosEval) ExecBlock.nil

theorem execFrobCheckedAddVarRevertGuardNeg {evm : EVM.State}
    (locals : Store) (name oldName addName : Ident)
    (old new addWord : UInt256) (addInt : Int)
    (hnameOld : (name == oldName) = false)
    (hnameAdd : (name == addName) = false)
    (hold : locals.get? oldName = some (.int (Int.ofNat old.toNat)))
    (hadd : locals.get? addName = some (.int addInt))
    (haddMod : addInt % (Int.ofNat EVM.wordModulus) = Int.ofNat addWord.toNat)
    (hnew : new = addWord + old)
    (hcond : addInt < 0 ∧ old.toNat < new.toNat) :
    ExecBlock config { contract := contract, locals := locals } evm
      (checkedAddSignedInto name (.var oldName) (.var addName))
      .reverted := by
  let locals' := locals.insert name (.int (Int.ofNat new.toNat))
  have holdEval :
      evalExpr? config { contract := contract, locals := locals } evm (.var oldName) =
        .ok (.int (Int.ofNat old.toNat)) :=
    vatEvalExpr_varUInt256 hold
  have haddEval :
      evalExpr? config { contract := contract, locals := locals } evm (.var addName) =
        .ok (.int addInt) :=
    vatEvalExpr_varInt hadd
  have hlet :
      evalExpr? config { contract := contract, locals := locals } evm
        (wordWrap256 (.binary .add (.var oldName) (.var addName))) =
        .ok (.int (Int.ofNat new.toNat)) := by
    exact evalExpr_fold_wordWrapAdd_ok holdEval haddEval haddMod hnew
  have hnewEval :
      evalExpr? config { contract := contract, locals := locals' } evm (.var name) =
        .ok (.int (Int.ofNat new.toNat)) := by
    exact vatEvalExpr_varUInt256 (by simp [locals'])
  have haddAfter :
      evalExpr? config { contract := contract, locals := locals' } evm (.var addName) =
        .ok (.int addInt) := by
    exact vatEvalExpr_varInt (by
      change (locals.insert name (.int (Int.ofNat new.toNat))).get? addName =
        some (.int addInt)
      rw [store_get_ne _ _ hnameAdd]
      exact hadd)
  have holdAfter :
      evalExpr? config { contract := contract, locals := locals' } evm (.var oldName) =
        .ok (.int (Int.ofNat old.toNat)) := by
    exact vatEvalExpr_varUInt256 (by
      change (locals.insert name (.int (Int.ofNat new.toNat))).get? oldName =
        some (.int (Int.ofNat old.toNat))
      rw [store_get_ne _ _ hnameOld]
      exact hold)
  have hguardNegEval :
      evalExpr? config { contract := contract, locals := locals' } evm
        (eitherExpr (.binary .ge (.var addName) (.intLit 0))
          (.binary .le (.var name) (.var oldName))) =
        .ok (.bool false) :=
    evalSignedAddGuardNeg_false haddAfter hnewEval holdAfter hcond
  change ExecBlock config { contract := contract, locals := locals } evm
    [ .letDecl name (some uint256)
        (wordWrap256 (.binary .add (.var oldName) (.var addName))),
      .require
        (eitherExpr (.binary .ge (.var addName) (.intLit 0))
          (.binary .le (.var name) (.var oldName))),
      .require
        (eitherExpr (.binary .le (.var addName) (.intLit 0))
          (.binary .ge (.var name) (.var oldName))) ]
    .reverted
  refine ExecBlock.consNormal (ExecStmt.letDecl hlet) ?_
  exact ExecBlock.consRevert (ExecStmt.requireFalse hguardNegEval)

theorem execFrobCheckedAddVarRevertGuardPos {evm : EVM.State}
    (locals : Store) (name oldName addName : Ident)
    (old new addWord : UInt256) (addInt : Int)
    (hnameOld : (name == oldName) = false)
    (hnameAdd : (name == addName) = false)
    (hold : locals.get? oldName = some (.int (Int.ofNat old.toNat)))
    (hadd : locals.get? addName = some (.int addInt))
    (haddMod : addInt % (Int.ofNat EVM.wordModulus) = Int.ofNat addWord.toNat)
    (hnew : new = addWord + old)
    (hguardNeg : 0 ≤ addInt ∨ new.toNat ≤ old.toNat)
    (hcond : 0 < addInt ∧ new.toNat < old.toNat) :
    ExecBlock config { contract := contract, locals := locals } evm
      (checkedAddSignedInto name (.var oldName) (.var addName))
      .reverted := by
  let locals' := locals.insert name (.int (Int.ofNat new.toNat))
  have holdEval :
      evalExpr? config { contract := contract, locals := locals } evm (.var oldName) =
        .ok (.int (Int.ofNat old.toNat)) :=
    vatEvalExpr_varUInt256 hold
  have haddEval :
      evalExpr? config { contract := contract, locals := locals } evm (.var addName) =
        .ok (.int addInt) :=
    vatEvalExpr_varInt hadd
  have hlet :
      evalExpr? config { contract := contract, locals := locals } evm
        (wordWrap256 (.binary .add (.var oldName) (.var addName))) =
        .ok (.int (Int.ofNat new.toNat)) := by
    exact evalExpr_fold_wordWrapAdd_ok holdEval haddEval haddMod hnew
  have hnewEval :
      evalExpr? config { contract := contract, locals := locals' } evm (.var name) =
        .ok (.int (Int.ofNat new.toNat)) := by
    exact vatEvalExpr_varUInt256 (by simp [locals'])
  have haddAfter :
      evalExpr? config { contract := contract, locals := locals' } evm (.var addName) =
        .ok (.int addInt) := by
    exact vatEvalExpr_varInt (by
      change (locals.insert name (.int (Int.ofNat new.toNat))).get? addName =
        some (.int addInt)
      rw [store_get_ne _ _ hnameAdd]
      exact hadd)
  have holdAfter :
      evalExpr? config { contract := contract, locals := locals' } evm (.var oldName) =
        .ok (.int (Int.ofNat old.toNat)) := by
    exact vatEvalExpr_varUInt256 (by
      change (locals.insert name (.int (Int.ofNat new.toNat))).get? oldName =
        some (.int (Int.ofNat old.toNat))
      rw [store_get_ne _ _ hnameOld]
      exact hold)
  have hguardNegEval :
      evalExpr? config { contract := contract, locals := locals' } evm
        (eitherExpr (.binary .ge (.var addName) (.intLit 0))
          (.binary .le (.var name) (.var oldName))) =
        .ok (.bool true) :=
    evalSignedAddGuardNeg_true haddAfter hnewEval holdAfter hguardNeg
  have hguardPosEval :
      evalExpr? config { contract := contract, locals := locals' } evm
        (eitherExpr (.binary .le (.var addName) (.intLit 0))
          (.binary .ge (.var name) (.var oldName))) =
        .ok (.bool false) :=
    evalSignedAddGuardPos_false haddAfter hnewEval holdAfter hcond
  change ExecBlock config { contract := contract, locals := locals } evm
    [ .letDecl name (some uint256)
        (wordWrap256 (.binary .add (.var oldName) (.var addName))),
      .require
        (eitherExpr (.binary .ge (.var addName) (.intLit 0))
          (.binary .le (.var name) (.var oldName))),
      .require
        (eitherExpr (.binary .le (.var addName) (.intLit 0))
          (.binary .ge (.var name) (.var oldName))) ]
    .reverted
  refine ExecBlock.consNormal (ExecStmt.letDecl hlet) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue hguardNegEval) ?_
  exact ExecBlock.consRevert (ExecStmt.requireFalse hguardPosEval)

theorem execFrobUrnInkAddRevertGuardNeg {evm : EVM.State} {I : ExecutionEnv}
    (locals : Store) (urnInk urnInkNew : UInt256)
    (hurnInk : locals.get? "urnInk" = some (.int (Int.ofNat urnInk.toNat)))
    (hdink : locals.get? "dink" = some (frobDinkValue I))
    (hnew : urnInkNew = frobDinkWord I + urnInk)
    (hcond : frobDinkInt I < 0 ∧ urnInk.toNat < urnInkNew.toNat) :
    ExecBlock config { contract := contract, locals := locals } evm
      (checkedAddSignedInto "urnInkNew" (.var "urnInk") (.var "dink"))
      .reverted := by
  exact execFrobCheckedAddVarRevertGuardNeg locals "urnInkNew" "urnInk" "dink"
    urnInk urnInkNew (frobDinkWord I) (frobDinkInt I)
    (by native_decide) (by native_decide) hurnInk
    (by simpa [frobDinkValue] using hdink) (frobDinkInt_mod_word I) hnew hcond

theorem execFrobUrnInkAddRevertGuardPos {evm : EVM.State} {I : ExecutionEnv}
    (locals : Store) (urnInk urnInkNew : UInt256)
    (hurnInk : locals.get? "urnInk" = some (.int (Int.ofNat urnInk.toNat)))
    (hdink : locals.get? "dink" = some (frobDinkValue I))
    (hnew : urnInkNew = frobDinkWord I + urnInk)
    (hguardNeg : 0 ≤ frobDinkInt I ∨ urnInkNew.toNat ≤ urnInk.toNat)
    (hcond : 0 < frobDinkInt I ∧ urnInkNew.toNat < urnInk.toNat) :
    ExecBlock config { contract := contract, locals := locals } evm
      (checkedAddSignedInto "urnInkNew" (.var "urnInk") (.var "dink"))
      .reverted := by
  exact execFrobCheckedAddVarRevertGuardPos locals "urnInkNew" "urnInk" "dink"
    urnInk urnInkNew (frobDinkWord I) (frobDinkInt I)
    (by native_decide) (by native_decide) hurnInk
    (by simpa [frobDinkValue] using hdink) (frobDinkInt_mod_word I) hnew hguardNeg hcond

theorem execFrobUrnArtAddOk {evm : EVM.State} {I : ExecutionEnv}
    (locals : Store) (urnArt urnArtNew : UInt256)
    (hurnArt : locals.get? "urnArt" = some (.int (Int.ofNat urnArt.toNat)))
    (hdart : locals.get? "dart" = some (frobDartValue I))
    (hnew : urnArtNew = frobDartWord I + urnArt)
    (hguardNeg : 0 ≤ frobDartInt I ∨ urnArtNew.toNat ≤ urnArt.toNat)
    (hguardPos : frobDartInt I ≤ 0 ∨ urnArt.toNat ≤ urnArtNew.toNat) :
    ExecBlock config { contract := contract, locals := locals } evm
      (checkedAddSignedInto "urnArtNew" (.var "urnArt") (.var "dart"))
      (.ok
        { contract := contract,
          locals := locals.insert "urnArtNew" (.int (Int.ofNat urnArtNew.toNat)) }
        evm) := by
  exact execFrobCheckedAddVarOk locals "urnArtNew" "urnArt" "dart"
    urnArt urnArtNew (frobDartWord I) (frobDartInt I)
    (by native_decide) (by native_decide) hurnArt
    (by simpa [frobDartValue] using hdart) (frobDartInt_mod_word I)
    hnew hguardNeg hguardPos

theorem execFrobUrnArtAddRevertGuardNeg {evm : EVM.State} {I : ExecutionEnv}
    (locals : Store) (urnArt urnArtNew : UInt256)
    (hurnArt : locals.get? "urnArt" = some (.int (Int.ofNat urnArt.toNat)))
    (hdart : locals.get? "dart" = some (frobDartValue I))
    (hnew : urnArtNew = frobDartWord I + urnArt)
    (hcond : frobDartInt I < 0 ∧ urnArt.toNat < urnArtNew.toNat) :
    ExecBlock config { contract := contract, locals := locals } evm
      (checkedAddSignedInto "urnArtNew" (.var "urnArt") (.var "dart"))
      .reverted := by
  exact execFrobCheckedAddVarRevertGuardNeg locals "urnArtNew" "urnArt" "dart"
    urnArt urnArtNew (frobDartWord I) (frobDartInt I)
    (by native_decide) (by native_decide) hurnArt
    (by simpa [frobDartValue] using hdart) (frobDartInt_mod_word I) hnew hcond

theorem execFrobUrnArtAddRevertGuardPos {evm : EVM.State} {I : ExecutionEnv}
    (locals : Store) (urnArt urnArtNew : UInt256)
    (hurnArt : locals.get? "urnArt" = some (.int (Int.ofNat urnArt.toNat)))
    (hdart : locals.get? "dart" = some (frobDartValue I))
    (hnew : urnArtNew = frobDartWord I + urnArt)
    (hguardNeg : 0 ≤ frobDartInt I ∨ urnArtNew.toNat ≤ urnArt.toNat)
    (hcond : 0 < frobDartInt I ∧ urnArtNew.toNat < urnArt.toNat) :
    ExecBlock config { contract := contract, locals := locals } evm
      (checkedAddSignedInto "urnArtNew" (.var "urnArt") (.var "dart"))
      .reverted := by
  exact execFrobCheckedAddVarRevertGuardPos locals "urnArtNew" "urnArt" "dart"
    urnArt urnArtNew (frobDartWord I) (frobDartInt I)
    (by native_decide) (by native_decide) hurnArt
    (by simpa [frobDartValue] using hdart) (frobDartInt_mod_word I) hnew hguardNeg hcond

theorem execFrobIlkArtAddOk {evm : EVM.State} {I : ExecutionEnv}
    (locals : Store) (ilkArt ilkArtNew : UInt256)
    (hilkArt : locals.get? "ilkArt" = some (.int (Int.ofNat ilkArt.toNat)))
    (hdart : locals.get? "dart" = some (frobDartValue I))
    (hnew : ilkArtNew = frobDartWord I + ilkArt)
    (hguardNeg : 0 ≤ frobDartInt I ∨ ilkArtNew.toNat ≤ ilkArt.toNat)
    (hguardPos : frobDartInt I ≤ 0 ∨ ilkArt.toNat ≤ ilkArtNew.toNat) :
    ExecBlock config { contract := contract, locals := locals } evm
      (checkedAddSignedInto "ilkArtNew" (.var "ilkArt") (.var "dart"))
      (.ok
        { contract := contract,
          locals := locals.insert "ilkArtNew" (.int (Int.ofNat ilkArtNew.toNat)) }
        evm) := by
  exact execFrobCheckedAddVarOk locals "ilkArtNew" "ilkArt" "dart"
    ilkArt ilkArtNew (frobDartWord I) (frobDartInt I)
    (by native_decide) (by native_decide) hilkArt
    (by simpa [frobDartValue] using hdart) (frobDartInt_mod_word I)
    hnew hguardNeg hguardPos

theorem execFrobIlkArtAddRevertGuardNeg {evm : EVM.State} {I : ExecutionEnv}
    (locals : Store) (ilkArt ilkArtNew : UInt256)
    (hilkArt : locals.get? "ilkArt" = some (.int (Int.ofNat ilkArt.toNat)))
    (hdart : locals.get? "dart" = some (frobDartValue I))
    (hnew : ilkArtNew = frobDartWord I + ilkArt)
    (hcond : frobDartInt I < 0 ∧ ilkArt.toNat < ilkArtNew.toNat) :
    ExecBlock config { contract := contract, locals := locals } evm
      (checkedAddSignedInto "ilkArtNew" (.var "ilkArt") (.var "dart"))
      .reverted := by
  exact execFrobCheckedAddVarRevertGuardNeg locals "ilkArtNew" "ilkArt" "dart"
    ilkArt ilkArtNew (frobDartWord I) (frobDartInt I)
    (by native_decide) (by native_decide) hilkArt
    (by simpa [frobDartValue] using hdart) (frobDartInt_mod_word I) hnew hcond

theorem execFrobIlkArtAddRevertGuardPos {evm : EVM.State} {I : ExecutionEnv}
    (locals : Store) (ilkArt ilkArtNew : UInt256)
    (hilkArt : locals.get? "ilkArt" = some (.int (Int.ofNat ilkArt.toNat)))
    (hdart : locals.get? "dart" = some (frobDartValue I))
    (hnew : ilkArtNew = frobDartWord I + ilkArt)
    (hguardNeg : 0 ≤ frobDartInt I ∨ ilkArtNew.toNat ≤ ilkArt.toNat)
    (hcond : 0 < frobDartInt I ∧ ilkArtNew.toNat < ilkArt.toNat) :
    ExecBlock config { contract := contract, locals := locals } evm
      (checkedAddSignedInto "ilkArtNew" (.var "ilkArt") (.var "dart"))
      .reverted := by
  exact execFrobCheckedAddVarRevertGuardPos locals "ilkArtNew" "ilkArt" "dart"
    ilkArt ilkArtNew (frobDartWord I) (frobDartInt I)
    (by native_decide) (by native_decide) hilkArt
    (by simpa [frobDartValue] using hdart) (frobDartInt_mod_word I) hnew hguardNeg hcond

theorem execFrobLoadedPrefixThreeAdds {evm : EVM.State} {I : ExecutionEnv}
    {pre : List Stmt}
    (urnInk urnArt ilkArt ilkRate ilkSpot ilkLine ilkDust : UInt256)
    (hprefix :
      ExecBlock config { contract := contract, locals := frobStore I } evm pre
        (.ok
          { contract := contract,
            locals := frobStoreIlkDust I urnInk urnArt ilkArt ilkRate ilkSpot ilkLine
              ilkDust }
          evm))
    (hInkNeg : 0 ≤ frobDinkInt I ∨ (frobDinkWord I + urnInk).toNat ≤ urnInk.toNat)
    (hInkPos : frobDinkInt I ≤ 0 ∨ urnInk.toNat ≤ (frobDinkWord I + urnInk).toNat)
    (hArtNeg : 0 ≤ frobDartInt I ∨ (frobDartWord I + urnArt).toNat ≤ urnArt.toNat)
    (hArtPos : frobDartInt I ≤ 0 ∨ urnArt.toNat ≤ (frobDartWord I + urnArt).toNat)
    (hIlkNeg : 0 ≤ frobDartInt I ∨ (frobDartWord I + ilkArt).toNat ≤ ilkArt.toNat)
    (hIlkPos : frobDartInt I ≤ 0 ∨ ilkArt.toNat ≤ (frobDartWord I + ilkArt).toNat) :
    let localsLoaded :=
      frobStoreIlkDust I urnInk urnArt ilkArt ilkRate ilkSpot ilkLine ilkDust
    let urnInkNew := frobDinkWord I + urnInk
    let urnArtNew := frobDartWord I + urnArt
    let ilkArtNew := frobDartWord I + ilkArt
    ExecBlock config { contract := contract, locals := frobStore I } evm
      (pre ++
        checkedAddSignedInto "urnInkNew" (.var "urnInk") (.var "dink") ++
        checkedAddSignedInto "urnArtNew" (.var "urnArt") (.var "dart") ++
        checkedAddSignedInto "ilkArtNew" (.var "ilkArt") (.var "dart"))
      (.ok
        { contract := contract,
          locals :=
            (((localsLoaded.insert "urnInkNew" (.int (Int.ofNat urnInkNew.toNat))).insert
                "urnArtNew" (.int (Int.ofNat urnArtNew.toNat))).insert "ilkArtNew"
              (.int (Int.ofNat ilkArtNew.toNat))) }
        evm) := by
  intro localsLoaded urnInkNew urnArtNew ilkArtNew
  have hInkBlock :
      ExecBlock config { contract := contract, locals := localsLoaded } evm
        (checkedAddSignedInto "urnInkNew" (.var "urnInk") (.var "dink"))
        (.ok
          { contract := contract,
            locals := localsLoaded.insert "urnInkNew"
              (.int (Int.ofNat urnInkNew.toNat)) }
          evm) := by
    exact execFrobUrnInkAddOk (I := I) localsLoaded urnInk urnInkNew
      (by
        simpa [localsLoaded] using
          frobStoreIlkDust_get_urnInk I urnInk urnArt ilkArt ilkRate ilkSpot ilkLine
            ilkDust)
      (by
        simpa [localsLoaded] using
          frobStoreIlkDust_get_dink I urnInk urnArt ilkArt ilkRate ilkSpot ilkLine
            ilkDust)
      (by simp [urnInkNew]) (by simpa [urnInkNew] using hInkNeg)
      (by simpa [urnInkNew] using hInkPos)
  let localsInk := localsLoaded.insert "urnInkNew" (.int (Int.ofNat urnInkNew.toNat))
  have hArtBlock :
      ExecBlock config { contract := contract, locals := localsInk } evm
        (checkedAddSignedInto "urnArtNew" (.var "urnArt") (.var "dart"))
        (.ok
          { contract := contract,
            locals := localsInk.insert "urnArtNew" (.int (Int.ofNat urnArtNew.toNat)) }
          evm) := by
    exact execFrobUrnArtAddOk (I := I) localsInk urnArt urnArtNew
      (by
        change (localsLoaded.insert "urnInkNew"
          (.int (Int.ofNat urnInkNew.toNat))).get? "urnArt" =
          some (.int (Int.ofNat urnArt.toNat))
        rw [store_get_ne _ _ (by decide)]
        simpa [localsLoaded] using
          frobStoreIlkDust_get_urnArt I urnInk urnArt ilkArt ilkRate ilkSpot ilkLine
            ilkDust)
      (by
        change (localsLoaded.insert "urnInkNew"
          (.int (Int.ofNat urnInkNew.toNat))).get? "dart" =
          some (frobDartValue I)
        rw [store_get_ne _ _ (by decide)]
        simpa [localsLoaded] using
          frobStoreIlkDust_get_dart I urnInk urnArt ilkArt ilkRate ilkSpot ilkLine
            ilkDust)
      (by simp [urnArtNew]) (by simpa [urnArtNew] using hArtNeg)
      (by simpa [urnArtNew] using hArtPos)
  let localsArt := localsInk.insert "urnArtNew" (.int (Int.ofNat urnArtNew.toNat))
  have hIlkBlock :
      ExecBlock config { contract := contract, locals := localsArt } evm
        (checkedAddSignedInto "ilkArtNew" (.var "ilkArt") (.var "dart"))
        (.ok
          { contract := contract,
            locals := localsArt.insert "ilkArtNew" (.int (Int.ofNat ilkArtNew.toNat)) }
          evm) := by
    exact execFrobIlkArtAddOk (I := I) localsArt ilkArt ilkArtNew
      (by
        change ((localsLoaded.insert "urnInkNew" (.int (Int.ofNat urnInkNew.toNat))).insert
          "urnArtNew" (.int (Int.ofNat urnArtNew.toNat))).get? "ilkArt" =
          some (.int (Int.ofNat ilkArt.toNat))
        rw [store_get_ne _ _ (by decide)]
        rw [store_get_ne _ _ (by decide)]
        simpa [localsLoaded] using
          frobStoreIlkDust_get_ilkArt I urnInk urnArt ilkArt ilkRate ilkSpot ilkLine
            ilkDust)
      (by
        change ((localsLoaded.insert "urnInkNew" (.int (Int.ofNat urnInkNew.toNat))).insert
          "urnArtNew" (.int (Int.ofNat urnArtNew.toNat))).get? "dart" =
          some (frobDartValue I)
        rw [store_get_ne _ _ (by decide)]
        rw [store_get_ne _ _ (by decide)]
        simpa [localsLoaded] using
          frobStoreIlkDust_get_dart I urnInk urnArt ilkArt ilkRate ilkSpot ilkLine
            ilkDust)
      (by simp [ilkArtNew]) (by simpa [ilkArtNew] using hIlkNeg)
      (by simpa [ilkArtNew] using hIlkPos)
  have h01 := Reasoning.Refinement.execBlock_append hprefix
    (by simpa [localsLoaded] using hInkBlock)
  have h02 := Reasoning.Refinement.execBlock_append h01
    (by simpa [localsLoaded, localsInk] using hArtBlock)
  have h03 := Reasoning.Refinement.execBlock_append h02
    (by simpa [localsLoaded, localsInk, localsArt] using hIlkBlock)
  simpa [localsLoaded, localsInk, localsArt, List.append_assoc] using h03

theorem execFrobDtabMulCheckedOk {evm : EVM.State} {I : ExecutionEnv}
    (locals : Store) (rateOld : UInt256) (dtab : Int)
    (hrate : locals.get? "ilkRate" = some (.int (Int.ofNat rateOld.toNat)))
    (hdart : locals.get? "dart" = some (frobDartValue I))
    (hdtab : dtab = Int.ofNat rateOld.toNat * frobDartInt I)
    (hdtabLo : -((2 : Int) ^ 255) ≤ dtab)
    (hdtabHi : dtab < (2 : Int) ^ 255)
    (hguardMax :
      evalExpr? config
        { contract := contract,
          locals := locals.insert "dtab" (.int dtab) } evm
        (.binary .le (.var "ilkRate") (.intLit maxInt256)) =
        .ok (.bool true))
    (hguardMul :
      evalExpr? config
        { contract := contract,
          locals := locals.insert "dtab" (.int dtab) } evm
        (eitherExpr (.binary .eq (.var "dart") (.intLit 0))
          (.binary .eq (.binary .div (.var "dtab") (.var "dart"))
            (.var "ilkRate"))) =
        .ok (.bool true)) :
    ExecBlock config { contract := contract, locals := locals } evm
      (checkedMulSignedInto "dtab" (.var "ilkRate") (.var "dart"))
      (.ok
        { contract := contract, locals := locals.insert "dtab" (.int dtab) }
        evm) := by
  let locals' := locals.insert "dtab" (.int dtab)
  have hrateEval :
      evalExpr? config { contract := contract, locals := locals } evm (.var "ilkRate") =
        .ok (.int (Int.ofNat rateOld.toNat)) :=
    vatEvalExpr_varUInt256 hrate
  have hdartEval :
      evalExpr? config { contract := contract, locals := locals } evm (.var "dart") =
        .ok (.int (frobDartInt I)) :=
    vatEvalExpr_varInt (by simpa [frobDartValue] using hdart)
  have hmul :
      evalExpr? config { contract := contract, locals := locals } evm
        (.binary .mul (.var "ilkRate") (.var "dart")) =
        .ok (.int dtab) :=
    evalExpr_fold_mul_int_ok hrateEval hdartEval hdtab
  have hlet :
      evalExpr? config { contract := contract, locals := locals } evm
        (s256 (.binary .mul (.var "ilkRate") (.var "dart"))) =
        .ok (.int dtab) :=
    evalExpr_fold_s256_ok hmul hdtabLo hdtabHi
  change ExecBlock config { contract := contract, locals := locals } evm
    [ .letDecl "dtab" (some int256)
        (s256 (.binary .mul (.var "ilkRate") (.var "dart"))),
      .require (.binary .le (.var "ilkRate") (.intLit maxInt256)),
      .require
        (eitherExpr (.binary .eq (.var "dart") (.intLit 0))
          (.binary .eq (.binary .div (.var "dtab") (.var "dart"))
            (.var "ilkRate"))) ]
    (.ok { contract := contract, locals := locals' } evm)
  refine ExecBlock.consNormal (ExecStmt.letDecl hlet) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue hguardMax) ?_
  exact ExecBlock.consNormal (ExecStmt.requireTrue hguardMul) ExecBlock.nil

theorem execFrobDtabMulCheckedRevertRange {evm : EVM.State} {I : ExecutionEnv}
    (locals : Store) (rateOld : UInt256) (dtab : Int)
    (hrate : locals.get? "ilkRate" = some (.int (Int.ofNat rateOld.toNat)))
    (hdart : locals.get? "dart" = some (frobDartValue I))
    (hdtab : dtab = Int.ofNat rateOld.toNat * frobDartInt I)
    (hbad : dtab < -((2 : Int) ^ 255) ∨ dtab ≥ (2 : Int) ^ 255) :
    ExecBlock config { contract := contract, locals := locals } evm
      (checkedMulSignedInto "dtab" (.var "ilkRate") (.var "dart"))
      .reverted := by
  have hrateEval :
      evalExpr? config { contract := contract, locals := locals } evm (.var "ilkRate") =
        .ok (.int (Int.ofNat rateOld.toNat)) :=
    vatEvalExpr_varUInt256 hrate
  have hdartEval :
      evalExpr? config { contract := contract, locals := locals } evm (.var "dart") =
        .ok (.int (frobDartInt I)) :=
    vatEvalExpr_varInt (by simpa [frobDartValue] using hdart)
  have hmul :
      evalExpr? config { contract := contract, locals := locals } evm
        (.binary .mul (.var "ilkRate") (.var "dart")) =
        .ok (.int dtab) :=
    evalExpr_fold_mul_int_ok hrateEval hdartEval hdtab
  change ExecBlock config { contract := contract, locals := locals } evm
    [ .letDecl "dtab" (some int256)
        (s256 (.binary .mul (.var "ilkRate") (.var "dart"))),
      .require (.binary .le (.var "ilkRate") (.intLit maxInt256)),
      .require
        (eitherExpr (.binary .eq (.var "dart") (.intLit 0))
          (.binary .eq (.binary .div (.var "dtab") (.var "dart"))
            (.var "ilkRate"))) ]
    .reverted
  exact ExecBlock.consRevert (ExecStmt.letDeclRevert (evalExpr_s256_revert hmul hbad))

theorem execFrobDtabMulCheckedRevertMax {evm : EVM.State} {I : ExecutionEnv}
    (locals : Store) (rateOld : UInt256) (dtab : Int)
    (hrate : locals.get? "ilkRate" = some (.int (Int.ofNat rateOld.toNat)))
    (hdart : locals.get? "dart" = some (frobDartValue I))
    (hdtab : dtab = Int.ofNat rateOld.toNat * frobDartInt I)
    (hdtabLo : -((2 : Int) ^ 255) ≤ dtab)
    (hdtabHi : dtab < (2 : Int) ^ 255)
    (hguardMax :
      evalExpr? config { contract := contract, locals := locals.insert "dtab" (.int dtab) }
        evm (.binary .le (.var "ilkRate") (.intLit maxInt256)) =
        .ok (.bool false)) :
    ExecBlock config { contract := contract, locals := locals } evm
      (checkedMulSignedInto "dtab" (.var "ilkRate") (.var "dart"))
      .reverted := by
  have hrateEval :
      evalExpr? config { contract := contract, locals := locals } evm (.var "ilkRate") =
        .ok (.int (Int.ofNat rateOld.toNat)) :=
    vatEvalExpr_varUInt256 hrate
  have hdartEval :
      evalExpr? config { contract := contract, locals := locals } evm (.var "dart") =
        .ok (.int (frobDartInt I)) :=
    vatEvalExpr_varInt (by simpa [frobDartValue] using hdart)
  have hmul :
      evalExpr? config { contract := contract, locals := locals } evm
        (.binary .mul (.var "ilkRate") (.var "dart")) =
        .ok (.int dtab) :=
    evalExpr_fold_mul_int_ok hrateEval hdartEval hdtab
  have hlet :
      evalExpr? config { contract := contract, locals := locals } evm
        (s256 (.binary .mul (.var "ilkRate") (.var "dart"))) =
        .ok (.int dtab) :=
    evalExpr_fold_s256_ok hmul hdtabLo hdtabHi
  change ExecBlock config { contract := contract, locals := locals } evm
    [ .letDecl "dtab" (some int256)
        (s256 (.binary .mul (.var "ilkRate") (.var "dart"))),
      .require (.binary .le (.var "ilkRate") (.intLit maxInt256)),
      .require
        (eitherExpr (.binary .eq (.var "dart") (.intLit 0))
          (.binary .eq (.binary .div (.var "dtab") (.var "dart"))
            (.var "ilkRate"))) ]
    .reverted
  refine ExecBlock.consNormal (ExecStmt.letDecl hlet) ?_
  exact ExecBlock.consRevert (ExecStmt.requireFalse hguardMax)

theorem execFrobDtabMulCheckedRevertMaxSlt {evm : EVM.State} {I : ExecutionEnv}
    (locals : Store) (rateOld : UInt256) (dtab : Int)
    (hrate : locals.get? "ilkRate" = some (.int (Int.ofNat rateOld.toNat)))
    (hdart : locals.get? "dart" = some (frobDartValue I))
    (hdtab : dtab = Int.ofNat rateOld.toNat * frobDartInt I)
    (hdtabLo : -((2 : Int) ^ 255) ≤ dtab)
    (hdtabHi : dtab < (2 : Int) ^ 255)
    (hmaxFail : UInt256.slt rateOld ⟨0⟩ ≠ ⟨0⟩) :
    ExecBlock config { contract := contract, locals := locals } evm
      (checkedMulSignedInto "dtab" (.var "ilkRate") (.var "dart"))
      .reverted := by
  refine execFrobDtabMulCheckedRevertMax (evm := evm) (I := I) locals rateOld dtab
    hrate hdart hdtab hdtabLo hdtabHi ?_
  have hrateAfter :
      evalExpr? config { contract := contract, locals := locals.insert "dtab" (.int dtab) }
        evm (.var "ilkRate") = .ok (.int (Int.ofNat rateOld.toNat)) := by
    exact vatEvalExpr_varUInt256 (by
      change (locals.insert "dtab" (.int dtab)).get? "ilkRate" =
        some (.int (Int.ofNat rateOld.toNat))
      rw [store_get_ne _ _ (by decide)]
      exact hrate)
  exact vatEvalExpr_le_int_false hrateAfter (by simp [evalExpr?, pure])
    (uintWordGtMaxInt256_of_slt_ne_zero hmaxFail)

theorem execFrobDtabMulCheckedRevertMul {evm : EVM.State} {I : ExecutionEnv}
    (locals : Store) (rateOld : UInt256) (dtab : Int)
    (hrate : locals.get? "ilkRate" = some (.int (Int.ofNat rateOld.toNat)))
    (hdart : locals.get? "dart" = some (frobDartValue I))
    (hdtab : dtab = Int.ofNat rateOld.toNat * frobDartInt I)
    (hdtabLo : -((2 : Int) ^ 255) ≤ dtab)
    (hdtabHi : dtab < (2 : Int) ^ 255)
    (hguardMax :
      evalExpr? config { contract := contract, locals := locals.insert "dtab" (.int dtab) }
        evm (.binary .le (.var "ilkRate") (.intLit maxInt256)) =
        .ok (.bool true))
    (hguardMul :
      evalExpr? config { contract := contract, locals := locals.insert "dtab" (.int dtab) }
        evm
        (eitherExpr (.binary .eq (.var "dart") (.intLit 0))
          (.binary .eq (.binary .div (.var "dtab") (.var "dart"))
            (.var "ilkRate"))) =
        .ok (.bool false)) :
    ExecBlock config { contract := contract, locals := locals } evm
      (checkedMulSignedInto "dtab" (.var "ilkRate") (.var "dart"))
      .reverted := by
  have hrateEval :
      evalExpr? config { contract := contract, locals := locals } evm (.var "ilkRate") =
        .ok (.int (Int.ofNat rateOld.toNat)) :=
    vatEvalExpr_varUInt256 hrate
  have hdartEval :
      evalExpr? config { contract := contract, locals := locals } evm (.var "dart") =
        .ok (.int (frobDartInt I)) :=
    vatEvalExpr_varInt (by simpa [frobDartValue] using hdart)
  have hmul :
      evalExpr? config { contract := contract, locals := locals } evm
        (.binary .mul (.var "ilkRate") (.var "dart")) =
        .ok (.int dtab) :=
    evalExpr_fold_mul_int_ok hrateEval hdartEval hdtab
  have hlet :
      evalExpr? config { contract := contract, locals := locals } evm
        (s256 (.binary .mul (.var "ilkRate") (.var "dart"))) =
        .ok (.int dtab) :=
    evalExpr_fold_s256_ok hmul hdtabLo hdtabHi
  change ExecBlock config { contract := contract, locals := locals } evm
    [ .letDecl "dtab" (some int256)
        (s256 (.binary .mul (.var "ilkRate") (.var "dart"))),
      .require (.binary .le (.var "ilkRate") (.intLit maxInt256)),
      .require
        (eitherExpr (.binary .eq (.var "dart") (.intLit 0))
          (.binary .eq (.binary .div (.var "dtab") (.var "dart"))
            (.var "ilkRate"))) ]
    .reverted
  refine ExecBlock.consNormal (ExecStmt.letDecl hlet) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue hguardMax) ?_
  exact ExecBlock.consRevert (ExecStmt.requireFalse hguardMul)

theorem evalExpr_frob_dtab_mul_guard_dart_zero_true
    {evm : EVM.State} {locals : Store} (I : ExecutionEnv) {dtab : Int}
    (hdart : locals.get? "dart" = some (frobDartValue I))
    (hzero : frobDartInt I = 0) :
    evalExpr? config { contract := contract, locals := locals.insert "dtab" (.int dtab) } evm
      (eitherExpr (.binary .eq (.var "dart") (.intLit 0))
        (.binary .eq (.binary .div (.var "dtab") (.var "dart"))
          (.var "ilkRate"))) =
      .ok (.bool true) := by
  have hdartEval :
      evalExpr? config { contract := contract, locals := locals.insert "dtab" (.int dtab) } evm
        (.var "dart") = .ok (.int 0) := by
    have hget :
        (locals.insert "dtab" (.int dtab)).get? "dart" =
          some (frobDartValue I) := by
      rw [store_get_ne _ _ (by decide)]
      exact hdart
    simpa [frobDartValue, hzero] using vatEvalExpr_varInt hget
  have hleft :
      evalExpr? config { contract := contract, locals := locals.insert "dtab" (.int dtab) } evm
        (.binary .eq (.var "dart") (.intLit 0)) = .ok (.bool true) := by
    simp [evalExpr?, EvalResult.bind, bind, hdartEval, evalBinaryOp?]
  exact vatEvalExpr_or_true_left hleft

theorem evalExpr_frob_dtab_mul_guard_exact_true
    {evm : EVM.State} {locals : Store} (I : ExecutionEnv) {rate : UInt256} {dtab : Int}
    (hdart : locals.get? "dart" = some (frobDartValue I))
    (hrate : locals.get? "ilkRate" = some (.int (Int.ofNat rate.toNat)))
    (hdartNe : frobDartInt I ≠ 0)
    (hdiv : dtab / frobDartInt I = Int.ofNat rate.toNat) :
    evalExpr? config { contract := contract, locals := locals.insert "dtab" (.int dtab) } evm
      (eitherExpr (.binary .eq (.var "dart") (.intLit 0))
        (.binary .eq (.binary .div (.var "dtab") (.var "dart"))
          (.var "ilkRate"))) =
      .ok (.bool true) := by
  have hdartEval :
      evalExpr? config { contract := contract, locals := locals.insert "dtab" (.int dtab) } evm
        (.var "dart") = .ok (.int (frobDartInt I)) := by
    have hget :
        (locals.insert "dtab" (.int dtab)).get? "dart" =
          some (frobDartValue I) := by
      rw [store_get_ne _ _ (by decide)]
      exact hdart
    exact vatEvalExpr_varInt (by simpa [frobDartValue] using hget)
  have hdtabEval :
      evalExpr? config { contract := contract, locals := locals.insert "dtab" (.int dtab) } evm
        (.var "dtab") = .ok (.int dtab) :=
    vatEvalExpr_varInt (by simp)
  have hrateEval :
      evalExpr? config { contract := contract, locals := locals.insert "dtab" (.int dtab) } evm
        (.var "ilkRate") = .ok (.int (Int.ofNat rate.toNat)) := by
    have hget :
        (locals.insert "dtab" (.int dtab)).get? "ilkRate" =
          some (.int (Int.ofNat rate.toNat)) := by
      rw [store_get_ne _ _ (by decide)]
      exact hrate
    exact vatEvalExpr_varUInt256 hget
  have hleft :
      evalExpr? config { contract := contract, locals := locals.insert "dtab" (.int dtab) } evm
        (.binary .eq (.var "dart") (.intLit 0)) = .ok (.bool false) := by
    simp [evalExpr?, EvalResult.bind, bind, hdartEval, evalBinaryOp?, hdartNe]
  have hright :
      evalExpr? config { contract := contract, locals := locals.insert "dtab" (.int dtab) } evm
        (.binary .eq (.binary .div (.var "dtab") (.var "dart"))
          (.var "ilkRate")) =
      .ok (.bool true) := by
    simp [evalExpr?, EvalResult.bind, bind, hdtabEval, hdartEval, hrateEval,
      evalBinaryOp?, hdartNe, hdiv]
  exact vatEvalExpr_or_false_right hleft hright

theorem execFrobTabMulCheckedOk {evm : EVM.State} {locals : Store}
    (rate urnArtNew tab : UInt256)
    (hrate : locals.get? "ilkRate" = some (.int (Int.ofNat rate.toNat)))
    (hurnArtNew : locals.get? "urnArtNew" = some (.int (Int.ofNat urnArtNew.toNat)))
    (hprod : tab = UInt256.mul rate urnArtNew)
    (hfit : rate.toNat * urnArtNew.toNat < UInt256.size)
    (hguard : urnArtNew.toNat = 0 ∨ tab.toNat / urnArtNew.toNat = rate.toNat) :
    ExecBlock config { contract := contract, locals := locals } evm
      (checkedMulUintInto "tab" (.var "ilkRate") (.var "urnArtNew"))
      (.ok
        { contract := contract, locals := locals.insert "tab" (.int (Int.ofNat tab.toNat)) }
        evm) := by
  let locals' := locals.insert "tab" (.int (Int.ofNat tab.toNat))
  have hrateEval :
      evalExpr? config { contract := contract, locals := locals } evm (.var "ilkRate") =
        .ok (.int (Int.ofNat rate.toNat)) :=
    vatEvalExpr_varUInt256 hrate
  have hurnArtNewEval :
      evalExpr? config { contract := contract, locals := locals } evm (.var "urnArtNew") =
        .ok (.int (Int.ofNat urnArtNew.toNat)) :=
    vatEvalExpr_varUInt256 hurnArtNew
  have hguardEval :
      evalExpr? config { contract := contract, locals := locals' } evm
        (eitherExpr (.binary .eq (.var "urnArtNew") (.intLit 0))
          (.binary .eq (.binary .div (.var "tab") (.var "urnArtNew"))
            (.var "ilkRate"))) =
      .ok (.bool true) := by
    have hrateAfter :
        evalExpr? config { contract := contract, locals := locals' } evm (.var "ilkRate") =
          .ok (.int (Int.ofNat rate.toNat)) := by
      exact vatEvalExpr_varUInt256 (by
        change (locals.insert "tab" (.int (Int.ofNat tab.toNat))).get? "ilkRate" =
          some (.int (Int.ofNat rate.toNat))
        rw [store_get_ne _ _ (by decide)]
        exact hrate)
    have hurnArtNewAfter :
        evalExpr? config { contract := contract, locals := locals' } evm (.var "urnArtNew") =
          .ok (.int (Int.ofNat urnArtNew.toNat)) := by
      exact vatEvalExpr_varUInt256 (by
        change (locals.insert "tab" (.int (Int.ofNat tab.toNat))).get? "urnArtNew" =
          some (.int (Int.ofNat urnArtNew.toNat))
        rw [store_get_ne _ _ (by decide)]
        exact hurnArtNew)
    have htabAfter :
        evalExpr? config { contract := contract, locals := locals' } evm (.var "tab") =
          .ok (.int (Int.ofNat tab.toNat)) :=
      vatEvalExpr_varUInt256 (by simp [locals'])
    exact evalExpr_fork_mul_guard_true hrateAfter hurnArtNewAfter htabAfter hguard
  exact execForkMulUintIntoOk "tab" (.var "ilkRate") (.var "urnArtNew")
    rate urnArtNew tab hrateEval hurnArtNewEval hprod hfit hguardEval

theorem execFrobTabMulCheckedRevertOverflow {evm : EVM.State} {locals : Store}
    (rate urnArtNew : UInt256)
    (hrate : locals.get? "ilkRate" = some (.int (Int.ofNat rate.toNat)))
    (hurnArtNew : locals.get? "urnArtNew" = some (.int (Int.ofNat urnArtNew.toNat)))
    (hover : UInt256.size ≤ rate.toNat * urnArtNew.toNat) :
    ExecBlock config { contract := contract, locals := locals } evm
      (checkedMulUintInto "tab" (.var "ilkRate") (.var "urnArtNew"))
      .reverted := by
  exact execForkMulUintIntoRevertOfOverflow "tab" (.var "ilkRate") (.var "urnArtNew")
    rate urnArtNew
    (vatEvalExpr_varUInt256 hrate)
    (vatEvalExpr_varUInt256 hurnArtNew)
    hover

theorem execFrobCeilingDebtCheckedRevertOverflow {evm : EVM.State} {locals : Store}
    (ilkArtNew ilkRate : UInt256)
    (hilkArtNew : locals.get? "ilkArtNew" = some (.int (Int.ofNat ilkArtNew.toNat)))
    (hilkRate : locals.get? "ilkRate" = some (.int (Int.ofNat ilkRate.toNat)))
    (hover : UInt256.size ≤ ilkArtNew.toNat * ilkRate.toNat) :
    ExecBlock config { contract := contract, locals := locals } evm
      (checkedMulUintInto "ceilingDebt" (.var "ilkArtNew") (.var "ilkRate"))
      .reverted := by
  exact execForkMulUintIntoRevertOfOverflow "ceilingDebt" (.var "ilkArtNew")
    (.var "ilkRate") ilkArtNew ilkRate
    (vatEvalExpr_varUInt256 hilkArtNew)
    (vatEvalExpr_varUInt256 hilkRate)
    hover

theorem execFrobInkSpotCheckedRevertOverflow {evm : EVM.State} {locals : Store}
    (urnInkNew ilkSpot : UInt256)
    (hurnInkNew : locals.get? "urnInkNew" = some (.int (Int.ofNat urnInkNew.toNat)))
    (hilkSpot : locals.get? "ilkSpot" = some (.int (Int.ofNat ilkSpot.toNat)))
    (hover : UInt256.size ≤ urnInkNew.toNat * ilkSpot.toNat) :
    ExecBlock config { contract := contract, locals := locals } evm
      (checkedMulUintInto "inkSpot" (.var "urnInkNew") (.var "ilkSpot"))
      .reverted := by
  exact execForkMulUintIntoRevertOfOverflow "inkSpot" (.var "urnInkNew")
    (.var "ilkSpot") urnInkNew ilkSpot
    (vatEvalExpr_varUInt256 hurnInkNew)
    (vatEvalExpr_varUInt256 hilkSpot)
    hover

theorem execFrobCeilingDebtCheckedOk {evm : EVM.State} {locals : Store}
    (ilkArtNew ilkRate ceilingDebt : UInt256)
    (hilkArtNew : locals.get? "ilkArtNew" = some (.int (Int.ofNat ilkArtNew.toNat)))
    (hilkRate : locals.get? "ilkRate" = some (.int (Int.ofNat ilkRate.toNat)))
    (hceilingDebt : ceilingDebt = UInt256.mul ilkArtNew ilkRate)
    (hfit : ilkArtNew.toNat * ilkRate.toNat < UInt256.size)
    (hguard : ilkRate.toNat = 0 ∨ ceilingDebt.toNat / ilkRate.toNat = ilkArtNew.toNat) :
    ExecBlock config { contract := contract, locals := locals } evm
      (checkedMulUintInto "ceilingDebt" (.var "ilkArtNew") (.var "ilkRate"))
      (.ok
        { contract := contract,
          locals := locals.insert "ceilingDebt" (.int (Int.ofNat ceilingDebt.toNat)) }
        evm) := by
  let localsCeiling := locals.insert "ceilingDebt" (.int (Int.ofNat ceilingDebt.toNat))
  have hilkArtNewEval :
      evalExpr? config { contract := contract, locals := locals } evm (.var "ilkArtNew") =
        .ok (.int (Int.ofNat ilkArtNew.toNat)) :=
    vatEvalExpr_varUInt256 hilkArtNew
  have hilkRateEval :
      evalExpr? config { contract := contract, locals := locals } evm (.var "ilkRate") =
        .ok (.int (Int.ofNat ilkRate.toNat)) :=
    vatEvalExpr_varUInt256 hilkRate
  have hguardEval :
      evalExpr? config { contract := contract, locals := localsCeiling } evm
        (eitherExpr (.binary .eq (.var "ilkRate") (.intLit 0))
          (.binary .eq (.binary .div (.var "ceilingDebt") (.var "ilkRate"))
            (.var "ilkArtNew"))) =
        .ok (.bool true) := by
    have hilkArtNewAfter :
        evalExpr? config { contract := contract, locals := localsCeiling } evm
          (.var "ilkArtNew") = .ok (.int (Int.ofNat ilkArtNew.toNat)) :=
      vatEvalExpr_varUInt256 (by
        change (locals.insert "ceilingDebt" (.int (Int.ofNat ceilingDebt.toNat))).get?
          "ilkArtNew" = some (.int (Int.ofNat ilkArtNew.toNat))
        rw [store_get_ne _ _ (by decide)]
        exact hilkArtNew)
    have hilkRateAfter :
        evalExpr? config { contract := contract, locals := localsCeiling } evm
          (.var "ilkRate") = .ok (.int (Int.ofNat ilkRate.toNat)) :=
      vatEvalExpr_varUInt256 (by
        change (locals.insert "ceilingDebt" (.int (Int.ofNat ceilingDebt.toNat))).get?
          "ilkRate" = some (.int (Int.ofNat ilkRate.toNat))
        rw [store_get_ne _ _ (by decide)]
        exact hilkRate)
    have hceilingAfter :
        evalExpr? config { contract := contract, locals := localsCeiling } evm
          (.var "ceilingDebt") = .ok (.int (Int.ofNat ceilingDebt.toNat)) :=
      vatEvalExpr_varUInt256 (by simp [localsCeiling])
    exact evalExpr_fork_mul_guard_true hilkArtNewAfter hilkRateAfter hceilingAfter
      hguard
  exact execForkMulUintIntoOk "ceilingDebt" (.var "ilkArtNew") (.var "ilkRate")
    ilkArtNew ilkRate ceilingDebt hilkArtNewEval hilkRateEval hceilingDebt hfit
    hguardEval

theorem execFrobCeilingInkSpotCheckedOk {evm : EVM.State} {locals : Store}
    (ilkArtNew ilkRate ceilingDebt urnInkNew ilkSpot inkSpot : UInt256)
    (hilkArtNew : locals.get? "ilkArtNew" = some (.int (Int.ofNat ilkArtNew.toNat)))
    (hilkRate : locals.get? "ilkRate" = some (.int (Int.ofNat ilkRate.toNat)))
    (hurnInkNew : locals.get? "urnInkNew" = some (.int (Int.ofNat urnInkNew.toNat)))
    (hilkSpot : locals.get? "ilkSpot" = some (.int (Int.ofNat ilkSpot.toNat)))
    (hceilingDebt : ceilingDebt = UInt256.mul ilkArtNew ilkRate)
    (hceilingFit : ilkArtNew.toNat * ilkRate.toNat < UInt256.size)
    (hceilingGuard :
      ilkRate.toNat = 0 ∨ ceilingDebt.toNat / ilkRate.toNat = ilkArtNew.toNat)
    (hinkSpot : inkSpot = UInt256.mul urnInkNew ilkSpot)
    (hinkFit : urnInkNew.toNat * ilkSpot.toNat < UInt256.size)
    (hinkGuard : ilkSpot.toNat = 0 ∨ inkSpot.toNat / ilkSpot.toNat = urnInkNew.toNat) :
    ExecBlock config { contract := contract, locals := locals } evm
      (checkedMulUintInto "ceilingDebt" (.var "ilkArtNew") (.var "ilkRate") ++
        checkedMulUintInto "inkSpot" (.var "urnInkNew") (.var "ilkSpot"))
      (.ok
        { contract := contract,
          locals :=
            (locals.insert "ceilingDebt" (.int (Int.ofNat ceilingDebt.toNat))).insert
              "inkSpot" (.int (Int.ofNat inkSpot.toNat)) }
        evm) := by
  let localsCeiling :=
    locals.insert "ceilingDebt" (.int (Int.ofNat ceilingDebt.toNat))
  have hilkArtNewEval :
      evalExpr? config { contract := contract, locals := locals } evm (.var "ilkArtNew") =
        .ok (.int (Int.ofNat ilkArtNew.toNat)) :=
    vatEvalExpr_varUInt256 hilkArtNew
  have hilkRateEval :
      evalExpr? config { contract := contract, locals := locals } evm (.var "ilkRate") =
        .ok (.int (Int.ofNat ilkRate.toNat)) :=
    vatEvalExpr_varUInt256 hilkRate
  have hceilingGuardEval :
      evalExpr? config
        { contract := contract, locals := localsCeiling } evm
        (eitherExpr (.binary .eq (.var "ilkRate") (.intLit 0))
          (.binary .eq (.binary .div (.var "ceilingDebt") (.var "ilkRate"))
            (.var "ilkArtNew"))) =
        .ok (.bool true) := by
    have hilkArtNewAfter :
        evalExpr? config { contract := contract, locals := localsCeiling } evm
          (.var "ilkArtNew") = .ok (.int (Int.ofNat ilkArtNew.toNat)) :=
      vatEvalExpr_varUInt256 (by
        change (locals.insert "ceilingDebt" (.int (Int.ofNat ceilingDebt.toNat))).get?
          "ilkArtNew" = some (.int (Int.ofNat ilkArtNew.toNat))
        rw [store_get_ne _ _ (by decide)]
        exact hilkArtNew)
    have hilkRateAfter :
        evalExpr? config { contract := contract, locals := localsCeiling } evm
          (.var "ilkRate") = .ok (.int (Int.ofNat ilkRate.toNat)) :=
      vatEvalExpr_varUInt256 (by
        change (locals.insert "ceilingDebt" (.int (Int.ofNat ceilingDebt.toNat))).get?
          "ilkRate" = some (.int (Int.ofNat ilkRate.toNat))
        rw [store_get_ne _ _ (by decide)]
        exact hilkRate)
    have hceilingAfter :
        evalExpr? config { contract := contract, locals := localsCeiling } evm
          (.var "ceilingDebt") = .ok (.int (Int.ofNat ceilingDebt.toNat)) :=
      vatEvalExpr_varUInt256 (by simp [localsCeiling])
    exact evalExpr_fork_mul_guard_true hilkArtNewAfter hilkRateAfter hceilingAfter
      hceilingGuard
  have hceilingBlock :
      ExecBlock config { contract := contract, locals := locals } evm
        (checkedMulUintInto "ceilingDebt" (.var "ilkArtNew") (.var "ilkRate"))
        (.ok { contract := contract, locals := localsCeiling } evm) := by
    exact execForkMulUintIntoOk "ceilingDebt" (.var "ilkArtNew") (.var "ilkRate")
      ilkArtNew ilkRate ceilingDebt hilkArtNewEval hilkRateEval hceilingDebt
      hceilingFit hceilingGuardEval
  have hurnInkNewEval :
      evalExpr? config { contract := contract, locals := localsCeiling } evm
        (.var "urnInkNew") = .ok (.int (Int.ofNat urnInkNew.toNat)) :=
    vatEvalExpr_varUInt256 (by
      change (locals.insert "ceilingDebt" (.int (Int.ofNat ceilingDebt.toNat))).get?
        "urnInkNew" = some (.int (Int.ofNat urnInkNew.toNat))
      rw [store_get_ne _ _ (by decide)]
      exact hurnInkNew)
  have hilkSpotEval :
      evalExpr? config { contract := contract, locals := localsCeiling } evm
        (.var "ilkSpot") = .ok (.int (Int.ofNat ilkSpot.toNat)) :=
    vatEvalExpr_varUInt256 (by
      change (locals.insert "ceilingDebt" (.int (Int.ofNat ceilingDebt.toNat))).get?
        "ilkSpot" = some (.int (Int.ofNat ilkSpot.toNat))
      rw [store_get_ne _ _ (by decide)]
      exact hilkSpot)
  have hinkGuardEval :
      evalExpr? config
        { contract := contract,
          locals := localsCeiling.insert "inkSpot" (.int (Int.ofNat inkSpot.toNat)) }
        evm
        (eitherExpr (.binary .eq (.var "ilkSpot") (.intLit 0))
          (.binary .eq (.binary .div (.var "inkSpot") (.var "ilkSpot"))
            (.var "urnInkNew"))) =
        .ok (.bool true) := by
    have hurnInkAfter :
        evalExpr? config
          { contract := contract,
            locals := localsCeiling.insert "inkSpot" (.int (Int.ofNat inkSpot.toNat)) }
          evm (.var "urnInkNew") = .ok (.int (Int.ofNat urnInkNew.toNat)) :=
      vatEvalExpr_varUInt256 (by
        change ((locals.insert "ceilingDebt" (.int (Int.ofNat ceilingDebt.toNat))).insert
          "inkSpot" (.int (Int.ofNat inkSpot.toNat))).get? "urnInkNew" =
          some (.int (Int.ofNat urnInkNew.toNat))
        rw [store_get_ne _ _ (by decide)]
        rw [store_get_ne _ _ (by decide)]
        exact hurnInkNew)
    have hspotAfter :
        evalExpr? config
          { contract := contract,
            locals := localsCeiling.insert "inkSpot" (.int (Int.ofNat inkSpot.toNat)) }
          evm (.var "ilkSpot") = .ok (.int (Int.ofNat ilkSpot.toNat)) :=
      vatEvalExpr_varUInt256 (by
        change ((locals.insert "ceilingDebt" (.int (Int.ofNat ceilingDebt.toNat))).insert
          "inkSpot" (.int (Int.ofNat inkSpot.toNat))).get? "ilkSpot" =
          some (.int (Int.ofNat ilkSpot.toNat))
        rw [store_get_ne _ _ (by decide)]
        rw [store_get_ne _ _ (by decide)]
        exact hilkSpot)
    have hinkAfter :
        evalExpr? config
          { contract := contract,
            locals := localsCeiling.insert "inkSpot" (.int (Int.ofNat inkSpot.toNat)) }
          evm (.var "inkSpot") = .ok (.int (Int.ofNat inkSpot.toNat)) :=
      vatEvalExpr_varUInt256 (by simp [localsCeiling])
    exact evalExpr_fork_mul_guard_true hurnInkAfter hspotAfter hinkAfter hinkGuard
  have hinkBlock :
      ExecBlock config { contract := contract, locals := localsCeiling } evm
        (checkedMulUintInto "inkSpot" (.var "urnInkNew") (.var "ilkSpot"))
        (.ok
          { contract := contract,
            locals := localsCeiling.insert "inkSpot" (.int (Int.ofNat inkSpot.toNat)) }
          evm) := by
    exact execForkMulUintIntoOk "inkSpot" (.var "urnInkNew") (.var "ilkSpot")
      urnInkNew ilkSpot inkSpot hurnInkNewEval hilkSpotEval hinkSpot hinkFit
      hinkGuardEval
  have h := Reasoning.Refinement.execBlock_append hceilingBlock hinkBlock
  simpa [localsCeiling, List.append_assoc] using h

theorem execFrobCeilingSafetyOk {evm : EVM.State} {locals : Store}
    (ilkArtNew ilkRate ceilingDebt urnInkNew ilkSpot inkSpot : UInt256)
    (hilkArtNew : locals.get? "ilkArtNew" = some (.int (Int.ofNat ilkArtNew.toNat)))
    (hilkRate : locals.get? "ilkRate" = some (.int (Int.ofNat ilkRate.toNat)))
    (hurnInkNew : locals.get? "urnInkNew" = some (.int (Int.ofNat urnInkNew.toNat)))
    (hilkSpot : locals.get? "ilkSpot" = some (.int (Int.ofNat ilkSpot.toNat)))
    (hceilingDebt : ceilingDebt = UInt256.mul ilkArtNew ilkRate)
    (hceilingFit : ilkArtNew.toNat * ilkRate.toNat < UInt256.size)
    (hceilingGuard :
      ilkRate.toNat = 0 ∨ ceilingDebt.toNat / ilkRate.toNat = ilkArtNew.toNat)
    (hinkSpot : inkSpot = UInt256.mul urnInkNew ilkSpot)
    (hinkFit : urnInkNew.toNat * ilkSpot.toNat < UInt256.size)
    (hinkGuard : ilkSpot.toNat = 0 ∨ inkSpot.toNat / ilkSpot.toNat = urnInkNew.toNat)
    (hceilingReq :
      evalExpr? config
        { contract := contract,
          locals :=
            (locals.insert "ceilingDebt" (.int (Int.ofNat ceilingDebt.toNat))).insert
              "inkSpot" (.int (Int.ofNat inkSpot.toNat)) }
        evm
        (eitherExpr
          (.binary .le (.var "dart") (.intLit 0))
          (bothExpr
            (.binary .le (.var "ceilingDebt") (.var "ilkLine"))
            (.binary .le (.var "debtNew") (.storage LineRef)))) =
        .ok (.bool true))
    (hsafeReq :
      evalExpr? config
        { contract := contract,
          locals :=
            (locals.insert "ceilingDebt" (.int (Int.ofNat ceilingDebt.toNat))).insert
              "inkSpot" (.int (Int.ofNat inkSpot.toNat)) }
        evm
        (eitherExpr
          (bothExpr
            (.binary .le (.var "dart") (.intLit 0))
            (.binary .ge (.var "dink") (.intLit 0)))
          (.binary .le (.var "tab") (.var "inkSpot"))) =
        .ok (.bool true)) :
    ExecBlock config { contract := contract, locals := locals } evm
      (checkedMulUintInto "ceilingDebt" (.var "ilkArtNew") (.var "ilkRate") ++
        checkedMulUintInto "inkSpot" (.var "urnInkNew") (.var "ilkSpot") ++
        [ .require
            (eitherExpr
              (.binary .le (.var "dart") (.intLit 0))
              (bothExpr
                (.binary .le (.var "ceilingDebt") (.var "ilkLine"))
                (.binary .le (.var "debtNew") (.storage LineRef)))),
          .require
            (eitherExpr
              (bothExpr
                (.binary .le (.var "dart") (.intLit 0))
                (.binary .ge (.var "dink") (.intLit 0)))
              (.binary .le (.var "tab") (.var "inkSpot"))) ])
      (.ok
        { contract := contract,
          locals :=
            (locals.insert "ceilingDebt" (.int (Int.ofNat ceilingDebt.toNat))).insert
              "inkSpot" (.int (Int.ofNat inkSpot.toNat)) }
        evm) := by
  let localsFinal :=
    (locals.insert "ceilingDebt" (.int (Int.ofNat ceilingDebt.toNat))).insert
      "inkSpot" (.int (Int.ofNat inkSpot.toNat))
  have hmul :
      ExecBlock config { contract := contract, locals := locals } evm
        (checkedMulUintInto "ceilingDebt" (.var "ilkArtNew") (.var "ilkRate") ++
          checkedMulUintInto "inkSpot" (.var "urnInkNew") (.var "ilkSpot"))
        (.ok { contract := contract, locals := localsFinal } evm) := by
    simpa [localsFinal] using
      execFrobCeilingInkSpotCheckedOk
        (evm := evm) (locals := locals)
        ilkArtNew ilkRate ceilingDebt urnInkNew ilkSpot inkSpot
        hilkArtNew hilkRate hurnInkNew hilkSpot hceilingDebt hceilingFit
        hceilingGuard hinkSpot hinkFit hinkGuard
  have hreqs :
      ExecBlock config { contract := contract, locals := localsFinal } evm
        [ .require
            (eitherExpr
              (.binary .le (.var "dart") (.intLit 0))
              (bothExpr
                (.binary .le (.var "ceilingDebt") (.var "ilkLine"))
                (.binary .le (.var "debtNew") (.storage LineRef)))),
          .require
            (eitherExpr
              (bothExpr
                (.binary .le (.var "dart") (.intLit 0))
                (.binary .ge (.var "dink") (.intLit 0)))
              (.binary .le (.var "tab") (.var "inkSpot"))) ]
        (.ok { contract := contract, locals := localsFinal } evm) := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · simpa [localsFinal] using hceilingReq
    · exact ExecBlock.consNormal (ExecStmt.requireTrue (by
        simpa [localsFinal] using hsafeReq)) ExecBlock.nil
  have h := Reasoning.Refinement.execBlock_append hmul hreqs
  simpa [localsFinal, List.append_assoc] using h

theorem execFrobCeilingRequireRevert {evm : EVM.State} {locals : Store}
    (ilkArtNew ilkRate ceilingDebt urnInkNew ilkSpot inkSpot : UInt256)
    (hilkArtNew : locals.get? "ilkArtNew" = some (.int (Int.ofNat ilkArtNew.toNat)))
    (hilkRate : locals.get? "ilkRate" = some (.int (Int.ofNat ilkRate.toNat)))
    (hurnInkNew : locals.get? "urnInkNew" = some (.int (Int.ofNat urnInkNew.toNat)))
    (hilkSpot : locals.get? "ilkSpot" = some (.int (Int.ofNat ilkSpot.toNat)))
    (hceilingDebt : ceilingDebt = UInt256.mul ilkArtNew ilkRate)
    (hceilingFit : ilkArtNew.toNat * ilkRate.toNat < UInt256.size)
    (hceilingGuard :
      ilkRate.toNat = 0 ∨ ceilingDebt.toNat / ilkRate.toNat = ilkArtNew.toNat)
    (hinkSpot : inkSpot = UInt256.mul urnInkNew ilkSpot)
    (hinkFit : urnInkNew.toNat * ilkSpot.toNat < UInt256.size)
    (hinkGuard : ilkSpot.toNat = 0 ∨ inkSpot.toNat / ilkSpot.toNat = urnInkNew.toNat)
    (hceilingReq :
      evalExpr? config
        { contract := contract,
          locals :=
            (locals.insert "ceilingDebt" (.int (Int.ofNat ceilingDebt.toNat))).insert
              "inkSpot" (.int (Int.ofNat inkSpot.toNat)) }
        evm
        (eitherExpr
          (.binary .le (.var "dart") (.intLit 0))
          (bothExpr
            (.binary .le (.var "ceilingDebt") (.var "ilkLine"))
            (.binary .le (.var "debtNew") (.storage LineRef)))) =
        .ok (.bool false)) :
    ExecBlock config { contract := contract, locals := locals } evm
      (checkedMulUintInto "ceilingDebt" (.var "ilkArtNew") (.var "ilkRate") ++
        checkedMulUintInto "inkSpot" (.var "urnInkNew") (.var "ilkSpot") ++
        [ .require
            (eitherExpr
              (.binary .le (.var "dart") (.intLit 0))
              (bothExpr
                (.binary .le (.var "ceilingDebt") (.var "ilkLine"))
                (.binary .le (.var "debtNew") (.storage LineRef)))) ])
      .reverted := by
  let localsFinal :=
    (locals.insert "ceilingDebt" (.int (Int.ofNat ceilingDebt.toNat))).insert
      "inkSpot" (.int (Int.ofNat inkSpot.toNat))
  have hmul :
      ExecBlock config { contract := contract, locals := locals } evm
        (checkedMulUintInto "ceilingDebt" (.var "ilkArtNew") (.var "ilkRate") ++
          checkedMulUintInto "inkSpot" (.var "urnInkNew") (.var "ilkSpot"))
        (.ok { contract := contract, locals := localsFinal } evm) := by
    simpa [localsFinal] using
      execFrobCeilingInkSpotCheckedOk
        (evm := evm) (locals := locals)
        ilkArtNew ilkRate ceilingDebt urnInkNew ilkSpot inkSpot
        hilkArtNew hilkRate hurnInkNew hilkSpot hceilingDebt hceilingFit
        hceilingGuard hinkSpot hinkFit hinkGuard
  have hreq :
      ExecBlock config { contract := contract, locals := localsFinal } evm
        [ .require
            (eitherExpr
              (.binary .le (.var "dart") (.intLit 0))
              (bothExpr
                (.binary .le (.var "ceilingDebt") (.var "ilkLine"))
                (.binary .le (.var "debtNew") (.storage LineRef)))) ]
        .reverted := by
    exact ExecBlock.consRevert (ExecStmt.requireFalse (by
      simpa [localsFinal] using hceilingReq))
  have h := Reasoning.Refinement.execBlock_append hmul hreq
  simpa [localsFinal, List.append_assoc] using h

theorem execFrobSafetyRequireRevert {evm : EVM.State} {locals : Store}
    (ilkArtNew ilkRate ceilingDebt urnInkNew ilkSpot inkSpot : UInt256)
    (hilkArtNew : locals.get? "ilkArtNew" = some (.int (Int.ofNat ilkArtNew.toNat)))
    (hilkRate : locals.get? "ilkRate" = some (.int (Int.ofNat ilkRate.toNat)))
    (hurnInkNew : locals.get? "urnInkNew" = some (.int (Int.ofNat urnInkNew.toNat)))
    (hilkSpot : locals.get? "ilkSpot" = some (.int (Int.ofNat ilkSpot.toNat)))
    (hceilingDebt : ceilingDebt = UInt256.mul ilkArtNew ilkRate)
    (hceilingFit : ilkArtNew.toNat * ilkRate.toNat < UInt256.size)
    (hceilingGuard :
      ilkRate.toNat = 0 ∨ ceilingDebt.toNat / ilkRate.toNat = ilkArtNew.toNat)
    (hinkSpot : inkSpot = UInt256.mul urnInkNew ilkSpot)
    (hinkFit : urnInkNew.toNat * ilkSpot.toNat < UInt256.size)
    (hinkGuard : ilkSpot.toNat = 0 ∨ inkSpot.toNat / ilkSpot.toNat = urnInkNew.toNat)
    (hceilingReq :
      evalExpr? config
        { contract := contract,
          locals :=
            (locals.insert "ceilingDebt" (.int (Int.ofNat ceilingDebt.toNat))).insert
              "inkSpot" (.int (Int.ofNat inkSpot.toNat)) }
        evm
        (eitherExpr
          (.binary .le (.var "dart") (.intLit 0))
          (bothExpr
            (.binary .le (.var "ceilingDebt") (.var "ilkLine"))
            (.binary .le (.var "debtNew") (.storage LineRef)))) =
        .ok (.bool true))
    (hsafeReq :
      evalExpr? config
        { contract := contract,
          locals :=
            (locals.insert "ceilingDebt" (.int (Int.ofNat ceilingDebt.toNat))).insert
              "inkSpot" (.int (Int.ofNat inkSpot.toNat)) }
        evm
        (eitherExpr
          (bothExpr
            (.binary .le (.var "dart") (.intLit 0))
            (.binary .ge (.var "dink") (.intLit 0)))
          (.binary .le (.var "tab") (.var "inkSpot"))) =
        .ok (.bool false)) :
    ExecBlock config { contract := contract, locals := locals } evm
      (checkedMulUintInto "ceilingDebt" (.var "ilkArtNew") (.var "ilkRate") ++
        checkedMulUintInto "inkSpot" (.var "urnInkNew") (.var "ilkSpot") ++
        [ .require
            (eitherExpr
              (.binary .le (.var "dart") (.intLit 0))
              (bothExpr
                (.binary .le (.var "ceilingDebt") (.var "ilkLine"))
                (.binary .le (.var "debtNew") (.storage LineRef)))),
          .require
            (eitherExpr
              (bothExpr
                (.binary .le (.var "dart") (.intLit 0))
                (.binary .ge (.var "dink") (.intLit 0)))
              (.binary .le (.var "tab") (.var "inkSpot"))) ])
      .reverted := by
  let localsFinal :=
    (locals.insert "ceilingDebt" (.int (Int.ofNat ceilingDebt.toNat))).insert
      "inkSpot" (.int (Int.ofNat inkSpot.toNat))
  have hmul :
      ExecBlock config { contract := contract, locals := locals } evm
        (checkedMulUintInto "ceilingDebt" (.var "ilkArtNew") (.var "ilkRate") ++
          checkedMulUintInto "inkSpot" (.var "urnInkNew") (.var "ilkSpot"))
        (.ok { contract := contract, locals := localsFinal } evm) := by
    simpa [localsFinal] using
      execFrobCeilingInkSpotCheckedOk
        (evm := evm) (locals := locals)
        ilkArtNew ilkRate ceilingDebt urnInkNew ilkSpot inkSpot
        hilkArtNew hilkRate hurnInkNew hilkSpot hceilingDebt hceilingFit
        hceilingGuard hinkSpot hinkFit hinkGuard
  have hreqs :
      ExecBlock config { contract := contract, locals := localsFinal } evm
        [ .require
            (eitherExpr
              (.binary .le (.var "dart") (.intLit 0))
              (bothExpr
                (.binary .le (.var "ceilingDebt") (.var "ilkLine"))
                (.binary .le (.var "debtNew") (.storage LineRef)))),
          .require
            (eitherExpr
              (bothExpr
                (.binary .le (.var "dart") (.intLit 0))
                (.binary .ge (.var "dink") (.intLit 0)))
              (.binary .le (.var "tab") (.var "inkSpot"))) ]
        .reverted := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · simpa [localsFinal] using hceilingReq
    · exact ExecBlock.consRevert (ExecStmt.requireFalse (by
        simpa [localsFinal] using hsafeReq))
  have h := Reasoning.Refinement.execBlock_append hmul hreqs
  simpa [localsFinal, List.append_assoc] using h

theorem execFrobAuthorizationDustOk {evm : EVM.State} {locals : Store}
    (hu :
      evalExpr? config { contract := contract, locals := locals } evm
        (eitherExpr
          (bothExpr
            (.binary .le (.var "dart") (.intLit 0))
            (.binary .ge (.var "dink") (.intLit 0)))
          (wishExpr (.var "u") sender)) =
        .ok (.bool true))
    (hv :
      evalExpr? config { contract := contract, locals := locals } evm
        (eitherExpr (.binary .le (.var "dink") (.intLit 0)) (wishExpr (.var "v") sender)) =
        .ok (.bool true))
    (hw :
      evalExpr? config { contract := contract, locals := locals } evm
        (eitherExpr (.binary .ge (.var "dart") (.intLit 0)) (wishExpr (.var "w") sender)) =
        .ok (.bool true))
    (hdust :
      evalExpr? config { contract := contract, locals := locals } evm
        (eitherExpr (.binary .eq (.var "urnArtNew") (.intLit 0))
          (.binary .ge (.var "tab") (.var "ilkDust"))) =
        .ok (.bool true)) :
    ExecBlock config { contract := contract, locals := locals } evm
      [ .require
          (eitherExpr
            (bothExpr
              (.binary .le (.var "dart") (.intLit 0))
              (.binary .ge (.var "dink") (.intLit 0)))
            (wishExpr (.var "u") sender)),
        .require
          (eitherExpr (.binary .le (.var "dink") (.intLit 0)) (wishExpr (.var "v") sender)),
        .require
          (eitherExpr (.binary .ge (.var "dart") (.intLit 0)) (wishExpr (.var "w") sender)),
        .require
          (eitherExpr (.binary .eq (.var "urnArtNew") (.intLit 0))
            (.binary .ge (.var "tab") (.var "ilkDust"))) ]
      (.ok { contract := contract, locals := locals } evm) := by
  refine ExecBlock.consNormal (ExecStmt.requireTrue hu) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue hv) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue hw) ?_
  exact ExecBlock.consNormal (ExecStmt.requireTrue hdust) ExecBlock.nil

theorem execFrobAuthorizationDustRevertU {evm : EVM.State} {locals : Store}
    (hu :
      evalExpr? config { contract := contract, locals := locals } evm
        (eitherExpr
          (bothExpr
            (.binary .le (.var "dart") (.intLit 0))
            (.binary .ge (.var "dink") (.intLit 0)))
          (wishExpr (.var "u") sender)) =
        .ok (.bool false)) :
    ExecBlock config { contract := contract, locals := locals } evm
      [ .require
          (eitherExpr
            (bothExpr
              (.binary .le (.var "dart") (.intLit 0))
              (.binary .ge (.var "dink") (.intLit 0)))
            (wishExpr (.var "u") sender)),
        .require
          (eitherExpr (.binary .le (.var "dink") (.intLit 0)) (wishExpr (.var "v") sender)),
        .require
          (eitherExpr (.binary .ge (.var "dart") (.intLit 0)) (wishExpr (.var "w") sender)),
        .require
          (eitherExpr (.binary .eq (.var "urnArtNew") (.intLit 0))
            (.binary .ge (.var "tab") (.var "ilkDust"))) ]
      .reverted := by
  exact ExecBlock.consRevert (ExecStmt.requireFalse hu)

theorem execFrobAuthorizationDustRevertV {evm : EVM.State} {locals : Store}
    (hu :
      evalExpr? config { contract := contract, locals := locals } evm
        (eitherExpr
          (bothExpr
            (.binary .le (.var "dart") (.intLit 0))
            (.binary .ge (.var "dink") (.intLit 0)))
          (wishExpr (.var "u") sender)) =
        .ok (.bool true))
    (hv :
      evalExpr? config { contract := contract, locals := locals } evm
        (eitherExpr (.binary .le (.var "dink") (.intLit 0)) (wishExpr (.var "v") sender)) =
        .ok (.bool false)) :
    ExecBlock config { contract := contract, locals := locals } evm
      [ .require
          (eitherExpr
            (bothExpr
              (.binary .le (.var "dart") (.intLit 0))
              (.binary .ge (.var "dink") (.intLit 0)))
            (wishExpr (.var "u") sender)),
        .require
          (eitherExpr (.binary .le (.var "dink") (.intLit 0)) (wishExpr (.var "v") sender)),
        .require
          (eitherExpr (.binary .ge (.var "dart") (.intLit 0)) (wishExpr (.var "w") sender)),
        .require
          (eitherExpr (.binary .eq (.var "urnArtNew") (.intLit 0))
            (.binary .ge (.var "tab") (.var "ilkDust"))) ]
      .reverted := by
  refine ExecBlock.consNormal (ExecStmt.requireTrue hu) ?_
  exact ExecBlock.consRevert (ExecStmt.requireFalse hv)

theorem execFrobAuthorizationDustRevertW {evm : EVM.State} {locals : Store}
    (hu :
      evalExpr? config { contract := contract, locals := locals } evm
        (eitherExpr
          (bothExpr
            (.binary .le (.var "dart") (.intLit 0))
            (.binary .ge (.var "dink") (.intLit 0)))
          (wishExpr (.var "u") sender)) =
        .ok (.bool true))
    (hv :
      evalExpr? config { contract := contract, locals := locals } evm
        (eitherExpr (.binary .le (.var "dink") (.intLit 0)) (wishExpr (.var "v") sender)) =
        .ok (.bool true))
    (hw :
      evalExpr? config { contract := contract, locals := locals } evm
        (eitherExpr (.binary .ge (.var "dart") (.intLit 0)) (wishExpr (.var "w") sender)) =
        .ok (.bool false)) :
    ExecBlock config { contract := contract, locals := locals } evm
      [ .require
          (eitherExpr
            (bothExpr
              (.binary .le (.var "dart") (.intLit 0))
              (.binary .ge (.var "dink") (.intLit 0)))
            (wishExpr (.var "u") sender)),
        .require
          (eitherExpr (.binary .le (.var "dink") (.intLit 0)) (wishExpr (.var "v") sender)),
        .require
          (eitherExpr (.binary .ge (.var "dart") (.intLit 0)) (wishExpr (.var "w") sender)),
        .require
          (eitherExpr (.binary .eq (.var "urnArtNew") (.intLit 0))
            (.binary .ge (.var "tab") (.var "ilkDust"))) ]
      .reverted := by
  refine ExecBlock.consNormal (ExecStmt.requireTrue hu) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue hv) ?_
  exact ExecBlock.consRevert (ExecStmt.requireFalse hw)

theorem execFrobAuthorizationDustRevertDust {evm : EVM.State} {locals : Store}
    (hu :
      evalExpr? config { contract := contract, locals := locals } evm
        (eitherExpr
          (bothExpr
            (.binary .le (.var "dart") (.intLit 0))
            (.binary .ge (.var "dink") (.intLit 0)))
          (wishExpr (.var "u") sender)) =
        .ok (.bool true))
    (hv :
      evalExpr? config { contract := contract, locals := locals } evm
        (eitherExpr (.binary .le (.var "dink") (.intLit 0)) (wishExpr (.var "v") sender)) =
        .ok (.bool true))
    (hw :
      evalExpr? config { contract := contract, locals := locals } evm
        (eitherExpr (.binary .ge (.var "dart") (.intLit 0)) (wishExpr (.var "w") sender)) =
        .ok (.bool true))
    (hdust :
      evalExpr? config { contract := contract, locals := locals } evm
        (eitherExpr (.binary .eq (.var "urnArtNew") (.intLit 0))
          (.binary .ge (.var "tab") (.var "ilkDust"))) =
        .ok (.bool false)) :
    ExecBlock config { contract := contract, locals := locals } evm
      [ .require
          (eitherExpr
            (bothExpr
              (.binary .le (.var "dart") (.intLit 0))
              (.binary .ge (.var "dink") (.intLit 0)))
            (wishExpr (.var "u") sender)),
        .require
          (eitherExpr (.binary .le (.var "dink") (.intLit 0)) (wishExpr (.var "v") sender)),
        .require
          (eitherExpr (.binary .ge (.var "dart") (.intLit 0)) (wishExpr (.var "w") sender)),
        .require
          (eitherExpr (.binary .eq (.var "urnArtNew") (.intLit 0))
            (.binary .ge (.var "tab") (.var "ilkDust"))) ]
      .reverted := by
  refine ExecBlock.consNormal (ExecStmt.requireTrue hu) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue hv) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue hw) ?_
  exact ExecBlock.consRevert (ExecStmt.requireFalse hdust)

theorem execFrobAuthorizationDustOk_from_sourceConds {evm : EVM.State}
    {I : ExecutionEnv} {locals : Store}
    (uWish vWish wWish urnArtNew tab ilkDust : UInt256)
    (hdart : locals.get? "dart" = some (frobDartValue I))
    (hdink : locals.get? "dink" = some (frobDinkValue I))
    (hu : locals.get? "u" = some (frobUValue I))
    (hv : locals.get? "v" = some (frobVValue I))
    (hw : locals.get? "w" = some (frobWValue I))
    (hbaseCan : locals.get? "can" = none)
    (hsrc : evm.executionEnv.source = I.source)
    (hloadU :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (frobUWishSlot I) = uWish)
    (hloadV :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (frobVWishSlot I) = vWish)
    (hloadW :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (frobWWishSlot I) = wWish)
    (hurnArtNew :
      locals.get? "urnArtNew" = some (.int (Int.ofNat urnArtNew.toNat)))
    (htab : locals.get? "tab" = some (.int (Int.ofNat tab.toNat)))
    (hilkDust : locals.get? "ilkDust" = some (.int (Int.ofNat ilkDust.toNat)))
    (huOk :
      (frobDartInt I ≤ 0 ∧ 0 ≤ frobDinkInt I) ∨
        (uWish = ⟨1⟩ ∨ frobUMaskedWord I = hopeSourceWord I))
    (hvOk :
      frobDinkInt I ≤ 0 ∨
        (vWish = ⟨1⟩ ∨ frobVMaskedWord I = hopeSourceWord I))
    (hwOk :
      0 ≤ frobDartInt I ∨
        (wWish = ⟨1⟩ ∨ frobWMaskedWord I = hopeSourceWord I))
    (hdustOk : urnArtNew.toNat = 0 ∨ ilkDust.toNat ≤ tab.toNat) :
    ExecBlock config { contract := contract, locals := locals } evm
      [ .require
          (eitherExpr
            (bothExpr
              (.binary .le (.var "dart") (.intLit 0))
              (.binary .ge (.var "dink") (.intLit 0)))
            (wishExpr (.var "u") sender)),
        .require
          (eitherExpr (.binary .le (.var "dink") (.intLit 0)) (wishExpr (.var "v") sender)),
        .require
          (eitherExpr (.binary .ge (.var "dart") (.intLit 0)) (wishExpr (.var "w") sender)),
        .require
          (eitherExpr (.binary .eq (.var "urnArtNew") (.intLit 0))
            (.binary .ge (.var "tab") (.var "ilkDust"))) ]
      (.ok { contract := contract, locals := locals } evm) := by
  exact execFrobAuthorizationDustOk
    (evalExpr_frob_auth_u_req_true (evm := evm) (I := I)
      uWish hdart hdink hu hbaseCan hsrc hloadU huOk)
    (evalExpr_frob_auth_v_req_true (evm := evm) (I := I)
      vWish hdink hv hbaseCan hsrc hloadV hvOk)
    (evalExpr_frob_auth_w_req_true (evm := evm) (I := I)
      wWish hdart hw hbaseCan hsrc hloadW hwOk)
    (evalExpr_frob_dust_req_true urnArtNew tab ilkDust hurnArtNew htab hilkDust
      hdustOk)

theorem assignStorageRef_frob_urn_ink (evm : EVM.State) (I : ExecutionEnv)
    (locals : Store) (urnInkNew : UInt256)
    (hsz196 : 196 ≤ I.calldata.size)
    (hi : locals.get? "i" = some (frobIValue I))
    (hu : locals.get? "u" = some (frobUValue I))
    (hbase : locals.get? "urns" = none) :
    let evm' := Solm.EVM.storageStore evm evm.executionEnv.codeOwner
      (frobUrnInkSourceSlot I) urnInkNew
    assignStorageRef? config { contract := contract, locals := locals } evm .storage
      (urnsF (.var "i") (.var "u") "ink") (.int (Int.ofNat urnInkNew.toNat)) =
      .ok ({ contract := contract, locals := locals }, evm') := by
  intro evm'
  exact assignStorageRef_storage_scalar
    (hbase := hbase)
    (her := evalStorageRef_frob_urn_ink_locals evm I locals hsz196 hi hu)
    (hty := frobStorageType_urn_ink I)
    (hloc := frobStorageLayout_urn_ink_source I)
    (hstore := by simpa [evm'] using
      vatStorageLocStore_uint256 evm (frobUrnInkSourceSlot I) urnInkNew)

theorem assignStorageRef_frob_urn_art (evm : EVM.State) (I : ExecutionEnv)
    (locals : Store) (urnArtNew : UInt256)
    (hsz196 : 196 ≤ I.calldata.size)
    (hi : locals.get? "i" = some (frobIValue I))
    (hu : locals.get? "u" = some (frobUValue I))
    (hbase : locals.get? "urns" = none) :
    let evm' := Solm.EVM.storageStore evm evm.executionEnv.codeOwner
      (frobUrnArtSourceSlot I) urnArtNew
    assignStorageRef? config { contract := contract, locals := locals } evm .storage
      (urnsF (.var "i") (.var "u") "art") (.int (Int.ofNat urnArtNew.toNat)) =
      .ok ({ contract := contract, locals := locals }, evm') := by
  intro evm'
  exact assignStorageRef_storage_scalar
    (hbase := hbase)
    (her := evalStorageRef_frob_urn_art_locals evm I locals hsz196 hi hu)
    (hty := frobStorageType_urn_art I)
    (hloc := frobStorageLayout_urn_art_source I)
    (hstore := by simpa [evm'] using
      vatStorageLocStore_uint256 evm (frobUrnArtSourceSlot I) urnArtNew)

theorem assignStorageRef_frob_ilk_art (evm : EVM.State) (I : ExecutionEnv)
    (locals : Store) (ilkArtNew : UInt256)
    (hsz196 : 196 ≤ I.calldata.size)
    (hi : locals.get? "i" = some (frobIValue I))
    (hbase : locals.get? "ilks" = none) :
    let evm' := Solm.EVM.storageStore evm evm.executionEnv.codeOwner
      (frobIlkArtSourceSlot I) ilkArtNew
    assignStorageRef? config { contract := contract, locals := locals } evm .storage
      (ilksF (.var "i") "Art") (.int (Int.ofNat ilkArtNew.toNat)) =
      .ok ({ contract := contract, locals := locals }, evm') := by
  intro evm'
  exact assignStorageRef_storage_scalar
    (hbase := hbase)
    (her := evalStorageRef_frob_ilk_art_locals evm I locals hsz196 hi)
    (hty := frobStorageType_ilk_art I)
    (hloc := frobStorageLayout_ilk_art_source I)
    (hstore := by simpa [evm'] using
      vatStorageLocStore_uint256 evm (frobIlkArtSourceSlot I) ilkArtNew)

theorem assignStorageRef_frob_ilk_rate (evm : EVM.State) (I : ExecutionEnv)
    (locals : Store) (ilkRate : UInt256)
    (hsz196 : 196 ≤ I.calldata.size)
    (hi : locals.get? "i" = some (frobIValue I))
    (hbase : locals.get? "ilks" = none) :
    let evm' := Solm.EVM.storageStore evm evm.executionEnv.codeOwner
      (frobIlkRateSourceSlot I) ilkRate
    assignStorageRef? config { contract := contract, locals := locals } evm .storage
      (ilksF (.var "i") "rate") (.int (Int.ofNat ilkRate.toNat)) =
      .ok ({ contract := contract, locals := locals }, evm') := by
  intro evm'
  exact assignStorageRef_storage_scalar
    (hbase := hbase)
    (her := evalStorageRef_frob_ilk_rate_locals evm I locals hsz196 hi)
    (hty := frobStorageType_ilk_rate I)
    (hloc := frobStorageLayout_ilk_rate_source I)
    (hstore := by simpa [evm'] using
      vatStorageLocStore_uint256 evm (frobIlkRateSourceSlot I) ilkRate)

theorem assignStorageRef_frob_ilk_spot (evm : EVM.State) (I : ExecutionEnv)
    (locals : Store) (ilkSpot : UInt256)
    (hsz196 : 196 ≤ I.calldata.size)
    (hi : locals.get? "i" = some (frobIValue I))
    (hbase : locals.get? "ilks" = none) :
    let evm' := Solm.EVM.storageStore evm evm.executionEnv.codeOwner
      (frobIlkSpotSourceSlot I) ilkSpot
    assignStorageRef? config { contract := contract, locals := locals } evm .storage
      (ilksF (.var "i") "spot") (.int (Int.ofNat ilkSpot.toNat)) =
      .ok ({ contract := contract, locals := locals }, evm') := by
  intro evm'
  exact assignStorageRef_storage_scalar
    (hbase := hbase)
    (her := evalStorageRef_frob_ilk_spot_locals evm I locals hsz196 hi)
    (hty := frobStorageType_ilk_spot I)
    (hloc := frobStorageLayout_ilk_spot_source I)
    (hstore := by simpa [evm'] using
      vatStorageLocStore_uint256 evm (frobIlkSpotSourceSlot I) ilkSpot)

theorem assignStorageRef_frob_ilk_line (evm : EVM.State) (I : ExecutionEnv)
    (locals : Store) (ilkLine : UInt256)
    (hsz196 : 196 ≤ I.calldata.size)
    (hi : locals.get? "i" = some (frobIValue I))
    (hbase : locals.get? "ilks" = none) :
    let evm' := Solm.EVM.storageStore evm evm.executionEnv.codeOwner
      (frobIlkLineSourceSlot I) ilkLine
    assignStorageRef? config { contract := contract, locals := locals } evm .storage
      (ilksF (.var "i") "line") (.int (Int.ofNat ilkLine.toNat)) =
      .ok ({ contract := contract, locals := locals }, evm') := by
  intro evm'
  exact assignStorageRef_storage_scalar
    (hbase := hbase)
    (her := evalStorageRef_frob_ilk_line_locals evm I locals hsz196 hi)
    (hty := frobStorageType_ilk_line I)
    (hloc := frobStorageLayout_ilk_line_source I)
    (hstore := by simpa [evm'] using
      vatStorageLocStore_uint256 evm (frobIlkLineSourceSlot I) ilkLine)

theorem assignStorageRef_frob_ilk_dust (evm : EVM.State) (I : ExecutionEnv)
    (locals : Store) (ilkDust : UInt256)
    (hsz196 : 196 ≤ I.calldata.size)
    (hi : locals.get? "i" = some (frobIValue I))
    (hbase : locals.get? "ilks" = none) :
    let evm' := Solm.EVM.storageStore evm evm.executionEnv.codeOwner
      (frobIlkDustSourceSlot I) ilkDust
    assignStorageRef? config { contract := contract, locals := locals } evm .storage
      (ilksF (.var "i") "dust") (.int (Int.ofNat ilkDust.toNat)) =
      .ok ({ contract := contract, locals := locals }, evm') := by
  intro evm'
  exact assignStorageRef_storage_scalar
    (hbase := hbase)
    (her := evalStorageRef_frob_ilk_dust_locals evm I locals hsz196 hi)
    (hty := frobStorageType_ilk_dust I)
    (hloc := frobStorageLayout_ilk_dust_source I)
    (hstore := by simpa [evm'] using
      vatStorageLocStore_uint256 evm (frobIlkDustSourceSlot I) ilkDust)

theorem assignStorageRef_frob_gem_v (evm : EVM.State) (I : ExecutionEnv)
    (locals : Store) (gemNew : UInt256)
    (hsz196 : 196 ≤ I.calldata.size)
    (hi : locals.get? "i" = some (frobIValue I))
    (hv : locals.get? "v" = some (frobVValue I))
    (hbase : locals.get? "gem" = none) :
    let evm' := Solm.EVM.storageStore evm evm.executionEnv.codeOwner
      (frobGemVSourceSlot I) gemNew
    assignStorageRef? config { contract := contract, locals := locals } evm .storage
      (gemRef (.var "i") (.var "v")) (.int (Int.ofNat gemNew.toNat)) =
      .ok ({ contract := contract, locals := locals }, evm') := by
  intro evm'
  exact assignStorageRef_storage_scalar
    (hbase := hbase)
    (her := evalStorageRef_frob_gem_v_locals evm I locals hsz196 hi hv)
    (hty := frobStorageType_gem_v I)
    (hloc := frobStorageLayout_gem_v_source I)
    (hstore := by simpa [evm'] using
      vatStorageLocStore_uint256 evm (frobGemVSourceSlot I) gemNew)

theorem assignStorageRef_frob_dai_w (evm : EVM.State) (I : ExecutionEnv)
    (locals : Store) (daiNew : UInt256)
    (hw : locals.get? "w" = some (frobWValue I))
    (hbase : locals.get? "dai" = none) :
    let evm' := Solm.EVM.storageStore evm evm.executionEnv.codeOwner
      (frobDaiWSourceSlot I) daiNew
    assignStorageRef? config { contract := contract, locals := locals } evm .storage
      (daiRef (.var "w")) (.int (Int.ofNat daiNew.toNat)) =
      .ok ({ contract := contract, locals := locals }, evm') := by
  intro evm'
  exact assignStorageRef_storage_scalar
    (hbase := hbase)
    (her := evalStorageRef_frob_dai_w_locals evm I locals hw)
    (hty := frobStorageType_dai_w I)
    (hloc := frobStorageLayout_dai_w_source I)
    (hstore := by simpa [evm'] using
      vatStorageLocStore_uint256 evm (frobDaiWSourceSlot I) daiNew)

theorem execCheckedSubSignedOk {evm : EVM.State} {locals : Store}
    {x y : Expr} {name : Ident} {old new : UInt256} {subtrahendInt : Int}
    (hx : evalExpr? config { contract := contract, locals := locals } evm x =
      .ok (.int (Int.ofNat old.toNat)))
    (hy : evalExpr? config { contract := contract, locals := locals } evm y =
      .ok (.int subtrahendInt))
    (hwrap :
      (Int.ofNat old.toNat - subtrahendInt) % (Int.ofNat EVM.wordModulus) =
        Int.ofNat new.toNat)
    (hyAfter :
      evalExpr? config
        { contract := contract, locals := locals.insert name (.int (Int.ofNat new.toNat)) }
        evm y = .ok (.int subtrahendInt))
    (hxAfter :
      evalExpr? config
        { contract := contract, locals := locals.insert name (.int (Int.ofNat new.toNat)) }
        evm x = .ok (.int (Int.ofNat old.toNat)))
    (hguardNeg : subtrahendInt ≤ 0 ∨ new.toNat ≤ old.toNat)
    (hguardPos : 0 ≤ subtrahendInt ∨ old.toNat ≤ new.toNat) :
    ExecBlock config { contract := contract, locals := locals } evm
      (checkedSubSignedInto name x y)
      (.ok
        { contract := contract, locals := locals.insert name (.int (Int.ofNat new.toNat)) }
        evm) := by
  let locals' := locals.insert name (.int (Int.ofNat new.toNat))
  have hlet :
      evalExpr? config { contract := contract, locals := locals } evm
        (wordWrap256 (.binary .sub x y)) =
        .ok (.int (Int.ofNat new.toNat)) :=
    evalExpr_fold_wordWrapSub_ok hx hy hwrap
  have hnewEval :
      evalExpr? config { contract := contract, locals := locals' } evm (.var name) =
        .ok (.int (Int.ofNat new.toNat)) := by
    exact vatEvalExpr_varUInt256 (by simp [locals'])
  have hguardNegEval :
      evalExpr? config { contract := contract, locals := locals' } evm
        (eitherExpr (.binary .le y (.intLit 0)) (.binary .le (.var name) x)) =
        .ok (.bool true) :=
    evalSignedSubGuardNeg_true (by simpa [locals'] using hyAfter) hnewEval
      (by simpa [locals'] using hxAfter) hguardNeg
  have hguardPosEval :
      evalExpr? config { contract := contract, locals := locals' } evm
        (eitherExpr (.binary .ge y (.intLit 0)) (.binary .ge (.var name) x)) =
        .ok (.bool true) :=
    evalSignedSubGuardPos_true (by simpa [locals'] using hyAfter) hnewEval
      (by simpa [locals'] using hxAfter) hguardPos
  change ExecBlock config { contract := contract, locals := locals } evm
    [ .letDecl name (some uint256) (wordWrap256 (.binary .sub x y)),
      .require (eitherExpr (.binary .le y (.intLit 0)) (.binary .le (.var name) x)),
      .require (eitherExpr (.binary .ge y (.intLit 0)) (.binary .ge (.var name) x)) ]
    (.ok { contract := contract, locals := locals' } evm)
  refine ExecBlock.consNormal (ExecStmt.letDecl hlet) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue hguardNegEval) ?_
  exact ExecBlock.consNormal (ExecStmt.requireTrue hguardPosEval) ExecBlock.nil

theorem execCheckedAddSignedOk {evm : EVM.State} {locals : Store}
    {x y : Expr} {name : Ident} {old new addend : UInt256} {addendInt : Int}
    (hx : evalExpr? config { contract := contract, locals := locals } evm x =
      .ok (.int (Int.ofNat old.toNat)))
    (hy : evalExpr? config { contract := contract, locals := locals } evm y =
      .ok (.int addendInt))
    (haddend : addendInt % (Int.ofNat EVM.wordModulus) = Int.ofNat addend.toNat)
    (hnew : new = addend + old)
    (hyAfter :
      evalExpr? config
        { contract := contract, locals := locals.insert name (.int (Int.ofNat new.toNat)) }
        evm y = .ok (.int addendInt))
    (hxAfter :
      evalExpr? config
        { contract := contract, locals := locals.insert name (.int (Int.ofNat new.toNat)) }
        evm x = .ok (.int (Int.ofNat old.toNat)))
    (hguardNeg : 0 ≤ addendInt ∨ new.toNat ≤ old.toNat)
    (hguardPos : addendInt ≤ 0 ∨ old.toNat ≤ new.toNat) :
    ExecBlock config { contract := contract, locals := locals } evm
      (checkedAddSignedInto name x y)
      (.ok
        { contract := contract, locals := locals.insert name (.int (Int.ofNat new.toNat)) }
        evm) := by
  let locals' := locals.insert name (.int (Int.ofNat new.toNat))
  have hlet :
      evalExpr? config { contract := contract, locals := locals } evm
        (wordWrap256 (.binary .add x y)) =
        .ok (.int (Int.ofNat new.toNat)) :=
    evalExpr_fold_wordWrapAdd_ok hx hy haddend hnew
  have hnewEval :
      evalExpr? config { contract := contract, locals := locals' } evm (.var name) =
        .ok (.int (Int.ofNat new.toNat)) := by
    exact vatEvalExpr_varUInt256 (by simp [locals'])
  have hguardNegEval :
      evalExpr? config { contract := contract, locals := locals' } evm
        (eitherExpr (.binary .ge y (.intLit 0)) (.binary .le (.var name) x)) =
        .ok (.bool true) :=
    evalSignedAddGuardNeg_true (by simpa [locals'] using hyAfter) hnewEval
      (by simpa [locals'] using hxAfter) hguardNeg
  have hguardPosEval :
      evalExpr? config { contract := contract, locals := locals' } evm
        (eitherExpr (.binary .le y (.intLit 0)) (.binary .ge (.var name) x)) =
        .ok (.bool true) :=
    evalSignedAddGuardPos_true (by simpa [locals'] using hyAfter) hnewEval
      (by simpa [locals'] using hxAfter) hguardPos
  change ExecBlock config { contract := contract, locals := locals } evm
    [ .letDecl name (some uint256) (wordWrap256 (.binary .add x y)),
      .require (eitherExpr (.binary .ge y (.intLit 0)) (.binary .le (.var name) x)),
      .require (eitherExpr (.binary .le y (.intLit 0)) (.binary .ge (.var name) x)) ]
    (.ok { contract := contract, locals := locals' } evm)
  refine ExecBlock.consNormal (ExecStmt.letDecl hlet) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue hguardNegEval) ?_
  exact ExecBlock.consNormal (ExecStmt.requireTrue hguardPosEval) ExecBlock.nil

theorem execCheckedAddSignedRevertGuardNeg {evm : EVM.State} {locals : Store}
    {x y : Expr} {name : Ident} {old new addend : UInt256} {addendInt : Int}
    (hx : evalExpr? config { contract := contract, locals := locals } evm x =
      .ok (.int (Int.ofNat old.toNat)))
    (hy : evalExpr? config { contract := contract, locals := locals } evm y =
      .ok (.int addendInt))
    (haddend : addendInt % (Int.ofNat EVM.wordModulus) = Int.ofNat addend.toNat)
    (hnew : new = addend + old)
    (hyAfter :
      evalExpr? config
        { contract := contract, locals := locals.insert name (.int (Int.ofNat new.toNat)) }
        evm y = .ok (.int addendInt))
    (hxAfter :
      evalExpr? config
        { contract := contract, locals := locals.insert name (.int (Int.ofNat new.toNat)) }
        evm x = .ok (.int (Int.ofNat old.toNat)))
    (hcond : addendInt < 0 ∧ old.toNat < new.toNat) :
    ExecBlock config { contract := contract, locals := locals } evm
      (checkedAddSignedInto name x y)
      .reverted := by
  let locals' := locals.insert name (.int (Int.ofNat new.toNat))
  have hlet :
      evalExpr? config { contract := contract, locals := locals } evm
        (wordWrap256 (.binary .add x y)) =
        .ok (.int (Int.ofNat new.toNat)) :=
    evalExpr_fold_wordWrapAdd_ok hx hy haddend hnew
  have hnewEval :
      evalExpr? config { contract := contract, locals := locals' } evm (.var name) =
        .ok (.int (Int.ofNat new.toNat)) := by
    exact vatEvalExpr_varUInt256 (by simp [locals'])
  have hguardNegEval :
      evalExpr? config { contract := contract, locals := locals' } evm
        (eitherExpr (.binary .ge y (.intLit 0)) (.binary .le (.var name) x)) =
        .ok (.bool false) :=
    evalSignedAddGuardNeg_false (by simpa [locals'] using hyAfter) hnewEval
      (by simpa [locals'] using hxAfter) hcond
  change ExecBlock config { contract := contract, locals := locals } evm
    [ .letDecl name (some uint256) (wordWrap256 (.binary .add x y)),
      .require (eitherExpr (.binary .ge y (.intLit 0)) (.binary .le (.var name) x)),
      .require (eitherExpr (.binary .le y (.intLit 0)) (.binary .ge (.var name) x)) ]
    .reverted
  refine ExecBlock.consNormal (ExecStmt.letDecl hlet) ?_
  exact ExecBlock.consRevert (ExecStmt.requireFalse hguardNegEval)

theorem execCheckedAddSignedRevertGuardPos {evm : EVM.State} {locals : Store}
    {x y : Expr} {name : Ident} {old new addend : UInt256} {addendInt : Int}
    (hx : evalExpr? config { contract := contract, locals := locals } evm x =
      .ok (.int (Int.ofNat old.toNat)))
    (hy : evalExpr? config { contract := contract, locals := locals } evm y =
      .ok (.int addendInt))
    (haddend : addendInt % (Int.ofNat EVM.wordModulus) = Int.ofNat addend.toNat)
    (hnew : new = addend + old)
    (hyAfter :
      evalExpr? config
        { contract := contract, locals := locals.insert name (.int (Int.ofNat new.toNat)) }
        evm y = .ok (.int addendInt))
    (hxAfter :
      evalExpr? config
        { contract := contract, locals := locals.insert name (.int (Int.ofNat new.toNat)) }
        evm x = .ok (.int (Int.ofNat old.toNat)))
    (hguardNeg :
      evalExpr? config
        { contract := contract, locals := locals.insert name (.int (Int.ofNat new.toNat)) }
        evm (eitherExpr (.binary .ge y (.intLit 0)) (.binary .le (.var name) x)) =
      .ok (.bool true))
    (hcond : 0 < addendInt ∧ new.toNat < old.toNat) :
    ExecBlock config { contract := contract, locals := locals } evm
      (checkedAddSignedInto name x y)
      .reverted := by
  let locals' := locals.insert name (.int (Int.ofNat new.toNat))
  have hlet :
      evalExpr? config { contract := contract, locals := locals } evm
        (wordWrap256 (.binary .add x y)) =
        .ok (.int (Int.ofNat new.toNat)) :=
    evalExpr_fold_wordWrapAdd_ok hx hy haddend hnew
  have hnewEval :
      evalExpr? config { contract := contract, locals := locals' } evm (.var name) =
        .ok (.int (Int.ofNat new.toNat)) := by
    exact vatEvalExpr_varUInt256 (by simp [locals'])
  have hguardPosEval :
      evalExpr? config { contract := contract, locals := locals' } evm
        (eitherExpr (.binary .le y (.intLit 0)) (.binary .ge (.var name) x)) =
        .ok (.bool false) :=
    evalSignedAddGuardPos_false (by simpa [locals'] using hyAfter) hnewEval
      (by simpa [locals'] using hxAfter) hcond
  change ExecBlock config { contract := contract, locals := locals } evm
    [ .letDecl name (some uint256) (wordWrap256 (.binary .add x y)),
      .require (eitherExpr (.binary .ge y (.intLit 0)) (.binary .le (.var name) x)),
      .require (eitherExpr (.binary .le y (.intLit 0)) (.binary .ge (.var name) x)) ]
    .reverted
  refine ExecBlock.consNormal (ExecStmt.letDecl hlet) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (by simpa [locals'] using hguardNeg)) ?_
  exact ExecBlock.consRevert (ExecStmt.requireFalse hguardPosEval)

theorem execFrobGemSubCheckedOk {evm : EVM.State} {I : ExecutionEnv}
    (locals : Store) (gemOld gemNew : UInt256)
    (hsz196 : 196 ≤ I.calldata.size)
    (hi : locals.get? "i" = some (frobIValue I))
    (hv : locals.get? "v" = some (frobVValue I))
    (hdink : locals.get? "dink" = some (frobDinkValue I))
    (hbase : locals.get? "gem" = none)
    (hload :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (frobGemVSourceSlot I) = gemOld)
    (hnew : gemNew = UInt256.sub gemOld (frobDinkWord I))
    (hguardNeg : frobDinkInt I ≤ 0 ∨ gemNew.toNat ≤ gemOld.toNat)
    (hguardPos : 0 ≤ frobDinkInt I ∨ gemOld.toNat ≤ gemNew.toNat) :
    ExecBlock config { contract := contract, locals := locals } evm
      (checkedSubSignedInto "gemNew" (.storage (gemRef (.var "i") (.var "v"))) (.var "dink"))
      (.ok
        { contract := contract,
          locals := locals.insert "gemNew" (.int (Int.ofNat gemNew.toNat)) }
        evm) := by
  let locals' := locals.insert "gemNew" (.int (Int.ofNat gemNew.toNat))
  have hstorage :
      evalExpr? config { contract := contract, locals := locals } evm
        (.storage (gemRef (.var "i") (.var "v"))) =
        .ok (.int (Int.ofNat gemOld.toNat)) := by
    rw [evalExpr_frob_gem_v_locals locals hsz196 hi hv hbase, hload]
  have hdinkEval :
      evalExpr? config { contract := contract, locals := locals } evm (.var "dink") =
        .ok (.int (frobDinkInt I)) :=
    vatEvalExpr_varInt (by simpa [frobDinkValue] using hdink)
  have hdinkAfter :
      evalExpr? config { contract := contract, locals := locals' } evm (.var "dink") =
        .ok (.int (frobDinkInt I)) := by
    exact vatEvalExpr_varInt (by
      change (locals.insert "gemNew" (.int (Int.ofNat gemNew.toNat))).get? "dink" =
        some (.int (frobDinkInt I))
      rw [store_get_ne _ _ (by decide)]
      simpa [frobDinkValue] using hdink)
  have hiAfter : locals'.get? "i" = some (frobIValue I) := by
    change (locals.insert "gemNew" (.int (Int.ofNat gemNew.toNat))).get? "i" =
      some (frobIValue I)
    rw [store_get_ne _ _ (by decide)]
    exact hi
  have hvAfter : locals'.get? "v" = some (frobVValue I) := by
    change (locals.insert "gemNew" (.int (Int.ofNat gemNew.toNat))).get? "v" =
      some (frobVValue I)
    rw [store_get_ne _ _ (by decide)]
    exact hv
  have hbaseAfter : locals'.get? "gem" = none := by
    change (locals.insert "gemNew" (.int (Int.ofNat gemNew.toNat))).get? "gem" = none
    rw [store_get_ne _ _ (by decide)]
    exact hbase
  have hstorageAfter :
      evalExpr? config { contract := contract, locals := locals' } evm
        (.storage (gemRef (.var "i") (.var "v"))) =
        .ok (.int (Int.ofNat gemOld.toNat)) := by
    rw [evalExpr_frob_gem_v_locals locals' hsz196 hiAfter hvAfter hbaseAfter, hload]
  exact execCheckedSubSignedOk
    (x := .storage (gemRef (.var "i") (.var "v"))) (y := .var "dink")
    (name := "gemNew") hstorage hdinkEval
    (by simpa [hnew] using
      signedSubWrap gemOld (frobDinkWord I) (frobDinkInt I) (frobDinkInt_mod_word I))
    (by simpa [locals'] using hdinkAfter)
    (by simpa [locals'] using hstorageAfter)
    hguardNeg hguardPos

theorem execFrobGemSubCheckedRevertGuardNeg {evm : EVM.State} {I : ExecutionEnv}
    (locals : Store) (gemOld gemNew : UInt256)
    (hsz196 : 196 ≤ I.calldata.size)
    (hi : locals.get? "i" = some (frobIValue I))
    (hv : locals.get? "v" = some (frobVValue I))
    (hdink : locals.get? "dink" = some (frobDinkValue I))
    (hbase : locals.get? "gem" = none)
    (hload :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (frobGemVSourceSlot I) = gemOld)
    (hnew : gemNew = UInt256.sub gemOld (frobDinkWord I))
    (hfail :
      ¬ (UInt256.sgt (frobDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.gt gemNew gemOld = ⟨0⟩)) :
    ExecBlock config { contract := contract, locals := locals } evm
      (checkedSubSignedInto "gemNew" (.storage (gemRef (.var "i") (.var "v"))) (.var "dink"))
      .reverted := by
  let locals' := locals.insert "gemNew" (.int (Int.ofNat gemNew.toNat))
  have hstorage :
      evalExpr? config { contract := contract, locals := locals } evm
        (.storage (gemRef (.var "i") (.var "v"))) =
        .ok (.int (Int.ofNat gemOld.toNat)) := by
    rw [evalExpr_frob_gem_v_locals locals hsz196 hi hv hbase, hload]
  have hdinkEval :
      evalExpr? config { contract := contract, locals := locals } evm (.var "dink") =
        .ok (.int (frobDinkInt I)) :=
    vatEvalExpr_varInt (by simpa [frobDinkValue] using hdink)
  have hdinkAfter :
      evalExpr? config { contract := contract, locals := locals' } evm (.var "dink") =
        .ok (.int (frobDinkInt I)) := by
    exact vatEvalExpr_varInt (by
      change (locals.insert "gemNew" (.int (Int.ofNat gemNew.toNat))).get? "dink" =
        some (.int (frobDinkInt I))
      rw [store_get_ne _ _ (by decide)]
      simpa [frobDinkValue] using hdink)
  have hiAfter : locals'.get? "i" = some (frobIValue I) := by
    change (locals.insert "gemNew" (.int (Int.ofNat gemNew.toNat))).get? "i" =
      some (frobIValue I)
    rw [store_get_ne _ _ (by decide)]
    exact hi
  have hvAfter : locals'.get? "v" = some (frobVValue I) := by
    change (locals.insert "gemNew" (.int (Int.ofNat gemNew.toNat))).get? "v" =
      some (frobVValue I)
    rw [store_get_ne _ _ (by decide)]
    exact hv
  have hbaseAfter : locals'.get? "gem" = none := by
    change (locals.insert "gemNew" (.int (Int.ofNat gemNew.toNat))).get? "gem" = none
    rw [store_get_ne _ _ (by decide)]
    exact hbase
  have hstorageAfter :
      evalExpr? config { contract := contract, locals := locals' } evm
        (.storage (gemRef (.var "i") (.var "v"))) =
        .ok (.int (Int.ofNat gemOld.toNat)) := by
    rw [evalExpr_frob_gem_v_locals locals' hsz196 hiAfter hvAfter hbaseAfter, hload]
  exact execCheckedSubSignedRevertGuardNeg
    (x := .storage (gemRef (.var "i") (.var "v"))) (y := .var "dink")
    (name := "gemNew") hstorage hdinkEval
    (by simpa [hnew] using
      signedSubWrap gemOld (frobDinkWord I) (frobDinkInt I) (frobDinkInt_mod_word I))
    (by simpa [locals'] using hdinkAfter)
    (by simpa [locals'] using hstorageAfter)
    (frobDinkSubGuardNegFailCond hfail)

theorem execFrobGemSubCheckedRevertGuardPos {evm : EVM.State} {I : ExecutionEnv}
    (locals : Store) (gemOld gemNew : UInt256)
    (hsz196 : 196 ≤ I.calldata.size)
    (hi : locals.get? "i" = some (frobIValue I))
    (hv : locals.get? "v" = some (frobVValue I))
    (hdink : locals.get? "dink" = some (frobDinkValue I))
    (hbase : locals.get? "gem" = none)
    (hload :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (frobGemVSourceSlot I) = gemOld)
    (hnew : gemNew = UInt256.sub gemOld (frobDinkWord I))
    (hguardNeg :
      UInt256.sgt (frobDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.gt gemNew gemOld = ⟨0⟩)
    (hfail :
      ¬ (UInt256.slt (frobDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.lt gemNew gemOld = ⟨0⟩)) :
    ExecBlock config { contract := contract, locals := locals } evm
      (checkedSubSignedInto "gemNew" (.storage (gemRef (.var "i") (.var "v"))) (.var "dink"))
      .reverted := by
  let locals' := locals.insert "gemNew" (.int (Int.ofNat gemNew.toNat))
  have hstorage :
      evalExpr? config { contract := contract, locals := locals } evm
        (.storage (gemRef (.var "i") (.var "v"))) =
        .ok (.int (Int.ofNat gemOld.toNat)) := by
    rw [evalExpr_frob_gem_v_locals locals hsz196 hi hv hbase, hload]
  have hdinkEval :
      evalExpr? config { contract := contract, locals := locals } evm (.var "dink") =
        .ok (.int (frobDinkInt I)) :=
    vatEvalExpr_varInt (by simpa [frobDinkValue] using hdink)
  have hnewEval :
      evalExpr? config { contract := contract, locals := locals' } evm (.var "gemNew") =
        .ok (.int (Int.ofNat gemNew.toNat)) := by
    exact vatEvalExpr_varUInt256 (by simp [locals'])
  have hdinkAfter :
      evalExpr? config { contract := contract, locals := locals' } evm (.var "dink") =
        .ok (.int (frobDinkInt I)) := by
    exact vatEvalExpr_varInt (by
      change (locals.insert "gemNew" (.int (Int.ofNat gemNew.toNat))).get? "dink" =
        some (.int (frobDinkInt I))
      rw [store_get_ne _ _ (by decide)]
      simpa [frobDinkValue] using hdink)
  have hiAfter : locals'.get? "i" = some (frobIValue I) := by
    change (locals.insert "gemNew" (.int (Int.ofNat gemNew.toNat))).get? "i" =
      some (frobIValue I)
    rw [store_get_ne _ _ (by decide)]
    exact hi
  have hvAfter : locals'.get? "v" = some (frobVValue I) := by
    change (locals.insert "gemNew" (.int (Int.ofNat gemNew.toNat))).get? "v" =
      some (frobVValue I)
    rw [store_get_ne _ _ (by decide)]
    exact hv
  have hbaseAfter : locals'.get? "gem" = none := by
    change (locals.insert "gemNew" (.int (Int.ofNat gemNew.toNat))).get? "gem" = none
    rw [store_get_ne _ _ (by decide)]
    exact hbase
  have hstorageAfter :
      evalExpr? config { contract := contract, locals := locals' } evm
        (.storage (gemRef (.var "i") (.var "v"))) =
        .ok (.int (Int.ofNat gemOld.toNat)) := by
    rw [evalExpr_frob_gem_v_locals locals' hsz196 hiAfter hvAfter hbaseAfter, hload]
  have hguardNegEval :
      evalExpr? config { contract := contract, locals := locals' } evm
        (eitherExpr (.binary .le (.var "dink") (.intLit 0))
          (.binary .le (.var "gemNew") (.storage (gemRef (.var "i") (.var "v"))))) =
        .ok (.bool true) :=
    evalSignedSubGuardNeg_true hdinkAfter hnewEval hstorageAfter
      (frobDinkSubGuardNegCond hguardNeg)
  exact execCheckedSubSignedRevertGuardPos
    (x := .storage (gemRef (.var "i") (.var "v"))) (y := .var "dink")
    (name := "gemNew") hstorage hdinkEval
    (by simpa [hnew] using
      signedSubWrap gemOld (frobDinkWord I) (frobDinkInt I) (frobDinkInt_mod_word I))
    (by simpa [locals'] using hdinkAfter)
    (by simpa [locals'] using hstorageAfter)
    (by simpa [locals'] using hguardNegEval)
    (frobDinkSubGuardPosFailCond hfail)

theorem execFrobGemUpdateOk {evm : EVM.State} {I : ExecutionEnv}
    (locals : Store) (gemOld gemNew : UInt256)
    (hsz196 : 196 ≤ I.calldata.size)
    (hi : locals.get? "i" = some (frobIValue I))
    (hv : locals.get? "v" = some (frobVValue I))
    (hdink : locals.get? "dink" = some (frobDinkValue I))
    (hbase : locals.get? "gem" = none)
    (hload :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (frobGemVSourceSlot I) = gemOld)
    (hnew : gemNew = UInt256.sub gemOld (frobDinkWord I))
    (hguardNeg : frobDinkInt I ≤ 0 ∨ gemNew.toNat ≤ gemOld.toNat)
    (hguardPos : 0 ≤ frobDinkInt I ∨ gemOld.toNat ≤ gemNew.toNat) :
    ExecBlock config { contract := contract, locals := locals } evm
      (checkedSubSignedInto "gemNew" (.storage (gemRef (.var "i") (.var "v"))) (.var "dink") ++
        [ .assign .storage (gemRef (.var "i") (.var "v")) (.var "gemNew") ])
      (.ok
        { contract := contract,
          locals := locals.insert "gemNew" (.int (Int.ofNat gemNew.toNat)) }
        (Solm.EVM.storageStore evm evm.executionEnv.codeOwner (frobGemVSourceSlot I)
          gemNew)) := by
  let localsGem := locals.insert "gemNew" (.int (Int.ofNat gemNew.toNat))
  let evmGem :=
    Solm.EVM.storageStore evm evm.executionEnv.codeOwner (frobGemVSourceSlot I) gemNew
  have hsub :
      ExecBlock config { contract := contract, locals := locals } evm
        (checkedSubSignedInto "gemNew" (.storage (gemRef (.var "i") (.var "v"))) (.var "dink"))
        (.ok { contract := contract, locals := localsGem } evm) := by
    exact execFrobGemSubCheckedOk (I := I) locals gemOld gemNew hsz196 hi hv hdink hbase
      hload hnew hguardNeg hguardPos
  have hnewEval :
      evalExpr? config { contract := contract, locals := localsGem } evm (.var "gemNew") =
        .ok (.int (Int.ofNat gemNew.toNat)) :=
    vatEvalExpr_varUInt256 (by simp [localsGem])
  have hiAfter : localsGem.get? "i" = some (frobIValue I) := by
    change (locals.insert "gemNew" (.int (Int.ofNat gemNew.toNat))).get? "i" =
      some (frobIValue I)
    rw [store_get_ne _ _ (by decide)]
    exact hi
  have hvAfter : localsGem.get? "v" = some (frobVValue I) := by
    change (locals.insert "gemNew" (.int (Int.ofNat gemNew.toNat))).get? "v" =
      some (frobVValue I)
    rw [store_get_ne _ _ (by decide)]
    exact hv
  have hbaseAfter : localsGem.get? "gem" = none := by
    change (locals.insert "gemNew" (.int (Int.ofNat gemNew.toNat))).get? "gem" = none
    rw [store_get_ne _ _ (by decide)]
    exact hbase
  have hassign :
      assignStorageRef? config { contract := contract, locals := localsGem } evm
        .storage (gemRef (.var "i") (.var "v")) (.int (Int.ofNat gemNew.toNat)) =
      .ok ({ contract := contract, locals := localsGem }, evmGem) := by
    simpa [evmGem] using
      assignStorageRef_frob_gem_v evm I localsGem gemNew hsz196 hiAfter hvAfter hbaseAfter
  have hassignBlock :
      ExecBlock config { contract := contract, locals := localsGem } evm
        [ .assign .storage (gemRef (.var "i") (.var "v")) (.var "gemNew") ]
        (.ok { contract := contract, locals := localsGem } evmGem) := by
    exact ExecBlock.consNormal (ExecStmt.assign hnewEval hassign) ExecBlock.nil
  have h := Reasoning.Refinement.execBlock_append hsub hassignBlock
  simpa [localsGem, evmGem, List.append_assoc] using h

theorem execFrobDaiAddCheckedOk {evm : EVM.State} {I : ExecutionEnv}
    (locals : Store) (daiOld daiNew dtabWord : UInt256) (dtab : Int)
    (hw : locals.get? "w" = some (frobWValue I))
    (hdtab : locals.get? "dtab" = some (.int dtab))
    (hbase : locals.get? "dai" = none)
    (hload :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (frobDaiWSourceSlot I) = daiOld)
    (hdtabMod : dtab % (Int.ofNat EVM.wordModulus) = Int.ofNat dtabWord.toNat)
    (hnew : daiNew = dtabWord + daiOld)
    (hguardNeg : 0 ≤ dtab ∨ daiNew.toNat ≤ daiOld.toNat)
    (hguardPos : dtab ≤ 0 ∨ daiOld.toNat ≤ daiNew.toNat) :
    ExecBlock config { contract := contract, locals := locals } evm
      (checkedAddSignedInto "daiNew" (.storage (daiRef (.var "w"))) (.var "dtab"))
      (.ok
        { contract := contract,
          locals := locals.insert "daiNew" (.int (Int.ofNat daiNew.toNat)) }
        evm) := by
  let locals' := locals.insert "daiNew" (.int (Int.ofNat daiNew.toNat))
  have hstorage :
      evalExpr? config { contract := contract, locals := locals } evm
        (.storage (daiRef (.var "w"))) =
        .ok (.int (Int.ofNat daiOld.toNat)) := by
    rw [evalExpr_frob_dai_w_locals locals hw hbase, hload]
  have hdtabEval :
      evalExpr? config { contract := contract, locals := locals } evm (.var "dtab") =
        .ok (.int dtab) :=
    vatEvalExpr_varInt hdtab
  have hdtabAfter :
      evalExpr? config { contract := contract, locals := locals' } evm (.var "dtab") =
        .ok (.int dtab) := by
    exact vatEvalExpr_varInt (by
      change (locals.insert "daiNew" (.int (Int.ofNat daiNew.toNat))).get? "dtab" =
        some (.int dtab)
      rw [store_get_ne _ _ (by decide)]
      exact hdtab)
  have hwAfter : locals'.get? "w" = some (frobWValue I) := by
    change (locals.insert "daiNew" (.int (Int.ofNat daiNew.toNat))).get? "w" =
      some (frobWValue I)
    rw [store_get_ne _ _ (by decide)]
    exact hw
  have hbaseAfter : locals'.get? "dai" = none := by
    change (locals.insert "daiNew" (.int (Int.ofNat daiNew.toNat))).get? "dai" = none
    rw [store_get_ne _ _ (by decide)]
    exact hbase
  have hstorageAfter :
      evalExpr? config { contract := contract, locals := locals' } evm
        (.storage (daiRef (.var "w"))) =
        .ok (.int (Int.ofNat daiOld.toNat)) := by
    rw [evalExpr_frob_dai_w_locals locals' hwAfter hbaseAfter, hload]
  exact execCheckedAddSignedOk
    (x := .storage (daiRef (.var "w"))) (y := .var "dtab")
    (name := "daiNew") hstorage hdtabEval hdtabMod hnew
    (by simpa [locals'] using hdtabAfter)
    (by simpa [locals'] using hstorageAfter)
    hguardNeg hguardPos

theorem execFrobDaiAddCheckedRevertGuardNeg {evm : EVM.State} {I : ExecutionEnv}
    (locals : Store) (daiOld daiNew dtabWord : UInt256) (dtab : Int)
    (hw : locals.get? "w" = some (frobWValue I))
    (hdtab : locals.get? "dtab" = some (.int dtab))
    (hbase : locals.get? "dai" = none)
    (hload :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (frobDaiWSourceSlot I) = daiOld)
    (hdtabMod : dtab % (Int.ofNat EVM.wordModulus) = Int.ofNat dtabWord.toNat)
    (hnew : daiNew = dtabWord + daiOld)
    (hfail :
      ¬ (UInt256.slt dtabWord ⟨0⟩ = ⟨0⟩ ∨
        UInt256.gt daiNew daiOld = ⟨0⟩))
    (hdtabLo : -((2 : Int) ^ 255) ≤ dtab)
    (hdtabHi : dtab < (2 : Int) ^ 255) :
    ExecBlock config { contract := contract, locals := locals } evm
      (checkedAddSignedInto "daiNew" (.storage (daiRef (.var "w"))) (.var "dtab"))
      .reverted := by
  let locals' := locals.insert "daiNew" (.int (Int.ofNat daiNew.toNat))
  have hstorage :
      evalExpr? config { contract := contract, locals := locals } evm
        (.storage (daiRef (.var "w"))) =
        .ok (.int (Int.ofNat daiOld.toNat)) := by
    rw [evalExpr_frob_dai_w_locals locals hw hbase, hload]
  have hdtabEval :
      evalExpr? config { contract := contract, locals := locals } evm (.var "dtab") =
        .ok (.int dtab) :=
    vatEvalExpr_varInt hdtab
  have hdtabAfter :
      evalExpr? config { contract := contract, locals := locals' } evm (.var "dtab") =
        .ok (.int dtab) := by
    exact vatEvalExpr_varInt (by
      change (locals.insert "daiNew" (.int (Int.ofNat daiNew.toNat))).get? "dtab" =
        some (.int dtab)
      rw [store_get_ne _ _ (by decide)]
      exact hdtab)
  have hwAfter : locals'.get? "w" = some (frobWValue I) := by
    change (locals.insert "daiNew" (.int (Int.ofNat daiNew.toNat))).get? "w" =
      some (frobWValue I)
    rw [store_get_ne _ _ (by decide)]
    exact hw
  have hbaseAfter : locals'.get? "dai" = none := by
    change (locals.insert "daiNew" (.int (Int.ofNat daiNew.toNat))).get? "dai" = none
    rw [store_get_ne _ _ (by decide)]
    exact hbase
  have hstorageAfter :
      evalExpr? config { contract := contract, locals := locals' } evm
        (.storage (daiRef (.var "w"))) =
        .ok (.int (Int.ofNat daiOld.toNat)) := by
    rw [evalExpr_frob_dai_w_locals locals' hwAfter hbaseAfter, hload]
  exact execCheckedAddSignedRevertGuardNeg
    (x := .storage (daiRef (.var "w"))) (y := .var "dtab")
    (name := "daiNew") hstorage hdtabEval hdtabMod hnew
    (by simpa [locals'] using hdtabAfter)
    (by simpa [locals'] using hstorageAfter)
    (signedAddGuardNegFalseCond_of_word hdtabLo hdtabHi hdtabMod hfail)

theorem execFrobDaiAddCheckedRevertGuardPos {evm : EVM.State} {I : ExecutionEnv}
    (locals : Store) (daiOld daiNew dtabWord : UInt256) (dtab : Int)
    (hw : locals.get? "w" = some (frobWValue I))
    (hdtab : locals.get? "dtab" = some (.int dtab))
    (hbase : locals.get? "dai" = none)
    (hload :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (frobDaiWSourceSlot I) = daiOld)
    (hdtabMod : dtab % (Int.ofNat EVM.wordModulus) = Int.ofNat dtabWord.toNat)
    (hnew : daiNew = dtabWord + daiOld)
    (hguardNeg :
      UInt256.slt dtabWord ⟨0⟩ = ⟨0⟩ ∨
        UInt256.gt daiNew daiOld = ⟨0⟩)
    (hfail :
      ¬ (UInt256.sgt dtabWord ⟨0⟩ = ⟨0⟩ ∨
        UInt256.lt daiNew daiOld = ⟨0⟩))
    (hdtabLo : -((2 : Int) ^ 255) ≤ dtab)
    (hdtabHi : dtab < (2 : Int) ^ 255) :
    ExecBlock config { contract := contract, locals := locals } evm
      (checkedAddSignedInto "daiNew" (.storage (daiRef (.var "w"))) (.var "dtab"))
      .reverted := by
  let locals' := locals.insert "daiNew" (.int (Int.ofNat daiNew.toNat))
  have hstorage :
      evalExpr? config { contract := contract, locals := locals } evm
        (.storage (daiRef (.var "w"))) =
        .ok (.int (Int.ofNat daiOld.toNat)) := by
    rw [evalExpr_frob_dai_w_locals locals hw hbase, hload]
  have hdtabEval :
      evalExpr? config { contract := contract, locals := locals } evm (.var "dtab") =
        .ok (.int dtab) :=
    vatEvalExpr_varInt hdtab
  have hdtabAfter :
      evalExpr? config { contract := contract, locals := locals' } evm (.var "dtab") =
        .ok (.int dtab) := by
    exact vatEvalExpr_varInt (by
      change (locals.insert "daiNew" (.int (Int.ofNat daiNew.toNat))).get? "dtab" =
        some (.int dtab)
      rw [store_get_ne _ _ (by decide)]
      exact hdtab)
  have hnewEval :
      evalExpr? config { contract := contract, locals := locals' } evm (.var "daiNew") =
        .ok (.int (Int.ofNat daiNew.toNat)) := by
    exact vatEvalExpr_varUInt256 (by simp [locals'])
  have hwAfter : locals'.get? "w" = some (frobWValue I) := by
    change (locals.insert "daiNew" (.int (Int.ofNat daiNew.toNat))).get? "w" =
      some (frobWValue I)
    rw [store_get_ne _ _ (by decide)]
    exact hw
  have hbaseAfter : locals'.get? "dai" = none := by
    change (locals.insert "daiNew" (.int (Int.ofNat daiNew.toNat))).get? "dai" = none
    rw [store_get_ne _ _ (by decide)]
    exact hbase
  have hstorageAfter :
      evalExpr? config { contract := contract, locals := locals' } evm
        (.storage (daiRef (.var "w"))) =
        .ok (.int (Int.ofNat daiOld.toNat)) := by
    rw [evalExpr_frob_dai_w_locals locals' hwAfter hbaseAfter, hload]
  have hguardNegEval :
      evalExpr? config { contract := contract, locals := locals' } evm
        (eitherExpr (.binary .ge (.var "dtab") (.intLit 0))
          (.binary .le (.var "daiNew") (.storage (daiRef (.var "w"))))) =
        .ok (.bool true) :=
    evalSignedAddGuardNeg_true hdtabAfter hnewEval hstorageAfter
      (signedAddGuardNegCond_of_word hdtabLo hdtabHi hdtabMod hguardNeg)
  exact execCheckedAddSignedRevertGuardPos
    (x := .storage (daiRef (.var "w"))) (y := .var "dtab")
    (name := "daiNew") hstorage hdtabEval hdtabMod hnew
    (by simpa [locals'] using hdtabAfter)
    (by simpa [locals'] using hstorageAfter)
    (by simpa [locals'] using hguardNegEval)
    (signedAddGuardPosFalseCond_of_word hdtabLo hdtabHi hdtabMod hfail)

theorem execFrobDaiUpdateOk {evm : EVM.State} {I : ExecutionEnv}
    (locals : Store) (daiOld daiNew dtabWord : UInt256) (dtab : Int)
    (hw : locals.get? "w" = some (frobWValue I))
    (hdtab : locals.get? "dtab" = some (.int dtab))
    (hbase : locals.get? "dai" = none)
    (hload :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (frobDaiWSourceSlot I) = daiOld)
    (hdtabMod : dtab % (Int.ofNat EVM.wordModulus) = Int.ofNat dtabWord.toNat)
    (hnew : daiNew = dtabWord + daiOld)
    (hguardNeg : 0 ≤ dtab ∨ daiNew.toNat ≤ daiOld.toNat)
    (hguardPos : dtab ≤ 0 ∨ daiOld.toNat ≤ daiNew.toNat) :
    ExecBlock config { contract := contract, locals := locals } evm
      (checkedAddSignedInto "daiNew" (.storage (daiRef (.var "w"))) (.var "dtab") ++
        [ .assign .storage (daiRef (.var "w")) (.var "daiNew") ])
      (.ok
        { contract := contract,
          locals := locals.insert "daiNew" (.int (Int.ofNat daiNew.toNat)) }
        (Solm.EVM.storageStore evm evm.executionEnv.codeOwner (frobDaiWSourceSlot I)
          daiNew)) := by
  let localsDai := locals.insert "daiNew" (.int (Int.ofNat daiNew.toNat))
  let evmDai :=
    Solm.EVM.storageStore evm evm.executionEnv.codeOwner (frobDaiWSourceSlot I) daiNew
  have hadd :
      ExecBlock config { contract := contract, locals := locals } evm
        (checkedAddSignedInto "daiNew" (.storage (daiRef (.var "w"))) (.var "dtab"))
        (.ok { contract := contract, locals := localsDai } evm) := by
    exact execFrobDaiAddCheckedOk (I := I) locals daiOld daiNew dtabWord dtab hw hdtab
      hbase hload hdtabMod hnew hguardNeg hguardPos
  have hnewEval :
      evalExpr? config { contract := contract, locals := localsDai } evm (.var "daiNew") =
        .ok (.int (Int.ofNat daiNew.toNat)) :=
    vatEvalExpr_varUInt256 (by simp [localsDai])
  have hwAfter : localsDai.get? "w" = some (frobWValue I) := by
    change (locals.insert "daiNew" (.int (Int.ofNat daiNew.toNat))).get? "w" =
      some (frobWValue I)
    rw [store_get_ne _ _ (by decide)]
    exact hw
  have hbaseAfter : localsDai.get? "dai" = none := by
    change (locals.insert "daiNew" (.int (Int.ofNat daiNew.toNat))).get? "dai" = none
    rw [store_get_ne _ _ (by decide)]
    exact hbase
  have hassign :
      assignStorageRef? config { contract := contract, locals := localsDai } evm
        .storage (daiRef (.var "w")) (.int (Int.ofNat daiNew.toNat)) =
      .ok ({ contract := contract, locals := localsDai }, evmDai) := by
    simpa [evmDai] using
      assignStorageRef_frob_dai_w evm I localsDai daiNew hwAfter hbaseAfter
  have hassignBlock :
      ExecBlock config { contract := contract, locals := localsDai } evm
        [ .assign .storage (daiRef (.var "w")) (.var "daiNew") ]
        (.ok { contract := contract, locals := localsDai } evmDai) := by
    exact ExecBlock.consNormal (ExecStmt.assign hnewEval hassign) ExecBlock.nil
  have h := Reasoning.Refinement.execBlock_append hadd hassignBlock
  simpa [localsDai, evmDai, List.append_assoc] using h

theorem execFrobFinalStoreTailGemRevertFromBlock {evm : EVM.State}
    {locals : Store}
    (hGem :
      ExecBlock config { contract := contract, locals := locals } evm
        (checkedSubSignedInto "gemNew" (.storage (gemRef (.var "i") (.var "v")))
          (.var "dink"))
        .reverted) :
    ExecBlock config { contract := contract, locals := locals } evm
      (checkedSubSignedInto "gemNew" (.storage (gemRef (.var "i") (.var "v")))
        (.var "dink") ++
        [ .assign .storage (gemRef (.var "i") (.var "v")) (.var "gemNew") ] ++
        checkedAddSignedInto "daiNew" (.storage (daiRef (.var "w"))) (.var "dtab") ++
        [ .assign .storage (daiRef (.var "w")) (.var "daiNew"),
          .assign .storage (urnsF (.var "i") (.var "u") "ink") (.var "urnInkNew"),
          .assign .storage (urnsF (.var "i") (.var "u") "art") (.var "urnArtNew"),
          .assign .storage (ilksF (.var "i") "Art") (.var "ilkArtNew"),
          .assign .storage (ilksF (.var "i") "rate") (.var "ilkRate"),
          .assign .storage (ilksF (.var "i") "spot") (.var "ilkSpot"),
          .assign .storage (ilksF (.var "i") "line") (.var "ilkLine"),
          .assign .storage (ilksF (.var "i") "dust") (.var "ilkDust") ])
      .reverted := by
  have h := Reasoning.Refinement.execBlock_append_term
    (s2 :=
      [ .assign .storage (gemRef (.var "i") (.var "v")) (.var "gemNew") ] ++
        checkedAddSignedInto "daiNew" (.storage (daiRef (.var "w"))) (.var "dtab") ++
        [ .assign .storage (daiRef (.var "w")) (.var "daiNew"),
          .assign .storage (urnsF (.var "i") (.var "u") "ink") (.var "urnInkNew"),
          .assign .storage (urnsF (.var "i") (.var "u") "art") (.var "urnArtNew"),
          .assign .storage (ilksF (.var "i") "Art") (.var "ilkArtNew"),
          .assign .storage (ilksF (.var "i") "rate") (.var "ilkRate"),
          .assign .storage (ilksF (.var "i") "spot") (.var "ilkSpot"),
          .assign .storage (ilksF (.var "i") "line") (.var "ilkLine"),
          .assign .storage (ilksF (.var "i") "dust") (.var "ilkDust") ])
    hGem (by intro f e h; cases h)
  simpa [List.append_assoc] using h

theorem execFrobFinalStoreTailDaiRevertFromBlock {evm evmGem : EVM.State}
    {locals localsGem : Store}
    (hGem :
      ExecBlock config { contract := contract, locals := locals } evm
        (checkedSubSignedInto "gemNew" (.storage (gemRef (.var "i") (.var "v")))
          (.var "dink") ++
        [ .assign .storage (gemRef (.var "i") (.var "v")) (.var "gemNew") ])
        (.ok { contract := contract, locals := localsGem } evmGem))
    (hDai :
      ExecBlock config { contract := contract, locals := localsGem } evmGem
        (checkedAddSignedInto "daiNew" (.storage (daiRef (.var "w"))) (.var "dtab"))
        .reverted) :
    ExecBlock config { contract := contract, locals := locals } evm
      (checkedSubSignedInto "gemNew" (.storage (gemRef (.var "i") (.var "v")))
        (.var "dink") ++
        [ .assign .storage (gemRef (.var "i") (.var "v")) (.var "gemNew") ] ++
        checkedAddSignedInto "daiNew" (.storage (daiRef (.var "w"))) (.var "dtab") ++
        [ .assign .storage (daiRef (.var "w")) (.var "daiNew"),
          .assign .storage (urnsF (.var "i") (.var "u") "ink") (.var "urnInkNew"),
          .assign .storage (urnsF (.var "i") (.var "u") "art") (.var "urnArtNew"),
          .assign .storage (ilksF (.var "i") "Art") (.var "ilkArtNew"),
          .assign .storage (ilksF (.var "i") "rate") (.var "ilkRate"),
          .assign .storage (ilksF (.var "i") "spot") (.var "ilkSpot"),
          .assign .storage (ilksF (.var "i") "line") (.var "ilkLine"),
          .assign .storage (ilksF (.var "i") "dust") (.var "ilkDust") ])
      .reverted := by
  have h01 := Reasoning.Refinement.execBlock_append hGem hDai
  have h := Reasoning.Refinement.execBlock_append_term
    (s2 :=
      [ .assign .storage (daiRef (.var "w")) (.var "daiNew"),
        .assign .storage (urnsF (.var "i") (.var "u") "ink") (.var "urnInkNew"),
        .assign .storage (urnsF (.var "i") (.var "u") "art") (.var "urnArtNew"),
        .assign .storage (ilksF (.var "i") "Art") (.var "ilkArtNew"),
        .assign .storage (ilksF (.var "i") "rate") (.var "ilkRate"),
        .assign .storage (ilksF (.var "i") "spot") (.var "ilkSpot"),
        .assign .storage (ilksF (.var "i") "line") (.var "ilkLine"),
        .assign .storage (ilksF (.var "i") "dust") (.var "ilkDust") ])
    h01 (by intro f e h; cases h)
  simpa [List.append_assoc] using h

set_option maxHeartbeats 1000000 in
theorem execFrobFinalStoreTailOk {evm : EVM.State} {I : ExecutionEnv}
    (locals : Store)
    (gemOld gemNew daiOld daiNew dtabWord : UInt256) (dtab : Int)
    (urnInkNew urnArtNew ilkArtNew ilkRate ilkSpot ilkLine ilkDust : UInt256)
    (hsz196 : 196 ≤ I.calldata.size)
    (hi : locals.get? "i" = some (frobIValue I))
    (hu : locals.get? "u" = some (frobUValue I))
    (hv : locals.get? "v" = some (frobVValue I))
    (hw : locals.get? "w" = some (frobWValue I))
    (hdink : locals.get? "dink" = some (frobDinkValue I))
    (hdtab : locals.get? "dtab" = some (.int dtab))
    (hurnInkNew : locals.get? "urnInkNew" = some (.int (Int.ofNat urnInkNew.toNat)))
    (hurnArtNew : locals.get? "urnArtNew" = some (.int (Int.ofNat urnArtNew.toNat)))
    (hilkArtNew : locals.get? "ilkArtNew" = some (.int (Int.ofNat ilkArtNew.toNat)))
    (hilkRate : locals.get? "ilkRate" = some (.int (Int.ofNat ilkRate.toNat)))
    (hilkSpot : locals.get? "ilkSpot" = some (.int (Int.ofNat ilkSpot.toNat)))
    (hilkLine : locals.get? "ilkLine" = some (.int (Int.ofNat ilkLine.toNat)))
    (hilkDust : locals.get? "ilkDust" = some (.int (Int.ofNat ilkDust.toNat)))
    (hbaseGem : locals.get? "gem" = none)
    (hbaseDai : locals.get? "dai" = none)
    (hbaseUrns : locals.get? "urns" = none)
    (hbaseIlks : locals.get? "ilks" = none)
    (hloadGem :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (frobGemVSourceSlot I) = gemOld)
    (hloadDai :
      let evmGem := Solm.EVM.storageStore evm evm.executionEnv.codeOwner
        (frobGemVSourceSlot I) gemNew
      Solm.EVM.storageLoad evmGem evmGem.executionEnv.codeOwner
        (frobDaiWSourceSlot I) = daiOld)
    (hgemNew : gemNew = UInt256.sub gemOld (frobDinkWord I))
    (hdaiNew : daiNew = dtabWord + daiOld)
    (hdtabMod : dtab % (Int.ofNat EVM.wordModulus) = Int.ofNat dtabWord.toNat)
    (hGemNeg : frobDinkInt I ≤ 0 ∨ gemNew.toNat ≤ gemOld.toNat)
    (hGemPos : 0 ≤ frobDinkInt I ∨ gemOld.toNat ≤ gemNew.toNat)
    (hDaiNeg : 0 ≤ dtab ∨ daiNew.toNat ≤ daiOld.toNat)
    (hDaiPos : dtab ≤ 0 ∨ daiOld.toNat ≤ daiNew.toNat) :
    let evmGem := Solm.EVM.storageStore evm evm.executionEnv.codeOwner
      (frobGemVSourceSlot I) gemNew
    let evmDai := Solm.EVM.storageStore evmGem evmGem.executionEnv.codeOwner
      (frobDaiWSourceSlot I) daiNew
    let evmInk := Solm.EVM.storageStore evmDai evmDai.executionEnv.codeOwner
      (frobUrnInkSourceSlot I) urnInkNew
    let evmArt := Solm.EVM.storageStore evmInk evmInk.executionEnv.codeOwner
      (frobUrnArtSourceSlot I) urnArtNew
    let evmIlk := Solm.EVM.storageStore evmArt evmArt.executionEnv.codeOwner
      (frobIlkArtSourceSlot I) ilkArtNew
    let evmRate := Solm.EVM.storageStore evmIlk evmIlk.executionEnv.codeOwner
      (frobIlkRateSourceSlot I) ilkRate
    let evmSpot := Solm.EVM.storageStore evmRate evmRate.executionEnv.codeOwner
      (frobIlkSpotSourceSlot I) ilkSpot
    let evmLine := Solm.EVM.storageStore evmSpot evmSpot.executionEnv.codeOwner
      (frobIlkLineSourceSlot I) ilkLine
    let evmDust := Solm.EVM.storageStore evmLine evmLine.executionEnv.codeOwner
      (frobIlkDustSourceSlot I) ilkDust
    ExecBlock config { contract := contract, locals := locals } evm
      (checkedSubSignedInto "gemNew" (.storage (gemRef (.var "i") (.var "v"))) (.var "dink") ++
        [ .assign .storage (gemRef (.var "i") (.var "v")) (.var "gemNew") ] ++
        checkedAddSignedInto "daiNew" (.storage (daiRef (.var "w"))) (.var "dtab") ++
        [ .assign .storage (daiRef (.var "w")) (.var "daiNew"),
          .assign .storage (urnsF (.var "i") (.var "u") "ink") (.var "urnInkNew"),
          .assign .storage (urnsF (.var "i") (.var "u") "art") (.var "urnArtNew"),
          .assign .storage (ilksF (.var "i") "Art") (.var "ilkArtNew"),
          .assign .storage (ilksF (.var "i") "rate") (.var "ilkRate"),
          .assign .storage (ilksF (.var "i") "spot") (.var "ilkSpot"),
          .assign .storage (ilksF (.var "i") "line") (.var "ilkLine"),
          .assign .storage (ilksF (.var "i") "dust") (.var "ilkDust") ])
      (.ok
        { contract := contract,
          locals :=
            (locals.insert "gemNew" (.int (Int.ofNat gemNew.toNat))).insert "daiNew"
              (.int (Int.ofNat daiNew.toNat)) }
        evmDust) := by
  intro evmGem evmDai evmInk evmArt evmIlk evmRate evmSpot evmLine evmDust
  let localsGem := locals.insert "gemNew" (.int (Int.ofNat gemNew.toNat))
  let localsDai := localsGem.insert "daiNew" (.int (Int.ofNat daiNew.toNat))
  have hgemBlock :
      ExecBlock config { contract := contract, locals := locals } evm
        (checkedSubSignedInto "gemNew" (.storage (gemRef (.var "i") (.var "v"))) (.var "dink") ++
          [ .assign .storage (gemRef (.var "i") (.var "v")) (.var "gemNew") ])
        (.ok { contract := contract, locals := localsGem } evmGem) := by
    simpa [localsGem, evmGem] using
      execFrobGemUpdateOk (evm := evm) (I := I) locals gemOld gemNew hsz196 hi hv
        hdink hbaseGem hloadGem hgemNew hGemNeg hGemPos
  have hwGem : localsGem.get? "w" = some (frobWValue I) := by
    change (locals.insert "gemNew" (.int (Int.ofNat gemNew.toNat))).get? "w" =
      some (frobWValue I)
    rw [store_get_ne _ _ (by decide)]
    exact hw
  have hdtabGem : localsGem.get? "dtab" = some (.int dtab) := by
    change (locals.insert "gemNew" (.int (Int.ofNat gemNew.toNat))).get? "dtab" =
      some (.int dtab)
    rw [store_get_ne _ _ (by decide)]
    exact hdtab
  have hbaseDaiGem : localsGem.get? "dai" = none := by
    change (locals.insert "gemNew" (.int (Int.ofNat gemNew.toNat))).get? "dai" = none
    rw [store_get_ne _ _ (by decide)]
    exact hbaseDai
  have hdaiBlock :
      ExecBlock config { contract := contract, locals := localsGem } evmGem
        (checkedAddSignedInto "daiNew" (.storage (daiRef (.var "w"))) (.var "dtab") ++
          [ .assign .storage (daiRef (.var "w")) (.var "daiNew") ])
        (.ok { contract := contract, locals := localsDai } evmDai) := by
    simpa [localsGem, localsDai, evmGem, evmDai] using
      execFrobDaiUpdateOk (evm := evmGem) (I := I) localsGem daiOld daiNew
        dtabWord dtab hwGem hdtabGem hbaseDaiGem (by simpa [evmGem] using hloadDai)
        hdtabMod hdaiNew hDaiNeg hDaiPos
  have hTailBaseI : localsDai.get? "i" = some (frobIValue I) := by
    change ((locals.insert "gemNew" (.int (Int.ofNat gemNew.toNat))).insert "daiNew"
      (.int (Int.ofNat daiNew.toNat))).get? "i" = some (frobIValue I)
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    exact hi
  have hTailBaseU : localsDai.get? "u" = some (frobUValue I) := by
    change ((locals.insert "gemNew" (.int (Int.ofNat gemNew.toNat))).insert "daiNew"
      (.int (Int.ofNat daiNew.toNat))).get? "u" = some (frobUValue I)
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    exact hu
  have hTailUrns : localsDai.get? "urns" = none := by
    change ((locals.insert "gemNew" (.int (Int.ofNat gemNew.toNat))).insert "daiNew"
      (.int (Int.ofNat daiNew.toNat))).get? "urns" = none
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    exact hbaseUrns
  have hTailIlks : localsDai.get? "ilks" = none := by
    change ((locals.insert "gemNew" (.int (Int.ofNat gemNew.toNat))).insert "daiNew"
      (.int (Int.ofNat daiNew.toNat))).get? "ilks" = none
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    exact hbaseIlks
  have evalVarAfterDai {evm' : EVM.State} {name : Ident} {value : UInt256}
      (hget : locals.get? name = some (.int (Int.ofNat value.toNat)))
      (hnameGem : ("gemNew" == name) = false) (hnameDai : ("daiNew" == name) = false) :
      evalExpr? config { contract := contract, locals := localsDai } evm' (.var name) =
        .ok (.int (Int.ofNat value.toNat)) := by
    exact vatEvalExpr_varUInt256 (by
      change ((locals.insert "gemNew" (.int (Int.ofNat gemNew.toNat))).insert "daiNew"
        (.int (Int.ofNat daiNew.toNat))).get? name =
        some (.int (Int.ofNat value.toNat))
      rw [store_get_ne _ _ hnameDai]
      rw [store_get_ne _ _ hnameGem]
      exact hget)
  have hassignInk :
      assignStorageRef? config { contract := contract, locals := localsDai } evmDai
        .storage (urnsF (.var "i") (.var "u") "ink")
        (.int (Int.ofNat urnInkNew.toNat)) =
      .ok ({ contract := contract, locals := localsDai }, evmInk) := by
    simpa [evmInk] using
      assignStorageRef_frob_urn_ink evmDai I localsDai urnInkNew hsz196 hTailBaseI
        hTailBaseU hTailUrns
  have hassignArt :
      assignStorageRef? config { contract := contract, locals := localsDai } evmInk
        .storage (urnsF (.var "i") (.var "u") "art")
        (.int (Int.ofNat urnArtNew.toNat)) =
      .ok ({ contract := contract, locals := localsDai }, evmArt) := by
    simpa [evmArt] using
      assignStorageRef_frob_urn_art evmInk I localsDai urnArtNew hsz196 hTailBaseI
        hTailBaseU hTailUrns
  have hassignIlkArt :
      assignStorageRef? config { contract := contract, locals := localsDai } evmArt
        .storage (ilksF (.var "i") "Art") (.int (Int.ofNat ilkArtNew.toNat)) =
      .ok ({ contract := contract, locals := localsDai }, evmIlk) := by
    simpa [evmIlk] using
      assignStorageRef_frob_ilk_art evmArt I localsDai ilkArtNew hsz196 hTailBaseI
        hTailIlks
  have hassignRate :
      assignStorageRef? config { contract := contract, locals := localsDai } evmIlk
        .storage (ilksF (.var "i") "rate") (.int (Int.ofNat ilkRate.toNat)) =
      .ok ({ contract := contract, locals := localsDai }, evmRate) := by
    simpa [evmRate] using
      assignStorageRef_frob_ilk_rate evmIlk I localsDai ilkRate hsz196 hTailBaseI
        hTailIlks
  have hassignSpot :
      assignStorageRef? config { contract := contract, locals := localsDai } evmRate
        .storage (ilksF (.var "i") "spot") (.int (Int.ofNat ilkSpot.toNat)) =
      .ok ({ contract := contract, locals := localsDai }, evmSpot) := by
    simpa [evmSpot] using
      assignStorageRef_frob_ilk_spot evmRate I localsDai ilkSpot hsz196 hTailBaseI
        hTailIlks
  have hassignLine :
      assignStorageRef? config { contract := contract, locals := localsDai } evmSpot
        .storage (ilksF (.var "i") "line") (.int (Int.ofNat ilkLine.toNat)) =
      .ok ({ contract := contract, locals := localsDai }, evmLine) := by
    simpa [evmLine] using
      assignStorageRef_frob_ilk_line evmSpot I localsDai ilkLine hsz196 hTailBaseI
        hTailIlks
  have hassignDust :
      assignStorageRef? config { contract := contract, locals := localsDai } evmLine
        .storage (ilksF (.var "i") "dust") (.int (Int.ofNat ilkDust.toNat)) =
      .ok ({ contract := contract, locals := localsDai }, evmDust) := by
    simpa [evmDust] using
      assignStorageRef_frob_ilk_dust evmLine I localsDai ilkDust hsz196 hTailBaseI
        hTailIlks
  have hstores :
      ExecBlock config { contract := contract, locals := localsDai } evmDai
        [ .assign .storage (urnsF (.var "i") (.var "u") "ink") (.var "urnInkNew"),
          .assign .storage (urnsF (.var "i") (.var "u") "art") (.var "urnArtNew"),
          .assign .storage (ilksF (.var "i") "Art") (.var "ilkArtNew"),
          .assign .storage (ilksF (.var "i") "rate") (.var "ilkRate"),
          .assign .storage (ilksF (.var "i") "spot") (.var "ilkSpot"),
          .assign .storage (ilksF (.var "i") "line") (.var "ilkLine"),
          .assign .storage (ilksF (.var "i") "dust") (.var "ilkDust") ]
        (.ok { contract := contract, locals := localsDai } evmDust) := by
    refine ExecBlock.consNormal
      (ExecStmt.assign
        (evalVarAfterDai (evm' := evmDai) hurnInkNew (by native_decide)
          (by native_decide))
        hassignInk) ?_
    refine ExecBlock.consNormal
      (ExecStmt.assign
        (evalVarAfterDai (evm' := evmInk) hurnArtNew (by native_decide)
          (by native_decide))
        hassignArt) ?_
    refine ExecBlock.consNormal
      (ExecStmt.assign
        (evalVarAfterDai (evm' := evmArt) hilkArtNew (by native_decide)
          (by native_decide))
        hassignIlkArt) ?_
    refine ExecBlock.consNormal
      (ExecStmt.assign
        (evalVarAfterDai (evm' := evmIlk) hilkRate (by native_decide)
          (by native_decide))
        hassignRate) ?_
    refine ExecBlock.consNormal
      (ExecStmt.assign
        (evalVarAfterDai (evm' := evmRate) hilkSpot (by native_decide)
          (by native_decide))
        hassignSpot) ?_
    refine ExecBlock.consNormal
      (ExecStmt.assign
        (evalVarAfterDai (evm' := evmSpot) hilkLine (by native_decide)
          (by native_decide))
        hassignLine) ?_
    exact ExecBlock.consNormal
      (ExecStmt.assign
        (evalVarAfterDai (evm' := evmLine) hilkDust (by native_decide)
          (by native_decide))
        hassignDust) ExecBlock.nil
  have h01 := Reasoning.Refinement.execBlock_append hgemBlock hdaiBlock
  have h02 := Reasoning.Refinement.execBlock_append h01 hstores
  simpa [localsGem, localsDai, evmGem, evmDai, evmInk, evmArt, evmIlk, evmRate,
    evmSpot, evmLine, evmDust, List.append_assoc] using h02

theorem execFrobDebtAddStoreOk {evm : EVM.State} {locals : Store}
    (debtOld debtNew dtabWord : UInt256) (dtab : Int)
    (hbase : locals.get? "debt" = none)
    (hdtab : locals.get? "dtab" = some (.int dtab))
    (hload :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner foldDebtSlot = debtOld)
    (hdtabMod : dtab % (Int.ofNat EVM.wordModulus) = Int.ofNat dtabWord.toNat)
    (hnew : debtNew = dtabWord + debtOld)
    (hguardNeg : 0 ≤ dtab ∨ debtNew.toNat ≤ debtOld.toNat)
    (hguardPos : dtab ≤ 0 ∨ debtOld.toNat ≤ debtNew.toNat) :
    ExecBlock config { contract := contract, locals := locals } evm
      (checkedAddSignedInto "debtNew" (.storage debtRef) (.var "dtab") ++
        [ .assign .storage debtRef (.var "debtNew") ])
      (.ok
        { contract := contract,
          locals := locals.insert "debtNew" (.int (Int.ofNat debtNew.toNat)) }
        (Solm.EVM.storageStore evm evm.executionEnv.codeOwner foldDebtSlot debtNew)) := by
  let localsDebt := locals.insert "debtNew" (.int (Int.ofNat debtNew.toNat))
  let evmDebt := Solm.EVM.storageStore evm evm.executionEnv.codeOwner foldDebtSlot debtNew
  have hdebt :
      evalExpr? config { contract := contract, locals := locals } evm (.storage debtRef) =
        .ok (.int (Int.ofNat debtOld.toNat)) := by
    rw [evalExpr_fold_debt evm locals hbase]
    rw [hload]
  have hdtabEval :
      evalExpr? config { contract := contract, locals := locals } evm (.var "dtab") =
        .ok (.int dtab) :=
    vatEvalExpr_varInt hdtab
  have hlet :
      evalExpr? config { contract := contract, locals := locals } evm
        (wordWrap256 (.binary .add (.storage debtRef) (.var "dtab"))) =
        .ok (.int (Int.ofNat debtNew.toNat)) :=
    evalExpr_fold_wordWrapAdd_ok hdebt hdtabEval hdtabMod hnew
  have hdebtNewEval :
      evalExpr? config { contract := contract, locals := localsDebt } evm (.var "debtNew") =
        .ok (.int (Int.ofNat debtNew.toNat)) :=
    vatEvalExpr_varUInt256 (by simp [localsDebt])
  have hdtabAfter :
      evalExpr? config { contract := contract, locals := localsDebt } evm (.var "dtab") =
        .ok (.int dtab) := by
    exact vatEvalExpr_varInt (by
      change (locals.insert "debtNew" (.int (Int.ofNat debtNew.toNat))).get? "dtab" =
        some (.int dtab)
      rw [store_get_ne _ _ (by decide)]
      exact hdtab)
  have hbaseAfter : localsDebt.get? "debt" = none := by
    change (locals.insert "debtNew" (.int (Int.ofNat debtNew.toNat))).get? "debt" =
      none
    rw [store_get_ne _ _ (by decide)]
    exact hbase
  have hdebtAfter :
      evalExpr? config { contract := contract, locals := localsDebt } evm (.storage debtRef) =
        .ok (.int (Int.ofNat debtOld.toNat)) := by
    rw [evalExpr_fold_debt evm localsDebt hbaseAfter]
    rw [hload]
  have hguardNegEval :
      evalExpr? config { contract := contract, locals := localsDebt } evm
        (eitherExpr (.binary .ge (.var "dtab") (.intLit 0))
          (.binary .le (.var "debtNew") (.storage debtRef))) =
        .ok (.bool true) :=
    evalSignedAddGuardNeg_true hdtabAfter hdebtNewEval hdebtAfter hguardNeg
  have hguardPosEval :
      evalExpr? config { contract := contract, locals := localsDebt } evm
        (eitherExpr (.binary .le (.var "dtab") (.intLit 0))
          (.binary .ge (.var "debtNew") (.storage debtRef))) =
        .ok (.bool true) :=
    evalSignedAddGuardPos_true hdtabAfter hdebtNewEval hdebtAfter hguardPos
  have hAdd :
      ExecBlock config { contract := contract, locals := locals } evm
        (checkedAddSignedInto "debtNew" (.storage debtRef) (.var "dtab"))
        (.ok { contract := contract, locals := localsDebt } evm) := by
    change ExecBlock config { contract := contract, locals := locals } evm
      [ .letDecl "debtNew" (some uint256)
          (wordWrap256 (.binary .add (.storage debtRef) (.var "dtab"))),
        .require
          (eitherExpr (.binary .ge (.var "dtab") (.intLit 0))
            (.binary .le (.var "debtNew") (.storage debtRef))),
        .require
          (eitherExpr (.binary .le (.var "dtab") (.intLit 0))
            (.binary .ge (.var "debtNew") (.storage debtRef))) ]
      (.ok { contract := contract, locals := localsDebt } evm)
    refine ExecBlock.consNormal (ExecStmt.letDecl hlet) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguardNegEval) ?_
    exact ExecBlock.consNormal (ExecStmt.requireTrue hguardPosEval) ExecBlock.nil
  have hdebtAssign :
      assignStorageRef? config { contract := contract, locals := localsDebt } evm
        .storage debtRef (.int (Int.ofNat debtNew.toNat)) =
      .ok ({ contract := contract, locals := localsDebt }, evmDebt) := by
    simpa [evmDebt] using assign_fold_debt evm localsDebt debtNew hbaseAfter
  have hAssign :
      ExecBlock config { contract := contract, locals := localsDebt } evm
        [ .assign .storage debtRef (.var "debtNew") ]
        (.ok { contract := contract, locals := localsDebt } evmDebt) := by
    exact ExecBlock.consNormal (ExecStmt.assign hdebtNewEval hdebtAssign) ExecBlock.nil
  have h := Reasoning.Refinement.execBlock_append hAdd hAssign
  simpa [localsDebt, evmDebt, List.append_assoc] using h

theorem execFrobDebtAddCheckedRevertGuardNeg {evm : EVM.State} {locals : Store}
    (debtOld debtNew dtabWord : UInt256) (dtab : Int)
    (hbase : locals.get? "debt" = none)
    (hdtab : locals.get? "dtab" = some (.int dtab))
    (hload :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner foldDebtSlot = debtOld)
    (hdtabMod : dtab % (Int.ofNat EVM.wordModulus) = Int.ofNat dtabWord.toNat)
    (hnew : debtNew = dtabWord + debtOld)
    (hcond : dtab < 0 ∧ debtOld.toNat < debtNew.toNat) :
    ExecBlock config { contract := contract, locals := locals } evm
      (checkedAddSignedInto "debtNew" (.storage debtRef) (.var "dtab"))
      .reverted := by
  let localsDebt := locals.insert "debtNew" (.int (Int.ofNat debtNew.toNat))
  have hdebt :
      evalExpr? config { contract := contract, locals := locals } evm (.storage debtRef) =
        .ok (.int (Int.ofNat debtOld.toNat)) := by
    rw [evalExpr_fold_debt evm locals hbase]
    rw [hload]
  have hdtabEval :
      evalExpr? config { contract := contract, locals := locals } evm (.var "dtab") =
        .ok (.int dtab) :=
    vatEvalExpr_varInt hdtab
  have hdtabAfter :
      evalExpr? config { contract := contract, locals := localsDebt } evm (.var "dtab") =
        .ok (.int dtab) := by
    exact vatEvalExpr_varInt (by
      change (locals.insert "debtNew" (.int (Int.ofNat debtNew.toNat))).get? "dtab" =
        some (.int dtab)
      rw [store_get_ne _ _ (by decide)]
      exact hdtab)
  have hbaseAfter : localsDebt.get? "debt" = none := by
    change (locals.insert "debtNew" (.int (Int.ofNat debtNew.toNat))).get? "debt" =
      none
    rw [store_get_ne _ _ (by decide)]
    exact hbase
  have hdebtAfter :
      evalExpr? config { contract := contract, locals := localsDebt } evm (.storage debtRef) =
        .ok (.int (Int.ofNat debtOld.toNat)) := by
    rw [evalExpr_fold_debt evm localsDebt hbaseAfter]
    rw [hload]
  exact execCheckedAddSignedRevertGuardNeg
    (x := .storage debtRef) (y := .var "dtab") (name := "debtNew")
    (old := debtOld) (new := debtNew) (addend := dtabWord) (addendInt := dtab)
    hdebt hdtabEval hdtabMod hnew hdtabAfter hdebtAfter hcond

theorem execFrobDebtAddCheckedRevertGuardPos {evm : EVM.State} {locals : Store}
    (debtOld debtNew dtabWord : UInt256) (dtab : Int)
    (hbase : locals.get? "debt" = none)
    (hdtab : locals.get? "dtab" = some (.int dtab))
    (hload :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner foldDebtSlot = debtOld)
    (hdtabMod : dtab % (Int.ofNat EVM.wordModulus) = Int.ofNat dtabWord.toNat)
    (hnew : debtNew = dtabWord + debtOld)
    (hguardNeg : 0 ≤ dtab ∨ debtNew.toNat ≤ debtOld.toNat)
    (hcond : 0 < dtab ∧ debtNew.toNat < debtOld.toNat) :
    ExecBlock config { contract := contract, locals := locals } evm
      (checkedAddSignedInto "debtNew" (.storage debtRef) (.var "dtab"))
      .reverted := by
  let localsDebt := locals.insert "debtNew" (.int (Int.ofNat debtNew.toNat))
  have hdebt :
      evalExpr? config { contract := contract, locals := locals } evm (.storage debtRef) =
        .ok (.int (Int.ofNat debtOld.toNat)) := by
    rw [evalExpr_fold_debt evm locals hbase]
    rw [hload]
  have hdtabEval :
      evalExpr? config { contract := contract, locals := locals } evm (.var "dtab") =
        .ok (.int dtab) :=
    vatEvalExpr_varInt hdtab
  have hdtabAfter :
      evalExpr? config { contract := contract, locals := localsDebt } evm (.var "dtab") =
        .ok (.int dtab) := by
    exact vatEvalExpr_varInt (by
      change (locals.insert "debtNew" (.int (Int.ofNat debtNew.toNat))).get? "dtab" =
        some (.int dtab)
      rw [store_get_ne _ _ (by decide)]
      exact hdtab)
  have hbaseAfter : localsDebt.get? "debt" = none := by
    change (locals.insert "debtNew" (.int (Int.ofNat debtNew.toNat))).get? "debt" =
      none
    rw [store_get_ne _ _ (by decide)]
    exact hbase
  have hdebtAfter :
      evalExpr? config { contract := contract, locals := localsDebt } evm (.storage debtRef) =
        .ok (.int (Int.ofNat debtOld.toNat)) := by
    rw [evalExpr_fold_debt evm localsDebt hbaseAfter]
    rw [hload]
  have hdebtNewEval :
      evalExpr? config { contract := contract, locals := localsDebt } evm (.var "debtNew") =
        .ok (.int (Int.ofNat debtNew.toNat)) :=
    vatEvalExpr_varUInt256 (by simp [localsDebt])
  have hguardNegEval :
      evalExpr? config { contract := contract, locals := localsDebt } evm
        (eitherExpr (.binary .ge (.var "dtab") (.intLit 0))
          (.binary .le (.var "debtNew") (.storage debtRef))) =
        .ok (.bool true) :=
    evalSignedAddGuardNeg_true hdtabAfter hdebtNewEval hdebtAfter hguardNeg
  exact execCheckedAddSignedRevertGuardPos
    (x := .storage debtRef) (y := .var "dtab") (name := "debtNew")
    (old := debtOld) (new := debtNew) (addend := dtabWord) (addendInt := dtab)
    hdebt hdtabEval hdtabMod hnew hdtabAfter hdebtAfter hguardNegEval hcond

theorem execFrobLoadedPrefixUrnInkRevertGuardNeg {evm : EVM.State} {I : ExecutionEnv}
    {pre : List Stmt}
    (urnInk urnArt ilkArt ilkRate ilkSpot ilkLine ilkDust : UInt256)
    (hprefix :
      ExecBlock config { contract := contract, locals := frobStore I } evm pre
        (.ok
          { contract := contract,
            locals := frobStoreIlkDust I urnInk urnArt ilkArt ilkRate ilkSpot ilkLine
              ilkDust }
          evm))
    (hcond :
      frobDinkInt I < 0 ∧ urnInk.toNat < (frobDinkWord I + urnInk).toNat) :
    ExecBlock config { contract := contract, locals := frobStore I } evm
      (pre ++ checkedAddSignedInto "urnInkNew" (.var "urnInk") (.var "dink"))
      .reverted := by
  let localsLoaded :=
    frobStoreIlkDust I urnInk urnArt ilkArt ilkRate ilkSpot ilkLine ilkDust
  let urnInkNew := frobDinkWord I + urnInk
  have hInkBlock :
      ExecBlock config { contract := contract, locals := localsLoaded } evm
        (checkedAddSignedInto "urnInkNew" (.var "urnInk") (.var "dink"))
        .reverted := by
    exact execFrobUrnInkAddRevertGuardNeg (I := I) localsLoaded urnInk urnInkNew
      (by
        simpa [localsLoaded] using
          frobStoreIlkDust_get_urnInk I urnInk urnArt ilkArt ilkRate ilkSpot ilkLine
            ilkDust)
      (by
        simpa [localsLoaded] using
          frobStoreIlkDust_get_dink I urnInk urnArt ilkArt ilkRate ilkSpot ilkLine
            ilkDust)
      (by simp [urnInkNew]) (by simpa [urnInkNew] using hcond)
  have h := Reasoning.Refinement.execBlock_append hprefix
    (by simpa [localsLoaded] using hInkBlock)
  simpa [localsLoaded, List.append_assoc] using h

theorem execFrobLoadedPrefixUrnInkRevertGuardPos {evm : EVM.State} {I : ExecutionEnv}
    {pre : List Stmt}
    (urnInk urnArt ilkArt ilkRate ilkSpot ilkLine ilkDust : UInt256)
    (hprefix :
      ExecBlock config { contract := contract, locals := frobStore I } evm pre
        (.ok
          { contract := contract,
            locals := frobStoreIlkDust I urnInk urnArt ilkArt ilkRate ilkSpot ilkLine
              ilkDust }
          evm))
    (hguardNeg : 0 ≤ frobDinkInt I ∨ (frobDinkWord I + urnInk).toNat ≤ urnInk.toNat)
    (hcond :
      0 < frobDinkInt I ∧ (frobDinkWord I + urnInk).toNat < urnInk.toNat) :
    ExecBlock config { contract := contract, locals := frobStore I } evm
      (pre ++ checkedAddSignedInto "urnInkNew" (.var "urnInk") (.var "dink"))
      .reverted := by
  let localsLoaded :=
    frobStoreIlkDust I urnInk urnArt ilkArt ilkRate ilkSpot ilkLine ilkDust
  let urnInkNew := frobDinkWord I + urnInk
  have hInkBlock :
      ExecBlock config { contract := contract, locals := localsLoaded } evm
        (checkedAddSignedInto "urnInkNew" (.var "urnInk") (.var "dink"))
        .reverted := by
    exact execFrobUrnInkAddRevertGuardPos (I := I) localsLoaded urnInk urnInkNew
      (by
        simpa [localsLoaded] using
          frobStoreIlkDust_get_urnInk I urnInk urnArt ilkArt ilkRate ilkSpot ilkLine
            ilkDust)
      (by
        simpa [localsLoaded] using
          frobStoreIlkDust_get_dink I urnInk urnArt ilkArt ilkRate ilkSpot ilkLine
            ilkDust)
      (by simp [urnInkNew]) (by simpa [urnInkNew] using hguardNeg)
      (by simpa [urnInkNew] using hcond)
  have h := Reasoning.Refinement.execBlock_append hprefix
    (by simpa [localsLoaded] using hInkBlock)
  simpa [localsLoaded, List.append_assoc] using h

theorem execFrobLoadedPrefixUrnArtRevertGuardNeg {evm : EVM.State} {I : ExecutionEnv}
    {pre : List Stmt}
    (urnInk urnArt ilkArt ilkRate ilkSpot ilkLine ilkDust : UInt256)
    (hprefix :
      ExecBlock config { contract := contract, locals := frobStore I } evm pre
        (.ok
          { contract := contract,
            locals := frobStoreIlkDust I urnInk urnArt ilkArt ilkRate ilkSpot ilkLine
              ilkDust }
          evm))
    (hInkNeg : 0 ≤ frobDinkInt I ∨ (frobDinkWord I + urnInk).toNat ≤ urnInk.toNat)
    (hInkPos : frobDinkInt I ≤ 0 ∨ urnInk.toNat ≤ (frobDinkWord I + urnInk).toNat)
    (hcond :
      frobDartInt I < 0 ∧ urnArt.toNat < (frobDartWord I + urnArt).toNat) :
    ExecBlock config { contract := contract, locals := frobStore I } evm
      (pre ++
        checkedAddSignedInto "urnInkNew" (.var "urnInk") (.var "dink") ++
        checkedAddSignedInto "urnArtNew" (.var "urnArt") (.var "dart"))
      .reverted := by
  let localsLoaded :=
    frobStoreIlkDust I urnInk urnArt ilkArt ilkRate ilkSpot ilkLine ilkDust
  let urnInkNew := frobDinkWord I + urnInk
  let urnArtNew := frobDartWord I + urnArt
  have hInkBlock :
      ExecBlock config { contract := contract, locals := localsLoaded } evm
        (checkedAddSignedInto "urnInkNew" (.var "urnInk") (.var "dink"))
        (.ok
          { contract := contract,
            locals := localsLoaded.insert "urnInkNew"
              (.int (Int.ofNat urnInkNew.toNat)) }
          evm) := by
    exact execFrobUrnInkAddOk (I := I) localsLoaded urnInk urnInkNew
      (by
        simpa [localsLoaded] using
          frobStoreIlkDust_get_urnInk I urnInk urnArt ilkArt ilkRate ilkSpot ilkLine
            ilkDust)
      (by
        simpa [localsLoaded] using
          frobStoreIlkDust_get_dink I urnInk urnArt ilkArt ilkRate ilkSpot ilkLine
            ilkDust)
      (by simp [urnInkNew]) (by simpa [urnInkNew] using hInkNeg)
      (by simpa [urnInkNew] using hInkPos)
  let localsInk := localsLoaded.insert "urnInkNew" (.int (Int.ofNat urnInkNew.toNat))
  have hArtBlock :
      ExecBlock config { contract := contract, locals := localsInk } evm
        (checkedAddSignedInto "urnArtNew" (.var "urnArt") (.var "dart"))
        .reverted := by
    exact execFrobUrnArtAddRevertGuardNeg (I := I) localsInk urnArt urnArtNew
      (by
        change (localsLoaded.insert "urnInkNew"
          (.int (Int.ofNat urnInkNew.toNat))).get? "urnArt" =
          some (.int (Int.ofNat urnArt.toNat))
        rw [store_get_ne _ _ (by decide)]
        simpa [localsLoaded] using
          frobStoreIlkDust_get_urnArt I urnInk urnArt ilkArt ilkRate ilkSpot ilkLine
            ilkDust)
      (by
        change (localsLoaded.insert "urnInkNew"
          (.int (Int.ofNat urnInkNew.toNat))).get? "dart" =
          some (frobDartValue I)
        rw [store_get_ne _ _ (by decide)]
        simpa [localsLoaded] using
          frobStoreIlkDust_get_dart I urnInk urnArt ilkArt ilkRate ilkSpot ilkLine
            ilkDust)
      (by simp [urnArtNew]) (by simpa [urnArtNew] using hcond)
  have h01 := Reasoning.Refinement.execBlock_append hprefix
    (by simpa [localsLoaded] using hInkBlock)
  have h02 := Reasoning.Refinement.execBlock_append h01
    (by simpa [localsLoaded, localsInk] using hArtBlock)
  simpa [localsLoaded, localsInk, List.append_assoc] using h02

theorem execFrobLoadedPrefixUrnArtRevertGuardPos {evm : EVM.State} {I : ExecutionEnv}
    {pre : List Stmt}
    (urnInk urnArt ilkArt ilkRate ilkSpot ilkLine ilkDust : UInt256)
    (hprefix :
      ExecBlock config { contract := contract, locals := frobStore I } evm pre
        (.ok
          { contract := contract,
            locals := frobStoreIlkDust I urnInk urnArt ilkArt ilkRate ilkSpot ilkLine
              ilkDust }
          evm))
    (hInkNeg : 0 ≤ frobDinkInt I ∨ (frobDinkWord I + urnInk).toNat ≤ urnInk.toNat)
    (hInkPos : frobDinkInt I ≤ 0 ∨ urnInk.toNat ≤ (frobDinkWord I + urnInk).toNat)
    (hArtNeg : 0 ≤ frobDartInt I ∨ (frobDartWord I + urnArt).toNat ≤ urnArt.toNat)
    (hcond :
      0 < frobDartInt I ∧ (frobDartWord I + urnArt).toNat < urnArt.toNat) :
    ExecBlock config { contract := contract, locals := frobStore I } evm
      (pre ++
        checkedAddSignedInto "urnInkNew" (.var "urnInk") (.var "dink") ++
        checkedAddSignedInto "urnArtNew" (.var "urnArt") (.var "dart"))
      .reverted := by
  let localsLoaded :=
    frobStoreIlkDust I urnInk urnArt ilkArt ilkRate ilkSpot ilkLine ilkDust
  let urnInkNew := frobDinkWord I + urnInk
  let urnArtNew := frobDartWord I + urnArt
  have hInkBlock :
      ExecBlock config { contract := contract, locals := localsLoaded } evm
        (checkedAddSignedInto "urnInkNew" (.var "urnInk") (.var "dink"))
        (.ok
          { contract := contract,
            locals := localsLoaded.insert "urnInkNew"
              (.int (Int.ofNat urnInkNew.toNat)) }
          evm) := by
    exact execFrobUrnInkAddOk (I := I) localsLoaded urnInk urnInkNew
      (by
        simpa [localsLoaded] using
          frobStoreIlkDust_get_urnInk I urnInk urnArt ilkArt ilkRate ilkSpot ilkLine
            ilkDust)
      (by
        simpa [localsLoaded] using
          frobStoreIlkDust_get_dink I urnInk urnArt ilkArt ilkRate ilkSpot ilkLine
            ilkDust)
      (by simp [urnInkNew]) (by simpa [urnInkNew] using hInkNeg)
      (by simpa [urnInkNew] using hInkPos)
  let localsInk := localsLoaded.insert "urnInkNew" (.int (Int.ofNat urnInkNew.toNat))
  have hArtBlock :
      ExecBlock config { contract := contract, locals := localsInk } evm
        (checkedAddSignedInto "urnArtNew" (.var "urnArt") (.var "dart"))
        .reverted := by
    exact execFrobUrnArtAddRevertGuardPos (I := I) localsInk urnArt urnArtNew
      (by
        change (localsLoaded.insert "urnInkNew"
          (.int (Int.ofNat urnInkNew.toNat))).get? "urnArt" =
          some (.int (Int.ofNat urnArt.toNat))
        rw [store_get_ne _ _ (by decide)]
        simpa [localsLoaded] using
          frobStoreIlkDust_get_urnArt I urnInk urnArt ilkArt ilkRate ilkSpot ilkLine
            ilkDust)
      (by
        change (localsLoaded.insert "urnInkNew"
          (.int (Int.ofNat urnInkNew.toNat))).get? "dart" =
          some (frobDartValue I)
        rw [store_get_ne _ _ (by decide)]
        simpa [localsLoaded] using
          frobStoreIlkDust_get_dart I urnInk urnArt ilkArt ilkRate ilkSpot ilkLine
            ilkDust)
      (by simp [urnArtNew]) (by simpa [urnArtNew] using hArtNeg)
      (by simpa [urnArtNew] using hcond)
  have h01 := Reasoning.Refinement.execBlock_append hprefix
    (by simpa [localsLoaded] using hInkBlock)
  have h02 := Reasoning.Refinement.execBlock_append h01
    (by simpa [localsLoaded, localsInk] using hArtBlock)
  simpa [localsLoaded, localsInk, List.append_assoc] using h02

theorem execFrobLoadedPrefixIlkArtRevertGuardNeg {evm : EVM.State} {I : ExecutionEnv}
    {pre : List Stmt}
    (urnInk urnArt ilkArt ilkRate ilkSpot ilkLine ilkDust : UInt256)
    (hprefix :
      ExecBlock config { contract := contract, locals := frobStore I } evm pre
        (.ok
          { contract := contract,
            locals := frobStoreIlkDust I urnInk urnArt ilkArt ilkRate ilkSpot ilkLine
              ilkDust }
          evm))
    (hInkNeg : 0 ≤ frobDinkInt I ∨ (frobDinkWord I + urnInk).toNat ≤ urnInk.toNat)
    (hInkPos : frobDinkInt I ≤ 0 ∨ urnInk.toNat ≤ (frobDinkWord I + urnInk).toNat)
    (hArtNeg : 0 ≤ frobDartInt I ∨ (frobDartWord I + urnArt).toNat ≤ urnArt.toNat)
    (hArtPos : frobDartInt I ≤ 0 ∨ urnArt.toNat ≤ (frobDartWord I + urnArt).toNat)
    (hcond :
      frobDartInt I < 0 ∧ ilkArt.toNat < (frobDartWord I + ilkArt).toNat) :
    ExecBlock config { contract := contract, locals := frobStore I } evm
      (pre ++
        checkedAddSignedInto "urnInkNew" (.var "urnInk") (.var "dink") ++
        checkedAddSignedInto "urnArtNew" (.var "urnArt") (.var "dart") ++
        checkedAddSignedInto "ilkArtNew" (.var "ilkArt") (.var "dart"))
      .reverted := by
  let localsLoaded :=
    frobStoreIlkDust I urnInk urnArt ilkArt ilkRate ilkSpot ilkLine ilkDust
  let urnInkNew := frobDinkWord I + urnInk
  let urnArtNew := frobDartWord I + urnArt
  let ilkArtNew := frobDartWord I + ilkArt
  have hInkBlock :
      ExecBlock config { contract := contract, locals := localsLoaded } evm
        (checkedAddSignedInto "urnInkNew" (.var "urnInk") (.var "dink"))
        (.ok
          { contract := contract,
            locals := localsLoaded.insert "urnInkNew"
              (.int (Int.ofNat urnInkNew.toNat)) }
          evm) := by
    exact execFrobUrnInkAddOk (I := I) localsLoaded urnInk urnInkNew
      (by
        simpa [localsLoaded] using
          frobStoreIlkDust_get_urnInk I urnInk urnArt ilkArt ilkRate ilkSpot ilkLine
            ilkDust)
      (by
        simpa [localsLoaded] using
          frobStoreIlkDust_get_dink I urnInk urnArt ilkArt ilkRate ilkSpot ilkLine
            ilkDust)
      (by simp [urnInkNew]) (by simpa [urnInkNew] using hInkNeg)
      (by simpa [urnInkNew] using hInkPos)
  let localsInk := localsLoaded.insert "urnInkNew" (.int (Int.ofNat urnInkNew.toNat))
  have hArtBlock :
      ExecBlock config { contract := contract, locals := localsInk } evm
        (checkedAddSignedInto "urnArtNew" (.var "urnArt") (.var "dart"))
        (.ok
          { contract := contract,
            locals := localsInk.insert "urnArtNew" (.int (Int.ofNat urnArtNew.toNat)) }
          evm) := by
    exact execFrobUrnArtAddOk (I := I) localsInk urnArt urnArtNew
      (by
        change (localsLoaded.insert "urnInkNew"
          (.int (Int.ofNat urnInkNew.toNat))).get? "urnArt" =
          some (.int (Int.ofNat urnArt.toNat))
        rw [store_get_ne _ _ (by decide)]
        simpa [localsLoaded] using
          frobStoreIlkDust_get_urnArt I urnInk urnArt ilkArt ilkRate ilkSpot ilkLine
            ilkDust)
      (by
        change (localsLoaded.insert "urnInkNew"
          (.int (Int.ofNat urnInkNew.toNat))).get? "dart" =
          some (frobDartValue I)
        rw [store_get_ne _ _ (by decide)]
        simpa [localsLoaded] using
          frobStoreIlkDust_get_dart I urnInk urnArt ilkArt ilkRate ilkSpot ilkLine
            ilkDust)
      (by simp [urnArtNew]) (by simpa [urnArtNew] using hArtNeg)
      (by simpa [urnArtNew] using hArtPos)
  let localsArt := localsInk.insert "urnArtNew" (.int (Int.ofNat urnArtNew.toNat))
  have hIlkBlock :
      ExecBlock config { contract := contract, locals := localsArt } evm
        (checkedAddSignedInto "ilkArtNew" (.var "ilkArt") (.var "dart"))
        .reverted := by
    exact execFrobIlkArtAddRevertGuardNeg (I := I) localsArt ilkArt ilkArtNew
      (by
        change ((localsLoaded.insert "urnInkNew" (.int (Int.ofNat urnInkNew.toNat))).insert
          "urnArtNew" (.int (Int.ofNat urnArtNew.toNat))).get? "ilkArt" =
          some (.int (Int.ofNat ilkArt.toNat))
        rw [store_get_ne _ _ (by decide)]
        rw [store_get_ne _ _ (by decide)]
        simpa [localsLoaded] using
          frobStoreIlkDust_get_ilkArt I urnInk urnArt ilkArt ilkRate ilkSpot ilkLine
            ilkDust)
      (by
        change ((localsLoaded.insert "urnInkNew" (.int (Int.ofNat urnInkNew.toNat))).insert
          "urnArtNew" (.int (Int.ofNat urnArtNew.toNat))).get? "dart" =
          some (frobDartValue I)
        rw [store_get_ne _ _ (by decide)]
        rw [store_get_ne _ _ (by decide)]
        simpa [localsLoaded] using
          frobStoreIlkDust_get_dart I urnInk urnArt ilkArt ilkRate ilkSpot ilkLine
            ilkDust)
      (by simp [ilkArtNew]) (by simpa [ilkArtNew] using hcond)
  have h01 := Reasoning.Refinement.execBlock_append hprefix
    (by simpa [localsLoaded] using hInkBlock)
  have h02 := Reasoning.Refinement.execBlock_append h01
    (by simpa [localsLoaded, localsInk] using hArtBlock)
  have h03 := Reasoning.Refinement.execBlock_append h02
    (by simpa [localsLoaded, localsInk, localsArt] using hIlkBlock)
  simpa [localsLoaded, localsInk, localsArt, List.append_assoc] using h03

theorem execFrobLoadedPrefixIlkArtRevertGuardPos {evm : EVM.State} {I : ExecutionEnv}
    {pre : List Stmt}
    (urnInk urnArt ilkArt ilkRate ilkSpot ilkLine ilkDust : UInt256)
    (hprefix :
      ExecBlock config { contract := contract, locals := frobStore I } evm pre
        (.ok
          { contract := contract,
            locals := frobStoreIlkDust I urnInk urnArt ilkArt ilkRate ilkSpot ilkLine
              ilkDust }
          evm))
    (hInkNeg : 0 ≤ frobDinkInt I ∨ (frobDinkWord I + urnInk).toNat ≤ urnInk.toNat)
    (hInkPos : frobDinkInt I ≤ 0 ∨ urnInk.toNat ≤ (frobDinkWord I + urnInk).toNat)
    (hArtNeg : 0 ≤ frobDartInt I ∨ (frobDartWord I + urnArt).toNat ≤ urnArt.toNat)
    (hArtPos : frobDartInt I ≤ 0 ∨ urnArt.toNat ≤ (frobDartWord I + urnArt).toNat)
    (hIlkNeg : 0 ≤ frobDartInt I ∨ (frobDartWord I + ilkArt).toNat ≤ ilkArt.toNat)
    (hcond :
      0 < frobDartInt I ∧ (frobDartWord I + ilkArt).toNat < ilkArt.toNat) :
    ExecBlock config { contract := contract, locals := frobStore I } evm
      (pre ++
        checkedAddSignedInto "urnInkNew" (.var "urnInk") (.var "dink") ++
        checkedAddSignedInto "urnArtNew" (.var "urnArt") (.var "dart") ++
        checkedAddSignedInto "ilkArtNew" (.var "ilkArt") (.var "dart"))
      .reverted := by
  let localsLoaded :=
    frobStoreIlkDust I urnInk urnArt ilkArt ilkRate ilkSpot ilkLine ilkDust
  let urnInkNew := frobDinkWord I + urnInk
  let urnArtNew := frobDartWord I + urnArt
  let ilkArtNew := frobDartWord I + ilkArt
  have hInkBlock :
      ExecBlock config { contract := contract, locals := localsLoaded } evm
        (checkedAddSignedInto "urnInkNew" (.var "urnInk") (.var "dink"))
        (.ok
          { contract := contract,
            locals := localsLoaded.insert "urnInkNew"
              (.int (Int.ofNat urnInkNew.toNat)) }
          evm) := by
    exact execFrobUrnInkAddOk (I := I) localsLoaded urnInk urnInkNew
      (by
        simpa [localsLoaded] using
          frobStoreIlkDust_get_urnInk I urnInk urnArt ilkArt ilkRate ilkSpot ilkLine
            ilkDust)
      (by
        simpa [localsLoaded] using
          frobStoreIlkDust_get_dink I urnInk urnArt ilkArt ilkRate ilkSpot ilkLine
            ilkDust)
      (by simp [urnInkNew]) (by simpa [urnInkNew] using hInkNeg)
      (by simpa [urnInkNew] using hInkPos)
  let localsInk := localsLoaded.insert "urnInkNew" (.int (Int.ofNat urnInkNew.toNat))
  have hArtBlock :
      ExecBlock config { contract := contract, locals := localsInk } evm
        (checkedAddSignedInto "urnArtNew" (.var "urnArt") (.var "dart"))
        (.ok
          { contract := contract,
            locals := localsInk.insert "urnArtNew" (.int (Int.ofNat urnArtNew.toNat)) }
          evm) := by
    exact execFrobUrnArtAddOk (I := I) localsInk urnArt urnArtNew
      (by
        change (localsLoaded.insert "urnInkNew"
          (.int (Int.ofNat urnInkNew.toNat))).get? "urnArt" =
          some (.int (Int.ofNat urnArt.toNat))
        rw [store_get_ne _ _ (by decide)]
        simpa [localsLoaded] using
          frobStoreIlkDust_get_urnArt I urnInk urnArt ilkArt ilkRate ilkSpot ilkLine
            ilkDust)
      (by
        change (localsLoaded.insert "urnInkNew"
          (.int (Int.ofNat urnInkNew.toNat))).get? "dart" =
          some (frobDartValue I)
        rw [store_get_ne _ _ (by decide)]
        simpa [localsLoaded] using
          frobStoreIlkDust_get_dart I urnInk urnArt ilkArt ilkRate ilkSpot ilkLine
            ilkDust)
      (by simp [urnArtNew]) (by simpa [urnArtNew] using hArtNeg)
      (by simpa [urnArtNew] using hArtPos)
  let localsArt := localsInk.insert "urnArtNew" (.int (Int.ofNat urnArtNew.toNat))
  have hIlkBlock :
      ExecBlock config { contract := contract, locals := localsArt } evm
        (checkedAddSignedInto "ilkArtNew" (.var "ilkArt") (.var "dart"))
        .reverted := by
    exact execFrobIlkArtAddRevertGuardPos (I := I) localsArt ilkArt ilkArtNew
      (by
        change ((localsLoaded.insert "urnInkNew" (.int (Int.ofNat urnInkNew.toNat))).insert
          "urnArtNew" (.int (Int.ofNat urnArtNew.toNat))).get? "ilkArt" =
          some (.int (Int.ofNat ilkArt.toNat))
        rw [store_get_ne _ _ (by decide)]
        rw [store_get_ne _ _ (by decide)]
        simpa [localsLoaded] using
          frobStoreIlkDust_get_ilkArt I urnInk urnArt ilkArt ilkRate ilkSpot ilkLine
            ilkDust)
      (by
        change ((localsLoaded.insert "urnInkNew" (.int (Int.ofNat urnInkNew.toNat))).insert
          "urnArtNew" (.int (Int.ofNat urnArtNew.toNat))).get? "dart" =
          some (frobDartValue I)
        rw [store_get_ne _ _ (by decide)]
        rw [store_get_ne _ _ (by decide)]
        simpa [localsLoaded] using
          frobStoreIlkDust_get_dart I urnInk urnArt ilkArt ilkRate ilkSpot ilkLine
            ilkDust)
      (by simp [ilkArtNew]) (by simpa [ilkArtNew] using hIlkNeg)
      (by simpa [ilkArtNew] using hcond)
  have h01 := Reasoning.Refinement.execBlock_append hprefix
    (by simpa [localsLoaded] using hInkBlock)
  have h02 := Reasoning.Refinement.execBlock_append h01
    (by simpa [localsLoaded, localsInk] using hArtBlock)
  have h03 := Reasoning.Refinement.execBlock_append h02
    (by simpa [localsLoaded, localsInk, localsArt] using hIlkBlock)
  simpa [localsLoaded, localsInk, localsArt, List.append_assoc] using h03

theorem vatFrobSourceBodyNotLive {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hlive : vatSlotWord ⟨10⟩ σ I ≠ ⟨1⟩) :
    let locals := frobStore I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 locals frobTransition.body .reverted := by
  intro locals evm0
  have hguardLive := vatLiveGuardEval_false (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := Sat256.ofUInt256 g) (locals := locals)
    (by change (frobStore I).get? "live" = none; exact frobStore_get_live I)
    hlive
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0 frobTransition.body
        .reverted := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    exact ExecBlock.consRevert (ExecStmt.requireFalse hguardLive)
  simpa [ExecTransitionBody, frobTransition, nonpayable, requireLive, evm0, locals] using
    ExecFuncBody.execBlockRevert hblock

theorem vatDecode_frob_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 196) :
    decodeCalldataWithMode config.abiDecodeMode (frobTransition.params.map Param.name)
      (transitionSignature frobTransition).paramTypes I.calldata = none := by
  show decodeCalldataWithMode config.abiDecodeMode ["i", "u", "v", "w", "dink", "dart"]
    [bytes32, addr, addr, addr, int256, int256] I.calldata = none
  change decodeCalldataWithMode DecodeMode.legacySolc05 ["i", "u", "v", "w", "dink", "dart"]
    [bytes32, addr, addr, addr, int256, int256] I.calldata = none
  have htlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  unfold decodeCalldataWithMode decodeCalldata
  rw [if_neg (by rw [htlen]; omega : ¬ I.calldata.toList.length < 4)]
  rw [if_neg (by simp [bytes32, addr, int256, isDynamicABIType])]
  simp only
  simp only [decodeCalldata.decodeArgs]
  rw [show abiTupleHeadSize? [bytes32, addr, addr, addr, int256, int256] =
    some 192 by native_decide]
  simp only [bind, Option.bind]
  rw [if_pos (by rw [List.length_drop, htlen]; omega :
    (I.calldata.toList.drop 4).length < 192)]

theorem vatDecode_frob_ok {I : ExecutionEnv} (hsz196 : 196 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (frobTransition.params.map Param.name)
      (transitionSignature frobTransition).paramTypes I.calldata = some (frobStore I) := by
  show decodeCalldataWithMode config.abiDecodeMode ["i", "u", "v", "w", "dink", "dart"]
    [bytes32, addr, addr, addr, int256, int256] I.calldata = some (frobStore I)
  change decodeCalldataWithMode DecodeMode.legacySolc05 ["i", "u", "v", "w", "dink", "dart"]
    [bytes32, addr, addr, addr, int256, int256] I.calldata = some (frobStore I)
  rw [vatDecodeCalldata_legacyBytes32_address_address_address_int256_int256_ok
    (cd := I.calldata) (a := "i") (b := "u") (c := "v") (d := "w")
    (e := "dink") (f := "dart") hsz196]

theorem vatDispatchFrob {I : ExecutionEnv}
    (hsel : selIs I (vatSelBytes 11)) :
    dispatchMsg contract I.calldata = some frobTransition := by
  have hcd : I.calldata.extract 0 4 = vatSelBytes 11 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some frobTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd, LineSelectorBytes, cageSelectorBytes,
    canSelectorBytes, daiSelectorBytes, debtSelectorBytes, denySelectorBytes,
    fileIlkSelectorBytes, fileLineSelectorBytes, fluxSelectorBytes, foldSelectorBytes,
    forkSelectorBytes, frobSelectorBytes]
  native_decide

theorem vatReachFrobBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = vatBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (vatSelBytes 11)) :
    ∃ k C, RD vatBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨901⟩ [vatSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  have hword : vatSelWord I = ⟨0x76088703⟩ :=
    vatSelWord_eq_of_beq I hsz 0x76 0x08 0x87 0x03 ⟨0x76088703⟩
      (by native_decide) (by simpa [vatSelBytes] using hsel)
  have hroot : UInt256.gt (armSelNat vatBytecode vatRootSplitPc) (vatSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  have hlow : UInt256.gt (armSelNat vatBytecode vatLowSplitPc) (vatSelWord I) = ⟨0⟩ := by
    rw [hword]
    native_decide
  have hlowhigh :
      UInt256.gt (armSelNat vatBytecode vatLowHighSplitPc) (vatSelWord I) = ⟨0⟩ := by
    rw [hword]
    native_decide
  have heq0 : ∀ j, j < 2 →
      UInt256.eq (armSelNat vatBytecode (nthArmPc vatBytecode vatArms272FirstPc j))
        (vatSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j
    · rw [hword]
      native_decide
    · rw [hword]
      native_decide
  have htake :
      UInt256.eq (armSelNat vatBytecode (nthArmPc vatBytecode vatArms272FirstPc 2))
        (vatSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  exact vatReachArms272Body 2 (by omega) ⟨901⟩ hcode hwv hsz hsize
    hroot hlow hlowhigh heq0 htake (by jump_dest) (by native_decide)

theorem vatFrobX_decoded {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz196 : 196 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hreach : ∃ k C, RD vatBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨901⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD vatBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2975⟩
        [frobDartWord I, frobDinkWord I, frobWMaskedWord I, frobVMaskedWord I,
          frobUMaskedWord I, frobIWord I, ⟨524⟩, sel]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, hdecoded⟩ := RD.solcExternalStaticArgsLenOk
    (code := vatBytecode) (sel := sel) (entry := ⟨901⟩) (ret := ⟨524⟩)
    (decoded := ⟨923⟩) (need := ⟨192⟩) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by jump_dest)
    (by exact solcDecodeLenCheckOkUnsigned (by simpa using hsz196) hsize)
  obtain ⟨_, _, hroutine⟩ := RD.solcSixWordThreeAddressExternalLoadAndJump
    (code := vatBytecode) (decoded := ⟨923⟩) (ret := ⟨524⟩) (routine := ⟨2975⟩)
    (R := [sel]) hdecoded
    (by
      unfold solcSixWordThreeAddressExternalLoadAndJumpWf
      repeat' first | apply And.intro | native_decide)
    (by jump_dest) (by simp)
  exact ⟨_, _, by
    simpa [frobDartWord, frobDinkWord, frobWMaskedWord, frobWWord,
      frobVMaskedWord, frobVWord, frobUMaskedWord, frobUWord, frobIWord]
      using hroutine⟩

theorem vatFrobX_shortarg {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 196)
    (hsize : I.calldata.size < UInt256.size)
    (hreach : ∃ k C, RD vatBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨901⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev vatBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hlt :
      UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨192⟩ = ⟨1⟩ := by
    apply ult_one
    rw [usub_ofNat_word_toNat (by simpa using hsz4) hsize]
    change I.calldata.size - 4 < 192
    omega
  exact RD.solcExternalStaticArgsShortReverts
    (code := vatBytecode) (sel := sel) (entry := ⟨901⟩) (ret := ⟨524⟩)
    (decoded := ⟨923⟩) (need := ⟨192⟩) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) hlt

theorem vatFrobBodyCoreDecodeFailed_short
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = vatBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 196)
    (hsel : selIs I (vatSelBytes 11))
    (hreach : ∃ k C, RD vatBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨901⟩ [vatSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  exact (vatFrobX_shortarg (g := Sat256.ofUInt256 g) hsz4 hshort hsize hreach)
    |>.reEquivDecodingFailed hcode (vatDispatchFrob hsel)
      (vatDecode_frob_none_short hsz4 hshort)

theorem vatFrobBodyCoreNotLive
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = vatBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩) (hsz196 : 196 ≤ I.calldata.size)
    (hlive : vatSlotWord ⟨10⟩ σ_evm I ≠ ⟨1⟩)
    (hdispatch : dispatchMsg contract I.calldata = some frobTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (frobTransition.params.map Param.name)
        (transitionSignature frobTransition).paramTypes I.calldata = some (frobStore I))
    (hreach : ∃ k C, RD vatBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨901⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let locals := frobStore I
  let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hliveWord : vatSlotWord ⟨10⟩ σ_evm I = vatSlotWord ⟨10⟩ σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨10⟩ ⟨0⟩
  have hliveSolm : vatSlotWord ⟨10⟩ σ_solm I ≠ ⟨1⟩ := by
    intro hbad
    exact hlive (by rw [hliveWord, hbad])
  have hbody :
      ExecTransitionBody config contract evm0 locals frobTransition.body .reverted := by
    simpa [evm0, locals] using
      (vatFrobSourceBodyNotLive (cA := cA) (gh := gh) (bl := bl)
        (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g) hwv hliveSolm)
  obtain ⟨_, _, hdecoded⟩ := vatFrobX_decoded (g := Sat256.ofUInt256 g)
    hsz196 hsize hreach
  have hliveSolc : solcSlotWord σ_evm I ⟨10⟩ ≠ ⟨1⟩ := by
    simpa [vatSlotWord] using hlive
  have hmem :
      solcFreePtrMem.size = 96 :=
    solcFreePtrMem_size
  have hread64 :
      solcFreePtrMem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ :=
    solcFreePtrMem_read64
  have hrev := RD.vatLiveGuardRevert
    (code := vatBytecode) (pc := ⟨2975⟩) (okPc := ⟨3045⟩)
    (key := frobDartWord I) (ret := frobDinkWord I)
    (R := [frobWMaskedWord I, frobVMaskedWord I, frobUMaskedWord I, frobIWord I, ⟨524⟩, sel])
    hdecoded
    (by unfold vatLiveGuardWf; repeat' first | apply And.intro | native_decide)
    (by
      unfold solcErrorStringRevertTailWf vatLiveGuardTailPc vatNotLiveRawWord
      repeat' first | apply And.intro | native_decide)
    hliveSolc hmem hread64 (by simp)
  exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody


end Benchmarks.Dss.Vat
