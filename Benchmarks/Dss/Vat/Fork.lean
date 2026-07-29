import Benchmarks.Dss.Vat.Signed

namespace Benchmarks.Dss.Vat

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

/-! ## `fork(bytes32,address,address,int256,int256)` -/

abbrev forkIlkWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 4

abbrev forkSrcWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 36

abbrev forkSrcMaskedWord (I : ExecutionEnv) : UInt256 :=
  UInt256.land solcAddrMask (forkSrcWord I)

abbrev forkDstWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 68

abbrev forkDstMaskedWord (I : ExecutionEnv) : UInt256 :=
  UInt256.land solcAddrMask (forkDstWord I)

abbrev forkDinkWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 100

abbrev forkDartWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 132

abbrev forkDinkInt (I : ExecutionEnv) : Int :=
  if (forkDinkWord I).toNat < EVM.twoPow 255 then
    Int.ofNat (forkDinkWord I).toNat
  else
    Int.ofNat (forkDinkWord I).toNat - Int.ofNat EVM.wordModulus

abbrev forkDartInt (I : ExecutionEnv) : Int :=
  if (forkDartWord I).toNat < EVM.twoPow 255 then
    Int.ofNat (forkDartWord I).toNat
  else
    Int.ofNat (forkDartWord I).toNat - Int.ofNat EVM.wordModulus

theorem forkDinkInt_mod_word (I : ExecutionEnv) :
    forkDinkInt I % (Int.ofNat EVM.wordModulus) =
      Int.ofNat (forkDinkWord I).toNat := by
  have hltMod :
      Int.ofNat (forkDinkWord I).toNat < Int.ofNat EVM.wordModulus := by
    exact Int.ofNat_lt.mpr (by
      change (forkDinkWord I).val.val < EVM.twoPow 256
      exact (forkDinkWord I).val.isLt)
  have hbase :
      Int.ofNat (forkDinkWord I).toNat % Int.ofNat EVM.wordModulus =
        Int.ofNat (forkDinkWord I).toNat :=
    Int.emod_eq_of_lt (Int.natCast_nonneg _) hltMod
  unfold forkDinkInt
  split
  · exact hbase
  · rw [← Int.emod_eq_sub_self_emod]
    exact hbase

theorem forkDartInt_mod_word (I : ExecutionEnv) :
    forkDartInt I % (Int.ofNat EVM.wordModulus) =
      Int.ofNat (forkDartWord I).toNat := by
  have hltMod :
      Int.ofNat (forkDartWord I).toNat < Int.ofNat EVM.wordModulus := by
    exact Int.ofNat_lt.mpr (by
      change (forkDartWord I).val.val < EVM.twoPow 256
      exact (forkDartWord I).val.isLt)
  have hbase :
      Int.ofNat (forkDartWord I).toNat % Int.ofNat EVM.wordModulus =
        Int.ofNat (forkDartWord I).toNat :=
    Int.emod_eq_of_lt (Int.natCast_nonneg _) hltMod
  unfold forkDartInt
  split
  · exact hbase
  · rw [← Int.emod_eq_sub_self_emod]
    exact hbase

abbrev forkIlkValue (I : ExecutionEnv) : Value :=
  .fixedBytes bytes32Width ((I.calldata.toList.drop 4).take 32)

abbrev forkSrcValue (I : ExecutionEnv) : Value :=
  .address (AccountAddress.ofNat (forkSrcWord I).toNat)

abbrev forkDstValue (I : ExecutionEnv) : Value :=
  .address (AccountAddress.ofNat (forkDstWord I).toNat)

abbrev forkDinkValue (I : ExecutionEnv) : Value :=
  .int (forkDinkInt I)

abbrev forkDartValue (I : ExecutionEnv) : Value :=
  .int (forkDartInt I)

abbrev forkStore (I : ExecutionEnv) : Store :=
  (((((∅ : Store).insert "ilk" (forkIlkValue I)).insert "src" (forkSrcValue I)).insert
    "dst" (forkDstValue I)).insert "dink" (forkDinkValue I)).insert "dart" (forkDartValue I)

abbrev forkIlkKey (I : ExecutionEnv) : KeyValue :=
  .fixedBytes bytes32Width ((I.calldata.toList.drop 4).take 32)

abbrev forkSrcKey (I : ExecutionEnv) : KeyValue :=
  .address (AccountAddress.ofNat (forkSrcWord I).toNat)

abbrev forkDstKey (I : ExecutionEnv) : KeyValue :=
  .address (AccountAddress.ofNat (forkDstWord I).toNat)

abbrev forkSourceKey (I : ExecutionEnv) : KeyValue :=
  .address I.source

def forkSrcUrnBase (I : ExecutionEnv) : UInt256 :=
  urnsBase (forkIlkKey I) (forkSrcKey I)

def forkDstUrnBase (I : ExecutionEnv) : UInt256 :=
  urnsBase (forkIlkKey I) (forkDstKey I)

def forkIlkBase (I : ExecutionEnv) : UInt256 :=
  ilksBase (forkIlkKey I)

def forkSrcInkSlot (I : ExecutionEnv) : UInt256 := forkSrcUrnBase I
def forkSrcArtSlot (I : ExecutionEnv) : UInt256 := forkSrcUrnBase I + ⟨1⟩
def forkDstInkSlot (I : ExecutionEnv) : UInt256 := forkDstUrnBase I
def forkDstArtSlot (I : ExecutionEnv) : UInt256 := forkDstUrnBase I + ⟨1⟩
def forkIlkRateSlot (I : ExecutionEnv) : UInt256 := forkIlkBase I + ⟨1⟩
def forkIlkSpotSlot (I : ExecutionEnv) : UInt256 := forkIlkBase I + ⟨2⟩
def forkIlkDustSlot (I : ExecutionEnv) : UInt256 := forkIlkBase I + ⟨4⟩
def forkSrcWishSlot (I : ExecutionEnv) : UInt256 := canSlot (forkSrcKey I) (forkSourceKey I)
def forkDstWishSlot (I : ExecutionEnv) : UInt256 := canSlot (forkDstKey I) (forkSourceKey I)

def forkSrcInkNew (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.sub (solcSlotWord σ I (forkSrcInkSlot I)) (forkDinkWord I)

def forkAfterSrcInk (σ : AccountMap) (I : ExecutionEnv) : AccountMap :=
  sstoreAccountMap I.codeOwner σ (forkSrcInkSlot I) (forkSrcInkNew σ I)

def forkSrcArtNew (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.sub (solcSlotWord (forkAfterSrcInk σ I) I (forkSrcArtSlot I)) (forkDartWord I)

def forkAfterSrcArt (σ : AccountMap) (I : ExecutionEnv) : AccountMap :=
  sstoreAccountMap I.codeOwner (forkAfterSrcInk σ I) (forkSrcArtSlot I)
    (forkSrcArtNew σ I)

def forkDstInkNew (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  forkDinkWord I + solcSlotWord (forkAfterSrcArt σ I) I (forkDstInkSlot I)

def forkAfterDstInk (σ : AccountMap) (I : ExecutionEnv) : AccountMap :=
  sstoreAccountMap I.codeOwner (forkAfterSrcArt σ I) (forkDstInkSlot I)
    (forkDstInkNew σ I)

def forkDstArtNew (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  forkDartWord I + solcSlotWord (forkAfterDstInk σ I) I (forkDstArtSlot I)

def forkAfterDstArt (σ : AccountMap) (I : ExecutionEnv) : AccountMap :=
  sstoreAccountMap I.codeOwner (forkAfterDstInk σ I) (forkDstArtSlot I)
    (forkDstArtNew σ I)

abbrev forkSrcWishWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.lor
    (UInt256.eq (vatSlotWord (forkSrcWishSlot I) σ I) ⟨1⟩)
    (UInt256.eq (forkSrcMaskedWord I) (hopeSourceWord I))

abbrev forkDstWishWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.lor
    (UInt256.eq (vatSlotWord (forkDstWishSlot I) σ I) ⟨1⟩)
    (UInt256.eq (forkDstMaskedWord I) (hopeSourceWord I))

abbrev forkBothWishWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.land (forkDstWishWord σ I) (forkSrcWishWord σ I)

theorem forkDinkAddGuardNegCond {I : ExecutionEnv} {old new : UInt256}
    (h :
      UInt256.slt (forkDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.gt new old = ⟨0⟩) :
    0 ≤ forkDinkInt I ∨ new.toNat ≤ old.toNat := by
  cases h with
  | inl hslt =>
      exact Or.inl (slt_zero_eq_zero_to_nonneg (forkDinkWord I) hslt)
  | inr hgt =>
      exact Or.inr (ugt_eq_zero_to_le hgt)

theorem forkDinkAddGuardPosCond {I : ExecutionEnv} {old new : UInt256}
    (h :
      UInt256.sgt (forkDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.lt new old = ⟨0⟩) :
    forkDinkInt I ≤ 0 ∨ old.toNat ≤ new.toNat := by
  cases h with
  | inl hsgt =>
      exact Or.inl (sgt_zero_eq_zero_to_nonpos (forkDinkWord I) hsgt)
  | inr hlt =>
      exact Or.inr (ult_eq_zero_to_le hlt)

theorem forkDartAddGuardNegCond {I : ExecutionEnv} {old new : UInt256}
    (h :
      UInt256.slt (forkDartWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.gt new old = ⟨0⟩) :
    0 ≤ forkDartInt I ∨ new.toNat ≤ old.toNat := by
  cases h with
  | inl hslt =>
      exact Or.inl (slt_zero_eq_zero_to_nonneg (forkDartWord I) hslt)
  | inr hgt =>
      exact Or.inr (ugt_eq_zero_to_le hgt)

theorem forkDartAddGuardPosCond {I : ExecutionEnv} {old new : UInt256}
    (h :
      UInt256.sgt (forkDartWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.lt new old = ⟨0⟩) :
    forkDartInt I ≤ 0 ∨ old.toNat ≤ new.toNat := by
  cases h with
  | inl hsgt =>
      exact Or.inl (sgt_zero_eq_zero_to_nonpos (forkDartWord I) hsgt)
  | inr hlt =>
      exact Or.inr (ult_eq_zero_to_le hlt)

theorem forkDinkAddGuardNegFailCond {I : ExecutionEnv} {old new : UInt256}
    (h :
      ¬ (UInt256.slt (forkDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.gt new old = ⟨0⟩)) :
    forkDinkInt I < 0 ∧ old.toNat < new.toNat := by
  constructor
  · exact slt_zero_ne_zero_to_neg (forkDinkWord I) (by
      intro hslt
      exact h (Or.inl hslt))
  · exact ugt_ne_zero_to_gt (by
      intro hgt
      exact h (Or.inr hgt))

theorem forkDinkAddGuardPosFailCond {I : ExecutionEnv} {old new : UInt256}
    (h :
      ¬ (UInt256.sgt (forkDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.lt new old = ⟨0⟩)) :
    0 < forkDinkInt I ∧ new.toNat < old.toNat := by
  constructor
  · exact sgt_zero_ne_zero_to_pos (forkDinkWord I) (by
      intro hsgt
      exact h (Or.inl hsgt))
  · exact ult_ne_zero_to_lt (by
      intro hlt
      exact h (Or.inr hlt))

theorem forkDartAddGuardNegFailCond {I : ExecutionEnv} {old new : UInt256}
    (h :
      ¬ (UInt256.slt (forkDartWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.gt new old = ⟨0⟩)) :
    forkDartInt I < 0 ∧ old.toNat < new.toNat := by
  constructor
  · exact slt_zero_ne_zero_to_neg (forkDartWord I) (by
      intro hslt
      exact h (Or.inl hslt))
  · exact ugt_ne_zero_to_gt (by
      intro hgt
      exact h (Or.inr hgt))

theorem forkDartAddGuardPosFailCond {I : ExecutionEnv} {old new : UInt256}
    (h :
      ¬ (UInt256.sgt (forkDartWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.lt new old = ⟨0⟩)) :
    0 < forkDartInt I ∧ new.toNat < old.toNat := by
  constructor
  · exact sgt_zero_ne_zero_to_pos (forkDartWord I) (by
      intro hsgt
      exact h (Or.inl hsgt))
  · exact ult_ne_zero_to_lt (by
      intro hlt
      exact h (Or.inr hlt))

theorem forkDinkSubGuardNegCond {I : ExecutionEnv} {old new : UInt256}
    (h :
      UInt256.sgt (forkDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.gt new old = ⟨0⟩) :
    forkDinkInt I ≤ 0 ∨ new.toNat ≤ old.toNat := by
  cases h with
  | inl hsgt =>
      exact Or.inl (sgt_zero_eq_zero_to_nonpos (forkDinkWord I) hsgt)
  | inr hgt =>
      exact Or.inr (ugt_eq_zero_to_le hgt)

theorem forkDinkSubGuardPosCond {I : ExecutionEnv} {old new : UInt256}
    (h :
      UInt256.slt (forkDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.lt new old = ⟨0⟩) :
    0 ≤ forkDinkInt I ∨ old.toNat ≤ new.toNat := by
  cases h with
  | inl hslt =>
      exact Or.inl (slt_zero_eq_zero_to_nonneg (forkDinkWord I) hslt)
  | inr hlt =>
      exact Or.inr (ult_eq_zero_to_le hlt)

theorem forkDartSubGuardNegCond {I : ExecutionEnv} {old new : UInt256}
    (h :
      UInt256.sgt (forkDartWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.gt new old = ⟨0⟩) :
    forkDartInt I ≤ 0 ∨ new.toNat ≤ old.toNat := by
  cases h with
  | inl hsgt =>
      exact Or.inl (sgt_zero_eq_zero_to_nonpos (forkDartWord I) hsgt)
  | inr hgt =>
      exact Or.inr (ugt_eq_zero_to_le hgt)

theorem forkDartSubGuardPosCond {I : ExecutionEnv} {old new : UInt256}
    (h :
      UInt256.slt (forkDartWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.lt new old = ⟨0⟩) :
    0 ≤ forkDartInt I ∨ old.toNat ≤ new.toNat := by
  cases h with
  | inl hslt =>
      exact Or.inl (slt_zero_eq_zero_to_nonneg (forkDartWord I) hslt)
  | inr hlt =>
      exact Or.inr (ult_eq_zero_to_le hlt)

theorem forkDinkSubGuardNegFailCond {I : ExecutionEnv} {old new : UInt256}
    (h :
      ¬ (UInt256.sgt (forkDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.gt new old = ⟨0⟩)) :
    0 < forkDinkInt I ∧ old.toNat < new.toNat := by
  constructor
  · exact sgt_zero_ne_zero_to_pos (forkDinkWord I) (by
      intro hsgt
      exact h (Or.inl hsgt))
  · exact ugt_ne_zero_to_gt (by
      intro hgt
      exact h (Or.inr hgt))

theorem forkDinkSubGuardPosFailCond {I : ExecutionEnv} {old new : UInt256}
    (h :
      ¬ (UInt256.slt (forkDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.lt new old = ⟨0⟩)) :
    forkDinkInt I < 0 ∧ new.toNat < old.toNat := by
  constructor
  · exact slt_zero_ne_zero_to_neg (forkDinkWord I) (by
      intro hslt
      exact h (Or.inl hslt))
  · exact ult_ne_zero_to_lt (by
      intro hlt
      exact h (Or.inr hlt))

theorem forkDartSubGuardNegFailCond {I : ExecutionEnv} {old new : UInt256}
    (h :
      ¬ (UInt256.sgt (forkDartWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.gt new old = ⟨0⟩)) :
    0 < forkDartInt I ∧ old.toNat < new.toNat := by
  constructor
  · exact sgt_zero_ne_zero_to_pos (forkDartWord I) (by
      intro hsgt
      exact h (Or.inl hsgt))
  · exact ugt_ne_zero_to_gt (by
      intro hgt
      exact h (Or.inr hgt))

theorem forkDartSubGuardPosFailCond {I : ExecutionEnv} {old new : UInt256}
    (h :
      ¬ (UInt256.slt (forkDartWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.lt new old = ⟨0⟩)) :
    forkDartInt I < 0 ∧ new.toNat < old.toNat := by
  constructor
  · exact slt_zero_ne_zero_to_neg (forkDartWord I) (by
      intro hslt
      exact h (Or.inl hslt))
  · exact ult_ne_zero_to_lt (by
      intro hlt
      exact h (Or.inr hlt))

theorem accountMapEquiv_forkAfterSrcInk {σ τ : AccountMap} {I : ExecutionEnv}
    (hAccounts : accountMapEquiv σ τ) :
    accountMapEquiv (forkAfterSrcInk σ I) (forkAfterSrcInk τ I) := by
  have hSrcInkOld :
      solcSlotWord σ I (forkSrcInkSlot I) =
        solcSlotWord τ I (forkSrcInkSlot I) :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner (forkSrcInkSlot I) ⟨0⟩
  have hSrcInkNew : forkSrcInkNew σ I = forkSrcInkNew τ I := by
    simp [forkSrcInkNew, hSrcInkOld]
  simpa [forkAfterSrcInk, hSrcInkNew] using
    accountMapEquiv_sstoreAccountMap I.codeOwner (forkSrcInkSlot I)
      (forkSrcInkNew τ I) hAccounts

theorem accountMapEquiv_forkAfterSrcArt {σ τ : AccountMap} {I : ExecutionEnv}
    (hAccounts : accountMapEquiv σ τ) :
    accountMapEquiv (forkAfterSrcArt σ I) (forkAfterSrcArt τ I) := by
  have hSrcInk := accountMapEquiv_forkAfterSrcInk (I := I) hAccounts
  have hSrcArtOld :
      solcSlotWord (forkAfterSrcInk σ I) I (forkSrcArtSlot I) =
        solcSlotWord (forkAfterSrcInk τ I) I (forkSrcArtSlot I) :=
    accountMapEquiv_storage_findD hSrcInk I.codeOwner (forkSrcArtSlot I) ⟨0⟩
  have hSrcArtNew : forkSrcArtNew σ I = forkSrcArtNew τ I := by
    simp [forkSrcArtNew, hSrcArtOld]
  simpa [forkAfterSrcArt, hSrcArtNew] using
    accountMapEquiv_sstoreAccountMap I.codeOwner (forkSrcArtSlot I)
      (forkSrcArtNew τ I) hSrcInk

theorem accountMapEquiv_forkAfterDstInk {σ τ : AccountMap} {I : ExecutionEnv}
    (hAccounts : accountMapEquiv σ τ) :
    accountMapEquiv (forkAfterDstInk σ I) (forkAfterDstInk τ I) := by
  have hSrcArt := accountMapEquiv_forkAfterSrcArt (I := I) hAccounts
  have hDstInkOld :
      solcSlotWord (forkAfterSrcArt σ I) I (forkDstInkSlot I) =
        solcSlotWord (forkAfterSrcArt τ I) I (forkDstInkSlot I) :=
    accountMapEquiv_storage_findD hSrcArt I.codeOwner (forkDstInkSlot I) ⟨0⟩
  have hDstInkNew : forkDstInkNew σ I = forkDstInkNew τ I := by
    simp [forkDstInkNew, hDstInkOld]
  simpa [forkAfterDstInk, hDstInkNew] using
    accountMapEquiv_sstoreAccountMap I.codeOwner (forkDstInkSlot I)
      (forkDstInkNew τ I) hSrcArt

theorem accountMapEquiv_forkAfterDstArt {σ τ : AccountMap} {I : ExecutionEnv}
    (hAccounts : accountMapEquiv σ τ) :
    accountMapEquiv (forkAfterDstArt σ I) (forkAfterDstArt τ I) := by
  have hDstInk := accountMapEquiv_forkAfterDstInk (I := I) hAccounts
  have hDstArtOld :
      solcSlotWord (forkAfterDstInk σ I) I (forkDstArtSlot I) =
        solcSlotWord (forkAfterDstInk τ I) I (forkDstArtSlot I) :=
    accountMapEquiv_storage_findD hDstInk I.codeOwner (forkDstArtSlot I) ⟨0⟩
  have hDstArtNew : forkDstArtNew σ I = forkDstArtNew τ I := by
    simp [forkDstArtNew, hDstArtOld]
  simpa [forkAfterDstArt, hDstArtNew] using
    accountMapEquiv_sstoreAccountMap I.codeOwner (forkDstArtSlot I)
      (forkDstArtNew τ I) hDstInk

theorem forkSrcInkNew_eq_of_accountMapEquiv {σ τ : AccountMap} {I : ExecutionEnv}
    (hAccounts : accountMapEquiv σ τ) :
    forkSrcInkNew σ I = forkSrcInkNew τ I := by
  have hSrcInkOld :
      solcSlotWord σ I (forkSrcInkSlot I) =
        solcSlotWord τ I (forkSrcInkSlot I) :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner (forkSrcInkSlot I) ⟨0⟩
  simp [forkSrcInkNew, hSrcInkOld]

theorem forkSrcArtNew_eq_of_accountMapEquiv {σ τ : AccountMap} {I : ExecutionEnv}
    (hAccounts : accountMapEquiv σ τ) :
    forkSrcArtNew σ I = forkSrcArtNew τ I := by
  have hSrcInk := accountMapEquiv_forkAfterSrcInk (I := I) hAccounts
  have hSrcArtOld :
      solcSlotWord (forkAfterSrcInk σ I) I (forkSrcArtSlot I) =
        solcSlotWord (forkAfterSrcInk τ I) I (forkSrcArtSlot I) :=
    accountMapEquiv_storage_findD hSrcInk I.codeOwner (forkSrcArtSlot I) ⟨0⟩
  simp [forkSrcArtNew, hSrcArtOld]

theorem forkDstInkNew_eq_of_accountMapEquiv {σ τ : AccountMap} {I : ExecutionEnv}
    (hAccounts : accountMapEquiv σ τ) :
    forkDstInkNew σ I = forkDstInkNew τ I := by
  have hSrcArt := accountMapEquiv_forkAfterSrcArt (I := I) hAccounts
  have hDstInkOld :
      solcSlotWord (forkAfterSrcArt σ I) I (forkDstInkSlot I) =
        solcSlotWord (forkAfterSrcArt τ I) I (forkDstInkSlot I) :=
    accountMapEquiv_storage_findD hSrcArt I.codeOwner (forkDstInkSlot I) ⟨0⟩
  simp [forkDstInkNew, hDstInkOld]

theorem forkDstArtNew_eq_of_accountMapEquiv {σ τ : AccountMap} {I : ExecutionEnv}
    (hAccounts : accountMapEquiv σ τ) :
    forkDstArtNew σ I = forkDstArtNew τ I := by
  have hDstInk := accountMapEquiv_forkAfterDstInk (I := I) hAccounts
  have hDstArtOld :
      solcSlotWord (forkAfterDstInk σ I) I (forkDstArtSlot I) =
        solcSlotWord (forkAfterDstInk τ I) I (forkDstArtSlot I) :=
    accountMapEquiv_storage_findD hDstInk I.codeOwner (forkDstArtSlot I) ⟨0⟩
  simp [forkDstArtNew, hDstArtOld]

theorem forkAfterDstArt_slot_eq_of_accountMapEquiv {σ τ : AccountMap} {I : ExecutionEnv}
    (hAccounts : accountMapEquiv σ τ) (slot : UInt256) :
    solcSlotWord (forkAfterDstArt σ I) I slot =
      solcSlotWord (forkAfterDstArt τ I) I slot := by
  exact accountMapEquiv_storage_findD
    (accountMapEquiv_forkAfterDstArt (I := I) hAccounts) I.codeOwner slot ⟨0⟩

theorem forkSrcWishWord_eq_of_accountMapEquiv {σ τ : AccountMap} {I : ExecutionEnv}
    (hAccounts : accountMapEquiv σ τ) :
    forkSrcWishWord σ I = forkSrcWishWord τ I := by
  have hslot :
      vatSlotWord (forkSrcWishSlot I) σ I =
        vatSlotWord (forkSrcWishSlot I) τ I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner (forkSrcWishSlot I) ⟨0⟩
  unfold forkSrcWishWord
  simpa [vatSlotWord] using congrArg (fun w => UInt256.lor (UInt256.eq w ⟨1⟩)
    (UInt256.eq (forkSrcMaskedWord I) (hopeSourceWord I))) hslot

theorem forkDstWishWord_eq_of_accountMapEquiv {σ τ : AccountMap} {I : ExecutionEnv}
    (hAccounts : accountMapEquiv σ τ) :
    forkDstWishWord σ I = forkDstWishWord τ I := by
  have hslot :
      vatSlotWord (forkDstWishSlot I) σ I =
        vatSlotWord (forkDstWishSlot I) τ I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner (forkDstWishSlot I) ⟨0⟩
  unfold forkDstWishWord
  simpa [vatSlotWord] using congrArg (fun w => UInt256.lor (UInt256.eq w ⟨1⟩)
    (UInt256.eq (forkDstMaskedWord I) (hopeSourceWord I))) hslot

theorem forkBothWishWord_eq_of_accountMapEquiv {σ τ : AccountMap} {I : ExecutionEnv}
    (hAccounts : accountMapEquiv σ τ) :
    forkBothWishWord σ I = forkBothWishWord τ I := by
  simp [forkBothWishWord, forkSrcWishWord_eq_of_accountMapEquiv (I := I) hAccounts,
    forkDstWishWord_eq_of_accountMapEquiv (I := I) hAccounts]

theorem forkAfterDstArt_mulGuard_iff_of_accountMapEquiv
    {σ τ : AccountMap} {I : ExecutionEnv}
    (hAccounts : accountMapEquiv σ τ) (aSlot bSlot : UInt256) :
    (solcSlotWord (forkAfterDstArt σ I) I bSlot = ⟨0⟩ ∨
        UInt256.eq
          (UInt256.div
            (UInt256.mul
              (solcSlotWord (forkAfterDstArt σ I) I aSlot)
              (solcSlotWord (forkAfterDstArt σ I) I bSlot))
            (solcSlotWord (forkAfterDstArt σ I) I bSlot))
          (solcSlotWord (forkAfterDstArt σ I) I aSlot) ≠ ⟨0⟩) ↔
      (solcSlotWord (forkAfterDstArt τ I) I bSlot = ⟨0⟩ ∨
        UInt256.eq
          (UInt256.div
            (UInt256.mul
              (solcSlotWord (forkAfterDstArt τ I) I aSlot)
              (solcSlotWord (forkAfterDstArt τ I) I bSlot))
            (solcSlotWord (forkAfterDstArt τ I) I bSlot))
          (solcSlotWord (forkAfterDstArt τ I) I aSlot) ≠ ⟨0⟩) := by
  have ha := forkAfterDstArt_slot_eq_of_accountMapEquiv (I := I) hAccounts aSlot
  have hb := forkAfterDstArt_slot_eq_of_accountMapEquiv (I := I) hAccounts bSlot
  simp [ha, hb]

theorem forkAfterDstArt_unsafeGuard_iff_of_accountMapEquiv
    {σ τ : AccountMap} {I : ExecutionEnv}
    (hAccounts : accountMapEquiv σ τ) (tab aSlot bSlot : UInt256) :
    (UInt256.gt tab
        (UInt256.mul
          (solcSlotWord (forkAfterDstArt σ I) I aSlot)
          (solcSlotWord (forkAfterDstArt σ I) I bSlot)) = ⟨0⟩) ↔
      (UInt256.gt tab
        (UInt256.mul
          (solcSlotWord (forkAfterDstArt τ I) I aSlot)
          (solcSlotWord (forkAfterDstArt τ I) I bSlot)) = ⟨0⟩) := by
  have ha := forkAfterDstArt_slot_eq_of_accountMapEquiv (I := I) hAccounts aSlot
  have hb := forkAfterDstArt_slot_eq_of_accountMapEquiv (I := I) hAccounts bSlot
  simp [ha, hb]

theorem forkAfterDstArt_dustGuard_iff_of_accountMapEquiv
    {σ τ : AccountMap} {I : ExecutionEnv}
    (hAccounts : accountMapEquiv σ τ) (tab artSlot dustSlot : UInt256) :
    (UInt256.lor
        (UInt256.eq ⟨0⟩ (solcSlotWord (forkAfterDstArt σ I) I artSlot))
        (UInt256.isZero
          (UInt256.lt tab (solcSlotWord (forkAfterDstArt σ I) I dustSlot))) ≠ ⟨0⟩) ↔
      (UInt256.lor
        (UInt256.eq ⟨0⟩ (solcSlotWord (forkAfterDstArt τ I) I artSlot))
        (UInt256.isZero
          (UInt256.lt tab (solcSlotWord (forkAfterDstArt τ I) I dustSlot))) ≠ ⟨0⟩) := by
  have hart := forkAfterDstArt_slot_eq_of_accountMapEquiv (I := I) hAccounts artSlot
  have hdust := forkAfterDstArt_slot_eq_of_accountMapEquiv (I := I) hAccounts dustSlot
  simp [hart, hdust]

theorem forkSrcInkSubGuardNeg_iff_of_accountMapEquiv {σ τ : AccountMap} {I : ExecutionEnv}
    (hAccounts : accountMapEquiv σ τ) :
    (UInt256.sgt (forkDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.gt (forkSrcInkNew σ I) (solcSlotWord σ I (forkSrcInkSlot I)) = ⟨0⟩) ↔
      (UInt256.sgt (forkDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.gt (forkSrcInkNew τ I) (solcSlotWord τ I (forkSrcInkSlot I)) = ⟨0⟩) := by
  have hOld :
      solcSlotWord σ I (forkSrcInkSlot I) =
        solcSlotWord τ I (forkSrcInkSlot I) :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner (forkSrcInkSlot I) ⟨0⟩
  have hNew := forkSrcInkNew_eq_of_accountMapEquiv (I := I) hAccounts
  constructor <;> intro h <;> simpa [hOld, hNew] using h

theorem forkSrcInkSubGuardPos_iff_of_accountMapEquiv {σ τ : AccountMap} {I : ExecutionEnv}
    (hAccounts : accountMapEquiv σ τ) :
    (UInt256.slt (forkDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.lt (forkSrcInkNew σ I) (solcSlotWord σ I (forkSrcInkSlot I)) = ⟨0⟩) ↔
      (UInt256.slt (forkDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.lt (forkSrcInkNew τ I) (solcSlotWord τ I (forkSrcInkSlot I)) = ⟨0⟩) := by
  have hOld :
      solcSlotWord σ I (forkSrcInkSlot I) =
        solcSlotWord τ I (forkSrcInkSlot I) :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner (forkSrcInkSlot I) ⟨0⟩
  have hNew := forkSrcInkNew_eq_of_accountMapEquiv (I := I) hAccounts
  constructor <;> intro h <;> simpa [hOld, hNew] using h

theorem forkSrcArtSubGuardNeg_iff_of_accountMapEquiv {σ τ : AccountMap} {I : ExecutionEnv}
    (hAccounts : accountMapEquiv σ τ) :
    (UInt256.sgt (forkDartWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.gt (forkSrcArtNew σ I)
          (solcSlotWord (forkAfterSrcInk σ I) I (forkSrcArtSlot I)) = ⟨0⟩) ↔
      (UInt256.sgt (forkDartWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.gt (forkSrcArtNew τ I)
          (solcSlotWord (forkAfterSrcInk τ I) I (forkSrcArtSlot I)) = ⟨0⟩) := by
  have hSrcInk := accountMapEquiv_forkAfterSrcInk (I := I) hAccounts
  have hOld :
      solcSlotWord (forkAfterSrcInk σ I) I (forkSrcArtSlot I) =
        solcSlotWord (forkAfterSrcInk τ I) I (forkSrcArtSlot I) :=
    accountMapEquiv_storage_findD hSrcInk I.codeOwner (forkSrcArtSlot I) ⟨0⟩
  have hNew := forkSrcArtNew_eq_of_accountMapEquiv (I := I) hAccounts
  constructor <;> intro h <;> simpa [hOld, hNew] using h

theorem forkSrcArtSubGuardPos_iff_of_accountMapEquiv {σ τ : AccountMap} {I : ExecutionEnv}
    (hAccounts : accountMapEquiv σ τ) :
    (UInt256.slt (forkDartWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.lt (forkSrcArtNew σ I)
          (solcSlotWord (forkAfterSrcInk σ I) I (forkSrcArtSlot I)) = ⟨0⟩) ↔
      (UInt256.slt (forkDartWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.lt (forkSrcArtNew τ I)
          (solcSlotWord (forkAfterSrcInk τ I) I (forkSrcArtSlot I)) = ⟨0⟩) := by
  have hSrcInk := accountMapEquiv_forkAfterSrcInk (I := I) hAccounts
  have hOld :
      solcSlotWord (forkAfterSrcInk σ I) I (forkSrcArtSlot I) =
        solcSlotWord (forkAfterSrcInk τ I) I (forkSrcArtSlot I) :=
    accountMapEquiv_storage_findD hSrcInk I.codeOwner (forkSrcArtSlot I) ⟨0⟩
  have hNew := forkSrcArtNew_eq_of_accountMapEquiv (I := I) hAccounts
  constructor <;> intro h <;> simpa [hOld, hNew] using h

theorem forkDstInkAddGuardNeg_iff_of_accountMapEquiv {σ τ : AccountMap} {I : ExecutionEnv}
    (hAccounts : accountMapEquiv σ τ) :
    (UInt256.slt (forkDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.gt (forkDstInkNew σ I)
          (solcSlotWord (forkAfterSrcArt σ I) I (forkDstInkSlot I)) = ⟨0⟩) ↔
      (UInt256.slt (forkDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.gt (forkDstInkNew τ I)
          (solcSlotWord (forkAfterSrcArt τ I) I (forkDstInkSlot I)) = ⟨0⟩) := by
  have hSrcArt := accountMapEquiv_forkAfterSrcArt (I := I) hAccounts
  have hOld :
      solcSlotWord (forkAfterSrcArt σ I) I (forkDstInkSlot I) =
        solcSlotWord (forkAfterSrcArt τ I) I (forkDstInkSlot I) :=
    accountMapEquiv_storage_findD hSrcArt I.codeOwner (forkDstInkSlot I) ⟨0⟩
  have hNew := forkDstInkNew_eq_of_accountMapEquiv (I := I) hAccounts
  constructor <;> intro h <;> simpa [hOld, hNew] using h

theorem forkDstInkAddGuardPos_iff_of_accountMapEquiv {σ τ : AccountMap} {I : ExecutionEnv}
    (hAccounts : accountMapEquiv σ τ) :
    (UInt256.sgt (forkDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.lt (forkDstInkNew σ I)
          (solcSlotWord (forkAfterSrcArt σ I) I (forkDstInkSlot I)) = ⟨0⟩) ↔
      (UInt256.sgt (forkDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.lt (forkDstInkNew τ I)
          (solcSlotWord (forkAfterSrcArt τ I) I (forkDstInkSlot I)) = ⟨0⟩) := by
  have hSrcArt := accountMapEquiv_forkAfterSrcArt (I := I) hAccounts
  have hOld :
      solcSlotWord (forkAfterSrcArt σ I) I (forkDstInkSlot I) =
        solcSlotWord (forkAfterSrcArt τ I) I (forkDstInkSlot I) :=
    accountMapEquiv_storage_findD hSrcArt I.codeOwner (forkDstInkSlot I) ⟨0⟩
  have hNew := forkDstInkNew_eq_of_accountMapEquiv (I := I) hAccounts
  constructor <;> intro h <;> simpa [hOld, hNew] using h

theorem forkDstArtAddGuardNeg_iff_of_accountMapEquiv {σ τ : AccountMap} {I : ExecutionEnv}
    (hAccounts : accountMapEquiv σ τ) :
    (UInt256.slt (forkDartWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.gt (forkDstArtNew σ I)
          (solcSlotWord (forkAfterDstInk σ I) I (forkDstArtSlot I)) = ⟨0⟩) ↔
      (UInt256.slt (forkDartWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.gt (forkDstArtNew τ I)
          (solcSlotWord (forkAfterDstInk τ I) I (forkDstArtSlot I)) = ⟨0⟩) := by
  have hDstInk := accountMapEquiv_forkAfterDstInk (I := I) hAccounts
  have hOld :
      solcSlotWord (forkAfterDstInk σ I) I (forkDstArtSlot I) =
        solcSlotWord (forkAfterDstInk τ I) I (forkDstArtSlot I) :=
    accountMapEquiv_storage_findD hDstInk I.codeOwner (forkDstArtSlot I) ⟨0⟩
  have hNew := forkDstArtNew_eq_of_accountMapEquiv (I := I) hAccounts
  constructor <;> intro h <;> simpa [hOld, hNew] using h

theorem forkDstArtAddGuardPos_iff_of_accountMapEquiv {σ τ : AccountMap} {I : ExecutionEnv}
    (hAccounts : accountMapEquiv σ τ) :
    (UInt256.sgt (forkDartWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.lt (forkDstArtNew σ I)
          (solcSlotWord (forkAfterDstInk σ I) I (forkDstArtSlot I)) = ⟨0⟩) ↔
      (UInt256.sgt (forkDartWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.lt (forkDstArtNew τ I)
          (solcSlotWord (forkAfterDstInk τ I) I (forkDstArtSlot I)) = ⟨0⟩) := by
  have hDstInk := accountMapEquiv_forkAfterDstInk (I := I) hAccounts
  have hOld :
      solcSlotWord (forkAfterDstInk σ I) I (forkDstArtSlot I) =
        solcSlotWord (forkAfterDstInk τ I) I (forkDstArtSlot I) :=
    accountMapEquiv_storage_findD hDstInk I.codeOwner (forkDstArtSlot I) ⟨0⟩
  have hNew := forkDstArtNew_eq_of_accountMapEquiv (I := I) hAccounts
  constructor <;> intro h <;> simpa [hOld, hNew] using h

abbrev forkSrcInkEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "urns", steps := [.mindex (forkIlkKey I), .mindex (forkSrcKey I), .field "ink"] }

abbrev forkSrcArtEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "urns", steps := [.mindex (forkIlkKey I), .mindex (forkSrcKey I), .field "art"] }

abbrev forkDstInkEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "urns", steps := [.mindex (forkIlkKey I), .mindex (forkDstKey I), .field "ink"] }

abbrev forkDstArtEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "urns", steps := [.mindex (forkIlkKey I), .mindex (forkDstKey I), .field "art"] }

abbrev forkIlkRateEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "ilks", steps := [.mindex (forkIlkKey I), .field "rate"] }

abbrev forkIlkSpotEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "ilks", steps := [.mindex (forkIlkKey I), .field "spot"] }

abbrev forkIlkDustEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "ilks", steps := [.mindex (forkIlkKey I), .field "dust"] }

abbrev forkSrcWishEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "can", steps := [.mindex (forkSrcKey I), .mindex (forkSourceKey I)] }

abbrev forkDstWishEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "can", steps := [.mindex (forkDstKey I), .mindex (forkSourceKey I)] }

theorem forkStore_get_ilk (I : ExecutionEnv) :
    (forkStore I).get? "ilk" = some (forkIlkValue I) := by
  unfold forkStore
  rw [store_get_ne _ _ (by native_decide)]
  rw [store_get_ne _ _ (by native_decide)]
  rw [store_get_ne _ _ (by native_decide)]
  rw [store_get_ne _ _ (by native_decide)]
  simp

theorem forkStore_get_src (I : ExecutionEnv) :
    (forkStore I).get? "src" = some (forkSrcValue I) := by
  unfold forkStore
  rw [store_get_ne _ _ (by native_decide)]
  rw [store_get_ne _ _ (by native_decide)]
  rw [store_get_ne _ _ (by native_decide)]
  simp

theorem forkStore_get_dst (I : ExecutionEnv) :
    (forkStore I).get? "dst" = some (forkDstValue I) := by
  unfold forkStore
  rw [store_get_ne _ _ (by native_decide)]
  rw [store_get_ne _ _ (by native_decide)]
  simp

theorem forkStore_get_dink (I : ExecutionEnv) :
    (forkStore I).get? "dink" = some (forkDinkValue I) := by
  unfold forkStore
  rw [store_get_ne _ _ (by native_decide)]
  simp

theorem forkStore_get_dart (I : ExecutionEnv) :
    (forkStore I).get? "dart" = some (forkDartValue I) := by
  unfold forkStore
  simp

theorem forkStore_urns (I : ExecutionEnv) :
    (forkStore I).get? "urns" = none := by
  unfold forkStore
  repeat rw [store_get_ne _ _ (by native_decide)]
  simp

theorem forkStore_ilks (I : ExecutionEnv) :
    (forkStore I).get? "ilks" = none := by
  unfold forkStore
  repeat rw [store_get_ne _ _ (by native_decide)]
  simp

theorem forkStore_can (I : ExecutionEnv) :
    (forkStore I).get? "can" = none := by
  unfold forkStore
  repeat rw [store_get_ne _ _ (by native_decide)]
  simp

abbrev forkStoreSrcInkNew (I : ExecutionEnv) (srcInkNew : UInt256) : Store :=
  (forkStore I).insert "srcInkNew" (.int (Int.ofNat srcInkNew.toNat))

abbrev forkStoreSrcArtNew (I : ExecutionEnv) (srcInkNew srcArtNew : UInt256) : Store :=
  (forkStoreSrcInkNew I srcInkNew).insert "srcArtNew"
    (.int (Int.ofNat srcArtNew.toNat))

abbrev forkStoreDstInkNew (I : ExecutionEnv)
    (srcInkNew srcArtNew dstInkNew : UInt256) : Store :=
  (forkStoreSrcArtNew I srcInkNew srcArtNew).insert "dstInkNew"
    (.int (Int.ofNat dstInkNew.toNat))

abbrev forkStoreDstArtNew (I : ExecutionEnv)
    (srcInkNew srcArtNew dstInkNew dstArtNew : UInt256) : Store :=
  (forkStoreDstInkNew I srcInkNew srcArtNew dstInkNew).insert "dstArtNew"
    (.int (Int.ofNat dstArtNew.toNat))

abbrev forkStoreFinalLoads (I : ExecutionEnv)
    (srcInkNew srcArtNew dstInkNew dstArtNew
      srcArtFinal dstArtFinal srcInkFinal dstInkFinal : UInt256) : Store :=
  ((((forkStoreDstArtNew I srcInkNew srcArtNew dstInkNew dstArtNew).insert
      "srcArtFinal" (.int (Int.ofNat srcArtFinal.toNat))).insert
      "dstArtFinal" (.int (Int.ofNat dstArtFinal.toNat))).insert
      "srcInkFinal" (.int (Int.ofNat srcInkFinal.toNat))).insert
      "dstInkFinal" (.int (Int.ofNat dstInkFinal.toNat))

abbrev forkStoreUtabFinal (I : ExecutionEnv)
    (srcInkNew srcArtNew dstInkNew dstArtNew
      srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab : UInt256) : Store :=
  (forkStoreFinalLoads I srcInkNew srcArtNew dstInkNew dstArtNew
    srcArtFinal dstArtFinal srcInkFinal dstInkFinal).insert "utab"
    (.int (Int.ofNat utab.toNat))

abbrev forkStoreVtabFinal (I : ExecutionEnv)
    (srcInkNew srcArtNew dstInkNew dstArtNew
      srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab vtab : UInt256) : Store :=
  (forkStoreUtabFinal I srcInkNew srcArtNew dstInkNew dstArtNew
    srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab).insert "vtab"
    (.int (Int.ofNat vtab.toNat))

abbrev forkStoreSrcInkSpotFinal (I : ExecutionEnv)
    (srcInkNew srcArtNew dstInkNew dstArtNew
      srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab vtab srcInkSpot : UInt256) :
    Store :=
  (forkStoreVtabFinal I srcInkNew srcArtNew dstInkNew dstArtNew
    srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab vtab).insert "srcInkSpot"
    (.int (Int.ofNat srcInkSpot.toNat))

abbrev forkStoreDstInkSpotFinal (I : ExecutionEnv)
    (srcInkNew srcArtNew dstInkNew dstArtNew
      srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab vtab srcInkSpot
      dstInkSpot : UInt256) : Store :=
  (forkStoreSrcInkSpotFinal I srcInkNew srcArtNew dstInkNew dstArtNew
    srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab vtab srcInkSpot).insert
    "dstInkSpot" (.int (Int.ofNat dstInkSpot.toNat))

abbrev forkStoreUtab (I : ExecutionEnv)
    (srcInkNew srcArtNew dstInkNew dstArtNew utab : UInt256) : Store :=
  (forkStoreDstArtNew I srcInkNew srcArtNew dstInkNew dstArtNew).insert "utab"
    (.int (Int.ofNat utab.toNat))

abbrev forkStoreVtab (I : ExecutionEnv)
    (srcInkNew srcArtNew dstInkNew dstArtNew utab vtab : UInt256) : Store :=
  (forkStoreUtab I srcInkNew srcArtNew dstInkNew dstArtNew utab).insert "vtab"
    (.int (Int.ofNat vtab.toNat))

abbrev forkStoreSrcInkSpot (I : ExecutionEnv)
    (srcInkNew srcArtNew dstInkNew dstArtNew utab vtab srcInkSpot : UInt256) : Store :=
  (forkStoreVtab I srcInkNew srcArtNew dstInkNew dstArtNew utab vtab).insert "srcInkSpot"
    (.int (Int.ofNat srcInkSpot.toNat))

abbrev forkStoreDstInkSpot (I : ExecutionEnv)
    (srcInkNew srcArtNew dstInkNew dstArtNew utab vtab srcInkSpot dstInkSpot : UInt256) :
    Store :=
  (forkStoreSrcInkSpot I srcInkNew srcArtNew dstInkNew dstArtNew utab vtab srcInkSpot).insert
    "dstInkSpot" (.int (Int.ofNat dstInkSpot.toNat))

theorem forkStoreSrcInkNew_get_ilk (I : ExecutionEnv) (srcInkNew : UInt256) :
    (forkStoreSrcInkNew I srcInkNew).get? "ilk" = some (forkIlkValue I) := by
  change ((forkStore I).insert "srcInkNew" (.int (Int.ofNat srcInkNew.toNat))).get? "ilk" =
    some (forkIlkValue I)
  rw [store_get_ne _ _ (by native_decide), forkStore_get_ilk]

theorem forkStoreSrcInkNew_get_src (I : ExecutionEnv) (srcInkNew : UInt256) :
    (forkStoreSrcInkNew I srcInkNew).get? "src" = some (forkSrcValue I) := by
  change ((forkStore I).insert "srcInkNew" (.int (Int.ofNat srcInkNew.toNat))).get? "src" =
    some (forkSrcValue I)
  rw [store_get_ne _ _ (by native_decide), forkStore_get_src]

theorem forkStoreSrcInkNew_get_dart (I : ExecutionEnv) (srcInkNew : UInt256) :
    (forkStoreSrcInkNew I srcInkNew).get? "dart" = some (forkDartValue I) := by
  change ((forkStore I).insert "srcInkNew" (.int (Int.ofNat srcInkNew.toNat))).get? "dart" =
    some (forkDartValue I)
  rw [store_get_ne _ _ (by native_decide), forkStore_get_dart]

theorem forkStoreSrcInkNew_get_urns (I : ExecutionEnv) (srcInkNew : UInt256) :
    (forkStoreSrcInkNew I srcInkNew).get? "urns" = none := by
  change ((forkStore I).insert "srcInkNew" (.int (Int.ofNat srcInkNew.toNat))).get? "urns" =
    none
  rw [store_get_ne _ _ (by native_decide), forkStore_urns]

theorem forkStoreSrcArtNew_get_ilk (I : ExecutionEnv) (srcInkNew srcArtNew : UInt256) :
    (forkStoreSrcArtNew I srcInkNew srcArtNew).get? "ilk" = some (forkIlkValue I) := by
  change ((forkStoreSrcInkNew I srcInkNew).insert "srcArtNew"
    (.int (Int.ofNat srcArtNew.toNat))).get? "ilk" = some (forkIlkValue I)
  rw [store_get_ne _ _ (by native_decide), forkStoreSrcInkNew_get_ilk]

theorem forkStoreSrcArtNew_get_dst (I : ExecutionEnv) (srcInkNew srcArtNew : UInt256) :
    (forkStoreSrcArtNew I srcInkNew srcArtNew).get? "dst" = some (forkDstValue I) := by
  change ((forkStoreSrcInkNew I srcInkNew).insert "srcArtNew"
    (.int (Int.ofNat srcArtNew.toNat))).get? "dst" = some (forkDstValue I)
  rw [store_get_ne _ _ (by native_decide)]
  change ((forkStore I).insert "srcInkNew" (.int (Int.ofNat srcInkNew.toNat))).get? "dst" =
    some (forkDstValue I)
  rw [store_get_ne _ _ (by native_decide), forkStore_get_dst]

theorem forkStoreSrcArtNew_get_dink (I : ExecutionEnv) (srcInkNew srcArtNew : UInt256) :
    (forkStoreSrcArtNew I srcInkNew srcArtNew).get? "dink" = some (forkDinkValue I) := by
  change ((forkStoreSrcInkNew I srcInkNew).insert "srcArtNew"
    (.int (Int.ofNat srcArtNew.toNat))).get? "dink" = some (forkDinkValue I)
  rw [store_get_ne _ _ (by native_decide)]
  change ((forkStore I).insert "srcInkNew" (.int (Int.ofNat srcInkNew.toNat))).get? "dink" =
    some (forkDinkValue I)
  rw [store_get_ne _ _ (by native_decide), forkStore_get_dink]

theorem forkStoreSrcArtNew_get_urns (I : ExecutionEnv) (srcInkNew srcArtNew : UInt256) :
    (forkStoreSrcArtNew I srcInkNew srcArtNew).get? "urns" = none := by
  change ((forkStoreSrcInkNew I srcInkNew).insert "srcArtNew"
    (.int (Int.ofNat srcArtNew.toNat))).get? "urns" = none
  rw [store_get_ne _ _ (by native_decide), forkStoreSrcInkNew_get_urns]

theorem forkStoreDstInkNew_get_ilk (I : ExecutionEnv)
    (srcInkNew srcArtNew dstInkNew : UInt256) :
    (forkStoreDstInkNew I srcInkNew srcArtNew dstInkNew).get? "ilk" =
      some (forkIlkValue I) := by
  change ((forkStoreSrcArtNew I srcInkNew srcArtNew).insert "dstInkNew"
    (.int (Int.ofNat dstInkNew.toNat))).get? "ilk" = some (forkIlkValue I)
  rw [store_get_ne _ _ (by native_decide), forkStoreSrcArtNew_get_ilk]

theorem forkStoreDstInkNew_get_dst (I : ExecutionEnv)
    (srcInkNew srcArtNew dstInkNew : UInt256) :
    (forkStoreDstInkNew I srcInkNew srcArtNew dstInkNew).get? "dst" =
      some (forkDstValue I) := by
  change ((forkStoreSrcArtNew I srcInkNew srcArtNew).insert "dstInkNew"
    (.int (Int.ofNat dstInkNew.toNat))).get? "dst" = some (forkDstValue I)
  rw [store_get_ne _ _ (by native_decide), forkStoreSrcArtNew_get_dst]

theorem forkStoreDstInkNew_get_dart (I : ExecutionEnv)
    (srcInkNew srcArtNew dstInkNew : UInt256) :
    (forkStoreDstInkNew I srcInkNew srcArtNew dstInkNew).get? "dart" =
      some (forkDartValue I) := by
  change ((forkStoreSrcArtNew I srcInkNew srcArtNew).insert "dstInkNew"
    (.int (Int.ofNat dstInkNew.toNat))).get? "dart" = some (forkDartValue I)
  rw [store_get_ne _ _ (by native_decide)]
  change ((forkStoreSrcInkNew I srcInkNew).insert "srcArtNew"
    (.int (Int.ofNat srcArtNew.toNat))).get? "dart" = some (forkDartValue I)
  rw [store_get_ne _ _ (by native_decide), forkStoreSrcInkNew_get_dart]

theorem forkStoreDstInkNew_get_urns (I : ExecutionEnv)
    (srcInkNew srcArtNew dstInkNew : UInt256) :
    (forkStoreDstInkNew I srcInkNew srcArtNew dstInkNew).get? "urns" = none := by
  change ((forkStoreSrcArtNew I srcInkNew srcArtNew).insert "dstInkNew"
    (.int (Int.ofNat dstInkNew.toNat))).get? "urns" = none
  rw [store_get_ne _ _ (by native_decide), forkStoreSrcArtNew_get_urns]

theorem forkStoreDstArtNew_get_ilk (I : ExecutionEnv)
    (srcInkNew srcArtNew dstInkNew dstArtNew : UInt256) :
    (forkStoreDstArtNew I srcInkNew srcArtNew dstInkNew dstArtNew).get? "ilk" =
      some (forkIlkValue I) := by
  change ((forkStoreDstInkNew I srcInkNew srcArtNew dstInkNew).insert "dstArtNew"
    (.int (Int.ofNat dstArtNew.toNat))).get? "ilk" = some (forkIlkValue I)
  rw [store_get_ne _ _ (by native_decide), forkStoreDstInkNew_get_ilk]

theorem forkStoreDstArtNew_get_src (I : ExecutionEnv)
    (srcInkNew srcArtNew dstInkNew dstArtNew : UInt256) :
    (forkStoreDstArtNew I srcInkNew srcArtNew dstInkNew dstArtNew).get? "src" =
      some (forkSrcValue I) := by
  change ((forkStoreDstInkNew I srcInkNew srcArtNew dstInkNew).insert "dstArtNew"
    (.int (Int.ofNat dstArtNew.toNat))).get? "src" = some (forkSrcValue I)
  rw [store_get_ne _ _ (by native_decide)]
  change ((forkStoreSrcArtNew I srcInkNew srcArtNew).insert "dstInkNew"
    (.int (Int.ofNat dstInkNew.toNat))).get? "src" = some (forkSrcValue I)
  rw [store_get_ne _ _ (by native_decide)]
  change ((forkStoreSrcInkNew I srcInkNew).insert "srcArtNew"
    (.int (Int.ofNat srcArtNew.toNat))).get? "src" = some (forkSrcValue I)
  rw [store_get_ne _ _ (by native_decide), forkStoreSrcInkNew_get_src]

theorem forkStoreDstArtNew_get_dst (I : ExecutionEnv)
    (srcInkNew srcArtNew dstInkNew dstArtNew : UInt256) :
    (forkStoreDstArtNew I srcInkNew srcArtNew dstInkNew dstArtNew).get? "dst" =
      some (forkDstValue I) := by
  change ((forkStoreDstInkNew I srcInkNew srcArtNew dstInkNew).insert "dstArtNew"
    (.int (Int.ofNat dstArtNew.toNat))).get? "dst" = some (forkDstValue I)
  rw [store_get_ne _ _ (by native_decide), forkStoreDstInkNew_get_dst]

theorem forkStoreDstArtNew_get_urns (I : ExecutionEnv)
    (srcInkNew srcArtNew dstInkNew dstArtNew : UInt256) :
    (forkStoreDstArtNew I srcInkNew srcArtNew dstInkNew dstArtNew).get? "urns" = none := by
  change ((forkStoreDstInkNew I srcInkNew srcArtNew dstInkNew).insert "dstArtNew"
    (.int (Int.ofNat dstArtNew.toNat))).get? "urns" = none
  rw [store_get_ne _ _ (by native_decide), forkStoreDstInkNew_get_urns]

theorem forkStoreDstArtNew_get_ilks (I : ExecutionEnv)
    (srcInkNew srcArtNew dstInkNew dstArtNew : UInt256) :
    (forkStoreDstArtNew I srcInkNew srcArtNew dstInkNew dstArtNew).get? "ilks" = none := by
  change ((forkStoreDstInkNew I srcInkNew srcArtNew dstInkNew).insert "dstArtNew"
    (.int (Int.ofNat dstArtNew.toNat))).get? "ilks" = none
  rw [store_get_ne _ _ (by native_decide)]
  change ((forkStoreSrcArtNew I srcInkNew srcArtNew).insert "dstInkNew"
    (.int (Int.ofNat dstInkNew.toNat))).get? "ilks" = none
  rw [store_get_ne _ _ (by native_decide)]
  change ((forkStoreSrcInkNew I srcInkNew).insert "srcArtNew"
    (.int (Int.ofNat srcArtNew.toNat))).get? "ilks" = none
  rw [store_get_ne _ _ (by native_decide)]
  change ((forkStore I).insert "srcInkNew" (.int (Int.ofNat srcInkNew.toNat))).get? "ilks" =
    none
  rw [store_get_ne _ _ (by native_decide), forkStore_ilks]

theorem forkStoreUtab_get_ilk (I : ExecutionEnv)
    (srcInkNew srcArtNew dstInkNew dstArtNew utab : UInt256) :
    (forkStoreUtab I srcInkNew srcArtNew dstInkNew dstArtNew utab).get? "ilk" =
      some (forkIlkValue I) := by
  change ((forkStoreDstArtNew I srcInkNew srcArtNew dstInkNew dstArtNew).insert "utab"
    (.int (Int.ofNat utab.toNat))).get? "ilk" = some (forkIlkValue I)
  rw [store_get_ne _ _ (by native_decide), forkStoreDstArtNew_get_ilk]

theorem forkStoreUtab_get_src (I : ExecutionEnv)
    (srcInkNew srcArtNew dstInkNew dstArtNew utab : UInt256) :
    (forkStoreUtab I srcInkNew srcArtNew dstInkNew dstArtNew utab).get? "src" =
      some (forkSrcValue I) := by
  change ((forkStoreDstArtNew I srcInkNew srcArtNew dstInkNew dstArtNew).insert "utab"
    (.int (Int.ofNat utab.toNat))).get? "src" = some (forkSrcValue I)
  rw [store_get_ne _ _ (by native_decide), forkStoreDstArtNew_get_src]

theorem forkStoreUtab_get_dst (I : ExecutionEnv)
    (srcInkNew srcArtNew dstInkNew dstArtNew utab : UInt256) :
    (forkStoreUtab I srcInkNew srcArtNew dstInkNew dstArtNew utab).get? "dst" =
      some (forkDstValue I) := by
  change ((forkStoreDstArtNew I srcInkNew srcArtNew dstInkNew dstArtNew).insert "utab"
    (.int (Int.ofNat utab.toNat))).get? "dst" = some (forkDstValue I)
  rw [store_get_ne _ _ (by native_decide), forkStoreDstArtNew_get_dst]

theorem forkStoreUtab_get_urns (I : ExecutionEnv)
    (srcInkNew srcArtNew dstInkNew dstArtNew utab : UInt256) :
    (forkStoreUtab I srcInkNew srcArtNew dstInkNew dstArtNew utab).get? "urns" = none := by
  change ((forkStoreDstArtNew I srcInkNew srcArtNew dstInkNew dstArtNew).insert "utab"
    (.int (Int.ofNat utab.toNat))).get? "urns" = none
  rw [store_get_ne _ _ (by native_decide), forkStoreDstArtNew_get_urns]

theorem forkStoreUtab_get_ilks (I : ExecutionEnv)
    (srcInkNew srcArtNew dstInkNew dstArtNew utab : UInt256) :
    (forkStoreUtab I srcInkNew srcArtNew dstInkNew dstArtNew utab).get? "ilks" = none := by
  change ((forkStoreDstArtNew I srcInkNew srcArtNew dstInkNew dstArtNew).insert "utab"
    (.int (Int.ofNat utab.toNat))).get? "ilks" = none
  rw [store_get_ne _ _ (by native_decide), forkStoreDstArtNew_get_ilks]

theorem forkStoreUtab_get_utab (I : ExecutionEnv)
    (srcInkNew srcArtNew dstInkNew dstArtNew utab : UInt256) :
    (forkStoreUtab I srcInkNew srcArtNew dstInkNew dstArtNew utab).get? "utab" =
      some (.int (Int.ofNat utab.toNat)) := by
  simp [forkStoreUtab]

theorem forkStoreVtab_get_ilk (I : ExecutionEnv)
    (srcInkNew srcArtNew dstInkNew dstArtNew utab vtab : UInt256) :
    (forkStoreVtab I srcInkNew srcArtNew dstInkNew dstArtNew utab vtab).get? "ilk" =
      some (forkIlkValue I) := by
  change ((forkStoreUtab I srcInkNew srcArtNew dstInkNew dstArtNew utab).insert "vtab"
    (.int (Int.ofNat vtab.toNat))).get? "ilk" = some (forkIlkValue I)
  rw [store_get_ne _ _ (by native_decide), forkStoreUtab_get_ilk]

theorem forkStoreVtab_get_src (I : ExecutionEnv)
    (srcInkNew srcArtNew dstInkNew dstArtNew utab vtab : UInt256) :
    (forkStoreVtab I srcInkNew srcArtNew dstInkNew dstArtNew utab vtab).get? "src" =
      some (forkSrcValue I) := by
  change ((forkStoreUtab I srcInkNew srcArtNew dstInkNew dstArtNew utab).insert "vtab"
    (.int (Int.ofNat vtab.toNat))).get? "src" = some (forkSrcValue I)
  rw [store_get_ne _ _ (by native_decide), forkStoreUtab_get_src]

theorem forkStoreVtab_get_dst (I : ExecutionEnv)
    (srcInkNew srcArtNew dstInkNew dstArtNew utab vtab : UInt256) :
    (forkStoreVtab I srcInkNew srcArtNew dstInkNew dstArtNew utab vtab).get? "dst" =
      some (forkDstValue I) := by
  change ((forkStoreUtab I srcInkNew srcArtNew dstInkNew dstArtNew utab).insert "vtab"
    (.int (Int.ofNat vtab.toNat))).get? "dst" = some (forkDstValue I)
  rw [store_get_ne _ _ (by native_decide), forkStoreUtab_get_dst]

theorem forkStoreVtab_get_urns (I : ExecutionEnv)
    (srcInkNew srcArtNew dstInkNew dstArtNew utab vtab : UInt256) :
    (forkStoreVtab I srcInkNew srcArtNew dstInkNew dstArtNew utab vtab).get? "urns" =
      none := by
  change ((forkStoreUtab I srcInkNew srcArtNew dstInkNew dstArtNew utab).insert "vtab"
    (.int (Int.ofNat vtab.toNat))).get? "urns" = none
  rw [store_get_ne _ _ (by native_decide), forkStoreUtab_get_urns]

theorem forkStoreVtab_get_ilks (I : ExecutionEnv)
    (srcInkNew srcArtNew dstInkNew dstArtNew utab vtab : UInt256) :
    (forkStoreVtab I srcInkNew srcArtNew dstInkNew dstArtNew utab vtab).get? "ilks" =
      none := by
  change ((forkStoreUtab I srcInkNew srcArtNew dstInkNew dstArtNew utab).insert "vtab"
    (.int (Int.ofNat vtab.toNat))).get? "ilks" = none
  rw [store_get_ne _ _ (by native_decide), forkStoreUtab_get_ilks]

theorem forkStoreVtab_get_vtab (I : ExecutionEnv)
    (srcInkNew srcArtNew dstInkNew dstArtNew utab vtab : UInt256) :
    (forkStoreVtab I srcInkNew srcArtNew dstInkNew dstArtNew utab vtab).get? "vtab" =
      some (.int (Int.ofNat vtab.toNat)) := by
  simp [forkStoreVtab]

theorem forkStoreVtab_get_utab (I : ExecutionEnv)
    (srcInkNew srcArtNew dstInkNew dstArtNew utab vtab : UInt256) :
    (forkStoreVtab I srcInkNew srcArtNew dstInkNew dstArtNew utab vtab).get? "utab" =
      some (.int (Int.ofNat utab.toNat)) := by
  change ((forkStoreUtab I srcInkNew srcArtNew dstInkNew dstArtNew utab).insert "vtab"
    (.int (Int.ofNat vtab.toNat))).get? "utab" = some (.int (Int.ofNat utab.toNat))
  rw [store_get_ne _ _ (by native_decide), forkStoreUtab_get_utab]

theorem forkStoreSrcInkSpot_get_ilk (I : ExecutionEnv)
    (srcInkNew srcArtNew dstInkNew dstArtNew utab vtab srcInkSpot : UInt256) :
    (forkStoreSrcInkSpot I srcInkNew srcArtNew dstInkNew dstArtNew utab vtab srcInkSpot).get?
      "ilk" = some (forkIlkValue I) := by
  change ((forkStoreVtab I srcInkNew srcArtNew dstInkNew dstArtNew utab vtab).insert
    "srcInkSpot" (.int (Int.ofNat srcInkSpot.toNat))).get? "ilk" = some (forkIlkValue I)
  rw [store_get_ne _ _ (by native_decide), forkStoreVtab_get_ilk]

theorem forkStoreSrcInkSpot_get_src (I : ExecutionEnv)
    (srcInkNew srcArtNew dstInkNew dstArtNew utab vtab srcInkSpot : UInt256) :
    (forkStoreSrcInkSpot I srcInkNew srcArtNew dstInkNew dstArtNew utab vtab srcInkSpot).get?
      "src" = some (forkSrcValue I) := by
  change ((forkStoreVtab I srcInkNew srcArtNew dstInkNew dstArtNew utab vtab).insert
    "srcInkSpot" (.int (Int.ofNat srcInkSpot.toNat))).get? "src" = some (forkSrcValue I)
  rw [store_get_ne _ _ (by native_decide), forkStoreVtab_get_src]

theorem forkStoreSrcInkSpot_get_dst (I : ExecutionEnv)
    (srcInkNew srcArtNew dstInkNew dstArtNew utab vtab srcInkSpot : UInt256) :
    (forkStoreSrcInkSpot I srcInkNew srcArtNew dstInkNew dstArtNew utab vtab srcInkSpot).get?
      "dst" = some (forkDstValue I) := by
  change ((forkStoreVtab I srcInkNew srcArtNew dstInkNew dstArtNew utab vtab).insert
    "srcInkSpot" (.int (Int.ofNat srcInkSpot.toNat))).get? "dst" = some (forkDstValue I)
  rw [store_get_ne _ _ (by native_decide), forkStoreVtab_get_dst]

theorem forkStoreSrcInkSpot_get_urns (I : ExecutionEnv)
    (srcInkNew srcArtNew dstInkNew dstArtNew utab vtab srcInkSpot : UInt256) :
    (forkStoreSrcInkSpot I srcInkNew srcArtNew dstInkNew dstArtNew utab vtab srcInkSpot).get?
      "urns" = none := by
  change ((forkStoreVtab I srcInkNew srcArtNew dstInkNew dstArtNew utab vtab).insert
    "srcInkSpot" (.int (Int.ofNat srcInkSpot.toNat))).get? "urns" = none
  rw [store_get_ne _ _ (by native_decide), forkStoreVtab_get_urns]

theorem forkStoreSrcInkSpot_get_ilks (I : ExecutionEnv)
    (srcInkNew srcArtNew dstInkNew dstArtNew utab vtab srcInkSpot : UInt256) :
    (forkStoreSrcInkSpot I srcInkNew srcArtNew dstInkNew dstArtNew utab vtab srcInkSpot).get?
      "ilks" = none := by
  change ((forkStoreVtab I srcInkNew srcArtNew dstInkNew dstArtNew utab vtab).insert
    "srcInkSpot" (.int (Int.ofNat srcInkSpot.toNat))).get? "ilks" = none
  rw [store_get_ne _ _ (by native_decide), forkStoreVtab_get_ilks]

theorem forkStoreSrcInkSpot_get_can (I : ExecutionEnv)
    (srcInkNew srcArtNew dstInkNew dstArtNew utab vtab srcInkSpot : UInt256) :
    (forkStoreSrcInkSpot I srcInkNew srcArtNew dstInkNew dstArtNew utab vtab srcInkSpot).get?
      "can" = none := by
  unfold forkStoreSrcInkSpot forkStoreVtab forkStoreUtab forkStoreDstArtNew
    forkStoreDstInkNew forkStoreSrcArtNew forkStoreSrcInkNew forkStore
  repeat rw [store_get_ne _ _ (by native_decide)]
  simp

theorem forkStoreSrcInkSpot_get_srcInkSpot (I : ExecutionEnv)
    (srcInkNew srcArtNew dstInkNew dstArtNew utab vtab srcInkSpot : UInt256) :
    (forkStoreSrcInkSpot I srcInkNew srcArtNew dstInkNew dstArtNew utab vtab srcInkSpot).get?
      "srcInkSpot" = some (.int (Int.ofNat srcInkSpot.toNat)) := by
  simp [forkStoreSrcInkSpot]

theorem forkStoreSrcInkSpot_get_utab (I : ExecutionEnv)
    (srcInkNew srcArtNew dstInkNew dstArtNew utab vtab srcInkSpot : UInt256) :
    (forkStoreSrcInkSpot I srcInkNew srcArtNew dstInkNew dstArtNew utab vtab srcInkSpot).get?
      "utab" = some (.int (Int.ofNat utab.toNat)) := by
  change ((forkStoreVtab I srcInkNew srcArtNew dstInkNew dstArtNew utab vtab).insert
    "srcInkSpot" (.int (Int.ofNat srcInkSpot.toNat))).get? "utab" =
    some (.int (Int.ofNat utab.toNat))
  rw [store_get_ne _ _ (by native_decide), forkStoreVtab_get_utab]

theorem forkStoreSrcInkSpot_get_vtab (I : ExecutionEnv)
    (srcInkNew srcArtNew dstInkNew dstArtNew utab vtab srcInkSpot : UInt256) :
    (forkStoreSrcInkSpot I srcInkNew srcArtNew dstInkNew dstArtNew utab vtab srcInkSpot).get?
      "vtab" = some (.int (Int.ofNat vtab.toNat)) := by
  change ((forkStoreVtab I srcInkNew srcArtNew dstInkNew dstArtNew utab vtab).insert
    "srcInkSpot" (.int (Int.ofNat srcInkSpot.toNat))).get? "vtab" =
    some (.int (Int.ofNat vtab.toNat))
  rw [store_get_ne _ _ (by native_decide), forkStoreVtab_get_vtab]

theorem forkStoreDstInkSpot_get_dstInkSpot (I : ExecutionEnv)
    (srcInkNew srcArtNew dstInkNew dstArtNew utab vtab srcInkSpot dstInkSpot : UInt256) :
    (forkStoreDstInkSpot I srcInkNew srcArtNew dstInkNew dstArtNew utab vtab srcInkSpot
      dstInkSpot).get? "dstInkSpot" = some (.int (Int.ofNat dstInkSpot.toNat)) := by
  simp [forkStoreDstInkSpot]

theorem forkStoreDstInkSpot_get_ilk (I : ExecutionEnv)
    (srcInkNew srcArtNew dstInkNew dstArtNew utab vtab srcInkSpot dstInkSpot : UInt256) :
    (forkStoreDstInkSpot I srcInkNew srcArtNew dstInkNew dstArtNew utab vtab srcInkSpot
      dstInkSpot).get? "ilk" = some (forkIlkValue I) := by
  change ((forkStoreSrcInkSpot I srcInkNew srcArtNew dstInkNew dstArtNew utab vtab
    srcInkSpot).insert "dstInkSpot" (.int (Int.ofNat dstInkSpot.toNat))).get? "ilk" =
    some (forkIlkValue I)
  rw [store_get_ne _ _ (by native_decide), forkStoreSrcInkSpot_get_ilk]

theorem forkStoreDstInkSpot_get_src (I : ExecutionEnv)
    (srcInkNew srcArtNew dstInkNew dstArtNew utab vtab srcInkSpot dstInkSpot : UInt256) :
    (forkStoreDstInkSpot I srcInkNew srcArtNew dstInkNew dstArtNew utab vtab srcInkSpot
      dstInkSpot).get? "src" = some (forkSrcValue I) := by
  change ((forkStoreSrcInkSpot I srcInkNew srcArtNew dstInkNew dstArtNew utab vtab
    srcInkSpot).insert "dstInkSpot" (.int (Int.ofNat dstInkSpot.toNat))).get? "src" =
    some (forkSrcValue I)
  rw [store_get_ne _ _ (by native_decide), forkStoreSrcInkSpot_get_src]

theorem forkStoreDstInkSpot_get_dst (I : ExecutionEnv)
    (srcInkNew srcArtNew dstInkNew dstArtNew utab vtab srcInkSpot dstInkSpot : UInt256) :
    (forkStoreDstInkSpot I srcInkNew srcArtNew dstInkNew dstArtNew utab vtab srcInkSpot
      dstInkSpot).get? "dst" = some (forkDstValue I) := by
  change ((forkStoreSrcInkSpot I srcInkNew srcArtNew dstInkNew dstArtNew utab vtab
    srcInkSpot).insert "dstInkSpot" (.int (Int.ofNat dstInkSpot.toNat))).get? "dst" =
    some (forkDstValue I)
  rw [store_get_ne _ _ (by native_decide), forkStoreSrcInkSpot_get_dst]

theorem forkStoreDstInkSpot_get_urns (I : ExecutionEnv)
    (srcInkNew srcArtNew dstInkNew dstArtNew utab vtab srcInkSpot dstInkSpot : UInt256) :
    (forkStoreDstInkSpot I srcInkNew srcArtNew dstInkNew dstArtNew utab vtab srcInkSpot
      dstInkSpot).get? "urns" = none := by
  change ((forkStoreSrcInkSpot I srcInkNew srcArtNew dstInkNew dstArtNew utab vtab
    srcInkSpot).insert "dstInkSpot" (.int (Int.ofNat dstInkSpot.toNat))).get? "urns" =
    none
  rw [store_get_ne _ _ (by native_decide), forkStoreSrcInkSpot_get_urns]

theorem forkStoreDstInkSpot_get_ilks (I : ExecutionEnv)
    (srcInkNew srcArtNew dstInkNew dstArtNew utab vtab srcInkSpot dstInkSpot : UInt256) :
    (forkStoreDstInkSpot I srcInkNew srcArtNew dstInkNew dstArtNew utab vtab srcInkSpot
      dstInkSpot).get? "ilks" = none := by
  change ((forkStoreSrcInkSpot I srcInkNew srcArtNew dstInkNew dstArtNew utab vtab
    srcInkSpot).insert "dstInkSpot" (.int (Int.ofNat dstInkSpot.toNat))).get? "ilks" =
    none
  rw [store_get_ne _ _ (by native_decide), forkStoreSrcInkSpot_get_ilks]

theorem forkStoreDstInkSpot_get_can (I : ExecutionEnv)
    (srcInkNew srcArtNew dstInkNew dstArtNew utab vtab srcInkSpot dstInkSpot : UInt256) :
    (forkStoreDstInkSpot I srcInkNew srcArtNew dstInkNew dstArtNew utab vtab srcInkSpot
      dstInkSpot).get? "can" = none := by
  change ((forkStoreSrcInkSpot I srcInkNew srcArtNew dstInkNew dstArtNew utab vtab
    srcInkSpot).insert "dstInkSpot" (.int (Int.ofNat dstInkSpot.toNat))).get? "can" =
    none
  rw [store_get_ne _ _ (by native_decide), forkStoreSrcInkSpot_get_can]

theorem forkStoreDstInkSpot_get_utab (I : ExecutionEnv)
    (srcInkNew srcArtNew dstInkNew dstArtNew utab vtab srcInkSpot dstInkSpot : UInt256) :
    (forkStoreDstInkSpot I srcInkNew srcArtNew dstInkNew dstArtNew utab vtab srcInkSpot
      dstInkSpot).get? "utab" = some (.int (Int.ofNat utab.toNat)) := by
  change ((forkStoreSrcInkSpot I srcInkNew srcArtNew dstInkNew dstArtNew utab vtab
    srcInkSpot).insert "dstInkSpot" (.int (Int.ofNat dstInkSpot.toNat))).get? "utab" =
    some (.int (Int.ofNat utab.toNat))
  rw [store_get_ne _ _ (by native_decide), forkStoreSrcInkSpot_get_utab]

theorem forkStoreDstInkSpot_get_vtab (I : ExecutionEnv)
    (srcInkNew srcArtNew dstInkNew dstArtNew utab vtab srcInkSpot dstInkSpot : UInt256) :
    (forkStoreDstInkSpot I srcInkNew srcArtNew dstInkNew dstArtNew utab vtab srcInkSpot
      dstInkSpot).get? "vtab" = some (.int (Int.ofNat vtab.toNat)) := by
  change ((forkStoreSrcInkSpot I srcInkNew srcArtNew dstInkNew dstArtNew utab vtab
    srcInkSpot).insert "dstInkSpot" (.int (Int.ofNat dstInkSpot.toNat))).get? "vtab" =
    some (.int (Int.ofNat vtab.toNat))
  rw [store_get_ne _ _ (by native_decide), forkStoreSrcInkSpot_get_vtab]

theorem forkStoreDstInkSpot_get_srcInkSpot (I : ExecutionEnv)
    (srcInkNew srcArtNew dstInkNew dstArtNew utab vtab srcInkSpot dstInkSpot : UInt256) :
    (forkStoreDstInkSpot I srcInkNew srcArtNew dstInkNew dstArtNew utab vtab srcInkSpot
      dstInkSpot).get? "srcInkSpot" = some (.int (Int.ofNat srcInkSpot.toNat)) := by
  change ((forkStoreSrcInkSpot I srcInkNew srcArtNew dstInkNew dstArtNew utab vtab
    srcInkSpot).insert "dstInkSpot" (.int (Int.ofNat dstInkSpot.toNat))).get? "srcInkSpot" =
    some (.int (Int.ofNat srcInkSpot.toNat))
  rw [store_get_ne _ _ (by native_decide), forkStoreSrcInkSpot_get_srcInkSpot]

theorem forkStoreFinalLoads_get_srcArtFinal (I : ExecutionEnv)
    (srcInkNew srcArtNew dstInkNew dstArtNew
      srcArtFinal dstArtFinal srcInkFinal dstInkFinal : UInt256) :
    (forkStoreFinalLoads I srcInkNew srcArtNew dstInkNew dstArtNew
      srcArtFinal dstArtFinal srcInkFinal dstInkFinal).get? "srcArtFinal" =
      some (.int (Int.ofNat srcArtFinal.toNat)) := by
  unfold forkStoreFinalLoads
  repeat rw [store_get_ne _ _ (by native_decide)]
  simp

theorem forkStoreFinalLoads_get_dstArtFinal (I : ExecutionEnv)
    (srcInkNew srcArtNew dstInkNew dstArtNew
      srcArtFinal dstArtFinal srcInkFinal dstInkFinal : UInt256) :
    (forkStoreFinalLoads I srcInkNew srcArtNew dstInkNew dstArtNew
      srcArtFinal dstArtFinal srcInkFinal dstInkFinal).get? "dstArtFinal" =
      some (.int (Int.ofNat dstArtFinal.toNat)) := by
  unfold forkStoreFinalLoads
  repeat rw [store_get_ne _ _ (by native_decide)]
  simp

theorem forkStoreFinalLoads_get_srcInkFinal (I : ExecutionEnv)
    (srcInkNew srcArtNew dstInkNew dstArtNew
      srcArtFinal dstArtFinal srcInkFinal dstInkFinal : UInt256) :
    (forkStoreFinalLoads I srcInkNew srcArtNew dstInkNew dstArtNew
      srcArtFinal dstArtFinal srcInkFinal dstInkFinal).get? "srcInkFinal" =
      some (.int (Int.ofNat srcInkFinal.toNat)) := by
  unfold forkStoreFinalLoads
  repeat rw [store_get_ne _ _ (by native_decide)]
  simp

theorem forkStoreFinalLoads_get_dstInkFinal (I : ExecutionEnv)
    (srcInkNew srcArtNew dstInkNew dstArtNew
      srcArtFinal dstArtFinal srcInkFinal dstInkFinal : UInt256) :
    (forkStoreFinalLoads I srcInkNew srcArtNew dstInkNew dstArtNew
      srcArtFinal dstArtFinal srcInkFinal dstInkFinal).get? "dstInkFinal" =
      some (.int (Int.ofNat dstInkFinal.toNat)) := by
  simp [forkStoreFinalLoads]

theorem forkStoreFinalLoads_get_src (I : ExecutionEnv)
    (srcInkNew srcArtNew dstInkNew dstArtNew
      srcArtFinal dstArtFinal srcInkFinal dstInkFinal : UInt256) :
    (forkStoreFinalLoads I srcInkNew srcArtNew dstInkNew dstArtNew
      srcArtFinal dstArtFinal srcInkFinal dstInkFinal).get? "src" =
      some (forkSrcValue I) := by
  change (((((forkStoreDstArtNew I srcInkNew srcArtNew dstInkNew dstArtNew).insert
      "srcArtFinal" (.int (Int.ofNat srcArtFinal.toNat))).insert
      "dstArtFinal" (.int (Int.ofNat dstArtFinal.toNat))).insert
      "srcInkFinal" (.int (Int.ofNat srcInkFinal.toNat))).insert
      "dstInkFinal" (.int (Int.ofNat dstInkFinal.toNat))).get? "src" =
      some (forkSrcValue I)
  rw [store_get_ne _ _ (by native_decide), store_get_ne _ _ (by native_decide),
    store_get_ne _ _ (by native_decide), store_get_ne _ _ (by native_decide),
    forkStoreDstArtNew_get_src]

theorem forkStoreFinalLoads_get_dst (I : ExecutionEnv)
    (srcInkNew srcArtNew dstInkNew dstArtNew
      srcArtFinal dstArtFinal srcInkFinal dstInkFinal : UInt256) :
    (forkStoreFinalLoads I srcInkNew srcArtNew dstInkNew dstArtNew
      srcArtFinal dstArtFinal srcInkFinal dstInkFinal).get? "dst" =
      some (forkDstValue I) := by
  change (((((forkStoreDstArtNew I srcInkNew srcArtNew dstInkNew dstArtNew).insert
      "srcArtFinal" (.int (Int.ofNat srcArtFinal.toNat))).insert
      "dstArtFinal" (.int (Int.ofNat dstArtFinal.toNat))).insert
      "srcInkFinal" (.int (Int.ofNat srcInkFinal.toNat))).insert
      "dstInkFinal" (.int (Int.ofNat dstInkFinal.toNat))).get? "dst" =
      some (forkDstValue I)
  rw [store_get_ne _ _ (by native_decide), store_get_ne _ _ (by native_decide),
    store_get_ne _ _ (by native_decide), store_get_ne _ _ (by native_decide),
    forkStoreDstArtNew_get_dst]

theorem forkStoreFinalLoads_get_can (I : ExecutionEnv)
    (srcInkNew srcArtNew dstInkNew dstArtNew
      srcArtFinal dstArtFinal srcInkFinal dstInkFinal : UInt256) :
    (forkStoreFinalLoads I srcInkNew srcArtNew dstInkNew dstArtNew
      srcArtFinal dstArtFinal srcInkFinal dstInkFinal).get? "can" = none := by
  unfold forkStoreFinalLoads forkStoreDstArtNew forkStoreDstInkNew forkStoreSrcArtNew
    forkStoreSrcInkNew forkStore
  repeat rw [store_get_ne _ _ (by native_decide)]
  simp

theorem forkStoreFinalLoads_get_ilk (I : ExecutionEnv)
    (srcInkNew srcArtNew dstInkNew dstArtNew
      srcArtFinal dstArtFinal srcInkFinal dstInkFinal : UInt256) :
    (forkStoreFinalLoads I srcInkNew srcArtNew dstInkNew dstArtNew
      srcArtFinal dstArtFinal srcInkFinal dstInkFinal).get? "ilk" =
      some (forkIlkValue I) := by
  change (((((forkStoreDstArtNew I srcInkNew srcArtNew dstInkNew dstArtNew).insert
      "srcArtFinal" (.int (Int.ofNat srcArtFinal.toNat))).insert
      "dstArtFinal" (.int (Int.ofNat dstArtFinal.toNat))).insert
      "srcInkFinal" (.int (Int.ofNat srcInkFinal.toNat))).insert
      "dstInkFinal" (.int (Int.ofNat dstInkFinal.toNat))).get? "ilk" =
      some (forkIlkValue I)
  rw [store_get_ne _ _ (by native_decide), store_get_ne _ _ (by native_decide),
    store_get_ne _ _ (by native_decide), store_get_ne _ _ (by native_decide),
    forkStoreDstArtNew_get_ilk]

theorem forkStoreFinalLoads_get_ilks (I : ExecutionEnv)
    (srcInkNew srcArtNew dstInkNew dstArtNew
      srcArtFinal dstArtFinal srcInkFinal dstInkFinal : UInt256) :
    (forkStoreFinalLoads I srcInkNew srcArtNew dstInkNew dstArtNew
      srcArtFinal dstArtFinal srcInkFinal dstInkFinal).get? "ilks" = none := by
  change (((((forkStoreDstArtNew I srcInkNew srcArtNew dstInkNew dstArtNew).insert
      "srcArtFinal" (.int (Int.ofNat srcArtFinal.toNat))).insert
      "dstArtFinal" (.int (Int.ofNat dstArtFinal.toNat))).insert
      "srcInkFinal" (.int (Int.ofNat srcInkFinal.toNat))).insert
      "dstInkFinal" (.int (Int.ofNat dstInkFinal.toNat))).get? "ilks" = none
  rw [store_get_ne _ _ (by native_decide), store_get_ne _ _ (by native_decide),
    store_get_ne _ _ (by native_decide), store_get_ne _ _ (by native_decide),
    forkStoreDstArtNew_get_ilks]

theorem forkStoreUtabFinal_get_dstArtFinal (I : ExecutionEnv)
    (srcInkNew srcArtNew dstInkNew dstArtNew
      srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab : UInt256) :
    (forkStoreUtabFinal I srcInkNew srcArtNew dstInkNew dstArtNew
      srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab).get? "dstArtFinal" =
      some (.int (Int.ofNat dstArtFinal.toNat)) := by
  change ((forkStoreFinalLoads I srcInkNew srcArtNew dstInkNew dstArtNew
    srcArtFinal dstArtFinal srcInkFinal dstInkFinal).insert "utab"
    (.int (Int.ofNat utab.toNat))).get? "dstArtFinal" =
    some (.int (Int.ofNat dstArtFinal.toNat))
  rw [store_get_ne _ _ (by native_decide), forkStoreFinalLoads_get_dstArtFinal]

theorem forkStoreUtabFinal_get_ilk (I : ExecutionEnv)
    (srcInkNew srcArtNew dstInkNew dstArtNew
      srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab : UInt256) :
    (forkStoreUtabFinal I srcInkNew srcArtNew dstInkNew dstArtNew
      srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab).get? "ilk" =
      some (forkIlkValue I) := by
  change ((forkStoreFinalLoads I srcInkNew srcArtNew dstInkNew dstArtNew
    srcArtFinal dstArtFinal srcInkFinal dstInkFinal).insert "utab"
    (.int (Int.ofNat utab.toNat))).get? "ilk" = some (forkIlkValue I)
  rw [store_get_ne _ _ (by native_decide), forkStoreFinalLoads_get_ilk]

theorem forkStoreUtabFinal_get_ilks (I : ExecutionEnv)
    (srcInkNew srcArtNew dstInkNew dstArtNew
      srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab : UInt256) :
    (forkStoreUtabFinal I srcInkNew srcArtNew dstInkNew dstArtNew
      srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab).get? "ilks" = none := by
  change ((forkStoreFinalLoads I srcInkNew srcArtNew dstInkNew dstArtNew
    srcArtFinal dstArtFinal srcInkFinal dstInkFinal).insert "utab"
    (.int (Int.ofNat utab.toNat))).get? "ilks" = none
  rw [store_get_ne _ _ (by native_decide), forkStoreFinalLoads_get_ilks]

theorem forkStoreVtabFinal_get_srcInkFinal (I : ExecutionEnv)
    (srcInkNew srcArtNew dstInkNew dstArtNew
      srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab vtab : UInt256) :
    (forkStoreVtabFinal I srcInkNew srcArtNew dstInkNew dstArtNew
      srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab vtab).get? "srcInkFinal" =
      some (.int (Int.ofNat srcInkFinal.toNat)) := by
  change ((forkStoreUtabFinal I srcInkNew srcArtNew dstInkNew dstArtNew
    srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab).insert "vtab"
    (.int (Int.ofNat vtab.toNat))).get? "srcInkFinal" =
    some (.int (Int.ofNat srcInkFinal.toNat))
  rw [store_get_ne _ _ (by native_decide)]
  change (forkStoreUtabFinal I srcInkNew srcArtNew dstInkNew dstArtNew
    srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab).get? "srcInkFinal" =
    some (.int (Int.ofNat srcInkFinal.toNat))
  change ((forkStoreFinalLoads I srcInkNew srcArtNew dstInkNew dstArtNew
    srcArtFinal dstArtFinal srcInkFinal dstInkFinal).insert "utab"
    (.int (Int.ofNat utab.toNat))).get? "srcInkFinal" =
    some (.int (Int.ofNat srcInkFinal.toNat))
  rw [store_get_ne _ _ (by native_decide), forkStoreFinalLoads_get_srcInkFinal]

theorem forkStoreVtabFinal_get_ilk (I : ExecutionEnv)
    (srcInkNew srcArtNew dstInkNew dstArtNew
      srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab vtab : UInt256) :
    (forkStoreVtabFinal I srcInkNew srcArtNew dstInkNew dstArtNew
      srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab vtab).get? "ilk" =
      some (forkIlkValue I) := by
  change ((forkStoreUtabFinal I srcInkNew srcArtNew dstInkNew dstArtNew
    srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab).insert "vtab"
    (.int (Int.ofNat vtab.toNat))).get? "ilk" = some (forkIlkValue I)
  rw [store_get_ne _ _ (by native_decide), forkStoreUtabFinal_get_ilk]

theorem forkStoreVtabFinal_get_ilks (I : ExecutionEnv)
    (srcInkNew srcArtNew dstInkNew dstArtNew
      srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab vtab : UInt256) :
    (forkStoreVtabFinal I srcInkNew srcArtNew dstInkNew dstArtNew
      srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab vtab).get? "ilks" = none := by
  change ((forkStoreUtabFinal I srcInkNew srcArtNew dstInkNew dstArtNew
    srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab).insert "vtab"
    (.int (Int.ofNat vtab.toNat))).get? "ilks" = none
  rw [store_get_ne _ _ (by native_decide), forkStoreUtabFinal_get_ilks]

theorem forkStoreSrcInkSpotFinal_get_dstInkFinal (I : ExecutionEnv)
    (srcInkNew srcArtNew dstInkNew dstArtNew
      srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab vtab srcInkSpot : UInt256) :
    (forkStoreSrcInkSpotFinal I srcInkNew srcArtNew dstInkNew dstArtNew
      srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab vtab srcInkSpot).get? "dstInkFinal" =
      some (.int (Int.ofNat dstInkFinal.toNat)) := by
  change ((forkStoreVtabFinal I srcInkNew srcArtNew dstInkNew dstArtNew
    srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab vtab).insert "srcInkSpot"
    (.int (Int.ofNat srcInkSpot.toNat))).get? "dstInkFinal" =
    some (.int (Int.ofNat dstInkFinal.toNat))
  rw [store_get_ne _ _ (by native_decide)]
  change (forkStoreVtabFinal I srcInkNew srcArtNew dstInkNew dstArtNew
    srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab vtab).get? "dstInkFinal" =
    some (.int (Int.ofNat dstInkFinal.toNat))
  change ((forkStoreUtabFinal I srcInkNew srcArtNew dstInkNew dstArtNew
    srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab).insert "vtab"
    (.int (Int.ofNat vtab.toNat))).get? "dstInkFinal" =
    some (.int (Int.ofNat dstInkFinal.toNat))
  rw [store_get_ne _ _ (by native_decide)]
  change (forkStoreUtabFinal I srcInkNew srcArtNew dstInkNew dstArtNew
    srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab).get? "dstInkFinal" =
    some (.int (Int.ofNat dstInkFinal.toNat))
  change ((forkStoreFinalLoads I srcInkNew srcArtNew dstInkNew dstArtNew
    srcArtFinal dstArtFinal srcInkFinal dstInkFinal).insert "utab"
    (.int (Int.ofNat utab.toNat))).get? "dstInkFinal" =
    some (.int (Int.ofNat dstInkFinal.toNat))
  rw [store_get_ne _ _ (by native_decide), forkStoreFinalLoads_get_dstInkFinal]

theorem forkStoreSrcInkSpotFinal_get_ilk (I : ExecutionEnv)
    (srcInkNew srcArtNew dstInkNew dstArtNew
      srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab vtab srcInkSpot : UInt256) :
    (forkStoreSrcInkSpotFinal I srcInkNew srcArtNew dstInkNew dstArtNew
      srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab vtab srcInkSpot).get? "ilk" =
      some (forkIlkValue I) := by
  change ((forkStoreVtabFinal I srcInkNew srcArtNew dstInkNew dstArtNew
    srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab vtab).insert "srcInkSpot"
    (.int (Int.ofNat srcInkSpot.toNat))).get? "ilk" = some (forkIlkValue I)
  rw [store_get_ne _ _ (by native_decide), forkStoreVtabFinal_get_ilk]

theorem forkStoreSrcInkSpotFinal_get_ilks (I : ExecutionEnv)
    (srcInkNew srcArtNew dstInkNew dstArtNew
      srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab vtab srcInkSpot : UInt256) :
    (forkStoreSrcInkSpotFinal I srcInkNew srcArtNew dstInkNew dstArtNew
      srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab vtab srcInkSpot).get? "ilks" =
      none := by
  change ((forkStoreVtabFinal I srcInkNew srcArtNew dstInkNew dstArtNew
    srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab vtab).insert "srcInkSpot"
    (.int (Int.ofNat srcInkSpot.toNat))).get? "ilks" = none
  rw [store_get_ne _ _ (by native_decide), forkStoreVtabFinal_get_ilks]

theorem forkStoreUtabFinal_get_utab (I : ExecutionEnv)
    (srcInkNew srcArtNew dstInkNew dstArtNew
      srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab : UInt256) :
    (forkStoreUtabFinal I srcInkNew srcArtNew dstInkNew dstArtNew
      srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab).get? "utab" =
      some (.int (Int.ofNat utab.toNat)) := by
  simp [forkStoreUtabFinal]

theorem forkStoreVtabFinal_get_vtab (I : ExecutionEnv)
    (srcInkNew srcArtNew dstInkNew dstArtNew
      srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab vtab : UInt256) :
    (forkStoreVtabFinal I srcInkNew srcArtNew dstInkNew dstArtNew
      srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab vtab).get? "vtab" =
      some (.int (Int.ofNat vtab.toNat)) := by
  simp [forkStoreVtabFinal]

theorem forkStoreVtabFinal_get_utab (I : ExecutionEnv)
    (srcInkNew srcArtNew dstInkNew dstArtNew
      srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab vtab : UInt256) :
    (forkStoreVtabFinal I srcInkNew srcArtNew dstInkNew dstArtNew
      srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab vtab).get? "utab" =
      some (.int (Int.ofNat utab.toNat)) := by
  change ((forkStoreUtabFinal I srcInkNew srcArtNew dstInkNew dstArtNew
    srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab).insert "vtab"
    (.int (Int.ofNat vtab.toNat))).get? "utab" =
    some (.int (Int.ofNat utab.toNat))
  rw [store_get_ne _ _ (by native_decide), forkStoreUtabFinal_get_utab]

theorem forkStoreSrcInkSpotFinal_get_srcInkSpot (I : ExecutionEnv)
    (srcInkNew srcArtNew dstInkNew dstArtNew
      srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab vtab srcInkSpot : UInt256) :
    (forkStoreSrcInkSpotFinal I srcInkNew srcArtNew dstInkNew dstArtNew
      srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab vtab srcInkSpot).get?
        "srcInkSpot" =
      some (.int (Int.ofNat srcInkSpot.toNat)) := by
  simp [forkStoreSrcInkSpotFinal]

theorem forkStoreSrcInkSpotFinal_get_utab (I : ExecutionEnv)
    (srcInkNew srcArtNew dstInkNew dstArtNew
      srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab vtab srcInkSpot : UInt256) :
    (forkStoreSrcInkSpotFinal I srcInkNew srcArtNew dstInkNew dstArtNew
      srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab vtab srcInkSpot).get? "utab" =
      some (.int (Int.ofNat utab.toNat)) := by
  change ((forkStoreVtabFinal I srcInkNew srcArtNew dstInkNew dstArtNew
    srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab vtab).insert "srcInkSpot"
    (.int (Int.ofNat srcInkSpot.toNat))).get? "utab" =
    some (.int (Int.ofNat utab.toNat))
  rw [store_get_ne _ _ (by native_decide), forkStoreVtabFinal_get_utab]

theorem forkStoreDstInkSpotFinal_get_dstInkSpot (I : ExecutionEnv)
    (srcInkNew srcArtNew dstInkNew dstArtNew
      srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab vtab srcInkSpot
      dstInkSpot : UInt256) :
    (forkStoreDstInkSpotFinal I srcInkNew srcArtNew dstInkNew dstArtNew
      srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab vtab srcInkSpot
      dstInkSpot).get? "dstInkSpot" = some (.int (Int.ofNat dstInkSpot.toNat)) := by
  simp [forkStoreDstInkSpotFinal]

theorem forkStoreDstInkSpotFinal_get_srcInkSpot (I : ExecutionEnv)
    (srcInkNew srcArtNew dstInkNew dstArtNew
      srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab vtab srcInkSpot
      dstInkSpot : UInt256) :
    (forkStoreDstInkSpotFinal I srcInkNew srcArtNew dstInkNew dstArtNew
      srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab vtab srcInkSpot
      dstInkSpot).get? "srcInkSpot" = some (.int (Int.ofNat srcInkSpot.toNat)) := by
  change ((forkStoreSrcInkSpotFinal I srcInkNew srcArtNew dstInkNew dstArtNew
    srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab vtab srcInkSpot).insert
    "dstInkSpot" (.int (Int.ofNat dstInkSpot.toNat))).get? "srcInkSpot" =
    some (.int (Int.ofNat srcInkSpot.toNat))
  rw [store_get_ne _ _ (by native_decide), forkStoreSrcInkSpotFinal_get_srcInkSpot]

theorem forkStoreDstInkSpotFinal_get_utab (I : ExecutionEnv)
    (srcInkNew srcArtNew dstInkNew dstArtNew
      srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab vtab srcInkSpot
      dstInkSpot : UInt256) :
    (forkStoreDstInkSpotFinal I srcInkNew srcArtNew dstInkNew dstArtNew
      srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab vtab srcInkSpot
      dstInkSpot).get? "utab" = some (.int (Int.ofNat utab.toNat)) := by
  change ((forkStoreSrcInkSpotFinal I srcInkNew srcArtNew dstInkNew dstArtNew
    srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab vtab srcInkSpot).insert
    "dstInkSpot" (.int (Int.ofNat dstInkSpot.toNat))).get? "utab" =
    some (.int (Int.ofNat utab.toNat))
  rw [store_get_ne _ _ (by native_decide), forkStoreSrcInkSpotFinal_get_utab]

theorem forkStoreDstInkSpotFinal_get_vtab (I : ExecutionEnv)
    (srcInkNew srcArtNew dstInkNew dstArtNew
      srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab vtab srcInkSpot
      dstInkSpot : UInt256) :
    (forkStoreDstInkSpotFinal I srcInkNew srcArtNew dstInkNew dstArtNew
      srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab vtab srcInkSpot
      dstInkSpot).get? "vtab" = some (.int (Int.ofNat vtab.toNat)) := by
  change ((forkStoreSrcInkSpotFinal I srcInkNew srcArtNew dstInkNew dstArtNew
    srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab vtab srcInkSpot).insert
    "dstInkSpot" (.int (Int.ofNat dstInkSpot.toNat))).get? "vtab" =
    some (.int (Int.ofNat vtab.toNat))
  rw [store_get_ne _ _ (by native_decide)]
  change (forkStoreSrcInkSpotFinal I srcInkNew srcArtNew dstInkNew dstArtNew
    srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab vtab srcInkSpot).get? "vtab" =
    some (.int (Int.ofNat vtab.toNat))
  change ((forkStoreVtabFinal I srcInkNew srcArtNew dstInkNew dstArtNew
    srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab vtab).insert "srcInkSpot"
    (.int (Int.ofNat srcInkSpot.toNat))).get? "vtab" =
    some (.int (Int.ofNat vtab.toNat))
  rw [store_get_ne _ _ (by native_decide), forkStoreVtabFinal_get_vtab]

theorem forkStoreDstInkSpotFinal_get_ilk (I : ExecutionEnv)
    (srcInkNew srcArtNew dstInkNew dstArtNew
      srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab vtab srcInkSpot
      dstInkSpot : UInt256) :
    (forkStoreDstInkSpotFinal I srcInkNew srcArtNew dstInkNew dstArtNew
      srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab vtab srcInkSpot
      dstInkSpot).get? "ilk" = some (forkIlkValue I) := by
  change ((forkStoreSrcInkSpotFinal I srcInkNew srcArtNew dstInkNew dstArtNew
    srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab vtab srcInkSpot).insert
    "dstInkSpot" (.int (Int.ofNat dstInkSpot.toNat))).get? "ilk" =
    some (forkIlkValue I)
  rw [store_get_ne _ _ (by native_decide), forkStoreSrcInkSpotFinal_get_ilk]

theorem forkStoreDstInkSpotFinal_get_ilks (I : ExecutionEnv)
    (srcInkNew srcArtNew dstInkNew dstArtNew
      srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab vtab srcInkSpot
      dstInkSpot : UInt256) :
    (forkStoreDstInkSpotFinal I srcInkNew srcArtNew dstInkNew dstArtNew
      srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab vtab srcInkSpot
      dstInkSpot).get? "ilks" = none := by
  change ((forkStoreSrcInkSpotFinal I srcInkNew srcArtNew dstInkNew dstArtNew
    srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab vtab srcInkSpot).insert
    "dstInkSpot" (.int (Int.ofNat dstInkSpot.toNat))).get? "ilks" = none
  rw [store_get_ne _ _ (by native_decide), forkStoreSrcInkSpotFinal_get_ilks]

theorem forkStoreDstInkSpotFinal_get_srcArtFinal (I : ExecutionEnv)
    (srcInkNew srcArtNew dstInkNew dstArtNew
      srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab vtab srcInkSpot
      dstInkSpot : UInt256) :
    (forkStoreDstInkSpotFinal I srcInkNew srcArtNew dstInkNew dstArtNew
      srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab vtab srcInkSpot
      dstInkSpot).get? "srcArtFinal" = some (.int (Int.ofNat srcArtFinal.toNat)) := by
  change ((forkStoreSrcInkSpotFinal I srcInkNew srcArtNew dstInkNew dstArtNew
    srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab vtab srcInkSpot).insert
    "dstInkSpot" (.int (Int.ofNat dstInkSpot.toNat))).get? "srcArtFinal" =
    some (.int (Int.ofNat srcArtFinal.toNat))
  rw [store_get_ne _ _ (by native_decide)]
  change (forkStoreSrcInkSpotFinal I srcInkNew srcArtNew dstInkNew dstArtNew
    srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab vtab srcInkSpot).get?
      "srcArtFinal" = some (.int (Int.ofNat srcArtFinal.toNat))
  change ((forkStoreVtabFinal I srcInkNew srcArtNew dstInkNew dstArtNew
    srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab vtab).insert "srcInkSpot"
    (.int (Int.ofNat srcInkSpot.toNat))).get? "srcArtFinal" =
    some (.int (Int.ofNat srcArtFinal.toNat))
  rw [store_get_ne _ _ (by native_decide)]
  change (forkStoreVtabFinal I srcInkNew srcArtNew dstInkNew dstArtNew
    srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab vtab).get? "srcArtFinal" =
    some (.int (Int.ofNat srcArtFinal.toNat))
  change ((forkStoreUtabFinal I srcInkNew srcArtNew dstInkNew dstArtNew
    srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab).insert "vtab"
    (.int (Int.ofNat vtab.toNat))).get? "srcArtFinal" =
    some (.int (Int.ofNat srcArtFinal.toNat))
  rw [store_get_ne _ _ (by native_decide)]
  change (forkStoreUtabFinal I srcInkNew srcArtNew dstInkNew dstArtNew
    srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab).get? "srcArtFinal" =
    some (.int (Int.ofNat srcArtFinal.toNat))
  change ((forkStoreFinalLoads I srcInkNew srcArtNew dstInkNew dstArtNew
    srcArtFinal dstArtFinal srcInkFinal dstInkFinal).insert "utab"
    (.int (Int.ofNat utab.toNat))).get? "srcArtFinal" =
    some (.int (Int.ofNat srcArtFinal.toNat))
  rw [store_get_ne _ _ (by native_decide), forkStoreFinalLoads_get_srcArtFinal]

theorem forkStoreDstInkSpotFinal_get_dstArtFinal (I : ExecutionEnv)
    (srcInkNew srcArtNew dstInkNew dstArtNew
      srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab vtab srcInkSpot
      dstInkSpot : UInt256) :
    (forkStoreDstInkSpotFinal I srcInkNew srcArtNew dstInkNew dstArtNew
      srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab vtab srcInkSpot
      dstInkSpot).get? "dstArtFinal" = some (.int (Int.ofNat dstArtFinal.toNat)) := by
  change ((forkStoreSrcInkSpotFinal I srcInkNew srcArtNew dstInkNew dstArtNew
    srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab vtab srcInkSpot).insert
    "dstInkSpot" (.int (Int.ofNat dstInkSpot.toNat))).get? "dstArtFinal" =
    some (.int (Int.ofNat dstArtFinal.toNat))
  rw [store_get_ne _ _ (by native_decide)]
  change (forkStoreSrcInkSpotFinal I srcInkNew srcArtNew dstInkNew dstArtNew
    srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab vtab srcInkSpot).get?
      "dstArtFinal" = some (.int (Int.ofNat dstArtFinal.toNat))
  change ((forkStoreVtabFinal I srcInkNew srcArtNew dstInkNew dstArtNew
    srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab vtab).insert "srcInkSpot"
    (.int (Int.ofNat srcInkSpot.toNat))).get? "dstArtFinal" =
    some (.int (Int.ofNat dstArtFinal.toNat))
  rw [store_get_ne _ _ (by native_decide)]
  change (forkStoreVtabFinal I srcInkNew srcArtNew dstInkNew dstArtNew
    srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab vtab).get? "dstArtFinal" =
    some (.int (Int.ofNat dstArtFinal.toNat))
  change ((forkStoreUtabFinal I srcInkNew srcArtNew dstInkNew dstArtNew
    srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab).insert "vtab"
    (.int (Int.ofNat vtab.toNat))).get? "dstArtFinal" =
    some (.int (Int.ofNat dstArtFinal.toNat))
  rw [store_get_ne _ _ (by native_decide)]
  change (forkStoreUtabFinal I srcInkNew srcArtNew dstInkNew dstArtNew
    srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab).get? "dstArtFinal" =
    some (.int (Int.ofNat dstArtFinal.toNat))
  change ((forkStoreFinalLoads I srcInkNew srcArtNew dstInkNew dstArtNew
    srcArtFinal dstArtFinal srcInkFinal dstInkFinal).insert "utab"
    (.int (Int.ofNat utab.toNat))).get? "dstArtFinal" =
    some (.int (Int.ofNat dstArtFinal.toNat))
  rw [store_get_ne _ _ (by native_decide), forkStoreFinalLoads_get_dstArtFinal]

theorem forkStoreDstInkSpotFinal_get_src (I : ExecutionEnv)
    (srcInkNew srcArtNew dstInkNew dstArtNew
      srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab vtab srcInkSpot
      dstInkSpot : UInt256) :
    (forkStoreDstInkSpotFinal I srcInkNew srcArtNew dstInkNew dstArtNew
      srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab vtab srcInkSpot
      dstInkSpot).get? "src" = some (forkSrcValue I) := by
  change ((forkStoreSrcInkSpotFinal I srcInkNew srcArtNew dstInkNew dstArtNew
    srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab vtab srcInkSpot).insert
    "dstInkSpot" (.int (Int.ofNat dstInkSpot.toNat))).get? "src" =
    some (forkSrcValue I)
  rw [store_get_ne _ _ (by native_decide)]
  change ((forkStoreVtabFinal I srcInkNew srcArtNew dstInkNew dstArtNew
    srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab vtab).insert "srcInkSpot"
    (.int (Int.ofNat srcInkSpot.toNat))).get? "src" = some (forkSrcValue I)
  rw [store_get_ne _ _ (by native_decide)]
  change ((forkStoreUtabFinal I srcInkNew srcArtNew dstInkNew dstArtNew
    srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab).insert "vtab"
    (.int (Int.ofNat vtab.toNat))).get? "src" = some (forkSrcValue I)
  rw [store_get_ne _ _ (by native_decide)]
  change ((forkStoreFinalLoads I srcInkNew srcArtNew dstInkNew dstArtNew
    srcArtFinal dstArtFinal srcInkFinal dstInkFinal).insert "utab"
    (.int (Int.ofNat utab.toNat))).get? "src" = some (forkSrcValue I)
  rw [store_get_ne _ _ (by native_decide), forkStoreFinalLoads_get_src]

theorem forkStoreDstInkSpotFinal_get_dst (I : ExecutionEnv)
    (srcInkNew srcArtNew dstInkNew dstArtNew
      srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab vtab srcInkSpot
      dstInkSpot : UInt256) :
    (forkStoreDstInkSpotFinal I srcInkNew srcArtNew dstInkNew dstArtNew
      srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab vtab srcInkSpot
      dstInkSpot).get? "dst" = some (forkDstValue I) := by
  change ((forkStoreSrcInkSpotFinal I srcInkNew srcArtNew dstInkNew dstArtNew
    srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab vtab srcInkSpot).insert
    "dstInkSpot" (.int (Int.ofNat dstInkSpot.toNat))).get? "dst" =
    some (forkDstValue I)
  rw [store_get_ne _ _ (by native_decide)]
  change ((forkStoreVtabFinal I srcInkNew srcArtNew dstInkNew dstArtNew
    srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab vtab).insert "srcInkSpot"
    (.int (Int.ofNat srcInkSpot.toNat))).get? "dst" = some (forkDstValue I)
  rw [store_get_ne _ _ (by native_decide)]
  change ((forkStoreUtabFinal I srcInkNew srcArtNew dstInkNew dstArtNew
    srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab).insert "vtab"
    (.int (Int.ofNat vtab.toNat))).get? "dst" = some (forkDstValue I)
  rw [store_get_ne _ _ (by native_decide)]
  change ((forkStoreFinalLoads I srcInkNew srcArtNew dstInkNew dstArtNew
    srcArtFinal dstArtFinal srcInkFinal dstInkFinal).insert "utab"
    (.int (Int.ofNat utab.toNat))).get? "dst" = some (forkDstValue I)
  rw [store_get_ne _ _ (by native_decide), forkStoreFinalLoads_get_dst]

theorem forkStoreDstInkSpotFinal_get_can (I : ExecutionEnv)
    (srcInkNew srcArtNew dstInkNew dstArtNew
      srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab vtab srcInkSpot
      dstInkSpot : UInt256) :
    (forkStoreDstInkSpotFinal I srcInkNew srcArtNew dstInkNew dstArtNew
      srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab vtab srcInkSpot
      dstInkSpot).get? "can" = none := by
  change ((forkStoreSrcInkSpotFinal I srcInkNew srcArtNew dstInkNew dstArtNew
    srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab vtab srcInkSpot).insert
    "dstInkSpot" (.int (Int.ofNat dstInkSpot.toNat))).get? "can" = none
  rw [store_get_ne _ _ (by native_decide)]
  change ((forkStoreVtabFinal I srcInkNew srcArtNew dstInkNew dstArtNew
    srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab vtab).insert "srcInkSpot"
    (.int (Int.ofNat srcInkSpot.toNat))).get? "can" = none
  rw [store_get_ne _ _ (by native_decide)]
  change ((forkStoreUtabFinal I srcInkNew srcArtNew dstInkNew dstArtNew
    srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab).insert "vtab"
    (.int (Int.ofNat vtab.toNat))).get? "can" = none
  rw [store_get_ne _ _ (by native_decide)]
  change ((forkStoreFinalLoads I srcInkNew srcArtNew dstInkNew dstArtNew
    srcArtFinal dstArtFinal srcInkFinal dstInkFinal).insert "utab"
    (.int (Int.ofNat utab.toNat))).get? "can" = none
  rw [store_get_ne _ _ (by native_decide), forkStoreFinalLoads_get_can]

theorem forkIlkKeyWord_eq (I : ExecutionEnv) (hsz36 : 36 ≤ I.calldata.size) :
    keyValueToWord (forkIlkKey I) = forkIlkWord I := by
  unfold forkIlkKey forkIlkWord calldataWord
  have hword : ABI.bytesToWord ((I.calldata.toList.drop 4).take 32) =
      uInt256OfByteArray (I.calldata.readBytes 4 32) :=
    decode_word_at_eq I.calldata 4 (by omega) (by norm_num)
  simp [keyValueToWord, bytes32Width, ABI.bytesToWord, fromByteArrayBigEndian,
    byteArray_toList_eq, show 32 ≤ I.calldata.size - 4 by omega] at hword ⊢
  exact hword

theorem forkSrcUrnBase_eq (I : ExecutionEnv) (hsz164 : 164 ≤ I.calldata.size) :
    forkSrcUrnBase I =
      solcMappingSlot (solcMappingSlot ⟨3⟩ (forkIlkWord I)) (forkSrcMaskedWord I) := by
  unfold forkSrcUrnBase urnsBase urnsIlkSlot forkSrcKey forkSrcMaskedWord mapSlot solcMappingSlot
  rw [forkIlkKeyWord_eq I (by omega), keyValueToWord_address_ofNat_mask]

theorem forkDstUrnBase_eq (I : ExecutionEnv) (hsz164 : 164 ≤ I.calldata.size) :
    forkDstUrnBase I =
      solcMappingSlot (solcMappingSlot ⟨3⟩ (forkIlkWord I)) (forkDstMaskedWord I) := by
  unfold forkDstUrnBase urnsBase urnsIlkSlot forkDstKey forkDstMaskedWord mapSlot solcMappingSlot
  rw [forkIlkKeyWord_eq I (by omega), keyValueToWord_address_ofNat_mask]

theorem forkIlkBase_eq (I : ExecutionEnv) (hsz164 : 164 ≤ I.calldata.size) :
    forkIlkBase I = solcMappingSlot ⟨2⟩ (forkIlkWord I) := by
  unfold forkIlkBase ilksBase mapSlot solcMappingSlot
  rw [forkIlkKeyWord_eq I (by omega)]

theorem forkSrcInkSlot_eq (I : ExecutionEnv) (hsz164 : 164 ≤ I.calldata.size) :
    forkSrcInkSlot I =
      solcMappingSlot (solcMappingSlot ⟨3⟩ (forkIlkWord I)) (forkSrcMaskedWord I) := by
  simp [forkSrcInkSlot, forkSrcUrnBase_eq I hsz164]

theorem forkSrcArtSlot_eq (I : ExecutionEnv) (hsz164 : 164 ≤ I.calldata.size) :
    forkSrcArtSlot I =
      solcMappingSlot (solcMappingSlot ⟨3⟩ (forkIlkWord I)) (forkSrcMaskedWord I) + ⟨1⟩ := by
  simp [forkSrcArtSlot, forkSrcUrnBase_eq I hsz164]

theorem forkDstInkSlot_eq (I : ExecutionEnv) (hsz164 : 164 ≤ I.calldata.size) :
    forkDstInkSlot I =
      solcMappingSlot (solcMappingSlot ⟨3⟩ (forkIlkWord I)) (forkDstMaskedWord I) := by
  simp [forkDstInkSlot, forkDstUrnBase_eq I hsz164]

theorem forkDstArtSlot_eq (I : ExecutionEnv) (hsz164 : 164 ≤ I.calldata.size) :
    forkDstArtSlot I =
      solcMappingSlot (solcMappingSlot ⟨3⟩ (forkIlkWord I)) (forkDstMaskedWord I) + ⟨1⟩ := by
  simp [forkDstArtSlot, forkDstUrnBase_eq I hsz164]

theorem forkIlkRateSlot_eq (I : ExecutionEnv) (hsz164 : 164 ≤ I.calldata.size) :
    forkIlkRateSlot I = solcMappingSlot ⟨2⟩ (forkIlkWord I) + ⟨1⟩ := by
  simp [forkIlkRateSlot, forkIlkBase_eq I hsz164]

theorem forkIlkSpotSlot_eq (I : ExecutionEnv) (hsz164 : 164 ≤ I.calldata.size) :
    forkIlkSpotSlot I = solcMappingSlot ⟨2⟩ (forkIlkWord I) + ⟨2⟩ := by
  simp [forkIlkSpotSlot, forkIlkBase_eq I hsz164]

theorem forkIlkDustSlot_eq (I : ExecutionEnv) (hsz164 : 164 ≤ I.calldata.size) :
    forkIlkDustSlot I = solcMappingSlot ⟨2⟩ (forkIlkWord I) + ⟨4⟩ := by
  simp [forkIlkDustSlot, forkIlkBase_eq I hsz164]

theorem forkSrcWishSlot_eq (I : ExecutionEnv) :
    forkSrcWishSlot I =
      solcMappingSlot (solcMappingSlot ⟨1⟩ (forkSrcMaskedWord I)) (hopeSourceWord I) := by
  unfold forkSrcWishSlot canSlot canOwnerSlot forkSrcKey forkSourceKey forkSrcMaskedWord
    hopeSourceWord mapSlot solcMappingSlot
  rw [keyValueToWord_address_ofNat_mask, keyValueToWord_address]

theorem forkDstWishSlot_eq (I : ExecutionEnv) :
    forkDstWishSlot I =
      solcMappingSlot (solcMappingSlot ⟨1⟩ (forkDstMaskedWord I)) (hopeSourceWord I) := by
  unfold forkDstWishSlot canSlot canOwnerSlot forkDstKey forkSourceKey forkDstMaskedWord
    hopeSourceWord mapSlot solcMappingSlot
  rw [keyValueToWord_address_ofNat_mask, keyValueToWord_address]

theorem forkSrcMaskedWord_canonical (I : ExecutionEnv) :
    (forkSrcMaskedWord I).toNat < EVM.addressModulus := by
  unfold forkSrcMaskedWord
  rw [u256_land_comm solcAddrMask (forkSrcWord I)]
  exact solcAddrMask_result_canonical (forkSrcWord I)

theorem forkDstMaskedWord_canonical (I : ExecutionEnv) :
    (forkDstMaskedWord I).toNat < EVM.addressModulus := by
  unfold forkDstMaskedWord
  rw [u256_land_comm solcAddrMask (forkDstWord I)]
  exact solcAddrMask_result_canonical (forkDstWord I)

theorem forkHopeSource_ofNat (I : ExecutionEnv) :
    AccountAddress.ofNat (hopeSourceWord I).toNat = I.source := by
  apply Fin.ext
  rw [AccountAddress.ofNat, Fin.val_ofNat, hopeSourceWord_toNat, Nat.mod_eq_of_lt]
  exact I.source.isLt

private theorem forkIlkBytes_len (I : ExecutionEnv) (hsz164 : 164 ≤ I.calldata.size) :
    ((I.calldata.toList.drop 4).take 32).length = ↑bytes32Width + 1 := by
  have htlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  rw [List.length_take, List.length_drop, htlen]
  simp [bytes32Width]
  omega

theorem evalStorageRef_fork_src_ink (evm : EVM.State) (I : ExecutionEnv)
    (hsz164 : 164 ≤ I.calldata.size) :
    evalStorageRef config { contract := contract, locals := forkStore I } evm
      (urnsF (.var "ilk") (.var "src") "ink") = .ok (forkSrcInkEvaledRef I) := by
  simp [forkSrcInkEvaledRef, forkIlkValue, forkSrcValue, forkIlkKey, forkSrcKey,
    urnsF, evalStorageRef, evalStorageRefSteps, evalStorageRefStep, evalExpr?,
    valueToKey?, EvalResult.ofOption, EvalResult.bind, bind, pure,
    ← Std.HashMap.get?_eq_getElem?, forkStore_get_ilk, forkStore_get_src,
    forkIlkBytes_len I hsz164]

theorem evalStorageRef_fork_src_art (evm : EVM.State) (I : ExecutionEnv)
    (hsz164 : 164 ≤ I.calldata.size) :
    evalStorageRef config { contract := contract, locals := forkStore I } evm
      (urnsF (.var "ilk") (.var "src") "art") = .ok (forkSrcArtEvaledRef I) := by
  simp [forkSrcArtEvaledRef, forkIlkValue, forkSrcValue, forkIlkKey, forkSrcKey,
    urnsF, evalStorageRef, evalStorageRefSteps, evalStorageRefStep, evalExpr?,
    valueToKey?, EvalResult.ofOption, EvalResult.bind, bind, pure,
    ← Std.HashMap.get?_eq_getElem?, forkStore_get_ilk, forkStore_get_src,
    forkIlkBytes_len I hsz164]

theorem evalStorageRef_fork_dst_ink (evm : EVM.State) (I : ExecutionEnv)
    (hsz164 : 164 ≤ I.calldata.size) :
    evalStorageRef config { contract := contract, locals := forkStore I } evm
      (urnsF (.var "ilk") (.var "dst") "ink") = .ok (forkDstInkEvaledRef I) := by
  simp [forkDstInkEvaledRef, forkIlkValue, forkDstValue, forkIlkKey, forkDstKey,
    urnsF, evalStorageRef, evalStorageRefSteps, evalStorageRefStep, evalExpr?,
    valueToKey?, EvalResult.ofOption, EvalResult.bind, bind, pure,
    ← Std.HashMap.get?_eq_getElem?, forkStore_get_ilk, forkStore_get_dst,
    forkIlkBytes_len I hsz164]

theorem evalStorageRef_fork_dst_art (evm : EVM.State) (I : ExecutionEnv)
    (hsz164 : 164 ≤ I.calldata.size) :
    evalStorageRef config { contract := contract, locals := forkStore I } evm
      (urnsF (.var "ilk") (.var "dst") "art") = .ok (forkDstArtEvaledRef I) := by
  simp [forkDstArtEvaledRef, forkIlkValue, forkDstValue, forkIlkKey, forkDstKey,
    urnsF, evalStorageRef, evalStorageRefSteps, evalStorageRefStep, evalExpr?,
    valueToKey?, EvalResult.ofOption, EvalResult.bind, bind, pure,
    ← Std.HashMap.get?_eq_getElem?, forkStore_get_ilk, forkStore_get_dst,
    forkIlkBytes_len I hsz164]

theorem evalStorageRef_fork_ilk_rate (evm : EVM.State) (I : ExecutionEnv)
    (hsz164 : 164 ≤ I.calldata.size) :
    evalStorageRef config { contract := contract, locals := forkStore I } evm
      (ilksF (.var "ilk") "rate") = .ok (forkIlkRateEvaledRef I) := by
  simp [forkIlkRateEvaledRef, forkIlkValue, forkIlkKey, ilksF, evalStorageRef,
    evalStorageRefSteps, evalStorageRefStep, evalExpr?, valueToKey?, EvalResult.ofOption,
    EvalResult.bind, bind, pure, ← Std.HashMap.get?_eq_getElem?, forkStore_get_ilk,
    forkIlkBytes_len I hsz164]

theorem evalStorageRef_fork_ilk_spot (evm : EVM.State) (I : ExecutionEnv)
    (hsz164 : 164 ≤ I.calldata.size) :
    evalStorageRef config { contract := contract, locals := forkStore I } evm
      (ilksF (.var "ilk") "spot") = .ok (forkIlkSpotEvaledRef I) := by
  simp [forkIlkSpotEvaledRef, forkIlkValue, forkIlkKey, ilksF, evalStorageRef,
    evalStorageRefSteps, evalStorageRefStep, evalExpr?, valueToKey?, EvalResult.ofOption,
    EvalResult.bind, bind, pure, ← Std.HashMap.get?_eq_getElem?, forkStore_get_ilk,
    forkIlkBytes_len I hsz164]

theorem evalStorageRef_fork_ilk_dust (evm : EVM.State) (I : ExecutionEnv)
    (hsz164 : 164 ≤ I.calldata.size) :
    evalStorageRef config { contract := contract, locals := forkStore I } evm
      (ilksF (.var "ilk") "dust") = .ok (forkIlkDustEvaledRef I) := by
  simp [forkIlkDustEvaledRef, forkIlkValue, forkIlkKey, ilksF, evalStorageRef,
    evalStorageRefSteps, evalStorageRefStep, evalExpr?, valueToKey?, EvalResult.ofOption,
    EvalResult.bind, bind, pure, ← Std.HashMap.get?_eq_getElem?, forkStore_get_ilk,
    forkIlkBytes_len I hsz164]

theorem forkStorageType_urn_uint256 (I : ExecutionEnv) (er : EvaledStorageRef)
    (her : er = forkSrcInkEvaledRef I ∨ er = forkSrcArtEvaledRef I ∨
      er = forkDstInkEvaledRef I ∨ er = forkDstArtEvaledRef I) :
    storageTypeAt? contract.storage er = some (.elem (.int uint256Int)) := by
  rcases her with rfl | rfl | rfl | rfl <;>
    simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, UrnStructTy, uint256St]

theorem forkStorageType_ilk_uint256 (I : ExecutionEnv) (er : EvaledStorageRef)
    (her : er = forkIlkRateEvaledRef I ∨ er = forkIlkSpotEvaledRef I ∨
      er = forkIlkDustEvaledRef I) :
    storageTypeAt? contract.storage er = some (.elem (.int uint256Int)) := by
  rcases her with rfl | rfl | rfl <;>
    simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, IlkStructTy, uint256St]

theorem forkStorageType_can (I : ExecutionEnv) (er : EvaledStorageRef)
    (her : er = forkSrcWishEvaledRef I ∨ er = forkDstWishEvaledRef I) :
    storageTypeAt? contract.storage er = some (.elem (.int uint256Int)) := by
  rcases her with rfl | rfl <;>
    simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, uint256St]

theorem forkStorageLayout_src_ink (I : ExecutionEnv) :
    config.storage.layout (forkSrcInkEvaledRef I) =
      fun _ => some (wordLoc (forkSrcInkSlot I)) := by
  funext evm
  change storageLayoutRaw (forkSrcInkEvaledRef I) evm = some (wordLoc (forkSrcInkSlot I))
  simp [storageLayoutRaw, forkSrcInkEvaledRef, forkSrcInkSlot, forkSrcUrnBase]

theorem forkStorageLayout_src_art (I : ExecutionEnv) :
    config.storage.layout (forkSrcArtEvaledRef I) =
      fun _ => some (wordLoc (forkSrcArtSlot I)) := by
  funext evm
  change storageLayoutRaw (forkSrcArtEvaledRef I) evm = some (wordLoc (forkSrcArtSlot I))
  simp [storageLayoutRaw, forkSrcArtEvaledRef, forkSrcArtSlot, forkSrcUrnBase]

theorem forkStorageLayout_dst_ink (I : ExecutionEnv) :
    config.storage.layout (forkDstInkEvaledRef I) =
      fun _ => some (wordLoc (forkDstInkSlot I)) := by
  funext evm
  change storageLayoutRaw (forkDstInkEvaledRef I) evm = some (wordLoc (forkDstInkSlot I))
  simp [storageLayoutRaw, forkDstInkEvaledRef, forkDstInkSlot, forkDstUrnBase]

theorem forkStorageLayout_dst_art (I : ExecutionEnv) :
    config.storage.layout (forkDstArtEvaledRef I) =
      fun _ => some (wordLoc (forkDstArtSlot I)) := by
  funext evm
  change storageLayoutRaw (forkDstArtEvaledRef I) evm = some (wordLoc (forkDstArtSlot I))
  simp [storageLayoutRaw, forkDstArtEvaledRef, forkDstArtSlot, forkDstUrnBase]

theorem forkStorageLayout_ilk_rate (I : ExecutionEnv) :
    config.storage.layout (forkIlkRateEvaledRef I) =
      fun _ => some (wordLoc (forkIlkRateSlot I)) := by
  funext evm
  change storageLayoutRaw (forkIlkRateEvaledRef I) evm = some (wordLoc (forkIlkRateSlot I))
  simp [storageLayoutRaw, forkIlkRateEvaledRef, forkIlkRateSlot, forkIlkBase]

theorem forkStorageLayout_ilk_spot (I : ExecutionEnv) :
    config.storage.layout (forkIlkSpotEvaledRef I) =
      fun _ => some (wordLoc (forkIlkSpotSlot I)) := by
  funext evm
  change storageLayoutRaw (forkIlkSpotEvaledRef I) evm = some (wordLoc (forkIlkSpotSlot I))
  simp [storageLayoutRaw, forkIlkSpotEvaledRef, forkIlkSpotSlot, forkIlkBase]

theorem forkStorageLayout_ilk_dust (I : ExecutionEnv) :
    config.storage.layout (forkIlkDustEvaledRef I) =
      fun _ => some (wordLoc (forkIlkDustSlot I)) := by
  funext evm
  change storageLayoutRaw (forkIlkDustEvaledRef I) evm = some (wordLoc (forkIlkDustSlot I))
  simp [storageLayoutRaw, forkIlkDustEvaledRef, forkIlkDustSlot, forkIlkBase]

theorem forkStorageLayout_src_can (I : ExecutionEnv) :
    config.storage.layout (forkSrcWishEvaledRef I) =
      fun _ => some (wordLoc (forkSrcWishSlot I)) := by
  funext evm
  change storageLayoutRaw (forkSrcWishEvaledRef I) evm = some (wordLoc (forkSrcWishSlot I))
  simp [storageLayoutRaw, forkSrcWishEvaledRef, forkSrcWishSlot]

theorem forkStorageLayout_dst_can (I : ExecutionEnv) :
    config.storage.layout (forkDstWishEvaledRef I) =
      fun _ => some (wordLoc (forkDstWishSlot I)) := by
  funext evm
  change storageLayoutRaw (forkDstWishEvaledRef I) evm = some (wordLoc (forkDstWishSlot I))
  simp [storageLayoutRaw, forkDstWishEvaledRef, forkDstWishSlot]

set_option maxHeartbeats 0 in
theorem evalExpr_fork_src_ink {evm : EVM.State} {I : ExecutionEnv}
    (hsz164 : 164 ≤ I.calldata.size) :
    evalExpr? config { contract := contract, locals := forkStore I } evm
      (.storage (urnsF (.var "ilk") (.var "src") "ink")) =
      .ok (.int (Int.ofNat
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (forkSrcInkSlot I)).toNat)) := by
  exact evalExpr_storage_scalar_value
    (hbase := forkStore_urns I)
    (her := evalStorageRef_fork_src_ink evm I hsz164)
    (hty := forkStorageType_urn_uint256 I (forkSrcInkEvaledRef I) (Or.inl rfl))
    (hloc := forkStorageLayout_src_ink I)
    (hload := vatStorageLocLoad_uint256 evm (forkSrcInkSlot I))

set_option maxHeartbeats 0 in
theorem evalExpr_fork_src_art {evm : EVM.State} {I : ExecutionEnv}
    (hsz164 : 164 ≤ I.calldata.size) :
    evalExpr? config { contract := contract, locals := forkStore I } evm
      (.storage (urnsF (.var "ilk") (.var "src") "art")) =
      .ok (.int (Int.ofNat
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (forkSrcArtSlot I)).toNat)) := by
  exact evalExpr_storage_scalar_value
    (hbase := forkStore_urns I)
    (her := evalStorageRef_fork_src_art evm I hsz164)
    (hty := forkStorageType_urn_uint256 I (forkSrcArtEvaledRef I) (Or.inr (Or.inl rfl)))
    (hloc := forkStorageLayout_src_art I)
    (hload := vatStorageLocLoad_uint256 evm (forkSrcArtSlot I))

set_option maxHeartbeats 0 in
theorem evalExpr_fork_dst_ink {evm : EVM.State} {I : ExecutionEnv}
    (hsz164 : 164 ≤ I.calldata.size) :
    evalExpr? config { contract := contract, locals := forkStore I } evm
      (.storage (urnsF (.var "ilk") (.var "dst") "ink")) =
      .ok (.int (Int.ofNat
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (forkDstInkSlot I)).toNat)) := by
  exact evalExpr_storage_scalar_value
    (hbase := forkStore_urns I)
    (her := evalStorageRef_fork_dst_ink evm I hsz164)
    (hty := forkStorageType_urn_uint256 I (forkDstInkEvaledRef I)
      (Or.inr (Or.inr (Or.inl rfl))))
    (hloc := forkStorageLayout_dst_ink I)
    (hload := vatStorageLocLoad_uint256 evm (forkDstInkSlot I))

set_option maxHeartbeats 0 in
theorem evalExpr_fork_dst_art {evm : EVM.State} {I : ExecutionEnv}
    (hsz164 : 164 ≤ I.calldata.size) :
    evalExpr? config { contract := contract, locals := forkStore I } evm
      (.storage (urnsF (.var "ilk") (.var "dst") "art")) =
      .ok (.int (Int.ofNat
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (forkDstArtSlot I)).toNat)) := by
  exact evalExpr_storage_scalar_value
    (hbase := forkStore_urns I)
    (her := evalStorageRef_fork_dst_art evm I hsz164)
    (hty := forkStorageType_urn_uint256 I (forkDstArtEvaledRef I)
      (Or.inr (Or.inr (Or.inr rfl))))
    (hloc := forkStorageLayout_dst_art I)
    (hload := vatStorageLocLoad_uint256 evm (forkDstArtSlot I))

set_option maxHeartbeats 0 in
theorem evalExpr_fork_ilk_rate {evm : EVM.State} {I : ExecutionEnv}
    (hsz164 : 164 ≤ I.calldata.size) :
    evalExpr? config { contract := contract, locals := forkStore I } evm
      (.storage (ilksF (.var "ilk") "rate")) =
      .ok (.int (Int.ofNat
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (forkIlkRateSlot I)).toNat)) := by
  exact evalExpr_storage_scalar_value
    (hbase := forkStore_ilks I)
    (her := evalStorageRef_fork_ilk_rate evm I hsz164)
    (hty := forkStorageType_ilk_uint256 I (forkIlkRateEvaledRef I) (Or.inl rfl))
    (hloc := forkStorageLayout_ilk_rate I)
    (hload := vatStorageLocLoad_uint256 evm (forkIlkRateSlot I))

set_option maxHeartbeats 0 in
theorem evalExpr_fork_ilk_spot {evm : EVM.State} {I : ExecutionEnv}
    (hsz164 : 164 ≤ I.calldata.size) :
    evalExpr? config { contract := contract, locals := forkStore I } evm
      (.storage (ilksF (.var "ilk") "spot")) =
      .ok (.int (Int.ofNat
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (forkIlkSpotSlot I)).toNat)) := by
  exact evalExpr_storage_scalar_value
    (hbase := forkStore_ilks I)
    (her := evalStorageRef_fork_ilk_spot evm I hsz164)
    (hty := forkStorageType_ilk_uint256 I (forkIlkSpotEvaledRef I) (Or.inr (Or.inl rfl)))
    (hloc := forkStorageLayout_ilk_spot I)
    (hload := vatStorageLocLoad_uint256 evm (forkIlkSpotSlot I))

set_option maxHeartbeats 0 in
theorem evalExpr_fork_ilk_dust {evm : EVM.State} {I : ExecutionEnv}
    (hsz164 : 164 ≤ I.calldata.size) :
    evalExpr? config { contract := contract, locals := forkStore I } evm
      (.storage (ilksF (.var "ilk") "dust")) =
      .ok (.int (Int.ofNat
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (forkIlkDustSlot I)).toNat)) := by
  exact evalExpr_storage_scalar_value
    (hbase := forkStore_ilks I)
    (her := evalStorageRef_fork_ilk_dust evm I hsz164)
    (hty := forkStorageType_ilk_uint256 I (forkIlkDustEvaledRef I) (Or.inr (Or.inr rfl)))
    (hloc := forkStorageLayout_ilk_dust I)
    (hload := vatStorageLocLoad_uint256 evm (forkIlkDustSlot I))

set_option linter.unusedSimpArgs false in
theorem evalStorageRef_fork_src_ink_locals (evm : EVM.State) (I : ExecutionEnv)
    (locals : Store) (hsz164 : 164 ≤ I.calldata.size)
    (hilk : locals.get? "ilk" = some (forkIlkValue I))
    (hsrc : locals.get? "src" = some (forkSrcValue I)) :
    evalStorageRef config { contract := contract, locals := locals } evm
      (urnsF (.var "ilk") (.var "src") "ink") = .ok (forkSrcInkEvaledRef I) := by
  simp [forkSrcInkEvaledRef, forkIlkValue, forkSrcValue, forkIlkKey, forkSrcKey,
    urnsF, evalStorageRef, evalStorageRefSteps, evalStorageRefStep, evalExpr?,
    valueToKey?, EvalResult.ofOption, EvalResult.bind, bind, pure,
    ← Std.HashMap.get?_eq_getElem?, hilk, hsrc, forkIlkBytes_len I hsz164]

set_option linter.unusedSimpArgs false in
theorem evalStorageRef_fork_src_art_locals (evm : EVM.State) (I : ExecutionEnv)
    (locals : Store) (hsz164 : 164 ≤ I.calldata.size)
    (hilk : locals.get? "ilk" = some (forkIlkValue I))
    (hsrc : locals.get? "src" = some (forkSrcValue I)) :
    evalStorageRef config { contract := contract, locals := locals } evm
      (urnsF (.var "ilk") (.var "src") "art") = .ok (forkSrcArtEvaledRef I) := by
  simp [forkSrcArtEvaledRef, forkIlkValue, forkSrcValue, forkIlkKey, forkSrcKey,
    urnsF, evalStorageRef, evalStorageRefSteps, evalStorageRefStep, evalExpr?,
    valueToKey?, EvalResult.ofOption, EvalResult.bind, bind, pure,
    ← Std.HashMap.get?_eq_getElem?, hilk, hsrc, forkIlkBytes_len I hsz164]

set_option linter.unusedSimpArgs false in
theorem evalStorageRef_fork_dst_ink_locals (evm : EVM.State) (I : ExecutionEnv)
    (locals : Store) (hsz164 : 164 ≤ I.calldata.size)
    (hilk : locals.get? "ilk" = some (forkIlkValue I))
    (hdst : locals.get? "dst" = some (forkDstValue I)) :
    evalStorageRef config { contract := contract, locals := locals } evm
      (urnsF (.var "ilk") (.var "dst") "ink") = .ok (forkDstInkEvaledRef I) := by
  simp [forkDstInkEvaledRef, forkIlkValue, forkDstValue, forkIlkKey, forkDstKey,
    urnsF, evalStorageRef, evalStorageRefSteps, evalStorageRefStep, evalExpr?,
    valueToKey?, EvalResult.ofOption, EvalResult.bind, bind, pure,
    ← Std.HashMap.get?_eq_getElem?, hilk, hdst, forkIlkBytes_len I hsz164]

set_option linter.unusedSimpArgs false in
theorem evalStorageRef_fork_dst_art_locals (evm : EVM.State) (I : ExecutionEnv)
    (locals : Store) (hsz164 : 164 ≤ I.calldata.size)
    (hilk : locals.get? "ilk" = some (forkIlkValue I))
    (hdst : locals.get? "dst" = some (forkDstValue I)) :
    evalStorageRef config { contract := contract, locals := locals } evm
      (urnsF (.var "ilk") (.var "dst") "art") = .ok (forkDstArtEvaledRef I) := by
  simp [forkDstArtEvaledRef, forkIlkValue, forkDstValue, forkIlkKey, forkDstKey,
    urnsF, evalStorageRef, evalStorageRefSteps, evalStorageRefStep, evalExpr?,
    valueToKey?, EvalResult.ofOption, EvalResult.bind, bind, pure,
    ← Std.HashMap.get?_eq_getElem?, hilk, hdst, forkIlkBytes_len I hsz164]

set_option linter.unusedSimpArgs false in
theorem evalStorageRef_fork_ilk_rate_locals (evm : EVM.State) (I : ExecutionEnv)
    (locals : Store) (hsz164 : 164 ≤ I.calldata.size)
    (hilk : locals.get? "ilk" = some (forkIlkValue I)) :
    evalStorageRef config { contract := contract, locals := locals } evm
      (ilksF (.var "ilk") "rate") = .ok (forkIlkRateEvaledRef I) := by
  simp [forkIlkRateEvaledRef, forkIlkValue, forkIlkKey, ilksF, evalStorageRef,
    evalStorageRefSteps, evalStorageRefStep, evalExpr?, valueToKey?, EvalResult.ofOption,
    EvalResult.bind, bind, pure, ← Std.HashMap.get?_eq_getElem?, hilk,
    forkIlkBytes_len I hsz164]

set_option linter.unusedSimpArgs false in
theorem evalStorageRef_fork_ilk_spot_locals (evm : EVM.State) (I : ExecutionEnv)
    (locals : Store) (hsz164 : 164 ≤ I.calldata.size)
    (hilk : locals.get? "ilk" = some (forkIlkValue I)) :
    evalStorageRef config { contract := contract, locals := locals } evm
      (ilksF (.var "ilk") "spot") = .ok (forkIlkSpotEvaledRef I) := by
  simp [forkIlkSpotEvaledRef, forkIlkValue, forkIlkKey, ilksF, evalStorageRef,
    evalStorageRefSteps, evalStorageRefStep, evalExpr?, valueToKey?, EvalResult.ofOption,
    EvalResult.bind, bind, pure, ← Std.HashMap.get?_eq_getElem?, hilk,
    forkIlkBytes_len I hsz164]

set_option linter.unusedSimpArgs false in
theorem evalStorageRef_fork_ilk_dust_locals (evm : EVM.State) (I : ExecutionEnv)
    (locals : Store) (hsz164 : 164 ≤ I.calldata.size)
    (hilk : locals.get? "ilk" = some (forkIlkValue I)) :
    evalStorageRef config { contract := contract, locals := locals } evm
      (ilksF (.var "ilk") "dust") = .ok (forkIlkDustEvaledRef I) := by
  simp [forkIlkDustEvaledRef, forkIlkValue, forkIlkKey, ilksF, evalStorageRef,
    evalStorageRefSteps, evalStorageRefStep, evalExpr?, valueToKey?, EvalResult.ofOption,
    EvalResult.bind, bind, pure, ← Std.HashMap.get?_eq_getElem?, hilk,
    forkIlkBytes_len I hsz164]

theorem evalStorageRef_fork_src_can_locals (evm : EVM.State) (I : ExecutionEnv)
    (locals : Store)
    (hsource : evm.executionEnv.source = I.source)
    (hsrc : locals.get? "src" = some (forkSrcValue I)) :
    evalStorageRef config { contract := contract, locals := locals } evm
      (canRef (.var "src") sender) = .ok (forkSrcWishEvaledRef I) := by
  simp [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, canRef, sender,
    envValue, forkSrcWishEvaledRef, hsource, forkSrcValue, forkSourceKey, forkSrcKey,
    valueToKey?, EvalResult.bind, EvalResult.ofOption, bind, pure, evalExpr?,
    ← Std.HashMap.get?_eq_getElem?, hsrc]

theorem evalStorageRef_fork_dst_can_locals (evm : EVM.State) (I : ExecutionEnv)
    (locals : Store)
    (hsource : evm.executionEnv.source = I.source)
    (hdst : locals.get? "dst" = some (forkDstValue I)) :
    evalStorageRef config { contract := contract, locals := locals } evm
      (canRef (.var "dst") sender) = .ok (forkDstWishEvaledRef I) := by
  simp [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, canRef, sender,
    envValue, forkDstWishEvaledRef, hsource, forkDstValue, forkSourceKey, forkDstKey,
    valueToKey?, EvalResult.bind, EvalResult.ofOption, bind, pure, evalExpr?,
    ← Std.HashMap.get?_eq_getElem?, hdst]

theorem evalExpr_fork_src_ink_locals {evm : EVM.State} {I : ExecutionEnv}
    (locals : Store) (hsz164 : 164 ≤ I.calldata.size)
    (hilk : locals.get? "ilk" = some (forkIlkValue I))
    (hsrc : locals.get? "src" = some (forkSrcValue I))
    (hbase : locals.get? "urns" = none) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.storage (urnsF (.var "ilk") (.var "src") "ink")) =
      .ok (.int (Int.ofNat
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (forkSrcInkSlot I)).toNat)) := by
  exact evalExpr_storage_scalar_value
    (hbase := hbase)
    (her := evalStorageRef_fork_src_ink_locals evm I locals hsz164 hilk hsrc)
    (hty := forkStorageType_urn_uint256 I (forkSrcInkEvaledRef I) (Or.inl rfl))
    (hloc := forkStorageLayout_src_ink I)
    (hload := vatStorageLocLoad_uint256 evm (forkSrcInkSlot I))

theorem evalExpr_fork_src_art_locals {evm : EVM.State} {I : ExecutionEnv}
    (locals : Store) (hsz164 : 164 ≤ I.calldata.size)
    (hilk : locals.get? "ilk" = some (forkIlkValue I))
    (hsrc : locals.get? "src" = some (forkSrcValue I))
    (hbase : locals.get? "urns" = none) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.storage (urnsF (.var "ilk") (.var "src") "art")) =
      .ok (.int (Int.ofNat
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (forkSrcArtSlot I)).toNat)) := by
  exact evalExpr_storage_scalar_value
    (hbase := hbase)
    (her := evalStorageRef_fork_src_art_locals evm I locals hsz164 hilk hsrc)
    (hty := forkStorageType_urn_uint256 I (forkSrcArtEvaledRef I) (Or.inr (Or.inl rfl)))
    (hloc := forkStorageLayout_src_art I)
    (hload := vatStorageLocLoad_uint256 evm (forkSrcArtSlot I))

theorem evalExpr_fork_dst_ink_locals {evm : EVM.State} {I : ExecutionEnv}
    (locals : Store) (hsz164 : 164 ≤ I.calldata.size)
    (hilk : locals.get? "ilk" = some (forkIlkValue I))
    (hdst : locals.get? "dst" = some (forkDstValue I))
    (hbase : locals.get? "urns" = none) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.storage (urnsF (.var "ilk") (.var "dst") "ink")) =
      .ok (.int (Int.ofNat
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (forkDstInkSlot I)).toNat)) := by
  exact evalExpr_storage_scalar_value
    (hbase := hbase)
    (her := evalStorageRef_fork_dst_ink_locals evm I locals hsz164 hilk hdst)
    (hty := forkStorageType_urn_uint256 I (forkDstInkEvaledRef I)
      (Or.inr (Or.inr (Or.inl rfl))))
    (hloc := forkStorageLayout_dst_ink I)
    (hload := vatStorageLocLoad_uint256 evm (forkDstInkSlot I))

theorem evalExpr_fork_dst_art_locals {evm : EVM.State} {I : ExecutionEnv}
    (locals : Store) (hsz164 : 164 ≤ I.calldata.size)
    (hilk : locals.get? "ilk" = some (forkIlkValue I))
    (hdst : locals.get? "dst" = some (forkDstValue I))
    (hbase : locals.get? "urns" = none) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.storage (urnsF (.var "ilk") (.var "dst") "art")) =
      .ok (.int (Int.ofNat
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (forkDstArtSlot I)).toNat)) := by
  exact evalExpr_storage_scalar_value
    (hbase := hbase)
    (her := evalStorageRef_fork_dst_art_locals evm I locals hsz164 hilk hdst)
    (hty := forkStorageType_urn_uint256 I (forkDstArtEvaledRef I)
      (Or.inr (Or.inr (Or.inr rfl))))
    (hloc := forkStorageLayout_dst_art I)
    (hload := vatStorageLocLoad_uint256 evm (forkDstArtSlot I))

theorem evalExpr_fork_ilk_rate_locals {evm : EVM.State} {I : ExecutionEnv}
    (locals : Store) (hsz164 : 164 ≤ I.calldata.size)
    (hilk : locals.get? "ilk" = some (forkIlkValue I))
    (hbase : locals.get? "ilks" = none) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.storage (ilksF (.var "ilk") "rate")) =
      .ok (.int (Int.ofNat
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (forkIlkRateSlot I)).toNat)) := by
  exact evalExpr_storage_scalar_value
    (hbase := hbase)
    (her := evalStorageRef_fork_ilk_rate_locals evm I locals hsz164 hilk)
    (hty := forkStorageType_ilk_uint256 I (forkIlkRateEvaledRef I) (Or.inl rfl))
    (hloc := forkStorageLayout_ilk_rate I)
    (hload := vatStorageLocLoad_uint256 evm (forkIlkRateSlot I))

theorem evalExpr_fork_ilk_spot_locals {evm : EVM.State} {I : ExecutionEnv}
    (locals : Store) (hsz164 : 164 ≤ I.calldata.size)
    (hilk : locals.get? "ilk" = some (forkIlkValue I))
    (hbase : locals.get? "ilks" = none) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.storage (ilksF (.var "ilk") "spot")) =
      .ok (.int (Int.ofNat
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (forkIlkSpotSlot I)).toNat)) := by
  exact evalExpr_storage_scalar_value
    (hbase := hbase)
    (her := evalStorageRef_fork_ilk_spot_locals evm I locals hsz164 hilk)
    (hty := forkStorageType_ilk_uint256 I (forkIlkSpotEvaledRef I) (Or.inr (Or.inl rfl)))
    (hloc := forkStorageLayout_ilk_spot I)
    (hload := vatStorageLocLoad_uint256 evm (forkIlkSpotSlot I))

theorem evalExpr_fork_ilk_dust_locals {evm : EVM.State} {I : ExecutionEnv}
    (locals : Store) (hsz164 : 164 ≤ I.calldata.size)
    (hilk : locals.get? "ilk" = some (forkIlkValue I))
    (hbase : locals.get? "ilks" = none) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.storage (ilksF (.var "ilk") "dust")) =
      .ok (.int (Int.ofNat
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (forkIlkDustSlot I)).toNat)) := by
  exact evalExpr_storage_scalar_value
    (hbase := hbase)
    (her := evalStorageRef_fork_ilk_dust_locals evm I locals hsz164 hilk)
    (hty := forkStorageType_ilk_uint256 I (forkIlkDustEvaledRef I) (Or.inr (Or.inr rfl)))
    (hloc := forkStorageLayout_ilk_dust I)
    (hload := vatStorageLocLoad_uint256 evm (forkIlkDustSlot I))

theorem assignStorageRef_fork_src_ink (evm : EVM.State) (I : ExecutionEnv)
    (locals : Store) (srcInkNew : UInt256) (hsz164 : 164 ≤ I.calldata.size)
    (hilk : locals.get? "ilk" = some (forkIlkValue I))
    (hsrc : locals.get? "src" = some (forkSrcValue I))
    (hbase : locals.get? "urns" = none) :
    let evm' := Solm.EVM.storageStore evm evm.executionEnv.codeOwner
      (forkSrcInkSlot I) srcInkNew
    assignStorageRef? config { contract := contract, locals := locals } evm .storage
      (urnsF (.var "ilk") (.var "src") "ink") (.int (Int.ofNat srcInkNew.toNat)) =
      .ok ({ contract := contract, locals := locals }, evm') := by
  intro evm'
  exact assignStorageRef_storage_scalar
    (hbase := hbase)
    (her := evalStorageRef_fork_src_ink_locals evm I locals hsz164 hilk hsrc)
    (hty := forkStorageType_urn_uint256 I (forkSrcInkEvaledRef I) (Or.inl rfl))
    (hloc := forkStorageLayout_src_ink I)
    (hstore := by simpa [evm'] using
      vatStorageLocStore_uint256 evm (forkSrcInkSlot I) srcInkNew)

theorem assignStorageRef_fork_src_art (evm : EVM.State) (I : ExecutionEnv)
    (locals : Store) (srcArtNew : UInt256) (hsz164 : 164 ≤ I.calldata.size)
    (hilk : locals.get? "ilk" = some (forkIlkValue I))
    (hsrc : locals.get? "src" = some (forkSrcValue I))
    (hbase : locals.get? "urns" = none) :
    let evm' := Solm.EVM.storageStore evm evm.executionEnv.codeOwner
      (forkSrcArtSlot I) srcArtNew
    assignStorageRef? config { contract := contract, locals := locals } evm .storage
      (urnsF (.var "ilk") (.var "src") "art") (.int (Int.ofNat srcArtNew.toNat)) =
      .ok ({ contract := contract, locals := locals }, evm') := by
  intro evm'
  exact assignStorageRef_storage_scalar
    (hbase := hbase)
    (her := evalStorageRef_fork_src_art_locals evm I locals hsz164 hilk hsrc)
    (hty := forkStorageType_urn_uint256 I (forkSrcArtEvaledRef I) (Or.inr (Or.inl rfl)))
    (hloc := forkStorageLayout_src_art I)
    (hstore := by simpa [evm'] using
      vatStorageLocStore_uint256 evm (forkSrcArtSlot I) srcArtNew)

theorem assignStorageRef_fork_dst_ink (evm : EVM.State) (I : ExecutionEnv)
    (locals : Store) (dstInkNew : UInt256) (hsz164 : 164 ≤ I.calldata.size)
    (hilk : locals.get? "ilk" = some (forkIlkValue I))
    (hdst : locals.get? "dst" = some (forkDstValue I))
    (hbase : locals.get? "urns" = none) :
    let evm' := Solm.EVM.storageStore evm evm.executionEnv.codeOwner
      (forkDstInkSlot I) dstInkNew
    assignStorageRef? config { contract := contract, locals := locals } evm .storage
      (urnsF (.var "ilk") (.var "dst") "ink") (.int (Int.ofNat dstInkNew.toNat)) =
      .ok ({ contract := contract, locals := locals }, evm') := by
  intro evm'
  exact assignStorageRef_storage_scalar
    (hbase := hbase)
    (her := evalStorageRef_fork_dst_ink_locals evm I locals hsz164 hilk hdst)
    (hty := forkStorageType_urn_uint256 I (forkDstInkEvaledRef I)
      (Or.inr (Or.inr (Or.inl rfl))))
    (hloc := forkStorageLayout_dst_ink I)
    (hstore := by simpa [evm'] using
      vatStorageLocStore_uint256 evm (forkDstInkSlot I) dstInkNew)

theorem assignStorageRef_fork_dst_art (evm : EVM.State) (I : ExecutionEnv)
    (locals : Store) (dstArtNew : UInt256) (hsz164 : 164 ≤ I.calldata.size)
    (hilk : locals.get? "ilk" = some (forkIlkValue I))
    (hdst : locals.get? "dst" = some (forkDstValue I))
    (hbase : locals.get? "urns" = none) :
    let evm' := Solm.EVM.storageStore evm evm.executionEnv.codeOwner
      (forkDstArtSlot I) dstArtNew
    assignStorageRef? config { contract := contract, locals := locals } evm .storage
      (urnsF (.var "ilk") (.var "dst") "art") (.int (Int.ofNat dstArtNew.toNat)) =
      .ok ({ contract := contract, locals := locals }, evm') := by
  intro evm'
  exact assignStorageRef_storage_scalar
    (hbase := hbase)
    (her := evalStorageRef_fork_dst_art_locals evm I locals hsz164 hilk hdst)
    (hty := forkStorageType_urn_uint256 I (forkDstArtEvaledRef I)
      (Or.inr (Or.inr (Or.inr rfl))))
    (hloc := forkStorageLayout_dst_art I)
    (hstore := by simpa [evm'] using
      vatStorageLocStore_uint256 evm (forkDstArtSlot I) dstArtNew)

theorem execForkCheckedSubSignedRevertGuardNeg {evm : EVM.State} {locals : Store}
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
        { contract := contract, locals := locals.insert name (.int (Int.ofNat new.toNat)) } evm y =
      .ok (.int subtrahendInt))
    (hxAfter :
      evalExpr? config
        { contract := contract, locals := locals.insert name (.int (Int.ofNat new.toNat)) } evm x =
      .ok (.int (Int.ofNat old.toNat)))
    (hcond : 0 < subtrahendInt ∧ old.toNat < new.toNat) :
    ExecBlock config { contract := contract, locals := locals } evm
      (checkedSubSignedInto name x y)
      .reverted := by
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
        .ok (.bool false) :=
    evalSignedSubGuardNeg_false (by simpa [locals'] using hyAfter)
      hnewEval (by simpa [locals'] using hxAfter) hcond
  change ExecBlock config { contract := contract, locals := locals } evm
    [ .letDecl name (some uint256) (wordWrap256 (.binary .sub x y)),
      .require (eitherExpr (.binary .le y (.intLit 0)) (.binary .le (.var name) x)),
      .require (eitherExpr (.binary .ge y (.intLit 0)) (.binary .ge (.var name) x)) ]
    .reverted
  refine ExecBlock.consNormal (ExecStmt.letDecl hlet) ?_
  exact ExecBlock.consRevert (ExecStmt.requireFalse hguardNegEval)

theorem execForkCheckedSubSignedRevertGuardPos {evm : EVM.State} {locals : Store}
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
        { contract := contract, locals := locals.insert name (.int (Int.ofNat new.toNat)) } evm y =
      .ok (.int subtrahendInt))
    (hxAfter :
      evalExpr? config
        { contract := contract, locals := locals.insert name (.int (Int.ofNat new.toNat)) } evm x =
      .ok (.int (Int.ofNat old.toNat)))
    (hguardNeg :
      evalExpr? config
        { contract := contract, locals := locals.insert name (.int (Int.ofNat new.toNat)) } evm
        (eitherExpr (.binary .le y (.intLit 0)) (.binary .le (.var name) x)) =
      .ok (.bool true))
    (hcond : subtrahendInt < 0 ∧ new.toNat < old.toNat) :
    ExecBlock config { contract := contract, locals := locals } evm
      (checkedSubSignedInto name x y)
      .reverted := by
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
  have hguardPosEval :
      evalExpr? config { contract := contract, locals := locals' } evm
        (eitherExpr (.binary .ge y (.intLit 0)) (.binary .ge (.var name) x)) =
        .ok (.bool false) :=
    evalSignedSubGuardPos_false (by simpa [locals'] using hyAfter)
      hnewEval (by simpa [locals'] using hxAfter) hcond
  change ExecBlock config { contract := contract, locals := locals } evm
    [ .letDecl name (some uint256) (wordWrap256 (.binary .sub x y)),
      .require (eitherExpr (.binary .le y (.intLit 0)) (.binary .le (.var name) x)),
      .require (eitherExpr (.binary .ge y (.intLit 0)) (.binary .ge (.var name) x)) ]
    .reverted
  refine ExecBlock.consNormal (ExecStmt.letDecl hlet) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (by simpa [locals'] using hguardNeg)) ?_
  exact ExecBlock.consRevert (ExecStmt.requireFalse hguardPosEval)

theorem execForkCheckedAddSignedRevertGuardNeg {evm : EVM.State} {locals : Store}
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

theorem execForkCheckedAddSignedRevertGuardPos {evm : EVM.State} {locals : Store}
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

theorem execForkSrcInkUpdateOk {evm : EVM.State} {I : ExecutionEnv}
    (locals : Store) (srcInkOld srcInkNew : UInt256)
    (hsz164 : 164 ≤ I.calldata.size)
    (hilk : locals.get? "ilk" = some (forkIlkValue I))
    (hsrc : locals.get? "src" = some (forkSrcValue I))
    (hdink : locals.get? "dink" = some (forkDinkValue I))
    (hbase : locals.get? "urns" = none)
    (hload :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (forkSrcInkSlot I) = srcInkOld)
    (hnew : srcInkNew = UInt256.sub srcInkOld (forkDinkWord I))
    (hguardNeg : forkDinkInt I ≤ 0 ∨ srcInkNew.toNat ≤ srcInkOld.toNat)
    (hguardPos : 0 ≤ forkDinkInt I ∨ srcInkOld.toNat ≤ srcInkNew.toNat) :
    ExecBlock config { contract := contract, locals := locals } evm
      (checkedSubSignedInto "srcInkNew"
        (.storage (urnsF (.var "ilk") (.var "src") "ink")) (.var "dink") ++
        [ .assign .storage (urnsF (.var "ilk") (.var "src") "ink") (.var "srcInkNew") ])
      (.ok
        { contract := contract,
          locals := locals.insert "srcInkNew" (.int (Int.ofNat srcInkNew.toNat)) }
        (Solm.EVM.storageStore evm evm.executionEnv.codeOwner
          (forkSrcInkSlot I) srcInkNew)) := by
  let locals' := locals.insert "srcInkNew" (.int (Int.ofNat srcInkNew.toNat))
  let evm' := Solm.EVM.storageStore evm evm.executionEnv.codeOwner
    (forkSrcInkSlot I) srcInkNew
  have hstorage :
      evalExpr? config { contract := contract, locals := locals } evm
        (.storage (urnsF (.var "ilk") (.var "src") "ink")) =
        .ok (.int (Int.ofNat srcInkOld.toNat)) := by
    rw [evalExpr_fork_src_ink_locals locals hsz164 hilk hsrc hbase, hload]
  have hdinkEval :
      evalExpr? config { contract := contract, locals := locals } evm (.var "dink") =
        .ok (.int (forkDinkInt I)) :=
    vatEvalExpr_varInt (by simpa [forkDinkValue] using hdink)
  have hlet :
      evalExpr? config { contract := contract, locals := locals } evm
        (wordWrap256
          (.binary .sub (.storage (urnsF (.var "ilk") (.var "src") "ink")) (.var "dink"))) =
        .ok (.int (Int.ofNat srcInkNew.toNat)) := by
    exact evalExpr_fold_wordWrapSub_ok hstorage hdinkEval
      (by simpa [hnew] using
        signedSubWrap srcInkOld (forkDinkWord I) (forkDinkInt I) (forkDinkInt_mod_word I))
  have hsrcInkNewEval :
      evalExpr? config { contract := contract, locals := locals' } evm (.var "srcInkNew") =
        .ok (.int (Int.ofNat srcInkNew.toNat)) := by
    exact vatEvalExpr_varUInt256 (by simp [locals'])
  have hdinkAfter :
      evalExpr? config { contract := contract, locals := locals' } evm (.var "dink") =
        .ok (.int (forkDinkInt I)) := by
    exact vatEvalExpr_varInt (by
      change (locals.insert "srcInkNew" (.int (Int.ofNat srcInkNew.toNat))).get? "dink" =
        some (.int (forkDinkInt I))
      rw [store_get_ne _ _ (by native_decide)]
      simpa [forkDinkValue] using hdink)
  have hstorageAfter :
      evalExpr? config { contract := contract, locals := locals' } evm
        (.storage (urnsF (.var "ilk") (.var "src") "ink")) =
        .ok (.int (Int.ofNat srcInkOld.toNat)) := by
    have hilk' : locals'.get? "ilk" = some (forkIlkValue I) := by
      change (locals.insert "srcInkNew" (.int (Int.ofNat srcInkNew.toNat))).get? "ilk" =
        some (forkIlkValue I)
      rw [store_get_ne _ _ (by native_decide), hilk]
    have hsrc' : locals'.get? "src" = some (forkSrcValue I) := by
      change (locals.insert "srcInkNew" (.int (Int.ofNat srcInkNew.toNat))).get? "src" =
        some (forkSrcValue I)
      rw [store_get_ne _ _ (by native_decide), hsrc]
    have hbase' : locals'.get? "urns" = none := by
      change (locals.insert "srcInkNew" (.int (Int.ofNat srcInkNew.toNat))).get? "urns" =
        none
      rw [store_get_ne _ _ (by native_decide), hbase]
    rw [evalExpr_fork_src_ink_locals locals' hsz164 hilk' hsrc' hbase', hload]
  have hreqNeg :
      evalExpr? config { contract := contract, locals := locals' } evm
        (eitherExpr (.binary .le (.var "dink") (.intLit 0))
          (.binary .le (.var "srcInkNew")
            (.storage (urnsF (.var "ilk") (.var "src") "ink")))) =
        .ok (.bool true) :=
    evalSignedSubGuardNeg_true hdinkAfter hsrcInkNewEval hstorageAfter hguardNeg
  have hreqPos :
      evalExpr? config { contract := contract, locals := locals' } evm
        (eitherExpr (.binary .ge (.var "dink") (.intLit 0))
          (.binary .ge (.var "srcInkNew")
            (.storage (urnsF (.var "ilk") (.var "src") "ink")))) =
        .ok (.bool true) :=
    evalSignedSubGuardPos_true hdinkAfter hsrcInkNewEval hstorageAfter hguardPos
  have hassign :
      assignStorageRef? config { contract := contract, locals := locals' } evm .storage
        (urnsF (.var "ilk") (.var "src") "ink") (.int (Int.ofNat srcInkNew.toNat)) =
        .ok ({ contract := contract, locals := locals' }, evm') := by
    have hilk' : locals'.get? "ilk" = some (forkIlkValue I) := by
      change (locals.insert "srcInkNew" (.int (Int.ofNat srcInkNew.toNat))).get? "ilk" =
        some (forkIlkValue I)
      rw [store_get_ne _ _ (by native_decide), hilk]
    have hsrc' : locals'.get? "src" = some (forkSrcValue I) := by
      change (locals.insert "srcInkNew" (.int (Int.ofNat srcInkNew.toNat))).get? "src" =
        some (forkSrcValue I)
      rw [store_get_ne _ _ (by native_decide), hsrc]
    have hbase' : locals'.get? "urns" = none := by
      change (locals.insert "srcInkNew" (.int (Int.ofNat srcInkNew.toNat))).get? "urns" =
        none
      rw [store_get_ne _ _ (by native_decide), hbase]
    simpa [evm'] using
      assignStorageRef_fork_src_ink evm I locals' srcInkNew hsz164 hilk' hsrc' hbase'
  change ExecBlock config { contract := contract, locals := locals } evm
    [ .letDecl "srcInkNew" (some uint256)
        (wordWrap256
          (.binary .sub (.storage (urnsF (.var "ilk") (.var "src") "ink")) (.var "dink"))),
      .require
        (eitherExpr (.binary .le (.var "dink") (.intLit 0))
          (.binary .le (.var "srcInkNew")
            (.storage (urnsF (.var "ilk") (.var "src") "ink")))),
      .require
        (eitherExpr (.binary .ge (.var "dink") (.intLit 0))
          (.binary .ge (.var "srcInkNew")
            (.storage (urnsF (.var "ilk") (.var "src") "ink")))),
      .assign .storage (urnsF (.var "ilk") (.var "src") "ink") (.var "srcInkNew") ]
    (.ok { contract := contract, locals := locals' } evm')
  refine ExecBlock.consNormal (ExecStmt.letDecl hlet) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue hreqNeg) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue hreqPos) ?_
  exact ExecBlock.consNormal (ExecStmt.assign hsrcInkNewEval hassign) ExecBlock.nil

theorem execForkSrcInkUpdateRevertGuardNeg {evm : EVM.State} {I : ExecutionEnv}
    (locals : Store) (srcInkOld srcInkNew : UInt256)
    (hsz164 : 164 ≤ I.calldata.size)
    (hilk : locals.get? "ilk" = some (forkIlkValue I))
    (hsrc : locals.get? "src" = some (forkSrcValue I))
    (hdink : locals.get? "dink" = some (forkDinkValue I))
    (hbase : locals.get? "urns" = none)
    (hload :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (forkSrcInkSlot I) = srcInkOld)
    (hnew : srcInkNew = UInt256.sub srcInkOld (forkDinkWord I))
    (hfail :
      ¬ (UInt256.sgt (forkDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.gt srcInkNew srcInkOld = ⟨0⟩)) :
    ExecBlock config { contract := contract, locals := locals } evm
      (checkedSubSignedInto "srcInkNew"
        (.storage (urnsF (.var "ilk") (.var "src") "ink")) (.var "dink") ++
        [ .assign .storage (urnsF (.var "ilk") (.var "src") "ink") (.var "srcInkNew") ])
      .reverted := by
  let locals' := locals.insert "srcInkNew" (.int (Int.ofNat srcInkNew.toNat))
  have hstorage :
      evalExpr? config { contract := contract, locals := locals } evm
        (.storage (urnsF (.var "ilk") (.var "src") "ink")) =
        .ok (.int (Int.ofNat srcInkOld.toNat)) := by
    rw [evalExpr_fork_src_ink_locals locals hsz164 hilk hsrc hbase, hload]
  have hdinkEval :
      evalExpr? config { contract := contract, locals := locals } evm (.var "dink") =
        .ok (.int (forkDinkInt I)) :=
    vatEvalExpr_varInt (by simpa [forkDinkValue] using hdink)
  have hdinkAfter :
      evalExpr? config { contract := contract, locals := locals' } evm (.var "dink") =
        .ok (.int (forkDinkInt I)) := by
    exact vatEvalExpr_varInt (by
      change (locals.insert "srcInkNew" (.int (Int.ofNat srcInkNew.toNat))).get? "dink" =
        some (.int (forkDinkInt I))
      rw [store_get_ne _ _ (by native_decide)]
      simpa [forkDinkValue] using hdink)
  have hstorageAfter :
      evalExpr? config { contract := contract, locals := locals' } evm
        (.storage (urnsF (.var "ilk") (.var "src") "ink")) =
        .ok (.int (Int.ofNat srcInkOld.toNat)) := by
    have hilk' : locals'.get? "ilk" = some (forkIlkValue I) := by
      change (locals.insert "srcInkNew" (.int (Int.ofNat srcInkNew.toNat))).get? "ilk" =
        some (forkIlkValue I)
      rw [store_get_ne _ _ (by native_decide), hilk]
    have hsrc' : locals'.get? "src" = some (forkSrcValue I) := by
      change (locals.insert "srcInkNew" (.int (Int.ofNat srcInkNew.toNat))).get? "src" =
        some (forkSrcValue I)
      rw [store_get_ne _ _ (by native_decide), hsrc]
    have hbase' : locals'.get? "urns" = none := by
      change (locals.insert "srcInkNew" (.int (Int.ofNat srcInkNew.toNat))).get? "urns" =
        none
      rw [store_get_ne _ _ (by native_decide), hbase]
    rw [evalExpr_fork_src_ink_locals locals' hsz164 hilk' hsrc' hbase', hload]
  have hsub :
      ExecBlock config { contract := contract, locals := locals } evm
        (checkedSubSignedInto "srcInkNew"
          (.storage (urnsF (.var "ilk") (.var "src") "ink")) (.var "dink"))
        .reverted :=
    execForkCheckedSubSignedRevertGuardNeg
      (x := .storage (urnsF (.var "ilk") (.var "src") "ink")) (y := .var "dink")
      (name := "srcInkNew") hstorage hdinkEval
      (by simpa [hnew] using
        signedSubWrap srcInkOld (forkDinkWord I) (forkDinkInt I) (forkDinkInt_mod_word I))
      (by simpa [locals'] using hdinkAfter)
      (by simpa [locals'] using hstorageAfter)
      (forkDinkSubGuardNegFailCond hfail)
  exact execBlock_append_term hsub (by intro f e h; cases h)

theorem execForkSrcInkUpdateRevertGuardPos {evm : EVM.State} {I : ExecutionEnv}
    (locals : Store) (srcInkOld srcInkNew : UInt256)
    (hsz164 : 164 ≤ I.calldata.size)
    (hilk : locals.get? "ilk" = some (forkIlkValue I))
    (hsrc : locals.get? "src" = some (forkSrcValue I))
    (hdink : locals.get? "dink" = some (forkDinkValue I))
    (hbase : locals.get? "urns" = none)
    (hload :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (forkSrcInkSlot I) = srcInkOld)
    (hnew : srcInkNew = UInt256.sub srcInkOld (forkDinkWord I))
    (hguardNeg :
      UInt256.sgt (forkDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.gt srcInkNew srcInkOld = ⟨0⟩)
    (hfail :
      ¬ (UInt256.slt (forkDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.lt srcInkNew srcInkOld = ⟨0⟩)) :
    ExecBlock config { contract := contract, locals := locals } evm
      (checkedSubSignedInto "srcInkNew"
        (.storage (urnsF (.var "ilk") (.var "src") "ink")) (.var "dink") ++
        [ .assign .storage (urnsF (.var "ilk") (.var "src") "ink") (.var "srcInkNew") ])
      .reverted := by
  let locals' := locals.insert "srcInkNew" (.int (Int.ofNat srcInkNew.toNat))
  have hstorage :
      evalExpr? config { contract := contract, locals := locals } evm
        (.storage (urnsF (.var "ilk") (.var "src") "ink")) =
        .ok (.int (Int.ofNat srcInkOld.toNat)) := by
    rw [evalExpr_fork_src_ink_locals locals hsz164 hilk hsrc hbase, hload]
  have hdinkEval :
      evalExpr? config { contract := contract, locals := locals } evm (.var "dink") =
        .ok (.int (forkDinkInt I)) :=
    vatEvalExpr_varInt (by simpa [forkDinkValue] using hdink)
  have hnewEval :
      evalExpr? config { contract := contract, locals := locals' } evm (.var "srcInkNew") =
        .ok (.int (Int.ofNat srcInkNew.toNat)) := by
    exact vatEvalExpr_varUInt256 (by simp [locals'])
  have hdinkAfter :
      evalExpr? config { contract := contract, locals := locals' } evm (.var "dink") =
        .ok (.int (forkDinkInt I)) := by
    exact vatEvalExpr_varInt (by
      change (locals.insert "srcInkNew" (.int (Int.ofNat srcInkNew.toNat))).get? "dink" =
        some (.int (forkDinkInt I))
      rw [store_get_ne _ _ (by native_decide)]
      simpa [forkDinkValue] using hdink)
  have hstorageAfter :
      evalExpr? config { contract := contract, locals := locals' } evm
        (.storage (urnsF (.var "ilk") (.var "src") "ink")) =
        .ok (.int (Int.ofNat srcInkOld.toNat)) := by
    have hilk' : locals'.get? "ilk" = some (forkIlkValue I) := by
      change (locals.insert "srcInkNew" (.int (Int.ofNat srcInkNew.toNat))).get? "ilk" =
        some (forkIlkValue I)
      rw [store_get_ne _ _ (by native_decide), hilk]
    have hsrc' : locals'.get? "src" = some (forkSrcValue I) := by
      change (locals.insert "srcInkNew" (.int (Int.ofNat srcInkNew.toNat))).get? "src" =
        some (forkSrcValue I)
      rw [store_get_ne _ _ (by native_decide), hsrc]
    have hbase' : locals'.get? "urns" = none := by
      change (locals.insert "srcInkNew" (.int (Int.ofNat srcInkNew.toNat))).get? "urns" =
        none
      rw [store_get_ne _ _ (by native_decide), hbase]
    rw [evalExpr_fork_src_ink_locals locals' hsz164 hilk' hsrc' hbase', hload]
  have hguardNegEval :
      evalExpr? config { contract := contract, locals := locals' } evm
        (eitherExpr (.binary .le (.var "dink") (.intLit 0))
          (.binary .le (.var "srcInkNew")
            (.storage (urnsF (.var "ilk") (.var "src") "ink")))) =
        .ok (.bool true) :=
    evalSignedSubGuardNeg_true hdinkAfter hnewEval hstorageAfter
      (forkDinkSubGuardNegCond hguardNeg)
  have hsub :
      ExecBlock config { contract := contract, locals := locals } evm
        (checkedSubSignedInto "srcInkNew"
          (.storage (urnsF (.var "ilk") (.var "src") "ink")) (.var "dink"))
        .reverted :=
    execForkCheckedSubSignedRevertGuardPos
      (x := .storage (urnsF (.var "ilk") (.var "src") "ink")) (y := .var "dink")
      (name := "srcInkNew") hstorage hdinkEval
      (by simpa [hnew] using
        signedSubWrap srcInkOld (forkDinkWord I) (forkDinkInt I) (forkDinkInt_mod_word I))
      (by simpa [locals'] using hdinkAfter)
      (by simpa [locals'] using hstorageAfter)
      (by simpa [locals'] using hguardNegEval)
      (forkDinkSubGuardPosFailCond hfail)
  exact execBlock_append_term hsub (by intro f e h; cases h)

theorem execForkSrcArtUpdateOk {evm : EVM.State} {I : ExecutionEnv}
    (locals : Store) (srcArtOld srcArtNew : UInt256)
    (hsz164 : 164 ≤ I.calldata.size)
    (hilk : locals.get? "ilk" = some (forkIlkValue I))
    (hsrc : locals.get? "src" = some (forkSrcValue I))
    (hdart : locals.get? "dart" = some (forkDartValue I))
    (hbase : locals.get? "urns" = none)
    (hload :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (forkSrcArtSlot I) = srcArtOld)
    (hnew : srcArtNew = UInt256.sub srcArtOld (forkDartWord I))
    (hguardNeg : forkDartInt I ≤ 0 ∨ srcArtNew.toNat ≤ srcArtOld.toNat)
    (hguardPos : 0 ≤ forkDartInt I ∨ srcArtOld.toNat ≤ srcArtNew.toNat) :
    ExecBlock config { contract := contract, locals := locals } evm
      (checkedSubSignedInto "srcArtNew"
        (.storage (urnsF (.var "ilk") (.var "src") "art")) (.var "dart") ++
        [ .assign .storage (urnsF (.var "ilk") (.var "src") "art") (.var "srcArtNew") ])
      (.ok
        { contract := contract,
          locals := locals.insert "srcArtNew" (.int (Int.ofNat srcArtNew.toNat)) }
        (Solm.EVM.storageStore evm evm.executionEnv.codeOwner
          (forkSrcArtSlot I) srcArtNew)) := by
  let locals' := locals.insert "srcArtNew" (.int (Int.ofNat srcArtNew.toNat))
  let evm' := Solm.EVM.storageStore evm evm.executionEnv.codeOwner
    (forkSrcArtSlot I) srcArtNew
  have hstorage :
      evalExpr? config { contract := contract, locals := locals } evm
        (.storage (urnsF (.var "ilk") (.var "src") "art")) =
        .ok (.int (Int.ofNat srcArtOld.toNat)) := by
    rw [evalExpr_fork_src_art_locals locals hsz164 hilk hsrc hbase, hload]
  have hdartEval :
      evalExpr? config { contract := contract, locals := locals } evm (.var "dart") =
        .ok (.int (forkDartInt I)) :=
    vatEvalExpr_varInt (by simpa [forkDartValue] using hdart)
  have hlet :
      evalExpr? config { contract := contract, locals := locals } evm
        (wordWrap256
          (.binary .sub (.storage (urnsF (.var "ilk") (.var "src") "art")) (.var "dart"))) =
        .ok (.int (Int.ofNat srcArtNew.toNat)) := by
    exact evalExpr_fold_wordWrapSub_ok hstorage hdartEval
      (by simpa [hnew] using
        signedSubWrap srcArtOld (forkDartWord I) (forkDartInt I) (forkDartInt_mod_word I))
  have hsrcArtNewEval :
      evalExpr? config { contract := contract, locals := locals' } evm (.var "srcArtNew") =
        .ok (.int (Int.ofNat srcArtNew.toNat)) := by
    exact vatEvalExpr_varUInt256 (by simp [locals'])
  have hdartAfter :
      evalExpr? config { contract := contract, locals := locals' } evm (.var "dart") =
        .ok (.int (forkDartInt I)) := by
    exact vatEvalExpr_varInt (by
      change (locals.insert "srcArtNew" (.int (Int.ofNat srcArtNew.toNat))).get? "dart" =
        some (.int (forkDartInt I))
      rw [store_get_ne _ _ (by native_decide)]
      simpa [forkDartValue] using hdart)
  have hstorageAfter :
      evalExpr? config { contract := contract, locals := locals' } evm
        (.storage (urnsF (.var "ilk") (.var "src") "art")) =
        .ok (.int (Int.ofNat srcArtOld.toNat)) := by
    have hilk' : locals'.get? "ilk" = some (forkIlkValue I) := by
      change (locals.insert "srcArtNew" (.int (Int.ofNat srcArtNew.toNat))).get? "ilk" =
        some (forkIlkValue I)
      rw [store_get_ne _ _ (by native_decide), hilk]
    have hsrc' : locals'.get? "src" = some (forkSrcValue I) := by
      change (locals.insert "srcArtNew" (.int (Int.ofNat srcArtNew.toNat))).get? "src" =
        some (forkSrcValue I)
      rw [store_get_ne _ _ (by native_decide), hsrc]
    have hbase' : locals'.get? "urns" = none := by
      change (locals.insert "srcArtNew" (.int (Int.ofNat srcArtNew.toNat))).get? "urns" =
        none
      rw [store_get_ne _ _ (by native_decide), hbase]
    rw [evalExpr_fork_src_art_locals locals' hsz164 hilk' hsrc' hbase', hload]
  have hreqNeg :
      evalExpr? config { contract := contract, locals := locals' } evm
        (eitherExpr (.binary .le (.var "dart") (.intLit 0))
          (.binary .le (.var "srcArtNew")
            (.storage (urnsF (.var "ilk") (.var "src") "art")))) =
        .ok (.bool true) :=
    evalSignedSubGuardNeg_true hdartAfter hsrcArtNewEval hstorageAfter hguardNeg
  have hreqPos :
      evalExpr? config { contract := contract, locals := locals' } evm
        (eitherExpr (.binary .ge (.var "dart") (.intLit 0))
          (.binary .ge (.var "srcArtNew")
            (.storage (urnsF (.var "ilk") (.var "src") "art")))) =
        .ok (.bool true) :=
    evalSignedSubGuardPos_true hdartAfter hsrcArtNewEval hstorageAfter hguardPos
  have hassign :
      assignStorageRef? config { contract := contract, locals := locals' } evm .storage
        (urnsF (.var "ilk") (.var "src") "art") (.int (Int.ofNat srcArtNew.toNat)) =
        .ok ({ contract := contract, locals := locals' }, evm') := by
    have hilk' : locals'.get? "ilk" = some (forkIlkValue I) := by
      change (locals.insert "srcArtNew" (.int (Int.ofNat srcArtNew.toNat))).get? "ilk" =
        some (forkIlkValue I)
      rw [store_get_ne _ _ (by native_decide), hilk]
    have hsrc' : locals'.get? "src" = some (forkSrcValue I) := by
      change (locals.insert "srcArtNew" (.int (Int.ofNat srcArtNew.toNat))).get? "src" =
        some (forkSrcValue I)
      rw [store_get_ne _ _ (by native_decide), hsrc]
    have hbase' : locals'.get? "urns" = none := by
      change (locals.insert "srcArtNew" (.int (Int.ofNat srcArtNew.toNat))).get? "urns" =
        none
      rw [store_get_ne _ _ (by native_decide), hbase]
    simpa [evm'] using
      assignStorageRef_fork_src_art evm I locals' srcArtNew hsz164 hilk' hsrc' hbase'
  change ExecBlock config { contract := contract, locals := locals } evm
    [ .letDecl "srcArtNew" (some uint256)
        (wordWrap256
          (.binary .sub (.storage (urnsF (.var "ilk") (.var "src") "art")) (.var "dart"))),
      .require
        (eitherExpr (.binary .le (.var "dart") (.intLit 0))
          (.binary .le (.var "srcArtNew")
            (.storage (urnsF (.var "ilk") (.var "src") "art")))),
      .require
        (eitherExpr (.binary .ge (.var "dart") (.intLit 0))
          (.binary .ge (.var "srcArtNew")
            (.storage (urnsF (.var "ilk") (.var "src") "art")))),
      .assign .storage (urnsF (.var "ilk") (.var "src") "art") (.var "srcArtNew") ]
    (.ok { contract := contract, locals := locals' } evm')
  refine ExecBlock.consNormal (ExecStmt.letDecl hlet) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue hreqNeg) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue hreqPos) ?_
  exact ExecBlock.consNormal (ExecStmt.assign hsrcArtNewEval hassign) ExecBlock.nil

theorem execForkSrcArtUpdateRevertGuardNeg {evm : EVM.State} {I : ExecutionEnv}
    (locals : Store) (srcArtOld srcArtNew : UInt256)
    (hsz164 : 164 ≤ I.calldata.size)
    (hilk : locals.get? "ilk" = some (forkIlkValue I))
    (hsrc : locals.get? "src" = some (forkSrcValue I))
    (hdart : locals.get? "dart" = some (forkDartValue I))
    (hbase : locals.get? "urns" = none)
    (hload :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (forkSrcArtSlot I) = srcArtOld)
    (hnew : srcArtNew = UInt256.sub srcArtOld (forkDartWord I))
    (hfail :
      ¬ (UInt256.sgt (forkDartWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.gt srcArtNew srcArtOld = ⟨0⟩)) :
    ExecBlock config { contract := contract, locals := locals } evm
      (checkedSubSignedInto "srcArtNew"
        (.storage (urnsF (.var "ilk") (.var "src") "art")) (.var "dart") ++
        [ .assign .storage (urnsF (.var "ilk") (.var "src") "art") (.var "srcArtNew") ])
      .reverted := by
  let locals' := locals.insert "srcArtNew" (.int (Int.ofNat srcArtNew.toNat))
  have hstorage :
      evalExpr? config { contract := contract, locals := locals } evm
        (.storage (urnsF (.var "ilk") (.var "src") "art")) =
        .ok (.int (Int.ofNat srcArtOld.toNat)) := by
    rw [evalExpr_fork_src_art_locals locals hsz164 hilk hsrc hbase, hload]
  have hdartEval :
      evalExpr? config { contract := contract, locals := locals } evm (.var "dart") =
        .ok (.int (forkDartInt I)) :=
    vatEvalExpr_varInt (by simpa [forkDartValue] using hdart)
  have hdartAfter :
      evalExpr? config { contract := contract, locals := locals' } evm (.var "dart") =
        .ok (.int (forkDartInt I)) := by
    exact vatEvalExpr_varInt (by
      change (locals.insert "srcArtNew" (.int (Int.ofNat srcArtNew.toNat))).get? "dart" =
        some (.int (forkDartInt I))
      rw [store_get_ne _ _ (by native_decide)]
      simpa [forkDartValue] using hdart)
  have hstorageAfter :
      evalExpr? config { contract := contract, locals := locals' } evm
        (.storage (urnsF (.var "ilk") (.var "src") "art")) =
        .ok (.int (Int.ofNat srcArtOld.toNat)) := by
    have hilk' : locals'.get? "ilk" = some (forkIlkValue I) := by
      change (locals.insert "srcArtNew" (.int (Int.ofNat srcArtNew.toNat))).get? "ilk" =
        some (forkIlkValue I)
      rw [store_get_ne _ _ (by native_decide), hilk]
    have hsrc' : locals'.get? "src" = some (forkSrcValue I) := by
      change (locals.insert "srcArtNew" (.int (Int.ofNat srcArtNew.toNat))).get? "src" =
        some (forkSrcValue I)
      rw [store_get_ne _ _ (by native_decide), hsrc]
    have hbase' : locals'.get? "urns" = none := by
      change (locals.insert "srcArtNew" (.int (Int.ofNat srcArtNew.toNat))).get? "urns" =
        none
      rw [store_get_ne _ _ (by native_decide), hbase]
    rw [evalExpr_fork_src_art_locals locals' hsz164 hilk' hsrc' hbase', hload]
  have hsub :
      ExecBlock config { contract := contract, locals := locals } evm
        (checkedSubSignedInto "srcArtNew"
          (.storage (urnsF (.var "ilk") (.var "src") "art")) (.var "dart"))
        .reverted :=
    execForkCheckedSubSignedRevertGuardNeg
      (x := .storage (urnsF (.var "ilk") (.var "src") "art")) (y := .var "dart")
      (name := "srcArtNew") hstorage hdartEval
      (by simpa [hnew] using
        signedSubWrap srcArtOld (forkDartWord I) (forkDartInt I) (forkDartInt_mod_word I))
      (by simpa [locals'] using hdartAfter)
      (by simpa [locals'] using hstorageAfter)
      (forkDartSubGuardNegFailCond hfail)
  exact execBlock_append_term hsub (by intro f e h; cases h)

theorem execForkSrcArtUpdateRevertGuardPos {evm : EVM.State} {I : ExecutionEnv}
    (locals : Store) (srcArtOld srcArtNew : UInt256)
    (hsz164 : 164 ≤ I.calldata.size)
    (hilk : locals.get? "ilk" = some (forkIlkValue I))
    (hsrc : locals.get? "src" = some (forkSrcValue I))
    (hdart : locals.get? "dart" = some (forkDartValue I))
    (hbase : locals.get? "urns" = none)
    (hload :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (forkSrcArtSlot I) = srcArtOld)
    (hnew : srcArtNew = UInt256.sub srcArtOld (forkDartWord I))
    (hguardNeg :
      UInt256.sgt (forkDartWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.gt srcArtNew srcArtOld = ⟨0⟩)
    (hfail :
      ¬ (UInt256.slt (forkDartWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.lt srcArtNew srcArtOld = ⟨0⟩)) :
    ExecBlock config { contract := contract, locals := locals } evm
      (checkedSubSignedInto "srcArtNew"
        (.storage (urnsF (.var "ilk") (.var "src") "art")) (.var "dart") ++
        [ .assign .storage (urnsF (.var "ilk") (.var "src") "art") (.var "srcArtNew") ])
      .reverted := by
  let locals' := locals.insert "srcArtNew" (.int (Int.ofNat srcArtNew.toNat))
  have hstorage :
      evalExpr? config { contract := contract, locals := locals } evm
        (.storage (urnsF (.var "ilk") (.var "src") "art")) =
        .ok (.int (Int.ofNat srcArtOld.toNat)) := by
    rw [evalExpr_fork_src_art_locals locals hsz164 hilk hsrc hbase, hload]
  have hdartEval :
      evalExpr? config { contract := contract, locals := locals } evm (.var "dart") =
        .ok (.int (forkDartInt I)) :=
    vatEvalExpr_varInt (by simpa [forkDartValue] using hdart)
  have hnewEval :
      evalExpr? config { contract := contract, locals := locals' } evm (.var "srcArtNew") =
        .ok (.int (Int.ofNat srcArtNew.toNat)) := by
    exact vatEvalExpr_varUInt256 (by simp [locals'])
  have hdartAfter :
      evalExpr? config { contract := contract, locals := locals' } evm (.var "dart") =
        .ok (.int (forkDartInt I)) := by
    exact vatEvalExpr_varInt (by
      change (locals.insert "srcArtNew" (.int (Int.ofNat srcArtNew.toNat))).get? "dart" =
        some (.int (forkDartInt I))
      rw [store_get_ne _ _ (by native_decide)]
      simpa [forkDartValue] using hdart)
  have hstorageAfter :
      evalExpr? config { contract := contract, locals := locals' } evm
        (.storage (urnsF (.var "ilk") (.var "src") "art")) =
        .ok (.int (Int.ofNat srcArtOld.toNat)) := by
    have hilk' : locals'.get? "ilk" = some (forkIlkValue I) := by
      change (locals.insert "srcArtNew" (.int (Int.ofNat srcArtNew.toNat))).get? "ilk" =
        some (forkIlkValue I)
      rw [store_get_ne _ _ (by native_decide), hilk]
    have hsrc' : locals'.get? "src" = some (forkSrcValue I) := by
      change (locals.insert "srcArtNew" (.int (Int.ofNat srcArtNew.toNat))).get? "src" =
        some (forkSrcValue I)
      rw [store_get_ne _ _ (by native_decide), hsrc]
    have hbase' : locals'.get? "urns" = none := by
      change (locals.insert "srcArtNew" (.int (Int.ofNat srcArtNew.toNat))).get? "urns" =
        none
      rw [store_get_ne _ _ (by native_decide), hbase]
    rw [evalExpr_fork_src_art_locals locals' hsz164 hilk' hsrc' hbase', hload]
  have hguardNegEval :
      evalExpr? config { contract := contract, locals := locals' } evm
        (eitherExpr (.binary .le (.var "dart") (.intLit 0))
          (.binary .le (.var "srcArtNew")
            (.storage (urnsF (.var "ilk") (.var "src") "art")))) =
        .ok (.bool true) :=
    evalSignedSubGuardNeg_true hdartAfter hnewEval hstorageAfter
      (forkDartSubGuardNegCond hguardNeg)
  have hsub :
      ExecBlock config { contract := contract, locals := locals } evm
        (checkedSubSignedInto "srcArtNew"
          (.storage (urnsF (.var "ilk") (.var "src") "art")) (.var "dart"))
        .reverted :=
    execForkCheckedSubSignedRevertGuardPos
      (x := .storage (urnsF (.var "ilk") (.var "src") "art")) (y := .var "dart")
      (name := "srcArtNew") hstorage hdartEval
      (by simpa [hnew] using
        signedSubWrap srcArtOld (forkDartWord I) (forkDartInt I) (forkDartInt_mod_word I))
      (by simpa [locals'] using hdartAfter)
      (by simpa [locals'] using hstorageAfter)
      (by simpa [locals'] using hguardNegEval)
      (forkDartSubGuardPosFailCond hfail)
  exact execBlock_append_term hsub (by intro f e h; cases h)

theorem execForkDstInkUpdateOk {evm : EVM.State} {I : ExecutionEnv}
    (locals : Store) (dstInkOld dstInkNew : UInt256)
    (hsz164 : 164 ≤ I.calldata.size)
    (hilk : locals.get? "ilk" = some (forkIlkValue I))
    (hdst : locals.get? "dst" = some (forkDstValue I))
    (hdink : locals.get? "dink" = some (forkDinkValue I))
    (hbase : locals.get? "urns" = none)
    (hload :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (forkDstInkSlot I) = dstInkOld)
    (hnew : dstInkNew = forkDinkWord I + dstInkOld)
    (hguardNeg : 0 ≤ forkDinkInt I ∨ dstInkNew.toNat ≤ dstInkOld.toNat)
    (hguardPos : forkDinkInt I ≤ 0 ∨ dstInkOld.toNat ≤ dstInkNew.toNat) :
    ExecBlock config { contract := contract, locals := locals } evm
      (checkedAddSignedInto "dstInkNew"
        (.storage (urnsF (.var "ilk") (.var "dst") "ink")) (.var "dink") ++
        [ .assign .storage (urnsF (.var "ilk") (.var "dst") "ink") (.var "dstInkNew") ])
      (.ok
        { contract := contract,
          locals := locals.insert "dstInkNew" (.int (Int.ofNat dstInkNew.toNat)) }
        (Solm.EVM.storageStore evm evm.executionEnv.codeOwner
          (forkDstInkSlot I) dstInkNew)) := by
  let locals' := locals.insert "dstInkNew" (.int (Int.ofNat dstInkNew.toNat))
  let evm' := Solm.EVM.storageStore evm evm.executionEnv.codeOwner
    (forkDstInkSlot I) dstInkNew
  have hstorage :
      evalExpr? config { contract := contract, locals := locals } evm
        (.storage (urnsF (.var "ilk") (.var "dst") "ink")) =
        .ok (.int (Int.ofNat dstInkOld.toNat)) := by
    rw [evalExpr_fork_dst_ink_locals locals hsz164 hilk hdst hbase, hload]
  have hdinkEval :
      evalExpr? config { contract := contract, locals := locals } evm (.var "dink") =
        .ok (.int (forkDinkInt I)) :=
    vatEvalExpr_varInt (by simpa [forkDinkValue] using hdink)
  have hlet :
      evalExpr? config { contract := contract, locals := locals } evm
        (wordWrap256
          (.binary .add (.storage (urnsF (.var "ilk") (.var "dst") "ink")) (.var "dink"))) =
        .ok (.int (Int.ofNat dstInkNew.toNat)) := by
    exact evalExpr_fold_wordWrapAdd_ok hstorage hdinkEval
      (forkDinkInt_mod_word I) hnew
  have hdstInkNewEval :
      evalExpr? config { contract := contract, locals := locals' } evm (.var "dstInkNew") =
        .ok (.int (Int.ofNat dstInkNew.toNat)) := by
    exact vatEvalExpr_varUInt256 (by simp [locals'])
  have hdinkAfter :
      evalExpr? config { contract := contract, locals := locals' } evm (.var "dink") =
        .ok (.int (forkDinkInt I)) := by
    exact vatEvalExpr_varInt (by
      change (locals.insert "dstInkNew" (.int (Int.ofNat dstInkNew.toNat))).get? "dink" =
        some (.int (forkDinkInt I))
      rw [store_get_ne _ _ (by native_decide)]
      simpa [forkDinkValue] using hdink)
  have hstorageAfter :
      evalExpr? config { contract := contract, locals := locals' } evm
        (.storage (urnsF (.var "ilk") (.var "dst") "ink")) =
        .ok (.int (Int.ofNat dstInkOld.toNat)) := by
    have hilk' : locals'.get? "ilk" = some (forkIlkValue I) := by
      change (locals.insert "dstInkNew" (.int (Int.ofNat dstInkNew.toNat))).get? "ilk" =
        some (forkIlkValue I)
      rw [store_get_ne _ _ (by native_decide), hilk]
    have hdst' : locals'.get? "dst" = some (forkDstValue I) := by
      change (locals.insert "dstInkNew" (.int (Int.ofNat dstInkNew.toNat))).get? "dst" =
        some (forkDstValue I)
      rw [store_get_ne _ _ (by native_decide), hdst]
    have hbase' : locals'.get? "urns" = none := by
      change (locals.insert "dstInkNew" (.int (Int.ofNat dstInkNew.toNat))).get? "urns" =
        none
      rw [store_get_ne _ _ (by native_decide), hbase]
    rw [evalExpr_fork_dst_ink_locals locals' hsz164 hilk' hdst' hbase', hload]
  have hreqNeg :
      evalExpr? config { contract := contract, locals := locals' } evm
        (eitherExpr (.binary .ge (.var "dink") (.intLit 0))
          (.binary .le (.var "dstInkNew")
            (.storage (urnsF (.var "ilk") (.var "dst") "ink")))) =
        .ok (.bool true) :=
    evalSignedAddGuardNeg_true hdinkAfter hdstInkNewEval hstorageAfter hguardNeg
  have hreqPos :
      evalExpr? config { contract := contract, locals := locals' } evm
        (eitherExpr (.binary .le (.var "dink") (.intLit 0))
          (.binary .ge (.var "dstInkNew")
            (.storage (urnsF (.var "ilk") (.var "dst") "ink")))) =
        .ok (.bool true) :=
    evalSignedAddGuardPos_true hdinkAfter hdstInkNewEval hstorageAfter hguardPos
  have hassign :
      assignStorageRef? config { contract := contract, locals := locals' } evm .storage
        (urnsF (.var "ilk") (.var "dst") "ink") (.int (Int.ofNat dstInkNew.toNat)) =
        .ok ({ contract := contract, locals := locals' }, evm') := by
    have hilk' : locals'.get? "ilk" = some (forkIlkValue I) := by
      change (locals.insert "dstInkNew" (.int (Int.ofNat dstInkNew.toNat))).get? "ilk" =
        some (forkIlkValue I)
      rw [store_get_ne _ _ (by native_decide), hilk]
    have hdst' : locals'.get? "dst" = some (forkDstValue I) := by
      change (locals.insert "dstInkNew" (.int (Int.ofNat dstInkNew.toNat))).get? "dst" =
        some (forkDstValue I)
      rw [store_get_ne _ _ (by native_decide), hdst]
    have hbase' : locals'.get? "urns" = none := by
      change (locals.insert "dstInkNew" (.int (Int.ofNat dstInkNew.toNat))).get? "urns" =
        none
      rw [store_get_ne _ _ (by native_decide), hbase]
    simpa [evm'] using
      assignStorageRef_fork_dst_ink evm I locals' dstInkNew hsz164 hilk' hdst' hbase'
  change ExecBlock config { contract := contract, locals := locals } evm
    [ .letDecl "dstInkNew" (some uint256)
        (wordWrap256
          (.binary .add (.storage (urnsF (.var "ilk") (.var "dst") "ink")) (.var "dink"))),
      .require
        (eitherExpr (.binary .ge (.var "dink") (.intLit 0))
          (.binary .le (.var "dstInkNew")
            (.storage (urnsF (.var "ilk") (.var "dst") "ink")))),
      .require
        (eitherExpr (.binary .le (.var "dink") (.intLit 0))
          (.binary .ge (.var "dstInkNew")
            (.storage (urnsF (.var "ilk") (.var "dst") "ink")))),
      .assign .storage (urnsF (.var "ilk") (.var "dst") "ink") (.var "dstInkNew") ]
    (.ok { contract := contract, locals := locals' } evm')
  refine ExecBlock.consNormal (ExecStmt.letDecl hlet) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue hreqNeg) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue hreqPos) ?_
  exact ExecBlock.consNormal (ExecStmt.assign hdstInkNewEval hassign) ExecBlock.nil

theorem execForkDstInkUpdateRevertGuardNeg {evm : EVM.State} {I : ExecutionEnv}
    (locals : Store) (dstInkOld dstInkNew : UInt256)
    (hsz164 : 164 ≤ I.calldata.size)
    (hilk : locals.get? "ilk" = some (forkIlkValue I))
    (hdst : locals.get? "dst" = some (forkDstValue I))
    (hdink : locals.get? "dink" = some (forkDinkValue I))
    (hbase : locals.get? "urns" = none)
    (hload :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (forkDstInkSlot I) = dstInkOld)
    (hnew : dstInkNew = forkDinkWord I + dstInkOld)
    (hfail :
      ¬ (UInt256.slt (forkDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.gt dstInkNew dstInkOld = ⟨0⟩)) :
    ExecBlock config { contract := contract, locals := locals } evm
      (checkedAddSignedInto "dstInkNew"
        (.storage (urnsF (.var "ilk") (.var "dst") "ink")) (.var "dink") ++
        [ .assign .storage (urnsF (.var "ilk") (.var "dst") "ink") (.var "dstInkNew") ])
      .reverted := by
  let locals' := locals.insert "dstInkNew" (.int (Int.ofNat dstInkNew.toNat))
  have hstorage :
      evalExpr? config { contract := contract, locals := locals } evm
        (.storage (urnsF (.var "ilk") (.var "dst") "ink")) =
        .ok (.int (Int.ofNat dstInkOld.toNat)) := by
    rw [evalExpr_fork_dst_ink_locals locals hsz164 hilk hdst hbase, hload]
  have hdinkEval :
      evalExpr? config { contract := contract, locals := locals } evm (.var "dink") =
        .ok (.int (forkDinkInt I)) :=
    vatEvalExpr_varInt (by simpa [forkDinkValue] using hdink)
  have hdinkAfter :
      evalExpr? config { contract := contract, locals := locals' } evm (.var "dink") =
        .ok (.int (forkDinkInt I)) := by
    exact vatEvalExpr_varInt (by
      change (locals.insert "dstInkNew" (.int (Int.ofNat dstInkNew.toNat))).get? "dink" =
        some (.int (forkDinkInt I))
      rw [store_get_ne _ _ (by native_decide)]
      simpa [forkDinkValue] using hdink)
  have hstorageAfter :
      evalExpr? config { contract := contract, locals := locals' } evm
        (.storage (urnsF (.var "ilk") (.var "dst") "ink")) =
        .ok (.int (Int.ofNat dstInkOld.toNat)) := by
    have hilk' : locals'.get? "ilk" = some (forkIlkValue I) := by
      change (locals.insert "dstInkNew" (.int (Int.ofNat dstInkNew.toNat))).get? "ilk" =
        some (forkIlkValue I)
      rw [store_get_ne _ _ (by native_decide), hilk]
    have hdst' : locals'.get? "dst" = some (forkDstValue I) := by
      change (locals.insert "dstInkNew" (.int (Int.ofNat dstInkNew.toNat))).get? "dst" =
        some (forkDstValue I)
      rw [store_get_ne _ _ (by native_decide), hdst]
    have hbase' : locals'.get? "urns" = none := by
      change (locals.insert "dstInkNew" (.int (Int.ofNat dstInkNew.toNat))).get? "urns" =
        none
      rw [store_get_ne _ _ (by native_decide), hbase]
    rw [evalExpr_fork_dst_ink_locals locals' hsz164 hilk' hdst' hbase', hload]
  have hadd :
      ExecBlock config { contract := contract, locals := locals } evm
        (checkedAddSignedInto "dstInkNew"
          (.storage (urnsF (.var "ilk") (.var "dst") "ink")) (.var "dink"))
        .reverted :=
    execForkCheckedAddSignedRevertGuardNeg
      (x := .storage (urnsF (.var "ilk") (.var "dst") "ink")) (y := .var "dink")
      (name := "dstInkNew") hstorage hdinkEval (forkDinkInt_mod_word I) hnew
      (by simpa [locals'] using hdinkAfter)
      (by simpa [locals'] using hstorageAfter)
      (forkDinkAddGuardNegFailCond hfail)
  exact execBlock_append_term hadd (by intro f e h; cases h)

theorem execForkDstInkUpdateRevertGuardPos {evm : EVM.State} {I : ExecutionEnv}
    (locals : Store) (dstInkOld dstInkNew : UInt256)
    (hsz164 : 164 ≤ I.calldata.size)
    (hilk : locals.get? "ilk" = some (forkIlkValue I))
    (hdst : locals.get? "dst" = some (forkDstValue I))
    (hdink : locals.get? "dink" = some (forkDinkValue I))
    (hbase : locals.get? "urns" = none)
    (hload :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (forkDstInkSlot I) = dstInkOld)
    (hnew : dstInkNew = forkDinkWord I + dstInkOld)
    (hguardNeg :
      UInt256.slt (forkDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.gt dstInkNew dstInkOld = ⟨0⟩)
    (hfail :
      ¬ (UInt256.sgt (forkDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.lt dstInkNew dstInkOld = ⟨0⟩)) :
    ExecBlock config { contract := contract, locals := locals } evm
      (checkedAddSignedInto "dstInkNew"
        (.storage (urnsF (.var "ilk") (.var "dst") "ink")) (.var "dink") ++
        [ .assign .storage (urnsF (.var "ilk") (.var "dst") "ink") (.var "dstInkNew") ])
      .reverted := by
  let locals' := locals.insert "dstInkNew" (.int (Int.ofNat dstInkNew.toNat))
  have hstorage :
      evalExpr? config { contract := contract, locals := locals } evm
        (.storage (urnsF (.var "ilk") (.var "dst") "ink")) =
        .ok (.int (Int.ofNat dstInkOld.toNat)) := by
    rw [evalExpr_fork_dst_ink_locals locals hsz164 hilk hdst hbase, hload]
  have hdinkEval :
      evalExpr? config { contract := contract, locals := locals } evm (.var "dink") =
        .ok (.int (forkDinkInt I)) :=
    vatEvalExpr_varInt (by simpa [forkDinkValue] using hdink)
  have hnewEval :
      evalExpr? config { contract := contract, locals := locals' } evm (.var "dstInkNew") =
        .ok (.int (Int.ofNat dstInkNew.toNat)) := by
    exact vatEvalExpr_varUInt256 (by simp [locals'])
  have hdinkAfter :
      evalExpr? config { contract := contract, locals := locals' } evm (.var "dink") =
        .ok (.int (forkDinkInt I)) := by
    exact vatEvalExpr_varInt (by
      change (locals.insert "dstInkNew" (.int (Int.ofNat dstInkNew.toNat))).get? "dink" =
        some (.int (forkDinkInt I))
      rw [store_get_ne _ _ (by native_decide)]
      simpa [forkDinkValue] using hdink)
  have hstorageAfter :
      evalExpr? config { contract := contract, locals := locals' } evm
        (.storage (urnsF (.var "ilk") (.var "dst") "ink")) =
        .ok (.int (Int.ofNat dstInkOld.toNat)) := by
    have hilk' : locals'.get? "ilk" = some (forkIlkValue I) := by
      change (locals.insert "dstInkNew" (.int (Int.ofNat dstInkNew.toNat))).get? "ilk" =
        some (forkIlkValue I)
      rw [store_get_ne _ _ (by native_decide), hilk]
    have hdst' : locals'.get? "dst" = some (forkDstValue I) := by
      change (locals.insert "dstInkNew" (.int (Int.ofNat dstInkNew.toNat))).get? "dst" =
        some (forkDstValue I)
      rw [store_get_ne _ _ (by native_decide), hdst]
    have hbase' : locals'.get? "urns" = none := by
      change (locals.insert "dstInkNew" (.int (Int.ofNat dstInkNew.toNat))).get? "urns" =
        none
      rw [store_get_ne _ _ (by native_decide), hbase]
    rw [evalExpr_fork_dst_ink_locals locals' hsz164 hilk' hdst' hbase', hload]
  have hguardNegEval :
      evalExpr? config { contract := contract, locals := locals' } evm
        (eitherExpr (.binary .ge (.var "dink") (.intLit 0))
          (.binary .le (.var "dstInkNew")
            (.storage (urnsF (.var "ilk") (.var "dst") "ink")))) =
        .ok (.bool true) :=
    evalSignedAddGuardNeg_true hdinkAfter hnewEval hstorageAfter
      (forkDinkAddGuardNegCond hguardNeg)
  have hadd :
      ExecBlock config { contract := contract, locals := locals } evm
        (checkedAddSignedInto "dstInkNew"
          (.storage (urnsF (.var "ilk") (.var "dst") "ink")) (.var "dink"))
        .reverted :=
    execForkCheckedAddSignedRevertGuardPos
      (x := .storage (urnsF (.var "ilk") (.var "dst") "ink")) (y := .var "dink")
      (name := "dstInkNew") hstorage hdinkEval (forkDinkInt_mod_word I) hnew
      (by simpa [locals'] using hdinkAfter)
      (by simpa [locals'] using hstorageAfter)
      (by simpa [locals'] using hguardNegEval)
      (forkDinkAddGuardPosFailCond hfail)
  exact execBlock_append_term hadd (by intro f e h; cases h)

theorem execForkDstArtUpdateOk {evm : EVM.State} {I : ExecutionEnv}
    (locals : Store) (dstArtOld dstArtNew : UInt256)
    (hsz164 : 164 ≤ I.calldata.size)
    (hilk : locals.get? "ilk" = some (forkIlkValue I))
    (hdst : locals.get? "dst" = some (forkDstValue I))
    (hdart : locals.get? "dart" = some (forkDartValue I))
    (hbase : locals.get? "urns" = none)
    (hload :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (forkDstArtSlot I) = dstArtOld)
    (hnew : dstArtNew = forkDartWord I + dstArtOld)
    (hguardNeg : 0 ≤ forkDartInt I ∨ dstArtNew.toNat ≤ dstArtOld.toNat)
    (hguardPos : forkDartInt I ≤ 0 ∨ dstArtOld.toNat ≤ dstArtNew.toNat) :
    ExecBlock config { contract := contract, locals := locals } evm
      (checkedAddSignedInto "dstArtNew"
        (.storage (urnsF (.var "ilk") (.var "dst") "art")) (.var "dart") ++
        [ .assign .storage (urnsF (.var "ilk") (.var "dst") "art") (.var "dstArtNew") ])
      (.ok
        { contract := contract,
          locals := locals.insert "dstArtNew" (.int (Int.ofNat dstArtNew.toNat)) }
        (Solm.EVM.storageStore evm evm.executionEnv.codeOwner
          (forkDstArtSlot I) dstArtNew)) := by
  let locals' := locals.insert "dstArtNew" (.int (Int.ofNat dstArtNew.toNat))
  let evm' := Solm.EVM.storageStore evm evm.executionEnv.codeOwner
    (forkDstArtSlot I) dstArtNew
  have hstorage :
      evalExpr? config { contract := contract, locals := locals } evm
        (.storage (urnsF (.var "ilk") (.var "dst") "art")) =
        .ok (.int (Int.ofNat dstArtOld.toNat)) := by
    rw [evalExpr_fork_dst_art_locals locals hsz164 hilk hdst hbase, hload]
  have hdartEval :
      evalExpr? config { contract := contract, locals := locals } evm (.var "dart") =
        .ok (.int (forkDartInt I)) :=
    vatEvalExpr_varInt (by simpa [forkDartValue] using hdart)
  have hlet :
      evalExpr? config { contract := contract, locals := locals } evm
        (wordWrap256
          (.binary .add (.storage (urnsF (.var "ilk") (.var "dst") "art")) (.var "dart"))) =
        .ok (.int (Int.ofNat dstArtNew.toNat)) := by
    exact evalExpr_fold_wordWrapAdd_ok hstorage hdartEval
      (forkDartInt_mod_word I) hnew
  have hdstArtNewEval :
      evalExpr? config { contract := contract, locals := locals' } evm (.var "dstArtNew") =
        .ok (.int (Int.ofNat dstArtNew.toNat)) := by
    exact vatEvalExpr_varUInt256 (by simp [locals'])
  have hdartAfter :
      evalExpr? config { contract := contract, locals := locals' } evm (.var "dart") =
        .ok (.int (forkDartInt I)) := by
    exact vatEvalExpr_varInt (by
      change (locals.insert "dstArtNew" (.int (Int.ofNat dstArtNew.toNat))).get? "dart" =
        some (.int (forkDartInt I))
      rw [store_get_ne _ _ (by native_decide)]
      simpa [forkDartValue] using hdart)
  have hstorageAfter :
      evalExpr? config { contract := contract, locals := locals' } evm
        (.storage (urnsF (.var "ilk") (.var "dst") "art")) =
        .ok (.int (Int.ofNat dstArtOld.toNat)) := by
    have hilk' : locals'.get? "ilk" = some (forkIlkValue I) := by
      change (locals.insert "dstArtNew" (.int (Int.ofNat dstArtNew.toNat))).get? "ilk" =
        some (forkIlkValue I)
      rw [store_get_ne _ _ (by native_decide), hilk]
    have hdst' : locals'.get? "dst" = some (forkDstValue I) := by
      change (locals.insert "dstArtNew" (.int (Int.ofNat dstArtNew.toNat))).get? "dst" =
        some (forkDstValue I)
      rw [store_get_ne _ _ (by native_decide), hdst]
    have hbase' : locals'.get? "urns" = none := by
      change (locals.insert "dstArtNew" (.int (Int.ofNat dstArtNew.toNat))).get? "urns" =
        none
      rw [store_get_ne _ _ (by native_decide), hbase]
    rw [evalExpr_fork_dst_art_locals locals' hsz164 hilk' hdst' hbase', hload]
  have hreqNeg :
      evalExpr? config { contract := contract, locals := locals' } evm
        (eitherExpr (.binary .ge (.var "dart") (.intLit 0))
          (.binary .le (.var "dstArtNew")
            (.storage (urnsF (.var "ilk") (.var "dst") "art")))) =
        .ok (.bool true) :=
    evalSignedAddGuardNeg_true hdartAfter hdstArtNewEval hstorageAfter hguardNeg
  have hreqPos :
      evalExpr? config { contract := contract, locals := locals' } evm
        (eitherExpr (.binary .le (.var "dart") (.intLit 0))
          (.binary .ge (.var "dstArtNew")
            (.storage (urnsF (.var "ilk") (.var "dst") "art")))) =
        .ok (.bool true) :=
    evalSignedAddGuardPos_true hdartAfter hdstArtNewEval hstorageAfter hguardPos
  have hassign :
      assignStorageRef? config { contract := contract, locals := locals' } evm .storage
        (urnsF (.var "ilk") (.var "dst") "art") (.int (Int.ofNat dstArtNew.toNat)) =
        .ok ({ contract := contract, locals := locals' }, evm') := by
    have hilk' : locals'.get? "ilk" = some (forkIlkValue I) := by
      change (locals.insert "dstArtNew" (.int (Int.ofNat dstArtNew.toNat))).get? "ilk" =
        some (forkIlkValue I)
      rw [store_get_ne _ _ (by native_decide), hilk]
    have hdst' : locals'.get? "dst" = some (forkDstValue I) := by
      change (locals.insert "dstArtNew" (.int (Int.ofNat dstArtNew.toNat))).get? "dst" =
        some (forkDstValue I)
      rw [store_get_ne _ _ (by native_decide), hdst]
    have hbase' : locals'.get? "urns" = none := by
      change (locals.insert "dstArtNew" (.int (Int.ofNat dstArtNew.toNat))).get? "urns" =
        none
      rw [store_get_ne _ _ (by native_decide), hbase]
    simpa [evm'] using
      assignStorageRef_fork_dst_art evm I locals' dstArtNew hsz164 hilk' hdst' hbase'
  change ExecBlock config { contract := contract, locals := locals } evm
    [ .letDecl "dstArtNew" (some uint256)
        (wordWrap256
          (.binary .add (.storage (urnsF (.var "ilk") (.var "dst") "art")) (.var "dart"))),
      .require
        (eitherExpr (.binary .ge (.var "dart") (.intLit 0))
          (.binary .le (.var "dstArtNew")
            (.storage (urnsF (.var "ilk") (.var "dst") "art")))),
      .require
        (eitherExpr (.binary .le (.var "dart") (.intLit 0))
          (.binary .ge (.var "dstArtNew")
            (.storage (urnsF (.var "ilk") (.var "dst") "art")))),
      .assign .storage (urnsF (.var "ilk") (.var "dst") "art") (.var "dstArtNew") ]
    (.ok { contract := contract, locals := locals' } evm')
  refine ExecBlock.consNormal (ExecStmt.letDecl hlet) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue hreqNeg) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue hreqPos) ?_
  exact ExecBlock.consNormal (ExecStmt.assign hdstArtNewEval hassign) ExecBlock.nil

theorem execForkDstArtUpdateRevertGuardNeg {evm : EVM.State} {I : ExecutionEnv}
    (locals : Store) (dstArtOld dstArtNew : UInt256)
    (hsz164 : 164 ≤ I.calldata.size)
    (hilk : locals.get? "ilk" = some (forkIlkValue I))
    (hdst : locals.get? "dst" = some (forkDstValue I))
    (hdart : locals.get? "dart" = some (forkDartValue I))
    (hbase : locals.get? "urns" = none)
    (hload :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (forkDstArtSlot I) = dstArtOld)
    (hnew : dstArtNew = forkDartWord I + dstArtOld)
    (hfail :
      ¬ (UInt256.slt (forkDartWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.gt dstArtNew dstArtOld = ⟨0⟩)) :
    ExecBlock config { contract := contract, locals := locals } evm
      (checkedAddSignedInto "dstArtNew"
        (.storage (urnsF (.var "ilk") (.var "dst") "art")) (.var "dart") ++
        [ .assign .storage (urnsF (.var "ilk") (.var "dst") "art") (.var "dstArtNew") ])
      .reverted := by
  let locals' := locals.insert "dstArtNew" (.int (Int.ofNat dstArtNew.toNat))
  have hstorage :
      evalExpr? config { contract := contract, locals := locals } evm
        (.storage (urnsF (.var "ilk") (.var "dst") "art")) =
        .ok (.int (Int.ofNat dstArtOld.toNat)) := by
    rw [evalExpr_fork_dst_art_locals locals hsz164 hilk hdst hbase, hload]
  have hdartEval :
      evalExpr? config { contract := contract, locals := locals } evm (.var "dart") =
        .ok (.int (forkDartInt I)) :=
    vatEvalExpr_varInt (by simpa [forkDartValue] using hdart)
  have hdartAfter :
      evalExpr? config { contract := contract, locals := locals' } evm (.var "dart") =
        .ok (.int (forkDartInt I)) := by
    exact vatEvalExpr_varInt (by
      change (locals.insert "dstArtNew" (.int (Int.ofNat dstArtNew.toNat))).get? "dart" =
        some (.int (forkDartInt I))
      rw [store_get_ne _ _ (by native_decide)]
      simpa [forkDartValue] using hdart)
  have hstorageAfter :
      evalExpr? config { contract := contract, locals := locals' } evm
        (.storage (urnsF (.var "ilk") (.var "dst") "art")) =
        .ok (.int (Int.ofNat dstArtOld.toNat)) := by
    have hilk' : locals'.get? "ilk" = some (forkIlkValue I) := by
      change (locals.insert "dstArtNew" (.int (Int.ofNat dstArtNew.toNat))).get? "ilk" =
        some (forkIlkValue I)
      rw [store_get_ne _ _ (by native_decide), hilk]
    have hdst' : locals'.get? "dst" = some (forkDstValue I) := by
      change (locals.insert "dstArtNew" (.int (Int.ofNat dstArtNew.toNat))).get? "dst" =
        some (forkDstValue I)
      rw [store_get_ne _ _ (by native_decide), hdst]
    have hbase' : locals'.get? "urns" = none := by
      change (locals.insert "dstArtNew" (.int (Int.ofNat dstArtNew.toNat))).get? "urns" =
        none
      rw [store_get_ne _ _ (by native_decide), hbase]
    rw [evalExpr_fork_dst_art_locals locals' hsz164 hilk' hdst' hbase', hload]
  have hadd :
      ExecBlock config { contract := contract, locals := locals } evm
        (checkedAddSignedInto "dstArtNew"
          (.storage (urnsF (.var "ilk") (.var "dst") "art")) (.var "dart"))
        .reverted :=
    execForkCheckedAddSignedRevertGuardNeg
      (x := .storage (urnsF (.var "ilk") (.var "dst") "art")) (y := .var "dart")
      (name := "dstArtNew") hstorage hdartEval (forkDartInt_mod_word I) hnew
      (by simpa [locals'] using hdartAfter)
      (by simpa [locals'] using hstorageAfter)
      (forkDartAddGuardNegFailCond hfail)
  exact execBlock_append_term hadd (by intro f e h; cases h)

theorem execForkDstArtUpdateRevertGuardPos {evm : EVM.State} {I : ExecutionEnv}
    (locals : Store) (dstArtOld dstArtNew : UInt256)
    (hsz164 : 164 ≤ I.calldata.size)
    (hilk : locals.get? "ilk" = some (forkIlkValue I))
    (hdst : locals.get? "dst" = some (forkDstValue I))
    (hdart : locals.get? "dart" = some (forkDartValue I))
    (hbase : locals.get? "urns" = none)
    (hload :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (forkDstArtSlot I) = dstArtOld)
    (hnew : dstArtNew = forkDartWord I + dstArtOld)
    (hguardNeg :
      UInt256.slt (forkDartWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.gt dstArtNew dstArtOld = ⟨0⟩)
    (hfail :
      ¬ (UInt256.sgt (forkDartWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.lt dstArtNew dstArtOld = ⟨0⟩)) :
    ExecBlock config { contract := contract, locals := locals } evm
      (checkedAddSignedInto "dstArtNew"
        (.storage (urnsF (.var "ilk") (.var "dst") "art")) (.var "dart") ++
        [ .assign .storage (urnsF (.var "ilk") (.var "dst") "art") (.var "dstArtNew") ])
      .reverted := by
  let locals' := locals.insert "dstArtNew" (.int (Int.ofNat dstArtNew.toNat))
  have hstorage :
      evalExpr? config { contract := contract, locals := locals } evm
        (.storage (urnsF (.var "ilk") (.var "dst") "art")) =
        .ok (.int (Int.ofNat dstArtOld.toNat)) := by
    rw [evalExpr_fork_dst_art_locals locals hsz164 hilk hdst hbase, hload]
  have hdartEval :
      evalExpr? config { contract := contract, locals := locals } evm (.var "dart") =
        .ok (.int (forkDartInt I)) :=
    vatEvalExpr_varInt (by simpa [forkDartValue] using hdart)
  have hnewEval :
      evalExpr? config { contract := contract, locals := locals' } evm (.var "dstArtNew") =
        .ok (.int (Int.ofNat dstArtNew.toNat)) := by
    exact vatEvalExpr_varUInt256 (by simp [locals'])
  have hdartAfter :
      evalExpr? config { contract := contract, locals := locals' } evm (.var "dart") =
        .ok (.int (forkDartInt I)) := by
    exact vatEvalExpr_varInt (by
      change (locals.insert "dstArtNew" (.int (Int.ofNat dstArtNew.toNat))).get? "dart" =
        some (.int (forkDartInt I))
      rw [store_get_ne _ _ (by native_decide)]
      simpa [forkDartValue] using hdart)
  have hstorageAfter :
      evalExpr? config { contract := contract, locals := locals' } evm
        (.storage (urnsF (.var "ilk") (.var "dst") "art")) =
        .ok (.int (Int.ofNat dstArtOld.toNat)) := by
    have hilk' : locals'.get? "ilk" = some (forkIlkValue I) := by
      change (locals.insert "dstArtNew" (.int (Int.ofNat dstArtNew.toNat))).get? "ilk" =
        some (forkIlkValue I)
      rw [store_get_ne _ _ (by native_decide), hilk]
    have hdst' : locals'.get? "dst" = some (forkDstValue I) := by
      change (locals.insert "dstArtNew" (.int (Int.ofNat dstArtNew.toNat))).get? "dst" =
        some (forkDstValue I)
      rw [store_get_ne _ _ (by native_decide), hdst]
    have hbase' : locals'.get? "urns" = none := by
      change (locals.insert "dstArtNew" (.int (Int.ofNat dstArtNew.toNat))).get? "urns" =
        none
      rw [store_get_ne _ _ (by native_decide), hbase]
    rw [evalExpr_fork_dst_art_locals locals' hsz164 hilk' hdst' hbase', hload]
  have hguardNegEval :
      evalExpr? config { contract := contract, locals := locals' } evm
        (eitherExpr (.binary .ge (.var "dart") (.intLit 0))
          (.binary .le (.var "dstArtNew")
            (.storage (urnsF (.var "ilk") (.var "dst") "art")))) =
        .ok (.bool true) :=
    evalSignedAddGuardNeg_true hdartAfter hnewEval hstorageAfter
      (forkDartAddGuardNegCond hguardNeg)
  have hadd :
      ExecBlock config { contract := contract, locals := locals } evm
        (checkedAddSignedInto "dstArtNew"
          (.storage (urnsF (.var "ilk") (.var "dst") "art")) (.var "dart"))
        .reverted :=
    execForkCheckedAddSignedRevertGuardPos
      (x := .storage (urnsF (.var "ilk") (.var "dst") "art")) (y := .var "dart")
      (name := "dstArtNew") hstorage hdartEval (forkDartInt_mod_word I) hnew
      (by simpa [locals'] using hdartAfter)
      (by simpa [locals'] using hstorageAfter)
      (by simpa [locals'] using hguardNegEval)
      (forkDartAddGuardPosFailCond hfail)
  exact execBlock_append_term hadd (by intro f e h; cases h)

theorem execForkFinalLoadsOk {evm : EVM.State} {I : ExecutionEnv}
    (srcInkNew srcArtNew dstInkNew dstArtNew
      srcArtFinal dstArtFinal srcInkFinal dstInkFinal : UInt256)
    (hsz164 : 164 ≤ I.calldata.size)
    (hloadSrcArt :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (forkSrcArtSlot I) =
        srcArtFinal)
    (hloadDstArt :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (forkDstArtSlot I) =
        dstArtFinal)
    (hloadSrcInk :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (forkSrcInkSlot I) =
        srcInkFinal)
    (hloadDstInk :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (forkDstInkSlot I) =
        dstInkFinal) :
    ExecBlock config
      { contract := contract,
        locals := forkStoreDstArtNew I srcInkNew srcArtNew dstInkNew dstArtNew } evm
      [ .letDecl "srcArtFinal" (some uint256)
          (.storage (urnsF (.var "ilk") (.var "src") "art")),
        .letDecl "dstArtFinal" (some uint256)
          (.storage (urnsF (.var "ilk") (.var "dst") "art")),
        .letDecl "srcInkFinal" (some uint256)
          (.storage (urnsF (.var "ilk") (.var "src") "ink")),
        .letDecl "dstInkFinal" (some uint256)
          (.storage (urnsF (.var "ilk") (.var "dst") "ink")) ]
      (.ok
        { contract := contract,
          locals := forkStoreFinalLoads I srcInkNew srcArtNew dstInkNew dstArtNew
            srcArtFinal dstArtFinal srcInkFinal dstInkFinal } evm) := by
  let locals0 := forkStoreDstArtNew I srcInkNew srcArtNew dstInkNew dstArtNew
  let locals1 := locals0.insert "srcArtFinal" (.int (Int.ofNat srcArtFinal.toNat))
  let locals2 := locals1.insert "dstArtFinal" (.int (Int.ofNat dstArtFinal.toNat))
  let locals3 := locals2.insert "srcInkFinal" (.int (Int.ofNat srcInkFinal.toNat))
  let locals4 := locals3.insert "dstInkFinal" (.int (Int.ofNat dstInkFinal.toNat))
  have hsrcArtEval :
      evalExpr? config { contract := contract, locals := locals0 } evm
        (.storage (urnsF (.var "ilk") (.var "src") "art")) =
        .ok (.int (Int.ofNat srcArtFinal.toNat)) := by
    rw [evalExpr_fork_src_art_locals locals0 hsz164
      (by simpa [locals0] using
        forkStoreDstArtNew_get_ilk I srcInkNew srcArtNew dstInkNew dstArtNew)
      (by simpa [locals0] using
        forkStoreDstArtNew_get_src I srcInkNew srcArtNew dstInkNew dstArtNew)
      (by simpa [locals0] using
        forkStoreDstArtNew_get_urns I srcInkNew srcArtNew dstInkNew dstArtNew)]
    rw [hloadSrcArt]
  have hdstArtEval :
      evalExpr? config { contract := contract, locals := locals1 } evm
        (.storage (urnsF (.var "ilk") (.var "dst") "art")) =
        .ok (.int (Int.ofNat dstArtFinal.toNat)) := by
    rw [evalExpr_fork_dst_art_locals locals1 hsz164
      (by
        change (locals0.insert "srcArtFinal"
          (.int (Int.ofNat srcArtFinal.toNat))).get? "ilk" = some (forkIlkValue I)
        rw [store_get_ne _ _ (by native_decide)]
        simpa [locals0] using
          forkStoreDstArtNew_get_ilk I srcInkNew srcArtNew dstInkNew dstArtNew)
      (by
        change (locals0.insert "srcArtFinal"
          (.int (Int.ofNat srcArtFinal.toNat))).get? "dst" = some (forkDstValue I)
        rw [store_get_ne _ _ (by native_decide)]
        simpa [locals0] using
          forkStoreDstArtNew_get_dst I srcInkNew srcArtNew dstInkNew dstArtNew)
      (by
        change (locals0.insert "srcArtFinal"
          (.int (Int.ofNat srcArtFinal.toNat))).get? "urns" = none
        rw [store_get_ne _ _ (by native_decide)]
        simpa [locals0] using
          forkStoreDstArtNew_get_urns I srcInkNew srcArtNew dstInkNew dstArtNew)]
    rw [hloadDstArt]
  have hsrcInkEval :
      evalExpr? config { contract := contract, locals := locals2 } evm
        (.storage (urnsF (.var "ilk") (.var "src") "ink")) =
        .ok (.int (Int.ofNat srcInkFinal.toNat)) := by
    rw [evalExpr_fork_src_ink_locals locals2 hsz164
      (by
        change ((locals0.insert "srcArtFinal"
          (.int (Int.ofNat srcArtFinal.toNat))).insert "dstArtFinal"
          (.int (Int.ofNat dstArtFinal.toNat))).get? "ilk" = some (forkIlkValue I)
        rw [store_get_ne _ _ (by native_decide)]
        rw [store_get_ne _ _ (by native_decide)]
        simpa [locals0] using
          forkStoreDstArtNew_get_ilk I srcInkNew srcArtNew dstInkNew dstArtNew)
      (by
        change ((locals0.insert "srcArtFinal"
          (.int (Int.ofNat srcArtFinal.toNat))).insert "dstArtFinal"
          (.int (Int.ofNat dstArtFinal.toNat))).get? "src" = some (forkSrcValue I)
        rw [store_get_ne _ _ (by native_decide)]
        rw [store_get_ne _ _ (by native_decide)]
        simpa [locals0] using
          forkStoreDstArtNew_get_src I srcInkNew srcArtNew dstInkNew dstArtNew)
      (by
        change ((locals0.insert "srcArtFinal"
          (.int (Int.ofNat srcArtFinal.toNat))).insert "dstArtFinal"
          (.int (Int.ofNat dstArtFinal.toNat))).get? "urns" = none
        rw [store_get_ne _ _ (by native_decide)]
        rw [store_get_ne _ _ (by native_decide)]
        simpa [locals0] using
          forkStoreDstArtNew_get_urns I srcInkNew srcArtNew dstInkNew dstArtNew)]
    rw [hloadSrcInk]
  have hdstInkEval :
      evalExpr? config { contract := contract, locals := locals3 } evm
        (.storage (urnsF (.var "ilk") (.var "dst") "ink")) =
        .ok (.int (Int.ofNat dstInkFinal.toNat)) := by
    rw [evalExpr_fork_dst_ink_locals locals3 hsz164
      (by
        change (((locals0.insert "srcArtFinal"
          (.int (Int.ofNat srcArtFinal.toNat))).insert "dstArtFinal"
          (.int (Int.ofNat dstArtFinal.toNat))).insert "srcInkFinal"
          (.int (Int.ofNat srcInkFinal.toNat))).get? "ilk" = some (forkIlkValue I)
        rw [store_get_ne _ _ (by native_decide)]
        rw [store_get_ne _ _ (by native_decide)]
        rw [store_get_ne _ _ (by native_decide)]
        simpa [locals0] using
          forkStoreDstArtNew_get_ilk I srcInkNew srcArtNew dstInkNew dstArtNew)
      (by
        change (((locals0.insert "srcArtFinal"
          (.int (Int.ofNat srcArtFinal.toNat))).insert "dstArtFinal"
          (.int (Int.ofNat dstArtFinal.toNat))).insert "srcInkFinal"
          (.int (Int.ofNat srcInkFinal.toNat))).get? "dst" = some (forkDstValue I)
        rw [store_get_ne _ _ (by native_decide)]
        rw [store_get_ne _ _ (by native_decide)]
        rw [store_get_ne _ _ (by native_decide)]
        simpa [locals0] using
          forkStoreDstArtNew_get_dst I srcInkNew srcArtNew dstInkNew dstArtNew)
      (by
        change (((locals0.insert "srcArtFinal"
          (.int (Int.ofNat srcArtFinal.toNat))).insert "dstArtFinal"
          (.int (Int.ofNat dstArtFinal.toNat))).insert "srcInkFinal"
          (.int (Int.ofNat srcInkFinal.toNat))).get? "urns" = none
        rw [store_get_ne _ _ (by native_decide)]
        rw [store_get_ne _ _ (by native_decide)]
        rw [store_get_ne _ _ (by native_decide)]
        simpa [locals0] using
          forkStoreDstArtNew_get_urns I srcInkNew srcArtNew dstInkNew dstArtNew)]
    rw [hloadDstInk]
  change ExecBlock config { contract := contract, locals := locals0 } evm
    [ .letDecl "srcArtFinal" (some uint256)
        (.storage (urnsF (.var "ilk") (.var "src") "art")),
      .letDecl "dstArtFinal" (some uint256)
        (.storage (urnsF (.var "ilk") (.var "dst") "art")),
      .letDecl "srcInkFinal" (some uint256)
        (.storage (urnsF (.var "ilk") (.var "src") "ink")),
      .letDecl "dstInkFinal" (some uint256)
        (.storage (urnsF (.var "ilk") (.var "dst") "ink")) ]
    (.ok { contract := contract, locals := locals4 } evm)
  refine ExecBlock.consNormal (ExecStmt.letDecl hsrcArtEval) ?_
  refine ExecBlock.consNormal (ExecStmt.letDecl hdstArtEval) ?_
  refine ExecBlock.consNormal (ExecStmt.letDecl hsrcInkEval) ?_
  exact ExecBlock.consNormal (ExecStmt.letDecl hdstInkEval) ExecBlock.nil

theorem evalExpr_fork_mul256_ok {evm : EVM.State} {locals : Store}
    {x y : Expr} {a b prod : UInt256}
    (hx : evalExpr? config { contract := contract, locals := locals } evm x =
      .ok (.int (Int.ofNat a.toNat)))
    (hy : evalExpr? config { contract := contract, locals := locals } evm y =
      .ok (.int (Int.ofNat b.toNat)))
    (hprod : prod = UInt256.mul a b)
    (hfit : a.toNat * b.toNat < UInt256.size) :
    evalExpr? config { contract := contract, locals := locals } evm (mul256 x y) =
      .ok (.int (Int.ofNat prod.toNat)) := by
  have hlt : ¬ Int.ofNat (a.toNat * b.toNat) ≥ (2 : Int) ^ 256 :=
    not_le.mpr (Int.ofNat_lt.mpr (by simpa [UInt256.size] using hfit))
  have hword : prod.toNat = a.toNat * b.toNat := by
    rw [hprod, u256_mul_toNat, Nat.mod_eq_of_lt hfit]
  simp [mul256, u256, evalExpr?, EvalResult.bind, bind, hx, hy, evalBinaryOp?,
    uint256Int, hword]
  rw [if_neg]
  · rfl
  · intro hbad
    rcases hbad with hbad | hbad
    · exact (not_lt.mpr (Int.natCast_nonneg _)) hbad
    · exact hlt hbad

theorem forkUintCheckedMulFail_to_overflow {a b : UInt256}
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

theorem forkUintCheckedMulGuard_to_fit_and_source_guard {a b : UInt256}
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

theorem evalExpr_fork_mul256_revert {evm : EVM.State} {locals : Store}
    {x y : Expr} {a b : UInt256}
    (hx : evalExpr? config { contract := contract, locals := locals } evm x =
      .ok (.int (Int.ofNat a.toNat)))
    (hy : evalExpr? config { contract := contract, locals := locals } evm y =
      .ok (.int (Int.ofNat b.toNat)))
    (hover : UInt256.size ≤ a.toNat * b.toNat) :
    evalExpr? config { contract := contract, locals := locals } evm (mul256 x y) =
      .revert := by
  have hhi : Int.ofNat (a.toNat * b.toNat) ≥ (2 : Int) ^ 256 := by
    have hcast : (UInt256.size : Int) ≤ (a.toNat * b.toNat : Int) := by
      exact_mod_cast hover
    simpa [UInt256.size] using hcast
  simp [mul256, u256, evalExpr?, EvalResult.bind, bind, hx, hy, evalBinaryOp?,
    uint256Int]
  intro _
  exact hhi

theorem evalExpr_fork_mul_guard_true {evm : EVM.State} {locals : Store}
    {x y : Expr} {name : Ident} {a b prod : UInt256}
    (hx : evalExpr? config { contract := contract, locals := locals } evm x =
      .ok (.int (Int.ofNat a.toNat)))
    (hy : evalExpr? config { contract := contract, locals := locals } evm y =
      .ok (.int (Int.ofNat b.toNat)))
    (hname : evalExpr? config { contract := contract, locals := locals } evm (.var name) =
      .ok (.int (Int.ofNat prod.toNat)))
    (hcond : b.toNat = 0 ∨ prod.toNat / b.toNat = a.toNat) :
    evalExpr? config { contract := contract, locals := locals } evm
      (eitherExpr (.binary .eq y (.intLit 0))
        (.binary .eq (.binary .div (.var name) y) x)) =
      .ok (.bool true) := by
  by_cases hzero : b.toNat = 0
  · have hleft :
        evalExpr? config { contract := contract, locals := locals } evm
          (.binary .eq y (.intLit 0)) = .ok (.bool true) := by
      simp [evalExpr?, EvalResult.bind, bind, hy, evalBinaryOp?, hzero]
    exact vatEvalExpr_or_true_left hleft
  · have hdiv : prod.toNat / b.toNat = a.toNat := by
      rcases hcond with hcond | hcond
      · exact False.elim (hzero hcond)
      · exact hcond
    have hbneInt : (Int.ofNat b.toNat) ≠ 0 := by
      intro hbad
      exact hzero (Int.ofNat_eq_zero.mp hbad)
    have hdivInt : (Int.ofNat prod.toNat) / (Int.ofNat b.toNat) =
        Int.ofNat a.toNat := by
      simpa [Int.natCast_ediv] using congrArg Int.ofNat hdiv
    have hleft :
        evalExpr? config { contract := contract, locals := locals } evm
          (.binary .eq y (.intLit 0)) = .ok (.bool false) := by
      simp [evalExpr?, EvalResult.bind, bind, hy, evalBinaryOp?, hzero]
    have hright :
        evalExpr? config { contract := contract, locals := locals } evm
          (.binary .eq (.binary .div (.var name) y) x) = .ok (.bool true) := by
      simp [evalExpr?, EvalResult.bind, bind, hname, hy, hx, evalBinaryOp?,
        hzero]
      exact hdivInt
    exact vatEvalExpr_or_false_right hleft hright

theorem execForkMulUintIntoRevertOfOverflow {evm : EVM.State} {locals : Store}
    (name : Ident) (x y : Expr) (a b : UInt256)
    (hx : evalExpr? config { contract := contract, locals := locals } evm x =
      .ok (.int (Int.ofNat a.toNat)))
    (hy : evalExpr? config { contract := contract, locals := locals } evm y =
      .ok (.int (Int.ofNat b.toNat)))
    (hover : UInt256.size ≤ a.toNat * b.toNat) :
    ExecBlock config { contract := contract, locals := locals } evm
      (checkedMulUintInto name x y) .reverted := by
  have hlet : evalExpr? config { contract := contract, locals := locals } evm
      (mul256 x y) = .revert :=
    evalExpr_fork_mul256_revert hx hy hover
  change ExecBlock config { contract := contract, locals := locals } evm
    [ .letDecl name (some uint256) (mul256 x y),
      .require
        (eitherExpr (.binary .eq y (.intLit 0))
          (.binary .eq (.binary .div (.var name) y) x)) ] .reverted
  exact ExecBlock.consRevert (ExecStmt.letDeclRevert hlet)

theorem execForkMulUintIntoOk {evm : EVM.State} {locals : Store}
    (name : Ident) (x y : Expr) (a b prod : UInt256)
    (hx : evalExpr? config { contract := contract, locals := locals } evm x =
      .ok (.int (Int.ofNat a.toNat)))
    (hy : evalExpr? config { contract := contract, locals := locals } evm y =
      .ok (.int (Int.ofNat b.toNat)))
    (hprod : prod = UInt256.mul a b)
    (hfit : a.toNat * b.toNat < UInt256.size)
    (hguard :
      evalExpr? config
        { contract := contract, locals := locals.insert name (.int (Int.ofNat prod.toNat)) } evm
        (eitherExpr (.binary .eq y (.intLit 0))
          (.binary .eq (.binary .div (.var name) y) x)) =
        .ok (.bool true)) :
    ExecBlock config { contract := contract, locals := locals } evm
      (checkedMulUintInto name x y)
      (.ok { contract := contract, locals := locals.insert name (.int (Int.ofNat prod.toNat)) }
        evm) := by
  have hlet :
      evalExpr? config { contract := contract, locals := locals } evm (mul256 x y) =
        .ok (.int (Int.ofNat prod.toNat)) :=
    evalExpr_fork_mul256_ok hx hy hprod hfit
  change ExecBlock config { contract := contract, locals := locals } evm
    [ .letDecl name (some uint256) (mul256 x y),
      .require
        (eitherExpr (.binary .eq y (.intLit 0))
          (.binary .eq (.binary .div (.var name) y) x)) ]
    (.ok { contract := contract, locals := locals.insert name (.int (Int.ofNat prod.toNat)) }
      evm)
  refine ExecBlock.consNormal (ExecStmt.letDecl hlet) ?_
  exact ExecBlock.consNormal (ExecStmt.requireTrue hguard) ExecBlock.nil

set_option maxHeartbeats 0 in
theorem execForkUtabFinalMulOk {evm : EVM.State} {I : ExecutionEnv}
    (srcInkNew srcArtNew dstInkNew dstArtNew
      srcArtFinal dstArtFinal srcInkFinal dstInkFinal rate utab : UInt256)
    (hsz164 : 164 ≤ I.calldata.size)
    (hloadRate :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (forkIlkRateSlot I) = rate)
    (hprod : utab = UInt256.mul srcArtFinal rate)
    (hfit : srcArtFinal.toNat * rate.toNat < UInt256.size)
    (hguard : rate.toNat = 0 ∨ utab.toNat / rate.toNat = srcArtFinal.toNat) :
    ExecBlock config
      { contract := contract,
        locals := forkStoreFinalLoads I srcInkNew srcArtNew dstInkNew dstArtNew
          srcArtFinal dstArtFinal srcInkFinal dstInkFinal } evm
      (checkedMulUintInto "utab" (.var "srcArtFinal")
        (.storage (ilksF (.var "ilk") "rate")))
      (.ok
        { contract := contract,
          locals := forkStoreUtabFinal I srcInkNew srcArtNew dstInkNew dstArtNew
            srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab } evm) := by
  let locals := forkStoreFinalLoads I srcInkNew srcArtNew dstInkNew dstArtNew
    srcArtFinal dstArtFinal srcInkFinal dstInkFinal
  have hx :
      evalExpr? config { contract := contract, locals := locals } evm (.var "srcArtFinal") =
        .ok (.int (Int.ofNat srcArtFinal.toNat)) := by
    exact vatEvalExpr_varUInt256 (by
      change (forkStoreFinalLoads I srcInkNew srcArtNew dstInkNew dstArtNew
        srcArtFinal dstArtFinal srcInkFinal dstInkFinal).get? "srcArtFinal" =
        some (.int (Int.ofNat srcArtFinal.toNat))
      exact forkStoreFinalLoads_get_srcArtFinal I srcInkNew srcArtNew dstInkNew dstArtNew
        srcArtFinal dstArtFinal srcInkFinal dstInkFinal)
  have hy :
      evalExpr? config { contract := contract, locals := locals } evm
        (.storage (ilksF (.var "ilk") "rate")) =
        .ok (.int (Int.ofNat rate.toNat)) := by
    rw [evalExpr_fork_ilk_rate_locals locals hsz164
      (by
        change (forkStoreFinalLoads I srcInkNew srcArtNew dstInkNew dstArtNew
          srcArtFinal dstArtFinal srcInkFinal dstInkFinal).get? "ilk" =
          some (forkIlkValue I)
        exact forkStoreFinalLoads_get_ilk I srcInkNew srcArtNew dstInkNew dstArtNew
          srcArtFinal dstArtFinal srcInkFinal dstInkFinal)
      (by
        change (forkStoreFinalLoads I srcInkNew srcArtNew dstInkNew dstArtNew
          srcArtFinal dstArtFinal srcInkFinal dstInkFinal).get? "ilks" = none
        exact forkStoreFinalLoads_get_ilks I srcInkNew srcArtNew dstInkNew dstArtNew
          srcArtFinal dstArtFinal srcInkFinal dstInkFinal)]
    rw [hloadRate]
  have hx' :
      evalExpr? config
        { contract := contract, locals := locals.insert "utab" (.int (Int.ofNat utab.toNat)) }
        evm (.var "srcArtFinal") =
        .ok (.int (Int.ofNat srcArtFinal.toNat)) := by
    exact vatEvalExpr_varUInt256 (by
      change ((forkStoreFinalLoads I srcInkNew srcArtNew dstInkNew dstArtNew
        srcArtFinal dstArtFinal srcInkFinal dstInkFinal).insert "utab"
        (.int (Int.ofNat utab.toNat))).get? "srcArtFinal" =
        some (.int (Int.ofNat srcArtFinal.toNat))
      rw [store_get_ne _ _ (by native_decide), forkStoreFinalLoads_get_srcArtFinal])
  have hy' :
      evalExpr? config
        { contract := contract, locals := locals.insert "utab" (.int (Int.ofNat utab.toNat)) }
        evm (.storage (ilksF (.var "ilk") "rate")) =
        .ok (.int (Int.ofNat rate.toNat)) := by
    rw [evalExpr_fork_ilk_rate_locals
      (locals.insert "utab" (.int (Int.ofNat utab.toNat))) hsz164
      (by
        change ((forkStoreFinalLoads I srcInkNew srcArtNew dstInkNew dstArtNew
          srcArtFinal dstArtFinal srcInkFinal dstInkFinal).insert "utab"
          (.int (Int.ofNat utab.toNat))).get? "ilk" = some (forkIlkValue I)
        rw [store_get_ne _ _ (by native_decide), forkStoreFinalLoads_get_ilk])
      (by
        change ((forkStoreFinalLoads I srcInkNew srcArtNew dstInkNew dstArtNew
          srcArtFinal dstArtFinal srcInkFinal dstInkFinal).insert "utab"
          (.int (Int.ofNat utab.toNat))).get? "ilks" = none
        rw [store_get_ne _ _ (by native_decide), forkStoreFinalLoads_get_ilks])]
    rw [hloadRate]
  have hname :
      evalExpr? config
        { contract := contract, locals := locals.insert "utab" (.int (Int.ofNat utab.toNat)) }
        evm (.var "utab") = .ok (.int (Int.ofNat utab.toNat)) :=
    vatEvalExpr_varUInt256 (by simp)
  have hguardEval :
      evalExpr? config
        { contract := contract, locals := locals.insert "utab" (.int (Int.ofNat utab.toNat)) }
        evm
        (eitherExpr (.binary .eq (.storage (ilksF (.var "ilk") "rate")) (.intLit 0))
          (.binary .eq
            (.binary .div (.var "utab") (.storage (ilksF (.var "ilk") "rate")))
            (.var "srcArtFinal"))) =
        .ok (.bool true) :=
    evalExpr_fork_mul_guard_true hx' hy' hname hguard
  simpa [locals, forkStoreUtabFinal] using
    execForkMulUintIntoOk (evm := evm) (locals := locals)
      "utab" (.var "srcArtFinal") (.storage (ilksF (.var "ilk") "rate"))
      srcArtFinal rate utab hx hy hprod hfit hguardEval

set_option maxHeartbeats 0 in
theorem execForkVtabFinalMulOk {evm : EVM.State} {I : ExecutionEnv}
    (srcInkNew srcArtNew dstInkNew dstArtNew
      srcArtFinal dstArtFinal srcInkFinal dstInkFinal rate utab vtab : UInt256)
    (hsz164 : 164 ≤ I.calldata.size)
    (hloadRate :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (forkIlkRateSlot I) = rate)
    (hprod : vtab = UInt256.mul dstArtFinal rate)
    (hfit : dstArtFinal.toNat * rate.toNat < UInt256.size)
    (hguard : rate.toNat = 0 ∨ vtab.toNat / rate.toNat = dstArtFinal.toNat) :
    ExecBlock config
      { contract := contract,
        locals := forkStoreUtabFinal I srcInkNew srcArtNew dstInkNew dstArtNew
          srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab } evm
      (checkedMulUintInto "vtab" (.var "dstArtFinal")
        (.storage (ilksF (.var "ilk") "rate")))
      (.ok
        { contract := contract,
          locals := forkStoreVtabFinal I srcInkNew srcArtNew dstInkNew dstArtNew
            srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab vtab } evm) := by
  let locals := forkStoreUtabFinal I srcInkNew srcArtNew dstInkNew dstArtNew
    srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab
  have hx :
      evalExpr? config { contract := contract, locals := locals } evm (.var "dstArtFinal") =
        .ok (.int (Int.ofNat dstArtFinal.toNat)) := by
    exact vatEvalExpr_varUInt256 (by
      change (forkStoreUtabFinal I srcInkNew srcArtNew dstInkNew dstArtNew
        srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab).get? "dstArtFinal" =
        some (.int (Int.ofNat dstArtFinal.toNat))
      exact forkStoreUtabFinal_get_dstArtFinal I srcInkNew srcArtNew dstInkNew dstArtNew
        srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab)
  have hy :
      evalExpr? config { contract := contract, locals := locals } evm
        (.storage (ilksF (.var "ilk") "rate")) =
        .ok (.int (Int.ofNat rate.toNat)) := by
    rw [evalExpr_fork_ilk_rate_locals locals hsz164
      (by
        change (forkStoreUtabFinal I srcInkNew srcArtNew dstInkNew dstArtNew
          srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab).get? "ilk" =
          some (forkIlkValue I)
        exact forkStoreUtabFinal_get_ilk I srcInkNew srcArtNew dstInkNew dstArtNew
          srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab)
      (by
        change (forkStoreUtabFinal I srcInkNew srcArtNew dstInkNew dstArtNew
          srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab).get? "ilks" = none
        exact forkStoreUtabFinal_get_ilks I srcInkNew srcArtNew dstInkNew dstArtNew
          srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab)]
    rw [hloadRate]
  have hx' :
      evalExpr? config
        { contract := contract, locals := locals.insert "vtab" (.int (Int.ofNat vtab.toNat)) }
        evm (.var "dstArtFinal") =
        .ok (.int (Int.ofNat dstArtFinal.toNat)) := by
    exact vatEvalExpr_varUInt256 (by
      change ((forkStoreUtabFinal I srcInkNew srcArtNew dstInkNew dstArtNew
        srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab).insert "vtab"
        (.int (Int.ofNat vtab.toNat))).get? "dstArtFinal" =
        some (.int (Int.ofNat dstArtFinal.toNat))
      rw [store_get_ne _ _ (by native_decide), forkStoreUtabFinal_get_dstArtFinal])
  have hy' :
      evalExpr? config
        { contract := contract, locals := locals.insert "vtab" (.int (Int.ofNat vtab.toNat)) }
        evm (.storage (ilksF (.var "ilk") "rate")) =
        .ok (.int (Int.ofNat rate.toNat)) := by
    rw [evalExpr_fork_ilk_rate_locals
      (locals.insert "vtab" (.int (Int.ofNat vtab.toNat))) hsz164
      (by
        change ((forkStoreUtabFinal I srcInkNew srcArtNew dstInkNew dstArtNew
          srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab).insert "vtab"
          (.int (Int.ofNat vtab.toNat))).get? "ilk" = some (forkIlkValue I)
        rw [store_get_ne _ _ (by native_decide), forkStoreUtabFinal_get_ilk])
      (by
        change ((forkStoreUtabFinal I srcInkNew srcArtNew dstInkNew dstArtNew
          srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab).insert "vtab"
          (.int (Int.ofNat vtab.toNat))).get? "ilks" = none
        rw [store_get_ne _ _ (by native_decide), forkStoreUtabFinal_get_ilks])]
    rw [hloadRate]
  have hname :
      evalExpr? config
        { contract := contract, locals := locals.insert "vtab" (.int (Int.ofNat vtab.toNat)) }
        evm (.var "vtab") = .ok (.int (Int.ofNat vtab.toNat)) :=
    vatEvalExpr_varUInt256 (by simp)
  have hguardEval :
      evalExpr? config
        { contract := contract, locals := locals.insert "vtab" (.int (Int.ofNat vtab.toNat)) }
        evm
        (eitherExpr (.binary .eq (.storage (ilksF (.var "ilk") "rate")) (.intLit 0))
          (.binary .eq
            (.binary .div (.var "vtab") (.storage (ilksF (.var "ilk") "rate")))
            (.var "dstArtFinal"))) =
        .ok (.bool true) :=
    evalExpr_fork_mul_guard_true hx' hy' hname hguard
  simpa [locals, forkStoreVtabFinal] using
    execForkMulUintIntoOk (evm := evm) (locals := locals)
      "vtab" (.var "dstArtFinal") (.storage (ilksF (.var "ilk") "rate"))
      dstArtFinal rate vtab hx hy hprod hfit hguardEval

set_option maxHeartbeats 0 in
theorem execForkSrcInkSpotFinalMulOk {evm : EVM.State} {I : ExecutionEnv}
    (srcInkNew srcArtNew dstInkNew dstArtNew
      srcArtFinal dstArtFinal srcInkFinal dstInkFinal spot utab vtab srcInkSpot : UInt256)
    (hsz164 : 164 ≤ I.calldata.size)
    (hloadSpot :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (forkIlkSpotSlot I) = spot)
    (hprod : srcInkSpot = UInt256.mul srcInkFinal spot)
    (hfit : srcInkFinal.toNat * spot.toNat < UInt256.size)
    (hguard : spot.toNat = 0 ∨ srcInkSpot.toNat / spot.toNat = srcInkFinal.toNat) :
    ExecBlock config
      { contract := contract,
        locals := forkStoreVtabFinal I srcInkNew srcArtNew dstInkNew dstArtNew
          srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab vtab } evm
      (checkedMulUintInto "srcInkSpot" (.var "srcInkFinal")
        (.storage (ilksF (.var "ilk") "spot")))
      (.ok
        { contract := contract,
          locals := forkStoreSrcInkSpotFinal I srcInkNew srcArtNew dstInkNew dstArtNew
            srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab vtab srcInkSpot } evm) := by
  let locals := forkStoreVtabFinal I srcInkNew srcArtNew dstInkNew dstArtNew
    srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab vtab
  have hx :
      evalExpr? config { contract := contract, locals := locals } evm (.var "srcInkFinal") =
        .ok (.int (Int.ofNat srcInkFinal.toNat)) := by
    exact vatEvalExpr_varUInt256 (by
      change (forkStoreVtabFinal I srcInkNew srcArtNew dstInkNew dstArtNew
        srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab vtab).get? "srcInkFinal" =
        some (.int (Int.ofNat srcInkFinal.toNat))
      exact forkStoreVtabFinal_get_srcInkFinal I srcInkNew srcArtNew dstInkNew dstArtNew
        srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab vtab)
  have hy :
      evalExpr? config { contract := contract, locals := locals } evm
        (.storage (ilksF (.var "ilk") "spot")) =
        .ok (.int (Int.ofNat spot.toNat)) := by
    rw [evalExpr_fork_ilk_spot_locals locals hsz164
      (by
        change (forkStoreVtabFinal I srcInkNew srcArtNew dstInkNew dstArtNew
          srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab vtab).get? "ilk" =
          some (forkIlkValue I)
        exact forkStoreVtabFinal_get_ilk I srcInkNew srcArtNew dstInkNew dstArtNew
          srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab vtab)
      (by
        change (forkStoreVtabFinal I srcInkNew srcArtNew dstInkNew dstArtNew
          srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab vtab).get? "ilks" = none
        exact forkStoreVtabFinal_get_ilks I srcInkNew srcArtNew dstInkNew dstArtNew
          srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab vtab)]
    rw [hloadSpot]
  have hx' :
      evalExpr? config
        { contract := contract,
          locals := locals.insert "srcInkSpot" (.int (Int.ofNat srcInkSpot.toNat)) }
        evm (.var "srcInkFinal") = .ok (.int (Int.ofNat srcInkFinal.toNat)) := by
    exact vatEvalExpr_varUInt256 (by
      change ((forkStoreVtabFinal I srcInkNew srcArtNew dstInkNew dstArtNew
        srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab vtab).insert "srcInkSpot"
        (.int (Int.ofNat srcInkSpot.toNat))).get? "srcInkFinal" =
        some (.int (Int.ofNat srcInkFinal.toNat))
      rw [store_get_ne _ _ (by native_decide), forkStoreVtabFinal_get_srcInkFinal])
  have hy' :
      evalExpr? config
        { contract := contract,
          locals := locals.insert "srcInkSpot" (.int (Int.ofNat srcInkSpot.toNat)) }
        evm (.storage (ilksF (.var "ilk") "spot")) =
        .ok (.int (Int.ofNat spot.toNat)) := by
    rw [evalExpr_fork_ilk_spot_locals
      (locals.insert "srcInkSpot" (.int (Int.ofNat srcInkSpot.toNat))) hsz164
      (by
        change ((forkStoreVtabFinal I srcInkNew srcArtNew dstInkNew dstArtNew
          srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab vtab).insert "srcInkSpot"
          (.int (Int.ofNat srcInkSpot.toNat))).get? "ilk" = some (forkIlkValue I)
        rw [store_get_ne _ _ (by native_decide), forkStoreVtabFinal_get_ilk])
      (by
        change ((forkStoreVtabFinal I srcInkNew srcArtNew dstInkNew dstArtNew
          srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab vtab).insert "srcInkSpot"
          (.int (Int.ofNat srcInkSpot.toNat))).get? "ilks" = none
        rw [store_get_ne _ _ (by native_decide), forkStoreVtabFinal_get_ilks])]
    rw [hloadSpot]
  have hname :
      evalExpr? config
        { contract := contract,
          locals := locals.insert "srcInkSpot" (.int (Int.ofNat srcInkSpot.toNat)) }
        evm (.var "srcInkSpot") = .ok (.int (Int.ofNat srcInkSpot.toNat)) :=
    vatEvalExpr_varUInt256 (by simp)
  have hguardEval :
      evalExpr? config
        { contract := contract,
          locals := locals.insert "srcInkSpot" (.int (Int.ofNat srcInkSpot.toNat)) }
        evm
        (eitherExpr (.binary .eq (.storage (ilksF (.var "ilk") "spot")) (.intLit 0))
          (.binary .eq
            (.binary .div (.var "srcInkSpot") (.storage (ilksF (.var "ilk") "spot")))
            (.var "srcInkFinal"))) =
        .ok (.bool true) :=
    evalExpr_fork_mul_guard_true hx' hy' hname hguard
  simpa [locals, forkStoreSrcInkSpotFinal] using
    execForkMulUintIntoOk (evm := evm) (locals := locals)
      "srcInkSpot" (.var "srcInkFinal") (.storage (ilksF (.var "ilk") "spot"))
      srcInkFinal spot srcInkSpot hx hy hprod hfit hguardEval

set_option maxHeartbeats 0 in
theorem execForkDstInkSpotFinalMulOk {evm : EVM.State} {I : ExecutionEnv}
    (srcInkNew srcArtNew dstInkNew dstArtNew
      srcArtFinal dstArtFinal srcInkFinal dstInkFinal spot utab vtab srcInkSpot
      dstInkSpot : UInt256)
    (hsz164 : 164 ≤ I.calldata.size)
    (hloadSpot :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (forkIlkSpotSlot I) = spot)
    (hprod : dstInkSpot = UInt256.mul dstInkFinal spot)
    (hfit : dstInkFinal.toNat * spot.toNat < UInt256.size)
    (hguard : spot.toNat = 0 ∨ dstInkSpot.toNat / spot.toNat = dstInkFinal.toNat) :
    ExecBlock config
      { contract := contract,
        locals := forkStoreSrcInkSpotFinal I srcInkNew srcArtNew dstInkNew dstArtNew
          srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab vtab srcInkSpot } evm
      (checkedMulUintInto "dstInkSpot" (.var "dstInkFinal")
        (.storage (ilksF (.var "ilk") "spot")))
      (.ok
        { contract := contract,
          locals := forkStoreDstInkSpotFinal I srcInkNew srcArtNew dstInkNew dstArtNew
            srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab vtab srcInkSpot dstInkSpot } evm) := by
  let locals := forkStoreSrcInkSpotFinal I srcInkNew srcArtNew dstInkNew dstArtNew
    srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab vtab srcInkSpot
  have hx :
      evalExpr? config { contract := contract, locals := locals } evm (.var "dstInkFinal") =
        .ok (.int (Int.ofNat dstInkFinal.toNat)) := by
    exact vatEvalExpr_varUInt256 (by
      change (forkStoreSrcInkSpotFinal I srcInkNew srcArtNew dstInkNew dstArtNew
        srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab vtab srcInkSpot).get?
        "dstInkFinal" = some (.int (Int.ofNat dstInkFinal.toNat))
      exact forkStoreSrcInkSpotFinal_get_dstInkFinal I srcInkNew srcArtNew dstInkNew
        dstArtNew srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab vtab srcInkSpot)
  have hy :
      evalExpr? config { contract := contract, locals := locals } evm
        (.storage (ilksF (.var "ilk") "spot")) =
        .ok (.int (Int.ofNat spot.toNat)) := by
    rw [evalExpr_fork_ilk_spot_locals locals hsz164
      (by
        change (forkStoreSrcInkSpotFinal I srcInkNew srcArtNew dstInkNew dstArtNew
          srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab vtab srcInkSpot).get?
          "ilk" = some (forkIlkValue I)
        exact forkStoreSrcInkSpotFinal_get_ilk I srcInkNew srcArtNew dstInkNew dstArtNew
          srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab vtab srcInkSpot)
      (by
        change (forkStoreSrcInkSpotFinal I srcInkNew srcArtNew dstInkNew dstArtNew
          srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab vtab srcInkSpot).get?
          "ilks" = none
        exact forkStoreSrcInkSpotFinal_get_ilks I srcInkNew srcArtNew dstInkNew dstArtNew
          srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab vtab srcInkSpot)]
    rw [hloadSpot]
  have hx' :
      evalExpr? config
        { contract := contract,
          locals := locals.insert "dstInkSpot" (.int (Int.ofNat dstInkSpot.toNat)) }
        evm (.var "dstInkFinal") = .ok (.int (Int.ofNat dstInkFinal.toNat)) := by
    exact vatEvalExpr_varUInt256 (by
      change ((forkStoreSrcInkSpotFinal I srcInkNew srcArtNew dstInkNew dstArtNew
        srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab vtab srcInkSpot).insert
        "dstInkSpot" (.int (Int.ofNat dstInkSpot.toNat))).get? "dstInkFinal" =
        some (.int (Int.ofNat dstInkFinal.toNat))
      rw [store_get_ne _ _ (by native_decide), forkStoreSrcInkSpotFinal_get_dstInkFinal])
  have hy' :
      evalExpr? config
        { contract := contract,
          locals := locals.insert "dstInkSpot" (.int (Int.ofNat dstInkSpot.toNat)) }
        evm (.storage (ilksF (.var "ilk") "spot")) =
        .ok (.int (Int.ofNat spot.toNat)) := by
    rw [evalExpr_fork_ilk_spot_locals
      (locals.insert "dstInkSpot" (.int (Int.ofNat dstInkSpot.toNat))) hsz164
      (by
        change ((forkStoreSrcInkSpotFinal I srcInkNew srcArtNew dstInkNew dstArtNew
          srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab vtab srcInkSpot).insert
          "dstInkSpot" (.int (Int.ofNat dstInkSpot.toNat))).get? "ilk" =
          some (forkIlkValue I)
        rw [store_get_ne _ _ (by native_decide), forkStoreSrcInkSpotFinal_get_ilk])
      (by
        change ((forkStoreSrcInkSpotFinal I srcInkNew srcArtNew dstInkNew dstArtNew
          srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab vtab srcInkSpot).insert
          "dstInkSpot" (.int (Int.ofNat dstInkSpot.toNat))).get? "ilks" = none
        rw [store_get_ne _ _ (by native_decide), forkStoreSrcInkSpotFinal_get_ilks])]
    rw [hloadSpot]
  have hname :
      evalExpr? config
        { contract := contract,
          locals := locals.insert "dstInkSpot" (.int (Int.ofNat dstInkSpot.toNat)) }
        evm (.var "dstInkSpot") = .ok (.int (Int.ofNat dstInkSpot.toNat)) :=
    vatEvalExpr_varUInt256 (by simp)
  have hguardEval :
      evalExpr? config
        { contract := contract,
          locals := locals.insert "dstInkSpot" (.int (Int.ofNat dstInkSpot.toNat)) }
        evm
        (eitherExpr (.binary .eq (.storage (ilksF (.var "ilk") "spot")) (.intLit 0))
          (.binary .eq
            (.binary .div (.var "dstInkSpot") (.storage (ilksF (.var "ilk") "spot")))
            (.var "dstInkFinal"))) =
        .ok (.bool true) :=
    evalExpr_fork_mul_guard_true hx' hy' hname hguard
  simpa [locals, forkStoreDstInkSpotFinal] using
    execForkMulUintIntoOk (evm := evm) (locals := locals)
      "dstInkSpot" (.var "dstInkFinal") (.storage (ilksF (.var "ilk") "spot"))
      dstInkFinal spot dstInkSpot hx hy hprod hfit hguardEval

theorem execForkUtabMulOk {evm : EVM.State} {I : ExecutionEnv}
    (locals : Store) (srcArt rate utab : UInt256)
    (hsz164 : 164 ≤ I.calldata.size)
    (hilk : locals.get? "ilk" = some (forkIlkValue I))
    (hsrc : locals.get? "src" = some (forkSrcValue I))
    (hurns : locals.get? "urns" = none)
    (hilks : locals.get? "ilks" = none)
    (hloadSrc :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (forkSrcArtSlot I) = srcArt)
    (hloadRate :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (forkIlkRateSlot I) = rate)
    (hprod : utab = UInt256.mul srcArt rate)
    (hfit : srcArt.toNat * rate.toNat < UInt256.size)
    (hguard : rate.toNat = 0 ∨ utab.toNat / rate.toNat = srcArt.toNat) :
    ExecBlock config { contract := contract, locals := locals } evm
      (checkedMulUintInto "utab"
        (.storage (urnsF (.var "ilk") (.var "src") "art"))
        (.storage (ilksF (.var "ilk") "rate")))
      (.ok
        { contract := contract,
          locals := locals.insert "utab" (.int (Int.ofNat utab.toNat)) }
        evm) := by
  let locals' := locals.insert "utab" (.int (Int.ofNat utab.toNat))
  have hsrcArt :
      evalExpr? config { contract := contract, locals := locals } evm
        (.storage (urnsF (.var "ilk") (.var "src") "art")) =
        .ok (.int (Int.ofNat srcArt.toNat)) := by
    rw [evalExpr_fork_src_art_locals locals hsz164 hilk hsrc hurns, hloadSrc]
  have hrate :
      evalExpr? config { contract := contract, locals := locals } evm
        (.storage (ilksF (.var "ilk") "rate")) =
        .ok (.int (Int.ofNat rate.toNat)) := by
    rw [evalExpr_fork_ilk_rate_locals locals hsz164 hilk hilks, hloadRate]
  have hguardEval :
      evalExpr? config { contract := contract, locals := locals' } evm
        (eitherExpr
          (.binary .eq (.storage (ilksF (.var "ilk") "rate")) (.intLit 0))
          (.binary .eq (.binary .div (.var "utab")
            (.storage (ilksF (.var "ilk") "rate")))
            (.storage (urnsF (.var "ilk") (.var "src") "art")))) =
        .ok (.bool true) := by
    have hilk' : locals'.get? "ilk" = some (forkIlkValue I) := by
      change (locals.insert "utab" (.int (Int.ofNat utab.toNat))).get? "ilk" =
        some (forkIlkValue I)
      rw [store_get_ne _ _ (by native_decide), hilk]
    have hsrc' : locals'.get? "src" = some (forkSrcValue I) := by
      change (locals.insert "utab" (.int (Int.ofNat utab.toNat))).get? "src" =
        some (forkSrcValue I)
      rw [store_get_ne _ _ (by native_decide), hsrc]
    have hurns' : locals'.get? "urns" = none := by
      change (locals.insert "utab" (.int (Int.ofNat utab.toNat))).get? "urns" =
        none
      rw [store_get_ne _ _ (by native_decide), hurns]
    have hilks' : locals'.get? "ilks" = none := by
      change (locals.insert "utab" (.int (Int.ofNat utab.toNat))).get? "ilks" =
        none
      rw [store_get_ne _ _ (by native_decide), hilks]
    have hsrcArt' :
        evalExpr? config { contract := contract, locals := locals' } evm
          (.storage (urnsF (.var "ilk") (.var "src") "art")) =
          .ok (.int (Int.ofNat srcArt.toNat)) := by
      rw [evalExpr_fork_src_art_locals locals' hsz164 hilk' hsrc' hurns', hloadSrc]
    have hrate' :
        evalExpr? config { contract := contract, locals := locals' } evm
          (.storage (ilksF (.var "ilk") "rate")) =
          .ok (.int (Int.ofNat rate.toNat)) := by
      rw [evalExpr_fork_ilk_rate_locals locals' hsz164 hilk' hilks', hloadRate]
    have hutab :
        evalExpr? config { contract := contract, locals := locals' } evm (.var "utab") =
          .ok (.int (Int.ofNat utab.toNat)) := by
      exact vatEvalExpr_varUInt256 (by simp [locals'])
    exact evalExpr_fork_mul_guard_true hsrcArt' hrate' hutab hguard
  exact execForkMulUintIntoOk "utab"
    (.storage (urnsF (.var "ilk") (.var "src") "art"))
    (.storage (ilksF (.var "ilk") "rate")) srcArt rate utab
    hsrcArt hrate hprod hfit hguardEval

theorem execForkVtabMulOk {evm : EVM.State} {I : ExecutionEnv}
    (locals : Store) (dstArt rate vtab : UInt256)
    (hsz164 : 164 ≤ I.calldata.size)
    (hilk : locals.get? "ilk" = some (forkIlkValue I))
    (hdst : locals.get? "dst" = some (forkDstValue I))
    (hurns : locals.get? "urns" = none)
    (hilks : locals.get? "ilks" = none)
    (hloadDst :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (forkDstArtSlot I) = dstArt)
    (hloadRate :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (forkIlkRateSlot I) = rate)
    (hprod : vtab = UInt256.mul dstArt rate)
    (hfit : dstArt.toNat * rate.toNat < UInt256.size)
    (hguard : rate.toNat = 0 ∨ vtab.toNat / rate.toNat = dstArt.toNat) :
    ExecBlock config { contract := contract, locals := locals } evm
      (checkedMulUintInto "vtab"
        (.storage (urnsF (.var "ilk") (.var "dst") "art"))
        (.storage (ilksF (.var "ilk") "rate")))
      (.ok
        { contract := contract,
          locals := locals.insert "vtab" (.int (Int.ofNat vtab.toNat)) }
        evm) := by
  let locals' := locals.insert "vtab" (.int (Int.ofNat vtab.toNat))
  have hdstArt :
      evalExpr? config { contract := contract, locals := locals } evm
        (.storage (urnsF (.var "ilk") (.var "dst") "art")) =
        .ok (.int (Int.ofNat dstArt.toNat)) := by
    rw [evalExpr_fork_dst_art_locals locals hsz164 hilk hdst hurns, hloadDst]
  have hrate :
      evalExpr? config { contract := contract, locals := locals } evm
        (.storage (ilksF (.var "ilk") "rate")) =
        .ok (.int (Int.ofNat rate.toNat)) := by
    rw [evalExpr_fork_ilk_rate_locals locals hsz164 hilk hilks, hloadRate]
  have hguardEval :
      evalExpr? config { contract := contract, locals := locals' } evm
        (eitherExpr
          (.binary .eq (.storage (ilksF (.var "ilk") "rate")) (.intLit 0))
          (.binary .eq (.binary .div (.var "vtab")
            (.storage (ilksF (.var "ilk") "rate")))
            (.storage (urnsF (.var "ilk") (.var "dst") "art")))) =
        .ok (.bool true) := by
    have hilk' : locals'.get? "ilk" = some (forkIlkValue I) := by
      change (locals.insert "vtab" (.int (Int.ofNat vtab.toNat))).get? "ilk" =
        some (forkIlkValue I)
      rw [store_get_ne _ _ (by native_decide), hilk]
    have hdst' : locals'.get? "dst" = some (forkDstValue I) := by
      change (locals.insert "vtab" (.int (Int.ofNat vtab.toNat))).get? "dst" =
        some (forkDstValue I)
      rw [store_get_ne _ _ (by native_decide), hdst]
    have hurns' : locals'.get? "urns" = none := by
      change (locals.insert "vtab" (.int (Int.ofNat vtab.toNat))).get? "urns" =
        none
      rw [store_get_ne _ _ (by native_decide), hurns]
    have hilks' : locals'.get? "ilks" = none := by
      change (locals.insert "vtab" (.int (Int.ofNat vtab.toNat))).get? "ilks" =
        none
      rw [store_get_ne _ _ (by native_decide), hilks]
    have hdstArt' :
        evalExpr? config { contract := contract, locals := locals' } evm
          (.storage (urnsF (.var "ilk") (.var "dst") "art")) =
          .ok (.int (Int.ofNat dstArt.toNat)) := by
      rw [evalExpr_fork_dst_art_locals locals' hsz164 hilk' hdst' hurns', hloadDst]
    have hrate' :
        evalExpr? config { contract := contract, locals := locals' } evm
          (.storage (ilksF (.var "ilk") "rate")) =
          .ok (.int (Int.ofNat rate.toNat)) := by
      rw [evalExpr_fork_ilk_rate_locals locals' hsz164 hilk' hilks', hloadRate]
    have hvtab :
        evalExpr? config { contract := contract, locals := locals' } evm (.var "vtab") =
          .ok (.int (Int.ofNat vtab.toNat)) := by
      exact vatEvalExpr_varUInt256 (by simp [locals'])
    exact evalExpr_fork_mul_guard_true hdstArt' hrate' hvtab hguard
  exact execForkMulUintIntoOk "vtab"
    (.storage (urnsF (.var "ilk") (.var "dst") "art"))
    (.storage (ilksF (.var "ilk") "rate")) dstArt rate vtab
    hdstArt hrate hprod hfit hguardEval

theorem execForkSrcInkSpotMulOk {evm : EVM.State} {I : ExecutionEnv}
    (locals : Store) (srcInk spot srcInkSpot : UInt256)
    (hsz164 : 164 ≤ I.calldata.size)
    (hilk : locals.get? "ilk" = some (forkIlkValue I))
    (hsrc : locals.get? "src" = some (forkSrcValue I))
    (hurns : locals.get? "urns" = none)
    (hilks : locals.get? "ilks" = none)
    (hloadSrc :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (forkSrcInkSlot I) = srcInk)
    (hloadSpot :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (forkIlkSpotSlot I) = spot)
    (hprod : srcInkSpot = UInt256.mul srcInk spot)
    (hfit : srcInk.toNat * spot.toNat < UInt256.size)
    (hguard : spot.toNat = 0 ∨ srcInkSpot.toNat / spot.toNat = srcInk.toNat) :
    ExecBlock config { contract := contract, locals := locals } evm
      (checkedMulUintInto "srcInkSpot"
        (.storage (urnsF (.var "ilk") (.var "src") "ink"))
        (.storage (ilksF (.var "ilk") "spot")))
      (.ok
        { contract := contract,
          locals := locals.insert "srcInkSpot" (.int (Int.ofNat srcInkSpot.toNat)) }
        evm) := by
  let locals' := locals.insert "srcInkSpot" (.int (Int.ofNat srcInkSpot.toNat))
  have hsrcInk :
      evalExpr? config { contract := contract, locals := locals } evm
        (.storage (urnsF (.var "ilk") (.var "src") "ink")) =
        .ok (.int (Int.ofNat srcInk.toNat)) := by
    rw [evalExpr_fork_src_ink_locals locals hsz164 hilk hsrc hurns, hloadSrc]
  have hspot :
      evalExpr? config { contract := contract, locals := locals } evm
        (.storage (ilksF (.var "ilk") "spot")) =
        .ok (.int (Int.ofNat spot.toNat)) := by
    rw [evalExpr_fork_ilk_spot_locals locals hsz164 hilk hilks, hloadSpot]
  have hguardEval :
      evalExpr? config { contract := contract, locals := locals' } evm
        (eitherExpr
          (.binary .eq (.storage (ilksF (.var "ilk") "spot")) (.intLit 0))
          (.binary .eq (.binary .div (.var "srcInkSpot")
            (.storage (ilksF (.var "ilk") "spot")))
            (.storage (urnsF (.var "ilk") (.var "src") "ink")))) =
        .ok (.bool true) := by
    have hilk' : locals'.get? "ilk" = some (forkIlkValue I) := by
      change (locals.insert "srcInkSpot" (.int (Int.ofNat srcInkSpot.toNat))).get? "ilk" =
        some (forkIlkValue I)
      rw [store_get_ne _ _ (by native_decide), hilk]
    have hsrc' : locals'.get? "src" = some (forkSrcValue I) := by
      change (locals.insert "srcInkSpot" (.int (Int.ofNat srcInkSpot.toNat))).get? "src" =
        some (forkSrcValue I)
      rw [store_get_ne _ _ (by native_decide), hsrc]
    have hurns' : locals'.get? "urns" = none := by
      change (locals.insert "srcInkSpot" (.int (Int.ofNat srcInkSpot.toNat))).get? "urns" =
        none
      rw [store_get_ne _ _ (by native_decide), hurns]
    have hilks' : locals'.get? "ilks" = none := by
      change (locals.insert "srcInkSpot" (.int (Int.ofNat srcInkSpot.toNat))).get? "ilks" =
        none
      rw [store_get_ne _ _ (by native_decide), hilks]
    have hsrcInk' :
        evalExpr? config { contract := contract, locals := locals' } evm
          (.storage (urnsF (.var "ilk") (.var "src") "ink")) =
          .ok (.int (Int.ofNat srcInk.toNat)) := by
      rw [evalExpr_fork_src_ink_locals locals' hsz164 hilk' hsrc' hurns', hloadSrc]
    have hspot' :
        evalExpr? config { contract := contract, locals := locals' } evm
          (.storage (ilksF (.var "ilk") "spot")) =
          .ok (.int (Int.ofNat spot.toNat)) := by
      rw [evalExpr_fork_ilk_spot_locals locals' hsz164 hilk' hilks', hloadSpot]
    have hsrcInkSpot :
        evalExpr? config { contract := contract, locals := locals' } evm (.var "srcInkSpot") =
          .ok (.int (Int.ofNat srcInkSpot.toNat)) := by
      exact vatEvalExpr_varUInt256 (by simp [locals'])
    exact evalExpr_fork_mul_guard_true hsrcInk' hspot' hsrcInkSpot hguard
  exact execForkMulUintIntoOk "srcInkSpot"
    (.storage (urnsF (.var "ilk") (.var "src") "ink"))
    (.storage (ilksF (.var "ilk") "spot")) srcInk spot srcInkSpot
    hsrcInk hspot hprod hfit hguardEval

theorem execForkDstInkSpotMulOk {evm : EVM.State} {I : ExecutionEnv}
    (locals : Store) (dstInk spot dstInkSpot : UInt256)
    (hsz164 : 164 ≤ I.calldata.size)
    (hilk : locals.get? "ilk" = some (forkIlkValue I))
    (hdst : locals.get? "dst" = some (forkDstValue I))
    (hurns : locals.get? "urns" = none)
    (hilks : locals.get? "ilks" = none)
    (hloadDst :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (forkDstInkSlot I) = dstInk)
    (hloadSpot :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (forkIlkSpotSlot I) = spot)
    (hprod : dstInkSpot = UInt256.mul dstInk spot)
    (hfit : dstInk.toNat * spot.toNat < UInt256.size)
    (hguard : spot.toNat = 0 ∨ dstInkSpot.toNat / spot.toNat = dstInk.toNat) :
    ExecBlock config { contract := contract, locals := locals } evm
      (checkedMulUintInto "dstInkSpot"
        (.storage (urnsF (.var "ilk") (.var "dst") "ink"))
        (.storage (ilksF (.var "ilk") "spot")))
      (.ok
        { contract := contract,
          locals := locals.insert "dstInkSpot" (.int (Int.ofNat dstInkSpot.toNat)) }
        evm) := by
  let locals' := locals.insert "dstInkSpot" (.int (Int.ofNat dstInkSpot.toNat))
  have hdstInk :
      evalExpr? config { contract := contract, locals := locals } evm
        (.storage (urnsF (.var "ilk") (.var "dst") "ink")) =
        .ok (.int (Int.ofNat dstInk.toNat)) := by
    rw [evalExpr_fork_dst_ink_locals locals hsz164 hilk hdst hurns, hloadDst]
  have hspot :
      evalExpr? config { contract := contract, locals := locals } evm
        (.storage (ilksF (.var "ilk") "spot")) =
        .ok (.int (Int.ofNat spot.toNat)) := by
    rw [evalExpr_fork_ilk_spot_locals locals hsz164 hilk hilks, hloadSpot]
  have hguardEval :
      evalExpr? config { contract := contract, locals := locals' } evm
        (eitherExpr
          (.binary .eq (.storage (ilksF (.var "ilk") "spot")) (.intLit 0))
          (.binary .eq (.binary .div (.var "dstInkSpot")
            (.storage (ilksF (.var "ilk") "spot")))
            (.storage (urnsF (.var "ilk") (.var "dst") "ink")))) =
        .ok (.bool true) := by
    have hilk' : locals'.get? "ilk" = some (forkIlkValue I) := by
      change (locals.insert "dstInkSpot" (.int (Int.ofNat dstInkSpot.toNat))).get? "ilk" =
        some (forkIlkValue I)
      rw [store_get_ne _ _ (by native_decide), hilk]
    have hdst' : locals'.get? "dst" = some (forkDstValue I) := by
      change (locals.insert "dstInkSpot" (.int (Int.ofNat dstInkSpot.toNat))).get? "dst" =
        some (forkDstValue I)
      rw [store_get_ne _ _ (by native_decide), hdst]
    have hurns' : locals'.get? "urns" = none := by
      change (locals.insert "dstInkSpot" (.int (Int.ofNat dstInkSpot.toNat))).get? "urns" =
        none
      rw [store_get_ne _ _ (by native_decide), hurns]
    have hilks' : locals'.get? "ilks" = none := by
      change (locals.insert "dstInkSpot" (.int (Int.ofNat dstInkSpot.toNat))).get? "ilks" =
        none
      rw [store_get_ne _ _ (by native_decide), hilks]
    have hdstInk' :
        evalExpr? config { contract := contract, locals := locals' } evm
          (.storage (urnsF (.var "ilk") (.var "dst") "ink")) =
          .ok (.int (Int.ofNat dstInk.toNat)) := by
      rw [evalExpr_fork_dst_ink_locals locals' hsz164 hilk' hdst' hurns', hloadDst]
    have hspot' :
        evalExpr? config { contract := contract, locals := locals' } evm
          (.storage (ilksF (.var "ilk") "spot")) =
          .ok (.int (Int.ofNat spot.toNat)) := by
      rw [evalExpr_fork_ilk_spot_locals locals' hsz164 hilk' hilks', hloadSpot]
    have hdstInkSpot :
        evalExpr? config { contract := contract, locals := locals' } evm (.var "dstInkSpot") =
          .ok (.int (Int.ofNat dstInkSpot.toNat)) := by
      exact vatEvalExpr_varUInt256 (by simp [locals'])
    exact evalExpr_fork_mul_guard_true hdstInk' hspot' hdstInkSpot hguard
  exact execForkMulUintIntoOk "dstInkSpot"
    (.storage (urnsF (.var "ilk") (.var "dst") "ink"))
    (.storage (ilksF (.var "ilk") "spot")) dstInk spot dstInkSpot
    hdstInk hspot hprod hfit hguardEval

theorem execForkFinalRequiresOk {evm : EVM.State} {locals : Store}
    (hwish :
      evalExpr? config { contract := contract, locals := locals } evm
        (bothExpr (wishExpr (.var "src") sender) (wishExpr (.var "dst") sender)) =
        .ok (.bool true))
    (hutabLe :
      evalExpr? config { contract := contract, locals := locals } evm
        (.binary .le (.var "utab") (.var "srcInkSpot")) = .ok (.bool true))
    (hvtabLe :
      evalExpr? config { contract := contract, locals := locals } evm
        (.binary .le (.var "vtab") (.var "dstInkSpot")) = .ok (.bool true))
    (hsrcDust :
      evalExpr? config { contract := contract, locals := locals } evm
        (eitherExpr
          (.binary .ge (.var "utab") (.storage (ilksF (.var "ilk") "dust")))
          (.binary .eq (.var "srcArtFinal") (.intLit 0))) =
        .ok (.bool true))
    (hdstDust :
      evalExpr? config { contract := contract, locals := locals } evm
        (eitherExpr
          (.binary .ge (.var "vtab") (.storage (ilksF (.var "ilk") "dust")))
          (.binary .eq (.var "dstArtFinal") (.intLit 0))) =
        .ok (.bool true)) :
    ExecBlock config { contract := contract, locals := locals } evm
      [ .require (bothExpr (wishExpr (.var "src") sender) (wishExpr (.var "dst") sender)),
        .require (.binary .le (.var "utab") (.var "srcInkSpot")),
        .require (.binary .le (.var "vtab") (.var "dstInkSpot")),
        .require
          (eitherExpr
            (.binary .ge (.var "utab") (.storage (ilksF (.var "ilk") "dust")))
            (.binary .eq (.var "srcArtFinal") (.intLit 0))),
        .require
          (eitherExpr
            (.binary .ge (.var "vtab") (.storage (ilksF (.var "ilk") "dust")))
            (.binary .eq (.var "dstArtFinal") (.intLit 0))) ]
      (.ok { contract := contract, locals := locals } evm) := by
  refine ExecBlock.consNormal (ExecStmt.requireTrue hwish) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue hutabLe) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue hvtabLe) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue hsrcDust) ?_
  exact ExecBlock.consNormal (ExecStmt.requireTrue hdstDust) ExecBlock.nil

theorem execForkFinalRequiresRevertWish {evm : EVM.State} {locals : Store}
    (hwish :
      evalExpr? config { contract := contract, locals := locals } evm
        (bothExpr (wishExpr (.var "src") sender) (wishExpr (.var "dst") sender)) =
        .ok (.bool false)) :
    ExecBlock config { contract := contract, locals := locals } evm
      [ .require (bothExpr (wishExpr (.var "src") sender) (wishExpr (.var "dst") sender)),
        .require (.binary .le (.var "utab") (.var "srcInkSpot")),
        .require (.binary .le (.var "vtab") (.var "dstInkSpot")),
        .require
          (eitherExpr
            (.binary .ge (.var "utab") (.storage (ilksF (.var "ilk") "dust")))
            (.binary .eq (.var "srcArtFinal") (.intLit 0))),
        .require
          (eitherExpr
            (.binary .ge (.var "vtab") (.storage (ilksF (.var "ilk") "dust")))
            (.binary .eq (.var "dstArtFinal") (.intLit 0))) ]
      .reverted := by
  exact ExecBlock.consRevert (ExecStmt.requireFalse hwish)

theorem execForkFinalRequiresRevertUtab {evm : EVM.State} {locals : Store}
    (hwish :
      evalExpr? config { contract := contract, locals := locals } evm
        (bothExpr (wishExpr (.var "src") sender) (wishExpr (.var "dst") sender)) =
        .ok (.bool true))
    (hutabLe :
      evalExpr? config { contract := contract, locals := locals } evm
        (.binary .le (.var "utab") (.var "srcInkSpot")) = .ok (.bool false)) :
    ExecBlock config { contract := contract, locals := locals } evm
      [ .require (bothExpr (wishExpr (.var "src") sender) (wishExpr (.var "dst") sender)),
        .require (.binary .le (.var "utab") (.var "srcInkSpot")),
        .require (.binary .le (.var "vtab") (.var "dstInkSpot")),
        .require
          (eitherExpr
            (.binary .ge (.var "utab") (.storage (ilksF (.var "ilk") "dust")))
            (.binary .eq (.var "srcArtFinal") (.intLit 0))),
        .require
          (eitherExpr
            (.binary .ge (.var "vtab") (.storage (ilksF (.var "ilk") "dust")))
            (.binary .eq (.var "dstArtFinal") (.intLit 0))) ]
      .reverted := by
  refine ExecBlock.consNormal (ExecStmt.requireTrue hwish) ?_
  exact ExecBlock.consRevert (ExecStmt.requireFalse hutabLe)

theorem execForkFinalRequiresRevertVtab {evm : EVM.State} {locals : Store}
    (hwish :
      evalExpr? config { contract := contract, locals := locals } evm
        (bothExpr (wishExpr (.var "src") sender) (wishExpr (.var "dst") sender)) =
        .ok (.bool true))
    (hutabLe :
      evalExpr? config { contract := contract, locals := locals } evm
        (.binary .le (.var "utab") (.var "srcInkSpot")) = .ok (.bool true))
    (hvtabLe :
      evalExpr? config { contract := contract, locals := locals } evm
        (.binary .le (.var "vtab") (.var "dstInkSpot")) = .ok (.bool false)) :
    ExecBlock config { contract := contract, locals := locals } evm
      [ .require (bothExpr (wishExpr (.var "src") sender) (wishExpr (.var "dst") sender)),
        .require (.binary .le (.var "utab") (.var "srcInkSpot")),
        .require (.binary .le (.var "vtab") (.var "dstInkSpot")),
        .require
          (eitherExpr
            (.binary .ge (.var "utab") (.storage (ilksF (.var "ilk") "dust")))
            (.binary .eq (.var "srcArtFinal") (.intLit 0))),
        .require
          (eitherExpr
            (.binary .ge (.var "vtab") (.storage (ilksF (.var "ilk") "dust")))
            (.binary .eq (.var "dstArtFinal") (.intLit 0))) ]
      .reverted := by
  refine ExecBlock.consNormal (ExecStmt.requireTrue hwish) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue hutabLe) ?_
  exact ExecBlock.consRevert (ExecStmt.requireFalse hvtabLe)

theorem execForkFinalRequiresRevertSrcDust {evm : EVM.State} {locals : Store}
    (hwish :
      evalExpr? config { contract := contract, locals := locals } evm
        (bothExpr (wishExpr (.var "src") sender) (wishExpr (.var "dst") sender)) =
        .ok (.bool true))
    (hutabLe :
      evalExpr? config { contract := contract, locals := locals } evm
        (.binary .le (.var "utab") (.var "srcInkSpot")) = .ok (.bool true))
    (hvtabLe :
      evalExpr? config { contract := contract, locals := locals } evm
        (.binary .le (.var "vtab") (.var "dstInkSpot")) = .ok (.bool true))
    (hsrcDust :
      evalExpr? config { contract := contract, locals := locals } evm
        (eitherExpr
          (.binary .ge (.var "utab") (.storage (ilksF (.var "ilk") "dust")))
          (.binary .eq (.var "srcArtFinal") (.intLit 0))) =
        .ok (.bool false)) :
    ExecBlock config { contract := contract, locals := locals } evm
      [ .require (bothExpr (wishExpr (.var "src") sender) (wishExpr (.var "dst") sender)),
        .require (.binary .le (.var "utab") (.var "srcInkSpot")),
        .require (.binary .le (.var "vtab") (.var "dstInkSpot")),
        .require
          (eitherExpr
            (.binary .ge (.var "utab") (.storage (ilksF (.var "ilk") "dust")))
            (.binary .eq (.var "srcArtFinal") (.intLit 0))),
        .require
          (eitherExpr
            (.binary .ge (.var "vtab") (.storage (ilksF (.var "ilk") "dust")))
            (.binary .eq (.var "dstArtFinal") (.intLit 0))) ]
      .reverted := by
  refine ExecBlock.consNormal (ExecStmt.requireTrue hwish) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue hutabLe) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue hvtabLe) ?_
  exact ExecBlock.consRevert (ExecStmt.requireFalse hsrcDust)

theorem execForkFinalRequiresRevertDstDust {evm : EVM.State} {locals : Store}
    (hwish :
      evalExpr? config { contract := contract, locals := locals } evm
        (bothExpr (wishExpr (.var "src") sender) (wishExpr (.var "dst") sender)) =
        .ok (.bool true))
    (hutabLe :
      evalExpr? config { contract := contract, locals := locals } evm
        (.binary .le (.var "utab") (.var "srcInkSpot")) = .ok (.bool true))
    (hvtabLe :
      evalExpr? config { contract := contract, locals := locals } evm
        (.binary .le (.var "vtab") (.var "dstInkSpot")) = .ok (.bool true))
    (hsrcDust :
      evalExpr? config { contract := contract, locals := locals } evm
        (eitherExpr
          (.binary .ge (.var "utab") (.storage (ilksF (.var "ilk") "dust")))
          (.binary .eq (.var "srcArtFinal") (.intLit 0))) =
        .ok (.bool true))
    (hdstDust :
      evalExpr? config { contract := contract, locals := locals } evm
        (eitherExpr
          (.binary .ge (.var "vtab") (.storage (ilksF (.var "ilk") "dust")))
          (.binary .eq (.var "dstArtFinal") (.intLit 0))) =
        .ok (.bool false)) :
    ExecBlock config { contract := contract, locals := locals } evm
      [ .require (bothExpr (wishExpr (.var "src") sender) (wishExpr (.var "dst") sender)),
        .require (.binary .le (.var "utab") (.var "srcInkSpot")),
        .require (.binary .le (.var "vtab") (.var "dstInkSpot")),
        .require
          (eitherExpr
            (.binary .ge (.var "utab") (.storage (ilksF (.var "ilk") "dust")))
            (.binary .eq (.var "srcArtFinal") (.intLit 0))),
        .require
          (eitherExpr
            (.binary .ge (.var "vtab") (.storage (ilksF (.var "ilk") "dust")))
            (.binary .eq (.var "dstArtFinal") (.intLit 0))) ]
      .reverted := by
  refine ExecBlock.consNormal (ExecStmt.requireTrue hwish) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue hutabLe) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue hvtabLe) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue hsrcDust) ?_
  exact ExecBlock.consRevert (ExecStmt.requireFalse hdstDust)

theorem evalExpr_fork_utab_le_srcInkSpot_final {evm : EVM.State} {I : ExecutionEnv}
    (srcInkNew srcArtNew dstInkNew dstArtNew utab vtab srcInkSpot dstInkSpot : UInt256)
    (hle : utab.toNat ≤ srcInkSpot.toNat) :
    evalExpr? config
      { contract := contract,
        locals :=
          forkStoreDstInkSpot I srcInkNew srcArtNew dstInkNew dstArtNew utab vtab
            srcInkSpot dstInkSpot } evm
      (.binary .le (.var "utab") (.var "srcInkSpot")) = .ok (.bool true) := by
  let locals :=
    forkStoreDstInkSpot I srcInkNew srcArtNew dstInkNew dstArtNew utab vtab srcInkSpot
      dstInkSpot
  have hutab :
      evalExpr? config { contract := contract, locals := locals } evm (.var "utab") =
        .ok (.int (Int.ofNat utab.toNat)) :=
    vatEvalExpr_varUInt256 (by
      simpa [locals] using
        forkStoreDstInkSpot_get_utab I srcInkNew srcArtNew dstInkNew dstArtNew utab vtab
          srcInkSpot dstInkSpot)
  have hspot :
      evalExpr? config { contract := contract, locals := locals } evm (.var "srcInkSpot") =
        .ok (.int (Int.ofNat srcInkSpot.toNat)) :=
    vatEvalExpr_varUInt256 (by
      simpa [locals] using
        forkStoreDstInkSpot_get_srcInkSpot I srcInkNew srcArtNew dstInkNew dstArtNew utab vtab
          srcInkSpot dstInkSpot)
  exact vatEvalExpr_le_uint256_true hutab hspot hle

theorem evalExpr_fork_vtab_le_dstInkSpot_final {evm : EVM.State} {I : ExecutionEnv}
    (srcInkNew srcArtNew dstInkNew dstArtNew utab vtab srcInkSpot dstInkSpot : UInt256)
    (hle : vtab.toNat ≤ dstInkSpot.toNat) :
    evalExpr? config
      { contract := contract,
        locals :=
          forkStoreDstInkSpot I srcInkNew srcArtNew dstInkNew dstArtNew utab vtab
            srcInkSpot dstInkSpot } evm
      (.binary .le (.var "vtab") (.var "dstInkSpot")) = .ok (.bool true) := by
  let locals :=
    forkStoreDstInkSpot I srcInkNew srcArtNew dstInkNew dstArtNew utab vtab srcInkSpot
      dstInkSpot
  have hvtab :
      evalExpr? config { contract := contract, locals := locals } evm (.var "vtab") =
        .ok (.int (Int.ofNat vtab.toNat)) :=
    vatEvalExpr_varUInt256 (by
      simpa [locals] using
        forkStoreDstInkSpot_get_vtab I srcInkNew srcArtNew dstInkNew dstArtNew utab vtab
          srcInkSpot dstInkSpot)
  have hspot :
      evalExpr? config { contract := contract, locals := locals } evm (.var "dstInkSpot") =
        .ok (.int (Int.ofNat dstInkSpot.toNat)) :=
    vatEvalExpr_varUInt256 (by
      simpa [locals] using
        forkStoreDstInkSpot_get_dstInkSpot I srcInkNew srcArtNew dstInkNew dstArtNew utab vtab
          srcInkSpot dstInkSpot)
  exact vatEvalExpr_le_uint256_true hvtab hspot hle

theorem evalExpr_fork_utab_le_srcInkSpot_false_final {evm : EVM.State} {I : ExecutionEnv}
    (srcInkNew srcArtNew dstInkNew dstArtNew utab vtab srcInkSpot dstInkSpot : UInt256)
    (hgt : srcInkSpot.toNat < utab.toNat) :
    evalExpr? config
      { contract := contract,
        locals :=
          forkStoreDstInkSpot I srcInkNew srcArtNew dstInkNew dstArtNew utab vtab
            srcInkSpot dstInkSpot } evm
      (.binary .le (.var "utab") (.var "srcInkSpot")) = .ok (.bool false) := by
  let locals :=
    forkStoreDstInkSpot I srcInkNew srcArtNew dstInkNew dstArtNew utab vtab srcInkSpot
      dstInkSpot
  have hutab :
      evalExpr? config { contract := contract, locals := locals } evm (.var "utab") =
        .ok (.int (Int.ofNat utab.toNat)) :=
    vatEvalExpr_varUInt256 (by
      simpa [locals] using
        forkStoreDstInkSpot_get_utab I srcInkNew srcArtNew dstInkNew dstArtNew utab vtab
          srcInkSpot dstInkSpot)
  have hspot :
      evalExpr? config { contract := contract, locals := locals } evm (.var "srcInkSpot") =
        .ok (.int (Int.ofNat srcInkSpot.toNat)) :=
    vatEvalExpr_varUInt256 (by
      simpa [locals] using
        forkStoreDstInkSpot_get_srcInkSpot I srcInkNew srcArtNew dstInkNew dstArtNew utab vtab
          srcInkSpot dstInkSpot)
  exact vatEvalExpr_le_uint256_false hutab hspot hgt

theorem evalExpr_fork_vtab_le_dstInkSpot_false_final {evm : EVM.State} {I : ExecutionEnv}
    (srcInkNew srcArtNew dstInkNew dstArtNew utab vtab srcInkSpot dstInkSpot : UInt256)
    (hgt : dstInkSpot.toNat < vtab.toNat) :
    evalExpr? config
      { contract := contract,
        locals :=
          forkStoreDstInkSpot I srcInkNew srcArtNew dstInkNew dstArtNew utab vtab
            srcInkSpot dstInkSpot } evm
      (.binary .le (.var "vtab") (.var "dstInkSpot")) = .ok (.bool false) := by
  let locals :=
    forkStoreDstInkSpot I srcInkNew srcArtNew dstInkNew dstArtNew utab vtab srcInkSpot
      dstInkSpot
  have hvtab :
      evalExpr? config { contract := contract, locals := locals } evm (.var "vtab") =
        .ok (.int (Int.ofNat vtab.toNat)) :=
    vatEvalExpr_varUInt256 (by
      simpa [locals] using
        forkStoreDstInkSpot_get_vtab I srcInkNew srcArtNew dstInkNew dstArtNew utab vtab
          srcInkSpot dstInkSpot)
  have hspot :
      evalExpr? config { contract := contract, locals := locals } evm (.var "dstInkSpot") =
        .ok (.int (Int.ofNat dstInkSpot.toNat)) :=
    vatEvalExpr_varUInt256 (by
      simpa [locals] using
        forkStoreDstInkSpot_get_dstInkSpot I srcInkNew srcArtNew dstInkNew dstArtNew utab vtab
          srcInkSpot dstInkSpot)
  exact vatEvalExpr_le_uint256_false hvtab hspot hgt

theorem evalExpr_fork_utab_le_srcInkSpot_final_store {evm : EVM.State} {I : ExecutionEnv}
    (srcInkNew srcArtNew dstInkNew dstArtNew
      srcArtFinal dstArtFinal srcInkFinal dstInkFinal
      utab vtab srcInkSpot dstInkSpot : UInt256)
    (hle : utab.toNat ≤ srcInkSpot.toNat) :
    evalExpr? config
      { contract := contract,
        locals :=
          forkStoreDstInkSpotFinal I srcInkNew srcArtNew dstInkNew dstArtNew
            srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab vtab srcInkSpot
            dstInkSpot } evm
      (.binary .le (.var "utab") (.var "srcInkSpot")) = .ok (.bool true) := by
  let locals :=
    forkStoreDstInkSpotFinal I srcInkNew srcArtNew dstInkNew dstArtNew
      srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab vtab srcInkSpot dstInkSpot
  have hutab :
      evalExpr? config { contract := contract, locals := locals } evm (.var "utab") =
        .ok (.int (Int.ofNat utab.toNat)) :=
    vatEvalExpr_varUInt256 (by
      simpa [locals] using
        forkStoreDstInkSpotFinal_get_utab I srcInkNew srcArtNew dstInkNew dstArtNew
          srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab vtab srcInkSpot
          dstInkSpot)
  have hspot :
      evalExpr? config { contract := contract, locals := locals } evm (.var "srcInkSpot") =
        .ok (.int (Int.ofNat srcInkSpot.toNat)) :=
    vatEvalExpr_varUInt256 (by
      simpa [locals] using
        forkStoreDstInkSpotFinal_get_srcInkSpot I srcInkNew srcArtNew dstInkNew
          dstArtNew srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab vtab
          srcInkSpot dstInkSpot)
  exact vatEvalExpr_le_uint256_true hutab hspot hle

theorem evalExpr_fork_vtab_le_dstInkSpot_final_store {evm : EVM.State} {I : ExecutionEnv}
    (srcInkNew srcArtNew dstInkNew dstArtNew
      srcArtFinal dstArtFinal srcInkFinal dstInkFinal
      utab vtab srcInkSpot dstInkSpot : UInt256)
    (hle : vtab.toNat ≤ dstInkSpot.toNat) :
    evalExpr? config
      { contract := contract,
        locals :=
          forkStoreDstInkSpotFinal I srcInkNew srcArtNew dstInkNew dstArtNew
            srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab vtab srcInkSpot
            dstInkSpot } evm
      (.binary .le (.var "vtab") (.var "dstInkSpot")) = .ok (.bool true) := by
  let locals :=
    forkStoreDstInkSpotFinal I srcInkNew srcArtNew dstInkNew dstArtNew
      srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab vtab srcInkSpot dstInkSpot
  have hvtab :
      evalExpr? config { contract := contract, locals := locals } evm (.var "vtab") =
        .ok (.int (Int.ofNat vtab.toNat)) :=
    vatEvalExpr_varUInt256 (by
      simpa [locals] using
        forkStoreDstInkSpotFinal_get_vtab I srcInkNew srcArtNew dstInkNew dstArtNew
          srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab vtab srcInkSpot
          dstInkSpot)
  have hspot :
      evalExpr? config { contract := contract, locals := locals } evm (.var "dstInkSpot") =
        .ok (.int (Int.ofNat dstInkSpot.toNat)) :=
    vatEvalExpr_varUInt256 (by
      simpa [locals] using
        forkStoreDstInkSpotFinal_get_dstInkSpot I srcInkNew srcArtNew dstInkNew
          dstArtNew srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab vtab
          srcInkSpot dstInkSpot)
  exact vatEvalExpr_le_uint256_true hvtab hspot hle

theorem evalExpr_fork_utab_le_srcInkSpot_false_final_store
    {evm : EVM.State} {I : ExecutionEnv}
    (srcInkNew srcArtNew dstInkNew dstArtNew
      srcArtFinal dstArtFinal srcInkFinal dstInkFinal
      utab vtab srcInkSpot dstInkSpot : UInt256)
    (hgt : srcInkSpot.toNat < utab.toNat) :
    evalExpr? config
      { contract := contract,
        locals :=
          forkStoreDstInkSpotFinal I srcInkNew srcArtNew dstInkNew dstArtNew
            srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab vtab srcInkSpot
            dstInkSpot } evm
      (.binary .le (.var "utab") (.var "srcInkSpot")) = .ok (.bool false) := by
  let locals :=
    forkStoreDstInkSpotFinal I srcInkNew srcArtNew dstInkNew dstArtNew
      srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab vtab srcInkSpot dstInkSpot
  have hutab :
      evalExpr? config { contract := contract, locals := locals } evm (.var "utab") =
        .ok (.int (Int.ofNat utab.toNat)) :=
    vatEvalExpr_varUInt256 (by
      simpa [locals] using
        forkStoreDstInkSpotFinal_get_utab I srcInkNew srcArtNew dstInkNew dstArtNew
          srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab vtab srcInkSpot
          dstInkSpot)
  have hspot :
      evalExpr? config { contract := contract, locals := locals } evm (.var "srcInkSpot") =
        .ok (.int (Int.ofNat srcInkSpot.toNat)) :=
    vatEvalExpr_varUInt256 (by
      simpa [locals] using
        forkStoreDstInkSpotFinal_get_srcInkSpot I srcInkNew srcArtNew dstInkNew
          dstArtNew srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab vtab
          srcInkSpot dstInkSpot)
  exact vatEvalExpr_le_uint256_false hutab hspot hgt

theorem evalExpr_fork_vtab_le_dstInkSpot_false_final_store
    {evm : EVM.State} {I : ExecutionEnv}
    (srcInkNew srcArtNew dstInkNew dstArtNew
      srcArtFinal dstArtFinal srcInkFinal dstInkFinal
      utab vtab srcInkSpot dstInkSpot : UInt256)
    (hgt : dstInkSpot.toNat < vtab.toNat) :
    evalExpr? config
      { contract := contract,
        locals :=
          forkStoreDstInkSpotFinal I srcInkNew srcArtNew dstInkNew dstArtNew
            srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab vtab srcInkSpot
            dstInkSpot } evm
      (.binary .le (.var "vtab") (.var "dstInkSpot")) = .ok (.bool false) := by
  let locals :=
    forkStoreDstInkSpotFinal I srcInkNew srcArtNew dstInkNew dstArtNew
      srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab vtab srcInkSpot dstInkSpot
  have hvtab :
      evalExpr? config { contract := contract, locals := locals } evm (.var "vtab") =
        .ok (.int (Int.ofNat vtab.toNat)) :=
    vatEvalExpr_varUInt256 (by
      simpa [locals] using
        forkStoreDstInkSpotFinal_get_vtab I srcInkNew srcArtNew dstInkNew dstArtNew
          srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab vtab srcInkSpot
          dstInkSpot)
  have hspot :
      evalExpr? config { contract := contract, locals := locals } evm (.var "dstInkSpot") =
        .ok (.int (Int.ofNat dstInkSpot.toNat)) :=
    vatEvalExpr_varUInt256 (by
      simpa [locals] using
        forkStoreDstInkSpotFinal_get_dstInkSpot I srcInkNew srcArtNew dstInkNew
          dstArtNew srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab vtab
          srcInkSpot dstInkSpot)
  exact vatEvalExpr_le_uint256_false hvtab hspot hgt

theorem evalExpr_fork_src_dust_final_store {evm : EVM.State} {I : ExecutionEnv}
    (srcInkNew srcArtNew dstInkNew dstArtNew
      srcArtFinal dstArtFinal srcInkFinal dstInkFinal
      utab vtab srcInkSpot dstInkSpot dust : UInt256)
    (hsz164 : 164 ≤ I.calldata.size)
    (hloadDust :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (forkIlkDustSlot I) = dust)
    (hcond : dust.toNat ≤ utab.toNat ∨ srcArtFinal.toNat = 0) :
    evalExpr? config
      { contract := contract,
        locals :=
          forkStoreDstInkSpotFinal I srcInkNew srcArtNew dstInkNew dstArtNew
            srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab vtab srcInkSpot
            dstInkSpot } evm
      (eitherExpr
        (.binary .ge (.var "utab") (.storage (ilksF (.var "ilk") "dust")))
        (.binary .eq (.var "srcArtFinal") (.intLit 0))) =
      .ok (.bool true) := by
  let locals :=
    forkStoreDstInkSpotFinal I srcInkNew srcArtNew dstInkNew dstArtNew
      srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab vtab srcInkSpot dstInkSpot
  have hutab :
      evalExpr? config { contract := contract, locals := locals } evm (.var "utab") =
        .ok (.int (Int.ofNat utab.toNat)) :=
    vatEvalExpr_varUInt256 (by
      simpa [locals] using
        forkStoreDstInkSpotFinal_get_utab I srcInkNew srcArtNew dstInkNew dstArtNew
          srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab vtab srcInkSpot
          dstInkSpot)
  have hdust :
      evalExpr? config { contract := contract, locals := locals } evm
        (.storage (ilksF (.var "ilk") "dust")) =
        .ok (.int (Int.ofNat dust.toNat)) := by
    rw [evalExpr_fork_ilk_dust_locals locals hsz164
      (by
        simpa [locals] using
          forkStoreDstInkSpotFinal_get_ilk I srcInkNew srcArtNew dstInkNew dstArtNew
            srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab vtab srcInkSpot
            dstInkSpot)
      (by
        simpa [locals] using
          forkStoreDstInkSpotFinal_get_ilks I srcInkNew srcArtNew dstInkNew dstArtNew
            srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab vtab srcInkSpot
            dstInkSpot)]
    rw [hloadDust]
  cases hcond with
  | inl hge =>
      exact vatEvalExpr_or_true_left
        (vatEvalExpr_ge_uint256_true hutab hdust hge)
  | inr hzero =>
      by_cases hge : dust.toNat ≤ utab.toNat
      · exact vatEvalExpr_or_true_left
          (vatEvalExpr_ge_uint256_true hutab hdust hge)
      · have hleft := vatEvalExpr_ge_uint256_false hutab hdust (Nat.lt_of_not_ge hge)
        have hsrcArt :
            evalExpr? config { contract := contract, locals := locals } evm
              (.var "srcArtFinal") = .ok (.int (Int.ofNat srcArtFinal.toNat)) :=
          vatEvalExpr_varUInt256 (by
            simpa [locals] using
              forkStoreDstInkSpotFinal_get_srcArtFinal I srcInkNew srcArtNew
                dstInkNew dstArtNew srcArtFinal dstArtFinal srcInkFinal dstInkFinal
                utab vtab srcInkSpot dstInkSpot)
        have hright :
            evalExpr? config { contract := contract, locals := locals } evm
              (.binary .eq (.var "srcArtFinal") (.intLit 0)) = .ok (.bool true) := by
          simp [evalExpr?, EvalResult.bind, bind, hsrcArt, evalBinaryOp?, hzero]
        exact vatEvalExpr_or_false_right hleft hright

theorem evalExpr_fork_dst_dust_final_store {evm : EVM.State} {I : ExecutionEnv}
    (srcInkNew srcArtNew dstInkNew dstArtNew
      srcArtFinal dstArtFinal srcInkFinal dstInkFinal
      utab vtab srcInkSpot dstInkSpot dust : UInt256)
    (hsz164 : 164 ≤ I.calldata.size)
    (hloadDust :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (forkIlkDustSlot I) = dust)
    (hcond : dust.toNat ≤ vtab.toNat ∨ dstArtFinal.toNat = 0) :
    evalExpr? config
      { contract := contract,
        locals :=
          forkStoreDstInkSpotFinal I srcInkNew srcArtNew dstInkNew dstArtNew
            srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab vtab srcInkSpot
            dstInkSpot } evm
      (eitherExpr
        (.binary .ge (.var "vtab") (.storage (ilksF (.var "ilk") "dust")))
        (.binary .eq (.var "dstArtFinal") (.intLit 0))) =
      .ok (.bool true) := by
  let locals :=
    forkStoreDstInkSpotFinal I srcInkNew srcArtNew dstInkNew dstArtNew
      srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab vtab srcInkSpot dstInkSpot
  have hvtab :
      evalExpr? config { contract := contract, locals := locals } evm (.var "vtab") =
        .ok (.int (Int.ofNat vtab.toNat)) :=
    vatEvalExpr_varUInt256 (by
      simpa [locals] using
        forkStoreDstInkSpotFinal_get_vtab I srcInkNew srcArtNew dstInkNew dstArtNew
          srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab vtab srcInkSpot
          dstInkSpot)
  have hdust :
      evalExpr? config { contract := contract, locals := locals } evm
        (.storage (ilksF (.var "ilk") "dust")) =
        .ok (.int (Int.ofNat dust.toNat)) := by
    rw [evalExpr_fork_ilk_dust_locals locals hsz164
      (by
        simpa [locals] using
          forkStoreDstInkSpotFinal_get_ilk I srcInkNew srcArtNew dstInkNew dstArtNew
            srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab vtab srcInkSpot
            dstInkSpot)
      (by
        simpa [locals] using
          forkStoreDstInkSpotFinal_get_ilks I srcInkNew srcArtNew dstInkNew dstArtNew
            srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab vtab srcInkSpot
            dstInkSpot)]
    rw [hloadDust]
  cases hcond with
  | inl hge =>
      exact vatEvalExpr_or_true_left
        (vatEvalExpr_ge_uint256_true hvtab hdust hge)
  | inr hzero =>
      by_cases hge : dust.toNat ≤ vtab.toNat
      · exact vatEvalExpr_or_true_left
          (vatEvalExpr_ge_uint256_true hvtab hdust hge)
      · have hleft := vatEvalExpr_ge_uint256_false hvtab hdust (Nat.lt_of_not_ge hge)
        have hdstArt :
            evalExpr? config { contract := contract, locals := locals } evm
              (.var "dstArtFinal") = .ok (.int (Int.ofNat dstArtFinal.toNat)) :=
          vatEvalExpr_varUInt256 (by
            simpa [locals] using
              forkStoreDstInkSpotFinal_get_dstArtFinal I srcInkNew srcArtNew
                dstInkNew dstArtNew srcArtFinal dstArtFinal srcInkFinal dstInkFinal
                utab vtab srcInkSpot dstInkSpot)
        have hright :
            evalExpr? config { contract := contract, locals := locals } evm
              (.binary .eq (.var "dstArtFinal") (.intLit 0)) = .ok (.bool true) := by
          simp [evalExpr?, EvalResult.bind, bind, hdstArt, evalBinaryOp?, hzero]
        exact vatEvalExpr_or_false_right hleft hright

theorem evalExpr_fork_src_dust_false_final_store
    {evm : EVM.State} {I : ExecutionEnv}
    (srcInkNew srcArtNew dstInkNew dstArtNew
      srcArtFinal dstArtFinal srcInkFinal dstInkFinal
      utab vtab srcInkSpot dstInkSpot dust : UInt256)
    (hsz164 : 164 ≤ I.calldata.size)
    (hloadDust :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (forkIlkDustSlot I) = dust)
    (hgtDust : utab.toNat < dust.toNat)
    (hsrcArtPos : 0 < srcArtFinal.toNat) :
    evalExpr? config
      { contract := contract,
        locals :=
          forkStoreDstInkSpotFinal I srcInkNew srcArtNew dstInkNew dstArtNew
            srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab vtab srcInkSpot
            dstInkSpot } evm
      (eitherExpr
        (.binary .ge (.var "utab") (.storage (ilksF (.var "ilk") "dust")))
        (.binary .eq (.var "srcArtFinal") (.intLit 0))) =
      .ok (.bool false) := by
  let locals :=
    forkStoreDstInkSpotFinal I srcInkNew srcArtNew dstInkNew dstArtNew
      srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab vtab srcInkSpot dstInkSpot
  have hutab :
      evalExpr? config { contract := contract, locals := locals } evm (.var "utab") =
        .ok (.int (Int.ofNat utab.toNat)) :=
    vatEvalExpr_varUInt256 (by
      simpa [locals] using
        forkStoreDstInkSpotFinal_get_utab I srcInkNew srcArtNew dstInkNew dstArtNew
          srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab vtab srcInkSpot
          dstInkSpot)
  have hdust :
      evalExpr? config { contract := contract, locals := locals } evm
        (.storage (ilksF (.var "ilk") "dust")) =
        .ok (.int (Int.ofNat dust.toNat)) := by
    rw [evalExpr_fork_ilk_dust_locals locals hsz164
      (by
        simpa [locals] using
          forkStoreDstInkSpotFinal_get_ilk I srcInkNew srcArtNew dstInkNew dstArtNew
            srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab vtab srcInkSpot
            dstInkSpot)
      (by
        simpa [locals] using
          forkStoreDstInkSpotFinal_get_ilks I srcInkNew srcArtNew dstInkNew dstArtNew
            srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab vtab srcInkSpot
            dstInkSpot)]
    rw [hloadDust]
  have hsrcArt :
      evalExpr? config { contract := contract, locals := locals } evm
        (.var "srcArtFinal") = .ok (.int (Int.ofNat srcArtFinal.toNat)) :=
    vatEvalExpr_varUInt256 (by
      simpa [locals] using
        forkStoreDstInkSpotFinal_get_srcArtFinal I srcInkNew srcArtNew dstInkNew
          dstArtNew srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab vtab
          srcInkSpot dstInkSpot)
  have hsrcArtZero :
      evalExpr? config { contract := contract, locals := locals } evm
        (.binary .eq (.var "srcArtFinal") (.intLit 0)) = .ok (.bool false) := by
    simp [evalExpr?, EvalResult.bind, bind, hsrcArt, evalBinaryOp?]
    omega
  exact vatEvalExpr_or_false_right
    (vatEvalExpr_ge_uint256_false hutab hdust hgtDust)
    hsrcArtZero

theorem evalExpr_fork_dst_dust_false_final_store
    {evm : EVM.State} {I : ExecutionEnv}
    (srcInkNew srcArtNew dstInkNew dstArtNew
      srcArtFinal dstArtFinal srcInkFinal dstInkFinal
      utab vtab srcInkSpot dstInkSpot dust : UInt256)
    (hsz164 : 164 ≤ I.calldata.size)
    (hloadDust :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (forkIlkDustSlot I) = dust)
    (hgtDust : vtab.toNat < dust.toNat)
    (hdstArtPos : 0 < dstArtFinal.toNat) :
    evalExpr? config
      { contract := contract,
        locals :=
          forkStoreDstInkSpotFinal I srcInkNew srcArtNew dstInkNew dstArtNew
            srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab vtab srcInkSpot
            dstInkSpot } evm
      (eitherExpr
        (.binary .ge (.var "vtab") (.storage (ilksF (.var "ilk") "dust")))
        (.binary .eq (.var "dstArtFinal") (.intLit 0))) =
      .ok (.bool false) := by
  let locals :=
    forkStoreDstInkSpotFinal I srcInkNew srcArtNew dstInkNew dstArtNew
      srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab vtab srcInkSpot dstInkSpot
  have hvtab :
      evalExpr? config { contract := contract, locals := locals } evm (.var "vtab") =
        .ok (.int (Int.ofNat vtab.toNat)) :=
    vatEvalExpr_varUInt256 (by
      simpa [locals] using
        forkStoreDstInkSpotFinal_get_vtab I srcInkNew srcArtNew dstInkNew dstArtNew
          srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab vtab srcInkSpot
          dstInkSpot)
  have hdust :
      evalExpr? config { contract := contract, locals := locals } evm
        (.storage (ilksF (.var "ilk") "dust")) =
        .ok (.int (Int.ofNat dust.toNat)) := by
    rw [evalExpr_fork_ilk_dust_locals locals hsz164
      (by
        simpa [locals] using
          forkStoreDstInkSpotFinal_get_ilk I srcInkNew srcArtNew dstInkNew dstArtNew
            srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab vtab srcInkSpot
            dstInkSpot)
      (by
        simpa [locals] using
          forkStoreDstInkSpotFinal_get_ilks I srcInkNew srcArtNew dstInkNew dstArtNew
            srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab vtab srcInkSpot
            dstInkSpot)]
    rw [hloadDust]
  have hdstArt :
      evalExpr? config { contract := contract, locals := locals } evm
        (.var "dstArtFinal") = .ok (.int (Int.ofNat dstArtFinal.toNat)) :=
    vatEvalExpr_varUInt256 (by
      simpa [locals] using
        forkStoreDstInkSpotFinal_get_dstArtFinal I srcInkNew srcArtNew dstInkNew
          dstArtNew srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab vtab
          srcInkSpot dstInkSpot)
  have hdstArtZero :
      evalExpr? config { contract := contract, locals := locals } evm
        (.binary .eq (.var "dstArtFinal") (.intLit 0)) = .ok (.bool false) := by
    simp [evalExpr?, EvalResult.bind, bind, hdstArt, evalBinaryOp?]
    omega
  exact vatEvalExpr_or_false_right
    (vatEvalExpr_ge_uint256_false hvtab hdust hgtDust)
    hdstArtZero

theorem vatEvalExpr_and_true {evm : EVM.State} {locals : Store}
    {lhs rhs : Expr}
    (hlhs : evalExpr? config { contract := contract, locals := locals } evm lhs =
      .ok (.bool true))
    (hrhs : evalExpr? config { contract := contract, locals := locals } evm rhs =
      .ok (.bool true)) :
    evalExpr? config { contract := contract, locals := locals } evm (.binary .and lhs rhs) =
      .ok (.bool true) := by
  simp [evalExpr?, EvalResult.bind, bind, pure, hlhs, hrhs]

theorem evalExpr_fork_src_can_final {evm : EVM.State} {I : ExecutionEnv}
    (srcInkNew srcArtNew dstInkNew dstArtNew utab vtab srcInkSpot dstInkSpot : UInt256)
    (hsource : evm.executionEnv.source = I.source) :
    evalExpr? config
      { contract := contract,
        locals :=
          forkStoreDstInkSpot I srcInkNew srcArtNew dstInkNew dstArtNew utab vtab
            srcInkSpot dstInkSpot } evm
      (.storage (canRef (.var "src") sender)) =
      .ok (.int (Int.ofNat
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (forkSrcWishSlot I)).toNat)) := by
  let locals :=
    forkStoreDstInkSpot I srcInkNew srcArtNew dstInkNew dstArtNew utab vtab srcInkSpot
      dstInkSpot
  exact evalExpr_storage_scalar_value
    (hbase := by
      change locals.get? "can" = none
      simpa [locals] using
        forkStoreDstInkSpot_get_can I srcInkNew srcArtNew dstInkNew dstArtNew utab vtab
          srcInkSpot dstInkSpot)
    (her := evalStorageRef_fork_src_can_locals evm I locals hsource (by
      simpa [locals] using
        forkStoreDstInkSpot_get_src I srcInkNew srcArtNew dstInkNew dstArtNew utab vtab
          srcInkSpot dstInkSpot))
    (hty := forkStorageType_can I (forkSrcWishEvaledRef I) (Or.inl rfl))
    (hloc := forkStorageLayout_src_can I)
    (hload := vatStorageLocLoad_uint256 evm (forkSrcWishSlot I))

theorem evalExpr_fork_dst_can_final {evm : EVM.State} {I : ExecutionEnv}
    (srcInkNew srcArtNew dstInkNew dstArtNew utab vtab srcInkSpot dstInkSpot : UInt256)
    (hsource : evm.executionEnv.source = I.source) :
    evalExpr? config
      { contract := contract,
        locals :=
          forkStoreDstInkSpot I srcInkNew srcArtNew dstInkNew dstArtNew utab vtab
            srcInkSpot dstInkSpot } evm
      (.storage (canRef (.var "dst") sender)) =
      .ok (.int (Int.ofNat
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (forkDstWishSlot I)).toNat)) := by
  let locals :=
    forkStoreDstInkSpot I srcInkNew srcArtNew dstInkNew dstArtNew utab vtab srcInkSpot
      dstInkSpot
  exact evalExpr_storage_scalar_value
    (hbase := by
      change locals.get? "can" = none
      simpa [locals] using
        forkStoreDstInkSpot_get_can I srcInkNew srcArtNew dstInkNew dstArtNew utab vtab
          srcInkSpot dstInkSpot)
    (her := evalStorageRef_fork_dst_can_locals evm I locals hsource (by
      simpa [locals] using
        forkStoreDstInkSpot_get_dst I srcInkNew srcArtNew dstInkNew dstArtNew utab vtab
          srcInkSpot dstInkSpot))
    (hty := forkStorageType_can I (forkDstWishEvaledRef I) (Or.inr rfl))
    (hloc := forkStorageLayout_dst_can I)
    (hload := vatStorageLocLoad_uint256 evm (forkDstWishSlot I))

theorem evalExpr_fork_src_sender_eq_true_final {evm : EVM.State} {I : ExecutionEnv}
    (srcInkNew srcArtNew dstInkNew dstArtNew utab vtab srcInkSpot dstInkSpot : UInt256)
    (hsource : evm.executionEnv.source = I.source)
    (heq : forkSrcMaskedWord I = hopeSourceWord I) :
    evalExpr? config
      { contract := contract,
        locals :=
          forkStoreDstInkSpot I srcInkNew srcArtNew dstInkNew dstArtNew utab vtab
            srcInkSpot dstInkSpot } evm
      (.binary .eq (.var "src") sender) = .ok (.bool true) := by
  have hsrcValue :
      forkSrcValue I = .address evm.executionEnv.source := by
    rw [forkSrcValue, solcAddressValue_masked (forkSrcWord I)]
    change Value.address (AccountAddress.ofNat (forkSrcMaskedWord I).toNat) =
      Value.address evm.executionEnv.source
    rw [heq]
    rw [forkHopeSource_ofNat I, ← hsource]
  simp only [evalExpr?, sender, envValue, EvalResult.bind, EvalResult.ofOption, bind, pure]
  rw [forkStoreDstInkSpot_get_src I srcInkNew srcArtNew dstInkNew dstArtNew utab vtab
    srcInkSpot dstInkSpot, hsrcValue]
  simp [evalBinaryOp?]

theorem evalExpr_fork_dst_sender_eq_true_final {evm : EVM.State} {I : ExecutionEnv}
    (srcInkNew srcArtNew dstInkNew dstArtNew utab vtab srcInkSpot dstInkSpot : UInt256)
    (hsource : evm.executionEnv.source = I.source)
    (heq : forkDstMaskedWord I = hopeSourceWord I) :
    evalExpr? config
      { contract := contract,
        locals :=
          forkStoreDstInkSpot I srcInkNew srcArtNew dstInkNew dstArtNew utab vtab
            srcInkSpot dstInkSpot } evm
      (.binary .eq (.var "dst") sender) = .ok (.bool true) := by
  have hdstValue :
      forkDstValue I = .address evm.executionEnv.source := by
    rw [forkDstValue, solcAddressValue_masked (forkDstWord I)]
    change Value.address (AccountAddress.ofNat (forkDstMaskedWord I).toNat) =
      Value.address evm.executionEnv.source
    rw [heq]
    rw [forkHopeSource_ofNat I, ← hsource]
  simp only [evalExpr?, sender, envValue, EvalResult.bind, EvalResult.ofOption, bind, pure]
  rw [forkStoreDstInkSpot_get_dst I srcInkNew srcArtNew dstInkNew dstArtNew utab vtab
    srcInkSpot dstInkSpot, hdstValue]
  simp [evalBinaryOp?]

theorem evalExpr_fork_src_sender_eq_false_final {evm : EVM.State} {I : ExecutionEnv}
    (srcInkNew srcArtNew dstInkNew dstArtNew utab vtab srcInkSpot dstInkSpot : UInt256)
    (hsource : evm.executionEnv.source = I.source)
    (hne : forkSrcMaskedWord I ≠ hopeSourceWord I) :
    evalExpr? config
      { contract := contract,
        locals :=
          forkStoreDstInkSpot I srcInkNew srcArtNew dstInkNew dstArtNew utab vtab
            srcInkSpot dstInkSpot } evm
      (.binary .eq (.var "src") sender) = .ok (.bool false) := by
  have hneValue :
      forkSrcValue I ≠ .address evm.executionEnv.source := by
    intro hval
    have hmasked :
        Value.address (AccountAddress.ofNat (forkSrcMaskedWord I).toNat) =
        Value.address evm.executionEnv.source := by
      rw [← solcAddressValue_masked (forkSrcWord I), ← hval]
    have hword : forkSrcMaskedWord I = hopeSourceWord I := by
      apply u256_inj
      have haddrs :
          AccountAddress.ofNat (forkSrcMaskedWord I).toNat = evm.executionEnv.source := by
        injection hmasked with haddr
      have hnat := congrArg Fin.val haddrs
      unfold AccountAddress.ofNat at hnat
      change (forkSrcMaskedWord I).toNat % EVM.addressModulus =
        evm.executionEnv.source.val at hnat
      rw [Nat.mod_eq_of_lt (forkSrcMaskedWord_canonical I)] at hnat
      rw [hopeSourceWord_toNat, ← hsource]
      exact hnat
    exact hne hword
  have hbeq : (forkSrcValue I == Value.address evm.executionEnv.source) = false := by
    rw [Bool.eq_false_iff]
    intro hb
    exact hneValue (beq_iff_eq.mp hb)
  simp only [evalExpr?, sender, envValue, EvalResult.bind, EvalResult.ofOption, bind, pure]
  rw [forkStoreDstInkSpot_get_src I srcInkNew srcArtNew dstInkNew dstArtNew utab vtab
    srcInkSpot dstInkSpot]
  simp [evalBinaryOp?, hbeq]

theorem evalExpr_fork_dst_sender_eq_false_final {evm : EVM.State} {I : ExecutionEnv}
    (srcInkNew srcArtNew dstInkNew dstArtNew utab vtab srcInkSpot dstInkSpot : UInt256)
    (hsource : evm.executionEnv.source = I.source)
    (hne : forkDstMaskedWord I ≠ hopeSourceWord I) :
    evalExpr? config
      { contract := contract,
        locals :=
          forkStoreDstInkSpot I srcInkNew srcArtNew dstInkNew dstArtNew utab vtab
            srcInkSpot dstInkSpot } evm
      (.binary .eq (.var "dst") sender) = .ok (.bool false) := by
  have hneValue :
      forkDstValue I ≠ .address evm.executionEnv.source := by
    intro hval
    have hmasked :
        Value.address (AccountAddress.ofNat (forkDstMaskedWord I).toNat) =
        Value.address evm.executionEnv.source := by
      rw [← solcAddressValue_masked (forkDstWord I), ← hval]
    have hword : forkDstMaskedWord I = hopeSourceWord I := by
      apply u256_inj
      have haddrs :
          AccountAddress.ofNat (forkDstMaskedWord I).toNat = evm.executionEnv.source := by
        injection hmasked with haddr
      have hnat := congrArg Fin.val haddrs
      unfold AccountAddress.ofNat at hnat
      change (forkDstMaskedWord I).toNat % EVM.addressModulus =
        evm.executionEnv.source.val at hnat
      rw [Nat.mod_eq_of_lt (forkDstMaskedWord_canonical I)] at hnat
      rw [hopeSourceWord_toNat, ← hsource]
      exact hnat
    exact hne hword
  have hbeq : (forkDstValue I == Value.address evm.executionEnv.source) = false := by
    rw [Bool.eq_false_iff]
    intro hb
    exact hneValue (beq_iff_eq.mp hb)
  simp only [evalExpr?, sender, envValue, EvalResult.bind, EvalResult.ofOption, bind, pure]
  rw [forkStoreDstInkSpot_get_dst I srcInkNew srcArtNew dstInkNew dstArtNew utab vtab
    srcInkSpot dstInkSpot]
  simp [evalBinaryOp?, hbeq]

theorem evalExpr_fork_src_can_eq_true_final {evm : EVM.State} {I : ExecutionEnv}
    (srcInkNew srcArtNew dstInkNew dstArtNew utab vtab srcInkSpot dstInkSpot : UInt256)
    (hsource : evm.executionEnv.source = I.source)
    (hcan : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (forkSrcWishSlot I) = ⟨1⟩) :
    evalExpr? config
      { contract := contract,
        locals :=
          forkStoreDstInkSpot I srcInkNew srcArtNew dstInkNew dstArtNew utab vtab
            srcInkSpot dstInkSpot } evm
      (.binary .eq (.storage (canRef (.var "src") sender)) (.intLit 1)) =
      .ok (.bool true) := by
  simp [evalExpr?, EvalResult.bind, bind, pure, evalBinaryOp?,
    evalExpr_fork_src_can_final (evm := evm) (I := I)
      srcInkNew srcArtNew dstInkNew dstArtNew utab vtab srcInkSpot dstInkSpot hsource,
    hcan, show (⟨1⟩ : UInt256).toNat = 1 by decide]

theorem evalExpr_fork_dst_can_eq_true_final {evm : EVM.State} {I : ExecutionEnv}
    (srcInkNew srcArtNew dstInkNew dstArtNew utab vtab srcInkSpot dstInkSpot : UInt256)
    (hsource : evm.executionEnv.source = I.source)
    (hcan : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (forkDstWishSlot I) = ⟨1⟩) :
    evalExpr? config
      { contract := contract,
        locals :=
          forkStoreDstInkSpot I srcInkNew srcArtNew dstInkNew dstArtNew utab vtab
            srcInkSpot dstInkSpot } evm
      (.binary .eq (.storage (canRef (.var "dst") sender)) (.intLit 1)) =
      .ok (.bool true) := by
  simp [evalExpr?, EvalResult.bind, bind, pure, evalBinaryOp?,
    evalExpr_fork_dst_can_final (evm := evm) (I := I)
      srcInkNew srcArtNew dstInkNew dstArtNew utab vtab srcInkSpot dstInkSpot hsource,
    hcan, show (⟨1⟩ : UInt256).toNat = 1 by decide]

theorem evalExpr_fork_src_can_eq_false_final {evm : EVM.State} {I : ExecutionEnv}
    (srcInkNew srcArtNew dstInkNew dstArtNew utab vtab srcInkSpot dstInkSpot : UInt256)
    (hsource : evm.executionEnv.source = I.source)
    (hcan : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (forkSrcWishSlot I) ≠ ⟨1⟩) :
    evalExpr? config
      { contract := contract,
        locals :=
          forkStoreDstInkSpot I srcInkNew srcArtNew dstInkNew dstArtNew utab vtab
            srcInkSpot dstInkSpot } evm
      (.binary .eq (.storage (canRef (.var "src") sender)) (.intLit 1)) =
      .ok (.bool false) := by
  have hneNat :
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (forkSrcWishSlot I)).toNat ≠ 1 := by
    intro hnat
    apply hcan
    apply u256_inj
    rw [hnat]
    decide
  simp [evalExpr?, EvalResult.bind, bind, pure, evalBinaryOp?,
    evalExpr_fork_src_can_final (evm := evm) (I := I)
      srcInkNew srcArtNew dstInkNew dstArtNew utab vtab srcInkSpot dstInkSpot hsource,
    hneNat]

theorem evalExpr_fork_dst_can_eq_false_final {evm : EVM.State} {I : ExecutionEnv}
    (srcInkNew srcArtNew dstInkNew dstArtNew utab vtab srcInkSpot dstInkSpot : UInt256)
    (hsource : evm.executionEnv.source = I.source)
    (hcan : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (forkDstWishSlot I) ≠ ⟨1⟩) :
    evalExpr? config
      { contract := contract,
        locals :=
          forkStoreDstInkSpot I srcInkNew srcArtNew dstInkNew dstArtNew utab vtab
            srcInkSpot dstInkSpot } evm
      (.binary .eq (.storage (canRef (.var "dst") sender)) (.intLit 1)) =
      .ok (.bool false) := by
  have hneNat :
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (forkDstWishSlot I)).toNat ≠ 1 := by
    intro hnat
    apply hcan
    apply u256_inj
    rw [hnat]
    decide
  simp [evalExpr?, EvalResult.bind, bind, pure, evalBinaryOp?,
    evalExpr_fork_dst_can_final (evm := evm) (I := I)
      srcInkNew srcArtNew dstInkNew dstArtNew utab vtab srcInkSpot dstInkSpot hsource,
    hneNat]

theorem evalExpr_fork_src_wish_true_src_final {evm : EVM.State} {I : ExecutionEnv}
    (srcInkNew srcArtNew dstInkNew dstArtNew utab vtab srcInkSpot dstInkSpot : UInt256)
    (hsource : evm.executionEnv.source = I.source)
    (heq : forkSrcMaskedWord I = hopeSourceWord I) :
    evalExpr? config
      { contract := contract,
        locals :=
          forkStoreDstInkSpot I srcInkNew srcArtNew dstInkNew dstArtNew utab vtab
            srcInkSpot dstInkSpot } evm
      (wishExpr (.var "src") sender) = .ok (.bool true) := by
  exact vatEvalExpr_or_true_left
    (lhs := .binary .eq (.var "src") sender)
    (rhs := .binary .eq (.storage (canRef (.var "src") sender)) (.intLit 1))
    (evalExpr_fork_src_sender_eq_true_final (evm := evm) (I := I)
      srcInkNew srcArtNew dstInkNew dstArtNew utab vtab srcInkSpot dstInkSpot hsource heq)

theorem evalExpr_fork_dst_wish_true_dst_final {evm : EVM.State} {I : ExecutionEnv}
    (srcInkNew srcArtNew dstInkNew dstArtNew utab vtab srcInkSpot dstInkSpot : UInt256)
    (hsource : evm.executionEnv.source = I.source)
    (heq : forkDstMaskedWord I = hopeSourceWord I) :
    evalExpr? config
      { contract := contract,
        locals :=
          forkStoreDstInkSpot I srcInkNew srcArtNew dstInkNew dstArtNew utab vtab
            srcInkSpot dstInkSpot } evm
      (wishExpr (.var "dst") sender) = .ok (.bool true) := by
  exact vatEvalExpr_or_true_left
    (lhs := .binary .eq (.var "dst") sender)
    (rhs := .binary .eq (.storage (canRef (.var "dst") sender)) (.intLit 1))
    (evalExpr_fork_dst_sender_eq_true_final (evm := evm) (I := I)
      srcInkNew srcArtNew dstInkNew dstArtNew utab vtab srcInkSpot dstInkSpot hsource heq)

theorem evalExpr_fork_src_wish_true_can_final {evm : EVM.State} {I : ExecutionEnv}
    (srcInkNew srcArtNew dstInkNew dstArtNew utab vtab srcInkSpot dstInkSpot : UInt256)
    (hsource : evm.executionEnv.source = I.source)
    (hne : forkSrcMaskedWord I ≠ hopeSourceWord I)
    (hcan : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (forkSrcWishSlot I) = ⟨1⟩) :
    evalExpr? config
      { contract := contract,
        locals :=
          forkStoreDstInkSpot I srcInkNew srcArtNew dstInkNew dstArtNew utab vtab
            srcInkSpot dstInkSpot } evm
      (wishExpr (.var "src") sender) = .ok (.bool true) := by
  exact vatEvalExpr_or_false_right
    (lhs := .binary .eq (.var "src") sender)
    (rhs := .binary .eq (.storage (canRef (.var "src") sender)) (.intLit 1))
    (evalExpr_fork_src_sender_eq_false_final (evm := evm) (I := I)
      srcInkNew srcArtNew dstInkNew dstArtNew utab vtab srcInkSpot dstInkSpot hsource hne)
    (evalExpr_fork_src_can_eq_true_final (evm := evm) (I := I)
      srcInkNew srcArtNew dstInkNew dstArtNew utab vtab srcInkSpot dstInkSpot hsource hcan)

theorem evalExpr_fork_dst_wish_true_can_final {evm : EVM.State} {I : ExecutionEnv}
    (srcInkNew srcArtNew dstInkNew dstArtNew utab vtab srcInkSpot dstInkSpot : UInt256)
    (hsource : evm.executionEnv.source = I.source)
    (hne : forkDstMaskedWord I ≠ hopeSourceWord I)
    (hcan : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (forkDstWishSlot I) = ⟨1⟩) :
    evalExpr? config
      { contract := contract,
        locals :=
          forkStoreDstInkSpot I srcInkNew srcArtNew dstInkNew dstArtNew utab vtab
            srcInkSpot dstInkSpot } evm
      (wishExpr (.var "dst") sender) = .ok (.bool true) := by
  exact vatEvalExpr_or_false_right
    (lhs := .binary .eq (.var "dst") sender)
    (rhs := .binary .eq (.storage (canRef (.var "dst") sender)) (.intLit 1))
    (evalExpr_fork_dst_sender_eq_false_final (evm := evm) (I := I)
      srcInkNew srcArtNew dstInkNew dstArtNew utab vtab srcInkSpot dstInkSpot hsource hne)
    (evalExpr_fork_dst_can_eq_true_final (evm := evm) (I := I)
      srcInkNew srcArtNew dstInkNew dstArtNew utab vtab srcInkSpot dstInkSpot hsource hcan)

theorem evalExpr_fork_src_wish_false_final {evm : EVM.State} {I : ExecutionEnv}
    (srcInkNew srcArtNew dstInkNew dstArtNew utab vtab srcInkSpot dstInkSpot : UInt256)
    (hsource : evm.executionEnv.source = I.source)
    (hne : forkSrcMaskedWord I ≠ hopeSourceWord I)
    (hcan : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (forkSrcWishSlot I) ≠ ⟨1⟩) :
    evalExpr? config
      { contract := contract,
        locals :=
          forkStoreDstInkSpot I srcInkNew srcArtNew dstInkNew dstArtNew utab vtab
            srcInkSpot dstInkSpot } evm
      (wishExpr (.var "src") sender) = .ok (.bool false) := by
  exact vatEvalExpr_or_false_right
    (lhs := .binary .eq (.var "src") sender)
    (rhs := .binary .eq (.storage (canRef (.var "src") sender)) (.intLit 1))
    (evalExpr_fork_src_sender_eq_false_final (evm := evm) (I := I)
      srcInkNew srcArtNew dstInkNew dstArtNew utab vtab srcInkSpot dstInkSpot hsource hne)
    (evalExpr_fork_src_can_eq_false_final (evm := evm) (I := I)
      srcInkNew srcArtNew dstInkNew dstArtNew utab vtab srcInkSpot dstInkSpot hsource hcan)

theorem evalExpr_fork_dst_wish_false_final {evm : EVM.State} {I : ExecutionEnv}
    (srcInkNew srcArtNew dstInkNew dstArtNew utab vtab srcInkSpot dstInkSpot : UInt256)
    (hsource : evm.executionEnv.source = I.source)
    (hne : forkDstMaskedWord I ≠ hopeSourceWord I)
    (hcan : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (forkDstWishSlot I) ≠ ⟨1⟩) :
    evalExpr? config
      { contract := contract,
        locals :=
          forkStoreDstInkSpot I srcInkNew srcArtNew dstInkNew dstArtNew utab vtab
            srcInkSpot dstInkSpot } evm
      (wishExpr (.var "dst") sender) = .ok (.bool false) := by
  exact vatEvalExpr_or_false_right
    (lhs := .binary .eq (.var "dst") sender)
    (rhs := .binary .eq (.storage (canRef (.var "dst") sender)) (.intLit 1))
    (evalExpr_fork_dst_sender_eq_false_final (evm := evm) (I := I)
      srcInkNew srcArtNew dstInkNew dstArtNew utab vtab srcInkSpot dstInkSpot hsource hne)
    (evalExpr_fork_dst_can_eq_false_final (evm := evm) (I := I)
      srcInkNew srcArtNew dstInkNew dstArtNew utab vtab srcInkSpot dstInkSpot hsource hcan)

theorem evalExpr_fork_wish_both_true_final {evm : EVM.State} {I : ExecutionEnv}
    (srcInkNew srcArtNew dstInkNew dstArtNew utab vtab srcInkSpot dstInkSpot : UInt256)
    (hsrcWish :
      evalExpr? config
        { contract := contract,
          locals :=
            forkStoreDstInkSpot I srcInkNew srcArtNew dstInkNew dstArtNew utab vtab
              srcInkSpot dstInkSpot } evm
        (wishExpr (.var "src") sender) = .ok (.bool true))
    (hdstWish :
      evalExpr? config
        { contract := contract,
          locals :=
            forkStoreDstInkSpot I srcInkNew srcArtNew dstInkNew dstArtNew utab vtab
              srcInkSpot dstInkSpot } evm
        (wishExpr (.var "dst") sender) = .ok (.bool true)) :
    evalExpr? config
      { contract := contract,
        locals :=
          forkStoreDstInkSpot I srcInkNew srcArtNew dstInkNew dstArtNew utab vtab
            srcInkSpot dstInkSpot } evm
      (bothExpr (wishExpr (.var "src") sender) (wishExpr (.var "dst") sender)) =
      .ok (.bool true) := by
  exact vatEvalExpr_and_true hsrcWish hdstWish

theorem vatEvalExpr_and_false_left {evm : EVM.State} {locals : Store}
    {lhs rhs : Expr}
    (hlhs : evalExpr? config { contract := contract, locals := locals } evm lhs =
      .ok (.bool false)) :
    evalExpr? config { contract := contract, locals := locals } evm (.binary .and lhs rhs) =
      .ok (.bool false) := by
  simp [evalExpr?, EvalResult.bind, bind, pure, hlhs]

theorem vatEvalExpr_and_true_false_right {evm : EVM.State} {locals : Store}
    {lhs rhs : Expr}
    (hlhs : evalExpr? config { contract := contract, locals := locals } evm lhs =
      .ok (.bool true))
    (hrhs : evalExpr? config { contract := contract, locals := locals } evm rhs =
      .ok (.bool false)) :
    evalExpr? config { contract := contract, locals := locals } evm (.binary .and lhs rhs) =
      .ok (.bool false) := by
  simp [evalExpr?, EvalResult.bind, bind, pure, hlhs, hrhs]

theorem evalExpr_fork_wish_both_false_left_final {evm : EVM.State} {I : ExecutionEnv}
    (srcInkNew srcArtNew dstInkNew dstArtNew utab vtab srcInkSpot dstInkSpot : UInt256)
    (hsrcWish :
      evalExpr? config
        { contract := contract,
          locals :=
            forkStoreDstInkSpot I srcInkNew srcArtNew dstInkNew dstArtNew utab vtab
              srcInkSpot dstInkSpot } evm
        (wishExpr (.var "src") sender) = .ok (.bool false)) :
    evalExpr? config
      { contract := contract,
        locals :=
          forkStoreDstInkSpot I srcInkNew srcArtNew dstInkNew dstArtNew utab vtab
            srcInkSpot dstInkSpot } evm
      (bothExpr (wishExpr (.var "src") sender) (wishExpr (.var "dst") sender)) =
      .ok (.bool false) := by
  exact vatEvalExpr_and_false_left hsrcWish

theorem evalExpr_fork_wish_both_false_right_final {evm : EVM.State} {I : ExecutionEnv}
    (srcInkNew srcArtNew dstInkNew dstArtNew utab vtab srcInkSpot dstInkSpot : UInt256)
    (hsrcWish :
      evalExpr? config
        { contract := contract,
          locals :=
            forkStoreDstInkSpot I srcInkNew srcArtNew dstInkNew dstArtNew utab vtab
              srcInkSpot dstInkSpot } evm
        (wishExpr (.var "src") sender) = .ok (.bool true))
    (hdstWish :
      evalExpr? config
        { contract := contract,
          locals :=
            forkStoreDstInkSpot I srcInkNew srcArtNew dstInkNew dstArtNew utab vtab
              srcInkSpot dstInkSpot } evm
        (wishExpr (.var "dst") sender) = .ok (.bool false)) :
    evalExpr? config
      { contract := contract,
        locals :=
          forkStoreDstInkSpot I srcInkNew srcArtNew dstInkNew dstArtNew utab vtab
            srcInkSpot dstInkSpot } evm
      (bothExpr (wishExpr (.var "src") sender) (wishExpr (.var "dst") sender)) =
      .ok (.bool false) := by
  exact vatEvalExpr_and_true_false_right hsrcWish hdstWish

theorem forkSrcWishWord_true_src {σ : AccountMap} {I : ExecutionEnv}
    (heq : forkSrcMaskedWord I = hopeSourceWord I) :
    forkSrcWishWord σ I ≠ ⟨0⟩ := by
  by_cases hcan : vatSlotWord (forkSrcWishSlot I) σ I = ⟨1⟩
  · unfold forkSrcWishWord
    rw [heq, hcan, u256_eq_refl, u256_eq_refl]
    native_decide
  · unfold forkSrcWishWord
    rw [heq, u256_eq_refl, u256_eq_of_ne hcan]
    rw [u256_lor_comm, u256_lor_zero]
    exact one_ne_zero_uint

theorem forkSrcWishWord_true_can {σ : AccountMap} {I : ExecutionEnv}
    (hcan : vatSlotWord (forkSrcWishSlot I) σ I = ⟨1⟩) :
    forkSrcWishWord σ I ≠ ⟨0⟩ := by
  by_cases hsrc : forkSrcMaskedWord I = hopeSourceWord I
  · unfold forkSrcWishWord
    rw [hcan, hsrc, u256_eq_refl, u256_eq_refl]
    native_decide
  · unfold forkSrcWishWord
    rw [hcan, u256_eq_refl, u256_eq_of_ne hsrc]
    rw [u256_lor_zero]
    exact one_ne_zero_uint

theorem forkDstWishWord_true_dst {σ : AccountMap} {I : ExecutionEnv}
    (heq : forkDstMaskedWord I = hopeSourceWord I) :
    forkDstWishWord σ I ≠ ⟨0⟩ := by
  by_cases hcan : vatSlotWord (forkDstWishSlot I) σ I = ⟨1⟩
  · unfold forkDstWishWord
    rw [heq, hcan, u256_eq_refl, u256_eq_refl]
    native_decide
  · unfold forkDstWishWord
    rw [heq, u256_eq_refl, u256_eq_of_ne hcan]
    rw [u256_lor_comm, u256_lor_zero]
    exact one_ne_zero_uint

theorem forkDstWishWord_true_can {σ : AccountMap} {I : ExecutionEnv}
    (hcan : vatSlotWord (forkDstWishSlot I) σ I = ⟨1⟩) :
    forkDstWishWord σ I ≠ ⟨0⟩ := by
  by_cases hdst : forkDstMaskedWord I = hopeSourceWord I
  · unfold forkDstWishWord
    rw [hcan, hdst, u256_eq_refl, u256_eq_refl]
    native_decide
  · unfold forkDstWishWord
    rw [hcan, u256_eq_refl, u256_eq_of_ne hdst]
    rw [u256_lor_zero]
    exact one_ne_zero_uint

theorem forkSrcWishWord_false {σ : AccountMap} {I : ExecutionEnv}
    (hne : forkSrcMaskedWord I ≠ hopeSourceWord I)
    (hcan : vatSlotWord (forkSrcWishSlot I) σ I ≠ ⟨1⟩) :
    forkSrcWishWord σ I = ⟨0⟩ := by
  unfold forkSrcWishWord
  rw [u256_eq_of_ne hcan, u256_eq_of_ne hne]
  rfl

theorem forkDstWishWord_false {σ : AccountMap} {I : ExecutionEnv}
    (hne : forkDstMaskedWord I ≠ hopeSourceWord I)
    (hcan : vatSlotWord (forkDstWishSlot I) σ I ≠ ⟨1⟩) :
    forkDstWishWord σ I = ⟨0⟩ := by
  unfold forkDstWishWord
  rw [u256_eq_of_ne hcan, u256_eq_of_ne hne]
  rfl

theorem fork_u256_land_zero_left (a : UInt256) :
    UInt256.land (⟨0⟩ : UInt256) a = ⟨0⟩ := by
  apply u256_inj
  rw [u256_land_toNat]
  change Nat.land 0 a.toNat % UInt256.size = 0
  have hzero : Nat.land 0 a.toNat = 0 := by
    apply Nat.eq_of_testBit_eq
    intro i
    change (0 &&& a.toNat).testBit i = (0 : Nat).testBit i
    rw [Nat.testBit_and]
    simp
  simpa [hzero]

theorem fork_u256_land_zero_right (a : UInt256) :
    UInt256.land a (⟨0⟩ : UInt256) = ⟨0⟩ := by
  rw [u256_land_comm]
  exact fork_u256_land_zero_left a

theorem fork_u256_land_left_ne_zero_of_land_ne_zero {a b : UInt256}
    (h : UInt256.land a b ≠ ⟨0⟩) :
    a ≠ ⟨0⟩ := by
  intro hzero
  rw [hzero, fork_u256_land_zero_left] at h
  exact h rfl

theorem fork_u256_land_right_ne_zero_of_land_ne_zero {a b : UInt256}
    (h : UInt256.land a b ≠ ⟨0⟩) :
    b ≠ ⟨0⟩ := by
  intro hzero
  rw [hzero, fork_u256_land_zero_right] at h
  exact h rfl

theorem forkBothWishWord_false_src {σ : AccountMap} {I : ExecutionEnv}
    (hsrc : forkSrcWishWord σ I = ⟨0⟩) :
    forkBothWishWord σ I = ⟨0⟩ := by
  unfold forkBothWishWord
  rw [hsrc]
  exact fork_u256_land_zero_right (forkDstWishWord σ I)

theorem forkBothWishWord_false_dst {σ : AccountMap} {I : ExecutionEnv}
    (hdst : forkDstWishWord σ I = ⟨0⟩) :
    forkBothWishWord σ I = ⟨0⟩ := by
  unfold forkBothWishWord
  rw [hdst]
  exact fork_u256_land_zero_left (forkSrcWishWord σ I)

theorem forkBothWishWord_true {σ : AccountMap} {I : ExecutionEnv}
    (hsrc : forkSrcWishWord σ I ≠ ⟨0⟩)
    (hdst : forkDstWishWord σ I ≠ ⟨0⟩) :
    forkBothWishWord σ I ≠ ⟨0⟩ := by
  unfold forkBothWishWord
  by_cases hsrcZero : forkSrcWishWord σ I = ⟨0⟩
  · exact False.elim (hsrc hsrcZero)
  · by_cases hdstZero : forkDstWishWord σ I = ⟨0⟩
    · exact False.elim (hdst hdstZero)
    · have hsrcOne : forkSrcWishWord σ I = ⟨1⟩ := by
        unfold forkSrcWishWord at hsrcZero ⊢
        by_cases hcan : vatSlotWord (forkSrcWishSlot I) σ I = ⟨1⟩
        · rw [hcan, u256_eq_refl]
          by_cases haddr : forkSrcMaskedWord I = hopeSourceWord I
          · rw [haddr, u256_eq_refl]
            native_decide
          · rw [u256_eq_of_ne haddr]
            native_decide
        · rw [u256_eq_of_ne hcan]
          by_cases haddr : forkSrcMaskedWord I = hopeSourceWord I
          · rw [haddr, u256_eq_refl]
            native_decide
          · rw [u256_eq_of_ne hcan, u256_eq_of_ne haddr] at hsrcZero
            have hz : UInt256.lor (⟨0⟩ : UInt256) ⟨0⟩ = ⟨0⟩ := by native_decide
            exact False.elim (hsrcZero hz)
      have hdstOne : forkDstWishWord σ I = ⟨1⟩ := by
        unfold forkDstWishWord at hdstZero ⊢
        by_cases hcan : vatSlotWord (forkDstWishSlot I) σ I = ⟨1⟩
        · rw [hcan, u256_eq_refl]
          by_cases haddr : forkDstMaskedWord I = hopeSourceWord I
          · rw [haddr, u256_eq_refl]
            native_decide
          · rw [u256_eq_of_ne haddr]
            native_decide
        · rw [u256_eq_of_ne hcan]
          by_cases haddr : forkDstMaskedWord I = hopeSourceWord I
          · rw [haddr, u256_eq_refl]
            native_decide
          · rw [u256_eq_of_ne hcan, u256_eq_of_ne haddr] at hdstZero
            have hz : UInt256.lor (⟨0⟩ : UInt256) ⟨0⟩ = ⟨0⟩ := by native_decide
            exact False.elim (hdstZero hz)
      rw [hsrcOne, hdstOne]
      native_decide

theorem forkBothWishWord_true_src {σ : AccountMap} {I : ExecutionEnv}
    (h : forkBothWishWord σ I ≠ ⟨0⟩) :
    forkSrcWishWord σ I ≠ ⟨0⟩ := by
  unfold forkBothWishWord at h
  exact fork_u256_land_right_ne_zero_of_land_ne_zero h

theorem forkBothWishWord_true_dst {σ : AccountMap} {I : ExecutionEnv}
    (h : forkBothWishWord σ I ≠ ⟨0⟩) :
    forkDstWishWord σ I ≠ ⟨0⟩ := by
  unfold forkBothWishWord at h
  exact fork_u256_land_left_ne_zero_of_land_ne_zero h

theorem evalExpr_fork_src_wish_true_of_word_final {evm : EVM.State}
    {σ : AccountMap} {I : ExecutionEnv}
    (srcInkNew srcArtNew dstInkNew dstArtNew utab vtab srcInkSpot dstInkSpot : UInt256)
    (hsource : evm.executionEnv.source = I.source)
    (hload :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (forkSrcWishSlot I) =
        vatSlotWord (forkSrcWishSlot I) σ I)
    (hword : forkSrcWishWord σ I ≠ ⟨0⟩) :
    evalExpr? config
      { contract := contract,
        locals :=
          forkStoreDstInkSpot I srcInkNew srcArtNew dstInkNew dstArtNew utab vtab
            srcInkSpot dstInkSpot } evm
      (wishExpr (.var "src") sender) = .ok (.bool true) := by
  by_cases hsrc : forkSrcMaskedWord I = hopeSourceWord I
  · exact evalExpr_fork_src_wish_true_src_final
      (evm := evm) (I := I) srcInkNew srcArtNew dstInkNew dstArtNew
      utab vtab srcInkSpot dstInkSpot hsource hsrc
  · by_cases hcan : vatSlotWord (forkSrcWishSlot I) σ I = ⟨1⟩
    · exact evalExpr_fork_src_wish_true_can_final
        (evm := evm) (I := I) srcInkNew srcArtNew dstInkNew dstArtNew
        utab vtab srcInkSpot dstInkSpot hsource hsrc
        (by rw [hload, hcan])
    · exact False.elim (hword (forkSrcWishWord_false hsrc hcan))

theorem evalExpr_fork_dst_wish_true_of_word_final {evm : EVM.State}
    {σ : AccountMap} {I : ExecutionEnv}
    (srcInkNew srcArtNew dstInkNew dstArtNew utab vtab srcInkSpot dstInkSpot : UInt256)
    (hsource : evm.executionEnv.source = I.source)
    (hload :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (forkDstWishSlot I) =
        vatSlotWord (forkDstWishSlot I) σ I)
    (hword : forkDstWishWord σ I ≠ ⟨0⟩) :
    evalExpr? config
      { contract := contract,
        locals :=
          forkStoreDstInkSpot I srcInkNew srcArtNew dstInkNew dstArtNew utab vtab
            srcInkSpot dstInkSpot } evm
      (wishExpr (.var "dst") sender) = .ok (.bool true) := by
  by_cases hdst : forkDstMaskedWord I = hopeSourceWord I
  · exact evalExpr_fork_dst_wish_true_dst_final
      (evm := evm) (I := I) srcInkNew srcArtNew dstInkNew dstArtNew
      utab vtab srcInkSpot dstInkSpot hsource hdst
  · by_cases hcan : vatSlotWord (forkDstWishSlot I) σ I = ⟨1⟩
    · exact evalExpr_fork_dst_wish_true_can_final
        (evm := evm) (I := I) srcInkNew srcArtNew dstInkNew dstArtNew
        utab vtab srcInkSpot dstInkSpot hsource hdst
        (by rw [hload, hcan])
    · exact False.elim (hword (forkDstWishWord_false hdst hcan))

theorem evalExpr_fork_wish_both_true_of_word_final {evm : EVM.State}
    {σ : AccountMap} {I : ExecutionEnv}
    (srcInkNew srcArtNew dstInkNew dstArtNew utab vtab srcInkSpot dstInkSpot : UInt256)
    (hsource : evm.executionEnv.source = I.source)
    (hloadSrc :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (forkSrcWishSlot I) =
        vatSlotWord (forkSrcWishSlot I) σ I)
    (hloadDst :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (forkDstWishSlot I) =
        vatSlotWord (forkDstWishSlot I) σ I)
    (hword : forkBothWishWord σ I ≠ ⟨0⟩) :
    evalExpr? config
      { contract := contract,
        locals :=
          forkStoreDstInkSpot I srcInkNew srcArtNew dstInkNew dstArtNew utab vtab
            srcInkSpot dstInkSpot } evm
      (bothExpr (wishExpr (.var "src") sender) (wishExpr (.var "dst") sender)) =
      .ok (.bool true) := by
  exact evalExpr_fork_wish_both_true_final
    (evm := evm) (I := I) srcInkNew srcArtNew dstInkNew dstArtNew utab vtab
    srcInkSpot dstInkSpot
    (evalExpr_fork_src_wish_true_of_word_final (evm := evm) (σ := σ)
      srcInkNew srcArtNew dstInkNew dstArtNew utab vtab srcInkSpot dstInkSpot
      hsource hloadSrc (forkBothWishWord_true_src hword))
    (evalExpr_fork_dst_wish_true_of_word_final (evm := evm) (σ := σ)
      srcInkNew srcArtNew dstInkNew dstArtNew utab vtab srcInkSpot dstInkSpot
      hsource hloadDst (forkBothWishWord_true_dst hword))

theorem evalExpr_fork_src_wish_false_of_word_zero_final {evm : EVM.State}
    {σ : AccountMap} {I : ExecutionEnv}
    (srcInkNew srcArtNew dstInkNew dstArtNew utab vtab srcInkSpot dstInkSpot : UInt256)
    (hsource : evm.executionEnv.source = I.source)
    (hload :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (forkSrcWishSlot I) =
        vatSlotWord (forkSrcWishSlot I) σ I)
    (hword : forkSrcWishWord σ I = ⟨0⟩) :
    evalExpr? config
      { contract := contract,
        locals :=
          forkStoreDstInkSpot I srcInkNew srcArtNew dstInkNew dstArtNew utab vtab
            srcInkSpot dstInkSpot } evm
      (wishExpr (.var "src") sender) = .ok (.bool false) := by
  by_cases hsrc : forkSrcMaskedWord I = hopeSourceWord I
  · exact False.elim ((forkSrcWishWord_true_src (σ := σ) hsrc) hword)
  · by_cases hcan : vatSlotWord (forkSrcWishSlot I) σ I = ⟨1⟩
    · exact False.elim ((forkSrcWishWord_true_can (σ := σ) hcan) hword)
    · exact evalExpr_fork_src_wish_false_final
        (evm := evm) (I := I) srcInkNew srcArtNew dstInkNew dstArtNew
        utab vtab srcInkSpot dstInkSpot hsource hsrc
        (by intro hloadOne; exact hcan (by rw [← hload, hloadOne]))

theorem evalExpr_fork_dst_wish_false_of_word_zero_final {evm : EVM.State}
    {σ : AccountMap} {I : ExecutionEnv}
    (srcInkNew srcArtNew dstInkNew dstArtNew utab vtab srcInkSpot dstInkSpot : UInt256)
    (hsource : evm.executionEnv.source = I.source)
    (hload :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (forkDstWishSlot I) =
        vatSlotWord (forkDstWishSlot I) σ I)
    (hword : forkDstWishWord σ I = ⟨0⟩) :
    evalExpr? config
      { contract := contract,
        locals :=
          forkStoreDstInkSpot I srcInkNew srcArtNew dstInkNew dstArtNew utab vtab
            srcInkSpot dstInkSpot } evm
      (wishExpr (.var "dst") sender) = .ok (.bool false) := by
  by_cases hdst : forkDstMaskedWord I = hopeSourceWord I
  · exact False.elim ((forkDstWishWord_true_dst (σ := σ) hdst) hword)
  · by_cases hcan : vatSlotWord (forkDstWishSlot I) σ I = ⟨1⟩
    · exact False.elim ((forkDstWishWord_true_can (σ := σ) hcan) hword)
    · exact evalExpr_fork_dst_wish_false_final
        (evm := evm) (I := I) srcInkNew srcArtNew dstInkNew dstArtNew
        utab vtab srcInkSpot dstInkSpot hsource hdst
        (by intro hloadOne; exact hcan (by rw [← hload, hloadOne]))

theorem evalExpr_fork_wish_both_false_of_word_zero_final {evm : EVM.State}
    {σ : AccountMap} {I : ExecutionEnv}
    (srcInkNew srcArtNew dstInkNew dstArtNew utab vtab srcInkSpot dstInkSpot : UInt256)
    (hsource : evm.executionEnv.source = I.source)
    (hloadSrc :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (forkSrcWishSlot I) =
        vatSlotWord (forkSrcWishSlot I) σ I)
    (hloadDst :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (forkDstWishSlot I) =
        vatSlotWord (forkDstWishSlot I) σ I)
    (hword : forkBothWishWord σ I = ⟨0⟩) :
    evalExpr? config
      { contract := contract,
        locals :=
          forkStoreDstInkSpot I srcInkNew srcArtNew dstInkNew dstArtNew utab vtab
            srcInkSpot dstInkSpot } evm
      (bothExpr (wishExpr (.var "src") sender) (wishExpr (.var "dst") sender)) =
      .ok (.bool false) := by
  by_cases hsrcZero : forkSrcWishWord σ I = ⟨0⟩
  · exact evalExpr_fork_wish_both_false_left_final
      (evm := evm) (I := I) srcInkNew srcArtNew dstInkNew dstArtNew utab vtab
      srcInkSpot dstInkSpot
      (evalExpr_fork_src_wish_false_of_word_zero_final (evm := evm) (σ := σ)
        srcInkNew srcArtNew dstInkNew dstArtNew utab vtab srcInkSpot dstInkSpot
        hsource hloadSrc hsrcZero)
  · by_cases hdstZero : forkDstWishWord σ I = ⟨0⟩
    · exact evalExpr_fork_wish_both_false_right_final
        (evm := evm) (I := I) srcInkNew srcArtNew dstInkNew dstArtNew utab vtab
        srcInkSpot dstInkSpot
        (evalExpr_fork_src_wish_true_of_word_final (evm := evm) (σ := σ)
          srcInkNew srcArtNew dstInkNew dstArtNew utab vtab srcInkSpot dstInkSpot
          hsource hloadSrc hsrcZero)
        (evalExpr_fork_dst_wish_false_of_word_zero_final (evm := evm) (σ := σ)
          srcInkNew srcArtNew dstInkNew dstArtNew utab vtab srcInkSpot dstInkSpot
          hsource hloadDst hdstZero)
    · exact False.elim ((forkBothWishWord_true hsrcZero hdstZero) hword)

theorem evalExpr_fork_src_can_final_store {evm : EVM.State} {I : ExecutionEnv}
    (srcInkNew srcArtNew dstInkNew dstArtNew
      srcArtFinal dstArtFinal srcInkFinal dstInkFinal
      utab vtab srcInkSpot dstInkSpot : UInt256)
    (hsource : evm.executionEnv.source = I.source) :
    evalExpr? config
      { contract := contract,
        locals :=
          forkStoreDstInkSpotFinal I srcInkNew srcArtNew dstInkNew dstArtNew
            srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab vtab srcInkSpot
            dstInkSpot } evm
      (.storage (canRef (.var "src") sender)) =
      .ok (.int (Int.ofNat
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (forkSrcWishSlot I)).toNat)) := by
  let locals :=
    forkStoreDstInkSpotFinal I srcInkNew srcArtNew dstInkNew dstArtNew
      srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab vtab srcInkSpot dstInkSpot
  exact evalExpr_storage_scalar_value
    (hbase := by
      change locals.get? "can" = none
      simpa [locals] using
        forkStoreDstInkSpotFinal_get_can I srcInkNew srcArtNew dstInkNew dstArtNew
          srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab vtab srcInkSpot
          dstInkSpot)
    (her := evalStorageRef_fork_src_can_locals evm I locals hsource (by
      simpa [locals] using
        forkStoreDstInkSpotFinal_get_src I srcInkNew srcArtNew dstInkNew dstArtNew
          srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab vtab srcInkSpot
          dstInkSpot))
    (hty := forkStorageType_can I (forkSrcWishEvaledRef I) (Or.inl rfl))
    (hloc := forkStorageLayout_src_can I)
    (hload := vatStorageLocLoad_uint256 evm (forkSrcWishSlot I))

theorem evalExpr_fork_dst_can_final_store {evm : EVM.State} {I : ExecutionEnv}
    (srcInkNew srcArtNew dstInkNew dstArtNew
      srcArtFinal dstArtFinal srcInkFinal dstInkFinal
      utab vtab srcInkSpot dstInkSpot : UInt256)
    (hsource : evm.executionEnv.source = I.source) :
    evalExpr? config
      { contract := contract,
        locals :=
          forkStoreDstInkSpotFinal I srcInkNew srcArtNew dstInkNew dstArtNew
            srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab vtab srcInkSpot
            dstInkSpot } evm
      (.storage (canRef (.var "dst") sender)) =
      .ok (.int (Int.ofNat
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (forkDstWishSlot I)).toNat)) := by
  let locals :=
    forkStoreDstInkSpotFinal I srcInkNew srcArtNew dstInkNew dstArtNew
      srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab vtab srcInkSpot dstInkSpot
  exact evalExpr_storage_scalar_value
    (hbase := by
      change locals.get? "can" = none
      simpa [locals] using
        forkStoreDstInkSpotFinal_get_can I srcInkNew srcArtNew dstInkNew dstArtNew
          srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab vtab srcInkSpot
          dstInkSpot)
    (her := evalStorageRef_fork_dst_can_locals evm I locals hsource (by
      simpa [locals] using
        forkStoreDstInkSpotFinal_get_dst I srcInkNew srcArtNew dstInkNew dstArtNew
          srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab vtab srcInkSpot
          dstInkSpot))
    (hty := forkStorageType_can I (forkDstWishEvaledRef I) (Or.inr rfl))
    (hloc := forkStorageLayout_dst_can I)
    (hload := vatStorageLocLoad_uint256 evm (forkDstWishSlot I))

theorem evalExpr_fork_src_sender_eq_true_final_store {evm : EVM.State} {I : ExecutionEnv}
    (srcInkNew srcArtNew dstInkNew dstArtNew
      srcArtFinal dstArtFinal srcInkFinal dstInkFinal
      utab vtab srcInkSpot dstInkSpot : UInt256)
    (hsource : evm.executionEnv.source = I.source)
    (heq : forkSrcMaskedWord I = hopeSourceWord I) :
    evalExpr? config
      { contract := contract,
        locals :=
          forkStoreDstInkSpotFinal I srcInkNew srcArtNew dstInkNew dstArtNew
            srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab vtab srcInkSpot
            dstInkSpot } evm
      (.binary .eq (.var "src") sender) = .ok (.bool true) := by
  have hsrcValue :
      forkSrcValue I = .address evm.executionEnv.source := by
    rw [forkSrcValue, solcAddressValue_masked (forkSrcWord I)]
    change Value.address (AccountAddress.ofNat (forkSrcMaskedWord I).toNat) =
      Value.address evm.executionEnv.source
    rw [heq]
    rw [forkHopeSource_ofNat I, ← hsource]
  simp only [evalExpr?, sender, envValue, EvalResult.bind, EvalResult.ofOption, bind, pure]
  rw [forkStoreDstInkSpotFinal_get_src I srcInkNew srcArtNew dstInkNew dstArtNew
    srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab vtab srcInkSpot dstInkSpot,
    hsrcValue]
  simp [evalBinaryOp?]

theorem evalExpr_fork_dst_sender_eq_true_final_store {evm : EVM.State} {I : ExecutionEnv}
    (srcInkNew srcArtNew dstInkNew dstArtNew
      srcArtFinal dstArtFinal srcInkFinal dstInkFinal
      utab vtab srcInkSpot dstInkSpot : UInt256)
    (hsource : evm.executionEnv.source = I.source)
    (heq : forkDstMaskedWord I = hopeSourceWord I) :
    evalExpr? config
      { contract := contract,
        locals :=
          forkStoreDstInkSpotFinal I srcInkNew srcArtNew dstInkNew dstArtNew
            srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab vtab srcInkSpot
            dstInkSpot } evm
      (.binary .eq (.var "dst") sender) = .ok (.bool true) := by
  have hdstValue :
      forkDstValue I = .address evm.executionEnv.source := by
    rw [forkDstValue, solcAddressValue_masked (forkDstWord I)]
    change Value.address (AccountAddress.ofNat (forkDstMaskedWord I).toNat) =
      Value.address evm.executionEnv.source
    rw [heq]
    rw [forkHopeSource_ofNat I, ← hsource]
  simp only [evalExpr?, sender, envValue, EvalResult.bind, EvalResult.ofOption, bind, pure]
  rw [forkStoreDstInkSpotFinal_get_dst I srcInkNew srcArtNew dstInkNew dstArtNew
    srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab vtab srcInkSpot dstInkSpot,
    hdstValue]
  simp [evalBinaryOp?]

theorem evalExpr_fork_src_sender_eq_false_final_store {evm : EVM.State} {I : ExecutionEnv}
    (srcInkNew srcArtNew dstInkNew dstArtNew
      srcArtFinal dstArtFinal srcInkFinal dstInkFinal
      utab vtab srcInkSpot dstInkSpot : UInt256)
    (hsource : evm.executionEnv.source = I.source)
    (hne : forkSrcMaskedWord I ≠ hopeSourceWord I) :
    evalExpr? config
      { contract := contract,
        locals :=
          forkStoreDstInkSpotFinal I srcInkNew srcArtNew dstInkNew dstArtNew
            srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab vtab srcInkSpot
            dstInkSpot } evm
      (.binary .eq (.var "src") sender) = .ok (.bool false) := by
  have hneValue :
      forkSrcValue I ≠ .address evm.executionEnv.source := by
    intro hval
    have hmasked :
        Value.address (AccountAddress.ofNat (forkSrcMaskedWord I).toNat) =
        Value.address evm.executionEnv.source := by
      rw [← solcAddressValue_masked (forkSrcWord I), ← hval]
    have hword : forkSrcMaskedWord I = hopeSourceWord I := by
      apply u256_inj
      have haddrs :
          AccountAddress.ofNat (forkSrcMaskedWord I).toNat = evm.executionEnv.source := by
        injection hmasked with haddr
      have hnat := congrArg Fin.val haddrs
      unfold AccountAddress.ofNat at hnat
      change (forkSrcMaskedWord I).toNat % EVM.addressModulus =
        evm.executionEnv.source.val at hnat
      rw [Nat.mod_eq_of_lt (forkSrcMaskedWord_canonical I)] at hnat
      rw [hopeSourceWord_toNat, ← hsource]
      exact hnat
    exact hne hword
  have hbeq : (forkSrcValue I == Value.address evm.executionEnv.source) = false := by
    rw [Bool.eq_false_iff]
    intro hb
    exact hneValue (beq_iff_eq.mp hb)
  simp only [evalExpr?, sender, envValue, EvalResult.bind, EvalResult.ofOption, bind, pure]
  rw [forkStoreDstInkSpotFinal_get_src I srcInkNew srcArtNew dstInkNew dstArtNew
    srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab vtab srcInkSpot dstInkSpot]
  simp [evalBinaryOp?, hbeq]

theorem evalExpr_fork_dst_sender_eq_false_final_store {evm : EVM.State} {I : ExecutionEnv}
    (srcInkNew srcArtNew dstInkNew dstArtNew
      srcArtFinal dstArtFinal srcInkFinal dstInkFinal
      utab vtab srcInkSpot dstInkSpot : UInt256)
    (hsource : evm.executionEnv.source = I.source)
    (hne : forkDstMaskedWord I ≠ hopeSourceWord I) :
    evalExpr? config
      { contract := contract,
        locals :=
          forkStoreDstInkSpotFinal I srcInkNew srcArtNew dstInkNew dstArtNew
            srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab vtab srcInkSpot
            dstInkSpot } evm
      (.binary .eq (.var "dst") sender) = .ok (.bool false) := by
  have hneValue :
      forkDstValue I ≠ .address evm.executionEnv.source := by
    intro hval
    have hmasked :
        Value.address (AccountAddress.ofNat (forkDstMaskedWord I).toNat) =
        Value.address evm.executionEnv.source := by
      rw [← solcAddressValue_masked (forkDstWord I), ← hval]
    have hword : forkDstMaskedWord I = hopeSourceWord I := by
      apply u256_inj
      have haddrs :
          AccountAddress.ofNat (forkDstMaskedWord I).toNat = evm.executionEnv.source := by
        injection hmasked with haddr
      have hnat := congrArg Fin.val haddrs
      unfold AccountAddress.ofNat at hnat
      change (forkDstMaskedWord I).toNat % EVM.addressModulus =
        evm.executionEnv.source.val at hnat
      rw [Nat.mod_eq_of_lt (forkDstMaskedWord_canonical I)] at hnat
      rw [hopeSourceWord_toNat, ← hsource]
      exact hnat
    exact hne hword
  have hbeq : (forkDstValue I == Value.address evm.executionEnv.source) = false := by
    rw [Bool.eq_false_iff]
    intro hb
    exact hneValue (beq_iff_eq.mp hb)
  simp only [evalExpr?, sender, envValue, EvalResult.bind, EvalResult.ofOption, bind, pure]
  rw [forkStoreDstInkSpotFinal_get_dst I srcInkNew srcArtNew dstInkNew dstArtNew
    srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab vtab srcInkSpot dstInkSpot]
  simp [evalBinaryOp?, hbeq]

theorem evalExpr_fork_src_can_eq_true_final_store {evm : EVM.State} {I : ExecutionEnv}
    (srcInkNew srcArtNew dstInkNew dstArtNew
      srcArtFinal dstArtFinal srcInkFinal dstInkFinal
      utab vtab srcInkSpot dstInkSpot : UInt256)
    (hsource : evm.executionEnv.source = I.source)
    (hcan : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (forkSrcWishSlot I) = ⟨1⟩) :
    evalExpr? config
      { contract := contract,
        locals :=
          forkStoreDstInkSpotFinal I srcInkNew srcArtNew dstInkNew dstArtNew
            srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab vtab srcInkSpot
            dstInkSpot } evm
      (.binary .eq (.storage (canRef (.var "src") sender)) (.intLit 1)) =
      .ok (.bool true) := by
  simp [evalExpr?, EvalResult.bind, bind, pure, evalBinaryOp?,
    evalExpr_fork_src_can_final_store (evm := evm) (I := I)
      srcInkNew srcArtNew dstInkNew dstArtNew srcArtFinal dstArtFinal
      srcInkFinal dstInkFinal utab vtab srcInkSpot dstInkSpot hsource,
    hcan, show (⟨1⟩ : UInt256).toNat = 1 by decide]

theorem evalExpr_fork_dst_can_eq_true_final_store {evm : EVM.State} {I : ExecutionEnv}
    (srcInkNew srcArtNew dstInkNew dstArtNew
      srcArtFinal dstArtFinal srcInkFinal dstInkFinal
      utab vtab srcInkSpot dstInkSpot : UInt256)
    (hsource : evm.executionEnv.source = I.source)
    (hcan : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (forkDstWishSlot I) = ⟨1⟩) :
    evalExpr? config
      { contract := contract,
        locals :=
          forkStoreDstInkSpotFinal I srcInkNew srcArtNew dstInkNew dstArtNew
            srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab vtab srcInkSpot
            dstInkSpot } evm
      (.binary .eq (.storage (canRef (.var "dst") sender)) (.intLit 1)) =
      .ok (.bool true) := by
  simp [evalExpr?, EvalResult.bind, bind, pure, evalBinaryOp?,
    evalExpr_fork_dst_can_final_store (evm := evm) (I := I)
      srcInkNew srcArtNew dstInkNew dstArtNew srcArtFinal dstArtFinal
      srcInkFinal dstInkFinal utab vtab srcInkSpot dstInkSpot hsource,
    hcan, show (⟨1⟩ : UInt256).toNat = 1 by decide]

theorem evalExpr_fork_src_can_eq_false_final_store {evm : EVM.State} {I : ExecutionEnv}
    (srcInkNew srcArtNew dstInkNew dstArtNew
      srcArtFinal dstArtFinal srcInkFinal dstInkFinal
      utab vtab srcInkSpot dstInkSpot : UInt256)
    (hsource : evm.executionEnv.source = I.source)
    (hcan : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (forkSrcWishSlot I) ≠ ⟨1⟩) :
    evalExpr? config
      { contract := contract,
        locals :=
          forkStoreDstInkSpotFinal I srcInkNew srcArtNew dstInkNew dstArtNew
            srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab vtab srcInkSpot
            dstInkSpot } evm
      (.binary .eq (.storage (canRef (.var "src") sender)) (.intLit 1)) =
      .ok (.bool false) := by
  have hneNat :
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (forkSrcWishSlot I)).toNat ≠ 1 := by
    intro hnat
    apply hcan
    apply u256_inj
    rw [hnat]
    decide
  simp [evalExpr?, EvalResult.bind, bind, pure, evalBinaryOp?,
    evalExpr_fork_src_can_final_store (evm := evm) (I := I)
      srcInkNew srcArtNew dstInkNew dstArtNew srcArtFinal dstArtFinal
      srcInkFinal dstInkFinal utab vtab srcInkSpot dstInkSpot hsource,
    hneNat]

theorem evalExpr_fork_dst_can_eq_false_final_store {evm : EVM.State} {I : ExecutionEnv}
    (srcInkNew srcArtNew dstInkNew dstArtNew
      srcArtFinal dstArtFinal srcInkFinal dstInkFinal
      utab vtab srcInkSpot dstInkSpot : UInt256)
    (hsource : evm.executionEnv.source = I.source)
    (hcan : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (forkDstWishSlot I) ≠ ⟨1⟩) :
    evalExpr? config
      { contract := contract,
        locals :=
          forkStoreDstInkSpotFinal I srcInkNew srcArtNew dstInkNew dstArtNew
            srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab vtab srcInkSpot
            dstInkSpot } evm
      (.binary .eq (.storage (canRef (.var "dst") sender)) (.intLit 1)) =
      .ok (.bool false) := by
  have hneNat :
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (forkDstWishSlot I)).toNat ≠ 1 := by
    intro hnat
    apply hcan
    apply u256_inj
    rw [hnat]
    decide
  simp [evalExpr?, EvalResult.bind, bind, pure, evalBinaryOp?,
    evalExpr_fork_dst_can_final_store (evm := evm) (I := I)
      srcInkNew srcArtNew dstInkNew dstArtNew srcArtFinal dstArtFinal
      srcInkFinal dstInkFinal utab vtab srcInkSpot dstInkSpot hsource,
    hneNat]

theorem evalExpr_fork_src_wish_true_src_final_store {evm : EVM.State} {I : ExecutionEnv}
    (srcInkNew srcArtNew dstInkNew dstArtNew
      srcArtFinal dstArtFinal srcInkFinal dstInkFinal
      utab vtab srcInkSpot dstInkSpot : UInt256)
    (hsource : evm.executionEnv.source = I.source)
    (heq : forkSrcMaskedWord I = hopeSourceWord I) :
    evalExpr? config
      { contract := contract,
        locals :=
          forkStoreDstInkSpotFinal I srcInkNew srcArtNew dstInkNew dstArtNew
            srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab vtab srcInkSpot
            dstInkSpot } evm
      (wishExpr (.var "src") sender) = .ok (.bool true) := by
  exact vatEvalExpr_or_true_left
    (lhs := .binary .eq (.var "src") sender)
    (rhs := .binary .eq (.storage (canRef (.var "src") sender)) (.intLit 1))
    (evalExpr_fork_src_sender_eq_true_final_store (evm := evm) (I := I)
      srcInkNew srcArtNew dstInkNew dstArtNew srcArtFinal dstArtFinal
      srcInkFinal dstInkFinal utab vtab srcInkSpot dstInkSpot hsource heq)

theorem evalExpr_fork_dst_wish_true_dst_final_store {evm : EVM.State} {I : ExecutionEnv}
    (srcInkNew srcArtNew dstInkNew dstArtNew
      srcArtFinal dstArtFinal srcInkFinal dstInkFinal
      utab vtab srcInkSpot dstInkSpot : UInt256)
    (hsource : evm.executionEnv.source = I.source)
    (heq : forkDstMaskedWord I = hopeSourceWord I) :
    evalExpr? config
      { contract := contract,
        locals :=
          forkStoreDstInkSpotFinal I srcInkNew srcArtNew dstInkNew dstArtNew
            srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab vtab srcInkSpot
            dstInkSpot } evm
      (wishExpr (.var "dst") sender) = .ok (.bool true) := by
  exact vatEvalExpr_or_true_left
    (lhs := .binary .eq (.var "dst") sender)
    (rhs := .binary .eq (.storage (canRef (.var "dst") sender)) (.intLit 1))
    (evalExpr_fork_dst_sender_eq_true_final_store (evm := evm) (I := I)
      srcInkNew srcArtNew dstInkNew dstArtNew srcArtFinal dstArtFinal
      srcInkFinal dstInkFinal utab vtab srcInkSpot dstInkSpot hsource heq)

theorem evalExpr_fork_src_wish_true_can_final_store {evm : EVM.State} {I : ExecutionEnv}
    (srcInkNew srcArtNew dstInkNew dstArtNew
      srcArtFinal dstArtFinal srcInkFinal dstInkFinal
      utab vtab srcInkSpot dstInkSpot : UInt256)
    (hsource : evm.executionEnv.source = I.source)
    (hne : forkSrcMaskedWord I ≠ hopeSourceWord I)
    (hcan : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (forkSrcWishSlot I) = ⟨1⟩) :
    evalExpr? config
      { contract := contract,
        locals :=
          forkStoreDstInkSpotFinal I srcInkNew srcArtNew dstInkNew dstArtNew
            srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab vtab srcInkSpot
            dstInkSpot } evm
      (wishExpr (.var "src") sender) = .ok (.bool true) := by
  exact vatEvalExpr_or_false_right
    (lhs := .binary .eq (.var "src") sender)
    (rhs := .binary .eq (.storage (canRef (.var "src") sender)) (.intLit 1))
    (evalExpr_fork_src_sender_eq_false_final_store (evm := evm) (I := I)
      srcInkNew srcArtNew dstInkNew dstArtNew srcArtFinal dstArtFinal
      srcInkFinal dstInkFinal utab vtab srcInkSpot dstInkSpot hsource hne)
    (evalExpr_fork_src_can_eq_true_final_store (evm := evm) (I := I)
      srcInkNew srcArtNew dstInkNew dstArtNew srcArtFinal dstArtFinal
      srcInkFinal dstInkFinal utab vtab srcInkSpot dstInkSpot hsource hcan)

theorem evalExpr_fork_dst_wish_true_can_final_store {evm : EVM.State} {I : ExecutionEnv}
    (srcInkNew srcArtNew dstInkNew dstArtNew
      srcArtFinal dstArtFinal srcInkFinal dstInkFinal
      utab vtab srcInkSpot dstInkSpot : UInt256)
    (hsource : evm.executionEnv.source = I.source)
    (hne : forkDstMaskedWord I ≠ hopeSourceWord I)
    (hcan : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (forkDstWishSlot I) = ⟨1⟩) :
    evalExpr? config
      { contract := contract,
        locals :=
          forkStoreDstInkSpotFinal I srcInkNew srcArtNew dstInkNew dstArtNew
            srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab vtab srcInkSpot
            dstInkSpot } evm
      (wishExpr (.var "dst") sender) = .ok (.bool true) := by
  exact vatEvalExpr_or_false_right
    (lhs := .binary .eq (.var "dst") sender)
    (rhs := .binary .eq (.storage (canRef (.var "dst") sender)) (.intLit 1))
    (evalExpr_fork_dst_sender_eq_false_final_store (evm := evm) (I := I)
      srcInkNew srcArtNew dstInkNew dstArtNew srcArtFinal dstArtFinal
      srcInkFinal dstInkFinal utab vtab srcInkSpot dstInkSpot hsource hne)
    (evalExpr_fork_dst_can_eq_true_final_store (evm := evm) (I := I)
      srcInkNew srcArtNew dstInkNew dstArtNew srcArtFinal dstArtFinal
      srcInkFinal dstInkFinal utab vtab srcInkSpot dstInkSpot hsource hcan)

theorem evalExpr_fork_src_wish_false_final_store {evm : EVM.State} {I : ExecutionEnv}
    (srcInkNew srcArtNew dstInkNew dstArtNew
      srcArtFinal dstArtFinal srcInkFinal dstInkFinal
      utab vtab srcInkSpot dstInkSpot : UInt256)
    (hsource : evm.executionEnv.source = I.source)
    (hne : forkSrcMaskedWord I ≠ hopeSourceWord I)
    (hcan : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (forkSrcWishSlot I) ≠ ⟨1⟩) :
    evalExpr? config
      { contract := contract,
        locals :=
          forkStoreDstInkSpotFinal I srcInkNew srcArtNew dstInkNew dstArtNew
            srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab vtab srcInkSpot
            dstInkSpot } evm
      (wishExpr (.var "src") sender) = .ok (.bool false) := by
  exact vatEvalExpr_or_false_right
    (lhs := .binary .eq (.var "src") sender)
    (rhs := .binary .eq (.storage (canRef (.var "src") sender)) (.intLit 1))
    (evalExpr_fork_src_sender_eq_false_final_store (evm := evm) (I := I)
      srcInkNew srcArtNew dstInkNew dstArtNew srcArtFinal dstArtFinal
      srcInkFinal dstInkFinal utab vtab srcInkSpot dstInkSpot hsource hne)
    (evalExpr_fork_src_can_eq_false_final_store (evm := evm) (I := I)
      srcInkNew srcArtNew dstInkNew dstArtNew srcArtFinal dstArtFinal
      srcInkFinal dstInkFinal utab vtab srcInkSpot dstInkSpot hsource hcan)

theorem evalExpr_fork_dst_wish_false_final_store {evm : EVM.State} {I : ExecutionEnv}
    (srcInkNew srcArtNew dstInkNew dstArtNew
      srcArtFinal dstArtFinal srcInkFinal dstInkFinal
      utab vtab srcInkSpot dstInkSpot : UInt256)
    (hsource : evm.executionEnv.source = I.source)
    (hne : forkDstMaskedWord I ≠ hopeSourceWord I)
    (hcan : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (forkDstWishSlot I) ≠ ⟨1⟩) :
    evalExpr? config
      { contract := contract,
        locals :=
          forkStoreDstInkSpotFinal I srcInkNew srcArtNew dstInkNew dstArtNew
            srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab vtab srcInkSpot
            dstInkSpot } evm
      (wishExpr (.var "dst") sender) = .ok (.bool false) := by
  exact vatEvalExpr_or_false_right
    (lhs := .binary .eq (.var "dst") sender)
    (rhs := .binary .eq (.storage (canRef (.var "dst") sender)) (.intLit 1))
    (evalExpr_fork_dst_sender_eq_false_final_store (evm := evm) (I := I)
      srcInkNew srcArtNew dstInkNew dstArtNew srcArtFinal dstArtFinal
      srcInkFinal dstInkFinal utab vtab srcInkSpot dstInkSpot hsource hne)
    (evalExpr_fork_dst_can_eq_false_final_store (evm := evm) (I := I)
      srcInkNew srcArtNew dstInkNew dstArtNew srcArtFinal dstArtFinal
      srcInkFinal dstInkFinal utab vtab srcInkSpot dstInkSpot hsource hcan)

theorem evalExpr_fork_wish_both_true_final_store {evm : EVM.State} {I : ExecutionEnv}
    (srcInkNew srcArtNew dstInkNew dstArtNew
      srcArtFinal dstArtFinal srcInkFinal dstInkFinal
      utab vtab srcInkSpot dstInkSpot : UInt256)
    (hsrcWish :
      evalExpr? config
        { contract := contract,
          locals :=
            forkStoreDstInkSpotFinal I srcInkNew srcArtNew dstInkNew dstArtNew
              srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab vtab srcInkSpot
              dstInkSpot } evm
        (wishExpr (.var "src") sender) = .ok (.bool true))
    (hdstWish :
      evalExpr? config
        { contract := contract,
          locals :=
            forkStoreDstInkSpotFinal I srcInkNew srcArtNew dstInkNew dstArtNew
              srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab vtab srcInkSpot
              dstInkSpot } evm
        (wishExpr (.var "dst") sender) = .ok (.bool true)) :
    evalExpr? config
      { contract := contract,
        locals :=
          forkStoreDstInkSpotFinal I srcInkNew srcArtNew dstInkNew dstArtNew
            srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab vtab srcInkSpot
            dstInkSpot } evm
      (bothExpr (wishExpr (.var "src") sender) (wishExpr (.var "dst") sender)) =
      .ok (.bool true) := by
  exact vatEvalExpr_and_true hsrcWish hdstWish

theorem evalExpr_fork_wish_both_false_left_final_store {evm : EVM.State} {I : ExecutionEnv}
    (srcInkNew srcArtNew dstInkNew dstArtNew
      srcArtFinal dstArtFinal srcInkFinal dstInkFinal
      utab vtab srcInkSpot dstInkSpot : UInt256)
    (hsrcWish :
      evalExpr? config
        { contract := contract,
          locals :=
            forkStoreDstInkSpotFinal I srcInkNew srcArtNew dstInkNew dstArtNew
              srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab vtab srcInkSpot
              dstInkSpot } evm
        (wishExpr (.var "src") sender) = .ok (.bool false)) :
    evalExpr? config
      { contract := contract,
        locals :=
          forkStoreDstInkSpotFinal I srcInkNew srcArtNew dstInkNew dstArtNew
            srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab vtab srcInkSpot
            dstInkSpot } evm
      (bothExpr (wishExpr (.var "src") sender) (wishExpr (.var "dst") sender)) =
      .ok (.bool false) := by
  exact vatEvalExpr_and_false_left hsrcWish

theorem evalExpr_fork_wish_both_false_right_final_store {evm : EVM.State} {I : ExecutionEnv}
    (srcInkNew srcArtNew dstInkNew dstArtNew
      srcArtFinal dstArtFinal srcInkFinal dstInkFinal
      utab vtab srcInkSpot dstInkSpot : UInt256)
    (hsrcWish :
      evalExpr? config
        { contract := contract,
          locals :=
            forkStoreDstInkSpotFinal I srcInkNew srcArtNew dstInkNew dstArtNew
              srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab vtab srcInkSpot
              dstInkSpot } evm
        (wishExpr (.var "src") sender) = .ok (.bool true))
    (hdstWish :
      evalExpr? config
        { contract := contract,
          locals :=
            forkStoreDstInkSpotFinal I srcInkNew srcArtNew dstInkNew dstArtNew
              srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab vtab srcInkSpot
              dstInkSpot } evm
        (wishExpr (.var "dst") sender) = .ok (.bool false)) :
    evalExpr? config
      { contract := contract,
        locals :=
          forkStoreDstInkSpotFinal I srcInkNew srcArtNew dstInkNew dstArtNew
            srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab vtab srcInkSpot
            dstInkSpot } evm
      (bothExpr (wishExpr (.var "src") sender) (wishExpr (.var "dst") sender)) =
      .ok (.bool false) := by
  exact vatEvalExpr_and_true_false_right hsrcWish hdstWish

theorem evalExpr_fork_src_wish_true_of_word_final_store {evm : EVM.State}
    {σ : AccountMap} {I : ExecutionEnv}
    (srcInkNew srcArtNew dstInkNew dstArtNew
      srcArtFinal dstArtFinal srcInkFinal dstInkFinal
      utab vtab srcInkSpot dstInkSpot : UInt256)
    (hsource : evm.executionEnv.source = I.source)
    (hload :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (forkSrcWishSlot I) =
        vatSlotWord (forkSrcWishSlot I) σ I)
    (hword : forkSrcWishWord σ I ≠ ⟨0⟩) :
    evalExpr? config
      { contract := contract,
        locals :=
          forkStoreDstInkSpotFinal I srcInkNew srcArtNew dstInkNew dstArtNew
            srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab vtab srcInkSpot
            dstInkSpot } evm
      (wishExpr (.var "src") sender) = .ok (.bool true) := by
  by_cases hsrc : forkSrcMaskedWord I = hopeSourceWord I
  · exact evalExpr_fork_src_wish_true_src_final_store
      (evm := evm) (I := I) srcInkNew srcArtNew dstInkNew dstArtNew
      srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab vtab srcInkSpot
      dstInkSpot hsource hsrc
  · by_cases hcan : vatSlotWord (forkSrcWishSlot I) σ I = ⟨1⟩
    · exact evalExpr_fork_src_wish_true_can_final_store
        (evm := evm) (I := I) srcInkNew srcArtNew dstInkNew dstArtNew
        srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab vtab srcInkSpot
        dstInkSpot hsource hsrc (by rw [hload, hcan])
    · exact False.elim (hword (forkSrcWishWord_false hsrc hcan))

theorem evalExpr_fork_dst_wish_true_of_word_final_store {evm : EVM.State}
    {σ : AccountMap} {I : ExecutionEnv}
    (srcInkNew srcArtNew dstInkNew dstArtNew
      srcArtFinal dstArtFinal srcInkFinal dstInkFinal
      utab vtab srcInkSpot dstInkSpot : UInt256)
    (hsource : evm.executionEnv.source = I.source)
    (hload :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (forkDstWishSlot I) =
        vatSlotWord (forkDstWishSlot I) σ I)
    (hword : forkDstWishWord σ I ≠ ⟨0⟩) :
    evalExpr? config
      { contract := contract,
        locals :=
          forkStoreDstInkSpotFinal I srcInkNew srcArtNew dstInkNew dstArtNew
            srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab vtab srcInkSpot
            dstInkSpot } evm
      (wishExpr (.var "dst") sender) = .ok (.bool true) := by
  by_cases hdst : forkDstMaskedWord I = hopeSourceWord I
  · exact evalExpr_fork_dst_wish_true_dst_final_store
      (evm := evm) (I := I) srcInkNew srcArtNew dstInkNew dstArtNew
      srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab vtab srcInkSpot
      dstInkSpot hsource hdst
  · by_cases hcan : vatSlotWord (forkDstWishSlot I) σ I = ⟨1⟩
    · exact evalExpr_fork_dst_wish_true_can_final_store
        (evm := evm) (I := I) srcInkNew srcArtNew dstInkNew dstArtNew
        srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab vtab srcInkSpot
        dstInkSpot hsource hdst (by rw [hload, hcan])
    · exact False.elim (hword (forkDstWishWord_false hdst hcan))

theorem evalExpr_fork_wish_both_true_of_word_final_store {evm : EVM.State}
    {σ : AccountMap} {I : ExecutionEnv}
    (srcInkNew srcArtNew dstInkNew dstArtNew
      srcArtFinal dstArtFinal srcInkFinal dstInkFinal
      utab vtab srcInkSpot dstInkSpot : UInt256)
    (hsource : evm.executionEnv.source = I.source)
    (hloadSrc :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (forkSrcWishSlot I) =
        vatSlotWord (forkSrcWishSlot I) σ I)
    (hloadDst :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (forkDstWishSlot I) =
        vatSlotWord (forkDstWishSlot I) σ I)
    (hword : forkBothWishWord σ I ≠ ⟨0⟩) :
    evalExpr? config
      { contract := contract,
        locals :=
          forkStoreDstInkSpotFinal I srcInkNew srcArtNew dstInkNew dstArtNew
            srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab vtab srcInkSpot
            dstInkSpot } evm
      (bothExpr (wishExpr (.var "src") sender) (wishExpr (.var "dst") sender)) =
      .ok (.bool true) := by
  exact evalExpr_fork_wish_both_true_final_store
    (evm := evm) (I := I) srcInkNew srcArtNew dstInkNew dstArtNew
    srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab vtab srcInkSpot dstInkSpot
    (evalExpr_fork_src_wish_true_of_word_final_store (evm := evm) (σ := σ)
      srcInkNew srcArtNew dstInkNew dstArtNew srcArtFinal dstArtFinal
      srcInkFinal dstInkFinal utab vtab srcInkSpot dstInkSpot
      hsource hloadSrc (forkBothWishWord_true_src hword))
    (evalExpr_fork_dst_wish_true_of_word_final_store (evm := evm) (σ := σ)
      srcInkNew srcArtNew dstInkNew dstArtNew srcArtFinal dstArtFinal
      srcInkFinal dstInkFinal utab vtab srcInkSpot dstInkSpot
      hsource hloadDst (forkBothWishWord_true_dst hword))

theorem evalExpr_fork_src_wish_false_of_word_zero_final_store {evm : EVM.State}
    {σ : AccountMap} {I : ExecutionEnv}
    (srcInkNew srcArtNew dstInkNew dstArtNew
      srcArtFinal dstArtFinal srcInkFinal dstInkFinal
      utab vtab srcInkSpot dstInkSpot : UInt256)
    (hsource : evm.executionEnv.source = I.source)
    (hload :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (forkSrcWishSlot I) =
        vatSlotWord (forkSrcWishSlot I) σ I)
    (hword : forkSrcWishWord σ I = ⟨0⟩) :
    evalExpr? config
      { contract := contract,
        locals :=
          forkStoreDstInkSpotFinal I srcInkNew srcArtNew dstInkNew dstArtNew
            srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab vtab srcInkSpot
            dstInkSpot } evm
      (wishExpr (.var "src") sender) = .ok (.bool false) := by
  by_cases hsrc : forkSrcMaskedWord I = hopeSourceWord I
  · exact False.elim ((forkSrcWishWord_true_src (σ := σ) hsrc) hword)
  · by_cases hcan : vatSlotWord (forkSrcWishSlot I) σ I = ⟨1⟩
    · exact False.elim ((forkSrcWishWord_true_can (σ := σ) hcan) hword)
    · exact evalExpr_fork_src_wish_false_final_store
        (evm := evm) (I := I) srcInkNew srcArtNew dstInkNew dstArtNew
        srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab vtab srcInkSpot
        dstInkSpot hsource hsrc
        (by intro hloadOne; exact hcan (by rw [← hload, hloadOne]))

theorem evalExpr_fork_dst_wish_false_of_word_zero_final_store {evm : EVM.State}
    {σ : AccountMap} {I : ExecutionEnv}
    (srcInkNew srcArtNew dstInkNew dstArtNew
      srcArtFinal dstArtFinal srcInkFinal dstInkFinal
      utab vtab srcInkSpot dstInkSpot : UInt256)
    (hsource : evm.executionEnv.source = I.source)
    (hload :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (forkDstWishSlot I) =
        vatSlotWord (forkDstWishSlot I) σ I)
    (hword : forkDstWishWord σ I = ⟨0⟩) :
    evalExpr? config
      { contract := contract,
        locals :=
          forkStoreDstInkSpotFinal I srcInkNew srcArtNew dstInkNew dstArtNew
            srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab vtab srcInkSpot
            dstInkSpot } evm
      (wishExpr (.var "dst") sender) = .ok (.bool false) := by
  by_cases hdst : forkDstMaskedWord I = hopeSourceWord I
  · exact False.elim ((forkDstWishWord_true_dst (σ := σ) hdst) hword)
  · by_cases hcan : vatSlotWord (forkDstWishSlot I) σ I = ⟨1⟩
    · exact False.elim ((forkDstWishWord_true_can (σ := σ) hcan) hword)
    · exact evalExpr_fork_dst_wish_false_final_store
        (evm := evm) (I := I) srcInkNew srcArtNew dstInkNew dstArtNew
        srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab vtab srcInkSpot
        dstInkSpot hsource hdst
        (by intro hloadOne; exact hcan (by rw [← hload, hloadOne]))

theorem evalExpr_fork_wish_both_false_of_word_zero_final_store {evm : EVM.State}
    {σ : AccountMap} {I : ExecutionEnv}
    (srcInkNew srcArtNew dstInkNew dstArtNew
      srcArtFinal dstArtFinal srcInkFinal dstInkFinal
      utab vtab srcInkSpot dstInkSpot : UInt256)
    (hsource : evm.executionEnv.source = I.source)
    (hloadSrc :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (forkSrcWishSlot I) =
        vatSlotWord (forkSrcWishSlot I) σ I)
    (hloadDst :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (forkDstWishSlot I) =
        vatSlotWord (forkDstWishSlot I) σ I)
    (hword : forkBothWishWord σ I = ⟨0⟩) :
    evalExpr? config
      { contract := contract,
        locals :=
          forkStoreDstInkSpotFinal I srcInkNew srcArtNew dstInkNew dstArtNew
            srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab vtab srcInkSpot
            dstInkSpot } evm
      (bothExpr (wishExpr (.var "src") sender) (wishExpr (.var "dst") sender)) =
      .ok (.bool false) := by
  by_cases hsrcZero : forkSrcWishWord σ I = ⟨0⟩
  · exact evalExpr_fork_wish_both_false_left_final_store
      (evm := evm) (I := I) srcInkNew srcArtNew dstInkNew dstArtNew
      srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab vtab srcInkSpot
      dstInkSpot
      (evalExpr_fork_src_wish_false_of_word_zero_final_store (evm := evm) (σ := σ)
        srcInkNew srcArtNew dstInkNew dstArtNew srcArtFinal dstArtFinal
        srcInkFinal dstInkFinal utab vtab srcInkSpot dstInkSpot
        hsource hloadSrc hsrcZero)
  · by_cases hdstZero : forkDstWishWord σ I = ⟨0⟩
    · exact evalExpr_fork_wish_both_false_right_final_store
        (evm := evm) (I := I) srcInkNew srcArtNew dstInkNew dstArtNew
        srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab vtab srcInkSpot
        dstInkSpot
        (evalExpr_fork_src_wish_true_of_word_final_store (evm := evm) (σ := σ)
          srcInkNew srcArtNew dstInkNew dstArtNew srcArtFinal dstArtFinal
          srcInkFinal dstInkFinal utab vtab srcInkSpot dstInkSpot
          hsource hloadSrc hsrcZero)
        (evalExpr_fork_dst_wish_false_of_word_zero_final_store (evm := evm) (σ := σ)
          srcInkNew srcArtNew dstInkNew dstArtNew srcArtFinal dstArtFinal
          srcInkFinal dstInkFinal utab vtab srcInkSpot dstInkSpot
          hsource hloadDst hdstZero)
    · exact False.elim ((forkBothWishWord_true hsrcZero hdstZero) hword)

theorem fork_u256_isZero_ne_zero_to_eq_zero {a : UInt256}
    (h : UInt256.isZero a ≠ ⟨0⟩) :
    a = ⟨0⟩ := by
  by_contra hne
  have hz : UInt256.isZero a = ⟨0⟩ := isZero_eq_zero_of_ne hne
  exact h hz

theorem fork_u256_lor_left_ne_zero_of_lor_ne_zero_right_zero {a b : UInt256}
    (h : UInt256.lor a b ≠ ⟨0⟩) (hb : b = ⟨0⟩) :
    a ≠ ⟨0⟩ := by
  rw [hb, u256_lor_zero] at h
  exact h

theorem fork_u256_lor_one_ne_zero (w : UInt256) :
    UInt256.lor (⟨1⟩ : UInt256) w ≠ ⟨0⟩ := by
  intro h
  have hbit := congrArg (fun x : UInt256 => x.toNat % 2) h
  simp [UInt256.lor, Fin.lor, UInt256.size] at hbit
  change (Nat.lor 1 w.toNat % UInt256.size) % 2 = 0 at hbit
  rw [Nat.mod_mod_of_dvd _ (by norm_num [UInt256.size] : 2 ∣ UInt256.size)] at hbit
  have hlorOdd : Nat.lor 1 w.toNat % 2 = 1 := by
    have htest : Nat.testBit (Nat.lor 1 w.toNat) 0 = true := by
      change Nat.testBit (1 ||| w.toNat) 0 = true
      rw [Nat.testBit_or]
      simp
    simpa [Nat.testBit_zero] using htest
  omega

theorem forkDustSourceCond_of_evm {art tab dust : UInt256}
    (h :
      UInt256.lor
        (UInt256.eq ⟨0⟩ art)
        (UInt256.isZero (UInt256.lt tab dust)) ≠ ⟨0⟩) :
    dust.toNat ≤ tab.toNat ∨ art.toNat = 0 := by
  by_cases hzero : UInt256.eq ⟨0⟩ art = ⟨0⟩
  · have hcomm := h
    rw [u256_lor_comm] at hcomm
    have hltIsZero : UInt256.isZero (UInt256.lt tab dust) ≠ ⟨0⟩ :=
      fork_u256_lor_left_ne_zero_of_lor_ne_zero_right_zero hcomm hzero
    have hlt : UInt256.lt tab dust = ⟨0⟩ :=
      fork_u256_isZero_ne_zero_to_eq_zero hltIsZero
    exact Or.inl (ult_eq_zero_to_le hlt)
  · have heq : (⟨0⟩ : UInt256) = art :=
      u256_eq_ne_zero_to_eq hzero
    exact Or.inr (by rw [← heq]; rfl)

theorem forkDustSourceCond_false_of_evm {art tab dust : UInt256}
    (h :
      UInt256.lor
        (UInt256.eq ⟨0⟩ art)
        (UInt256.isZero (UInt256.lt tab dust)) = ⟨0⟩) :
    tab.toNat < dust.toNat ∧ 0 < art.toNat := by
  have heqZero : UInt256.eq ⟨0⟩ art = ⟨0⟩ := by
    by_contra hne
    have hart : (⟨0⟩ : UInt256) = art := u256_eq_ne_zero_to_eq hne
    have hone : UInt256.eq ⟨0⟩ art = ⟨1⟩ := by
      rw [← hart, u256_eq_refl]
    exact fork_u256_lor_one_ne_zero (UInt256.isZero (UInt256.lt tab dust))
      (by simpa [hone] using h)
  have hisZeroZero : UInt256.isZero (UInt256.lt tab dust) = ⟨0⟩ := by
    by_contra hne
    have hlor := h
    rw [u256_lor_comm] at hlor
    have hltZero : UInt256.lt tab dust = ⟨0⟩ :=
      fork_u256_isZero_ne_zero_to_eq_zero hne
    have hone : UInt256.isZero (UInt256.lt tab dust) = ⟨1⟩ := by
      rw [hltZero]
      native_decide
    exact fork_u256_lor_one_ne_zero (UInt256.eq ⟨0⟩ art)
      (by simpa [hone] using hlor)
  have hltNe : UInt256.lt tab dust ≠ ⟨0⟩ := by
    intro hltZero
    have hone : UInt256.isZero (UInt256.lt tab dust) = ⟨1⟩ := by
      rw [hltZero]
      native_decide
    rw [hone] at hisZeroZero
    exact one_ne_zero_uint hisZeroZero
  have hartPos : 0 < art.toNat := by
    apply Nat.pos_of_ne_zero
    intro hartNat
    have hart : (⟨0⟩ : UInt256) = art := by
      apply u256_inj
      simpa [hartNat]
    have hone : UInt256.eq ⟨0⟩ art = ⟨1⟩ := by
      rw [← hart, u256_eq_refl]
    rw [hone] at heqZero
    exact one_ne_zero_uint heqZero
  exact ⟨ult_ne_zero_to_lt hltNe, hartPos⟩

theorem vatEvalExpr_eq_uint256_zero_true {evm : EVM.State} {locals : Store}
    {x : Expr} {a : UInt256}
    (hx : evalExpr? config { contract := contract, locals := locals } evm x =
      .ok (.int (Int.ofNat a.toNat)))
    (hzero : a.toNat = 0) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.binary .eq x (.intLit 0)) = .ok (.bool true) := by
  simp [evalExpr?, EvalResult.bind, bind, hx, evalBinaryOp?, hzero]

theorem vatEvalExpr_eq_uint256_zero_false {evm : EVM.State} {locals : Store}
    {x : Expr} {a : UInt256}
    (hx : evalExpr? config { contract := contract, locals := locals } evm x =
      .ok (.int (Int.ofNat a.toNat)))
    (hpos : 0 < a.toNat) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.binary .eq x (.intLit 0)) = .ok (.bool false) := by
  simp [evalExpr?, EvalResult.bind, bind, hx, evalBinaryOp?]
  omega

theorem evalExpr_fork_src_dust_final {evm : EVM.State} {I : ExecutionEnv}
    (srcInkNew srcArtNew dstInkNew dstArtNew utab vtab srcInkSpot dstInkSpot dust : UInt256)
    (hsz164 : 164 ≤ I.calldata.size)
    (hloadDust :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (forkIlkDustSlot I) = dust)
    (hloadSrcArt :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (forkSrcArtSlot I) = srcArtNew)
    (hcond : dust.toNat ≤ utab.toNat ∨ srcArtNew.toNat = 0) :
    evalExpr? config
      { contract := contract,
        locals :=
          forkStoreDstInkSpot I srcInkNew srcArtNew dstInkNew dstArtNew utab vtab
            srcInkSpot dstInkSpot } evm
      (eitherExpr
        (.binary .ge (.var "utab") (.storage (ilksF (.var "ilk") "dust")))
        (.binary .eq (.storage (urnsF (.var "ilk") (.var "src") "art")) (.intLit 0))) =
      .ok (.bool true) := by
  let locals :=
    forkStoreDstInkSpot I srcInkNew srcArtNew dstInkNew dstArtNew utab vtab srcInkSpot
      dstInkSpot
  have hutab :
      evalExpr? config { contract := contract, locals := locals } evm (.var "utab") =
        .ok (.int (Int.ofNat utab.toNat)) :=
    vatEvalExpr_varUInt256 (by
      simpa [locals] using
        forkStoreDstInkSpot_get_utab I srcInkNew srcArtNew dstInkNew dstArtNew utab vtab
          srcInkSpot dstInkSpot)
  have hdust :
      evalExpr? config { contract := contract, locals := locals } evm
        (.storage (ilksF (.var "ilk") "dust")) =
        .ok (.int (Int.ofNat dust.toNat)) := by
    rw [evalExpr_fork_ilk_dust_locals locals hsz164
      (by
        simpa [locals] using
          forkStoreDstInkSpot_get_ilk I srcInkNew srcArtNew dstInkNew dstArtNew utab vtab
            srcInkSpot dstInkSpot)
      (by
        simpa [locals] using
          forkStoreDstInkSpot_get_ilks I srcInkNew srcArtNew dstInkNew dstArtNew utab vtab
            srcInkSpot dstInkSpot)]
    rw [hloadDust]
  cases hcond with
  | inl hge =>
      exact vatEvalExpr_or_true_left
        (vatEvalExpr_ge_uint256_true hutab hdust hge)
  | inr hzero =>
      by_cases hge : dust.toNat ≤ utab.toNat
      · exact vatEvalExpr_or_true_left
          (vatEvalExpr_ge_uint256_true hutab hdust hge)
      · have hleft := vatEvalExpr_ge_uint256_false hutab hdust (Nat.lt_of_not_ge hge)
        have hsrcArt :
            evalExpr? config { contract := contract, locals := locals } evm
              (.storage (urnsF (.var "ilk") (.var "src") "art")) =
              .ok (.int (Int.ofNat srcArtNew.toNat)) := by
          rw [evalExpr_fork_src_art_locals locals hsz164
            (by
              simpa [locals] using
                forkStoreDstInkSpot_get_ilk I srcInkNew srcArtNew dstInkNew dstArtNew utab
                  vtab srcInkSpot dstInkSpot)
            (by
              simpa [locals] using
                forkStoreDstInkSpot_get_src I srcInkNew srcArtNew dstInkNew dstArtNew utab
                  vtab srcInkSpot dstInkSpot)
            (by
              simpa [locals] using
                forkStoreDstInkSpot_get_urns I srcInkNew srcArtNew dstInkNew dstArtNew utab
                  vtab srcInkSpot dstInkSpot)]
          rw [hloadSrcArt]
        exact vatEvalExpr_or_false_right hleft
          (vatEvalExpr_eq_uint256_zero_true hsrcArt hzero)

theorem evalExpr_fork_src_dust_false_final {evm : EVM.State} {I : ExecutionEnv}
    (srcInkNew srcArtNew dstInkNew dstArtNew utab vtab srcInkSpot dstInkSpot dust : UInt256)
    (hsz164 : 164 ≤ I.calldata.size)
    (hloadDust :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (forkIlkDustSlot I) = dust)
    (hloadSrcArt :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (forkSrcArtSlot I) = srcArtNew)
    (hgtDust : utab.toNat < dust.toNat)
    (hsrcArtPos : 0 < srcArtNew.toNat) :
    evalExpr? config
      { contract := contract,
        locals :=
          forkStoreDstInkSpot I srcInkNew srcArtNew dstInkNew dstArtNew utab vtab
            srcInkSpot dstInkSpot } evm
      (eitherExpr
        (.binary .ge (.var "utab") (.storage (ilksF (.var "ilk") "dust")))
        (.binary .eq (.storage (urnsF (.var "ilk") (.var "src") "art")) (.intLit 0))) =
      .ok (.bool false) := by
  let locals :=
    forkStoreDstInkSpot I srcInkNew srcArtNew dstInkNew dstArtNew utab vtab srcInkSpot
      dstInkSpot
  have hutab :
      evalExpr? config { contract := contract, locals := locals } evm (.var "utab") =
        .ok (.int (Int.ofNat utab.toNat)) :=
    vatEvalExpr_varUInt256 (by
      simpa [locals] using
        forkStoreDstInkSpot_get_utab I srcInkNew srcArtNew dstInkNew dstArtNew utab vtab
          srcInkSpot dstInkSpot)
  have hdust :
      evalExpr? config { contract := contract, locals := locals } evm
        (.storage (ilksF (.var "ilk") "dust")) =
        .ok (.int (Int.ofNat dust.toNat)) := by
    rw [evalExpr_fork_ilk_dust_locals locals hsz164
      (by
        simpa [locals] using
          forkStoreDstInkSpot_get_ilk I srcInkNew srcArtNew dstInkNew dstArtNew utab vtab
            srcInkSpot dstInkSpot)
      (by
        simpa [locals] using
          forkStoreDstInkSpot_get_ilks I srcInkNew srcArtNew dstInkNew dstArtNew utab vtab
            srcInkSpot dstInkSpot)]
    rw [hloadDust]
  have hsrcArt :
      evalExpr? config { contract := contract, locals := locals } evm
        (.storage (urnsF (.var "ilk") (.var "src") "art")) =
        .ok (.int (Int.ofNat srcArtNew.toNat)) := by
    rw [evalExpr_fork_src_art_locals locals hsz164
      (by
        simpa [locals] using
          forkStoreDstInkSpot_get_ilk I srcInkNew srcArtNew dstInkNew dstArtNew utab vtab
            srcInkSpot dstInkSpot)
      (by
        simpa [locals] using
          forkStoreDstInkSpot_get_src I srcInkNew srcArtNew dstInkNew dstArtNew utab vtab
            srcInkSpot dstInkSpot)
      (by
        simpa [locals] using
          forkStoreDstInkSpot_get_urns I srcInkNew srcArtNew dstInkNew dstArtNew utab vtab
            srcInkSpot dstInkSpot)]
    rw [hloadSrcArt]
  exact vatEvalExpr_or_false_right
    (vatEvalExpr_ge_uint256_false hutab hdust hgtDust)
    (vatEvalExpr_eq_uint256_zero_false hsrcArt hsrcArtPos)

theorem evalExpr_fork_dst_dust_final {evm : EVM.State} {I : ExecutionEnv}
    (srcInkNew srcArtNew dstInkNew dstArtNew utab vtab srcInkSpot dstInkSpot dust : UInt256)
    (hsz164 : 164 ≤ I.calldata.size)
    (hloadDust :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (forkIlkDustSlot I) = dust)
    (hloadDstArt :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (forkDstArtSlot I) = dstArtNew)
    (hcond : dust.toNat ≤ vtab.toNat ∨ dstArtNew.toNat = 0) :
    evalExpr? config
      { contract := contract,
        locals :=
          forkStoreDstInkSpot I srcInkNew srcArtNew dstInkNew dstArtNew utab vtab
            srcInkSpot dstInkSpot } evm
      (eitherExpr
        (.binary .ge (.var "vtab") (.storage (ilksF (.var "ilk") "dust")))
        (.binary .eq (.storage (urnsF (.var "ilk") (.var "dst") "art")) (.intLit 0))) =
      .ok (.bool true) := by
  let locals :=
    forkStoreDstInkSpot I srcInkNew srcArtNew dstInkNew dstArtNew utab vtab srcInkSpot
      dstInkSpot
  have hvtab :
      evalExpr? config { contract := contract, locals := locals } evm (.var "vtab") =
        .ok (.int (Int.ofNat vtab.toNat)) :=
    vatEvalExpr_varUInt256 (by
      simpa [locals] using
        forkStoreDstInkSpot_get_vtab I srcInkNew srcArtNew dstInkNew dstArtNew utab vtab
          srcInkSpot dstInkSpot)
  have hdust :
      evalExpr? config { contract := contract, locals := locals } evm
        (.storage (ilksF (.var "ilk") "dust")) =
        .ok (.int (Int.ofNat dust.toNat)) := by
    rw [evalExpr_fork_ilk_dust_locals locals hsz164
      (by
        simpa [locals] using
          forkStoreDstInkSpot_get_ilk I srcInkNew srcArtNew dstInkNew dstArtNew utab vtab
            srcInkSpot dstInkSpot)
      (by
        simpa [locals] using
          forkStoreDstInkSpot_get_ilks I srcInkNew srcArtNew dstInkNew dstArtNew utab vtab
            srcInkSpot dstInkSpot)]
    rw [hloadDust]
  cases hcond with
  | inl hge =>
      exact vatEvalExpr_or_true_left
        (vatEvalExpr_ge_uint256_true hvtab hdust hge)
  | inr hzero =>
      by_cases hge : dust.toNat ≤ vtab.toNat
      · exact vatEvalExpr_or_true_left
          (vatEvalExpr_ge_uint256_true hvtab hdust hge)
      · have hleft := vatEvalExpr_ge_uint256_false hvtab hdust (Nat.lt_of_not_ge hge)
        have hdstArt :
            evalExpr? config { contract := contract, locals := locals } evm
              (.storage (urnsF (.var "ilk") (.var "dst") "art")) =
              .ok (.int (Int.ofNat dstArtNew.toNat)) := by
          rw [evalExpr_fork_dst_art_locals locals hsz164
            (by
              simpa [locals] using
                forkStoreDstInkSpot_get_ilk I srcInkNew srcArtNew dstInkNew dstArtNew utab
                  vtab srcInkSpot dstInkSpot)
            (by
              simpa [locals] using
                forkStoreDstInkSpot_get_dst I srcInkNew srcArtNew dstInkNew dstArtNew utab
                  vtab srcInkSpot dstInkSpot)
            (by
              simpa [locals] using
                forkStoreDstInkSpot_get_urns I srcInkNew srcArtNew dstInkNew dstArtNew utab
                  vtab srcInkSpot dstInkSpot)]
          rw [hloadDstArt]
        exact vatEvalExpr_or_false_right hleft
          (vatEvalExpr_eq_uint256_zero_true hdstArt hzero)

theorem evalExpr_fork_dst_dust_false_final {evm : EVM.State} {I : ExecutionEnv}
    (srcInkNew srcArtNew dstInkNew dstArtNew utab vtab srcInkSpot dstInkSpot dust : UInt256)
    (hsz164 : 164 ≤ I.calldata.size)
    (hloadDust :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (forkIlkDustSlot I) = dust)
    (hloadDstArt :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (forkDstArtSlot I) = dstArtNew)
    (hgtDust : vtab.toNat < dust.toNat)
    (hdstArtPos : 0 < dstArtNew.toNat) :
    evalExpr? config
      { contract := contract,
        locals :=
          forkStoreDstInkSpot I srcInkNew srcArtNew dstInkNew dstArtNew utab vtab
            srcInkSpot dstInkSpot } evm
      (eitherExpr
        (.binary .ge (.var "vtab") (.storage (ilksF (.var "ilk") "dust")))
        (.binary .eq (.storage (urnsF (.var "ilk") (.var "dst") "art")) (.intLit 0))) =
      .ok (.bool false) := by
  let locals :=
    forkStoreDstInkSpot I srcInkNew srcArtNew dstInkNew dstArtNew utab vtab srcInkSpot
      dstInkSpot
  have hvtab :
      evalExpr? config { contract := contract, locals := locals } evm (.var "vtab") =
        .ok (.int (Int.ofNat vtab.toNat)) :=
    vatEvalExpr_varUInt256 (by
      simpa [locals] using
        forkStoreDstInkSpot_get_vtab I srcInkNew srcArtNew dstInkNew dstArtNew utab vtab
          srcInkSpot dstInkSpot)
  have hdust :
      evalExpr? config { contract := contract, locals := locals } evm
        (.storage (ilksF (.var "ilk") "dust")) =
        .ok (.int (Int.ofNat dust.toNat)) := by
    rw [evalExpr_fork_ilk_dust_locals locals hsz164
      (by
        simpa [locals] using
          forkStoreDstInkSpot_get_ilk I srcInkNew srcArtNew dstInkNew dstArtNew utab vtab
            srcInkSpot dstInkSpot)
      (by
        simpa [locals] using
          forkStoreDstInkSpot_get_ilks I srcInkNew srcArtNew dstInkNew dstArtNew utab vtab
            srcInkSpot dstInkSpot)]
    rw [hloadDust]
  have hdstArt :
      evalExpr? config { contract := contract, locals := locals } evm
        (.storage (urnsF (.var "ilk") (.var "dst") "art")) =
        .ok (.int (Int.ofNat dstArtNew.toNat)) := by
    rw [evalExpr_fork_dst_art_locals locals hsz164
      (by
        simpa [locals] using
          forkStoreDstInkSpot_get_ilk I srcInkNew srcArtNew dstInkNew dstArtNew utab vtab
            srcInkSpot dstInkSpot)
      (by
        simpa [locals] using
          forkStoreDstInkSpot_get_dst I srcInkNew srcArtNew dstInkNew dstArtNew utab vtab
            srcInkSpot dstInkSpot)
      (by
        simpa [locals] using
          forkStoreDstInkSpot_get_urns I srcInkNew srcArtNew dstInkNew dstArtNew utab vtab
            srcInkSpot dstInkSpot)]
    rw [hloadDstArt]
  exact vatEvalExpr_or_false_right
    (vatEvalExpr_ge_uint256_false hvtab hdust hgtDust)
    (vatEvalExpr_eq_uint256_zero_false hdstArt hdstArtPos)

set_option maxHeartbeats 1000000 in
theorem execForkSourceOk {evm0 : EVM.State} {I : ExecutionEnv}
    (srcInkOld srcInkNew srcArtOld srcArtNew dstInkOld dstInkNew dstArtOld dstArtNew
      srcArtFinal dstArtFinal srcInkFinal dstInkFinal rate spot utab vtab
      srcInkSpot dstInkSpot : UInt256)
    (hwei : evm0.executionEnv.weiValue = ⟨0⟩)
    (hsz164 : 164 ≤ I.calldata.size)
    (hloadSrcInk :
      Solm.EVM.storageLoad evm0 evm0.executionEnv.codeOwner (forkSrcInkSlot I) = srcInkOld)
    (hsrcInkNew : srcInkNew = UInt256.sub srcInkOld (forkDinkWord I))
    (hsrcInkGuardNeg : forkDinkInt I ≤ 0 ∨ srcInkNew.toNat ≤ srcInkOld.toNat)
    (hsrcInkGuardPos : 0 ≤ forkDinkInt I ∨ srcInkOld.toNat ≤ srcInkNew.toNat)
    (hloadSrcArt :
      Solm.EVM.storageLoad
        (Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner (forkSrcInkSlot I)
          srcInkNew)
        (Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner (forkSrcInkSlot I)
          srcInkNew).executionEnv.codeOwner
        (forkSrcArtSlot I) = srcArtOld)
    (hsrcArtNew : srcArtNew = UInt256.sub srcArtOld (forkDartWord I))
    (hsrcArtGuardNeg : forkDartInt I ≤ 0 ∨ srcArtNew.toNat ≤ srcArtOld.toNat)
    (hsrcArtGuardPos : 0 ≤ forkDartInt I ∨ srcArtOld.toNat ≤ srcArtNew.toNat)
    (hloadDstInk :
      Solm.EVM.storageLoad
        (Solm.EVM.storageStore
          (Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner (forkSrcInkSlot I)
            srcInkNew)
          evm0.executionEnv.codeOwner (forkSrcArtSlot I) srcArtNew)
        evm0.executionEnv.codeOwner (forkDstInkSlot I) = dstInkOld)
    (hdstInkNew : dstInkNew = forkDinkWord I + dstInkOld)
    (hdstInkGuardNeg : 0 ≤ forkDinkInt I ∨ dstInkNew.toNat ≤ dstInkOld.toNat)
    (hdstInkGuardPos : forkDinkInt I ≤ 0 ∨ dstInkOld.toNat ≤ dstInkNew.toNat)
    (hloadDstArt :
      Solm.EVM.storageLoad
        (Solm.EVM.storageStore
          (Solm.EVM.storageStore
            (Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner (forkSrcInkSlot I)
              srcInkNew)
            evm0.executionEnv.codeOwner (forkSrcArtSlot I) srcArtNew)
          evm0.executionEnv.codeOwner (forkDstInkSlot I) dstInkNew)
        evm0.executionEnv.codeOwner (forkDstArtSlot I) = dstArtOld)
    (hdstArtNew : dstArtNew = forkDartWord I + dstArtOld)
    (hdstArtGuardNeg : 0 ≤ forkDartInt I ∨ dstArtNew.toNat ≤ dstArtOld.toNat)
    (hdstArtGuardPos : forkDartInt I ≤ 0 ∨ dstArtOld.toNat ≤ dstArtNew.toNat)
    (hloadSrcArtFinal :
      Solm.EVM.storageLoad
        (Solm.EVM.storageStore
          (Solm.EVM.storageStore
            (Solm.EVM.storageStore
              (Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner (forkSrcInkSlot I)
                srcInkNew)
              evm0.executionEnv.codeOwner (forkSrcArtSlot I) srcArtNew)
            evm0.executionEnv.codeOwner (forkDstInkSlot I) dstInkNew)
          evm0.executionEnv.codeOwner (forkDstArtSlot I) dstArtNew)
        evm0.executionEnv.codeOwner (forkSrcArtSlot I) = srcArtFinal)
    (hloadDstArtFinal :
      Solm.EVM.storageLoad
        (Solm.EVM.storageStore
          (Solm.EVM.storageStore
            (Solm.EVM.storageStore
              (Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner (forkSrcInkSlot I)
                srcInkNew)
              evm0.executionEnv.codeOwner (forkSrcArtSlot I) srcArtNew)
            evm0.executionEnv.codeOwner (forkDstInkSlot I) dstInkNew)
          evm0.executionEnv.codeOwner (forkDstArtSlot I) dstArtNew)
        evm0.executionEnv.codeOwner (forkDstArtSlot I) = dstArtFinal)
    (hloadSrcInkFinal :
      Solm.EVM.storageLoad
        (Solm.EVM.storageStore
          (Solm.EVM.storageStore
            (Solm.EVM.storageStore
              (Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner (forkSrcInkSlot I)
                srcInkNew)
              evm0.executionEnv.codeOwner (forkSrcArtSlot I) srcArtNew)
            evm0.executionEnv.codeOwner (forkDstInkSlot I) dstInkNew)
          evm0.executionEnv.codeOwner (forkDstArtSlot I) dstArtNew)
        evm0.executionEnv.codeOwner (forkSrcInkSlot I) = srcInkFinal)
    (hloadDstInkFinal :
      Solm.EVM.storageLoad
        (Solm.EVM.storageStore
          (Solm.EVM.storageStore
            (Solm.EVM.storageStore
              (Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner (forkSrcInkSlot I)
                srcInkNew)
              evm0.executionEnv.codeOwner (forkSrcArtSlot I) srcArtNew)
            evm0.executionEnv.codeOwner (forkDstInkSlot I) dstInkNew)
          evm0.executionEnv.codeOwner (forkDstArtSlot I) dstArtNew)
        evm0.executionEnv.codeOwner (forkDstInkSlot I) = dstInkFinal)
    (hloadRate :
      Solm.EVM.storageLoad
        (Solm.EVM.storageStore
          (Solm.EVM.storageStore
            (Solm.EVM.storageStore
              (Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner (forkSrcInkSlot I)
                srcInkNew)
              evm0.executionEnv.codeOwner (forkSrcArtSlot I) srcArtNew)
            evm0.executionEnv.codeOwner (forkDstInkSlot I) dstInkNew)
          evm0.executionEnv.codeOwner (forkDstArtSlot I) dstArtNew)
        evm0.executionEnv.codeOwner (forkIlkRateSlot I) = rate)
    (hloadSpot :
      Solm.EVM.storageLoad
        (Solm.EVM.storageStore
          (Solm.EVM.storageStore
            (Solm.EVM.storageStore
              (Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner (forkSrcInkSlot I)
                srcInkNew)
              evm0.executionEnv.codeOwner (forkSrcArtSlot I) srcArtNew)
            evm0.executionEnv.codeOwner (forkDstInkSlot I) dstInkNew)
          evm0.executionEnv.codeOwner (forkDstArtSlot I) dstArtNew)
        evm0.executionEnv.codeOwner (forkIlkSpotSlot I) = spot)
    (hutabProd : utab = UInt256.mul srcArtFinal rate)
    (hutabFit : srcArtFinal.toNat * rate.toNat < UInt256.size)
    (hutabGuard : rate.toNat = 0 ∨ utab.toNat / rate.toNat = srcArtFinal.toNat)
    (hvtabProd : vtab = UInt256.mul dstArtFinal rate)
    (hvtabFit : dstArtFinal.toNat * rate.toNat < UInt256.size)
    (hvtabGuard : rate.toNat = 0 ∨ vtab.toNat / rate.toNat = dstArtFinal.toNat)
    (hsrcInkSpotProd : srcInkSpot = UInt256.mul srcInkFinal spot)
    (hsrcInkSpotFit : srcInkFinal.toNat * spot.toNat < UInt256.size)
    (hsrcInkSpotGuard : spot.toNat = 0 ∨ srcInkSpot.toNat / spot.toNat = srcInkFinal.toNat)
    (hdstInkSpotProd : dstInkSpot = UInt256.mul dstInkFinal spot)
    (hdstInkSpotFit : dstInkFinal.toNat * spot.toNat < UInt256.size)
    (hdstInkSpotGuard : spot.toNat = 0 ∨ dstInkSpot.toNat / spot.toNat = dstInkFinal.toNat) :
    let evm1 := Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner
      (forkSrcInkSlot I) srcInkNew
    let evm2 := Solm.EVM.storageStore evm1 evm1.executionEnv.codeOwner
      (forkSrcArtSlot I) srcArtNew
    let evm3 := Solm.EVM.storageStore evm2 evm2.executionEnv.codeOwner
      (forkDstInkSlot I) dstInkNew
    let evm4 := Solm.EVM.storageStore evm3 evm3.executionEnv.codeOwner
      (forkDstArtSlot I) dstArtNew
    let finalLocals :=
      forkStoreDstInkSpotFinal I srcInkNew srcArtNew dstInkNew dstArtNew
        srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab vtab srcInkSpot dstInkSpot
    evalExpr? config { contract := contract, locals := finalLocals } evm4
        (bothExpr (wishExpr (.var "src") sender) (wishExpr (.var "dst") sender)) =
        .ok (.bool true) →
    evalExpr? config { contract := contract, locals := finalLocals } evm4
        (.binary .le (.var "utab") (.var "srcInkSpot")) = .ok (.bool true) →
    evalExpr? config { contract := contract, locals := finalLocals } evm4
        (.binary .le (.var "vtab") (.var "dstInkSpot")) = .ok (.bool true) →
    evalExpr? config { contract := contract, locals := finalLocals } evm4
        (eitherExpr
          (.binary .ge (.var "utab") (.storage (ilksF (.var "ilk") "dust")))
          (.binary .eq (.var "srcArtFinal") (.intLit 0))) =
        .ok (.bool true) →
    evalExpr? config { contract := contract, locals := finalLocals } evm4
        (eitherExpr
          (.binary .ge (.var "vtab") (.storage (ilksF (.var "ilk") "dust")))
          (.binary .eq (.var "dstArtFinal") (.intLit 0))) =
        .ok (.bool true) →
    ExecTransitionBody config contract evm0 (forkStore I) forkTransition.body
      (.returned { contract := contract, locals := finalLocals } evm4 none) := by
  intro evm1 evm2 evm3 evm4 finalLocals hwish hutabLe hvtabLe hsrcDust hdstDust
  have hprefix :
      ExecBlock config { contract := contract, locals := forkStore I } evm0 nonpayable
        (.ok { contract := contract, locals := forkStore I } evm0) := by
    change ExecBlock config { contract := contract, locals := forkStore I } evm0
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)) ]
      (.ok { contract := contract, locals := forkStore I } evm0)
    exact ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwei))
      ExecBlock.nil
  have hsrcInkBlock :=
    execForkSrcInkUpdateOk (evm := evm0) (I := I) (locals := forkStore I)
      srcInkOld srcInkNew hsz164 (forkStore_get_ilk I) (forkStore_get_src I)
      (forkStore_get_dink I) (forkStore_urns I) hloadSrcInk hsrcInkNew
      hsrcInkGuardNeg hsrcInkGuardPos
  have hsrcArtBlock :=
    execForkSrcArtUpdateOk (evm := evm1) (I := I)
      (locals := forkStoreSrcInkNew I srcInkNew) srcArtOld srcArtNew hsz164
      (forkStoreSrcInkNew_get_ilk I srcInkNew)
      (forkStoreSrcInkNew_get_src I srcInkNew)
      (forkStoreSrcInkNew_get_dart I srcInkNew)
      (forkStoreSrcInkNew_get_urns I srcInkNew)
      (by simpa [evm1, storageStore_executionEnv] using hloadSrcArt) hsrcArtNew
      hsrcArtGuardNeg hsrcArtGuardPos
  have hdstInkBlock :=
    execForkDstInkUpdateOk (evm := evm2) (I := I)
      (locals := forkStoreSrcArtNew I srcInkNew srcArtNew) dstInkOld dstInkNew hsz164
      (forkStoreSrcArtNew_get_ilk I srcInkNew srcArtNew)
      (forkStoreSrcArtNew_get_dst I srcInkNew srcArtNew)
      (forkStoreSrcArtNew_get_dink I srcInkNew srcArtNew)
      (forkStoreSrcArtNew_get_urns I srcInkNew srcArtNew)
      (by simpa [evm1, evm2, storageStore_executionEnv] using hloadDstInk) hdstInkNew
      hdstInkGuardNeg hdstInkGuardPos
  have hdstArtBlock :=
    execForkDstArtUpdateOk (evm := evm3) (I := I)
      (locals := forkStoreDstInkNew I srcInkNew srcArtNew dstInkNew) dstArtOld dstArtNew
      hsz164 (forkStoreDstInkNew_get_ilk I srcInkNew srcArtNew dstInkNew)
      (forkStoreDstInkNew_get_dst I srcInkNew srcArtNew dstInkNew)
      (forkStoreDstInkNew_get_dart I srcInkNew srcArtNew dstInkNew)
      (forkStoreDstInkNew_get_urns I srcInkNew srcArtNew dstInkNew)
      (by simpa [evm1, evm2, evm3, storageStore_executionEnv] using hloadDstArt)
      hdstArtNew hdstArtGuardNeg hdstArtGuardPos
  have hfinalLoadsBlock :=
    execForkFinalLoadsOk (evm := evm4) (I := I)
      srcInkNew srcArtNew dstInkNew dstArtNew srcArtFinal dstArtFinal
      srcInkFinal dstInkFinal hsz164
      (by
        simpa [evm1, evm2, evm3, evm4, storageStore_executionEnv] using
          hloadSrcArtFinal)
      (by
        simpa [evm1, evm2, evm3, evm4, storageStore_executionEnv] using
          hloadDstArtFinal)
      (by
        simpa [evm1, evm2, evm3, evm4, storageStore_executionEnv] using
          hloadSrcInkFinal)
      (by
        simpa [evm1, evm2, evm3, evm4, storageStore_executionEnv] using
          hloadDstInkFinal)
  let localsFinal :=
    forkStoreFinalLoads I srcInkNew srcArtNew dstInkNew dstArtNew srcArtFinal
      dstArtFinal srcInkFinal dstInkFinal
  have hloadRateFinal :
      Solm.EVM.storageLoad evm4 evm4.executionEnv.codeOwner (forkIlkRateSlot I) = rate := by
    simpa [evm1, evm2, evm3, evm4, storageStore_executionEnv] using hloadRate
  have hloadSpotFinal :
      Solm.EVM.storageLoad evm4 evm4.executionEnv.codeOwner (forkIlkSpotSlot I) = spot := by
    simpa [evm1, evm2, evm3, evm4, storageStore_executionEnv] using hloadSpot
  have hutabBlock :=
    execForkUtabFinalMulOk (evm := evm4) (I := I)
      srcInkNew srcArtNew dstInkNew dstArtNew srcArtFinal dstArtFinal
      srcInkFinal dstInkFinal rate utab hsz164 hloadRateFinal
      hutabProd hutabFit hutabGuard
  have hvtabBlock :=
    execForkVtabFinalMulOk (evm := evm4) (I := I)
      srcInkNew srcArtNew dstInkNew dstArtNew srcArtFinal dstArtFinal
      srcInkFinal dstInkFinal rate utab vtab hsz164 hloadRateFinal
      hvtabProd hvtabFit hvtabGuard
  have hsrcInkSpotBlock :=
    execForkSrcInkSpotFinalMulOk (evm := evm4) (I := I)
      srcInkNew srcArtNew dstInkNew dstArtNew srcArtFinal dstArtFinal
      srcInkFinal dstInkFinal spot utab vtab srcInkSpot hsz164 hloadSpotFinal
      hsrcInkSpotProd hsrcInkSpotFit hsrcInkSpotGuard
  have hdstInkSpotBlock :=
    execForkDstInkSpotFinalMulOk (evm := evm4) (I := I)
      srcInkNew srcArtNew dstInkNew dstArtNew srcArtFinal dstArtFinal
      srcInkFinal dstInkFinal spot utab vtab srcInkSpot dstInkSpot hsz164 hloadSpotFinal
      hdstInkSpotProd hdstInkSpotFit hdstInkSpotGuard
  have hfinalBlock :
      ExecBlock config { contract := contract, locals := finalLocals } evm4
        [ .require (bothExpr (wishExpr (.var "src") sender) (wishExpr (.var "dst") sender)),
          .require (.binary .le (.var "utab") (.var "srcInkSpot")),
          .require (.binary .le (.var "vtab") (.var "dstInkSpot")),
          .require
            (eitherExpr
              (.binary .ge (.var "utab") (.storage (ilksF (.var "ilk") "dust")))
              (.binary .eq (.var "srcArtFinal") (.intLit 0))),
          .require
            (eitherExpr
              (.binary .ge (.var "vtab") (.storage (ilksF (.var "ilk") "dust")))
              (.binary .eq (.var "dstArtFinal") (.intLit 0))) ]
        (.ok { contract := contract, locals := finalLocals } evm4) :=
    execForkFinalRequiresOk hwish hutabLe hvtabLe hsrcDust hdstDust
  have h01 := execBlock_append hprefix hsrcInkBlock
  have h02 := execBlock_append h01 hsrcArtBlock
  have h03 := execBlock_append h02 hdstInkBlock
  have h04 := execBlock_append h03 hdstArtBlock
  have h05 := execBlock_append h04 hfinalLoadsBlock
  have h06 := execBlock_append h05 hutabBlock
  have h06 := execBlock_append h06 hvtabBlock
  have h07 := execBlock_append h06 hsrcInkSpotBlock
  have hblock := execBlock_append h07 hdstInkSpotBlock
  have hblock := execBlock_append hblock hfinalBlock
  simpa [ExecTransitionBody, forkTransition, nonpayable, checkedSubSignedInto,
    checkedAddSignedInto, checkedMulUintInto, List.append_assoc, storageStore_executionEnv] using
    ExecFuncBody.execBlockOK hblock

theorem execForkSourceRevertSrcInkGuardNeg {evm0 : EVM.State} {I : ExecutionEnv}
    (srcInkOld srcInkNew : UInt256)
    (hwei : evm0.executionEnv.weiValue = ⟨0⟩)
    (hsz164 : 164 ≤ I.calldata.size)
    (hloadSrcInk :
      Solm.EVM.storageLoad evm0 evm0.executionEnv.codeOwner (forkSrcInkSlot I) = srcInkOld)
    (hsrcInkNew : srcInkNew = UInt256.sub srcInkOld (forkDinkWord I))
    (hfail :
      ¬ (UInt256.sgt (forkDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.gt srcInkNew srcInkOld = ⟨0⟩)) :
    ExecTransitionBody config contract evm0 (forkStore I) forkTransition.body .reverted := by
  have hprefix :
      ExecBlock config { contract := contract, locals := forkStore I } evm0 nonpayable
        (.ok { contract := contract, locals := forkStore I } evm0) := by
    change ExecBlock config { contract := contract, locals := forkStore I } evm0
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)) ]
      (.ok { contract := contract, locals := forkStore I } evm0)
    exact ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwei))
      ExecBlock.nil
  have hsrcInkRevert :
      ExecBlock config { contract := contract, locals := forkStore I } evm0
        (checkedSubSignedInto "srcInkNew"
          (.storage (urnsF (.var "ilk") (.var "src") "ink")) (.var "dink") ++
          [ .assign .storage (urnsF (.var "ilk") (.var "src") "ink")
            (.var "srcInkNew") ])
        .reverted :=
    execForkSrcInkUpdateRevertGuardNeg (evm := evm0) (I := I) (locals := forkStore I)
      srcInkOld srcInkNew hsz164 (forkStore_get_ilk I) (forkStore_get_src I)
      (forkStore_get_dink I) (forkStore_urns I) hloadSrcInk hsrcInkNew hfail
  have h01 := execBlock_append hprefix hsrcInkRevert
  have hblock := execBlock_append_term
    (s2 :=
      checkedSubSignedInto "srcArtNew"
        (.storage (urnsF (.var "ilk") (.var "src") "art")) (.var "dart") ++
      [ .assign .storage (urnsF (.var "ilk") (.var "src") "art")
        (.var "srcArtNew") ] ++
      checkedAddSignedInto "dstInkNew"
        (.storage (urnsF (.var "ilk") (.var "dst") "ink")) (.var "dink") ++
      [ .assign .storage (urnsF (.var "ilk") (.var "dst") "ink")
        (.var "dstInkNew") ] ++
      checkedAddSignedInto "dstArtNew"
        (.storage (urnsF (.var "ilk") (.var "dst") "art")) (.var "dart") ++
      [ .assign .storage (urnsF (.var "ilk") (.var "dst") "art")
        (.var "dstArtNew") ] ++
      [ .letDecl "srcArtFinal" (some uint256)
          (.storage (urnsF (.var "ilk") (.var "src") "art")),
        .letDecl "dstArtFinal" (some uint256)
          (.storage (urnsF (.var "ilk") (.var "dst") "art")),
        .letDecl "srcInkFinal" (some uint256)
          (.storage (urnsF (.var "ilk") (.var "src") "ink")),
        .letDecl "dstInkFinal" (some uint256)
          (.storage (urnsF (.var "ilk") (.var "dst") "ink")) ] ++
      checkedMulUintInto "utab" (.var "srcArtFinal")
        (.storage (ilksF (.var "ilk") "rate")) ++
      checkedMulUintInto "vtab" (.var "dstArtFinal")
        (.storage (ilksF (.var "ilk") "rate")) ++
      checkedMulUintInto "srcInkSpot" (.var "srcInkFinal")
        (.storage (ilksF (.var "ilk") "spot")) ++
      checkedMulUintInto "dstInkSpot" (.var "dstInkFinal")
        (.storage (ilksF (.var "ilk") "spot")) ++
      [ .require (bothExpr (wishExpr (.var "src") sender) (wishExpr (.var "dst") sender)),
        .require (.binary .le (.var "utab") (.var "srcInkSpot")),
        .require (.binary .le (.var "vtab") (.var "dstInkSpot")),
        .require
          (eitherExpr
            (.binary .ge (.var "utab") (.storage (ilksF (.var "ilk") "dust")))
            (.binary .eq (.var "srcArtFinal") (.intLit 0))),
        .require
          (eitherExpr
            (.binary .ge (.var "vtab") (.storage (ilksF (.var "ilk") "dust")))
            (.binary .eq (.var "dstArtFinal") (.intLit 0))) ])
    h01 (by intro f e h; cases h)
  simpa [ExecTransitionBody, forkTransition, nonpayable, checkedSubSignedInto,
    checkedAddSignedInto, checkedMulUintInto, List.append_assoc] using
    ExecFuncBody.execBlockRevert hblock

theorem execForkSourceRevertSrcInkGuardPos {evm0 : EVM.State} {I : ExecutionEnv}
    (srcInkOld srcInkNew : UInt256)
    (hwei : evm0.executionEnv.weiValue = ⟨0⟩)
    (hsz164 : 164 ≤ I.calldata.size)
    (hloadSrcInk :
      Solm.EVM.storageLoad evm0 evm0.executionEnv.codeOwner (forkSrcInkSlot I) = srcInkOld)
    (hsrcInkNew : srcInkNew = UInt256.sub srcInkOld (forkDinkWord I))
    (hguardNeg :
      UInt256.sgt (forkDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.gt srcInkNew srcInkOld = ⟨0⟩)
    (hfail :
      ¬ (UInt256.slt (forkDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.lt srcInkNew srcInkOld = ⟨0⟩)) :
    ExecTransitionBody config contract evm0 (forkStore I) forkTransition.body .reverted := by
  have hprefix :
      ExecBlock config { contract := contract, locals := forkStore I } evm0 nonpayable
        (.ok { contract := contract, locals := forkStore I } evm0) := by
    change ExecBlock config { contract := contract, locals := forkStore I } evm0
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)) ]
      (.ok { contract := contract, locals := forkStore I } evm0)
    exact ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwei))
      ExecBlock.nil
  have hsrcInkRevert :
      ExecBlock config { contract := contract, locals := forkStore I } evm0
        (checkedSubSignedInto "srcInkNew"
          (.storage (urnsF (.var "ilk") (.var "src") "ink")) (.var "dink") ++
          [ .assign .storage (urnsF (.var "ilk") (.var "src") "ink")
            (.var "srcInkNew") ])
        .reverted :=
    execForkSrcInkUpdateRevertGuardPos (evm := evm0) (I := I) (locals := forkStore I)
      srcInkOld srcInkNew hsz164 (forkStore_get_ilk I) (forkStore_get_src I)
      (forkStore_get_dink I) (forkStore_urns I) hloadSrcInk hsrcInkNew hguardNeg hfail
  have h01 := execBlock_append hprefix hsrcInkRevert
  have hblock := execBlock_append_term
    (s2 :=
      checkedSubSignedInto "srcArtNew"
        (.storage (urnsF (.var "ilk") (.var "src") "art")) (.var "dart") ++
      [ .assign .storage (urnsF (.var "ilk") (.var "src") "art")
        (.var "srcArtNew") ] ++
      checkedAddSignedInto "dstInkNew"
        (.storage (urnsF (.var "ilk") (.var "dst") "ink")) (.var "dink") ++
      [ .assign .storage (urnsF (.var "ilk") (.var "dst") "ink")
        (.var "dstInkNew") ] ++
      checkedAddSignedInto "dstArtNew"
        (.storage (urnsF (.var "ilk") (.var "dst") "art")) (.var "dart") ++
      [ .assign .storage (urnsF (.var "ilk") (.var "dst") "art")
        (.var "dstArtNew") ] ++
      [ .letDecl "srcArtFinal" (some uint256)
          (.storage (urnsF (.var "ilk") (.var "src") "art")),
        .letDecl "dstArtFinal" (some uint256)
          (.storage (urnsF (.var "ilk") (.var "dst") "art")),
        .letDecl "srcInkFinal" (some uint256)
          (.storage (urnsF (.var "ilk") (.var "src") "ink")),
        .letDecl "dstInkFinal" (some uint256)
          (.storage (urnsF (.var "ilk") (.var "dst") "ink")) ] ++
      checkedMulUintInto "utab" (.var "srcArtFinal")
        (.storage (ilksF (.var "ilk") "rate")) ++
      checkedMulUintInto "vtab" (.var "dstArtFinal")
        (.storage (ilksF (.var "ilk") "rate")) ++
      checkedMulUintInto "srcInkSpot" (.var "srcInkFinal")
        (.storage (ilksF (.var "ilk") "spot")) ++
      checkedMulUintInto "dstInkSpot" (.var "dstInkFinal")
        (.storage (ilksF (.var "ilk") "spot")) ++
      [ .require (bothExpr (wishExpr (.var "src") sender) (wishExpr (.var "dst") sender)),
        .require (.binary .le (.var "utab") (.var "srcInkSpot")),
        .require (.binary .le (.var "vtab") (.var "dstInkSpot")),
        .require
          (eitherExpr
            (.binary .ge (.var "utab") (.storage (ilksF (.var "ilk") "dust")))
            (.binary .eq (.var "srcArtFinal") (.intLit 0))),
        .require
          (eitherExpr
            (.binary .ge (.var "vtab") (.storage (ilksF (.var "ilk") "dust")))
            (.binary .eq (.var "dstArtFinal") (.intLit 0))) ])
    h01 (by intro f e h; cases h)
  simpa [ExecTransitionBody, forkTransition, nonpayable, checkedSubSignedInto,
    checkedAddSignedInto, checkedMulUintInto, List.append_assoc] using
    ExecFuncBody.execBlockRevert hblock

theorem execForkSourceRevertSrcArtGuardNeg {evm0 : EVM.State} {I : ExecutionEnv}
    (srcInkOld srcInkNew srcArtOld srcArtNew : UInt256)
    (hwei : evm0.executionEnv.weiValue = ⟨0⟩)
    (hsz164 : 164 ≤ I.calldata.size)
    (hloadSrcInk :
      Solm.EVM.storageLoad evm0 evm0.executionEnv.codeOwner (forkSrcInkSlot I) = srcInkOld)
    (hsrcInkNew : srcInkNew = UInt256.sub srcInkOld (forkDinkWord I))
    (hsrcInkGuardNeg : forkDinkInt I ≤ 0 ∨ srcInkNew.toNat ≤ srcInkOld.toNat)
    (hsrcInkGuardPos : 0 ≤ forkDinkInt I ∨ srcInkOld.toNat ≤ srcInkNew.toNat)
    (hloadSrcArt :
      Solm.EVM.storageLoad
        (Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner (forkSrcInkSlot I)
          srcInkNew)
        (Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner (forkSrcInkSlot I)
          srcInkNew).executionEnv.codeOwner
        (forkSrcArtSlot I) = srcArtOld)
    (hsrcArtNew : srcArtNew = UInt256.sub srcArtOld (forkDartWord I))
    (hfail :
      ¬ (UInt256.sgt (forkDartWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.gt srcArtNew srcArtOld = ⟨0⟩)) :
    ExecTransitionBody config contract evm0 (forkStore I) forkTransition.body .reverted := by
  let evm1 := Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner
    (forkSrcInkSlot I) srcInkNew
  have hprefix :
      ExecBlock config { contract := contract, locals := forkStore I } evm0 nonpayable
        (.ok { contract := contract, locals := forkStore I } evm0) := by
    change ExecBlock config { contract := contract, locals := forkStore I } evm0
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)) ]
      (.ok { contract := contract, locals := forkStore I } evm0)
    exact ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwei))
      ExecBlock.nil
  have hsrcInkBlock :
      ExecBlock config { contract := contract, locals := forkStore I } evm0
        (checkedSubSignedInto "srcInkNew"
          (.storage (urnsF (.var "ilk") (.var "src") "ink")) (.var "dink") ++
          [ .assign .storage (urnsF (.var "ilk") (.var "src") "ink")
            (.var "srcInkNew") ])
        (.ok { contract := contract, locals := forkStoreSrcInkNew I srcInkNew } evm1) := by
    simpa [evm1] using
      execForkSrcInkUpdateOk (evm := evm0) (I := I) (locals := forkStore I)
        srcInkOld srcInkNew hsz164 (forkStore_get_ilk I) (forkStore_get_src I)
        (forkStore_get_dink I) (forkStore_urns I) hloadSrcInk hsrcInkNew
        hsrcInkGuardNeg hsrcInkGuardPos
  have hsrcArtRevert :
      ExecBlock config { contract := contract, locals := forkStoreSrcInkNew I srcInkNew } evm1
        (checkedSubSignedInto "srcArtNew"
          (.storage (urnsF (.var "ilk") (.var "src") "art")) (.var "dart") ++
          [ .assign .storage (urnsF (.var "ilk") (.var "src") "art")
            (.var "srcArtNew") ])
        .reverted := by
    exact execForkSrcArtUpdateRevertGuardNeg (evm := evm1) (I := I)
      (locals := forkStoreSrcInkNew I srcInkNew) srcArtOld srcArtNew hsz164
      (forkStoreSrcInkNew_get_ilk I srcInkNew)
      (forkStoreSrcInkNew_get_src I srcInkNew)
      (forkStoreSrcInkNew_get_dart I srcInkNew)
      (forkStoreSrcInkNew_get_urns I srcInkNew)
      (by simpa [evm1] using hloadSrcArt) hsrcArtNew hfail
  have h01 := execBlock_append hprefix hsrcInkBlock
  have h02 := execBlock_append h01 hsrcArtRevert
  have hblock := execBlock_append_term
    (s2 :=
      checkedAddSignedInto "dstInkNew"
        (.storage (urnsF (.var "ilk") (.var "dst") "ink")) (.var "dink") ++
      [ .assign .storage (urnsF (.var "ilk") (.var "dst") "ink")
        (.var "dstInkNew") ] ++
      checkedAddSignedInto "dstArtNew"
        (.storage (urnsF (.var "ilk") (.var "dst") "art")) (.var "dart") ++
      [ .assign .storage (urnsF (.var "ilk") (.var "dst") "art")
        (.var "dstArtNew") ] ++
      [ .letDecl "srcArtFinal" (some uint256)
          (.storage (urnsF (.var "ilk") (.var "src") "art")),
        .letDecl "dstArtFinal" (some uint256)
          (.storage (urnsF (.var "ilk") (.var "dst") "art")),
        .letDecl "srcInkFinal" (some uint256)
          (.storage (urnsF (.var "ilk") (.var "src") "ink")),
        .letDecl "dstInkFinal" (some uint256)
          (.storage (urnsF (.var "ilk") (.var "dst") "ink")) ] ++
      checkedMulUintInto "utab" (.var "srcArtFinal")
        (.storage (ilksF (.var "ilk") "rate")) ++
      checkedMulUintInto "vtab" (.var "dstArtFinal")
        (.storage (ilksF (.var "ilk") "rate")) ++
      checkedMulUintInto "srcInkSpot" (.var "srcInkFinal")
        (.storage (ilksF (.var "ilk") "spot")) ++
      checkedMulUintInto "dstInkSpot" (.var "dstInkFinal")
        (.storage (ilksF (.var "ilk") "spot")) ++
      [ .require (bothExpr (wishExpr (.var "src") sender) (wishExpr (.var "dst") sender)),
        .require (.binary .le (.var "utab") (.var "srcInkSpot")),
        .require (.binary .le (.var "vtab") (.var "dstInkSpot")),
        .require
          (eitherExpr
            (.binary .ge (.var "utab") (.storage (ilksF (.var "ilk") "dust")))
            (.binary .eq (.var "srcArtFinal") (.intLit 0))),
        .require
          (eitherExpr
            (.binary .ge (.var "vtab") (.storage (ilksF (.var "ilk") "dust")))
            (.binary .eq (.var "dstArtFinal") (.intLit 0))) ])
    h02 (by intro f e h; cases h)
  simpa [ExecTransitionBody, forkTransition, nonpayable, checkedSubSignedInto,
    checkedAddSignedInto, checkedMulUintInto, List.append_assoc] using
    ExecFuncBody.execBlockRevert hblock

theorem execForkSourceRevertSrcArtGuardPos {evm0 : EVM.State} {I : ExecutionEnv}
    (srcInkOld srcInkNew srcArtOld srcArtNew : UInt256)
    (hwei : evm0.executionEnv.weiValue = ⟨0⟩)
    (hsz164 : 164 ≤ I.calldata.size)
    (hloadSrcInk :
      Solm.EVM.storageLoad evm0 evm0.executionEnv.codeOwner (forkSrcInkSlot I) = srcInkOld)
    (hsrcInkNew : srcInkNew = UInt256.sub srcInkOld (forkDinkWord I))
    (hsrcInkGuardNeg : forkDinkInt I ≤ 0 ∨ srcInkNew.toNat ≤ srcInkOld.toNat)
    (hsrcInkGuardPos : 0 ≤ forkDinkInt I ∨ srcInkOld.toNat ≤ srcInkNew.toNat)
    (hloadSrcArt :
      Solm.EVM.storageLoad
        (Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner (forkSrcInkSlot I)
          srcInkNew)
        (Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner (forkSrcInkSlot I)
          srcInkNew).executionEnv.codeOwner
        (forkSrcArtSlot I) = srcArtOld)
    (hsrcArtNew : srcArtNew = UInt256.sub srcArtOld (forkDartWord I))
    (hguardNeg :
      UInt256.sgt (forkDartWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.gt srcArtNew srcArtOld = ⟨0⟩)
    (hfail :
      ¬ (UInt256.slt (forkDartWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.lt srcArtNew srcArtOld = ⟨0⟩)) :
    ExecTransitionBody config contract evm0 (forkStore I) forkTransition.body .reverted := by
  let evm1 := Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner
    (forkSrcInkSlot I) srcInkNew
  have hprefix :
      ExecBlock config { contract := contract, locals := forkStore I } evm0 nonpayable
        (.ok { contract := contract, locals := forkStore I } evm0) := by
    change ExecBlock config { contract := contract, locals := forkStore I } evm0
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)) ]
      (.ok { contract := contract, locals := forkStore I } evm0)
    exact ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwei))
      ExecBlock.nil
  have hsrcInkBlock :
      ExecBlock config { contract := contract, locals := forkStore I } evm0
        (checkedSubSignedInto "srcInkNew"
          (.storage (urnsF (.var "ilk") (.var "src") "ink")) (.var "dink") ++
          [ .assign .storage (urnsF (.var "ilk") (.var "src") "ink")
            (.var "srcInkNew") ])
        (.ok { contract := contract, locals := forkStoreSrcInkNew I srcInkNew } evm1) := by
    simpa [evm1] using
      execForkSrcInkUpdateOk (evm := evm0) (I := I) (locals := forkStore I)
        srcInkOld srcInkNew hsz164 (forkStore_get_ilk I) (forkStore_get_src I)
        (forkStore_get_dink I) (forkStore_urns I) hloadSrcInk hsrcInkNew
        hsrcInkGuardNeg hsrcInkGuardPos
  have hsrcArtRevert :
      ExecBlock config { contract := contract, locals := forkStoreSrcInkNew I srcInkNew } evm1
        (checkedSubSignedInto "srcArtNew"
          (.storage (urnsF (.var "ilk") (.var "src") "art")) (.var "dart") ++
          [ .assign .storage (urnsF (.var "ilk") (.var "src") "art")
            (.var "srcArtNew") ])
        .reverted := by
    exact execForkSrcArtUpdateRevertGuardPos (evm := evm1) (I := I)
      (locals := forkStoreSrcInkNew I srcInkNew) srcArtOld srcArtNew hsz164
      (forkStoreSrcInkNew_get_ilk I srcInkNew)
      (forkStoreSrcInkNew_get_src I srcInkNew)
      (forkStoreSrcInkNew_get_dart I srcInkNew)
      (forkStoreSrcInkNew_get_urns I srcInkNew)
      (by simpa [evm1] using hloadSrcArt) hsrcArtNew hguardNeg hfail
  have h01 := execBlock_append hprefix hsrcInkBlock
  have h02 := execBlock_append h01 hsrcArtRevert
  have hblock := execBlock_append_term
    (s2 :=
      checkedAddSignedInto "dstInkNew"
        (.storage (urnsF (.var "ilk") (.var "dst") "ink")) (.var "dink") ++
      [ .assign .storage (urnsF (.var "ilk") (.var "dst") "ink")
        (.var "dstInkNew") ] ++
      checkedAddSignedInto "dstArtNew"
        (.storage (urnsF (.var "ilk") (.var "dst") "art")) (.var "dart") ++
      [ .assign .storage (urnsF (.var "ilk") (.var "dst") "art")
        (.var "dstArtNew") ] ++
      [ .letDecl "srcArtFinal" (some uint256)
          (.storage (urnsF (.var "ilk") (.var "src") "art")),
        .letDecl "dstArtFinal" (some uint256)
          (.storage (urnsF (.var "ilk") (.var "dst") "art")),
        .letDecl "srcInkFinal" (some uint256)
          (.storage (urnsF (.var "ilk") (.var "src") "ink")),
        .letDecl "dstInkFinal" (some uint256)
          (.storage (urnsF (.var "ilk") (.var "dst") "ink")) ] ++
      checkedMulUintInto "utab" (.var "srcArtFinal")
        (.storage (ilksF (.var "ilk") "rate")) ++
      checkedMulUintInto "vtab" (.var "dstArtFinal")
        (.storage (ilksF (.var "ilk") "rate")) ++
      checkedMulUintInto "srcInkSpot" (.var "srcInkFinal")
        (.storage (ilksF (.var "ilk") "spot")) ++
      checkedMulUintInto "dstInkSpot" (.var "dstInkFinal")
        (.storage (ilksF (.var "ilk") "spot")) ++
      [ .require (bothExpr (wishExpr (.var "src") sender) (wishExpr (.var "dst") sender)),
        .require (.binary .le (.var "utab") (.var "srcInkSpot")),
        .require (.binary .le (.var "vtab") (.var "dstInkSpot")),
        .require
          (eitherExpr
            (.binary .ge (.var "utab") (.storage (ilksF (.var "ilk") "dust")))
            (.binary .eq (.var "srcArtFinal") (.intLit 0))),
        .require
          (eitherExpr
            (.binary .ge (.var "vtab") (.storage (ilksF (.var "ilk") "dust")))
            (.binary .eq (.var "dstArtFinal") (.intLit 0))) ])
    h02 (by intro f e h; cases h)
  simpa [ExecTransitionBody, forkTransition, nonpayable, checkedSubSignedInto,
    checkedAddSignedInto, checkedMulUintInto, List.append_assoc] using
    ExecFuncBody.execBlockRevert hblock

theorem execForkSourceRevertDstInkGuardNeg {evm0 : EVM.State} {I : ExecutionEnv}
    (srcInkOld srcInkNew srcArtOld srcArtNew dstInkOld dstInkNew : UInt256)
    (hwei : evm0.executionEnv.weiValue = ⟨0⟩)
    (hsz164 : 164 ≤ I.calldata.size)
    (hloadSrcInk :
      Solm.EVM.storageLoad evm0 evm0.executionEnv.codeOwner (forkSrcInkSlot I) = srcInkOld)
    (hsrcInkNew : srcInkNew = UInt256.sub srcInkOld (forkDinkWord I))
    (hsrcInkGuardNeg : forkDinkInt I ≤ 0 ∨ srcInkNew.toNat ≤ srcInkOld.toNat)
    (hsrcInkGuardPos : 0 ≤ forkDinkInt I ∨ srcInkOld.toNat ≤ srcInkNew.toNat)
    (hloadSrcArt :
      Solm.EVM.storageLoad
        (Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner (forkSrcInkSlot I)
          srcInkNew)
        evm0.executionEnv.codeOwner (forkSrcArtSlot I) = srcArtOld)
    (hsrcArtNew : srcArtNew = UInt256.sub srcArtOld (forkDartWord I))
    (hsrcArtGuardNeg : forkDartInt I ≤ 0 ∨ srcArtNew.toNat ≤ srcArtOld.toNat)
    (hsrcArtGuardPos : 0 ≤ forkDartInt I ∨ srcArtOld.toNat ≤ srcArtNew.toNat)
    (hloadDstInk :
      Solm.EVM.storageLoad
        (Solm.EVM.storageStore
          (Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner (forkSrcInkSlot I)
            srcInkNew)
          evm0.executionEnv.codeOwner (forkSrcArtSlot I) srcArtNew)
        evm0.executionEnv.codeOwner (forkDstInkSlot I) = dstInkOld)
    (hdstInkNew : dstInkNew = forkDinkWord I + dstInkOld)
    (hfail :
      ¬ (UInt256.slt (forkDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.gt dstInkNew dstInkOld = ⟨0⟩)) :
    ExecTransitionBody config contract evm0 (forkStore I) forkTransition.body .reverted := by
  let evm1 := Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner
    (forkSrcInkSlot I) srcInkNew
  let evm2 := Solm.EVM.storageStore evm1 evm1.executionEnv.codeOwner
    (forkSrcArtSlot I) srcArtNew
  have hprefix :
      ExecBlock config { contract := contract, locals := forkStore I } evm0 nonpayable
        (.ok { contract := contract, locals := forkStore I } evm0) := by
    change ExecBlock config { contract := contract, locals := forkStore I } evm0
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)) ]
      (.ok { contract := contract, locals := forkStore I } evm0)
    exact ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwei))
      ExecBlock.nil
  have hsrcInkBlock :=
    execForkSrcInkUpdateOk (evm := evm0) (I := I) (locals := forkStore I)
      srcInkOld srcInkNew hsz164 (forkStore_get_ilk I) (forkStore_get_src I)
      (forkStore_get_dink I) (forkStore_urns I) hloadSrcInk hsrcInkNew
      hsrcInkGuardNeg hsrcInkGuardPos
  have hsrcArtBlock :=
    execForkSrcArtUpdateOk (evm := evm1) (I := I)
      (locals := forkStoreSrcInkNew I srcInkNew) srcArtOld srcArtNew hsz164
      (forkStoreSrcInkNew_get_ilk I srcInkNew)
      (forkStoreSrcInkNew_get_src I srcInkNew)
      (forkStoreSrcInkNew_get_dart I srcInkNew)
      (forkStoreSrcInkNew_get_urns I srcInkNew)
      (by simpa [evm1, storageStore_executionEnv] using hloadSrcArt) hsrcArtNew
      hsrcArtGuardNeg hsrcArtGuardPos
  have hdstInkRevert :
      ExecBlock config { contract := contract, locals := forkStoreSrcArtNew I srcInkNew srcArtNew }
        evm2
        (checkedAddSignedInto "dstInkNew"
          (.storage (urnsF (.var "ilk") (.var "dst") "ink")) (.var "dink") ++
          [ .assign .storage (urnsF (.var "ilk") (.var "dst") "ink")
            (.var "dstInkNew") ])
        .reverted := by
    exact execForkDstInkUpdateRevertGuardNeg (evm := evm2) (I := I)
      (locals := forkStoreSrcArtNew I srcInkNew srcArtNew) dstInkOld dstInkNew hsz164
      (forkStoreSrcArtNew_get_ilk I srcInkNew srcArtNew)
      (forkStoreSrcArtNew_get_dst I srcInkNew srcArtNew)
      (forkStoreSrcArtNew_get_dink I srcInkNew srcArtNew)
      (forkStoreSrcArtNew_get_urns I srcInkNew srcArtNew)
      (by simpa [evm1, evm2, storageStore_executionEnv] using hloadDstInk)
      hdstInkNew hfail
  have h01 := execBlock_append hprefix hsrcInkBlock
  have h02 := execBlock_append h01 hsrcArtBlock
  have h03 := execBlock_append h02 hdstInkRevert
  have hblock := execBlock_append_term
    (s2 :=
      checkedAddSignedInto "dstArtNew"
        (.storage (urnsF (.var "ilk") (.var "dst") "art")) (.var "dart") ++
      [ .assign .storage (urnsF (.var "ilk") (.var "dst") "art")
        (.var "dstArtNew") ] ++
      [ .letDecl "srcArtFinal" (some uint256)
          (.storage (urnsF (.var "ilk") (.var "src") "art")),
        .letDecl "dstArtFinal" (some uint256)
          (.storage (urnsF (.var "ilk") (.var "dst") "art")),
        .letDecl "srcInkFinal" (some uint256)
          (.storage (urnsF (.var "ilk") (.var "src") "ink")),
        .letDecl "dstInkFinal" (some uint256)
          (.storage (urnsF (.var "ilk") (.var "dst") "ink")) ] ++
      checkedMulUintInto "utab" (.var "srcArtFinal")
        (.storage (ilksF (.var "ilk") "rate")) ++
      checkedMulUintInto "vtab" (.var "dstArtFinal")
        (.storage (ilksF (.var "ilk") "rate")) ++
      checkedMulUintInto "srcInkSpot" (.var "srcInkFinal")
        (.storage (ilksF (.var "ilk") "spot")) ++
      checkedMulUintInto "dstInkSpot" (.var "dstInkFinal")
        (.storage (ilksF (.var "ilk") "spot")) ++
      [ .require (bothExpr (wishExpr (.var "src") sender) (wishExpr (.var "dst") sender)),
        .require (.binary .le (.var "utab") (.var "srcInkSpot")),
        .require (.binary .le (.var "vtab") (.var "dstInkSpot")),
        .require
          (eitherExpr
            (.binary .ge (.var "utab") (.storage (ilksF (.var "ilk") "dust")))
            (.binary .eq (.var "srcArtFinal") (.intLit 0))),
        .require
          (eitherExpr
            (.binary .ge (.var "vtab") (.storage (ilksF (.var "ilk") "dust")))
            (.binary .eq (.var "dstArtFinal") (.intLit 0))) ])
    h03 (by intro f e h; cases h)
  simpa [ExecTransitionBody, forkTransition, nonpayable, checkedSubSignedInto,
    checkedAddSignedInto, checkedMulUintInto, List.append_assoc] using
    ExecFuncBody.execBlockRevert hblock

theorem execForkSourceRevertDstInkGuardPos {evm0 : EVM.State} {I : ExecutionEnv}
    (srcInkOld srcInkNew srcArtOld srcArtNew dstInkOld dstInkNew : UInt256)
    (hwei : evm0.executionEnv.weiValue = ⟨0⟩)
    (hsz164 : 164 ≤ I.calldata.size)
    (hloadSrcInk :
      Solm.EVM.storageLoad evm0 evm0.executionEnv.codeOwner (forkSrcInkSlot I) = srcInkOld)
    (hsrcInkNew : srcInkNew = UInt256.sub srcInkOld (forkDinkWord I))
    (hsrcInkGuardNeg : forkDinkInt I ≤ 0 ∨ srcInkNew.toNat ≤ srcInkOld.toNat)
    (hsrcInkGuardPos : 0 ≤ forkDinkInt I ∨ srcInkOld.toNat ≤ srcInkNew.toNat)
    (hloadSrcArt :
      Solm.EVM.storageLoad
        (Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner (forkSrcInkSlot I)
          srcInkNew)
        evm0.executionEnv.codeOwner (forkSrcArtSlot I) = srcArtOld)
    (hsrcArtNew : srcArtNew = UInt256.sub srcArtOld (forkDartWord I))
    (hsrcArtGuardNeg : forkDartInt I ≤ 0 ∨ srcArtNew.toNat ≤ srcArtOld.toNat)
    (hsrcArtGuardPos : 0 ≤ forkDartInt I ∨ srcArtOld.toNat ≤ srcArtNew.toNat)
    (hloadDstInk :
      Solm.EVM.storageLoad
        (Solm.EVM.storageStore
          (Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner (forkSrcInkSlot I)
            srcInkNew)
          evm0.executionEnv.codeOwner (forkSrcArtSlot I) srcArtNew)
        evm0.executionEnv.codeOwner (forkDstInkSlot I) = dstInkOld)
    (hdstInkNew : dstInkNew = forkDinkWord I + dstInkOld)
    (hguardNeg :
      UInt256.slt (forkDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.gt dstInkNew dstInkOld = ⟨0⟩)
    (hfail :
      ¬ (UInt256.sgt (forkDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.lt dstInkNew dstInkOld = ⟨0⟩)) :
    ExecTransitionBody config contract evm0 (forkStore I) forkTransition.body .reverted := by
  let evm1 := Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner
    (forkSrcInkSlot I) srcInkNew
  let evm2 := Solm.EVM.storageStore evm1 evm1.executionEnv.codeOwner
    (forkSrcArtSlot I) srcArtNew
  have hprefix :
      ExecBlock config { contract := contract, locals := forkStore I } evm0 nonpayable
        (.ok { contract := contract, locals := forkStore I } evm0) := by
    change ExecBlock config { contract := contract, locals := forkStore I } evm0
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)) ]
      (.ok { contract := contract, locals := forkStore I } evm0)
    exact ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwei))
      ExecBlock.nil
  have hsrcInkBlock :=
    execForkSrcInkUpdateOk (evm := evm0) (I := I) (locals := forkStore I)
      srcInkOld srcInkNew hsz164 (forkStore_get_ilk I) (forkStore_get_src I)
      (forkStore_get_dink I) (forkStore_urns I) hloadSrcInk hsrcInkNew
      hsrcInkGuardNeg hsrcInkGuardPos
  have hsrcArtBlock :=
    execForkSrcArtUpdateOk (evm := evm1) (I := I)
      (locals := forkStoreSrcInkNew I srcInkNew) srcArtOld srcArtNew hsz164
      (forkStoreSrcInkNew_get_ilk I srcInkNew)
      (forkStoreSrcInkNew_get_src I srcInkNew)
      (forkStoreSrcInkNew_get_dart I srcInkNew)
      (forkStoreSrcInkNew_get_urns I srcInkNew)
      (by simpa [evm1, storageStore_executionEnv] using hloadSrcArt) hsrcArtNew
      hsrcArtGuardNeg hsrcArtGuardPos
  have hdstInkRevert :
      ExecBlock config { contract := contract, locals := forkStoreSrcArtNew I srcInkNew srcArtNew }
        evm2
        (checkedAddSignedInto "dstInkNew"
          (.storage (urnsF (.var "ilk") (.var "dst") "ink")) (.var "dink") ++
          [ .assign .storage (urnsF (.var "ilk") (.var "dst") "ink")
            (.var "dstInkNew") ])
        .reverted := by
    exact execForkDstInkUpdateRevertGuardPos (evm := evm2) (I := I)
      (locals := forkStoreSrcArtNew I srcInkNew srcArtNew) dstInkOld dstInkNew hsz164
      (forkStoreSrcArtNew_get_ilk I srcInkNew srcArtNew)
      (forkStoreSrcArtNew_get_dst I srcInkNew srcArtNew)
      (forkStoreSrcArtNew_get_dink I srcInkNew srcArtNew)
      (forkStoreSrcArtNew_get_urns I srcInkNew srcArtNew)
      (by simpa [evm1, evm2, storageStore_executionEnv] using hloadDstInk)
      hdstInkNew hguardNeg hfail
  have h01 := execBlock_append hprefix hsrcInkBlock
  have h02 := execBlock_append h01 hsrcArtBlock
  have h03 := execBlock_append h02 hdstInkRevert
  have hblock := execBlock_append_term
    (s2 :=
      checkedAddSignedInto "dstArtNew"
        (.storage (urnsF (.var "ilk") (.var "dst") "art")) (.var "dart") ++
      [ .assign .storage (urnsF (.var "ilk") (.var "dst") "art")
        (.var "dstArtNew") ] ++
      [ .letDecl "srcArtFinal" (some uint256)
          (.storage (urnsF (.var "ilk") (.var "src") "art")),
        .letDecl "dstArtFinal" (some uint256)
          (.storage (urnsF (.var "ilk") (.var "dst") "art")),
        .letDecl "srcInkFinal" (some uint256)
          (.storage (urnsF (.var "ilk") (.var "src") "ink")),
        .letDecl "dstInkFinal" (some uint256)
          (.storage (urnsF (.var "ilk") (.var "dst") "ink")) ] ++
      checkedMulUintInto "utab" (.var "srcArtFinal")
        (.storage (ilksF (.var "ilk") "rate")) ++
      checkedMulUintInto "vtab" (.var "dstArtFinal")
        (.storage (ilksF (.var "ilk") "rate")) ++
      checkedMulUintInto "srcInkSpot" (.var "srcInkFinal")
        (.storage (ilksF (.var "ilk") "spot")) ++
      checkedMulUintInto "dstInkSpot" (.var "dstInkFinal")
        (.storage (ilksF (.var "ilk") "spot")) ++
      [ .require (bothExpr (wishExpr (.var "src") sender) (wishExpr (.var "dst") sender)),
        .require (.binary .le (.var "utab") (.var "srcInkSpot")),
        .require (.binary .le (.var "vtab") (.var "dstInkSpot")),
        .require
          (eitherExpr
            (.binary .ge (.var "utab") (.storage (ilksF (.var "ilk") "dust")))
            (.binary .eq (.var "srcArtFinal") (.intLit 0))),
        .require
          (eitherExpr
            (.binary .ge (.var "vtab") (.storage (ilksF (.var "ilk") "dust")))
            (.binary .eq (.var "dstArtFinal") (.intLit 0))) ])
    h03 (by intro f e h; cases h)
  simpa [ExecTransitionBody, forkTransition, nonpayable, checkedSubSignedInto,
    checkedAddSignedInto, checkedMulUintInto, List.append_assoc] using
    ExecFuncBody.execBlockRevert hblock

theorem execForkSourceRevertDstArtGuardNeg {evm0 : EVM.State} {I : ExecutionEnv}
    (srcInkOld srcInkNew srcArtOld srcArtNew dstInkOld dstInkNew dstArtOld
      dstArtNew : UInt256)
    (hwei : evm0.executionEnv.weiValue = ⟨0⟩)
    (hsz164 : 164 ≤ I.calldata.size)
    (hloadSrcInk :
      Solm.EVM.storageLoad evm0 evm0.executionEnv.codeOwner (forkSrcInkSlot I) = srcInkOld)
    (hsrcInkNew : srcInkNew = UInt256.sub srcInkOld (forkDinkWord I))
    (hsrcInkGuardNeg : forkDinkInt I ≤ 0 ∨ srcInkNew.toNat ≤ srcInkOld.toNat)
    (hsrcInkGuardPos : 0 ≤ forkDinkInt I ∨ srcInkOld.toNat ≤ srcInkNew.toNat)
    (hloadSrcArt :
      Solm.EVM.storageLoad
        (Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner (forkSrcInkSlot I)
          srcInkNew)
        evm0.executionEnv.codeOwner (forkSrcArtSlot I) = srcArtOld)
    (hsrcArtNew : srcArtNew = UInt256.sub srcArtOld (forkDartWord I))
    (hsrcArtGuardNeg : forkDartInt I ≤ 0 ∨ srcArtNew.toNat ≤ srcArtOld.toNat)
    (hsrcArtGuardPos : 0 ≤ forkDartInt I ∨ srcArtOld.toNat ≤ srcArtNew.toNat)
    (hloadDstInk :
      Solm.EVM.storageLoad
        (Solm.EVM.storageStore
          (Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner (forkSrcInkSlot I)
            srcInkNew)
          evm0.executionEnv.codeOwner (forkSrcArtSlot I) srcArtNew)
        evm0.executionEnv.codeOwner (forkDstInkSlot I) = dstInkOld)
    (hdstInkNew : dstInkNew = forkDinkWord I + dstInkOld)
    (hdstInkGuardNeg : 0 ≤ forkDinkInt I ∨ dstInkNew.toNat ≤ dstInkOld.toNat)
    (hdstInkGuardPos : forkDinkInt I ≤ 0 ∨ dstInkOld.toNat ≤ dstInkNew.toNat)
    (hloadDstArt :
      Solm.EVM.storageLoad
        (Solm.EVM.storageStore
          (Solm.EVM.storageStore
            (Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner (forkSrcInkSlot I)
              srcInkNew)
            evm0.executionEnv.codeOwner (forkSrcArtSlot I) srcArtNew)
          evm0.executionEnv.codeOwner (forkDstInkSlot I) dstInkNew)
        evm0.executionEnv.codeOwner (forkDstArtSlot I) = dstArtOld)
    (hdstArtNew : dstArtNew = forkDartWord I + dstArtOld)
    (hfail :
      ¬ (UInt256.slt (forkDartWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.gt dstArtNew dstArtOld = ⟨0⟩)) :
    ExecTransitionBody config contract evm0 (forkStore I) forkTransition.body .reverted := by
  let evm1 := Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner
    (forkSrcInkSlot I) srcInkNew
  let evm2 := Solm.EVM.storageStore evm1 evm1.executionEnv.codeOwner
    (forkSrcArtSlot I) srcArtNew
  let evm3 := Solm.EVM.storageStore evm2 evm2.executionEnv.codeOwner
    (forkDstInkSlot I) dstInkNew
  have hprefix :
      ExecBlock config { contract := contract, locals := forkStore I } evm0 nonpayable
        (.ok { contract := contract, locals := forkStore I } evm0) := by
    change ExecBlock config { contract := contract, locals := forkStore I } evm0
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)) ]
      (.ok { contract := contract, locals := forkStore I } evm0)
    exact ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwei))
      ExecBlock.nil
  have hsrcInkBlock :=
    execForkSrcInkUpdateOk (evm := evm0) (I := I) (locals := forkStore I)
      srcInkOld srcInkNew hsz164 (forkStore_get_ilk I) (forkStore_get_src I)
      (forkStore_get_dink I) (forkStore_urns I) hloadSrcInk hsrcInkNew
      hsrcInkGuardNeg hsrcInkGuardPos
  have hsrcArtBlock :=
    execForkSrcArtUpdateOk (evm := evm1) (I := I)
      (locals := forkStoreSrcInkNew I srcInkNew) srcArtOld srcArtNew hsz164
      (forkStoreSrcInkNew_get_ilk I srcInkNew)
      (forkStoreSrcInkNew_get_src I srcInkNew)
      (forkStoreSrcInkNew_get_dart I srcInkNew)
      (forkStoreSrcInkNew_get_urns I srcInkNew)
      (by simpa [evm1, storageStore_executionEnv] using hloadSrcArt) hsrcArtNew
      hsrcArtGuardNeg hsrcArtGuardPos
  have hdstInkBlock :=
    execForkDstInkUpdateOk (evm := evm2) (I := I)
      (locals := forkStoreSrcArtNew I srcInkNew srcArtNew) dstInkOld dstInkNew hsz164
      (forkStoreSrcArtNew_get_ilk I srcInkNew srcArtNew)
      (forkStoreSrcArtNew_get_dst I srcInkNew srcArtNew)
      (forkStoreSrcArtNew_get_dink I srcInkNew srcArtNew)
      (forkStoreSrcArtNew_get_urns I srcInkNew srcArtNew)
      (by simpa [evm1, evm2, storageStore_executionEnv] using hloadDstInk) hdstInkNew
      hdstInkGuardNeg hdstInkGuardPos
  have hdstArtRevert :
      ExecBlock config
        { contract := contract, locals := forkStoreDstInkNew I srcInkNew srcArtNew dstInkNew }
        evm3
        (checkedAddSignedInto "dstArtNew"
          (.storage (urnsF (.var "ilk") (.var "dst") "art")) (.var "dart") ++
          [ .assign .storage (urnsF (.var "ilk") (.var "dst") "art")
            (.var "dstArtNew") ])
        .reverted := by
    exact execForkDstArtUpdateRevertGuardNeg (evm := evm3) (I := I)
      (locals := forkStoreDstInkNew I srcInkNew srcArtNew dstInkNew) dstArtOld dstArtNew
      hsz164 (forkStoreDstInkNew_get_ilk I srcInkNew srcArtNew dstInkNew)
      (forkStoreDstInkNew_get_dst I srcInkNew srcArtNew dstInkNew)
      (forkStoreDstInkNew_get_dart I srcInkNew srcArtNew dstInkNew)
      (forkStoreDstInkNew_get_urns I srcInkNew srcArtNew dstInkNew)
      (by simpa [evm1, evm2, evm3, storageStore_executionEnv] using hloadDstArt)
      hdstArtNew hfail
  have h01 := execBlock_append hprefix hsrcInkBlock
  have h02 := execBlock_append h01 hsrcArtBlock
  have h03 := execBlock_append h02 hdstInkBlock
  have h04 := execBlock_append h03 hdstArtRevert
  have hblock := execBlock_append_term
    (s2 :=
      [ .letDecl "srcArtFinal" (some uint256)
          (.storage (urnsF (.var "ilk") (.var "src") "art")),
        .letDecl "dstArtFinal" (some uint256)
          (.storage (urnsF (.var "ilk") (.var "dst") "art")),
        .letDecl "srcInkFinal" (some uint256)
          (.storage (urnsF (.var "ilk") (.var "src") "ink")),
        .letDecl "dstInkFinal" (some uint256)
          (.storage (urnsF (.var "ilk") (.var "dst") "ink")) ] ++
      checkedMulUintInto "utab" (.var "srcArtFinal")
        (.storage (ilksF (.var "ilk") "rate")) ++
      checkedMulUintInto "vtab" (.var "dstArtFinal")
        (.storage (ilksF (.var "ilk") "rate")) ++
      checkedMulUintInto "srcInkSpot" (.var "srcInkFinal")
        (.storage (ilksF (.var "ilk") "spot")) ++
      checkedMulUintInto "dstInkSpot" (.var "dstInkFinal")
        (.storage (ilksF (.var "ilk") "spot")) ++
      [ .require (bothExpr (wishExpr (.var "src") sender) (wishExpr (.var "dst") sender)),
        .require (.binary .le (.var "utab") (.var "srcInkSpot")),
        .require (.binary .le (.var "vtab") (.var "dstInkSpot")),
        .require
          (eitherExpr
            (.binary .ge (.var "utab") (.storage (ilksF (.var "ilk") "dust")))
            (.binary .eq (.var "srcArtFinal") (.intLit 0))),
        .require
          (eitherExpr
            (.binary .ge (.var "vtab") (.storage (ilksF (.var "ilk") "dust")))
            (.binary .eq (.var "dstArtFinal") (.intLit 0))) ])
    h04 (by intro f e h; cases h)
  simpa [ExecTransitionBody, forkTransition, nonpayable, checkedSubSignedInto,
    checkedAddSignedInto, checkedMulUintInto, List.append_assoc] using
    ExecFuncBody.execBlockRevert hblock

theorem execForkSourceRevertDstArtGuardPos {evm0 : EVM.State} {I : ExecutionEnv}
    (srcInkOld srcInkNew srcArtOld srcArtNew dstInkOld dstInkNew dstArtOld
      dstArtNew : UInt256)
    (hwei : evm0.executionEnv.weiValue = ⟨0⟩)
    (hsz164 : 164 ≤ I.calldata.size)
    (hloadSrcInk :
      Solm.EVM.storageLoad evm0 evm0.executionEnv.codeOwner (forkSrcInkSlot I) = srcInkOld)
    (hsrcInkNew : srcInkNew = UInt256.sub srcInkOld (forkDinkWord I))
    (hsrcInkGuardNeg : forkDinkInt I ≤ 0 ∨ srcInkNew.toNat ≤ srcInkOld.toNat)
    (hsrcInkGuardPos : 0 ≤ forkDinkInt I ∨ srcInkOld.toNat ≤ srcInkNew.toNat)
    (hloadSrcArt :
      Solm.EVM.storageLoad
        (Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner (forkSrcInkSlot I)
          srcInkNew)
        evm0.executionEnv.codeOwner (forkSrcArtSlot I) = srcArtOld)
    (hsrcArtNew : srcArtNew = UInt256.sub srcArtOld (forkDartWord I))
    (hsrcArtGuardNeg : forkDartInt I ≤ 0 ∨ srcArtNew.toNat ≤ srcArtOld.toNat)
    (hsrcArtGuardPos : 0 ≤ forkDartInt I ∨ srcArtOld.toNat ≤ srcArtNew.toNat)
    (hloadDstInk :
      Solm.EVM.storageLoad
        (Solm.EVM.storageStore
          (Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner (forkSrcInkSlot I)
            srcInkNew)
          evm0.executionEnv.codeOwner (forkSrcArtSlot I) srcArtNew)
        evm0.executionEnv.codeOwner (forkDstInkSlot I) = dstInkOld)
    (hdstInkNew : dstInkNew = forkDinkWord I + dstInkOld)
    (hdstInkGuardNeg : 0 ≤ forkDinkInt I ∨ dstInkNew.toNat ≤ dstInkOld.toNat)
    (hdstInkGuardPos : forkDinkInt I ≤ 0 ∨ dstInkOld.toNat ≤ dstInkNew.toNat)
    (hloadDstArt :
      Solm.EVM.storageLoad
        (Solm.EVM.storageStore
          (Solm.EVM.storageStore
            (Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner (forkSrcInkSlot I)
              srcInkNew)
            evm0.executionEnv.codeOwner (forkSrcArtSlot I) srcArtNew)
          evm0.executionEnv.codeOwner (forkDstInkSlot I) dstInkNew)
        evm0.executionEnv.codeOwner (forkDstArtSlot I) = dstArtOld)
    (hdstArtNew : dstArtNew = forkDartWord I + dstArtOld)
    (hguardNeg :
      UInt256.slt (forkDartWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.gt dstArtNew dstArtOld = ⟨0⟩)
    (hfail :
      ¬ (UInt256.sgt (forkDartWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.lt dstArtNew dstArtOld = ⟨0⟩)) :
    ExecTransitionBody config contract evm0 (forkStore I) forkTransition.body .reverted := by
  let evm1 := Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner
    (forkSrcInkSlot I) srcInkNew
  let evm2 := Solm.EVM.storageStore evm1 evm1.executionEnv.codeOwner
    (forkSrcArtSlot I) srcArtNew
  let evm3 := Solm.EVM.storageStore evm2 evm2.executionEnv.codeOwner
    (forkDstInkSlot I) dstInkNew
  have hprefix :
      ExecBlock config { contract := contract, locals := forkStore I } evm0 nonpayable
        (.ok { contract := contract, locals := forkStore I } evm0) := by
    change ExecBlock config { contract := contract, locals := forkStore I } evm0
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)) ]
      (.ok { contract := contract, locals := forkStore I } evm0)
    exact ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwei))
      ExecBlock.nil
  have hsrcInkBlock :=
    execForkSrcInkUpdateOk (evm := evm0) (I := I) (locals := forkStore I)
      srcInkOld srcInkNew hsz164 (forkStore_get_ilk I) (forkStore_get_src I)
      (forkStore_get_dink I) (forkStore_urns I) hloadSrcInk hsrcInkNew
      hsrcInkGuardNeg hsrcInkGuardPos
  have hsrcArtBlock :=
    execForkSrcArtUpdateOk (evm := evm1) (I := I)
      (locals := forkStoreSrcInkNew I srcInkNew) srcArtOld srcArtNew hsz164
      (forkStoreSrcInkNew_get_ilk I srcInkNew)
      (forkStoreSrcInkNew_get_src I srcInkNew)
      (forkStoreSrcInkNew_get_dart I srcInkNew)
      (forkStoreSrcInkNew_get_urns I srcInkNew)
      (by simpa [evm1, storageStore_executionEnv] using hloadSrcArt) hsrcArtNew
      hsrcArtGuardNeg hsrcArtGuardPos
  have hdstInkBlock :=
    execForkDstInkUpdateOk (evm := evm2) (I := I)
      (locals := forkStoreSrcArtNew I srcInkNew srcArtNew) dstInkOld dstInkNew hsz164
      (forkStoreSrcArtNew_get_ilk I srcInkNew srcArtNew)
      (forkStoreSrcArtNew_get_dst I srcInkNew srcArtNew)
      (forkStoreSrcArtNew_get_dink I srcInkNew srcArtNew)
      (forkStoreSrcArtNew_get_urns I srcInkNew srcArtNew)
      (by simpa [evm1, evm2, storageStore_executionEnv] using hloadDstInk) hdstInkNew
      hdstInkGuardNeg hdstInkGuardPos
  have hdstArtRevert :
      ExecBlock config
        { contract := contract, locals := forkStoreDstInkNew I srcInkNew srcArtNew dstInkNew }
        evm3
        (checkedAddSignedInto "dstArtNew"
          (.storage (urnsF (.var "ilk") (.var "dst") "art")) (.var "dart") ++
          [ .assign .storage (urnsF (.var "ilk") (.var "dst") "art")
            (.var "dstArtNew") ])
        .reverted := by
    exact execForkDstArtUpdateRevertGuardPos (evm := evm3) (I := I)
      (locals := forkStoreDstInkNew I srcInkNew srcArtNew dstInkNew) dstArtOld dstArtNew
      hsz164 (forkStoreDstInkNew_get_ilk I srcInkNew srcArtNew dstInkNew)
      (forkStoreDstInkNew_get_dst I srcInkNew srcArtNew dstInkNew)
      (forkStoreDstInkNew_get_dart I srcInkNew srcArtNew dstInkNew)
      (forkStoreDstInkNew_get_urns I srcInkNew srcArtNew dstInkNew)
      (by simpa [evm1, evm2, evm3, storageStore_executionEnv] using hloadDstArt)
      hdstArtNew hguardNeg hfail
  have h01 := execBlock_append hprefix hsrcInkBlock
  have h02 := execBlock_append h01 hsrcArtBlock
  have h03 := execBlock_append h02 hdstInkBlock
  have h04 := execBlock_append h03 hdstArtRevert
  have hblock := execBlock_append_term
    (s2 :=
      [ .letDecl "srcArtFinal" (some uint256)
          (.storage (urnsF (.var "ilk") (.var "src") "art")),
        .letDecl "dstArtFinal" (some uint256)
          (.storage (urnsF (.var "ilk") (.var "dst") "art")),
        .letDecl "srcInkFinal" (some uint256)
          (.storage (urnsF (.var "ilk") (.var "src") "ink")),
        .letDecl "dstInkFinal" (some uint256)
          (.storage (urnsF (.var "ilk") (.var "dst") "ink")) ] ++
      checkedMulUintInto "utab" (.var "srcArtFinal")
        (.storage (ilksF (.var "ilk") "rate")) ++
      checkedMulUintInto "vtab" (.var "dstArtFinal")
        (.storage (ilksF (.var "ilk") "rate")) ++
      checkedMulUintInto "srcInkSpot" (.var "srcInkFinal")
        (.storage (ilksF (.var "ilk") "spot")) ++
      checkedMulUintInto "dstInkSpot" (.var "dstInkFinal")
        (.storage (ilksF (.var "ilk") "spot")) ++
      [ .require (bothExpr (wishExpr (.var "src") sender) (wishExpr (.var "dst") sender)),
        .require (.binary .le (.var "utab") (.var "srcInkSpot")),
        .require (.binary .le (.var "vtab") (.var "dstInkSpot")),
        .require
          (eitherExpr
            (.binary .ge (.var "utab") (.storage (ilksF (.var "ilk") "dust")))
            (.binary .eq (.var "srcArtFinal") (.intLit 0))),
        .require
          (eitherExpr
            (.binary .ge (.var "vtab") (.storage (ilksF (.var "ilk") "dust")))
            (.binary .eq (.var "dstArtFinal") (.intLit 0))) ])
    h04 (by intro f e h; cases h)
  simpa [ExecTransitionBody, forkTransition, nonpayable, checkedSubSignedInto,
    checkedAddSignedInto, checkedMulUintInto, List.append_assoc] using
    ExecFuncBody.execBlockRevert hblock

set_option maxHeartbeats 1000000 in
theorem execForkSourceRevertUtabMul {evm0 : EVM.State} {I : ExecutionEnv}
    (srcInkOld srcInkNew srcArtOld srcArtNew dstInkOld dstInkNew dstArtOld dstArtNew
      srcArtFinal dstArtFinal srcInkFinal dstInkFinal rate : UInt256)
    (hwei : evm0.executionEnv.weiValue = ⟨0⟩)
    (hsz164 : 164 ≤ I.calldata.size)
    (hloadSrcInk :
      Solm.EVM.storageLoad evm0 evm0.executionEnv.codeOwner (forkSrcInkSlot I) = srcInkOld)
    (hsrcInkNew : srcInkNew = UInt256.sub srcInkOld (forkDinkWord I))
    (hsrcInkGuardNeg : forkDinkInt I ≤ 0 ∨ srcInkNew.toNat ≤ srcInkOld.toNat)
    (hsrcInkGuardPos : 0 ≤ forkDinkInt I ∨ srcInkOld.toNat ≤ srcInkNew.toNat)
    (hloadSrcArt :
      Solm.EVM.storageLoad
        (Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner (forkSrcInkSlot I)
          srcInkNew)
        evm0.executionEnv.codeOwner (forkSrcArtSlot I) = srcArtOld)
    (hsrcArtNew : srcArtNew = UInt256.sub srcArtOld (forkDartWord I))
    (hsrcArtGuardNeg : forkDartInt I ≤ 0 ∨ srcArtNew.toNat ≤ srcArtOld.toNat)
    (hsrcArtGuardPos : 0 ≤ forkDartInt I ∨ srcArtOld.toNat ≤ srcArtNew.toNat)
    (hloadDstInk :
      Solm.EVM.storageLoad
        (Solm.EVM.storageStore
          (Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner (forkSrcInkSlot I)
            srcInkNew)
          evm0.executionEnv.codeOwner (forkSrcArtSlot I) srcArtNew)
        evm0.executionEnv.codeOwner (forkDstInkSlot I) = dstInkOld)
    (hdstInkNew : dstInkNew = forkDinkWord I + dstInkOld)
    (hdstInkGuardNeg : 0 ≤ forkDinkInt I ∨ dstInkNew.toNat ≤ dstInkOld.toNat)
    (hdstInkGuardPos : forkDinkInt I ≤ 0 ∨ dstInkOld.toNat ≤ dstInkNew.toNat)
    (hloadDstArt :
      Solm.EVM.storageLoad
        (Solm.EVM.storageStore
          (Solm.EVM.storageStore
            (Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner (forkSrcInkSlot I)
              srcInkNew)
            evm0.executionEnv.codeOwner (forkSrcArtSlot I) srcArtNew)
          evm0.executionEnv.codeOwner (forkDstInkSlot I) dstInkNew)
        evm0.executionEnv.codeOwner (forkDstArtSlot I) = dstArtOld)
    (hdstArtNew : dstArtNew = forkDartWord I + dstArtOld)
    (hdstArtGuardNeg : 0 ≤ forkDartInt I ∨ dstArtNew.toNat ≤ dstArtOld.toNat)
    (hdstArtGuardPos : forkDartInt I ≤ 0 ∨ dstArtOld.toNat ≤ dstArtNew.toNat)
    (hloadSrcArtFinal :
      Solm.EVM.storageLoad
        (Solm.EVM.storageStore
          (Solm.EVM.storageStore
            (Solm.EVM.storageStore
              (Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner (forkSrcInkSlot I)
                srcInkNew)
              evm0.executionEnv.codeOwner (forkSrcArtSlot I) srcArtNew)
            evm0.executionEnv.codeOwner (forkDstInkSlot I) dstInkNew)
        evm0.executionEnv.codeOwner (forkDstArtSlot I) dstArtNew)
        evm0.executionEnv.codeOwner (forkSrcArtSlot I) = srcArtFinal)
    (hloadDstArtFinal :
      Solm.EVM.storageLoad
        (Solm.EVM.storageStore
          (Solm.EVM.storageStore
            (Solm.EVM.storageStore
              (Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner (forkSrcInkSlot I)
                srcInkNew)
              evm0.executionEnv.codeOwner (forkSrcArtSlot I) srcArtNew)
            evm0.executionEnv.codeOwner (forkDstInkSlot I) dstInkNew)
        evm0.executionEnv.codeOwner (forkDstArtSlot I) dstArtNew)
        evm0.executionEnv.codeOwner (forkDstArtSlot I) = dstArtFinal)
    (hloadSrcInkFinal :
      Solm.EVM.storageLoad
        (Solm.EVM.storageStore
          (Solm.EVM.storageStore
            (Solm.EVM.storageStore
              (Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner (forkSrcInkSlot I)
                srcInkNew)
              evm0.executionEnv.codeOwner (forkSrcArtSlot I) srcArtNew)
            evm0.executionEnv.codeOwner (forkDstInkSlot I) dstInkNew)
        evm0.executionEnv.codeOwner (forkDstArtSlot I) dstArtNew)
        evm0.executionEnv.codeOwner (forkSrcInkSlot I) = srcInkFinal)
    (hloadDstInkFinal :
      Solm.EVM.storageLoad
        (Solm.EVM.storageStore
          (Solm.EVM.storageStore
            (Solm.EVM.storageStore
              (Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner (forkSrcInkSlot I)
                srcInkNew)
              evm0.executionEnv.codeOwner (forkSrcArtSlot I) srcArtNew)
            evm0.executionEnv.codeOwner (forkDstInkSlot I) dstInkNew)
        evm0.executionEnv.codeOwner (forkDstArtSlot I) dstArtNew)
        evm0.executionEnv.codeOwner (forkDstInkSlot I) = dstInkFinal)
    (hloadRate :
      Solm.EVM.storageLoad
        (Solm.EVM.storageStore
          (Solm.EVM.storageStore
            (Solm.EVM.storageStore
              (Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner (forkSrcInkSlot I)
                srcInkNew)
              evm0.executionEnv.codeOwner (forkSrcArtSlot I) srcArtNew)
            evm0.executionEnv.codeOwner (forkDstInkSlot I) dstInkNew)
          evm0.executionEnv.codeOwner (forkDstArtSlot I) dstArtNew)
        evm0.executionEnv.codeOwner (forkIlkRateSlot I) = rate)
    (hover : UInt256.size ≤ srcArtFinal.toNat * rate.toNat) :
    ExecTransitionBody config contract evm0 (forkStore I) forkTransition.body .reverted := by
  let evm1 := Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner
    (forkSrcInkSlot I) srcInkNew
  let evm2 := Solm.EVM.storageStore evm1 evm1.executionEnv.codeOwner
    (forkSrcArtSlot I) srcArtNew
  let evm3 := Solm.EVM.storageStore evm2 evm2.executionEnv.codeOwner
    (forkDstInkSlot I) dstInkNew
  let evm4 := Solm.EVM.storageStore evm3 evm3.executionEnv.codeOwner
    (forkDstArtSlot I) dstArtNew
  have hprefix :
      ExecBlock config { contract := contract, locals := forkStore I } evm0 nonpayable
        (.ok { contract := contract, locals := forkStore I } evm0) := by
    change ExecBlock config { contract := contract, locals := forkStore I } evm0
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)) ]
      (.ok { contract := contract, locals := forkStore I } evm0)
    exact ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwei))
      ExecBlock.nil
  have hsrcInkBlock :=
    execForkSrcInkUpdateOk (evm := evm0) (I := I) (locals := forkStore I)
      srcInkOld srcInkNew hsz164 (forkStore_get_ilk I) (forkStore_get_src I)
      (forkStore_get_dink I) (forkStore_urns I) hloadSrcInk hsrcInkNew
      hsrcInkGuardNeg hsrcInkGuardPos
  have hsrcArtBlock :=
    execForkSrcArtUpdateOk (evm := evm1) (I := I)
      (locals := forkStoreSrcInkNew I srcInkNew) srcArtOld srcArtNew hsz164
      (forkStoreSrcInkNew_get_ilk I srcInkNew)
      (forkStoreSrcInkNew_get_src I srcInkNew)
      (forkStoreSrcInkNew_get_dart I srcInkNew)
      (forkStoreSrcInkNew_get_urns I srcInkNew)
      (by simpa [evm1, storageStore_executionEnv] using hloadSrcArt) hsrcArtNew
      hsrcArtGuardNeg hsrcArtGuardPos
  have hdstInkBlock :=
    execForkDstInkUpdateOk (evm := evm2) (I := I)
      (locals := forkStoreSrcArtNew I srcInkNew srcArtNew) dstInkOld dstInkNew hsz164
      (forkStoreSrcArtNew_get_ilk I srcInkNew srcArtNew)
      (forkStoreSrcArtNew_get_dst I srcInkNew srcArtNew)
      (forkStoreSrcArtNew_get_dink I srcInkNew srcArtNew)
      (forkStoreSrcArtNew_get_urns I srcInkNew srcArtNew)
      (by simpa [evm1, evm2, storageStore_executionEnv] using hloadDstInk) hdstInkNew
      hdstInkGuardNeg hdstInkGuardPos
  have hdstArtBlock :=
    execForkDstArtUpdateOk (evm := evm3) (I := I)
      (locals := forkStoreDstInkNew I srcInkNew srcArtNew dstInkNew) dstArtOld dstArtNew
      hsz164 (forkStoreDstInkNew_get_ilk I srcInkNew srcArtNew dstInkNew)
      (forkStoreDstInkNew_get_dst I srcInkNew srcArtNew dstInkNew)
      (forkStoreDstInkNew_get_dart I srcInkNew srcArtNew dstInkNew)
      (forkStoreDstInkNew_get_urns I srcInkNew srcArtNew dstInkNew)
      (by simpa [evm1, evm2, evm3, storageStore_executionEnv] using hloadDstArt)
      hdstArtNew hdstArtGuardNeg hdstArtGuardPos
  have hfinalLoadsBlock :=
    execForkFinalLoadsOk (evm := evm4) (I := I)
      srcInkNew srcArtNew dstInkNew dstArtNew srcArtFinal dstArtFinal
      srcInkFinal dstInkFinal hsz164
      (by
        simpa [evm1, evm2, evm3, evm4, storageStore_executionEnv] using
          hloadSrcArtFinal)
      (by
        simpa [evm1, evm2, evm3, evm4, storageStore_executionEnv] using
          hloadDstArtFinal)
      (by
        simpa [evm1, evm2, evm3, evm4, storageStore_executionEnv] using
          hloadSrcInkFinal)
      (by
        simpa [evm1, evm2, evm3, evm4, storageStore_executionEnv] using
          hloadDstInkFinal)
  let localsFinal :=
    forkStoreFinalLoads I srcInkNew srcArtNew dstInkNew dstArtNew srcArtFinal
      dstArtFinal srcInkFinal dstInkFinal
  have hloadRateFinal :
      Solm.EVM.storageLoad evm4 evm4.executionEnv.codeOwner (forkIlkRateSlot I) = rate := by
    simpa [evm1, evm2, evm3, evm4, storageStore_executionEnv] using hloadRate
  have hsrcArtEval :
      evalExpr? config { contract := contract, locals := localsFinal } evm4
        (.var "srcArtFinal") = .ok (.int (Int.ofNat srcArtFinal.toNat)) := by
    exact vatEvalExpr_varUInt256 (by
      simpa [localsFinal] using
        forkStoreFinalLoads_get_srcArtFinal I srcInkNew srcArtNew dstInkNew dstArtNew
          srcArtFinal dstArtFinal srcInkFinal dstInkFinal)
  have hrateEval :
      evalExpr? config { contract := contract, locals := localsFinal } evm4
        (.storage (ilksF (.var "ilk") "rate")) =
        .ok (.int (Int.ofNat rate.toNat)) := by
    rw [evalExpr_fork_ilk_rate_locals localsFinal hsz164
      (by
        change
          (forkStoreFinalLoads I srcInkNew srcArtNew dstInkNew dstArtNew
            srcArtFinal dstArtFinal srcInkFinal dstInkFinal).get? "ilk" =
            some (forkIlkValue I)
        exact forkStoreFinalLoads_get_ilk I srcInkNew srcArtNew dstInkNew
          dstArtNew srcArtFinal dstArtFinal srcInkFinal dstInkFinal)
      (by
        change
          (forkStoreFinalLoads I srcInkNew srcArtNew dstInkNew dstArtNew
            srcArtFinal dstArtFinal srcInkFinal dstInkFinal).get? "ilks" =
            none
        exact forkStoreFinalLoads_get_ilks I srcInkNew srcArtNew dstInkNew
          dstArtNew srcArtFinal dstArtFinal srcInkFinal dstInkFinal)]
    simpa [hloadRateFinal]
  have hutabRevert :
      ExecBlock config { contract := contract, locals := localsFinal } evm4
        (checkedMulUintInto "utab" (.var "srcArtFinal")
          (.storage (ilksF (.var "ilk") "rate"))) .reverted :=
    execForkMulUintIntoRevertOfOverflow (evm := evm4) (locals := localsFinal)
      "utab" (.var "srcArtFinal") (.storage (ilksF (.var "ilk") "rate"))
      srcArtFinal rate hsrcArtEval hrateEval hover
  have h01 := execBlock_append hprefix hsrcInkBlock
  have h02 := execBlock_append h01 hsrcArtBlock
  have h03 := execBlock_append h02 hdstInkBlock
  have h04 := execBlock_append h03 hdstArtBlock
  have h05 := execBlock_append h04 hfinalLoadsBlock
  have h06 := execBlock_append h05 hutabRevert
  have hblock := execBlock_append_term
    (s2 :=
      checkedMulUintInto "vtab" (.var "dstArtFinal")
        (.storage (ilksF (.var "ilk") "rate")) ++
      checkedMulUintInto "srcInkSpot" (.var "srcInkFinal")
        (.storage (ilksF (.var "ilk") "spot")) ++
      checkedMulUintInto "dstInkSpot" (.var "dstInkFinal")
        (.storage (ilksF (.var "ilk") "spot")) ++
      [ .require (bothExpr (wishExpr (.var "src") sender) (wishExpr (.var "dst") sender)),
        .require (.binary .le (.var "utab") (.var "srcInkSpot")),
        .require (.binary .le (.var "vtab") (.var "dstInkSpot")),
        .require
          (eitherExpr
            (.binary .ge (.var "utab") (.storage (ilksF (.var "ilk") "dust")))
            (.binary .eq (.var "srcArtFinal") (.intLit 0))),
        .require
          (eitherExpr
            (.binary .ge (.var "vtab") (.storage (ilksF (.var "ilk") "dust")))
            (.binary .eq (.var "dstArtFinal") (.intLit 0))) ])
    h06 (by intro f e h; cases h)
  simpa [ExecTransitionBody, forkTransition, nonpayable, checkedSubSignedInto,
    checkedAddSignedInto, checkedMulUintInto, List.append_assoc, storageStore_executionEnv]
    using ExecFuncBody.execBlockRevert hblock

set_option maxHeartbeats 1000000 in
theorem execForkSourceRevertVtabMul {evm0 : EVM.State} {I : ExecutionEnv}
    (srcInkOld srcInkNew srcArtOld srcArtNew dstInkOld dstInkNew dstArtOld dstArtNew
      srcArtFinal dstArtFinal srcInkFinal dstInkFinal rate utab : UInt256)
    (hwei : evm0.executionEnv.weiValue = ⟨0⟩)
    (hsz164 : 164 ≤ I.calldata.size)
    (hloadSrcInk :
      Solm.EVM.storageLoad evm0 evm0.executionEnv.codeOwner (forkSrcInkSlot I) = srcInkOld)
    (hsrcInkNew : srcInkNew = srcInkOld.sub (forkDinkWord I))
    (hsrcInkGuardNeg : forkDinkInt I ≤ 0 ∨ srcInkNew.toNat ≤ srcInkOld.toNat)
    (hsrcInkGuardPos : 0 ≤ forkDinkInt I ∨ srcInkOld.toNat ≤ srcInkNew.toNat)
    (hloadSrcArt :
      Solm.EVM.storageLoad
        (Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner (forkSrcInkSlot I)
          srcInkNew)
        evm0.executionEnv.codeOwner (forkSrcArtSlot I) = srcArtOld)
    (hsrcArtNew : srcArtNew = srcArtOld.sub (forkDartWord I))
    (hsrcArtGuardNeg : forkDartInt I ≤ 0 ∨ srcArtNew.toNat ≤ srcArtOld.toNat)
    (hsrcArtGuardPos : 0 ≤ forkDartInt I ∨ srcArtOld.toNat ≤ srcArtNew.toNat)
    (hloadDstInk :
      Solm.EVM.storageLoad
        (Solm.EVM.storageStore
          (Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner (forkSrcInkSlot I)
            srcInkNew)
          evm0.executionEnv.codeOwner (forkSrcArtSlot I) srcArtNew)
        evm0.executionEnv.codeOwner (forkDstInkSlot I) = dstInkOld)
    (hdstInkNew : dstInkNew = forkDinkWord I + dstInkOld)
    (hdstInkGuardNeg : 0 ≤ forkDinkInt I ∨ dstInkNew.toNat ≤ dstInkOld.toNat)
    (hdstInkGuardPos : forkDinkInt I ≤ 0 ∨ dstInkOld.toNat ≤ dstInkNew.toNat)
    (hloadDstArt :
      Solm.EVM.storageLoad
        (Solm.EVM.storageStore
          (Solm.EVM.storageStore
            (Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner (forkSrcInkSlot I)
              srcInkNew)
            evm0.executionEnv.codeOwner (forkSrcArtSlot I) srcArtNew)
          evm0.executionEnv.codeOwner (forkDstInkSlot I) dstInkNew)
        evm0.executionEnv.codeOwner (forkDstArtSlot I) = dstArtOld)
    (hdstArtNew : dstArtNew = forkDartWord I + dstArtOld)
    (hdstArtGuardNeg : 0 ≤ forkDartInt I ∨ dstArtNew.toNat ≤ dstArtOld.toNat)
    (hdstArtGuardPos : forkDartInt I ≤ 0 ∨ dstArtOld.toNat ≤ dstArtNew.toNat)
    (hloadSrcArtFinal :
      Solm.EVM.storageLoad
        (Solm.EVM.storageStore
          (Solm.EVM.storageStore
            (Solm.EVM.storageStore
              (Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner (forkSrcInkSlot I)
                srcInkNew)
              evm0.executionEnv.codeOwner (forkSrcArtSlot I) srcArtNew)
            evm0.executionEnv.codeOwner (forkDstInkSlot I) dstInkNew)
          evm0.executionEnv.codeOwner (forkDstArtSlot I) dstArtNew)
        evm0.executionEnv.codeOwner (forkSrcArtSlot I) = srcArtFinal)
    (hloadDstArtFinal :
      Solm.EVM.storageLoad
        (Solm.EVM.storageStore
          (Solm.EVM.storageStore
            (Solm.EVM.storageStore
              (Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner (forkSrcInkSlot I)
                srcInkNew)
              evm0.executionEnv.codeOwner (forkSrcArtSlot I) srcArtNew)
            evm0.executionEnv.codeOwner (forkDstInkSlot I) dstInkNew)
          evm0.executionEnv.codeOwner (forkDstArtSlot I) dstArtNew)
        evm0.executionEnv.codeOwner (forkDstArtSlot I) = dstArtFinal)
    (hloadSrcInkFinal :
      Solm.EVM.storageLoad
        (Solm.EVM.storageStore
          (Solm.EVM.storageStore
            (Solm.EVM.storageStore
              (Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner (forkSrcInkSlot I)
                srcInkNew)
              evm0.executionEnv.codeOwner (forkSrcArtSlot I) srcArtNew)
            evm0.executionEnv.codeOwner (forkDstInkSlot I) dstInkNew)
          evm0.executionEnv.codeOwner (forkDstArtSlot I) dstArtNew)
        evm0.executionEnv.codeOwner (forkSrcInkSlot I) = srcInkFinal)
    (hloadDstInkFinal :
      Solm.EVM.storageLoad
        (Solm.EVM.storageStore
          (Solm.EVM.storageStore
            (Solm.EVM.storageStore
              (Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner (forkSrcInkSlot I)
                srcInkNew)
              evm0.executionEnv.codeOwner (forkSrcArtSlot I) srcArtNew)
            evm0.executionEnv.codeOwner (forkDstInkSlot I) dstInkNew)
          evm0.executionEnv.codeOwner (forkDstArtSlot I) dstArtNew)
        evm0.executionEnv.codeOwner (forkDstInkSlot I) = dstInkFinal)
    (hloadRate :
      Solm.EVM.storageLoad
        (Solm.EVM.storageStore
          (Solm.EVM.storageStore
            (Solm.EVM.storageStore
              (Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner (forkSrcInkSlot I)
                srcInkNew)
              evm0.executionEnv.codeOwner (forkSrcArtSlot I) srcArtNew)
            evm0.executionEnv.codeOwner (forkDstInkSlot I) dstInkNew)
          evm0.executionEnv.codeOwner (forkDstArtSlot I) dstArtNew)
        evm0.executionEnv.codeOwner (forkIlkRateSlot I) = rate)
    (hutabProd : utab = UInt256.mul srcArtFinal rate)
    (hutabFit : srcArtFinal.toNat * rate.toNat < UInt256.size)
    (hutabGuard : rate.toNat = 0 ∨ utab.toNat / rate.toNat = srcArtFinal.toNat)
    (hover : UInt256.size ≤ dstArtFinal.toNat * rate.toNat) :
    ExecTransitionBody config contract evm0 (forkStore I) forkTransition.body .reverted := by
  let evm1 := Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner
    (forkSrcInkSlot I) srcInkNew
  let evm2 := Solm.EVM.storageStore evm1 evm1.executionEnv.codeOwner
    (forkSrcArtSlot I) srcArtNew
  let evm3 := Solm.EVM.storageStore evm2 evm2.executionEnv.codeOwner
    (forkDstInkSlot I) dstInkNew
  let evm4 := Solm.EVM.storageStore evm3 evm3.executionEnv.codeOwner
    (forkDstArtSlot I) dstArtNew
  have hprefix :
      ExecBlock config { contract := contract, locals := forkStore I } evm0 nonpayable
        (.ok { contract := contract, locals := forkStore I } evm0) := by
    change ExecBlock config { contract := contract, locals := forkStore I } evm0
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)) ]
      (.ok { contract := contract, locals := forkStore I } evm0)
    exact ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwei))
      ExecBlock.nil
  have hsrcInkBlock :=
    execForkSrcInkUpdateOk (evm := evm0) (I := I) (locals := forkStore I)
      srcInkOld srcInkNew hsz164 (forkStore_get_ilk I) (forkStore_get_src I)
      (forkStore_get_dink I) (forkStore_urns I) hloadSrcInk hsrcInkNew
      hsrcInkGuardNeg hsrcInkGuardPos
  have hsrcArtBlock :=
    execForkSrcArtUpdateOk (evm := evm1) (I := I)
      (locals := forkStoreSrcInkNew I srcInkNew) srcArtOld srcArtNew hsz164
      (forkStoreSrcInkNew_get_ilk I srcInkNew)
      (forkStoreSrcInkNew_get_src I srcInkNew)
      (forkStoreSrcInkNew_get_dart I srcInkNew)
      (forkStoreSrcInkNew_get_urns I srcInkNew)
      (by simpa [evm1, storageStore_executionEnv] using hloadSrcArt) hsrcArtNew
      hsrcArtGuardNeg hsrcArtGuardPos
  have hdstInkBlock :=
    execForkDstInkUpdateOk (evm := evm2) (I := I)
      (locals := forkStoreSrcArtNew I srcInkNew srcArtNew) dstInkOld dstInkNew hsz164
      (forkStoreSrcArtNew_get_ilk I srcInkNew srcArtNew)
      (forkStoreSrcArtNew_get_dst I srcInkNew srcArtNew)
      (forkStoreSrcArtNew_get_dink I srcInkNew srcArtNew)
      (forkStoreSrcArtNew_get_urns I srcInkNew srcArtNew)
      (by simpa [evm1, evm2, storageStore_executionEnv] using hloadDstInk) hdstInkNew
      hdstInkGuardNeg hdstInkGuardPos
  have hdstArtBlock :=
    execForkDstArtUpdateOk (evm := evm3) (I := I)
      (locals := forkStoreDstInkNew I srcInkNew srcArtNew dstInkNew) dstArtOld dstArtNew
      hsz164 (forkStoreDstInkNew_get_ilk I srcInkNew srcArtNew dstInkNew)
      (forkStoreDstInkNew_get_dst I srcInkNew srcArtNew dstInkNew)
      (forkStoreDstInkNew_get_dart I srcInkNew srcArtNew dstInkNew)
      (forkStoreDstInkNew_get_urns I srcInkNew srcArtNew dstInkNew)
      (by simpa [evm1, evm2, evm3, storageStore_executionEnv] using hloadDstArt)
      hdstArtNew hdstArtGuardNeg hdstArtGuardPos
  have hfinalLoadsBlock :=
    execForkFinalLoadsOk (evm := evm4) (I := I)
      srcInkNew srcArtNew dstInkNew dstArtNew srcArtFinal dstArtFinal
      srcInkFinal dstInkFinal hsz164
      (by
        simpa [evm1, evm2, evm3, evm4, storageStore_executionEnv] using
          hloadSrcArtFinal)
      (by
        simpa [evm1, evm2, evm3, evm4, storageStore_executionEnv] using
          hloadDstArtFinal)
      (by
        simpa [evm1, evm2, evm3, evm4, storageStore_executionEnv] using
          hloadSrcInkFinal)
      (by
        simpa [evm1, evm2, evm3, evm4, storageStore_executionEnv] using
          hloadDstInkFinal)
  have hloadRateFinal :
      Solm.EVM.storageLoad evm4 evm4.executionEnv.codeOwner (forkIlkRateSlot I) = rate := by
    simpa [evm1, evm2, evm3, evm4, storageStore_executionEnv] using hloadRate
  have hutabBlock :=
    execForkUtabFinalMulOk (evm := evm4) (I := I)
      srcInkNew srcArtNew dstInkNew dstArtNew srcArtFinal dstArtFinal
      srcInkFinal dstInkFinal rate utab hsz164 hloadRateFinal
      hutabProd hutabFit hutabGuard
  let localsUtab :=
    forkStoreUtabFinal I srcInkNew srcArtNew dstInkNew dstArtNew srcArtFinal
      dstArtFinal srcInkFinal dstInkFinal utab
  have hdstArtEval :
      evalExpr? config { contract := contract, locals := localsUtab } evm4
        (.var "dstArtFinal") = .ok (.int (Int.ofNat dstArtFinal.toNat)) := by
    exact vatEvalExpr_varUInt256 (by
      change (forkStoreUtabFinal I srcInkNew srcArtNew dstInkNew dstArtNew
        srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab).get? "dstArtFinal" =
        some (.int (Int.ofNat dstArtFinal.toNat))
      exact forkStoreUtabFinal_get_dstArtFinal I srcInkNew srcArtNew dstInkNew dstArtNew
        srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab)
  have hrateEval :
      evalExpr? config { contract := contract, locals := localsUtab } evm4
        (.storage (ilksF (.var "ilk") "rate")) =
        .ok (.int (Int.ofNat rate.toNat)) := by
    rw [evalExpr_fork_ilk_rate_locals localsUtab hsz164
      (by
        change (forkStoreUtabFinal I srcInkNew srcArtNew dstInkNew dstArtNew
          srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab).get? "ilk" =
          some (forkIlkValue I)
        exact forkStoreUtabFinal_get_ilk I srcInkNew srcArtNew dstInkNew dstArtNew
          srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab)
      (by
        change (forkStoreUtabFinal I srcInkNew srcArtNew dstInkNew dstArtNew
          srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab).get? "ilks" = none
        exact forkStoreUtabFinal_get_ilks I srcInkNew srcArtNew dstInkNew dstArtNew
          srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab)]
    simpa [hloadRateFinal]
  have hvtabRevert :
      ExecBlock config { contract := contract, locals := localsUtab } evm4
        (checkedMulUintInto "vtab" (.var "dstArtFinal")
          (.storage (ilksF (.var "ilk") "rate"))) .reverted :=
    execForkMulUintIntoRevertOfOverflow (evm := evm4) (locals := localsUtab)
      "vtab" (.var "dstArtFinal") (.storage (ilksF (.var "ilk") "rate"))
      dstArtFinal rate hdstArtEval hrateEval hover
  have h01 := execBlock_append hprefix hsrcInkBlock
  have h02 := execBlock_append h01 hsrcArtBlock
  have h03 := execBlock_append h02 hdstInkBlock
  have h04 := execBlock_append h03 hdstArtBlock
  have h05 := execBlock_append h04 hfinalLoadsBlock
  have h06 := execBlock_append h05 hutabBlock
  have h07 := execBlock_append h06 hvtabRevert
  have hblock := execBlock_append_term
    (s2 :=
      checkedMulUintInto "srcInkSpot" (.var "srcInkFinal")
        (.storage (ilksF (.var "ilk") "spot")) ++
      checkedMulUintInto "dstInkSpot" (.var "dstInkFinal")
        (.storage (ilksF (.var "ilk") "spot")) ++
      [ .require (bothExpr (wishExpr (.var "src") sender) (wishExpr (.var "dst") sender)),
        .require (.binary .le (.var "utab") (.var "srcInkSpot")),
        .require (.binary .le (.var "vtab") (.var "dstInkSpot")),
        .require
          (eitherExpr
            (.binary .ge (.var "utab") (.storage (ilksF (.var "ilk") "dust")))
            (.binary .eq (.var "srcArtFinal") (.intLit 0))),
        .require
          (eitherExpr
            (.binary .ge (.var "vtab") (.storage (ilksF (.var "ilk") "dust")))
            (.binary .eq (.var "dstArtFinal") (.intLit 0))) ])
    h07 (by intro f e h; cases h)
  simpa [ExecTransitionBody, forkTransition, nonpayable, checkedSubSignedInto,
    checkedAddSignedInto, checkedMulUintInto, List.append_assoc, storageStore_executionEnv]
    using ExecFuncBody.execBlockRevert hblock

set_option maxHeartbeats 1000000 in
theorem execForkSourceRevertSrcInkSpotMul {evm0 : EVM.State} {I : ExecutionEnv}
    (srcInkOld srcInkNew srcArtOld srcArtNew dstInkOld dstInkNew dstArtOld dstArtNew
      srcArtFinal dstArtFinal srcInkFinal dstInkFinal rate spot utab vtab : UInt256)
    (hwei : evm0.executionEnv.weiValue = ⟨0⟩)
    (hsz164 : 164 ≤ I.calldata.size)
    (hloadSrcInk :
      Solm.EVM.storageLoad evm0 evm0.executionEnv.codeOwner (forkSrcInkSlot I) = srcInkOld)
    (hsrcInkNew : srcInkNew = srcInkOld.sub (forkDinkWord I))
    (hsrcInkGuardNeg : forkDinkInt I ≤ 0 ∨ srcInkNew.toNat ≤ srcInkOld.toNat)
    (hsrcInkGuardPos : 0 ≤ forkDinkInt I ∨ srcInkOld.toNat ≤ srcInkNew.toNat)
    (hloadSrcArt :
      Solm.EVM.storageLoad
        (Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner (forkSrcInkSlot I)
          srcInkNew)
        evm0.executionEnv.codeOwner (forkSrcArtSlot I) = srcArtOld)
    (hsrcArtNew : srcArtNew = srcArtOld.sub (forkDartWord I))
    (hsrcArtGuardNeg : forkDartInt I ≤ 0 ∨ srcArtNew.toNat ≤ srcArtOld.toNat)
    (hsrcArtGuardPos : 0 ≤ forkDartInt I ∨ srcArtOld.toNat ≤ srcArtNew.toNat)
    (hloadDstInk :
      Solm.EVM.storageLoad
        (Solm.EVM.storageStore
          (Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner (forkSrcInkSlot I)
            srcInkNew)
          evm0.executionEnv.codeOwner (forkSrcArtSlot I) srcArtNew)
        evm0.executionEnv.codeOwner (forkDstInkSlot I) = dstInkOld)
    (hdstInkNew : dstInkNew = forkDinkWord I + dstInkOld)
    (hdstInkGuardNeg : 0 ≤ forkDinkInt I ∨ dstInkNew.toNat ≤ dstInkOld.toNat)
    (hdstInkGuardPos : forkDinkInt I ≤ 0 ∨ dstInkOld.toNat ≤ dstInkNew.toNat)
    (hloadDstArt :
      Solm.EVM.storageLoad
        (Solm.EVM.storageStore
          (Solm.EVM.storageStore
            (Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner (forkSrcInkSlot I)
              srcInkNew)
            evm0.executionEnv.codeOwner (forkSrcArtSlot I) srcArtNew)
          evm0.executionEnv.codeOwner (forkDstInkSlot I) dstInkNew)
        evm0.executionEnv.codeOwner (forkDstArtSlot I) = dstArtOld)
    (hdstArtNew : dstArtNew = forkDartWord I + dstArtOld)
    (hdstArtGuardNeg : 0 ≤ forkDartInt I ∨ dstArtNew.toNat ≤ dstArtOld.toNat)
    (hdstArtGuardPos : forkDartInt I ≤ 0 ∨ dstArtOld.toNat ≤ dstArtNew.toNat)
    (hloadSrcArtFinal :
      Solm.EVM.storageLoad
        (Solm.EVM.storageStore
          (Solm.EVM.storageStore
            (Solm.EVM.storageStore
              (Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner (forkSrcInkSlot I)
                srcInkNew)
              evm0.executionEnv.codeOwner (forkSrcArtSlot I) srcArtNew)
            evm0.executionEnv.codeOwner (forkDstInkSlot I) dstInkNew)
          evm0.executionEnv.codeOwner (forkDstArtSlot I) dstArtNew)
        evm0.executionEnv.codeOwner (forkSrcArtSlot I) = srcArtFinal)
    (hloadDstArtFinal :
      Solm.EVM.storageLoad
        (Solm.EVM.storageStore
          (Solm.EVM.storageStore
            (Solm.EVM.storageStore
              (Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner (forkSrcInkSlot I)
                srcInkNew)
              evm0.executionEnv.codeOwner (forkSrcArtSlot I) srcArtNew)
            evm0.executionEnv.codeOwner (forkDstInkSlot I) dstInkNew)
          evm0.executionEnv.codeOwner (forkDstArtSlot I) dstArtNew)
        evm0.executionEnv.codeOwner (forkDstArtSlot I) = dstArtFinal)
    (hloadSrcInkFinal :
      Solm.EVM.storageLoad
        (Solm.EVM.storageStore
          (Solm.EVM.storageStore
            (Solm.EVM.storageStore
              (Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner (forkSrcInkSlot I)
                srcInkNew)
              evm0.executionEnv.codeOwner (forkSrcArtSlot I) srcArtNew)
            evm0.executionEnv.codeOwner (forkDstInkSlot I) dstInkNew)
          evm0.executionEnv.codeOwner (forkDstArtSlot I) dstArtNew)
        evm0.executionEnv.codeOwner (forkSrcInkSlot I) = srcInkFinal)
    (hloadDstInkFinal :
      Solm.EVM.storageLoad
        (Solm.EVM.storageStore
          (Solm.EVM.storageStore
            (Solm.EVM.storageStore
              (Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner (forkSrcInkSlot I)
                srcInkNew)
              evm0.executionEnv.codeOwner (forkSrcArtSlot I) srcArtNew)
            evm0.executionEnv.codeOwner (forkDstInkSlot I) dstInkNew)
          evm0.executionEnv.codeOwner (forkDstArtSlot I) dstArtNew)
        evm0.executionEnv.codeOwner (forkDstInkSlot I) = dstInkFinal)
    (hloadRate :
      Solm.EVM.storageLoad
        (Solm.EVM.storageStore
          (Solm.EVM.storageStore
            (Solm.EVM.storageStore
              (Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner (forkSrcInkSlot I)
                srcInkNew)
              evm0.executionEnv.codeOwner (forkSrcArtSlot I) srcArtNew)
            evm0.executionEnv.codeOwner (forkDstInkSlot I) dstInkNew)
          evm0.executionEnv.codeOwner (forkDstArtSlot I) dstArtNew)
        evm0.executionEnv.codeOwner (forkIlkRateSlot I) = rate)
    (hloadSpot :
      Solm.EVM.storageLoad
        (Solm.EVM.storageStore
          (Solm.EVM.storageStore
            (Solm.EVM.storageStore
              (Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner (forkSrcInkSlot I)
                srcInkNew)
              evm0.executionEnv.codeOwner (forkSrcArtSlot I) srcArtNew)
            evm0.executionEnv.codeOwner (forkDstInkSlot I) dstInkNew)
          evm0.executionEnv.codeOwner (forkDstArtSlot I) dstArtNew)
        evm0.executionEnv.codeOwner (forkIlkSpotSlot I) = spot)
    (hutabProd : utab = UInt256.mul srcArtFinal rate)
    (hutabFit : srcArtFinal.toNat * rate.toNat < UInt256.size)
    (hutabGuard : rate.toNat = 0 ∨ utab.toNat / rate.toNat = srcArtFinal.toNat)
    (hvtabProd : vtab = UInt256.mul dstArtFinal rate)
    (hvtabFit : dstArtFinal.toNat * rate.toNat < UInt256.size)
    (hvtabGuard : rate.toNat = 0 ∨ vtab.toNat / rate.toNat = dstArtFinal.toNat)
    (hover : UInt256.size ≤ srcInkFinal.toNat * spot.toNat) :
    ExecTransitionBody config contract evm0 (forkStore I) forkTransition.body .reverted := by
  let evm1 := Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner
    (forkSrcInkSlot I) srcInkNew
  let evm2 := Solm.EVM.storageStore evm1 evm1.executionEnv.codeOwner
    (forkSrcArtSlot I) srcArtNew
  let evm3 := Solm.EVM.storageStore evm2 evm2.executionEnv.codeOwner
    (forkDstInkSlot I) dstInkNew
  let evm4 := Solm.EVM.storageStore evm3 evm3.executionEnv.codeOwner
    (forkDstArtSlot I) dstArtNew
  have hprefix :
      ExecBlock config { contract := contract, locals := forkStore I } evm0 nonpayable
        (.ok { contract := contract, locals := forkStore I } evm0) := by
    change ExecBlock config { contract := contract, locals := forkStore I } evm0
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)) ]
      (.ok { contract := contract, locals := forkStore I } evm0)
    exact ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwei))
      ExecBlock.nil
  have hsrcInkBlock :=
    execForkSrcInkUpdateOk (evm := evm0) (I := I) (locals := forkStore I)
      srcInkOld srcInkNew hsz164 (forkStore_get_ilk I) (forkStore_get_src I)
      (forkStore_get_dink I) (forkStore_urns I) hloadSrcInk hsrcInkNew
      hsrcInkGuardNeg hsrcInkGuardPos
  have hsrcArtBlock :=
    execForkSrcArtUpdateOk (evm := evm1) (I := I)
      (locals := forkStoreSrcInkNew I srcInkNew) srcArtOld srcArtNew hsz164
      (forkStoreSrcInkNew_get_ilk I srcInkNew)
      (forkStoreSrcInkNew_get_src I srcInkNew)
      (forkStoreSrcInkNew_get_dart I srcInkNew)
      (forkStoreSrcInkNew_get_urns I srcInkNew)
      (by simpa [evm1, storageStore_executionEnv] using hloadSrcArt) hsrcArtNew
      hsrcArtGuardNeg hsrcArtGuardPos
  have hdstInkBlock :=
    execForkDstInkUpdateOk (evm := evm2) (I := I)
      (locals := forkStoreSrcArtNew I srcInkNew srcArtNew) dstInkOld dstInkNew hsz164
      (forkStoreSrcArtNew_get_ilk I srcInkNew srcArtNew)
      (forkStoreSrcArtNew_get_dst I srcInkNew srcArtNew)
      (forkStoreSrcArtNew_get_dink I srcInkNew srcArtNew)
      (forkStoreSrcArtNew_get_urns I srcInkNew srcArtNew)
      (by simpa [evm1, evm2, storageStore_executionEnv] using hloadDstInk) hdstInkNew
      hdstInkGuardNeg hdstInkGuardPos
  have hdstArtBlock :=
    execForkDstArtUpdateOk (evm := evm3) (I := I)
      (locals := forkStoreDstInkNew I srcInkNew srcArtNew dstInkNew) dstArtOld dstArtNew
      hsz164 (forkStoreDstInkNew_get_ilk I srcInkNew srcArtNew dstInkNew)
      (forkStoreDstInkNew_get_dst I srcInkNew srcArtNew dstInkNew)
      (forkStoreDstInkNew_get_dart I srcInkNew srcArtNew dstInkNew)
      (forkStoreDstInkNew_get_urns I srcInkNew srcArtNew dstInkNew)
      (by simpa [evm1, evm2, evm3, storageStore_executionEnv] using hloadDstArt)
      hdstArtNew hdstArtGuardNeg hdstArtGuardPos
  have hfinalLoadsBlock :=
    execForkFinalLoadsOk (evm := evm4) (I := I)
      srcInkNew srcArtNew dstInkNew dstArtNew srcArtFinal dstArtFinal
      srcInkFinal dstInkFinal hsz164
      (by
        simpa [evm1, evm2, evm3, evm4, storageStore_executionEnv] using
          hloadSrcArtFinal)
      (by
        simpa [evm1, evm2, evm3, evm4, storageStore_executionEnv] using
          hloadDstArtFinal)
      (by
        simpa [evm1, evm2, evm3, evm4, storageStore_executionEnv] using
          hloadSrcInkFinal)
      (by
        simpa [evm1, evm2, evm3, evm4, storageStore_executionEnv] using
          hloadDstInkFinal)
  have hloadRateFinal :
      Solm.EVM.storageLoad evm4 evm4.executionEnv.codeOwner (forkIlkRateSlot I) = rate := by
    simpa [evm1, evm2, evm3, evm4, storageStore_executionEnv] using hloadRate
  have hloadSpotFinal :
      Solm.EVM.storageLoad evm4 evm4.executionEnv.codeOwner (forkIlkSpotSlot I) = spot := by
    simpa [evm1, evm2, evm3, evm4, storageStore_executionEnv] using hloadSpot
  have hutabBlock :=
    execForkUtabFinalMulOk (evm := evm4) (I := I)
      srcInkNew srcArtNew dstInkNew dstArtNew srcArtFinal dstArtFinal
      srcInkFinal dstInkFinal rate utab hsz164 hloadRateFinal
      hutabProd hutabFit hutabGuard
  have hvtabBlock :=
    execForkVtabFinalMulOk (evm := evm4) (I := I)
      srcInkNew srcArtNew dstInkNew dstArtNew srcArtFinal dstArtFinal
      srcInkFinal dstInkFinal rate utab vtab hsz164 hloadRateFinal
      hvtabProd hvtabFit hvtabGuard
  let localsVtab :=
    forkStoreVtabFinal I srcInkNew srcArtNew dstInkNew dstArtNew srcArtFinal
      dstArtFinal srcInkFinal dstInkFinal utab vtab
  have hsrcInkEval :
      evalExpr? config { contract := contract, locals := localsVtab } evm4
        (.var "srcInkFinal") = .ok (.int (Int.ofNat srcInkFinal.toNat)) := by
    exact vatEvalExpr_varUInt256 (by
      change (forkStoreVtabFinal I srcInkNew srcArtNew dstInkNew dstArtNew
        srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab vtab).get? "srcInkFinal" =
        some (.int (Int.ofNat srcInkFinal.toNat))
      exact forkStoreVtabFinal_get_srcInkFinal I srcInkNew srcArtNew dstInkNew dstArtNew
        srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab vtab)
  have hspotEval :
      evalExpr? config { contract := contract, locals := localsVtab } evm4
        (.storage (ilksF (.var "ilk") "spot")) =
        .ok (.int (Int.ofNat spot.toNat)) := by
    rw [evalExpr_fork_ilk_spot_locals localsVtab hsz164
      (by
        change (forkStoreVtabFinal I srcInkNew srcArtNew dstInkNew dstArtNew
          srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab vtab).get? "ilk" =
          some (forkIlkValue I)
        exact forkStoreVtabFinal_get_ilk I srcInkNew srcArtNew dstInkNew dstArtNew
          srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab vtab)
      (by
        change (forkStoreVtabFinal I srcInkNew srcArtNew dstInkNew dstArtNew
          srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab vtab).get? "ilks" = none
        exact forkStoreVtabFinal_get_ilks I srcInkNew srcArtNew dstInkNew dstArtNew
          srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab vtab)]
    simpa [hloadSpotFinal]
  have hsrcInkSpotRevert :
      ExecBlock config { contract := contract, locals := localsVtab } evm4
        (checkedMulUintInto "srcInkSpot" (.var "srcInkFinal")
          (.storage (ilksF (.var "ilk") "spot"))) .reverted :=
    execForkMulUintIntoRevertOfOverflow (evm := evm4) (locals := localsVtab)
      "srcInkSpot" (.var "srcInkFinal") (.storage (ilksF (.var "ilk") "spot"))
      srcInkFinal spot hsrcInkEval hspotEval hover
  have h01 := execBlock_append hprefix hsrcInkBlock
  have h02 := execBlock_append h01 hsrcArtBlock
  have h03 := execBlock_append h02 hdstInkBlock
  have h04 := execBlock_append h03 hdstArtBlock
  have h05 := execBlock_append h04 hfinalLoadsBlock
  have h06 := execBlock_append h05 hutabBlock
  have h07 := execBlock_append h06 hvtabBlock
  have h08 := execBlock_append h07 hsrcInkSpotRevert
  have hblock := execBlock_append_term
    (s2 :=
      checkedMulUintInto "dstInkSpot" (.var "dstInkFinal")
        (.storage (ilksF (.var "ilk") "spot")) ++
      [ .require (bothExpr (wishExpr (.var "src") sender) (wishExpr (.var "dst") sender)),
        .require (.binary .le (.var "utab") (.var "srcInkSpot")),
        .require (.binary .le (.var "vtab") (.var "dstInkSpot")),
        .require
          (eitherExpr
            (.binary .ge (.var "utab") (.storage (ilksF (.var "ilk") "dust")))
            (.binary .eq (.var "srcArtFinal") (.intLit 0))),
        .require
          (eitherExpr
            (.binary .ge (.var "vtab") (.storage (ilksF (.var "ilk") "dust")))
            (.binary .eq (.var "dstArtFinal") (.intLit 0))) ])
    h08 (by intro f e h; cases h)
  simpa [ExecTransitionBody, forkTransition, nonpayable, checkedSubSignedInto,
    checkedAddSignedInto, checkedMulUintInto, List.append_assoc, storageStore_executionEnv]
    using ExecFuncBody.execBlockRevert hblock

set_option maxHeartbeats 1000000 in
theorem execForkSourceRevertDstInkSpotMul {evm0 : EVM.State} {I : ExecutionEnv}
    (srcInkOld srcInkNew srcArtOld srcArtNew dstInkOld dstInkNew dstArtOld dstArtNew
      srcArtFinal dstArtFinal srcInkFinal dstInkFinal rate spot utab vtab
      srcInkSpot : UInt256)
    (hwei : evm0.executionEnv.weiValue = ⟨0⟩)
    (hsz164 : 164 ≤ I.calldata.size)
    (hloadSrcInk :
      Solm.EVM.storageLoad evm0 evm0.executionEnv.codeOwner (forkSrcInkSlot I) = srcInkOld)
    (hsrcInkNew : srcInkNew = srcInkOld.sub (forkDinkWord I))
    (hsrcInkGuardNeg : forkDinkInt I ≤ 0 ∨ srcInkNew.toNat ≤ srcInkOld.toNat)
    (hsrcInkGuardPos : 0 ≤ forkDinkInt I ∨ srcInkOld.toNat ≤ srcInkNew.toNat)
    (hloadSrcArt :
      Solm.EVM.storageLoad
        (Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner (forkSrcInkSlot I)
          srcInkNew)
        evm0.executionEnv.codeOwner (forkSrcArtSlot I) = srcArtOld)
    (hsrcArtNew : srcArtNew = srcArtOld.sub (forkDartWord I))
    (hsrcArtGuardNeg : forkDartInt I ≤ 0 ∨ srcArtNew.toNat ≤ srcArtOld.toNat)
    (hsrcArtGuardPos : 0 ≤ forkDartInt I ∨ srcArtOld.toNat ≤ srcArtNew.toNat)
    (hloadDstInk :
      Solm.EVM.storageLoad
        (Solm.EVM.storageStore
          (Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner (forkSrcInkSlot I)
            srcInkNew)
          evm0.executionEnv.codeOwner (forkSrcArtSlot I) srcArtNew)
        evm0.executionEnv.codeOwner (forkDstInkSlot I) = dstInkOld)
    (hdstInkNew : dstInkNew = forkDinkWord I + dstInkOld)
    (hdstInkGuardNeg : 0 ≤ forkDinkInt I ∨ dstInkNew.toNat ≤ dstInkOld.toNat)
    (hdstInkGuardPos : forkDinkInt I ≤ 0 ∨ dstInkOld.toNat ≤ dstInkNew.toNat)
    (hloadDstArt :
      Solm.EVM.storageLoad
        (Solm.EVM.storageStore
          (Solm.EVM.storageStore
            (Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner (forkSrcInkSlot I)
              srcInkNew)
            evm0.executionEnv.codeOwner (forkSrcArtSlot I) srcArtNew)
          evm0.executionEnv.codeOwner (forkDstInkSlot I) dstInkNew)
        evm0.executionEnv.codeOwner (forkDstArtSlot I) = dstArtOld)
    (hdstArtNew : dstArtNew = forkDartWord I + dstArtOld)
    (hdstArtGuardNeg : 0 ≤ forkDartInt I ∨ dstArtNew.toNat ≤ dstArtOld.toNat)
    (hdstArtGuardPos : forkDartInt I ≤ 0 ∨ dstArtOld.toNat ≤ dstArtNew.toNat)
    (hloadSrcArtFinal :
      Solm.EVM.storageLoad
        (Solm.EVM.storageStore
          (Solm.EVM.storageStore
            (Solm.EVM.storageStore
              (Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner (forkSrcInkSlot I)
                srcInkNew)
              evm0.executionEnv.codeOwner (forkSrcArtSlot I) srcArtNew)
            evm0.executionEnv.codeOwner (forkDstInkSlot I) dstInkNew)
          evm0.executionEnv.codeOwner (forkDstArtSlot I) dstArtNew)
        evm0.executionEnv.codeOwner (forkSrcArtSlot I) = srcArtFinal)
    (hloadDstArtFinal :
      Solm.EVM.storageLoad
        (Solm.EVM.storageStore
          (Solm.EVM.storageStore
            (Solm.EVM.storageStore
              (Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner (forkSrcInkSlot I)
                srcInkNew)
              evm0.executionEnv.codeOwner (forkSrcArtSlot I) srcArtNew)
            evm0.executionEnv.codeOwner (forkDstInkSlot I) dstInkNew)
          evm0.executionEnv.codeOwner (forkDstArtSlot I) dstArtNew)
        evm0.executionEnv.codeOwner (forkDstArtSlot I) = dstArtFinal)
    (hloadSrcInkFinal :
      Solm.EVM.storageLoad
        (Solm.EVM.storageStore
          (Solm.EVM.storageStore
            (Solm.EVM.storageStore
              (Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner (forkSrcInkSlot I)
                srcInkNew)
              evm0.executionEnv.codeOwner (forkSrcArtSlot I) srcArtNew)
            evm0.executionEnv.codeOwner (forkDstInkSlot I) dstInkNew)
          evm0.executionEnv.codeOwner (forkDstArtSlot I) dstArtNew)
        evm0.executionEnv.codeOwner (forkSrcInkSlot I) = srcInkFinal)
    (hloadDstInkFinal :
      Solm.EVM.storageLoad
        (Solm.EVM.storageStore
          (Solm.EVM.storageStore
            (Solm.EVM.storageStore
              (Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner (forkSrcInkSlot I)
                srcInkNew)
              evm0.executionEnv.codeOwner (forkSrcArtSlot I) srcArtNew)
            evm0.executionEnv.codeOwner (forkDstInkSlot I) dstInkNew)
          evm0.executionEnv.codeOwner (forkDstArtSlot I) dstArtNew)
        evm0.executionEnv.codeOwner (forkDstInkSlot I) = dstInkFinal)
    (hloadRate :
      Solm.EVM.storageLoad
        (Solm.EVM.storageStore
          (Solm.EVM.storageStore
            (Solm.EVM.storageStore
              (Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner (forkSrcInkSlot I)
                srcInkNew)
              evm0.executionEnv.codeOwner (forkSrcArtSlot I) srcArtNew)
            evm0.executionEnv.codeOwner (forkDstInkSlot I) dstInkNew)
          evm0.executionEnv.codeOwner (forkDstArtSlot I) dstArtNew)
        evm0.executionEnv.codeOwner (forkIlkRateSlot I) = rate)
    (hloadSpot :
      Solm.EVM.storageLoad
        (Solm.EVM.storageStore
          (Solm.EVM.storageStore
            (Solm.EVM.storageStore
              (Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner (forkSrcInkSlot I)
                srcInkNew)
              evm0.executionEnv.codeOwner (forkSrcArtSlot I) srcArtNew)
            evm0.executionEnv.codeOwner (forkDstInkSlot I) dstInkNew)
          evm0.executionEnv.codeOwner (forkDstArtSlot I) dstArtNew)
        evm0.executionEnv.codeOwner (forkIlkSpotSlot I) = spot)
    (hutabProd : utab = UInt256.mul srcArtFinal rate)
    (hutabFit : srcArtFinal.toNat * rate.toNat < UInt256.size)
    (hutabGuard : rate.toNat = 0 ∨ utab.toNat / rate.toNat = srcArtFinal.toNat)
    (hvtabProd : vtab = UInt256.mul dstArtFinal rate)
    (hvtabFit : dstArtFinal.toNat * rate.toNat < UInt256.size)
    (hvtabGuard : rate.toNat = 0 ∨ vtab.toNat / rate.toNat = dstArtFinal.toNat)
    (hsrcInkSpotProd : srcInkSpot = UInt256.mul srcInkFinal spot)
    (hsrcInkSpotFit : srcInkFinal.toNat * spot.toNat < UInt256.size)
    (hsrcInkSpotGuard : spot.toNat = 0 ∨ srcInkSpot.toNat / spot.toNat = srcInkFinal.toNat)
    (hover : UInt256.size ≤ dstInkFinal.toNat * spot.toNat) :
    ExecTransitionBody config contract evm0 (forkStore I) forkTransition.body .reverted := by
  let evm1 := Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner
    (forkSrcInkSlot I) srcInkNew
  let evm2 := Solm.EVM.storageStore evm1 evm1.executionEnv.codeOwner
    (forkSrcArtSlot I) srcArtNew
  let evm3 := Solm.EVM.storageStore evm2 evm2.executionEnv.codeOwner
    (forkDstInkSlot I) dstInkNew
  let evm4 := Solm.EVM.storageStore evm3 evm3.executionEnv.codeOwner
    (forkDstArtSlot I) dstArtNew
  have hprefix :
      ExecBlock config { contract := contract, locals := forkStore I } evm0 nonpayable
        (.ok { contract := contract, locals := forkStore I } evm0) := by
    change ExecBlock config { contract := contract, locals := forkStore I } evm0
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)) ]
      (.ok { contract := contract, locals := forkStore I } evm0)
    exact ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwei))
      ExecBlock.nil
  have hsrcInkBlock :=
    execForkSrcInkUpdateOk (evm := evm0) (I := I) (locals := forkStore I)
      srcInkOld srcInkNew hsz164 (forkStore_get_ilk I) (forkStore_get_src I)
      (forkStore_get_dink I) (forkStore_urns I) hloadSrcInk hsrcInkNew
      hsrcInkGuardNeg hsrcInkGuardPos
  have hsrcArtBlock :=
    execForkSrcArtUpdateOk (evm := evm1) (I := I)
      (locals := forkStoreSrcInkNew I srcInkNew) srcArtOld srcArtNew hsz164
      (forkStoreSrcInkNew_get_ilk I srcInkNew)
      (forkStoreSrcInkNew_get_src I srcInkNew)
      (forkStoreSrcInkNew_get_dart I srcInkNew)
      (forkStoreSrcInkNew_get_urns I srcInkNew)
      (by simpa [evm1, storageStore_executionEnv] using hloadSrcArt) hsrcArtNew
      hsrcArtGuardNeg hsrcArtGuardPos
  have hdstInkBlock :=
    execForkDstInkUpdateOk (evm := evm2) (I := I)
      (locals := forkStoreSrcArtNew I srcInkNew srcArtNew) dstInkOld dstInkNew hsz164
      (forkStoreSrcArtNew_get_ilk I srcInkNew srcArtNew)
      (forkStoreSrcArtNew_get_dst I srcInkNew srcArtNew)
      (forkStoreSrcArtNew_get_dink I srcInkNew srcArtNew)
      (forkStoreSrcArtNew_get_urns I srcInkNew srcArtNew)
      (by simpa [evm1, evm2, storageStore_executionEnv] using hloadDstInk) hdstInkNew
      hdstInkGuardNeg hdstInkGuardPos
  have hdstArtBlock :=
    execForkDstArtUpdateOk (evm := evm3) (I := I)
      (locals := forkStoreDstInkNew I srcInkNew srcArtNew dstInkNew) dstArtOld dstArtNew
      hsz164 (forkStoreDstInkNew_get_ilk I srcInkNew srcArtNew dstInkNew)
      (forkStoreDstInkNew_get_dst I srcInkNew srcArtNew dstInkNew)
      (forkStoreDstInkNew_get_dart I srcInkNew srcArtNew dstInkNew)
      (forkStoreDstInkNew_get_urns I srcInkNew srcArtNew dstInkNew)
      (by simpa [evm1, evm2, evm3, storageStore_executionEnv] using hloadDstArt)
      hdstArtNew hdstArtGuardNeg hdstArtGuardPos
  have hfinalLoadsBlock :=
    execForkFinalLoadsOk (evm := evm4) (I := I)
      srcInkNew srcArtNew dstInkNew dstArtNew srcArtFinal dstArtFinal
      srcInkFinal dstInkFinal hsz164
      (by
        simpa [evm1, evm2, evm3, evm4, storageStore_executionEnv] using
          hloadSrcArtFinal)
      (by
        simpa [evm1, evm2, evm3, evm4, storageStore_executionEnv] using
          hloadDstArtFinal)
      (by
        simpa [evm1, evm2, evm3, evm4, storageStore_executionEnv] using
          hloadSrcInkFinal)
      (by
        simpa [evm1, evm2, evm3, evm4, storageStore_executionEnv] using
          hloadDstInkFinal)
  have hloadRateFinal :
      Solm.EVM.storageLoad evm4 evm4.executionEnv.codeOwner (forkIlkRateSlot I) = rate := by
    simpa [evm1, evm2, evm3, evm4, storageStore_executionEnv] using hloadRate
  have hloadSpotFinal :
      Solm.EVM.storageLoad evm4 evm4.executionEnv.codeOwner (forkIlkSpotSlot I) = spot := by
    simpa [evm1, evm2, evm3, evm4, storageStore_executionEnv] using hloadSpot
  have hutabBlock :=
    execForkUtabFinalMulOk (evm := evm4) (I := I)
      srcInkNew srcArtNew dstInkNew dstArtNew srcArtFinal dstArtFinal
      srcInkFinal dstInkFinal rate utab hsz164 hloadRateFinal
      hutabProd hutabFit hutabGuard
  have hvtabBlock :=
    execForkVtabFinalMulOk (evm := evm4) (I := I)
      srcInkNew srcArtNew dstInkNew dstArtNew srcArtFinal dstArtFinal
      srcInkFinal dstInkFinal rate utab vtab hsz164 hloadRateFinal
      hvtabProd hvtabFit hvtabGuard
  have hsrcInkSpotBlock :=
    execForkSrcInkSpotFinalMulOk (evm := evm4) (I := I)
      srcInkNew srcArtNew dstInkNew dstArtNew srcArtFinal dstArtFinal
      srcInkFinal dstInkFinal spot utab vtab srcInkSpot hsz164 hloadSpotFinal
      hsrcInkSpotProd hsrcInkSpotFit hsrcInkSpotGuard
  let localsSrcInkSpot :=
    forkStoreSrcInkSpotFinal I srcInkNew srcArtNew dstInkNew dstArtNew
      srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab vtab srcInkSpot
  have hdstInkEval :
      evalExpr? config { contract := contract, locals := localsSrcInkSpot } evm4
        (.var "dstInkFinal") = .ok (.int (Int.ofNat dstInkFinal.toNat)) := by
    exact vatEvalExpr_varUInt256 (by
      change (forkStoreSrcInkSpotFinal I srcInkNew srcArtNew dstInkNew dstArtNew
        srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab vtab srcInkSpot).get?
        "dstInkFinal" = some (.int (Int.ofNat dstInkFinal.toNat))
      exact forkStoreSrcInkSpotFinal_get_dstInkFinal I srcInkNew srcArtNew dstInkNew
        dstArtNew srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab vtab srcInkSpot)
  have hspotEval :
      evalExpr? config { contract := contract, locals := localsSrcInkSpot } evm4
        (.storage (ilksF (.var "ilk") "spot")) =
        .ok (.int (Int.ofNat spot.toNat)) := by
    rw [evalExpr_fork_ilk_spot_locals localsSrcInkSpot hsz164
      (by
        change (forkStoreSrcInkSpotFinal I srcInkNew srcArtNew dstInkNew dstArtNew
          srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab vtab srcInkSpot).get?
          "ilk" = some (forkIlkValue I)
        exact forkStoreSrcInkSpotFinal_get_ilk I srcInkNew srcArtNew dstInkNew dstArtNew
          srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab vtab srcInkSpot)
      (by
        change (forkStoreSrcInkSpotFinal I srcInkNew srcArtNew dstInkNew dstArtNew
          srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab vtab srcInkSpot).get?
          "ilks" = none
        exact forkStoreSrcInkSpotFinal_get_ilks I srcInkNew srcArtNew dstInkNew dstArtNew
          srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab vtab srcInkSpot)]
    simpa [hloadSpotFinal]
  have hdstInkSpotRevert :
      ExecBlock config { contract := contract, locals := localsSrcInkSpot } evm4
        (checkedMulUintInto "dstInkSpot" (.var "dstInkFinal")
          (.storage (ilksF (.var "ilk") "spot"))) .reverted :=
    execForkMulUintIntoRevertOfOverflow (evm := evm4) (locals := localsSrcInkSpot)
      "dstInkSpot" (.var "dstInkFinal") (.storage (ilksF (.var "ilk") "spot"))
      dstInkFinal spot hdstInkEval hspotEval hover
  have h01 := execBlock_append hprefix hsrcInkBlock
  have h02 := execBlock_append h01 hsrcArtBlock
  have h03 := execBlock_append h02 hdstInkBlock
  have h04 := execBlock_append h03 hdstArtBlock
  have h05 := execBlock_append h04 hfinalLoadsBlock
  have h06 := execBlock_append h05 hutabBlock
  have h07 := execBlock_append h06 hvtabBlock
  have h08 := execBlock_append h07 hsrcInkSpotBlock
  have h09 := execBlock_append h08 hdstInkSpotRevert
  have hblock := execBlock_append_term
    (s2 :=
      [ .require (bothExpr (wishExpr (.var "src") sender) (wishExpr (.var "dst") sender)),
        .require (.binary .le (.var "utab") (.var "srcInkSpot")),
        .require (.binary .le (.var "vtab") (.var "dstInkSpot")),
        .require
          (eitherExpr
            (.binary .ge (.var "utab") (.storage (ilksF (.var "ilk") "dust")))
            (.binary .eq (.var "srcArtFinal") (.intLit 0))),
        .require
          (eitherExpr
            (.binary .ge (.var "vtab") (.storage (ilksF (.var "ilk") "dust")))
            (.binary .eq (.var "dstArtFinal") (.intLit 0))) ])
    h09 (by intro f e h; cases h)
  simpa [ExecTransitionBody, forkTransition, nonpayable, checkedSubSignedInto,
    checkedAddSignedInto, checkedMulUintInto, List.append_assoc, storageStore_executionEnv]
    using ExecFuncBody.execBlockRevert hblock

set_option maxHeartbeats 1000000 in
theorem execForkSourceRevertFinal {evm0 : EVM.State} {I : ExecutionEnv}
    (srcInkOld srcInkNew srcArtOld srcArtNew dstInkOld dstInkNew dstArtOld dstArtNew
      srcArtFinal dstArtFinal srcInkFinal dstInkFinal rate spot utab vtab
      srcInkSpot dstInkSpot : UInt256)
    (hwei : evm0.executionEnv.weiValue = ⟨0⟩)
    (hsz164 : 164 ≤ I.calldata.size)
    (hloadSrcInk :
      Solm.EVM.storageLoad evm0 evm0.executionEnv.codeOwner (forkSrcInkSlot I) = srcInkOld)
    (hsrcInkNew : srcInkNew = UInt256.sub srcInkOld (forkDinkWord I))
    (hsrcInkGuardNeg : forkDinkInt I ≤ 0 ∨ srcInkNew.toNat ≤ srcInkOld.toNat)
    (hsrcInkGuardPos : 0 ≤ forkDinkInt I ∨ srcInkOld.toNat ≤ srcInkNew.toNat)
    (hloadSrcArt :
      Solm.EVM.storageLoad
        (Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner (forkSrcInkSlot I)
          srcInkNew)
        evm0.executionEnv.codeOwner (forkSrcArtSlot I) = srcArtOld)
    (hsrcArtNew : srcArtNew = UInt256.sub srcArtOld (forkDartWord I))
    (hsrcArtGuardNeg : forkDartInt I ≤ 0 ∨ srcArtNew.toNat ≤ srcArtOld.toNat)
    (hsrcArtGuardPos : 0 ≤ forkDartInt I ∨ srcArtOld.toNat ≤ srcArtNew.toNat)
    (hloadDstInk :
      Solm.EVM.storageLoad
        (Solm.EVM.storageStore
          (Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner (forkSrcInkSlot I)
            srcInkNew)
          evm0.executionEnv.codeOwner (forkSrcArtSlot I) srcArtNew)
        evm0.executionEnv.codeOwner (forkDstInkSlot I) = dstInkOld)
    (hdstInkNew : dstInkNew = forkDinkWord I + dstInkOld)
    (hdstInkGuardNeg : 0 ≤ forkDinkInt I ∨ dstInkNew.toNat ≤ dstInkOld.toNat)
    (hdstInkGuardPos : forkDinkInt I ≤ 0 ∨ dstInkOld.toNat ≤ dstInkNew.toNat)
    (hloadDstArt :
      Solm.EVM.storageLoad
        (Solm.EVM.storageStore
          (Solm.EVM.storageStore
            (Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner (forkSrcInkSlot I)
              srcInkNew)
            evm0.executionEnv.codeOwner (forkSrcArtSlot I) srcArtNew)
          evm0.executionEnv.codeOwner (forkDstInkSlot I) dstInkNew)
        evm0.executionEnv.codeOwner (forkDstArtSlot I) = dstArtOld)
    (hdstArtNew : dstArtNew = forkDartWord I + dstArtOld)
    (hdstArtGuardNeg : 0 ≤ forkDartInt I ∨ dstArtNew.toNat ≤ dstArtOld.toNat)
    (hdstArtGuardPos : forkDartInt I ≤ 0 ∨ dstArtOld.toNat ≤ dstArtNew.toNat)
    (hloadSrcArtFinal :
      Solm.EVM.storageLoad
        (Solm.EVM.storageStore
          (Solm.EVM.storageStore
            (Solm.EVM.storageStore
              (Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner (forkSrcInkSlot I)
                srcInkNew)
              evm0.executionEnv.codeOwner (forkSrcArtSlot I) srcArtNew)
            evm0.executionEnv.codeOwner (forkDstInkSlot I) dstInkNew)
        evm0.executionEnv.codeOwner (forkDstArtSlot I) dstArtNew)
        evm0.executionEnv.codeOwner (forkSrcArtSlot I) = srcArtFinal)
    (hloadDstArtFinal :
      Solm.EVM.storageLoad
        (Solm.EVM.storageStore
          (Solm.EVM.storageStore
            (Solm.EVM.storageStore
              (Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner (forkSrcInkSlot I)
                srcInkNew)
              evm0.executionEnv.codeOwner (forkSrcArtSlot I) srcArtNew)
            evm0.executionEnv.codeOwner (forkDstInkSlot I) dstInkNew)
        evm0.executionEnv.codeOwner (forkDstArtSlot I) dstArtNew)
        evm0.executionEnv.codeOwner (forkDstArtSlot I) = dstArtFinal)
    (hloadSrcInkFinal :
      Solm.EVM.storageLoad
        (Solm.EVM.storageStore
          (Solm.EVM.storageStore
            (Solm.EVM.storageStore
              (Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner (forkSrcInkSlot I)
                srcInkNew)
              evm0.executionEnv.codeOwner (forkSrcArtSlot I) srcArtNew)
            evm0.executionEnv.codeOwner (forkDstInkSlot I) dstInkNew)
        evm0.executionEnv.codeOwner (forkDstArtSlot I) dstArtNew)
        evm0.executionEnv.codeOwner (forkSrcInkSlot I) = srcInkFinal)
    (hloadDstInkFinal :
      Solm.EVM.storageLoad
        (Solm.EVM.storageStore
          (Solm.EVM.storageStore
            (Solm.EVM.storageStore
              (Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner (forkSrcInkSlot I)
                srcInkNew)
              evm0.executionEnv.codeOwner (forkSrcArtSlot I) srcArtNew)
            evm0.executionEnv.codeOwner (forkDstInkSlot I) dstInkNew)
        evm0.executionEnv.codeOwner (forkDstArtSlot I) dstArtNew)
        evm0.executionEnv.codeOwner (forkDstInkSlot I) = dstInkFinal)
    (hloadRate :
      Solm.EVM.storageLoad
        (Solm.EVM.storageStore
          (Solm.EVM.storageStore
            (Solm.EVM.storageStore
              (Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner (forkSrcInkSlot I)
                srcInkNew)
              evm0.executionEnv.codeOwner (forkSrcArtSlot I) srcArtNew)
            evm0.executionEnv.codeOwner (forkDstInkSlot I) dstInkNew)
          evm0.executionEnv.codeOwner (forkDstArtSlot I) dstArtNew)
        evm0.executionEnv.codeOwner (forkIlkRateSlot I) = rate)
    (hloadSpot :
      Solm.EVM.storageLoad
        (Solm.EVM.storageStore
          (Solm.EVM.storageStore
            (Solm.EVM.storageStore
              (Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner (forkSrcInkSlot I)
                srcInkNew)
              evm0.executionEnv.codeOwner (forkSrcArtSlot I) srcArtNew)
            evm0.executionEnv.codeOwner (forkDstInkSlot I) dstInkNew)
          evm0.executionEnv.codeOwner (forkDstArtSlot I) dstArtNew)
        evm0.executionEnv.codeOwner (forkIlkSpotSlot I) = spot)
    (hutabProd : utab = UInt256.mul srcArtFinal rate)
    (hutabFit : srcArtFinal.toNat * rate.toNat < UInt256.size)
    (hutabGuard : rate.toNat = 0 ∨ utab.toNat / rate.toNat = srcArtFinal.toNat)
    (hvtabProd : vtab = UInt256.mul dstArtFinal rate)
    (hvtabFit : dstArtFinal.toNat * rate.toNat < UInt256.size)
    (hvtabGuard : rate.toNat = 0 ∨ vtab.toNat / rate.toNat = dstArtFinal.toNat)
    (hsrcInkSpotProd : srcInkSpot = UInt256.mul srcInkFinal spot)
    (hsrcInkSpotFit : srcInkFinal.toNat * spot.toNat < UInt256.size)
    (hsrcInkSpotGuard : spot.toNat = 0 ∨ srcInkSpot.toNat / spot.toNat = srcInkFinal.toNat)
    (hdstInkSpotProd : dstInkSpot = UInt256.mul dstInkFinal spot)
    (hdstInkSpotFit : dstInkFinal.toNat * spot.toNat < UInt256.size)
    (hdstInkSpotGuard : spot.toNat = 0 ∨ dstInkSpot.toNat / spot.toNat = dstInkFinal.toNat) :
    let evm1 := Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner
      (forkSrcInkSlot I) srcInkNew
    let evm2 := Solm.EVM.storageStore evm1 evm1.executionEnv.codeOwner
      (forkSrcArtSlot I) srcArtNew
    let evm3 := Solm.EVM.storageStore evm2 evm2.executionEnv.codeOwner
      (forkDstInkSlot I) dstInkNew
    let evm4 := Solm.EVM.storageStore evm3 evm3.executionEnv.codeOwner
      (forkDstArtSlot I) dstArtNew
    let finalLocals :=
      forkStoreDstInkSpotFinal I srcInkNew srcArtNew dstInkNew dstArtNew
        srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab vtab srcInkSpot dstInkSpot
    ExecBlock config { contract := contract, locals := finalLocals } evm4
      [ .require (bothExpr (wishExpr (.var "src") sender) (wishExpr (.var "dst") sender)),
        .require (.binary .le (.var "utab") (.var "srcInkSpot")),
        .require (.binary .le (.var "vtab") (.var "dstInkSpot")),
        .require
          (eitherExpr
            (.binary .ge (.var "utab") (.storage (ilksF (.var "ilk") "dust")))
            (.binary .eq (.var "srcArtFinal") (.intLit 0))),
        .require
          (eitherExpr
            (.binary .ge (.var "vtab") (.storage (ilksF (.var "ilk") "dust")))
            (.binary .eq (.var "dstArtFinal") (.intLit 0))) ]
      .reverted →
    ExecTransitionBody config contract evm0 (forkStore I) forkTransition.body .reverted := by
  intro evm1 evm2 evm3 evm4 finalLocals hfinalBlock
  have hprefix :
      ExecBlock config { contract := contract, locals := forkStore I } evm0 nonpayable
        (.ok { contract := contract, locals := forkStore I } evm0) := by
    change ExecBlock config { contract := contract, locals := forkStore I } evm0
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)) ]
      (.ok { contract := contract, locals := forkStore I } evm0)
    exact ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwei))
      ExecBlock.nil
  have hsrcInkBlock :=
    execForkSrcInkUpdateOk (evm := evm0) (I := I) (locals := forkStore I)
      srcInkOld srcInkNew hsz164 (forkStore_get_ilk I) (forkStore_get_src I)
      (forkStore_get_dink I) (forkStore_urns I) hloadSrcInk hsrcInkNew
      hsrcInkGuardNeg hsrcInkGuardPos
  have hsrcArtBlock :=
    execForkSrcArtUpdateOk (evm := evm1) (I := I)
      (locals := forkStoreSrcInkNew I srcInkNew) srcArtOld srcArtNew hsz164
      (forkStoreSrcInkNew_get_ilk I srcInkNew)
      (forkStoreSrcInkNew_get_src I srcInkNew)
      (forkStoreSrcInkNew_get_dart I srcInkNew)
      (forkStoreSrcInkNew_get_urns I srcInkNew)
      (by simpa [evm1, storageStore_executionEnv] using hloadSrcArt) hsrcArtNew
      hsrcArtGuardNeg hsrcArtGuardPos
  have hdstInkBlock :=
    execForkDstInkUpdateOk (evm := evm2) (I := I)
      (locals := forkStoreSrcArtNew I srcInkNew srcArtNew) dstInkOld dstInkNew hsz164
      (forkStoreSrcArtNew_get_ilk I srcInkNew srcArtNew)
      (forkStoreSrcArtNew_get_dst I srcInkNew srcArtNew)
      (forkStoreSrcArtNew_get_dink I srcInkNew srcArtNew)
      (forkStoreSrcArtNew_get_urns I srcInkNew srcArtNew)
      (by simpa [evm1, evm2, storageStore_executionEnv] using hloadDstInk) hdstInkNew
      hdstInkGuardNeg hdstInkGuardPos
  have hdstArtBlock :=
    execForkDstArtUpdateOk (evm := evm3) (I := I)
      (locals := forkStoreDstInkNew I srcInkNew srcArtNew dstInkNew) dstArtOld dstArtNew
      hsz164 (forkStoreDstInkNew_get_ilk I srcInkNew srcArtNew dstInkNew)
      (forkStoreDstInkNew_get_dst I srcInkNew srcArtNew dstInkNew)
      (forkStoreDstInkNew_get_dart I srcInkNew srcArtNew dstInkNew)
      (forkStoreDstInkNew_get_urns I srcInkNew srcArtNew dstInkNew)
      (by simpa [evm1, evm2, evm3, storageStore_executionEnv] using hloadDstArt)
      hdstArtNew hdstArtGuardNeg hdstArtGuardPos
  have hfinalLoadsBlock :=
    execForkFinalLoadsOk (evm := evm4) (I := I)
      srcInkNew srcArtNew dstInkNew dstArtNew srcArtFinal dstArtFinal
      srcInkFinal dstInkFinal hsz164
      (by
        simpa [evm1, evm2, evm3, evm4, storageStore_executionEnv] using
          hloadSrcArtFinal)
      (by
        simpa [evm1, evm2, evm3, evm4, storageStore_executionEnv] using
          hloadDstArtFinal)
      (by
        simpa [evm1, evm2, evm3, evm4, storageStore_executionEnv] using
          hloadSrcInkFinal)
      (by
        simpa [evm1, evm2, evm3, evm4, storageStore_executionEnv] using
          hloadDstInkFinal)
  let localsFinal :=
    forkStoreFinalLoads I srcInkNew srcArtNew dstInkNew dstArtNew srcArtFinal
      dstArtFinal srcInkFinal dstInkFinal
  have hloadRateFinal :
      Solm.EVM.storageLoad evm4 evm4.executionEnv.codeOwner (forkIlkRateSlot I) = rate := by
    simpa [evm1, evm2, evm3, evm4, storageStore_executionEnv] using hloadRate
  have hloadSpotFinal :
      Solm.EVM.storageLoad evm4 evm4.executionEnv.codeOwner (forkIlkSpotSlot I) = spot := by
    simpa [evm1, evm2, evm3, evm4, storageStore_executionEnv] using hloadSpot
  have hutabBlock :=
    execForkUtabFinalMulOk (evm := evm4) (I := I)
      srcInkNew srcArtNew dstInkNew dstArtNew srcArtFinal dstArtFinal
      srcInkFinal dstInkFinal rate utab hsz164 hloadRateFinal
      hutabProd hutabFit hutabGuard
  have hvtabBlock :=
    execForkVtabFinalMulOk (evm := evm4) (I := I)
      srcInkNew srcArtNew dstInkNew dstArtNew srcArtFinal dstArtFinal
      srcInkFinal dstInkFinal rate utab vtab hsz164 hloadRateFinal
      hvtabProd hvtabFit hvtabGuard
  have hsrcInkSpotBlock :=
    execForkSrcInkSpotFinalMulOk (evm := evm4) (I := I)
      srcInkNew srcArtNew dstInkNew dstArtNew srcArtFinal dstArtFinal
      srcInkFinal dstInkFinal spot utab vtab srcInkSpot hsz164 hloadSpotFinal
      hsrcInkSpotProd hsrcInkSpotFit hsrcInkSpotGuard
  have hdstInkSpotBlock :=
    execForkDstInkSpotFinalMulOk (evm := evm4) (I := I)
      srcInkNew srcArtNew dstInkNew dstArtNew srcArtFinal dstArtFinal
      srcInkFinal dstInkFinal spot utab vtab srcInkSpot dstInkSpot hsz164 hloadSpotFinal
      hdstInkSpotProd hdstInkSpotFit hdstInkSpotGuard
  have h01 := execBlock_append hprefix hsrcInkBlock
  have h02 := execBlock_append h01 hsrcArtBlock
  have h03 := execBlock_append h02 hdstInkBlock
  have h04 := execBlock_append h03 hdstArtBlock
  have h05 := execBlock_append h04 hfinalLoadsBlock
  have h06 := execBlock_append h05 hutabBlock
  have h06 := execBlock_append h06 hvtabBlock
  have h07 := execBlock_append h06 hsrcInkSpotBlock
  have hblock := execBlock_append h07 hdstInkSpotBlock
  have hblock := execBlock_append hblock hfinalBlock
  simpa [ExecTransitionBody, forkTransition, nonpayable, checkedSubSignedInto,
    checkedAddSignedInto, checkedMulUintInto, List.append_assoc, storageStore_executionEnv] using
    ExecFuncBody.execBlockRevert hblock

theorem execForkSourceRevertWish {evm0 : EVM.State} {I : ExecutionEnv}
    (srcInkOld srcInkNew srcArtOld srcArtNew dstInkOld dstInkNew dstArtOld dstArtNew
      srcArtFinal dstArtFinal srcInkFinal dstInkFinal rate spot utab vtab
      srcInkSpot dstInkSpot : UInt256)
    (hwei : evm0.executionEnv.weiValue = ⟨0⟩)
    (hsz164 : 164 ≤ I.calldata.size)
    (hloadSrcInk :
      Solm.EVM.storageLoad evm0 evm0.executionEnv.codeOwner (forkSrcInkSlot I) = srcInkOld)
    (hsrcInkNew : srcInkNew = UInt256.sub srcInkOld (forkDinkWord I))
    (hsrcInkGuardNeg : forkDinkInt I ≤ 0 ∨ srcInkNew.toNat ≤ srcInkOld.toNat)
    (hsrcInkGuardPos : 0 ≤ forkDinkInt I ∨ srcInkOld.toNat ≤ srcInkNew.toNat)
    (hloadSrcArt :
      Solm.EVM.storageLoad
        (Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner (forkSrcInkSlot I)
          srcInkNew)
        evm0.executionEnv.codeOwner (forkSrcArtSlot I) = srcArtOld)
    (hsrcArtNew : srcArtNew = UInt256.sub srcArtOld (forkDartWord I))
    (hsrcArtGuardNeg : forkDartInt I ≤ 0 ∨ srcArtNew.toNat ≤ srcArtOld.toNat)
    (hsrcArtGuardPos : 0 ≤ forkDartInt I ∨ srcArtOld.toNat ≤ srcArtNew.toNat)
    (hloadDstInk :
      Solm.EVM.storageLoad
        (Solm.EVM.storageStore
          (Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner (forkSrcInkSlot I)
            srcInkNew)
          evm0.executionEnv.codeOwner (forkSrcArtSlot I) srcArtNew)
        evm0.executionEnv.codeOwner (forkDstInkSlot I) = dstInkOld)
    (hdstInkNew : dstInkNew = forkDinkWord I + dstInkOld)
    (hdstInkGuardNeg : 0 ≤ forkDinkInt I ∨ dstInkNew.toNat ≤ dstInkOld.toNat)
    (hdstInkGuardPos : forkDinkInt I ≤ 0 ∨ dstInkOld.toNat ≤ dstInkNew.toNat)
    (hloadDstArt :
      Solm.EVM.storageLoad
        (Solm.EVM.storageStore
          (Solm.EVM.storageStore
            (Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner (forkSrcInkSlot I)
              srcInkNew)
            evm0.executionEnv.codeOwner (forkSrcArtSlot I) srcArtNew)
          evm0.executionEnv.codeOwner (forkDstInkSlot I) dstInkNew)
        evm0.executionEnv.codeOwner (forkDstArtSlot I) = dstArtOld)
    (hdstArtNew : dstArtNew = forkDartWord I + dstArtOld)
    (hdstArtGuardNeg : 0 ≤ forkDartInt I ∨ dstArtNew.toNat ≤ dstArtOld.toNat)
    (hdstArtGuardPos : forkDartInt I ≤ 0 ∨ dstArtOld.toNat ≤ dstArtNew.toNat)
    (hloadSrcArtFinal :
      Solm.EVM.storageLoad
        (Solm.EVM.storageStore
          (Solm.EVM.storageStore
            (Solm.EVM.storageStore
              (Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner (forkSrcInkSlot I)
                srcInkNew)
              evm0.executionEnv.codeOwner (forkSrcArtSlot I) srcArtNew)
            evm0.executionEnv.codeOwner (forkDstInkSlot I) dstInkNew)
        evm0.executionEnv.codeOwner (forkDstArtSlot I) dstArtNew)
        evm0.executionEnv.codeOwner (forkSrcArtSlot I) = srcArtFinal)
    (hloadDstArtFinal :
      Solm.EVM.storageLoad
        (Solm.EVM.storageStore
          (Solm.EVM.storageStore
            (Solm.EVM.storageStore
              (Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner (forkSrcInkSlot I)
                srcInkNew)
              evm0.executionEnv.codeOwner (forkSrcArtSlot I) srcArtNew)
            evm0.executionEnv.codeOwner (forkDstInkSlot I) dstInkNew)
        evm0.executionEnv.codeOwner (forkDstArtSlot I) dstArtNew)
        evm0.executionEnv.codeOwner (forkDstArtSlot I) = dstArtFinal)
    (hloadSrcInkFinal :
      Solm.EVM.storageLoad
        (Solm.EVM.storageStore
          (Solm.EVM.storageStore
            (Solm.EVM.storageStore
              (Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner (forkSrcInkSlot I)
                srcInkNew)
              evm0.executionEnv.codeOwner (forkSrcArtSlot I) srcArtNew)
            evm0.executionEnv.codeOwner (forkDstInkSlot I) dstInkNew)
        evm0.executionEnv.codeOwner (forkDstArtSlot I) dstArtNew)
        evm0.executionEnv.codeOwner (forkSrcInkSlot I) = srcInkFinal)
    (hloadDstInkFinal :
      Solm.EVM.storageLoad
        (Solm.EVM.storageStore
          (Solm.EVM.storageStore
            (Solm.EVM.storageStore
              (Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner (forkSrcInkSlot I)
                srcInkNew)
              evm0.executionEnv.codeOwner (forkSrcArtSlot I) srcArtNew)
            evm0.executionEnv.codeOwner (forkDstInkSlot I) dstInkNew)
        evm0.executionEnv.codeOwner (forkDstArtSlot I) dstArtNew)
        evm0.executionEnv.codeOwner (forkDstInkSlot I) = dstInkFinal)
    (hloadRate :
      Solm.EVM.storageLoad
        (Solm.EVM.storageStore
          (Solm.EVM.storageStore
            (Solm.EVM.storageStore
              (Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner (forkSrcInkSlot I)
                srcInkNew)
              evm0.executionEnv.codeOwner (forkSrcArtSlot I) srcArtNew)
            evm0.executionEnv.codeOwner (forkDstInkSlot I) dstInkNew)
          evm0.executionEnv.codeOwner (forkDstArtSlot I) dstArtNew)
        evm0.executionEnv.codeOwner (forkIlkRateSlot I) = rate)
    (hloadSpot :
      Solm.EVM.storageLoad
        (Solm.EVM.storageStore
          (Solm.EVM.storageStore
            (Solm.EVM.storageStore
              (Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner (forkSrcInkSlot I)
                srcInkNew)
              evm0.executionEnv.codeOwner (forkSrcArtSlot I) srcArtNew)
            evm0.executionEnv.codeOwner (forkDstInkSlot I) dstInkNew)
          evm0.executionEnv.codeOwner (forkDstArtSlot I) dstArtNew)
        evm0.executionEnv.codeOwner (forkIlkSpotSlot I) = spot)
    (hutabProd : utab = UInt256.mul srcArtFinal rate)
    (hutabFit : srcArtFinal.toNat * rate.toNat < UInt256.size)
    (hutabGuard : rate.toNat = 0 ∨ utab.toNat / rate.toNat = srcArtFinal.toNat)
    (hvtabProd : vtab = UInt256.mul dstArtFinal rate)
    (hvtabFit : dstArtFinal.toNat * rate.toNat < UInt256.size)
    (hvtabGuard : rate.toNat = 0 ∨ vtab.toNat / rate.toNat = dstArtFinal.toNat)
    (hsrcInkSpotProd : srcInkSpot = UInt256.mul srcInkFinal spot)
    (hsrcInkSpotFit : srcInkFinal.toNat * spot.toNat < UInt256.size)
    (hsrcInkSpotGuard : spot.toNat = 0 ∨ srcInkSpot.toNat / spot.toNat = srcInkFinal.toNat)
    (hdstInkSpotProd : dstInkSpot = UInt256.mul dstInkFinal spot)
    (hdstInkSpotFit : dstInkFinal.toNat * spot.toNat < UInt256.size)
    (hdstInkSpotGuard : spot.toNat = 0 ∨ dstInkSpot.toNat / spot.toNat = dstInkFinal.toNat) :
    let evm1 := Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner
      (forkSrcInkSlot I) srcInkNew
    let evm2 := Solm.EVM.storageStore evm1 evm1.executionEnv.codeOwner
      (forkSrcArtSlot I) srcArtNew
    let evm3 := Solm.EVM.storageStore evm2 evm2.executionEnv.codeOwner
      (forkDstInkSlot I) dstInkNew
    let evm4 := Solm.EVM.storageStore evm3 evm3.executionEnv.codeOwner
      (forkDstArtSlot I) dstArtNew
    let finalLocals :=
      forkStoreDstInkSpotFinal I srcInkNew srcArtNew dstInkNew dstArtNew
        srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab vtab srcInkSpot dstInkSpot
    evalExpr? config { contract := contract, locals := finalLocals } evm4
        (bothExpr (wishExpr (.var "src") sender) (wishExpr (.var "dst") sender)) =
        .ok (.bool false) →
    ExecTransitionBody config contract evm0 (forkStore I) forkTransition.body .reverted := by
  intro evm1 evm2 evm3 evm4 finalLocals hwish
  exact execForkSourceRevertFinal (evm0 := evm0) (I := I)
    srcInkOld srcInkNew srcArtOld srcArtNew dstInkOld dstInkNew dstArtOld dstArtNew
    srcArtFinal dstArtFinal srcInkFinal dstInkFinal rate spot utab vtab srcInkSpot
    dstInkSpot hwei hsz164 hloadSrcInk hsrcInkNew
    hsrcInkGuardNeg hsrcInkGuardPos hloadSrcArt hsrcArtNew hsrcArtGuardNeg
    hsrcArtGuardPos hloadDstInk hdstInkNew hdstInkGuardNeg hdstInkGuardPos hloadDstArt
    hdstArtNew hdstArtGuardNeg hdstArtGuardPos hloadSrcArtFinal hloadDstArtFinal
    hloadSrcInkFinal hloadDstInkFinal hloadRate hloadSpot hutabProd hutabFit hutabGuard
    hvtabProd hvtabFit hvtabGuard hsrcInkSpotProd hsrcInkSpotFit hsrcInkSpotGuard
    hdstInkSpotProd hdstInkSpotFit hdstInkSpotGuard
    (by
      simpa [evm1, evm2, evm3, evm4, finalLocals, storageStore_executionEnv] using
        execForkFinalRequiresRevertWish hwish)

set_option maxHeartbeats 0 in
theorem decodeABIValues_bytes32_address_address_int256_int256_legacy_ok {bytes : List UInt8}
    (hlen0 : (bytes.take 32).length = 32)
    (hlen32 : ((bytes.drop 32).take 32).length = 32)
    (hlen64 : ((bytes.drop 64).take 32).length = 32)
    (hlen96 : ((bytes.drop 96).take 32).length = 32)
    (hlen128 : ((bytes.drop 128).take 32).length = 32) :
    decodeABIValues? [bytes32, addr, addr, int256, int256] bytes 0 0 160 160
      DecodeMode.legacySolc05 =
      some
        ([ .fixedBytes bytes32Width (bytes.take 32),
           .address (AccountAddress.ofNat
             (ABI.bytesToWord ((bytes.drop 32).take 32)).toNat),
           .address (AccountAddress.ofNat
             (ABI.bytesToWord ((bytes.drop 64).take 32)).toNat),
           .int
             (if (ABI.bytesToWord ((bytes.drop 96).take 32)).toNat < EVM.twoPow 255 then
               Int.ofNat (ABI.bytesToWord ((bytes.drop 96).take 32)).toNat
             else
               Int.ofNat (ABI.bytesToWord ((bytes.drop 96).take 32)).toNat -
                 Int.ofNat EVM.wordModulus),
           .int
             (if (ABI.bytesToWord ((bytes.drop 128).take 32)).toNat < EVM.twoPow 255 then
               Int.ofNat (ABI.bytesToWord ((bytes.drop 128).take 32)).toNat
             else
               Int.ofNat (ABI.bytesToWord ((bytes.drop 128).take 32)).toNat -
                 Int.ofNat EVM.wordModulus) ],
         160) := by
  have hge32 : 32 ≤ bytes.length - 32 := by
    rw [List.length_take, List.length_drop] at hlen32
    omega
  have hge64 : 32 ≤ bytes.length - 64 := by
    rw [List.length_take, List.length_drop] at hlen64
    omega
  have hge96 : 32 ≤ bytes.length - 96 := by
    rw [List.length_take, List.length_drop] at hlen96
    omega
  have hge128 : 32 ≤ bytes.length - 128 := by
    rw [List.length_take, List.length_drop] at hlen128
    omega
  have htakeBytes32 :
      List.take (↑bytes32Width + 1) (List.take 32 bytes) = List.take 32 bytes := by
    simp [bytes32Width]
  have hltWord96 :
      ↑(ABI.bytesToWord ((bytes.drop 96).take 32)).val < EVM.wordModulus := by
    change (ABI.bytesToWord ((bytes.drop 96).take 32)).val.val < EVM.twoPow 256
    exact (ABI.bytesToWord ((bytes.drop 96).take 32)).val.isLt
  have hltWord128 :
      ↑(ABI.bytesToWord ((bytes.drop 128).take 32)).val < EVM.wordModulus := by
    change (ABI.bytesToWord ((bytes.drop 128).take 32)).val.val < EVM.twoPow 256
    exact (ABI.bytesToWord ((bytes.drop 128).take 32)).val.isLt
  have hmod96Val :
      (↑(ABI.bytesToWord ((bytes.drop 96).take 32)).val) % EVM.wordModulus =
        ↑(ABI.bytesToWord ((bytes.drop 96).take 32)).val :=
    Nat.mod_eq_of_lt hltWord96
  have hmod96Int :
      ((↑(↑(ABI.bytesToWord ((bytes.drop 96).take 32)).val) : Int) %
          (↑EVM.wordModulus : Int)) =
        (↑(↑(ABI.bytesToWord ((bytes.drop 96).take 32)).val) : Int) := by
    exact Int.emod_eq_of_lt (Int.natCast_nonneg _) (by exact_mod_cast hltWord96)
  have hmod128Val :
      (↑(ABI.bytesToWord ((bytes.drop 128).take 32)).val) % EVM.wordModulus =
        ↑(ABI.bytesToWord ((bytes.drop 128).take 32)).val :=
    Nat.mod_eq_of_lt hltWord128
  have hmod128Int :
      ((↑(↑(ABI.bytesToWord ((bytes.drop 128).take 32)).val) : Int) %
          (↑EVM.wordModulus : Int)) =
        (↑(↑(ABI.bytesToWord ((bytes.drop 128).take 32)).val) : Int) := by
    exact Int.emod_eq_of_lt (Int.natCast_nonneg _) (by exact_mod_cast hltWord128)
  set_option linter.unusedSimpArgs false in
    simp (config := { maxSteps := 200000 }) [decodeABIValues?, decodeABIValue?, readBytes?,
      readWord?, decodeABIWord?,
      bytes32, addr, int256, bytes32Width, int256Int, isDynamicABIType,
      staticABIEncodedSize?, hlen0, hlen32, hlen64, hlen96, hlen128, htakeBytes32,
      hge32, hge64, hge96, hge128, UInt256.toNat,
      show EVM.twoPow (256 - 1) = EVM.twoPow 255 by rfl,
      show EVM.twoPow 256 = EVM.wordModulus by rfl]
  rw [hmod96Val]
  rw [hmod96Int]
  rw [hmod128Val]
  rw [hmod128Int]
  exact ⟨rfl, rfl⟩

set_option maxHeartbeats 0 in
theorem decodeCalldata_legacyBytes32_address_address_int256_int256_ok {cd : ByteArray}
    {v w x y z : Solm.Ident} (hsz164 : 164 ≤ cd.size) :
    decodeCalldataWithMode DecodeMode.legacySolc05 [v, w, x, y, z]
      [bytes32, addr, addr, int256, int256] cd =
      some ((((((∅ : Store).insert v
        (.fixedBytes bytes32Width ((cd.toList.drop 4).take 32))).insert w
        (.address (AccountAddress.ofNat (calldataWord cd 36).toNat))).insert x
        (.address (AccountAddress.ofNat (calldataWord cd 68).toNat))).insert y
        (.int
          (if (calldataWord cd 100).toNat < EVM.twoPow 255 then
            Int.ofNat (calldataWord cd 100).toNat
          else
            Int.ofNat (calldataWord cd 100).toNat - Int.ofNat EVM.wordModulus))).insert z
        (.int
          (if (calldataWord cd 132).toNat < EVM.twoPow 255 then
            Int.ofNat (calldataWord cd 132).toNat
          else
            Int.ofNat (calldataWord cd 132).toNat - Int.ofNat EVM.wordModulus))) := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have htake4 : ((cd.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  have htake36 : ((cd.toList.drop 36).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  have htake68 : ((cd.toList.drop 68).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  have htake100 : ((cd.toList.drop 100).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  have htake132 : ((cd.toList.drop 132).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  have hword36 : ABI.bytesToWord ((cd.toList.drop 36).take 32) = calldataWord cd 36 :=
    decode_word_at_eq cd 36 (by omega) (by norm_num)
  have hword68 : ABI.bytesToWord ((cd.toList.drop 68).take 32) = calldataWord cd 68 :=
    decode_word_at_eq cd 68 (by omega) (by norm_num)
  have hword100 : ABI.bytesToWord ((cd.toList.drop 100).take 32) = calldataWord cd 100 :=
    decode_word_at_eq cd 100 (by omega) (by norm_num)
  have hword132 : ABI.bytesToWord ((cd.toList.drop 132).take 32) = calldataWord cd 132 :=
    decode_word_at_eq cd 132 (by omega) (by norm_num)
  unfold decodeCalldataWithMode decodeCalldata
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  rw [if_neg (by simp [bytes32, addr, int256, isDynamicABIType])]
  simp only
  simp only [decodeCalldata.decodeArgs]
  rw [show abiTupleHeadSize? [bytes32, addr, addr, int256, int256] = some 160 by native_decide]
  simp only [bind, Option.bind]
  rw [if_neg (by rw [List.length_drop, htlen]; omega :
    ¬ (cd.toList.drop 4).length < 160)]
  rw [decodeABIValues_bytes32_address_address_int256_int256_legacy_ok
    (bytes := cd.toList.drop 4)
    (by simpa using htake4)
    (by simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
      using htake36)
    (by simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
      using htake68)
    (by simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
      using htake100)
    (by simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
      using htake132)]
  rw [show ABI.bytesToWord (((cd.toList.drop 4).drop 32).take 32) =
      calldataWord cd 36 from by
    simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hword36]
  rw [show ABI.bytesToWord (((cd.toList.drop 4).drop 64).take 32) =
      calldataWord cd 68 from by
    simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hword68]
  rw [show ABI.bytesToWord (((cd.toList.drop 4).drop 96).take 32) =
      calldataWord cd 100 from by
    simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hword100]
  rw [show ABI.bytesToWord (((cd.toList.drop 4).drop 128).take 32) =
      calldataWord cd 132 from by
    simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hword132]
  simp [decodeCalldata.insertValues]

set_option maxHeartbeats 0 in
theorem vatDecode_fork_ok {I : ExecutionEnv} (hsz164 : 164 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (forkTransition.params.map Param.name)
      (transitionSignature forkTransition).paramTypes I.calldata = some (forkStore I) := by
  show decodeCalldataWithMode config.abiDecodeMode ["ilk", "src", "dst", "dink", "dart"]
    [bytes32, addr, addr, int256, int256] I.calldata = _
  change decodeCalldataWithMode DecodeMode.legacySolc05 ["ilk", "src", "dst", "dink", "dart"]
    [bytes32, addr, addr, int256, int256] I.calldata = some (forkStore I)
  simpa [forkStore, forkIlkValue, forkSrcValue, forkDstValue, forkDinkValue,
    forkDartValue, forkSrcWord, forkDstWord, forkDinkWord, forkDartWord,
    forkDinkInt, forkDartInt, calldataWord] using
      decodeCalldata_legacyBytes32_address_address_int256_int256_ok
        (cd := I.calldata) (v := "ilk") (w := "src") (x := "dst") (y := "dink")
        (z := "dart") hsz164

theorem vatDecode_fork_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 164) :
    decodeCalldataWithMode config.abiDecodeMode (forkTransition.params.map Param.name)
      (transitionSignature forkTransition).paramTypes I.calldata = none := by
  show decodeCalldataWithMode config.abiDecodeMode ["ilk", "src", "dst", "dink", "dart"]
    [bytes32, addr, addr, int256, int256] I.calldata = none
  change decodeCalldataWithMode DecodeMode.legacySolc05 ["ilk", "src", "dst", "dink", "dart"]
    [bytes32, addr, addr, int256, int256] I.calldata = none
  have htlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  unfold decodeCalldataWithMode decodeCalldata
  rw [if_neg (by rw [htlen]; omega : ¬ I.calldata.toList.length < 4)]
  rw [if_neg (by simp [bytes32, addr, int256, isDynamicABIType])]
  simp only
  simp only [decodeCalldata.decodeArgs]
  rw [show abiTupleHeadSize? [bytes32, addr, addr, int256, int256] = some 160 by native_decide]
  simp only [bind, Option.bind]
  rw [if_pos (by rw [List.length_drop, htlen]; omega :
    (I.calldata.toList.drop 4).length < 160)]

theorem vatDispatchFork {I : ExecutionEnv}
    (hsel : selIs I (vatSelBytes 10)) :
    dispatchMsg contract I.calldata = some forkTransition := by
  have hcd : I.calldata.extract 0 4 = vatSelBytes 10 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some forkTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd, LineSelectorBytes, cageSelectorBytes,
    canSelectorBytes, daiSelectorBytes, debtSelectorBytes, denySelectorBytes,
    fileIlkSelectorBytes, fileLineSelectorBytes, fluxSelectorBytes, foldSelectorBytes,
    forkSelectorBytes]
  native_decide

theorem vatReachForkBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = vatBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (vatSelBytes 10)) :
    ∃ k C, RD vatBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨1095⟩ [vatSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  have hword : vatSelWord I = ⟨0x870c616d⟩ :=
    vatSelWord_eq_of_beq I hsz 0x87 0x0c 0x61 0x6d ⟨0x870c616d⟩
      (by native_decide) (by simpa [vatSelBytes] using hsel)
  have hroot : UInt256.gt (armSelNat vatBytecode vatRootSplitPc) (vatSelWord I) = ⟨0⟩ := by
    rw [hword]
    native_decide
  have hhigh : UInt256.gt (armSelNat vatBytecode vatHighSplitPc) (vatSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  have hhighlow :
      UInt256.gt (armSelNat vatBytecode vatHighLowSplitPc) (vatSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  have heq0 : ∀ j, j < 1 →
      UInt256.eq (armSelNat vatBytecode (nthArmPc vatBytecode vatArms212FirstPc j))
        (vatSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j
    rw [hword]
    native_decide
  have htake :
      UInt256.eq (armSelNat vatBytecode (nthArmPc vatBytecode vatArms212FirstPc 1))
        (vatSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  exact vatReachArms212Body 1 (by omega) ⟨1095⟩ hcode hwv hsz hsize
    hroot hhigh hhighlow heq0 htake (by jump_dest) (by native_decide)

@[reducible] def solcForkExternalLoadAndJumpWf
    (code : ByteArray) (pc routine : UInt256) : Prop :=
  let p1 := pc + ⟨1⟩
  let p2 := p1 + ⟨1⟩
  let p3 := p2 + ⟨1⟩
  let p4 := p3 + ⟨1⟩
  let p5 := p4 + ⟨1⟩
  let p7 := p5 + UInt256.ofNat 2
  let p9 := p7 + UInt256.ofNat 2
  let p11 := p9 + UInt256.ofNat 2
  let p12 := p11 + ⟨1⟩
  let p13 := p12 + ⟨1⟩
  let p15 := p13 + UInt256.ofNat 2
  let p16 := p15 + ⟨1⟩
  let p17 := p16 + ⟨1⟩
  let p18 := p17 + ⟨1⟩
  let p19 := p18 + ⟨1⟩
  let p20 := p19 + ⟨1⟩
  let p21 := p20 + ⟨1⟩
  let p23 := p21 + UInt256.ofNat 2
  let p24 := p23 + ⟨1⟩
  let p25 := p24 + ⟨1⟩
  let p26 := p25 + ⟨1⟩
  let p27 := p26 + ⟨1⟩
  let p28 := p27 + ⟨1⟩
  let p29 := p28 + ⟨1⟩
  let p30 := p29 + ⟨1⟩
  let p32 := p30 + UInt256.ofNat 2
  let p33 := p32 + ⟨1⟩
  let p34 := p33 + ⟨1⟩
  let p35 := p34 + ⟨1⟩
  let p36 := p35 + ⟨1⟩
  let p38 := p36 + UInt256.ofNat 2
  let p39 := p38 + ⟨1⟩
  let p40 := p39 + ⟨1⟩
  let p43 := p40 + UInt256.ofNat 3
  decode code pc = some (.JUMPDEST, .none)
  ∧ decode code p1 = some (.POP, .none)
  ∧ decode code p2 = some (.DUP1, .none)
  ∧ decode code p3 = some (.CALLDATALOAD, .none)
  ∧ decode code p4 = some (.SWAP1, .none)
  ∧ decode code p5 = some (.Push .PUSH1, some (⟨1⟩, 1))
  ∧ decode code p7 = some (.Push .PUSH1, some (⟨1⟩, 1))
  ∧ decode code p9 = some (.Push .PUSH1, some (⟨160⟩, 1))
  ∧ decode code p11 = some (.SHL, .none)
  ∧ decode code p12 = some (.SUB, .none)
  ∧ decode code p13 = some (.Push .PUSH1, some (⟨32⟩, 1))
  ∧ decode code p15 = some (.DUP3, .none)
  ∧ decode code p16 = some (.ADD, .none)
  ∧ decode code p17 = some (.CALLDATALOAD, .none)
  ∧ decode code p18 = some (.DUP2, .none)
  ∧ decode code p19 = some (.AND, .none)
  ∧ decode code p20 = some (.SWAP2, .none)
  ∧ decode code p21 = some (.Push .PUSH1, some (⟨64⟩, 1))
  ∧ decode code p23 = some (.DUP2, .none)
  ∧ decode code p24 = some (.ADD, .none)
  ∧ decode code p25 = some (.CALLDATALOAD, .none)
  ∧ decode code p26 = some (.SWAP1, .none)
  ∧ decode code p27 = some (.SWAP2, .none)
  ∧ decode code p28 = some (.AND, .none)
  ∧ decode code p29 = some (.SWAP1, .none)
  ∧ decode code p30 = some (.Push .PUSH1, some (⟨96⟩, 1))
  ∧ decode code p32 = some (.DUP2, .none)
  ∧ decode code p33 = some (.ADD, .none)
  ∧ decode code p34 = some (.CALLDATALOAD, .none)
  ∧ decode code p35 = some (.SWAP1, .none)
  ∧ decode code p36 = some (.Push .PUSH1, some (⟨128⟩, 1))
  ∧ decode code p38 = some (.ADD, .none)
  ∧ decode code p39 = some (.CALLDATALOAD, .none)
  ∧ decode code p40 = some (.Push .PUSH2, some (routine, 2))
  ∧ decode code p43 = some (.JUMP, .none)

set_option maxHeartbeats 1000000 in
theorem RD.solcForkExternalLoadAndJump {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {decoded ret routine de : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD code ee g s0 decoded (de :: ⟨4⟩ :: ret :: R) mem aw rdata acc k C)
    (hwf : solcForkExternalLoadAndJumpWf code decoded routine)
    (hroutine : (D_J code 0).contains routine = true)
    (hov : R.length + 9 ≤ 1024) :
    ∃ k' C', RD code ee g s0 routine
      (calldataWord ee.calldata 132 ::
        calldataWord ee.calldata 100 ::
        UInt256.land solcAddrMask (calldataWord ee.calldata 68) ::
        UInt256.land solcAddrMask (calldataWord ee.calldata 36) ::
        calldataWord ee.calldata 4 :: ret :: R)
      mem aw rdata acc k' C' := by
  rcases hwf with
    ⟨hd0, hd1, hd2, hd3, hd4, hd5, hd7, hd9, hd11, hd12, hd13, hd15, hd16,
      hd17, hd18, hd19, hd20, hd21, hd23, hd24, hd25, hd26, hd27, hd28, hd29,
      hd30, hd32, hd33, hd34, hd35, hd36, hd38, hd39, hd40, hd43⟩
  have rd1 := h.jumpdest hd0 (by evm_ov)
  have rd2 := rd1.pop hd1 (by evm_ov)
  have rd3 := rd2.dup1 hd2 (by evm_ov)
  have rd4 := rd3.calldataload hd3 (by evm_ov)
  have rd5 := rd4.swap1 hd4 (by evm_ov)
  have rd7 := rd5.push1 ⟨1⟩ hd5 (by evm_ov)
  have rd9 := rd7.push1 ⟨1⟩ hd7 (by evm_ov)
  have rd11 := rd9.push1 ⟨160⟩ hd9 (by evm_ov)
  have rd12 := rd11.shl hd11 (by evm_ov)
  have rd13 := rd12.sub hd12 (by evm_ov)
  have rd15 := rd13.push1 ⟨32⟩ hd13 (by evm_ov)
  have rd16 := rd15.dup3 hd15 (by evm_ov)
  have rd17 := rd16.add hd16 (by evm_ov)
  have rd18 := rd17.calldataload hd17 (by evm_ov)
  have rd19 := rd18.dup2 hd18 (by evm_ov)
  have rd20 := rd19.and hd19 (by evm_ov)
  have rd21 := rd20.swap2 hd20 (by evm_ov)
  have rd23 := rd21.push1 ⟨64⟩ hd21 (by evm_ov)
  have rd24 := rd23.dup2 hd23 (by evm_ov)
  have rd25 := rd24.add hd24 (by evm_ov)
  have rd26 := rd25.calldataload hd25 (by evm_ov)
  have rd27 := rd26.swap1 hd26 (by evm_ov)
  have rd28 := rd27.swap2 hd27 (by evm_ov)
  have rd29 := rd28.and hd28 (by evm_ov)
  have rd30 := rd29.swap1 hd29 (by evm_ov)
  have rd32 := rd30.push1 ⟨96⟩ hd30 (by evm_ov)
  have rd33 := rd32.dup2 hd32 (by evm_ov)
  have rd34 := rd33.add hd33 (by evm_ov)
  have rd35 := rd34.calldataload hd34 (by evm_ov)
  have rd36 := rd35.swap1 hd35 (by evm_ov)
  have rd38 := rd36.push1 ⟨128⟩ hd36 (by evm_ov)
  have rd39 := rd38.add hd38 (by evm_ov)
  have rd40 := rd39.calldataload hd39 (by evm_ov)
  have rd43 := rd40.push2 routine hd40 (by evm_ov)
  exact ⟨_, _, by
    simpa [calldataWord, show (⟨4⟩ : UInt256).toNat = 4 from by decide,
      show ((⟨4⟩ : UInt256) + ⟨32⟩).toNat = 36 from by decide,
      show ((⟨4⟩ : UInt256) + ⟨64⟩).toNat = 68 from by decide,
      show ((⟨4⟩ : UInt256) + ⟨96⟩).toNat = 100 from by decide,
      show ((⟨4⟩ : UInt256) + ⟨128⟩).toNat = 132 from by decide,
      show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
        solcAddrMask from by decide, u256_land_comm]
      using rd43.jump hd43 hroutine (by evm_ov)⟩

theorem vatForkX_decoded {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz164 : 164 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hreach : ∃ k C, RD vatBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1095⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD vatBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4726⟩
        [forkDartWord I, forkDinkWord I, forkDstMaskedWord I, forkSrcMaskedWord I,
          forkIlkWord I, ⟨524⟩, sel]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, hdecoded⟩ := RD.solcExternalStaticArgsLenOk
    (code := vatBytecode) (sel := sel) (entry := ⟨1095⟩) (ret := ⟨524⟩)
    (decoded := ⟨1117⟩) (need := ⟨160⟩) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by jump_dest)
    (by exact solcDecodeLenCheckOkUnsigned (by simpa using hsz164) hsize)
  obtain ⟨_, _, hroutine⟩ := RD.solcForkExternalLoadAndJump
    (code := vatBytecode) (decoded := ⟨1117⟩) (ret := ⟨524⟩) (routine := ⟨4726⟩)
    (R := [sel]) hdecoded
    (by
      unfold solcForkExternalLoadAndJumpWf
      repeat' first | apply And.intro | native_decide)
    (by jump_dest) (by simp)
  exact ⟨_, _, by
    simpa [forkDartWord, forkDinkWord, forkDstMaskedWord, forkDstWord, forkSrcMaskedWord,
      forkSrcWord, forkIlkWord] using hroutine⟩

theorem vatForkX_shortarg {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 164)
    (hsize : I.calldata.size < UInt256.size)
    (hreach : ∃ k C, RD vatBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1095⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev vatBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hlt :
      UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨160⟩ = ⟨1⟩ := by
    apply ult_one
    rw [usub_ofNat_word_toNat (by simpa using hsz4) hsize]
    change I.calldata.size - 4 < 160
    omega
  exact RD.solcExternalStaticArgsShortReverts
    (code := vatBytecode) (sel := sel) (entry := ⟨1095⟩) (ret := ⟨524⟩)
    (decoded := ⟨1117⟩) (need := ⟨160⟩) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) hlt

theorem vatForkBodyCoreDecodeFailed_short
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = vatBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 164)
    (hsel : selIs I (vatSelBytes 10))
    (hreach : ∃ k C, RD vatBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1095⟩ [vatSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  exact (vatForkX_shortarg (g := Sat256.ofUInt256 g) hsz4 hshort hsize hreach)
    |>.reEquivDecodingFailed hcode (vatDispatchFork hsel)
      (vatDecode_fork_none_short hsz4 hshort)

set_option maxHeartbeats 1000000 in
theorem forkWordAt0Mem_twoWordHashMem_solcMappingSlot (baseSlot key oldKey : UInt256)
    {mem : ByteArray} (hmem : mem.size = 96) :
    UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC ((wordAt0Mem key (twoWordHashMem oldKey baseSlot mem)).readWithPadding 0 64))) =
      solcMappingSlot baseSlot key := by
  have hbase : (twoWordHashMem oldKey baseSlot mem).size = 96 :=
    twoWordHashMem_size_96 oldKey baseSlot hmem
  have hread64 :
      (wordAt0Mem key (twoWordHashMem oldKey baseSlot mem)).readWithPadding 0 64 =
        UInt256.toByteArray key ++ UInt256.toByteArray baseSlot := by
    rw [readWithPadding_eq_extract' _ 0 64 (by norm_num) (by norm_num)
        (by rw [wordAt0Mem_size_96 key hbase]; omega)]
    have hleft :
        (wordAt0Mem key (twoWordHashMem oldKey baseSlot mem)).extract 0 32 =
          UInt256.toByteArray key := by
      rw [← readWithPadding_eq_extract _ 0
          (by rw [wordAt0Mem_size_96 key hbase]; omega),
        wordAt0Mem_read0]
    have hright :
        (wordAt0Mem key (twoWordHashMem oldKey baseSlot mem)).extract 32 64 =
          UInt256.toByteArray baseSlot := by
      rw [← readWithPadding_eq_extract _ 32
          (by rw [wordAt0Mem_size_96 key hbase]; omega)]
      unfold wordAt0Mem
      rw [write32_read_above _ _ 0 32 (by rw [toByteArray_size]) (by rw [hbase]; omega)
        (by omega) (by rw [hbase]; norm_num)]
      exact twoWordHashMem_read32 oldKey baseSlot hmem
    rw [show (wordAt0Mem key (twoWordHashMem oldKey baseSlot mem)).extract 0 64 =
        (wordAt0Mem key (twoWordHashMem oldKey baseSlot mem)).extract 0 32 ++
          (wordAt0Mem key (twoWordHashMem oldKey baseSlot mem)).extract 32 64 by
        rw [ByteArray.extract_append_extract]
        norm_num]
    rw [hleft, hright]
  rw [hread64]
  unfold solcMappingSlot
  exact mappingSlot_single key baseSlot

theorem wordAt0Mem_read64 (key : UInt256) {mem : ByteArray} (hmem : mem.size = 96) :
    (wordAt0Mem key mem).readWithPadding 64 32 = mem.readWithPadding 64 32 := by
  unfold wordAt0Mem
  rw [write32_read_above _ _ 0 64 (by rw [toByteArray_size])
    (by omega) (by omega) (by rw [hmem])]

theorem RD.vatCheckedMulUintOk {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {x y ret : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {activeWords : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD vatBytecode ee g s0 ⟨6752⟩ (x :: y :: ret :: R) mem
      activeWords rdata acc k C)
    (hok :
      x = ⟨0⟩ ∨
        UInt256.eq (UInt256.div (UInt256.mul y x) x) y ≠ ⟨0⟩)
    (hret : (D_J vatBytecode 0).contains ret = true)
    (hov : R.length + 10 ≤ 1024) :
    ∃ k' C', RD vatBytecode ee g s0 ret ((UInt256.mul y x) :: R) mem
      activeWords rdata acc k' C' := by
  let prod := UInt256.mul y x
  have rd6753 := h.jumpdest (by native_decide) (by evm_ov)
  have rd6755 := rd6753.push1 ⟨0⟩ (by native_decide) (by evm_ov)
  have rd6756 := rd6755.dup2 (by native_decide) (by evm_ov)
  have rd6757 := rd6756.iszero (by native_decide) (by evm_ov)
  have rd6758 := rd6757.dup1 (by native_decide) (by evm_ov)
  have rd6761pre := rd6758.push2 ⟨6697⟩ (by native_decide) (by evm_ov)
  by_cases hxzero : x = ⟨0⟩
  · have rd6697 := by
      rw [hxzero, show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rd6761pre
      simpa [prod] using rd6761pre.jumpiT (by native_decide) one_ne_zero_uint
        (by jump_dest) (by evm_ov)
    have rd6698 := rd6697.jumpdest (by native_decide) (by evm_ov)
    have rd6701 := rd6698.push2 ⟨6615⟩ (by native_decide) (by evm_ov)
    have rd6615 := rd6701.jumpiT (by native_decide) one_ne_zero_uint (by jump_dest)
      (by evm_ov)
    have rd6616 := rd6615.jumpdest (by native_decide) (by evm_ov)
    have rd6617 := rd6616.swap3 (by native_decide) (by evm_ov)
    have rd6618 := rd6617.swap2 (by native_decide) (by evm_ov)
    have rd6619 := rd6618.pop (by native_decide) (by evm_ov)
    have rd6620 := rd6619.pop (by native_decide) (by evm_ov)
    exact ⟨_, _, by
      simpa [prod, hxzero] using rd6620.jump (by native_decide) hret (by evm_ov)⟩
  · have rd6762 := by
      have hcond : UInt256.isZero x = ⟨0⟩ := isZero_eq_zero_of_ne hxzero
      rw [hcond] at rd6761pre
      simpa [prod] using rd6761pre.jumpiNT (by native_decide)
        (by decide : (⟨0⟩ : UInt256) = ⟨0⟩) (by evm_ov)
    have rd6763 := rd6762.pop (by native_decide) (by evm_ov)
    have rd6764 := rd6763.pop (by native_decide) (by evm_ov)
    have rd6765 := rd6764.dup1 (by native_decide) (by evm_ov)
    have rd6766 := rd6765.dup3 (by native_decide) (by evm_ov)
    have rd6767 := rd6766.mul (by native_decide) (by evm_ov)
    have rd6768 := rd6767.dup3 (by native_decide) (by evm_ov)
    have rd6769 := rd6768.dup3 (by native_decide) (by evm_ov)
    have rd6770 := rd6769.dup3 (by native_decide) (by evm_ov)
    have rd6771 := rd6770.dup2 (by native_decide)
      (by simp only [List.length_cons] at hov ⊢; omega)
    have rd6774pre := rd6771.push2 ⟨6776⟩ (by native_decide)
      (by simp only [List.length_cons] at hov ⊢; omega)
    have rd6776 := by
      simpa [prod] using rd6774pre.jumpiT (by native_decide) hxzero (by jump_dest)
        (by evm_ov)
    have rd6777 := rd6776.jumpdest (by native_decide) (by evm_ov)
    have rd6778pre := RD.div rd6777 (by native_decide) (by evm_ov)
    have rd6779 := rd6778pre.eq (by native_decide) (by evm_ov)
    have rd6782pre := rd6779.push2 ⟨6615⟩ (by native_decide) (by evm_ov)
    have heq : UInt256.eq (UInt256.div prod x) y ≠ ⟨0⟩ := by
      simpa [prod] using hok.resolve_left hxzero
    have rd6615 := rd6782pre.jumpiT (by native_decide) heq (by jump_dest)
      (by evm_ov)
    have rd6616 := rd6615.jumpdest (by native_decide) (by evm_ov)
    have rd6617 := rd6616.swap3 (by native_decide) (by evm_ov)
    have rd6618 := rd6617.swap2 (by native_decide) (by evm_ov)
    have rd6619 := rd6618.pop (by native_decide) (by evm_ov)
    have rd6620 := rd6619.pop (by native_decide) (by evm_ov)
    exact ⟨_, _, by simpa [prod] using rd6620.jump (by native_decide) hret (by evm_ov)⟩

set_option maxHeartbeats 1000000 in
theorem RD.vatCheckedMulUintRevert {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {x y ret : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {activeWords : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD vatBytecode ee g s0 ⟨6752⟩ (x :: y :: ret :: R) mem
      activeWords rdata acc k C)
    (hfail :
      ¬ (x = ⟨0⟩ ∨
        UInt256.eq (UInt256.div (UInt256.mul y x) x) y ≠ ⟨0⟩))
    (hov : R.length + 10 ≤ 1024) :
    RDrev vatBytecode g s0 := by
  let prod := UInt256.mul y x
  have hxzero : x ≠ ⟨0⟩ := by
    intro hx
    exact hfail (Or.inl hx)
  have heqZero :
      UInt256.eq (UInt256.div prod x) y = ⟨0⟩ := by
    by_contra hne
    exact hfail (Or.inr (by simpa [prod] using hne))
  have rd6753 := h.jumpdest (by native_decide) (by evm_ov)
  have rd6755 := rd6753.push1 ⟨0⟩ (by native_decide) (by evm_ov)
  have rd6756 := rd6755.dup2 (by native_decide) (by evm_ov)
  have rd6757 := rd6756.iszero (by native_decide) (by evm_ov)
  have rd6758 := rd6757.dup1 (by native_decide) (by evm_ov)
  have rd6761pre := rd6758.push2 ⟨6697⟩ (by native_decide) (by evm_ov)
  have rd6762 := by
    have hcond : UInt256.isZero x = ⟨0⟩ := isZero_eq_zero_of_ne hxzero
    rw [hcond] at rd6761pre
    simpa [prod] using rd6761pre.jumpiNT (by native_decide)
      (by decide : (⟨0⟩ : UInt256) = ⟨0⟩) (by evm_ov)
  have rd6763 := rd6762.pop (by native_decide) (by evm_ov)
  have rd6764 := rd6763.pop (by native_decide) (by evm_ov)
  have rd6765 := rd6764.dup1 (by native_decide) (by evm_ov)
  have rd6766 := rd6765.dup3 (by native_decide) (by evm_ov)
  have rd6767 := rd6766.mul (by native_decide) (by evm_ov)
  have rd6768 := rd6767.dup3 (by native_decide) (by evm_ov)
  have rd6769 := rd6768.dup3 (by native_decide) (by evm_ov)
  have rd6770 := rd6769.dup3 (by native_decide) (by evm_ov)
  have rd6771 := rd6770.dup2 (by native_decide)
    (by simp only [List.length_cons] at hov ⊢; omega)
  have rd6774pre := rd6771.push2 ⟨6776⟩ (by native_decide)
    (by simp only [List.length_cons] at hov ⊢; omega)
  have rd6776 := by
    simpa [prod] using rd6774pre.jumpiT (by native_decide) hxzero (by jump_dest)
      (by evm_ov)
  have rd6777 := rd6776.jumpdest (by native_decide) (by evm_ov)
  have rd6778pre := RD.div rd6777 (by native_decide) (by evm_ov)
  have rd6779 := rd6778pre.eq (by native_decide) (by evm_ov)
  have rd6782pre := rd6779.push2 ⟨6615⟩ (by native_decide) (by evm_ov)
  have rd6783 := by
    rw [heqZero] at rd6782pre
    simpa [prod] using rd6782pre.jumpiNT (by native_decide)
      (by decide : (⟨0⟩ : UInt256) = ⟨0⟩) (by evm_ov)
  have rdRev := evm_run rd6783 with [
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov)]
  exact RD.rev 0 rdRev (by native_decide) (fun s _ hstk => memExpRevert0 s hstk)
    (by evm_ov)

set_option maxHeartbeats 1000000 in
theorem RD.vatForkSrcInkSubSuccess
    {cA gh bl σ σ₀ A I} {g : Sat256} {k C : ℕ} {sel : UInt256}
    {mem : ByteArray}
    (h : RD vatBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4726⟩
      [forkDartWord I, forkDinkWord I, forkDstMaskedWord I, forkSrcMaskedWord I,
        forkIlkWord I, ⟨524⟩, sel]
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hmem : mem.size = 96)
    (hsz164 : 164 ≤ I.calldata.size)
    (hpos :
      UInt256.sgt (forkDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.gt
          (UInt256.sub (solcSlotWord σ I (forkSrcInkSlot I)) (forkDinkWord I))
          (solcSlotWord σ I (forkSrcInkSlot I)) = ⟨0⟩)
    (hneg :
      UInt256.slt (forkDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.lt
          (UInt256.sub (solcSlotWord σ I (forkSrcInkSlot I)) (forkDinkWord I))
          (solcSlotWord σ I (forkSrcInkSlot I)) = ⟨0⟩) :
    ∃ k' C', RD vatBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4792⟩
      [UInt256.sub (solcSlotWord σ I (forkSrcInkSlot I)) (forkDinkWord I),
        forkIlkBase I, forkDstUrnBase I, forkSrcUrnBase I, forkDartWord I,
        forkDinkWord I, forkDstMaskedWord I, forkSrcMaskedWord I, forkIlkWord I,
        ⟨524⟩, sel]
      (twoWordHashMem (forkIlkWord I) ⟨2⟩
        (wordAt0Mem (forkDstMaskedWord I)
          (twoWordHashMem (forkSrcMaskedWord I) (solcMappingSlot ⟨3⟩ (forkIlkWord I))
            (twoWordHashMem (forkIlkWord I) ⟨3⟩ mem))))
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  let urnsIlk := solcMappingSlot ⟨3⟩ (forkIlkWord I)
  let srcBase := solcMappingSlot urnsIlk (forkSrcMaskedWord I)
  let dstBase := solcMappingSlot urnsIlk (forkDstMaskedWord I)
  let ilkBase := solcMappingSlot ⟨2⟩ (forkIlkWord I)
  let srcInkOld := solcSlotWord σ I srcBase
  have rd4727 := h.jumpdest (by native_decide) (by evm_ov)
  have rd4729 := rd4727.push1 ⟨0⟩ (by native_decide) (by evm_ov)
  have rd4730 := rd4729.dup6 (by native_decide) (by evm_ov)
  have rd4731pre := rd4730.dup2 (by native_decide) (by evm_ov)
  have rd4732 := rd4731pre.mstore 0 (wordAt0Mem (forkIlkWord I) mem)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd4734 := rd4732.push1 ⟨3⟩ (by native_decide) (by evm_ov)
  have rd4736 := rd4734.push1 ⟨32⟩ (by native_decide) (by evm_ov)
  have rd4737 := rd4736.swap1 (by native_decide) (by evm_ov)
  have rd4738pre := rd4737.dup2 (by native_decide) (by evm_ov)
  have rd4739 := rd4738pre.mstore 0 (twoWordHashMem (forkIlkWord I) ⟨3⟩ mem)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd4741 := rd4739.push1 ⟨64⟩ (by native_decide) (by evm_ov)
  have rd4742 := rd4741.dup1 (by native_decide) (by evm_ov)
  have rd4743pre := rd4742.dup4 (by native_decide) (by evm_ov)
  have hurnsIlk :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((twoWordHashMem (forkIlkWord I) ⟨3⟩ mem).readWithPadding 0 64))) =
        urnsIlk := by
    simpa [urnsIlk] using twoWordHashMem_solcMappingSlot ⟨3⟩ (forkIlkWord I) hmem
  have rd4744 := rd4743pre.keccak256 0 urnsIlk (UInt256.ofNat 3)
    (by native_decide) mem_cost hurnsIlk (by native_decide) (by evm_ov)
  have rd4746 := rd4744.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  have rd4748 := rd4746.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  have rd4750 := rd4748.push1 ⟨160⟩ (by native_decide) (by evm_ov)
  have rd4751 := rd4750.shl (by native_decide) (by evm_ov)
  have rd4752 := rd4751.sub (by native_decide) (by evm_ov)
  have rd4753 := rd4752.dup9 (by native_decide) (by evm_ov)
  have rd4754raw := rd4753.dup2 (by native_decide) (by evm_ov)
  have rd4755raw := rd4754raw.and (by native_decide) (by evm_ov)
  have hsrcMask :
      UInt256.land
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩)
          (forkSrcMaskedWord I) =
        forkSrcMaskedWord I := by
    rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by decide]
    rw [u256_land_comm]
    exact solcAddrMask_clean (forkSrcMaskedWord_canonical I)
  have rd4755 := rd4755raw
  rw [hsrcMask] at rd4755
  have rd4756 := rd4755.dup6 (by native_decide) (by evm_ov)
  have rd4757 := rd4756.mstore 0
    (wordAt0Mem (forkSrcMaskedWord I) (twoWordHashMem (forkIlkWord I) ⟨3⟩ mem))
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd4758 := rd4757.swap1 (by native_decide) (by evm_ov)
  have rd4759pre := rd4758.dup4 (by native_decide) (by evm_ov)
  have rd4760 := rd4759pre.mstore 0
    (twoWordHashMem (forkSrcMaskedWord I) urnsIlk
      (twoWordHashMem (forkIlkWord I) ⟨3⟩ mem))
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd4761 := rd4760.dup2 (by native_decide) (by evm_ov)
  have rd4762pre := rd4761.dup5 (by native_decide) (by evm_ov)
  have hmemIlk3 : (twoWordHashMem (forkIlkWord I) ⟨3⟩ mem).size = 96 :=
    twoWordHashMem_size_96 (forkIlkWord I) ⟨3⟩ hmem
  have hsrcBase :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((twoWordHashMem (forkSrcMaskedWord I) urnsIlk
            (twoWordHashMem (forkIlkWord I) ⟨3⟩ mem)).readWithPadding 0 64))) =
        srcBase := by
    simpa [srcBase] using
      twoWordHashMem_solcMappingSlot urnsIlk (forkSrcMaskedWord I) hmemIlk3
  have rd4763 := rd4762pre.keccak256 0 srcBase (UInt256.ofNat 3)
    (by native_decide) mem_cost hsrcBase (by native_decide) (by evm_ov)
  have rd4764 := rd4763.swap1 (by native_decide) (by evm_ov)
  have rd4765raw := rd4764.dup8 (by native_decide) (by evm_ov)
  have rd4766raw := rd4765raw.and (by native_decide) (by evm_ov)
  have hdstMask :
      UInt256.land (forkDstMaskedWord I)
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩) =
        forkDstMaskedWord I := by
    rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by decide]
    exact solcAddrMask_clean (forkDstMaskedWord_canonical I)
  have rd4766 := rd4766raw
  rw [hdstMask] at rd4766
  have rd4767 := rd4766.dup5 (by native_decide) (by evm_ov)
  have rd4768 := rd4767.mstore 0
    (wordAt0Mem (forkDstMaskedWord I)
      (twoWordHashMem (forkSrcMaskedWord I) urnsIlk
        (twoWordHashMem (forkIlkWord I) ⟨3⟩ mem)))
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd4769pre := rd4768.dup2 (by native_decide) (by evm_ov)
  have rd4770pre := rd4769pre.dup5 (by native_decide) (by evm_ov)
  have hmemSrcBase :
      (twoWordHashMem (forkSrcMaskedWord I) urnsIlk
        (twoWordHashMem (forkIlkWord I) ⟨3⟩ mem)).size = 96 :=
    twoWordHashMem_size_96 (forkSrcMaskedWord I) urnsIlk hmemIlk3
  have hdstBase :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((wordAt0Mem (forkDstMaskedWord I)
            (twoWordHashMem (forkSrcMaskedWord I) urnsIlk
              (twoWordHashMem (forkIlkWord I) ⟨3⟩ mem))).readWithPadding 0 64))) =
        dstBase := by
    simpa [dstBase] using
      forkWordAt0Mem_twoWordHashMem_solcMappingSlot urnsIlk (forkDstMaskedWord I)
        (forkSrcMaskedWord I) hmemIlk3
  have rd4771 := rd4770pre.keccak256 0 dstBase (UInt256.ofNat 3)
    (by native_decide) mem_cost hdstBase (by native_decide) (by evm_ov)
  have rd4772 := rd4771.dup10 (by native_decide) (by evm_ov)
  have rd4773pre := rd4772.dup6 (by native_decide) (by evm_ov)
  have rd4774 := rd4773pre.mstore 0
    (wordAt0Mem (forkIlkWord I)
      (wordAt0Mem (forkDstMaskedWord I)
        (twoWordHashMem (forkSrcMaskedWord I) urnsIlk
          (twoWordHashMem (forkIlkWord I) ⟨3⟩ mem))))
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd4776 := rd4774.push1 ⟨2⟩ (by native_decide) (by evm_ov)
  have rd4777 := rd4776.swap1 (by native_decide) (by evm_ov)
  have rd4778pre := rd4777.swap4 (by native_decide) (by evm_ov)
  have rd4779 := rd4778pre.mstore 0
    (twoWordHashMem (forkIlkWord I) ⟨2⟩
      (wordAt0Mem (forkDstMaskedWord I)
        (twoWordHashMem (forkSrcMaskedWord I) urnsIlk
          (twoWordHashMem (forkIlkWord I) ⟨3⟩ mem))))
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd4780 := rd4779.swap3 (by native_decide) (by evm_ov)
  have hmemDstBase :
      (wordAt0Mem (forkDstMaskedWord I)
        (twoWordHashMem (forkSrcMaskedWord I) urnsIlk
          (twoWordHashMem (forkIlkWord I) ⟨3⟩ mem))).size = 96 :=
    wordAt0Mem_size_96 (forkDstMaskedWord I) hmemSrcBase
  have hilkBase :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((twoWordHashMem (forkIlkWord I) ⟨2⟩
            (wordAt0Mem (forkDstMaskedWord I)
              (twoWordHashMem (forkSrcMaskedWord I) urnsIlk
                (twoWordHashMem (forkIlkWord I) ⟨3⟩ mem)))).readWithPadding 0 64))) =
        ilkBase := by
    simpa [ilkBase] using twoWordHashMem_solcMappingSlot ⟨2⟩ (forkIlkWord I) hmemDstBase
  have rd4781 := rd4780.keccak256 0 ilkBase (UInt256.ofNat 3)
    (by native_decide) mem_cost hilkBase (by native_decide) (by evm_ov)
  have rd4782pre := rd4781.dup3 (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd4783raw⟩ := rd4782pre.sload (by native_decide) (by evm_ov)
  have hold :
      (σ.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD srcBase ⟨0⟩)) =
        srcInkOld := by
    simp [srcInkOld, solcSlotWord]
  have rd4783 := rd4783raw
  rw [hold] at rd4783
  have rd4786 := rd4783.push2 ⟨4792⟩ (by native_decide) (by evm_ov)
  have rd4787 := rd4786.swap1 (by native_decide) (by evm_ov)
  have rd4788 := rd4787.dup7 (by native_decide) (by evm_ov)
  have rd4791 := rd4788.push2 ⟨6795⟩ (by native_decide) (by evm_ov)
  have rd6795 := rd4791.jump (by native_decide) (by jump_dest) (by evm_ov)
  obtain ⟨_, _, rd4792⟩ := RD.vatSignedSubOk
    (x := srcInkOld) (y := forkDinkWord I) (ret := ⟨4792⟩)
    (R := ilkBase :: dstBase :: srcBase :: forkDartWord I :: forkDinkWord I ::
      forkDstMaskedWord I :: forkSrcMaskedWord I :: forkIlkWord I :: ⟨524⟩ :: sel :: [])
    rd6795
    (by simpa [srcInkOld, srcBase, forkSrcInkSlot_eq I hsz164] using hpos)
    (by simpa [srcInkOld, srcBase, forkSrcInkSlot_eq I hsz164] using hneg)
    (by jump_dest) (by simp)
  exact ⟨_, _, by
    simpa [srcInkOld, srcBase, dstBase, ilkBase, urnsIlk, forkSrcUrnBase_eq I hsz164,
      forkDstUrnBase_eq I hsz164, forkIlkBase_eq I hsz164,
      forkSrcInkSlot_eq I hsz164]
      using rd4792⟩

set_option maxHeartbeats 1000000 in
theorem RD.vatForkSrcInkSubRevert
    {cA gh bl σ σ₀ A I} {g : Sat256} {k C : ℕ} {sel : UInt256}
    {mem : ByteArray}
    (h : RD vatBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4726⟩
      [forkDartWord I, forkDinkWord I, forkDstMaskedWord I, forkSrcMaskedWord I,
        forkIlkWord I, ⟨524⟩, sel]
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hmem : mem.size = 96)
    (hsz164 : 164 ≤ I.calldata.size)
    (hfail :
      ¬ (UInt256.sgt (forkDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.gt
          (UInt256.sub (solcSlotWord σ I (forkSrcInkSlot I)) (forkDinkWord I))
          (solcSlotWord σ I (forkSrcInkSlot I)) = ⟨0⟩) ∨
      (UInt256.sgt (forkDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.gt
          (UInt256.sub (solcSlotWord σ I (forkSrcInkSlot I)) (forkDinkWord I))
          (solcSlotWord σ I (forkSrcInkSlot I)) = ⟨0⟩) ∧
        ¬ (UInt256.slt (forkDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
          UInt256.lt
            (UInt256.sub (solcSlotWord σ I (forkSrcInkSlot I)) (forkDinkWord I))
            (solcSlotWord σ I (forkSrcInkSlot I)) = ⟨0⟩)) :
    RDrev vatBytecode g (initState cA gh bl σ σ₀ g A I) := by
  let urnsIlk := solcMappingSlot ⟨3⟩ (forkIlkWord I)
  let srcBase := solcMappingSlot urnsIlk (forkSrcMaskedWord I)
  let dstBase := solcMappingSlot urnsIlk (forkDstMaskedWord I)
  let ilkBase := solcMappingSlot ⟨2⟩ (forkIlkWord I)
  let srcInkOld := solcSlotWord σ I srcBase
  have rd4727 := h.jumpdest (by native_decide) (by evm_ov)
  have rd4729 := rd4727.push1 ⟨0⟩ (by native_decide) (by evm_ov)
  have rd4730 := rd4729.dup6 (by native_decide) (by evm_ov)
  have rd4731pre := rd4730.dup2 (by native_decide) (by evm_ov)
  have rd4732 := rd4731pre.mstore 0 (wordAt0Mem (forkIlkWord I) mem)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd4734 := rd4732.push1 ⟨3⟩ (by native_decide) (by evm_ov)
  have rd4736 := rd4734.push1 ⟨32⟩ (by native_decide) (by evm_ov)
  have rd4737 := rd4736.swap1 (by native_decide) (by evm_ov)
  have rd4738pre := rd4737.dup2 (by native_decide) (by evm_ov)
  have rd4739 := rd4738pre.mstore 0 (twoWordHashMem (forkIlkWord I) ⟨3⟩ mem)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd4741 := rd4739.push1 ⟨64⟩ (by native_decide) (by evm_ov)
  have rd4742 := rd4741.dup1 (by native_decide) (by evm_ov)
  have rd4743pre := rd4742.dup4 (by native_decide) (by evm_ov)
  have hurnsIlk :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((twoWordHashMem (forkIlkWord I) ⟨3⟩ mem).readWithPadding 0 64))) =
        urnsIlk := by
    simpa [urnsIlk] using twoWordHashMem_solcMappingSlot ⟨3⟩ (forkIlkWord I) hmem
  have rd4744 := rd4743pre.keccak256 0 urnsIlk (UInt256.ofNat 3)
    (by native_decide) mem_cost hurnsIlk (by native_decide) (by evm_ov)
  have rd4746 := rd4744.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  have rd4748 := rd4746.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  have rd4750 := rd4748.push1 ⟨160⟩ (by native_decide) (by evm_ov)
  have rd4751 := rd4750.shl (by native_decide) (by evm_ov)
  have rd4752 := rd4751.sub (by native_decide) (by evm_ov)
  have rd4753 := rd4752.dup9 (by native_decide) (by evm_ov)
  have rd4754raw := rd4753.dup2 (by native_decide) (by evm_ov)
  have rd4755raw := rd4754raw.and (by native_decide) (by evm_ov)
  have hsrcMask :
      UInt256.land
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩)
          (forkSrcMaskedWord I) =
        forkSrcMaskedWord I := by
    rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by decide]
    rw [u256_land_comm]
    exact solcAddrMask_clean (forkSrcMaskedWord_canonical I)
  have rd4755 := rd4755raw
  rw [hsrcMask] at rd4755
  have rd4756 := rd4755.dup6 (by native_decide) (by evm_ov)
  have rd4757 := rd4756.mstore 0
    (wordAt0Mem (forkSrcMaskedWord I) (twoWordHashMem (forkIlkWord I) ⟨3⟩ mem))
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd4758 := rd4757.swap1 (by native_decide) (by evm_ov)
  have rd4759pre := rd4758.dup4 (by native_decide) (by evm_ov)
  have rd4760 := rd4759pre.mstore 0
    (twoWordHashMem (forkSrcMaskedWord I) urnsIlk
      (twoWordHashMem (forkIlkWord I) ⟨3⟩ mem))
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd4761 := rd4760.dup2 (by native_decide) (by evm_ov)
  have rd4762pre := rd4761.dup5 (by native_decide) (by evm_ov)
  have hmemIlk3 : (twoWordHashMem (forkIlkWord I) ⟨3⟩ mem).size = 96 :=
    twoWordHashMem_size_96 (forkIlkWord I) ⟨3⟩ hmem
  have hsrcBase :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((twoWordHashMem (forkSrcMaskedWord I) urnsIlk
            (twoWordHashMem (forkIlkWord I) ⟨3⟩ mem)).readWithPadding 0 64))) =
        srcBase := by
    simpa [srcBase] using
      twoWordHashMem_solcMappingSlot urnsIlk (forkSrcMaskedWord I) hmemIlk3
  have rd4763 := rd4762pre.keccak256 0 srcBase (UInt256.ofNat 3)
    (by native_decide) mem_cost hsrcBase (by native_decide) (by evm_ov)
  have rd4764 := rd4763.swap1 (by native_decide) (by evm_ov)
  have rd4765raw := rd4764.dup8 (by native_decide) (by evm_ov)
  have rd4766raw := rd4765raw.and (by native_decide) (by evm_ov)
  have hdstMask :
      UInt256.land (forkDstMaskedWord I)
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩) =
        forkDstMaskedWord I := by
    rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by decide]
    exact solcAddrMask_clean (forkDstMaskedWord_canonical I)
  have rd4766 := rd4766raw
  rw [hdstMask] at rd4766
  have rd4767 := rd4766.dup5 (by native_decide) (by evm_ov)
  have rd4768 := rd4767.mstore 0
    (wordAt0Mem (forkDstMaskedWord I)
      (twoWordHashMem (forkSrcMaskedWord I) urnsIlk
        (twoWordHashMem (forkIlkWord I) ⟨3⟩ mem)))
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd4769pre := rd4768.dup2 (by native_decide) (by evm_ov)
  have rd4770pre := rd4769pre.dup5 (by native_decide) (by evm_ov)
  have hmemSrcBase :
      (twoWordHashMem (forkSrcMaskedWord I) urnsIlk
        (twoWordHashMem (forkIlkWord I) ⟨3⟩ mem)).size = 96 :=
    twoWordHashMem_size_96 (forkSrcMaskedWord I) urnsIlk hmemIlk3
  have hdstBase :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((wordAt0Mem (forkDstMaskedWord I)
            (twoWordHashMem (forkSrcMaskedWord I) urnsIlk
              (twoWordHashMem (forkIlkWord I) ⟨3⟩ mem))).readWithPadding 0 64))) =
        dstBase := by
    simpa [dstBase] using
      forkWordAt0Mem_twoWordHashMem_solcMappingSlot urnsIlk (forkDstMaskedWord I)
        (forkSrcMaskedWord I) hmemIlk3
  have rd4771 := rd4770pre.keccak256 0 dstBase (UInt256.ofNat 3)
    (by native_decide) mem_cost hdstBase (by native_decide) (by evm_ov)
  have rd4772 := rd4771.dup10 (by native_decide) (by evm_ov)
  have rd4773pre := rd4772.dup6 (by native_decide) (by evm_ov)
  have rd4774 := rd4773pre.mstore 0
    (wordAt0Mem (forkIlkWord I)
      (wordAt0Mem (forkDstMaskedWord I)
        (twoWordHashMem (forkSrcMaskedWord I) urnsIlk
          (twoWordHashMem (forkIlkWord I) ⟨3⟩ mem))))
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd4776 := rd4774.push1 ⟨2⟩ (by native_decide) (by evm_ov)
  have rd4777 := rd4776.swap1 (by native_decide) (by evm_ov)
  have rd4778pre := rd4777.swap4 (by native_decide) (by evm_ov)
  have rd4779 := rd4778pre.mstore 0
    (twoWordHashMem (forkIlkWord I) ⟨2⟩
      (wordAt0Mem (forkDstMaskedWord I)
        (twoWordHashMem (forkSrcMaskedWord I) urnsIlk
          (twoWordHashMem (forkIlkWord I) ⟨3⟩ mem))))
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd4780 := rd4779.swap3 (by native_decide) (by evm_ov)
  have hmemDstBase :
      (wordAt0Mem (forkDstMaskedWord I)
        (twoWordHashMem (forkSrcMaskedWord I) urnsIlk
          (twoWordHashMem (forkIlkWord I) ⟨3⟩ mem))).size = 96 :=
    wordAt0Mem_size_96 (forkDstMaskedWord I) hmemSrcBase
  have hilkBase :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((twoWordHashMem (forkIlkWord I) ⟨2⟩
            (wordAt0Mem (forkDstMaskedWord I)
              (twoWordHashMem (forkSrcMaskedWord I) urnsIlk
                (twoWordHashMem (forkIlkWord I) ⟨3⟩ mem)))).readWithPadding 0 64))) =
        ilkBase := by
    simpa [ilkBase] using twoWordHashMem_solcMappingSlot ⟨2⟩ (forkIlkWord I) hmemDstBase
  have rd4781 := rd4780.keccak256 0 ilkBase (UInt256.ofNat 3)
    (by native_decide) mem_cost hilkBase (by native_decide) (by evm_ov)
  have rd4782pre := rd4781.dup3 (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd4783raw⟩ := rd4782pre.sload (by native_decide) (by evm_ov)
  have hold :
      (σ.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD srcBase ⟨0⟩)) =
        srcInkOld := by
    simp [srcInkOld, solcSlotWord]
  have rd4783 := rd4783raw
  rw [hold] at rd4783
  have rd4786 := rd4783.push2 ⟨4792⟩ (by native_decide) (by evm_ov)
  have rd4787 := rd4786.swap1 (by native_decide) (by evm_ov)
  have rd4788 := rd4787.dup7 (by native_decide) (by evm_ov)
  have rd4791 := rd4788.push2 ⟨6795⟩ (by native_decide) (by evm_ov)
  have rd6795 := rd4791.jump (by native_decide) (by jump_dest) (by evm_ov)
  exact RD.vatSignedSubRevert
    (x := srcInkOld) (y := forkDinkWord I) (ret := ⟨4792⟩)
    (R := ilkBase :: dstBase :: srcBase :: forkDartWord I :: forkDinkWord I ::
      forkDstMaskedWord I :: forkSrcMaskedWord I :: forkIlkWord I :: ⟨524⟩ :: sel :: [])
    rd6795
    (by simpa [srcInkOld, srcBase, forkSrcInkSlot_eq I hsz164] using hfail)
    (by simp)

theorem RD.vatForkSrcArtSubSuccess
    {cA gh bl σ σ₀ A I} {g : Sat256} {k C : ℕ} {sel srcInkNew : UInt256}
    {mem : ByteArray}
    (h : RD vatBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4792⟩
      [srcInkNew, forkIlkBase I, forkDstUrnBase I, forkSrcUrnBase I, forkDartWord I,
        forkDinkWord I, forkDstMaskedWord I, forkSrcMaskedWord I, forkIlkWord I,
        ⟨524⟩, sel]
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hperm : I.perm = true)
    (hpos :
      UInt256.sgt (forkDartWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.gt
          (UInt256.sub
            (solcSlotWord
              (sstoreAccountMap I.codeOwner σ (forkSrcInkSlot I) srcInkNew)
              I (forkSrcArtSlot I))
            (forkDartWord I))
          (solcSlotWord
            (sstoreAccountMap I.codeOwner σ (forkSrcInkSlot I) srcInkNew)
            I (forkSrcArtSlot I)) = ⟨0⟩)
    (hneg :
      UInt256.slt (forkDartWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.lt
          (UInt256.sub
            (solcSlotWord
              (sstoreAccountMap I.codeOwner σ (forkSrcInkSlot I) srcInkNew)
              I (forkSrcArtSlot I))
            (forkDartWord I))
          (solcSlotWord
            (sstoreAccountMap I.codeOwner σ (forkSrcInkSlot I) srcInkNew)
            I (forkSrcArtSlot I)) = ⟨0⟩) :
    ∃ k' C', RD vatBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4809⟩
      [UInt256.sub
          (solcSlotWord
            (sstoreAccountMap I.codeOwner σ (forkSrcInkSlot I) srcInkNew)
            I (forkSrcArtSlot I))
          (forkDartWord I),
        forkIlkBase I, forkDstUrnBase I, forkSrcUrnBase I, forkDartWord I,
        forkDinkWord I, forkDstMaskedWord I, forkSrcMaskedWord I, forkIlkWord I,
        ⟨524⟩, sel]
      mem (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ (forkSrcInkSlot I) srcInkNew) k' C' := by
  let srcBase := forkSrcUrnBase I
  let σSrcInk := sstoreAccountMap I.codeOwner σ (forkSrcInkSlot I) srcInkNew
  let srcArtOld := solcSlotWord σSrcInk I (forkSrcArtSlot I)
  have rd4793 := h.jumpdest (by native_decide) (by evm_ov)
  have rd4794pre := rd4793.dup4 (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd4795raw⟩ := rd4794pre.sstore hperm (by native_decide) (by evm_ov)
  have hrd4795 :
      ∃ k' C', RD vatBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4795⟩
        [forkIlkBase I, forkDstUrnBase I, forkSrcUrnBase I, forkDartWord I,
          forkDinkWord I, forkDstMaskedWord I, forkSrcMaskedWord I, forkIlkWord I,
          ⟨524⟩, sel]
        mem (UInt256.ofNat 3) ByteArray.empty (cA, σSrcInk) k' C' := by
    exact ⟨_, _, by
      simpa [σSrcInk, forkSrcInkSlot] using rd4795raw⟩
  obtain ⟨_, _, rd4795⟩ := hrd4795
  have rd4797 := rd4795.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  have rd4798pre := rd4797.dup4 (by native_decide) (by evm_ov)
  have rd4799pre := rd4798pre.add (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd4800raw⟩ := rd4799pre.sload (by native_decide) (by evm_ov)
  have hold :
      (σSrcInk.find? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD (srcBase + ⟨1⟩) ⟨0⟩)) = srcArtOld := by
    simp [srcArtOld, solcSlotWord, σSrcInk, srcBase, forkSrcArtSlot]
  have rd4800 := rd4800raw
  rw [hold] at rd4800
  have rd4803 := rd4800.push2 ⟨4809⟩ (by native_decide) (by evm_ov)
  have rd4804 := rd4803.swap1 (by native_decide) (by evm_ov)
  have rd4805 := rd4804.dup6 (by native_decide) (by evm_ov)
  have rd4808 := rd4805.push2 ⟨6795⟩ (by native_decide) (by evm_ov)
  have rd6795 := rd4808.jump (by native_decide) (by jump_dest) (by evm_ov)
  obtain ⟨_, _, rd4809⟩ := RD.vatSignedSubOk
    (x := srcArtOld) (y := forkDartWord I) (ret := ⟨4809⟩)
    (R := forkIlkBase I :: forkDstUrnBase I :: forkSrcUrnBase I ::
      forkDartWord I :: forkDinkWord I :: forkDstMaskedWord I ::
      forkSrcMaskedWord I :: forkIlkWord I :: ⟨524⟩ :: sel :: [])
    rd6795
    (by simpa [srcArtOld, σSrcInk] using hpos)
    (by simpa [srcArtOld, σSrcInk] using hneg)
    (by jump_dest) (by simp)
  exact ⟨_, _, by
    simpa [srcArtOld, σSrcInk] using rd4809⟩

theorem RD.vatForkSrcArtSubRevert
    {cA gh bl σ σ₀ A I} {g : Sat256} {k C : ℕ} {sel srcInkNew : UInt256}
    {mem : ByteArray}
    (h : RD vatBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4792⟩
      [srcInkNew, forkIlkBase I, forkDstUrnBase I, forkSrcUrnBase I, forkDartWord I,
        forkDinkWord I, forkDstMaskedWord I, forkSrcMaskedWord I, forkIlkWord I,
        ⟨524⟩, sel]
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hperm : I.perm = true)
    (hfail :
      ¬ (UInt256.sgt (forkDartWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.gt
          (UInt256.sub
            (solcSlotWord
              (sstoreAccountMap I.codeOwner σ (forkSrcInkSlot I) srcInkNew)
              I (forkSrcArtSlot I))
            (forkDartWord I))
          (solcSlotWord
            (sstoreAccountMap I.codeOwner σ (forkSrcInkSlot I) srcInkNew)
            I (forkSrcArtSlot I)) = ⟨0⟩) ∨
      (UInt256.sgt (forkDartWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.gt
          (UInt256.sub
            (solcSlotWord
              (sstoreAccountMap I.codeOwner σ (forkSrcInkSlot I) srcInkNew)
              I (forkSrcArtSlot I))
            (forkDartWord I))
          (solcSlotWord
            (sstoreAccountMap I.codeOwner σ (forkSrcInkSlot I) srcInkNew)
            I (forkSrcArtSlot I)) = ⟨0⟩) ∧
        ¬ (UInt256.slt (forkDartWord I) ⟨0⟩ = ⟨0⟩ ∨
          UInt256.lt
            (UInt256.sub
              (solcSlotWord
                (sstoreAccountMap I.codeOwner σ (forkSrcInkSlot I) srcInkNew)
                I (forkSrcArtSlot I))
              (forkDartWord I))
            (solcSlotWord
              (sstoreAccountMap I.codeOwner σ (forkSrcInkSlot I) srcInkNew)
              I (forkSrcArtSlot I)) = ⟨0⟩)) :
    RDrev vatBytecode g (initState cA gh bl σ σ₀ g A I) := by
  let srcBase := forkSrcUrnBase I
  let σSrcInk := sstoreAccountMap I.codeOwner σ (forkSrcInkSlot I) srcInkNew
  let srcArtOld := solcSlotWord σSrcInk I (forkSrcArtSlot I)
  have rd4793 := h.jumpdest (by native_decide) (by evm_ov)
  have rd4794pre := rd4793.dup4 (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd4795raw⟩ := rd4794pre.sstore hperm (by native_decide) (by evm_ov)
  have hrd4795 :
      ∃ k' C', RD vatBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4795⟩
        [forkIlkBase I, forkDstUrnBase I, forkSrcUrnBase I, forkDartWord I,
          forkDinkWord I, forkDstMaskedWord I, forkSrcMaskedWord I, forkIlkWord I,
          ⟨524⟩, sel]
        mem (UInt256.ofNat 3) ByteArray.empty (cA, σSrcInk) k' C' := by
    exact ⟨_, _, by
      simpa [σSrcInk, forkSrcInkSlot] using rd4795raw⟩
  obtain ⟨_, _, rd4795⟩ := hrd4795
  have rd4797 := rd4795.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  have rd4798pre := rd4797.dup4 (by native_decide) (by evm_ov)
  have rd4799pre := rd4798pre.add (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd4800raw⟩ := rd4799pre.sload (by native_decide) (by evm_ov)
  have hold :
      (σSrcInk.find? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD (srcBase + ⟨1⟩) ⟨0⟩)) = srcArtOld := by
    simp [srcArtOld, solcSlotWord, σSrcInk, srcBase, forkSrcArtSlot]
  have rd4800 := rd4800raw
  rw [hold] at rd4800
  have rd4803 := rd4800.push2 ⟨4809⟩ (by native_decide) (by evm_ov)
  have rd4804 := rd4803.swap1 (by native_decide) (by evm_ov)
  have rd4805 := rd4804.dup6 (by native_decide) (by evm_ov)
  have rd4808 := rd4805.push2 ⟨6795⟩ (by native_decide) (by evm_ov)
  have rd6795 := rd4808.jump (by native_decide) (by jump_dest) (by evm_ov)
  exact RD.vatSignedSubRevert
    (x := srcArtOld) (y := forkDartWord I) (ret := ⟨4809⟩)
    (R := forkIlkBase I :: forkDstUrnBase I :: forkSrcUrnBase I ::
      forkDartWord I :: forkDinkWord I :: forkDstMaskedWord I ::
      forkSrcMaskedWord I :: forkIlkWord I :: ⟨524⟩ :: sel :: [])
    rd6795
    (by simpa [srcArtOld, σSrcInk] using hfail)
    (by simp)

theorem RD.vatForkDstInkAddSuccess
    {cA gh bl σ σ₀ A I} {g : Sat256} {k C : ℕ}
    {sel srcInkNew srcArtNew : UInt256} {mem : ByteArray}
    (h : RD vatBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4809⟩
      [srcArtNew, forkIlkBase I, forkDstUrnBase I, forkSrcUrnBase I, forkDartWord I,
        forkDinkWord I, forkDstMaskedWord I, forkSrcMaskedWord I, forkIlkWord I,
        ⟨524⟩, sel]
      mem (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ (forkSrcInkSlot I) srcInkNew) k C)
    (hperm : I.perm = true)
    (hneg :
      UInt256.slt (forkDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.gt
          (forkDinkWord I +
            solcSlotWord
              (sstoreAccountMap I.codeOwner
                (sstoreAccountMap I.codeOwner σ (forkSrcInkSlot I) srcInkNew)
                (forkSrcArtSlot I) srcArtNew)
              I (forkDstInkSlot I))
          (solcSlotWord
            (sstoreAccountMap I.codeOwner
              (sstoreAccountMap I.codeOwner σ (forkSrcInkSlot I) srcInkNew)
              (forkSrcArtSlot I) srcArtNew)
            I (forkDstInkSlot I)) = ⟨0⟩)
    (hpos :
      UInt256.sgt (forkDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.lt
          (forkDinkWord I +
            solcSlotWord
              (sstoreAccountMap I.codeOwner
                (sstoreAccountMap I.codeOwner σ (forkSrcInkSlot I) srcInkNew)
                (forkSrcArtSlot I) srcArtNew)
              I (forkDstInkSlot I))
          (solcSlotWord
            (sstoreAccountMap I.codeOwner
              (sstoreAccountMap I.codeOwner σ (forkSrcInkSlot I) srcInkNew)
              (forkSrcArtSlot I) srcArtNew)
            I (forkDstInkSlot I)) = ⟨0⟩) :
    ∃ k' C', RD vatBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4826⟩
      [forkDinkWord I +
          solcSlotWord
            (sstoreAccountMap I.codeOwner
              (sstoreAccountMap I.codeOwner σ (forkSrcInkSlot I) srcInkNew)
              (forkSrcArtSlot I) srcArtNew)
            I (forkDstInkSlot I),
        forkIlkBase I, forkDstUrnBase I, forkSrcUrnBase I, forkDartWord I,
        forkDinkWord I, forkDstMaskedWord I, forkSrcMaskedWord I, forkIlkWord I,
        ⟨524⟩, sel]
      mem (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner σ (forkSrcInkSlot I) srcInkNew)
        (forkSrcArtSlot I) srcArtNew) k' C' := by
  let srcBase := forkSrcUrnBase I
  let dstBase := forkDstUrnBase I
  let σSrcInk := sstoreAccountMap I.codeOwner σ (forkSrcInkSlot I) srcInkNew
  let σSrcArt := sstoreAccountMap I.codeOwner σSrcInk (forkSrcArtSlot I) srcArtNew
  let dstInkOld := solcSlotWord σSrcArt I (forkDstInkSlot I)
  have rd4810 := h.jumpdest (by native_decide) (by evm_ov)
  have rd4812 := rd4810.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  have rd4813pre := rd4812.dup5 (by native_decide) (by evm_ov)
  have rd4814pre := rd4813pre.add (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd4815raw⟩ := rd4814pre.sstore hperm (by native_decide) (by evm_ov)
  have hrd4815 :
      ∃ k' C', RD vatBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4815⟩
        [forkIlkBase I, forkDstUrnBase I, forkSrcUrnBase I, forkDartWord I,
          forkDinkWord I, forkDstMaskedWord I, forkSrcMaskedWord I, forkIlkWord I,
          ⟨524⟩, sel]
        mem (UInt256.ofNat 3) ByteArray.empty (cA, σSrcArt) k' C' := by
    exact ⟨_, _, by
      simpa [σSrcArt, σSrcInk, srcBase, forkSrcArtSlot, forkSrcInkSlot] using rd4815raw⟩
  obtain ⟨_, _, rd4815⟩ := hrd4815
  have rd4816pre := rd4815.dup2 (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd4817raw⟩ := rd4816pre.sload (by native_decide) (by evm_ov)
  have hold :
      (σSrcArt.find? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD dstBase ⟨0⟩)) = dstInkOld := by
    simp [dstInkOld, solcSlotWord, σSrcArt, dstBase, forkDstInkSlot]
  have rd4817 := rd4817raw
  rw [hold] at rd4817
  have rd4820 := rd4817.push2 ⟨4826⟩ (by native_decide) (by evm_ov)
  have rd4821 := rd4820.swap1 (by native_decide) (by evm_ov)
  have rd4822 := rd4821.dup7 (by native_decide) (by evm_ov)
  have rd4825 := rd4822.push2 ⟨6653⟩ (by native_decide) (by evm_ov)
  have rd6653 := rd4825.jump (by native_decide) (by jump_dest) (by evm_ov)
  obtain ⟨_, _, rd4826⟩ := RD.vatSignedAddOk
    (x := dstInkOld) (y := forkDinkWord I) (ret := ⟨4826⟩)
    (R := forkIlkBase I :: forkDstUrnBase I :: forkSrcUrnBase I ::
      forkDartWord I :: forkDinkWord I :: forkDstMaskedWord I ::
      forkSrcMaskedWord I :: forkIlkWord I :: ⟨524⟩ :: sel :: [])
    rd6653
    (by simpa [dstInkOld, σSrcArt, σSrcInk] using hneg)
    (by simpa [dstInkOld, σSrcArt, σSrcInk] using hpos)
    (by jump_dest) (by simp)
  exact ⟨_, _, by
    simpa [dstInkOld, σSrcArt, σSrcInk] using rd4826⟩

theorem RD.vatForkDstInkAddRevert
    {cA gh bl σ σ₀ A I} {g : Sat256} {k C : ℕ}
    {sel srcInkNew srcArtNew : UInt256} {mem : ByteArray}
    (h : RD vatBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4809⟩
      [srcArtNew, forkIlkBase I, forkDstUrnBase I, forkSrcUrnBase I, forkDartWord I,
        forkDinkWord I, forkDstMaskedWord I, forkSrcMaskedWord I, forkIlkWord I,
        ⟨524⟩, sel]
      mem (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ (forkSrcInkSlot I) srcInkNew) k C)
    (hperm : I.perm = true)
    (hfail :
      ¬ (UInt256.slt (forkDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.gt
          (forkDinkWord I +
            solcSlotWord
              (sstoreAccountMap I.codeOwner
                (sstoreAccountMap I.codeOwner σ (forkSrcInkSlot I) srcInkNew)
                (forkSrcArtSlot I) srcArtNew)
              I (forkDstInkSlot I))
          (solcSlotWord
            (sstoreAccountMap I.codeOwner
              (sstoreAccountMap I.codeOwner σ (forkSrcInkSlot I) srcInkNew)
              (forkSrcArtSlot I) srcArtNew)
            I (forkDstInkSlot I)) = ⟨0⟩) ∨
      (UInt256.slt (forkDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.gt
          (forkDinkWord I +
            solcSlotWord
              (sstoreAccountMap I.codeOwner
                (sstoreAccountMap I.codeOwner σ (forkSrcInkSlot I) srcInkNew)
                (forkSrcArtSlot I) srcArtNew)
              I (forkDstInkSlot I))
          (solcSlotWord
            (sstoreAccountMap I.codeOwner
              (sstoreAccountMap I.codeOwner σ (forkSrcInkSlot I) srcInkNew)
              (forkSrcArtSlot I) srcArtNew)
            I (forkDstInkSlot I)) = ⟨0⟩) ∧
        ¬ (UInt256.sgt (forkDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
          UInt256.lt
            (forkDinkWord I +
              solcSlotWord
                (sstoreAccountMap I.codeOwner
                  (sstoreAccountMap I.codeOwner σ (forkSrcInkSlot I) srcInkNew)
                  (forkSrcArtSlot I) srcArtNew)
                I (forkDstInkSlot I))
            (solcSlotWord
              (sstoreAccountMap I.codeOwner
                (sstoreAccountMap I.codeOwner σ (forkSrcInkSlot I) srcInkNew)
                (forkSrcArtSlot I) srcArtNew)
              I (forkDstInkSlot I)) = ⟨0⟩)) :
    RDrev vatBytecode g (initState cA gh bl σ σ₀ g A I) := by
  let srcBase := forkSrcUrnBase I
  let dstBase := forkDstUrnBase I
  let σSrcInk := sstoreAccountMap I.codeOwner σ (forkSrcInkSlot I) srcInkNew
  let σSrcArt := sstoreAccountMap I.codeOwner σSrcInk (forkSrcArtSlot I) srcArtNew
  let dstInkOld := solcSlotWord σSrcArt I (forkDstInkSlot I)
  have rd4810 := h.jumpdest (by native_decide) (by evm_ov)
  have rd4812 := rd4810.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  have rd4813pre := rd4812.dup5 (by native_decide) (by evm_ov)
  have rd4814pre := rd4813pre.add (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd4815raw⟩ := rd4814pre.sstore hperm (by native_decide) (by evm_ov)
  have hrd4815 :
      ∃ k' C', RD vatBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4815⟩
        [forkIlkBase I, forkDstUrnBase I, forkSrcUrnBase I, forkDartWord I,
          forkDinkWord I, forkDstMaskedWord I, forkSrcMaskedWord I, forkIlkWord I,
          ⟨524⟩, sel]
        mem (UInt256.ofNat 3) ByteArray.empty (cA, σSrcArt) k' C' := by
    exact ⟨_, _, by
      simpa [σSrcArt, σSrcInk, srcBase, forkSrcArtSlot, forkSrcInkSlot] using rd4815raw⟩
  obtain ⟨_, _, rd4815⟩ := hrd4815
  have rd4816pre := rd4815.dup2 (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd4817raw⟩ := rd4816pre.sload (by native_decide) (by evm_ov)
  have hold :
      (σSrcArt.find? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD dstBase ⟨0⟩)) = dstInkOld := by
    simp [dstInkOld, solcSlotWord, σSrcArt, dstBase, forkDstInkSlot]
  have rd4817 := rd4817raw
  rw [hold] at rd4817
  have rd4820 := rd4817.push2 ⟨4826⟩ (by native_decide) (by evm_ov)
  have rd4821 := rd4820.swap1 (by native_decide) (by evm_ov)
  have rd4822 := rd4821.dup7 (by native_decide) (by evm_ov)
  have rd4825 := rd4822.push2 ⟨6653⟩ (by native_decide) (by evm_ov)
  have rd6653 := rd4825.jump (by native_decide) (by jump_dest) (by evm_ov)
  exact RD.vatSignedAddRevert
    (x := dstInkOld) (y := forkDinkWord I) (ret := ⟨4826⟩)
    (R := forkIlkBase I :: forkDstUrnBase I :: forkSrcUrnBase I ::
      forkDartWord I :: forkDinkWord I :: forkDstMaskedWord I ::
      forkSrcMaskedWord I :: forkIlkWord I :: ⟨524⟩ :: sel :: [])
    rd6653
    (by simpa [dstInkOld, σSrcArt, σSrcInk] using hfail)
    (by simp)

theorem RD.vatForkDstArtAddSuccess
    {cA gh bl σ σ₀ A I} {g : Sat256} {k C : ℕ}
    {sel srcInkNew srcArtNew dstInkNew : UInt256} {mem : ByteArray}
    (h : RD vatBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4826⟩
      [dstInkNew, forkIlkBase I, forkDstUrnBase I, forkSrcUrnBase I, forkDartWord I,
        forkDinkWord I, forkDstMaskedWord I, forkSrcMaskedWord I, forkIlkWord I,
        ⟨524⟩, sel]
      mem (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner σ (forkSrcInkSlot I) srcInkNew)
        (forkSrcArtSlot I) srcArtNew) k C)
    (hperm : I.perm = true)
    (hneg :
      UInt256.slt (forkDartWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.gt
          (forkDartWord I +
            solcSlotWord
              (sstoreAccountMap I.codeOwner
                (sstoreAccountMap I.codeOwner
                  (sstoreAccountMap I.codeOwner σ (forkSrcInkSlot I) srcInkNew)
                  (forkSrcArtSlot I) srcArtNew)
                (forkDstInkSlot I) dstInkNew)
              I (forkDstArtSlot I))
          (solcSlotWord
            (sstoreAccountMap I.codeOwner
              (sstoreAccountMap I.codeOwner
                (sstoreAccountMap I.codeOwner σ (forkSrcInkSlot I) srcInkNew)
                (forkSrcArtSlot I) srcArtNew)
              (forkDstInkSlot I) dstInkNew)
            I (forkDstArtSlot I)) = ⟨0⟩)
    (hpos :
      UInt256.sgt (forkDartWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.lt
          (forkDartWord I +
            solcSlotWord
              (sstoreAccountMap I.codeOwner
                (sstoreAccountMap I.codeOwner
                  (sstoreAccountMap I.codeOwner σ (forkSrcInkSlot I) srcInkNew)
                  (forkSrcArtSlot I) srcArtNew)
                (forkDstInkSlot I) dstInkNew)
              I (forkDstArtSlot I))
          (solcSlotWord
            (sstoreAccountMap I.codeOwner
              (sstoreAccountMap I.codeOwner
                (sstoreAccountMap I.codeOwner σ (forkSrcInkSlot I) srcInkNew)
                (forkSrcArtSlot I) srcArtNew)
              (forkDstInkSlot I) dstInkNew)
            I (forkDstArtSlot I)) = ⟨0⟩) :
    ∃ k' C', RD vatBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4843⟩
      [forkDartWord I +
          solcSlotWord
            (sstoreAccountMap I.codeOwner
              (sstoreAccountMap I.codeOwner
                (sstoreAccountMap I.codeOwner σ (forkSrcInkSlot I) srcInkNew)
                (forkSrcArtSlot I) srcArtNew)
              (forkDstInkSlot I) dstInkNew)
            I (forkDstArtSlot I),
        forkIlkBase I, forkDstUrnBase I, forkSrcUrnBase I, forkDartWord I,
        forkDinkWord I, forkDstMaskedWord I, forkSrcMaskedWord I, forkIlkWord I,
        ⟨524⟩, sel]
      mem (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner σ (forkSrcInkSlot I) srcInkNew)
          (forkSrcArtSlot I) srcArtNew)
        (forkDstInkSlot I) dstInkNew) k' C' := by
  let dstBase := forkDstUrnBase I
  let σSrcInk := sstoreAccountMap I.codeOwner σ (forkSrcInkSlot I) srcInkNew
  let σSrcArt := sstoreAccountMap I.codeOwner σSrcInk (forkSrcArtSlot I) srcArtNew
  let σDstInk := sstoreAccountMap I.codeOwner σSrcArt (forkDstInkSlot I) dstInkNew
  let dstArtOld := solcSlotWord σDstInk I (forkDstArtSlot I)
  have rd4827 := h.jumpdest (by native_decide) (by evm_ov)
  have rd4828pre := rd4827.dup3 (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd4829raw⟩ := rd4828pre.sstore hperm (by native_decide) (by evm_ov)
  have hrd4829 :
      ∃ k' C', RD vatBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4829⟩
        [forkIlkBase I, forkDstUrnBase I, forkSrcUrnBase I, forkDartWord I,
          forkDinkWord I, forkDstMaskedWord I, forkSrcMaskedWord I, forkIlkWord I,
          ⟨524⟩, sel]
        mem (UInt256.ofNat 3) ByteArray.empty (cA, σDstInk) k' C' := by
    exact ⟨_, _, by
      simpa [σDstInk, σSrcArt, σSrcInk, forkDstInkSlot] using rd4829raw⟩
  obtain ⟨_, _, rd4829⟩ := hrd4829
  have rd4831 := rd4829.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  have rd4832pre := rd4831.dup3 (by native_decide) (by evm_ov)
  have rd4833pre := rd4832pre.add (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd4834raw⟩ := rd4833pre.sload (by native_decide) (by evm_ov)
  have hold :
      (σDstInk.find? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD (dstBase + ⟨1⟩) ⟨0⟩)) = dstArtOld := by
    simp [dstArtOld, solcSlotWord, σDstInk, dstBase, forkDstArtSlot]
  have rd4834 := rd4834raw
  rw [hold] at rd4834
  have rd4837 := rd4834.push2 ⟨4843⟩ (by native_decide) (by evm_ov)
  have rd4838 := rd4837.swap1 (by native_decide) (by evm_ov)
  have rd4839 := rd4838.dup6 (by native_decide) (by evm_ov)
  have rd4842 := rd4839.push2 ⟨6653⟩ (by native_decide) (by evm_ov)
  have rd6653 := rd4842.jump (by native_decide) (by jump_dest) (by evm_ov)
  obtain ⟨_, _, rd4843⟩ := RD.vatSignedAddOk
    (x := dstArtOld) (y := forkDartWord I) (ret := ⟨4843⟩)
    (R := forkIlkBase I :: forkDstUrnBase I :: forkSrcUrnBase I ::
      forkDartWord I :: forkDinkWord I :: forkDstMaskedWord I ::
      forkSrcMaskedWord I :: forkIlkWord I :: ⟨524⟩ :: sel :: [])
    rd6653
    (by simpa [dstArtOld, σDstInk, σSrcArt, σSrcInk] using hneg)
    (by simpa [dstArtOld, σDstInk, σSrcArt, σSrcInk] using hpos)
    (by jump_dest) (by simp)
  exact ⟨_, _, by
    simpa [dstArtOld, σDstInk, σSrcArt, σSrcInk] using rd4843⟩

theorem RD.vatForkDstArtAddRevert
    {cA gh bl σ σ₀ A I} {g : Sat256} {k C : ℕ}
    {sel srcInkNew srcArtNew dstInkNew : UInt256} {mem : ByteArray}
    (h : RD vatBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4826⟩
      [dstInkNew, forkIlkBase I, forkDstUrnBase I, forkSrcUrnBase I, forkDartWord I,
        forkDinkWord I, forkDstMaskedWord I, forkSrcMaskedWord I, forkIlkWord I,
        ⟨524⟩, sel]
      mem (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner σ (forkSrcInkSlot I) srcInkNew)
        (forkSrcArtSlot I) srcArtNew) k C)
    (hperm : I.perm = true)
    (hfail :
      ¬ (UInt256.slt (forkDartWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.gt
          (forkDartWord I +
            solcSlotWord
              (sstoreAccountMap I.codeOwner
                (sstoreAccountMap I.codeOwner
                  (sstoreAccountMap I.codeOwner σ (forkSrcInkSlot I) srcInkNew)
                  (forkSrcArtSlot I) srcArtNew)
                (forkDstInkSlot I) dstInkNew)
              I (forkDstArtSlot I))
          (solcSlotWord
            (sstoreAccountMap I.codeOwner
              (sstoreAccountMap I.codeOwner
                (sstoreAccountMap I.codeOwner σ (forkSrcInkSlot I) srcInkNew)
                (forkSrcArtSlot I) srcArtNew)
              (forkDstInkSlot I) dstInkNew)
            I (forkDstArtSlot I)) = ⟨0⟩) ∨
      (UInt256.slt (forkDartWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.gt
          (forkDartWord I +
            solcSlotWord
              (sstoreAccountMap I.codeOwner
                (sstoreAccountMap I.codeOwner
                  (sstoreAccountMap I.codeOwner σ (forkSrcInkSlot I) srcInkNew)
                  (forkSrcArtSlot I) srcArtNew)
                (forkDstInkSlot I) dstInkNew)
              I (forkDstArtSlot I))
          (solcSlotWord
            (sstoreAccountMap I.codeOwner
              (sstoreAccountMap I.codeOwner
                (sstoreAccountMap I.codeOwner σ (forkSrcInkSlot I) srcInkNew)
                (forkSrcArtSlot I) srcArtNew)
              (forkDstInkSlot I) dstInkNew)
            I (forkDstArtSlot I)) = ⟨0⟩) ∧
        ¬ (UInt256.sgt (forkDartWord I) ⟨0⟩ = ⟨0⟩ ∨
          UInt256.lt
            (forkDartWord I +
              solcSlotWord
                (sstoreAccountMap I.codeOwner
                  (sstoreAccountMap I.codeOwner
                    (sstoreAccountMap I.codeOwner σ (forkSrcInkSlot I) srcInkNew)
                    (forkSrcArtSlot I) srcArtNew)
                  (forkDstInkSlot I) dstInkNew)
                I (forkDstArtSlot I))
            (solcSlotWord
              (sstoreAccountMap I.codeOwner
                (sstoreAccountMap I.codeOwner
                  (sstoreAccountMap I.codeOwner σ (forkSrcInkSlot I) srcInkNew)
                  (forkSrcArtSlot I) srcArtNew)
                (forkDstInkSlot I) dstInkNew)
              I (forkDstArtSlot I)) = ⟨0⟩)) :
    RDrev vatBytecode g (initState cA gh bl σ σ₀ g A I) := by
  let dstBase := forkDstUrnBase I
  let σSrcInk := sstoreAccountMap I.codeOwner σ (forkSrcInkSlot I) srcInkNew
  let σSrcArt := sstoreAccountMap I.codeOwner σSrcInk (forkSrcArtSlot I) srcArtNew
  let σDstInk := sstoreAccountMap I.codeOwner σSrcArt (forkDstInkSlot I) dstInkNew
  let dstArtOld := solcSlotWord σDstInk I (forkDstArtSlot I)
  have rd4827 := h.jumpdest (by native_decide) (by evm_ov)
  have rd4828pre := rd4827.dup3 (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd4829raw⟩ := rd4828pre.sstore hperm (by native_decide) (by evm_ov)
  have hrd4829 :
      ∃ k' C', RD vatBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4829⟩
        [forkIlkBase I, forkDstUrnBase I, forkSrcUrnBase I, forkDartWord I,
          forkDinkWord I, forkDstMaskedWord I, forkSrcMaskedWord I, forkIlkWord I,
          ⟨524⟩, sel]
        mem (UInt256.ofNat 3) ByteArray.empty (cA, σDstInk) k' C' := by
    exact ⟨_, _, by
      simpa [σDstInk, σSrcArt, σSrcInk, forkDstInkSlot] using rd4829raw⟩
  obtain ⟨_, _, rd4829⟩ := hrd4829
  have rd4831 := rd4829.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  have rd4832pre := rd4831.dup3 (by native_decide) (by evm_ov)
  have rd4833pre := rd4832pre.add (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd4834raw⟩ := rd4833pre.sload (by native_decide) (by evm_ov)
  have hold :
      (σDstInk.find? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD (dstBase + ⟨1⟩) ⟨0⟩)) = dstArtOld := by
    simp [dstArtOld, solcSlotWord, σDstInk, dstBase, forkDstArtSlot]
  have rd4834 := rd4834raw
  rw [hold] at rd4834
  have rd4837 := rd4834.push2 ⟨4843⟩ (by native_decide) (by evm_ov)
  have rd4838 := rd4837.swap1 (by native_decide) (by evm_ov)
  have rd4839 := rd4838.dup6 (by native_decide) (by evm_ov)
  have rd4842 := rd4839.push2 ⟨6653⟩ (by native_decide) (by evm_ov)
  have rd6653 := rd4842.jump (by native_decide) (by jump_dest) (by evm_ov)
  exact RD.vatSignedAddRevert
    (x := dstArtOld) (y := forkDartWord I) (ret := ⟨4843⟩)
    (R := forkIlkBase I :: forkDstUrnBase I :: forkSrcUrnBase I ::
      forkDartWord I :: forkDinkWord I :: forkDstMaskedWord I ::
      forkSrcMaskedWord I :: forkIlkWord I :: ⟨524⟩ :: sel :: [])
    rd6653
    (by simpa [dstArtOld, σDstInk, σSrcArt, σSrcInk] using hfail)
    (by simp)

theorem RD.vatForkUtabMulSuccess
    {cA gh bl σ σ₀ A I} {g : Sat256} {k C : ℕ}
    {sel srcInkNew srcArtNew dstInkNew dstArtNew : UInt256} {mem : ByteArray}
    (h : RD vatBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4843⟩
      [dstArtNew, forkIlkBase I, forkDstUrnBase I, forkSrcUrnBase I, forkDartWord I,
        forkDinkWord I, forkDstMaskedWord I, forkSrcMaskedWord I, forkIlkWord I,
        ⟨524⟩, sel]
      mem (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner σ (forkSrcInkSlot I) srcInkNew)
          (forkSrcArtSlot I) srcArtNew)
        (forkDstInkSlot I) dstInkNew) k C)
    (hperm : I.perm = true)
    (hok :
      solcSlotWord
          (sstoreAccountMap I.codeOwner
            (sstoreAccountMap I.codeOwner
              (sstoreAccountMap I.codeOwner
                (sstoreAccountMap I.codeOwner σ (forkSrcInkSlot I) srcInkNew)
                (forkSrcArtSlot I) srcArtNew)
              (forkDstInkSlot I) dstInkNew)
            (forkDstArtSlot I) dstArtNew)
          I (forkIlkRateSlot I) = ⟨0⟩ ∨
        UInt256.eq
          (UInt256.div
            (UInt256.mul
              (solcSlotWord
                (sstoreAccountMap I.codeOwner
                  (sstoreAccountMap I.codeOwner
                    (sstoreAccountMap I.codeOwner
                      (sstoreAccountMap I.codeOwner σ (forkSrcInkSlot I) srcInkNew)
                      (forkSrcArtSlot I) srcArtNew)
                    (forkDstInkSlot I) dstInkNew)
                  (forkDstArtSlot I) dstArtNew)
                I (forkSrcArtSlot I))
              (solcSlotWord
                (sstoreAccountMap I.codeOwner
                  (sstoreAccountMap I.codeOwner
                    (sstoreAccountMap I.codeOwner
                      (sstoreAccountMap I.codeOwner σ (forkSrcInkSlot I) srcInkNew)
                      (forkSrcArtSlot I) srcArtNew)
                    (forkDstInkSlot I) dstInkNew)
                  (forkDstArtSlot I) dstArtNew)
                I (forkIlkRateSlot I)))
            (solcSlotWord
              (sstoreAccountMap I.codeOwner
                (sstoreAccountMap I.codeOwner
                  (sstoreAccountMap I.codeOwner
                    (sstoreAccountMap I.codeOwner σ (forkSrcInkSlot I) srcInkNew)
                    (forkSrcArtSlot I) srcArtNew)
                  (forkDstInkSlot I) dstInkNew)
                (forkDstArtSlot I) dstArtNew)
              I (forkIlkRateSlot I)))
          (solcSlotWord
            (sstoreAccountMap I.codeOwner
              (sstoreAccountMap I.codeOwner
                (sstoreAccountMap I.codeOwner
                  (sstoreAccountMap I.codeOwner σ (forkSrcInkSlot I) srcInkNew)
                  (forkSrcArtSlot I) srcArtNew)
                (forkDstInkSlot I) dstInkNew)
              (forkDstArtSlot I) dstArtNew)
            I (forkSrcArtSlot I)) ≠ ⟨0⟩) :
    ∃ k' C', RD vatBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4871⟩
      [UInt256.mul
          (solcSlotWord
            (sstoreAccountMap I.codeOwner
              (sstoreAccountMap I.codeOwner
                (sstoreAccountMap I.codeOwner
                  (sstoreAccountMap I.codeOwner σ (forkSrcInkSlot I) srcInkNew)
                  (forkSrcArtSlot I) srcArtNew)
                (forkDstInkSlot I) dstInkNew)
              (forkDstArtSlot I) dstArtNew)
            I (forkSrcArtSlot I))
          (solcSlotWord
            (sstoreAccountMap I.codeOwner
              (sstoreAccountMap I.codeOwner
                (sstoreAccountMap I.codeOwner
                  (sstoreAccountMap I.codeOwner σ (forkSrcInkSlot I) srcInkNew)
                  (forkSrcArtSlot I) srcArtNew)
                (forkDstInkSlot I) dstInkNew)
              (forkDstArtSlot I) dstArtNew)
            I (forkIlkRateSlot I)),
        ⟨0⟩, forkIlkBase I, forkDstUrnBase I, forkSrcUrnBase I, forkDartWord I,
        forkDinkWord I, forkDstMaskedWord I, forkSrcMaskedWord I, forkIlkWord I,
        ⟨524⟩, sel]
      mem (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner
            (sstoreAccountMap I.codeOwner σ (forkSrcInkSlot I) srcInkNew)
            (forkSrcArtSlot I) srcArtNew)
          (forkDstInkSlot I) dstInkNew)
        (forkDstArtSlot I) dstArtNew) k' C' := by
  let srcBase := forkSrcUrnBase I
  let dstBase := forkDstUrnBase I
  let ilkBase := forkIlkBase I
  let σSrcInk := sstoreAccountMap I.codeOwner σ (forkSrcInkSlot I) srcInkNew
  let σSrcArt := sstoreAccountMap I.codeOwner σSrcInk (forkSrcArtSlot I) srcArtNew
  let σDstInk := sstoreAccountMap I.codeOwner σSrcArt (forkDstInkSlot I) dstInkNew
  let σDstArt := sstoreAccountMap I.codeOwner σDstInk (forkDstArtSlot I) dstArtNew
  let srcArtFinal := solcSlotWord σDstArt I (forkSrcArtSlot I)
  let rate := solcSlotWord σDstArt I (forkIlkRateSlot I)
  have rd4844 := h.jumpdest (by native_decide) (by evm_ov)
  have rd4845 := rd4844.dup3 (by native_decide) (by evm_ov)
  have rd4847 := rd4845.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  have rd4848pre := rd4847.add (by native_decide) (by evm_ov)
  have rd4849 := rd4848pre.dup2 (by native_decide) (by evm_ov)
  have rd4850pre := rd4849.swap1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd4851raw⟩ := rd4850pre.sstore hperm (by native_decide) (by evm_ov)
  have hrd4851 :
      ∃ k' C', RD vatBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4851⟩
        [dstArtNew, forkIlkBase I, forkDstUrnBase I, forkSrcUrnBase I, forkDartWord I,
          forkDinkWord I, forkDstMaskedWord I, forkSrcMaskedWord I, forkIlkWord I,
          ⟨524⟩, sel]
        mem (UInt256.ofNat 3) ByteArray.empty (cA, σDstArt) k' C' := by
    exact ⟨_, _, by
      simpa [σDstArt, σDstInk, σSrcArt, σSrcInk, dstBase, forkDstArtSlot,
        forkDstInkSlot, u256_add_comm (⟨1⟩ : UInt256) dstBase] using rd4851raw⟩
  obtain ⟨_, _, rd4851⟩ := hrd4851
  have rd4852 := rd4851.pop (by native_decide) (by evm_ov)
  have rd4854 := rd4852.push1 ⟨0⟩ (by native_decide) (by evm_ov)
  have rd4857 := rd4854.push2 ⟨4871⟩ (by native_decide) (by evm_ov)
  have rd4858 := rd4857.dup5 (by native_decide) (by evm_ov)
  have rd4860 := rd4858.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  have rd4861pre := rd4860.add (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd4862raw⟩ := rd4861pre.sload (by native_decide) (by evm_ov)
  have hsrcArt :
      (σDstArt.find? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD (⟨1⟩ + srcBase) ⟨0⟩)) = srcArtFinal := by
    rw [u256_add_comm (⟨1⟩ : UInt256) srcBase]
    simp [srcArtFinal, solcSlotWord, σDstArt, srcBase, forkSrcArtSlot]
  have rd4862 := rd4862raw
  rw [hsrcArt] at rd4862
  have rd4863 := rd4862.dup4 (by native_decide) (by evm_ov)
  have rd4865 := rd4863.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  have rd4866pre := rd4865.add (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd4867raw⟩ := rd4866pre.sload (by native_decide) (by evm_ov)
  have hrate :
      (σDstArt.find? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD (⟨1⟩ + ilkBase) ⟨0⟩)) = rate := by
    rw [u256_add_comm (⟨1⟩ : UInt256) ilkBase]
    simp [rate, solcSlotWord, σDstArt, ilkBase, forkIlkRateSlot]
  have rd4867 := rd4867raw
  rw [hrate] at rd4867
  have rd4870 := rd4867.push2 ⟨6752⟩ (by native_decide) (by evm_ov)
  have rd6752 := rd4870.jump (by native_decide) (by jump_dest) (by evm_ov)
  obtain ⟨_, _, rd4871⟩ := RD.vatCheckedMulUintOk
    (x := rate) (y := srcArtFinal) (ret := ⟨4871⟩)
    (R := ⟨0⟩ :: forkIlkBase I :: forkDstUrnBase I :: forkSrcUrnBase I ::
      forkDartWord I :: forkDinkWord I :: forkDstMaskedWord I ::
      forkSrcMaskedWord I :: forkIlkWord I :: ⟨524⟩ :: sel :: [])
    rd6752
    (by simpa [rate, srcArtFinal, σDstArt, σDstInk, σSrcArt, σSrcInk] using hok)
    (by jump_dest) (by simp)
  exact ⟨_, _, by
    simpa [rate, srcArtFinal, σDstArt, σDstInk, σSrcArt, σSrcInk] using rd4871⟩

theorem RD.vatForkUtabMulRevert
    {cA gh bl σ σ₀ A I} {g : Sat256} {k C : ℕ}
    {sel srcInkNew srcArtNew dstInkNew dstArtNew : UInt256} {mem : ByteArray}
    (h : RD vatBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4843⟩
      [dstArtNew, forkIlkBase I, forkDstUrnBase I, forkSrcUrnBase I, forkDartWord I,
        forkDinkWord I, forkDstMaskedWord I, forkSrcMaskedWord I, forkIlkWord I,
        ⟨524⟩, sel]
      mem (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner σ (forkSrcInkSlot I) srcInkNew)
          (forkSrcArtSlot I) srcArtNew)
        (forkDstInkSlot I) dstInkNew) k C)
    (hperm : I.perm = true)
    (hfail :
      ¬ (solcSlotWord
          (sstoreAccountMap I.codeOwner
            (sstoreAccountMap I.codeOwner
              (sstoreAccountMap I.codeOwner
                (sstoreAccountMap I.codeOwner σ (forkSrcInkSlot I) srcInkNew)
                (forkSrcArtSlot I) srcArtNew)
              (forkDstInkSlot I) dstInkNew)
            (forkDstArtSlot I) dstArtNew)
          I (forkIlkRateSlot I) = ⟨0⟩ ∨
        UInt256.eq
          (UInt256.div
            (UInt256.mul
              (solcSlotWord
                (sstoreAccountMap I.codeOwner
                  (sstoreAccountMap I.codeOwner
                    (sstoreAccountMap I.codeOwner
                      (sstoreAccountMap I.codeOwner σ (forkSrcInkSlot I) srcInkNew)
                      (forkSrcArtSlot I) srcArtNew)
                    (forkDstInkSlot I) dstInkNew)
                  (forkDstArtSlot I) dstArtNew)
                I (forkSrcArtSlot I))
              (solcSlotWord
                (sstoreAccountMap I.codeOwner
                  (sstoreAccountMap I.codeOwner
                    (sstoreAccountMap I.codeOwner
                      (sstoreAccountMap I.codeOwner σ (forkSrcInkSlot I) srcInkNew)
                      (forkSrcArtSlot I) srcArtNew)
                    (forkDstInkSlot I) dstInkNew)
                  (forkDstArtSlot I) dstArtNew)
                I (forkIlkRateSlot I)))
            (solcSlotWord
              (sstoreAccountMap I.codeOwner
                (sstoreAccountMap I.codeOwner
                  (sstoreAccountMap I.codeOwner
                    (sstoreAccountMap I.codeOwner σ (forkSrcInkSlot I) srcInkNew)
                    (forkSrcArtSlot I) srcArtNew)
                  (forkDstInkSlot I) dstInkNew)
                (forkDstArtSlot I) dstArtNew)
              I (forkIlkRateSlot I)))
          (solcSlotWord
            (sstoreAccountMap I.codeOwner
              (sstoreAccountMap I.codeOwner
                (sstoreAccountMap I.codeOwner
                  (sstoreAccountMap I.codeOwner σ (forkSrcInkSlot I) srcInkNew)
                  (forkSrcArtSlot I) srcArtNew)
                (forkDstInkSlot I) dstInkNew)
              (forkDstArtSlot I) dstArtNew)
            I (forkSrcArtSlot I)) ≠ ⟨0⟩)) :
    RDrev vatBytecode g (initState cA gh bl σ σ₀ g A I) := by
  let srcBase := forkSrcUrnBase I
  let dstBase := forkDstUrnBase I
  let ilkBase := forkIlkBase I
  let σSrcInk := sstoreAccountMap I.codeOwner σ (forkSrcInkSlot I) srcInkNew
  let σSrcArt := sstoreAccountMap I.codeOwner σSrcInk (forkSrcArtSlot I) srcArtNew
  let σDstInk := sstoreAccountMap I.codeOwner σSrcArt (forkDstInkSlot I) dstInkNew
  let σDstArt := sstoreAccountMap I.codeOwner σDstInk (forkDstArtSlot I) dstArtNew
  let srcArtFinal := solcSlotWord σDstArt I (forkSrcArtSlot I)
  let rate := solcSlotWord σDstArt I (forkIlkRateSlot I)
  have rd4844 := h.jumpdest (by native_decide) (by evm_ov)
  have rd4845 := rd4844.dup3 (by native_decide) (by evm_ov)
  have rd4847 := rd4845.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  have rd4848pre := rd4847.add (by native_decide) (by evm_ov)
  have rd4849 := rd4848pre.dup2 (by native_decide) (by evm_ov)
  have rd4850pre := rd4849.swap1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd4851raw⟩ := rd4850pre.sstore hperm (by native_decide) (by evm_ov)
  have hrd4851 :
      ∃ k' C', RD vatBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4851⟩
        [dstArtNew, forkIlkBase I, forkDstUrnBase I, forkSrcUrnBase I, forkDartWord I,
          forkDinkWord I, forkDstMaskedWord I, forkSrcMaskedWord I, forkIlkWord I,
          ⟨524⟩, sel]
        mem (UInt256.ofNat 3) ByteArray.empty (cA, σDstArt) k' C' := by
    exact ⟨_, _, by
      simpa [σDstArt, σDstInk, σSrcArt, σSrcInk, dstBase, forkDstArtSlot,
        forkDstInkSlot, u256_add_comm (⟨1⟩ : UInt256) dstBase] using rd4851raw⟩
  obtain ⟨_, _, rd4851⟩ := hrd4851
  have rd4852 := rd4851.pop (by native_decide) (by evm_ov)
  have rd4854 := rd4852.push1 ⟨0⟩ (by native_decide) (by evm_ov)
  have rd4857 := rd4854.push2 ⟨4871⟩ (by native_decide) (by evm_ov)
  have rd4858 := rd4857.dup5 (by native_decide) (by evm_ov)
  have rd4860 := rd4858.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  have rd4861pre := rd4860.add (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd4862raw⟩ := rd4861pre.sload (by native_decide) (by evm_ov)
  have hsrcArt :
      (σDstArt.find? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD (⟨1⟩ + srcBase) ⟨0⟩)) = srcArtFinal := by
    rw [u256_add_comm (⟨1⟩ : UInt256) srcBase]
    simp [srcArtFinal, solcSlotWord, σDstArt, srcBase, forkSrcArtSlot]
  have rd4862 := rd4862raw
  rw [hsrcArt] at rd4862
  have rd4863 := rd4862.dup4 (by native_decide) (by evm_ov)
  have rd4865 := rd4863.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  have rd4866pre := rd4865.add (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd4867raw⟩ := rd4866pre.sload (by native_decide) (by evm_ov)
  have hrate :
      (σDstArt.find? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD (⟨1⟩ + ilkBase) ⟨0⟩)) = rate := by
    rw [u256_add_comm (⟨1⟩ : UInt256) ilkBase]
    simp [rate, solcSlotWord, σDstArt, ilkBase, forkIlkRateSlot]
  have rd4867 := rd4867raw
  rw [hrate] at rd4867
  have rd4870 := rd4867.push2 ⟨6752⟩ (by native_decide) (by evm_ov)
  have rd6752 := rd4870.jump (by native_decide) (by jump_dest) (by evm_ov)
  exact RD.vatCheckedMulUintRevert
    (x := rate) (y := srcArtFinal) (ret := ⟨4871⟩)
    (R := ⟨0⟩ :: forkIlkBase I :: forkDstUrnBase I :: forkSrcUrnBase I ::
      forkDartWord I :: forkDinkWord I :: forkDstMaskedWord I ::
      forkSrcMaskedWord I :: forkIlkWord I :: ⟨524⟩ :: sel :: [])
    rd6752
    (by simpa [rate, srcArtFinal, σDstArt, σDstInk, σSrcArt, σSrcInk] using hfail)
    (by simp)

theorem RD.vatForkVtabMulSuccess
    {cA gh bl σ σ₀ A I} {g : Sat256} {k C : ℕ}
    {sel srcInkNew srcArtNew dstInkNew dstArtNew utab : UInt256} {mem : ByteArray}
    (h : RD vatBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4871⟩
      [utab, ⟨0⟩, forkIlkBase I, forkDstUrnBase I, forkSrcUrnBase I,
        forkDartWord I, forkDinkWord I, forkDstMaskedWord I, forkSrcMaskedWord I,
        forkIlkWord I, ⟨524⟩, sel]
      mem (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner
            (sstoreAccountMap I.codeOwner σ (forkSrcInkSlot I) srcInkNew)
            (forkSrcArtSlot I) srcArtNew)
          (forkDstInkSlot I) dstInkNew)
        (forkDstArtSlot I) dstArtNew) k C)
    (hok :
      solcSlotWord
          (sstoreAccountMap I.codeOwner
            (sstoreAccountMap I.codeOwner
              (sstoreAccountMap I.codeOwner
                (sstoreAccountMap I.codeOwner σ (forkSrcInkSlot I) srcInkNew)
                (forkSrcArtSlot I) srcArtNew)
              (forkDstInkSlot I) dstInkNew)
            (forkDstArtSlot I) dstArtNew)
          I (forkIlkRateSlot I) = ⟨0⟩ ∨
        UInt256.eq
          (UInt256.div
            (UInt256.mul
              (solcSlotWord
                (sstoreAccountMap I.codeOwner
                  (sstoreAccountMap I.codeOwner
                    (sstoreAccountMap I.codeOwner
                      (sstoreAccountMap I.codeOwner σ (forkSrcInkSlot I) srcInkNew)
                      (forkSrcArtSlot I) srcArtNew)
                    (forkDstInkSlot I) dstInkNew)
                  (forkDstArtSlot I) dstArtNew)
                I (forkDstArtSlot I))
              (solcSlotWord
                (sstoreAccountMap I.codeOwner
                  (sstoreAccountMap I.codeOwner
                    (sstoreAccountMap I.codeOwner
                      (sstoreAccountMap I.codeOwner σ (forkSrcInkSlot I) srcInkNew)
                      (forkSrcArtSlot I) srcArtNew)
                    (forkDstInkSlot I) dstInkNew)
                  (forkDstArtSlot I) dstArtNew)
                I (forkIlkRateSlot I)))
            (solcSlotWord
              (sstoreAccountMap I.codeOwner
                (sstoreAccountMap I.codeOwner
                  (sstoreAccountMap I.codeOwner
                    (sstoreAccountMap I.codeOwner σ (forkSrcInkSlot I) srcInkNew)
                    (forkSrcArtSlot I) srcArtNew)
                  (forkDstInkSlot I) dstInkNew)
                (forkDstArtSlot I) dstArtNew)
              I (forkIlkRateSlot I)))
          (solcSlotWord
            (sstoreAccountMap I.codeOwner
              (sstoreAccountMap I.codeOwner
                (sstoreAccountMap I.codeOwner
                  (sstoreAccountMap I.codeOwner σ (forkSrcInkSlot I) srcInkNew)
                  (forkSrcArtSlot I) srcArtNew)
                (forkDstInkSlot I) dstInkNew)
              (forkDstArtSlot I) dstArtNew)
            I (forkDstArtSlot I)) ≠ ⟨0⟩) :
    ∃ k' C', RD vatBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4893⟩
      [UInt256.mul
          (solcSlotWord
            (sstoreAccountMap I.codeOwner
              (sstoreAccountMap I.codeOwner
                (sstoreAccountMap I.codeOwner
                  (sstoreAccountMap I.codeOwner σ (forkSrcInkSlot I) srcInkNew)
                  (forkSrcArtSlot I) srcArtNew)
                (forkDstInkSlot I) dstInkNew)
              (forkDstArtSlot I) dstArtNew)
            I (forkDstArtSlot I))
          (solcSlotWord
            (sstoreAccountMap I.codeOwner
              (sstoreAccountMap I.codeOwner
                (sstoreAccountMap I.codeOwner
                  (sstoreAccountMap I.codeOwner σ (forkSrcInkSlot I) srcInkNew)
                  (forkSrcArtSlot I) srcArtNew)
                (forkDstInkSlot I) dstInkNew)
              (forkDstArtSlot I) dstArtNew)
            I (forkIlkRateSlot I)),
        ⟨0⟩, utab, forkIlkBase I, forkDstUrnBase I, forkSrcUrnBase I,
        forkDartWord I, forkDinkWord I, forkDstMaskedWord I, forkSrcMaskedWord I,
        forkIlkWord I, ⟨524⟩, sel]
      mem (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner
            (sstoreAccountMap I.codeOwner σ (forkSrcInkSlot I) srcInkNew)
            (forkSrcArtSlot I) srcArtNew)
          (forkDstInkSlot I) dstInkNew)
        (forkDstArtSlot I) dstArtNew) k' C' := by
  let dstBase := forkDstUrnBase I
  let ilkBase := forkIlkBase I
  let σSrcInk := sstoreAccountMap I.codeOwner σ (forkSrcInkSlot I) srcInkNew
  let σSrcArt := sstoreAccountMap I.codeOwner σSrcInk (forkSrcArtSlot I) srcArtNew
  let σDstInk := sstoreAccountMap I.codeOwner σSrcArt (forkDstInkSlot I) dstInkNew
  let σDstArt := sstoreAccountMap I.codeOwner σDstInk (forkDstArtSlot I) dstArtNew
  let dstArtFinal := solcSlotWord σDstArt I (forkDstArtSlot I)
  let rate := solcSlotWord σDstArt I (forkIlkRateSlot I)
  have rd4872 := h.jumpdest (by native_decide) (by evm_ov)
  have rd4873 := rd4872.swap1 (by native_decide) (by evm_ov)
  have rd4874 := rd4873.pop (by native_decide) (by evm_ov)
  have rd4876 := rd4874.push1 ⟨0⟩ (by native_decide) (by evm_ov)
  have rd4879 := rd4876.push2 ⟨4893⟩ (by native_decide) (by evm_ov)
  have rd4880 := rd4879.dup5 (by native_decide) (by evm_ov)
  have rd4882 := rd4880.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  have rd4883pre := rd4882.add (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd4884raw⟩ := rd4883pre.sload (by native_decide) (by evm_ov)
  have hdstArt :
      (σDstArt.find? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD (⟨1⟩ + dstBase) ⟨0⟩)) = dstArtFinal := by
    rw [u256_add_comm (⟨1⟩ : UInt256) dstBase]
    simp [dstArtFinal, solcSlotWord, σDstArt, dstBase, forkDstArtSlot]
  have rd4884 := rd4884raw
  rw [hdstArt] at rd4884
  have rd4885 := rd4884.dup5 (by native_decide) (by evm_ov)
  have rd4887 := rd4885.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  have rd4888pre := rd4887.add (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd4889raw⟩ := rd4888pre.sload (by native_decide) (by evm_ov)
  have hrate :
      (σDstArt.find? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD (⟨1⟩ + ilkBase) ⟨0⟩)) = rate := by
    rw [u256_add_comm (⟨1⟩ : UInt256) ilkBase]
    simp [rate, solcSlotWord, σDstArt, ilkBase, forkIlkRateSlot]
  have rd4889 := rd4889raw
  rw [hrate] at rd4889
  have rd4892 := rd4889.push2 ⟨6752⟩ (by native_decide) (by evm_ov)
  have rd6752 := rd4892.jump (by native_decide) (by jump_dest) (by evm_ov)
  obtain ⟨_, _, rd4893⟩ := RD.vatCheckedMulUintOk
    (x := rate) (y := dstArtFinal) (ret := ⟨4893⟩)
    (R := ⟨0⟩ :: utab :: forkIlkBase I :: forkDstUrnBase I :: forkSrcUrnBase I ::
      forkDartWord I :: forkDinkWord I :: forkDstMaskedWord I ::
      forkSrcMaskedWord I :: forkIlkWord I :: ⟨524⟩ :: sel :: [])
    rd6752
    (by simpa [rate, dstArtFinal, σDstArt, σDstInk, σSrcArt, σSrcInk] using hok)
    (by jump_dest) (by simp)
  exact ⟨_, _, by
    simpa [rate, dstArtFinal, σDstArt, σDstInk, σSrcArt, σSrcInk] using rd4893⟩

theorem RD.vatForkVtabMulRevert
    {cA gh bl σ σ₀ A I} {g : Sat256} {k C : ℕ}
    {sel srcInkNew srcArtNew dstInkNew dstArtNew utab : UInt256} {mem : ByteArray}
    (h : RD vatBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4871⟩
      [utab, ⟨0⟩, forkIlkBase I, forkDstUrnBase I, forkSrcUrnBase I,
        forkDartWord I, forkDinkWord I, forkDstMaskedWord I, forkSrcMaskedWord I,
        forkIlkWord I, ⟨524⟩, sel]
      mem (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner
            (sstoreAccountMap I.codeOwner σ (forkSrcInkSlot I) srcInkNew)
            (forkSrcArtSlot I) srcArtNew)
          (forkDstInkSlot I) dstInkNew)
        (forkDstArtSlot I) dstArtNew) k C)
    (hfail :
      ¬ (solcSlotWord
          (sstoreAccountMap I.codeOwner
            (sstoreAccountMap I.codeOwner
              (sstoreAccountMap I.codeOwner
                (sstoreAccountMap I.codeOwner σ (forkSrcInkSlot I) srcInkNew)
                (forkSrcArtSlot I) srcArtNew)
              (forkDstInkSlot I) dstInkNew)
            (forkDstArtSlot I) dstArtNew)
          I (forkIlkRateSlot I) = ⟨0⟩ ∨
        UInt256.eq
          (UInt256.div
            (UInt256.mul
              (solcSlotWord
                (sstoreAccountMap I.codeOwner
                  (sstoreAccountMap I.codeOwner
                    (sstoreAccountMap I.codeOwner
                      (sstoreAccountMap I.codeOwner σ (forkSrcInkSlot I) srcInkNew)
                      (forkSrcArtSlot I) srcArtNew)
                    (forkDstInkSlot I) dstInkNew)
                  (forkDstArtSlot I) dstArtNew)
                I (forkDstArtSlot I))
              (solcSlotWord
                (sstoreAccountMap I.codeOwner
                  (sstoreAccountMap I.codeOwner
                    (sstoreAccountMap I.codeOwner
                      (sstoreAccountMap I.codeOwner σ (forkSrcInkSlot I) srcInkNew)
                      (forkSrcArtSlot I) srcArtNew)
                    (forkDstInkSlot I) dstInkNew)
                  (forkDstArtSlot I) dstArtNew)
                I (forkIlkRateSlot I)))
            (solcSlotWord
              (sstoreAccountMap I.codeOwner
                (sstoreAccountMap I.codeOwner
                  (sstoreAccountMap I.codeOwner
                    (sstoreAccountMap I.codeOwner σ (forkSrcInkSlot I) srcInkNew)
                    (forkSrcArtSlot I) srcArtNew)
                  (forkDstInkSlot I) dstInkNew)
                (forkDstArtSlot I) dstArtNew)
              I (forkIlkRateSlot I)))
          (solcSlotWord
            (sstoreAccountMap I.codeOwner
              (sstoreAccountMap I.codeOwner
                (sstoreAccountMap I.codeOwner
                  (sstoreAccountMap I.codeOwner σ (forkSrcInkSlot I) srcInkNew)
                  (forkSrcArtSlot I) srcArtNew)
                (forkDstInkSlot I) dstInkNew)
              (forkDstArtSlot I) dstArtNew)
            I (forkDstArtSlot I)) ≠ ⟨0⟩)) :
    RDrev vatBytecode g (initState cA gh bl σ σ₀ g A I) := by
  let dstBase := forkDstUrnBase I
  let ilkBase := forkIlkBase I
  let σSrcInk := sstoreAccountMap I.codeOwner σ (forkSrcInkSlot I) srcInkNew
  let σSrcArt := sstoreAccountMap I.codeOwner σSrcInk (forkSrcArtSlot I) srcArtNew
  let σDstInk := sstoreAccountMap I.codeOwner σSrcArt (forkDstInkSlot I) dstInkNew
  let σDstArt := sstoreAccountMap I.codeOwner σDstInk (forkDstArtSlot I) dstArtNew
  let dstArtFinal := solcSlotWord σDstArt I (forkDstArtSlot I)
  let rate := solcSlotWord σDstArt I (forkIlkRateSlot I)
  have rd4872 := h.jumpdest (by native_decide) (by evm_ov)
  have rd4873 := rd4872.swap1 (by native_decide) (by evm_ov)
  have rd4874 := rd4873.pop (by native_decide) (by evm_ov)
  have rd4876 := rd4874.push1 ⟨0⟩ (by native_decide) (by evm_ov)
  have rd4879 := rd4876.push2 ⟨4893⟩ (by native_decide) (by evm_ov)
  have rd4880 := rd4879.dup5 (by native_decide) (by evm_ov)
  have rd4882 := rd4880.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  have rd4883pre := rd4882.add (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd4884raw⟩ := rd4883pre.sload (by native_decide) (by evm_ov)
  have hdstArt :
      (σDstArt.find? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD (⟨1⟩ + dstBase) ⟨0⟩)) = dstArtFinal := by
    rw [u256_add_comm (⟨1⟩ : UInt256) dstBase]
    simp [dstArtFinal, solcSlotWord, σDstArt, dstBase, forkDstArtSlot]
  have rd4884 := rd4884raw
  rw [hdstArt] at rd4884
  have rd4885 := rd4884.dup5 (by native_decide) (by evm_ov)
  have rd4887 := rd4885.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  have rd4888pre := rd4887.add (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd4889raw⟩ := rd4888pre.sload (by native_decide) (by evm_ov)
  have hrate :
      (σDstArt.find? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD (⟨1⟩ + ilkBase) ⟨0⟩)) = rate := by
    rw [u256_add_comm (⟨1⟩ : UInt256) ilkBase]
    simp [rate, solcSlotWord, σDstArt, ilkBase, forkIlkRateSlot]
  have rd4889 := rd4889raw
  rw [hrate] at rd4889
  have rd4892 := rd4889.push2 ⟨6752⟩ (by native_decide) (by evm_ov)
  have rd6752 := rd4892.jump (by native_decide) (by jump_dest) (by evm_ov)
  exact RD.vatCheckedMulUintRevert
    (x := rate) (y := dstArtFinal) (ret := ⟨4893⟩)
    (R := ⟨0⟩ :: utab :: forkIlkBase I :: forkDstUrnBase I :: forkSrcUrnBase I ::
      forkDartWord I :: forkDinkWord I :: forkDstMaskedWord I ::
      forkSrcMaskedWord I :: forkIlkWord I :: ⟨524⟩ :: sel :: [])
    rd6752
    (by simpa [rate, dstArtFinal, σDstArt, σDstInk, σSrcArt, σSrcInk] using hfail)
    (by simp)

set_option maxHeartbeats 1000000 in
theorem RD.vatForkWishLoadedAt6557
    {cA gh bl σInit σ σ₀ A I} {g : Sat256} {k C : ℕ}
    {usr slot ret : UInt256} {R : List UInt256} {mem : ByteArray}
    (h : RD vatBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨6557⟩
      (UInt256.ofNat I.source.val :: usr :: ret :: R)
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hmem : mem.size = 96)
    (hclean : UInt256.land solcAddrMask usr = usr)
    (hslot : slot = solcMappingSlot (solcMappingSlot ⟨1⟩ usr) (hopeSourceWord I))
    (hov : R.length + 12 ≤ 1024) :
    ∃ k' C', RD vatBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨6599⟩
      (vatSlotWord slot σ I :: ⟨1⟩ :: ⟨0⟩ :: usr :: hopeSourceWord I ::
        UInt256.ofNat I.source.val :: usr :: ret :: R)
      (twoWordHashMem (hopeSourceWord I) (solcMappingSlot ⟨1⟩ usr)
        (twoWordHashMem usr ⟨1⟩ mem))
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
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
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd6580pre := evm_run rd6573 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd6580 := rd6580pre.mstore 0
    (twoWordHashMem usr ⟨1⟩ mem)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd6585pre := evm_run rd6580 with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw dup5 (by native_decide) (by evm_ov)]
  have hinner :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((twoWordHashMem usr ⟨1⟩ mem)
            |>.readWithPadding 0 64))) =
        solcMappingSlot ⟨1⟩ usr :=
    twoWordHashMem_solcMappingSlot ⟨1⟩ usr hmem
  have rd6585 := rd6585pre.keccak256 0
    (solcMappingSlot ⟨1⟩ usr) (UInt256.ofNat 3)
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
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd6595pre := evm_run rd6591 with [
    raw swap6 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov)]
  have rd6595 := rd6595pre.mstore 0
    (twoWordHashMem (hopeSourceWord I) (solcMappingSlot ⟨1⟩ usr)
      (twoWordHashMem usr ⟨1⟩ mem))
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd6597pre := evm_run rd6595 with [
    raw dup3 (by native_decide) (by evm_ov)]
  have houter :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((twoWordHashMem (hopeSourceWord I)
            (solcMappingSlot ⟨1⟩ usr)
            (twoWordHashMem usr ⟨1⟩ mem)).readWithPadding 0 64))) =
        slot := by
    rw [hslot]
    exact twoWordHashMem_solcMappingSlot (solcMappingSlot ⟨1⟩ usr)
      (hopeSourceWord I)
      (twoWordHashMem_size_96 usr ⟨1⟩ hmem)
  have rd6597 := rd6597pre.keccak256 0 slot (UInt256.ofNat 3)
    (by native_decide) mem_cost houter (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd6599raw⟩ := rd6597.sload (by native_decide) (by evm_ov)
  exact ⟨_, _, by simpa [vatSlotWord, solcSlotWord] using rd6599raw⟩

set_option maxHeartbeats 1000000 in
theorem RD.vatForkWishReturnOk
    {cA gh bl σInit σ σ₀ A I} {g : Sat256} {k C : ℕ}
    {usr slot ret : UInt256} {R : List UInt256} {mem : ByteArray}
    (h : RD vatBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨6599⟩
      (vatSlotWord slot σ I :: ⟨1⟩ :: ⟨0⟩ :: usr :: hopeSourceWord I ::
        UInt256.ofNat I.source.val :: usr :: ret :: R)
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hret : (D_J vatBytecode 0).contains ret = true)
    (hov : R.length + 9 ≤ 1024) :
    ∃ k' C', RD vatBytecode I g (initState cA gh bl σInit σ₀ g A I) ret
      (UInt256.lor
        (UInt256.eq (vatSlotWord slot σ I) ⟨1⟩)
        (UInt256.eq usr (hopeSourceWord I)) :: R)
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
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
  have rd6793 := rd6792.or (by native_decide) (by evm_ov)
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
theorem RD.vatForkWishSuccess
    {cA gh bl σInit σ σ₀ A I} {g : Sat256} {k C : ℕ}
    {sel utab vtab : UInt256} {mem : ByteArray}
    (h : RD vatBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨4893⟩
      [vtab, ⟨0⟩, utab, forkIlkBase I, forkDstUrnBase I, forkSrcUrnBase I,
        forkDartWord I, forkDinkWord I, forkDstMaskedWord I, forkSrcMaskedWord I,
        forkIlkWord I, ⟨524⟩, sel]
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hmem : mem.size = 96)
    (hwish : forkBothWishWord σ I ≠ ⟨0⟩) :
    ∃ k' C', RD vatBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨4990⟩
      [vtab, utab, forkIlkBase I, forkDstUrnBase I, forkSrcUrnBase I,
        forkDartWord I, forkDinkWord I, forkDstMaskedWord I, forkSrcMaskedWord I,
        forkIlkWord I, ⟨524⟩, sel]
      (twoWordHashMem (hopeSourceWord I) (solcMappingSlot ⟨1⟩ (forkDstMaskedWord I))
        (twoWordHashMem (forkDstMaskedWord I) ⟨1⟩
          (twoWordHashMem (hopeSourceWord I) (solcMappingSlot ⟨1⟩ (forkSrcMaskedWord I))
            (twoWordHashMem (forkSrcMaskedWord I) ⟨1⟩ mem))))
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  let memSrc :=
    twoWordHashMem (hopeSourceWord I) (solcMappingSlot ⟨1⟩ (forkSrcMaskedWord I))
      (twoWordHashMem (forkSrcMaskedWord I) ⟨1⟩ mem)
  let memDst :=
    twoWordHashMem (hopeSourceWord I) (solcMappingSlot ⟨1⟩ (forkDstMaskedWord I))
      (twoWordHashMem (forkDstMaskedWord I) ⟨1⟩ memSrc)
  have rd4907 := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw push2 ⟨4923⟩ (by native_decide) (by evm_ov),
    raw push2 ⟨4908⟩ (by native_decide) (by evm_ov),
    raw dup11 (by native_decide) (by evm_ov),
    raw caller (by native_decide) (by evm_ov),
    raw push2 ⟨6557⟩ (by native_decide) (by evm_ov),
    raw jump (by native_decide) (by jump_dest) (by evm_ov)]
  obtain ⟨_, _, rd6599src⟩ := RD.vatForkWishLoadedAt6557
    (usr := forkSrcMaskedWord I) (slot := forkSrcWishSlot I) (ret := ⟨4908⟩)
    (R := ⟨4923⟩ :: vtab :: utab :: forkIlkBase I :: forkDstUrnBase I ::
      forkSrcUrnBase I :: forkDartWord I :: forkDinkWord I :: forkDstMaskedWord I ::
      forkSrcMaskedWord I :: forkIlkWord I :: ⟨524⟩ :: sel :: [])
    rd4907 hmem
    (solcAddrMask_clean_left (forkSrcMaskedWord_canonical I))
    (forkSrcWishSlot_eq I)
    (by simp)
  obtain ⟨_, _, rd4908⟩ := RD.vatForkWishReturnOk
    (usr := forkSrcMaskedWord I) (slot := forkSrcWishSlot I) (ret := ⟨4908⟩)
    (R := ⟨4923⟩ :: vtab :: utab :: forkIlkBase I :: forkDstUrnBase I ::
      forkSrcUrnBase I :: forkDartWord I :: forkDinkWord I :: forkDstMaskedWord I ::
      forkSrcMaskedWord I :: forkIlkWord I :: ⟨524⟩ :: sel :: [])
    rd6599src (by jump_dest) (by simp)
  have rd4917 := evm_run rd4908 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push2 ⟨4918⟩ (by native_decide) (by evm_ov),
    raw dup11 (by native_decide) (by evm_ov),
    raw caller (by native_decide) (by evm_ov),
    raw push2 ⟨6557⟩ (by native_decide) (by evm_ov),
    raw jump (by native_decide) (by jump_dest) (by evm_ov)]
  have hmemSrc : memSrc.size = 96 := by
    exact twoWordHashMem_size_96 (hopeSourceWord I) (solcMappingSlot ⟨1⟩ (forkSrcMaskedWord I))
      (twoWordHashMem_size_96 (forkSrcMaskedWord I) ⟨1⟩ hmem)
  obtain ⟨_, _, rd6599dst⟩ := RD.vatForkWishLoadedAt6557
    (usr := forkDstMaskedWord I) (slot := forkDstWishSlot I) (ret := ⟨4918⟩)
    (R := forkSrcWishWord σ I :: ⟨4923⟩ :: vtab :: utab :: forkIlkBase I ::
      forkDstUrnBase I :: forkSrcUrnBase I :: forkDartWord I :: forkDinkWord I ::
      forkDstMaskedWord I :: forkSrcMaskedWord I :: forkIlkWord I :: ⟨524⟩ ::
      sel :: [])
    (by simpa [forkSrcWishWord, memSrc] using rd4917)
    hmemSrc
    (solcAddrMask_clean_left (forkDstMaskedWord_canonical I))
    (forkDstWishSlot_eq I)
    (by simp)
  obtain ⟨_, _, rd4918⟩ := RD.vatForkWishReturnOk
    (usr := forkDstMaskedWord I) (slot := forkDstWishSlot I) (ret := ⟨4918⟩)
    (R := forkSrcWishWord σ I :: ⟨4923⟩ :: vtab :: utab :: forkIlkBase I ::
      forkDstUrnBase I :: forkSrcUrnBase I :: forkDartWord I :: forkDinkWord I ::
      forkDstMaskedWord I :: forkSrcMaskedWord I :: forkIlkWord I :: ⟨524⟩ ::
      sel :: [])
    rd6599dst (by jump_dest) (by simp)
  have rd6787 := evm_run rd4918 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push2 ⟨6787⟩ (by native_decide) (by evm_ov),
    raw jump (by native_decide) (by jump_dest) (by evm_ov)]
  have rd4923 := evm_run rd6787 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw jump (by native_decide) (by jump_dest) (by evm_ov)]
  have rd4927pre := evm_run rd4923 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push2 ⟨4990⟩ (by native_decide) (by evm_ov)]
  exact ⟨_, _, by
    simpa [forkBothWishWord, forkDstWishWord, forkSrcWishWord, memDst, memSrc] using
      rd4927pre.jumpiT (by native_decide) hwish (by jump_dest) (by evm_ov)⟩

set_option maxHeartbeats 1000000 in
theorem RD.vatForkWishBranchRevert
    {cA gh bl σInit σ σ₀ A I} {g : Sat256} {k C : ℕ}
    {sel utab vtab : UInt256} {mem : ByteArray}
    (h : RD vatBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨4893⟩
      [vtab, ⟨0⟩, utab, forkIlkBase I, forkDstUrnBase I, forkSrcUrnBase I,
        forkDartWord I, forkDinkWord I, forkDstMaskedWord I, forkSrcMaskedWord I,
        forkIlkWord I, ⟨524⟩, sel]
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hwish : forkBothWishWord σ I = ⟨0⟩) :
    RDrev vatBytecode g (initState cA gh bl σInit σ₀ g A I) := by
  let memSrc :=
    twoWordHashMem (hopeSourceWord I) (solcMappingSlot ⟨1⟩ (forkSrcMaskedWord I))
      (twoWordHashMem (forkSrcMaskedWord I) ⟨1⟩ mem)
  let memDst :=
    twoWordHashMem (hopeSourceWord I) (solcMappingSlot ⟨1⟩ (forkDstMaskedWord I))
      (twoWordHashMem (forkDstMaskedWord I) ⟨1⟩ memSrc)
  have rd4907 := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw push2 ⟨4923⟩ (by native_decide) (by evm_ov),
    raw push2 ⟨4908⟩ (by native_decide) (by evm_ov),
    raw dup11 (by native_decide) (by evm_ov),
    raw caller (by native_decide) (by evm_ov),
    raw push2 ⟨6557⟩ (by native_decide) (by evm_ov),
    raw jump (by native_decide) (by jump_dest) (by evm_ov)]
  obtain ⟨_, _, rd6599src⟩ := RD.vatForkWishLoadedAt6557
    (usr := forkSrcMaskedWord I) (slot := forkSrcWishSlot I) (ret := ⟨4908⟩)
    (R := ⟨4923⟩ :: vtab :: utab :: forkIlkBase I :: forkDstUrnBase I ::
      forkSrcUrnBase I :: forkDartWord I :: forkDinkWord I :: forkDstMaskedWord I ::
      forkSrcMaskedWord I :: forkIlkWord I :: ⟨524⟩ :: sel :: [])
    rd4907 hmem
    (solcAddrMask_clean_left (forkSrcMaskedWord_canonical I))
    (forkSrcWishSlot_eq I)
    (by simp)
  obtain ⟨_, _, rd4908⟩ := RD.vatForkWishReturnOk
    (usr := forkSrcMaskedWord I) (slot := forkSrcWishSlot I) (ret := ⟨4908⟩)
    (R := ⟨4923⟩ :: vtab :: utab :: forkIlkBase I :: forkDstUrnBase I ::
      forkSrcUrnBase I :: forkDartWord I :: forkDinkWord I :: forkDstMaskedWord I ::
      forkSrcMaskedWord I :: forkIlkWord I :: ⟨524⟩ :: sel :: [])
    rd6599src (by jump_dest) (by simp)
  have rd4917 := evm_run rd4908 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push2 ⟨4918⟩ (by native_decide) (by evm_ov),
    raw dup11 (by native_decide) (by evm_ov),
    raw caller (by native_decide) (by evm_ov),
    raw push2 ⟨6557⟩ (by native_decide) (by evm_ov),
    raw jump (by native_decide) (by jump_dest) (by evm_ov)]
  have hmemSrc : memSrc.size = 96 := by
    exact twoWordHashMem_size_96 (hopeSourceWord I) (solcMappingSlot ⟨1⟩ (forkSrcMaskedWord I))
      (twoWordHashMem_size_96 (forkSrcMaskedWord I) ⟨1⟩ hmem)
  obtain ⟨_, _, rd6599dst⟩ := RD.vatForkWishLoadedAt6557
    (usr := forkDstMaskedWord I) (slot := forkDstWishSlot I) (ret := ⟨4918⟩)
    (R := forkSrcWishWord σ I :: ⟨4923⟩ :: vtab :: utab :: forkIlkBase I ::
      forkDstUrnBase I :: forkSrcUrnBase I :: forkDartWord I :: forkDinkWord I ::
      forkDstMaskedWord I :: forkSrcMaskedWord I :: forkIlkWord I :: ⟨524⟩ ::
      sel :: [])
    (by simpa [forkSrcWishWord, memSrc] using rd4917)
    hmemSrc
    (solcAddrMask_clean_left (forkDstMaskedWord_canonical I))
    (forkDstWishSlot_eq I)
    (by simp)
  obtain ⟨_, _, rd4918⟩ := RD.vatForkWishReturnOk
    (usr := forkDstMaskedWord I) (slot := forkDstWishSlot I) (ret := ⟨4918⟩)
    (R := forkSrcWishWord σ I :: ⟨4923⟩ :: vtab :: utab :: forkIlkBase I ::
      forkDstUrnBase I :: forkSrcUrnBase I :: forkDartWord I :: forkDinkWord I ::
      forkDstMaskedWord I :: forkSrcMaskedWord I :: forkIlkWord I :: ⟨524⟩ ::
      sel :: [])
    rd6599dst (by jump_dest) (by simp)
  have rd6787 := evm_run rd4918 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push2 ⟨6787⟩ (by native_decide) (by evm_ov),
    raw jump (by native_decide) (by jump_dest) (by evm_ov)]
  have rd4923 := evm_run rd6787 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw jump (by native_decide) (by jump_dest) (by evm_ov)]
  have rd4927pre := evm_run rd4923 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push2 ⟨4990⟩ (by native_decide) (by evm_ov)]
  have rd4928 := by
    simpa [forkBothWishWord, forkDstWishWord, forkSrcWishWord, memDst, memSrc] using
      rd4927pre.jumpiNT (by native_decide) hwish (by evm_ov)
  have hmemDst : memDst.size = 96 := by
    dsimp [memDst]
    apply twoWordHashMem_size_96
    apply twoWordHashMem_size_96
    exact hmemSrc
  have hread64Src : memSrc.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
    dsimp [memSrc]
    apply twoWordHashMem_read64
    · apply twoWordHashMem_size_96
      exact hmem
    · exact twoWordHashMem_read64 (forkSrcMaskedWord I) ⟨1⟩ hmem hread64
  have hread64Dst : memDst.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
    dsimp [memDst]
    apply twoWordHashMem_read64
    · apply twoWordHashMem_size_96
      exact hmemSrc
    · exact twoWordHashMem_read64 (forkDstMaskedWord I) ⟨1⟩ hmemSrc hread64Src
  exact RD.solcErrorStringRevertTail
    (code := vatBytecode) (pc := ⟨4928⟩) (len := ⟨15⟩)
    (rawWord := ⟨112128532177926167570164739106265433⟩) (shift := ⟨138⟩)
    (word := UInt256.shiftLeft ⟨112128532177926167570164739106265433⟩ ⟨138⟩)
    (op := .PUSH15) (width := 15)
    rd4928
    (by unfold solcErrorStringRevertTailWf; repeat' first | apply And.intro | native_decide)
    (by native_decide) rfl hmemDst hread64Dst (by simp)

theorem RD.vatForkSrcUnsafeCheckSuccess
    {cA gh bl σInit σ σ₀ A I} {g : Sat256} {k C : ℕ}
    {sel utab vtab : UInt256} {mem : ByteArray}
    (h : RD vatBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨4990⟩
      [vtab, utab, forkIlkBase I, forkDstUrnBase I, forkSrcUrnBase I,
        forkDartWord I, forkDinkWord I, forkDstMaskedWord I, forkSrcMaskedWord I,
        forkIlkWord I, ⟨524⟩, sel]
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hok :
      solcSlotWord σ I (forkIlkSpotSlot I) = ⟨0⟩ ∨
        UInt256.eq
          (UInt256.div
            (UInt256.mul
              (solcSlotWord σ I (forkSrcInkSlot I))
              (solcSlotWord σ I (forkIlkSpotSlot I)))
            (solcSlotWord σ I (forkIlkSpotSlot I)))
          (solcSlotWord σ I (forkSrcInkSlot I)) ≠ ⟨0⟩)
    (hle :
      UInt256.gt utab
        (UInt256.mul
          (solcSlotWord σ I (forkSrcInkSlot I))
          (solcSlotWord σ I (forkIlkSpotSlot I))) = ⟨0⟩) :
    ∃ k' C', RD vatBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨5079⟩
      [vtab, utab, forkIlkBase I, forkDstUrnBase I, forkSrcUrnBase I,
        forkDartWord I, forkDinkWord I, forkDstMaskedWord I, forkSrcMaskedWord I,
        forkIlkWord I, ⟨524⟩, sel]
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  let srcInkFinal := solcSlotWord σ I (forkSrcInkSlot I)
  let spot := solcSlotWord σ I (forkIlkSpotSlot I)
  let srcInkSpot := UInt256.mul srcInkFinal spot
  have rd4991 := h.jumpdest (by native_decide) (by evm_ov)
  have rd4994 := rd4991.push2 ⟨5008⟩ (by native_decide) (by evm_ov)
  have rd4995 := rd4994.dup6 (by native_decide) (by evm_ov)
  have rd4997 := rd4995.push1 ⟨0⟩ (by native_decide) (by evm_ov)
  have rd4998pre := rd4997.add (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd4999raw⟩ := rd4998pre.sload (by native_decide) (by evm_ov)
  have hsrcInk :
      (σ.find? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD (⟨0⟩ + forkSrcUrnBase I) ⟨0⟩)) = srcInkFinal := by
    rw [u256_zero_add]
    simp [srcInkFinal, solcSlotWord, forkSrcInkSlot]
  have rd4999 := rd4999raw
  rw [hsrcInk] at rd4999
  have rd5000 := rd4999.dup5 (by native_decide) (by evm_ov)
  have rd5002 := rd5000.push1 ⟨2⟩ (by native_decide) (by evm_ov)
  have rd5003pre := rd5002.add (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd5004raw⟩ := rd5003pre.sload (by native_decide) (by evm_ov)
  have hspot :
      (σ.find? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD (⟨2⟩ + forkIlkBase I) ⟨0⟩)) = spot := by
    rw [u256_add_comm (⟨2⟩ : UInt256) (forkIlkBase I)]
    simp [spot, solcSlotWord, forkIlkSpotSlot]
  have rd5004 := rd5004raw
  rw [hspot] at rd5004
  have rd5007 := rd5004.push2 ⟨6752⟩ (by native_decide) (by evm_ov)
  have rd6752 := rd5007.jump (by native_decide) (by jump_dest) (by evm_ov)
  obtain ⟨_, _, rd5008⟩ := RD.vatCheckedMulUintOk
    (x := spot) (y := srcInkFinal) (ret := ⟨5008⟩)
    (R := vtab :: utab :: forkIlkBase I :: forkDstUrnBase I :: forkSrcUrnBase I ::
      forkDartWord I :: forkDinkWord I :: forkDstMaskedWord I ::
      forkSrcMaskedWord I :: forkIlkWord I :: ⟨524⟩ :: sel :: [])
    rd6752
    (by simpa [spot, srcInkFinal, srcInkSpot] using hok)
    (by jump_dest) (by simp)
  have rd5009 := rd5008.jumpdest (by native_decide) (by evm_ov)
  have rd5010 := rd5009.dup3 (by native_decide) (by evm_ov)
  have rd5011 := rd5010.gt (by native_decide) (by evm_ov)
  have rd5012pre := rd5011.iszero (by native_decide) (by evm_ov)
  have rd5012 := by
    rw [show UInt256.gt utab srcInkSpot = ⟨0⟩ by simpa [srcInkSpot] using hle,
      show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rd5012pre
    exact rd5012pre
  have rd5015 := rd5012.push2 ⟨5079⟩ (by native_decide) (by evm_ov)
  exact ⟨_, _, by
    simpa [srcInkSpot, srcInkFinal, spot] using
      rd5015.jumpiT (by native_decide) one_ne_zero_uint (by jump_dest) (by evm_ov)⟩

theorem RD.vatForkSrcUnsafeMulRevert
    {cA gh bl σInit σ σ₀ A I} {g : Sat256} {k C : ℕ}
    {sel utab vtab : UInt256} {mem : ByteArray}
    (h : RD vatBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨4990⟩
      [vtab, utab, forkIlkBase I, forkDstUrnBase I, forkSrcUrnBase I,
        forkDartWord I, forkDinkWord I, forkDstMaskedWord I, forkSrcMaskedWord I,
        forkIlkWord I, ⟨524⟩, sel]
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hfail :
      ¬ (solcSlotWord σ I (forkIlkSpotSlot I) = ⟨0⟩ ∨
        UInt256.eq
          (UInt256.div
            (UInt256.mul
              (solcSlotWord σ I (forkSrcInkSlot I))
              (solcSlotWord σ I (forkIlkSpotSlot I)))
            (solcSlotWord σ I (forkIlkSpotSlot I)))
          (solcSlotWord σ I (forkSrcInkSlot I)) ≠ ⟨0⟩)) :
    RDrev vatBytecode g (initState cA gh bl σInit σ₀ g A I) := by
  let srcInkFinal := solcSlotWord σ I (forkSrcInkSlot I)
  let spot := solcSlotWord σ I (forkIlkSpotSlot I)
  let srcInkSpot := UInt256.mul srcInkFinal spot
  have rd4991 := h.jumpdest (by native_decide) (by evm_ov)
  have rd4994 := rd4991.push2 ⟨5008⟩ (by native_decide) (by evm_ov)
  have rd4995 := rd4994.dup6 (by native_decide) (by evm_ov)
  have rd4997 := rd4995.push1 ⟨0⟩ (by native_decide) (by evm_ov)
  have rd4998pre := rd4997.add (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd4999raw⟩ := rd4998pre.sload (by native_decide) (by evm_ov)
  have hsrcInk :
      (σ.find? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD (⟨0⟩ + forkSrcUrnBase I) ⟨0⟩)) = srcInkFinal := by
    rw [u256_zero_add]
    simp [srcInkFinal, solcSlotWord, forkSrcInkSlot]
  have rd4999 := rd4999raw
  rw [hsrcInk] at rd4999
  have rd5000 := rd4999.dup5 (by native_decide) (by evm_ov)
  have rd5002 := rd5000.push1 ⟨2⟩ (by native_decide) (by evm_ov)
  have rd5003pre := rd5002.add (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd5004raw⟩ := rd5003pre.sload (by native_decide) (by evm_ov)
  have hspot :
      (σ.find? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD (⟨2⟩ + forkIlkBase I) ⟨0⟩)) = spot := by
    rw [u256_add_comm (⟨2⟩ : UInt256) (forkIlkBase I)]
    simp [spot, solcSlotWord, forkIlkSpotSlot]
  have rd5004 := rd5004raw
  rw [hspot] at rd5004
  have rd5007 := rd5004.push2 ⟨6752⟩ (by native_decide) (by evm_ov)
  have rd6752 := rd5007.jump (by native_decide) (by jump_dest) (by evm_ov)
  exact RD.vatCheckedMulUintRevert
    (x := spot) (y := srcInkFinal) (ret := ⟨5008⟩)
    (R := vtab :: utab :: forkIlkBase I :: forkDstUrnBase I :: forkSrcUrnBase I ::
      forkDartWord I :: forkDinkWord I :: forkDstMaskedWord I ::
      forkSrcMaskedWord I :: forkIlkWord I :: ⟨524⟩ :: sel :: [])
    rd6752
    (by simpa [spot, srcInkFinal, srcInkSpot] using hfail)
    (by simp)

theorem RD.vatForkSrcUnsafeCheckRevert
    {cA gh bl σInit σ σ₀ A I} {g : Sat256} {k C : ℕ}
    {sel utab vtab : UInt256} {mem : ByteArray}
    (h : RD vatBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨4990⟩
      [vtab, utab, forkIlkBase I, forkDstUrnBase I, forkSrcUrnBase I,
        forkDartWord I, forkDinkWord I, forkDstMaskedWord I, forkSrcMaskedWord I,
        forkIlkWord I, ⟨524⟩, sel]
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hok :
      solcSlotWord σ I (forkIlkSpotSlot I) = ⟨0⟩ ∨
        UInt256.eq
          (UInt256.div
            (UInt256.mul
              (solcSlotWord σ I (forkSrcInkSlot I))
              (solcSlotWord σ I (forkIlkSpotSlot I)))
            (solcSlotWord σ I (forkIlkSpotSlot I)))
          (solcSlotWord σ I (forkSrcInkSlot I)) ≠ ⟨0⟩)
    (hgt :
      UInt256.gt utab
        (UInt256.mul
          (solcSlotWord σ I (forkSrcInkSlot I))
          (solcSlotWord σ I (forkIlkSpotSlot I))) ≠ ⟨0⟩) :
    RDrev vatBytecode g (initState cA gh bl σInit σ₀ g A I) := by
  let srcInkFinal := solcSlotWord σ I (forkSrcInkSlot I)
  let spot := solcSlotWord σ I (forkIlkSpotSlot I)
  let srcInkSpot := UInt256.mul srcInkFinal spot
  have rd4991 := h.jumpdest (by native_decide) (by evm_ov)
  have rd4994 := rd4991.push2 ⟨5008⟩ (by native_decide) (by evm_ov)
  have rd4995 := rd4994.dup6 (by native_decide) (by evm_ov)
  have rd4997 := rd4995.push1 ⟨0⟩ (by native_decide) (by evm_ov)
  have rd4998pre := rd4997.add (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd4999raw⟩ := rd4998pre.sload (by native_decide) (by evm_ov)
  have hsrcInk :
      (σ.find? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD (⟨0⟩ + forkSrcUrnBase I) ⟨0⟩)) = srcInkFinal := by
    rw [u256_zero_add]
    simp [srcInkFinal, solcSlotWord, forkSrcInkSlot]
  have rd4999 := rd4999raw
  rw [hsrcInk] at rd4999
  have rd5000 := rd4999.dup5 (by native_decide) (by evm_ov)
  have rd5002 := rd5000.push1 ⟨2⟩ (by native_decide) (by evm_ov)
  have rd5003pre := rd5002.add (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd5004raw⟩ := rd5003pre.sload (by native_decide) (by evm_ov)
  have hspot :
      (σ.find? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD (⟨2⟩ + forkIlkBase I) ⟨0⟩)) = spot := by
    rw [u256_add_comm (⟨2⟩ : UInt256) (forkIlkBase I)]
    simp [spot, solcSlotWord, forkIlkSpotSlot]
  have rd5004 := rd5004raw
  rw [hspot] at rd5004
  have rd5007 := rd5004.push2 ⟨6752⟩ (by native_decide) (by evm_ov)
  have rd6752 := rd5007.jump (by native_decide) (by jump_dest) (by evm_ov)
  obtain ⟨_, _, rd5008⟩ := RD.vatCheckedMulUintOk
    (x := spot) (y := srcInkFinal) (ret := ⟨5008⟩)
    (R := vtab :: utab :: forkIlkBase I :: forkDstUrnBase I :: forkSrcUrnBase I ::
      forkDartWord I :: forkDinkWord I :: forkDstMaskedWord I ::
      forkSrcMaskedWord I :: forkIlkWord I :: ⟨524⟩ :: sel :: [])
    rd6752
    (by simpa [spot, srcInkFinal, srcInkSpot] using hok)
    (by jump_dest) (by simp)
  have rd5009 := rd5008.jumpdest (by native_decide) (by evm_ov)
  have rd5010 := rd5009.dup3 (by native_decide) (by evm_ov)
  have rd5011 := rd5010.gt (by native_decide) (by evm_ov)
  have rd5012pre := rd5011.iszero (by native_decide) (by evm_ov)
  have rd5012 := by
    rw [show UInt256.isZero (UInt256.gt utab srcInkSpot) = ⟨0⟩ from by
      apply isZero_eq_zero_of_ne
      simpa [srcInkSpot, srcInkFinal, spot] using hgt] at rd5012pre
    exact rd5012pre
  have rd5015 := rd5012.push2 ⟨5079⟩ (by native_decide) (by evm_ov)
  have rd5016 := by
    simpa [srcInkSpot, srcInkFinal, spot] using
      rd5015.jumpiNT (by native_decide) rfl (by evm_ov)
  exact RD.solcErrorStringRevertTail
    (code := vatBytecode) (pc := ⟨5016⟩) (len := ⟨16⟩)
    (rawWord := ⟨114819616950196395593142626671494656611⟩) (shift := ⟨128⟩)
    (word := UInt256.shiftLeft ⟨114819616950196395593142626671494656611⟩ ⟨128⟩)
    (op := .PUSH16) (width := 16)
    rd5016
    (by unfold solcErrorStringRevertTailWf; repeat' first | apply And.intro | native_decide)
    (by native_decide) rfl hmem hread64 (by simp)

theorem RD.vatForkDstUnsafeCheckSuccess
    {cA gh bl σInit σ σ₀ A I} {g : Sat256} {k C : ℕ}
    {sel utab vtab : UInt256} {mem : ByteArray}
    (h : RD vatBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨5079⟩
      [vtab, utab, forkIlkBase I, forkDstUrnBase I, forkSrcUrnBase I,
        forkDartWord I, forkDinkWord I, forkDstMaskedWord I, forkSrcMaskedWord I,
        forkIlkWord I, ⟨524⟩, sel]
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hok :
      solcSlotWord σ I (forkIlkSpotSlot I) = ⟨0⟩ ∨
        UInt256.eq
          (UInt256.div
            (UInt256.mul
              (solcSlotWord σ I (forkDstInkSlot I))
              (solcSlotWord σ I (forkIlkSpotSlot I)))
            (solcSlotWord σ I (forkIlkSpotSlot I)))
          (solcSlotWord σ I (forkDstInkSlot I)) ≠ ⟨0⟩)
    (hle :
      UInt256.gt vtab
        (UInt256.mul
          (solcSlotWord σ I (forkDstInkSlot I))
          (solcSlotWord σ I (forkIlkSpotSlot I))) = ⟨0⟩) :
    ∃ k' C', RD vatBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨5168⟩
      [vtab, utab, forkIlkBase I, forkDstUrnBase I, forkSrcUrnBase I,
        forkDartWord I, forkDinkWord I, forkDstMaskedWord I, forkSrcMaskedWord I,
        forkIlkWord I, ⟨524⟩, sel]
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  let dstInkFinal := solcSlotWord σ I (forkDstInkSlot I)
  let spot := solcSlotWord σ I (forkIlkSpotSlot I)
  let dstInkSpot := UInt256.mul dstInkFinal spot
  have rd5080 := h.jumpdest (by native_decide) (by evm_ov)
  have rd5083 := rd5080.push2 ⟨5097⟩ (by native_decide) (by evm_ov)
  have rd5084 := rd5083.dup5 (by native_decide) (by evm_ov)
  have rd5086 := rd5084.push1 ⟨0⟩ (by native_decide) (by evm_ov)
  have rd5087pre := rd5086.add (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd5088raw⟩ := rd5087pre.sload (by native_decide) (by evm_ov)
  have hdstInk :
      (σ.find? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD (⟨0⟩ + forkDstUrnBase I) ⟨0⟩)) = dstInkFinal := by
    rw [u256_zero_add]
    simp [dstInkFinal, solcSlotWord, forkDstInkSlot]
  have rd5088 := rd5088raw
  rw [hdstInk] at rd5088
  have rd5089 := rd5088.dup5 (by native_decide) (by evm_ov)
  have rd5091 := rd5089.push1 ⟨2⟩ (by native_decide) (by evm_ov)
  have rd5092pre := rd5091.add (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd5093raw⟩ := rd5092pre.sload (by native_decide) (by evm_ov)
  have hspot :
      (σ.find? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD (⟨2⟩ + forkIlkBase I) ⟨0⟩)) = spot := by
    rw [u256_add_comm (⟨2⟩ : UInt256) (forkIlkBase I)]
    simp [spot, solcSlotWord, forkIlkSpotSlot]
  have rd5093 := rd5093raw
  rw [hspot] at rd5093
  have rd5096 := rd5093.push2 ⟨6752⟩ (by native_decide) (by evm_ov)
  have rd6752 := rd5096.jump (by native_decide) (by jump_dest) (by evm_ov)
  obtain ⟨_, _, rd5097⟩ := RD.vatCheckedMulUintOk
    (x := spot) (y := dstInkFinal) (ret := ⟨5097⟩)
    (R := vtab :: utab :: forkIlkBase I :: forkDstUrnBase I :: forkSrcUrnBase I ::
      forkDartWord I :: forkDinkWord I :: forkDstMaskedWord I ::
      forkSrcMaskedWord I :: forkIlkWord I :: ⟨524⟩ :: sel :: [])
    rd6752
    (by simpa [spot, dstInkFinal, dstInkSpot] using hok)
    (by jump_dest) (by simp)
  have rd5098 := rd5097.jumpdest (by native_decide) (by evm_ov)
  have rd5099 := rd5098.dup2 (by native_decide) (by evm_ov)
  have rd5100 := rd5099.gt (by native_decide) (by evm_ov)
  have rd5101pre := rd5100.iszero (by native_decide) (by evm_ov)
  have rd5101 := by
    rw [show UInt256.gt vtab dstInkSpot = ⟨0⟩ by simpa [dstInkSpot] using hle,
      show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rd5101pre
    exact rd5101pre
  have rd5104 := rd5101.push2 ⟨5168⟩ (by native_decide) (by evm_ov)
  exact ⟨_, _, by
    simpa [dstInkSpot, dstInkFinal, spot] using
      rd5104.jumpiT (by native_decide) one_ne_zero_uint (by jump_dest) (by evm_ov)⟩

theorem RD.vatForkDstUnsafeMulRevert
    {cA gh bl σInit σ σ₀ A I} {g : Sat256} {k C : ℕ}
    {sel utab vtab : UInt256} {mem : ByteArray}
    (h : RD vatBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨5079⟩
      [vtab, utab, forkIlkBase I, forkDstUrnBase I, forkSrcUrnBase I,
        forkDartWord I, forkDinkWord I, forkDstMaskedWord I, forkSrcMaskedWord I,
        forkIlkWord I, ⟨524⟩, sel]
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hfail :
      ¬ (solcSlotWord σ I (forkIlkSpotSlot I) = ⟨0⟩ ∨
        UInt256.eq
          (UInt256.div
            (UInt256.mul
              (solcSlotWord σ I (forkDstInkSlot I))
              (solcSlotWord σ I (forkIlkSpotSlot I)))
            (solcSlotWord σ I (forkIlkSpotSlot I)))
          (solcSlotWord σ I (forkDstInkSlot I)) ≠ ⟨0⟩)) :
    RDrev vatBytecode g (initState cA gh bl σInit σ₀ g A I) := by
  let dstInkFinal := solcSlotWord σ I (forkDstInkSlot I)
  let spot := solcSlotWord σ I (forkIlkSpotSlot I)
  let dstInkSpot := UInt256.mul dstInkFinal spot
  have rd5080 := h.jumpdest (by native_decide) (by evm_ov)
  have rd5083 := rd5080.push2 ⟨5097⟩ (by native_decide) (by evm_ov)
  have rd5084 := rd5083.dup5 (by native_decide) (by evm_ov)
  have rd5086 := rd5084.push1 ⟨0⟩ (by native_decide) (by evm_ov)
  have rd5087pre := rd5086.add (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd5088raw⟩ := rd5087pre.sload (by native_decide) (by evm_ov)
  have hdstInk :
      (σ.find? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD (⟨0⟩ + forkDstUrnBase I) ⟨0⟩)) = dstInkFinal := by
    rw [u256_zero_add]
    simp [dstInkFinal, solcSlotWord, forkDstInkSlot]
  have rd5088 := rd5088raw
  rw [hdstInk] at rd5088
  have rd5089 := rd5088.dup5 (by native_decide) (by evm_ov)
  have rd5091 := rd5089.push1 ⟨2⟩ (by native_decide) (by evm_ov)
  have rd5092pre := rd5091.add (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd5093raw⟩ := rd5092pre.sload (by native_decide) (by evm_ov)
  have hspot :
      (σ.find? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD (⟨2⟩ + forkIlkBase I) ⟨0⟩)) = spot := by
    rw [u256_add_comm (⟨2⟩ : UInt256) (forkIlkBase I)]
    simp [spot, solcSlotWord, forkIlkSpotSlot]
  have rd5093 := rd5093raw
  rw [hspot] at rd5093
  have rd5096 := rd5093.push2 ⟨6752⟩ (by native_decide) (by evm_ov)
  have rd6752 := rd5096.jump (by native_decide) (by jump_dest) (by evm_ov)
  exact RD.vatCheckedMulUintRevert
    (x := spot) (y := dstInkFinal) (ret := ⟨5097⟩)
    (R := vtab :: utab :: forkIlkBase I :: forkDstUrnBase I :: forkSrcUrnBase I ::
      forkDartWord I :: forkDinkWord I :: forkDstMaskedWord I ::
      forkSrcMaskedWord I :: forkIlkWord I :: ⟨524⟩ :: sel :: [])
    rd6752
    (by simpa [spot, dstInkFinal, dstInkSpot] using hfail)
    (by simp)

theorem RD.vatForkDstUnsafeCheckRevert
    {cA gh bl σInit σ σ₀ A I} {g : Sat256} {k C : ℕ}
    {sel utab vtab : UInt256} {mem : ByteArray}
    (h : RD vatBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨5079⟩
      [vtab, utab, forkIlkBase I, forkDstUrnBase I, forkSrcUrnBase I,
        forkDartWord I, forkDinkWord I, forkDstMaskedWord I, forkSrcMaskedWord I,
        forkIlkWord I, ⟨524⟩, sel]
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hok :
      solcSlotWord σ I (forkIlkSpotSlot I) = ⟨0⟩ ∨
        UInt256.eq
          (UInt256.div
            (UInt256.mul
              (solcSlotWord σ I (forkDstInkSlot I))
              (solcSlotWord σ I (forkIlkSpotSlot I)))
            (solcSlotWord σ I (forkIlkSpotSlot I)))
          (solcSlotWord σ I (forkDstInkSlot I)) ≠ ⟨0⟩)
    (hgt :
      UInt256.gt vtab
        (UInt256.mul
          (solcSlotWord σ I (forkDstInkSlot I))
          (solcSlotWord σ I (forkIlkSpotSlot I))) ≠ ⟨0⟩) :
    RDrev vatBytecode g (initState cA gh bl σInit σ₀ g A I) := by
  let dstInkFinal := solcSlotWord σ I (forkDstInkSlot I)
  let spot := solcSlotWord σ I (forkIlkSpotSlot I)
  let dstInkSpot := UInt256.mul dstInkFinal spot
  have rd5080 := h.jumpdest (by native_decide) (by evm_ov)
  have rd5083 := rd5080.push2 ⟨5097⟩ (by native_decide) (by evm_ov)
  have rd5084 := rd5083.dup5 (by native_decide) (by evm_ov)
  have rd5086 := rd5084.push1 ⟨0⟩ (by native_decide) (by evm_ov)
  have rd5087pre := rd5086.add (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd5088raw⟩ := rd5087pre.sload (by native_decide) (by evm_ov)
  have hdstInk :
      (σ.find? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD (⟨0⟩ + forkDstUrnBase I) ⟨0⟩)) = dstInkFinal := by
    rw [u256_zero_add]
    simp [dstInkFinal, solcSlotWord, forkDstInkSlot]
  have rd5088 := rd5088raw
  rw [hdstInk] at rd5088
  have rd5089 := rd5088.dup5 (by native_decide) (by evm_ov)
  have rd5091 := rd5089.push1 ⟨2⟩ (by native_decide) (by evm_ov)
  have rd5092pre := rd5091.add (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd5093raw⟩ := rd5092pre.sload (by native_decide) (by evm_ov)
  have hspot :
      (σ.find? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD (⟨2⟩ + forkIlkBase I) ⟨0⟩)) = spot := by
    rw [u256_add_comm (⟨2⟩ : UInt256) (forkIlkBase I)]
    simp [spot, solcSlotWord, forkIlkSpotSlot]
  have rd5093 := rd5093raw
  rw [hspot] at rd5093
  have rd5096 := rd5093.push2 ⟨6752⟩ (by native_decide) (by evm_ov)
  have rd6752 := rd5096.jump (by native_decide) (by jump_dest) (by evm_ov)
  obtain ⟨_, _, rd5097⟩ := RD.vatCheckedMulUintOk
    (x := spot) (y := dstInkFinal) (ret := ⟨5097⟩)
    (R := vtab :: utab :: forkIlkBase I :: forkDstUrnBase I :: forkSrcUrnBase I ::
      forkDartWord I :: forkDinkWord I :: forkDstMaskedWord I ::
      forkSrcMaskedWord I :: forkIlkWord I :: ⟨524⟩ :: sel :: [])
    rd6752
    (by simpa [spot, dstInkFinal, dstInkSpot] using hok)
    (by jump_dest) (by simp)
  have rd5098 := rd5097.jumpdest (by native_decide) (by evm_ov)
  have rd5099 := rd5098.dup2 (by native_decide) (by evm_ov)
  have rd5100 := rd5099.gt (by native_decide) (by evm_ov)
  have rd5101pre := rd5100.iszero (by native_decide) (by evm_ov)
  have rd5101 := by
    rw [show UInt256.isZero (UInt256.gt vtab dstInkSpot) = ⟨0⟩ from by
      apply isZero_eq_zero_of_ne
      simpa [dstInkSpot, dstInkFinal, spot] using hgt] at rd5101pre
    exact rd5101pre
  have rd5104 := rd5101.push2 ⟨5168⟩ (by native_decide) (by evm_ov)
  have rd5105 := by
    simpa [dstInkSpot, dstInkFinal, spot] using
      rd5104.jumpiNT (by native_decide) rfl (by evm_ov)
  exact RD.solcErrorStringRevertTail
    (code := vatBytecode) (pc := ⟨5105⟩) (len := ⟨16⟩)
    (rawWord := ⟨28704904237549098898285656667873418461⟩) (shift := ⟨130⟩)
    (word := UInt256.shiftLeft ⟨28704904237549098898285656667873418461⟩ ⟨130⟩)
    (op := .PUSH16) (width := 16)
    rd5105
    (by unfold solcErrorStringRevertTailWf; repeat' first | apply And.intro | native_decide)
    (by native_decide) rfl hmem hread64 (by simp)

theorem RD.vatForkDustChecksSuccess
    {cA gh bl σInit σ σ₀ A I} {g : Sat256} {k C : ℕ}
    {sel utab vtab : UInt256} {mem : ByteArray}
    (h : RD vatBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨5168⟩
      [vtab, utab, forkIlkBase I, forkDstUrnBase I, forkSrcUrnBase I,
        forkDartWord I, forkDinkWord I, forkDstMaskedWord I, forkSrcMaskedWord I,
        forkIlkWord I, ⟨524⟩, sel]
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hsrcDust :
      UInt256.lor
        (UInt256.eq ⟨0⟩ (solcSlotWord σ I (forkSrcArtSlot I)))
        (UInt256.isZero (UInt256.lt utab (solcSlotWord σ I (forkIlkDustSlot I)))) ≠ ⟨0⟩)
    (hdstDust :
      UInt256.lor
        (UInt256.eq ⟨0⟩ (solcSlotWord σ I (forkDstArtSlot I)))
        (UInt256.isZero (UInt256.lt vtab (solcSlotWord σ I (forkIlkDustSlot I)))) ≠ ⟨0⟩) :
    ∃ k' C', RD vatBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨5344⟩
      [vtab, utab, forkIlkBase I, forkDstUrnBase I, forkSrcUrnBase I,
        forkDartWord I, forkDinkWord I, forkDstMaskedWord I, forkSrcMaskedWord I,
        forkIlkWord I, ⟨524⟩, sel]
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  let dust := solcSlotWord σ I (forkIlkDustSlot I)
  let srcArtFinal := solcSlotWord σ I (forkSrcArtSlot I)
  let dstArtFinal := solcSlotWord σ I (forkDstArtSlot I)
  have rd5169 := h.jumpdest (by native_decide) (by evm_ov)
  have rd5172 := rd5169.push2 ⟨5192⟩ (by native_decide) (by evm_ov)
  have rd5173 := rd5172.dup4 (by native_decide) (by evm_ov)
  have rd5175 := rd5173.push1 ⟨4⟩ (by native_decide) (by evm_ov)
  have rd5176pre := rd5175.add (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd5177raw⟩ := rd5176pre.sload (by native_decide) (by evm_ov)
  have hdust :
      (σ.find? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD (⟨4⟩ + forkIlkBase I) ⟨0⟩)) = dust := by
    rw [u256_add_comm (⟨4⟩ : UInt256) (forkIlkBase I)]
    simp [dust, solcSlotWord, forkIlkDustSlot]
  have rd5177 := rd5177raw
  rw [hdust] at rd5177
  have rd5178 := rd5177.dup4 (by native_decide) (by evm_ov)
  have rd5179 := rd5178.lt (by native_decide) (by evm_ov)
  have rd5180 := rd5179.iszero (by native_decide) (by evm_ov)
  have rd5181 := rd5180.dup7 (by native_decide) (by evm_ov)
  have rd5183 := rd5181.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  have rd5184pre := rd5183.add (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd5185raw⟩ := rd5184pre.sload (by native_decide) (by evm_ov)
  have hsrcArt :
      (σ.find? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD (⟨1⟩ + forkSrcUrnBase I) ⟨0⟩)) = srcArtFinal := by
    rw [u256_add_comm (⟨1⟩ : UInt256) (forkSrcUrnBase I)]
    simp [srcArtFinal, solcSlotWord, forkSrcArtSlot]
  have rd5185 := rd5185raw
  rw [hsrcArt] at rd5185
  have rd5187 := rd5185.push1 ⟨0⟩ (by native_decide) (by evm_ov)
  have rd5188 := rd5187.eq (by native_decide) (by evm_ov)
  have rd5191pre := rd5188.push2 ⟨6791⟩ (by native_decide) (by evm_ov)
  have rd6791 := rd5191pre.jump (by native_decide) (by jump_dest) (by evm_ov)
  have rd5192 := evm_run rd6791 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw or (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw jump (by native_decide) (by jump_dest) (by evm_ov)]
  have rd5196pre := evm_run rd5192 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push2 ⟨5256⟩ (by native_decide) (by evm_ov)]
  have rd5256 := by
    simpa [dust, srcArtFinal] using
      rd5196pre.jumpiT (by native_decide) hsrcDust (by jump_dest) (by evm_ov)
  have rd5257 := rd5256.jumpdest (by native_decide) (by evm_ov)
  have rd5260 := rd5257.push2 ⟨5280⟩ (by native_decide) (by evm_ov)
  have rd5261 := rd5260.dup4 (by native_decide) (by evm_ov)
  have rd5263 := rd5261.push1 ⟨4⟩ (by native_decide) (by evm_ov)
  have rd5264pre := rd5263.add (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd5265raw⟩ := rd5264pre.sload (by native_decide) (by evm_ov)
  have rd5265 := rd5265raw
  rw [hdust] at rd5265
  have rd5266 := rd5265.dup3 (by native_decide) (by evm_ov)
  have rd5267 := rd5266.lt (by native_decide) (by evm_ov)
  have rd5268 := rd5267.iszero (by native_decide) (by evm_ov)
  have rd5269 := rd5268.dup6 (by native_decide) (by evm_ov)
  have rd5271 := rd5269.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  have rd5272pre := rd5271.add (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd5273raw⟩ := rd5272pre.sload (by native_decide) (by evm_ov)
  have hdstArt :
      (σ.find? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD (⟨1⟩ + forkDstUrnBase I) ⟨0⟩)) = dstArtFinal := by
    rw [u256_add_comm (⟨1⟩ : UInt256) (forkDstUrnBase I)]
    simp [dstArtFinal, solcSlotWord, forkDstArtSlot]
  have rd5273 := rd5273raw
  rw [hdstArt] at rd5273
  have rd5275 := rd5273.push1 ⟨0⟩ (by native_decide) (by evm_ov)
  have rd5276 := rd5275.eq (by native_decide) (by evm_ov)
  have rd5279pre := rd5276.push2 ⟨6791⟩ (by native_decide) (by evm_ov)
  have rd6791' := rd5279pre.jump (by native_decide) (by jump_dest) (by evm_ov)
  have rd5280 := evm_run rd6791' with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw or (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw jump (by native_decide) (by jump_dest) (by evm_ov)]
  have rd5284pre := evm_run rd5280 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push2 ⟨5344⟩ (by native_decide) (by evm_ov)]
  exact ⟨_, _, by
    simpa [dust, dstArtFinal] using
      rd5284pre.jumpiT (by native_decide) hdstDust (by jump_dest) (by evm_ov)⟩

theorem RD.vatForkSrcDustCheckRevert
    {cA gh bl σInit σ σ₀ A I} {g : Sat256} {k C : ℕ}
    {sel utab vtab : UInt256} {mem : ByteArray}
    (h : RD vatBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨5168⟩
      [vtab, utab, forkIlkBase I, forkDstUrnBase I, forkSrcUrnBase I,
        forkDartWord I, forkDinkWord I, forkDstMaskedWord I, forkSrcMaskedWord I,
        forkIlkWord I, ⟨524⟩, sel]
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hsrcDust :
      UInt256.lor
        (UInt256.eq ⟨0⟩ (solcSlotWord σ I (forkSrcArtSlot I)))
        (UInt256.isZero (UInt256.lt utab (solcSlotWord σ I (forkIlkDustSlot I)))) = ⟨0⟩) :
    RDrev vatBytecode g (initState cA gh bl σInit σ₀ g A I) := by
  let dust := solcSlotWord σ I (forkIlkDustSlot I)
  let srcArtFinal := solcSlotWord σ I (forkSrcArtSlot I)
  have rd5169 := h.jumpdest (by native_decide) (by evm_ov)
  have rd5172 := rd5169.push2 ⟨5192⟩ (by native_decide) (by evm_ov)
  have rd5173 := rd5172.dup4 (by native_decide) (by evm_ov)
  have rd5175 := rd5173.push1 ⟨4⟩ (by native_decide) (by evm_ov)
  have rd5176pre := rd5175.add (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd5177raw⟩ := rd5176pre.sload (by native_decide) (by evm_ov)
  have hdust :
      (σ.find? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD (⟨4⟩ + forkIlkBase I) ⟨0⟩)) = dust := by
    rw [u256_add_comm (⟨4⟩ : UInt256) (forkIlkBase I)]
    simp [dust, solcSlotWord, forkIlkDustSlot]
  have rd5177 := rd5177raw
  rw [hdust] at rd5177
  have rd5178 := rd5177.dup4 (by native_decide) (by evm_ov)
  have rd5179 := rd5178.lt (by native_decide) (by evm_ov)
  have rd5180 := rd5179.iszero (by native_decide) (by evm_ov)
  have rd5181 := rd5180.dup7 (by native_decide) (by evm_ov)
  have rd5183 := rd5181.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  have rd5184pre := rd5183.add (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd5185raw⟩ := rd5184pre.sload (by native_decide) (by evm_ov)
  have hsrcArt :
      (σ.find? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD (⟨1⟩ + forkSrcUrnBase I) ⟨0⟩)) = srcArtFinal := by
    rw [u256_add_comm (⟨1⟩ : UInt256) (forkSrcUrnBase I)]
    simp [srcArtFinal, solcSlotWord, forkSrcArtSlot]
  have rd5185 := rd5185raw
  rw [hsrcArt] at rd5185
  have rd5187 := rd5185.push1 ⟨0⟩ (by native_decide) (by evm_ov)
  have rd5188 := rd5187.eq (by native_decide) (by evm_ov)
  have rd5191pre := rd5188.push2 ⟨6791⟩ (by native_decide) (by evm_ov)
  have rd6791 := rd5191pre.jump (by native_decide) (by jump_dest) (by evm_ov)
  have rd5192 := evm_run rd6791 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw or (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw jump (by native_decide) (by jump_dest) (by evm_ov)]
  have rd5196pre := evm_run rd5192 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push2 ⟨5256⟩ (by native_decide) (by evm_ov)]
  have rd5197 := by
    simpa [dust, srcArtFinal] using
      rd5196pre.jumpiNT (by native_decide) hsrcDust (by evm_ov)
  exact RD.solcErrorStringRevertTail
    (code := vatBytecode) (pc := ⟨5197⟩) (len := ⟨12⟩)
    (rawWord := ⟨26733525317886098202355266147⟩) (shift := ⟨160⟩)
    (word := UInt256.shiftLeft ⟨26733525317886098202355266147⟩ ⟨160⟩)
    (op := .PUSH12) (width := 12)
    rd5197
    (by unfold solcErrorStringRevertTailWf; repeat' first | apply And.intro | native_decide)
    (by native_decide) rfl hmem hread64 (by simp)

theorem RD.vatForkDstDustCheckRevert
    {cA gh bl σInit σ σ₀ A I} {g : Sat256} {k C : ℕ}
    {sel utab vtab : UInt256} {mem : ByteArray}
    (h : RD vatBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨5168⟩
      [vtab, utab, forkIlkBase I, forkDstUrnBase I, forkSrcUrnBase I,
        forkDartWord I, forkDinkWord I, forkDstMaskedWord I, forkSrcMaskedWord I,
        forkIlkWord I, ⟨524⟩, sel]
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hsrcDust :
      UInt256.lor
        (UInt256.eq ⟨0⟩ (solcSlotWord σ I (forkSrcArtSlot I)))
        (UInt256.isZero (UInt256.lt utab (solcSlotWord σ I (forkIlkDustSlot I)))) ≠ ⟨0⟩)
    (hdstDust :
      UInt256.lor
        (UInt256.eq ⟨0⟩ (solcSlotWord σ I (forkDstArtSlot I)))
        (UInt256.isZero (UInt256.lt vtab (solcSlotWord σ I (forkIlkDustSlot I)))) = ⟨0⟩) :
    RDrev vatBytecode g (initState cA gh bl σInit σ₀ g A I) := by
  let dust := solcSlotWord σ I (forkIlkDustSlot I)
  let srcArtFinal := solcSlotWord σ I (forkSrcArtSlot I)
  let dstArtFinal := solcSlotWord σ I (forkDstArtSlot I)
  have rd5169 := h.jumpdest (by native_decide) (by evm_ov)
  have rd5172 := rd5169.push2 ⟨5192⟩ (by native_decide) (by evm_ov)
  have rd5173 := rd5172.dup4 (by native_decide) (by evm_ov)
  have rd5175 := rd5173.push1 ⟨4⟩ (by native_decide) (by evm_ov)
  have rd5176pre := rd5175.add (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd5177raw⟩ := rd5176pre.sload (by native_decide) (by evm_ov)
  have hdust :
      (σ.find? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD (⟨4⟩ + forkIlkBase I) ⟨0⟩)) = dust := by
    rw [u256_add_comm (⟨4⟩ : UInt256) (forkIlkBase I)]
    simp [dust, solcSlotWord, forkIlkDustSlot]
  have rd5177 := rd5177raw
  rw [hdust] at rd5177
  have rd5178 := rd5177.dup4 (by native_decide) (by evm_ov)
  have rd5179 := rd5178.lt (by native_decide) (by evm_ov)
  have rd5180 := rd5179.iszero (by native_decide) (by evm_ov)
  have rd5181 := rd5180.dup7 (by native_decide) (by evm_ov)
  have rd5183 := rd5181.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  have rd5184pre := rd5183.add (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd5185raw⟩ := rd5184pre.sload (by native_decide) (by evm_ov)
  have hsrcArt :
      (σ.find? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD (⟨1⟩ + forkSrcUrnBase I) ⟨0⟩)) = srcArtFinal := by
    rw [u256_add_comm (⟨1⟩ : UInt256) (forkSrcUrnBase I)]
    simp [srcArtFinal, solcSlotWord, forkSrcArtSlot]
  have rd5185 := rd5185raw
  rw [hsrcArt] at rd5185
  have rd5187 := rd5185.push1 ⟨0⟩ (by native_decide) (by evm_ov)
  have rd5188 := rd5187.eq (by native_decide) (by evm_ov)
  have rd5191pre := rd5188.push2 ⟨6791⟩ (by native_decide) (by evm_ov)
  have rd6791 := rd5191pre.jump (by native_decide) (by jump_dest) (by evm_ov)
  have rd5192 := evm_run rd6791 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw or (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw jump (by native_decide) (by jump_dest) (by evm_ov)]
  have rd5196pre := evm_run rd5192 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push2 ⟨5256⟩ (by native_decide) (by evm_ov)]
  have rd5256 := by
    simpa [dust, srcArtFinal] using
      rd5196pre.jumpiT (by native_decide) hsrcDust (by jump_dest) (by evm_ov)
  have rd5257 := rd5256.jumpdest (by native_decide) (by evm_ov)
  have rd5260 := rd5257.push2 ⟨5280⟩ (by native_decide) (by evm_ov)
  have rd5261 := rd5260.dup4 (by native_decide) (by evm_ov)
  have rd5263 := rd5261.push1 ⟨4⟩ (by native_decide) (by evm_ov)
  have rd5264pre := rd5263.add (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd5265raw⟩ := rd5264pre.sload (by native_decide) (by evm_ov)
  have rd5265 := rd5265raw
  rw [hdust] at rd5265
  have rd5266 := rd5265.dup3 (by native_decide) (by evm_ov)
  have rd5267 := rd5266.lt (by native_decide) (by evm_ov)
  have rd5268 := rd5267.iszero (by native_decide) (by evm_ov)
  have rd5269 := rd5268.dup6 (by native_decide) (by evm_ov)
  have rd5271 := rd5269.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  have rd5272pre := rd5271.add (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd5273raw⟩ := rd5272pre.sload (by native_decide) (by evm_ov)
  have hdstArt :
      (σ.find? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD (⟨1⟩ + forkDstUrnBase I) ⟨0⟩)) = dstArtFinal := by
    rw [u256_add_comm (⟨1⟩ : UInt256) (forkDstUrnBase I)]
    simp [dstArtFinal, solcSlotWord, forkDstArtSlot]
  have rd5273 := rd5273raw
  rw [hdstArt] at rd5273
  have rd5275 := rd5273.push1 ⟨0⟩ (by native_decide) (by evm_ov)
  have rd5276 := rd5275.eq (by native_decide) (by evm_ov)
  have rd5279pre := rd5276.push2 ⟨6791⟩ (by native_decide) (by evm_ov)
  have rd6791' := rd5279pre.jump (by native_decide) (by jump_dest) (by evm_ov)
  have rd5280 := evm_run rd6791' with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw or (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw jump (by native_decide) (by jump_dest) (by evm_ov)]
  have rd5284pre := evm_run rd5280 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push2 ⟨5344⟩ (by native_decide) (by evm_ov)]
  have rd5285 := by
    simpa [dust, dstArtFinal] using
      rd5284pre.jumpiNT (by native_decide) hdstDust (by evm_ov)
  exact RD.solcErrorStringRevertTail
    (code := vatBytecode) (pc := ⟨5285⟩) (len := ⟨12⟩)
    (rawWord := ⟨6683381329471524550588570845⟩) (shift := ⟨162⟩)
    (word := UInt256.shiftLeft ⟨6683381329471524550588570845⟩ ⟨162⟩)
    (op := .PUSH12) (width := 12)
    rd5285
    (by unfold solcErrorStringRevertTailWf; repeat' first | apply And.intro | native_decide)
    (by native_decide) rfl hmem hread64 (by simp)

theorem RD.vatForkCleanupSuccess
    {cA gh bl σInit σ σ₀ A I} {g : Sat256} {k C : ℕ}
    {sel utab vtab : UInt256} {mem : ByteArray}
    (h : RD vatBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨5344⟩
      [vtab, utab, forkIlkBase I, forkDstUrnBase I, forkSrcUrnBase I,
        forkDartWord I, forkDinkWord I, forkDstMaskedWord I, forkSrcMaskedWord I,
        forkIlkWord I, ⟨524⟩, sel]
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD vatBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨524⟩ [sel]
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have rd5345 := h.jumpdest (by native_decide) (by evm_ov)
  have rd5346 := rd5345.pop (by native_decide) (by evm_ov)
  have rd5347 := rd5346.pop (by native_decide) (by evm_ov)
  have rd5348 := rd5347.pop (by native_decide) (by evm_ov)
  have rd5349 := rd5348.pop (by native_decide) (by evm_ov)
  have rd5350 := rd5349.pop (by native_decide) (by evm_ov)
  have rd5351 := rd5350.pop (by native_decide) (by evm_ov)
  have rd5352 := rd5351.pop (by native_decide) (by evm_ov)
  have rd5353 := rd5352.pop (by native_decide) (by evm_ov)
  have rd5354 := rd5353.pop (by native_decide) (by evm_ov)
  have rd5355 := rd5354.pop (by native_decide) (by evm_ov)
  exact ⟨_, _, rd5355.jump (by native_decide) (by jump_dest) (by evm_ov)⟩

set_option maxHeartbeats 0 in
theorem RD.vatForkSuccessPath
    {cA gh bl σ σ₀ A I} {g : Sat256} {k C : ℕ}
    {sel srcInkNew srcArtNew dstInkNew dstArtNew utab vtab : UInt256}
    {mem : ByteArray}
    (h : RD vatBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4726⟩
      [forkDartWord I, forkDinkWord I, forkDstMaskedWord I, forkSrcMaskedWord I,
        forkIlkWord I, ⟨524⟩, sel]
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hmem : mem.size = 96)
    (hsz164 : 164 ≤ I.calldata.size)
    (hperm : I.perm = true)
    (hsrcInkNewEq :
      srcInkNew = UInt256.sub (solcSlotWord σ I (forkSrcInkSlot I)) (forkDinkWord I))
    (hsrcArtNewEq :
      srcArtNew =
        UInt256.sub
          (solcSlotWord
            (sstoreAccountMap I.codeOwner σ (forkSrcInkSlot I) srcInkNew)
            I (forkSrcArtSlot I))
          (forkDartWord I))
    (hdstInkNewEq :
      dstInkNew =
        forkDinkWord I +
          solcSlotWord
            (sstoreAccountMap I.codeOwner
              (sstoreAccountMap I.codeOwner σ (forkSrcInkSlot I) srcInkNew)
              (forkSrcArtSlot I) srcArtNew)
            I (forkDstInkSlot I))
    (hdstArtNewEq :
      dstArtNew =
        forkDartWord I +
          solcSlotWord
            (sstoreAccountMap I.codeOwner
              (sstoreAccountMap I.codeOwner
                (sstoreAccountMap I.codeOwner σ (forkSrcInkSlot I) srcInkNew)
                (forkSrcArtSlot I) srcArtNew)
              (forkDstInkSlot I) dstInkNew)
            I (forkDstArtSlot I))
    (hutabEq :
      utab =
        UInt256.mul
          (solcSlotWord
            (sstoreAccountMap I.codeOwner
              (sstoreAccountMap I.codeOwner
                (sstoreAccountMap I.codeOwner
                  (sstoreAccountMap I.codeOwner σ (forkSrcInkSlot I) srcInkNew)
                  (forkSrcArtSlot I) srcArtNew)
                (forkDstInkSlot I) dstInkNew)
              (forkDstArtSlot I) dstArtNew)
            I (forkSrcArtSlot I))
          (solcSlotWord
            (sstoreAccountMap I.codeOwner
              (sstoreAccountMap I.codeOwner
                (sstoreAccountMap I.codeOwner
                  (sstoreAccountMap I.codeOwner σ (forkSrcInkSlot I) srcInkNew)
                  (forkSrcArtSlot I) srcArtNew)
                (forkDstInkSlot I) dstInkNew)
              (forkDstArtSlot I) dstArtNew)
            I (forkIlkRateSlot I)))
    (hvtabEq :
      vtab =
        UInt256.mul
          (solcSlotWord
            (sstoreAccountMap I.codeOwner
              (sstoreAccountMap I.codeOwner
                (sstoreAccountMap I.codeOwner
                  (sstoreAccountMap I.codeOwner σ (forkSrcInkSlot I) srcInkNew)
                  (forkSrcArtSlot I) srcArtNew)
                (forkDstInkSlot I) dstInkNew)
              (forkDstArtSlot I) dstArtNew)
            I (forkDstArtSlot I))
          (solcSlotWord
            (sstoreAccountMap I.codeOwner
              (sstoreAccountMap I.codeOwner
                (sstoreAccountMap I.codeOwner
                  (sstoreAccountMap I.codeOwner σ (forkSrcInkSlot I) srcInkNew)
                  (forkSrcArtSlot I) srcArtNew)
                (forkDstInkSlot I) dstInkNew)
              (forkDstArtSlot I) dstArtNew)
            I (forkIlkRateSlot I)))
    (hsrcInkPos :
      UInt256.sgt (forkDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.gt
          (UInt256.sub (solcSlotWord σ I (forkSrcInkSlot I)) (forkDinkWord I))
          (solcSlotWord σ I (forkSrcInkSlot I)) = ⟨0⟩)
    (hsrcInkNeg :
      UInt256.slt (forkDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.lt
          (UInt256.sub (solcSlotWord σ I (forkSrcInkSlot I)) (forkDinkWord I))
          (solcSlotWord σ I (forkSrcInkSlot I)) = ⟨0⟩)
    (hsrcArtPos :
      UInt256.sgt (forkDartWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.gt
          (UInt256.sub
            (solcSlotWord
              (sstoreAccountMap I.codeOwner σ (forkSrcInkSlot I) srcInkNew)
              I (forkSrcArtSlot I))
            (forkDartWord I))
          (solcSlotWord
            (sstoreAccountMap I.codeOwner σ (forkSrcInkSlot I) srcInkNew)
            I (forkSrcArtSlot I)) = ⟨0⟩)
    (hsrcArtNeg :
      UInt256.slt (forkDartWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.lt
          (UInt256.sub
            (solcSlotWord
              (sstoreAccountMap I.codeOwner σ (forkSrcInkSlot I) srcInkNew)
              I (forkSrcArtSlot I))
            (forkDartWord I))
          (solcSlotWord
            (sstoreAccountMap I.codeOwner σ (forkSrcInkSlot I) srcInkNew)
            I (forkSrcArtSlot I)) = ⟨0⟩)
    (hdstInkNeg :
      UInt256.slt (forkDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.gt
          (forkDinkWord I +
            solcSlotWord
              (sstoreAccountMap I.codeOwner
                (sstoreAccountMap I.codeOwner σ (forkSrcInkSlot I) srcInkNew)
                (forkSrcArtSlot I) srcArtNew)
              I (forkDstInkSlot I))
          (solcSlotWord
            (sstoreAccountMap I.codeOwner
              (sstoreAccountMap I.codeOwner σ (forkSrcInkSlot I) srcInkNew)
              (forkSrcArtSlot I) srcArtNew)
            I (forkDstInkSlot I)) = ⟨0⟩)
    (hdstInkPos :
      UInt256.sgt (forkDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.lt
          (forkDinkWord I +
            solcSlotWord
              (sstoreAccountMap I.codeOwner
                (sstoreAccountMap I.codeOwner σ (forkSrcInkSlot I) srcInkNew)
                (forkSrcArtSlot I) srcArtNew)
              I (forkDstInkSlot I))
          (solcSlotWord
            (sstoreAccountMap I.codeOwner
              (sstoreAccountMap I.codeOwner σ (forkSrcInkSlot I) srcInkNew)
              (forkSrcArtSlot I) srcArtNew)
            I (forkDstInkSlot I)) = ⟨0⟩)
    (hdstArtNeg :
      UInt256.slt (forkDartWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.gt
          (forkDartWord I +
            solcSlotWord
              (sstoreAccountMap I.codeOwner
                (sstoreAccountMap I.codeOwner
                  (sstoreAccountMap I.codeOwner σ (forkSrcInkSlot I) srcInkNew)
                  (forkSrcArtSlot I) srcArtNew)
                (forkDstInkSlot I) dstInkNew)
              I (forkDstArtSlot I))
          (solcSlotWord
            (sstoreAccountMap I.codeOwner
              (sstoreAccountMap I.codeOwner
                (sstoreAccountMap I.codeOwner σ (forkSrcInkSlot I) srcInkNew)
                (forkSrcArtSlot I) srcArtNew)
              (forkDstInkSlot I) dstInkNew)
            I (forkDstArtSlot I)) = ⟨0⟩)
    (hdstArtPos :
      UInt256.sgt (forkDartWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.lt
          (forkDartWord I +
            solcSlotWord
              (sstoreAccountMap I.codeOwner
                (sstoreAccountMap I.codeOwner
                  (sstoreAccountMap I.codeOwner σ (forkSrcInkSlot I) srcInkNew)
                  (forkSrcArtSlot I) srcArtNew)
                (forkDstInkSlot I) dstInkNew)
              I (forkDstArtSlot I))
          (solcSlotWord
            (sstoreAccountMap I.codeOwner
              (sstoreAccountMap I.codeOwner
                (sstoreAccountMap I.codeOwner σ (forkSrcInkSlot I) srcInkNew)
                (forkSrcArtSlot I) srcArtNew)
              (forkDstInkSlot I) dstInkNew)
            I (forkDstArtSlot I)) = ⟨0⟩)
    (hutabOk :
      solcSlotWord
          (sstoreAccountMap I.codeOwner
            (sstoreAccountMap I.codeOwner
              (sstoreAccountMap I.codeOwner
                (sstoreAccountMap I.codeOwner σ (forkSrcInkSlot I) srcInkNew)
                (forkSrcArtSlot I) srcArtNew)
              (forkDstInkSlot I) dstInkNew)
            (forkDstArtSlot I) dstArtNew)
          I (forkIlkRateSlot I) = ⟨0⟩ ∨
        UInt256.eq
          (UInt256.div
            (UInt256.mul
              (solcSlotWord
                (sstoreAccountMap I.codeOwner
                  (sstoreAccountMap I.codeOwner
                    (sstoreAccountMap I.codeOwner
                      (sstoreAccountMap I.codeOwner σ (forkSrcInkSlot I) srcInkNew)
                      (forkSrcArtSlot I) srcArtNew)
                    (forkDstInkSlot I) dstInkNew)
                  (forkDstArtSlot I) dstArtNew)
                I (forkSrcArtSlot I))
              (solcSlotWord
                (sstoreAccountMap I.codeOwner
                  (sstoreAccountMap I.codeOwner
                    (sstoreAccountMap I.codeOwner
                      (sstoreAccountMap I.codeOwner σ (forkSrcInkSlot I) srcInkNew)
                      (forkSrcArtSlot I) srcArtNew)
                    (forkDstInkSlot I) dstInkNew)
                  (forkDstArtSlot I) dstArtNew)
                I (forkIlkRateSlot I)))
            (solcSlotWord
              (sstoreAccountMap I.codeOwner
                (sstoreAccountMap I.codeOwner
                  (sstoreAccountMap I.codeOwner
                    (sstoreAccountMap I.codeOwner σ (forkSrcInkSlot I) srcInkNew)
                    (forkSrcArtSlot I) srcArtNew)
                  (forkDstInkSlot I) dstInkNew)
                (forkDstArtSlot I) dstArtNew)
              I (forkIlkRateSlot I)))
          (solcSlotWord
            (sstoreAccountMap I.codeOwner
              (sstoreAccountMap I.codeOwner
                (sstoreAccountMap I.codeOwner
                  (sstoreAccountMap I.codeOwner σ (forkSrcInkSlot I) srcInkNew)
                  (forkSrcArtSlot I) srcArtNew)
                (forkDstInkSlot I) dstInkNew)
              (forkDstArtSlot I) dstArtNew)
            I (forkSrcArtSlot I)) ≠ ⟨0⟩)
    (hvtabOk :
      solcSlotWord
          (sstoreAccountMap I.codeOwner
            (sstoreAccountMap I.codeOwner
              (sstoreAccountMap I.codeOwner
                (sstoreAccountMap I.codeOwner σ (forkSrcInkSlot I) srcInkNew)
                (forkSrcArtSlot I) srcArtNew)
              (forkDstInkSlot I) dstInkNew)
            (forkDstArtSlot I) dstArtNew)
          I (forkIlkRateSlot I) = ⟨0⟩ ∨
        UInt256.eq
          (UInt256.div
            (UInt256.mul
              (solcSlotWord
                (sstoreAccountMap I.codeOwner
                  (sstoreAccountMap I.codeOwner
                    (sstoreAccountMap I.codeOwner
                      (sstoreAccountMap I.codeOwner σ (forkSrcInkSlot I) srcInkNew)
                      (forkSrcArtSlot I) srcArtNew)
                    (forkDstInkSlot I) dstInkNew)
                  (forkDstArtSlot I) dstArtNew)
                I (forkDstArtSlot I))
              (solcSlotWord
                (sstoreAccountMap I.codeOwner
                  (sstoreAccountMap I.codeOwner
                    (sstoreAccountMap I.codeOwner
                      (sstoreAccountMap I.codeOwner σ (forkSrcInkSlot I) srcInkNew)
                      (forkSrcArtSlot I) srcArtNew)
                    (forkDstInkSlot I) dstInkNew)
                  (forkDstArtSlot I) dstArtNew)
                I (forkIlkRateSlot I)))
            (solcSlotWord
              (sstoreAccountMap I.codeOwner
                (sstoreAccountMap I.codeOwner
                  (sstoreAccountMap I.codeOwner
                    (sstoreAccountMap I.codeOwner σ (forkSrcInkSlot I) srcInkNew)
                    (forkSrcArtSlot I) srcArtNew)
                  (forkDstInkSlot I) dstInkNew)
                (forkDstArtSlot I) dstArtNew)
              I (forkIlkRateSlot I)))
          (solcSlotWord
            (sstoreAccountMap I.codeOwner
              (sstoreAccountMap I.codeOwner
                (sstoreAccountMap I.codeOwner
                  (sstoreAccountMap I.codeOwner σ (forkSrcInkSlot I) srcInkNew)
                  (forkSrcArtSlot I) srcArtNew)
                (forkDstInkSlot I) dstInkNew)
              (forkDstArtSlot I) dstArtNew)
            I (forkDstArtSlot I)) ≠ ⟨0⟩)
    (hwish :
      forkBothWishWord
        (sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner
            (sstoreAccountMap I.codeOwner
              (sstoreAccountMap I.codeOwner σ (forkSrcInkSlot I) srcInkNew)
              (forkSrcArtSlot I) srcArtNew)
            (forkDstInkSlot I) dstInkNew)
          (forkDstArtSlot I) dstArtNew)
        I ≠ ⟨0⟩)
    (hsrcUnsafe :
      UInt256.gt utab
        (UInt256.mul
          (solcSlotWord
            (sstoreAccountMap I.codeOwner
              (sstoreAccountMap I.codeOwner
                (sstoreAccountMap I.codeOwner
                  (sstoreAccountMap I.codeOwner σ (forkSrcInkSlot I) srcInkNew)
                  (forkSrcArtSlot I) srcArtNew)
                (forkDstInkSlot I) dstInkNew)
              (forkDstArtSlot I) dstArtNew)
            I (forkSrcInkSlot I))
          (solcSlotWord
            (sstoreAccountMap I.codeOwner
              (sstoreAccountMap I.codeOwner
                (sstoreAccountMap I.codeOwner
                  (sstoreAccountMap I.codeOwner σ (forkSrcInkSlot I) srcInkNew)
                  (forkSrcArtSlot I) srcArtNew)
                (forkDstInkSlot I) dstInkNew)
              (forkDstArtSlot I) dstArtNew)
            I (forkIlkSpotSlot I))) = ⟨0⟩)
    (hdstUnsafe :
      UInt256.gt vtab
        (UInt256.mul
          (solcSlotWord
            (sstoreAccountMap I.codeOwner
              (sstoreAccountMap I.codeOwner
                (sstoreAccountMap I.codeOwner
                  (sstoreAccountMap I.codeOwner σ (forkSrcInkSlot I) srcInkNew)
                  (forkSrcArtSlot I) srcArtNew)
                (forkDstInkSlot I) dstInkNew)
              (forkDstArtSlot I) dstArtNew)
            I (forkDstInkSlot I))
          (solcSlotWord
            (sstoreAccountMap I.codeOwner
              (sstoreAccountMap I.codeOwner
                (sstoreAccountMap I.codeOwner
                  (sstoreAccountMap I.codeOwner σ (forkSrcInkSlot I) srcInkNew)
                  (forkSrcArtSlot I) srcArtNew)
                (forkDstInkSlot I) dstInkNew)
              (forkDstArtSlot I) dstArtNew)
            I (forkIlkSpotSlot I))) = ⟨0⟩)
    (hsrcInkSpotOk :
      solcSlotWord
          (sstoreAccountMap I.codeOwner
            (sstoreAccountMap I.codeOwner
              (sstoreAccountMap I.codeOwner
                (sstoreAccountMap I.codeOwner σ (forkSrcInkSlot I) srcInkNew)
                (forkSrcArtSlot I) srcArtNew)
              (forkDstInkSlot I) dstInkNew)
            (forkDstArtSlot I) dstArtNew)
          I (forkIlkSpotSlot I) = ⟨0⟩ ∨
        UInt256.eq
          (UInt256.div
            (UInt256.mul
              (solcSlotWord
                (sstoreAccountMap I.codeOwner
                  (sstoreAccountMap I.codeOwner
                    (sstoreAccountMap I.codeOwner
                      (sstoreAccountMap I.codeOwner σ (forkSrcInkSlot I) srcInkNew)
                      (forkSrcArtSlot I) srcArtNew)
                    (forkDstInkSlot I) dstInkNew)
                  (forkDstArtSlot I) dstArtNew)
                I (forkSrcInkSlot I))
              (solcSlotWord
                (sstoreAccountMap I.codeOwner
                  (sstoreAccountMap I.codeOwner
                    (sstoreAccountMap I.codeOwner
                      (sstoreAccountMap I.codeOwner σ (forkSrcInkSlot I) srcInkNew)
                      (forkSrcArtSlot I) srcArtNew)
                    (forkDstInkSlot I) dstInkNew)
                  (forkDstArtSlot I) dstArtNew)
                I (forkIlkSpotSlot I)))
            (solcSlotWord
              (sstoreAccountMap I.codeOwner
                (sstoreAccountMap I.codeOwner
                  (sstoreAccountMap I.codeOwner
                    (sstoreAccountMap I.codeOwner σ (forkSrcInkSlot I) srcInkNew)
                    (forkSrcArtSlot I) srcArtNew)
                  (forkDstInkSlot I) dstInkNew)
                (forkDstArtSlot I) dstArtNew)
              I (forkIlkSpotSlot I)))
          (solcSlotWord
            (sstoreAccountMap I.codeOwner
              (sstoreAccountMap I.codeOwner
                (sstoreAccountMap I.codeOwner
                  (sstoreAccountMap I.codeOwner σ (forkSrcInkSlot I) srcInkNew)
                  (forkSrcArtSlot I) srcArtNew)
                (forkDstInkSlot I) dstInkNew)
              (forkDstArtSlot I) dstArtNew)
            I (forkSrcInkSlot I)) ≠ ⟨0⟩)
    (hdstInkSpotOk :
      solcSlotWord
          (sstoreAccountMap I.codeOwner
            (sstoreAccountMap I.codeOwner
              (sstoreAccountMap I.codeOwner
                (sstoreAccountMap I.codeOwner σ (forkSrcInkSlot I) srcInkNew)
                (forkSrcArtSlot I) srcArtNew)
              (forkDstInkSlot I) dstInkNew)
            (forkDstArtSlot I) dstArtNew)
          I (forkIlkSpotSlot I) = ⟨0⟩ ∨
        UInt256.eq
          (UInt256.div
            (UInt256.mul
              (solcSlotWord
                (sstoreAccountMap I.codeOwner
                  (sstoreAccountMap I.codeOwner
                    (sstoreAccountMap I.codeOwner
                      (sstoreAccountMap I.codeOwner σ (forkSrcInkSlot I) srcInkNew)
                      (forkSrcArtSlot I) srcArtNew)
                    (forkDstInkSlot I) dstInkNew)
                  (forkDstArtSlot I) dstArtNew)
                I (forkDstInkSlot I))
              (solcSlotWord
                (sstoreAccountMap I.codeOwner
                  (sstoreAccountMap I.codeOwner
                    (sstoreAccountMap I.codeOwner
                      (sstoreAccountMap I.codeOwner σ (forkSrcInkSlot I) srcInkNew)
                      (forkSrcArtSlot I) srcArtNew)
                    (forkDstInkSlot I) dstInkNew)
                  (forkDstArtSlot I) dstArtNew)
                I (forkIlkSpotSlot I)))
            (solcSlotWord
              (sstoreAccountMap I.codeOwner
                (sstoreAccountMap I.codeOwner
                  (sstoreAccountMap I.codeOwner
                    (sstoreAccountMap I.codeOwner σ (forkSrcInkSlot I) srcInkNew)
                    (forkSrcArtSlot I) srcArtNew)
                  (forkDstInkSlot I) dstInkNew)
                (forkDstArtSlot I) dstArtNew)
              I (forkIlkSpotSlot I)))
          (solcSlotWord
            (sstoreAccountMap I.codeOwner
              (sstoreAccountMap I.codeOwner
                (sstoreAccountMap I.codeOwner
                  (sstoreAccountMap I.codeOwner σ (forkSrcInkSlot I) srcInkNew)
                  (forkSrcArtSlot I) srcArtNew)
                (forkDstInkSlot I) dstInkNew)
              (forkDstArtSlot I) dstArtNew)
            I (forkDstInkSlot I)) ≠ ⟨0⟩)
    (hsrcDust :
      UInt256.lor
        (UInt256.eq ⟨0⟩
          (solcSlotWord
            (sstoreAccountMap I.codeOwner
              (sstoreAccountMap I.codeOwner
                (sstoreAccountMap I.codeOwner
                  (sstoreAccountMap I.codeOwner σ (forkSrcInkSlot I) srcInkNew)
                  (forkSrcArtSlot I) srcArtNew)
                (forkDstInkSlot I) dstInkNew)
              (forkDstArtSlot I) dstArtNew)
            I (forkSrcArtSlot I)))
        (UInt256.isZero
          (UInt256.lt utab
            (solcSlotWord
              (sstoreAccountMap I.codeOwner
                (sstoreAccountMap I.codeOwner
                  (sstoreAccountMap I.codeOwner
                    (sstoreAccountMap I.codeOwner σ (forkSrcInkSlot I) srcInkNew)
                    (forkSrcArtSlot I) srcArtNew)
                  (forkDstInkSlot I) dstInkNew)
                (forkDstArtSlot I) dstArtNew)
              I (forkIlkDustSlot I)))) ≠ ⟨0⟩)
    (hdstDust :
      UInt256.lor
        (UInt256.eq ⟨0⟩
          (solcSlotWord
            (sstoreAccountMap I.codeOwner
              (sstoreAccountMap I.codeOwner
                (sstoreAccountMap I.codeOwner
                  (sstoreAccountMap I.codeOwner σ (forkSrcInkSlot I) srcInkNew)
                  (forkSrcArtSlot I) srcArtNew)
                (forkDstInkSlot I) dstInkNew)
              (forkDstArtSlot I) dstArtNew)
            I (forkDstArtSlot I)))
        (UInt256.isZero
          (UInt256.lt vtab
            (solcSlotWord
              (sstoreAccountMap I.codeOwner
                (sstoreAccountMap I.codeOwner
                  (sstoreAccountMap I.codeOwner
                    (sstoreAccountMap I.codeOwner σ (forkSrcInkSlot I) srcInkNew)
                    (forkSrcArtSlot I) srcArtNew)
                  (forkDstInkSlot I) dstInkNew)
                (forkDstArtSlot I) dstArtNew)
              I (forkIlkDustSlot I)))) ≠ ⟨0⟩) :
    ∃ k' C', RD vatBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨524⟩ [sel]
      (twoWordHashMem (hopeSourceWord I) (solcMappingSlot ⟨1⟩ (forkDstMaskedWord I))
        (twoWordHashMem (forkDstMaskedWord I) ⟨1⟩
          (twoWordHashMem (hopeSourceWord I) (solcMappingSlot ⟨1⟩ (forkSrcMaskedWord I))
            (twoWordHashMem (forkSrcMaskedWord I) ⟨1⟩
              (twoWordHashMem (forkIlkWord I) ⟨2⟩
                (wordAt0Mem (forkDstMaskedWord I)
                  (twoWordHashMem (forkSrcMaskedWord I)
                    (solcMappingSlot ⟨3⟩ (forkIlkWord I))
                    (twoWordHashMem (forkIlkWord I) ⟨3⟩ mem))))))))
      (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner
            (sstoreAccountMap I.codeOwner σ (forkSrcInkSlot I) srcInkNew)
            (forkSrcArtSlot I) srcArtNew)
          (forkDstInkSlot I) dstInkNew)
        (forkDstArtSlot I) dstArtNew) k' C' := by
  let σSrcInk := sstoreAccountMap I.codeOwner σ (forkSrcInkSlot I) srcInkNew
  let σSrcArt := sstoreAccountMap I.codeOwner σSrcInk (forkSrcArtSlot I) srcArtNew
  let σDstInk := sstoreAccountMap I.codeOwner σSrcArt (forkDstInkSlot I) dstInkNew
  let σDstArt := sstoreAccountMap I.codeOwner σDstInk (forkDstArtSlot I) dstArtNew
  let memPrefix :=
    twoWordHashMem (forkIlkWord I) ⟨2⟩
      (wordAt0Mem (forkDstMaskedWord I)
        (twoWordHashMem (forkSrcMaskedWord I)
          (solcMappingSlot ⟨3⟩ (forkIlkWord I))
          (twoWordHashMem (forkIlkWord I) ⟨3⟩ mem)))
  let memWish :=
    twoWordHashMem (hopeSourceWord I) (solcMappingSlot ⟨1⟩ (forkDstMaskedWord I))
      (twoWordHashMem (forkDstMaskedWord I) ⟨1⟩
        (twoWordHashMem (hopeSourceWord I) (solcMappingSlot ⟨1⟩ (forkSrcMaskedWord I))
          (twoWordHashMem (forkSrcMaskedWord I) ⟨1⟩ memPrefix)))
  obtain ⟨_, _, h4792⟩ := RD.vatForkSrcInkSubSuccess
    (sel := sel) h hmem hsz164 hsrcInkPos hsrcInkNeg
  obtain ⟨_, _, h4809⟩ := RD.vatForkSrcArtSubSuccess
    (sel := sel) (srcInkNew := srcInkNew)
    (by simpa [hsrcInkNewEq] using h4792) hperm
    (by simpa [σSrcInk] using hsrcArtPos)
    (by simpa [σSrcInk] using hsrcArtNeg)
  obtain ⟨_, _, h4826⟩ := RD.vatForkDstInkAddSuccess
    (sel := sel) (srcInkNew := srcInkNew) (srcArtNew := srcArtNew)
    (by simpa [hsrcArtNewEq] using h4809) hperm
    (by simpa [σSrcInk, σSrcArt] using hdstInkNeg)
    (by simpa [σSrcInk, σSrcArt] using hdstInkPos)
  obtain ⟨_, _, h4843⟩ := RD.vatForkDstArtAddSuccess
    (sel := sel) (srcInkNew := srcInkNew) (srcArtNew := srcArtNew)
    (dstInkNew := dstInkNew) (by simpa [hdstInkNewEq] using h4826) hperm
    (by simpa [σSrcInk, σSrcArt, σDstInk] using hdstArtNeg)
    (by simpa [σSrcInk, σSrcArt, σDstInk] using hdstArtPos)
  obtain ⟨_, _, h4871⟩ := RD.vatForkUtabMulSuccess
    (sel := sel) (srcInkNew := srcInkNew) (srcArtNew := srcArtNew)
    (dstInkNew := dstInkNew) (dstArtNew := dstArtNew)
    (by simpa [hdstArtNewEq] using h4843) hperm
    (by simpa [σSrcInk, σSrcArt, σDstInk, σDstArt] using hutabOk)
  obtain ⟨_, _, h4893⟩ := RD.vatForkVtabMulSuccess
    (sel := sel) (srcInkNew := srcInkNew) (srcArtNew := srcArtNew)
    (dstInkNew := dstInkNew) (dstArtNew := dstArtNew) (utab := utab)
    (by simpa [hutabEq] using h4871)
    (by simpa [σSrcInk, σSrcArt, σDstInk, σDstArt] using hvtabOk)
  have hmemPrefix : memPrefix.size = 96 := by
    dsimp [memPrefix]
    apply twoWordHashMem_size_96
    apply wordAt0Mem_size_96
    apply twoWordHashMem_size_96
    apply twoWordHashMem_size_96
    exact hmem
  obtain ⟨_, _, h4990⟩ := RD.vatForkWishSuccess
    (cA := cA) (gh := gh) (bl := bl) (σInit := σ) (σ := σDstArt) (σ₀ := σ₀) (A := A)
    (I := I) (g := g) (sel := sel) (utab := utab) (vtab := vtab)
    (by simpa [memPrefix, σSrcInk, σSrcArt, σDstInk, σDstArt, hvtabEq] using h4893)
    hmemPrefix
    (by simpa [σSrcInk, σSrcArt, σDstInk, σDstArt] using hwish)
  obtain ⟨_, _, h5079⟩ := RD.vatForkSrcUnsafeCheckSuccess
    (cA := cA) (gh := gh) (bl := bl) (σInit := σ) (σ := σDstArt) (σ₀ := σ₀) (A := A)
    (I := I) (g := g) (sel := sel) (utab := utab) (vtab := vtab)
    h4990
    (by simpa [σSrcInk, σSrcArt, σDstInk, σDstArt] using hsrcInkSpotOk)
    (by simpa [σSrcInk, σSrcArt, σDstInk, σDstArt] using hsrcUnsafe)
  obtain ⟨_, _, h5168⟩ := RD.vatForkDstUnsafeCheckSuccess
    (cA := cA) (gh := gh) (bl := bl) (σInit := σ) (σ := σDstArt) (σ₀ := σ₀) (A := A)
    (I := I) (g := g) (sel := sel) (utab := utab) (vtab := vtab)
    h5079
    (by simpa [σSrcInk, σSrcArt, σDstInk, σDstArt] using hdstInkSpotOk)
    (by simpa [σSrcInk, σSrcArt, σDstInk, σDstArt] using hdstUnsafe)
  obtain ⟨_, _, h5344⟩ := RD.vatForkDustChecksSuccess
    (cA := cA) (gh := gh) (bl := bl) (σInit := σ) (σ := σDstArt) (σ₀ := σ₀) (A := A)
    (I := I) (g := g) (sel := sel) (utab := utab) (vtab := vtab)
    h5168
    (by simpa [σSrcInk, σSrcArt, σDstInk, σDstArt] using hsrcDust)
    (by simpa [σSrcInk, σSrcArt, σDstInk, σDstArt] using hdstDust)
  obtain ⟨_, _, h524⟩ := RD.vatForkCleanupSuccess
    (cA := cA) (gh := gh) (bl := bl) (σInit := σ) (σ := σDstArt) (σ₀ := σ₀) (A := A)
    (I := I) (g := g) (sel := sel) (utab := utab) (vtab := vtab) h5344
  exact ⟨_, _, by simpa [memWish, memPrefix, σSrcInk, σSrcArt, σDstInk, σDstArt] using h524⟩

theorem RD.vatForkFinishSuccess
    {cA gh bl σInit σFinal σ₀ A I} {g : Sat256} {sel : UInt256}
    {mem : ByteArray}
    (h : ∃ k C, RD vatBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨524⟩
      [sel] mem (UInt256.ofNat 3) ByteArray.empty (cA, σFinal) k C) :
    RDret vatBytecode g (initState cA gh bl σInit σ₀ g A I)
      (cA, σFinal) ByteArray.empty := by
  obtain ⟨_, _, h524⟩ := h
  have h525 := h524.jumpdest (by native_decide) (by evm_ov)
  exact RD.stop h525 (by native_decide) (by simp)

theorem accountMapEquiv_forkSourceFinal
    {cA gh bl σ σ₀ A I} {g : UInt256}
    (srcInkNew srcArtNew dstInkNew dstArtNew : UInt256)
    (hSrcInk : srcInkNew = forkSrcInkNew σ I)
    (hSrcArt : srcArtNew = forkSrcArtNew σ I)
    (hDstInk : dstInkNew = forkDstInkNew σ I)
    (hDstArt : dstArtNew = forkDstArtNew σ I) :
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    let evm1 := Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner
      (forkSrcInkSlot I) srcInkNew
    let evm2 := Solm.EVM.storageStore evm1 evm1.executionEnv.codeOwner
      (forkSrcArtSlot I) srcArtNew
    let evm3 := Solm.EVM.storageStore evm2 evm2.executionEnv.codeOwner
      (forkDstInkSlot I) dstInkNew
    let evm4 := Solm.EVM.storageStore evm3 evm3.executionEnv.codeOwner
      (forkDstArtSlot I) dstArtNew
    accountMapEquiv (forkAfterDstArt σ I) evm4.accountMap := by
  intro evm0 evm1 evm2 evm3 evm4
  have h0 : accountMapEquiv σ evm0.accountMap := by
    simp [evm0, initState, accountMapEquiv_refl]
  have h1 : accountMapEquiv (forkAfterSrcInk σ I) evm1.accountMap := by
    simpa [evm1, evm0, initState, storageStore_accountMap, forkAfterSrcInk,
      storageStore_executionEnv, hSrcInk] using
      accountMapEquiv_sstoreAccountMap I.codeOwner (forkSrcInkSlot I)
        (forkSrcInkNew σ I) h0
  have h2 : accountMapEquiv (forkAfterSrcArt σ I) evm2.accountMap := by
    simpa [evm2, evm1, evm0, initState, storageStore_accountMap, forkAfterSrcArt,
      storageStore_executionEnv, hSrcArt] using
      accountMapEquiv_sstoreAccountMap I.codeOwner (forkSrcArtSlot I)
        (forkSrcArtNew σ I) h1
  have h3 : accountMapEquiv (forkAfterDstInk σ I) evm3.accountMap := by
    simpa [evm3, evm2, evm1, evm0, initState, storageStore_accountMap,
      forkAfterDstInk, storageStore_executionEnv, hDstInk] using
      accountMapEquiv_sstoreAccountMap I.codeOwner (forkDstInkSlot I)
        (forkDstInkNew σ I) h2
  simpa [evm4, evm3, evm2, evm1, evm0, initState, storageStore_accountMap,
    forkAfterDstArt, storageStore_executionEnv, hDstArt] using
    accountMapEquiv_sstoreAccountMap I.codeOwner (forkDstArtSlot I)
      (forkDstArtNew σ I) h3

theorem forkSourceFinal_createdAccounts
    {cA gh bl σ σ₀ A I} {g : UInt256}
    (srcInkNew srcArtNew dstInkNew dstArtNew : UInt256) :
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    let evm1 := Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner
      (forkSrcInkSlot I) srcInkNew
    let evm2 := Solm.EVM.storageStore evm1 evm1.executionEnv.codeOwner
      (forkSrcArtSlot I) srcArtNew
    let evm3 := Solm.EVM.storageStore evm2 evm2.executionEnv.codeOwner
      (forkDstInkSlot I) dstInkNew
    let evm4 := Solm.EVM.storageStore evm3 evm3.executionEnv.codeOwner
      (forkDstArtSlot I) dstArtNew
    (cA, forkAfterDstArt σ I).1 = evm4.createdAccounts := by
  intro evm0 evm1 evm2 evm3 evm4
  simp [evm4, evm3, evm2, evm1, evm0, initState, storageStore_createdAccounts]

theorem forkSourceFinal_storageLoad
    {cA gh bl σ σ₀ A I} {g : UInt256}
    (srcInkNew srcArtNew dstInkNew dstArtNew slot : UInt256)
    (hSrcInk : srcInkNew = forkSrcInkNew σ I)
    (hSrcArt : srcArtNew = forkSrcArtNew σ I)
    (hDstInk : dstInkNew = forkDstInkNew σ I)
    (hDstArt : dstArtNew = forkDstArtNew σ I) :
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    let evm1 := Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner
      (forkSrcInkSlot I) srcInkNew
    let evm2 := Solm.EVM.storageStore evm1 evm1.executionEnv.codeOwner
      (forkSrcArtSlot I) srcArtNew
    let evm3 := Solm.EVM.storageStore evm2 evm2.executionEnv.codeOwner
      (forkDstInkSlot I) dstInkNew
    let evm4 := Solm.EVM.storageStore evm3 evm3.executionEnv.codeOwner
      (forkDstArtSlot I) dstArtNew
    Solm.EVM.storageLoad evm4 evm4.executionEnv.codeOwner slot =
      solcSlotWord (forkAfterDstArt σ I) I slot := by
  intro evm0 evm1 evm2 evm3 evm4
  have howner : evm4.executionEnv.codeOwner = I.codeOwner := by
    simp [evm4, evm3, evm2, evm1, evm0, initState, storageStore_executionEnv]
  have hmap : evm4.accountMap = forkAfterDstArt σ I := by
    simp [evm4, evm3, evm2, evm1, evm0, initState, storageStore_accountMap,
      storageStore_executionEnv, forkAfterDstArt, forkAfterDstInk, forkAfterSrcArt,
      forkAfterSrcInk, hSrcInk, hSrcArt, hDstInk, hDstArt]
  simp [Solm.EVM.storageLoad, solcSlotWord, State.lookupAccount, Account.lookupStorage,
    howner, hmap]

theorem vatForkSourceSuccessBodyFromFinalGuards
    {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hsz164 : 164 ≤ I.calldata.size)
    (hsrcInkNeg :
      UInt256.sgt (forkDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.gt (forkSrcInkNew σ I)
          (solcSlotWord σ I (forkSrcInkSlot I)) = ⟨0⟩)
    (hsrcInkPos :
      UInt256.slt (forkDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.lt (forkSrcInkNew σ I)
          (solcSlotWord σ I (forkSrcInkSlot I)) = ⟨0⟩)
    (hsrcArtNeg :
      UInt256.sgt (forkDartWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.gt (forkSrcArtNew σ I)
          (solcSlotWord (forkAfterSrcInk σ I) I (forkSrcArtSlot I)) = ⟨0⟩)
    (hsrcArtPos :
      UInt256.slt (forkDartWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.lt (forkSrcArtNew σ I)
          (solcSlotWord (forkAfterSrcInk σ I) I (forkSrcArtSlot I)) = ⟨0⟩)
    (hdstInkNeg :
      UInt256.slt (forkDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.gt (forkDstInkNew σ I)
          (solcSlotWord (forkAfterSrcArt σ I) I (forkDstInkSlot I)) = ⟨0⟩)
    (hdstInkPos :
      UInt256.sgt (forkDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.lt (forkDstInkNew σ I)
          (solcSlotWord (forkAfterSrcArt σ I) I (forkDstInkSlot I)) = ⟨0⟩)
    (hdstArtNeg :
      UInt256.slt (forkDartWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.gt (forkDstArtNew σ I)
          (solcSlotWord (forkAfterDstInk σ I) I (forkDstArtSlot I)) = ⟨0⟩)
    (hdstArtPos :
      UInt256.sgt (forkDartWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.lt (forkDstArtNew σ I)
          (solcSlotWord (forkAfterDstInk σ I) I (forkDstArtSlot I)) = ⟨0⟩)
    (hutabOk :
      solcSlotWord (forkAfterDstArt σ I) I (forkIlkRateSlot I) = ⟨0⟩ ∨
        UInt256.eq
          (UInt256.div
            (UInt256.mul
              (solcSlotWord (forkAfterDstArt σ I) I (forkSrcArtSlot I))
              (solcSlotWord (forkAfterDstArt σ I) I (forkIlkRateSlot I)))
            (solcSlotWord (forkAfterDstArt σ I) I (forkIlkRateSlot I)))
          (solcSlotWord (forkAfterDstArt σ I) I (forkSrcArtSlot I)) ≠ ⟨0⟩)
    (hvtabOk :
      solcSlotWord (forkAfterDstArt σ I) I (forkIlkRateSlot I) = ⟨0⟩ ∨
        UInt256.eq
          (UInt256.div
            (UInt256.mul
              (solcSlotWord (forkAfterDstArt σ I) I (forkDstArtSlot I))
              (solcSlotWord (forkAfterDstArt σ I) I (forkIlkRateSlot I)))
            (solcSlotWord (forkAfterDstArt σ I) I (forkIlkRateSlot I)))
          (solcSlotWord (forkAfterDstArt σ I) I (forkDstArtSlot I)) ≠ ⟨0⟩)
    (hwish : forkBothWishWord (forkAfterDstArt σ I) I ≠ ⟨0⟩)
    (hsrcInkSpotOk :
      solcSlotWord (forkAfterDstArt σ I) I (forkIlkSpotSlot I) = ⟨0⟩ ∨
        UInt256.eq
          (UInt256.div
            (UInt256.mul
              (solcSlotWord (forkAfterDstArt σ I) I (forkSrcInkSlot I))
              (solcSlotWord (forkAfterDstArt σ I) I (forkIlkSpotSlot I)))
            (solcSlotWord (forkAfterDstArt σ I) I (forkIlkSpotSlot I)))
          (solcSlotWord (forkAfterDstArt σ I) I (forkSrcInkSlot I)) ≠ ⟨0⟩)
    (hsrcUnsafe :
      UInt256.gt
        (UInt256.mul
          (solcSlotWord (forkAfterDstArt σ I) I (forkSrcArtSlot I))
          (solcSlotWord (forkAfterDstArt σ I) I (forkIlkRateSlot I)))
        (UInt256.mul
          (solcSlotWord (forkAfterDstArt σ I) I (forkSrcInkSlot I))
          (solcSlotWord (forkAfterDstArt σ I) I (forkIlkSpotSlot I))) = ⟨0⟩)
    (hdstInkSpotOk :
      solcSlotWord (forkAfterDstArt σ I) I (forkIlkSpotSlot I) = ⟨0⟩ ∨
        UInt256.eq
          (UInt256.div
            (UInt256.mul
              (solcSlotWord (forkAfterDstArt σ I) I (forkDstInkSlot I))
              (solcSlotWord (forkAfterDstArt σ I) I (forkIlkSpotSlot I)))
            (solcSlotWord (forkAfterDstArt σ I) I (forkIlkSpotSlot I)))
          (solcSlotWord (forkAfterDstArt σ I) I (forkDstInkSlot I)) ≠ ⟨0⟩)
    (hdstUnsafe :
      UInt256.gt
        (UInt256.mul
          (solcSlotWord (forkAfterDstArt σ I) I (forkDstArtSlot I))
          (solcSlotWord (forkAfterDstArt σ I) I (forkIlkRateSlot I)))
        (UInt256.mul
          (solcSlotWord (forkAfterDstArt σ I) I (forkDstInkSlot I))
          (solcSlotWord (forkAfterDstArt σ I) I (forkIlkSpotSlot I))) = ⟨0⟩)
    (hsrcDust :
      UInt256.lor
        (UInt256.eq ⟨0⟩ (solcSlotWord (forkAfterDstArt σ I) I (forkSrcArtSlot I)))
        (UInt256.isZero
          (UInt256.lt
            (UInt256.mul
              (solcSlotWord (forkAfterDstArt σ I) I (forkSrcArtSlot I))
              (solcSlotWord (forkAfterDstArt σ I) I (forkIlkRateSlot I)))
            (solcSlotWord (forkAfterDstArt σ I) I (forkIlkDustSlot I)))) ≠ ⟨0⟩)
    (hdstDust :
      UInt256.lor
        (UInt256.eq ⟨0⟩ (solcSlotWord (forkAfterDstArt σ I) I (forkDstArtSlot I)))
        (UInt256.isZero
          (UInt256.lt
            (UInt256.mul
              (solcSlotWord (forkAfterDstArt σ I) I (forkDstArtSlot I))
              (solcSlotWord (forkAfterDstArt σ I) I (forkIlkRateSlot I)))
            (solcSlotWord (forkAfterDstArt σ I) I (forkIlkDustSlot I)))) ≠ ⟨0⟩) :
    let srcInkNew := forkSrcInkNew σ I
    let srcArtNew := forkSrcArtNew σ I
    let dstInkNew := forkDstInkNew σ I
    let dstArtNew := forkDstArtNew σ I
    let srcArtFinal := solcSlotWord (forkAfterDstArt σ I) I (forkSrcArtSlot I)
    let dstArtFinal := solcSlotWord (forkAfterDstArt σ I) I (forkDstArtSlot I)
    let srcInkFinal := solcSlotWord (forkAfterDstArt σ I) I (forkSrcInkSlot I)
    let dstInkFinal := solcSlotWord (forkAfterDstArt σ I) I (forkDstInkSlot I)
    let rate := solcSlotWord (forkAfterDstArt σ I) I (forkIlkRateSlot I)
    let spot := solcSlotWord (forkAfterDstArt σ I) I (forkIlkSpotSlot I)
    let dust := solcSlotWord (forkAfterDstArt σ I) I (forkIlkDustSlot I)
    let utab := UInt256.mul srcArtFinal rate
    let vtab := UInt256.mul dstArtFinal rate
    let srcInkSpot := UInt256.mul srcInkFinal spot
    let dstInkSpot := UInt256.mul dstInkFinal spot
    let finalLocals :=
      forkStoreDstInkSpotFinal I srcInkNew srcArtNew dstInkNew dstArtNew
        srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab vtab srcInkSpot dstInkSpot
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    let evm1 := Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner
      (forkSrcInkSlot I) srcInkNew
    let evm2 := Solm.EVM.storageStore evm1 evm1.executionEnv.codeOwner
      (forkSrcArtSlot I) srcArtNew
    let evm3 := Solm.EVM.storageStore evm2 evm2.executionEnv.codeOwner
      (forkDstInkSlot I) dstInkNew
    let evm4 := Solm.EVM.storageStore evm3 evm3.executionEnv.codeOwner
      (forkDstArtSlot I) dstArtNew
    ExecTransitionBody config contract evm0 (forkStore I) forkTransition.body
      (.returned { contract := contract, locals := finalLocals } evm4 none) := by
  intro srcInkNew srcArtNew dstInkNew dstArtNew srcArtFinal dstArtFinal
    srcInkFinal dstInkFinal rate spot dust utab vtab srcInkSpot dstInkSpot finalLocals
    evm0 evm1 evm2 evm3 evm4
  have hloadSrcInk :
      Solm.EVM.storageLoad evm0 evm0.executionEnv.codeOwner (forkSrcInkSlot I) =
        solcSlotWord σ I (forkSrcInkSlot I) := by
    simp [evm0, initState, Solm.EVM.storageLoad, solcSlotWord, State.lookupAccount,
      Account.lookupStorage]
  have hloadSrcArt :
      Solm.EVM.storageLoad evm1 evm1.executionEnv.codeOwner (forkSrcArtSlot I) =
        solcSlotWord (forkAfterSrcInk σ I) I (forkSrcArtSlot I) := by
    simp [evm1, evm0, initState, Solm.EVM.storageLoad, solcSlotWord,
      State.lookupAccount, Account.lookupStorage, storageStore_accountMap,
      storageStore_executionEnv, forkAfterSrcInk, srcInkNew]
  have hloadDstInk :
      Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner (forkDstInkSlot I) =
        solcSlotWord (forkAfterSrcArt σ I) I (forkDstInkSlot I) := by
    simp [evm2, evm1, evm0, initState, Solm.EVM.storageLoad, solcSlotWord,
      State.lookupAccount, Account.lookupStorage, storageStore_accountMap,
      storageStore_executionEnv, forkAfterSrcInk, forkAfterSrcArt, srcInkNew,
      srcArtNew]
  have hloadDstArt :
      Solm.EVM.storageLoad evm3 evm3.executionEnv.codeOwner (forkDstArtSlot I) =
        solcSlotWord (forkAfterDstInk σ I) I (forkDstArtSlot I) := by
    simp [evm3, evm2, evm1, evm0, initState, Solm.EVM.storageLoad, solcSlotWord,
      State.lookupAccount, Account.lookupStorage, storageStore_accountMap,
      storageStore_executionEnv, forkAfterSrcInk, forkAfterSrcArt, forkAfterDstInk,
      srcInkNew, srcArtNew, dstInkNew]
  have hloadFinal (slot : UInt256) :
      Solm.EVM.storageLoad evm4 evm4.executionEnv.codeOwner slot =
        solcSlotWord (forkAfterDstArt σ I) I slot := by
    simpa [evm4, evm3, evm2, evm1, evm0, storageStore_executionEnv, srcInkNew,
      srcArtNew, dstInkNew, dstArtNew] using
      forkSourceFinal_storageLoad (cA := cA) (gh := gh) (bl := bl) (σ := σ)
        (σ₀ := σ₀) (A := A) (I := I) (g := g)
        (forkSrcInkNew σ I) (forkSrcArtNew σ I) (forkDstInkNew σ I)
        (forkDstArtNew σ I) slot rfl rfl rfl rfl
  have hutabFitGuard := forkUintCheckedMulGuard_to_fit_and_source_guard
    (a := srcArtFinal) (b := rate) hutabOk
  have hvtabFitGuard := forkUintCheckedMulGuard_to_fit_and_source_guard
    (a := dstArtFinal) (b := rate) hvtabOk
  have hsrcInkSpotFitGuard := forkUintCheckedMulGuard_to_fit_and_source_guard
    (a := srcInkFinal) (b := spot) hsrcInkSpotOk
  have hdstInkSpotFitGuard := forkUintCheckedMulGuard_to_fit_and_source_guard
    (a := dstInkFinal) (b := spot) hdstInkSpotOk
  exact execForkSourceOk
    (evm0 := evm0) (I := I)
    (solcSlotWord σ I (forkSrcInkSlot I)) srcInkNew
    (solcSlotWord (forkAfterSrcInk σ I) I (forkSrcArtSlot I)) srcArtNew
    (solcSlotWord (forkAfterSrcArt σ I) I (forkDstInkSlot I)) dstInkNew
    (solcSlotWord (forkAfterDstInk σ I) I (forkDstArtSlot I)) dstArtNew
    srcArtFinal dstArtFinal srcInkFinal dstInkFinal rate spot utab vtab
    srcInkSpot dstInkSpot
    (by simpa [evm0, initState] using hwv) hsz164
    hloadSrcInk rfl
    (forkDinkSubGuardNegCond hsrcInkNeg)
    (forkDinkSubGuardPosCond hsrcInkPos)
    (by simpa [evm1, storageStore_executionEnv] using hloadSrcArt) rfl
    (forkDartSubGuardNegCond hsrcArtNeg)
    (forkDartSubGuardPosCond hsrcArtPos)
    (by simpa [evm2, evm1, storageStore_executionEnv] using hloadDstInk) rfl
    (forkDinkAddGuardNegCond hdstInkNeg)
    (forkDinkAddGuardPosCond hdstInkPos)
    (by simpa [evm3, evm2, evm1, storageStore_executionEnv] using hloadDstArt) rfl
    (forkDartAddGuardNegCond hdstArtNeg)
    (forkDartAddGuardPosCond hdstArtPos)
    (by
      simpa [evm4, evm3, evm2, evm1, storageStore_executionEnv, srcArtFinal] using
        hloadFinal (forkSrcArtSlot I))
    (by
      simpa [evm4, evm3, evm2, evm1, storageStore_executionEnv, dstArtFinal] using
        hloadFinal (forkDstArtSlot I))
    (by
      simpa [evm4, evm3, evm2, evm1, storageStore_executionEnv, srcInkFinal] using
        hloadFinal (forkSrcInkSlot I))
    (by
      simpa [evm4, evm3, evm2, evm1, storageStore_executionEnv, dstInkFinal] using
        hloadFinal (forkDstInkSlot I))
    (by
      simpa [evm4, evm3, evm2, evm1, storageStore_executionEnv, rate] using
        hloadFinal (forkIlkRateSlot I))
    (by
      simpa [evm4, evm3, evm2, evm1, storageStore_executionEnv, spot] using
        hloadFinal (forkIlkSpotSlot I))
    rfl hutabFitGuard.1 hutabFitGuard.2
    rfl hvtabFitGuard.1 hvtabFitGuard.2
    rfl hsrcInkSpotFitGuard.1 hsrcInkSpotFitGuard.2
    rfl hdstInkSpotFitGuard.1 hdstInkSpotFitGuard.2
    (by
      exact evalExpr_fork_wish_both_true_of_word_final_store
        (evm := evm4) (σ := forkAfterDstArt σ I) (I := I)
        srcInkNew srcArtNew dstInkNew dstArtNew srcArtFinal dstArtFinal
        srcInkFinal dstInkFinal utab vtab srcInkSpot dstInkSpot
        (by simp [evm4, evm3, evm2, evm1, evm0, initState, storageStore_executionEnv])
        (by simpa [vatSlotWord] using hloadFinal (forkSrcWishSlot I))
        (by simpa [vatSlotWord] using hloadFinal (forkDstWishSlot I))
        hwish)
    (evalExpr_fork_utab_le_srcInkSpot_final_store
      (evm := evm4) (I := I) srcInkNew srcArtNew dstInkNew dstArtNew
      srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab vtab srcInkSpot
      dstInkSpot (by simpa [utab, srcInkSpot] using ugt_eq_zero_to_le hsrcUnsafe))
    (evalExpr_fork_vtab_le_dstInkSpot_final_store
      (evm := evm4) (I := I) srcInkNew srcArtNew dstInkNew dstArtNew
      srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab vtab srcInkSpot
      dstInkSpot (by simpa [vtab, dstInkSpot] using ugt_eq_zero_to_le hdstUnsafe))
    (evalExpr_fork_src_dust_final_store
      (evm := evm4) (I := I) srcInkNew srcArtNew dstInkNew dstArtNew
      srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab vtab srcInkSpot
      dstInkSpot dust hsz164
      (by simpa [dust] using hloadFinal (forkIlkDustSlot I))
      (by simpa [srcArtFinal, utab, dust] using forkDustSourceCond_of_evm hsrcDust))
    (evalExpr_fork_dst_dust_final_store
      (evm := evm4) (I := I) srcInkNew srcArtNew dstInkNew dstArtNew
      srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab vtab srcInkSpot
      dstInkSpot dust hsz164
      (by simpa [dust] using hloadFinal (forkIlkDustSlot I))
      (by simpa [dstArtFinal, vtab, dust] using forkDustSourceCond_of_evm hdstDust))

theorem vatForkSourceRevertBodyFromFinalBlock
    {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hsz164 : 164 ≤ I.calldata.size)
    (hsrcInkNeg :
      UInt256.sgt (forkDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.gt (forkSrcInkNew σ I)
          (solcSlotWord σ I (forkSrcInkSlot I)) = ⟨0⟩)
    (hsrcInkPos :
      UInt256.slt (forkDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.lt (forkSrcInkNew σ I)
          (solcSlotWord σ I (forkSrcInkSlot I)) = ⟨0⟩)
    (hsrcArtNeg :
      UInt256.sgt (forkDartWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.gt (forkSrcArtNew σ I)
          (solcSlotWord (forkAfterSrcInk σ I) I (forkSrcArtSlot I)) = ⟨0⟩)
    (hsrcArtPos :
      UInt256.slt (forkDartWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.lt (forkSrcArtNew σ I)
          (solcSlotWord (forkAfterSrcInk σ I) I (forkSrcArtSlot I)) = ⟨0⟩)
    (hdstInkNeg :
      UInt256.slt (forkDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.gt (forkDstInkNew σ I)
          (solcSlotWord (forkAfterSrcArt σ I) I (forkDstInkSlot I)) = ⟨0⟩)
    (hdstInkPos :
      UInt256.sgt (forkDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.lt (forkDstInkNew σ I)
          (solcSlotWord (forkAfterSrcArt σ I) I (forkDstInkSlot I)) = ⟨0⟩)
    (hdstArtNeg :
      UInt256.slt (forkDartWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.gt (forkDstArtNew σ I)
          (solcSlotWord (forkAfterDstInk σ I) I (forkDstArtSlot I)) = ⟨0⟩)
    (hdstArtPos :
      UInt256.sgt (forkDartWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.lt (forkDstArtNew σ I)
          (solcSlotWord (forkAfterDstInk σ I) I (forkDstArtSlot I)) = ⟨0⟩)
    (hutabOk :
      solcSlotWord (forkAfterDstArt σ I) I (forkIlkRateSlot I) = ⟨0⟩ ∨
        UInt256.eq
          (UInt256.div
            (UInt256.mul
              (solcSlotWord (forkAfterDstArt σ I) I (forkSrcArtSlot I))
              (solcSlotWord (forkAfterDstArt σ I) I (forkIlkRateSlot I)))
            (solcSlotWord (forkAfterDstArt σ I) I (forkIlkRateSlot I)))
          (solcSlotWord (forkAfterDstArt σ I) I (forkSrcArtSlot I)) ≠ ⟨0⟩)
    (hvtabOk :
      solcSlotWord (forkAfterDstArt σ I) I (forkIlkRateSlot I) = ⟨0⟩ ∨
        UInt256.eq
          (UInt256.div
            (UInt256.mul
              (solcSlotWord (forkAfterDstArt σ I) I (forkDstArtSlot I))
              (solcSlotWord (forkAfterDstArt σ I) I (forkIlkRateSlot I)))
            (solcSlotWord (forkAfterDstArt σ I) I (forkIlkRateSlot I)))
          (solcSlotWord (forkAfterDstArt σ I) I (forkDstArtSlot I)) ≠ ⟨0⟩)
    (hsrcInkSpotOk :
      solcSlotWord (forkAfterDstArt σ I) I (forkIlkSpotSlot I) = ⟨0⟩ ∨
        UInt256.eq
          (UInt256.div
            (UInt256.mul
              (solcSlotWord (forkAfterDstArt σ I) I (forkSrcInkSlot I))
              (solcSlotWord (forkAfterDstArt σ I) I (forkIlkSpotSlot I)))
            (solcSlotWord (forkAfterDstArt σ I) I (forkIlkSpotSlot I)))
          (solcSlotWord (forkAfterDstArt σ I) I (forkSrcInkSlot I)) ≠ ⟨0⟩)
    (hdstInkSpotOk :
      solcSlotWord (forkAfterDstArt σ I) I (forkIlkSpotSlot I) = ⟨0⟩ ∨
        UInt256.eq
          (UInt256.div
            (UInt256.mul
              (solcSlotWord (forkAfterDstArt σ I) I (forkDstInkSlot I))
              (solcSlotWord (forkAfterDstArt σ I) I (forkIlkSpotSlot I)))
            (solcSlotWord (forkAfterDstArt σ I) I (forkIlkSpotSlot I)))
          (solcSlotWord (forkAfterDstArt σ I) I (forkDstInkSlot I)) ≠ ⟨0⟩) :
    let srcInkNew := forkSrcInkNew σ I
    let srcArtNew := forkSrcArtNew σ I
    let dstInkNew := forkDstInkNew σ I
    let dstArtNew := forkDstArtNew σ I
    let srcArtFinal := solcSlotWord (forkAfterDstArt σ I) I (forkSrcArtSlot I)
    let dstArtFinal := solcSlotWord (forkAfterDstArt σ I) I (forkDstArtSlot I)
    let srcInkFinal := solcSlotWord (forkAfterDstArt σ I) I (forkSrcInkSlot I)
    let dstInkFinal := solcSlotWord (forkAfterDstArt σ I) I (forkDstInkSlot I)
    let rate := solcSlotWord (forkAfterDstArt σ I) I (forkIlkRateSlot I)
    let spot := solcSlotWord (forkAfterDstArt σ I) I (forkIlkSpotSlot I)
    let utab := UInt256.mul srcArtFinal rate
    let vtab := UInt256.mul dstArtFinal rate
    let srcInkSpot := UInt256.mul srcInkFinal spot
    let dstInkSpot := UInt256.mul dstInkFinal spot
    let finalLocals :=
      forkStoreDstInkSpotFinal I srcInkNew srcArtNew dstInkNew dstArtNew
        srcArtFinal dstArtFinal srcInkFinal dstInkFinal utab vtab srcInkSpot dstInkSpot
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    let evm1 := Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner
      (forkSrcInkSlot I) srcInkNew
    let evm2 := Solm.EVM.storageStore evm1 evm1.executionEnv.codeOwner
      (forkSrcArtSlot I) srcArtNew
    let evm3 := Solm.EVM.storageStore evm2 evm2.executionEnv.codeOwner
      (forkDstInkSlot I) dstInkNew
    let evm4 := Solm.EVM.storageStore evm3 evm3.executionEnv.codeOwner
      (forkDstArtSlot I) dstArtNew
    ExecBlock config { contract := contract, locals := finalLocals } evm4
      [ .require (bothExpr (wishExpr (.var "src") sender) (wishExpr (.var "dst") sender)),
        .require (.binary .le (.var "utab") (.var "srcInkSpot")),
        .require (.binary .le (.var "vtab") (.var "dstInkSpot")),
        .require
          (eitherExpr
            (.binary .ge (.var "utab") (.storage (ilksF (.var "ilk") "dust")))
            (.binary .eq (.var "srcArtFinal") (.intLit 0))),
        .require
          (eitherExpr
            (.binary .ge (.var "vtab") (.storage (ilksF (.var "ilk") "dust")))
            (.binary .eq (.var "dstArtFinal") (.intLit 0))) ]
      .reverted →
    ExecTransitionBody config contract evm0 (forkStore I) forkTransition.body .reverted := by
  intro srcInkNew srcArtNew dstInkNew dstArtNew srcArtFinal dstArtFinal
    srcInkFinal dstInkFinal rate spot utab vtab srcInkSpot dstInkSpot finalLocals
    evm0 evm1 evm2 evm3 evm4 hfinalBlock
  have hloadSrcInk :
      Solm.EVM.storageLoad evm0 evm0.executionEnv.codeOwner (forkSrcInkSlot I) =
        solcSlotWord σ I (forkSrcInkSlot I) := by
    simp [evm0, initState, Solm.EVM.storageLoad, solcSlotWord, State.lookupAccount,
      Account.lookupStorage]
  have hloadSrcArt :
      Solm.EVM.storageLoad evm1 evm1.executionEnv.codeOwner (forkSrcArtSlot I) =
        solcSlotWord (forkAfterSrcInk σ I) I (forkSrcArtSlot I) := by
    simp [evm1, evm0, initState, Solm.EVM.storageLoad, solcSlotWord,
      State.lookupAccount, Account.lookupStorage, storageStore_accountMap,
      storageStore_executionEnv, forkAfterSrcInk, srcInkNew]
  have hloadDstInk :
      Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner (forkDstInkSlot I) =
        solcSlotWord (forkAfterSrcArt σ I) I (forkDstInkSlot I) := by
    simp [evm2, evm1, evm0, initState, Solm.EVM.storageLoad, solcSlotWord,
      State.lookupAccount, Account.lookupStorage, storageStore_accountMap,
      storageStore_executionEnv, forkAfterSrcInk, forkAfterSrcArt, srcInkNew,
      srcArtNew]
  have hloadDstArt :
      Solm.EVM.storageLoad evm3 evm3.executionEnv.codeOwner (forkDstArtSlot I) =
        solcSlotWord (forkAfterDstInk σ I) I (forkDstArtSlot I) := by
    simp [evm3, evm2, evm1, evm0, initState, Solm.EVM.storageLoad, solcSlotWord,
      State.lookupAccount, Account.lookupStorage, storageStore_accountMap,
      storageStore_executionEnv, forkAfterSrcInk, forkAfterSrcArt, forkAfterDstInk,
      srcInkNew, srcArtNew, dstInkNew]
  have hloadFinal (slot : UInt256) :
      Solm.EVM.storageLoad evm4 evm4.executionEnv.codeOwner slot =
        solcSlotWord (forkAfterDstArt σ I) I slot := by
    simpa [evm4, evm3, evm2, evm1, evm0, storageStore_executionEnv, srcInkNew,
      srcArtNew, dstInkNew, dstArtNew] using
      forkSourceFinal_storageLoad (cA := cA) (gh := gh) (bl := bl) (σ := σ)
        (σ₀ := σ₀) (A := A) (I := I) (g := g)
        (forkSrcInkNew σ I) (forkSrcArtNew σ I) (forkDstInkNew σ I)
        (forkDstArtNew σ I) slot rfl rfl rfl rfl
  have hutabFitGuard := forkUintCheckedMulGuard_to_fit_and_source_guard
    (a := srcArtFinal) (b := rate) hutabOk
  have hvtabFitGuard := forkUintCheckedMulGuard_to_fit_and_source_guard
    (a := dstArtFinal) (b := rate) hvtabOk
  have hsrcInkSpotFitGuard := forkUintCheckedMulGuard_to_fit_and_source_guard
    (a := srcInkFinal) (b := spot) hsrcInkSpotOk
  have hdstInkSpotFitGuard := forkUintCheckedMulGuard_to_fit_and_source_guard
    (a := dstInkFinal) (b := spot) hdstInkSpotOk
  exact execForkSourceRevertFinal
    (evm0 := evm0) (I := I)
    (solcSlotWord σ I (forkSrcInkSlot I)) srcInkNew
    (solcSlotWord (forkAfterSrcInk σ I) I (forkSrcArtSlot I)) srcArtNew
    (solcSlotWord (forkAfterSrcArt σ I) I (forkDstInkSlot I)) dstInkNew
    (solcSlotWord (forkAfterDstInk σ I) I (forkDstArtSlot I)) dstArtNew
    srcArtFinal dstArtFinal srcInkFinal dstInkFinal rate spot utab vtab
    srcInkSpot dstInkSpot
    (by simpa [evm0, initState] using hwv) hsz164
    hloadSrcInk rfl
    (forkDinkSubGuardNegCond hsrcInkNeg)
    (forkDinkSubGuardPosCond hsrcInkPos)
    (by simpa [evm1, storageStore_executionEnv] using hloadSrcArt) rfl
    (forkDartSubGuardNegCond hsrcArtNeg)
    (forkDartSubGuardPosCond hsrcArtPos)
    (by simpa [evm2, evm1, storageStore_executionEnv] using hloadDstInk) rfl
    (forkDinkAddGuardNegCond hdstInkNeg)
    (forkDinkAddGuardPosCond hdstInkPos)
    (by simpa [evm3, evm2, evm1, storageStore_executionEnv] using hloadDstArt) rfl
    (forkDartAddGuardNegCond hdstArtNeg)
    (forkDartAddGuardPosCond hdstArtPos)
    (by
      simpa [evm4, evm3, evm2, evm1, storageStore_executionEnv, srcArtFinal] using
        hloadFinal (forkSrcArtSlot I))
    (by
      simpa [evm4, evm3, evm2, evm1, storageStore_executionEnv, dstArtFinal] using
        hloadFinal (forkDstArtSlot I))
    (by
      simpa [evm4, evm3, evm2, evm1, storageStore_executionEnv, srcInkFinal] using
        hloadFinal (forkSrcInkSlot I))
    (by
      simpa [evm4, evm3, evm2, evm1, storageStore_executionEnv, dstInkFinal] using
        hloadFinal (forkDstInkSlot I))
    (by
      simpa [evm4, evm3, evm2, evm1, storageStore_executionEnv, rate] using
        hloadFinal (forkIlkRateSlot I))
    (by
      simpa [evm4, evm3, evm2, evm1, storageStore_executionEnv, spot] using
        hloadFinal (forkIlkSpotSlot I))
    rfl hutabFitGuard.1 hutabFitGuard.2
    rfl hvtabFitGuard.1 hvtabFitGuard.2
    rfl hsrcInkSpotFitGuard.1 hsrcInkSpotFitGuard.2
    rfl hdstInkSpotFitGuard.1 hdstInkSpotFitGuard.2
    hfinalBlock

theorem vatForkSuccessEquivFromFinalState
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {evmFinal : EVM.State} {finalLocals : Store}
    (hcode : I.code = vatBytecode)
    (hdispatch : dispatchMsg contract I.calldata = some forkTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (forkTransition.params.map Param.name)
        (transitionSignature forkTransition).paramTypes I.calldata = some (forkStore I))
    (hret : RDret vatBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
      (cA, forkAfterDstArt σ_evm I) ByteArray.empty)
    (hbody :
      ExecTransitionBody config contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (forkStore I) forkTransition.body
        (.returned { contract := contract, locals := finalLocals } evmFinal none))
    (hcreated : (cA, forkAfterDstArt σ_evm I).1 = evmFinal.createdAccounts)
    (haccounts : accountMapEquiv (cA, forkAfterDstArt σ_evm I).2 evmFinal.accountMap) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have henc : returnEquiv ByteArray.empty none forkTransition.returnType := by
    rw [show forkTransition.returnType = [] by rfl]
    exact returnEquiv.fallthrough rfl (by rfl) (by native_decide)
  exact hret.reEquivExecutionGenAccountMapEquiv hcode hdispatch hdecode hbody
    hcreated haccounts henc

theorem vatForkSuccessEquivFromSourceFinal
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {finalLocals : Store}
    (hcode : I.code = vatBytecode)
    (hdispatch : dispatchMsg contract I.calldata = some forkTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (forkTransition.params.map Param.name)
        (transitionSignature forkTransition).paramTypes I.calldata = some (forkStore I))
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hret : RDret vatBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
      (cA, forkAfterDstArt σ_evm I) ByteArray.empty)
    (hbody :
      let srcInkNew := forkSrcInkNew σ_solm I
      let srcArtNew := forkSrcArtNew σ_solm I
      let dstInkNew := forkDstInkNew σ_solm I
      let dstArtNew := forkDstArtNew σ_solm I
      let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
      let evm1 := Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner
        (forkSrcInkSlot I) srcInkNew
      let evm2 := Solm.EVM.storageStore evm1 evm1.executionEnv.codeOwner
        (forkSrcArtSlot I) srcArtNew
      let evm3 := Solm.EVM.storageStore evm2 evm2.executionEnv.codeOwner
        (forkDstInkSlot I) dstInkNew
      let evm4 := Solm.EVM.storageStore evm3 evm3.executionEnv.codeOwner
        (forkDstArtSlot I) dstArtNew
      ExecTransitionBody config contract evm0 (forkStore I) forkTransition.body
        (.returned { contract := contract, locals := finalLocals } evm4 none)) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  dsimp at hbody
  have hcreated :=
    forkSourceFinal_createdAccounts (cA := cA) (gh := gh) (bl := bl)
      (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
      (forkSrcInkNew σ_solm I) (forkSrcArtNew σ_solm I)
      (forkDstInkNew σ_solm I) (forkDstArtNew σ_solm I)
  have hsourceAccounts :=
    accountMapEquiv_forkSourceFinal (cA := cA) (gh := gh) (bl := bl)
      (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
      (forkSrcInkNew σ_solm I) (forkSrcArtNew σ_solm I)
      (forkDstInkNew σ_solm I) (forkDstArtNew σ_solm I)
      rfl rfl rfl rfl
  have haccounts :
      accountMapEquiv (forkAfterDstArt σ_evm I)
        (Solm.EVM.storageStore
          (Solm.EVM.storageStore
            (Solm.EVM.storageStore
              (Solm.EVM.storageStore
                (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
                (forkSrcInkSlot I) (forkSrcInkNew σ_solm I))
              (Solm.EVM.storageStore
                (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
                (forkSrcInkSlot I) (forkSrcInkNew σ_solm I)).executionEnv.codeOwner
              (forkSrcArtSlot I) (forkSrcArtNew σ_solm I))
            (Solm.EVM.storageStore
              (Solm.EVM.storageStore
                (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
                (forkSrcInkSlot I) (forkSrcInkNew σ_solm I))
              (Solm.EVM.storageStore
                (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
                (forkSrcInkSlot I) (forkSrcInkNew σ_solm I)).executionEnv.codeOwner
              (forkSrcArtSlot I) (forkSrcArtNew σ_solm I)).executionEnv.codeOwner
            (forkDstInkSlot I) (forkDstInkNew σ_solm I))
          (Solm.EVM.storageStore
            (Solm.EVM.storageStore
              (Solm.EVM.storageStore
                (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
                (forkSrcInkSlot I) (forkSrcInkNew σ_solm I))
              (Solm.EVM.storageStore
                (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
                (forkSrcInkSlot I) (forkSrcInkNew σ_solm I)).executionEnv.codeOwner
              (forkSrcArtSlot I) (forkSrcArtNew σ_solm I))
            (Solm.EVM.storageStore
              (Solm.EVM.storageStore
                (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
                (forkSrcInkSlot I) (forkSrcInkNew σ_solm I))
              (Solm.EVM.storageStore
                (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
                (forkSrcInkSlot I) (forkSrcInkNew σ_solm I)).executionEnv.codeOwner
              (forkSrcArtSlot I) (forkSrcArtNew σ_solm I)).executionEnv.codeOwner
            (forkDstInkSlot I) (forkDstInkNew σ_solm I)).executionEnv.codeOwner
          (forkDstArtSlot I) (forkDstArtNew σ_solm I)).accountMap := by
    exact (accountMapEquiv_forkAfterDstArt hAccounts).trans hsourceAccounts
  exact vatForkSuccessEquivFromFinalState hcode hdispatch hdecode hret hbody
    (by simpa using hcreated) haccounts

set_option maxHeartbeats 0 in
theorem vatForkSuccessEquivFromFinalGuards
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = vatBytecode)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (vatSelBytes 10))
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsz164 : 164 ≤ I.calldata.size)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (forkTransition.params.map Param.name)
        (transitionSignature forkTransition).paramTypes I.calldata = some (forkStore I))
    (hdecoded :
      ∃ k C, RD vatBytecode I (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨4726⟩
        [forkDartWord I, forkDinkWord I, forkDstMaskedWord I, forkSrcMaskedWord I,
          forkIlkWord I, ⟨524⟩, vatSelWord I]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hsrcInkNeg :
      UInt256.sgt (forkDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.gt (forkSrcInkNew σ_evm I)
          (solcSlotWord σ_evm I (forkSrcInkSlot I)) = ⟨0⟩)
    (hsrcInkPos :
      UInt256.slt (forkDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.lt (forkSrcInkNew σ_evm I)
          (solcSlotWord σ_evm I (forkSrcInkSlot I)) = ⟨0⟩)
    (hsrcArtNeg :
      UInt256.sgt (forkDartWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.gt (forkSrcArtNew σ_evm I)
          (solcSlotWord (forkAfterSrcInk σ_evm I) I (forkSrcArtSlot I)) = ⟨0⟩)
    (hsrcArtPos :
      UInt256.slt (forkDartWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.lt (forkSrcArtNew σ_evm I)
          (solcSlotWord (forkAfterSrcInk σ_evm I) I (forkSrcArtSlot I)) = ⟨0⟩)
    (hdstInkNeg :
      UInt256.slt (forkDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.gt (forkDstInkNew σ_evm I)
          (solcSlotWord (forkAfterSrcArt σ_evm I) I (forkDstInkSlot I)) = ⟨0⟩)
    (hdstInkPos :
      UInt256.sgt (forkDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.lt (forkDstInkNew σ_evm I)
          (solcSlotWord (forkAfterSrcArt σ_evm I) I (forkDstInkSlot I)) = ⟨0⟩)
    (hdstArtNeg :
      UInt256.slt (forkDartWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.gt (forkDstArtNew σ_evm I)
          (solcSlotWord (forkAfterDstInk σ_evm I) I (forkDstArtSlot I)) = ⟨0⟩)
    (hdstArtPos :
      UInt256.sgt (forkDartWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.lt (forkDstArtNew σ_evm I)
          (solcSlotWord (forkAfterDstInk σ_evm I) I (forkDstArtSlot I)) = ⟨0⟩)
    (hutabOk :
      solcSlotWord (forkAfterDstArt σ_evm I) I (forkIlkRateSlot I) = ⟨0⟩ ∨
        UInt256.eq
          (UInt256.div
            (UInt256.mul
              (solcSlotWord (forkAfterDstArt σ_evm I) I (forkSrcArtSlot I))
              (solcSlotWord (forkAfterDstArt σ_evm I) I (forkIlkRateSlot I)))
            (solcSlotWord (forkAfterDstArt σ_evm I) I (forkIlkRateSlot I)))
          (solcSlotWord (forkAfterDstArt σ_evm I) I (forkSrcArtSlot I)) ≠ ⟨0⟩)
    (hvtabOk :
      solcSlotWord (forkAfterDstArt σ_evm I) I (forkIlkRateSlot I) = ⟨0⟩ ∨
        UInt256.eq
          (UInt256.div
            (UInt256.mul
              (solcSlotWord (forkAfterDstArt σ_evm I) I (forkDstArtSlot I))
              (solcSlotWord (forkAfterDstArt σ_evm I) I (forkIlkRateSlot I)))
            (solcSlotWord (forkAfterDstArt σ_evm I) I (forkIlkRateSlot I)))
          (solcSlotWord (forkAfterDstArt σ_evm I) I (forkDstArtSlot I)) ≠ ⟨0⟩)
    (hwish : forkBothWishWord (forkAfterDstArt σ_evm I) I ≠ ⟨0⟩)
    (hsrcInkSpotOk :
      solcSlotWord (forkAfterDstArt σ_evm I) I (forkIlkSpotSlot I) = ⟨0⟩ ∨
        UInt256.eq
          (UInt256.div
            (UInt256.mul
              (solcSlotWord (forkAfterDstArt σ_evm I) I (forkSrcInkSlot I))
              (solcSlotWord (forkAfterDstArt σ_evm I) I (forkIlkSpotSlot I)))
            (solcSlotWord (forkAfterDstArt σ_evm I) I (forkIlkSpotSlot I)))
          (solcSlotWord (forkAfterDstArt σ_evm I) I (forkSrcInkSlot I)) ≠ ⟨0⟩)
    (hsrcUnsafe :
      UInt256.gt
        (UInt256.mul
          (solcSlotWord (forkAfterDstArt σ_evm I) I (forkSrcArtSlot I))
          (solcSlotWord (forkAfterDstArt σ_evm I) I (forkIlkRateSlot I)))
        (UInt256.mul
          (solcSlotWord (forkAfterDstArt σ_evm I) I (forkSrcInkSlot I))
          (solcSlotWord (forkAfterDstArt σ_evm I) I (forkIlkSpotSlot I))) = ⟨0⟩)
    (hdstInkSpotOk :
      solcSlotWord (forkAfterDstArt σ_evm I) I (forkIlkSpotSlot I) = ⟨0⟩ ∨
        UInt256.eq
          (UInt256.div
            (UInt256.mul
              (solcSlotWord (forkAfterDstArt σ_evm I) I (forkDstInkSlot I))
              (solcSlotWord (forkAfterDstArt σ_evm I) I (forkIlkSpotSlot I)))
            (solcSlotWord (forkAfterDstArt σ_evm I) I (forkIlkSpotSlot I)))
          (solcSlotWord (forkAfterDstArt σ_evm I) I (forkDstInkSlot I)) ≠ ⟨0⟩)
    (hdstUnsafe :
      UInt256.gt
        (UInt256.mul
          (solcSlotWord (forkAfterDstArt σ_evm I) I (forkDstArtSlot I))
          (solcSlotWord (forkAfterDstArt σ_evm I) I (forkIlkRateSlot I)))
        (UInt256.mul
          (solcSlotWord (forkAfterDstArt σ_evm I) I (forkDstInkSlot I))
          (solcSlotWord (forkAfterDstArt σ_evm I) I (forkIlkSpotSlot I))) = ⟨0⟩)
    (hsrcDust :
      UInt256.lor
        (UInt256.eq ⟨0⟩ (solcSlotWord (forkAfterDstArt σ_evm I) I (forkSrcArtSlot I)))
        (UInt256.isZero
          (UInt256.lt
            (UInt256.mul
              (solcSlotWord (forkAfterDstArt σ_evm I) I (forkSrcArtSlot I))
              (solcSlotWord (forkAfterDstArt σ_evm I) I (forkIlkRateSlot I)))
            (solcSlotWord (forkAfterDstArt σ_evm I) I (forkIlkDustSlot I)))) ≠ ⟨0⟩)
    (hdstDust :
      UInt256.lor
        (UInt256.eq ⟨0⟩ (solcSlotWord (forkAfterDstArt σ_evm I) I (forkDstArtSlot I)))
        (UInt256.isZero
          (UInt256.lt
            (UInt256.mul
              (solcSlotWord (forkAfterDstArt σ_evm I) I (forkDstArtSlot I))
              (solcSlotWord (forkAfterDstArt σ_evm I) I (forkIlkRateSlot I)))
            (solcSlotWord (forkAfterDstArt σ_evm I) I (forkIlkDustSlot I)))) ≠ ⟨0⟩) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let utab :=
    UInt256.mul
      (solcSlotWord (forkAfterDstArt σ_evm I) I (forkSrcArtSlot I))
      (solcSlotWord (forkAfterDstArt σ_evm I) I (forkIlkRateSlot I))
  let vtab :=
    UInt256.mul
      (solcSlotWord (forkAfterDstArt σ_evm I) I (forkDstArtSlot I))
      (solcSlotWord (forkAfterDstArt σ_evm I) I (forkIlkRateSlot I))
  obtain ⟨_, _, hdecodedRD⟩ := hdecoded
  have hpath := RD.vatForkSuccessPath
    (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
    (I := I) (g := Sat256.ofUInt256 g) (sel := vatSelWord I)
    (srcInkNew := forkSrcInkNew σ_evm I) (srcArtNew := forkSrcArtNew σ_evm I)
    (dstInkNew := forkDstInkNew σ_evm I) (dstArtNew := forkDstArtNew σ_evm I)
    (utab := utab) (vtab := vtab)
    hdecodedRD solcFreePtrMem_size hsz164 hperm
    (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
    (by simpa [forkSrcInkNew] using hsrcInkNeg)
    (by simpa [forkSrcInkNew] using hsrcInkPos)
    (by simpa [forkAfterSrcInk, forkSrcArtNew] using hsrcArtNeg)
    (by simpa [forkAfterSrcInk, forkSrcArtNew] using hsrcArtPos)
    (by simpa [forkAfterSrcInk, forkAfterSrcArt, forkDstInkNew] using hdstInkNeg)
    (by simpa [forkAfterSrcInk, forkAfterSrcArt, forkDstInkNew] using hdstInkPos)
    (by
      simpa [forkAfterSrcInk, forkAfterSrcArt, forkAfterDstInk, forkDstArtNew] using
        hdstArtNeg)
    (by
      simpa [forkAfterSrcInk, forkAfterSrcArt, forkAfterDstInk, forkDstArtNew] using
        hdstArtPos)
    (by
      simpa [utab, forkAfterDstArt, forkAfterDstInk, forkAfterSrcArt, forkAfterSrcInk] using
        hutabOk)
    (by
      simpa [vtab, forkAfterDstArt, forkAfterDstInk, forkAfterSrcArt, forkAfterSrcInk] using
        hvtabOk)
    (by
      simpa [forkAfterDstArt, forkAfterDstInk, forkAfterSrcArt, forkAfterSrcInk] using
        hwish)
    (by
      simpa [utab, forkAfterDstArt, forkAfterDstInk, forkAfterSrcArt, forkAfterSrcInk] using
        hsrcUnsafe)
    (by
      simpa [vtab, forkAfterDstArt, forkAfterDstInk, forkAfterSrcArt, forkAfterSrcInk] using
        hdstUnsafe)
    (by
      simpa [forkAfterDstArt, forkAfterDstInk, forkAfterSrcArt, forkAfterSrcInk] using
        hsrcInkSpotOk)
    (by
      simpa [forkAfterDstArt, forkAfterDstInk, forkAfterSrcArt, forkAfterSrcInk] using
        hdstInkSpotOk)
    (by
      simpa [utab, forkAfterDstArt, forkAfterDstInk, forkAfterSrcArt, forkAfterSrcInk] using
        hsrcDust)
    (by
      simpa [vtab, forkAfterDstArt, forkAfterDstInk, forkAfterSrcArt, forkAfterSrcInk] using
        hdstDust)
  have hret := RD.vatForkFinishSuccess
    (cA := cA) (gh := gh) (bl := bl) (σInit := σ_evm)
    (σFinal := forkAfterDstArt σ_evm I) (σ₀ := σ₀) (A := A) (I := I)
    (g := Sat256.ofUInt256 g) (sel := vatSelWord I) hpath
  have hsrcInkNegS :=
    (forkSrcInkSubGuardNeg_iff_of_accountMapEquiv (I := I) hAccounts).mp hsrcInkNeg
  have hsrcInkPosS :=
    (forkSrcInkSubGuardPos_iff_of_accountMapEquiv (I := I) hAccounts).mp hsrcInkPos
  have hsrcArtNegS :=
    (forkSrcArtSubGuardNeg_iff_of_accountMapEquiv (I := I) hAccounts).mp hsrcArtNeg
  have hsrcArtPosS :=
    (forkSrcArtSubGuardPos_iff_of_accountMapEquiv (I := I) hAccounts).mp hsrcArtPos
  have hdstInkNegS :=
    (forkDstInkAddGuardNeg_iff_of_accountMapEquiv (I := I) hAccounts).mp hdstInkNeg
  have hdstInkPosS :=
    (forkDstInkAddGuardPos_iff_of_accountMapEquiv (I := I) hAccounts).mp hdstInkPos
  have hdstArtNegS :=
    (forkDstArtAddGuardNeg_iff_of_accountMapEquiv (I := I) hAccounts).mp hdstArtNeg
  have hdstArtPosS :=
    (forkDstArtAddGuardPos_iff_of_accountMapEquiv (I := I) hAccounts).mp hdstArtPos
  have hAfterAccounts := accountMapEquiv_forkAfterDstArt (I := I) hAccounts
  have hutabOkS :=
    (forkAfterDstArt_mulGuard_iff_of_accountMapEquiv (I := I) hAccounts
      (forkSrcArtSlot I) (forkIlkRateSlot I)).mp hutabOk
  have hvtabOkS :=
    (forkAfterDstArt_mulGuard_iff_of_accountMapEquiv (I := I) hAccounts
      (forkDstArtSlot I) (forkIlkRateSlot I)).mp hvtabOk
  have hwishS : forkBothWishWord (forkAfterDstArt σ_solm I) I ≠ ⟨0⟩ := by
    have heq := forkBothWishWord_eq_of_accountMapEquiv (I := I) hAfterAccounts
    rwa [← heq]
  have hsrcInkSpotOkS :=
    (forkAfterDstArt_mulGuard_iff_of_accountMapEquiv (I := I) hAccounts
      (forkSrcInkSlot I) (forkIlkSpotSlot I)).mp hsrcInkSpotOk
  have hdstInkSpotOkS :=
    (forkAfterDstArt_mulGuard_iff_of_accountMapEquiv (I := I) hAccounts
      (forkDstInkSlot I) (forkIlkSpotSlot I)).mp hdstInkSpotOk
  have hsrcTabEq :
      UInt256.mul
          (solcSlotWord (forkAfterDstArt σ_evm I) I (forkSrcArtSlot I))
          (solcSlotWord (forkAfterDstArt σ_evm I) I (forkIlkRateSlot I)) =
        UInt256.mul
          (solcSlotWord (forkAfterDstArt σ_solm I) I (forkSrcArtSlot I))
          (solcSlotWord (forkAfterDstArt σ_solm I) I (forkIlkRateSlot I)) := by
    have hart := forkAfterDstArt_slot_eq_of_accountMapEquiv (I := I) hAccounts
      (forkSrcArtSlot I)
    have hrate := forkAfterDstArt_slot_eq_of_accountMapEquiv (I := I) hAccounts
      (forkIlkRateSlot I)
    simp [hart, hrate]
  have hdstTabEq :
      UInt256.mul
          (solcSlotWord (forkAfterDstArt σ_evm I) I (forkDstArtSlot I))
          (solcSlotWord (forkAfterDstArt σ_evm I) I (forkIlkRateSlot I)) =
        UInt256.mul
          (solcSlotWord (forkAfterDstArt σ_solm I) I (forkDstArtSlot I))
          (solcSlotWord (forkAfterDstArt σ_solm I) I (forkIlkRateSlot I)) := by
    have hart := forkAfterDstArt_slot_eq_of_accountMapEquiv (I := I) hAccounts
      (forkDstArtSlot I)
    have hrate := forkAfterDstArt_slot_eq_of_accountMapEquiv (I := I) hAccounts
      (forkIlkRateSlot I)
    simp [hart, hrate]
  have hsrcUnsafeS :=
    (forkAfterDstArt_unsafeGuard_iff_of_accountMapEquiv (I := I) hAccounts
      (UInt256.mul
        (solcSlotWord (forkAfterDstArt σ_solm I) I (forkSrcArtSlot I))
        (solcSlotWord (forkAfterDstArt σ_solm I) I (forkIlkRateSlot I)))
      (forkSrcInkSlot I) (forkIlkSpotSlot I)).mp (by
        simpa [hsrcTabEq] using hsrcUnsafe)
  have hdstUnsafeS :=
    (forkAfterDstArt_unsafeGuard_iff_of_accountMapEquiv (I := I) hAccounts
      (UInt256.mul
        (solcSlotWord (forkAfterDstArt σ_solm I) I (forkDstArtSlot I))
        (solcSlotWord (forkAfterDstArt σ_solm I) I (forkIlkRateSlot I)))
      (forkDstInkSlot I) (forkIlkSpotSlot I)).mp (by
        simpa [hdstTabEq] using hdstUnsafe)
  have hsrcDustS :=
    (forkAfterDstArt_dustGuard_iff_of_accountMapEquiv (I := I) hAccounts
      (UInt256.mul
        (solcSlotWord (forkAfterDstArt σ_solm I) I (forkSrcArtSlot I))
        (solcSlotWord (forkAfterDstArt σ_solm I) I (forkIlkRateSlot I)))
      (forkSrcArtSlot I) (forkIlkDustSlot I)).mp (by
        simpa [hsrcTabEq] using hsrcDust)
  have hdstDustS :=
    (forkAfterDstArt_dustGuard_iff_of_accountMapEquiv (I := I) hAccounts
      (UInt256.mul
        (solcSlotWord (forkAfterDstArt σ_solm I) I (forkDstArtSlot I))
        (solcSlotWord (forkAfterDstArt σ_solm I) I (forkIlkRateSlot I)))
      (forkDstArtSlot I) (forkIlkDustSlot I)).mp (by
        simpa [hdstTabEq] using hdstDust)
  have hbody :=
    vatForkSourceSuccessBodyFromFinalGuards
      (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀)
      (A := A) (I := I) (g := g)
      hwv hsz164 hsrcInkNegS hsrcInkPosS hsrcArtNegS hsrcArtPosS
      hdstInkNegS hdstInkPosS hdstArtNegS hdstArtPosS
      hutabOkS hvtabOkS hwishS hsrcInkSpotOkS hsrcUnsafeS
      hdstInkSpotOkS hdstUnsafeS hsrcDustS hdstDustS
  exact vatForkSuccessEquivFromSourceFinal hcode (vatDispatchFork hsel) hdecode
    hAccounts hret hbody

set_option maxHeartbeats 0 in
theorem vatForkBodyCore : VatBodyTheorem 10 := by
  intro cA gh bl σ_evm σ_solm σ₀ A I g hcode hsize hperm hwv hsel hAccounts
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (vatSelBytes 10) rfl hsel
  have hreach := vatReachForkBody (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
    (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz4 hsize hsel
  by_cases hsz164 : 164 ≤ I.calldata.size
  · have hdecode := vatDecode_fork_ok (I := I) hsz164
    obtain ⟨_, _, hdecoded⟩ := vatForkX_decoded
      (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
      (A := A) (I := I) (g := Sat256.ofUInt256 g)
      hsz164 hsize hreach
    by_cases hsrcInkNeg :
        UInt256.sgt (forkDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
          UInt256.gt (forkSrcInkNew σ_evm I)
            (solcSlotWord σ_evm I (forkSrcInkSlot I)) = ⟨0⟩
    · by_cases hsrcInkPos :
          UInt256.slt (forkDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
            UInt256.lt (forkSrcInkNew σ_evm I)
              (solcSlotWord σ_evm I (forkSrcInkSlot I)) = ⟨0⟩
      · by_cases hsrcArtNeg :
            UInt256.sgt (forkDartWord I) ⟨0⟩ = ⟨0⟩ ∨
              UInt256.gt (forkSrcArtNew σ_evm I)
                (solcSlotWord (forkAfterSrcInk σ_evm I) I (forkSrcArtSlot I)) = ⟨0⟩
        · by_cases hsrcArtPos :
              UInt256.slt (forkDartWord I) ⟨0⟩ = ⟨0⟩ ∨
                UInt256.lt (forkSrcArtNew σ_evm I)
                  (solcSlotWord (forkAfterSrcInk σ_evm I) I (forkSrcArtSlot I)) = ⟨0⟩
          · by_cases hdstInkNeg :
                UInt256.slt (forkDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
                  UInt256.gt (forkDstInkNew σ_evm I)
                    (solcSlotWord (forkAfterSrcArt σ_evm I) I (forkDstInkSlot I)) = ⟨0⟩
            · by_cases hdstInkPos :
                  UInt256.sgt (forkDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
                    UInt256.lt (forkDstInkNew σ_evm I)
                      (solcSlotWord (forkAfterSrcArt σ_evm I) I (forkDstInkSlot I)) = ⟨0⟩
              · by_cases hdstArtNeg :
                    UInt256.slt (forkDartWord I) ⟨0⟩ = ⟨0⟩ ∨
                      UInt256.gt (forkDstArtNew σ_evm I)
                        (solcSlotWord (forkAfterDstInk σ_evm I) I (forkDstArtSlot I)) = ⟨0⟩
                · by_cases hdstArtPos :
                    UInt256.sgt (forkDartWord I) ⟨0⟩ = ⟨0⟩ ∨
                      UInt256.lt (forkDstArtNew σ_evm I)
                        (solcSlotWord (forkAfterDstInk σ_evm I) I (forkDstArtSlot I)) = ⟨0⟩
                  · let σFinal := forkAfterDstArt σ_evm I
                    by_cases hsuccess :
                        (solcSlotWord σFinal I (forkIlkRateSlot I) = ⟨0⟩ ∨
                          UInt256.eq
                            (UInt256.div
                              (UInt256.mul
                                (solcSlotWord σFinal I (forkSrcArtSlot I))
                                (solcSlotWord σFinal I (forkIlkRateSlot I)))
                              (solcSlotWord σFinal I (forkIlkRateSlot I)))
                            (solcSlotWord σFinal I (forkSrcArtSlot I)) ≠ ⟨0⟩) ∧
                        (solcSlotWord σFinal I (forkIlkRateSlot I) = ⟨0⟩ ∨
                          UInt256.eq
                            (UInt256.div
                              (UInt256.mul
                                (solcSlotWord σFinal I (forkDstArtSlot I))
                                (solcSlotWord σFinal I (forkIlkRateSlot I)))
                              (solcSlotWord σFinal I (forkIlkRateSlot I)))
                            (solcSlotWord σFinal I (forkDstArtSlot I)) ≠ ⟨0⟩) ∧
                        forkBothWishWord σFinal I ≠ ⟨0⟩ ∧
                        (solcSlotWord σFinal I (forkIlkSpotSlot I) = ⟨0⟩ ∨
                          UInt256.eq
                            (UInt256.div
                              (UInt256.mul
                                (solcSlotWord σFinal I (forkSrcInkSlot I))
                                (solcSlotWord σFinal I (forkIlkSpotSlot I)))
                              (solcSlotWord σFinal I (forkIlkSpotSlot I)))
                            (solcSlotWord σFinal I (forkSrcInkSlot I)) ≠ ⟨0⟩) ∧
                        UInt256.gt
                          (UInt256.mul
                            (solcSlotWord σFinal I (forkSrcArtSlot I))
                            (solcSlotWord σFinal I (forkIlkRateSlot I)))
                          (UInt256.mul
                            (solcSlotWord σFinal I (forkSrcInkSlot I))
                            (solcSlotWord σFinal I (forkIlkSpotSlot I))) = ⟨0⟩ ∧
                        (solcSlotWord σFinal I (forkIlkSpotSlot I) = ⟨0⟩ ∨
                          UInt256.eq
                            (UInt256.div
                              (UInt256.mul
                                (solcSlotWord σFinal I (forkDstInkSlot I))
                                (solcSlotWord σFinal I (forkIlkSpotSlot I)))
                              (solcSlotWord σFinal I (forkIlkSpotSlot I)))
                            (solcSlotWord σFinal I (forkDstInkSlot I)) ≠ ⟨0⟩) ∧
                        UInt256.gt
                          (UInt256.mul
                            (solcSlotWord σFinal I (forkDstArtSlot I))
                            (solcSlotWord σFinal I (forkIlkRateSlot I)))
                          (UInt256.mul
                            (solcSlotWord σFinal I (forkDstInkSlot I))
                            (solcSlotWord σFinal I (forkIlkSpotSlot I))) = ⟨0⟩ ∧
                        UInt256.lor
                          (UInt256.eq ⟨0⟩ (solcSlotWord σFinal I (forkSrcArtSlot I)))
                          (UInt256.isZero
                            (UInt256.lt
                              (UInt256.mul
                                (solcSlotWord σFinal I (forkSrcArtSlot I))
                                (solcSlotWord σFinal I (forkIlkRateSlot I)))
                              (solcSlotWord σFinal I (forkIlkDustSlot I)))) ≠ ⟨0⟩ ∧
                        UInt256.lor
                          (UInt256.eq ⟨0⟩ (solcSlotWord σFinal I (forkDstArtSlot I)))
                          (UInt256.isZero
                            (UInt256.lt
                              (UInt256.mul
                                (solcSlotWord σFinal I (forkDstArtSlot I))
                                (solcSlotWord σFinal I (forkIlkRateSlot I)))
                              (solcSlotWord σFinal I (forkIlkDustSlot I)))) ≠ ⟨0⟩
                    · rcases hsuccess with
                        ⟨hutabOk, hvtabOk, hwish, hsrcInkSpotOk, hsrcUnsafe,
                          hdstInkSpotOk, hdstUnsafe, hsrcDust, hdstDust⟩
                      exact vatForkSuccessEquivFromFinalGuards
                        (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm)
                        (σ_solm := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
                        hcode hperm hwv hsel hAccounts hsz164 hdecode
                        ⟨_, _, hdecoded⟩
                        hsrcInkNeg hsrcInkPos hsrcArtNeg hsrcArtPos hdstInkNeg
                        hdstInkPos hdstArtNeg hdstArtPos
                        (by simpa [σFinal] using hutabOk)
                        (by simpa [σFinal] using hvtabOk)
                        (by simpa [σFinal] using hwish)
                        (by simpa [σFinal] using hsrcInkSpotOk)
                        (by simpa [σFinal] using hsrcUnsafe)
                        (by simpa [σFinal] using hdstInkSpotOk)
                        (by simpa [σFinal] using hdstUnsafe)
                        (by simpa [σFinal] using hsrcDust)
                        (by simpa [σFinal] using hdstDust)
                    · by_cases hutabOk :
                        (solcSlotWord σFinal I (forkIlkRateSlot I) = ⟨0⟩ ∨
                          UInt256.eq
                            (UInt256.div
                              (UInt256.mul
                                (solcSlotWord σFinal I (forkSrcArtSlot I))
                                (solcSlotWord σFinal I (forkIlkRateSlot I)))
                              (solcSlotWord σFinal I (forkIlkRateSlot I)))
                            (solcSlotWord σFinal I (forkSrcArtSlot I)) ≠ ⟨0⟩)
                      · by_cases hvtabOk :
                          (solcSlotWord σFinal I (forkIlkRateSlot I) = ⟨0⟩ ∨
                            UInt256.eq
                              (UInt256.div
                                (UInt256.mul
                                  (solcSlotWord σFinal I (forkDstArtSlot I))
                                  (solcSlotWord σFinal I (forkIlkRateSlot I)))
                                (solcSlotWord σFinal I (forkIlkRateSlot I)))
                              (solcSlotWord σFinal I (forkDstArtSlot I)) ≠ ⟨0⟩)
                        · by_cases hsrcInkSpotOk :
                            (solcSlotWord σFinal I (forkIlkSpotSlot I) = ⟨0⟩ ∨
                              UInt256.eq
                                (UInt256.div
                                  (UInt256.mul
                                    (solcSlotWord σFinal I (forkSrcInkSlot I))
                                    (solcSlotWord σFinal I (forkIlkSpotSlot I)))
                                  (solcSlotWord σFinal I (forkIlkSpotSlot I)))
                                (solcSlotWord σFinal I (forkSrcInkSlot I)) ≠ ⟨0⟩)
                          · by_cases hdstInkSpotOk :
                              (solcSlotWord σFinal I (forkIlkSpotSlot I) = ⟨0⟩ ∨
                                UInt256.eq
                                    (UInt256.div
                                      (UInt256.mul
                                        (solcSlotWord σFinal I (forkDstInkSlot I))
                                        (solcSlotWord σFinal I (forkIlkSpotSlot I)))
                                      (solcSlotWord σFinal I (forkIlkSpotSlot I)))
                                    (solcSlotWord σFinal I (forkDstInkSlot I)) ≠ ⟨0⟩)
                            · have hsrcInkNegS :
                                  UInt256.sgt (forkDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
                                    UInt256.gt (forkSrcInkNew σ_solm I)
                                      (solcSlotWord σ_solm I (forkSrcInkSlot I)) = ⟨0⟩ :=
                                (forkSrcInkSubGuardNeg_iff_of_accountMapEquiv (I := I)
                                  hAccounts).mp hsrcInkNeg
                              have hsrcInkPosS :
                                  UInt256.slt (forkDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
                                    UInt256.lt (forkSrcInkNew σ_solm I)
                                      (solcSlotWord σ_solm I (forkSrcInkSlot I)) = ⟨0⟩ :=
                                (forkSrcInkSubGuardPos_iff_of_accountMapEquiv (I := I)
                                  hAccounts).mp hsrcInkPos
                              have hsrcArtNegS :
                                  UInt256.sgt (forkDartWord I) ⟨0⟩ = ⟨0⟩ ∨
                                    UInt256.gt (forkSrcArtNew σ_solm I)
                                      (solcSlotWord (forkAfterSrcInk σ_solm I) I
                                        (forkSrcArtSlot I)) = ⟨0⟩ :=
                                (forkSrcArtSubGuardNeg_iff_of_accountMapEquiv (I := I)
                                  hAccounts).mp hsrcArtNeg
                              have hsrcArtPosS :
                                  UInt256.slt (forkDartWord I) ⟨0⟩ = ⟨0⟩ ∨
                                    UInt256.lt (forkSrcArtNew σ_solm I)
                                      (solcSlotWord (forkAfterSrcInk σ_solm I) I
                                        (forkSrcArtSlot I)) = ⟨0⟩ :=
                                (forkSrcArtSubGuardPos_iff_of_accountMapEquiv (I := I)
                                  hAccounts).mp hsrcArtPos
                              have hdstInkNegS :
                                  UInt256.slt (forkDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
                                    UInt256.gt (forkDstInkNew σ_solm I)
                                      (solcSlotWord (forkAfterSrcArt σ_solm I) I
                                        (forkDstInkSlot I)) = ⟨0⟩ :=
                                (forkDstInkAddGuardNeg_iff_of_accountMapEquiv (I := I)
                                  hAccounts).mp hdstInkNeg
                              have hdstInkPosS :
                                  UInt256.sgt (forkDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
                                    UInt256.lt (forkDstInkNew σ_solm I)
                                      (solcSlotWord (forkAfterSrcArt σ_solm I) I
                                        (forkDstInkSlot I)) = ⟨0⟩ :=
                                (forkDstInkAddGuardPos_iff_of_accountMapEquiv (I := I)
                                  hAccounts).mp hdstInkPos
                              have hdstArtNegS :
                                  UInt256.slt (forkDartWord I) ⟨0⟩ = ⟨0⟩ ∨
                                    UInt256.gt (forkDstArtNew σ_solm I)
                                      (solcSlotWord (forkAfterDstInk σ_solm I) I
                                        (forkDstArtSlot I)) = ⟨0⟩ :=
                                (forkDstArtAddGuardNeg_iff_of_accountMapEquiv (I := I)
                                  hAccounts).mp hdstArtNeg
                              have hdstArtPosS :
                                  UInt256.sgt (forkDartWord I) ⟨0⟩ = ⟨0⟩ ∨
                                    UInt256.lt (forkDstArtNew σ_solm I)
                                      (solcSlotWord (forkAfterDstInk σ_solm I) I
                                        (forkDstArtSlot I)) = ⟨0⟩ :=
                                (forkDstArtAddGuardPos_iff_of_accountMapEquiv (I := I)
                                  hAccounts).mp hdstArtPos
                              have hutabOkS :
                                  solcSlotWord (forkAfterDstArt σ_solm I) I
                                        (forkIlkRateSlot I) = ⟨0⟩ ∨
                                      UInt256.eq
                                        (UInt256.div
                                          (UInt256.mul
                                            (solcSlotWord (forkAfterDstArt σ_solm I) I
                                              (forkSrcArtSlot I))
                                            (solcSlotWord (forkAfterDstArt σ_solm I) I
                                              (forkIlkRateSlot I)))
                                          (solcSlotWord (forkAfterDstArt σ_solm I) I
                                            (forkIlkRateSlot I)))
                                        (solcSlotWord (forkAfterDstArt σ_solm I) I
                                          (forkSrcArtSlot I)) ≠ ⟨0⟩ := by
                                have hart := forkAfterDstArt_slot_eq_of_accountMapEquiv
                                  (I := I) hAccounts (forkSrcArtSlot I)
                                have hrate := forkAfterDstArt_slot_eq_of_accountMapEquiv
                                  (I := I) hAccounts (forkIlkRateSlot I)
                                simpa [σFinal, hart, hrate] using hutabOk
                              have hvtabOkS :
                                  solcSlotWord (forkAfterDstArt σ_solm I) I
                                        (forkIlkRateSlot I) = ⟨0⟩ ∨
                                      UInt256.eq
                                        (UInt256.div
                                          (UInt256.mul
                                            (solcSlotWord (forkAfterDstArt σ_solm I) I
                                              (forkDstArtSlot I))
                                            (solcSlotWord (forkAfterDstArt σ_solm I) I
                                              (forkIlkRateSlot I)))
                                          (solcSlotWord (forkAfterDstArt σ_solm I) I
                                            (forkIlkRateSlot I)))
                                        (solcSlotWord (forkAfterDstArt σ_solm I) I
                                          (forkDstArtSlot I)) ≠ ⟨0⟩ := by
                                have hart := forkAfterDstArt_slot_eq_of_accountMapEquiv
                                  (I := I) hAccounts (forkDstArtSlot I)
                                have hrate := forkAfterDstArt_slot_eq_of_accountMapEquiv
                                  (I := I) hAccounts (forkIlkRateSlot I)
                                simpa [σFinal, hart, hrate] using hvtabOk
                              have hsrcInkSpotOkS :
                                  solcSlotWord (forkAfterDstArt σ_solm I) I
                                        (forkIlkSpotSlot I) = ⟨0⟩ ∨
                                      UInt256.eq
                                        (UInt256.div
                                          (UInt256.mul
                                            (solcSlotWord (forkAfterDstArt σ_solm I) I
                                              (forkSrcInkSlot I))
                                            (solcSlotWord (forkAfterDstArt σ_solm I) I
                                              (forkIlkSpotSlot I)))
                                          (solcSlotWord (forkAfterDstArt σ_solm I) I
                                            (forkIlkSpotSlot I)))
                                        (solcSlotWord (forkAfterDstArt σ_solm I) I
                                          (forkSrcInkSlot I)) ≠ ⟨0⟩ := by
                                have hink := forkAfterDstArt_slot_eq_of_accountMapEquiv
                                  (I := I) hAccounts (forkSrcInkSlot I)
                                have hspot := forkAfterDstArt_slot_eq_of_accountMapEquiv
                                  (I := I) hAccounts (forkIlkSpotSlot I)
                                simpa [σFinal, hink, hspot] using hsrcInkSpotOk
                              have hdstInkSpotOkS :
                                  solcSlotWord (forkAfterDstArt σ_solm I) I
                                        (forkIlkSpotSlot I) = ⟨0⟩ ∨
                                      UInt256.eq
                                        (UInt256.div
                                          (UInt256.mul
                                            (solcSlotWord (forkAfterDstArt σ_solm I) I
                                              (forkDstInkSlot I))
                                            (solcSlotWord (forkAfterDstArt σ_solm I) I
                                              (forkIlkSpotSlot I)))
                                          (solcSlotWord (forkAfterDstArt σ_solm I) I
                                            (forkIlkSpotSlot I)))
                                        (solcSlotWord (forkAfterDstArt σ_solm I) I
                                          (forkDstInkSlot I)) ≠ ⟨0⟩ := by
                                have hink := forkAfterDstArt_slot_eq_of_accountMapEquiv
                                  (I := I) hAccounts (forkDstInkSlot I)
                                have hspot := forkAfterDstArt_slot_eq_of_accountMapEquiv
                                  (I := I) hAccounts (forkIlkSpotSlot I)
                                simpa [σFinal, hink, hspot] using hdstInkSpotOk
                              let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
                              let evm1 := Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner
                                (forkSrcInkSlot I) (forkSrcInkNew σ_solm I)
                              let evm2 := Solm.EVM.storageStore evm1 evm1.executionEnv.codeOwner
                                (forkSrcArtSlot I) (forkSrcArtNew σ_solm I)
                              let evm3 := Solm.EVM.storageStore evm2 evm2.executionEnv.codeOwner
                                (forkDstInkSlot I) (forkDstInkNew σ_solm I)
                              let evm4 := Solm.EVM.storageStore evm3 evm3.executionEnv.codeOwner
                                (forkDstArtSlot I) (forkDstArtNew σ_solm I)
                              let σFinalS := forkAfterDstArt σ_solm I
                              let srcArtFinalS := solcSlotWord σFinalS I (forkSrcArtSlot I)
                              let dstArtFinalS := solcSlotWord σFinalS I (forkDstArtSlot I)
                              let srcInkFinalS := solcSlotWord σFinalS I (forkSrcInkSlot I)
                              let dstInkFinalS := solcSlotWord σFinalS I (forkDstInkSlot I)
                              let rateS := solcSlotWord σFinalS I (forkIlkRateSlot I)
                              let spotS := solcSlotWord σFinalS I (forkIlkSpotSlot I)
                              let utabS := UInt256.mul srcArtFinalS rateS
                              let vtabS := UInt256.mul dstArtFinalS rateS
                              let srcInkSpotS := UInt256.mul srcInkFinalS spotS
                              let dstInkSpotS := UInt256.mul dstInkFinalS spotS
                              let finalLocalsS :=
                                forkStoreDstInkSpotFinal I
                                  (forkSrcInkNew σ_solm I) (forkSrcArtNew σ_solm I)
                                  (forkDstInkNew σ_solm I) (forkDstArtNew σ_solm I)
                                  srcArtFinalS dstArtFinalS srcInkFinalS dstInkFinalS
                                  utabS vtabS srcInkSpotS dstInkSpotS
                              have hloadFinalS (slot : UInt256) :
                                  Solm.EVM.storageLoad evm4 evm4.executionEnv.codeOwner slot =
                                    solcSlotWord σFinalS I slot := by
                                simpa [evm4, evm3, evm2, evm1, evm0, σFinalS,
                                  storageStore_executionEnv] using
                                    forkSourceFinal_storageLoad (cA := cA) (gh := gh)
                                      (bl := bl) (σ := σ_solm) (σ₀ := σ₀) (A := A)
                                      (I := I) (g := g)
                                      (forkSrcInkNew σ_solm I) (forkSrcArtNew σ_solm I)
                                      (forkDstInkNew σ_solm I) (forkDstArtNew σ_solm I)
                                      slot rfl rfl rfl rfl
                              have hsourceBodyOf :
                                  ExecBlock config { contract := contract, locals := finalLocalsS } evm4
                                    [ .require (bothExpr (wishExpr (.var "src") sender)
                                        (wishExpr (.var "dst") sender)),
                                      .require (.binary .le (.var "utab") (.var "srcInkSpot")),
                                      .require (.binary .le (.var "vtab") (.var "dstInkSpot")),
                                      .require
                                        (eitherExpr
                                          (.binary .ge (.var "utab")
                                            (.storage (ilksF (.var "ilk") "dust")))
                                          (.binary .eq (.var "srcArtFinal") (.intLit 0))),
                                      .require
                                        (eitherExpr
                                          (.binary .ge (.var "vtab")
                                            (.storage (ilksF (.var "ilk") "dust")))
                                          (.binary .eq (.var "dstArtFinal") (.intLit 0))) ]
                                    .reverted →
                                  ExecTransitionBody config contract evm0 (forkStore I)
                                    forkTransition.body .reverted := by
                                intro hfinal
                                simpa [evm0, evm1, evm2, evm3, evm4, σFinalS,
                                  srcArtFinalS, dstArtFinalS, srcInkFinalS, dstInkFinalS,
                                  rateS, spotS, utabS, vtabS, srcInkSpotS, dstInkSpotS,
                                  finalLocalsS] using
                                  vatForkSourceRevertBodyFromFinalBlock
                                    (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm)
                                    (σ₀ := σ₀) (A := A) (I := I) (g := g)
                                    hwv hsz164 hsrcInkNegS hsrcInkPosS hsrcArtNegS
                                    hsrcArtPosS hdstInkNegS hdstInkPosS hdstArtNegS
                                    hdstArtPosS hutabOkS hvtabOkS hsrcInkSpotOkS
                                    hdstInkSpotOkS hfinal
                              have hsourceEq : evm4.executionEnv.source = I.source := by
                                simp [evm4, evm3, evm2, evm1, evm0, initState,
                                  storageStore_executionEnv]
                              obtain ⟨_, _, h4792⟩ := RD.vatForkSrcInkSubSuccess
                                (h := hdecoded) solcFreePtrMem_size hsz164
                                (by simpa [forkSrcInkNew] using hsrcInkNeg)
                                (by simpa [forkSrcInkNew] using hsrcInkPos)
                              obtain ⟨_, _, h4809⟩ := RD.vatForkSrcArtSubSuccess
                                (h := by simpa [forkSrcInkNew] using h4792) hperm
                                (by simpa [forkSrcArtNew, forkAfterSrcInk] using hsrcArtNeg)
                                (by simpa [forkSrcArtNew, forkAfterSrcInk] using hsrcArtPos)
                              obtain ⟨_, _, h4826⟩ := RD.vatForkDstInkAddSuccess
                                (h := by simpa [forkSrcArtNew, forkAfterSrcInk] using h4809)
                                hperm
                                (by simpa [forkDstInkNew, forkAfterSrcArt] using hdstInkNeg)
                                (by simpa [forkDstInkNew, forkAfterSrcArt] using hdstInkPos)
                              obtain ⟨_, _, h4843⟩ := RD.vatForkDstArtAddSuccess
                                (h := by simpa [forkDstInkNew, forkAfterSrcArt] using h4826)
                                hperm
                                (by simpa [forkDstArtNew, forkAfterDstInk] using hdstArtNeg)
                                (by simpa [forkDstArtNew, forkAfterDstInk] using hdstArtPos)
                              obtain ⟨_, _, h4871⟩ := RD.vatForkUtabMulSuccess
                                (h := by
                                  simpa [σFinal, forkAfterDstArt, forkDstArtNew,
                                    forkAfterDstInk] using h4843)
                                hperm
                                (by simpa [σFinal, forkAfterDstArt, forkDstArtNew,
                                  forkAfterDstInk] using hutabOk)
                              obtain ⟨_, _, h4893⟩ := RD.vatForkVtabMulSuccess
                                (h := by
                                  simpa [σFinal, forkAfterDstArt, forkDstArtNew,
                                    forkAfterDstInk] using h4871)
                                (by simpa [σFinal, forkAfterDstArt, forkDstArtNew,
                                  forkAfterDstInk] using hvtabOk)
                              let memPrefix :=
                                twoWordHashMem (forkIlkWord I) ⟨2⟩
                                  (wordAt0Mem (forkDstMaskedWord I)
                                    (twoWordHashMem (forkSrcMaskedWord I)
                                      (solcMappingSlot ⟨3⟩ (forkIlkWord I))
                                      (twoWordHashMem (forkIlkWord I) ⟨3⟩ solcFreePtrMem)))
                              have hmemPrefix : memPrefix.size = 96 := by
                                dsimp [memPrefix]
                                apply twoWordHashMem_size_96
                                apply wordAt0Mem_size_96
                                apply twoWordHashMem_size_96
                                apply twoWordHashMem_size_96
                                exact solcFreePtrMem_size
                              have hread64Prefix :
                                  memPrefix.readWithPadding 64 32 =
                                    UInt256.toByteArray ⟨128⟩ := by
                                dsimp [memPrefix]
                                apply twoWordHashMem_read64
                                · apply wordAt0Mem_size_96
                                  apply twoWordHashMem_size_96
                                  apply twoWordHashMem_size_96
                                  exact solcFreePtrMem_size
                                · rw [wordAt0Mem_read64]
                                  apply twoWordHashMem_read64
                                  · apply twoWordHashMem_size_96
                                    exact solcFreePtrMem_size
                                  · apply twoWordHashMem_read64
                                    · exact solcFreePtrMem_size
                                    · exact solcFreePtrMem_read64
                                  · apply twoWordHashMem_size_96
                                    apply twoWordHashMem_size_96
                                    exact solcFreePtrMem_size
                              by_cases hwish : forkBothWishWord σFinal I ≠ ⟨0⟩
                              · obtain ⟨_, _, h4990⟩ := RD.vatForkWishSuccess
                                  (h := by
                                    simpa [σFinal, forkAfterDstArt, forkDstArtNew,
                                      forkAfterDstInk, memPrefix] using h4893)
                                  hmemPrefix
                                  (by simpa [σFinal] using hwish)
                                let memSrc : ByteArray :=
                                  twoWordHashMem (hopeSourceWord I)
                                    (solcMappingSlot (⟨1⟩ : UInt256) (forkSrcMaskedWord I))
                                    (twoWordHashMem (forkSrcMaskedWord I)
                                      (⟨1⟩ : UInt256) memPrefix)
                                let memWish : ByteArray :=
                                  twoWordHashMem (hopeSourceWord I)
                                    (solcMappingSlot (⟨1⟩ : UInt256) (forkDstMaskedWord I))
                                    (twoWordHashMem (forkDstMaskedWord I)
                                      (⟨1⟩ : UInt256) memSrc)
                                have hmemSrc : memSrc.size = 96 := by
                                  dsimp [memSrc]
                                  apply twoWordHashMem_size_96
                                  apply twoWordHashMem_size_96
                                  exact hmemPrefix
                                have hmemWish : memWish.size = 96 := by
                                  dsimp [memWish]
                                  apply twoWordHashMem_size_96
                                  apply twoWordHashMem_size_96
                                  exact hmemSrc
                                have hread64Src :
                                    memSrc.readWithPadding 64 32 =
                                      UInt256.toByteArray ⟨128⟩ := by
                                  dsimp [memSrc]
                                  apply twoWordHashMem_read64
                                  · apply twoWordHashMem_size_96
                                    exact hmemPrefix
                                  · exact twoWordHashMem_read64
                                      (forkSrcMaskedWord I) ⟨1⟩ hmemPrefix hread64Prefix
                                have hread64Wish :
                                    memWish.readWithPadding 64 32 =
                                      UInt256.toByteArray ⟨128⟩ := by
                                  dsimp [memWish]
                                  apply twoWordHashMem_read64
                                  · apply twoWordHashMem_size_96
                                    exact hmemSrc
                                  · exact twoWordHashMem_read64
                                      (forkDstMaskedWord I) ⟨1⟩ hmemSrc hread64Src
                                let srcUnsafeWord : UInt256 :=
                                  UInt256.gt
                                    (UInt256.mul
                                      (solcSlotWord σFinal I (forkSrcArtSlot I))
                                      (solcSlotWord σFinal I (forkIlkRateSlot I)))
                                    (UInt256.mul
                                      (solcSlotWord σFinal I (forkSrcInkSlot I))
                                      (solcSlotWord σFinal I (forkIlkSpotSlot I)))
                                by_cases hsrcUnsafe : srcUnsafeWord = UInt256.ofNat 0
                                · obtain ⟨_, _, h5079⟩ := RD.vatForkSrcUnsafeCheckSuccess
                                    (h := by
                                      simpa [σFinal, forkAfterDstArt, forkDstArtNew,
                                        forkAfterDstInk, memWish, memSrc] using h4990)
                                    (by simpa [σFinal, forkAfterDstArt, forkDstArtNew,
                                      forkAfterDstInk] using hsrcInkSpotOk)
                                    (by simpa [srcUnsafeWord, σFinal, forkAfterDstArt,
                                      forkDstArtNew, forkAfterDstInk] using hsrcUnsafe)
                                  let dstUnsafeWord : UInt256 :=
                                    UInt256.gt
                                      (UInt256.mul
                                        (solcSlotWord σFinal I (forkDstArtSlot I))
                                        (solcSlotWord σFinal I (forkIlkRateSlot I)))
                                      (UInt256.mul
                                        (solcSlotWord σFinal I (forkDstInkSlot I))
                                        (solcSlotWord σFinal I (forkIlkSpotSlot I)))
                                  by_cases hdstUnsafe : dstUnsafeWord = UInt256.ofNat 0
                                  · obtain ⟨_, _, h5168⟩ := RD.vatForkDstUnsafeCheckSuccess
                                      (h := by
                                        simpa [σFinal, forkAfterDstArt, forkDstArtNew,
                                          forkAfterDstInk, memWish, memSrc] using h5079)
                                      (by simpa [σFinal, forkAfterDstArt, forkDstArtNew,
                                        forkAfterDstInk] using hdstInkSpotOk)
                                      (by simpa [dstUnsafeWord, σFinal, forkAfterDstArt,
                                        forkDstArtNew, forkAfterDstInk] using hdstUnsafe)
                                    by_cases hsrcDust :
                                        UInt256.lor
                                          (UInt256.eq ⟨0⟩
                                            (solcSlotWord σFinal I (forkSrcArtSlot I)))
                                          (UInt256.isZero
                                            (UInt256.lt
                                              (UInt256.mul
                                                (solcSlotWord σFinal I (forkSrcArtSlot I))
                                                (solcSlotWord σFinal I (forkIlkRateSlot I)))
                                              (solcSlotWord σFinal I
                                                (forkIlkDustSlot I)))) ≠ ⟨0⟩
                                    · by_cases hdstDust :
                                          UInt256.lor
                                            (UInt256.eq ⟨0⟩
                                              (solcSlotWord σFinal I (forkDstArtSlot I)))
                                            (UInt256.isZero
                                              (UInt256.lt
                                                (UInt256.mul
                                                  (solcSlotWord σFinal I (forkDstArtSlot I))
                                                  (solcSlotWord σFinal I (forkIlkRateSlot I)))
                                                (solcSlotWord σFinal I
                                                  (forkIlkDustSlot I)))) ≠ ⟨0⟩
                                      · exact False.elim (hsuccess
                                          ⟨hutabOk, hvtabOk, hwish, hsrcInkSpotOk,
                                            (by simpa [srcUnsafeWord] using hsrcUnsafe),
                                            hdstInkSpotOk,
                                            (by simpa [dstUnsafeWord] using hdstUnsafe),
                                            hsrcDust, hdstDust⟩)
                                      · have hdstDustEq :
                                            UInt256.lor
                                              (UInt256.eq ⟨0⟩
                                                (solcSlotWord σFinal I (forkDstArtSlot I)))
                                              (UInt256.isZero
                                                (UInt256.lt
                                                  (UInt256.mul
                                                    (solcSlotWord σFinal I (forkDstArtSlot I))
                                                    (solcSlotWord σFinal I
                                                      (forkIlkRateSlot I)))
                                                  (solcSlotWord σFinal I
                                                    (forkIlkDustSlot I)))) = ⟨0⟩ := by
                                          by_contra hne
                                          exact hdstDust hne
                                        have hdstDustEqS :
                                            UInt256.lor
                                              (UInt256.eq ⟨0⟩ dstArtFinalS)
                                              (UInt256.isZero (UInt256.lt vtabS
                                                (solcSlotWord σFinalS I
                                                  (forkIlkDustSlot I)))) = ⟨0⟩ := by
                                          have hart := forkAfterDstArt_slot_eq_of_accountMapEquiv
                                            (I := I) hAccounts (forkDstArtSlot I)
                                          have hrate := forkAfterDstArt_slot_eq_of_accountMapEquiv
                                            (I := I) hAccounts (forkIlkRateSlot I)
                                          have hdust := forkAfterDstArt_slot_eq_of_accountMapEquiv
                                            (I := I) hAccounts (forkIlkDustSlot I)
                                          simpa [σFinal, σFinalS, dstArtFinalS, vtabS, hart,
                                            hrate, hdust] using hdstDustEq
                                        have hdstDustCondS :=
                                          forkDustSourceCond_false_of_evm hdstDustEqS
                                        have hwishS : forkBothWishWord σFinalS I ≠ ⟨0⟩ := by
                                          have heq := forkBothWishWord_eq_of_accountMapEquiv
                                            (I := I)
                                            (accountMapEquiv_forkAfterDstArt (I := I) hAccounts)
                                          rwa [← heq]
                                        have hsrcUnsafeS :
                                            UInt256.gt utabS srcInkSpotS = ⟨0⟩ := by
                                          have hart := forkAfterDstArt_slot_eq_of_accountMapEquiv
                                            (I := I) hAccounts (forkSrcArtSlot I)
                                          have hrate := forkAfterDstArt_slot_eq_of_accountMapEquiv
                                            (I := I) hAccounts (forkIlkRateSlot I)
                                          have hink := forkAfterDstArt_slot_eq_of_accountMapEquiv
                                            (I := I) hAccounts (forkSrcInkSlot I)
                                          have hspot := forkAfterDstArt_slot_eq_of_accountMapEquiv
                                            (I := I) hAccounts (forkIlkSpotSlot I)
                                          simpa [srcUnsafeWord, σFinal, σFinalS, utabS,
                                            srcInkSpotS, srcArtFinalS, srcInkFinalS, rateS,
                                            spotS, hart, hrate, hink, hspot] using hsrcUnsafe
                                        have hdstUnsafeS :
                                            UInt256.gt vtabS dstInkSpotS = ⟨0⟩ := by
                                          have hart := forkAfterDstArt_slot_eq_of_accountMapEquiv
                                            (I := I) hAccounts (forkDstArtSlot I)
                                          have hrate := forkAfterDstArt_slot_eq_of_accountMapEquiv
                                            (I := I) hAccounts (forkIlkRateSlot I)
                                          have hink := forkAfterDstArt_slot_eq_of_accountMapEquiv
                                            (I := I) hAccounts (forkDstInkSlot I)
                                          have hspot := forkAfterDstArt_slot_eq_of_accountMapEquiv
                                            (I := I) hAccounts (forkIlkSpotSlot I)
                                          simpa [dstUnsafeWord, σFinal, σFinalS, vtabS,
                                            dstInkSpotS, dstArtFinalS, dstInkFinalS, rateS,
                                            spotS, hart, hrate, hink, hspot] using hdstUnsafe
                                        have hsrcDustS :
                                            UInt256.lor
                                              (UInt256.eq ⟨0⟩ srcArtFinalS)
                                              (UInt256.isZero (UInt256.lt utabS
                                                (solcSlotWord σFinalS I
                                                  (forkIlkDustSlot I)))) ≠ ⟨0⟩ := by
                                          have hart := forkAfterDstArt_slot_eq_of_accountMapEquiv
                                            (I := I) hAccounts (forkSrcArtSlot I)
                                          have hrate := forkAfterDstArt_slot_eq_of_accountMapEquiv
                                            (I := I) hAccounts (forkIlkRateSlot I)
                                          have hdust := forkAfterDstArt_slot_eq_of_accountMapEquiv
                                            (I := I) hAccounts (forkIlkDustSlot I)
                                          simpa [σFinal, σFinalS, srcArtFinalS, utabS, hart,
                                            hrate, hdust] using hsrcDust
                                        have hbody := hsourceBodyOf
                                          (execForkFinalRequiresRevertDstDust
                                            (evalExpr_fork_wish_both_true_of_word_final_store
                                              (evm := evm4) (σ := σFinalS)
                                              (forkSrcInkNew σ_solm I) (forkSrcArtNew σ_solm I)
                                              (forkDstInkNew σ_solm I) (forkDstArtNew σ_solm I)
                                              srcArtFinalS dstArtFinalS srcInkFinalS
                                              dstInkFinalS utabS vtabS srcInkSpotS
                                              dstInkSpotS hsourceEq
                                              (by simpa [vatSlotWord] using
                                                hloadFinalS (forkSrcWishSlot I))
                                              (by simpa [vatSlotWord] using
                                                hloadFinalS (forkDstWishSlot I))
                                              hwishS)
                                            (evalExpr_fork_utab_le_srcInkSpot_final_store
                                              (evm := evm4) (I := I)
                                              (forkSrcInkNew σ_solm I) (forkSrcArtNew σ_solm I)
                                              (forkDstInkNew σ_solm I) (forkDstArtNew σ_solm I)
                                              srcArtFinalS dstArtFinalS srcInkFinalS
                                              dstInkFinalS utabS vtabS srcInkSpotS
                                              dstInkSpotS (ugt_eq_zero_to_le hsrcUnsafeS))
                                            (evalExpr_fork_vtab_le_dstInkSpot_final_store
                                              (evm := evm4) (I := I)
                                              (forkSrcInkNew σ_solm I) (forkSrcArtNew σ_solm I)
                                              (forkDstInkNew σ_solm I) (forkDstArtNew σ_solm I)
                                              srcArtFinalS dstArtFinalS srcInkFinalS
                                              dstInkFinalS utabS vtabS srcInkSpotS
                                              dstInkSpotS (ugt_eq_zero_to_le hdstUnsafeS))
                                            (evalExpr_fork_src_dust_final_store
                                              (evm := evm4) (I := I)
                                              (forkSrcInkNew σ_solm I) (forkSrcArtNew σ_solm I)
                                              (forkDstInkNew σ_solm I) (forkDstArtNew σ_solm I)
                                              srcArtFinalS dstArtFinalS srcInkFinalS
                                              dstInkFinalS utabS vtabS srcInkSpotS
                                              dstInkSpotS
                                              (solcSlotWord σFinalS I (forkIlkDustSlot I))
                                              hsz164 (hloadFinalS (forkIlkDustSlot I))
                                              (by simpa [srcArtFinalS, utabS] using
                                                forkDustSourceCond_of_evm hsrcDustS))
                                            (evalExpr_fork_dst_dust_false_final_store
                                              (evm := evm4) (I := I)
                                              (forkSrcInkNew σ_solm I) (forkSrcArtNew σ_solm I)
                                              (forkDstInkNew σ_solm I) (forkDstArtNew σ_solm I)
                                              srcArtFinalS dstArtFinalS srcInkFinalS
                                              dstInkFinalS utabS vtabS srcInkSpotS
                                              dstInkSpotS
                                              (solcSlotWord σFinalS I (forkIlkDustSlot I))
                                              hsz164 (hloadFinalS (forkIlkDustSlot I))
                                              hdstDustCondS.1 hdstDustCondS.2))
                                        have hrev := RD.vatForkDstDustCheckRevert
                                          (h := by
                                            simpa [σFinal, forkAfterDstArt, forkDstArtNew,
                                              forkAfterDstInk, memWish, memSrc] using h5168)
                                          hmemWish hread64Wish hsrcDust hdstDustEq
                                        exact hrev.reEquivExecutionRevert hcode
                                          (vatDispatchFork hsel) hdecode hbody
                                    · have hsrcDustEq :
                                          UInt256.lor
                                            (UInt256.eq ⟨0⟩
                                              (solcSlotWord σFinal I (forkSrcArtSlot I)))
                                            (UInt256.isZero
                                              (UInt256.lt
                                                (UInt256.mul
                                                  (solcSlotWord σFinal I (forkSrcArtSlot I))
                                                  (solcSlotWord σFinal I (forkIlkRateSlot I)))
                                                (solcSlotWord σFinal I
                                                  (forkIlkDustSlot I)))) = ⟨0⟩ := by
                                        by_contra hne
                                        exact hsrcDust hne
                                      have hrev := RD.vatForkSrcDustCheckRevert
                                        (h := by
                                          simpa [σFinal, forkAfterDstArt, forkDstArtNew,
                                            forkAfterDstInk, memWish, memSrc] using h5168)
                                        hmemWish hread64Wish hsrcDustEq
                                      have hbody := hsourceBodyOf
                                        (by
                                          have hsrcDustEqS :
                                              UInt256.lor
                                                (UInt256.eq ⟨0⟩ srcArtFinalS)
                                                (UInt256.isZero (UInt256.lt utabS
                                                  (solcSlotWord σFinalS I
                                                    (forkIlkDustSlot I)))) = ⟨0⟩ := by
                                            have hart := forkAfterDstArt_slot_eq_of_accountMapEquiv
                                              (I := I) hAccounts (forkSrcArtSlot I)
                                            have hrate := forkAfterDstArt_slot_eq_of_accountMapEquiv
                                              (I := I) hAccounts (forkIlkRateSlot I)
                                            have hdust := forkAfterDstArt_slot_eq_of_accountMapEquiv
                                              (I := I) hAccounts (forkIlkDustSlot I)
                                            simpa [σFinal, σFinalS, srcArtFinalS, utabS, hart,
                                              hrate, hdust] using hsrcDustEq
                                          have hsrcDustCondS :=
                                            forkDustSourceCond_false_of_evm hsrcDustEqS
                                          exact execForkFinalRequiresRevertSrcDust
                                            (by
                                              have hwishS : forkBothWishWord σFinalS I ≠ ⟨0⟩ := by
                                                have heq := forkBothWishWord_eq_of_accountMapEquiv
                                                  (I := I)
                                                  (accountMapEquiv_forkAfterDstArt (I := I) hAccounts)
                                                rwa [← heq]
                                              exact evalExpr_fork_wish_both_true_of_word_final_store
                                                (evm := evm4) (σ := σFinalS)
                                                (forkSrcInkNew σ_solm I) (forkSrcArtNew σ_solm I)
                                                (forkDstInkNew σ_solm I) (forkDstArtNew σ_solm I)
                                                srcArtFinalS dstArtFinalS srcInkFinalS
                                                dstInkFinalS utabS vtabS srcInkSpotS
                                                dstInkSpotS hsourceEq
                                                (by simpa [vatSlotWord] using
                                                  hloadFinalS (forkSrcWishSlot I))
                                                (by simpa [vatSlotWord] using
                                                  hloadFinalS (forkDstWishSlot I))
                                                hwishS)
                                            (by
                                              have hsrcUnsafeS :
                                                  UInt256.gt utabS srcInkSpotS = ⟨0⟩ := by
                                                have hart := forkAfterDstArt_slot_eq_of_accountMapEquiv
                                                  (I := I) hAccounts (forkSrcArtSlot I)
                                                have hrate := forkAfterDstArt_slot_eq_of_accountMapEquiv
                                                  (I := I) hAccounts (forkIlkRateSlot I)
                                                have hink := forkAfterDstArt_slot_eq_of_accountMapEquiv
                                                  (I := I) hAccounts (forkSrcInkSlot I)
                                                have hspot := forkAfterDstArt_slot_eq_of_accountMapEquiv
                                                  (I := I) hAccounts (forkIlkSpotSlot I)
                                                simpa [srcUnsafeWord, σFinal, σFinalS, utabS,
                                                  srcInkSpotS, srcArtFinalS, srcInkFinalS,
                                                  rateS, spotS, hart, hrate, hink, hspot]
                                                  using hsrcUnsafe
                                              exact evalExpr_fork_utab_le_srcInkSpot_final_store
                                                (evm := evm4) (I := I)
                                                (forkSrcInkNew σ_solm I) (forkSrcArtNew σ_solm I)
                                                (forkDstInkNew σ_solm I) (forkDstArtNew σ_solm I)
                                                srcArtFinalS dstArtFinalS srcInkFinalS
                                                dstInkFinalS utabS vtabS srcInkSpotS
                                                dstInkSpotS (ugt_eq_zero_to_le hsrcUnsafeS))
                                            (by
                                              have hdstUnsafeS :
                                                  UInt256.gt vtabS dstInkSpotS = ⟨0⟩ := by
                                                have hart := forkAfterDstArt_slot_eq_of_accountMapEquiv
                                                  (I := I) hAccounts (forkDstArtSlot I)
                                                have hrate := forkAfterDstArt_slot_eq_of_accountMapEquiv
                                                  (I := I) hAccounts (forkIlkRateSlot I)
                                                have hink := forkAfterDstArt_slot_eq_of_accountMapEquiv
                                                  (I := I) hAccounts (forkDstInkSlot I)
                                                have hspot := forkAfterDstArt_slot_eq_of_accountMapEquiv
                                                  (I := I) hAccounts (forkIlkSpotSlot I)
                                                simpa [dstUnsafeWord, σFinal, σFinalS, vtabS,
                                                  dstInkSpotS, dstArtFinalS, dstInkFinalS,
                                                  rateS, spotS, hart, hrate, hink, hspot]
                                                  using hdstUnsafe
                                              exact evalExpr_fork_vtab_le_dstInkSpot_final_store
                                                (evm := evm4) (I := I)
                                                (forkSrcInkNew σ_solm I) (forkSrcArtNew σ_solm I)
                                                (forkDstInkNew σ_solm I) (forkDstArtNew σ_solm I)
                                                srcArtFinalS dstArtFinalS srcInkFinalS
                                                dstInkFinalS utabS vtabS srcInkSpotS
                                                dstInkSpotS (ugt_eq_zero_to_le hdstUnsafeS))
                                            (evalExpr_fork_src_dust_false_final_store
                                              (evm := evm4) (I := I)
                                              (forkSrcInkNew σ_solm I) (forkSrcArtNew σ_solm I)
                                              (forkDstInkNew σ_solm I) (forkDstArtNew σ_solm I)
                                              srcArtFinalS dstArtFinalS srcInkFinalS
                                              dstInkFinalS utabS vtabS srcInkSpotS
                                              dstInkSpotS
                                              (solcSlotWord σFinalS I (forkIlkDustSlot I))
                                              hsz164 (hloadFinalS (forkIlkDustSlot I))
                                              hsrcDustCondS.1 hsrcDustCondS.2))
                                      exact hrev.reEquivExecutionRevert hcode
                                        (vatDispatchFork hsel) hdecode hbody
                                  · have hrev := RD.vatForkDstUnsafeCheckRevert
                                      (h := by
                                        simpa [σFinal, forkAfterDstArt, forkDstArtNew,
                                          forkAfterDstInk, memWish, memSrc] using h5079)
                                      hmemWish hread64Wish
                                      (by simpa [σFinal, forkAfterDstArt, forkDstArtNew,
                                        forkAfterDstInk] using hdstInkSpotOk)
                                      (by simpa [dstUnsafeWord, σFinal, forkAfterDstArt,
                                        forkDstArtNew, forkAfterDstInk] using hdstUnsafe)
                                    have hbody := hsourceBodyOf
                                      (by
                                        have hwishS : forkBothWishWord σFinalS I ≠ ⟨0⟩ := by
                                          have heq := forkBothWishWord_eq_of_accountMapEquiv
                                            (I := I)
                                            (accountMapEquiv_forkAfterDstArt (I := I) hAccounts)
                                          rwa [← heq]
                                        have hsrcUnsafeS :
                                            UInt256.gt utabS srcInkSpotS = ⟨0⟩ := by
                                          have hart := forkAfterDstArt_slot_eq_of_accountMapEquiv
                                            (I := I) hAccounts (forkSrcArtSlot I)
                                          have hrate := forkAfterDstArt_slot_eq_of_accountMapEquiv
                                            (I := I) hAccounts (forkIlkRateSlot I)
                                          have hink := forkAfterDstArt_slot_eq_of_accountMapEquiv
                                            (I := I) hAccounts (forkSrcInkSlot I)
                                          have hspot := forkAfterDstArt_slot_eq_of_accountMapEquiv
                                            (I := I) hAccounts (forkIlkSpotSlot I)
                                          simpa [srcUnsafeWord, σFinal, σFinalS, utabS,
                                            srcInkSpotS, srcArtFinalS, srcInkFinalS, rateS,
                                            spotS, hart, hrate, hink, hspot] using hsrcUnsafe
                                        have hdstUnsafeS :
                                            UInt256.gt vtabS dstInkSpotS ≠ ⟨0⟩ := by
                                          have hart := forkAfterDstArt_slot_eq_of_accountMapEquiv
                                            (I := I) hAccounts (forkDstArtSlot I)
                                          have hrate := forkAfterDstArt_slot_eq_of_accountMapEquiv
                                            (I := I) hAccounts (forkIlkRateSlot I)
                                          have hink := forkAfterDstArt_slot_eq_of_accountMapEquiv
                                            (I := I) hAccounts (forkDstInkSlot I)
                                          have hspot := forkAfterDstArt_slot_eq_of_accountMapEquiv
                                            (I := I) hAccounts (forkIlkSpotSlot I)
                                          simpa [dstUnsafeWord, σFinal, σFinalS, vtabS,
                                            dstInkSpotS, dstArtFinalS, dstInkFinalS, rateS,
                                            spotS, hart, hrate, hink, hspot] using hdstUnsafe
                                        exact execForkFinalRequiresRevertVtab
                                          (evalExpr_fork_wish_both_true_of_word_final_store
                                            (evm := evm4) (σ := σFinalS)
                                            (forkSrcInkNew σ_solm I) (forkSrcArtNew σ_solm I)
                                            (forkDstInkNew σ_solm I) (forkDstArtNew σ_solm I)
                                            srcArtFinalS dstArtFinalS srcInkFinalS
                                            dstInkFinalS utabS vtabS srcInkSpotS
                                            dstInkSpotS hsourceEq
                                            (by simpa [vatSlotWord] using
                                              hloadFinalS (forkSrcWishSlot I))
                                            (by simpa [vatSlotWord] using
                                              hloadFinalS (forkDstWishSlot I))
                                            hwishS)
                                          (evalExpr_fork_utab_le_srcInkSpot_final_store
                                            (evm := evm4) (I := I)
                                            (forkSrcInkNew σ_solm I) (forkSrcArtNew σ_solm I)
                                            (forkDstInkNew σ_solm I) (forkDstArtNew σ_solm I)
                                            srcArtFinalS dstArtFinalS srcInkFinalS
                                            dstInkFinalS utabS vtabS srcInkSpotS
                                            dstInkSpotS (ugt_eq_zero_to_le hsrcUnsafeS))
                                          (evalExpr_fork_vtab_le_dstInkSpot_false_final_store
                                            (evm := evm4) (I := I)
                                            (forkSrcInkNew σ_solm I) (forkSrcArtNew σ_solm I)
                                            (forkDstInkNew σ_solm I) (forkDstArtNew σ_solm I)
                                            srcArtFinalS dstArtFinalS srcInkFinalS
                                            dstInkFinalS utabS vtabS srcInkSpotS
                                            dstInkSpotS (ugt_ne_zero_to_gt hdstUnsafeS)))
                                    exact hrev.reEquivExecutionRevert hcode
                                      (vatDispatchFork hsel) hdecode hbody
                                · have hrev := RD.vatForkSrcUnsafeCheckRevert
                                    (h := by
                                      simpa [σFinal, forkAfterDstArt, forkDstArtNew,
                                        forkAfterDstInk, memWish, memSrc] using h4990)
                                    hmemWish hread64Wish
                                    (by simpa [σFinal, forkAfterDstArt, forkDstArtNew,
                                      forkAfterDstInk] using hsrcInkSpotOk)
                                    (by simpa [srcUnsafeWord, σFinal, forkAfterDstArt,
                                      forkDstArtNew, forkAfterDstInk] using hsrcUnsafe)
                                  have hbody := hsourceBodyOf
                                    (by
                                      have hwishS : forkBothWishWord σFinalS I ≠ ⟨0⟩ := by
                                        have heq := forkBothWishWord_eq_of_accountMapEquiv
                                          (I := I)
                                          (accountMapEquiv_forkAfterDstArt (I := I) hAccounts)
                                        rwa [← heq]
                                      have hsrcUnsafeS :
                                          UInt256.gt utabS srcInkSpotS ≠ ⟨0⟩ := by
                                        have hart := forkAfterDstArt_slot_eq_of_accountMapEquiv
                                          (I := I) hAccounts (forkSrcArtSlot I)
                                        have hrate := forkAfterDstArt_slot_eq_of_accountMapEquiv
                                          (I := I) hAccounts (forkIlkRateSlot I)
                                        have hink := forkAfterDstArt_slot_eq_of_accountMapEquiv
                                          (I := I) hAccounts (forkSrcInkSlot I)
                                        have hspot := forkAfterDstArt_slot_eq_of_accountMapEquiv
                                          (I := I) hAccounts (forkIlkSpotSlot I)
                                        simpa [srcUnsafeWord, σFinal, σFinalS, utabS,
                                          srcInkSpotS, srcArtFinalS, srcInkFinalS, rateS,
                                          spotS, hart, hrate, hink, hspot] using hsrcUnsafe
                                      exact execForkFinalRequiresRevertUtab
                                        (evalExpr_fork_wish_both_true_of_word_final_store
                                          (evm := evm4) (σ := σFinalS)
                                          (forkSrcInkNew σ_solm I) (forkSrcArtNew σ_solm I)
                                          (forkDstInkNew σ_solm I) (forkDstArtNew σ_solm I)
                                          srcArtFinalS dstArtFinalS srcInkFinalS
                                          dstInkFinalS utabS vtabS srcInkSpotS
                                          dstInkSpotS hsourceEq
                                          (by simpa [vatSlotWord] using
                                            hloadFinalS (forkSrcWishSlot I))
                                          (by simpa [vatSlotWord] using
                                            hloadFinalS (forkDstWishSlot I))
                                          hwishS)
                                        (evalExpr_fork_utab_le_srcInkSpot_false_final_store
                                          (evm := evm4) (I := I)
                                          (forkSrcInkNew σ_solm I) (forkSrcArtNew σ_solm I)
                                          (forkDstInkNew σ_solm I) (forkDstArtNew σ_solm I)
                                          srcArtFinalS dstArtFinalS srcInkFinalS
                                          dstInkFinalS utabS vtabS srcInkSpotS
                                          dstInkSpotS (ugt_ne_zero_to_gt hsrcUnsafeS)))
                                  exact hrev.reEquivExecutionRevert hcode
                                    (vatDispatchFork hsel) hdecode hbody
                              · have hwishZero : forkBothWishWord σFinal I = ⟨0⟩ := by
                                  by_contra hne
                                  exact hwish hne
                                have hrev := RD.vatForkWishBranchRevert
                                  (h := by
                                    simpa [σFinal, forkAfterDstArt, forkDstArtNew,
                                      forkAfterDstInk, memPrefix] using h4893)
                                  hmemPrefix hread64Prefix
                                  (by simpa [σFinal] using hwishZero)
                                have hbody := hsourceBodyOf
                                  (by
                                    have hwishZeroS : forkBothWishWord σFinalS I = ⟨0⟩ := by
                                      have heq := forkBothWishWord_eq_of_accountMapEquiv
                                        (I := I)
                                        (accountMapEquiv_forkAfterDstArt (I := I) hAccounts)
                                      rwa [← heq]
                                    exact execForkFinalRequiresRevertWish
                                      (evalExpr_fork_wish_both_false_of_word_zero_final_store
                                        (evm := evm4) (σ := σFinalS)
                                        (forkSrcInkNew σ_solm I) (forkSrcArtNew σ_solm I)
                                        (forkDstInkNew σ_solm I) (forkDstArtNew σ_solm I)
                                        srcArtFinalS dstArtFinalS srcInkFinalS dstInkFinalS
                                        utabS vtabS srcInkSpotS dstInkSpotS hsourceEq
                                        (by simpa [vatSlotWord] using
                                          hloadFinalS (forkSrcWishSlot I))
                                        (by simpa [vatSlotWord] using
                                          hloadFinalS (forkDstWishSlot I))
                                        hwishZeroS))
                                exact hrev.reEquivExecutionRevert hcode
                                  (vatDispatchFork hsel) hdecode hbody
                            · have hsrcInkNegS :
                                  UInt256.sgt (forkDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
                                    UInt256.gt (forkSrcInkNew σ_solm I)
                                      (solcSlotWord σ_solm I (forkSrcInkSlot I)) = ⟨0⟩ :=
                                (forkSrcInkSubGuardNeg_iff_of_accountMapEquiv (I := I)
                                  hAccounts).mp hsrcInkNeg
                              have hsrcInkPosS :
                                  UInt256.slt (forkDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
                                    UInt256.lt (forkSrcInkNew σ_solm I)
                                      (solcSlotWord σ_solm I (forkSrcInkSlot I)) = ⟨0⟩ :=
                                (forkSrcInkSubGuardPos_iff_of_accountMapEquiv (I := I)
                                  hAccounts).mp hsrcInkPos
                              have hsrcArtNegS :
                                  UInt256.sgt (forkDartWord I) ⟨0⟩ = ⟨0⟩ ∨
                                    UInt256.gt (forkSrcArtNew σ_solm I)
                                      (solcSlotWord (forkAfterSrcInk σ_solm I) I
                                        (forkSrcArtSlot I)) = ⟨0⟩ :=
                                (forkSrcArtSubGuardNeg_iff_of_accountMapEquiv (I := I)
                                  hAccounts).mp hsrcArtNeg
                              have hsrcArtPosS :
                                  UInt256.slt (forkDartWord I) ⟨0⟩ = ⟨0⟩ ∨
                                    UInt256.lt (forkSrcArtNew σ_solm I)
                                      (solcSlotWord (forkAfterSrcInk σ_solm I) I
                                        (forkSrcArtSlot I)) = ⟨0⟩ :=
                                (forkSrcArtSubGuardPos_iff_of_accountMapEquiv (I := I)
                                  hAccounts).mp hsrcArtPos
                              have hdstInkNegS :
                                  UInt256.slt (forkDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
                                    UInt256.gt (forkDstInkNew σ_solm I)
                                      (solcSlotWord (forkAfterSrcArt σ_solm I) I
                                        (forkDstInkSlot I)) = ⟨0⟩ :=
                                (forkDstInkAddGuardNeg_iff_of_accountMapEquiv (I := I)
                                  hAccounts).mp hdstInkNeg
                              have hdstInkPosS :
                                  UInt256.sgt (forkDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
                                    UInt256.lt (forkDstInkNew σ_solm I)
                                      (solcSlotWord (forkAfterSrcArt σ_solm I) I
                                        (forkDstInkSlot I)) = ⟨0⟩ :=
                                (forkDstInkAddGuardPos_iff_of_accountMapEquiv (I := I)
                                  hAccounts).mp hdstInkPos
                              have hdstArtNegS :
                                  UInt256.slt (forkDartWord I) ⟨0⟩ = ⟨0⟩ ∨
                                    UInt256.gt (forkDstArtNew σ_solm I)
                                      (solcSlotWord (forkAfterDstInk σ_solm I) I
                                        (forkDstArtSlot I)) = ⟨0⟩ :=
                                (forkDstArtAddGuardNeg_iff_of_accountMapEquiv (I := I)
                                  hAccounts).mp hdstArtNeg
                              have hdstArtPosS :
                                  UInt256.sgt (forkDartWord I) ⟨0⟩ = ⟨0⟩ ∨
                                    UInt256.lt (forkDstArtNew σ_solm I)
                                      (solcSlotWord (forkAfterDstInk σ_solm I) I
                                        (forkDstArtSlot I)) = ⟨0⟩ :=
                                (forkDstArtAddGuardPos_iff_of_accountMapEquiv (I := I)
                                  hAccounts).mp hdstArtPos
                              let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
                              let evm1 := Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner
                                (forkSrcInkSlot I) (forkSrcInkNew σ_solm I)
                              let evm2 := Solm.EVM.storageStore evm1 evm1.executionEnv.codeOwner
                                (forkSrcArtSlot I) (forkSrcArtNew σ_solm I)
                              let evm3 := Solm.EVM.storageStore evm2 evm2.executionEnv.codeOwner
                                (forkDstInkSlot I) (forkDstInkNew σ_solm I)
                              let evm4 := Solm.EVM.storageStore evm3 evm3.executionEnv.codeOwner
                                (forkDstArtSlot I) (forkDstArtNew σ_solm I)
                              have hloadSrcInk :
                                  Solm.EVM.storageLoad evm0 evm0.executionEnv.codeOwner
                                    (forkSrcInkSlot I) =
                                  solcSlotWord σ_solm I (forkSrcInkSlot I) := by
                                simp [evm0, initState, Solm.EVM.storageLoad, solcSlotWord,
                                  State.lookupAccount, Account.lookupStorage]
                              have hloadSrcArt :
                                  Solm.EVM.storageLoad evm1 evm1.executionEnv.codeOwner
                                    (forkSrcArtSlot I) =
                                  solcSlotWord (forkAfterSrcInk σ_solm I) I
                                    (forkSrcArtSlot I) := by
                                simp [evm1, evm0, initState, Solm.EVM.storageLoad,
                                  solcSlotWord, State.lookupAccount, Account.lookupStorage,
                                  storageStore_accountMap, storageStore_executionEnv,
                                  forkAfterSrcInk]
                              have hloadDstInk :
                                  Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner
                                    (forkDstInkSlot I) =
                                  solcSlotWord (forkAfterSrcArt σ_solm I) I
                                    (forkDstInkSlot I) := by
                                simp [evm2, evm1, evm0, initState, Solm.EVM.storageLoad,
                                  solcSlotWord, State.lookupAccount, Account.lookupStorage,
                                  storageStore_accountMap, storageStore_executionEnv,
                                  forkAfterSrcInk, forkAfterSrcArt]
                              have hloadDstArt :
                                  Solm.EVM.storageLoad evm3 evm3.executionEnv.codeOwner
                                    (forkDstArtSlot I) =
                                  solcSlotWord (forkAfterDstInk σ_solm I) I
                                    (forkDstArtSlot I) := by
                                simp [evm3, evm2, evm1, evm0, initState, Solm.EVM.storageLoad,
                                  solcSlotWord, State.lookupAccount, Account.lookupStorage,
                                  storageStore_accountMap, storageStore_executionEnv,
                                  forkAfterSrcInk, forkAfterSrcArt, forkAfterDstInk]
                              have hloadFinal (slot : UInt256) :
                                  Solm.EVM.storageLoad evm4 evm4.executionEnv.codeOwner slot =
                                    solcSlotWord (forkAfterDstArt σ_solm I) I slot := by
                                simpa [evm4, evm3, evm2, evm1, evm0,
                                  storageStore_executionEnv] using
                                    forkSourceFinal_storageLoad (cA := cA) (gh := gh)
                                      (bl := bl) (σ := σ_solm) (σ₀ := σ₀) (A := A)
                                      (I := I) (g := g)
                                      (forkSrcInkNew σ_solm I) (forkSrcArtNew σ_solm I)
                                      (forkDstInkNew σ_solm I) (forkDstArtNew σ_solm I)
                                      slot rfl rfl rfl rfl
                              have hutabOkS :
                                  solcSlotWord (forkAfterDstArt σ_solm I) I
                                        (forkIlkRateSlot I) = ⟨0⟩ ∨
                                      UInt256.eq
                                        (UInt256.div
                                          (UInt256.mul
                                            (solcSlotWord (forkAfterDstArt σ_solm I) I
                                              (forkSrcArtSlot I))
                                            (solcSlotWord (forkAfterDstArt σ_solm I) I
                                              (forkIlkRateSlot I)))
                                          (solcSlotWord (forkAfterDstArt σ_solm I) I
                                            (forkIlkRateSlot I)))
                                        (solcSlotWord (forkAfterDstArt σ_solm I) I
                                          (forkSrcArtSlot I)) ≠ ⟨0⟩ := by
                                have hart := forkAfterDstArt_slot_eq_of_accountMapEquiv
                                  (I := I) hAccounts (forkSrcArtSlot I)
                                have hrate := forkAfterDstArt_slot_eq_of_accountMapEquiv
                                  (I := I) hAccounts (forkIlkRateSlot I)
                                simpa [σFinal, hart, hrate] using hutabOk
                              have hvtabOkS :
                                  solcSlotWord (forkAfterDstArt σ_solm I) I
                                        (forkIlkRateSlot I) = ⟨0⟩ ∨
                                      UInt256.eq
                                        (UInt256.div
                                          (UInt256.mul
                                            (solcSlotWord (forkAfterDstArt σ_solm I) I
                                              (forkDstArtSlot I))
                                            (solcSlotWord (forkAfterDstArt σ_solm I) I
                                              (forkIlkRateSlot I)))
                                          (solcSlotWord (forkAfterDstArt σ_solm I) I
                                            (forkIlkRateSlot I)))
                                        (solcSlotWord (forkAfterDstArt σ_solm I) I
                                          (forkDstArtSlot I)) ≠ ⟨0⟩ := by
                                have hart := forkAfterDstArt_slot_eq_of_accountMapEquiv
                                  (I := I) hAccounts (forkDstArtSlot I)
                                have hrate := forkAfterDstArt_slot_eq_of_accountMapEquiv
                                  (I := I) hAccounts (forkIlkRateSlot I)
                                simpa [σFinal, hart, hrate] using hvtabOk
                              have hsrcInkSpotOkS :
                                  solcSlotWord (forkAfterDstArt σ_solm I) I
                                        (forkIlkSpotSlot I) = ⟨0⟩ ∨
                                      UInt256.eq
                                        (UInt256.div
                                          (UInt256.mul
                                            (solcSlotWord (forkAfterDstArt σ_solm I) I
                                              (forkSrcInkSlot I))
                                            (solcSlotWord (forkAfterDstArt σ_solm I) I
                                              (forkIlkSpotSlot I)))
                                          (solcSlotWord (forkAfterDstArt σ_solm I) I
                                            (forkIlkSpotSlot I)))
                                        (solcSlotWord (forkAfterDstArt σ_solm I) I
                                          (forkSrcInkSlot I)) ≠ ⟨0⟩ := by
                                have hink := forkAfterDstArt_slot_eq_of_accountMapEquiv
                                  (I := I) hAccounts (forkSrcInkSlot I)
                                have hspot := forkAfterDstArt_slot_eq_of_accountMapEquiv
                                  (I := I) hAccounts (forkIlkSpotSlot I)
                                simpa [σFinal, hink, hspot] using hsrcInkSpotOk
                              have hdstInkSpotFailS :
                                  ¬ (solcSlotWord (forkAfterDstArt σ_solm I) I
                                        (forkIlkSpotSlot I) = ⟨0⟩ ∨
                                      UInt256.eq
                                        (UInt256.div
                                          (UInt256.mul
                                            (solcSlotWord (forkAfterDstArt σ_solm I) I
                                              (forkDstInkSlot I))
                                            (solcSlotWord (forkAfterDstArt σ_solm I) I
                                              (forkIlkSpotSlot I)))
                                          (solcSlotWord (forkAfterDstArt σ_solm I) I
                                            (forkIlkSpotSlot I)))
                                        (solcSlotWord (forkAfterDstArt σ_solm I) I
                                          (forkDstInkSlot I)) ≠ ⟨0⟩) := by
                                intro hokS
                                have hink := forkAfterDstArt_slot_eq_of_accountMapEquiv
                                  (I := I) hAccounts (forkDstInkSlot I)
                                have hspot := forkAfterDstArt_slot_eq_of_accountMapEquiv
                                  (I := I) hAccounts (forkIlkSpotSlot I)
                                exact hdstInkSpotOk (by simpa [σFinal, hink, hspot] using hokS)
                              have hutabFitGuard := forkUintCheckedMulGuard_to_fit_and_source_guard
                                (a := solcSlotWord (forkAfterDstArt σ_solm I) I
                                  (forkSrcArtSlot I))
                                (b := solcSlotWord (forkAfterDstArt σ_solm I) I
                                  (forkIlkRateSlot I))
                                hutabOkS
                              have hvtabFitGuard := forkUintCheckedMulGuard_to_fit_and_source_guard
                                (a := solcSlotWord (forkAfterDstArt σ_solm I) I
                                  (forkDstArtSlot I))
                                (b := solcSlotWord (forkAfterDstArt σ_solm I) I
                                  (forkIlkRateSlot I))
                                hvtabOkS
                              have hsrcInkSpotFitGuard :=
                                forkUintCheckedMulGuard_to_fit_and_source_guard
                                  (a := solcSlotWord (forkAfterDstArt σ_solm I) I
                                    (forkSrcInkSlot I))
                                  (b := solcSlotWord (forkAfterDstArt σ_solm I) I
                                    (forkIlkSpotSlot I))
                                  hsrcInkSpotOkS
                              have hbody := execForkSourceRevertDstInkSpotMul
                                (evm0 := evm0) (I := I)
                                (solcSlotWord σ_solm I (forkSrcInkSlot I))
                                (forkSrcInkNew σ_solm I)
                                (solcSlotWord (forkAfterSrcInk σ_solm I) I
                                  (forkSrcArtSlot I))
                                (forkSrcArtNew σ_solm I)
                                (solcSlotWord (forkAfterSrcArt σ_solm I) I
                                  (forkDstInkSlot I))
                                (forkDstInkNew σ_solm I)
                                (solcSlotWord (forkAfterDstInk σ_solm I) I
                                  (forkDstArtSlot I))
                                (forkDstArtNew σ_solm I)
                                (solcSlotWord (forkAfterDstArt σ_solm I) I
                                  (forkSrcArtSlot I))
                                (solcSlotWord (forkAfterDstArt σ_solm I) I
                                  (forkDstArtSlot I))
                                (solcSlotWord (forkAfterDstArt σ_solm I) I
                                  (forkSrcInkSlot I))
                                (solcSlotWord (forkAfterDstArt σ_solm I) I
                                  (forkDstInkSlot I))
                                (solcSlotWord (forkAfterDstArt σ_solm I) I
                                  (forkIlkRateSlot I))
                                (solcSlotWord (forkAfterDstArt σ_solm I) I
                                  (forkIlkSpotSlot I))
                                (UInt256.mul
                                  (solcSlotWord (forkAfterDstArt σ_solm I) I
                                    (forkSrcArtSlot I))
                                  (solcSlotWord (forkAfterDstArt σ_solm I) I
                                    (forkIlkRateSlot I)))
                                (UInt256.mul
                                  (solcSlotWord (forkAfterDstArt σ_solm I) I
                                    (forkDstArtSlot I))
                                  (solcSlotWord (forkAfterDstArt σ_solm I) I
                                    (forkIlkRateSlot I)))
                                (UInt256.mul
                                  (solcSlotWord (forkAfterDstArt σ_solm I) I
                                    (forkSrcInkSlot I))
                                  (solcSlotWord (forkAfterDstArt σ_solm I) I
                                    (forkIlkSpotSlot I)))
                                (by simpa [evm0, initState] using hwv) hsz164
                                hloadSrcInk rfl
                                (forkDinkSubGuardNegCond hsrcInkNegS)
                                (forkDinkSubGuardPosCond hsrcInkPosS)
                                (by simpa [evm1, storageStore_executionEnv] using hloadSrcArt)
                                rfl
                                (forkDartSubGuardNegCond hsrcArtNegS)
                                (forkDartSubGuardPosCond hsrcArtPosS)
                                (by simpa [evm2, evm1, storageStore_executionEnv]
                                  using hloadDstInk)
                                rfl
                                (forkDinkAddGuardNegCond hdstInkNegS)
                                (forkDinkAddGuardPosCond hdstInkPosS)
                                (by simpa [evm3, evm2, evm1, storageStore_executionEnv]
                                  using hloadDstArt)
                                rfl
                                (forkDartAddGuardNegCond hdstArtNegS)
                                (forkDartAddGuardPosCond hdstArtPosS)
                                (by
                                  simpa [evm4, evm3, evm2, evm1, storageStore_executionEnv]
                                    using hloadFinal (forkSrcArtSlot I))
                                (by
                                  simpa [evm4, evm3, evm2, evm1, storageStore_executionEnv]
                                    using hloadFinal (forkDstArtSlot I))
                                (by
                                  simpa [evm4, evm3, evm2, evm1, storageStore_executionEnv]
                                    using hloadFinal (forkSrcInkSlot I))
                                (by
                                  simpa [evm4, evm3, evm2, evm1, storageStore_executionEnv]
                                    using hloadFinal (forkDstInkSlot I))
                                (by
                                  simpa [evm4, evm3, evm2, evm1, storageStore_executionEnv]
                                    using hloadFinal (forkIlkRateSlot I))
                                (by
                                  simpa [evm4, evm3, evm2, evm1, storageStore_executionEnv]
                                    using hloadFinal (forkIlkSpotSlot I))
                                rfl hutabFitGuard.1 hutabFitGuard.2
                                rfl hvtabFitGuard.1 hvtabFitGuard.2
                                rfl hsrcInkSpotFitGuard.1 hsrcInkSpotFitGuard.2
                                (forkUintCheckedMulFail_to_overflow hdstInkSpotFailS)
                              obtain ⟨_, _, h4792⟩ := RD.vatForkSrcInkSubSuccess
                                (h := hdecoded) solcFreePtrMem_size hsz164
                                (by simpa [forkSrcInkNew] using hsrcInkNeg)
                                (by simpa [forkSrcInkNew] using hsrcInkPos)
                              obtain ⟨_, _, h4809⟩ := RD.vatForkSrcArtSubSuccess
                                (h := by simpa [forkSrcInkNew] using h4792) hperm
                                (by simpa [forkSrcArtNew, forkAfterSrcInk] using hsrcArtNeg)
                                (by simpa [forkSrcArtNew, forkAfterSrcInk] using hsrcArtPos)
                              obtain ⟨_, _, h4826⟩ := RD.vatForkDstInkAddSuccess
                                (h := by simpa [forkSrcArtNew, forkAfterSrcInk] using h4809)
                                hperm
                                (by simpa [forkDstInkNew, forkAfterSrcArt] using hdstInkNeg)
                                (by simpa [forkDstInkNew, forkAfterSrcArt] using hdstInkPos)
                              obtain ⟨_, _, h4843⟩ := RD.vatForkDstArtAddSuccess
                                (h := by simpa [forkDstInkNew, forkAfterSrcArt] using h4826)
                                hperm
                                (by simpa [forkDstArtNew, forkAfterDstInk] using hdstArtNeg)
                                (by simpa [forkDstArtNew, forkAfterDstInk] using hdstArtPos)
                              obtain ⟨_, _, h4871⟩ := RD.vatForkUtabMulSuccess
                                (h := by
                                  simpa [forkDstArtNew, forkAfterDstInk] using h4843)
                                hperm
                                (by simpa [σFinal, forkAfterDstArt, forkDstArtNew,
                                  forkAfterDstInk] using hutabOk)
                              obtain ⟨_, _, h4893⟩ := RD.vatForkVtabMulSuccess
                                (h := by
                                  simpa [σFinal, forkAfterDstArt, forkDstArtNew,
                                    forkAfterDstInk] using h4871)
                                (by simpa [σFinal, forkAfterDstArt, forkDstArtNew,
                                  forkAfterDstInk] using hvtabOk)
                              let memPrefix :=
                                twoWordHashMem (forkIlkWord I) ⟨2⟩
                                  (wordAt0Mem (forkDstMaskedWord I)
                                    (twoWordHashMem (forkSrcMaskedWord I)
                                      (solcMappingSlot ⟨3⟩ (forkIlkWord I))
                                      (twoWordHashMem (forkIlkWord I) ⟨3⟩ solcFreePtrMem)))
                              have hmemPrefix : memPrefix.size = 96 := by
                                dsimp [memPrefix]
                                apply twoWordHashMem_size_96
                                apply wordAt0Mem_size_96
                                apply twoWordHashMem_size_96
                                apply twoWordHashMem_size_96
                                exact solcFreePtrMem_size
                              have hread64Prefix :
                                  memPrefix.readWithPadding 64 32 =
                                    UInt256.toByteArray ⟨128⟩ := by
                                dsimp [memPrefix]
                                apply twoWordHashMem_read64
                                · apply wordAt0Mem_size_96
                                  apply twoWordHashMem_size_96
                                  apply twoWordHashMem_size_96
                                  exact solcFreePtrMem_size
                                · rw [wordAt0Mem_read64]
                                  apply twoWordHashMem_read64
                                  · apply twoWordHashMem_size_96
                                    exact solcFreePtrMem_size
                                  · apply twoWordHashMem_read64
                                    · exact solcFreePtrMem_size
                                    · exact solcFreePtrMem_read64
                                  · apply twoWordHashMem_size_96
                                    apply twoWordHashMem_size_96
                                    exact solcFreePtrMem_size
                              by_cases hwish : forkBothWishWord σFinal I ≠ ⟨0⟩
                              · obtain ⟨_, _, h4990⟩ := (RD.vatForkWishSuccess
                                  (h := by
                                    simpa [σFinal, forkAfterDstArt, forkDstArtNew,
                                      forkAfterDstInk, memPrefix] using h4893)
                                  hmemPrefix
                                  (by simpa [σFinal] using hwish))
                                let memSrc : ByteArray :=
                                  twoWordHashMem (hopeSourceWord I)
                                    (solcMappingSlot (⟨1⟩ : UInt256) (forkSrcMaskedWord I))
                                    (twoWordHashMem (forkSrcMaskedWord I) (⟨1⟩ : UInt256) memPrefix)
                                let memWish : ByteArray :=
                                  twoWordHashMem (hopeSourceWord I)
                                    (solcMappingSlot (⟨1⟩ : UInt256) (forkDstMaskedWord I))
                                    (twoWordHashMem (forkDstMaskedWord I) (⟨1⟩ : UInt256) memSrc)
                                have hmemSrc : memSrc.size = 96 := by
                                  dsimp [memSrc]
                                  apply twoWordHashMem_size_96
                                  apply twoWordHashMem_size_96
                                  exact hmemPrefix
                                have hmemWish : memWish.size = 96 := by
                                  dsimp [memWish]
                                  apply twoWordHashMem_size_96
                                  apply twoWordHashMem_size_96
                                  exact hmemSrc
                                have hread64Src :
                                    memSrc.readWithPadding 64 32 =
                                      UInt256.toByteArray ⟨128⟩ := by
                                  dsimp [memSrc]
                                  apply twoWordHashMem_read64
                                  · apply twoWordHashMem_size_96
                                    exact hmemPrefix
                                  · exact twoWordHashMem_read64
                                      (forkSrcMaskedWord I) ⟨1⟩ hmemPrefix hread64Prefix
                                have hread64Wish :
                                    memWish.readWithPadding 64 32 =
                                      UInt256.toByteArray ⟨128⟩ := by
                                  dsimp [memWish]
                                  apply twoWordHashMem_read64
                                  · apply twoWordHashMem_size_96
                                    exact hmemSrc
                                  · exact twoWordHashMem_read64
                                      (forkDstMaskedWord I) ⟨1⟩ hmemSrc hread64Src
                                let srcUnsafeWord : UInt256 :=
                                  UInt256.gt
                                    (UInt256.mul
                                      (solcSlotWord σFinal I (forkSrcArtSlot I))
                                      (solcSlotWord σFinal I (forkIlkRateSlot I)))
                                    (UInt256.mul
                                      (solcSlotWord σFinal I (forkSrcInkSlot I))
                                      (solcSlotWord σFinal I (forkIlkSpotSlot I)))
                                by_cases hsrcUnsafe : srcUnsafeWord = UInt256.ofNat 0
                                · obtain ⟨_, _, h5079⟩ := RD.vatForkSrcUnsafeCheckSuccess
                                    (h := by
                                      simpa [σFinal, forkAfterDstArt, forkDstArtNew,
                                        forkAfterDstInk, memWish, memSrc] using h4990)
                                    (by simpa [σFinal, forkAfterDstArt, forkDstArtNew,
                                      forkAfterDstInk] using hsrcInkSpotOk)
                                    (by simpa [srcUnsafeWord, σFinal, forkAfterDstArt,
                                      forkDstArtNew, forkAfterDstInk] using hsrcUnsafe)
                                  have hrev := RD.vatForkDstUnsafeMulRevert
                                    (h := by
                                      simpa [σFinal, forkAfterDstArt, forkDstArtNew,
                                        forkAfterDstInk, memWish, memSrc] using h5079)
                                    (by simpa [σFinal, forkAfterDstArt, forkDstArtNew,
                                      forkAfterDstInk] using hdstInkSpotOk)
                                  exact hrev.reEquivExecutionRevert hcode (vatDispatchFork hsel)
                                    hdecode hbody
                                · have hrev := RD.vatForkSrcUnsafeCheckRevert
                                    (h := by
                                      simpa [σFinal, forkAfterDstArt, forkDstArtNew,
                                        forkAfterDstInk, memWish, memSrc] using h4990)
                                    hmemWish hread64Wish
                                    (by simpa [σFinal, forkAfterDstArt, forkDstArtNew,
                                      forkAfterDstInk] using hsrcInkSpotOk)
                                    (by simpa [srcUnsafeWord, σFinal, forkAfterDstArt,
                                      forkDstArtNew, forkAfterDstInk] using hsrcUnsafe)
                                  exact hrev.reEquivExecutionRevert hcode (vatDispatchFork hsel)
                                    hdecode hbody
                              · have hwishZero : forkBothWishWord σFinal I = ⟨0⟩ := by
                                  by_contra hne
                                  exact hwish hne
                                have hrev := RD.vatForkWishBranchRevert
                                  (h := by
                                    simpa [σFinal, forkAfterDstArt, forkDstArtNew,
                                      forkAfterDstInk, memPrefix] using h4893)
                                  hmemPrefix hread64Prefix
                                  (by simpa [σFinal] using hwishZero)
                                exact hrev.reEquivExecutionRevert hcode (vatDispatchFork hsel)
                                  hdecode hbody
                          · have hsrcInkNegS :
                                UInt256.sgt (forkDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
                                  UInt256.gt (forkSrcInkNew σ_solm I)
                                    (solcSlotWord σ_solm I (forkSrcInkSlot I)) = ⟨0⟩ :=
                              (forkSrcInkSubGuardNeg_iff_of_accountMapEquiv (I := I)
                                hAccounts).mp hsrcInkNeg
                            have hsrcInkPosS :
                                UInt256.slt (forkDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
                                  UInt256.lt (forkSrcInkNew σ_solm I)
                                    (solcSlotWord σ_solm I (forkSrcInkSlot I)) = ⟨0⟩ :=
                              (forkSrcInkSubGuardPos_iff_of_accountMapEquiv (I := I)
                                hAccounts).mp hsrcInkPos
                            have hsrcArtNegS :
                                UInt256.sgt (forkDartWord I) ⟨0⟩ = ⟨0⟩ ∨
                                  UInt256.gt (forkSrcArtNew σ_solm I)
                                    (solcSlotWord (forkAfterSrcInk σ_solm I) I
                                      (forkSrcArtSlot I)) = ⟨0⟩ :=
                              (forkSrcArtSubGuardNeg_iff_of_accountMapEquiv (I := I)
                                hAccounts).mp hsrcArtNeg
                            have hsrcArtPosS :
                                UInt256.slt (forkDartWord I) ⟨0⟩ = ⟨0⟩ ∨
                                  UInt256.lt (forkSrcArtNew σ_solm I)
                                    (solcSlotWord (forkAfterSrcInk σ_solm I) I
                                      (forkSrcArtSlot I)) = ⟨0⟩ :=
                              (forkSrcArtSubGuardPos_iff_of_accountMapEquiv (I := I)
                                hAccounts).mp hsrcArtPos
                            have hdstInkNegS :
                                UInt256.slt (forkDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
                                  UInt256.gt (forkDstInkNew σ_solm I)
                                    (solcSlotWord (forkAfterSrcArt σ_solm I) I
                                      (forkDstInkSlot I)) = ⟨0⟩ :=
                              (forkDstInkAddGuardNeg_iff_of_accountMapEquiv (I := I)
                                hAccounts).mp hdstInkNeg
                            have hdstInkPosS :
                                UInt256.sgt (forkDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
                                  UInt256.lt (forkDstInkNew σ_solm I)
                                    (solcSlotWord (forkAfterSrcArt σ_solm I) I
                                      (forkDstInkSlot I)) = ⟨0⟩ :=
                              (forkDstInkAddGuardPos_iff_of_accountMapEquiv (I := I)
                                hAccounts).mp hdstInkPos
                            have hdstArtNegS :
                                UInt256.slt (forkDartWord I) ⟨0⟩ = ⟨0⟩ ∨
                                  UInt256.gt (forkDstArtNew σ_solm I)
                                    (solcSlotWord (forkAfterDstInk σ_solm I) I
                                      (forkDstArtSlot I)) = ⟨0⟩ :=
                              (forkDstArtAddGuardNeg_iff_of_accountMapEquiv (I := I)
                                hAccounts).mp hdstArtNeg
                            have hdstArtPosS :
                                UInt256.sgt (forkDartWord I) ⟨0⟩ = ⟨0⟩ ∨
                                  UInt256.lt (forkDstArtNew σ_solm I)
                                    (solcSlotWord (forkAfterDstInk σ_solm I) I
                                      (forkDstArtSlot I)) = ⟨0⟩ :=
                              (forkDstArtAddGuardPos_iff_of_accountMapEquiv (I := I)
                                hAccounts).mp hdstArtPos
                            let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
                            let evm1 := Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner
                              (forkSrcInkSlot I) (forkSrcInkNew σ_solm I)
                            let evm2 := Solm.EVM.storageStore evm1 evm1.executionEnv.codeOwner
                              (forkSrcArtSlot I) (forkSrcArtNew σ_solm I)
                            let evm3 := Solm.EVM.storageStore evm2 evm2.executionEnv.codeOwner
                              (forkDstInkSlot I) (forkDstInkNew σ_solm I)
                            let evm4 := Solm.EVM.storageStore evm3 evm3.executionEnv.codeOwner
                              (forkDstArtSlot I) (forkDstArtNew σ_solm I)
                            have hloadSrcInk :
                                Solm.EVM.storageLoad evm0 evm0.executionEnv.codeOwner
                                  (forkSrcInkSlot I) =
                                solcSlotWord σ_solm I (forkSrcInkSlot I) := by
                              simp [evm0, initState, Solm.EVM.storageLoad, solcSlotWord,
                                State.lookupAccount, Account.lookupStorage]
                            have hloadSrcArt :
                                Solm.EVM.storageLoad evm1 evm1.executionEnv.codeOwner
                                  (forkSrcArtSlot I) =
                                solcSlotWord (forkAfterSrcInk σ_solm I) I
                                  (forkSrcArtSlot I) := by
                              simp [evm1, evm0, initState, Solm.EVM.storageLoad,
                                solcSlotWord, State.lookupAccount, Account.lookupStorage,
                                storageStore_accountMap, storageStore_executionEnv,
                                forkAfterSrcInk]
                            have hloadDstInk :
                                Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner
                                  (forkDstInkSlot I) =
                                solcSlotWord (forkAfterSrcArt σ_solm I) I
                                  (forkDstInkSlot I) := by
                              simp [evm2, evm1, evm0, initState, Solm.EVM.storageLoad,
                                solcSlotWord, State.lookupAccount, Account.lookupStorage,
                                storageStore_accountMap, storageStore_executionEnv,
                                forkAfterSrcInk, forkAfterSrcArt]
                            have hloadDstArt :
                                Solm.EVM.storageLoad evm3 evm3.executionEnv.codeOwner
                                  (forkDstArtSlot I) =
                                solcSlotWord (forkAfterDstInk σ_solm I) I
                                  (forkDstArtSlot I) := by
                              simp [evm3, evm2, evm1, evm0, initState, Solm.EVM.storageLoad,
                                solcSlotWord, State.lookupAccount, Account.lookupStorage,
                                storageStore_accountMap, storageStore_executionEnv,
                                forkAfterSrcInk, forkAfterSrcArt, forkAfterDstInk]
                            have hloadFinal (slot : UInt256) :
                                Solm.EVM.storageLoad evm4 evm4.executionEnv.codeOwner slot =
                                  solcSlotWord (forkAfterDstArt σ_solm I) I slot := by
                              simpa [evm4, evm3, evm2, evm1, evm0,
                                storageStore_executionEnv] using
                                  forkSourceFinal_storageLoad (cA := cA) (gh := gh)
                                    (bl := bl) (σ := σ_solm) (σ₀ := σ₀) (A := A)
                                    (I := I) (g := g)
                                    (forkSrcInkNew σ_solm I) (forkSrcArtNew σ_solm I)
                                    (forkDstInkNew σ_solm I) (forkDstArtNew σ_solm I)
                                    slot rfl rfl rfl rfl
                            have hutabOkS :
                                solcSlotWord (forkAfterDstArt σ_solm I) I
                                      (forkIlkRateSlot I) = ⟨0⟩ ∨
                                    UInt256.eq
                                      (UInt256.div
                                        (UInt256.mul
                                          (solcSlotWord (forkAfterDstArt σ_solm I) I
                                            (forkSrcArtSlot I))
                                          (solcSlotWord (forkAfterDstArt σ_solm I) I
                                            (forkIlkRateSlot I)))
                                        (solcSlotWord (forkAfterDstArt σ_solm I) I
                                          (forkIlkRateSlot I)))
                                      (solcSlotWord (forkAfterDstArt σ_solm I) I
                                        (forkSrcArtSlot I)) ≠ ⟨0⟩ := by
                              have hart := forkAfterDstArt_slot_eq_of_accountMapEquiv
                                (I := I) hAccounts (forkSrcArtSlot I)
                              have hrate := forkAfterDstArt_slot_eq_of_accountMapEquiv
                                (I := I) hAccounts (forkIlkRateSlot I)
                              simpa [σFinal, hart, hrate] using hutabOk
                            have hvtabOkS :
                                solcSlotWord (forkAfterDstArt σ_solm I) I
                                      (forkIlkRateSlot I) = ⟨0⟩ ∨
                                    UInt256.eq
                                      (UInt256.div
                                        (UInt256.mul
                                          (solcSlotWord (forkAfterDstArt σ_solm I) I
                                            (forkDstArtSlot I))
                                          (solcSlotWord (forkAfterDstArt σ_solm I) I
                                            (forkIlkRateSlot I)))
                                        (solcSlotWord (forkAfterDstArt σ_solm I) I
                                          (forkIlkRateSlot I)))
                                      (solcSlotWord (forkAfterDstArt σ_solm I) I
                                        (forkDstArtSlot I)) ≠ ⟨0⟩ := by
                              have hart := forkAfterDstArt_slot_eq_of_accountMapEquiv
                                (I := I) hAccounts (forkDstArtSlot I)
                              have hrate := forkAfterDstArt_slot_eq_of_accountMapEquiv
                                (I := I) hAccounts (forkIlkRateSlot I)
                              simpa [σFinal, hart, hrate] using hvtabOk
                            have hsrcInkSpotFailS :
                                ¬ (solcSlotWord (forkAfterDstArt σ_solm I) I
                                      (forkIlkSpotSlot I) = ⟨0⟩ ∨
                                    UInt256.eq
                                      (UInt256.div
                                        (UInt256.mul
                                          (solcSlotWord (forkAfterDstArt σ_solm I) I
                                            (forkSrcInkSlot I))
                                          (solcSlotWord (forkAfterDstArt σ_solm I) I
                                            (forkIlkSpotSlot I)))
                                        (solcSlotWord (forkAfterDstArt σ_solm I) I
                                          (forkIlkSpotSlot I)))
                                      (solcSlotWord (forkAfterDstArt σ_solm I) I
                                        (forkSrcInkSlot I)) ≠ ⟨0⟩) := by
                              intro hokS
                              have hink := forkAfterDstArt_slot_eq_of_accountMapEquiv
                                (I := I) hAccounts (forkSrcInkSlot I)
                              have hspot := forkAfterDstArt_slot_eq_of_accountMapEquiv
                                (I := I) hAccounts (forkIlkSpotSlot I)
                              exact hsrcInkSpotOk (by simpa [σFinal, hink, hspot] using hokS)
                            have hutabFitGuard := forkUintCheckedMulGuard_to_fit_and_source_guard
                              (a := solcSlotWord (forkAfterDstArt σ_solm I) I
                                (forkSrcArtSlot I))
                              (b := solcSlotWord (forkAfterDstArt σ_solm I) I
                                (forkIlkRateSlot I))
                              hutabOkS
                            have hvtabFitGuard := forkUintCheckedMulGuard_to_fit_and_source_guard
                              (a := solcSlotWord (forkAfterDstArt σ_solm I) I
                                (forkDstArtSlot I))
                              (b := solcSlotWord (forkAfterDstArt σ_solm I) I
                                (forkIlkRateSlot I))
                              hvtabOkS
                            have hbody := execForkSourceRevertSrcInkSpotMul
                              (evm0 := evm0) (I := I)
                              (solcSlotWord σ_solm I (forkSrcInkSlot I))
                              (forkSrcInkNew σ_solm I)
                              (solcSlotWord (forkAfterSrcInk σ_solm I) I
                                (forkSrcArtSlot I))
                              (forkSrcArtNew σ_solm I)
                              (solcSlotWord (forkAfterSrcArt σ_solm I) I
                                (forkDstInkSlot I))
                              (forkDstInkNew σ_solm I)
                              (solcSlotWord (forkAfterDstInk σ_solm I) I
                                (forkDstArtSlot I))
                              (forkDstArtNew σ_solm I)
                              (solcSlotWord (forkAfterDstArt σ_solm I) I
                                (forkSrcArtSlot I))
                              (solcSlotWord (forkAfterDstArt σ_solm I) I
                                (forkDstArtSlot I))
                              (solcSlotWord (forkAfterDstArt σ_solm I) I
                                (forkSrcInkSlot I))
                              (solcSlotWord (forkAfterDstArt σ_solm I) I
                                (forkDstInkSlot I))
                              (solcSlotWord (forkAfterDstArt σ_solm I) I
                                (forkIlkRateSlot I))
                              (solcSlotWord (forkAfterDstArt σ_solm I) I
                                (forkIlkSpotSlot I))
                              (UInt256.mul
                                (solcSlotWord (forkAfterDstArt σ_solm I) I
                                  (forkSrcArtSlot I))
                                (solcSlotWord (forkAfterDstArt σ_solm I) I
                                  (forkIlkRateSlot I)))
                              (UInt256.mul
                                (solcSlotWord (forkAfterDstArt σ_solm I) I
                                  (forkDstArtSlot I))
                                (solcSlotWord (forkAfterDstArt σ_solm I) I
                                  (forkIlkRateSlot I)))
                              (by simpa [evm0, initState] using hwv) hsz164
                              hloadSrcInk rfl
                              (forkDinkSubGuardNegCond hsrcInkNegS)
                              (forkDinkSubGuardPosCond hsrcInkPosS)
                              (by simpa [evm1, storageStore_executionEnv] using hloadSrcArt)
                              rfl
                              (forkDartSubGuardNegCond hsrcArtNegS)
                              (forkDartSubGuardPosCond hsrcArtPosS)
                              (by simpa [evm2, evm1, storageStore_executionEnv]
                                using hloadDstInk)
                              rfl
                              (forkDinkAddGuardNegCond hdstInkNegS)
                              (forkDinkAddGuardPosCond hdstInkPosS)
                              (by simpa [evm3, evm2, evm1, storageStore_executionEnv]
                                using hloadDstArt)
                              rfl
                              (forkDartAddGuardNegCond hdstArtNegS)
                              (forkDartAddGuardPosCond hdstArtPosS)
                              (by
                                simpa [evm4, evm3, evm2, evm1, storageStore_executionEnv]
                                  using hloadFinal (forkSrcArtSlot I))
                              (by
                                simpa [evm4, evm3, evm2, evm1, storageStore_executionEnv]
                                  using hloadFinal (forkDstArtSlot I))
                              (by
                                simpa [evm4, evm3, evm2, evm1, storageStore_executionEnv]
                                  using hloadFinal (forkSrcInkSlot I))
                              (by
                                simpa [evm4, evm3, evm2, evm1, storageStore_executionEnv]
                                  using hloadFinal (forkDstInkSlot I))
                              (by
                                simpa [evm4, evm3, evm2, evm1, storageStore_executionEnv]
                                  using hloadFinal (forkIlkRateSlot I))
                              (by
                                simpa [evm4, evm3, evm2, evm1, storageStore_executionEnv]
                                  using hloadFinal (forkIlkSpotSlot I))
                              rfl hutabFitGuard.1 hutabFitGuard.2
                              rfl hvtabFitGuard.1 hvtabFitGuard.2
                              (forkUintCheckedMulFail_to_overflow hsrcInkSpotFailS)
                            obtain ⟨_, _, h4792⟩ := RD.vatForkSrcInkSubSuccess
                              (h := hdecoded) solcFreePtrMem_size hsz164
                              (by simpa [forkSrcInkNew] using hsrcInkNeg)
                              (by simpa [forkSrcInkNew] using hsrcInkPos)
                            obtain ⟨_, _, h4809⟩ := RD.vatForkSrcArtSubSuccess
                              (h := by simpa [forkSrcInkNew] using h4792) hperm
                              (by simpa [forkSrcArtNew, forkAfterSrcInk] using hsrcArtNeg)
                              (by simpa [forkSrcArtNew, forkAfterSrcInk] using hsrcArtPos)
                            obtain ⟨_, _, h4826⟩ := RD.vatForkDstInkAddSuccess
                              (h := by simpa [forkSrcArtNew, forkAfterSrcInk] using h4809)
                              hperm
                              (by simpa [forkDstInkNew, forkAfterSrcArt] using hdstInkNeg)
                              (by simpa [forkDstInkNew, forkAfterSrcArt] using hdstInkPos)
                            obtain ⟨_, _, h4843⟩ := RD.vatForkDstArtAddSuccess
                              (h := by simpa [forkDstInkNew, forkAfterSrcArt] using h4826)
                              hperm
                              (by simpa [forkDstArtNew, forkAfterDstInk] using hdstArtNeg)
                              (by simpa [forkDstArtNew, forkAfterDstInk] using hdstArtPos)
                            obtain ⟨_, _, h4871⟩ := RD.vatForkUtabMulSuccess
                              (h := by
                                simpa [forkDstArtNew, forkAfterDstInk] using h4843)
                              hperm
                              (by simpa [σFinal, forkAfterDstArt, forkDstArtNew,
                                forkAfterDstInk] using hutabOk)
                            obtain ⟨_, _, h4893⟩ := RD.vatForkVtabMulSuccess
                              (h := by
                                simpa [σFinal, forkAfterDstArt, forkDstArtNew,
                                  forkAfterDstInk] using h4871)
                              (by simpa [σFinal, forkAfterDstArt, forkDstArtNew,
                                forkAfterDstInk] using hvtabOk)
                            let memPrefix :=
                              twoWordHashMem (forkIlkWord I) ⟨2⟩
                                (wordAt0Mem (forkDstMaskedWord I)
                                  (twoWordHashMem (forkSrcMaskedWord I)
                                    (solcMappingSlot ⟨3⟩ (forkIlkWord I))
                                    (twoWordHashMem (forkIlkWord I) ⟨3⟩ solcFreePtrMem)))
                            have hmemPrefix : memPrefix.size = 96 := by
                              dsimp [memPrefix]
                              apply twoWordHashMem_size_96
                              apply wordAt0Mem_size_96
                              apply twoWordHashMem_size_96
                              apply twoWordHashMem_size_96
                              exact solcFreePtrMem_size
                            have hread64Prefix :
                                memPrefix.readWithPadding 64 32 =
                                  UInt256.toByteArray ⟨128⟩ := by
                              dsimp [memPrefix]
                              apply twoWordHashMem_read64
                              · apply wordAt0Mem_size_96
                                apply twoWordHashMem_size_96
                                apply twoWordHashMem_size_96
                                exact solcFreePtrMem_size
                              · rw [wordAt0Mem_read64]
                                apply twoWordHashMem_read64
                                · apply twoWordHashMem_size_96
                                  exact solcFreePtrMem_size
                                · apply twoWordHashMem_read64
                                  · exact solcFreePtrMem_size
                                  · exact solcFreePtrMem_read64
                                · apply twoWordHashMem_size_96
                                  apply twoWordHashMem_size_96
                                  exact solcFreePtrMem_size
                            by_cases hwish : forkBothWishWord σFinal I ≠ ⟨0⟩
                            · obtain ⟨_, _, h4990⟩ := RD.vatForkWishSuccess
                                (h := by
                                  simpa [σFinal, forkAfterDstArt, forkDstArtNew,
                                    forkAfterDstInk, memPrefix] using h4893)
                                hmemPrefix
                                (by simpa [σFinal] using hwish)
                              have hrev := RD.vatForkSrcUnsafeMulRevert
                                (h := by
                                  simpa [σFinal, forkAfterDstArt, forkDstArtNew,
                                    forkAfterDstInk] using h4990)
                                (by simpa [σFinal, forkAfterDstArt, forkDstArtNew,
                                  forkAfterDstInk] using hsrcInkSpotOk)
                              exact hrev.reEquivExecutionRevert hcode (vatDispatchFork hsel)
                                hdecode hbody
                            · have hwishZero : forkBothWishWord σFinal I = ⟨0⟩ := by
                                by_contra hne
                                exact hwish hne
                              have hrev := RD.vatForkWishBranchRevert
                                (h := by
                                  simpa [σFinal, forkAfterDstArt, forkDstArtNew,
                                    forkAfterDstInk, memPrefix] using h4893)
                                hmemPrefix hread64Prefix
                                (by simpa [σFinal] using hwishZero)
                              exact hrev.reEquivExecutionRevert hcode (vatDispatchFork hsel)
                                hdecode hbody
                        · have hsrcInkNegS :
                              UInt256.sgt (forkDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
                                UInt256.gt (forkSrcInkNew σ_solm I)
                                  (solcSlotWord σ_solm I (forkSrcInkSlot I)) = ⟨0⟩ :=
                            (forkSrcInkSubGuardNeg_iff_of_accountMapEquiv (I := I)
                              hAccounts).mp hsrcInkNeg
                          have hsrcInkPosS :
                              UInt256.slt (forkDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
                                UInt256.lt (forkSrcInkNew σ_solm I)
                                  (solcSlotWord σ_solm I (forkSrcInkSlot I)) = ⟨0⟩ :=
                            (forkSrcInkSubGuardPos_iff_of_accountMapEquiv (I := I)
                              hAccounts).mp hsrcInkPos
                          have hsrcArtNegS :
                              UInt256.sgt (forkDartWord I) ⟨0⟩ = ⟨0⟩ ∨
                                UInt256.gt (forkSrcArtNew σ_solm I)
                                  (solcSlotWord (forkAfterSrcInk σ_solm I) I
                                    (forkSrcArtSlot I)) = ⟨0⟩ :=
                            (forkSrcArtSubGuardNeg_iff_of_accountMapEquiv (I := I)
                              hAccounts).mp hsrcArtNeg
                          have hsrcArtPosS :
                              UInt256.slt (forkDartWord I) ⟨0⟩ = ⟨0⟩ ∨
                                UInt256.lt (forkSrcArtNew σ_solm I)
                                  (solcSlotWord (forkAfterSrcInk σ_solm I) I
                                    (forkSrcArtSlot I)) = ⟨0⟩ :=
                            (forkSrcArtSubGuardPos_iff_of_accountMapEquiv (I := I)
                              hAccounts).mp hsrcArtPos
                          have hdstInkNegS :
                              UInt256.slt (forkDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
                                UInt256.gt (forkDstInkNew σ_solm I)
                                  (solcSlotWord (forkAfterSrcArt σ_solm I) I
                                    (forkDstInkSlot I)) = ⟨0⟩ :=
                            (forkDstInkAddGuardNeg_iff_of_accountMapEquiv (I := I)
                              hAccounts).mp hdstInkNeg
                          have hdstInkPosS :
                              UInt256.sgt (forkDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
                                UInt256.lt (forkDstInkNew σ_solm I)
                                  (solcSlotWord (forkAfterSrcArt σ_solm I) I
                                    (forkDstInkSlot I)) = ⟨0⟩ :=
                            (forkDstInkAddGuardPos_iff_of_accountMapEquiv (I := I)
                              hAccounts).mp hdstInkPos
                          have hdstArtNegS :
                              UInt256.slt (forkDartWord I) ⟨0⟩ = ⟨0⟩ ∨
                                UInt256.gt (forkDstArtNew σ_solm I)
                                  (solcSlotWord (forkAfterDstInk σ_solm I) I
                                    (forkDstArtSlot I)) = ⟨0⟩ :=
                            (forkDstArtAddGuardNeg_iff_of_accountMapEquiv (I := I)
                              hAccounts).mp hdstArtNeg
                          have hdstArtPosS :
                              UInt256.sgt (forkDartWord I) ⟨0⟩ = ⟨0⟩ ∨
                                UInt256.lt (forkDstArtNew σ_solm I)
                                  (solcSlotWord (forkAfterDstInk σ_solm I) I
                                    (forkDstArtSlot I)) = ⟨0⟩ :=
                            (forkDstArtAddGuardPos_iff_of_accountMapEquiv (I := I)
                              hAccounts).mp hdstArtPos
                          let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
                          let evm1 := Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner
                            (forkSrcInkSlot I) (forkSrcInkNew σ_solm I)
                          let evm2 := Solm.EVM.storageStore evm1 evm1.executionEnv.codeOwner
                            (forkSrcArtSlot I) (forkSrcArtNew σ_solm I)
                          let evm3 := Solm.EVM.storageStore evm2 evm2.executionEnv.codeOwner
                            (forkDstInkSlot I) (forkDstInkNew σ_solm I)
                          let evm4 := Solm.EVM.storageStore evm3 evm3.executionEnv.codeOwner
                            (forkDstArtSlot I) (forkDstArtNew σ_solm I)
                          have hloadSrcInk :
                              Solm.EVM.storageLoad evm0 evm0.executionEnv.codeOwner
                                (forkSrcInkSlot I) =
                              solcSlotWord σ_solm I (forkSrcInkSlot I) := by
                            simp [evm0, initState, Solm.EVM.storageLoad, solcSlotWord,
                              State.lookupAccount, Account.lookupStorage]
                          have hloadSrcArt :
                              Solm.EVM.storageLoad evm1 evm1.executionEnv.codeOwner
                                (forkSrcArtSlot I) =
                              solcSlotWord (forkAfterSrcInk σ_solm I) I
                                (forkSrcArtSlot I) := by
                            simp [evm1, evm0, initState, Solm.EVM.storageLoad,
                              solcSlotWord, State.lookupAccount, Account.lookupStorage,
                              storageStore_accountMap, storageStore_executionEnv,
                              forkAfterSrcInk]
                          have hloadDstInk :
                              Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner
                                (forkDstInkSlot I) =
                              solcSlotWord (forkAfterSrcArt σ_solm I) I
                                (forkDstInkSlot I) := by
                            simp [evm2, evm1, evm0, initState, Solm.EVM.storageLoad,
                              solcSlotWord, State.lookupAccount, Account.lookupStorage,
                              storageStore_accountMap, storageStore_executionEnv,
                              forkAfterSrcInk, forkAfterSrcArt]
                          have hloadDstArt :
                              Solm.EVM.storageLoad evm3 evm3.executionEnv.codeOwner
                                (forkDstArtSlot I) =
                              solcSlotWord (forkAfterDstInk σ_solm I) I
                                (forkDstArtSlot I) := by
                            simp [evm3, evm2, evm1, evm0, initState, Solm.EVM.storageLoad,
                              solcSlotWord, State.lookupAccount, Account.lookupStorage,
                              storageStore_accountMap, storageStore_executionEnv,
                              forkAfterSrcInk, forkAfterSrcArt, forkAfterDstInk]
                          have hloadFinal (slot : UInt256) :
                              Solm.EVM.storageLoad evm4 evm4.executionEnv.codeOwner slot =
                                solcSlotWord (forkAfterDstArt σ_solm I) I slot := by
                            simpa [evm4, evm3, evm2, evm1, evm0,
                              storageStore_executionEnv] using
                                forkSourceFinal_storageLoad (cA := cA) (gh := gh)
                                  (bl := bl) (σ := σ_solm) (σ₀ := σ₀) (A := A)
                                  (I := I) (g := g)
                                  (forkSrcInkNew σ_solm I) (forkSrcArtNew σ_solm I)
                                  (forkDstInkNew σ_solm I) (forkDstArtNew σ_solm I)
                                  slot rfl rfl rfl rfl
                          have hutabOkS :
                              solcSlotWord (forkAfterDstArt σ_solm I) I
                                    (forkIlkRateSlot I) = ⟨0⟩ ∨
                                  UInt256.eq
                                    (UInt256.div
                                      (UInt256.mul
                                        (solcSlotWord (forkAfterDstArt σ_solm I) I
                                          (forkSrcArtSlot I))
                                        (solcSlotWord (forkAfterDstArt σ_solm I) I
                                          (forkIlkRateSlot I)))
                                      (solcSlotWord (forkAfterDstArt σ_solm I) I
                                        (forkIlkRateSlot I)))
                                    (solcSlotWord (forkAfterDstArt σ_solm I) I
                                      (forkSrcArtSlot I)) ≠ ⟨0⟩ := by
                            have hart := forkAfterDstArt_slot_eq_of_accountMapEquiv
                              (I := I) hAccounts (forkSrcArtSlot I)
                            have hrate := forkAfterDstArt_slot_eq_of_accountMapEquiv
                              (I := I) hAccounts (forkIlkRateSlot I)
                            simpa [σFinal, hart, hrate] using hutabOk
                          have hvtabFailS :
                              ¬ (solcSlotWord (forkAfterDstArt σ_solm I) I
                                    (forkIlkRateSlot I) = ⟨0⟩ ∨
                                  UInt256.eq
                                    (UInt256.div
                                      (UInt256.mul
                                        (solcSlotWord (forkAfterDstArt σ_solm I) I
                                          (forkDstArtSlot I))
                                        (solcSlotWord (forkAfterDstArt σ_solm I) I
                                          (forkIlkRateSlot I)))
                                      (solcSlotWord (forkAfterDstArt σ_solm I) I
                                        (forkIlkRateSlot I)))
                                    (solcSlotWord (forkAfterDstArt σ_solm I) I
                                      (forkDstArtSlot I)) ≠ ⟨0⟩) := by
                            intro hokS
                            have hart := forkAfterDstArt_slot_eq_of_accountMapEquiv
                              (I := I) hAccounts (forkDstArtSlot I)
                            have hrate := forkAfterDstArt_slot_eq_of_accountMapEquiv
                              (I := I) hAccounts (forkIlkRateSlot I)
                            exact hvtabOk (by simpa [σFinal, hart, hrate] using hokS)
                          have hutabFitGuard := forkUintCheckedMulGuard_to_fit_and_source_guard
                            (a := solcSlotWord (forkAfterDstArt σ_solm I) I
                              (forkSrcArtSlot I))
                            (b := solcSlotWord (forkAfterDstArt σ_solm I) I
                              (forkIlkRateSlot I))
                            hutabOkS
                          have hbody := execForkSourceRevertVtabMul
                            (evm0 := evm0) (I := I)
                            (solcSlotWord σ_solm I (forkSrcInkSlot I))
                            (forkSrcInkNew σ_solm I)
                            (solcSlotWord (forkAfterSrcInk σ_solm I) I
                              (forkSrcArtSlot I))
                            (forkSrcArtNew σ_solm I)
                            (solcSlotWord (forkAfterSrcArt σ_solm I) I
                              (forkDstInkSlot I))
                            (forkDstInkNew σ_solm I)
                            (solcSlotWord (forkAfterDstInk σ_solm I) I
                              (forkDstArtSlot I))
                            (forkDstArtNew σ_solm I)
                            (solcSlotWord (forkAfterDstArt σ_solm I) I
                              (forkSrcArtSlot I))
                            (solcSlotWord (forkAfterDstArt σ_solm I) I
                              (forkDstArtSlot I))
                            (solcSlotWord (forkAfterDstArt σ_solm I) I
                              (forkSrcInkSlot I))
                            (solcSlotWord (forkAfterDstArt σ_solm I) I
                              (forkDstInkSlot I))
                            (solcSlotWord (forkAfterDstArt σ_solm I) I
                              (forkIlkRateSlot I))
                            (UInt256.mul
                              (solcSlotWord (forkAfterDstArt σ_solm I) I
                                (forkSrcArtSlot I))
                              (solcSlotWord (forkAfterDstArt σ_solm I) I
                                (forkIlkRateSlot I)))
                            (by simpa [evm0, initState] using hwv) hsz164
                            hloadSrcInk rfl
                            (forkDinkSubGuardNegCond hsrcInkNegS)
                            (forkDinkSubGuardPosCond hsrcInkPosS)
                            (by simpa [evm1, storageStore_executionEnv] using hloadSrcArt)
                            rfl
                            (forkDartSubGuardNegCond hsrcArtNegS)
                            (forkDartSubGuardPosCond hsrcArtPosS)
                            (by simpa [evm2, evm1, storageStore_executionEnv]
                              using hloadDstInk)
                            rfl
                            (forkDinkAddGuardNegCond hdstInkNegS)
                            (forkDinkAddGuardPosCond hdstInkPosS)
                            (by simpa [evm3, evm2, evm1, storageStore_executionEnv]
                              using hloadDstArt)
                            rfl
                            (forkDartAddGuardNegCond hdstArtNegS)
                            (forkDartAddGuardPosCond hdstArtPosS)
                            (by
                              simpa [evm4, evm3, evm2, evm1, storageStore_executionEnv]
                                using hloadFinal (forkSrcArtSlot I))
                            (by
                              simpa [evm4, evm3, evm2, evm1, storageStore_executionEnv]
                                using hloadFinal (forkDstArtSlot I))
                            (by
                              simpa [evm4, evm3, evm2, evm1, storageStore_executionEnv]
                                using hloadFinal (forkSrcInkSlot I))
                            (by
                              simpa [evm4, evm3, evm2, evm1, storageStore_executionEnv]
                                using hloadFinal (forkDstInkSlot I))
                            (by
                              simpa [evm4, evm3, evm2, evm1, storageStore_executionEnv]
                                using hloadFinal (forkIlkRateSlot I))
                            rfl hutabFitGuard.1 hutabFitGuard.2
                            (forkUintCheckedMulFail_to_overflow hvtabFailS)
                          obtain ⟨_, _, h4792⟩ := RD.vatForkSrcInkSubSuccess
                            (h := hdecoded) solcFreePtrMem_size hsz164
                            (by simpa [forkSrcInkNew] using hsrcInkNeg)
                            (by simpa [forkSrcInkNew] using hsrcInkPos)
                          obtain ⟨_, _, h4809⟩ := RD.vatForkSrcArtSubSuccess
                            (h := by simpa [forkSrcInkNew] using h4792) hperm
                            (by simpa [forkSrcArtNew, forkAfterSrcInk] using hsrcArtNeg)
                            (by simpa [forkSrcArtNew, forkAfterSrcInk] using hsrcArtPos)
                          obtain ⟨_, _, h4826⟩ := RD.vatForkDstInkAddSuccess
                            (h := by simpa [forkSrcArtNew, forkAfterSrcInk] using h4809)
                            hperm
                            (by simpa [forkDstInkNew, forkAfterSrcArt] using hdstInkNeg)
                            (by simpa [forkDstInkNew, forkAfterSrcArt] using hdstInkPos)
                          obtain ⟨_, _, h4843⟩ := RD.vatForkDstArtAddSuccess
                            (h := by simpa [forkDstInkNew, forkAfterSrcArt] using h4826)
                            hperm
                            (by simpa [forkDstArtNew, forkAfterDstInk] using hdstArtNeg)
                            (by simpa [forkDstArtNew, forkAfterDstInk] using hdstArtPos)
                          obtain ⟨_, _, h4871⟩ := RD.vatForkUtabMulSuccess
                            (h := by
                              simpa [forkDstArtNew, forkAfterDstInk] using h4843)
                            hperm
                            (by simpa [σFinal, forkAfterDstArt, forkDstArtNew,
                              forkAfterDstInk] using hutabOk)
                          have hrev := RD.vatForkVtabMulRevert
                            (h := by
                              simpa [σFinal, forkAfterDstArt, forkDstArtNew,
                                forkAfterDstInk] using h4871)
                            (by simpa [σFinal, forkAfterDstArt, forkDstArtNew,
                              forkAfterDstInk] using hvtabOk)
                          exact hrev.reEquivExecutionRevert hcode (vatDispatchFork hsel)
                            hdecode hbody
                      · have hsrcInkNegS :
                            UInt256.sgt (forkDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
                              UInt256.gt (forkSrcInkNew σ_solm I)
                                (solcSlotWord σ_solm I (forkSrcInkSlot I)) = ⟨0⟩ :=
                          (forkSrcInkSubGuardNeg_iff_of_accountMapEquiv (I := I)
                            hAccounts).mp hsrcInkNeg
                        have hsrcInkPosS :
                            UInt256.slt (forkDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
                              UInt256.lt (forkSrcInkNew σ_solm I)
                                (solcSlotWord σ_solm I (forkSrcInkSlot I)) = ⟨0⟩ :=
                          (forkSrcInkSubGuardPos_iff_of_accountMapEquiv (I := I)
                            hAccounts).mp hsrcInkPos
                        have hsrcArtNegS :
                            UInt256.sgt (forkDartWord I) ⟨0⟩ = ⟨0⟩ ∨
                              UInt256.gt (forkSrcArtNew σ_solm I)
                                (solcSlotWord (forkAfterSrcInk σ_solm I) I
                                  (forkSrcArtSlot I)) = ⟨0⟩ :=
                          (forkSrcArtSubGuardNeg_iff_of_accountMapEquiv (I := I)
                            hAccounts).mp hsrcArtNeg
                        have hsrcArtPosS :
                            UInt256.slt (forkDartWord I) ⟨0⟩ = ⟨0⟩ ∨
                              UInt256.lt (forkSrcArtNew σ_solm I)
                                (solcSlotWord (forkAfterSrcInk σ_solm I) I
                                  (forkSrcArtSlot I)) = ⟨0⟩ :=
                          (forkSrcArtSubGuardPos_iff_of_accountMapEquiv (I := I)
                            hAccounts).mp hsrcArtPos
                        have hdstInkNegS :
                            UInt256.slt (forkDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
                              UInt256.gt (forkDstInkNew σ_solm I)
                                (solcSlotWord (forkAfterSrcArt σ_solm I) I
                                  (forkDstInkSlot I)) = ⟨0⟩ :=
                          (forkDstInkAddGuardNeg_iff_of_accountMapEquiv (I := I)
                            hAccounts).mp hdstInkNeg
                        have hdstInkPosS :
                            UInt256.sgt (forkDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
                              UInt256.lt (forkDstInkNew σ_solm I)
                                (solcSlotWord (forkAfterSrcArt σ_solm I) I
                                  (forkDstInkSlot I)) = ⟨0⟩ :=
                          (forkDstInkAddGuardPos_iff_of_accountMapEquiv (I := I)
                            hAccounts).mp hdstInkPos
                        have hdstArtNegS :
                            UInt256.slt (forkDartWord I) ⟨0⟩ = ⟨0⟩ ∨
                              UInt256.gt (forkDstArtNew σ_solm I)
                                (solcSlotWord (forkAfterDstInk σ_solm I) I
                                  (forkDstArtSlot I)) = ⟨0⟩ :=
                          (forkDstArtAddGuardNeg_iff_of_accountMapEquiv (I := I)
                            hAccounts).mp hdstArtNeg
                        have hdstArtPosS :
                            UInt256.sgt (forkDartWord I) ⟨0⟩ = ⟨0⟩ ∨
                              UInt256.lt (forkDstArtNew σ_solm I)
                                (solcSlotWord (forkAfterDstInk σ_solm I) I
                                  (forkDstArtSlot I)) = ⟨0⟩ :=
                          (forkDstArtAddGuardPos_iff_of_accountMapEquiv (I := I)
                            hAccounts).mp hdstArtPos
                        let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
                        let evm1 := Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner
                          (forkSrcInkSlot I) (forkSrcInkNew σ_solm I)
                        let evm2 := Solm.EVM.storageStore evm1 evm1.executionEnv.codeOwner
                          (forkSrcArtSlot I) (forkSrcArtNew σ_solm I)
                        let evm3 := Solm.EVM.storageStore evm2 evm2.executionEnv.codeOwner
                          (forkDstInkSlot I) (forkDstInkNew σ_solm I)
                        let evm4 := Solm.EVM.storageStore evm3 evm3.executionEnv.codeOwner
                          (forkDstArtSlot I) (forkDstArtNew σ_solm I)
                        have hloadSrcInk :
                            Solm.EVM.storageLoad evm0 evm0.executionEnv.codeOwner
                              (forkSrcInkSlot I) =
                            solcSlotWord σ_solm I (forkSrcInkSlot I) := by
                          simp [evm0, initState, Solm.EVM.storageLoad, solcSlotWord,
                            State.lookupAccount, Account.lookupStorage]
                        have hloadSrcArt :
                            Solm.EVM.storageLoad evm1 evm1.executionEnv.codeOwner
                              (forkSrcArtSlot I) =
                            solcSlotWord (forkAfterSrcInk σ_solm I) I
                              (forkSrcArtSlot I) := by
                          simp [evm1, evm0, initState, Solm.EVM.storageLoad, solcSlotWord,
                            State.lookupAccount, Account.lookupStorage, storageStore_accountMap,
                            storageStore_executionEnv, forkAfterSrcInk]
                        have hloadDstInk :
                            Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner
                              (forkDstInkSlot I) =
                            solcSlotWord (forkAfterSrcArt σ_solm I) I
                              (forkDstInkSlot I) := by
                          simp [evm2, evm1, evm0, initState, Solm.EVM.storageLoad,
                            solcSlotWord, State.lookupAccount, Account.lookupStorage,
                            storageStore_accountMap, storageStore_executionEnv,
                            forkAfterSrcInk, forkAfterSrcArt]
                        have hloadDstArt :
                            Solm.EVM.storageLoad evm3 evm3.executionEnv.codeOwner
                              (forkDstArtSlot I) =
                            solcSlotWord (forkAfterDstInk σ_solm I) I
                              (forkDstArtSlot I) := by
                          simp [evm3, evm2, evm1, evm0, initState, Solm.EVM.storageLoad,
                            solcSlotWord, State.lookupAccount, Account.lookupStorage,
                            storageStore_accountMap, storageStore_executionEnv,
                            forkAfterSrcInk, forkAfterSrcArt, forkAfterDstInk]
                        have hloadFinal (slot : UInt256) :
                            Solm.EVM.storageLoad evm4 evm4.executionEnv.codeOwner slot =
                              solcSlotWord (forkAfterDstArt σ_solm I) I slot := by
                          simpa [evm4, evm3, evm2, evm1, evm0, storageStore_executionEnv]
                            using
                              forkSourceFinal_storageLoad (cA := cA) (gh := gh) (bl := bl)
                                (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
                                (forkSrcInkNew σ_solm I) (forkSrcArtNew σ_solm I)
                                (forkDstInkNew σ_solm I) (forkDstArtNew σ_solm I)
                                slot rfl rfl rfl rfl
                        have hutabFailS :
                            ¬ (solcSlotWord (forkAfterDstArt σ_solm I) I
                                  (forkIlkRateSlot I) = ⟨0⟩ ∨
                                UInt256.eq
                                  (UInt256.div
                                    (UInt256.mul
                                      (solcSlotWord (forkAfterDstArt σ_solm I) I
                                        (forkSrcArtSlot I))
                                      (solcSlotWord (forkAfterDstArt σ_solm I) I
                                        (forkIlkRateSlot I)))
                                    (solcSlotWord (forkAfterDstArt σ_solm I) I
                                      (forkIlkRateSlot I)))
                                  (solcSlotWord (forkAfterDstArt σ_solm I) I
                                    (forkSrcArtSlot I)) ≠ ⟨0⟩) := by
                          intro hokS
                          have hart := forkAfterDstArt_slot_eq_of_accountMapEquiv
                            (I := I) hAccounts (forkSrcArtSlot I)
                          have hrate := forkAfterDstArt_slot_eq_of_accountMapEquiv
                            (I := I) hAccounts (forkIlkRateSlot I)
                          exact hutabOk (by simpa [σFinal, hart, hrate] using hokS)
                        have hbody := execForkSourceRevertUtabMul
                          (evm0 := evm0) (I := I)
                          (solcSlotWord σ_solm I (forkSrcInkSlot I)) (forkSrcInkNew σ_solm I)
                          (solcSlotWord (forkAfterSrcInk σ_solm I) I (forkSrcArtSlot I))
                          (forkSrcArtNew σ_solm I)
                          (solcSlotWord (forkAfterSrcArt σ_solm I) I (forkDstInkSlot I))
                          (forkDstInkNew σ_solm I)
                          (solcSlotWord (forkAfterDstInk σ_solm I) I (forkDstArtSlot I))
                          (forkDstArtNew σ_solm I)
                          (solcSlotWord (forkAfterDstArt σ_solm I) I (forkSrcArtSlot I))
                          (solcSlotWord (forkAfterDstArt σ_solm I) I (forkDstArtSlot I))
                          (solcSlotWord (forkAfterDstArt σ_solm I) I (forkSrcInkSlot I))
                          (solcSlotWord (forkAfterDstArt σ_solm I) I (forkDstInkSlot I))
                          (solcSlotWord (forkAfterDstArt σ_solm I) I (forkIlkRateSlot I))
                          (by simpa [evm0, initState] using hwv) hsz164
                          hloadSrcInk rfl
                          (forkDinkSubGuardNegCond hsrcInkNegS)
                          (forkDinkSubGuardPosCond hsrcInkPosS)
                          (by simpa [evm1, storageStore_executionEnv] using hloadSrcArt) rfl
                          (forkDartSubGuardNegCond hsrcArtNegS)
                          (forkDartSubGuardPosCond hsrcArtPosS)
                          (by simpa [evm2, evm1, storageStore_executionEnv] using hloadDstInk)
                          rfl
                          (forkDinkAddGuardNegCond hdstInkNegS)
                          (forkDinkAddGuardPosCond hdstInkPosS)
                          (by simpa [evm3, evm2, evm1, storageStore_executionEnv]
                            using hloadDstArt)
                          rfl
                          (forkDartAddGuardNegCond hdstArtNegS)
                          (forkDartAddGuardPosCond hdstArtPosS)
                          (by
                            simpa [evm4, evm3, evm2, evm1, storageStore_executionEnv]
                              using hloadFinal (forkSrcArtSlot I))
                          (by
                            simpa [evm4, evm3, evm2, evm1, storageStore_executionEnv]
                              using hloadFinal (forkDstArtSlot I))
                          (by
                            simpa [evm4, evm3, evm2, evm1, storageStore_executionEnv]
                              using hloadFinal (forkSrcInkSlot I))
                          (by
                            simpa [evm4, evm3, evm2, evm1, storageStore_executionEnv]
                              using hloadFinal (forkDstInkSlot I))
                          (by
                            simpa [evm4, evm3, evm2, evm1, storageStore_executionEnv]
                              using hloadFinal (forkIlkRateSlot I))
                          (forkUintCheckedMulFail_to_overflow hutabFailS)
                        obtain ⟨_, _, h4792⟩ := RD.vatForkSrcInkSubSuccess
                          (h := hdecoded) solcFreePtrMem_size hsz164
                          (by simpa [forkSrcInkNew] using hsrcInkNeg)
                          (by simpa [forkSrcInkNew] using hsrcInkPos)
                        obtain ⟨_, _, h4809⟩ := RD.vatForkSrcArtSubSuccess
                          (h := by simpa [forkSrcInkNew] using h4792) hperm
                          (by simpa [forkSrcArtNew, forkAfterSrcInk] using hsrcArtNeg)
                          (by simpa [forkSrcArtNew, forkAfterSrcInk] using hsrcArtPos)
                        obtain ⟨_, _, h4826⟩ := RD.vatForkDstInkAddSuccess
                          (h := by simpa [forkSrcArtNew, forkAfterSrcInk] using h4809) hperm
                          (by simpa [forkDstInkNew, forkAfterSrcArt] using hdstInkNeg)
                          (by simpa [forkDstInkNew, forkAfterSrcArt] using hdstInkPos)
                        obtain ⟨_, _, h4843⟩ := RD.vatForkDstArtAddSuccess
                          (h := by simpa [forkDstInkNew, forkAfterSrcArt] using h4826) hperm
                          (by simpa [forkDstArtNew, forkAfterDstInk] using hdstArtNeg)
                          (by simpa [forkDstArtNew, forkAfterDstInk] using hdstArtPos)
                        have hrev := RD.vatForkUtabMulRevert
                          (h := by
                            simpa [forkDstArtNew, forkAfterDstInk] using h4843)
                          hperm
                          (by simpa [σFinal, forkAfterDstArt, forkDstArtNew,
                            forkAfterDstInk] using hutabOk)
                        exact hrev.reEquivExecutionRevert hcode (vatDispatchFork hsel)
                          hdecode hbody
                  · have hsrcInkNegS :
                        UInt256.sgt (forkDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
                          UInt256.gt (forkSrcInkNew σ_solm I)
                            (solcSlotWord σ_solm I (forkSrcInkSlot I)) = ⟨0⟩ :=
                      (forkSrcInkSubGuardNeg_iff_of_accountMapEquiv (I := I) hAccounts).mp
                        hsrcInkNeg
                    have hsrcInkPosS :
                        UInt256.slt (forkDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
                          UInt256.lt (forkSrcInkNew σ_solm I)
                            (solcSlotWord σ_solm I (forkSrcInkSlot I)) = ⟨0⟩ :=
                      (forkSrcInkSubGuardPos_iff_of_accountMapEquiv (I := I) hAccounts).mp
                        hsrcInkPos
                    have hsrcArtNegS :
                        UInt256.sgt (forkDartWord I) ⟨0⟩ = ⟨0⟩ ∨
                          UInt256.gt (forkSrcArtNew σ_solm I)
                            (solcSlotWord (forkAfterSrcInk σ_solm I) I (forkSrcArtSlot I)) = ⟨0⟩ :=
                      (forkSrcArtSubGuardNeg_iff_of_accountMapEquiv (I := I) hAccounts).mp
                        hsrcArtNeg
                    have hsrcArtPosS :
                        UInt256.slt (forkDartWord I) ⟨0⟩ = ⟨0⟩ ∨
                          UInt256.lt (forkSrcArtNew σ_solm I)
                            (solcSlotWord (forkAfterSrcInk σ_solm I) I (forkSrcArtSlot I)) = ⟨0⟩ :=
                      (forkSrcArtSubGuardPos_iff_of_accountMapEquiv (I := I) hAccounts).mp
                        hsrcArtPos
                    have hdstInkNegS :
                        UInt256.slt (forkDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
                          UInt256.gt (forkDstInkNew σ_solm I)
                            (solcSlotWord (forkAfterSrcArt σ_solm I) I (forkDstInkSlot I)) = ⟨0⟩ :=
                      (forkDstInkAddGuardNeg_iff_of_accountMapEquiv (I := I) hAccounts).mp
                        hdstInkNeg
                    have hdstInkPosS :
                        UInt256.sgt (forkDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
                          UInt256.lt (forkDstInkNew σ_solm I)
                            (solcSlotWord (forkAfterSrcArt σ_solm I) I (forkDstInkSlot I)) = ⟨0⟩ :=
                      (forkDstInkAddGuardPos_iff_of_accountMapEquiv (I := I) hAccounts).mp
                        hdstInkPos
                    have hdstArtNegS :
                        UInt256.slt (forkDartWord I) ⟨0⟩ = ⟨0⟩ ∨
                          UInt256.gt (forkDstArtNew σ_solm I)
                            (solcSlotWord (forkAfterDstInk σ_solm I) I (forkDstArtSlot I)) = ⟨0⟩ :=
                      (forkDstArtAddGuardNeg_iff_of_accountMapEquiv (I := I) hAccounts).mp
                        hdstArtNeg
                    have hdstArtPosFailS :
                        ¬ (UInt256.sgt (forkDartWord I) ⟨0⟩ = ⟨0⟩ ∨
                          UInt256.lt (forkDstArtNew σ_solm I)
                            (solcSlotWord (forkAfterDstInk σ_solm I) I (forkDstArtSlot I)) = ⟨0⟩) := by
                      intro hs
                      exact hdstArtPos ((forkDstArtAddGuardPos_iff_of_accountMapEquiv
                        (I := I) hAccounts).mpr hs)
                    have hloadSrcInk :
                        Solm.EVM.storageLoad
                          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
                          (forkSrcInkSlot I) =
                        solcSlotWord σ_solm I (forkSrcInkSlot I) := by
                      simp [initState, Solm.EVM.storageLoad, solcSlotWord, State.lookupAccount,
                        Account.lookupStorage]
                    have hloadSrcArt :
                        Solm.EVM.storageLoad
                          (Solm.EVM.storageStore
                            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
                            (forkSrcInkSlot I) (forkSrcInkNew σ_solm I))
                          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
                          (forkSrcArtSlot I) =
                        solcSlotWord (forkAfterSrcInk σ_solm I) I (forkSrcArtSlot I) := by
                      simp [initState, Solm.EVM.storageLoad, solcSlotWord, State.lookupAccount,
                        Account.lookupStorage, storageStore_accountMap, forkAfterSrcInk]
                    have hloadDstInk :
                        Solm.EVM.storageLoad
                          (Solm.EVM.storageStore
                            (Solm.EVM.storageStore
                              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
                              (forkSrcInkSlot I) (forkSrcInkNew σ_solm I))
                            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
                            (forkSrcArtSlot I) (forkSrcArtNew σ_solm I))
                          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
                          (forkDstInkSlot I) =
                        solcSlotWord (forkAfterSrcArt σ_solm I) I (forkDstInkSlot I) := by
                      simp [initState, Solm.EVM.storageLoad, solcSlotWord, State.lookupAccount,
                        Account.lookupStorage, storageStore_accountMap, forkAfterSrcInk, forkAfterSrcArt]
                    have hloadDstArt :
                        Solm.EVM.storageLoad
                          (Solm.EVM.storageStore
                            (Solm.EVM.storageStore
                              (Solm.EVM.storageStore
                                (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                                (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
                                (forkSrcInkSlot I) (forkSrcInkNew σ_solm I))
                              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
                              (forkSrcArtSlot I) (forkSrcArtNew σ_solm I))
                            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
                            (forkDstInkSlot I) (forkDstInkNew σ_solm I))
                          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
                          (forkDstArtSlot I) =
                        solcSlotWord (forkAfterDstInk σ_solm I) I (forkDstArtSlot I) := by
                      simp [initState, Solm.EVM.storageLoad, solcSlotWord, State.lookupAccount,
                        Account.lookupStorage, storageStore_accountMap, forkAfterSrcInk,
                        forkAfterSrcArt, forkAfterDstInk]
                    have hbody := execForkSourceRevertDstArtGuardPos
                      (evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) (I := I)
                      (solcSlotWord σ_solm I (forkSrcInkSlot I)) (forkSrcInkNew σ_solm I)
                      (solcSlotWord (forkAfterSrcInk σ_solm I) I (forkSrcArtSlot I))
                      (forkSrcArtNew σ_solm I)
                      (solcSlotWord (forkAfterSrcArt σ_solm I) I (forkDstInkSlot I))
                      (forkDstInkNew σ_solm I)
                      (solcSlotWord (forkAfterDstInk σ_solm I) I (forkDstArtSlot I))
                      (forkDstArtNew σ_solm I)
                      (by simpa [initState] using hwv) hsz164 hloadSrcInk rfl
                      (forkDinkSubGuardNegCond hsrcInkNegS)
                      (forkDinkSubGuardPosCond hsrcInkPosS)
                      hloadSrcArt rfl
                      (forkDartSubGuardNegCond hsrcArtNegS)
                      (forkDartSubGuardPosCond hsrcArtPosS)
                      hloadDstInk rfl
                      (forkDinkAddGuardNegCond hdstInkNegS)
                      (forkDinkAddGuardPosCond hdstInkPosS)
                      hloadDstArt rfl hdstArtNegS hdstArtPosFailS
                    obtain ⟨_, _, h4792⟩ := RD.vatForkSrcInkSubSuccess
                      (h := hdecoded) solcFreePtrMem_size hsz164
                      (by simpa [forkSrcInkNew] using hsrcInkNeg)
                      (by simpa [forkSrcInkNew] using hsrcInkPos)
                    obtain ⟨_, _, h4809⟩ := RD.vatForkSrcArtSubSuccess
                      (h := by simpa [forkSrcInkNew] using h4792) hperm
                      (by simpa [forkSrcArtNew, forkAfterSrcInk] using hsrcArtNeg)
                      (by simpa [forkSrcArtNew, forkAfterSrcInk] using hsrcArtPos)
                    obtain ⟨_, _, h4826⟩ := RD.vatForkDstInkAddSuccess
                      (h := by simpa [forkSrcArtNew, forkAfterSrcInk] using h4809) hperm
                      (by simpa [forkDstInkNew, forkAfterSrcArt] using hdstInkNeg)
                      (by simpa [forkDstInkNew, forkAfterSrcArt] using hdstInkPos)
                    have hrev := RD.vatForkDstArtAddRevert
                      (h := by simpa [forkDstInkNew, forkAfterSrcArt] using h4826) hperm
                      (Or.inr ⟨by simpa [forkDstArtNew, forkAfterDstInk] using hdstArtNeg,
                        by simpa [forkDstArtNew, forkAfterDstInk] using hdstArtPos⟩)
                    exact hrev.reEquivExecutionRevert hcode (vatDispatchFork hsel) hdecode hbody
                · have hsrcInkNegS :
                      UInt256.sgt (forkDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
                        UInt256.gt (forkSrcInkNew σ_solm I)
                          (solcSlotWord σ_solm I (forkSrcInkSlot I)) = ⟨0⟩ :=
                    (forkSrcInkSubGuardNeg_iff_of_accountMapEquiv (I := I) hAccounts).mp
                      hsrcInkNeg
                  have hsrcInkPosS :
                      UInt256.slt (forkDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
                        UInt256.lt (forkSrcInkNew σ_solm I)
                          (solcSlotWord σ_solm I (forkSrcInkSlot I)) = ⟨0⟩ :=
                    (forkSrcInkSubGuardPos_iff_of_accountMapEquiv (I := I) hAccounts).mp
                      hsrcInkPos
                  have hsrcArtNegS :
                      UInt256.sgt (forkDartWord I) ⟨0⟩ = ⟨0⟩ ∨
                        UInt256.gt (forkSrcArtNew σ_solm I)
                          (solcSlotWord (forkAfterSrcInk σ_solm I) I (forkSrcArtSlot I)) = ⟨0⟩ :=
                    (forkSrcArtSubGuardNeg_iff_of_accountMapEquiv (I := I) hAccounts).mp
                      hsrcArtNeg
                  have hsrcArtPosS :
                      UInt256.slt (forkDartWord I) ⟨0⟩ = ⟨0⟩ ∨
                        UInt256.lt (forkSrcArtNew σ_solm I)
                          (solcSlotWord (forkAfterSrcInk σ_solm I) I (forkSrcArtSlot I)) = ⟨0⟩ :=
                    (forkSrcArtSubGuardPos_iff_of_accountMapEquiv (I := I) hAccounts).mp
                      hsrcArtPos
                  have hdstInkNegS :
                      UInt256.slt (forkDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
                        UInt256.gt (forkDstInkNew σ_solm I)
                          (solcSlotWord (forkAfterSrcArt σ_solm I) I (forkDstInkSlot I)) = ⟨0⟩ :=
                    (forkDstInkAddGuardNeg_iff_of_accountMapEquiv (I := I) hAccounts).mp
                      hdstInkNeg
                  have hdstInkPosS :
                      UInt256.sgt (forkDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
                        UInt256.lt (forkDstInkNew σ_solm I)
                          (solcSlotWord (forkAfterSrcArt σ_solm I) I (forkDstInkSlot I)) = ⟨0⟩ :=
                    (forkDstInkAddGuardPos_iff_of_accountMapEquiv (I := I) hAccounts).mp
                      hdstInkPos
                  have hdstArtNegFailS :
                      ¬ (UInt256.slt (forkDartWord I) ⟨0⟩ = ⟨0⟩ ∨
                        UInt256.gt (forkDstArtNew σ_solm I)
                          (solcSlotWord (forkAfterDstInk σ_solm I) I (forkDstArtSlot I)) = ⟨0⟩) := by
                    intro hs
                    exact hdstArtNeg ((forkDstArtAddGuardNeg_iff_of_accountMapEquiv
                      (I := I) hAccounts).mpr hs)
                  have hloadSrcInk :
                      Solm.EVM.storageLoad
                        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
                        (forkSrcInkSlot I) =
                      solcSlotWord σ_solm I (forkSrcInkSlot I) := by
                    simp [initState, Solm.EVM.storageLoad, solcSlotWord, State.lookupAccount,
                      Account.lookupStorage]
                  have hloadSrcArt :
                      Solm.EVM.storageLoad
                        (Solm.EVM.storageStore
                          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
                          (forkSrcInkSlot I) (forkSrcInkNew σ_solm I))
                        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
                        (forkSrcArtSlot I) =
                      solcSlotWord (forkAfterSrcInk σ_solm I) I (forkSrcArtSlot I) := by
                    simp [initState, Solm.EVM.storageLoad, solcSlotWord, State.lookupAccount,
                      Account.lookupStorage, storageStore_accountMap, forkAfterSrcInk]
                  have hloadDstInk :
                      Solm.EVM.storageLoad
                        (Solm.EVM.storageStore
                          (Solm.EVM.storageStore
                            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
                            (forkSrcInkSlot I) (forkSrcInkNew σ_solm I))
                          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
                          (forkSrcArtSlot I) (forkSrcArtNew σ_solm I))
                        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
                        (forkDstInkSlot I) =
                      solcSlotWord (forkAfterSrcArt σ_solm I) I (forkDstInkSlot I) := by
                    simp [initState, Solm.EVM.storageLoad, solcSlotWord, State.lookupAccount,
                      Account.lookupStorage, storageStore_accountMap, forkAfterSrcInk, forkAfterSrcArt]
                  have hloadDstArt :
                      Solm.EVM.storageLoad
                        (Solm.EVM.storageStore
                          (Solm.EVM.storageStore
                            (Solm.EVM.storageStore
                              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
                              (forkSrcInkSlot I) (forkSrcInkNew σ_solm I))
                            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
                            (forkSrcArtSlot I) (forkSrcArtNew σ_solm I))
                          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
                          (forkDstInkSlot I) (forkDstInkNew σ_solm I))
                        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
                        (forkDstArtSlot I) =
                      solcSlotWord (forkAfterDstInk σ_solm I) I (forkDstArtSlot I) := by
                    simp [initState, Solm.EVM.storageLoad, solcSlotWord, State.lookupAccount,
                      Account.lookupStorage, storageStore_accountMap, forkAfterSrcInk,
                      forkAfterSrcArt, forkAfterDstInk]
                  have hbody := execForkSourceRevertDstArtGuardNeg
                    (evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) (I := I)
                    (solcSlotWord σ_solm I (forkSrcInkSlot I)) (forkSrcInkNew σ_solm I)
                    (solcSlotWord (forkAfterSrcInk σ_solm I) I (forkSrcArtSlot I))
                    (forkSrcArtNew σ_solm I)
                    (solcSlotWord (forkAfterSrcArt σ_solm I) I (forkDstInkSlot I))
                    (forkDstInkNew σ_solm I)
                    (solcSlotWord (forkAfterDstInk σ_solm I) I (forkDstArtSlot I))
                    (forkDstArtNew σ_solm I)
                    (by simpa [initState] using hwv) hsz164 hloadSrcInk rfl
                    (forkDinkSubGuardNegCond hsrcInkNegS)
                    (forkDinkSubGuardPosCond hsrcInkPosS)
                    hloadSrcArt rfl
                    (forkDartSubGuardNegCond hsrcArtNegS)
                    (forkDartSubGuardPosCond hsrcArtPosS)
                    hloadDstInk rfl
                    (forkDinkAddGuardNegCond hdstInkNegS)
                    (forkDinkAddGuardPosCond hdstInkPosS)
                    hloadDstArt rfl hdstArtNegFailS
                  obtain ⟨_, _, h4792⟩ := RD.vatForkSrcInkSubSuccess
                    (h := hdecoded) solcFreePtrMem_size hsz164
                    (by simpa [forkSrcInkNew] using hsrcInkNeg)
                    (by simpa [forkSrcInkNew] using hsrcInkPos)
                  obtain ⟨_, _, h4809⟩ := RD.vatForkSrcArtSubSuccess
                    (h := by simpa [forkSrcInkNew] using h4792) hperm
                    (by simpa [forkSrcArtNew, forkAfterSrcInk] using hsrcArtNeg)
                    (by simpa [forkSrcArtNew, forkAfterSrcInk] using hsrcArtPos)
                  obtain ⟨_, _, h4826⟩ := RD.vatForkDstInkAddSuccess
                    (h := by simpa [forkSrcArtNew, forkAfterSrcInk] using h4809) hperm
                    (by simpa [forkDstInkNew, forkAfterSrcArt] using hdstInkNeg)
                    (by simpa [forkDstInkNew, forkAfterSrcArt] using hdstInkPos)
                  have hrev := RD.vatForkDstArtAddRevert
                    (h := by simpa [forkDstInkNew, forkAfterSrcArt] using h4826) hperm
                    (Or.inl (by simpa [forkDstArtNew, forkAfterDstInk] using hdstArtNeg))
                  exact hrev.reEquivExecutionRevert hcode (vatDispatchFork hsel) hdecode hbody
              · have hsrcInkNegS :
                    UInt256.sgt (forkDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
                      UInt256.gt (forkSrcInkNew σ_solm I)
                        (solcSlotWord σ_solm I (forkSrcInkSlot I)) = ⟨0⟩ :=
                  (forkSrcInkSubGuardNeg_iff_of_accountMapEquiv (I := I) hAccounts).mp
                    hsrcInkNeg
                have hsrcInkPosS :
                    UInt256.slt (forkDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
                      UInt256.lt (forkSrcInkNew σ_solm I)
                        (solcSlotWord σ_solm I (forkSrcInkSlot I)) = ⟨0⟩ :=
                  (forkSrcInkSubGuardPos_iff_of_accountMapEquiv (I := I) hAccounts).mp
                    hsrcInkPos
                have hsrcArtNegS :
                    UInt256.sgt (forkDartWord I) ⟨0⟩ = ⟨0⟩ ∨
                      UInt256.gt (forkSrcArtNew σ_solm I)
                        (solcSlotWord (forkAfterSrcInk σ_solm I) I (forkSrcArtSlot I)) = ⟨0⟩ :=
                  (forkSrcArtSubGuardNeg_iff_of_accountMapEquiv (I := I) hAccounts).mp
                    hsrcArtNeg
                have hsrcArtPosS :
                    UInt256.slt (forkDartWord I) ⟨0⟩ = ⟨0⟩ ∨
                      UInt256.lt (forkSrcArtNew σ_solm I)
                        (solcSlotWord (forkAfterSrcInk σ_solm I) I (forkSrcArtSlot I)) = ⟨0⟩ :=
                  (forkSrcArtSubGuardPos_iff_of_accountMapEquiv (I := I) hAccounts).mp
                    hsrcArtPos
                have hdstInkNegS :
                    UInt256.slt (forkDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
                      UInt256.gt (forkDstInkNew σ_solm I)
                        (solcSlotWord (forkAfterSrcArt σ_solm I) I (forkDstInkSlot I)) = ⟨0⟩ :=
                  (forkDstInkAddGuardNeg_iff_of_accountMapEquiv (I := I) hAccounts).mp
                    hdstInkNeg
                have hdstInkPosFailS :
                    ¬ (UInt256.sgt (forkDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
                      UInt256.lt (forkDstInkNew σ_solm I)
                        (solcSlotWord (forkAfterSrcArt σ_solm I) I (forkDstInkSlot I)) = ⟨0⟩) := by
                  intro hs
                  exact hdstInkPos ((forkDstInkAddGuardPos_iff_of_accountMapEquiv
                    (I := I) hAccounts).mpr hs)
                have hloadSrcInk :
                    Solm.EVM.storageLoad
                      (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                      (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
                      (forkSrcInkSlot I) =
                    solcSlotWord σ_solm I (forkSrcInkSlot I) := by
                  simp [initState, Solm.EVM.storageLoad, solcSlotWord, State.lookupAccount,
                    Account.lookupStorage]
                have hloadSrcArt :
                    Solm.EVM.storageLoad
                      (Solm.EVM.storageStore
                        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
                        (forkSrcInkSlot I) (forkSrcInkNew σ_solm I))
                      (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
                      (forkSrcArtSlot I) =
                    solcSlotWord (forkAfterSrcInk σ_solm I) I (forkSrcArtSlot I) := by
                  simp [initState, Solm.EVM.storageLoad, solcSlotWord, State.lookupAccount,
                    Account.lookupStorage, storageStore_accountMap, forkAfterSrcInk]
                have hloadDstInk :
                    Solm.EVM.storageLoad
                      (Solm.EVM.storageStore
                        (Solm.EVM.storageStore
                          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
                          (forkSrcInkSlot I) (forkSrcInkNew σ_solm I))
                        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
                        (forkSrcArtSlot I) (forkSrcArtNew σ_solm I))
                      (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
                      (forkDstInkSlot I) =
                    solcSlotWord (forkAfterSrcArt σ_solm I) I (forkDstInkSlot I) := by
                  simp [initState, Solm.EVM.storageLoad, solcSlotWord, State.lookupAccount,
                    Account.lookupStorage, storageStore_accountMap, forkAfterSrcInk, forkAfterSrcArt]
                have hbody := execForkSourceRevertDstInkGuardPos
                  (evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) (I := I)
                  (solcSlotWord σ_solm I (forkSrcInkSlot I)) (forkSrcInkNew σ_solm I)
                  (solcSlotWord (forkAfterSrcInk σ_solm I) I (forkSrcArtSlot I))
                  (forkSrcArtNew σ_solm I)
                  (solcSlotWord (forkAfterSrcArt σ_solm I) I (forkDstInkSlot I))
                  (forkDstInkNew σ_solm I)
                  (by simpa [initState] using hwv) hsz164 hloadSrcInk rfl
                  (forkDinkSubGuardNegCond hsrcInkNegS)
                  (forkDinkSubGuardPosCond hsrcInkPosS)
                  hloadSrcArt rfl
                  (forkDartSubGuardNegCond hsrcArtNegS)
                  (forkDartSubGuardPosCond hsrcArtPosS)
                  hloadDstInk rfl hdstInkNegS hdstInkPosFailS
                obtain ⟨_, _, h4792⟩ := RD.vatForkSrcInkSubSuccess
                  (h := hdecoded) solcFreePtrMem_size hsz164
                  (by simpa [forkSrcInkNew] using hsrcInkNeg)
                  (by simpa [forkSrcInkNew] using hsrcInkPos)
                obtain ⟨_, _, h4809⟩ := RD.vatForkSrcArtSubSuccess
                  (h := by simpa [forkSrcInkNew] using h4792) hperm
                  (by simpa [forkSrcArtNew, forkAfterSrcInk] using hsrcArtNeg)
                  (by simpa [forkSrcArtNew, forkAfterSrcInk] using hsrcArtPos)
                have hrev := RD.vatForkDstInkAddRevert
                  (h := by simpa [forkSrcArtNew, forkAfterSrcInk] using h4809) hperm
                  (Or.inr ⟨by simpa [forkDstInkNew, forkAfterSrcArt] using hdstInkNeg,
                    by simpa [forkDstInkNew, forkAfterSrcArt] using hdstInkPos⟩)
                exact hrev.reEquivExecutionRevert hcode (vatDispatchFork hsel) hdecode hbody
            · have hsrcInkNegS :
                  UInt256.sgt (forkDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
                    UInt256.gt (forkSrcInkNew σ_solm I)
                      (solcSlotWord σ_solm I (forkSrcInkSlot I)) = ⟨0⟩ :=
                (forkSrcInkSubGuardNeg_iff_of_accountMapEquiv (I := I) hAccounts).mp
                  hsrcInkNeg
              have hsrcInkPosS :
                  UInt256.slt (forkDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
                    UInt256.lt (forkSrcInkNew σ_solm I)
                      (solcSlotWord σ_solm I (forkSrcInkSlot I)) = ⟨0⟩ :=
                (forkSrcInkSubGuardPos_iff_of_accountMapEquiv (I := I) hAccounts).mp
                  hsrcInkPos
              have hsrcArtNegS :
                  UInt256.sgt (forkDartWord I) ⟨0⟩ = ⟨0⟩ ∨
                    UInt256.gt (forkSrcArtNew σ_solm I)
                      (solcSlotWord (forkAfterSrcInk σ_solm I) I (forkSrcArtSlot I)) = ⟨0⟩ :=
                (forkSrcArtSubGuardNeg_iff_of_accountMapEquiv (I := I) hAccounts).mp
                  hsrcArtNeg
              have hsrcArtPosS :
                  UInt256.slt (forkDartWord I) ⟨0⟩ = ⟨0⟩ ∨
                    UInt256.lt (forkSrcArtNew σ_solm I)
                      (solcSlotWord (forkAfterSrcInk σ_solm I) I (forkSrcArtSlot I)) = ⟨0⟩ :=
                (forkSrcArtSubGuardPos_iff_of_accountMapEquiv (I := I) hAccounts).mp
                  hsrcArtPos
              have hdstInkNegFailS :
                  ¬ (UInt256.slt (forkDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
                    UInt256.gt (forkDstInkNew σ_solm I)
                      (solcSlotWord (forkAfterSrcArt σ_solm I) I (forkDstInkSlot I)) = ⟨0⟩) := by
                intro hs
                exact hdstInkNeg ((forkDstInkAddGuardNeg_iff_of_accountMapEquiv
                  (I := I) hAccounts).mpr hs)
              have hloadSrcInk :
                  Solm.EVM.storageLoad
                    (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                    (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
                    (forkSrcInkSlot I) =
                  solcSlotWord σ_solm I (forkSrcInkSlot I) := by
                simp [initState, Solm.EVM.storageLoad, solcSlotWord, State.lookupAccount,
                  Account.lookupStorage]
              have hloadSrcArt :
                  Solm.EVM.storageLoad
                    (Solm.EVM.storageStore
                      (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                      (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
                      (forkSrcInkSlot I) (forkSrcInkNew σ_solm I))
                    (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
                    (forkSrcArtSlot I) =
                  solcSlotWord (forkAfterSrcInk σ_solm I) I (forkSrcArtSlot I) := by
                simp [initState, Solm.EVM.storageLoad, solcSlotWord, State.lookupAccount,
                  Account.lookupStorage, storageStore_accountMap, storageStore_executionEnv,
                  forkAfterSrcInk]
              have hloadDstInk :
                  Solm.EVM.storageLoad
                    (Solm.EVM.storageStore
                      (Solm.EVM.storageStore
                        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
                        (forkSrcInkSlot I) (forkSrcInkNew σ_solm I))
                      (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
                      (forkSrcArtSlot I) (forkSrcArtNew σ_solm I))
                    (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
                    (forkDstInkSlot I) =
                  solcSlotWord (forkAfterSrcArt σ_solm I) I (forkDstInkSlot I) := by
                simp [initState, Solm.EVM.storageLoad, solcSlotWord, State.lookupAccount,
                  Account.lookupStorage, storageStore_accountMap, storageStore_executionEnv,
                  forkAfterSrcInk, forkAfterSrcArt]
              have hbody := execForkSourceRevertDstInkGuardNeg
                (evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) (I := I)
                (solcSlotWord σ_solm I (forkSrcInkSlot I)) (forkSrcInkNew σ_solm I)
                (solcSlotWord (forkAfterSrcInk σ_solm I) I (forkSrcArtSlot I))
                (forkSrcArtNew σ_solm I)
                (solcSlotWord (forkAfterSrcArt σ_solm I) I (forkDstInkSlot I))
                (forkDstInkNew σ_solm I)
                (by simpa [initState] using hwv) hsz164 hloadSrcInk rfl
                (forkDinkSubGuardNegCond hsrcInkNegS)
                (forkDinkSubGuardPosCond hsrcInkPosS)
                hloadSrcArt rfl
                (forkDartSubGuardNegCond hsrcArtNegS)
                (forkDartSubGuardPosCond hsrcArtPosS)
                hloadDstInk rfl hdstInkNegFailS
              obtain ⟨_, _, h4792⟩ := RD.vatForkSrcInkSubSuccess
                (h := hdecoded) solcFreePtrMem_size hsz164
                (by simpa [forkSrcInkNew] using hsrcInkNeg)
                (by simpa [forkSrcInkNew] using hsrcInkPos)
              obtain ⟨_, _, h4809⟩ := RD.vatForkSrcArtSubSuccess
                (h := by simpa [forkSrcInkNew] using h4792) hperm
                (by simpa [forkSrcArtNew, forkAfterSrcInk] using hsrcArtNeg)
                (by simpa [forkSrcArtNew, forkAfterSrcInk] using hsrcArtPos)
              have hrev := RD.vatForkDstInkAddRevert
                (h := by simpa [forkSrcArtNew, forkAfterSrcInk] using h4809) hperm
                (Or.inl (by simpa [forkDstInkNew, forkAfterSrcArt] using hdstInkNeg))
              exact hrev.reEquivExecutionRevert hcode (vatDispatchFork hsel) hdecode hbody
          · have hsrcInkNegS :
                UInt256.sgt (forkDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
                  UInt256.gt (forkSrcInkNew σ_solm I)
                    (solcSlotWord σ_solm I (forkSrcInkSlot I)) = ⟨0⟩ :=
              (forkSrcInkSubGuardNeg_iff_of_accountMapEquiv (I := I) hAccounts).mp
                hsrcInkNeg
            have hsrcInkPosS :
                UInt256.slt (forkDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
                  UInt256.lt (forkSrcInkNew σ_solm I)
                    (solcSlotWord σ_solm I (forkSrcInkSlot I)) = ⟨0⟩ :=
              (forkSrcInkSubGuardPos_iff_of_accountMapEquiv (I := I) hAccounts).mp
                hsrcInkPos
            have hsrcArtNegS :
                UInt256.sgt (forkDartWord I) ⟨0⟩ = ⟨0⟩ ∨
                  UInt256.gt (forkSrcArtNew σ_solm I)
                    (solcSlotWord (forkAfterSrcInk σ_solm I) I (forkSrcArtSlot I)) = ⟨0⟩ :=
              (forkSrcArtSubGuardNeg_iff_of_accountMapEquiv (I := I) hAccounts).mp
                hsrcArtNeg
            have hsrcArtPosFailS :
                ¬ (UInt256.slt (forkDartWord I) ⟨0⟩ = ⟨0⟩ ∨
                  UInt256.lt (forkSrcArtNew σ_solm I)
                    (solcSlotWord (forkAfterSrcInk σ_solm I) I (forkSrcArtSlot I)) = ⟨0⟩) := by
              intro hs
              exact hsrcArtPos ((forkSrcArtSubGuardPos_iff_of_accountMapEquiv
                (I := I) hAccounts).mpr hs)
            have hloadSrcInk :
                Solm.EVM.storageLoad
                  (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                  (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
                  (forkSrcInkSlot I) =
                solcSlotWord σ_solm I (forkSrcInkSlot I) := by
              simp [initState, Solm.EVM.storageLoad, solcSlotWord, State.lookupAccount,
                Account.lookupStorage]
            have hloadSrcArt :
                Solm.EVM.storageLoad
                  (Solm.EVM.storageStore
                    (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                    (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
                    (forkSrcInkSlot I) (forkSrcInkNew σ_solm I))
                  (Solm.EVM.storageStore
                    (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                    (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
                    (forkSrcInkSlot I) (forkSrcInkNew σ_solm I)).executionEnv.codeOwner
                  (forkSrcArtSlot I) =
                solcSlotWord (forkAfterSrcInk σ_solm I) I (forkSrcArtSlot I) := by
              simp [initState, Solm.EVM.storageLoad, solcSlotWord, State.lookupAccount,
                Account.lookupStorage, storageStore_accountMap, storageStore_executionEnv,
                forkAfterSrcInk]
            have hbody := execForkSourceRevertSrcArtGuardPos
              (evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) (I := I)
              (solcSlotWord σ_solm I (forkSrcInkSlot I)) (forkSrcInkNew σ_solm I)
              (solcSlotWord (forkAfterSrcInk σ_solm I) I (forkSrcArtSlot I))
              (forkSrcArtNew σ_solm I)
              (by simpa [initState] using hwv) hsz164 hloadSrcInk rfl
              (forkDinkSubGuardNegCond hsrcInkNegS)
              (forkDinkSubGuardPosCond hsrcInkPosS)
              hloadSrcArt rfl hsrcArtNegS hsrcArtPosFailS
            obtain ⟨_, _, h4792⟩ := RD.vatForkSrcInkSubSuccess
              (h := hdecoded) solcFreePtrMem_size hsz164
              (by simpa [forkSrcInkNew] using hsrcInkNeg)
              (by simpa [forkSrcInkNew] using hsrcInkPos)
            have hrev := RD.vatForkSrcArtSubRevert
              (h := by simpa [forkSrcInkNew] using h4792) hperm
              (Or.inr ⟨by simpa [forkSrcArtNew, forkAfterSrcInk] using hsrcArtNeg,
                by simpa [forkSrcArtNew, forkAfterSrcInk] using hsrcArtPos⟩)
            exact hrev.reEquivExecutionRevert hcode (vatDispatchFork hsel) hdecode hbody
        · have hsrcInkNegS :
              UInt256.sgt (forkDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
                UInt256.gt (forkSrcInkNew σ_solm I)
                  (solcSlotWord σ_solm I (forkSrcInkSlot I)) = ⟨0⟩ :=
            (forkSrcInkSubGuardNeg_iff_of_accountMapEquiv (I := I) hAccounts).mp
              hsrcInkNeg
          have hsrcInkPosS :
              UInt256.slt (forkDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
                UInt256.lt (forkSrcInkNew σ_solm I)
                  (solcSlotWord σ_solm I (forkSrcInkSlot I)) = ⟨0⟩ :=
            (forkSrcInkSubGuardPos_iff_of_accountMapEquiv (I := I) hAccounts).mp
              hsrcInkPos
          have hsrcArtNegFailS :
              ¬ (UInt256.sgt (forkDartWord I) ⟨0⟩ = ⟨0⟩ ∨
                UInt256.gt (forkSrcArtNew σ_solm I)
                  (solcSlotWord (forkAfterSrcInk σ_solm I) I (forkSrcArtSlot I)) = ⟨0⟩) := by
            intro hs
            exact hsrcArtNeg ((forkSrcArtSubGuardNeg_iff_of_accountMapEquiv
              (I := I) hAccounts).mpr hs)
          have hloadSrcInk :
              Solm.EVM.storageLoad
                (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
                (forkSrcInkSlot I) =
              solcSlotWord σ_solm I (forkSrcInkSlot I) := by
            simp [initState, Solm.EVM.storageLoad, solcSlotWord, State.lookupAccount,
              Account.lookupStorage]
          have hloadSrcArt :
              Solm.EVM.storageLoad
                (Solm.EVM.storageStore
                  (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                  (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
                  (forkSrcInkSlot I) (forkSrcInkNew σ_solm I))
                (Solm.EVM.storageStore
                  (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                  (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
                  (forkSrcInkSlot I) (forkSrcInkNew σ_solm I)).executionEnv.codeOwner
                (forkSrcArtSlot I) =
              solcSlotWord (forkAfterSrcInk σ_solm I) I (forkSrcArtSlot I) := by
            simp [initState, Solm.EVM.storageLoad, solcSlotWord, State.lookupAccount,
              Account.lookupStorage, storageStore_accountMap, storageStore_executionEnv,
              forkAfterSrcInk]
          have hbody := execForkSourceRevertSrcArtGuardNeg
            (evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) (I := I)
            (solcSlotWord σ_solm I (forkSrcInkSlot I)) (forkSrcInkNew σ_solm I)
            (solcSlotWord (forkAfterSrcInk σ_solm I) I (forkSrcArtSlot I))
            (forkSrcArtNew σ_solm I)
            (by simpa [initState] using hwv) hsz164 hloadSrcInk rfl
            (forkDinkSubGuardNegCond hsrcInkNegS)
            (forkDinkSubGuardPosCond hsrcInkPosS)
            hloadSrcArt rfl hsrcArtNegFailS
          obtain ⟨_, _, h4792⟩ := RD.vatForkSrcInkSubSuccess
            (h := hdecoded) solcFreePtrMem_size hsz164
            (by simpa [forkSrcInkNew] using hsrcInkNeg)
            (by simpa [forkSrcInkNew] using hsrcInkPos)
          have hrev := RD.vatForkSrcArtSubRevert
            (h := by simpa [forkSrcInkNew] using h4792) hperm
            (Or.inl (by simpa [forkSrcArtNew, forkAfterSrcInk] using hsrcArtNeg))
          exact hrev.reEquivExecutionRevert hcode (vatDispatchFork hsel) hdecode hbody
      · have hsrcInkNegS :
            UInt256.sgt (forkDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
              UInt256.gt (forkSrcInkNew σ_solm I)
                (solcSlotWord σ_solm I (forkSrcInkSlot I)) = ⟨0⟩ :=
          (forkSrcInkSubGuardNeg_iff_of_accountMapEquiv (I := I) hAccounts).mp
            hsrcInkNeg
        have hsrcInkPosFailS :
            ¬ (UInt256.slt (forkDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
              UInt256.lt (forkSrcInkNew σ_solm I)
                (solcSlotWord σ_solm I (forkSrcInkSlot I)) = ⟨0⟩) := by
          intro hs
          exact hsrcInkPos ((forkSrcInkSubGuardPos_iff_of_accountMapEquiv
            (I := I) hAccounts).mpr hs)
        have hloadSrcInk :
            Solm.EVM.storageLoad
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
              (forkSrcInkSlot I) =
            solcSlotWord σ_solm I (forkSrcInkSlot I) := by
          simp [initState, Solm.EVM.storageLoad, solcSlotWord, State.lookupAccount,
            Account.lookupStorage]
        have hbody := execForkSourceRevertSrcInkGuardPos
          (evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) (I := I)
          (solcSlotWord σ_solm I (forkSrcInkSlot I)) (forkSrcInkNew σ_solm I)
          (by simpa [initState] using hwv) hsz164 hloadSrcInk rfl
          hsrcInkNegS hsrcInkPosFailS
        have hrev := RD.vatForkSrcInkSubRevert
          (h := hdecoded) solcFreePtrMem_size hsz164
          (Or.inr ⟨by simpa [forkSrcInkNew] using hsrcInkNeg,
            by simpa [forkSrcInkNew] using hsrcInkPos⟩)
        exact hrev.reEquivExecutionRevert hcode (vatDispatchFork hsel) hdecode hbody
    · have hsrcInkNegFailS :
          ¬ (UInt256.sgt (forkDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
            UInt256.gt (forkSrcInkNew σ_solm I)
              (solcSlotWord σ_solm I (forkSrcInkSlot I)) = ⟨0⟩) := by
        intro hs
        exact hsrcInkNeg ((forkSrcInkSubGuardNeg_iff_of_accountMapEquiv
          (I := I) hAccounts).mpr hs)
      have hloadSrcInk :
          Solm.EVM.storageLoad
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
            (forkSrcInkSlot I) =
          solcSlotWord σ_solm I (forkSrcInkSlot I) := by
        simp [initState, Solm.EVM.storageLoad, solcSlotWord, State.lookupAccount,
          Account.lookupStorage]
      have hbody := execForkSourceRevertSrcInkGuardNeg
        (evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) (I := I)
        (solcSlotWord σ_solm I (forkSrcInkSlot I)) (forkSrcInkNew σ_solm I)
        (by simpa [initState] using hwv) hsz164 hloadSrcInk rfl
        hsrcInkNegFailS
      have hrev := RD.vatForkSrcInkSubRevert
        (h := hdecoded) solcFreePtrMem_size hsz164
        (Or.inl (by simpa [forkSrcInkNew] using hsrcInkNeg))
      exact hrev.reEquivExecutionRevert hcode (vatDispatchFork hsel) hdecode hbody
  · have hshort : I.calldata.size < 164 := by omega
    exact vatForkBodyCoreDecodeFailed_short hcode hsize hsz4 hshort hsel hreach

end Benchmarks.Dss.Vat
