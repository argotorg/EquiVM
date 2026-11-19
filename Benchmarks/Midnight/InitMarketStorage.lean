import Benchmarks.Midnight.PackedUint16
import Benchmarks.Midnight.PackedByte
import Benchmarks.Midnight.PackedFee
import Benchmarks.Midnight.SettlementFields

/-! Ordered packed storage updates used when a market is first initialized. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

def initMarketTick (evm : EVM.State) (id : UInt256) : EVM.State :=
  Stele.EVM.storageStore evm evm.executionEnv.codeOwner (solcMappingSlot ⟨1⟩ id + ⟨2⟩)
    (setUint8Offset18Word (marketFeeWord evm id) ⟨4⟩)

def storeSettlementFee (evm : EVM.State) (id : UInt256) (i : Fin 7)
    (value : UInt256) : EVM.State :=
  Stele.EVM.storageStore evm evm.executionEnv.codeOwner (solcMappingSlot ⟨1⟩ id + ⟨2⟩)
    (setUint16Word (marketFeeWord evm id) value ⟨i.val, by omega⟩)

def storeSettlementFeeAccounts (σ : AccountMap) (I : ExecutionEnv) (id : UInt256)
    (i : Fin 7) (value : UInt256) : AccountMap :=
  sstoreAccountMap I.codeOwner σ (solcMappingSlot ⟨1⟩ id + ⟨2⟩)
    (setUint16Word (solcSlotWordAt (solcMappingSlot ⟨1⟩ id + ⟨2⟩) σ I) value ⟨i.val, by omega⟩)

theorem accountStorageWord_fold (σ : AccountMap) (I : ExecutionEnv) (slot : UInt256) :
    ((σ.get? I.codeOwner).option (⟨0⟩ : UInt256) (fun ac ↦ ac.storage.getD slot ⟨0⟩)) =
      solcSlotWordAt slot σ I := rfl

theorem storeSettlementFee_solc (σ : AccountMap) (I : ExecutionEnv) (id value : UInt256)
    (i : Fin 7) (hvalue : value.toNat < 2^16) :
    sstoreAccountMap I.codeOwner σ (solcMappingSlot ⟨1⟩ id + ⟨2⟩)
      (UInt256.lor
        (UInt256.land (UInt256.ofNat (65535 * 2 ^ (16 * i.val)))
          (UInt256.shiftLeft value (UInt256.ofNat (16 * i.val))))
        (UInt256.land (UInt256.lnot (UInt256.ofNat (65535 * 2 ^ (16 * i.val))))
          (solcSlotWordAt (solcMappingSlot ⟨1⟩ id + ⟨2⟩) σ I))) =
      storeSettlementFeeAccounts σ I id i value := by
  have hm : UInt256.ofNat (65535 * 2 ^ (16 * i.val)) =
      UInt256.shiftLeft ⟨65535⟩ (UInt256.ofNat (16 * i.val)) := by
    clear * - i
    revert i
    decide
  rw [hm, setUint16Word_solc _ value i hvalue]
  rfl

@[simp] theorem initMarketTick_env (evm : EVM.State) (id : UInt256) :
    (initMarketTick evm id).executionEnv = evm.executionEnv := storageStore_executionEnv ..

@[simp] theorem storeSettlementFee_env (evm : EVM.State) (id : UInt256) (i : Fin 7)
    (value : UInt256) :
    (storeSettlementFee evm id i value).executionEnv = evm.executionEnv := storageStore_executionEnv ..

@[simp] theorem storeSettlementFee_accounts (evm : EVM.State) (id : UInt256) (i : Fin 7)
    (value : UInt256) :
    (storeSettlementFee evm id i value).accountMap =
      storeSettlementFeeAccounts evm.accountMap evm.executionEnv id i value := by
  rw [storeSettlementFee, storageStore_accountMap]
  rw [marketFeeWord, storageLoad_codeOwner_eq_solcSlotWordAt evm evm.executionEnv _ rfl]
  rfl

theorem settlementFeeField_store (evm : EVM.State) (id value : UInt256) (i : Fin 7) :
    storageLocStore evm (settlementFeeFieldLoc id i) (.int value.toNat) =
      some (storeSettlementFee evm id i value) := by
  simpa only [settlementFeeFieldLoc, uint16Loc, storeSettlementFee, marketFeeWord,
    packedUInt16Int, Int.ofNat_eq_natCast] using
    storageLocStore_uint16_word evm (solcMappingSlot ⟨1⟩ id + ⟨2⟩) value ⟨i.val, by omega⟩

theorem assignSettlementFee {frame : Frame} {evm : EVM.State} {id : UInt256}
    (i : Fin 7) (value : UInt256)
    (hget : frame.locals.get? "_marketState" =
      some (.storageRef (marketStateRef id) marketStateType)) :
    assignStorageRef? config frame evm .storage { base := "_marketState", steps :=
      [.field ("settlementFeeCbp" ++ toString i.val)] } (.int value.toNat) =
      .ok (frame, storeSettlementFee evm id i value) :=
  assignStorageAliasField hget (settlementFeeField_type i) rfl
    (settlementFeeField_layout id i) (settlementFeeField_store evm id value i)

theorem wordLandAssoc (a b c : UInt256) :
    UInt256.land (UInt256.land a b) c = UInt256.land a (UInt256.land b c) := by
  apply u256_inj
  simp only [uland_toNat, Nat.land_assoc]

theorem wordLandOr (a b c : UInt256) :
    UInt256.land (UInt256.lor a b) c =
      UInt256.lor (UInt256.land a c) (UInt256.land b c) := by
  apply u256_inj
  simp only [uland_toNat, u256_lor_toNat_exact]
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_and, Nat.testBit_or]
  cases a.toNat.testBit i <;> cases b.toNat.testBit i <;> cases c.toNat.testBit i <;> rfl

theorem wordOrAssoc (a b c : UInt256) :
    UInt256.lor (UInt256.lor a b) c = UInt256.lor a (UInt256.lor b c) := by
  apply u256_inj
  simp only [u256_lor_toNat_exact, Nat.lor_assoc]

theorem wordShiftLeftZero (a : UInt256) : UInt256.shiftLeft a (UInt256.ofNat 0) = a := by
  unfold UInt256.shiftLeft
  rw [if_neg (show ¬ (UInt256.ofNat 0).val ≥ 256 from by decide)]
  apply u256_inj
  change (a.toNat <<< 0) % UInt256.size = a.toNat
  rw [Nat.shiftLeft_zero]
  exact Nat.mod_eq_of_lt a.val.isLt

theorem setUint16Pair (old first second : UInt256) (hsecond : second.toNat < 2^16) :
    UInt256.lor (UInt256.land ⟨4294901760⟩ (UInt256.shiftLeft second ⟨16⟩))
      (UInt256.lor (UInt256.land first ⟨65535⟩) (UInt256.land old (UInt256.lnot ⟨4294967295⟩))) =
      setUint16Word (setUint16Word old first 0) second 1 := by
  rw [setUint16Word_clean _ second 1 hsecond]
  simp only [setUint16Word, show 16 * (0 : Fin 16).val = 0 from rfl,
    show 16 * (1 : Fin 16).val = 16 from rfl, wordShiftLeftZero]
  rw [wordLandOr, wordLandAssoc, wordLandAssoc]
  have hm : UInt256.land (UInt256.lnot ⟨65535⟩)
      (UInt256.lnot (UInt256.shiftLeft ⟨65535⟩ (UInt256.ofNat 16))) =
        UInt256.lnot ⟨4294967295⟩ := by decide
  have hv : UInt256.land ⟨65535⟩
      (UInt256.lnot (UInt256.shiftLeft ⟨65535⟩ (UInt256.ofNat 16))) = ⟨65535⟩ := by decide
  have hs : UInt256.land ⟨4294901760⟩ (UInt256.shiftLeft second ⟨16⟩) =
      UInt256.shiftLeft second ⟨16⟩ := by
    rw [u256_land_comm]
    exact shiftLeft_land_mask second 16 16 (by decide) (by decide) hsecond
  rw [hm, hv, hs, u256_lor_comm (UInt256.land old _), u256_lor_comm _ (UInt256.shiftLeft second _)]
  rfl

theorem storeSettlementFee_pair (σ : AccountMap) (I : ExecutionEnv) (id first second : UInt256)
    (hsecond : second.toNat < 2^16) :
    sstoreAccountMap I.codeOwner σ (solcMappingSlot ⟨1⟩ id + ⟨2⟩)
      (UInt256.lor (UInt256.land ⟨4294901760⟩ (UInt256.shiftLeft second ⟨16⟩))
        (UInt256.lor (UInt256.land first ⟨65535⟩)
          (UInt256.land (solcSlotWordAt (solcMappingSlot ⟨1⟩ id + ⟨2⟩) σ I)
            (UInt256.lnot ⟨4294967295⟩)))) =
      storeSettlementFeeAccounts (storeSettlementFeeAccounts σ I id 0 first) I id 1 second := by
  rw [setUint16Pair _ first second hsecond]
  cases ha : σ.get? I.codeOwner with
  | none => simp only [storeSettlementFeeAccounts, sstoreAccountMap_absent_same ha]
  | some ac =>
    have hl : solcSlotWordAt (solcMappingSlot ⟨1⟩ id + ⟨2⟩)
        (storeSettlementFeeAccounts σ I id 0 first) I =
        setUint16Word (solcSlotWordAt (solcMappingSlot ⟨1⟩ id + ⟨2⟩) σ I) first 0 :=
      sstoreAccountMap_storage_getD_self_present σ I.codeOwner ha _ _
    change _ = sstoreAccountMap I.codeOwner (storeSettlementFeeAccounts σ I id 0 first)
      (solcMappingSlot ⟨1⟩ id + ⟨2⟩)
      (setUint16Word (solcSlotWordAt (solcMappingSlot ⟨1⟩ id + ⟨2⟩)
        (storeSettlementFeeAccounts σ I id 0 first) I) second 1)
    rw [hl]
    unfold storeSettlementFeeAccounts
    exact sstoreAccountMap_self_update ..

def initSettlementState (evm : EVM.State) (id word : UInt256) : Nat → EVM.State
  | 0 => evm
  | n + 1 => storeSettlementFee (initSettlementState evm id word n) id
      ⟨n % 7, Nat.mod_lt _ (by decide)⟩ (settlementFeeWord word n)

def initSettlementAccounts (σ : AccountMap) (I : ExecutionEnv) (id word : UInt256) : Nat → AccountMap
  | 0 => σ
  | n + 1 => storeSettlementFeeAccounts (initSettlementAccounts σ I id word n) I id
      ⟨n % 7, Nat.mod_lt _ (by decide)⟩ (settlementFeeWord word n)

@[simp] theorem initSettlementState_env (evm : EVM.State) (id word : UInt256) (n : Nat) :
    (initSettlementState evm id word n).executionEnv = evm.executionEnv := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [initSettlementState, storeSettlementFee_env, ih]

theorem initSettlementState_accounts (evm : EVM.State) (id word : UInt256) (n : Nat) :
    (initSettlementState evm id word n).accountMap =
      initSettlementAccounts evm.accountMap evm.executionEnv id word n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [initSettlementState, initSettlementAccounts,
      storeSettlementFee_accounts, initSettlementState_env, ih]

def initMarketContinuous (evm : EVM.State) (id : UInt256) (token : AccountAddress) : EVM.State :=
  Stele.EVM.storageStore evm evm.executionEnv.codeOwner (solcMappingSlot ⟨1⟩ id + ⟨2⟩)
    (setUint32Offset14Word (marketFeeWord evm id)
      (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner
        (solcMappingSlot ⟨5⟩ (UInt256.ofNat token.val))))

@[simp] theorem initMarketContinuous_env (evm : EVM.State) (id : UInt256) (token : AccountAddress) :
    (initMarketContinuous evm id token).executionEnv = evm.executionEnv := storageStore_executionEnv ..

end Benchmarks.Midnight
