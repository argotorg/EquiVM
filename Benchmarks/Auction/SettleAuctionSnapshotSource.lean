import Benchmarks.Auction.AuctionGetter
import Benchmarks.Auction.Common

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Auction

def auctionSetBoolOffset20TrueWord (old : UInt256) : UInt256 :=
  UInt256.ofNat (old.toNat % 2 ^ 160 + 2 ^ 160 + old.toNat / 2 ^ 168 * 2 ^ 168)

def auctionSettleAuctionMarkSettledState (evm : EVM.State) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨211⟩
    (auctionSetBoolOffset20TrueWord (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨211⟩))

def auctionSettleAuctionEnterState (evm : EVM.State) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨101⟩ ⟨2⟩

def auctionSettleAuctionExitState (evm : EVM.State) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨101⟩ ⟨1⟩

def auctionSettleAuctionMarkSettledMap (σ : AccountMap) (I : ExecutionEnv) : AccountMap :=
  sstoreAccountMap I.codeOwner σ ⟨211⟩
    (auctionSetBoolOffset20TrueWord (auctionSlotWord ⟨211⟩ σ I))

def auctionSettleAuctionEnterMap (σ : AccountMap) (I : ExecutionEnv) : AccountMap :=
  sstoreAccountMap I.codeOwner σ ⟨101⟩ ⟨2⟩

def auctionSettleAuctionExitMap (σ : AccountMap) (I : ExecutionEnv) : AccountMap :=
  sstoreAccountMap I.codeOwner σ ⟨101⟩ ⟨1⟩

def auctionOwnerAddressAt (evm : EVM.State) : AccountAddress :=
  AccountAddress.ofNat
    (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨151⟩)
      solcAddrMask).toNat

def auctionSettleAuctionAmount (evm : EVM.State) : UInt256 :=
  Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨208⟩

def auctionSettleAuctionSnapshotFields (evm : EVM.State) : List (Ident × Value) :=
  [("nounId", .int (Int.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨207⟩).toNat)),
    ("amount", .int (Int.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨208⟩).toNat)),
    ("startTime",
      .int (Int.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨209⟩).toNat)),
    ("endTime",
      .int (Int.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨210⟩).toNat)),
    ("bidder",
      .address (AccountAddress.ofNat
        (auctionPackedBidderWord
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨211⟩)).toNat)),
    ("settled",
      wordToElem .bool
        (auctionPackedSettledWord (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨211⟩)))]

def auctionSettleAuctionSnapshotValue (evm : EVM.State) : Value :=
  .struct "Auction" (auctionSettleAuctionSnapshotFields evm)

def auctionSettleAuctionSnapshotStore (evm : EVM.State) : Store :=
  (∅ : Store).insert "_auction" (auctionSettleAuctionSnapshotValue evm)

theorem auctionSettleAuctionSnapshotStore_get_self (evm : EVM.State) :
    (auctionSettleAuctionSnapshotStore evm).get? "_auction" =
      some (auctionSettleAuctionSnapshotValue evm) := by
  rw [auctionSettleAuctionSnapshotStore]
  exact store_get_self _ _ _

theorem auctionSettleAuctionSnapshotStore_get_ne (evm : EVM.State) {x : Ident}
    (hne : x ≠ "_auction") :
    (auctionSettleAuctionSnapshotStore evm).get? x = none := by
  rw [auctionSettleAuctionSnapshotStore]
  have hbeq : ("_auction" == x) = false := by
    rw [beq_eq_false_iff_ne]
    intro h
    exact hne h.symm
  rw [store_get_ne _ _ hbeq]
  simp

theorem auctionSettleAuctionSnapshotStore_base_auction (evm : EVM.State) :
    (auctionSettleAuctionSnapshotStore evm).get? "auction" = none := by
  exact auctionSettleAuctionSnapshotStore_get_ne evm (by decide)

theorem auctionSettleAuctionSnapshotStore_base_nouns (evm : EVM.State) :
    (auctionSettleAuctionSnapshotStore evm).get? "nouns" = none := by
  exact auctionSettleAuctionSnapshotStore_get_ne evm (by decide)

theorem auctionSettleAuctionSnapshotStore_base_owner (evm : EVM.State) :
    (auctionSettleAuctionSnapshotStore evm).get? "_owner" = none := by
  exact auctionSettleAuctionSnapshotStore_get_ne evm (by decide)

theorem auctionSettleAuctionSnapshotStore_insert_base_owner
    (evm : EVM.State) {ret : Ident} (v : Value) (hne : (ret == "_owner") = false) :
    ((auctionSettleAuctionSnapshotStore evm).insert ret v).get? "_owner" = none := by
  rw [store_get_ne _ _ hne]
  exact auctionSettleAuctionSnapshotStore_base_owner evm

theorem evalExpr_settleAuction_snapshot (evm : EVM.State) :
    evalExpr? auctionConfig { contract := auctionContract, locals := ∅ } evm (.storage auctionRef) =
      .ok (auctionSettleAuctionSnapshotValue evm) := by
  have hloadNoun : storageLocLoad evm (auctionUint256Loc ⟨207⟩) =
      .int (Int.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨207⟩).toNat) := by
    simpa using auctionStorageLocLoad_uint256 evm ⟨207⟩
  have hloadAmount : storageLocLoad evm (auctionUint256Loc ⟨208⟩) =
      .int (Int.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨208⟩).toNat) := by
    simpa using auctionStorageLocLoad_uint256 evm ⟨208⟩
  have hloadStart : storageLocLoad evm (auctionUint256Loc ⟨209⟩) =
      .int (Int.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨209⟩).toNat) := by
    simpa using auctionStorageLocLoad_uint256 evm ⟨209⟩
  have hloadEnd : storageLocLoad evm (auctionUint256Loc ⟨210⟩) =
      .int (Int.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨210⟩).toNat) := by
    simpa using auctionStorageLocLoad_uint256 evm ⟨210⟩
  have hloadBidder : storageLocLoad evm (auctionAddrLoc ⟨211⟩) =
      .address (AccountAddress.ofNat
        (auctionPackedBidderWord
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨211⟩)).toNat) := by
    simpa [auctionPackedBidderWord] using
      auctionStorageLocLoad_address_offset0 evm ⟨211⟩
  have hloadSettled : storageLocLoad evm (auctionBoolLocAt ⟨211⟩ 20) =
      wordToElem .bool
        (auctionPackedSettledWord (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨211⟩)) := by
    simpa [auctionPackedSettledWord, auctionPackedSettledBaseWord] using
      auctionStorageLocLoad_bool_offset evm ⟨211⟩ ⟨20, by decide⟩
  simp [evalExpr?, evalStorageRef, evalStorageRefSteps, auctionRef, auctionConfig,
    resolveStorageRef?, storageTypeAt?, auctionContract, storageDecls, auctionStructTy, uint256St,
    addrSt, boolSt, readStorage?, readFields?, EvalResult.ofOption, EvalResult.bind, bind, pure,
    auctionSettleAuctionSnapshotValue, auctionSettleAuctionSnapshotFields, auctionStorageLayout,
    hloadNoun, hloadAmount, hloadStart, hloadEnd, hloadBidder, hloadSettled]

theorem auctionSetBoolOffset20TrueNat_lt_size (old : UInt256) :
    old.toNat % 2 ^ 160 + 2 ^ 160 + old.toNat / 2 ^ 168 * 2 ^ 168 <
      UInt256.size := by
  have hq : old.toNat / 2 ^ 168 < 2 ^ 88 := by
    apply Nat.div_lt_of_lt_mul
    rw [show 2 ^ 168 * 2 ^ 88 = (2 : Nat) ^ 256 by rw [← Nat.pow_add]]
    change old.val.val < 2 ^ 256
    simp [UInt256.size]
  have hlow : old.toNat % 2 ^ 160 ≤ 2 ^ 160 - 1 :=
    Nat.le_pred_of_lt (Nat.mod_lt _ (by norm_num))
  have hqle : old.toNat / 2 ^ 168 ≤ 2 ^ 88 - 1 := Nat.le_pred_of_lt hq
  have hqterm : old.toNat / 2 ^ 168 * 2 ^ 168 ≤ (2 ^ 88 - 1) * 2 ^ 168 :=
    Nat.mul_le_mul_right _ hqle
  have hmax : (2 ^ 160 - 1) + 2 ^ 160 + (2 ^ 88 - 1) * 2 ^ 168 <
      UInt256.size := by
    norm_num [UInt256.size, Nat.pow_add]
  omega

theorem auctionStorageLocStore_bool_true_offset20 (evm : EVM.State) (slot : UInt256) :
    storageLocStore evm (auctionBoolLocAt slot 20) (.bool true) =
      some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot
        (auctionSetBoolOffset20TrueWord
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot))) := by
  unfold storageLocStore storageLocWriteWord auctionBoolLocAt auctionSetBoolOffset20TrueWord
  simp only [valueToWord, Bool.toUInt256_true, bind, Option.bind]
  congr 2
  apply u256_inj
  show fromBytes'
      (List.take (20 : Fin 32).val _ ++ List.take (1 : Fin 33).val _
        ++ List.drop ((20 : Fin 32).val + (1 : Fin 33).val) _) =
        (UInt256.ofNat
          ((Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot).toNat % 2 ^ 160 +
            2 ^ 160 +
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot).toNat / 2 ^ 168 *
              2 ^ 168)).toNat
  rw [show (20 : Fin 32).val = 20 from rfl, show (1 : Fin 33).val = 1 from rfl]
  rw [show List.take 1 (EVM.Word.toBytesLEWithSizeProof (UInt256.ofNat 1)).1 = [1] by
    native_decide]
  rw [fromBytes'_append, fromBytes'_append]
  rw [fromBytes'_take_wordLE, fromBytes'_drop_wordLE]
  have hlen20 : ((EVM.Word.toBytesLEWithSizeProof
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).1.take 20).length = 20 := by
    rw [List.length_take, (EVM.Word.toBytesLEWithSizeProof
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).2]
    norm_num
  rw [hlen20]
  simp [fromBytes']
  change (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot).toNat % 2 ^ 160 +
      2 ^ 160 +
      2 ^ 168 * ((Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot).toNat / 2 ^ 168) =
    (UInt256.ofNat
      ((Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot).toNat % 2 ^ 160 +
        2 ^ 160 +
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot).toNat / 2 ^ 168 *
          2 ^ 168)).toNat
  rw [show 2 ^ 168 *
      ((Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot).toNat / 2 ^ 168) =
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot).toNat / 2 ^ 168 * 2 ^ 168 by
    ring]
  rw [ulit_toNat' _ (auctionSetBoolOffset20TrueNat_lt_size
    (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot))]

theorem auctionSettleAuctionAssignSettledTrue (evm : EVM.State) (locals : Store)
    (hbase : locals.get? "auction" = none) :
    assignStorageRef? auctionConfig { contract := auctionContract, locals := locals } evm .storage
        (aField "settled") (.bool true) =
      .ok ({ contract := auctionContract, locals := locals },
        auctionSettleAuctionMarkSettledState evm) := by
  have her : evalStorageRef auctionConfig { contract := auctionContract, locals := locals } evm
      (aField "settled") =
      .ok ({ base := "auction", steps := [.field "settled"] } : EvaledStorageRef) := by
    simp [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, aField, EvalResult.bind, pure,
      bind]
  have hty : storageTypeAt? auctionContract.storage
      ({ base := "auction", steps := [.field "settled"] } : EvaledStorageRef) =
        some (.elem .bool) := by
    decide
  exact assignStorageRef_storage_scalar_value (cfg := auctionConfig)
    (solm := { contract := auctionContract, locals := locals }) (evm := evm)
    (evm' := auctionSettleAuctionMarkSettledState evm)
    (slot := aField "settled")
    (er := { base := "auction", steps := [.field "settled"] })
    (ty := .elem .bool) (loc := auctionBoolLocAt ⟨211⟩ 20)
    (value := .bool true) (by simpa [aField] using hbase) her hty (by rfl)
    (by trivial)
    (by simpa [auctionSettleAuctionMarkSettledState] using
      auctionStorageLocStore_bool_true_offset20 evm ⟨211⟩)

theorem auctionSettleAuctionMarkSettledState_storageLoad_ne_settled
    (evm : EVM.State) {slot : UInt256} (hne : slot ≠ ⟨211⟩) :
    Solm.EVM.storageLoad (auctionSettleAuctionMarkSettledState evm)
        (auctionSettleAuctionMarkSettledState evm).executionEnv.codeOwner slot =
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot := by
  have hload : Solm.EVM.storageLoad (auctionSettleAuctionMarkSettledState evm)
      evm.executionEnv.codeOwner slot =
        Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot := by
    simpa [auctionSettleAuctionMarkSettledState] using
      storageLoad_storageStore_ne evm evm.executionEnv.codeOwner
        (readSlot := slot) (writeSlot := ⟨211⟩)
        (val := auctionSetBoolOffset20TrueWord
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨211⟩)) hne
  have henv : (auctionSettleAuctionMarkSettledState evm).executionEnv = evm.executionEnv := by
    simpa [auctionSettleAuctionMarkSettledState] using
      storageStore_executionEnv evm evm.executionEnv.codeOwner ⟨211⟩
        (auctionSetBoolOffset20TrueWord
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨211⟩))
  simpa [henv] using hload

theorem auctionSettleAuctionMarkSettledState_storageLoad_nouns (evm : EVM.State) :
    Solm.EVM.storageLoad (auctionSettleAuctionMarkSettledState evm)
        (auctionSettleAuctionMarkSettledState evm).executionEnv.codeOwner ⟨201⟩ =
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨201⟩ := by
  exact auctionSettleAuctionMarkSettledState_storageLoad_ne_settled evm (by decide)

theorem auctionSettleAuctionMarkSettledState_storageLoad_owner (evm : EVM.State) :
    Solm.EVM.storageLoad (auctionSettleAuctionMarkSettledState evm)
        (auctionSettleAuctionMarkSettledState evm).executionEnv.codeOwner ⟨151⟩ =
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨151⟩ := by
  exact auctionSettleAuctionMarkSettledState_storageLoad_ne_settled evm (by decide)

theorem auctionSettleAuctionMarkSettledState_storageLoad_amount (evm : EVM.State) :
    Solm.EVM.storageLoad (auctionSettleAuctionMarkSettledState evm)
        (auctionSettleAuctionMarkSettledState evm).executionEnv.codeOwner ⟨208⟩ =
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨208⟩ := by
  exact auctionSettleAuctionMarkSettledState_storageLoad_ne_settled evm (by decide)

theorem auctionSettleAuctionMarkSettledMap_accountMap {cA gh bl σ σ₀ A I}
    {g : Sat256} :
    accountMapEquiv (auctionSettleAuctionMarkSettledMap σ I)
      (auctionSettleAuctionMarkSettledState
        (initState cA gh bl σ σ₀ g A I)).accountMap := by
  apply accountMapEquiv.of_eq
  simp [auctionSettleAuctionMarkSettledMap, auctionSettleAuctionMarkSettledState, initState,
    storageStore_accountMap, auctionSlotWord, Solm.EVM.storageLoad, State.lookupAccount,
    Account.lookupStorage]

theorem auctionSettleAuctionMarkSettledState_equiv
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : Sat256}
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    EVMStateEquiv
      (auctionSettleAuctionMarkSettledState (initState cA gh bl σ_evm σ₀ g A I))
      (auctionSettleAuctionMarkSettledState (initState cA gh bl σ_solm σ₀ g A I)) := by
  have hσ : EVMStateEquiv (initState cA gh bl σ_evm σ₀ g A I)
      (initState cA gh bl σ_solm σ₀ g A I) := by
    exact EVMStateEquiv.initState hAccounts
  exact hσ.storageStore_codeOwner ⟨211⟩ (by
    have hword : auctionSlotWord ⟨211⟩ σ_evm I = auctionSlotWord ⟨211⟩ σ_solm I := by
      simpa [auctionSlotWord] using
        accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨211⟩ (default : UInt256)
    simpa [initState, auctionSlotWord, Solm.EVM.storageLoad, State.lookupAccount] using
      congrArg auctionSetBoolOffset20TrueWord hword)

theorem auctionSettleAuctionAssignStatusEntered (evm : EVM.State) (locals : Store)
    (hbase : locals.get? "_status" = none) :
    assignStorageRef? auctionConfig { contract := auctionContract, locals := locals } evm .storage
        statusRef (.int 2) =
      .ok ({ contract := auctionContract, locals := locals },
        auctionSettleAuctionEnterState evm) := by
  have her : evalStorageRef auctionConfig { contract := auctionContract, locals := locals } evm
      statusRef = .ok { base := "_status", steps := [] } := by
    simp [evalStorageRef, evalStorageRefSteps, statusRef, EvalResult.bind, pure, bind]
  have hty : storageTypeAt? auctionContract.storage
      ({ base := "_status", steps := [] } : EvaledStorageRef) = some (.elem (.int uint256Int)) := by
    decide
  exact assignStorageRef_storage_scalar (cfg := auctionConfig)
    (solm := { contract := auctionContract, locals := locals }) (evm := evm)
    (evm' := auctionSettleAuctionEnterState evm) (slot := statusRef)
    (er := { base := "_status", steps := [] }) (ty := .elem (.int uint256Int))
    (loc := auctionUint256Loc ⟨101⟩) (n := 2) hbase her hty (by rfl)
    (by simpa [auctionSettleAuctionEnterState] using
      auctionStorageLocStore_uint256 evm ⟨101⟩ ⟨2⟩)

theorem auctionSettleAuctionAssignStatusNotEntered (evm : EVM.State) (locals : Store)
    (hbase : locals.get? "_status" = none) :
    assignStorageRef? auctionConfig { contract := auctionContract, locals := locals } evm .storage
        statusRef (.int 1) =
      .ok ({ contract := auctionContract, locals := locals },
        auctionSettleAuctionExitState evm) := by
  have her : evalStorageRef auctionConfig { contract := auctionContract, locals := locals } evm
      statusRef = .ok { base := "_status", steps := [] } := by
    simp [evalStorageRef, evalStorageRefSteps, statusRef, EvalResult.bind, pure, bind]
  have hty : storageTypeAt? auctionContract.storage
      ({ base := "_status", steps := [] } : EvaledStorageRef) = some (.elem (.int uint256Int)) := by
    decide
  exact assignStorageRef_storage_scalar (cfg := auctionConfig)
    (solm := { contract := auctionContract, locals := locals }) (evm := evm)
    (evm' := auctionSettleAuctionExitState evm) (slot := statusRef)
    (er := { base := "_status", steps := [] }) (ty := .elem (.int uint256Int))
    (loc := auctionUint256Loc ⟨101⟩) (n := 1) hbase her hty (by rfl)
    (by simpa [auctionSettleAuctionExitState] using
      auctionStorageLocStore_uint256 evm ⟨101⟩ ⟨1⟩)

theorem auctionSettleAuctionEnterMap_accountMap {cA gh bl σ σ₀ A I} {g : Sat256} :
    accountMapEquiv (auctionSettleAuctionEnterMap σ I)
      (auctionSettleAuctionEnterState (initState cA gh bl σ σ₀ g A I)).accountMap := by
  apply accountMapEquiv.of_eq
  simp [auctionSettleAuctionEnterMap, auctionSettleAuctionEnterState, initState,
    storageStore_accountMap]

theorem auctionSettleAuctionExitMap_accountMap {cA gh bl σ σ₀ A I} {g : Sat256} :
    accountMapEquiv (auctionSettleAuctionExitMap σ I)
      (auctionSettleAuctionExitState (initState cA gh bl σ σ₀ g A I)).accountMap := by
  apply accountMapEquiv.of_eq
  simp [auctionSettleAuctionExitMap, auctionSettleAuctionExitState, initState,
    storageStore_accountMap]

theorem auctionSettleAuctionEnterState_equiv
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : Sat256}
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    EVMStateEquiv
      (auctionSettleAuctionEnterState (initState cA gh bl σ_evm σ₀ g A I))
      (auctionSettleAuctionEnterState (initState cA gh bl σ_solm σ₀ g A I)) := by
  have hσ : EVMStateEquiv (initState cA gh bl σ_evm σ₀ g A I)
      (initState cA gh bl σ_solm σ₀ g A I) := by
    exact EVMStateEquiv.initState hAccounts
  exact hσ.storageStore_codeOwner ⟨101⟩ rfl

theorem auctionSettleAuctionExitState_equiv
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : Sat256}
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    EVMStateEquiv
      (auctionSettleAuctionExitState (initState cA gh bl σ_evm σ₀ g A I))
      (auctionSettleAuctionExitState (initState cA gh bl σ_solm σ₀ g A I)) := by
  have hσ : EVMStateEquiv (initState cA gh bl σ_evm σ₀ g A I)
      (initState cA gh bl σ_solm σ₀ g A I) := by
    exact EVMStateEquiv.initState hAccounts
  exact hσ.storageStore_codeOwner ⟨101⟩ rfl

theorem auctionSettleAuctionEnterState_storageLoad_ne_status
    (evm : EVM.State) {slot : UInt256} (hne : slot ≠ ⟨101⟩) :
    Solm.EVM.storageLoad (auctionSettleAuctionEnterState evm)
        (auctionSettleAuctionEnterState evm).executionEnv.codeOwner slot =
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot := by
  have hload : Solm.EVM.storageLoad (auctionSettleAuctionEnterState evm)
      evm.executionEnv.codeOwner slot =
        Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot := by
    simpa [auctionSettleAuctionEnterState] using
      storageLoad_storageStore_ne evm evm.executionEnv.codeOwner
        (readSlot := slot) (writeSlot := ⟨101⟩) (val := ⟨2⟩) hne
  have henv : (auctionSettleAuctionEnterState evm).executionEnv = evm.executionEnv := by
    simpa [auctionSettleAuctionEnterState] using
      storageStore_executionEnv evm evm.executionEnv.codeOwner ⟨101⟩ ⟨2⟩
  simpa [henv] using hload

theorem auctionSettleAuctionEnterState_storageLoad_startTime (evm : EVM.State) :
    Solm.EVM.storageLoad (auctionSettleAuctionEnterState evm)
        (auctionSettleAuctionEnterState evm).executionEnv.codeOwner ⟨209⟩ =
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨209⟩ := by
  exact auctionSettleAuctionEnterState_storageLoad_ne_status evm (by decide)

theorem evalExpr_settleAuction_startTime (evm : EVM.State) :
    evalExpr? auctionConfig { contract := auctionContract, locals := ∅ } evm
      (.storage (aField "startTime")) =
      .ok (.int (Int.ofNat
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨209⟩).toNat)) := by
  have hbase : (∅ : Store).get? (aField "startTime").base = none := by
    simp [aField]
  have her : evalStorageRef auctionConfig { contract := auctionContract, locals := (∅ : Store) }
      evm (aField "startTime") =
      .ok ({ base := "auction", steps := [.field "startTime"] } : EvaledStorageRef) := by
    simp [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, aField, auctionConfig,
      auctionContract, storageDecls, auctionStructTy, uint256St, addrSt, boolSt,
      EvalResult.bind, bind, pure]
  have hty : storageTypeAt? auctionContract.storage
      ({ base := "auction", steps := [.field "startTime"] } : EvaledStorageRef) =
      some (.elem (.int uint256Int)) := by
    simp [storageTypeAt?, storageTypeStep?, auctionContract, storageDecls, auctionStructTy,
      uint256St]
  have hloc : auctionConfig.storage.layout
      ({ base := "auction", steps := [.field "startTime"] } : EvaledStorageRef) =
      fun _ => some (auctionUint256Loc ⟨209⟩) := by
    funext evm'
    simp [auctionConfig, auctionStorageLayout]
  rw [evalExpr_storage_scalar (t := .int uint256Int) (hbase := hbase)
    (her := her) (hty := hty) (hloc := hloc)]
  exact congrArg EvalResult.ok (by simpa using auctionStorageLocLoad_uint256 evm ⟨209⟩)

theorem evalExpr_settleAuction_endTime (evm : EVM.State) :
    evalExpr? auctionConfig { contract := auctionContract, locals := ∅ } evm
      (.storage (aField "endTime")) =
      .ok (.int (Int.ofNat
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨210⟩).toNat)) := by
  have hbase : (∅ : Store).get? (aField "endTime").base = none := by
    simp [aField]
  have her : evalStorageRef auctionConfig { contract := auctionContract, locals := (∅ : Store) }
      evm (aField "endTime") =
      .ok ({ base := "auction", steps := [.field "endTime"] } : EvaledStorageRef) := by
    simp [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, aField, auctionConfig,
      auctionContract, storageDecls, auctionStructTy, uint256St, addrSt, boolSt,
      EvalResult.bind, bind, pure]
  have hty : storageTypeAt? auctionContract.storage
      ({ base := "auction", steps := [.field "endTime"] } : EvaledStorageRef) =
      some (.elem (.int uint256Int)) := by
    simp [storageTypeAt?, storageTypeStep?, auctionContract, storageDecls, auctionStructTy,
      uint256St]
  have hloc : auctionConfig.storage.layout
      ({ base := "auction", steps := [.field "endTime"] } : EvaledStorageRef) =
      fun _ => some (auctionUint256Loc ⟨210⟩) := by
    funext evm'
    simp [auctionConfig, auctionStorageLayout]
  rw [evalExpr_storage_scalar (t := .int uint256Int) (hbase := hbase)
    (her := her) (hty := hty) (hloc := hloc)]
  exact congrArg EvalResult.ok (by simpa using auctionStorageLocLoad_uint256 evm ⟨210⟩)

theorem evalExpr_settleAuction_now (evm : EVM.State) (locals : Store) :
    evalExpr? auctionConfig { contract := auctionContract, locals := locals } evm now =
      .ok (.int (Int.ofNat (UInt256.ofNat evm.executionEnv.header.timestamp).toNat)) := by
  simp [now, evalExpr?, envValue, pure]

theorem evalExpr_settleAuction_entered (evm : EVM.State) (locals : Store) :
    evalExpr? auctionConfig { contract := auctionContract, locals := locals } evm entered =
      .ok (.int 2) := by
  simp [entered, evalExpr?, pure]

theorem evalExpr_settleAuction_notEntered (evm : EVM.State) (locals : Store) :
    evalExpr? auctionConfig { contract := auctionContract, locals := locals } evm notEntered =
      .ok (.int 1) := by
  simp [notEntered, evalExpr?, pure]

theorem evalExpr_settleAuction_zeroAddr (evm : EVM.State) (locals : Store) :
    evalExpr? auctionConfig { contract := auctionContract, locals := locals } evm zeroAddr =
      .ok (.address (AccountAddress.ofNat 0)) := by
  simp [zeroAddr, evalExpr?, castValue?, addrSt, EvalResult.bind, EvalResult.ofOption, bind,
    pure]

theorem evalExpr_settleAuction_status (evm : EVM.State) :
    evalExpr? auctionConfig { contract := auctionContract, locals := ∅ } evm
      (.storage statusRef) =
      .ok (.int (Int.ofNat
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨101⟩).toNat)) := by
  have her : evalStorageRef auctionConfig { contract := auctionContract, locals := (∅ : Store) }
      evm statusRef = .ok { base := "_status", steps := [] } := by
    simp [evalStorageRef, evalStorageRefSteps, statusRef, EvalResult.bind, pure, bind]
  have hty : storageTypeAt? auctionContract.storage
      ({ base := "_status", steps := [] } : EvaledStorageRef) =
        some (.elem (.int uint256Int)) := by
    decide
  rw [evalExpr_storage_scalar (t := .int uint256Int) (hbase := by simp)
    (her := her) (hty := hty) (hloc := by rfl)]
  exact congrArg EvalResult.ok (by simpa using auctionStorageLocLoad_uint256 evm ⟨101⟩)

theorem evalExpr_settleAuction_status_ne_entered_true (evm : EVM.State)
    (hstatus : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨101⟩ ≠ ⟨2⟩) :
    evalExpr? auctionConfig { contract := auctionContract, locals := ∅ } evm
      (.binary .ne (.storage statusRef) entered) = .ok (.bool true) := by
  simp only [evalExpr?, evalExpr_settleAuction_status, evalExpr_settleAuction_entered,
    EvalResult.bind, bind, evalBinaryOp?]
  have hbeq :
      (Value.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨101⟩).toNat) ==
        Value.int 2) = false := by
    rw [beq_eq_false_iff_ne]
    intro h
    rw [Value.int.injEq] at h
    apply hstatus
    apply u256_inj
    change (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨101⟩).toNat =
      (⟨2⟩ : UInt256).toNat
    have hnat :
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨101⟩).toNat = 2 :=
      Int.ofNat.inj h
    simpa using hnat
  rw [hbeq]
  rfl

theorem evalExpr_settleAuction_status_ne_entered_false (evm : EVM.State)
    (hstatus : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨101⟩ = ⟨2⟩) :
    evalExpr? auctionConfig { contract := auctionContract, locals := ∅ } evm
      (.binary .ne (.storage statusRef) entered) = .ok (.bool false) := by
  simp only [evalExpr?, evalExpr_settleAuction_status, evalExpr_settleAuction_entered,
    EvalResult.bind, bind, evalBinaryOp?]
  rw [hstatus]
  rfl

theorem evalExpr_settleAuction_mem_nounId (evm : EVM.State) :
    evalExpr? auctionConfig
        { contract := auctionContract, locals := auctionSettleAuctionSnapshotStore evm }
        evm (auctionMemField "nounId") =
      .ok (.int (Int.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨207⟩).toNat)) := by
  simp [auctionMemField, auctionSettleAuctionSnapshotStore, auctionSettleAuctionSnapshotValue,
    auctionSettleAuctionSnapshotFields, evalExpr?, EvalResult.ofOption, lookupField?,
    lookupAssoc, EvalResult.bind, bind]

theorem evalExpr_settleAuction_mem_amount (evm : EVM.State) :
    evalExpr? auctionConfig
        { contract := auctionContract, locals := auctionSettleAuctionSnapshotStore evm }
        evm (auctionMemField "amount") =
      .ok (.int (Int.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨208⟩).toNat)) := by
  simp [auctionMemField, auctionSettleAuctionSnapshotStore, auctionSettleAuctionSnapshotValue,
    auctionSettleAuctionSnapshotFields, evalExpr?, EvalResult.ofOption, lookupField?,
    lookupAssoc, EvalResult.bind, bind]

theorem evalExpr_settleAuction_mem_startTime (evm : EVM.State) :
    evalExpr? auctionConfig
        { contract := auctionContract, locals := auctionSettleAuctionSnapshotStore evm }
        evm (auctionMemField "startTime") =
      .ok (.int (Int.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨209⟩).toNat)) := by
  simp [auctionMemField, auctionSettleAuctionSnapshotStore, auctionSettleAuctionSnapshotValue,
    auctionSettleAuctionSnapshotFields, evalExpr?, EvalResult.ofOption, lookupField?,
    lookupAssoc, EvalResult.bind, bind]

theorem evalExpr_settleAuction_mem_endTime (evm : EVM.State) :
    evalExpr? auctionConfig
        { contract := auctionContract, locals := auctionSettleAuctionSnapshotStore evm }
        evm (auctionMemField "endTime") =
      .ok (.int (Int.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨210⟩).toNat)) := by
  simp [auctionMemField, auctionSettleAuctionSnapshotStore, auctionSettleAuctionSnapshotValue,
    auctionSettleAuctionSnapshotFields, evalExpr?, EvalResult.ofOption, lookupField?,
    lookupAssoc, EvalResult.bind, bind]

theorem evalExpr_settleAuction_mem_bidder (evm : EVM.State) :
    evalExpr? auctionConfig
        { contract := auctionContract, locals := auctionSettleAuctionSnapshotStore evm }
        evm (auctionMemField "bidder") =
      .ok (.address (AccountAddress.ofNat
        (auctionPackedBidderWord
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨211⟩)).toNat)) := by
  simp [auctionMemField, auctionSettleAuctionSnapshotStore, auctionSettleAuctionSnapshotValue,
    auctionSettleAuctionSnapshotFields, evalExpr?, EvalResult.ofOption, lookupField?,
    lookupAssoc, EvalResult.bind, bind]

theorem evalExpr_settleAuction_mem_settled (evm : EVM.State) :
    evalExpr? auctionConfig
        { contract := auctionContract, locals := auctionSettleAuctionSnapshotStore evm }
        evm (auctionMemField "settled") =
      .ok (wordToElem .bool
        (auctionPackedSettledWord (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨211⟩))) := by
  simp [auctionMemField, auctionSettleAuctionSnapshotStore, auctionSettleAuctionSnapshotValue,
    auctionSettleAuctionSnapshotFields, evalExpr?, EvalResult.ofOption, lookupField?,
    lookupAssoc, EvalResult.bind, bind]

theorem evalExpr_settleAuction_started_true (evm : EVM.State)
    (hstart : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨209⟩ ≠ ⟨0⟩) :
    evalExpr? auctionConfig
        { contract := auctionContract, locals := auctionSettleAuctionSnapshotStore evm }
        evm (.binary .ne (auctionMemField "startTime") (.intLit 0)) = .ok (.bool true) := by
  simp only [evalExpr?, evalExpr_settleAuction_mem_startTime, EvalResult.bind, bind, pure,
    evalBinaryOp?]
  have hneNat : ¬ (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨209⟩).toNat = 0 := by
    intro hzero
    exact hstart (uint256_toNat_eq_zero hzero)
  simp [hneNat]

theorem evalExpr_settleAuction_started_false (evm : EVM.State)
    (hstart : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨209⟩ = ⟨0⟩) :
    evalExpr? auctionConfig
        { contract := auctionContract, locals := auctionSettleAuctionSnapshotStore evm }
        evm (.binary .ne (auctionMemField "startTime") (.intLit 0)) = .ok (.bool false) := by
  simp only [evalExpr?, evalExpr_settleAuction_mem_startTime, EvalResult.bind, bind, pure,
    evalBinaryOp?]
  rw [hstart]
  rfl

theorem evalExpr_settleAuction_settled (evm : EVM.State) :
    evalExpr? auctionConfig { contract := auctionContract, locals := ∅ } evm
      (.storage (aField "settled")) =
      .ok (wordToElem .bool
        (auctionPackedSettledWord (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨211⟩))) := by
  have hbase : (∅ : Store).get? (aField "settled").base = none := by
    simp [aField]
  have her : evalStorageRef auctionConfig { contract := auctionContract, locals := (∅ : Store) }
      evm (aField "settled") =
      .ok ({ base := "auction", steps := [.field "settled"] } : EvaledStorageRef) := by
    simp [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, aField, auctionConfig,
      auctionContract, storageDecls, auctionStructTy, uint256St, addrSt, boolSt,
      EvalResult.bind, bind, pure]
  have hty : storageTypeAt? auctionContract.storage
      ({ base := "auction", steps := [.field "settled"] } : EvaledStorageRef) =
      some (.elem .bool) := by
    simp [storageTypeAt?, storageTypeStep?, auctionContract, storageDecls, auctionStructTy, boolSt]
  have hloc : auctionConfig.storage.layout
      ({ base := "auction", steps := [.field "settled"] } : EvaledStorageRef) =
      fun _ => some (auctionBoolLocAt ⟨211⟩ 20) := by
    funext evm'
    simp [auctionConfig, auctionStorageLayout]
  rw [evalExpr_storage_scalar (t := .bool) (hbase := hbase)
    (her := her) (hty := hty) (hloc := hloc)]
  exact congrArg EvalResult.ok (by
    simpa [auctionPackedSettledWord, auctionPackedSettledBaseWord] using
      auctionStorageLocLoad_bool_offset evm ⟨211⟩ ⟨20, by decide⟩)

theorem evalExpr_settleAuction_settled_false (evm : EVM.State)
    (hsettled : auctionPackedSettledWord
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨211⟩) = ⟨0⟩) :
    evalExpr? auctionConfig { contract := auctionContract, locals := ∅ } evm
      (.storage (aField "settled")) = .ok (.bool false) := by
  rw [evalExpr_settleAuction_settled]
  simp [wordToElem, hsettled]

theorem evalExpr_settleAuction_settled_true (evm : EVM.State)
    (hsettled : auctionPackedSettledWord
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨211⟩) ≠ ⟨0⟩) :
    evalExpr? auctionConfig { contract := auctionContract, locals := ∅ } evm
      (.storage (aField "settled")) = .ok (.bool true) := by
  rw [evalExpr_settleAuction_settled]
  have hbeq :
      ((auctionPackedSettledWord
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨211⟩)).val == 0) =
        false := by
    rw [beq_eq_false_iff_ne]
    intro hval
    apply hsettled
    apply u256_inj
    simpa [UInt256.toNat] using hval
  simp [wordToElem, hbeq]

theorem evalExpr_settleAuction_not_settled_true (evm : EVM.State)
    (hsettled : auctionPackedSettledWord
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨211⟩) = ⟨0⟩) :
    evalExpr? auctionConfig
        { contract := auctionContract, locals := auctionSettleAuctionSnapshotStore evm }
        evm (.unary .not (auctionMemField "settled")) = .ok (.bool true) := by
  simp [evalExpr?, EvalResult.bind, bind, evalExpr_settleAuction_mem_settled,
    wordToElem, hsettled, evalUnaryOp?, EvalResult.ofOption]

theorem evalExpr_settleAuction_not_settled_false (evm : EVM.State)
    (hsettled : auctionPackedSettledWord
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨211⟩) ≠ ⟨0⟩) :
    evalExpr? auctionConfig
        { contract := auctionContract, locals := auctionSettleAuctionSnapshotStore evm }
        evm (.unary .not (auctionMemField "settled")) = .ok (.bool false) := by
  rw [Solm.evalExpr?.eq_def]
  simp only [evalExpr_settleAuction_mem_settled, EvalResult.bind, bind, evalUnaryOp?]
  have hbeq :
      ((auctionPackedSettledWord
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨211⟩)).val == 0) =
        false := by
    rw [beq_eq_false_iff_ne]
    intro hval
    apply hsettled
    apply u256_inj
    simpa [UInt256.toNat] using hval
  simp [wordToElem, hbeq, EvalResult.ofOption]

theorem evalExpr_settleAuction_time_reached_true (evm : EVM.State)
    (htime : (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨210⟩).toNat ≤
      (UInt256.ofNat evm.executionEnv.header.timestamp).toNat) :
    evalExpr? auctionConfig
        { contract := auctionContract, locals := auctionSettleAuctionSnapshotStore evm }
        evm (.binary .ge now (auctionMemField "endTime")) = .ok (.bool true) := by
  simp only [evalExpr?, evalExpr_settleAuction_now, evalExpr_settleAuction_mem_endTime,
    EvalResult.bind, bind, evalBinaryOp?]
  norm_num
  exact htime

theorem evalExpr_settleAuction_time_reached_false (evm : EVM.State)
    (htime : (UInt256.ofNat evm.executionEnv.header.timestamp).toNat <
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨210⟩).toNat) :
    evalExpr? auctionConfig
        { contract := auctionContract, locals := auctionSettleAuctionSnapshotStore evm }
        evm (.binary .ge now (auctionMemField "endTime")) = .ok (.bool false) := by
  simp only [evalExpr?, evalExpr_settleAuction_now, evalExpr_settleAuction_mem_endTime,
    EvalResult.bind, bind, evalBinaryOp?]
  norm_num
  exact htime

theorem evalExpr_settleAuction_bidder_zero_true (evm : EVM.State)
    (hbidder :
      AccountAddress.ofNat
          (auctionPackedBidderWord
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨211⟩)).toNat =
        AccountAddress.ofNat 0) :
    evalExpr? auctionConfig
        { contract := auctionContract, locals := auctionSettleAuctionSnapshotStore evm }
        evm (.binary .eq (auctionMemField "bidder") zeroAddr) = .ok (.bool true) := by
  simp only [evalExpr?, evalExpr_settleAuction_mem_bidder, evalExpr_settleAuction_zeroAddr,
    EvalResult.bind, bind, evalBinaryOp?]
  rw [hbidder]
  rfl

theorem evalExpr_settleAuction_bidder_zero_false (evm : EVM.State)
    (hbidder :
      AccountAddress.ofNat
          (auctionPackedBidderWord
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨211⟩)).toNat ≠
        AccountAddress.ofNat 0) :
    evalExpr? auctionConfig
        { contract := auctionContract, locals := auctionSettleAuctionSnapshotStore evm }
        evm (.binary .eq (auctionMemField "bidder") zeroAddr) = .ok (.bool false) := by
  simp only [evalExpr?, evalExpr_settleAuction_mem_bidder, evalExpr_settleAuction_zeroAddr,
    EvalResult.bind, bind, evalBinaryOp?]
  have hbeq :
      (Value.address (AccountAddress.ofNat
          (auctionPackedBidderWord
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨211⟩)).toNat) ==
        Value.address (AccountAddress.ofNat 0)) = false := by
    rw [beq_eq_false_iff_ne]
    intro h
    rw [Value.address.injEq] at h
    exact hbidder h
  simp [hbeq]

theorem evalExpr_settleAuction_amount_positive_true (evm : EVM.State)
    (hamount : 0 < (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨208⟩).toNat) :
    evalExpr? auctionConfig
        { contract := auctionContract, locals := auctionSettleAuctionSnapshotStore evm }
        evm (.binary .gt (auctionMemField "amount") (.intLit 0)) = .ok (.bool true) := by
  simp only [evalExpr?, evalExpr_settleAuction_mem_amount, EvalResult.bind, bind, pure,
    evalBinaryOp?]
  norm_num
  exact hamount

theorem evalExpr_settleAuction_amount_positive_false (evm : EVM.State)
    (hamount : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨208⟩ = ⟨0⟩) :
    evalExpr? auctionConfig
        { contract := auctionContract, locals := auctionSettleAuctionSnapshotStore evm }
        evm (.binary .gt (auctionMemField "amount") (.intLit 0)) = .ok (.bool false) := by
  simp only [evalExpr?, evalExpr_settleAuction_mem_amount, EvalResult.bind, bind, pure,
    evalBinaryOp?]
  rw [hamount]
  rfl

def auctionSettleAuctionDefaultPayout : List Stmt :=
  [ .internalCall "_safeTransferETHWithFallback"
      [.storage ownerRef, auctionMemField "amount"] "_pay" ]

def auctionSettleAuctionMemoryPayout : List Stmt :=
  [ .internalCall "_safeTransferETHWithMemory"
      [.storage ownerRef, auctionMemField "amount"] "_pay",
    .return [.var "_pay"] ]

theorem auctionSettleAuctionBodyReverts_notStarted (evm : EVM.State)
    (hstart : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨209⟩ = ⟨0⟩)
    (payout : List Stmt := auctionSettleAuctionDefaultPayout)
    (tail : List Stmt := []) :
    ExecFuncBody auctionConfig { contract := auctionContract, locals := ∅ } evm
      (settleAuctionBody payout ++ tail) .reverted := by
  dsimp [settleAuctionBody]
  refine ExecFuncBody.execBlockRevert ?_
  refine ExecBlock.consNormal (ExecStmt.letDecl (evalExpr_settleAuction_snapshot evm)) ?_
  exact ExecBlock.consRevert
    (ExecStmt.requireFalse (evalExpr_settleAuction_started_false evm hstart))

theorem auctionSettleAuctionBodyReverts_alreadySettled (evm : EVM.State)
    (hstart : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨209⟩ ≠ ⟨0⟩)
    (hsettled : auctionPackedSettledWord
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨211⟩) ≠ ⟨0⟩)
    (payout : List Stmt := auctionSettleAuctionDefaultPayout)
    (tail : List Stmt := []) :
    ExecFuncBody auctionConfig { contract := auctionContract, locals := ∅ } evm
      (settleAuctionBody payout ++ tail) .reverted := by
  dsimp [settleAuctionBody]
  refine ExecFuncBody.execBlockRevert ?_
  refine ExecBlock.consNormal (ExecStmt.letDecl (evalExpr_settleAuction_snapshot evm)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_settleAuction_started_true evm hstart)) ?_
  exact ExecBlock.consRevert
    (ExecStmt.requireFalse (evalExpr_settleAuction_not_settled_false evm hsettled))

theorem auctionSettleAuctionBodyReverts_timeNotReached (evm : EVM.State)
    (hstart : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨209⟩ ≠ ⟨0⟩)
    (hsettled : auctionPackedSettledWord
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨211⟩) = ⟨0⟩)
    (htime : (UInt256.ofNat evm.executionEnv.header.timestamp).toNat <
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨210⟩).toNat)
    (payout : List Stmt := auctionSettleAuctionDefaultPayout)
    (tail : List Stmt := []) :
    ExecFuncBody auctionConfig { contract := auctionContract, locals := ∅ } evm
      (settleAuctionBody payout ++ tail) .reverted := by
  dsimp [settleAuctionBody]
  refine ExecFuncBody.execBlockRevert ?_
  refine ExecBlock.consNormal (ExecStmt.letDecl (evalExpr_settleAuction_snapshot evm)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_settleAuction_started_true evm hstart)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_settleAuction_not_settled_true evm hsettled)) ?_
  exact ExecBlock.consRevert
    (ExecStmt.requireFalse (evalExpr_settleAuction_time_reached_false evm htime))

theorem evalExpr_settleAuction_nouns_after_markSettled (evm : EVM.State) :
    evalExpr? auctionConfig
        { contract := auctionContract, locals := auctionSettleAuctionSnapshotStore evm }
        (auctionSettleAuctionMarkSettledState evm) (.storage nounsRef) =
      .ok (.address (AccountAddress.ofNat
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨201⟩)
          solcAddrMask).toNat)) := by
  have her : evalStorageRef auctionConfig
      { contract := auctionContract, locals := auctionSettleAuctionSnapshotStore evm }
      (auctionSettleAuctionMarkSettledState evm) nounsRef =
        .ok { base := "nouns", steps := [] } := by
    simp [evalStorageRef, evalStorageRefSteps, nounsRef, EvalResult.bind, pure, bind]
  have hty : storageTypeAt? auctionContract.storage
      ({ base := "nouns", steps := [] } : EvaledStorageRef) = some (.elem .address) := by
    decide
  rw [evalExpr_storage_scalar (t := .address)
    (hbase := auctionSettleAuctionSnapshotStore_base_nouns evm) (her := her) (hty := hty)
    (hloc := by rfl)]
  exact congrArg EvalResult.ok (by
    have hload :=
      auctionStorageLocLoad_address_offset0 (auctionSettleAuctionMarkSettledState evm) ⟨201⟩
    rw [auctionSettleAuctionMarkSettledState_storageLoad_nouns] at hload
    simpa [auctionAddrLoc] using hload)

theorem evalExpr_settleAuction_nounsNoCode_after_markSettled (evm : EVM.State)
    (hcode :
      (UInt256.ofNat (((auctionSettleAuctionMarkSettledState evm).lookupAccount
        (AccountAddress.ofNat
          ((UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨201⟩)
            solcAddrMask).toNat))).option 0 (fun acc => acc.code.size))).toNat = 0) :
    evalExpr? auctionConfig
        { contract := auctionContract, locals := auctionSettleAuctionSnapshotStore evm }
        (auctionSettleAuctionMarkSettledState evm)
        (.binary .gt (.extCodeSize (.storage nounsRef)) (.intLit 0)) = .ok (.bool false) := by
  simp [evalExpr?, EvalResult.bind, bind, evalExpr_settleAuction_nouns_after_markSettled,
    evalBinaryOp?, EVM.Word.ofNat, hcode]

theorem evalExpr_settleAuction_nounsCode_after_markSettled (evm : EVM.State)
    (hcode :
      0 < (UInt256.ofNat (((auctionSettleAuctionMarkSettledState evm).lookupAccount
        (AccountAddress.ofNat
          ((UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨201⟩)
            solcAddrMask).toNat))).option 0 (fun acc => acc.code.size))).toNat) :
    evalExpr? auctionConfig
        { contract := auctionContract, locals := auctionSettleAuctionSnapshotStore evm }
        (auctionSettleAuctionMarkSettledState evm)
        (.binary .gt (.extCodeSize (.storage nounsRef)) (.intLit 0)) = .ok (.bool true) := by
  simp [evalExpr?, EvalResult.bind, bind, evalExpr_settleAuction_nouns_after_markSettled,
    evalBinaryOp?, EVM.Word.ofNat]
  exact hcode

theorem auctionUniswapExtCodeSizeWord_zero_lookup_code_zero {σ : AccountMap}
    {target : UInt256} {addr : AccountAddress}
    (haddr : addr = AccountAddress.ofUInt256 target)
    (hzero : Reasoning.Theory.uniswapExtCodeSizeWord σ target = ⟨0⟩) :
    (UInt256.ofNat ((σ.find? addr).option 0 (fun acc => acc.code.size))).toNat = 0 := by
  subst addr
  unfold Reasoning.Theory.uniswapExtCodeSizeWord at hzero
  cases hacc : σ.find? (AccountAddress.ofUInt256 target) with
  | none =>
      simpa [hacc, Option.option] using
        (show (UInt256.ofNat 0).toNat = 0 from by native_decide)
  | some acc =>
      have hword := congrArg UInt256.toNat hzero
      simpa [hacc] using hword

theorem auctionUniswapExtCodeSizeWord_ne_zero_lookup_code_pos {σ : AccountMap}
    {target : UInt256} {addr : AccountAddress}
    (haddr : addr = AccountAddress.ofUInt256 target)
    (hne : Reasoning.Theory.uniswapExtCodeSizeWord σ target ≠ ⟨0⟩) :
    0 < (UInt256.ofNat ((σ.find? addr).option 0 (fun acc => acc.code.size))).toNat := by
  subst addr
  unfold Reasoning.Theory.uniswapExtCodeSizeWord at hne
  cases hacc : σ.find? (AccountAddress.ofUInt256 target) with
  | none =>
      exfalso
      exact hne (by simp [hacc, Option.option])
  | some acc =>
      have hwordNe : UInt256.ofNat acc.code.size ≠ (⟨0⟩ : UInt256) := by
        intro hzero
        exact hne (by simpa [hacc] using hzero)
      have htoNatNe : (UInt256.ofNat acc.code.size).toNat ≠ 0 := by
        intro hzeroNat
        apply hwordNe
        cases hword : UInt256.ofNat acc.code.size with
        | mk val =>
            cases val using Fin.cases
            · rfl
            · simp [UInt256.toNat, hword] at hzeroNat
      simpa [hacc] using Nat.pos_of_ne_zero htoNatNe

theorem evalExpr_settleAuction_owner_after_markSettled (evm : EVM.State) :
    evalExpr? auctionConfig
        { contract := auctionContract, locals := auctionSettleAuctionSnapshotStore evm }
        (auctionSettleAuctionMarkSettledState evm) (.storage ownerRef) =
      .ok (.address (AccountAddress.ofNat
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨151⟩)
          solcAddrMask).toNat)) := by
  have her : evalStorageRef auctionConfig
      { contract := auctionContract, locals := auctionSettleAuctionSnapshotStore evm }
      (auctionSettleAuctionMarkSettledState evm) ownerRef =
        .ok { base := "_owner", steps := [] } := by
    simp [evalStorageRef, evalStorageRefSteps, ownerRef, EvalResult.bind, pure, bind]
  have hty : storageTypeAt? auctionContract.storage
      ({ base := "_owner", steps := [] } : EvaledStorageRef) = some (.elem .address) := by
    decide
  rw [evalExpr_storage_scalar (t := .address)
    (hbase := auctionSettleAuctionSnapshotStore_base_owner evm) (her := her) (hty := hty)
    (hloc := by rfl)]
  exact congrArg EvalResult.ok (by
    have hload :=
      auctionStorageLocLoad_address_offset0 (auctionSettleAuctionMarkSettledState evm) ⟨151⟩
    rw [auctionSettleAuctionMarkSettledState_storageLoad_owner] at hload
    simpa [auctionAddrLoc] using hload)

theorem evalExpr_settleAuction_zero_after_markSettled (evm : EVM.State) :
    evalExpr? auctionConfig
        { contract := auctionContract, locals := auctionSettleAuctionSnapshotStore evm }
        (auctionSettleAuctionMarkSettledState evm) (.intLit 0) = .ok (.int 0) := by
  simp [evalExpr?, pure]

theorem evalExpr_settleAuction_zeroAddr_after_markSettled (evm : EVM.State) :
    evalExpr? auctionConfig
        { contract := auctionContract, locals := auctionSettleAuctionSnapshotStore evm }
        (auctionSettleAuctionMarkSettledState evm) zeroAddr =
      .ok (.address (AccountAddress.ofNat 0)) := by
  simp [zeroAddr, evalExpr?, castValue?, addrSt, EvalResult.bind, EvalResult.ofOption, bind,
    pure]

theorem evalExpr_settleAuction_this_after_markSettled (evm : EVM.State) :
    evalExpr? auctionConfig
        { contract := auctionContract, locals := auctionSettleAuctionSnapshotStore evm }
        (auctionSettleAuctionMarkSettledState evm) (.env .this) =
      .ok (.address evm.executionEnv.codeOwner) := by
  simp [evalExpr?, envValue, auctionSettleAuctionMarkSettledState, storageStore_executionEnv, pure]

theorem evalExpr_settleAuction_mem_nounId_after_markSettled (evm : EVM.State) :
    evalExpr? auctionConfig
        { contract := auctionContract, locals := auctionSettleAuctionSnapshotStore evm }
        (auctionSettleAuctionMarkSettledState evm) (auctionMemField "nounId") =
      .ok (.int (Int.ofNat
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨207⟩).toNat)) := by
  simp [auctionMemField, auctionSettleAuctionSnapshotStore, auctionSettleAuctionSnapshotValue,
    auctionSettleAuctionSnapshotFields, evalExpr?, EvalResult.ofOption, lookupField?,
    lookupAssoc, EvalResult.bind, bind]

theorem evalExpr_settleAuction_mem_amount_after_markSettled (evm : EVM.State) :
    evalExpr? auctionConfig
        { contract := auctionContract, locals := auctionSettleAuctionSnapshotStore evm }
        (auctionSettleAuctionMarkSettledState evm) (auctionMemField "amount") =
      .ok (.int (Int.ofNat
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨208⟩).toNat)) := by
  simp [auctionMemField, auctionSettleAuctionSnapshotStore, auctionSettleAuctionSnapshotValue,
    auctionSettleAuctionSnapshotFields, evalExpr?, EvalResult.ofOption, lookupField?,
    lookupAssoc, EvalResult.bind, bind]

theorem evalExpr_settleAuction_mem_bidder_after_markSettled (evm : EVM.State) :
    evalExpr? auctionConfig
        { contract := auctionContract, locals := auctionSettleAuctionSnapshotStore evm }
        (auctionSettleAuctionMarkSettledState evm) (auctionMemField "bidder") =
      .ok (.address (AccountAddress.ofNat
        (auctionPackedBidderWord
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨211⟩)).toNat)) := by
  simp [auctionMemField, auctionSettleAuctionSnapshotStore, auctionSettleAuctionSnapshotValue,
    auctionSettleAuctionSnapshotFields, evalExpr?, EvalResult.ofOption, lookupField?,
    lookupAssoc, EvalResult.bind, bind]

theorem evalExpr_settleAuction_bidder_zero_true_after_markSettled (evm : EVM.State)
    (hbidder :
      AccountAddress.ofNat
          (auctionPackedBidderWord
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨211⟩)).toNat =
        AccountAddress.ofNat 0) :
    evalExpr? auctionConfig
        { contract := auctionContract, locals := auctionSettleAuctionSnapshotStore evm }
        (auctionSettleAuctionMarkSettledState evm)
        (.binary .eq (auctionMemField "bidder") zeroAddr) = .ok (.bool true) := by
  simp only [evalExpr?, evalExpr_settleAuction_mem_bidder_after_markSettled,
    evalExpr_settleAuction_zeroAddr_after_markSettled, EvalResult.bind, bind, evalBinaryOp?]
  rw [hbidder]
  rfl

theorem evalExpr_settleAuction_bidder_zero_false_after_markSettled (evm : EVM.State)
    (hbidder :
      AccountAddress.ofNat
          (auctionPackedBidderWord
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨211⟩)).toNat ≠
        AccountAddress.ofNat 0) :
    evalExpr? auctionConfig
        { contract := auctionContract, locals := auctionSettleAuctionSnapshotStore evm }
        (auctionSettleAuctionMarkSettledState evm)
        (.binary .eq (auctionMemField "bidder") zeroAddr) = .ok (.bool false) := by
  simp only [evalExpr?, evalExpr_settleAuction_mem_bidder_after_markSettled,
    evalExpr_settleAuction_zeroAddr_after_markSettled, EvalResult.bind, bind, evalBinaryOp?]
  have hbeq :
      (Value.address (AccountAddress.ofNat
          (auctionPackedBidderWord
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨211⟩)).toNat) ==
        Value.address (AccountAddress.ofNat 0)) = false := by
    rw [beq_eq_false_iff_ne]
    intro h
    rw [Value.address.injEq] at h
    exact hbidder h
  simp [hbeq]

theorem evalExpr_settleAuction_amount_positive_true_after_markSettled (evm : EVM.State)
    (hamount : 0 < (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨208⟩).toNat) :
    evalExpr? auctionConfig
        { contract := auctionContract, locals := auctionSettleAuctionSnapshotStore evm }
        (auctionSettleAuctionMarkSettledState evm)
        (.binary .gt (auctionMemField "amount") (.intLit 0)) = .ok (.bool true) := by
  simp only [evalExpr?, evalExpr_settleAuction_mem_amount_after_markSettled,
    EvalResult.bind, bind, pure, evalBinaryOp?]
  norm_num
  exact hamount

theorem evalExpr_settleAuction_amount_positive_false_after_markSettled (evm : EVM.State)
    (hamount : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨208⟩ = ⟨0⟩) :
    evalExpr? auctionConfig
        { contract := auctionContract, locals := auctionSettleAuctionSnapshotStore evm }
        (auctionSettleAuctionMarkSettledState evm)
        (.binary .gt (auctionMemField "amount") (.intLit 0)) = .ok (.bool false) := by
  simp only [evalExpr?, evalExpr_settleAuction_mem_amount_after_markSettled,
    EvalResult.bind, bind, pure, evalBinaryOp?]
  rw [hamount]
  rfl

theorem evalExprs_settleAuction_burn_args_after_markSettled (evm : EVM.State) :
    evalExprs? auctionConfig
        { contract := auctionContract, locals := auctionSettleAuctionSnapshotStore evm }
        (auctionSettleAuctionMarkSettledState evm) [auctionMemField "nounId"] =
      .ok [.int (Int.ofNat
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨207⟩).toNat)] := by
  simp [evalExprs?, evalExpr_settleAuction_mem_nounId_after_markSettled, EvalResult.bind, bind,
    pure]

theorem evalExprs_settleAuction_transferFrom_args_after_markSettled (evm : EVM.State) :
    evalExprs? auctionConfig
        { contract := auctionContract, locals := auctionSettleAuctionSnapshotStore evm }
        (auctionSettleAuctionMarkSettledState evm)
        [.env .this, auctionMemField "bidder", auctionMemField "nounId"] =
      .ok
        [.address evm.executionEnv.codeOwner,
          .address (AccountAddress.ofNat
            (auctionPackedBidderWord
              (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨211⟩)).toNat),
          .int (Int.ofNat
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨207⟩).toNat)] := by
  simp [evalExprs?, evalExpr_settleAuction_this_after_markSettled,
    evalExpr_settleAuction_mem_bidder_after_markSettled,
    evalExpr_settleAuction_mem_nounId_after_markSettled, EvalResult.bind, bind, pure]

theorem evalExprs_settleAuction_pay_args_after_markSettled (evm : EVM.State) :
    evalExprs? auctionConfig
        { contract := auctionContract, locals := auctionSettleAuctionSnapshotStore evm }
        (auctionSettleAuctionMarkSettledState evm) [.storage ownerRef, auctionMemField "amount"] =
      .ok
        [.address (AccountAddress.ofNat
          (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨151⟩)
            solcAddrMask).toNat),
        .int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨208⟩).toNat)] := by
  simp [evalExprs?, evalExpr_settleAuction_owner_after_markSettled,
    evalExpr_settleAuction_mem_amount_after_markSettled, EvalResult.bind, bind, pure]

theorem evalExpr_settleAuction_owner_after_callResult
    (evm evm' : EVM.State) {ret : Ident} (v : Value)
    (hne : (ret == "_owner") = false) :
    evalExpr? auctionConfig
        { contract := auctionContract,
          locals := (auctionSettleAuctionSnapshotStore evm).insert ret v }
        evm' (.storage ownerRef) =
      .ok (.address (AccountAddress.ofNat
        (UInt256.land (Solm.EVM.storageLoad evm' evm'.executionEnv.codeOwner ⟨151⟩)
          solcAddrMask).toNat)) := by
  have her : evalStorageRef auctionConfig
      { contract := auctionContract,
        locals := (auctionSettleAuctionSnapshotStore evm).insert ret v }
      evm' ownerRef = .ok { base := "_owner", steps := [] } := by
    simp [evalStorageRef, evalStorageRefSteps, ownerRef, EvalResult.bind, pure, bind]
  have hty : storageTypeAt? auctionContract.storage
      ({ base := "_owner", steps := [] } : EvaledStorageRef) = some (.elem .address) := by
    decide
  rw [evalExpr_storage_scalar (t := .address)
    (hbase := auctionSettleAuctionSnapshotStore_insert_base_owner evm v hne)
    (her := her) (hty := hty) (hloc := by rfl)]
  exact congrArg EvalResult.ok (by
    have hload := auctionStorageLocLoad_address_offset0 evm' ⟨151⟩
    simpa [auctionAddrLoc] using hload)

theorem evalExpr_settleAuction_mem_amount_after_callResult
    (evm evm' : EVM.State) {ret : Ident} (v : Value)
    (hne : (ret == "_auction") = false) :
    evalExpr? auctionConfig
        { contract := auctionContract,
          locals := (auctionSettleAuctionSnapshotStore evm).insert ret v }
        evm' (auctionMemField "amount") =
      .ok (.int (Int.ofNat
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨208⟩).toNat)) := by
  simp [auctionMemField, Solm.evalExpr?.eq_def,
    Std.HashMap.getElem_insert, hne,
    auctionSettleAuctionSnapshotStore, auctionSettleAuctionSnapshotValue,
    auctionSettleAuctionSnapshotFields, EvalResult.ofOption, lookupField?, lookupAssoc,
    EvalResult.bind, bind]

theorem evalExprs_settleAuction_pay_args_after_callResult
    (evm evm' : EVM.State) {ret : Ident} (v : Value)
    (hneAuction : (ret == "_auction") = false) (hneOwner : (ret == "_owner") = false) :
    evalExprs? auctionConfig
        { contract := auctionContract,
          locals := (auctionSettleAuctionSnapshotStore evm).insert ret v }
        evm' [.storage ownerRef, auctionMemField "amount"] =
      .ok
        [.address (AccountAddress.ofNat
          (UInt256.land (Solm.EVM.storageLoad evm' evm'.executionEnv.codeOwner ⟨151⟩)
            solcAddrMask).toNat),
        .int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨208⟩).toNat)] := by
  simp [evalExprs?, evalExpr_settleAuction_owner_after_callResult evm evm' v hneOwner,
    evalExpr_settleAuction_mem_amount_after_callResult evm evm' v hneAuction,
    EvalResult.bind, bind, pure]

theorem evalExpr_settleAuction_amount_positive_false_after_callResult
    (evm evm' : EVM.State) {ret : Ident} (v : Value)
    (hne : (ret == "_auction") = false)
    (hamount : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨208⟩ = ⟨0⟩) :
    evalExpr? auctionConfig
        { contract := auctionContract,
          locals := (auctionSettleAuctionSnapshotStore evm).insert ret v }
        evm' (.binary .gt (auctionMemField "amount") (.intLit 0)) = .ok (.bool false) := by
  simp only [evalExpr?, evalExpr_settleAuction_mem_amount_after_callResult evm evm' v hne,
    EvalResult.bind, bind, pure, evalBinaryOp?]
  rw [hamount]
  rfl

theorem evalExpr_settleAuction_amount_positive_true_after_callResult
    (evm evm' : EVM.State) {ret : Ident} (v : Value)
    (hne : (ret == "_auction") = false)
    (hamount : 0 < (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨208⟩).toNat) :
    evalExpr? auctionConfig
        { contract := auctionContract,
          locals := (auctionSettleAuctionSnapshotStore evm).insert ret v }
        evm' (.binary .gt (auctionMemField "amount") (.intLit 0)) = .ok (.bool true) := by
  simp only [evalExpr?, evalExpr_settleAuction_mem_amount_after_callResult evm evm' v hne,
    EvalResult.bind, bind, pure, evalBinaryOp?]
  norm_num
  exact hamount

theorem auctionExternalABI_decode_burn (out : ByteArray) :
    auctionConfig.externalABI.decode? "burn" out = some [] := by
  simp [auctionConfig, auctionExternalABI, isVoidExternal, decodeVoid?]

theorem auctionExternalABI_decode_transferFrom (out : ByteArray) :
    auctionConfig.externalABI.decode? "transferFrom" out = some [] := by
  simp [auctionConfig, auctionExternalABI, isVoidExternal, decodeVoid?]

theorem auctionLookupCallable_safeTransfer :
    lookupCallable? auctionContract "_safeTransferETHWithFallback" =
      some safeTransferETHWithFallback.toCallable := by
  rfl

end Auction
