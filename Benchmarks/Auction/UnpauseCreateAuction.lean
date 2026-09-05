import Benchmarks.Auction.AuctionGetter
import Benchmarks.Auction.Common
import Benchmarks.Auction.CreateAuction
import Benchmarks.Auction.Pause
import Reasoning.ExternalCall

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Auction

def auctionUnpauseMintSelectorWord : UInt256 :=
  UInt256.shiftLeft (UInt256.land (⟨0xffffffff⟩ : UInt256) ⟨0x1249c58b⟩) ⟨224⟩

noncomputable def auctionUnpauseMintSelMem (I : ExecutionEnv) : ByteArray :=
  (UInt256.toByteArray auctionUnpauseMintSelectorWord).write 0 (auctionEventMem I) 128 32

theorem auctionUnpauseMintSelMem_size (I : ExecutionEnv) :
    (auctionUnpauseMintSelMem I).size = 160 := by
  exact toByteArray_write32_size_of_le (base := auctionEventMem I)
    (word := auctionUnpauseMintSelectorWord) (off := 128) (baseSize := 160)
    (finalSize := 160) (auctionEventMem_size I) (by rw [auctionEventMem_size]; omega)
    (by omega)

theorem auctionUnpauseMintSelMem_read64 (I : ExecutionEnv) :
    (auctionUnpauseMintSelMem I).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  rw [auctionUnpauseMintSelMem]
  rw [write32_read_below _ _ 128 64 (by rw [toByteArray_size])
    (by rw [auctionEventMem_size]; omega) (by omega)]
  exact auctionEventMem_read64 I

theorem auctionUnpauseMintSelMem_mload64 (I : ExecutionEnv) :
    (if (⟨64⟩ : UInt256).toNat ≥ (auctionUnpauseMintSelMem I).size ∨
        (⟨64⟩ : UInt256) ≥ UInt256.ofNat 5 * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat
       (fromByteArrayBigEndian ((auctionUnpauseMintSelMem I).readWithPadding
        (⟨64⟩ : UInt256).toNat 32))) = ⟨128⟩ := by
  exact mloadFreePtrValue (by rw [auctionUnpauseMintSelMem_size]; decide) (by decide)
    (auctionUnpauseMintSelMem_read64 I)

theorem auctionUnpauseMintCallMem_read64 (I : ExecutionEnv) {o : ByteArray}
    (hosz : o.size < UInt256.size) :
    (o.write 0 (auctionUnpauseMintSelMem I) 128
        (min (⟨32⟩ : UInt256) (UInt256.ofNat o.size)).toNat).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  let len := (min (⟨32⟩ : UInt256) (UInt256.ofNat o.size)).toNat
  have hsrc : len ≤ o.size := by
    unfold len
    unfold min UInt256.instMin minOfLe
    by_cases hle : (⟨32⟩ : UInt256) ≤ UInt256.ofNat o.size
    · simp [hle]
      have hleNat : (⟨32⟩ : UInt256).toNat ≤ (UInt256.ofNat o.size).toNat := hle
      simpa [UInt256.toNat_ofNat_of_lt hosz] using hleNat
    · simp [hle, UInt256.toNat_ofNat_of_lt hosz]
  by_cases hlen : len = 0
  · simpa [len, hlen, byteArray_write_len_zero] using auctionUnpauseMintSelMem_read64 I
  · have hpres := write_read_below_gen_extend o (auctionUnpauseMintSelMem I) 128 len 64
      hlen hsrc (by rw [auctionUnpauseMintSelMem_size]; decide) (by decide)
    simpa [len] using hpres.trans (auctionUnpauseMintSelMem_read64 I)

theorem auctionUnpauseMintCallMem_size_gt64 (I : ExecutionEnv) {o : ByteArray}
    (hosz : o.size < UInt256.size) :
    64 <
      (o.write 0 (auctionUnpauseMintSelMem I) 128
        (min (⟨32⟩ : UInt256) (UInt256.ofNat o.size)).toNat).size := by
  let len := (min (⟨32⟩ : UInt256) (UInt256.ofNat o.size)).toNat
  have hsrc : len ≤ o.size := by
    unfold len
    unfold min UInt256.instMin minOfLe
    by_cases hle : (⟨32⟩ : UInt256) ≤ UInt256.ofNat o.size
    · simp [hle]
      have hleNat : (⟨32⟩ : UInt256).toNat ≤ (UInt256.ofNat o.size).toNat := hle
      simpa [UInt256.toNat_ofNat_of_lt hosz] using hleNat
    · simp [hle, UInt256.toNat_ofNat_of_lt hosz]
  have hlen32 : len ≤ 32 := by
    unfold len
    unfold min UInt256.instMin minOfLe
    by_cases hle : (⟨32⟩ : UInt256) ≤ UInt256.ofNat o.size
    · simp [hle]
      decide
    · simp [hle]
      have hnotNat : ¬ 32 ≤ (UInt256.ofNat o.size).toNat := by
        intro hnat
        exact hle hnat
      omega
  by_cases hlen : len = 0
  · simp [len, hlen, byteArray_write_len_zero, auctionUnpauseMintSelMem_size]
  · have hin : 128 + len ≤ (auctionUnpauseMintSelMem I).size := by
      rw [auctionUnpauseMintSelMem_size]
      omega
    rw [write_eq_gen o (auctionUnpauseMintSelMem I) 128 len hlen hsrc hin]
    rw [ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
      ByteArray.size_extract, auctionUnpauseMintSelMem_size]
    omega

theorem auctionUnpauseMintCallMem_mload64 (I : ExecutionEnv) {o : ByteArray}
    (hosz : o.size < UInt256.size) :
    (if (⟨64⟩ : UInt256).toNat ≥
          (o.write 0 (auctionUnpauseMintSelMem I) 128
            (min (⟨32⟩ : UInt256) (UInt256.ofNat o.size)).toNat).size ∨
        (⟨64⟩ : UInt256) ≥ UInt256.ofNat 5 * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat
       (fromByteArrayBigEndian
        ((o.write 0 (auctionUnpauseMintSelMem I) 128
          (min (⟨32⟩ : UInt256) (UInt256.ofNat o.size)).toNat).readWithPadding
          (⟨64⟩ : UInt256).toNat 32))) = ⟨128⟩ := by
  exact mloadFreePtrValue (by
      simpa using auctionUnpauseMintCallMem_size_gt64 I hosz)
    (by decide) (auctionUnpauseMintCallMem_read64 I hosz)

theorem auctionUnpauseMintCallCopyLen_eq32 {o : ByteArray}
    (ho32 : 32 ≤ o.size) (hosz : o.size < UInt256.size) :
    (min (⟨32⟩ : UInt256) (UInt256.ofNat o.size)).toNat = 32 := by
  unfold min UInt256.instMin minOfLe
  have hle : (⟨32⟩ : UInt256) ≤ UInt256.ofNat o.size := by
    change (⟨32⟩ : UInt256).toNat ≤ (UInt256.ofNat o.size).toNat
    simpa [UInt256.toNat_ofNat_of_lt hosz] using ho32
  change (if (⟨32⟩ : UInt256) ≤ UInt256.ofNat o.size then (⟨32⟩ : UInt256)
    else UInt256.ofNat o.size).toNat = 32
  rw [if_pos hle]
  decide

theorem auctionUnpauseMintCallMem_size_eq160 (I : ExecutionEnv) {o : ByteArray}
    (ho32 : 32 ≤ o.size) (hosz : o.size < UInt256.size) :
    (o.write 0 (auctionUnpauseMintSelMem I) 128
        (min (⟨32⟩ : UInt256) (UInt256.ofNat o.size)).toNat).size = 160 := by
  have hlen := auctionUnpauseMintCallCopyLen_eq32 (o := o) ho32 hosz
  rw [hlen]
  rw [write32_eq o (auctionUnpauseMintSelMem I) 128 ho32
    (by rw [auctionUnpauseMintSelMem_size]; decide)]
  have hpre : ((auctionUnpauseMintSelMem I).extract 0 128).size = 128 := by
    rw [ByteArray.size_extract, auctionUnpauseMintSelMem_size]
    omega
  have hsrc : (o.extract 0 32).size = 32 := by
    rw [ByteArray.size_extract]
    omega
  have hsuf :
      ((auctionUnpauseMintSelMem I).extract (128 + 32) (auctionUnpauseMintSelMem I).size).size =
        0 := by
    rw [ByteArray.size_extract, auctionUnpauseMintSelMem_size]
    omega
  rw [ByteArray.size_append, ByteArray.size_append, hpre, hsrc, hsuf]

theorem auctionUnpauseMintCallMem_read128 (I : ExecutionEnv) {o : ByteArray}
    (ho32 : 32 ≤ o.size) (hosz : o.size < UInt256.size) :
    (o.write 0 (auctionUnpauseMintSelMem I) 128
        (min (⟨32⟩ : UInt256) (UInt256.ofNat o.size)).toNat).readWithPadding 128 32 =
      o.extract 0 32 := by
  have hlen := auctionUnpauseMintCallCopyLen_eq32 (o := o) ho32 hosz
  rw [hlen]
  exact write32_read_back o (auctionUnpauseMintSelMem I) 128 ho32
    (by rw [auctionUnpauseMintSelMem_size]; decide)

theorem auctionUnpauseMintSelectorWord_prefix :
    (UInt256.toByteArray auctionUnpauseMintSelectorWord).extract 0 4 = mintSelector := by
  rw [auctionUnpauseMintSelectorWord, toByteArray_eq_toBytesBE]
  native_decide

theorem auctionUnpauseMintSelMem_read128_4 (I : ExecutionEnv) :
    (auctionUnpauseMintSelMem I).readWithPadding 128 4 = mintSelector := by
  rw [auctionUnpauseMintSelMem]
  rw [write32_read_prefix_len _ _ 128 4 (by rw [toByteArray_size])
    (by rw [auctionEventMem_size]; omega) (by omega) (by omega) (by omega)]
  exact auctionUnpauseMintSelectorWord_prefix

theorem auctionUnpauseMintEncode_eq (I : ExecutionEnv) :
    auctionConfig.externalABI.encode? "mint" [] =
      some ((auctionUnpauseMintSelMem I).readWithPadding 128 4) := by
  rw [auctionUnpauseMintSelMem_read128_4]
  exact auctionExternalABI_encode_mint

def auctionMintTargetWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.land solcAddrMask (auctionSlotWord ⟨201⟩ σ I)

theorem auctionMintTarget_eq (w : UInt256) :
    EVM.address (AccountAddress.ofNat ((UInt256.land w solcAddrMask).toNat)) =
      AccountAddress.ofUInt256 (UInt256.land solcAddrMask w) := by
  rw [u256_land_comm]
  congr

theorem auctionUnpauseAssign (evm : EVM.State) :
    assignStorageRef? auctionConfig { contract := auctionContract, locals := ∅ } evm .storage
        pausedRef (.bool false) =
      .ok ({ contract := auctionContract, locals := ∅ }, auctionUnpausePostState evm) := by
  have her : evalStorageRef auctionConfig { contract := auctionContract, locals := ∅ } evm
      pausedRef = .ok { base := "_paused", steps := [] } := by
    simp [evalStorageRef, evalStorageRefSteps, pausedRef, EvalResult.bind, pure, bind]
  have hty : storageTypeAt? auctionContract.storage
      ({ base := "_paused", steps := [] } : EvaledStorageRef) = some (.elem .bool) := by
    decide
  have hstore :
      storageLocStore evm (auctionBoolLoc ⟨51⟩) (.bool false) =
        some (auctionUnpausePostState evm) := by
    simpa [auctionBoolLoc, boolOffset0Loc, auctionUnpausePostState, auctionPausedSetFalseWord,
      setBoolOffset0Word] using
      auctionStorageLocStore_bool_false_offset0 evm ⟨51⟩
  exact assignStorageRef_storage_scalar_value (cfg := auctionConfig)
    (solm := { contract := auctionContract, locals := ∅ }) (evm := evm)
    (evm' := auctionUnpausePostState evm) (slot := pausedRef)
    (er := { base := "_paused", steps := [] }) (ty := .elem .bool)
    (loc := auctionBoolLoc ⟨51⟩) (value := .bool false) (by simp) her hty (by rfl)
    (by trivial) hstore

theorem evalExpr_unpause_false (evm : EVM.State) :
    evalExpr? auctionConfig { contract := auctionContract, locals := ∅ } evm (.boolLit false) =
      .ok (.bool false) := by
  simp [evalExpr?, pure]

theorem evalExpr_unpause_start (evm : EVM.State) :
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
    simp [storageTypeAt?, storageTypeStep?, auctionContract, storageDecls,
      auctionStructTy, uint256St]
  have hloc : auctionConfig.storage.layout
      ({ base := "auction", steps := [.field "startTime"] } : EvaledStorageRef) =
      fun _ => some (auctionUint256Loc ⟨209⟩) := by
    funext evm'
    simp [auctionConfig, auctionStorageLayout]
  rw [evalExpr_storage_scalar (t := .int uint256Int) (hbase := hbase)
    (her := her) (hty := hty) (hloc := hloc)]
  exact congrArg EvalResult.ok (by simpa using auctionStorageLocLoad_uint256 evm ⟨209⟩)

theorem evalExpr_unpause_start_eq_zero_false (evm : EVM.State)
    (hstart : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨209⟩ ≠ ⟨0⟩) :
    evalExpr? auctionConfig { contract := auctionContract, locals := ∅ } evm
      (.binary .eq (.storage (aField "startTime")) (.intLit 0)) = .ok (.bool false) := by
  simp only [evalExpr?, evalExpr_unpause_start, EvalResult.bind, bind, pure, evalBinaryOp?]
  have hbeq :
      (Value.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨209⟩).toNat) ==
        Value.int 0) = false := by
    rw [beq_eq_false_iff_ne]
    intro h
    rw [Value.int.injEq] at h
    exact hstart (uint256_toNat_eq_zero (Int.ofNat.inj h))
  rw [hbeq]

theorem evalExpr_unpause_start_eq_zero_true (evm : EVM.State)
    (hstart : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨209⟩ = ⟨0⟩) :
    evalExpr? auctionConfig { contract := auctionContract, locals := ∅ } evm
      (.binary .eq (.storage (aField "startTime")) (.intLit 0)) = .ok (.bool true) := by
  simp only [evalExpr?, evalExpr_unpause_start, EvalResult.bind, bind, pure, evalBinaryOp?]
  rw [hstart]
  rfl

theorem evalExpr_unpause_settled (evm : EVM.State) :
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

theorem evalExpr_unpause_settled_false (evm : EVM.State)
    (hsettled : auctionPackedSettledWord
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨211⟩) = ⟨0⟩) :
    evalExpr? auctionConfig { contract := auctionContract, locals := ∅ } evm
      (.storage (aField "settled")) = .ok (.bool false) := by
  rw [evalExpr_unpause_settled]
  simp [wordToElem, hsettled]

theorem evalExpr_unpause_settled_true (evm : EVM.State)
    (hsettled : auctionPackedSettledWord
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨211⟩) ≠ ⟨0⟩) :
    evalExpr? auctionConfig { contract := auctionContract, locals := ∅ } evm
      (.storage (aField "settled")) = .ok (.bool true) := by
  rw [evalExpr_unpause_settled]
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

theorem evalExpr_unpause_createCond_false (evm : EVM.State)
    (hstart : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨209⟩ ≠ ⟨0⟩)
    (hsettled : auctionPackedSettledWord
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨211⟩) = ⟨0⟩) :
    evalExpr? auctionConfig { contract := auctionContract, locals := ∅ } evm
      (.binary .or (.binary .eq (.storage (aField "startTime")) (.intLit 0))
        (.storage (aField "settled"))) = .ok (.bool false) := by
  simp [evalExpr?, EvalResult.bind, bind, pure,
    evalExpr_unpause_start_eq_zero_false evm hstart,
    evalExpr_unpause_settled_false evm hsettled]

theorem evalExpr_unpause_createCond_true_start (evm : EVM.State)
    (hstart : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨209⟩ = ⟨0⟩) :
    evalExpr? auctionConfig { contract := auctionContract, locals := ∅ } evm
      (.binary .or (.binary .eq (.storage (aField "startTime")) (.intLit 0))
        (.storage (aField "settled"))) = .ok (.bool true) := by
  simp [evalExpr?, EvalResult.bind, bind, pure,
    evalExpr_unpause_start_eq_zero_true evm hstart]

theorem evalExpr_unpause_createCond_true_settled (evm : EVM.State)
    (hstart : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨209⟩ ≠ ⟨0⟩)
    (hsettled : auctionPackedSettledWord
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨211⟩) ≠ ⟨0⟩) :
    evalExpr? auctionConfig { contract := auctionContract, locals := ∅ } evm
      (.binary .or (.binary .eq (.storage (aField "startTime")) (.intLit 0))
        (.storage (aField "settled"))) = .ok (.bool true) := by
  simp [evalExpr?, EvalResult.bind, bind, pure,
    evalExpr_unpause_start_eq_zero_false evm hstart,
    evalExpr_unpause_settled_true evm hsettled]

theorem auctionUnpausePostState_storageLoad_ne_paused (evm : EVM.State) {slot : UInt256}
    (hne : slot ≠ ⟨51⟩) :
    Solm.EVM.storageLoad (auctionUnpausePostState evm)
        (auctionUnpausePostState evm).executionEnv.codeOwner slot =
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot := by
  have hload : Solm.EVM.storageLoad (auctionUnpausePostState evm) evm.executionEnv.codeOwner slot =
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot := by
    simpa [auctionUnpausePostState] using
      storageLoad_storageStore_ne evm evm.executionEnv.codeOwner
        (readSlot := slot) (writeSlot := ⟨51⟩)
        (val := auctionPausedSetFalseWord
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨51⟩)) hne
  have henv : (auctionUnpausePostState evm).executionEnv = evm.executionEnv := by
    simpa [auctionUnpausePostState] using
      storageStore_executionEnv evm evm.executionEnv.codeOwner ⟨51⟩
        (auctionPausedSetFalseWord
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨51⟩))
  simpa [henv] using hload

theorem evalExpr_unpausePost_createCond_true_start (evm : EVM.State)
    (hstart : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨209⟩ = ⟨0⟩) :
    evalExpr? auctionConfig { contract := auctionContract, locals := ∅ }
        (auctionUnpausePostState evm)
        (.binary .or (.binary .eq (.storage (aField "startTime")) (.intLit 0))
          (.storage (aField "settled"))) =
      .ok (.bool true) := by
  apply evalExpr_unpause_createCond_true_start
  rw [auctionUnpausePostState_storageLoad_ne_paused evm
    (by decide : (⟨209⟩ : UInt256) ≠ (⟨51⟩ : UInt256))]
  exact hstart

theorem evalExpr_unpausePost_createCond_true_settled (evm : EVM.State)
    (hstart : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨209⟩ ≠ ⟨0⟩)
    (hsettled : auctionPackedSettledWord
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨211⟩) ≠ ⟨0⟩) :
    evalExpr? auctionConfig { contract := auctionContract, locals := ∅ }
        (auctionUnpausePostState evm)
        (.binary .or (.binary .eq (.storage (aField "startTime")) (.intLit 0))
          (.storage (aField "settled"))) =
      .ok (.bool true) := by
  apply evalExpr_unpause_createCond_true_settled
  · rw [auctionUnpausePostState_storageLoad_ne_paused evm
      (by decide : (⟨209⟩ : UInt256) ≠ (⟨51⟩ : UInt256))]
    exact hstart
  · rw [auctionUnpausePostState_storageLoad_ne_paused evm
      (by decide : (⟨211⟩ : UInt256) ≠ (⟨51⟩ : UInt256))]
    exact hsettled

theorem evalExpr_unpausePost_createCond_true_of_not_noCreate {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : Sat256}
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hnoCreate :
      ¬ (auctionSlotWord ⟨209⟩ σ_evm I ≠ ⟨0⟩ ∧
        auctionPackedSettledWord (auctionSlotWord ⟨211⟩ σ_evm I) = ⟨0⟩)) :
    evalExpr? auctionConfig { contract := auctionContract, locals := ∅ }
        (auctionUnpausePostState (initState cA gh bl σ_solm σ₀ g A I))
        (.binary .or (.binary .eq (.storage (aField "startTime")) (.intLit 0))
          (.storage (aField "settled"))) =
      .ok (.bool true) := by
  let evmS := initState cA gh bl σ_solm σ₀ g A I
  have hstartWord :
      auctionSlotWord ⟨209⟩ σ_evm I = auctionSlotWord ⟨209⟩ σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨209⟩ ⟨0⟩
  have hsettledWord :
      auctionSlotWord ⟨211⟩ σ_evm I = auctionSlotWord ⟨211⟩ σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨211⟩ ⟨0⟩
  by_cases hstartZero : auctionSlotWord ⟨209⟩ σ_evm I = ⟨0⟩
  · have hstartSolm :
        Solm.EVM.storageLoad evmS evmS.executionEnv.codeOwner ⟨209⟩ = ⟨0⟩ := by
      have hmap : auctionSlotWord ⟨209⟩ σ_solm I = ⟨0⟩ := by
        simpa [hstartWord] using hstartZero
      simpa [evmS, initState, auctionSlotWord, Solm.EVM.storageLoad, State.lookupAccount]
        using hmap
    simpa [evmS] using evalExpr_unpausePost_createCond_true_start evmS hstartSolm
  · have hsettledNe :
        auctionPackedSettledWord (auctionSlotWord ⟨211⟩ σ_evm I) ≠ ⟨0⟩ := by
      intro hsettled
      exact hnoCreate ⟨hstartZero, hsettled⟩
    have hstartSolm :
        Solm.EVM.storageLoad evmS evmS.executionEnv.codeOwner ⟨209⟩ ≠ ⟨0⟩ := by
      intro hs
      apply hstartZero
      have hmap : auctionSlotWord ⟨209⟩ σ_solm I = ⟨0⟩ := by
        simpa [evmS, initState, auctionSlotWord, Solm.EVM.storageLoad, State.lookupAccount]
          using hs
      simpa [hstartWord] using hmap
    have hsettledSolm :
        auctionPackedSettledWord
            (Solm.EVM.storageLoad evmS evmS.executionEnv.codeOwner ⟨211⟩) ≠ ⟨0⟩ := by
      intro hs
      apply hsettledNe
      have hmap : auctionPackedSettledWord (auctionSlotWord ⟨211⟩ σ_solm I) = ⟨0⟩ := by
        simpa [evmS, initState, auctionSlotWord, Solm.EVM.storageLoad, State.lookupAccount]
          using hs
      simpa [hsettledWord] using hmap
    simpa [evmS] using
      evalExpr_unpausePost_createCond_true_settled evmS hstartSolm hsettledSolm

theorem auctionUnpauseBodyReturns_noCreate (evm : EVM.State)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (howner :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨151⟩) solcAddrMask =
        auctionSourceWord evm.executionEnv)
    (hpaused :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨51⟩) ⟨255⟩ ≠
        ⟨0⟩)
    (hstart : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨209⟩ ≠ ⟨0⟩)
    (hsettled : auctionPackedSettledWord
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨211⟩) = ⟨0⟩) :
    ExecTransitionBody auctionConfig auctionContract evm ∅ unpauseTransition.body
      (.returned { contract := auctionContract, locals := ∅ } (auctionUnpausePostState evm) none) := by
  let evm' := auctionUnpausePostState evm
  have hstartPost : Solm.EVM.storageLoad evm' evm'.executionEnv.codeOwner ⟨209⟩ ≠ ⟨0⟩ := by
    intro h
    apply hstart
    have hload : Solm.EVM.storageLoad evm' evm.executionEnv.codeOwner ⟨209⟩ =
        Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨209⟩ := by
      simpa [evm', auctionUnpausePostState] using
        storageLoad_storageStore_ne evm evm.executionEnv.codeOwner
          (readSlot := ⟨209⟩) (writeSlot := ⟨51⟩)
          (val := auctionPausedSetFalseWord
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨51⟩)) (by decide)
    have henv : evm'.executionEnv = evm.executionEnv := by
      simpa [evm', auctionUnpausePostState] using
        storageStore_executionEnv evm evm.executionEnv.codeOwner ⟨51⟩
          (auctionPausedSetFalseWord
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨51⟩))
    have h' : Solm.EVM.storageLoad evm' evm.executionEnv.codeOwner ⟨209⟩ = ⟨0⟩ := by
      simpa [henv] using h
    exact hload.symm.trans h'
  have hsettledPost : auctionPackedSettledWord
        (Solm.EVM.storageLoad evm' evm'.executionEnv.codeOwner ⟨211⟩) = ⟨0⟩ := by
    have hload : Solm.EVM.storageLoad evm' evm.executionEnv.codeOwner ⟨211⟩ =
        Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨211⟩ := by
      simpa [evm', auctionUnpausePostState] using
        storageLoad_storageStore_ne evm evm.executionEnv.codeOwner
          (readSlot := ⟨211⟩) (writeSlot := ⟨51⟩)
          (val := auctionPausedSetFalseWord
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨51⟩)) (by decide)
    have henv : evm'.executionEnv = evm.executionEnv := by
      simpa [evm', auctionUnpausePostState] using
        storageStore_executionEnv evm evm.executionEnv.codeOwner ⟨51⟩
          (auctionPausedSetFalseWord
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨51⟩))
    have hload' : Solm.EVM.storageLoad evm' evm'.executionEnv.codeOwner ⟨211⟩ =
        Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨211⟩ := by
      simpa [henv] using hload
    rw [hload']
    exact hsettled
  refine ExecFuncBody.execBlockOK ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalExpr_pause_owner_eq_true evm howner)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalExpr_pause_paused_true evm hpaused)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_unpause_false evm) (auctionUnpauseAssign evm)) ?_
  exact ExecBlock.consNormal
    (ExecStmt.iteFalse (evalExpr_unpause_createCond_false evm' hstartPost hsettledPost)
      ExecBlock.nil) ExecBlock.nil

theorem auctionUnpauseBodyReturns_create_success (evm evmCall : EVM.State) {out : ByteArray}
    {nounId : UInt256}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (howner :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨151⟩) solcAddrMask =
        auctionSourceWord evm.executionEnv)
    (hpaused :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨51⟩) ⟨255⟩ ≠
        ⟨0⟩)
    (hcond :
      evalExpr? auctionConfig { contract := auctionContract, locals := ∅ } (auctionUnpausePostState evm)
        (.binary .or (.binary .eq (.storage (aField "startTime")) (.intLit 0))
          (.storage (aField "settled"))) = .ok (.bool true))
    (hcall : typedCallViaEVM auctionConfig (auctionUnpausePostState evm)
      (EVM.address (AccountAddress.ofNat
        ((UInt256.land
          (Solm.EVM.storageLoad (auctionUnpausePostState evm)
            (auctionUnpausePostState evm).executionEnv.codeOwner ⟨201⟩)
          solcAddrMask).toNat))) "mint" 0 [] (true, evmCall, out) true)
    (hdec : ABI.decodeReturnValue? uint256 out = some (.int (Int.ofNat nounId.toNat)))
    (hadd : (auctionCreateAuctionStartWord evmCall).toNat +
        (auctionCreateAuctionDurationWord evmCall).toNat < UInt256.size) :
    ExecTransitionBody auctionConfig auctionContract evm ∅ unpauseTransition.body
      (.returned (resumeAfterInternalCall { contract := auctionContract, locals := ∅ } "_c" none)
        (auctionCreateAuctionSourceSuccessPostState evmCall nounId) none) := by
  let evm' := auctionUnpausePostState evm
  refine ExecFuncBody.execBlockOK ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalExpr_pause_owner_eq_true evm howner)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalExpr_pause_paused_true evm hpaused)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_unpause_false evm) (auctionUnpauseAssign evm)) ?_
  refine ExecBlock.consNormal (ExecStmt.iteTrue (by simpa [evm'] using hcond) ?_) ExecBlock.nil
  refine ExecBlock.consNormal ?_ ExecBlock.nil
  exact internalCallFunctionReturn
    (cfg := auctionConfig) (caller := { contract := auctionContract, locals := ∅ })
    (evm := evm') (calleeEvm := auctionCreateAuctionSourceSuccessPostState evmCall nounId)
    (name := "_createAuction") (args := []) (retVar := "_c") (argVals := [])
    (callee := createAuctionFn) (locals := ∅)
      (calleeSolm :=
        ({ contract := auctionContract,
           locals := auctionCreateAuctionAfterEndStore nounId evmCall } : Frame))
      (value := none) (by rfl) (by rfl) (by rfl)
      (auctionCreateAuctionBodyReturns_success hcall hdec hadd)

theorem evalExpr_createAuction_endTime_expr_revert (evm : EVM.State) (nounId : UInt256)
    (hover : UInt256.size ≤ (auctionCreateAuctionStartWord evm).toNat +
        (auctionCreateAuctionDurationWord evm).toNat) :
    evalExpr? auctionConfig
        { contract := auctionContract, locals := auctionCreateAuctionAfterStartStore nounId evm }
        evm (u256 (.binary .add (.var "startTime") (.storage durationRef))) = .revert := by
  have hdurationBase : (auctionCreateAuctionAfterStartStore nounId evm).get? "duration" = none := by
    rw [auctionCreateAuctionAfterStartStore, auctionCreateAuctionAfterMintStore]
    repeat rw [store_get_ne _ _ (by decide)]
    simp
  simp only [u256, evalExpr?, auctionCreateAuctionAfterStartStore_startTime,
    evalExpr_createAuction_duration evm (auctionCreateAuctionAfterStartStore nounId evm)
      hdurationBase,
    EvalResult.bind, bind, pure, evalBinaryOp?]
  simp [uint256Int]
  have hge : ¬ Int.ofNat ((auctionCreateAuctionStartWord evm).toNat +
        (auctionCreateAuctionDurationWord evm).toNat) < Int.ofNat (2 ^ 256) := by
    rw [not_lt]
    exact Int.ofNat_le.mpr (by simpa [UInt256.size] using hover)
  simp [EvalResult.ofOption, uint256Int, evalBinaryOp?]
  intro _
  exact Int.ofNat_le.mpr (by simpa [UInt256.size] using hover)

theorem auctionCreateAuctionSuccessBlockReverts_addOverflow (evm : EVM.State)
    (nounId : UInt256)
    (hover : UInt256.size ≤ (auctionCreateAuctionStartWord evm).toNat +
        (auctionCreateAuctionDurationWord evm).toNat) :
    ExecBlock auctionConfig
      { contract := auctionContract, locals := auctionCreateAuctionAfterMintStore nounId } evm
      [ .letDecl "startTime" (some uint256) now,
        .letDecl "endTime" (some uint256)
          (u256 (.binary .add (.var "startTime") (.storage durationRef))),
        .assign .storage (aField "nounId") (.var "nounId"),
        .assign .storage (aField "amount") (.intLit 0),
        .assign .storage (aField "startTime") (.var "startTime"),
        .assign .storage (aField "endTime") (.var "endTime"),
        .assign .storage (aField "bidder") zeroAddr,
        .assign .storage (aField "settled") (.boolLit false) ] .reverted := by
  refine ExecBlock.consNormal
    (ExecStmt.letDecl (evalExpr_createAuction_now evm (auctionCreateAuctionAfterMintStore nounId))) ?_
  exact ExecBlock.consRevert
    (ExecStmt.letDeclRevert (evalExpr_createAuction_endTime_expr_revert evm nounId hover))

theorem auctionCreateAuctionBodyReverts_addOverflow {evm evmCall : EVM.State}
    {out : ByteArray} {nounId : UInt256}
    (hcall : typedCallViaEVM auctionConfig evm
      (EVM.address (AccountAddress.ofNat
        ((UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨201⟩)
          solcAddrMask).toNat))) "mint" 0 [] (true, evmCall, out) true)
    (hdec : ABI.decodeReturnValue? uint256 out = some (.int (Int.ofNat nounId.toNat)))
    (hover : UInt256.size ≤ (auctionCreateAuctionStartWord evmCall).toNat +
        (auctionCreateAuctionDurationWord evmCall).toNat) :
    ExecFuncBody auctionConfig { contract := auctionContract, locals := ∅ } evm createAuctionFn.body
      .reverted := by
  dsimp [createAuctionFn]
  refine ExecFuncBody.execBlockRevert ?_
  refine ExecBlock.consRevert ?_
  refine ExecStmt.checkedCallSuccess (evalExpr_createAuction_nouns evm)
    (evalExpr_createAuction_zero evm) (evalExprs_createAuction_mint_args evm) hcall
    (auctionExternalABI_decode_mint hdec) ?_
  simpa [auctionCreateAuctionAfterMintStore, collapseReturns] using
    auctionCreateAuctionSuccessBlockReverts_addOverflow evmCall nounId hover

theorem auctionUnpauseBodyReverts_create_addOverflow (evm evmCall : EVM.State)
    {out : ByteArray} {nounId : UInt256}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (howner :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨151⟩) solcAddrMask =
        auctionSourceWord evm.executionEnv)
    (hpaused :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨51⟩) ⟨255⟩ ≠
        ⟨0⟩)
    (hcond :
      evalExpr? auctionConfig { contract := auctionContract, locals := ∅ } (auctionUnpausePostState evm)
        (.binary .or (.binary .eq (.storage (aField "startTime")) (.intLit 0))
          (.storage (aField "settled"))) = .ok (.bool true))
    (hcall : typedCallViaEVM auctionConfig (auctionUnpausePostState evm)
      (EVM.address (AccountAddress.ofNat
        ((UInt256.land
          (Solm.EVM.storageLoad (auctionUnpausePostState evm)
            (auctionUnpausePostState evm).executionEnv.codeOwner ⟨201⟩)
          solcAddrMask).toNat))) "mint" 0 [] (true, evmCall, out) true)
    (hdec : ABI.decodeReturnValue? uint256 out = some (.int (Int.ofNat nounId.toNat)))
    (hover : UInt256.size ≤ (auctionCreateAuctionStartWord evmCall).toNat +
        (auctionCreateAuctionDurationWord evmCall).toNat) :
    ExecTransitionBody auctionConfig auctionContract evm ∅ unpauseTransition.body .reverted := by
  let evm' := auctionUnpausePostState evm
  refine ExecFuncBody.execBlockRevert ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalExpr_pause_owner_eq_true evm howner)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalExpr_pause_paused_true evm hpaused)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_unpause_false evm) (auctionUnpauseAssign evm)) ?_
  refine ExecBlock.consRevert (ExecStmt.iteTrue (by simpa [evm'] using hcond) ?_)
  exact ExecBlock.consRevert (internalCallFunctionRevert
    (cfg := auctionConfig) (caller := { contract := auctionContract, locals := ∅ })
    (evm := evm') (name := "_createAuction") (args := []) (retVar := "_c")
    (argVals := []) (callee := createAuctionFn) (locals := ∅)
    (by rfl) (by rfl) (by rfl)
    (auctionCreateAuctionBodyReverts_addOverflow hcall hdec hover))

theorem auctionExternalABI_decode_mint_none {out : ByteArray}
    (hdec : ABI.decodeReturnValue? uint256 out = none) :
    auctionConfig.externalABI.decode? "mint" out = none := by
  simpa [auctionConfig, auctionExternalABI, decodeReturn?] using hdec

theorem auctionCreateAuctionBodyReverts_decodeFailure {evm evmCall : EVM.State}
    {out : ByteArray}
    (hcall : typedCallViaEVM auctionConfig evm
      (EVM.address (AccountAddress.ofNat
        ((UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨201⟩)
          solcAddrMask).toNat))) "mint" 0 [] (true, evmCall, out) true)
    (hdec : ABI.decodeReturnValue? uint256 out = none) :
    ExecFuncBody auctionConfig { contract := auctionContract, locals := ∅ } evm createAuctionFn.body
      .reverted := by
  dsimp [createAuctionFn]
  refine ExecFuncBody.execBlockRevert ?_
  refine ExecBlock.consRevert ?_
  exact ExecStmt.checkedCallReturnDecodeRevert (evalExpr_createAuction_nouns evm)
    (evalExpr_createAuction_zero evm) (evalExprs_createAuction_mint_args evm) hcall
    (auctionExternalABI_decode_mint_none hdec)

theorem auctionUnpauseBodyReverts_create_decodeFailure (evm evmCall : EVM.State)
    {out : ByteArray}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (howner :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨151⟩) solcAddrMask =
        auctionSourceWord evm.executionEnv)
    (hpaused :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨51⟩) ⟨255⟩ ≠
        ⟨0⟩)
    (hcond :
      evalExpr? auctionConfig { contract := auctionContract, locals := ∅ } (auctionUnpausePostState evm)
        (.binary .or (.binary .eq (.storage (aField "startTime")) (.intLit 0))
          (.storage (aField "settled"))) = .ok (.bool true))
    (hcall : typedCallViaEVM auctionConfig (auctionUnpausePostState evm)
      (EVM.address (AccountAddress.ofNat
        ((UInt256.land
          (Solm.EVM.storageLoad (auctionUnpausePostState evm)
            (auctionUnpausePostState evm).executionEnv.codeOwner ⟨201⟩)
          solcAddrMask).toNat))) "mint" 0 [] (true, evmCall, out) true)
    (hdec : ABI.decodeReturnValue? uint256 out = none) :
    ExecTransitionBody auctionConfig auctionContract evm ∅ unpauseTransition.body .reverted := by
  let evm' := auctionUnpausePostState evm
  refine ExecFuncBody.execBlockRevert ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalExpr_pause_owner_eq_true evm howner)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalExpr_pause_paused_true evm hpaused)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_unpause_false evm) (auctionUnpauseAssign evm)) ?_
  refine ExecBlock.consRevert (ExecStmt.iteTrue (by simpa [evm'] using hcond) ?_)
  exact ExecBlock.consRevert (internalCallFunctionRevert
    (cfg := auctionConfig) (caller := { contract := auctionContract, locals := ∅ })
    (evm := evm') (name := "_createAuction") (args := []) (retVar := "_c")
    (argVals := []) (callee := createAuctionFn) (locals := ∅)
    (by rfl) (by rfl) (by rfl)
    (auctionCreateAuctionBodyReverts_decodeFailure hcall hdec))

theorem evalExpr_createAuction_emptyErr_slice_revert (evm : EVM.State) :
    evalExpr? auctionConfig
      { contract := auctionContract, locals := (∅ : Store).insert "err" (.bytes ByteArray.empty) }
      evm
      (.binary .eq (.bytesSlice (.var "err") (.intLit 0) (.intLit 4))
        (.bytesLit errorStringSelector)) = .revert := by
  simp [evalExpr?, EvalResult.bind, bind, pure]
  native_decide

theorem evalExpr_createAuction_err_selector_slice_revert (evm : EVM.State) {out : ByteArray}
    (hshort : out.size < 4) :
    evalExpr? auctionConfig
      { contract := auctionContract, locals := (∅ : Store).insert "err" (.bytes out) }
      evm (.bytesSlice (.var "err") (.intLit 0) (.intLit 4)) = .revert := by
  have hshortInt : (out.size : Int) < 4 := by exact_mod_cast hshort
  simp only [evalExpr?, bind, EvalResult.bind, EvalResult.ofOption,
    Std.HashMap.get?_eq_getElem?, Std.HashMap.mem_insert, BEq.rfl,
    Std.HashMap.not_mem_empty, or_false, getElem?_pos, Std.HashMap.getElem_insert_self,
    sliceBytes?, Bool.or_eq_true, decide_eq_true_eq, gt_iff_lt, Int.lt_toNat,
    Int.ofNat_toNat, sup_lt_iff, Bool.decide_and, Bool.and_eq_true]
  norm_num [hshortInt]

theorem evalExpr_createAuction_err_selector_slice_ok (evm : EVM.State) {out : ByteArray}
    (hlen : 4 ≤ out.size) :
    evalExpr? auctionConfig
      { contract := auctionContract, locals := (∅ : Store).insert "err" (.bytes out) }
      evm (.bytesSlice (.var "err") (.intLit 0) (.intLit 4)) =
        .ok (.bytes (out.extract 0 4)) := by
  have hlenInt : ¬ (out.size : Int) < 4 := by omega
  simp only [evalExpr?, bind, EvalResult.bind, EvalResult.ofOption,
    Std.HashMap.get?_eq_getElem?, Std.HashMap.mem_insert, BEq.rfl,
    Std.HashMap.not_mem_empty, or_false, getElem?_pos, Std.HashMap.getElem_insert_self,
    sliceBytes?, Bool.or_eq_true, decide_eq_true_eq, gt_iff_lt, Int.lt_toNat,
    Int.ofNat_toNat, sup_lt_iff, Bool.decide_and, Bool.and_eq_true]
  norm_num [hlenInt]
  rfl

theorem evalExpr_createAuction_err_slice_revert (evm : EVM.State) {out : ByteArray}
    (hshort : out.size < 4) :
    evalExpr? auctionConfig
      { contract := auctionContract, locals := (∅ : Store).insert "err" (.bytes out) }
      evm
      (.binary .eq (.bytesSlice (.var "err") (.intLit 0) (.intLit 4))
        (.bytesLit errorStringSelector)) = .revert := by
  simp only [evalExpr?, bind, EvalResult.bind,
    evalExpr_createAuction_err_selector_slice_revert evm hshort]

theorem evalExpr_createAuction_err_slice_false (evm : EVM.State) {out : ByteArray}
    (hlen : 4 ≤ out.size) (hsel : out.extract 0 4 ≠ errorStringSelector) :
    evalExpr? auctionConfig
      { contract := auctionContract, locals := (∅ : Store).insert "err" (.bytes out) }
      evm
      (.binary .eq (.bytesSlice (.var "err") (.intLit 0) (.intLit 4))
        (.bytesLit errorStringSelector)) = .ok (.bool false) := by
  simp only [evalExpr?, bind, EvalResult.bind,
    evalExpr_createAuction_err_selector_slice_ok evm hlen]
  simp only [evalBinaryOp?]
  simpa using hsel

theorem evalExpr_createAuction_err_slice_true (evm : EVM.State) {out : ByteArray}
    (hlen : 4 ≤ out.size) (hsel : out.extract 0 4 = errorStringSelector) :
    evalExpr? auctionConfig
      { contract := auctionContract, locals := (∅ : Store).insert "err" (.bytes out) }
      evm
      (.binary .eq (.bytesSlice (.var "err") (.intLit 0) (.intLit 4))
        (.bytesLit errorStringSelector)) = .ok (.bool true) := by
  simp only [evalExpr?, bind, EvalResult.bind,
    evalExpr_createAuction_err_selector_slice_ok evm hlen]
  simp only [evalBinaryOp?]
  simp [hsel]

theorem evalExpr_createAuction_error_payload_ok (evm : EVM.State) {out : ByteArray}
    (hlen : 4 ≤ out.size) :
    evalExpr? auctionConfig
      { contract := auctionContract, locals := (∅ : Store).insert "err" (.bytes out) }
      evm (errorStringPayload "err") = .ok (.bytes (out.extract 4 out.size)) := by
  have hlenInt : ¬ (out.size : Int) < 4 := by omega
  simp only [errorStringPayload, localBytesLength, evalExpr?, bind, EvalResult.bind,
    EvalResult.ofOption, Std.HashMap.get?_eq_getElem?, Std.HashMap.mem_insert, BEq.rfl,
    Std.HashMap.not_mem_empty, or_false, getElem?_pos, Std.HashMap.getElem_insert_self,
    readLocalPath?, pure, sliceBytes?, Bool.or_eq_true, decide_eq_true_eq, gt_iff_lt,
    Int.lt_toNat, Int.ofNat_toNat, sup_lt_iff, Bool.decide_and, Bool.and_eq_true]
  norm_num [hlenInt]
  rfl

theorem evalExpr_createAuction_error_decode_ok (evm : EVM.State) {out : ByteArray}
    {decoded : Value} (hlen : 4 ≤ out.size)
    (hdec : ABI.decodeReturnValue? .string (out.extract 4 out.size) = some decoded) :
    evalExpr? auctionConfig
      { contract := auctionContract, locals := (∅ : Store).insert "err" (.bytes out) }
      evm (.abiDecode .string (errorStringPayload "err")) = .ok decoded := by
  rw [evalExpr?]
  rw [evalExpr_createAuction_error_payload_ok evm hlen]
  simp [EvalResult.bind, bind, pure, auctionConfig, ABI.decodeReturnValueWithMode?, hdec]

theorem evalExpr_createAuction_error_decode_revert (evm : EVM.State) {out : ByteArray}
    (hlen : 4 ≤ out.size)
    (hdec : ABI.decodeReturnValue? .string (out.extract 4 out.size) = none) :
    evalExpr? auctionConfig
      { contract := auctionContract, locals := (∅ : Store).insert "err" (.bytes out) }
      evm (.abiDecode .string (errorStringPayload "err")) = .revert := by
  rw [evalExpr?]
  rw [evalExpr_createAuction_error_payload_ok evm hlen]
  simp [EvalResult.bind, bind, pure, auctionConfig, ABI.decodeReturnValueWithMode?, hdec]

theorem evalExpr_createAuction_error_long_enough_true (evm : EVM.State) {out : ByteArray}
    (hlong : 68 ≤ out.size) :
    evalExpr? auctionConfig
      { contract := auctionContract, locals := (∅ : Store).insert "err" (.bytes out) }
      evm (errorStringReturndataLongEnough "err") = .ok (.bool true) := by
  simp [errorStringReturndataLongEnough, localBytesLength, evalExpr?, EvalResult.bind, bind,
    pure, readLocalPath?, evalBinaryOp?]
  omega

theorem evalExpr_createAuction_error_long_enough_false (evm : EVM.State) {out : ByteArray}
    (hshort : out.size < 68) :
    evalExpr? auctionConfig
      { contract := auctionContract, locals := (∅ : Store).insert "err" (.bytes out) }
      evm (errorStringReturndataLongEnough "err") = .ok (.bool false) := by
  simp [errorStringReturndataLongEnough, localBytesLength, evalExpr?, EvalResult.bind, bind,
    pure, readLocalPath?, evalBinaryOp?]
  omega

def createAuctionErrFrame (out : ByteArray) : Frame :=
  { contract := auctionContract, locals := (∅ : Store).insert "err" (.bytes out) }

def createAuctionErrOffsetFrame (out : ByteArray) (off : Nat) : Frame :=
  { contract := auctionContract,
    locals := ((∅ : Store).insert "err" (.bytes out)).insert "_errOffset"
      (.int (Int.ofNat off)) }

def createAuctionErrLengthFrame (out : ByteArray) (off len : Nat) : Frame :=
  { contract := auctionContract,
    locals := (((∅ : Store).insert "err" (.bytes out)).insert "_errOffset"
      (.int (Int.ofNat off))).insert "_errLength" (.int (Int.ofNat len)) }

def createAuctionErrDecodedFrame (out : ByteArray) (off len : Nat) (decoded : Value) :
    Frame :=
  { contract := auctionContract,
    locals := ((((∅ : Store).insert "err" (.bytes out)).insert "_errOffset"
      (.int (Int.ofNat off))).insert "_errLength" (.int (Int.ofNat len))).insert
      "_errString" decoded }

theorem evalExpr_createAuction_error_err_ok_offsetFrame (evm : EVM.State)
    {out : ByteArray} {off : Nat} :
    evalExpr? auctionConfig (createAuctionErrOffsetFrame out off) evm (.var "err") =
      .ok (.bytes out) := by
  rw [Solm.evalExpr?.eq_def]
  simp [createAuctionErrOffsetFrame, EvalResult.ofOption, Std.HashMap.getElem_insert,
    Std.HashMap.getElem_insert_self]

theorem evalExpr_createAuction_error_err_ok_lengthFrame (evm : EVM.State)
    {out : ByteArray} {off len : Nat} :
    evalExpr? auctionConfig (createAuctionErrLengthFrame out off len) evm (.var "err") =
      .ok (.bytes out) := by
  rw [Solm.evalExpr?.eq_def]
  simp [createAuctionErrLengthFrame, EvalResult.ofOption, Std.HashMap.getElem_insert,
    Std.HashMap.getElem_insert_self]

theorem evalExpr_createAuction_error_offset_var_ok (evm : EVM.State)
    {out : ByteArray} {off : Nat} :
    evalExpr? auctionConfig (createAuctionErrOffsetFrame out off) evm (.var "_errOffset") =
      .ok (.int (Int.ofNat off)) := by
  rw [Solm.evalExpr?.eq_def]
  simp [createAuctionErrOffsetFrame, EvalResult.ofOption, Std.HashMap.getElem_insert,
    Std.HashMap.getElem_insert_self]

theorem evalExpr_createAuction_error_offset_var_ok_lengthFrame (evm : EVM.State)
    {out : ByteArray} {off len : Nat} :
    evalExpr? auctionConfig (createAuctionErrLengthFrame out off len) evm (.var "_errOffset") =
      .ok (.int (Int.ofNat off)) := by
  rw [Solm.evalExpr?.eq_def]
  simp [createAuctionErrLengthFrame, EvalResult.ofOption, Std.HashMap.getElem_insert,
    Std.HashMap.getElem_insert_self]

theorem evalExpr_createAuction_error_length_var_ok (evm : EVM.State)
    {out : ByteArray} {off len : Nat} :
    evalExpr? auctionConfig (createAuctionErrLengthFrame out off len) evm (.var "_errLength") =
      .ok (.int (Int.ofNat len)) := by
  rw [Solm.evalExpr?.eq_def]
  simp [createAuctionErrLengthFrame, EvalResult.ofOption, Std.HashMap.getElem_insert,
    Std.HashMap.getElem_insert_self]

theorem evalExpr_createAuction_error_local_length_ok_offsetFrame (evm : EVM.State)
    {out : ByteArray} {off : Nat} :
    evalExpr? auctionConfig (createAuctionErrOffsetFrame out off) evm (localBytesLength "err") =
      .ok (.int (Int.ofNat out.size)) := by
  rw [Solm.evalExpr?.eq_def]
  simp [localBytesLength, createAuctionErrOffsetFrame, EvalResult.bind, bind, readLocalPath?,
    Std.HashMap.getElem_insert, Std.HashMap.getElem_insert_self, pure]

theorem evalExpr_createAuction_error_local_length_ok_lengthFrame (evm : EVM.State)
    {out : ByteArray} {off len : Nat} :
    evalExpr? auctionConfig (createAuctionErrLengthFrame out off len) evm (localBytesLength "err") =
      .ok (.int (Int.ofNat out.size)) := by
  rw [Solm.evalExpr?.eq_def]
  simp [localBytesLength, createAuctionErrLengthFrame, EvalResult.bind, bind, readLocalPath?,
    Std.HashMap.getElem_insert, Std.HashMap.getElem_insert_self, pure]

theorem evalExpr_createAuction_error_offset_add36_ok (evm : EVM.State)
    {out : ByteArray} {off : Nat} :
    evalExpr? auctionConfig (createAuctionErrOffsetFrame out off) evm
      (.binary .add (.var "_errOffset") (.intLit 36)) =
        .ok (.int ((Int.ofNat off) + 36)) := by
  rw [Solm.evalExpr?.eq_def]
  simp only [EvalResult.bind, bind]
  rw [evalExpr_createAuction_error_offset_var_ok]
  simp [Solm.evalExpr?.eq_def, EvalResult.bind, bind, evalBinaryOp?]

theorem evalExpr_createAuction_error_offset_add32_ok (evm : EVM.State)
    {out : ByteArray} {off : Nat} :
    evalExpr? auctionConfig (createAuctionErrOffsetFrame out off) evm
      (.binary .add (.var "_errOffset") (.intLit 32)) =
        .ok (.int ((Int.ofNat off) + 32)) := by
  rw [Solm.evalExpr?.eq_def]
  simp only [EvalResult.bind, bind]
  rw [evalExpr_createAuction_error_offset_var_ok]
  simp [Solm.evalExpr?.eq_def, EvalResult.bind, bind, evalBinaryOp?]

theorem evalExpr_createAuction_error_offset_length_add_ok (evm : EVM.State)
    {out : ByteArray} {off len : Nat} :
    evalExpr? auctionConfig (createAuctionErrLengthFrame out off len) evm
      (.binary .add (.var "_errOffset") (.var "_errLength")) =
        .ok (.int ((Int.ofNat off) + Int.ofNat len)) := by
  rw [Solm.evalExpr?.eq_def]
  simp only [EvalResult.bind, bind]
  rw [evalExpr_createAuction_error_offset_var_ok_lengthFrame,
    evalExpr_createAuction_error_length_var_ok]
  simp [EvalResult.bind, bind, evalBinaryOp?]

theorem evalExpr_createAuction_error_payload_bound_lhs_ok (evm : EVM.State)
    {out : ByteArray} {off len : Nat} :
    evalExpr? auctionConfig (createAuctionErrLengthFrame out off len) evm
      (.binary .add (.binary .add (.var "_errOffset") (.var "_errLength")) (.intLit 36)) =
        .ok (.int ((Int.ofNat off) + Int.ofNat len + 36)) := by
  rw [Solm.evalExpr?.eq_def]
  simp only [EvalResult.bind, bind]
  rw [evalExpr_createAuction_error_offset_length_add_ok]
  simp [Solm.evalExpr?.eq_def, EvalResult.bind, bind, evalBinaryOp?]

theorem decodeReturnValue_uint256_of_readNat {b : ByteArray} {off : Nat}
    (hsmall : b.size < (2 : Nat) ^ 255)
    (hoff : ABI.readNat? b.toList 0 = some off) :
    ABI.decodeReturnValue? uint256 b = some (.int (Int.ofNat off)) := by
  change ABI.decodeReturnValue? abiUInt256 b = some (.int (Int.ofNat off))
  have hlenList := readNat?_some_length hoff
  have hlen : 32 ≤ b.size := by
    simpa [byteArray_toList_eq] using hlenList
  have hok := decodeReturnValue_uint256_ok (returndata := b) hlen hsmall
  rw [hok]
  congr
  unfold ABI.readNat? ABI.readWord? at hoff
  cases hbytes : ABI.readBytes? b.toList 0 32 with
  | none => simp [hbytes] at hoff
  | some wordBytes =>
      simp [hbytes, ABI.bytesToWord] at hoff
      cases hoff
      unfold ABI.readBytes? at hbytes
      have htake : ((b.toList.drop 0).take 32).length = 32 := by
        simpa using hlenList
      rw [if_pos htake] at hbytes
      cases hbytes
      rw [List.drop_zero]
      have hbext : b.extract 0 32 = ByteArray.mk ((b.toList.take 32).toArray) := by
        apply ByteArray.ext
        apply Array.toList_inj.mp
        rw [byteArray_toList_eq, ByteArray.data_extract, Array.toList_extract,
          List.extract_eq_take_drop, List.drop_zero]
      rw [hbext]
      simp [fromByteArrayBigEndian, byteArray_toList_eq]
      have hlt : fromBytesBigEndian (List.take 32 b.data.toList) < UInt256.size := by
        simpa [fromByteArrayBigEndian, byteArray_toList_eq] using
          (show fromByteArrayBigEndian (ByteArray.mk ((b.toList.take 32).toArray)) <
              UInt256.size by
            simpa [← hbext] using fromByteArrayBigEndian_extract0_32_lt hlen)
      exact (UInt256.toNat_ofNat_of_lt hlt).symm

theorem readNat?_extract_zero_of_readNat {b : ByteArray} {off n : Nat}
    (h : ABI.readNat? b.toList off = some n) :
    ABI.readNat? (b.extract off (off + 32)).toList 0 = some n := by
  unfold ABI.readNat? ABI.readWord? at h ⊢
  cases hbytes : ABI.readBytes? b.toList off 32 with
  | none => simp [hbytes] at h
  | some wordBytes =>
      simp [hbytes] at h
      unfold ABI.readBytes? at hbytes ⊢
      have hlen : ((b.toList.drop off).take 32).length = 32 := by
        by_cases hlen : ((b.toList.drop off).take 32).length = 32
        · exact hlen
        · rw [if_neg hlen] at hbytes
          cases hbytes
      rw [if_pos hlen] at hbytes
      cases hbytes
      have hsliceLen : (((b.extract off (off + 32)).toList.drop 0).take 32).length = 32 := by
        rw [List.drop_zero]
        rw [byteArray_toList_eq, ByteArray.data_extract, Array.toList_extract,
          List.extract_eq_take_drop]
        rw [byteArray_toList_eq] at hlen
        simpa using hlen
      rw [if_pos hsliceLen]
      rw [List.drop_zero]
      rw [byteArray_toList_eq, ByteArray.data_extract, Array.toList_extract,
        List.extract_eq_take_drop]
      simp only [Nat.add_sub_cancel_left, List.take_take]
      rw [min_self]
      simpa [byteArray_toList_eq] using h

theorem decodeReturnValue_uint256_slice_of_readNat {b : ByteArray} {off len : Nat}
    (hlen : ABI.readNat? b.toList off = some len) :
    ABI.decodeReturnValue? uint256 (b.extract off (off + 32)) =
      some (.int (Int.ofNat len)) := by
  have hread := readNat?_extract_zero_of_readNat (b := b) (off := off) hlen
  exact decodeReturnValue_uint256_of_readNat (b := b.extract off (off + 32))
    (by
      have hle : (b.extract off (off + 32)).size ≤ 32 := by
        rw [ByteArray.size_extract]
        omega
      exact lt_of_le_of_lt hle (by norm_num))
    hread

theorem evalExpr_createAuction_error_offset_decode_ok (evm : EVM.State) {out : ByteArray}
    {off : Nat} (hlen : 4 ≤ out.size)
    (hsmall : (out.extract 4 out.size).size < (2 : Nat) ^ 255)
    (hoff : ABI.readNat? (out.extract 4 out.size).toList 0 = some off) :
    evalExpr? auctionConfig (createAuctionErrFrame out) evm (errorStringOffsetDecode "err") =
      .ok (.int (Int.ofNat off)) := by
  change evalExpr? auctionConfig
    { contract := auctionContract, locals := (∅ : Store).insert "err" (.bytes out) }
      evm (.abiDecode uint256 (errorStringPayload "err")) = .ok (.int (Int.ofNat off))
  rw [Solm.evalExpr?.eq_def]
  simp only [EvalResult.bind, bind]
  rw [evalExpr_createAuction_error_payload_ok evm hlen]
  simp [EvalResult.bind, bind, pure, auctionConfig, ABI.decodeReturnValueWithMode?,
    decodeReturnValue_uint256_of_readNat hsmall hoff]

theorem evalExpr_createAuction_error_offset_max_true (evm : EVM.State) {out : ByteArray}
    {off : Nat} (hoffMax : off ≤ ABI.solcMaxU64) :
    evalExpr? auctionConfig (createAuctionErrOffsetFrame out off) evm
      (.binary .le (.var "_errOffset") solcMaxU64Expr) = .ok (.bool true) := by
  have hle : (Int.ofNat off) ≤ Int.ofNat ABI.solcMaxU64 := Int.ofNat_le.mpr hoffMax
  rw [Solm.evalExpr?.eq_def]
  simp only [EvalResult.bind, bind]
  rw [evalExpr_createAuction_error_offset_var_ok]
  simp [Solm.evalExpr?.eq_def, solcMaxU64Expr, evalBinaryOp?, hle, hoffMax]

theorem evalExpr_createAuction_error_offset_max_false (evm : EVM.State) {out : ByteArray}
    {off : Nat} (hoffMax : ABI.solcMaxU64 < off) :
    evalExpr? auctionConfig (createAuctionErrOffsetFrame out off) evm
      (.binary .le (.var "_errOffset") solcMaxU64Expr) = .ok (.bool false) := by
  have hle : ¬ (Int.ofNat off) ≤ Int.ofNat ABI.solcMaxU64 := by
    intro h
    exact Nat.not_le_of_gt hoffMax (Int.ofNat_le.mp h)
  rw [Solm.evalExpr?.eq_def]
  simp only [EvalResult.bind, bind]
  rw [evalExpr_createAuction_error_offset_var_ok]
  simp [Solm.evalExpr?.eq_def, solcMaxU64Expr, evalBinaryOp?, hle,
    Nat.not_le_of_gt hoffMax]

theorem evalExpr_createAuction_error_offset_bounds_true (evm : EVM.State) {out : ByteArray}
    {off : Nat} (hoffBound : off + 36 ≤ out.size) :
    evalExpr? auctionConfig (createAuctionErrOffsetFrame out off) evm
      (errorStringOffsetInBounds "err" "_errOffset") = .ok (.bool true) := by
  have hcast : (Int.ofNat off) + 36 = Int.ofNat (off + 36) := by norm_num
  have hle : (Int.ofNat off) + 36 ≤ Int.ofNat out.size := by
    rw [hcast]
    exact Int.ofNat_le.mpr hoffBound
  change evalExpr? auctionConfig (createAuctionErrOffsetFrame out off) evm
      (.binary .le (.binary .add (.var "_errOffset") (.intLit 36)) (localBytesLength "err")) =
    .ok (.bool true)
  rw [Solm.evalExpr?.eq_def]
  simp [EvalResult.bind, bind, evalExpr_createAuction_error_offset_add36_ok,
    evalExpr_createAuction_error_local_length_ok_offsetFrame, evalBinaryOp?, hle, hoffBound]
  exact hle

theorem evalExpr_createAuction_error_offset_bounds_false (evm : EVM.State) {out : ByteArray}
    {off : Nat} (hoffBound : out.size < off + 36) :
    evalExpr? auctionConfig (createAuctionErrOffsetFrame out off) evm
      (errorStringOffsetInBounds "err" "_errOffset") = .ok (.bool false) := by
  have hcast : (Int.ofNat off) + 36 = Int.ofNat (off + 36) := by norm_num
  have hle : ¬ (Int.ofNat off) + 36 ≤ Int.ofNat out.size := by
    intro h
    rw [hcast] at h
    exact Nat.not_le_of_gt hoffBound (Int.ofNat_le.mp h)
  change evalExpr? auctionConfig (createAuctionErrOffsetFrame out off) evm
      (.binary .le (.binary .add (.var "_errOffset") (.intLit 36)) (localBytesLength "err")) =
    .ok (.bool false)
  rw [Solm.evalExpr?.eq_def]
  simp [EvalResult.bind, bind, evalExpr_createAuction_error_offset_add36_ok,
    evalExpr_createAuction_error_local_length_ok_offsetFrame, evalBinaryOp?, hle,
    Nat.not_le_of_gt hoffBound]
  exact_mod_cast hoffBound

theorem evalExpr_createAuction_error_payload_ok_offsetFrame (evm : EVM.State) {out : ByteArray}
    {off : Nat} (hlen : 4 ≤ out.size) :
    evalExpr? auctionConfig (createAuctionErrOffsetFrame out off) evm
      (errorStringPayload "err") = .ok (.bytes (out.extract 4 out.size)) := by
  have hlenInt : ¬ (out.size : Int) < 4 := by omega
  change evalExpr? auctionConfig (createAuctionErrOffsetFrame out off) evm
      (.bytesSlice (.var "err") (.intLit 4) (localBytesLength "err")) =
    .ok (.bytes (out.extract 4 out.size))
  rw [Solm.evalExpr?.eq_def]
  simp only [EvalResult.bind, bind, evalExpr_createAuction_error_err_ok_offsetFrame,
    evalExpr_createAuction_error_local_length_ok_offsetFrame]
  simp [Solm.evalExpr?.eq_def, sliceBytes?, hlenInt]

theorem evalExpr_createAuction_error_payload_ok_lengthFrame (evm : EVM.State) {out : ByteArray}
    {off len : Nat} (hlen : 4 ≤ out.size) :
    evalExpr? auctionConfig (createAuctionErrLengthFrame out off len) evm
      (errorStringPayload "err") = .ok (.bytes (out.extract 4 out.size)) := by
  have hlenInt : ¬ (out.size : Int) < 4 := by omega
  change evalExpr? auctionConfig (createAuctionErrLengthFrame out off len) evm
      (.bytesSlice (.var "err") (.intLit 4) (localBytesLength "err")) =
    .ok (.bytes (out.extract 4 out.size))
  rw [Solm.evalExpr?.eq_def]
  simp only [EvalResult.bind, bind, evalExpr_createAuction_error_err_ok_lengthFrame,
    evalExpr_createAuction_error_local_length_ok_lengthFrame]
  simp [Solm.evalExpr?.eq_def, sliceBytes?, hlenInt]

theorem evalExpr_createAuction_error_decode_ok_lengthFrame (evm : EVM.State) {out : ByteArray}
    {off len : Nat} {decoded : Value} (hlen : 4 ≤ out.size)
    (hdec : ABI.decodeReturnValue? .string (out.extract 4 out.size) = some decoded) :
    evalExpr? auctionConfig (createAuctionErrLengthFrame out off len) evm
      (.abiDecode .string (errorStringPayload "err")) = .ok decoded := by
  rw [evalExpr?]
  rw [evalExpr_createAuction_error_payload_ok_lengthFrame evm hlen]
  simp [EvalResult.bind, bind, pure, auctionConfig, ABI.decodeReturnValueWithMode?, hdec]

theorem evalExpr_createAuction_error_decode_revert_lengthFrame (evm : EVM.State)
    {out : ByteArray} {off len : Nat} (hlen : 4 ≤ out.size)
    (hdec : ABI.decodeReturnValue? .string (out.extract 4 out.size) = none) :
    evalExpr? auctionConfig (createAuctionErrLengthFrame out off len) evm
      (.abiDecode .string (errorStringPayload "err")) = .revert := by
  rw [evalExpr?]
  rw [evalExpr_createAuction_error_payload_ok_lengthFrame evm hlen]
  simp [EvalResult.bind, bind, pure, auctionConfig, ABI.decodeReturnValueWithMode?, hdec]

theorem evalExpr_createAuction_error_length_word_ok (evm : EVM.State) {out : ByteArray}
    {off : Nat} (hlen : 4 ≤ out.size) (hoffBound : off + 36 ≤ out.size) :
    evalExpr? auctionConfig (createAuctionErrOffsetFrame out off) evm
      (errorStringLengthWord "err" "_errOffset") =
        .ok (.bytes ((out.extract 4 out.size).extract off (off + 32))) := by
  have hstart : ¬ (off : Int) < 0 := by omega
  have hpayloadSize : (out.extract 4 out.size).size = out.size - 4 := by
    rw [ByteArray.size_extract, min_self]
  have hcastEnd : Int.ofNat (off + 32) = Int.ofNat off + 32 := by norm_num
  have hend : ¬ (Int.ofNat (out.size - 4) < Int.ofNat off + 32) := by
    have hnat : off + 32 ≤ out.size - 4 := by omega
    rw [← hcastEnd]
    exact not_lt.mpr (Int.ofNat_le.mpr hnat)
  have hendNonneg : ¬ (Int.ofNat off + 32) < 0 := by
    exact not_lt.mpr (by
      have hoffNonneg : (0 : Int) ≤ Int.ofNat off := Int.ofNat_nonneg off
      omega)
  have hendToNat : (Int.ofNat off + 32).toNat = off + 32 := by
    rw [← hcastEnd]
    exact Int.toNat_natCast (off + 32)
  have hendNotBeforeStart : ¬ (Int.ofNat off + 32).toNat < off := by
    rw [hendToNat]
    omega
  have hnotBounds :
      ¬ ((Int.ofNat off + 32).toNat < off ∨
        Int.ofNat (out.size - 4) < Int.ofNat off + 32) := by
    exact not_or.mpr ⟨hendNotBeforeStart, hend⟩
  change evalExpr? auctionConfig (createAuctionErrOffsetFrame out off) evm
      (.bytesSlice (errorStringPayload "err") (.var "_errOffset")
        (.binary .add (.var "_errOffset") (.intLit 32))) =
    .ok (.bytes ((out.extract 4 out.size).extract off (off + 32)))
  rw [Solm.evalExpr?.eq_def]
  simp only [EvalResult.bind, bind]
  rw [evalExpr_createAuction_error_payload_ok_offsetFrame evm hlen]
  rw [evalExpr_createAuction_error_offset_var_ok]
  rw [evalExpr_createAuction_error_offset_add32_ok]
  unfold sliceBytes?
  simp only [EvalResult.bind, bind]
  have hstartToNat : (Int.ofNat off).toNat = off := Int.toNat_natCast off
  have hendToNat' : (↑off + 32 : Int).toNat = off + 32 := by
    simpa using hendToNat
  simp only [Bool.or_eq_true, decide_eq_true_eq, gt_iff_lt]
  have hnegGuard : ¬ (Int.ofNat off < 0 ∨ Int.ofNat off + 32 < 0) := by
    exact not_or.mpr ⟨by simpa using hstart, hendNonneg⟩
  have hboundsGuard :
      ¬ ((Int.ofNat off + 32).toNat < (Int.ofNat off).toNat ∨
        (out.extract 4 out.size).size < (Int.ofNat off + 32).toNat) := by
    rw [hstartToNat, hendToNat, hpayloadSize]
    omega
  rw [if_neg hnegGuard, if_neg hboundsGuard]
  rw [hendToNat, hstartToNat]

theorem evalExpr_createAuction_error_length_decode_ok (evm : EVM.State) {out : ByteArray}
    {off len : Nat} (hlenOut : 4 ≤ out.size) (hoffBound : off + 36 ≤ out.size)
    (hlen : ABI.readNat? (out.extract 4 out.size).toList off = some len) :
    evalExpr? auctionConfig (createAuctionErrOffsetFrame out off) evm
      (errorStringLengthDecode "err" "_errOffset") = .ok (.int (Int.ofNat len)) := by
  change evalExpr? auctionConfig (createAuctionErrOffsetFrame out off) evm
      (.abiDecode uint256 (errorStringLengthWord "err" "_errOffset")) =
    .ok (.int (Int.ofNat len))
  rw [Solm.evalExpr?.eq_def]
  simp only [EvalResult.bind, bind]
  rw [evalExpr_createAuction_error_length_word_ok evm hlenOut hoffBound]
  simp [EvalResult.bind, bind, pure, auctionConfig, ABI.decodeReturnValueWithMode?,
    decodeReturnValue_uint256_slice_of_readNat hlen]

theorem evalExpr_createAuction_error_length_max_true (evm : EVM.State) {out : ByteArray}
    {off len : Nat} (hlenMax : len ≤ ABI.solcMaxU64) :
    evalExpr? auctionConfig (createAuctionErrLengthFrame out off len) evm
      (.binary .le (.var "_errLength") solcMaxU64Expr) = .ok (.bool true) := by
  have hle : (Int.ofNat len) ≤ Int.ofNat ABI.solcMaxU64 := Int.ofNat_le.mpr hlenMax
  rw [Solm.evalExpr?.eq_def]
  simp only [EvalResult.bind, bind]
  rw [evalExpr_createAuction_error_length_var_ok]
  simp [Solm.evalExpr?.eq_def, solcMaxU64Expr, evalBinaryOp?, hle, hlenMax]

theorem evalExpr_createAuction_error_length_max_false (evm : EVM.State) {out : ByteArray}
    {off len : Nat} (hlenMax : ABI.solcMaxU64 < len) :
    evalExpr? auctionConfig (createAuctionErrLengthFrame out off len) evm
      (.binary .le (.var "_errLength") solcMaxU64Expr) = .ok (.bool false) := by
  have hle : ¬ (Int.ofNat len) ≤ Int.ofNat ABI.solcMaxU64 := by
    intro h
    exact Nat.not_le_of_gt hlenMax (Int.ofNat_le.mp h)
  rw [Solm.evalExpr?.eq_def]
  simp only [EvalResult.bind, bind]
  rw [evalExpr_createAuction_error_length_var_ok]
  simp [Solm.evalExpr?.eq_def, solcMaxU64Expr, evalBinaryOp?, hle,
    Nat.not_le_of_gt hlenMax]

theorem evalExpr_createAuction_error_payload_bounds_true (evm : EVM.State) {out : ByteArray}
    {off len : Nat} (hpayloadBound : off + len + 36 ≤ out.size) :
    evalExpr? auctionConfig (createAuctionErrLengthFrame out off len) evm
      (errorStringPayloadInBounds "err" "_errOffset" "_errLength") = .ok (.bool true) := by
  have hcast :
      (Int.ofNat off) + Int.ofNat len + 36 = Int.ofNat (off + len + 36) := by
    norm_num
  have hle : (Int.ofNat off) + Int.ofNat len + 36 ≤ Int.ofNat out.size := by
    rw [hcast]
    exact Int.ofNat_le.mpr hpayloadBound
  change evalExpr? auctionConfig (createAuctionErrLengthFrame out off len) evm
      (.binary .le
        (.binary .add (.binary .add (.var "_errOffset") (.var "_errLength")) (.intLit 36))
        (localBytesLength "err")) = .ok (.bool true)
  rw [Solm.evalExpr?.eq_def]
  simp [EvalResult.bind, bind, evalExpr_createAuction_error_payload_bound_lhs_ok,
    evalExpr_createAuction_error_local_length_ok_lengthFrame, evalBinaryOp?, hle,
    hpayloadBound]
  exact hle

theorem evalExpr_createAuction_error_payload_bounds_false (evm : EVM.State) {out : ByteArray}
    {off len : Nat} (hpayloadBound : out.size < off + len + 36) :
    evalExpr? auctionConfig (createAuctionErrLengthFrame out off len) evm
      (errorStringPayloadInBounds "err" "_errOffset" "_errLength") = .ok (.bool false) := by
  have hcast :
      (Int.ofNat off) + Int.ofNat len + 36 = Int.ofNat (off + len + 36) := by
    norm_num
  have hle : ¬ ((Int.ofNat off) + Int.ofNat len + 36 ≤ Int.ofNat out.size) := by
    intro h
    rw [hcast] at h
    exact Nat.not_le_of_gt hpayloadBound (Int.ofNat_le.mp h)
  change evalExpr? auctionConfig (createAuctionErrLengthFrame out off len) evm
      (.binary .le
        (.binary .add (.binary .add (.var "_errOffset") (.var "_errLength")) (.intLit 36))
        (localBytesLength "err")) = .ok (.bool false)
  rw [Solm.evalExpr?.eq_def]
  simp [EvalResult.bind, bind, evalExpr_createAuction_error_payload_bound_lhs_ok,
    evalExpr_createAuction_error_local_length_ok_lengthFrame, evalBinaryOp?, hle,
    Nat.not_le_of_gt hpayloadBound]
  exact_mod_cast hpayloadBound

def errorStringRoundedAllocNat (off len : Nat) : Nat :=
  Nat.land (UInt256.size - 32) (off + len + 63)

def errorStringNewFreeNat (off len : Nat) : Nat :=
  128 + errorStringRoundedAllocNat off len

theorem evalExpr_createAuction_error_alloc_sum32_ok (evm : EVM.State)
    {out : ByteArray} {off len : Nat} :
    evalExpr? auctionConfig (createAuctionErrLengthFrame out off len) evm
      (.binary .add
        (.binary .add (.var "_errOffset") (.var "_errLength"))
        (.intLit 32)) = .ok (.int (Int.ofNat (off + len + 32))) := by
  rw [Solm.evalExpr?.eq_def]
  simp only [EvalResult.bind, bind]
  rw [evalExpr_createAuction_error_offset_length_add_ok]
  simp [Solm.evalExpr?.eq_def, EvalResult.bind, bind, evalBinaryOp?]

theorem evalExpr_createAuction_error_alloc_sum_ok (evm : EVM.State)
    {out : ByteArray} {off len : Nat} :
    evalExpr? auctionConfig (createAuctionErrLengthFrame out off len) evm
      (.binary .add
        (.binary .add
          (.binary .add (.var "_errOffset") (.var "_errLength"))
          (.intLit 32))
        (.intLit 31)) = .ok (.int (Int.ofNat (off + len + 63))) := by
  rw [Solm.evalExpr?.eq_def]
  simp only [EvalResult.bind, bind]
  rw [evalExpr_createAuction_error_alloc_sum32_ok]
  simp [Solm.evalExpr?.eq_def, EvalResult.bind, bind, evalBinaryOp?]
  omega

theorem evalExpr_createAuction_error_rounded_alloc_ok (evm : EVM.State)
    {out : ByteArray} {off len : Nat} (hsum : off + len + 63 < UInt256.size) :
    evalExpr? auctionConfig (createAuctionErrLengthFrame out off len) evm
      (errorStringRoundedAllocSize (.var "_errOffset") (.var "_errLength")) =
        .ok (.int (Int.ofNat (errorStringRoundedAllocNat off len))) := by
  have hmaskLt : UInt256.size - 32 < EVM.wordModulus := by
    norm_num [UInt256.size, EVM.wordModulus, EVM.twoPow]
  have hsumCast :
      Int.ofNat off + Int.ofNat len + 63 = Int.ofNat (off + len + 63) := by
    norm_num
  have hsumGuard :
      0 ≤ Int.ofNat off + Int.ofNat len + 63 ∧
        Int.ofNat off + Int.ofNat len + 63 < (EVM.wordModulus : Int) := by
    constructor
    · exact Int.add_nonneg
        (Int.add_nonneg (Int.natCast_nonneg off) (Int.natCast_nonneg len))
        (by norm_num)
    · rw [hsumCast]
      exact Int.ofNat_lt.mpr (by
        simpa [EVM.wordModulus, EVM.twoPow, UInt256.size] using hsum)
  have hsumToNat : (Int.ofNat off + Int.ofNat len + 63).toNat = off + len + 63 := by
    rw [hsumCast]
    exact Int.toNat_natCast (off + len + 63)
  have hsumToNat' : (↑off + ↑len + 63 : Int).toNat = off + len + 63 := by
    simpa using hsumToNat
  change evalExpr? auctionConfig (createAuctionErrLengthFrame out off len) evm
      (.binary .bitAnd solcWordAlignMaskExpr
        (.binary .add
          (.binary .add
            (.binary .add (.var "_errOffset") (.var "_errLength"))
            (.intLit 32))
          (.intLit 31))) =
    .ok (.int (Int.ofNat (errorStringRoundedAllocNat off len)))
  rw [Solm.evalExpr?.eq_def]
  simp only [EvalResult.bind, bind]
  rw [evalExpr_createAuction_error_alloc_sum_ok]
  simp [Solm.evalExpr?.eq_def, solcWordAlignMaskExpr, errorStringRoundedAllocSize,
    errorStringRoundedAllocNat, evalBinaryOp?, hsum, hmaskLt]
  rw [if_pos (by simpa using hsumGuard)]
  rw [hsumToNat']

theorem evalExpr_createAuction_error_new_free_ok (evm : EVM.State)
    {out : ByteArray} {off len : Nat} (hsum : off + len + 63 < UInt256.size) :
    evalExpr? auctionConfig (createAuctionErrLengthFrame out off len) evm
      (errorStringNewFreePtr "_errOffset" "_errLength") =
        .ok (.int (Int.ofNat (errorStringNewFreeNat off len))) := by
  change evalExpr? auctionConfig (createAuctionErrLengthFrame out off len) evm
      (.binary .add (.intLit 128)
        (errorStringRoundedAllocSize (.var "_errOffset") (.var "_errLength"))) =
    .ok (.int (Int.ofNat (errorStringNewFreeNat off len)))
  rw [Solm.evalExpr?.eq_def]
  simp only [EvalResult.bind, bind]
  rw [evalExpr_createAuction_error_rounded_alloc_ok evm hsum]
  simp [Solm.evalExpr?.eq_def, errorStringNewFreePtr, errorStringNewFreeNat,
    EvalResult.bind, bind, evalBinaryOp?]

theorem evalExpr_createAuction_error_alloc_u64_true (evm : EVM.State) {out : ByteArray}
    {off len : Nat} (hoffMax : off ≤ ABI.solcMaxU64) (hlenMax : len ≤ ABI.solcMaxU64)
    (halloc : errorStringNewFreeNat off len ≤ ABI.solcMaxU64) :
    evalExpr? auctionConfig (createAuctionErrLengthFrame out off len) evm
      (errorStringAllocationWithinU64 "_errOffset" "_errLength") = .ok (.bool true) := by
  have hsum : off + len + 63 < UInt256.size := by
    norm_num [ABI.solcMaxU64, UInt256.size] at *
    omega
  have hle :
      Int.ofNat (errorStringNewFreeNat off len) ≤ Int.ofNat ABI.solcMaxU64 :=
    Int.ofNat_le.mpr halloc
  change evalExpr? auctionConfig (createAuctionErrLengthFrame out off len) evm
      (.binary .le (errorStringNewFreePtr "_errOffset" "_errLength") solcMaxU64Expr) =
    .ok (.bool true)
  rw [Solm.evalExpr?.eq_def]
  simp only [EvalResult.bind, bind]
  rw [evalExpr_createAuction_error_new_free_ok evm hsum]
  simp [Solm.evalExpr?.eq_def, errorStringAllocationWithinU64, solcMaxU64Expr,
    evalBinaryOp?, hle]
  exact halloc

theorem evalExpr_createAuction_error_alloc_u64_false (evm : EVM.State) {out : ByteArray}
    {off len : Nat} (hoffMax : off ≤ ABI.solcMaxU64) (hlenMax : len ≤ ABI.solcMaxU64)
    (halloc : ABI.solcMaxU64 < errorStringNewFreeNat off len) :
    evalExpr? auctionConfig (createAuctionErrLengthFrame out off len) evm
      (errorStringAllocationWithinU64 "_errOffset" "_errLength") = .ok (.bool false) := by
  have hsum : off + len + 63 < UInt256.size := by
    norm_num [ABI.solcMaxU64, UInt256.size] at *
    omega
  have hle : ¬ (Int.ofNat (errorStringNewFreeNat off len)) ≤ Int.ofNat ABI.solcMaxU64 := by
    exact fun h => Nat.not_le_of_gt halloc (Int.ofNat_le.mp h)
  change evalExpr? auctionConfig (createAuctionErrLengthFrame out off len) evm
      (.binary .le (errorStringNewFreePtr "_errOffset" "_errLength") solcMaxU64Expr) =
    .ok (.bool false)
  rw [Solm.evalExpr?.eq_def]
  simp only [EvalResult.bind, bind]
  rw [evalExpr_createAuction_error_new_free_ok evm hsum]
  simp [Solm.evalExpr?.eq_def, errorStringAllocationWithinU64, solcMaxU64Expr,
    evalBinaryOp?, hle]
  exact halloc

theorem evalExpr_createAuction_error_alloc_no_wrap_true (evm : EVM.State) {out : ByteArray}
    {off len : Nat} (hoffMax : off ≤ ABI.solcMaxU64) (hlenMax : len ≤ ABI.solcMaxU64) :
    evalExpr? auctionConfig (createAuctionErrLengthFrame out off len) evm
      (errorStringAllocationNoWrap "_errOffset" "_errLength") = .ok (.bool true) := by
  have hsum : off + len + 63 < UInt256.size := by
    norm_num [ABI.solcMaxU64, UInt256.size] at *
    omega
  have hle : (128 : Int) ≤ Int.ofNat (errorStringNewFreeNat off len) := by
    simp [errorStringNewFreeNat]
  change evalExpr? auctionConfig (createAuctionErrLengthFrame out off len) evm
      (.binary .ge (errorStringNewFreePtr "_errOffset" "_errLength") (.intLit 128)) =
    .ok (.bool true)
  rw [Solm.evalExpr?.eq_def]
  simp only [EvalResult.bind, bind]
  rw [evalExpr_createAuction_error_new_free_ok evm hsum]
  simp [Solm.evalExpr?.eq_def, errorStringAllocationNoWrap, evalBinaryOp?, hle]
  simp [errorStringNewFreeNat]

theorem evalExpr_pause_true_frame (evm : EVM.State) (locals : Store) :
    evalExpr? auctionConfig { contract := auctionContract, locals := locals } evm (.boolLit true) =
      .ok (.bool true) := by
  simp [evalExpr?, pure]

theorem evalExpr_pause_paused_false_frame (evm : EVM.State) (locals : Store)
    (hbase : locals.get? pausedRef.base = none)
    (hzero :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨51⟩) ⟨255⟩ =
        ⟨0⟩) :
    evalExpr? auctionConfig { contract := auctionContract, locals := locals }
      evm (.storage pausedRef) = .ok (.bool false) := by
  have her : evalStorageRef auctionConfig { contract := auctionContract, locals := locals } evm
      pausedRef = .ok { base := "_paused", steps := [] } := by
    simp [evalStorageRef, evalStorageRefSteps, pausedRef, EvalResult.bind, pure, bind]
  have hty : storageTypeAt? auctionContract.storage
      ({ base := "_paused", steps := [] } : EvaledStorageRef) = some (.elem .bool) := by
    decide
  rw [evalExpr_storage_scalar (t := .bool) (hbase := hbase) (her := her) (hty := hty)
    (hloc := by rfl)]
  exact congrArg EvalResult.ok (by
    simpa [auctionBoolLoc, boolOffset0Loc] using
      auctionStorageLocLoad_bool_offset0_false evm ⟨51⟩ hzero)

theorem evalExpr_pause_paused_true_frame (evm : EVM.State) (locals : Store)
    (hbase : locals.get? pausedRef.base = none)
    (hnz :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨51⟩) ⟨255⟩ ≠
        ⟨0⟩) :
    evalExpr? auctionConfig { contract := auctionContract, locals := locals }
      evm (.storage pausedRef) = .ok (.bool true) := by
  have her : evalStorageRef auctionConfig { contract := auctionContract, locals := locals } evm
      pausedRef = .ok { base := "_paused", steps := [] } := by
    simp [evalStorageRef, evalStorageRefSteps, pausedRef, EvalResult.bind, pure, bind]
  have hty : storageTypeAt? auctionContract.storage
      ({ base := "_paused", steps := [] } : EvaledStorageRef) = some (.elem .bool) := by
    decide
  rw [evalExpr_storage_scalar (t := .bool) (hbase := hbase) (her := her) (hty := hty)
    (hloc := by rfl)]
  exact congrArg EvalResult.ok (by
    simpa [auctionBoolLoc, boolOffset0Loc] using
      auctionStorageLocLoad_bool_offset0_true evm ⟨51⟩ hnz)

theorem evalExpr_pause_notPaused_true_frame (evm : EVM.State) (locals : Store)
    (hbase : locals.get? pausedRef.base = none)
    (hzero :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨51⟩) ⟨255⟩ =
        ⟨0⟩) :
    evalExpr? auctionConfig { contract := auctionContract, locals := locals }
      evm (.unary .not (.storage pausedRef)) = .ok (.bool true) := by
  simp [evalExpr?, EvalResult.bind, bind,
    evalExpr_pause_paused_false_frame evm locals hbase hzero, evalUnaryOp?]
  rfl

theorem evalExpr_pause_notPaused_false_frame (evm : EVM.State) (locals : Store)
    (hbase : locals.get? pausedRef.base = none)
    (hnz :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨51⟩) ⟨255⟩ ≠
        ⟨0⟩) :
    evalExpr? auctionConfig { contract := auctionContract, locals := locals }
      evm (.unary .not (.storage pausedRef)) = .ok (.bool false) := by
  simp [evalExpr?, EvalResult.bind, bind,
    evalExpr_pause_paused_true_frame evm locals hbase hnz, evalUnaryOp?]
  rfl

theorem auctionPauseAssign_frame (evm : EVM.State) (locals : Store)
    (hbase : locals.get? pausedRef.base = none) :
    assignStorageRef? auctionConfig { contract := auctionContract, locals := locals } evm .storage
        pausedRef (.bool true) =
      .ok ({ contract := auctionContract, locals := locals }, auctionPausePostState evm) := by
  have her : evalStorageRef auctionConfig { contract := auctionContract, locals := locals } evm
      pausedRef = .ok { base := "_paused", steps := [] } := by
    simp [evalStorageRef, evalStorageRefSteps, pausedRef, EvalResult.bind, pure, bind]
  have hty : storageTypeAt? auctionContract.storage
      ({ base := "_paused", steps := [] } : EvaledStorageRef) = some (.elem .bool) := by
    decide
  have hstore :
      storageLocStore evm (auctionBoolLoc ⟨51⟩) (.bool true) =
        some (auctionPausePostState evm) := by
    simpa [auctionBoolLoc, boolOffset0Loc, auctionPausePostState, auctionPausedSetTrueWord,
      setBoolOffset0Word] using
      auctionStorageLocStore_bool_true_offset0 evm ⟨51⟩
  exact assignStorageRef_storage_scalar_value (cfg := auctionConfig)
    (solm := { contract := auctionContract, locals := locals }) (evm := evm)
    (evm' := auctionPausePostState evm) (slot := pausedRef)
    (er := { base := "_paused", steps := [] }) (ty := .elem .bool)
    (loc := auctionBoolLoc ⟨51⟩) (value := .bool true) hbase her hty (by rfl)
    (by trivial) hstore

theorem execCreateAuctionErrorStringGuardBlock {evm : EVM.State} {out : ByteArray}
    {off len : Nat} {tail : List Stmt} {result : ExecResult}
    (hlen : 4 ≤ out.size) (hlong : 68 ≤ out.size)
    (hsmall : (out.extract 4 out.size).size < (2 : Nat) ^ 255)
    (hoff : ABI.readNat? (out.extract 4 out.size).toList 0 = some off)
    (hoffMax : off ≤ ABI.solcMaxU64)
    (hoffBound : off + 36 ≤ out.size)
    (hlenWord : ABI.readNat? (out.extract 4 out.size).toList off = some len)
    (hlenMax : len ≤ ABI.solcMaxU64)
    (hpayloadBound : off + len + 36 ≤ out.size)
    (halloc : errorStringNewFreeNat off len ≤ ABI.solcMaxU64)
    (htail : ExecBlock auctionConfig (createAuctionErrLengthFrame out off len) evm tail result) :
    ExecBlock auctionConfig (createAuctionErrFrame out) evm
      ([ .require (errorStringReturndataLongEnough "err"),
         .letDecl "_errOffset" (some uint256) (errorStringOffsetDecode "err"),
         .require (.binary .le (.var "_errOffset") solcMaxU64Expr),
         .require (errorStringOffsetInBounds "err" "_errOffset"),
         .letDecl "_errLength" (some uint256) (errorStringLengthDecode "err" "_errOffset"),
         .require (.binary .le (.var "_errLength") solcMaxU64Expr),
         .require (errorStringPayloadInBounds "err" "_errOffset" "_errLength"),
         .require (errorStringAllocationWithinU64 "_errOffset" "_errLength"),
         .require (errorStringAllocationNoWrap "_errOffset" "_errLength") ] ++ tail)
      result := by
  refine @ExecBlock.consNormal auctionConfig (createAuctionErrFrame out) evm
    (.require (errorStringReturndataLongEnough "err"))
    (createAuctionErrFrame out) evm
    ([ .letDecl "_errOffset" (some uint256) (errorStringOffsetDecode "err"),
       .require (.binary .le (.var "_errOffset") solcMaxU64Expr),
       .require (errorStringOffsetInBounds "err" "_errOffset"),
       .letDecl "_errLength" (some uint256) (errorStringLengthDecode "err" "_errOffset"),
       .require (.binary .le (.var "_errLength") solcMaxU64Expr),
       .require (errorStringPayloadInBounds "err" "_errOffset" "_errLength"),
       .require (errorStringAllocationWithinU64 "_errOffset" "_errLength"),
       .require (errorStringAllocationNoWrap "_errOffset" "_errLength") ] ++ tail)
    result ?_ ?_
  · exact ExecStmt.requireTrue (evalExpr_createAuction_error_long_enough_true evm hlong)
  · refine @ExecBlock.consNormal auctionConfig (createAuctionErrFrame out) evm
      (.letDecl "_errOffset" (some uint256) (errorStringOffsetDecode "err"))
      (createAuctionErrOffsetFrame out off) evm
      ([ .require (.binary .le (.var "_errOffset") solcMaxU64Expr),
         .require (errorStringOffsetInBounds "err" "_errOffset"),
         .letDecl "_errLength" (some uint256) (errorStringLengthDecode "err" "_errOffset"),
         .require (.binary .le (.var "_errLength") solcMaxU64Expr),
         .require (errorStringPayloadInBounds "err" "_errOffset" "_errLength"),
         .require (errorStringAllocationWithinU64 "_errOffset" "_errLength"),
         .require (errorStringAllocationNoWrap "_errOffset" "_errLength") ] ++ tail)
      result ?_ ?_
    · simpa [createAuctionErrFrame, createAuctionErrOffsetFrame] using
        ExecStmt.letDecl
          (evalExpr_createAuction_error_offset_decode_ok evm hlen hsmall hoff)
    · refine @ExecBlock.consNormal auctionConfig (createAuctionErrOffsetFrame out off) evm
        (.require (.binary .le (.var "_errOffset") solcMaxU64Expr))
        (createAuctionErrOffsetFrame out off) evm
        ([ .require (errorStringOffsetInBounds "err" "_errOffset"),
           .letDecl "_errLength" (some uint256) (errorStringLengthDecode "err" "_errOffset"),
           .require (.binary .le (.var "_errLength") solcMaxU64Expr),
           .require (errorStringPayloadInBounds "err" "_errOffset" "_errLength"),
           .require (errorStringAllocationWithinU64 "_errOffset" "_errLength"),
           .require (errorStringAllocationNoWrap "_errOffset" "_errLength") ] ++ tail)
        result ?_ ?_
      · exact ExecStmt.requireTrue (evalExpr_createAuction_error_offset_max_true evm hoffMax)
      · refine @ExecBlock.consNormal auctionConfig (createAuctionErrOffsetFrame out off) evm
          (.require (errorStringOffsetInBounds "err" "_errOffset"))
          (createAuctionErrOffsetFrame out off) evm
          ([ .letDecl "_errLength" (some uint256) (errorStringLengthDecode "err" "_errOffset"),
             .require (.binary .le (.var "_errLength") solcMaxU64Expr),
             .require (errorStringPayloadInBounds "err" "_errOffset" "_errLength"),
             .require (errorStringAllocationWithinU64 "_errOffset" "_errLength"),
             .require (errorStringAllocationNoWrap "_errOffset" "_errLength") ] ++ tail)
          result ?_ ?_
        · exact ExecStmt.requireTrue
            (evalExpr_createAuction_error_offset_bounds_true evm hoffBound)
        · refine @ExecBlock.consNormal auctionConfig (createAuctionErrOffsetFrame out off) evm
            (.letDecl "_errLength" (some uint256)
              (errorStringLengthDecode "err" "_errOffset"))
            (createAuctionErrLengthFrame out off len) evm
            ([ .require (.binary .le (.var "_errLength") solcMaxU64Expr),
               .require (errorStringPayloadInBounds "err" "_errOffset" "_errLength"),
               .require (errorStringAllocationWithinU64 "_errOffset" "_errLength"),
               .require (errorStringAllocationNoWrap "_errOffset" "_errLength") ] ++ tail)
            result ?_ ?_
          · simpa [createAuctionErrOffsetFrame, createAuctionErrLengthFrame] using
              ExecStmt.letDecl
                (evalExpr_createAuction_error_length_decode_ok evm hlen hoffBound hlenWord)
          · refine @ExecBlock.consNormal
              auctionConfig (createAuctionErrLengthFrame out off len) evm
              (.require (.binary .le (.var "_errLength") solcMaxU64Expr))
              (createAuctionErrLengthFrame out off len) evm
              ([ .require (errorStringPayloadInBounds "err" "_errOffset" "_errLength"),
                 .require (errorStringAllocationWithinU64 "_errOffset" "_errLength"),
                 .require (errorStringAllocationNoWrap "_errOffset" "_errLength") ] ++ tail)
              result ?_ ?_
            · exact ExecStmt.requireTrue
                (evalExpr_createAuction_error_length_max_true evm hlenMax)
            · refine @ExecBlock.consNormal
                auctionConfig (createAuctionErrLengthFrame out off len) evm
                (.require (errorStringPayloadInBounds "err" "_errOffset" "_errLength"))
                (createAuctionErrLengthFrame out off len) evm
                ([ .require (errorStringAllocationWithinU64 "_errOffset" "_errLength"),
                   .require (errorStringAllocationNoWrap "_errOffset" "_errLength") ] ++ tail)
                result ?_ ?_
              · exact ExecStmt.requireTrue
                  (evalExpr_createAuction_error_payload_bounds_true evm hpayloadBound)
              · refine @ExecBlock.consNormal
                  auctionConfig (createAuctionErrLengthFrame out off len) evm
                  (.require (errorStringAllocationWithinU64 "_errOffset" "_errLength"))
                  (createAuctionErrLengthFrame out off len) evm
                  ([ .require (errorStringAllocationNoWrap "_errOffset" "_errLength") ] ++ tail)
                  result ?_ ?_
                · exact ExecStmt.requireTrue
                    (evalExpr_createAuction_error_alloc_u64_true evm hoffMax hlenMax halloc)
                · exact @ExecBlock.consNormal
                    auctionConfig (createAuctionErrLengthFrame out off len) evm
                    (.require (errorStringAllocationNoWrap "_errOffset" "_errLength"))
                    (createAuctionErrLengthFrame out off len) evm tail result
                    (ExecStmt.requireTrue
                      (evalExpr_createAuction_error_alloc_no_wrap_true evm hoffMax hlenMax))
                    htail

theorem execCreateAuctionErrorStringOffsetMaxReverts {evm : EVM.State} {out : ByteArray}
    {off : Nat} {tail : List Stmt}
    (hlen : 4 ≤ out.size) (hlong : 68 ≤ out.size)
    (hsmall : (out.extract 4 out.size).size < (2 : Nat) ^ 255)
    (hoff : ABI.readNat? (out.extract 4 out.size).toList 0 = some off)
    (hoffMax : ABI.solcMaxU64 < off) :
    ExecBlock auctionConfig (createAuctionErrFrame out) evm
      ([ .require (errorStringReturndataLongEnough "err"),
         .letDecl "_errOffset" (some uint256) (errorStringOffsetDecode "err"),
         .require (.binary .le (.var "_errOffset") solcMaxU64Expr) ] ++ tail)
      .reverted := by
  refine @ExecBlock.consNormal auctionConfig (createAuctionErrFrame out) evm
    (.require (errorStringReturndataLongEnough "err"))
    (createAuctionErrFrame out) evm
    ([ .letDecl "_errOffset" (some uint256) (errorStringOffsetDecode "err"),
       .require (.binary .le (.var "_errOffset") solcMaxU64Expr) ] ++ tail)
    .reverted ?_ ?_
  · exact ExecStmt.requireTrue (evalExpr_createAuction_error_long_enough_true evm hlong)
  · refine @ExecBlock.consNormal auctionConfig (createAuctionErrFrame out) evm
      (.letDecl "_errOffset" (some uint256) (errorStringOffsetDecode "err"))
      (createAuctionErrOffsetFrame out off) evm
      ([ .require (.binary .le (.var "_errOffset") solcMaxU64Expr) ] ++ tail)
      .reverted ?_ ?_
    · simpa [createAuctionErrFrame, createAuctionErrOffsetFrame] using
        ExecStmt.letDecl
          (evalExpr_createAuction_error_offset_decode_ok evm hlen hsmall hoff)
    · exact ExecBlock.consRevert
        (ExecStmt.requireFalse
          (evalExpr_createAuction_error_offset_max_false evm hoffMax))

theorem execCreateAuctionErrorStringOffsetBoundsReverts {evm : EVM.State} {out : ByteArray}
    {off : Nat} {tail : List Stmt}
    (hlen : 4 ≤ out.size) (hlong : 68 ≤ out.size)
    (hsmall : (out.extract 4 out.size).size < (2 : Nat) ^ 255)
    (hoff : ABI.readNat? (out.extract 4 out.size).toList 0 = some off)
    (hoffMax : off ≤ ABI.solcMaxU64) (hoffBound : out.size < off + 36) :
    ExecBlock auctionConfig (createAuctionErrFrame out) evm
      ([ .require (errorStringReturndataLongEnough "err"),
         .letDecl "_errOffset" (some uint256) (errorStringOffsetDecode "err"),
         .require (.binary .le (.var "_errOffset") solcMaxU64Expr),
         .require (errorStringOffsetInBounds "err" "_errOffset") ] ++ tail)
      .reverted := by
  refine @ExecBlock.consNormal auctionConfig (createAuctionErrFrame out) evm
    (.require (errorStringReturndataLongEnough "err"))
    (createAuctionErrFrame out) evm
    ([ .letDecl "_errOffset" (some uint256) (errorStringOffsetDecode "err"),
       .require (.binary .le (.var "_errOffset") solcMaxU64Expr),
       .require (errorStringOffsetInBounds "err" "_errOffset") ] ++ tail)
    .reverted ?_ ?_
  · exact ExecStmt.requireTrue (evalExpr_createAuction_error_long_enough_true evm hlong)
  · refine @ExecBlock.consNormal auctionConfig (createAuctionErrFrame out) evm
      (.letDecl "_errOffset" (some uint256) (errorStringOffsetDecode "err"))
      (createAuctionErrOffsetFrame out off) evm
      ([ .require (.binary .le (.var "_errOffset") solcMaxU64Expr),
         .require (errorStringOffsetInBounds "err" "_errOffset") ] ++ tail)
      .reverted ?_ ?_
    · simpa [createAuctionErrFrame, createAuctionErrOffsetFrame] using
        ExecStmt.letDecl
          (evalExpr_createAuction_error_offset_decode_ok evm hlen hsmall hoff)
    · refine @ExecBlock.consNormal auctionConfig (createAuctionErrOffsetFrame out off) evm
        (.require (.binary .le (.var "_errOffset") solcMaxU64Expr))
        (createAuctionErrOffsetFrame out off) evm
        ([ .require (errorStringOffsetInBounds "err" "_errOffset") ] ++ tail)
        .reverted ?_ ?_
      · exact ExecStmt.requireTrue
          (evalExpr_createAuction_error_offset_max_true evm hoffMax)
      · exact ExecBlock.consRevert
          (ExecStmt.requireFalse
            (evalExpr_createAuction_error_offset_bounds_false evm hoffBound))

theorem execCreateAuctionErrorStringGuardPrefix {evm : EVM.State} {out : ByteArray}
    {off len : Nat} {tail : List Stmt} {result : ExecResult}
    (hlenOut : 4 ≤ out.size) (hlong : 68 ≤ out.size)
    (hsmall : (out.extract 4 out.size).size < (2 : Nat) ^ 255)
    (hoff : ABI.readNat? (out.extract 4 out.size).toList 0 = some off)
    (hoffMax : off ≤ ABI.solcMaxU64) (hoffBound : off + 36 ≤ out.size)
    (hlenWord : ABI.readNat? (out.extract 4 out.size).toList off = some len)
    (htail : ExecBlock auctionConfig (createAuctionErrLengthFrame out off len) evm tail result) :
    ExecBlock auctionConfig (createAuctionErrFrame out) evm
      ([ .require (errorStringReturndataLongEnough "err"),
         .letDecl "_errOffset" (some uint256) (errorStringOffsetDecode "err"),
         .require (.binary .le (.var "_errOffset") solcMaxU64Expr),
         .require (errorStringOffsetInBounds "err" "_errOffset"),
         .letDecl "_errLength" (some uint256) (errorStringLengthDecode "err" "_errOffset") ] ++
        tail)
      result := by
  refine @ExecBlock.consNormal auctionConfig (createAuctionErrFrame out) evm
    (.require (errorStringReturndataLongEnough "err"))
    (createAuctionErrFrame out) evm
    ([ .letDecl "_errOffset" (some uint256) (errorStringOffsetDecode "err"),
       .require (.binary .le (.var "_errOffset") solcMaxU64Expr),
       .require (errorStringOffsetInBounds "err" "_errOffset"),
       .letDecl "_errLength" (some uint256) (errorStringLengthDecode "err" "_errOffset") ] ++
      tail)
    result ?_ ?_
  · exact ExecStmt.requireTrue (evalExpr_createAuction_error_long_enough_true evm hlong)
  · refine @ExecBlock.consNormal auctionConfig (createAuctionErrFrame out) evm
      (.letDecl "_errOffset" (some uint256) (errorStringOffsetDecode "err"))
      (createAuctionErrOffsetFrame out off) evm
      ([ .require (.binary .le (.var "_errOffset") solcMaxU64Expr),
         .require (errorStringOffsetInBounds "err" "_errOffset"),
         .letDecl "_errLength" (some uint256) (errorStringLengthDecode "err" "_errOffset") ] ++
        tail)
      result ?_ ?_
    · simpa [createAuctionErrFrame, createAuctionErrOffsetFrame] using
        ExecStmt.letDecl
          (evalExpr_createAuction_error_offset_decode_ok evm hlenOut hsmall hoff)
    · refine @ExecBlock.consNormal auctionConfig (createAuctionErrOffsetFrame out off) evm
        (.require (.binary .le (.var "_errOffset") solcMaxU64Expr))
        (createAuctionErrOffsetFrame out off) evm
        ([ .require (errorStringOffsetInBounds "err" "_errOffset"),
           .letDecl "_errLength" (some uint256) (errorStringLengthDecode "err" "_errOffset") ] ++
          tail)
        result ?_ ?_
      · exact ExecStmt.requireTrue
          (evalExpr_createAuction_error_offset_max_true evm hoffMax)
      · refine @ExecBlock.consNormal auctionConfig (createAuctionErrOffsetFrame out off) evm
          (.require (errorStringOffsetInBounds "err" "_errOffset"))
          (createAuctionErrOffsetFrame out off) evm
          ([ .letDecl "_errLength" (some uint256)
              (errorStringLengthDecode "err" "_errOffset") ] ++ tail)
          result ?_ ?_
        · exact ExecStmt.requireTrue
            (evalExpr_createAuction_error_offset_bounds_true evm hoffBound)
        · refine @ExecBlock.consNormal auctionConfig (createAuctionErrOffsetFrame out off) evm
            (.letDecl "_errLength" (some uint256)
              (errorStringLengthDecode "err" "_errOffset"))
            (createAuctionErrLengthFrame out off len) evm tail result ?_ htail
          simpa [createAuctionErrOffsetFrame, createAuctionErrLengthFrame] using
            ExecStmt.letDecl
              (evalExpr_createAuction_error_length_decode_ok evm hlenOut hoffBound hlenWord)

theorem execCreateAuctionErrorStringLengthMaxReverts {evm : EVM.State} {out : ByteArray}
    {off len : Nat} {tail : List Stmt}
    (hlenOut : 4 ≤ out.size) (hlong : 68 ≤ out.size)
    (hsmall : (out.extract 4 out.size).size < (2 : Nat) ^ 255)
    (hoff : ABI.readNat? (out.extract 4 out.size).toList 0 = some off)
    (hoffMax : off ≤ ABI.solcMaxU64) (hoffBound : off + 36 ≤ out.size)
    (hlenWord : ABI.readNat? (out.extract 4 out.size).toList off = some len)
    (hlenMax : ABI.solcMaxU64 < len) :
    ExecBlock auctionConfig (createAuctionErrFrame out) evm
      ([ .require (errorStringReturndataLongEnough "err"),
         .letDecl "_errOffset" (some uint256) (errorStringOffsetDecode "err"),
         .require (.binary .le (.var "_errOffset") solcMaxU64Expr),
         .require (errorStringOffsetInBounds "err" "_errOffset"),
         .letDecl "_errLength" (some uint256) (errorStringLengthDecode "err" "_errOffset"),
         .require (.binary .le (.var "_errLength") solcMaxU64Expr) ] ++ tail)
      .reverted := by
  refine execCreateAuctionErrorStringGuardPrefix hlenOut hlong hsmall hoff hoffMax
    hoffBound hlenWord ?_
  exact ExecBlock.consRevert
    (ExecStmt.requireFalse (evalExpr_createAuction_error_length_max_false evm hlenMax))

theorem execCreateAuctionErrorStringPayloadBoundsReverts {evm : EVM.State} {out : ByteArray}
    {off len : Nat} {tail : List Stmt}
    (hlenOut : 4 ≤ out.size) (hlong : 68 ≤ out.size)
    (hsmall : (out.extract 4 out.size).size < (2 : Nat) ^ 255)
    (hoff : ABI.readNat? (out.extract 4 out.size).toList 0 = some off)
    (hoffMax : off ≤ ABI.solcMaxU64) (hoffBound : off + 36 ≤ out.size)
    (hlenWord : ABI.readNat? (out.extract 4 out.size).toList off = some len)
    (hlenMax : len ≤ ABI.solcMaxU64) (hpayloadBound : out.size < off + len + 36) :
    ExecBlock auctionConfig (createAuctionErrFrame out) evm
      ([ .require (errorStringReturndataLongEnough "err"),
         .letDecl "_errOffset" (some uint256) (errorStringOffsetDecode "err"),
         .require (.binary .le (.var "_errOffset") solcMaxU64Expr),
         .require (errorStringOffsetInBounds "err" "_errOffset"),
         .letDecl "_errLength" (some uint256) (errorStringLengthDecode "err" "_errOffset"),
         .require (.binary .le (.var "_errLength") solcMaxU64Expr),
         .require (errorStringPayloadInBounds "err" "_errOffset" "_errLength") ] ++ tail)
      .reverted := by
  refine execCreateAuctionErrorStringGuardPrefix hlenOut hlong hsmall hoff hoffMax
    hoffBound hlenWord ?_
  refine @ExecBlock.consNormal auctionConfig (createAuctionErrLengthFrame out off len) evm
    (.require (.binary .le (.var "_errLength") solcMaxU64Expr))
    (createAuctionErrLengthFrame out off len) evm
    ([ .require (errorStringPayloadInBounds "err" "_errOffset" "_errLength") ] ++ tail)
    .reverted ?_ ?_
  · exact ExecStmt.requireTrue (evalExpr_createAuction_error_length_max_true evm hlenMax)
  · exact ExecBlock.consRevert
      (ExecStmt.requireFalse
        (evalExpr_createAuction_error_payload_bounds_false evm hpayloadBound))

theorem execCreateAuctionErrorStringAllocU64Reverts {evm : EVM.State} {out : ByteArray}
    {off len : Nat} {tail : List Stmt}
    (hlenOut : 4 ≤ out.size) (hlong : 68 ≤ out.size)
    (hsmall : (out.extract 4 out.size).size < (2 : Nat) ^ 255)
    (hoff : ABI.readNat? (out.extract 4 out.size).toList 0 = some off)
    (hoffMax : off ≤ ABI.solcMaxU64) (hoffBound : off + 36 ≤ out.size)
    (hlenWord : ABI.readNat? (out.extract 4 out.size).toList off = some len)
    (hlenMax : len ≤ ABI.solcMaxU64) (hpayloadBound : off + len + 36 ≤ out.size)
    (halloc : ABI.solcMaxU64 < errorStringNewFreeNat off len) :
    ExecBlock auctionConfig (createAuctionErrFrame out) evm
      ([ .require (errorStringReturndataLongEnough "err"),
         .letDecl "_errOffset" (some uint256) (errorStringOffsetDecode "err"),
         .require (.binary .le (.var "_errOffset") solcMaxU64Expr),
         .require (errorStringOffsetInBounds "err" "_errOffset"),
         .letDecl "_errLength" (some uint256) (errorStringLengthDecode "err" "_errOffset"),
         .require (.binary .le (.var "_errLength") solcMaxU64Expr),
         .require (errorStringPayloadInBounds "err" "_errOffset" "_errLength"),
         .require (errorStringAllocationWithinU64 "_errOffset" "_errLength") ] ++ tail)
      .reverted := by
  refine execCreateAuctionErrorStringGuardPrefix hlenOut hlong hsmall hoff hoffMax
    hoffBound hlenWord ?_
  refine @ExecBlock.consNormal auctionConfig (createAuctionErrLengthFrame out off len) evm
    (.require (.binary .le (.var "_errLength") solcMaxU64Expr))
    (createAuctionErrLengthFrame out off len) evm
    ([ .require (errorStringPayloadInBounds "err" "_errOffset" "_errLength"),
       .require (errorStringAllocationWithinU64 "_errOffset" "_errLength") ] ++ tail)
    .reverted ?_ ?_
  · exact ExecStmt.requireTrue (evalExpr_createAuction_error_length_max_true evm hlenMax)
  · refine @ExecBlock.consNormal auctionConfig (createAuctionErrLengthFrame out off len) evm
      (.require (errorStringPayloadInBounds "err" "_errOffset" "_errLength"))
      (createAuctionErrLengthFrame out off len) evm
      ([ .require (errorStringAllocationWithinU64 "_errOffset" "_errLength") ] ++ tail)
      .reverted ?_ ?_
    · exact ExecStmt.requireTrue
        (evalExpr_createAuction_error_payload_bounds_true evm hpayloadBound)
    · exact ExecBlock.consRevert
        (ExecStmt.requireFalse
          (evalExpr_createAuction_error_alloc_u64_false evm hoffMax hlenMax halloc))

theorem execCreateAuctionErrorStringThenReturns {evm : EVM.State} {out : ByteArray}
    {off len : Nat} {decoded : Value}
    (hlen : 4 ≤ out.size) (hlong : 68 ≤ out.size)
    (hsmall : (out.extract 4 out.size).size < (2 : Nat) ^ 255)
    (hoff : ABI.readNat? (out.extract 4 out.size).toList 0 = some off)
    (hoffMax : off ≤ ABI.solcMaxU64)
    (hoffBound : off + 36 ≤ out.size)
    (hlenWord : ABI.readNat? (out.extract 4 out.size).toList off = some len)
    (hlenMax : len ≤ ABI.solcMaxU64)
    (hpayloadBound : off + len + 36 ≤ out.size)
    (halloc : errorStringNewFreeNat off len ≤ ABI.solcMaxU64)
    (hdec : ABI.decodeReturnValue? .string (out.extract 4 out.size) = some decoded)
    (hnotPaused :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨51⟩) ⟨255⟩ =
        ⟨0⟩) :
    ExecBlock auctionConfig (createAuctionErrFrame out) evm
      [ .require (errorStringReturndataLongEnough "err"),
        .letDecl "_errOffset" (some uint256) (errorStringOffsetDecode "err"),
        .require (.binary .le (.var "_errOffset") solcMaxU64Expr),
        .require (errorStringOffsetInBounds "err" "_errOffset"),
        .letDecl "_errLength" (some uint256) (errorStringLengthDecode "err" "_errOffset"),
        .require (.binary .le (.var "_errLength") solcMaxU64Expr),
        .require (errorStringPayloadInBounds "err" "_errOffset" "_errLength"),
        .require (errorStringAllocationWithinU64 "_errOffset" "_errLength"),
        .require (errorStringAllocationNoWrap "_errOffset" "_errLength"),
        .letDecl "_errString" (some .string) (.abiDecode .string (errorStringPayload "err")),
        .require (.unary .not (.storage pausedRef)),
        .assign .storage pausedRef (.boolLit true) ]
      (.ok (createAuctionErrDecodedFrame out off len decoded) (auctionPausePostState evm)) := by
  refine execCreateAuctionErrorStringGuardBlock hlen hlong hsmall hoff hoffMax hoffBound
    hlenWord hlenMax hpayloadBound halloc ?_
  refine @ExecBlock.consNormal auctionConfig (createAuctionErrLengthFrame out off len) evm
    (.letDecl "_errString" (some .string) (.abiDecode .string (errorStringPayload "err")))
    (createAuctionErrDecodedFrame out off len decoded) evm
    [ .require (.unary .not (.storage pausedRef)),
      .assign .storage pausedRef (.boolLit true) ]
    (.ok (createAuctionErrDecodedFrame out off len decoded) (auctionPausePostState evm)) ?_ ?_
  · simpa [createAuctionErrLengthFrame, createAuctionErrDecodedFrame] using
      ExecStmt.letDecl (evalExpr_createAuction_error_decode_ok_lengthFrame evm hlen hdec)
  · have hbaseDecoded :
        (createAuctionErrDecodedFrame out off len decoded).locals.get? pausedRef.base = none := by
      simp [createAuctionErrDecodedFrame, pausedRef]
    refine @ExecBlock.consNormal
      auctionConfig (createAuctionErrDecodedFrame out off len decoded) evm
      (.require (.unary .not (.storage pausedRef)))
      (createAuctionErrDecodedFrame out off len decoded) evm
      [ .assign .storage pausedRef (.boolLit true) ]
      (.ok (createAuctionErrDecodedFrame out off len decoded) (auctionPausePostState evm)) ?_ ?_
    · have hnotPausedDecoded :
          evalExpr? auctionConfig (createAuctionErrDecodedFrame out off len decoded) evm
            (.unary .not (.storage pausedRef)) = .ok (.bool true) := by
        simpa [createAuctionErrDecodedFrame] using
          evalExpr_pause_notPaused_true_frame evm
            (createAuctionErrDecodedFrame out off len decoded).locals hbaseDecoded hnotPaused
      exact ExecStmt.requireTrue hnotPausedDecoded
    · have htrueDecoded :
          evalExpr? auctionConfig (createAuctionErrDecodedFrame out off len decoded) evm
            (.boolLit true) = .ok (.bool true) := by
        simpa [createAuctionErrDecodedFrame] using
          evalExpr_pause_true_frame evm (createAuctionErrDecodedFrame out off len decoded).locals
      have hassignDecoded :
          assignStorageRef? auctionConfig (createAuctionErrDecodedFrame out off len decoded) evm
              .storage pausedRef (.bool true) =
            .ok (createAuctionErrDecodedFrame out off len decoded, auctionPausePostState evm) := by
        simpa [createAuctionErrDecodedFrame] using
          auctionPauseAssign_frame evm (createAuctionErrDecodedFrame out off len decoded).locals
            hbaseDecoded
      exact @ExecBlock.consNormal
        auctionConfig (createAuctionErrDecodedFrame out off len decoded) evm
        (.assign .storage pausedRef (.boolLit true))
        (createAuctionErrDecodedFrame out off len decoded) (auctionPausePostState evm) []
        (.ok (createAuctionErrDecodedFrame out off len decoded) (auctionPausePostState evm))
        (ExecStmt.assign htrueDecoded hassignDecoded) ExecBlock.nil

theorem execCreateAuctionErrorStringThenDecodeReverts {evm : EVM.State} {out : ByteArray}
    {off len : Nat}
    (hlen : 4 ≤ out.size) (hlong : 68 ≤ out.size)
    (hsmall : (out.extract 4 out.size).size < (2 : Nat) ^ 255)
    (hoff : ABI.readNat? (out.extract 4 out.size).toList 0 = some off)
    (hoffMax : off ≤ ABI.solcMaxU64)
    (hoffBound : off + 36 ≤ out.size)
    (hlenWord : ABI.readNat? (out.extract 4 out.size).toList off = some len)
    (hlenMax : len ≤ ABI.solcMaxU64)
    (hpayloadBound : off + len + 36 ≤ out.size)
    (halloc : errorStringNewFreeNat off len ≤ ABI.solcMaxU64)
    (hdec : ABI.decodeReturnValue? .string (out.extract 4 out.size) = none) :
    ExecBlock auctionConfig (createAuctionErrFrame out) evm
      [ .require (errorStringReturndataLongEnough "err"),
        .letDecl "_errOffset" (some uint256) (errorStringOffsetDecode "err"),
        .require (.binary .le (.var "_errOffset") solcMaxU64Expr),
        .require (errorStringOffsetInBounds "err" "_errOffset"),
        .letDecl "_errLength" (some uint256) (errorStringLengthDecode "err" "_errOffset"),
        .require (.binary .le (.var "_errLength") solcMaxU64Expr),
        .require (errorStringPayloadInBounds "err" "_errOffset" "_errLength"),
        .require (errorStringAllocationWithinU64 "_errOffset" "_errLength"),
        .require (errorStringAllocationNoWrap "_errOffset" "_errLength"),
        .letDecl "_errString" (some .string) (.abiDecode .string (errorStringPayload "err")),
        .require (.unary .not (.storage pausedRef)),
        .assign .storage pausedRef (.boolLit true) ]
      .reverted := by
  refine execCreateAuctionErrorStringGuardBlock hlen hlong hsmall hoff hoffMax hoffBound
    hlenWord hlenMax hpayloadBound halloc ?_
  exact ExecBlock.consRevert
    (ExecStmt.letDeclRevert
      (evalExpr_createAuction_error_decode_revert_lengthFrame evm hlen hdec))

theorem execCreateAuctionErrorStringThenPausedReverts {evm : EVM.State} {out : ByteArray}
    {off len : Nat} {decoded : Value}
    (hlen : 4 ≤ out.size) (hlong : 68 ≤ out.size)
    (hsmall : (out.extract 4 out.size).size < (2 : Nat) ^ 255)
    (hoff : ABI.readNat? (out.extract 4 out.size).toList 0 = some off)
    (hoffMax : off ≤ ABI.solcMaxU64)
    (hoffBound : off + 36 ≤ out.size)
    (hlenWord : ABI.readNat? (out.extract 4 out.size).toList off = some len)
    (hlenMax : len ≤ ABI.solcMaxU64)
    (hpayloadBound : off + len + 36 ≤ out.size)
    (halloc : errorStringNewFreeNat off len ≤ ABI.solcMaxU64)
    (hdec : ABI.decodeReturnValue? .string (out.extract 4 out.size) = some decoded)
    (hpaused :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨51⟩) ⟨255⟩ ≠
        ⟨0⟩) :
    ExecBlock auctionConfig (createAuctionErrFrame out) evm
      [ .require (errorStringReturndataLongEnough "err"),
        .letDecl "_errOffset" (some uint256) (errorStringOffsetDecode "err"),
        .require (.binary .le (.var "_errOffset") solcMaxU64Expr),
        .require (errorStringOffsetInBounds "err" "_errOffset"),
        .letDecl "_errLength" (some uint256) (errorStringLengthDecode "err" "_errOffset"),
        .require (.binary .le (.var "_errLength") solcMaxU64Expr),
        .require (errorStringPayloadInBounds "err" "_errOffset" "_errLength"),
        .require (errorStringAllocationWithinU64 "_errOffset" "_errLength"),
        .require (errorStringAllocationNoWrap "_errOffset" "_errLength"),
        .letDecl "_errString" (some .string) (.abiDecode .string (errorStringPayload "err")),
        .require (.unary .not (.storage pausedRef)),
        .assign .storage pausedRef (.boolLit true) ]
      .reverted := by
  refine execCreateAuctionErrorStringGuardBlock hlen hlong hsmall hoff hoffMax hoffBound
    hlenWord hlenMax hpayloadBound halloc ?_
  refine @ExecBlock.consNormal auctionConfig (createAuctionErrLengthFrame out off len) evm
    (.letDecl "_errString" (some .string) (.abiDecode .string (errorStringPayload "err")))
    (createAuctionErrDecodedFrame out off len decoded) evm
    [ .require (.unary .not (.storage pausedRef)),
      .assign .storage pausedRef (.boolLit true) ]
    .reverted ?_ ?_
  · simpa [createAuctionErrLengthFrame, createAuctionErrDecodedFrame] using
      ExecStmt.letDecl (evalExpr_createAuction_error_decode_ok_lengthFrame evm hlen hdec)
  · have hbaseDecoded :
        (createAuctionErrDecodedFrame out off len decoded).locals.get? pausedRef.base = none := by
      simp [createAuctionErrDecodedFrame, pausedRef]
    have hpausedDecoded :
        evalExpr? auctionConfig (createAuctionErrDecodedFrame out off len decoded) evm
          (.unary .not (.storage pausedRef)) = .ok (.bool false) := by
      simpa [createAuctionErrDecodedFrame] using
        evalExpr_pause_notPaused_false_frame evm
          (createAuctionErrDecodedFrame out off len decoded).locals hbaseDecoded hpaused
    exact ExecBlock.consRevert (ExecStmt.requireFalse hpausedDecoded)

theorem auctionCreateAuctionBodyReverts_callFailure_empty {evm evmCall : EVM.State}
    (hcall : typedCallViaEVM auctionConfig evm
      (EVM.address (AccountAddress.ofNat
        ((UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨201⟩)
          solcAddrMask).toNat))) "mint" 0 [] (false, evmCall, ByteArray.empty) true) :
    ExecFuncBody auctionConfig { contract := auctionContract, locals := ∅ } evm createAuctionFn.body
      .reverted := by
  dsimp [createAuctionFn]
  refine ExecFuncBody.execBlockRevert ?_
  refine ExecBlock.consRevert ?_
  refine ExecStmt.checkedCallFail (evalExpr_createAuction_nouns evm)
    (evalExpr_createAuction_zero evm) (evalExprs_createAuction_mint_args evm) hcall ?_
  refine ExecBlock.consRevert
    (ExecStmt.iteCondRevert (evalExpr_createAuction_emptyErr_slice_revert evmCall))

theorem auctionCreateAuctionBodyReverts_callFailure_short {evm evmCall : EVM.State}
    {out : ByteArray}
    (hcall : typedCallViaEVM auctionConfig evm
      (EVM.address (AccountAddress.ofNat
        ((UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨201⟩)
          solcAddrMask).toNat))) "mint" 0 [] (false, evmCall, out) true)
    (hshort : out.size < 4) :
    ExecFuncBody auctionConfig { contract := auctionContract, locals := ∅ } evm createAuctionFn.body
      .reverted := by
  dsimp [createAuctionFn]
  refine ExecFuncBody.execBlockRevert ?_
  refine ExecBlock.consRevert ?_
  refine ExecStmt.checkedCallFail (evalExpr_createAuction_nouns evm)
    (evalExpr_createAuction_zero evm) (evalExprs_createAuction_mint_args evm) hcall ?_
  refine ExecBlock.consRevert
    (ExecStmt.iteCondRevert (evalExpr_createAuction_err_slice_revert evmCall hshort))

theorem auctionCreateAuctionBodyReverts_callFailure_nonError {evm evmCall : EVM.State}
    {out : ByteArray}
    (hcall : typedCallViaEVM auctionConfig evm
      (EVM.address (AccountAddress.ofNat
        ((UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨201⟩)
          solcAddrMask).toNat))) "mint" 0 [] (false, evmCall, out) true)
    (hlen : 4 ≤ out.size) (hsel : out.extract 0 4 ≠ errorStringSelector) :
    ExecFuncBody auctionConfig { contract := auctionContract, locals := ∅ } evm createAuctionFn.body
      .reverted := by
  dsimp [createAuctionFn]
  refine ExecFuncBody.execBlockRevert ?_
  refine ExecBlock.consRevert ?_
  refine ExecStmt.checkedCallFail (evalExpr_createAuction_nouns evm)
    (evalExpr_createAuction_zero evm) (evalExprs_createAuction_mint_args evm) hcall ?_
  refine ExecBlock.consRevert ?_
  refine ExecStmt.iteFalse (evalExpr_createAuction_err_slice_false evmCall hlen hsel) ?_
  exact ExecBlock.consRevert (ExecStmt.requireFalse (by simp [evalExpr?, pure]))

theorem auctionCreateAuctionBodyReturns_callFailure_errorString {evm evmCall : EVM.State}
    {out : ByteArray} {off len : Nat} {decoded : Value}
    (hcall : typedCallViaEVM auctionConfig evm
      (EVM.address (AccountAddress.ofNat
        ((UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨201⟩)
          solcAddrMask).toNat))) "mint" 0 [] (false, evmCall, out) true)
    (hlen : 4 ≤ out.size) (hsel : out.extract 0 4 = errorStringSelector)
    (hlong : 68 ≤ out.size)
    (hsmall : (out.extract 4 out.size).size < (2 : Nat) ^ 255)
    (hoff : ABI.readNat? (out.extract 4 out.size).toList 0 = some off)
    (hoffMax : off ≤ ABI.solcMaxU64)
    (hoffBound : off + 36 ≤ out.size)
    (hlenWord : ABI.readNat? (out.extract 4 out.size).toList off = some len)
    (hlenMax : len ≤ ABI.solcMaxU64)
    (hpayloadBound : off + len + 36 ≤ out.size)
    (halloc : errorStringNewFreeNat off len ≤ ABI.solcMaxU64)
    (hdec : ABI.decodeReturnValue? .string (out.extract 4 out.size) = some decoded)
    (hnotPaused :
      UInt256.land (Solm.EVM.storageLoad evmCall evmCall.executionEnv.codeOwner ⟨51⟩) ⟨255⟩ =
        ⟨0⟩) :
    ExecFuncBody auctionConfig { contract := auctionContract, locals := ∅ } evm createAuctionFn.body
      (.returned (createAuctionErrDecodedFrame out off len decoded)
        (auctionPausePostState evmCall) none) := by
  dsimp [createAuctionFn]
  refine ExecFuncBody.execBlockOK ?_
  refine ExecBlock.consNormal ?_ ExecBlock.nil
  refine ExecStmt.checkedCallFail (evalExpr_createAuction_nouns evm)
    (evalExpr_createAuction_zero evm) (evalExprs_createAuction_mint_args evm) hcall ?_
  have hthen : ExecBlock auctionConfig (createAuctionErrFrame out) evmCall
      [ .require (errorStringReturndataLongEnough "err"),
        .letDecl "_errOffset" (some uint256) (errorStringOffsetDecode "err"),
        .require (.binary .le (.var "_errOffset") solcMaxU64Expr),
        .require (errorStringOffsetInBounds "err" "_errOffset"),
        .letDecl "_errLength" (some uint256) (errorStringLengthDecode "err" "_errOffset"),
        .require (.binary .le (.var "_errLength") solcMaxU64Expr),
        .require (errorStringPayloadInBounds "err" "_errOffset" "_errLength"),
        .require (errorStringAllocationWithinU64 "_errOffset" "_errLength"),
        .require (errorStringAllocationNoWrap "_errOffset" "_errLength"),
        .letDecl "_errString" (some .string) (.abiDecode .string (errorStringPayload "err")),
        .require (.unary .not (.storage pausedRef)),
        .assign .storage pausedRef (.boolLit true) ]
      (.ok (createAuctionErrDecodedFrame out off len decoded)
        (auctionPausePostState evmCall)) :=
    execCreateAuctionErrorStringThenReturns hlen hlong hsmall hoff hoffMax hoffBound
      hlenWord hlenMax hpayloadBound halloc hdec hnotPaused
  have hcatch : ExecBlock auctionConfig (createAuctionErrFrame out) evmCall
      [ .ite (.binary .eq (.bytesSlice (.var "err") (.intLit 0) (.intLit 4))
          (.bytesLit errorStringSelector))
        [ .require (errorStringReturndataLongEnough "err"),
          .letDecl "_errOffset" (some uint256) (errorStringOffsetDecode "err"),
          .require (.binary .le (.var "_errOffset") solcMaxU64Expr),
          .require (errorStringOffsetInBounds "err" "_errOffset"),
          .letDecl "_errLength" (some uint256) (errorStringLengthDecode "err" "_errOffset"),
          .require (.binary .le (.var "_errLength") solcMaxU64Expr),
          .require (errorStringPayloadInBounds "err" "_errOffset" "_errLength"),
          .require (errorStringAllocationWithinU64 "_errOffset" "_errLength"),
          .require (errorStringAllocationNoWrap "_errOffset" "_errLength"),
          .letDecl "_errString" (some .string) (.abiDecode .string (errorStringPayload "err")),
          .require (.unary .not (.storage pausedRef)),
          .assign .storage pausedRef (.boolLit true) ]
        [ .require (.boolLit false) ] ]
      (.ok (createAuctionErrDecodedFrame out off len decoded)
        (auctionPausePostState evmCall)) := by
    exact ExecBlock.consNormal
      (ExecStmt.iteTrue
        (by
          simpa [createAuctionErrFrame] using
            evalExpr_createAuction_err_slice_true evmCall hlen hsel)
        hthen)
      ExecBlock.nil
  simpa [createAuctionErrFrame] using hcatch

theorem auctionCreateAuctionBodyReverts_callFailure_errorStringShort
    {evm evmCall : EVM.State} {out : ByteArray}
    (hcall : typedCallViaEVM auctionConfig evm
      (EVM.address (AccountAddress.ofNat
        ((UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨201⟩)
          solcAddrMask).toNat))) "mint" 0 [] (false, evmCall, out) true)
    (hlen : 4 ≤ out.size) (hsel : out.extract 0 4 = errorStringSelector)
    (hshort : out.size < 68) :
    ExecFuncBody auctionConfig { contract := auctionContract, locals := ∅ } evm createAuctionFn.body
      .reverted := by
  dsimp [createAuctionFn]
  refine ExecFuncBody.execBlockRevert ?_
  refine ExecBlock.consRevert ?_
  refine ExecStmt.checkedCallFail (evalExpr_createAuction_nouns evm)
    (evalExpr_createAuction_zero evm) (evalExprs_createAuction_mint_args evm) hcall ?_
  refine ExecBlock.consRevert ?_
  refine ExecStmt.iteTrue (evalExpr_createAuction_err_slice_true evmCall hlen hsel) ?_
  exact ExecBlock.consRevert
    (ExecStmt.requireFalse (evalExpr_createAuction_error_long_enough_false evmCall hshort))

theorem auctionCreateAuctionBodyReverts_callFailure_errorStringOffsetMax
    {evm evmCall : EVM.State} {out : ByteArray} {off : Nat}
    (hcall : typedCallViaEVM auctionConfig evm
      (EVM.address (AccountAddress.ofNat
        ((UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨201⟩)
          solcAddrMask).toNat))) "mint" 0 [] (false, evmCall, out) true)
    (hlen : 4 ≤ out.size) (hsel : out.extract 0 4 = errorStringSelector)
    (hlong : 68 ≤ out.size)
    (hsmall : (out.extract 4 out.size).size < (2 : Nat) ^ 255)
    (hoff : ABI.readNat? (out.extract 4 out.size).toList 0 = some off)
    (hoffMax : ABI.solcMaxU64 < off) :
    ExecFuncBody auctionConfig { contract := auctionContract, locals := ∅ } evm createAuctionFn.body
      .reverted := by
  dsimp [createAuctionFn]
  refine ExecFuncBody.execBlockRevert ?_
  refine ExecBlock.consRevert ?_
  refine ExecStmt.checkedCallFail (evalExpr_createAuction_nouns evm)
    (evalExpr_createAuction_zero evm) (evalExprs_createAuction_mint_args evm) hcall ?_
  have hthen : ExecBlock auctionConfig (createAuctionErrFrame out) evmCall
      [ .require (errorStringReturndataLongEnough "err"),
        .letDecl "_errOffset" (some uint256) (errorStringOffsetDecode "err"),
        .require (.binary .le (.var "_errOffset") solcMaxU64Expr),
        .require (errorStringOffsetInBounds "err" "_errOffset"),
        .letDecl "_errLength" (some uint256) (errorStringLengthDecode "err" "_errOffset"),
        .require (.binary .le (.var "_errLength") solcMaxU64Expr),
        .require (errorStringPayloadInBounds "err" "_errOffset" "_errLength"),
        .require (errorStringAllocationWithinU64 "_errOffset" "_errLength"),
        .require (errorStringAllocationNoWrap "_errOffset" "_errLength"),
        .letDecl "_errString" (some .string) (.abiDecode .string (errorStringPayload "err")),
        .require (.unary .not (.storage pausedRef)),
        .assign .storage pausedRef (.boolLit true) ]
      .reverted := by
    simpa using
      (execCreateAuctionErrorStringOffsetMaxReverts (evm := evmCall) hlen hlong hsmall
        hoff hoffMax
        (tail := [
          .require (errorStringOffsetInBounds "err" "_errOffset"),
          .letDecl "_errLength" (some uint256) (errorStringLengthDecode "err" "_errOffset"),
          .require (.binary .le (.var "_errLength") solcMaxU64Expr),
          .require (errorStringPayloadInBounds "err" "_errOffset" "_errLength"),
          .require (errorStringAllocationWithinU64 "_errOffset" "_errLength"),
          .require (errorStringAllocationNoWrap "_errOffset" "_errLength"),
          .letDecl "_errString" (some .string) (.abiDecode .string (errorStringPayload "err")),
          .require (.unary .not (.storage pausedRef)),
          .assign .storage pausedRef (.boolLit true) ]))
  have hcatch : ExecBlock auctionConfig (createAuctionErrFrame out) evmCall
      [ .ite (.binary .eq (.bytesSlice (.var "err") (.intLit 0) (.intLit 4))
          (.bytesLit errorStringSelector))
        [ .require (errorStringReturndataLongEnough "err"),
          .letDecl "_errOffset" (some uint256) (errorStringOffsetDecode "err"),
          .require (.binary .le (.var "_errOffset") solcMaxU64Expr),
          .require (errorStringOffsetInBounds "err" "_errOffset"),
          .letDecl "_errLength" (some uint256) (errorStringLengthDecode "err" "_errOffset"),
          .require (.binary .le (.var "_errLength") solcMaxU64Expr),
          .require (errorStringPayloadInBounds "err" "_errOffset" "_errLength"),
          .require (errorStringAllocationWithinU64 "_errOffset" "_errLength"),
          .require (errorStringAllocationNoWrap "_errOffset" "_errLength"),
          .letDecl "_errString" (some .string) (.abiDecode .string (errorStringPayload "err")),
          .require (.unary .not (.storage pausedRef)),
          .assign .storage pausedRef (.boolLit true) ]
        [ .require (.boolLit false) ] ]
      .reverted := by
    exact ExecBlock.consRevert
      (ExecStmt.iteTrue
        (by
          simpa [createAuctionErrFrame] using
            evalExpr_createAuction_err_slice_true evmCall hlen hsel)
        hthen)
  simpa [createAuctionErrFrame] using hcatch

theorem auctionCreateAuctionBodyReverts_callFailure_errorStringOffsetBounds
    {evm evmCall : EVM.State} {out : ByteArray} {off : Nat}
    (hcall : typedCallViaEVM auctionConfig evm
      (EVM.address (AccountAddress.ofNat
        ((UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨201⟩)
          solcAddrMask).toNat))) "mint" 0 [] (false, evmCall, out) true)
    (hlen : 4 ≤ out.size) (hsel : out.extract 0 4 = errorStringSelector)
    (hlong : 68 ≤ out.size)
    (hsmall : (out.extract 4 out.size).size < (2 : Nat) ^ 255)
    (hoff : ABI.readNat? (out.extract 4 out.size).toList 0 = some off)
    (hoffMax : off ≤ ABI.solcMaxU64) (hoffBound : out.size < off + 36) :
    ExecFuncBody auctionConfig { contract := auctionContract, locals := ∅ } evm createAuctionFn.body
      .reverted := by
  dsimp [createAuctionFn]
  refine ExecFuncBody.execBlockRevert ?_
  refine ExecBlock.consRevert ?_
  refine ExecStmt.checkedCallFail (evalExpr_createAuction_nouns evm)
    (evalExpr_createAuction_zero evm) (evalExprs_createAuction_mint_args evm) hcall ?_
  have hthen : ExecBlock auctionConfig (createAuctionErrFrame out) evmCall
      [ .require (errorStringReturndataLongEnough "err"),
        .letDecl "_errOffset" (some uint256) (errorStringOffsetDecode "err"),
        .require (.binary .le (.var "_errOffset") solcMaxU64Expr),
        .require (errorStringOffsetInBounds "err" "_errOffset"),
        .letDecl "_errLength" (some uint256) (errorStringLengthDecode "err" "_errOffset"),
        .require (.binary .le (.var "_errLength") solcMaxU64Expr),
        .require (errorStringPayloadInBounds "err" "_errOffset" "_errLength"),
        .require (errorStringAllocationWithinU64 "_errOffset" "_errLength"),
        .require (errorStringAllocationNoWrap "_errOffset" "_errLength"),
        .letDecl "_errString" (some .string) (.abiDecode .string (errorStringPayload "err")),
        .require (.unary .not (.storage pausedRef)),
        .assign .storage pausedRef (.boolLit true) ]
      .reverted := by
    simpa using
      (execCreateAuctionErrorStringOffsetBoundsReverts (evm := evmCall) hlen hlong hsmall
        hoff hoffMax hoffBound
        (tail := [
          .letDecl "_errLength" (some uint256) (errorStringLengthDecode "err" "_errOffset"),
          .require (.binary .le (.var "_errLength") solcMaxU64Expr),
          .require (errorStringPayloadInBounds "err" "_errOffset" "_errLength"),
          .require (errorStringAllocationWithinU64 "_errOffset" "_errLength"),
          .require (errorStringAllocationNoWrap "_errOffset" "_errLength"),
          .letDecl "_errString" (some .string) (.abiDecode .string (errorStringPayload "err")),
          .require (.unary .not (.storage pausedRef)),
          .assign .storage pausedRef (.boolLit true) ]))
  have hcatch : ExecBlock auctionConfig (createAuctionErrFrame out) evmCall
      [ .ite (.binary .eq (.bytesSlice (.var "err") (.intLit 0) (.intLit 4))
          (.bytesLit errorStringSelector))
        [ .require (errorStringReturndataLongEnough "err"),
          .letDecl "_errOffset" (some uint256) (errorStringOffsetDecode "err"),
          .require (.binary .le (.var "_errOffset") solcMaxU64Expr),
          .require (errorStringOffsetInBounds "err" "_errOffset"),
          .letDecl "_errLength" (some uint256) (errorStringLengthDecode "err" "_errOffset"),
          .require (.binary .le (.var "_errLength") solcMaxU64Expr),
          .require (errorStringPayloadInBounds "err" "_errOffset" "_errLength"),
          .require (errorStringAllocationWithinU64 "_errOffset" "_errLength"),
          .require (errorStringAllocationNoWrap "_errOffset" "_errLength"),
          .letDecl "_errString" (some .string) (.abiDecode .string (errorStringPayload "err")),
          .require (.unary .not (.storage pausedRef)),
          .assign .storage pausedRef (.boolLit true) ]
        [ .require (.boolLit false) ] ]
      .reverted := by
    exact ExecBlock.consRevert
      (ExecStmt.iteTrue
        (by
          simpa [createAuctionErrFrame] using
            evalExpr_createAuction_err_slice_true evmCall hlen hsel)
        hthen)
  simpa [createAuctionErrFrame] using hcatch

theorem auctionCreateAuctionBodyReverts_callFailure_errorStringLengthMax
    {evm evmCall : EVM.State} {out : ByteArray} {off len : Nat}
    (hcall : typedCallViaEVM auctionConfig evm
      (EVM.address (AccountAddress.ofNat
        ((UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨201⟩)
          solcAddrMask).toNat))) "mint" 0 [] (false, evmCall, out) true)
    (hlen : 4 ≤ out.size) (hsel : out.extract 0 4 = errorStringSelector)
    (hlong : 68 ≤ out.size)
    (hsmall : (out.extract 4 out.size).size < (2 : Nat) ^ 255)
    (hoff : ABI.readNat? (out.extract 4 out.size).toList 0 = some off)
    (hoffMax : off ≤ ABI.solcMaxU64) (hoffBound : off + 36 ≤ out.size)
    (hlenWord : ABI.readNat? (out.extract 4 out.size).toList off = some len)
    (hlenMax : ABI.solcMaxU64 < len) :
    ExecFuncBody auctionConfig { contract := auctionContract, locals := ∅ } evm createAuctionFn.body
      .reverted := by
  dsimp [createAuctionFn]
  refine ExecFuncBody.execBlockRevert ?_
  refine ExecBlock.consRevert ?_
  refine ExecStmt.checkedCallFail (evalExpr_createAuction_nouns evm)
    (evalExpr_createAuction_zero evm) (evalExprs_createAuction_mint_args evm) hcall ?_
  have hthen : ExecBlock auctionConfig (createAuctionErrFrame out) evmCall
      [ .require (errorStringReturndataLongEnough "err"),
        .letDecl "_errOffset" (some uint256) (errorStringOffsetDecode "err"),
        .require (.binary .le (.var "_errOffset") solcMaxU64Expr),
        .require (errorStringOffsetInBounds "err" "_errOffset"),
        .letDecl "_errLength" (some uint256) (errorStringLengthDecode "err" "_errOffset"),
        .require (.binary .le (.var "_errLength") solcMaxU64Expr),
        .require (errorStringPayloadInBounds "err" "_errOffset" "_errLength"),
        .require (errorStringAllocationWithinU64 "_errOffset" "_errLength"),
        .require (errorStringAllocationNoWrap "_errOffset" "_errLength"),
        .letDecl "_errString" (some .string) (.abiDecode .string (errorStringPayload "err")),
        .require (.unary .not (.storage pausedRef)),
        .assign .storage pausedRef (.boolLit true) ]
      .reverted := by
    simpa using
      (execCreateAuctionErrorStringLengthMaxReverts (evm := evmCall) hlen hlong hsmall
        hoff hoffMax hoffBound hlenWord hlenMax
        (tail := [
          .require (errorStringPayloadInBounds "err" "_errOffset" "_errLength"),
          .require (errorStringAllocationWithinU64 "_errOffset" "_errLength"),
          .require (errorStringAllocationNoWrap "_errOffset" "_errLength"),
          .letDecl "_errString" (some .string) (.abiDecode .string (errorStringPayload "err")),
          .require (.unary .not (.storage pausedRef)),
          .assign .storage pausedRef (.boolLit true) ]))
  have hcatch : ExecBlock auctionConfig (createAuctionErrFrame out) evmCall
      [ .ite (.binary .eq (.bytesSlice (.var "err") (.intLit 0) (.intLit 4))
          (.bytesLit errorStringSelector))
        [ .require (errorStringReturndataLongEnough "err"),
          .letDecl "_errOffset" (some uint256) (errorStringOffsetDecode "err"),
          .require (.binary .le (.var "_errOffset") solcMaxU64Expr),
          .require (errorStringOffsetInBounds "err" "_errOffset"),
          .letDecl "_errLength" (some uint256) (errorStringLengthDecode "err" "_errOffset"),
          .require (.binary .le (.var "_errLength") solcMaxU64Expr),
          .require (errorStringPayloadInBounds "err" "_errOffset" "_errLength"),
          .require (errorStringAllocationWithinU64 "_errOffset" "_errLength"),
          .require (errorStringAllocationNoWrap "_errOffset" "_errLength"),
          .letDecl "_errString" (some .string) (.abiDecode .string (errorStringPayload "err")),
          .require (.unary .not (.storage pausedRef)),
          .assign .storage pausedRef (.boolLit true) ]
        [ .require (.boolLit false) ] ]
      .reverted := by
    exact ExecBlock.consRevert
      (ExecStmt.iteTrue
        (by
          simpa [createAuctionErrFrame] using
            evalExpr_createAuction_err_slice_true evmCall hlen hsel)
        hthen)
  simpa [createAuctionErrFrame] using hcatch

theorem auctionCreateAuctionBodyReverts_callFailure_errorStringPayloadBounds
    {evm evmCall : EVM.State} {out : ByteArray} {off len : Nat}
    (hcall : typedCallViaEVM auctionConfig evm
      (EVM.address (AccountAddress.ofNat
        ((UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨201⟩)
          solcAddrMask).toNat))) "mint" 0 [] (false, evmCall, out) true)
    (hlen : 4 ≤ out.size) (hsel : out.extract 0 4 = errorStringSelector)
    (hlong : 68 ≤ out.size)
    (hsmall : (out.extract 4 out.size).size < (2 : Nat) ^ 255)
    (hoff : ABI.readNat? (out.extract 4 out.size).toList 0 = some off)
    (hoffMax : off ≤ ABI.solcMaxU64) (hoffBound : off + 36 ≤ out.size)
    (hlenWord : ABI.readNat? (out.extract 4 out.size).toList off = some len)
    (hlenMax : len ≤ ABI.solcMaxU64) (hpayloadBound : out.size < off + len + 36) :
    ExecFuncBody auctionConfig { contract := auctionContract, locals := ∅ } evm createAuctionFn.body
      .reverted := by
  dsimp [createAuctionFn]
  refine ExecFuncBody.execBlockRevert ?_
  refine ExecBlock.consRevert ?_
  refine ExecStmt.checkedCallFail (evalExpr_createAuction_nouns evm)
    (evalExpr_createAuction_zero evm) (evalExprs_createAuction_mint_args evm) hcall ?_
  have hthen : ExecBlock auctionConfig (createAuctionErrFrame out) evmCall
      [ .require (errorStringReturndataLongEnough "err"),
        .letDecl "_errOffset" (some uint256) (errorStringOffsetDecode "err"),
        .require (.binary .le (.var "_errOffset") solcMaxU64Expr),
        .require (errorStringOffsetInBounds "err" "_errOffset"),
        .letDecl "_errLength" (some uint256) (errorStringLengthDecode "err" "_errOffset"),
        .require (.binary .le (.var "_errLength") solcMaxU64Expr),
        .require (errorStringPayloadInBounds "err" "_errOffset" "_errLength"),
        .require (errorStringAllocationWithinU64 "_errOffset" "_errLength"),
        .require (errorStringAllocationNoWrap "_errOffset" "_errLength"),
        .letDecl "_errString" (some .string) (.abiDecode .string (errorStringPayload "err")),
        .require (.unary .not (.storage pausedRef)),
        .assign .storage pausedRef (.boolLit true) ]
      .reverted := by
    simpa using
      (execCreateAuctionErrorStringPayloadBoundsReverts (evm := evmCall) hlen hlong hsmall
        hoff hoffMax hoffBound hlenWord hlenMax hpayloadBound
        (tail := [
          .require (errorStringAllocationWithinU64 "_errOffset" "_errLength"),
          .require (errorStringAllocationNoWrap "_errOffset" "_errLength"),
          .letDecl "_errString" (some .string) (.abiDecode .string (errorStringPayload "err")),
          .require (.unary .not (.storage pausedRef)),
          .assign .storage pausedRef (.boolLit true) ]))
  have hcatch : ExecBlock auctionConfig (createAuctionErrFrame out) evmCall
      [ .ite (.binary .eq (.bytesSlice (.var "err") (.intLit 0) (.intLit 4))
          (.bytesLit errorStringSelector))
        [ .require (errorStringReturndataLongEnough "err"),
          .letDecl "_errOffset" (some uint256) (errorStringOffsetDecode "err"),
          .require (.binary .le (.var "_errOffset") solcMaxU64Expr),
          .require (errorStringOffsetInBounds "err" "_errOffset"),
          .letDecl "_errLength" (some uint256) (errorStringLengthDecode "err" "_errOffset"),
          .require (.binary .le (.var "_errLength") solcMaxU64Expr),
          .require (errorStringPayloadInBounds "err" "_errOffset" "_errLength"),
          .require (errorStringAllocationWithinU64 "_errOffset" "_errLength"),
          .require (errorStringAllocationNoWrap "_errOffset" "_errLength"),
          .letDecl "_errString" (some .string) (.abiDecode .string (errorStringPayload "err")),
          .require (.unary .not (.storage pausedRef)),
          .assign .storage pausedRef (.boolLit true) ]
        [ .require (.boolLit false) ] ]
      .reverted := by
    exact ExecBlock.consRevert
      (ExecStmt.iteTrue
        (by
          simpa [createAuctionErrFrame] using
            evalExpr_createAuction_err_slice_true evmCall hlen hsel)
        hthen)
  simpa [createAuctionErrFrame] using hcatch

theorem auctionCreateAuctionBodyReverts_callFailure_errorStringAllocU64
    {evm evmCall : EVM.State} {out : ByteArray} {off len : Nat}
    (hcall : typedCallViaEVM auctionConfig evm
      (EVM.address (AccountAddress.ofNat
        ((UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨201⟩)
          solcAddrMask).toNat))) "mint" 0 [] (false, evmCall, out) true)
    (hlen : 4 ≤ out.size) (hsel : out.extract 0 4 = errorStringSelector)
    (hlong : 68 ≤ out.size)
    (hsmall : (out.extract 4 out.size).size < (2 : Nat) ^ 255)
    (hoff : ABI.readNat? (out.extract 4 out.size).toList 0 = some off)
    (hoffMax : off ≤ ABI.solcMaxU64) (hoffBound : off + 36 ≤ out.size)
    (hlenWord : ABI.readNat? (out.extract 4 out.size).toList off = some len)
    (hlenMax : len ≤ ABI.solcMaxU64) (hpayloadBound : off + len + 36 ≤ out.size)
    (halloc : ABI.solcMaxU64 < errorStringNewFreeNat off len) :
    ExecFuncBody auctionConfig { contract := auctionContract, locals := ∅ } evm createAuctionFn.body
      .reverted := by
  dsimp [createAuctionFn]
  refine ExecFuncBody.execBlockRevert ?_
  refine ExecBlock.consRevert ?_
  refine ExecStmt.checkedCallFail (evalExpr_createAuction_nouns evm)
    (evalExpr_createAuction_zero evm) (evalExprs_createAuction_mint_args evm) hcall ?_
  have hthen : ExecBlock auctionConfig (createAuctionErrFrame out) evmCall
      [ .require (errorStringReturndataLongEnough "err"),
        .letDecl "_errOffset" (some uint256) (errorStringOffsetDecode "err"),
        .require (.binary .le (.var "_errOffset") solcMaxU64Expr),
        .require (errorStringOffsetInBounds "err" "_errOffset"),
        .letDecl "_errLength" (some uint256) (errorStringLengthDecode "err" "_errOffset"),
        .require (.binary .le (.var "_errLength") solcMaxU64Expr),
        .require (errorStringPayloadInBounds "err" "_errOffset" "_errLength"),
        .require (errorStringAllocationWithinU64 "_errOffset" "_errLength"),
        .require (errorStringAllocationNoWrap "_errOffset" "_errLength"),
        .letDecl "_errString" (some .string) (.abiDecode .string (errorStringPayload "err")),
        .require (.unary .not (.storage pausedRef)),
        .assign .storage pausedRef (.boolLit true) ]
      .reverted := by
    simpa using
      (execCreateAuctionErrorStringAllocU64Reverts (evm := evmCall) hlen hlong hsmall
        hoff hoffMax hoffBound hlenWord hlenMax hpayloadBound halloc
        (tail := [
          .require (errorStringAllocationNoWrap "_errOffset" "_errLength"),
          .letDecl "_errString" (some .string) (.abiDecode .string (errorStringPayload "err")),
          .require (.unary .not (.storage pausedRef)),
          .assign .storage pausedRef (.boolLit true) ]))
  have hcatch : ExecBlock auctionConfig (createAuctionErrFrame out) evmCall
      [ .ite (.binary .eq (.bytesSlice (.var "err") (.intLit 0) (.intLit 4))
          (.bytesLit errorStringSelector))
        [ .require (errorStringReturndataLongEnough "err"),
          .letDecl "_errOffset" (some uint256) (errorStringOffsetDecode "err"),
          .require (.binary .le (.var "_errOffset") solcMaxU64Expr),
          .require (errorStringOffsetInBounds "err" "_errOffset"),
          .letDecl "_errLength" (some uint256) (errorStringLengthDecode "err" "_errOffset"),
          .require (.binary .le (.var "_errLength") solcMaxU64Expr),
          .require (errorStringPayloadInBounds "err" "_errOffset" "_errLength"),
          .require (errorStringAllocationWithinU64 "_errOffset" "_errLength"),
          .require (errorStringAllocationNoWrap "_errOffset" "_errLength"),
          .letDecl "_errString" (some .string) (.abiDecode .string (errorStringPayload "err")),
          .require (.unary .not (.storage pausedRef)),
          .assign .storage pausedRef (.boolLit true) ]
        [ .require (.boolLit false) ] ]
      .reverted := by
    exact ExecBlock.consRevert
      (ExecStmt.iteTrue
        (by
          simpa [createAuctionErrFrame] using
            evalExpr_createAuction_err_slice_true evmCall hlen hsel)
        hthen)
  simpa [createAuctionErrFrame] using hcatch

theorem auctionCreateAuctionBodyReverts_callFailure_errorStringDecode
    {evm evmCall : EVM.State} {out : ByteArray} {off len : Nat}
    (hcall : typedCallViaEVM auctionConfig evm
      (EVM.address (AccountAddress.ofNat
        ((UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨201⟩)
          solcAddrMask).toNat))) "mint" 0 [] (false, evmCall, out) true)
    (hlen : 4 ≤ out.size) (hsel : out.extract 0 4 = errorStringSelector)
    (hlong : 68 ≤ out.size)
    (hsmall : (out.extract 4 out.size).size < (2 : Nat) ^ 255)
    (hoff : ABI.readNat? (out.extract 4 out.size).toList 0 = some off)
    (hoffMax : off ≤ ABI.solcMaxU64)
    (hoffBound : off + 36 ≤ out.size)
    (hlenWord : ABI.readNat? (out.extract 4 out.size).toList off = some len)
    (hlenMax : len ≤ ABI.solcMaxU64)
    (hpayloadBound : off + len + 36 ≤ out.size)
    (halloc : errorStringNewFreeNat off len ≤ ABI.solcMaxU64)
    (hdec : ABI.decodeReturnValue? .string (out.extract 4 out.size) = none) :
    ExecFuncBody auctionConfig { contract := auctionContract, locals := ∅ } evm createAuctionFn.body
      .reverted := by
  dsimp [createAuctionFn]
  refine ExecFuncBody.execBlockRevert ?_
  refine ExecBlock.consRevert ?_
  refine ExecStmt.checkedCallFail (evalExpr_createAuction_nouns evm)
    (evalExpr_createAuction_zero evm) (evalExprs_createAuction_mint_args evm) hcall ?_
  have hthen : ExecBlock auctionConfig (createAuctionErrFrame out) evmCall
      [ .require (errorStringReturndataLongEnough "err"),
        .letDecl "_errOffset" (some uint256) (errorStringOffsetDecode "err"),
        .require (.binary .le (.var "_errOffset") solcMaxU64Expr),
        .require (errorStringOffsetInBounds "err" "_errOffset"),
        .letDecl "_errLength" (some uint256) (errorStringLengthDecode "err" "_errOffset"),
        .require (.binary .le (.var "_errLength") solcMaxU64Expr),
        .require (errorStringPayloadInBounds "err" "_errOffset" "_errLength"),
        .require (errorStringAllocationWithinU64 "_errOffset" "_errLength"),
        .require (errorStringAllocationNoWrap "_errOffset" "_errLength"),
        .letDecl "_errString" (some .string) (.abiDecode .string (errorStringPayload "err")),
        .require (.unary .not (.storage pausedRef)),
        .assign .storage pausedRef (.boolLit true) ]
      .reverted :=
    execCreateAuctionErrorStringThenDecodeReverts hlen hlong hsmall hoff hoffMax hoffBound
      hlenWord hlenMax hpayloadBound halloc hdec
  have hcatch : ExecBlock auctionConfig (createAuctionErrFrame out) evmCall
      [ .ite (.binary .eq (.bytesSlice (.var "err") (.intLit 0) (.intLit 4))
          (.bytesLit errorStringSelector))
        [ .require (errorStringReturndataLongEnough "err"),
          .letDecl "_errOffset" (some uint256) (errorStringOffsetDecode "err"),
          .require (.binary .le (.var "_errOffset") solcMaxU64Expr),
          .require (errorStringOffsetInBounds "err" "_errOffset"),
          .letDecl "_errLength" (some uint256) (errorStringLengthDecode "err" "_errOffset"),
          .require (.binary .le (.var "_errLength") solcMaxU64Expr),
          .require (errorStringPayloadInBounds "err" "_errOffset" "_errLength"),
          .require (errorStringAllocationWithinU64 "_errOffset" "_errLength"),
          .require (errorStringAllocationNoWrap "_errOffset" "_errLength"),
          .letDecl "_errString" (some .string) (.abiDecode .string (errorStringPayload "err")),
          .require (.unary .not (.storage pausedRef)),
          .assign .storage pausedRef (.boolLit true) ]
        [ .require (.boolLit false) ] ]
      .reverted := by
    exact ExecBlock.consRevert
      (ExecStmt.iteTrue
        (by
          simpa [createAuctionErrFrame] using
            evalExpr_createAuction_err_slice_true evmCall hlen hsel)
        hthen)
  simpa [createAuctionErrFrame] using hcatch

theorem auctionCreateAuctionBodyReverts_callFailure_errorStringPaused
    {evm evmCall : EVM.State} {out : ByteArray} {off len : Nat} {decoded : Value}
    (hcall : typedCallViaEVM auctionConfig evm
      (EVM.address (AccountAddress.ofNat
        ((UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨201⟩)
          solcAddrMask).toNat))) "mint" 0 [] (false, evmCall, out) true)
    (hlen : 4 ≤ out.size) (hsel : out.extract 0 4 = errorStringSelector)
    (hlong : 68 ≤ out.size)
    (hsmall : (out.extract 4 out.size).size < (2 : Nat) ^ 255)
    (hoff : ABI.readNat? (out.extract 4 out.size).toList 0 = some off)
    (hoffMax : off ≤ ABI.solcMaxU64)
    (hoffBound : off + 36 ≤ out.size)
    (hlenWord : ABI.readNat? (out.extract 4 out.size).toList off = some len)
    (hlenMax : len ≤ ABI.solcMaxU64)
    (hpayloadBound : off + len + 36 ≤ out.size)
    (halloc : errorStringNewFreeNat off len ≤ ABI.solcMaxU64)
    (hdec : ABI.decodeReturnValue? .string (out.extract 4 out.size) = some decoded)
    (hpaused :
      UInt256.land (Solm.EVM.storageLoad evmCall evmCall.executionEnv.codeOwner ⟨51⟩) ⟨255⟩ ≠
        ⟨0⟩) :
    ExecFuncBody auctionConfig { contract := auctionContract, locals := ∅ } evm createAuctionFn.body
      .reverted := by
  dsimp [createAuctionFn]
  refine ExecFuncBody.execBlockRevert ?_
  refine ExecBlock.consRevert ?_
  refine ExecStmt.checkedCallFail (evalExpr_createAuction_nouns evm)
    (evalExpr_createAuction_zero evm) (evalExprs_createAuction_mint_args evm) hcall ?_
  have hthen : ExecBlock auctionConfig (createAuctionErrFrame out) evmCall
      [ .require (errorStringReturndataLongEnough "err"),
        .letDecl "_errOffset" (some uint256) (errorStringOffsetDecode "err"),
        .require (.binary .le (.var "_errOffset") solcMaxU64Expr),
        .require (errorStringOffsetInBounds "err" "_errOffset"),
        .letDecl "_errLength" (some uint256) (errorStringLengthDecode "err" "_errOffset"),
        .require (.binary .le (.var "_errLength") solcMaxU64Expr),
        .require (errorStringPayloadInBounds "err" "_errOffset" "_errLength"),
        .require (errorStringAllocationWithinU64 "_errOffset" "_errLength"),
        .require (errorStringAllocationNoWrap "_errOffset" "_errLength"),
        .letDecl "_errString" (some .string) (.abiDecode .string (errorStringPayload "err")),
        .require (.unary .not (.storage pausedRef)),
        .assign .storage pausedRef (.boolLit true) ]
      .reverted :=
    execCreateAuctionErrorStringThenPausedReverts hlen hlong hsmall hoff hoffMax hoffBound
      hlenWord hlenMax hpayloadBound halloc hdec hpaused
  have hcatch : ExecBlock auctionConfig (createAuctionErrFrame out) evmCall
      [ .ite (.binary .eq (.bytesSlice (.var "err") (.intLit 0) (.intLit 4))
          (.bytesLit errorStringSelector))
        [ .require (errorStringReturndataLongEnough "err"),
          .letDecl "_errOffset" (some uint256) (errorStringOffsetDecode "err"),
          .require (.binary .le (.var "_errOffset") solcMaxU64Expr),
          .require (errorStringOffsetInBounds "err" "_errOffset"),
          .letDecl "_errLength" (some uint256) (errorStringLengthDecode "err" "_errOffset"),
          .require (.binary .le (.var "_errLength") solcMaxU64Expr),
          .require (errorStringPayloadInBounds "err" "_errOffset" "_errLength"),
          .require (errorStringAllocationWithinU64 "_errOffset" "_errLength"),
          .require (errorStringAllocationNoWrap "_errOffset" "_errLength"),
          .letDecl "_errString" (some .string) (.abiDecode .string (errorStringPayload "err")),
          .require (.unary .not (.storage pausedRef)),
          .assign .storage pausedRef (.boolLit true) ]
        [ .require (.boolLit false) ] ]
      .reverted := by
    exact ExecBlock.consRevert
      (ExecStmt.iteTrue
        (by
          simpa [createAuctionErrFrame] using
            evalExpr_createAuction_err_slice_true evmCall hlen hsel)
        hthen)
  simpa [createAuctionErrFrame] using hcatch

theorem auctionUnpauseBodyReverts_create_callFailure_empty (evm evmCall : EVM.State)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (howner :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨151⟩) solcAddrMask =
        auctionSourceWord evm.executionEnv)
    (hpaused :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨51⟩) ⟨255⟩ ≠
        ⟨0⟩)
    (hcond :
      evalExpr? auctionConfig { contract := auctionContract, locals := ∅ } (auctionUnpausePostState evm)
        (.binary .or (.binary .eq (.storage (aField "startTime")) (.intLit 0))
          (.storage (aField "settled"))) = .ok (.bool true))
    (hcall : typedCallViaEVM auctionConfig (auctionUnpausePostState evm)
      (EVM.address (AccountAddress.ofNat
        ((UInt256.land
          (Solm.EVM.storageLoad (auctionUnpausePostState evm)
            (auctionUnpausePostState evm).executionEnv.codeOwner ⟨201⟩)
          solcAddrMask).toNat))) "mint" 0 [] (false, evmCall, ByteArray.empty) true) :
    ExecTransitionBody auctionConfig auctionContract evm ∅ unpauseTransition.body .reverted := by
  let evm' := auctionUnpausePostState evm
  refine ExecFuncBody.execBlockRevert ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalExpr_pause_owner_eq_true evm howner)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalExpr_pause_paused_true evm hpaused)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_unpause_false evm) (auctionUnpauseAssign evm)) ?_
  refine ExecBlock.consRevert (ExecStmt.iteTrue (by simpa [evm'] using hcond) ?_)
  exact ExecBlock.consRevert (internalCallFunctionRevert
    (cfg := auctionConfig) (caller := { contract := auctionContract, locals := ∅ })
    (evm := evm') (name := "_createAuction") (args := []) (retVar := "_c")
    (argVals := []) (callee := createAuctionFn) (locals := ∅)
    (by rfl) (by rfl) (by rfl)
    (auctionCreateAuctionBodyReverts_callFailure_empty hcall))

theorem auctionUnpauseBodyReverts_create_callFailure_short (evm evmCall : EVM.State)
    {out : ByteArray}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (howner :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨151⟩) solcAddrMask =
        auctionSourceWord evm.executionEnv)
    (hpaused :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨51⟩) ⟨255⟩ ≠
        ⟨0⟩)
    (hcond :
      evalExpr? auctionConfig { contract := auctionContract, locals := ∅ } (auctionUnpausePostState evm)
        (.binary .or (.binary .eq (.storage (aField "startTime")) (.intLit 0))
          (.storage (aField "settled"))) = .ok (.bool true))
    (hcall : typedCallViaEVM auctionConfig (auctionUnpausePostState evm)
      (EVM.address (AccountAddress.ofNat
        ((UInt256.land
          (Solm.EVM.storageLoad (auctionUnpausePostState evm)
            (auctionUnpausePostState evm).executionEnv.codeOwner ⟨201⟩)
          solcAddrMask).toNat))) "mint" 0 [] (false, evmCall, out) true)
    (hshort : out.size < 4) :
    ExecTransitionBody auctionConfig auctionContract evm ∅ unpauseTransition.body .reverted := by
  let evm' := auctionUnpausePostState evm
  refine ExecFuncBody.execBlockRevert ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalExpr_pause_owner_eq_true evm howner)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalExpr_pause_paused_true evm hpaused)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_unpause_false evm) (auctionUnpauseAssign evm)) ?_
  refine ExecBlock.consRevert (ExecStmt.iteTrue (by simpa [evm'] using hcond) ?_)
  exact ExecBlock.consRevert (internalCallFunctionRevert
    (cfg := auctionConfig) (caller := { contract := auctionContract, locals := ∅ })
    (evm := evm') (name := "_createAuction") (args := []) (retVar := "_c")
    (argVals := []) (callee := createAuctionFn) (locals := ∅)
    (by rfl) (by rfl) (by rfl)
    (auctionCreateAuctionBodyReverts_callFailure_short hcall hshort))

theorem auctionUnpauseBodyReverts_create_callFailure_nonError (evm evmCall : EVM.State)
    {out : ByteArray}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (howner :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨151⟩) solcAddrMask =
        auctionSourceWord evm.executionEnv)
    (hpaused :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨51⟩) ⟨255⟩ ≠
        ⟨0⟩)
    (hcond :
      evalExpr? auctionConfig { contract := auctionContract, locals := ∅ } (auctionUnpausePostState evm)
        (.binary .or (.binary .eq (.storage (aField "startTime")) (.intLit 0))
          (.storage (aField "settled"))) = .ok (.bool true))
    (hcall : typedCallViaEVM auctionConfig (auctionUnpausePostState evm)
      (EVM.address (AccountAddress.ofNat
        ((UInt256.land
          (Solm.EVM.storageLoad (auctionUnpausePostState evm)
            (auctionUnpausePostState evm).executionEnv.codeOwner ⟨201⟩)
          solcAddrMask).toNat))) "mint" 0 [] (false, evmCall, out) true)
    (hlen : 4 ≤ out.size) (hsel : out.extract 0 4 ≠ errorStringSelector) :
    ExecTransitionBody auctionConfig auctionContract evm ∅ unpauseTransition.body .reverted := by
  let evm' := auctionUnpausePostState evm
  refine ExecFuncBody.execBlockRevert ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalExpr_pause_owner_eq_true evm howner)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalExpr_pause_paused_true evm hpaused)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_unpause_false evm) (auctionUnpauseAssign evm)) ?_
  refine ExecBlock.consRevert (ExecStmt.iteTrue (by simpa [evm'] using hcond) ?_)
  exact ExecBlock.consRevert (internalCallFunctionRevert
    (cfg := auctionConfig) (caller := { contract := auctionContract, locals := ∅ })
    (evm := evm') (name := "_createAuction") (args := []) (retVar := "_c")
    (argVals := []) (callee := createAuctionFn) (locals := ∅)
    (by rfl) (by rfl) (by rfl)
    (auctionCreateAuctionBodyReverts_callFailure_nonError hcall hlen hsel))

theorem auctionUnpauseBodyReturns_create_callFailure_errorString (evm evmCall : EVM.State)
    {out : ByteArray} {off len : Nat} {decoded : Value}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (howner :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨151⟩) solcAddrMask =
        auctionSourceWord evm.executionEnv)
    (hpaused :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨51⟩) ⟨255⟩ ≠
        ⟨0⟩)
    (hcond :
      evalExpr? auctionConfig { contract := auctionContract, locals := ∅ } (auctionUnpausePostState evm)
        (.binary .or (.binary .eq (.storage (aField "startTime")) (.intLit 0))
          (.storage (aField "settled"))) = .ok (.bool true))
    (hcall : typedCallViaEVM auctionConfig (auctionUnpausePostState evm)
      (EVM.address (AccountAddress.ofNat
        ((UInt256.land
          (Solm.EVM.storageLoad (auctionUnpausePostState evm)
            (auctionUnpausePostState evm).executionEnv.codeOwner ⟨201⟩)
          solcAddrMask).toNat))) "mint" 0 [] (false, evmCall, out) true)
    (hlen : 4 ≤ out.size) (hsel : out.extract 0 4 = errorStringSelector)
    (hlong : 68 ≤ out.size)
    (hsmall : (out.extract 4 out.size).size < (2 : Nat) ^ 255)
    (hoff : ABI.readNat? (out.extract 4 out.size).toList 0 = some off)
    (hoffMax : off ≤ ABI.solcMaxU64)
    (hoffBound : off + 36 ≤ out.size)
    (hlenWord : ABI.readNat? (out.extract 4 out.size).toList off = some len)
    (hlenMax : len ≤ ABI.solcMaxU64)
    (hpayloadBound : off + len + 36 ≤ out.size)
    (halloc : errorStringNewFreeNat off len ≤ ABI.solcMaxU64)
    (hdec : ABI.decodeReturnValue? .string (out.extract 4 out.size) = some decoded)
    (hnotPaused :
      UInt256.land (Solm.EVM.storageLoad evmCall evmCall.executionEnv.codeOwner ⟨51⟩) ⟨255⟩ =
        ⟨0⟩) :
    ExecTransitionBody auctionConfig auctionContract evm ∅ unpauseTransition.body
      (.returned (resumeAfterInternalCall { contract := auctionContract, locals := ∅ } "_c" none)
        (auctionPausePostState evmCall) none) := by
  let evm' := auctionUnpausePostState evm
  refine ExecFuncBody.execBlockOK ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalExpr_pause_owner_eq_true evm howner)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalExpr_pause_paused_true evm hpaused)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_unpause_false evm) (auctionUnpauseAssign evm)) ?_
  refine ExecBlock.consNormal (ExecStmt.iteTrue (by simpa [evm'] using hcond) ?_) ExecBlock.nil
  refine ExecBlock.consNormal ?_ ExecBlock.nil
  exact internalCallFunctionReturn
    (cfg := auctionConfig) (caller := { contract := auctionContract, locals := ∅ })
    (evm := evm') (calleeEvm := auctionPausePostState evmCall)
    (name := "_createAuction") (args := []) (retVar := "_c") (argVals := [])
    (callee := createAuctionFn) (locals := ∅)
      (calleeSolm := createAuctionErrDecodedFrame out off len decoded)
      (value := none) (by rfl) (by rfl) (by rfl)
      (auctionCreateAuctionBodyReturns_callFailure_errorString hcall hlen hsel hlong hsmall
        hoff hoffMax hoffBound hlenWord hlenMax hpayloadBound halloc hdec hnotPaused)

theorem auctionUnpauseBodyReverts_create_callFailure_errorStringShort
    (evm evmCall : EVM.State) {out : ByteArray}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (howner :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨151⟩) solcAddrMask =
        auctionSourceWord evm.executionEnv)
    (hpaused :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨51⟩) ⟨255⟩ ≠
        ⟨0⟩)
    (hcond :
      evalExpr? auctionConfig { contract := auctionContract, locals := ∅ } (auctionUnpausePostState evm)
        (.binary .or (.binary .eq (.storage (aField "startTime")) (.intLit 0))
          (.storage (aField "settled"))) = .ok (.bool true))
    (hcall : typedCallViaEVM auctionConfig (auctionUnpausePostState evm)
      (EVM.address (AccountAddress.ofNat
        ((UInt256.land
          (Solm.EVM.storageLoad (auctionUnpausePostState evm)
            (auctionUnpausePostState evm).executionEnv.codeOwner ⟨201⟩)
          solcAddrMask).toNat))) "mint" 0 [] (false, evmCall, out) true)
    (hlen : 4 ≤ out.size) (hsel : out.extract 0 4 = errorStringSelector)
    (hshort : out.size < 68) :
    ExecTransitionBody auctionConfig auctionContract evm ∅ unpauseTransition.body .reverted := by
  let evm' := auctionUnpausePostState evm
  refine ExecFuncBody.execBlockRevert ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalExpr_pause_owner_eq_true evm howner)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalExpr_pause_paused_true evm hpaused)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_unpause_false evm) (auctionUnpauseAssign evm)) ?_
  refine ExecBlock.consRevert (ExecStmt.iteTrue (by simpa [evm'] using hcond) ?_)
  exact ExecBlock.consRevert (internalCallFunctionRevert
    (cfg := auctionConfig) (caller := { contract := auctionContract, locals := ∅ })
    (evm := evm') (name := "_createAuction") (args := []) (retVar := "_c")
    (argVals := []) (callee := createAuctionFn) (locals := ∅)
    (by rfl) (by rfl) (by rfl)
    (auctionCreateAuctionBodyReverts_callFailure_errorStringShort hcall hlen hsel hshort))

theorem auctionUnpauseBodyReverts_create_callFailure_errorStringOffsetMax
    (evm evmCall : EVM.State) {out : ByteArray} {off : Nat}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (howner :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨151⟩) solcAddrMask =
        auctionSourceWord evm.executionEnv)
    (hpaused :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨51⟩) ⟨255⟩ ≠
        ⟨0⟩)
    (hcond :
      evalExpr? auctionConfig { contract := auctionContract, locals := ∅ } (auctionUnpausePostState evm)
        (.binary .or (.binary .eq (.storage (aField "startTime")) (.intLit 0))
          (.storage (aField "settled"))) = .ok (.bool true))
    (hcall : typedCallViaEVM auctionConfig (auctionUnpausePostState evm)
      (EVM.address (AccountAddress.ofNat
        ((UInt256.land
          (Solm.EVM.storageLoad (auctionUnpausePostState evm)
            (auctionUnpausePostState evm).executionEnv.codeOwner ⟨201⟩)
          solcAddrMask).toNat))) "mint" 0 [] (false, evmCall, out) true)
    (hlen : 4 ≤ out.size) (hsel : out.extract 0 4 = errorStringSelector)
    (hlong : 68 ≤ out.size)
    (hsmall : (out.extract 4 out.size).size < (2 : Nat) ^ 255)
    (hoff : ABI.readNat? (out.extract 4 out.size).toList 0 = some off)
    (hoffMax : ABI.solcMaxU64 < off) :
    ExecTransitionBody auctionConfig auctionContract evm ∅ unpauseTransition.body .reverted := by
  let evm' := auctionUnpausePostState evm
  refine ExecFuncBody.execBlockRevert ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalExpr_pause_owner_eq_true evm howner)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalExpr_pause_paused_true evm hpaused)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_unpause_false evm) (auctionUnpauseAssign evm)) ?_
  refine ExecBlock.consRevert (ExecStmt.iteTrue (by simpa [evm'] using hcond) ?_)
  exact ExecBlock.consRevert (internalCallFunctionRevert
    (cfg := auctionConfig) (caller := { contract := auctionContract, locals := ∅ })
    (evm := evm') (name := "_createAuction") (args := []) (retVar := "_c")
    (argVals := []) (callee := createAuctionFn) (locals := ∅)
    (by rfl) (by rfl) (by rfl)
    (auctionCreateAuctionBodyReverts_callFailure_errorStringOffsetMax hcall hlen hsel hlong
      hsmall hoff hoffMax))

theorem auctionUnpauseBodyReverts_create_callFailure_errorStringOffsetBounds
    (evm evmCall : EVM.State) {out : ByteArray} {off : Nat}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (howner :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨151⟩) solcAddrMask =
        auctionSourceWord evm.executionEnv)
    (hpaused :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨51⟩) ⟨255⟩ ≠
        ⟨0⟩)
    (hcond :
      evalExpr? auctionConfig { contract := auctionContract, locals := ∅ } (auctionUnpausePostState evm)
        (.binary .or (.binary .eq (.storage (aField "startTime")) (.intLit 0))
          (.storage (aField "settled"))) = .ok (.bool true))
    (hcall : typedCallViaEVM auctionConfig (auctionUnpausePostState evm)
      (EVM.address (AccountAddress.ofNat
        ((UInt256.land
          (Solm.EVM.storageLoad (auctionUnpausePostState evm)
            (auctionUnpausePostState evm).executionEnv.codeOwner ⟨201⟩)
          solcAddrMask).toNat))) "mint" 0 [] (false, evmCall, out) true)
    (hlen : 4 ≤ out.size) (hsel : out.extract 0 4 = errorStringSelector)
    (hlong : 68 ≤ out.size)
    (hsmall : (out.extract 4 out.size).size < (2 : Nat) ^ 255)
    (hoff : ABI.readNat? (out.extract 4 out.size).toList 0 = some off)
    (hoffMax : off ≤ ABI.solcMaxU64) (hoffBound : out.size < off + 36) :
    ExecTransitionBody auctionConfig auctionContract evm ∅ unpauseTransition.body .reverted := by
  let evm' := auctionUnpausePostState evm
  refine ExecFuncBody.execBlockRevert ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalExpr_pause_owner_eq_true evm howner)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalExpr_pause_paused_true evm hpaused)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_unpause_false evm) (auctionUnpauseAssign evm)) ?_
  refine ExecBlock.consRevert (ExecStmt.iteTrue (by simpa [evm'] using hcond) ?_)
  exact ExecBlock.consRevert (internalCallFunctionRevert
    (cfg := auctionConfig) (caller := { contract := auctionContract, locals := ∅ })
    (evm := evm') (name := "_createAuction") (args := []) (retVar := "_c")
    (argVals := []) (callee := createAuctionFn) (locals := ∅)
    (by rfl) (by rfl) (by rfl)
    (auctionCreateAuctionBodyReverts_callFailure_errorStringOffsetBounds hcall hlen hsel hlong
      hsmall hoff hoffMax hoffBound))

theorem auctionUnpauseBodyReverts_create_callFailure_errorStringLengthMax
    (evm evmCall : EVM.State) {out : ByteArray} {off len : Nat}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (howner :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨151⟩) solcAddrMask =
        auctionSourceWord evm.executionEnv)
    (hpaused :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨51⟩) ⟨255⟩ ≠
        ⟨0⟩)
    (hcond :
      evalExpr? auctionConfig { contract := auctionContract, locals := ∅ } (auctionUnpausePostState evm)
        (.binary .or (.binary .eq (.storage (aField "startTime")) (.intLit 0))
          (.storage (aField "settled"))) = .ok (.bool true))
    (hcall : typedCallViaEVM auctionConfig (auctionUnpausePostState evm)
      (EVM.address (AccountAddress.ofNat
        ((UInt256.land
          (Solm.EVM.storageLoad (auctionUnpausePostState evm)
            (auctionUnpausePostState evm).executionEnv.codeOwner ⟨201⟩)
          solcAddrMask).toNat))) "mint" 0 [] (false, evmCall, out) true)
    (hlen : 4 ≤ out.size) (hsel : out.extract 0 4 = errorStringSelector)
    (hlong : 68 ≤ out.size)
    (hsmall : (out.extract 4 out.size).size < (2 : Nat) ^ 255)
    (hoff : ABI.readNat? (out.extract 4 out.size).toList 0 = some off)
    (hoffMax : off ≤ ABI.solcMaxU64) (hoffBound : off + 36 ≤ out.size)
    (hlenWord : ABI.readNat? (out.extract 4 out.size).toList off = some len)
    (hlenMax : ABI.solcMaxU64 < len) :
    ExecTransitionBody auctionConfig auctionContract evm ∅ unpauseTransition.body .reverted := by
  let evm' := auctionUnpausePostState evm
  refine ExecFuncBody.execBlockRevert ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalExpr_pause_owner_eq_true evm howner)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalExpr_pause_paused_true evm hpaused)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_unpause_false evm) (auctionUnpauseAssign evm)) ?_
  refine ExecBlock.consRevert (ExecStmt.iteTrue (by simpa [evm'] using hcond) ?_)
  exact ExecBlock.consRevert (internalCallFunctionRevert
    (cfg := auctionConfig) (caller := { contract := auctionContract, locals := ∅ })
    (evm := evm') (name := "_createAuction") (args := []) (retVar := "_c")
    (argVals := []) (callee := createAuctionFn) (locals := ∅)
    (by rfl) (by rfl) (by rfl)
    (auctionCreateAuctionBodyReverts_callFailure_errorStringLengthMax hcall hlen hsel hlong
      hsmall hoff hoffMax hoffBound hlenWord hlenMax))

theorem auctionUnpauseBodyReverts_create_callFailure_errorStringPayloadBounds
    (evm evmCall : EVM.State) {out : ByteArray} {off len : Nat}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (howner :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨151⟩) solcAddrMask =
        auctionSourceWord evm.executionEnv)
    (hpaused :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨51⟩) ⟨255⟩ ≠
        ⟨0⟩)
    (hcond :
      evalExpr? auctionConfig { contract := auctionContract, locals := ∅ } (auctionUnpausePostState evm)
        (.binary .or (.binary .eq (.storage (aField "startTime")) (.intLit 0))
          (.storage (aField "settled"))) = .ok (.bool true))
    (hcall : typedCallViaEVM auctionConfig (auctionUnpausePostState evm)
      (EVM.address (AccountAddress.ofNat
        ((UInt256.land
          (Solm.EVM.storageLoad (auctionUnpausePostState evm)
            (auctionUnpausePostState evm).executionEnv.codeOwner ⟨201⟩)
          solcAddrMask).toNat))) "mint" 0 [] (false, evmCall, out) true)
    (hlen : 4 ≤ out.size) (hsel : out.extract 0 4 = errorStringSelector)
    (hlong : 68 ≤ out.size)
    (hsmall : (out.extract 4 out.size).size < (2 : Nat) ^ 255)
    (hoff : ABI.readNat? (out.extract 4 out.size).toList 0 = some off)
    (hoffMax : off ≤ ABI.solcMaxU64) (hoffBound : off + 36 ≤ out.size)
    (hlenWord : ABI.readNat? (out.extract 4 out.size).toList off = some len)
    (hlenMax : len ≤ ABI.solcMaxU64) (hpayloadBound : out.size < off + len + 36) :
    ExecTransitionBody auctionConfig auctionContract evm ∅ unpauseTransition.body .reverted := by
  let evm' := auctionUnpausePostState evm
  refine ExecFuncBody.execBlockRevert ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalExpr_pause_owner_eq_true evm howner)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalExpr_pause_paused_true evm hpaused)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_unpause_false evm) (auctionUnpauseAssign evm)) ?_
  refine ExecBlock.consRevert (ExecStmt.iteTrue (by simpa [evm'] using hcond) ?_)
  exact ExecBlock.consRevert (internalCallFunctionRevert
    (cfg := auctionConfig) (caller := { contract := auctionContract, locals := ∅ })
    (evm := evm') (name := "_createAuction") (args := []) (retVar := "_c")
    (argVals := []) (callee := createAuctionFn) (locals := ∅)
    (by rfl) (by rfl) (by rfl)
    (auctionCreateAuctionBodyReverts_callFailure_errorStringPayloadBounds hcall hlen hsel
      hlong hsmall hoff hoffMax hoffBound hlenWord hlenMax hpayloadBound))

theorem auctionUnpauseBodyReverts_create_callFailure_errorStringAllocU64
    (evm evmCall : EVM.State) {out : ByteArray} {off len : Nat}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (howner :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨151⟩) solcAddrMask =
        auctionSourceWord evm.executionEnv)
    (hpaused :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨51⟩) ⟨255⟩ ≠
        ⟨0⟩)
    (hcond :
      evalExpr? auctionConfig { contract := auctionContract, locals := ∅ } (auctionUnpausePostState evm)
        (.binary .or (.binary .eq (.storage (aField "startTime")) (.intLit 0))
          (.storage (aField "settled"))) = .ok (.bool true))
    (hcall : typedCallViaEVM auctionConfig (auctionUnpausePostState evm)
      (EVM.address (AccountAddress.ofNat
        ((UInt256.land
          (Solm.EVM.storageLoad (auctionUnpausePostState evm)
            (auctionUnpausePostState evm).executionEnv.codeOwner ⟨201⟩)
          solcAddrMask).toNat))) "mint" 0 [] (false, evmCall, out) true)
    (hlen : 4 ≤ out.size) (hsel : out.extract 0 4 = errorStringSelector)
    (hlong : 68 ≤ out.size)
    (hsmall : (out.extract 4 out.size).size < (2 : Nat) ^ 255)
    (hoff : ABI.readNat? (out.extract 4 out.size).toList 0 = some off)
    (hoffMax : off ≤ ABI.solcMaxU64) (hoffBound : off + 36 ≤ out.size)
    (hlenWord : ABI.readNat? (out.extract 4 out.size).toList off = some len)
    (hlenMax : len ≤ ABI.solcMaxU64) (hpayloadBound : off + len + 36 ≤ out.size)
    (halloc : ABI.solcMaxU64 < errorStringNewFreeNat off len) :
    ExecTransitionBody auctionConfig auctionContract evm ∅ unpauseTransition.body .reverted := by
  let evm' := auctionUnpausePostState evm
  refine ExecFuncBody.execBlockRevert ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalExpr_pause_owner_eq_true evm howner)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalExpr_pause_paused_true evm hpaused)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_unpause_false evm) (auctionUnpauseAssign evm)) ?_
  refine ExecBlock.consRevert (ExecStmt.iteTrue (by simpa [evm'] using hcond) ?_)
  exact ExecBlock.consRevert (internalCallFunctionRevert
    (cfg := auctionConfig) (caller := { contract := auctionContract, locals := ∅ })
    (evm := evm') (name := "_createAuction") (args := []) (retVar := "_c")
    (argVals := []) (callee := createAuctionFn) (locals := ∅)
    (by rfl) (by rfl) (by rfl)
    (auctionCreateAuctionBodyReverts_callFailure_errorStringAllocU64 hcall hlen hsel hlong
      hsmall hoff hoffMax hoffBound hlenWord hlenMax hpayloadBound halloc))

theorem auctionUnpauseBodyReverts_create_callFailure_errorStringDecode
    (evm evmCall : EVM.State) {out : ByteArray} {off len : Nat}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (howner :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨151⟩) solcAddrMask =
        auctionSourceWord evm.executionEnv)
    (hpaused :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨51⟩) ⟨255⟩ ≠
        ⟨0⟩)
    (hcond :
      evalExpr? auctionConfig { contract := auctionContract, locals := ∅ } (auctionUnpausePostState evm)
        (.binary .or (.binary .eq (.storage (aField "startTime")) (.intLit 0))
          (.storage (aField "settled"))) = .ok (.bool true))
    (hcall : typedCallViaEVM auctionConfig (auctionUnpausePostState evm)
      (EVM.address (AccountAddress.ofNat
        ((UInt256.land
          (Solm.EVM.storageLoad (auctionUnpausePostState evm)
            (auctionUnpausePostState evm).executionEnv.codeOwner ⟨201⟩)
          solcAddrMask).toNat))) "mint" 0 [] (false, evmCall, out) true)
    (hlen : 4 ≤ out.size) (hsel : out.extract 0 4 = errorStringSelector)
    (hlong : 68 ≤ out.size)
    (hsmall : (out.extract 4 out.size).size < (2 : Nat) ^ 255)
    (hoff : ABI.readNat? (out.extract 4 out.size).toList 0 = some off)
    (hoffMax : off ≤ ABI.solcMaxU64)
    (hoffBound : off + 36 ≤ out.size)
    (hlenWord : ABI.readNat? (out.extract 4 out.size).toList off = some len)
    (hlenMax : len ≤ ABI.solcMaxU64)
    (hpayloadBound : off + len + 36 ≤ out.size)
    (halloc : errorStringNewFreeNat off len ≤ ABI.solcMaxU64)
    (hdec : ABI.decodeReturnValue? .string (out.extract 4 out.size) = none) :
    ExecTransitionBody auctionConfig auctionContract evm ∅ unpauseTransition.body .reverted := by
  let evm' := auctionUnpausePostState evm
  refine ExecFuncBody.execBlockRevert ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalExpr_pause_owner_eq_true evm howner)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalExpr_pause_paused_true evm hpaused)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_unpause_false evm) (auctionUnpauseAssign evm)) ?_
  refine ExecBlock.consRevert (ExecStmt.iteTrue (by simpa [evm'] using hcond) ?_)
  exact ExecBlock.consRevert (internalCallFunctionRevert
    (cfg := auctionConfig) (caller := { contract := auctionContract, locals := ∅ })
    (evm := evm') (name := "_createAuction") (args := []) (retVar := "_c")
    (argVals := []) (callee := createAuctionFn) (locals := ∅)
    (by rfl) (by rfl) (by rfl)
    (auctionCreateAuctionBodyReverts_callFailure_errorStringDecode hcall hlen hsel hlong hsmall
      hoff hoffMax hoffBound hlenWord hlenMax hpayloadBound halloc hdec))

theorem auctionUnpauseBodyReverts_create_callFailure_errorStringPaused
    (evm evmCall : EVM.State) {out : ByteArray} {off len : Nat} {decoded : Value}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (howner :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨151⟩) solcAddrMask =
        auctionSourceWord evm.executionEnv)
    (hpaused :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨51⟩) ⟨255⟩ ≠
        ⟨0⟩)
    (hcond :
      evalExpr? auctionConfig { contract := auctionContract, locals := ∅ } (auctionUnpausePostState evm)
        (.binary .or (.binary .eq (.storage (aField "startTime")) (.intLit 0))
          (.storage (aField "settled"))) = .ok (.bool true))
    (hcall : typedCallViaEVM auctionConfig (auctionUnpausePostState evm)
      (EVM.address (AccountAddress.ofNat
        ((UInt256.land
          (Solm.EVM.storageLoad (auctionUnpausePostState evm)
            (auctionUnpausePostState evm).executionEnv.codeOwner ⟨201⟩)
          solcAddrMask).toNat))) "mint" 0 [] (false, evmCall, out) true)
    (hlen : 4 ≤ out.size) (hsel : out.extract 0 4 = errorStringSelector)
    (hlong : 68 ≤ out.size)
    (hsmall : (out.extract 4 out.size).size < (2 : Nat) ^ 255)
    (hoff : ABI.readNat? (out.extract 4 out.size).toList 0 = some off)
    (hoffMax : off ≤ ABI.solcMaxU64)
    (hoffBound : off + 36 ≤ out.size)
    (hlenWord : ABI.readNat? (out.extract 4 out.size).toList off = some len)
    (hlenMax : len ≤ ABI.solcMaxU64)
    (hpayloadBound : off + len + 36 ≤ out.size)
    (halloc : errorStringNewFreeNat off len ≤ ABI.solcMaxU64)
    (hdec : ABI.decodeReturnValue? .string (out.extract 4 out.size) = some decoded)
    (hpausedCall :
      UInt256.land (Solm.EVM.storageLoad evmCall evmCall.executionEnv.codeOwner ⟨51⟩) ⟨255⟩ ≠
        ⟨0⟩) :
    ExecTransitionBody auctionConfig auctionContract evm ∅ unpauseTransition.body .reverted := by
  let evm' := auctionUnpausePostState evm
  refine ExecFuncBody.execBlockRevert ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalExpr_pause_owner_eq_true evm howner)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalExpr_pause_paused_true evm hpaused)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_unpause_false evm) (auctionUnpauseAssign evm)) ?_
  refine ExecBlock.consRevert (ExecStmt.iteTrue (by simpa [evm'] using hcond) ?_)
  exact ExecBlock.consRevert (internalCallFunctionRevert
    (cfg := auctionConfig) (caller := { contract := auctionContract, locals := ∅ })
    (evm := evm') (name := "_createAuction") (args := []) (retVar := "_c")
    (argVals := []) (callee := createAuctionFn) (locals := ∅)
    (by rfl) (by rfl) (by rfl)
    (auctionCreateAuctionBodyReverts_callFailure_errorStringPaused hcall hlen hsel hlong hsmall
      hoff hoffMax hoffBound hlenWord hlenMax hpayloadBound halloc hdec hpausedCall))

theorem auctionUnpausePostMap_accountMap {cA gh bl σ σ₀ A I} {g : Sat256} :
    accountMapEquiv (auctionUnpausePostMap σ I)
      (auctionUnpausePostState (initState cA gh bl σ σ₀ g A I)).accountMap := by
  apply accountMapEquiv.of_eq
  simp [auctionUnpausePostMap, auctionUnpausePostState, initState,
    storageStore_accountMap, auctionSlotWord, Solm.EVM.storageLoad,
    State.lookupAccount, Account.lookupStorage]

theorem auctionUnpausePostState_equiv {cA gh bl σ_evm σ_solm σ₀ A I} {g : Sat256}
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    EVMStateEquiv (auctionUnpausePostState (initState cA gh bl σ_evm σ₀ g A I))
      (auctionUnpausePostState (initState cA gh bl σ_solm σ₀ g A I)) := by
  have hσ : EVMStateEquiv (initState cA gh bl σ_evm σ₀ g A I)
      (initState cA gh bl σ_solm σ₀ g A I) := by
    exact EVMStateEquiv.initState hAccounts
  exact hσ.storageStore_codeOwner ⟨51⟩ (by
    have hword : auctionSlotWord ⟨51⟩ σ_evm I = auctionSlotWord ⟨51⟩ σ_solm I := by
      simpa [auctionSlotWord] using
        accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨51⟩ (default : UInt256)
    simpa [initState, auctionSlotWord, Solm.EVM.storageLoad, State.lookupAccount] using
      congrArg auctionPausedSetFalseWord hword)

theorem auctionUnpausePost_mintTarget_eq {cA gh bl σ_evm σ_solm σ₀ A I} {g : Sat256}
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    EVM.address (AccountAddress.ofNat
        ((UInt256.land (auctionSlotWord ⟨201⟩ (auctionUnpausePostMap σ_evm I) I)
          solcAddrMask).toNat)) =
      EVM.address (AccountAddress.ofNat
        ((UInt256.land
          (Solm.EVM.storageLoad
            (auctionUnpausePostState (initState cA gh bl σ_solm σ₀ g A I))
            (auctionUnpausePostState
              (initState cA gh bl σ_solm σ₀ g A I)).executionEnv.codeOwner
            ⟨201⟩) solcAddrMask).toNat)) := by
  have hslot : auctionSlotWord ⟨201⟩ (auctionUnpausePostMap σ_evm I) I =
      auctionSlotWord ⟨201⟩ σ_evm I := by
    simpa [auctionUnpausePostMap, auctionSlotWord] using
      sstoreAccountMap_storage_findD_ne σ_evm I.codeOwner ⟨201⟩ ⟨51⟩
        (auctionPausedSetFalseWord (auctionSlotWord ⟨51⟩ σ_evm I)) (by decide)
  have hload :
      Solm.EVM.storageLoad
          (auctionUnpausePostState (initState cA gh bl σ_solm σ₀ g A I))
          (auctionUnpausePostState
            (initState cA gh bl σ_solm σ₀ g A I)).executionEnv.codeOwner
          ⟨201⟩ =
        auctionSlotWord ⟨201⟩ σ_solm I := by
    let evm := initState cA gh bl σ_solm σ₀ g A I
    have henv : (auctionUnpausePostState evm).executionEnv = evm.executionEnv := by
      simp [auctionUnpausePostState, storageStore_executionEnv]
    have hload0 : Solm.EVM.storageLoad (auctionUnpausePostState evm)
          evm.executionEnv.codeOwner ⟨201⟩ =
        Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨201⟩ := by
      simpa [auctionUnpausePostState] using
        (storageLoad_storageStore_ne evm evm.executionEnv.codeOwner
        (readSlot := ⟨201⟩) (writeSlot := ⟨51⟩)
        (val := auctionPausedSetFalseWord
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨51⟩))
          (by decide))
    have hload1 : Solm.EVM.storageLoad (auctionUnpausePostState evm)
          (auctionUnpausePostState evm).executionEnv.codeOwner ⟨201⟩ =
        Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨201⟩ := by
      simpa [henv] using hload0
    simpa [evm, initState, auctionSlotWord, Solm.EVM.storageLoad, State.lookupAccount]
      using hload1
  have hbase : auctionSlotWord ⟨201⟩ σ_evm I = auctionSlotWord ⟨201⟩ σ_solm I := by
    simpa [auctionSlotWord] using
      accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨201⟩ (default : UInt256)
  rw [hslot, hload, hbase]

theorem auctionUnpauseMintCall_transport {cA gh bl σ_evm σ_solm σ₀ A I} {g : Sat256}
    {cA' : Batteries.RBSet AccountAddress compare} {σ' : AccountMap} {z : Bool}
    {o : ByteArray} {A' : Substate}
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hcall : typedCallViaEVM auctionConfig
      { initState cA gh bl σ_evm σ₀ g A I with accountMap := auctionUnpausePostMap σ_evm I }
      (EVM.address (AccountAddress.ofNat
        ((UInt256.land (auctionSlotWord ⟨201⟩ (auctionUnpausePostMap σ_evm I) I)
          solcAddrMask).toNat))) "mint" 0 []
      (z,
        { initState cA gh bl σ_evm σ₀ g A I with
          accountMap := σ', substate := A', createdAccounts := cA' }, o) true) :
    ∃ (σ'_solm : AccountMap) (A'_solm : Substate),
      typedCallViaEVM auctionConfig
        (auctionUnpausePostState (initState cA gh bl σ_solm σ₀ g A I))
        (EVM.address (AccountAddress.ofNat
          ((UInt256.land
            (Solm.EVM.storageLoad
              (auctionUnpausePostState (initState cA gh bl σ_solm σ₀ g A I))
              (auctionUnpausePostState
                (initState cA gh bl σ_solm σ₀ g A I)).executionEnv.codeOwner
              ⟨201⟩) solcAddrMask).toNat))) "mint" 0 []
        (z,
          { auctionUnpausePostState (initState cA gh bl σ_solm σ₀ g A I) with
            accountMap := σ'_solm, substate := A'_solm, createdAccounts := cA' }, o) true ∧
      EVMStateEquiv
        { initState cA gh bl σ_evm σ₀ g A I with
          accountMap := σ', substate := A', createdAccounts := cA' }
        { auctionUnpausePostState (initState cA gh bl σ_solm σ₀ g A I) with
          accountMap := σ'_solm, substate := A'_solm, createdAccounts := cA' } := by
  let evmE0 := { initState cA gh bl σ_evm σ₀ g A I with
    accountMap := auctionUnpausePostMap σ_evm I }
  let evmS0 := auctionUnpausePostState (initState cA gh bl σ_solm σ₀ g A I)
  have htarget := auctionUnpausePost_mintTarget_eq (cA := cA) (gh := gh) (bl := bl)
    (σ_evm := σ_evm) (σ_solm := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hAccounts
  have hcallTarget : typedCallViaEVM auctionConfig evmE0
      (EVM.address (AccountAddress.ofNat
        ((UInt256.land
          (Solm.EVM.storageLoad evmS0 evmS0.executionEnv.codeOwner ⟨201⟩)
          solcAddrMask).toNat))) "mint" 0 []
      (z,
        { initState cA gh bl σ_evm σ₀ g A I with
          accountMap := σ', substate := A', createdAccounts := cA' }, o) true := by
    simpa [evmE0, evmS0] using htarget ▸ hcall
  have hpostE : accountMapEquiv (auctionUnpausePostMap σ_evm I)
      (auctionUnpausePostState (initState cA gh bl σ_evm σ₀ g A I)).accountMap := by
    exact auctionUnpausePostMap_accountMap
  have hpostState : EVMStateEquiv
      (auctionUnpausePostState (initState cA gh bl σ_evm σ₀ g A I)) evmS0 := by
    simpa [evmS0] using auctionUnpausePostState_equiv
      (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
      (σ₀ := σ₀) (A := A) (I := I) (g := g) hAccounts
  have hAccountsStart : accountMapEquiv evmE0.accountMap evmS0.accountMap := by
    simpa [evmE0] using accountMapEquiv.trans hpostE hpostState.accountMap
  obtain ⟨σ'_solm, A'_solm, hcallS, hσ'⟩ :=
    typedCallViaEVM_accountMapEquiv hcallTarget hAccountsStart
      (by
        simp [evmE0, evmS0, auctionUnpausePostState, initState, Solm.EVM.storageStore,
          State.lookupAccount]
        cases σ_solm.find? I.codeOwner <;> rfl)
      (by simp [evmE0, evmS0, auctionUnpausePostState, initState, storageStore_createdAccounts])
      (by
        simp [evmE0, evmS0, auctionUnpausePostState, initState, Solm.EVM.storageStore,
          State.lookupAccount]
        cases σ_solm.find? I.codeOwner <;> rfl)
      (by
        simp [evmE0, evmS0, auctionUnpausePostState, initState, Solm.EVM.storageStore,
          State.lookupAccount]
        cases σ_solm.find? I.codeOwner <;> rfl)
      (by
        simp [evmE0, evmS0, auctionUnpausePostState, initState, Solm.EVM.storageStore,
          State.lookupAccount]
        cases σ_solm.find? I.codeOwner <;> rfl)
      (by
        simp [evmE0, evmS0, auctionUnpausePostState, initState, storageStore_executionEnv])
  refine ⟨σ'_solm, A'_solm, ?_, ?_⟩
  · simpa [evmS0] using hcallS
  · refine ⟨?_, ?_, ?_⟩
    · simp [evmS0, auctionUnpausePostState, initState, storageStore_executionEnv]
    · rfl
    · exact hσ'

end Auction
