import Examples.BytesStore.FullSetChunk
import Examples.BytesStore.FullSetPacketByte

/-!
# BytesStore — `setChunkByte(uint256,uint256,uint8)` runtime slice

This split module starts the nested dynamic-array byte setter proof.  It reuses the existing
`setPacketByte` byte-update machinery shape, but the calldata words and storage header slot differ:
the bytes header is `chunksDataBase + chunkIndex`, and the byte index/value are the second and
third ABI words.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000
set_option maxHeartbeats 4000000

namespace BytesStore

def bytesStoreSetChunkByteChunkIndexWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 4

def bytesStoreSetChunkByteIndexWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 36

def bytesStoreSetChunkByteValueWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 68

def bytesStoreSetChunkByteLocals (I : ExecutionEnv) : Store :=
  (((∅ : Store).insert "chunkIndex"
    (.int (Int.ofNat (bytesStoreSetChunkByteChunkIndexWord I).toNat))).insert "byteIndex"
    (.int (Int.ofNat (bytesStoreSetChunkByteIndexWord I).toNat))).insert "value"
    (.int (Int.ofNat (bytesStoreSetChunkByteValueWord I).toNat))

theorem bytesStoreSetChunkByteLocals_get_chunkIndex (I : ExecutionEnv) :
    (bytesStoreSetChunkByteLocals I).get? "chunkIndex" =
      some (.int (Int.ofNat (bytesStoreSetChunkByteChunkIndexWord I).toNat)) := by
  rw [bytesStoreSetChunkByteLocals]
  rw [store_get_ne (h := by decide)]
  rw [store_get_ne (h := by decide)]
  exact store_get_self (∅ : Store) "chunkIndex"
    (.int (Int.ofNat (bytesStoreSetChunkByteChunkIndexWord I).toNat))

theorem bytesStoreSetChunkByteLocals_getElem_chunkIndex (I : ExecutionEnv) :
    (bytesStoreSetChunkByteLocals I)["chunkIndex"]? =
      some (.int (Int.ofNat (bytesStoreSetChunkByteChunkIndexWord I).toNat)) := by
  simpa [Std.HashMap.get?_eq_getElem?] using
    bytesStoreSetChunkByteLocals_get_chunkIndex I

theorem bytesStoreSetChunkByteLocals_get_byteIndex (I : ExecutionEnv) :
    (bytesStoreSetChunkByteLocals I).get? "byteIndex" =
      some (.int (Int.ofNat (bytesStoreSetChunkByteIndexWord I).toNat)) := by
  rw [bytesStoreSetChunkByteLocals]
  rw [store_get_ne (h := by decide)]
  exact store_get_self ((∅ : Store).insert "chunkIndex"
    (.int (Int.ofNat (bytesStoreSetChunkByteChunkIndexWord I).toNat))) "byteIndex"
    (.int (Int.ofNat (bytesStoreSetChunkByteIndexWord I).toNat))

theorem bytesStoreSetChunkByteLocals_getElem_byteIndex (I : ExecutionEnv) :
    (bytesStoreSetChunkByteLocals I)["byteIndex"]? =
      some (.int (Int.ofNat (bytesStoreSetChunkByteIndexWord I).toNat)) := by
  simpa [Std.HashMap.get?_eq_getElem?] using
    bytesStoreSetChunkByteLocals_get_byteIndex I

theorem bytesStoreSetChunkByteLocals_get_chunks_none (I : ExecutionEnv) :
    (bytesStoreSetChunkByteLocals I).get? "chunks" = none := by
  rw [bytesStoreSetChunkByteLocals]
  rw [store_get_ne (h := by decide)]
  rw [store_get_ne (h := by decide)]
  rw [store_get_ne (h := by decide)]
  simp

theorem bytesStoreSetChunkByteLocals_getElem_chunks_none (I : ExecutionEnv) :
    (bytesStoreSetChunkByteLocals I)["chunks"]? = none := by
  simpa [Std.HashMap.get?_eq_getElem?] using
    bytesStoreSetChunkByteLocals_get_chunks_none I

def bytesStoreSetChunkByteRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "chunks"
    steps := [
      .aindex (.int (Int.ofNat (bytesStoreSetChunkByteChunkIndexWord I).toNat)),
      .aindex (.int (Int.ofNat (bytesStoreSetChunkByteIndexWord I).toNat))] }

def bytesStoreSetChunkByteHeaderRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "chunks"
    steps := [.aindex (.int (Int.ofNat (bytesStoreSetChunkByteChunkIndexWord I).toNat))] }

def bytesStoreSetChunkByteValue (I : ExecutionEnv) : Value :=
  .int (Int.ofNat (bytesStoreSetChunkByteValueWord I).toNat)

def bytesStoreSetChunkByteFrame (I : ExecutionEnv) : Frame :=
  { contract := bytesStoreContract, locals := bytesStoreSetChunkByteLocals I }

def bytesStoreSetChunkByteSlot (I : ExecutionEnv) : UInt256 :=
  chunksDataBase + bytesStoreSetChunkByteChunkIndexWord I

theorem bytesStoreSetChunkByteHeaderRef_length_slot (evm : EVM.State) (I : ExecutionEnv) :
    ∃ loc, bytesStoreLayout
        { bytesStoreSetChunkByteHeaderRef I with
          steps := (bytesStoreSetChunkByteHeaderRef I).steps ++ [.length] } evm =
          some loc ∧
        loc.slot = bytesStoreSetChunkByteSlot I := by
  refine ⟨bytesLikeLengthLoc (bytesStoreSetChunkByteSlot I) evm, ?_, ?_⟩
  · have hnonneg : ¬ ((bytesStoreSetChunkByteChunkIndexWord I).toNat : Int) < 0 := by
      omega
    simp [bytesStoreLayout, bytesStoreSetChunkByteHeaderRef, chunksElemSlot?,
      nonnegativeIndexSlot?, bytesStoreSetChunkByteSlot, u256_ofNat_toNat]
    simp [hnonneg]
  · simp [bytesLikeLengthLoc]

def bytesStoreSetChunkByteHeaderWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  (σ.find? I.codeOwner |>.option ⟨0⟩
    (fun acc => acc.storage.findD (bytesStoreSetChunkByteSlot I) ⟨0⟩))

theorem bytesStoreSetChunkByteHeaderWord_eq_of_accountMapEquiv
    {σ_evm σ_solm : AccountMap} {I : ExecutionEnv}
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    bytesStoreSetChunkByteHeaderWord σ_evm I =
      bytesStoreSetChunkByteHeaderWord σ_solm I :=
  accountMapEquiv_storage_findD hAccounts I.codeOwner
    (bytesStoreSetChunkByteSlot I) ⟨0⟩

theorem bytesStoreStorageLoadSetChunkByteHeader_initState_of_accountMapEquiv
    {cA : Batteries.RBSet AccountAddress compare} {gh : BlockHeader} {bl : ProcessedBlocks}
    {σ_evm σ_solm σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : Sat256}
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    Solm.EVM.storageLoad (initState cA gh bl σ_solm σ₀ g A I)
        (initState cA gh bl σ_solm σ₀ g A I).executionEnv.codeOwner
        (bytesStoreSetChunkByteSlot I) =
      bytesStoreSetChunkByteHeaderWord σ_evm I := by
  simpa [bytesStoreSetChunkByteHeaderWord] using
    bytesStoreStorageLoad_initState_of_accountMapEquiv
      (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
      (I := I) (g := g) (bytesStoreSetChunkByteSlot I) hAccounts

theorem bytesStoreStorageLoadSetChunkByteHeader_of_accountMapEquiv
    {evm : EVM.State} {σ : AccountMap} {I : ExecutionEnv}
    (howner : evm.executionEnv.codeOwner = I.codeOwner)
    (hAccounts : accountMapEquiv σ evm.accountMap) :
    Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (bytesStoreSetChunkByteSlot I) =
      bytesStoreSetChunkByteHeaderWord σ I := by
  exact (accountStorageWord_eq_storageLoad_of_accountMapEquiv
    (owner := I.codeOwner) (slot := bytesStoreSetChunkByteSlot I)
    howner hAccounts).symm

def bytesStoreSetChunkByteShortScale (I : ExecutionEnv) : UInt256 :=
  UInt256.exp ⟨256⟩ (UInt256.sub ⟨31⟩ (bytesStoreSetChunkByteIndexWord I))

def bytesStoreSetChunkByteShortStoredWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.lor
    (UInt256.mul
      (UInt256.div (UInt256.shiftLeft (bytesStoreSetChunkByteValueWord I) ⟨248⟩)
        (UInt256.shiftLeft ⟨1⟩ ⟨248⟩))
      (bytesStoreSetChunkByteShortScale I))
    (UInt256.land
      (UInt256.lnot (UInt256.mul ⟨255⟩ (bytesStoreSetChunkByteShortScale I)))
      (bytesStoreSetChunkByteHeaderWord σ I))

def bytesStoreSetChunkByteLongWordIndex (I : ExecutionEnv) : UInt256 :=
  UInt256.mod (bytesStoreSetChunkByteIndexWord I) ⟨32⟩

def bytesStoreSetChunkByteLongDataSlot (I : ExecutionEnv) : UInt256 :=
  bytesLikeDataBase (bytesStoreSetChunkByteSlot I) +
    UInt256.div (bytesStoreSetChunkByteIndexWord I) ⟨32⟩

def bytesStoreSetChunkByteLongScale (I : ExecutionEnv) : UInt256 :=
  UInt256.exp ⟨256⟩ (UInt256.sub ⟨31⟩ (bytesStoreSetChunkByteLongWordIndex I))

def bytesStoreSetChunkByteLongOldWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  (σ.find? I.codeOwner |>.option ⟨0⟩
    (fun acc => acc.storage.findD (bytesStoreSetChunkByteLongDataSlot I) ⟨0⟩))

theorem bytesStoreSetChunkByteLongOldWord_eq_of_accountMapEquiv
    {σ_evm σ_solm : AccountMap} {I : ExecutionEnv}
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    bytesStoreSetChunkByteLongOldWord σ_evm I =
      bytesStoreSetChunkByteLongOldWord σ_solm I :=
  accountMapEquiv_storage_findD hAccounts I.codeOwner
    (bytesStoreSetChunkByteLongDataSlot I) ⟨0⟩

theorem bytesStoreStorageLoadSetChunkByteLongData_initState_of_accountMapEquiv
    {cA : Batteries.RBSet AccountAddress compare} {gh : BlockHeader} {bl : ProcessedBlocks}
    {σ_evm σ_solm σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : Sat256}
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    Solm.EVM.storageLoad (initState cA gh bl σ_solm σ₀ g A I)
        (initState cA gh bl σ_solm σ₀ g A I).executionEnv.codeOwner
        (bytesStoreSetChunkByteLongDataSlot I) =
      bytesStoreSetChunkByteLongOldWord σ_evm I := by
  simpa [bytesStoreSetChunkByteLongOldWord] using
    bytesStoreStorageLoad_initState_of_accountMapEquiv
      (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
      (I := I) (g := g) (bytesStoreSetChunkByteLongDataSlot I) hAccounts

def bytesStoreSetChunkByteLongStoredWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.lor
    (UInt256.mul
      (UInt256.div (UInt256.shiftLeft (bytesStoreSetChunkByteValueWord I) ⟨248⟩)
        (UInt256.shiftLeft ⟨1⟩ ⟨248⟩))
      (bytesStoreSetChunkByteLongScale I))
    (UInt256.land
      (UInt256.lnot (UInt256.mul ⟨255⟩ (bytesStoreSetChunkByteLongScale I)))
      (bytesStoreSetChunkByteLongOldWord σ I))

theorem bytesStoreSetChunkByteChunkIndexWord_eq_setChunkIndexWord (I : ExecutionEnv) :
    bytesStoreSetChunkByteChunkIndexWord I = bytesStoreSetChunkIndexWord I := by
  rfl

theorem bytesStoreSetChunkByteLongWordIndex_toNat (I : ExecutionEnv) :
    (bytesStoreSetChunkByteLongWordIndex I).toNat =
      (bytesStoreSetChunkByteIndexWord I).toNat % 32 := by
  rw [bytesStoreSetChunkByteLongWordIndex]
  unfold UInt256.mod
  rw [if_neg (by native_decide)]
  rfl

theorem bytesStoreSetChunkByteLongWordIndex_lt32 (I : ExecutionEnv) :
    (bytesStoreSetChunkByteLongWordIndex I).toNat < 32 := by
  rw [bytesStoreSetChunkByteLongWordIndex_toNat]
  exact Nat.mod_lt _ (by decide : 0 < 32)

theorem bytesStoreSetChunkByteLongWordIndex_eq_index_of_lt32
    {I : ExecutionEnv}
    (hidx : (bytesStoreSetChunkByteIndexWord I).toNat < 32) :
    bytesStoreSetChunkByteLongWordIndex I =
      bytesStoreSetChunkByteIndexWord I := by
  apply u256_inj
  rw [bytesStoreSetChunkByteLongWordIndex_toNat]
  exact Nat.mod_eq_of_lt hidx

theorem bytesStoreSetChunkByte_storageTypeAt {I : ExecutionEnv} :
    storageTypeAt? bytesStoreContract.storage (bytesStoreSetChunkByteRef I) =
      some uint8St := by
  simp [bytesStoreSetChunkByteRef, storageTypeAt?, bytesStoreContract, storageDecls,
    storageTypeStep?, bytesSt, uint8St, uint8Int]

theorem bytesStoreSetChunkByteLayoutShort {evm : EVM.State} {I : ExecutionEnv}
    (hpacked : checkBytesPacked (bytesStoreSetChunkByteSlot I) evm = true)
    (hidx : (bytesStoreSetChunkByteIndexWord I).toNat < 31) :
    bytesStoreConfig.storage.layout (bytesStoreSetChunkByteRef I) evm =
      some (uint8Loc (bytesStoreSetChunkByteSlot I)
        ⟨31 - (bytesStoreSetChunkByteIndexWord I).toNat, by omega⟩) := by
  have hchunkNN :
      ¬ (((bytesStoreSetChunkByteChunkIndexWord I).toNat : Int) < 0) := by omega
  have hbyteNN :
      ¬ (((bytesStoreSetChunkByteIndexWord I).toNat : Int) < 0) := by omega
  have hpackedSlot :
      checkBytesPacked (chunksDataBase + bytesStoreSetChunkByteChunkIndexWord I) evm = true := by
    simpa [bytesStoreSetChunkByteSlot] using hpacked
  simp [bytesStoreConfig, bytesStoreStorageLayout, solidityStorageLayout,
    bytesStoreLayout, bytesStoreSetChunkByteRef, bytesStoreSetChunkByteSlot,
    chunksElemSlot?, nonnegativeIndexSlot?, bytesLikeByteLoc?, uint8Loc, uint8Int, hpackedSlot,
    hidx, hchunkNN, hbyteNN, u256_ofNat_toNat]

theorem bytesStoreSetChunkByteLayoutLong {evm : EVM.State} {I : ExecutionEnv}
    (hpacked : checkBytesPacked (bytesStoreSetChunkByteSlot I) evm = false) :
    bytesStoreConfig.storage.layout (bytesStoreSetChunkByteRef I) evm =
      some (uint8Loc (bytesStoreSetChunkByteLongDataSlot I)
        ⟨31 - (bytesStoreSetChunkByteLongWordIndex I).toNat, by
          have hidx := bytesStoreSetChunkByteLongWordIndex_lt32 I
          omega⟩) := by
  have hchunkNN :
      ¬ (((bytesStoreSetChunkByteChunkIndexWord I).toNat : Int) < 0) := by omega
  have hbyteNN :
      ¬ (((bytesStoreSetChunkByteIndexWord I).toNat : Int) < 0) := by omega
  have hpackedSlot :
      checkBytesPacked (chunksDataBase + bytesStoreSetChunkByteChunkIndexWord I) evm = false := by
    simpa [bytesStoreSetChunkByteSlot] using hpacked
  rw [bytesStoreSetChunkByteLongDataSlot, u256_div32_eq_ofNat_toNat_div]
  simp [bytesStoreConfig, bytesStoreStorageLayout, solidityStorageLayout,
    bytesStoreLayout, bytesStoreSetChunkByteRef, bytesStoreSetChunkByteSlot,
    chunksElemSlot?, nonnegativeIndexSlot?, bytesLikeByteLoc?, uint8Loc, uint8Int, hpackedSlot,
    hchunkNN, hbyteNN, bytesStoreSetChunkByteLongWordIndex_toNat, u256_ofNat_toNat]

theorem bytesStoreSetChunkByteIndex_lt31_of_short_bound {I : ExecutionEnv} {len : UInt256}
    (hshort : len.toNat < 32)
    (hbound : (bytesStoreSetChunkByteIndexWord I).toNat < len.toNat) :
    (bytesStoreSetChunkByteIndexWord I).toNat < 31 := by
  omega

theorem bytesStoreSetChunkByteValueHighShiftDiv
    {I : ExecutionEnv}
    (hcanon : (bytesStoreSetChunkByteValueWord I).toNat < EVM.twoPow 8) :
    UInt256.div (UInt256.shiftLeft (bytesStoreSetChunkByteValueWord I) ⟨248⟩)
        (UInt256.shiftLeft ⟨1⟩ ⟨248⟩) =
      bytesStoreSetChunkByteValueWord I := by
  apply u256_inj
  rw [udiv_toNat, bytesStoreShiftLeftOne248_toNat]
  unfold UInt256.shiftLeft
  rw [if_neg (by decide : ¬ ((⟨248⟩ : UInt256).val ≥ 256))]
  change ((((bytesStoreSetChunkByteValueWord I).val <<< (⟨248⟩ : UInt256).val) :
      Fin UInt256.size).val) / 2 ^ 248 = (bytesStoreSetChunkByteValueWord I).toNat
  rw [Fin.shiftLeft_val, Nat.shiftLeft_eq]
  change (bytesStoreSetChunkByteValueWord I).toNat * 2 ^ 248 % UInt256.size / 2 ^ 248 =
    (bytesStoreSetChunkByteValueWord I).toNat
  rw [Nat.mod_eq_of_lt]
  · rw [Nat.mul_comm]
    rw [Nat.mul_div_right _ (by positivity : 0 < 2 ^ 248)]
  · rw [show UInt256.size = 2 ^ 256 from rfl]
    calc (bytesStoreSetChunkByteValueWord I).toNat * 2 ^ 248 < 256 * 2 ^ 248 :=
        Nat.mul_lt_mul_of_pos_right hcanon (by positivity)
      _ = 2 ^ 256 := by
        rw [show (256 : Nat) = 2 ^ 8 by norm_num]
        rw [← pow_add]
        norm_num

theorem bytesStoreSetChunkByteShortScale_toNat {I : ExecutionEnv} {len : UInt256}
    (hshort : len.toNat < 32)
    (hbound : (bytesStoreSetChunkByteIndexWord I).toNat < len.toNat) :
    (bytesStoreSetChunkByteShortScale I).toNat =
      2 ^ ((31 - (bytesStoreSetChunkByteIndexWord I).toNat) * 8) := by
  have hidx : (bytesStoreSetChunkByteIndexWord I).toNat < 31 :=
    bytesStoreSetChunkByteIndex_lt31_of_short_bound hshort hbound
  interval_cases hnat : (bytesStoreSetChunkByteIndexWord I).toNat
  all_goals
    have hword : bytesStoreSetChunkByteIndexWord I =
        UInt256.ofNat (bytesStoreSetChunkByteIndexWord I).toNat := by
      exact (u256_ofNat_toNat (bytesStoreSetChunkByteIndexWord I)).symm
    rw [bytesStoreSetChunkByteShortScale, hword, hnat]
    native_decide

theorem bytesStoreSetChunkByteShortMaskWord_toNat {I : ExecutionEnv} {len : UInt256}
    (hshort : len.toNat < 32)
    (hbound : (bytesStoreSetChunkByteIndexWord I).toNat < len.toNat) :
    (UInt256.mul ⟨255⟩ (bytesStoreSetChunkByteShortScale I)).toNat =
      255 * 2 ^ ((31 - (bytesStoreSetChunkByteIndexWord I).toNat) * 8) := by
  rw [u256_mul_toNat, bytesStoreSetChunkByteShortScale_toNat (I := I) (len := len)
    hshort hbound]
  rw [show (⟨255⟩ : UInt256).toNat = 255 by decide]
  rw [Nat.mod_eq_of_lt]
  have hk : ((31 - (bytesStoreSetChunkByteIndexWord I).toNat) * 8) + 8 ≤ 256 := by
    have hidx : (bytesStoreSetChunkByteIndexWord I).toNat < 31 :=
      bytesStoreSetChunkByteIndex_lt31_of_short_bound (I := I) (len := len) hshort hbound
    omega
  calc 255 * 2 ^ ((31 - (bytesStoreSetChunkByteIndexWord I).toNat) * 8) <
      256 * 2 ^ ((31 - (bytesStoreSetChunkByteIndexWord I).toNat) * 8) := by
        exact Nat.mul_lt_mul_of_pos_right (by norm_num : 255 < 256) (by positivity)
    _ ≤ UInt256.size := by
      rw [show UInt256.size = 2 ^ 256 from rfl]
      rw [show 256 = 2 ^ 8 by norm_num, ← Nat.pow_add]
      exact Nat.pow_le_pow_right (by norm_num) (by omega)

theorem bytesStoreSetChunkByteShortClearMask_toNat {I : ExecutionEnv} {len : UInt256}
    (hshort : len.toNat < 32)
    (hbound : (bytesStoreSetChunkByteIndexWord I).toNat < len.toNat) :
    (UInt256.lnot (UInt256.mul ⟨255⟩ (bytesStoreSetChunkByteShortScale I))).toNat =
      2 ^ 256 - 1 - 255 * 2 ^ ((31 - (bytesStoreSetChunkByteIndexWord I).toNat) * 8) := by
  rw [u256_lnot_toNat, bytesStoreSetChunkByteShortMaskWord_toNat (I := I) (len := len)
    hshort hbound]
  rfl

theorem bytesStoreSetChunkByteLongScale_toNat {I : ExecutionEnv} :
    (bytesStoreSetChunkByteLongScale I).toNat =
      2 ^ ((31 - (bytesStoreSetChunkByteLongWordIndex I).toNat) * 8) := by
  have hidx : (bytesStoreSetChunkByteLongWordIndex I).toNat < 32 :=
    bytesStoreSetChunkByteLongWordIndex_lt32 I
  interval_cases hnat : (bytesStoreSetChunkByteLongWordIndex I).toNat
  all_goals
    have hword : bytesStoreSetChunkByteLongWordIndex I =
        UInt256.ofNat (bytesStoreSetChunkByteLongWordIndex I).toNat := by
      exact (u256_ofNat_toNat (bytesStoreSetChunkByteLongWordIndex I)).symm
    rw [bytesStoreSetChunkByteLongScale, hword, hnat]
    native_decide

theorem bytesStoreSetChunkByteLongMaskWord_toNat {I : ExecutionEnv} :
    (UInt256.mul ⟨255⟩ (bytesStoreSetChunkByteLongScale I)).toNat =
      255 * 2 ^ ((31 - (bytesStoreSetChunkByteLongWordIndex I).toNat) * 8) := by
  rw [u256_mul_toNat, bytesStoreSetChunkByteLongScale_toNat (I := I)]
  rw [show (⟨255⟩ : UInt256).toNat = 255 by decide]
  rw [Nat.mod_eq_of_lt]
  have hk : ((31 - (bytesStoreSetChunkByteLongWordIndex I).toNat) * 8) + 8 ≤ 256 := by
    have hidx : (bytesStoreSetChunkByteLongWordIndex I).toNat < 32 :=
      bytesStoreSetChunkByteLongWordIndex_lt32 I
    omega
  calc 255 * 2 ^ ((31 - (bytesStoreSetChunkByteLongWordIndex I).toNat) * 8) <
      256 * 2 ^ ((31 - (bytesStoreSetChunkByteLongWordIndex I).toNat) * 8) := by
        exact Nat.mul_lt_mul_of_pos_right (by norm_num : 255 < 256) (by positivity)
    _ = 2 ^ (((31 - (bytesStoreSetChunkByteLongWordIndex I).toNat) * 8) + 8) := by
        rw [show 256 = 2 ^ 8 by norm_num, ← Nat.pow_add]
        ring
    _ ≤ 2 ^ 256 := Nat.pow_le_pow_right (by norm_num) hk
    _ = UInt256.size := rfl

theorem bytesStoreSetChunkByteLongClearMask_toNat {I : ExecutionEnv} :
    (UInt256.lnot (UInt256.mul ⟨255⟩ (bytesStoreSetChunkByteLongScale I))).toNat =
      (2 : Nat) ^ 256 - 1 -
        255 * 2 ^ ((31 - (bytesStoreSetChunkByteLongWordIndex I).toNat) * 8) := by
  rw [u256_lnot_toNat, bytesStoreSetChunkByteLongMaskWord_toNat (I := I)]
  rfl

theorem bytesStoreSetChunkByteShortStoredWord_byteAt
    {σ : AccountMap} {I : ExecutionEnv} {len : UInt256}
    (hcanon : (bytesStoreSetChunkByteValueWord I).toNat < EVM.twoPow 8)
    (hshort : len.toNat < 32)
    (hbound : (bytesStoreSetChunkByteIndexWord I).toNat < len.toNat) :
    UInt256.byteAt (bytesStoreSetChunkByteIndexWord I)
      (bytesStoreSetChunkByteShortStoredWord σ I) =
        bytesStoreSetChunkByteValueWord I := by
  apply u256_inj
  have hi31 : (bytesStoreSetChunkByteIndexWord I).toNat ≤ 31 := by
    have hlt := bytesStoreSetChunkByteIndex_lt31_of_short_bound (I := I) (len := len)
      hshort hbound
    omega
  rw [byteAt_toNat_of_le31 hi31]
  rw [bytesStoreSetChunkByteShortStoredWord,
    bytesStoreSetChunkByteValueHighShiftDiv hcanon]
  rw [u256_lor_toNat, u256_mul_toNat, u256_land_toNat]
  rw [bytesStoreSetChunkByteShortScale_toNat (I := I) (len := len) hshort hbound]
  rw [bytesStoreSetChunkByteShortClearMask_toNat (I := I) (len := len) hshort hbound]
  have hv : (bytesStoreSetChunkByteValueWord I).toNat < 256 := by
    simpa [EVM.twoPow] using hcanon
  have hk : ((31 - (bytesStoreSetChunkByteIndexWord I).toNat) * 8) + 8 ≤ 256 := by
    have hidx : (bytesStoreSetChunkByteIndexWord I).toNat < 31 :=
      bytesStoreSetChunkByteIndex_lt31_of_short_bound (I := I) (len := len) hshort hbound
    omega
  have hleftLt : (bytesStoreSetChunkByteValueWord I).toNat *
      2 ^ ((31 - (bytesStoreSetChunkByteIndexWord I).toNat) * 8) < UInt256.size := by
    rw [show UInt256.size = 2 ^ 256 from rfl]
    calc (bytesStoreSetChunkByteValueWord I).toNat *
            2 ^ ((31 - (bytesStoreSetChunkByteIndexWord I).toNat) * 8) <
          256 * 2 ^ ((31 - (bytesStoreSetChunkByteIndexWord I).toNat) * 8) :=
            Nat.mul_lt_mul_of_pos_right hv (by positivity)
        _ ≤ 2 ^ 256 := by
          rw [show 256 = 2 ^ 8 by norm_num, ← Nat.pow_add]
          exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hrightLt : (((2 : Nat) ^ 256 - 1 -
        255 * 2 ^ ((31 - (bytesStoreSetChunkByteIndexWord I).toNat) * 8)) &&&
        (bytesStoreSetChunkByteHeaderWord σ I).toNat) < UInt256.size := by
    exact lt_of_le_of_lt Nat.and_le_right (bytesStoreSetChunkByteHeaderWord σ I).val.isLt
  rw [Nat.mod_eq_of_lt hleftLt]
  change ((bytesStoreSetChunkByteValueWord I).toNat *
          2 ^ ((31 - (bytesStoreSetChunkByteIndexWord I).toNat) * 8)).lor
        ((((2 : Nat) ^ 256 - 1 -
          255 * 2 ^ ((31 - (bytesStoreSetChunkByteIndexWord I).toNat) * 8)) &&&
          (bytesStoreSetChunkByteHeaderWord σ I).toNat) % UInt256.size) %
        UInt256.size /
      2 ^ ((31 - (bytesStoreSetChunkByteIndexWord I).toNat) * 8) % 256 =
    (bytesStoreSetChunkByteValueWord I).toNat
  rw [Nat.mod_eq_of_lt hrightLt]
  have hlorLt :
      ((bytesStoreSetChunkByteValueWord I).toNat *
            2 ^ ((31 - (bytesStoreSetChunkByteIndexWord I).toNat) * 8)).lor
          (((2 : Nat) ^ 256 - 1 -
              255 * 2 ^ ((31 - (bytesStoreSetChunkByteIndexWord I).toNat) * 8)) &&&
            (bytesStoreSetChunkByteHeaderWord σ I).toNat) < UInt256.size := by
    change ((bytesStoreSetChunkByteValueWord I).toNat *
          2 ^ ((31 - (bytesStoreSetChunkByteIndexWord I).toNat) * 8)) |||
        (((2 : Nat) ^ 256 - 1 -
            255 * 2 ^ ((31 - (bytesStoreSetChunkByteIndexWord I).toNat) * 8)) &&&
          (bytesStoreSetChunkByteHeaderWord σ I).toNat) < 2 ^ 256
    apply Nat.or_lt_two_pow
    · simpa [UInt256.size] using hleftLt
    · simpa [UInt256.size] using hrightLt
  rw [Nat.mod_eq_of_lt hlorLt]
  exact nat_byte_lane_lor_clear_eq
    (old := (bytesStoreSetChunkByteHeaderWord σ I).toNat)
    (v := (bytesStoreSetChunkByteValueWord I).toNat)
    (k := (31 - (bytesStoreSetChunkByteIndexWord I).toNat) * 8) hv hk

theorem bytesStoreSetChunkByteLongStoredWord_byteAt
    {σ : AccountMap} {I : ExecutionEnv}
    (hcanon : (bytesStoreSetChunkByteValueWord I).toNat < EVM.twoPow 8) :
    UInt256.byteAt (bytesStoreSetChunkByteLongWordIndex I)
      (bytesStoreSetChunkByteLongStoredWord σ I) =
        bytesStoreSetChunkByteValueWord I := by
  apply u256_inj
  have hv : (bytesStoreSetChunkByteValueWord I).toNat < 256 := by
    simpa [EVM.twoPow] using hcanon
  have hidxLt : (bytesStoreSetChunkByteLongWordIndex I).toNat < 32 :=
    bytesStoreSetChunkByteLongWordIndex_lt32 I
  have hidxLe : (bytesStoreSetChunkByteLongWordIndex I).toNat ≤ 31 := by omega
  rw [byteAt_toNat_of_le31 hidxLe]
  rw [bytesStoreSetChunkByteLongStoredWord,
    bytesStoreSetChunkByteValueHighShiftDiv hcanon]
  rw [u256_lor_toNat, u256_mul_toNat, u256_land_toNat]
  rw [bytesStoreSetChunkByteLongScale_toNat (I := I)]
  rw [bytesStoreSetChunkByteLongClearMask_toNat (I := I)]
  have hk : ((31 - (bytesStoreSetChunkByteLongWordIndex I).toNat) * 8) + 8 ≤ 256 := by
    omega
  have hleftLt : (bytesStoreSetChunkByteValueWord I).toNat *
      2 ^ ((31 - (bytesStoreSetChunkByteLongWordIndex I).toNat) * 8) < UInt256.size := by
    rw [show UInt256.size = 2 ^ 256 from rfl]
    calc (bytesStoreSetChunkByteValueWord I).toNat *
            2 ^ ((31 - (bytesStoreSetChunkByteLongWordIndex I).toNat) * 8) <
          256 * 2 ^ ((31 - (bytesStoreSetChunkByteLongWordIndex I).toNat) * 8) :=
            Nat.mul_lt_mul_of_pos_right hv (by positivity)
        _ = 2 ^ (8 + (31 - (bytesStoreSetChunkByteLongWordIndex I).toNat) * 8) := by
          rw [show 256 = 2 ^ 8 by norm_num, Nat.pow_add]
        _ ≤ 2 ^ 256 := by
          exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hrightLt : (((2 : Nat) ^ 256 - 1 -
        255 * 2 ^ ((31 - (bytesStoreSetChunkByteLongWordIndex I).toNat) * 8)) &&&
        (bytesStoreSetChunkByteLongOldWord σ I).toNat) < UInt256.size := by
    exact lt_of_le_of_lt Nat.and_le_right (bytesStoreSetChunkByteLongOldWord σ I).val.isLt
  rw [Nat.mod_eq_of_lt hleftLt]
  change (((bytesStoreSetChunkByteValueWord I).toNat *
          2 ^ ((31 - (bytesStoreSetChunkByteLongWordIndex I).toNat) * 8)).lor
        ((((2 : Nat) ^ 256 - 1 -
          255 * 2 ^ ((31 - (bytesStoreSetChunkByteLongWordIndex I).toNat) * 8)) &&&
          (bytesStoreSetChunkByteLongOldWord σ I).toNat) % UInt256.size) %
        UInt256.size) /
      2 ^ ((31 - (bytesStoreSetChunkByteLongWordIndex I).toNat) * 8) % 256 =
    (bytesStoreSetChunkByteValueWord I).toNat
  rw [Nat.mod_eq_of_lt hrightLt]
  have hlorLt :
      ((bytesStoreSetChunkByteValueWord I).toNat *
            2 ^ ((31 - (bytesStoreSetChunkByteLongWordIndex I).toNat) * 8)).lor
          (((2 : Nat) ^ 256 - 1 -
              255 * 2 ^ ((31 - (bytesStoreSetChunkByteLongWordIndex I).toNat) * 8)) &&&
            (bytesStoreSetChunkByteLongOldWord σ I).toNat) < UInt256.size := by
    change ((bytesStoreSetChunkByteValueWord I).toNat *
          2 ^ ((31 - (bytesStoreSetChunkByteLongWordIndex I).toNat) * 8)) |||
        (((2 : Nat) ^ 256 - 1 -
            255 * 2 ^ ((31 - (bytesStoreSetChunkByteLongWordIndex I).toNat) * 8)) &&&
          (bytesStoreSetChunkByteLongOldWord σ I).toNat) < 2 ^ 256
    apply Nat.or_lt_two_pow
    · simpa [UInt256.size] using hleftLt
    · simpa [UInt256.size] using hrightLt
  rw [Nat.mod_eq_of_lt hlorLt]
  exact nat_byte_lane_lor_clear_eq
    (old := (bytesStoreSetChunkByteLongOldWord σ I).toNat)
    (v := (bytesStoreSetChunkByteValueWord I).toNat)
    (k := (31 - (bytesStoreSetChunkByteLongWordIndex I).toNat) * 8) hv hk

theorem bytesStoreSetChunkByteLongStoredWord_byteAt_index_of_lt32
    {σ : AccountMap} {I : ExecutionEnv}
    (hcanon : (bytesStoreSetChunkByteValueWord I).toNat < EVM.twoPow 8)
    (hidx : (bytesStoreSetChunkByteIndexWord I).toNat < 32) :
    UInt256.byteAt (bytesStoreSetChunkByteIndexWord I)
      (bytesStoreSetChunkByteLongStoredWord σ I) =
        bytesStoreSetChunkByteValueWord I := by
  have heq := bytesStoreSetChunkByteLongWordIndex_eq_index_of_lt32
    (I := I) hidx
  rw [← heq]
  exact bytesStoreSetChunkByteLongStoredWord_byteAt (σ := σ) (I := I) hcanon

theorem bytesStoreSetChunkByteShortStoredWord_toNat_update
    {σ : AccountMap} {I : ExecutionEnv} {len : UInt256}
    (hcanon : (bytesStoreSetChunkByteValueWord I).toNat < EVM.twoPow 8)
    (hshort : len.toNat < 32)
    (hbound : (bytesStoreSetChunkByteIndexWord I).toNat < len.toNat) :
    (bytesStoreSetChunkByteHeaderWord σ I).toNat %
          2 ^ ((31 - (bytesStoreSetChunkByteIndexWord I).toNat) * 8) +
        2 ^ ((31 - (bytesStoreSetChunkByteIndexWord I).toNat) * 8) *
          (bytesStoreSetChunkByteValueWord I).toNat +
      2 ^ ((31 - (bytesStoreSetChunkByteIndexWord I).toNat) * 8 + 8) *
        ((bytesStoreSetChunkByteHeaderWord σ I).toNat /
          2 ^ ((31 - (bytesStoreSetChunkByteIndexWord I).toNat) * 8 + 8)) =
    (bytesStoreSetChunkByteShortStoredWord σ I).toNat := by
  have hv : (bytesStoreSetChunkByteValueWord I).toNat < 256 := by
    simpa [EVM.twoPow] using hcanon
  rw [bytesStoreSetChunkByteShortStoredWord,
    bytesStoreSetChunkByteValueHighShiftDiv hcanon]
  rw [u256_lor_toNat, u256_mul_toNat, u256_land_toNat]
  rw [bytesStoreSetChunkByteShortScale_toNat (I := I) (len := len) hshort hbound]
  rw [bytesStoreSetChunkByteShortClearMask_toNat (I := I) (len := len) hshort hbound]
  have hk : ((31 - (bytesStoreSetChunkByteIndexWord I).toNat) * 8) + 8 ≤ 256 := by
    have hidx := bytesStoreSetChunkByteIndex_lt31_of_short_bound
      (I := I) (len := len) hshort hbound
    omega
  have hleftLt : (bytesStoreSetChunkByteValueWord I).toNat *
      2 ^ ((31 - (bytesStoreSetChunkByteIndexWord I).toNat) * 8) < UInt256.size := by
    rw [show UInt256.size = 2 ^ 256 from rfl]
    calc (bytesStoreSetChunkByteValueWord I).toNat *
            2 ^ ((31 - (bytesStoreSetChunkByteIndexWord I).toNat) * 8) <
          256 * 2 ^ ((31 - (bytesStoreSetChunkByteIndexWord I).toNat) * 8) :=
            Nat.mul_lt_mul_of_pos_right hv (by positivity)
        _ ≤ 2 ^ 256 := by
          rw [show 256 = 2 ^ 8 by norm_num, ← Nat.pow_add]
          exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hrightLt : (((2 : Nat) ^ 256 - 1 -
        255 * 2 ^ ((31 - (bytesStoreSetChunkByteIndexWord I).toNat) * 8)) &&&
        (bytesStoreSetChunkByteHeaderWord σ I).toNat) < UInt256.size := by
    exact lt_of_le_of_lt Nat.and_le_right (bytesStoreSetChunkByteHeaderWord σ I).val.isLt
  rw [Nat.mod_eq_of_lt hleftLt]
  change (bytesStoreSetChunkByteHeaderWord σ I).toNat %
        2 ^ ((31 - (bytesStoreSetChunkByteIndexWord I).toNat) * 8) +
      2 ^ ((31 - (bytesStoreSetChunkByteIndexWord I).toNat) * 8) *
        (bytesStoreSetChunkByteValueWord I).toNat +
      2 ^ (((31 - (bytesStoreSetChunkByteIndexWord I).toNat) * 8) + 8) *
        ((bytesStoreSetChunkByteHeaderWord σ I).toNat /
          2 ^ (((31 - (bytesStoreSetChunkByteIndexWord I).toNat) * 8) + 8)) =
      ((bytesStoreSetChunkByteValueWord I).toNat *
          2 ^ ((31 - (bytesStoreSetChunkByteIndexWord I).toNat) * 8)).lor
        ((((2 : Nat) ^ 256 - 1 -
          255 * 2 ^ ((31 - (bytesStoreSetChunkByteIndexWord I).toNat) * 8)) &&&
          (bytesStoreSetChunkByteHeaderWord σ I).toNat) % UInt256.size) %
        UInt256.size
  rw [Nat.mod_eq_of_lt hrightLt]
  have hlorLt :
      ((bytesStoreSetChunkByteValueWord I).toNat *
            2 ^ ((31 - (bytesStoreSetChunkByteIndexWord I).toNat) * 8)).lor
          (((2 : Nat) ^ 256 - 1 -
              255 * 2 ^ ((31 - (bytesStoreSetChunkByteIndexWord I).toNat) * 8)) &&&
            (bytesStoreSetChunkByteHeaderWord σ I).toNat) < UInt256.size := by
    change ((bytesStoreSetChunkByteValueWord I).toNat *
          2 ^ ((31 - (bytesStoreSetChunkByteIndexWord I).toNat) * 8)) |||
        (((2 : Nat) ^ 256 - 1 -
            255 * 2 ^ ((31 - (bytesStoreSetChunkByteIndexWord I).toNat) * 8)) &&&
          (bytesStoreSetChunkByteHeaderWord σ I).toNat) < 2 ^ 256
    apply Nat.or_lt_two_pow
    · simpa [UInt256.size] using hleftLt
    · simpa [UInt256.size] using hrightLt
  rw [Nat.mod_eq_of_lt hlorLt]
  rw [show 2 ^ ((31 - (bytesStoreSetChunkByteIndexWord I).toNat) * 8) *
        (bytesStoreSetChunkByteValueWord I).toNat =
        (bytesStoreSetChunkByteValueWord I).toNat *
          2 ^ ((31 - (bytesStoreSetChunkByteIndexWord I).toNat) * 8) by ring]
  rw [show 2 ^ (((31 - (bytesStoreSetChunkByteIndexWord I).toNat) * 8) + 8) *
        ((bytesStoreSetChunkByteHeaderWord σ I).toNat /
          2 ^ (((31 - (bytesStoreSetChunkByteIndexWord I).toNat) * 8) + 8)) =
      (bytesStoreSetChunkByteHeaderWord σ I).toNat /
          2 ^ (((31 - (bytesStoreSetChunkByteIndexWord I).toNat) * 8) + 8) *
        2 ^ (((31 - (bytesStoreSetChunkByteIndexWord I).toNat) * 8) + 8) by ring]
  exact nat_byte_update_eq
    (old := (bytesStoreSetChunkByteHeaderWord σ I).toNat)
    (v := (bytesStoreSetChunkByteValueWord I).toNat)
    (k := (31 - (bytesStoreSetChunkByteIndexWord I).toNat) * 8)
    hv hk (by exact (bytesStoreSetChunkByteHeaderWord σ I).val.isLt)

theorem bytesStoreSetChunkByteLongStoredWord_toNat_update
    {σ : AccountMap} {I : ExecutionEnv}
    (hcanon : (bytesStoreSetChunkByteValueWord I).toNat < EVM.twoPow 8) :
    (bytesStoreSetChunkByteLongOldWord σ I).toNat %
          2 ^ ((31 - (bytesStoreSetChunkByteLongWordIndex I).toNat) * 8) +
        2 ^ ((31 - (bytesStoreSetChunkByteLongWordIndex I).toNat) * 8) *
          (bytesStoreSetChunkByteValueWord I).toNat +
      2 ^ ((31 - (bytesStoreSetChunkByteLongWordIndex I).toNat) * 8 + 8) *
        ((bytesStoreSetChunkByteLongOldWord σ I).toNat /
          2 ^ ((31 - (bytesStoreSetChunkByteLongWordIndex I).toNat) * 8 + 8)) =
    (bytesStoreSetChunkByteLongStoredWord σ I).toNat := by
  have hv : (bytesStoreSetChunkByteValueWord I).toNat < 256 := by
    simpa [EVM.twoPow] using hcanon
  rw [bytesStoreSetChunkByteLongStoredWord,
    bytesStoreSetChunkByteValueHighShiftDiv hcanon]
  rw [u256_lor_toNat, u256_mul_toNat, u256_land_toNat]
  rw [bytesStoreSetChunkByteLongScale_toNat (I := I)]
  rw [bytesStoreSetChunkByteLongClearMask_toNat (I := I)]
  have hidxLt : (bytesStoreSetChunkByteLongWordIndex I).toNat < 32 :=
    bytesStoreSetChunkByteLongWordIndex_lt32 I
  have hk : ((31 - (bytesStoreSetChunkByteLongWordIndex I).toNat) * 8) + 8 ≤ 256 := by
    omega
  have hleftLt : (bytesStoreSetChunkByteValueWord I).toNat *
      2 ^ ((31 - (bytesStoreSetChunkByteLongWordIndex I).toNat) * 8) < UInt256.size := by
    rw [show UInt256.size = 2 ^ 256 from rfl]
    calc (bytesStoreSetChunkByteValueWord I).toNat *
            2 ^ ((31 - (bytesStoreSetChunkByteLongWordIndex I).toNat) * 8) <
          256 * 2 ^ ((31 - (bytesStoreSetChunkByteLongWordIndex I).toNat) * 8) :=
            Nat.mul_lt_mul_of_pos_right hv (by positivity)
        _ = 2 ^ (8 + (31 - (bytesStoreSetChunkByteLongWordIndex I).toNat) * 8) := by
          rw [show 256 = 2 ^ 8 by norm_num, Nat.pow_add]
        _ ≤ 2 ^ 256 := by
          exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hrightLt : (((2 : Nat) ^ 256 - 1 -
        255 * 2 ^ ((31 - (bytesStoreSetChunkByteLongWordIndex I).toNat) * 8)) &&&
        (bytesStoreSetChunkByteLongOldWord σ I).toNat) < UInt256.size := by
    exact lt_of_le_of_lt Nat.and_le_right (bytesStoreSetChunkByteLongOldWord σ I).val.isLt
  rw [Nat.mod_eq_of_lt hleftLt]
  change (bytesStoreSetChunkByteLongOldWord σ I).toNat %
        2 ^ ((31 - (bytesStoreSetChunkByteLongWordIndex I).toNat) * 8) +
      2 ^ ((31 - (bytesStoreSetChunkByteLongWordIndex I).toNat) * 8) *
        (bytesStoreSetChunkByteValueWord I).toNat +
      2 ^ (((31 - (bytesStoreSetChunkByteLongWordIndex I).toNat) * 8) + 8) *
        ((bytesStoreSetChunkByteLongOldWord σ I).toNat /
          2 ^ (((31 - (bytesStoreSetChunkByteLongWordIndex I).toNat) * 8) + 8)) =
      ((bytesStoreSetChunkByteValueWord I).toNat *
          2 ^ ((31 - (bytesStoreSetChunkByteLongWordIndex I).toNat) * 8)).lor
        ((((2 : Nat) ^ 256 - 1 -
          255 * 2 ^ ((31 - (bytesStoreSetChunkByteLongWordIndex I).toNat) * 8)) &&&
          (bytesStoreSetChunkByteLongOldWord σ I).toNat) % UInt256.size) %
        UInt256.size
  rw [Nat.mod_eq_of_lt hrightLt]
  have hlorLt :
      ((bytesStoreSetChunkByteValueWord I).toNat *
            2 ^ ((31 - (bytesStoreSetChunkByteLongWordIndex I).toNat) * 8)).lor
          (((2 : Nat) ^ 256 - 1 -
              255 * 2 ^ ((31 - (bytesStoreSetChunkByteLongWordIndex I).toNat) * 8)) &&&
            (bytesStoreSetChunkByteLongOldWord σ I).toNat) < UInt256.size := by
    change ((bytesStoreSetChunkByteValueWord I).toNat *
          2 ^ ((31 - (bytesStoreSetChunkByteLongWordIndex I).toNat) * 8)) |||
        (((2 : Nat) ^ 256 - 1 -
            255 * 2 ^ ((31 - (bytesStoreSetChunkByteLongWordIndex I).toNat) * 8)) &&&
          (bytesStoreSetChunkByteLongOldWord σ I).toNat) < 2 ^ 256
    apply Nat.or_lt_two_pow
    · simpa [UInt256.size] using hleftLt
    · simpa [UInt256.size] using hrightLt
  rw [Nat.mod_eq_of_lt hlorLt]
  rw [show 2 ^ ((31 - (bytesStoreSetChunkByteLongWordIndex I).toNat) * 8) *
        (bytesStoreSetChunkByteValueWord I).toNat =
        (bytesStoreSetChunkByteValueWord I).toNat *
          2 ^ ((31 - (bytesStoreSetChunkByteLongWordIndex I).toNat) * 8) by ring]
  rw [show 2 ^ (((31 - (bytesStoreSetChunkByteLongWordIndex I).toNat) * 8) + 8) *
        ((bytesStoreSetChunkByteLongOldWord σ I).toNat /
          2 ^ (((31 - (bytesStoreSetChunkByteLongWordIndex I).toNat) * 8) + 8)) =
      (bytesStoreSetChunkByteLongOldWord σ I).toNat /
          2 ^ (((31 - (bytesStoreSetChunkByteLongWordIndex I).toNat) * 8) + 8) *
        2 ^ (((31 - (bytesStoreSetChunkByteLongWordIndex I).toNat) * 8) + 8) by ring]
  exact nat_byte_update_eq
    (old := (bytesStoreSetChunkByteLongOldWord σ I).toNat)
    (v := (bytesStoreSetChunkByteValueWord I).toNat)
    (k := (31 - (bytesStoreSetChunkByteLongWordIndex I).toNat) * 8)
    hv hk (by exact (bytesStoreSetChunkByteLongOldWord σ I).val.isLt)

theorem bytesStoreSetChunkByteShortScale_mod256_zero {I : ExecutionEnv} {len : UInt256}
    (hshort : len.toNat < 32)
    (hbound : (bytesStoreSetChunkByteIndexWord I).toNat < len.toNat) :
    (bytesStoreSetChunkByteShortScale I).toNat % 256 = 0 := by
  have hidx : (bytesStoreSetChunkByteIndexWord I).toNat < 31 :=
    bytesStoreSetChunkByteIndex_lt31_of_short_bound hshort hbound
  interval_cases hnat : (bytesStoreSetChunkByteIndexWord I).toNat
  all_goals
    have hword : bytesStoreSetChunkByteIndexWord I =
        UInt256.ofNat (bytesStoreSetChunkByteIndexWord I).toNat := by
      exact (u256_ofNat_toNat (bytesStoreSetChunkByteIndexWord I)).symm
    rw [bytesStoreSetChunkByteShortScale, hword, hnat]
    native_decide

theorem bytesStoreSetChunkByteShortClearMask_mod256_255 {I : ExecutionEnv} {len : UInt256}
    (hshort : len.toNat < 32)
    (hbound : (bytesStoreSetChunkByteIndexWord I).toNat < len.toNat) :
    (UInt256.lnot (UInt256.mul ⟨255⟩ (bytesStoreSetChunkByteShortScale I))).toNat % 256 =
      255 := by
  have hidx : (bytesStoreSetChunkByteIndexWord I).toNat < 31 :=
    bytesStoreSetChunkByteIndex_lt31_of_short_bound hshort hbound
  interval_cases hnat : (bytesStoreSetChunkByteIndexWord I).toNat
  all_goals
    have hword : bytesStoreSetChunkByteIndexWord I =
        UInt256.ofNat (bytesStoreSetChunkByteIndexWord I).toNat := by
      exact (u256_ofNat_toNat (bytesStoreSetChunkByteIndexWord I)).symm
    rw [bytesStoreSetChunkByteShortScale, hword, hnat]
    native_decide

theorem bytesStoreSetChunkByteShortStoredWord_mod256
    {σ : AccountMap} {I : ExecutionEnv} {len : UInt256}
    (hshort : len.toNat < 32)
    (hbound : (bytesStoreSetChunkByteIndexWord I).toNat < len.toNat) :
    (bytesStoreSetChunkByteShortStoredWord σ I).toNat % 256 =
      (bytesStoreSetChunkByteHeaderWord σ I).toNat % 256 := by
  have hscale := bytesStoreSetChunkByteShortScale_mod256_zero
    (I := I) (len := len) hshort hbound
  have hmask := bytesStoreSetChunkByteShortClearMask_mod256_255
    (I := I) (len := len) hshort hbound
  have hleft :
      (UInt256.mul
        (UInt256.div (UInt256.shiftLeft (bytesStoreSetChunkByteValueWord I) ⟨248⟩)
          (UInt256.shiftLeft ⟨1⟩ ⟨248⟩))
        (bytesStoreSetChunkByteShortScale I)).toNat % 256 = 0 := by
    rw [u256_mul_toNat, nat_mod_u256_mod_256, Nat.mul_mod, hscale]
    simp
  have hright :
      (UInt256.land
        (UInt256.lnot (UInt256.mul ⟨255⟩ (bytesStoreSetChunkByteShortScale I)))
        (bytesStoreSetChunkByteHeaderWord σ I)).toNat % 256 =
        (bytesStoreSetChunkByteHeaderWord σ I).toNat % 256 := by
    rw [u256_land_toNat, nat_mod_u256_mod_256]
    exact nat_land_mod_256_of_left_255 hmask
  rw [bytesStoreSetChunkByteShortStoredWord, u256_lor_toNat, nat_mod_u256_mod_256]
  rw [nat_lor_mod_256_of_left_zero hleft, hright]

theorem bytesStoreSetChunkByteShortStoredWord_flag_eq
    {σ : AccountMap} {I : ExecutionEnv} {len : UInt256}
    (hshort : len.toNat < 32)
    (hbound : (bytesStoreSetChunkByteIndexWord I).toNat < len.toNat) :
    UInt256.land (bytesStoreSetChunkByteShortStoredWord σ I) ⟨1⟩ =
      UInt256.land (bytesStoreSetChunkByteHeaderWord σ I) ⟨1⟩ := by
  apply u256_inj
  rw [uInt256_land_one_toNat, uInt256_land_one_toNat]
  have hmod := bytesStoreSetChunkByteShortStoredWord_mod256
    (σ := σ) (I := I) (len := len) hshort hbound
  have hleft :
      (bytesStoreSetChunkByteShortStoredWord σ I).toNat % 2 =
        ((bytesStoreSetChunkByteShortStoredWord σ I).toNat % 256) % 2 := by
    rw [Nat.mod_mod_of_dvd]
    norm_num
  have hright :
      (bytesStoreSetChunkByteHeaderWord σ I).toNat % 2 =
        ((bytesStoreSetChunkByteHeaderWord σ I).toNat % 256) % 2 := by
    rw [Nat.mod_mod_of_dvd]
    norm_num
  rw [hleft, hright, hmod]

theorem bytesStoreSetChunkByteShortStoredWord_shortLen_eq
    {σ : AccountMap} {I : ExecutionEnv} {len : UInt256}
    (hshort : len.toNat < 32)
    (hbound : (bytesStoreSetChunkByteIndexWord I).toNat < len.toNat) :
    UInt256.land (UInt256.div (bytesStoreSetChunkByteShortStoredWord σ I) ⟨2⟩) ⟨127⟩ =
      UInt256.land (UInt256.div (bytesStoreSetChunkByteHeaderWord σ I) ⟨2⟩) ⟨127⟩ := by
  apply u256_inj
  rw [bytesStoreShortLenBits_toNat, bytesStoreShortLenBits_toNat]
  rw [bytesStoreSetChunkByteShortStoredWord_mod256 (σ := σ) (I := I) (len := len)
    hshort hbound]

theorem bytesStoreSetChunkByteStorageLocStoreShort
    {evm : EVM.State} {σ : AccountMap} {I : ExecutionEnv} {len : UInt256}
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (bytesStoreSetChunkByteSlot I) = bytesStoreSetChunkByteHeaderWord σ I)
    (hcanon : (bytesStoreSetChunkByteValueWord I).toNat < EVM.twoPow 8)
    (hshort : len.toNat < 32)
    (hbound : (bytesStoreSetChunkByteIndexWord I).toNat < len.toNat) :
    storageLocStore evm
      (uint8Loc (bytesStoreSetChunkByteSlot I)
        ⟨31 - (bytesStoreSetChunkByteIndexWord I).toNat, by
          have hidx := bytesStoreSetChunkByteIndex_lt31_of_short_bound
            (I := I) (len := len) hshort hbound
          omega⟩)
      (bytesStoreSetChunkByteValue I) =
      some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner
        (bytesStoreSetChunkByteSlot I)
        (bytesStoreSetChunkByteShortStoredWord σ I)) := by
  let offFin : Fin 32 :=
    ⟨31 - (bytesStoreSetChunkByteIndexWord I).toNat, by
      have hidx := bytesStoreSetChunkByteIndex_lt31_of_short_bound
        (I := I) (len := len) hshort hbound
      omega⟩
  have hbyte : (bytesStoreSetChunkByteValueWord I).toNat < 256 := by
    simpa [EVM.twoPow] using hcanon
  have hoffBound : offFin.val + (1 : Fin 33).val - 1 < 32 := by
    have hidx := bytesStoreSetChunkByteIndex_lt31_of_short_bound
      (I := I) (len := len) hshort hbound
    simp [offFin]
    omega
  have htarget :
      (bytesStoreSetChunkByteShortStoredWord σ I).toNat =
        (bytesStoreSetChunkByteHeaderWord σ I).toNat % 2 ^ (8 * offFin.val) +
          2 ^ (8 * offFin.val) * (bytesStoreSetChunkByteValueWord I).toNat +
          2 ^ (8 * offFin.val + 8) *
            ((bytesStoreSetChunkByteHeaderWord σ I).toNat /
              2 ^ (8 * offFin.val + 8)) := by
    change
      (bytesStoreSetChunkByteShortStoredWord σ I).toNat =
        (bytesStoreSetChunkByteHeaderWord σ I).toNat %
            2 ^ (8 * (31 - (bytesStoreSetChunkByteIndexWord I).toNat)) +
          2 ^ (8 * (31 - (bytesStoreSetChunkByteIndexWord I).toNat)) *
            (bytesStoreSetChunkByteValueWord I).toNat +
          2 ^ (8 * (31 - (bytesStoreSetChunkByteIndexWord I).toNat) + 8) *
            ((bytesStoreSetChunkByteHeaderWord σ I).toNat /
              2 ^ (8 * (31 - (bytesStoreSetChunkByteIndexWord I).toNat) + 8))
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
      (bytesStoreSetChunkByteShortStoredWord_toNat_update
        (σ := σ) (I := I) (len := len) hcanon hshort hbound).symm
  change storageLocStore evm
      { slot := bytesStoreSetChunkByteSlot I, offset := offFin, size := 1,
        hbound := hoffBound, type := .int uint8Int }
      (bytesStoreSetChunkByteValue I) =
      some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner
        (bytesStoreSetChunkByteSlot I)
        (bytesStoreSetChunkByteShortStoredWord σ I))
  exact storageLocStore_oneByte_int_ofNat_update evm
    (bytesStoreSetChunkByteSlot I) (bytesStoreSetChunkByteHeaderWord σ I)
    (bytesStoreSetChunkByteShortStoredWord σ I) offFin (.int uint8Int) hoffBound
    (bytesStoreSetChunkByteValueWord I).toNat hload hbyte htarget

theorem bytesStoreSetChunkByteStorageLocStoreLong
    {evm : EVM.State} {σ : AccountMap} {I : ExecutionEnv}
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (bytesStoreSetChunkByteLongDataSlot I) =
      bytesStoreSetChunkByteLongOldWord σ I)
    (hcanon : (bytesStoreSetChunkByteValueWord I).toNat < EVM.twoPow 8) :
    storageLocStore evm
      (uint8Loc (bytesStoreSetChunkByteLongDataSlot I)
        ⟨31 - (bytesStoreSetChunkByteLongWordIndex I).toNat, by
          have hidx := bytesStoreSetChunkByteLongWordIndex_lt32 I
          omega⟩)
      (bytesStoreSetChunkByteValue I) =
      some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner
        (bytesStoreSetChunkByteLongDataSlot I)
        (bytesStoreSetChunkByteLongStoredWord σ I)) := by
  let offFin : Fin 32 :=
    ⟨31 - (bytesStoreSetChunkByteLongWordIndex I).toNat, by
      have hidx := bytesStoreSetChunkByteLongWordIndex_lt32 I
      omega⟩
  have hbyte : (bytesStoreSetChunkByteValueWord I).toNat < 256 := by
    simpa [EVM.twoPow] using hcanon
  have hoffBound : offFin.val + (1 : Fin 33).val - 1 < 32 := by
    simp [offFin]
    omega
  have htarget :
      (bytesStoreSetChunkByteLongStoredWord σ I).toNat =
        (bytesStoreSetChunkByteLongOldWord σ I).toNat % 2 ^ (8 * offFin.val) +
          2 ^ (8 * offFin.val) * (bytesStoreSetChunkByteValueWord I).toNat +
          2 ^ (8 * offFin.val + 8) *
            ((bytesStoreSetChunkByteLongOldWord σ I).toNat /
              2 ^ (8 * offFin.val + 8)) := by
    change
      (bytesStoreSetChunkByteLongStoredWord σ I).toNat =
        (bytesStoreSetChunkByteLongOldWord σ I).toNat %
            2 ^ (8 * (31 - (bytesStoreSetChunkByteLongWordIndex I).toNat)) +
          2 ^ (8 * (31 - (bytesStoreSetChunkByteLongWordIndex I).toNat)) *
            (bytesStoreSetChunkByteValueWord I).toNat +
          2 ^ (8 * (31 - (bytesStoreSetChunkByteLongWordIndex I).toNat) + 8) *
            ((bytesStoreSetChunkByteLongOldWord σ I).toNat /
              2 ^ (8 * (31 - (bytesStoreSetChunkByteLongWordIndex I).toNat) + 8))
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
      (bytesStoreSetChunkByteLongStoredWord_toNat_update
        (σ := σ) (I := I) hcanon).symm
  change storageLocStore evm
      { slot := bytesStoreSetChunkByteLongDataSlot I, offset := offFin, size := 1,
        hbound := hoffBound, type := .int uint8Int }
      (bytesStoreSetChunkByteValue I) =
      some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner
        (bytesStoreSetChunkByteLongDataSlot I)
        (bytesStoreSetChunkByteLongStoredWord σ I))
  exact storageLocStore_oneByte_int_ofNat_update evm
    (bytesStoreSetChunkByteLongDataSlot I) (bytesStoreSetChunkByteLongOldWord σ I)
    (bytesStoreSetChunkByteLongStoredWord σ I) offFin (.int uint8Int) hoffBound
    (bytesStoreSetChunkByteValueWord I).toNat hload hbyte htarget

theorem bytesStoreSetChunkByteEvalStorageRefOfLength {evm : EVM.State}
    {I : ExecutionEnv} {chunksLen : UInt256} {len : Nat}
    (hload :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩ = chunksLen)
    (hchunkBound :
      (bytesStoreSetChunkByteChunkIndexWord I).toNat < chunksLen.toNat)
    (hlen : readStorageBytesLength? bytesStoreConfig evm
      (bytesStoreSetChunkByteHeaderRef I) = .ok len)
    (hbound : (bytesStoreSetChunkByteIndexWord I).toNat < len) :
    evalStorageRef bytesStoreConfig
      (bytesStoreSetChunkByteFrame I)
      evm (chunkByteRef (.var "chunkIndex") (.var "byteIndex")) =
        .ok (bytesStoreSetChunkByteRef I) := by
  have hgetChunkIndex :
      (bytesStoreSetChunkByteFrame I).locals.get? "chunkIndex" =
        some (.int (Int.ofNat (bytesStoreSetChunkByteChunkIndexWord I).toNat)) := by
    simpa [bytesStoreSetChunkByteFrame] using
      bytesStoreSetChunkByteLocals_get_chunkIndex I
  have hgetByteIndex :
      (bytesStoreSetChunkByteFrame I).locals.get? "byteIndex" =
        some (.int (Int.ofNat (bytesStoreSetChunkByteIndexWord I).toNat)) := by
    simpa [bytesStoreSetChunkByteFrame] using
      bytesStoreSetChunkByteLocals_get_byteIndex I
  have hgetChunkIndexElem :
      (bytesStoreSetChunkByteLocals I)["chunkIndex"]? =
        some (.int (Int.ofNat (bytesStoreSetChunkByteChunkIndexWord I).toNat)) :=
    bytesStoreSetChunkByteLocals_getElem_chunkIndex I
  have hindexKey :
      valueToKey? (.int (Int.ofNat (bytesStoreSetChunkByteIndexWord I).toNat)) =
        some (.int (Int.ofNat (bytesStoreSetChunkByteIndexWord I).toNat)) := by
    simp [valueToKey?]
  have hlen' :
      readStorageBytesLength?
        { storage := bytesStoreStorageLayout, externalABI := defaultExternalCallABI,
          selfDeployment := genSolidityConstructorDeployment [] }
        evm (bytesStoreSetChunkByteHeaderRef I) = .ok len := by
    simpa [bytesStoreConfig] using hlen
  let headerRef : EvaledStorageRef :=
    { base := "chunks"
      steps := [.aindex
        (.int ((bytesStoreSetChunkByteChunkIndexWord I).toNat : Int))] }
  have hlenHeader :
      readStorageBytesLength?
        { storage := bytesStoreStorageLayout, externalABI := defaultExternalCallABI,
          selfDeployment := genSolidityConstructorDeployment [] }
        evm headerRef = .ok len := by
    simpa [headerRef, bytesStoreSetChunkByteHeaderRef] using hlen'
  simp only [headerRef, bytesStoreStorageLayout, solidityStorageLayout] at hlenHeader
  have hstep :
      evalStorageRefStep bytesStoreConfig (bytesStoreSetChunkByteFrame I) evm
        "chunks" [] (.aindex (.var "chunkIndex")) =
        .ok (.aindex (.int (Int.ofNat (bytesStoreSetChunkByteChunkIndexWord I).toNat))) := by
    simp [evalStorageRefStep, evalExpr?, bytesStoreSetChunkByteFrame,
      hgetChunkIndexElem, valueToKey?, EvalResult.ofOption, EvalResult.bind, bind, pure,
      arrayIndexInBounds?, storageTypeAt?, bytesStoreConfig, bytesStoreContract,
      storageDecls, bytesSt, bytesStoreStorageLayout, solidityStorageLayout,
      bytesStoreLayout, bytesStoreStorageLocLoad_uint256, hload, hchunkBound]
  have hbounds :
      arrayIndexInBounds? bytesStoreConfig evm
        (bytesStoreSetChunkByteFrame I).contract.storage "chunks"
        [.aindex (.int (Int.ofNat (bytesStoreSetChunkByteChunkIndexWord I).toNat))]
        (.int (Int.ofNat (bytesStoreSetChunkByteIndexWord I).toNat)) = .ok () := by
    simp [arrayIndexInBounds?, storageTypeAt?, bytesStoreConfig, bytesStoreSetChunkByteFrame,
      bytesStoreContract, storageDecls, storageTypeStep?, bytesSt, bytesStoreStorageLayout,
      solidityStorageLayout, hlenHeader, hbound]
  simpa [chunkByteRef, bytesStoreSetChunkByteRef] using
    (evalStorageRef_step_aindex_var_of_get?_ok
      (cfg := bytesStoreConfig) (solm := bytesStoreSetChunkByteFrame I) (evm := evm)
      (base := "chunks") (name := "byteIndex") (step := .aindex (.var "chunkIndex"))
      (estep := .aindex (.int (Int.ofNat (bytesStoreSetChunkByteChunkIndexWord I).toNat)))
      hstep hgetByteIndex hindexKey hbounds)

theorem bytesStoreSetChunkByteEvalStorageRefRevertsOfLength {evm : EVM.State}
    {I : ExecutionEnv} {chunksLen : UInt256} {len : Nat}
    (hload :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩ = chunksLen)
    (hchunkBound :
      (bytesStoreSetChunkByteChunkIndexWord I).toNat < chunksLen.toNat)
    (hlen : readStorageBytesLength? bytesStoreConfig evm
      (bytesStoreSetChunkByteHeaderRef I) = .ok len)
    (hbound : ¬ (bytesStoreSetChunkByteIndexWord I).toNat < len) :
    evalStorageRef bytesStoreConfig
      (bytesStoreSetChunkByteFrame I)
      evm (chunkByteRef (.var "chunkIndex") (.var "byteIndex")) = .revert := by
  have hgetChunkIndex :
      (bytesStoreSetChunkByteFrame I).locals.get? "chunkIndex" =
        some (.int (Int.ofNat (bytesStoreSetChunkByteChunkIndexWord I).toNat)) := by
    simpa [bytesStoreSetChunkByteFrame] using
      bytesStoreSetChunkByteLocals_get_chunkIndex I
  have hgetByteIndex :
      (bytesStoreSetChunkByteFrame I).locals.get? "byteIndex" =
        some (.int (Int.ofNat (bytesStoreSetChunkByteIndexWord I).toNat)) := by
    simpa [bytesStoreSetChunkByteFrame] using
      bytesStoreSetChunkByteLocals_get_byteIndex I
  have hgetChunkIndexElem :
      (bytesStoreSetChunkByteLocals I)["chunkIndex"]? =
        some (.int (Int.ofNat (bytesStoreSetChunkByteChunkIndexWord I).toNat)) :=
    bytesStoreSetChunkByteLocals_getElem_chunkIndex I
  have hindexKey :
      valueToKey? (.int (Int.ofNat (bytesStoreSetChunkByteIndexWord I).toNat)) =
        some (.int (Int.ofNat (bytesStoreSetChunkByteIndexWord I).toNat)) := by
    simp [valueToKey?]
  have hlen' :
      readStorageBytesLength?
        { storage := bytesStoreStorageLayout, externalABI := defaultExternalCallABI,
          selfDeployment := genSolidityConstructorDeployment [] }
        evm (bytesStoreSetChunkByteHeaderRef I) = .ok len := by
    simpa [bytesStoreConfig] using hlen
  let headerRef : EvaledStorageRef :=
    { base := "chunks"
      steps := [.aindex
        (.int ((bytesStoreSetChunkByteChunkIndexWord I).toNat : Int))] }
  have hlenHeader :
      readStorageBytesLength?
        { storage := bytesStoreStorageLayout, externalABI := defaultExternalCallABI,
          selfDeployment := genSolidityConstructorDeployment [] }
        evm headerRef = .ok len := by
    simpa [headerRef, bytesStoreSetChunkByteHeaderRef] using hlen'
  simp only [headerRef, bytesStoreStorageLayout, solidityStorageLayout] at hlenHeader
  have hstep :
      evalStorageRefStep bytesStoreConfig (bytesStoreSetChunkByteFrame I) evm
        "chunks" [] (.aindex (.var "chunkIndex")) =
        .ok (.aindex (.int (Int.ofNat (bytesStoreSetChunkByteChunkIndexWord I).toNat))) := by
    simp [evalStorageRefStep, evalExpr?, bytesStoreSetChunkByteFrame,
      hgetChunkIndexElem, valueToKey?, EvalResult.ofOption, EvalResult.bind, bind, pure,
      arrayIndexInBounds?, storageTypeAt?, bytesStoreConfig, bytesStoreContract,
      storageDecls, bytesSt, bytesStoreStorageLayout, solidityStorageLayout,
      bytesStoreLayout, bytesStoreStorageLocLoad_uint256, hload, hchunkBound]
  have hbounds :
      arrayIndexInBounds? bytesStoreConfig evm
        (bytesStoreSetChunkByteFrame I).contract.storage "chunks"
        [.aindex (.int (Int.ofNat (bytesStoreSetChunkByteChunkIndexWord I).toNat))]
        (.int (Int.ofNat (bytesStoreSetChunkByteIndexWord I).toNat)) = .revert := by
    simp [arrayIndexInBounds?, storageTypeAt?, bytesStoreConfig, bytesStoreSetChunkByteFrame,
      bytesStoreContract, storageDecls, storageTypeStep?, bytesSt, bytesStoreStorageLayout,
      solidityStorageLayout, hlenHeader, hbound]
  simpa [chunkByteRef] using
    (evalStorageRef_step_aindex_var_of_get?_revert
      (cfg := bytesStoreConfig) (solm := bytesStoreSetChunkByteFrame I) (evm := evm)
      (base := "chunks") (name := "byteIndex") (step := .aindex (.var "chunkIndex"))
      (estep := .aindex (.int (Int.ofNat (bytesStoreSetChunkByteChunkIndexWord I).toNat)))
      hstep hgetByteIndex hindexKey hbounds)

theorem bytesStoreSetChunkByteEvalStorageRefRevertsOfLengthRead {evm : EVM.State}
    {I : ExecutionEnv} {chunksLen : UInt256}
    (hload :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩ = chunksLen)
    (hchunkBound :
      (bytesStoreSetChunkByteChunkIndexWord I).toNat < chunksLen.toNat)
    (hlen : readStorageBytesLength? bytesStoreConfig evm
      (bytesStoreSetChunkByteHeaderRef I) = .revert) :
    evalStorageRef bytesStoreConfig
      (bytesStoreSetChunkByteFrame I)
      evm (chunkByteRef (.var "chunkIndex") (.var "byteIndex")) = .revert := by
  have hgetChunkIndex :
      (bytesStoreSetChunkByteFrame I).locals.get? "chunkIndex" =
        some (.int (Int.ofNat (bytesStoreSetChunkByteChunkIndexWord I).toNat)) := by
    simpa [bytesStoreSetChunkByteFrame] using
      bytesStoreSetChunkByteLocals_get_chunkIndex I
  have hgetByteIndex :
      (bytesStoreSetChunkByteFrame I).locals.get? "byteIndex" =
        some (.int (Int.ofNat (bytesStoreSetChunkByteIndexWord I).toNat)) := by
    simpa [bytesStoreSetChunkByteFrame] using
      bytesStoreSetChunkByteLocals_get_byteIndex I
  have hgetChunkIndexElem :
      (bytesStoreSetChunkByteLocals I)["chunkIndex"]? =
        some (.int (Int.ofNat (bytesStoreSetChunkByteChunkIndexWord I).toNat)) :=
    bytesStoreSetChunkByteLocals_getElem_chunkIndex I
  have hindexKey :
      valueToKey? (.int (Int.ofNat (bytesStoreSetChunkByteIndexWord I).toNat)) =
        some (.int (Int.ofNat (bytesStoreSetChunkByteIndexWord I).toNat)) := by
    simp [valueToKey?]
  have hlen' :
      readStorageBytesLength?
        { storage := bytesStoreStorageLayout, externalABI := defaultExternalCallABI,
          selfDeployment := genSolidityConstructorDeployment [] }
        evm (bytesStoreSetChunkByteHeaderRef I) = .revert := by
    simpa [bytesStoreConfig] using hlen
  let headerRef : EvaledStorageRef :=
    { base := "chunks"
      steps := [.aindex
        (.int ((bytesStoreSetChunkByteChunkIndexWord I).toNat : Int))] }
  have hlenHeader :
      readStorageBytesLength?
        { storage := bytesStoreStorageLayout, externalABI := defaultExternalCallABI,
          selfDeployment := genSolidityConstructorDeployment [] }
        evm headerRef = .revert := by
    simpa [headerRef, bytesStoreSetChunkByteHeaderRef] using hlen'
  simp only [headerRef, bytesStoreStorageLayout, solidityStorageLayout] at hlenHeader
  have hstep :
      evalStorageRefStep bytesStoreConfig (bytesStoreSetChunkByteFrame I) evm
        "chunks" [] (.aindex (.var "chunkIndex")) =
        .ok (.aindex (.int (Int.ofNat (bytesStoreSetChunkByteChunkIndexWord I).toNat))) := by
    simp [evalStorageRefStep, evalExpr?, bytesStoreSetChunkByteFrame,
      hgetChunkIndexElem, valueToKey?, EvalResult.ofOption, EvalResult.bind, bind, pure,
      arrayIndexInBounds?, storageTypeAt?, bytesStoreConfig, bytesStoreContract,
      storageDecls, bytesSt, bytesStoreStorageLayout, solidityStorageLayout,
      bytesStoreLayout, bytesStoreStorageLocLoad_uint256, hload, hchunkBound]
  have hbounds :
      arrayIndexInBounds? bytesStoreConfig evm
        (bytesStoreSetChunkByteFrame I).contract.storage "chunks"
        [.aindex (.int (Int.ofNat (bytesStoreSetChunkByteChunkIndexWord I).toNat))]
        (.int (Int.ofNat (bytesStoreSetChunkByteIndexWord I).toNat)) = .revert := by
    simp [arrayIndexInBounds?, storageTypeAt?, bytesStoreConfig, bytesStoreSetChunkByteFrame,
      bytesStoreContract, storageDecls, storageTypeStep?, bytesSt, bytesStoreStorageLayout,
      solidityStorageLayout, hlenHeader]
  simpa [chunkByteRef] using
    (evalStorageRef_step_aindex_var_of_get?_revert
      (cfg := bytesStoreConfig) (solm := bytesStoreSetChunkByteFrame I) (evm := evm)
      (base := "chunks") (name := "byteIndex") (step := .aindex (.var "chunkIndex"))
      (estep := .aindex (.int (Int.ofNat (bytesStoreSetChunkByteChunkIndexWord I).toNat)))
      hstep hgetByteIndex hindexKey hbounds)

theorem bytesStoreSetChunkByteEvalStorageRefRevertsOfChunksLength {evm : EVM.State}
    {I : ExecutionEnv} {chunksLen : UInt256}
    (hload :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩ = chunksLen)
    (hbound :
      ¬ (bytesStoreSetChunkByteChunkIndexWord I).toNat < chunksLen.toNat) :
    evalStorageRef bytesStoreConfig
      (bytesStoreSetChunkByteFrame I)
      evm (chunkByteRef (.var "chunkIndex") (.var "byteIndex")) = .revert := by
  have hgetIndexElem :
      (bytesStoreSetChunkByteLocals I)["chunkIndex"]? =
        some (.int (Int.ofNat (bytesStoreSetChunkByteChunkIndexWord I).toNat)) :=
    bytesStoreSetChunkByteLocals_getElem_chunkIndex I
  have hstep :
      evalStorageRefStep bytesStoreConfig (bytesStoreSetChunkByteFrame I) evm
        "chunks" [] (.aindex (.var "chunkIndex")) = .revert := by
    simp [evalStorageRefStep, evalExpr?, bytesStoreSetChunkByteFrame, hgetIndexElem,
      valueToKey?, EvalResult.ofOption, EvalResult.bind, bind, pure, arrayIndexInBounds?,
      storageTypeAt?, bytesStoreConfig, bytesStoreContract, storageDecls, bytesSt,
      bytesStoreStorageLayout, solidityStorageLayout, bytesStoreLayout,
      bytesStoreStorageLocLoad_uint256, hload, hbound]
  simpa [chunkByteRef] using
    (evalStorageRef_step_revert
      (cfg := bytesStoreConfig) (solm := bytesStoreSetChunkByteFrame I) (evm := evm)
      (base := "chunks") (step := .aindex (.var "chunkIndex"))
      (rest := [.aindex (.var "byteIndex")]) hstep)

theorem bytesStoreSetChunkByteBodyReturns {evm evm' : EVM.State} {I : ExecutionEnv}
    {ret : Value}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hassign :
      assignStorageRef? bytesStoreConfig
        (bytesStoreSetChunkByteFrame I)
        evm .storage (chunkByteRef (.var "chunkIndex") (.var "byteIndex"))
          (bytesStoreSetChunkByteValue I) =
          .ok (bytesStoreSetChunkByteFrame I, evm'))
    (hret :
      evalExpr? bytesStoreConfig
        (bytesStoreSetChunkByteFrame I)
        evm' (.storage (chunkByteRef (.var "chunkIndex") (.var "byteIndex"))) = .ok ret) :
    ExecTransitionBody bytesStoreConfig bytesStoreContract evm
      (bytesStoreSetChunkByteLocals I) setChunkByteTransition.body
      (.returned
        (bytesStoreSetChunkByteFrame I)
        evm' (some ret)) := by
  let solm : Frame := bytesStoreSetChunkByteFrame I
  have hvalue :
      evalExpr? bytesStoreConfig solm evm (.var "value") =
        .ok (bytesStoreSetChunkByteValue I) := by
    exact evalExpr_var_of_get? (by
      simp [solm, bytesStoreSetChunkByteFrame, bytesStoreSetChunkByteValue,
        bytesStoreSetChunkByteLocals])
  have hassign :
      assignStorageRef? bytesStoreConfig solm evm .storage
        (chunkByteRef (.var "chunkIndex") (.var "byteIndex"))
          (bytesStoreSetChunkByteValue I) =
          .ok (solm, evm') := by
    simpa [solm] using hassign
  have hret :
      evalExpr? bytesStoreConfig solm evm'
        (.storage (chunkByteRef (.var "chunkIndex") (.var "byteIndex"))) = .ok ret := by
    simpa [solm] using hret
  exact ExecFuncBody.execBlockRet <|
    ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consNormal (ExecStmt.assign hvalue hassign) <|
        ExecBlock.consReturn (ExecStmt.return hret)

theorem bytesStoreSetChunkByteBodyReturnReverts {evm evm' : EVM.State} {I : ExecutionEnv}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hassign :
      assignStorageRef? bytesStoreConfig
        (bytesStoreSetChunkByteFrame I)
        evm .storage (chunkByteRef (.var "chunkIndex") (.var "byteIndex"))
          (bytesStoreSetChunkByteValue I) =
          .ok (bytesStoreSetChunkByteFrame I, evm'))
    (hret :
      evalExpr? bytesStoreConfig
        (bytesStoreSetChunkByteFrame I)
        evm' (.storage (chunkByteRef (.var "chunkIndex") (.var "byteIndex"))) = .revert) :
    ExecTransitionBody bytesStoreConfig bytesStoreContract evm
      (bytesStoreSetChunkByteLocals I) setChunkByteTransition.body .reverted := by
  let solm : Frame := bytesStoreSetChunkByteFrame I
  have hvalue :
      evalExpr? bytesStoreConfig solm evm (.var "value") =
        .ok (bytesStoreSetChunkByteValue I) := by
    exact evalExpr_var_of_get? (by
      simp [solm, bytesStoreSetChunkByteFrame, bytesStoreSetChunkByteValue,
        bytesStoreSetChunkByteLocals])
  have hassign :
      assignStorageRef? bytesStoreConfig solm evm .storage
        (chunkByteRef (.var "chunkIndex") (.var "byteIndex"))
          (bytesStoreSetChunkByteValue I) =
          .ok (solm, evm') := by
    simpa [solm] using hassign
  have hret :
      evalExpr? bytesStoreConfig solm evm'
        (.storage (chunkByteRef (.var "chunkIndex") (.var "byteIndex"))) = .revert := by
    simpa [solm] using hret
  exact ExecFuncBody.execBlockRevert <|
    ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consNormal (ExecStmt.assign hvalue hassign) <|
        ExecBlock.consRevert (ExecStmt.returnRevert hret)

theorem bytesStoreSetChunkByteResolveOfLength {evm : EVM.State} {I : ExecutionEnv}
    {chunksLen : UInt256} {len : Nat}
    (hload :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩ = chunksLen)
    (hchunkBound :
      (bytesStoreSetChunkByteChunkIndexWord I).toNat < chunksLen.toNat)
    (hlen : readStorageBytesLength? bytesStoreConfig evm
      (bytesStoreSetChunkByteHeaderRef I) = .ok len)
    (hbound : (bytesStoreSetChunkByteIndexWord I).toNat < len) :
    resolveStorageRef? bytesStoreConfig
      (bytesStoreSetChunkByteFrame I)
      evm (chunkByteRef (.var "chunkIndex") (.var "byteIndex")) =
        .ok (bytesStoreSetChunkByteRef I, uint8St) := by
  have hgetChunks :
      (bytesStoreSetChunkByteLocals I).get? "chunks" = none :=
    bytesStoreSetChunkByteLocals_get_chunks_none I
  let sourceRef : StorageRef :=
    { base := "chunks"
      steps := [.aindex (.var "chunkIndex"), .aindex (.var "byteIndex")] }
  have herInline' :
      evalStorageRef bytesStoreConfig
        ({ contract := bytesStoreContract, locals := bytesStoreSetChunkByteLocals I } :
          Frame)
        evm sourceRef =
          .ok (bytesStoreSetChunkByteRef I) := by
    simpa [sourceRef, chunkByteRef, bytesStoreSetChunkByteFrame] using
      (bytesStoreSetChunkByteEvalStorageRefOfLength
        (evm := evm) (I := I) (chunksLen := chunksLen) (len := len)
        hload hchunkBound hlen hbound)
  exact resolveStorageRef?_ok hgetChunks herInline'
    bytesStoreSetChunkByte_storageTypeAt

theorem bytesStoreSetChunkByteAssignOfLength {evm evm' : EVM.State}
    {I : ExecutionEnv} {chunksLen : UInt256} {len : Nat}
    (hload :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩ = chunksLen)
    (hchunkBound :
      (bytesStoreSetChunkByteChunkIndexWord I).toNat < chunksLen.toNat)
    (hlen : readStorageBytesLength? bytesStoreConfig evm
      (bytesStoreSetChunkByteHeaderRef I) = .ok len)
    (hbound : (bytesStoreSetChunkByteIndexWord I).toNat < len)
    (hstore :
      (match bytesStoreConfig.storage.layout (bytesStoreSetChunkByteRef I) evm with
      | some loc => storageLocStore evm loc (bytesStoreSetChunkByteValue I)
      | none => none) = some evm') :
    assignStorageRef? bytesStoreConfig
      (bytesStoreSetChunkByteFrame I)
      evm .storage (chunkByteRef (.var "chunkIndex") (.var "byteIndex"))
        (bytesStoreSetChunkByteValue I) =
        .ok (bytesStoreSetChunkByteFrame I, evm') := by
  exact assignStorageRef_storage_scalar_ok_of_resolve_match_store
    (bytesStoreSetChunkByteResolveOfLength (I := I) hload hchunkBound hlen hbound)
    hstore
    (by simp [bytesStoreSetChunkByteValue])

theorem bytesStoreSetChunkByteShortBodyReturns_of_post_readback
    {evm : EVM.State} {σ : AccountMap} {I : ExecutionEnv}
    {chunksLen chunksLenPost len : UInt256} {acc : Account}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hloadChunks : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩ = chunksLen)
    (hchunkBound : (bytesStoreSetChunkByteChunkIndexWord I).toNat < chunksLen.toNat)
    (hloadChunksPost :
      Solm.EVM.storageLoad
          (Solm.EVM.storageStore evm evm.executionEnv.codeOwner
            (bytesStoreSetChunkByteSlot I)
            (bytesStoreSetChunkByteShortStoredWord σ I))
          evm.executionEnv.codeOwner ⟨1⟩ = chunksLenPost)
    (hchunkBoundPost :
      (bytesStoreSetChunkByteChunkIndexWord I).toNat < chunksLenPost.toNat)
    (hloadHeader : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (bytesStoreSetChunkByteSlot I) = bytesStoreSetChunkByteHeaderWord σ I)
    (hacc : evm.accountMap.find? evm.executionEnv.codeOwner = some acc)
    (hcanon : (bytesStoreSetChunkByteValueWord I).toNat < EVM.twoPow 8)
    (hlen : len =
      UInt256.land (UInt256.div (bytesStoreSetChunkByteHeaderWord σ I) ⟨2⟩) ⟨127⟩)
    (hshort : len.toNat < 32)
    (hbound : (bytesStoreSetChunkByteIndexWord I).toNat < len.toNat)
    (hflag : UInt256.land (bytesStoreSetChunkByteHeaderWord σ I) ⟨1⟩ = ⟨0⟩)
    (_hvalid : UInt256.sub (UInt256.land (bytesStoreSetChunkByteHeaderWord σ I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStoreSetChunkByteHeaderWord σ I) ⟨2⟩) ⟨127⟩)
          ⟨32⟩) ≠ ⟨0⟩) :
    ExecTransitionBody bytesStoreConfig bytesStoreContract evm
      (bytesStoreSetChunkByteLocals I) setChunkByteTransition.body
      (.returned
        (bytesStoreSetChunkByteFrame I)
        (Solm.EVM.storageStore evm evm.executionEnv.codeOwner
          (bytesStoreSetChunkByteSlot I)
          (bytesStoreSetChunkByteShortStoredWord σ I))
        (some (bytesStoreSetChunkByteValue I))) := by
  let evm' := Solm.EVM.storageStore evm evm.executionEnv.codeOwner
    (bytesStoreSetChunkByteSlot I)
    (bytesStoreSetChunkByteShortStoredWord σ I)
  have hlenRead :
      readStorageBytesLength? bytesStoreConfig evm
          (bytesStoreSetChunkByteHeaderRef I) =
        .ok len.toNat := by
    have hltLen : UInt256.lt len ⟨32⟩ = ⟨1⟩ := by
      exact ult_one (by
        simpa [show (⟨32⟩ : UInt256).toNat = 32 from by decide] using hshort)
    have hvalidLen : UInt256.sub ⟨0⟩ (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩ := by
      rw [hltLen]
      native_decide
    exact bytesStoreReadLengthOfHeaderLoad
      (er := bytesStoreSetChunkByteHeaderRef I) (evm := evm)
      (baseSlot := bytesStoreSetChunkByteSlot I)
      (header := bytesStoreSetChunkByteHeaderWord σ I) (len := len.toNat)
      (bytesStoreSetChunkByteHeaderRef_length_slot evm I)
      hloadHeader
      (solidityDecodeBytesLengthHeader_short_valid hflag hlen (by simpa [hflag] using hvalidLen))
  have hpacked : checkBytesPacked (bytesStoreSetChunkByteSlot I) evm = true :=
    checkBytesPacked_of_storageLoad_land_one_zero hloadHeader hflag
  have hidx31 : (bytesStoreSetChunkByteIndexWord I).toNat < 31 :=
    bytesStoreSetChunkByteIndex_lt31_of_short_bound (I := I) (len := len)
      hshort hbound
  have hlayout :
      bytesStoreConfig.storage.layout (bytesStoreSetChunkByteRef I) evm =
        some (uint8Loc (bytesStoreSetChunkByteSlot I)
          ⟨31 - (bytesStoreSetChunkByteIndexWord I).toNat, by omega⟩) :=
    bytesStoreSetChunkByteLayoutShort (evm := evm) (I := I) hpacked hidx31
  have hstore :
      (match bytesStoreConfig.storage.layout (bytesStoreSetChunkByteRef I) evm with
      | some loc => storageLocStore evm loc (bytesStoreSetChunkByteValue I)
      | none => none) = some evm' := by
    rw [hlayout]
    simpa [evm'] using
      bytesStoreSetChunkByteStorageLocStoreShort
        (evm := evm) (σ := σ) (I := I) (len := len)
        hloadHeader hcanon hshort hbound
  have hassign :
      assignStorageRef? bytesStoreConfig
        (bytesStoreSetChunkByteFrame I)
        evm .storage (chunkByteRef (.var "chunkIndex") (.var "byteIndex"))
          (bytesStoreSetChunkByteValue I) =
          .ok (bytesStoreSetChunkByteFrame I, evm') :=
    bytesStoreSetChunkByteAssignOfLength (evm := evm) (evm' := evm') (I := I)
      hloadChunks hchunkBound hlenRead hbound hstore
  have hloadPost :
      Solm.EVM.storageLoad evm' evm'.executionEnv.codeOwner
          (bytesStoreSetChunkByteSlot I) =
        bytesStoreSetChunkByteShortStoredWord σ I := by
    simpa [evm'] using
      storageLoad_storageStore_codeOwner_same_present evm hacc
        (bytesStoreSetChunkByteSlot I)
        (bytesStoreSetChunkByteShortStoredWord σ I)
  have hloadChunksPost' :
      Solm.EVM.storageLoad evm' evm'.executionEnv.codeOwner ⟨1⟩ = chunksLenPost := by
    simpa [evm', storageStore_executionEnv] using hloadChunksPost
  have hflagPost :
      UInt256.land (bytesStoreSetChunkByteShortStoredWord σ I) ⟨1⟩ = ⟨0⟩ := by
    rw [bytesStoreSetChunkByteShortStoredWord_flag_eq
      (σ := σ) (I := I) (len := len) hshort hbound, hflag]
  have hlenPost :
      readStorageBytesLength? bytesStoreConfig evm'
          (bytesStoreSetChunkByteHeaderRef I) =
        .ok len.toNat := by
    have hltLen : UInt256.lt len ⟨32⟩ = ⟨1⟩ := by
      exact ult_one (by
        simpa [show (⟨32⟩ : UInt256).toNat = 32 from by decide] using hshort)
    have hvalidLen : UInt256.sub ⟨0⟩ (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩ := by
      rw [hltLen]
      native_decide
    have hlenPostWord :
        UInt256.land
            (UInt256.div (bytesStoreSetChunkByteShortStoredWord σ I) ⟨2⟩) ⟨127⟩ =
          len := by
      rw [bytesStoreSetChunkByteShortStoredWord_shortLen_eq
        (σ := σ) (I := I) (len := len) hshort hbound]
      exact hlen.symm
    exact bytesStoreReadLengthOfHeaderLoad
      (er := bytesStoreSetChunkByteHeaderRef I) (evm := evm')
      (baseSlot := bytesStoreSetChunkByteSlot I)
      (header := bytesStoreSetChunkByteShortStoredWord σ I) (len := len.toNat)
      (bytesStoreSetChunkByteHeaderRef_length_slot evm' I)
      hloadPost
      (solidityDecodeBytesLengthHeader_short_valid hflagPost hlenPostWord.symm (by
        simpa [hflagPost] using hvalidLen))
  have hpackedPost : checkBytesPacked (bytesStoreSetChunkByteSlot I) evm' = true :=
    checkBytesPacked_of_storageLoad_land_one_zero hloadPost hflagPost
  have hlayoutPost :
      bytesStoreConfig.storage.layout (bytesStoreSetChunkByteRef I) evm' =
        some (uint8Loc (bytesStoreSetChunkByteSlot I)
          ⟨31 - (bytesStoreSetChunkByteIndexWord I).toNat, by omega⟩) :=
    bytesStoreSetChunkByteLayoutShort (evm := evm') (I := I) hpackedPost hidx31
  have hidxLe : (bytesStoreSetChunkByteIndexWord I).toNat ≤ 31 := by
    omega
  have hret :
      evalExpr? bytesStoreConfig
        (bytesStoreSetChunkByteFrame I)
        evm' (.storage (chunkByteRef (.var "chunkIndex") (.var "byteIndex"))) =
          .ok (bytesStoreSetChunkByteValue I) := by
    rw [evalExpr_storage_scalar_of_resolve_layout
      (bytesStoreSetChunkByteResolveOfLength
        (evm := evm') (I := I) (chunksLen := chunksLenPost) (len := len.toNat)
        hloadChunksPost' hchunkBoundPost hlenPost hbound)
      hlayoutPost]
    rw [storageLocLoad_uint8Loc_byteAt
      (slot := bytesStoreSetChunkByteSlot I)
      (idx := bytesStoreSetChunkByteIndexWord I)
      (off := ⟨31 - (bytesStoreSetChunkByteIndexWord I).toNat, by omega⟩)
      (hoff := by rfl) (hidx := hidxLe)]
    rw [hloadPost]
    rw [bytesStoreSetChunkByteShortStoredWord_byteAt
      (σ := σ) (I := I) (len := len) hcanon hshort hbound]
    simp [bytesStoreSetChunkByteValue]
  simpa [evm'] using
    bytesStoreSetChunkByteBodyReturns (evm := evm) (evm' := evm') (I := I)
      hwv hassign hret

theorem bytesStoreSetChunkByteLongBodyReturns_of_post_readback
    {evm : EVM.State} {σ : AccountMap} {I : ExecutionEnv}
    {chunksLen chunksLenPost len lenPost postHeaderWord : UInt256} {acc : Account}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hloadChunks : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩ = chunksLen)
    (hchunkBound : (bytesStoreSetChunkByteChunkIndexWord I).toNat < chunksLen.toNat)
    (hloadChunksPost :
      Solm.EVM.storageLoad
          (Solm.EVM.storageStore evm evm.executionEnv.codeOwner
            (bytesStoreSetChunkByteLongDataSlot I)
            (bytesStoreSetChunkByteLongStoredWord σ I))
          evm.executionEnv.codeOwner ⟨1⟩ = chunksLenPost)
    (hchunkBoundPost :
      (bytesStoreSetChunkByteChunkIndexWord I).toNat < chunksLenPost.toNat)
    (hloadHeader : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (bytesStoreSetChunkByteSlot I) = bytesStoreSetChunkByteHeaderWord σ I)
    (hloadData : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (bytesStoreSetChunkByteLongDataSlot I) =
      bytesStoreSetChunkByteLongOldWord σ I)
    (hloadHeaderPost :
      Solm.EVM.storageLoad
          (Solm.EVM.storageStore evm evm.executionEnv.codeOwner
            (bytesStoreSetChunkByteLongDataSlot I)
            (bytesStoreSetChunkByteLongStoredWord σ I))
          evm.executionEnv.codeOwner (bytesStoreSetChunkByteSlot I) =
        postHeaderWord)
    (hacc : evm.accountMap.find? evm.executionEnv.codeOwner = some acc)
    (hcanon : (bytesStoreSetChunkByteValueWord I).toNat < EVM.twoPow 8)
    (hlen : len = UInt256.div (bytesStoreSetChunkByteHeaderWord σ I) ⟨2⟩)
    (hlenPost : lenPost = UInt256.div postHeaderWord ⟨2⟩)
    (hbound : (bytesStoreSetChunkByteIndexWord I).toNat < len.toNat)
    (hboundPost : (bytesStoreSetChunkByteIndexWord I).toNat < lenPost.toNat)
    (hflag : UInt256.land (bytesStoreSetChunkByteHeaderWord σ I) ⟨1⟩ ≠ ⟨0⟩)
    (hflagPost : UInt256.land postHeaderWord ⟨1⟩ ≠ ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (bytesStoreSetChunkByteHeaderWord σ I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStoreSetChunkByteHeaderWord σ I) ⟨2⟩) ⟨32⟩) ≠
          ⟨0⟩)
    (hvalidPost : UInt256.sub (UInt256.land postHeaderWord ⟨1⟩)
        (UInt256.lt (UInt256.div postHeaderWord ⟨2⟩) ⟨32⟩) ≠ ⟨0⟩) :
    ExecTransitionBody bytesStoreConfig bytesStoreContract evm
      (bytesStoreSetChunkByteLocals I) setChunkByteTransition.body
      (.returned
        (bytesStoreSetChunkByteFrame I)
        (Solm.EVM.storageStore evm evm.executionEnv.codeOwner
          (bytesStoreSetChunkByteLongDataSlot I)
          (bytesStoreSetChunkByteLongStoredWord σ I))
        (some (bytesStoreSetChunkByteValue I))) := by
  let evm' := Solm.EVM.storageStore evm evm.executionEnv.codeOwner
    (bytesStoreSetChunkByteLongDataSlot I)
    (bytesStoreSetChunkByteLongStoredWord σ I)
  have hvalidLen :
      UInt256.sub (UInt256.land (bytesStoreSetChunkByteHeaderWord σ I) ⟨1⟩)
        (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩ := by
    simpa [hlen] using hvalid
  have hlenRead :
      readStorageBytesLength? bytesStoreConfig evm
          (bytesStoreSetChunkByteHeaderRef I) =
        .ok len.toNat := by
    exact bytesStoreReadLengthOfHeaderLoad
      (er := bytesStoreSetChunkByteHeaderRef I) (evm := evm)
      (baseSlot := bytesStoreSetChunkByteSlot I)
      (header := bytesStoreSetChunkByteHeaderWord σ I) (len := len.toNat)
      (bytesStoreSetChunkByteHeaderRef_length_slot evm I)
      hloadHeader
      (solidityDecodeBytesLengthHeader_long_valid hflag hlen hvalidLen)
  have hpacked : checkBytesPacked (bytesStoreSetChunkByteSlot I) evm = false :=
    checkBytesPacked_of_storageLoad_land_one_ne_zero hloadHeader hflag
  have hlayout :
      bytesStoreConfig.storage.layout (bytesStoreSetChunkByteRef I) evm =
        some (uint8Loc (bytesStoreSetChunkByteLongDataSlot I)
          ⟨31 - (bytesStoreSetChunkByteLongWordIndex I).toNat, by
            have hidx := bytesStoreSetChunkByteLongWordIndex_lt32 I
            omega⟩) :=
    bytesStoreSetChunkByteLayoutLong (evm := evm) (I := I) hpacked
  have hstore :
      (match bytesStoreConfig.storage.layout (bytesStoreSetChunkByteRef I) evm with
      | some loc => storageLocStore evm loc (bytesStoreSetChunkByteValue I)
      | none => none) = some evm' := by
    rw [hlayout]
    simpa [evm'] using
      bytesStoreSetChunkByteStorageLocStoreLong
        (evm := evm) (σ := σ) (I := I) hloadData hcanon
  have hassign :
      assignStorageRef? bytesStoreConfig
        (bytesStoreSetChunkByteFrame I)
        evm .storage (chunkByteRef (.var "chunkIndex") (.var "byteIndex"))
          (bytesStoreSetChunkByteValue I) =
          .ok (bytesStoreSetChunkByteFrame I, evm') :=
    bytesStoreSetChunkByteAssignOfLength (evm := evm) (evm' := evm') (I := I)
      hloadChunks hchunkBound hlenRead hbound hstore
  have hloadHeaderPost' :
      Solm.EVM.storageLoad evm' evm'.executionEnv.codeOwner
          (bytesStoreSetChunkByteSlot I) =
        postHeaderWord := by
    simpa [evm', storageStore_executionEnv] using hloadHeaderPost
  have hloadChunksPost' :
      Solm.EVM.storageLoad evm' evm'.executionEnv.codeOwner ⟨1⟩ = chunksLenPost := by
    simpa [evm', storageStore_executionEnv] using hloadChunksPost
  have hlenPost :
      readStorageBytesLength? bytesStoreConfig evm'
          (bytesStoreSetChunkByteHeaderRef I) =
        .ok lenPost.toNat := by
    have hvalidLenPost :
        UInt256.sub (UInt256.land postHeaderWord ⟨1⟩) (UInt256.lt lenPost ⟨32⟩) ≠
          ⟨0⟩ := by
      simpa [hlenPost] using hvalidPost
    exact bytesStoreReadLengthOfHeaderLoad
      (er := bytesStoreSetChunkByteHeaderRef I) (evm := evm')
      (baseSlot := bytesStoreSetChunkByteSlot I)
      (header := postHeaderWord) (len := lenPost.toNat)
      (bytesStoreSetChunkByteHeaderRef_length_slot evm' I)
      hloadHeaderPost'
      (solidityDecodeBytesLengthHeader_long_valid hflagPost hlenPost hvalidLenPost)
  have hpackedPost : checkBytesPacked (bytesStoreSetChunkByteSlot I) evm' = false :=
    checkBytesPacked_of_storageLoad_land_one_ne_zero hloadHeaderPost' hflagPost
  have hlayoutPost :
      bytesStoreConfig.storage.layout (bytesStoreSetChunkByteRef I) evm' =
        some (uint8Loc (bytesStoreSetChunkByteLongDataSlot I)
          ⟨31 - (bytesStoreSetChunkByteLongWordIndex I).toNat, by
            have hidx := bytesStoreSetChunkByteLongWordIndex_lt32 I
            omega⟩) :=
    bytesStoreSetChunkByteLayoutLong (evm := evm') (I := I) hpackedPost
  have hloadDataPost :
      Solm.EVM.storageLoad evm' evm'.executionEnv.codeOwner
          (bytesStoreSetChunkByteLongDataSlot I) =
        bytesStoreSetChunkByteLongStoredWord σ I := by
    simpa [evm'] using
      storageLoad_storageStore_codeOwner_same_present evm hacc
        (bytesStoreSetChunkByteLongDataSlot I)
        (bytesStoreSetChunkByteLongStoredWord σ I)
  have hret :
      evalExpr? bytesStoreConfig
        (bytesStoreSetChunkByteFrame I)
        evm' (.storage (chunkByteRef (.var "chunkIndex") (.var "byteIndex"))) =
          .ok (bytesStoreSetChunkByteValue I) := by
    rw [evalExpr_storage_scalar_of_resolve_layout
      (bytesStoreSetChunkByteResolveOfLength
        (evm := evm') (I := I) (chunksLen := chunksLenPost) (len := lenPost.toNat)
        hloadChunksPost' hchunkBoundPost hlenPost hboundPost)
      hlayoutPost]
    rw [storageLocLoad_uint8Loc_byteAt
      (evm := evm') (slot := bytesStoreSetChunkByteLongDataSlot I)
      (idx := bytesStoreSetChunkByteLongWordIndex I)
      (off := ⟨31 - (bytesStoreSetChunkByteLongWordIndex I).toNat, by
        have hidx := bytesStoreSetChunkByteLongWordIndex_lt32 I
        omega⟩)
      (by rfl)
      (by
        have hidx := bytesStoreSetChunkByteLongWordIndex_lt32 I
        omega)]
    rw [hloadDataPost]
    rw [bytesStoreSetChunkByteLongStoredWord_byteAt (σ := σ) (I := I) hcanon]
    simp [bytesStoreSetChunkByteValue]
  simpa [evm'] using
    bytesStoreSetChunkByteBodyReturns (evm := evm) (evm' := evm') (I := I)
      hwv hassign hret

theorem bytesStoreSetChunkByteLongBodyReturnsOfPostShortReadback
    {evm : EVM.State} {σ : AccountMap} {I : ExecutionEnv}
    {chunksLen chunksLenPost len lenPost postHeaderWord : UInt256} {acc : Account}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hloadChunks : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩ = chunksLen)
    (hchunkBound : (bytesStoreSetChunkByteChunkIndexWord I).toNat < chunksLen.toNat)
    (hloadChunksPost :
      Solm.EVM.storageLoad
          (Solm.EVM.storageStore evm evm.executionEnv.codeOwner
            (bytesStoreSetChunkByteLongDataSlot I)
            (bytesStoreSetChunkByteLongStoredWord σ I))
          evm.executionEnv.codeOwner ⟨1⟩ = chunksLenPost)
    (hchunkBoundPost :
      (bytesStoreSetChunkByteChunkIndexWord I).toNat < chunksLenPost.toNat)
    (hloadHeader : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (bytesStoreSetChunkByteSlot I) = bytesStoreSetChunkByteHeaderWord σ I)
    (hloadData : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (bytesStoreSetChunkByteLongDataSlot I) =
      bytesStoreSetChunkByteLongOldWord σ I)
    (hloadHeaderPost :
      Solm.EVM.storageLoad
          (Solm.EVM.storageStore evm evm.executionEnv.codeOwner
            (bytesStoreSetChunkByteLongDataSlot I)
            (bytesStoreSetChunkByteLongStoredWord σ I))
          evm.executionEnv.codeOwner (bytesStoreSetChunkByteSlot I) =
        postHeaderWord)
    (hacc : evm.accountMap.find? evm.executionEnv.codeOwner = some acc)
    (hcanon : (bytesStoreSetChunkByteValueWord I).toNat < EVM.twoPow 8)
    (hlen : len = UInt256.div (bytesStoreSetChunkByteHeaderWord σ I) ⟨2⟩)
    (hlenPost : lenPost = UInt256.land (UInt256.div postHeaderWord ⟨2⟩) ⟨127⟩)
    (hbound : (bytesStoreSetChunkByteIndexWord I).toNat < len.toNat)
    (hboundPost : (bytesStoreSetChunkByteIndexWord I).toNat < lenPost.toNat)
    (hflag : UInt256.land (bytesStoreSetChunkByteHeaderWord σ I) ⟨1⟩ ≠ ⟨0⟩)
    (hflagPost : UInt256.land postHeaderWord ⟨1⟩ = ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (bytesStoreSetChunkByteHeaderWord σ I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStoreSetChunkByteHeaderWord σ I) ⟨2⟩) ⟨32⟩) ≠
          ⟨0⟩)
    (hvalidPost : UInt256.sub (UInt256.land postHeaderWord ⟨1⟩)
        (UInt256.lt (UInt256.land (UInt256.div postHeaderWord ⟨2⟩) ⟨127⟩) ⟨32⟩) ≠
          ⟨0⟩) :
    ExecTransitionBody bytesStoreConfig bytesStoreContract evm
      (bytesStoreSetChunkByteLocals I) setChunkByteTransition.body
      (.returned
        (bytesStoreSetChunkByteFrame I)
        (Solm.EVM.storageStore evm evm.executionEnv.codeOwner
          (bytesStoreSetChunkByteLongDataSlot I)
          (bytesStoreSetChunkByteLongStoredWord σ I))
        (some (bytesStoreSetChunkByteValue I))) := by
  let evm' := Solm.EVM.storageStore evm evm.executionEnv.codeOwner
    (bytesStoreSetChunkByteLongDataSlot I)
    (bytesStoreSetChunkByteLongStoredWord σ I)
  have hvalidLen :
      UInt256.sub (UInt256.land (bytesStoreSetChunkByteHeaderWord σ I) ⟨1⟩)
        (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩ := by
    simpa [hlen] using hvalid
  have hlenRead :
      readStorageBytesLength? bytesStoreConfig evm
          (bytesStoreSetChunkByteHeaderRef I) =
        .ok len.toNat := by
    exact bytesStoreReadLengthOfHeaderLoad
      (er := bytesStoreSetChunkByteHeaderRef I) (evm := evm)
      (baseSlot := bytesStoreSetChunkByteSlot I)
      (header := bytesStoreSetChunkByteHeaderWord σ I) (len := len.toNat)
      (bytesStoreSetChunkByteHeaderRef_length_slot evm I)
      hloadHeader
      (solidityDecodeBytesLengthHeader_long_valid hflag hlen hvalidLen)
  have hpacked : checkBytesPacked (bytesStoreSetChunkByteSlot I) evm = false :=
    checkBytesPacked_of_storageLoad_land_one_ne_zero hloadHeader hflag
  have hlayout :
      bytesStoreConfig.storage.layout (bytesStoreSetChunkByteRef I) evm =
        some (uint8Loc (bytesStoreSetChunkByteLongDataSlot I)
          ⟨31 - (bytesStoreSetChunkByteLongWordIndex I).toNat, by
            have hidx := bytesStoreSetChunkByteLongWordIndex_lt32 I
            omega⟩) :=
    bytesStoreSetChunkByteLayoutLong (evm := evm) (I := I) hpacked
  have hstore :
      (match bytesStoreConfig.storage.layout (bytesStoreSetChunkByteRef I) evm with
      | some loc => storageLocStore evm loc (bytesStoreSetChunkByteValue I)
      | none => none) = some evm' := by
    rw [hlayout]
    simpa [evm'] using
      bytesStoreSetChunkByteStorageLocStoreLong
        (evm := evm) (σ := σ) (I := I) hloadData hcanon
  have hassign :
      assignStorageRef? bytesStoreConfig
        (bytesStoreSetChunkByteFrame I)
        evm .storage (chunkByteRef (.var "chunkIndex") (.var "byteIndex"))
          (bytesStoreSetChunkByteValue I) =
          .ok (bytesStoreSetChunkByteFrame I, evm') :=
    bytesStoreSetChunkByteAssignOfLength (evm := evm) (evm' := evm') (I := I)
      hloadChunks hchunkBound hlenRead hbound hstore
  have hloadHeaderPost' :
      Solm.EVM.storageLoad evm' evm'.executionEnv.codeOwner
          (bytesStoreSetChunkByteSlot I) =
        postHeaderWord := by
    simpa [evm', storageStore_executionEnv] using hloadHeaderPost
  have hloadChunksPost' :
      Solm.EVM.storageLoad evm' evm'.executionEnv.codeOwner ⟨1⟩ = chunksLenPost := by
    simpa [evm', storageStore_executionEnv] using hloadChunksPost
  have hvalid0 :
      UInt256.sub ⟨0⟩ (UInt256.lt lenPost ⟨32⟩) ≠ ⟨0⟩ := by
    simpa [hflagPost, hlenPost] using hvalidPost
  have hshortPost : lenPost.toNat < 32 :=
    solidityShortBytesValid_lt32 hvalid0
  have hlenPostRead :
      readStorageBytesLength? bytesStoreConfig evm'
          (bytesStoreSetChunkByteHeaderRef I) =
        .ok lenPost.toNat := by
    exact bytesStoreReadLengthOfHeaderLoad
      (er := bytesStoreSetChunkByteHeaderRef I) (evm := evm')
      (baseSlot := bytesStoreSetChunkByteSlot I)
      (header := postHeaderWord) (len := lenPost.toNat)
      (bytesStoreSetChunkByteHeaderRef_length_slot evm' I)
      hloadHeaderPost'
      (solidityDecodeBytesLengthHeader_short_valid hflagPost hlenPost
        (by simpa [← hlenPost] using hvalidPost))
  have hpackedPost : checkBytesPacked (bytesStoreSetChunkByteSlot I) evm' = true :=
    checkBytesPacked_of_storageLoad_land_one_zero hloadHeaderPost' hflagPost
  have hidx31 : (bytesStoreSetChunkByteIndexWord I).toNat < 31 :=
    bytesStoreSetChunkByteIndex_lt31_of_short_bound (I := I) (len := lenPost)
      hshortPost hboundPost
  have hlayoutPost :
      bytesStoreConfig.storage.layout (bytesStoreSetChunkByteRef I) evm' =
        some (uint8Loc (bytesStoreSetChunkByteSlot I)
          ⟨31 - (bytesStoreSetChunkByteIndexWord I).toNat, by omega⟩) :=
    bytesStoreSetChunkByteLayoutShort (evm := evm') (I := I) hpackedPost hidx31
  have hheaderStored : postHeaderWord = bytesStoreSetChunkByteLongStoredWord σ I := by
    by_cases hEq : bytesStoreSetChunkByteSlot I =
        bytesStoreSetChunkByteLongDataSlot I
    · have hsame :
          Solm.EVM.storageLoad evm' evm'.executionEnv.codeOwner
              (bytesStoreSetChunkByteSlot I) =
            bytesStoreSetChunkByteLongStoredWord σ I := by
        simpa [evm', hEq] using
          storageLoad_storageStore_codeOwner_same_present evm hacc
            (bytesStoreSetChunkByteLongDataSlot I)
            (bytesStoreSetChunkByteLongStoredWord σ I)
      exact hloadHeaderPost'.symm.trans hsame
    · have hpostOld :
          Solm.EVM.storageLoad evm' evm'.executionEnv.codeOwner
              (bytesStoreSetChunkByteSlot I) =
            bytesStoreSetChunkByteHeaderWord σ I := by
        have hne :
            bytesStoreSetChunkByteSlot I ≠
              bytesLikeDataBase (bytesStoreSetChunkByteSlot I) +
                UInt256.div (bytesStoreSetChunkByteIndexWord I) ⟨32⟩ := by
          simpa [bytesStoreSetChunkByteLongDataSlot] using hEq
        have hpostOldOwner :
            Solm.EVM.storageLoad evm' evm.executionEnv.codeOwner
                (bytesStoreSetChunkByteSlot I) =
              Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
                (bytesStoreSetChunkByteSlot I) := by
          simpa [evm', bytesStoreSetChunkByteLongDataSlot] using
            bytesStoreStorageLoadBytesHeaderAfterDataStore_ne_of_ne
              (evm := evm) (baseSlot := bytesStoreSetChunkByteSlot I)
              (idx := bytesStoreSetChunkByteIndexWord I)
              (val := bytesStoreSetChunkByteLongStoredWord σ I) hne
        simpa [evm', storageStore_executionEnv, hloadHeader] using hpostOldOwner
      have hzeroOld :
          UInt256.land (bytesStoreSetChunkByteHeaderWord σ I) ⟨1⟩ = ⟨0⟩ := by
        have hpostWord :
            postHeaderWord = bytesStoreSetChunkByteHeaderWord σ I :=
          hloadHeaderPost'.symm.trans hpostOld
        simpa [hpostWord] using hflagPost
      exact False.elim (hflag hzeroOld)
  have hidxLe : (bytesStoreSetChunkByteIndexWord I).toNat ≤ 31 := by
    omega
  have hret :
      evalExpr? bytesStoreConfig
        (bytesStoreSetChunkByteFrame I)
        evm' (.storage (chunkByteRef (.var "chunkIndex") (.var "byteIndex"))) =
          .ok (bytesStoreSetChunkByteValue I) := by
    rw [evalExpr_storage_scalar_of_resolve_layout
      (bytesStoreSetChunkByteResolveOfLength
        (evm := evm') (I := I) (chunksLen := chunksLenPost) (len := lenPost.toNat)
        hloadChunksPost' hchunkBoundPost hlenPostRead hboundPost)
      hlayoutPost]
    rw [storageLocLoad_uint8Loc_byteAt
      (slot := bytesStoreSetChunkByteSlot I)
      (idx := bytesStoreSetChunkByteIndexWord I)
      (off := ⟨31 - (bytesStoreSetChunkByteIndexWord I).toNat, by omega⟩)
      (hoff := by rfl) (hidx := hidxLe)]
    rw [hloadHeaderPost']
    rw [hheaderStored]
    rw [bytesStoreSetChunkByteLongStoredWord_byteAt_index_of_lt32
      (σ := σ) (I := I) hcanon (by omega)]
    simp [bytesStoreSetChunkByteValue]
  simpa [evm'] using
    bytesStoreSetChunkByteBodyReturns (evm := evm) (evm' := evm') (I := I)
      hwv hassign hret

theorem bytesStoreSetChunkByteResolveRevertsOfLength {evm : EVM.State}
    {I : ExecutionEnv} {chunksLen : UInt256} {len : Nat}
    (hload :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩ = chunksLen)
    (hchunkBound :
      (bytesStoreSetChunkByteChunkIndexWord I).toNat < chunksLen.toNat)
    (hlen : readStorageBytesLength? bytesStoreConfig evm
      (bytesStoreSetChunkByteHeaderRef I) = .ok len)
    (hbound : ¬ (bytesStoreSetChunkByteIndexWord I).toNat < len) :
    resolveStorageRef? bytesStoreConfig
      (bytesStoreSetChunkByteFrame I) evm
      (chunkByteRef (.var "chunkIndex") (.var "byteIndex")) = .revert := by
  have hgetChunks :
      (bytesStoreSetChunkByteLocals I).get? "chunks" = none :=
    bytesStoreSetChunkByteLocals_get_chunks_none I
  have herInline :
      evalStorageRef bytesStoreConfig
        { contract := bytesStoreContract, locals := bytesStoreSetChunkByteLocals I }
        evm (chunkByteRef (.var "chunkIndex") (.var "byteIndex")) = .revert := by
    simpa [bytesStoreSetChunkByteFrame] using
      (bytesStoreSetChunkByteEvalStorageRefRevertsOfLength
        (evm := evm) (I := I) (chunksLen := chunksLen) (len := len)
        hload hchunkBound hlen hbound)
  exact resolveStorageRef?_revert_of_evalStorageRef_revert hgetChunks herInline

theorem bytesStoreSetChunkByteBodyBoundsRevertsOfLength {evm : EVM.State}
    {I : ExecutionEnv} {chunksLen : UInt256} {len : Nat}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hload :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩ = chunksLen)
    (hchunkBound :
      (bytesStoreSetChunkByteChunkIndexWord I).toNat < chunksLen.toNat)
    (hlen : readStorageBytesLength? bytesStoreConfig evm
      (bytesStoreSetChunkByteHeaderRef I) = .ok len)
    (hbound : ¬ (bytesStoreSetChunkByteIndexWord I).toNat < len) :
    ExecTransitionBody bytesStoreConfig bytesStoreContract evm
      (bytesStoreSetChunkByteLocals I) setChunkByteTransition.body .reverted := by
  let solm : Frame := bytesStoreSetChunkByteFrame I
  have hvalue :
      evalExpr? bytesStoreConfig solm evm (.var "value") =
        .ok (bytesStoreSetChunkByteValue I) := by
    exact evalExpr_var_of_get? (by
      simp [solm, bytesStoreSetChunkByteFrame, bytesStoreSetChunkByteValue,
        bytesStoreSetChunkByteLocals])
  have hassign :
      assignStorageRef? bytesStoreConfig solm evm .storage
        (chunkByteRef (.var "chunkIndex") (.var "byteIndex"))
          (bytesStoreSetChunkByteValue I) = .revert := by
    exact assignStorageRef_storage_revert_of_resolve
      (bytesStoreSetChunkByteResolveRevertsOfLength
        (evm := evm) (I := I) (chunksLen := chunksLen) (len := len)
        hload hchunkBound hlen hbound)
  exact ExecFuncBody.execBlockRevert <|
    ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consRevert (ExecStmt.assignStoreRevert hvalue hassign)

theorem bytesStoreSetChunkByteResolveRevertsOfLengthRead {evm : EVM.State}
    {I : ExecutionEnv} {chunksLen : UInt256}
    (hload :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩ = chunksLen)
    (hchunkBound :
      (bytesStoreSetChunkByteChunkIndexWord I).toNat < chunksLen.toNat)
    (hlen : readStorageBytesLength? bytesStoreConfig evm
      (bytesStoreSetChunkByteHeaderRef I) = .revert) :
    resolveStorageRef? bytesStoreConfig
      (bytesStoreSetChunkByteFrame I) evm
      (chunkByteRef (.var "chunkIndex") (.var "byteIndex")) = .revert := by
  have hgetChunks :
      (bytesStoreSetChunkByteLocals I).get? "chunks" = none :=
    bytesStoreSetChunkByteLocals_get_chunks_none I
  have herInline :
      evalStorageRef bytesStoreConfig
        { contract := bytesStoreContract, locals := bytesStoreSetChunkByteLocals I }
        evm (chunkByteRef (.var "chunkIndex") (.var "byteIndex")) = .revert := by
    simpa [bytesStoreSetChunkByteFrame] using
      (bytesStoreSetChunkByteEvalStorageRefRevertsOfLengthRead
        (evm := evm) (I := I) (chunksLen := chunksLen)
        hload hchunkBound hlen)
  exact resolveStorageRef?_revert_of_evalStorageRef_revert hgetChunks herInline

theorem bytesStoreSetChunkByteBodyRevertsOfLengthRead {evm : EVM.State}
    {I : ExecutionEnv} {chunksLen : UInt256}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hload :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩ = chunksLen)
    (hchunkBound :
      (bytesStoreSetChunkByteChunkIndexWord I).toNat < chunksLen.toNat)
    (hlen : readStorageBytesLength? bytesStoreConfig evm
      (bytesStoreSetChunkByteHeaderRef I) = .revert) :
    ExecTransitionBody bytesStoreConfig bytesStoreContract evm
      (bytesStoreSetChunkByteLocals I) setChunkByteTransition.body .reverted := by
  let solm : Frame := bytesStoreSetChunkByteFrame I
  have hvalue :
      evalExpr? bytesStoreConfig solm evm (.var "value") =
        .ok (bytesStoreSetChunkByteValue I) := by
    exact evalExpr_var_of_get? (by
      simp [solm, bytesStoreSetChunkByteFrame, bytesStoreSetChunkByteValue,
        bytesStoreSetChunkByteLocals])
  have hassign :
      assignStorageRef? bytesStoreConfig solm evm .storage
        (chunkByteRef (.var "chunkIndex") (.var "byteIndex"))
          (bytesStoreSetChunkByteValue I) = .revert := by
    exact assignStorageRef_storage_revert_of_resolve
      (bytesStoreSetChunkByteResolveRevertsOfLengthRead
        (evm := evm) (I := I) (chunksLen := chunksLen) hload hchunkBound hlen)
  exact ExecFuncBody.execBlockRevert <|
    ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consRevert (ExecStmt.assignStoreRevert hvalue hassign)

theorem bytesStoreSetChunkByteResolveRevertsOfChunksLength {evm : EVM.State}
    {I : ExecutionEnv} {chunksLen : UInt256}
    (hload :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩ = chunksLen)
    (hbound :
      ¬ (bytesStoreSetChunkByteChunkIndexWord I).toNat < chunksLen.toNat) :
    resolveStorageRef? bytesStoreConfig
      (bytesStoreSetChunkByteFrame I) evm
      (chunkByteRef (.var "chunkIndex") (.var "byteIndex")) = .revert := by
  have hgetChunksGet :
      (bytesStoreSetChunkByteLocals I).get? "chunks" = none :=
    bytesStoreSetChunkByteLocals_get_chunks_none I
  have herInline :
      evalStorageRef bytesStoreConfig
        { contract := bytesStoreContract, locals := bytesStoreSetChunkByteLocals I }
        evm (chunkByteRef (.var "chunkIndex") (.var "byteIndex")) = .revert := by
    simpa [bytesStoreSetChunkByteFrame] using
      (bytesStoreSetChunkByteEvalStorageRefRevertsOfChunksLength
        (evm := evm) (I := I) (chunksLen := chunksLen) hload hbound)
  exact resolveStorageRef?_revert_of_evalStorageRef_revert hgetChunksGet herInline

theorem bytesStoreSetChunkByteBodyBoundsRevertsOfChunksLength {evm : EVM.State}
    {I : ExecutionEnv} {chunksLen : UInt256}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hload :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩ = chunksLen)
    (hbound :
      ¬ (bytesStoreSetChunkByteChunkIndexWord I).toNat < chunksLen.toNat) :
    ExecTransitionBody bytesStoreConfig bytesStoreContract evm
      (bytesStoreSetChunkByteLocals I) setChunkByteTransition.body .reverted := by
  let solm : Frame := bytesStoreSetChunkByteFrame I
  have hvalue :
      evalExpr? bytesStoreConfig solm evm (.var "value") =
        .ok (bytesStoreSetChunkByteValue I) := by
    exact evalExpr_var_of_get? (by
      simp [solm, bytesStoreSetChunkByteFrame, bytesStoreSetChunkByteValue,
        bytesStoreSetChunkByteLocals])
  have hassign :
      assignStorageRef? bytesStoreConfig solm evm .storage
        (chunkByteRef (.var "chunkIndex") (.var "byteIndex"))
          (bytesStoreSetChunkByteValue I) = .revert := by
    exact assignStorageRef_storage_revert_of_resolve
      (bytesStoreSetChunkByteResolveRevertsOfChunksLength
        (evm := evm) (I := I) (chunksLen := chunksLen) hload hbound)
  exact ExecFuncBody.execBlockRevert <|
    ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consRevert (ExecStmt.assignStoreRevert hvalue hassign)

theorem bytesStoreSetChunkByteBodyReturnRevertsOfPostChunksLength
    {evm evm' : EVM.State} {I : ExecutionEnv} {chunksLenPost : UInt256}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hassign :
      assignStorageRef? bytesStoreConfig
        (bytesStoreSetChunkByteFrame I)
        evm .storage (chunkByteRef (.var "chunkIndex") (.var "byteIndex"))
          (bytesStoreSetChunkByteValue I) =
          .ok (bytesStoreSetChunkByteFrame I, evm'))
    (hloadPost :
      Solm.EVM.storageLoad evm' evm'.executionEnv.codeOwner ⟨1⟩ = chunksLenPost)
    (hboundPost :
      ¬ (bytesStoreSetChunkByteChunkIndexWord I).toNat < chunksLenPost.toNat) :
    ExecTransitionBody bytesStoreConfig bytesStoreContract evm
      (bytesStoreSetChunkByteLocals I) setChunkByteTransition.body .reverted := by
  have hret :
      evalExpr? bytesStoreConfig
        (bytesStoreSetChunkByteFrame I)
        evm' (.storage (chunkByteRef (.var "chunkIndex") (.var "byteIndex"))) = .revert := by
    rw [evalExpr?]
    rw [bytesStoreSetChunkByteResolveRevertsOfChunksLength
      (evm := evm') (I := I) (chunksLen := chunksLenPost) hloadPost hboundPost]
    rfl
  exact bytesStoreSetChunkByteBodyReturnReverts
    (evm := evm) (evm' := evm') (I := I) hwv hassign hret

theorem bytesStoreSetChunkByteBodyReturnRevertsOfPostLengthRead
    {evm evm' : EVM.State} {I : ExecutionEnv} {chunksLenPost : UInt256}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hassign :
      assignStorageRef? bytesStoreConfig
        (bytesStoreSetChunkByteFrame I)
        evm .storage (chunkByteRef (.var "chunkIndex") (.var "byteIndex"))
          (bytesStoreSetChunkByteValue I) =
          .ok (bytesStoreSetChunkByteFrame I, evm'))
    (hloadPost :
      Solm.EVM.storageLoad evm' evm'.executionEnv.codeOwner ⟨1⟩ = chunksLenPost)
    (hchunkBoundPost :
      (bytesStoreSetChunkByteChunkIndexWord I).toNat < chunksLenPost.toNat)
    (hlenPost :
      readStorageBytesLength? bytesStoreConfig evm'
        (bytesStoreSetChunkByteHeaderRef I) = .revert) :
    ExecTransitionBody bytesStoreConfig bytesStoreContract evm
      (bytesStoreSetChunkByteLocals I) setChunkByteTransition.body .reverted := by
  have hret :
      evalExpr? bytesStoreConfig
        (bytesStoreSetChunkByteFrame I)
        evm' (.storage (chunkByteRef (.var "chunkIndex") (.var "byteIndex"))) = .revert := by
    rw [evalExpr?]
    rw [bytesStoreSetChunkByteResolveRevertsOfLengthRead
      (evm := evm') (I := I) (chunksLen := chunksLenPost)
      hloadPost hchunkBoundPost hlenPost]
    rfl
  exact bytesStoreSetChunkByteBodyReturnReverts
    (evm := evm) (evm' := evm') (I := I) hwv hassign hret

theorem bytesStoreSetChunkByteBodyReturnRevertsOfPostLength
    {evm evm' : EVM.State} {I : ExecutionEnv} {chunksLenPost : UInt256} {lenPost : Nat}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hassign :
      assignStorageRef? bytesStoreConfig
        (bytesStoreSetChunkByteFrame I)
        evm .storage (chunkByteRef (.var "chunkIndex") (.var "byteIndex"))
          (bytesStoreSetChunkByteValue I) =
          .ok (bytesStoreSetChunkByteFrame I, evm'))
    (hloadPost :
      Solm.EVM.storageLoad evm' evm'.executionEnv.codeOwner ⟨1⟩ = chunksLenPost)
    (hchunkBoundPost :
      (bytesStoreSetChunkByteChunkIndexWord I).toNat < chunksLenPost.toNat)
    (hlenPost :
      readStorageBytesLength? bytesStoreConfig evm'
        (bytesStoreSetChunkByteHeaderRef I) = .ok lenPost)
    (hboundPost : ¬ (bytesStoreSetChunkByteIndexWord I).toNat < lenPost) :
    ExecTransitionBody bytesStoreConfig bytesStoreContract evm
      (bytesStoreSetChunkByteLocals I) setChunkByteTransition.body .reverted := by
  have hret :
      evalExpr? bytesStoreConfig
        (bytesStoreSetChunkByteFrame I)
        evm' (.storage (chunkByteRef (.var "chunkIndex") (.var "byteIndex"))) = .revert := by
    rw [evalExpr?]
    rw [bytesStoreSetChunkByteResolveRevertsOfLength
      (evm := evm') (I := I) (chunksLen := chunksLenPost) (len := lenPost)
      hloadPost hchunkBoundPost hlenPost hboundPost]
    rfl
  exact bytesStoreSetChunkByteBodyReturnReverts
    (evm := evm) (evm' := evm') (I := I) hwv hassign hret

theorem bytesStoreSetChunkByteShortBodyReturnRevertsOfPostChunksLength
    {evm : EVM.State} {σ : AccountMap} {I : ExecutionEnv}
    {chunksLen chunksLenPost len : UInt256}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hloadChunks : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩ = chunksLen)
    (hchunkBound : (bytesStoreSetChunkByteChunkIndexWord I).toNat < chunksLen.toNat)
    (hloadChunksPost :
      Solm.EVM.storageLoad
          (Solm.EVM.storageStore evm evm.executionEnv.codeOwner
            (bytesStoreSetChunkByteSlot I)
            (bytesStoreSetChunkByteShortStoredWord σ I))
          evm.executionEnv.codeOwner ⟨1⟩ = chunksLenPost)
    (hchunkBoundPost :
      ¬ (bytesStoreSetChunkByteChunkIndexWord I).toNat < chunksLenPost.toNat)
    (hloadHeader : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (bytesStoreSetChunkByteSlot I) = bytesStoreSetChunkByteHeaderWord σ I)
    (hcanon : (bytesStoreSetChunkByteValueWord I).toNat < EVM.twoPow 8)
    (hlen : len =
      UInt256.land (UInt256.div (bytesStoreSetChunkByteHeaderWord σ I) ⟨2⟩) ⟨127⟩)
    (hshort : len.toNat < 32)
    (hbound : (bytesStoreSetChunkByteIndexWord I).toNat < len.toNat)
    (hflag : UInt256.land (bytesStoreSetChunkByteHeaderWord σ I) ⟨1⟩ = ⟨0⟩) :
    ExecTransitionBody bytesStoreConfig bytesStoreContract evm
      (bytesStoreSetChunkByteLocals I) setChunkByteTransition.body .reverted := by
  let evm' := Solm.EVM.storageStore evm evm.executionEnv.codeOwner
    (bytesStoreSetChunkByteSlot I)
    (bytesStoreSetChunkByteShortStoredWord σ I)
  have hlenRead :
      readStorageBytesLength? bytesStoreConfig evm
          (bytesStoreSetChunkByteHeaderRef I) =
        .ok len.toNat := by
    have hltLen : UInt256.lt len ⟨32⟩ = ⟨1⟩ := by
      exact ult_one (by
        simpa [show (⟨32⟩ : UInt256).toNat = 32 from by decide] using hshort)
    have hvalidLen : UInt256.sub ⟨0⟩ (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩ := by
      rw [hltLen]
      native_decide
    exact bytesStoreReadLengthOfHeaderLoad
      (er := bytesStoreSetChunkByteHeaderRef I) (evm := evm)
      (baseSlot := bytesStoreSetChunkByteSlot I)
      (header := bytesStoreSetChunkByteHeaderWord σ I) (len := len.toNat)
      (bytesStoreSetChunkByteHeaderRef_length_slot evm I)
      hloadHeader
      (solidityDecodeBytesLengthHeader_short_valid hflag hlen (by simpa [hflag] using hvalidLen))
  have hpacked : checkBytesPacked (bytesStoreSetChunkByteSlot I) evm = true :=
    checkBytesPacked_of_storageLoad_land_one_zero hloadHeader hflag
  have hidx31 : (bytesStoreSetChunkByteIndexWord I).toNat < 31 :=
    bytesStoreSetChunkByteIndex_lt31_of_short_bound (I := I) (len := len)
      hshort hbound
  have hlayout :
      bytesStoreConfig.storage.layout (bytesStoreSetChunkByteRef I) evm =
        some (uint8Loc (bytesStoreSetChunkByteSlot I)
          ⟨31 - (bytesStoreSetChunkByteIndexWord I).toNat, by omega⟩) :=
    bytesStoreSetChunkByteLayoutShort (evm := evm) (I := I) hpacked hidx31
  have hstore :
      (match bytesStoreConfig.storage.layout (bytesStoreSetChunkByteRef I) evm with
      | some loc => storageLocStore evm loc (bytesStoreSetChunkByteValue I)
      | none => none) = some evm' := by
    rw [hlayout]
    simpa [evm'] using
      bytesStoreSetChunkByteStorageLocStoreShort
        (evm := evm) (σ := σ) (I := I) (len := len)
        hloadHeader hcanon hshort hbound
  have hassign :
      assignStorageRef? bytesStoreConfig
        (bytesStoreSetChunkByteFrame I)
        evm .storage (chunkByteRef (.var "chunkIndex") (.var "byteIndex"))
          (bytesStoreSetChunkByteValue I) =
          .ok (bytesStoreSetChunkByteFrame I, evm') :=
    bytesStoreSetChunkByteAssignOfLength (evm := evm) (evm' := evm') (I := I)
      hloadChunks hchunkBound hlenRead hbound hstore
  have hloadChunksPost' :
      Solm.EVM.storageLoad evm' evm'.executionEnv.codeOwner ⟨1⟩ = chunksLenPost := by
    simpa [evm', storageStore_executionEnv] using hloadChunksPost
  exact bytesStoreSetChunkByteBodyReturnRevertsOfPostChunksLength
    (evm := evm) (evm' := evm') (I := I) (chunksLenPost := chunksLenPost)
    hwv hassign hloadChunksPost' hchunkBoundPost

theorem bytesStoreSetChunkByteLongBodyReturnRevertsOfPostChunksLength
    {evm : EVM.State} {σ : AccountMap} {I : ExecutionEnv}
    {chunksLen chunksLenPost len : UInt256}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hloadChunks : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩ = chunksLen)
    (hchunkBound : (bytesStoreSetChunkByteChunkIndexWord I).toNat < chunksLen.toNat)
    (hloadChunksPost :
      Solm.EVM.storageLoad
          (Solm.EVM.storageStore evm evm.executionEnv.codeOwner
            (bytesStoreSetChunkByteLongDataSlot I)
            (bytesStoreSetChunkByteLongStoredWord σ I))
          evm.executionEnv.codeOwner ⟨1⟩ = chunksLenPost)
    (hchunkBoundPost :
      ¬ (bytesStoreSetChunkByteChunkIndexWord I).toNat < chunksLenPost.toNat)
    (hloadHeader : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (bytesStoreSetChunkByteSlot I) = bytesStoreSetChunkByteHeaderWord σ I)
    (hloadData : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (bytesStoreSetChunkByteLongDataSlot I) =
      bytesStoreSetChunkByteLongOldWord σ I)
    (hcanon : (bytesStoreSetChunkByteValueWord I).toNat < EVM.twoPow 8)
    (hlen : len = UInt256.div (bytesStoreSetChunkByteHeaderWord σ I) ⟨2⟩)
    (hbound : (bytesStoreSetChunkByteIndexWord I).toNat < len.toNat)
    (hflag : UInt256.land (bytesStoreSetChunkByteHeaderWord σ I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (bytesStoreSetChunkByteHeaderWord σ I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStoreSetChunkByteHeaderWord σ I) ⟨2⟩) ⟨32⟩) ≠
          ⟨0⟩) :
    ExecTransitionBody bytesStoreConfig bytesStoreContract evm
      (bytesStoreSetChunkByteLocals I) setChunkByteTransition.body .reverted := by
  let evm' := Solm.EVM.storageStore evm evm.executionEnv.codeOwner
    (bytesStoreSetChunkByteLongDataSlot I)
    (bytesStoreSetChunkByteLongStoredWord σ I)
  have hvalidLen :
      UInt256.sub (UInt256.land (bytesStoreSetChunkByteHeaderWord σ I) ⟨1⟩)
        (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩ := by
    simpa [hlen] using hvalid
  have hlenRead :
      readStorageBytesLength? bytesStoreConfig evm
          (bytesStoreSetChunkByteHeaderRef I) =
        .ok len.toNat := by
    exact bytesStoreReadLengthOfHeaderLoad
      (er := bytesStoreSetChunkByteHeaderRef I) (evm := evm)
      (baseSlot := bytesStoreSetChunkByteSlot I)
      (header := bytesStoreSetChunkByteHeaderWord σ I) (len := len.toNat)
      (bytesStoreSetChunkByteHeaderRef_length_slot evm I)
      hloadHeader
      (solidityDecodeBytesLengthHeader_long_valid hflag hlen hvalidLen)
  have hpacked : checkBytesPacked (bytesStoreSetChunkByteSlot I) evm = false :=
    checkBytesPacked_of_storageLoad_land_one_ne_zero hloadHeader hflag
  have hlayout :
      bytesStoreConfig.storage.layout (bytesStoreSetChunkByteRef I) evm =
        some (uint8Loc (bytesStoreSetChunkByteLongDataSlot I)
          ⟨31 - (bytesStoreSetChunkByteLongWordIndex I).toNat, by
            have hidx := bytesStoreSetChunkByteLongWordIndex_lt32 I
            omega⟩) :=
    bytesStoreSetChunkByteLayoutLong (evm := evm) (I := I) hpacked
  have hstore :
      (match bytesStoreConfig.storage.layout (bytesStoreSetChunkByteRef I) evm with
      | some loc => storageLocStore evm loc (bytesStoreSetChunkByteValue I)
      | none => none) = some evm' := by
    rw [hlayout]
    simpa [evm'] using
      bytesStoreSetChunkByteStorageLocStoreLong
        (evm := evm) (σ := σ) (I := I) hloadData hcanon
  have hassign :
      assignStorageRef? bytesStoreConfig
        (bytesStoreSetChunkByteFrame I)
        evm .storage (chunkByteRef (.var "chunkIndex") (.var "byteIndex"))
          (bytesStoreSetChunkByteValue I) =
          .ok (bytesStoreSetChunkByteFrame I, evm') :=
    bytesStoreSetChunkByteAssignOfLength (evm := evm) (evm' := evm') (I := I)
      hloadChunks hchunkBound hlenRead hbound hstore
  have hloadChunksPost' :
      Solm.EVM.storageLoad evm' evm'.executionEnv.codeOwner ⟨1⟩ = chunksLenPost := by
    simpa [evm', storageStore_executionEnv] using hloadChunksPost
  exact bytesStoreSetChunkByteBodyReturnRevertsOfPostChunksLength
    (evm := evm) (evm' := evm') (I := I) (chunksLenPost := chunksLenPost)
    hwv hassign hloadChunksPost' hchunkBoundPost

theorem bytesStoreSetChunkByteLongBodyReturnRevertsOfPostLongMalformed
    {evm : EVM.State} {σ : AccountMap} {I : ExecutionEnv}
    {chunksLen chunksLenPost len postHeaderWord : UInt256}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hloadChunks : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩ = chunksLen)
    (hchunkBound : (bytesStoreSetChunkByteChunkIndexWord I).toNat < chunksLen.toNat)
    (hloadChunksPost :
      Solm.EVM.storageLoad
          (Solm.EVM.storageStore evm evm.executionEnv.codeOwner
            (bytesStoreSetChunkByteLongDataSlot I)
            (bytesStoreSetChunkByteLongStoredWord σ I))
          evm.executionEnv.codeOwner ⟨1⟩ = chunksLenPost)
    (hchunkBoundPost :
      (bytesStoreSetChunkByteChunkIndexWord I).toNat < chunksLenPost.toNat)
    (hloadHeader : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (bytesStoreSetChunkByteSlot I) = bytesStoreSetChunkByteHeaderWord σ I)
    (hloadData : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (bytesStoreSetChunkByteLongDataSlot I) =
      bytesStoreSetChunkByteLongOldWord σ I)
    (hloadHeaderPost :
      Solm.EVM.storageLoad
          (Solm.EVM.storageStore evm evm.executionEnv.codeOwner
            (bytesStoreSetChunkByteLongDataSlot I)
            (bytesStoreSetChunkByteLongStoredWord σ I))
          evm.executionEnv.codeOwner (bytesStoreSetChunkByteSlot I) =
        postHeaderWord)
    (hcanon : (bytesStoreSetChunkByteValueWord I).toNat < EVM.twoPow 8)
    (hlen : len = UInt256.div (bytesStoreSetChunkByteHeaderWord σ I) ⟨2⟩)
    (hbound : (bytesStoreSetChunkByteIndexWord I).toNat < len.toNat)
    (hflag : UInt256.land (bytesStoreSetChunkByteHeaderWord σ I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (bytesStoreSetChunkByteHeaderWord σ I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStoreSetChunkByteHeaderWord σ I) ⟨2⟩) ⟨32⟩) ≠
          ⟨0⟩)
    (hflagPost : UInt256.land postHeaderWord ⟨1⟩ ≠ ⟨0⟩)
    (hbadPost : UInt256.sub (UInt256.land postHeaderWord ⟨1⟩)
        (UInt256.lt (UInt256.div postHeaderWord ⟨2⟩) ⟨32⟩) = ⟨0⟩) :
    ExecTransitionBody bytesStoreConfig bytesStoreContract evm
      (bytesStoreSetChunkByteLocals I) setChunkByteTransition.body .reverted := by
  let evm' := Solm.EVM.storageStore evm evm.executionEnv.codeOwner
    (bytesStoreSetChunkByteLongDataSlot I)
    (bytesStoreSetChunkByteLongStoredWord σ I)
  have hvalidLen :
      UInt256.sub (UInt256.land (bytesStoreSetChunkByteHeaderWord σ I) ⟨1⟩)
        (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩ := by
    simpa [hlen] using hvalid
  have hlenRead :
      readStorageBytesLength? bytesStoreConfig evm
          (bytesStoreSetChunkByteHeaderRef I) =
        .ok len.toNat := by
    exact bytesStoreReadLengthOfHeaderLoad
      (er := bytesStoreSetChunkByteHeaderRef I) (evm := evm)
      (baseSlot := bytesStoreSetChunkByteSlot I)
      (header := bytesStoreSetChunkByteHeaderWord σ I) (len := len.toNat)
      (bytesStoreSetChunkByteHeaderRef_length_slot evm I)
      hloadHeader
      (solidityDecodeBytesLengthHeader_long_valid hflag hlen hvalidLen)
  have hpacked : checkBytesPacked (bytesStoreSetChunkByteSlot I) evm = false :=
    checkBytesPacked_of_storageLoad_land_one_ne_zero hloadHeader hflag
  have hlayout :
      bytesStoreConfig.storage.layout (bytesStoreSetChunkByteRef I) evm =
        some (uint8Loc (bytesStoreSetChunkByteLongDataSlot I)
          ⟨31 - (bytesStoreSetChunkByteLongWordIndex I).toNat, by
            have hidx := bytesStoreSetChunkByteLongWordIndex_lt32 I
            omega⟩) :=
    bytesStoreSetChunkByteLayoutLong (evm := evm) (I := I) hpacked
  have hstore :
      (match bytesStoreConfig.storage.layout (bytesStoreSetChunkByteRef I) evm with
      | some loc => storageLocStore evm loc (bytesStoreSetChunkByteValue I)
      | none => none) = some evm' := by
    rw [hlayout]
    simpa [evm'] using
      bytesStoreSetChunkByteStorageLocStoreLong
        (evm := evm) (σ := σ) (I := I) hloadData hcanon
  have hassign :
      assignStorageRef? bytesStoreConfig
        (bytesStoreSetChunkByteFrame I)
        evm .storage (chunkByteRef (.var "chunkIndex") (.var "byteIndex"))
          (bytesStoreSetChunkByteValue I) =
          .ok (bytesStoreSetChunkByteFrame I, evm') :=
    bytesStoreSetChunkByteAssignOfLength (evm := evm) (evm' := evm') (I := I)
      hloadChunks hchunkBound hlenRead hbound hstore
  have hloadChunksPost' :
      Solm.EVM.storageLoad evm' evm'.executionEnv.codeOwner ⟨1⟩ = chunksLenPost := by
    simpa [evm', storageStore_executionEnv] using hloadChunksPost
  have hloadHeaderPost' :
      Solm.EVM.storageLoad evm' evm'.executionEnv.codeOwner
          (bytesStoreSetChunkByteSlot I) =
        postHeaderWord := by
    simpa [evm', storageStore_executionEnv] using hloadHeaderPost
  have hlenPost :
      readStorageBytesLength? bytesStoreConfig evm'
          (bytesStoreSetChunkByteHeaderRef I) = .revert := by
    exact bytesStoreReadLengthRevertOfHeaderLoad
      (er := bytesStoreSetChunkByteHeaderRef I) (evm := evm')
      (baseSlot := bytesStoreSetChunkByteSlot I)
      (header := postHeaderWord)
      (bytesStoreSetChunkByteHeaderRef_length_slot evm' I)
      hloadHeaderPost'
      (by simp [solidityDecodeBytesLengthHeader, hflagPost, hbadPost])
  exact bytesStoreSetChunkByteBodyReturnRevertsOfPostLengthRead
    (evm := evm) (evm' := evm') (I := I) (chunksLenPost := chunksLenPost)
    hwv hassign hloadChunksPost' hchunkBoundPost hlenPost

theorem bytesStoreSetChunkByteLongBodyReturnRevertsOfPostLongLength
    {evm : EVM.State} {σ : AccountMap} {I : ExecutionEnv}
    {chunksLen chunksLenPost len lenPost postHeaderWord : UInt256}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hloadChunks : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩ = chunksLen)
    (hchunkBound : (bytesStoreSetChunkByteChunkIndexWord I).toNat < chunksLen.toNat)
    (hloadChunksPost :
      Solm.EVM.storageLoad
          (Solm.EVM.storageStore evm evm.executionEnv.codeOwner
            (bytesStoreSetChunkByteLongDataSlot I)
            (bytesStoreSetChunkByteLongStoredWord σ I))
          evm.executionEnv.codeOwner ⟨1⟩ = chunksLenPost)
    (hchunkBoundPost :
      (bytesStoreSetChunkByteChunkIndexWord I).toNat < chunksLenPost.toNat)
    (hloadHeader : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (bytesStoreSetChunkByteSlot I) = bytesStoreSetChunkByteHeaderWord σ I)
    (hloadData : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (bytesStoreSetChunkByteLongDataSlot I) =
      bytesStoreSetChunkByteLongOldWord σ I)
    (hloadHeaderPost :
      Solm.EVM.storageLoad
          (Solm.EVM.storageStore evm evm.executionEnv.codeOwner
            (bytesStoreSetChunkByteLongDataSlot I)
            (bytesStoreSetChunkByteLongStoredWord σ I))
          evm.executionEnv.codeOwner (bytesStoreSetChunkByteSlot I) =
        postHeaderWord)
    (hcanon : (bytesStoreSetChunkByteValueWord I).toNat < EVM.twoPow 8)
    (hlen : len = UInt256.div (bytesStoreSetChunkByteHeaderWord σ I) ⟨2⟩)
    (hlenPost : lenPost = UInt256.div postHeaderWord ⟨2⟩)
    (hbound : (bytesStoreSetChunkByteIndexWord I).toNat < len.toNat)
    (hboundPost : ¬ (bytesStoreSetChunkByteIndexWord I).toNat < lenPost.toNat)
    (hflag : UInt256.land (bytesStoreSetChunkByteHeaderWord σ I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (bytesStoreSetChunkByteHeaderWord σ I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStoreSetChunkByteHeaderWord σ I) ⟨2⟩) ⟨32⟩) ≠
          ⟨0⟩)
    (hflagPost : UInt256.land postHeaderWord ⟨1⟩ ≠ ⟨0⟩)
    (hvalidPost : UInt256.sub (UInt256.land postHeaderWord ⟨1⟩)
        (UInt256.lt (UInt256.div postHeaderWord ⟨2⟩) ⟨32⟩) ≠ ⟨0⟩) :
    ExecTransitionBody bytesStoreConfig bytesStoreContract evm
      (bytesStoreSetChunkByteLocals I) setChunkByteTransition.body .reverted := by
  let evm' := Solm.EVM.storageStore evm evm.executionEnv.codeOwner
    (bytesStoreSetChunkByteLongDataSlot I)
    (bytesStoreSetChunkByteLongStoredWord σ I)
  have hvalidLen :
      UInt256.sub (UInt256.land (bytesStoreSetChunkByteHeaderWord σ I) ⟨1⟩)
        (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩ := by
    simpa [hlen] using hvalid
  have hlenRead :
      readStorageBytesLength? bytesStoreConfig evm
          (bytesStoreSetChunkByteHeaderRef I) =
        .ok len.toNat := by
    exact bytesStoreReadLengthOfHeaderLoad
      (er := bytesStoreSetChunkByteHeaderRef I) (evm := evm)
      (baseSlot := bytesStoreSetChunkByteSlot I)
      (header := bytesStoreSetChunkByteHeaderWord σ I) (len := len.toNat)
      (bytesStoreSetChunkByteHeaderRef_length_slot evm I)
      hloadHeader
      (solidityDecodeBytesLengthHeader_long_valid hflag hlen hvalidLen)
  have hpacked : checkBytesPacked (bytesStoreSetChunkByteSlot I) evm = false :=
    checkBytesPacked_of_storageLoad_land_one_ne_zero hloadHeader hflag
  have hlayout :
      bytesStoreConfig.storage.layout (bytesStoreSetChunkByteRef I) evm =
        some (uint8Loc (bytesStoreSetChunkByteLongDataSlot I)
          ⟨31 - (bytesStoreSetChunkByteLongWordIndex I).toNat, by
            have hidx := bytesStoreSetChunkByteLongWordIndex_lt32 I
            omega⟩) :=
    bytesStoreSetChunkByteLayoutLong (evm := evm) (I := I) hpacked
  have hstore :
      (match bytesStoreConfig.storage.layout (bytesStoreSetChunkByteRef I) evm with
      | some loc => storageLocStore evm loc (bytesStoreSetChunkByteValue I)
      | none => none) = some evm' := by
    rw [hlayout]
    simpa [evm'] using
      bytesStoreSetChunkByteStorageLocStoreLong
        (evm := evm) (σ := σ) (I := I) hloadData hcanon
  have hassign :
      assignStorageRef? bytesStoreConfig
        (bytesStoreSetChunkByteFrame I)
        evm .storage (chunkByteRef (.var "chunkIndex") (.var "byteIndex"))
          (bytesStoreSetChunkByteValue I) =
          .ok (bytesStoreSetChunkByteFrame I, evm') :=
    bytesStoreSetChunkByteAssignOfLength (evm := evm) (evm' := evm') (I := I)
      hloadChunks hchunkBound hlenRead hbound hstore
  have hloadChunksPost' :
      Solm.EVM.storageLoad evm' evm'.executionEnv.codeOwner ⟨1⟩ = chunksLenPost := by
    simpa [evm', storageStore_executionEnv] using hloadChunksPost
  have hloadHeaderPost' :
      Solm.EVM.storageLoad evm' evm'.executionEnv.codeOwner
          (bytesStoreSetChunkByteSlot I) =
        postHeaderWord := by
    simpa [evm', storageStore_executionEnv] using hloadHeaderPost
  have hlenPostRead :
      readStorageBytesLength? bytesStoreConfig evm'
          (bytesStoreSetChunkByteHeaderRef I) = .ok lenPost.toNat := by
    have hvalidLenPost :
        UInt256.sub (UInt256.land postHeaderWord ⟨1⟩) (UInt256.lt lenPost ⟨32⟩) ≠
          ⟨0⟩ := by
      simpa [hlenPost] using hvalidPost
    exact bytesStoreReadLengthOfHeaderLoad
      (er := bytesStoreSetChunkByteHeaderRef I) (evm := evm')
      (baseSlot := bytesStoreSetChunkByteSlot I)
      (header := postHeaderWord) (len := lenPost.toNat)
      (bytesStoreSetChunkByteHeaderRef_length_slot evm' I)
      hloadHeaderPost'
      (solidityDecodeBytesLengthHeader_long_valid hflagPost hlenPost hvalidLenPost)
  exact bytesStoreSetChunkByteBodyReturnRevertsOfPostLength
    (evm := evm) (evm' := evm') (I := I) (chunksLenPost := chunksLenPost)
    (lenPost := lenPost.toNat)
    hwv hassign hloadChunksPost' hchunkBoundPost hlenPostRead hboundPost

theorem bytesStoreSetChunkByteLongBodyReturnRevertsOfPostShortLength
    {evm : EVM.State} {σ : AccountMap} {I : ExecutionEnv}
    {chunksLen chunksLenPost len lenPost postHeaderWord : UInt256}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hloadChunks : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩ = chunksLen)
    (hchunkBound : (bytesStoreSetChunkByteChunkIndexWord I).toNat < chunksLen.toNat)
    (hloadChunksPost :
      Solm.EVM.storageLoad
          (Solm.EVM.storageStore evm evm.executionEnv.codeOwner
            (bytesStoreSetChunkByteLongDataSlot I)
            (bytesStoreSetChunkByteLongStoredWord σ I))
          evm.executionEnv.codeOwner ⟨1⟩ = chunksLenPost)
    (hchunkBoundPost :
      (bytesStoreSetChunkByteChunkIndexWord I).toNat < chunksLenPost.toNat)
    (hloadHeader : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (bytesStoreSetChunkByteSlot I) = bytesStoreSetChunkByteHeaderWord σ I)
    (hloadData : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (bytesStoreSetChunkByteLongDataSlot I) =
      bytesStoreSetChunkByteLongOldWord σ I)
    (hloadHeaderPost :
      Solm.EVM.storageLoad
          (Solm.EVM.storageStore evm evm.executionEnv.codeOwner
            (bytesStoreSetChunkByteLongDataSlot I)
            (bytesStoreSetChunkByteLongStoredWord σ I))
          evm.executionEnv.codeOwner (bytesStoreSetChunkByteSlot I) =
        postHeaderWord)
    (hcanon : (bytesStoreSetChunkByteValueWord I).toNat < EVM.twoPow 8)
    (hlen : len = UInt256.div (bytesStoreSetChunkByteHeaderWord σ I) ⟨2⟩)
    (hlenPost : lenPost = UInt256.land (UInt256.div postHeaderWord ⟨2⟩) ⟨127⟩)
    (hbound : (bytesStoreSetChunkByteIndexWord I).toNat < len.toNat)
    (hboundPost : ¬ (bytesStoreSetChunkByteIndexWord I).toNat < lenPost.toNat)
    (hflag : UInt256.land (bytesStoreSetChunkByteHeaderWord σ I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (bytesStoreSetChunkByteHeaderWord σ I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStoreSetChunkByteHeaderWord σ I) ⟨2⟩) ⟨32⟩) ≠
          ⟨0⟩)
    (hflagPost : UInt256.land postHeaderWord ⟨1⟩ = ⟨0⟩)
    (hvalidPost : UInt256.sub (UInt256.land postHeaderWord ⟨1⟩)
        (UInt256.lt (UInt256.land (UInt256.div postHeaderWord ⟨2⟩) ⟨127⟩) ⟨32⟩) ≠
          ⟨0⟩) :
    ExecTransitionBody bytesStoreConfig bytesStoreContract evm
      (bytesStoreSetChunkByteLocals I) setChunkByteTransition.body .reverted := by
  let evm' := Solm.EVM.storageStore evm evm.executionEnv.codeOwner
    (bytesStoreSetChunkByteLongDataSlot I)
    (bytesStoreSetChunkByteLongStoredWord σ I)
  have hvalidLen :
      UInt256.sub (UInt256.land (bytesStoreSetChunkByteHeaderWord σ I) ⟨1⟩)
        (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩ := by
    simpa [hlen] using hvalid
  have hlenRead :
      readStorageBytesLength? bytesStoreConfig evm
          (bytesStoreSetChunkByteHeaderRef I) =
        .ok len.toNat := by
    exact bytesStoreReadLengthOfHeaderLoad
      (er := bytesStoreSetChunkByteHeaderRef I) (evm := evm)
      (baseSlot := bytesStoreSetChunkByteSlot I)
      (header := bytesStoreSetChunkByteHeaderWord σ I) (len := len.toNat)
      (bytesStoreSetChunkByteHeaderRef_length_slot evm I)
      hloadHeader
      (solidityDecodeBytesLengthHeader_long_valid hflag hlen hvalidLen)
  have hpacked : checkBytesPacked (bytesStoreSetChunkByteSlot I) evm = false :=
    checkBytesPacked_of_storageLoad_land_one_ne_zero hloadHeader hflag
  have hlayout :
      bytesStoreConfig.storage.layout (bytesStoreSetChunkByteRef I) evm =
        some (uint8Loc (bytesStoreSetChunkByteLongDataSlot I)
          ⟨31 - (bytesStoreSetChunkByteLongWordIndex I).toNat, by
            have hidx := bytesStoreSetChunkByteLongWordIndex_lt32 I
            omega⟩) :=
    bytesStoreSetChunkByteLayoutLong (evm := evm) (I := I) hpacked
  have hstore :
      (match bytesStoreConfig.storage.layout (bytesStoreSetChunkByteRef I) evm with
      | some loc => storageLocStore evm loc (bytesStoreSetChunkByteValue I)
      | none => none) = some evm' := by
    rw [hlayout]
    simpa [evm'] using
      bytesStoreSetChunkByteStorageLocStoreLong
        (evm := evm) (σ := σ) (I := I) hloadData hcanon
  have hassign :
      assignStorageRef? bytesStoreConfig
        (bytesStoreSetChunkByteFrame I)
        evm .storage (chunkByteRef (.var "chunkIndex") (.var "byteIndex"))
          (bytesStoreSetChunkByteValue I) =
          .ok (bytesStoreSetChunkByteFrame I, evm') :=
    bytesStoreSetChunkByteAssignOfLength (evm := evm) (evm' := evm') (I := I)
      hloadChunks hchunkBound hlenRead hbound hstore
  have hloadChunksPost' :
      Solm.EVM.storageLoad evm' evm'.executionEnv.codeOwner ⟨1⟩ = chunksLenPost := by
    simpa [evm', storageStore_executionEnv] using hloadChunksPost
  have hloadHeaderPost' :
      Solm.EVM.storageLoad evm' evm'.executionEnv.codeOwner
          (bytesStoreSetChunkByteSlot I) =
        postHeaderWord := by
    simpa [evm', storageStore_executionEnv] using hloadHeaderPost
  have hlenPostRead :
      readStorageBytesLength? bytesStoreConfig evm'
          (bytesStoreSetChunkByteHeaderRef I) = .ok lenPost.toNat := by
    have hvalidLenPost :
        UInt256.sub ⟨0⟩ (UInt256.lt lenPost ⟨32⟩) ≠ ⟨0⟩ := by
      simpa [hflagPost, hlenPost] using hvalidPost
    exact bytesStoreReadLengthOfHeaderLoad
      (er := bytesStoreSetChunkByteHeaderRef I) (evm := evm')
      (baseSlot := bytesStoreSetChunkByteSlot I)
      (header := postHeaderWord) (len := lenPost.toNat)
      (bytesStoreSetChunkByteHeaderRef_length_slot evm' I)
      hloadHeaderPost'
      (solidityDecodeBytesLengthHeader_short_valid hflagPost hlenPost
        (by simpa [← hlenPost] using hvalidPost))
  exact bytesStoreSetChunkByteBodyReturnRevertsOfPostLength
    (evm := evm) (evm' := evm') (I := I) (chunksLenPost := chunksLenPost)
    (lenPost := lenPost.toNat)
    hwv hassign hloadChunksPost' hchunkBoundPost hlenPostRead hboundPost

theorem bytesStoreSetChunkByteLongBodyReturnRevertsOfPostShortMalformed
    {evm : EVM.State} {σ : AccountMap} {I : ExecutionEnv}
    {chunksLen chunksLenPost len postHeaderWord : UInt256}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hloadChunks : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩ = chunksLen)
    (hchunkBound : (bytesStoreSetChunkByteChunkIndexWord I).toNat < chunksLen.toNat)
    (hloadChunksPost :
      Solm.EVM.storageLoad
          (Solm.EVM.storageStore evm evm.executionEnv.codeOwner
            (bytesStoreSetChunkByteLongDataSlot I)
            (bytesStoreSetChunkByteLongStoredWord σ I))
          evm.executionEnv.codeOwner ⟨1⟩ = chunksLenPost)
    (hchunkBoundPost :
      (bytesStoreSetChunkByteChunkIndexWord I).toNat < chunksLenPost.toNat)
    (hloadHeader : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (bytesStoreSetChunkByteSlot I) = bytesStoreSetChunkByteHeaderWord σ I)
    (hloadData : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (bytesStoreSetChunkByteLongDataSlot I) =
      bytesStoreSetChunkByteLongOldWord σ I)
    (hloadHeaderPost :
      Solm.EVM.storageLoad
          (Solm.EVM.storageStore evm evm.executionEnv.codeOwner
            (bytesStoreSetChunkByteLongDataSlot I)
            (bytesStoreSetChunkByteLongStoredWord σ I))
          evm.executionEnv.codeOwner (bytesStoreSetChunkByteSlot I) =
        postHeaderWord)
    (hcanon : (bytesStoreSetChunkByteValueWord I).toNat < EVM.twoPow 8)
    (hlen : len = UInt256.div (bytesStoreSetChunkByteHeaderWord σ I) ⟨2⟩)
    (hbound : (bytesStoreSetChunkByteIndexWord I).toNat < len.toNat)
    (hflag : UInt256.land (bytesStoreSetChunkByteHeaderWord σ I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (bytesStoreSetChunkByteHeaderWord σ I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStoreSetChunkByteHeaderWord σ I) ⟨2⟩) ⟨32⟩) ≠
          ⟨0⟩)
    (hflagPost : UInt256.land postHeaderWord ⟨1⟩ = ⟨0⟩)
    (hbadPost : UInt256.sub (UInt256.land postHeaderWord ⟨1⟩)
        (UInt256.lt (UInt256.land (UInt256.div postHeaderWord ⟨2⟩) ⟨127⟩) ⟨32⟩) = ⟨0⟩) :
    ExecTransitionBody bytesStoreConfig bytesStoreContract evm
      (bytesStoreSetChunkByteLocals I) setChunkByteTransition.body .reverted := by
  let evm' := Solm.EVM.storageStore evm evm.executionEnv.codeOwner
    (bytesStoreSetChunkByteLongDataSlot I)
    (bytesStoreSetChunkByteLongStoredWord σ I)
  have hvalidLen :
      UInt256.sub (UInt256.land (bytesStoreSetChunkByteHeaderWord σ I) ⟨1⟩)
        (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩ := by
    simpa [hlen] using hvalid
  have hlenRead :
      readStorageBytesLength? bytesStoreConfig evm
          (bytesStoreSetChunkByteHeaderRef I) =
        .ok len.toNat := by
    exact bytesStoreReadLengthOfHeaderLoad
      (er := bytesStoreSetChunkByteHeaderRef I) (evm := evm)
      (baseSlot := bytesStoreSetChunkByteSlot I)
      (header := bytesStoreSetChunkByteHeaderWord σ I) (len := len.toNat)
      (bytesStoreSetChunkByteHeaderRef_length_slot evm I)
      hloadHeader
      (solidityDecodeBytesLengthHeader_long_valid hflag hlen hvalidLen)
  have hpacked : checkBytesPacked (bytesStoreSetChunkByteSlot I) evm = false :=
    checkBytesPacked_of_storageLoad_land_one_ne_zero hloadHeader hflag
  have hlayout :
      bytesStoreConfig.storage.layout (bytesStoreSetChunkByteRef I) evm =
        some (uint8Loc (bytesStoreSetChunkByteLongDataSlot I)
          ⟨31 - (bytesStoreSetChunkByteLongWordIndex I).toNat, by
            have hidx := bytesStoreSetChunkByteLongWordIndex_lt32 I
            omega⟩) :=
    bytesStoreSetChunkByteLayoutLong (evm := evm) (I := I) hpacked
  have hstore :
      (match bytesStoreConfig.storage.layout (bytesStoreSetChunkByteRef I) evm with
      | some loc => storageLocStore evm loc (bytesStoreSetChunkByteValue I)
      | none => none) = some evm' := by
    rw [hlayout]
    simpa [evm'] using
      bytesStoreSetChunkByteStorageLocStoreLong
        (evm := evm) (σ := σ) (I := I) hloadData hcanon
  have hassign :
      assignStorageRef? bytesStoreConfig
        (bytesStoreSetChunkByteFrame I)
        evm .storage (chunkByteRef (.var "chunkIndex") (.var "byteIndex"))
          (bytesStoreSetChunkByteValue I) =
          .ok (bytesStoreSetChunkByteFrame I, evm') :=
    bytesStoreSetChunkByteAssignOfLength (evm := evm) (evm' := evm') (I := I)
      hloadChunks hchunkBound hlenRead hbound hstore
  have hloadChunksPost' :
      Solm.EVM.storageLoad evm' evm'.executionEnv.codeOwner ⟨1⟩ = chunksLenPost := by
    simpa [evm', storageStore_executionEnv] using hloadChunksPost
  have hloadHeaderPost' :
      Solm.EVM.storageLoad evm' evm'.executionEnv.codeOwner
          (bytesStoreSetChunkByteSlot I) =
        postHeaderWord := by
    simpa [evm', storageStore_executionEnv] using hloadHeaderPost
  have hlenPost :
      readStorageBytesLength? bytesStoreConfig evm'
          (bytesStoreSetChunkByteHeaderRef I) = .revert := by
    have hbadPost' :
        UInt256.sub ⟨0⟩
          (UInt256.lt (UInt256.land (UInt256.div postHeaderWord ⟨2⟩) ⟨127⟩) ⟨32⟩) =
          ⟨0⟩ := by
      simpa [hflagPost] using hbadPost
    exact bytesStoreReadLengthRevertOfHeaderLoad
      (er := bytesStoreSetChunkByteHeaderRef I) (evm := evm')
      (baseSlot := bytesStoreSetChunkByteSlot I)
      (header := postHeaderWord)
      (bytesStoreSetChunkByteHeaderRef_length_slot evm' I)
      hloadHeaderPost'
      (by simp [solidityDecodeBytesLengthHeader, hflagPost, hbadPost'])
  exact bytesStoreSetChunkByteBodyReturnRevertsOfPostLengthRead
    (evm := evm) (evm' := evm') (I := I) (chunksLenPost := chunksLenPost)
    hwv hassign hloadChunksPost' hchunkBoundPost hlenPost

theorem bytesStoreDecode_setChunkByte {I : ExecutionEnv}
    (hsz100 : 100 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (bytesStoreSetChunkByteValueWord I).toNat < EVM.twoPow 8) :
    decodeCalldata (setChunkByteTransition.params.map Param.name)
      (transitionSignature setChunkByteTransition).paramTypes I.calldata =
        some (bytesStoreSetChunkByteLocals I) := by
  show decodeCalldata ["chunkIndex", "byteIndex", "value"] [uint256, uint256, uint8]
      I.calldata = some (bytesStoreSetChunkByteLocals I)
  simpa [uint256, uint8, uint8Int, abiUInt256, abiUInt8,
    bytesStoreSetChunkByteLocals, bytesStoreSetChunkByteChunkIndexWord,
    bytesStoreSetChunkByteIndexWord, bytesStoreSetChunkByteValueWord] using
    decodeCalldata_uint256_uint256_uint8_ok (cd := I.calldata) (x := "chunkIndex")
      (y := "byteIndex") (z := "value") hsz100 hhi hcanon

theorem bytesStoreDecode_setChunkByte_locals {I : ExecutionEnv}
    (hsz100 : 100 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (bytesStoreSetChunkByteValueWord I).toNat < EVM.twoPow 8) :
    decodeCalldata (setChunkByteTransition.params.map Param.name)
      (transitionSignature setChunkByteTransition).paramTypes I.calldata =
        some (bytesStoreSetChunkByteLocals I) := by
  simpa [bytesStoreSetChunkByteLocals] using
    bytesStoreDecode_setChunkByte (I := I) hsz100 hhi hcanon

theorem bytesStoreDecode_setChunkByte_none_noncanon_value {I : ExecutionEnv}
    (hsz100 : 100 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hnc : ¬ (bytesStoreSetChunkByteValueWord I).toNat < EVM.twoPow 8) :
    decodeCalldata (setChunkByteTransition.params.map Param.name)
      (transitionSignature setChunkByteTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["chunkIndex", "byteIndex", "value"] [uint256, uint256, uint8]
      I.calldata = none
  simpa [uint256, uint8, uint8Int, abiUInt256, abiUInt8,
    bytesStoreSetChunkByteValueWord] using
    decodeCalldata_uint256_uint256_uint8_none_noncanon2 (cd := I.calldata)
      (x := "chunkIndex") (y := "byteIndex") (z := "value") hsz100 hhi hnc

theorem bytesStoreDecode_setChunkByte_none_short {I : ExecutionEnv}
    (hshort : I.calldata.size < 100) :
    decodeCalldata (setChunkByteTransition.params.map Param.name)
      (transitionSignature setChunkByteTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["chunkIndex", "byteIndex", "value"] [uint256, uint256, uint8]
      I.calldata = none
  simpa [uint256, uint8, uint8Int, abiUInt256, abiUInt8] using
    decodeCalldata_uint256_uint256_uint8_none_short (cd := I.calldata)
      (x := "chunkIndex") (y := "byteIndex") (z := "value") hshort

theorem bytesStoreDecode_setChunkByte_none_huge {I : ExecutionEnv}
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size) :
    decodeCalldata (setChunkByteTransition.params.map Param.name)
      (transitionSignature setChunkByteTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["chunkIndex", "byteIndex", "value"] [uint256, uint256, uint8]
      I.calldata = none
  simpa [uint256, uint8, uint8Int, abiUInt256, abiUInt8] using
    decodeCalldata_uint256_uint256_uint8_none_huge (cd := I.calldata)
      (x := "chunkIndex") (y := "byteIndex") (z := "value") hbig

end BytesStore
