import Examples.BytesStoreLite.FullSetChunk
import Examples.BytesStoreLite.FullSetPacketByte

/-!
# BytesStoreLite — `setChunkByte(uint256,uint256,uint8)` runtime slice

This split module starts the nested dynamic-array byte setter proof.  It reuses the existing
`setPacketByte` byte-update machinery shape, but the calldata words and storage header slot differ:
the bytes header is `chunksDataBase + chunkIndex`, and the byte index/value are the second and
third ABI words.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000
set_option maxHeartbeats 4000000

namespace BytesStoreLite

def bytesStoreLiteSetChunkByteChunkIndexWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 4

def bytesStoreLiteSetChunkByteIndexWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 36

def bytesStoreLiteSetChunkByteValueWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 68

def bytesStoreLiteSetChunkByteLocals (I : ExecutionEnv) : Store :=
  (((∅ : Store).insert "chunkIndex"
    (.int (Int.ofNat (bytesStoreLiteSetChunkByteChunkIndexWord I).toNat))).insert "byteIndex"
    (.int (Int.ofNat (bytesStoreLiteSetChunkByteIndexWord I).toNat))).insert "value"
    (.int (Int.ofNat (bytesStoreLiteSetChunkByteValueWord I).toNat))

theorem bytesStoreLiteSetChunkByteLocals_get_chunkIndex (I : ExecutionEnv) :
    (bytesStoreLiteSetChunkByteLocals I).get? "chunkIndex" =
      some (.int (Int.ofNat (bytesStoreLiteSetChunkByteChunkIndexWord I).toNat)) := by
  rw [bytesStoreLiteSetChunkByteLocals]
  rw [store_get_ne (h := by decide)]
  rw [store_get_ne (h := by decide)]
  exact store_get_self (∅ : Store) "chunkIndex"
    (.int (Int.ofNat (bytesStoreLiteSetChunkByteChunkIndexWord I).toNat))

theorem bytesStoreLiteSetChunkByteLocals_getElem_chunkIndex (I : ExecutionEnv) :
    (bytesStoreLiteSetChunkByteLocals I)["chunkIndex"]? =
      some (.int (Int.ofNat (bytesStoreLiteSetChunkByteChunkIndexWord I).toNat)) := by
  simpa [Std.HashMap.get?_eq_getElem?] using
    bytesStoreLiteSetChunkByteLocals_get_chunkIndex I

theorem bytesStoreLiteSetChunkByteLocals_get_byteIndex (I : ExecutionEnv) :
    (bytesStoreLiteSetChunkByteLocals I).get? "byteIndex" =
      some (.int (Int.ofNat (bytesStoreLiteSetChunkByteIndexWord I).toNat)) := by
  rw [bytesStoreLiteSetChunkByteLocals]
  rw [store_get_ne (h := by decide)]
  exact store_get_self ((∅ : Store).insert "chunkIndex"
    (.int (Int.ofNat (bytesStoreLiteSetChunkByteChunkIndexWord I).toNat))) "byteIndex"
    (.int (Int.ofNat (bytesStoreLiteSetChunkByteIndexWord I).toNat))

theorem bytesStoreLiteSetChunkByteLocals_getElem_byteIndex (I : ExecutionEnv) :
    (bytesStoreLiteSetChunkByteLocals I)["byteIndex"]? =
      some (.int (Int.ofNat (bytesStoreLiteSetChunkByteIndexWord I).toNat)) := by
  simpa [Std.HashMap.get?_eq_getElem?] using
    bytesStoreLiteSetChunkByteLocals_get_byteIndex I

theorem bytesStoreLiteSetChunkByteLocals_get_chunks_none (I : ExecutionEnv) :
    (bytesStoreLiteSetChunkByteLocals I).get? "chunks" = none := by
  rw [bytesStoreLiteSetChunkByteLocals]
  rw [store_get_ne (h := by decide)]
  rw [store_get_ne (h := by decide)]
  rw [store_get_ne (h := by decide)]
  simp

theorem bytesStoreLiteSetChunkByteLocals_getElem_chunks_none (I : ExecutionEnv) :
    (bytesStoreLiteSetChunkByteLocals I)["chunks"]? = none := by
  simpa [Std.HashMap.get?_eq_getElem?] using
    bytesStoreLiteSetChunkByteLocals_get_chunks_none I

def bytesStoreLiteSetChunkByteRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "chunks"
    steps := [
      .aindex (.int (Int.ofNat (bytesStoreLiteSetChunkByteChunkIndexWord I).toNat)),
      .aindex (.int (Int.ofNat (bytesStoreLiteSetChunkByteIndexWord I).toNat))] }

def bytesStoreLiteSetChunkByteHeaderRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "chunks"
    steps := [.aindex (.int (Int.ofNat (bytesStoreLiteSetChunkByteChunkIndexWord I).toNat))] }

def bytesStoreLiteSetChunkByteValue (I : ExecutionEnv) : Value :=
  .int (Int.ofNat (bytesStoreLiteSetChunkByteValueWord I).toNat)

def bytesStoreLiteSetChunkByteFrame (I : ExecutionEnv) : Frame :=
  { contract := bytesStoreLiteContract, locals := bytesStoreLiteSetChunkByteLocals I }

def bytesStoreLiteSetChunkByteSlot (I : ExecutionEnv) : UInt256 :=
  chunksDataBase + bytesStoreLiteSetChunkByteChunkIndexWord I

theorem bytesStoreLiteSetChunkByteHeaderRef_length_slot (evm : EVM.State) (I : ExecutionEnv) :
    ∃ loc, bytesStoreLiteLayout
        { bytesStoreLiteSetChunkByteHeaderRef I with
          steps := (bytesStoreLiteSetChunkByteHeaderRef I).steps ++ [.length] } evm =
          some loc ∧
        loc.slot = bytesStoreLiteSetChunkByteSlot I := by
  refine ⟨bytesLikeLengthLoc (bytesStoreLiteSetChunkByteSlot I) evm, ?_, ?_⟩
  · have hnonneg : ¬ ((bytesStoreLiteSetChunkByteChunkIndexWord I).toNat : Int) < 0 := by
      omega
    simp [bytesStoreLiteLayout, bytesStoreLiteSetChunkByteHeaderRef, chunksElemSlot?,
      nonnegativeIndexSlot?, bytesStoreLiteSetChunkByteSlot, u256_ofNat_toNat]
    simp [hnonneg]
  · simp [bytesLikeLengthLoc]

def bytesStoreLiteSetChunkByteHeaderWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  (σ.find? I.codeOwner |>.option ⟨0⟩
    (fun acc => acc.storage.findD (bytesStoreLiteSetChunkByteSlot I) ⟨0⟩))

theorem bytesStoreLiteSetChunkByteHeaderWord_eq_of_accountMapEquiv
    {σ_evm σ_solm : AccountMap} {I : ExecutionEnv}
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    bytesStoreLiteSetChunkByteHeaderWord σ_evm I =
      bytesStoreLiteSetChunkByteHeaderWord σ_solm I :=
  accountMapEquiv_storage_findD hAccounts I.codeOwner
    (bytesStoreLiteSetChunkByteSlot I) ⟨0⟩

theorem bytesStoreLiteStorageLoadSetChunkByteHeader_initState_of_accountMapEquiv
    {cA : Batteries.RBSet AccountAddress compare} {gh : BlockHeader} {bl : ProcessedBlocks}
    {σ_evm σ_solm σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : Sat256}
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    Solm.EVM.storageLoad (initState cA gh bl σ_solm σ₀ g A I)
        (initState cA gh bl σ_solm σ₀ g A I).executionEnv.codeOwner
        (bytesStoreLiteSetChunkByteSlot I) =
      bytesStoreLiteSetChunkByteHeaderWord σ_evm I := by
  simpa [bytesStoreLiteSetChunkByteHeaderWord] using
    bytesStoreLiteStorageLoad_initState_of_accountMapEquiv
      (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
      (I := I) (g := g) (bytesStoreLiteSetChunkByteSlot I) hAccounts

theorem bytesStoreLiteStorageLoadSetChunkByteHeader_of_accountMapEquiv
    {evm : EVM.State} {σ : AccountMap} {I : ExecutionEnv}
    (howner : evm.executionEnv.codeOwner = I.codeOwner)
    (hAccounts : accountMapEquiv σ evm.accountMap) :
    Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (bytesStoreLiteSetChunkByteSlot I) =
      bytesStoreLiteSetChunkByteHeaderWord σ I := by
  exact (accountStorageWord_eq_storageLoad_of_accountMapEquiv
    (owner := I.codeOwner) (slot := bytesStoreLiteSetChunkByteSlot I)
    howner hAccounts).symm

def bytesStoreLiteSetChunkByteShortScale (I : ExecutionEnv) : UInt256 :=
  UInt256.exp ⟨256⟩ (UInt256.sub ⟨31⟩ (bytesStoreLiteSetChunkByteIndexWord I))

def bytesStoreLiteSetChunkByteShortStoredWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.lor
    (UInt256.mul
      (UInt256.div (UInt256.shiftLeft (bytesStoreLiteSetChunkByteValueWord I) ⟨248⟩)
        (UInt256.shiftLeft ⟨1⟩ ⟨248⟩))
      (bytesStoreLiteSetChunkByteShortScale I))
    (UInt256.land
      (UInt256.lnot (UInt256.mul ⟨255⟩ (bytesStoreLiteSetChunkByteShortScale I)))
      (bytesStoreLiteSetChunkByteHeaderWord σ I))

def bytesStoreLiteSetChunkByteLongWordIndex (I : ExecutionEnv) : UInt256 :=
  UInt256.mod (bytesStoreLiteSetChunkByteIndexWord I) ⟨32⟩

def bytesStoreLiteSetChunkByteLongDataSlot (I : ExecutionEnv) : UInt256 :=
  bytesLikeDataBase (bytesStoreLiteSetChunkByteSlot I) +
    UInt256.div (bytesStoreLiteSetChunkByteIndexWord I) ⟨32⟩

def bytesStoreLiteSetChunkByteLongScale (I : ExecutionEnv) : UInt256 :=
  UInt256.exp ⟨256⟩ (UInt256.sub ⟨31⟩ (bytesStoreLiteSetChunkByteLongWordIndex I))

def bytesStoreLiteSetChunkByteLongOldWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  (σ.find? I.codeOwner |>.option ⟨0⟩
    (fun acc => acc.storage.findD (bytesStoreLiteSetChunkByteLongDataSlot I) ⟨0⟩))

theorem bytesStoreLiteSetChunkByteLongOldWord_eq_of_accountMapEquiv
    {σ_evm σ_solm : AccountMap} {I : ExecutionEnv}
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    bytesStoreLiteSetChunkByteLongOldWord σ_evm I =
      bytesStoreLiteSetChunkByteLongOldWord σ_solm I :=
  accountMapEquiv_storage_findD hAccounts I.codeOwner
    (bytesStoreLiteSetChunkByteLongDataSlot I) ⟨0⟩

theorem bytesStoreLiteStorageLoadSetChunkByteLongData_initState_of_accountMapEquiv
    {cA : Batteries.RBSet AccountAddress compare} {gh : BlockHeader} {bl : ProcessedBlocks}
    {σ_evm σ_solm σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : Sat256}
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    Solm.EVM.storageLoad (initState cA gh bl σ_solm σ₀ g A I)
        (initState cA gh bl σ_solm σ₀ g A I).executionEnv.codeOwner
        (bytesStoreLiteSetChunkByteLongDataSlot I) =
      bytesStoreLiteSetChunkByteLongOldWord σ_evm I := by
  simpa [bytesStoreLiteSetChunkByteLongOldWord] using
    bytesStoreLiteStorageLoad_initState_of_accountMapEquiv
      (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
      (I := I) (g := g) (bytesStoreLiteSetChunkByteLongDataSlot I) hAccounts

def bytesStoreLiteSetChunkByteLongStoredWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.lor
    (UInt256.mul
      (UInt256.div (UInt256.shiftLeft (bytesStoreLiteSetChunkByteValueWord I) ⟨248⟩)
        (UInt256.shiftLeft ⟨1⟩ ⟨248⟩))
      (bytesStoreLiteSetChunkByteLongScale I))
    (UInt256.land
      (UInt256.lnot (UInt256.mul ⟨255⟩ (bytesStoreLiteSetChunkByteLongScale I)))
      (bytesStoreLiteSetChunkByteLongOldWord σ I))

theorem bytesStoreLiteSetChunkByteChunkIndexWord_eq_setChunkIndexWord (I : ExecutionEnv) :
    bytesStoreLiteSetChunkByteChunkIndexWord I = bytesStoreLiteSetChunkIndexWord I := by
  rfl

theorem bytesStoreLiteSetChunkByteLongWordIndex_toNat (I : ExecutionEnv) :
    (bytesStoreLiteSetChunkByteLongWordIndex I).toNat =
      (bytesStoreLiteSetChunkByteIndexWord I).toNat % 32 := by
  rw [bytesStoreLiteSetChunkByteLongWordIndex]
  unfold UInt256.mod
  rw [if_neg (by native_decide)]
  rfl

theorem bytesStoreLiteSetChunkByteLongWordIndex_lt32 (I : ExecutionEnv) :
    (bytesStoreLiteSetChunkByteLongWordIndex I).toNat < 32 := by
  rw [bytesStoreLiteSetChunkByteLongWordIndex_toNat]
  exact Nat.mod_lt _ (by decide : 0 < 32)

theorem bytesStoreLiteSetChunkByteLongWordIndex_eq_index_of_lt32
    {I : ExecutionEnv}
    (hidx : (bytesStoreLiteSetChunkByteIndexWord I).toNat < 32) :
    bytesStoreLiteSetChunkByteLongWordIndex I =
      bytesStoreLiteSetChunkByteIndexWord I := by
  apply u256_inj
  rw [bytesStoreLiteSetChunkByteLongWordIndex_toNat]
  exact Nat.mod_eq_of_lt hidx

theorem bytesStoreLiteSetChunkByte_storageTypeAt {I : ExecutionEnv} :
    storageTypeAt? bytesStoreLiteContract.storage (bytesStoreLiteSetChunkByteRef I) =
      some uint8St := by
  simp [bytesStoreLiteSetChunkByteRef, storageTypeAt?, bytesStoreLiteContract, storageDecls,
    storageTypeStep?, bytesSt, uint8St, uint8Int]

theorem bytesStoreLiteSetChunkByteLayoutShort {evm : EVM.State} {I : ExecutionEnv}
    (hpacked : checkBytesPacked (bytesStoreLiteSetChunkByteSlot I) evm = true)
    (hidx : (bytesStoreLiteSetChunkByteIndexWord I).toNat < 31) :
    bytesStoreLiteConfig.storage.layout (bytesStoreLiteSetChunkByteRef I) evm =
      some (uint8Loc (bytesStoreLiteSetChunkByteSlot I)
        ⟨31 - (bytesStoreLiteSetChunkByteIndexWord I).toNat, by omega⟩) := by
  have hchunkNN :
      ¬ (((bytesStoreLiteSetChunkByteChunkIndexWord I).toNat : Int) < 0) := by omega
  have hbyteNN :
      ¬ (((bytesStoreLiteSetChunkByteIndexWord I).toNat : Int) < 0) := by omega
  have hpackedSlot :
      checkBytesPacked (chunksDataBase + bytesStoreLiteSetChunkByteChunkIndexWord I) evm = true := by
    simpa [bytesStoreLiteSetChunkByteSlot] using hpacked
  simp [bytesStoreLiteConfig, bytesStoreLiteStorageLayout, solidityStorageLayout,
    bytesStoreLiteLayout, bytesStoreLiteSetChunkByteRef, bytesStoreLiteSetChunkByteSlot,
    chunksElemSlot?, nonnegativeIndexSlot?, bytesLikeByteLoc?, uint8Loc, uint8Int, hpackedSlot,
    hidx, hchunkNN, hbyteNN, u256_ofNat_toNat]

theorem bytesStoreLiteSetChunkByteLayoutLong {evm : EVM.State} {I : ExecutionEnv}
    (hpacked : checkBytesPacked (bytesStoreLiteSetChunkByteSlot I) evm = false) :
    bytesStoreLiteConfig.storage.layout (bytesStoreLiteSetChunkByteRef I) evm =
      some (uint8Loc (bytesStoreLiteSetChunkByteLongDataSlot I)
        ⟨31 - (bytesStoreLiteSetChunkByteLongWordIndex I).toNat, by
          have hidx := bytesStoreLiteSetChunkByteLongWordIndex_lt32 I
          omega⟩) := by
  have hchunkNN :
      ¬ (((bytesStoreLiteSetChunkByteChunkIndexWord I).toNat : Int) < 0) := by omega
  have hbyteNN :
      ¬ (((bytesStoreLiteSetChunkByteIndexWord I).toNat : Int) < 0) := by omega
  have hpackedSlot :
      checkBytesPacked (chunksDataBase + bytesStoreLiteSetChunkByteChunkIndexWord I) evm = false := by
    simpa [bytesStoreLiteSetChunkByteSlot] using hpacked
  rw [bytesStoreLiteSetChunkByteLongDataSlot, u256_div32_eq_ofNat_toNat_div]
  simp [bytesStoreLiteConfig, bytesStoreLiteStorageLayout, solidityStorageLayout,
    bytesStoreLiteLayout, bytesStoreLiteSetChunkByteRef, bytesStoreLiteSetChunkByteSlot,
    chunksElemSlot?, nonnegativeIndexSlot?, bytesLikeByteLoc?, uint8Loc, uint8Int, hpackedSlot,
    hchunkNN, hbyteNN, bytesStoreLiteSetChunkByteLongWordIndex_toNat, u256_ofNat_toNat]

theorem bytesStoreLiteSetChunkByteIndex_lt31_of_short_bound {I : ExecutionEnv} {len : UInt256}
    (hshort : len.toNat < 32)
    (hbound : (bytesStoreLiteSetChunkByteIndexWord I).toNat < len.toNat) :
    (bytesStoreLiteSetChunkByteIndexWord I).toNat < 31 := by
  omega

theorem bytesStoreLiteSetChunkByteValueHighShiftDiv
    {I : ExecutionEnv}
    (hcanon : (bytesStoreLiteSetChunkByteValueWord I).toNat < EVM.twoPow 8) :
    UInt256.div (UInt256.shiftLeft (bytesStoreLiteSetChunkByteValueWord I) ⟨248⟩)
        (UInt256.shiftLeft ⟨1⟩ ⟨248⟩) =
      bytesStoreLiteSetChunkByteValueWord I := by
  apply u256_inj
  rw [udiv_toNat, bytesStoreLiteShiftLeftOne248_toNat]
  unfold UInt256.shiftLeft
  rw [if_neg (by decide : ¬ ((⟨248⟩ : UInt256).val ≥ 256))]
  change ((((bytesStoreLiteSetChunkByteValueWord I).val <<< (⟨248⟩ : UInt256).val) :
      Fin UInt256.size).val) / 2 ^ 248 = (bytesStoreLiteSetChunkByteValueWord I).toNat
  rw [Fin.shiftLeft_val, Nat.shiftLeft_eq]
  change (bytesStoreLiteSetChunkByteValueWord I).toNat * 2 ^ 248 % UInt256.size / 2 ^ 248 =
    (bytesStoreLiteSetChunkByteValueWord I).toNat
  rw [Nat.mod_eq_of_lt]
  · rw [Nat.mul_comm]
    rw [Nat.mul_div_right _ (by positivity : 0 < 2 ^ 248)]
  · rw [show UInt256.size = 2 ^ 256 from rfl]
    calc (bytesStoreLiteSetChunkByteValueWord I).toNat * 2 ^ 248 < 256 * 2 ^ 248 :=
        Nat.mul_lt_mul_of_pos_right hcanon (by positivity)
      _ = 2 ^ 256 := by
        rw [show (256 : Nat) = 2 ^ 8 by norm_num]
        rw [← pow_add]
        norm_num

theorem bytesStoreLiteSetChunkByteShortScale_toNat {I : ExecutionEnv} {len : UInt256}
    (hshort : len.toNat < 32)
    (hbound : (bytesStoreLiteSetChunkByteIndexWord I).toNat < len.toNat) :
    (bytesStoreLiteSetChunkByteShortScale I).toNat =
      2 ^ ((31 - (bytesStoreLiteSetChunkByteIndexWord I).toNat) * 8) := by
  have hidx : (bytesStoreLiteSetChunkByteIndexWord I).toNat < 31 :=
    bytesStoreLiteSetChunkByteIndex_lt31_of_short_bound hshort hbound
  interval_cases hnat : (bytesStoreLiteSetChunkByteIndexWord I).toNat
  all_goals
    have hword : bytesStoreLiteSetChunkByteIndexWord I =
        UInt256.ofNat (bytesStoreLiteSetChunkByteIndexWord I).toNat := by
      exact (u256_ofNat_toNat (bytesStoreLiteSetChunkByteIndexWord I)).symm
    rw [bytesStoreLiteSetChunkByteShortScale, hword, hnat]
    native_decide

theorem bytesStoreLiteSetChunkByteShortMaskWord_toNat {I : ExecutionEnv} {len : UInt256}
    (hshort : len.toNat < 32)
    (hbound : (bytesStoreLiteSetChunkByteIndexWord I).toNat < len.toNat) :
    (UInt256.mul ⟨255⟩ (bytesStoreLiteSetChunkByteShortScale I)).toNat =
      255 * 2 ^ ((31 - (bytesStoreLiteSetChunkByteIndexWord I).toNat) * 8) := by
  rw [u256_mul_toNat, bytesStoreLiteSetChunkByteShortScale_toNat (I := I) (len := len)
    hshort hbound]
  rw [show (⟨255⟩ : UInt256).toNat = 255 by decide]
  rw [Nat.mod_eq_of_lt]
  have hk : ((31 - (bytesStoreLiteSetChunkByteIndexWord I).toNat) * 8) + 8 ≤ 256 := by
    have hidx : (bytesStoreLiteSetChunkByteIndexWord I).toNat < 31 :=
      bytesStoreLiteSetChunkByteIndex_lt31_of_short_bound (I := I) (len := len) hshort hbound
    omega
  calc 255 * 2 ^ ((31 - (bytesStoreLiteSetChunkByteIndexWord I).toNat) * 8) <
      256 * 2 ^ ((31 - (bytesStoreLiteSetChunkByteIndexWord I).toNat) * 8) := by
        exact Nat.mul_lt_mul_of_pos_right (by norm_num : 255 < 256) (by positivity)
    _ ≤ UInt256.size := by
      rw [show UInt256.size = 2 ^ 256 from rfl]
      rw [show 256 = 2 ^ 8 by norm_num, ← Nat.pow_add]
      exact Nat.pow_le_pow_right (by norm_num) (by omega)

theorem bytesStoreLiteSetChunkByteShortClearMask_toNat {I : ExecutionEnv} {len : UInt256}
    (hshort : len.toNat < 32)
    (hbound : (bytesStoreLiteSetChunkByteIndexWord I).toNat < len.toNat) :
    (UInt256.lnot (UInt256.mul ⟨255⟩ (bytesStoreLiteSetChunkByteShortScale I))).toNat =
      2 ^ 256 - 1 - 255 * 2 ^ ((31 - (bytesStoreLiteSetChunkByteIndexWord I).toNat) * 8) := by
  rw [u256_lnot_toNat, bytesStoreLiteSetChunkByteShortMaskWord_toNat (I := I) (len := len)
    hshort hbound]
  rfl

theorem bytesStoreLiteSetChunkByteLongScale_toNat {I : ExecutionEnv} :
    (bytesStoreLiteSetChunkByteLongScale I).toNat =
      2 ^ ((31 - (bytesStoreLiteSetChunkByteLongWordIndex I).toNat) * 8) := by
  have hidx : (bytesStoreLiteSetChunkByteLongWordIndex I).toNat < 32 :=
    bytesStoreLiteSetChunkByteLongWordIndex_lt32 I
  interval_cases hnat : (bytesStoreLiteSetChunkByteLongWordIndex I).toNat
  all_goals
    have hword : bytesStoreLiteSetChunkByteLongWordIndex I =
        UInt256.ofNat (bytesStoreLiteSetChunkByteLongWordIndex I).toNat := by
      exact (u256_ofNat_toNat (bytesStoreLiteSetChunkByteLongWordIndex I)).symm
    rw [bytesStoreLiteSetChunkByteLongScale, hword, hnat]
    native_decide

theorem bytesStoreLiteSetChunkByteLongMaskWord_toNat {I : ExecutionEnv} :
    (UInt256.mul ⟨255⟩ (bytesStoreLiteSetChunkByteLongScale I)).toNat =
      255 * 2 ^ ((31 - (bytesStoreLiteSetChunkByteLongWordIndex I).toNat) * 8) := by
  rw [u256_mul_toNat, bytesStoreLiteSetChunkByteLongScale_toNat (I := I)]
  rw [show (⟨255⟩ : UInt256).toNat = 255 by decide]
  rw [Nat.mod_eq_of_lt]
  have hk : ((31 - (bytesStoreLiteSetChunkByteLongWordIndex I).toNat) * 8) + 8 ≤ 256 := by
    have hidx : (bytesStoreLiteSetChunkByteLongWordIndex I).toNat < 32 :=
      bytesStoreLiteSetChunkByteLongWordIndex_lt32 I
    omega
  calc 255 * 2 ^ ((31 - (bytesStoreLiteSetChunkByteLongWordIndex I).toNat) * 8) <
      256 * 2 ^ ((31 - (bytesStoreLiteSetChunkByteLongWordIndex I).toNat) * 8) := by
        exact Nat.mul_lt_mul_of_pos_right (by norm_num : 255 < 256) (by positivity)
    _ = 2 ^ (((31 - (bytesStoreLiteSetChunkByteLongWordIndex I).toNat) * 8) + 8) := by
        rw [show 256 = 2 ^ 8 by norm_num, ← Nat.pow_add]
        ring
    _ ≤ 2 ^ 256 := Nat.pow_le_pow_right (by norm_num) hk
    _ = UInt256.size := rfl

theorem bytesStoreLiteSetChunkByteLongClearMask_toNat {I : ExecutionEnv} :
    (UInt256.lnot (UInt256.mul ⟨255⟩ (bytesStoreLiteSetChunkByteLongScale I))).toNat =
      (2 : Nat) ^ 256 - 1 -
        255 * 2 ^ ((31 - (bytesStoreLiteSetChunkByteLongWordIndex I).toNat) * 8) := by
  rw [u256_lnot_toNat, bytesStoreLiteSetChunkByteLongMaskWord_toNat (I := I)]
  rfl

theorem bytesStoreLiteSetChunkByteShortStoredWord_byteAt
    {σ : AccountMap} {I : ExecutionEnv} {len : UInt256}
    (hcanon : (bytesStoreLiteSetChunkByteValueWord I).toNat < EVM.twoPow 8)
    (hshort : len.toNat < 32)
    (hbound : (bytesStoreLiteSetChunkByteIndexWord I).toNat < len.toNat) :
    UInt256.byteAt (bytesStoreLiteSetChunkByteIndexWord I)
      (bytesStoreLiteSetChunkByteShortStoredWord σ I) =
        bytesStoreLiteSetChunkByteValueWord I := by
  apply u256_inj
  have hi31 : (bytesStoreLiteSetChunkByteIndexWord I).toNat ≤ 31 := by
    have hlt := bytesStoreLiteSetChunkByteIndex_lt31_of_short_bound (I := I) (len := len)
      hshort hbound
    omega
  rw [byteAt_toNat_of_le31 hi31]
  rw [bytesStoreLiteSetChunkByteShortStoredWord,
    bytesStoreLiteSetChunkByteValueHighShiftDiv hcanon]
  rw [u256_lor_toNat, u256_mul_toNat, u256_land_toNat]
  rw [bytesStoreLiteSetChunkByteShortScale_toNat (I := I) (len := len) hshort hbound]
  rw [bytesStoreLiteSetChunkByteShortClearMask_toNat (I := I) (len := len) hshort hbound]
  have hv : (bytesStoreLiteSetChunkByteValueWord I).toNat < 256 := by
    simpa [EVM.twoPow] using hcanon
  have hk : ((31 - (bytesStoreLiteSetChunkByteIndexWord I).toNat) * 8) + 8 ≤ 256 := by
    have hidx : (bytesStoreLiteSetChunkByteIndexWord I).toNat < 31 :=
      bytesStoreLiteSetChunkByteIndex_lt31_of_short_bound (I := I) (len := len) hshort hbound
    omega
  have hleftLt : (bytesStoreLiteSetChunkByteValueWord I).toNat *
      2 ^ ((31 - (bytesStoreLiteSetChunkByteIndexWord I).toNat) * 8) < UInt256.size := by
    rw [show UInt256.size = 2 ^ 256 from rfl]
    calc (bytesStoreLiteSetChunkByteValueWord I).toNat *
            2 ^ ((31 - (bytesStoreLiteSetChunkByteIndexWord I).toNat) * 8) <
          256 * 2 ^ ((31 - (bytesStoreLiteSetChunkByteIndexWord I).toNat) * 8) :=
            Nat.mul_lt_mul_of_pos_right hv (by positivity)
        _ ≤ 2 ^ 256 := by
          rw [show 256 = 2 ^ 8 by norm_num, ← Nat.pow_add]
          exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hrightLt : (((2 : Nat) ^ 256 - 1 -
        255 * 2 ^ ((31 - (bytesStoreLiteSetChunkByteIndexWord I).toNat) * 8)) &&&
        (bytesStoreLiteSetChunkByteHeaderWord σ I).toNat) < UInt256.size := by
    exact lt_of_le_of_lt Nat.and_le_right (bytesStoreLiteSetChunkByteHeaderWord σ I).val.isLt
  rw [Nat.mod_eq_of_lt hleftLt]
  change ((bytesStoreLiteSetChunkByteValueWord I).toNat *
          2 ^ ((31 - (bytesStoreLiteSetChunkByteIndexWord I).toNat) * 8)).lor
        ((((2 : Nat) ^ 256 - 1 -
          255 * 2 ^ ((31 - (bytesStoreLiteSetChunkByteIndexWord I).toNat) * 8)) &&&
          (bytesStoreLiteSetChunkByteHeaderWord σ I).toNat) % UInt256.size) %
        UInt256.size /
      2 ^ ((31 - (bytesStoreLiteSetChunkByteIndexWord I).toNat) * 8) % 256 =
    (bytesStoreLiteSetChunkByteValueWord I).toNat
  rw [Nat.mod_eq_of_lt hrightLt]
  have hlorLt :
      ((bytesStoreLiteSetChunkByteValueWord I).toNat *
            2 ^ ((31 - (bytesStoreLiteSetChunkByteIndexWord I).toNat) * 8)).lor
          (((2 : Nat) ^ 256 - 1 -
              255 * 2 ^ ((31 - (bytesStoreLiteSetChunkByteIndexWord I).toNat) * 8)) &&&
            (bytesStoreLiteSetChunkByteHeaderWord σ I).toNat) < UInt256.size := by
    change ((bytesStoreLiteSetChunkByteValueWord I).toNat *
          2 ^ ((31 - (bytesStoreLiteSetChunkByteIndexWord I).toNat) * 8)) |||
        (((2 : Nat) ^ 256 - 1 -
            255 * 2 ^ ((31 - (bytesStoreLiteSetChunkByteIndexWord I).toNat) * 8)) &&&
          (bytesStoreLiteSetChunkByteHeaderWord σ I).toNat) < 2 ^ 256
    apply Nat.or_lt_two_pow
    · simpa [UInt256.size] using hleftLt
    · simpa [UInt256.size] using hrightLt
  rw [Nat.mod_eq_of_lt hlorLt]
  exact nat_byte_lane_lor_clear_eq
    (old := (bytesStoreLiteSetChunkByteHeaderWord σ I).toNat)
    (v := (bytesStoreLiteSetChunkByteValueWord I).toNat)
    (k := (31 - (bytesStoreLiteSetChunkByteIndexWord I).toNat) * 8) hv hk

theorem bytesStoreLiteSetChunkByteLongStoredWord_byteAt
    {σ : AccountMap} {I : ExecutionEnv}
    (hcanon : (bytesStoreLiteSetChunkByteValueWord I).toNat < EVM.twoPow 8) :
    UInt256.byteAt (bytesStoreLiteSetChunkByteLongWordIndex I)
      (bytesStoreLiteSetChunkByteLongStoredWord σ I) =
        bytesStoreLiteSetChunkByteValueWord I := by
  apply u256_inj
  have hv : (bytesStoreLiteSetChunkByteValueWord I).toNat < 256 := by
    simpa [EVM.twoPow] using hcanon
  have hidxLt : (bytesStoreLiteSetChunkByteLongWordIndex I).toNat < 32 :=
    bytesStoreLiteSetChunkByteLongWordIndex_lt32 I
  have hidxLe : (bytesStoreLiteSetChunkByteLongWordIndex I).toNat ≤ 31 := by omega
  rw [byteAt_toNat_of_le31 hidxLe]
  rw [bytesStoreLiteSetChunkByteLongStoredWord,
    bytesStoreLiteSetChunkByteValueHighShiftDiv hcanon]
  rw [u256_lor_toNat, u256_mul_toNat, u256_land_toNat]
  rw [bytesStoreLiteSetChunkByteLongScale_toNat (I := I)]
  rw [bytesStoreLiteSetChunkByteLongClearMask_toNat (I := I)]
  have hk : ((31 - (bytesStoreLiteSetChunkByteLongWordIndex I).toNat) * 8) + 8 ≤ 256 := by
    omega
  have hleftLt : (bytesStoreLiteSetChunkByteValueWord I).toNat *
      2 ^ ((31 - (bytesStoreLiteSetChunkByteLongWordIndex I).toNat) * 8) < UInt256.size := by
    rw [show UInt256.size = 2 ^ 256 from rfl]
    calc (bytesStoreLiteSetChunkByteValueWord I).toNat *
            2 ^ ((31 - (bytesStoreLiteSetChunkByteLongWordIndex I).toNat) * 8) <
          256 * 2 ^ ((31 - (bytesStoreLiteSetChunkByteLongWordIndex I).toNat) * 8) :=
            Nat.mul_lt_mul_of_pos_right hv (by positivity)
        _ = 2 ^ (8 + (31 - (bytesStoreLiteSetChunkByteLongWordIndex I).toNat) * 8) := by
          rw [show 256 = 2 ^ 8 by norm_num, Nat.pow_add]
        _ ≤ 2 ^ 256 := by
          exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hrightLt : (((2 : Nat) ^ 256 - 1 -
        255 * 2 ^ ((31 - (bytesStoreLiteSetChunkByteLongWordIndex I).toNat) * 8)) &&&
        (bytesStoreLiteSetChunkByteLongOldWord σ I).toNat) < UInt256.size := by
    exact lt_of_le_of_lt Nat.and_le_right (bytesStoreLiteSetChunkByteLongOldWord σ I).val.isLt
  rw [Nat.mod_eq_of_lt hleftLt]
  change (((bytesStoreLiteSetChunkByteValueWord I).toNat *
          2 ^ ((31 - (bytesStoreLiteSetChunkByteLongWordIndex I).toNat) * 8)).lor
        ((((2 : Nat) ^ 256 - 1 -
          255 * 2 ^ ((31 - (bytesStoreLiteSetChunkByteLongWordIndex I).toNat) * 8)) &&&
          (bytesStoreLiteSetChunkByteLongOldWord σ I).toNat) % UInt256.size) %
        UInt256.size) /
      2 ^ ((31 - (bytesStoreLiteSetChunkByteLongWordIndex I).toNat) * 8) % 256 =
    (bytesStoreLiteSetChunkByteValueWord I).toNat
  rw [Nat.mod_eq_of_lt hrightLt]
  have hlorLt :
      ((bytesStoreLiteSetChunkByteValueWord I).toNat *
            2 ^ ((31 - (bytesStoreLiteSetChunkByteLongWordIndex I).toNat) * 8)).lor
          (((2 : Nat) ^ 256 - 1 -
              255 * 2 ^ ((31 - (bytesStoreLiteSetChunkByteLongWordIndex I).toNat) * 8)) &&&
            (bytesStoreLiteSetChunkByteLongOldWord σ I).toNat) < UInt256.size := by
    change ((bytesStoreLiteSetChunkByteValueWord I).toNat *
          2 ^ ((31 - (bytesStoreLiteSetChunkByteLongWordIndex I).toNat) * 8)) |||
        (((2 : Nat) ^ 256 - 1 -
            255 * 2 ^ ((31 - (bytesStoreLiteSetChunkByteLongWordIndex I).toNat) * 8)) &&&
          (bytesStoreLiteSetChunkByteLongOldWord σ I).toNat) < 2 ^ 256
    apply Nat.or_lt_two_pow
    · simpa [UInt256.size] using hleftLt
    · simpa [UInt256.size] using hrightLt
  rw [Nat.mod_eq_of_lt hlorLt]
  exact nat_byte_lane_lor_clear_eq
    (old := (bytesStoreLiteSetChunkByteLongOldWord σ I).toNat)
    (v := (bytesStoreLiteSetChunkByteValueWord I).toNat)
    (k := (31 - (bytesStoreLiteSetChunkByteLongWordIndex I).toNat) * 8) hv hk

theorem bytesStoreLiteSetChunkByteLongStoredWord_byteAt_index_of_lt32
    {σ : AccountMap} {I : ExecutionEnv}
    (hcanon : (bytesStoreLiteSetChunkByteValueWord I).toNat < EVM.twoPow 8)
    (hidx : (bytesStoreLiteSetChunkByteIndexWord I).toNat < 32) :
    UInt256.byteAt (bytesStoreLiteSetChunkByteIndexWord I)
      (bytesStoreLiteSetChunkByteLongStoredWord σ I) =
        bytesStoreLiteSetChunkByteValueWord I := by
  have heq := bytesStoreLiteSetChunkByteLongWordIndex_eq_index_of_lt32
    (I := I) hidx
  rw [← heq]
  exact bytesStoreLiteSetChunkByteLongStoredWord_byteAt (σ := σ) (I := I) hcanon

theorem bytesStoreLiteSetChunkByteShortStoredWord_toNat_update
    {σ : AccountMap} {I : ExecutionEnv} {len : UInt256}
    (hcanon : (bytesStoreLiteSetChunkByteValueWord I).toNat < EVM.twoPow 8)
    (hshort : len.toNat < 32)
    (hbound : (bytesStoreLiteSetChunkByteIndexWord I).toNat < len.toNat) :
    (bytesStoreLiteSetChunkByteHeaderWord σ I).toNat %
          2 ^ ((31 - (bytesStoreLiteSetChunkByteIndexWord I).toNat) * 8) +
        2 ^ ((31 - (bytesStoreLiteSetChunkByteIndexWord I).toNat) * 8) *
          (bytesStoreLiteSetChunkByteValueWord I).toNat +
      2 ^ ((31 - (bytesStoreLiteSetChunkByteIndexWord I).toNat) * 8 + 8) *
        ((bytesStoreLiteSetChunkByteHeaderWord σ I).toNat /
          2 ^ ((31 - (bytesStoreLiteSetChunkByteIndexWord I).toNat) * 8 + 8)) =
    (bytesStoreLiteSetChunkByteShortStoredWord σ I).toNat := by
  have hv : (bytesStoreLiteSetChunkByteValueWord I).toNat < 256 := by
    simpa [EVM.twoPow] using hcanon
  rw [bytesStoreLiteSetChunkByteShortStoredWord,
    bytesStoreLiteSetChunkByteValueHighShiftDiv hcanon]
  rw [u256_lor_toNat, u256_mul_toNat, u256_land_toNat]
  rw [bytesStoreLiteSetChunkByteShortScale_toNat (I := I) (len := len) hshort hbound]
  rw [bytesStoreLiteSetChunkByteShortClearMask_toNat (I := I) (len := len) hshort hbound]
  have hk : ((31 - (bytesStoreLiteSetChunkByteIndexWord I).toNat) * 8) + 8 ≤ 256 := by
    have hidx := bytesStoreLiteSetChunkByteIndex_lt31_of_short_bound
      (I := I) (len := len) hshort hbound
    omega
  have hleftLt : (bytesStoreLiteSetChunkByteValueWord I).toNat *
      2 ^ ((31 - (bytesStoreLiteSetChunkByteIndexWord I).toNat) * 8) < UInt256.size := by
    rw [show UInt256.size = 2 ^ 256 from rfl]
    calc (bytesStoreLiteSetChunkByteValueWord I).toNat *
            2 ^ ((31 - (bytesStoreLiteSetChunkByteIndexWord I).toNat) * 8) <
          256 * 2 ^ ((31 - (bytesStoreLiteSetChunkByteIndexWord I).toNat) * 8) :=
            Nat.mul_lt_mul_of_pos_right hv (by positivity)
        _ ≤ 2 ^ 256 := by
          rw [show 256 = 2 ^ 8 by norm_num, ← Nat.pow_add]
          exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hrightLt : (((2 : Nat) ^ 256 - 1 -
        255 * 2 ^ ((31 - (bytesStoreLiteSetChunkByteIndexWord I).toNat) * 8)) &&&
        (bytesStoreLiteSetChunkByteHeaderWord σ I).toNat) < UInt256.size := by
    exact lt_of_le_of_lt Nat.and_le_right (bytesStoreLiteSetChunkByteHeaderWord σ I).val.isLt
  rw [Nat.mod_eq_of_lt hleftLt]
  change (bytesStoreLiteSetChunkByteHeaderWord σ I).toNat %
        2 ^ ((31 - (bytesStoreLiteSetChunkByteIndexWord I).toNat) * 8) +
      2 ^ ((31 - (bytesStoreLiteSetChunkByteIndexWord I).toNat) * 8) *
        (bytesStoreLiteSetChunkByteValueWord I).toNat +
      2 ^ (((31 - (bytesStoreLiteSetChunkByteIndexWord I).toNat) * 8) + 8) *
        ((bytesStoreLiteSetChunkByteHeaderWord σ I).toNat /
          2 ^ (((31 - (bytesStoreLiteSetChunkByteIndexWord I).toNat) * 8) + 8)) =
      ((bytesStoreLiteSetChunkByteValueWord I).toNat *
          2 ^ ((31 - (bytesStoreLiteSetChunkByteIndexWord I).toNat) * 8)).lor
        ((((2 : Nat) ^ 256 - 1 -
          255 * 2 ^ ((31 - (bytesStoreLiteSetChunkByteIndexWord I).toNat) * 8)) &&&
          (bytesStoreLiteSetChunkByteHeaderWord σ I).toNat) % UInt256.size) %
        UInt256.size
  rw [Nat.mod_eq_of_lt hrightLt]
  have hlorLt :
      ((bytesStoreLiteSetChunkByteValueWord I).toNat *
            2 ^ ((31 - (bytesStoreLiteSetChunkByteIndexWord I).toNat) * 8)).lor
          (((2 : Nat) ^ 256 - 1 -
              255 * 2 ^ ((31 - (bytesStoreLiteSetChunkByteIndexWord I).toNat) * 8)) &&&
            (bytesStoreLiteSetChunkByteHeaderWord σ I).toNat) < UInt256.size := by
    change ((bytesStoreLiteSetChunkByteValueWord I).toNat *
          2 ^ ((31 - (bytesStoreLiteSetChunkByteIndexWord I).toNat) * 8)) |||
        (((2 : Nat) ^ 256 - 1 -
            255 * 2 ^ ((31 - (bytesStoreLiteSetChunkByteIndexWord I).toNat) * 8)) &&&
          (bytesStoreLiteSetChunkByteHeaderWord σ I).toNat) < 2 ^ 256
    apply Nat.or_lt_two_pow
    · simpa [UInt256.size] using hleftLt
    · simpa [UInt256.size] using hrightLt
  rw [Nat.mod_eq_of_lt hlorLt]
  rw [show 2 ^ ((31 - (bytesStoreLiteSetChunkByteIndexWord I).toNat) * 8) *
        (bytesStoreLiteSetChunkByteValueWord I).toNat =
        (bytesStoreLiteSetChunkByteValueWord I).toNat *
          2 ^ ((31 - (bytesStoreLiteSetChunkByteIndexWord I).toNat) * 8) by ring]
  rw [show 2 ^ (((31 - (bytesStoreLiteSetChunkByteIndexWord I).toNat) * 8) + 8) *
        ((bytesStoreLiteSetChunkByteHeaderWord σ I).toNat /
          2 ^ (((31 - (bytesStoreLiteSetChunkByteIndexWord I).toNat) * 8) + 8)) =
      (bytesStoreLiteSetChunkByteHeaderWord σ I).toNat /
          2 ^ (((31 - (bytesStoreLiteSetChunkByteIndexWord I).toNat) * 8) + 8) *
        2 ^ (((31 - (bytesStoreLiteSetChunkByteIndexWord I).toNat) * 8) + 8) by ring]
  exact nat_byte_update_eq
    (old := (bytesStoreLiteSetChunkByteHeaderWord σ I).toNat)
    (v := (bytesStoreLiteSetChunkByteValueWord I).toNat)
    (k := (31 - (bytesStoreLiteSetChunkByteIndexWord I).toNat) * 8)
    hv hk (by exact (bytesStoreLiteSetChunkByteHeaderWord σ I).val.isLt)

theorem bytesStoreLiteSetChunkByteLongStoredWord_toNat_update
    {σ : AccountMap} {I : ExecutionEnv}
    (hcanon : (bytesStoreLiteSetChunkByteValueWord I).toNat < EVM.twoPow 8) :
    (bytesStoreLiteSetChunkByteLongOldWord σ I).toNat %
          2 ^ ((31 - (bytesStoreLiteSetChunkByteLongWordIndex I).toNat) * 8) +
        2 ^ ((31 - (bytesStoreLiteSetChunkByteLongWordIndex I).toNat) * 8) *
          (bytesStoreLiteSetChunkByteValueWord I).toNat +
      2 ^ ((31 - (bytesStoreLiteSetChunkByteLongWordIndex I).toNat) * 8 + 8) *
        ((bytesStoreLiteSetChunkByteLongOldWord σ I).toNat /
          2 ^ ((31 - (bytesStoreLiteSetChunkByteLongWordIndex I).toNat) * 8 + 8)) =
    (bytesStoreLiteSetChunkByteLongStoredWord σ I).toNat := by
  have hv : (bytesStoreLiteSetChunkByteValueWord I).toNat < 256 := by
    simpa [EVM.twoPow] using hcanon
  rw [bytesStoreLiteSetChunkByteLongStoredWord,
    bytesStoreLiteSetChunkByteValueHighShiftDiv hcanon]
  rw [u256_lor_toNat, u256_mul_toNat, u256_land_toNat]
  rw [bytesStoreLiteSetChunkByteLongScale_toNat (I := I)]
  rw [bytesStoreLiteSetChunkByteLongClearMask_toNat (I := I)]
  have hidxLt : (bytesStoreLiteSetChunkByteLongWordIndex I).toNat < 32 :=
    bytesStoreLiteSetChunkByteLongWordIndex_lt32 I
  have hk : ((31 - (bytesStoreLiteSetChunkByteLongWordIndex I).toNat) * 8) + 8 ≤ 256 := by
    omega
  have hleftLt : (bytesStoreLiteSetChunkByteValueWord I).toNat *
      2 ^ ((31 - (bytesStoreLiteSetChunkByteLongWordIndex I).toNat) * 8) < UInt256.size := by
    rw [show UInt256.size = 2 ^ 256 from rfl]
    calc (bytesStoreLiteSetChunkByteValueWord I).toNat *
            2 ^ ((31 - (bytesStoreLiteSetChunkByteLongWordIndex I).toNat) * 8) <
          256 * 2 ^ ((31 - (bytesStoreLiteSetChunkByteLongWordIndex I).toNat) * 8) :=
            Nat.mul_lt_mul_of_pos_right hv (by positivity)
        _ = 2 ^ (8 + (31 - (bytesStoreLiteSetChunkByteLongWordIndex I).toNat) * 8) := by
          rw [show 256 = 2 ^ 8 by norm_num, Nat.pow_add]
        _ ≤ 2 ^ 256 := by
          exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hrightLt : (((2 : Nat) ^ 256 - 1 -
        255 * 2 ^ ((31 - (bytesStoreLiteSetChunkByteLongWordIndex I).toNat) * 8)) &&&
        (bytesStoreLiteSetChunkByteLongOldWord σ I).toNat) < UInt256.size := by
    exact lt_of_le_of_lt Nat.and_le_right (bytesStoreLiteSetChunkByteLongOldWord σ I).val.isLt
  rw [Nat.mod_eq_of_lt hleftLt]
  change (bytesStoreLiteSetChunkByteLongOldWord σ I).toNat %
        2 ^ ((31 - (bytesStoreLiteSetChunkByteLongWordIndex I).toNat) * 8) +
      2 ^ ((31 - (bytesStoreLiteSetChunkByteLongWordIndex I).toNat) * 8) *
        (bytesStoreLiteSetChunkByteValueWord I).toNat +
      2 ^ (((31 - (bytesStoreLiteSetChunkByteLongWordIndex I).toNat) * 8) + 8) *
        ((bytesStoreLiteSetChunkByteLongOldWord σ I).toNat /
          2 ^ (((31 - (bytesStoreLiteSetChunkByteLongWordIndex I).toNat) * 8) + 8)) =
      ((bytesStoreLiteSetChunkByteValueWord I).toNat *
          2 ^ ((31 - (bytesStoreLiteSetChunkByteLongWordIndex I).toNat) * 8)).lor
        ((((2 : Nat) ^ 256 - 1 -
          255 * 2 ^ ((31 - (bytesStoreLiteSetChunkByteLongWordIndex I).toNat) * 8)) &&&
          (bytesStoreLiteSetChunkByteLongOldWord σ I).toNat) % UInt256.size) %
        UInt256.size
  rw [Nat.mod_eq_of_lt hrightLt]
  have hlorLt :
      ((bytesStoreLiteSetChunkByteValueWord I).toNat *
            2 ^ ((31 - (bytesStoreLiteSetChunkByteLongWordIndex I).toNat) * 8)).lor
          (((2 : Nat) ^ 256 - 1 -
              255 * 2 ^ ((31 - (bytesStoreLiteSetChunkByteLongWordIndex I).toNat) * 8)) &&&
            (bytesStoreLiteSetChunkByteLongOldWord σ I).toNat) < UInt256.size := by
    change ((bytesStoreLiteSetChunkByteValueWord I).toNat *
          2 ^ ((31 - (bytesStoreLiteSetChunkByteLongWordIndex I).toNat) * 8)) |||
        (((2 : Nat) ^ 256 - 1 -
            255 * 2 ^ ((31 - (bytesStoreLiteSetChunkByteLongWordIndex I).toNat) * 8)) &&&
          (bytesStoreLiteSetChunkByteLongOldWord σ I).toNat) < 2 ^ 256
    apply Nat.or_lt_two_pow
    · simpa [UInt256.size] using hleftLt
    · simpa [UInt256.size] using hrightLt
  rw [Nat.mod_eq_of_lt hlorLt]
  rw [show 2 ^ ((31 - (bytesStoreLiteSetChunkByteLongWordIndex I).toNat) * 8) *
        (bytesStoreLiteSetChunkByteValueWord I).toNat =
        (bytesStoreLiteSetChunkByteValueWord I).toNat *
          2 ^ ((31 - (bytesStoreLiteSetChunkByteLongWordIndex I).toNat) * 8) by ring]
  rw [show 2 ^ (((31 - (bytesStoreLiteSetChunkByteLongWordIndex I).toNat) * 8) + 8) *
        ((bytesStoreLiteSetChunkByteLongOldWord σ I).toNat /
          2 ^ (((31 - (bytesStoreLiteSetChunkByteLongWordIndex I).toNat) * 8) + 8)) =
      (bytesStoreLiteSetChunkByteLongOldWord σ I).toNat /
          2 ^ (((31 - (bytesStoreLiteSetChunkByteLongWordIndex I).toNat) * 8) + 8) *
        2 ^ (((31 - (bytesStoreLiteSetChunkByteLongWordIndex I).toNat) * 8) + 8) by ring]
  exact nat_byte_update_eq
    (old := (bytesStoreLiteSetChunkByteLongOldWord σ I).toNat)
    (v := (bytesStoreLiteSetChunkByteValueWord I).toNat)
    (k := (31 - (bytesStoreLiteSetChunkByteLongWordIndex I).toNat) * 8)
    hv hk (by exact (bytesStoreLiteSetChunkByteLongOldWord σ I).val.isLt)

theorem bytesStoreLiteSetChunkByteShortScale_mod256_zero {I : ExecutionEnv} {len : UInt256}
    (hshort : len.toNat < 32)
    (hbound : (bytesStoreLiteSetChunkByteIndexWord I).toNat < len.toNat) :
    (bytesStoreLiteSetChunkByteShortScale I).toNat % 256 = 0 := by
  have hidx : (bytesStoreLiteSetChunkByteIndexWord I).toNat < 31 :=
    bytesStoreLiteSetChunkByteIndex_lt31_of_short_bound hshort hbound
  interval_cases hnat : (bytesStoreLiteSetChunkByteIndexWord I).toNat
  all_goals
    have hword : bytesStoreLiteSetChunkByteIndexWord I =
        UInt256.ofNat (bytesStoreLiteSetChunkByteIndexWord I).toNat := by
      exact (u256_ofNat_toNat (bytesStoreLiteSetChunkByteIndexWord I)).symm
    rw [bytesStoreLiteSetChunkByteShortScale, hword, hnat]
    native_decide

theorem bytesStoreLiteSetChunkByteShortClearMask_mod256_255 {I : ExecutionEnv} {len : UInt256}
    (hshort : len.toNat < 32)
    (hbound : (bytesStoreLiteSetChunkByteIndexWord I).toNat < len.toNat) :
    (UInt256.lnot (UInt256.mul ⟨255⟩ (bytesStoreLiteSetChunkByteShortScale I))).toNat % 256 =
      255 := by
  have hidx : (bytesStoreLiteSetChunkByteIndexWord I).toNat < 31 :=
    bytesStoreLiteSetChunkByteIndex_lt31_of_short_bound hshort hbound
  interval_cases hnat : (bytesStoreLiteSetChunkByteIndexWord I).toNat
  all_goals
    have hword : bytesStoreLiteSetChunkByteIndexWord I =
        UInt256.ofNat (bytesStoreLiteSetChunkByteIndexWord I).toNat := by
      exact (u256_ofNat_toNat (bytesStoreLiteSetChunkByteIndexWord I)).symm
    rw [bytesStoreLiteSetChunkByteShortScale, hword, hnat]
    native_decide

theorem bytesStoreLiteSetChunkByteShortStoredWord_mod256
    {σ : AccountMap} {I : ExecutionEnv} {len : UInt256}
    (hshort : len.toNat < 32)
    (hbound : (bytesStoreLiteSetChunkByteIndexWord I).toNat < len.toNat) :
    (bytesStoreLiteSetChunkByteShortStoredWord σ I).toNat % 256 =
      (bytesStoreLiteSetChunkByteHeaderWord σ I).toNat % 256 := by
  have hscale := bytesStoreLiteSetChunkByteShortScale_mod256_zero
    (I := I) (len := len) hshort hbound
  have hmask := bytesStoreLiteSetChunkByteShortClearMask_mod256_255
    (I := I) (len := len) hshort hbound
  have hleft :
      (UInt256.mul
        (UInt256.div (UInt256.shiftLeft (bytesStoreLiteSetChunkByteValueWord I) ⟨248⟩)
          (UInt256.shiftLeft ⟨1⟩ ⟨248⟩))
        (bytesStoreLiteSetChunkByteShortScale I)).toNat % 256 = 0 := by
    rw [u256_mul_toNat, nat_mod_u256_mod_256, Nat.mul_mod, hscale]
    simp
  have hright :
      (UInt256.land
        (UInt256.lnot (UInt256.mul ⟨255⟩ (bytesStoreLiteSetChunkByteShortScale I)))
        (bytesStoreLiteSetChunkByteHeaderWord σ I)).toNat % 256 =
        (bytesStoreLiteSetChunkByteHeaderWord σ I).toNat % 256 := by
    rw [u256_land_toNat, nat_mod_u256_mod_256]
    exact nat_land_mod_256_of_left_255 hmask
  rw [bytesStoreLiteSetChunkByteShortStoredWord, u256_lor_toNat, nat_mod_u256_mod_256]
  rw [nat_lor_mod_256_of_left_zero hleft, hright]

theorem bytesStoreLiteSetChunkByteShortStoredWord_flag_eq
    {σ : AccountMap} {I : ExecutionEnv} {len : UInt256}
    (hshort : len.toNat < 32)
    (hbound : (bytesStoreLiteSetChunkByteIndexWord I).toNat < len.toNat) :
    UInt256.land (bytesStoreLiteSetChunkByteShortStoredWord σ I) ⟨1⟩ =
      UInt256.land (bytesStoreLiteSetChunkByteHeaderWord σ I) ⟨1⟩ := by
  apply u256_inj
  rw [uInt256_land_one_toNat, uInt256_land_one_toNat]
  have hmod := bytesStoreLiteSetChunkByteShortStoredWord_mod256
    (σ := σ) (I := I) (len := len) hshort hbound
  have hleft :
      (bytesStoreLiteSetChunkByteShortStoredWord σ I).toNat % 2 =
        ((bytesStoreLiteSetChunkByteShortStoredWord σ I).toNat % 256) % 2 := by
    rw [Nat.mod_mod_of_dvd]
    norm_num
  have hright :
      (bytesStoreLiteSetChunkByteHeaderWord σ I).toNat % 2 =
        ((bytesStoreLiteSetChunkByteHeaderWord σ I).toNat % 256) % 2 := by
    rw [Nat.mod_mod_of_dvd]
    norm_num
  rw [hleft, hright, hmod]

theorem bytesStoreLiteSetChunkByteShortStoredWord_shortLen_eq
    {σ : AccountMap} {I : ExecutionEnv} {len : UInt256}
    (hshort : len.toNat < 32)
    (hbound : (bytesStoreLiteSetChunkByteIndexWord I).toNat < len.toNat) :
    UInt256.land (UInt256.div (bytesStoreLiteSetChunkByteShortStoredWord σ I) ⟨2⟩) ⟨127⟩ =
      UInt256.land (UInt256.div (bytesStoreLiteSetChunkByteHeaderWord σ I) ⟨2⟩) ⟨127⟩ := by
  apply u256_inj
  rw [bytesStoreLiteShortLenBits_toNat, bytesStoreLiteShortLenBits_toNat]
  rw [bytesStoreLiteSetChunkByteShortStoredWord_mod256 (σ := σ) (I := I) (len := len)
    hshort hbound]

theorem bytesStoreLiteSetChunkByteStorageLocStoreShort
    {evm : EVM.State} {σ : AccountMap} {I : ExecutionEnv} {len : UInt256}
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (bytesStoreLiteSetChunkByteSlot I) = bytesStoreLiteSetChunkByteHeaderWord σ I)
    (hcanon : (bytesStoreLiteSetChunkByteValueWord I).toNat < EVM.twoPow 8)
    (hshort : len.toNat < 32)
    (hbound : (bytesStoreLiteSetChunkByteIndexWord I).toNat < len.toNat) :
    storageLocStore evm
      (uint8Loc (bytesStoreLiteSetChunkByteSlot I)
        ⟨31 - (bytesStoreLiteSetChunkByteIndexWord I).toNat, by
          have hidx := bytesStoreLiteSetChunkByteIndex_lt31_of_short_bound
            (I := I) (len := len) hshort hbound
          omega⟩)
      (bytesStoreLiteSetChunkByteValue I) =
      some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner
        (bytesStoreLiteSetChunkByteSlot I)
        (bytesStoreLiteSetChunkByteShortStoredWord σ I)) := by
  let offFin : Fin 32 :=
    ⟨31 - (bytesStoreLiteSetChunkByteIndexWord I).toNat, by
      have hidx := bytesStoreLiteSetChunkByteIndex_lt31_of_short_bound
        (I := I) (len := len) hshort hbound
      omega⟩
  have hbyte : (bytesStoreLiteSetChunkByteValueWord I).toNat < 256 := by
    simpa [EVM.twoPow] using hcanon
  have hoffBound : offFin.val + (1 : Fin 33).val - 1 < 32 := by
    have hidx := bytesStoreLiteSetChunkByteIndex_lt31_of_short_bound
      (I := I) (len := len) hshort hbound
    simp [offFin]
    omega
  have htarget :
      (bytesStoreLiteSetChunkByteShortStoredWord σ I).toNat =
        (bytesStoreLiteSetChunkByteHeaderWord σ I).toNat % 2 ^ (8 * offFin.val) +
          2 ^ (8 * offFin.val) * (bytesStoreLiteSetChunkByteValueWord I).toNat +
          2 ^ (8 * offFin.val + 8) *
            ((bytesStoreLiteSetChunkByteHeaderWord σ I).toNat /
              2 ^ (8 * offFin.val + 8)) := by
    change
      (bytesStoreLiteSetChunkByteShortStoredWord σ I).toNat =
        (bytesStoreLiteSetChunkByteHeaderWord σ I).toNat %
            2 ^ (8 * (31 - (bytesStoreLiteSetChunkByteIndexWord I).toNat)) +
          2 ^ (8 * (31 - (bytesStoreLiteSetChunkByteIndexWord I).toNat)) *
            (bytesStoreLiteSetChunkByteValueWord I).toNat +
          2 ^ (8 * (31 - (bytesStoreLiteSetChunkByteIndexWord I).toNat) + 8) *
            ((bytesStoreLiteSetChunkByteHeaderWord σ I).toNat /
              2 ^ (8 * (31 - (bytesStoreLiteSetChunkByteIndexWord I).toNat) + 8))
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
      (bytesStoreLiteSetChunkByteShortStoredWord_toNat_update
        (σ := σ) (I := I) (len := len) hcanon hshort hbound).symm
  change storageLocStore evm
      { slot := bytesStoreLiteSetChunkByteSlot I, offset := offFin, size := 1,
        hbound := hoffBound, type := .int uint8Int }
      (bytesStoreLiteSetChunkByteValue I) =
      some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner
        (bytesStoreLiteSetChunkByteSlot I)
        (bytesStoreLiteSetChunkByteShortStoredWord σ I))
  exact storageLocStore_oneByte_int_ofNat_update evm
    (bytesStoreLiteSetChunkByteSlot I) (bytesStoreLiteSetChunkByteHeaderWord σ I)
    (bytesStoreLiteSetChunkByteShortStoredWord σ I) offFin (.int uint8Int) hoffBound
    (bytesStoreLiteSetChunkByteValueWord I).toNat hload hbyte htarget

theorem bytesStoreLiteSetChunkByteStorageLocStoreLong
    {evm : EVM.State} {σ : AccountMap} {I : ExecutionEnv}
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (bytesStoreLiteSetChunkByteLongDataSlot I) =
      bytesStoreLiteSetChunkByteLongOldWord σ I)
    (hcanon : (bytesStoreLiteSetChunkByteValueWord I).toNat < EVM.twoPow 8) :
    storageLocStore evm
      (uint8Loc (bytesStoreLiteSetChunkByteLongDataSlot I)
        ⟨31 - (bytesStoreLiteSetChunkByteLongWordIndex I).toNat, by
          have hidx := bytesStoreLiteSetChunkByteLongWordIndex_lt32 I
          omega⟩)
      (bytesStoreLiteSetChunkByteValue I) =
      some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner
        (bytesStoreLiteSetChunkByteLongDataSlot I)
        (bytesStoreLiteSetChunkByteLongStoredWord σ I)) := by
  let offFin : Fin 32 :=
    ⟨31 - (bytesStoreLiteSetChunkByteLongWordIndex I).toNat, by
      have hidx := bytesStoreLiteSetChunkByteLongWordIndex_lt32 I
      omega⟩
  have hbyte : (bytesStoreLiteSetChunkByteValueWord I).toNat < 256 := by
    simpa [EVM.twoPow] using hcanon
  have hoffBound : offFin.val + (1 : Fin 33).val - 1 < 32 := by
    simp [offFin]
    omega
  have htarget :
      (bytesStoreLiteSetChunkByteLongStoredWord σ I).toNat =
        (bytesStoreLiteSetChunkByteLongOldWord σ I).toNat % 2 ^ (8 * offFin.val) +
          2 ^ (8 * offFin.val) * (bytesStoreLiteSetChunkByteValueWord I).toNat +
          2 ^ (8 * offFin.val + 8) *
            ((bytesStoreLiteSetChunkByteLongOldWord σ I).toNat /
              2 ^ (8 * offFin.val + 8)) := by
    change
      (bytesStoreLiteSetChunkByteLongStoredWord σ I).toNat =
        (bytesStoreLiteSetChunkByteLongOldWord σ I).toNat %
            2 ^ (8 * (31 - (bytesStoreLiteSetChunkByteLongWordIndex I).toNat)) +
          2 ^ (8 * (31 - (bytesStoreLiteSetChunkByteLongWordIndex I).toNat)) *
            (bytesStoreLiteSetChunkByteValueWord I).toNat +
          2 ^ (8 * (31 - (bytesStoreLiteSetChunkByteLongWordIndex I).toNat) + 8) *
            ((bytesStoreLiteSetChunkByteLongOldWord σ I).toNat /
              2 ^ (8 * (31 - (bytesStoreLiteSetChunkByteLongWordIndex I).toNat) + 8))
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
      (bytesStoreLiteSetChunkByteLongStoredWord_toNat_update
        (σ := σ) (I := I) hcanon).symm
  change storageLocStore evm
      { slot := bytesStoreLiteSetChunkByteLongDataSlot I, offset := offFin, size := 1,
        hbound := hoffBound, type := .int uint8Int }
      (bytesStoreLiteSetChunkByteValue I) =
      some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner
        (bytesStoreLiteSetChunkByteLongDataSlot I)
        (bytesStoreLiteSetChunkByteLongStoredWord σ I))
  exact storageLocStore_oneByte_int_ofNat_update evm
    (bytesStoreLiteSetChunkByteLongDataSlot I) (bytesStoreLiteSetChunkByteLongOldWord σ I)
    (bytesStoreLiteSetChunkByteLongStoredWord σ I) offFin (.int uint8Int) hoffBound
    (bytesStoreLiteSetChunkByteValueWord I).toNat hload hbyte htarget

theorem bytesStoreLiteSetChunkByteEvalStorageRefOfLength {evm : EVM.State}
    {I : ExecutionEnv} {chunksLen : UInt256} {len : Nat}
    (hload :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩ = chunksLen)
    (hchunkBound :
      (bytesStoreLiteSetChunkByteChunkIndexWord I).toNat < chunksLen.toNat)
    (hlen : readStorageBytesLength? bytesStoreLiteConfig evm
      (bytesStoreLiteSetChunkByteHeaderRef I) = .ok len)
    (hbound : (bytesStoreLiteSetChunkByteIndexWord I).toNat < len) :
    evalStorageRef bytesStoreLiteConfig
      (bytesStoreLiteSetChunkByteFrame I)
      evm (chunkByteRef (.var "chunkIndex") (.var "byteIndex")) =
        .ok (bytesStoreLiteSetChunkByteRef I) := by
  have hgetChunkIndex :
      (bytesStoreLiteSetChunkByteFrame I).locals.get? "chunkIndex" =
        some (.int (Int.ofNat (bytesStoreLiteSetChunkByteChunkIndexWord I).toNat)) := by
    simpa [bytesStoreLiteSetChunkByteFrame] using
      bytesStoreLiteSetChunkByteLocals_get_chunkIndex I
  have hgetByteIndex :
      (bytesStoreLiteSetChunkByteFrame I).locals.get? "byteIndex" =
        some (.int (Int.ofNat (bytesStoreLiteSetChunkByteIndexWord I).toNat)) := by
    simpa [bytesStoreLiteSetChunkByteFrame] using
      bytesStoreLiteSetChunkByteLocals_get_byteIndex I
  have hgetChunkIndexElem :
      (bytesStoreLiteSetChunkByteLocals I)["chunkIndex"]? =
        some (.int (Int.ofNat (bytesStoreLiteSetChunkByteChunkIndexWord I).toNat)) :=
    bytesStoreLiteSetChunkByteLocals_getElem_chunkIndex I
  have hindexKey :
      valueToKey? (.int (Int.ofNat (bytesStoreLiteSetChunkByteIndexWord I).toNat)) =
        some (.int (Int.ofNat (bytesStoreLiteSetChunkByteIndexWord I).toNat)) := by
    simp [valueToKey?]
  have hlen' :
      readStorageBytesLength?
        { storage := bytesStoreLiteStorageLayout, externalABI := defaultExternalCallABI,
          selfDeployment := genSolidityConstructorDeployment [] }
        evm (bytesStoreLiteSetChunkByteHeaderRef I) = .ok len := by
    simpa [bytesStoreLiteConfig] using hlen
  let headerRef : EvaledStorageRef :=
    { base := "chunks"
      steps := [.aindex
        (.int ((bytesStoreLiteSetChunkByteChunkIndexWord I).toNat : Int))] }
  have hlenHeader :
      readStorageBytesLength?
        { storage := bytesStoreLiteStorageLayout, externalABI := defaultExternalCallABI,
          selfDeployment := genSolidityConstructorDeployment [] }
        evm headerRef = .ok len := by
    simpa [headerRef, bytesStoreLiteSetChunkByteHeaderRef] using hlen'
  simp only [headerRef, bytesStoreLiteStorageLayout, solidityStorageLayout] at hlenHeader
  have hstep :
      evalStorageRefStep bytesStoreLiteConfig (bytesStoreLiteSetChunkByteFrame I) evm
        "chunks" [] (.aindex (.var "chunkIndex")) =
        .ok (.aindex (.int (Int.ofNat (bytesStoreLiteSetChunkByteChunkIndexWord I).toNat))) := by
    simp [evalStorageRefStep, evalExpr?, bytesStoreLiteSetChunkByteFrame,
      hgetChunkIndexElem, valueToKey?, EvalResult.ofOption, EvalResult.bind, bind, pure,
      arrayIndexInBounds?, storageTypeAt?, bytesStoreLiteConfig, bytesStoreLiteContract,
      storageDecls, bytesSt, bytesStoreLiteStorageLayout, solidityStorageLayout,
      bytesStoreLiteLayout, bytesStoreLiteStorageLocLoad_uint256, hload, hchunkBound]
  have hbounds :
      arrayIndexInBounds? bytesStoreLiteConfig evm
        (bytesStoreLiteSetChunkByteFrame I).contract.storage "chunks"
        [.aindex (.int (Int.ofNat (bytesStoreLiteSetChunkByteChunkIndexWord I).toNat))]
        (.int (Int.ofNat (bytesStoreLiteSetChunkByteIndexWord I).toNat)) = .ok () := by
    simp [arrayIndexInBounds?, storageTypeAt?, bytesStoreLiteConfig, bytesStoreLiteSetChunkByteFrame,
      bytesStoreLiteContract, storageDecls, storageTypeStep?, bytesSt, bytesStoreLiteStorageLayout,
      solidityStorageLayout, hlenHeader, hbound]
  simpa [chunkByteRef, bytesStoreLiteSetChunkByteRef] using
    (evalStorageRef_step_aindex_var_of_get?_ok
      (cfg := bytesStoreLiteConfig) (solm := bytesStoreLiteSetChunkByteFrame I) (evm := evm)
      (base := "chunks") (name := "byteIndex") (step := .aindex (.var "chunkIndex"))
      (estep := .aindex (.int (Int.ofNat (bytesStoreLiteSetChunkByteChunkIndexWord I).toNat)))
      hstep hgetByteIndex hindexKey hbounds)

theorem bytesStoreLiteSetChunkByteEvalStorageRefRevertsOfLength {evm : EVM.State}
    {I : ExecutionEnv} {chunksLen : UInt256} {len : Nat}
    (hload :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩ = chunksLen)
    (hchunkBound :
      (bytesStoreLiteSetChunkByteChunkIndexWord I).toNat < chunksLen.toNat)
    (hlen : readStorageBytesLength? bytesStoreLiteConfig evm
      (bytesStoreLiteSetChunkByteHeaderRef I) = .ok len)
    (hbound : ¬ (bytesStoreLiteSetChunkByteIndexWord I).toNat < len) :
    evalStorageRef bytesStoreLiteConfig
      (bytesStoreLiteSetChunkByteFrame I)
      evm (chunkByteRef (.var "chunkIndex") (.var "byteIndex")) = .revert := by
  have hgetChunkIndex :
      (bytesStoreLiteSetChunkByteFrame I).locals.get? "chunkIndex" =
        some (.int (Int.ofNat (bytesStoreLiteSetChunkByteChunkIndexWord I).toNat)) := by
    simpa [bytesStoreLiteSetChunkByteFrame] using
      bytesStoreLiteSetChunkByteLocals_get_chunkIndex I
  have hgetByteIndex :
      (bytesStoreLiteSetChunkByteFrame I).locals.get? "byteIndex" =
        some (.int (Int.ofNat (bytesStoreLiteSetChunkByteIndexWord I).toNat)) := by
    simpa [bytesStoreLiteSetChunkByteFrame] using
      bytesStoreLiteSetChunkByteLocals_get_byteIndex I
  have hgetChunkIndexElem :
      (bytesStoreLiteSetChunkByteLocals I)["chunkIndex"]? =
        some (.int (Int.ofNat (bytesStoreLiteSetChunkByteChunkIndexWord I).toNat)) :=
    bytesStoreLiteSetChunkByteLocals_getElem_chunkIndex I
  have hindexKey :
      valueToKey? (.int (Int.ofNat (bytesStoreLiteSetChunkByteIndexWord I).toNat)) =
        some (.int (Int.ofNat (bytesStoreLiteSetChunkByteIndexWord I).toNat)) := by
    simp [valueToKey?]
  have hlen' :
      readStorageBytesLength?
        { storage := bytesStoreLiteStorageLayout, externalABI := defaultExternalCallABI,
          selfDeployment := genSolidityConstructorDeployment [] }
        evm (bytesStoreLiteSetChunkByteHeaderRef I) = .ok len := by
    simpa [bytesStoreLiteConfig] using hlen
  let headerRef : EvaledStorageRef :=
    { base := "chunks"
      steps := [.aindex
        (.int ((bytesStoreLiteSetChunkByteChunkIndexWord I).toNat : Int))] }
  have hlenHeader :
      readStorageBytesLength?
        { storage := bytesStoreLiteStorageLayout, externalABI := defaultExternalCallABI,
          selfDeployment := genSolidityConstructorDeployment [] }
        evm headerRef = .ok len := by
    simpa [headerRef, bytesStoreLiteSetChunkByteHeaderRef] using hlen'
  simp only [headerRef, bytesStoreLiteStorageLayout, solidityStorageLayout] at hlenHeader
  have hstep :
      evalStorageRefStep bytesStoreLiteConfig (bytesStoreLiteSetChunkByteFrame I) evm
        "chunks" [] (.aindex (.var "chunkIndex")) =
        .ok (.aindex (.int (Int.ofNat (bytesStoreLiteSetChunkByteChunkIndexWord I).toNat))) := by
    simp [evalStorageRefStep, evalExpr?, bytesStoreLiteSetChunkByteFrame,
      hgetChunkIndexElem, valueToKey?, EvalResult.ofOption, EvalResult.bind, bind, pure,
      arrayIndexInBounds?, storageTypeAt?, bytesStoreLiteConfig, bytesStoreLiteContract,
      storageDecls, bytesSt, bytesStoreLiteStorageLayout, solidityStorageLayout,
      bytesStoreLiteLayout, bytesStoreLiteStorageLocLoad_uint256, hload, hchunkBound]
  have hbounds :
      arrayIndexInBounds? bytesStoreLiteConfig evm
        (bytesStoreLiteSetChunkByteFrame I).contract.storage "chunks"
        [.aindex (.int (Int.ofNat (bytesStoreLiteSetChunkByteChunkIndexWord I).toNat))]
        (.int (Int.ofNat (bytesStoreLiteSetChunkByteIndexWord I).toNat)) = .revert := by
    simp [arrayIndexInBounds?, storageTypeAt?, bytesStoreLiteConfig, bytesStoreLiteSetChunkByteFrame,
      bytesStoreLiteContract, storageDecls, storageTypeStep?, bytesSt, bytesStoreLiteStorageLayout,
      solidityStorageLayout, hlenHeader, hbound]
  simpa [chunkByteRef] using
    (evalStorageRef_step_aindex_var_of_get?_revert
      (cfg := bytesStoreLiteConfig) (solm := bytesStoreLiteSetChunkByteFrame I) (evm := evm)
      (base := "chunks") (name := "byteIndex") (step := .aindex (.var "chunkIndex"))
      (estep := .aindex (.int (Int.ofNat (bytesStoreLiteSetChunkByteChunkIndexWord I).toNat)))
      hstep hgetByteIndex hindexKey hbounds)

theorem bytesStoreLiteSetChunkByteEvalStorageRefRevertsOfLengthRead {evm : EVM.State}
    {I : ExecutionEnv} {chunksLen : UInt256}
    (hload :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩ = chunksLen)
    (hchunkBound :
      (bytesStoreLiteSetChunkByteChunkIndexWord I).toNat < chunksLen.toNat)
    (hlen : readStorageBytesLength? bytesStoreLiteConfig evm
      (bytesStoreLiteSetChunkByteHeaderRef I) = .revert) :
    evalStorageRef bytesStoreLiteConfig
      (bytesStoreLiteSetChunkByteFrame I)
      evm (chunkByteRef (.var "chunkIndex") (.var "byteIndex")) = .revert := by
  have hgetChunkIndex :
      (bytesStoreLiteSetChunkByteFrame I).locals.get? "chunkIndex" =
        some (.int (Int.ofNat (bytesStoreLiteSetChunkByteChunkIndexWord I).toNat)) := by
    simpa [bytesStoreLiteSetChunkByteFrame] using
      bytesStoreLiteSetChunkByteLocals_get_chunkIndex I
  have hgetByteIndex :
      (bytesStoreLiteSetChunkByteFrame I).locals.get? "byteIndex" =
        some (.int (Int.ofNat (bytesStoreLiteSetChunkByteIndexWord I).toNat)) := by
    simpa [bytesStoreLiteSetChunkByteFrame] using
      bytesStoreLiteSetChunkByteLocals_get_byteIndex I
  have hgetChunkIndexElem :
      (bytesStoreLiteSetChunkByteLocals I)["chunkIndex"]? =
        some (.int (Int.ofNat (bytesStoreLiteSetChunkByteChunkIndexWord I).toNat)) :=
    bytesStoreLiteSetChunkByteLocals_getElem_chunkIndex I
  have hindexKey :
      valueToKey? (.int (Int.ofNat (bytesStoreLiteSetChunkByteIndexWord I).toNat)) =
        some (.int (Int.ofNat (bytesStoreLiteSetChunkByteIndexWord I).toNat)) := by
    simp [valueToKey?]
  have hlen' :
      readStorageBytesLength?
        { storage := bytesStoreLiteStorageLayout, externalABI := defaultExternalCallABI,
          selfDeployment := genSolidityConstructorDeployment [] }
        evm (bytesStoreLiteSetChunkByteHeaderRef I) = .revert := by
    simpa [bytesStoreLiteConfig] using hlen
  let headerRef : EvaledStorageRef :=
    { base := "chunks"
      steps := [.aindex
        (.int ((bytesStoreLiteSetChunkByteChunkIndexWord I).toNat : Int))] }
  have hlenHeader :
      readStorageBytesLength?
        { storage := bytesStoreLiteStorageLayout, externalABI := defaultExternalCallABI,
          selfDeployment := genSolidityConstructorDeployment [] }
        evm headerRef = .revert := by
    simpa [headerRef, bytesStoreLiteSetChunkByteHeaderRef] using hlen'
  simp only [headerRef, bytesStoreLiteStorageLayout, solidityStorageLayout] at hlenHeader
  have hstep :
      evalStorageRefStep bytesStoreLiteConfig (bytesStoreLiteSetChunkByteFrame I) evm
        "chunks" [] (.aindex (.var "chunkIndex")) =
        .ok (.aindex (.int (Int.ofNat (bytesStoreLiteSetChunkByteChunkIndexWord I).toNat))) := by
    simp [evalStorageRefStep, evalExpr?, bytesStoreLiteSetChunkByteFrame,
      hgetChunkIndexElem, valueToKey?, EvalResult.ofOption, EvalResult.bind, bind, pure,
      arrayIndexInBounds?, storageTypeAt?, bytesStoreLiteConfig, bytesStoreLiteContract,
      storageDecls, bytesSt, bytesStoreLiteStorageLayout, solidityStorageLayout,
      bytesStoreLiteLayout, bytesStoreLiteStorageLocLoad_uint256, hload, hchunkBound]
  have hbounds :
      arrayIndexInBounds? bytesStoreLiteConfig evm
        (bytesStoreLiteSetChunkByteFrame I).contract.storage "chunks"
        [.aindex (.int (Int.ofNat (bytesStoreLiteSetChunkByteChunkIndexWord I).toNat))]
        (.int (Int.ofNat (bytesStoreLiteSetChunkByteIndexWord I).toNat)) = .revert := by
    simp [arrayIndexInBounds?, storageTypeAt?, bytesStoreLiteConfig, bytesStoreLiteSetChunkByteFrame,
      bytesStoreLiteContract, storageDecls, storageTypeStep?, bytesSt, bytesStoreLiteStorageLayout,
      solidityStorageLayout, hlenHeader]
  simpa [chunkByteRef] using
    (evalStorageRef_step_aindex_var_of_get?_revert
      (cfg := bytesStoreLiteConfig) (solm := bytesStoreLiteSetChunkByteFrame I) (evm := evm)
      (base := "chunks") (name := "byteIndex") (step := .aindex (.var "chunkIndex"))
      (estep := .aindex (.int (Int.ofNat (bytesStoreLiteSetChunkByteChunkIndexWord I).toNat)))
      hstep hgetByteIndex hindexKey hbounds)

theorem bytesStoreLiteSetChunkByteEvalStorageRefRevertsOfChunksLength {evm : EVM.State}
    {I : ExecutionEnv} {chunksLen : UInt256}
    (hload :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩ = chunksLen)
    (hbound :
      ¬ (bytesStoreLiteSetChunkByteChunkIndexWord I).toNat < chunksLen.toNat) :
    evalStorageRef bytesStoreLiteConfig
      (bytesStoreLiteSetChunkByteFrame I)
      evm (chunkByteRef (.var "chunkIndex") (.var "byteIndex")) = .revert := by
  have hgetIndexElem :
      (bytesStoreLiteSetChunkByteLocals I)["chunkIndex"]? =
        some (.int (Int.ofNat (bytesStoreLiteSetChunkByteChunkIndexWord I).toNat)) :=
    bytesStoreLiteSetChunkByteLocals_getElem_chunkIndex I
  have hstep :
      evalStorageRefStep bytesStoreLiteConfig (bytesStoreLiteSetChunkByteFrame I) evm
        "chunks" [] (.aindex (.var "chunkIndex")) = .revert := by
    simp [evalStorageRefStep, evalExpr?, bytesStoreLiteSetChunkByteFrame, hgetIndexElem,
      valueToKey?, EvalResult.ofOption, EvalResult.bind, bind, pure, arrayIndexInBounds?,
      storageTypeAt?, bytesStoreLiteConfig, bytesStoreLiteContract, storageDecls, bytesSt,
      bytesStoreLiteStorageLayout, solidityStorageLayout, bytesStoreLiteLayout,
      bytesStoreLiteStorageLocLoad_uint256, hload, hbound]
  simpa [chunkByteRef] using
    (evalStorageRef_step_revert
      (cfg := bytesStoreLiteConfig) (solm := bytesStoreLiteSetChunkByteFrame I) (evm := evm)
      (base := "chunks") (step := .aindex (.var "chunkIndex"))
      (rest := [.aindex (.var "byteIndex")]) hstep)

theorem bytesStoreLiteSetChunkByteBodyReturns {evm evm' : EVM.State} {I : ExecutionEnv}
    {ret : Value}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hassign :
      assignStorageRef? bytesStoreLiteConfig
        (bytesStoreLiteSetChunkByteFrame I)
        evm .storage (chunkByteRef (.var "chunkIndex") (.var "byteIndex"))
          (bytesStoreLiteSetChunkByteValue I) =
          .ok (bytesStoreLiteSetChunkByteFrame I, evm'))
    (hret :
      evalExpr? bytesStoreLiteConfig
        (bytesStoreLiteSetChunkByteFrame I)
        evm' (.storage (chunkByteRef (.var "chunkIndex") (.var "byteIndex"))) = .ok ret) :
    ExecTransitionBody bytesStoreLiteConfig bytesStoreLiteContract evm
      (bytesStoreLiteSetChunkByteLocals I) setChunkByteTransition.body
      (.returned
        (bytesStoreLiteSetChunkByteFrame I)
        evm' (some ret)) := by
  let solm : Frame := bytesStoreLiteSetChunkByteFrame I
  have hvalue :
      evalExpr? bytesStoreLiteConfig solm evm (.var "value") =
        .ok (bytesStoreLiteSetChunkByteValue I) := by
    exact evalExpr_var_of_get? (by
      simp [solm, bytesStoreLiteSetChunkByteFrame, bytesStoreLiteSetChunkByteValue,
        bytesStoreLiteSetChunkByteLocals])
  have hassign :
      assignStorageRef? bytesStoreLiteConfig solm evm .storage
        (chunkByteRef (.var "chunkIndex") (.var "byteIndex"))
          (bytesStoreLiteSetChunkByteValue I) =
          .ok (solm, evm') := by
    simpa [solm] using hassign
  have hret :
      evalExpr? bytesStoreLiteConfig solm evm'
        (.storage (chunkByteRef (.var "chunkIndex") (.var "byteIndex"))) = .ok ret := by
    simpa [solm] using hret
  exact ExecFuncBody.execBlockRet <|
    ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consNormal (ExecStmt.assign hvalue hassign) <|
        ExecBlock.consReturn (ExecStmt.return hret)

theorem bytesStoreLiteSetChunkByteBodyReturnReverts {evm evm' : EVM.State} {I : ExecutionEnv}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hassign :
      assignStorageRef? bytesStoreLiteConfig
        (bytesStoreLiteSetChunkByteFrame I)
        evm .storage (chunkByteRef (.var "chunkIndex") (.var "byteIndex"))
          (bytesStoreLiteSetChunkByteValue I) =
          .ok (bytesStoreLiteSetChunkByteFrame I, evm'))
    (hret :
      evalExpr? bytesStoreLiteConfig
        (bytesStoreLiteSetChunkByteFrame I)
        evm' (.storage (chunkByteRef (.var "chunkIndex") (.var "byteIndex"))) = .revert) :
    ExecTransitionBody bytesStoreLiteConfig bytesStoreLiteContract evm
      (bytesStoreLiteSetChunkByteLocals I) setChunkByteTransition.body .reverted := by
  let solm : Frame := bytesStoreLiteSetChunkByteFrame I
  have hvalue :
      evalExpr? bytesStoreLiteConfig solm evm (.var "value") =
        .ok (bytesStoreLiteSetChunkByteValue I) := by
    exact evalExpr_var_of_get? (by
      simp [solm, bytesStoreLiteSetChunkByteFrame, bytesStoreLiteSetChunkByteValue,
        bytesStoreLiteSetChunkByteLocals])
  have hassign :
      assignStorageRef? bytesStoreLiteConfig solm evm .storage
        (chunkByteRef (.var "chunkIndex") (.var "byteIndex"))
          (bytesStoreLiteSetChunkByteValue I) =
          .ok (solm, evm') := by
    simpa [solm] using hassign
  have hret :
      evalExpr? bytesStoreLiteConfig solm evm'
        (.storage (chunkByteRef (.var "chunkIndex") (.var "byteIndex"))) = .revert := by
    simpa [solm] using hret
  exact ExecFuncBody.execBlockRevert <|
    ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consNormal (ExecStmt.assign hvalue hassign) <|
        ExecBlock.consRevert (ExecStmt.returnRevert hret)

theorem bytesStoreLiteSetChunkByteResolveOfLength {evm : EVM.State} {I : ExecutionEnv}
    {chunksLen : UInt256} {len : Nat}
    (hload :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩ = chunksLen)
    (hchunkBound :
      (bytesStoreLiteSetChunkByteChunkIndexWord I).toNat < chunksLen.toNat)
    (hlen : readStorageBytesLength? bytesStoreLiteConfig evm
      (bytesStoreLiteSetChunkByteHeaderRef I) = .ok len)
    (hbound : (bytesStoreLiteSetChunkByteIndexWord I).toNat < len) :
    resolveStorageRef? bytesStoreLiteConfig
      (bytesStoreLiteSetChunkByteFrame I)
      evm (chunkByteRef (.var "chunkIndex") (.var "byteIndex")) =
        .ok (bytesStoreLiteSetChunkByteRef I, uint8St) := by
  have hgetChunks :
      (bytesStoreLiteSetChunkByteLocals I).get? "chunks" = none :=
    bytesStoreLiteSetChunkByteLocals_get_chunks_none I
  let sourceRef : StorageRef :=
    { base := "chunks"
      steps := [.aindex (.var "chunkIndex"), .aindex (.var "byteIndex")] }
  have herInline' :
      evalStorageRef bytesStoreLiteConfig
        ({ contract := bytesStoreLiteContract, locals := bytesStoreLiteSetChunkByteLocals I } :
          Frame)
        evm sourceRef =
          .ok (bytesStoreLiteSetChunkByteRef I) := by
    simpa [sourceRef, chunkByteRef, bytesStoreLiteSetChunkByteFrame] using
      (bytesStoreLiteSetChunkByteEvalStorageRefOfLength
        (evm := evm) (I := I) (chunksLen := chunksLen) (len := len)
        hload hchunkBound hlen hbound)
  exact resolveStorageRef?_ok hgetChunks herInline'
    bytesStoreLiteSetChunkByte_storageTypeAt

theorem bytesStoreLiteSetChunkByteAssignOfLength {evm evm' : EVM.State}
    {I : ExecutionEnv} {chunksLen : UInt256} {len : Nat}
    (hload :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩ = chunksLen)
    (hchunkBound :
      (bytesStoreLiteSetChunkByteChunkIndexWord I).toNat < chunksLen.toNat)
    (hlen : readStorageBytesLength? bytesStoreLiteConfig evm
      (bytesStoreLiteSetChunkByteHeaderRef I) = .ok len)
    (hbound : (bytesStoreLiteSetChunkByteIndexWord I).toNat < len)
    (hstore :
      (match bytesStoreLiteConfig.storage.layout (bytesStoreLiteSetChunkByteRef I) evm with
      | some loc => storageLocStore evm loc (bytesStoreLiteSetChunkByteValue I)
      | none => none) = some evm') :
    assignStorageRef? bytesStoreLiteConfig
      (bytesStoreLiteSetChunkByteFrame I)
      evm .storage (chunkByteRef (.var "chunkIndex") (.var "byteIndex"))
        (bytesStoreLiteSetChunkByteValue I) =
        .ok (bytesStoreLiteSetChunkByteFrame I, evm') := by
  exact assignStorageRef_storage_scalar_ok_of_resolve_match_store
    (bytesStoreLiteSetChunkByteResolveOfLength (I := I) hload hchunkBound hlen hbound)
    hstore
    (by simp [bytesStoreLiteSetChunkByteValue])

theorem bytesStoreLiteSetChunkByteShortBodyReturns_of_post_readback
    {evm : EVM.State} {σ : AccountMap} {I : ExecutionEnv}
    {chunksLen chunksLenPost len : UInt256} {acc : Account}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hloadChunks : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩ = chunksLen)
    (hchunkBound : (bytesStoreLiteSetChunkByteChunkIndexWord I).toNat < chunksLen.toNat)
    (hloadChunksPost :
      Solm.EVM.storageLoad
          (Solm.EVM.storageStore evm evm.executionEnv.codeOwner
            (bytesStoreLiteSetChunkByteSlot I)
            (bytesStoreLiteSetChunkByteShortStoredWord σ I))
          evm.executionEnv.codeOwner ⟨1⟩ = chunksLenPost)
    (hchunkBoundPost :
      (bytesStoreLiteSetChunkByteChunkIndexWord I).toNat < chunksLenPost.toNat)
    (hloadHeader : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (bytesStoreLiteSetChunkByteSlot I) = bytesStoreLiteSetChunkByteHeaderWord σ I)
    (hacc : evm.accountMap.find? evm.executionEnv.codeOwner = some acc)
    (hcanon : (bytesStoreLiteSetChunkByteValueWord I).toNat < EVM.twoPow 8)
    (hlen : len =
      UInt256.land (UInt256.div (bytesStoreLiteSetChunkByteHeaderWord σ I) ⟨2⟩) ⟨127⟩)
    (hshort : len.toNat < 32)
    (hbound : (bytesStoreLiteSetChunkByteIndexWord I).toNat < len.toNat)
    (hflag : UInt256.land (bytesStoreLiteSetChunkByteHeaderWord σ I) ⟨1⟩ = ⟨0⟩)
    (_hvalid : UInt256.sub (UInt256.land (bytesStoreLiteSetChunkByteHeaderWord σ I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStoreLiteSetChunkByteHeaderWord σ I) ⟨2⟩) ⟨127⟩)
          ⟨32⟩) ≠ ⟨0⟩) :
    ExecTransitionBody bytesStoreLiteConfig bytesStoreLiteContract evm
      (bytesStoreLiteSetChunkByteLocals I) setChunkByteTransition.body
      (.returned
        (bytesStoreLiteSetChunkByteFrame I)
        (Solm.EVM.storageStore evm evm.executionEnv.codeOwner
          (bytesStoreLiteSetChunkByteSlot I)
          (bytesStoreLiteSetChunkByteShortStoredWord σ I))
        (some (bytesStoreLiteSetChunkByteValue I))) := by
  let evm' := Solm.EVM.storageStore evm evm.executionEnv.codeOwner
    (bytesStoreLiteSetChunkByteSlot I)
    (bytesStoreLiteSetChunkByteShortStoredWord σ I)
  have hlenRead :
      readStorageBytesLength? bytesStoreLiteConfig evm
          (bytesStoreLiteSetChunkByteHeaderRef I) =
        .ok len.toNat := by
    have hltLen : UInt256.lt len ⟨32⟩ = ⟨1⟩ := by
      exact ult_one (by
        simpa [show (⟨32⟩ : UInt256).toNat = 32 from by decide] using hshort)
    have hvalidLen : UInt256.sub ⟨0⟩ (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩ := by
      rw [hltLen]
      native_decide
    exact bytesStoreLiteReadLengthOfHeaderLoad
      (er := bytesStoreLiteSetChunkByteHeaderRef I) (evm := evm)
      (baseSlot := bytesStoreLiteSetChunkByteSlot I)
      (header := bytesStoreLiteSetChunkByteHeaderWord σ I) (len := len.toNat)
      (bytesStoreLiteSetChunkByteHeaderRef_length_slot evm I)
      hloadHeader
      (solidityDecodeBytesLengthHeader_short_valid hflag hlen (by simpa [hflag] using hvalidLen))
  have hpacked : checkBytesPacked (bytesStoreLiteSetChunkByteSlot I) evm = true :=
    checkBytesPacked_of_storageLoad_land_one_zero hloadHeader hflag
  have hidx31 : (bytesStoreLiteSetChunkByteIndexWord I).toNat < 31 :=
    bytesStoreLiteSetChunkByteIndex_lt31_of_short_bound (I := I) (len := len)
      hshort hbound
  have hlayout :
      bytesStoreLiteConfig.storage.layout (bytesStoreLiteSetChunkByteRef I) evm =
        some (uint8Loc (bytesStoreLiteSetChunkByteSlot I)
          ⟨31 - (bytesStoreLiteSetChunkByteIndexWord I).toNat, by omega⟩) :=
    bytesStoreLiteSetChunkByteLayoutShort (evm := evm) (I := I) hpacked hidx31
  have hstore :
      (match bytesStoreLiteConfig.storage.layout (bytesStoreLiteSetChunkByteRef I) evm with
      | some loc => storageLocStore evm loc (bytesStoreLiteSetChunkByteValue I)
      | none => none) = some evm' := by
    rw [hlayout]
    simpa [evm'] using
      bytesStoreLiteSetChunkByteStorageLocStoreShort
        (evm := evm) (σ := σ) (I := I) (len := len)
        hloadHeader hcanon hshort hbound
  have hassign :
      assignStorageRef? bytesStoreLiteConfig
        (bytesStoreLiteSetChunkByteFrame I)
        evm .storage (chunkByteRef (.var "chunkIndex") (.var "byteIndex"))
          (bytesStoreLiteSetChunkByteValue I) =
          .ok (bytesStoreLiteSetChunkByteFrame I, evm') :=
    bytesStoreLiteSetChunkByteAssignOfLength (evm := evm) (evm' := evm') (I := I)
      hloadChunks hchunkBound hlenRead hbound hstore
  have hloadPost :
      Solm.EVM.storageLoad evm' evm'.executionEnv.codeOwner
          (bytesStoreLiteSetChunkByteSlot I) =
        bytesStoreLiteSetChunkByteShortStoredWord σ I := by
    simpa [evm'] using
      storageLoad_storageStore_codeOwner_same_present evm hacc
        (bytesStoreLiteSetChunkByteSlot I)
        (bytesStoreLiteSetChunkByteShortStoredWord σ I)
  have hloadChunksPost' :
      Solm.EVM.storageLoad evm' evm'.executionEnv.codeOwner ⟨1⟩ = chunksLenPost := by
    simpa [evm', storageStore_executionEnv] using hloadChunksPost
  have hflagPost :
      UInt256.land (bytesStoreLiteSetChunkByteShortStoredWord σ I) ⟨1⟩ = ⟨0⟩ := by
    rw [bytesStoreLiteSetChunkByteShortStoredWord_flag_eq
      (σ := σ) (I := I) (len := len) hshort hbound, hflag]
  have hlenPost :
      readStorageBytesLength? bytesStoreLiteConfig evm'
          (bytesStoreLiteSetChunkByteHeaderRef I) =
        .ok len.toNat := by
    have hltLen : UInt256.lt len ⟨32⟩ = ⟨1⟩ := by
      exact ult_one (by
        simpa [show (⟨32⟩ : UInt256).toNat = 32 from by decide] using hshort)
    have hvalidLen : UInt256.sub ⟨0⟩ (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩ := by
      rw [hltLen]
      native_decide
    have hlenPostWord :
        UInt256.land
            (UInt256.div (bytesStoreLiteSetChunkByteShortStoredWord σ I) ⟨2⟩) ⟨127⟩ =
          len := by
      rw [bytesStoreLiteSetChunkByteShortStoredWord_shortLen_eq
        (σ := σ) (I := I) (len := len) hshort hbound]
      exact hlen.symm
    exact bytesStoreLiteReadLengthOfHeaderLoad
      (er := bytesStoreLiteSetChunkByteHeaderRef I) (evm := evm')
      (baseSlot := bytesStoreLiteSetChunkByteSlot I)
      (header := bytesStoreLiteSetChunkByteShortStoredWord σ I) (len := len.toNat)
      (bytesStoreLiteSetChunkByteHeaderRef_length_slot evm' I)
      hloadPost
      (solidityDecodeBytesLengthHeader_short_valid hflagPost hlenPostWord.symm (by
        simpa [hflagPost] using hvalidLen))
  have hpackedPost : checkBytesPacked (bytesStoreLiteSetChunkByteSlot I) evm' = true :=
    checkBytesPacked_of_storageLoad_land_one_zero hloadPost hflagPost
  have hlayoutPost :
      bytesStoreLiteConfig.storage.layout (bytesStoreLiteSetChunkByteRef I) evm' =
        some (uint8Loc (bytesStoreLiteSetChunkByteSlot I)
          ⟨31 - (bytesStoreLiteSetChunkByteIndexWord I).toNat, by omega⟩) :=
    bytesStoreLiteSetChunkByteLayoutShort (evm := evm') (I := I) hpackedPost hidx31
  have hidxLe : (bytesStoreLiteSetChunkByteIndexWord I).toNat ≤ 31 := by
    omega
  have hret :
      evalExpr? bytesStoreLiteConfig
        (bytesStoreLiteSetChunkByteFrame I)
        evm' (.storage (chunkByteRef (.var "chunkIndex") (.var "byteIndex"))) =
          .ok (bytesStoreLiteSetChunkByteValue I) := by
    rw [evalExpr_storage_scalar_of_resolve_layout
      (bytesStoreLiteSetChunkByteResolveOfLength
        (evm := evm') (I := I) (chunksLen := chunksLenPost) (len := len.toNat)
        hloadChunksPost' hchunkBoundPost hlenPost hbound)
      hlayoutPost]
    rw [storageLocLoad_uint8Loc_byteAt
      (slot := bytesStoreLiteSetChunkByteSlot I)
      (idx := bytesStoreLiteSetChunkByteIndexWord I)
      (off := ⟨31 - (bytesStoreLiteSetChunkByteIndexWord I).toNat, by omega⟩)
      (hoff := by rfl) (hidx := hidxLe)]
    rw [hloadPost]
    rw [bytesStoreLiteSetChunkByteShortStoredWord_byteAt
      (σ := σ) (I := I) (len := len) hcanon hshort hbound]
    simp [bytesStoreLiteSetChunkByteValue]
  simpa [evm'] using
    bytesStoreLiteSetChunkByteBodyReturns (evm := evm) (evm' := evm') (I := I)
      hwv hassign hret

theorem bytesStoreLiteSetChunkByteLongBodyReturns_of_post_readback
    {evm : EVM.State} {σ : AccountMap} {I : ExecutionEnv}
    {chunksLen chunksLenPost len lenPost postHeaderWord : UInt256} {acc : Account}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hloadChunks : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩ = chunksLen)
    (hchunkBound : (bytesStoreLiteSetChunkByteChunkIndexWord I).toNat < chunksLen.toNat)
    (hloadChunksPost :
      Solm.EVM.storageLoad
          (Solm.EVM.storageStore evm evm.executionEnv.codeOwner
            (bytesStoreLiteSetChunkByteLongDataSlot I)
            (bytesStoreLiteSetChunkByteLongStoredWord σ I))
          evm.executionEnv.codeOwner ⟨1⟩ = chunksLenPost)
    (hchunkBoundPost :
      (bytesStoreLiteSetChunkByteChunkIndexWord I).toNat < chunksLenPost.toNat)
    (hloadHeader : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (bytesStoreLiteSetChunkByteSlot I) = bytesStoreLiteSetChunkByteHeaderWord σ I)
    (hloadData : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (bytesStoreLiteSetChunkByteLongDataSlot I) =
      bytesStoreLiteSetChunkByteLongOldWord σ I)
    (hloadHeaderPost :
      Solm.EVM.storageLoad
          (Solm.EVM.storageStore evm evm.executionEnv.codeOwner
            (bytesStoreLiteSetChunkByteLongDataSlot I)
            (bytesStoreLiteSetChunkByteLongStoredWord σ I))
          evm.executionEnv.codeOwner (bytesStoreLiteSetChunkByteSlot I) =
        postHeaderWord)
    (hacc : evm.accountMap.find? evm.executionEnv.codeOwner = some acc)
    (hcanon : (bytesStoreLiteSetChunkByteValueWord I).toNat < EVM.twoPow 8)
    (hlen : len = UInt256.div (bytesStoreLiteSetChunkByteHeaderWord σ I) ⟨2⟩)
    (hlenPost : lenPost = UInt256.div postHeaderWord ⟨2⟩)
    (hbound : (bytesStoreLiteSetChunkByteIndexWord I).toNat < len.toNat)
    (hboundPost : (bytesStoreLiteSetChunkByteIndexWord I).toNat < lenPost.toNat)
    (hflag : UInt256.land (bytesStoreLiteSetChunkByteHeaderWord σ I) ⟨1⟩ ≠ ⟨0⟩)
    (hflagPost : UInt256.land postHeaderWord ⟨1⟩ ≠ ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (bytesStoreLiteSetChunkByteHeaderWord σ I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStoreLiteSetChunkByteHeaderWord σ I) ⟨2⟩) ⟨32⟩) ≠
          ⟨0⟩)
    (hvalidPost : UInt256.sub (UInt256.land postHeaderWord ⟨1⟩)
        (UInt256.lt (UInt256.div postHeaderWord ⟨2⟩) ⟨32⟩) ≠ ⟨0⟩) :
    ExecTransitionBody bytesStoreLiteConfig bytesStoreLiteContract evm
      (bytesStoreLiteSetChunkByteLocals I) setChunkByteTransition.body
      (.returned
        (bytesStoreLiteSetChunkByteFrame I)
        (Solm.EVM.storageStore evm evm.executionEnv.codeOwner
          (bytesStoreLiteSetChunkByteLongDataSlot I)
          (bytesStoreLiteSetChunkByteLongStoredWord σ I))
        (some (bytesStoreLiteSetChunkByteValue I))) := by
  let evm' := Solm.EVM.storageStore evm evm.executionEnv.codeOwner
    (bytesStoreLiteSetChunkByteLongDataSlot I)
    (bytesStoreLiteSetChunkByteLongStoredWord σ I)
  have hvalidLen :
      UInt256.sub (UInt256.land (bytesStoreLiteSetChunkByteHeaderWord σ I) ⟨1⟩)
        (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩ := by
    simpa [hlen] using hvalid
  have hlenRead :
      readStorageBytesLength? bytesStoreLiteConfig evm
          (bytesStoreLiteSetChunkByteHeaderRef I) =
        .ok len.toNat := by
    exact bytesStoreLiteReadLengthOfHeaderLoad
      (er := bytesStoreLiteSetChunkByteHeaderRef I) (evm := evm)
      (baseSlot := bytesStoreLiteSetChunkByteSlot I)
      (header := bytesStoreLiteSetChunkByteHeaderWord σ I) (len := len.toNat)
      (bytesStoreLiteSetChunkByteHeaderRef_length_slot evm I)
      hloadHeader
      (solidityDecodeBytesLengthHeader_long_valid hflag hlen hvalidLen)
  have hpacked : checkBytesPacked (bytesStoreLiteSetChunkByteSlot I) evm = false :=
    checkBytesPacked_of_storageLoad_land_one_ne_zero hloadHeader hflag
  have hlayout :
      bytesStoreLiteConfig.storage.layout (bytesStoreLiteSetChunkByteRef I) evm =
        some (uint8Loc (bytesStoreLiteSetChunkByteLongDataSlot I)
          ⟨31 - (bytesStoreLiteSetChunkByteLongWordIndex I).toNat, by
            have hidx := bytesStoreLiteSetChunkByteLongWordIndex_lt32 I
            omega⟩) :=
    bytesStoreLiteSetChunkByteLayoutLong (evm := evm) (I := I) hpacked
  have hstore :
      (match bytesStoreLiteConfig.storage.layout (bytesStoreLiteSetChunkByteRef I) evm with
      | some loc => storageLocStore evm loc (bytesStoreLiteSetChunkByteValue I)
      | none => none) = some evm' := by
    rw [hlayout]
    simpa [evm'] using
      bytesStoreLiteSetChunkByteStorageLocStoreLong
        (evm := evm) (σ := σ) (I := I) hloadData hcanon
  have hassign :
      assignStorageRef? bytesStoreLiteConfig
        (bytesStoreLiteSetChunkByteFrame I)
        evm .storage (chunkByteRef (.var "chunkIndex") (.var "byteIndex"))
          (bytesStoreLiteSetChunkByteValue I) =
          .ok (bytesStoreLiteSetChunkByteFrame I, evm') :=
    bytesStoreLiteSetChunkByteAssignOfLength (evm := evm) (evm' := evm') (I := I)
      hloadChunks hchunkBound hlenRead hbound hstore
  have hloadHeaderPost' :
      Solm.EVM.storageLoad evm' evm'.executionEnv.codeOwner
          (bytesStoreLiteSetChunkByteSlot I) =
        postHeaderWord := by
    simpa [evm', storageStore_executionEnv] using hloadHeaderPost
  have hloadChunksPost' :
      Solm.EVM.storageLoad evm' evm'.executionEnv.codeOwner ⟨1⟩ = chunksLenPost := by
    simpa [evm', storageStore_executionEnv] using hloadChunksPost
  have hlenPost :
      readStorageBytesLength? bytesStoreLiteConfig evm'
          (bytesStoreLiteSetChunkByteHeaderRef I) =
        .ok lenPost.toNat := by
    have hvalidLenPost :
        UInt256.sub (UInt256.land postHeaderWord ⟨1⟩) (UInt256.lt lenPost ⟨32⟩) ≠
          ⟨0⟩ := by
      simpa [hlenPost] using hvalidPost
    exact bytesStoreLiteReadLengthOfHeaderLoad
      (er := bytesStoreLiteSetChunkByteHeaderRef I) (evm := evm')
      (baseSlot := bytesStoreLiteSetChunkByteSlot I)
      (header := postHeaderWord) (len := lenPost.toNat)
      (bytesStoreLiteSetChunkByteHeaderRef_length_slot evm' I)
      hloadHeaderPost'
      (solidityDecodeBytesLengthHeader_long_valid hflagPost hlenPost hvalidLenPost)
  have hpackedPost : checkBytesPacked (bytesStoreLiteSetChunkByteSlot I) evm' = false :=
    checkBytesPacked_of_storageLoad_land_one_ne_zero hloadHeaderPost' hflagPost
  have hlayoutPost :
      bytesStoreLiteConfig.storage.layout (bytesStoreLiteSetChunkByteRef I) evm' =
        some (uint8Loc (bytesStoreLiteSetChunkByteLongDataSlot I)
          ⟨31 - (bytesStoreLiteSetChunkByteLongWordIndex I).toNat, by
            have hidx := bytesStoreLiteSetChunkByteLongWordIndex_lt32 I
            omega⟩) :=
    bytesStoreLiteSetChunkByteLayoutLong (evm := evm') (I := I) hpackedPost
  have hloadDataPost :
      Solm.EVM.storageLoad evm' evm'.executionEnv.codeOwner
          (bytesStoreLiteSetChunkByteLongDataSlot I) =
        bytesStoreLiteSetChunkByteLongStoredWord σ I := by
    simpa [evm'] using
      storageLoad_storageStore_codeOwner_same_present evm hacc
        (bytesStoreLiteSetChunkByteLongDataSlot I)
        (bytesStoreLiteSetChunkByteLongStoredWord σ I)
  have hret :
      evalExpr? bytesStoreLiteConfig
        (bytesStoreLiteSetChunkByteFrame I)
        evm' (.storage (chunkByteRef (.var "chunkIndex") (.var "byteIndex"))) =
          .ok (bytesStoreLiteSetChunkByteValue I) := by
    rw [evalExpr_storage_scalar_of_resolve_layout
      (bytesStoreLiteSetChunkByteResolveOfLength
        (evm := evm') (I := I) (chunksLen := chunksLenPost) (len := lenPost.toNat)
        hloadChunksPost' hchunkBoundPost hlenPost hboundPost)
      hlayoutPost]
    rw [storageLocLoad_uint8Loc_byteAt
      (evm := evm') (slot := bytesStoreLiteSetChunkByteLongDataSlot I)
      (idx := bytesStoreLiteSetChunkByteLongWordIndex I)
      (off := ⟨31 - (bytesStoreLiteSetChunkByteLongWordIndex I).toNat, by
        have hidx := bytesStoreLiteSetChunkByteLongWordIndex_lt32 I
        omega⟩)
      (by rfl)
      (by
        have hidx := bytesStoreLiteSetChunkByteLongWordIndex_lt32 I
        omega)]
    rw [hloadDataPost]
    rw [bytesStoreLiteSetChunkByteLongStoredWord_byteAt (σ := σ) (I := I) hcanon]
    simp [bytesStoreLiteSetChunkByteValue]
  simpa [evm'] using
    bytesStoreLiteSetChunkByteBodyReturns (evm := evm) (evm' := evm') (I := I)
      hwv hassign hret

theorem bytesStoreLiteSetChunkByteLongBodyReturnsOfPostShortReadback
    {evm : EVM.State} {σ : AccountMap} {I : ExecutionEnv}
    {chunksLen chunksLenPost len lenPost postHeaderWord : UInt256} {acc : Account}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hloadChunks : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩ = chunksLen)
    (hchunkBound : (bytesStoreLiteSetChunkByteChunkIndexWord I).toNat < chunksLen.toNat)
    (hloadChunksPost :
      Solm.EVM.storageLoad
          (Solm.EVM.storageStore evm evm.executionEnv.codeOwner
            (bytesStoreLiteSetChunkByteLongDataSlot I)
            (bytesStoreLiteSetChunkByteLongStoredWord σ I))
          evm.executionEnv.codeOwner ⟨1⟩ = chunksLenPost)
    (hchunkBoundPost :
      (bytesStoreLiteSetChunkByteChunkIndexWord I).toNat < chunksLenPost.toNat)
    (hloadHeader : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (bytesStoreLiteSetChunkByteSlot I) = bytesStoreLiteSetChunkByteHeaderWord σ I)
    (hloadData : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (bytesStoreLiteSetChunkByteLongDataSlot I) =
      bytesStoreLiteSetChunkByteLongOldWord σ I)
    (hloadHeaderPost :
      Solm.EVM.storageLoad
          (Solm.EVM.storageStore evm evm.executionEnv.codeOwner
            (bytesStoreLiteSetChunkByteLongDataSlot I)
            (bytesStoreLiteSetChunkByteLongStoredWord σ I))
          evm.executionEnv.codeOwner (bytesStoreLiteSetChunkByteSlot I) =
        postHeaderWord)
    (hacc : evm.accountMap.find? evm.executionEnv.codeOwner = some acc)
    (hcanon : (bytesStoreLiteSetChunkByteValueWord I).toNat < EVM.twoPow 8)
    (hlen : len = UInt256.div (bytesStoreLiteSetChunkByteHeaderWord σ I) ⟨2⟩)
    (hlenPost : lenPost = UInt256.land (UInt256.div postHeaderWord ⟨2⟩) ⟨127⟩)
    (hbound : (bytesStoreLiteSetChunkByteIndexWord I).toNat < len.toNat)
    (hboundPost : (bytesStoreLiteSetChunkByteIndexWord I).toNat < lenPost.toNat)
    (hflag : UInt256.land (bytesStoreLiteSetChunkByteHeaderWord σ I) ⟨1⟩ ≠ ⟨0⟩)
    (hflagPost : UInt256.land postHeaderWord ⟨1⟩ = ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (bytesStoreLiteSetChunkByteHeaderWord σ I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStoreLiteSetChunkByteHeaderWord σ I) ⟨2⟩) ⟨32⟩) ≠
          ⟨0⟩)
    (hvalidPost : UInt256.sub (UInt256.land postHeaderWord ⟨1⟩)
        (UInt256.lt (UInt256.land (UInt256.div postHeaderWord ⟨2⟩) ⟨127⟩) ⟨32⟩) ≠
          ⟨0⟩) :
    ExecTransitionBody bytesStoreLiteConfig bytesStoreLiteContract evm
      (bytesStoreLiteSetChunkByteLocals I) setChunkByteTransition.body
      (.returned
        (bytesStoreLiteSetChunkByteFrame I)
        (Solm.EVM.storageStore evm evm.executionEnv.codeOwner
          (bytesStoreLiteSetChunkByteLongDataSlot I)
          (bytesStoreLiteSetChunkByteLongStoredWord σ I))
        (some (bytesStoreLiteSetChunkByteValue I))) := by
  let evm' := Solm.EVM.storageStore evm evm.executionEnv.codeOwner
    (bytesStoreLiteSetChunkByteLongDataSlot I)
    (bytesStoreLiteSetChunkByteLongStoredWord σ I)
  have hvalidLen :
      UInt256.sub (UInt256.land (bytesStoreLiteSetChunkByteHeaderWord σ I) ⟨1⟩)
        (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩ := by
    simpa [hlen] using hvalid
  have hlenRead :
      readStorageBytesLength? bytesStoreLiteConfig evm
          (bytesStoreLiteSetChunkByteHeaderRef I) =
        .ok len.toNat := by
    exact bytesStoreLiteReadLengthOfHeaderLoad
      (er := bytesStoreLiteSetChunkByteHeaderRef I) (evm := evm)
      (baseSlot := bytesStoreLiteSetChunkByteSlot I)
      (header := bytesStoreLiteSetChunkByteHeaderWord σ I) (len := len.toNat)
      (bytesStoreLiteSetChunkByteHeaderRef_length_slot evm I)
      hloadHeader
      (solidityDecodeBytesLengthHeader_long_valid hflag hlen hvalidLen)
  have hpacked : checkBytesPacked (bytesStoreLiteSetChunkByteSlot I) evm = false :=
    checkBytesPacked_of_storageLoad_land_one_ne_zero hloadHeader hflag
  have hlayout :
      bytesStoreLiteConfig.storage.layout (bytesStoreLiteSetChunkByteRef I) evm =
        some (uint8Loc (bytesStoreLiteSetChunkByteLongDataSlot I)
          ⟨31 - (bytesStoreLiteSetChunkByteLongWordIndex I).toNat, by
            have hidx := bytesStoreLiteSetChunkByteLongWordIndex_lt32 I
            omega⟩) :=
    bytesStoreLiteSetChunkByteLayoutLong (evm := evm) (I := I) hpacked
  have hstore :
      (match bytesStoreLiteConfig.storage.layout (bytesStoreLiteSetChunkByteRef I) evm with
      | some loc => storageLocStore evm loc (bytesStoreLiteSetChunkByteValue I)
      | none => none) = some evm' := by
    rw [hlayout]
    simpa [evm'] using
      bytesStoreLiteSetChunkByteStorageLocStoreLong
        (evm := evm) (σ := σ) (I := I) hloadData hcanon
  have hassign :
      assignStorageRef? bytesStoreLiteConfig
        (bytesStoreLiteSetChunkByteFrame I)
        evm .storage (chunkByteRef (.var "chunkIndex") (.var "byteIndex"))
          (bytesStoreLiteSetChunkByteValue I) =
          .ok (bytesStoreLiteSetChunkByteFrame I, evm') :=
    bytesStoreLiteSetChunkByteAssignOfLength (evm := evm) (evm' := evm') (I := I)
      hloadChunks hchunkBound hlenRead hbound hstore
  have hloadHeaderPost' :
      Solm.EVM.storageLoad evm' evm'.executionEnv.codeOwner
          (bytesStoreLiteSetChunkByteSlot I) =
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
      readStorageBytesLength? bytesStoreLiteConfig evm'
          (bytesStoreLiteSetChunkByteHeaderRef I) =
        .ok lenPost.toNat := by
    exact bytesStoreLiteReadLengthOfHeaderLoad
      (er := bytesStoreLiteSetChunkByteHeaderRef I) (evm := evm')
      (baseSlot := bytesStoreLiteSetChunkByteSlot I)
      (header := postHeaderWord) (len := lenPost.toNat)
      (bytesStoreLiteSetChunkByteHeaderRef_length_slot evm' I)
      hloadHeaderPost'
      (solidityDecodeBytesLengthHeader_short_valid hflagPost hlenPost
        (by simpa [← hlenPost] using hvalidPost))
  have hpackedPost : checkBytesPacked (bytesStoreLiteSetChunkByteSlot I) evm' = true :=
    checkBytesPacked_of_storageLoad_land_one_zero hloadHeaderPost' hflagPost
  have hidx31 : (bytesStoreLiteSetChunkByteIndexWord I).toNat < 31 :=
    bytesStoreLiteSetChunkByteIndex_lt31_of_short_bound (I := I) (len := lenPost)
      hshortPost hboundPost
  have hlayoutPost :
      bytesStoreLiteConfig.storage.layout (bytesStoreLiteSetChunkByteRef I) evm' =
        some (uint8Loc (bytesStoreLiteSetChunkByteSlot I)
          ⟨31 - (bytesStoreLiteSetChunkByteIndexWord I).toNat, by omega⟩) :=
    bytesStoreLiteSetChunkByteLayoutShort (evm := evm') (I := I) hpackedPost hidx31
  have hheaderStored : postHeaderWord = bytesStoreLiteSetChunkByteLongStoredWord σ I := by
    by_cases hEq : bytesStoreLiteSetChunkByteSlot I =
        bytesStoreLiteSetChunkByteLongDataSlot I
    · have hsame :
          Solm.EVM.storageLoad evm' evm'.executionEnv.codeOwner
              (bytesStoreLiteSetChunkByteSlot I) =
            bytesStoreLiteSetChunkByteLongStoredWord σ I := by
        simpa [evm', hEq] using
          storageLoad_storageStore_codeOwner_same_present evm hacc
            (bytesStoreLiteSetChunkByteLongDataSlot I)
            (bytesStoreLiteSetChunkByteLongStoredWord σ I)
      exact hloadHeaderPost'.symm.trans hsame
    · have hpostOld :
          Solm.EVM.storageLoad evm' evm'.executionEnv.codeOwner
              (bytesStoreLiteSetChunkByteSlot I) =
            bytesStoreLiteSetChunkByteHeaderWord σ I := by
        have hne :
            bytesStoreLiteSetChunkByteSlot I ≠
              bytesLikeDataBase (bytesStoreLiteSetChunkByteSlot I) +
                UInt256.div (bytesStoreLiteSetChunkByteIndexWord I) ⟨32⟩ := by
          simpa [bytesStoreLiteSetChunkByteLongDataSlot] using hEq
        have hpostOldOwner :
            Solm.EVM.storageLoad evm' evm.executionEnv.codeOwner
                (bytesStoreLiteSetChunkByteSlot I) =
              Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
                (bytesStoreLiteSetChunkByteSlot I) := by
          simpa [evm', bytesStoreLiteSetChunkByteLongDataSlot] using
            bytesStoreLiteStorageLoadBytesHeaderAfterDataStore_ne_of_ne
              (evm := evm) (baseSlot := bytesStoreLiteSetChunkByteSlot I)
              (idx := bytesStoreLiteSetChunkByteIndexWord I)
              (val := bytesStoreLiteSetChunkByteLongStoredWord σ I) hne
        simpa [evm', storageStore_executionEnv, hloadHeader] using hpostOldOwner
      have hzeroOld :
          UInt256.land (bytesStoreLiteSetChunkByteHeaderWord σ I) ⟨1⟩ = ⟨0⟩ := by
        have hpostWord :
            postHeaderWord = bytesStoreLiteSetChunkByteHeaderWord σ I :=
          hloadHeaderPost'.symm.trans hpostOld
        simpa [hpostWord] using hflagPost
      exact False.elim (hflag hzeroOld)
  have hidxLe : (bytesStoreLiteSetChunkByteIndexWord I).toNat ≤ 31 := by
    omega
  have hret :
      evalExpr? bytesStoreLiteConfig
        (bytesStoreLiteSetChunkByteFrame I)
        evm' (.storage (chunkByteRef (.var "chunkIndex") (.var "byteIndex"))) =
          .ok (bytesStoreLiteSetChunkByteValue I) := by
    rw [evalExpr_storage_scalar_of_resolve_layout
      (bytesStoreLiteSetChunkByteResolveOfLength
        (evm := evm') (I := I) (chunksLen := chunksLenPost) (len := lenPost.toNat)
        hloadChunksPost' hchunkBoundPost hlenPostRead hboundPost)
      hlayoutPost]
    rw [storageLocLoad_uint8Loc_byteAt
      (slot := bytesStoreLiteSetChunkByteSlot I)
      (idx := bytesStoreLiteSetChunkByteIndexWord I)
      (off := ⟨31 - (bytesStoreLiteSetChunkByteIndexWord I).toNat, by omega⟩)
      (hoff := by rfl) (hidx := hidxLe)]
    rw [hloadHeaderPost']
    rw [hheaderStored]
    rw [bytesStoreLiteSetChunkByteLongStoredWord_byteAt_index_of_lt32
      (σ := σ) (I := I) hcanon (by omega)]
    simp [bytesStoreLiteSetChunkByteValue]
  simpa [evm'] using
    bytesStoreLiteSetChunkByteBodyReturns (evm := evm) (evm' := evm') (I := I)
      hwv hassign hret

theorem bytesStoreLiteSetChunkByteResolveRevertsOfLength {evm : EVM.State}
    {I : ExecutionEnv} {chunksLen : UInt256} {len : Nat}
    (hload :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩ = chunksLen)
    (hchunkBound :
      (bytesStoreLiteSetChunkByteChunkIndexWord I).toNat < chunksLen.toNat)
    (hlen : readStorageBytesLength? bytesStoreLiteConfig evm
      (bytesStoreLiteSetChunkByteHeaderRef I) = .ok len)
    (hbound : ¬ (bytesStoreLiteSetChunkByteIndexWord I).toNat < len) :
    resolveStorageRef? bytesStoreLiteConfig
      (bytesStoreLiteSetChunkByteFrame I) evm
      (chunkByteRef (.var "chunkIndex") (.var "byteIndex")) = .revert := by
  have hgetChunks :
      (bytesStoreLiteSetChunkByteLocals I).get? "chunks" = none :=
    bytesStoreLiteSetChunkByteLocals_get_chunks_none I
  have herInline :
      evalStorageRef bytesStoreLiteConfig
        { contract := bytesStoreLiteContract, locals := bytesStoreLiteSetChunkByteLocals I }
        evm (chunkByteRef (.var "chunkIndex") (.var "byteIndex")) = .revert := by
    simpa [bytesStoreLiteSetChunkByteFrame] using
      (bytesStoreLiteSetChunkByteEvalStorageRefRevertsOfLength
        (evm := evm) (I := I) (chunksLen := chunksLen) (len := len)
        hload hchunkBound hlen hbound)
  exact resolveStorageRef?_revert_of_evalStorageRef_revert hgetChunks herInline

theorem bytesStoreLiteSetChunkByteBodyBoundsRevertsOfLength {evm : EVM.State}
    {I : ExecutionEnv} {chunksLen : UInt256} {len : Nat}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hload :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩ = chunksLen)
    (hchunkBound :
      (bytesStoreLiteSetChunkByteChunkIndexWord I).toNat < chunksLen.toNat)
    (hlen : readStorageBytesLength? bytesStoreLiteConfig evm
      (bytesStoreLiteSetChunkByteHeaderRef I) = .ok len)
    (hbound : ¬ (bytesStoreLiteSetChunkByteIndexWord I).toNat < len) :
    ExecTransitionBody bytesStoreLiteConfig bytesStoreLiteContract evm
      (bytesStoreLiteSetChunkByteLocals I) setChunkByteTransition.body .reverted := by
  let solm : Frame := bytesStoreLiteSetChunkByteFrame I
  have hvalue :
      evalExpr? bytesStoreLiteConfig solm evm (.var "value") =
        .ok (bytesStoreLiteSetChunkByteValue I) := by
    exact evalExpr_var_of_get? (by
      simp [solm, bytesStoreLiteSetChunkByteFrame, bytesStoreLiteSetChunkByteValue,
        bytesStoreLiteSetChunkByteLocals])
  have hassign :
      assignStorageRef? bytesStoreLiteConfig solm evm .storage
        (chunkByteRef (.var "chunkIndex") (.var "byteIndex"))
          (bytesStoreLiteSetChunkByteValue I) = .revert := by
    exact assignStorageRef_storage_revert_of_resolve
      (bytesStoreLiteSetChunkByteResolveRevertsOfLength
        (evm := evm) (I := I) (chunksLen := chunksLen) (len := len)
        hload hchunkBound hlen hbound)
  exact ExecFuncBody.execBlockRevert <|
    ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consRevert (ExecStmt.assignStoreRevert hvalue hassign)

theorem bytesStoreLiteSetChunkByteResolveRevertsOfLengthRead {evm : EVM.State}
    {I : ExecutionEnv} {chunksLen : UInt256}
    (hload :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩ = chunksLen)
    (hchunkBound :
      (bytesStoreLiteSetChunkByteChunkIndexWord I).toNat < chunksLen.toNat)
    (hlen : readStorageBytesLength? bytesStoreLiteConfig evm
      (bytesStoreLiteSetChunkByteHeaderRef I) = .revert) :
    resolveStorageRef? bytesStoreLiteConfig
      (bytesStoreLiteSetChunkByteFrame I) evm
      (chunkByteRef (.var "chunkIndex") (.var "byteIndex")) = .revert := by
  have hgetChunks :
      (bytesStoreLiteSetChunkByteLocals I).get? "chunks" = none :=
    bytesStoreLiteSetChunkByteLocals_get_chunks_none I
  have herInline :
      evalStorageRef bytesStoreLiteConfig
        { contract := bytesStoreLiteContract, locals := bytesStoreLiteSetChunkByteLocals I }
        evm (chunkByteRef (.var "chunkIndex") (.var "byteIndex")) = .revert := by
    simpa [bytesStoreLiteSetChunkByteFrame] using
      (bytesStoreLiteSetChunkByteEvalStorageRefRevertsOfLengthRead
        (evm := evm) (I := I) (chunksLen := chunksLen)
        hload hchunkBound hlen)
  exact resolveStorageRef?_revert_of_evalStorageRef_revert hgetChunks herInline

theorem bytesStoreLiteSetChunkByteBodyRevertsOfLengthRead {evm : EVM.State}
    {I : ExecutionEnv} {chunksLen : UInt256}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hload :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩ = chunksLen)
    (hchunkBound :
      (bytesStoreLiteSetChunkByteChunkIndexWord I).toNat < chunksLen.toNat)
    (hlen : readStorageBytesLength? bytesStoreLiteConfig evm
      (bytesStoreLiteSetChunkByteHeaderRef I) = .revert) :
    ExecTransitionBody bytesStoreLiteConfig bytesStoreLiteContract evm
      (bytesStoreLiteSetChunkByteLocals I) setChunkByteTransition.body .reverted := by
  let solm : Frame := bytesStoreLiteSetChunkByteFrame I
  have hvalue :
      evalExpr? bytesStoreLiteConfig solm evm (.var "value") =
        .ok (bytesStoreLiteSetChunkByteValue I) := by
    exact evalExpr_var_of_get? (by
      simp [solm, bytesStoreLiteSetChunkByteFrame, bytesStoreLiteSetChunkByteValue,
        bytesStoreLiteSetChunkByteLocals])
  have hassign :
      assignStorageRef? bytesStoreLiteConfig solm evm .storage
        (chunkByteRef (.var "chunkIndex") (.var "byteIndex"))
          (bytesStoreLiteSetChunkByteValue I) = .revert := by
    exact assignStorageRef_storage_revert_of_resolve
      (bytesStoreLiteSetChunkByteResolveRevertsOfLengthRead
        (evm := evm) (I := I) (chunksLen := chunksLen) hload hchunkBound hlen)
  exact ExecFuncBody.execBlockRevert <|
    ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consRevert (ExecStmt.assignStoreRevert hvalue hassign)

theorem bytesStoreLiteSetChunkByteResolveRevertsOfChunksLength {evm : EVM.State}
    {I : ExecutionEnv} {chunksLen : UInt256}
    (hload :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩ = chunksLen)
    (hbound :
      ¬ (bytesStoreLiteSetChunkByteChunkIndexWord I).toNat < chunksLen.toNat) :
    resolveStorageRef? bytesStoreLiteConfig
      (bytesStoreLiteSetChunkByteFrame I) evm
      (chunkByteRef (.var "chunkIndex") (.var "byteIndex")) = .revert := by
  have hgetChunksGet :
      (bytesStoreLiteSetChunkByteLocals I).get? "chunks" = none :=
    bytesStoreLiteSetChunkByteLocals_get_chunks_none I
  have herInline :
      evalStorageRef bytesStoreLiteConfig
        { contract := bytesStoreLiteContract, locals := bytesStoreLiteSetChunkByteLocals I }
        evm (chunkByteRef (.var "chunkIndex") (.var "byteIndex")) = .revert := by
    simpa [bytesStoreLiteSetChunkByteFrame] using
      (bytesStoreLiteSetChunkByteEvalStorageRefRevertsOfChunksLength
        (evm := evm) (I := I) (chunksLen := chunksLen) hload hbound)
  exact resolveStorageRef?_revert_of_evalStorageRef_revert hgetChunksGet herInline

theorem bytesStoreLiteSetChunkByteBodyBoundsRevertsOfChunksLength {evm : EVM.State}
    {I : ExecutionEnv} {chunksLen : UInt256}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hload :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩ = chunksLen)
    (hbound :
      ¬ (bytesStoreLiteSetChunkByteChunkIndexWord I).toNat < chunksLen.toNat) :
    ExecTransitionBody bytesStoreLiteConfig bytesStoreLiteContract evm
      (bytesStoreLiteSetChunkByteLocals I) setChunkByteTransition.body .reverted := by
  let solm : Frame := bytesStoreLiteSetChunkByteFrame I
  have hvalue :
      evalExpr? bytesStoreLiteConfig solm evm (.var "value") =
        .ok (bytesStoreLiteSetChunkByteValue I) := by
    exact evalExpr_var_of_get? (by
      simp [solm, bytesStoreLiteSetChunkByteFrame, bytesStoreLiteSetChunkByteValue,
        bytesStoreLiteSetChunkByteLocals])
  have hassign :
      assignStorageRef? bytesStoreLiteConfig solm evm .storage
        (chunkByteRef (.var "chunkIndex") (.var "byteIndex"))
          (bytesStoreLiteSetChunkByteValue I) = .revert := by
    exact assignStorageRef_storage_revert_of_resolve
      (bytesStoreLiteSetChunkByteResolveRevertsOfChunksLength
        (evm := evm) (I := I) (chunksLen := chunksLen) hload hbound)
  exact ExecFuncBody.execBlockRevert <|
    ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consRevert (ExecStmt.assignStoreRevert hvalue hassign)

theorem bytesStoreLiteSetChunkByteBodyReturnRevertsOfPostChunksLength
    {evm evm' : EVM.State} {I : ExecutionEnv} {chunksLenPost : UInt256}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hassign :
      assignStorageRef? bytesStoreLiteConfig
        (bytesStoreLiteSetChunkByteFrame I)
        evm .storage (chunkByteRef (.var "chunkIndex") (.var "byteIndex"))
          (bytesStoreLiteSetChunkByteValue I) =
          .ok (bytesStoreLiteSetChunkByteFrame I, evm'))
    (hloadPost :
      Solm.EVM.storageLoad evm' evm'.executionEnv.codeOwner ⟨1⟩ = chunksLenPost)
    (hboundPost :
      ¬ (bytesStoreLiteSetChunkByteChunkIndexWord I).toNat < chunksLenPost.toNat) :
    ExecTransitionBody bytesStoreLiteConfig bytesStoreLiteContract evm
      (bytesStoreLiteSetChunkByteLocals I) setChunkByteTransition.body .reverted := by
  have hret :
      evalExpr? bytesStoreLiteConfig
        (bytesStoreLiteSetChunkByteFrame I)
        evm' (.storage (chunkByteRef (.var "chunkIndex") (.var "byteIndex"))) = .revert := by
    rw [evalExpr?]
    rw [bytesStoreLiteSetChunkByteResolveRevertsOfChunksLength
      (evm := evm') (I := I) (chunksLen := chunksLenPost) hloadPost hboundPost]
    rfl
  exact bytesStoreLiteSetChunkByteBodyReturnReverts
    (evm := evm) (evm' := evm') (I := I) hwv hassign hret

theorem bytesStoreLiteSetChunkByteBodyReturnRevertsOfPostLengthRead
    {evm evm' : EVM.State} {I : ExecutionEnv} {chunksLenPost : UInt256}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hassign :
      assignStorageRef? bytesStoreLiteConfig
        (bytesStoreLiteSetChunkByteFrame I)
        evm .storage (chunkByteRef (.var "chunkIndex") (.var "byteIndex"))
          (bytesStoreLiteSetChunkByteValue I) =
          .ok (bytesStoreLiteSetChunkByteFrame I, evm'))
    (hloadPost :
      Solm.EVM.storageLoad evm' evm'.executionEnv.codeOwner ⟨1⟩ = chunksLenPost)
    (hchunkBoundPost :
      (bytesStoreLiteSetChunkByteChunkIndexWord I).toNat < chunksLenPost.toNat)
    (hlenPost :
      readStorageBytesLength? bytesStoreLiteConfig evm'
        (bytesStoreLiteSetChunkByteHeaderRef I) = .revert) :
    ExecTransitionBody bytesStoreLiteConfig bytesStoreLiteContract evm
      (bytesStoreLiteSetChunkByteLocals I) setChunkByteTransition.body .reverted := by
  have hret :
      evalExpr? bytesStoreLiteConfig
        (bytesStoreLiteSetChunkByteFrame I)
        evm' (.storage (chunkByteRef (.var "chunkIndex") (.var "byteIndex"))) = .revert := by
    rw [evalExpr?]
    rw [bytesStoreLiteSetChunkByteResolveRevertsOfLengthRead
      (evm := evm') (I := I) (chunksLen := chunksLenPost)
      hloadPost hchunkBoundPost hlenPost]
    rfl
  exact bytesStoreLiteSetChunkByteBodyReturnReverts
    (evm := evm) (evm' := evm') (I := I) hwv hassign hret

theorem bytesStoreLiteSetChunkByteBodyReturnRevertsOfPostLength
    {evm evm' : EVM.State} {I : ExecutionEnv} {chunksLenPost : UInt256} {lenPost : Nat}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hassign :
      assignStorageRef? bytesStoreLiteConfig
        (bytesStoreLiteSetChunkByteFrame I)
        evm .storage (chunkByteRef (.var "chunkIndex") (.var "byteIndex"))
          (bytesStoreLiteSetChunkByteValue I) =
          .ok (bytesStoreLiteSetChunkByteFrame I, evm'))
    (hloadPost :
      Solm.EVM.storageLoad evm' evm'.executionEnv.codeOwner ⟨1⟩ = chunksLenPost)
    (hchunkBoundPost :
      (bytesStoreLiteSetChunkByteChunkIndexWord I).toNat < chunksLenPost.toNat)
    (hlenPost :
      readStorageBytesLength? bytesStoreLiteConfig evm'
        (bytesStoreLiteSetChunkByteHeaderRef I) = .ok lenPost)
    (hboundPost : ¬ (bytesStoreLiteSetChunkByteIndexWord I).toNat < lenPost) :
    ExecTransitionBody bytesStoreLiteConfig bytesStoreLiteContract evm
      (bytesStoreLiteSetChunkByteLocals I) setChunkByteTransition.body .reverted := by
  have hret :
      evalExpr? bytesStoreLiteConfig
        (bytesStoreLiteSetChunkByteFrame I)
        evm' (.storage (chunkByteRef (.var "chunkIndex") (.var "byteIndex"))) = .revert := by
    rw [evalExpr?]
    rw [bytesStoreLiteSetChunkByteResolveRevertsOfLength
      (evm := evm') (I := I) (chunksLen := chunksLenPost) (len := lenPost)
      hloadPost hchunkBoundPost hlenPost hboundPost]
    rfl
  exact bytesStoreLiteSetChunkByteBodyReturnReverts
    (evm := evm) (evm' := evm') (I := I) hwv hassign hret

theorem bytesStoreLiteSetChunkByteShortBodyReturnRevertsOfPostChunksLength
    {evm : EVM.State} {σ : AccountMap} {I : ExecutionEnv}
    {chunksLen chunksLenPost len : UInt256}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hloadChunks : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩ = chunksLen)
    (hchunkBound : (bytesStoreLiteSetChunkByteChunkIndexWord I).toNat < chunksLen.toNat)
    (hloadChunksPost :
      Solm.EVM.storageLoad
          (Solm.EVM.storageStore evm evm.executionEnv.codeOwner
            (bytesStoreLiteSetChunkByteSlot I)
            (bytesStoreLiteSetChunkByteShortStoredWord σ I))
          evm.executionEnv.codeOwner ⟨1⟩ = chunksLenPost)
    (hchunkBoundPost :
      ¬ (bytesStoreLiteSetChunkByteChunkIndexWord I).toNat < chunksLenPost.toNat)
    (hloadHeader : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (bytesStoreLiteSetChunkByteSlot I) = bytesStoreLiteSetChunkByteHeaderWord σ I)
    (hcanon : (bytesStoreLiteSetChunkByteValueWord I).toNat < EVM.twoPow 8)
    (hlen : len =
      UInt256.land (UInt256.div (bytesStoreLiteSetChunkByteHeaderWord σ I) ⟨2⟩) ⟨127⟩)
    (hshort : len.toNat < 32)
    (hbound : (bytesStoreLiteSetChunkByteIndexWord I).toNat < len.toNat)
    (hflag : UInt256.land (bytesStoreLiteSetChunkByteHeaderWord σ I) ⟨1⟩ = ⟨0⟩) :
    ExecTransitionBody bytesStoreLiteConfig bytesStoreLiteContract evm
      (bytesStoreLiteSetChunkByteLocals I) setChunkByteTransition.body .reverted := by
  let evm' := Solm.EVM.storageStore evm evm.executionEnv.codeOwner
    (bytesStoreLiteSetChunkByteSlot I)
    (bytesStoreLiteSetChunkByteShortStoredWord σ I)
  have hlenRead :
      readStorageBytesLength? bytesStoreLiteConfig evm
          (bytesStoreLiteSetChunkByteHeaderRef I) =
        .ok len.toNat := by
    have hltLen : UInt256.lt len ⟨32⟩ = ⟨1⟩ := by
      exact ult_one (by
        simpa [show (⟨32⟩ : UInt256).toNat = 32 from by decide] using hshort)
    have hvalidLen : UInt256.sub ⟨0⟩ (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩ := by
      rw [hltLen]
      native_decide
    exact bytesStoreLiteReadLengthOfHeaderLoad
      (er := bytesStoreLiteSetChunkByteHeaderRef I) (evm := evm)
      (baseSlot := bytesStoreLiteSetChunkByteSlot I)
      (header := bytesStoreLiteSetChunkByteHeaderWord σ I) (len := len.toNat)
      (bytesStoreLiteSetChunkByteHeaderRef_length_slot evm I)
      hloadHeader
      (solidityDecodeBytesLengthHeader_short_valid hflag hlen (by simpa [hflag] using hvalidLen))
  have hpacked : checkBytesPacked (bytesStoreLiteSetChunkByteSlot I) evm = true :=
    checkBytesPacked_of_storageLoad_land_one_zero hloadHeader hflag
  have hidx31 : (bytesStoreLiteSetChunkByteIndexWord I).toNat < 31 :=
    bytesStoreLiteSetChunkByteIndex_lt31_of_short_bound (I := I) (len := len)
      hshort hbound
  have hlayout :
      bytesStoreLiteConfig.storage.layout (bytesStoreLiteSetChunkByteRef I) evm =
        some (uint8Loc (bytesStoreLiteSetChunkByteSlot I)
          ⟨31 - (bytesStoreLiteSetChunkByteIndexWord I).toNat, by omega⟩) :=
    bytesStoreLiteSetChunkByteLayoutShort (evm := evm) (I := I) hpacked hidx31
  have hstore :
      (match bytesStoreLiteConfig.storage.layout (bytesStoreLiteSetChunkByteRef I) evm with
      | some loc => storageLocStore evm loc (bytesStoreLiteSetChunkByteValue I)
      | none => none) = some evm' := by
    rw [hlayout]
    simpa [evm'] using
      bytesStoreLiteSetChunkByteStorageLocStoreShort
        (evm := evm) (σ := σ) (I := I) (len := len)
        hloadHeader hcanon hshort hbound
  have hassign :
      assignStorageRef? bytesStoreLiteConfig
        (bytesStoreLiteSetChunkByteFrame I)
        evm .storage (chunkByteRef (.var "chunkIndex") (.var "byteIndex"))
          (bytesStoreLiteSetChunkByteValue I) =
          .ok (bytesStoreLiteSetChunkByteFrame I, evm') :=
    bytesStoreLiteSetChunkByteAssignOfLength (evm := evm) (evm' := evm') (I := I)
      hloadChunks hchunkBound hlenRead hbound hstore
  have hloadChunksPost' :
      Solm.EVM.storageLoad evm' evm'.executionEnv.codeOwner ⟨1⟩ = chunksLenPost := by
    simpa [evm', storageStore_executionEnv] using hloadChunksPost
  exact bytesStoreLiteSetChunkByteBodyReturnRevertsOfPostChunksLength
    (evm := evm) (evm' := evm') (I := I) (chunksLenPost := chunksLenPost)
    hwv hassign hloadChunksPost' hchunkBoundPost

theorem bytesStoreLiteSetChunkByteLongBodyReturnRevertsOfPostChunksLength
    {evm : EVM.State} {σ : AccountMap} {I : ExecutionEnv}
    {chunksLen chunksLenPost len : UInt256}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hloadChunks : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩ = chunksLen)
    (hchunkBound : (bytesStoreLiteSetChunkByteChunkIndexWord I).toNat < chunksLen.toNat)
    (hloadChunksPost :
      Solm.EVM.storageLoad
          (Solm.EVM.storageStore evm evm.executionEnv.codeOwner
            (bytesStoreLiteSetChunkByteLongDataSlot I)
            (bytesStoreLiteSetChunkByteLongStoredWord σ I))
          evm.executionEnv.codeOwner ⟨1⟩ = chunksLenPost)
    (hchunkBoundPost :
      ¬ (bytesStoreLiteSetChunkByteChunkIndexWord I).toNat < chunksLenPost.toNat)
    (hloadHeader : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (bytesStoreLiteSetChunkByteSlot I) = bytesStoreLiteSetChunkByteHeaderWord σ I)
    (hloadData : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (bytesStoreLiteSetChunkByteLongDataSlot I) =
      bytesStoreLiteSetChunkByteLongOldWord σ I)
    (hcanon : (bytesStoreLiteSetChunkByteValueWord I).toNat < EVM.twoPow 8)
    (hlen : len = UInt256.div (bytesStoreLiteSetChunkByteHeaderWord σ I) ⟨2⟩)
    (hbound : (bytesStoreLiteSetChunkByteIndexWord I).toNat < len.toNat)
    (hflag : UInt256.land (bytesStoreLiteSetChunkByteHeaderWord σ I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (bytesStoreLiteSetChunkByteHeaderWord σ I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStoreLiteSetChunkByteHeaderWord σ I) ⟨2⟩) ⟨32⟩) ≠
          ⟨0⟩) :
    ExecTransitionBody bytesStoreLiteConfig bytesStoreLiteContract evm
      (bytesStoreLiteSetChunkByteLocals I) setChunkByteTransition.body .reverted := by
  let evm' := Solm.EVM.storageStore evm evm.executionEnv.codeOwner
    (bytesStoreLiteSetChunkByteLongDataSlot I)
    (bytesStoreLiteSetChunkByteLongStoredWord σ I)
  have hvalidLen :
      UInt256.sub (UInt256.land (bytesStoreLiteSetChunkByteHeaderWord σ I) ⟨1⟩)
        (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩ := by
    simpa [hlen] using hvalid
  have hlenRead :
      readStorageBytesLength? bytesStoreLiteConfig evm
          (bytesStoreLiteSetChunkByteHeaderRef I) =
        .ok len.toNat := by
    exact bytesStoreLiteReadLengthOfHeaderLoad
      (er := bytesStoreLiteSetChunkByteHeaderRef I) (evm := evm)
      (baseSlot := bytesStoreLiteSetChunkByteSlot I)
      (header := bytesStoreLiteSetChunkByteHeaderWord σ I) (len := len.toNat)
      (bytesStoreLiteSetChunkByteHeaderRef_length_slot evm I)
      hloadHeader
      (solidityDecodeBytesLengthHeader_long_valid hflag hlen hvalidLen)
  have hpacked : checkBytesPacked (bytesStoreLiteSetChunkByteSlot I) evm = false :=
    checkBytesPacked_of_storageLoad_land_one_ne_zero hloadHeader hflag
  have hlayout :
      bytesStoreLiteConfig.storage.layout (bytesStoreLiteSetChunkByteRef I) evm =
        some (uint8Loc (bytesStoreLiteSetChunkByteLongDataSlot I)
          ⟨31 - (bytesStoreLiteSetChunkByteLongWordIndex I).toNat, by
            have hidx := bytesStoreLiteSetChunkByteLongWordIndex_lt32 I
            omega⟩) :=
    bytesStoreLiteSetChunkByteLayoutLong (evm := evm) (I := I) hpacked
  have hstore :
      (match bytesStoreLiteConfig.storage.layout (bytesStoreLiteSetChunkByteRef I) evm with
      | some loc => storageLocStore evm loc (bytesStoreLiteSetChunkByteValue I)
      | none => none) = some evm' := by
    rw [hlayout]
    simpa [evm'] using
      bytesStoreLiteSetChunkByteStorageLocStoreLong
        (evm := evm) (σ := σ) (I := I) hloadData hcanon
  have hassign :
      assignStorageRef? bytesStoreLiteConfig
        (bytesStoreLiteSetChunkByteFrame I)
        evm .storage (chunkByteRef (.var "chunkIndex") (.var "byteIndex"))
          (bytesStoreLiteSetChunkByteValue I) =
          .ok (bytesStoreLiteSetChunkByteFrame I, evm') :=
    bytesStoreLiteSetChunkByteAssignOfLength (evm := evm) (evm' := evm') (I := I)
      hloadChunks hchunkBound hlenRead hbound hstore
  have hloadChunksPost' :
      Solm.EVM.storageLoad evm' evm'.executionEnv.codeOwner ⟨1⟩ = chunksLenPost := by
    simpa [evm', storageStore_executionEnv] using hloadChunksPost
  exact bytesStoreLiteSetChunkByteBodyReturnRevertsOfPostChunksLength
    (evm := evm) (evm' := evm') (I := I) (chunksLenPost := chunksLenPost)
    hwv hassign hloadChunksPost' hchunkBoundPost

theorem bytesStoreLiteSetChunkByteLongBodyReturnRevertsOfPostLongMalformed
    {evm : EVM.State} {σ : AccountMap} {I : ExecutionEnv}
    {chunksLen chunksLenPost len postHeaderWord : UInt256}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hloadChunks : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩ = chunksLen)
    (hchunkBound : (bytesStoreLiteSetChunkByteChunkIndexWord I).toNat < chunksLen.toNat)
    (hloadChunksPost :
      Solm.EVM.storageLoad
          (Solm.EVM.storageStore evm evm.executionEnv.codeOwner
            (bytesStoreLiteSetChunkByteLongDataSlot I)
            (bytesStoreLiteSetChunkByteLongStoredWord σ I))
          evm.executionEnv.codeOwner ⟨1⟩ = chunksLenPost)
    (hchunkBoundPost :
      (bytesStoreLiteSetChunkByteChunkIndexWord I).toNat < chunksLenPost.toNat)
    (hloadHeader : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (bytesStoreLiteSetChunkByteSlot I) = bytesStoreLiteSetChunkByteHeaderWord σ I)
    (hloadData : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (bytesStoreLiteSetChunkByteLongDataSlot I) =
      bytesStoreLiteSetChunkByteLongOldWord σ I)
    (hloadHeaderPost :
      Solm.EVM.storageLoad
          (Solm.EVM.storageStore evm evm.executionEnv.codeOwner
            (bytesStoreLiteSetChunkByteLongDataSlot I)
            (bytesStoreLiteSetChunkByteLongStoredWord σ I))
          evm.executionEnv.codeOwner (bytesStoreLiteSetChunkByteSlot I) =
        postHeaderWord)
    (hcanon : (bytesStoreLiteSetChunkByteValueWord I).toNat < EVM.twoPow 8)
    (hlen : len = UInt256.div (bytesStoreLiteSetChunkByteHeaderWord σ I) ⟨2⟩)
    (hbound : (bytesStoreLiteSetChunkByteIndexWord I).toNat < len.toNat)
    (hflag : UInt256.land (bytesStoreLiteSetChunkByteHeaderWord σ I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (bytesStoreLiteSetChunkByteHeaderWord σ I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStoreLiteSetChunkByteHeaderWord σ I) ⟨2⟩) ⟨32⟩) ≠
          ⟨0⟩)
    (hflagPost : UInt256.land postHeaderWord ⟨1⟩ ≠ ⟨0⟩)
    (hbadPost : UInt256.sub (UInt256.land postHeaderWord ⟨1⟩)
        (UInt256.lt (UInt256.div postHeaderWord ⟨2⟩) ⟨32⟩) = ⟨0⟩) :
    ExecTransitionBody bytesStoreLiteConfig bytesStoreLiteContract evm
      (bytesStoreLiteSetChunkByteLocals I) setChunkByteTransition.body .reverted := by
  let evm' := Solm.EVM.storageStore evm evm.executionEnv.codeOwner
    (bytesStoreLiteSetChunkByteLongDataSlot I)
    (bytesStoreLiteSetChunkByteLongStoredWord σ I)
  have hvalidLen :
      UInt256.sub (UInt256.land (bytesStoreLiteSetChunkByteHeaderWord σ I) ⟨1⟩)
        (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩ := by
    simpa [hlen] using hvalid
  have hlenRead :
      readStorageBytesLength? bytesStoreLiteConfig evm
          (bytesStoreLiteSetChunkByteHeaderRef I) =
        .ok len.toNat := by
    exact bytesStoreLiteReadLengthOfHeaderLoad
      (er := bytesStoreLiteSetChunkByteHeaderRef I) (evm := evm)
      (baseSlot := bytesStoreLiteSetChunkByteSlot I)
      (header := bytesStoreLiteSetChunkByteHeaderWord σ I) (len := len.toNat)
      (bytesStoreLiteSetChunkByteHeaderRef_length_slot evm I)
      hloadHeader
      (solidityDecodeBytesLengthHeader_long_valid hflag hlen hvalidLen)
  have hpacked : checkBytesPacked (bytesStoreLiteSetChunkByteSlot I) evm = false :=
    checkBytesPacked_of_storageLoad_land_one_ne_zero hloadHeader hflag
  have hlayout :
      bytesStoreLiteConfig.storage.layout (bytesStoreLiteSetChunkByteRef I) evm =
        some (uint8Loc (bytesStoreLiteSetChunkByteLongDataSlot I)
          ⟨31 - (bytesStoreLiteSetChunkByteLongWordIndex I).toNat, by
            have hidx := bytesStoreLiteSetChunkByteLongWordIndex_lt32 I
            omega⟩) :=
    bytesStoreLiteSetChunkByteLayoutLong (evm := evm) (I := I) hpacked
  have hstore :
      (match bytesStoreLiteConfig.storage.layout (bytesStoreLiteSetChunkByteRef I) evm with
      | some loc => storageLocStore evm loc (bytesStoreLiteSetChunkByteValue I)
      | none => none) = some evm' := by
    rw [hlayout]
    simpa [evm'] using
      bytesStoreLiteSetChunkByteStorageLocStoreLong
        (evm := evm) (σ := σ) (I := I) hloadData hcanon
  have hassign :
      assignStorageRef? bytesStoreLiteConfig
        (bytesStoreLiteSetChunkByteFrame I)
        evm .storage (chunkByteRef (.var "chunkIndex") (.var "byteIndex"))
          (bytesStoreLiteSetChunkByteValue I) =
          .ok (bytesStoreLiteSetChunkByteFrame I, evm') :=
    bytesStoreLiteSetChunkByteAssignOfLength (evm := evm) (evm' := evm') (I := I)
      hloadChunks hchunkBound hlenRead hbound hstore
  have hloadChunksPost' :
      Solm.EVM.storageLoad evm' evm'.executionEnv.codeOwner ⟨1⟩ = chunksLenPost := by
    simpa [evm', storageStore_executionEnv] using hloadChunksPost
  have hloadHeaderPost' :
      Solm.EVM.storageLoad evm' evm'.executionEnv.codeOwner
          (bytesStoreLiteSetChunkByteSlot I) =
        postHeaderWord := by
    simpa [evm', storageStore_executionEnv] using hloadHeaderPost
  have hlenPost :
      readStorageBytesLength? bytesStoreLiteConfig evm'
          (bytesStoreLiteSetChunkByteHeaderRef I) = .revert := by
    exact bytesStoreLiteReadLengthRevertOfHeaderLoad
      (er := bytesStoreLiteSetChunkByteHeaderRef I) (evm := evm')
      (baseSlot := bytesStoreLiteSetChunkByteSlot I)
      (header := postHeaderWord)
      (bytesStoreLiteSetChunkByteHeaderRef_length_slot evm' I)
      hloadHeaderPost'
      (by simp [solidityDecodeBytesLengthHeader, hflagPost, hbadPost])
  exact bytesStoreLiteSetChunkByteBodyReturnRevertsOfPostLengthRead
    (evm := evm) (evm' := evm') (I := I) (chunksLenPost := chunksLenPost)
    hwv hassign hloadChunksPost' hchunkBoundPost hlenPost

theorem bytesStoreLiteSetChunkByteLongBodyReturnRevertsOfPostLongLength
    {evm : EVM.State} {σ : AccountMap} {I : ExecutionEnv}
    {chunksLen chunksLenPost len lenPost postHeaderWord : UInt256}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hloadChunks : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩ = chunksLen)
    (hchunkBound : (bytesStoreLiteSetChunkByteChunkIndexWord I).toNat < chunksLen.toNat)
    (hloadChunksPost :
      Solm.EVM.storageLoad
          (Solm.EVM.storageStore evm evm.executionEnv.codeOwner
            (bytesStoreLiteSetChunkByteLongDataSlot I)
            (bytesStoreLiteSetChunkByteLongStoredWord σ I))
          evm.executionEnv.codeOwner ⟨1⟩ = chunksLenPost)
    (hchunkBoundPost :
      (bytesStoreLiteSetChunkByteChunkIndexWord I).toNat < chunksLenPost.toNat)
    (hloadHeader : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (bytesStoreLiteSetChunkByteSlot I) = bytesStoreLiteSetChunkByteHeaderWord σ I)
    (hloadData : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (bytesStoreLiteSetChunkByteLongDataSlot I) =
      bytesStoreLiteSetChunkByteLongOldWord σ I)
    (hloadHeaderPost :
      Solm.EVM.storageLoad
          (Solm.EVM.storageStore evm evm.executionEnv.codeOwner
            (bytesStoreLiteSetChunkByteLongDataSlot I)
            (bytesStoreLiteSetChunkByteLongStoredWord σ I))
          evm.executionEnv.codeOwner (bytesStoreLiteSetChunkByteSlot I) =
        postHeaderWord)
    (hcanon : (bytesStoreLiteSetChunkByteValueWord I).toNat < EVM.twoPow 8)
    (hlen : len = UInt256.div (bytesStoreLiteSetChunkByteHeaderWord σ I) ⟨2⟩)
    (hlenPost : lenPost = UInt256.div postHeaderWord ⟨2⟩)
    (hbound : (bytesStoreLiteSetChunkByteIndexWord I).toNat < len.toNat)
    (hboundPost : ¬ (bytesStoreLiteSetChunkByteIndexWord I).toNat < lenPost.toNat)
    (hflag : UInt256.land (bytesStoreLiteSetChunkByteHeaderWord σ I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (bytesStoreLiteSetChunkByteHeaderWord σ I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStoreLiteSetChunkByteHeaderWord σ I) ⟨2⟩) ⟨32⟩) ≠
          ⟨0⟩)
    (hflagPost : UInt256.land postHeaderWord ⟨1⟩ ≠ ⟨0⟩)
    (hvalidPost : UInt256.sub (UInt256.land postHeaderWord ⟨1⟩)
        (UInt256.lt (UInt256.div postHeaderWord ⟨2⟩) ⟨32⟩) ≠ ⟨0⟩) :
    ExecTransitionBody bytesStoreLiteConfig bytesStoreLiteContract evm
      (bytesStoreLiteSetChunkByteLocals I) setChunkByteTransition.body .reverted := by
  let evm' := Solm.EVM.storageStore evm evm.executionEnv.codeOwner
    (bytesStoreLiteSetChunkByteLongDataSlot I)
    (bytesStoreLiteSetChunkByteLongStoredWord σ I)
  have hvalidLen :
      UInt256.sub (UInt256.land (bytesStoreLiteSetChunkByteHeaderWord σ I) ⟨1⟩)
        (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩ := by
    simpa [hlen] using hvalid
  have hlenRead :
      readStorageBytesLength? bytesStoreLiteConfig evm
          (bytesStoreLiteSetChunkByteHeaderRef I) =
        .ok len.toNat := by
    exact bytesStoreLiteReadLengthOfHeaderLoad
      (er := bytesStoreLiteSetChunkByteHeaderRef I) (evm := evm)
      (baseSlot := bytesStoreLiteSetChunkByteSlot I)
      (header := bytesStoreLiteSetChunkByteHeaderWord σ I) (len := len.toNat)
      (bytesStoreLiteSetChunkByteHeaderRef_length_slot evm I)
      hloadHeader
      (solidityDecodeBytesLengthHeader_long_valid hflag hlen hvalidLen)
  have hpacked : checkBytesPacked (bytesStoreLiteSetChunkByteSlot I) evm = false :=
    checkBytesPacked_of_storageLoad_land_one_ne_zero hloadHeader hflag
  have hlayout :
      bytesStoreLiteConfig.storage.layout (bytesStoreLiteSetChunkByteRef I) evm =
        some (uint8Loc (bytesStoreLiteSetChunkByteLongDataSlot I)
          ⟨31 - (bytesStoreLiteSetChunkByteLongWordIndex I).toNat, by
            have hidx := bytesStoreLiteSetChunkByteLongWordIndex_lt32 I
            omega⟩) :=
    bytesStoreLiteSetChunkByteLayoutLong (evm := evm) (I := I) hpacked
  have hstore :
      (match bytesStoreLiteConfig.storage.layout (bytesStoreLiteSetChunkByteRef I) evm with
      | some loc => storageLocStore evm loc (bytesStoreLiteSetChunkByteValue I)
      | none => none) = some evm' := by
    rw [hlayout]
    simpa [evm'] using
      bytesStoreLiteSetChunkByteStorageLocStoreLong
        (evm := evm) (σ := σ) (I := I) hloadData hcanon
  have hassign :
      assignStorageRef? bytesStoreLiteConfig
        (bytesStoreLiteSetChunkByteFrame I)
        evm .storage (chunkByteRef (.var "chunkIndex") (.var "byteIndex"))
          (bytesStoreLiteSetChunkByteValue I) =
          .ok (bytesStoreLiteSetChunkByteFrame I, evm') :=
    bytesStoreLiteSetChunkByteAssignOfLength (evm := evm) (evm' := evm') (I := I)
      hloadChunks hchunkBound hlenRead hbound hstore
  have hloadChunksPost' :
      Solm.EVM.storageLoad evm' evm'.executionEnv.codeOwner ⟨1⟩ = chunksLenPost := by
    simpa [evm', storageStore_executionEnv] using hloadChunksPost
  have hloadHeaderPost' :
      Solm.EVM.storageLoad evm' evm'.executionEnv.codeOwner
          (bytesStoreLiteSetChunkByteSlot I) =
        postHeaderWord := by
    simpa [evm', storageStore_executionEnv] using hloadHeaderPost
  have hlenPostRead :
      readStorageBytesLength? bytesStoreLiteConfig evm'
          (bytesStoreLiteSetChunkByteHeaderRef I) = .ok lenPost.toNat := by
    have hvalidLenPost :
        UInt256.sub (UInt256.land postHeaderWord ⟨1⟩) (UInt256.lt lenPost ⟨32⟩) ≠
          ⟨0⟩ := by
      simpa [hlenPost] using hvalidPost
    exact bytesStoreLiteReadLengthOfHeaderLoad
      (er := bytesStoreLiteSetChunkByteHeaderRef I) (evm := evm')
      (baseSlot := bytesStoreLiteSetChunkByteSlot I)
      (header := postHeaderWord) (len := lenPost.toNat)
      (bytesStoreLiteSetChunkByteHeaderRef_length_slot evm' I)
      hloadHeaderPost'
      (solidityDecodeBytesLengthHeader_long_valid hflagPost hlenPost hvalidLenPost)
  exact bytesStoreLiteSetChunkByteBodyReturnRevertsOfPostLength
    (evm := evm) (evm' := evm') (I := I) (chunksLenPost := chunksLenPost)
    (lenPost := lenPost.toNat)
    hwv hassign hloadChunksPost' hchunkBoundPost hlenPostRead hboundPost

theorem bytesStoreLiteSetChunkByteLongBodyReturnRevertsOfPostShortLength
    {evm : EVM.State} {σ : AccountMap} {I : ExecutionEnv}
    {chunksLen chunksLenPost len lenPost postHeaderWord : UInt256}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hloadChunks : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩ = chunksLen)
    (hchunkBound : (bytesStoreLiteSetChunkByteChunkIndexWord I).toNat < chunksLen.toNat)
    (hloadChunksPost :
      Solm.EVM.storageLoad
          (Solm.EVM.storageStore evm evm.executionEnv.codeOwner
            (bytesStoreLiteSetChunkByteLongDataSlot I)
            (bytesStoreLiteSetChunkByteLongStoredWord σ I))
          evm.executionEnv.codeOwner ⟨1⟩ = chunksLenPost)
    (hchunkBoundPost :
      (bytesStoreLiteSetChunkByteChunkIndexWord I).toNat < chunksLenPost.toNat)
    (hloadHeader : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (bytesStoreLiteSetChunkByteSlot I) = bytesStoreLiteSetChunkByteHeaderWord σ I)
    (hloadData : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (bytesStoreLiteSetChunkByteLongDataSlot I) =
      bytesStoreLiteSetChunkByteLongOldWord σ I)
    (hloadHeaderPost :
      Solm.EVM.storageLoad
          (Solm.EVM.storageStore evm evm.executionEnv.codeOwner
            (bytesStoreLiteSetChunkByteLongDataSlot I)
            (bytesStoreLiteSetChunkByteLongStoredWord σ I))
          evm.executionEnv.codeOwner (bytesStoreLiteSetChunkByteSlot I) =
        postHeaderWord)
    (hcanon : (bytesStoreLiteSetChunkByteValueWord I).toNat < EVM.twoPow 8)
    (hlen : len = UInt256.div (bytesStoreLiteSetChunkByteHeaderWord σ I) ⟨2⟩)
    (hlenPost : lenPost = UInt256.land (UInt256.div postHeaderWord ⟨2⟩) ⟨127⟩)
    (hbound : (bytesStoreLiteSetChunkByteIndexWord I).toNat < len.toNat)
    (hboundPost : ¬ (bytesStoreLiteSetChunkByteIndexWord I).toNat < lenPost.toNat)
    (hflag : UInt256.land (bytesStoreLiteSetChunkByteHeaderWord σ I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (bytesStoreLiteSetChunkByteHeaderWord σ I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStoreLiteSetChunkByteHeaderWord σ I) ⟨2⟩) ⟨32⟩) ≠
          ⟨0⟩)
    (hflagPost : UInt256.land postHeaderWord ⟨1⟩ = ⟨0⟩)
    (hvalidPost : UInt256.sub (UInt256.land postHeaderWord ⟨1⟩)
        (UInt256.lt (UInt256.land (UInt256.div postHeaderWord ⟨2⟩) ⟨127⟩) ⟨32⟩) ≠
          ⟨0⟩) :
    ExecTransitionBody bytesStoreLiteConfig bytesStoreLiteContract evm
      (bytesStoreLiteSetChunkByteLocals I) setChunkByteTransition.body .reverted := by
  let evm' := Solm.EVM.storageStore evm evm.executionEnv.codeOwner
    (bytesStoreLiteSetChunkByteLongDataSlot I)
    (bytesStoreLiteSetChunkByteLongStoredWord σ I)
  have hvalidLen :
      UInt256.sub (UInt256.land (bytesStoreLiteSetChunkByteHeaderWord σ I) ⟨1⟩)
        (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩ := by
    simpa [hlen] using hvalid
  have hlenRead :
      readStorageBytesLength? bytesStoreLiteConfig evm
          (bytesStoreLiteSetChunkByteHeaderRef I) =
        .ok len.toNat := by
    exact bytesStoreLiteReadLengthOfHeaderLoad
      (er := bytesStoreLiteSetChunkByteHeaderRef I) (evm := evm)
      (baseSlot := bytesStoreLiteSetChunkByteSlot I)
      (header := bytesStoreLiteSetChunkByteHeaderWord σ I) (len := len.toNat)
      (bytesStoreLiteSetChunkByteHeaderRef_length_slot evm I)
      hloadHeader
      (solidityDecodeBytesLengthHeader_long_valid hflag hlen hvalidLen)
  have hpacked : checkBytesPacked (bytesStoreLiteSetChunkByteSlot I) evm = false :=
    checkBytesPacked_of_storageLoad_land_one_ne_zero hloadHeader hflag
  have hlayout :
      bytesStoreLiteConfig.storage.layout (bytesStoreLiteSetChunkByteRef I) evm =
        some (uint8Loc (bytesStoreLiteSetChunkByteLongDataSlot I)
          ⟨31 - (bytesStoreLiteSetChunkByteLongWordIndex I).toNat, by
            have hidx := bytesStoreLiteSetChunkByteLongWordIndex_lt32 I
            omega⟩) :=
    bytesStoreLiteSetChunkByteLayoutLong (evm := evm) (I := I) hpacked
  have hstore :
      (match bytesStoreLiteConfig.storage.layout (bytesStoreLiteSetChunkByteRef I) evm with
      | some loc => storageLocStore evm loc (bytesStoreLiteSetChunkByteValue I)
      | none => none) = some evm' := by
    rw [hlayout]
    simpa [evm'] using
      bytesStoreLiteSetChunkByteStorageLocStoreLong
        (evm := evm) (σ := σ) (I := I) hloadData hcanon
  have hassign :
      assignStorageRef? bytesStoreLiteConfig
        (bytesStoreLiteSetChunkByteFrame I)
        evm .storage (chunkByteRef (.var "chunkIndex") (.var "byteIndex"))
          (bytesStoreLiteSetChunkByteValue I) =
          .ok (bytesStoreLiteSetChunkByteFrame I, evm') :=
    bytesStoreLiteSetChunkByteAssignOfLength (evm := evm) (evm' := evm') (I := I)
      hloadChunks hchunkBound hlenRead hbound hstore
  have hloadChunksPost' :
      Solm.EVM.storageLoad evm' evm'.executionEnv.codeOwner ⟨1⟩ = chunksLenPost := by
    simpa [evm', storageStore_executionEnv] using hloadChunksPost
  have hloadHeaderPost' :
      Solm.EVM.storageLoad evm' evm'.executionEnv.codeOwner
          (bytesStoreLiteSetChunkByteSlot I) =
        postHeaderWord := by
    simpa [evm', storageStore_executionEnv] using hloadHeaderPost
  have hlenPostRead :
      readStorageBytesLength? bytesStoreLiteConfig evm'
          (bytesStoreLiteSetChunkByteHeaderRef I) = .ok lenPost.toNat := by
    have hvalidLenPost :
        UInt256.sub ⟨0⟩ (UInt256.lt lenPost ⟨32⟩) ≠ ⟨0⟩ := by
      simpa [hflagPost, hlenPost] using hvalidPost
    exact bytesStoreLiteReadLengthOfHeaderLoad
      (er := bytesStoreLiteSetChunkByteHeaderRef I) (evm := evm')
      (baseSlot := bytesStoreLiteSetChunkByteSlot I)
      (header := postHeaderWord) (len := lenPost.toNat)
      (bytesStoreLiteSetChunkByteHeaderRef_length_slot evm' I)
      hloadHeaderPost'
      (solidityDecodeBytesLengthHeader_short_valid hflagPost hlenPost
        (by simpa [← hlenPost] using hvalidPost))
  exact bytesStoreLiteSetChunkByteBodyReturnRevertsOfPostLength
    (evm := evm) (evm' := evm') (I := I) (chunksLenPost := chunksLenPost)
    (lenPost := lenPost.toNat)
    hwv hassign hloadChunksPost' hchunkBoundPost hlenPostRead hboundPost

theorem bytesStoreLiteSetChunkByteLongBodyReturnRevertsOfPostShortMalformed
    {evm : EVM.State} {σ : AccountMap} {I : ExecutionEnv}
    {chunksLen chunksLenPost len postHeaderWord : UInt256}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hloadChunks : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩ = chunksLen)
    (hchunkBound : (bytesStoreLiteSetChunkByteChunkIndexWord I).toNat < chunksLen.toNat)
    (hloadChunksPost :
      Solm.EVM.storageLoad
          (Solm.EVM.storageStore evm evm.executionEnv.codeOwner
            (bytesStoreLiteSetChunkByteLongDataSlot I)
            (bytesStoreLiteSetChunkByteLongStoredWord σ I))
          evm.executionEnv.codeOwner ⟨1⟩ = chunksLenPost)
    (hchunkBoundPost :
      (bytesStoreLiteSetChunkByteChunkIndexWord I).toNat < chunksLenPost.toNat)
    (hloadHeader : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (bytesStoreLiteSetChunkByteSlot I) = bytesStoreLiteSetChunkByteHeaderWord σ I)
    (hloadData : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (bytesStoreLiteSetChunkByteLongDataSlot I) =
      bytesStoreLiteSetChunkByteLongOldWord σ I)
    (hloadHeaderPost :
      Solm.EVM.storageLoad
          (Solm.EVM.storageStore evm evm.executionEnv.codeOwner
            (bytesStoreLiteSetChunkByteLongDataSlot I)
            (bytesStoreLiteSetChunkByteLongStoredWord σ I))
          evm.executionEnv.codeOwner (bytesStoreLiteSetChunkByteSlot I) =
        postHeaderWord)
    (hcanon : (bytesStoreLiteSetChunkByteValueWord I).toNat < EVM.twoPow 8)
    (hlen : len = UInt256.div (bytesStoreLiteSetChunkByteHeaderWord σ I) ⟨2⟩)
    (hbound : (bytesStoreLiteSetChunkByteIndexWord I).toNat < len.toNat)
    (hflag : UInt256.land (bytesStoreLiteSetChunkByteHeaderWord σ I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (bytesStoreLiteSetChunkByteHeaderWord σ I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStoreLiteSetChunkByteHeaderWord σ I) ⟨2⟩) ⟨32⟩) ≠
          ⟨0⟩)
    (hflagPost : UInt256.land postHeaderWord ⟨1⟩ = ⟨0⟩)
    (hbadPost : UInt256.sub (UInt256.land postHeaderWord ⟨1⟩)
        (UInt256.lt (UInt256.land (UInt256.div postHeaderWord ⟨2⟩) ⟨127⟩) ⟨32⟩) = ⟨0⟩) :
    ExecTransitionBody bytesStoreLiteConfig bytesStoreLiteContract evm
      (bytesStoreLiteSetChunkByteLocals I) setChunkByteTransition.body .reverted := by
  let evm' := Solm.EVM.storageStore evm evm.executionEnv.codeOwner
    (bytesStoreLiteSetChunkByteLongDataSlot I)
    (bytesStoreLiteSetChunkByteLongStoredWord σ I)
  have hvalidLen :
      UInt256.sub (UInt256.land (bytesStoreLiteSetChunkByteHeaderWord σ I) ⟨1⟩)
        (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩ := by
    simpa [hlen] using hvalid
  have hlenRead :
      readStorageBytesLength? bytesStoreLiteConfig evm
          (bytesStoreLiteSetChunkByteHeaderRef I) =
        .ok len.toNat := by
    exact bytesStoreLiteReadLengthOfHeaderLoad
      (er := bytesStoreLiteSetChunkByteHeaderRef I) (evm := evm)
      (baseSlot := bytesStoreLiteSetChunkByteSlot I)
      (header := bytesStoreLiteSetChunkByteHeaderWord σ I) (len := len.toNat)
      (bytesStoreLiteSetChunkByteHeaderRef_length_slot evm I)
      hloadHeader
      (solidityDecodeBytesLengthHeader_long_valid hflag hlen hvalidLen)
  have hpacked : checkBytesPacked (bytesStoreLiteSetChunkByteSlot I) evm = false :=
    checkBytesPacked_of_storageLoad_land_one_ne_zero hloadHeader hflag
  have hlayout :
      bytesStoreLiteConfig.storage.layout (bytesStoreLiteSetChunkByteRef I) evm =
        some (uint8Loc (bytesStoreLiteSetChunkByteLongDataSlot I)
          ⟨31 - (bytesStoreLiteSetChunkByteLongWordIndex I).toNat, by
            have hidx := bytesStoreLiteSetChunkByteLongWordIndex_lt32 I
            omega⟩) :=
    bytesStoreLiteSetChunkByteLayoutLong (evm := evm) (I := I) hpacked
  have hstore :
      (match bytesStoreLiteConfig.storage.layout (bytesStoreLiteSetChunkByteRef I) evm with
      | some loc => storageLocStore evm loc (bytesStoreLiteSetChunkByteValue I)
      | none => none) = some evm' := by
    rw [hlayout]
    simpa [evm'] using
      bytesStoreLiteSetChunkByteStorageLocStoreLong
        (evm := evm) (σ := σ) (I := I) hloadData hcanon
  have hassign :
      assignStorageRef? bytesStoreLiteConfig
        (bytesStoreLiteSetChunkByteFrame I)
        evm .storage (chunkByteRef (.var "chunkIndex") (.var "byteIndex"))
          (bytesStoreLiteSetChunkByteValue I) =
          .ok (bytesStoreLiteSetChunkByteFrame I, evm') :=
    bytesStoreLiteSetChunkByteAssignOfLength (evm := evm) (evm' := evm') (I := I)
      hloadChunks hchunkBound hlenRead hbound hstore
  have hloadChunksPost' :
      Solm.EVM.storageLoad evm' evm'.executionEnv.codeOwner ⟨1⟩ = chunksLenPost := by
    simpa [evm', storageStore_executionEnv] using hloadChunksPost
  have hloadHeaderPost' :
      Solm.EVM.storageLoad evm' evm'.executionEnv.codeOwner
          (bytesStoreLiteSetChunkByteSlot I) =
        postHeaderWord := by
    simpa [evm', storageStore_executionEnv] using hloadHeaderPost
  have hlenPost :
      readStorageBytesLength? bytesStoreLiteConfig evm'
          (bytesStoreLiteSetChunkByteHeaderRef I) = .revert := by
    have hbadPost' :
        UInt256.sub ⟨0⟩
          (UInt256.lt (UInt256.land (UInt256.div postHeaderWord ⟨2⟩) ⟨127⟩) ⟨32⟩) =
          ⟨0⟩ := by
      simpa [hflagPost] using hbadPost
    exact bytesStoreLiteReadLengthRevertOfHeaderLoad
      (er := bytesStoreLiteSetChunkByteHeaderRef I) (evm := evm')
      (baseSlot := bytesStoreLiteSetChunkByteSlot I)
      (header := postHeaderWord)
      (bytesStoreLiteSetChunkByteHeaderRef_length_slot evm' I)
      hloadHeaderPost'
      (by simp [solidityDecodeBytesLengthHeader, hflagPost, hbadPost'])
  exact bytesStoreLiteSetChunkByteBodyReturnRevertsOfPostLengthRead
    (evm := evm) (evm' := evm') (I := I) (chunksLenPost := chunksLenPost)
    hwv hassign hloadChunksPost' hchunkBoundPost hlenPost

theorem bytesStoreLiteDecode_setChunkByte {I : ExecutionEnv}
    (hsz100 : 100 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (bytesStoreLiteSetChunkByteValueWord I).toNat < EVM.twoPow 8) :
    decodeCalldata (setChunkByteTransition.params.map Param.name)
      (transitionSignature setChunkByteTransition).paramTypes I.calldata =
        some (bytesStoreLiteSetChunkByteLocals I) := by
  show decodeCalldata ["chunkIndex", "byteIndex", "value"] [uint256, uint256, uint8]
      I.calldata = some (bytesStoreLiteSetChunkByteLocals I)
  simpa [uint256, uint8, uint8Int, abiUInt256, abiUInt8,
    bytesStoreLiteSetChunkByteLocals, bytesStoreLiteSetChunkByteChunkIndexWord,
    bytesStoreLiteSetChunkByteIndexWord, bytesStoreLiteSetChunkByteValueWord] using
    decodeCalldata_uint256_uint256_uint8_ok (cd := I.calldata) (x := "chunkIndex")
      (y := "byteIndex") (z := "value") hsz100 hhi hcanon

theorem bytesStoreLiteDecode_setChunkByte_locals {I : ExecutionEnv}
    (hsz100 : 100 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (bytesStoreLiteSetChunkByteValueWord I).toNat < EVM.twoPow 8) :
    decodeCalldata (setChunkByteTransition.params.map Param.name)
      (transitionSignature setChunkByteTransition).paramTypes I.calldata =
        some (bytesStoreLiteSetChunkByteLocals I) := by
  simpa [bytesStoreLiteSetChunkByteLocals] using
    bytesStoreLiteDecode_setChunkByte (I := I) hsz100 hhi hcanon

theorem bytesStoreLiteDecode_setChunkByte_none_noncanon_value {I : ExecutionEnv}
    (hsz100 : 100 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hnc : ¬ (bytesStoreLiteSetChunkByteValueWord I).toNat < EVM.twoPow 8) :
    decodeCalldata (setChunkByteTransition.params.map Param.name)
      (transitionSignature setChunkByteTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["chunkIndex", "byteIndex", "value"] [uint256, uint256, uint8]
      I.calldata = none
  simpa [uint256, uint8, uint8Int, abiUInt256, abiUInt8,
    bytesStoreLiteSetChunkByteValueWord] using
    decodeCalldata_uint256_uint256_uint8_none_noncanon2 (cd := I.calldata)
      (x := "chunkIndex") (y := "byteIndex") (z := "value") hsz100 hhi hnc

theorem bytesStoreLiteDecode_setChunkByte_none_short {I : ExecutionEnv}
    (hshort : I.calldata.size < 100) :
    decodeCalldata (setChunkByteTransition.params.map Param.name)
      (transitionSignature setChunkByteTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["chunkIndex", "byteIndex", "value"] [uint256, uint256, uint8]
      I.calldata = none
  simpa [uint256, uint8, uint8Int, abiUInt256, abiUInt8] using
    decodeCalldata_uint256_uint256_uint8_none_short (cd := I.calldata)
      (x := "chunkIndex") (y := "byteIndex") (z := "value") hshort

theorem bytesStoreLiteDecode_setChunkByte_none_huge {I : ExecutionEnv}
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size) :
    decodeCalldata (setChunkByteTransition.params.map Param.name)
      (transitionSignature setChunkByteTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["chunkIndex", "byteIndex", "value"] [uint256, uint256, uint8]
      I.calldata = none
  simpa [uint256, uint8, uint8Int, abiUInt256, abiUInt8] using
    decodeCalldata_uint256_uint256_uint8_none_huge (cd := I.calldata)
      (x := "chunkIndex") (y := "byteIndex") (z := "value") hbig

end BytesStoreLite
