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
  have hval : valueToWord (bytesStoreLiteSetChunkByteValue I) =
      some (UInt256.ofNat (bytesStoreLiteSetChunkByteValueWord I).toNat) := by
    simp [bytesStoreLiteSetChunkByteValue, valueToWord]
    exact bytesStoreLiteWordOfIntOfNatEq (bytesStoreLiteSetChunkByteValueWord I).toNat
  have hoffVal : offFin.val = 31 - (bytesStoreLiteSetChunkByteIndexWord I).toNat := by
    rfl
  have hoffLe : offFin.val ≤ 32 := Nat.le_of_lt offFin.isLt
  have hv : (bytesStoreLiteSetChunkByteValueWord I).toNat < 256 := by
    simpa [EVM.twoPow] using hcanon
  have hoffBound : offFin.val + (1 : Fin 33).val - 1 < 32 := by
    have hidx := bytesStoreLiteSetChunkByteIndex_lt31_of_short_bound
      (I := I) (len := len) hshort hbound
    simp [offFin]
    omega
  have htarget :
      (bytesStoreLiteSetChunkByteShortStoredWord σ I).toNat =
        fromBytes'
          ((EVM.Word.toBytesLEWithSizeProof
                (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
                  (bytesStoreLiteSetChunkByteSlot I))).1.take offFin.val ++
           (EVM.Word.toBytesLEWithSizeProof
                (storageLocWriteWord
                  (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
                    (bytesStoreLiteSetChunkByteSlot I))
                  offFin.val none
                  (UInt256.ofNat (bytesStoreLiteSetChunkByteValueWord I).toNat))).1.take 1 ++
           (EVM.Word.toBytesLEWithSizeProof
                (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
                  (bytesStoreLiteSetChunkByteSlot I))).1.drop
              (offFin.val + 1)) := by
    rw [hload]
    simp only [storageLocWriteWord]
    symm
    rw [fromBytes'_append, fromBytes'_append]
    rw [fromBytes'_take_wordLE, fromBytes'_take_wordLE, fromBytes'_drop_wordLE]
    have hslen := (EVM.Word.toBytesLEWithSizeProof
      (bytesStoreLiteSetChunkByteHeaderWord σ I)).2
    have hvlen := (EVM.Word.toBytesLEWithSizeProof
      (UInt256.ofNat (bytesStoreLiteSetChunkByteValueWord I).toNat)).2
    rw [List.length_take, hslen, Nat.min_eq_left hoffLe]
    rw [List.length_append, List.length_take, hslen, Nat.min_eq_left hoffLe,
      List.length_take, hvlen, Nat.min_eq_left (by norm_num : 1 ≤ 32)]
    rw [show 8 * (offFin.val + 1) = 8 * offFin.val + 8 by ring]
    rw [show 256 ^ offFin.val = 2 ^ (8 * offFin.val) by
      rw [show (256 : Nat) = 2 ^ 8 by norm_num, ← Nat.pow_mul]]
    rw [show 256 ^ 1 = 256 by norm_num]
    rw [show (UInt256.ofNat (bytesStoreLiteSetChunkByteValueWord I).toNat).toNat % 256 =
        (bytesStoreLiteSetChunkByteValueWord I).toNat by
      rw [ulit_toNat' _ (lt_of_lt_of_le hv (by norm_num [UInt256.size]))]
      exact Nat.mod_eq_of_lt hv]
    rw [hoffVal]
    rw [show 8 * (31 - (bytesStoreLiteSetChunkByteIndexWord I).toNat) =
        (31 - (bytesStoreLiteSetChunkByteIndexWord I).toNat) * 8 by ring]
    rw [show 256 ^ (31 - (bytesStoreLiteSetChunkByteIndexWord I).toNat + 1) =
        2 ^ (((31 - (bytesStoreLiteSetChunkByteIndexWord I).toNat) * 8) + 8) by
      rw [show 256 = 2 ^ 8 by norm_num, ← Nat.pow_mul]
      congr 1
      ring]
    change
      (bytesStoreLiteSetChunkByteHeaderWord σ I).toNat %
            2 ^ ((31 - (bytesStoreLiteSetChunkByteIndexWord I).toNat) * 8) +
          2 ^ ((31 - (bytesStoreLiteSetChunkByteIndexWord I).toNat) * 8) *
            (bytesStoreLiteSetChunkByteValueWord I).toNat +
        2 ^ ((31 - (bytesStoreLiteSetChunkByteIndexWord I).toNat) * 8 + 8) *
          ((bytesStoreLiteSetChunkByteHeaderWord σ I).toNat /
            2 ^ ((31 - (bytesStoreLiteSetChunkByteIndexWord I).toNat) * 8 + 8)) =
      (bytesStoreLiteSetChunkByteShortStoredWord σ I).toNat
    exact bytesStoreLiteSetChunkByteShortStoredWord_toNat_update
      (σ := σ) (I := I) (len := len) hcanon hshort hbound
  change storageLocStore evm
      { slot := bytesStoreLiteSetChunkByteSlot I, offset := offFin, size := 1,
        hbound := hoffBound, type := .int uint8Int }
      (bytesStoreLiteSetChunkByteValue I) =
      some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner
        (bytesStoreLiteSetChunkByteSlot I)
        (bytesStoreLiteSetChunkByteShortStoredWord σ I))
  exact storageLocStore_oneByte_local evm (bytesStoreLiteSetChunkByteSlot I)
    (UInt256.ofNat (bytesStoreLiteSetChunkByteValueWord I).toNat)
    (bytesStoreLiteSetChunkByteShortStoredWord σ I)
    offFin (.int uint8Int) hoffBound
    (bytesStoreLiteSetChunkByteValue I) hval htarget

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
  have hval : valueToWord (bytesStoreLiteSetChunkByteValue I) =
      some (UInt256.ofNat (bytesStoreLiteSetChunkByteValueWord I).toNat) := by
    simp [bytesStoreLiteSetChunkByteValue, valueToWord]
    exact bytesStoreLiteWordOfIntOfNatEq (bytesStoreLiteSetChunkByteValueWord I).toNat
  have hoffVal : offFin.val = 31 - (bytesStoreLiteSetChunkByteLongWordIndex I).toNat := by
    rfl
  have hoffLe : offFin.val ≤ 32 := Nat.le_of_lt offFin.isLt
  have hv : (bytesStoreLiteSetChunkByteValueWord I).toNat < 256 := by
    simpa [EVM.twoPow] using hcanon
  have hoffBound : offFin.val + (1 : Fin 33).val - 1 < 32 := by
    simp [offFin]
    omega
  have htarget :
      (bytesStoreLiteSetChunkByteLongStoredWord σ I).toNat =
        fromBytes'
          ((EVM.Word.toBytesLEWithSizeProof
                (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
                  (bytesStoreLiteSetChunkByteLongDataSlot I))).1.take offFin.val ++
           (EVM.Word.toBytesLEWithSizeProof
                (storageLocWriteWord
                  (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
                    (bytesStoreLiteSetChunkByteLongDataSlot I))
                  offFin.val none
                  (UInt256.ofNat (bytesStoreLiteSetChunkByteValueWord I).toNat))).1.take 1 ++
           (EVM.Word.toBytesLEWithSizeProof
                (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
                  (bytesStoreLiteSetChunkByteLongDataSlot I))).1.drop
              (offFin.val + 1)) := by
    rw [hload]
    simp only [storageLocWriteWord]
    symm
    rw [fromBytes'_append, fromBytes'_append]
    rw [fromBytes'_take_wordLE, fromBytes'_take_wordLE, fromBytes'_drop_wordLE]
    have hslen := (EVM.Word.toBytesLEWithSizeProof
      (bytesStoreLiteSetChunkByteLongOldWord σ I)).2
    have hvlen := (EVM.Word.toBytesLEWithSizeProof
      (UInt256.ofNat (bytesStoreLiteSetChunkByteValueWord I).toNat)).2
    rw [List.length_take, hslen, Nat.min_eq_left hoffLe]
    rw [List.length_append, List.length_take, hslen, Nat.min_eq_left hoffLe,
      List.length_take, hvlen, Nat.min_eq_left (by norm_num : 1 ≤ 32)]
    rw [show 8 * (offFin.val + 1) = 8 * offFin.val + 8 by ring]
    rw [show 256 ^ offFin.val = 2 ^ (8 * offFin.val) by
      rw [show (256 : Nat) = 2 ^ 8 by norm_num, ← Nat.pow_mul]]
    rw [show 256 ^ 1 = 256 by norm_num]
    rw [show (UInt256.ofNat (bytesStoreLiteSetChunkByteValueWord I).toNat).toNat % 256 =
        (bytesStoreLiteSetChunkByteValueWord I).toNat by
      rw [ulit_toNat' _ (lt_of_lt_of_le hv (by norm_num [UInt256.size]))]
      exact Nat.mod_eq_of_lt hv]
    rw [hoffVal]
    rw [show 8 * (31 - (bytesStoreLiteSetChunkByteLongWordIndex I).toNat) =
        (31 - (bytesStoreLiteSetChunkByteLongWordIndex I).toNat) * 8 by ring]
    rw [show 256 ^ (31 - (bytesStoreLiteSetChunkByteLongWordIndex I).toNat + 1) =
        2 ^ (((31 - (bytesStoreLiteSetChunkByteLongWordIndex I).toNat) * 8) + 8) by
      rw [show 256 = 2 ^ 8 by norm_num, ← Nat.pow_mul]
      congr 1
      ring]
    change
      (bytesStoreLiteSetChunkByteLongOldWord σ I).toNat %
            2 ^ ((31 - (bytesStoreLiteSetChunkByteLongWordIndex I).toNat) * 8) +
          2 ^ ((31 - (bytesStoreLiteSetChunkByteLongWordIndex I).toNat) * 8) *
            (bytesStoreLiteSetChunkByteValueWord I).toNat +
        2 ^ ((31 - (bytesStoreLiteSetChunkByteLongWordIndex I).toNat) * 8 + 8) *
          ((bytesStoreLiteSetChunkByteLongOldWord σ I).toNat /
            2 ^ ((31 - (bytesStoreLiteSetChunkByteLongWordIndex I).toNat) * 8 + 8)) =
      (bytesStoreLiteSetChunkByteLongStoredWord σ I).toNat
    exact bytesStoreLiteSetChunkByteLongStoredWord_toNat_update
      (σ := σ) (I := I) hcanon
  change storageLocStore evm
      { slot := bytesStoreLiteSetChunkByteLongDataSlot I, offset := offFin, size := 1,
        hbound := hoffBound, type := .int uint8Int }
      (bytesStoreLiteSetChunkByteValue I) =
      some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner
        (bytesStoreLiteSetChunkByteLongDataSlot I)
        (bytesStoreLiteSetChunkByteLongStoredWord σ I))
  exact storageLocStore_oneByte_local evm (bytesStoreLiteSetChunkByteLongDataSlot I)
    (UInt256.ofNat (bytesStoreLiteSetChunkByteValueWord I).toNat)
    (bytesStoreLiteSetChunkByteLongStoredWord σ I)
    offFin (.int uint8Int) hoffBound
    (bytesStoreLiteSetChunkByteValue I) hval htarget

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
    simp [solm, bytesStoreLiteSetChunkByteFrame, bytesStoreLiteSetChunkByteValue,
      bytesStoreLiteSetChunkByteLocals, evalExpr?, EvalResult.ofOption]
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
  have hgetChunkIndexElem :
      (bytesStoreLiteSetChunkByteLocals I)["chunkIndex"]? =
        some (.int (Int.ofNat (bytesStoreLiteSetChunkByteChunkIndexWord I).toNat)) :=
    bytesStoreLiteSetChunkByteLocals_getElem_chunkIndex I
  have hgetByteIndexElem :
      (bytesStoreLiteSetChunkByteLocals I)["byteIndex"]? =
        some (.int (Int.ofNat (bytesStoreLiteSetChunkByteIndexWord I).toNat)) :=
    bytesStoreLiteSetChunkByteLocals_getElem_byteIndex I
  have hgetChunks :
      (bytesStoreLiteSetChunkByteLocals I).get? "chunks" = none :=
    bytesStoreLiteSetChunkByteLocals_get_chunks_none I
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
  have her :
      evalStorageRef bytesStoreLiteConfig
        (bytesStoreLiteSetChunkByteFrame I)
        evm (chunkByteRef (.var "chunkIndex") (.var "byteIndex")) =
          .ok (bytesStoreLiteSetChunkByteRef I) := by
    simp [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, evalExpr?, chunkByteRef,
      bytesStoreLiteSetChunkByteFrame, bytesStoreLiteSetChunkByteRef,
      hgetChunkIndexElem, hgetByteIndexElem,
      valueToKey?, EvalResult.ofOption, EvalResult.bind, bind, pure,
      arrayIndexInBounds?, storageTypeAt?, bytesStoreLiteConfig, bytesStoreLiteContract,
      storageDecls, storageTypeStep?, bytesSt, bytesStoreLiteStorageLayout, solidityStorageLayout,
      bytesStoreLiteLayout, bytesStoreLiteStorageLocLoad_uint256, hload, hchunkBound,
      hlenHeader,
      hbound]
  have herInline :
      evalStorageRef bytesStoreLiteConfig
        { contract := bytesStoreLiteContract, locals := bytesStoreLiteSetChunkByteLocals I }
        evm (chunkByteRef (.var "chunkIndex") (.var "byteIndex")) =
          .ok (bytesStoreLiteSetChunkByteRef I) := by
    simpa [bytesStoreLiteSetChunkByteFrame] using her
  let sourceRef : StorageRef :=
    { base := "chunks"
      steps := [.aindex (.var "chunkIndex"), .aindex (.var "byteIndex")] }
  have herInline' :
      evalStorageRef bytesStoreLiteConfig
        ({ contract := bytesStoreLiteContract, locals := bytesStoreLiteSetChunkByteLocals I } :
          Frame)
        evm sourceRef =
          .ok (bytesStoreLiteSetChunkByteRef I) := by
    simpa [sourceRef, chunkByteRef] using herInline
  rw [resolveStorageRef?]
  simp only [chunkByteRef, bytesStoreLiteSetChunkByteFrame, hgetChunks]
  rw [herInline']
  simp [bytesStoreLiteSetChunkByte_storageTypeAt, EvalResult.ofOption, EvalResult.bind, bind,
    pure]

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
  rw [assignStorageRef?]
  rw [bytesStoreLiteSetChunkByteResolveOfLength (I := I) hload hchunkBound hlen hbound]
  cases hloc : bytesStoreLiteConfig.storage.layout (bytesStoreLiteSetChunkByteRef I) evm with
  | none =>
      simp [hloc] at hstore
  | some loc =>
      have hstoreLoc :
          storageLocStore evm loc
            (.int (Int.ofNat (bytesStoreLiteSetChunkByteValueWord I).toNat)) = some evm' := by
        simpa [hloc, bytesStoreLiteSetChunkByteValue] using hstore
      have hstoreLoc' :
          storageLocStore evm loc
            (.int ((bytesStoreLiteSetChunkByteValueWord I).toNat : Int)) = some evm' := by
        simpa using hstoreLoc
      simp [bytesStoreLiteSetChunkByteValue, hloc, EvalResult.ofOption, EvalResult.bind, bind,
        pure]
      rw [hstoreLoc']

theorem bytesStoreLiteSetChunkByteShortBodyReturns
    {evm : EVM.State} {σ : AccountMap} {I : ExecutionEnv}
    {chunksLen len : UInt256} {acc : Account}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hloadChunks : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩ = chunksLen)
    (hchunkBound : (bytesStoreLiteSetChunkByteChunkIndexWord I).toNat < chunksLen.toNat)
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
    have hchunkNN :
        ¬ (((bytesStoreLiteSetChunkByteChunkIndexWord I).toNat : Int) < 0) := by omega
    have hltLen : UInt256.lt len ⟨32⟩ = ⟨1⟩ := by
      exact ult_one (by
        simpa [show (⟨32⟩ : UInt256).toNat = 32 from by decide] using hshort)
    have hvalidLen : UInt256.sub ⟨0⟩ (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩ := by
      rw [hltLen]
      native_decide
    have hloadHeaderSlot :
        Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
            (chunksDataBase + bytesStoreLiteSetChunkByteChunkIndexWord I) =
          bytesStoreLiteSetChunkByteHeaderWord σ I := by
      simpa [bytesStoreLiteSetChunkByteSlot] using hloadHeader
    simp [readStorageBytesLength?, storageNatResultToEval, bytesStoreLiteConfig,
      bytesStoreLiteStorageLayout, solidityStorageLayout, solidityReadBytesLength?,
      solidityDecodeBytesLengthHeader, bytesStoreLiteLayout, bytesStoreLiteSetChunkByteHeaderRef,
      chunksElemSlot?, nonnegativeIndexSlot?, hchunkNN, hloadHeaderSlot, hflag, ← hlen,
      hvalidLen, u256_ofNat_toNat]
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
    have hloadPostOwner :
        Solm.EVM.storageLoad evm' evm.executionEnv.codeOwner
            (bytesStoreLiteSetChunkByteSlot I) =
          bytesStoreLiteSetChunkByteShortStoredWord σ I := by
      simpa [evm'] using
        storageLoad_storageStore_same_present evm evm.executionEnv.codeOwner hacc
          (bytesStoreLiteSetChunkByteSlot I)
          (bytesStoreLiteSetChunkByteShortStoredWord σ I)
    simpa [evm', storageStore_executionEnv] using hloadPostOwner
  have hloadChunksPost :
      Solm.EVM.storageLoad evm' evm'.executionEnv.codeOwner ⟨1⟩ = chunksLen := by
    simpa [evm', storageStore_executionEnv] using
      bytesStoreLiteStorageLoadChunksLengthAfterChunkHeaderStore_eq_of_before
        (evm := evm) (chunkIndex := bytesStoreLiteSetChunkByteChunkIndexWord I)
        (val := bytesStoreLiteSetChunkByteShortStoredWord σ I) hloadChunks
  have hflagPost :
      UInt256.land (bytesStoreLiteSetChunkByteShortStoredWord σ I) ⟨1⟩ = ⟨0⟩ := by
    rw [bytesStoreLiteSetChunkByteShortStoredWord_flag_eq
      (σ := σ) (I := I) (len := len) hshort hbound, hflag]
  have hlenPost :
      readStorageBytesLength? bytesStoreLiteConfig evm'
          (bytesStoreLiteSetChunkByteHeaderRef I) =
        .ok len.toNat := by
    have hchunkNN :
        ¬ (((bytesStoreLiteSetChunkByteChunkIndexWord I).toNat : Int) < 0) := by omega
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
    have hloadPostSlot :
        Solm.EVM.storageLoad evm' evm'.executionEnv.codeOwner
            (chunksDataBase + bytesStoreLiteSetChunkByteChunkIndexWord I) =
          bytesStoreLiteSetChunkByteShortStoredWord σ I := by
      simpa [bytesStoreLiteSetChunkByteSlot] using hloadPost
    simp [readStorageBytesLength?, storageNatResultToEval, bytesStoreLiteConfig,
      bytesStoreLiteStorageLayout, solidityStorageLayout, solidityReadBytesLength?,
      solidityDecodeBytesLengthHeader, bytesStoreLiteLayout, bytesStoreLiteSetChunkByteHeaderRef,
      chunksElemSlot?, nonnegativeIndexSlot?, hchunkNN, hloadPostSlot, hflagPost,
      hlenPostWord, hvalidLen, u256_ofNat_toNat]
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
    rw [evalExpr?]
    rw [bytesStoreLiteSetChunkByteResolveOfLength
      (evm := evm') (I := I) (chunksLen := chunksLen) (len := len.toNat)
      hloadChunksPost hchunkBound hlenPost hbound]
    simp only [bind, EvalResult.bind]
    rw [Solm.readStorage?.eq_def]
    rw [hlayoutPost]
    simp [uint8St]
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

theorem bytesStoreLiteSetChunkByteLongBodyReturns
    {evm : EVM.State} {σ : AccountMap} {I : ExecutionEnv}
    {chunksLen len : UInt256} {acc : Account}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hloadChunks : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩ = chunksLen)
    (hchunkBound : (bytesStoreLiteSetChunkByteChunkIndexWord I).toNat < chunksLen.toNat)
    (hloadHeader : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (bytesStoreLiteSetChunkByteSlot I) = bytesStoreLiteSetChunkByteHeaderWord σ I)
    (hloadData : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (bytesStoreLiteSetChunkByteLongDataSlot I) =
      bytesStoreLiteSetChunkByteLongOldWord σ I)
    (hacc : evm.accountMap.find? evm.executionEnv.codeOwner = some acc)
    (hcanon : (bytesStoreLiteSetChunkByteValueWord I).toNat < EVM.twoPow 8)
    (hlen : len = UInt256.div (bytesStoreLiteSetChunkByteHeaderWord σ I) ⟨2⟩)
    (hbound : (bytesStoreLiteSetChunkByteIndexWord I).toNat < len.toNat)
    (hflag : UInt256.land (bytesStoreLiteSetChunkByteHeaderWord σ I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (bytesStoreLiteSetChunkByteHeaderWord σ I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStoreLiteSetChunkByteHeaderWord σ I) ⟨2⟩) ⟨32⟩) ≠
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
    have hchunkNN :
        ¬ (((bytesStoreLiteSetChunkByteChunkIndexWord I).toNat : Int) < 0) := by omega
    have hloadHeaderSlot :
        Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
            (chunksDataBase + bytesStoreLiteSetChunkByteChunkIndexWord I) =
          bytesStoreLiteSetChunkByteHeaderWord σ I := by
      simpa [bytesStoreLiteSetChunkByteSlot] using hloadHeader
    simp [readStorageBytesLength?, storageNatResultToEval, bytesStoreLiteConfig,
      bytesStoreLiteStorageLayout, solidityStorageLayout, solidityReadBytesLength?,
      solidityDecodeBytesLengthHeader, bytesStoreLiteLayout, bytesStoreLiteSetChunkByteHeaderRef,
      chunksElemSlot?, nonnegativeIndexSlot?, hchunkNN, hloadHeaderSlot, hflag, ← hlen,
      hvalidLen, u256_ofNat_toNat]
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
  have hloadHeaderPost :
      Solm.EVM.storageLoad evm' evm'.executionEnv.codeOwner
          (bytesStoreLiteSetChunkByteSlot I) =
        bytesStoreLiteSetChunkByteHeaderWord σ I := by
    simpa [evm', storageStore_executionEnv, bytesStoreLiteSetChunkByteLongDataSlot] using
      bytesStoreLiteStorageLoadBytesHeaderAfterDataStore_eq_of_before
        (evm := evm) (baseSlot := bytesStoreLiteSetChunkByteSlot I)
        (idx := bytesStoreLiteSetChunkByteIndexWord I)
        (val := bytesStoreLiteSetChunkByteLongStoredWord σ I) hloadHeader
  have hloadChunksPost :
      Solm.EVM.storageLoad evm' evm'.executionEnv.codeOwner ⟨1⟩ = chunksLen := by
    simpa [evm', storageStore_executionEnv, bytesStoreLiteSetChunkByteLongDataSlot] using
      bytesStoreLiteStorageLoadChunksLengthAfterChunkDataStore_eq_of_before
        (evm := evm) (chunkIndex := bytesStoreLiteSetChunkByteChunkIndexWord I)
        (idx := bytesStoreLiteSetChunkByteIndexWord I)
        (val := bytesStoreLiteSetChunkByteLongStoredWord σ I) hloadChunks
  have hlenPost :
      readStorageBytesLength? bytesStoreLiteConfig evm'
          (bytesStoreLiteSetChunkByteHeaderRef I) =
        .ok len.toNat := by
    have hchunkNN :
        ¬ (((bytesStoreLiteSetChunkByteChunkIndexWord I).toNat : Int) < 0) := by omega
    have hloadHeaderPostSlot :
        Solm.EVM.storageLoad evm' evm'.executionEnv.codeOwner
            (chunksDataBase + bytesStoreLiteSetChunkByteChunkIndexWord I) =
          bytesStoreLiteSetChunkByteHeaderWord σ I := by
      simpa [bytesStoreLiteSetChunkByteSlot] using hloadHeaderPost
    simp [readStorageBytesLength?, storageNatResultToEval, bytesStoreLiteConfig,
      bytesStoreLiteStorageLayout, solidityStorageLayout, solidityReadBytesLength?,
      solidityDecodeBytesLengthHeader, bytesStoreLiteLayout, bytesStoreLiteSetChunkByteHeaderRef,
      chunksElemSlot?, nonnegativeIndexSlot?, hchunkNN, hloadHeaderPostSlot, hflag, ← hlen,
      hvalidLen, u256_ofNat_toNat]
  have hpackedPost : checkBytesPacked (bytesStoreLiteSetChunkByteSlot I) evm' = false :=
    checkBytesPacked_of_storageLoad_land_one_ne_zero hloadHeaderPost hflag
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
    simpa [evm', storageStore_executionEnv] using
      storageLoad_storageStore_same_present evm evm.executionEnv.codeOwner hacc
        (bytesStoreLiteSetChunkByteLongDataSlot I)
        (bytesStoreLiteSetChunkByteLongStoredWord σ I)
  have hret :
      evalExpr? bytesStoreLiteConfig
        (bytesStoreLiteSetChunkByteFrame I)
        evm' (.storage (chunkByteRef (.var "chunkIndex") (.var "byteIndex"))) =
          .ok (bytesStoreLiteSetChunkByteValue I) := by
    rw [evalExpr?]
    rw [bytesStoreLiteSetChunkByteResolveOfLength
      (evm := evm') (I := I) (chunksLen := chunksLen) (len := len.toNat)
      hloadChunksPost hchunkBound hlenPost hbound]
    simp only [bind, EvalResult.bind]
    rw [Solm.readStorage?.eq_def]
    rw [hlayoutPost]
    simp [uint8St]
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
  have hgetChunkIndexElem :
      (bytesStoreLiteSetChunkByteLocals I)["chunkIndex"]? =
        some (.int (Int.ofNat (bytesStoreLiteSetChunkByteChunkIndexWord I).toNat)) :=
    bytesStoreLiteSetChunkByteLocals_getElem_chunkIndex I
  have hgetByteIndexElem :
      (bytesStoreLiteSetChunkByteLocals I)["byteIndex"]? =
        some (.int (Int.ofNat (bytesStoreLiteSetChunkByteIndexWord I).toNat)) :=
    bytesStoreLiteSetChunkByteLocals_getElem_byteIndex I
  have hgetChunks :
      (bytesStoreLiteSetChunkByteLocals I).get? "chunks" = none :=
    bytesStoreLiteSetChunkByteLocals_get_chunks_none I
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
  have her :
      evalStorageRef bytesStoreLiteConfig
        (bytesStoreLiteSetChunkByteFrame I)
        evm (chunkByteRef (.var "chunkIndex") (.var "byteIndex")) = .revert := by
    simp [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, evalExpr?, chunkByteRef,
      bytesStoreLiteSetChunkByteFrame, hgetChunkIndexElem, hgetByteIndexElem,
      valueToKey?, EvalResult.ofOption, EvalResult.bind, bind, pure,
      arrayIndexInBounds?, storageTypeAt?, bytesStoreLiteConfig, bytesStoreLiteContract,
      storageDecls, storageTypeStep?, bytesSt, bytesStoreLiteStorageLayout, solidityStorageLayout,
      bytesStoreLiteLayout, bytesStoreLiteStorageLocLoad_uint256, hload, hchunkBound,
      hlenHeader, hbound]
  have herInline :
      evalStorageRef bytesStoreLiteConfig
        { contract := bytesStoreLiteContract, locals := bytesStoreLiteSetChunkByteLocals I }
        evm (chunkByteRef (.var "chunkIndex") (.var "byteIndex")) = .revert := by
    simpa [bytesStoreLiteSetChunkByteFrame] using her
  rw [resolveStorageRef?]
  simp only [chunkByteRef, bytesStoreLiteSetChunkByteFrame, hgetChunks]
  change (match evalStorageRef bytesStoreLiteConfig
      { contract := bytesStoreLiteContract, locals := bytesStoreLiteSetChunkByteLocals I }
      evm (chunkByteRef (.var "chunkIndex") (.var "byteIndex")) with
    | .ok er => do
        let ty ← EvalResult.ofOption EvalError.storageError
          (storageTypeAt? bytesStoreLiteContract.storage er)
        pure (er, ty)
    | .revert => .revert
    | .error e => .error e) = .revert
  rw [herInline]

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
    simp [solm, bytesStoreLiteSetChunkByteFrame, bytesStoreLiteSetChunkByteValue,
      bytesStoreLiteSetChunkByteLocals, evalExpr?, EvalResult.ofOption]
  have hassign :
      assignStorageRef? bytesStoreLiteConfig solm evm .storage
        (chunkByteRef (.var "chunkIndex") (.var "byteIndex"))
          (bytesStoreLiteSetChunkByteValue I) = .revert := by
    rw [assignStorageRef?]
    rw [bytesStoreLiteSetChunkByteResolveRevertsOfLength
      (evm := evm) (I := I) (chunksLen := chunksLen) (len := len)
      hload hchunkBound hlen hbound]
    rfl
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
  have hgetChunkIndexElem :
      (bytesStoreLiteSetChunkByteLocals I)["chunkIndex"]? =
        some (.int (Int.ofNat (bytesStoreLiteSetChunkByteChunkIndexWord I).toNat)) :=
    bytesStoreLiteSetChunkByteLocals_getElem_chunkIndex I
  have hgetByteIndexElem :
      (bytesStoreLiteSetChunkByteLocals I)["byteIndex"]? =
        some (.int (Int.ofNat (bytesStoreLiteSetChunkByteIndexWord I).toNat)) :=
    bytesStoreLiteSetChunkByteLocals_getElem_byteIndex I
  have hgetChunks :
      (bytesStoreLiteSetChunkByteLocals I).get? "chunks" = none :=
    bytesStoreLiteSetChunkByteLocals_get_chunks_none I
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
  have her :
      evalStorageRef bytesStoreLiteConfig
        (bytesStoreLiteSetChunkByteFrame I)
        evm (chunkByteRef (.var "chunkIndex") (.var "byteIndex")) = .revert := by
    simp [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, evalExpr?, chunkByteRef,
      bytesStoreLiteSetChunkByteFrame, hgetChunkIndexElem, hgetByteIndexElem,
      valueToKey?, EvalResult.ofOption, EvalResult.bind, bind, pure,
      arrayIndexInBounds?, storageTypeAt?, bytesStoreLiteConfig, bytesStoreLiteContract,
      storageDecls, storageTypeStep?, bytesSt, bytesStoreLiteStorageLayout, solidityStorageLayout,
      bytesStoreLiteLayout, bytesStoreLiteStorageLocLoad_uint256, hload, hchunkBound,
      hlenHeader]
  have herInline :
      evalStorageRef bytesStoreLiteConfig
        { contract := bytesStoreLiteContract, locals := bytesStoreLiteSetChunkByteLocals I }
        evm (chunkByteRef (.var "chunkIndex") (.var "byteIndex")) = .revert := by
    simpa [bytesStoreLiteSetChunkByteFrame] using her
  rw [resolveStorageRef?]
  simp only [chunkByteRef, bytesStoreLiteSetChunkByteFrame, hgetChunks]
  change (match evalStorageRef bytesStoreLiteConfig
      { contract := bytesStoreLiteContract, locals := bytesStoreLiteSetChunkByteLocals I }
      evm (chunkByteRef (.var "chunkIndex") (.var "byteIndex")) with
    | .ok er => do
        let ty ← EvalResult.ofOption EvalError.storageError
          (storageTypeAt? bytesStoreLiteContract.storage er)
        pure (er, ty)
    | .revert => .revert
    | .error e => .error e) = .revert
  rw [herInline]

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
    simp [solm, bytesStoreLiteSetChunkByteFrame, bytesStoreLiteSetChunkByteValue,
      bytesStoreLiteSetChunkByteLocals, evalExpr?, EvalResult.ofOption]
  have hassign :
      assignStorageRef? bytesStoreLiteConfig solm evm .storage
        (chunkByteRef (.var "chunkIndex") (.var "byteIndex"))
          (bytesStoreLiteSetChunkByteValue I) = .revert := by
    rw [assignStorageRef?]
    rw [bytesStoreLiteSetChunkByteResolveRevertsOfLengthRead
      (evm := evm) (I := I) (chunksLen := chunksLen) hload hchunkBound hlen]
    rfl
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
  have hgetIndexElem :
      (bytesStoreLiteSetChunkByteLocals I)["chunkIndex"]? =
        some (.int (Int.ofNat (bytesStoreLiteSetChunkByteChunkIndexWord I).toNat)) :=
    bytesStoreLiteSetChunkByteLocals_getElem_chunkIndex I
  have her :
      evalStorageRef bytesStoreLiteConfig
        (bytesStoreLiteSetChunkByteFrame I)
        evm (chunkByteRef (.var "chunkIndex") (.var "byteIndex")) = .revert := by
    simp [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, evalExpr?, chunkByteRef,
      bytesStoreLiteSetChunkByteFrame, hgetIndexElem, valueToKey?, EvalResult.ofOption,
      EvalResult.bind, bind, pure, arrayIndexInBounds?, storageTypeAt?, bytesStoreLiteConfig,
      bytesStoreLiteContract, storageDecls, bytesSt, bytesStoreLiteStorageLayout,
      solidityStorageLayout, bytesStoreLiteLayout, bytesStoreLiteStorageLocLoad_uint256,
      hload, hbound]
  have hgetChunksGet :
      (bytesStoreLiteSetChunkByteLocals I).get? "chunks" = none :=
    bytesStoreLiteSetChunkByteLocals_get_chunks_none I
  have herInline :
      evalStorageRef bytesStoreLiteConfig
        { contract := bytesStoreLiteContract, locals := bytesStoreLiteSetChunkByteLocals I }
        evm (chunkByteRef (.var "chunkIndex") (.var "byteIndex")) = .revert := by
    simpa [bytesStoreLiteSetChunkByteFrame] using her
  rw [resolveStorageRef?]
  simp only [chunkByteRef, bytesStoreLiteSetChunkByteFrame, hgetChunksGet]
  change (match evalStorageRef bytesStoreLiteConfig
      { contract := bytesStoreLiteContract, locals := bytesStoreLiteSetChunkByteLocals I }
      evm (chunkByteRef (.var "chunkIndex") (.var "byteIndex")) with
    | .ok er => do
        let ty ← EvalResult.ofOption EvalError.storageError
          (storageTypeAt? bytesStoreLiteContract.storage er)
        pure (er, ty)
    | .revert => .revert
    | .error e => .error e) = .revert
  rw [herInline]

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
    simp [solm, bytesStoreLiteSetChunkByteFrame, bytesStoreLiteSetChunkByteValue,
      bytesStoreLiteSetChunkByteLocals, evalExpr?, EvalResult.ofOption]
  have hassign :
      assignStorageRef? bytesStoreLiteConfig solm evm .storage
        (chunkByteRef (.var "chunkIndex") (.var "byteIndex"))
          (bytesStoreLiteSetChunkByteValue I) = .revert := by
    rw [assignStorageRef?]
    rw [bytesStoreLiteSetChunkByteResolveRevertsOfChunksLength
      (evm := evm) (I := I) (chunksLen := chunksLen) hload hbound]
    rfl
  exact ExecFuncBody.execBlockRevert <|
    ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consRevert (ExecStmt.assignStoreRevert hvalue hassign)

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
