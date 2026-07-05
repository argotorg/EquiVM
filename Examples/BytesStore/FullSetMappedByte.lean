import Examples.BytesStore.FullSetMapped
import Examples.BytesStore.FullSetChunkByte

/-!
# BytesStore — `setMappedByte(uint256,uint256,uint8)` runtime slice

This split module starts the final full-contract setter arm.  The ABI shape matches
`setChunkByte(uint256,uint256,uint8)`, while the bytes header slot is the mapping value slot
`keccak256(key, 4)`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000
set_option maxHeartbeats 4000000

namespace BytesStore

def bytesStoreSetMappedByteKeyWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 4

def bytesStoreSetMappedByteIndexWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 36

def bytesStoreSetMappedByteValueWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 68

def bytesStoreSetMappedByteLocals (I : ExecutionEnv) : Store :=
  (((∅ : Store).insert "key"
    (.int (Int.ofNat (bytesStoreSetMappedByteKeyWord I).toNat))).insert "byteIndex"
    (.int (Int.ofNat (bytesStoreSetMappedByteIndexWord I).toNat))).insert "value"
    (.int (Int.ofNat (bytesStoreSetMappedByteValueWord I).toNat))

theorem bytesStoreSetMappedByteLocals_get_key (I : ExecutionEnv) :
    (bytesStoreSetMappedByteLocals I).get? "key" =
      some (.int (Int.ofNat (bytesStoreSetMappedByteKeyWord I).toNat)) := by
  rw [bytesStoreSetMappedByteLocals]
  rw [store_get_ne (h := by decide)]
  rw [store_get_ne (h := by decide)]
  exact store_get_self (∅ : Store) "key"
    (.int (Int.ofNat (bytesStoreSetMappedByteKeyWord I).toNat))

theorem bytesStoreSetMappedByteLocals_getElem_key (I : ExecutionEnv) :
    (bytesStoreSetMappedByteLocals I)["key"]? =
      some (.int (Int.ofNat (bytesStoreSetMappedByteKeyWord I).toNat)) := by
  simpa [Std.HashMap.get?_eq_getElem?] using
    bytesStoreSetMappedByteLocals_get_key I

theorem bytesStoreSetMappedByteLocals_get_byteIndex (I : ExecutionEnv) :
    (bytesStoreSetMappedByteLocals I).get? "byteIndex" =
      some (.int (Int.ofNat (bytesStoreSetMappedByteIndexWord I).toNat)) := by
  rw [bytesStoreSetMappedByteLocals]
  rw [store_get_ne (h := by decide)]
  exact store_get_self ((∅ : Store).insert "key"
    (.int (Int.ofNat (bytesStoreSetMappedByteKeyWord I).toNat))) "byteIndex"
    (.int (Int.ofNat (bytesStoreSetMappedByteIndexWord I).toNat))

theorem bytesStoreSetMappedByteLocals_getElem_byteIndex (I : ExecutionEnv) :
    (bytesStoreSetMappedByteLocals I)["byteIndex"]? =
      some (.int (Int.ofNat (bytesStoreSetMappedByteIndexWord I).toNat)) := by
  simpa [Std.HashMap.get?_eq_getElem?] using
    bytesStoreSetMappedByteLocals_get_byteIndex I

theorem bytesStoreSetMappedByteLocals_get_mapped_none (I : ExecutionEnv) :
    (bytesStoreSetMappedByteLocals I).get? "mapped" = none := by
  rw [bytesStoreSetMappedByteLocals]
  rw [store_get_ne (h := by decide)]
  rw [store_get_ne (h := by decide)]
  rw [store_get_ne (h := by decide)]
  simp

theorem bytesStoreSetMappedByteLocals_getElem_mapped_none (I : ExecutionEnv) :
    (bytesStoreSetMappedByteLocals I)["mapped"]? = none := by
  simpa [Std.HashMap.get?_eq_getElem?] using
    bytesStoreSetMappedByteLocals_get_mapped_none I

def bytesStoreSetMappedByteRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "mapped"
    steps := [
      .mindex (.int (Int.ofNat (bytesStoreSetMappedByteKeyWord I).toNat)),
      .aindex (.int (Int.ofNat (bytesStoreSetMappedByteIndexWord I).toNat))] }

def bytesStoreSetMappedByteHeaderRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "mapped"
    steps := [.mindex (.int (Int.ofNat (bytesStoreSetMappedByteKeyWord I).toNat))] }

def bytesStoreSetMappedByteValue (I : ExecutionEnv) : Value :=
  .int (Int.ofNat (bytesStoreSetMappedByteValueWord I).toNat)

def bytesStoreSetMappedByteFrame (I : ExecutionEnv) : Frame :=
  { contract := bytesStoreContract, locals := bytesStoreSetMappedByteLocals I }

def bytesStoreSetMappedByteSlot (I : ExecutionEnv) : UInt256 :=
  bytesStoreSetMappedSlotOf (bytesStoreSetMappedByteKeyWord I)

theorem bytesStoreSetMappedByteHeaderRef_length_slot (evm : EVM.State) (I : ExecutionEnv) :
    ∃ loc, bytesStoreLayout
        { bytesStoreSetMappedByteHeaderRef I with
          steps := (bytesStoreSetMappedByteHeaderRef I).steps ++ [.length] } evm =
          some loc ∧
        loc.slot = bytesStoreSetMappedByteSlot I := by
  simpa [bytesStoreSetMappedByteHeaderRef, bytesStoreSetMappedByteSlot,
    bytesStoreSetMappedRefOf]
    using bytesStoreSetMappedRefOf_length_slot evm (bytesStoreSetMappedByteKeyWord I)

def bytesStoreSetMappedByteHeaderWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  (σ.find? I.codeOwner |>.option ⟨0⟩
    (fun acc => acc.storage.findD (bytesStoreSetMappedByteSlot I) ⟨0⟩))

theorem bytesStoreSetMappedByteHeaderWord_eq_of_accountMapEquiv
    {σ_evm σ_solm : AccountMap} {I : ExecutionEnv}
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    bytesStoreSetMappedByteHeaderWord σ_evm I =
      bytesStoreSetMappedByteHeaderWord σ_solm I :=
  accountMapEquiv_storage_findD hAccounts I.codeOwner
    (bytesStoreSetMappedByteSlot I) ⟨0⟩

theorem bytesStoreStorageLoadSetMappedByteHeader_initState_of_accountMapEquiv
    {cA : Batteries.RBSet AccountAddress compare} {gh : BlockHeader} {bl : ProcessedBlocks}
    {σ_evm σ_solm σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : Sat256}
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    Solm.EVM.storageLoad (initState cA gh bl σ_solm σ₀ g A I)
        (initState cA gh bl σ_solm σ₀ g A I).executionEnv.codeOwner
        (bytesStoreSetMappedByteSlot I) =
      bytesStoreSetMappedByteHeaderWord σ_evm I := by
  simpa [bytesStoreSetMappedByteHeaderWord] using
    bytesStoreStorageLoad_initState_of_accountMapEquiv
      (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
      (I := I) (g := g) (bytesStoreSetMappedByteSlot I) hAccounts

theorem bytesStoreStorageLoadSetMappedByteHeader_of_accountMapEquiv
    {evm : EVM.State} {σ : AccountMap} {I : ExecutionEnv}
    (howner : evm.executionEnv.codeOwner = I.codeOwner)
    (hAccounts : accountMapEquiv σ evm.accountMap) :
    Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (bytesStoreSetMappedByteSlot I) =
      bytesStoreSetMappedByteHeaderWord σ I := by
  exact (accountStorageWord_eq_storageLoad_of_accountMapEquiv
    (owner := I.codeOwner) (slot := bytesStoreSetMappedByteSlot I)
    howner hAccounts).symm

def bytesStoreSetMappedByteShortScale (I : ExecutionEnv) : UInt256 :=
  UInt256.exp ⟨256⟩ (UInt256.sub ⟨31⟩ (bytesStoreSetMappedByteIndexWord I))

def bytesStoreSetMappedByteShortStoredWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.lor
    (UInt256.mul
      (UInt256.div (UInt256.shiftLeft (bytesStoreSetMappedByteValueWord I) ⟨248⟩)
        (UInt256.shiftLeft ⟨1⟩ ⟨248⟩))
      (bytesStoreSetMappedByteShortScale I))
    (UInt256.land
      (UInt256.lnot (UInt256.mul ⟨255⟩ (bytesStoreSetMappedByteShortScale I)))
      (bytesStoreSetMappedByteHeaderWord σ I))

def bytesStoreSetMappedByteLongWordIndex (I : ExecutionEnv) : UInt256 :=
  UInt256.mod (bytesStoreSetMappedByteIndexWord I) ⟨32⟩

def bytesStoreSetMappedByteLongDataSlot (I : ExecutionEnv) : UInt256 :=
  bytesLikeDataBase (bytesStoreSetMappedByteSlot I) +
    UInt256.div (bytesStoreSetMappedByteIndexWord I) ⟨32⟩

def bytesStoreSetMappedByteLongScale (I : ExecutionEnv) : UInt256 :=
  UInt256.exp ⟨256⟩ (UInt256.sub ⟨31⟩ (bytesStoreSetMappedByteLongWordIndex I))

def bytesStoreSetMappedByteLongOldWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  (σ.find? I.codeOwner |>.option ⟨0⟩
    (fun acc => acc.storage.findD (bytesStoreSetMappedByteLongDataSlot I) ⟨0⟩))

theorem bytesStoreSetMappedByteLongOldWord_eq_of_accountMapEquiv
    {σ_evm σ_solm : AccountMap} {I : ExecutionEnv}
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    bytesStoreSetMappedByteLongOldWord σ_evm I =
      bytesStoreSetMappedByteLongOldWord σ_solm I :=
  accountMapEquiv_storage_findD hAccounts I.codeOwner
    (bytesStoreSetMappedByteLongDataSlot I) ⟨0⟩

theorem bytesStoreStorageLoadSetMappedByteLongData_initState_of_accountMapEquiv
    {cA : Batteries.RBSet AccountAddress compare} {gh : BlockHeader} {bl : ProcessedBlocks}
    {σ_evm σ_solm σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : Sat256}
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    Solm.EVM.storageLoad (initState cA gh bl σ_solm σ₀ g A I)
        (initState cA gh bl σ_solm σ₀ g A I).executionEnv.codeOwner
        (bytesStoreSetMappedByteLongDataSlot I) =
      bytesStoreSetMappedByteLongOldWord σ_evm I := by
  simpa [bytesStoreSetMappedByteLongOldWord] using
    bytesStoreStorageLoad_initState_of_accountMapEquiv
      (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
      (I := I) (g := g) (bytesStoreSetMappedByteLongDataSlot I) hAccounts

def bytesStoreSetMappedByteLongStoredWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.lor
    (UInt256.mul
      (UInt256.div (UInt256.shiftLeft (bytesStoreSetMappedByteValueWord I) ⟨248⟩)
        (UInt256.shiftLeft ⟨1⟩ ⟨248⟩))
      (bytesStoreSetMappedByteLongScale I))
    (UInt256.land
      (UInt256.lnot (UInt256.mul ⟨255⟩ (bytesStoreSetMappedByteLongScale I)))
      (bytesStoreSetMappedByteLongOldWord σ I))

theorem bytesStoreSetMappedByteKeyWord_eq_setMappedKeyWord (I : ExecutionEnv) :
    bytesStoreSetMappedByteKeyWord I = bytesStoreSetMappedKeyWord I := by
  rfl

theorem bytesStoreSetMappedByteIndexWord_eq_setChunkByteIndexWord (I : ExecutionEnv) :
    bytesStoreSetMappedByteIndexWord I = bytesStoreSetChunkByteIndexWord I := by
  rfl

theorem bytesStoreSetMappedByteValueWord_eq_setChunkByteValueWord (I : ExecutionEnv) :
    bytesStoreSetMappedByteValueWord I = bytesStoreSetChunkByteValueWord I := by
  rfl

theorem bytesStoreSetMappedByteSlotHash (I : ExecutionEnv) :
    UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC
          ((twoWordHashMem (bytesStoreSetMappedByteKeyWord I) ⟨4⟩ solcFreePtrMem
            ).readWithPadding 0 64))) =
      bytesStoreSetMappedByteSlot I := by
  rw [twoWordHashMem_read0_64 (bytesStoreSetMappedByteKeyWord I) ⟨4⟩
    solcFreePtrMem_size]
  unfold bytesStoreSetMappedByteSlot bytesStoreSetMappedSlotOf mappedValueSlot
  rw [keyValueToWord_uint256]
  exact mappingSlot_single (bytesStoreSetMappedByteKeyWord I) ⟨4⟩

theorem bytesStoreSetMappedByteLongWordIndex_toNat (I : ExecutionEnv) :
    (bytesStoreSetMappedByteLongWordIndex I).toNat =
      (bytesStoreSetMappedByteIndexWord I).toNat % 32 := by
  rw [bytesStoreSetMappedByteLongWordIndex]
  unfold UInt256.mod
  rw [if_neg (by native_decide)]
  rfl

theorem bytesStoreSetMappedByteLongWordIndex_lt32 (I : ExecutionEnv) :
    (bytesStoreSetMappedByteLongWordIndex I).toNat < 32 := by
  rw [bytesStoreSetMappedByteLongWordIndex_toNat]
  exact Nat.mod_lt _ (by decide : 0 < 32)

theorem bytesStoreSetMappedByteLongWordIndex_eq_index_of_lt32
    {I : ExecutionEnv}
    (hidx : (bytesStoreSetMappedByteIndexWord I).toNat < 32) :
    bytesStoreSetMappedByteLongWordIndex I =
      bytesStoreSetMappedByteIndexWord I := by
  apply u256_inj
  rw [bytesStoreSetMappedByteLongWordIndex_toNat]
  exact Nat.mod_eq_of_lt hidx

theorem bytesStoreSetMappedByte_storageTypeAt {I : ExecutionEnv} :
    storageTypeAt? bytesStoreContract.storage (bytesStoreSetMappedByteRef I) =
      some uint8St := by
  simp [bytesStoreSetMappedByteRef, storageTypeAt?, bytesStoreContract, storageDecls,
    bytesSt, uint8St, uint8Int, storageTypeStep?]

theorem bytesStoreSetMappedByteLayoutShort {evm : EVM.State} {I : ExecutionEnv}
    (hpacked : checkBytesPacked (bytesStoreSetMappedByteSlot I) evm = true)
    (hidx : (bytesStoreSetMappedByteIndexWord I).toNat < 31) :
    bytesStoreConfig.storage.layout (bytesStoreSetMappedByteRef I) evm =
      some (uint8Loc (bytesStoreSetMappedByteSlot I)
        ⟨31 - (bytesStoreSetMappedByteIndexWord I).toNat, by omega⟩) := by
  have hbyteNN :
      ¬ (((bytesStoreSetMappedByteIndexWord I).toNat : Int) < 0) := by omega
  change bytesLikeByteLoc?
      (mappedValueSlot (.int (Int.ofNat (bytesStoreSetMappedByteKeyWord I).toNat)))
      (.int (Int.ofNat (bytesStoreSetMappedByteIndexWord I).toNat)) evm =
        some (uint8Loc (bytesStoreSetMappedByteSlot I)
          ⟨31 - (bytesStoreSetMappedByteIndexWord I).toNat, by omega⟩)
  have hpackedMapped :
      checkBytesPacked
          (mappedValueSlot (.int ((bytesStoreSetMappedByteKeyWord I).toNat : Int)))
          evm = true := by
    simpa [bytesStoreSetMappedByteSlot, bytesStoreSetMappedSlotOf] using hpacked
  simp [bytesLikeByteLoc?, hbyteNN, hpackedMapped, hidx,
    bytesStoreSetMappedByteSlot, bytesStoreSetMappedSlotOf]

theorem bytesStoreSetMappedByteLayoutLong {evm : EVM.State} {I : ExecutionEnv}
    (hpacked : checkBytesPacked (bytesStoreSetMappedByteSlot I) evm = false) :
    bytesStoreConfig.storage.layout (bytesStoreSetMappedByteRef I) evm =
      some (uint8Loc (bytesStoreSetMappedByteLongDataSlot I)
        ⟨31 - (bytesStoreSetMappedByteLongWordIndex I).toNat, by
          have hidx := bytesStoreSetMappedByteLongWordIndex_lt32 I
          omega⟩) := by
  have hbyteNN :
      ¬ (((bytesStoreSetMappedByteIndexWord I).toNat : Int) < 0) := by omega
  change bytesLikeByteLoc?
      (mappedValueSlot (.int (Int.ofNat (bytesStoreSetMappedByteKeyWord I).toNat)))
      (.int (Int.ofNat (bytesStoreSetMappedByteIndexWord I).toNat)) evm =
        some (uint8Loc (bytesStoreSetMappedByteLongDataSlot I)
          ⟨31 - (bytesStoreSetMappedByteLongWordIndex I).toNat, by
            have hidx := bytesStoreSetMappedByteLongWordIndex_lt32 I
            omega⟩)
  have hpackedMapped :
      checkBytesPacked
          (mappedValueSlot (.int ((bytesStoreSetMappedByteKeyWord I).toNat : Int)))
          evm = false := by
    simpa [bytesStoreSetMappedByteSlot, bytesStoreSetMappedSlotOf] using hpacked
  rw [bytesStoreSetMappedByteLongDataSlot, u256_div32_eq_ofNat_toNat_div]
  simp [bytesLikeByteLoc?, hbyteNN, hpackedMapped,
    bytesStoreSetMappedByteSlot, bytesStoreSetMappedSlotOf,
    bytesStoreSetMappedByteLongWordIndex_toNat]

theorem bytesStoreSetMappedByteIndex_lt31_of_short_bound {I : ExecutionEnv}
    {len : UInt256}
    (hshort : len.toNat < 32)
    (hbound : (bytesStoreSetMappedByteIndexWord I).toNat < len.toNat) :
    (bytesStoreSetMappedByteIndexWord I).toNat < 31 := by
  omega

theorem bytesStoreSetMappedByteValueHighShiftDiv
    {I : ExecutionEnv}
    (hcanon : (bytesStoreSetMappedByteValueWord I).toNat < EVM.twoPow 8) :
    UInt256.div (UInt256.shiftLeft (bytesStoreSetMappedByteValueWord I) ⟨248⟩)
        (UInt256.shiftLeft ⟨1⟩ ⟨248⟩) =
      bytesStoreSetMappedByteValueWord I := by
  simpa [bytesStoreSetMappedByteValueWord_eq_setChunkByteValueWord] using
    bytesStoreSetChunkByteValueHighShiftDiv (I := I) hcanon

theorem bytesStoreSetMappedByteValueHighMulShiftRight
    {I : ExecutionEnv}
    (hcanon : (bytesStoreSetMappedByteValueWord I).toNat < EVM.twoPow 8) :
    UInt256.shiftRight
      (UInt256.mul (bytesStoreSetMappedByteValueWord I)
        (UInt256.shiftLeft ⟨1⟩ ⟨248⟩)) ⟨248⟩ =
      bytesStoreSetMappedByteValueWord I := by
  rw [bytesStoreShiftRight248_eq_div_scale]
  apply u256_inj
  rw [udiv_toNat, u256_mul_toNat, bytesStoreShiftLeftOne248_toNat]
  have hv : (bytesStoreSetMappedByteValueWord I).toNat < 256 := by
    simpa [EVM.twoPow] using hcanon
  have hlt : (bytesStoreSetMappedByteValueWord I).toNat * 2 ^ 248 < UInt256.size := by
    rw [show UInt256.size = 2 ^ 256 from rfl]
    calc (bytesStoreSetMappedByteValueWord I).toNat * 2 ^ 248 < 256 * 2 ^ 248 :=
        Nat.mul_lt_mul_of_pos_right hv (by positivity)
      _ = 2 ^ 256 := by
        rw [show (256 : Nat) = 2 ^ 8 by norm_num, ← Nat.pow_add]
        norm_num
  rw [Nat.mod_eq_of_lt hlt]
  rw [Nat.mul_comm]
  rw [Nat.mul_div_right _ (by positivity : 0 < 2 ^ 248)]

theorem bytesStoreSetMappedByteLongScale_toNat {I : ExecutionEnv} :
    (bytesStoreSetMappedByteLongScale I).toNat =
      2 ^ ((31 - (bytesStoreSetMappedByteLongWordIndex I).toNat) * 8) := by
  simpa [bytesStoreSetMappedByteLongScale, bytesStoreSetChunkByteLongScale,
    bytesStoreSetMappedByteLongWordIndex, bytesStoreSetChunkByteLongWordIndex,
    bytesStoreSetMappedByteIndexWord, bytesStoreSetChunkByteIndexWord] using
    bytesStoreSetChunkByteLongScale_toNat (I := I)

theorem bytesStoreSetMappedByteLongMaskWord_toNat {I : ExecutionEnv} :
    (UInt256.mul ⟨255⟩ (bytesStoreSetMappedByteLongScale I)).toNat =
      255 * 2 ^ ((31 - (bytesStoreSetMappedByteLongWordIndex I).toNat) * 8) := by
  simpa [bytesStoreSetMappedByteLongScale, bytesStoreSetChunkByteLongScale,
    bytesStoreSetMappedByteLongWordIndex, bytesStoreSetChunkByteLongWordIndex,
    bytesStoreSetMappedByteIndexWord, bytesStoreSetChunkByteIndexWord] using
    bytesStoreSetChunkByteLongMaskWord_toNat (I := I)

theorem bytesStoreSetMappedByteLongClearMask_toNat {I : ExecutionEnv} :
    (UInt256.lnot (UInt256.mul ⟨255⟩ (bytesStoreSetMappedByteLongScale I))).toNat =
      (2 : Nat) ^ 256 - 1 -
        255 * 2 ^ ((31 - (bytesStoreSetMappedByteLongWordIndex I).toNat) * 8) := by
  simpa [bytesStoreSetMappedByteLongScale, bytesStoreSetChunkByteLongScale,
    bytesStoreSetMappedByteLongWordIndex, bytesStoreSetChunkByteLongWordIndex,
    bytesStoreSetMappedByteIndexWord, bytesStoreSetChunkByteIndexWord] using
    bytesStoreSetChunkByteLongClearMask_toNat (I := I)

theorem bytesStoreSetMappedByteShortScale_toNat {I : ExecutionEnv} {len : UInt256}
    (hshort : len.toNat < 32)
    (hbound : (bytesStoreSetMappedByteIndexWord I).toNat < len.toNat) :
    (bytesStoreSetMappedByteShortScale I).toNat =
      2 ^ ((31 - (bytesStoreSetMappedByteIndexWord I).toNat) * 8) := by
  simpa [bytesStoreSetMappedByteShortScale, bytesStoreSetChunkByteShortScale,
    bytesStoreSetMappedByteIndexWord, bytesStoreSetChunkByteIndexWord] using
    bytesStoreSetChunkByteShortScale_toNat (I := I) (len := len) hshort hbound

theorem bytesStoreSetMappedByteShortMaskWord_toNat {I : ExecutionEnv} {len : UInt256}
    (hshort : len.toNat < 32)
    (hbound : (bytesStoreSetMappedByteIndexWord I).toNat < len.toNat) :
    (UInt256.mul ⟨255⟩ (bytesStoreSetMappedByteShortScale I)).toNat =
      255 * 2 ^ ((31 - (bytesStoreSetMappedByteIndexWord I).toNat) * 8) := by
  simpa [bytesStoreSetMappedByteShortScale, bytesStoreSetChunkByteShortScale,
    bytesStoreSetMappedByteIndexWord, bytesStoreSetChunkByteIndexWord] using
    bytesStoreSetChunkByteShortMaskWord_toNat (I := I) (len := len) hshort hbound

theorem bytesStoreSetMappedByteShortClearMask_toNat {I : ExecutionEnv} {len : UInt256}
    (hshort : len.toNat < 32)
    (hbound : (bytesStoreSetMappedByteIndexWord I).toNat < len.toNat) :
    (UInt256.lnot (UInt256.mul ⟨255⟩ (bytesStoreSetMappedByteShortScale I))).toNat =
      2 ^ 256 - 1 -
        255 * 2 ^ ((31 - (bytesStoreSetMappedByteIndexWord I).toNat) * 8) := by
  simpa [bytesStoreSetMappedByteShortScale, bytesStoreSetChunkByteShortScale,
    bytesStoreSetMappedByteIndexWord, bytesStoreSetChunkByteIndexWord] using
    bytesStoreSetChunkByteShortClearMask_toNat (I := I) (len := len) hshort hbound

theorem bytesStoreSetMappedByteShortStoredWord_byteAt
    {σ : AccountMap} {I : ExecutionEnv} {len : UInt256}
    (hcanon : (bytesStoreSetMappedByteValueWord I).toNat < EVM.twoPow 8)
    (hshort : len.toNat < 32)
    (hbound : (bytesStoreSetMappedByteIndexWord I).toNat < len.toNat) :
    UInt256.byteAt (bytesStoreSetMappedByteIndexWord I)
      (bytesStoreSetMappedByteShortStoredWord σ I) =
        bytesStoreSetMappedByteValueWord I := by
  apply u256_inj
  have hi31 : (bytesStoreSetMappedByteIndexWord I).toNat ≤ 31 := by
    have hlt := bytesStoreSetMappedByteIndex_lt31_of_short_bound (I := I) (len := len)
      hshort hbound
    omega
  rw [byteAt_toNat_of_le31 hi31]
  rw [bytesStoreSetMappedByteShortStoredWord,
    bytesStoreSetMappedByteValueHighShiftDiv hcanon]
  rw [u256_lor_toNat, u256_mul_toNat, u256_land_toNat]
  rw [bytesStoreSetMappedByteShortScale_toNat (I := I) (len := len) hshort hbound]
  rw [bytesStoreSetMappedByteShortClearMask_toNat (I := I) (len := len) hshort hbound]
  have hv : (bytesStoreSetMappedByteValueWord I).toNat < 256 := by
    simpa [EVM.twoPow] using hcanon
  have hk : ((31 - (bytesStoreSetMappedByteIndexWord I).toNat) * 8) + 8 ≤ 256 := by
    have hidx : (bytesStoreSetMappedByteIndexWord I).toNat < 31 :=
      bytesStoreSetMappedByteIndex_lt31_of_short_bound (I := I) (len := len) hshort hbound
    omega
  have hleftLt : (bytesStoreSetMappedByteValueWord I).toNat *
      2 ^ ((31 - (bytesStoreSetMappedByteIndexWord I).toNat) * 8) < UInt256.size := by
    rw [show UInt256.size = 2 ^ 256 from rfl]
    calc (bytesStoreSetMappedByteValueWord I).toNat *
            2 ^ ((31 - (bytesStoreSetMappedByteIndexWord I).toNat) * 8) <
          256 * 2 ^ ((31 - (bytesStoreSetMappedByteIndexWord I).toNat) * 8) :=
            Nat.mul_lt_mul_of_pos_right hv (by positivity)
        _ ≤ 2 ^ 256 := by
          rw [show 256 = 2 ^ 8 by norm_num, ← Nat.pow_add]
          exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hrightLt : (((2 : Nat) ^ 256 - 1 -
        255 * 2 ^ ((31 - (bytesStoreSetMappedByteIndexWord I).toNat) * 8)) &&&
        (bytesStoreSetMappedByteHeaderWord σ I).toNat) < UInt256.size := by
    exact lt_of_le_of_lt Nat.and_le_right (bytesStoreSetMappedByteHeaderWord σ I).val.isLt
  rw [Nat.mod_eq_of_lt hleftLt]
  change ((bytesStoreSetMappedByteValueWord I).toNat *
          2 ^ ((31 - (bytesStoreSetMappedByteIndexWord I).toNat) * 8)).lor
        ((((2 : Nat) ^ 256 - 1 -
          255 * 2 ^ ((31 - (bytesStoreSetMappedByteIndexWord I).toNat) * 8)) &&&
          (bytesStoreSetMappedByteHeaderWord σ I).toNat) % UInt256.size) %
        UInt256.size /
      2 ^ ((31 - (bytesStoreSetMappedByteIndexWord I).toNat) * 8) % 256 =
    (bytesStoreSetMappedByteValueWord I).toNat
  rw [Nat.mod_eq_of_lt hrightLt]
  have hlorLt :
      ((bytesStoreSetMappedByteValueWord I).toNat *
            2 ^ ((31 - (bytesStoreSetMappedByteIndexWord I).toNat) * 8)).lor
          (((2 : Nat) ^ 256 - 1 -
              255 * 2 ^ ((31 - (bytesStoreSetMappedByteIndexWord I).toNat) * 8)) &&&
            (bytesStoreSetMappedByteHeaderWord σ I).toNat) < UInt256.size := by
    change ((bytesStoreSetMappedByteValueWord I).toNat *
          2 ^ ((31 - (bytesStoreSetMappedByteIndexWord I).toNat) * 8)) |||
        (((2 : Nat) ^ 256 - 1 -
            255 * 2 ^ ((31 - (bytesStoreSetMappedByteIndexWord I).toNat) * 8)) &&&
          (bytesStoreSetMappedByteHeaderWord σ I).toNat) < 2 ^ 256
    apply Nat.or_lt_two_pow
    · simpa [UInt256.size] using hleftLt
    · simpa [UInt256.size] using hrightLt
  rw [Nat.mod_eq_of_lt hlorLt]
  exact nat_byte_lane_lor_clear_eq
    (old := (bytesStoreSetMappedByteHeaderWord σ I).toNat)
    (v := (bytesStoreSetMappedByteValueWord I).toNat)
    (k := (31 - (bytesStoreSetMappedByteIndexWord I).toNat) * 8) hv hk

theorem bytesStoreSetMappedByteLongStoredWord_byteAt
    {σ : AccountMap} {I : ExecutionEnv}
    (hcanon : (bytesStoreSetMappedByteValueWord I).toNat < EVM.twoPow 8) :
    UInt256.byteAt (bytesStoreSetMappedByteLongWordIndex I)
      (bytesStoreSetMappedByteLongStoredWord σ I) =
        bytesStoreSetMappedByteValueWord I := by
  apply u256_inj
  have hv : (bytesStoreSetMappedByteValueWord I).toNat < 256 := by
    simpa [EVM.twoPow] using hcanon
  have hidxLt : (bytesStoreSetMappedByteLongWordIndex I).toNat < 32 :=
    bytesStoreSetMappedByteLongWordIndex_lt32 I
  have hidxLe : (bytesStoreSetMappedByteLongWordIndex I).toNat ≤ 31 := by omega
  rw [byteAt_toNat_of_le31 hidxLe]
  rw [bytesStoreSetMappedByteLongStoredWord,
    bytesStoreSetMappedByteValueHighShiftDiv hcanon]
  rw [u256_lor_toNat, u256_mul_toNat, u256_land_toNat]
  rw [bytesStoreSetMappedByteLongScale_toNat (I := I)]
  rw [bytesStoreSetMappedByteLongClearMask_toNat (I := I)]
  have hk : ((31 - (bytesStoreSetMappedByteLongWordIndex I).toNat) * 8) + 8 ≤ 256 := by
    omega
  have hleftLt : (bytesStoreSetMappedByteValueWord I).toNat *
      2 ^ ((31 - (bytesStoreSetMappedByteLongWordIndex I).toNat) * 8) < UInt256.size := by
    rw [show UInt256.size = 2 ^ 256 from rfl]
    calc (bytesStoreSetMappedByteValueWord I).toNat *
            2 ^ ((31 - (bytesStoreSetMappedByteLongWordIndex I).toNat) * 8) <
          256 * 2 ^ ((31 - (bytesStoreSetMappedByteLongWordIndex I).toNat) * 8) :=
            Nat.mul_lt_mul_of_pos_right hv (by positivity)
        _ = 2 ^ (8 + (31 - (bytesStoreSetMappedByteLongWordIndex I).toNat) * 8) := by
          rw [show 256 = 2 ^ 8 by norm_num, Nat.pow_add]
        _ ≤ 2 ^ 256 := by
          exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hrightLt : (((2 : Nat) ^ 256 - 1 -
        255 * 2 ^ ((31 - (bytesStoreSetMappedByteLongWordIndex I).toNat) * 8)) &&&
        (bytesStoreSetMappedByteLongOldWord σ I).toNat) < UInt256.size := by
    exact lt_of_le_of_lt Nat.and_le_right (bytesStoreSetMappedByteLongOldWord σ I).val.isLt
  rw [Nat.mod_eq_of_lt hleftLt]
  change (((bytesStoreSetMappedByteValueWord I).toNat *
          2 ^ ((31 - (bytesStoreSetMappedByteLongWordIndex I).toNat) * 8)).lor
        ((((2 : Nat) ^ 256 - 1 -
          255 * 2 ^ ((31 - (bytesStoreSetMappedByteLongWordIndex I).toNat) * 8)) &&&
          (bytesStoreSetMappedByteLongOldWord σ I).toNat) % UInt256.size) %
        UInt256.size) /
      2 ^ ((31 - (bytesStoreSetMappedByteLongWordIndex I).toNat) * 8) % 256 =
    (bytesStoreSetMappedByteValueWord I).toNat
  rw [Nat.mod_eq_of_lt hrightLt]
  have hlorLt :
      ((bytesStoreSetMappedByteValueWord I).toNat *
            2 ^ ((31 - (bytesStoreSetMappedByteLongWordIndex I).toNat) * 8)).lor
          (((2 : Nat) ^ 256 - 1 -
              255 * 2 ^ ((31 - (bytesStoreSetMappedByteLongWordIndex I).toNat) * 8)) &&&
            (bytesStoreSetMappedByteLongOldWord σ I).toNat) < UInt256.size := by
    change ((bytesStoreSetMappedByteValueWord I).toNat *
          2 ^ ((31 - (bytesStoreSetMappedByteLongWordIndex I).toNat) * 8)) |||
        (((2 : Nat) ^ 256 - 1 -
            255 * 2 ^ ((31 - (bytesStoreSetMappedByteLongWordIndex I).toNat) * 8)) &&&
          (bytesStoreSetMappedByteLongOldWord σ I).toNat) < 2 ^ 256
    apply Nat.or_lt_two_pow
    · simpa [UInt256.size] using hleftLt
    · simpa [UInt256.size] using hrightLt
  rw [Nat.mod_eq_of_lt hlorLt]
  exact nat_byte_lane_lor_clear_eq
    (old := (bytesStoreSetMappedByteLongOldWord σ I).toNat)
    (v := (bytesStoreSetMappedByteValueWord I).toNat)
    (k := (31 - (bytesStoreSetMappedByteLongWordIndex I).toNat) * 8) hv hk

theorem bytesStoreSetMappedByteLongStoredWord_byteAt_index_of_lt32
    {σ : AccountMap} {I : ExecutionEnv}
    (hcanon : (bytesStoreSetMappedByteValueWord I).toNat < EVM.twoPow 8)
    (hidx : (bytesStoreSetMappedByteIndexWord I).toNat < 32) :
    UInt256.byteAt (bytesStoreSetMappedByteIndexWord I)
      (bytesStoreSetMappedByteLongStoredWord σ I) =
        bytesStoreSetMappedByteValueWord I := by
  have heq := bytesStoreSetMappedByteLongWordIndex_eq_index_of_lt32
    (I := I) hidx
  rw [← heq]
  exact bytesStoreSetMappedByteLongStoredWord_byteAt (σ := σ) (I := I) hcanon

theorem bytesStoreSetMappedByteShortStoredWord_toNat_update
    {σ : AccountMap} {I : ExecutionEnv} {len : UInt256}
    (hcanon : (bytesStoreSetMappedByteValueWord I).toNat < EVM.twoPow 8)
    (hshort : len.toNat < 32)
    (hbound : (bytesStoreSetMappedByteIndexWord I).toNat < len.toNat) :
    (bytesStoreSetMappedByteHeaderWord σ I).toNat %
          2 ^ ((31 - (bytesStoreSetMappedByteIndexWord I).toNat) * 8) +
        2 ^ ((31 - (bytesStoreSetMappedByteIndexWord I).toNat) * 8) *
          (bytesStoreSetMappedByteValueWord I).toNat +
      2 ^ ((31 - (bytesStoreSetMappedByteIndexWord I).toNat) * 8 + 8) *
        ((bytesStoreSetMappedByteHeaderWord σ I).toNat /
          2 ^ ((31 - (bytesStoreSetMappedByteIndexWord I).toNat) * 8 + 8)) =
    (bytesStoreSetMappedByteShortStoredWord σ I).toNat := by
  have hv : (bytesStoreSetMappedByteValueWord I).toNat < 256 := by
    simpa [EVM.twoPow] using hcanon
  rw [bytesStoreSetMappedByteShortStoredWord,
    bytesStoreSetMappedByteValueHighShiftDiv hcanon]
  rw [u256_lor_toNat, u256_mul_toNat, u256_land_toNat]
  rw [bytesStoreSetMappedByteShortScale_toNat (I := I) (len := len) hshort hbound]
  rw [bytesStoreSetMappedByteShortClearMask_toNat (I := I) (len := len) hshort hbound]
  have hk : ((31 - (bytesStoreSetMappedByteIndexWord I).toNat) * 8) + 8 ≤ 256 := by
    have hidx := bytesStoreSetMappedByteIndex_lt31_of_short_bound
      (I := I) (len := len) hshort hbound
    omega
  have hleftLt : (bytesStoreSetMappedByteValueWord I).toNat *
      2 ^ ((31 - (bytesStoreSetMappedByteIndexWord I).toNat) * 8) < UInt256.size := by
    rw [show UInt256.size = 2 ^ 256 from rfl]
    calc (bytesStoreSetMappedByteValueWord I).toNat *
            2 ^ ((31 - (bytesStoreSetMappedByteIndexWord I).toNat) * 8) <
          256 * 2 ^ ((31 - (bytesStoreSetMappedByteIndexWord I).toNat) * 8) :=
            Nat.mul_lt_mul_of_pos_right hv (by positivity)
        _ ≤ 2 ^ 256 := by
          rw [show 256 = 2 ^ 8 by norm_num, ← Nat.pow_add]
          exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hrightLt : (((2 : Nat) ^ 256 - 1 -
        255 * 2 ^ ((31 - (bytesStoreSetMappedByteIndexWord I).toNat) * 8)) &&&
        (bytesStoreSetMappedByteHeaderWord σ I).toNat) < UInt256.size := by
    exact lt_of_le_of_lt Nat.and_le_right (bytesStoreSetMappedByteHeaderWord σ I).val.isLt
  rw [Nat.mod_eq_of_lt hleftLt]
  change (bytesStoreSetMappedByteHeaderWord σ I).toNat %
        2 ^ ((31 - (bytesStoreSetMappedByteIndexWord I).toNat) * 8) +
      2 ^ ((31 - (bytesStoreSetMappedByteIndexWord I).toNat) * 8) *
        (bytesStoreSetMappedByteValueWord I).toNat +
      2 ^ (((31 - (bytesStoreSetMappedByteIndexWord I).toNat) * 8) + 8) *
        ((bytesStoreSetMappedByteHeaderWord σ I).toNat /
          2 ^ (((31 - (bytesStoreSetMappedByteIndexWord I).toNat) * 8) + 8)) =
      ((bytesStoreSetMappedByteValueWord I).toNat *
          2 ^ ((31 - (bytesStoreSetMappedByteIndexWord I).toNat) * 8)).lor
        ((((2 : Nat) ^ 256 - 1 -
          255 * 2 ^ ((31 - (bytesStoreSetMappedByteIndexWord I).toNat) * 8)) &&&
          (bytesStoreSetMappedByteHeaderWord σ I).toNat) % UInt256.size) %
        UInt256.size
  rw [Nat.mod_eq_of_lt hrightLt]
  have hlorLt :
      ((bytesStoreSetMappedByteValueWord I).toNat *
            2 ^ ((31 - (bytesStoreSetMappedByteIndexWord I).toNat) * 8)).lor
          (((2 : Nat) ^ 256 - 1 -
              255 * 2 ^ ((31 - (bytesStoreSetMappedByteIndexWord I).toNat) * 8)) &&&
            (bytesStoreSetMappedByteHeaderWord σ I).toNat) < UInt256.size := by
    change ((bytesStoreSetMappedByteValueWord I).toNat *
          2 ^ ((31 - (bytesStoreSetMappedByteIndexWord I).toNat) * 8)) |||
        (((2 : Nat) ^ 256 - 1 -
            255 * 2 ^ ((31 - (bytesStoreSetMappedByteIndexWord I).toNat) * 8)) &&&
          (bytesStoreSetMappedByteHeaderWord σ I).toNat) < 2 ^ 256
    apply Nat.or_lt_two_pow
    · simpa [UInt256.size] using hleftLt
    · simpa [UInt256.size] using hrightLt
  rw [Nat.mod_eq_of_lt hlorLt]
  rw [show 2 ^ ((31 - (bytesStoreSetMappedByteIndexWord I).toNat) * 8) *
        (bytesStoreSetMappedByteValueWord I).toNat =
        (bytesStoreSetMappedByteValueWord I).toNat *
          2 ^ ((31 - (bytesStoreSetMappedByteIndexWord I).toNat) * 8) by ring]
  rw [show 2 ^ (((31 - (bytesStoreSetMappedByteIndexWord I).toNat) * 8) + 8) *
        ((bytesStoreSetMappedByteHeaderWord σ I).toNat /
          2 ^ (((31 - (bytesStoreSetMappedByteIndexWord I).toNat) * 8) + 8)) =
      (bytesStoreSetMappedByteHeaderWord σ I).toNat /
          2 ^ (((31 - (bytesStoreSetMappedByteIndexWord I).toNat) * 8) + 8) *
        2 ^ (((31 - (bytesStoreSetMappedByteIndexWord I).toNat) * 8) + 8) by ring]
  exact nat_byte_update_eq
    (old := (bytesStoreSetMappedByteHeaderWord σ I).toNat)
    (v := (bytesStoreSetMappedByteValueWord I).toNat)
    (k := (31 - (bytesStoreSetMappedByteIndexWord I).toNat) * 8)
    hv hk (by exact (bytesStoreSetMappedByteHeaderWord σ I).val.isLt)

theorem bytesStoreSetMappedByteLongStoredWord_toNat_update
    {σ : AccountMap} {I : ExecutionEnv}
    (hcanon : (bytesStoreSetMappedByteValueWord I).toNat < EVM.twoPow 8) :
    (bytesStoreSetMappedByteLongOldWord σ I).toNat %
          2 ^ ((31 - (bytesStoreSetMappedByteLongWordIndex I).toNat) * 8) +
        2 ^ ((31 - (bytesStoreSetMappedByteLongWordIndex I).toNat) * 8) *
          (bytesStoreSetMappedByteValueWord I).toNat +
      2 ^ ((31 - (bytesStoreSetMappedByteLongWordIndex I).toNat) * 8 + 8) *
        ((bytesStoreSetMappedByteLongOldWord σ I).toNat /
          2 ^ ((31 - (bytesStoreSetMappedByteLongWordIndex I).toNat) * 8 + 8)) =
    (bytesStoreSetMappedByteLongStoredWord σ I).toNat := by
  have hv : (bytesStoreSetMappedByteValueWord I).toNat < 256 := by
    simpa [EVM.twoPow] using hcanon
  rw [bytesStoreSetMappedByteLongStoredWord,
    bytesStoreSetMappedByteValueHighShiftDiv hcanon]
  rw [u256_lor_toNat, u256_mul_toNat, u256_land_toNat]
  rw [bytesStoreSetMappedByteLongScale_toNat (I := I)]
  rw [bytesStoreSetMappedByteLongClearMask_toNat (I := I)]
  have hidxLt : (bytesStoreSetMappedByteLongWordIndex I).toNat < 32 :=
    bytesStoreSetMappedByteLongWordIndex_lt32 I
  have hk : ((31 - (bytesStoreSetMappedByteLongWordIndex I).toNat) * 8) + 8 ≤ 256 := by
    omega
  have hleftLt : (bytesStoreSetMappedByteValueWord I).toNat *
      2 ^ ((31 - (bytesStoreSetMappedByteLongWordIndex I).toNat) * 8) < UInt256.size := by
    rw [show UInt256.size = 2 ^ 256 from rfl]
    calc (bytesStoreSetMappedByteValueWord I).toNat *
            2 ^ ((31 - (bytesStoreSetMappedByteLongWordIndex I).toNat) * 8) <
          256 * 2 ^ ((31 - (bytesStoreSetMappedByteLongWordIndex I).toNat) * 8) :=
            Nat.mul_lt_mul_of_pos_right hv (by positivity)
        _ = 2 ^ (8 + (31 - (bytesStoreSetMappedByteLongWordIndex I).toNat) * 8) := by
          rw [show 256 = 2 ^ 8 by norm_num, Nat.pow_add]
        _ ≤ 2 ^ 256 := by
          exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hrightLt : (((2 : Nat) ^ 256 - 1 -
        255 * 2 ^ ((31 - (bytesStoreSetMappedByteLongWordIndex I).toNat) * 8)) &&&
        (bytesStoreSetMappedByteLongOldWord σ I).toNat) < UInt256.size := by
    exact lt_of_le_of_lt Nat.and_le_right (bytesStoreSetMappedByteLongOldWord σ I).val.isLt
  rw [Nat.mod_eq_of_lt hleftLt]
  change (bytesStoreSetMappedByteLongOldWord σ I).toNat %
        2 ^ ((31 - (bytesStoreSetMappedByteLongWordIndex I).toNat) * 8) +
      2 ^ ((31 - (bytesStoreSetMappedByteLongWordIndex I).toNat) * 8) *
        (bytesStoreSetMappedByteValueWord I).toNat +
      2 ^ (((31 - (bytesStoreSetMappedByteLongWordIndex I).toNat) * 8) + 8) *
        ((bytesStoreSetMappedByteLongOldWord σ I).toNat /
          2 ^ (((31 - (bytesStoreSetMappedByteLongWordIndex I).toNat) * 8) + 8)) =
      ((bytesStoreSetMappedByteValueWord I).toNat *
          2 ^ ((31 - (bytesStoreSetMappedByteLongWordIndex I).toNat) * 8)).lor
        ((((2 : Nat) ^ 256 - 1 -
          255 * 2 ^ ((31 - (bytesStoreSetMappedByteLongWordIndex I).toNat) * 8)) &&&
          (bytesStoreSetMappedByteLongOldWord σ I).toNat) % UInt256.size) %
        UInt256.size
  rw [Nat.mod_eq_of_lt hrightLt]
  have hlorLt :
      ((bytesStoreSetMappedByteValueWord I).toNat *
            2 ^ ((31 - (bytesStoreSetMappedByteLongWordIndex I).toNat) * 8)).lor
          (((2 : Nat) ^ 256 - 1 -
              255 * 2 ^ ((31 - (bytesStoreSetMappedByteLongWordIndex I).toNat) * 8)) &&&
            (bytesStoreSetMappedByteLongOldWord σ I).toNat) < UInt256.size := by
    change ((bytesStoreSetMappedByteValueWord I).toNat *
          2 ^ ((31 - (bytesStoreSetMappedByteLongWordIndex I).toNat) * 8)) |||
        (((2 : Nat) ^ 256 - 1 -
            255 * 2 ^ ((31 - (bytesStoreSetMappedByteLongWordIndex I).toNat) * 8)) &&&
          (bytesStoreSetMappedByteLongOldWord σ I).toNat) < 2 ^ 256
    apply Nat.or_lt_two_pow
    · simpa [UInt256.size] using hleftLt
    · simpa [UInt256.size] using hrightLt
  rw [Nat.mod_eq_of_lt hlorLt]
  rw [show 2 ^ ((31 - (bytesStoreSetMappedByteLongWordIndex I).toNat) * 8) *
        (bytesStoreSetMappedByteValueWord I).toNat =
        (bytesStoreSetMappedByteValueWord I).toNat *
          2 ^ ((31 - (bytesStoreSetMappedByteLongWordIndex I).toNat) * 8) by ring]
  rw [show 2 ^ (((31 - (bytesStoreSetMappedByteLongWordIndex I).toNat) * 8) + 8) *
        ((bytesStoreSetMappedByteLongOldWord σ I).toNat /
          2 ^ (((31 - (bytesStoreSetMappedByteLongWordIndex I).toNat) * 8) + 8)) =
      (bytesStoreSetMappedByteLongOldWord σ I).toNat /
          2 ^ (((31 - (bytesStoreSetMappedByteLongWordIndex I).toNat) * 8) + 8) *
        2 ^ (((31 - (bytesStoreSetMappedByteLongWordIndex I).toNat) * 8) + 8) by ring]
  exact nat_byte_update_eq
    (old := (bytesStoreSetMappedByteLongOldWord σ I).toNat)
    (v := (bytesStoreSetMappedByteValueWord I).toNat)
    (k := (31 - (bytesStoreSetMappedByteLongWordIndex I).toNat) * 8)
    hv hk (by exact (bytesStoreSetMappedByteLongOldWord σ I).val.isLt)

theorem bytesStoreSetMappedByteShortScale_mod256_zero {I : ExecutionEnv} {len : UInt256}
    (hshort : len.toNat < 32)
    (hbound : (bytesStoreSetMappedByteIndexWord I).toNat < len.toNat) :
    (bytesStoreSetMappedByteShortScale I).toNat % 256 = 0 := by
  have hidx : (bytesStoreSetMappedByteIndexWord I).toNat < 31 :=
    bytesStoreSetMappedByteIndex_lt31_of_short_bound hshort hbound
  interval_cases hnat : (bytesStoreSetMappedByteIndexWord I).toNat
  all_goals
    have hword : bytesStoreSetMappedByteIndexWord I =
        UInt256.ofNat (bytesStoreSetMappedByteIndexWord I).toNat := by
      exact (u256_ofNat_toNat (bytesStoreSetMappedByteIndexWord I)).symm
    rw [bytesStoreSetMappedByteShortScale, hword, hnat]
    native_decide

theorem bytesStoreSetMappedByteShortClearMask_mod256_255 {I : ExecutionEnv}
    {len : UInt256}
    (hshort : len.toNat < 32)
    (hbound : (bytesStoreSetMappedByteIndexWord I).toNat < len.toNat) :
    (UInt256.lnot (UInt256.mul ⟨255⟩ (bytesStoreSetMappedByteShortScale I))).toNat %
        256 = 255 := by
  have hidx : (bytesStoreSetMappedByteIndexWord I).toNat < 31 :=
    bytesStoreSetMappedByteIndex_lt31_of_short_bound hshort hbound
  interval_cases hnat : (bytesStoreSetMappedByteIndexWord I).toNat
  all_goals
    have hword : bytesStoreSetMappedByteIndexWord I =
        UInt256.ofNat (bytesStoreSetMappedByteIndexWord I).toNat := by
      exact (u256_ofNat_toNat (bytesStoreSetMappedByteIndexWord I)).symm
    rw [bytesStoreSetMappedByteShortScale, hword, hnat]
    native_decide

theorem bytesStoreSetMappedByteShortStoredWord_mod256
    {σ : AccountMap} {I : ExecutionEnv} {len : UInt256}
    (hshort : len.toNat < 32)
    (hbound : (bytesStoreSetMappedByteIndexWord I).toNat < len.toNat) :
    (bytesStoreSetMappedByteShortStoredWord σ I).toNat % 256 =
      (bytesStoreSetMappedByteHeaderWord σ I).toNat % 256 := by
  have hscale := bytesStoreSetMappedByteShortScale_mod256_zero
    (I := I) (len := len) hshort hbound
  have hmask := bytesStoreSetMappedByteShortClearMask_mod256_255
    (I := I) (len := len) hshort hbound
  have hleft :
      (UInt256.mul
        (UInt256.div (UInt256.shiftLeft (bytesStoreSetMappedByteValueWord I) ⟨248⟩)
          (UInt256.shiftLeft ⟨1⟩ ⟨248⟩))
        (bytesStoreSetMappedByteShortScale I)).toNat % 256 = 0 := by
    rw [u256_mul_toNat, nat_mod_u256_mod_256, Nat.mul_mod, hscale]
    simp
  have hright :
      (UInt256.land
        (UInt256.lnot (UInt256.mul ⟨255⟩ (bytesStoreSetMappedByteShortScale I)))
        (bytesStoreSetMappedByteHeaderWord σ I)).toNat % 256 =
        (bytesStoreSetMappedByteHeaderWord σ I).toNat % 256 := by
    rw [u256_land_toNat, nat_mod_u256_mod_256]
    exact nat_land_mod_256_of_left_255 hmask
  rw [bytesStoreSetMappedByteShortStoredWord, u256_lor_toNat, nat_mod_u256_mod_256]
  rw [nat_lor_mod_256_of_left_zero hleft, hright]

theorem bytesStoreSetMappedByteShortStoredWord_flag_eq
    {σ : AccountMap} {I : ExecutionEnv} {len : UInt256}
    (hshort : len.toNat < 32)
    (hbound : (bytesStoreSetMappedByteIndexWord I).toNat < len.toNat) :
    UInt256.land (bytesStoreSetMappedByteShortStoredWord σ I) ⟨1⟩ =
      UInt256.land (bytesStoreSetMappedByteHeaderWord σ I) ⟨1⟩ := by
  apply u256_inj
  rw [uInt256_land_one_toNat, uInt256_land_one_toNat]
  have hmod := bytesStoreSetMappedByteShortStoredWord_mod256
    (σ := σ) (I := I) (len := len) hshort hbound
  have hleft :
      (bytesStoreSetMappedByteShortStoredWord σ I).toNat % 2 =
        ((bytesStoreSetMappedByteShortStoredWord σ I).toNat % 256) % 2 := by
    rw [Nat.mod_mod_of_dvd]
    norm_num
  have hright :
      (bytesStoreSetMappedByteHeaderWord σ I).toNat % 2 =
        ((bytesStoreSetMappedByteHeaderWord σ I).toNat % 256) % 2 := by
    rw [Nat.mod_mod_of_dvd]
    norm_num
  rw [hleft, hright, hmod]

theorem bytesStoreSetMappedByteShortStoredWord_shortLen_eq
    {σ : AccountMap} {I : ExecutionEnv} {len : UInt256}
    (hshort : len.toNat < 32)
    (hbound : (bytesStoreSetMappedByteIndexWord I).toNat < len.toNat) :
    UInt256.land (UInt256.div (bytesStoreSetMappedByteShortStoredWord σ I) ⟨2⟩) ⟨127⟩ =
      UInt256.land (UInt256.div (bytesStoreSetMappedByteHeaderWord σ I) ⟨2⟩) ⟨127⟩ := by
  apply u256_inj
  rw [bytesStoreShortLenBits_toNat, bytesStoreShortLenBits_toNat]
  rw [bytesStoreSetMappedByteShortStoredWord_mod256 (σ := σ) (I := I) (len := len)
    hshort hbound]

theorem bytesStoreSetMappedByteStorageLocStoreShort
    {evm : EVM.State} {σ : AccountMap} {I : ExecutionEnv} {len : UInt256}
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (bytesStoreSetMappedByteSlot I) = bytesStoreSetMappedByteHeaderWord σ I)
    (hcanon : (bytesStoreSetMappedByteValueWord I).toNat < EVM.twoPow 8)
    (hshort : len.toNat < 32)
    (hbound : (bytesStoreSetMappedByteIndexWord I).toNat < len.toNat) :
    storageLocStore evm
      (uint8Loc (bytesStoreSetMappedByteSlot I)
        ⟨31 - (bytesStoreSetMappedByteIndexWord I).toNat, by
          have hidx := bytesStoreSetMappedByteIndex_lt31_of_short_bound
            (I := I) (len := len) hshort hbound
          omega⟩)
      (bytesStoreSetMappedByteValue I) =
      some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner
        (bytesStoreSetMappedByteSlot I)
        (bytesStoreSetMappedByteShortStoredWord σ I)) := by
  let offFin : Fin 32 :=
    ⟨31 - (bytesStoreSetMappedByteIndexWord I).toNat, by
      have hidx := bytesStoreSetMappedByteIndex_lt31_of_short_bound
        (I := I) (len := len) hshort hbound
      omega⟩
  have hval : valueToWord (bytesStoreSetMappedByteValue I) =
      some (UInt256.ofNat (bytesStoreSetMappedByteValueWord I).toNat) := by
    simp [bytesStoreSetMappedByteValue, valueToWord]
    exact bytesStoreWordOfIntOfNatEq (bytesStoreSetMappedByteValueWord I).toNat
  have hoffVal : offFin.val = 31 - (bytesStoreSetMappedByteIndexWord I).toNat := by
    rfl
  have hoffLe : offFin.val ≤ 32 := Nat.le_of_lt offFin.isLt
  have hv : (bytesStoreSetMappedByteValueWord I).toNat < 256 := by
    simpa [EVM.twoPow] using hcanon
  have hoffBound : offFin.val + (1 : Fin 33).val - 1 < 32 := by
    have hidx := bytesStoreSetMappedByteIndex_lt31_of_short_bound
      (I := I) (len := len) hshort hbound
    simp [offFin]
    omega
  have htarget :
      (bytesStoreSetMappedByteShortStoredWord σ I).toNat =
        fromBytes'
          ((EVM.Word.toBytesLEWithSizeProof
                (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
                  (bytesStoreSetMappedByteSlot I))).1.take offFin.val ++
           (EVM.Word.toBytesLEWithSizeProof
                (storageLocWriteWord
                  (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
                    (bytesStoreSetMappedByteSlot I))
                  offFin.val none
                  (UInt256.ofNat (bytesStoreSetMappedByteValueWord I).toNat))).1.take 1 ++
           (EVM.Word.toBytesLEWithSizeProof
                (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
                  (bytesStoreSetMappedByteSlot I))).1.drop
              (offFin.val + 1)) := by
    rw [hload]
    simp only [storageLocWriteWord]
    symm
    rw [fromBytes'_append, fromBytes'_append]
    rw [fromBytes'_take_wordLE, fromBytes'_take_wordLE, fromBytes'_drop_wordLE]
    have hslen := (EVM.Word.toBytesLEWithSizeProof
      (bytesStoreSetMappedByteHeaderWord σ I)).2
    have hvlen := (EVM.Word.toBytesLEWithSizeProof
      (UInt256.ofNat (bytesStoreSetMappedByteValueWord I).toNat)).2
    rw [List.length_take, hslen, Nat.min_eq_left hoffLe]
    rw [List.length_append, List.length_take, hslen, Nat.min_eq_left hoffLe,
      List.length_take, hvlen, Nat.min_eq_left (by norm_num : 1 ≤ 32)]
    rw [show 8 * (offFin.val + 1) = 8 * offFin.val + 8 by ring]
    rw [show 256 ^ offFin.val = 2 ^ (8 * offFin.val) by
      rw [show (256 : Nat) = 2 ^ 8 by norm_num, ← Nat.pow_mul]]
    rw [show 256 ^ 1 = 256 by norm_num]
    rw [show (UInt256.ofNat (bytesStoreSetMappedByteValueWord I).toNat).toNat % 256 =
        (bytesStoreSetMappedByteValueWord I).toNat by
      rw [ulit_toNat' _ (lt_of_lt_of_le hv (by norm_num [UInt256.size]))]
      exact Nat.mod_eq_of_lt hv]
    rw [hoffVal]
    rw [show 8 * (31 - (bytesStoreSetMappedByteIndexWord I).toNat) =
        (31 - (bytesStoreSetMappedByteIndexWord I).toNat) * 8 by ring]
    rw [show 256 ^ (31 - (bytesStoreSetMappedByteIndexWord I).toNat + 1) =
        2 ^ (((31 - (bytesStoreSetMappedByteIndexWord I).toNat) * 8) + 8) by
      rw [show 256 = 2 ^ 8 by norm_num, ← Nat.pow_mul]
      congr 1
      ring]
    change
      (bytesStoreSetMappedByteHeaderWord σ I).toNat %
            2 ^ ((31 - (bytesStoreSetMappedByteIndexWord I).toNat) * 8) +
          2 ^ ((31 - (bytesStoreSetMappedByteIndexWord I).toNat) * 8) *
            (bytesStoreSetMappedByteValueWord I).toNat +
        2 ^ ((31 - (bytesStoreSetMappedByteIndexWord I).toNat) * 8 + 8) *
          ((bytesStoreSetMappedByteHeaderWord σ I).toNat /
            2 ^ ((31 - (bytesStoreSetMappedByteIndexWord I).toNat) * 8 + 8)) =
      (bytesStoreSetMappedByteShortStoredWord σ I).toNat
    exact bytesStoreSetMappedByteShortStoredWord_toNat_update
      (σ := σ) (I := I) (len := len) hcanon hshort hbound
  change storageLocStore evm
      { slot := bytesStoreSetMappedByteSlot I, offset := offFin, size := 1,
        hbound := hoffBound, type := .int uint8Int }
      (bytesStoreSetMappedByteValue I) =
      some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner
        (bytesStoreSetMappedByteSlot I)
        (bytesStoreSetMappedByteShortStoredWord σ I))
  exact storageLocStore_oneByte_local evm (bytesStoreSetMappedByteSlot I)
    (UInt256.ofNat (bytesStoreSetMappedByteValueWord I).toNat)
    (bytesStoreSetMappedByteShortStoredWord σ I)
    offFin (.int uint8Int) hoffBound
    (bytesStoreSetMappedByteValue I) hval htarget

theorem bytesStoreSetMappedByteStorageLocStoreLong
    {evm : EVM.State} {σ : AccountMap} {I : ExecutionEnv}
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (bytesStoreSetMappedByteLongDataSlot I) =
      bytesStoreSetMappedByteLongOldWord σ I)
    (hcanon : (bytesStoreSetMappedByteValueWord I).toNat < EVM.twoPow 8) :
    storageLocStore evm
      (uint8Loc (bytesStoreSetMappedByteLongDataSlot I)
        ⟨31 - (bytesStoreSetMappedByteLongWordIndex I).toNat, by
          have hidx := bytesStoreSetMappedByteLongWordIndex_lt32 I
          omega⟩)
      (bytesStoreSetMappedByteValue I) =
      some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner
        (bytesStoreSetMappedByteLongDataSlot I)
        (bytesStoreSetMappedByteLongStoredWord σ I)) := by
  let offFin : Fin 32 :=
    ⟨31 - (bytesStoreSetMappedByteLongWordIndex I).toNat, by
      have hidx := bytesStoreSetMappedByteLongWordIndex_lt32 I
      omega⟩
  have hval : valueToWord (bytesStoreSetMappedByteValue I) =
      some (UInt256.ofNat (bytesStoreSetMappedByteValueWord I).toNat) := by
    simp [bytesStoreSetMappedByteValue, valueToWord]
    exact bytesStoreWordOfIntOfNatEq (bytesStoreSetMappedByteValueWord I).toNat
  have hoffVal : offFin.val = 31 - (bytesStoreSetMappedByteLongWordIndex I).toNat := by
    rfl
  have hoffLe : offFin.val ≤ 32 := Nat.le_of_lt offFin.isLt
  have hv : (bytesStoreSetMappedByteValueWord I).toNat < 256 := by
    simpa [EVM.twoPow] using hcanon
  have hoffBound : offFin.val + (1 : Fin 33).val - 1 < 32 := by
    simp [offFin]
    omega
  have htarget :
      (bytesStoreSetMappedByteLongStoredWord σ I).toNat =
        fromBytes'
          ((EVM.Word.toBytesLEWithSizeProof
                (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
                  (bytesStoreSetMappedByteLongDataSlot I))).1.take offFin.val ++
           (EVM.Word.toBytesLEWithSizeProof
                (storageLocWriteWord
                  (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
                    (bytesStoreSetMappedByteLongDataSlot I))
                  offFin.val none
                  (UInt256.ofNat (bytesStoreSetMappedByteValueWord I).toNat))).1.take 1 ++
           (EVM.Word.toBytesLEWithSizeProof
                (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
                  (bytesStoreSetMappedByteLongDataSlot I))).1.drop
              (offFin.val + 1)) := by
    rw [hload]
    simp only [storageLocWriteWord]
    symm
    rw [fromBytes'_append, fromBytes'_append]
    rw [fromBytes'_take_wordLE, fromBytes'_take_wordLE, fromBytes'_drop_wordLE]
    have hslen := (EVM.Word.toBytesLEWithSizeProof
      (bytesStoreSetMappedByteLongOldWord σ I)).2
    have hvlen := (EVM.Word.toBytesLEWithSizeProof
      (UInt256.ofNat (bytesStoreSetMappedByteValueWord I).toNat)).2
    rw [List.length_take, hslen, Nat.min_eq_left hoffLe]
    rw [List.length_append, List.length_take, hslen, Nat.min_eq_left hoffLe,
      List.length_take, hvlen, Nat.min_eq_left (by norm_num : 1 ≤ 32)]
    rw [show 8 * (offFin.val + 1) = 8 * offFin.val + 8 by ring]
    rw [show 256 ^ offFin.val = 2 ^ (8 * offFin.val) by
      rw [show (256 : Nat) = 2 ^ 8 by norm_num, ← Nat.pow_mul]]
    rw [show 256 ^ 1 = 256 by norm_num]
    rw [show (UInt256.ofNat (bytesStoreSetMappedByteValueWord I).toNat).toNat % 256 =
        (bytesStoreSetMappedByteValueWord I).toNat by
      rw [ulit_toNat' _ (lt_of_lt_of_le hv (by norm_num [UInt256.size]))]
      exact Nat.mod_eq_of_lt hv]
    rw [hoffVal]
    rw [show 8 * (31 - (bytesStoreSetMappedByteLongWordIndex I).toNat) =
        (31 - (bytesStoreSetMappedByteLongWordIndex I).toNat) * 8 by ring]
    rw [show 256 ^ (31 - (bytesStoreSetMappedByteLongWordIndex I).toNat + 1) =
        2 ^ (((31 - (bytesStoreSetMappedByteLongWordIndex I).toNat) * 8) + 8) by
      rw [show 256 = 2 ^ 8 by norm_num, ← Nat.pow_mul]
      congr 1
      ring]
    change
      (bytesStoreSetMappedByteLongOldWord σ I).toNat %
            2 ^ ((31 - (bytesStoreSetMappedByteLongWordIndex I).toNat) * 8) +
          2 ^ ((31 - (bytesStoreSetMappedByteLongWordIndex I).toNat) * 8) *
            (bytesStoreSetMappedByteValueWord I).toNat +
        2 ^ ((31 - (bytesStoreSetMappedByteLongWordIndex I).toNat) * 8 + 8) *
          ((bytesStoreSetMappedByteLongOldWord σ I).toNat /
            2 ^ ((31 - (bytesStoreSetMappedByteLongWordIndex I).toNat) * 8 + 8)) =
      (bytesStoreSetMappedByteLongStoredWord σ I).toNat
    exact bytesStoreSetMappedByteLongStoredWord_toNat_update
      (σ := σ) (I := I) hcanon
  change storageLocStore evm
      { slot := bytesStoreSetMappedByteLongDataSlot I, offset := offFin, size := 1,
        hbound := hoffBound, type := .int uint8Int }
      (bytesStoreSetMappedByteValue I) =
      some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner
        (bytesStoreSetMappedByteLongDataSlot I)
        (bytesStoreSetMappedByteLongStoredWord σ I))
  exact storageLocStore_oneByte_local evm (bytesStoreSetMappedByteLongDataSlot I)
    (UInt256.ofNat (bytesStoreSetMappedByteValueWord I).toNat)
    (bytesStoreSetMappedByteLongStoredWord σ I)
    offFin (.int uint8Int) hoffBound
    (bytesStoreSetMappedByteValue I) hval htarget

theorem bytesStoreSetMappedByteBodyReturns {evm evm' : EVM.State}
    {I : ExecutionEnv} {ret : Value}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hassign :
      assignStorageRef? bytesStoreConfig
        (bytesStoreSetMappedByteFrame I)
        evm .storage (mappedByteRef (.var "key") (.var "byteIndex"))
          (bytesStoreSetMappedByteValue I) =
          .ok (bytesStoreSetMappedByteFrame I, evm'))
    (hret :
      evalExpr? bytesStoreConfig
        (bytesStoreSetMappedByteFrame I)
        evm' (.storage (mappedByteRef (.var "key") (.var "byteIndex"))) = .ok ret) :
    ExecTransitionBody bytesStoreConfig bytesStoreContract evm
      (bytesStoreSetMappedByteLocals I) setMappedByteTransition.body
      (.returned
        (bytesStoreSetMappedByteFrame I)
        evm' (some ret)) := by
  let solm : Frame := bytesStoreSetMappedByteFrame I
  have hvalue :
      evalExpr? bytesStoreConfig solm evm (.var "value") =
        .ok (bytesStoreSetMappedByteValue I) := by
    exact evalExpr_var_of_get? (by
      simp [solm, bytesStoreSetMappedByteFrame, bytesStoreSetMappedByteValue,
        bytesStoreSetMappedByteLocals])
  have hassign :
      assignStorageRef? bytesStoreConfig solm evm .storage
        (mappedByteRef (.var "key") (.var "byteIndex"))
          (bytesStoreSetMappedByteValue I) =
          .ok (solm, evm') := by
    simpa [solm] using hassign
  have hret :
      evalExpr? bytesStoreConfig solm evm'
        (.storage (mappedByteRef (.var "key") (.var "byteIndex"))) = .ok ret := by
    simpa [solm] using hret
  exact ExecFuncBody.execBlockRet <|
    ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consNormal (ExecStmt.assign hvalue hassign) <|
        ExecBlock.consReturn (ExecStmt.return hret)

theorem bytesStoreSetMappedByteBodyReturnReverts {evm evm' : EVM.State}
    {I : ExecutionEnv}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hassign :
      assignStorageRef? bytesStoreConfig
        (bytesStoreSetMappedByteFrame I)
        evm .storage (mappedByteRef (.var "key") (.var "byteIndex"))
          (bytesStoreSetMappedByteValue I) =
          .ok (bytesStoreSetMappedByteFrame I, evm'))
    (hret :
      evalExpr? bytesStoreConfig
        (bytesStoreSetMappedByteFrame I)
        evm' (.storage (mappedByteRef (.var "key") (.var "byteIndex"))) = .revert) :
    ExecTransitionBody bytesStoreConfig bytesStoreContract evm
      (bytesStoreSetMappedByteLocals I) setMappedByteTransition.body .reverted := by
  let solm : Frame := bytesStoreSetMappedByteFrame I
  have hvalue :
      evalExpr? bytesStoreConfig solm evm (.var "value") =
        .ok (bytesStoreSetMappedByteValue I) := by
    exact evalExpr_var_of_get? (by
      simp [solm, bytesStoreSetMappedByteFrame, bytesStoreSetMappedByteValue,
        bytesStoreSetMappedByteLocals])
  have hassign :
      assignStorageRef? bytesStoreConfig solm evm .storage
        (mappedByteRef (.var "key") (.var "byteIndex"))
          (bytesStoreSetMappedByteValue I) =
          .ok (solm, evm') := by
    simpa [solm] using hassign
  have hret :
      evalExpr? bytesStoreConfig solm evm'
        (.storage (mappedByteRef (.var "key") (.var "byteIndex"))) = .revert := by
    simpa [solm] using hret
  exact ExecFuncBody.execBlockRevert <|
    ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consNormal (ExecStmt.assign hvalue hassign) <|
        ExecBlock.consRevert (ExecStmt.returnRevert hret)

theorem bytesStoreSetMappedByteEvalStorageRefOfLength {evm : EVM.State}
    {I : ExecutionEnv} {len : Nat}
    (hlen : readStorageBytesLength? bytesStoreConfig evm
      (bytesStoreSetMappedByteHeaderRef I) = .ok len)
    (hbound : (bytesStoreSetMappedByteIndexWord I).toNat < len) :
    evalStorageRef bytesStoreConfig
      (bytesStoreSetMappedByteFrame I)
      evm (mappedByteRef (.var "key") (.var "byteIndex")) =
        .ok (bytesStoreSetMappedByteRef I) := by
  have hgetKey :
      (bytesStoreSetMappedByteLocals I).get? "key" =
        some (.int (Int.ofNat (bytesStoreSetMappedByteKeyWord I).toNat)) :=
    bytesStoreSetMappedByteLocals_get_key I
  have hgetByteIndex :
      (bytesStoreSetMappedByteLocals I).get? "byteIndex" =
        some (.int (Int.ofNat (bytesStoreSetMappedByteIndexWord I).toNat)) :=
    bytesStoreSetMappedByteLocals_get_byteIndex I
  have hlen' :
      readStorageBytesLength?
        { storage :=
            { layout := bytesStoreLayout
              readValue? := solidityReadValue? bytesStoreLayout
              writeValue? := solidityWriteValue? bytesStoreLayout
              clearValue? := solidityClearValue? bytesStoreLayout
              readBytesLength := solidityReadBytesLength? bytesStoreLayout }
          externalABI := defaultExternalCallABI
          selfDeployment := genSolidityConstructorDeployment [] }
        evm
        { base := "mapped"
          steps := [
            .mindex (.int ((bytesStoreSetMappedByteKeyWord I).toNat : Int))] } =
        .ok len := by
    simpa [bytesStoreConfig, bytesStoreStorageLayout, solidityStorageLayout,
      bytesStoreSetMappedByteHeaderRef] using hlen
  have hindexKey :
      valueToKey? (.int (Int.ofNat (bytesStoreSetMappedByteIndexWord I).toNat)) =
        some (.int (Int.ofNat (bytesStoreSetMappedByteIndexWord I).toNat)) := by
    simp [valueToKey?]
  have hstep :
      evalStorageRefStep bytesStoreConfig (bytesStoreSetMappedByteFrame I) evm
        "mapped" [] (.mindex (.var "key")) =
        .ok (.mindex (.int (Int.ofNat (bytesStoreSetMappedByteKeyWord I).toNat))) := by
    have hgetKeyElem :
        (bytesStoreSetMappedByteLocals I)["key"]? =
          some (.int (Int.ofNat (bytesStoreSetMappedByteKeyWord I).toNat)) := by
      simpa [Std.HashMap.get?_eq_getElem?] using hgetKey
    simp [evalStorageRefStep, evalExpr?, bytesStoreSetMappedByteFrame,
      EvalResult.ofOption, EvalResult.bind, bind, pure, hgetKeyElem, valueToKey?]
  have hbounds :
      arrayIndexInBounds? bytesStoreConfig evm
        (bytesStoreSetMappedByteFrame I).contract.storage "mapped"
        [.mindex (.int (Int.ofNat (bytesStoreSetMappedByteKeyWord I).toNat))]
        (.int (Int.ofNat (bytesStoreSetMappedByteIndexWord I).toNat)) = .ok () := by
    simpa [arrayIndexInBounds?, storageTypeAt?, bytesStoreConfig,
      bytesStoreSetMappedByteFrame, bytesStoreContract, storageDecls,
      storageTypeStep?, bytesSt, bytesStoreStorageLayout, solidityStorageLayout,
      bytesStoreLayout, hlen'] using hbound
  simpa [mappedByteRef, bytesStoreSetMappedByteRef] using
    (evalStorageRef_step_aindex_var_of_get?_ok
      (cfg := bytesStoreConfig) (solm := bytesStoreSetMappedByteFrame I)
      (evm := evm) (base := "mapped") (name := "byteIndex")
      (step := .mindex (.var "key"))
      (estep := .mindex (.int (Int.ofNat (bytesStoreSetMappedByteKeyWord I).toNat)))
      hstep hgetByteIndex hindexKey hbounds)

theorem bytesStoreSetMappedByteEvalStorageRefRevertsOfLength {evm : EVM.State}
    {I : ExecutionEnv} {len : Nat}
    (hlen : readStorageBytesLength? bytesStoreConfig evm
      (bytesStoreSetMappedByteHeaderRef I) = .ok len)
    (hbound : ¬ (bytesStoreSetMappedByteIndexWord I).toNat < len) :
    evalStorageRef bytesStoreConfig
      (bytesStoreSetMappedByteFrame I)
      evm (mappedByteRef (.var "key") (.var "byteIndex")) = .revert := by
  have hgetKey :
      (bytesStoreSetMappedByteLocals I).get? "key" =
        some (.int (Int.ofNat (bytesStoreSetMappedByteKeyWord I).toNat)) :=
    bytesStoreSetMappedByteLocals_get_key I
  have hgetByteIndex :
      (bytesStoreSetMappedByteLocals I).get? "byteIndex" =
        some (.int (Int.ofNat (bytesStoreSetMappedByteIndexWord I).toNat)) :=
    bytesStoreSetMappedByteLocals_get_byteIndex I
  have hlen' :
      readStorageBytesLength?
        { storage :=
            { layout := bytesStoreLayout
              readValue? := solidityReadValue? bytesStoreLayout
              writeValue? := solidityWriteValue? bytesStoreLayout
              clearValue? := solidityClearValue? bytesStoreLayout
              readBytesLength := solidityReadBytesLength? bytesStoreLayout }
          externalABI := defaultExternalCallABI
          selfDeployment := genSolidityConstructorDeployment [] }
        evm
        { base := "mapped"
          steps := [
            .mindex (.int ((bytesStoreSetMappedByteKeyWord I).toNat : Int))] } =
        .ok len := by
    simpa [bytesStoreConfig, bytesStoreStorageLayout, solidityStorageLayout,
      bytesStoreSetMappedByteHeaderRef] using hlen
  have hindexKey :
      valueToKey? (.int (Int.ofNat (bytesStoreSetMappedByteIndexWord I).toNat)) =
        some (.int (Int.ofNat (bytesStoreSetMappedByteIndexWord I).toNat)) := by
    simp [valueToKey?]
  have hstep :
      evalStorageRefStep bytesStoreConfig (bytesStoreSetMappedByteFrame I) evm
        "mapped" [] (.mindex (.var "key")) =
        .ok (.mindex (.int (Int.ofNat (bytesStoreSetMappedByteKeyWord I).toNat))) := by
    have hgetKeyElem :
        (bytesStoreSetMappedByteLocals I)["key"]? =
          some (.int (Int.ofNat (bytesStoreSetMappedByteKeyWord I).toNat)) := by
      simpa [Std.HashMap.get?_eq_getElem?] using hgetKey
    simp [evalStorageRefStep, evalExpr?, bytesStoreSetMappedByteFrame,
      EvalResult.ofOption, EvalResult.bind, bind, pure, hgetKeyElem, valueToKey?]
  have hbounds :
      arrayIndexInBounds? bytesStoreConfig evm
        (bytesStoreSetMappedByteFrame I).contract.storage "mapped"
        [.mindex (.int (Int.ofNat (bytesStoreSetMappedByteKeyWord I).toNat))]
        (.int (Int.ofNat (bytesStoreSetMappedByteIndexWord I).toNat)) = .revert := by
    simpa [arrayIndexInBounds?, storageTypeAt?, bytesStoreConfig,
      bytesStoreSetMappedByteFrame, bytesStoreContract, storageDecls,
      storageTypeStep?, bytesSt, bytesStoreStorageLayout, solidityStorageLayout,
      bytesStoreLayout, hlen'] using Nat.le_of_not_gt hbound
  simpa [mappedByteRef] using
    (evalStorageRef_step_aindex_var_of_get?_revert
      (cfg := bytesStoreConfig) (solm := bytesStoreSetMappedByteFrame I)
      (evm := evm) (base := "mapped") (name := "byteIndex")
      (step := .mindex (.var "key"))
      (estep := .mindex (.int (Int.ofNat (bytesStoreSetMappedByteKeyWord I).toNat)))
      hstep hgetByteIndex hindexKey hbounds)

theorem bytesStoreSetMappedByteEvalStorageRefRevertsOfLengthRead {evm : EVM.State}
    {I : ExecutionEnv}
    (hlen : readStorageBytesLength? bytesStoreConfig evm
      (bytesStoreSetMappedByteHeaderRef I) = .revert) :
    evalStorageRef bytesStoreConfig
      (bytesStoreSetMappedByteFrame I)
      evm (mappedByteRef (.var "key") (.var "byteIndex")) = .revert := by
  have hgetKey :
      (bytesStoreSetMappedByteLocals I).get? "key" =
        some (.int (Int.ofNat (bytesStoreSetMappedByteKeyWord I).toNat)) :=
    bytesStoreSetMappedByteLocals_get_key I
  have hgetByteIndex :
      (bytesStoreSetMappedByteLocals I).get? "byteIndex" =
        some (.int (Int.ofNat (bytesStoreSetMappedByteIndexWord I).toNat)) :=
    bytesStoreSetMappedByteLocals_get_byteIndex I
  have hlen' :
      readStorageBytesLength?
        { storage :=
            { layout := bytesStoreLayout
              readValue? := solidityReadValue? bytesStoreLayout
              writeValue? := solidityWriteValue? bytesStoreLayout
              clearValue? := solidityClearValue? bytesStoreLayout
              readBytesLength := solidityReadBytesLength? bytesStoreLayout }
          externalABI := defaultExternalCallABI
          selfDeployment := genSolidityConstructorDeployment [] }
        evm
        { base := "mapped"
          steps := [
            .mindex (.int ((bytesStoreSetMappedByteKeyWord I).toNat : Int))] } =
        .revert := by
    simpa [bytesStoreConfig, bytesStoreStorageLayout, solidityStorageLayout,
      bytesStoreSetMappedByteHeaderRef] using hlen
  have hindexKey :
      valueToKey? (.int (Int.ofNat (bytesStoreSetMappedByteIndexWord I).toNat)) =
        some (.int (Int.ofNat (bytesStoreSetMappedByteIndexWord I).toNat)) := by
    simp [valueToKey?]
  have hstep :
      evalStorageRefStep bytesStoreConfig (bytesStoreSetMappedByteFrame I) evm
        "mapped" [] (.mindex (.var "key")) =
        .ok (.mindex (.int (Int.ofNat (bytesStoreSetMappedByteKeyWord I).toNat))) := by
    have hgetKeyElem :
        (bytesStoreSetMappedByteLocals I)["key"]? =
          some (.int (Int.ofNat (bytesStoreSetMappedByteKeyWord I).toNat)) := by
      simpa [Std.HashMap.get?_eq_getElem?] using hgetKey
    simp [evalStorageRefStep, evalExpr?, bytesStoreSetMappedByteFrame,
      EvalResult.ofOption, EvalResult.bind, bind, pure, hgetKeyElem, valueToKey?]
  have hbounds :
      arrayIndexInBounds? bytesStoreConfig evm
        (bytesStoreSetMappedByteFrame I).contract.storage "mapped"
        [.mindex (.int (Int.ofNat (bytesStoreSetMappedByteKeyWord I).toNat))]
        (.int (Int.ofNat (bytesStoreSetMappedByteIndexWord I).toNat)) = .revert := by
    simp [arrayIndexInBounds?, storageTypeAt?, bytesStoreConfig,
      bytesStoreSetMappedByteFrame, bytesStoreContract, storageDecls,
      storageTypeStep?, bytesSt, bytesStoreStorageLayout, solidityStorageLayout, hlen']
  simpa [mappedByteRef] using
    (evalStorageRef_step_aindex_var_of_get?_revert
      (cfg := bytesStoreConfig) (solm := bytesStoreSetMappedByteFrame I)
      (evm := evm) (base := "mapped") (name := "byteIndex")
      (step := .mindex (.var "key"))
      (estep := .mindex (.int (Int.ofNat (bytesStoreSetMappedByteKeyWord I).toNat)))
      hstep hgetByteIndex hindexKey hbounds)

theorem bytesStoreSetMappedByteResolveOfLength {evm : EVM.State}
    {I : ExecutionEnv} {len : Nat}
    (hlen : readStorageBytesLength? bytesStoreConfig evm
      (bytesStoreSetMappedByteHeaderRef I) = .ok len)
    (hbound : (bytesStoreSetMappedByteIndexWord I).toNat < len) :
    resolveStorageRef? bytesStoreConfig
      (bytesStoreSetMappedByteFrame I)
      evm (mappedByteRef (.var "key") (.var "byteIndex")) =
        .ok (bytesStoreSetMappedByteRef I, uint8St) := by
  have hgetMapped :
      (bytesStoreSetMappedByteLocals I).get? "mapped" = none :=
    bytesStoreSetMappedByteLocals_get_mapped_none I
  let sourceRef : StorageRef :=
    { base := "mapped"
      steps := [.mindex (.var "key"), .aindex (.var "byteIndex")] }
  have herInline' :
      evalStorageRef bytesStoreConfig
        ({ contract := bytesStoreContract, locals := bytesStoreSetMappedByteLocals I } :
          Frame)
        evm sourceRef =
          .ok (bytesStoreSetMappedByteRef I) := by
    simpa [sourceRef, mappedByteRef, bytesStoreSetMappedByteFrame] using
      (bytesStoreSetMappedByteEvalStorageRefOfLength
        (evm := evm) (I := I) (len := len) hlen hbound)
  exact resolveStorageRef?_ok hgetMapped herInline'
    bytesStoreSetMappedByte_storageTypeAt

theorem bytesStoreSetMappedByteAssignOfLength {evm evm' : EVM.State}
    {I : ExecutionEnv} {len : Nat}
    (hlen : readStorageBytesLength? bytesStoreConfig evm
      (bytesStoreSetMappedByteHeaderRef I) = .ok len)
    (hbound : (bytesStoreSetMappedByteIndexWord I).toNat < len)
    (hstore :
      (match bytesStoreConfig.storage.layout (bytesStoreSetMappedByteRef I) evm with
      | some loc => storageLocStore evm loc (bytesStoreSetMappedByteValue I)
      | none => none) = some evm') :
    assignStorageRef? bytesStoreConfig
      (bytesStoreSetMappedByteFrame I)
      evm .storage (mappedByteRef (.var "key") (.var "byteIndex"))
        (bytesStoreSetMappedByteValue I) =
        .ok (bytesStoreSetMappedByteFrame I, evm') := by
  exact assignStorageRef_storage_scalar_ok_of_resolve_match_store
    (bytesStoreSetMappedByteResolveOfLength (I := I) hlen hbound)
    hstore
    (by simp [bytesStoreSetMappedByteValue])

theorem bytesStoreSetMappedByteShortBodyReturns
    {evm : EVM.State} {σ : AccountMap} {I : ExecutionEnv} {len : UInt256}
    {acc : Account}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hloadHeader : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (bytesStoreSetMappedByteSlot I) = bytesStoreSetMappedByteHeaderWord σ I)
    (hacc : evm.accountMap.find? evm.executionEnv.codeOwner = some acc)
    (hcanon : (bytesStoreSetMappedByteValueWord I).toNat < EVM.twoPow 8)
    (hlen : len =
      UInt256.land (UInt256.div (bytesStoreSetMappedByteHeaderWord σ I) ⟨2⟩) ⟨127⟩)
    (hshort : len.toNat < 32)
    (hbound : (bytesStoreSetMappedByteIndexWord I).toNat < len.toNat)
    (hflag : UInt256.land (bytesStoreSetMappedByteHeaderWord σ I) ⟨1⟩ = ⟨0⟩)
    (_hvalid : UInt256.sub (UInt256.land (bytesStoreSetMappedByteHeaderWord σ I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStoreSetMappedByteHeaderWord σ I) ⟨2⟩)
            ⟨127⟩) ⟨32⟩) ≠ ⟨0⟩) :
    ExecTransitionBody bytesStoreConfig bytesStoreContract evm
      (bytesStoreSetMappedByteLocals I) setMappedByteTransition.body
      (.returned
        (bytesStoreSetMappedByteFrame I)
        (Solm.EVM.storageStore evm evm.executionEnv.codeOwner
          (bytesStoreSetMappedByteSlot I)
          (bytesStoreSetMappedByteShortStoredWord σ I))
        (some (bytesStoreSetMappedByteValue I))) := by
  let evm' := Solm.EVM.storageStore evm evm.executionEnv.codeOwner
    (bytesStoreSetMappedByteSlot I)
    (bytesStoreSetMappedByteShortStoredWord σ I)
  have hlenRead :
      readStorageBytesLength? bytesStoreConfig evm
          (bytesStoreSetMappedByteHeaderRef I) =
        .ok len.toNat := by
    have hltLen : UInt256.lt len ⟨32⟩ = ⟨1⟩ := by
      exact ult_one (by
        simpa [show (⟨32⟩ : UInt256).toNat = 32 from by decide] using hshort)
    have hvalidLen : UInt256.sub ⟨0⟩ (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩ := by
      rw [hltLen]
      native_decide
    exact bytesStoreReadLengthOfHeaderLoad
      (er := bytesStoreSetMappedByteHeaderRef I) (evm := evm)
      (baseSlot := bytesStoreSetMappedByteSlot I)
      (header := bytesStoreSetMappedByteHeaderWord σ I) (len := len.toNat)
      (bytesStoreSetMappedByteHeaderRef_length_slot evm I)
      hloadHeader
      (solidityDecodeBytesLengthHeader_short_valid hflag hlen (by simpa [hflag] using hvalidLen))
  have hpacked : checkBytesPacked (bytesStoreSetMappedByteSlot I) evm = true :=
    checkBytesPacked_of_storageLoad_land_one_zero hloadHeader hflag
  have hidx31 : (bytesStoreSetMappedByteIndexWord I).toNat < 31 :=
    bytesStoreSetMappedByteIndex_lt31_of_short_bound (I := I) (len := len)
      hshort hbound
  have hlayout :
      bytesStoreConfig.storage.layout (bytesStoreSetMappedByteRef I) evm =
        some (uint8Loc (bytesStoreSetMappedByteSlot I)
          ⟨31 - (bytesStoreSetMappedByteIndexWord I).toNat, by omega⟩) :=
    bytesStoreSetMappedByteLayoutShort (evm := evm) (I := I) hpacked hidx31
  have hstore :
      (match bytesStoreConfig.storage.layout (bytesStoreSetMappedByteRef I) evm with
      | some loc => storageLocStore evm loc (bytesStoreSetMappedByteValue I)
      | none => none) = some evm' := by
    rw [hlayout]
    simpa [evm'] using
      bytesStoreSetMappedByteStorageLocStoreShort
        (evm := evm) (σ := σ) (I := I) (len := len)
        hloadHeader hcanon hshort hbound
  have hassign :
      assignStorageRef? bytesStoreConfig
        (bytesStoreSetMappedByteFrame I)
        evm .storage (mappedByteRef (.var "key") (.var "byteIndex"))
          (bytesStoreSetMappedByteValue I) =
          .ok (bytesStoreSetMappedByteFrame I, evm') :=
    bytesStoreSetMappedByteAssignOfLength (evm := evm) (evm' := evm') (I := I)
      hlenRead hbound hstore
  have hloadPost :
      Solm.EVM.storageLoad evm' evm'.executionEnv.codeOwner
          (bytesStoreSetMappedByteSlot I) =
        bytesStoreSetMappedByteShortStoredWord σ I := by
    simpa [evm'] using
      storageLoad_storageStore_codeOwner_same_present evm hacc
        (bytesStoreSetMappedByteSlot I)
        (bytesStoreSetMappedByteShortStoredWord σ I)
  have hflagPost :
      UInt256.land (bytesStoreSetMappedByteShortStoredWord σ I) ⟨1⟩ = ⟨0⟩ := by
    rw [bytesStoreSetMappedByteShortStoredWord_flag_eq
      (σ := σ) (I := I) (len := len) hshort hbound, hflag]
  have hlenPost :
      readStorageBytesLength? bytesStoreConfig evm'
          (bytesStoreSetMappedByteHeaderRef I) =
        .ok len.toNat := by
    have hltLen : UInt256.lt len ⟨32⟩ = ⟨1⟩ := by
      exact ult_one (by
        simpa [show (⟨32⟩ : UInt256).toNat = 32 from by decide] using hshort)
    have hvalidLen : UInt256.sub ⟨0⟩ (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩ := by
      rw [hltLen]
      native_decide
    have hlenPostWord :
        UInt256.land
            (UInt256.div (bytesStoreSetMappedByteShortStoredWord σ I) ⟨2⟩) ⟨127⟩ =
          len := by
      rw [bytesStoreSetMappedByteShortStoredWord_shortLen_eq
        (σ := σ) (I := I) (len := len) hshort hbound]
      exact hlen.symm
    exact bytesStoreReadLengthOfHeaderLoad
      (er := bytesStoreSetMappedByteHeaderRef I) (evm := evm')
      (baseSlot := bytesStoreSetMappedByteSlot I)
      (header := bytesStoreSetMappedByteShortStoredWord σ I) (len := len.toNat)
      (bytesStoreSetMappedByteHeaderRef_length_slot evm' I)
      hloadPost
      (solidityDecodeBytesLengthHeader_short_valid hflagPost hlenPostWord.symm
        (by simpa [hflagPost] using hvalidLen))
  have hpackedPost : checkBytesPacked (bytesStoreSetMappedByteSlot I) evm' = true :=
    checkBytesPacked_of_storageLoad_land_one_zero hloadPost hflagPost
  have hlayoutPost :
      bytesStoreConfig.storage.layout (bytesStoreSetMappedByteRef I) evm' =
        some (uint8Loc (bytesStoreSetMappedByteSlot I)
          ⟨31 - (bytesStoreSetMappedByteIndexWord I).toNat, by omega⟩) :=
    bytesStoreSetMappedByteLayoutShort (evm := evm') (I := I) hpackedPost hidx31
  have hidxLe : (bytesStoreSetMappedByteIndexWord I).toNat ≤ 31 := by
    omega
  have hret :
      evalExpr? bytesStoreConfig
        (bytesStoreSetMappedByteFrame I)
        evm' (.storage (mappedByteRef (.var "key") (.var "byteIndex"))) =
          .ok (bytesStoreSetMappedByteValue I) := by
    rw [evalExpr_storage_scalar_of_resolve_layout
      (bytesStoreSetMappedByteResolveOfLength
        (evm := evm') (I := I) (len := len.toNat) hlenPost hbound)
      hlayoutPost]
    rw [storageLocLoad_uint8Loc_byteAt
      (slot := bytesStoreSetMappedByteSlot I)
      (idx := bytesStoreSetMappedByteIndexWord I)
      (off := ⟨31 - (bytesStoreSetMappedByteIndexWord I).toNat, by omega⟩)
      (hoff := by rfl) (hidx := hidxLe)]
    rw [hloadPost]
    rw [bytesStoreSetMappedByteShortStoredWord_byteAt
      (σ := σ) (I := I) (len := len) hcanon hshort hbound]
    simp [bytesStoreSetMappedByteValue]
  simpa [evm'] using
    bytesStoreSetMappedByteBodyReturns (evm := evm) (evm' := evm') (I := I)
      hwv hassign hret

theorem bytesStoreSetMappedByteLongBodyReturns_of_post_readback
    {evm : EVM.State} {σ : AccountMap} {I : ExecutionEnv} {len : UInt256}
    {acc : Account}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hloadHeader : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (bytesStoreSetMappedByteSlot I) = bytesStoreSetMappedByteHeaderWord σ I)
    (hloadData : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (bytesStoreSetMappedByteLongDataSlot I) =
      bytesStoreSetMappedByteLongOldWord σ I)
    (hloadHeaderPost :
      Solm.EVM.storageLoad
          (Solm.EVM.storageStore evm evm.executionEnv.codeOwner
            (bytesStoreSetMappedByteLongDataSlot I)
            (bytesStoreSetMappedByteLongStoredWord σ I))
          (Solm.EVM.storageStore evm evm.executionEnv.codeOwner
            (bytesStoreSetMappedByteLongDataSlot I)
            (bytesStoreSetMappedByteLongStoredWord σ I)).executionEnv.codeOwner
          (bytesStoreSetMappedByteSlot I) =
        bytesStoreSetMappedByteHeaderWord σ I)
    (hacc : evm.accountMap.find? evm.executionEnv.codeOwner = some acc)
    (hcanon : (bytesStoreSetMappedByteValueWord I).toNat < EVM.twoPow 8)
    (hlen : len = UInt256.div (bytesStoreSetMappedByteHeaderWord σ I) ⟨2⟩)
    (hbound : (bytesStoreSetMappedByteIndexWord I).toNat < len.toNat)
    (hflag : UInt256.land (bytesStoreSetMappedByteHeaderWord σ I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (bytesStoreSetMappedByteHeaderWord σ I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStoreSetMappedByteHeaderWord σ I) ⟨2⟩) ⟨32⟩) ≠
          ⟨0⟩) :
    ExecTransitionBody bytesStoreConfig bytesStoreContract evm
      (bytesStoreSetMappedByteLocals I) setMappedByteTransition.body
      (.returned
        (bytesStoreSetMappedByteFrame I)
        (Solm.EVM.storageStore evm evm.executionEnv.codeOwner
          (bytesStoreSetMappedByteLongDataSlot I)
          (bytesStoreSetMappedByteLongStoredWord σ I))
        (some (bytesStoreSetMappedByteValue I))) := by
  let evm' := Solm.EVM.storageStore evm evm.executionEnv.codeOwner
    (bytesStoreSetMappedByteLongDataSlot I)
    (bytesStoreSetMappedByteLongStoredWord σ I)
  have hvalidLen :
      UInt256.sub (UInt256.land (bytesStoreSetMappedByteHeaderWord σ I) ⟨1⟩)
        (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩ := by
    simpa [hlen] using hvalid
  have hlenRead :
      readStorageBytesLength? bytesStoreConfig evm
          (bytesStoreSetMappedByteHeaderRef I) =
        .ok len.toNat := by
    exact bytesStoreReadLengthOfHeaderLoad
      (er := bytesStoreSetMappedByteHeaderRef I) (evm := evm)
      (baseSlot := bytesStoreSetMappedByteSlot I)
      (header := bytesStoreSetMappedByteHeaderWord σ I) (len := len.toNat)
      (bytesStoreSetMappedByteHeaderRef_length_slot evm I)
      hloadHeader
      (solidityDecodeBytesLengthHeader_long_valid hflag hlen hvalidLen)
  have hpacked : checkBytesPacked (bytesStoreSetMappedByteSlot I) evm = false :=
    checkBytesPacked_of_storageLoad_land_one_ne_zero hloadHeader hflag
  have hlayout :
      bytesStoreConfig.storage.layout (bytesStoreSetMappedByteRef I) evm =
        some (uint8Loc (bytesStoreSetMappedByteLongDataSlot I)
          ⟨31 - (bytesStoreSetMappedByteLongWordIndex I).toNat, by
            have hidx := bytesStoreSetMappedByteLongWordIndex_lt32 I
            omega⟩) :=
    bytesStoreSetMappedByteLayoutLong (evm := evm) (I := I) hpacked
  have hstore :
      (match bytesStoreConfig.storage.layout (bytesStoreSetMappedByteRef I) evm with
      | some loc => storageLocStore evm loc (bytesStoreSetMappedByteValue I)
      | none => none) = some evm' := by
    rw [hlayout]
    simpa [evm'] using
      bytesStoreSetMappedByteStorageLocStoreLong
        (evm := evm) (σ := σ) (I := I) hloadData hcanon
  have hassign :
      assignStorageRef? bytesStoreConfig
        (bytesStoreSetMappedByteFrame I)
        evm .storage (mappedByteRef (.var "key") (.var "byteIndex"))
          (bytesStoreSetMappedByteValue I) =
          .ok (bytesStoreSetMappedByteFrame I, evm') :=
    bytesStoreSetMappedByteAssignOfLength (evm := evm) (evm' := evm') (I := I)
      hlenRead hbound hstore
  have hlenPost :
      readStorageBytesLength? bytesStoreConfig evm'
          (bytesStoreSetMappedByteHeaderRef I) =
        .ok len.toNat := by
    exact bytesStoreReadLengthOfHeaderLoad
      (er := bytesStoreSetMappedByteHeaderRef I) (evm := evm')
      (baseSlot := bytesStoreSetMappedByteSlot I)
      (header := bytesStoreSetMappedByteHeaderWord σ I) (len := len.toNat)
      (bytesStoreSetMappedByteHeaderRef_length_slot evm' I)
      hloadHeaderPost
      (solidityDecodeBytesLengthHeader_long_valid hflag hlen hvalidLen)
  have hpackedPost : checkBytesPacked (bytesStoreSetMappedByteSlot I) evm' = false :=
    checkBytesPacked_of_storageLoad_land_one_ne_zero hloadHeaderPost hflag
  have hlayoutPost :
      bytesStoreConfig.storage.layout (bytesStoreSetMappedByteRef I) evm' =
        some (uint8Loc (bytesStoreSetMappedByteLongDataSlot I)
          ⟨31 - (bytesStoreSetMappedByteLongWordIndex I).toNat, by
            have hidx := bytesStoreSetMappedByteLongWordIndex_lt32 I
            omega⟩) :=
    bytesStoreSetMappedByteLayoutLong (evm := evm') (I := I) hpackedPost
  have hloadDataPost :
      Solm.EVM.storageLoad evm' evm'.executionEnv.codeOwner
          (bytesStoreSetMappedByteLongDataSlot I) =
        bytesStoreSetMappedByteLongStoredWord σ I := by
    simpa [evm'] using
      storageLoad_storageStore_codeOwner_same_present evm hacc
        (bytesStoreSetMappedByteLongDataSlot I)
        (bytesStoreSetMappedByteLongStoredWord σ I)
  have hret :
      evalExpr? bytesStoreConfig
        (bytesStoreSetMappedByteFrame I)
        evm' (.storage (mappedByteRef (.var "key") (.var "byteIndex"))) =
          .ok (bytesStoreSetMappedByteValue I) := by
    rw [evalExpr_storage_scalar_of_resolve_layout
      (bytesStoreSetMappedByteResolveOfLength
        (evm := evm') (I := I) (len := len.toNat) hlenPost hbound)
      hlayoutPost]
    rw [storageLocLoad_uint8Loc_byteAt
      (evm := evm') (slot := bytesStoreSetMappedByteLongDataSlot I)
      (idx := bytesStoreSetMappedByteLongWordIndex I)
      (off := ⟨31 - (bytesStoreSetMappedByteLongWordIndex I).toNat, by
        have hidx := bytesStoreSetMappedByteLongWordIndex_lt32 I
        omega⟩)
      (by rfl)
      (by
        have hidx := bytesStoreSetMappedByteLongWordIndex_lt32 I
        omega)]
    rw [hloadDataPost]
    rw [bytesStoreSetMappedByteLongStoredWord_byteAt (σ := σ) (I := I) hcanon]
    simp [bytesStoreSetMappedByteValue]
  simpa [evm'] using
    bytesStoreSetMappedByteBodyReturns (evm := evm) (evm' := evm') (I := I)
      hwv hassign hret

theorem bytesStoreSetMappedByteLongBodyReturnsOfPostLongReadback
    {evm : EVM.State} {σ : AccountMap} {I : ExecutionEnv}
    {len lenPost postHeaderWord : UInt256} {acc : Account}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hloadHeader : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (bytesStoreSetMappedByteSlot I) = bytesStoreSetMappedByteHeaderWord σ I)
    (hloadData : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (bytesStoreSetMappedByteLongDataSlot I) =
      bytesStoreSetMappedByteLongOldWord σ I)
    (hloadHeaderPost :
      Solm.EVM.storageLoad
          (Solm.EVM.storageStore evm evm.executionEnv.codeOwner
            (bytesStoreSetMappedByteLongDataSlot I)
            (bytesStoreSetMappedByteLongStoredWord σ I))
          evm.executionEnv.codeOwner
          (bytesStoreSetMappedByteSlot I) =
        postHeaderWord)
    (hacc : evm.accountMap.find? evm.executionEnv.codeOwner = some acc)
    (hcanon : (bytesStoreSetMappedByteValueWord I).toNat < EVM.twoPow 8)
    (hlen : len = UInt256.div (bytesStoreSetMappedByteHeaderWord σ I) ⟨2⟩)
    (hlenPost : lenPost = UInt256.div postHeaderWord ⟨2⟩)
    (hbound : (bytesStoreSetMappedByteIndexWord I).toNat < len.toNat)
    (hboundPost : (bytesStoreSetMappedByteIndexWord I).toNat < lenPost.toNat)
    (hflag : UInt256.land (bytesStoreSetMappedByteHeaderWord σ I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (bytesStoreSetMappedByteHeaderWord σ I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStoreSetMappedByteHeaderWord σ I) ⟨2⟩) ⟨32⟩) ≠
          ⟨0⟩)
    (hflagPost : UInt256.land postHeaderWord ⟨1⟩ ≠ ⟨0⟩)
    (hvalidPost : UInt256.sub (UInt256.land postHeaderWord ⟨1⟩)
        (UInt256.lt (UInt256.div postHeaderWord ⟨2⟩) ⟨32⟩) ≠ ⟨0⟩) :
    ExecTransitionBody bytesStoreConfig bytesStoreContract evm
      (bytesStoreSetMappedByteLocals I) setMappedByteTransition.body
      (.returned
        (bytesStoreSetMappedByteFrame I)
        (Solm.EVM.storageStore evm evm.executionEnv.codeOwner
          (bytesStoreSetMappedByteLongDataSlot I)
          (bytesStoreSetMappedByteLongStoredWord σ I))
        (some (bytesStoreSetMappedByteValue I))) := by
  let evm' := Solm.EVM.storageStore evm evm.executionEnv.codeOwner
    (bytesStoreSetMappedByteLongDataSlot I)
    (bytesStoreSetMappedByteLongStoredWord σ I)
  have hloadHeaderPost' :
      Solm.EVM.storageLoad evm' evm'.executionEnv.codeOwner
          (bytesStoreSetMappedByteSlot I) =
        postHeaderWord := by
    simpa [evm', storageStore_executionEnv] using hloadHeaderPost
  have hvalidLen :
      UInt256.sub (UInt256.land (bytesStoreSetMappedByteHeaderWord σ I) ⟨1⟩)
        (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩ := by
    simpa [hlen] using hvalid
  have hlenRead :
      readStorageBytesLength? bytesStoreConfig evm
          (bytesStoreSetMappedByteHeaderRef I) =
        .ok len.toNat := by
    exact bytesStoreReadLengthOfHeaderLoad
      (er := bytesStoreSetMappedByteHeaderRef I) (evm := evm)
      (baseSlot := bytesStoreSetMappedByteSlot I)
      (header := bytesStoreSetMappedByteHeaderWord σ I) (len := len.toNat)
      (bytesStoreSetMappedByteHeaderRef_length_slot evm I)
      hloadHeader
      (solidityDecodeBytesLengthHeader_long_valid hflag hlen hvalidLen)
  have hpacked : checkBytesPacked (bytesStoreSetMappedByteSlot I) evm = false :=
    checkBytesPacked_of_storageLoad_land_one_ne_zero hloadHeader hflag
  have hlayout :
      bytesStoreConfig.storage.layout (bytesStoreSetMappedByteRef I) evm =
        some (uint8Loc (bytesStoreSetMappedByteLongDataSlot I)
          ⟨31 - (bytesStoreSetMappedByteLongWordIndex I).toNat, by
            have hidx := bytesStoreSetMappedByteLongWordIndex_lt32 I
            omega⟩) :=
    bytesStoreSetMappedByteLayoutLong (evm := evm) (I := I) hpacked
  have hstore :
      (match bytesStoreConfig.storage.layout (bytesStoreSetMappedByteRef I) evm with
      | some loc => storageLocStore evm loc (bytesStoreSetMappedByteValue I)
      | none => none) = some evm' := by
    rw [hlayout]
    simpa [evm'] using
      bytesStoreSetMappedByteStorageLocStoreLong
        (evm := evm) (σ := σ) (I := I) hloadData hcanon
  have hassign :
      assignStorageRef? bytesStoreConfig
        (bytesStoreSetMappedByteFrame I)
        evm .storage (mappedByteRef (.var "key") (.var "byteIndex"))
          (bytesStoreSetMappedByteValue I) =
          .ok (bytesStoreSetMappedByteFrame I, evm') :=
    bytesStoreSetMappedByteAssignOfLength (evm := evm) (evm' := evm') (I := I)
      hlenRead hbound hstore
  have hlenPostRead :
      readStorageBytesLength? bytesStoreConfig evm'
          (bytesStoreSetMappedByteHeaderRef I) =
        .ok lenPost.toNat := by
    have hvalidLenPost :
        UInt256.sub (UInt256.land postHeaderWord ⟨1⟩)
          (UInt256.lt lenPost ⟨32⟩) ≠ ⟨0⟩ := by
      simpa [hlenPost] using hvalidPost
    exact bytesStoreReadLengthOfHeaderLoad
      (er := bytesStoreSetMappedByteHeaderRef I) (evm := evm')
      (baseSlot := bytesStoreSetMappedByteSlot I)
      (header := postHeaderWord) (len := lenPost.toNat)
      (bytesStoreSetMappedByteHeaderRef_length_slot evm' I)
      hloadHeaderPost'
      (solidityDecodeBytesLengthHeader_long_valid hflagPost hlenPost hvalidLenPost)
  have hpackedPost : checkBytesPacked (bytesStoreSetMappedByteSlot I) evm' = false :=
    checkBytesPacked_of_storageLoad_land_one_ne_zero hloadHeaderPost' hflagPost
  have hlayoutPost :
      bytesStoreConfig.storage.layout (bytesStoreSetMappedByteRef I) evm' =
        some (uint8Loc (bytesStoreSetMappedByteLongDataSlot I)
          ⟨31 - (bytesStoreSetMappedByteLongWordIndex I).toNat, by
            have hidx := bytesStoreSetMappedByteLongWordIndex_lt32 I
            omega⟩) :=
    bytesStoreSetMappedByteLayoutLong (evm := evm') (I := I) hpackedPost
  have hloadDataPost :
      Solm.EVM.storageLoad evm' evm'.executionEnv.codeOwner
          (bytesStoreSetMappedByteLongDataSlot I) =
        bytesStoreSetMappedByteLongStoredWord σ I := by
    simpa [evm'] using
      storageLoad_storageStore_codeOwner_same_present evm hacc
        (bytesStoreSetMappedByteLongDataSlot I)
        (bytesStoreSetMappedByteLongStoredWord σ I)
  have hret :
      evalExpr? bytesStoreConfig
        (bytesStoreSetMappedByteFrame I)
        evm' (.storage (mappedByteRef (.var "key") (.var "byteIndex"))) =
          .ok (bytesStoreSetMappedByteValue I) := by
    rw [evalExpr_storage_scalar_of_resolve_layout
      (bytesStoreSetMappedByteResolveOfLength
        (evm := evm') (I := I) (len := lenPost.toNat) hlenPostRead hboundPost)
      hlayoutPost]
    rw [storageLocLoad_uint8Loc_byteAt
      (evm := evm') (slot := bytesStoreSetMappedByteLongDataSlot I)
      (idx := bytesStoreSetMappedByteLongWordIndex I)
      (off := ⟨31 - (bytesStoreSetMappedByteLongWordIndex I).toNat, by
        have hidx := bytesStoreSetMappedByteLongWordIndex_lt32 I
        omega⟩)
      (by rfl)
      (by
        have hidx := bytesStoreSetMappedByteLongWordIndex_lt32 I
        omega)]
    rw [hloadDataPost]
    rw [bytesStoreSetMappedByteLongStoredWord_byteAt (σ := σ) (I := I) hcanon]
    simp [bytesStoreSetMappedByteValue]
  simpa [evm'] using
    bytesStoreSetMappedByteBodyReturns (evm := evm) (evm' := evm') (I := I)
      hwv hassign hret

theorem bytesStoreSetMappedByteLongBodyReturnsOfPostShortReadback
    {evm : EVM.State} {σ : AccountMap} {I : ExecutionEnv}
    {len lenPost postHeaderWord : UInt256}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hloadHeader : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (bytesStoreSetMappedByteSlot I) = bytesStoreSetMappedByteHeaderWord σ I)
    (hloadData : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (bytesStoreSetMappedByteLongDataSlot I) =
      bytesStoreSetMappedByteLongOldWord σ I)
    (hloadHeaderPost :
      Solm.EVM.storageLoad
          (Solm.EVM.storageStore evm evm.executionEnv.codeOwner
            (bytesStoreSetMappedByteLongDataSlot I)
            (bytesStoreSetMappedByteLongStoredWord σ I))
          evm.executionEnv.codeOwner
          (bytesStoreSetMappedByteSlot I) =
        postHeaderWord)
    (hcanon : (bytesStoreSetMappedByteValueWord I).toNat < EVM.twoPow 8)
    (hlen : len = UInt256.div (bytesStoreSetMappedByteHeaderWord σ I) ⟨2⟩)
    (hlenPost : lenPost = UInt256.land (UInt256.div postHeaderWord ⟨2⟩) ⟨127⟩)
    (hbound : (bytesStoreSetMappedByteIndexWord I).toNat < len.toNat)
    (hboundPost : (bytesStoreSetMappedByteIndexWord I).toNat < lenPost.toNat)
    (hflag : UInt256.land (bytesStoreSetMappedByteHeaderWord σ I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (bytesStoreSetMappedByteHeaderWord σ I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStoreSetMappedByteHeaderWord σ I) ⟨2⟩) ⟨32⟩) ≠
          ⟨0⟩)
    (hflagPost : UInt256.land postHeaderWord ⟨1⟩ = ⟨0⟩)
    (hvalidPost : UInt256.sub (UInt256.land postHeaderWord ⟨1⟩)
        (UInt256.lt (UInt256.land (UInt256.div postHeaderWord ⟨2⟩) ⟨127⟩) ⟨32⟩) ≠
          ⟨0⟩)
    (hbytePost :
      UInt256.byteAt (bytesStoreSetMappedByteIndexWord I) postHeaderWord =
        bytesStoreSetMappedByteValueWord I) :
    ExecTransitionBody bytesStoreConfig bytesStoreContract evm
      (bytesStoreSetMappedByteLocals I) setMappedByteTransition.body
      (.returned
        (bytesStoreSetMappedByteFrame I)
        (Solm.EVM.storageStore evm evm.executionEnv.codeOwner
          (bytesStoreSetMappedByteLongDataSlot I)
          (bytesStoreSetMappedByteLongStoredWord σ I))
        (some (bytesStoreSetMappedByteValue I))) := by
  let evm' := Solm.EVM.storageStore evm evm.executionEnv.codeOwner
    (bytesStoreSetMappedByteLongDataSlot I)
    (bytesStoreSetMappedByteLongStoredWord σ I)
  have hloadHeaderPost' :
      Solm.EVM.storageLoad evm' evm'.executionEnv.codeOwner
          (bytesStoreSetMappedByteSlot I) =
        postHeaderWord := by
    simpa [evm', storageStore_executionEnv] using hloadHeaderPost
  have hvalidLen :
      UInt256.sub (UInt256.land (bytesStoreSetMappedByteHeaderWord σ I) ⟨1⟩)
        (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩ := by
    simpa [hlen] using hvalid
  have hlenRead :
      readStorageBytesLength? bytesStoreConfig evm
          (bytesStoreSetMappedByteHeaderRef I) =
        .ok len.toNat := by
    exact bytesStoreReadLengthOfHeaderLoad
      (er := bytesStoreSetMappedByteHeaderRef I) (evm := evm)
      (baseSlot := bytesStoreSetMappedByteSlot I)
      (header := bytesStoreSetMappedByteHeaderWord σ I) (len := len.toNat)
      (bytesStoreSetMappedByteHeaderRef_length_slot evm I)
      hloadHeader
      (solidityDecodeBytesLengthHeader_long_valid hflag hlen hvalidLen)
  have hpacked : checkBytesPacked (bytesStoreSetMappedByteSlot I) evm = false :=
    checkBytesPacked_of_storageLoad_land_one_ne_zero hloadHeader hflag
  have hlayout :
      bytesStoreConfig.storage.layout (bytesStoreSetMappedByteRef I) evm =
        some (uint8Loc (bytesStoreSetMappedByteLongDataSlot I)
          ⟨31 - (bytesStoreSetMappedByteLongWordIndex I).toNat, by
            have hidx := bytesStoreSetMappedByteLongWordIndex_lt32 I
            omega⟩) :=
    bytesStoreSetMappedByteLayoutLong (evm := evm) (I := I) hpacked
  have hstore :
      (match bytesStoreConfig.storage.layout (bytesStoreSetMappedByteRef I) evm with
      | some loc => storageLocStore evm loc (bytesStoreSetMappedByteValue I)
      | none => none) = some evm' := by
    rw [hlayout]
    simpa [evm'] using
      bytesStoreSetMappedByteStorageLocStoreLong
        (evm := evm) (σ := σ) (I := I) hloadData hcanon
  have hassign :
      assignStorageRef? bytesStoreConfig
        (bytesStoreSetMappedByteFrame I)
        evm .storage (mappedByteRef (.var "key") (.var "byteIndex"))
          (bytesStoreSetMappedByteValue I) =
          .ok (bytesStoreSetMappedByteFrame I, evm') :=
    bytesStoreSetMappedByteAssignOfLength (evm := evm) (evm' := evm') (I := I)
      hlenRead hbound hstore
  have hlenPostRead :
      readStorageBytesLength? bytesStoreConfig evm'
          (bytesStoreSetMappedByteHeaderRef I) =
        .ok lenPost.toNat := by
    have hvalidLenPost :
        UInt256.sub ⟨0⟩ (UInt256.lt lenPost ⟨32⟩) ≠ ⟨0⟩ := by
      simpa [hlenPost, hflagPost] using hvalidPost
    exact bytesStoreReadLengthOfHeaderLoad
      (er := bytesStoreSetMappedByteHeaderRef I) (evm := evm')
      (baseSlot := bytesStoreSetMappedByteSlot I)
      (header := postHeaderWord) (len := lenPost.toNat)
      (bytesStoreSetMappedByteHeaderRef_length_slot evm' I)
      hloadHeaderPost'
      (solidityDecodeBytesLengthHeader_short_valid hflagPost hlenPost
        (by simpa [← hlenPost] using hvalidPost))
  have hpackedPost : checkBytesPacked (bytesStoreSetMappedByteSlot I) evm' = true :=
    checkBytesPacked_of_storageLoad_land_one_zero hloadHeaderPost' hflagPost
  have hshortPost : lenPost.toNat < 32 := by
    have hvalidLenPost :
        UInt256.sub ⟨0⟩ (UInt256.lt lenPost ⟨32⟩) ≠ ⟨0⟩ := by
      simpa [hlenPost, hflagPost] using hvalidPost
    exact solidityShortBytesValid_lt32 hvalidLenPost
  have hidx31 : (bytesStoreSetMappedByteIndexWord I).toNat < 31 :=
    bytesStoreSetMappedByteIndex_lt31_of_short_bound (I := I) (len := lenPost)
      hshortPost hboundPost
  have hlayoutPost :
      bytesStoreConfig.storage.layout (bytesStoreSetMappedByteRef I) evm' =
        some (uint8Loc (bytesStoreSetMappedByteSlot I)
          ⟨31 - (bytesStoreSetMappedByteIndexWord I).toNat, by omega⟩) :=
    bytesStoreSetMappedByteLayoutShort (evm := evm') (I := I) hpackedPost hidx31
  have hidxLe : (bytesStoreSetMappedByteIndexWord I).toNat ≤ 31 := by
    omega
  have hret :
      evalExpr? bytesStoreConfig
        (bytesStoreSetMappedByteFrame I)
        evm' (.storage (mappedByteRef (.var "key") (.var "byteIndex"))) =
          .ok (bytesStoreSetMappedByteValue I) := by
    rw [evalExpr_storage_scalar_of_resolve_layout
      (bytesStoreSetMappedByteResolveOfLength
        (evm := evm') (I := I) (len := lenPost.toNat) hlenPostRead hboundPost)
      hlayoutPost]
    rw [storageLocLoad_uint8Loc_byteAt
      (slot := bytesStoreSetMappedByteSlot I)
      (idx := bytesStoreSetMappedByteIndexWord I)
      (off := ⟨31 - (bytesStoreSetMappedByteIndexWord I).toNat, by omega⟩)
      (hoff := by rfl) (hidx := hidxLe)]
    rw [hloadHeaderPost']
    rw [hbytePost]
    simp [bytesStoreSetMappedByteValue]
  simpa [evm'] using
    bytesStoreSetMappedByteBodyReturns (evm := evm) (evm' := evm') (I := I)
      hwv hassign hret

private theorem bytesStoreSetMappedByteDecodeLenCheckOk {sz : ℕ}
    (hlen : 100 ≤ sz) (hhi : sz < 2 ^ 255 + 4) (hsz : sz < UInt256.size) :
    UInt256.slt (UInt256.sub (UInt256.ofNat sz) ⟨4⟩) ⟨96⟩ = ⟨0⟩ := by
  exact solcCalldataStaticLenCheckOk (words := 3) (by simpa using hlen) hhi hsz

private theorem bytesStoreSetMappedByteDecodeLenCheckShort {sz : ℕ}
    (hhead : 4 ≤ sz) (hshort : sz < 100) (hsz : sz < UInt256.size) :
    UInt256.slt (UInt256.sub (UInt256.ofNat sz) ⟨4⟩) ⟨96⟩ = ⟨1⟩ := by
  exact solcCalldataStaticLenCheckShort (words := 3) hhead (by simpa using hshort) hsz
    (by norm_num)

private theorem bytesStoreSetMappedByteDecodeLenCheckHuge {sz : ℕ}
    (hbig : 2 ^ 255 + 4 ≤ sz) (hsz : sz < UInt256.size) :
    UInt256.slt (UInt256.sub (UInt256.ofNat sz) ⟨4⟩) ⟨96⟩ = ⟨1⟩ := by
  exact solcCalldataStaticLenCheckHuge (words := 3) hbig hsz (by norm_num)

theorem bytesStoreSetMappedByteSelector_size {I : ExecutionEnv}
    (hsel : selIs I ⟨#[0x13, 0x2f, 0xa3, 0x46]⟩) :
    4 ≤ I.calldata.size := by
  have hs := byteArray_size_eq_of_beq hsel
  have hleft : (⟨#[0x13, 0x2f, 0xa3, 0x46]⟩ : ByteArray).size = 4 := rfl
  rw [hleft, ByteArray.size_extract] at hs
  omega

theorem bytesStoreX_setMappedByteDecodeValid {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨319⟩ [bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hsz100 : 100 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hsize : I.calldata.size < UInt256.size)
    (hcanon : UInt256.land (bytesStoreSetMappedByteValueWord I) ⟨255⟩ =
      bytesStoreSetMappedByteValueWord I) :
    ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨772⟩
      [bytesStoreSetMappedByteValueWord I, bytesStoreSetMappedByteIndexWord I,
        bytesStoreSetMappedByteKeyWord I, ⟨301⟩, bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd319⟩ := hreach
  have hslt :
      UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨96⟩ = ⟨0⟩ :=
    bytesStoreSetMappedByteDecodeLenCheckOk hsz100 hhi hsize
  have rd2009 := evm_run rd319 with [
    jumpdest, push2 ⟨301⟩, push2 ⟨333⟩, calldatasize, push1 ⟨4⟩,
    push2 ⟨2009⟩, jump (by native_decide)]
  have rd2027 := evm_run rd2009 with [
    jumpdest, push0, push0, push0, push1 ⟨96⟩, dup5, dup7, sub, slt, iszero,
    push2 ⟨2027⟩, jumpiT (by rw [hslt]; decide) (by native_decide)]
  have rd1946 := evm_run rd2027 with [
    jumpdest, dup4, calldataload, swap3, pop, push1 ⟨32⟩, dup5, add, calldataload,
    swap2, pop, push2 ⟨2050⟩, push1 ⟨64⟩, dup6, add, push2 ⟨1946⟩,
    jump (by native_decide)]
  rw [show (⟨4⟩ : UInt256).toNat = 4 from by decide,
    show uInt256OfByteArray (I.calldata.readBytes 4 32) =
      bytesStoreSetMappedByteKeyWord I from rfl,
    show (⟨4⟩ + ⟨32⟩ : UInt256) = ⟨36⟩ from by native_decide,
    show (⟨4⟩ + ⟨64⟩ : UInt256) = ⟨68⟩ from by native_decide] at rd1946
  have rd1950 := evm_run rd1946 with [
    jumpdest, dup1, calldataload]
  rw [show (⟨68⟩ : UInt256).toNat = 68 from by decide,
    show uInt256OfByteArray (I.calldata.readBytes 68 32) =
      bytesStoreSetMappedByteValueWord I from rfl] at rd1950
  have rd2050 := evm_run rd1950 with [
    push1 ⟨255⟩, dup2, and, dup2, eq,
    push2 ⟨1962⟩,
    jumpiT (by rw [bytesStoreSetPacketByteUint8CanonEqGuard hcanon]; decide)
      (by native_decide),
    jumpdest, swap2, swap1, pop, jump (by native_decide)]
  exact ⟨_, _, evm_run rd2050 with [
    jumpdest, swap1, pop, swap3, pop, swap3, pop, swap3, jump (by native_decide),
    jumpdest, push2 ⟨772⟩, jump (by native_decide)]⟩

theorem bytesStoreX_setMappedByteDecodeShort {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨319⟩ [bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 100)
    (hsize : I.calldata.size < UInt256.size) :
    RDrev bytesStoreBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd319⟩ := hreach
  have hslt :
      UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨96⟩ = ⟨1⟩ :=
    bytesStoreSetMappedByteDecodeLenCheckShort hsz4 hshort hsize
  have rd2009 := evm_run rd319 with [
    jumpdest, push2 ⟨301⟩, push2 ⟨333⟩, calldatasize, push1 ⟨4⟩,
    push2 ⟨2009⟩, jump (by native_decide)]
  exact evm_run rd2009 with [
    jumpdest, push0, push0, push0, push1 ⟨96⟩, dup5, dup7, sub, slt, iszero,
    push2 ⟨2027⟩, jumpiNT (by rw [hslt]; decide),
    raw revertStub (by native_decide) (by native_decide) (by native_decide) (by evm_ov)]

theorem bytesStoreX_setMappedByteDecodeHuge {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨319⟩ [bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size) :
    RDrev bytesStoreBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd319⟩ := hreach
  have hslt :
      UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨96⟩ = ⟨1⟩ :=
    bytesStoreSetMappedByteDecodeLenCheckHuge hbig hsize
  have rd2009 := evm_run rd319 with [
    jumpdest, push2 ⟨301⟩, push2 ⟨333⟩, calldatasize, push1 ⟨4⟩,
    push2 ⟨2009⟩, jump (by native_decide)]
  exact evm_run rd2009 with [
    jumpdest, push0, push0, push0, push1 ⟨96⟩, dup5, dup7, sub, slt, iszero,
    push2 ⟨2027⟩, jumpiNT (by rw [hslt]; decide),
    raw revertStub (by native_decide) (by native_decide) (by native_decide) (by evm_ov)]

theorem bytesStoreX_setMappedByteDecodeNoncanonValue {cA gh bl σ σ₀ A I}
    {g : Sat256}
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨319⟩ [bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hsz100 : 100 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hsize : I.calldata.size < UInt256.size)
    (hnc : UInt256.land (bytesStoreSetMappedByteValueWord I) ⟨255⟩ ≠
      bytesStoreSetMappedByteValueWord I) :
    RDrev bytesStoreBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd319⟩ := hreach
  have hslt :
      UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨96⟩ = ⟨0⟩ :=
    bytesStoreSetMappedByteDecodeLenCheckOk hsz100 hhi hsize
  have rd2009 := evm_run rd319 with [
    jumpdest, push2 ⟨301⟩, push2 ⟨333⟩, calldatasize, push1 ⟨4⟩,
    push2 ⟨2009⟩, jump (by native_decide)]
  have rd2027 := evm_run rd2009 with [
    jumpdest, push0, push0, push0, push1 ⟨96⟩, dup5, dup7, sub, slt, iszero,
    push2 ⟨2027⟩, jumpiT (by rw [hslt]; decide) (by native_decide)]
  have rd1946 := evm_run rd2027 with [
    jumpdest, dup4, calldataload, swap3, pop, push1 ⟨32⟩, dup5, add, calldataload,
    swap2, pop, push2 ⟨2050⟩, push1 ⟨64⟩, dup6, add, push2 ⟨1946⟩,
    jump (by native_decide)]
  rw [show (⟨4⟩ : UInt256).toNat = 4 from by decide,
    show uInt256OfByteArray (I.calldata.readBytes 4 32) =
      bytesStoreSetMappedByteKeyWord I from rfl,
    show (⟨4⟩ + ⟨32⟩ : UInt256) = ⟨36⟩ from by native_decide,
    show (⟨4⟩ + ⟨64⟩ : UInt256) = ⟨68⟩ from by native_decide] at rd1946
  have rd1950 := evm_run rd1946 with [
    jumpdest, dup1, calldataload]
  rw [show (⟨68⟩ : UInt256).toNat = 68 from by decide,
    show uInt256OfByteArray (I.calldata.readBytes 68 32) =
      bytesStoreSetMappedByteValueWord I from rfl] at rd1950
  exact evm_run rd1950 with [
    push1 ⟨255⟩, dup2, and, dup2, eq,
    push2 ⟨1962⟩,
    jumpiNT (by rw [bytesStoreSetPacketByteUint8NoncanonEqGuard hnc]),
    raw revertStub (by native_decide) (by native_decide) (by native_decide) (by evm_ov)]

theorem bytesStoreX_setMappedByteReachLengthDecoder {cA gh bl σ σ₀ A I}
    {g : Sat256}
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨772⟩
      [bytesStoreSetMappedByteValueWord I, bytesStoreSetMappedByteIndexWord I,
        bytesStoreSetMappedByteKeyWord I, ⟨301⟩, bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2246⟩
      [bytesStoreSetMappedByteHeaderWord σ I, ⟨805⟩,
        bytesStoreSetMappedByteIndexWord I, bytesStoreSetMappedByteSlot I,
        UInt256.shiftLeft (bytesStoreSetMappedByteValueWord I) ⟨248⟩, ⟨0⟩,
        bytesStoreSetMappedByteValueWord I, bytesStoreSetMappedByteIndexWord I,
        bytesStoreSetMappedByteKeyWord I, ⟨301⟩, bytesStoreSelWord I]
      (twoWordHashMem (bytesStoreSetMappedByteKeyWord I) ⟨4⟩ solcFreePtrMem)
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd772⟩ := hreach
  have hslot := bytesStoreSetMappedByteSlotHash I
  have rd788 := evm_run rd772 with [
    jumpdest, push0, dup4, dup2,
    raw mstore 0 (wordAt0Mem (bytesStoreSetMappedByteKeyWord I) solcFreePtrMem)
      (UInt256.ofNat 3) (by native_decide)
      mem_cost
      (by rfl)
      (by native_decide) (by evm_ov),
    push1 ⟨4⟩, push1 ⟨32⟩,
    raw mstore 0
      (twoWordHashMem (bytesStoreSetMappedByteKeyWord I) ⟨4⟩ solcFreePtrMem)
      (UInt256.ofNat 3) (by native_decide)
      mem_cost
      (by rfl)
      (by native_decide) (by evm_ov),
    push1 ⟨64⟩, dup2,
    raw keccak256 0 (bytesStoreSetMappedByteSlot I) (UInt256.ofNat 3)
      (by native_decide) mem_cost hslot (by native_decide) (by evm_ov),
    dup1]
  obtain ⟨_, _, rd788₀⟩ := rd788.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd788'⟩ :
      ∃ k C, RD bytesStoreBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨788⟩
        [bytesStoreSetMappedByteHeaderWord σ I, bytesStoreSetMappedByteSlot I,
          ⟨0⟩, bytesStoreSetMappedByteValueWord I, bytesStoreSetMappedByteIndexWord I,
          bytesStoreSetMappedByteKeyWord I, ⟨301⟩, bytesStoreSelWord I]
        (twoWordHashMem (bytesStoreSetMappedByteKeyWord I) ⟨4⟩ solcFreePtrMem)
        (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by
      simpa [bytesStoreSetMappedByteHeaderWord, initState] using rd788₀⟩
  exact ⟨_, _, evm_run rd788' with [
    push1 ⟨248⟩, dup5, swap1, shl, swap2, swap1, dup6, swap1,
    push2 ⟨805⟩, swap1, push2 ⟨2246⟩, jump (by native_decide)]⟩

theorem bytesStoreX_setMappedByteOobAfterLength {cA gh bl σ σ₀ A I}
    {g : Sat256} {len : UInt256}
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨805⟩
      [len, bytesStoreSetMappedByteIndexWord I, bytesStoreSetMappedByteSlot I,
        UInt256.shiftLeft (bytesStoreSetMappedByteValueWord I) ⟨248⟩, ⟨0⟩,
        bytesStoreSetMappedByteValueWord I, bytesStoreSetMappedByteIndexWord I,
        bytesStoreSetMappedByteKeyWord I, ⟨301⟩, bytesStoreSelWord I]
      (twoWordHashMem (bytesStoreSetMappedByteKeyWord I) ⟨4⟩ solcFreePtrMem)
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hbound : ¬ (bytesStoreSetMappedByteIndexWord I).toNat < len.toNat) :
    RDrev bytesStoreBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd805⟩ := hreach
  have hlt : UInt256.lt (bytesStoreSetMappedByteIndexWord I) len = ⟨0⟩ :=
    ult_zero (by omega)
  have rd2579 := evm_run rd805 with [
    jumpdest, dup2, lt, push2 ⟨819⟩,
    jumpiNT (by simpa using hlt),
    push2 ⟨819⟩, push2 ⟨2579⟩, jump (by native_decide)]
  exact bytesStoreX_panic32Mem ⟨_, _, rd2579⟩
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem bytesStoreX_setMappedByteOobLong {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨772⟩
      [bytesStoreSetMappedByteValueWord I, bytesStoreSetMappedByteIndexWord I,
        bytesStoreSetMappedByteKeyWord I, ⟨301⟩, bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hflag : UInt256.land (bytesStoreSetMappedByteHeaderWord σ I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (bytesStoreSetMappedByteHeaderWord σ I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStoreSetMappedByteHeaderWord σ I) ⟨2⟩) ⟨32⟩) ≠
      ⟨0⟩)
    (hbound :
      ¬ (bytesStoreSetMappedByteIndexWord I).toNat <
        (UInt256.div (bytesStoreSetMappedByteHeaderWord σ I) ⟨2⟩).toNat) :
    RDrev bytesStoreBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hdec := bytesStoreX_setMappedByteReachLengthDecoder hreach
  have hlen := bytesStoreX_bytesLengthDecoderLongValidMem
    (A := A) (I := I) (g := g) hdec hflag hvalid (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  exact bytesStoreX_setMappedByteOobAfterLength (g := g) hlen hbound

theorem bytesStoreX_setMappedByteOobShort {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨772⟩
      [bytesStoreSetMappedByteValueWord I, bytesStoreSetMappedByteIndexWord I,
        bytesStoreSetMappedByteKeyWord I, ⟨301⟩, bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hflag : UInt256.land (bytesStoreSetMappedByteHeaderWord σ I) ⟨1⟩ = ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (bytesStoreSetMappedByteHeaderWord σ I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStoreSetMappedByteHeaderWord σ I) ⟨2⟩)
            ⟨127⟩) ⟨32⟩) ≠ ⟨0⟩)
    (hbound :
      ¬ (bytesStoreSetMappedByteIndexWord I).toNat <
        (UInt256.land (UInt256.div (bytesStoreSetMappedByteHeaderWord σ I) ⟨2⟩)
          ⟨127⟩).toNat) :
    RDrev bytesStoreBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hdec := bytesStoreX_setMappedByteReachLengthDecoder hreach
  have hlen := bytesStoreX_bytesLengthDecoderShortValidMem
    (A := A) (I := I) (g := g) hdec hflag hvalid (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  exact bytesStoreX_setMappedByteOobAfterLength (g := g) hlen hbound

theorem bytesStoreX_setMappedByteLongMalformed {cA gh bl σ σ₀ A I}
    {g : Sat256}
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨772⟩
      [bytesStoreSetMappedByteValueWord I, bytesStoreSetMappedByteIndexWord I,
        bytesStoreSetMappedByteKeyWord I, ⟨301⟩, bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hflag : UInt256.land (bytesStoreSetMappedByteHeaderWord σ I) ⟨1⟩ ≠ ⟨0⟩)
    (hbad : UInt256.sub (UInt256.land (bytesStoreSetMappedByteHeaderWord σ I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStoreSetMappedByteHeaderWord σ I) ⟨2⟩) ⟨32⟩) =
      ⟨0⟩) :
    RDrev bytesStoreBytecode g (initState cA gh bl σ σ₀ g A I) := by
  exact bytesStoreX_bytesLengthDecoderLongMalformedMem
    (bytesStoreX_setMappedByteReachLengthDecoder hreach) hflag hbad
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem bytesStoreX_setMappedByteShortMalformed {cA gh bl σ σ₀ A I}
    {g : Sat256}
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨772⟩
      [bytesStoreSetMappedByteValueWord I, bytesStoreSetMappedByteIndexWord I,
        bytesStoreSetMappedByteKeyWord I, ⟨301⟩, bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hflag : UInt256.land (bytesStoreSetMappedByteHeaderWord σ I) ⟨1⟩ = ⟨0⟩)
    (hbad : UInt256.sub (UInt256.land (bytesStoreSetMappedByteHeaderWord σ I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStoreSetMappedByteHeaderWord σ I) ⟨2⟩)
            ⟨127⟩) ⟨32⟩) = ⟨0⟩) :
    RDrev bytesStoreBytecode g (initState cA gh bl σ σ₀ g A I) := by
  exact bytesStoreX_bytesLengthDecoderShortMalformedMem
    (bytesStoreX_setMappedByteReachLengthDecoder hreach) hflag hbad
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem bytesStoreSetMappedByteResolveRevertsOfLength {evm : EVM.State}
    {I : ExecutionEnv} {len : Nat}
    (hlen : readStorageBytesLength? bytesStoreConfig evm
      (bytesStoreSetMappedByteHeaderRef I) = .ok len)
    (hbound : ¬ (bytesStoreSetMappedByteIndexWord I).toNat < len) :
    resolveStorageRef? bytesStoreConfig
      (bytesStoreSetMappedByteFrame I) evm
      (mappedByteRef (.var "key") (.var "byteIndex")) = .revert := by
  have hgetMapped :
      (bytesStoreSetMappedByteLocals I).get? "mapped" = none :=
    bytesStoreSetMappedByteLocals_get_mapped_none I
  have herInline :
      evalStorageRef bytesStoreConfig
        { contract := bytesStoreContract, locals := bytesStoreSetMappedByteLocals I }
        evm (mappedByteRef (.var "key") (.var "byteIndex")) = .revert := by
    simpa [bytesStoreSetMappedByteFrame] using
      (bytesStoreSetMappedByteEvalStorageRefRevertsOfLength
        (evm := evm) (I := I) (len := len) hlen hbound)
  exact resolveStorageRef?_revert_of_evalStorageRef_revert hgetMapped herInline

theorem bytesStoreSetMappedByteBodyBoundsRevertsOfLength {evm : EVM.State}
    {I : ExecutionEnv} {len : Nat}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hlen : readStorageBytesLength? bytesStoreConfig evm
      (bytesStoreSetMappedByteHeaderRef I) = .ok len)
    (hbound : ¬ (bytesStoreSetMappedByteIndexWord I).toNat < len) :
    ExecTransitionBody bytesStoreConfig bytesStoreContract evm
      (bytesStoreSetMappedByteLocals I) setMappedByteTransition.body .reverted := by
  let solm : Frame := bytesStoreSetMappedByteFrame I
  have hvalue :
      evalExpr? bytesStoreConfig solm evm (.var "value") =
        .ok (bytesStoreSetMappedByteValue I) := by
    exact evalExpr_var_of_get? (by
      simp [solm, bytesStoreSetMappedByteFrame, bytesStoreSetMappedByteValue,
        bytesStoreSetMappedByteLocals])
  have hassign :
      assignStorageRef? bytesStoreConfig solm evm .storage
        (mappedByteRef (.var "key") (.var "byteIndex"))
          (bytesStoreSetMappedByteValue I) = .revert := by
    exact assignStorageRef_storage_revert_of_resolve
      (bytesStoreSetMappedByteResolveRevertsOfLength (I := I) hlen hbound)
  exact ExecFuncBody.execBlockRevert <|
    ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consRevert (ExecStmt.assignStoreRevert hvalue hassign)

theorem bytesStoreSetMappedByteResolveRevertsOfLengthRead {evm : EVM.State}
    {I : ExecutionEnv}
    (hlen : readStorageBytesLength? bytesStoreConfig evm
      (bytesStoreSetMappedByteHeaderRef I) = .revert) :
    resolveStorageRef? bytesStoreConfig
      (bytesStoreSetMappedByteFrame I) evm
      (mappedByteRef (.var "key") (.var "byteIndex")) = .revert := by
  have hgetMapped :
      (bytesStoreSetMappedByteLocals I).get? "mapped" = none :=
    bytesStoreSetMappedByteLocals_get_mapped_none I
  have herInline :
      evalStorageRef bytesStoreConfig
        { contract := bytesStoreContract, locals := bytesStoreSetMappedByteLocals I }
        evm (mappedByteRef (.var "key") (.var "byteIndex")) = .revert := by
    simpa [bytesStoreSetMappedByteFrame] using
      (bytesStoreSetMappedByteEvalStorageRefRevertsOfLengthRead
        (evm := evm) (I := I) hlen)
  exact resolveStorageRef?_revert_of_evalStorageRef_revert hgetMapped herInline

theorem bytesStoreSetMappedByteBodyRevertsOfLengthRead {evm : EVM.State}
    {I : ExecutionEnv}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hlen : readStorageBytesLength? bytesStoreConfig evm
      (bytesStoreSetMappedByteHeaderRef I) = .revert) :
    ExecTransitionBody bytesStoreConfig bytesStoreContract evm
      (bytesStoreSetMappedByteLocals I) setMappedByteTransition.body .reverted := by
  let solm : Frame := bytesStoreSetMappedByteFrame I
  have hvalue :
      evalExpr? bytesStoreConfig solm evm (.var "value") =
        .ok (bytesStoreSetMappedByteValue I) := by
    exact evalExpr_var_of_get? (by
      simp [solm, bytesStoreSetMappedByteFrame, bytesStoreSetMappedByteValue,
        bytesStoreSetMappedByteLocals])
  have hassign :
      assignStorageRef? bytesStoreConfig solm evm .storage
        (mappedByteRef (.var "key") (.var "byteIndex"))
          (bytesStoreSetMappedByteValue I) = .revert := by
    exact assignStorageRef_storage_revert_of_resolve
      (bytesStoreSetMappedByteResolveRevertsOfLengthRead (I := I) hlen)
  exact ExecFuncBody.execBlockRevert <|
    ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consRevert (ExecStmt.assignStoreRevert hvalue hassign)

theorem bytesStoreSetMappedByteBodyReturnRevertsOfPostLengthRead
    {evm evm' : EVM.State} {I : ExecutionEnv}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hassign :
      assignStorageRef? bytesStoreConfig
        (bytesStoreSetMappedByteFrame I)
        evm .storage (mappedByteRef (.var "key") (.var "byteIndex"))
          (bytesStoreSetMappedByteValue I) =
          .ok (bytesStoreSetMappedByteFrame I, evm'))
    (hlenPost :
      readStorageBytesLength? bytesStoreConfig evm'
          (bytesStoreSetMappedByteHeaderRef I) = .revert) :
    ExecTransitionBody bytesStoreConfig bytesStoreContract evm
      (bytesStoreSetMappedByteLocals I) setMappedByteTransition.body .reverted := by
  have hret :
      evalExpr? bytesStoreConfig
        (bytesStoreSetMappedByteFrame I)
        evm' (.storage (mappedByteRef (.var "key") (.var "byteIndex"))) = .revert := by
    rw [evalExpr?]
    rw [bytesStoreSetMappedByteResolveRevertsOfLengthRead (I := I) hlenPost]
    rfl
  exact bytesStoreSetMappedByteBodyReturnReverts
    (evm := evm) (evm' := evm') (I := I) hwv hassign hret

theorem bytesStoreSetMappedByteLongBodyReturnRevertsOfPostLongMalformed
    {evm : EVM.State} {σ : AccountMap} {I : ExecutionEnv}
    {len postHeaderWord : UInt256}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hloadHeader : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (bytesStoreSetMappedByteSlot I) = bytesStoreSetMappedByteHeaderWord σ I)
    (hloadData : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (bytesStoreSetMappedByteLongDataSlot I) =
      bytesStoreSetMappedByteLongOldWord σ I)
    (hloadHeaderPost :
      Solm.EVM.storageLoad
          (Solm.EVM.storageStore evm evm.executionEnv.codeOwner
            (bytesStoreSetMappedByteLongDataSlot I)
            (bytesStoreSetMappedByteLongStoredWord σ I))
          evm.executionEnv.codeOwner (bytesStoreSetMappedByteSlot I) =
        postHeaderWord)
    (hcanon : (bytesStoreSetMappedByteValueWord I).toNat < EVM.twoPow 8)
    (hlen : len = UInt256.div (bytesStoreSetMappedByteHeaderWord σ I) ⟨2⟩)
    (hbound : (bytesStoreSetMappedByteIndexWord I).toNat < len.toNat)
    (hflag : UInt256.land (bytesStoreSetMappedByteHeaderWord σ I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (bytesStoreSetMappedByteHeaderWord σ I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStoreSetMappedByteHeaderWord σ I) ⟨2⟩) ⟨32⟩) ≠
          ⟨0⟩)
    (hflagPost : UInt256.land postHeaderWord ⟨1⟩ ≠ ⟨0⟩)
    (hbadPost : UInt256.sub (UInt256.land postHeaderWord ⟨1⟩)
        (UInt256.lt (UInt256.div postHeaderWord ⟨2⟩) ⟨32⟩) = ⟨0⟩) :
    ExecTransitionBody bytesStoreConfig bytesStoreContract evm
      (bytesStoreSetMappedByteLocals I) setMappedByteTransition.body .reverted := by
  let evm' := Solm.EVM.storageStore evm evm.executionEnv.codeOwner
    (bytesStoreSetMappedByteLongDataSlot I)
    (bytesStoreSetMappedByteLongStoredWord σ I)
  have hvalidLen :
      UInt256.sub (UInt256.land (bytesStoreSetMappedByteHeaderWord σ I) ⟨1⟩)
        (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩ := by
    simpa [hlen] using hvalid
  have hlenRead :
      readStorageBytesLength? bytesStoreConfig evm
          (bytesStoreSetMappedByteHeaderRef I) =
        .ok len.toNat := by
    exact bytesStoreReadLengthOfHeaderLoad
      (er := bytesStoreSetMappedByteHeaderRef I) (evm := evm)
      (baseSlot := bytesStoreSetMappedByteSlot I)
      (header := bytesStoreSetMappedByteHeaderWord σ I) (len := len.toNat)
      (bytesStoreSetMappedByteHeaderRef_length_slot evm I)
      hloadHeader
      (solidityDecodeBytesLengthHeader_long_valid hflag hlen hvalidLen)
  have hpacked : checkBytesPacked (bytesStoreSetMappedByteSlot I) evm = false :=
    checkBytesPacked_of_storageLoad_land_one_ne_zero hloadHeader hflag
  have hlayout :
      bytesStoreConfig.storage.layout (bytesStoreSetMappedByteRef I) evm =
        some (uint8Loc (bytesStoreSetMappedByteLongDataSlot I)
          ⟨31 - (bytesStoreSetMappedByteLongWordIndex I).toNat, by
            have hidx := bytesStoreSetMappedByteLongWordIndex_lt32 I
            omega⟩) :=
    bytesStoreSetMappedByteLayoutLong (evm := evm) (I := I) hpacked
  have hstore :
      (match bytesStoreConfig.storage.layout (bytesStoreSetMappedByteRef I) evm with
      | some loc => storageLocStore evm loc (bytesStoreSetMappedByteValue I)
      | none => none) = some evm' := by
    rw [hlayout]
    simpa [evm'] using
      bytesStoreSetMappedByteStorageLocStoreLong
        (evm := evm) (σ := σ) (I := I) hloadData hcanon
  have hassign :
      assignStorageRef? bytesStoreConfig
        (bytesStoreSetMappedByteFrame I)
        evm .storage (mappedByteRef (.var "key") (.var "byteIndex"))
          (bytesStoreSetMappedByteValue I) =
          .ok (bytesStoreSetMappedByteFrame I, evm') :=
    bytesStoreSetMappedByteAssignOfLength (evm := evm) (evm' := evm') (I := I)
      hlenRead hbound hstore
  have hloadHeaderPost' :
      Solm.EVM.storageLoad evm' evm'.executionEnv.codeOwner
          (bytesStoreSetMappedByteSlot I) = postHeaderWord := by
    simpa [evm', storageStore_executionEnv] using hloadHeaderPost
  have hlenPost :
      readStorageBytesLength? bytesStoreConfig evm'
          (bytesStoreSetMappedByteHeaderRef I) = .revert := by
    exact bytesStoreReadLengthRevertOfHeaderLoad
      (er := bytesStoreSetMappedByteHeaderRef I) (evm := evm')
      (baseSlot := bytesStoreSetMappedByteSlot I)
      (header := postHeaderWord)
      (bytesStoreSetMappedByteHeaderRef_length_slot evm' I)
      hloadHeaderPost'
      (by simp [solidityDecodeBytesLengthHeader, hflagPost, hbadPost])
  exact bytesStoreSetMappedByteBodyReturnRevertsOfPostLengthRead
    (evm := evm) (evm' := evm') (I := I) hwv hassign hlenPost

theorem bytesStoreSetMappedByteLongBodyReturnRevertsOfPostShortMalformed
    {evm : EVM.State} {σ : AccountMap} {I : ExecutionEnv}
    {len postHeaderWord : UInt256}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hloadHeader : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (bytesStoreSetMappedByteSlot I) = bytesStoreSetMappedByteHeaderWord σ I)
    (hloadData : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (bytesStoreSetMappedByteLongDataSlot I) =
      bytesStoreSetMappedByteLongOldWord σ I)
    (hloadHeaderPost :
      Solm.EVM.storageLoad
          (Solm.EVM.storageStore evm evm.executionEnv.codeOwner
            (bytesStoreSetMappedByteLongDataSlot I)
            (bytesStoreSetMappedByteLongStoredWord σ I))
          evm.executionEnv.codeOwner (bytesStoreSetMappedByteSlot I) =
        postHeaderWord)
    (hcanon : (bytesStoreSetMappedByteValueWord I).toNat < EVM.twoPow 8)
    (hlen : len = UInt256.div (bytesStoreSetMappedByteHeaderWord σ I) ⟨2⟩)
    (hbound : (bytesStoreSetMappedByteIndexWord I).toNat < len.toNat)
    (hflag : UInt256.land (bytesStoreSetMappedByteHeaderWord σ I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (bytesStoreSetMappedByteHeaderWord σ I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStoreSetMappedByteHeaderWord σ I) ⟨2⟩) ⟨32⟩) ≠
          ⟨0⟩)
    (hflagPost : UInt256.land postHeaderWord ⟨1⟩ = ⟨0⟩)
    (hbadPost : UInt256.sub (UInt256.land postHeaderWord ⟨1⟩)
        (UInt256.lt (UInt256.land (UInt256.div postHeaderWord ⟨2⟩) ⟨127⟩) ⟨32⟩) =
          ⟨0⟩) :
    ExecTransitionBody bytesStoreConfig bytesStoreContract evm
      (bytesStoreSetMappedByteLocals I) setMappedByteTransition.body .reverted := by
  let evm' := Solm.EVM.storageStore evm evm.executionEnv.codeOwner
    (bytesStoreSetMappedByteLongDataSlot I)
    (bytesStoreSetMappedByteLongStoredWord σ I)
  have hvalidLen :
      UInt256.sub (UInt256.land (bytesStoreSetMappedByteHeaderWord σ I) ⟨1⟩)
        (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩ := by
    simpa [hlen] using hvalid
  have hlenRead :
      readStorageBytesLength? bytesStoreConfig evm
          (bytesStoreSetMappedByteHeaderRef I) =
        .ok len.toNat := by
    exact bytesStoreReadLengthOfHeaderLoad
      (er := bytesStoreSetMappedByteHeaderRef I) (evm := evm)
      (baseSlot := bytesStoreSetMappedByteSlot I)
      (header := bytesStoreSetMappedByteHeaderWord σ I) (len := len.toNat)
      (bytesStoreSetMappedByteHeaderRef_length_slot evm I)
      hloadHeader
      (solidityDecodeBytesLengthHeader_long_valid hflag hlen hvalidLen)
  have hpacked : checkBytesPacked (bytesStoreSetMappedByteSlot I) evm = false :=
    checkBytesPacked_of_storageLoad_land_one_ne_zero hloadHeader hflag
  have hlayout :
      bytesStoreConfig.storage.layout (bytesStoreSetMappedByteRef I) evm =
        some (uint8Loc (bytesStoreSetMappedByteLongDataSlot I)
          ⟨31 - (bytesStoreSetMappedByteLongWordIndex I).toNat, by
            have hidx := bytesStoreSetMappedByteLongWordIndex_lt32 I
            omega⟩) :=
    bytesStoreSetMappedByteLayoutLong (evm := evm) (I := I) hpacked
  have hstore :
      (match bytesStoreConfig.storage.layout (bytesStoreSetMappedByteRef I) evm with
      | some loc => storageLocStore evm loc (bytesStoreSetMappedByteValue I)
      | none => none) = some evm' := by
    rw [hlayout]
    simpa [evm'] using
      bytesStoreSetMappedByteStorageLocStoreLong
        (evm := evm) (σ := σ) (I := I) hloadData hcanon
  have hassign :
      assignStorageRef? bytesStoreConfig
        (bytesStoreSetMappedByteFrame I)
        evm .storage (mappedByteRef (.var "key") (.var "byteIndex"))
          (bytesStoreSetMappedByteValue I) =
          .ok (bytesStoreSetMappedByteFrame I, evm') :=
    bytesStoreSetMappedByteAssignOfLength (evm := evm) (evm' := evm') (I := I)
      hlenRead hbound hstore
  have hloadHeaderPost' :
      Solm.EVM.storageLoad evm' evm'.executionEnv.codeOwner
          (bytesStoreSetMappedByteSlot I) = postHeaderWord := by
    simpa [evm', storageStore_executionEnv] using hloadHeaderPost
  have hlenPost :
      readStorageBytesLength? bytesStoreConfig evm'
          (bytesStoreSetMappedByteHeaderRef I) = .revert := by
    have hbadPost0 :
        UInt256.sub ⟨0⟩
          (UInt256.lt (UInt256.land (UInt256.div postHeaderWord ⟨2⟩) ⟨127⟩) ⟨32⟩) =
            ⟨0⟩ := by
      simpa [hflagPost] using hbadPost
    exact bytesStoreReadLengthRevertOfHeaderLoad
      (er := bytesStoreSetMappedByteHeaderRef I) (evm := evm')
      (baseSlot := bytesStoreSetMappedByteSlot I)
      (header := postHeaderWord)
      (bytesStoreSetMappedByteHeaderRef_length_slot evm' I)
      hloadHeaderPost'
      (by simp [solidityDecodeBytesLengthHeader, hflagPost, hbadPost0])
  exact bytesStoreSetMappedByteBodyReturnRevertsOfPostLengthRead
    (evm := evm) (evm' := evm') (I := I) hwv hassign hlenPost

theorem bytesStoreSetMappedByteLongBodyReturnRevertsOfPostLongLength
    {evm : EVM.State} {σ : AccountMap} {I : ExecutionEnv}
    {len lenPost postHeaderWord : UInt256}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hloadHeader : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (bytesStoreSetMappedByteSlot I) = bytesStoreSetMappedByteHeaderWord σ I)
    (hloadData : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (bytesStoreSetMappedByteLongDataSlot I) =
      bytesStoreSetMappedByteLongOldWord σ I)
    (hloadHeaderPost :
      Solm.EVM.storageLoad
          (Solm.EVM.storageStore evm evm.executionEnv.codeOwner
            (bytesStoreSetMappedByteLongDataSlot I)
            (bytesStoreSetMappedByteLongStoredWord σ I))
          evm.executionEnv.codeOwner (bytesStoreSetMappedByteSlot I) =
        postHeaderWord)
    (hcanon : (bytesStoreSetMappedByteValueWord I).toNat < EVM.twoPow 8)
    (hlen : len = UInt256.div (bytesStoreSetMappedByteHeaderWord σ I) ⟨2⟩)
    (hlenPost : lenPost = UInt256.div postHeaderWord ⟨2⟩)
    (hbound : (bytesStoreSetMappedByteIndexWord I).toNat < len.toNat)
    (hboundPost : ¬ (bytesStoreSetMappedByteIndexWord I).toNat < lenPost.toNat)
    (hflag : UInt256.land (bytesStoreSetMappedByteHeaderWord σ I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (bytesStoreSetMappedByteHeaderWord σ I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStoreSetMappedByteHeaderWord σ I) ⟨2⟩) ⟨32⟩) ≠
          ⟨0⟩)
    (hflagPost : UInt256.land postHeaderWord ⟨1⟩ ≠ ⟨0⟩)
    (hvalidPost : UInt256.sub (UInt256.land postHeaderWord ⟨1⟩)
        (UInt256.lt (UInt256.div postHeaderWord ⟨2⟩) ⟨32⟩) ≠ ⟨0⟩) :
    ExecTransitionBody bytesStoreConfig bytesStoreContract evm
      (bytesStoreSetMappedByteLocals I) setMappedByteTransition.body .reverted := by
  let evm' := Solm.EVM.storageStore evm evm.executionEnv.codeOwner
    (bytesStoreSetMappedByteLongDataSlot I)
    (bytesStoreSetMappedByteLongStoredWord σ I)
  have hvalidLen :
      UInt256.sub (UInt256.land (bytesStoreSetMappedByteHeaderWord σ I) ⟨1⟩)
        (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩ := by
    simpa [hlen] using hvalid
  have hlenRead :
      readStorageBytesLength? bytesStoreConfig evm
          (bytesStoreSetMappedByteHeaderRef I) =
        .ok len.toNat := by
    exact bytesStoreReadLengthOfHeaderLoad
      (er := bytesStoreSetMappedByteHeaderRef I) (evm := evm)
      (baseSlot := bytesStoreSetMappedByteSlot I)
      (header := bytesStoreSetMappedByteHeaderWord σ I) (len := len.toNat)
      (bytesStoreSetMappedByteHeaderRef_length_slot evm I)
      hloadHeader
      (solidityDecodeBytesLengthHeader_long_valid hflag hlen hvalidLen)
  have hpacked : checkBytesPacked (bytesStoreSetMappedByteSlot I) evm = false :=
    checkBytesPacked_of_storageLoad_land_one_ne_zero hloadHeader hflag
  have hlayout :
      bytesStoreConfig.storage.layout (bytesStoreSetMappedByteRef I) evm =
        some (uint8Loc (bytesStoreSetMappedByteLongDataSlot I)
          ⟨31 - (bytesStoreSetMappedByteLongWordIndex I).toNat, by
            have hidx := bytesStoreSetMappedByteLongWordIndex_lt32 I
            omega⟩) :=
    bytesStoreSetMappedByteLayoutLong (evm := evm) (I := I) hpacked
  have hstore :
      (match bytesStoreConfig.storage.layout (bytesStoreSetMappedByteRef I) evm with
      | some loc => storageLocStore evm loc (bytesStoreSetMappedByteValue I)
      | none => none) = some evm' := by
    rw [hlayout]
    simpa [evm'] using
      bytesStoreSetMappedByteStorageLocStoreLong
        (evm := evm) (σ := σ) (I := I) hloadData hcanon
  have hassign :
      assignStorageRef? bytesStoreConfig
        (bytesStoreSetMappedByteFrame I)
        evm .storage (mappedByteRef (.var "key") (.var "byteIndex"))
          (bytesStoreSetMappedByteValue I) =
          .ok (bytesStoreSetMappedByteFrame I, evm') :=
    bytesStoreSetMappedByteAssignOfLength (evm := evm) (evm' := evm') (I := I)
      hlenRead hbound hstore
  have hloadHeaderPost' :
      Solm.EVM.storageLoad evm' evm'.executionEnv.codeOwner
          (bytesStoreSetMappedByteSlot I) = postHeaderWord := by
    simpa [evm', storageStore_executionEnv] using hloadHeaderPost
  have hlenPostRead :
      readStorageBytesLength? bytesStoreConfig evm'
          (bytesStoreSetMappedByteHeaderRef I) = .ok lenPost.toNat := by
    have hvalidLenPost :
        UInt256.sub (UInt256.land postHeaderWord ⟨1⟩)
          (UInt256.lt lenPost ⟨32⟩) ≠ ⟨0⟩ := by
      simpa [hlenPost] using hvalidPost
    exact bytesStoreReadLengthOfHeaderLoad
      (er := bytesStoreSetMappedByteHeaderRef I) (evm := evm')
      (baseSlot := bytesStoreSetMappedByteSlot I)
      (header := postHeaderWord) (len := lenPost.toNat)
      (bytesStoreSetMappedByteHeaderRef_length_slot evm' I)
      hloadHeaderPost'
      (solidityDecodeBytesLengthHeader_long_valid hflagPost hlenPost hvalidLenPost)
  have hret :
      evalExpr? bytesStoreConfig
        (bytesStoreSetMappedByteFrame I)
        evm' (.storage (mappedByteRef (.var "key") (.var "byteIndex"))) = .revert := by
    rw [evalExpr?]
    rw [bytesStoreSetMappedByteResolveRevertsOfLength
      (evm := evm') (I := I) hlenPostRead hboundPost]
    rfl
  exact bytesStoreSetMappedByteBodyReturnReverts
    (evm := evm) (evm' := evm') (I := I) hwv hassign hret

theorem bytesStoreSetMappedByteLongBodyReturnRevertsOfPostShortLength
    {evm : EVM.State} {σ : AccountMap} {I : ExecutionEnv}
    {len lenPost postHeaderWord : UInt256}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hloadHeader : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (bytesStoreSetMappedByteSlot I) = bytesStoreSetMappedByteHeaderWord σ I)
    (hloadData : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (bytesStoreSetMappedByteLongDataSlot I) =
      bytesStoreSetMappedByteLongOldWord σ I)
    (hloadHeaderPost :
      Solm.EVM.storageLoad
          (Solm.EVM.storageStore evm evm.executionEnv.codeOwner
            (bytesStoreSetMappedByteLongDataSlot I)
            (bytesStoreSetMappedByteLongStoredWord σ I))
          evm.executionEnv.codeOwner (bytesStoreSetMappedByteSlot I) =
        postHeaderWord)
    (hcanon : (bytesStoreSetMappedByteValueWord I).toNat < EVM.twoPow 8)
    (hlen : len = UInt256.div (bytesStoreSetMappedByteHeaderWord σ I) ⟨2⟩)
    (hlenPost : lenPost = UInt256.land (UInt256.div postHeaderWord ⟨2⟩) ⟨127⟩)
    (hbound : (bytesStoreSetMappedByteIndexWord I).toNat < len.toNat)
    (hboundPost : ¬ (bytesStoreSetMappedByteIndexWord I).toNat < lenPost.toNat)
    (hflag : UInt256.land (bytesStoreSetMappedByteHeaderWord σ I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (bytesStoreSetMappedByteHeaderWord σ I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStoreSetMappedByteHeaderWord σ I) ⟨2⟩) ⟨32⟩) ≠
          ⟨0⟩)
    (hflagPost : UInt256.land postHeaderWord ⟨1⟩ = ⟨0⟩)
    (hvalidPost : UInt256.sub (UInt256.land postHeaderWord ⟨1⟩)
        (UInt256.lt (UInt256.land (UInt256.div postHeaderWord ⟨2⟩) ⟨127⟩) ⟨32⟩) ≠
          ⟨0⟩) :
    ExecTransitionBody bytesStoreConfig bytesStoreContract evm
      (bytesStoreSetMappedByteLocals I) setMappedByteTransition.body .reverted := by
  let evm' := Solm.EVM.storageStore evm evm.executionEnv.codeOwner
    (bytesStoreSetMappedByteLongDataSlot I)
    (bytesStoreSetMappedByteLongStoredWord σ I)
  have hvalidLen :
      UInt256.sub (UInt256.land (bytesStoreSetMappedByteHeaderWord σ I) ⟨1⟩)
        (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩ := by
    simpa [hlen] using hvalid
  have hlenRead :
      readStorageBytesLength? bytesStoreConfig evm
          (bytesStoreSetMappedByteHeaderRef I) =
        .ok len.toNat := by
    exact bytesStoreReadLengthOfHeaderLoad
      (er := bytesStoreSetMappedByteHeaderRef I) (evm := evm)
      (baseSlot := bytesStoreSetMappedByteSlot I)
      (header := bytesStoreSetMappedByteHeaderWord σ I) (len := len.toNat)
      (bytesStoreSetMappedByteHeaderRef_length_slot evm I)
      hloadHeader
      (solidityDecodeBytesLengthHeader_long_valid hflag hlen hvalidLen)
  have hpacked : checkBytesPacked (bytesStoreSetMappedByteSlot I) evm = false :=
    checkBytesPacked_of_storageLoad_land_one_ne_zero hloadHeader hflag
  have hlayout :
      bytesStoreConfig.storage.layout (bytesStoreSetMappedByteRef I) evm =
        some (uint8Loc (bytesStoreSetMappedByteLongDataSlot I)
          ⟨31 - (bytesStoreSetMappedByteLongWordIndex I).toNat, by
            have hidx := bytesStoreSetMappedByteLongWordIndex_lt32 I
            omega⟩) :=
    bytesStoreSetMappedByteLayoutLong (evm := evm) (I := I) hpacked
  have hstore :
      (match bytesStoreConfig.storage.layout (bytesStoreSetMappedByteRef I) evm with
      | some loc => storageLocStore evm loc (bytesStoreSetMappedByteValue I)
      | none => none) = some evm' := by
    rw [hlayout]
    simpa [evm'] using
      bytesStoreSetMappedByteStorageLocStoreLong
        (evm := evm) (σ := σ) (I := I) hloadData hcanon
  have hassign :
      assignStorageRef? bytesStoreConfig
        (bytesStoreSetMappedByteFrame I)
        evm .storage (mappedByteRef (.var "key") (.var "byteIndex"))
          (bytesStoreSetMappedByteValue I) =
          .ok (bytesStoreSetMappedByteFrame I, evm') :=
    bytesStoreSetMappedByteAssignOfLength (evm := evm) (evm' := evm') (I := I)
      hlenRead hbound hstore
  have hloadHeaderPost' :
      Solm.EVM.storageLoad evm' evm'.executionEnv.codeOwner
          (bytesStoreSetMappedByteSlot I) = postHeaderWord := by
    simpa [evm', storageStore_executionEnv] using hloadHeaderPost
  have hlenPostRead :
      readStorageBytesLength? bytesStoreConfig evm'
          (bytesStoreSetMappedByteHeaderRef I) = .ok lenPost.toNat := by
    have hvalidLenPost :
        UInt256.sub ⟨0⟩ (UInt256.lt lenPost ⟨32⟩) ≠ ⟨0⟩ := by
      simpa [hlenPost, hflagPost] using hvalidPost
    exact bytesStoreReadLengthOfHeaderLoad
      (er := bytesStoreSetMappedByteHeaderRef I) (evm := evm')
      (baseSlot := bytesStoreSetMappedByteSlot I)
      (header := postHeaderWord) (len := lenPost.toNat)
      (bytesStoreSetMappedByteHeaderRef_length_slot evm' I)
      hloadHeaderPost'
      (solidityDecodeBytesLengthHeader_short_valid hflagPost hlenPost
        (by simpa [hlenPost] using hvalidPost))
  have hret :
      evalExpr? bytesStoreConfig
        (bytesStoreSetMappedByteFrame I)
        evm' (.storage (mappedByteRef (.var "key") (.var "byteIndex"))) = .revert := by
    rw [evalExpr?]
    rw [bytesStoreSetMappedByteResolveRevertsOfLength
      (evm := evm') (I := I) hlenPostRead hboundPost]
    rfl
  exact bytesStoreSetMappedByteBodyReturnReverts
    (evm := evm) (evm' := evm') (I := I) hwv hassign hret

theorem bytesStoreDecode_setMappedByte {I : ExecutionEnv}
    (hsz100 : 100 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (bytesStoreSetMappedByteValueWord I).toNat < EVM.twoPow 8) :
    decodeCalldata (setMappedByteTransition.params.map Param.name)
      (transitionSignature setMappedByteTransition).paramTypes I.calldata =
        some (bytesStoreSetMappedByteLocals I) := by
  show decodeCalldata ["key", "byteIndex", "value"] [uint256, uint256, uint8]
      I.calldata = some (bytesStoreSetMappedByteLocals I)
  simpa [uint256, uint8, uint8Int, abiUInt256, abiUInt8,
    bytesStoreSetMappedByteLocals, bytesStoreSetMappedByteKeyWord,
    bytesStoreSetMappedByteIndexWord, bytesStoreSetMappedByteValueWord] using
    decodeCalldata_uint256_uint256_uint8_ok (cd := I.calldata) (x := "key")
      (y := "byteIndex") (z := "value") hsz100 hhi hcanon

theorem bytesStoreDecode_setMappedByte_none_noncanon_value {I : ExecutionEnv}
    (hsz100 : 100 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hnc : ¬ (bytesStoreSetMappedByteValueWord I).toNat < EVM.twoPow 8) :
    decodeCalldata (setMappedByteTransition.params.map Param.name)
      (transitionSignature setMappedByteTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["key", "byteIndex", "value"] [uint256, uint256, uint8]
      I.calldata = none
  simpa [uint256, uint8, uint8Int, abiUInt256, abiUInt8,
    bytesStoreSetMappedByteValueWord] using
    decodeCalldata_uint256_uint256_uint8_none_noncanon2 (cd := I.calldata)
      (x := "key") (y := "byteIndex") (z := "value") hsz100 hhi hnc

theorem bytesStoreDecode_setMappedByte_none_short {I : ExecutionEnv}
    (hshort : I.calldata.size < 100) :
    decodeCalldata (setMappedByteTransition.params.map Param.name)
      (transitionSignature setMappedByteTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["key", "byteIndex", "value"] [uint256, uint256, uint8]
      I.calldata = none
  simpa [uint256, uint8, uint8Int, abiUInt256, abiUInt8] using
    decodeCalldata_uint256_uint256_uint8_none_short (cd := I.calldata)
      (x := "key") (y := "byteIndex") (z := "value") hshort

theorem bytesStoreDecode_setMappedByte_none_huge {I : ExecutionEnv}
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size) :
    decodeCalldata (setMappedByteTransition.params.map Param.name)
      (transitionSignature setMappedByteTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["key", "byteIndex", "value"] [uint256, uint256, uint8]
      I.calldata = none
  simpa [uint256, uint8, uint8Int, abiUInt256, abiUInt8] using
    decodeCalldata_uint256_uint256_uint8_none_huge (cd := I.calldata)
      (x := "key") (y := "byteIndex") (z := "value") hbig

theorem bytesStoreSetMappedByteDecodeShortRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x13, 0x2f, 0xa3, 0x46]⟩)
    (_hAccounts : accountMapEquiv σ_evm σ_solm)
    (hshort : I.calldata.size < 100) :
    runtimeEquivalenceFor bytesStoreConfig bytesStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsz := bytesStoreSetMappedByteSelector_size hsel
  have hreach := bytesStoreReachSetMappedByte (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz hsize hsel
  have hreachPc : ∃ k C, RD bytesStoreBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨319⟩
      [bytesStoreSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ_evm) k C := by
    simpa [bytesStoreSetMappedByteEntryPc] using hreach
  have hd := bytesStoreDispatch_setMappedByte (cd := I.calldata)
    (by simpa [selIs] using hsel)
  have hdec := bytesStoreDecode_setMappedByte_none_short (I := I) hshort
  exact (bytesStoreX_setMappedByteDecodeShort
      (g := Sat256.ofUInt256 g) hreachPc hsz hshort hsize)
    |>.reEquivDecodingFailed hcode hd hdec

theorem bytesStoreSetMappedByteDecodeHugeRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x13, 0x2f, 0xa3, 0x46]⟩)
    (_hAccounts : accountMapEquiv σ_evm σ_solm)
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size) :
    runtimeEquivalenceFor bytesStoreConfig bytesStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsz := bytesStoreSetMappedByteSelector_size hsel
  have hreach := bytesStoreReachSetMappedByte (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz hsize hsel
  have hreachPc : ∃ k C, RD bytesStoreBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨319⟩
      [bytesStoreSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ_evm) k C := by
    simpa [bytesStoreSetMappedByteEntryPc] using hreach
  have hd := bytesStoreDispatch_setMappedByte (cd := I.calldata)
    (by simpa [selIs] using hsel)
  have hdec := bytesStoreDecode_setMappedByte_none_huge (I := I) hbig
  exact (bytesStoreX_setMappedByteDecodeHuge
      (g := Sat256.ofUInt256 g) hreachPc hbig hsize)
    |>.reEquivDecodingFailed hcode hd hdec

theorem bytesStoreSetMappedByteDecodeNoncanonValueRuntime
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = bytesStoreBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x13, 0x2f, 0xa3, 0x46]⟩)
    (_hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsz100 : 100 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hnc : ¬ (bytesStoreSetMappedByteValueWord I).toNat < EVM.twoPow 8) :
    runtimeEquivalenceFor bytesStoreConfig bytesStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsz := bytesStoreSetMappedByteSelector_size hsel
  have hreach := bytesStoreReachSetMappedByte (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz hsize hsel
  have hreachPc : ∃ k C, RD bytesStoreBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨319⟩
      [bytesStoreSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ_evm) k C := by
    simpa [bytesStoreSetMappedByteEntryPc] using hreach
  have hd := bytesStoreDispatch_setMappedByte (cd := I.calldata)
    (by simpa [selIs] using hsel)
  have hdec := bytesStoreDecode_setMappedByte_none_noncanon_value
    (I := I) hsz100 hhi hnc
  exact (bytesStoreX_setMappedByteDecodeNoncanonValue
      (g := Sat256.ofUInt256 g) hreachPc hsz100 hhi hsize
      (bytesStoreSetPacketByteLand255_ne_self_of_not_uint8 hnc))
    |>.reEquivDecodingFailed hcode hd hdec

theorem bytesStoreSetMappedByteOobLongRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x13, 0x2f, 0xa3, 0x46]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsz100 : 100 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (bytesStoreSetMappedByteValueWord I).toNat < EVM.twoPow 8)
    (hflag : UInt256.land (bytesStoreSetMappedByteHeaderWord σ_evm I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (bytesStoreSetMappedByteHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStoreSetMappedByteHeaderWord σ_evm I) ⟨2⟩) ⟨32⟩) ≠
      ⟨0⟩)
    (hbound :
      ¬ (bytesStoreSetMappedByteIndexWord I).toNat <
        (UInt256.div (bytesStoreSetMappedByteHeaderWord σ_evm I) ⟨2⟩).toNat) :
    runtimeEquivalenceFor bytesStoreConfig bytesStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsz := bytesStoreSetMappedByteSelector_size hsel
  have hreach := bytesStoreReachSetMappedByte (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz hsize hsel
  have hreachPc : ∃ k C, RD bytesStoreBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨319⟩
      [bytesStoreSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ_evm) k C := by
    simpa [bytesStoreSetMappedByteEntryPc] using hreach
  have hreachBody := bytesStoreX_setMappedByteDecodeValid
    (g := Sat256.ofUInt256 g) hreachPc hsz100 hhi hsize
    (bytesStoreSetPacketByteLand255_eq_self_of_uint8 hcanon)
  have hd := bytesStoreDispatch_setMappedByte (cd := I.calldata)
    (by simpa [selIs] using hsel)
  have hdec := bytesStoreDecode_setMappedByte (I := I) hsz100 hhi hcanon
  have hload :
      Solm.EVM.storageLoad
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        I.codeOwner (bytesStoreSetMappedByteSlot I) =
          bytesStoreSetMappedByteHeaderWord σ_evm I := by
    simpa [initState] using
      bytesStoreStorageLoadSetMappedByteHeader_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hloadMapped :
      Solm.EVM.storageLoad
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        I.codeOwner
          (mappedValueSlot
            (.int (Int.ofNat (bytesStoreSetMappedByteKeyWord I).toNat))) =
          bytesStoreSetMappedByteHeaderWord σ_evm I := by
    simpa [bytesStoreSetMappedByteSlot, bytesStoreSetMappedSlotOf] using hload
  have hloadMapped' :
      Solm.EVM.storageLoad
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        I.codeOwner
          (mappedValueSlot
            (.int ((bytesStoreSetMappedByteKeyWord I).toNat : Int))) =
          bytesStoreSetMappedByteHeaderWord σ_evm I := by
    simpa using hloadMapped
  have hcodeOwner :
      (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner =
        I.codeOwner := by
    rfl
  have hlen :
      readStorageBytesLength? bytesStoreConfig
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (bytesStoreSetMappedByteHeaderRef I) =
          .ok (UInt256.div (bytesStoreSetMappedByteHeaderWord σ_evm I) ⟨2⟩).toNat := by
    exact bytesStoreReadLengthOfHeaderLoad
      (er := bytesStoreSetMappedByteHeaderRef I)
      (evm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
      (baseSlot := bytesStoreSetMappedByteSlot I)
      (header := bytesStoreSetMappedByteHeaderWord σ_evm I)
      (len := (UInt256.div (bytesStoreSetMappedByteHeaderWord σ_evm I) ⟨2⟩).toNat)
      (bytesStoreSetMappedByteHeaderRef_length_slot
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I)
      hload
      (solidityDecodeBytesLengthHeader_long_valid hflag rfl hvalid)
  have hbody :
      ExecTransitionBody bytesStoreConfig bytesStoreContract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (bytesStoreSetMappedByteLocals I) setMappedByteTransition.body .reverted := by
    exact bytesStoreSetMappedByteBodyBoundsRevertsOfLength
      (by simp only [initState]; exact hwv) hlen hbound
  exact (bytesStoreX_setMappedByteOobLong
      (g := Sat256.ofUInt256 g) hreachBody hflag hvalid hbound)
    |>.reEquivExecutionRevert hcode hd hdec hbody

theorem bytesStoreSetMappedByteOobShortRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x13, 0x2f, 0xa3, 0x46]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsz100 : 100 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (bytesStoreSetMappedByteValueWord I).toNat < EVM.twoPow 8)
    (hflag : UInt256.land (bytesStoreSetMappedByteHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (bytesStoreSetMappedByteHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStoreSetMappedByteHeaderWord σ_evm I) ⟨2⟩)
            ⟨127⟩) ⟨32⟩) ≠ ⟨0⟩)
    (hbound :
      ¬ (bytesStoreSetMappedByteIndexWord I).toNat <
        (UInt256.land (UInt256.div (bytesStoreSetMappedByteHeaderWord σ_evm I) ⟨2⟩)
          ⟨127⟩).toNat) :
    runtimeEquivalenceFor bytesStoreConfig bytesStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsz := bytesStoreSetMappedByteSelector_size hsel
  have hreach := bytesStoreReachSetMappedByte (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz hsize hsel
  have hreachPc : ∃ k C, RD bytesStoreBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨319⟩
      [bytesStoreSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ_evm) k C := by
    simpa [bytesStoreSetMappedByteEntryPc] using hreach
  have hreachBody := bytesStoreX_setMappedByteDecodeValid
    (g := Sat256.ofUInt256 g) hreachPc hsz100 hhi hsize
    (bytesStoreSetPacketByteLand255_eq_self_of_uint8 hcanon)
  have hd := bytesStoreDispatch_setMappedByte (cd := I.calldata)
    (by simpa [selIs] using hsel)
  have hdec := bytesStoreDecode_setMappedByte (I := I) hsz100 hhi hcanon
  have hload :
      Solm.EVM.storageLoad
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        I.codeOwner (bytesStoreSetMappedByteSlot I) =
          bytesStoreSetMappedByteHeaderWord σ_evm I := by
    simpa [initState] using
      bytesStoreStorageLoadSetMappedByteHeader_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hloadMapped :
      Solm.EVM.storageLoad
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        I.codeOwner
          (mappedValueSlot
            (.int (Int.ofNat (bytesStoreSetMappedByteKeyWord I).toNat))) =
          bytesStoreSetMappedByteHeaderWord σ_evm I := by
    simpa [bytesStoreSetMappedByteSlot, bytesStoreSetMappedSlotOf] using hload
  have hloadMapped' :
      Solm.EVM.storageLoad
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        I.codeOwner
          (mappedValueSlot
            (.int ((bytesStoreSetMappedByteKeyWord I).toNat : Int))) =
          bytesStoreSetMappedByteHeaderWord σ_evm I := by
    simpa using hloadMapped
  have hcodeOwner :
      (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner =
        I.codeOwner := by
    rfl
  have hvalid0 :
      UInt256.sub ⟨0⟩
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStoreSetMappedByteHeaderWord σ_evm I) ⟨2⟩)
            ⟨127⟩) ⟨32⟩) ≠ ⟨0⟩ := by
    simpa [hflag] using hvalid
  have hlen :
      readStorageBytesLength? bytesStoreConfig
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (bytesStoreSetMappedByteHeaderRef I) =
          .ok (UInt256.land
            (UInt256.div (bytesStoreSetMappedByteHeaderWord σ_evm I) ⟨2⟩)
            ⟨127⟩).toNat := by
    exact bytesStoreReadLengthOfHeaderLoad
      (er := bytesStoreSetMappedByteHeaderRef I)
      (evm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
      (baseSlot := bytesStoreSetMappedByteSlot I)
      (header := bytesStoreSetMappedByteHeaderWord σ_evm I)
      (len := (UInt256.land
        (UInt256.div (bytesStoreSetMappedByteHeaderWord σ_evm I) ⟨2⟩)
        ⟨127⟩).toNat)
      (bytesStoreSetMappedByteHeaderRef_length_slot
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I)
      hload
      (solidityDecodeBytesLengthHeader_short_valid hflag rfl hvalid)
  have hbody :
      ExecTransitionBody bytesStoreConfig bytesStoreContract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (bytesStoreSetMappedByteLocals I) setMappedByteTransition.body .reverted := by
    exact bytesStoreSetMappedByteBodyBoundsRevertsOfLength
      (by simp only [initState]; exact hwv) hlen hbound
  exact (bytesStoreX_setMappedByteOobShort
      (g := Sat256.ofUInt256 g) hreachBody hflag hvalid hbound)
    |>.reEquivExecutionRevert hcode hd hdec hbody

theorem bytesStoreSetMappedByteLongMalformedRuntime
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = bytesStoreBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x13, 0x2f, 0xa3, 0x46]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsz100 : 100 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (bytesStoreSetMappedByteValueWord I).toNat < EVM.twoPow 8)
    (hflag : UInt256.land (bytesStoreSetMappedByteHeaderWord σ_evm I) ⟨1⟩ ≠ ⟨0⟩)
    (hbad : UInt256.sub (UInt256.land (bytesStoreSetMappedByteHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStoreSetMappedByteHeaderWord σ_evm I) ⟨2⟩) ⟨32⟩) =
      ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreConfig bytesStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsz := bytesStoreSetMappedByteSelector_size hsel
  have hreach := bytesStoreReachSetMappedByte (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz hsize hsel
  have hreachPc : ∃ k C, RD bytesStoreBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨319⟩
      [bytesStoreSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ_evm) k C := by
    simpa [bytesStoreSetMappedByteEntryPc] using hreach
  have hreachBody := bytesStoreX_setMappedByteDecodeValid
    (g := Sat256.ofUInt256 g) hreachPc hsz100 hhi hsize
    (bytesStoreSetPacketByteLand255_eq_self_of_uint8 hcanon)
  have hd := bytesStoreDispatch_setMappedByte (cd := I.calldata)
    (by simpa [selIs] using hsel)
  have hdec := bytesStoreDecode_setMappedByte (I := I) hsz100 hhi hcanon
  have hload :
      Solm.EVM.storageLoad
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        I.codeOwner (bytesStoreSetMappedByteSlot I) =
          bytesStoreSetMappedByteHeaderWord σ_evm I := by
    simpa [initState] using
      bytesStoreStorageLoadSetMappedByteHeader_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hloadMapped :
      Solm.EVM.storageLoad
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        I.codeOwner
          (mappedValueSlot
            (.int ((bytesStoreSetMappedByteKeyWord I).toNat : Int))) =
          bytesStoreSetMappedByteHeaderWord σ_evm I := by
    simpa [bytesStoreSetMappedByteSlot, bytesStoreSetMappedSlotOf] using hload
  have hcodeOwner :
      (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner =
        I.codeOwner := by
    rfl
  have hlen :
      readStorageBytesLength? bytesStoreConfig
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (bytesStoreSetMappedByteHeaderRef I) = .revert := by
    exact bytesStoreReadLengthRevertOfHeaderLoad
      (er := bytesStoreSetMappedByteHeaderRef I)
      (evm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
      (baseSlot := bytesStoreSetMappedByteSlot I)
      (header := bytesStoreSetMappedByteHeaderWord σ_evm I)
      (bytesStoreSetMappedByteHeaderRef_length_slot
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I)
      hload
      (by simp [solidityDecodeBytesLengthHeader, hflag, hbad])
  have hbody :
      ExecTransitionBody bytesStoreConfig bytesStoreContract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (bytesStoreSetMappedByteLocals I) setMappedByteTransition.body .reverted := by
    exact bytesStoreSetMappedByteBodyRevertsOfLengthRead
      (by simp only [initState]; exact hwv) hlen
  exact (bytesStoreX_setMappedByteLongMalformed
      (g := Sat256.ofUInt256 g) hreachBody hflag hbad)
    |>.reEquivExecutionRevert hcode hd hdec hbody

theorem bytesStoreSetMappedByteShortMalformedRuntime
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = bytesStoreBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x13, 0x2f, 0xa3, 0x46]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsz100 : 100 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (bytesStoreSetMappedByteValueWord I).toNat < EVM.twoPow 8)
    (hflag : UInt256.land (bytesStoreSetMappedByteHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩)
    (hbad : UInt256.sub (UInt256.land (bytesStoreSetMappedByteHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStoreSetMappedByteHeaderWord σ_evm I) ⟨2⟩)
            ⟨127⟩) ⟨32⟩) = ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreConfig bytesStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsz := bytesStoreSetMappedByteSelector_size hsel
  have hreach := bytesStoreReachSetMappedByte (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz hsize hsel
  have hreachPc : ∃ k C, RD bytesStoreBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨319⟩
      [bytesStoreSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ_evm) k C := by
    simpa [bytesStoreSetMappedByteEntryPc] using hreach
  have hreachBody := bytesStoreX_setMappedByteDecodeValid
    (g := Sat256.ofUInt256 g) hreachPc hsz100 hhi hsize
    (bytesStoreSetPacketByteLand255_eq_self_of_uint8 hcanon)
  have hd := bytesStoreDispatch_setMappedByte (cd := I.calldata)
    (by simpa [selIs] using hsel)
  have hdec := bytesStoreDecode_setMappedByte (I := I) hsz100 hhi hcanon
  have hload :
      Solm.EVM.storageLoad
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        I.codeOwner (bytesStoreSetMappedByteSlot I) =
          bytesStoreSetMappedByteHeaderWord σ_evm I := by
    simpa [initState] using
      bytesStoreStorageLoadSetMappedByteHeader_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hloadMapped :
      Solm.EVM.storageLoad
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        I.codeOwner
          (mappedValueSlot
            (.int ((bytesStoreSetMappedByteKeyWord I).toNat : Int))) =
          bytesStoreSetMappedByteHeaderWord σ_evm I := by
    simpa [bytesStoreSetMappedByteSlot, bytesStoreSetMappedSlotOf] using hload
  have hcodeOwner :
      (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner =
        I.codeOwner := by
    rfl
  have hbad0 :
      UInt256.sub ⟨0⟩
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStoreSetMappedByteHeaderWord σ_evm I) ⟨2⟩)
            ⟨127⟩) ⟨32⟩) = ⟨0⟩ := by
    simpa [hflag] using hbad
  have hlen :
      readStorageBytesLength? bytesStoreConfig
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (bytesStoreSetMappedByteHeaderRef I) = .revert := by
    exact bytesStoreReadLengthRevertOfHeaderLoad
      (er := bytesStoreSetMappedByteHeaderRef I)
      (evm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
      (baseSlot := bytesStoreSetMappedByteSlot I)
      (header := bytesStoreSetMappedByteHeaderWord σ_evm I)
      (bytesStoreSetMappedByteHeaderRef_length_slot
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I)
      hload
      (by simp [solidityDecodeBytesLengthHeader, hflag, hbad0])
  have hbody :
      ExecTransitionBody bytesStoreConfig bytesStoreContract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (bytesStoreSetMappedByteLocals I) setMappedByteTransition.body .reverted := by
    exact bytesStoreSetMappedByteBodyRevertsOfLengthRead
      (by simp only [initState]; exact hwv) hlen
  exact (bytesStoreX_setMappedByteShortMalformed
      (g := Sat256.ofUInt256 g) hreachBody hflag hbad)
    |>.reEquivExecutionRevert hcode hd hdec hbody

end BytesStore
