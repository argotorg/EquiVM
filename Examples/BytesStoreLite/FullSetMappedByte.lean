import Examples.BytesStoreLite.FullSetMapped
import Examples.BytesStoreLite.FullSetChunkByte

/-!
# BytesStoreLite — `setMappedByte(uint256,uint256,uint8)` runtime slice

This split module starts the final full-contract setter arm.  The ABI shape matches
`setChunkByte(uint256,uint256,uint8)`, while the bytes header slot is the mapping value slot
`keccak256(key, 4)`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000
set_option maxHeartbeats 4000000

namespace BytesStoreLite

def bytesStoreLiteSetMappedByteKeyWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 4

def bytesStoreLiteSetMappedByteIndexWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 36

def bytesStoreLiteSetMappedByteValueWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 68

def bytesStoreLiteSetMappedByteLocals (I : ExecutionEnv) : Store :=
  (((∅ : Store).insert "key"
    (.int (Int.ofNat (bytesStoreLiteSetMappedByteKeyWord I).toNat))).insert "byteIndex"
    (.int (Int.ofNat (bytesStoreLiteSetMappedByteIndexWord I).toNat))).insert "value"
    (.int (Int.ofNat (bytesStoreLiteSetMappedByteValueWord I).toNat))

def bytesStoreLiteSetMappedByteRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "mapped"
    steps := [
      .mindex (.int (Int.ofNat (bytesStoreLiteSetMappedByteKeyWord I).toNat)),
      .aindex (.int (Int.ofNat (bytesStoreLiteSetMappedByteIndexWord I).toNat))] }

def bytesStoreLiteSetMappedByteHeaderRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "mapped"
    steps := [.mindex (.int (Int.ofNat (bytesStoreLiteSetMappedByteKeyWord I).toNat))] }

def bytesStoreLiteSetMappedByteValue (I : ExecutionEnv) : Value :=
  .int (Int.ofNat (bytesStoreLiteSetMappedByteValueWord I).toNat)

def bytesStoreLiteSetMappedByteFrame (I : ExecutionEnv) : Frame :=
  { contract := bytesStoreLiteContract, locals := bytesStoreLiteSetMappedByteLocals I }

def bytesStoreLiteSetMappedByteSlot (I : ExecutionEnv) : UInt256 :=
  bytesStoreLiteSetMappedSlotOf (bytesStoreLiteSetMappedByteKeyWord I)

def bytesStoreLiteSetMappedByteHeaderWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  (σ.find? I.codeOwner |>.option ⟨0⟩
    (fun acc => acc.storage.findD (bytesStoreLiteSetMappedByteSlot I) ⟨0⟩))

def bytesStoreLiteSetMappedByteShortScale (I : ExecutionEnv) : UInt256 :=
  UInt256.exp ⟨256⟩ (UInt256.sub ⟨31⟩ (bytesStoreLiteSetMappedByteIndexWord I))

def bytesStoreLiteSetMappedByteShortStoredWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.lor
    (UInt256.mul
      (UInt256.div (UInt256.shiftLeft (bytesStoreLiteSetMappedByteValueWord I) ⟨248⟩)
        (UInt256.shiftLeft ⟨1⟩ ⟨248⟩))
      (bytesStoreLiteSetMappedByteShortScale I))
    (UInt256.land
      (UInt256.lnot (UInt256.mul ⟨255⟩ (bytesStoreLiteSetMappedByteShortScale I)))
      (bytesStoreLiteSetMappedByteHeaderWord σ I))

def bytesStoreLiteSetMappedByteLongWordIndex (I : ExecutionEnv) : UInt256 :=
  UInt256.mod (bytesStoreLiteSetMappedByteIndexWord I) ⟨32⟩

def bytesStoreLiteSetMappedByteLongDataSlot (I : ExecutionEnv) : UInt256 :=
  bytesLikeDataBase (bytesStoreLiteSetMappedByteSlot I) +
    UInt256.div (bytesStoreLiteSetMappedByteIndexWord I) ⟨32⟩

/-- Trusted keccak disjointness: `mapped[key]` long-bytes data slots do not alias the header. -/
axiom bytesStoreLiteMappedLongDataSlot_ne_header (key idx : UInt256) :
    bytesLikeDataBase (bytesStoreLiteSetMappedSlotOf key) + UInt256.div idx ⟨32⟩ ≠
      bytesStoreLiteSetMappedSlotOf key

def bytesStoreLiteSetMappedByteLongScale (I : ExecutionEnv) : UInt256 :=
  UInt256.exp ⟨256⟩ (UInt256.sub ⟨31⟩ (bytesStoreLiteSetMappedByteLongWordIndex I))

def bytesStoreLiteSetMappedByteLongOldWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  (σ.find? I.codeOwner |>.option ⟨0⟩
    (fun acc => acc.storage.findD (bytesStoreLiteSetMappedByteLongDataSlot I) ⟨0⟩))

def bytesStoreLiteSetMappedByteLongStoredWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.lor
    (UInt256.mul
      (UInt256.div (UInt256.shiftLeft (bytesStoreLiteSetMappedByteValueWord I) ⟨248⟩)
        (UInt256.shiftLeft ⟨1⟩ ⟨248⟩))
      (bytesStoreLiteSetMappedByteLongScale I))
    (UInt256.land
      (UInt256.lnot (UInt256.mul ⟨255⟩ (bytesStoreLiteSetMappedByteLongScale I)))
      (bytesStoreLiteSetMappedByteLongOldWord σ I))

theorem bytesStoreLiteSetMappedByteKeyWord_eq_setMappedKeyWord (I : ExecutionEnv) :
    bytesStoreLiteSetMappedByteKeyWord I = bytesStoreLiteSetMappedKeyWord I := by
  rfl

theorem bytesStoreLiteSetMappedByteIndexWord_eq_setChunkByteIndexWord (I : ExecutionEnv) :
    bytesStoreLiteSetMappedByteIndexWord I = bytesStoreLiteSetChunkByteIndexWord I := by
  rfl

theorem bytesStoreLiteSetMappedByteValueWord_eq_setChunkByteValueWord (I : ExecutionEnv) :
    bytesStoreLiteSetMappedByteValueWord I = bytesStoreLiteSetChunkByteValueWord I := by
  rfl

theorem bytesStoreLiteSetMappedByteSlotHash (I : ExecutionEnv) :
    UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC
          ((twoWordHashMem (bytesStoreLiteSetMappedByteKeyWord I) ⟨4⟩ solcFreePtrMem
            ).readWithPadding 0 64))) =
      bytesStoreLiteSetMappedByteSlot I := by
  rw [twoWordHashMem_read0_64 (bytesStoreLiteSetMappedByteKeyWord I) ⟨4⟩
    solcFreePtrMem_size]
  unfold bytesStoreLiteSetMappedByteSlot bytesStoreLiteSetMappedSlotOf mappedValueSlot
  rw [keyValueToWord_uint256]
  exact mappingSlot_single (bytesStoreLiteSetMappedByteKeyWord I) ⟨4⟩

theorem bytesStoreLiteSetMappedByteLongWordIndex_toNat (I : ExecutionEnv) :
    (bytesStoreLiteSetMappedByteLongWordIndex I).toNat =
      (bytesStoreLiteSetMappedByteIndexWord I).toNat % 32 := by
  rw [bytesStoreLiteSetMappedByteLongWordIndex]
  unfold UInt256.mod
  rw [if_neg (by native_decide)]
  rfl

theorem bytesStoreLiteSetMappedByteLongWordIndex_lt32 (I : ExecutionEnv) :
    (bytesStoreLiteSetMappedByteLongWordIndex I).toNat < 32 := by
  rw [bytesStoreLiteSetMappedByteLongWordIndex_toNat]
  exact Nat.mod_lt _ (by decide : 0 < 32)

theorem bytesStoreLiteSetMappedByte_storageTypeAt {I : ExecutionEnv} :
    storageTypeAt? bytesStoreLiteContract.storage (bytesStoreLiteSetMappedByteRef I) =
      some uint8St := by
  simp [bytesStoreLiteSetMappedByteRef, storageTypeAt?, bytesStoreLiteContract, storageDecls,
    bytesSt, uint8St, uint8Int, storageTypeStep?]

theorem bytesStoreLiteSetMappedByteLayoutShort {evm : EVM.State} {I : ExecutionEnv}
    (hpacked : checkBytesPacked (bytesStoreLiteSetMappedByteSlot I) evm = true)
    (hidx : (bytesStoreLiteSetMappedByteIndexWord I).toNat < 31) :
    bytesStoreLiteConfig.storage.layout (bytesStoreLiteSetMappedByteRef I) evm =
      some (uint8Loc (bytesStoreLiteSetMappedByteSlot I)
        ⟨31 - (bytesStoreLiteSetMappedByteIndexWord I).toNat, by omega⟩) := by
  have hbyteNN :
      ¬ (((bytesStoreLiteSetMappedByteIndexWord I).toNat : Int) < 0) := by omega
  change bytesLikeByteLoc?
      (mappedValueSlot (.int (Int.ofNat (bytesStoreLiteSetMappedByteKeyWord I).toNat)))
      (.int (Int.ofNat (bytesStoreLiteSetMappedByteIndexWord I).toNat)) evm =
        some (uint8Loc (bytesStoreLiteSetMappedByteSlot I)
          ⟨31 - (bytesStoreLiteSetMappedByteIndexWord I).toNat, by omega⟩)
  have hpackedMapped :
      checkBytesPacked
          (mappedValueSlot (.int ((bytesStoreLiteSetMappedByteKeyWord I).toNat : Int)))
          evm = true := by
    simpa [bytesStoreLiteSetMappedByteSlot, bytesStoreLiteSetMappedSlotOf] using hpacked
  simp [bytesLikeByteLoc?, hbyteNN, hpackedMapped, hidx,
    bytesStoreLiteSetMappedByteSlot, bytesStoreLiteSetMappedSlotOf]

theorem bytesStoreLiteSetMappedByteLayoutLong {evm : EVM.State} {I : ExecutionEnv}
    (hpacked : checkBytesPacked (bytesStoreLiteSetMappedByteSlot I) evm = false) :
    bytesStoreLiteConfig.storage.layout (bytesStoreLiteSetMappedByteRef I) evm =
      some (uint8Loc (bytesStoreLiteSetMappedByteLongDataSlot I)
        ⟨31 - (bytesStoreLiteSetMappedByteLongWordIndex I).toNat, by
          have hidx := bytesStoreLiteSetMappedByteLongWordIndex_lt32 I
          omega⟩) := by
  have hbyteNN :
      ¬ (((bytesStoreLiteSetMappedByteIndexWord I).toNat : Int) < 0) := by omega
  change bytesLikeByteLoc?
      (mappedValueSlot (.int (Int.ofNat (bytesStoreLiteSetMappedByteKeyWord I).toNat)))
      (.int (Int.ofNat (bytesStoreLiteSetMappedByteIndexWord I).toNat)) evm =
        some (uint8Loc (bytesStoreLiteSetMappedByteLongDataSlot I)
          ⟨31 - (bytesStoreLiteSetMappedByteLongWordIndex I).toNat, by
            have hidx := bytesStoreLiteSetMappedByteLongWordIndex_lt32 I
            omega⟩)
  have hpackedMapped :
      checkBytesPacked
          (mappedValueSlot (.int ((bytesStoreLiteSetMappedByteKeyWord I).toNat : Int)))
          evm = false := by
    simpa [bytesStoreLiteSetMappedByteSlot, bytesStoreLiteSetMappedSlotOf] using hpacked
  rw [bytesStoreLiteSetMappedByteLongDataSlot, u256_div32_eq_ofNat_toNat_div]
  simp [bytesLikeByteLoc?, hbyteNN, hpackedMapped,
    bytesStoreLiteSetMappedByteSlot, bytesStoreLiteSetMappedSlotOf,
    bytesStoreLiteSetMappedByteLongWordIndex_toNat]

theorem bytesStoreLiteSetMappedByteIndex_lt31_of_short_bound {I : ExecutionEnv}
    {len : UInt256}
    (hshort : len.toNat < 32)
    (hbound : (bytesStoreLiteSetMappedByteIndexWord I).toNat < len.toNat) :
    (bytesStoreLiteSetMappedByteIndexWord I).toNat < 31 := by
  omega

theorem bytesStoreLiteSetMappedByteValueHighShiftDiv
    {I : ExecutionEnv}
    (hcanon : (bytesStoreLiteSetMappedByteValueWord I).toNat < EVM.twoPow 8) :
    UInt256.div (UInt256.shiftLeft (bytesStoreLiteSetMappedByteValueWord I) ⟨248⟩)
        (UInt256.shiftLeft ⟨1⟩ ⟨248⟩) =
      bytesStoreLiteSetMappedByteValueWord I := by
  simpa [bytesStoreLiteSetMappedByteValueWord_eq_setChunkByteValueWord] using
    bytesStoreLiteSetChunkByteValueHighShiftDiv (I := I) hcanon

theorem bytesStoreLiteSetMappedByteValueHighMulShiftRight
    {I : ExecutionEnv}
    (hcanon : (bytesStoreLiteSetMappedByteValueWord I).toNat < EVM.twoPow 8) :
    UInt256.shiftRight
      (UInt256.mul (bytesStoreLiteSetMappedByteValueWord I)
        (UInt256.shiftLeft ⟨1⟩ ⟨248⟩)) ⟨248⟩ =
      bytesStoreLiteSetMappedByteValueWord I := by
  rw [bytesStoreLiteShiftRight248_eq_div_scale]
  apply u256_inj
  rw [udiv_toNat, u256_mul_toNat, bytesStoreLiteShiftLeftOne248_toNat]
  have hv : (bytesStoreLiteSetMappedByteValueWord I).toNat < 256 := by
    simpa [EVM.twoPow] using hcanon
  have hlt : (bytesStoreLiteSetMappedByteValueWord I).toNat * 2 ^ 248 < UInt256.size := by
    rw [show UInt256.size = 2 ^ 256 from rfl]
    calc (bytesStoreLiteSetMappedByteValueWord I).toNat * 2 ^ 248 < 256 * 2 ^ 248 :=
        Nat.mul_lt_mul_of_pos_right hv (by positivity)
      _ = 2 ^ 256 := by
        rw [show (256 : Nat) = 2 ^ 8 by norm_num, ← Nat.pow_add]
        norm_num
  rw [Nat.mod_eq_of_lt hlt]
  rw [Nat.mul_comm]
  rw [Nat.mul_div_right _ (by positivity : 0 < 2 ^ 248)]

theorem bytesStoreLiteSetMappedByteLongScale_toNat {I : ExecutionEnv} :
    (bytesStoreLiteSetMappedByteLongScale I).toNat =
      2 ^ ((31 - (bytesStoreLiteSetMappedByteLongWordIndex I).toNat) * 8) := by
  simpa [bytesStoreLiteSetMappedByteLongScale, bytesStoreLiteSetChunkByteLongScale,
    bytesStoreLiteSetMappedByteLongWordIndex, bytesStoreLiteSetChunkByteLongWordIndex,
    bytesStoreLiteSetMappedByteIndexWord, bytesStoreLiteSetChunkByteIndexWord] using
    bytesStoreLiteSetChunkByteLongScale_toNat (I := I)

theorem bytesStoreLiteSetMappedByteLongMaskWord_toNat {I : ExecutionEnv} :
    (UInt256.mul ⟨255⟩ (bytesStoreLiteSetMappedByteLongScale I)).toNat =
      255 * 2 ^ ((31 - (bytesStoreLiteSetMappedByteLongWordIndex I).toNat) * 8) := by
  simpa [bytesStoreLiteSetMappedByteLongScale, bytesStoreLiteSetChunkByteLongScale,
    bytesStoreLiteSetMappedByteLongWordIndex, bytesStoreLiteSetChunkByteLongWordIndex,
    bytesStoreLiteSetMappedByteIndexWord, bytesStoreLiteSetChunkByteIndexWord] using
    bytesStoreLiteSetChunkByteLongMaskWord_toNat (I := I)

theorem bytesStoreLiteSetMappedByteLongClearMask_toNat {I : ExecutionEnv} :
    (UInt256.lnot (UInt256.mul ⟨255⟩ (bytesStoreLiteSetMappedByteLongScale I))).toNat =
      (2 : Nat) ^ 256 - 1 -
        255 * 2 ^ ((31 - (bytesStoreLiteSetMappedByteLongWordIndex I).toNat) * 8) := by
  simpa [bytesStoreLiteSetMappedByteLongScale, bytesStoreLiteSetChunkByteLongScale,
    bytesStoreLiteSetMappedByteLongWordIndex, bytesStoreLiteSetChunkByteLongWordIndex,
    bytesStoreLiteSetMappedByteIndexWord, bytesStoreLiteSetChunkByteIndexWord] using
    bytesStoreLiteSetChunkByteLongClearMask_toNat (I := I)

theorem bytesStoreLiteSetMappedByteShortScale_toNat {I : ExecutionEnv} {len : UInt256}
    (hshort : len.toNat < 32)
    (hbound : (bytesStoreLiteSetMappedByteIndexWord I).toNat < len.toNat) :
    (bytesStoreLiteSetMappedByteShortScale I).toNat =
      2 ^ ((31 - (bytesStoreLiteSetMappedByteIndexWord I).toNat) * 8) := by
  simpa [bytesStoreLiteSetMappedByteShortScale, bytesStoreLiteSetChunkByteShortScale,
    bytesStoreLiteSetMappedByteIndexWord, bytesStoreLiteSetChunkByteIndexWord] using
    bytesStoreLiteSetChunkByteShortScale_toNat (I := I) (len := len) hshort hbound

theorem bytesStoreLiteSetMappedByteShortMaskWord_toNat {I : ExecutionEnv} {len : UInt256}
    (hshort : len.toNat < 32)
    (hbound : (bytesStoreLiteSetMappedByteIndexWord I).toNat < len.toNat) :
    (UInt256.mul ⟨255⟩ (bytesStoreLiteSetMappedByteShortScale I)).toNat =
      255 * 2 ^ ((31 - (bytesStoreLiteSetMappedByteIndexWord I).toNat) * 8) := by
  simpa [bytesStoreLiteSetMappedByteShortScale, bytesStoreLiteSetChunkByteShortScale,
    bytesStoreLiteSetMappedByteIndexWord, bytesStoreLiteSetChunkByteIndexWord] using
    bytesStoreLiteSetChunkByteShortMaskWord_toNat (I := I) (len := len) hshort hbound

theorem bytesStoreLiteSetMappedByteShortClearMask_toNat {I : ExecutionEnv} {len : UInt256}
    (hshort : len.toNat < 32)
    (hbound : (bytesStoreLiteSetMappedByteIndexWord I).toNat < len.toNat) :
    (UInt256.lnot (UInt256.mul ⟨255⟩ (bytesStoreLiteSetMappedByteShortScale I))).toNat =
      2 ^ 256 - 1 -
        255 * 2 ^ ((31 - (bytesStoreLiteSetMappedByteIndexWord I).toNat) * 8) := by
  simpa [bytesStoreLiteSetMappedByteShortScale, bytesStoreLiteSetChunkByteShortScale,
    bytesStoreLiteSetMappedByteIndexWord, bytesStoreLiteSetChunkByteIndexWord] using
    bytesStoreLiteSetChunkByteShortClearMask_toNat (I := I) (len := len) hshort hbound

theorem bytesStoreLiteSetMappedByteShortStoredWord_byteAt
    {σ : AccountMap} {I : ExecutionEnv} {len : UInt256}
    (hcanon : (bytesStoreLiteSetMappedByteValueWord I).toNat < EVM.twoPow 8)
    (hshort : len.toNat < 32)
    (hbound : (bytesStoreLiteSetMappedByteIndexWord I).toNat < len.toNat) :
    UInt256.byteAt (bytesStoreLiteSetMappedByteIndexWord I)
      (bytesStoreLiteSetMappedByteShortStoredWord σ I) =
        bytesStoreLiteSetMappedByteValueWord I := by
  apply u256_inj
  have hi31 : (bytesStoreLiteSetMappedByteIndexWord I).toNat ≤ 31 := by
    have hlt := bytesStoreLiteSetMappedByteIndex_lt31_of_short_bound (I := I) (len := len)
      hshort hbound
    omega
  rw [byteAt_toNat_of_le31 hi31]
  rw [bytesStoreLiteSetMappedByteShortStoredWord,
    bytesStoreLiteSetMappedByteValueHighShiftDiv hcanon]
  rw [u256_lor_toNat, u256_mul_toNat, u256_land_toNat]
  rw [bytesStoreLiteSetMappedByteShortScale_toNat (I := I) (len := len) hshort hbound]
  rw [bytesStoreLiteSetMappedByteShortClearMask_toNat (I := I) (len := len) hshort hbound]
  have hv : (bytesStoreLiteSetMappedByteValueWord I).toNat < 256 := by
    simpa [EVM.twoPow] using hcanon
  have hk : ((31 - (bytesStoreLiteSetMappedByteIndexWord I).toNat) * 8) + 8 ≤ 256 := by
    have hidx : (bytesStoreLiteSetMappedByteIndexWord I).toNat < 31 :=
      bytesStoreLiteSetMappedByteIndex_lt31_of_short_bound (I := I) (len := len) hshort hbound
    omega
  have hleftLt : (bytesStoreLiteSetMappedByteValueWord I).toNat *
      2 ^ ((31 - (bytesStoreLiteSetMappedByteIndexWord I).toNat) * 8) < UInt256.size := by
    rw [show UInt256.size = 2 ^ 256 from rfl]
    calc (bytesStoreLiteSetMappedByteValueWord I).toNat *
            2 ^ ((31 - (bytesStoreLiteSetMappedByteIndexWord I).toNat) * 8) <
          256 * 2 ^ ((31 - (bytesStoreLiteSetMappedByteIndexWord I).toNat) * 8) :=
            Nat.mul_lt_mul_of_pos_right hv (by positivity)
        _ ≤ 2 ^ 256 := by
          rw [show 256 = 2 ^ 8 by norm_num, ← Nat.pow_add]
          exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hrightLt : (((2 : Nat) ^ 256 - 1 -
        255 * 2 ^ ((31 - (bytesStoreLiteSetMappedByteIndexWord I).toNat) * 8)) &&&
        (bytesStoreLiteSetMappedByteHeaderWord σ I).toNat) < UInt256.size := by
    exact lt_of_le_of_lt Nat.and_le_right (bytesStoreLiteSetMappedByteHeaderWord σ I).val.isLt
  rw [Nat.mod_eq_of_lt hleftLt]
  change ((bytesStoreLiteSetMappedByteValueWord I).toNat *
          2 ^ ((31 - (bytesStoreLiteSetMappedByteIndexWord I).toNat) * 8)).lor
        ((((2 : Nat) ^ 256 - 1 -
          255 * 2 ^ ((31 - (bytesStoreLiteSetMappedByteIndexWord I).toNat) * 8)) &&&
          (bytesStoreLiteSetMappedByteHeaderWord σ I).toNat) % UInt256.size) %
        UInt256.size /
      2 ^ ((31 - (bytesStoreLiteSetMappedByteIndexWord I).toNat) * 8) % 256 =
    (bytesStoreLiteSetMappedByteValueWord I).toNat
  rw [Nat.mod_eq_of_lt hrightLt]
  have hlorLt :
      ((bytesStoreLiteSetMappedByteValueWord I).toNat *
            2 ^ ((31 - (bytesStoreLiteSetMappedByteIndexWord I).toNat) * 8)).lor
          (((2 : Nat) ^ 256 - 1 -
              255 * 2 ^ ((31 - (bytesStoreLiteSetMappedByteIndexWord I).toNat) * 8)) &&&
            (bytesStoreLiteSetMappedByteHeaderWord σ I).toNat) < UInt256.size := by
    change ((bytesStoreLiteSetMappedByteValueWord I).toNat *
          2 ^ ((31 - (bytesStoreLiteSetMappedByteIndexWord I).toNat) * 8)) |||
        (((2 : Nat) ^ 256 - 1 -
            255 * 2 ^ ((31 - (bytesStoreLiteSetMappedByteIndexWord I).toNat) * 8)) &&&
          (bytesStoreLiteSetMappedByteHeaderWord σ I).toNat) < 2 ^ 256
    apply Nat.or_lt_two_pow
    · simpa [UInt256.size] using hleftLt
    · simpa [UInt256.size] using hrightLt
  rw [Nat.mod_eq_of_lt hlorLt]
  exact nat_byte_lane_lor_clear_eq
    (old := (bytesStoreLiteSetMappedByteHeaderWord σ I).toNat)
    (v := (bytesStoreLiteSetMappedByteValueWord I).toNat)
    (k := (31 - (bytesStoreLiteSetMappedByteIndexWord I).toNat) * 8) hv hk

theorem bytesStoreLiteSetMappedByteLongStoredWord_byteAt
    {σ : AccountMap} {I : ExecutionEnv}
    (hcanon : (bytesStoreLiteSetMappedByteValueWord I).toNat < EVM.twoPow 8) :
    UInt256.byteAt (bytesStoreLiteSetMappedByteLongWordIndex I)
      (bytesStoreLiteSetMappedByteLongStoredWord σ I) =
        bytesStoreLiteSetMappedByteValueWord I := by
  apply u256_inj
  have hv : (bytesStoreLiteSetMappedByteValueWord I).toNat < 256 := by
    simpa [EVM.twoPow] using hcanon
  have hidxLt : (bytesStoreLiteSetMappedByteLongWordIndex I).toNat < 32 :=
    bytesStoreLiteSetMappedByteLongWordIndex_lt32 I
  have hidxLe : (bytesStoreLiteSetMappedByteLongWordIndex I).toNat ≤ 31 := by omega
  rw [byteAt_toNat_of_le31 hidxLe]
  rw [bytesStoreLiteSetMappedByteLongStoredWord,
    bytesStoreLiteSetMappedByteValueHighShiftDiv hcanon]
  rw [u256_lor_toNat, u256_mul_toNat, u256_land_toNat]
  rw [bytesStoreLiteSetMappedByteLongScale_toNat (I := I)]
  rw [bytesStoreLiteSetMappedByteLongClearMask_toNat (I := I)]
  have hk : ((31 - (bytesStoreLiteSetMappedByteLongWordIndex I).toNat) * 8) + 8 ≤ 256 := by
    omega
  have hleftLt : (bytesStoreLiteSetMappedByteValueWord I).toNat *
      2 ^ ((31 - (bytesStoreLiteSetMappedByteLongWordIndex I).toNat) * 8) < UInt256.size := by
    rw [show UInt256.size = 2 ^ 256 from rfl]
    calc (bytesStoreLiteSetMappedByteValueWord I).toNat *
            2 ^ ((31 - (bytesStoreLiteSetMappedByteLongWordIndex I).toNat) * 8) <
          256 * 2 ^ ((31 - (bytesStoreLiteSetMappedByteLongWordIndex I).toNat) * 8) :=
            Nat.mul_lt_mul_of_pos_right hv (by positivity)
        _ = 2 ^ (8 + (31 - (bytesStoreLiteSetMappedByteLongWordIndex I).toNat) * 8) := by
          rw [show 256 = 2 ^ 8 by norm_num, Nat.pow_add]
        _ ≤ 2 ^ 256 := by
          exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hrightLt : (((2 : Nat) ^ 256 - 1 -
        255 * 2 ^ ((31 - (bytesStoreLiteSetMappedByteLongWordIndex I).toNat) * 8)) &&&
        (bytesStoreLiteSetMappedByteLongOldWord σ I).toNat) < UInt256.size := by
    exact lt_of_le_of_lt Nat.and_le_right (bytesStoreLiteSetMappedByteLongOldWord σ I).val.isLt
  rw [Nat.mod_eq_of_lt hleftLt]
  change (((bytesStoreLiteSetMappedByteValueWord I).toNat *
          2 ^ ((31 - (bytesStoreLiteSetMappedByteLongWordIndex I).toNat) * 8)).lor
        ((((2 : Nat) ^ 256 - 1 -
          255 * 2 ^ ((31 - (bytesStoreLiteSetMappedByteLongWordIndex I).toNat) * 8)) &&&
          (bytesStoreLiteSetMappedByteLongOldWord σ I).toNat) % UInt256.size) %
        UInt256.size) /
      2 ^ ((31 - (bytesStoreLiteSetMappedByteLongWordIndex I).toNat) * 8) % 256 =
    (bytesStoreLiteSetMappedByteValueWord I).toNat
  rw [Nat.mod_eq_of_lt hrightLt]
  have hlorLt :
      ((bytesStoreLiteSetMappedByteValueWord I).toNat *
            2 ^ ((31 - (bytesStoreLiteSetMappedByteLongWordIndex I).toNat) * 8)).lor
          (((2 : Nat) ^ 256 - 1 -
              255 * 2 ^ ((31 - (bytesStoreLiteSetMappedByteLongWordIndex I).toNat) * 8)) &&&
            (bytesStoreLiteSetMappedByteLongOldWord σ I).toNat) < UInt256.size := by
    change ((bytesStoreLiteSetMappedByteValueWord I).toNat *
          2 ^ ((31 - (bytesStoreLiteSetMappedByteLongWordIndex I).toNat) * 8)) |||
        (((2 : Nat) ^ 256 - 1 -
            255 * 2 ^ ((31 - (bytesStoreLiteSetMappedByteLongWordIndex I).toNat) * 8)) &&&
          (bytesStoreLiteSetMappedByteLongOldWord σ I).toNat) < 2 ^ 256
    apply Nat.or_lt_two_pow
    · simpa [UInt256.size] using hleftLt
    · simpa [UInt256.size] using hrightLt
  rw [Nat.mod_eq_of_lt hlorLt]
  exact nat_byte_lane_lor_clear_eq
    (old := (bytesStoreLiteSetMappedByteLongOldWord σ I).toNat)
    (v := (bytesStoreLiteSetMappedByteValueWord I).toNat)
    (k := (31 - (bytesStoreLiteSetMappedByteLongWordIndex I).toNat) * 8) hv hk

theorem bytesStoreLiteSetMappedByteShortStoredWord_toNat_update
    {σ : AccountMap} {I : ExecutionEnv} {len : UInt256}
    (hcanon : (bytesStoreLiteSetMappedByteValueWord I).toNat < EVM.twoPow 8)
    (hshort : len.toNat < 32)
    (hbound : (bytesStoreLiteSetMappedByteIndexWord I).toNat < len.toNat) :
    (bytesStoreLiteSetMappedByteHeaderWord σ I).toNat %
          2 ^ ((31 - (bytesStoreLiteSetMappedByteIndexWord I).toNat) * 8) +
        2 ^ ((31 - (bytesStoreLiteSetMappedByteIndexWord I).toNat) * 8) *
          (bytesStoreLiteSetMappedByteValueWord I).toNat +
      2 ^ ((31 - (bytesStoreLiteSetMappedByteIndexWord I).toNat) * 8 + 8) *
        ((bytesStoreLiteSetMappedByteHeaderWord σ I).toNat /
          2 ^ ((31 - (bytesStoreLiteSetMappedByteIndexWord I).toNat) * 8 + 8)) =
    (bytesStoreLiteSetMappedByteShortStoredWord σ I).toNat := by
  have hv : (bytesStoreLiteSetMappedByteValueWord I).toNat < 256 := by
    simpa [EVM.twoPow] using hcanon
  rw [bytesStoreLiteSetMappedByteShortStoredWord,
    bytesStoreLiteSetMappedByteValueHighShiftDiv hcanon]
  rw [u256_lor_toNat, u256_mul_toNat, u256_land_toNat]
  rw [bytesStoreLiteSetMappedByteShortScale_toNat (I := I) (len := len) hshort hbound]
  rw [bytesStoreLiteSetMappedByteShortClearMask_toNat (I := I) (len := len) hshort hbound]
  have hk : ((31 - (bytesStoreLiteSetMappedByteIndexWord I).toNat) * 8) + 8 ≤ 256 := by
    have hidx := bytesStoreLiteSetMappedByteIndex_lt31_of_short_bound
      (I := I) (len := len) hshort hbound
    omega
  have hleftLt : (bytesStoreLiteSetMappedByteValueWord I).toNat *
      2 ^ ((31 - (bytesStoreLiteSetMappedByteIndexWord I).toNat) * 8) < UInt256.size := by
    rw [show UInt256.size = 2 ^ 256 from rfl]
    calc (bytesStoreLiteSetMappedByteValueWord I).toNat *
            2 ^ ((31 - (bytesStoreLiteSetMappedByteIndexWord I).toNat) * 8) <
          256 * 2 ^ ((31 - (bytesStoreLiteSetMappedByteIndexWord I).toNat) * 8) :=
            Nat.mul_lt_mul_of_pos_right hv (by positivity)
        _ ≤ 2 ^ 256 := by
          rw [show 256 = 2 ^ 8 by norm_num, ← Nat.pow_add]
          exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hrightLt : (((2 : Nat) ^ 256 - 1 -
        255 * 2 ^ ((31 - (bytesStoreLiteSetMappedByteIndexWord I).toNat) * 8)) &&&
        (bytesStoreLiteSetMappedByteHeaderWord σ I).toNat) < UInt256.size := by
    exact lt_of_le_of_lt Nat.and_le_right (bytesStoreLiteSetMappedByteHeaderWord σ I).val.isLt
  rw [Nat.mod_eq_of_lt hleftLt]
  change (bytesStoreLiteSetMappedByteHeaderWord σ I).toNat %
        2 ^ ((31 - (bytesStoreLiteSetMappedByteIndexWord I).toNat) * 8) +
      2 ^ ((31 - (bytesStoreLiteSetMappedByteIndexWord I).toNat) * 8) *
        (bytesStoreLiteSetMappedByteValueWord I).toNat +
      2 ^ (((31 - (bytesStoreLiteSetMappedByteIndexWord I).toNat) * 8) + 8) *
        ((bytesStoreLiteSetMappedByteHeaderWord σ I).toNat /
          2 ^ (((31 - (bytesStoreLiteSetMappedByteIndexWord I).toNat) * 8) + 8)) =
      ((bytesStoreLiteSetMappedByteValueWord I).toNat *
          2 ^ ((31 - (bytesStoreLiteSetMappedByteIndexWord I).toNat) * 8)).lor
        ((((2 : Nat) ^ 256 - 1 -
          255 * 2 ^ ((31 - (bytesStoreLiteSetMappedByteIndexWord I).toNat) * 8)) &&&
          (bytesStoreLiteSetMappedByteHeaderWord σ I).toNat) % UInt256.size) %
        UInt256.size
  rw [Nat.mod_eq_of_lt hrightLt]
  have hlorLt :
      ((bytesStoreLiteSetMappedByteValueWord I).toNat *
            2 ^ ((31 - (bytesStoreLiteSetMappedByteIndexWord I).toNat) * 8)).lor
          (((2 : Nat) ^ 256 - 1 -
              255 * 2 ^ ((31 - (bytesStoreLiteSetMappedByteIndexWord I).toNat) * 8)) &&&
            (bytesStoreLiteSetMappedByteHeaderWord σ I).toNat) < UInt256.size := by
    change ((bytesStoreLiteSetMappedByteValueWord I).toNat *
          2 ^ ((31 - (bytesStoreLiteSetMappedByteIndexWord I).toNat) * 8)) |||
        (((2 : Nat) ^ 256 - 1 -
            255 * 2 ^ ((31 - (bytesStoreLiteSetMappedByteIndexWord I).toNat) * 8)) &&&
          (bytesStoreLiteSetMappedByteHeaderWord σ I).toNat) < 2 ^ 256
    apply Nat.or_lt_two_pow
    · simpa [UInt256.size] using hleftLt
    · simpa [UInt256.size] using hrightLt
  rw [Nat.mod_eq_of_lt hlorLt]
  rw [show 2 ^ ((31 - (bytesStoreLiteSetMappedByteIndexWord I).toNat) * 8) *
        (bytesStoreLiteSetMappedByteValueWord I).toNat =
        (bytesStoreLiteSetMappedByteValueWord I).toNat *
          2 ^ ((31 - (bytesStoreLiteSetMappedByteIndexWord I).toNat) * 8) by ring]
  rw [show 2 ^ (((31 - (bytesStoreLiteSetMappedByteIndexWord I).toNat) * 8) + 8) *
        ((bytesStoreLiteSetMappedByteHeaderWord σ I).toNat /
          2 ^ (((31 - (bytesStoreLiteSetMappedByteIndexWord I).toNat) * 8) + 8)) =
      (bytesStoreLiteSetMappedByteHeaderWord σ I).toNat /
          2 ^ (((31 - (bytesStoreLiteSetMappedByteIndexWord I).toNat) * 8) + 8) *
        2 ^ (((31 - (bytesStoreLiteSetMappedByteIndexWord I).toNat) * 8) + 8) by ring]
  exact nat_byte_update_eq
    (old := (bytesStoreLiteSetMappedByteHeaderWord σ I).toNat)
    (v := (bytesStoreLiteSetMappedByteValueWord I).toNat)
    (k := (31 - (bytesStoreLiteSetMappedByteIndexWord I).toNat) * 8)
    hv hk (by exact (bytesStoreLiteSetMappedByteHeaderWord σ I).val.isLt)

theorem bytesStoreLiteSetMappedByteLongStoredWord_toNat_update
    {σ : AccountMap} {I : ExecutionEnv}
    (hcanon : (bytesStoreLiteSetMappedByteValueWord I).toNat < EVM.twoPow 8) :
    (bytesStoreLiteSetMappedByteLongOldWord σ I).toNat %
          2 ^ ((31 - (bytesStoreLiteSetMappedByteLongWordIndex I).toNat) * 8) +
        2 ^ ((31 - (bytesStoreLiteSetMappedByteLongWordIndex I).toNat) * 8) *
          (bytesStoreLiteSetMappedByteValueWord I).toNat +
      2 ^ ((31 - (bytesStoreLiteSetMappedByteLongWordIndex I).toNat) * 8 + 8) *
        ((bytesStoreLiteSetMappedByteLongOldWord σ I).toNat /
          2 ^ ((31 - (bytesStoreLiteSetMappedByteLongWordIndex I).toNat) * 8 + 8)) =
    (bytesStoreLiteSetMappedByteLongStoredWord σ I).toNat := by
  have hv : (bytesStoreLiteSetMappedByteValueWord I).toNat < 256 := by
    simpa [EVM.twoPow] using hcanon
  rw [bytesStoreLiteSetMappedByteLongStoredWord,
    bytesStoreLiteSetMappedByteValueHighShiftDiv hcanon]
  rw [u256_lor_toNat, u256_mul_toNat, u256_land_toNat]
  rw [bytesStoreLiteSetMappedByteLongScale_toNat (I := I)]
  rw [bytesStoreLiteSetMappedByteLongClearMask_toNat (I := I)]
  have hidxLt : (bytesStoreLiteSetMappedByteLongWordIndex I).toNat < 32 :=
    bytesStoreLiteSetMappedByteLongWordIndex_lt32 I
  have hk : ((31 - (bytesStoreLiteSetMappedByteLongWordIndex I).toNat) * 8) + 8 ≤ 256 := by
    omega
  have hleftLt : (bytesStoreLiteSetMappedByteValueWord I).toNat *
      2 ^ ((31 - (bytesStoreLiteSetMappedByteLongWordIndex I).toNat) * 8) < UInt256.size := by
    rw [show UInt256.size = 2 ^ 256 from rfl]
    calc (bytesStoreLiteSetMappedByteValueWord I).toNat *
            2 ^ ((31 - (bytesStoreLiteSetMappedByteLongWordIndex I).toNat) * 8) <
          256 * 2 ^ ((31 - (bytesStoreLiteSetMappedByteLongWordIndex I).toNat) * 8) :=
            Nat.mul_lt_mul_of_pos_right hv (by positivity)
        _ = 2 ^ (8 + (31 - (bytesStoreLiteSetMappedByteLongWordIndex I).toNat) * 8) := by
          rw [show 256 = 2 ^ 8 by norm_num, Nat.pow_add]
        _ ≤ 2 ^ 256 := by
          exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hrightLt : (((2 : Nat) ^ 256 - 1 -
        255 * 2 ^ ((31 - (bytesStoreLiteSetMappedByteLongWordIndex I).toNat) * 8)) &&&
        (bytesStoreLiteSetMappedByteLongOldWord σ I).toNat) < UInt256.size := by
    exact lt_of_le_of_lt Nat.and_le_right (bytesStoreLiteSetMappedByteLongOldWord σ I).val.isLt
  rw [Nat.mod_eq_of_lt hleftLt]
  change (bytesStoreLiteSetMappedByteLongOldWord σ I).toNat %
        2 ^ ((31 - (bytesStoreLiteSetMappedByteLongWordIndex I).toNat) * 8) +
      2 ^ ((31 - (bytesStoreLiteSetMappedByteLongWordIndex I).toNat) * 8) *
        (bytesStoreLiteSetMappedByteValueWord I).toNat +
      2 ^ (((31 - (bytesStoreLiteSetMappedByteLongWordIndex I).toNat) * 8) + 8) *
        ((bytesStoreLiteSetMappedByteLongOldWord σ I).toNat /
          2 ^ (((31 - (bytesStoreLiteSetMappedByteLongWordIndex I).toNat) * 8) + 8)) =
      ((bytesStoreLiteSetMappedByteValueWord I).toNat *
          2 ^ ((31 - (bytesStoreLiteSetMappedByteLongWordIndex I).toNat) * 8)).lor
        ((((2 : Nat) ^ 256 - 1 -
          255 * 2 ^ ((31 - (bytesStoreLiteSetMappedByteLongWordIndex I).toNat) * 8)) &&&
          (bytesStoreLiteSetMappedByteLongOldWord σ I).toNat) % UInt256.size) %
        UInt256.size
  rw [Nat.mod_eq_of_lt hrightLt]
  have hlorLt :
      ((bytesStoreLiteSetMappedByteValueWord I).toNat *
            2 ^ ((31 - (bytesStoreLiteSetMappedByteLongWordIndex I).toNat) * 8)).lor
          (((2 : Nat) ^ 256 - 1 -
              255 * 2 ^ ((31 - (bytesStoreLiteSetMappedByteLongWordIndex I).toNat) * 8)) &&&
            (bytesStoreLiteSetMappedByteLongOldWord σ I).toNat) < UInt256.size := by
    change ((bytesStoreLiteSetMappedByteValueWord I).toNat *
          2 ^ ((31 - (bytesStoreLiteSetMappedByteLongWordIndex I).toNat) * 8)) |||
        (((2 : Nat) ^ 256 - 1 -
            255 * 2 ^ ((31 - (bytesStoreLiteSetMappedByteLongWordIndex I).toNat) * 8)) &&&
          (bytesStoreLiteSetMappedByteLongOldWord σ I).toNat) < 2 ^ 256
    apply Nat.or_lt_two_pow
    · simpa [UInt256.size] using hleftLt
    · simpa [UInt256.size] using hrightLt
  rw [Nat.mod_eq_of_lt hlorLt]
  rw [show 2 ^ ((31 - (bytesStoreLiteSetMappedByteLongWordIndex I).toNat) * 8) *
        (bytesStoreLiteSetMappedByteValueWord I).toNat =
        (bytesStoreLiteSetMappedByteValueWord I).toNat *
          2 ^ ((31 - (bytesStoreLiteSetMappedByteLongWordIndex I).toNat) * 8) by ring]
  rw [show 2 ^ (((31 - (bytesStoreLiteSetMappedByteLongWordIndex I).toNat) * 8) + 8) *
        ((bytesStoreLiteSetMappedByteLongOldWord σ I).toNat /
          2 ^ (((31 - (bytesStoreLiteSetMappedByteLongWordIndex I).toNat) * 8) + 8)) =
      (bytesStoreLiteSetMappedByteLongOldWord σ I).toNat /
          2 ^ (((31 - (bytesStoreLiteSetMappedByteLongWordIndex I).toNat) * 8) + 8) *
        2 ^ (((31 - (bytesStoreLiteSetMappedByteLongWordIndex I).toNat) * 8) + 8) by ring]
  exact nat_byte_update_eq
    (old := (bytesStoreLiteSetMappedByteLongOldWord σ I).toNat)
    (v := (bytesStoreLiteSetMappedByteValueWord I).toNat)
    (k := (31 - (bytesStoreLiteSetMappedByteLongWordIndex I).toNat) * 8)
    hv hk (by exact (bytesStoreLiteSetMappedByteLongOldWord σ I).val.isLt)

theorem bytesStoreLiteSetMappedByteShortScale_mod256_zero {I : ExecutionEnv} {len : UInt256}
    (hshort : len.toNat < 32)
    (hbound : (bytesStoreLiteSetMappedByteIndexWord I).toNat < len.toNat) :
    (bytesStoreLiteSetMappedByteShortScale I).toNat % 256 = 0 := by
  have hidx : (bytesStoreLiteSetMappedByteIndexWord I).toNat < 31 :=
    bytesStoreLiteSetMappedByteIndex_lt31_of_short_bound hshort hbound
  interval_cases hnat : (bytesStoreLiteSetMappedByteIndexWord I).toNat
  all_goals
    have hword : bytesStoreLiteSetMappedByteIndexWord I =
        UInt256.ofNat (bytesStoreLiteSetMappedByteIndexWord I).toNat := by
      exact (u256_ofNat_toNat (bytesStoreLiteSetMappedByteIndexWord I)).symm
    rw [bytesStoreLiteSetMappedByteShortScale, hword, hnat]
    native_decide

theorem bytesStoreLiteSetMappedByteShortClearMask_mod256_255 {I : ExecutionEnv}
    {len : UInt256}
    (hshort : len.toNat < 32)
    (hbound : (bytesStoreLiteSetMappedByteIndexWord I).toNat < len.toNat) :
    (UInt256.lnot (UInt256.mul ⟨255⟩ (bytesStoreLiteSetMappedByteShortScale I))).toNat %
        256 = 255 := by
  have hidx : (bytesStoreLiteSetMappedByteIndexWord I).toNat < 31 :=
    bytesStoreLiteSetMappedByteIndex_lt31_of_short_bound hshort hbound
  interval_cases hnat : (bytesStoreLiteSetMappedByteIndexWord I).toNat
  all_goals
    have hword : bytesStoreLiteSetMappedByteIndexWord I =
        UInt256.ofNat (bytesStoreLiteSetMappedByteIndexWord I).toNat := by
      exact (u256_ofNat_toNat (bytesStoreLiteSetMappedByteIndexWord I)).symm
    rw [bytesStoreLiteSetMappedByteShortScale, hword, hnat]
    native_decide

theorem bytesStoreLiteSetMappedByteShortStoredWord_mod256
    {σ : AccountMap} {I : ExecutionEnv} {len : UInt256}
    (hshort : len.toNat < 32)
    (hbound : (bytesStoreLiteSetMappedByteIndexWord I).toNat < len.toNat) :
    (bytesStoreLiteSetMappedByteShortStoredWord σ I).toNat % 256 =
      (bytesStoreLiteSetMappedByteHeaderWord σ I).toNat % 256 := by
  have hscale := bytesStoreLiteSetMappedByteShortScale_mod256_zero
    (I := I) (len := len) hshort hbound
  have hmask := bytesStoreLiteSetMappedByteShortClearMask_mod256_255
    (I := I) (len := len) hshort hbound
  have hleft :
      (UInt256.mul
        (UInt256.div (UInt256.shiftLeft (bytesStoreLiteSetMappedByteValueWord I) ⟨248⟩)
          (UInt256.shiftLeft ⟨1⟩ ⟨248⟩))
        (bytesStoreLiteSetMappedByteShortScale I)).toNat % 256 = 0 := by
    rw [u256_mul_toNat, nat_mod_u256_mod_256, Nat.mul_mod, hscale]
    simp
  have hright :
      (UInt256.land
        (UInt256.lnot (UInt256.mul ⟨255⟩ (bytesStoreLiteSetMappedByteShortScale I)))
        (bytesStoreLiteSetMappedByteHeaderWord σ I)).toNat % 256 =
        (bytesStoreLiteSetMappedByteHeaderWord σ I).toNat % 256 := by
    rw [u256_land_toNat, nat_mod_u256_mod_256]
    exact nat_land_mod_256_of_left_255 hmask
  rw [bytesStoreLiteSetMappedByteShortStoredWord, u256_lor_toNat, nat_mod_u256_mod_256]
  rw [nat_lor_mod_256_of_left_zero hleft, hright]

theorem bytesStoreLiteSetMappedByteShortStoredWord_flag_eq
    {σ : AccountMap} {I : ExecutionEnv} {len : UInt256}
    (hshort : len.toNat < 32)
    (hbound : (bytesStoreLiteSetMappedByteIndexWord I).toNat < len.toNat) :
    UInt256.land (bytesStoreLiteSetMappedByteShortStoredWord σ I) ⟨1⟩ =
      UInt256.land (bytesStoreLiteSetMappedByteHeaderWord σ I) ⟨1⟩ := by
  apply u256_inj
  rw [uInt256_land_one_toNat, uInt256_land_one_toNat]
  have hmod := bytesStoreLiteSetMappedByteShortStoredWord_mod256
    (σ := σ) (I := I) (len := len) hshort hbound
  have hleft :
      (bytesStoreLiteSetMappedByteShortStoredWord σ I).toNat % 2 =
        ((bytesStoreLiteSetMappedByteShortStoredWord σ I).toNat % 256) % 2 := by
    rw [Nat.mod_mod_of_dvd]
    norm_num
  have hright :
      (bytesStoreLiteSetMappedByteHeaderWord σ I).toNat % 2 =
        ((bytesStoreLiteSetMappedByteHeaderWord σ I).toNat % 256) % 2 := by
    rw [Nat.mod_mod_of_dvd]
    norm_num
  rw [hleft, hright, hmod]

theorem bytesStoreLiteSetMappedByteShortStoredWord_shortLen_eq
    {σ : AccountMap} {I : ExecutionEnv} {len : UInt256}
    (hshort : len.toNat < 32)
    (hbound : (bytesStoreLiteSetMappedByteIndexWord I).toNat < len.toNat) :
    UInt256.land (UInt256.div (bytesStoreLiteSetMappedByteShortStoredWord σ I) ⟨2⟩) ⟨127⟩ =
      UInt256.land (UInt256.div (bytesStoreLiteSetMappedByteHeaderWord σ I) ⟨2⟩) ⟨127⟩ := by
  apply u256_inj
  rw [bytesStoreLiteShortLenBits_toNat, bytesStoreLiteShortLenBits_toNat]
  rw [bytesStoreLiteSetMappedByteShortStoredWord_mod256 (σ := σ) (I := I) (len := len)
    hshort hbound]

theorem bytesStoreLiteSetMappedByteStorageLocStoreShort
    {evm : EVM.State} {σ : AccountMap} {I : ExecutionEnv} {len : UInt256}
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (bytesStoreLiteSetMappedByteSlot I) = bytesStoreLiteSetMappedByteHeaderWord σ I)
    (hcanon : (bytesStoreLiteSetMappedByteValueWord I).toNat < EVM.twoPow 8)
    (hshort : len.toNat < 32)
    (hbound : (bytesStoreLiteSetMappedByteIndexWord I).toNat < len.toNat) :
    storageLocStore evm
      (uint8Loc (bytesStoreLiteSetMappedByteSlot I)
        ⟨31 - (bytesStoreLiteSetMappedByteIndexWord I).toNat, by
          have hidx := bytesStoreLiteSetMappedByteIndex_lt31_of_short_bound
            (I := I) (len := len) hshort hbound
          omega⟩)
      (bytesStoreLiteSetMappedByteValue I) =
      some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner
        (bytesStoreLiteSetMappedByteSlot I)
        (bytesStoreLiteSetMappedByteShortStoredWord σ I)) := by
  let offFin : Fin 32 :=
    ⟨31 - (bytesStoreLiteSetMappedByteIndexWord I).toNat, by
      have hidx := bytesStoreLiteSetMappedByteIndex_lt31_of_short_bound
        (I := I) (len := len) hshort hbound
      omega⟩
  have hval : valueToWord (bytesStoreLiteSetMappedByteValue I) =
      some (UInt256.ofNat (bytesStoreLiteSetMappedByteValueWord I).toNat) := by
    simp [bytesStoreLiteSetMappedByteValue, valueToWord]
    exact bytesStoreLiteWordOfIntOfNatEq (bytesStoreLiteSetMappedByteValueWord I).toNat
  have hoffVal : offFin.val = 31 - (bytesStoreLiteSetMappedByteIndexWord I).toNat := by
    rfl
  have hoffLe : offFin.val ≤ 32 := Nat.le_of_lt offFin.isLt
  have hv : (bytesStoreLiteSetMappedByteValueWord I).toNat < 256 := by
    simpa [EVM.twoPow] using hcanon
  have hoffBound : offFin.val + (1 : Fin 33).val - 1 < 32 := by
    have hidx := bytesStoreLiteSetMappedByteIndex_lt31_of_short_bound
      (I := I) (len := len) hshort hbound
    simp [offFin]
    omega
  have htarget :
      (bytesStoreLiteSetMappedByteShortStoredWord σ I).toNat =
        fromBytes'
          ((EVM.Word.toBytesLEWithSizeProof
                (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
                  (bytesStoreLiteSetMappedByteSlot I))).1.take offFin.val ++
           (EVM.Word.toBytesLEWithSizeProof
                (storageLocWriteWord
                  (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
                    (bytesStoreLiteSetMappedByteSlot I))
                  offFin.val none
                  (UInt256.ofNat (bytesStoreLiteSetMappedByteValueWord I).toNat))).1.take 1 ++
           (EVM.Word.toBytesLEWithSizeProof
                (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
                  (bytesStoreLiteSetMappedByteSlot I))).1.drop
              (offFin.val + 1)) := by
    rw [hload]
    simp only [storageLocWriteWord]
    symm
    rw [fromBytes'_append, fromBytes'_append]
    rw [fromBytes'_take_wordLE, fromBytes'_take_wordLE, fromBytes'_drop_wordLE]
    have hslen := (EVM.Word.toBytesLEWithSizeProof
      (bytesStoreLiteSetMappedByteHeaderWord σ I)).2
    have hvlen := (EVM.Word.toBytesLEWithSizeProof
      (UInt256.ofNat (bytesStoreLiteSetMappedByteValueWord I).toNat)).2
    rw [List.length_take, hslen, Nat.min_eq_left hoffLe]
    rw [List.length_append, List.length_take, hslen, Nat.min_eq_left hoffLe,
      List.length_take, hvlen, Nat.min_eq_left (by norm_num : 1 ≤ 32)]
    rw [show 8 * (offFin.val + 1) = 8 * offFin.val + 8 by ring]
    rw [show 256 ^ offFin.val = 2 ^ (8 * offFin.val) by
      rw [show (256 : Nat) = 2 ^ 8 by norm_num, ← Nat.pow_mul]]
    rw [show 256 ^ 1 = 256 by norm_num]
    rw [show (UInt256.ofNat (bytesStoreLiteSetMappedByteValueWord I).toNat).toNat % 256 =
        (bytesStoreLiteSetMappedByteValueWord I).toNat by
      rw [ulit_toNat' _ (lt_of_lt_of_le hv (by norm_num [UInt256.size]))]
      exact Nat.mod_eq_of_lt hv]
    rw [hoffVal]
    rw [show 8 * (31 - (bytesStoreLiteSetMappedByteIndexWord I).toNat) =
        (31 - (bytesStoreLiteSetMappedByteIndexWord I).toNat) * 8 by ring]
    rw [show 256 ^ (31 - (bytesStoreLiteSetMappedByteIndexWord I).toNat + 1) =
        2 ^ (((31 - (bytesStoreLiteSetMappedByteIndexWord I).toNat) * 8) + 8) by
      rw [show 256 = 2 ^ 8 by norm_num, ← Nat.pow_mul]
      congr 1
      ring]
    change
      (bytesStoreLiteSetMappedByteHeaderWord σ I).toNat %
            2 ^ ((31 - (bytesStoreLiteSetMappedByteIndexWord I).toNat) * 8) +
          2 ^ ((31 - (bytesStoreLiteSetMappedByteIndexWord I).toNat) * 8) *
            (bytesStoreLiteSetMappedByteValueWord I).toNat +
        2 ^ ((31 - (bytesStoreLiteSetMappedByteIndexWord I).toNat) * 8 + 8) *
          ((bytesStoreLiteSetMappedByteHeaderWord σ I).toNat /
            2 ^ ((31 - (bytesStoreLiteSetMappedByteIndexWord I).toNat) * 8 + 8)) =
      (bytesStoreLiteSetMappedByteShortStoredWord σ I).toNat
    exact bytesStoreLiteSetMappedByteShortStoredWord_toNat_update
      (σ := σ) (I := I) (len := len) hcanon hshort hbound
  change storageLocStore evm
      { slot := bytesStoreLiteSetMappedByteSlot I, offset := offFin, size := 1,
        hbound := hoffBound, type := .int uint8Int }
      (bytesStoreLiteSetMappedByteValue I) =
      some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner
        (bytesStoreLiteSetMappedByteSlot I)
        (bytesStoreLiteSetMappedByteShortStoredWord σ I))
  exact storageLocStore_oneByte_local evm (bytesStoreLiteSetMappedByteSlot I)
    (UInt256.ofNat (bytesStoreLiteSetMappedByteValueWord I).toNat)
    (bytesStoreLiteSetMappedByteShortStoredWord σ I)
    offFin (.int uint8Int) hoffBound
    (bytesStoreLiteSetMappedByteValue I) hval htarget

theorem bytesStoreLiteSetMappedByteStorageLocStoreLong
    {evm : EVM.State} {σ : AccountMap} {I : ExecutionEnv}
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (bytesStoreLiteSetMappedByteLongDataSlot I) =
      bytesStoreLiteSetMappedByteLongOldWord σ I)
    (hcanon : (bytesStoreLiteSetMappedByteValueWord I).toNat < EVM.twoPow 8) :
    storageLocStore evm
      (uint8Loc (bytesStoreLiteSetMappedByteLongDataSlot I)
        ⟨31 - (bytesStoreLiteSetMappedByteLongWordIndex I).toNat, by
          have hidx := bytesStoreLiteSetMappedByteLongWordIndex_lt32 I
          omega⟩)
      (bytesStoreLiteSetMappedByteValue I) =
      some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner
        (bytesStoreLiteSetMappedByteLongDataSlot I)
        (bytesStoreLiteSetMappedByteLongStoredWord σ I)) := by
  let offFin : Fin 32 :=
    ⟨31 - (bytesStoreLiteSetMappedByteLongWordIndex I).toNat, by
      have hidx := bytesStoreLiteSetMappedByteLongWordIndex_lt32 I
      omega⟩
  have hval : valueToWord (bytesStoreLiteSetMappedByteValue I) =
      some (UInt256.ofNat (bytesStoreLiteSetMappedByteValueWord I).toNat) := by
    simp [bytesStoreLiteSetMappedByteValue, valueToWord]
    exact bytesStoreLiteWordOfIntOfNatEq (bytesStoreLiteSetMappedByteValueWord I).toNat
  have hoffVal : offFin.val = 31 - (bytesStoreLiteSetMappedByteLongWordIndex I).toNat := by
    rfl
  have hoffLe : offFin.val ≤ 32 := Nat.le_of_lt offFin.isLt
  have hv : (bytesStoreLiteSetMappedByteValueWord I).toNat < 256 := by
    simpa [EVM.twoPow] using hcanon
  have hoffBound : offFin.val + (1 : Fin 33).val - 1 < 32 := by
    simp [offFin]
    omega
  have htarget :
      (bytesStoreLiteSetMappedByteLongStoredWord σ I).toNat =
        fromBytes'
          ((EVM.Word.toBytesLEWithSizeProof
                (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
                  (bytesStoreLiteSetMappedByteLongDataSlot I))).1.take offFin.val ++
           (EVM.Word.toBytesLEWithSizeProof
                (storageLocWriteWord
                  (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
                    (bytesStoreLiteSetMappedByteLongDataSlot I))
                  offFin.val none
                  (UInt256.ofNat (bytesStoreLiteSetMappedByteValueWord I).toNat))).1.take 1 ++
           (EVM.Word.toBytesLEWithSizeProof
                (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
                  (bytesStoreLiteSetMappedByteLongDataSlot I))).1.drop
              (offFin.val + 1)) := by
    rw [hload]
    simp only [storageLocWriteWord]
    symm
    rw [fromBytes'_append, fromBytes'_append]
    rw [fromBytes'_take_wordLE, fromBytes'_take_wordLE, fromBytes'_drop_wordLE]
    have hslen := (EVM.Word.toBytesLEWithSizeProof
      (bytesStoreLiteSetMappedByteLongOldWord σ I)).2
    have hvlen := (EVM.Word.toBytesLEWithSizeProof
      (UInt256.ofNat (bytesStoreLiteSetMappedByteValueWord I).toNat)).2
    rw [List.length_take, hslen, Nat.min_eq_left hoffLe]
    rw [List.length_append, List.length_take, hslen, Nat.min_eq_left hoffLe,
      List.length_take, hvlen, Nat.min_eq_left (by norm_num : 1 ≤ 32)]
    rw [show 8 * (offFin.val + 1) = 8 * offFin.val + 8 by ring]
    rw [show 256 ^ offFin.val = 2 ^ (8 * offFin.val) by
      rw [show (256 : Nat) = 2 ^ 8 by norm_num, ← Nat.pow_mul]]
    rw [show 256 ^ 1 = 256 by norm_num]
    rw [show (UInt256.ofNat (bytesStoreLiteSetMappedByteValueWord I).toNat).toNat % 256 =
        (bytesStoreLiteSetMappedByteValueWord I).toNat by
      rw [ulit_toNat' _ (lt_of_lt_of_le hv (by norm_num [UInt256.size]))]
      exact Nat.mod_eq_of_lt hv]
    rw [hoffVal]
    rw [show 8 * (31 - (bytesStoreLiteSetMappedByteLongWordIndex I).toNat) =
        (31 - (bytesStoreLiteSetMappedByteLongWordIndex I).toNat) * 8 by ring]
    rw [show 256 ^ (31 - (bytesStoreLiteSetMappedByteLongWordIndex I).toNat + 1) =
        2 ^ (((31 - (bytesStoreLiteSetMappedByteLongWordIndex I).toNat) * 8) + 8) by
      rw [show 256 = 2 ^ 8 by norm_num, ← Nat.pow_mul]
      congr 1
      ring]
    change
      (bytesStoreLiteSetMappedByteLongOldWord σ I).toNat %
            2 ^ ((31 - (bytesStoreLiteSetMappedByteLongWordIndex I).toNat) * 8) +
          2 ^ ((31 - (bytesStoreLiteSetMappedByteLongWordIndex I).toNat) * 8) *
            (bytesStoreLiteSetMappedByteValueWord I).toNat +
        2 ^ ((31 - (bytesStoreLiteSetMappedByteLongWordIndex I).toNat) * 8 + 8) *
          ((bytesStoreLiteSetMappedByteLongOldWord σ I).toNat /
            2 ^ ((31 - (bytesStoreLiteSetMappedByteLongWordIndex I).toNat) * 8 + 8)) =
      (bytesStoreLiteSetMappedByteLongStoredWord σ I).toNat
    exact bytesStoreLiteSetMappedByteLongStoredWord_toNat_update
      (σ := σ) (I := I) hcanon
  change storageLocStore evm
      { slot := bytesStoreLiteSetMappedByteLongDataSlot I, offset := offFin, size := 1,
        hbound := hoffBound, type := .int uint8Int }
      (bytesStoreLiteSetMappedByteValue I) =
      some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner
        (bytesStoreLiteSetMappedByteLongDataSlot I)
        (bytesStoreLiteSetMappedByteLongStoredWord σ I))
  exact storageLocStore_oneByte_local evm (bytesStoreLiteSetMappedByteLongDataSlot I)
    (UInt256.ofNat (bytesStoreLiteSetMappedByteValueWord I).toNat)
    (bytesStoreLiteSetMappedByteLongStoredWord σ I)
    offFin (.int uint8Int) hoffBound
    (bytesStoreLiteSetMappedByteValue I) hval htarget

theorem bytesStoreLiteSetMappedByteBodyReturns {evm evm' : EVM.State}
    {I : ExecutionEnv} {ret : Value}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hassign :
      assignStorageRef? bytesStoreLiteConfig
        (bytesStoreLiteSetMappedByteFrame I)
        evm .storage (mappedByteRef (.var "key") (.var "byteIndex"))
          (bytesStoreLiteSetMappedByteValue I) =
          .ok (bytesStoreLiteSetMappedByteFrame I, evm'))
    (hret :
      evalExpr? bytesStoreLiteConfig
        (bytesStoreLiteSetMappedByteFrame I)
        evm' (.storage (mappedByteRef (.var "key") (.var "byteIndex"))) = .ok ret) :
    ExecTransitionBody bytesStoreLiteConfig bytesStoreLiteContract evm
      (bytesStoreLiteSetMappedByteLocals I) setMappedByteTransition.body
      (.returned
        (bytesStoreLiteSetMappedByteFrame I)
        evm' (some ret)) := by
  let solm : Frame := bytesStoreLiteSetMappedByteFrame I
  have hvalue :
      evalExpr? bytesStoreLiteConfig solm evm (.var "value") =
        .ok (bytesStoreLiteSetMappedByteValue I) := by
    simp [solm, bytesStoreLiteSetMappedByteFrame, bytesStoreLiteSetMappedByteValue,
      bytesStoreLiteSetMappedByteLocals, evalExpr?, EvalResult.ofOption]
  have hassign :
      assignStorageRef? bytesStoreLiteConfig solm evm .storage
        (mappedByteRef (.var "key") (.var "byteIndex"))
          (bytesStoreLiteSetMappedByteValue I) =
          .ok (solm, evm') := by
    simpa [solm] using hassign
  have hret :
      evalExpr? bytesStoreLiteConfig solm evm'
        (.storage (mappedByteRef (.var "key") (.var "byteIndex"))) = .ok ret := by
    simpa [solm] using hret
  exact ExecFuncBody.execBlockRet <|
    ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consNormal (ExecStmt.assign hvalue hassign) <|
        ExecBlock.consReturn (ExecStmt.return hret)

theorem bytesStoreLiteSetMappedByteResolveOfLength {evm : EVM.State}
    {I : ExecutionEnv} {len : Nat}
    (hlen : readStorageBytesLength? bytesStoreLiteConfig evm
      (bytesStoreLiteSetMappedByteHeaderRef I) = .ok len)
    (hbound : (bytesStoreLiteSetMappedByteIndexWord I).toNat < len) :
    resolveStorageRef? bytesStoreLiteConfig
      (bytesStoreLiteSetMappedByteFrame I)
      evm (mappedByteRef (.var "key") (.var "byteIndex")) =
        .ok (bytesStoreLiteSetMappedByteRef I, uint8St) := by
  have hgetKey :
      (bytesStoreLiteSetMappedByteLocals I).get? "key" =
        some (.int (Int.ofNat (bytesStoreLiteSetMappedByteKeyWord I).toNat)) := by
    rw [bytesStoreLiteSetMappedByteLocals]
    rw [store_get_ne (h := by decide)]
    rw [store_get_ne (h := by decide)]
    exact store_get_self (∅ : Store) "key"
      (.int (Int.ofNat (bytesStoreLiteSetMappedByteKeyWord I).toNat))
  have hgetKeyElem :
      (bytesStoreLiteSetMappedByteLocals I)["key"]? =
        some (.int (Int.ofNat (bytesStoreLiteSetMappedByteKeyWord I).toNat)) := by
    simpa [Std.HashMap.get?_eq_getElem?] using hgetKey
  have hgetByteIndex :
      (bytesStoreLiteSetMappedByteLocals I).get? "byteIndex" =
        some (.int (Int.ofNat (bytesStoreLiteSetMappedByteIndexWord I).toNat)) := by
    rw [bytesStoreLiteSetMappedByteLocals]
    rw [store_get_ne (h := by decide)]
    exact store_get_self ((∅ : Store).insert "key"
      (.int (Int.ofNat (bytesStoreLiteSetMappedByteKeyWord I).toNat))) "byteIndex"
      (.int (Int.ofNat (bytesStoreLiteSetMappedByteIndexWord I).toNat))
  have hgetByteIndexElem :
      (bytesStoreLiteSetMappedByteLocals I)["byteIndex"]? =
        some (.int (Int.ofNat (bytesStoreLiteSetMappedByteIndexWord I).toNat)) := by
    simpa [Std.HashMap.get?_eq_getElem?] using hgetByteIndex
  have hgetMapped :
      (bytesStoreLiteSetMappedByteLocals I).get? "mapped" = none := by
    rw [bytesStoreLiteSetMappedByteLocals]
    rw [store_get_ne (h := by decide)]
    rw [store_get_ne (h := by decide)]
    rw [store_get_ne (h := by decide)]
    simp
  have hlen' :
      readStorageBytesLength?
        { storage :=
            { layout := bytesStoreLiteLayout
              readValue? := solidityReadValue? bytesStoreLiteLayout
              writeValue? := solidityWriteValue? bytesStoreLiteLayout
              clearValue? := solidityClearValue? bytesStoreLiteLayout
              readBytesLength := solidityReadBytesLength? bytesStoreLiteLayout }
          externalABI := defaultExternalCallABI
          selfDeployment := genSolidityConstructorDeployment [] }
        evm
        { base := "mapped"
          steps := [
            .mindex (.int ((bytesStoreLiteSetMappedByteKeyWord I).toNat : Int))] } =
        .ok len := by
    simpa [bytesStoreLiteConfig, bytesStoreLiteStorageLayout, solidityStorageLayout,
      bytesStoreLiteSetMappedByteHeaderRef] using hlen
  have her :
      evalStorageRef bytesStoreLiteConfig
        (bytesStoreLiteSetMappedByteFrame I)
        evm (mappedByteRef (.var "key") (.var "byteIndex")) =
          .ok (bytesStoreLiteSetMappedByteRef I) := by
    simp [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, evalExpr?, mappedByteRef,
      bytesStoreLiteSetMappedByteFrame, bytesStoreLiteSetMappedByteRef,
      hgetKeyElem, hgetByteIndexElem,
      valueToKey?, EvalResult.ofOption, EvalResult.bind, bind, pure,
      arrayIndexInBounds?, storageTypeAt?, bytesStoreLiteConfig, bytesStoreLiteContract,
      storageDecls, storageTypeStep?, bytesSt, bytesStoreLiteStorageLayout, solidityStorageLayout,
      bytesStoreLiteLayout]
    rw [hlen']
    simp [hbound]
  have herInline :
      evalStorageRef bytesStoreLiteConfig
        { contract := bytesStoreLiteContract, locals := bytesStoreLiteSetMappedByteLocals I }
        evm (mappedByteRef (.var "key") (.var "byteIndex")) =
          .ok (bytesStoreLiteSetMappedByteRef I) := by
    simpa [bytesStoreLiteSetMappedByteFrame] using her
  let sourceRef : StorageRef :=
    { base := "mapped"
      steps := [.mindex (.var "key"), .aindex (.var "byteIndex")] }
  have herInline' :
      evalStorageRef bytesStoreLiteConfig
        ({ contract := bytesStoreLiteContract, locals := bytesStoreLiteSetMappedByteLocals I } :
          Frame)
        evm sourceRef =
          .ok (bytesStoreLiteSetMappedByteRef I) := by
    simpa [sourceRef, mappedByteRef] using herInline
  rw [resolveStorageRef?]
  simp only [mappedByteRef, bytesStoreLiteSetMappedByteFrame, hgetMapped]
  rw [herInline']
  simp [bytesStoreLiteSetMappedByte_storageTypeAt, EvalResult.ofOption, EvalResult.bind, bind,
    pure]

theorem bytesStoreLiteSetMappedByteAssignOfLength {evm evm' : EVM.State}
    {I : ExecutionEnv} {len : Nat}
    (hlen : readStorageBytesLength? bytesStoreLiteConfig evm
      (bytesStoreLiteSetMappedByteHeaderRef I) = .ok len)
    (hbound : (bytesStoreLiteSetMappedByteIndexWord I).toNat < len)
    (hstore :
      (match bytesStoreLiteConfig.storage.layout (bytesStoreLiteSetMappedByteRef I) evm with
      | some loc => storageLocStore evm loc (bytesStoreLiteSetMappedByteValue I)
      | none => none) = some evm') :
    assignStorageRef? bytesStoreLiteConfig
      (bytesStoreLiteSetMappedByteFrame I)
      evm .storage (mappedByteRef (.var "key") (.var "byteIndex"))
        (bytesStoreLiteSetMappedByteValue I) =
        .ok (bytesStoreLiteSetMappedByteFrame I, evm') := by
  rw [assignStorageRef?]
  rw [bytesStoreLiteSetMappedByteResolveOfLength (I := I) hlen hbound]
  cases hloc : bytesStoreLiteConfig.storage.layout (bytesStoreLiteSetMappedByteRef I) evm with
  | none =>
      simp [hloc] at hstore
  | some loc =>
      have hstoreLoc :
          storageLocStore evm loc
            (.int (Int.ofNat (bytesStoreLiteSetMappedByteValueWord I).toNat)) = some evm' := by
        simpa [hloc, bytesStoreLiteSetMappedByteValue] using hstore
      have hstoreLoc' :
          storageLocStore evm loc
            (.int ((bytesStoreLiteSetMappedByteValueWord I).toNat : Int)) = some evm' := by
        simpa using hstoreLoc
      simp [bytesStoreLiteSetMappedByteValue, hloc, EvalResult.ofOption, EvalResult.bind, bind,
        pure]
      rw [hstoreLoc']

theorem bytesStoreLiteSetMappedByteShortBodyReturns
    {evm : EVM.State} {σ : AccountMap} {I : ExecutionEnv} {len : UInt256}
    {acc : Account}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hloadHeader : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (bytesStoreLiteSetMappedByteSlot I) = bytesStoreLiteSetMappedByteHeaderWord σ I)
    (hacc : evm.accountMap.find? evm.executionEnv.codeOwner = some acc)
    (hcanon : (bytesStoreLiteSetMappedByteValueWord I).toNat < EVM.twoPow 8)
    (hlen : len =
      UInt256.land (UInt256.div (bytesStoreLiteSetMappedByteHeaderWord σ I) ⟨2⟩) ⟨127⟩)
    (hshort : len.toNat < 32)
    (hbound : (bytesStoreLiteSetMappedByteIndexWord I).toNat < len.toNat)
    (hflag : UInt256.land (bytesStoreLiteSetMappedByteHeaderWord σ I) ⟨1⟩ = ⟨0⟩)
    (_hvalid : UInt256.sub (UInt256.land (bytesStoreLiteSetMappedByteHeaderWord σ I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStoreLiteSetMappedByteHeaderWord σ I) ⟨2⟩)
            ⟨127⟩) ⟨32⟩) ≠ ⟨0⟩) :
    ExecTransitionBody bytesStoreLiteConfig bytesStoreLiteContract evm
      (bytesStoreLiteSetMappedByteLocals I) setMappedByteTransition.body
      (.returned
        (bytesStoreLiteSetMappedByteFrame I)
        (Solm.EVM.storageStore evm evm.executionEnv.codeOwner
          (bytesStoreLiteSetMappedByteSlot I)
          (bytesStoreLiteSetMappedByteShortStoredWord σ I))
        (some (bytesStoreLiteSetMappedByteValue I))) := by
  let evm' := Solm.EVM.storageStore evm evm.executionEnv.codeOwner
    (bytesStoreLiteSetMappedByteSlot I)
    (bytesStoreLiteSetMappedByteShortStoredWord σ I)
  have hlenRead :
      readStorageBytesLength? bytesStoreLiteConfig evm
          (bytesStoreLiteSetMappedByteHeaderRef I) =
        .ok len.toNat := by
    have hltLen : UInt256.lt len ⟨32⟩ = ⟨1⟩ := by
      exact ult_one (by
        simpa [show (⟨32⟩ : UInt256).toNat = 32 from by decide] using hshort)
    have hvalidLen : UInt256.sub ⟨0⟩ (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩ := by
      rw [hltLen]
      native_decide
    have hloadHeaderSlot :
        Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
          (mappedValueSlot (.int ((bytesStoreLiteSetMappedByteKeyWord I).toNat : Int))) =
          bytesStoreLiteSetMappedByteHeaderWord σ I := by
      simpa [bytesStoreLiteSetMappedByteSlot, bytesStoreLiteSetMappedSlotOf] using hloadHeader
    simp [readStorageBytesLength?, storageNatResultToEval, bytesStoreLiteConfig,
      bytesStoreLiteStorageLayout, solidityStorageLayout, solidityReadBytesLength?,
      solidityDecodeBytesLengthHeader, bytesStoreLiteLayout,
      bytesStoreLiteSetMappedByteHeaderRef, hloadHeaderSlot, hflag, ← hlen,
      hvalidLen]
  have hpacked : checkBytesPacked (bytesStoreLiteSetMappedByteSlot I) evm = true :=
    checkBytesPacked_of_storageLoad_land_one_zero hloadHeader hflag
  have hidx31 : (bytesStoreLiteSetMappedByteIndexWord I).toNat < 31 :=
    bytesStoreLiteSetMappedByteIndex_lt31_of_short_bound (I := I) (len := len)
      hshort hbound
  have hlayout :
      bytesStoreLiteConfig.storage.layout (bytesStoreLiteSetMappedByteRef I) evm =
        some (uint8Loc (bytesStoreLiteSetMappedByteSlot I)
          ⟨31 - (bytesStoreLiteSetMappedByteIndexWord I).toNat, by omega⟩) :=
    bytesStoreLiteSetMappedByteLayoutShort (evm := evm) (I := I) hpacked hidx31
  have hstore :
      (match bytesStoreLiteConfig.storage.layout (bytesStoreLiteSetMappedByteRef I) evm with
      | some loc => storageLocStore evm loc (bytesStoreLiteSetMappedByteValue I)
      | none => none) = some evm' := by
    rw [hlayout]
    simpa [evm'] using
      bytesStoreLiteSetMappedByteStorageLocStoreShort
        (evm := evm) (σ := σ) (I := I) (len := len)
        hloadHeader hcanon hshort hbound
  have hassign :
      assignStorageRef? bytesStoreLiteConfig
        (bytesStoreLiteSetMappedByteFrame I)
        evm .storage (mappedByteRef (.var "key") (.var "byteIndex"))
          (bytesStoreLiteSetMappedByteValue I) =
          .ok (bytesStoreLiteSetMappedByteFrame I, evm') :=
    bytesStoreLiteSetMappedByteAssignOfLength (evm := evm) (evm' := evm') (I := I)
      hlenRead hbound hstore
  have hloadPost :
      Solm.EVM.storageLoad evm' evm'.executionEnv.codeOwner
          (bytesStoreLiteSetMappedByteSlot I) =
        bytesStoreLiteSetMappedByteShortStoredWord σ I := by
    have hloadPostOwner :
        Solm.EVM.storageLoad evm' evm.executionEnv.codeOwner
            (bytesStoreLiteSetMappedByteSlot I) =
          bytesStoreLiteSetMappedByteShortStoredWord σ I := by
      simpa [evm'] using
        storageLoad_storageStore_same_present evm evm.executionEnv.codeOwner hacc
          (bytesStoreLiteSetMappedByteSlot I)
          (bytesStoreLiteSetMappedByteShortStoredWord σ I)
    simpa [evm', storageStore_executionEnv] using hloadPostOwner
  have hflagPost :
      UInt256.land (bytesStoreLiteSetMappedByteShortStoredWord σ I) ⟨1⟩ = ⟨0⟩ := by
    rw [bytesStoreLiteSetMappedByteShortStoredWord_flag_eq
      (σ := σ) (I := I) (len := len) hshort hbound, hflag]
  have hlenPost :
      readStorageBytesLength? bytesStoreLiteConfig evm'
          (bytesStoreLiteSetMappedByteHeaderRef I) =
        .ok len.toNat := by
    have hltLen : UInt256.lt len ⟨32⟩ = ⟨1⟩ := by
      exact ult_one (by
        simpa [show (⟨32⟩ : UInt256).toNat = 32 from by decide] using hshort)
    have hvalidLen : UInt256.sub ⟨0⟩ (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩ := by
      rw [hltLen]
      native_decide
    have hlenPostWord :
        UInt256.land
            (UInt256.div (bytesStoreLiteSetMappedByteShortStoredWord σ I) ⟨2⟩) ⟨127⟩ =
          len := by
      rw [bytesStoreLiteSetMappedByteShortStoredWord_shortLen_eq
        (σ := σ) (I := I) (len := len) hshort hbound]
      exact hlen.symm
    have hloadPostSlot :
        Solm.EVM.storageLoad evm' evm'.executionEnv.codeOwner
          (mappedValueSlot (.int ((bytesStoreLiteSetMappedByteKeyWord I).toNat : Int))) =
          bytesStoreLiteSetMappedByteShortStoredWord σ I := by
      simpa [bytesStoreLiteSetMappedByteSlot, bytesStoreLiteSetMappedSlotOf] using hloadPost
    simp [readStorageBytesLength?, storageNatResultToEval, bytesStoreLiteConfig,
      bytesStoreLiteStorageLayout, solidityStorageLayout, solidityReadBytesLength?,
      solidityDecodeBytesLengthHeader, bytesStoreLiteLayout,
      bytesStoreLiteSetMappedByteHeaderRef, hloadPostSlot, hflagPost,
      hlenPostWord, hvalidLen]
  have hpackedPost : checkBytesPacked (bytesStoreLiteSetMappedByteSlot I) evm' = true :=
    checkBytesPacked_of_storageLoad_land_one_zero hloadPost hflagPost
  have hlayoutPost :
      bytesStoreLiteConfig.storage.layout (bytesStoreLiteSetMappedByteRef I) evm' =
        some (uint8Loc (bytesStoreLiteSetMappedByteSlot I)
          ⟨31 - (bytesStoreLiteSetMappedByteIndexWord I).toNat, by omega⟩) :=
    bytesStoreLiteSetMappedByteLayoutShort (evm := evm') (I := I) hpackedPost hidx31
  have hidxLe : (bytesStoreLiteSetMappedByteIndexWord I).toNat ≤ 31 := by
    omega
  have hret :
      evalExpr? bytesStoreLiteConfig
        (bytesStoreLiteSetMappedByteFrame I)
        evm' (.storage (mappedByteRef (.var "key") (.var "byteIndex"))) =
          .ok (bytesStoreLiteSetMappedByteValue I) := by
    rw [evalExpr?]
    rw [bytesStoreLiteSetMappedByteResolveOfLength
      (evm := evm') (I := I) (len := len.toNat) hlenPost hbound]
    simp only [bind, EvalResult.bind]
    rw [Solm.readStorage?.eq_def]
    rw [hlayoutPost]
    simp [uint8St]
    rw [storageLocLoad_uint8Loc_byteAt
      (slot := bytesStoreLiteSetMappedByteSlot I)
      (idx := bytesStoreLiteSetMappedByteIndexWord I)
      (off := ⟨31 - (bytesStoreLiteSetMappedByteIndexWord I).toNat, by omega⟩)
      (hoff := by rfl) (hidx := hidxLe)]
    rw [hloadPost]
    rw [bytesStoreLiteSetMappedByteShortStoredWord_byteAt
      (σ := σ) (I := I) (len := len) hcanon hshort hbound]
    simp [bytesStoreLiteSetMappedByteValue]
  simpa [evm'] using
    bytesStoreLiteSetMappedByteBodyReturns (evm := evm) (evm' := evm') (I := I)
      hwv hassign hret

theorem bytesStoreLiteSetMappedByteLongBodyReturns
    {evm : EVM.State} {σ : AccountMap} {I : ExecutionEnv} {len : UInt256}
    {acc : Account}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hloadHeader : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (bytesStoreLiteSetMappedByteSlot I) = bytesStoreLiteSetMappedByteHeaderWord σ I)
    (hloadData : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (bytesStoreLiteSetMappedByteLongDataSlot I) =
      bytesStoreLiteSetMappedByteLongOldWord σ I)
    (hacc : evm.accountMap.find? evm.executionEnv.codeOwner = some acc)
    (hcanon : (bytesStoreLiteSetMappedByteValueWord I).toNat < EVM.twoPow 8)
    (hlen : len = UInt256.div (bytesStoreLiteSetMappedByteHeaderWord σ I) ⟨2⟩)
    (hbound : (bytesStoreLiteSetMappedByteIndexWord I).toNat < len.toNat)
    (hflag : UInt256.land (bytesStoreLiteSetMappedByteHeaderWord σ I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (bytesStoreLiteSetMappedByteHeaderWord σ I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStoreLiteSetMappedByteHeaderWord σ I) ⟨2⟩) ⟨32⟩) ≠
          ⟨0⟩) :
    ExecTransitionBody bytesStoreLiteConfig bytesStoreLiteContract evm
      (bytesStoreLiteSetMappedByteLocals I) setMappedByteTransition.body
      (.returned
        (bytesStoreLiteSetMappedByteFrame I)
        (Solm.EVM.storageStore evm evm.executionEnv.codeOwner
          (bytesStoreLiteSetMappedByteLongDataSlot I)
          (bytesStoreLiteSetMappedByteLongStoredWord σ I))
        (some (bytesStoreLiteSetMappedByteValue I))) := by
  let evm' := Solm.EVM.storageStore evm evm.executionEnv.codeOwner
    (bytesStoreLiteSetMappedByteLongDataSlot I)
    (bytesStoreLiteSetMappedByteLongStoredWord σ I)
  have hvalidLen :
      UInt256.sub (UInt256.land (bytesStoreLiteSetMappedByteHeaderWord σ I) ⟨1⟩)
        (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩ := by
    simpa [hlen] using hvalid
  have hlenRead :
      readStorageBytesLength? bytesStoreLiteConfig evm
          (bytesStoreLiteSetMappedByteHeaderRef I) =
        .ok len.toNat := by
    have hloadHeaderSlot :
        Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
          (mappedValueSlot (.int ((bytesStoreLiteSetMappedByteKeyWord I).toNat : Int))) =
          bytesStoreLiteSetMappedByteHeaderWord σ I := by
      simpa [bytesStoreLiteSetMappedByteSlot, bytesStoreLiteSetMappedSlotOf] using hloadHeader
    simp [readStorageBytesLength?, storageNatResultToEval, bytesStoreLiteConfig,
      bytesStoreLiteStorageLayout, solidityStorageLayout, solidityReadBytesLength?,
      solidityDecodeBytesLengthHeader, bytesStoreLiteLayout,
      bytesStoreLiteSetMappedByteHeaderRef, hloadHeaderSlot, hflag, ← hlen,
      hvalidLen]
  have hpacked : checkBytesPacked (bytesStoreLiteSetMappedByteSlot I) evm = false :=
    checkBytesPacked_of_storageLoad_land_one_ne_zero hloadHeader hflag
  have hlayout :
      bytesStoreLiteConfig.storage.layout (bytesStoreLiteSetMappedByteRef I) evm =
        some (uint8Loc (bytesStoreLiteSetMappedByteLongDataSlot I)
          ⟨31 - (bytesStoreLiteSetMappedByteLongWordIndex I).toNat, by
            have hidx := bytesStoreLiteSetMappedByteLongWordIndex_lt32 I
            omega⟩) :=
    bytesStoreLiteSetMappedByteLayoutLong (evm := evm) (I := I) hpacked
  have hstore :
      (match bytesStoreLiteConfig.storage.layout (bytesStoreLiteSetMappedByteRef I) evm with
      | some loc => storageLocStore evm loc (bytesStoreLiteSetMappedByteValue I)
      | none => none) = some evm' := by
    rw [hlayout]
    simpa [evm'] using
      bytesStoreLiteSetMappedByteStorageLocStoreLong
        (evm := evm) (σ := σ) (I := I) hloadData hcanon
  have hassign :
      assignStorageRef? bytesStoreLiteConfig
        (bytesStoreLiteSetMappedByteFrame I)
        evm .storage (mappedByteRef (.var "key") (.var "byteIndex"))
          (bytesStoreLiteSetMappedByteValue I) =
          .ok (bytesStoreLiteSetMappedByteFrame I, evm') :=
    bytesStoreLiteSetMappedByteAssignOfLength (evm := evm) (evm' := evm') (I := I)
      hlenRead hbound hstore
  have hneHeader :
      bytesStoreLiteSetMappedByteSlot I ≠ bytesStoreLiteSetMappedByteLongDataSlot I := by
    exact (bytesStoreLiteMappedLongDataSlot_ne_header
      (bytesStoreLiteSetMappedByteKeyWord I)
      (bytesStoreLiteSetMappedByteIndexWord I)).symm
  have hloadHeaderPost :
      Solm.EVM.storageLoad evm' evm'.executionEnv.codeOwner
          (bytesStoreLiteSetMappedByteSlot I) =
        bytesStoreLiteSetMappedByteHeaderWord σ I := by
    simpa [evm', storageStore_executionEnv] using
      (by
        rw [storageLoad_storageStore_ne evm evm.executionEnv.codeOwner hneHeader]
        exact hloadHeader)
  have hlenPost :
      readStorageBytesLength? bytesStoreLiteConfig evm'
          (bytesStoreLiteSetMappedByteHeaderRef I) =
        .ok len.toNat := by
    have hloadHeaderPostSlot :
        Solm.EVM.storageLoad evm' evm'.executionEnv.codeOwner
          (mappedValueSlot (.int ((bytesStoreLiteSetMappedByteKeyWord I).toNat : Int))) =
          bytesStoreLiteSetMappedByteHeaderWord σ I := by
      simpa [bytesStoreLiteSetMappedByteSlot, bytesStoreLiteSetMappedSlotOf] using
        hloadHeaderPost
    simp [readStorageBytesLength?, storageNatResultToEval, bytesStoreLiteConfig,
      bytesStoreLiteStorageLayout, solidityStorageLayout, solidityReadBytesLength?,
      solidityDecodeBytesLengthHeader, bytesStoreLiteLayout,
      bytesStoreLiteSetMappedByteHeaderRef, hloadHeaderPostSlot, hflag, ← hlen,
      hvalidLen]
  have hpackedPost : checkBytesPacked (bytesStoreLiteSetMappedByteSlot I) evm' = false :=
    checkBytesPacked_of_storageLoad_land_one_ne_zero hloadHeaderPost hflag
  have hlayoutPost :
      bytesStoreLiteConfig.storage.layout (bytesStoreLiteSetMappedByteRef I) evm' =
        some (uint8Loc (bytesStoreLiteSetMappedByteLongDataSlot I)
          ⟨31 - (bytesStoreLiteSetMappedByteLongWordIndex I).toNat, by
            have hidx := bytesStoreLiteSetMappedByteLongWordIndex_lt32 I
            omega⟩) :=
    bytesStoreLiteSetMappedByteLayoutLong (evm := evm') (I := I) hpackedPost
  have hloadDataPost :
      Solm.EVM.storageLoad evm' evm'.executionEnv.codeOwner
          (bytesStoreLiteSetMappedByteLongDataSlot I) =
        bytesStoreLiteSetMappedByteLongStoredWord σ I := by
    simpa [evm', storageStore_executionEnv] using
      storageLoad_storageStore_same_present evm evm.executionEnv.codeOwner hacc
        (bytesStoreLiteSetMappedByteLongDataSlot I)
        (bytesStoreLiteSetMappedByteLongStoredWord σ I)
  have hret :
      evalExpr? bytesStoreLiteConfig
        (bytesStoreLiteSetMappedByteFrame I)
        evm' (.storage (mappedByteRef (.var "key") (.var "byteIndex"))) =
          .ok (bytesStoreLiteSetMappedByteValue I) := by
    rw [evalExpr?]
    rw [bytesStoreLiteSetMappedByteResolveOfLength
      (evm := evm') (I := I) (len := len.toNat) hlenPost hbound]
    simp only [bind, EvalResult.bind]
    rw [Solm.readStorage?.eq_def]
    rw [hlayoutPost]
    simp [uint8St]
    rw [storageLocLoad_uint8Loc_byteAt
      (evm := evm') (slot := bytesStoreLiteSetMappedByteLongDataSlot I)
      (idx := bytesStoreLiteSetMappedByteLongWordIndex I)
      (off := ⟨31 - (bytesStoreLiteSetMappedByteLongWordIndex I).toNat, by
        have hidx := bytesStoreLiteSetMappedByteLongWordIndex_lt32 I
        omega⟩)
      (by rfl)
      (by
        have hidx := bytesStoreLiteSetMappedByteLongWordIndex_lt32 I
        omega)]
    rw [hloadDataPost]
    rw [bytesStoreLiteSetMappedByteLongStoredWord_byteAt (σ := σ) (I := I) hcanon]
    simp [bytesStoreLiteSetMappedByteValue]
  simpa [evm'] using
    bytesStoreLiteSetMappedByteBodyReturns (evm := evm) (evm' := evm') (I := I)
      hwv hassign hret

private theorem bytesStoreLiteSetMappedByteDecodeLenCheckOk {sz : ℕ}
    (hlen : 100 ≤ sz) (hhi : sz < 2 ^ 255 + 4) (hsz : sz < UInt256.size) :
    UInt256.slt (UInt256.sub (UInt256.ofNat sz) ⟨4⟩) ⟨96⟩ = ⟨0⟩ := by
  exact solcCalldataStaticLenCheckOk (words := 3) (by simpa using hlen) hhi hsz

private theorem bytesStoreLiteSetMappedByteDecodeLenCheckShort {sz : ℕ}
    (hhead : 4 ≤ sz) (hshort : sz < 100) (hsz : sz < UInt256.size) :
    UInt256.slt (UInt256.sub (UInt256.ofNat sz) ⟨4⟩) ⟨96⟩ = ⟨1⟩ := by
  exact solcCalldataStaticLenCheckShort (words := 3) hhead (by simpa using hshort) hsz
    (by norm_num)

private theorem bytesStoreLiteSetMappedByteDecodeLenCheckHuge {sz : ℕ}
    (hbig : 2 ^ 255 + 4 ≤ sz) (hsz : sz < UInt256.size) :
    UInt256.slt (UInt256.sub (UInt256.ofNat sz) ⟨4⟩) ⟨96⟩ = ⟨1⟩ := by
  exact solcCalldataStaticLenCheckHuge (words := 3) hbig hsz (by norm_num)

theorem bytesStoreLiteSetMappedByteSelector_size {I : ExecutionEnv}
    (hsel : selIs I ⟨#[0x13, 0x2f, 0xa3, 0x46]⟩) :
    4 ≤ I.calldata.size := by
  have hs := byteArray_size_eq_of_beq hsel
  have hleft : (⟨#[0x13, 0x2f, 0xa3, 0x46]⟩ : ByteArray).size = 4 := rfl
  rw [hleft, ByteArray.size_extract] at hs
  omega

theorem bytesStoreLiteX_setMappedByteDecodeValid {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨319⟩ [bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hsz100 : 100 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hsize : I.calldata.size < UInt256.size)
    (hcanon : UInt256.land (bytesStoreLiteSetMappedByteValueWord I) ⟨255⟩ =
      bytesStoreLiteSetMappedByteValueWord I) :
    ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨772⟩
      [bytesStoreLiteSetMappedByteValueWord I, bytesStoreLiteSetMappedByteIndexWord I,
        bytesStoreLiteSetMappedByteKeyWord I, ⟨301⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd319⟩ := hreach
  have hslt :
      UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨96⟩ = ⟨0⟩ :=
    bytesStoreLiteSetMappedByteDecodeLenCheckOk hsz100 hhi hsize
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
      bytesStoreLiteSetMappedByteKeyWord I from rfl,
    show (⟨4⟩ + ⟨32⟩ : UInt256) = ⟨36⟩ from by native_decide,
    show (⟨4⟩ + ⟨64⟩ : UInt256) = ⟨68⟩ from by native_decide] at rd1946
  have rd1950 := evm_run rd1946 with [
    jumpdest, dup1, calldataload]
  rw [show (⟨68⟩ : UInt256).toNat = 68 from by decide,
    show uInt256OfByteArray (I.calldata.readBytes 68 32) =
      bytesStoreLiteSetMappedByteValueWord I from rfl] at rd1950
  have rd2050 := evm_run rd1950 with [
    push1 ⟨255⟩, dup2, and, dup2, eq,
    push2 ⟨1962⟩,
    jumpiT (by rw [bytesStoreLiteSetPacketByteUint8CanonEqGuard hcanon]; decide)
      (by native_decide),
    jumpdest, swap2, swap1, pop, jump (by native_decide)]
  exact ⟨_, _, evm_run rd2050 with [
    jumpdest, swap1, pop, swap3, pop, swap3, pop, swap3, jump (by native_decide),
    jumpdest, push2 ⟨772⟩, jump (by native_decide)]⟩

theorem bytesStoreLiteX_setMappedByteDecodeShort {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨319⟩ [bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 100)
    (hsize : I.calldata.size < UInt256.size) :
    RDrev bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd319⟩ := hreach
  have hslt :
      UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨96⟩ = ⟨1⟩ :=
    bytesStoreLiteSetMappedByteDecodeLenCheckShort hsz4 hshort hsize
  have rd2009 := evm_run rd319 with [
    jumpdest, push2 ⟨301⟩, push2 ⟨333⟩, calldatasize, push1 ⟨4⟩,
    push2 ⟨2009⟩, jump (by native_decide)]
  exact evm_run rd2009 with [
    jumpdest, push0, push0, push0, push1 ⟨96⟩, dup5, dup7, sub, slt, iszero,
    push2 ⟨2027⟩, jumpiNT (by rw [hslt]; decide),
    raw revertStub (by native_decide) (by native_decide) (by native_decide) (by evm_ov)]

theorem bytesStoreLiteX_setMappedByteDecodeHuge {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨319⟩ [bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size) :
    RDrev bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd319⟩ := hreach
  have hslt :
      UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨96⟩ = ⟨1⟩ :=
    bytesStoreLiteSetMappedByteDecodeLenCheckHuge hbig hsize
  have rd2009 := evm_run rd319 with [
    jumpdest, push2 ⟨301⟩, push2 ⟨333⟩, calldatasize, push1 ⟨4⟩,
    push2 ⟨2009⟩, jump (by native_decide)]
  exact evm_run rd2009 with [
    jumpdest, push0, push0, push0, push1 ⟨96⟩, dup5, dup7, sub, slt, iszero,
    push2 ⟨2027⟩, jumpiNT (by rw [hslt]; decide),
    raw revertStub (by native_decide) (by native_decide) (by native_decide) (by evm_ov)]

theorem bytesStoreLiteX_setMappedByteDecodeNoncanonValue {cA gh bl σ σ₀ A I}
    {g : Sat256}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨319⟩ [bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hsz100 : 100 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hsize : I.calldata.size < UInt256.size)
    (hnc : UInt256.land (bytesStoreLiteSetMappedByteValueWord I) ⟨255⟩ ≠
      bytesStoreLiteSetMappedByteValueWord I) :
    RDrev bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd319⟩ := hreach
  have hslt :
      UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨96⟩ = ⟨0⟩ :=
    bytesStoreLiteSetMappedByteDecodeLenCheckOk hsz100 hhi hsize
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
      bytesStoreLiteSetMappedByteKeyWord I from rfl,
    show (⟨4⟩ + ⟨32⟩ : UInt256) = ⟨36⟩ from by native_decide,
    show (⟨4⟩ + ⟨64⟩ : UInt256) = ⟨68⟩ from by native_decide] at rd1946
  have rd1950 := evm_run rd1946 with [
    jumpdest, dup1, calldataload]
  rw [show (⟨68⟩ : UInt256).toNat = 68 from by decide,
    show uInt256OfByteArray (I.calldata.readBytes 68 32) =
      bytesStoreLiteSetMappedByteValueWord I from rfl] at rd1950
  exact evm_run rd1950 with [
    push1 ⟨255⟩, dup2, and, dup2, eq,
    push2 ⟨1962⟩,
    jumpiNT (by rw [bytesStoreLiteSetPacketByteUint8NoncanonEqGuard hnc]),
    raw revertStub (by native_decide) (by native_decide) (by native_decide) (by evm_ov)]

theorem bytesStoreLiteX_setMappedByteReachLengthDecoder {cA gh bl σ σ₀ A I}
    {g : Sat256}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨772⟩
      [bytesStoreLiteSetMappedByteValueWord I, bytesStoreLiteSetMappedByteIndexWord I,
        bytesStoreLiteSetMappedByteKeyWord I, ⟨301⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2246⟩
      [bytesStoreLiteSetMappedByteHeaderWord σ I, ⟨805⟩,
        bytesStoreLiteSetMappedByteIndexWord I, bytesStoreLiteSetMappedByteSlot I,
        UInt256.shiftLeft (bytesStoreLiteSetMappedByteValueWord I) ⟨248⟩, ⟨0⟩,
        bytesStoreLiteSetMappedByteValueWord I, bytesStoreLiteSetMappedByteIndexWord I,
        bytesStoreLiteSetMappedByteKeyWord I, ⟨301⟩, bytesStoreLiteSelWord I]
      (twoWordHashMem (bytesStoreLiteSetMappedByteKeyWord I) ⟨4⟩ solcFreePtrMem)
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd772⟩ := hreach
  have hslot := bytesStoreLiteSetMappedByteSlotHash I
  have rd788 := evm_run rd772 with [
    jumpdest, push0, dup4, dup2,
    raw mstore 0 (wordAt0Mem (bytesStoreLiteSetMappedByteKeyWord I) solcFreePtrMem)
      (UInt256.ofNat 3) (by native_decide)
      mem_cost
      (by rfl)
      (by native_decide) (by evm_ov),
    push1 ⟨4⟩, push1 ⟨32⟩,
    raw mstore 0
      (twoWordHashMem (bytesStoreLiteSetMappedByteKeyWord I) ⟨4⟩ solcFreePtrMem)
      (UInt256.ofNat 3) (by native_decide)
      mem_cost
      (by rfl)
      (by native_decide) (by evm_ov),
    push1 ⟨64⟩, dup2,
    raw keccak256 0 (bytesStoreLiteSetMappedByteSlot I) (UInt256.ofNat 3)
      (by native_decide) mem_cost hslot (by native_decide) (by evm_ov),
    dup1]
  obtain ⟨_, _, rd788₀⟩ := rd788.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd788'⟩ :
      ∃ k C, RD bytesStoreLiteBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨788⟩
        [bytesStoreLiteSetMappedByteHeaderWord σ I, bytesStoreLiteSetMappedByteSlot I,
          ⟨0⟩, bytesStoreLiteSetMappedByteValueWord I, bytesStoreLiteSetMappedByteIndexWord I,
          bytesStoreLiteSetMappedByteKeyWord I, ⟨301⟩, bytesStoreLiteSelWord I]
        (twoWordHashMem (bytesStoreLiteSetMappedByteKeyWord I) ⟨4⟩ solcFreePtrMem)
        (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by
      simpa [bytesStoreLiteSetMappedByteHeaderWord, initState] using rd788₀⟩
  exact ⟨_, _, evm_run rd788' with [
    push1 ⟨248⟩, dup5, swap1, shl, swap2, swap1, dup6, swap1,
    push2 ⟨805⟩, swap1, push2 ⟨2246⟩, jump (by native_decide)]⟩

theorem bytesStoreLiteX_setMappedByteOobAfterLength {cA gh bl σ σ₀ A I}
    {g : Sat256} {len : UInt256}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨805⟩
      [len, bytesStoreLiteSetMappedByteIndexWord I, bytesStoreLiteSetMappedByteSlot I,
        UInt256.shiftLeft (bytesStoreLiteSetMappedByteValueWord I) ⟨248⟩, ⟨0⟩,
        bytesStoreLiteSetMappedByteValueWord I, bytesStoreLiteSetMappedByteIndexWord I,
        bytesStoreLiteSetMappedByteKeyWord I, ⟨301⟩, bytesStoreLiteSelWord I]
      (twoWordHashMem (bytesStoreLiteSetMappedByteKeyWord I) ⟨4⟩ solcFreePtrMem)
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hbound : ¬ (bytesStoreLiteSetMappedByteIndexWord I).toNat < len.toNat) :
    RDrev bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd805⟩ := hreach
  have hlt : UInt256.lt (bytesStoreLiteSetMappedByteIndexWord I) len = ⟨0⟩ :=
    ult_zero (by omega)
  have rd2579 := evm_run rd805 with [
    jumpdest, dup2, lt, push2 ⟨819⟩,
    jumpiNT (by simpa using hlt),
    push2 ⟨819⟩, push2 ⟨2579⟩, jump (by native_decide)]
  exact bytesStoreLiteX_panic32Mem ⟨_, _, rd2579⟩
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem bytesStoreLiteX_setMappedByteOobLong {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨772⟩
      [bytesStoreLiteSetMappedByteValueWord I, bytesStoreLiteSetMappedByteIndexWord I,
        bytesStoreLiteSetMappedByteKeyWord I, ⟨301⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hflag : UInt256.land (bytesStoreLiteSetMappedByteHeaderWord σ I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (bytesStoreLiteSetMappedByteHeaderWord σ I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStoreLiteSetMappedByteHeaderWord σ I) ⟨2⟩) ⟨32⟩) ≠
      ⟨0⟩)
    (hbound :
      ¬ (bytesStoreLiteSetMappedByteIndexWord I).toNat <
        (UInt256.div (bytesStoreLiteSetMappedByteHeaderWord σ I) ⟨2⟩).toNat) :
    RDrev bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hdec := bytesStoreLiteX_setMappedByteReachLengthDecoder hreach
  have hlen := bytesStoreLiteX_bytesLengthDecoderLongValidMem
    (A := A) (I := I) (g := g) hdec hflag hvalid (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  exact bytesStoreLiteX_setMappedByteOobAfterLength (g := g) hlen hbound

theorem bytesStoreLiteX_setMappedByteOobShort {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨772⟩
      [bytesStoreLiteSetMappedByteValueWord I, bytesStoreLiteSetMappedByteIndexWord I,
        bytesStoreLiteSetMappedByteKeyWord I, ⟨301⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hflag : UInt256.land (bytesStoreLiteSetMappedByteHeaderWord σ I) ⟨1⟩ = ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (bytesStoreLiteSetMappedByteHeaderWord σ I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStoreLiteSetMappedByteHeaderWord σ I) ⟨2⟩)
            ⟨127⟩) ⟨32⟩) ≠ ⟨0⟩)
    (hbound :
      ¬ (bytesStoreLiteSetMappedByteIndexWord I).toNat <
        (UInt256.land (UInt256.div (bytesStoreLiteSetMappedByteHeaderWord σ I) ⟨2⟩)
          ⟨127⟩).toNat) :
    RDrev bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hdec := bytesStoreLiteX_setMappedByteReachLengthDecoder hreach
  have hlen := bytesStoreLiteX_bytesLengthDecoderShortValidMem
    (A := A) (I := I) (g := g) hdec hflag hvalid (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  exact bytesStoreLiteX_setMappedByteOobAfterLength (g := g) hlen hbound

theorem bytesStoreLiteX_setMappedByteLongMalformed {cA gh bl σ σ₀ A I}
    {g : Sat256}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨772⟩
      [bytesStoreLiteSetMappedByteValueWord I, bytesStoreLiteSetMappedByteIndexWord I,
        bytesStoreLiteSetMappedByteKeyWord I, ⟨301⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hflag : UInt256.land (bytesStoreLiteSetMappedByteHeaderWord σ I) ⟨1⟩ ≠ ⟨0⟩)
    (hbad : UInt256.sub (UInt256.land (bytesStoreLiteSetMappedByteHeaderWord σ I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStoreLiteSetMappedByteHeaderWord σ I) ⟨2⟩) ⟨32⟩) =
      ⟨0⟩) :
    RDrev bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I) := by
  exact bytesStoreLiteX_bytesLengthDecoderLongMalformedMem
    (bytesStoreLiteX_setMappedByteReachLengthDecoder hreach) hflag hbad
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem bytesStoreLiteX_setMappedByteShortMalformed {cA gh bl σ σ₀ A I}
    {g : Sat256}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨772⟩
      [bytesStoreLiteSetMappedByteValueWord I, bytesStoreLiteSetMappedByteIndexWord I,
        bytesStoreLiteSetMappedByteKeyWord I, ⟨301⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hflag : UInt256.land (bytesStoreLiteSetMappedByteHeaderWord σ I) ⟨1⟩ = ⟨0⟩)
    (hbad : UInt256.sub (UInt256.land (bytesStoreLiteSetMappedByteHeaderWord σ I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStoreLiteSetMappedByteHeaderWord σ I) ⟨2⟩)
            ⟨127⟩) ⟨32⟩) = ⟨0⟩) :
    RDrev bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I) := by
  exact bytesStoreLiteX_bytesLengthDecoderShortMalformedMem
    (bytesStoreLiteX_setMappedByteReachLengthDecoder hreach) hflag hbad
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem bytesStoreLiteSetMappedByteResolveRevertsOfLength {evm : EVM.State}
    {I : ExecutionEnv} {len : Nat}
    (hlen : readStorageBytesLength? bytesStoreLiteConfig evm
      (bytesStoreLiteSetMappedByteHeaderRef I) = .ok len)
    (hbound : ¬ (bytesStoreLiteSetMappedByteIndexWord I).toNat < len) :
    resolveStorageRef? bytesStoreLiteConfig
      (bytesStoreLiteSetMappedByteFrame I) evm
      (mappedByteRef (.var "key") (.var "byteIndex")) = .revert := by
  have hgetKey :
      (bytesStoreLiteSetMappedByteLocals I).get? "key" =
        some (.int (Int.ofNat (bytesStoreLiteSetMappedByteKeyWord I).toNat)) := by
    rw [bytesStoreLiteSetMappedByteLocals]
    rw [store_get_ne (h := by decide)]
    rw [store_get_ne (h := by decide)]
    exact store_get_self (∅ : Store) "key"
      (.int (Int.ofNat (bytesStoreLiteSetMappedByteKeyWord I).toNat))
  have hgetKeyElem :
      (bytesStoreLiteSetMappedByteLocals I)["key"]? =
        some (.int (Int.ofNat (bytesStoreLiteSetMappedByteKeyWord I).toNat)) := by
    simpa [Std.HashMap.get?_eq_getElem?] using hgetKey
  have hgetByteIndex :
      (bytesStoreLiteSetMappedByteLocals I).get? "byteIndex" =
        some (.int (Int.ofNat (bytesStoreLiteSetMappedByteIndexWord I).toNat)) := by
    rw [bytesStoreLiteSetMappedByteLocals]
    rw [store_get_ne (h := by decide)]
    exact store_get_self ((∅ : Store).insert "key"
      (.int (Int.ofNat (bytesStoreLiteSetMappedByteKeyWord I).toNat))) "byteIndex"
      (.int (Int.ofNat (bytesStoreLiteSetMappedByteIndexWord I).toNat))
  have hgetByteIndexElem :
      (bytesStoreLiteSetMappedByteLocals I)["byteIndex"]? =
        some (.int (Int.ofNat (bytesStoreLiteSetMappedByteIndexWord I).toNat)) := by
    simpa [Std.HashMap.get?_eq_getElem?] using hgetByteIndex
  have hgetMapped :
      (bytesStoreLiteSetMappedByteLocals I).get? "mapped" = none := by
    rw [bytesStoreLiteSetMappedByteLocals]
    rw [store_get_ne (h := by decide)]
    rw [store_get_ne (h := by decide)]
    rw [store_get_ne (h := by decide)]
    simp
  have hlen' :
      readStorageBytesLength?
        { storage :=
            { layout := bytesStoreLiteLayout
              readValue? := solidityReadValue? bytesStoreLiteLayout
              writeValue? := solidityWriteValue? bytesStoreLiteLayout
              clearValue? := solidityClearValue? bytesStoreLiteLayout
              readBytesLength := solidityReadBytesLength? bytesStoreLiteLayout }
          externalABI := defaultExternalCallABI
          selfDeployment := genSolidityConstructorDeployment [] }
        evm
        { base := "mapped"
          steps := [
            .mindex (.int ((bytesStoreLiteSetMappedByteKeyWord I).toNat : Int))] } =
        .ok len := by
    simpa [bytesStoreLiteConfig, bytesStoreLiteStorageLayout, solidityStorageLayout,
      bytesStoreLiteSetMappedByteHeaderRef] using hlen
  have her :
      evalStorageRef bytesStoreLiteConfig
        (bytesStoreLiteSetMappedByteFrame I)
        evm (mappedByteRef (.var "key") (.var "byteIndex")) = .revert := by
    simp [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, evalExpr?, mappedByteRef,
      bytesStoreLiteSetMappedByteFrame, hgetKeyElem, hgetByteIndexElem,
      valueToKey?, EvalResult.ofOption, EvalResult.bind, bind, pure,
      arrayIndexInBounds?, storageTypeAt?, bytesStoreLiteConfig, bytesStoreLiteContract,
      storageDecls, storageTypeStep?, bytesSt, bytesStoreLiteStorageLayout, solidityStorageLayout,
      bytesStoreLiteLayout]
    rw [hlen']
    simp [hbound]
  have herInline :
      evalStorageRef bytesStoreLiteConfig
        { contract := bytesStoreLiteContract, locals := bytesStoreLiteSetMappedByteLocals I }
        evm (mappedByteRef (.var "key") (.var "byteIndex")) = .revert := by
    simpa [bytesStoreLiteSetMappedByteFrame] using her
  rw [resolveStorageRef?]
  simp only [mappedByteRef, bytesStoreLiteSetMappedByteFrame, hgetMapped]
  change (match evalStorageRef bytesStoreLiteConfig
      { contract := bytesStoreLiteContract, locals := bytesStoreLiteSetMappedByteLocals I }
      evm (mappedByteRef (.var "key") (.var "byteIndex")) with
    | .ok er => do
        let ty ← EvalResult.ofOption EvalError.storageError
          (storageTypeAt? bytesStoreLiteContract.storage er)
        pure (er, ty)
    | .revert => .revert
    | .error e => .error e) = .revert
  rw [herInline]

theorem bytesStoreLiteSetMappedByteBodyBoundsRevertsOfLength {evm : EVM.State}
    {I : ExecutionEnv} {len : Nat}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hlen : readStorageBytesLength? bytesStoreLiteConfig evm
      (bytesStoreLiteSetMappedByteHeaderRef I) = .ok len)
    (hbound : ¬ (bytesStoreLiteSetMappedByteIndexWord I).toNat < len) :
    ExecTransitionBody bytesStoreLiteConfig bytesStoreLiteContract evm
      (bytesStoreLiteSetMappedByteLocals I) setMappedByteTransition.body .reverted := by
  let solm : Frame := bytesStoreLiteSetMappedByteFrame I
  have hvalue :
      evalExpr? bytesStoreLiteConfig solm evm (.var "value") =
        .ok (bytesStoreLiteSetMappedByteValue I) := by
    simp [solm, bytesStoreLiteSetMappedByteFrame, bytesStoreLiteSetMappedByteValue,
      bytesStoreLiteSetMappedByteLocals, evalExpr?, EvalResult.ofOption]
  have hassign :
      assignStorageRef? bytesStoreLiteConfig solm evm .storage
        (mappedByteRef (.var "key") (.var "byteIndex"))
          (bytesStoreLiteSetMappedByteValue I) = .revert := by
    rw [assignStorageRef?]
    rw [bytesStoreLiteSetMappedByteResolveRevertsOfLength (I := I) hlen hbound]
    rfl
  exact ExecFuncBody.execBlockRevert <|
    ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consRevert (ExecStmt.assignStoreRevert hvalue hassign)

theorem bytesStoreLiteSetMappedByteResolveRevertsOfLengthRead {evm : EVM.State}
    {I : ExecutionEnv}
    (hlen : readStorageBytesLength? bytesStoreLiteConfig evm
      (bytesStoreLiteSetMappedByteHeaderRef I) = .revert) :
    resolveStorageRef? bytesStoreLiteConfig
      (bytesStoreLiteSetMappedByteFrame I) evm
      (mappedByteRef (.var "key") (.var "byteIndex")) = .revert := by
  have hgetKey :
      (bytesStoreLiteSetMappedByteLocals I).get? "key" =
        some (.int (Int.ofNat (bytesStoreLiteSetMappedByteKeyWord I).toNat)) := by
    rw [bytesStoreLiteSetMappedByteLocals]
    rw [store_get_ne (h := by decide)]
    rw [store_get_ne (h := by decide)]
    exact store_get_self (∅ : Store) "key"
      (.int (Int.ofNat (bytesStoreLiteSetMappedByteKeyWord I).toNat))
  have hgetKeyElem :
      (bytesStoreLiteSetMappedByteLocals I)["key"]? =
        some (.int (Int.ofNat (bytesStoreLiteSetMappedByteKeyWord I).toNat)) := by
    simpa [Std.HashMap.get?_eq_getElem?] using hgetKey
  have hgetByteIndex :
      (bytesStoreLiteSetMappedByteLocals I).get? "byteIndex" =
        some (.int (Int.ofNat (bytesStoreLiteSetMappedByteIndexWord I).toNat)) := by
    rw [bytesStoreLiteSetMappedByteLocals]
    rw [store_get_ne (h := by decide)]
    exact store_get_self ((∅ : Store).insert "key"
      (.int (Int.ofNat (bytesStoreLiteSetMappedByteKeyWord I).toNat))) "byteIndex"
      (.int (Int.ofNat (bytesStoreLiteSetMappedByteIndexWord I).toNat))
  have hgetByteIndexElem :
      (bytesStoreLiteSetMappedByteLocals I)["byteIndex"]? =
        some (.int (Int.ofNat (bytesStoreLiteSetMappedByteIndexWord I).toNat)) := by
    simpa [Std.HashMap.get?_eq_getElem?] using hgetByteIndex
  have hgetMapped :
      (bytesStoreLiteSetMappedByteLocals I).get? "mapped" = none := by
    rw [bytesStoreLiteSetMappedByteLocals]
    rw [store_get_ne (h := by decide)]
    rw [store_get_ne (h := by decide)]
    rw [store_get_ne (h := by decide)]
    simp
  have hlen' :
      readStorageBytesLength?
        { storage :=
            { layout := bytesStoreLiteLayout
              readValue? := solidityReadValue? bytesStoreLiteLayout
              writeValue? := solidityWriteValue? bytesStoreLiteLayout
              clearValue? := solidityClearValue? bytesStoreLiteLayout
              readBytesLength := solidityReadBytesLength? bytesStoreLiteLayout }
          externalABI := defaultExternalCallABI
          selfDeployment := genSolidityConstructorDeployment [] }
        evm
        { base := "mapped"
          steps := [
            .mindex (.int ((bytesStoreLiteSetMappedByteKeyWord I).toNat : Int))] } =
        .revert := by
    simpa [bytesStoreLiteConfig, bytesStoreLiteStorageLayout, solidityStorageLayout,
      bytesStoreLiteSetMappedByteHeaderRef] using hlen
  have her :
      evalStorageRef bytesStoreLiteConfig
        (bytesStoreLiteSetMappedByteFrame I)
        evm (mappedByteRef (.var "key") (.var "byteIndex")) = .revert := by
    simp [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, evalExpr?, mappedByteRef,
      bytesStoreLiteSetMappedByteFrame, hgetKeyElem, hgetByteIndexElem,
      valueToKey?, EvalResult.ofOption, EvalResult.bind, bind, pure,
      arrayIndexInBounds?, storageTypeAt?, bytesStoreLiteConfig, bytesStoreLiteContract,
      storageDecls, storageTypeStep?, bytesSt, bytesStoreLiteStorageLayout, solidityStorageLayout,
      bytesStoreLiteLayout]
    rw [hlen']
  have herInline :
      evalStorageRef bytesStoreLiteConfig
        { contract := bytesStoreLiteContract, locals := bytesStoreLiteSetMappedByteLocals I }
        evm (mappedByteRef (.var "key") (.var "byteIndex")) = .revert := by
    simpa [bytesStoreLiteSetMappedByteFrame] using her
  rw [resolveStorageRef?]
  simp only [mappedByteRef, bytesStoreLiteSetMappedByteFrame, hgetMapped]
  change (match evalStorageRef bytesStoreLiteConfig
      { contract := bytesStoreLiteContract, locals := bytesStoreLiteSetMappedByteLocals I }
      evm (mappedByteRef (.var "key") (.var "byteIndex")) with
    | .ok er => do
        let ty ← EvalResult.ofOption EvalError.storageError
          (storageTypeAt? bytesStoreLiteContract.storage er)
        pure (er, ty)
    | .revert => .revert
    | .error e => .error e) = .revert
  rw [herInline]

theorem bytesStoreLiteSetMappedByteBodyRevertsOfLengthRead {evm : EVM.State}
    {I : ExecutionEnv}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hlen : readStorageBytesLength? bytesStoreLiteConfig evm
      (bytesStoreLiteSetMappedByteHeaderRef I) = .revert) :
    ExecTransitionBody bytesStoreLiteConfig bytesStoreLiteContract evm
      (bytesStoreLiteSetMappedByteLocals I) setMappedByteTransition.body .reverted := by
  let solm : Frame := bytesStoreLiteSetMappedByteFrame I
  have hvalue :
      evalExpr? bytesStoreLiteConfig solm evm (.var "value") =
        .ok (bytesStoreLiteSetMappedByteValue I) := by
    simp [solm, bytesStoreLiteSetMappedByteFrame, bytesStoreLiteSetMappedByteValue,
      bytesStoreLiteSetMappedByteLocals, evalExpr?, EvalResult.ofOption]
  have hassign :
      assignStorageRef? bytesStoreLiteConfig solm evm .storage
        (mappedByteRef (.var "key") (.var "byteIndex"))
          (bytesStoreLiteSetMappedByteValue I) = .revert := by
    rw [assignStorageRef?]
    rw [bytesStoreLiteSetMappedByteResolveRevertsOfLengthRead (I := I) hlen]
    rfl
  exact ExecFuncBody.execBlockRevert <|
    ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consRevert (ExecStmt.assignStoreRevert hvalue hassign)

theorem bytesStoreLiteDecode_setMappedByte {I : ExecutionEnv}
    (hsz100 : 100 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (bytesStoreLiteSetMappedByteValueWord I).toNat < EVM.twoPow 8) :
    decodeCalldata (setMappedByteTransition.params.map Param.name)
      (transitionSignature setMappedByteTransition).paramTypes I.calldata =
        some (bytesStoreLiteSetMappedByteLocals I) := by
  show decodeCalldata ["key", "byteIndex", "value"] [uint256, uint256, uint8]
      I.calldata = some (bytesStoreLiteSetMappedByteLocals I)
  simpa [uint256, uint8, uint8Int, abiUInt256, abiUInt8,
    bytesStoreLiteSetMappedByteLocals, bytesStoreLiteSetMappedByteKeyWord,
    bytesStoreLiteSetMappedByteIndexWord, bytesStoreLiteSetMappedByteValueWord] using
    decodeCalldata_uint256_uint256_uint8_ok (cd := I.calldata) (x := "key")
      (y := "byteIndex") (z := "value") hsz100 hhi hcanon

theorem bytesStoreLiteDecode_setMappedByte_none_noncanon_value {I : ExecutionEnv}
    (hsz100 : 100 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hnc : ¬ (bytesStoreLiteSetMappedByteValueWord I).toNat < EVM.twoPow 8) :
    decodeCalldata (setMappedByteTransition.params.map Param.name)
      (transitionSignature setMappedByteTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["key", "byteIndex", "value"] [uint256, uint256, uint8]
      I.calldata = none
  simpa [uint256, uint8, uint8Int, abiUInt256, abiUInt8,
    bytesStoreLiteSetMappedByteValueWord] using
    decodeCalldata_uint256_uint256_uint8_none_noncanon2 (cd := I.calldata)
      (x := "key") (y := "byteIndex") (z := "value") hsz100 hhi hnc

theorem bytesStoreLiteDecode_setMappedByte_none_short {I : ExecutionEnv}
    (hshort : I.calldata.size < 100) :
    decodeCalldata (setMappedByteTransition.params.map Param.name)
      (transitionSignature setMappedByteTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["key", "byteIndex", "value"] [uint256, uint256, uint8]
      I.calldata = none
  simpa [uint256, uint8, uint8Int, abiUInt256, abiUInt8] using
    decodeCalldata_uint256_uint256_uint8_none_short (cd := I.calldata)
      (x := "key") (y := "byteIndex") (z := "value") hshort

theorem bytesStoreLiteDecode_setMappedByte_none_huge {I : ExecutionEnv}
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size) :
    decodeCalldata (setMappedByteTransition.params.map Param.name)
      (transitionSignature setMappedByteTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["key", "byteIndex", "value"] [uint256, uint256, uint8]
      I.calldata = none
  simpa [uint256, uint8, uint8Int, abiUInt256, abiUInt8] using
    decodeCalldata_uint256_uint256_uint8_none_huge (cd := I.calldata)
      (x := "key") (y := "byteIndex") (z := "value") hbig

theorem bytesStoreLiteSetMappedByteDecodeShortRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x13, 0x2f, 0xa3, 0x46]⟩)
    (_hAccounts : accountMapEquiv σ_evm σ_solm)
    (hshort : I.calldata.size < 100) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsz := bytesStoreLiteSetMappedByteSelector_size hsel
  have hreach := bytesStoreLiteReachSetMappedByte (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz hsize hsel
  have hreachPc : ∃ k C, RD bytesStoreLiteBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨319⟩
      [bytesStoreLiteSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ_evm) k C := by
    simpa [bytesStoreLiteSetMappedByteEntryPc] using hreach
  have hd := bytesStoreLiteDispatch_setMappedByte (cd := I.calldata)
    (by simpa [selIs] using hsel)
  have hdec := bytesStoreLiteDecode_setMappedByte_none_short (I := I) hshort
  exact (bytesStoreLiteX_setMappedByteDecodeShort
      (g := Sat256.ofUInt256 g) hreachPc hsz hshort hsize)
    |>.reEquivDecodingFailed hcode hd hdec

theorem bytesStoreLiteSetMappedByteDecodeHugeRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x13, 0x2f, 0xa3, 0x46]⟩)
    (_hAccounts : accountMapEquiv σ_evm σ_solm)
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsz := bytesStoreLiteSetMappedByteSelector_size hsel
  have hreach := bytesStoreLiteReachSetMappedByte (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz hsize hsel
  have hreachPc : ∃ k C, RD bytesStoreLiteBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨319⟩
      [bytesStoreLiteSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ_evm) k C := by
    simpa [bytesStoreLiteSetMappedByteEntryPc] using hreach
  have hd := bytesStoreLiteDispatch_setMappedByte (cd := I.calldata)
    (by simpa [selIs] using hsel)
  have hdec := bytesStoreLiteDecode_setMappedByte_none_huge (I := I) hbig
  exact (bytesStoreLiteX_setMappedByteDecodeHuge
      (g := Sat256.ofUInt256 g) hreachPc hbig hsize)
    |>.reEquivDecodingFailed hcode hd hdec

theorem bytesStoreLiteSetMappedByteDecodeNoncanonValueRuntime
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x13, 0x2f, 0xa3, 0x46]⟩)
    (_hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsz100 : 100 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hnc : ¬ (bytesStoreLiteSetMappedByteValueWord I).toNat < EVM.twoPow 8) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsz := bytesStoreLiteSetMappedByteSelector_size hsel
  have hreach := bytesStoreLiteReachSetMappedByte (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz hsize hsel
  have hreachPc : ∃ k C, RD bytesStoreLiteBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨319⟩
      [bytesStoreLiteSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ_evm) k C := by
    simpa [bytesStoreLiteSetMappedByteEntryPc] using hreach
  have hd := bytesStoreLiteDispatch_setMappedByte (cd := I.calldata)
    (by simpa [selIs] using hsel)
  have hdec := bytesStoreLiteDecode_setMappedByte_none_noncanon_value
    (I := I) hsz100 hhi hnc
  exact (bytesStoreLiteX_setMappedByteDecodeNoncanonValue
      (g := Sat256.ofUInt256 g) hreachPc hsz100 hhi hsize
      (bytesStoreLiteSetPacketByteLand255_ne_self_of_not_uint8 hnc))
    |>.reEquivDecodingFailed hcode hd hdec

theorem bytesStoreLiteSetMappedByteOobLongRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x13, 0x2f, 0xa3, 0x46]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsz100 : 100 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (bytesStoreLiteSetMappedByteValueWord I).toNat < EVM.twoPow 8)
    (hflag : UInt256.land (bytesStoreLiteSetMappedByteHeaderWord σ_evm I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (bytesStoreLiteSetMappedByteHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStoreLiteSetMappedByteHeaderWord σ_evm I) ⟨2⟩) ⟨32⟩) ≠
      ⟨0⟩)
    (hbound :
      ¬ (bytesStoreLiteSetMappedByteIndexWord I).toNat <
        (UInt256.div (bytesStoreLiteSetMappedByteHeaderWord σ_evm I) ⟨2⟩).toNat) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsz := bytesStoreLiteSetMappedByteSelector_size hsel
  have hreach := bytesStoreLiteReachSetMappedByte (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz hsize hsel
  have hreachPc : ∃ k C, RD bytesStoreLiteBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨319⟩
      [bytesStoreLiteSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ_evm) k C := by
    simpa [bytesStoreLiteSetMappedByteEntryPc] using hreach
  have hreachBody := bytesStoreLiteX_setMappedByteDecodeValid
    (g := Sat256.ofUInt256 g) hreachPc hsz100 hhi hsize
    (bytesStoreLiteSetPacketByteLand255_eq_self_of_uint8 hcanon)
  have hd := bytesStoreLiteDispatch_setMappedByte (cd := I.calldata)
    (by simpa [selIs] using hsel)
  have hdec := bytesStoreLiteDecode_setMappedByte (I := I) hsz100 hhi hcanon
  have hword :
      bytesStoreLiteSetMappedByteHeaderWord σ_evm I =
        bytesStoreLiteSetMappedByteHeaderWord σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner
      (bytesStoreLiteSetMappedByteSlot I) ⟨0⟩
  have hslot :
      (σ_solm.find? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD (bytesStoreLiteSetMappedByteSlot I) ⟨0⟩)) =
      (σ_evm.find? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD (bytesStoreLiteSetMappedByteSlot I) ⟨0⟩)) := by
    simpa [bytesStoreLiteSetMappedByteHeaderWord] using hword.symm
  have hload :
      Solm.EVM.storageLoad
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        I.codeOwner (bytesStoreLiteSetMappedByteSlot I) =
          bytesStoreLiteSetMappedByteHeaderWord σ_evm I := by
    simp [Solm.EVM.storageLoad, initState, State.lookupAccount, Account.lookupStorage,
      bytesStoreLiteSetMappedByteHeaderWord, hslot]
  have hloadMapped :
      Solm.EVM.storageLoad
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        I.codeOwner
          (mappedValueSlot
            (.int (Int.ofNat (bytesStoreLiteSetMappedByteKeyWord I).toNat))) =
          bytesStoreLiteSetMappedByteHeaderWord σ_evm I := by
    simpa [bytesStoreLiteSetMappedByteSlot, bytesStoreLiteSetMappedSlotOf] using hload
  have hloadMapped' :
      Solm.EVM.storageLoad
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        I.codeOwner
          (mappedValueSlot
            (.int ((bytesStoreLiteSetMappedByteKeyWord I).toNat : Int))) =
          bytesStoreLiteSetMappedByteHeaderWord σ_evm I := by
    simpa using hloadMapped
  have hcodeOwner :
      (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner =
        I.codeOwner := by
    rfl
  have hlen :
      readStorageBytesLength? bytesStoreLiteConfig
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (bytesStoreLiteSetMappedByteHeaderRef I) =
          .ok (UInt256.div (bytesStoreLiteSetMappedByteHeaderWord σ_evm I) ⟨2⟩).toNat := by
    simp [readStorageBytesLength?, storageNatResultToEval, bytesStoreLiteConfig,
      bytesStoreLiteStorageLayout, solidityStorageLayout, solidityReadBytesLength?,
      solidityDecodeBytesLengthHeader, bytesStoreLiteLayout,
      bytesStoreLiteSetMappedByteHeaderRef, hcodeOwner, hloadMapped', hflag, hvalid]
  have hbody :
      ExecTransitionBody bytesStoreLiteConfig bytesStoreLiteContract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (bytesStoreLiteSetMappedByteLocals I) setMappedByteTransition.body .reverted := by
    exact bytesStoreLiteSetMappedByteBodyBoundsRevertsOfLength
      (by simp only [initState]; exact hwv) hlen hbound
  exact (bytesStoreLiteX_setMappedByteOobLong
      (g := Sat256.ofUInt256 g) hreachBody hflag hvalid hbound)
    |>.reEquivExecutionRevert hcode hd hdec hbody

theorem bytesStoreLiteSetMappedByteOobShortRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x13, 0x2f, 0xa3, 0x46]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsz100 : 100 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (bytesStoreLiteSetMappedByteValueWord I).toNat < EVM.twoPow 8)
    (hflag : UInt256.land (bytesStoreLiteSetMappedByteHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (bytesStoreLiteSetMappedByteHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStoreLiteSetMappedByteHeaderWord σ_evm I) ⟨2⟩)
            ⟨127⟩) ⟨32⟩) ≠ ⟨0⟩)
    (hbound :
      ¬ (bytesStoreLiteSetMappedByteIndexWord I).toNat <
        (UInt256.land (UInt256.div (bytesStoreLiteSetMappedByteHeaderWord σ_evm I) ⟨2⟩)
          ⟨127⟩).toNat) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsz := bytesStoreLiteSetMappedByteSelector_size hsel
  have hreach := bytesStoreLiteReachSetMappedByte (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz hsize hsel
  have hreachPc : ∃ k C, RD bytesStoreLiteBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨319⟩
      [bytesStoreLiteSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ_evm) k C := by
    simpa [bytesStoreLiteSetMappedByteEntryPc] using hreach
  have hreachBody := bytesStoreLiteX_setMappedByteDecodeValid
    (g := Sat256.ofUInt256 g) hreachPc hsz100 hhi hsize
    (bytesStoreLiteSetPacketByteLand255_eq_self_of_uint8 hcanon)
  have hd := bytesStoreLiteDispatch_setMappedByte (cd := I.calldata)
    (by simpa [selIs] using hsel)
  have hdec := bytesStoreLiteDecode_setMappedByte (I := I) hsz100 hhi hcanon
  have hword :
      bytesStoreLiteSetMappedByteHeaderWord σ_evm I =
        bytesStoreLiteSetMappedByteHeaderWord σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner
      (bytesStoreLiteSetMappedByteSlot I) ⟨0⟩
  have hslot :
      (σ_solm.find? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD (bytesStoreLiteSetMappedByteSlot I) ⟨0⟩)) =
      (σ_evm.find? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD (bytesStoreLiteSetMappedByteSlot I) ⟨0⟩)) := by
    simpa [bytesStoreLiteSetMappedByteHeaderWord] using hword.symm
  have hload :
      Solm.EVM.storageLoad
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        I.codeOwner (bytesStoreLiteSetMappedByteSlot I) =
          bytesStoreLiteSetMappedByteHeaderWord σ_evm I := by
    simp [Solm.EVM.storageLoad, initState, State.lookupAccount, Account.lookupStorage,
      bytesStoreLiteSetMappedByteHeaderWord, hslot]
  have hloadMapped :
      Solm.EVM.storageLoad
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        I.codeOwner
          (mappedValueSlot
            (.int (Int.ofNat (bytesStoreLiteSetMappedByteKeyWord I).toNat))) =
          bytesStoreLiteSetMappedByteHeaderWord σ_evm I := by
    simpa [bytesStoreLiteSetMappedByteSlot, bytesStoreLiteSetMappedSlotOf] using hload
  have hloadMapped' :
      Solm.EVM.storageLoad
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        I.codeOwner
          (mappedValueSlot
            (.int ((bytesStoreLiteSetMappedByteKeyWord I).toNat : Int))) =
          bytesStoreLiteSetMappedByteHeaderWord σ_evm I := by
    simpa using hloadMapped
  have hcodeOwner :
      (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner =
        I.codeOwner := by
    rfl
  have hvalid0 :
      UInt256.sub ⟨0⟩
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStoreLiteSetMappedByteHeaderWord σ_evm I) ⟨2⟩)
            ⟨127⟩) ⟨32⟩) ≠ ⟨0⟩ := by
    simpa [hflag] using hvalid
  have hlen :
      readStorageBytesLength? bytesStoreLiteConfig
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (bytesStoreLiteSetMappedByteHeaderRef I) =
          .ok (UInt256.land
            (UInt256.div (bytesStoreLiteSetMappedByteHeaderWord σ_evm I) ⟨2⟩)
            ⟨127⟩).toNat := by
    simp [readStorageBytesLength?, storageNatResultToEval, bytesStoreLiteConfig,
      bytesStoreLiteStorageLayout, solidityStorageLayout, solidityReadBytesLength?,
      solidityDecodeBytesLengthHeader, bytesStoreLiteLayout,
      bytesStoreLiteSetMappedByteHeaderRef, hcodeOwner, hloadMapped', hflag, hvalid0]
  have hbody :
      ExecTransitionBody bytesStoreLiteConfig bytesStoreLiteContract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (bytesStoreLiteSetMappedByteLocals I) setMappedByteTransition.body .reverted := by
    exact bytesStoreLiteSetMappedByteBodyBoundsRevertsOfLength
      (by simp only [initState]; exact hwv) hlen hbound
  exact (bytesStoreLiteX_setMappedByteOobShort
      (g := Sat256.ofUInt256 g) hreachBody hflag hvalid hbound)
    |>.reEquivExecutionRevert hcode hd hdec hbody

theorem bytesStoreLiteSetMappedByteLongMalformedRuntime
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x13, 0x2f, 0xa3, 0x46]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsz100 : 100 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (bytesStoreLiteSetMappedByteValueWord I).toNat < EVM.twoPow 8)
    (hflag : UInt256.land (bytesStoreLiteSetMappedByteHeaderWord σ_evm I) ⟨1⟩ ≠ ⟨0⟩)
    (hbad : UInt256.sub (UInt256.land (bytesStoreLiteSetMappedByteHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStoreLiteSetMappedByteHeaderWord σ_evm I) ⟨2⟩) ⟨32⟩) =
      ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsz := bytesStoreLiteSetMappedByteSelector_size hsel
  have hreach := bytesStoreLiteReachSetMappedByte (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz hsize hsel
  have hreachPc : ∃ k C, RD bytesStoreLiteBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨319⟩
      [bytesStoreLiteSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ_evm) k C := by
    simpa [bytesStoreLiteSetMappedByteEntryPc] using hreach
  have hreachBody := bytesStoreLiteX_setMappedByteDecodeValid
    (g := Sat256.ofUInt256 g) hreachPc hsz100 hhi hsize
    (bytesStoreLiteSetPacketByteLand255_eq_self_of_uint8 hcanon)
  have hd := bytesStoreLiteDispatch_setMappedByte (cd := I.calldata)
    (by simpa [selIs] using hsel)
  have hdec := bytesStoreLiteDecode_setMappedByte (I := I) hsz100 hhi hcanon
  have hword :
      bytesStoreLiteSetMappedByteHeaderWord σ_evm I =
        bytesStoreLiteSetMappedByteHeaderWord σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner
      (bytesStoreLiteSetMappedByteSlot I) ⟨0⟩
  have hslot :
      (σ_solm.find? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD (bytesStoreLiteSetMappedByteSlot I) ⟨0⟩)) =
      (σ_evm.find? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD (bytesStoreLiteSetMappedByteSlot I) ⟨0⟩)) := by
    simpa [bytesStoreLiteSetMappedByteHeaderWord] using hword.symm
  have hload :
      Solm.EVM.storageLoad
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        I.codeOwner (bytesStoreLiteSetMappedByteSlot I) =
          bytesStoreLiteSetMappedByteHeaderWord σ_evm I := by
    simp [Solm.EVM.storageLoad, initState, State.lookupAccount, Account.lookupStorage,
      bytesStoreLiteSetMappedByteHeaderWord, hslot]
  have hloadMapped :
      Solm.EVM.storageLoad
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        I.codeOwner
          (mappedValueSlot
            (.int ((bytesStoreLiteSetMappedByteKeyWord I).toNat : Int))) =
          bytesStoreLiteSetMappedByteHeaderWord σ_evm I := by
    simpa [bytesStoreLiteSetMappedByteSlot, bytesStoreLiteSetMappedSlotOf] using hload
  have hcodeOwner :
      (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner =
        I.codeOwner := by
    rfl
  have hlen :
      readStorageBytesLength? bytesStoreLiteConfig
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (bytesStoreLiteSetMappedByteHeaderRef I) = .revert := by
    simp [readStorageBytesLength?, storageNatResultToEval, bytesStoreLiteConfig,
      bytesStoreLiteStorageLayout, solidityStorageLayout, solidityReadBytesLength?,
      solidityDecodeBytesLengthHeader, bytesStoreLiteLayout,
      bytesStoreLiteSetMappedByteHeaderRef, hcodeOwner, hloadMapped, hflag, hbad]
  have hbody :
      ExecTransitionBody bytesStoreLiteConfig bytesStoreLiteContract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (bytesStoreLiteSetMappedByteLocals I) setMappedByteTransition.body .reverted := by
    exact bytesStoreLiteSetMappedByteBodyRevertsOfLengthRead
      (by simp only [initState]; exact hwv) hlen
  exact (bytesStoreLiteX_setMappedByteLongMalformed
      (g := Sat256.ofUInt256 g) hreachBody hflag hbad)
    |>.reEquivExecutionRevert hcode hd hdec hbody

theorem bytesStoreLiteSetMappedByteShortMalformedRuntime
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x13, 0x2f, 0xa3, 0x46]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsz100 : 100 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (bytesStoreLiteSetMappedByteValueWord I).toNat < EVM.twoPow 8)
    (hflag : UInt256.land (bytesStoreLiteSetMappedByteHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩)
    (hbad : UInt256.sub (UInt256.land (bytesStoreLiteSetMappedByteHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStoreLiteSetMappedByteHeaderWord σ_evm I) ⟨2⟩)
            ⟨127⟩) ⟨32⟩) = ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsz := bytesStoreLiteSetMappedByteSelector_size hsel
  have hreach := bytesStoreLiteReachSetMappedByte (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz hsize hsel
  have hreachPc : ∃ k C, RD bytesStoreLiteBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨319⟩
      [bytesStoreLiteSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ_evm) k C := by
    simpa [bytesStoreLiteSetMappedByteEntryPc] using hreach
  have hreachBody := bytesStoreLiteX_setMappedByteDecodeValid
    (g := Sat256.ofUInt256 g) hreachPc hsz100 hhi hsize
    (bytesStoreLiteSetPacketByteLand255_eq_self_of_uint8 hcanon)
  have hd := bytesStoreLiteDispatch_setMappedByte (cd := I.calldata)
    (by simpa [selIs] using hsel)
  have hdec := bytesStoreLiteDecode_setMappedByte (I := I) hsz100 hhi hcanon
  have hword :
      bytesStoreLiteSetMappedByteHeaderWord σ_evm I =
        bytesStoreLiteSetMappedByteHeaderWord σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner
      (bytesStoreLiteSetMappedByteSlot I) ⟨0⟩
  have hslot :
      (σ_solm.find? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD (bytesStoreLiteSetMappedByteSlot I) ⟨0⟩)) =
      (σ_evm.find? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD (bytesStoreLiteSetMappedByteSlot I) ⟨0⟩)) := by
    simpa [bytesStoreLiteSetMappedByteHeaderWord] using hword.symm
  have hload :
      Solm.EVM.storageLoad
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        I.codeOwner (bytesStoreLiteSetMappedByteSlot I) =
          bytesStoreLiteSetMappedByteHeaderWord σ_evm I := by
    simp [Solm.EVM.storageLoad, initState, State.lookupAccount, Account.lookupStorage,
      bytesStoreLiteSetMappedByteHeaderWord, hslot]
  have hloadMapped :
      Solm.EVM.storageLoad
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        I.codeOwner
          (mappedValueSlot
            (.int ((bytesStoreLiteSetMappedByteKeyWord I).toNat : Int))) =
          bytesStoreLiteSetMappedByteHeaderWord σ_evm I := by
    simpa [bytesStoreLiteSetMappedByteSlot, bytesStoreLiteSetMappedSlotOf] using hload
  have hcodeOwner :
      (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner =
        I.codeOwner := by
    rfl
  have hbad0 :
      UInt256.sub ⟨0⟩
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStoreLiteSetMappedByteHeaderWord σ_evm I) ⟨2⟩)
            ⟨127⟩) ⟨32⟩) = ⟨0⟩ := by
    simpa [hflag] using hbad
  have hlen :
      readStorageBytesLength? bytesStoreLiteConfig
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (bytesStoreLiteSetMappedByteHeaderRef I) = .revert := by
    simp [readStorageBytesLength?, storageNatResultToEval, bytesStoreLiteConfig,
      bytesStoreLiteStorageLayout, solidityStorageLayout, solidityReadBytesLength?,
      solidityDecodeBytesLengthHeader, bytesStoreLiteLayout,
      bytesStoreLiteSetMappedByteHeaderRef, hcodeOwner, hloadMapped, hflag, hbad0]
  have hbody :
      ExecTransitionBody bytesStoreLiteConfig bytesStoreLiteContract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (bytesStoreLiteSetMappedByteLocals I) setMappedByteTransition.body .reverted := by
    exact bytesStoreLiteSetMappedByteBodyRevertsOfLengthRead
      (by simp only [initState]; exact hwv) hlen
  exact (bytesStoreLiteX_setMappedByteShortMalformed
      (g := Sat256.ofUInt256 g) hreachBody hflag hbad)
    |>.reEquivExecutionRevert hcode hd hdec hbody

end BytesStoreLite
