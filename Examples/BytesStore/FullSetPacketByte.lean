import Examples.BytesStore.FullSetByte
import Examples.BytesStore.FullSetPacketStorage

/-!
# BytesStore — `setPacketByte(uint256,uint8)` runtime slice

This module starts the packet byte setter proof in a separate file so the large dispatcher/getter
module does not keep growing while the remaining setter bodies are proved.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

namespace BytesStore

def bytesStoreSetPacketByteLocals (I : ExecutionEnv) : Store :=
  ((∅ : Store).insert "byteIndex"
    (.int (Int.ofNat (bytesStoreSetByteIndexWord I).toNat))).insert "value"
    (.int (Int.ofNat (bytesStoreSetByteValueWord I).toNat))

theorem bytesStoreSetPacketByteLocals_get_byteIndex (I : ExecutionEnv) :
    (bytesStoreSetPacketByteLocals I).get? "byteIndex" =
      some (.int (Int.ofNat (bytesStoreSetByteIndexWord I).toNat)) := by
  rw [bytesStoreSetPacketByteLocals]
  rw [store_get_ne (h := by decide)]
  rw [store_get_self]

theorem bytesStoreSetPacketByteLocals_getElem_byteIndex (I : ExecutionEnv) :
    (bytesStoreSetPacketByteLocals I)["byteIndex"]? =
      some (.int (Int.ofNat (bytesStoreSetByteIndexWord I).toNat)) := by
  simpa [Std.HashMap.get?_eq_getElem?] using
    bytesStoreSetPacketByteLocals_get_byteIndex I

theorem bytesStoreSetPacketByteLocals_get_packet_none (I : ExecutionEnv) :
    (bytesStoreSetPacketByteLocals I).get? "packet" = none := by
  rw [bytesStoreSetPacketByteLocals]
  rw [store_get_ne (h := by decide)]
  rw [store_get_ne (h := by decide)]
  simp

theorem bytesStoreSetPacketByteLocals_getElem_packet_none (I : ExecutionEnv) :
    (bytesStoreSetPacketByteLocals I)["packet"]? = none := by
  simpa [Std.HashMap.get?_eq_getElem?] using
    bytesStoreSetPacketByteLocals_get_packet_none I

def bytesStoreSetPacketByteRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "packet"
    steps := [.field "data",
      .aindex (.int (Int.ofNat (bytesStoreSetByteIndexWord I).toNat))] }

def bytesStoreSetPacketByteValue (I : ExecutionEnv) : Value :=
  .int (Int.ofNat (bytesStoreSetByteValueWord I).toNat)

def bytesStoreSetPacketByteFrame (I : ExecutionEnv) : Frame :=
  { contract := bytesStoreContract, locals := bytesStoreSetPacketByteLocals I }

def bytesStoreSetPacketByteShortScale (I : ExecutionEnv) : UInt256 :=
  UInt256.exp ⟨256⟩ (UInt256.sub ⟨31⟩ (bytesStoreSetByteIndexWord I))

def bytesStoreSetPacketByteShortStoredWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.lor
    (UInt256.mul
      (UInt256.div (UInt256.shiftLeft (bytesStoreSetByteValueWord I) ⟨248⟩)
        (UInt256.shiftLeft ⟨1⟩ ⟨248⟩))
      (bytesStoreSetPacketByteShortScale I))
    (UInt256.land
      (UInt256.lnot (UInt256.mul ⟨255⟩ (bytesStoreSetPacketByteShortScale I)))
      (bytesStorePacketLengthHeaderWord σ I))

def bytesStoreSetPacketByteLongWordIndex (I : ExecutionEnv) : UInt256 :=
  UInt256.mod (bytesStoreSetByteIndexWord I) ⟨32⟩

def bytesStoreSetPacketByteLongDataSlot (I : ExecutionEnv) : UInt256 :=
  bytesLikeDataBase ⟨2⟩ + UInt256.div (bytesStoreSetByteIndexWord I) ⟨32⟩

def bytesStoreSetPacketByteLongScale (I : ExecutionEnv) : UInt256 :=
  UInt256.exp ⟨256⟩ (UInt256.sub ⟨31⟩ (bytesStoreSetPacketByteLongWordIndex I))

def bytesStoreSetPacketByteLongOldWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  (σ.find? I.codeOwner |>.option ⟨0⟩
    (fun acc => acc.storage.findD (bytesStoreSetPacketByteLongDataSlot I) ⟨0⟩))

theorem bytesStoreSetPacketByteLongOldWord_eq_of_accountMapEquiv
    {σ_evm σ_solm : AccountMap} {I : ExecutionEnv}
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    bytesStoreSetPacketByteLongOldWord σ_evm I =
      bytesStoreSetPacketByteLongOldWord σ_solm I :=
  accountMapEquiv_storage_findD hAccounts I.codeOwner
    (bytesStoreSetPacketByteLongDataSlot I) ⟨0⟩

theorem bytesStoreStorageLoadSetPacketByteLongData_initState_of_accountMapEquiv
    {cA : Batteries.RBSet AccountAddress compare} {gh : BlockHeader} {bl : ProcessedBlocks}
    {σ_evm σ_solm σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : Sat256}
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    Solm.EVM.storageLoad (initState cA gh bl σ_solm σ₀ g A I)
        (initState cA gh bl σ_solm σ₀ g A I).executionEnv.codeOwner
        (bytesStoreSetPacketByteLongDataSlot I) =
      bytesStoreSetPacketByteLongOldWord σ_evm I := by
  simpa [bytesStoreSetPacketByteLongOldWord] using
    bytesStoreStorageLoad_initState_of_accountMapEquiv
      (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
      (I := I) (g := g) (bytesStoreSetPacketByteLongDataSlot I) hAccounts

def bytesStoreSetPacketByteLongStoredWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.lor
    (UInt256.mul
      (UInt256.div (UInt256.shiftLeft (bytesStoreSetByteValueWord I) ⟨248⟩)
        (UInt256.shiftLeft ⟨1⟩ ⟨248⟩))
      (bytesStoreSetPacketByteLongScale I))
    (UInt256.land
      (UInt256.lnot (UInt256.mul ⟨255⟩ (bytesStoreSetPacketByteLongScale I)))
      (bytesStoreSetPacketByteLongOldWord σ I))

theorem bytesStoreSetPacketByteLongBaseHash :
    UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC ((wordAt0Mem (⟨2⟩ : UInt256) solcFreePtrMem).readWithPadding 0 32))) =
      bytesLikeDataBase ⟨2⟩ := by
  rw [wordAt0Mem_read0]
  simpa [bytesLikeDataBase] using keccakSlot_eq (UInt256.toByteArray (⟨2⟩ : UInt256))

theorem bytesStoreSetPacketByteLongBaseHashMem (mem : ByteArray) :
    UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC ((wordAt0Mem (⟨2⟩ : UInt256) mem).readWithPadding 0 32))) =
      bytesLikeDataBase ⟨2⟩ := by
  rw [wordAt0Mem_read0]
  simpa [bytesLikeDataBase] using keccakSlot_eq (UInt256.toByteArray (⟨2⟩ : UInt256))

theorem bytesStoreX_returnUInt8_301OfMem {cA gh bl σinit σ σ₀ A I} {g : Sat256}
    {val : UInt256} {mem : ByteArray}
    (hsize : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨301⟩
      [val, bytesStoreSelWord I] mem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C) :
    RDret bytesStoreBytecode g (initState cA gh bl σinit σ₀ g A I) (cA, σ)
      (UInt256.toByteArray (UInt256.land val ⟨255⟩)) := by
  obtain ⟨_, _, rd301⟩ := hreach
  have rd273 := evm_run rd301 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by native_decide)
      mem_cost
      (mloadFreePtrValue (by rw [hsize]; decide) (by decide) hread64)
      (by native_decide) (by evm_ov),
    push1 ⟨255⟩, swap1, swap2, and, dup2,
    raw mstore 6 (bytesStoreReturnFromMem mem (UInt256.land val ⟨255⟩))
      (UInt256.ofNat 5) (by native_decide)
      mem_cost
      (by rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide]; rfl)
      (by native_decide) (by evm_ov),
    push1 ⟨32⟩, add, push2 ⟨273⟩, jump (by native_decide)]
  exact evm_run rd273 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 5) (by native_decide)
      mem_cost
      (bytesStoreReturnFromMem_mload64 mem (UInt256.land val ⟨255⟩) hsize hread64)
      (by native_decide) (by evm_ov),
    dup1, swap2, sub, swap1,
    raw ret 0 (UInt256.toByteArray (UInt256.land val ⟨255⟩)) (by native_decide)
      mem_cost
      (by
        rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide,
          show (UInt256.sub ((⟨32⟩ : UInt256) + ⟨128⟩) ⟨128⟩).toNat = 32 from by decide,
          bytesStoreReturnFromMem_read128 mem (UInt256.land val ⟨255⟩) hsize])
      (by evm_ov)]

theorem bytesStoreSetPacketByteShortStoredWord_load_self
    {σ : AccountMap} {I : ExecutionEnv} {acc : Account}
    (hacc : σ.find? I.codeOwner = some acc)
    (hnz : (bytesStoreSetPacketByteShortStoredWord σ I == (default : UInt256)) = false) :
    (((sstoreAccountMap I.codeOwner σ ⟨2⟩
        (bytesStoreSetPacketByteShortStoredWord σ I)).find? I.codeOwner).option
        (default : UInt256) (fun acc => acc.storage.findD ⟨2⟩ (default : UInt256))) =
      bytesStoreSetPacketByteShortStoredWord σ I := by
  exact sstoreAccountMap_storage_findD_self_of_find_some σ I.codeOwner acc ⟨2⟩
    (bytesStoreSetPacketByteShortStoredWord σ I) hacc hnz

theorem bytesStoreSetPacketByteLongWordIndex_toNat (I : ExecutionEnv) :
    (bytesStoreSetPacketByteLongWordIndex I).toNat =
      (bytesStoreSetByteIndexWord I).toNat % 32 := by
  simpa [bytesStoreSetPacketByteLongWordIndex, bytesStoreSetByteLongWordIndex] using
    bytesStoreSetByteLongWordIndex_toNat I

theorem bytesStoreSetPacketByteLongWordIndex_lt32 (I : ExecutionEnv) :
    (bytesStoreSetPacketByteLongWordIndex I).toNat < 32 := by
  rw [bytesStoreSetPacketByteLongWordIndex_toNat]
  exact Nat.mod_lt _ (by decide : 0 < 32)

theorem bytesStoreSetPacketByteLongWordIndex_eq_index_of_lt32
    {I : ExecutionEnv}
    (hidx : (bytesStoreSetByteIndexWord I).toNat < 32) :
    bytesStoreSetPacketByteLongWordIndex I =
      bytesStoreSetByteIndexWord I := by
  apply u256_inj
  rw [bytesStoreSetPacketByteLongWordIndex_toNat]
  exact Nat.mod_eq_of_lt hidx

theorem bytesStoreSetPacketByteLongScale_toNat {I : ExecutionEnv} :
    (bytesStoreSetPacketByteLongScale I).toNat =
      2 ^ ((31 - (bytesStoreSetPacketByteLongWordIndex I).toNat) * 8) := by
  simpa [bytesStoreSetPacketByteLongScale, bytesStoreSetByteLongScale,
    bytesStoreSetPacketByteLongWordIndex, bytesStoreSetByteLongWordIndex] using
    bytesStoreSetByteLongScale_toNat (I := I)

theorem bytesStoreSetPacketByteLongMaskWord_toNat {I : ExecutionEnv} :
    (UInt256.mul ⟨255⟩ (bytesStoreSetPacketByteLongScale I)).toNat =
      255 * 2 ^ ((31 - (bytesStoreSetPacketByteLongWordIndex I).toNat) * 8) := by
  simpa [bytesStoreSetPacketByteLongScale, bytesStoreSetByteLongScale,
    bytesStoreSetPacketByteLongWordIndex, bytesStoreSetByteLongWordIndex] using
    bytesStoreSetByteLongMaskWord_toNat (I := I)

theorem bytesStoreSetPacketByteLongClearMask_toNat {I : ExecutionEnv} :
    (UInt256.lnot (UInt256.mul ⟨255⟩ (bytesStoreSetPacketByteLongScale I))).toNat =
      (2 : Nat) ^ 256 - 1 -
        255 * 2 ^ ((31 - (bytesStoreSetPacketByteLongWordIndex I).toNat) * 8) := by
  simpa [bytesStoreSetPacketByteLongScale, bytesStoreSetByteLongScale,
    bytesStoreSetPacketByteLongWordIndex, bytesStoreSetByteLongWordIndex] using
    bytesStoreSetByteLongClearMask_toNat (I := I)

theorem bytesStoreSetPacketByteShortScale_toNat {I : ExecutionEnv} {len : UInt256}
    (hshort : len.toNat < 32)
    (hbound : (bytesStoreSetByteIndexWord I).toNat < len.toNat) :
    (bytesStoreSetPacketByteShortScale I).toNat =
      2 ^ ((31 - (bytesStoreSetByteIndexWord I).toNat) * 8) := by
  simpa [bytesStoreSetPacketByteShortScale, bytesStoreSetByteShortScale] using
    bytesStoreSetByteShortScale_toNat (I := I) (len := len) hshort hbound

theorem bytesStoreSetPacketByteShortMaskWord_toNat {I : ExecutionEnv} {len : UInt256}
    (hshort : len.toNat < 32)
    (hbound : (bytesStoreSetByteIndexWord I).toNat < len.toNat) :
    (UInt256.mul ⟨255⟩ (bytesStoreSetPacketByteShortScale I)).toNat =
      255 * 2 ^ ((31 - (bytesStoreSetByteIndexWord I).toNat) * 8) := by
  simpa [bytesStoreSetPacketByteShortScale, bytesStoreSetByteShortScale] using
    bytesStoreSetByteShortMaskWord_toNat (I := I) (len := len) hshort hbound

theorem bytesStoreSetPacketByteShortClearMask_toNat {I : ExecutionEnv} {len : UInt256}
    (hshort : len.toNat < 32)
    (hbound : (bytesStoreSetByteIndexWord I).toNat < len.toNat) :
    (UInt256.lnot (UInt256.mul ⟨255⟩ (bytesStoreSetPacketByteShortScale I))).toNat =
      2 ^ 256 - 1 - 255 * 2 ^ ((31 - (bytesStoreSetByteIndexWord I).toNat) * 8) := by
  simpa [bytesStoreSetPacketByteShortScale, bytesStoreSetByteShortScale] using
    bytesStoreSetByteShortClearMask_toNat (I := I) (len := len) hshort hbound

theorem bytesStoreSetPacketByteShortStoredWord_byteAt
    {σ : AccountMap} {I : ExecutionEnv} {len : UInt256}
    (hcanon : (bytesStoreSetByteValueWord I).toNat < EVM.twoPow 8)
    (hshort : len.toNat < 32)
    (hbound : (bytesStoreSetByteIndexWord I).toNat < len.toNat) :
    UInt256.byteAt (bytesStoreSetByteIndexWord I)
      (bytesStoreSetPacketByteShortStoredWord σ I) = bytesStoreSetByteValueWord I := by
  apply u256_inj
  have hi31 : (bytesStoreSetByteIndexWord I).toNat ≤ 31 := by
    have hlt := bytesStoreSetByteIndex_lt31_of_short_bound (I := I) (len := len)
      hshort hbound
    omega
  rw [byteAt_toNat_of_le31 hi31]
  rw [bytesStoreSetPacketByteShortStoredWord, bytesStoreSetByteValueHighShiftDiv hcanon]
  rw [u256_lor_toNat, u256_mul_toNat, u256_land_toNat]
  rw [bytesStoreSetPacketByteShortScale_toNat (I := I) (len := len) hshort hbound]
  rw [bytesStoreSetPacketByteShortClearMask_toNat (I := I) (len := len) hshort hbound]
  have hv : (bytesStoreSetByteValueWord I).toNat < 256 := by
    simpa [EVM.twoPow] using hcanon
  have hk : ((31 - (bytesStoreSetByteIndexWord I).toNat) * 8) + 8 ≤ 256 := by
    have hidx : (bytesStoreSetByteIndexWord I).toNat < 31 :=
      bytesStoreSetByteIndex_lt31_of_short_bound (I := I) (len := len) hshort hbound
    omega
  have hleftLt : (bytesStoreSetByteValueWord I).toNat *
      2 ^ ((31 - (bytesStoreSetByteIndexWord I).toNat) * 8) < UInt256.size := by
    rw [show UInt256.size = 2 ^ 256 from rfl]
    calc (bytesStoreSetByteValueWord I).toNat *
            2 ^ ((31 - (bytesStoreSetByteIndexWord I).toNat) * 8) <
          256 * 2 ^ ((31 - (bytesStoreSetByteIndexWord I).toNat) * 8) :=
            Nat.mul_lt_mul_of_pos_right hv (by positivity)
        _ ≤ 2 ^ 256 := by
          rw [show 256 = 2 ^ 8 by norm_num, ← Nat.pow_add]
          exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hrightLt : (((2 : Nat) ^ 256 - 1 -
        255 * 2 ^ ((31 - (bytesStoreSetByteIndexWord I).toNat) * 8)) &&&
        (bytesStorePacketLengthHeaderWord σ I).toNat) < UInt256.size := by
    exact lt_of_le_of_lt Nat.and_le_right (bytesStorePacketLengthHeaderWord σ I).val.isLt
  rw [Nat.mod_eq_of_lt hleftLt]
  change ((bytesStoreSetByteValueWord I).toNat *
          2 ^ ((31 - (bytesStoreSetByteIndexWord I).toNat) * 8)).lor
        ((((2 : Nat) ^ 256 - 1 -
          255 * 2 ^ ((31 - (bytesStoreSetByteIndexWord I).toNat) * 8)) &&&
          (bytesStorePacketLengthHeaderWord σ I).toNat) % UInt256.size) %
        UInt256.size /
      2 ^ ((31 - (bytesStoreSetByteIndexWord I).toNat) * 8) % 256 =
    (bytesStoreSetByteValueWord I).toNat
  rw [Nat.mod_eq_of_lt hrightLt]
  have hlorLt :
      ((bytesStoreSetByteValueWord I).toNat *
            2 ^ ((31 - (bytesStoreSetByteIndexWord I).toNat) * 8)).lor
          (((2 : Nat) ^ 256 - 1 -
              255 * 2 ^ ((31 - (bytesStoreSetByteIndexWord I).toNat) * 8)) &&&
            (bytesStorePacketLengthHeaderWord σ I).toNat) < UInt256.size := by
    change ((bytesStoreSetByteValueWord I).toNat *
          2 ^ ((31 - (bytesStoreSetByteIndexWord I).toNat) * 8)) |||
        (((2 : Nat) ^ 256 - 1 -
            255 * 2 ^ ((31 - (bytesStoreSetByteIndexWord I).toNat) * 8)) &&&
          (bytesStorePacketLengthHeaderWord σ I).toNat) < 2 ^ 256
    apply Nat.or_lt_two_pow
    · simpa [UInt256.size] using hleftLt
    · simpa [UInt256.size] using hrightLt
  rw [Nat.mod_eq_of_lt hlorLt]
  exact nat_byte_lane_lor_clear_eq
    (old := (bytesStorePacketLengthHeaderWord σ I).toNat)
    (v := (bytesStoreSetByteValueWord I).toNat)
    (k := (31 - (bytesStoreSetByteIndexWord I).toNat) * 8) hv hk

theorem bytesStoreSetPacketByteLongStoredWord_byteAt
    {σ : AccountMap} {I : ExecutionEnv}
    (hcanon : (bytesStoreSetByteValueWord I).toNat < EVM.twoPow 8) :
    UInt256.byteAt (bytesStoreSetPacketByteLongWordIndex I)
      (bytesStoreSetPacketByteLongStoredWord σ I) = bytesStoreSetByteValueWord I := by
  apply u256_inj
  have hv : (bytesStoreSetByteValueWord I).toNat < 256 := by
    simpa [EVM.twoPow] using hcanon
  have hidxLt : (bytesStoreSetPacketByteLongWordIndex I).toNat < 32 :=
    bytesStoreSetPacketByteLongWordIndex_lt32 I
  have hidxLe : (bytesStoreSetPacketByteLongWordIndex I).toNat ≤ 31 := by omega
  rw [byteAt_toNat_of_le31 hidxLe]
  rw [bytesStoreSetPacketByteLongStoredWord, bytesStoreSetByteValueHighShiftDiv hcanon]
  rw [u256_lor_toNat, u256_mul_toNat, u256_land_toNat]
  rw [bytesStoreSetPacketByteLongScale_toNat (I := I)]
  rw [bytesStoreSetPacketByteLongClearMask_toNat (I := I)]
  have hk : ((31 - (bytesStoreSetPacketByteLongWordIndex I).toNat) * 8) + 8 ≤ 256 := by
    omega
  have hleftLt : (bytesStoreSetByteValueWord I).toNat *
      2 ^ ((31 - (bytesStoreSetPacketByteLongWordIndex I).toNat) * 8) < UInt256.size := by
    rw [show UInt256.size = 2 ^ 256 from rfl]
    calc (bytesStoreSetByteValueWord I).toNat *
            2 ^ ((31 - (bytesStoreSetPacketByteLongWordIndex I).toNat) * 8) <
          256 * 2 ^ ((31 - (bytesStoreSetPacketByteLongWordIndex I).toNat) * 8) :=
            Nat.mul_lt_mul_of_pos_right hv (by positivity)
        _ = 2 ^ (8 + (31 - (bytesStoreSetPacketByteLongWordIndex I).toNat) * 8) := by
          rw [show 256 = 2 ^ 8 by norm_num, Nat.pow_add]
        _ ≤ 2 ^ 256 := by
          exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hrightLt : (((2 : Nat) ^ 256 - 1 -
        255 * 2 ^ ((31 - (bytesStoreSetPacketByteLongWordIndex I).toNat) * 8)) &&&
        (bytesStoreSetPacketByteLongOldWord σ I).toNat) < UInt256.size := by
    exact lt_of_le_of_lt Nat.and_le_right (bytesStoreSetPacketByteLongOldWord σ I).val.isLt
  rw [Nat.mod_eq_of_lt hleftLt]
  change (((bytesStoreSetByteValueWord I).toNat *
          2 ^ ((31 - (bytesStoreSetPacketByteLongWordIndex I).toNat) * 8)).lor
        ((((2 : Nat) ^ 256 - 1 -
          255 * 2 ^ ((31 - (bytesStoreSetPacketByteLongWordIndex I).toNat) * 8)) &&&
          (bytesStoreSetPacketByteLongOldWord σ I).toNat) % UInt256.size) %
        UInt256.size) /
      2 ^ ((31 - (bytesStoreSetPacketByteLongWordIndex I).toNat) * 8) % 256 =
    (bytesStoreSetByteValueWord I).toNat
  rw [Nat.mod_eq_of_lt hrightLt]
  have hlorLt :
      ((bytesStoreSetByteValueWord I).toNat *
            2 ^ ((31 - (bytesStoreSetPacketByteLongWordIndex I).toNat) * 8)).lor
          (((2 : Nat) ^ 256 - 1 -
              255 * 2 ^ ((31 - (bytesStoreSetPacketByteLongWordIndex I).toNat) * 8)) &&&
            (bytesStoreSetPacketByteLongOldWord σ I).toNat) < UInt256.size := by
    change ((bytesStoreSetByteValueWord I).toNat *
          2 ^ ((31 - (bytesStoreSetPacketByteLongWordIndex I).toNat) * 8)) |||
        (((2 : Nat) ^ 256 - 1 -
            255 * 2 ^ ((31 - (bytesStoreSetPacketByteLongWordIndex I).toNat) * 8)) &&&
          (bytesStoreSetPacketByteLongOldWord σ I).toNat) < 2 ^ 256
    apply Nat.or_lt_two_pow
    · simpa [UInt256.size] using hleftLt
    · simpa [UInt256.size] using hrightLt
  rw [Nat.mod_eq_of_lt hlorLt]
  exact nat_byte_lane_lor_clear_eq
    (old := (bytesStoreSetPacketByteLongOldWord σ I).toNat)
    (v := (bytesStoreSetByteValueWord I).toNat)
    (k := (31 - (bytesStoreSetPacketByteLongWordIndex I).toNat) * 8) hv hk

theorem bytesStoreSetPacketByteLongStoredWord_byteAt_index_of_lt32
    {σ : AccountMap} {I : ExecutionEnv}
    (hcanon : (bytesStoreSetByteValueWord I).toNat < EVM.twoPow 8)
    (hidx : (bytesStoreSetByteIndexWord I).toNat < 32) :
    UInt256.byteAt (bytesStoreSetByteIndexWord I)
      (bytesStoreSetPacketByteLongStoredWord σ I) =
        bytesStoreSetByteValueWord I := by
  have heq := bytesStoreSetPacketByteLongWordIndex_eq_index_of_lt32
    (I := I) hidx
  rw [← heq]
  exact bytesStoreSetPacketByteLongStoredWord_byteAt (σ := σ) (I := I) hcanon

theorem bytesStoreSetPacketByteShortStoredWord_toNat_update
    {σ : AccountMap} {I : ExecutionEnv} {len : UInt256}
    (hcanon : (bytesStoreSetByteValueWord I).toNat < EVM.twoPow 8)
    (hshort : len.toNat < 32)
    (hbound : (bytesStoreSetByteIndexWord I).toNat < len.toNat) :
    (bytesStorePacketLengthHeaderWord σ I).toNat %
          2 ^ ((31 - (bytesStoreSetByteIndexWord I).toNat) * 8) +
        2 ^ ((31 - (bytesStoreSetByteIndexWord I).toNat) * 8) *
          (bytesStoreSetByteValueWord I).toNat +
      2 ^ ((31 - (bytesStoreSetByteIndexWord I).toNat) * 8 + 8) *
        ((bytesStorePacketLengthHeaderWord σ I).toNat /
          2 ^ ((31 - (bytesStoreSetByteIndexWord I).toNat) * 8 + 8)) =
    (bytesStoreSetPacketByteShortStoredWord σ I).toNat := by
  have hv : (bytesStoreSetByteValueWord I).toNat < 256 := by
    simpa [EVM.twoPow] using hcanon
  rw [bytesStoreSetPacketByteShortStoredWord, bytesStoreSetByteValueHighShiftDiv hcanon]
  rw [u256_lor_toNat, u256_mul_toNat, u256_land_toNat]
  rw [bytesStoreSetPacketByteShortScale_toNat (I := I) (len := len) hshort hbound]
  rw [bytesStoreSetPacketByteShortClearMask_toNat (I := I) (len := len) hshort hbound]
  have hk : ((31 - (bytesStoreSetByteIndexWord I).toNat) * 8) + 8 ≤ 256 := by
    have hidx := bytesStoreSetByteIndex_lt31_of_short_bound
      (I := I) (len := len) hshort hbound
    omega
  have hleftLt : (bytesStoreSetByteValueWord I).toNat *
      2 ^ ((31 - (bytesStoreSetByteIndexWord I).toNat) * 8) < UInt256.size := by
    rw [show UInt256.size = 2 ^ 256 from rfl]
    calc (bytesStoreSetByteValueWord I).toNat *
            2 ^ ((31 - (bytesStoreSetByteIndexWord I).toNat) * 8) <
          256 * 2 ^ ((31 - (bytesStoreSetByteIndexWord I).toNat) * 8) :=
            Nat.mul_lt_mul_of_pos_right hv (by positivity)
        _ ≤ 2 ^ 256 := by
          rw [show 256 = 2 ^ 8 by norm_num, ← Nat.pow_add]
          exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hrightLt : (((2 : Nat) ^ 256 - 1 -
        255 * 2 ^ ((31 - (bytesStoreSetByteIndexWord I).toNat) * 8)) &&&
        (bytesStorePacketLengthHeaderWord σ I).toNat) < UInt256.size := by
    exact lt_of_le_of_lt Nat.and_le_right (bytesStorePacketLengthHeaderWord σ I).val.isLt
  rw [Nat.mod_eq_of_lt hleftLt]
  change (bytesStorePacketLengthHeaderWord σ I).toNat %
        2 ^ ((31 - (bytesStoreSetByteIndexWord I).toNat) * 8) +
      2 ^ ((31 - (bytesStoreSetByteIndexWord I).toNat) * 8) *
        (bytesStoreSetByteValueWord I).toNat +
      2 ^ (((31 - (bytesStoreSetByteIndexWord I).toNat) * 8) + 8) *
        ((bytesStorePacketLengthHeaderWord σ I).toNat /
          2 ^ (((31 - (bytesStoreSetByteIndexWord I).toNat) * 8) + 8)) =
      ((bytesStoreSetByteValueWord I).toNat *
          2 ^ ((31 - (bytesStoreSetByteIndexWord I).toNat) * 8)).lor
        ((((2 : Nat) ^ 256 - 1 -
          255 * 2 ^ ((31 - (bytesStoreSetByteIndexWord I).toNat) * 8)) &&&
          (bytesStorePacketLengthHeaderWord σ I).toNat) % UInt256.size) %
        UInt256.size
  rw [Nat.mod_eq_of_lt hrightLt]
  have hlorLt :
      ((bytesStoreSetByteValueWord I).toNat *
            2 ^ ((31 - (bytesStoreSetByteIndexWord I).toNat) * 8)).lor
          (((2 : Nat) ^ 256 - 1 -
              255 * 2 ^ ((31 - (bytesStoreSetByteIndexWord I).toNat) * 8)) &&&
            (bytesStorePacketLengthHeaderWord σ I).toNat) < UInt256.size := by
    change ((bytesStoreSetByteValueWord I).toNat *
          2 ^ ((31 - (bytesStoreSetByteIndexWord I).toNat) * 8)) |||
        (((2 : Nat) ^ 256 - 1 -
            255 * 2 ^ ((31 - (bytesStoreSetByteIndexWord I).toNat) * 8)) &&&
          (bytesStorePacketLengthHeaderWord σ I).toNat) < 2 ^ 256
    apply Nat.or_lt_two_pow
    · simpa [UInt256.size] using hleftLt
    · simpa [UInt256.size] using hrightLt
  rw [Nat.mod_eq_of_lt hlorLt]
  rw [show 2 ^ ((31 - (bytesStoreSetByteIndexWord I).toNat) * 8) *
        (bytesStoreSetByteValueWord I).toNat =
        (bytesStoreSetByteValueWord I).toNat *
          2 ^ ((31 - (bytesStoreSetByteIndexWord I).toNat) * 8) by ring]
  rw [show 2 ^ (((31 - (bytesStoreSetByteIndexWord I).toNat) * 8) + 8) *
        ((bytesStorePacketLengthHeaderWord σ I).toNat /
          2 ^ (((31 - (bytesStoreSetByteIndexWord I).toNat) * 8) + 8)) =
      (bytesStorePacketLengthHeaderWord σ I).toNat /
          2 ^ (((31 - (bytesStoreSetByteIndexWord I).toNat) * 8) + 8) *
        2 ^ (((31 - (bytesStoreSetByteIndexWord I).toNat) * 8) + 8) by ring]
  exact nat_byte_update_eq
    (old := (bytesStorePacketLengthHeaderWord σ I).toNat)
    (v := (bytesStoreSetByteValueWord I).toNat)
    (k := (31 - (bytesStoreSetByteIndexWord I).toNat) * 8)
    hv hk (by exact (bytesStorePacketLengthHeaderWord σ I).val.isLt)

theorem bytesStoreSetPacketByteLongStoredWord_toNat_update
    {σ : AccountMap} {I : ExecutionEnv}
    (hcanon : (bytesStoreSetByteValueWord I).toNat < EVM.twoPow 8) :
    (bytesStoreSetPacketByteLongOldWord σ I).toNat %
          2 ^ ((31 - (bytesStoreSetPacketByteLongWordIndex I).toNat) * 8) +
        2 ^ ((31 - (bytesStoreSetPacketByteLongWordIndex I).toNat) * 8) *
          (bytesStoreSetByteValueWord I).toNat +
      2 ^ ((31 - (bytesStoreSetPacketByteLongWordIndex I).toNat) * 8 + 8) *
        ((bytesStoreSetPacketByteLongOldWord σ I).toNat /
          2 ^ ((31 - (bytesStoreSetPacketByteLongWordIndex I).toNat) * 8 + 8)) =
    (bytesStoreSetPacketByteLongStoredWord σ I).toNat := by
  have hv : (bytesStoreSetByteValueWord I).toNat < 256 := by
    simpa [EVM.twoPow] using hcanon
  rw [bytesStoreSetPacketByteLongStoredWord, bytesStoreSetByteValueHighShiftDiv hcanon]
  rw [u256_lor_toNat, u256_mul_toNat, u256_land_toNat]
  rw [bytesStoreSetPacketByteLongScale_toNat (I := I)]
  rw [bytesStoreSetPacketByteLongClearMask_toNat (I := I)]
  have hidxLt : (bytesStoreSetPacketByteLongWordIndex I).toNat < 32 :=
    bytesStoreSetPacketByteLongWordIndex_lt32 I
  have hk : ((31 - (bytesStoreSetPacketByteLongWordIndex I).toNat) * 8) + 8 ≤ 256 := by
    omega
  have hleftLt : (bytesStoreSetByteValueWord I).toNat *
      2 ^ ((31 - (bytesStoreSetPacketByteLongWordIndex I).toNat) * 8) < UInt256.size := by
    rw [show UInt256.size = 2 ^ 256 from rfl]
    calc (bytesStoreSetByteValueWord I).toNat *
            2 ^ ((31 - (bytesStoreSetPacketByteLongWordIndex I).toNat) * 8) <
          256 * 2 ^ ((31 - (bytesStoreSetPacketByteLongWordIndex I).toNat) * 8) :=
            Nat.mul_lt_mul_of_pos_right hv (by positivity)
        _ = 2 ^ (8 + (31 - (bytesStoreSetPacketByteLongWordIndex I).toNat) * 8) := by
          rw [show 256 = 2 ^ 8 by norm_num, Nat.pow_add]
        _ ≤ 2 ^ 256 := by
          exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hrightLt : (((2 : Nat) ^ 256 - 1 -
        255 * 2 ^ ((31 - (bytesStoreSetPacketByteLongWordIndex I).toNat) * 8)) &&&
        (bytesStoreSetPacketByteLongOldWord σ I).toNat) < UInt256.size := by
    exact lt_of_le_of_lt Nat.and_le_right (bytesStoreSetPacketByteLongOldWord σ I).val.isLt
  rw [Nat.mod_eq_of_lt hleftLt]
  change (bytesStoreSetPacketByteLongOldWord σ I).toNat %
        2 ^ ((31 - (bytesStoreSetPacketByteLongWordIndex I).toNat) * 8) +
      2 ^ ((31 - (bytesStoreSetPacketByteLongWordIndex I).toNat) * 8) *
        (bytesStoreSetByteValueWord I).toNat +
      2 ^ (((31 - (bytesStoreSetPacketByteLongWordIndex I).toNat) * 8) + 8) *
        ((bytesStoreSetPacketByteLongOldWord σ I).toNat /
          2 ^ (((31 - (bytesStoreSetPacketByteLongWordIndex I).toNat) * 8) + 8)) =
      ((bytesStoreSetByteValueWord I).toNat *
          2 ^ ((31 - (bytesStoreSetPacketByteLongWordIndex I).toNat) * 8)).lor
        ((((2 : Nat) ^ 256 - 1 -
          255 * 2 ^ ((31 - (bytesStoreSetPacketByteLongWordIndex I).toNat) * 8)) &&&
          (bytesStoreSetPacketByteLongOldWord σ I).toNat) % UInt256.size) %
        UInt256.size
  rw [Nat.mod_eq_of_lt hrightLt]
  have hlorLt :
      ((bytesStoreSetByteValueWord I).toNat *
            2 ^ ((31 - (bytesStoreSetPacketByteLongWordIndex I).toNat) * 8)).lor
          (((2 : Nat) ^ 256 - 1 -
              255 * 2 ^ ((31 - (bytesStoreSetPacketByteLongWordIndex I).toNat) * 8)) &&&
            (bytesStoreSetPacketByteLongOldWord σ I).toNat) < UInt256.size := by
    change ((bytesStoreSetByteValueWord I).toNat *
          2 ^ ((31 - (bytesStoreSetPacketByteLongWordIndex I).toNat) * 8)) |||
        (((2 : Nat) ^ 256 - 1 -
            255 * 2 ^ ((31 - (bytesStoreSetPacketByteLongWordIndex I).toNat) * 8)) &&&
          (bytesStoreSetPacketByteLongOldWord σ I).toNat) < 2 ^ 256
    apply Nat.or_lt_two_pow
    · simpa [UInt256.size] using hleftLt
    · simpa [UInt256.size] using hrightLt
  rw [Nat.mod_eq_of_lt hlorLt]
  rw [show 2 ^ ((31 - (bytesStoreSetPacketByteLongWordIndex I).toNat) * 8) *
        (bytesStoreSetByteValueWord I).toNat =
        (bytesStoreSetByteValueWord I).toNat *
          2 ^ ((31 - (bytesStoreSetPacketByteLongWordIndex I).toNat) * 8) by ring]
  rw [show 2 ^ (((31 - (bytesStoreSetPacketByteLongWordIndex I).toNat) * 8) + 8) *
        ((bytesStoreSetPacketByteLongOldWord σ I).toNat /
          2 ^ (((31 - (bytesStoreSetPacketByteLongWordIndex I).toNat) * 8) + 8)) =
      (bytesStoreSetPacketByteLongOldWord σ I).toNat /
          2 ^ (((31 - (bytesStoreSetPacketByteLongWordIndex I).toNat) * 8) + 8) *
        2 ^ (((31 - (bytesStoreSetPacketByteLongWordIndex I).toNat) * 8) + 8) by ring]
  exact nat_byte_update_eq
    (old := (bytesStoreSetPacketByteLongOldWord σ I).toNat)
    (v := (bytesStoreSetByteValueWord I).toNat)
    (k := (31 - (bytesStoreSetPacketByteLongWordIndex I).toNat) * 8)
    hv hk (by exact (bytesStoreSetPacketByteLongOldWord σ I).val.isLt)

theorem bytesStoreSetPacketByteShortScale_mod256_zero {I : ExecutionEnv} {len : UInt256}
    (hshort : len.toNat < 32)
    (hbound : (bytesStoreSetByteIndexWord I).toNat < len.toNat) :
    (bytesStoreSetPacketByteShortScale I).toNat % 256 = 0 := by
  simpa [bytesStoreSetPacketByteShortScale, bytesStoreSetByteShortScale] using
    bytesStoreSetByteShortScale_mod256_zero (I := I) (len := len) hshort hbound

theorem bytesStoreSetPacketByteShortClearMask_mod256_255
    {I : ExecutionEnv} {len : UInt256}
    (hshort : len.toNat < 32)
    (hbound : (bytesStoreSetByteIndexWord I).toNat < len.toNat) :
    (UInt256.lnot (UInt256.mul ⟨255⟩ (bytesStoreSetPacketByteShortScale I))).toNat % 256 =
      255 := by
  simpa [bytesStoreSetPacketByteShortScale, bytesStoreSetByteShortScale] using
    bytesStoreSetByteShortClearMask_mod256_255 (I := I) (len := len) hshort hbound

theorem bytesStoreSetPacketByteShortStoredWord_mod256
    {σ : AccountMap} {I : ExecutionEnv} {len : UInt256}
    (hshort : len.toNat < 32)
    (hbound : (bytesStoreSetByteIndexWord I).toNat < len.toNat) :
    (bytesStoreSetPacketByteShortStoredWord σ I).toNat % 256 =
      (bytesStorePacketLengthHeaderWord σ I).toNat % 256 := by
  have hscale := bytesStoreSetPacketByteShortScale_mod256_zero
    (I := I) (len := len) hshort hbound
  have hmask := bytesStoreSetPacketByteShortClearMask_mod256_255
    (I := I) (len := len) hshort hbound
  have hleft :
      (UInt256.mul
        (UInt256.div (UInt256.shiftLeft (bytesStoreSetByteValueWord I) ⟨248⟩)
          (UInt256.shiftLeft ⟨1⟩ ⟨248⟩))
        (bytesStoreSetPacketByteShortScale I)).toNat % 256 = 0 := by
    rw [u256_mul_toNat, nat_mod_u256_mod_256, Nat.mul_mod, hscale]
    simp
  have hright :
      (UInt256.land
        (UInt256.lnot (UInt256.mul ⟨255⟩ (bytesStoreSetPacketByteShortScale I)))
        (bytesStorePacketLengthHeaderWord σ I)).toNat % 256 =
        (bytesStorePacketLengthHeaderWord σ I).toNat % 256 := by
    rw [u256_land_toNat, nat_mod_u256_mod_256]
    exact nat_land_mod_256_of_left_255 hmask
  rw [bytesStoreSetPacketByteShortStoredWord, u256_lor_toNat, nat_mod_u256_mod_256]
  rw [nat_lor_mod_256_of_left_zero hleft, hright]

theorem bytesStoreSetPacketByteShortStoredWord_flag_eq
    {σ : AccountMap} {I : ExecutionEnv} {len : UInt256}
    (hshort : len.toNat < 32)
    (hbound : (bytesStoreSetByteIndexWord I).toNat < len.toNat) :
    UInt256.land (bytesStoreSetPacketByteShortStoredWord σ I) ⟨1⟩ =
      UInt256.land (bytesStorePacketLengthHeaderWord σ I) ⟨1⟩ := by
  apply u256_inj
  rw [uInt256_land_one_toNat, uInt256_land_one_toNat]
  have hmod := bytesStoreSetPacketByteShortStoredWord_mod256
    (σ := σ) (I := I) (len := len) hshort hbound
  have hleft :
      (bytesStoreSetPacketByteShortStoredWord σ I).toNat % 2 =
        ((bytesStoreSetPacketByteShortStoredWord σ I).toNat % 256) % 2 := by
    rw [Nat.mod_mod_of_dvd]
    norm_num
  have hright :
      (bytesStorePacketLengthHeaderWord σ I).toNat % 2 =
        ((bytesStorePacketLengthHeaderWord σ I).toNat % 256) % 2 := by
    rw [Nat.mod_mod_of_dvd]
    norm_num
  rw [hleft, hright, hmod]

theorem bytesStoreSetPacketByteShortStoredWord_shortLen_eq
    {σ : AccountMap} {I : ExecutionEnv} {len : UInt256}
    (hshort : len.toNat < 32)
    (hbound : (bytesStoreSetByteIndexWord I).toNat < len.toNat) :
    UInt256.land (UInt256.div (bytesStoreSetPacketByteShortStoredWord σ I) ⟨2⟩) ⟨127⟩ =
      UInt256.land (UInt256.div (bytesStorePacketLengthHeaderWord σ I) ⟨2⟩) ⟨127⟩ := by
  apply u256_inj
  rw [bytesStoreShortLenBits_toNat, bytesStoreShortLenBits_toNat]
  rw [bytesStoreSetPacketByteShortStoredWord_mod256 (σ := σ) (I := I) (len := len)
    hshort hbound]

theorem bytesStoreSetPacketByteShortStoredWord_ne_zero
    {σ : AccountMap} {I : ExecutionEnv} {len : UInt256}
    (hlen : len =
      UInt256.land (UInt256.div (bytesStorePacketLengthHeaderWord σ I) ⟨2⟩) ⟨127⟩)
    (hshort : len.toNat < 32)
    (hbound : (bytesStoreSetByteIndexWord I).toNat < len.toNat) :
    bytesStoreSetPacketByteShortStoredWord σ I ≠ ⟨0⟩ := by
  intro hzero
  have hshortLen := bytesStoreSetPacketByteShortStoredWord_shortLen_eq
    (σ := σ) (I := I) (len := len) hshort hbound
  rw [hzero] at hshortLen
  have hlenZero : len.toNat = 0 := by
    rw [hlen, ← hshortLen]
    native_decide
  omega

theorem bytesStoreSetPacketByteShortStoredWord_beq_zero_false
    {σ : AccountMap} {I : ExecutionEnv} {len : UInt256}
    (hlen : len =
      UInt256.land (UInt256.div (bytesStorePacketLengthHeaderWord σ I) ⟨2⟩) ⟨127⟩)
    (hshort : len.toNat < 32)
    (hbound : (bytesStoreSetByteIndexWord I).toNat < len.toNat) :
    (bytesStoreSetPacketByteShortStoredWord σ I == (default : UInt256)) = false := by
  exact beq_false_of_ne
    (bytesStoreSetPacketByteShortStoredWord_ne_zero (σ := σ) (I := I) (len := len)
      hlen hshort hbound)

theorem bytesStoreSetPacketByte_storageTypeAt {I : ExecutionEnv} :
    storageTypeAt? bytesStoreContract.storage (bytesStoreSetPacketByteRef I) =
      some uint8St := by
  simp [bytesStoreSetPacketByteRef, storageTypeAt?, bytesStoreContract, storageDecls,
    packetStructDecl, packetStructTy, bytesSt, uint8St, uint8Int, storageTypeStep?]

theorem bytesStoreSetPacketByteLayoutShort {evm : EVM.State} {I : ExecutionEnv}
    (hpacked : checkBytesPacked ⟨2⟩ evm = true)
    (hidx : (bytesStoreSetByteIndexWord I).toNat < 31) :
    bytesStoreConfig.storage.layout (bytesStoreSetPacketByteRef I) evm =
      some (uint8Loc ⟨2⟩ ⟨31 - (bytesStoreSetByteIndexWord I).toNat, by omega⟩) := by
  simp [bytesStoreConfig, bytesStoreStorageLayout, solidityStorageLayout,
    bytesStoreLayout, bytesStoreSetPacketByteRef, bytesLikeByteLoc?, uint8Loc,
    uint8Int, hpacked, hidx]

theorem bytesStoreSetPacketByteLayoutLong {evm : EVM.State} {I : ExecutionEnv}
    (hpacked : checkBytesPacked ⟨2⟩ evm = false) :
    bytesStoreConfig.storage.layout (bytesStoreSetPacketByteRef I) evm =
      some (uint8Loc (bytesStoreSetPacketByteLongDataSlot I)
        ⟨31 - (bytesStoreSetPacketByteLongWordIndex I).toNat, by
          have hidx := bytesStoreSetPacketByteLongWordIndex_lt32 I
          omega⟩) := by
  rw [bytesStoreSetPacketByteLongDataSlot, u256_div32_eq_ofNat_toNat_div]
  simp [bytesStoreConfig, bytesStoreStorageLayout, solidityStorageLayout,
    bytesStoreLayout, bytesStoreSetPacketByteRef, bytesLikeByteLoc?, uint8Loc,
    uint8Int, hpacked, bytesStoreSetPacketByteLongWordIndex_toNat]

theorem bytesStoreSetPacketByteStorageLocStoreShort
    {evm : EVM.State} {σ : AccountMap} {I : ExecutionEnv} {len : UInt256}
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩ =
      bytesStorePacketLengthHeaderWord σ I)
    (hcanon : (bytesStoreSetByteValueWord I).toNat < EVM.twoPow 8)
    (hshort : len.toNat < 32)
    (hbound : (bytesStoreSetByteIndexWord I).toNat < len.toNat) :
    storageLocStore evm
      (uint8Loc ⟨2⟩ ⟨31 - (bytesStoreSetByteIndexWord I).toNat, by
        have hidx := bytesStoreSetByteIndex_lt31_of_short_bound
          (I := I) (len := len) hshort hbound
        omega⟩)
      (bytesStoreSetPacketByteValue I) =
      some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨2⟩
        (bytesStoreSetPacketByteShortStoredWord σ I)) := by
  let offFin : Fin 32 :=
    ⟨31 - (bytesStoreSetByteIndexWord I).toNat, by
      have hidx := bytesStoreSetByteIndex_lt31_of_short_bound
        (I := I) (len := len) hshort hbound
      omega⟩
  have hval : valueToWord (bytesStoreSetPacketByteValue I) =
      some (UInt256.ofNat (bytesStoreSetByteValueWord I).toNat) := by
    simp [bytesStoreSetPacketByteValue, valueToWord]
    exact bytesStoreWordOfIntOfNatEq (bytesStoreSetByteValueWord I).toNat
  have hoffVal : offFin.val = 31 - (bytesStoreSetByteIndexWord I).toNat := by
    rfl
  have hoffLe : offFin.val ≤ 32 := Nat.le_of_lt offFin.isLt
  have hv : (bytesStoreSetByteValueWord I).toNat < 256 := by
    simpa [EVM.twoPow] using hcanon
  have hoffBound : offFin.val + (1 : Fin 33).val - 1 < 32 := by
    have hidx := bytesStoreSetByteIndex_lt31_of_short_bound
      (I := I) (len := len) hshort hbound
    simp [offFin]
    omega
  have htarget :
      (bytesStoreSetPacketByteShortStoredWord σ I).toNat =
        fromBytes'
          ((EVM.Word.toBytesLEWithSizeProof
                (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩)).1.take offFin.val ++
           (EVM.Word.toBytesLEWithSizeProof
                (storageLocWriteWord
                  (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩)
                  offFin.val none
                  (UInt256.ofNat (bytesStoreSetByteValueWord I).toNat))).1.take 1 ++
           (EVM.Word.toBytesLEWithSizeProof
                (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩)).1.drop
              (offFin.val + 1)) := by
    rw [hload]
    simp only [storageLocWriteWord]
    symm
    rw [fromBytes'_append, fromBytes'_append]
    rw [fromBytes'_take_wordLE, fromBytes'_take_wordLE, fromBytes'_drop_wordLE]
    have hslen := (EVM.Word.toBytesLEWithSizeProof
      (bytesStorePacketLengthHeaderWord σ I)).2
    have hvlen := (EVM.Word.toBytesLEWithSizeProof
      (UInt256.ofNat (bytesStoreSetByteValueWord I).toNat)).2
    rw [List.length_take, hslen, Nat.min_eq_left hoffLe]
    rw [List.length_append, List.length_take, hslen, Nat.min_eq_left hoffLe,
      List.length_take, hvlen, Nat.min_eq_left (by norm_num : 1 ≤ 32)]
    rw [show 8 * (offFin.val + 1) = 8 * offFin.val + 8 by ring]
    rw [show 256 ^ offFin.val = 2 ^ (8 * offFin.val) by
      rw [show (256 : Nat) = 2 ^ 8 by norm_num, ← Nat.pow_mul]]
    rw [show 256 ^ 1 = 256 by norm_num]
    rw [show (UInt256.ofNat (bytesStoreSetByteValueWord I).toNat).toNat % 256 =
        (bytesStoreSetByteValueWord I).toNat by
      rw [ulit_toNat' _ (lt_of_lt_of_le hv (by norm_num [UInt256.size]))]
      exact Nat.mod_eq_of_lt hv]
    rw [hoffVal]
    rw [show 8 * (31 - (bytesStoreSetByteIndexWord I).toNat) =
        (31 - (bytesStoreSetByteIndexWord I).toNat) * 8 by ring]
    rw [show 256 ^ (31 - (bytesStoreSetByteIndexWord I).toNat + 1) =
        2 ^ (((31 - (bytesStoreSetByteIndexWord I).toNat) * 8) + 8) by
      rw [show 256 = 2 ^ 8 by norm_num, ← Nat.pow_mul]
      congr 1
      ring]
    change
      (bytesStorePacketLengthHeaderWord σ I).toNat %
            2 ^ ((31 - (bytesStoreSetByteIndexWord I).toNat) * 8) +
          2 ^ ((31 - (bytesStoreSetByteIndexWord I).toNat) * 8) *
            (bytesStoreSetByteValueWord I).toNat +
        2 ^ ((31 - (bytesStoreSetByteIndexWord I).toNat) * 8 + 8) *
          ((bytesStorePacketLengthHeaderWord σ I).toNat /
            2 ^ ((31 - (bytesStoreSetByteIndexWord I).toNat) * 8 + 8)) =
      (bytesStoreSetPacketByteShortStoredWord σ I).toNat
    exact bytesStoreSetPacketByteShortStoredWord_toNat_update
      (σ := σ) (I := I) (len := len) hcanon hshort hbound
  change storageLocStore evm
      { slot := ⟨2⟩, offset := offFin, size := 1, hbound := hoffBound,
        type := .int uint8Int }
      (bytesStoreSetPacketByteValue I) =
      some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨2⟩
        (bytesStoreSetPacketByteShortStoredWord σ I))
  exact storageLocStore_oneByte_local evm ⟨2⟩
    (UInt256.ofNat (bytesStoreSetByteValueWord I).toNat)
    (bytesStoreSetPacketByteShortStoredWord σ I)
    offFin (.int uint8Int) hoffBound
    (bytesStoreSetPacketByteValue I) hval htarget

theorem bytesStoreSetPacketByteStorageLocStoreLong
    {evm : EVM.State} {σ : AccountMap} {I : ExecutionEnv}
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (bytesStoreSetPacketByteLongDataSlot I) =
      bytesStoreSetPacketByteLongOldWord σ I)
    (hcanon : (bytesStoreSetByteValueWord I).toNat < EVM.twoPow 8) :
    storageLocStore evm
      (uint8Loc (bytesStoreSetPacketByteLongDataSlot I)
        ⟨31 - (bytesStoreSetPacketByteLongWordIndex I).toNat, by
          have hidx := bytesStoreSetPacketByteLongWordIndex_lt32 I
          omega⟩)
      (bytesStoreSetPacketByteValue I) =
      some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner
        (bytesStoreSetPacketByteLongDataSlot I)
        (bytesStoreSetPacketByteLongStoredWord σ I)) := by
  let offFin : Fin 32 :=
    ⟨31 - (bytesStoreSetPacketByteLongWordIndex I).toNat, by
      have hidx := bytesStoreSetPacketByteLongWordIndex_lt32 I
      omega⟩
  have hval : valueToWord (bytesStoreSetPacketByteValue I) =
      some (UInt256.ofNat (bytesStoreSetByteValueWord I).toNat) := by
    simp [bytesStoreSetPacketByteValue, valueToWord]
    exact bytesStoreWordOfIntOfNatEq (bytesStoreSetByteValueWord I).toNat
  have hoffVal : offFin.val = 31 - (bytesStoreSetPacketByteLongWordIndex I).toNat := by
    rfl
  have hoffLe : offFin.val ≤ 32 := Nat.le_of_lt offFin.isLt
  have hv : (bytesStoreSetByteValueWord I).toNat < 256 := by
    simpa [EVM.twoPow] using hcanon
  have hoffBound : offFin.val + (1 : Fin 33).val - 1 < 32 := by
    simp [offFin]
    omega
  have htarget :
      (bytesStoreSetPacketByteLongStoredWord σ I).toNat =
        fromBytes'
          ((EVM.Word.toBytesLEWithSizeProof
                (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
                  (bytesStoreSetPacketByteLongDataSlot I))).1.take offFin.val ++
           (EVM.Word.toBytesLEWithSizeProof
                (storageLocWriteWord
                  (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
                    (bytesStoreSetPacketByteLongDataSlot I))
                  offFin.val none
                  (UInt256.ofNat (bytesStoreSetByteValueWord I).toNat))).1.take 1 ++
           (EVM.Word.toBytesLEWithSizeProof
                (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
                  (bytesStoreSetPacketByteLongDataSlot I))).1.drop
              (offFin.val + 1)) := by
    rw [hload]
    simp only [storageLocWriteWord]
    symm
    rw [fromBytes'_append, fromBytes'_append]
    rw [fromBytes'_take_wordLE, fromBytes'_take_wordLE, fromBytes'_drop_wordLE]
    have hslen := (EVM.Word.toBytesLEWithSizeProof
      (bytesStoreSetPacketByteLongOldWord σ I)).2
    have hvlen := (EVM.Word.toBytesLEWithSizeProof
      (UInt256.ofNat (bytesStoreSetByteValueWord I).toNat)).2
    rw [List.length_take, hslen, Nat.min_eq_left hoffLe]
    rw [List.length_append, List.length_take, hslen, Nat.min_eq_left hoffLe,
      List.length_take, hvlen, Nat.min_eq_left (by norm_num : 1 ≤ 32)]
    rw [show 8 * (offFin.val + 1) = 8 * offFin.val + 8 by ring]
    rw [show 256 ^ offFin.val = 2 ^ (8 * offFin.val) by
      rw [show (256 : Nat) = 2 ^ 8 by norm_num, ← Nat.pow_mul]]
    rw [show 256 ^ 1 = 256 by norm_num]
    rw [show (UInt256.ofNat (bytesStoreSetByteValueWord I).toNat).toNat % 256 =
        (bytesStoreSetByteValueWord I).toNat by
      rw [ulit_toNat' _ (lt_of_lt_of_le hv (by norm_num [UInt256.size]))]
      exact Nat.mod_eq_of_lt hv]
    rw [hoffVal]
    rw [show 8 * (31 - (bytesStoreSetPacketByteLongWordIndex I).toNat) =
        (31 - (bytesStoreSetPacketByteLongWordIndex I).toNat) * 8 by ring]
    rw [show 256 ^ (31 - (bytesStoreSetPacketByteLongWordIndex I).toNat + 1) =
        2 ^ (((31 - (bytesStoreSetPacketByteLongWordIndex I).toNat) * 8) + 8) by
      rw [show 256 = 2 ^ 8 by norm_num, ← Nat.pow_mul]
      congr 1
      ring]
    change
      (bytesStoreSetPacketByteLongOldWord σ I).toNat %
            2 ^ ((31 - (bytesStoreSetPacketByteLongWordIndex I).toNat) * 8) +
          2 ^ ((31 - (bytesStoreSetPacketByteLongWordIndex I).toNat) * 8) *
            (bytesStoreSetByteValueWord I).toNat +
        2 ^ ((31 - (bytesStoreSetPacketByteLongWordIndex I).toNat) * 8 + 8) *
          ((bytesStoreSetPacketByteLongOldWord σ I).toNat /
            2 ^ ((31 - (bytesStoreSetPacketByteLongWordIndex I).toNat) * 8 + 8)) =
      (bytesStoreSetPacketByteLongStoredWord σ I).toNat
    exact bytesStoreSetPacketByteLongStoredWord_toNat_update
      (σ := σ) (I := I) hcanon
  change storageLocStore evm
      { slot := bytesStoreSetPacketByteLongDataSlot I, offset := offFin, size := 1,
        hbound := hoffBound, type := .int uint8Int }
      (bytesStoreSetPacketByteValue I) =
      some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner
        (bytesStoreSetPacketByteLongDataSlot I)
        (bytesStoreSetPacketByteLongStoredWord σ I))
  exact storageLocStore_oneByte_local evm (bytesStoreSetPacketByteLongDataSlot I)
    (UInt256.ofNat (bytesStoreSetByteValueWord I).toNat)
    (bytesStoreSetPacketByteLongStoredWord σ I)
    offFin (.int uint8Int) hoffBound
    (bytesStoreSetPacketByteValue I) hval htarget

theorem bytesStoreSetPacketByteEvalStorageRefOfLength {evm : EVM.State} {I : ExecutionEnv}
    {len : Nat}
    (hlen : readStorageBytesLength? bytesStoreConfig evm
      { base := "packet", steps := [.field "data"] } = .ok len)
    (hbound : (bytesStoreSetByteIndexWord I).toNat < len) :
    evalStorageRef bytesStoreConfig
      (bytesStoreSetPacketByteFrame I)
      evm (packetDataByteRef (.var "byteIndex")) =
        .ok (bytesStoreSetPacketByteRef I) := by
  have hstep :
      evalStorageRefStep bytesStoreConfig (bytesStoreSetPacketByteFrame I) evm
        "packet" [] (.field "data") = .ok (.field "data") := by
    simp [evalStorageRefStep, pure]
  have hgetIndex :
      (bytesStoreSetPacketByteLocals I).get? "byteIndex" =
        some (.int (Int.ofNat (bytesStoreSetByteIndexWord I).toNat)) :=
    bytesStoreSetPacketByteLocals_get_byteIndex I
  have hlen' :
      readStorageBytesLength?
        { storage := bytesStoreStorageLayout, externalABI := defaultExternalCallABI,
          selfDeployment := genSolidityConstructorDeployment [] }
        evm { base := "packet", steps := [.field "data"] } = .ok len := by
    simpa [bytesStoreConfig] using hlen
  have hkey :
      valueToKey? (.int (Int.ofNat (bytesStoreSetByteIndexWord I).toNat)) =
        some (.int (Int.ofNat (bytesStoreSetByteIndexWord I).toNat)) := by
    simp [valueToKey?]
  have hbounds :
      arrayIndexInBounds? bytesStoreConfig evm
        (bytesStoreSetPacketByteFrame I).contract.storage "packet" [.field "data"]
        (.int (Int.ofNat (bytesStoreSetByteIndexWord I).toNat)) = .ok () := by
    simpa [arrayIndexInBounds?, storageTypeAt?, bytesStoreConfig,
      bytesStoreSetPacketByteFrame, bytesStoreContract, storageDecls,
      packetStructDecl, packetStructTy, bytesSt, storageTypeStep?, hlen'] using hbound
  simpa [packetDataByteRef, bytesStoreSetPacketByteFrame, bytesStoreSetPacketByteRef] using
    (evalStorageRef_step_aindex_var_of_get?_ok
      (cfg := bytesStoreConfig) (solm := bytesStoreSetPacketByteFrame I)
      (evm := evm) (base := "packet") (name := "byteIndex")
      (step := .field "data") (estep := .field "data")
      hstep hgetIndex hkey hbounds)

theorem bytesStoreSetPacketByteEvalStorageRefRevertsOfLength
    {evm : EVM.State} {I : ExecutionEnv} {len : Nat}
    (hlen : readStorageBytesLength? bytesStoreConfig evm
      { base := "packet", steps := [.field "data"] } = .ok len)
    (hbound : ¬ (bytesStoreSetByteIndexWord I).toNat < len) :
    evalStorageRef bytesStoreConfig
      { contract := bytesStoreContract, locals := bytesStoreSetPacketByteLocals I }
      evm (packetDataByteRef (.var "byteIndex")) = .revert := by
  have hstep :
      evalStorageRefStep bytesStoreConfig
        { contract := bytesStoreContract, locals := bytesStoreSetPacketByteLocals I }
        evm "packet" [] (.field "data") = .ok (.field "data") := by
    simp [evalStorageRefStep, pure]
  have hgetIndex :
      (bytesStoreSetPacketByteLocals I).get? "byteIndex" =
        some (.int (Int.ofNat (bytesStoreSetByteIndexWord I).toNat)) :=
    bytesStoreSetPacketByteLocals_get_byteIndex I
  have hlen' :
      readStorageBytesLength?
        { storage := bytesStoreStorageLayout, externalABI := defaultExternalCallABI,
          selfDeployment := genSolidityConstructorDeployment [] }
        evm { base := "packet", steps := [.field "data"] } = .ok len := by
    simpa [bytesStoreConfig] using hlen
  have hkey :
      valueToKey? (.int (Int.ofNat (bytesStoreSetByteIndexWord I).toNat)) =
        some (.int (Int.ofNat (bytesStoreSetByteIndexWord I).toNat)) := by
    simp [valueToKey?]
  have hbounds :
      arrayIndexInBounds? bytesStoreConfig evm bytesStoreContract.storage
        "packet" [.field "data"]
        (.int (Int.ofNat (bytesStoreSetByteIndexWord I).toNat)) = .revert := by
    simpa [arrayIndexInBounds?, storageTypeAt?, bytesStoreConfig,
      bytesStoreContract, storageDecls, packetStructDecl, packetStructTy,
      bytesSt, storageTypeStep?, hlen'] using Nat.le_of_not_gt hbound
  simpa [packetDataByteRef] using
    (evalStorageRef_step_aindex_var_of_get?_revert
      (cfg := bytesStoreConfig)
      (solm := { contract := bytesStoreContract, locals := bytesStoreSetPacketByteLocals I })
      (evm := evm) (base := "packet") (name := "byteIndex")
      (step := .field "data") (estep := .field "data")
      hstep hgetIndex hkey hbounds)

theorem bytesStoreSetPacketByteEvalStorageRefRevertsOfLengthRead
    {evm : EVM.State} {I : ExecutionEnv}
    (hlen : readStorageBytesLength? bytesStoreConfig evm
      { base := "packet", steps := [.field "data"] } = .revert) :
    evalStorageRef bytesStoreConfig
      { contract := bytesStoreContract, locals := bytesStoreSetPacketByteLocals I }
      evm (packetDataByteRef (.var "byteIndex")) = .revert := by
  have hstep :
      evalStorageRefStep bytesStoreConfig
        { contract := bytesStoreContract, locals := bytesStoreSetPacketByteLocals I }
        evm "packet" [] (.field "data") = .ok (.field "data") := by
    simp [evalStorageRefStep, pure]
  have hgetIndex :
      (bytesStoreSetPacketByteLocals I).get? "byteIndex" =
        some (.int (Int.ofNat (bytesStoreSetByteIndexWord I).toNat)) :=
    bytesStoreSetPacketByteLocals_get_byteIndex I
  have hlen' :
      readStorageBytesLength?
        { storage := bytesStoreStorageLayout, externalABI := defaultExternalCallABI,
          selfDeployment := genSolidityConstructorDeployment [] }
        evm { base := "packet", steps := [.field "data"] } = .revert := by
    simpa [bytesStoreConfig] using hlen
  have hkey :
      valueToKey? (.int (Int.ofNat (bytesStoreSetByteIndexWord I).toNat)) =
        some (.int (Int.ofNat (bytesStoreSetByteIndexWord I).toNat)) := by
    simp [valueToKey?]
  have hbounds :
      arrayIndexInBounds? bytesStoreConfig evm bytesStoreContract.storage
        "packet" [.field "data"]
        (.int (Int.ofNat (bytesStoreSetByteIndexWord I).toNat)) = .revert := by
    simp [arrayIndexInBounds?, storageTypeAt?, bytesStoreConfig,
      bytesStoreContract, storageDecls, packetStructDecl, packetStructTy,
      bytesSt, storageTypeStep?, hlen']
  simpa [packetDataByteRef] using
    (evalStorageRef_step_aindex_var_of_get?_revert
      (cfg := bytesStoreConfig)
      (solm := { contract := bytesStoreContract, locals := bytesStoreSetPacketByteLocals I })
      (evm := evm) (base := "packet") (name := "byteIndex")
      (step := .field "data") (estep := .field "data")
      hstep hgetIndex hkey hbounds)

theorem bytesStoreSetPacketByteResolveOfLength {evm : EVM.State} {I : ExecutionEnv}
    {len : Nat}
    (hlen : readStorageBytesLength? bytesStoreConfig evm
      { base := "packet", steps := [.field "data"] } = .ok len)
    (hbound : (bytesStoreSetByteIndexWord I).toNat < len) :
    resolveStorageRef? bytesStoreConfig
      (bytesStoreSetPacketByteFrame I)
      evm (packetDataByteRef (.var "byteIndex")) =
        .ok (bytesStoreSetPacketByteRef I, uint8St) := by
  have hgetPacket :
      (bytesStoreSetPacketByteLocals I).get? "packet" = none :=
    bytesStoreSetPacketByteLocals_get_packet_none I
  have herInline' :
      evalStorageRef bytesStoreConfig
        { contract := bytesStoreContract, locals := bytesStoreSetPacketByteLocals I }
        evm { base := "packet", steps := [.field "data", .aindex (.var "byteIndex")] } =
          .ok (bytesStoreSetPacketByteRef I) := by
    simpa [packetDataByteRef, bytesStoreSetPacketByteFrame] using
      (bytesStoreSetPacketByteEvalStorageRefOfLength
        (evm := evm) (I := I) (len := len) hlen hbound)
  exact resolveStorageRef?_ok hgetPacket herInline'
    bytesStoreSetPacketByte_storageTypeAt

theorem bytesStoreSetPacketByteAssignOfLength {evm evm' : EVM.State}
    {I : ExecutionEnv} {len : Nat}
    (hlen : readStorageBytesLength? bytesStoreConfig evm
      { base := "packet", steps := [.field "data"] } = .ok len)
    (hbound : (bytesStoreSetByteIndexWord I).toNat < len)
    (hstore :
      (match bytesStoreConfig.storage.layout (bytesStoreSetPacketByteRef I) evm with
      | some loc => storageLocStore evm loc (bytesStoreSetPacketByteValue I)
      | none => none) = some evm') :
    assignStorageRef? bytesStoreConfig
      (bytesStoreSetPacketByteFrame I)
      evm .storage (packetDataByteRef (.var "byteIndex")) (bytesStoreSetPacketByteValue I) =
        .ok (bytesStoreSetPacketByteFrame I, evm') := by
  exact assignStorageRef_storage_scalar_ok_of_resolve_match_store
    (bytesStoreSetPacketByteResolveOfLength (I := I) hlen hbound)
    hstore
    (by simp [bytesStoreSetPacketByteValue])

theorem bytesStoreSetPacketByteBodyReturns {evm evm' : EVM.State} {I : ExecutionEnv}
    {ret : Value}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hassign :
      assignStorageRef? bytesStoreConfig
        (bytesStoreSetPacketByteFrame I)
        evm .storage (packetDataByteRef (.var "byteIndex"))
          (bytesStoreSetPacketByteValue I) =
          .ok (bytesStoreSetPacketByteFrame I, evm'))
    (hret :
      evalExpr? bytesStoreConfig
        (bytesStoreSetPacketByteFrame I)
        evm' (.storage (packetDataByteRef (.var "byteIndex"))) = .ok ret) :
    ExecTransitionBody bytesStoreConfig bytesStoreContract evm
      (bytesStoreSetPacketByteLocals I) setPacketByteTransition.body
      (.returned
        (bytesStoreSetPacketByteFrame I)
        evm' (some ret)) := by
  let solm : Frame := bytesStoreSetPacketByteFrame I
  have hvalue :
      evalExpr? bytesStoreConfig solm evm (.var "value") =
        .ok (bytesStoreSetPacketByteValue I) := by
    exact evalExpr_var_of_get? (by
      simp [solm, bytesStoreSetPacketByteFrame, bytesStoreSetPacketByteValue,
        bytesStoreSetPacketByteLocals])
  have hassign :
      assignStorageRef? bytesStoreConfig solm evm .storage
        (packetDataByteRef (.var "byteIndex")) (bytesStoreSetPacketByteValue I) =
          .ok (solm, evm') := by
    simpa [solm] using hassign
  have hret :
      evalExpr? bytesStoreConfig solm evm'
        (.storage (packetDataByteRef (.var "byteIndex"))) = .ok ret := by
    simpa [solm] using hret
  exact ExecFuncBody.execBlockRet <|
    ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consNormal (ExecStmt.assign hvalue hassign) <|
        ExecBlock.consReturn (ExecStmt.return hret)

theorem bytesStoreSetPacketByteBodyReturnReverts {evm evm' : EVM.State}
    {I : ExecutionEnv}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hassign :
      assignStorageRef? bytesStoreConfig
        (bytesStoreSetPacketByteFrame I)
        evm .storage (packetDataByteRef (.var "byteIndex"))
          (bytesStoreSetPacketByteValue I) =
          .ok (bytesStoreSetPacketByteFrame I, evm'))
    (hret :
      evalExpr? bytesStoreConfig
        (bytesStoreSetPacketByteFrame I)
        evm' (.storage (packetDataByteRef (.var "byteIndex"))) = .revert) :
    ExecTransitionBody bytesStoreConfig bytesStoreContract evm
      (bytesStoreSetPacketByteLocals I) setPacketByteTransition.body .reverted := by
  let solm : Frame := bytesStoreSetPacketByteFrame I
  have hvalue :
      evalExpr? bytesStoreConfig solm evm (.var "value") =
        .ok (bytesStoreSetPacketByteValue I) := by
    exact evalExpr_var_of_get? (by
      simp [solm, bytesStoreSetPacketByteFrame, bytesStoreSetPacketByteValue,
        bytesStoreSetPacketByteLocals])
  have hassign :
      assignStorageRef? bytesStoreConfig solm evm .storage
        (packetDataByteRef (.var "byteIndex")) (bytesStoreSetPacketByteValue I) =
          .ok (solm, evm') := by
    simpa [solm] using hassign
  have hret :
      evalExpr? bytesStoreConfig solm evm'
        (.storage (packetDataByteRef (.var "byteIndex"))) = .revert := by
    simpa [solm] using hret
  exact ExecFuncBody.execBlockRevert <|
    ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consNormal (ExecStmt.assign hvalue hassign) <|
        ExecBlock.consRevert (ExecStmt.returnRevert hret)

theorem bytesStoreSetPacketByteShortBodyReturns
    {evm : EVM.State} {σ : AccountMap} {I : ExecutionEnv} {len : UInt256} {acc : Account}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩ =
      bytesStorePacketLengthHeaderWord σ I)
    (hacc : evm.accountMap.find? evm.executionEnv.codeOwner = some acc)
    (hcanon : (bytesStoreSetByteValueWord I).toNat < EVM.twoPow 8)
    (hlen : len =
      UInt256.land (UInt256.div (bytesStorePacketLengthHeaderWord σ I) ⟨2⟩) ⟨127⟩)
    (hshort : len.toNat < 32)
    (hbound : (bytesStoreSetByteIndexWord I).toNat < len.toNat)
    (hflag : UInt256.land (bytesStorePacketLengthHeaderWord σ I) ⟨1⟩ = ⟨0⟩)
    (_hvalid : UInt256.sub (UInt256.land (bytesStorePacketLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStorePacketLengthHeaderWord σ I) ⟨2⟩) ⟨127⟩)
          ⟨32⟩) ≠ ⟨0⟩) :
    ExecTransitionBody bytesStoreConfig bytesStoreContract evm
      (bytesStoreSetPacketByteLocals I) setPacketByteTransition.body
      (.returned
        (bytesStoreSetPacketByteFrame I)
        (Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨2⟩
          (bytesStoreSetPacketByteShortStoredWord σ I))
        (some (bytesStoreSetPacketByteValue I))) := by
  let evm' := Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨2⟩
    (bytesStoreSetPacketByteShortStoredWord σ I)
  have hlenRead :
      readStorageBytesLength? bytesStoreConfig evm
          { base := "packet", steps := [.field "data"] } =
        .ok len.toNat := by
    have hltLen : UInt256.lt len ⟨32⟩ = ⟨1⟩ := by
      exact ult_one (by
        simpa [show (⟨32⟩ : UInt256).toNat = 32 from by decide] using hshort)
    have hvalidLen : UInt256.sub ⟨0⟩ (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩ := by
      rw [hltLen]
      native_decide
    exact bytesStoreReadLengthOfHeaderLoad
      (er := bytesStorePacketDataRef) (evm := evm)
      (baseSlot := ⟨2⟩) (header := bytesStorePacketLengthHeaderWord σ I)
      (len := len.toNat)
      (bytesStorePacketDataRef_length_slot evm) hload
      (solidityDecodeBytesLengthHeader_short_valid hflag hlen (by simpa [hflag] using hvalidLen))
  have hpacked : checkBytesPacked ⟨2⟩ evm = true :=
    checkBytesPacked_of_storageLoad_land_one_zero hload hflag
  have hidx31 : (bytesStoreSetByteIndexWord I).toNat < 31 :=
    bytesStoreSetByteIndex_lt31_of_short_bound (I := I) (len := len) hshort hbound
  have hlayout :
      bytesStoreConfig.storage.layout (bytesStoreSetPacketByteRef I) evm =
        some (uint8Loc ⟨2⟩ ⟨31 - (bytesStoreSetByteIndexWord I).toNat, by omega⟩) :=
    bytesStoreSetPacketByteLayoutShort (evm := evm) (I := I) hpacked hidx31
  have hstore :
      (match bytesStoreConfig.storage.layout (bytesStoreSetPacketByteRef I) evm with
      | some loc => storageLocStore evm loc (bytesStoreSetPacketByteValue I)
      | none => none) = some evm' := by
    rw [hlayout]
    simpa [evm'] using
      bytesStoreSetPacketByteStorageLocStoreShort
        (evm := evm) (σ := σ) (I := I) (len := len)
        hload hcanon hshort hbound
  have hassign :
      assignStorageRef? bytesStoreConfig
        (bytesStoreSetPacketByteFrame I)
        evm .storage (packetDataByteRef (.var "byteIndex"))
          (bytesStoreSetPacketByteValue I) =
          .ok (bytesStoreSetPacketByteFrame I, evm') :=
    bytesStoreSetPacketByteAssignOfLength (evm := evm) (evm' := evm') (I := I)
      hlenRead hbound hstore
  have hloadPost :
      Solm.EVM.storageLoad evm' evm'.executionEnv.codeOwner ⟨2⟩ =
        bytesStoreSetPacketByteShortStoredWord σ I := by
    simpa [evm'] using
      storageLoad_storageStore_codeOwner_same_present evm hacc ⟨2⟩
        (bytesStoreSetPacketByteShortStoredWord σ I)
  have hflagPost :
      UInt256.land (bytesStoreSetPacketByteShortStoredWord σ I) ⟨1⟩ = ⟨0⟩ := by
    rw [bytesStoreSetPacketByteShortStoredWord_flag_eq
      (σ := σ) (I := I) (len := len) hshort hbound, hflag]
  have hlenPost :
      readStorageBytesLength? bytesStoreConfig evm'
          { base := "packet", steps := [.field "data"] } =
        .ok len.toNat := by
    have hltLen : UInt256.lt len ⟨32⟩ = ⟨1⟩ := by
      exact ult_one (by
        simpa [show (⟨32⟩ : UInt256).toNat = 32 from by decide] using hshort)
    have hvalidLen : UInt256.sub ⟨0⟩ (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩ := by
      rw [hltLen]
      native_decide
    have hlenPostWord :
        UInt256.land (UInt256.div (bytesStoreSetPacketByteShortStoredWord σ I) ⟨2⟩)
            ⟨127⟩ = len := by
      rw [bytesStoreSetPacketByteShortStoredWord_shortLen_eq
        (σ := σ) (I := I) (len := len) hshort hbound]
      exact hlen.symm
    exact bytesStoreReadLengthOfHeaderLoad
      (er := bytesStorePacketDataRef) (evm := evm')
      (baseSlot := ⟨2⟩) (header := bytesStoreSetPacketByteShortStoredWord σ I)
      (len := len.toNat)
      (bytesStorePacketDataRef_length_slot evm') hloadPost
      (solidityDecodeBytesLengthHeader_short_valid hflagPost hlenPostWord.symm
        (by simpa [hflagPost] using hvalidLen))
  have hpackedPost : checkBytesPacked ⟨2⟩ evm' = true :=
    checkBytesPacked_of_storageLoad_land_one_zero hloadPost hflagPost
  have hlayoutPost :
      bytesStoreConfig.storage.layout (bytesStoreSetPacketByteRef I) evm' =
        some (uint8Loc ⟨2⟩ ⟨31 - (bytesStoreSetByteIndexWord I).toNat, by omega⟩) :=
    bytesStoreSetPacketByteLayoutShort (evm := evm') (I := I) hpackedPost hidx31
  have hidxLe : (bytesStoreSetByteIndexWord I).toNat ≤ 31 := by
    omega
  have hret :
      evalExpr? bytesStoreConfig
        (bytesStoreSetPacketByteFrame I)
        evm' (.storage (packetDataByteRef (.var "byteIndex"))) =
          .ok (bytesStoreSetPacketByteValue I) := by
    rw [evalExpr_storage_scalar_of_resolve_layout
      (bytesStoreSetPacketByteResolveOfLength (evm := evm') (I := I) hlenPost hbound)
      hlayoutPost]
    rw [storageLocLoad_uint8Loc_byteAt
      (slot := ⟨2⟩) (idx := bytesStoreSetByteIndexWord I)
      (off := ⟨31 - (bytesStoreSetByteIndexWord I).toNat, by omega⟩)
      (hoff := by rfl) (hidx := hidxLe)]
    rw [hloadPost]
    rw [bytesStoreSetPacketByteShortStoredWord_byteAt
      (σ := σ) (I := I) (len := len) hcanon hshort hbound]
    simp [bytesStoreSetPacketByteValue]
  simpa [evm'] using
    bytesStoreSetPacketByteBodyReturns (evm := evm) (evm' := evm') (I := I)
      hwv hassign hret

theorem bytesStoreSetPacketByteLongBodyReturnsOfPostLongReadback
    {evm : EVM.State} {σ : AccountMap} {I : ExecutionEnv}
    {len lenPost postHeaderWord : UInt256} {acc : Account}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hloadHeader : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩ =
      bytesStorePacketLengthHeaderWord σ I)
    (hloadData : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (bytesStoreSetPacketByteLongDataSlot I) =
      bytesStoreSetPacketByteLongOldWord σ I)
    (hloadHeaderPost :
      Solm.EVM.storageLoad
          (Solm.EVM.storageStore evm evm.executionEnv.codeOwner
            (bytesStoreSetPacketByteLongDataSlot I)
            (bytesStoreSetPacketByteLongStoredWord σ I))
          evm.executionEnv.codeOwner ⟨2⟩ =
        postHeaderWord)
    (hacc : evm.accountMap.find? evm.executionEnv.codeOwner = some acc)
    (hcanon : (bytesStoreSetByteValueWord I).toNat < EVM.twoPow 8)
    (hlen : len = UInt256.div (bytesStorePacketLengthHeaderWord σ I) ⟨2⟩)
    (hlenPost : lenPost = UInt256.div postHeaderWord ⟨2⟩)
    (hbound : (bytesStoreSetByteIndexWord I).toNat < len.toNat)
    (hboundPost : (bytesStoreSetByteIndexWord I).toNat < lenPost.toNat)
    (hflag : UInt256.land (bytesStorePacketLengthHeaderWord σ I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (bytesStorePacketLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStorePacketLengthHeaderWord σ I) ⟨2⟩) ⟨32⟩) ≠
          ⟨0⟩)
    (hflagPost : UInt256.land postHeaderWord ⟨1⟩ ≠ ⟨0⟩)
    (hvalidPost : UInt256.sub (UInt256.land postHeaderWord ⟨1⟩)
        (UInt256.lt (UInt256.div postHeaderWord ⟨2⟩) ⟨32⟩) ≠ ⟨0⟩) :
    ExecTransitionBody bytesStoreConfig bytesStoreContract evm
      (bytesStoreSetPacketByteLocals I) setPacketByteTransition.body
      (.returned
        (bytesStoreSetPacketByteFrame I)
        (Solm.EVM.storageStore evm evm.executionEnv.codeOwner
          (bytesStoreSetPacketByteLongDataSlot I)
          (bytesStoreSetPacketByteLongStoredWord σ I))
        (some (bytesStoreSetPacketByteValue I))) := by
  let evm' := Solm.EVM.storageStore evm evm.executionEnv.codeOwner
    (bytesStoreSetPacketByteLongDataSlot I)
    (bytesStoreSetPacketByteLongStoredWord σ I)
  have hloadHeaderPost' :
      Solm.EVM.storageLoad evm' evm'.executionEnv.codeOwner ⟨2⟩ =
        postHeaderWord := by
    simpa [evm', storageStore_executionEnv] using hloadHeaderPost
  have hvalidLen :
      UInt256.sub (UInt256.land (bytesStorePacketLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩ := by
    simpa [hlen] using hvalid
  have hlenRead :
      readStorageBytesLength? bytesStoreConfig evm
          { base := "packet", steps := [.field "data"] } =
        .ok len.toNat := by
    exact bytesStoreReadLengthOfHeaderLoad
      (er := bytesStorePacketDataRef) (evm := evm)
      (baseSlot := ⟨2⟩) (header := bytesStorePacketLengthHeaderWord σ I)
      (len := len.toNat)
      (bytesStorePacketDataRef_length_slot evm) hloadHeader
      (solidityDecodeBytesLengthHeader_long_valid hflag hlen hvalidLen)
  have hpacked : checkBytesPacked ⟨2⟩ evm = false :=
    checkBytesPacked_of_storageLoad_land_one_ne_zero hloadHeader hflag
  have hlayout :
      bytesStoreConfig.storage.layout (bytesStoreSetPacketByteRef I) evm =
        some (uint8Loc (bytesStoreSetPacketByteLongDataSlot I)
          ⟨31 - (bytesStoreSetPacketByteLongWordIndex I).toNat, by
            have hidx := bytesStoreSetPacketByteLongWordIndex_lt32 I
            omega⟩) :=
    bytesStoreSetPacketByteLayoutLong (evm := evm) (I := I) hpacked
  have hstore :
      (match bytesStoreConfig.storage.layout (bytesStoreSetPacketByteRef I) evm with
      | some loc => storageLocStore evm loc (bytesStoreSetPacketByteValue I)
      | none => none) = some evm' := by
    rw [hlayout]
    simpa [evm'] using
      bytesStoreSetPacketByteStorageLocStoreLong
        (evm := evm) (σ := σ) (I := I) hloadData hcanon
  have hassign :
      assignStorageRef? bytesStoreConfig
        (bytesStoreSetPacketByteFrame I)
        evm .storage (packetDataByteRef (.var "byteIndex"))
          (bytesStoreSetPacketByteValue I) =
          .ok (bytesStoreSetPacketByteFrame I, evm') :=
    bytesStoreSetPacketByteAssignOfLength (evm := evm) (evm' := evm') (I := I)
      hlenRead hbound hstore
  have hlenPostRead :
      readStorageBytesLength? bytesStoreConfig evm'
          { base := "packet", steps := [.field "data"] } =
        .ok lenPost.toNat := by
    have hvalidLenPost :
        UInt256.sub (UInt256.land postHeaderWord ⟨1⟩)
          (UInt256.lt lenPost ⟨32⟩) ≠ ⟨0⟩ := by
      simpa [hlenPost] using hvalidPost
    exact bytesStoreReadLengthOfHeaderLoad
      (er := bytesStorePacketDataRef) (evm := evm')
      (baseSlot := ⟨2⟩) (header := postHeaderWord) (len := lenPost.toNat)
      (bytesStorePacketDataRef_length_slot evm') hloadHeaderPost'
      (solidityDecodeBytesLengthHeader_long_valid hflagPost hlenPost hvalidLenPost)
  have hpackedPost : checkBytesPacked ⟨2⟩ evm' = false :=
    checkBytesPacked_of_storageLoad_land_one_ne_zero hloadHeaderPost' hflagPost
  have hlayoutPost :
      bytesStoreConfig.storage.layout (bytesStoreSetPacketByteRef I) evm' =
        some (uint8Loc (bytesStoreSetPacketByteLongDataSlot I)
          ⟨31 - (bytesStoreSetPacketByteLongWordIndex I).toNat, by
            have hidx := bytesStoreSetPacketByteLongWordIndex_lt32 I
            omega⟩) :=
    bytesStoreSetPacketByteLayoutLong (evm := evm') (I := I) hpackedPost
  have hloadDataPost :
      Solm.EVM.storageLoad evm' evm'.executionEnv.codeOwner
          (bytesStoreSetPacketByteLongDataSlot I) =
        bytesStoreSetPacketByteLongStoredWord σ I := by
    simpa [evm'] using
      storageLoad_storageStore_codeOwner_same_present evm hacc
        (bytesStoreSetPacketByteLongDataSlot I)
        (bytesStoreSetPacketByteLongStoredWord σ I)
  have hret :
      evalExpr? bytesStoreConfig
        (bytesStoreSetPacketByteFrame I)
        evm' (.storage (packetDataByteRef (.var "byteIndex"))) =
          .ok (bytesStoreSetPacketByteValue I) := by
    rw [evalExpr_storage_scalar_of_resolve_layout
      (bytesStoreSetPacketByteResolveOfLength
        (evm := evm') (I := I) (len := lenPost.toNat) hlenPostRead hboundPost)
      hlayoutPost]
    rw [storageLocLoad_uint8Loc_byteAt
      (evm := evm') (slot := bytesStoreSetPacketByteLongDataSlot I)
      (idx := bytesStoreSetPacketByteLongWordIndex I)
      (off := ⟨31 - (bytesStoreSetPacketByteLongWordIndex I).toNat, by
        have hidx := bytesStoreSetPacketByteLongWordIndex_lt32 I
        omega⟩)
      (by rfl)
      (by
        have hidx := bytesStoreSetPacketByteLongWordIndex_lt32 I
        omega)]
    rw [hloadDataPost]
    rw [bytesStoreSetPacketByteLongStoredWord_byteAt (σ := σ) (I := I) hcanon]
    simp [bytesStoreSetPacketByteValue]
  simpa [evm'] using
    bytesStoreSetPacketByteBodyReturns (evm := evm) (evm' := evm') (I := I)
      hwv hassign hret

theorem bytesStoreSetPacketByteResolveRevertsOfLength {evm : EVM.State} {I : ExecutionEnv}
    {len : Nat}
    (hlen : readStorageBytesLength? bytesStoreConfig evm
      { base := "packet", steps := [.field "data"] } = .ok len)
    (hbound : ¬ (bytesStoreSetByteIndexWord I).toNat < len) :
    resolveStorageRef? bytesStoreConfig
      { contract := bytesStoreContract, locals := bytesStoreSetPacketByteLocals I }
      evm (packetDataByteRef (.var "byteIndex")) = .revert := by
  have hgetPacket :
      (bytesStoreSetPacketByteLocals I).get? "packet" = none :=
    bytesStoreSetPacketByteLocals_get_packet_none I
  have her :
      evalStorageRef bytesStoreConfig
        { contract := bytesStoreContract, locals := bytesStoreSetPacketByteLocals I }
        evm (packetDataByteRef (.var "byteIndex")) = .revert := by
    exact bytesStoreSetPacketByteEvalStorageRefRevertsOfLength
      (evm := evm) (I := I) (len := len) hlen hbound
  exact resolveStorageRef?_revert_of_evalStorageRef_revert hgetPacket her

theorem bytesStoreSetPacketByteLongBodyReturnRevertsOfPostLongLength
    {evm : EVM.State} {σ : AccountMap} {I : ExecutionEnv}
    {len lenPost postHeaderWord : UInt256} {acc : Account}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hloadHeader : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩ =
      bytesStorePacketLengthHeaderWord σ I)
    (hloadData : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (bytesStoreSetPacketByteLongDataSlot I) =
      bytesStoreSetPacketByteLongOldWord σ I)
    (hloadHeaderPost :
      Solm.EVM.storageLoad
          (Solm.EVM.storageStore evm evm.executionEnv.codeOwner
            (bytesStoreSetPacketByteLongDataSlot I)
            (bytesStoreSetPacketByteLongStoredWord σ I))
          evm.executionEnv.codeOwner ⟨2⟩ =
        postHeaderWord)
    (hacc : evm.accountMap.find? evm.executionEnv.codeOwner = some acc)
    (hcanon : (bytesStoreSetByteValueWord I).toNat < EVM.twoPow 8)
    (hlen : len = UInt256.div (bytesStorePacketLengthHeaderWord σ I) ⟨2⟩)
    (hlenPost : lenPost = UInt256.div postHeaderWord ⟨2⟩)
    (hbound : (bytesStoreSetByteIndexWord I).toNat < len.toNat)
    (hboundPost : ¬ (bytesStoreSetByteIndexWord I).toNat < lenPost.toNat)
    (hflag : UInt256.land (bytesStorePacketLengthHeaderWord σ I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (bytesStorePacketLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStorePacketLengthHeaderWord σ I) ⟨2⟩) ⟨32⟩) ≠
          ⟨0⟩)
    (hflagPost : UInt256.land postHeaderWord ⟨1⟩ ≠ ⟨0⟩)
    (hvalidPost : UInt256.sub (UInt256.land postHeaderWord ⟨1⟩)
        (UInt256.lt (UInt256.div postHeaderWord ⟨2⟩) ⟨32⟩) ≠ ⟨0⟩) :
    ExecTransitionBody bytesStoreConfig bytesStoreContract evm
      (bytesStoreSetPacketByteLocals I) setPacketByteTransition.body .reverted := by
  let evm' := Solm.EVM.storageStore evm evm.executionEnv.codeOwner
    (bytesStoreSetPacketByteLongDataSlot I)
    (bytesStoreSetPacketByteLongStoredWord σ I)
  have hloadHeaderPost' :
      Solm.EVM.storageLoad evm' evm'.executionEnv.codeOwner ⟨2⟩ =
        postHeaderWord := by
    simpa [evm', storageStore_executionEnv] using hloadHeaderPost
  have hvalidLen :
      UInt256.sub (UInt256.land (bytesStorePacketLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩ := by
    simpa [hlen] using hvalid
  have hlenRead :
      readStorageBytesLength? bytesStoreConfig evm
          { base := "packet", steps := [.field "data"] } =
        .ok len.toNat := by
    exact bytesStoreReadLengthOfHeaderLoad
      (er := bytesStorePacketDataRef) (evm := evm)
      (baseSlot := ⟨2⟩) (header := bytesStorePacketLengthHeaderWord σ I)
      (len := len.toNat)
      (bytesStorePacketDataRef_length_slot evm) hloadHeader
      (solidityDecodeBytesLengthHeader_long_valid hflag hlen hvalidLen)
  have hpacked : checkBytesPacked ⟨2⟩ evm = false :=
    checkBytesPacked_of_storageLoad_land_one_ne_zero hloadHeader hflag
  have hlayout :
      bytesStoreConfig.storage.layout (bytesStoreSetPacketByteRef I) evm =
        some (uint8Loc (bytesStoreSetPacketByteLongDataSlot I)
          ⟨31 - (bytesStoreSetPacketByteLongWordIndex I).toNat, by
            have hidx := bytesStoreSetPacketByteLongWordIndex_lt32 I
            omega⟩) :=
    bytesStoreSetPacketByteLayoutLong (evm := evm) (I := I) hpacked
  have hstore :
      (match bytesStoreConfig.storage.layout (bytesStoreSetPacketByteRef I) evm with
      | some loc => storageLocStore evm loc (bytesStoreSetPacketByteValue I)
      | none => none) = some evm' := by
    rw [hlayout]
    simpa [evm'] using
      bytesStoreSetPacketByteStorageLocStoreLong
        (evm := evm) (σ := σ) (I := I) hloadData hcanon
  have hassign :
      assignStorageRef? bytesStoreConfig
        (bytesStoreSetPacketByteFrame I)
        evm .storage (packetDataByteRef (.var "byteIndex"))
          (bytesStoreSetPacketByteValue I) =
          .ok (bytesStoreSetPacketByteFrame I, evm') :=
    bytesStoreSetPacketByteAssignOfLength (evm := evm) (evm' := evm') (I := I)
      hlenRead hbound hstore
  have hlenPostRead :
      readStorageBytesLength? bytesStoreConfig evm'
          { base := "packet", steps := [.field "data"] } =
        .ok lenPost.toNat := by
    have hvalidLenPost :
        UInt256.sub (UInt256.land postHeaderWord ⟨1⟩)
          (UInt256.lt lenPost ⟨32⟩) ≠ ⟨0⟩ := by
      simpa [hlenPost] using hvalidPost
    exact bytesStoreReadLengthOfHeaderLoad
      (er := bytesStorePacketDataRef) (evm := evm')
      (baseSlot := ⟨2⟩) (header := postHeaderWord) (len := lenPost.toNat)
      (bytesStorePacketDataRef_length_slot evm') hloadHeaderPost'
      (solidityDecodeBytesLengthHeader_long_valid hflagPost hlenPost hvalidLenPost)
  have hret :
      evalExpr? bytesStoreConfig
        (bytesStoreSetPacketByteFrame I)
        evm' (.storage (packetDataByteRef (.var "byteIndex"))) = .revert := by
    have hresolve :
        resolveStorageRef? bytesStoreConfig
          (bytesStoreSetPacketByteFrame I) evm'
          (packetDataByteRef (.var "byteIndex")) = .revert := by
      simpa [bytesStoreSetPacketByteFrame] using
        bytesStoreSetPacketByteResolveRevertsOfLength
          (evm := evm') (I := I) (len := lenPost.toNat) hlenPostRead hboundPost
    rw [evalExpr?]
    rw [hresolve]
    simp [Bind.bind, EvalResult.bind]
  simpa [evm'] using
    bytesStoreSetPacketByteBodyReturnReverts (evm := evm) (evm' := evm') (I := I)
      hwv hassign hret

theorem bytesStoreSetPacketByteLongBodyReturnsOfPostShortReadback
    {evm : EVM.State} {σ : AccountMap} {I : ExecutionEnv}
    {len lenPost postHeaderWord : UInt256}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hloadHeader : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩ =
      bytesStorePacketLengthHeaderWord σ I)
    (hloadData : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (bytesStoreSetPacketByteLongDataSlot I) =
      bytesStoreSetPacketByteLongOldWord σ I)
    (hloadHeaderPost :
      Solm.EVM.storageLoad
          (Solm.EVM.storageStore evm evm.executionEnv.codeOwner
            (bytesStoreSetPacketByteLongDataSlot I)
            (bytesStoreSetPacketByteLongStoredWord σ I))
          evm.executionEnv.codeOwner ⟨2⟩ =
        postHeaderWord)
    (hcanon : (bytesStoreSetByteValueWord I).toNat < EVM.twoPow 8)
    (hlen : len = UInt256.div (bytesStorePacketLengthHeaderWord σ I) ⟨2⟩)
    (hlenPost : lenPost = UInt256.land (UInt256.div postHeaderWord ⟨2⟩) ⟨127⟩)
    (hbound : (bytesStoreSetByteIndexWord I).toNat < len.toNat)
    (hboundPost : (bytesStoreSetByteIndexWord I).toNat < lenPost.toNat)
    (hflag : UInt256.land (bytesStorePacketLengthHeaderWord σ I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (bytesStorePacketLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStorePacketLengthHeaderWord σ I) ⟨2⟩) ⟨32⟩) ≠
          ⟨0⟩)
    (hflagPost : UInt256.land postHeaderWord ⟨1⟩ = ⟨0⟩)
    (hvalidPost : UInt256.sub (UInt256.land postHeaderWord ⟨1⟩)
        (UInt256.lt (UInt256.land (UInt256.div postHeaderWord ⟨2⟩) ⟨127⟩) ⟨32⟩) ≠
          ⟨0⟩)
    (hbytePost :
      UInt256.byteAt (bytesStoreSetByteIndexWord I) postHeaderWord =
        bytesStoreSetByteValueWord I) :
    ExecTransitionBody bytesStoreConfig bytesStoreContract evm
      (bytesStoreSetPacketByteLocals I) setPacketByteTransition.body
      (.returned
        (bytesStoreSetPacketByteFrame I)
        (Solm.EVM.storageStore evm evm.executionEnv.codeOwner
          (bytesStoreSetPacketByteLongDataSlot I)
          (bytesStoreSetPacketByteLongStoredWord σ I))
        (some (bytesStoreSetPacketByteValue I))) := by
  let evm' := Solm.EVM.storageStore evm evm.executionEnv.codeOwner
    (bytesStoreSetPacketByteLongDataSlot I)
    (bytesStoreSetPacketByteLongStoredWord σ I)
  have hloadHeaderPost' :
      Solm.EVM.storageLoad evm' evm'.executionEnv.codeOwner ⟨2⟩ =
        postHeaderWord := by
    simpa [evm', storageStore_executionEnv] using hloadHeaderPost
  have hvalidLen :
      UInt256.sub (UInt256.land (bytesStorePacketLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩ := by
    simpa [hlen] using hvalid
  have hlenRead :
      readStorageBytesLength? bytesStoreConfig evm
          { base := "packet", steps := [.field "data"] } =
        .ok len.toNat := by
    exact bytesStoreReadLengthOfHeaderLoad
      (er := bytesStorePacketDataRef) (evm := evm)
      (baseSlot := ⟨2⟩) (header := bytesStorePacketLengthHeaderWord σ I)
      (len := len.toNat)
      (bytesStorePacketDataRef_length_slot evm) hloadHeader
      (solidityDecodeBytesLengthHeader_long_valid hflag hlen hvalidLen)
  have hpacked : checkBytesPacked ⟨2⟩ evm = false :=
    checkBytesPacked_of_storageLoad_land_one_ne_zero hloadHeader hflag
  have hlayout :
      bytesStoreConfig.storage.layout (bytesStoreSetPacketByteRef I) evm =
        some (uint8Loc (bytesStoreSetPacketByteLongDataSlot I)
          ⟨31 - (bytesStoreSetPacketByteLongWordIndex I).toNat, by
            have hidx := bytesStoreSetPacketByteLongWordIndex_lt32 I
            omega⟩) :=
    bytesStoreSetPacketByteLayoutLong (evm := evm) (I := I) hpacked
  have hstore :
      (match bytesStoreConfig.storage.layout (bytesStoreSetPacketByteRef I) evm with
      | some loc => storageLocStore evm loc (bytesStoreSetPacketByteValue I)
      | none => none) = some evm' := by
    rw [hlayout]
    simpa [evm'] using
      bytesStoreSetPacketByteStorageLocStoreLong
        (evm := evm) (σ := σ) (I := I) hloadData hcanon
  have hassign :
      assignStorageRef? bytesStoreConfig
        (bytesStoreSetPacketByteFrame I)
        evm .storage (packetDataByteRef (.var "byteIndex"))
          (bytesStoreSetPacketByteValue I) =
          .ok (bytesStoreSetPacketByteFrame I, evm') :=
    bytesStoreSetPacketByteAssignOfLength (evm := evm) (evm' := evm') (I := I)
      hlenRead hbound hstore
  have hlenPostRead :
      readStorageBytesLength? bytesStoreConfig evm'
          { base := "packet", steps := [.field "data"] } =
        .ok lenPost.toNat := by
    have hvalidLenPost :
        UInt256.sub ⟨0⟩ (UInt256.lt lenPost ⟨32⟩) ≠ ⟨0⟩ := by
      simpa [hlenPost, hflagPost] using hvalidPost
    exact bytesStoreReadLengthOfHeaderLoad
      (er := bytesStorePacketDataRef) (evm := evm')
      (baseSlot := ⟨2⟩) (header := postHeaderWord) (len := lenPost.toNat)
      (bytesStorePacketDataRef_length_slot evm') hloadHeaderPost'
      (solidityDecodeBytesLengthHeader_short_valid hflagPost hlenPost
        (by simpa [← hlenPost] using hvalidPost))
  have hpackedPost : checkBytesPacked ⟨2⟩ evm' = true :=
    checkBytesPacked_of_storageLoad_land_one_zero hloadHeaderPost' hflagPost
  have hshortPost : lenPost.toNat < 32 := by
    have hvalidLenPost :
        UInt256.sub ⟨0⟩ (UInt256.lt lenPost ⟨32⟩) ≠ ⟨0⟩ := by
      simpa [hlenPost, hflagPost] using hvalidPost
    exact solidityShortBytesValid_lt32 hvalidLenPost
  have hidx31 : (bytesStoreSetByteIndexWord I).toNat < 31 :=
    bytesStoreSetByteIndex_lt31_of_short_bound (I := I) (len := lenPost)
      hshortPost hboundPost
  have hlayoutPost :
      bytesStoreConfig.storage.layout (bytesStoreSetPacketByteRef I) evm' =
        some (uint8Loc ⟨2⟩
          ⟨31 - (bytesStoreSetByteIndexWord I).toNat, by omega⟩) :=
    bytesStoreSetPacketByteLayoutShort (evm := evm') (I := I) hpackedPost hidx31
  have hidxLe : (bytesStoreSetByteIndexWord I).toNat ≤ 31 := by
    omega
  have hret :
      evalExpr? bytesStoreConfig
        (bytesStoreSetPacketByteFrame I)
        evm' (.storage (packetDataByteRef (.var "byteIndex"))) =
          .ok (bytesStoreSetPacketByteValue I) := by
    rw [evalExpr_storage_scalar_of_resolve_layout
      (bytesStoreSetPacketByteResolveOfLength
        (evm := evm') (I := I) (len := lenPost.toNat) hlenPostRead hboundPost)
      hlayoutPost]
    rw [storageLocLoad_uint8Loc_byteAt
      (slot := ⟨2⟩)
      (idx := bytesStoreSetByteIndexWord I)
      (off := ⟨31 - (bytesStoreSetByteIndexWord I).toNat, by omega⟩)
      (hoff := by rfl) (hidx := hidxLe)]
    rw [hloadHeaderPost']
    rw [hbytePost]
    simp [bytesStoreSetPacketByteValue]
  simpa [evm'] using
    bytesStoreSetPacketByteBodyReturns (evm := evm) (evm' := evm') (I := I)
      hwv hassign hret

theorem bytesStoreSetPacketByteLongBodyReturnRevertsOfPostShortLength
    {evm : EVM.State} {σ : AccountMap} {I : ExecutionEnv}
    {len lenPost postHeaderWord : UInt256}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hloadHeader : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩ =
      bytesStorePacketLengthHeaderWord σ I)
    (hloadData : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (bytesStoreSetPacketByteLongDataSlot I) =
      bytesStoreSetPacketByteLongOldWord σ I)
    (hloadHeaderPost :
      Solm.EVM.storageLoad
          (Solm.EVM.storageStore evm evm.executionEnv.codeOwner
            (bytesStoreSetPacketByteLongDataSlot I)
            (bytesStoreSetPacketByteLongStoredWord σ I))
          evm.executionEnv.codeOwner ⟨2⟩ =
        postHeaderWord)
    (hcanon : (bytesStoreSetByteValueWord I).toNat < EVM.twoPow 8)
    (hlen : len = UInt256.div (bytesStorePacketLengthHeaderWord σ I) ⟨2⟩)
    (hlenPost : lenPost = UInt256.land (UInt256.div postHeaderWord ⟨2⟩) ⟨127⟩)
    (hbound : (bytesStoreSetByteIndexWord I).toNat < len.toNat)
    (hboundPost : ¬ (bytesStoreSetByteIndexWord I).toNat < lenPost.toNat)
    (hflag : UInt256.land (bytesStorePacketLengthHeaderWord σ I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (bytesStorePacketLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStorePacketLengthHeaderWord σ I) ⟨2⟩) ⟨32⟩) ≠
          ⟨0⟩)
    (hflagPost : UInt256.land postHeaderWord ⟨1⟩ = ⟨0⟩)
    (hvalidPost : UInt256.sub (UInt256.land postHeaderWord ⟨1⟩)
        (UInt256.lt (UInt256.land (UInt256.div postHeaderWord ⟨2⟩) ⟨127⟩) ⟨32⟩) ≠
          ⟨0⟩) :
    ExecTransitionBody bytesStoreConfig bytesStoreContract evm
      (bytesStoreSetPacketByteLocals I) setPacketByteTransition.body .reverted := by
  let evm' := Solm.EVM.storageStore evm evm.executionEnv.codeOwner
    (bytesStoreSetPacketByteLongDataSlot I)
    (bytesStoreSetPacketByteLongStoredWord σ I)
  have hloadHeaderPost' :
      Solm.EVM.storageLoad evm' evm'.executionEnv.codeOwner ⟨2⟩ =
        postHeaderWord := by
    simpa [evm', storageStore_executionEnv] using hloadHeaderPost
  have hvalidLen :
      UInt256.sub (UInt256.land (bytesStorePacketLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩ := by
    simpa [hlen] using hvalid
  have hlenRead :
      readStorageBytesLength? bytesStoreConfig evm
          { base := "packet", steps := [.field "data"] } =
        .ok len.toNat := by
    exact bytesStoreReadLengthOfHeaderLoad
      (er := bytesStorePacketDataRef) (evm := evm)
      (baseSlot := ⟨2⟩) (header := bytesStorePacketLengthHeaderWord σ I)
      (len := len.toNat)
      (bytesStorePacketDataRef_length_slot evm) hloadHeader
      (solidityDecodeBytesLengthHeader_long_valid hflag hlen hvalidLen)
  have hpacked : checkBytesPacked ⟨2⟩ evm = false :=
    checkBytesPacked_of_storageLoad_land_one_ne_zero hloadHeader hflag
  have hlayout :
      bytesStoreConfig.storage.layout (bytesStoreSetPacketByteRef I) evm =
        some (uint8Loc (bytesStoreSetPacketByteLongDataSlot I)
          ⟨31 - (bytesStoreSetPacketByteLongWordIndex I).toNat, by
            have hidx := bytesStoreSetPacketByteLongWordIndex_lt32 I
            omega⟩) :=
    bytesStoreSetPacketByteLayoutLong (evm := evm) (I := I) hpacked
  have hstore :
      (match bytesStoreConfig.storage.layout (bytesStoreSetPacketByteRef I) evm with
      | some loc => storageLocStore evm loc (bytesStoreSetPacketByteValue I)
      | none => none) = some evm' := by
    rw [hlayout]
    simpa [evm'] using
      bytesStoreSetPacketByteStorageLocStoreLong
        (evm := evm) (σ := σ) (I := I) hloadData hcanon
  have hassign :
      assignStorageRef? bytesStoreConfig
        (bytesStoreSetPacketByteFrame I)
        evm .storage (packetDataByteRef (.var "byteIndex"))
          (bytesStoreSetPacketByteValue I) =
          .ok (bytesStoreSetPacketByteFrame I, evm') :=
    bytesStoreSetPacketByteAssignOfLength (evm := evm) (evm' := evm') (I := I)
      hlenRead hbound hstore
  have hlenPostRead :
      readStorageBytesLength? bytesStoreConfig evm'
          { base := "packet", steps := [.field "data"] } =
        .ok lenPost.toNat := by
    have hvalidLenPost :
        UInt256.sub ⟨0⟩ (UInt256.lt lenPost ⟨32⟩) ≠ ⟨0⟩ := by
      simpa [hlenPost, hflagPost] using hvalidPost
    exact bytesStoreReadLengthOfHeaderLoad
      (er := bytesStorePacketDataRef) (evm := evm')
      (baseSlot := ⟨2⟩) (header := postHeaderWord) (len := lenPost.toNat)
      (bytesStorePacketDataRef_length_slot evm') hloadHeaderPost'
      (solidityDecodeBytesLengthHeader_short_valid hflagPost hlenPost
        (by simpa [← hlenPost] using hvalidPost))
  have hret :
      evalExpr? bytesStoreConfig
        (bytesStoreSetPacketByteFrame I)
        evm' (.storage (packetDataByteRef (.var "byteIndex"))) = .revert := by
    have hresolve :
        resolveStorageRef? bytesStoreConfig
          (bytesStoreSetPacketByteFrame I) evm'
          (packetDataByteRef (.var "byteIndex")) = .revert := by
      simpa [bytesStoreSetPacketByteFrame] using
        bytesStoreSetPacketByteResolveRevertsOfLength
          (evm := evm') (I := I) (len := lenPost.toNat) hlenPostRead hboundPost
    rw [evalExpr?]
    rw [hresolve]
    simp [Bind.bind, EvalResult.bind]
  exact bytesStoreSetPacketByteBodyReturnReverts
    (evm := evm) (evm' := evm') (I := I) hwv hassign hret

theorem bytesStoreSetPacketByteBodyBoundsRevertsOfLength
    {evm : EVM.State} {I : ExecutionEnv} {len : Nat}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hlen : readStorageBytesLength? bytesStoreConfig evm
      { base := "packet", steps := [.field "data"] } = .ok len)
    (hbound : ¬ (bytesStoreSetByteIndexWord I).toNat < len) :
    ExecTransitionBody bytesStoreConfig bytesStoreContract evm
      (bytesStoreSetPacketByteLocals I) setPacketByteTransition.body .reverted := by
  let solm : Frame :=
    { contract := bytesStoreContract, locals := bytesStoreSetPacketByteLocals I }
  have hvalue :
      evalExpr? bytesStoreConfig solm evm (.var "value") =
        .ok (bytesStoreSetPacketByteValue I) := by
    exact evalExpr_var_of_get? (by
      simp [solm, bytesStoreSetPacketByteValue, bytesStoreSetPacketByteLocals])
  have hassign :
      assignStorageRef? bytesStoreConfig solm evm .storage
        (packetDataByteRef (.var "byteIndex")) (bytesStoreSetPacketByteValue I) = .revert := by
    exact assignStorageRef_storage_revert_of_resolve
      (bytesStoreSetPacketByteResolveRevertsOfLength (I := I) hlen hbound)
  exact ExecFuncBody.execBlockRevert <|
    ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consRevert (ExecStmt.assignStoreRevert hvalue hassign)

theorem bytesStoreSetPacketByteResolveRevertsOfLengthRead
    {evm : EVM.State} {I : ExecutionEnv}
    (hlen : readStorageBytesLength? bytesStoreConfig evm
      { base := "packet", steps := [.field "data"] } = .revert) :
    resolveStorageRef? bytesStoreConfig
      { contract := bytesStoreContract, locals := bytesStoreSetPacketByteLocals I }
      evm (packetDataByteRef (.var "byteIndex")) = .revert := by
  have hgetPacket :
      (bytesStoreSetPacketByteLocals I).get? "packet" = none :=
    bytesStoreSetPacketByteLocals_get_packet_none I
  have her :
      evalStorageRef bytesStoreConfig
        { contract := bytesStoreContract, locals := bytesStoreSetPacketByteLocals I }
        evm (packetDataByteRef (.var "byteIndex")) = .revert := by
    exact bytesStoreSetPacketByteEvalStorageRefRevertsOfLengthRead
      (evm := evm) (I := I) hlen
  exact resolveStorageRef?_revert_of_evalStorageRef_revert hgetPacket her

theorem bytesStoreSetPacketByteBodyRevertsOfLengthRead
    {evm : EVM.State} {I : ExecutionEnv}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hlen : readStorageBytesLength? bytesStoreConfig evm
      { base := "packet", steps := [.field "data"] } = .revert) :
    ExecTransitionBody bytesStoreConfig bytesStoreContract evm
      (bytesStoreSetPacketByteLocals I) setPacketByteTransition.body .reverted := by
  let solm : Frame :=
    { contract := bytesStoreContract, locals := bytesStoreSetPacketByteLocals I }
  have hvalue :
      evalExpr? bytesStoreConfig solm evm (.var "value") =
        .ok (bytesStoreSetPacketByteValue I) := by
    exact evalExpr_var_of_get? (by
      simp [solm, bytesStoreSetPacketByteValue, bytesStoreSetPacketByteLocals])
  have hassign :
      assignStorageRef? bytesStoreConfig solm evm .storage
        (packetDataByteRef (.var "byteIndex")) (bytesStoreSetPacketByteValue I) = .revert := by
    exact assignStorageRef_storage_revert_of_resolve
      (bytesStoreSetPacketByteResolveRevertsOfLengthRead (I := I) hlen)
  exact ExecFuncBody.execBlockRevert <|
    ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consRevert (ExecStmt.assignStoreRevert hvalue hassign)

theorem bytesStoreSetPacketByteBodyReturnRevertsOfPostLengthRead
    {evm evm' : EVM.State} {I : ExecutionEnv}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hassign :
      assignStorageRef? bytesStoreConfig
        (bytesStoreSetPacketByteFrame I)
        evm .storage (packetDataByteRef (.var "byteIndex"))
          (bytesStoreSetPacketByteValue I) =
          .ok (bytesStoreSetPacketByteFrame I, evm'))
    (hlenPost :
      readStorageBytesLength? bytesStoreConfig evm'
          { base := "packet", steps := [.field "data"] } = .revert) :
    ExecTransitionBody bytesStoreConfig bytesStoreContract evm
      (bytesStoreSetPacketByteLocals I) setPacketByteTransition.body .reverted := by
  have hret :
      evalExpr? bytesStoreConfig
        (bytesStoreSetPacketByteFrame I)
        evm' (.storage (packetDataByteRef (.var "byteIndex"))) = .revert := by
    have hresolve :
        resolveStorageRef? bytesStoreConfig
          (bytesStoreSetPacketByteFrame I) evm'
          (packetDataByteRef (.var "byteIndex")) = .revert := by
      simpa [bytesStoreSetPacketByteFrame] using
        bytesStoreSetPacketByteResolveRevertsOfLengthRead
          (evm := evm') (I := I) hlenPost
    rw [evalExpr?]
    rw [hresolve]
    simp [Bind.bind, EvalResult.bind]
  exact bytesStoreSetPacketByteBodyReturnReverts
    (evm := evm) (evm' := evm') (I := I) hwv hassign hret

theorem bytesStoreSetPacketByteLongBodyReturnRevertsOfPostShortMalformed
    {evm : EVM.State} {σ : AccountMap} {I : ExecutionEnv}
    {len postHeaderWord : UInt256}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hloadHeader : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩ =
      bytesStorePacketLengthHeaderWord σ I)
    (hloadData : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (bytesStoreSetPacketByteLongDataSlot I) =
      bytesStoreSetPacketByteLongOldWord σ I)
    (hloadHeaderPost :
      Solm.EVM.storageLoad
          (Solm.EVM.storageStore evm evm.executionEnv.codeOwner
            (bytesStoreSetPacketByteLongDataSlot I)
            (bytesStoreSetPacketByteLongStoredWord σ I))
          evm.executionEnv.codeOwner ⟨2⟩ =
        postHeaderWord)
    (hcanon : (bytesStoreSetByteValueWord I).toNat < EVM.twoPow 8)
    (hlen : len = UInt256.div (bytesStorePacketLengthHeaderWord σ I) ⟨2⟩)
    (hbound : (bytesStoreSetByteIndexWord I).toNat < len.toNat)
    (hflag : UInt256.land (bytesStorePacketLengthHeaderWord σ I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (bytesStorePacketLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStorePacketLengthHeaderWord σ I) ⟨2⟩) ⟨32⟩) ≠
          ⟨0⟩)
    (hflagPost : UInt256.land postHeaderWord ⟨1⟩ = ⟨0⟩)
    (hbadPost : UInt256.sub (UInt256.land postHeaderWord ⟨1⟩)
        (UInt256.lt (UInt256.land (UInt256.div postHeaderWord ⟨2⟩) ⟨127⟩) ⟨32⟩) =
          ⟨0⟩) :
    ExecTransitionBody bytesStoreConfig bytesStoreContract evm
      (bytesStoreSetPacketByteLocals I) setPacketByteTransition.body .reverted := by
  let evm' := Solm.EVM.storageStore evm evm.executionEnv.codeOwner
    (bytesStoreSetPacketByteLongDataSlot I)
    (bytesStoreSetPacketByteLongStoredWord σ I)
  have hloadHeaderPost' :
      Solm.EVM.storageLoad evm' evm'.executionEnv.codeOwner ⟨2⟩ =
        postHeaderWord := by
    simpa [evm', storageStore_executionEnv] using hloadHeaderPost
  have hvalidLen :
      UInt256.sub (UInt256.land (bytesStorePacketLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩ := by
    simpa [hlen] using hvalid
  have hlenRead :
      readStorageBytesLength? bytesStoreConfig evm
          { base := "packet", steps := [.field "data"] } =
        .ok len.toNat := by
    exact bytesStoreReadLengthOfHeaderLoad
      (er := bytesStorePacketDataRef) (evm := evm)
      (baseSlot := ⟨2⟩) (header := bytesStorePacketLengthHeaderWord σ I)
      (len := len.toNat)
      (bytesStorePacketDataRef_length_slot evm) hloadHeader
      (solidityDecodeBytesLengthHeader_long_valid hflag hlen hvalidLen)
  have hpacked : checkBytesPacked ⟨2⟩ evm = false :=
    checkBytesPacked_of_storageLoad_land_one_ne_zero hloadHeader hflag
  have hlayout :
      bytesStoreConfig.storage.layout (bytesStoreSetPacketByteRef I) evm =
        some (uint8Loc (bytesStoreSetPacketByteLongDataSlot I)
          ⟨31 - (bytesStoreSetPacketByteLongWordIndex I).toNat, by
            have hidx := bytesStoreSetPacketByteLongWordIndex_lt32 I
            omega⟩) :=
    bytesStoreSetPacketByteLayoutLong (evm := evm) (I := I) hpacked
  have hstore :
      (match bytesStoreConfig.storage.layout (bytesStoreSetPacketByteRef I) evm with
      | some loc => storageLocStore evm loc (bytesStoreSetPacketByteValue I)
      | none => none) = some evm' := by
    rw [hlayout]
    simpa [evm'] using
      bytesStoreSetPacketByteStorageLocStoreLong
        (evm := evm) (σ := σ) (I := I) hloadData hcanon
  have hassign :
      assignStorageRef? bytesStoreConfig
        (bytesStoreSetPacketByteFrame I)
        evm .storage (packetDataByteRef (.var "byteIndex"))
          (bytesStoreSetPacketByteValue I) =
          .ok (bytesStoreSetPacketByteFrame I, evm') :=
    bytesStoreSetPacketByteAssignOfLength (evm := evm) (evm' := evm') (I := I)
      hlenRead hbound hstore
  have hlenPost :
      readStorageBytesLength? bytesStoreConfig evm'
          { base := "packet", steps := [.field "data"] } = .revert := by
    have hbadPost0 :
        UInt256.sub ⟨0⟩
          (UInt256.lt (UInt256.land (UInt256.div postHeaderWord ⟨2⟩) ⟨127⟩) ⟨32⟩) =
            ⟨0⟩ := by
      simpa [hflagPost] using hbadPost
    exact bytesStoreReadLengthRevertOfHeaderLoad
      (er := bytesStorePacketDataRef) (evm := evm')
      (baseSlot := ⟨2⟩) (header := postHeaderWord)
      (bytesStorePacketDataRef_length_slot evm') hloadHeaderPost'
      (by simp [solidityDecodeBytesLengthHeader, hflagPost, hbadPost0])
  exact bytesStoreSetPacketByteBodyReturnRevertsOfPostLengthRead
    (evm := evm) (evm' := evm') (I := I) hwv hassign hlenPost

theorem bytesStoreSetPacketByteLongBodyReturnRevertsOfPostLongMalformed
    {evm : EVM.State} {σ : AccountMap} {I : ExecutionEnv}
    {len postHeaderWord : UInt256}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hloadHeader : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩ =
      bytesStorePacketLengthHeaderWord σ I)
    (hloadData : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (bytesStoreSetPacketByteLongDataSlot I) =
      bytesStoreSetPacketByteLongOldWord σ I)
    (hloadHeaderPost :
      Solm.EVM.storageLoad
          (Solm.EVM.storageStore evm evm.executionEnv.codeOwner
            (bytesStoreSetPacketByteLongDataSlot I)
            (bytesStoreSetPacketByteLongStoredWord σ I))
          evm.executionEnv.codeOwner ⟨2⟩ =
        postHeaderWord)
    (hcanon : (bytesStoreSetByteValueWord I).toNat < EVM.twoPow 8)
    (hlen : len = UInt256.div (bytesStorePacketLengthHeaderWord σ I) ⟨2⟩)
    (hbound : (bytesStoreSetByteIndexWord I).toNat < len.toNat)
    (hflag : UInt256.land (bytesStorePacketLengthHeaderWord σ I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (bytesStorePacketLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStorePacketLengthHeaderWord σ I) ⟨2⟩) ⟨32⟩) ≠
          ⟨0⟩)
    (hflagPost : UInt256.land postHeaderWord ⟨1⟩ ≠ ⟨0⟩)
    (hbadPost : UInt256.sub (UInt256.land postHeaderWord ⟨1⟩)
        (UInt256.lt (UInt256.div postHeaderWord ⟨2⟩) ⟨32⟩) = ⟨0⟩) :
    ExecTransitionBody bytesStoreConfig bytesStoreContract evm
      (bytesStoreSetPacketByteLocals I) setPacketByteTransition.body .reverted := by
  let evm' := Solm.EVM.storageStore evm evm.executionEnv.codeOwner
    (bytesStoreSetPacketByteLongDataSlot I)
    (bytesStoreSetPacketByteLongStoredWord σ I)
  have hloadHeaderPost' :
      Solm.EVM.storageLoad evm' evm'.executionEnv.codeOwner ⟨2⟩ =
        postHeaderWord := by
    simpa [evm', storageStore_executionEnv] using hloadHeaderPost
  have hvalidLen :
      UInt256.sub (UInt256.land (bytesStorePacketLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩ := by
    simpa [hlen] using hvalid
  have hlenRead :
      readStorageBytesLength? bytesStoreConfig evm
          { base := "packet", steps := [.field "data"] } =
        .ok len.toNat := by
    exact bytesStoreReadLengthOfHeaderLoad
      (er := bytesStorePacketDataRef) (evm := evm)
      (baseSlot := ⟨2⟩) (header := bytesStorePacketLengthHeaderWord σ I)
      (len := len.toNat)
      (bytesStorePacketDataRef_length_slot evm) hloadHeader
      (solidityDecodeBytesLengthHeader_long_valid hflag hlen hvalidLen)
  have hpacked : checkBytesPacked ⟨2⟩ evm = false :=
    checkBytesPacked_of_storageLoad_land_one_ne_zero hloadHeader hflag
  have hlayout :
      bytesStoreConfig.storage.layout (bytesStoreSetPacketByteRef I) evm =
        some (uint8Loc (bytesStoreSetPacketByteLongDataSlot I)
          ⟨31 - (bytesStoreSetPacketByteLongWordIndex I).toNat, by
            have hidx := bytesStoreSetPacketByteLongWordIndex_lt32 I
            omega⟩) :=
    bytesStoreSetPacketByteLayoutLong (evm := evm) (I := I) hpacked
  have hstore :
      (match bytesStoreConfig.storage.layout (bytesStoreSetPacketByteRef I) evm with
      | some loc => storageLocStore evm loc (bytesStoreSetPacketByteValue I)
      | none => none) = some evm' := by
    rw [hlayout]
    simpa [evm'] using
      bytesStoreSetPacketByteStorageLocStoreLong
        (evm := evm) (σ := σ) (I := I) hloadData hcanon
  have hassign :
      assignStorageRef? bytesStoreConfig
        (bytesStoreSetPacketByteFrame I)
        evm .storage (packetDataByteRef (.var "byteIndex"))
          (bytesStoreSetPacketByteValue I) =
          .ok (bytesStoreSetPacketByteFrame I, evm') :=
    bytesStoreSetPacketByteAssignOfLength (evm := evm) (evm' := evm') (I := I)
      hlenRead hbound hstore
  have hlenPostRead :
      readStorageBytesLength? bytesStoreConfig evm'
          { base := "packet", steps := [.field "data"] } = .revert := by
    exact bytesStoreReadLengthRevertOfHeaderLoad
      (er := bytesStorePacketDataRef) (evm := evm')
      (baseSlot := ⟨2⟩) (header := postHeaderWord)
      (bytesStorePacketDataRef_length_slot evm') hloadHeaderPost'
      (by simp [solidityDecodeBytesLengthHeader, hflagPost, hbadPost])
  exact bytesStoreSetPacketByteBodyReturnRevertsOfPostLengthRead
    (evm := evm) (evm' := evm') (I := I) hwv hassign hlenPostRead

theorem bytesStoreDecode_setPacketByte_locals {I : ExecutionEnv}
    (hsz68 : 68 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (bytesStoreSetByteValueWord I).toNat < EVM.twoPow 8) :
    decodeCalldata (setPacketByteTransition.params.map Param.name)
      (transitionSignature setPacketByteTransition).paramTypes I.calldata =
        some (bytesStoreSetPacketByteLocals I) := by
  simpa [bytesStoreSetPacketByteLocals] using
    bytesStoreDecode_setPacketByte (I := I) hsz68 hhi hcanon

theorem bytesStoreSetPacketByteUint8CanonEqGuard {w : UInt256}
    (h : UInt256.land w ⟨255⟩ = w) :
    UInt256.eq w (UInt256.land w ⟨255⟩) = ⟨1⟩ := by
  rw [h]
  exact u256_eq_refl w

theorem bytesStoreSetPacketByteUint8NoncanonEqGuard {w : UInt256}
    (h : UInt256.land w ⟨255⟩ ≠ w) :
    UInt256.eq w (UInt256.land w ⟨255⟩) = ⟨0⟩ := by
  exact u256_eq_of_ne (by
    intro hw
    exact h hw.symm)

theorem bytesStoreSetPacketByteLand255_toNat (w : UInt256) :
    (UInt256.land w ⟨255⟩).toNat = w.toNat % EVM.twoPow 8 := by
  change Nat.land w.toNat (⟨255⟩ : UInt256).toNat % EVM.twoPow 256 =
    w.toNat % EVM.twoPow 8
  rw [show (⟨255⟩ : UInt256).toNat = 255 from by decide,
    show (255 : Nat) = 2 ^ 8 - 1 from by decide,
    nat_land_mask_eq_mod]
  have hlt : w.toNat % 2 ^ 8 < EVM.twoPow 256 := by
    exact lt_of_lt_of_le (Nat.mod_lt _ (by norm_num : 0 < 2 ^ 8)) (by
      norm_num [EVM.twoPow])
  rw [Nat.mod_eq_of_lt hlt]
  rw [show EVM.twoPow 8 = 2 ^ 8 from by decide]

theorem bytesStoreSetPacketByteLand255_eq_self_of_uint8 {w : UInt256}
    (h : w.toNat < EVM.twoPow 8) :
    UInt256.land w ⟨255⟩ = w := by
  apply u256_inj
  rw [bytesStoreSetPacketByteLand255_toNat]
  exact Nat.mod_eq_of_lt h

theorem bytesStoreSetPacketByteLand255_ne_self_of_not_uint8 {w : UInt256}
    (h : ¬ w.toNat < EVM.twoPow 8) :
    UInt256.land w ⟨255⟩ ≠ w := by
  intro hland
  apply h
  have hnat : (UInt256.land w ⟨255⟩).toNat = w.toNat := by
    rw [hland]
  rw [bytesStoreSetPacketByteLand255_toNat] at hnat
  rw [← hnat]
  exact Nat.mod_lt _ (by decide : 0 < EVM.twoPow 8)

theorem bytesStoreX_setPacketByteDecodeValid {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨282⟩ [bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hsz68 : 68 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hsize : I.calldata.size < UInt256.size)
    (hcanon : UInt256.land (bytesStoreSetByteValueWord I) ⟨255⟩ =
      bytesStoreSetByteValueWord I) :
    ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨601⟩
      [bytesStoreSetByteValueWord I, bytesStoreSetByteIndexWord I, ⟨301⟩,
        bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd282⟩ := hreach
  have hslt :
      UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ = ⟨0⟩ :=
    solcDecodeLenCheckOk_4_64 hsz68 hhi hsize
  have rd1967 := evm_run rd282 with [
    jumpdest, push2 ⟨301⟩, push2 ⟨296⟩, calldatasize, push1 ⟨4⟩,
    push2 ⟨1967⟩, jump (by native_decide)]
  have rd1984 := evm_run rd1967 with [
    jumpdest, push0, push0, push1 ⟨64⟩, dup4, dup6, sub, slt, iszero,
    push2 ⟨1984⟩, jumpiT (by rw [hslt]; decide) (by native_decide)]
  have rd1946 := evm_run rd1984 with [
    jumpdest, dup3, calldataload, swap2, pop, push2 ⟨2000⟩, push1 ⟨32⟩,
    dup5, add, push2 ⟨1946⟩, jump (by native_decide)]
  rw [show (⟨4⟩ : UInt256).toNat = 4 from by decide,
    show uInt256OfByteArray (I.calldata.readBytes 4 32) =
      bytesStoreSetByteIndexWord I from rfl,
    show (⟨4⟩ + ⟨32⟩ : UInt256) = ⟨36⟩ from by native_decide] at rd1946
  have rd1950 := evm_run rd1946 with [
    jumpdest, dup1, calldataload]
  rw [show (⟨36⟩ : UInt256).toNat = 36 from by decide,
    show uInt256OfByteArray (I.calldata.readBytes 36 32) =
      bytesStoreSetByteValueWord I from rfl] at rd1950
  have rd2000 := evm_run rd1950 with [
    push1 ⟨255⟩, dup2, and, dup2, eq,
    push2 ⟨1962⟩,
    jumpiT (by rw [bytesStoreSetPacketByteUint8CanonEqGuard hcanon]; decide)
      (by native_decide),
    jumpdest, swap2, swap1, pop, jump (by native_decide)]
  exact ⟨_, _, evm_run rd2000 with [
    jumpdest, swap1, pop, swap3, pop, swap3, swap1, pop, jump (by native_decide),
    jumpdest, push2 ⟨601⟩, jump (by native_decide)]⟩

theorem bytesStoreX_setPacketByteDecodeShort {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨282⟩ [bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 68)
    (hsize : I.calldata.size < UInt256.size) :
    RDrev bytesStoreBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd282⟩ := hreach
  have hslt :
      UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ = ⟨1⟩ :=
    solcDecodeLenCheckShort_4_64 hsz4 hshort hsize
  have rd1967 := evm_run rd282 with [
    jumpdest, push2 ⟨301⟩, push2 ⟨296⟩, calldatasize, push1 ⟨4⟩,
    push2 ⟨1967⟩, jump (by native_decide)]
  exact evm_run rd1967 with [
    jumpdest, push0, push0, push1 ⟨64⟩, dup4, dup6, sub, slt, iszero,
    push2 ⟨1984⟩, jumpiNT (by rw [hslt]; decide),
    raw revertStub (by native_decide) (by native_decide) (by native_decide) (by evm_ov)]

theorem bytesStoreX_setPacketByteDecodeHuge {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨282⟩ [bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size) :
    RDrev bytesStoreBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd282⟩ := hreach
  have hslt :
      UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ = ⟨1⟩ :=
    solcDecodeLenCheckHuge_4_64 hbig hsize
  have rd1967 := evm_run rd282 with [
    jumpdest, push2 ⟨301⟩, push2 ⟨296⟩, calldatasize, push1 ⟨4⟩,
    push2 ⟨1967⟩, jump (by native_decide)]
  exact evm_run rd1967 with [
    jumpdest, push0, push0, push1 ⟨64⟩, dup4, dup6, sub, slt, iszero,
    push2 ⟨1984⟩, jumpiNT (by rw [hslt]; decide),
    raw revertStub (by native_decide) (by native_decide) (by native_decide) (by evm_ov)]

theorem bytesStoreX_setPacketByteDecodeNoncanonValue {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨282⟩ [bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hsz68 : 68 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hsize : I.calldata.size < UInt256.size)
    (hnc : UInt256.land (bytesStoreSetByteValueWord I) ⟨255⟩ ≠
      bytesStoreSetByteValueWord I) :
    RDrev bytesStoreBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd282⟩ := hreach
  have hslt :
      UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ = ⟨0⟩ :=
    solcDecodeLenCheckOk_4_64 hsz68 hhi hsize
  have rd1967 := evm_run rd282 with [
    jumpdest, push2 ⟨301⟩, push2 ⟨296⟩, calldatasize, push1 ⟨4⟩,
    push2 ⟨1967⟩, jump (by native_decide)]
  have rd1984 := evm_run rd1967 with [
    jumpdest, push0, push0, push1 ⟨64⟩, dup4, dup6, sub, slt, iszero,
    push2 ⟨1984⟩, jumpiT (by rw [hslt]; decide) (by native_decide)]
  have rd1946 := evm_run rd1984 with [
    jumpdest, dup3, calldataload, swap2, pop, push2 ⟨2000⟩, push1 ⟨32⟩,
    dup5, add, push2 ⟨1946⟩, jump (by native_decide)]
  rw [show (⟨4⟩ : UInt256).toNat = 4 from by decide,
    show uInt256OfByteArray (I.calldata.readBytes 4 32) =
      bytesStoreSetByteIndexWord I from rfl,
    show (⟨4⟩ + ⟨32⟩ : UInt256) = ⟨36⟩ from by native_decide] at rd1946
  have rd1950 := evm_run rd1946 with [
    jumpdest, dup1, calldataload]
  rw [show (⟨36⟩ : UInt256).toNat = 36 from by decide,
    show uInt256OfByteArray (I.calldata.readBytes 36 32) =
      bytesStoreSetByteValueWord I from rfl] at rd1950
  exact evm_run rd1950 with [
    push1 ⟨255⟩, dup2, and, dup2, eq,
    push2 ⟨1962⟩,
    jumpiNT (by rw [bytesStoreSetPacketByteUint8NoncanonEqGuard hnc]),
    raw revertStub (by native_decide) (by native_decide) (by native_decide) (by evm_ov)]

theorem bytesStoreX_setPacketByteReachLengthDecoder {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨601⟩
      [bytesStoreSetByteValueWord I, bytesStoreSetByteIndexWord I, ⟨301⟩,
        bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2246⟩
      [bytesStorePacketLengthHeaderWord σ I, ⟨622⟩,
        bytesStoreSetByteIndexWord I, ⟨2⟩,
        UInt256.shiftLeft (bytesStoreSetByteValueWord I) ⟨248⟩, ⟨0⟩,
        bytesStoreSetByteValueWord I, bytesStoreSetByteIndexWord I, ⟨301⟩,
        bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd601⟩ := hreach
  have rd613 := evm_run rd601 with [
    jumpdest, push0, dup2, push1 ⟨248⟩, shl, push1 ⟨2⟩, push0, add, dup5, dup2]
  obtain ⟨_, _, rd614₀⟩ := rd613.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd614⟩ :
      ∃ k C, RD bytesStoreBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨614⟩
        [bytesStorePacketLengthHeaderWord σ I, bytesStoreSetByteIndexWord I, ⟨2⟩,
          UInt256.shiftLeft (bytesStoreSetByteValueWord I) ⟨248⟩, ⟨0⟩,
          bytesStoreSetByteValueWord I, bytesStoreSetByteIndexWord I, ⟨301⟩,
          bytesStoreSelWord I]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by
      simpa [bytesStorePacketLengthHeaderWord, initState] using rd614₀⟩
  exact ⟨_, _, evm_run rd614 with [
    push2 ⟨622⟩, swap1, push2 ⟨2246⟩, jump (by native_decide)]⟩

theorem bytesStoreX_setPacketByteOobAfterLength {cA gh bl σ σ₀ A I} {g : Sat256}
    {len : UInt256}
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨622⟩
      [len, bytesStoreSetByteIndexWord I, ⟨2⟩,
        UInt256.shiftLeft (bytesStoreSetByteValueWord I) ⟨248⟩, ⟨0⟩,
        bytesStoreSetByteValueWord I, bytesStoreSetByteIndexWord I, ⟨301⟩,
        bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hbound : ¬ (bytesStoreSetByteIndexWord I).toNat < len.toNat) :
    RDrev bytesStoreBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd622⟩ := hreach
  have hlt : UInt256.lt (bytesStoreSetByteIndexWord I) len = ⟨0⟩ :=
    ult_zero (by omega)
  have rd2579 := evm_run rd622 with [
    jumpdest, dup2, lt, push2 ⟨636⟩,
    jumpiNT (by simpa using hlt),
    push2 ⟨636⟩, push2 ⟨2579⟩, jump (by native_decide)]
  exact bytesStoreX_panic32Mem ⟨_, _, rd2579⟩
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem bytesStoreX_setPacketBytePanic32MemFromReach
    {cA gh bl σinit σ σ₀ A I} {g : Sat256} {stk : List UInt256} {mem : ByteArray}
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨2579⟩ stk
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hov : stk.length + 3 ≤ 1024) :
    RDrev bytesStoreBytecode g (initState cA gh bl σinit σ₀ g A I) := by
  obtain ⟨_, _, rd2579⟩ := hreach
  have hsel :
      UInt256.shiftLeft (⟨0x4e487b71⟩ : UInt256) ⟨224⟩ =
        bytesStoreFullPanicSelectorWord := by
    decide
  have rd2591₀ := evm_run rd2579 with [
    jumpdest, push4 ⟨0x4e487b71⟩, push1 ⟨224⟩, shl, push0]
  have rd2591 := rd2591₀
  rw [hsel] at rd2591
  exact evm_run rd2591 with [
    raw mstore 0 (bytesStoreFullPanic22Mem1From mem) (UInt256.ofNat 3) (by native_decide)
      mem_cost
      (by rw [show (⟨0⟩ : UInt256).toNat = 0 from rfl]; rfl)
      (by decide) (by evm_ov),
    push1 ⟨0x32⟩, push1 ⟨4⟩,
    raw mstore 0 (bytesStoreFullPanicMemFrom ⟨0x32⟩ mem) (UInt256.ofNat 3)
      (by native_decide)
      mem_cost
      (by rw [show (⟨4⟩ : UInt256).toNat = 4 from by decide]; rfl)
      (by decide) (by evm_ov),
    push1 ⟨36⟩, push0,
    raw rev 0 (by native_decide) mem_cost
      (by evm_ov)]

theorem bytesStoreX_setPacketByteReturnOobLength
    {cA gh bl σinit σ σ₀ A I} {g : Sat256} {len : UInt256}
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨709⟩
      [len, bytesStoreSetByteIndexWord I, ⟨2⟩, ⟨0⟩,
        bytesStoreSetByteValueWord I, bytesStoreSetByteIndexWord I, ⟨301⟩,
        bytesStoreSelWord I]
      (wordAt0Mem (⟨2⟩ : UInt256) solcFreePtrMem) (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C)
    (hbound : ¬ (bytesStoreSetByteIndexWord I).toNat < len.toNat) :
    RDrev bytesStoreBytecode g (initState cA gh bl σinit σ₀ g A I) := by
  obtain ⟨_, _, rd709⟩ := hreach
  have hlt : UInt256.lt (bytesStoreSetByteIndexWord I) len = ⟨0⟩ :=
    ult_zero (by omega)
  have rd2579 := evm_run rd709 with [
    jumpdest, dup2, lt, push2 ⟨723⟩,
    jumpiNT (by simpa using hlt),
    push2 ⟨723⟩, push2 ⟨2579⟩, jump (by native_decide)]
  exact bytesStoreX_setPacketBytePanic32MemFromReach ⟨_, _, rd2579⟩
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem bytesStoreX_setPacketByteOobLong {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨601⟩
      [bytesStoreSetByteValueWord I, bytesStoreSetByteIndexWord I, ⟨301⟩,
        bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hflag : UInt256.land (bytesStorePacketLengthHeaderWord σ I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (bytesStorePacketLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStorePacketLengthHeaderWord σ I) ⟨2⟩) ⟨32⟩) ≠ ⟨0⟩)
    (hbound :
      ¬ (bytesStoreSetByteIndexWord I).toNat <
        (UInt256.div (bytesStorePacketLengthHeaderWord σ I) ⟨2⟩).toNat) :
    RDrev bytesStoreBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hdec := bytesStoreX_setPacketByteReachLengthDecoder hreach
  have hlen := bytesStoreX_bytesLengthDecoderLongValidMem
    (A := A) (I := I) (g := g) hdec hflag hvalid (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  exact bytesStoreX_setPacketByteOobAfterLength (g := g) hlen hbound

theorem bytesStoreX_setPacketByteOobShort {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨601⟩
      [bytesStoreSetByteValueWord I, bytesStoreSetByteIndexWord I, ⟨301⟩,
        bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hflag : UInt256.land (bytesStorePacketLengthHeaderWord σ I) ⟨1⟩ = ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (bytesStorePacketLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStorePacketLengthHeaderWord σ I) ⟨2⟩) ⟨127⟩)
          ⟨32⟩) ≠ ⟨0⟩)
    (hbound :
      ¬ (bytesStoreSetByteIndexWord I).toNat <
        (UInt256.land (UInt256.div (bytesStorePacketLengthHeaderWord σ I) ⟨2⟩) ⟨127⟩).toNat) :
    RDrev bytesStoreBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hdec := bytesStoreX_setPacketByteReachLengthDecoder hreach
  have hlen := bytesStoreX_bytesLengthDecoderShortValidMem
    (A := A) (I := I) (g := g) hdec hflag hvalid (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  exact bytesStoreX_setPacketByteOobAfterLength (g := g) hlen hbound

theorem bytesStoreX_setPacketByteLongMalformed {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨601⟩
      [bytesStoreSetByteValueWord I, bytesStoreSetByteIndexWord I, ⟨301⟩,
        bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hflag : UInt256.land (bytesStorePacketLengthHeaderWord σ I) ⟨1⟩ ≠ ⟨0⟩)
    (hbad : UInt256.sub (UInt256.land (bytesStorePacketLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStorePacketLengthHeaderWord σ I) ⟨2⟩) ⟨32⟩) = ⟨0⟩) :
    RDrev bytesStoreBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hdec := bytesStoreX_setPacketByteReachLengthDecoder (g := g) hreach
  exact bytesStoreX_bytesLengthDecoderLongMalformedMem
    hdec hflag hbad (by simp only [List.length_cons, List.length_nil]; omega)

theorem bytesStoreX_setPacketByteShortMalformed {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨601⟩
      [bytesStoreSetByteValueWord I, bytesStoreSetByteIndexWord I, ⟨301⟩,
        bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hflag : UInt256.land (bytesStorePacketLengthHeaderWord σ I) ⟨1⟩ = ⟨0⟩)
    (hbad : UInt256.sub (UInt256.land (bytesStorePacketLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStorePacketLengthHeaderWord σ I) ⟨2⟩) ⟨127⟩)
          ⟨32⟩) = ⟨0⟩) :
    RDrev bytesStoreBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hdec := bytesStoreX_setPacketByteReachLengthDecoder (g := g) hreach
  exact bytesStoreX_bytesLengthDecoderShortMalformedMem
    hdec hflag hbad (by simp only [List.length_cons, List.length_nil]; omega)

theorem bytesStoreX_setPacketByteShortReachStoreCommon {cA gh bl σ σ₀ A I}
    {g : Sat256} {len : UInt256}
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨622⟩
      [len, bytesStoreSetByteIndexWord I, ⟨2⟩,
        UInt256.shiftLeft (bytesStoreSetByteValueWord I) ⟨248⟩, ⟨0⟩,
        bytesStoreSetByteValueWord I, bytesStoreSetByteIndexWord I, ⟨301⟩,
        bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hbound : (bytesStoreSetByteIndexWord I).toNat < len.toNat)
    (hflag : UInt256.land (bytesStorePacketLengthHeaderWord σ I) ⟨1⟩ = ⟨0⟩) :
    ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨665⟩
      [bytesStoreSetByteIndexWord I, ⟨2⟩,
        UInt256.shiftLeft (bytesStoreSetByteValueWord I) ⟨248⟩, ⟨0⟩,
        bytesStoreSetByteValueWord I, bytesStoreSetByteIndexWord I, ⟨301⟩,
        bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd622⟩ := hreach
  have hlt : UInt256.lt (bytesStoreSetByteIndexWord I) len = ⟨1⟩ :=
    ult_one hbound
  have rd636 := evm_run rd622 with [
    jumpdest, dup2, lt, push2 ⟨636⟩,
    jumpiT (by rw [hlt]; decide) (by native_decide)]
  have rd638 := evm_run rd636 with [jumpdest, dup2]
  obtain ⟨_, _, rd639₀⟩ := rd638.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd639⟩ :
      ∃ k C, RD bytesStoreBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨639⟩
        [bytesStorePacketLengthHeaderWord σ I, bytesStoreSetByteIndexWord I, ⟨2⟩,
          UInt256.shiftLeft (bytesStoreSetByteValueWord I) ⟨248⟩, ⟨0⟩,
          bytesStoreSetByteValueWord I, bytesStoreSetByteIndexWord I, ⟨301⟩,
          bytesStoreSelWord I]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by
      simpa [bytesStorePacketLengthHeaderWord, initState] using rd639₀⟩
  have rd665 := evm_run rd639 with [
    push1 ⟨1⟩, and, iszero, push2 ⟨665⟩,
    jumpiT (by
      rw [u256_land_comm, hflag]
      decide)
      (by native_decide)]
  exact ⟨_, _, rd665⟩

theorem bytesStoreX_setPacketByteLongReachStoreCommon {cA gh bl σ σ₀ A I}
    {g : Sat256} {len : UInt256}
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨622⟩
      [len, bytesStoreSetByteIndexWord I, ⟨2⟩,
        UInt256.shiftLeft (bytesStoreSetByteValueWord I) ⟨248⟩, ⟨0⟩,
        bytesStoreSetByteValueWord I, bytesStoreSetByteIndexWord I, ⟨301⟩,
        bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hbound : (bytesStoreSetByteIndexWord I).toNat < len.toNat)
    (hflag : UInt256.land (bytesStorePacketLengthHeaderWord σ I) ⟨1⟩ ≠ ⟨0⟩) :
    ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨665⟩
      [bytesStoreSetPacketByteLongWordIndex I, bytesStoreSetPacketByteLongDataSlot I,
        UInt256.shiftLeft (bytesStoreSetByteValueWord I) ⟨248⟩, ⟨0⟩,
        bytesStoreSetByteValueWord I, bytesStoreSetByteIndexWord I, ⟨301⟩,
        bytesStoreSelWord I]
      (wordAt0Mem (⟨2⟩ : UInt256) solcFreePtrMem) (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd622⟩ := hreach
  have hlt : UInt256.lt (bytesStoreSetByteIndexWord I) len = ⟨1⟩ :=
    ult_one hbound
  have hflagOne :
      UInt256.land (bytesStorePacketLengthHeaderWord σ I) ⟨1⟩ = ⟨1⟩ :=
    u256_land_one_eq_one_of_ne_zero hflag
  have hslot := bytesStoreSetPacketByteLongBaseHash
  have rd636 := evm_run rd622 with [
    jumpdest, dup2, lt, push2 ⟨636⟩,
    jumpiT (by rw [hlt]; decide) (by native_decide)]
  have rd638 := evm_run rd636 with [jumpdest, dup2]
  obtain ⟨_, _, rd639₀⟩ := rd638.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd639⟩ :
      ∃ k C, RD bytesStoreBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨639⟩
        [bytesStorePacketLengthHeaderWord σ I, bytesStoreSetByteIndexWord I, ⟨2⟩,
          UInt256.shiftLeft (bytesStoreSetByteValueWord I) ⟨248⟩, ⟨0⟩,
          bytesStoreSetByteValueWord I, bytesStoreSetByteIndexWord I, ⟨301⟩,
          bytesStoreSelWord I]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by
      simpa [bytesStorePacketLengthHeaderWord, initState] using rd639₀⟩
  have rd664 := evm_run rd639 with [
    push1 ⟨1⟩, and, iszero, push2 ⟨665⟩,
    jumpiNT (by
      rw [u256_land_comm, hflagOne]
      decide),
    swap1, push0,
    raw mstore 0 (wordAt0Mem (⟨2⟩ : UInt256) solcFreePtrMem)
      (UInt256.ofNat 3) (by native_decide)
      mem_cost
      (by rfl)
      (by native_decide) (by evm_ov),
    push1 ⟨32⟩, push0,
    raw keccak256 0 (bytesLikeDataBase ⟨2⟩) (UInt256.ofNat 3)
      (by native_decide) mem_cost hslot (by native_decide) (by evm_ov),
    swap1, push1 ⟨32⟩, swap2, dup3, dup3, div, add, swap2, swap1]
  have rd665raw := RD.mod rd664 (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  exact ⟨_, _, by
    simpa [bytesStoreSetPacketByteLongWordIndex,
      bytesStoreSetPacketByteLongDataSlot,
      u256_add_comm (UInt256.div (bytesStoreSetByteIndexWord I) ⟨32⟩)
        (bytesLikeDataBase ⟨2⟩)] using rd665raw⟩

theorem bytesStoreX_setPacketByteShortStorePacket {cA gh bl σ σ₀ A I}
    {g : Sat256}
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨665⟩
      [bytesStoreSetByteIndexWord I, ⟨2⟩,
        UInt256.shiftLeft (bytesStoreSetByteValueWord I) ⟨248⟩, ⟨0⟩,
        bytesStoreSetByteValueWord I, bytesStoreSetByteIndexWord I, ⟨301⟩,
        bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hperm : I.perm = true) :
    ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨694⟩
      [⟨0⟩, bytesStoreSetByteValueWord I, bytesStoreSetByteIndexWord I, ⟨301⟩,
        bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ ⟨2⟩
        (bytesStoreSetPacketByteShortStoredWord σ I)) k C := by
  obtain ⟨_, _, rd665⟩ := hreach
  have rd674 := evm_run rd665 with [
    jumpdest, push1 ⟨31⟩, sub, push2 ⟨256⟩, exp, dup2]
  obtain ⟨_, _, rd675₀⟩ := rd674.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd675⟩ :
      ∃ k C, RD bytesStoreBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨675⟩
        [bytesStorePacketLengthHeaderWord σ I,
          UInt256.exp ⟨256⟩ (UInt256.sub ⟨31⟩ (bytesStoreSetByteIndexWord I)),
          ⟨2⟩, UInt256.shiftLeft (bytesStoreSetByteValueWord I) ⟨248⟩, ⟨0⟩,
          bytesStoreSetByteValueWord I, bytesStoreSetByteIndexWord I, ⟨301⟩,
          bytesStoreSelWord I]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by
      simpa [bytesStorePacketLengthHeaderWord, initState] using rd675₀⟩
  have rd692 := evm_run rd675 with [
    dup2, push1 ⟨255⟩, mul, not, and, swap1,
    push1 ⟨1⟩, push1 ⟨248⟩, shl, dup5, div, mul, lor, swap1]
  obtain ⟨_, _, rd692'⟩ :
      ∃ k C, RD bytesStoreBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨692⟩
        [⟨2⟩,
          bytesStoreSetPacketByteShortStoredWord σ I,
          UInt256.shiftLeft (bytesStoreSetByteValueWord I) ⟨248⟩, ⟨0⟩,
          bytesStoreSetByteValueWord I, bytesStoreSetByteIndexWord I, ⟨301⟩,
          bytesStoreSelWord I]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by
      simpa [bytesStoreSetPacketByteShortStoredWord,
        bytesStoreSetPacketByteShortScale] using rd692⟩
  obtain ⟨_, _, rd693₀⟩ := rd692'.sstore hperm (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd693⟩ :
      ∃ k C, RD bytesStoreBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨693⟩
        [UInt256.shiftLeft (bytesStoreSetByteValueWord I) ⟨248⟩, ⟨0⟩,
          bytesStoreSetByteValueWord I, bytesStoreSetByteIndexWord I, ⟨301⟩,
          bytesStoreSelWord I]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, sstoreAccountMap I.codeOwner σ ⟨2⟩
          (bytesStoreSetPacketByteShortStoredWord σ I)) k C := by
    exact ⟨_, _, by simpa [sstoreAccountMap, initState] using rd693₀⟩
  exact ⟨_, _, evm_run rd693 with [pop]⟩

theorem bytesStoreX_setPacketByteLongStorePacket {cA gh bl σ σ₀ A I}
    {g : Sat256}
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨665⟩
      [bytesStoreSetPacketByteLongWordIndex I, bytesStoreSetPacketByteLongDataSlot I,
        UInt256.shiftLeft (bytesStoreSetByteValueWord I) ⟨248⟩, ⟨0⟩,
        bytesStoreSetByteValueWord I, bytesStoreSetByteIndexWord I, ⟨301⟩,
        bytesStoreSelWord I]
      (wordAt0Mem (⟨2⟩ : UInt256) solcFreePtrMem) (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C)
    (hperm : I.perm = true) :
    ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨694⟩
      [⟨0⟩, bytesStoreSetByteValueWord I, bytesStoreSetByteIndexWord I, ⟨301⟩,
        bytesStoreSelWord I]
      (wordAt0Mem (⟨2⟩ : UInt256) solcFreePtrMem) (UInt256.ofNat 3)
      ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ (bytesStoreSetPacketByteLongDataSlot I)
        (bytesStoreSetPacketByteLongStoredWord σ I)) k C := by
  obtain ⟨_, _, rd665⟩ := hreach
  have rd674 := evm_run rd665 with [
    jumpdest, push1 ⟨31⟩, sub, push2 ⟨256⟩, exp, dup2]
  obtain ⟨_, _, rd675₀⟩ := rd674.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd675⟩ :
      ∃ k C, RD bytesStoreBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨675⟩
        [bytesStoreSetPacketByteLongOldWord σ I,
          UInt256.exp ⟨256⟩ (UInt256.sub ⟨31⟩
            (bytesStoreSetPacketByteLongWordIndex I)),
          bytesStoreSetPacketByteLongDataSlot I,
          UInt256.shiftLeft (bytesStoreSetByteValueWord I) ⟨248⟩, ⟨0⟩,
          bytesStoreSetByteValueWord I, bytesStoreSetByteIndexWord I, ⟨301⟩,
          bytesStoreSelWord I]
        (wordAt0Mem (⟨2⟩ : UInt256) solcFreePtrMem) (UInt256.ofNat 3)
        ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by
      simpa [bytesStoreSetPacketByteLongOldWord, initState] using rd675₀⟩
  have rd692 := evm_run rd675 with [
    dup2, push1 ⟨255⟩, mul, not, and, swap1,
    push1 ⟨1⟩, push1 ⟨248⟩, shl, dup5, div, mul, lor, swap1]
  obtain ⟨_, _, rd692'⟩ :
      ∃ k C, RD bytesStoreBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨692⟩
        [bytesStoreSetPacketByteLongDataSlot I,
          bytesStoreSetPacketByteLongStoredWord σ I,
          UInt256.shiftLeft (bytesStoreSetByteValueWord I) ⟨248⟩, ⟨0⟩,
          bytesStoreSetByteValueWord I, bytesStoreSetByteIndexWord I, ⟨301⟩,
          bytesStoreSelWord I]
        (wordAt0Mem (⟨2⟩ : UInt256) solcFreePtrMem) (UInt256.ofNat 3)
        ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by
      simpa [bytesStoreSetPacketByteLongStoredWord,
        bytesStoreSetPacketByteLongScale] using rd692⟩
  obtain ⟨_, _, rd693₀⟩ := rd692'.sstore hperm (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd693⟩ :
      ∃ k C, RD bytesStoreBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨693⟩
        [UInt256.shiftLeft (bytesStoreSetByteValueWord I) ⟨248⟩, ⟨0⟩,
          bytesStoreSetByteValueWord I, bytesStoreSetByteIndexWord I, ⟨301⟩,
          bytesStoreSelWord I]
        (wordAt0Mem (⟨2⟩ : UInt256) solcFreePtrMem) (UInt256.ofNat 3)
        ByteArray.empty
        (cA, sstoreAccountMap I.codeOwner σ (bytesStoreSetPacketByteLongDataSlot I)
          (bytesStoreSetPacketByteLongStoredWord σ I)) k C := by
    exact ⟨_, _, by simpa [sstoreAccountMap, initState] using rd693₀⟩
  exact ⟨_, _, evm_run rd693 with [pop]⟩

theorem bytesStoreX_setPacketByteReturnReachLengthDecoder
    {cA gh bl σinit σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨694⟩
      [⟨0⟩, bytesStoreSetByteValueWord I, bytesStoreSetByteIndexWord I, ⟨301⟩,
        bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨2246⟩
      [Option.option ⟨0⟩ (fun ac => Batteries.RBMap.findD ac.storage ⟨2⟩ ⟨0⟩)
          (Batteries.RBMap.find? σ I.codeOwner),
        ⟨709⟩,
        bytesStoreSetByteIndexWord I, ⟨2⟩, ⟨0⟩,
        bytesStoreSetByteValueWord I, bytesStoreSetByteIndexWord I, ⟨301⟩,
        bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd694⟩ := hreach
  have rd700 := evm_run rd694 with [push1 ⟨2⟩, push0, add, dup4, dup2]
  obtain ⟨_, _, rd701₀⟩ := rd700.sload (by native_decide) (by evm_ov)
  have rd2246 := evm_run rd701₀ with [
    push2 ⟨709⟩, swap1, push2 ⟨2246⟩, jump (by native_decide)]
  exact ⟨_, _, rd2246⟩

theorem bytesStoreX_setPacketByteReturnReachLengthDecoderMem
    {cA gh bl σinit σ σ₀ A I} {g : Sat256} {mem : ByteArray}
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨694⟩
      [⟨0⟩, bytesStoreSetByteValueWord I, bytesStoreSetByteIndexWord I, ⟨301⟩,
        bytesStoreSelWord I]
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨2246⟩
      [Option.option ⟨0⟩ (fun ac => Batteries.RBMap.findD ac.storage ⟨2⟩ ⟨0⟩)
          (Batteries.RBMap.find? σ I.codeOwner),
        ⟨709⟩,
        bytesStoreSetByteIndexWord I, ⟨2⟩, ⟨0⟩,
        bytesStoreSetByteValueWord I, bytesStoreSetByteIndexWord I, ⟨301⟩,
        bytesStoreSelWord I]
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd694⟩ := hreach
  have rd700 := evm_run rd694 with [push1 ⟨2⟩, push0, add, dup4, dup2]
  obtain ⟨_, _, rd701₀⟩ := rd700.sload (by native_decide) (by evm_ov)
  have rd2246 := evm_run rd701₀ with [
    push2 ⟨709⟩, swap1, push2 ⟨2246⟩, jump (by native_decide)]
  exact ⟨_, _, rd2246⟩

theorem bytesStoreX_setPacketByteLongWriteReturnReachLengthDecoder
    {cA gh bl σ σ₀ A I} {g : Sat256} {len : UInt256}
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨622⟩
      [len, bytesStoreSetByteIndexWord I, ⟨2⟩,
        UInt256.shiftLeft (bytesStoreSetByteValueWord I) ⟨248⟩, ⟨0⟩,
        bytesStoreSetByteValueWord I, bytesStoreSetByteIndexWord I, ⟨301⟩,
        bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hbound : (bytesStoreSetByteIndexWord I).toNat < len.toNat)
    (hflag : UInt256.land (bytesStorePacketLengthHeaderWord σ I) ⟨1⟩ ≠ ⟨0⟩)
    (hperm : I.perm = true) :
    ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2246⟩
      [Option.option ⟨0⟩ (fun ac => Batteries.RBMap.findD ac.storage ⟨2⟩ ⟨0⟩)
          (Batteries.RBMap.find?
            (sstoreAccountMap I.codeOwner σ (bytesStoreSetPacketByteLongDataSlot I)
              (bytesStoreSetPacketByteLongStoredWord σ I)) I.codeOwner),
        ⟨709⟩, bytesStoreSetByteIndexWord I, ⟨2⟩, ⟨0⟩,
        bytesStoreSetByteValueWord I, bytesStoreSetByteIndexWord I, ⟨301⟩,
        bytesStoreSelWord I]
      (wordAt0Mem (⟨2⟩ : UInt256) solcFreePtrMem) (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ (bytesStoreSetPacketByteLongDataSlot I)
        (bytesStoreSetPacketByteLongStoredWord σ I)) k C := by
  have h665 := bytesStoreX_setPacketByteLongReachStoreCommon
    (g := g) hreach hbound hflag
  have h694 := bytesStoreX_setPacketByteLongStorePacket
    (g := g) h665 hperm
  exact bytesStoreX_setPacketByteReturnReachLengthDecoderMem
    (σinit := σ)
    (σ := sstoreAccountMap I.codeOwner σ (bytesStoreSetPacketByteLongDataSlot I)
      (bytesStoreSetPacketByteLongStoredWord σ I))
    h694

theorem bytesStoreX_setPacketByteLongWriteReturnDecodedPostLongLength
    {cA gh bl σ σ₀ A I} {g : Sat256} {len lenPost : UInt256}
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨622⟩
      [len, bytesStoreSetByteIndexWord I, ⟨2⟩,
        UInt256.shiftLeft (bytesStoreSetByteValueWord I) ⟨248⟩, ⟨0⟩,
        bytesStoreSetByteValueWord I, bytesStoreSetByteIndexWord I, ⟨301⟩,
        bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hbound : (bytesStoreSetByteIndexWord I).toNat < len.toNat)
    (hflag : UInt256.land (bytesStorePacketLengthHeaderWord σ I) ⟨1⟩ ≠ ⟨0⟩)
    (hlenPost : lenPost = UInt256.div
      (bytesStorePacketLengthHeaderWord
        (sstoreAccountMap I.codeOwner σ (bytesStoreSetPacketByteLongDataSlot I)
          (bytesStoreSetPacketByteLongStoredWord σ I)) I) ⟨2⟩)
    (hflagPost : UInt256.land
        (bytesStorePacketLengthHeaderWord
          (sstoreAccountMap I.codeOwner σ (bytesStoreSetPacketByteLongDataSlot I)
            (bytesStoreSetPacketByteLongStoredWord σ I)) I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalidPost : UInt256.sub (UInt256.land
        (bytesStorePacketLengthHeaderWord
          (sstoreAccountMap I.codeOwner σ (bytesStoreSetPacketByteLongDataSlot I)
            (bytesStoreSetPacketByteLongStoredWord σ I)) I) ⟨1⟩)
        (UInt256.lt (UInt256.div
          (bytesStorePacketLengthHeaderWord
            (sstoreAccountMap I.codeOwner σ (bytesStoreSetPacketByteLongDataSlot I)
              (bytesStoreSetPacketByteLongStoredWord σ I)) I) ⟨2⟩) ⟨32⟩) ≠ ⟨0⟩)
    (hperm : I.perm = true) :
    ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨709⟩
      [lenPost, bytesStoreSetByteIndexWord I, ⟨2⟩, ⟨0⟩,
        bytesStoreSetByteValueWord I, bytesStoreSetByteIndexWord I, ⟨301⟩,
        bytesStoreSelWord I]
      (wordAt0Mem (⟨2⟩ : UInt256) solcFreePtrMem) (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ (bytesStoreSetPacketByteLongDataSlot I)
        (bytesStoreSetPacketByteLongStoredWord σ I)) k C := by
  let σ' := sstoreAccountMap I.codeOwner σ (bytesStoreSetPacketByteLongDataSlot I)
    (bytesStoreSetPacketByteLongStoredWord σ I)
  let header' : UInt256 :=
    Option.option ⟨0⟩ (fun ac => Batteries.RBMap.findD ac.storage ⟨2⟩ ⟨0⟩)
      (Batteries.RBMap.find? σ' I.codeOwner)
  have hdec := bytesStoreX_setPacketByteLongWriteReturnReachLengthDecoder
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (I := I) (g := g) (len := len) hreach hbound hflag hperm
  have hheader : header' = bytesStorePacketLengthHeaderWord σ' I := by
    rfl
  have hdecoded := bytesStoreX_bytesLengthDecoderLongValidMemCarried
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (τ := σ') (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (header := header') (ret := ⟨709⟩)
    (rest := [bytesStoreSetByteIndexWord I, ⟨2⟩, ⟨0⟩,
      bytesStoreSetByteValueWord I, bytesStoreSetByteIndexWord I, ⟨301⟩,
      bytesStoreSelWord I])
    (mem := wordAt0Mem (⟨2⟩ : UInt256) solcFreePtrMem)
    (aw := UInt256.ofNat 3) (rdata := ByteArray.empty)
    (by simpa [header', σ'] using hdec)
    (by simpa [hheader, σ'] using hflagPost)
    (by simpa [hheader, σ'] using hvalidPost)
    (by native_decide)
    (by simp)
  simpa [σ', header', hheader, hlenPost] using hdecoded

theorem bytesStoreX_setPacketByteLongWriteReturnDecodedPostShortLength
    {cA gh bl σ σ₀ A I} {g : Sat256} {len lenPost : UInt256}
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨622⟩
      [len, bytesStoreSetByteIndexWord I, ⟨2⟩,
        UInt256.shiftLeft (bytesStoreSetByteValueWord I) ⟨248⟩, ⟨0⟩,
        bytesStoreSetByteValueWord I, bytesStoreSetByteIndexWord I, ⟨301⟩,
        bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hbound : (bytesStoreSetByteIndexWord I).toNat < len.toNat)
    (hflag : UInt256.land (bytesStorePacketLengthHeaderWord σ I) ⟨1⟩ ≠ ⟨0⟩)
    (hlenPost : lenPost = UInt256.land (UInt256.div
      (bytesStorePacketLengthHeaderWord
        (sstoreAccountMap I.codeOwner σ (bytesStoreSetPacketByteLongDataSlot I)
          (bytesStoreSetPacketByteLongStoredWord σ I)) I) ⟨2⟩) ⟨127⟩)
    (hflagPost : UInt256.land
        (bytesStorePacketLengthHeaderWord
          (sstoreAccountMap I.codeOwner σ (bytesStoreSetPacketByteLongDataSlot I)
            (bytesStoreSetPacketByteLongStoredWord σ I)) I) ⟨1⟩ = ⟨0⟩)
    (hvalidPost : UInt256.sub (UInt256.land
        (bytesStorePacketLengthHeaderWord
          (sstoreAccountMap I.codeOwner σ (bytesStoreSetPacketByteLongDataSlot I)
            (bytesStoreSetPacketByteLongStoredWord σ I)) I) ⟨1⟩)
        (UInt256.lt (UInt256.land (UInt256.div
          (bytesStorePacketLengthHeaderWord
            (sstoreAccountMap I.codeOwner σ (bytesStoreSetPacketByteLongDataSlot I)
              (bytesStoreSetPacketByteLongStoredWord σ I)) I) ⟨2⟩) ⟨127⟩) ⟨32⟩) ≠
          ⟨0⟩)
    (hperm : I.perm = true) :
    ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨709⟩
      [lenPost, bytesStoreSetByteIndexWord I, ⟨2⟩, ⟨0⟩,
        bytesStoreSetByteValueWord I, bytesStoreSetByteIndexWord I, ⟨301⟩,
        bytesStoreSelWord I]
      (wordAt0Mem (⟨2⟩ : UInt256) solcFreePtrMem) (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ (bytesStoreSetPacketByteLongDataSlot I)
        (bytesStoreSetPacketByteLongStoredWord σ I)) k C := by
  let σ' := sstoreAccountMap I.codeOwner σ (bytesStoreSetPacketByteLongDataSlot I)
    (bytesStoreSetPacketByteLongStoredWord σ I)
  let header' : UInt256 :=
    Option.option ⟨0⟩ (fun ac => Batteries.RBMap.findD ac.storage ⟨2⟩ ⟨0⟩)
      (Batteries.RBMap.find? σ' I.codeOwner)
  have hdec := bytesStoreX_setPacketByteLongWriteReturnReachLengthDecoder
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (I := I) (g := g) (len := len) hreach hbound hflag hperm
  have hheader : header' = bytesStorePacketLengthHeaderWord σ' I := by
    rfl
  have hdecoded := bytesStoreX_bytesLengthDecoderShortValidMemCarried
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (τ := σ') (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (header := header') (ret := ⟨709⟩)
    (rest := [bytesStoreSetByteIndexWord I, ⟨2⟩, ⟨0⟩,
      bytesStoreSetByteValueWord I, bytesStoreSetByteIndexWord I, ⟨301⟩,
      bytesStoreSelWord I])
    (mem := wordAt0Mem (⟨2⟩ : UInt256) solcFreePtrMem)
    (aw := UInt256.ofNat 3) (rdata := ByteArray.empty)
    (by simpa [header', σ'] using hdec)
    (by simpa [hheader, σ'] using hflagPost)
    (by simpa [hheader, σ'] using hvalidPost)
    (by native_decide)
    (by simp)
  simpa [σ', header', hheader, hlenPost] using hdecoded

theorem bytesStoreX_setPacketByteLongWriteReturnLongMalformed
    {cA gh bl σ σ₀ A I} {g : Sat256} {len : UInt256}
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨622⟩
      [len, bytesStoreSetByteIndexWord I, ⟨2⟩,
        UInt256.shiftLeft (bytesStoreSetByteValueWord I) ⟨248⟩, ⟨0⟩,
        bytesStoreSetByteValueWord I, bytesStoreSetByteIndexWord I, ⟨301⟩,
        bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hbound : (bytesStoreSetByteIndexWord I).toNat < len.toNat)
    (hflag : UInt256.land (bytesStorePacketLengthHeaderWord σ I) ⟨1⟩ ≠ ⟨0⟩)
    (hflagPost : UInt256.land
        (bytesStorePacketLengthHeaderWord
          (sstoreAccountMap I.codeOwner σ (bytesStoreSetPacketByteLongDataSlot I)
            (bytesStoreSetPacketByteLongStoredWord σ I)) I) ⟨1⟩ ≠ ⟨0⟩)
    (hbadPost : UInt256.sub (UInt256.land
        (bytesStorePacketLengthHeaderWord
          (sstoreAccountMap I.codeOwner σ (bytesStoreSetPacketByteLongDataSlot I)
            (bytesStoreSetPacketByteLongStoredWord σ I)) I) ⟨1⟩)
        (UInt256.lt (UInt256.div
          (bytesStorePacketLengthHeaderWord
            (sstoreAccountMap I.codeOwner σ (bytesStoreSetPacketByteLongDataSlot I)
              (bytesStoreSetPacketByteLongStoredWord σ I)) I) ⟨2⟩) ⟨32⟩) = ⟨0⟩)
    (hperm : I.perm = true) :
    RDrev bytesStoreBytecode g (initState cA gh bl σ σ₀ g A I) := by
  let σ' := sstoreAccountMap I.codeOwner σ (bytesStoreSetPacketByteLongDataSlot I)
    (bytesStoreSetPacketByteLongStoredWord σ I)
  let header' : UInt256 :=
    Option.option ⟨0⟩ (fun ac => Batteries.RBMap.findD ac.storage ⟨2⟩ ⟨0⟩)
      (Batteries.RBMap.find? σ' I.codeOwner)
  have hdec := bytesStoreX_setPacketByteLongWriteReturnReachLengthDecoder
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (I := I) (g := g) (len := len) hreach hbound hflag hperm
  have hheader : header' = bytesStorePacketLengthHeaderWord σ' I := by
    rfl
  exact bytesStoreX_bytesLengthDecoderLongMalformedMemCarried
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σ') (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (header := header') (ret := ⟨709⟩)
    (rest := [bytesStoreSetByteIndexWord I, ⟨2⟩, ⟨0⟩,
      bytesStoreSetByteValueWord I, bytesStoreSetByteIndexWord I, ⟨301⟩,
      bytesStoreSelWord I])
    (mem := wordAt0Mem (⟨2⟩ : UInt256) solcFreePtrMem)
    (by simpa [header', σ'] using hdec)
    (by simpa [hheader, σ'] using hflagPost)
    (by simpa [hheader, σ'] using hbadPost)
    (by simp)

theorem bytesStoreX_setPacketByteLongWriteReturnShortMalformed
    {cA gh bl σ σ₀ A I} {g : Sat256} {len : UInt256}
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨622⟩
      [len, bytesStoreSetByteIndexWord I, ⟨2⟩,
        UInt256.shiftLeft (bytesStoreSetByteValueWord I) ⟨248⟩, ⟨0⟩,
        bytesStoreSetByteValueWord I, bytesStoreSetByteIndexWord I, ⟨301⟩,
        bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hbound : (bytesStoreSetByteIndexWord I).toNat < len.toNat)
    (hflag : UInt256.land (bytesStorePacketLengthHeaderWord σ I) ⟨1⟩ ≠ ⟨0⟩)
    (hflagPost : UInt256.land
        (bytesStorePacketLengthHeaderWord
          (sstoreAccountMap I.codeOwner σ (bytesStoreSetPacketByteLongDataSlot I)
            (bytesStoreSetPacketByteLongStoredWord σ I)) I) ⟨1⟩ = ⟨0⟩)
    (hbadPost : UInt256.sub (UInt256.land
        (bytesStorePacketLengthHeaderWord
          (sstoreAccountMap I.codeOwner σ (bytesStoreSetPacketByteLongDataSlot I)
            (bytesStoreSetPacketByteLongStoredWord σ I)) I) ⟨1⟩)
        (UInt256.lt (UInt256.land (UInt256.div
          (bytesStorePacketLengthHeaderWord
            (sstoreAccountMap I.codeOwner σ (bytesStoreSetPacketByteLongDataSlot I)
              (bytesStoreSetPacketByteLongStoredWord σ I)) I) ⟨2⟩) ⟨127⟩) ⟨32⟩) =
          ⟨0⟩)
    (hperm : I.perm = true) :
    RDrev bytesStoreBytecode g (initState cA gh bl σ σ₀ g A I) := by
  let σ' := sstoreAccountMap I.codeOwner σ (bytesStoreSetPacketByteLongDataSlot I)
    (bytesStoreSetPacketByteLongStoredWord σ I)
  let header' : UInt256 :=
    Option.option ⟨0⟩ (fun ac => Batteries.RBMap.findD ac.storage ⟨2⟩ ⟨0⟩)
      (Batteries.RBMap.find? σ' I.codeOwner)
  have hdec := bytesStoreX_setPacketByteLongWriteReturnReachLengthDecoder
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (I := I) (g := g) (len := len) hreach hbound hflag hperm
  have hheader : header' = bytesStorePacketLengthHeaderWord σ' I := by
    rfl
  exact bytesStoreX_bytesLengthDecoderShortMalformedMemCarried
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σ') (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (header := header') (ret := ⟨709⟩)
    (rest := [bytesStoreSetByteIndexWord I, ⟨2⟩, ⟨0⟩,
      bytesStoreSetByteValueWord I, bytesStoreSetByteIndexWord I, ⟨301⟩,
      bytesStoreSelWord I])
    (mem := wordAt0Mem (⟨2⟩ : UInt256) solcFreePtrMem)
    (by simpa [header', σ'] using hdec)
    (by simpa [hheader, σ'] using hflagPost)
    (by simpa [hheader, σ'] using hbadPost)
    (by simp)

theorem bytesStoreX_setPacketByteLongReadReturnToWrapper
    {cA gh bl σinit τ σ₀ A I} {g : Sat256} {len header dataWord : UInt256}
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨709⟩
      [len, bytesStoreSetByteIndexWord I, ⟨2⟩, ⟨0⟩,
        bytesStoreSetByteValueWord I, bytesStoreSetByteIndexWord I, ⟨301⟩,
        bytesStoreSelWord I]
      (wordAt0Mem (⟨2⟩ : UInt256) solcFreePtrMem) (UInt256.ofNat 3)
      ByteArray.empty (cA, τ) k C)
    (hbound : (bytesStoreSetByteIndexWord I).toNat < len.toNat)
    (hheader :
      ((τ.find? I.codeOwner).option ⟨0⟩
        (fun acc => acc.storage.findD ⟨2⟩ ⟨0⟩)) = header)
    (hflag : UInt256.land header ⟨1⟩ ≠ ⟨0⟩)
    (hdata :
      ((τ.find? I.codeOwner).option ⟨0⟩
        (fun acc => acc.storage.findD (bytesStoreSetPacketByteLongDataSlot I) ⟨0⟩)) =
          dataWord)
    (hbyte :
      UInt256.shiftRight
        (UInt256.mul (UInt256.byteAt (bytesStoreSetPacketByteLongWordIndex I) dataWord)
          (UInt256.shiftLeft ⟨1⟩ ⟨248⟩))
        ⟨248⟩ = bytesStoreSetByteValueWord I) :
    ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨301⟩
      [bytesStoreSetByteValueWord I, bytesStoreSelWord I]
      (wordAt0Mem (⟨2⟩ : UInt256)
        (wordAt0Mem (⟨2⟩ : UInt256) solcFreePtrMem))
      (UInt256.ofNat 3) ByteArray.empty (cA, τ) k C := by
  obtain ⟨_, _, rd709⟩ := hreach
  have hlt : UInt256.lt (bytesStoreSetByteIndexWord I) len = ⟨1⟩ :=
    ult_one hbound
  have hflagOne : UInt256.land header ⟨1⟩ = ⟨1⟩ :=
    u256_land_one_eq_one_of_ne_zero hflag
  have hslot := bytesStoreSetPacketByteLongBaseHashMem
    (wordAt0Mem (⟨2⟩ : UInt256) solcFreePtrMem)
  have rd723 := evm_run rd709 with [
    jumpdest, dup2, lt, push2 ⟨723⟩,
    jumpiT (by rw [hlt]; decide) (by native_decide)]
  have rd725 := evm_run rd723 with [jumpdest, dup2]
  obtain ⟨_, _, rd726₀⟩ := rd725.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd726⟩ :
      ∃ k C, RD bytesStoreBytecode I g
        (initState cA gh bl σinit σ₀ g A I) ⟨726⟩
        [header, bytesStoreSetByteIndexWord I, ⟨2⟩, ⟨0⟩,
          bytesStoreSetByteValueWord I, bytesStoreSetByteIndexWord I, ⟨301⟩,
          bytesStoreSelWord I]
        (wordAt0Mem (⟨2⟩ : UInt256) solcFreePtrMem) (UInt256.ofNat 3)
        ByteArray.empty (cA, τ) k C := by
    exact ⟨_, _, by simpa [initState, hheader] using rd726₀⟩
  have rd751 := evm_run rd726 with [
    push1 ⟨1⟩, and, iszero, push2 ⟨752⟩,
    jumpiNT (by
      rw [u256_land_comm, hflagOne]
      decide),
    swap1, push0,
    raw mstore 0
      (wordAt0Mem (⟨2⟩ : UInt256)
        (wordAt0Mem (⟨2⟩ : UInt256) solcFreePtrMem))
      (UInt256.ofNat 3) (by native_decide)
      mem_cost
      (by rfl)
      (by native_decide) (by evm_ov),
    push1 ⟨32⟩, push0,
    raw keccak256 0 (bytesLikeDataBase ⟨2⟩) (UInt256.ofNat 3)
      (by native_decide) mem_cost hslot (by native_decide) (by evm_ov),
    swap1, push1 ⟨32⟩, swap2, dup3, dup3, div, add, swap2, swap1]
  have rd752raw := RD.mod rd751 (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨_, _, rd752⟩ :
      ∃ k C, RD bytesStoreBytecode I g
        (initState cA gh bl σinit σ₀ g A I) ⟨752⟩
        [bytesStoreSetPacketByteLongWordIndex I,
          bytesStoreSetPacketByteLongDataSlot I, ⟨0⟩,
          bytesStoreSetByteValueWord I, bytesStoreSetByteIndexWord I, ⟨301⟩,
          bytesStoreSelWord I]
        (wordAt0Mem (⟨2⟩ : UInt256)
          (wordAt0Mem (⟨2⟩ : UInt256) solcFreePtrMem))
        (UInt256.ofNat 3) ByteArray.empty (cA, τ) k C := by
    exact ⟨_, _, by
      simpa [bytesStoreSetPacketByteLongWordIndex,
        bytesStoreSetPacketByteLongDataSlot,
        u256_add_comm (UInt256.div (bytesStoreSetByteIndexWord I) ⟨32⟩)
          (bytesLikeDataBase ⟨2⟩)] using rd752raw⟩
  have rd754 := evm_run rd752 with [jumpdest, swap1]
  obtain ⟨_, _, rd755₀⟩ := rd754.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd755⟩ :
      ∃ k C, RD bytesStoreBytecode I g
        (initState cA gh bl σinit σ₀ g A I) ⟨755⟩
        [dataWord, bytesStoreSetPacketByteLongWordIndex I, ⟨0⟩,
          bytesStoreSetByteValueWord I, bytesStoreSetByteIndexWord I, ⟨301⟩,
          bytesStoreSelWord I]
        (wordAt0Mem (⟨2⟩ : UInt256)
          (wordAt0Mem (⟨2⟩ : UInt256) solcFreePtrMem))
        (UInt256.ofNat 3) ByteArray.empty (cA, τ) k C := by
    exact ⟨_, _, by simpa [initState, hdata] using rd755₀⟩
  have rd761 := evm_run rd755 with [
    push1 ⟨1⟩, push1 ⟨248⟩, shl, swap2]
  have rd762 := RD.byte rd761 (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd301 := evm_run rd762 with [
    mul, push1 ⟨248⟩, shr,
    swap4, swap3, pop, pop, pop, jump (by native_decide)]
  exact ⟨_, _, by simpa [hbyte] using rd301⟩

theorem bytesStoreX_setPacketByteShortWriteReturnReachLengthDecoder
    {cA gh bl σ σ₀ A I} {g : Sat256} {len : UInt256}
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨622⟩
      [len, bytesStoreSetByteIndexWord I, ⟨2⟩,
        UInt256.shiftLeft (bytesStoreSetByteValueWord I) ⟨248⟩, ⟨0⟩,
        bytesStoreSetByteValueWord I, bytesStoreSetByteIndexWord I, ⟨301⟩,
        bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hbound : (bytesStoreSetByteIndexWord I).toNat < len.toNat)
    (hflag : UInt256.land (bytesStorePacketLengthHeaderWord σ I) ⟨1⟩ = ⟨0⟩)
    (hperm : I.perm = true) :
    ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2246⟩
      [Option.option ⟨0⟩ (fun ac => Batteries.RBMap.findD ac.storage ⟨2⟩ ⟨0⟩)
          (Batteries.RBMap.find?
            (sstoreAccountMap I.codeOwner σ ⟨2⟩
              (bytesStoreSetPacketByteShortStoredWord σ I)) I.codeOwner),
        ⟨709⟩, bytesStoreSetByteIndexWord I, ⟨2⟩, ⟨0⟩,
        bytesStoreSetByteValueWord I, bytesStoreSetByteIndexWord I, ⟨301⟩,
        bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ ⟨2⟩
        (bytesStoreSetPacketByteShortStoredWord σ I)) k C := by
  have h665 := bytesStoreX_setPacketByteShortReachStoreCommon
    (g := g) hreach hbound hflag
  have h694 := bytesStoreX_setPacketByteShortStorePacket
    (g := g) h665 hperm
  exact bytesStoreX_setPacketByteReturnReachLengthDecoder
    (σinit := σ)
    (σ := sstoreAccountMap I.codeOwner σ ⟨2⟩
      (bytesStoreSetPacketByteShortStoredWord σ I))
    h694

theorem bytesStoreX_setPacketByteShortWriteReturnDecodedLength
    {cA gh bl σ σ₀ A I} {g : Sat256} {len : UInt256} {acc : Account}
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨622⟩
      [len, bytesStoreSetByteIndexWord I, ⟨2⟩,
        UInt256.shiftLeft (bytesStoreSetByteValueWord I) ⟨248⟩, ⟨0⟩,
        bytesStoreSetByteValueWord I, bytesStoreSetByteIndexWord I, ⟨301⟩,
        bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hlen : len =
      UInt256.land (UInt256.div (bytesStorePacketLengthHeaderWord σ I) ⟨2⟩) ⟨127⟩)
    (hshort : len.toNat < 32)
    (hbound : (bytesStoreSetByteIndexWord I).toNat < len.toNat)
    (hflag : UInt256.land (bytesStorePacketLengthHeaderWord σ I) ⟨1⟩ = ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (bytesStorePacketLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStorePacketLengthHeaderWord σ I) ⟨2⟩) ⟨127⟩)
          ⟨32⟩) ≠ ⟨0⟩)
    (hperm : I.perm = true)
    (hacc : σ.find? I.codeOwner = some acc) :
    ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨709⟩
      [len, bytesStoreSetByteIndexWord I, ⟨2⟩, ⟨0⟩,
        bytesStoreSetByteValueWord I, bytesStoreSetByteIndexWord I, ⟨301⟩,
        bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ ⟨2⟩
        (bytesStoreSetPacketByteShortStoredWord σ I)) k C := by
  let σ' := sstoreAccountMap I.codeOwner σ ⟨2⟩
    (bytesStoreSetPacketByteShortStoredWord σ I)
  let header' : UInt256 :=
    Option.option ⟨0⟩ (fun ac => Batteries.RBMap.findD ac.storage ⟨2⟩ ⟨0⟩)
      (Batteries.RBMap.find? σ' I.codeOwner)
  have hdec := bytesStoreX_setPacketByteShortWriteReturnReachLengthDecoder
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (I := I) (g := g) (len := len) hreach hbound hflag hperm
  have hnz := bytesStoreSetPacketByteShortStoredWord_beq_zero_false
    (σ := σ) (I := I) (len := len) hlen hshort hbound
  have hheader : header' = bytesStoreSetPacketByteShortStoredWord σ I := by
    simpa [header', σ'] using
      bytesStoreSetPacketByteShortStoredWord_load_self (σ := σ) (I := I) (acc := acc)
        hacc hnz
  have hflag' : UInt256.land header' ⟨1⟩ = ⟨0⟩ := by
    rw [hheader, bytesStoreSetPacketByteShortStoredWord_flag_eq
      (σ := σ) (I := I) (len := len) hshort hbound, hflag]
  have hvalid' : UInt256.sub (UInt256.land header' ⟨1⟩)
      (UInt256.lt (UInt256.land (UInt256.div header' ⟨2⟩) ⟨127⟩) ⟨32⟩) ≠
        ⟨0⟩ := by
    rw [hheader, bytesStoreSetPacketByteShortStoredWord_flag_eq
      (σ := σ) (I := I) (len := len) hshort hbound,
      bytesStoreSetPacketByteShortStoredWord_shortLen_eq
        (σ := σ) (I := I) (len := len) hshort hbound]
    exact hvalid
  have hdecoded := bytesStoreX_bytesLengthDecoderShortValidMemCarried
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (τ := σ') (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (header := header') (ret := ⟨709⟩)
    (rest := [bytesStoreSetByteIndexWord I, ⟨2⟩, ⟨0⟩,
      bytesStoreSetByteValueWord I, bytesStoreSetByteIndexWord I, ⟨301⟩,
      bytesStoreSelWord I])
    (mem := solcFreePtrMem) (aw := UInt256.ofNat 3) (rdata := ByteArray.empty)
    (by simpa [header', σ'] using hdec) hflag' hvalid' (by native_decide)
    (by simp)
  have hlen' :
      UInt256.land (UInt256.div (bytesStoreSetPacketByteShortStoredWord σ I) ⟨2⟩) ⟨127⟩ =
        len := by
    rw [bytesStoreSetPacketByteShortStoredWord_shortLen_eq
      (σ := σ) (I := I) (len := len) hshort hbound, ← hlen]
  simpa [σ', header', hheader, hlen'] using hdecoded

theorem bytesStoreX_setPacketByteShortReadReturnToWrapper
    {cA gh bl σinit τ σ₀ A I} {g : Sat256} {len header : UInt256} {mem : ByteArray}
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨709⟩
      [len, bytesStoreSetByteIndexWord I, ⟨2⟩, ⟨0⟩,
        bytesStoreSetByteValueWord I, bytesStoreSetByteIndexWord I, ⟨301⟩,
        bytesStoreSelWord I]
      mem (UInt256.ofNat 3) ByteArray.empty (cA, τ) k C)
    (hbound : (bytesStoreSetByteIndexWord I).toNat < len.toNat)
    (hheader :
      ((τ.find? I.codeOwner).option ⟨0⟩
        (fun acc => acc.storage.findD ⟨2⟩ ⟨0⟩)) = header)
    (hflag : UInt256.land header ⟨1⟩ = ⟨0⟩)
    (hbyte :
      UInt256.shiftRight
        (UInt256.mul (UInt256.byteAt (bytesStoreSetByteIndexWord I) header)
          (UInt256.shiftLeft ⟨1⟩ ⟨248⟩))
        ⟨248⟩ = bytesStoreSetByteValueWord I) :
    ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨301⟩
      [bytesStoreSetByteValueWord I, bytesStoreSelWord I]
      mem (UInt256.ofNat 3) ByteArray.empty (cA, τ) k C := by
  obtain ⟨_, _, rd709⟩ := hreach
  have hlt : UInt256.lt (bytesStoreSetByteIndexWord I) len = ⟨1⟩ :=
    ult_one hbound
  have rd723 := evm_run rd709 with [
    jumpdest, dup2, lt, push2 ⟨723⟩,
    jumpiT (by rw [hlt]; decide) (by native_decide)]
  have rd725 := evm_run rd723 with [jumpdest, dup2]
  obtain ⟨_, _, rd726₀⟩ := rd725.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd726⟩ :
      ∃ k C, RD bytesStoreBytecode I g
        (initState cA gh bl σinit σ₀ g A I) ⟨726⟩
        [header, bytesStoreSetByteIndexWord I, ⟨2⟩, ⟨0⟩,
          bytesStoreSetByteValueWord I, bytesStoreSetByteIndexWord I, ⟨301⟩,
          bytesStoreSelWord I]
        mem (UInt256.ofNat 3) ByteArray.empty (cA, τ) k C := by
    exact ⟨_, _, by simpa [initState, hheader] using rd726₀⟩
  have rd752 := evm_run rd726 with [
    push1 ⟨1⟩, and, iszero, push2 ⟨752⟩,
    jumpiT (by
      rw [u256_land_comm, hflag]
      decide)
      (by native_decide)]
  have rd771 := evm_run rd752 with [
    jumpdest, swap1]
  obtain ⟨_, _, rd755₀⟩ := rd771.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd755⟩ :
      ∃ k C, RD bytesStoreBytecode I g
        (initState cA gh bl σinit σ₀ g A I) ⟨755⟩
        [header, bytesStoreSetByteIndexWord I, ⟨0⟩,
          bytesStoreSetByteValueWord I, bytesStoreSetByteIndexWord I, ⟨301⟩,
          bytesStoreSelWord I]
        mem (UInt256.ofNat 3) ByteArray.empty (cA, τ) k C := by
    exact ⟨_, _, by simpa [initState, hheader] using rd755₀⟩
  have rd761 := evm_run rd755 with [
    push1 ⟨1⟩, push1 ⟨248⟩, shl, swap2]
  have rd762 := RD.byte rd761 (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd301 := evm_run rd762 with [
    mul, push1 ⟨248⟩, shr,
    swap4, swap3, pop, pop, pop, jump (by native_decide)]
  exact ⟨_, _, by simpa [hbyte] using rd301⟩

theorem bytesStoreX_setPacketByteShortSuccessReturn
    {cA gh bl σ σ₀ A I} {g : Sat256} {len : UInt256} {acc : Account}
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨601⟩
      [bytesStoreSetByteValueWord I, bytesStoreSetByteIndexWord I, ⟨301⟩,
        bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hcanon : (bytesStoreSetByteValueWord I).toNat < EVM.twoPow 8)
    (hlen : len =
      UInt256.land (UInt256.div (bytesStorePacketLengthHeaderWord σ I) ⟨2⟩) ⟨127⟩)
    (hshort : len.toNat < 32)
    (hbound : (bytesStoreSetByteIndexWord I).toNat < len.toNat)
    (hflag : UInt256.land (bytesStorePacketLengthHeaderWord σ I) ⟨1⟩ = ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (bytesStorePacketLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStorePacketLengthHeaderWord σ I) ⟨2⟩) ⟨127⟩)
          ⟨32⟩) ≠ ⟨0⟩)
    (hperm : I.perm = true)
    (hacc : σ.find? I.codeOwner = some acc) :
    RDret bytesStoreBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, sstoreAccountMap I.codeOwner σ ⟨2⟩
        (bytesStoreSetPacketByteShortStoredWord σ I))
      (UInt256.toByteArray (bytesStoreSetByteValueWord I)) := by
  let σ' := sstoreAccountMap I.codeOwner σ ⟨2⟩
    (bytesStoreSetPacketByteShortStoredWord σ I)
  let header' : UInt256 :=
    Option.option ⟨0⟩ (fun ac => Batteries.RBMap.findD ac.storage ⟨2⟩ ⟨0⟩)
      (Batteries.RBMap.find? σ' I.codeOwner)
  have hdec := bytesStoreX_setPacketByteReachLengthDecoder (g := g) hreach
  have h622 := bytesStoreX_bytesLengthDecoderShortValidMem
    (A := A) (I := I) (g := g) hdec hflag hvalid (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have hread := bytesStoreX_setPacketByteShortWriteReturnDecodedLength
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (I := I) (g := g) (len := len) (acc := acc) (by simpa [hlen] using h622)
    hlen hshort hbound
    hflag hvalid hperm hacc
  have hnz := bytesStoreSetPacketByteShortStoredWord_beq_zero_false
    (σ := σ) (I := I) (len := len) hlen hshort hbound
  have hheader : header' = bytesStoreSetPacketByteShortStoredWord σ I := by
    simpa [header', σ'] using
      bytesStoreSetPacketByteShortStoredWord_load_self (σ := σ) (I := I) (acc := acc)
        hacc hnz
  have hflag' : UInt256.land header' ⟨1⟩ = ⟨0⟩ := by
    rw [hheader, bytesStoreSetPacketByteShortStoredWord_flag_eq
      (σ := σ) (I := I) (len := len) hshort hbound, hflag]
  have hbyteAt :
      UInt256.byteAt (bytesStoreSetByteIndexWord I) header' =
        bytesStoreSetByteValueWord I := by
    rw [hheader]
    exact bytesStoreSetPacketByteShortStoredWord_byteAt
      (σ := σ) (I := I) (len := len) hcanon hshort hbound
  have hbyte :
      UInt256.shiftRight
        (UInt256.mul (UInt256.byteAt (bytesStoreSetByteIndexWord I) header')
          (UInt256.shiftLeft ⟨1⟩ ⟨248⟩))
        ⟨248⟩ = bytesStoreSetByteValueWord I := by
    rw [hbyteAt]
    exact bytesStoreSetByteValueHighMulShiftRight hcanon
  have h301 := bytesStoreX_setPacketByteShortReadReturnToWrapper
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (τ := σ') (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (len := len) (header := header') hread hbound
    (by rfl) hflag' hbyte
  have hret := bytesStoreX_returnUInt8_301
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σ') (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (val := bytesStoreSetByteValueWord I) h301
  simpa [σ', bytesStoreSetPacketByteLand255_eq_self_of_uint8 hcanon] using hret

theorem bytesStoreX_setPacketByteLongShortSuccessReturn
    {cA gh bl σ σ₀ A I} {g : Sat256} {len lenPost : UInt256} {acc : Account}
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨622⟩
      [len, bytesStoreSetByteIndexWord I, ⟨2⟩,
        UInt256.shiftLeft (bytesStoreSetByteValueWord I) ⟨248⟩, ⟨0⟩,
        bytesStoreSetByteValueWord I, bytesStoreSetByteIndexWord I, ⟨301⟩,
        bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hcanon : (bytesStoreSetByteValueWord I).toNat < EVM.twoPow 8)
    (hlenPost : lenPost = UInt256.land (UInt256.div
      (bytesStorePacketLengthHeaderWord
        (sstoreAccountMap I.codeOwner σ (bytesStoreSetPacketByteLongDataSlot I)
          (bytesStoreSetPacketByteLongStoredWord σ I)) I) ⟨2⟩) ⟨127⟩)
    (hflagPost : UInt256.land
        (bytesStorePacketLengthHeaderWord
          (sstoreAccountMap I.codeOwner σ (bytesStoreSetPacketByteLongDataSlot I)
            (bytesStoreSetPacketByteLongStoredWord σ I)) I) ⟨1⟩ = ⟨0⟩)
    (hvalidPost : UInt256.sub (UInt256.land
        (bytesStorePacketLengthHeaderWord
          (sstoreAccountMap I.codeOwner σ (bytesStoreSetPacketByteLongDataSlot I)
            (bytesStoreSetPacketByteLongStoredWord σ I)) I) ⟨1⟩)
        (UInt256.lt (UInt256.land (UInt256.div
          (bytesStorePacketLengthHeaderWord
            (sstoreAccountMap I.codeOwner σ (bytesStoreSetPacketByteLongDataSlot I)
              (bytesStoreSetPacketByteLongStoredWord σ I)) I) ⟨2⟩) ⟨127⟩) ⟨32⟩) ≠
          ⟨0⟩)
    (hbound : (bytesStoreSetByteIndexWord I).toNat < len.toNat)
    (hboundPost : (bytesStoreSetByteIndexWord I).toNat < lenPost.toNat)
    (hflag : UInt256.land (bytesStorePacketLengthHeaderWord σ I) ⟨1⟩ ≠ ⟨0⟩)
    (hperm : I.perm = true)
    (hacc : σ.find? I.codeOwner = some acc) :
    RDret bytesStoreBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, sstoreAccountMap I.codeOwner σ (bytesStoreSetPacketByteLongDataSlot I)
        (bytesStoreSetPacketByteLongStoredWord σ I))
      (UInt256.toByteArray (bytesStoreSetByteValueWord I)) := by
  let σ' := sstoreAccountMap I.codeOwner σ (bytesStoreSetPacketByteLongDataSlot I)
    (bytesStoreSetPacketByteLongStoredWord σ I)
  let header' : UInt256 :=
    Option.option ⟨0⟩ (fun ac => Batteries.RBMap.findD ac.storage ⟨2⟩ ⟨0⟩)
      (Batteries.RBMap.find? σ' I.codeOwner)
  have hread := bytesStoreX_setPacketByteLongWriteReturnDecodedPostShortLength
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (I := I) (g := g) (len := len) (lenPost := lenPost)
    hreach hbound hflag hlenPost hflagPost hvalidPost hperm
  have hheader : header' = bytesStorePacketLengthHeaderWord σ' I := by
    rfl
  have hvalid0 :
      UInt256.sub ⟨0⟩ (UInt256.lt lenPost ⟨32⟩) ≠ ⟨0⟩ := by
    simpa [hlenPost, hflagPost, σ'] using hvalidPost
  have hshortPost : lenPost.toNat < 32 :=
    solidityShortBytesValid_lt32 hvalid0
  have hidxLt32 : (bytesStoreSetByteIndexWord I).toNat < 32 :=
    lt_trans hboundPost hshortPost
  have hbyteAt :
      UInt256.byteAt (bytesStoreSetByteIndexWord I) header' =
        bytesStoreSetByteValueWord I := by
    by_cases hEq : ⟨2⟩ = bytesStoreSetPacketByteLongDataSlot I
    · have hheaderStored :
          header' = bytesStoreSetPacketByteLongStoredWord σ I := by
        simpa [header', σ', bytesStorePacketLengthHeaderWord, hEq] using
          sstoreAccountMap_storage_findD_self_of_find_some_any σ I.codeOwner acc
            (bytesStoreSetPacketByteLongDataSlot I)
            (bytesStoreSetPacketByteLongStoredWord σ I) hacc
      rw [hheaderStored]
      exact bytesStoreSetPacketByteLongStoredWord_byteAt_index_of_lt32
        (σ := σ) (I := I) hcanon hidxLt32
    · have hheaderOld : header' = bytesStorePacketLengthHeaderWord σ I := by
        simpa [header', σ', bytesStorePacketLengthHeaderWord,
          bytesStoreSetPacketByteLongDataSlot] using
          bytesStoreBytesHeaderWordAfterDataSstore_eq_of_before_of_ne
            (σ := σ) (I := I) (baseSlot := ⟨2⟩)
            (idx := bytesStoreSetByteIndexWord I)
            (val := bytesStoreSetPacketByteLongStoredWord σ I) hEq (by rfl)
      have hflagOldZero :
          UInt256.land (bytesStorePacketLengthHeaderWord σ I) ⟨1⟩ = ⟨0⟩ := by
        rw [← hheaderOld]
        simpa [hheader, σ'] using hflagPost
      exact False.elim (hflag hflagOldZero)
  have hbyte :
      UInt256.shiftRight
        (UInt256.mul (UInt256.byteAt (bytesStoreSetByteIndexWord I) header')
          (UInt256.shiftLeft ⟨1⟩ ⟨248⟩))
        ⟨248⟩ = bytesStoreSetByteValueWord I := by
    rw [hbyteAt]
    exact bytesStoreSetByteValueHighMulShiftRight hcanon
  have h301 := bytesStoreX_setPacketByteShortReadReturnToWrapper
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (τ := σ') (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (len := lenPost) (header := header')
    hread hboundPost (by rfl) (by simpa [hheader, σ'] using hflagPost) hbyte
  have hret := bytesStoreX_returnUInt8_301OfMem
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σ') (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (val := bytesStoreSetByteValueWord I)
    (mem := wordAt0Mem (⟨2⟩ : UInt256) solcFreePtrMem)
    (wordAt0Mem_size_96 _ solcFreePtrMem_size)
    (bytesStoreWordAt0Mem_read64 _ solcFreePtrMem_size solcFreePtrMem_read64)
    h301
  simpa [σ', bytesStoreSetPacketByteLand255_eq_self_of_uint8 hcanon] using hret

theorem bytesStoreX_setPacketByteLongLongSuccessReturn
    {cA gh bl σ σ₀ A I} {g : Sat256} {len lenPost : UInt256} {acc : Account}
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨601⟩
      [bytesStoreSetByteValueWord I, bytesStoreSetByteIndexWord I, ⟨301⟩,
        bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hcanon : (bytesStoreSetByteValueWord I).toNat < EVM.twoPow 8)
    (hlen : len = UInt256.div (bytesStorePacketLengthHeaderWord σ I) ⟨2⟩)
    (hlenPost : lenPost = UInt256.div
      (bytesStorePacketLengthHeaderWord
        (sstoreAccountMap I.codeOwner σ (bytesStoreSetPacketByteLongDataSlot I)
          (bytesStoreSetPacketByteLongStoredWord σ I)) I) ⟨2⟩)
    (hflagPost : UInt256.land
        (bytesStorePacketLengthHeaderWord
          (sstoreAccountMap I.codeOwner σ (bytesStoreSetPacketByteLongDataSlot I)
            (bytesStoreSetPacketByteLongStoredWord σ I)) I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalidPost : UInt256.sub (UInt256.land
        (bytesStorePacketLengthHeaderWord
          (sstoreAccountMap I.codeOwner σ (bytesStoreSetPacketByteLongDataSlot I)
            (bytesStoreSetPacketByteLongStoredWord σ I)) I) ⟨1⟩)
        (UInt256.lt (UInt256.div
          (bytesStorePacketLengthHeaderWord
            (sstoreAccountMap I.codeOwner σ (bytesStoreSetPacketByteLongDataSlot I)
              (bytesStoreSetPacketByteLongStoredWord σ I)) I) ⟨2⟩) ⟨32⟩) ≠ ⟨0⟩)
    (hbound : (bytesStoreSetByteIndexWord I).toNat < len.toNat)
    (hboundPost : (bytesStoreSetByteIndexWord I).toNat < lenPost.toNat)
    (hflag : UInt256.land (bytesStorePacketLengthHeaderWord σ I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (bytesStorePacketLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStorePacketLengthHeaderWord σ I) ⟨2⟩) ⟨32⟩) ≠ ⟨0⟩)
    (hperm : I.perm = true)
    (hacc : σ.find? I.codeOwner = some acc) :
    RDret bytesStoreBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, sstoreAccountMap I.codeOwner σ (bytesStoreSetPacketByteLongDataSlot I)
        (bytesStoreSetPacketByteLongStoredWord σ I))
      (UInt256.toByteArray (bytesStoreSetByteValueWord I)) := by
  let σ' := sstoreAccountMap I.codeOwner σ (bytesStoreSetPacketByteLongDataSlot I)
    (bytesStoreSetPacketByteLongStoredWord σ I)
  let header' : UInt256 :=
    Option.option ⟨0⟩ (fun ac => Batteries.RBMap.findD ac.storage ⟨2⟩ ⟨0⟩)
      (Batteries.RBMap.find? σ' I.codeOwner)
  let dataWord' : UInt256 :=
    Option.option ⟨0⟩
      (fun ac => Batteries.RBMap.findD ac.storage (bytesStoreSetPacketByteLongDataSlot I)
        ⟨0⟩)
      (Batteries.RBMap.find? σ' I.codeOwner)
  have hdec := bytesStoreX_setPacketByteReachLengthDecoder (g := g) hreach
  have h622 := bytesStoreX_bytesLengthDecoderLongValidMem
    (A := A) (I := I) (g := g) hdec hflag hvalid (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have hread := bytesStoreX_setPacketByteLongWriteReturnDecodedPostLongLength
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (I := I) (g := g) (len := len) (lenPost := lenPost)
    (by simpa [hlen] using h622)
    hbound hflag hlenPost hflagPost hvalidPost hperm
  have hheader : header' = bytesStorePacketLengthHeaderWord σ' I := by
    rfl
  have hdata : dataWord' = bytesStoreSetPacketByteLongStoredWord σ I := by
    simpa [dataWord', σ'] using
      sstoreAccountMap_storage_findD_self_of_find_some_any σ I.codeOwner acc
        (bytesStoreSetPacketByteLongDataSlot I)
        (bytesStoreSetPacketByteLongStoredWord σ I) hacc
  have hbyteAt :
      UInt256.byteAt (bytesStoreSetPacketByteLongWordIndex I) dataWord' =
        bytesStoreSetByteValueWord I := by
    rw [hdata]
    exact bytesStoreSetPacketByteLongStoredWord_byteAt
      (σ := σ) (I := I) hcanon
  have hbyte :
      UInt256.shiftRight
        (UInt256.mul (UInt256.byteAt (bytesStoreSetPacketByteLongWordIndex I) dataWord')
          (UInt256.shiftLeft ⟨1⟩ ⟨248⟩))
        ⟨248⟩ = bytesStoreSetByteValueWord I := by
    rw [hbyteAt]
    exact bytesStoreSetByteValueHighMulShiftRight hcanon
  have h301 := bytesStoreX_setPacketByteLongReadReturnToWrapper
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (τ := σ') (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (len := lenPost) (header := header')
    (dataWord := dataWord') hread hboundPost (by rfl)
    (by simpa [hheader, σ'] using hflagPost) (by rfl) hbyte
  have hret := bytesStoreX_returnUInt8_301OfMem
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σ') (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (val := bytesStoreSetByteValueWord I)
    (mem := wordAt0Mem (⟨2⟩ : UInt256)
      (wordAt0Mem (⟨2⟩ : UInt256) solcFreePtrMem))
    (wordAt0Mem_size_96 _ (wordAt0Mem_size_96 _ solcFreePtrMem_size))
    (bytesStoreWordAt0Mem_read64 _
      (wordAt0Mem_size_96 _ solcFreePtrMem_size)
      (bytesStoreWordAt0Mem_read64 _ solcFreePtrMem_size solcFreePtrMem_read64))
    h301
  simpa [σ', bytesStoreSetPacketByteLand255_eq_self_of_uint8 hcanon] using hret

theorem bytesStoreSetPacketByteShortSuccessRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256} {len : UInt256} {accEvm : Account}
    (hcode : I.code = bytesStoreBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x0a, 0xb2, 0x59, 0x00]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (haccEvm : σ_evm.find? I.codeOwner = some accEvm)
    (hsz68 : 68 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (bytesStoreSetByteValueWord I).toNat < EVM.twoPow 8)
    (hlen : len =
      UInt256.land (UInt256.div (bytesStorePacketLengthHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩)
    (hshort : len.toNat < 32)
    (hbound : (bytesStoreSetByteIndexWord I).toNat < len.toNat)
    (hflag : UInt256.land (bytesStorePacketLengthHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (bytesStorePacketLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStorePacketLengthHeaderWord σ_evm I) ⟨2⟩)
            ⟨127⟩)
          ⟨32⟩) ≠ ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreConfig bytesStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsz := bytesStoreSetPacketByteSelector_size hsel
  have hreach := bytesStoreReachSetPacketByte (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz hsize hsel
  have hreachPc : ∃ k C, RD bytesStoreBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨282⟩
      [bytesStoreSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ_evm) k C := by
    simpa [bytesStoreSetPacketByteEntryPc] using hreach
  have hreachBody := bytesStoreX_setPacketByteDecodeValid
    (g := Sat256.ofUInt256 g) hreachPc hsz68 hhi hsize
    (bytesStoreSetPacketByteLand255_eq_self_of_uint8 hcanon)
  have hd := bytesStoreDispatch_setPacketByte (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec := bytesStoreDecode_setPacketByte_locals (I := I) hsz68 hhi hcanon
  have hret := bytesStoreX_setPacketByteShortSuccessReturn
    (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
    (I := I) (g := Sat256.ofUInt256 g) (len := len) (acc := accEvm)
    hreachBody hcanon hlen hshort hbound hflag hvalid hperm haccEvm
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmSolm1 := Solm.EVM.storageStore evmSolm0 evmSolm0.executionEnv.codeOwner ⟨2⟩
    (bytesStoreSetPacketByteShortStoredWord σ_evm I)
  have hload :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner ⟨2⟩ =
        bytesStorePacketLengthHeaderWord σ_evm I := by
    simpa [evmSolm0] using
      bytesStoreStorageLoadPacketLength_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  obtain ⟨accSolm, haccSolm⟩ :=
    accountMapEquiv_find?_some_exists hAccounts haccEvm
  have hbody :
      ExecTransitionBody bytesStoreConfig bytesStoreContract evmSolm0
        (bytesStoreSetPacketByteLocals I) setPacketByteTransition.body
        (.returned
          (bytesStoreSetPacketByteFrame I)
          evmSolm1 (some (bytesStoreSetPacketByteValue I))) := by
    simpa [evmSolm0, evmSolm1, initState, bytesStoreSetPacketByteFrame] using
      bytesStoreSetPacketByteShortBodyReturns
        (evm := evmSolm0) (σ := σ_evm) (I := I) (len := len) (acc := accSolm)
        (by simp [evmSolm0, initState]; exact hwv)
        hload
        (by simpa [evmSolm0, initState] using haccSolm)
        hcanon hlen hshort hbound hflag hvalid
  have hpostAccounts :
      accountMapEquiv
        (sstoreAccountMap I.codeOwner σ_evm ⟨2⟩
          (bytesStoreSetPacketByteShortStoredWord σ_evm I))
        evmSolm1.accountMap := by
    simpa [evmSolm1, evmSolm0] using
      bytesStoreAccountMapEquiv_storageStore_initState
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
        (⟨2⟩ : UInt256) (bytesStoreSetPacketByteShortStoredWord σ_evm I)
  exact hret.reEquivExecutionGenAccountMapEquiv hcode hd hdec hbody
    (by simp [evmSolm1, evmSolm0, initState, storageStore_createdAccounts])
    hpostAccounts
    (returnEquiv_of_encode (uint8ReturnEncoding (bytesStoreSetByteValueWord I) hcanon))

theorem bytesStoreSetPacketByteLongReturnLongSuccessRuntime
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {len lenPost : UInt256}
    {accEvm : Account}
    (hcode : I.code = bytesStoreBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x0a, 0xb2, 0x59, 0x00]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (haccEvm : σ_evm.find? I.codeOwner = some accEvm)
    (hsz68 : 68 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (bytesStoreSetByteValueWord I).toNat < EVM.twoPow 8)
    (hlenPost : lenPost = UInt256.div
      (bytesStorePacketLengthHeaderWord
        (sstoreAccountMap I.codeOwner σ_evm (bytesStoreSetPacketByteLongDataSlot I)
          (bytesStoreSetPacketByteLongStoredWord σ_evm I)) I) ⟨2⟩)
    (hflagPost : UInt256.land
        (bytesStorePacketLengthHeaderWord
          (sstoreAccountMap I.codeOwner σ_evm (bytesStoreSetPacketByteLongDataSlot I)
            (bytesStoreSetPacketByteLongStoredWord σ_evm I)) I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalidPost : UInt256.sub (UInt256.land
        (bytesStorePacketLengthHeaderWord
          (sstoreAccountMap I.codeOwner σ_evm (bytesStoreSetPacketByteLongDataSlot I)
            (bytesStoreSetPacketByteLongStoredWord σ_evm I)) I) ⟨1⟩)
        (UInt256.lt (UInt256.div
          (bytesStorePacketLengthHeaderWord
            (sstoreAccountMap I.codeOwner σ_evm (bytesStoreSetPacketByteLongDataSlot I)
              (bytesStoreSetPacketByteLongStoredWord σ_evm I)) I) ⟨2⟩) ⟨32⟩) ≠ ⟨0⟩)
    (hlen : len = UInt256.div (bytesStorePacketLengthHeaderWord σ_evm I) ⟨2⟩)
    (hbound : (bytesStoreSetByteIndexWord I).toNat < len.toNat)
    (hboundPost : (bytesStoreSetByteIndexWord I).toNat < lenPost.toNat)
    (hflag : UInt256.land (bytesStorePacketLengthHeaderWord σ_evm I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (bytesStorePacketLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStorePacketLengthHeaderWord σ_evm I) ⟨2⟩) ⟨32⟩) ≠
      ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreConfig bytesStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsz := bytesStoreSetPacketByteSelector_size hsel
  have hreach := bytesStoreReachSetPacketByte (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz hsize hsel
  have hreachPc : ∃ k C, RD bytesStoreBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨282⟩
      [bytesStoreSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ_evm) k C := by
    simpa [bytesStoreSetPacketByteEntryPc] using hreach
  have hreachBody := bytesStoreX_setPacketByteDecodeValid
    (g := Sat256.ofUInt256 g) hreachPc hsz68 hhi hsize
    (bytesStoreSetPacketByteLand255_eq_self_of_uint8 hcanon)
  have hret := bytesStoreX_setPacketByteLongLongSuccessReturn
    (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
    (I := I) (g := Sat256.ofUInt256 g) (len := len) (lenPost := lenPost)
    (acc := accEvm)
    hreachBody hcanon hlen hlenPost hflagPost hvalidPost hbound hboundPost hflag hvalid
    hperm haccEvm
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmSolm1 := Solm.EVM.storageStore evmSolm0 evmSolm0.executionEnv.codeOwner
    (bytesStoreSetPacketByteLongDataSlot I)
    (bytesStoreSetPacketByteLongStoredWord σ_evm I)
  have hloadHeader :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner ⟨2⟩ =
        bytesStorePacketLengthHeaderWord σ_evm I := by
    simpa [evmSolm0] using
      bytesStoreStorageLoadPacketLength_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hloadData :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner
          (bytesStoreSetPacketByteLongDataSlot I) =
        bytesStoreSetPacketByteLongOldWord σ_evm I := by
    simpa [evmSolm0] using
      bytesStoreStorageLoadSetPacketByteLongData_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  obtain ⟨accSolm, haccSolm⟩ :=
    accountMapEquiv_find?_some_exists hAccounts haccEvm
  have hpostAccounts :
      accountMapEquiv
        (sstoreAccountMap I.codeOwner σ_evm (bytesStoreSetPacketByteLongDataSlot I)
          (bytesStoreSetPacketByteLongStoredWord σ_evm I))
        evmSolm1.accountMap := by
    simpa [evmSolm1, evmSolm0] using
      bytesStoreAccountMapEquiv_storageStore_initState
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
        (bytesStoreSetPacketByteLongDataSlot I)
        (bytesStoreSetPacketByteLongStoredWord σ_evm I)
  have hloadHeaderPost :
      Solm.EVM.storageLoad
          (Solm.EVM.storageStore evmSolm0 evmSolm0.executionEnv.codeOwner
            (bytesStoreSetPacketByteLongDataSlot I)
            (bytesStoreSetPacketByteLongStoredWord σ_evm I))
          evmSolm0.executionEnv.codeOwner ⟨2⟩ =
        bytesStorePacketLengthHeaderWord
          (sstoreAccountMap I.codeOwner σ_evm (bytesStoreSetPacketByteLongDataSlot I)
            (bytesStoreSetPacketByteLongStoredWord σ_evm I)) I := by
    have howner : evmSolm1.executionEnv.codeOwner = I.codeOwner := by
      simp [evmSolm1, evmSolm0, initState, storageStore_executionEnv]
    simpa [evmSolm1, storageStore_executionEnv] using
      bytesStoreStorageLoadPacketLength_of_accountMapEquiv
        (evm := evmSolm1)
        (σ := sstoreAccountMap I.codeOwner σ_evm (bytesStoreSetPacketByteLongDataSlot I)
          (bytesStoreSetPacketByteLongStoredWord σ_evm I))
        (I := I) howner hpostAccounts
  have hbody :
      ExecTransitionBody bytesStoreConfig bytesStoreContract evmSolm0
        (bytesStoreSetPacketByteLocals I) setPacketByteTransition.body
        (.returned
          (bytesStoreSetPacketByteFrame I)
          evmSolm1 (some (bytesStoreSetPacketByteValue I))) := by
    simpa [evmSolm0, evmSolm1, initState, bytesStoreSetPacketByteFrame] using
      bytesStoreSetPacketByteLongBodyReturnsOfPostLongReadback
        (evm := evmSolm0) (σ := σ_evm) (I := I)
        (len := len) (lenPost := lenPost)
        (postHeaderWord := bytesStorePacketLengthHeaderWord
          (sstoreAccountMap I.codeOwner σ_evm (bytesStoreSetPacketByteLongDataSlot I)
            (bytesStoreSetPacketByteLongStoredWord σ_evm I)) I)
        (acc := accSolm)
        (by simp [evmSolm0, initState]; exact hwv)
        hloadHeader hloadData hloadHeaderPost
        (by simpa [evmSolm0, initState] using haccSolm)
        hcanon hlen hlenPost hbound hboundPost hflag hvalid hflagPost hvalidPost
  have hd := bytesStoreDispatch_setPacketByte (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec := bytesStoreDecode_setPacketByte_locals (I := I) hsz68 hhi hcanon
  exact hret.reEquivExecutionGenAccountMapEquiv hcode hd hdec hbody
    (by simp [evmSolm1, evmSolm0, initState, storageStore_createdAccounts])
    hpostAccounts
    (returnEquiv_of_encode (uint8ReturnEncoding (bytesStoreSetByteValueWord I) hcanon))

theorem bytesStoreSetPacketByteLongReturnShortSuccessRuntime
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {len lenPost : UInt256}
    {accEvm : Account}
    (hcode : I.code = bytesStoreBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x0a, 0xb2, 0x59, 0x00]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (haccEvm : σ_evm.find? I.codeOwner = some accEvm)
    (hsz68 : 68 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (bytesStoreSetByteValueWord I).toNat < EVM.twoPow 8)
    (hlenPost : lenPost = UInt256.land (UInt256.div
      (bytesStorePacketLengthHeaderWord
        (sstoreAccountMap I.codeOwner σ_evm (bytesStoreSetPacketByteLongDataSlot I)
          (bytesStoreSetPacketByteLongStoredWord σ_evm I)) I) ⟨2⟩) ⟨127⟩)
    (hflagPost : UInt256.land
        (bytesStorePacketLengthHeaderWord
          (sstoreAccountMap I.codeOwner σ_evm (bytesStoreSetPacketByteLongDataSlot I)
            (bytesStoreSetPacketByteLongStoredWord σ_evm I)) I) ⟨1⟩ = ⟨0⟩)
    (hvalidPost : UInt256.sub (UInt256.land
        (bytesStorePacketLengthHeaderWord
          (sstoreAccountMap I.codeOwner σ_evm (bytesStoreSetPacketByteLongDataSlot I)
            (bytesStoreSetPacketByteLongStoredWord σ_evm I)) I) ⟨1⟩)
        (UInt256.lt (UInt256.land (UInt256.div
          (bytesStorePacketLengthHeaderWord
            (sstoreAccountMap I.codeOwner σ_evm (bytesStoreSetPacketByteLongDataSlot I)
              (bytesStoreSetPacketByteLongStoredWord σ_evm I)) I) ⟨2⟩) ⟨127⟩) ⟨32⟩) ≠
          ⟨0⟩)
    (hlen : len = UInt256.div (bytesStorePacketLengthHeaderWord σ_evm I) ⟨2⟩)
    (hbound : (bytesStoreSetByteIndexWord I).toNat < len.toNat)
    (hboundPost : (bytesStoreSetByteIndexWord I).toNat < lenPost.toNat)
    (hflag : UInt256.land (bytesStorePacketLengthHeaderWord σ_evm I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (bytesStorePacketLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStorePacketLengthHeaderWord σ_evm I) ⟨2⟩) ⟨32⟩) ≠
      ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreConfig bytesStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsz := bytesStoreSetPacketByteSelector_size hsel
  have hreach := bytesStoreReachSetPacketByte (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz hsize hsel
  have hreachPc : ∃ k C, RD bytesStoreBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨282⟩
      [bytesStoreSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ_evm) k C := by
    simpa [bytesStoreSetPacketByteEntryPc] using hreach
  have hreachBody := bytesStoreX_setPacketByteDecodeValid
    (g := Sat256.ofUInt256 g) hreachPc hsz68 hhi hsize
    (bytesStoreSetPacketByteLand255_eq_self_of_uint8 hcanon)
  have hdecLen := bytesStoreX_setPacketByteReachLengthDecoder
    (g := Sat256.ofUInt256 g) hreachBody
  have h622Raw := bytesStoreX_bytesLengthDecoderLongValidMem
    (A := A) (I := I) (g := Sat256.ofUInt256 g) hdecLen hflag hvalid
    (by native_decide) (by simp only [List.length_cons, List.length_nil]; omega)
  have h622 :
      ∃ k C, RD bytesStoreBytecode I (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨622⟩
        [len, bytesStoreSetByteIndexWord I, ⟨2⟩,
          UInt256.shiftLeft (bytesStoreSetByteValueWord I) ⟨248⟩, ⟨0⟩,
          bytesStoreSetByteValueWord I, bytesStoreSetByteIndexWord I, ⟨301⟩,
          bytesStoreSelWord I]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C := by
    simpa [hlen] using h622Raw
  have hret := bytesStoreX_setPacketByteLongShortSuccessReturn
    (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
    (I := I) (g := Sat256.ofUInt256 g) (len := len) (lenPost := lenPost)
    (acc := accEvm)
    h622 hcanon hlenPost hflagPost hvalidPost hbound hboundPost hflag hperm haccEvm
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmSolm1 := Solm.EVM.storageStore evmSolm0 evmSolm0.executionEnv.codeOwner
    (bytesStoreSetPacketByteLongDataSlot I)
    (bytesStoreSetPacketByteLongStoredWord σ_evm I)
  have hloadHeader :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner ⟨2⟩ =
        bytesStorePacketLengthHeaderWord σ_evm I := by
    simpa [evmSolm0] using
      bytesStoreStorageLoadPacketLength_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hloadData :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner
          (bytesStoreSetPacketByteLongDataSlot I) =
        bytesStoreSetPacketByteLongOldWord σ_evm I := by
    simpa [evmSolm0] using
      bytesStoreStorageLoadSetPacketByteLongData_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hpostAccounts :
      accountMapEquiv
        (sstoreAccountMap I.codeOwner σ_evm (bytesStoreSetPacketByteLongDataSlot I)
          (bytesStoreSetPacketByteLongStoredWord σ_evm I))
        evmSolm1.accountMap := by
    simpa [evmSolm1, evmSolm0] using
      bytesStoreAccountMapEquiv_storageStore_initState
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
        (bytesStoreSetPacketByteLongDataSlot I)
        (bytesStoreSetPacketByteLongStoredWord σ_evm I)
  have hloadHeaderPost :
      Solm.EVM.storageLoad
          (Solm.EVM.storageStore evmSolm0 evmSolm0.executionEnv.codeOwner
            (bytesStoreSetPacketByteLongDataSlot I)
            (bytesStoreSetPacketByteLongStoredWord σ_evm I))
          evmSolm0.executionEnv.codeOwner ⟨2⟩ =
        bytesStorePacketLengthHeaderWord
          (sstoreAccountMap I.codeOwner σ_evm (bytesStoreSetPacketByteLongDataSlot I)
            (bytesStoreSetPacketByteLongStoredWord σ_evm I)) I := by
    have howner : evmSolm1.executionEnv.codeOwner = I.codeOwner := by
      simp [evmSolm1, evmSolm0, initState, storageStore_executionEnv]
    simpa [evmSolm1, storageStore_executionEnv] using
      bytesStoreStorageLoadPacketLength_of_accountMapEquiv
        (evm := evmSolm1)
        (σ := sstoreAccountMap I.codeOwner σ_evm (bytesStoreSetPacketByteLongDataSlot I)
          (bytesStoreSetPacketByteLongStoredWord σ_evm I))
        (I := I) howner hpostAccounts
  have hvalid0 :
      UInt256.sub ⟨0⟩ (UInt256.lt lenPost ⟨32⟩) ≠ ⟨0⟩ := by
    simpa [hlenPost, hflagPost] using hvalidPost
  have hshortPost : lenPost.toNat < 32 :=
    solidityShortBytesValid_lt32 hvalid0
  have hidxLt32 : (bytesStoreSetByteIndexWord I).toNat < 32 :=
    lt_trans hboundPost hshortPost
  have hbytePost :
      UInt256.byteAt (bytesStoreSetByteIndexWord I)
        (bytesStorePacketLengthHeaderWord
          (sstoreAccountMap I.codeOwner σ_evm (bytesStoreSetPacketByteLongDataSlot I)
            (bytesStoreSetPacketByteLongStoredWord σ_evm I)) I) =
        bytesStoreSetByteValueWord I := by
    by_cases hEq : ⟨2⟩ = bytesStoreSetPacketByteLongDataSlot I
    · have hheaderPostStored :
          bytesStorePacketLengthHeaderWord
              (sstoreAccountMap I.codeOwner σ_evm (bytesStoreSetPacketByteLongDataSlot I)
                (bytesStoreSetPacketByteLongStoredWord σ_evm I)) I =
            bytesStoreSetPacketByteLongStoredWord σ_evm I := by
        simpa [bytesStorePacketLengthHeaderWord, hEq] using
          sstoreAccountMap_storage_findD_self_of_find_some_any σ_evm I.codeOwner accEvm
            (bytesStoreSetPacketByteLongDataSlot I)
            (bytesStoreSetPacketByteLongStoredWord σ_evm I) haccEvm
      rw [hheaderPostStored]
      exact bytesStoreSetPacketByteLongStoredWord_byteAt_index_of_lt32
        (σ := σ_evm) (I := I) hcanon hidxLt32
    · have hheaderOld :
          bytesStorePacketLengthHeaderWord
              (sstoreAccountMap I.codeOwner σ_evm (bytesStoreSetPacketByteLongDataSlot I)
                (bytesStoreSetPacketByteLongStoredWord σ_evm I)) I =
            bytesStorePacketLengthHeaderWord σ_evm I := by
        simpa [bytesStorePacketLengthHeaderWord,
          bytesStoreSetPacketByteLongDataSlot] using
          bytesStoreBytesHeaderWordAfterDataSstore_eq_of_before_of_ne
            (σ := σ_evm) (I := I) (baseSlot := ⟨2⟩)
            (idx := bytesStoreSetByteIndexWord I)
            (val := bytesStoreSetPacketByteLongStoredWord σ_evm I) hEq (by rfl)
      have hflagOldZero :
          UInt256.land (bytesStorePacketLengthHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩ := by
        rw [← hheaderOld]
        exact hflagPost
      exact False.elim (hflag hflagOldZero)
  have hbody :
      ExecTransitionBody bytesStoreConfig bytesStoreContract evmSolm0
        (bytesStoreSetPacketByteLocals I) setPacketByteTransition.body
        (.returned
          (bytesStoreSetPacketByteFrame I)
          evmSolm1 (some (bytesStoreSetPacketByteValue I))) := by
    simpa [evmSolm0, evmSolm1, initState, bytesStoreSetPacketByteFrame] using
      bytesStoreSetPacketByteLongBodyReturnsOfPostShortReadback
        (evm := evmSolm0) (σ := σ_evm) (I := I)
        (len := len) (lenPost := lenPost)
        (postHeaderWord := bytesStorePacketLengthHeaderWord
          (sstoreAccountMap I.codeOwner σ_evm (bytesStoreSetPacketByteLongDataSlot I)
            (bytesStoreSetPacketByteLongStoredWord σ_evm I)) I)
        (by simp [evmSolm0, initState]; exact hwv)
        hloadHeader hloadData hloadHeaderPost
        hcanon hlen hlenPost hbound hboundPost hflag hvalid hflagPost hvalidPost
        hbytePost
  have hd := bytesStoreDispatch_setPacketByte (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec := bytesStoreDecode_setPacketByte_locals (I := I) hsz68 hhi hcanon
  exact hret.reEquivExecutionGenAccountMapEquiv hcode hd hdec hbody
    (by simp [evmSolm1, evmSolm0, initState, storageStore_createdAccounts])
    hpostAccounts
    (returnEquiv_of_encode (uint8ReturnEncoding (bytesStoreSetByteValueWord I) hcanon))

theorem bytesStoreSetPacketByteLongReturnShortOobLengthRuntime
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {len lenPost : UInt256}
    (hcode : I.code = bytesStoreBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x0a, 0xb2, 0x59, 0x00]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsz68 : 68 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (bytesStoreSetByteValueWord I).toNat < EVM.twoPow 8)
    (hlenPost : lenPost = UInt256.land (UInt256.div
      (bytesStorePacketLengthHeaderWord
        (sstoreAccountMap I.codeOwner σ_evm (bytesStoreSetPacketByteLongDataSlot I)
          (bytesStoreSetPacketByteLongStoredWord σ_evm I)) I) ⟨2⟩) ⟨127⟩)
    (hflagPost : UInt256.land
        (bytesStorePacketLengthHeaderWord
          (sstoreAccountMap I.codeOwner σ_evm (bytesStoreSetPacketByteLongDataSlot I)
            (bytesStoreSetPacketByteLongStoredWord σ_evm I)) I) ⟨1⟩ = ⟨0⟩)
    (hvalidPost : UInt256.sub (UInt256.land
        (bytesStorePacketLengthHeaderWord
          (sstoreAccountMap I.codeOwner σ_evm (bytesStoreSetPacketByteLongDataSlot I)
            (bytesStoreSetPacketByteLongStoredWord σ_evm I)) I) ⟨1⟩)
        (UInt256.lt (UInt256.land (UInt256.div
          (bytesStorePacketLengthHeaderWord
            (sstoreAccountMap I.codeOwner σ_evm (bytesStoreSetPacketByteLongDataSlot I)
              (bytesStoreSetPacketByteLongStoredWord σ_evm I)) I) ⟨2⟩) ⟨127⟩) ⟨32⟩) ≠
          ⟨0⟩)
    (hlen : len = UInt256.div (bytesStorePacketLengthHeaderWord σ_evm I) ⟨2⟩)
    (hbound : (bytesStoreSetByteIndexWord I).toNat < len.toNat)
    (hboundPost : ¬ (bytesStoreSetByteIndexWord I).toNat < lenPost.toNat)
    (hflag : UInt256.land (bytesStorePacketLengthHeaderWord σ_evm I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (bytesStorePacketLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStorePacketLengthHeaderWord σ_evm I) ⟨2⟩) ⟨32⟩) ≠
      ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreConfig bytesStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsz := bytesStoreSetPacketByteSelector_size hsel
  have hreach := bytesStoreReachSetPacketByte (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz hsize hsel
  have hreachPc : ∃ k C, RD bytesStoreBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨282⟩
      [bytesStoreSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ_evm) k C := by
    simpa [bytesStoreSetPacketByteEntryPc] using hreach
  have hreachBody := bytesStoreX_setPacketByteDecodeValid
    (g := Sat256.ofUInt256 g) hreachPc hsz68 hhi hsize
    (bytesStoreSetPacketByteLand255_eq_self_of_uint8 hcanon)
  have hdecLen := bytesStoreX_setPacketByteReachLengthDecoder
    (g := Sat256.ofUInt256 g) hreachBody
  have h622Raw := bytesStoreX_bytesLengthDecoderLongValidMem
    (A := A) (I := I) (g := Sat256.ofUInt256 g) hdecLen hflag hvalid
    (by native_decide) (by simp only [List.length_cons, List.length_nil]; omega)
  have h622 :
      ∃ k C, RD bytesStoreBytecode I (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨622⟩
        [len, bytesStoreSetByteIndexWord I, ⟨2⟩,
          UInt256.shiftLeft (bytesStoreSetByteValueWord I) ⟨248⟩, ⟨0⟩,
          bytesStoreSetByteValueWord I, bytesStoreSetByteIndexWord I, ⟨301⟩,
          bytesStoreSelWord I]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C := by
    simpa [hlen] using h622Raw
  have hread := bytesStoreX_setPacketByteLongWriteReturnDecodedPostShortLength
    (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
    (I := I) (g := Sat256.ofUInt256 g) (len := len) (lenPost := lenPost)
    h622 hbound hflag hlenPost hflagPost hvalidPost hperm
  have hrev := bytesStoreX_setPacketByteReturnOobLength
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ_evm)
    (σ := sstoreAccountMap I.codeOwner σ_evm (bytesStoreSetPacketByteLongDataSlot I)
      (bytesStoreSetPacketByteLongStoredWord σ_evm I))
    (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g) (len := lenPost)
    hread hboundPost
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmSolm1 := Solm.EVM.storageStore evmSolm0 evmSolm0.executionEnv.codeOwner
    (bytesStoreSetPacketByteLongDataSlot I)
    (bytesStoreSetPacketByteLongStoredWord σ_evm I)
  have hloadHeader :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner ⟨2⟩ =
        bytesStorePacketLengthHeaderWord σ_evm I := by
    simpa [evmSolm0] using
      bytesStoreStorageLoadPacketLength_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hloadData :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner
          (bytesStoreSetPacketByteLongDataSlot I) =
        bytesStoreSetPacketByteLongOldWord σ_evm I := by
    simpa [evmSolm0] using
      bytesStoreStorageLoadSetPacketByteLongData_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hpostAccounts :
      accountMapEquiv
        (sstoreAccountMap I.codeOwner σ_evm (bytesStoreSetPacketByteLongDataSlot I)
          (bytesStoreSetPacketByteLongStoredWord σ_evm I))
        evmSolm1.accountMap := by
    simpa [evmSolm1, evmSolm0] using
      bytesStoreAccountMapEquiv_storageStore_initState
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
        (bytesStoreSetPacketByteLongDataSlot I)
        (bytesStoreSetPacketByteLongStoredWord σ_evm I)
  have hloadHeaderPost :
      Solm.EVM.storageLoad
          (Solm.EVM.storageStore evmSolm0 evmSolm0.executionEnv.codeOwner
            (bytesStoreSetPacketByteLongDataSlot I)
            (bytesStoreSetPacketByteLongStoredWord σ_evm I))
          evmSolm0.executionEnv.codeOwner ⟨2⟩ =
        bytesStorePacketLengthHeaderWord
          (sstoreAccountMap I.codeOwner σ_evm (bytesStoreSetPacketByteLongDataSlot I)
            (bytesStoreSetPacketByteLongStoredWord σ_evm I)) I := by
    have howner : evmSolm1.executionEnv.codeOwner = I.codeOwner := by
      simp [evmSolm1, evmSolm0, initState, storageStore_executionEnv]
    simpa [evmSolm1, storageStore_executionEnv] using
      bytesStoreStorageLoadPacketLength_of_accountMapEquiv
        (evm := evmSolm1)
        (σ := sstoreAccountMap I.codeOwner σ_evm (bytesStoreSetPacketByteLongDataSlot I)
          (bytesStoreSetPacketByteLongStoredWord σ_evm I))
        (I := I) howner hpostAccounts
  have hbody :
      ExecTransitionBody bytesStoreConfig bytesStoreContract evmSolm0
        (bytesStoreSetPacketByteLocals I) setPacketByteTransition.body .reverted := by
    simpa [evmSolm0, evmSolm1, initState] using
      bytesStoreSetPacketByteLongBodyReturnRevertsOfPostShortLength
        (evm := evmSolm0) (σ := σ_evm) (I := I)
        (len := len) (lenPost := lenPost)
        (postHeaderWord := bytesStorePacketLengthHeaderWord
          (sstoreAccountMap I.codeOwner σ_evm (bytesStoreSetPacketByteLongDataSlot I)
            (bytesStoreSetPacketByteLongStoredWord σ_evm I)) I)
        (by simp [evmSolm0, initState]; exact hwv)
        hloadHeader hloadData hloadHeaderPost hcanon hlen hlenPost hbound hboundPost
        hflag hvalid hflagPost hvalidPost
  have hd := bytesStoreDispatch_setPacketByte (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec := bytesStoreDecode_setPacketByte_locals (I := I) hsz68 hhi hcanon
  exact hrev.reEquivExecutionRevert hcode hd hdec hbody

theorem bytesStoreSetPacketByteLongReturnLongOobLengthRuntime
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {len lenPost : UInt256}
    {accEvm : Account}
    (hcode : I.code = bytesStoreBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x0a, 0xb2, 0x59, 0x00]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (haccEvm : σ_evm.find? I.codeOwner = some accEvm)
    (hsz68 : 68 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (bytesStoreSetByteValueWord I).toNat < EVM.twoPow 8)
    (hlenPost : lenPost = UInt256.div
      (bytesStorePacketLengthHeaderWord
        (sstoreAccountMap I.codeOwner σ_evm (bytesStoreSetPacketByteLongDataSlot I)
          (bytesStoreSetPacketByteLongStoredWord σ_evm I)) I) ⟨2⟩)
    (hflagPost : UInt256.land
        (bytesStorePacketLengthHeaderWord
          (sstoreAccountMap I.codeOwner σ_evm (bytesStoreSetPacketByteLongDataSlot I)
            (bytesStoreSetPacketByteLongStoredWord σ_evm I)) I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalidPost : UInt256.sub (UInt256.land
        (bytesStorePacketLengthHeaderWord
          (sstoreAccountMap I.codeOwner σ_evm (bytesStoreSetPacketByteLongDataSlot I)
            (bytesStoreSetPacketByteLongStoredWord σ_evm I)) I) ⟨1⟩)
        (UInt256.lt (UInt256.div
          (bytesStorePacketLengthHeaderWord
            (sstoreAccountMap I.codeOwner σ_evm (bytesStoreSetPacketByteLongDataSlot I)
              (bytesStoreSetPacketByteLongStoredWord σ_evm I)) I) ⟨2⟩) ⟨32⟩) ≠ ⟨0⟩)
    (hlen : len = UInt256.div (bytesStorePacketLengthHeaderWord σ_evm I) ⟨2⟩)
    (hbound : (bytesStoreSetByteIndexWord I).toNat < len.toNat)
    (hboundPost : ¬ (bytesStoreSetByteIndexWord I).toNat < lenPost.toNat)
    (hflag : UInt256.land (bytesStorePacketLengthHeaderWord σ_evm I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (bytesStorePacketLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStorePacketLengthHeaderWord σ_evm I) ⟨2⟩) ⟨32⟩) ≠
      ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreConfig bytesStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsz := bytesStoreSetPacketByteSelector_size hsel
  have hreach := bytesStoreReachSetPacketByte (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz hsize hsel
  have hreachPc : ∃ k C, RD bytesStoreBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨282⟩
      [bytesStoreSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ_evm) k C := by
    simpa [bytesStoreSetPacketByteEntryPc] using hreach
  have hreachBody := bytesStoreX_setPacketByteDecodeValid
    (g := Sat256.ofUInt256 g) hreachPc hsz68 hhi hsize
    (bytesStoreSetPacketByteLand255_eq_self_of_uint8 hcanon)
  have hdecLen := bytesStoreX_setPacketByteReachLengthDecoder
    (g := Sat256.ofUInt256 g) hreachBody
  have h622Raw := bytesStoreX_bytesLengthDecoderLongValidMem
    (A := A) (I := I) (g := Sat256.ofUInt256 g) hdecLen hflag hvalid
    (by native_decide) (by simp only [List.length_cons, List.length_nil]; omega)
  have h622 :
      ∃ k C, RD bytesStoreBytecode I (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨622⟩
        [len, bytesStoreSetByteIndexWord I, ⟨2⟩,
          UInt256.shiftLeft (bytesStoreSetByteValueWord I) ⟨248⟩, ⟨0⟩,
          bytesStoreSetByteValueWord I, bytesStoreSetByteIndexWord I, ⟨301⟩,
          bytesStoreSelWord I]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C := by
    simpa [hlen] using h622Raw
  have hread := bytesStoreX_setPacketByteLongWriteReturnDecodedPostLongLength
    (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
    (I := I) (g := Sat256.ofUInt256 g) (len := len) (lenPost := lenPost)
    h622 hbound hflag hlenPost hflagPost hvalidPost hperm
  have hrev := bytesStoreX_setPacketByteReturnOobLength
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ_evm)
    (σ := sstoreAccountMap I.codeOwner σ_evm (bytesStoreSetPacketByteLongDataSlot I)
      (bytesStoreSetPacketByteLongStoredWord σ_evm I))
    (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g) (len := lenPost)
    hread hboundPost
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmSolm1 := Solm.EVM.storageStore evmSolm0 evmSolm0.executionEnv.codeOwner
    (bytesStoreSetPacketByteLongDataSlot I)
    (bytesStoreSetPacketByteLongStoredWord σ_evm I)
  have hloadHeader :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner ⟨2⟩ =
        bytesStorePacketLengthHeaderWord σ_evm I := by
    simpa [evmSolm0] using
      bytesStoreStorageLoadPacketLength_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hloadData :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner
          (bytesStoreSetPacketByteLongDataSlot I) =
        bytesStoreSetPacketByteLongOldWord σ_evm I := by
    simpa [evmSolm0] using
      bytesStoreStorageLoadSetPacketByteLongData_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  obtain ⟨accSolm, haccSolm⟩ :=
    accountMapEquiv_find?_some_exists hAccounts haccEvm
  have hpostAccounts :
      accountMapEquiv
        (sstoreAccountMap I.codeOwner σ_evm (bytesStoreSetPacketByteLongDataSlot I)
          (bytesStoreSetPacketByteLongStoredWord σ_evm I))
        evmSolm1.accountMap := by
    simpa [evmSolm1, evmSolm0] using
      bytesStoreAccountMapEquiv_storageStore_initState
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
        (bytesStoreSetPacketByteLongDataSlot I)
        (bytesStoreSetPacketByteLongStoredWord σ_evm I)
  have hloadHeaderPost :
      Solm.EVM.storageLoad
          (Solm.EVM.storageStore evmSolm0 evmSolm0.executionEnv.codeOwner
            (bytesStoreSetPacketByteLongDataSlot I)
            (bytesStoreSetPacketByteLongStoredWord σ_evm I))
          evmSolm0.executionEnv.codeOwner ⟨2⟩ =
        bytesStorePacketLengthHeaderWord
          (sstoreAccountMap I.codeOwner σ_evm (bytesStoreSetPacketByteLongDataSlot I)
            (bytesStoreSetPacketByteLongStoredWord σ_evm I)) I := by
    have howner : evmSolm1.executionEnv.codeOwner = I.codeOwner := by
      simp [evmSolm1, evmSolm0, initState, storageStore_executionEnv]
    simpa [evmSolm1, storageStore_executionEnv] using
      bytesStoreStorageLoadPacketLength_of_accountMapEquiv
        (evm := evmSolm1)
        (σ := sstoreAccountMap I.codeOwner σ_evm (bytesStoreSetPacketByteLongDataSlot I)
          (bytesStoreSetPacketByteLongStoredWord σ_evm I))
        (I := I) howner hpostAccounts
  have hbody :
      ExecTransitionBody bytesStoreConfig bytesStoreContract evmSolm0
        (bytesStoreSetPacketByteLocals I) setPacketByteTransition.body .reverted := by
    simpa [evmSolm0, evmSolm1, initState, bytesStoreSetPacketByteFrame] using
      bytesStoreSetPacketByteLongBodyReturnRevertsOfPostLongLength
        (evm := evmSolm0) (σ := σ_evm) (I := I)
        (len := len) (lenPost := lenPost)
        (postHeaderWord := bytesStorePacketLengthHeaderWord
          (sstoreAccountMap I.codeOwner σ_evm (bytesStoreSetPacketByteLongDataSlot I)
            (bytesStoreSetPacketByteLongStoredWord σ_evm I)) I)
        (acc := accSolm)
        (by simp [evmSolm0, initState]; exact hwv)
        hloadHeader hloadData hloadHeaderPost
        (by simpa [evmSolm0, initState] using haccSolm)
        hcanon hlen hlenPost hbound hboundPost hflag hvalid hflagPost hvalidPost
  have hd := bytesStoreDispatch_setPacketByte (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec := bytesStoreDecode_setPacketByte_locals (I := I) hsz68 hhi hcanon
  exact hrev.reEquivExecutionRevert hcode hd hdec hbody

theorem bytesStoreSetPacketByteLongReturnLongMalformedRuntime
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {len : UInt256}
    (hcode : I.code = bytesStoreBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x0a, 0xb2, 0x59, 0x00]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsz68 : 68 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (bytesStoreSetByteValueWord I).toNat < EVM.twoPow 8)
    (hlen : len = UInt256.div (bytesStorePacketLengthHeaderWord σ_evm I) ⟨2⟩)
    (hbound : (bytesStoreSetByteIndexWord I).toNat < len.toNat)
    (hflag : UInt256.land (bytesStorePacketLengthHeaderWord σ_evm I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (bytesStorePacketLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStorePacketLengthHeaderWord σ_evm I) ⟨2⟩) ⟨32⟩) ≠
      ⟨0⟩)
    (hflagPost : UInt256.land
        (bytesStorePacketLengthHeaderWord
          (sstoreAccountMap I.codeOwner σ_evm (bytesStoreSetPacketByteLongDataSlot I)
            (bytesStoreSetPacketByteLongStoredWord σ_evm I)) I) ⟨1⟩ ≠ ⟨0⟩)
    (hbadPost : UInt256.sub (UInt256.land
        (bytesStorePacketLengthHeaderWord
          (sstoreAccountMap I.codeOwner σ_evm (bytesStoreSetPacketByteLongDataSlot I)
            (bytesStoreSetPacketByteLongStoredWord σ_evm I)) I) ⟨1⟩)
        (UInt256.lt (UInt256.div
          (bytesStorePacketLengthHeaderWord
            (sstoreAccountMap I.codeOwner σ_evm (bytesStoreSetPacketByteLongDataSlot I)
              (bytesStoreSetPacketByteLongStoredWord σ_evm I)) I) ⟨2⟩) ⟨32⟩) = ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreConfig bytesStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsz := bytesStoreSetPacketByteSelector_size hsel
  have hreach := bytesStoreReachSetPacketByte (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz hsize hsel
  have hreachPc : ∃ k C, RD bytesStoreBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨282⟩
      [bytesStoreSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ_evm) k C := by
    simpa [bytesStoreSetPacketByteEntryPc] using hreach
  have hreachBody := bytesStoreX_setPacketByteDecodeValid
    (g := Sat256.ofUInt256 g) hreachPc hsz68 hhi hsize
    (bytesStoreSetPacketByteLand255_eq_self_of_uint8 hcanon)
  have hdecLen := bytesStoreX_setPacketByteReachLengthDecoder
    (g := Sat256.ofUInt256 g) hreachBody
  have h622Raw := bytesStoreX_bytesLengthDecoderLongValidMem
    (A := A) (I := I) (g := Sat256.ofUInt256 g) hdecLen hflag hvalid
    (by native_decide) (by simp only [List.length_cons, List.length_nil]; omega)
  have h622 :
      ∃ k C, RD bytesStoreBytecode I (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨622⟩
        [len, bytesStoreSetByteIndexWord I, ⟨2⟩,
          UInt256.shiftLeft (bytesStoreSetByteValueWord I) ⟨248⟩, ⟨0⟩,
          bytesStoreSetByteValueWord I, bytesStoreSetByteIndexWord I, ⟨301⟩,
          bytesStoreSelWord I]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C := by
    simpa [hlen] using h622Raw
  have hrev := bytesStoreX_setPacketByteLongWriteReturnLongMalformed
    (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
    (I := I) (g := Sat256.ofUInt256 g) (len := len)
    h622 hbound hflag hflagPost hbadPost hperm
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmSolm1 := Solm.EVM.storageStore evmSolm0 evmSolm0.executionEnv.codeOwner
    (bytesStoreSetPacketByteLongDataSlot I)
    (bytesStoreSetPacketByteLongStoredWord σ_evm I)
  have hloadHeader :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner ⟨2⟩ =
        bytesStorePacketLengthHeaderWord σ_evm I := by
    simpa [evmSolm0] using
      bytesStoreStorageLoadPacketLength_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hloadData :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner
          (bytesStoreSetPacketByteLongDataSlot I) =
        bytesStoreSetPacketByteLongOldWord σ_evm I := by
    simpa [evmSolm0] using
      bytesStoreStorageLoadSetPacketByteLongData_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hpostAccounts :
      accountMapEquiv
        (sstoreAccountMap I.codeOwner σ_evm (bytesStoreSetPacketByteLongDataSlot I)
          (bytesStoreSetPacketByteLongStoredWord σ_evm I))
        evmSolm1.accountMap := by
    simpa [evmSolm1, evmSolm0] using
      bytesStoreAccountMapEquiv_storageStore_initState
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
        (bytesStoreSetPacketByteLongDataSlot I)
        (bytesStoreSetPacketByteLongStoredWord σ_evm I)
  have hloadHeaderPost :
      Solm.EVM.storageLoad
          (Solm.EVM.storageStore evmSolm0 evmSolm0.executionEnv.codeOwner
            (bytesStoreSetPacketByteLongDataSlot I)
            (bytesStoreSetPacketByteLongStoredWord σ_evm I))
          evmSolm0.executionEnv.codeOwner ⟨2⟩ =
        bytesStorePacketLengthHeaderWord
          (sstoreAccountMap I.codeOwner σ_evm (bytesStoreSetPacketByteLongDataSlot I)
            (bytesStoreSetPacketByteLongStoredWord σ_evm I)) I := by
    have howner : evmSolm1.executionEnv.codeOwner = I.codeOwner := by
      simp [evmSolm1, evmSolm0, initState, storageStore_executionEnv]
    simpa [evmSolm1, storageStore_executionEnv] using
      bytesStoreStorageLoadPacketLength_of_accountMapEquiv
        (evm := evmSolm1)
        (σ := sstoreAccountMap I.codeOwner σ_evm (bytesStoreSetPacketByteLongDataSlot I)
          (bytesStoreSetPacketByteLongStoredWord σ_evm I))
        (I := I) howner hpostAccounts
  have hbody :
      ExecTransitionBody bytesStoreConfig bytesStoreContract evmSolm0
        (bytesStoreSetPacketByteLocals I) setPacketByteTransition.body .reverted := by
    simpa [evmSolm0, evmSolm1, initState, bytesStoreSetPacketByteFrame] using
      bytesStoreSetPacketByteLongBodyReturnRevertsOfPostLongMalformed
        (evm := evmSolm0) (σ := σ_evm) (I := I) (len := len)
        (postHeaderWord := bytesStorePacketLengthHeaderWord
          (sstoreAccountMap I.codeOwner σ_evm (bytesStoreSetPacketByteLongDataSlot I)
            (bytesStoreSetPacketByteLongStoredWord σ_evm I)) I)
        (by simp [evmSolm0, initState]; exact hwv)
        hloadHeader hloadData hloadHeaderPost hcanon hlen hbound hflag hvalid
        hflagPost hbadPost
  have hd := bytesStoreDispatch_setPacketByte (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec := bytesStoreDecode_setPacketByte_locals (I := I) hsz68 hhi hcanon
  exact hrev.reEquivExecutionRevert hcode hd hdec hbody

theorem bytesStoreSetPacketByteLongReturnShortMalformedRuntime
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {len : UInt256}
    (hcode : I.code = bytesStoreBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x0a, 0xb2, 0x59, 0x00]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsz68 : 68 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (bytesStoreSetByteValueWord I).toNat < EVM.twoPow 8)
    (hlen : len = UInt256.div (bytesStorePacketLengthHeaderWord σ_evm I) ⟨2⟩)
    (hbound : (bytesStoreSetByteIndexWord I).toNat < len.toNat)
    (hflag : UInt256.land (bytesStorePacketLengthHeaderWord σ_evm I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (bytesStorePacketLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStorePacketLengthHeaderWord σ_evm I) ⟨2⟩) ⟨32⟩) ≠
      ⟨0⟩)
    (hflagPost : UInt256.land
        (bytesStorePacketLengthHeaderWord
          (sstoreAccountMap I.codeOwner σ_evm (bytesStoreSetPacketByteLongDataSlot I)
            (bytesStoreSetPacketByteLongStoredWord σ_evm I)) I) ⟨1⟩ = ⟨0⟩)
    (hbadPost : UInt256.sub (UInt256.land
        (bytesStorePacketLengthHeaderWord
          (sstoreAccountMap I.codeOwner σ_evm (bytesStoreSetPacketByteLongDataSlot I)
            (bytesStoreSetPacketByteLongStoredWord σ_evm I)) I) ⟨1⟩)
        (UInt256.lt (UInt256.land (UInt256.div
          (bytesStorePacketLengthHeaderWord
            (sstoreAccountMap I.codeOwner σ_evm (bytesStoreSetPacketByteLongDataSlot I)
              (bytesStoreSetPacketByteLongStoredWord σ_evm I)) I) ⟨2⟩) ⟨127⟩) ⟨32⟩) =
          ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreConfig bytesStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsz := bytesStoreSetPacketByteSelector_size hsel
  have hreach := bytesStoreReachSetPacketByte (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz hsize hsel
  have hreachPc : ∃ k C, RD bytesStoreBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨282⟩
      [bytesStoreSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ_evm) k C := by
    simpa [bytesStoreSetPacketByteEntryPc] using hreach
  have hreachBody := bytesStoreX_setPacketByteDecodeValid
    (g := Sat256.ofUInt256 g) hreachPc hsz68 hhi hsize
    (bytesStoreSetPacketByteLand255_eq_self_of_uint8 hcanon)
  have hdecLen := bytesStoreX_setPacketByteReachLengthDecoder
    (g := Sat256.ofUInt256 g) hreachBody
  have h622Raw := bytesStoreX_bytesLengthDecoderLongValidMem
    (A := A) (I := I) (g := Sat256.ofUInt256 g) hdecLen hflag hvalid
    (by native_decide) (by simp only [List.length_cons, List.length_nil]; omega)
  have h622 :
      ∃ k C, RD bytesStoreBytecode I (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨622⟩
        [len, bytesStoreSetByteIndexWord I, ⟨2⟩,
          UInt256.shiftLeft (bytesStoreSetByteValueWord I) ⟨248⟩, ⟨0⟩,
          bytesStoreSetByteValueWord I, bytesStoreSetByteIndexWord I, ⟨301⟩,
          bytesStoreSelWord I]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C := by
    simpa [hlen] using h622Raw
  have hrev := bytesStoreX_setPacketByteLongWriteReturnShortMalformed
    (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
    (I := I) (g := Sat256.ofUInt256 g) (len := len)
    h622 hbound hflag hflagPost hbadPost hperm
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmSolm1 := Solm.EVM.storageStore evmSolm0 evmSolm0.executionEnv.codeOwner
    (bytesStoreSetPacketByteLongDataSlot I)
    (bytesStoreSetPacketByteLongStoredWord σ_evm I)
  have hloadHeader :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner ⟨2⟩ =
        bytesStorePacketLengthHeaderWord σ_evm I := by
    simpa [evmSolm0] using
      bytesStoreStorageLoadPacketLength_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hloadData :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner
          (bytesStoreSetPacketByteLongDataSlot I) =
        bytesStoreSetPacketByteLongOldWord σ_evm I := by
    simpa [evmSolm0] using
      bytesStoreStorageLoadSetPacketByteLongData_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hpostAccounts :
      accountMapEquiv
        (sstoreAccountMap I.codeOwner σ_evm (bytesStoreSetPacketByteLongDataSlot I)
          (bytesStoreSetPacketByteLongStoredWord σ_evm I))
        evmSolm1.accountMap := by
    simpa [evmSolm1, evmSolm0] using
      bytesStoreAccountMapEquiv_storageStore_initState
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
        (bytesStoreSetPacketByteLongDataSlot I)
        (bytesStoreSetPacketByteLongStoredWord σ_evm I)
  have hloadHeaderPost :
      Solm.EVM.storageLoad
          (Solm.EVM.storageStore evmSolm0 evmSolm0.executionEnv.codeOwner
            (bytesStoreSetPacketByteLongDataSlot I)
            (bytesStoreSetPacketByteLongStoredWord σ_evm I))
          evmSolm0.executionEnv.codeOwner ⟨2⟩ =
        bytesStorePacketLengthHeaderWord
          (sstoreAccountMap I.codeOwner σ_evm (bytesStoreSetPacketByteLongDataSlot I)
            (bytesStoreSetPacketByteLongStoredWord σ_evm I)) I := by
    have howner : evmSolm1.executionEnv.codeOwner = I.codeOwner := by
      simp [evmSolm1, evmSolm0, initState, storageStore_executionEnv]
    simpa [evmSolm1, storageStore_executionEnv] using
      bytesStoreStorageLoadPacketLength_of_accountMapEquiv
        (evm := evmSolm1)
        (σ := sstoreAccountMap I.codeOwner σ_evm (bytesStoreSetPacketByteLongDataSlot I)
          (bytesStoreSetPacketByteLongStoredWord σ_evm I))
        (I := I) howner hpostAccounts
  have hbody :
      ExecTransitionBody bytesStoreConfig bytesStoreContract evmSolm0
        (bytesStoreSetPacketByteLocals I) setPacketByteTransition.body .reverted := by
    simpa [evmSolm0, evmSolm1, initState] using
      bytesStoreSetPacketByteLongBodyReturnRevertsOfPostShortMalformed
        (evm := evmSolm0) (σ := σ_evm) (I := I) (len := len)
        (postHeaderWord := bytesStorePacketLengthHeaderWord
          (sstoreAccountMap I.codeOwner σ_evm (bytesStoreSetPacketByteLongDataSlot I)
            (bytesStoreSetPacketByteLongStoredWord σ_evm I)) I)
        (by simp [evmSolm0, initState]; exact hwv)
        hloadHeader hloadData hloadHeaderPost hcanon hlen hbound hflag hvalid
        hflagPost hbadPost
  have hd := bytesStoreDispatch_setPacketByte (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec := bytesStoreDecode_setPacketByte_locals (I := I) hsz68 hhi hcanon
  exact hrev.reEquivExecutionRevert hcode hd hdec hbody

theorem bytesStoreSetPacketByteDecodeShortRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x0a, 0xb2, 0x59, 0x00]⟩)
    (_hAccounts : accountMapEquiv σ_evm σ_solm)
    (hshort : I.calldata.size < 68) :
    runtimeEquivalenceFor bytesStoreConfig bytesStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsz := bytesStoreSetPacketByteSelector_size hsel
  have hreach := bytesStoreReachSetPacketByte (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz hsize hsel
  have hreachPc : ∃ k C, RD bytesStoreBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨282⟩
      [bytesStoreSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ_evm) k C := by
    simpa [bytesStoreSetPacketByteEntryPc] using hreach
  have hd := bytesStoreDispatch_setPacketByte (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec := bytesStoreDecode_setPacketByte_none_short (I := I) hshort
  exact (bytesStoreX_setPacketByteDecodeShort
      (g := Sat256.ofUInt256 g) hreachPc hsz hshort hsize)
    |>.reEquivDecodingFailed hcode hd hdec

theorem bytesStoreSetPacketByteDecodeHugeRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x0a, 0xb2, 0x59, 0x00]⟩)
    (_hAccounts : accountMapEquiv σ_evm σ_solm)
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size) :
    runtimeEquivalenceFor bytesStoreConfig bytesStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsz := bytesStoreSetPacketByteSelector_size hsel
  have hreach := bytesStoreReachSetPacketByte (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz hsize hsel
  have hreachPc : ∃ k C, RD bytesStoreBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨282⟩
      [bytesStoreSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ_evm) k C := by
    simpa [bytesStoreSetPacketByteEntryPc] using hreach
  have hd := bytesStoreDispatch_setPacketByte (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec := bytesStoreDecode_setPacketByte_none_huge (I := I) hbig
  exact (bytesStoreX_setPacketByteDecodeHuge
      (g := Sat256.ofUInt256 g) hreachPc hbig hsize)
    |>.reEquivDecodingFailed hcode hd hdec

theorem bytesStoreSetPacketByteDecodeNoncanonValueRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x0a, 0xb2, 0x59, 0x00]⟩)
    (_hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsz68 : 68 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hnc : ¬ (bytesStoreSetByteValueWord I).toNat < EVM.twoPow 8) :
    runtimeEquivalenceFor bytesStoreConfig bytesStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsz := bytesStoreSetPacketByteSelector_size hsel
  have hreach := bytesStoreReachSetPacketByte (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz hsize hsel
  have hreachPc : ∃ k C, RD bytesStoreBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨282⟩
      [bytesStoreSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ_evm) k C := by
    simpa [bytesStoreSetPacketByteEntryPc] using hreach
  have hd := bytesStoreDispatch_setPacketByte (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec := bytesStoreDecode_setPacketByte_none_noncanon_value (I := I) hsz68 hhi hnc
  exact (bytesStoreX_setPacketByteDecodeNoncanonValue
      (g := Sat256.ofUInt256 g) hreachPc hsz68 hhi hsize
      (bytesStoreSetPacketByteLand255_ne_self_of_not_uint8 hnc))
    |>.reEquivDecodingFailed hcode hd hdec

theorem bytesStoreSetPacketByteOobLongRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x0a, 0xb2, 0x59, 0x00]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsz68 : 68 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (bytesStoreSetByteValueWord I).toNat < EVM.twoPow 8)
    (hflag : UInt256.land (bytesStorePacketLengthHeaderWord σ_evm I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (bytesStorePacketLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStorePacketLengthHeaderWord σ_evm I) ⟨2⟩) ⟨32⟩) ≠ ⟨0⟩)
    (hbound :
      ¬ (bytesStoreSetByteIndexWord I).toNat <
        (UInt256.div (bytesStorePacketLengthHeaderWord σ_evm I) ⟨2⟩).toNat) :
    runtimeEquivalenceFor bytesStoreConfig bytesStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsz := bytesStoreSetPacketByteSelector_size hsel
  have hreach := bytesStoreReachSetPacketByte (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz hsize hsel
  have hreachPc : ∃ k C, RD bytesStoreBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨282⟩
      [bytesStoreSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ_evm) k C := by
    simpa [bytesStoreSetPacketByteEntryPc] using hreach
  have hreachBody := bytesStoreX_setPacketByteDecodeValid
    (g := Sat256.ofUInt256 g) hreachPc hsz68 hhi hsize
    (bytesStoreSetPacketByteLand255_eq_self_of_uint8 hcanon)
  have hd := bytesStoreDispatch_setPacketByte (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec := bytesStoreDecode_setPacketByte_locals (I := I) hsz68 hhi hcanon
  have hload :
      Solm.EVM.storageLoad
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        I.codeOwner ⟨2⟩ = bytesStorePacketLengthHeaderWord σ_evm I := by
    simpa [initState] using
      bytesStoreStorageLoadPacketLength_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hload' :
      Solm.EVM.storageLoad
        { (default : EVM.State) with
          accountMap := σ_solm
          σ₀ := σ₀
          executionEnv := I
          substate := A
          createdAccounts := cA
          machineState.gasAvailable := .ofUInt256 g
          blocks := bl
          genesisBlockHeader := gh }
        I.codeOwner ⟨2⟩ = bytesStorePacketLengthHeaderWord σ_evm I := by
    simpa [initState] using hload
  have hlen :
      readStorageBytesLength? bytesStoreConfig
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        { base := "packet", steps := [.field "data"] } =
          .ok (UInt256.div (bytesStorePacketLengthHeaderWord σ_evm I) ⟨2⟩).toNat := by
    exact bytesStoreReadLengthOfHeaderLoad
      (er := bytesStorePacketDataRef)
      (evm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
      (baseSlot := ⟨2⟩) (header := bytesStorePacketLengthHeaderWord σ_evm I)
      (len := (UInt256.div (bytesStorePacketLengthHeaderWord σ_evm I) ⟨2⟩).toNat)
      (bytesStorePacketDataRef_length_slot
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I))
      (by simpa [initState] using hload)
      (solidityDecodeBytesLengthHeader_long_valid hflag rfl hvalid)
  have hbody :
      ExecTransitionBody bytesStoreConfig bytesStoreContract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (bytesStoreSetPacketByteLocals I) setPacketByteTransition.body .reverted := by
    exact bytesStoreSetPacketByteBodyBoundsRevertsOfLength
      (by simp only [initState]; exact hwv) hlen hbound
  exact (bytesStoreX_setPacketByteOobLong
      (g := Sat256.ofUInt256 g) hreachBody hflag hvalid hbound)
    |>.reEquivExecutionRevert hcode hd hdec hbody

theorem bytesStoreSetPacketByteOobShortRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x0a, 0xb2, 0x59, 0x00]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsz68 : 68 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (bytesStoreSetByteValueWord I).toNat < EVM.twoPow 8)
    (hflag : UInt256.land (bytesStorePacketLengthHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (bytesStorePacketLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStorePacketLengthHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩)
          ⟨32⟩) ≠ ⟨0⟩)
    (hbound :
      ¬ (bytesStoreSetByteIndexWord I).toNat <
        (UInt256.land (UInt256.div (bytesStorePacketLengthHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩).toNat) :
    runtimeEquivalenceFor bytesStoreConfig bytesStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsz := bytesStoreSetPacketByteSelector_size hsel
  have hreach := bytesStoreReachSetPacketByte (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz hsize hsel
  have hreachPc : ∃ k C, RD bytesStoreBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨282⟩
      [bytesStoreSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ_evm) k C := by
    simpa [bytesStoreSetPacketByteEntryPc] using hreach
  have hreachBody := bytesStoreX_setPacketByteDecodeValid
    (g := Sat256.ofUInt256 g) hreachPc hsz68 hhi hsize
    (bytesStoreSetPacketByteLand255_eq_self_of_uint8 hcanon)
  have hd := bytesStoreDispatch_setPacketByte (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec := bytesStoreDecode_setPacketByte_locals (I := I) hsz68 hhi hcanon
  have hload :
      Solm.EVM.storageLoad
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        I.codeOwner ⟨2⟩ = bytesStorePacketLengthHeaderWord σ_evm I := by
    simpa [initState] using
      bytesStoreStorageLoadPacketLength_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hload' :
      Solm.EVM.storageLoad
        { (default : EVM.State) with
          accountMap := σ_solm
          σ₀ := σ₀
          executionEnv := I
          substate := A
          createdAccounts := cA
          machineState.gasAvailable := .ofUInt256 g
          blocks := bl
          genesisBlockHeader := gh }
        I.codeOwner ⟨2⟩ = bytesStorePacketLengthHeaderWord σ_evm I := by
    simpa [initState] using hload
  have hvalid0 :
      UInt256.sub ⟨0⟩
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStorePacketLengthHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩)
          ⟨32⟩) ≠ ⟨0⟩ := by
    simpa [hflag] using hvalid
  have hlen :
      readStorageBytesLength? bytesStoreConfig
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        { base := "packet", steps := [.field "data"] } =
          .ok (UInt256.land
            (UInt256.div (bytesStorePacketLengthHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩).toNat := by
    exact bytesStoreReadLengthOfHeaderLoad
      (er := bytesStorePacketDataRef)
      (evm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
      (baseSlot := ⟨2⟩) (header := bytesStorePacketLengthHeaderWord σ_evm I)
      (len := (UInt256.land
        (UInt256.div (bytesStorePacketLengthHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩).toNat)
      (bytesStorePacketDataRef_length_slot
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I))
      (by simpa [initState] using hload)
      (solidityDecodeBytesLengthHeader_short_valid hflag rfl hvalid)
  have hbody :
      ExecTransitionBody bytesStoreConfig bytesStoreContract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (bytesStoreSetPacketByteLocals I) setPacketByteTransition.body .reverted := by
    exact bytesStoreSetPacketByteBodyBoundsRevertsOfLength
      (by simp only [initState]; exact hwv) hlen hbound
  exact (bytesStoreX_setPacketByteOobShort
      (g := Sat256.ofUInt256 g) hreachBody hflag hvalid hbound)
    |>.reEquivExecutionRevert hcode hd hdec hbody

theorem bytesStoreSetPacketByteLongMalformedRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x0a, 0xb2, 0x59, 0x00]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsz68 : 68 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (bytesStoreSetByteValueWord I).toNat < EVM.twoPow 8)
    (hflag : UInt256.land (bytesStorePacketLengthHeaderWord σ_evm I) ⟨1⟩ ≠ ⟨0⟩)
    (hbad : UInt256.sub (UInt256.land (bytesStorePacketLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStorePacketLengthHeaderWord σ_evm I) ⟨2⟩) ⟨32⟩) = ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreConfig bytesStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsz := bytesStoreSetPacketByteSelector_size hsel
  have hreach := bytesStoreReachSetPacketByte (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz hsize hsel
  have hreachPc : ∃ k C, RD bytesStoreBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨282⟩
      [bytesStoreSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ_evm) k C := by
    simpa [bytesStoreSetPacketByteEntryPc] using hreach
  have hreachBody := bytesStoreX_setPacketByteDecodeValid
    (g := Sat256.ofUInt256 g) hreachPc hsz68 hhi hsize
    (bytesStoreSetPacketByteLand255_eq_self_of_uint8 hcanon)
  have hd := bytesStoreDispatch_setPacketByte (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec := bytesStoreDecode_setPacketByte_locals (I := I) hsz68 hhi hcanon
  have hload :
      Solm.EVM.storageLoad
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        I.codeOwner ⟨2⟩ = bytesStorePacketLengthHeaderWord σ_evm I := by
    simpa [initState] using
      bytesStoreStorageLoadPacketLength_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hload' :
      Solm.EVM.storageLoad
        { (default : EVM.State) with
          accountMap := σ_solm
          σ₀ := σ₀
          executionEnv := I
          substate := A
          createdAccounts := cA
          machineState.gasAvailable := .ofUInt256 g
          blocks := bl
          genesisBlockHeader := gh }
        I.codeOwner ⟨2⟩ = bytesStorePacketLengthHeaderWord σ_evm I := by
    simpa [initState] using hload
  have hlen :
      readStorageBytesLength? bytesStoreConfig
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        { base := "packet", steps := [.field "data"] } = .revert := by
    exact bytesStoreReadLengthRevertOfHeaderLoad
      (er := bytesStorePacketDataRef)
      (evm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
      (baseSlot := ⟨2⟩) (header := bytesStorePacketLengthHeaderWord σ_evm I)
      (bytesStorePacketDataRef_length_slot
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I))
      (by simpa [initState] using hload)
      (by simp [solidityDecodeBytesLengthHeader, hflag, hbad])
  have hbody :
      ExecTransitionBody bytesStoreConfig bytesStoreContract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (bytesStoreSetPacketByteLocals I) setPacketByteTransition.body .reverted := by
    exact bytesStoreSetPacketByteBodyRevertsOfLengthRead
      (by simp only [initState]; exact hwv) hlen
  exact (bytesStoreX_setPacketByteLongMalformed
      (g := Sat256.ofUInt256 g) hreachBody hflag hbad)
    |>.reEquivExecutionRevert hcode hd hdec hbody

theorem bytesStoreSetPacketByteShortMalformedRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x0a, 0xb2, 0x59, 0x00]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsz68 : 68 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (bytesStoreSetByteValueWord I).toNat < EVM.twoPow 8)
    (hflag : UInt256.land (bytesStorePacketLengthHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩)
    (hbad : UInt256.sub (UInt256.land (bytesStorePacketLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStorePacketLengthHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩)
          ⟨32⟩) = ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreConfig bytesStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsz := bytesStoreSetPacketByteSelector_size hsel
  have hreach := bytesStoreReachSetPacketByte (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz hsize hsel
  have hreachPc : ∃ k C, RD bytesStoreBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨282⟩
      [bytesStoreSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ_evm) k C := by
    simpa [bytesStoreSetPacketByteEntryPc] using hreach
  have hreachBody := bytesStoreX_setPacketByteDecodeValid
    (g := Sat256.ofUInt256 g) hreachPc hsz68 hhi hsize
    (bytesStoreSetPacketByteLand255_eq_self_of_uint8 hcanon)
  have hd := bytesStoreDispatch_setPacketByte (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec := bytesStoreDecode_setPacketByte_locals (I := I) hsz68 hhi hcanon
  have hload :
      Solm.EVM.storageLoad
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        I.codeOwner ⟨2⟩ = bytesStorePacketLengthHeaderWord σ_evm I := by
    simpa [initState] using
      bytesStoreStorageLoadPacketLength_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hload' :
      Solm.EVM.storageLoad
        { (default : EVM.State) with
          accountMap := σ_solm
          σ₀ := σ₀
          executionEnv := I
          substate := A
          createdAccounts := cA
          machineState.gasAvailable := .ofUInt256 g
          blocks := bl
          genesisBlockHeader := gh }
        I.codeOwner ⟨2⟩ = bytesStorePacketLengthHeaderWord σ_evm I := by
    simpa [initState] using hload
  have hbad0 :
      UInt256.sub ⟨0⟩
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStorePacketLengthHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩)
          ⟨32⟩) = ⟨0⟩ := by
    simpa [hflag] using hbad
  have hlen :
      readStorageBytesLength? bytesStoreConfig
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        { base := "packet", steps := [.field "data"] } = .revert := by
    exact bytesStoreReadLengthRevertOfHeaderLoad
      (er := bytesStorePacketDataRef)
      (evm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
      (baseSlot := ⟨2⟩) (header := bytesStorePacketLengthHeaderWord σ_evm I)
      (bytesStorePacketDataRef_length_slot
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I))
      (by simpa [initState] using hload)
      (by simp [solidityDecodeBytesLengthHeader, hflag, hbad0])
  have hbody :
      ExecTransitionBody bytesStoreConfig bytesStoreContract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (bytesStoreSetPacketByteLocals I) setPacketByteTransition.body .reverted := by
    exact bytesStoreSetPacketByteBodyRevertsOfLengthRead
      (by simp only [initState]; exact hwv) hlen
  exact (bytesStoreX_setPacketByteShortMalformed
      (g := Sat256.ofUInt256 g) hreachBody hflag hbad)
    |>.reEquivExecutionRevert hcode hd hdec hbody

theorem bytesStoreSetPacketByteRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x0a, 0xb2, 0x59, 0x00]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor bytesStoreConfig bytesStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  by_cases hsz68 : 68 ≤ I.calldata.size
  · by_cases hhi : I.calldata.size < 2 ^ 255 + 4
    · by_cases hcanon : (bytesStoreSetByteValueWord I).toNat < EVM.twoPow 8
      · by_cases hflagLong :
          UInt256.land (bytesStorePacketLengthHeaderWord σ_evm I) ⟨1⟩ ≠ ⟨0⟩
        · by_cases hvalidLong :
            UInt256.sub (UInt256.land (bytesStorePacketLengthHeaderWord σ_evm I) ⟨1⟩)
              (UInt256.lt (UInt256.div (bytesStorePacketLengthHeaderWord σ_evm I) ⟨2⟩)
                ⟨32⟩) ≠ ⟨0⟩
          · let len := UInt256.div (bytesStorePacketLengthHeaderWord σ_evm I) ⟨2⟩
            by_cases hbound : (bytesStoreSetByteIndexWord I).toNat < len.toNat
            · by_cases haccSome : ∃ accEvm, σ_evm.find? I.codeOwner = some accEvm
              · obtain ⟨accEvm, haccEq⟩ := haccSome
                let postHeader :=
                  bytesStorePacketLengthHeaderWord
                    (sstoreAccountMap I.codeOwner σ_evm
                      (bytesStoreSetPacketByteLongDataSlot I)
                      (bytesStoreSetPacketByteLongStoredWord σ_evm I)) I
                by_cases hflagPostLong : UInt256.land postHeader ⟨1⟩ ≠ ⟨0⟩
                · by_cases hvalidPostLong :
                    UInt256.sub (UInt256.land postHeader ⟨1⟩)
                      (UInt256.lt (UInt256.div postHeader ⟨2⟩) ⟨32⟩) ≠ ⟨0⟩
                  · let lenPost := UInt256.div postHeader ⟨2⟩
                    by_cases hboundPost :
                        (bytesStoreSetByteIndexWord I).toNat < lenPost.toNat
                    · exact bytesStoreSetPacketByteLongReturnLongSuccessRuntime
                        (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm)
                        (σ_solm := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
                        (len := len) (lenPost := lenPost) (accEvm := accEvm)
                        hcode hsize hperm hwv hsel hAccounts haccEq hsz68 hhi hcanon
                        (by rfl) (by simpa [postHeader] using hflagPostLong)
                        (by simpa [postHeader] using hvalidPostLong)
                        (by rfl) hbound hboundPost hflagLong hvalidLong
                    · exact bytesStoreSetPacketByteLongReturnLongOobLengthRuntime
                        (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm)
                        (σ_solm := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
                        (len := len) (lenPost := lenPost) (accEvm := accEvm)
                        hcode hsize hperm hwv hsel hAccounts haccEq hsz68 hhi hcanon
                        (by rfl) (by simpa [postHeader] using hflagPostLong)
                        (by simpa [postHeader] using hvalidPostLong)
                        (by rfl) hbound hboundPost hflagLong hvalidLong
                  · exact bytesStoreSetPacketByteLongReturnLongMalformedRuntime
                      (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm)
                      (σ_solm := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
                      (len := len)
                      hcode hsize hperm hwv hsel hAccounts hsz68 hhi hcanon
                      (by rfl) hbound hflagLong hvalidLong
                      (by simpa [postHeader] using hflagPostLong)
                      (by simpa [postHeader] using hvalidPostLong)
                · have hflagPostShort : UInt256.land postHeader ⟨1⟩ = ⟨0⟩ := by
                    by_contra hne
                    exact hflagPostLong hne
                  by_cases hvalidPostShort :
                    UInt256.sub (UInt256.land postHeader ⟨1⟩)
                      (UInt256.lt (UInt256.land (UInt256.div postHeader ⟨2⟩) ⟨127⟩)
                        ⟨32⟩) ≠ ⟨0⟩
                  · let lenPost := UInt256.land (UInt256.div postHeader ⟨2⟩) ⟨127⟩
                    by_cases hboundPost :
                        (bytesStoreSetByteIndexWord I).toNat < lenPost.toNat
                    · exact bytesStoreSetPacketByteLongReturnShortSuccessRuntime
                        (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm)
                        (σ_solm := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
                        (len := len) (lenPost := lenPost) (accEvm := accEvm)
                        hcode hsize hperm hwv hsel hAccounts haccEq hsz68 hhi hcanon
                        (by rfl) (by simpa [postHeader] using hflagPostShort)
                        (by simpa [postHeader] using hvalidPostShort)
                        (by rfl) hbound hboundPost hflagLong hvalidLong
                    · exact bytesStoreSetPacketByteLongReturnShortOobLengthRuntime
                        (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm)
                        (σ_solm := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
                        (len := len) (lenPost := lenPost)
                        hcode hsize hperm hwv hsel hAccounts hsz68 hhi hcanon
                        (by rfl) (by simpa [postHeader] using hflagPostShort)
                        (by simpa [postHeader] using hvalidPostShort)
                        (by rfl) hbound hboundPost hflagLong hvalidLong
                  · have hbadPostShort :
                      UInt256.sub (UInt256.land postHeader ⟨1⟩)
                        (UInt256.lt
                          (UInt256.land (UInt256.div postHeader ⟨2⟩) ⟨127⟩) ⟨32⟩) =
                          ⟨0⟩ := by
                      by_contra hne
                      exact hvalidPostShort hne
                    exact bytesStoreSetPacketByteLongReturnShortMalformedRuntime
                      (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm)
                      (σ_solm := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
                      (len := len)
                      hcode hsize hperm hwv hsel hAccounts hsz68 hhi hcanon
                      (by rfl) hbound hflagLong hvalidLong
                      (by simpa [postHeader] using hflagPostShort)
                      (by simpa [postHeader] using hbadPostShort)
              · have haccNone : σ_evm.find? I.codeOwner = none := by
                  cases haccEq : σ_evm.find? I.codeOwner with
                  | none => rfl
                  | some accEvm => exact False.elim (haccSome ⟨accEvm, haccEq⟩)
                have hhdr :
                    bytesStorePacketLengthHeaderWord σ_evm I = ⟨0⟩ := by
                  simp [bytesStorePacketLengthHeaderWord, haccNone, Option.option]
                have hflag0 :
                    UInt256.land (bytesStorePacketLengthHeaderWord σ_evm I) ⟨1⟩ =
                      ⟨0⟩ := by
                  rw [hhdr]
                  native_decide
                exact False.elim (hflagLong hflag0)
            · exact bytesStoreSetPacketByteOobLongRuntime
                (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm)
                (σ_solm := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
                hcode hsize hperm hwv hsel hAccounts hsz68 hhi hcanon hflagLong
                hvalidLong hbound
          · have hbad :
              UInt256.sub (UInt256.land (bytesStorePacketLengthHeaderWord σ_evm I) ⟨1⟩)
                (UInt256.lt (UInt256.div (bytesStorePacketLengthHeaderWord σ_evm I) ⟨2⟩)
                  ⟨32⟩) = ⟨0⟩ := by
              by_contra hne
              exact hvalidLong hne
            exact bytesStoreSetPacketByteLongMalformedRuntime
              (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm)
              (σ_solm := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
              hcode hsize hperm hwv hsel hAccounts hsz68 hhi hcanon hflagLong hbad
        · have hflagShort :
            UInt256.land (bytesStorePacketLengthHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩ := by
            by_contra hne
            exact hflagLong hne
          by_cases hvalidShort :
              UInt256.sub (UInt256.land (bytesStorePacketLengthHeaderWord σ_evm I) ⟨1⟩)
                (UInt256.lt
                  (UInt256.land
                    (UInt256.div (bytesStorePacketLengthHeaderWord σ_evm I) ⟨2⟩)
                    ⟨127⟩) ⟨32⟩) ≠ ⟨0⟩
          · let len :=
              UInt256.land
                (UInt256.div (bytesStorePacketLengthHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩
            have hltNe : UInt256.lt len ⟨32⟩ ≠ ⟨0⟩ := by
              intro hlt0
              have hzero : UInt256.sub ⟨0⟩ ⟨0⟩ = (⟨0⟩ : UInt256) := by
                native_decide
              exact hvalidShort (by simpa [len, hflagShort, hlt0] using hzero)
            have hshort : len.toNat < 32 := by
              have hlt := ult_ne_zero_toNat_lt hltNe
              simpa using hlt
            by_cases hbound : (bytesStoreSetByteIndexWord I).toNat < len.toNat
            · by_cases haccSome : ∃ accEvm, σ_evm.find? I.codeOwner = some accEvm
              · obtain ⟨accEvm, haccEq⟩ := haccSome
                exact bytesStoreSetPacketByteShortSuccessRuntime
                  (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm)
                  (σ_solm := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
                  (len := len) (accEvm := accEvm)
                  hcode hsize hperm hwv hsel hAccounts haccEq hsz68 hhi hcanon
                  (by rfl) hshort hbound hflagShort hvalidShort
              · have haccNone : σ_evm.find? I.codeOwner = none := by
                  cases haccEq : σ_evm.find? I.codeOwner with
                  | none => rfl
                  | some accEvm => exact False.elim (haccSome ⟨accEvm, haccEq⟩)
                have hhdr :
                    bytesStorePacketLengthHeaderWord σ_evm I = ⟨0⟩ := by
                  simp [bytesStorePacketLengthHeaderWord, haccNone, Option.option]
                have hlenZero : len = ⟨0⟩ := by
                  change
                    UInt256.land
                      (UInt256.div (bytesStorePacketLengthHeaderWord σ_evm I) ⟨2⟩)
                      ⟨127⟩ = ⟨0⟩
                  rw [hhdr]
                  native_decide
                have hlen0 : len.toNat = 0 := by
                  simp [hlenZero]
                have hbadBound : (bytesStoreSetByteIndexWord I).toNat < 0 := by
                  simpa [hlen0] using hbound
                exact False.elim (Nat.not_lt_zero _ hbadBound)
            · exact bytesStoreSetPacketByteOobShortRuntime
                (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm)
                (σ_solm := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
                hcode hsize hperm hwv hsel hAccounts hsz68 hhi hcanon hflagShort
                hvalidShort hbound
          · have hbad :
              UInt256.sub (UInt256.land (bytesStorePacketLengthHeaderWord σ_evm I) ⟨1⟩)
                (UInt256.lt
                  (UInt256.land
                    (UInt256.div (bytesStorePacketLengthHeaderWord σ_evm I) ⟨2⟩)
                    ⟨127⟩) ⟨32⟩) = ⟨0⟩ := by
              by_contra hne
              exact hvalidShort hne
            exact bytesStoreSetPacketByteShortMalformedRuntime
              (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm)
              (σ_solm := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
              hcode hsize hperm hwv hsel hAccounts hsz68 hhi hcanon hflagShort hbad
      · exact bytesStoreSetPacketByteDecodeNoncanonValueRuntime
          (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
          (σ₀ := σ₀) (A := A) (I := I) (g := g)
          hcode hsize hperm hwv hsel hAccounts hsz68 hhi hcanon
    · exact bytesStoreSetPacketByteDecodeHugeRuntime
        (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
        (σ₀ := σ₀) (A := A) (I := I) (g := g)
        hcode hsize hperm hwv hsel hAccounts (by omega)
  · exact bytesStoreSetPacketByteDecodeShortRuntime
      (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
      (σ₀ := σ₀) (A := A) (I := I) (g := g)
      hcode hsize hperm hwv hsel hAccounts (by omega)

end BytesStore
