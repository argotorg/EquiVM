import Examples.BytesStoreLite.FullSetByte

/-!
# BytesStoreLite — `setPacketByte(uint256,uint8)` runtime slice

This module starts the packet byte setter proof in a separate file so the large dispatcher/getter
module does not keep growing while the remaining setter bodies are proved.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

namespace BytesStoreLite

def bytesStoreLiteSetPacketByteLocals (I : ExecutionEnv) : Store :=
  ((∅ : Store).insert "byteIndex"
    (.int (Int.ofNat (bytesStoreLiteSetByteIndexWord I).toNat))).insert "value"
    (.int (Int.ofNat (bytesStoreLiteSetByteValueWord I).toNat))

def bytesStoreLiteSetPacketByteRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "packet"
    steps := [.field "data",
      .aindex (.int (Int.ofNat (bytesStoreLiteSetByteIndexWord I).toNat))] }

def bytesStoreLiteSetPacketByteValue (I : ExecutionEnv) : Value :=
  .int (Int.ofNat (bytesStoreLiteSetByteValueWord I).toNat)

def bytesStoreLiteSetPacketByteFrame (I : ExecutionEnv) : Frame :=
  { contract := bytesStoreLiteContract, locals := bytesStoreLiteSetPacketByteLocals I }

def bytesStoreLiteSetPacketByteShortScale (I : ExecutionEnv) : UInt256 :=
  UInt256.exp ⟨256⟩ (UInt256.sub ⟨31⟩ (bytesStoreLiteSetByteIndexWord I))

def bytesStoreLiteSetPacketByteShortStoredWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.lor
    (UInt256.mul
      (UInt256.div (UInt256.shiftLeft (bytesStoreLiteSetByteValueWord I) ⟨248⟩)
        (UInt256.shiftLeft ⟨1⟩ ⟨248⟩))
      (bytesStoreLiteSetPacketByteShortScale I))
    (UInt256.land
      (UInt256.lnot (UInt256.mul ⟨255⟩ (bytesStoreLiteSetPacketByteShortScale I)))
      (bytesStoreLitePacketLengthHeaderWord σ I))

def bytesStoreLiteSetPacketByteLongWordIndex (I : ExecutionEnv) : UInt256 :=
  UInt256.mod (bytesStoreLiteSetByteIndexWord I) ⟨32⟩

def bytesStoreLiteSetPacketByteLongDataSlot (I : ExecutionEnv) : UInt256 :=
  bytesLikeDataBase ⟨2⟩ + UInt256.div (bytesStoreLiteSetByteIndexWord I) ⟨32⟩

def bytesStoreLiteSetPacketByteLongScale (I : ExecutionEnv) : UInt256 :=
  UInt256.exp ⟨256⟩ (UInt256.sub ⟨31⟩ (bytesStoreLiteSetPacketByteLongWordIndex I))

def bytesStoreLiteSetPacketByteLongOldWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  (σ.find? I.codeOwner |>.option ⟨0⟩
    (fun acc => acc.storage.findD (bytesStoreLiteSetPacketByteLongDataSlot I) ⟨0⟩))

def bytesStoreLiteSetPacketByteLongStoredWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.lor
    (UInt256.mul
      (UInt256.div (UInt256.shiftLeft (bytesStoreLiteSetByteValueWord I) ⟨248⟩)
        (UInt256.shiftLeft ⟨1⟩ ⟨248⟩))
      (bytesStoreLiteSetPacketByteLongScale I))
    (UInt256.land
      (UInt256.lnot (UInt256.mul ⟨255⟩ (bytesStoreLiteSetPacketByteLongScale I)))
      (bytesStoreLiteSetPacketByteLongOldWord σ I))

/-- Trusted keccak disjointness: `packet.data` long-bytes data slots do not alias its header. -/
axiom bytesStoreLitePacketDataSlot_ne_header (idx : UInt256) :
    bytesLikeDataBase ⟨2⟩ + UInt256.div idx ⟨32⟩ ≠ (⟨2⟩ : UInt256)

theorem bytesStoreLiteSetPacketByteLongBaseHash :
    UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC ((wordAt0Mem (⟨2⟩ : UInt256) solcFreePtrMem).readWithPadding 0 32))) =
      bytesLikeDataBase ⟨2⟩ := by
  rw [wordAt0Mem_read0]
  simpa [bytesLikeDataBase] using keccakSlot_eq (UInt256.toByteArray (⟨2⟩ : UInt256))

theorem bytesStoreLiteSetPacketByteLongBaseHashMem (mem : ByteArray) :
    UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC ((wordAt0Mem (⟨2⟩ : UInt256) mem).readWithPadding 0 32))) =
      bytesLikeDataBase ⟨2⟩ := by
  rw [wordAt0Mem_read0]
  simpa [bytesLikeDataBase] using keccakSlot_eq (UInt256.toByteArray (⟨2⟩ : UInt256))

theorem bytesStoreLiteX_returnUInt8_301OfMem {cA gh bl σinit σ σ₀ A I} {g : Sat256}
    {val : UInt256} {mem : ByteArray}
    (hsize : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨301⟩
      [val, bytesStoreLiteSelWord I] mem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C) :
    RDret bytesStoreLiteBytecode g (initState cA gh bl σinit σ₀ g A I) (cA, σ)
      (UInt256.toByteArray (UInt256.land val ⟨255⟩)) := by
  obtain ⟨_, _, rd301⟩ := hreach
  have rd273 := evm_run rd301 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by native_decide)
      mem_cost
      (mloadFreePtrValue (by rw [hsize]; decide) (by decide) hread64)
      (by native_decide) (by evm_ov),
    push1 ⟨255⟩, swap1, swap2, and, dup2,
    raw mstore 6 (bytesStoreLiteReturnFromMem mem (UInt256.land val ⟨255⟩))
      (UInt256.ofNat 5) (by native_decide)
      mem_cost
      (by rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide]; rfl)
      (by native_decide) (by evm_ov),
    push1 ⟨32⟩, add, push2 ⟨273⟩, jump (by native_decide)]
  exact evm_run rd273 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 5) (by native_decide)
      mem_cost
      (bytesStoreLiteReturnFromMem_mload64 mem (UInt256.land val ⟨255⟩) hsize hread64)
      (by native_decide) (by evm_ov),
    dup1, swap2, sub, swap1,
    raw ret 0 (UInt256.toByteArray (UInt256.land val ⟨255⟩)) (by native_decide)
      mem_cost
      (by
        rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide,
          show (UInt256.sub ((⟨32⟩ : UInt256) + ⟨128⟩) ⟨128⟩).toNat = 32 from by decide,
          bytesStoreLiteReturnFromMem_read128 mem (UInt256.land val ⟨255⟩) hsize])
      (by evm_ov)]

theorem bytesStoreLiteSetPacketByteShortStoredWord_load_self
    {σ : AccountMap} {I : ExecutionEnv} {acc : Account}
    (hacc : σ.find? I.codeOwner = some acc)
    (hnz : (bytesStoreLiteSetPacketByteShortStoredWord σ I == (default : UInt256)) = false) :
    (((sstoreAccountMap I.codeOwner σ ⟨2⟩
        (bytesStoreLiteSetPacketByteShortStoredWord σ I)).find? I.codeOwner).option
        (default : UInt256) (fun acc => acc.storage.findD ⟨2⟩ (default : UInt256))) =
      bytesStoreLiteSetPacketByteShortStoredWord σ I := by
  exact sstoreAccountMap_storage_findD_self_of_find_some σ I.codeOwner acc ⟨2⟩
    (bytesStoreLiteSetPacketByteShortStoredWord σ I) hacc hnz

theorem bytesStoreLiteSetPacketByteLongWordIndex_toNat (I : ExecutionEnv) :
    (bytesStoreLiteSetPacketByteLongWordIndex I).toNat =
      (bytesStoreLiteSetByteIndexWord I).toNat % 32 := by
  simpa [bytesStoreLiteSetPacketByteLongWordIndex, bytesStoreLiteSetByteLongWordIndex] using
    bytesStoreLiteSetByteLongWordIndex_toNat I

theorem bytesStoreLiteSetPacketByteLongWordIndex_lt32 (I : ExecutionEnv) :
    (bytesStoreLiteSetPacketByteLongWordIndex I).toNat < 32 := by
  rw [bytesStoreLiteSetPacketByteLongWordIndex_toNat]
  exact Nat.mod_lt _ (by decide : 0 < 32)

theorem bytesStoreLiteSetPacketByteLongScale_toNat {I : ExecutionEnv} :
    (bytesStoreLiteSetPacketByteLongScale I).toNat =
      2 ^ ((31 - (bytesStoreLiteSetPacketByteLongWordIndex I).toNat) * 8) := by
  simpa [bytesStoreLiteSetPacketByteLongScale, bytesStoreLiteSetByteLongScale,
    bytesStoreLiteSetPacketByteLongWordIndex, bytesStoreLiteSetByteLongWordIndex] using
    bytesStoreLiteSetByteLongScale_toNat (I := I)

theorem bytesStoreLiteSetPacketByteLongMaskWord_toNat {I : ExecutionEnv} :
    (UInt256.mul ⟨255⟩ (bytesStoreLiteSetPacketByteLongScale I)).toNat =
      255 * 2 ^ ((31 - (bytesStoreLiteSetPacketByteLongWordIndex I).toNat) * 8) := by
  simpa [bytesStoreLiteSetPacketByteLongScale, bytesStoreLiteSetByteLongScale,
    bytesStoreLiteSetPacketByteLongWordIndex, bytesStoreLiteSetByteLongWordIndex] using
    bytesStoreLiteSetByteLongMaskWord_toNat (I := I)

theorem bytesStoreLiteSetPacketByteLongClearMask_toNat {I : ExecutionEnv} :
    (UInt256.lnot (UInt256.mul ⟨255⟩ (bytesStoreLiteSetPacketByteLongScale I))).toNat =
      (2 : Nat) ^ 256 - 1 -
        255 * 2 ^ ((31 - (bytesStoreLiteSetPacketByteLongWordIndex I).toNat) * 8) := by
  simpa [bytesStoreLiteSetPacketByteLongScale, bytesStoreLiteSetByteLongScale,
    bytesStoreLiteSetPacketByteLongWordIndex, bytesStoreLiteSetByteLongWordIndex] using
    bytesStoreLiteSetByteLongClearMask_toNat (I := I)

theorem bytesStoreLiteSetPacketByteShortScale_toNat {I : ExecutionEnv} {len : UInt256}
    (hshort : len.toNat < 32)
    (hbound : (bytesStoreLiteSetByteIndexWord I).toNat < len.toNat) :
    (bytesStoreLiteSetPacketByteShortScale I).toNat =
      2 ^ ((31 - (bytesStoreLiteSetByteIndexWord I).toNat) * 8) := by
  simpa [bytesStoreLiteSetPacketByteShortScale, bytesStoreLiteSetByteShortScale] using
    bytesStoreLiteSetByteShortScale_toNat (I := I) (len := len) hshort hbound

theorem bytesStoreLiteSetPacketByteShortMaskWord_toNat {I : ExecutionEnv} {len : UInt256}
    (hshort : len.toNat < 32)
    (hbound : (bytesStoreLiteSetByteIndexWord I).toNat < len.toNat) :
    (UInt256.mul ⟨255⟩ (bytesStoreLiteSetPacketByteShortScale I)).toNat =
      255 * 2 ^ ((31 - (bytesStoreLiteSetByteIndexWord I).toNat) * 8) := by
  simpa [bytesStoreLiteSetPacketByteShortScale, bytesStoreLiteSetByteShortScale] using
    bytesStoreLiteSetByteShortMaskWord_toNat (I := I) (len := len) hshort hbound

theorem bytesStoreLiteSetPacketByteShortClearMask_toNat {I : ExecutionEnv} {len : UInt256}
    (hshort : len.toNat < 32)
    (hbound : (bytesStoreLiteSetByteIndexWord I).toNat < len.toNat) :
    (UInt256.lnot (UInt256.mul ⟨255⟩ (bytesStoreLiteSetPacketByteShortScale I))).toNat =
      2 ^ 256 - 1 - 255 * 2 ^ ((31 - (bytesStoreLiteSetByteIndexWord I).toNat) * 8) := by
  simpa [bytesStoreLiteSetPacketByteShortScale, bytesStoreLiteSetByteShortScale] using
    bytesStoreLiteSetByteShortClearMask_toNat (I := I) (len := len) hshort hbound

theorem bytesStoreLiteSetPacketByteShortStoredWord_byteAt
    {σ : AccountMap} {I : ExecutionEnv} {len : UInt256}
    (hcanon : (bytesStoreLiteSetByteValueWord I).toNat < EVM.twoPow 8)
    (hshort : len.toNat < 32)
    (hbound : (bytesStoreLiteSetByteIndexWord I).toNat < len.toNat) :
    UInt256.byteAt (bytesStoreLiteSetByteIndexWord I)
      (bytesStoreLiteSetPacketByteShortStoredWord σ I) = bytesStoreLiteSetByteValueWord I := by
  apply u256_inj
  have hi31 : (bytesStoreLiteSetByteIndexWord I).toNat ≤ 31 := by
    have hlt := bytesStoreLiteSetByteIndex_lt31_of_short_bound (I := I) (len := len)
      hshort hbound
    omega
  rw [byteAt_toNat_of_le31 hi31]
  rw [bytesStoreLiteSetPacketByteShortStoredWord, bytesStoreLiteSetByteValueHighShiftDiv hcanon]
  rw [u256_lor_toNat, u256_mul_toNat, u256_land_toNat]
  rw [bytesStoreLiteSetPacketByteShortScale_toNat (I := I) (len := len) hshort hbound]
  rw [bytesStoreLiteSetPacketByteShortClearMask_toNat (I := I) (len := len) hshort hbound]
  have hv : (bytesStoreLiteSetByteValueWord I).toNat < 256 := by
    simpa [EVM.twoPow] using hcanon
  have hk : ((31 - (bytesStoreLiteSetByteIndexWord I).toNat) * 8) + 8 ≤ 256 := by
    have hidx : (bytesStoreLiteSetByteIndexWord I).toNat < 31 :=
      bytesStoreLiteSetByteIndex_lt31_of_short_bound (I := I) (len := len) hshort hbound
    omega
  have hleftLt : (bytesStoreLiteSetByteValueWord I).toNat *
      2 ^ ((31 - (bytesStoreLiteSetByteIndexWord I).toNat) * 8) < UInt256.size := by
    rw [show UInt256.size = 2 ^ 256 from rfl]
    calc (bytesStoreLiteSetByteValueWord I).toNat *
            2 ^ ((31 - (bytesStoreLiteSetByteIndexWord I).toNat) * 8) <
          256 * 2 ^ ((31 - (bytesStoreLiteSetByteIndexWord I).toNat) * 8) :=
            Nat.mul_lt_mul_of_pos_right hv (by positivity)
        _ ≤ 2 ^ 256 := by
          rw [show 256 = 2 ^ 8 by norm_num, ← Nat.pow_add]
          exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hrightLt : (((2 : Nat) ^ 256 - 1 -
        255 * 2 ^ ((31 - (bytesStoreLiteSetByteIndexWord I).toNat) * 8)) &&&
        (bytesStoreLitePacketLengthHeaderWord σ I).toNat) < UInt256.size := by
    exact lt_of_le_of_lt Nat.and_le_right (bytesStoreLitePacketLengthHeaderWord σ I).val.isLt
  rw [Nat.mod_eq_of_lt hleftLt]
  change ((bytesStoreLiteSetByteValueWord I).toNat *
          2 ^ ((31 - (bytesStoreLiteSetByteIndexWord I).toNat) * 8)).lor
        ((((2 : Nat) ^ 256 - 1 -
          255 * 2 ^ ((31 - (bytesStoreLiteSetByteIndexWord I).toNat) * 8)) &&&
          (bytesStoreLitePacketLengthHeaderWord σ I).toNat) % UInt256.size) %
        UInt256.size /
      2 ^ ((31 - (bytesStoreLiteSetByteIndexWord I).toNat) * 8) % 256 =
    (bytesStoreLiteSetByteValueWord I).toNat
  rw [Nat.mod_eq_of_lt hrightLt]
  have hlorLt :
      ((bytesStoreLiteSetByteValueWord I).toNat *
            2 ^ ((31 - (bytesStoreLiteSetByteIndexWord I).toNat) * 8)).lor
          (((2 : Nat) ^ 256 - 1 -
              255 * 2 ^ ((31 - (bytesStoreLiteSetByteIndexWord I).toNat) * 8)) &&&
            (bytesStoreLitePacketLengthHeaderWord σ I).toNat) < UInt256.size := by
    change ((bytesStoreLiteSetByteValueWord I).toNat *
          2 ^ ((31 - (bytesStoreLiteSetByteIndexWord I).toNat) * 8)) |||
        (((2 : Nat) ^ 256 - 1 -
            255 * 2 ^ ((31 - (bytesStoreLiteSetByteIndexWord I).toNat) * 8)) &&&
          (bytesStoreLitePacketLengthHeaderWord σ I).toNat) < 2 ^ 256
    apply Nat.or_lt_two_pow
    · simpa [UInt256.size] using hleftLt
    · simpa [UInt256.size] using hrightLt
  rw [Nat.mod_eq_of_lt hlorLt]
  exact nat_byte_lane_lor_clear_eq
    (old := (bytesStoreLitePacketLengthHeaderWord σ I).toNat)
    (v := (bytesStoreLiteSetByteValueWord I).toNat)
    (k := (31 - (bytesStoreLiteSetByteIndexWord I).toNat) * 8) hv hk

theorem bytesStoreLiteSetPacketByteLongStoredWord_byteAt
    {σ : AccountMap} {I : ExecutionEnv}
    (hcanon : (bytesStoreLiteSetByteValueWord I).toNat < EVM.twoPow 8) :
    UInt256.byteAt (bytesStoreLiteSetPacketByteLongWordIndex I)
      (bytesStoreLiteSetPacketByteLongStoredWord σ I) = bytesStoreLiteSetByteValueWord I := by
  apply u256_inj
  have hv : (bytesStoreLiteSetByteValueWord I).toNat < 256 := by
    simpa [EVM.twoPow] using hcanon
  have hidxLt : (bytesStoreLiteSetPacketByteLongWordIndex I).toNat < 32 :=
    bytesStoreLiteSetPacketByteLongWordIndex_lt32 I
  have hidxLe : (bytesStoreLiteSetPacketByteLongWordIndex I).toNat ≤ 31 := by omega
  rw [byteAt_toNat_of_le31 hidxLe]
  rw [bytesStoreLiteSetPacketByteLongStoredWord, bytesStoreLiteSetByteValueHighShiftDiv hcanon]
  rw [u256_lor_toNat, u256_mul_toNat, u256_land_toNat]
  rw [bytesStoreLiteSetPacketByteLongScale_toNat (I := I)]
  rw [bytesStoreLiteSetPacketByteLongClearMask_toNat (I := I)]
  have hk : ((31 - (bytesStoreLiteSetPacketByteLongWordIndex I).toNat) * 8) + 8 ≤ 256 := by
    omega
  have hleftLt : (bytesStoreLiteSetByteValueWord I).toNat *
      2 ^ ((31 - (bytesStoreLiteSetPacketByteLongWordIndex I).toNat) * 8) < UInt256.size := by
    rw [show UInt256.size = 2 ^ 256 from rfl]
    calc (bytesStoreLiteSetByteValueWord I).toNat *
            2 ^ ((31 - (bytesStoreLiteSetPacketByteLongWordIndex I).toNat) * 8) <
          256 * 2 ^ ((31 - (bytesStoreLiteSetPacketByteLongWordIndex I).toNat) * 8) :=
            Nat.mul_lt_mul_of_pos_right hv (by positivity)
        _ = 2 ^ (8 + (31 - (bytesStoreLiteSetPacketByteLongWordIndex I).toNat) * 8) := by
          rw [show 256 = 2 ^ 8 by norm_num, Nat.pow_add]
        _ ≤ 2 ^ 256 := by
          exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hrightLt : (((2 : Nat) ^ 256 - 1 -
        255 * 2 ^ ((31 - (bytesStoreLiteSetPacketByteLongWordIndex I).toNat) * 8)) &&&
        (bytesStoreLiteSetPacketByteLongOldWord σ I).toNat) < UInt256.size := by
    exact lt_of_le_of_lt Nat.and_le_right (bytesStoreLiteSetPacketByteLongOldWord σ I).val.isLt
  rw [Nat.mod_eq_of_lt hleftLt]
  change (((bytesStoreLiteSetByteValueWord I).toNat *
          2 ^ ((31 - (bytesStoreLiteSetPacketByteLongWordIndex I).toNat) * 8)).lor
        ((((2 : Nat) ^ 256 - 1 -
          255 * 2 ^ ((31 - (bytesStoreLiteSetPacketByteLongWordIndex I).toNat) * 8)) &&&
          (bytesStoreLiteSetPacketByteLongOldWord σ I).toNat) % UInt256.size) %
        UInt256.size) /
      2 ^ ((31 - (bytesStoreLiteSetPacketByteLongWordIndex I).toNat) * 8) % 256 =
    (bytesStoreLiteSetByteValueWord I).toNat
  rw [Nat.mod_eq_of_lt hrightLt]
  have hlorLt :
      ((bytesStoreLiteSetByteValueWord I).toNat *
            2 ^ ((31 - (bytesStoreLiteSetPacketByteLongWordIndex I).toNat) * 8)).lor
          (((2 : Nat) ^ 256 - 1 -
              255 * 2 ^ ((31 - (bytesStoreLiteSetPacketByteLongWordIndex I).toNat) * 8)) &&&
            (bytesStoreLiteSetPacketByteLongOldWord σ I).toNat) < UInt256.size := by
    change ((bytesStoreLiteSetByteValueWord I).toNat *
          2 ^ ((31 - (bytesStoreLiteSetPacketByteLongWordIndex I).toNat) * 8)) |||
        (((2 : Nat) ^ 256 - 1 -
            255 * 2 ^ ((31 - (bytesStoreLiteSetPacketByteLongWordIndex I).toNat) * 8)) &&&
          (bytesStoreLiteSetPacketByteLongOldWord σ I).toNat) < 2 ^ 256
    apply Nat.or_lt_two_pow
    · simpa [UInt256.size] using hleftLt
    · simpa [UInt256.size] using hrightLt
  rw [Nat.mod_eq_of_lt hlorLt]
  exact nat_byte_lane_lor_clear_eq
    (old := (bytesStoreLiteSetPacketByteLongOldWord σ I).toNat)
    (v := (bytesStoreLiteSetByteValueWord I).toNat)
    (k := (31 - (bytesStoreLiteSetPacketByteLongWordIndex I).toNat) * 8) hv hk

theorem bytesStoreLiteSetPacketByteShortStoredWord_toNat_update
    {σ : AccountMap} {I : ExecutionEnv} {len : UInt256}
    (hcanon : (bytesStoreLiteSetByteValueWord I).toNat < EVM.twoPow 8)
    (hshort : len.toNat < 32)
    (hbound : (bytesStoreLiteSetByteIndexWord I).toNat < len.toNat) :
    (bytesStoreLitePacketLengthHeaderWord σ I).toNat %
          2 ^ ((31 - (bytesStoreLiteSetByteIndexWord I).toNat) * 8) +
        2 ^ ((31 - (bytesStoreLiteSetByteIndexWord I).toNat) * 8) *
          (bytesStoreLiteSetByteValueWord I).toNat +
      2 ^ ((31 - (bytesStoreLiteSetByteIndexWord I).toNat) * 8 + 8) *
        ((bytesStoreLitePacketLengthHeaderWord σ I).toNat /
          2 ^ ((31 - (bytesStoreLiteSetByteIndexWord I).toNat) * 8 + 8)) =
    (bytesStoreLiteSetPacketByteShortStoredWord σ I).toNat := by
  have hv : (bytesStoreLiteSetByteValueWord I).toNat < 256 := by
    simpa [EVM.twoPow] using hcanon
  rw [bytesStoreLiteSetPacketByteShortStoredWord, bytesStoreLiteSetByteValueHighShiftDiv hcanon]
  rw [u256_lor_toNat, u256_mul_toNat, u256_land_toNat]
  rw [bytesStoreLiteSetPacketByteShortScale_toNat (I := I) (len := len) hshort hbound]
  rw [bytesStoreLiteSetPacketByteShortClearMask_toNat (I := I) (len := len) hshort hbound]
  have hk : ((31 - (bytesStoreLiteSetByteIndexWord I).toNat) * 8) + 8 ≤ 256 := by
    have hidx := bytesStoreLiteSetByteIndex_lt31_of_short_bound
      (I := I) (len := len) hshort hbound
    omega
  have hleftLt : (bytesStoreLiteSetByteValueWord I).toNat *
      2 ^ ((31 - (bytesStoreLiteSetByteIndexWord I).toNat) * 8) < UInt256.size := by
    rw [show UInt256.size = 2 ^ 256 from rfl]
    calc (bytesStoreLiteSetByteValueWord I).toNat *
            2 ^ ((31 - (bytesStoreLiteSetByteIndexWord I).toNat) * 8) <
          256 * 2 ^ ((31 - (bytesStoreLiteSetByteIndexWord I).toNat) * 8) :=
            Nat.mul_lt_mul_of_pos_right hv (by positivity)
        _ ≤ 2 ^ 256 := by
          rw [show 256 = 2 ^ 8 by norm_num, ← Nat.pow_add]
          exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hrightLt : (((2 : Nat) ^ 256 - 1 -
        255 * 2 ^ ((31 - (bytesStoreLiteSetByteIndexWord I).toNat) * 8)) &&&
        (bytesStoreLitePacketLengthHeaderWord σ I).toNat) < UInt256.size := by
    exact lt_of_le_of_lt Nat.and_le_right (bytesStoreLitePacketLengthHeaderWord σ I).val.isLt
  rw [Nat.mod_eq_of_lt hleftLt]
  change (bytesStoreLitePacketLengthHeaderWord σ I).toNat %
        2 ^ ((31 - (bytesStoreLiteSetByteIndexWord I).toNat) * 8) +
      2 ^ ((31 - (bytesStoreLiteSetByteIndexWord I).toNat) * 8) *
        (bytesStoreLiteSetByteValueWord I).toNat +
      2 ^ (((31 - (bytesStoreLiteSetByteIndexWord I).toNat) * 8) + 8) *
        ((bytesStoreLitePacketLengthHeaderWord σ I).toNat /
          2 ^ (((31 - (bytesStoreLiteSetByteIndexWord I).toNat) * 8) + 8)) =
      ((bytesStoreLiteSetByteValueWord I).toNat *
          2 ^ ((31 - (bytesStoreLiteSetByteIndexWord I).toNat) * 8)).lor
        ((((2 : Nat) ^ 256 - 1 -
          255 * 2 ^ ((31 - (bytesStoreLiteSetByteIndexWord I).toNat) * 8)) &&&
          (bytesStoreLitePacketLengthHeaderWord σ I).toNat) % UInt256.size) %
        UInt256.size
  rw [Nat.mod_eq_of_lt hrightLt]
  have hlorLt :
      ((bytesStoreLiteSetByteValueWord I).toNat *
            2 ^ ((31 - (bytesStoreLiteSetByteIndexWord I).toNat) * 8)).lor
          (((2 : Nat) ^ 256 - 1 -
              255 * 2 ^ ((31 - (bytesStoreLiteSetByteIndexWord I).toNat) * 8)) &&&
            (bytesStoreLitePacketLengthHeaderWord σ I).toNat) < UInt256.size := by
    change ((bytesStoreLiteSetByteValueWord I).toNat *
          2 ^ ((31 - (bytesStoreLiteSetByteIndexWord I).toNat) * 8)) |||
        (((2 : Nat) ^ 256 - 1 -
            255 * 2 ^ ((31 - (bytesStoreLiteSetByteIndexWord I).toNat) * 8)) &&&
          (bytesStoreLitePacketLengthHeaderWord σ I).toNat) < 2 ^ 256
    apply Nat.or_lt_two_pow
    · simpa [UInt256.size] using hleftLt
    · simpa [UInt256.size] using hrightLt
  rw [Nat.mod_eq_of_lt hlorLt]
  rw [show 2 ^ ((31 - (bytesStoreLiteSetByteIndexWord I).toNat) * 8) *
        (bytesStoreLiteSetByteValueWord I).toNat =
        (bytesStoreLiteSetByteValueWord I).toNat *
          2 ^ ((31 - (bytesStoreLiteSetByteIndexWord I).toNat) * 8) by ring]
  rw [show 2 ^ (((31 - (bytesStoreLiteSetByteIndexWord I).toNat) * 8) + 8) *
        ((bytesStoreLitePacketLengthHeaderWord σ I).toNat /
          2 ^ (((31 - (bytesStoreLiteSetByteIndexWord I).toNat) * 8) + 8)) =
      (bytesStoreLitePacketLengthHeaderWord σ I).toNat /
          2 ^ (((31 - (bytesStoreLiteSetByteIndexWord I).toNat) * 8) + 8) *
        2 ^ (((31 - (bytesStoreLiteSetByteIndexWord I).toNat) * 8) + 8) by ring]
  exact nat_byte_update_eq
    (old := (bytesStoreLitePacketLengthHeaderWord σ I).toNat)
    (v := (bytesStoreLiteSetByteValueWord I).toNat)
    (k := (31 - (bytesStoreLiteSetByteIndexWord I).toNat) * 8)
    hv hk (by exact (bytesStoreLitePacketLengthHeaderWord σ I).val.isLt)

theorem bytesStoreLiteSetPacketByteLongStoredWord_toNat_update
    {σ : AccountMap} {I : ExecutionEnv}
    (hcanon : (bytesStoreLiteSetByteValueWord I).toNat < EVM.twoPow 8) :
    (bytesStoreLiteSetPacketByteLongOldWord σ I).toNat %
          2 ^ ((31 - (bytesStoreLiteSetPacketByteLongWordIndex I).toNat) * 8) +
        2 ^ ((31 - (bytesStoreLiteSetPacketByteLongWordIndex I).toNat) * 8) *
          (bytesStoreLiteSetByteValueWord I).toNat +
      2 ^ ((31 - (bytesStoreLiteSetPacketByteLongWordIndex I).toNat) * 8 + 8) *
        ((bytesStoreLiteSetPacketByteLongOldWord σ I).toNat /
          2 ^ ((31 - (bytesStoreLiteSetPacketByteLongWordIndex I).toNat) * 8 + 8)) =
    (bytesStoreLiteSetPacketByteLongStoredWord σ I).toNat := by
  have hv : (bytesStoreLiteSetByteValueWord I).toNat < 256 := by
    simpa [EVM.twoPow] using hcanon
  rw [bytesStoreLiteSetPacketByteLongStoredWord, bytesStoreLiteSetByteValueHighShiftDiv hcanon]
  rw [u256_lor_toNat, u256_mul_toNat, u256_land_toNat]
  rw [bytesStoreLiteSetPacketByteLongScale_toNat (I := I)]
  rw [bytesStoreLiteSetPacketByteLongClearMask_toNat (I := I)]
  have hidxLt : (bytesStoreLiteSetPacketByteLongWordIndex I).toNat < 32 :=
    bytesStoreLiteSetPacketByteLongWordIndex_lt32 I
  have hk : ((31 - (bytesStoreLiteSetPacketByteLongWordIndex I).toNat) * 8) + 8 ≤ 256 := by
    omega
  have hleftLt : (bytesStoreLiteSetByteValueWord I).toNat *
      2 ^ ((31 - (bytesStoreLiteSetPacketByteLongWordIndex I).toNat) * 8) < UInt256.size := by
    rw [show UInt256.size = 2 ^ 256 from rfl]
    calc (bytesStoreLiteSetByteValueWord I).toNat *
            2 ^ ((31 - (bytesStoreLiteSetPacketByteLongWordIndex I).toNat) * 8) <
          256 * 2 ^ ((31 - (bytesStoreLiteSetPacketByteLongWordIndex I).toNat) * 8) :=
            Nat.mul_lt_mul_of_pos_right hv (by positivity)
        _ = 2 ^ (8 + (31 - (bytesStoreLiteSetPacketByteLongWordIndex I).toNat) * 8) := by
          rw [show 256 = 2 ^ 8 by norm_num, Nat.pow_add]
        _ ≤ 2 ^ 256 := by
          exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hrightLt : (((2 : Nat) ^ 256 - 1 -
        255 * 2 ^ ((31 - (bytesStoreLiteSetPacketByteLongWordIndex I).toNat) * 8)) &&&
        (bytesStoreLiteSetPacketByteLongOldWord σ I).toNat) < UInt256.size := by
    exact lt_of_le_of_lt Nat.and_le_right (bytesStoreLiteSetPacketByteLongOldWord σ I).val.isLt
  rw [Nat.mod_eq_of_lt hleftLt]
  change (bytesStoreLiteSetPacketByteLongOldWord σ I).toNat %
        2 ^ ((31 - (bytesStoreLiteSetPacketByteLongWordIndex I).toNat) * 8) +
      2 ^ ((31 - (bytesStoreLiteSetPacketByteLongWordIndex I).toNat) * 8) *
        (bytesStoreLiteSetByteValueWord I).toNat +
      2 ^ (((31 - (bytesStoreLiteSetPacketByteLongWordIndex I).toNat) * 8) + 8) *
        ((bytesStoreLiteSetPacketByteLongOldWord σ I).toNat /
          2 ^ (((31 - (bytesStoreLiteSetPacketByteLongWordIndex I).toNat) * 8) + 8)) =
      ((bytesStoreLiteSetByteValueWord I).toNat *
          2 ^ ((31 - (bytesStoreLiteSetPacketByteLongWordIndex I).toNat) * 8)).lor
        ((((2 : Nat) ^ 256 - 1 -
          255 * 2 ^ ((31 - (bytesStoreLiteSetPacketByteLongWordIndex I).toNat) * 8)) &&&
          (bytesStoreLiteSetPacketByteLongOldWord σ I).toNat) % UInt256.size) %
        UInt256.size
  rw [Nat.mod_eq_of_lt hrightLt]
  have hlorLt :
      ((bytesStoreLiteSetByteValueWord I).toNat *
            2 ^ ((31 - (bytesStoreLiteSetPacketByteLongWordIndex I).toNat) * 8)).lor
          (((2 : Nat) ^ 256 - 1 -
              255 * 2 ^ ((31 - (bytesStoreLiteSetPacketByteLongWordIndex I).toNat) * 8)) &&&
            (bytesStoreLiteSetPacketByteLongOldWord σ I).toNat) < UInt256.size := by
    change ((bytesStoreLiteSetByteValueWord I).toNat *
          2 ^ ((31 - (bytesStoreLiteSetPacketByteLongWordIndex I).toNat) * 8)) |||
        (((2 : Nat) ^ 256 - 1 -
            255 * 2 ^ ((31 - (bytesStoreLiteSetPacketByteLongWordIndex I).toNat) * 8)) &&&
          (bytesStoreLiteSetPacketByteLongOldWord σ I).toNat) < 2 ^ 256
    apply Nat.or_lt_two_pow
    · simpa [UInt256.size] using hleftLt
    · simpa [UInt256.size] using hrightLt
  rw [Nat.mod_eq_of_lt hlorLt]
  rw [show 2 ^ ((31 - (bytesStoreLiteSetPacketByteLongWordIndex I).toNat) * 8) *
        (bytesStoreLiteSetByteValueWord I).toNat =
        (bytesStoreLiteSetByteValueWord I).toNat *
          2 ^ ((31 - (bytesStoreLiteSetPacketByteLongWordIndex I).toNat) * 8) by ring]
  rw [show 2 ^ (((31 - (bytesStoreLiteSetPacketByteLongWordIndex I).toNat) * 8) + 8) *
        ((bytesStoreLiteSetPacketByteLongOldWord σ I).toNat /
          2 ^ (((31 - (bytesStoreLiteSetPacketByteLongWordIndex I).toNat) * 8) + 8)) =
      (bytesStoreLiteSetPacketByteLongOldWord σ I).toNat /
          2 ^ (((31 - (bytesStoreLiteSetPacketByteLongWordIndex I).toNat) * 8) + 8) *
        2 ^ (((31 - (bytesStoreLiteSetPacketByteLongWordIndex I).toNat) * 8) + 8) by ring]
  exact nat_byte_update_eq
    (old := (bytesStoreLiteSetPacketByteLongOldWord σ I).toNat)
    (v := (bytesStoreLiteSetByteValueWord I).toNat)
    (k := (31 - (bytesStoreLiteSetPacketByteLongWordIndex I).toNat) * 8)
    hv hk (by exact (bytesStoreLiteSetPacketByteLongOldWord σ I).val.isLt)

theorem bytesStoreLiteSetPacketByteShortScale_mod256_zero {I : ExecutionEnv} {len : UInt256}
    (hshort : len.toNat < 32)
    (hbound : (bytesStoreLiteSetByteIndexWord I).toNat < len.toNat) :
    (bytesStoreLiteSetPacketByteShortScale I).toNat % 256 = 0 := by
  simpa [bytesStoreLiteSetPacketByteShortScale, bytesStoreLiteSetByteShortScale] using
    bytesStoreLiteSetByteShortScale_mod256_zero (I := I) (len := len) hshort hbound

theorem bytesStoreLiteSetPacketByteShortClearMask_mod256_255
    {I : ExecutionEnv} {len : UInt256}
    (hshort : len.toNat < 32)
    (hbound : (bytesStoreLiteSetByteIndexWord I).toNat < len.toNat) :
    (UInt256.lnot (UInt256.mul ⟨255⟩ (bytesStoreLiteSetPacketByteShortScale I))).toNat % 256 =
      255 := by
  simpa [bytesStoreLiteSetPacketByteShortScale, bytesStoreLiteSetByteShortScale] using
    bytesStoreLiteSetByteShortClearMask_mod256_255 (I := I) (len := len) hshort hbound

theorem bytesStoreLiteSetPacketByteShortStoredWord_mod256
    {σ : AccountMap} {I : ExecutionEnv} {len : UInt256}
    (hshort : len.toNat < 32)
    (hbound : (bytesStoreLiteSetByteIndexWord I).toNat < len.toNat) :
    (bytesStoreLiteSetPacketByteShortStoredWord σ I).toNat % 256 =
      (bytesStoreLitePacketLengthHeaderWord σ I).toNat % 256 := by
  have hscale := bytesStoreLiteSetPacketByteShortScale_mod256_zero
    (I := I) (len := len) hshort hbound
  have hmask := bytesStoreLiteSetPacketByteShortClearMask_mod256_255
    (I := I) (len := len) hshort hbound
  have hleft :
      (UInt256.mul
        (UInt256.div (UInt256.shiftLeft (bytesStoreLiteSetByteValueWord I) ⟨248⟩)
          (UInt256.shiftLeft ⟨1⟩ ⟨248⟩))
        (bytesStoreLiteSetPacketByteShortScale I)).toNat % 256 = 0 := by
    rw [u256_mul_toNat, nat_mod_u256_mod_256, Nat.mul_mod, hscale]
    simp
  have hright :
      (UInt256.land
        (UInt256.lnot (UInt256.mul ⟨255⟩ (bytesStoreLiteSetPacketByteShortScale I)))
        (bytesStoreLitePacketLengthHeaderWord σ I)).toNat % 256 =
        (bytesStoreLitePacketLengthHeaderWord σ I).toNat % 256 := by
    rw [u256_land_toNat, nat_mod_u256_mod_256]
    exact nat_land_mod_256_of_left_255 hmask
  rw [bytesStoreLiteSetPacketByteShortStoredWord, u256_lor_toNat, nat_mod_u256_mod_256]
  rw [nat_lor_mod_256_of_left_zero hleft, hright]

theorem bytesStoreLiteSetPacketByteShortStoredWord_flag_eq
    {σ : AccountMap} {I : ExecutionEnv} {len : UInt256}
    (hshort : len.toNat < 32)
    (hbound : (bytesStoreLiteSetByteIndexWord I).toNat < len.toNat) :
    UInt256.land (bytesStoreLiteSetPacketByteShortStoredWord σ I) ⟨1⟩ =
      UInt256.land (bytesStoreLitePacketLengthHeaderWord σ I) ⟨1⟩ := by
  apply u256_inj
  rw [uInt256_land_one_toNat, uInt256_land_one_toNat]
  have hmod := bytesStoreLiteSetPacketByteShortStoredWord_mod256
    (σ := σ) (I := I) (len := len) hshort hbound
  have hleft :
      (bytesStoreLiteSetPacketByteShortStoredWord σ I).toNat % 2 =
        ((bytesStoreLiteSetPacketByteShortStoredWord σ I).toNat % 256) % 2 := by
    rw [Nat.mod_mod_of_dvd]
    norm_num
  have hright :
      (bytesStoreLitePacketLengthHeaderWord σ I).toNat % 2 =
        ((bytesStoreLitePacketLengthHeaderWord σ I).toNat % 256) % 2 := by
    rw [Nat.mod_mod_of_dvd]
    norm_num
  rw [hleft, hright, hmod]

theorem bytesStoreLiteSetPacketByteShortStoredWord_shortLen_eq
    {σ : AccountMap} {I : ExecutionEnv} {len : UInt256}
    (hshort : len.toNat < 32)
    (hbound : (bytesStoreLiteSetByteIndexWord I).toNat < len.toNat) :
    UInt256.land (UInt256.div (bytesStoreLiteSetPacketByteShortStoredWord σ I) ⟨2⟩) ⟨127⟩ =
      UInt256.land (UInt256.div (bytesStoreLitePacketLengthHeaderWord σ I) ⟨2⟩) ⟨127⟩ := by
  apply u256_inj
  rw [bytesStoreLiteShortLenBits_toNat, bytesStoreLiteShortLenBits_toNat]
  rw [bytesStoreLiteSetPacketByteShortStoredWord_mod256 (σ := σ) (I := I) (len := len)
    hshort hbound]

theorem bytesStoreLiteSetPacketByteShortStoredWord_ne_zero
    {σ : AccountMap} {I : ExecutionEnv} {len : UInt256}
    (hlen : len =
      UInt256.land (UInt256.div (bytesStoreLitePacketLengthHeaderWord σ I) ⟨2⟩) ⟨127⟩)
    (hshort : len.toNat < 32)
    (hbound : (bytesStoreLiteSetByteIndexWord I).toNat < len.toNat) :
    bytesStoreLiteSetPacketByteShortStoredWord σ I ≠ ⟨0⟩ := by
  intro hzero
  have hshortLen := bytesStoreLiteSetPacketByteShortStoredWord_shortLen_eq
    (σ := σ) (I := I) (len := len) hshort hbound
  rw [hzero] at hshortLen
  have hlenZero : len.toNat = 0 := by
    rw [hlen, ← hshortLen]
    native_decide
  omega

theorem bytesStoreLiteSetPacketByteShortStoredWord_beq_zero_false
    {σ : AccountMap} {I : ExecutionEnv} {len : UInt256}
    (hlen : len =
      UInt256.land (UInt256.div (bytesStoreLitePacketLengthHeaderWord σ I) ⟨2⟩) ⟨127⟩)
    (hshort : len.toNat < 32)
    (hbound : (bytesStoreLiteSetByteIndexWord I).toNat < len.toNat) :
    (bytesStoreLiteSetPacketByteShortStoredWord σ I == (default : UInt256)) = false := by
  exact beq_false_of_ne
    (bytesStoreLiteSetPacketByteShortStoredWord_ne_zero (σ := σ) (I := I) (len := len)
      hlen hshort hbound)

theorem bytesStoreLiteSetPacketByte_storageTypeAt {I : ExecutionEnv} :
    storageTypeAt? bytesStoreLiteContract.storage (bytesStoreLiteSetPacketByteRef I) =
      some uint8St := by
  simp [bytesStoreLiteSetPacketByteRef, storageTypeAt?, bytesStoreLiteContract, storageDecls,
    packetStructDecl, packetStructTy, bytesSt, uint8St, uint8Int, storageTypeStep?]

theorem bytesStoreLiteSetPacketByteLayoutShort {evm : EVM.State} {I : ExecutionEnv}
    (hpacked : checkBytesPacked ⟨2⟩ evm = true)
    (hidx : (bytesStoreLiteSetByteIndexWord I).toNat < 31) :
    bytesStoreLiteConfig.storage.layout (bytesStoreLiteSetPacketByteRef I) evm =
      some (uint8Loc ⟨2⟩ ⟨31 - (bytesStoreLiteSetByteIndexWord I).toNat, by omega⟩) := by
  simp [bytesStoreLiteConfig, bytesStoreLiteStorageLayout, solidityStorageLayout,
    bytesStoreLiteLayout, bytesStoreLiteSetPacketByteRef, bytesLikeByteLoc?, uint8Loc,
    uint8Int, hpacked, hidx]

theorem bytesStoreLiteSetPacketByteLayoutLong {evm : EVM.State} {I : ExecutionEnv}
    (hpacked : checkBytesPacked ⟨2⟩ evm = false) :
    bytesStoreLiteConfig.storage.layout (bytesStoreLiteSetPacketByteRef I) evm =
      some (uint8Loc (bytesStoreLiteSetPacketByteLongDataSlot I)
        ⟨31 - (bytesStoreLiteSetPacketByteLongWordIndex I).toNat, by
          have hidx := bytesStoreLiteSetPacketByteLongWordIndex_lt32 I
          omega⟩) := by
  rw [bytesStoreLiteSetPacketByteLongDataSlot, u256_div32_eq_ofNat_toNat_div]
  simp [bytesStoreLiteConfig, bytesStoreLiteStorageLayout, solidityStorageLayout,
    bytesStoreLiteLayout, bytesStoreLiteSetPacketByteRef, bytesLikeByteLoc?, uint8Loc,
    uint8Int, hpacked, bytesStoreLiteSetPacketByteLongWordIndex_toNat]

theorem bytesStoreLiteSetPacketByteStorageLocStoreShort
    {evm : EVM.State} {σ : AccountMap} {I : ExecutionEnv} {len : UInt256}
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩ =
      bytesStoreLitePacketLengthHeaderWord σ I)
    (hcanon : (bytesStoreLiteSetByteValueWord I).toNat < EVM.twoPow 8)
    (hshort : len.toNat < 32)
    (hbound : (bytesStoreLiteSetByteIndexWord I).toNat < len.toNat) :
    storageLocStore evm
      (uint8Loc ⟨2⟩ ⟨31 - (bytesStoreLiteSetByteIndexWord I).toNat, by
        have hidx := bytesStoreLiteSetByteIndex_lt31_of_short_bound
          (I := I) (len := len) hshort hbound
        omega⟩)
      (bytesStoreLiteSetPacketByteValue I) =
      some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨2⟩
        (bytesStoreLiteSetPacketByteShortStoredWord σ I)) := by
  let offFin : Fin 32 :=
    ⟨31 - (bytesStoreLiteSetByteIndexWord I).toNat, by
      have hidx := bytesStoreLiteSetByteIndex_lt31_of_short_bound
        (I := I) (len := len) hshort hbound
      omega⟩
  have hval : valueToWord (bytesStoreLiteSetPacketByteValue I) =
      some (UInt256.ofNat (bytesStoreLiteSetByteValueWord I).toNat) := by
    simp [bytesStoreLiteSetPacketByteValue, valueToWord]
    exact bytesStoreLiteWordOfIntOfNatEq (bytesStoreLiteSetByteValueWord I).toNat
  have hoffVal : offFin.val = 31 - (bytesStoreLiteSetByteIndexWord I).toNat := by
    rfl
  have hoffLe : offFin.val ≤ 32 := Nat.le_of_lt offFin.isLt
  have hv : (bytesStoreLiteSetByteValueWord I).toNat < 256 := by
    simpa [EVM.twoPow] using hcanon
  have hoffBound : offFin.val + (1 : Fin 33).val - 1 < 32 := by
    have hidx := bytesStoreLiteSetByteIndex_lt31_of_short_bound
      (I := I) (len := len) hshort hbound
    simp [offFin]
    omega
  have htarget :
      (bytesStoreLiteSetPacketByteShortStoredWord σ I).toNat =
        fromBytes'
          ((EVM.Word.toBytesLEWithSizeProof
                (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩)).1.take offFin.val ++
           (EVM.Word.toBytesLEWithSizeProof
                (storageLocWriteWord
                  (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩)
                  offFin.val none
                  (UInt256.ofNat (bytesStoreLiteSetByteValueWord I).toNat))).1.take 1 ++
           (EVM.Word.toBytesLEWithSizeProof
                (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩)).1.drop
              (offFin.val + 1)) := by
    rw [hload]
    simp only [storageLocWriteWord]
    symm
    rw [fromBytes'_append, fromBytes'_append]
    rw [fromBytes'_take_wordLE, fromBytes'_take_wordLE, fromBytes'_drop_wordLE]
    have hslen := (EVM.Word.toBytesLEWithSizeProof
      (bytesStoreLitePacketLengthHeaderWord σ I)).2
    have hvlen := (EVM.Word.toBytesLEWithSizeProof
      (UInt256.ofNat (bytesStoreLiteSetByteValueWord I).toNat)).2
    rw [List.length_take, hslen, Nat.min_eq_left hoffLe]
    rw [List.length_append, List.length_take, hslen, Nat.min_eq_left hoffLe,
      List.length_take, hvlen, Nat.min_eq_left (by norm_num : 1 ≤ 32)]
    rw [show 8 * (offFin.val + 1) = 8 * offFin.val + 8 by ring]
    rw [show 256 ^ offFin.val = 2 ^ (8 * offFin.val) by
      rw [show (256 : Nat) = 2 ^ 8 by norm_num, ← Nat.pow_mul]]
    rw [show 256 ^ 1 = 256 by norm_num]
    rw [show (UInt256.ofNat (bytesStoreLiteSetByteValueWord I).toNat).toNat % 256 =
        (bytesStoreLiteSetByteValueWord I).toNat by
      rw [ulit_toNat' _ (lt_of_lt_of_le hv (by norm_num [UInt256.size]))]
      exact Nat.mod_eq_of_lt hv]
    rw [hoffVal]
    rw [show 8 * (31 - (bytesStoreLiteSetByteIndexWord I).toNat) =
        (31 - (bytesStoreLiteSetByteIndexWord I).toNat) * 8 by ring]
    rw [show 256 ^ (31 - (bytesStoreLiteSetByteIndexWord I).toNat + 1) =
        2 ^ (((31 - (bytesStoreLiteSetByteIndexWord I).toNat) * 8) + 8) by
      rw [show 256 = 2 ^ 8 by norm_num, ← Nat.pow_mul]
      congr 1
      ring]
    change
      (bytesStoreLitePacketLengthHeaderWord σ I).toNat %
            2 ^ ((31 - (bytesStoreLiteSetByteIndexWord I).toNat) * 8) +
          2 ^ ((31 - (bytesStoreLiteSetByteIndexWord I).toNat) * 8) *
            (bytesStoreLiteSetByteValueWord I).toNat +
        2 ^ ((31 - (bytesStoreLiteSetByteIndexWord I).toNat) * 8 + 8) *
          ((bytesStoreLitePacketLengthHeaderWord σ I).toNat /
            2 ^ ((31 - (bytesStoreLiteSetByteIndexWord I).toNat) * 8 + 8)) =
      (bytesStoreLiteSetPacketByteShortStoredWord σ I).toNat
    exact bytesStoreLiteSetPacketByteShortStoredWord_toNat_update
      (σ := σ) (I := I) (len := len) hcanon hshort hbound
  change storageLocStore evm
      { slot := ⟨2⟩, offset := offFin, size := 1, hbound := hoffBound,
        type := .int uint8Int }
      (bytesStoreLiteSetPacketByteValue I) =
      some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨2⟩
        (bytesStoreLiteSetPacketByteShortStoredWord σ I))
  exact storageLocStore_oneByte_local evm ⟨2⟩
    (UInt256.ofNat (bytesStoreLiteSetByteValueWord I).toNat)
    (bytesStoreLiteSetPacketByteShortStoredWord σ I)
    offFin (.int uint8Int) hoffBound
    (bytesStoreLiteSetPacketByteValue I) hval htarget

theorem bytesStoreLiteSetPacketByteStorageLocStoreLong
    {evm : EVM.State} {σ : AccountMap} {I : ExecutionEnv}
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (bytesStoreLiteSetPacketByteLongDataSlot I) =
      bytesStoreLiteSetPacketByteLongOldWord σ I)
    (hcanon : (bytesStoreLiteSetByteValueWord I).toNat < EVM.twoPow 8) :
    storageLocStore evm
      (uint8Loc (bytesStoreLiteSetPacketByteLongDataSlot I)
        ⟨31 - (bytesStoreLiteSetPacketByteLongWordIndex I).toNat, by
          have hidx := bytesStoreLiteSetPacketByteLongWordIndex_lt32 I
          omega⟩)
      (bytesStoreLiteSetPacketByteValue I) =
      some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner
        (bytesStoreLiteSetPacketByteLongDataSlot I)
        (bytesStoreLiteSetPacketByteLongStoredWord σ I)) := by
  let offFin : Fin 32 :=
    ⟨31 - (bytesStoreLiteSetPacketByteLongWordIndex I).toNat, by
      have hidx := bytesStoreLiteSetPacketByteLongWordIndex_lt32 I
      omega⟩
  have hval : valueToWord (bytesStoreLiteSetPacketByteValue I) =
      some (UInt256.ofNat (bytesStoreLiteSetByteValueWord I).toNat) := by
    simp [bytesStoreLiteSetPacketByteValue, valueToWord]
    exact bytesStoreLiteWordOfIntOfNatEq (bytesStoreLiteSetByteValueWord I).toNat
  have hoffVal : offFin.val = 31 - (bytesStoreLiteSetPacketByteLongWordIndex I).toNat := by
    rfl
  have hoffLe : offFin.val ≤ 32 := Nat.le_of_lt offFin.isLt
  have hv : (bytesStoreLiteSetByteValueWord I).toNat < 256 := by
    simpa [EVM.twoPow] using hcanon
  have hoffBound : offFin.val + (1 : Fin 33).val - 1 < 32 := by
    simp [offFin]
    omega
  have htarget :
      (bytesStoreLiteSetPacketByteLongStoredWord σ I).toNat =
        fromBytes'
          ((EVM.Word.toBytesLEWithSizeProof
                (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
                  (bytesStoreLiteSetPacketByteLongDataSlot I))).1.take offFin.val ++
           (EVM.Word.toBytesLEWithSizeProof
                (storageLocWriteWord
                  (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
                    (bytesStoreLiteSetPacketByteLongDataSlot I))
                  offFin.val none
                  (UInt256.ofNat (bytesStoreLiteSetByteValueWord I).toNat))).1.take 1 ++
           (EVM.Word.toBytesLEWithSizeProof
                (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
                  (bytesStoreLiteSetPacketByteLongDataSlot I))).1.drop
              (offFin.val + 1)) := by
    rw [hload]
    simp only [storageLocWriteWord]
    symm
    rw [fromBytes'_append, fromBytes'_append]
    rw [fromBytes'_take_wordLE, fromBytes'_take_wordLE, fromBytes'_drop_wordLE]
    have hslen := (EVM.Word.toBytesLEWithSizeProof
      (bytesStoreLiteSetPacketByteLongOldWord σ I)).2
    have hvlen := (EVM.Word.toBytesLEWithSizeProof
      (UInt256.ofNat (bytesStoreLiteSetByteValueWord I).toNat)).2
    rw [List.length_take, hslen, Nat.min_eq_left hoffLe]
    rw [List.length_append, List.length_take, hslen, Nat.min_eq_left hoffLe,
      List.length_take, hvlen, Nat.min_eq_left (by norm_num : 1 ≤ 32)]
    rw [show 8 * (offFin.val + 1) = 8 * offFin.val + 8 by ring]
    rw [show 256 ^ offFin.val = 2 ^ (8 * offFin.val) by
      rw [show (256 : Nat) = 2 ^ 8 by norm_num, ← Nat.pow_mul]]
    rw [show 256 ^ 1 = 256 by norm_num]
    rw [show (UInt256.ofNat (bytesStoreLiteSetByteValueWord I).toNat).toNat % 256 =
        (bytesStoreLiteSetByteValueWord I).toNat by
      rw [ulit_toNat' _ (lt_of_lt_of_le hv (by norm_num [UInt256.size]))]
      exact Nat.mod_eq_of_lt hv]
    rw [hoffVal]
    rw [show 8 * (31 - (bytesStoreLiteSetPacketByteLongWordIndex I).toNat) =
        (31 - (bytesStoreLiteSetPacketByteLongWordIndex I).toNat) * 8 by ring]
    rw [show 256 ^ (31 - (bytesStoreLiteSetPacketByteLongWordIndex I).toNat + 1) =
        2 ^ (((31 - (bytesStoreLiteSetPacketByteLongWordIndex I).toNat) * 8) + 8) by
      rw [show 256 = 2 ^ 8 by norm_num, ← Nat.pow_mul]
      congr 1
      ring]
    change
      (bytesStoreLiteSetPacketByteLongOldWord σ I).toNat %
            2 ^ ((31 - (bytesStoreLiteSetPacketByteLongWordIndex I).toNat) * 8) +
          2 ^ ((31 - (bytesStoreLiteSetPacketByteLongWordIndex I).toNat) * 8) *
            (bytesStoreLiteSetByteValueWord I).toNat +
        2 ^ ((31 - (bytesStoreLiteSetPacketByteLongWordIndex I).toNat) * 8 + 8) *
          ((bytesStoreLiteSetPacketByteLongOldWord σ I).toNat /
            2 ^ ((31 - (bytesStoreLiteSetPacketByteLongWordIndex I).toNat) * 8 + 8)) =
      (bytesStoreLiteSetPacketByteLongStoredWord σ I).toNat
    exact bytesStoreLiteSetPacketByteLongStoredWord_toNat_update
      (σ := σ) (I := I) hcanon
  change storageLocStore evm
      { slot := bytesStoreLiteSetPacketByteLongDataSlot I, offset := offFin, size := 1,
        hbound := hoffBound, type := .int uint8Int }
      (bytesStoreLiteSetPacketByteValue I) =
      some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner
        (bytesStoreLiteSetPacketByteLongDataSlot I)
        (bytesStoreLiteSetPacketByteLongStoredWord σ I))
  exact storageLocStore_oneByte_local evm (bytesStoreLiteSetPacketByteLongDataSlot I)
    (UInt256.ofNat (bytesStoreLiteSetByteValueWord I).toNat)
    (bytesStoreLiteSetPacketByteLongStoredWord σ I)
    offFin (.int uint8Int) hoffBound
    (bytesStoreLiteSetPacketByteValue I) hval htarget

theorem bytesStoreLiteSetPacketByteResolveOfLength {evm : EVM.State} {I : ExecutionEnv}
    {len : Nat}
    (hlen : readStorageBytesLength? bytesStoreLiteConfig evm
      { base := "packet", steps := [.field "data"] } = .ok len)
    (hbound : (bytesStoreLiteSetByteIndexWord I).toNat < len) :
    resolveStorageRef? bytesStoreLiteConfig
      (bytesStoreLiteSetPacketByteFrame I)
      evm (packetDataByteRef (.var "byteIndex")) =
        .ok (bytesStoreLiteSetPacketByteRef I, uint8St) := by
  have hgetIndex :
      (bytesStoreLiteSetPacketByteLocals I).get? "byteIndex" =
        some (.int (Int.ofNat (bytesStoreLiteSetByteIndexWord I).toNat)) := by
    rw [bytesStoreLiteSetPacketByteLocals]
    rw [store_get_ne (h := by decide)]
    rw [store_get_self]
  have hgetIndexElem :
      (bytesStoreLiteSetPacketByteLocals I)["byteIndex"]? =
        some (.int (Int.ofNat (bytesStoreLiteSetByteIndexWord I).toNat)) := by
    simpa [Std.HashMap.get?_eq_getElem?] using hgetIndex
  have hgetPacket :
      (bytesStoreLiteSetPacketByteLocals I).get? "packet" = none := by
    rw [bytesStoreLiteSetPacketByteLocals]
    rw [store_get_ne (h := by decide)]
    rw [store_get_ne (h := by decide)]
    simp
  have hgetPacketElem :
      (bytesStoreLiteSetPacketByteLocals I)["packet"]? = none := by
    simpa [Std.HashMap.get?_eq_getElem?] using hgetPacket
  have hlen' :
      readStorageBytesLength?
        { storage := bytesStoreLiteStorageLayout, externalABI := defaultExternalCallABI,
          selfDeployment := genSolidityConstructorDeployment [] }
        evm { base := "packet", steps := [.field "data"] } = .ok len := by
    simpa [bytesStoreLiteConfig] using hlen
  have her :
      evalStorageRef bytesStoreLiteConfig
        (bytesStoreLiteSetPacketByteFrame I)
        evm (packetDataByteRef (.var "byteIndex")) =
          .ok (bytesStoreLiteSetPacketByteRef I) := by
    simp [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, evalExpr?, packetDataByteRef,
      bytesStoreLiteSetPacketByteFrame, bytesStoreLiteSetPacketByteRef, hgetIndexElem,
      valueToKey?, EvalResult.ofOption, EvalResult.bind, bind, pure, arrayIndexInBounds?,
      storageTypeAt?, bytesStoreLiteConfig, bytesStoreLiteContract, storageDecls,
      packetStructDecl, packetStructTy, bytesSt, storageTypeStep?, hlen', hbound]
  have her' :
      evalStorageRef bytesStoreLiteConfig
        (bytesStoreLiteSetPacketByteFrame I)
        evm { base := "packet", steps := [.field "data", .aindex (.var "byteIndex")] } =
          .ok (bytesStoreLiteSetPacketByteRef I) := by
    simpa [packetDataByteRef] using her
  have herInline :
      evalStorageRef bytesStoreLiteConfig
        { contract := bytesStoreLiteContract, locals := bytesStoreLiteSetPacketByteLocals I }
        evm (packetDataByteRef (.var "byteIndex")) =
          .ok (bytesStoreLiteSetPacketByteRef I) := by
    simpa [bytesStoreLiteSetPacketByteFrame] using her
  have herInline' :
      evalStorageRef bytesStoreLiteConfig
        { contract := bytesStoreLiteContract, locals := bytesStoreLiteSetPacketByteLocals I }
        evm { base := "packet", steps := [.field "data", .aindex (.var "byteIndex")] } =
          .ok (bytesStoreLiteSetPacketByteRef I) := by
    simpa [packetDataByteRef] using herInline
  rw [resolveStorageRef?]
  simp only [packetDataByteRef, bytesStoreLiteSetPacketByteFrame, hgetPacket]
  rw [herInline']
  simp [bytesStoreLiteSetPacketByte_storageTypeAt, EvalResult.ofOption, EvalResult.bind, bind,
    pure]

theorem bytesStoreLiteSetPacketByteAssignOfLength {evm evm' : EVM.State}
    {I : ExecutionEnv} {len : Nat}
    (hlen : readStorageBytesLength? bytesStoreLiteConfig evm
      { base := "packet", steps := [.field "data"] } = .ok len)
    (hbound : (bytesStoreLiteSetByteIndexWord I).toNat < len)
    (hstore :
      (match bytesStoreLiteConfig.storage.layout (bytesStoreLiteSetPacketByteRef I) evm with
      | some loc => storageLocStore evm loc (bytesStoreLiteSetPacketByteValue I)
      | none => none) = some evm') :
    assignStorageRef? bytesStoreLiteConfig
      (bytesStoreLiteSetPacketByteFrame I)
      evm .storage (packetDataByteRef (.var "byteIndex")) (bytesStoreLiteSetPacketByteValue I) =
        .ok (bytesStoreLiteSetPacketByteFrame I, evm') := by
  rw [assignStorageRef?]
  rw [bytesStoreLiteSetPacketByteResolveOfLength (I := I) hlen hbound]
  cases hloc : bytesStoreLiteConfig.storage.layout (bytesStoreLiteSetPacketByteRef I) evm with
  | none =>
      simp [hloc] at hstore
  | some loc =>
      have hstoreLoc :
          storageLocStore evm loc
            (.int (Int.ofNat (bytesStoreLiteSetByteValueWord I).toNat)) = some evm' := by
        simpa [hloc, bytesStoreLiteSetPacketByteValue] using hstore
      have hstoreLoc' :
          storageLocStore evm loc
            (.int ((bytesStoreLiteSetByteValueWord I).toNat : Int)) = some evm' := by
        simpa using hstoreLoc
      simp [bytesStoreLiteSetPacketByteValue, hloc, EvalResult.ofOption, EvalResult.bind, bind,
        pure]
      rw [hstoreLoc']

theorem bytesStoreLiteSetPacketByteBodyReturns {evm evm' : EVM.State} {I : ExecutionEnv}
    {ret : Value}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hassign :
      assignStorageRef? bytesStoreLiteConfig
        (bytesStoreLiteSetPacketByteFrame I)
        evm .storage (packetDataByteRef (.var "byteIndex"))
          (bytesStoreLiteSetPacketByteValue I) =
          .ok (bytesStoreLiteSetPacketByteFrame I, evm'))
    (hret :
      evalExpr? bytesStoreLiteConfig
        (bytesStoreLiteSetPacketByteFrame I)
        evm' (.storage (packetDataByteRef (.var "byteIndex"))) = .ok ret) :
    ExecTransitionBody bytesStoreLiteConfig bytesStoreLiteContract evm
      (bytesStoreLiteSetPacketByteLocals I) setPacketByteTransition.body
      (.returned
        (bytesStoreLiteSetPacketByteFrame I)
        evm' (some ret)) := by
  let solm : Frame := bytesStoreLiteSetPacketByteFrame I
  have hvalue :
      evalExpr? bytesStoreLiteConfig solm evm (.var "value") =
        .ok (bytesStoreLiteSetPacketByteValue I) := by
    simp [solm, bytesStoreLiteSetPacketByteFrame, bytesStoreLiteSetPacketByteValue,
      bytesStoreLiteSetPacketByteLocals, evalExpr?, EvalResult.ofOption]
  have hassign :
      assignStorageRef? bytesStoreLiteConfig solm evm .storage
        (packetDataByteRef (.var "byteIndex")) (bytesStoreLiteSetPacketByteValue I) =
          .ok (solm, evm') := by
    simpa [solm] using hassign
  have hret :
      evalExpr? bytesStoreLiteConfig solm evm'
        (.storage (packetDataByteRef (.var "byteIndex"))) = .ok ret := by
    simpa [solm] using hret
  exact ExecFuncBody.execBlockRet <|
    ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consNormal (ExecStmt.assign hvalue hassign) <|
        ExecBlock.consReturn (ExecStmt.return hret)

theorem bytesStoreLiteSetPacketByteShortBodyReturns
    {evm : EVM.State} {σ : AccountMap} {I : ExecutionEnv} {len : UInt256} {acc : Account}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩ =
      bytesStoreLitePacketLengthHeaderWord σ I)
    (hacc : evm.accountMap.find? evm.executionEnv.codeOwner = some acc)
    (hcanon : (bytesStoreLiteSetByteValueWord I).toNat < EVM.twoPow 8)
    (hlen : len =
      UInt256.land (UInt256.div (bytesStoreLitePacketLengthHeaderWord σ I) ⟨2⟩) ⟨127⟩)
    (hshort : len.toNat < 32)
    (hbound : (bytesStoreLiteSetByteIndexWord I).toNat < len.toNat)
    (hflag : UInt256.land (bytesStoreLitePacketLengthHeaderWord σ I) ⟨1⟩ = ⟨0⟩)
    (_hvalid : UInt256.sub (UInt256.land (bytesStoreLitePacketLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStoreLitePacketLengthHeaderWord σ I) ⟨2⟩) ⟨127⟩)
          ⟨32⟩) ≠ ⟨0⟩) :
    ExecTransitionBody bytesStoreLiteConfig bytesStoreLiteContract evm
      (bytesStoreLiteSetPacketByteLocals I) setPacketByteTransition.body
      (.returned
        (bytesStoreLiteSetPacketByteFrame I)
        (Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨2⟩
          (bytesStoreLiteSetPacketByteShortStoredWord σ I))
        (some (bytesStoreLiteSetPacketByteValue I))) := by
  let evm' := Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨2⟩
    (bytesStoreLiteSetPacketByteShortStoredWord σ I)
  have hlenRead :
      readStorageBytesLength? bytesStoreLiteConfig evm
          { base := "packet", steps := [.field "data"] } =
        .ok len.toNat := by
    have hltLen : UInt256.lt len ⟨32⟩ = ⟨1⟩ := by
      exact ult_one (by
        simpa [show (⟨32⟩ : UInt256).toNat = 32 from by decide] using hshort)
    have hvalidLen : UInt256.sub ⟨0⟩ (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩ := by
      rw [hltLen]
      native_decide
    simp [readStorageBytesLength?, storageNatResultToEval, bytesStoreLiteConfig,
      bytesStoreLiteStorageLayout, solidityStorageLayout, solidityReadBytesLength?,
      solidityDecodeBytesLengthHeader, bytesStoreLiteLayout, hload, hflag, ← hlen,
      hvalidLen]
  have hpacked : checkBytesPacked ⟨2⟩ evm = true :=
    checkBytesPacked_of_storageLoad_land_one_zero hload hflag
  have hidx31 : (bytesStoreLiteSetByteIndexWord I).toNat < 31 :=
    bytesStoreLiteSetByteIndex_lt31_of_short_bound (I := I) (len := len) hshort hbound
  have hlayout :
      bytesStoreLiteConfig.storage.layout (bytesStoreLiteSetPacketByteRef I) evm =
        some (uint8Loc ⟨2⟩ ⟨31 - (bytesStoreLiteSetByteIndexWord I).toNat, by omega⟩) :=
    bytesStoreLiteSetPacketByteLayoutShort (evm := evm) (I := I) hpacked hidx31
  have hstore :
      (match bytesStoreLiteConfig.storage.layout (bytesStoreLiteSetPacketByteRef I) evm with
      | some loc => storageLocStore evm loc (bytesStoreLiteSetPacketByteValue I)
      | none => none) = some evm' := by
    rw [hlayout]
    simpa [evm'] using
      bytesStoreLiteSetPacketByteStorageLocStoreShort
        (evm := evm) (σ := σ) (I := I) (len := len)
        hload hcanon hshort hbound
  have hassign :
      assignStorageRef? bytesStoreLiteConfig
        (bytesStoreLiteSetPacketByteFrame I)
        evm .storage (packetDataByteRef (.var "byteIndex"))
          (bytesStoreLiteSetPacketByteValue I) =
          .ok (bytesStoreLiteSetPacketByteFrame I, evm') :=
    bytesStoreLiteSetPacketByteAssignOfLength (evm := evm) (evm' := evm') (I := I)
      hlenRead hbound hstore
  have hloadPost :
      Solm.EVM.storageLoad evm' evm'.executionEnv.codeOwner ⟨2⟩ =
        bytesStoreLiteSetPacketByteShortStoredWord σ I := by
    have hloadPostOwner :
        Solm.EVM.storageLoad evm' evm.executionEnv.codeOwner ⟨2⟩ =
          bytesStoreLiteSetPacketByteShortStoredWord σ I := by
      simpa [evm'] using
        storageLoad_storageStore_same_present evm evm.executionEnv.codeOwner hacc ⟨2⟩
          (bytesStoreLiteSetPacketByteShortStoredWord σ I)
    simpa [evm', storageStore_executionEnv] using hloadPostOwner
  have hflagPost :
      UInt256.land (bytesStoreLiteSetPacketByteShortStoredWord σ I) ⟨1⟩ = ⟨0⟩ := by
    rw [bytesStoreLiteSetPacketByteShortStoredWord_flag_eq
      (σ := σ) (I := I) (len := len) hshort hbound, hflag]
  have hlenPost :
      readStorageBytesLength? bytesStoreLiteConfig evm'
          { base := "packet", steps := [.field "data"] } =
        .ok len.toNat := by
    have hltLen : UInt256.lt len ⟨32⟩ = ⟨1⟩ := by
      exact ult_one (by
        simpa [show (⟨32⟩ : UInt256).toNat = 32 from by decide] using hshort)
    have hvalidLen : UInt256.sub ⟨0⟩ (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩ := by
      rw [hltLen]
      native_decide
    have hlenPostWord :
        UInt256.land (UInt256.div (bytesStoreLiteSetPacketByteShortStoredWord σ I) ⟨2⟩)
            ⟨127⟩ = len := by
      rw [bytesStoreLiteSetPacketByteShortStoredWord_shortLen_eq
        (σ := σ) (I := I) (len := len) hshort hbound]
      exact hlen.symm
    simp [readStorageBytesLength?, storageNatResultToEval, bytesStoreLiteConfig,
      bytesStoreLiteStorageLayout, solidityStorageLayout, solidityReadBytesLength?,
      solidityDecodeBytesLengthHeader, bytesStoreLiteLayout, hloadPost, hflagPost,
      hlenPostWord, hvalidLen]
  have hpackedPost : checkBytesPacked ⟨2⟩ evm' = true :=
    checkBytesPacked_of_storageLoad_land_one_zero hloadPost hflagPost
  have hlayoutPost :
      bytesStoreLiteConfig.storage.layout (bytesStoreLiteSetPacketByteRef I) evm' =
        some (uint8Loc ⟨2⟩ ⟨31 - (bytesStoreLiteSetByteIndexWord I).toNat, by omega⟩) :=
    bytesStoreLiteSetPacketByteLayoutShort (evm := evm') (I := I) hpackedPost hidx31
  have hidxLe : (bytesStoreLiteSetByteIndexWord I).toNat ≤ 31 := by
    omega
  have hret :
      evalExpr? bytesStoreLiteConfig
        (bytesStoreLiteSetPacketByteFrame I)
        evm' (.storage (packetDataByteRef (.var "byteIndex"))) =
          .ok (bytesStoreLiteSetPacketByteValue I) := by
    rw [evalExpr?]
    rw [bytesStoreLiteSetPacketByteResolveOfLength (evm := evm') (I := I) hlenPost hbound]
    simp only [bind, EvalResult.bind]
    rw [Solm.readStorage?.eq_def]
    rw [hlayoutPost]
    simp [uint8St]
    rw [storageLocLoad_uint8Loc_byteAt
      (slot := ⟨2⟩) (idx := bytesStoreLiteSetByteIndexWord I)
      (off := ⟨31 - (bytesStoreLiteSetByteIndexWord I).toNat, by omega⟩)
      (hoff := by rfl) (hidx := hidxLe)]
    rw [hloadPost]
    rw [bytesStoreLiteSetPacketByteShortStoredWord_byteAt
      (σ := σ) (I := I) (len := len) hcanon hshort hbound]
    simp [bytesStoreLiteSetPacketByteValue]
  simpa [evm'] using
    bytesStoreLiteSetPacketByteBodyReturns (evm := evm) (evm' := evm') (I := I)
      hwv hassign hret

theorem bytesStoreLiteSetPacketByteLongBodyReturns
    {evm : EVM.State} {σ : AccountMap} {I : ExecutionEnv} {len : UInt256} {acc : Account}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hloadHeader : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩ =
      bytesStoreLitePacketLengthHeaderWord σ I)
    (hloadData : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (bytesStoreLiteSetPacketByteLongDataSlot I) =
      bytesStoreLiteSetPacketByteLongOldWord σ I)
    (hacc : evm.accountMap.find? evm.executionEnv.codeOwner = some acc)
    (hcanon : (bytesStoreLiteSetByteValueWord I).toNat < EVM.twoPow 8)
    (hlen : len = UInt256.div (bytesStoreLitePacketLengthHeaderWord σ I) ⟨2⟩)
    (hbound : (bytesStoreLiteSetByteIndexWord I).toNat < len.toNat)
    (hflag : UInt256.land (bytesStoreLitePacketLengthHeaderWord σ I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (bytesStoreLitePacketLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStoreLitePacketLengthHeaderWord σ I) ⟨2⟩) ⟨32⟩) ≠ ⟨0⟩) :
    ExecTransitionBody bytesStoreLiteConfig bytesStoreLiteContract evm
      (bytesStoreLiteSetPacketByteLocals I) setPacketByteTransition.body
      (.returned
        (bytesStoreLiteSetPacketByteFrame I)
        (Solm.EVM.storageStore evm evm.executionEnv.codeOwner
          (bytesStoreLiteSetPacketByteLongDataSlot I)
          (bytesStoreLiteSetPacketByteLongStoredWord σ I))
        (some (bytesStoreLiteSetPacketByteValue I))) := by
  let evm' := Solm.EVM.storageStore evm evm.executionEnv.codeOwner
    (bytesStoreLiteSetPacketByteLongDataSlot I)
    (bytesStoreLiteSetPacketByteLongStoredWord σ I)
  have hvalidLen :
      UInt256.sub (UInt256.land (bytesStoreLitePacketLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩ := by
    simpa [hlen] using hvalid
  have hlenRead :
      readStorageBytesLength? bytesStoreLiteConfig evm
          { base := "packet", steps := [.field "data"] } =
        .ok len.toNat := by
    simp [readStorageBytesLength?, storageNatResultToEval, bytesStoreLiteConfig,
      bytesStoreLiteStorageLayout, solidityStorageLayout, solidityReadBytesLength?,
      solidityDecodeBytesLengthHeader, bytesStoreLiteLayout, hloadHeader, hflag, ← hlen,
      hvalidLen]
  have hpacked : checkBytesPacked ⟨2⟩ evm = false :=
    checkBytesPacked_of_storageLoad_land_one_ne_zero hloadHeader hflag
  have hlayout :
      bytesStoreLiteConfig.storage.layout (bytesStoreLiteSetPacketByteRef I) evm =
        some (uint8Loc (bytesStoreLiteSetPacketByteLongDataSlot I)
          ⟨31 - (bytesStoreLiteSetPacketByteLongWordIndex I).toNat, by
            have hidx := bytesStoreLiteSetPacketByteLongWordIndex_lt32 I
            omega⟩) :=
    bytesStoreLiteSetPacketByteLayoutLong (evm := evm) (I := I) hpacked
  have hstore :
      (match bytesStoreLiteConfig.storage.layout (bytesStoreLiteSetPacketByteRef I) evm with
      | some loc => storageLocStore evm loc (bytesStoreLiteSetPacketByteValue I)
      | none => none) = some evm' := by
    rw [hlayout]
    simpa [evm'] using
      bytesStoreLiteSetPacketByteStorageLocStoreLong
        (evm := evm) (σ := σ) (I := I) hloadData hcanon
  have hassign :
      assignStorageRef? bytesStoreLiteConfig
        (bytesStoreLiteSetPacketByteFrame I)
        evm .storage (packetDataByteRef (.var "byteIndex"))
          (bytesStoreLiteSetPacketByteValue I) =
          .ok (bytesStoreLiteSetPacketByteFrame I, evm') :=
    bytesStoreLiteSetPacketByteAssignOfLength (evm := evm) (evm' := evm') (I := I)
      hlenRead hbound hstore
  have hne : (⟨2⟩ : UInt256) ≠ bytesStoreLiteSetPacketByteLongDataSlot I := by
    exact (bytesStoreLitePacketDataSlot_ne_header (bytesStoreLiteSetByteIndexWord I)).symm
  have hloadHeaderPost :
      Solm.EVM.storageLoad evm' evm'.executionEnv.codeOwner ⟨2⟩ =
        bytesStoreLitePacketLengthHeaderWord σ I := by
    simpa [evm', storageStore_executionEnv] using
      (by
        rw [storageLoad_storageStore_ne evm evm.executionEnv.codeOwner hne]
        exact hloadHeader)
  have hlenPost :
      readStorageBytesLength? bytesStoreLiteConfig evm'
          { base := "packet", steps := [.field "data"] } =
        .ok len.toNat := by
    simp [readStorageBytesLength?, storageNatResultToEval, bytesStoreLiteConfig,
      bytesStoreLiteStorageLayout, solidityStorageLayout, solidityReadBytesLength?,
      solidityDecodeBytesLengthHeader, bytesStoreLiteLayout, hloadHeaderPost, hflag, ← hlen,
      hvalidLen]
  have hpackedPost : checkBytesPacked ⟨2⟩ evm' = false :=
    checkBytesPacked_of_storageLoad_land_one_ne_zero hloadHeaderPost hflag
  have hlayoutPost :
      bytesStoreLiteConfig.storage.layout (bytesStoreLiteSetPacketByteRef I) evm' =
        some (uint8Loc (bytesStoreLiteSetPacketByteLongDataSlot I)
          ⟨31 - (bytesStoreLiteSetPacketByteLongWordIndex I).toNat, by
            have hidx := bytesStoreLiteSetPacketByteLongWordIndex_lt32 I
            omega⟩) :=
    bytesStoreLiteSetPacketByteLayoutLong (evm := evm') (I := I) hpackedPost
  have hloadDataPost :
      Solm.EVM.storageLoad evm' evm'.executionEnv.codeOwner
          (bytesStoreLiteSetPacketByteLongDataSlot I) =
        bytesStoreLiteSetPacketByteLongStoredWord σ I := by
    simpa [evm', storageStore_executionEnv] using
      storageLoad_storageStore_same_present evm evm.executionEnv.codeOwner hacc
        (bytesStoreLiteSetPacketByteLongDataSlot I)
        (bytesStoreLiteSetPacketByteLongStoredWord σ I)
  have hret :
      evalExpr? bytesStoreLiteConfig
        (bytesStoreLiteSetPacketByteFrame I)
        evm' (.storage (packetDataByteRef (.var "byteIndex"))) =
          .ok (bytesStoreLiteSetPacketByteValue I) := by
    rw [evalExpr?]
    rw [bytesStoreLiteSetPacketByteResolveOfLength (evm := evm') (I := I) hlenPost hbound]
    simp only [bind, EvalResult.bind]
    rw [Solm.readStorage?.eq_def]
    rw [hlayoutPost]
    simp [uint8St]
    rw [storageLocLoad_uint8Loc_byteAt
      (evm := evm') (slot := bytesStoreLiteSetPacketByteLongDataSlot I)
      (idx := bytesStoreLiteSetPacketByteLongWordIndex I)
      (off := ⟨31 - (bytesStoreLiteSetPacketByteLongWordIndex I).toNat, by
        have hidx := bytesStoreLiteSetPacketByteLongWordIndex_lt32 I
        omega⟩)
      (by rfl)
      (by
        have hidx := bytesStoreLiteSetPacketByteLongWordIndex_lt32 I
        omega)]
    rw [hloadDataPost]
    rw [bytesStoreLiteSetPacketByteLongStoredWord_byteAt (σ := σ) (I := I) hcanon]
    simp [bytesStoreLiteSetPacketByteValue]
  simpa [evm'] using
    bytesStoreLiteSetPacketByteBodyReturns (evm := evm) (evm' := evm') (I := I)
      hwv hassign hret

theorem bytesStoreLiteSetPacketByteResolveRevertsOfLength {evm : EVM.State} {I : ExecutionEnv}
    {len : Nat}
    (hlen : readStorageBytesLength? bytesStoreLiteConfig evm
      { base := "packet", steps := [.field "data"] } = .ok len)
    (hbound : ¬ (bytesStoreLiteSetByteIndexWord I).toNat < len) :
    resolveStorageRef? bytesStoreLiteConfig
      { contract := bytesStoreLiteContract, locals := bytesStoreLiteSetPacketByteLocals I }
      evm (packetDataByteRef (.var "byteIndex")) = .revert := by
  have hgetIndex :
      (bytesStoreLiteSetPacketByteLocals I).get? "byteIndex" =
        some (.int (Int.ofNat (bytesStoreLiteSetByteIndexWord I).toNat)) := by
    rw [bytesStoreLiteSetPacketByteLocals]
    rw [store_get_ne (h := by decide)]
    rw [store_get_self]
  have hgetIndexElem :
      (bytesStoreLiteSetPacketByteLocals I)["byteIndex"]? =
        some (.int (Int.ofNat (bytesStoreLiteSetByteIndexWord I).toNat)) := by
    simpa [Std.HashMap.get?_eq_getElem?] using hgetIndex
  have hgetPacket :
      (bytesStoreLiteSetPacketByteLocals I).get? "packet" = none := by
    rw [bytesStoreLiteSetPacketByteLocals]
    rw [store_get_ne (h := by decide)]
    rw [store_get_ne (h := by decide)]
    simp
  have hgetPacketElem :
      (bytesStoreLiteSetPacketByteLocals I)["packet"]? = none := by
    simpa [Std.HashMap.get?_eq_getElem?] using hgetPacket
  have hlen' :
      readStorageBytesLength?
        { storage := bytesStoreLiteStorageLayout, externalABI := defaultExternalCallABI,
          selfDeployment := genSolidityConstructorDeployment [] }
        evm { base := "packet", steps := [.field "data"] } = .ok len := by
    simpa [bytesStoreLiteConfig] using hlen
  have her :
      evalStorageRef bytesStoreLiteConfig
        { contract := bytesStoreLiteContract, locals := bytesStoreLiteSetPacketByteLocals I }
        evm (packetDataByteRef (.var "byteIndex")) = .revert := by
    simp [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, evalExpr?, packetDataByteRef,
      hgetIndexElem, valueToKey?, EvalResult.ofOption, EvalResult.bind, bind, pure,
      arrayIndexInBounds?, storageTypeAt?, bytesStoreLiteConfig, bytesStoreLiteContract,
      storageDecls, packetStructDecl, packetStructTy, bytesSt, storageTypeStep?, hlen', hbound]
  rw [resolveStorageRef?]
  simp only [packetDataByteRef, hgetPacket]
  change (match evalStorageRef bytesStoreLiteConfig
      { contract := bytesStoreLiteContract, locals := bytesStoreLiteSetPacketByteLocals I }
      evm (packetDataByteRef (.var "byteIndex")) with
    | .ok er => do
        let ty ← EvalResult.ofOption EvalError.storageError
          (storageTypeAt? bytesStoreLiteContract.storage er)
        pure (er, ty)
    | .revert => .revert
    | .error e => .error e) = .revert
  rw [her]

theorem bytesStoreLiteSetPacketByteBodyBoundsRevertsOfLength
    {evm : EVM.State} {I : ExecutionEnv} {len : Nat}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hlen : readStorageBytesLength? bytesStoreLiteConfig evm
      { base := "packet", steps := [.field "data"] } = .ok len)
    (hbound : ¬ (bytesStoreLiteSetByteIndexWord I).toNat < len) :
    ExecTransitionBody bytesStoreLiteConfig bytesStoreLiteContract evm
      (bytesStoreLiteSetPacketByteLocals I) setPacketByteTransition.body .reverted := by
  let solm : Frame :=
    { contract := bytesStoreLiteContract, locals := bytesStoreLiteSetPacketByteLocals I }
  have hvalue :
      evalExpr? bytesStoreLiteConfig solm evm (.var "value") =
        .ok (bytesStoreLiteSetPacketByteValue I) := by
    simp [solm, bytesStoreLiteSetPacketByteValue, bytesStoreLiteSetPacketByteLocals, evalExpr?,
      EvalResult.ofOption]
  have hassign :
      assignStorageRef? bytesStoreLiteConfig solm evm .storage
        (packetDataByteRef (.var "byteIndex")) (bytesStoreLiteSetPacketByteValue I) = .revert := by
    rw [assignStorageRef?]
    rw [bytesStoreLiteSetPacketByteResolveRevertsOfLength (I := I) hlen hbound]
    rfl
  exact ExecFuncBody.execBlockRevert <|
    ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consRevert (ExecStmt.assignStoreRevert hvalue hassign)

theorem bytesStoreLiteSetPacketByteResolveRevertsOfLengthRead
    {evm : EVM.State} {I : ExecutionEnv}
    (hlen : readStorageBytesLength? bytesStoreLiteConfig evm
      { base := "packet", steps := [.field "data"] } = .revert) :
    resolveStorageRef? bytesStoreLiteConfig
      { contract := bytesStoreLiteContract, locals := bytesStoreLiteSetPacketByteLocals I }
      evm (packetDataByteRef (.var "byteIndex")) = .revert := by
  have hgetIndex :
      (bytesStoreLiteSetPacketByteLocals I).get? "byteIndex" =
        some (.int (Int.ofNat (bytesStoreLiteSetByteIndexWord I).toNat)) := by
    rw [bytesStoreLiteSetPacketByteLocals]
    rw [store_get_ne (h := by decide)]
    rw [store_get_self]
  have hgetIndexElem :
      (bytesStoreLiteSetPacketByteLocals I)["byteIndex"]? =
        some (.int (Int.ofNat (bytesStoreLiteSetByteIndexWord I).toNat)) := by
    simpa [Std.HashMap.get?_eq_getElem?] using hgetIndex
  have hgetPacket :
      (bytesStoreLiteSetPacketByteLocals I).get? "packet" = none := by
    rw [bytesStoreLiteSetPacketByteLocals]
    rw [store_get_ne (h := by decide)]
    rw [store_get_ne (h := by decide)]
    simp
  have hgetPacketElem :
      (bytesStoreLiteSetPacketByteLocals I)["packet"]? = none := by
    simpa [Std.HashMap.get?_eq_getElem?] using hgetPacket
  have hlen' :
      readStorageBytesLength?
        { storage := bytesStoreLiteStorageLayout, externalABI := defaultExternalCallABI,
          selfDeployment := genSolidityConstructorDeployment [] }
        evm { base := "packet", steps := [.field "data"] } = .revert := by
    simpa [bytesStoreLiteConfig] using hlen
  have her :
      evalStorageRef bytesStoreLiteConfig
        { contract := bytesStoreLiteContract, locals := bytesStoreLiteSetPacketByteLocals I }
        evm (packetDataByteRef (.var "byteIndex")) = .revert := by
    simp [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, evalExpr?, packetDataByteRef,
      hgetIndexElem, valueToKey?, EvalResult.ofOption, EvalResult.bind, bind, pure,
      arrayIndexInBounds?, storageTypeAt?, bytesStoreLiteConfig, bytesStoreLiteContract,
      storageDecls, packetStructDecl, packetStructTy, bytesSt, storageTypeStep?, hlen']
  rw [resolveStorageRef?]
  simp only [packetDataByteRef, hgetPacket]
  change (match evalStorageRef bytesStoreLiteConfig
      { contract := bytesStoreLiteContract, locals := bytesStoreLiteSetPacketByteLocals I }
      evm (packetDataByteRef (.var "byteIndex")) with
    | .ok er => do
        let ty ← EvalResult.ofOption EvalError.storageError
          (storageTypeAt? bytesStoreLiteContract.storage er)
        pure (er, ty)
    | .revert => .revert
    | .error e => .error e) = .revert
  rw [her]

theorem bytesStoreLiteSetPacketByteBodyRevertsOfLengthRead
    {evm : EVM.State} {I : ExecutionEnv}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hlen : readStorageBytesLength? bytesStoreLiteConfig evm
      { base := "packet", steps := [.field "data"] } = .revert) :
    ExecTransitionBody bytesStoreLiteConfig bytesStoreLiteContract evm
      (bytesStoreLiteSetPacketByteLocals I) setPacketByteTransition.body .reverted := by
  let solm : Frame :=
    { contract := bytesStoreLiteContract, locals := bytesStoreLiteSetPacketByteLocals I }
  have hvalue :
      evalExpr? bytesStoreLiteConfig solm evm (.var "value") =
        .ok (bytesStoreLiteSetPacketByteValue I) := by
    simp [solm, bytesStoreLiteSetPacketByteValue, bytesStoreLiteSetPacketByteLocals, evalExpr?,
      EvalResult.ofOption]
  have hassign :
      assignStorageRef? bytesStoreLiteConfig solm evm .storage
        (packetDataByteRef (.var "byteIndex")) (bytesStoreLiteSetPacketByteValue I) = .revert := by
    rw [assignStorageRef?]
    rw [bytesStoreLiteSetPacketByteResolveRevertsOfLengthRead (I := I) hlen]
    rfl
  exact ExecFuncBody.execBlockRevert <|
    ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consRevert (ExecStmt.assignStoreRevert hvalue hassign)

theorem bytesStoreLiteDecode_setPacketByte_locals {I : ExecutionEnv}
    (hsz68 : 68 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (bytesStoreLiteSetByteValueWord I).toNat < EVM.twoPow 8) :
    decodeCalldata (setPacketByteTransition.params.map Param.name)
      (transitionSignature setPacketByteTransition).paramTypes I.calldata =
        some (bytesStoreLiteSetPacketByteLocals I) := by
  simpa [bytesStoreLiteSetPacketByteLocals] using
    bytesStoreLiteDecode_setPacketByte (I := I) hsz68 hhi hcanon

theorem bytesStoreLiteSetPacketByteUint8CanonEqGuard {w : UInt256}
    (h : UInt256.land w ⟨255⟩ = w) :
    UInt256.eq w (UInt256.land w ⟨255⟩) = ⟨1⟩ := by
  rw [h]
  exact u256_eq_refl w

theorem bytesStoreLiteSetPacketByteUint8NoncanonEqGuard {w : UInt256}
    (h : UInt256.land w ⟨255⟩ ≠ w) :
    UInt256.eq w (UInt256.land w ⟨255⟩) = ⟨0⟩ := by
  exact u256_eq_of_ne (by
    intro hw
    exact h hw.symm)

theorem bytesStoreLiteSetPacketByteLand255_toNat (w : UInt256) :
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

theorem bytesStoreLiteSetPacketByteLand255_eq_self_of_uint8 {w : UInt256}
    (h : w.toNat < EVM.twoPow 8) :
    UInt256.land w ⟨255⟩ = w := by
  apply u256_inj
  rw [bytesStoreLiteSetPacketByteLand255_toNat]
  exact Nat.mod_eq_of_lt h

theorem bytesStoreLiteSetPacketByteLand255_ne_self_of_not_uint8 {w : UInt256}
    (h : ¬ w.toNat < EVM.twoPow 8) :
    UInt256.land w ⟨255⟩ ≠ w := by
  intro hland
  apply h
  have hnat : (UInt256.land w ⟨255⟩).toNat = w.toNat := by
    rw [hland]
  rw [bytesStoreLiteSetPacketByteLand255_toNat] at hnat
  rw [← hnat]
  exact Nat.mod_lt _ (by decide : 0 < EVM.twoPow 8)

theorem bytesStoreLiteX_setPacketByteDecodeValid {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨282⟩ [bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hsz68 : 68 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hsize : I.calldata.size < UInt256.size)
    (hcanon : UInt256.land (bytesStoreLiteSetByteValueWord I) ⟨255⟩ =
      bytesStoreLiteSetByteValueWord I) :
    ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨601⟩
      [bytesStoreLiteSetByteValueWord I, bytesStoreLiteSetByteIndexWord I, ⟨301⟩,
        bytesStoreLiteSelWord I]
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
      bytesStoreLiteSetByteIndexWord I from rfl,
    show (⟨4⟩ + ⟨32⟩ : UInt256) = ⟨36⟩ from by native_decide] at rd1946
  have rd1950 := evm_run rd1946 with [
    jumpdest, dup1, calldataload]
  rw [show (⟨36⟩ : UInt256).toNat = 36 from by decide,
    show uInt256OfByteArray (I.calldata.readBytes 36 32) =
      bytesStoreLiteSetByteValueWord I from rfl] at rd1950
  have rd2000 := evm_run rd1950 with [
    push1 ⟨255⟩, dup2, and, dup2, eq,
    push2 ⟨1962⟩,
    jumpiT (by rw [bytesStoreLiteSetPacketByteUint8CanonEqGuard hcanon]; decide)
      (by native_decide),
    jumpdest, swap2, swap1, pop, jump (by native_decide)]
  exact ⟨_, _, evm_run rd2000 with [
    jumpdest, swap1, pop, swap3, pop, swap3, swap1, pop, jump (by native_decide),
    jumpdest, push2 ⟨601⟩, jump (by native_decide)]⟩

theorem bytesStoreLiteX_setPacketByteDecodeShort {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨282⟩ [bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 68)
    (hsize : I.calldata.size < UInt256.size) :
    RDrev bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I) := by
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

theorem bytesStoreLiteX_setPacketByteDecodeHuge {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨282⟩ [bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size) :
    RDrev bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I) := by
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

theorem bytesStoreLiteX_setPacketByteDecodeNoncanonValue {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨282⟩ [bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hsz68 : 68 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hsize : I.calldata.size < UInt256.size)
    (hnc : UInt256.land (bytesStoreLiteSetByteValueWord I) ⟨255⟩ ≠
      bytesStoreLiteSetByteValueWord I) :
    RDrev bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I) := by
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
      bytesStoreLiteSetByteIndexWord I from rfl,
    show (⟨4⟩ + ⟨32⟩ : UInt256) = ⟨36⟩ from by native_decide] at rd1946
  have rd1950 := evm_run rd1946 with [
    jumpdest, dup1, calldataload]
  rw [show (⟨36⟩ : UInt256).toNat = 36 from by decide,
    show uInt256OfByteArray (I.calldata.readBytes 36 32) =
      bytesStoreLiteSetByteValueWord I from rfl] at rd1950
  exact evm_run rd1950 with [
    push1 ⟨255⟩, dup2, and, dup2, eq,
    push2 ⟨1962⟩,
    jumpiNT (by rw [bytesStoreLiteSetPacketByteUint8NoncanonEqGuard hnc]),
    raw revertStub (by native_decide) (by native_decide) (by native_decide) (by evm_ov)]

theorem bytesStoreLiteX_setPacketByteReachLengthDecoder {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨601⟩
      [bytesStoreLiteSetByteValueWord I, bytesStoreLiteSetByteIndexWord I, ⟨301⟩,
        bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2246⟩
      [bytesStoreLitePacketLengthHeaderWord σ I, ⟨622⟩,
        bytesStoreLiteSetByteIndexWord I, ⟨2⟩,
        UInt256.shiftLeft (bytesStoreLiteSetByteValueWord I) ⟨248⟩, ⟨0⟩,
        bytesStoreLiteSetByteValueWord I, bytesStoreLiteSetByteIndexWord I, ⟨301⟩,
        bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd601⟩ := hreach
  have rd613 := evm_run rd601 with [
    jumpdest, push0, dup2, push1 ⟨248⟩, shl, push1 ⟨2⟩, push0, add, dup5, dup2]
  obtain ⟨_, _, rd614₀⟩ := rd613.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd614⟩ :
      ∃ k C, RD bytesStoreLiteBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨614⟩
        [bytesStoreLitePacketLengthHeaderWord σ I, bytesStoreLiteSetByteIndexWord I, ⟨2⟩,
          UInt256.shiftLeft (bytesStoreLiteSetByteValueWord I) ⟨248⟩, ⟨0⟩,
          bytesStoreLiteSetByteValueWord I, bytesStoreLiteSetByteIndexWord I, ⟨301⟩,
          bytesStoreLiteSelWord I]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by
      simpa [bytesStoreLitePacketLengthHeaderWord, initState] using rd614₀⟩
  exact ⟨_, _, evm_run rd614 with [
    push2 ⟨622⟩, swap1, push2 ⟨2246⟩, jump (by native_decide)]⟩

theorem bytesStoreLiteX_setPacketByteOobAfterLength {cA gh bl σ σ₀ A I} {g : Sat256}
    {len : UInt256}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨622⟩
      [len, bytesStoreLiteSetByteIndexWord I, ⟨2⟩,
        UInt256.shiftLeft (bytesStoreLiteSetByteValueWord I) ⟨248⟩, ⟨0⟩,
        bytesStoreLiteSetByteValueWord I, bytesStoreLiteSetByteIndexWord I, ⟨301⟩,
        bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hbound : ¬ (bytesStoreLiteSetByteIndexWord I).toNat < len.toNat) :
    RDrev bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd622⟩ := hreach
  have hlt : UInt256.lt (bytesStoreLiteSetByteIndexWord I) len = ⟨0⟩ :=
    ult_zero (by omega)
  have rd2579 := evm_run rd622 with [
    jumpdest, dup2, lt, push2 ⟨636⟩,
    jumpiNT (by simpa using hlt),
    push2 ⟨636⟩, push2 ⟨2579⟩, jump (by native_decide)]
  exact bytesStoreLiteX_panic32Mem ⟨_, _, rd2579⟩
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem bytesStoreLiteX_setPacketByteOobLong {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨601⟩
      [bytesStoreLiteSetByteValueWord I, bytesStoreLiteSetByteIndexWord I, ⟨301⟩,
        bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hflag : UInt256.land (bytesStoreLitePacketLengthHeaderWord σ I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (bytesStoreLitePacketLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStoreLitePacketLengthHeaderWord σ I) ⟨2⟩) ⟨32⟩) ≠ ⟨0⟩)
    (hbound :
      ¬ (bytesStoreLiteSetByteIndexWord I).toNat <
        (UInt256.div (bytesStoreLitePacketLengthHeaderWord σ I) ⟨2⟩).toNat) :
    RDrev bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hdec := bytesStoreLiteX_setPacketByteReachLengthDecoder hreach
  have hlen := bytesStoreLiteX_bytesLengthDecoderLongValidMem
    (A := A) (I := I) (g := g) hdec hflag hvalid (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  exact bytesStoreLiteX_setPacketByteOobAfterLength (g := g) hlen hbound

theorem bytesStoreLiteX_setPacketByteOobShort {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨601⟩
      [bytesStoreLiteSetByteValueWord I, bytesStoreLiteSetByteIndexWord I, ⟨301⟩,
        bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hflag : UInt256.land (bytesStoreLitePacketLengthHeaderWord σ I) ⟨1⟩ = ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (bytesStoreLitePacketLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStoreLitePacketLengthHeaderWord σ I) ⟨2⟩) ⟨127⟩)
          ⟨32⟩) ≠ ⟨0⟩)
    (hbound :
      ¬ (bytesStoreLiteSetByteIndexWord I).toNat <
        (UInt256.land (UInt256.div (bytesStoreLitePacketLengthHeaderWord σ I) ⟨2⟩) ⟨127⟩).toNat) :
    RDrev bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hdec := bytesStoreLiteX_setPacketByteReachLengthDecoder hreach
  have hlen := bytesStoreLiteX_bytesLengthDecoderShortValidMem
    (A := A) (I := I) (g := g) hdec hflag hvalid (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  exact bytesStoreLiteX_setPacketByteOobAfterLength (g := g) hlen hbound

theorem bytesStoreLiteX_setPacketByteLongMalformed {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨601⟩
      [bytesStoreLiteSetByteValueWord I, bytesStoreLiteSetByteIndexWord I, ⟨301⟩,
        bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hflag : UInt256.land (bytesStoreLitePacketLengthHeaderWord σ I) ⟨1⟩ ≠ ⟨0⟩)
    (hbad : UInt256.sub (UInt256.land (bytesStoreLitePacketLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStoreLitePacketLengthHeaderWord σ I) ⟨2⟩) ⟨32⟩) = ⟨0⟩) :
    RDrev bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hdec := bytesStoreLiteX_setPacketByteReachLengthDecoder (g := g) hreach
  exact bytesStoreLiteX_bytesLengthDecoderLongMalformedMem
    hdec hflag hbad (by simp only [List.length_cons, List.length_nil]; omega)

theorem bytesStoreLiteX_setPacketByteShortMalformed {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨601⟩
      [bytesStoreLiteSetByteValueWord I, bytesStoreLiteSetByteIndexWord I, ⟨301⟩,
        bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hflag : UInt256.land (bytesStoreLitePacketLengthHeaderWord σ I) ⟨1⟩ = ⟨0⟩)
    (hbad : UInt256.sub (UInt256.land (bytesStoreLitePacketLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStoreLitePacketLengthHeaderWord σ I) ⟨2⟩) ⟨127⟩)
          ⟨32⟩) = ⟨0⟩) :
    RDrev bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hdec := bytesStoreLiteX_setPacketByteReachLengthDecoder (g := g) hreach
  exact bytesStoreLiteX_bytesLengthDecoderShortMalformedMem
    hdec hflag hbad (by simp only [List.length_cons, List.length_nil]; omega)

theorem bytesStoreLiteX_setPacketByteShortReachStoreCommon {cA gh bl σ σ₀ A I}
    {g : Sat256} {len : UInt256}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨622⟩
      [len, bytesStoreLiteSetByteIndexWord I, ⟨2⟩,
        UInt256.shiftLeft (bytesStoreLiteSetByteValueWord I) ⟨248⟩, ⟨0⟩,
        bytesStoreLiteSetByteValueWord I, bytesStoreLiteSetByteIndexWord I, ⟨301⟩,
        bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hbound : (bytesStoreLiteSetByteIndexWord I).toNat < len.toNat)
    (hflag : UInt256.land (bytesStoreLitePacketLengthHeaderWord σ I) ⟨1⟩ = ⟨0⟩) :
    ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨665⟩
      [bytesStoreLiteSetByteIndexWord I, ⟨2⟩,
        UInt256.shiftLeft (bytesStoreLiteSetByteValueWord I) ⟨248⟩, ⟨0⟩,
        bytesStoreLiteSetByteValueWord I, bytesStoreLiteSetByteIndexWord I, ⟨301⟩,
        bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd622⟩ := hreach
  have hlt : UInt256.lt (bytesStoreLiteSetByteIndexWord I) len = ⟨1⟩ :=
    ult_one hbound
  have rd636 := evm_run rd622 with [
    jumpdest, dup2, lt, push2 ⟨636⟩,
    jumpiT (by rw [hlt]; decide) (by native_decide)]
  have rd638 := evm_run rd636 with [jumpdest, dup2]
  obtain ⟨_, _, rd639₀⟩ := rd638.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd639⟩ :
      ∃ k C, RD bytesStoreLiteBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨639⟩
        [bytesStoreLitePacketLengthHeaderWord σ I, bytesStoreLiteSetByteIndexWord I, ⟨2⟩,
          UInt256.shiftLeft (bytesStoreLiteSetByteValueWord I) ⟨248⟩, ⟨0⟩,
          bytesStoreLiteSetByteValueWord I, bytesStoreLiteSetByteIndexWord I, ⟨301⟩,
          bytesStoreLiteSelWord I]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by
      simpa [bytesStoreLitePacketLengthHeaderWord, initState] using rd639₀⟩
  have rd665 := evm_run rd639 with [
    push1 ⟨1⟩, and, iszero, push2 ⟨665⟩,
    jumpiT (by
      rw [u256_land_comm, hflag]
      decide)
      (by native_decide)]
  exact ⟨_, _, rd665⟩

theorem bytesStoreLiteX_setPacketByteLongReachStoreCommon {cA gh bl σ σ₀ A I}
    {g : Sat256} {len : UInt256}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨622⟩
      [len, bytesStoreLiteSetByteIndexWord I, ⟨2⟩,
        UInt256.shiftLeft (bytesStoreLiteSetByteValueWord I) ⟨248⟩, ⟨0⟩,
        bytesStoreLiteSetByteValueWord I, bytesStoreLiteSetByteIndexWord I, ⟨301⟩,
        bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hbound : (bytesStoreLiteSetByteIndexWord I).toNat < len.toNat)
    (hflag : UInt256.land (bytesStoreLitePacketLengthHeaderWord σ I) ⟨1⟩ ≠ ⟨0⟩) :
    ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨665⟩
      [bytesStoreLiteSetPacketByteLongWordIndex I, bytesStoreLiteSetPacketByteLongDataSlot I,
        UInt256.shiftLeft (bytesStoreLiteSetByteValueWord I) ⟨248⟩, ⟨0⟩,
        bytesStoreLiteSetByteValueWord I, bytesStoreLiteSetByteIndexWord I, ⟨301⟩,
        bytesStoreLiteSelWord I]
      (wordAt0Mem (⟨2⟩ : UInt256) solcFreePtrMem) (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd622⟩ := hreach
  have hlt : UInt256.lt (bytesStoreLiteSetByteIndexWord I) len = ⟨1⟩ :=
    ult_one hbound
  have hflagOne :
      UInt256.land (bytesStoreLitePacketLengthHeaderWord σ I) ⟨1⟩ = ⟨1⟩ :=
    u256_land_one_eq_one_of_ne_zero hflag
  have hslot := bytesStoreLiteSetPacketByteLongBaseHash
  have rd636 := evm_run rd622 with [
    jumpdest, dup2, lt, push2 ⟨636⟩,
    jumpiT (by rw [hlt]; decide) (by native_decide)]
  have rd638 := evm_run rd636 with [jumpdest, dup2]
  obtain ⟨_, _, rd639₀⟩ := rd638.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd639⟩ :
      ∃ k C, RD bytesStoreLiteBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨639⟩
        [bytesStoreLitePacketLengthHeaderWord σ I, bytesStoreLiteSetByteIndexWord I, ⟨2⟩,
          UInt256.shiftLeft (bytesStoreLiteSetByteValueWord I) ⟨248⟩, ⟨0⟩,
          bytesStoreLiteSetByteValueWord I, bytesStoreLiteSetByteIndexWord I, ⟨301⟩,
          bytesStoreLiteSelWord I]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by
      simpa [bytesStoreLitePacketLengthHeaderWord, initState] using rd639₀⟩
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
    simpa [bytesStoreLiteSetPacketByteLongWordIndex,
      bytesStoreLiteSetPacketByteLongDataSlot,
      u256_add_comm (UInt256.div (bytesStoreLiteSetByteIndexWord I) ⟨32⟩)
        (bytesLikeDataBase ⟨2⟩)] using rd665raw⟩

theorem bytesStoreLiteX_setPacketByteShortStorePacket {cA gh bl σ σ₀ A I}
    {g : Sat256}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨665⟩
      [bytesStoreLiteSetByteIndexWord I, ⟨2⟩,
        UInt256.shiftLeft (bytesStoreLiteSetByteValueWord I) ⟨248⟩, ⟨0⟩,
        bytesStoreLiteSetByteValueWord I, bytesStoreLiteSetByteIndexWord I, ⟨301⟩,
        bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hperm : I.perm = true) :
    ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨694⟩
      [⟨0⟩, bytesStoreLiteSetByteValueWord I, bytesStoreLiteSetByteIndexWord I, ⟨301⟩,
        bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ ⟨2⟩
        (bytesStoreLiteSetPacketByteShortStoredWord σ I)) k C := by
  obtain ⟨_, _, rd665⟩ := hreach
  have rd674 := evm_run rd665 with [
    jumpdest, push1 ⟨31⟩, sub, push2 ⟨256⟩, exp, dup2]
  obtain ⟨_, _, rd675₀⟩ := rd674.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd675⟩ :
      ∃ k C, RD bytesStoreLiteBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨675⟩
        [bytesStoreLitePacketLengthHeaderWord σ I,
          UInt256.exp ⟨256⟩ (UInt256.sub ⟨31⟩ (bytesStoreLiteSetByteIndexWord I)),
          ⟨2⟩, UInt256.shiftLeft (bytesStoreLiteSetByteValueWord I) ⟨248⟩, ⟨0⟩,
          bytesStoreLiteSetByteValueWord I, bytesStoreLiteSetByteIndexWord I, ⟨301⟩,
          bytesStoreLiteSelWord I]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by
      simpa [bytesStoreLitePacketLengthHeaderWord, initState] using rd675₀⟩
  have rd692 := evm_run rd675 with [
    dup2, push1 ⟨255⟩, mul, not, and, swap1,
    push1 ⟨1⟩, push1 ⟨248⟩, shl, dup5, div, mul, lor, swap1]
  obtain ⟨_, _, rd692'⟩ :
      ∃ k C, RD bytesStoreLiteBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨692⟩
        [⟨2⟩,
          bytesStoreLiteSetPacketByteShortStoredWord σ I,
          UInt256.shiftLeft (bytesStoreLiteSetByteValueWord I) ⟨248⟩, ⟨0⟩,
          bytesStoreLiteSetByteValueWord I, bytesStoreLiteSetByteIndexWord I, ⟨301⟩,
          bytesStoreLiteSelWord I]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by
      simpa [bytesStoreLiteSetPacketByteShortStoredWord,
        bytesStoreLiteSetPacketByteShortScale] using rd692⟩
  obtain ⟨_, _, rd693₀⟩ := rd692'.sstore hperm (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd693⟩ :
      ∃ k C, RD bytesStoreLiteBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨693⟩
        [UInt256.shiftLeft (bytesStoreLiteSetByteValueWord I) ⟨248⟩, ⟨0⟩,
          bytesStoreLiteSetByteValueWord I, bytesStoreLiteSetByteIndexWord I, ⟨301⟩,
          bytesStoreLiteSelWord I]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, sstoreAccountMap I.codeOwner σ ⟨2⟩
          (bytesStoreLiteSetPacketByteShortStoredWord σ I)) k C := by
    exact ⟨_, _, by simpa [sstoreAccountMap, initState] using rd693₀⟩
  exact ⟨_, _, evm_run rd693 with [pop]⟩

theorem bytesStoreLiteX_setPacketByteLongStorePacket {cA gh bl σ σ₀ A I}
    {g : Sat256}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨665⟩
      [bytesStoreLiteSetPacketByteLongWordIndex I, bytesStoreLiteSetPacketByteLongDataSlot I,
        UInt256.shiftLeft (bytesStoreLiteSetByteValueWord I) ⟨248⟩, ⟨0⟩,
        bytesStoreLiteSetByteValueWord I, bytesStoreLiteSetByteIndexWord I, ⟨301⟩,
        bytesStoreLiteSelWord I]
      (wordAt0Mem (⟨2⟩ : UInt256) solcFreePtrMem) (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C)
    (hperm : I.perm = true) :
    ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨694⟩
      [⟨0⟩, bytesStoreLiteSetByteValueWord I, bytesStoreLiteSetByteIndexWord I, ⟨301⟩,
        bytesStoreLiteSelWord I]
      (wordAt0Mem (⟨2⟩ : UInt256) solcFreePtrMem) (UInt256.ofNat 3)
      ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ (bytesStoreLiteSetPacketByteLongDataSlot I)
        (bytesStoreLiteSetPacketByteLongStoredWord σ I)) k C := by
  obtain ⟨_, _, rd665⟩ := hreach
  have rd674 := evm_run rd665 with [
    jumpdest, push1 ⟨31⟩, sub, push2 ⟨256⟩, exp, dup2]
  obtain ⟨_, _, rd675₀⟩ := rd674.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd675⟩ :
      ∃ k C, RD bytesStoreLiteBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨675⟩
        [bytesStoreLiteSetPacketByteLongOldWord σ I,
          UInt256.exp ⟨256⟩ (UInt256.sub ⟨31⟩
            (bytesStoreLiteSetPacketByteLongWordIndex I)),
          bytesStoreLiteSetPacketByteLongDataSlot I,
          UInt256.shiftLeft (bytesStoreLiteSetByteValueWord I) ⟨248⟩, ⟨0⟩,
          bytesStoreLiteSetByteValueWord I, bytesStoreLiteSetByteIndexWord I, ⟨301⟩,
          bytesStoreLiteSelWord I]
        (wordAt0Mem (⟨2⟩ : UInt256) solcFreePtrMem) (UInt256.ofNat 3)
        ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by
      simpa [bytesStoreLiteSetPacketByteLongOldWord, initState] using rd675₀⟩
  have rd692 := evm_run rd675 with [
    dup2, push1 ⟨255⟩, mul, not, and, swap1,
    push1 ⟨1⟩, push1 ⟨248⟩, shl, dup5, div, mul, lor, swap1]
  obtain ⟨_, _, rd692'⟩ :
      ∃ k C, RD bytesStoreLiteBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨692⟩
        [bytesStoreLiteSetPacketByteLongDataSlot I,
          bytesStoreLiteSetPacketByteLongStoredWord σ I,
          UInt256.shiftLeft (bytesStoreLiteSetByteValueWord I) ⟨248⟩, ⟨0⟩,
          bytesStoreLiteSetByteValueWord I, bytesStoreLiteSetByteIndexWord I, ⟨301⟩,
          bytesStoreLiteSelWord I]
        (wordAt0Mem (⟨2⟩ : UInt256) solcFreePtrMem) (UInt256.ofNat 3)
        ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by
      simpa [bytesStoreLiteSetPacketByteLongStoredWord,
        bytesStoreLiteSetPacketByteLongScale] using rd692⟩
  obtain ⟨_, _, rd693₀⟩ := rd692'.sstore hperm (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd693⟩ :
      ∃ k C, RD bytesStoreLiteBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨693⟩
        [UInt256.shiftLeft (bytesStoreLiteSetByteValueWord I) ⟨248⟩, ⟨0⟩,
          bytesStoreLiteSetByteValueWord I, bytesStoreLiteSetByteIndexWord I, ⟨301⟩,
          bytesStoreLiteSelWord I]
        (wordAt0Mem (⟨2⟩ : UInt256) solcFreePtrMem) (UInt256.ofNat 3)
        ByteArray.empty
        (cA, sstoreAccountMap I.codeOwner σ (bytesStoreLiteSetPacketByteLongDataSlot I)
          (bytesStoreLiteSetPacketByteLongStoredWord σ I)) k C := by
    exact ⟨_, _, by simpa [sstoreAccountMap, initState] using rd693₀⟩
  exact ⟨_, _, evm_run rd693 with [pop]⟩

theorem bytesStoreLiteX_setPacketByteReturnReachLengthDecoder
    {cA gh bl σinit σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨694⟩
      [⟨0⟩, bytesStoreLiteSetByteValueWord I, bytesStoreLiteSetByteIndexWord I, ⟨301⟩,
        bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨2246⟩
      [Option.option ⟨0⟩ (fun ac => Batteries.RBMap.findD ac.storage ⟨2⟩ ⟨0⟩)
          (Batteries.RBMap.find? σ I.codeOwner),
        ⟨709⟩,
        bytesStoreLiteSetByteIndexWord I, ⟨2⟩, ⟨0⟩,
        bytesStoreLiteSetByteValueWord I, bytesStoreLiteSetByteIndexWord I, ⟨301⟩,
        bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd694⟩ := hreach
  have rd700 := evm_run rd694 with [push1 ⟨2⟩, push0, add, dup4, dup2]
  obtain ⟨_, _, rd701₀⟩ := rd700.sload (by native_decide) (by evm_ov)
  have rd2246 := evm_run rd701₀ with [
    push2 ⟨709⟩, swap1, push2 ⟨2246⟩, jump (by native_decide)]
  exact ⟨_, _, rd2246⟩

theorem bytesStoreLiteX_setPacketByteReturnReachLengthDecoderMem
    {cA gh bl σinit σ σ₀ A I} {g : Sat256} {mem : ByteArray}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨694⟩
      [⟨0⟩, bytesStoreLiteSetByteValueWord I, bytesStoreLiteSetByteIndexWord I, ⟨301⟩,
        bytesStoreLiteSelWord I]
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨2246⟩
      [Option.option ⟨0⟩ (fun ac => Batteries.RBMap.findD ac.storage ⟨2⟩ ⟨0⟩)
          (Batteries.RBMap.find? σ I.codeOwner),
        ⟨709⟩,
        bytesStoreLiteSetByteIndexWord I, ⟨2⟩, ⟨0⟩,
        bytesStoreLiteSetByteValueWord I, bytesStoreLiteSetByteIndexWord I, ⟨301⟩,
        bytesStoreLiteSelWord I]
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd694⟩ := hreach
  have rd700 := evm_run rd694 with [push1 ⟨2⟩, push0, add, dup4, dup2]
  obtain ⟨_, _, rd701₀⟩ := rd700.sload (by native_decide) (by evm_ov)
  have rd2246 := evm_run rd701₀ with [
    push2 ⟨709⟩, swap1, push2 ⟨2246⟩, jump (by native_decide)]
  exact ⟨_, _, rd2246⟩

theorem bytesStoreLiteX_setPacketByteLongWriteReturnReachLengthDecoder
    {cA gh bl σ σ₀ A I} {g : Sat256} {len : UInt256}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨622⟩
      [len, bytesStoreLiteSetByteIndexWord I, ⟨2⟩,
        UInt256.shiftLeft (bytesStoreLiteSetByteValueWord I) ⟨248⟩, ⟨0⟩,
        bytesStoreLiteSetByteValueWord I, bytesStoreLiteSetByteIndexWord I, ⟨301⟩,
        bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hbound : (bytesStoreLiteSetByteIndexWord I).toNat < len.toNat)
    (hflag : UInt256.land (bytesStoreLitePacketLengthHeaderWord σ I) ⟨1⟩ ≠ ⟨0⟩)
    (hperm : I.perm = true) :
    ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2246⟩
      [Option.option ⟨0⟩ (fun ac => Batteries.RBMap.findD ac.storage ⟨2⟩ ⟨0⟩)
          (Batteries.RBMap.find?
            (sstoreAccountMap I.codeOwner σ (bytesStoreLiteSetPacketByteLongDataSlot I)
              (bytesStoreLiteSetPacketByteLongStoredWord σ I)) I.codeOwner),
        ⟨709⟩, bytesStoreLiteSetByteIndexWord I, ⟨2⟩, ⟨0⟩,
        bytesStoreLiteSetByteValueWord I, bytesStoreLiteSetByteIndexWord I, ⟨301⟩,
        bytesStoreLiteSelWord I]
      (wordAt0Mem (⟨2⟩ : UInt256) solcFreePtrMem) (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ (bytesStoreLiteSetPacketByteLongDataSlot I)
        (bytesStoreLiteSetPacketByteLongStoredWord σ I)) k C := by
  have h665 := bytesStoreLiteX_setPacketByteLongReachStoreCommon
    (g := g) hreach hbound hflag
  have h694 := bytesStoreLiteX_setPacketByteLongStorePacket
    (g := g) h665 hperm
  exact bytesStoreLiteX_setPacketByteReturnReachLengthDecoderMem
    (σinit := σ)
    (σ := sstoreAccountMap I.codeOwner σ (bytesStoreLiteSetPacketByteLongDataSlot I)
      (bytesStoreLiteSetPacketByteLongStoredWord σ I))
    h694

theorem bytesStoreLiteX_setPacketByteLongWriteReturnDecodedLength
    {cA gh bl σ σ₀ A I} {g : Sat256} {len : UInt256}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨622⟩
      [len, bytesStoreLiteSetByteIndexWord I, ⟨2⟩,
        UInt256.shiftLeft (bytesStoreLiteSetByteValueWord I) ⟨248⟩, ⟨0⟩,
        bytesStoreLiteSetByteValueWord I, bytesStoreLiteSetByteIndexWord I, ⟨301⟩,
        bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hlen : len = UInt256.div (bytesStoreLitePacketLengthHeaderWord σ I) ⟨2⟩)
    (hbound : (bytesStoreLiteSetByteIndexWord I).toNat < len.toNat)
    (hflag : UInt256.land (bytesStoreLitePacketLengthHeaderWord σ I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (bytesStoreLitePacketLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStoreLitePacketLengthHeaderWord σ I) ⟨2⟩) ⟨32⟩) ≠ ⟨0⟩)
    (hperm : I.perm = true) :
    ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨709⟩
      [len, bytesStoreLiteSetByteIndexWord I, ⟨2⟩, ⟨0⟩,
        bytesStoreLiteSetByteValueWord I, bytesStoreLiteSetByteIndexWord I, ⟨301⟩,
        bytesStoreLiteSelWord I]
      (wordAt0Mem (⟨2⟩ : UInt256) solcFreePtrMem) (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ (bytesStoreLiteSetPacketByteLongDataSlot I)
        (bytesStoreLiteSetPacketByteLongStoredWord σ I)) k C := by
  let σ' := sstoreAccountMap I.codeOwner σ (bytesStoreLiteSetPacketByteLongDataSlot I)
    (bytesStoreLiteSetPacketByteLongStoredWord σ I)
  let header' : UInt256 :=
    Option.option ⟨0⟩ (fun ac => Batteries.RBMap.findD ac.storage ⟨2⟩ ⟨0⟩)
      (Batteries.RBMap.find? σ' I.codeOwner)
  have hdec := bytesStoreLiteX_setPacketByteLongWriteReturnReachLengthDecoder
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (I := I) (g := g) (len := len) hreach hbound hflag hperm
  have hne : (⟨2⟩ : UInt256) ≠ bytesStoreLiteSetPacketByteLongDataSlot I := by
    exact (bytesStoreLitePacketDataSlot_ne_header (bytesStoreLiteSetByteIndexWord I)).symm
  have hheader : header' = bytesStoreLitePacketLengthHeaderWord σ I := by
    simpa [header', σ', bytesStoreLitePacketLengthHeaderWord] using
      sstoreAccountMap_storage_findD_ne σ I.codeOwner ⟨2⟩
        (bytesStoreLiteSetPacketByteLongDataSlot I)
        (bytesStoreLiteSetPacketByteLongStoredWord σ I) hne
  have hdecoded := bytesStoreLiteX_bytesLengthDecoderLongValidMemCarried
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (τ := σ') (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (header := header') (ret := ⟨709⟩)
    (rest := [bytesStoreLiteSetByteIndexWord I, ⟨2⟩, ⟨0⟩,
      bytesStoreLiteSetByteValueWord I, bytesStoreLiteSetByteIndexWord I, ⟨301⟩,
      bytesStoreLiteSelWord I])
    (mem := wordAt0Mem (⟨2⟩ : UInt256) solcFreePtrMem)
    (aw := UInt256.ofNat 3) (rdata := ByteArray.empty)
    (by simpa [header', σ'] using hdec)
    (by simpa [hheader] using hflag)
    (by simpa [hheader] using hvalid)
    (by native_decide)
    (by simp)
  simpa [σ', header', hheader, hlen] using hdecoded

theorem bytesStoreLiteX_setPacketByteLongReadReturnToWrapper
    {cA gh bl σinit τ σ₀ A I} {g : Sat256} {len header dataWord : UInt256}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨709⟩
      [len, bytesStoreLiteSetByteIndexWord I, ⟨2⟩, ⟨0⟩,
        bytesStoreLiteSetByteValueWord I, bytesStoreLiteSetByteIndexWord I, ⟨301⟩,
        bytesStoreLiteSelWord I]
      (wordAt0Mem (⟨2⟩ : UInt256) solcFreePtrMem) (UInt256.ofNat 3)
      ByteArray.empty (cA, τ) k C)
    (hbound : (bytesStoreLiteSetByteIndexWord I).toNat < len.toNat)
    (hheader :
      ((τ.find? I.codeOwner).option ⟨0⟩
        (fun acc => acc.storage.findD ⟨2⟩ ⟨0⟩)) = header)
    (hflag : UInt256.land header ⟨1⟩ ≠ ⟨0⟩)
    (hdata :
      ((τ.find? I.codeOwner).option ⟨0⟩
        (fun acc => acc.storage.findD (bytesStoreLiteSetPacketByteLongDataSlot I) ⟨0⟩)) =
          dataWord)
    (hbyte :
      UInt256.shiftRight
        (UInt256.mul (UInt256.byteAt (bytesStoreLiteSetPacketByteLongWordIndex I) dataWord)
          (UInt256.shiftLeft ⟨1⟩ ⟨248⟩))
        ⟨248⟩ = bytesStoreLiteSetByteValueWord I) :
    ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨301⟩
      [bytesStoreLiteSetByteValueWord I, bytesStoreLiteSelWord I]
      (wordAt0Mem (⟨2⟩ : UInt256)
        (wordAt0Mem (⟨2⟩ : UInt256) solcFreePtrMem))
      (UInt256.ofNat 3) ByteArray.empty (cA, τ) k C := by
  obtain ⟨_, _, rd709⟩ := hreach
  have hlt : UInt256.lt (bytesStoreLiteSetByteIndexWord I) len = ⟨1⟩ :=
    ult_one hbound
  have hflagOne : UInt256.land header ⟨1⟩ = ⟨1⟩ :=
    u256_land_one_eq_one_of_ne_zero hflag
  have hslot := bytesStoreLiteSetPacketByteLongBaseHashMem
    (wordAt0Mem (⟨2⟩ : UInt256) solcFreePtrMem)
  have rd723 := evm_run rd709 with [
    jumpdest, dup2, lt, push2 ⟨723⟩,
    jumpiT (by rw [hlt]; decide) (by native_decide)]
  have rd725 := evm_run rd723 with [jumpdest, dup2]
  obtain ⟨_, _, rd726₀⟩ := rd725.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd726⟩ :
      ∃ k C, RD bytesStoreLiteBytecode I g
        (initState cA gh bl σinit σ₀ g A I) ⟨726⟩
        [header, bytesStoreLiteSetByteIndexWord I, ⟨2⟩, ⟨0⟩,
          bytesStoreLiteSetByteValueWord I, bytesStoreLiteSetByteIndexWord I, ⟨301⟩,
          bytesStoreLiteSelWord I]
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
      ∃ k C, RD bytesStoreLiteBytecode I g
        (initState cA gh bl σinit σ₀ g A I) ⟨752⟩
        [bytesStoreLiteSetPacketByteLongWordIndex I,
          bytesStoreLiteSetPacketByteLongDataSlot I, ⟨0⟩,
          bytesStoreLiteSetByteValueWord I, bytesStoreLiteSetByteIndexWord I, ⟨301⟩,
          bytesStoreLiteSelWord I]
        (wordAt0Mem (⟨2⟩ : UInt256)
          (wordAt0Mem (⟨2⟩ : UInt256) solcFreePtrMem))
        (UInt256.ofNat 3) ByteArray.empty (cA, τ) k C := by
    exact ⟨_, _, by
      simpa [bytesStoreLiteSetPacketByteLongWordIndex,
        bytesStoreLiteSetPacketByteLongDataSlot,
        u256_add_comm (UInt256.div (bytesStoreLiteSetByteIndexWord I) ⟨32⟩)
          (bytesLikeDataBase ⟨2⟩)] using rd752raw⟩
  have rd754 := evm_run rd752 with [jumpdest, swap1]
  obtain ⟨_, _, rd755₀⟩ := rd754.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd755⟩ :
      ∃ k C, RD bytesStoreLiteBytecode I g
        (initState cA gh bl σinit σ₀ g A I) ⟨755⟩
        [dataWord, bytesStoreLiteSetPacketByteLongWordIndex I, ⟨0⟩,
          bytesStoreLiteSetByteValueWord I, bytesStoreLiteSetByteIndexWord I, ⟨301⟩,
          bytesStoreLiteSelWord I]
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

theorem bytesStoreLiteX_setPacketByteShortWriteReturnReachLengthDecoder
    {cA gh bl σ σ₀ A I} {g : Sat256} {len : UInt256}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨622⟩
      [len, bytesStoreLiteSetByteIndexWord I, ⟨2⟩,
        UInt256.shiftLeft (bytesStoreLiteSetByteValueWord I) ⟨248⟩, ⟨0⟩,
        bytesStoreLiteSetByteValueWord I, bytesStoreLiteSetByteIndexWord I, ⟨301⟩,
        bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hbound : (bytesStoreLiteSetByteIndexWord I).toNat < len.toNat)
    (hflag : UInt256.land (bytesStoreLitePacketLengthHeaderWord σ I) ⟨1⟩ = ⟨0⟩)
    (hperm : I.perm = true) :
    ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2246⟩
      [Option.option ⟨0⟩ (fun ac => Batteries.RBMap.findD ac.storage ⟨2⟩ ⟨0⟩)
          (Batteries.RBMap.find?
            (sstoreAccountMap I.codeOwner σ ⟨2⟩
              (bytesStoreLiteSetPacketByteShortStoredWord σ I)) I.codeOwner),
        ⟨709⟩, bytesStoreLiteSetByteIndexWord I, ⟨2⟩, ⟨0⟩,
        bytesStoreLiteSetByteValueWord I, bytesStoreLiteSetByteIndexWord I, ⟨301⟩,
        bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ ⟨2⟩
        (bytesStoreLiteSetPacketByteShortStoredWord σ I)) k C := by
  have h665 := bytesStoreLiteX_setPacketByteShortReachStoreCommon
    (g := g) hreach hbound hflag
  have h694 := bytesStoreLiteX_setPacketByteShortStorePacket
    (g := g) h665 hperm
  exact bytesStoreLiteX_setPacketByteReturnReachLengthDecoder
    (σinit := σ)
    (σ := sstoreAccountMap I.codeOwner σ ⟨2⟩
      (bytesStoreLiteSetPacketByteShortStoredWord σ I))
    h694

theorem bytesStoreLiteX_setPacketByteShortWriteReturnDecodedLength
    {cA gh bl σ σ₀ A I} {g : Sat256} {len : UInt256} {acc : Account}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨622⟩
      [len, bytesStoreLiteSetByteIndexWord I, ⟨2⟩,
        UInt256.shiftLeft (bytesStoreLiteSetByteValueWord I) ⟨248⟩, ⟨0⟩,
        bytesStoreLiteSetByteValueWord I, bytesStoreLiteSetByteIndexWord I, ⟨301⟩,
        bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hlen : len =
      UInt256.land (UInt256.div (bytesStoreLitePacketLengthHeaderWord σ I) ⟨2⟩) ⟨127⟩)
    (hshort : len.toNat < 32)
    (hbound : (bytesStoreLiteSetByteIndexWord I).toNat < len.toNat)
    (hflag : UInt256.land (bytesStoreLitePacketLengthHeaderWord σ I) ⟨1⟩ = ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (bytesStoreLitePacketLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStoreLitePacketLengthHeaderWord σ I) ⟨2⟩) ⟨127⟩)
          ⟨32⟩) ≠ ⟨0⟩)
    (hperm : I.perm = true)
    (hacc : σ.find? I.codeOwner = some acc) :
    ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨709⟩
      [len, bytesStoreLiteSetByteIndexWord I, ⟨2⟩, ⟨0⟩,
        bytesStoreLiteSetByteValueWord I, bytesStoreLiteSetByteIndexWord I, ⟨301⟩,
        bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ ⟨2⟩
        (bytesStoreLiteSetPacketByteShortStoredWord σ I)) k C := by
  let σ' := sstoreAccountMap I.codeOwner σ ⟨2⟩
    (bytesStoreLiteSetPacketByteShortStoredWord σ I)
  let header' : UInt256 :=
    Option.option ⟨0⟩ (fun ac => Batteries.RBMap.findD ac.storage ⟨2⟩ ⟨0⟩)
      (Batteries.RBMap.find? σ' I.codeOwner)
  have hdec := bytesStoreLiteX_setPacketByteShortWriteReturnReachLengthDecoder
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (I := I) (g := g) (len := len) hreach hbound hflag hperm
  have hnz := bytesStoreLiteSetPacketByteShortStoredWord_beq_zero_false
    (σ := σ) (I := I) (len := len) hlen hshort hbound
  have hheader : header' = bytesStoreLiteSetPacketByteShortStoredWord σ I := by
    simpa [header', σ'] using
      bytesStoreLiteSetPacketByteShortStoredWord_load_self (σ := σ) (I := I) (acc := acc)
        hacc hnz
  have hflag' : UInt256.land header' ⟨1⟩ = ⟨0⟩ := by
    rw [hheader, bytesStoreLiteSetPacketByteShortStoredWord_flag_eq
      (σ := σ) (I := I) (len := len) hshort hbound, hflag]
  have hvalid' : UInt256.sub (UInt256.land header' ⟨1⟩)
      (UInt256.lt (UInt256.land (UInt256.div header' ⟨2⟩) ⟨127⟩) ⟨32⟩) ≠
        ⟨0⟩ := by
    rw [hheader, bytesStoreLiteSetPacketByteShortStoredWord_flag_eq
      (σ := σ) (I := I) (len := len) hshort hbound,
      bytesStoreLiteSetPacketByteShortStoredWord_shortLen_eq
        (σ := σ) (I := I) (len := len) hshort hbound]
    exact hvalid
  have hdecoded := bytesStoreLiteX_bytesLengthDecoderShortValidMemCarried
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (τ := σ') (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (header := header') (ret := ⟨709⟩)
    (rest := [bytesStoreLiteSetByteIndexWord I, ⟨2⟩, ⟨0⟩,
      bytesStoreLiteSetByteValueWord I, bytesStoreLiteSetByteIndexWord I, ⟨301⟩,
      bytesStoreLiteSelWord I])
    (mem := solcFreePtrMem) (aw := UInt256.ofNat 3) (rdata := ByteArray.empty)
    (by simpa [header', σ'] using hdec) hflag' hvalid' (by native_decide)
    (by simp)
  have hlen' :
      UInt256.land (UInt256.div (bytesStoreLiteSetPacketByteShortStoredWord σ I) ⟨2⟩) ⟨127⟩ =
        len := by
    rw [bytesStoreLiteSetPacketByteShortStoredWord_shortLen_eq
      (σ := σ) (I := I) (len := len) hshort hbound, ← hlen]
  simpa [σ', header', hheader, hlen'] using hdecoded

theorem bytesStoreLiteX_setPacketByteShortReadReturnToWrapper
    {cA gh bl σinit τ σ₀ A I} {g : Sat256} {len header : UInt256}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨709⟩
      [len, bytesStoreLiteSetByteIndexWord I, ⟨2⟩, ⟨0⟩,
        bytesStoreLiteSetByteValueWord I, bytesStoreLiteSetByteIndexWord I, ⟨301⟩,
        bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, τ) k C)
    (hbound : (bytesStoreLiteSetByteIndexWord I).toNat < len.toNat)
    (hheader :
      ((τ.find? I.codeOwner).option ⟨0⟩
        (fun acc => acc.storage.findD ⟨2⟩ ⟨0⟩)) = header)
    (hflag : UInt256.land header ⟨1⟩ = ⟨0⟩)
    (hbyte :
      UInt256.shiftRight
        (UInt256.mul (UInt256.byteAt (bytesStoreLiteSetByteIndexWord I) header)
          (UInt256.shiftLeft ⟨1⟩ ⟨248⟩))
        ⟨248⟩ = bytesStoreLiteSetByteValueWord I) :
    ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨301⟩
      [bytesStoreLiteSetByteValueWord I, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, τ) k C := by
  obtain ⟨_, _, rd709⟩ := hreach
  have hlt : UInt256.lt (bytesStoreLiteSetByteIndexWord I) len = ⟨1⟩ :=
    ult_one hbound
  have rd723 := evm_run rd709 with [
    jumpdest, dup2, lt, push2 ⟨723⟩,
    jumpiT (by rw [hlt]; decide) (by native_decide)]
  have rd725 := evm_run rd723 with [jumpdest, dup2]
  obtain ⟨_, _, rd726₀⟩ := rd725.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd726⟩ :
      ∃ k C, RD bytesStoreLiteBytecode I g
        (initState cA gh bl σinit σ₀ g A I) ⟨726⟩
        [header, bytesStoreLiteSetByteIndexWord I, ⟨2⟩, ⟨0⟩,
          bytesStoreLiteSetByteValueWord I, bytesStoreLiteSetByteIndexWord I, ⟨301⟩,
          bytesStoreLiteSelWord I]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, τ) k C := by
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
      ∃ k C, RD bytesStoreLiteBytecode I g
        (initState cA gh bl σinit σ₀ g A I) ⟨755⟩
        [header, bytesStoreLiteSetByteIndexWord I, ⟨0⟩,
          bytesStoreLiteSetByteValueWord I, bytesStoreLiteSetByteIndexWord I, ⟨301⟩,
          bytesStoreLiteSelWord I]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, τ) k C := by
    exact ⟨_, _, by simpa [initState, hheader] using rd755₀⟩
  have rd761 := evm_run rd755 with [
    push1 ⟨1⟩, push1 ⟨248⟩, shl, swap2]
  have rd762 := RD.byte rd761 (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd301 := evm_run rd762 with [
    mul, push1 ⟨248⟩, shr,
    swap4, swap3, pop, pop, pop, jump (by native_decide)]
  exact ⟨_, _, by simpa [hbyte] using rd301⟩

theorem bytesStoreLiteX_setPacketByteShortSuccessReturn
    {cA gh bl σ σ₀ A I} {g : Sat256} {len : UInt256} {acc : Account}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨601⟩
      [bytesStoreLiteSetByteValueWord I, bytesStoreLiteSetByteIndexWord I, ⟨301⟩,
        bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hcanon : (bytesStoreLiteSetByteValueWord I).toNat < EVM.twoPow 8)
    (hlen : len =
      UInt256.land (UInt256.div (bytesStoreLitePacketLengthHeaderWord σ I) ⟨2⟩) ⟨127⟩)
    (hshort : len.toNat < 32)
    (hbound : (bytesStoreLiteSetByteIndexWord I).toNat < len.toNat)
    (hflag : UInt256.land (bytesStoreLitePacketLengthHeaderWord σ I) ⟨1⟩ = ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (bytesStoreLitePacketLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStoreLitePacketLengthHeaderWord σ I) ⟨2⟩) ⟨127⟩)
          ⟨32⟩) ≠ ⟨0⟩)
    (hperm : I.perm = true)
    (hacc : σ.find? I.codeOwner = some acc) :
    RDret bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, sstoreAccountMap I.codeOwner σ ⟨2⟩
        (bytesStoreLiteSetPacketByteShortStoredWord σ I))
      (UInt256.toByteArray (bytesStoreLiteSetByteValueWord I)) := by
  let σ' := sstoreAccountMap I.codeOwner σ ⟨2⟩
    (bytesStoreLiteSetPacketByteShortStoredWord σ I)
  let header' : UInt256 :=
    Option.option ⟨0⟩ (fun ac => Batteries.RBMap.findD ac.storage ⟨2⟩ ⟨0⟩)
      (Batteries.RBMap.find? σ' I.codeOwner)
  have hdec := bytesStoreLiteX_setPacketByteReachLengthDecoder (g := g) hreach
  have h622 := bytesStoreLiteX_bytesLengthDecoderShortValidMem
    (A := A) (I := I) (g := g) hdec hflag hvalid (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have hread := bytesStoreLiteX_setPacketByteShortWriteReturnDecodedLength
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (I := I) (g := g) (len := len) (acc := acc) (by simpa [hlen] using h622)
    hlen hshort hbound
    hflag hvalid hperm hacc
  have hnz := bytesStoreLiteSetPacketByteShortStoredWord_beq_zero_false
    (σ := σ) (I := I) (len := len) hlen hshort hbound
  have hheader : header' = bytesStoreLiteSetPacketByteShortStoredWord σ I := by
    simpa [header', σ'] using
      bytesStoreLiteSetPacketByteShortStoredWord_load_self (σ := σ) (I := I) (acc := acc)
        hacc hnz
  have hflag' : UInt256.land header' ⟨1⟩ = ⟨0⟩ := by
    rw [hheader, bytesStoreLiteSetPacketByteShortStoredWord_flag_eq
      (σ := σ) (I := I) (len := len) hshort hbound, hflag]
  have hbyteAt :
      UInt256.byteAt (bytesStoreLiteSetByteIndexWord I) header' =
        bytesStoreLiteSetByteValueWord I := by
    rw [hheader]
    exact bytesStoreLiteSetPacketByteShortStoredWord_byteAt
      (σ := σ) (I := I) (len := len) hcanon hshort hbound
  have hbyte :
      UInt256.shiftRight
        (UInt256.mul (UInt256.byteAt (bytesStoreLiteSetByteIndexWord I) header')
          (UInt256.shiftLeft ⟨1⟩ ⟨248⟩))
        ⟨248⟩ = bytesStoreLiteSetByteValueWord I := by
    rw [hbyteAt]
    exact bytesStoreLiteSetByteValueHighMulShiftRight hcanon
  have h301 := bytesStoreLiteX_setPacketByteShortReadReturnToWrapper
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (τ := σ') (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (len := len) (header := header') hread hbound
    (by rfl) hflag' hbyte
  have hret := bytesStoreLiteX_returnUInt8_301
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σ') (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (val := bytesStoreLiteSetByteValueWord I) h301
  simpa [σ', bytesStoreLiteSetPacketByteLand255_eq_self_of_uint8 hcanon] using hret

theorem bytesStoreLiteX_setPacketByteLongSuccessReturn
    {cA gh bl σ σ₀ A I} {g : Sat256} {len : UInt256} {acc : Account}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨601⟩
      [bytesStoreLiteSetByteValueWord I, bytesStoreLiteSetByteIndexWord I, ⟨301⟩,
        bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hcanon : (bytesStoreLiteSetByteValueWord I).toNat < EVM.twoPow 8)
    (hlen : len = UInt256.div (bytesStoreLitePacketLengthHeaderWord σ I) ⟨2⟩)
    (hbound : (bytesStoreLiteSetByteIndexWord I).toNat < len.toNat)
    (hflag : UInt256.land (bytesStoreLitePacketLengthHeaderWord σ I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (bytesStoreLitePacketLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStoreLitePacketLengthHeaderWord σ I) ⟨2⟩) ⟨32⟩) ≠ ⟨0⟩)
    (hperm : I.perm = true)
    (hacc : σ.find? I.codeOwner = some acc) :
    RDret bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, sstoreAccountMap I.codeOwner σ (bytesStoreLiteSetPacketByteLongDataSlot I)
        (bytesStoreLiteSetPacketByteLongStoredWord σ I))
      (UInt256.toByteArray (bytesStoreLiteSetByteValueWord I)) := by
  let σ' := sstoreAccountMap I.codeOwner σ (bytesStoreLiteSetPacketByteLongDataSlot I)
    (bytesStoreLiteSetPacketByteLongStoredWord σ I)
  let header' : UInt256 :=
    Option.option ⟨0⟩ (fun ac => Batteries.RBMap.findD ac.storage ⟨2⟩ ⟨0⟩)
      (Batteries.RBMap.find? σ' I.codeOwner)
  let dataWord' : UInt256 :=
    Option.option ⟨0⟩
      (fun ac => Batteries.RBMap.findD ac.storage (bytesStoreLiteSetPacketByteLongDataSlot I)
        ⟨0⟩)
      (Batteries.RBMap.find? σ' I.codeOwner)
  have hdec := bytesStoreLiteX_setPacketByteReachLengthDecoder (g := g) hreach
  have h622 := bytesStoreLiteX_bytesLengthDecoderLongValidMem
    (A := A) (I := I) (g := g) hdec hflag hvalid (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have hread := bytesStoreLiteX_setPacketByteLongWriteReturnDecodedLength
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (I := I) (g := g) (len := len) (by simpa [hlen] using h622)
    hlen hbound hflag hvalid hperm
  have hne : (⟨2⟩ : UInt256) ≠ bytesStoreLiteSetPacketByteLongDataSlot I := by
    exact (bytesStoreLitePacketDataSlot_ne_header (bytesStoreLiteSetByteIndexWord I)).symm
  have hheader : header' = bytesStoreLitePacketLengthHeaderWord σ I := by
    simpa [header', σ', bytesStoreLitePacketLengthHeaderWord] using
      sstoreAccountMap_storage_findD_ne σ I.codeOwner ⟨2⟩
        (bytesStoreLiteSetPacketByteLongDataSlot I)
        (bytesStoreLiteSetPacketByteLongStoredWord σ I) hne
  have hdata : dataWord' = bytesStoreLiteSetPacketByteLongStoredWord σ I := by
    simpa [dataWord', σ'] using
      sstoreAccountMap_storage_findD_self_of_find_some_any σ I.codeOwner acc
        (bytesStoreLiteSetPacketByteLongDataSlot I)
        (bytesStoreLiteSetPacketByteLongStoredWord σ I) hacc
  have hbyteAt :
      UInt256.byteAt (bytesStoreLiteSetPacketByteLongWordIndex I) dataWord' =
        bytesStoreLiteSetByteValueWord I := by
    rw [hdata]
    exact bytesStoreLiteSetPacketByteLongStoredWord_byteAt
      (σ := σ) (I := I) hcanon
  have hbyte :
      UInt256.shiftRight
        (UInt256.mul (UInt256.byteAt (bytesStoreLiteSetPacketByteLongWordIndex I) dataWord')
          (UInt256.shiftLeft ⟨1⟩ ⟨248⟩))
        ⟨248⟩ = bytesStoreLiteSetByteValueWord I := by
    rw [hbyteAt]
    exact bytesStoreLiteSetByteValueHighMulShiftRight hcanon
  have h301 := bytesStoreLiteX_setPacketByteLongReadReturnToWrapper
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (τ := σ') (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (len := len) (header := header')
    (dataWord := dataWord') hread hbound (by rfl)
    (by simpa [hheader] using hflag) (by rfl) hbyte
  have hret := bytesStoreLiteX_returnUInt8_301OfMem
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σ') (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (val := bytesStoreLiteSetByteValueWord I)
    (mem := wordAt0Mem (⟨2⟩ : UInt256)
      (wordAt0Mem (⟨2⟩ : UInt256) solcFreePtrMem))
    (wordAt0Mem_size_96 _ (wordAt0Mem_size_96 _ solcFreePtrMem_size))
    (bytesStoreLiteWordAt0Mem_read64 _
      (wordAt0Mem_size_96 _ solcFreePtrMem_size)
      (bytesStoreLiteWordAt0Mem_read64 _ solcFreePtrMem_size solcFreePtrMem_read64))
    h301
  simpa [σ', bytesStoreLiteSetPacketByteLand255_eq_self_of_uint8 hcanon] using hret

theorem bytesStoreLiteSetPacketByteShortSuccessRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256} {len : UInt256} {accEvm : Account}
    (hcode : I.code = bytesStoreLiteBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x0a, 0xb2, 0x59, 0x00]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (haccEvm : σ_evm.find? I.codeOwner = some accEvm)
    (hsz68 : 68 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (bytesStoreLiteSetByteValueWord I).toNat < EVM.twoPow 8)
    (hlen : len =
      UInt256.land (UInt256.div (bytesStoreLitePacketLengthHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩)
    (hshort : len.toNat < 32)
    (hbound : (bytesStoreLiteSetByteIndexWord I).toNat < len.toNat)
    (hflag : UInt256.land (bytesStoreLitePacketLengthHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (bytesStoreLitePacketLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStoreLitePacketLengthHeaderWord σ_evm I) ⟨2⟩)
            ⟨127⟩)
          ⟨32⟩) ≠ ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsz := bytesStoreLiteSetPacketByteSelector_size hsel
  have hreach := bytesStoreLiteReachSetPacketByte (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz hsize hsel
  have hreachPc : ∃ k C, RD bytesStoreLiteBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨282⟩
      [bytesStoreLiteSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ_evm) k C := by
    simpa [bytesStoreLiteSetPacketByteEntryPc] using hreach
  have hreachBody := bytesStoreLiteX_setPacketByteDecodeValid
    (g := Sat256.ofUInt256 g) hreachPc hsz68 hhi hsize
    (bytesStoreLiteSetPacketByteLand255_eq_self_of_uint8 hcanon)
  have hd := bytesStoreLiteDispatch_setPacketByte (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec := bytesStoreLiteDecode_setPacketByte_locals (I := I) hsz68 hhi hcanon
  have hret := bytesStoreLiteX_setPacketByteShortSuccessReturn
    (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
    (I := I) (g := Sat256.ofUInt256 g) (len := len) (acc := accEvm)
    hreachBody hcanon hlen hshort hbound hflag hvalid hperm haccEvm
  have hword :
      bytesStoreLitePacketLengthHeaderWord σ_evm I =
        bytesStoreLitePacketLengthHeaderWord σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨2⟩ ⟨0⟩
  have hslot :
      (σ_solm.find? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD ⟨2⟩ ⟨0⟩)) =
      (σ_evm.find? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD ⟨2⟩ ⟨0⟩)) := by
    simpa [bytesStoreLitePacketLengthHeaderWord] using hword.symm
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmSolm1 := Solm.EVM.storageStore evmSolm0 evmSolm0.executionEnv.codeOwner ⟨2⟩
    (bytesStoreLiteSetPacketByteShortStoredWord σ_evm I)
  have hload :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner ⟨2⟩ =
        bytesStoreLitePacketLengthHeaderWord σ_evm I := by
    simp [evmSolm0, Solm.EVM.storageLoad, initState, State.lookupAccount,
      Account.lookupStorage, bytesStoreLitePacketLengthHeaderWord, hslot]
  obtain ⟨accSolm, haccSolm⟩ :=
    accountMapEquiv_find?_some_exists hAccounts haccEvm
  have hbody :
      ExecTransitionBody bytesStoreLiteConfig bytesStoreLiteContract evmSolm0
        (bytesStoreLiteSetPacketByteLocals I) setPacketByteTransition.body
        (.returned
          (bytesStoreLiteSetPacketByteFrame I)
          evmSolm1 (some (bytesStoreLiteSetPacketByteValue I))) := by
    simpa [evmSolm0, evmSolm1, initState, bytesStoreLiteSetPacketByteFrame] using
      bytesStoreLiteSetPacketByteShortBodyReturns
        (evm := evmSolm0) (σ := σ_evm) (I := I) (len := len) (acc := accSolm)
        (by simp [evmSolm0, initState]; exact hwv)
        hload
        (by simpa [evmSolm0, initState] using haccSolm)
        hcanon hlen hshort hbound hflag hvalid
  have hpostAccounts :
      accountMapEquiv
        (sstoreAccountMap I.codeOwner σ_evm ⟨2⟩
          (bytesStoreLiteSetPacketByteShortStoredWord σ_evm I))
        evmSolm1.accountMap := by
    simp [evmSolm1, evmSolm0, initState, storageStore_accountMap]
    exact accountMapEquiv_sstoreAccountMap I.codeOwner ⟨2⟩
      (bytesStoreLiteSetPacketByteShortStoredWord σ_evm I) hAccounts
  exact hret.reEquivExecutionGenAccountMapEquiv hcode hd hdec hbody
    (by simp [evmSolm1, evmSolm0, initState, storageStore_createdAccounts])
    hpostAccounts
    (returnEquiv_of_encode (uint8ReturnEncoding (bytesStoreLiteSetByteValueWord I) hcanon))

theorem bytesStoreLiteSetPacketByteLongSuccessRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256} {len : UInt256} {accEvm : Account}
    (hcode : I.code = bytesStoreLiteBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x0a, 0xb2, 0x59, 0x00]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (haccEvm : σ_evm.find? I.codeOwner = some accEvm)
    (hsz68 : 68 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (bytesStoreLiteSetByteValueWord I).toNat < EVM.twoPow 8)
    (hlen : len = UInt256.div (bytesStoreLitePacketLengthHeaderWord σ_evm I) ⟨2⟩)
    (hbound : (bytesStoreLiteSetByteIndexWord I).toNat < len.toNat)
    (hflag : UInt256.land (bytesStoreLitePacketLengthHeaderWord σ_evm I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (bytesStoreLitePacketLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStoreLitePacketLengthHeaderWord σ_evm I) ⟨2⟩) ⟨32⟩) ≠ ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsz := bytesStoreLiteSetPacketByteSelector_size hsel
  have hreach := bytesStoreLiteReachSetPacketByte (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz hsize hsel
  have hreachPc : ∃ k C, RD bytesStoreLiteBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨282⟩
      [bytesStoreLiteSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ_evm) k C := by
    simpa [bytesStoreLiteSetPacketByteEntryPc] using hreach
  have hreachBody := bytesStoreLiteX_setPacketByteDecodeValid
    (g := Sat256.ofUInt256 g) hreachPc hsz68 hhi hsize
    (bytesStoreLiteSetPacketByteLand255_eq_self_of_uint8 hcanon)
  have hd := bytesStoreLiteDispatch_setPacketByte (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec := bytesStoreLiteDecode_setPacketByte_locals (I := I) hsz68 hhi hcanon
  have hret := bytesStoreLiteX_setPacketByteLongSuccessReturn
    (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
    (I := I) (g := Sat256.ofUInt256 g) (len := len) (acc := accEvm)
    hreachBody hcanon hlen hbound hflag hvalid hperm haccEvm
  have hword :
      bytesStoreLitePacketLengthHeaderWord σ_evm I =
        bytesStoreLitePacketLengthHeaderWord σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨2⟩ ⟨0⟩
  have hslot :
      (σ_solm.find? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD ⟨2⟩ ⟨0⟩)) =
      (σ_evm.find? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD ⟨2⟩ ⟨0⟩)) := by
    simpa [bytesStoreLitePacketLengthHeaderWord] using hword.symm
  have hdataWord :
      bytesStoreLiteSetPacketByteLongOldWord σ_evm I =
        bytesStoreLiteSetPacketByteLongOldWord σ_solm I := by
    exact accountMapEquiv_storage_findD hAccounts I.codeOwner
      (bytesStoreLiteSetPacketByteLongDataSlot I) ⟨0⟩
  have hdataSlot :
      (σ_solm.find? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD (bytesStoreLiteSetPacketByteLongDataSlot I) ⟨0⟩)) =
      (σ_evm.find? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD (bytesStoreLiteSetPacketByteLongDataSlot I) ⟨0⟩)) := by
    simpa [bytesStoreLiteSetPacketByteLongOldWord] using hdataWord.symm
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmSolm1 := Solm.EVM.storageStore evmSolm0 evmSolm0.executionEnv.codeOwner
    (bytesStoreLiteSetPacketByteLongDataSlot I)
    (bytesStoreLiteSetPacketByteLongStoredWord σ_evm I)
  have hloadHeader :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner ⟨2⟩ =
        bytesStoreLitePacketLengthHeaderWord σ_evm I := by
    simp [evmSolm0, Solm.EVM.storageLoad, initState, State.lookupAccount,
      Account.lookupStorage, bytesStoreLitePacketLengthHeaderWord, hslot]
  have hloadData :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner
          (bytesStoreLiteSetPacketByteLongDataSlot I) =
        bytesStoreLiteSetPacketByteLongOldWord σ_evm I := by
    simp [evmSolm0, Solm.EVM.storageLoad, initState, State.lookupAccount,
      Account.lookupStorage, bytesStoreLiteSetPacketByteLongOldWord, hdataSlot]
  obtain ⟨accSolm, haccSolm⟩ :=
    accountMapEquiv_find?_some_exists hAccounts haccEvm
  have hbody :
      ExecTransitionBody bytesStoreLiteConfig bytesStoreLiteContract evmSolm0
        (bytesStoreLiteSetPacketByteLocals I) setPacketByteTransition.body
        (.returned
          (bytesStoreLiteSetPacketByteFrame I)
          evmSolm1 (some (bytesStoreLiteSetPacketByteValue I))) := by
    simpa [evmSolm0, evmSolm1, initState, bytesStoreLiteSetPacketByteFrame] using
      bytesStoreLiteSetPacketByteLongBodyReturns
        (evm := evmSolm0) (σ := σ_evm) (I := I) (len := len) (acc := accSolm)
        (by simp [evmSolm0, initState]; exact hwv)
        hloadHeader hloadData
        (by simpa [evmSolm0, initState] using haccSolm)
        hcanon hlen hbound hflag hvalid
  have hpostAccounts :
      accountMapEquiv
        (sstoreAccountMap I.codeOwner σ_evm (bytesStoreLiteSetPacketByteLongDataSlot I)
          (bytesStoreLiteSetPacketByteLongStoredWord σ_evm I))
        evmSolm1.accountMap := by
    simp [evmSolm1, evmSolm0, initState, storageStore_accountMap]
    exact accountMapEquiv_sstoreAccountMap I.codeOwner
      (bytesStoreLiteSetPacketByteLongDataSlot I)
      (bytesStoreLiteSetPacketByteLongStoredWord σ_evm I) hAccounts
  exact hret.reEquivExecutionGenAccountMapEquiv hcode hd hdec hbody
    (by simp [evmSolm1, evmSolm0, initState, storageStore_createdAccounts])
    hpostAccounts
    (returnEquiv_of_encode (uint8ReturnEncoding (bytesStoreLiteSetByteValueWord I) hcanon))

theorem bytesStoreLiteSetPacketByteDecodeShortRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x0a, 0xb2, 0x59, 0x00]⟩)
    (_hAccounts : accountMapEquiv σ_evm σ_solm)
    (hshort : I.calldata.size < 68) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsz := bytesStoreLiteSetPacketByteSelector_size hsel
  have hreach := bytesStoreLiteReachSetPacketByte (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz hsize hsel
  have hreachPc : ∃ k C, RD bytesStoreLiteBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨282⟩
      [bytesStoreLiteSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ_evm) k C := by
    simpa [bytesStoreLiteSetPacketByteEntryPc] using hreach
  have hd := bytesStoreLiteDispatch_setPacketByte (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec := bytesStoreLiteDecode_setPacketByte_none_short (I := I) hshort
  exact (bytesStoreLiteX_setPacketByteDecodeShort
      (g := Sat256.ofUInt256 g) hreachPc hsz hshort hsize)
    |>.reEquivDecodingFailed hcode hd hdec

theorem bytesStoreLiteSetPacketByteDecodeHugeRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x0a, 0xb2, 0x59, 0x00]⟩)
    (_hAccounts : accountMapEquiv σ_evm σ_solm)
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsz := bytesStoreLiteSetPacketByteSelector_size hsel
  have hreach := bytesStoreLiteReachSetPacketByte (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz hsize hsel
  have hreachPc : ∃ k C, RD bytesStoreLiteBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨282⟩
      [bytesStoreLiteSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ_evm) k C := by
    simpa [bytesStoreLiteSetPacketByteEntryPc] using hreach
  have hd := bytesStoreLiteDispatch_setPacketByte (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec := bytesStoreLiteDecode_setPacketByte_none_huge (I := I) hbig
  exact (bytesStoreLiteX_setPacketByteDecodeHuge
      (g := Sat256.ofUInt256 g) hreachPc hbig hsize)
    |>.reEquivDecodingFailed hcode hd hdec

theorem bytesStoreLiteSetPacketByteDecodeNoncanonValueRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x0a, 0xb2, 0x59, 0x00]⟩)
    (_hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsz68 : 68 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hnc : ¬ (bytesStoreLiteSetByteValueWord I).toNat < EVM.twoPow 8) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsz := bytesStoreLiteSetPacketByteSelector_size hsel
  have hreach := bytesStoreLiteReachSetPacketByte (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz hsize hsel
  have hreachPc : ∃ k C, RD bytesStoreLiteBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨282⟩
      [bytesStoreLiteSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ_evm) k C := by
    simpa [bytesStoreLiteSetPacketByteEntryPc] using hreach
  have hd := bytesStoreLiteDispatch_setPacketByte (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec := bytesStoreLiteDecode_setPacketByte_none_noncanon_value (I := I) hsz68 hhi hnc
  exact (bytesStoreLiteX_setPacketByteDecodeNoncanonValue
      (g := Sat256.ofUInt256 g) hreachPc hsz68 hhi hsize
      (bytesStoreLiteSetPacketByteLand255_ne_self_of_not_uint8 hnc))
    |>.reEquivDecodingFailed hcode hd hdec

theorem bytesStoreLiteSetPacketByteOobLongRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x0a, 0xb2, 0x59, 0x00]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsz68 : 68 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (bytesStoreLiteSetByteValueWord I).toNat < EVM.twoPow 8)
    (hflag : UInt256.land (bytesStoreLitePacketLengthHeaderWord σ_evm I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (bytesStoreLitePacketLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStoreLitePacketLengthHeaderWord σ_evm I) ⟨2⟩) ⟨32⟩) ≠ ⟨0⟩)
    (hbound :
      ¬ (bytesStoreLiteSetByteIndexWord I).toNat <
        (UInt256.div (bytesStoreLitePacketLengthHeaderWord σ_evm I) ⟨2⟩).toNat) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsz := bytesStoreLiteSetPacketByteSelector_size hsel
  have hreach := bytesStoreLiteReachSetPacketByte (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz hsize hsel
  have hreachPc : ∃ k C, RD bytesStoreLiteBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨282⟩
      [bytesStoreLiteSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ_evm) k C := by
    simpa [bytesStoreLiteSetPacketByteEntryPc] using hreach
  have hreachBody := bytesStoreLiteX_setPacketByteDecodeValid
    (g := Sat256.ofUInt256 g) hreachPc hsz68 hhi hsize
    (bytesStoreLiteSetPacketByteLand255_eq_self_of_uint8 hcanon)
  have hd := bytesStoreLiteDispatch_setPacketByte (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec := bytesStoreLiteDecode_setPacketByte_locals (I := I) hsz68 hhi hcanon
  have hword :
      bytesStoreLitePacketLengthHeaderWord σ_evm I =
        bytesStoreLitePacketLengthHeaderWord σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨2⟩ ⟨0⟩
  have hslot :
      (σ_solm.find? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD ⟨2⟩ ⟨0⟩)) =
      (σ_evm.find? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD ⟨2⟩ ⟨0⟩)) := by
    simpa [bytesStoreLitePacketLengthHeaderWord] using hword.symm
  have hload :
      Solm.EVM.storageLoad
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        I.codeOwner ⟨2⟩ = bytesStoreLitePacketLengthHeaderWord σ_evm I := by
    simp [Solm.EVM.storageLoad, initState, State.lookupAccount, Account.lookupStorage,
      bytesStoreLitePacketLengthHeaderWord, hslot]
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
        I.codeOwner ⟨2⟩ = bytesStoreLitePacketLengthHeaderWord σ_evm I := by
    simpa [initState] using hload
  have hlen :
      readStorageBytesLength? bytesStoreLiteConfig
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        { base := "packet", steps := [.field "data"] } =
          .ok (UInt256.div (bytesStoreLitePacketLengthHeaderWord σ_evm I) ⟨2⟩).toNat := by
    simp [readStorageBytesLength?, storageNatResultToEval, bytesStoreLiteConfig,
      bytesStoreLiteStorageLayout, solidityStorageLayout, solidityReadBytesLength?,
      solidityDecodeBytesLengthHeader, bytesStoreLiteLayout, initState, hload', hflag, hvalid]
  have hbody :
      ExecTransitionBody bytesStoreLiteConfig bytesStoreLiteContract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (bytesStoreLiteSetPacketByteLocals I) setPacketByteTransition.body .reverted := by
    exact bytesStoreLiteSetPacketByteBodyBoundsRevertsOfLength
      (by simp only [initState]; exact hwv) hlen hbound
  exact (bytesStoreLiteX_setPacketByteOobLong
      (g := Sat256.ofUInt256 g) hreachBody hflag hvalid hbound)
    |>.reEquivExecutionRevert hcode hd hdec hbody

theorem bytesStoreLiteSetPacketByteOobShortRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x0a, 0xb2, 0x59, 0x00]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsz68 : 68 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (bytesStoreLiteSetByteValueWord I).toNat < EVM.twoPow 8)
    (hflag : UInt256.land (bytesStoreLitePacketLengthHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (bytesStoreLitePacketLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStoreLitePacketLengthHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩)
          ⟨32⟩) ≠ ⟨0⟩)
    (hbound :
      ¬ (bytesStoreLiteSetByteIndexWord I).toNat <
        (UInt256.land (UInt256.div (bytesStoreLitePacketLengthHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩).toNat) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsz := bytesStoreLiteSetPacketByteSelector_size hsel
  have hreach := bytesStoreLiteReachSetPacketByte (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz hsize hsel
  have hreachPc : ∃ k C, RD bytesStoreLiteBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨282⟩
      [bytesStoreLiteSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ_evm) k C := by
    simpa [bytesStoreLiteSetPacketByteEntryPc] using hreach
  have hreachBody := bytesStoreLiteX_setPacketByteDecodeValid
    (g := Sat256.ofUInt256 g) hreachPc hsz68 hhi hsize
    (bytesStoreLiteSetPacketByteLand255_eq_self_of_uint8 hcanon)
  have hd := bytesStoreLiteDispatch_setPacketByte (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec := bytesStoreLiteDecode_setPacketByte_locals (I := I) hsz68 hhi hcanon
  have hword :
      bytesStoreLitePacketLengthHeaderWord σ_evm I =
        bytesStoreLitePacketLengthHeaderWord σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨2⟩ ⟨0⟩
  have hslot :
      (σ_solm.find? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD ⟨2⟩ ⟨0⟩)) =
      (σ_evm.find? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD ⟨2⟩ ⟨0⟩)) := by
    simpa [bytesStoreLitePacketLengthHeaderWord] using hword.symm
  have hload :
      Solm.EVM.storageLoad
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        I.codeOwner ⟨2⟩ = bytesStoreLitePacketLengthHeaderWord σ_evm I := by
    simp [Solm.EVM.storageLoad, initState, State.lookupAccount, Account.lookupStorage,
      bytesStoreLitePacketLengthHeaderWord, hslot]
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
        I.codeOwner ⟨2⟩ = bytesStoreLitePacketLengthHeaderWord σ_evm I := by
    simpa [initState] using hload
  have hvalid0 :
      UInt256.sub ⟨0⟩
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStoreLitePacketLengthHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩)
          ⟨32⟩) ≠ ⟨0⟩ := by
    simpa [hflag] using hvalid
  have hlen :
      readStorageBytesLength? bytesStoreLiteConfig
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        { base := "packet", steps := [.field "data"] } =
          .ok (UInt256.land
            (UInt256.div (bytesStoreLitePacketLengthHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩).toNat := by
    simp [readStorageBytesLength?, storageNatResultToEval, bytesStoreLiteConfig,
      bytesStoreLiteStorageLayout, solidityStorageLayout, solidityReadBytesLength?,
      solidityDecodeBytesLengthHeader, bytesStoreLiteLayout, initState, hload', hflag, hvalid0]
  have hbody :
      ExecTransitionBody bytesStoreLiteConfig bytesStoreLiteContract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (bytesStoreLiteSetPacketByteLocals I) setPacketByteTransition.body .reverted := by
    exact bytesStoreLiteSetPacketByteBodyBoundsRevertsOfLength
      (by simp only [initState]; exact hwv) hlen hbound
  exact (bytesStoreLiteX_setPacketByteOobShort
      (g := Sat256.ofUInt256 g) hreachBody hflag hvalid hbound)
    |>.reEquivExecutionRevert hcode hd hdec hbody

theorem bytesStoreLiteSetPacketByteLongMalformedRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x0a, 0xb2, 0x59, 0x00]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsz68 : 68 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (bytesStoreLiteSetByteValueWord I).toNat < EVM.twoPow 8)
    (hflag : UInt256.land (bytesStoreLitePacketLengthHeaderWord σ_evm I) ⟨1⟩ ≠ ⟨0⟩)
    (hbad : UInt256.sub (UInt256.land (bytesStoreLitePacketLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStoreLitePacketLengthHeaderWord σ_evm I) ⟨2⟩) ⟨32⟩) = ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsz := bytesStoreLiteSetPacketByteSelector_size hsel
  have hreach := bytesStoreLiteReachSetPacketByte (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz hsize hsel
  have hreachPc : ∃ k C, RD bytesStoreLiteBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨282⟩
      [bytesStoreLiteSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ_evm) k C := by
    simpa [bytesStoreLiteSetPacketByteEntryPc] using hreach
  have hreachBody := bytesStoreLiteX_setPacketByteDecodeValid
    (g := Sat256.ofUInt256 g) hreachPc hsz68 hhi hsize
    (bytesStoreLiteSetPacketByteLand255_eq_self_of_uint8 hcanon)
  have hd := bytesStoreLiteDispatch_setPacketByte (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec := bytesStoreLiteDecode_setPacketByte_locals (I := I) hsz68 hhi hcanon
  have hword :
      bytesStoreLitePacketLengthHeaderWord σ_evm I =
        bytesStoreLitePacketLengthHeaderWord σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨2⟩ ⟨0⟩
  have hslot :
      (σ_solm.find? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD ⟨2⟩ ⟨0⟩)) =
      (σ_evm.find? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD ⟨2⟩ ⟨0⟩)) := by
    simpa [bytesStoreLitePacketLengthHeaderWord] using hword.symm
  have hload :
      Solm.EVM.storageLoad
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        I.codeOwner ⟨2⟩ = bytesStoreLitePacketLengthHeaderWord σ_evm I := by
    simp [Solm.EVM.storageLoad, initState, State.lookupAccount, Account.lookupStorage,
      bytesStoreLitePacketLengthHeaderWord, hslot]
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
        I.codeOwner ⟨2⟩ = bytesStoreLitePacketLengthHeaderWord σ_evm I := by
    simpa [initState] using hload
  have hlen :
      readStorageBytesLength? bytesStoreLiteConfig
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        { base := "packet", steps := [.field "data"] } = .revert := by
    simp [readStorageBytesLength?, storageNatResultToEval, bytesStoreLiteConfig,
      bytesStoreLiteStorageLayout, solidityStorageLayout, solidityReadBytesLength?,
      solidityDecodeBytesLengthHeader, bytesStoreLiteLayout, initState, hload', hflag, hbad]
  have hbody :
      ExecTransitionBody bytesStoreLiteConfig bytesStoreLiteContract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (bytesStoreLiteSetPacketByteLocals I) setPacketByteTransition.body .reverted := by
    exact bytesStoreLiteSetPacketByteBodyRevertsOfLengthRead
      (by simp only [initState]; exact hwv) hlen
  exact (bytesStoreLiteX_setPacketByteLongMalformed
      (g := Sat256.ofUInt256 g) hreachBody hflag hbad)
    |>.reEquivExecutionRevert hcode hd hdec hbody

theorem bytesStoreLiteSetPacketByteShortMalformedRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x0a, 0xb2, 0x59, 0x00]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsz68 : 68 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (bytesStoreLiteSetByteValueWord I).toNat < EVM.twoPow 8)
    (hflag : UInt256.land (bytesStoreLitePacketLengthHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩)
    (hbad : UInt256.sub (UInt256.land (bytesStoreLitePacketLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStoreLitePacketLengthHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩)
          ⟨32⟩) = ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsz := bytesStoreLiteSetPacketByteSelector_size hsel
  have hreach := bytesStoreLiteReachSetPacketByte (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz hsize hsel
  have hreachPc : ∃ k C, RD bytesStoreLiteBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨282⟩
      [bytesStoreLiteSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ_evm) k C := by
    simpa [bytesStoreLiteSetPacketByteEntryPc] using hreach
  have hreachBody := bytesStoreLiteX_setPacketByteDecodeValid
    (g := Sat256.ofUInt256 g) hreachPc hsz68 hhi hsize
    (bytesStoreLiteSetPacketByteLand255_eq_self_of_uint8 hcanon)
  have hd := bytesStoreLiteDispatch_setPacketByte (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec := bytesStoreLiteDecode_setPacketByte_locals (I := I) hsz68 hhi hcanon
  have hword :
      bytesStoreLitePacketLengthHeaderWord σ_evm I =
        bytesStoreLitePacketLengthHeaderWord σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨2⟩ ⟨0⟩
  have hslot :
      (σ_solm.find? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD ⟨2⟩ ⟨0⟩)) =
      (σ_evm.find? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD ⟨2⟩ ⟨0⟩)) := by
    simpa [bytesStoreLitePacketLengthHeaderWord] using hword.symm
  have hload :
      Solm.EVM.storageLoad
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        I.codeOwner ⟨2⟩ = bytesStoreLitePacketLengthHeaderWord σ_evm I := by
    simp [Solm.EVM.storageLoad, initState, State.lookupAccount, Account.lookupStorage,
      bytesStoreLitePacketLengthHeaderWord, hslot]
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
        I.codeOwner ⟨2⟩ = bytesStoreLitePacketLengthHeaderWord σ_evm I := by
    simpa [initState] using hload
  have hbad0 :
      UInt256.sub ⟨0⟩
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStoreLitePacketLengthHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩)
          ⟨32⟩) = ⟨0⟩ := by
    simpa [hflag] using hbad
  have hlen :
      readStorageBytesLength? bytesStoreLiteConfig
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        { base := "packet", steps := [.field "data"] } = .revert := by
    simp [readStorageBytesLength?, storageNatResultToEval, bytesStoreLiteConfig,
      bytesStoreLiteStorageLayout, solidityStorageLayout, solidityReadBytesLength?,
      solidityDecodeBytesLengthHeader, bytesStoreLiteLayout, initState, hload', hflag, hbad0]
  have hbody :
      ExecTransitionBody bytesStoreLiteConfig bytesStoreLiteContract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (bytesStoreLiteSetPacketByteLocals I) setPacketByteTransition.body .reverted := by
    exact bytesStoreLiteSetPacketByteBodyRevertsOfLengthRead
      (by simp only [initState]; exact hwv) hlen
  exact (bytesStoreLiteX_setPacketByteShortMalformed
      (g := Sat256.ofUInt256 g) hreachBody hflag hbad)
    |>.reEquivExecutionRevert hcode hd hdec hbody

theorem bytesStoreLiteSetPacketByteRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x0a, 0xb2, 0x59, 0x00]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  by_cases hsz68 : 68 ≤ I.calldata.size
  · by_cases hhi : I.calldata.size < 2 ^ 255 + 4
    · by_cases hcanon : (bytesStoreLiteSetByteValueWord I).toNat < EVM.twoPow 8
      · by_cases hflagLong :
          UInt256.land (bytesStoreLitePacketLengthHeaderWord σ_evm I) ⟨1⟩ ≠ ⟨0⟩
        · by_cases hvalidLong :
            UInt256.sub (UInt256.land (bytesStoreLitePacketLengthHeaderWord σ_evm I) ⟨1⟩)
              (UInt256.lt (UInt256.div (bytesStoreLitePacketLengthHeaderWord σ_evm I) ⟨2⟩)
                ⟨32⟩) ≠ ⟨0⟩
          · let len := UInt256.div (bytesStoreLitePacketLengthHeaderWord σ_evm I) ⟨2⟩
            by_cases hbound : (bytesStoreLiteSetByteIndexWord I).toNat < len.toNat
            · by_cases haccSome : ∃ accEvm, σ_evm.find? I.codeOwner = some accEvm
              · obtain ⟨accEvm, haccEq⟩ := haccSome
                exact bytesStoreLiteSetPacketByteLongSuccessRuntime
                  (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm)
                  (σ_solm := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
                  (len := len) (accEvm := accEvm)
                  hcode hsize hperm hwv hsel hAccounts haccEq hsz68 hhi hcanon
                  (by rfl) hbound hflagLong hvalidLong
              · have haccNone : σ_evm.find? I.codeOwner = none := by
                  cases haccEq : σ_evm.find? I.codeOwner with
                  | none => rfl
                  | some accEvm => exact False.elim (haccSome ⟨accEvm, haccEq⟩)
                have hhdr :
                    bytesStoreLitePacketLengthHeaderWord σ_evm I = ⟨0⟩ := by
                  simp [bytesStoreLitePacketLengthHeaderWord, haccNone, Option.option]
                have hflag0 :
                    UInt256.land (bytesStoreLitePacketLengthHeaderWord σ_evm I) ⟨1⟩ =
                      ⟨0⟩ := by
                  rw [hhdr]
                  native_decide
                exact False.elim (hflagLong hflag0)
            · exact bytesStoreLiteSetPacketByteOobLongRuntime
                (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm)
                (σ_solm := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
                hcode hsize hperm hwv hsel hAccounts hsz68 hhi hcanon hflagLong
                hvalidLong hbound
          · have hbad :
              UInt256.sub (UInt256.land (bytesStoreLitePacketLengthHeaderWord σ_evm I) ⟨1⟩)
                (UInt256.lt (UInt256.div (bytesStoreLitePacketLengthHeaderWord σ_evm I) ⟨2⟩)
                  ⟨32⟩) = ⟨0⟩ := by
              by_contra hne
              exact hvalidLong hne
            exact bytesStoreLiteSetPacketByteLongMalformedRuntime
              (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm)
              (σ_solm := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
              hcode hsize hperm hwv hsel hAccounts hsz68 hhi hcanon hflagLong hbad
        · have hflagShort :
            UInt256.land (bytesStoreLitePacketLengthHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩ := by
            by_contra hne
            exact hflagLong hne
          by_cases hvalidShort :
              UInt256.sub (UInt256.land (bytesStoreLitePacketLengthHeaderWord σ_evm I) ⟨1⟩)
                (UInt256.lt
                  (UInt256.land
                    (UInt256.div (bytesStoreLitePacketLengthHeaderWord σ_evm I) ⟨2⟩)
                    ⟨127⟩) ⟨32⟩) ≠ ⟨0⟩
          · let len :=
              UInt256.land
                (UInt256.div (bytesStoreLitePacketLengthHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩
            have hltNe : UInt256.lt len ⟨32⟩ ≠ ⟨0⟩ := by
              intro hlt0
              have hzero : UInt256.sub ⟨0⟩ ⟨0⟩ = (⟨0⟩ : UInt256) := by
                native_decide
              exact hvalidShort (by simpa [len, hflagShort, hlt0] using hzero)
            have hshort : len.toNat < 32 := by
              have hlt := ult_ne_zero_toNat_lt hltNe
              simpa using hlt
            by_cases hbound : (bytesStoreLiteSetByteIndexWord I).toNat < len.toNat
            · by_cases haccSome : ∃ accEvm, σ_evm.find? I.codeOwner = some accEvm
              · obtain ⟨accEvm, haccEq⟩ := haccSome
                exact bytesStoreLiteSetPacketByteShortSuccessRuntime
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
                    bytesStoreLitePacketLengthHeaderWord σ_evm I = ⟨0⟩ := by
                  simp [bytesStoreLitePacketLengthHeaderWord, haccNone, Option.option]
                have hlenZero : len = ⟨0⟩ := by
                  change
                    UInt256.land
                      (UInt256.div (bytesStoreLitePacketLengthHeaderWord σ_evm I) ⟨2⟩)
                      ⟨127⟩ = ⟨0⟩
                  rw [hhdr]
                  native_decide
                have hlen0 : len.toNat = 0 := by
                  simp [hlenZero]
                have hbadBound : (bytesStoreLiteSetByteIndexWord I).toNat < 0 := by
                  simpa [hlen0] using hbound
                exact False.elim (Nat.not_lt_zero _ hbadBound)
            · exact bytesStoreLiteSetPacketByteOobShortRuntime
                (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm)
                (σ_solm := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
                hcode hsize hperm hwv hsel hAccounts hsz68 hhi hcanon hflagShort
                hvalidShort hbound
          · have hbad :
              UInt256.sub (UInt256.land (bytesStoreLitePacketLengthHeaderWord σ_evm I) ⟨1⟩)
                (UInt256.lt
                  (UInt256.land
                    (UInt256.div (bytesStoreLitePacketLengthHeaderWord σ_evm I) ⟨2⟩)
                    ⟨127⟩) ⟨32⟩) = ⟨0⟩ := by
              by_contra hne
              exact hvalidShort hne
            exact bytesStoreLiteSetPacketByteShortMalformedRuntime
              (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm)
              (σ_solm := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
              hcode hsize hperm hwv hsel hAccounts hsz68 hhi hcanon hflagShort hbad
      · exact bytesStoreLiteSetPacketByteDecodeNoncanonValueRuntime
          (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
          (σ₀ := σ₀) (A := A) (I := I) (g := g)
          hcode hsize hperm hwv hsel hAccounts hsz68 hhi hcanon
    · exact bytesStoreLiteSetPacketByteDecodeHugeRuntime
        (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
        (σ₀ := σ₀) (A := A) (I := I) (g := g)
        hcode hsize hperm hwv hsel hAccounts (by omega)
  · exact bytesStoreLiteSetPacketByteDecodeShortRuntime
      (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
      (σ₀ := σ₀) (A := A) (I := I) (g := g)
      hcode hsize hperm hwv hsel hAccounts (by omega)

end BytesStoreLite
