import Benchmarks.Dss.Flipper.Bytecode
import Reasoning.ABI
import Reasoning.Theory
import Reasoning.Stepping
import Reasoning.Reach
import Reasoning.Solc
import Reasoning.Memory
import Reasoning.Storage
import Reasoning.Dispatch
import Reasoning.SolmBody
import Mathlib.Tactic.IntervalCases
import Solm.Equiv

/-!
# MakerDAO/Sky DSS Flipper shared proof foundation

Contract-wide selector notation and constants for the optimized Flipper runtime.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace Benchmarks.Dss.Flipper

/-- The 4-byte selector word computed by `CALLDATALOAD(0); SHR 224`. -/
abbrev flipperSelWord (I : ExecutionEnv) : UInt256 :=
  UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩

/-- The 4-byte selector of `I`'s calldata equals `sel`. -/
abbrev selIs (I : ExecutionEnv) (sel : ByteArray) : Prop :=
  (sel == I.calldata.extract 0 4) = true

/-- Function selectors in `contract.transitions` order. -/
def flipperSelBytes : ℕ → ByteArray
  | 0 => ⟨#[0x7d, 0x78, 0x0d, 0x82]⟩  -- beg()
  | 1 => ⟨#[0x44, 0x23, 0xc5, 0xf1]⟩  -- bids(uint256)
  | 2 => ⟨#[0xe4, 0x88, 0x18, 0x13]⟩  -- cat()
  | 3 => ⟨#[0xc9, 0x59, 0xc4, 0x2b]⟩  -- deal(uint256)
  | 4 => ⟨#[0x5f, 0xf3, 0xa3, 0x82]⟩  -- dent(uint256,uint256,uint256)
  | 5 => ⟨#[0x9c, 0x52, 0xa7, 0xf1]⟩  -- deny(address)
  | 6 => ⟨#[0xd4, 0xe8, 0xbe, 0x83]⟩  -- file(bytes32,address)
  | 7 => ⟨#[0x29, 0xae, 0x81, 0x14]⟩  -- file(bytes32,uint256)
  | 8 => ⟨#[0xc5, 0xce, 0x28, 0x1e]⟩  -- ilk()
  | 9 => ⟨#[0x35, 0x1d, 0xe6, 0x00]⟩  -- kick(address,address,uint256,uint256,uint256)
  | 10 => ⟨#[0xcf, 0xdd, 0x33, 0x02]⟩ -- kicks()
  | 11 => ⟨#[0x65, 0xfa, 0xe3, 0x5e]⟩ -- rely(address)
  | 12 => ⟨#[0xcf, 0xc4, 0xaf, 0x55]⟩ -- tau()
  | 13 => ⟨#[0x4b, 0x43, 0xed, 0x12]⟩ -- tend(uint256,uint256,uint256)
  | 14 => ⟨#[0xfc, 0x7b, 0x6a, 0xee]⟩ -- tick(uint256)
  | 15 => ⟨#[0x4e, 0x8b, 0x1d, 0xd5]⟩ -- ttl()
  | 16 => ⟨#[0x36, 0x56, 0x9e, 0x77]⟩ -- vat()
  | 17 => ⟨#[0xbf, 0x35, 0x3d, 0xbb]⟩ -- wards(address)
  | _ => ⟨#[0x26, 0xe0, 0x27, 0xf1]⟩  -- yank(uint256)

def flipperSlotWord (slot : UInt256) (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  solcSlotWord σ I slot

theorem flipperDecodeCalldataLegacyUInt256_ok {cd : ByteArray} {x : Solm.Ident}
    (hsz36 : 36 ≤ cd.size) :
    decodeCalldataWithMode DecodeMode.legacySolc05 [x] [abiUInt256] cd =
      some ((∅ : Store).insert x (.int (Int.ofNat (calldataWord cd 4).toNat))) := by
  have hlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have htake4 : ((cd.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, hlen]
    omega
  have hword4 : ABI.bytesToWord ((cd.toList.drop 4).take 32) = calldataWord cd 4 :=
    decode_word_at_eq cd 4 (by omega) (by norm_num)
  rw [decodeCalldataWithMode_legacyScalarWords_eq (names := [x]) (types := [abiUInt256])
    (cd := cd) (by decide)]
  rw [if_neg (by rw [hlen]; omega : ¬ cd.toList.length < 4)]
  simp only [decodeScalarWordsWithMode?]
  rw [decodeScalarWordWithMode_uint256_ok (mode := DecodeMode.legacySolc05)
    (bytes := cd.toList.drop 4) (start := 0) htake4]
  change decodeCalldata.insertValues [x]
      [.int (Int.ofNat (ABI.bytesToWord ((cd.toList.drop 4).take 32)).toNat)] ∅ =
    some ((∅ : Store).insert x (.int (Int.ofNat (calldataWord cd 4).toNat)))
  simp [decodeCalldata.insertValues, hword4]

theorem flipperDecodeCalldataLegacyUInt256_none_short {cd : ByteArray} {x : Solm.Ident}
    (hsz4 : 4 ≤ cd.size) (hshort : cd.size < 36) :
    decodeCalldataWithMode DecodeMode.legacySolc05 [x] [abiUInt256] cd = none := by
  have hlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  rw [decodeCalldataWithMode_legacyScalarWords_eq (names := [x]) (types := [abiUInt256])
    (cd := cd) (by decide)]
  rw [if_neg (by rw [hlen]; omega : ¬ cd.toList.length < 4)]
  simp only [decodeScalarWordsWithMode?]
  have htake0n : ¬ ((cd.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, hlen]
    omega
  rw [decodeScalarWordWithMode_uint256_none_short (mode := DecodeMode.legacySolc05)
    (start := 0) (by simpa using htake0n)]
  simp only [Option.bind, bind]

theorem flipperDecodeCalldataLegacyUInt256UInt256UInt256_ok {cd : ByteArray}
    {x y z : Solm.Ident} (hsz100 : 100 ≤ cd.size) :
    decodeCalldataWithMode DecodeMode.legacySolc05 [x, y, z]
        [abiUInt256, abiUInt256, abiUInt256] cd =
      some ((((∅ : Store).insert x (.int (Int.ofNat (calldataWord cd 4).toNat))).insert y
        (.int (Int.ofNat (calldataWord cd 36).toNat))).insert z
        (.int (Int.ofNat (calldataWord cd 68).toNat))) := by
  have hlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have htake4 : ((cd.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, hlen]
    omega
  have htake36 : ((cd.toList.drop 4).drop 32 |>.take 32).length = 32 := by
    rw [List.length_take, List.length_drop, List.length_drop, hlen]
    omega
  have htake68 : ((cd.toList.drop 4).drop 64 |>.take 32).length = 32 := by
    rw [List.length_take, List.length_drop, List.length_drop, hlen]
    omega
  have hword4 : ABI.bytesToWord ((cd.toList.drop 4).take 32) = calldataWord cd 4 :=
    decode_word_at_eq cd 4 (by omega) (by norm_num)
  have hword36 :
      ABI.bytesToWord (((cd.toList.drop 4).drop 32).take 32) = calldataWord cd 36 := by
    simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
      using decode_word_at_eq cd 36 (by omega) (by norm_num)
  have hword68 :
      ABI.bytesToWord (((cd.toList.drop 4).drop 64).take 32) = calldataWord cd 68 := by
    simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
      using decode_word_at_eq cd 68 (by omega) (by norm_num)
  rw [decodeCalldataWithMode_legacyScalarWords_eq (names := [x, y, z])
    (types := [abiUInt256, abiUInt256, abiUInt256]) (cd := cd) (by decide)]
  rw [if_neg (by rw [hlen]; omega : ¬ cd.toList.length < 4)]
  simp only [decodeScalarWordsWithMode?]
  rw [decodeScalarWordWithMode_uint256_ok (mode := DecodeMode.legacySolc05)
    (bytes := cd.toList.drop 4) (start := 0) htake4]
  rw [decodeScalarWordWithMode_uint256_ok (mode := DecodeMode.legacySolc05)
    (bytes := cd.toList.drop 4) (start := 32) htake36]
  rw [decodeScalarWordWithMode_uint256_ok (mode := DecodeMode.legacySolc05)
    (bytes := cd.toList.drop 4) (start := 64) htake68]
  simp only [Option.bind, bind]
  change decodeCalldata.insertValues [x, y, z]
      [.int (Int.ofNat (ABI.bytesToWord ((cd.toList.drop 4).take 32)).toNat),
        .int (Int.ofNat (ABI.bytesToWord (((cd.toList.drop 4).drop 32).take 32)).toNat),
        .int (Int.ofNat (ABI.bytesToWord (((cd.toList.drop 4).drop 64).take 32)).toNat)] ∅ =
    some ((((∅ : Store).insert x (.int (Int.ofNat (calldataWord cd 4).toNat))).insert y
      (.int (Int.ofNat (calldataWord cd 36).toNat))).insert z
      (.int (Int.ofNat (calldataWord cd 68).toNat)))
  rw [hword4, hword36, hword68]
  simp [decodeCalldata.insertValues]

theorem flipperDecodeCalldataLegacyUInt256UInt256UInt256_none_short {cd : ByteArray}
    {x y z : Solm.Ident} (hsz4 : 4 ≤ cd.size) (hshort : cd.size < 100) :
    decodeCalldataWithMode DecodeMode.legacySolc05 [x, y, z]
      [abiUInt256, abiUInt256, abiUInt256] cd = none := by
  have hlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  rw [decodeCalldataWithMode_legacyScalarWords_eq (names := [x, y, z])
    (types := [abiUInt256, abiUInt256, abiUInt256]) (cd := cd) (by decide)]
  rw [if_neg (by rw [hlen]; omega : ¬ cd.toList.length < 4)]
  by_cases hlen0 : 32 ≤ (cd.toList.drop 4).length
  · have htake0 : ((cd.toList.drop 4).take 32).length = 32 := by
      rw [List.length_take]
      omega
    simp only [decodeScalarWordsWithMode?]
    rw [decodeScalarWordWithMode_uint256_ok (mode := DecodeMode.legacySolc05)
      (bytes := cd.toList.drop 4) (start := 0) htake0]
    by_cases hlen32 : 64 ≤ (cd.toList.drop 4).length
    · have htake32 : (((cd.toList.drop 4).drop 32).take 32).length = 32 := by
        rw [List.length_take, List.length_drop]
        omega
      rw [decodeScalarWordWithMode_uint256_ok (mode := DecodeMode.legacySolc05)
        (bytes := cd.toList.drop 4) (start := 32) htake32]
      have htake64n : ¬ (((cd.toList.drop 4).drop 64).take 32).length = 32 := by
        rw [List.length_take, List.length_drop, List.length_drop, hlen]
        omega
      rw [decodeScalarWordWithMode_uint256_none_short (mode := DecodeMode.legacySolc05)
        (start := 64) (by simpa using htake64n)]
      simp only [Option.bind, bind]
    · have htake32n : ¬ (((cd.toList.drop 4).drop 32).take 32).length = 32 := by
        rw [List.length_take, List.length_drop]
        omega
      rw [decodeScalarWordWithMode_uint256_none_short (mode := DecodeMode.legacySolc05)
        (start := 32) (by simpa using htake32n)]
      simp only [Option.bind, bind]
  · have htake0n : ¬ ((cd.toList.drop 4).take 32).length = 32 := by
      rw [List.length_take]
      omega
    simp only [decodeScalarWordsWithMode?]
    rw [decodeScalarWordWithMode_uint256_none_short (mode := DecodeMode.legacySolc05)
      (start := 0) (by simpa using htake0n)]
    simp only [Option.bind, bind]

abbrev flipperAddressReturnWord (slot : UInt256) (σ : AccountMap) (I : ExecutionEnv) :
    UInt256 :=
  UInt256.land (flipperSlotWord slot σ I) solcAddrMask

def uint48Mask : UInt256 := ⟨281474976710655⟩

def uint48Divisor : UInt256 := ⟨281474976710656⟩

abbrev flipperUint48Offset0Word (slot : UInt256) (σ : AccountMap) (I : ExecutionEnv) :
    UInt256 :=
  UInt256.land (flipperSlotWord slot σ I) uint48Mask

abbrev flipperUint48Offset6Word (slot : UInt256) (σ : AccountMap) (I : ExecutionEnv) :
    UInt256 :=
  UInt256.land (UInt256.div (flipperSlotWord slot σ I) uint48Divisor) uint48Mask

theorem uint48Mask_toNat :
    uint48Mask.toNat = 256 ^ 6 - 1 := by
  native_decide

theorem uint48Mask_bound (w : UInt256) :
    (UInt256.land w uint48Mask).toNat < EVM.twoPow 48 := by
  rw [uland_toNat, uint48Mask_toNat]
  exact lt_of_le_of_lt (nat_land_le_right _ _) (by norm_num [EVM.twoPow])

theorem uint48Mask_clean {w : UInt256} (hcanon : w.toNat < EVM.twoPow 48) :
    UInt256.land w uint48Mask = w := by
  apply u256_inj
  show Nat.land w.toNat uint48Mask.toNat % EVM.twoPow 256 = w.toNat
  rw [uint48Mask_toNat]
  rw [show 256 ^ 6 = 2 ^ 48 by norm_num, nat_land_mask_eq_mod]
  have hmodlt : w.toNat % 2 ^ 48 < EVM.twoPow 256 :=
    lt_trans (Nat.mod_lt _ (by norm_num : 0 < 2 ^ 48)) (by norm_num [EVM.twoPow])
  rw [Nat.mod_eq_of_lt hmodlt]
  exact Nat.mod_eq_of_lt (by simpa [EVM.twoPow] using hcanon)

theorem uint48Mask_toNat_mod (w : UInt256) :
    (UInt256.land w uint48Mask).toNat = w.toNat % 2 ^ 48 := by
  rw [uland_toNat, uint48Mask_toNat]
  rw [show 256 ^ 6 = 2 ^ 48 by norm_num]
  change Nat.land w.toNat (2 ^ 48 - 1) = w.toNat % 2 ^ 48
  exact nat_land_mask_eq_mod w.toNat 48

theorem uint48ReturnEncodingMasked (w : UInt256) :
    encodeReturnValue? uint48
        (.int (Int.ofNat (UInt256.land w uint48Mask).toNat)) =
      some (UInt256.toByteArray (UInt256.land w uint48Mask)) := by
  have hword : EVM.word (UInt256.land w uint48Mask).toNat =
      UInt256.land w uint48Mask := by
    show UInt256.ofNat (UInt256.land w uint48Mask).toNat =
      UInt256.land w uint48Mask
    exact u256_ofNat_toNat _
  refine scalarReturnEncoding (t := (.int (.uint ⟨48, by decide⟩)))
    (w := UInt256.land w uint48Mask) rfl ?_ ?_
  · simp only [abiTupleHeadSize?, staticABIEncodedSize?, isDynamicABIType, bind, Option.bind]
    decide
  · simp [encodeABIValue?, encodeABIWord?, hword, uint48Mask_bound w]

theorem flipperStorageLocLoad_address_offset0 (evm : EVM.State) (slot : UInt256) :
    storageLocLoad evm (addrLoc slot) =
      .address (AccountAddress.ofNat
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)
          solcAddrMask).toNat) := by
  simpa [addrLoc, addressOffset0Loc] using storageLocLoad_address_offset0 evm slot

theorem flipperStorageLocLoad_uint256 (evm : EVM.State) (slot : UInt256) :
    storageLocLoad evm (wordLoc slot) =
      .int (Int.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot).toNat) := by
  simpa [wordLoc, uint256Loc] using storageLocLoad_uint256 evm slot

theorem flipperStorageLocStore_uint256 (evm : EVM.State) (slot val : UInt256) :
    storageLocStore evm (wordLoc slot) (.int (Int.ofNat val.toNat)) =
      some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot val) := by
  simpa [wordLoc, uint256Loc] using storageLocStore_uint256 evm slot val

theorem flipperStorageLocLoad_bytes32 (evm : EVM.State) (slot : UInt256) :
    storageLocLoad evm (bytes32Loc slot) =
      .fixedBytes bytes32Width
        (EVM.Word.toBytesBE (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)) := by
  simpa [bytes32Loc, Reasoning.Theory.bytes32Loc, bytes32Width] using
    storageLocLoad_bytes32 evm slot

theorem flipperStorageLocLoad_uint48_offset0 (evm : EVM.State) (slot : UInt256) :
    storageLocLoad evm (uint48Loc slot ⟨0, by decide⟩ (by decide)) =
      .int (Int.ofNat (UInt256.land
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot) uint48Mask).toNat) := by
  have h := storageLocLoad_uint_offset0 (evm := evm) (slot := slot)
    (size := (⟨6, by decide⟩ : Fin 33)) (width := (⟨48, by decide⟩ : ABI.BitWidth))
    (hbound := by decide)
    (hbits := by decide)
  have hmask : UInt256.ofNat (2 ^ (8 * (⟨6, by decide⟩ : Fin 33).val) - 1) =
      uint48Mask := by
    native_decide
  simpa [uint48Loc, uint48Int, hmask] using h

theorem flipperStorageLocLoad_uint48_offset6 (evm : EVM.State) (slot : UInt256) :
    storageLocLoad evm (uint48Loc slot ⟨6, by decide⟩ (by decide)) =
      .int (Int.ofNat (UInt256.land
        (UInt256.div (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)
          uint48Divisor) uint48Mask).toNat) := by
  have h := storageLocLoad_uint_offset (evm := evm) (slot := slot)
    (offset := ⟨6, by decide⟩) (size := (⟨6, by decide⟩ : Fin 33))
    (width := (⟨48, by decide⟩ : ABI.BitWidth)) (hbound := by decide)
    (hoff := by decide) (hsize := by decide)
  have hmask : UInt256.ofNat (256 ^ (⟨6, by decide⟩ : Fin 33).val - 1) =
      uint48Mask := by
    native_decide
  have hdiv : UInt256.ofNat (256 ^ (⟨6, by decide⟩ : Fin 32).val) =
      uint48Divisor := by
    native_decide
  simpa [uint48Loc, uint48Int, hmask, hdiv] using h

abbrev setUint48Offset0Word (old val : UInt256) : UInt256 :=
  UInt256.lor (UInt256.land old (UInt256.lnot uint48Mask))
    (UInt256.land val uint48Mask)

theorem setUint48Offset0Word_toNat (old val : UInt256) (hval : val.toNat < 2 ^ 48) :
    (setUint48Offset0Word old val).toNat =
      val.toNat + 2 ^ 48 * (old.toNat / 2 ^ 48) := by
  unfold setUint48Offset0Word
  rw [u256_lor_toNat]
  have hhigh :
      (UInt256.land old (UInt256.lnot uint48Mask)).toNat =
        (old.toNat / 2 ^ 48) * 2 ^ 48 := by
    rw [show UInt256.lnot uint48Mask = UInt256.ofNat ((2 : Nat) ^ 256 - 2 ^ 48) by
      native_decide]
    rw [u256_land_comm]
    exact u256_land_high_mask_toNat old 48 (by norm_num)
  have hlow : (UInt256.land val uint48Mask).toNat = val.toNat := by
    rw [u256_land_toNat]
    change Nat.land val.toNat (2 ^ 48 - 1) % UInt256.size = val.toNat
    rw [nat_land_mask_eq_mod]
    rw [Nat.mod_eq_of_lt hval]
    exact Nat.mod_eq_of_lt val.val.isLt
  rw [hhigh]
  have hlowLt : (UInt256.land val uint48Mask).toNat < 2 ^ 48 := by
    rw [hlow]
    exact hval
  rw [nat_lor_comm]
  rw [nat_lor_shift_add (UInt256.land val uint48Mask).toNat (old.toNat / 2 ^ 48)
    48 hlowLt]
  rw [hlow]
  have hlt : val.toNat + old.toNat / 2 ^ 48 * 2 ^ 48 < UInt256.size := by
    have hq : old.toNat / 2 ^ 48 < 2 ^ 208 := by
      apply Nat.div_lt_of_lt_mul
      rw [show 2 ^ 48 * 2 ^ 208 = (2 : Nat) ^ 256 by norm_num [Nat.pow_add]]
      exact old.val.isLt
    have hqle : old.toNat / 2 ^ 48 ≤ 2 ^ 208 - 1 := Nat.le_pred_of_lt hq
    have hle : old.toNat / 2 ^ 48 * 2 ^ 48 ≤ (2 ^ 208 - 1) * 2 ^ 48 :=
      Nat.mul_le_mul_right _ hqle
    norm_num [UInt256.size] at hval hle ⊢
    omega
  rw [Nat.mod_eq_of_lt hlt]
  rw [Nat.mul_comm]

theorem flipperStorageLocStore_uint48_offset0 (evm : EVM.State) (slot val : UInt256)
    (hval : val.toNat < 2 ^ 48) :
    storageLocStore evm (uint48Loc slot ⟨0, by decide⟩ (by decide))
      (.int (Int.ofNat val.toNat)) =
      some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot
        (setUint48Offset0Word (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot) val)) := by
  unfold storageLocStore storageLocWriteWord uint48Loc
  simp only [valueToWord, wordOfInt_ofNat_toNat, bind, Option.bind, pure]
  congr 2
  apply u256_inj
  show fromBytes'
      (List.take (0 : Fin 32).val _ ++ List.take (6 : Fin 33).val _
        ++ List.drop ((0 : Fin 32).val + (6 : Fin 33).val) _) =
      (setUint48Offset0Word (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)
        val).toNat
  rw [show (0 : Fin 32).val = 0 from rfl, show (6 : Fin 33).val = 6 from rfl,
    List.take_zero, List.nil_append]
  rw [fromBytes'_append, fromBytes'_take_wordLE, fromBytes'_drop_wordLE]
  have hwordToNat :=
    setUint48Offset0Word_toNat
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot) val hval
  rw [hwordToNat]
  rw [List.length_take, (EVM.Word.toBytesLEWithSizeProof val).2]
  norm_num [Nat.pow_add]
  ring_nf
  all_goals
    rw [← show (2 : Nat) ^ 48 = 281474976710656 by norm_num]
    exact hval

theorem natLandClearMiddle48_96 (n : Nat) (hn : n < 2 ^ 256) :
    Nat.land n ((2 : Nat) ^ 256 - 2 ^ 96 + 2 ^ 48 - 1) =
      n % 2 ^ 48 + (n / 2 ^ 96) * 2 ^ 96 := by
  apply Nat.eq_of_testBit_eq
  intro i
  change (n &&& ((2 : Nat) ^ 256 - 2 ^ 96 + 2 ^ 48 - 1)).testBit i =
    (n % 2 ^ 48 + n / 2 ^ 96 * 2 ^ 96).testBit i
  have hmask :
      (2 : Nat) ^ 256 - 2 ^ 96 + 2 ^ 48 - 1 =
        Nat.lor (2 ^ 48 - 1) ((2 ^ 160 - 1) <<< 96) := by
    rw [Nat.shiftLeft_eq]
    rw [nat_lor_shift_add (2 ^ 48 - 1) (2 ^ 160 - 1) 96]
    · norm_num [Nat.pow_add]
    · norm_num
  have hrhs :
      n % 2 ^ 48 + n / 2 ^ 96 * 2 ^ 96 =
        Nat.lor (n % 2 ^ 48) ((n / 2 ^ 96) * 2 ^ 96) := by
    rw [nat_lor_shift_add (n % 2 ^ 48) (n / 2 ^ 96) 96]
    · exact (Nat.mod_lt _ (by positivity : 0 < 2 ^ 48)).trans_le (by norm_num)
  rw [hmask, hrhs]
  rw [Nat.testBit_and]
  change (n.testBit i && (((2 ^ 48 - 1) ||| ((2 ^ 160 - 1) <<< 96)).testBit i)) =
    (((n % 2 ^ 48) ||| (n / 2 ^ 96 * 2 ^ 96)).testBit i)
  rw [Nat.testBit_or, Nat.testBit_or]
  rw [Nat.testBit_two_pow_sub_one, Nat.testBit_mod_two_pow]
  rw [show (n / 2 ^ 96) * 2 ^ 96 = (n / 2 ^ 96) <<< 96 by rw [Nat.shiftLeft_eq]]
  rw [testBit_shiftLeft, testBit_shiftLeft]
  by_cases hi48 : i < 48
  · have hi96 : i < 96 := by omega
    simp [hi48, hi96]
  · have hnot48 : ¬ i < 48 := hi48
    by_cases hi96 : i < 96
    · simp [hnot48, hi96]
    · have h96le : 96 ≤ i := Nat.le_of_not_gt hi96
      by_cases hi256 : i < 256
      · have hlt160 : i - 96 < 160 := by omega
        have hmaskBit :
            Nat.testBit 1461501637330902918203684832716283019655932542975
              (i - 96) = true := by
          change Nat.testBit (2 ^ 160 - 1) (i - 96) = true
          rw [Nat.testBit_two_pow_sub_one]
          simp [hlt160]
        simp [hnot48, hi96, hmaskBit]
        exact (divPow_testBit n 96 i h96le).symm
      · have hnot160 : ¬ i - 96 < 160 := by omega
        have hmaskBit :
            Nat.testBit 1461501637330902918203684832716283019655932542975
              (i - 96) = false := by
          change Nat.testBit (2 ^ 160 - 1) (i - 96) = false
          rw [Nat.testBit_two_pow_sub_one]
          simp [hnot160]
        simp [hnot48, hi96, hmaskBit]
        have hq : n / 2 ^ 96 < 2 ^ 160 := by
          apply Nat.div_lt_of_lt_mul
          rw [show 2 ^ 96 * 2 ^ 160 = (2 : Nat) ^ 256 by
            rw [← Nat.pow_add]]
          exact hn
        exact Nat.testBit_lt_two_pow
          (lt_of_lt_of_le hq (Nat.pow_le_pow_right (by norm_num) (by omega)))

abbrev setUint48Offset6Word (old val : UInt256) : UInt256 :=
  UInt256.lor
    (UInt256.land old (UInt256.lnot (UInt256.shiftLeft uint48Mask ⟨48⟩)))
    (UInt256.shiftLeft (UInt256.land val uint48Mask) ⟨48⟩)

theorem setUint48Offset6Word_toNat (old val : UInt256) (hval : val.toNat < 2 ^ 48) :
    (setUint48Offset6Word old val).toNat =
      old.toNat % 2 ^ 48 + val.toNat * 2 ^ 48 +
        (old.toNat / 2 ^ 96) * 2 ^ 96 := by
  unfold setUint48Offset6Word
  have hclearMask :
      UInt256.lnot (UInt256.shiftLeft uint48Mask ⟨48⟩) =
        UInt256.ofNat ((2 : Nat) ^ 256 - 2 ^ 96 + 2 ^ 48 - 1) := by
    native_decide
  have hvalLow : (UInt256.land val uint48Mask).toNat = val.toNat := by
    rw [u256_land_toNat]
    change Nat.land val.toNat (2 ^ 48 - 1) % UInt256.size = val.toNat
    rw [nat_land_mask_eq_mod]
    rw [Nat.mod_eq_of_lt hval]
    exact Nat.mod_eq_of_lt val.val.isLt
  have hshiftToNat :
      (UInt256.shiftLeft (UInt256.land val uint48Mask) ⟨48⟩).toNat =
        val.toNat * 2 ^ 48 := by
    unfold UInt256.shiftLeft
    rw [if_neg (by decide : ¬ ((⟨48⟩ : UInt256).val ≥ 256))]
    change (((UInt256.land val uint48Mask).toNat <<< 48) % UInt256.size) =
      val.toNat * 2 ^ 48
    rw [hvalLow, Nat.shiftLeft_eq]
    have hlt : val.toNat * 2 ^ 48 < UInt256.size := by
      calc
        val.toNat * 2 ^ 48 < 2 ^ 48 * 2 ^ 48 :=
          Nat.mul_lt_mul_of_pos_right hval (by norm_num)
        _ < UInt256.size := by norm_num [UInt256.size, Nat.pow_add]
    exact Nat.mod_eq_of_lt hlt
  have hclearToNat :
      (UInt256.land old (UInt256.lnot (UInt256.shiftLeft uint48Mask ⟨48⟩))).toNat =
        old.toNat % 2 ^ 48 + (old.toNat / 2 ^ 96) * 2 ^ 96 := by
    rw [hclearMask, u256_land_toNat]
    have hmaskLt :
        (2 : Nat) ^ 256 - 2 ^ 96 + 2 ^ 48 - 1 < UInt256.size := by
      norm_num [UInt256.size]
    rw [ulit_toNat' _ hmaskLt]
    rw [natLandClearMiddle48_96 old.toNat old.val.isLt]
    have hlt :
        old.toNat % 2 ^ 48 + old.toNat / 2 ^ 96 * 2 ^ 96 < UInt256.size := by
      have hlow : old.toNat % 2 ^ 48 < 2 ^ 48 := Nat.mod_lt _ (by positivity)
      have hq : old.toNat / 2 ^ 96 < 2 ^ 160 := by
        apply Nat.div_lt_of_lt_mul
        rw [show 2 ^ 96 * 2 ^ 160 = (2 : Nat) ^ 256 by rw [← Nat.pow_add]]
        exact old.val.isLt
      have hlowLe : old.toNat % 2 ^ 48 ≤ 2 ^ 48 - 1 := Nat.le_pred_of_lt hlow
      have hqLe : old.toNat / 2 ^ 96 ≤ 2 ^ 160 - 1 := Nat.le_pred_of_lt hq
      have hhighLe : old.toNat / 2 ^ 96 * 2 ^ 96 ≤ (2 ^ 160 - 1) * 2 ^ 96 :=
        Nat.mul_le_mul_right _ hqLe
      norm_num [UInt256.size, Nat.pow_add] at hlowLe hhighLe ⊢
      omega
    rw [Nat.mod_eq_of_lt hlt]
  rw [u256_lor_toNat, hclearToNat, hshiftToNat]
  let low := old.toNat % 2 ^ 48
  let mid := val.toNat * 2 ^ 48
  let high := old.toNat / 2 ^ 96 * 2 ^ 96
  have hlowLt : low < 2 ^ 48 := by
    exact Nat.mod_lt _ (by positivity)
  have hlowLt96 : low < 2 ^ 96 := lt_of_lt_of_le hlowLt (by norm_num)
  have hmidLt96 : mid < 2 ^ 96 := by
    calc
      mid = val.toNat * 2 ^ 48 := rfl
      _ < 2 ^ 48 * 2 ^ 48 := Nat.mul_lt_mul_of_pos_right hval (by norm_num)
      _ = 2 ^ 96 := by norm_num [Nat.pow_add]
  have hclearLor : low + high = Nat.lor low high := by
    rw [nat_lor_shift_add low (old.toNat / 2 ^ 96) 96 hlowLt96]
  have hmidHighLor : Nat.lor mid high = mid + high := by
    rw [nat_lor_shift_add mid (old.toNat / 2 ^ 96) 96 hmidLt96]
  have hlor :
      Nat.lor (low + high) mid = low + mid + high := by
    rw [hclearLor]
    change ((low ||| high) ||| mid) = low + mid + high
    rw [Nat.lor_assoc]
    rw [show high ||| mid = mid ||| high from nat_lor_comm high mid]
    rw [show mid ||| high = mid + high from hmidHighLor]
    have hfactor : mid + high =
        (val.toNat + old.toNat / 2 ^ 96 * 2 ^ 48) * 2 ^ 48 := by
      dsimp [mid, high]
      ring
    rw [hfactor]
    rw [show low ||| ((val.toNat + old.toNat / 2 ^ 96 * 2 ^ 48) * 2 ^ 48) =
        low + ((val.toNat + old.toNat / 2 ^ 96 * 2 ^ 48) * 2 ^ 48) from
      nat_lor_shift_add low (val.toNat + old.toNat / 2 ^ 96 * 2 ^ 48) 48 hlowLt]
    rw [← hfactor]
    ring
  rw [show old.toNat % 2 ^ 48 + old.toNat / 2 ^ 96 * 2 ^ 96 = low + high from rfl]
  rw [show val.toNat * 2 ^ 48 = mid from rfl]
  rw [hlor]
  have hlt : low + mid + high < UInt256.size := by
    have hq : old.toNat / 2 ^ 96 < 2 ^ 160 := by
      apply Nat.div_lt_of_lt_mul
      rw [show 2 ^ 96 * 2 ^ 160 = (2 : Nat) ^ 256 by rw [← Nat.pow_add]]
      exact old.val.isLt
    have hlowLe : low ≤ 2 ^ 48 - 1 := Nat.le_pred_of_lt hlowLt
    have hvalLe : val.toNat ≤ 2 ^ 48 - 1 := Nat.le_pred_of_lt hval
    have hqLe : old.toNat / 2 ^ 96 ≤ 2 ^ 160 - 1 := Nat.le_pred_of_lt hq
    have hmidLe : mid ≤ (2 ^ 48 - 1) * 2 ^ 48 :=
      Nat.mul_le_mul_right _ hvalLe
    have hhighLe : high ≤ (2 ^ 160 - 1) * 2 ^ 96 :=
      Nat.mul_le_mul_right _ hqLe
    dsimp [low, mid, high] at hlowLe hmidLe hhighLe ⊢
    norm_num [UInt256.size, Nat.pow_add] at hlowLe hmidLe hhighLe ⊢
    omega
  rw [Nat.mod_eq_of_lt hlt]

theorem flipperStorageLocStore_uint48_offset6 (evm : EVM.State) (slot val : UInt256)
    (hval : val.toNat < 2 ^ 48) :
    storageLocStore evm (uint48Loc slot ⟨6, by decide⟩ (by decide))
      (.int (Int.ofNat val.toNat)) =
      some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot
        (setUint48Offset6Word (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)
          val)) := by
  unfold storageLocStore storageLocWriteWord uint48Loc
  simp only [valueToWord, wordOfInt_ofNat_toNat, bind, Option.bind, pure]
  congr 2
  apply u256_inj
  show fromBytes'
      (List.take (6 : Fin 32).val _ ++ List.take (6 : Fin 33).val _
        ++ List.drop ((6 : Fin 32).val + (6 : Fin 33).val) _) =
      (setUint48Offset6Word (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)
        val).toNat
  rw [show (6 : Fin 32).val = 6 from rfl, show (6 : Fin 33).val = 6 from rfl]
  rw [fromBytes'_append, fromBytes'_append, fromBytes'_take_wordLE, fromBytes'_take_wordLE,
    fromBytes'_drop_wordLE]
  have hwordToNat :=
    setUint48Offset6Word_toNat
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot) val hval
  rw [hwordToNat]
  rw [show 256 ^ 6 = (2 : Nat) ^ 48 by norm_num [Nat.pow_add]]
  rw [Nat.mod_eq_of_lt hval]
  rw [List.length_append]
  rw [List.length_take, (EVM.Word.toBytesLEWithSizeProof
    (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).2]
  rw [List.length_take, (EVM.Word.toBytesLEWithSizeProof val).2]
  norm_num [Nat.pow_add]
  ring_nf

abbrev flipperUsr (I : ExecutionEnv) : AccountAddress :=
  AccountAddress.ofNat (calldataWord I.calldata 4).toNat

abbrev flipperUsrKey (I : ExecutionEnv) : UInt256 :=
  UInt256.land solcAddrMask (calldataWord I.calldata 4)

abbrev flipperUsrValue (I : ExecutionEnv) : Value :=
  .address (flipperUsr I)

abbrev flipperUsrStore (I : ExecutionEnv) : Store :=
  (∅ : Store).insert "usr" (flipperUsrValue I)

abbrev flipperUsrEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "wards", steps := [.mindex (.address (flipperUsr I))] }

abbrev flipperUsrSlotFor (I : ExecutionEnv) : UInt256 :=
  wardsSlot (.address (flipperUsr I))

theorem flipperUsrSlotFor_eq (I : ExecutionEnv) :
    flipperUsrSlotFor I = solcMappingSlot ⟨0⟩ (flipperUsrKey I) := by
  unfold flipperUsrSlotFor flipperUsr flipperUsrKey wardsSlot mapSlot solcMappingSlot
  rw [keyValueToWord_address_ofNat_mask]

abbrev flipperCallerWardsSlot (I : ExecutionEnv) : UInt256 :=
  solcMappingSlot ⟨0⟩ (solcSourceWord I)

abbrev flipperCallerWardsEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "wards", steps := [.mindex (.address I.source)] }

theorem flipperCallerWardsEvaledRef_ok {cA gh bl σ σ₀ A I} {g : Sat256} {locals : Store}
    (_hbase : locals.get? "wards" = none) :
    evalStorageRef config { contract := contract, locals := locals }
      (initState cA gh bl σ σ₀ g A I) (wardsRef sender) =
        .ok (flipperCallerWardsEvaledRef I) := by
  simp [flipperCallerWardsEvaledRef, wardsRef, sender, evalStorageRef, evalStorageRefSteps,
    evalStorageRefStep, evalExpr?, envValue, valueToKey?, EvalResult.ofOption,
    EvalResult.bind, pure, bind, initState]

theorem flipperAuthGuardEval_true {cA gh bl σ σ₀ A I} {g : Sat256} {locals : Store}
    (hbase : locals.get? "wards" = none)
    (hauth : flipperSlotWord (flipperCallerWardsSlot I) σ I = ⟨1⟩) :
    evalExpr? config { contract := contract, locals := locals }
      (initState cA gh bl σ σ₀ g A I)
      (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) = .ok (.bool true) := by
  have her := flipperCallerWardsEvaledRef_ok (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) (locals := locals) hbase
  have hload :
      Solm.EVM.storageLoad (initState cA gh bl σ σ₀ g A I) I.codeOwner
        (flipperCallerWardsSlot I) = ⟨1⟩ := by
    simpa [flipperSlotWord] using hauth
  rw [evalExpr?]
  simp only [EvalResult.bind, bind]
  rw [evalExpr_storage_scalar
    (t := .int uint256Int) (loc := wordLoc (flipperCallerWardsSlot I))
    (hbase := by simpa [wardsRef] using hbase)
    (her := her)
    (hty := by simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, uint256St])
    (hloc := by
      funext evm
      simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw,
        flipperCallerWardsEvaledRef, flipperCallerWardsSlot, wardsSlot, mapSlot,
        solcMappingSlot, keyValueToWord_address, solcSourceWord])]
  rw [flipperStorageLocLoad_uint256]
  simp only [initState] at hload ⊢
  rw [hload]
  simp [evalExpr?, evalBinaryOp?]
  all_goals native_decide

theorem flipperAuthGuardEval_false {cA gh bl σ σ₀ A I} {g : Sat256} {locals : Store}
    (hbase : locals.get? "wards" = none)
    (hauth : flipperSlotWord (flipperCallerWardsSlot I) σ I ≠ ⟨1⟩) :
    evalExpr? config { contract := contract, locals := locals }
      (initState cA gh bl σ σ₀ g A I)
      (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) = .ok (.bool false) := by
  have her := flipperCallerWardsEvaledRef_ok (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) (locals := locals) hbase
  let w := Solm.EVM.storageLoad (initState cA gh bl σ σ₀ g A I) I.codeOwner
    (flipperCallerWardsSlot I)
  have hload : w ≠ ⟨1⟩ := by
    intro hw
    exact hauth (by simpa [w, flipperSlotWord] using hw)
  rw [evalExpr?]
  simp only [EvalResult.bind, bind]
  rw [evalExpr_storage_scalar
    (t := .int uint256Int) (loc := wordLoc (flipperCallerWardsSlot I))
    (hbase := by simpa [wardsRef] using hbase)
    (her := her)
    (hty := by simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, uint256St])
    (hloc := by
      funext evm
      simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw,
        flipperCallerWardsEvaledRef, flipperCallerWardsSlot, wardsSlot, mapSlot,
        solcMappingSlot, keyValueToWord_address, solcSourceWord])]
  rw [flipperStorageLocLoad_uint256]
  simp only [initState] at hload ⊢
  simp [evalExpr?, evalBinaryOp?]
  · intro hnat
    apply hload
    apply u256_inj
    simpa using hnat
  all_goals native_decide

theorem flipperAddressGetterBodyReturns (evm : EVM.State) (locals : Store)
    {ref : StorageRef} {er : EvaledStorageRef} {slot : UInt256}
    (h : evm.executionEnv.weiValue = ⟨0⟩)
    (hbase : locals.get? ref.base = none)
    (her : evalStorageRef config { contract := contract, locals := locals } evm ref = .ok er)
    (hty : storageTypeAt? contract.storage er = some (.elem .address))
    (hloc : config.storage.layout er = fun _ => some (addrLoc slot)) :
    ExecTransitionBody config contract evm locals (nonpayable ++ [ .return [(.storage ref)] ])
      (.returned { contract := contract, locals := locals } evm
        (some [(.address (AccountAddress.ofNat
          (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)
            solcAddrMask).toNat))])) := by
  simpa [nonpayable] using
    nonpayableReturnExprBodyReturns (cfg := config) (contract := contract) h (by
      rw [evalExpr_storage_scalar (hbase := hbase) (her := her) (hty := hty) (hloc := hloc)]
      exact congrArg EvalResult.ok (flipperStorageLocLoad_address_offset0 evm slot))

theorem flipperUint256GetterBodyReturns (evm : EVM.State) (locals : Store)
    {ref : StorageRef} {er : EvaledStorageRef} {slot : UInt256}
    (h : evm.executionEnv.weiValue = ⟨0⟩)
    (hbase : locals.get? ref.base = none)
    (her : evalStorageRef config { contract := contract, locals := locals } evm ref = .ok er)
    (hty : storageTypeAt? contract.storage er = some (.elem (.int uint256Int)))
    (hloc : config.storage.layout er = fun _ => some (wordLoc slot)) :
    ExecTransitionBody config contract evm locals (nonpayable ++ [ .return [(.storage ref)] ])
      (.returned { contract := contract, locals := locals } evm
        (some [(.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot).toNat))])) := by
  simpa [nonpayable] using
    nonpayableReturnExprBodyReturns (cfg := config) (contract := contract) h (by
      rw [evalExpr_storage_scalar (hbase := hbase) (her := her) (hty := hty) (hloc := hloc)]
      exact congrArg EvalResult.ok (flipperStorageLocLoad_uint256 evm slot))

theorem flipperBytes32GetterBodyReturns (evm : EVM.State) (locals : Store)
    {ref : StorageRef} {er : EvaledStorageRef} {slot : UInt256}
    (h : evm.executionEnv.weiValue = ⟨0⟩)
    (hbase : locals.get? ref.base = none)
    (her : evalStorageRef config { contract := contract, locals := locals } evm ref = .ok er)
    (hty : storageTypeAt? contract.storage er = some (.elem (.bytes bytes32Width)))
    (hloc : config.storage.layout er = fun _ => some (bytes32Loc slot)) :
    ExecTransitionBody config contract evm locals (nonpayable ++ [ .return [(.storage ref)] ])
      (.returned { contract := contract, locals := locals } evm
        (some [(.fixedBytes bytes32Width
          (EVM.Word.toBytesBE (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)))])) := by
  simpa [nonpayable] using
    nonpayableReturnExprBodyReturns (cfg := config) (contract := contract) h (by
      rw [evalExpr_storage_scalar (hbase := hbase) (her := her) (hty := hty) (hloc := hloc)]
      exact congrArg EvalResult.ok (flipperStorageLocLoad_bytes32 evm slot))

theorem flipperUint48Offset0GetterBodyReturns (evm : EVM.State) (locals : Store)
    {ref : StorageRef} {er : EvaledStorageRef} {slot : UInt256}
    (h : evm.executionEnv.weiValue = ⟨0⟩)
    (hbase : locals.get? ref.base = none)
    (her : evalStorageRef config { contract := contract, locals := locals } evm ref = .ok er)
    (hty : storageTypeAt? contract.storage er = some (.elem (.int uint48Int)))
    (hloc : config.storage.layout er =
      fun _ => some (uint48Loc slot ⟨0, by decide⟩ (by decide))) :
    ExecTransitionBody config contract evm locals (nonpayable ++ [ .return [(.storage ref)] ])
      (.returned { contract := contract, locals := locals } evm
        (some [(.int (Int.ofNat
          (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)
            uint48Mask).toNat))])) := by
  simpa [nonpayable] using
    nonpayableReturnExprBodyReturns (cfg := config) (contract := contract) h (by
      rw [evalExpr_storage_scalar (hbase := hbase) (her := her) (hty := hty) (hloc := hloc)]
      exact congrArg EvalResult.ok (flipperStorageLocLoad_uint48_offset0 evm slot))

theorem flipperUint48Offset6GetterBodyReturns (evm : EVM.State) (locals : Store)
    {ref : StorageRef} {er : EvaledStorageRef} {slot : UInt256}
    (h : evm.executionEnv.weiValue = ⟨0⟩)
    (hbase : locals.get? ref.base = none)
    (her : evalStorageRef config { contract := contract, locals := locals } evm ref = .ok er)
    (hty : storageTypeAt? contract.storage er = some (.elem (.int uint48Int)))
    (hloc : config.storage.layout er =
      fun _ => some (uint48Loc slot ⟨6, by decide⟩ (by decide))) :
    ExecTransitionBody config contract evm locals (nonpayable ++ [ .return [(.storage ref)] ])
      (.returned { contract := contract, locals := locals } evm
        (some [(.int (Int.ofNat
          (UInt256.land (UInt256.div
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot) uint48Divisor)
            uint48Mask).toNat))])) := by
  simpa [nonpayable] using
    nonpayableReturnExprBodyReturns (cfg := config) (contract := contract) h (by
      rw [evalExpr_storage_scalar (hbase := hbase) (her := her) (hty := hty) (hloc := hloc)]
      exact congrArg EvalResult.ok (flipperStorageLocLoad_uint48_offset6 evm slot))

theorem flipperAddressGetterBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    {transition : TransitionDecl} {entry returnPc routine slot : UInt256}
    (hcode : I.code = flipperBytecode)
    (hdispatch : dispatchMsg contract I.calldata = some transition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (transition.params.map Param.name)
        (transitionSignature transition).paramTypes I.calldata = some ∅)
    (hreach : ∃ k C, RD flipperBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) entry [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hentry : solcGetterEntryWf flipperBytecode entry returnPc routine)
    (hgetter : solcAddressSlotGetterWf flipperBytecode routine slot)
    (hroutine : (D_J flipperBytecode 0).contains routine = true)
    (hreturnJd : (D_J flipperBytecode 0).contains returnPc = true)
    (hretmem : solcReturnAddressFromMemWf flipperBytecode returnPc)
    (hreturn : transition.returnType = [addr])
    (hbody :
      ExecTransitionBody config contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅ transition.body
        (.returned { contract := contract, locals := ∅ }
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (some [(.address (AccountAddress.ofNat
            (flipperAddressReturnWord slot σ_solm I).toNat))]))) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hword : flipperSlotWord slot σ_evm I = flipperSlotWord slot σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner slot ⟨0⟩
  have hval :
      some [Value.address (AccountAddress.ofNat (flipperAddressReturnWord slot σ_solm I).toNat)] =
        some [Value.address (AccountAddress.ofNat (flipperAddressReturnWord slot σ_evm I).toNat)] := by
    have hslot : flipperSlotWord slot σ_solm I = flipperSlotWord slot σ_evm I := hword.symm
    simp [flipperAddressReturnWord, hslot]
  have henc :
      returnEquiv (UInt256.toByteArray (flipperAddressReturnWord slot σ_evm I))
        (some [(.address (AccountAddress.ofNat (flipperAddressReturnWord slot σ_evm I).toNat))])
        transition.returnType := by
    rw [hreturn]
    simpa [flipperAddressReturnWord] using
      (returnEquiv_of_encode
        (solcAddressReturnEncoding (addrTy := addr) rfl (flipperSlotWord slot σ_evm I)))
  have hret := RD.solcAddressGetterExternal (code := flipperBytecode) (g := Sat256.ofUInt256 g)
    (returnPc := returnPc) (entry := entry) (routine := routine) (slot := slot)
    hreach hentry hgetter hroutine hreturnJd hretmem
  have hret' :
      RDret flipperBytecode (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) (cA, σ_evm)
        (UInt256.toByteArray (flipperAddressReturnWord slot σ_evm I)) := by
    simpa [flipperAddressReturnWord, flipperSlotWord] using hret
  exact hret'.reEquivExecutionTransport hcode hdispatch hdecode hbody hval hAccounts henc

theorem flipperBytes32GetterBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    {transition : TransitionDecl} {entry returnPc routine slot : UInt256}
    (hcode : I.code = flipperBytecode)
    (hdispatch : dispatchMsg contract I.calldata = some transition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (transition.params.map Param.name)
        (transitionSignature transition).paramTypes I.calldata = some ∅)
    (hreach : ∃ k C, RD flipperBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) entry [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hentry : solcGetterEntryWf flipperBytecode entry returnPc routine)
    (hgetter : solcWordSlotGetterWf flipperBytecode routine slot)
    (hroutine : (D_J flipperBytecode 0).contains routine = true)
    (hreturnJd : (D_J flipperBytecode 0).contains returnPc = true)
    (hretmem : solcReturnWordFromMemWf flipperBytecode returnPc)
    (hreturn : transition.returnType = [bytes32])
    (hbody :
      ExecTransitionBody config contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅ transition.body
        (.returned { contract := contract, locals := ∅ }
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (some [(.fixedBytes bytes32Width
            (EVM.Word.toBytesBE (flipperSlotWord slot σ_solm I)))]))) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hword : flipperSlotWord slot σ_evm I = flipperSlotWord slot σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner slot ⟨0⟩
  have hval :
      some [Value.fixedBytes bytes32Width (EVM.Word.toBytesBE (flipperSlotWord slot σ_solm I))] =
        some [Value.fixedBytes bytes32Width (EVM.Word.toBytesBE (flipperSlotWord slot σ_evm I))] := by
    rw [hword]
  have henc :
      returnEquiv (UInt256.toByteArray (flipperSlotWord slot σ_evm I))
        (some [(.fixedBytes bytes32Width (EVM.Word.toBytesBE (flipperSlotWord slot σ_evm I)))])
        transition.returnType := by
    rw [hreturn]
    exact returnEquiv_of_encode
      (by simpa [bytes32, bytes32Width] using bytes32ReturnEncoding (flipperSlotWord slot σ_evm I))
  have hret := RD.solcWordGetterExternal (code := flipperBytecode) (g := Sat256.ofUInt256 g)
    (returnPc := returnPc) (entry := entry) (routine := routine) (slot := slot)
    hreach hentry hgetter hroutine hreturnJd hretmem
  have hret' :
      RDret flipperBytecode (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) (cA, σ_evm)
        (UInt256.toByteArray (flipperSlotWord slot σ_evm I)) := by
    simpa [flipperSlotWord] using hret
  exact hret'.reEquivExecutionTransport hcode hdispatch hdecode hbody hval hAccounts henc

theorem flipperUint256GetterBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    {transition : TransitionDecl} {entry returnPc routine slot : UInt256}
    (hcode : I.code = flipperBytecode)
    (hdispatch : dispatchMsg contract I.calldata = some transition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (transition.params.map Param.name)
        (transitionSignature transition).paramTypes I.calldata = some ∅)
    (hreach : ∃ k C, RD flipperBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) entry [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hentry : solcGetterEntryWf flipperBytecode entry returnPc routine)
    (hgetter : solcWordSlotGetterWf flipperBytecode routine slot)
    (hroutine : (D_J flipperBytecode 0).contains routine = true)
    (hreturnJd : (D_J flipperBytecode 0).contains returnPc = true)
    (hretmem : solcReturnWordFromMemWf flipperBytecode returnPc)
    (hreturn : transition.returnType = [uint256])
    (hbody :
      ExecTransitionBody config contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅ transition.body
        (.returned { contract := contract, locals := ∅ }
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (some [(.int (Int.ofNat (flipperSlotWord slot σ_solm I).toNat))]))) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hword : flipperSlotWord slot σ_evm I = flipperSlotWord slot σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner slot ⟨0⟩
  have hval :
      some [Value.int (Int.ofNat (flipperSlotWord slot σ_solm I).toNat)] =
        some [Value.int (Int.ofNat (flipperSlotWord slot σ_evm I).toNat)] := by
    rw [hword]
  have henc :
      returnEquiv (UInt256.toByteArray (flipperSlotWord slot σ_evm I))
        (some [(.int (Int.ofNat (flipperSlotWord slot σ_evm I).toNat))])
        transition.returnType := by
    rw [hreturn]
    exact returnEquiv_of_encode
      (by simpa [uint256] using uint256ReturnEncoding (flipperSlotWord slot σ_evm I))
  have hret := RD.solcWordGetterExternal (code := flipperBytecode) (g := Sat256.ofUInt256 g)
    (returnPc := returnPc) (entry := entry) (routine := routine) (slot := slot)
    hreach hentry hgetter hroutine hreturnJd hretmem
  have hret' :
      RDret flipperBytecode (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) (cA, σ_evm)
        (UInt256.toByteArray (flipperSlotWord slot σ_evm I)) := by
    simpa [flipperSlotWord] using hret
  exact hret'.reEquivExecutionTransport hcode hdispatch hdecode hbody hval hAccounts henc

@[reducible] def solcUint48Offset0SlotGetterWf
    (code : ByteArray) (pc slot : UInt256) : Prop :=
  let p1 := pc + ⟨1⟩
  let p3 := p1 + UInt256.ofNat 2
  let p4 := p3 + ⟨1⟩
  let p11 := p4 + UInt256.ofNat 7
  let p12 := p11 + ⟨1⟩
  let p13 := p12 + ⟨1⟩
  decode code pc = some (.JUMPDEST, .none)
  ∧ decode code p1 = some (.Push .PUSH1, some (slot, 1))
  ∧ decode code p3 = some (.SLOAD, .none)
  ∧ decode code p4 = some (.Push .PUSH6, some (uint48Mask, 6))
  ∧ decode code p11 = some (.AND, .none)
  ∧ decode code p12 = some (.DUP2, .none)
  ∧ decode code p13 = some (.JUMP, .none)

@[reducible] def solcUint48Offset6SlotGetterWf
    (code : ByteArray) (pc slot : UInt256) : Prop :=
  let p1 := pc + ⟨1⟩
  let p3 := p1 + UInt256.ofNat 2
  let p4 := p3 + ⟨1⟩
  let p6 := p4 + UInt256.ofNat 2
  let p8 := p6 + UInt256.ofNat 2
  let p9 := p8 + ⟨1⟩
  let p10 := p9 + ⟨1⟩
  let p11 := p10 + ⟨1⟩
  let p18 := p11 + UInt256.ofNat 7
  let p19 := p18 + ⟨1⟩
  let p20 := p19 + ⟨1⟩
  decode code pc = some (.JUMPDEST, .none)
  ∧ decode code p1 = some (.Push .PUSH1, some (slot, 1))
  ∧ decode code p3 = some (.SLOAD, .none)
  ∧ decode code p4 = some (.Push .PUSH1, some (⟨1⟩, 1))
  ∧ decode code p6 = some (.Push .PUSH1, some (⟨48⟩, 1))
  ∧ decode code p8 = some (.SHL, .none)
  ∧ decode code p9 = some (.SWAP1, .none)
  ∧ decode code p10 = some (.DIV, .none)
  ∧ decode code p11 = some (.Push .PUSH6, some (uint48Mask, 6))
  ∧ decode code p18 = some (.AND, .none)
  ∧ decode code p19 = some (.DUP2, .none)
  ∧ decode code p20 = some (.JUMP, .none)

@[reducible] def solcReturnUint48FromMemWf (code : ByteArray) (pc : UInt256) : Prop :=
  let p1 := pc + ⟨1⟩
  let p3 := p1 + UInt256.ofNat 2
  let p4 := p3 + ⟨1⟩
  let p5 := p4 + ⟨1⟩
  let p12 := p5 + UInt256.ofNat 7
  let p13 := p12 + ⟨1⟩
  let p14 := p13 + ⟨1⟩
  let p15 := p14 + ⟨1⟩
  let p16 := p15 + ⟨1⟩
  let p17 := p16 + ⟨1⟩
  let p18 := p17 + ⟨1⟩
  let p19 := p18 + ⟨1⟩
  let p20 := p19 + ⟨1⟩
  let p21 := p20 + ⟨1⟩
  let p23 := p21 + UInt256.ofNat 2
  let p24 := p23 + ⟨1⟩
  let p25 := p24 + ⟨1⟩
  decode code pc = some (.JUMPDEST, .none)
  ∧ decode code p1 = some (.Push .PUSH1, some (⟨64⟩, 1))
  ∧ decode code p3 = some (.DUP1, .none)
  ∧ decode code p4 = some (.MLOAD, .none)
  ∧ decode code p5 = some (.Push .PUSH6, some (uint48Mask, 6))
  ∧ decode code p12 = some (.SWAP1, .none)
  ∧ decode code p13 = some (.SWAP3, .none)
  ∧ decode code p14 = some (.AND, .none)
  ∧ decode code p15 = some (.DUP3, .none)
  ∧ decode code p16 = some (.MSTORE, .none)
  ∧ decode code p17 = some (.MLOAD, .none)
  ∧ decode code p18 = some (.SWAP1, .none)
  ∧ decode code p19 = some (.DUP2, .none)
  ∧ decode code p20 = some (.SWAP1, .none)
  ∧ decode code p21 = some (.SUB, .none)
  ∧ decode code p23 = some (.Push .PUSH1, some (⟨32⟩, 1))
  ∧ decode code p24 = some (.ADD, .none)
  ∧ decode code p25 = some (.SWAP1, .none)
  ∧ decode code (p25 + ⟨1⟩) = some (.RETURN, .none)

theorem RD.solcUint48Offset0SlotGetter {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {pc slot ret : UInt256} {R : List UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD code ee g s0 pc (ret :: R) mem aw rdata (cA, σ) k C)
    (hwf : solcUint48Offset0SlotGetterWf code pc slot)
    (hret : (D_J code 0).contains ret = true)
    (hov : R.length + 4 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ret
      (UInt256.land (solcSlotWord σ ee slot) uint48Mask :: ret :: R)
      mem aw rdata (cA, σ) k' C' := by
  rcases hwf with ⟨hd0, hd1, hd3, hd4, hd11, hd12, hd13⟩
  have rd1 := h.jumpdest hd0 (by simp only [List.length_cons]; omega)
  have rd3 := rd1.push1 slot hd1 (by simp only [List.length_cons]; omega)
  obtain ⟨_, _, rd4⟩ := rd3.sload hd3 (by simp only [List.length_cons]; omega)
  have rd11 := rd4.pushConst uint48Mask (width := 6) (op := .PUSH6)
    (by decide) hd4 (by simp only [List.length_cons]; omega)
  have rd12 := rd11.and hd11 (by simp only [List.length_cons]; omega)
  have rd13 := rd12.dup2 hd12 (by omega)
  have rdRet := rd13.jump hd13 hret (by simp only [List.length_cons]; omega)
  have hcomm :
      UInt256.land uint48Mask (solcSlotWord σ ee slot) =
        UInt256.land (solcSlotWord σ ee slot) uint48Mask :=
    u256_land_comm _ _
  exact ⟨_, _, by simpa [hcomm] using rdRet⟩

theorem RD.solcUint48Offset6SlotGetter {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {pc slot ret : UInt256} {R : List UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD code ee g s0 pc (ret :: R) mem aw rdata (cA, σ) k C)
    (hwf : solcUint48Offset6SlotGetterWf code pc slot)
    (hret : (D_J code 0).contains ret = true)
    (hov : R.length + 4 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ret
      (UInt256.land (UInt256.div (solcSlotWord σ ee slot) uint48Divisor) uint48Mask ::
        ret :: R) mem aw rdata (cA, σ) k' C' := by
  rcases hwf with ⟨hd0, hd1, hd3, hd4, hd6, hd8, hd9, hd10, hd11, hd18, hd19, hd20⟩
  have rd1 := h.jumpdest hd0 (by simp only [List.length_cons]; omega)
  have rd3 := rd1.push1 slot hd1 (by simp only [List.length_cons]; omega)
  obtain ⟨_, _, rd4⟩ := rd3.sload hd3 (by simp only [List.length_cons]; omega)
  have rd6 := rd4.push1 ⟨1⟩ hd4 (by simp only [List.length_cons]; omega)
  have rd8 := rd6.push1 ⟨48⟩ hd6 (by simp only [List.length_cons]; omega)
  have rd9 := rd8.shl hd8 (by simp only [List.length_cons]; omega)
  have rd10 := rd9.swap1 hd9 (by simp only [List.length_cons]; omega)
  have rd11 := rd10.div hd10 (by simp only [List.length_cons]; omega)
  have rd18 := rd11.pushConst uint48Mask (width := 6) (op := .PUSH6)
    (by decide) hd11 (by simp only [List.length_cons]; omega)
  have rd19 := rd18.and hd18 (by simp only [List.length_cons]; omega)
  have rd20 := rd19.dup2 hd19 (by omega)
  have rdRet := rd20.jump hd20 hret (by simp only [List.length_cons]; omega)
  have hdiv :
      UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨48⟩ = uint48Divisor := by
    native_decide
  have hcomm :
      UInt256.land uint48Mask
          (UInt256.div (solcSlotWord σ ee slot)
            (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨48⟩)) =
        UInt256.land (UInt256.div (solcSlotWord σ ee slot) uint48Divisor) uint48Mask := by
    rw [hdiv]
    exact u256_land_comm _ _
  exact ⟨_, _, by simpa [hcomm] using rdRet⟩

theorem RD.flipperReturnUint48FromMem {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {val ret : UInt256} {R : List UInt256}
    {mem memout rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD flipperBytecode ee g s0 ⟨643⟩ (val :: ret :: R) mem (UInt256.ofNat 3)
        rdata acc k C)
    (hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 3 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32)))
        = ⟨128⟩)
    (hmemout :
      (UInt256.toByteArray (UInt256.land val uint48Mask)).write 0 mem 128 32 = memout)
    (hmemoutLoad64 :
      (if (⟨64⟩ : UInt256).toNat ≥ memout.size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 5 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (memout.readWithPadding (⟨64⟩ : UInt256).toNat 32)))
        = ⟨128⟩)
    (hread128 :
      memout.readWithPadding 128 32 = UInt256.toByteArray (UInt256.land val uint48Mask))
    (hov : R.length + 9 ≤ 1024) :
    RDret flipperBytecode g s0 acc (UInt256.toByteArray (UInt256.land val uint48Mask)) := by
  have rd1 := h.jumpdest (by native_decide) (by simp only [List.length_cons]; omega)
  have rd3 := rd1.push1 ⟨64⟩ (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rd4 := rd3.dup1 (by native_decide) (by simp only [List.length_cons]; omega)
  have rd5 := rd4.mload 0 ⟨128⟩ (UInt256.ofNat 3) (by native_decide) mem_cost hmload64
    (by decide) (by simp only [List.length_cons]; omega)
  have rd12 := rd5.pushConst uint48Mask (width := 6) (op := .PUSH6)
    (by decide) (by native_decide) (by simp only [List.length_cons]; omega)
  have rd13 := rd12.swap1 (by native_decide) (by simp only [List.length_cons]; omega)
  have rd14 := rd13.swap3 (by native_decide) (by simp only [List.length_cons]; omega)
  have rd15 := rd14.and (by native_decide) (by simp only [List.length_cons]; omega)
  have rd16 := rd15.dup3 (by native_decide) (by simp only [List.length_cons]; omega)
  have rd17 := rd16.mstore 6 memout (UInt256.ofNat 5) (by native_decide) mem_cost
    (by
      rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide]
      exact hmemout)
    (by decide) (by simp only [List.length_cons]; omega)
  have rd18 := rd17.mload 0 ⟨128⟩ (UInt256.ofNat 5) (by native_decide) mem_cost
    hmemoutLoad64
    (by decide) (by simp only [List.length_cons]; omega)
  have rd19 := rd18.swap1 (by native_decide) (by simp only [List.length_cons]; omega)
  have rd20 := rd19.dup2 (by native_decide) (by simp only [List.length_cons]; omega)
  have rd21 := rd20.swap1 (by native_decide) (by simp only [List.length_cons]; omega)
  have rd23 := rd21.sub (by native_decide) (by simp only [List.length_cons]; omega)
  have rd24 := rd23.push1 ⟨32⟩ (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rd25 := rd24.add (by native_decide) (by simp only [List.length_cons]; omega)
  have rd26 := rd25.swap1 (by native_decide) (by simp only [List.length_cons]; omega)
  exact rd26.ret 0 (UInt256.toByteArray (UInt256.land val uint48Mask)) (by native_decide)
    mem_cost
    (by
      rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide,
        show ((⟨32⟩ : UInt256) + UInt256.sub (⟨128⟩ : UInt256) ⟨128⟩).toNat = 32
          from by decide]
      exact hread128)
    (by evm_ov)

theorem RD.flipperUint48Offset0GetterExternal {cA gh bl σ σ₀ A I}
    {g : Sat256} {sel entry routine slot : UInt256}
    (hreach : ∃ k C, RD flipperBytecode I g
      (Reasoning.Theory.initState cA gh bl σ σ₀ g A I)
      entry [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hentry : solcGetterEntryWf flipperBytecode entry ⟨643⟩ routine)
    (hgetter : solcUint48Offset0SlotGetterWf flipperBytecode routine slot)
    (hroutine : (D_J flipperBytecode 0).contains routine = true)
    (hret : (D_J flipperBytecode 0).contains (⟨643⟩ : UInt256) = true) :
    RDret flipperBytecode g (Reasoning.Theory.initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray (UInt256.land (solcSlotWord σ I slot) uint48Mask)) := by
  obtain ⟨_, _, rdRoutine⟩ := RD.solcGetterThunk hreach hentry hroutine
  obtain ⟨_, _, rdReturn⟩ := RD.solcUint48Offset0SlotGetter (slot := slot) (R := [sel])
    rdRoutine hgetter hret (by simp only [List.length_singleton]; omega)
  have hrd := RD.flipperReturnUint48FromMem rdReturn
    solcFreePtrMem_mload64
    (by rfl)
    (solcReturnMem_mload64
      (UInt256.land (UInt256.land (solcSlotWord σ I slot) uint48Mask) uint48Mask))
    (solcReturnMem_read128
      (UInt256.land (UInt256.land (solcSlotWord σ I slot) uint48Mask) uint48Mask))
    (by simp only [List.length_singleton]; omega)
  have hclean :
      UInt256.land (UInt256.land (solcSlotWord σ I slot) uint48Mask) uint48Mask =
        UInt256.land (solcSlotWord σ I slot) uint48Mask := by
    exact uint48Mask_clean (uint48Mask_bound _)
  simpa [hclean] using hrd

theorem RD.flipperUint48Offset6GetterExternal {cA gh bl σ σ₀ A I}
    {g : Sat256} {sel entry routine slot : UInt256}
    (hreach : ∃ k C, RD flipperBytecode I g
      (Reasoning.Theory.initState cA gh bl σ σ₀ g A I)
      entry [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hentry : solcGetterEntryWf flipperBytecode entry ⟨643⟩ routine)
    (hgetter : solcUint48Offset6SlotGetterWf flipperBytecode routine slot)
    (hroutine : (D_J flipperBytecode 0).contains routine = true)
    (hret : (D_J flipperBytecode 0).contains (⟨643⟩ : UInt256) = true) :
    RDret flipperBytecode g (Reasoning.Theory.initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray
        (UInt256.land (UInt256.div (solcSlotWord σ I slot) uint48Divisor) uint48Mask)) := by
  obtain ⟨_, _, rdRoutine⟩ := RD.solcGetterThunk hreach hentry hroutine
  obtain ⟨_, _, rdReturn⟩ := RD.solcUint48Offset6SlotGetter (slot := slot) (R := [sel])
    rdRoutine hgetter hret (by simp only [List.length_singleton]; omega)
  have hrd := RD.flipperReturnUint48FromMem rdReturn
    solcFreePtrMem_mload64
    (by rfl)
    (solcReturnMem_mload64
      (UInt256.land
        (UInt256.land (UInt256.div (solcSlotWord σ I slot) uint48Divisor) uint48Mask)
        uint48Mask))
    (solcReturnMem_read128
      (UInt256.land
        (UInt256.land (UInt256.div (solcSlotWord σ I slot) uint48Divisor) uint48Mask)
        uint48Mask))
    (by simp only [List.length_singleton]; omega)
  have hclean :
      UInt256.land
          (UInt256.land (UInt256.div (solcSlotWord σ I slot) uint48Divisor) uint48Mask)
          uint48Mask =
        UInt256.land (UInt256.div (solcSlotWord σ I slot) uint48Divisor) uint48Mask := by
    exact uint48Mask_clean (uint48Mask_bound _)
  simpa [hclean] using hrd

theorem flipperUint48Offset0GetterBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    {transition : TransitionDecl} {entry routine slot : UInt256}
    (hcode : I.code = flipperBytecode)
    (hdispatch : dispatchMsg contract I.calldata = some transition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (transition.params.map Param.name)
        (transitionSignature transition).paramTypes I.calldata = some ∅)
    (hreach : ∃ k C, RD flipperBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) entry [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hentry : solcGetterEntryWf flipperBytecode entry ⟨643⟩ routine)
    (hgetter : solcUint48Offset0SlotGetterWf flipperBytecode routine slot)
    (hroutine : (D_J flipperBytecode 0).contains routine = true)
    (hreturnJd : (D_J flipperBytecode 0).contains (⟨643⟩ : UInt256) = true)
    (hreturn : transition.returnType = [uint48])
    (hbody :
      ExecTransitionBody config contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅ transition.body
        (.returned { contract := contract, locals := ∅ }
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (some [(.int (Int.ofNat (flipperUint48Offset0Word slot σ_solm I).toNat))]))) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hword : flipperSlotWord slot σ_evm I = flipperSlotWord slot σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner slot ⟨0⟩
  have hval :
      some [Value.int (Int.ofNat (flipperUint48Offset0Word slot σ_solm I).toNat)] =
        some [Value.int (Int.ofNat (flipperUint48Offset0Word slot σ_evm I).toNat)] := by
    simp [flipperUint48Offset0Word, hword]
  have henc :
      returnEquiv (UInt256.toByteArray (flipperUint48Offset0Word slot σ_evm I))
        (some [(.int (Int.ofNat (flipperUint48Offset0Word slot σ_evm I).toNat))])
        transition.returnType := by
    rw [hreturn]
    exact returnEquiv_of_encode
      (by simpa [flipperUint48Offset0Word] using
        uint48ReturnEncodingMasked (flipperSlotWord slot σ_evm I))
  have hret := RD.flipperUint48Offset0GetterExternal
    (g := Sat256.ofUInt256 g) (entry := entry) (routine := routine) (slot := slot)
    hreach hentry hgetter hroutine hreturnJd
  have hret' :
      RDret flipperBytecode (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) (cA, σ_evm)
        (UInt256.toByteArray (flipperUint48Offset0Word slot σ_evm I)) := by
    simpa [flipperUint48Offset0Word, flipperSlotWord] using hret
  exact hret'.reEquivExecutionTransport hcode hdispatch hdecode hbody hval hAccounts henc

theorem flipperUint48Offset6GetterBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    {transition : TransitionDecl} {entry routine slot : UInt256}
    (hcode : I.code = flipperBytecode)
    (hdispatch : dispatchMsg contract I.calldata = some transition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (transition.params.map Param.name)
        (transitionSignature transition).paramTypes I.calldata = some ∅)
    (hreach : ∃ k C, RD flipperBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) entry [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hentry : solcGetterEntryWf flipperBytecode entry ⟨643⟩ routine)
    (hgetter : solcUint48Offset6SlotGetterWf flipperBytecode routine slot)
    (hroutine : (D_J flipperBytecode 0).contains routine = true)
    (hreturnJd : (D_J flipperBytecode 0).contains (⟨643⟩ : UInt256) = true)
    (hreturn : transition.returnType = [uint48])
    (hbody :
      ExecTransitionBody config contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅ transition.body
        (.returned { contract := contract, locals := ∅ }
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (some [(.int (Int.ofNat (flipperUint48Offset6Word slot σ_solm I).toNat))]))) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hword : flipperSlotWord slot σ_evm I = flipperSlotWord slot σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner slot ⟨0⟩
  have hval :
      some [Value.int (Int.ofNat (flipperUint48Offset6Word slot σ_solm I).toNat)] =
        some [Value.int (Int.ofNat (flipperUint48Offset6Word slot σ_evm I).toNat)] := by
    simp [flipperUint48Offset6Word, hword]
  have henc :
      returnEquiv (UInt256.toByteArray (flipperUint48Offset6Word slot σ_evm I))
        (some [(.int (Int.ofNat (flipperUint48Offset6Word slot σ_evm I).toNat))])
        transition.returnType := by
    rw [hreturn]
    exact returnEquiv_of_encode
      (by simpa [flipperUint48Offset6Word] using
        uint48ReturnEncodingMasked (UInt256.div (flipperSlotWord slot σ_evm I) uint48Divisor))
  have hret := RD.flipperUint48Offset6GetterExternal
    (g := Sat256.ofUInt256 g) (entry := entry) (routine := routine) (slot := slot)
    hreach hentry hgetter hroutine hreturnJd
  have hret' :
      RDret flipperBytecode (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) (cA, σ_evm)
        (UInt256.toByteArray (flipperUint48Offset6Word slot σ_evm I)) := by
    simpa [flipperUint48Offset6Word, flipperSlotWord] using hret
  exact hret'.reEquivExecutionTransport hcode hdispatch hdecode hbody hval hAccounts henc

@[reducible] def flipperAuthTailPc (pc : UInt256) : UInt256 :=
  let p1 := pc + ⟨1⟩
  let p2 := p1 + ⟨1⟩
  let p4 := p2 + UInt256.ofNat 2
  let p5 := p4 + ⟨1⟩
  let p6 := p5 + ⟨1⟩
  let p7 := p6 + ⟨1⟩
  let p9 := p7 + UInt256.ofNat 2
  let p10 := p9 + ⟨1⟩
  let p11 := p10 + ⟨1⟩
  let p12 := p11 + ⟨1⟩
  let p14 := p12 + UInt256.ofNat 2
  let p15 := p14 + ⟨1⟩
  let p16 := p15 + ⟨1⟩
  let p17 := p16 + ⟨1⟩
  let p19 := p17 + UInt256.ofNat 2
  let p20 := p19 + ⟨1⟩
  let p23 := p20 + UInt256.ofNat 3
  p23 + ⟨1⟩

@[reducible] def flipperAuthCheckWf (code : ByteArray) (pc okPc : UInt256) : Prop :=
  let p1 := pc + ⟨1⟩
  let p2 := p1 + ⟨1⟩
  let p4 := p2 + UInt256.ofNat 2
  let p5 := p4 + ⟨1⟩
  let p6 := p5 + ⟨1⟩
  let p7 := p6 + ⟨1⟩
  let p9 := p7 + UInt256.ofNat 2
  let p10 := p9 + ⟨1⟩
  let p11 := p10 + ⟨1⟩
  let p12 := p11 + ⟨1⟩
  let p14 := p12 + UInt256.ofNat 2
  let p15 := p14 + ⟨1⟩
  let p16 := p15 + ⟨1⟩
  let p17 := p16 + ⟨1⟩
  let p19 := p17 + UInt256.ofNat 2
  let p20 := p19 + ⟨1⟩
  let p23 := p20 + UInt256.ofNat 3
  decode code pc = some (.JUMPDEST, .none)
  ∧ decode code p1 = some (.CALLER, .none)
  ∧ decode code p2 = some (.Push .PUSH1, some (⟨0⟩, 1))
  ∧ decode code p4 = some (.SWAP1, .none)
  ∧ decode code p5 = some (.DUP2, .none)
  ∧ decode code p6 = some (.MSTORE, .none)
  ∧ decode code p7 = some (.Push .PUSH1, some (⟨32⟩, 1))
  ∧ decode code p9 = some (.DUP2, .none)
  ∧ decode code p10 = some (.SWAP1, .none)
  ∧ decode code p11 = some (.MSTORE, .none)
  ∧ decode code p12 = some (.Push .PUSH1, some (⟨64⟩, 1))
  ∧ decode code p14 = some (.SWAP1, .none)
  ∧ decode code p15 = some (.KECCAK256, .none)
  ∧ decode code p16 = some (.SLOAD, .none)
  ∧ decode code p17 = some (.Push .PUSH1, some (⟨1⟩, 1))
  ∧ decode code p19 = some (.EQ, .none)
  ∧ decode code p20 = some (.Push .PUSH2, some (okPc, 2))
  ∧ decode code p23 = some (.JUMPI, .none)

abbrev flipperNotAuthorizedRawWord : UInt256 :=
  ⟨1882396589317237868685917121345356193241433⟩

abbrev flipperAuthErrorLen : UInt256 := ⟨22⟩

abbrev flipperAuthErrorOffset : UInt256 := ⟨6342⟩

theorem write32_read_above_from (src base : ByteArray) (srcAddr destAddr readAddr : ℕ)
    (hsrc : srcAddr + 32 ≤ src.size) (hinwrite : destAddr + 32 ≤ base.size)
    (habove : destAddr + 32 ≤ readAddr) (hin : readAddr + 32 ≤ base.size) :
    (src.write srcAddr base destAddr 32).readWithPadding readAddr 32 =
      base.readWithPadding readAddr 32 := by
  have hbsz : (base.extract 0 destAddr).size = destAddr := by
    rw [ByteArray.size_extract]
    omega
  have hsz32 : (src.extract srcAddr (srcAddr + 32)).size = 32 := by
    rw [ByteArray.size_extract]
    omega
  have hcsz : (base.extract (destAddr + 32) base.size).size =
      base.size - (destAddr + 32) := by
    rw [ByteArray.size_extract]
    omega
  have habsz :
      (base.extract 0 destAddr ++ src.extract srcAddr (srcAddr + 32)).size =
        destAddr + 32 := by
    rw [ByteArray.size_append, hbsz, hsz32]
  rw [write_eq_gen_from src base srcAddr destAddr 32 (by decide) hsrc hinwrite,
    readWithPadding_eq_extract _ readAddr
      (by rw [ByteArray.size_append, habsz, hcsz]; omega),
    readWithPadding_eq_extract _ readAddr (by omega),
    extract_append_right_window _ _ _ _ (by rw [habsz]; omega), habsz,
    extract_extract_BA,
    show destAddr + 32 + (readAddr - (destAddr + 32)) = readAddr from by omega,
    show min (destAddr + 32 + (readAddr + 32 - (destAddr + 32))) base.size =
      readAddr + 32 from by omega]

theorem flipperSolcErrorStringMem2_read64 (len : UInt256) {mem : ByteArray}
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (solcErrorStringMem2 len mem).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold solcErrorStringMem2
  rw [toByteArray_write_read_below_of_gap len _ 164 64
      (by rw [solcErrorStringMem1_size hmem]; omega) (by omega)
      (by rw [solcErrorStringMem1_size hmem]; exact lt_usize _ (by norm_num))]
  unfold solcErrorStringMem1
  rw [toByteArray_write_read_below_of_gap (⟨32⟩ : UInt256) _ 132 64
      (by rw [solcErrorStringMem0_size hmem]; omega) (by omega)
      (by rw [solcErrorStringMem0_size hmem]; exact lt_usize _ (by norm_num))]
  unfold solcErrorStringMem0
  rw [toByteArray_write_read_below_of_gap solcErrorStringSelector _ 128 64
      (by omega) (by omega) (by rw [hmem]; exact lt_usize _ (by norm_num))]
  exact hread64

noncomputable def flipperAuthScratchMem (mem : ByteArray) : ByteArray :=
  flipperBytecode.write flipperAuthErrorOffset.toNat
    (solcErrorStringMem2 flipperAuthErrorLen mem) 0 32

noncomputable def flipperAuthOriginalWord (mem : ByteArray) : UInt256 :=
  UInt256.ofNat
    (fromByteArrayBigEndian
      ((solcErrorStringMem2 flipperAuthErrorLen mem).readWithPadding 0 32))

noncomputable def flipperAuthScratchWord (mem : ByteArray) : UInt256 :=
  UInt256.ofNat
    (fromByteArrayBigEndian ((flipperAuthScratchMem mem).readWithPadding 0 32))

noncomputable def flipperAuthRestoredMem (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray (flipperAuthOriginalWord mem)).write 0
    (flipperAuthScratchMem mem) 0 32

noncomputable def flipperAuthCodecopyErrorMem (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray (flipperAuthScratchWord mem)).write 0
    (flipperAuthRestoredMem mem) 196 32

theorem flipperAuthScratchMem_size {mem : ByteArray} (hmem : mem.size = 96) :
    (flipperAuthScratchMem mem).size = 196 := by
  have hsrc : flipperAuthErrorOffset.toNat + 32 ≤ flipperBytecode.size := by
    native_decide
  unfold flipperAuthScratchMem
  rw [write_eq_gen_from flipperBytecode (solcErrorStringMem2 flipperAuthErrorLen mem)
    flipperAuthErrorOffset.toNat 0 32 (by decide) hsrc
    (by rw [solcErrorStringMem2_size flipperAuthErrorLen hmem]; omega)]
  rw [ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract,
    solcErrorStringMem2_size flipperAuthErrorLen hmem]
  omega

theorem flipperAuthScratchMem_read64 {mem : ByteArray}
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (flipperAuthScratchMem mem).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold flipperAuthScratchMem
  rw [write32_read_above_from flipperBytecode
    (solcErrorStringMem2 flipperAuthErrorLen mem) flipperAuthErrorOffset.toNat 0 64
    (by native_decide)
    (by rw [solcErrorStringMem2_size flipperAuthErrorLen hmem]; omega)
    (by omega)
    (by rw [solcErrorStringMem2_size flipperAuthErrorLen hmem]; omega)]
  exact flipperSolcErrorStringMem2_read64 flipperAuthErrorLen hmem hread64

theorem flipperAuthRestoredMem_size {mem : ByteArray} (hmem : mem.size = 96) :
    (flipperAuthRestoredMem mem).size = 196 := by
  unfold flipperAuthRestoredMem
  exact toByteArray_write32_size_of_le (flipperAuthScratchMem mem)
    (flipperAuthOriginalWord mem) 0 196 196 (flipperAuthScratchMem_size hmem)
    (by rw [flipperAuthScratchMem_size hmem]; omega) (by omega)

theorem flipperAuthRestoredMem_read64 {mem : ByteArray}
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (flipperAuthRestoredMem mem).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold flipperAuthRestoredMem
  rw [write32_read_above (UInt256.toByteArray (flipperAuthOriginalWord mem))
    (flipperAuthScratchMem mem) 0 64 (by rw [toByteArray_size])
    (by rw [flipperAuthScratchMem_size hmem]; omega) (by omega)
    (by rw [flipperAuthScratchMem_size hmem]; omega)]
  exact flipperAuthScratchMem_read64 hmem hread64

theorem flipperAuthCodecopyErrorMem_size {mem : ByteArray} (hmem : mem.size = 96) :
    (flipperAuthCodecopyErrorMem mem).size = 228 := by
  unfold flipperAuthCodecopyErrorMem
  exact toByteArray_write32_size_of_le (flipperAuthRestoredMem mem)
    (flipperAuthScratchWord mem) 196 196 228 (flipperAuthRestoredMem_size hmem)
    (by simp [flipperAuthRestoredMem_size hmem]) (by omega)

theorem flipperAuthCodecopyErrorMem_read64 {mem : ByteArray}
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (flipperAuthCodecopyErrorMem mem).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold flipperAuthCodecopyErrorMem
  rw [write32_read_below (UInt256.toByteArray (flipperAuthScratchWord mem))
    (flipperAuthRestoredMem mem) 196 64 (by rw [toByteArray_size])
    (by simp [flipperAuthRestoredMem_size hmem]) (by omega)]
  exact flipperAuthRestoredMem_read64 hmem hread64

theorem flipperAuthCodecopyErrorMem_mload64 {mem : ByteArray}
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (if (⟨64⟩ : UInt256).toNat ≥ (flipperAuthCodecopyErrorMem mem).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 8 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((flipperAuthCodecopyErrorMem mem).readWithPadding (⟨64⟩ : UInt256).toNat 32)))
      = ⟨128⟩ :=
  mloadFreePtrValue (by rw [flipperAuthCodecopyErrorMem_size hmem]; decide)
    (by decide) (flipperAuthCodecopyErrorMem_read64 hmem hread64)

@[reducible] def flipperAuthCodecopyRevertTailWf (pc : UInt256) : Prop :=
  let p2 := pc + UInt256.ofNat 2
  let p3 := p2 + ⟨1⟩
  let p4 := p3 + ⟨1⟩
  let p8 := p4 + UInt256.ofNat 4
  let p10 := p8 + UInt256.ofNat 2
  let p11 := p10 + ⟨1⟩
  let p12 := p11 + ⟨1⟩
  let p13 := p12 + ⟨1⟩
  let p15 := p13 + UInt256.ofNat 2
  let p17 := p15 + UInt256.ofNat 2
  let p18 := p17 + ⟨1⟩
  let p19 := p18 + ⟨1⟩
  let p20 := p19 + ⟨1⟩
  let p22 := p20 + UInt256.ofNat 2
  let p24 := p22 + UInt256.ofNat 2
  let p25 := p24 + ⟨1⟩
  let p26 := p25 + ⟨1⟩
  let p27 := p26 + ⟨1⟩
  let p29 := p27 + UInt256.ofNat 2
  let p30 := p29 + ⟨1⟩
  let p31 := p30 + ⟨1⟩
  let p33 := p31 + UInt256.ofNat 2
  let p36 := p33 + UInt256.ofNat 3
  let p37 := p36 + ⟨1⟩
  let p38 := p37 + ⟨1⟩
  let p39 := p38 + ⟨1⟩
  let p40 := p39 + ⟨1⟩
  let p41 := p40 + ⟨1⟩
  let p42 := p41 + ⟨1⟩
  let p44 := p42 + UInt256.ofNat 2
  let p45 := p44 + ⟨1⟩
  let p46 := p45 + ⟨1⟩
  let p47 := p46 + ⟨1⟩
  let p48 := p47 + ⟨1⟩
  let p49 := p48 + ⟨1⟩
  let p50 := p49 + ⟨1⟩
  let p51 := p50 + ⟨1⟩
  let p52 := p51 + ⟨1⟩
  let p54 := p52 + ⟨1⟩
  let p55 := p54 + UInt256.ofNat 2
  let p56 := p55 + ⟨1⟩
  let p57 := p56 + ⟨1⟩
  decode flipperBytecode pc = some (.Push .PUSH1, some (⟨64⟩, 1))
  ∧ decode flipperBytecode p2 = some (.DUP1, .none)
  ∧ decode flipperBytecode p3 = some (.MLOAD, .none)
  ∧ decode flipperBytecode p4 = some (.Push .PUSH3, some (⟨4594637⟩, 3))
  ∧ decode flipperBytecode p8 = some (.Push .PUSH1, some (⟨229⟩, 1))
  ∧ decode flipperBytecode p10 = some (.SHL, .none)
  ∧ decode flipperBytecode p11 = some (.DUP2, .none)
  ∧ decode flipperBytecode p12 = some (.MSTORE, .none)
  ∧ decode flipperBytecode p13 = some (.Push .PUSH1, some (⟨32⟩, 1))
  ∧ decode flipperBytecode p15 = some (.Push .PUSH1, some (⟨4⟩, 1))
  ∧ decode flipperBytecode p17 = some (.DUP3, .none)
  ∧ decode flipperBytecode p18 = some (.ADD, .none)
  ∧ decode flipperBytecode p19 = some (.MSTORE, .none)
  ∧ decode flipperBytecode p20 = some (.Push .PUSH1, some (flipperAuthErrorLen, 1))
  ∧ decode flipperBytecode p22 = some (.Push .PUSH1, some (⟨36⟩, 1))
  ∧ decode flipperBytecode p24 = some (.DUP3, .none)
  ∧ decode flipperBytecode p25 = some (.ADD, .none)
  ∧ decode flipperBytecode p26 = some (.MSTORE, .none)
  ∧ decode flipperBytecode p27 = some (.Push .PUSH1, some (⟨0⟩, 1))
  ∧ decode flipperBytecode p29 = some (.DUP1, .none)
  ∧ decode flipperBytecode p30 = some (.MLOAD, .none)
  ∧ decode flipperBytecode p31 = some (.Push .PUSH1, some (⟨32⟩, 1))
  ∧ decode flipperBytecode p33 = some (.Push .PUSH2, some (flipperAuthErrorOffset, 2))
  ∧ decode flipperBytecode p36 = some (.DUP4, .none)
  ∧ decode flipperBytecode p37 = some (.CODECOPY, .none)
  ∧ decode flipperBytecode p38 = some (.DUP2, .none)
  ∧ decode flipperBytecode p39 = some (.MLOAD, .none)
  ∧ decode flipperBytecode p40 = some (.SWAP2, .none)
  ∧ decode flipperBytecode p41 = some (.MSTORE, .none)
  ∧ decode flipperBytecode p42 = some (.Push .PUSH1, some (⟨68⟩, 1))
  ∧ decode flipperBytecode p44 = some (.DUP3, .none)
  ∧ decode flipperBytecode p45 = some (.ADD, .none)
  ∧ decode flipperBytecode p46 = some (.MSTORE, .none)
  ∧ decode flipperBytecode p47 = some (.SWAP1, .none)
  ∧ decode flipperBytecode p48 = some (.MLOAD, .none)
  ∧ decode flipperBytecode p49 = some (.SWAP1, .none)
  ∧ decode flipperBytecode p50 = some (.DUP2, .none)
  ∧ decode flipperBytecode p51 = some (.SWAP1, .none)
  ∧ decode flipperBytecode p52 = some (.SUB, .none)
  ∧ decode flipperBytecode p54 = some (.Push .PUSH1, some (⟨100⟩, 1))
  ∧ decode flipperBytecode p55 = some (.ADD, .none)
  ∧ decode flipperBytecode p56 = some (.SWAP1, .none)
  ∧ decode flipperBytecode p57 = some (.REVERT, .none)

set_option maxHeartbeats 0 in
theorem RD.flipperAuthCodecopyRevertTail {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {pc : UInt256}
    {stk : List UInt256} {mem rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD flipperBytecode ee g s0 pc stk mem (UInt256.ofNat 3) rdata acc k C)
    (hwf : flipperAuthCodecopyRevertTailWf pc)
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hov : stk.length + 7 ≤ 1024) :
    RDrev flipperBytecode g s0 := by
  rcases hwf with
    ⟨hd0, hd2, hd3, hd4, hd8, hd10, hd11, hd12, hd13, hd15, hd17, hd18,
      hd19, hd20, hd22, hd24, hd25, hd26, hd27, hd29, hd30, hd31, hd33,
      hd36, hd37, hd38, hd39, hd40, hd41, hd42, hd44, hd45, hd46, hd47,
      hd48, hd49, hd50, hd51, hd52, hd54, hd55, hd56, hd57⟩
  have rdMload := evm_run h with [
    raw push1 ⟨64⟩ hd0 (by evm_ov),
    raw dup1 hd2 (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) hd3 mem_cost
      (mloadFreePtrValue (by rw [hmem]; decide) (by decide) hread64)
      (by decide) (by evm_ov)]
  have rdSelectorRaw := rdMload.pushConst (⟨4594637⟩ : UInt256)
    (width := 3) (op := .PUSH3) (by decide) hd4
    (by simp only [List.length_cons]; omega)
  have rdPrefix := evm_run rdSelectorRaw with [
    raw push1 ⟨229⟩ hd8 (by evm_ov),
    raw shl hd10 (by evm_ov),
    raw dup2 hd11 (by evm_ov),
    raw mstore 6 (solcErrorStringMem0 mem) (UInt256.ofNat 5)
      hd12 mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨32⟩ hd13 (by evm_ov),
    raw push1 ⟨4⟩ hd15 (by evm_ov),
    raw dup3 hd17 (by evm_ov),
    raw add hd18 (by evm_ov),
    raw mstore 3 (solcErrorStringMem1 mem) (UInt256.ofNat 6)
      hd19 mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 flipperAuthErrorLen hd20 (by evm_ov),
    raw push1 ⟨36⟩ hd22 (by evm_ov),
    raw dup3 hd24 (by evm_ov),
    raw add hd25 (by evm_ov),
    raw mstore 3 (solcErrorStringMem2 flipperAuthErrorLen mem) (UInt256.ofNat 7)
      hd26 mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨0⟩ hd27 (by evm_ov),
    raw dup1 hd29 (by evm_ov),
    raw mload 0 (flipperAuthOriginalWord mem) (UInt256.ofNat 7)
      hd30 mem_cost
      (by
        unfold flipperAuthOriginalWord
        rw [if_neg]
        · rfl
        · rw [solcErrorStringMem2_size flipperAuthErrorLen hmem]
          native_decide)
      (by decide) (by evm_ov),
    raw push1 ⟨32⟩ hd31 (by evm_ov),
    raw push2 flipperAuthErrorOffset hd33 (by evm_ov),
    raw dup4 hd36 (by simp only [List.length_cons]; omega)]
  have hcopy :
      flipperBytecode.write flipperAuthErrorOffset.toNat
          (solcErrorStringMem2 flipperAuthErrorLen mem) 0 32 =
        flipperAuthScratchMem mem := by
    rfl
  have rdCopy := rdPrefix.codecopy 0 (flipperAuthScratchMem mem) (UInt256.ofNat 7)
    hd37
    (fun s haws hstks => by
      simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstks,
        List.getElem!_cons_zero, List.getElem!_cons_succ]
      native_decide)
    hcopy
    (by native_decide)
    (by evm_ov)
  have rdRestorePrefix := evm_run rdCopy with [
    raw dup2 hd38 (by evm_ov),
    raw mload 0 (flipperAuthScratchWord mem) (UInt256.ofNat 7)
      hd39 mem_cost
      (by
        unfold flipperAuthScratchWord
        rw [if_neg]
        · rfl
        · rw [flipperAuthScratchMem_size hmem]
          native_decide)
      (by decide) (by evm_ov),
    raw swap2 hd40 (by evm_ov)]
  have rdRestored := rdRestorePrefix.mstore 0 (flipperAuthRestoredMem mem)
    (UInt256.ofNat 7) hd41 mem_cost (by rfl) (by decide) (by evm_ov)
  have rdPayloadPrefix := evm_run rdRestored with [
    raw push1 ⟨68⟩ hd42 (by evm_ov),
    raw dup3 hd44 (by evm_ov),
    raw add hd45 (by evm_ov)]
  have rdPayload := rdPayloadPrefix.mstore 3 (flipperAuthCodecopyErrorMem mem)
    (UInt256.ofNat 8) hd46 mem_cost (by rfl) (by decide) (by evm_ov)
  exact evm_run rdPayload with [
    raw swap1 hd47 (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 8)
      hd48 mem_cost (flipperAuthCodecopyErrorMem_mload64 hmem hread64)
      (by decide) (by evm_ov),
    raw swap1 hd49 (by evm_ov),
    raw dup2 hd50 (by evm_ov),
    raw swap1 hd51 (by evm_ov),
    raw sub hd52 (by evm_ov),
    raw push1 ⟨100⟩ hd54 (by evm_ov),
    raw add hd55 (by evm_ov),
    raw swap1 hd56 (by evm_ov),
    raw rev 0 hd57 mem_cost (by evm_ov)]

theorem RD.flipperAuthCheckOk {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {pc okPc key ret : UInt256} {R : List UInt256}
    {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD code ee g s0 pc (key :: ret :: R)
        solcFreePtrMem (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hwf : flipperAuthCheckWf code pc okPc)
    (hauth : solcSlotWord σ ee (solcMappingSlot ⟨0⟩ (solcSourceWord ee)) = ⟨1⟩)
    (hok : (D_J code 0).contains okPc = true)
    (hov : R.length + 8 ≤ 1024) :
    ∃ k' C', RD code ee g s0 okPc (key :: ret :: R)
      (twoWordHashMem (solcSourceWord ee) ⟨0⟩ solcFreePtrMem)
      (UInt256.ofNat 3) rdata (cA, σ) k' C' := by
  rcases hwf with
    ⟨hd0, hd1, hd2, hd4, hd5, hd6, hd7, hd9, hd10, hd11, hd12, hd14, hd15,
      hd16, hd17, hd19, hd20, hd23⟩
  have rd6 := evm_run h with [
    raw jumpdest hd0 (by evm_ov),
    raw caller hd1 (by evm_ov),
    raw push1 ⟨0⟩ hd2 (by evm_ov),
    raw swap1 hd4 (by evm_ov),
    raw dup2 hd5 (by evm_ov)]
  have rd7 := rd6.mstore 0 (wordAt0Mem (solcSourceWord ee) solcFreePtrMem)
    (UInt256.ofNat 3) hd6 mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd11 := evm_run rd7 with [
    raw push1 ⟨32⟩ hd7 (by evm_ov),
    raw dup2 hd9 (by evm_ov),
    raw swap1 hd10 (by evm_ov)]
  have rd12 := rd11.mstore 0 (twoWordHashMem (solcSourceWord ee) ⟨0⟩ solcFreePtrMem)
    (UInt256.ofNat 3) hd11 mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd15 := evm_run rd12 with [
    raw push1 ⟨64⟩ hd12 (by evm_ov),
    raw swap1 hd14 (by evm_ov)]
  have hslot := twoWordHashMem_solcMappingSlot ⟨0⟩ (solcSourceWord ee) solcFreePtrMem_size
  have rd16 := rd15.keccak256 0 (solcMappingSlot ⟨0⟩ (solcSourceWord ee))
    (UInt256.ofNat 3) hd15 mem_cost hslot (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd17⟩ := rd16.sload hd16 (by evm_ov)
  have rd19 := rd17.push1 ⟨1⟩ hd17 (by evm_ov)
  have rd20₀ := rd19.eq hd19 (by evm_ov)
  have hauthRaw :
      (σ.find? ee.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD (solcMappingSlot ⟨0⟩ (solcSourceWord ee)) ⟨0⟩)) =
          ⟨1⟩ := by
    simpa [solcSlotWord] using hauth
  have rd20 := rd20₀
  rw [hauthRaw, uInt256_eq_self] at rd20
  have rd23 := rd20.push2 okPc hd20 (by evm_ov)
  exact ⟨_, _, rd23.jumpiT hd23 one_ne_zero_uint hok (by evm_ov)⟩

theorem RD.flipperAuthCheckRevert {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {pc okPc key ret : UInt256} {R : List UInt256}
    {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD flipperBytecode ee g s0 pc (key :: ret :: R)
        solcFreePtrMem (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hwf : flipperAuthCheckWf flipperBytecode pc okPc)
    (htail : flipperAuthCodecopyRevertTailWf (flipperAuthTailPc pc))
    (hauth : solcSlotWord σ ee (solcMappingSlot ⟨0⟩ (solcSourceWord ee)) ≠ ⟨1⟩)
    (hov : R.length + 9 ≤ 1024) :
    RDrev flipperBytecode g s0 := by
  rcases hwf with
    ⟨hd0, hd1, hd2, hd4, hd5, hd6, hd7, hd9, hd10, hd11, hd12, hd14, hd15,
      hd16, hd17, hd19, hd20, hd23⟩
  have rd6 := evm_run h with [
    raw jumpdest hd0 (by evm_ov),
    raw caller hd1 (by evm_ov),
    raw push1 ⟨0⟩ hd2 (by evm_ov),
    raw swap1 hd4 (by evm_ov),
    raw dup2 hd5 (by evm_ov)]
  have rd7 := rd6.mstore 0 (wordAt0Mem (solcSourceWord ee) solcFreePtrMem)
    (UInt256.ofNat 3) hd6 mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd11 := evm_run rd7 with [
    raw push1 ⟨32⟩ hd7 (by evm_ov),
    raw dup2 hd9 (by evm_ov),
    raw swap1 hd10 (by evm_ov)]
  have rd12 := rd11.mstore 0 (twoWordHashMem (solcSourceWord ee) ⟨0⟩ solcFreePtrMem)
    (UInt256.ofNat 3) hd11 mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd15 := evm_run rd12 with [
    raw push1 ⟨64⟩ hd12 (by evm_ov),
    raw swap1 hd14 (by evm_ov)]
  have hslot := twoWordHashMem_solcMappingSlot ⟨0⟩ (solcSourceWord ee) solcFreePtrMem_size
  have rd16 := rd15.keccak256 0 (solcMappingSlot ⟨0⟩ (solcSourceWord ee))
    (UInt256.ofNat 3) hd15 mem_cost hslot (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd17⟩ := rd16.sload hd16 (by evm_ov)
  have rd19 := rd17.push1 ⟨1⟩ hd17 (by evm_ov)
  have rd20₀ := rd19.eq hd19 (by evm_ov)
  have hauthRaw :
      (σ.find? ee.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD (solcMappingSlot ⟨0⟩ (solcSourceWord ee)) ⟨0⟩)) ≠
          ⟨1⟩ := by
    simpa [solcSlotWord] using hauth
  have heq0 :
      UInt256.eq ⟨1⟩
        (σ.find? ee.codeOwner |>.option ⟨0⟩
          (fun acc => acc.storage.findD (solcMappingSlot ⟨0⟩ (solcSourceWord ee)) ⟨0⟩)) =
          ⟨0⟩ := by
    exact u256_eq_of_ne (fun h1 => hauthRaw h1.symm)
  have rd20 := rd20₀
  rw [heq0] at rd20
  have rd23 := rd20.push2 okPc hd20 (by evm_ov)
  have rdTail₀ := rd23.jumpiNT hd23 (by decide : (⟨0⟩ : UInt256) = ⟨0⟩) (by evm_ov)
  exact RD.flipperAuthCodecopyRevertTail (by simpa [flipperAuthTailPc] using rdTail₀)
    htail
    (twoWordHashMem_size_96 (solcSourceWord ee) ⟨0⟩ solcFreePtrMem_size)
    (twoWordHashMem_read64 (solcSourceWord ee) ⟨0⟩ solcFreePtrMem_size solcFreePtrMem_read64)
    (by
      simp only [List.length_cons]
      omega)

@[reducible] def flipperMappingStoreOneWf (code : ByteArray) (pc : UInt256) : Prop :=
  let p1 := pc + ⟨1⟩
  let p3 := p1 + UInt256.ofNat 2
  let p5 := p3 + UInt256.ofNat 2
  let p7 := p5 + UInt256.ofNat 2
  let p8 := p7 + ⟨1⟩
  let p9 := p8 + ⟨1⟩
  let p10 := p9 + ⟨1⟩
  let p12 := p10 + UInt256.ofNat 2
  let p13 := p12 + ⟨1⟩
  let p14 := p13 + ⟨1⟩
  let p15 := p14 + ⟨1⟩
  let p17 := p15 + UInt256.ofNat 2
  let p18 := p17 + ⟨1⟩
  let p19 := p18 + ⟨1⟩
  let p20 := p19 + ⟨1⟩
  let p22 := p20 + UInt256.ofNat 2
  let p23 := p22 + ⟨1⟩
  let p24 := p23 + ⟨1⟩
  let p26 := p24 + UInt256.ofNat 2
  let p27 := p26 + ⟨1⟩
  let p28 := p27 + ⟨1⟩
  decode code pc = some (.JUMPDEST, .none)
  ∧ decode code p1 = some (.Push .PUSH1, some (⟨1⟩, 1))
  ∧ decode code p3 = some (.Push .PUSH1, some (⟨1⟩, 1))
  ∧ decode code p5 = some (.Push .PUSH1, some (⟨160⟩, 1))
  ∧ decode code p7 = some (.SHL, .none)
  ∧ decode code p8 = some (.SUB, .none)
  ∧ decode code p9 = some (.AND, .none)
  ∧ decode code p10 = some (.Push .PUSH1, some (⟨0⟩, 1))
  ∧ decode code p12 = some (.SWAP1, .none)
  ∧ decode code p13 = some (.DUP2, .none)
  ∧ decode code p14 = some (.MSTORE, .none)
  ∧ decode code p15 = some (.Push .PUSH1, some (⟨32⟩, 1))
  ∧ decode code p17 = some (.DUP2, .none)
  ∧ decode code p18 = some (.SWAP1, .none)
  ∧ decode code p19 = some (.MSTORE, .none)
  ∧ decode code p20 = some (.Push .PUSH1, some (⟨64⟩, 1))
  ∧ decode code p22 = some (.SWAP1, .none)
  ∧ decode code p23 = some (.KECCAK256, .none)
  ∧ decode code p24 = some (.Push .PUSH1, some (⟨1⟩, 1))
  ∧ decode code p26 = some (.SWAP1, .none)
  ∧ decode code p27 = some (.SSTORE, .none)
  ∧ decode code p28 = some (.JUMP, .none)

theorem RD.flipperMappingStoreOne {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {pc key ret : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD code ee g s0 pc (key :: ret :: R) mem (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hwf : flipperMappingStoreOneWf code pc)
    (hret : (D_J code 0).contains ret = true)
    (hperm : ee.perm = true)
    (hmem : mem.size = 96)
    (hcanonKey : key.toNat < EVM.addressModulus)
    (hov : R.length + 6 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ret R (twoWordHashMem key ⟨0⟩ mem) (UInt256.ofNat 3) rdata
      (cA, sstoreAccountMap ee.codeOwner σ (solcMappingSlot ⟨0⟩ key) ⟨1⟩) k' C' := by
  rcases hwf with
    ⟨hd0, hd1, hd3, hd5, hd7, hd8, hd9, hd10, hd12, hd13, hd14, hd15,
      hd17, hd18, hd19, hd20, hd22, hd23, hd24, hd26, hd27, hd28⟩
  have hmask : UInt256.land solcAddrMask key = key :=
    solcAddrMask_clean_left hcanonKey
  have hmaskLiteral :
      UInt256.land (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩) key =
        key := by
    rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by decide]
    exact hmask
  have rdMasked := evm_run h with [
    raw jumpdest hd0 (by evm_ov),
    raw push1 ⟨1⟩ hd1 (by evm_ov),
    raw push1 ⟨1⟩ hd3 (by evm_ov),
    raw push1 ⟨160⟩ hd5 (by evm_ov),
    raw shl hd7 (by evm_ov),
    raw sub hd8 (by evm_ov),
    raw and hd9 (by evm_ov)]
  rw [hmaskLiteral] at rdMasked
  have rdMstore0Prefix := evm_run rdMasked with [
    raw push1 ⟨0⟩ hd10 (by evm_ov),
    raw swap1 hd12 (by evm_ov),
    raw dup2 hd13 (by evm_ov)]
  have rdAfterKey := rdMstore0Prefix.mstore 0 (wordAt0Mem key mem)
    (UInt256.ofNat 3) hd14 mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rdMstoreSlotPrefix := evm_run rdAfterKey with [
    raw push1 ⟨32⟩ hd15 (by evm_ov),
    raw dup2 hd17 (by evm_ov),
    raw swap1 hd18 (by evm_ov)]
  have rdHashMem := rdMstoreSlotPrefix.mstore 0 (twoWordHashMem key ⟨0⟩ mem)
    (UInt256.ofNat 3) hd19 mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rdKeccakPrefix := evm_run rdHashMem with [
    raw push1 ⟨64⟩ hd20 (by evm_ov),
    raw swap1 hd22 (by evm_ov)]
  have hslot := twoWordHashMem_solcMappingSlot ⟨0⟩ key hmem
  have rdSlot := rdKeccakPrefix.keccak256 0 (solcMappingSlot ⟨0⟩ key)
    (UInt256.ofNat 3) hd23 mem_cost hslot (by native_decide) (by evm_ov)
  have rdBeforeStore := evm_run rdSlot with [
    raw push1 ⟨1⟩ hd24 (by evm_ov),
    raw swap1 hd26 (by evm_ov)]
  obtain ⟨_, _, rdOut⟩ := rdBeforeStore.sstore hperm hd27 (by evm_ov)
  exact ⟨_, _, rdOut.jump hd28 hret (by evm_ov)⟩

@[reducible] def flipperMappingStoreZeroWf (code : ByteArray) (pc : UInt256) : Prop :=
  let p1 := pc + ⟨1⟩
  let p3 := p1 + UInt256.ofNat 2
  let p5 := p3 + UInt256.ofNat 2
  let p7 := p5 + UInt256.ofNat 2
  let p8 := p7 + ⟨1⟩
  let p9 := p8 + ⟨1⟩
  let p10 := p9 + ⟨1⟩
  let p12 := p10 + UInt256.ofNat 2
  let p13 := p12 + ⟨1⟩
  let p14 := p13 + ⟨1⟩
  let p15 := p14 + ⟨1⟩
  let p17 := p15 + UInt256.ofNat 2
  let p18 := p17 + ⟨1⟩
  let p19 := p18 + ⟨1⟩
  let p20 := p19 + ⟨1⟩
  let p22 := p20 + UInt256.ofNat 2
  let p23 := p22 + ⟨1⟩
  let p24 := p23 + ⟨1⟩
  let p25 := p24 + ⟨1⟩
  decode code pc = some (.JUMPDEST, .none)
  ∧ decode code p1 = some (.Push .PUSH1, some (⟨1⟩, 1))
  ∧ decode code p3 = some (.Push .PUSH1, some (⟨1⟩, 1))
  ∧ decode code p5 = some (.Push .PUSH1, some (⟨160⟩, 1))
  ∧ decode code p7 = some (.SHL, .none)
  ∧ decode code p8 = some (.SUB, .none)
  ∧ decode code p9 = some (.AND, .none)
  ∧ decode code p10 = some (.Push .PUSH1, some (⟨0⟩, 1))
  ∧ decode code p12 = some (.SWAP1, .none)
  ∧ decode code p13 = some (.DUP2, .none)
  ∧ decode code p14 = some (.MSTORE, .none)
  ∧ decode code p15 = some (.Push .PUSH1, some (⟨32⟩, 1))
  ∧ decode code p17 = some (.DUP2, .none)
  ∧ decode code p18 = some (.SWAP1, .none)
  ∧ decode code p19 = some (.MSTORE, .none)
  ∧ decode code p20 = some (.Push .PUSH1, some (⟨64⟩, 1))
  ∧ decode code p22 = some (.DUP2, .none)
  ∧ decode code p23 = some (.KECCAK256, .none)
  ∧ decode code p24 = some (.SSTORE, .none)
  ∧ decode code p25 = some (.JUMP, .none)

theorem RD.flipperMappingStoreZero {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {pc key ret : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD code ee g s0 pc (key :: ret :: R) mem (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hwf : flipperMappingStoreZeroWf code pc)
    (hret : (D_J code 0).contains ret = true)
    (hperm : ee.perm = true)
    (hmem : mem.size = 96)
    (hcanonKey : key.toNat < EVM.addressModulus)
    (hov : R.length + 6 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ret R (twoWordHashMem key ⟨0⟩ mem) (UInt256.ofNat 3) rdata
      (cA, sstoreAccountMap ee.codeOwner σ (solcMappingSlot ⟨0⟩ key) ⟨0⟩) k' C' := by
  rcases hwf with
    ⟨hd0, hd1, hd3, hd5, hd7, hd8, hd9, hd10, hd12, hd13, hd14, hd15,
      hd17, hd18, hd19, hd20, hd22, hd23, hd24, hd25⟩
  have hmask : UInt256.land solcAddrMask key = key :=
    solcAddrMask_clean_left hcanonKey
  have hmaskLiteral :
      UInt256.land (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩) key =
        key := by
    rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by decide]
    exact hmask
  have rdMasked := evm_run h with [
    raw jumpdest hd0 (by evm_ov),
    raw push1 ⟨1⟩ hd1 (by evm_ov),
    raw push1 ⟨1⟩ hd3 (by evm_ov),
    raw push1 ⟨160⟩ hd5 (by evm_ov),
    raw shl hd7 (by evm_ov),
    raw sub hd8 (by evm_ov),
    raw and hd9 (by evm_ov)]
  rw [hmaskLiteral] at rdMasked
  have rdMstore0Prefix := evm_run rdMasked with [
    raw push1 ⟨0⟩ hd10 (by evm_ov),
    raw swap1 hd12 (by evm_ov),
    raw dup2 hd13 (by evm_ov)]
  have rdAfterKey := rdMstore0Prefix.mstore 0 (wordAt0Mem key mem)
    (UInt256.ofNat 3) hd14 mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rdMstoreSlotPrefix := evm_run rdAfterKey with [
    raw push1 ⟨32⟩ hd15 (by evm_ov),
    raw dup2 hd17 (by evm_ov),
    raw swap1 hd18 (by evm_ov)]
  have rdHashMem := rdMstoreSlotPrefix.mstore 0 (twoWordHashMem key ⟨0⟩ mem)
    (UInt256.ofNat 3) hd19 mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rdKeccakPrefix := evm_run rdHashMem with [
    raw push1 ⟨64⟩ hd20 (by evm_ov),
    raw dup2 hd22 (by evm_ov)]
  have hslot := twoWordHashMem_solcMappingSlot ⟨0⟩ key hmem
  have rdSlot := rdKeccakPrefix.keccak256 0 (solcMappingSlot ⟨0⟩ key)
    (UInt256.ofNat 3) hd23 mem_cost hslot (by native_decide) (by evm_ov)
  obtain ⟨_, _, rdOut⟩ := rdSlot.sstore hperm hd24 (by evm_ov)
  exact ⟨_, _, rdOut.jump hd25 hret (by evm_ov)⟩

end Benchmarks.Dss.Flipper
