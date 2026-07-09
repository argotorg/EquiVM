import Benchmarks.Dss.Vat.Bytecode
import Reasoning.ABI
import Reasoning.Dispatch
import Reasoning.Memory
import Reasoning.Refinement
import Reasoning.SolmBody
import Reasoning.Solc
import Reasoning.Stepping
import Reasoning.Storage
import Reasoning.Theory
import Mathlib.Tactic.IntervalCases

/-!
# MakerDAO/Sky DSS Vat shared proof foundation

Contract-wide selector notation and proof-shape abbreviations for the optimized Vat runtime.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

namespace Benchmarks.Dss.Vat

/-- The 4-byte selector word computed by `CALLDATALOAD(0); SHR 224`. -/
abbrev vatSelWord (I : ExecutionEnv) : UInt256 :=
  UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩

/-- The 4-byte selector of `I`'s calldata equals `sel`. -/
abbrev selIs (I : ExecutionEnv) (sel : ByteArray) : Prop :=
  (sel == I.calldata.extract 0 4) = true

/-- Function selectors in `contract.transitions` order. -/
def vatSelBytes : ℕ → ByteArray
  | 0 => ⟨#[0xba, 0xbe, 0x8a, 0x3f]⟩ -- Line()
  | 1 => ⟨#[0x69, 0x24, 0x50, 0x09]⟩ -- cage()
  | 2 => ⟨#[0x45, 0x38, 0xc4, 0xeb]⟩ -- can(address,address)
  | 3 => ⟨#[0x6c, 0x25, 0xb3, 0x46]⟩ -- dai(address)
  | 4 => ⟨#[0x0d, 0xca, 0x59, 0xc1]⟩ -- debt()
  | 5 => ⟨#[0x9c, 0x52, 0xa7, 0xf1]⟩ -- deny(address)
  | 6 => ⟨#[0x1a, 0x0b, 0x28, 0x7e]⟩ -- file(bytes32,bytes32,uint256)
  | 7 => ⟨#[0x29, 0xae, 0x81, 0x14]⟩ -- file(bytes32,uint256)
  | 8 => ⟨#[0x61, 0x11, 0xbe, 0x2e]⟩ -- flux(bytes32,address,address,uint256)
  | 9 => ⟨#[0xb6, 0x53, 0x37, 0xdf]⟩ -- fold(bytes32,address,int256)
  | 10 => ⟨#[0x87, 0x0c, 0x61, 0x6d]⟩ -- fork(bytes32,address,address,int256,int256)
  | 11 => ⟨#[0x76, 0x08, 0x87, 0x03]⟩ -- frob(bytes32,address,address,address,int256,int256)
  | 12 => ⟨#[0x21, 0x44, 0x14, 0xd5]⟩ -- gem(bytes32,address)
  | 13 => ⟨#[0x7b, 0xab, 0x3f, 0x40]⟩ -- grab(bytes32,address,address,address,int256,int256)
  | 14 => ⟨#[0xf3, 0x7a, 0xc6, 0x1c]⟩ -- heal(uint256)
  | 15 => ⟨#[0xa3, 0xb2, 0x2f, 0xc4]⟩ -- hope(address)
  | 16 => ⟨#[0xd9, 0x63, 0x8d, 0x36]⟩ -- ilks(bytes32)
  | 17 => ⟨#[0x3b, 0x66, 0x31, 0x95]⟩ -- init(bytes32)
  | 18 => ⟨#[0x95, 0x7a, 0xa5, 0x8c]⟩ -- live()
  | 19 => ⟨#[0xbb, 0x35, 0x78, 0x3b]⟩ -- move(address,address,uint256)
  | 20 => ⟨#[0xdc, 0x4d, 0x20, 0xfa]⟩ -- nope(address)
  | 21 => ⟨#[0x65, 0xfa, 0xe3, 0x5e]⟩ -- rely(address)
  | 22 => ⟨#[0xf0, 0x59, 0x21, 0x2a]⟩ -- sin(address)
  | 23 => ⟨#[0x7c, 0xdd, 0x3f, 0xde]⟩ -- slip(bytes32,address,int256)
  | 24 => ⟨#[0xf2, 0x4e, 0x23, 0xeb]⟩ -- suck(address,address,uint256)
  | 25 => ⟨#[0x24, 0x24, 0xbe, 0x5c]⟩ -- urns(bytes32,address)
  | 26 => ⟨#[0x2d, 0x61, 0xa3, 0x55]⟩ -- vice()
  | _ => ⟨#[0xbf, 0x35, 0x3d, 0xbb]⟩ -- wards(address)

/-- The common top-level shape of a routed Vat runtime body proof. -/
abbrev VatBodyTheorem (i : ℕ) : Prop :=
  ∀ {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256},
    I.code = vatBytecode →
    I.calldata.size < UInt256.size →
    I.perm = true →
    I.weiValue = ⟨0⟩ →
    selIs I (vatSelBytes i) →
    accountMapEquiv σ_evm σ_solm →
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I

def vatSlotWord (slot : UInt256) (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  solcSlotWord σ I slot

theorem vatStorageLocLoad_uint256 (evm : EVM.State) (slot : UInt256) :
    storageLocLoad evm (wordLoc slot) =
      .int (Int.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot).toNat) := by
  simpa [wordLoc, uint256Loc] using storageLocLoad_uint256 evm slot

theorem vatStorageLocStore_uint256 (evm : EVM.State) (slot val : UInt256) :
    storageLocStore evm (wordLoc slot) (.int (Int.ofNat val.toNat)) =
      some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot val) := by
  simpa [wordLoc, uint256Loc] using storageLocStore_uint256 evm slot val

theorem vatDecodeScalarWordWithMode_legacyInt256_ok {bytes : List UInt8} {start : Nat}
    (hlen : ((bytes.drop start).take 32).length = 32) :
    decodeScalarWordWithMode? DecodeMode.legacySolc05 int256 bytes start =
      some
        (.int
          (if (ABI.bytesToWord ((bytes.drop start).take 32)).toNat < EVM.twoPow 255 then
            Int.ofNat (ABI.bytesToWord ((bytes.drop start).take 32)).toNat
          else
            Int.ofNat (ABI.bytesToWord ((bytes.drop start).take 32)).toNat -
              Int.ofNat EVM.wordModulus),
          start + 32) := by
  have hltWord :
      ↑(ABI.bytesToWord ((bytes.drop start).take 32)).val < EVM.wordModulus := by
    change (ABI.bytesToWord ((bytes.drop start).take 32)).val.val < EVM.twoPow 256
    exact (ABI.bytesToWord ((bytes.drop start).take 32)).val.isLt
  have hmodVal :
      (↑(ABI.bytesToWord ((bytes.drop start).take 32)).val) % EVM.wordModulus =
        ↑(ABI.bytesToWord ((bytes.drop start).take 32)).val :=
    Nat.mod_eq_of_lt hltWord
  have hmodInt :
      ((↑(↑(ABI.bytesToWord ((bytes.drop start).take 32)).val) : Int) %
          (↑EVM.wordModulus : Int)) =
        (↑(↑(ABI.bytesToWord ((bytes.drop start).take 32)).val) : Int) := by
    exact Int.emod_eq_of_lt (Int.natCast_nonneg _) (by exact_mod_cast hltWord)
  simp [decodeScalarWordWithMode?, readWord?, readBytes?, decodeABIWord?, int256,
    int256Int, hlen, UInt256.toNat,
    show EVM.twoPow (256 - 1) = EVM.twoPow 255 by rfl,
    show EVM.twoPow 256 = EVM.wordModulus by rfl]
  rw [hmodVal]
  rw [hmodInt]

theorem vatDecodeScalarWords_address_address_address_int256_int256_legacy_ok
    {bytes : List UInt8}
    (hlen32 : ((bytes.drop 32).take 32).length = 32)
    (hlen64 : ((bytes.drop 64).take 32).length = 32)
    (hlen96 : ((bytes.drop 96).take 32).length = 32)
    (hlen128 : ((bytes.drop 128).take 32).length = 32)
    (hlen160 : ((bytes.drop 160).take 32).length = 32) :
    decodeScalarWordsWithMode? DecodeMode.legacySolc05
      [addr, addr, addr, int256, int256] bytes 32 =
      some
        [ .address (AccountAddress.ofNat
            (ABI.bytesToWord ((bytes.drop 32).take 32)).toNat),
          .address (AccountAddress.ofNat
            (ABI.bytesToWord ((bytes.drop 64).take 32)).toNat),
          .address (AccountAddress.ofNat
            (ABI.bytesToWord ((bytes.drop 96).take 32)).toNat),
          .int
            (if (ABI.bytesToWord ((bytes.drop 128).take 32)).toNat < EVM.twoPow 255 then
              Int.ofNat (ABI.bytesToWord ((bytes.drop 128).take 32)).toNat
            else
              Int.ofNat (ABI.bytesToWord ((bytes.drop 128).take 32)).toNat -
                Int.ofNat EVM.wordModulus),
          .int
            (if (ABI.bytesToWord ((bytes.drop 160).take 32)).toNat < EVM.twoPow 255 then
              Int.ofNat (ABI.bytesToWord ((bytes.drop 160).take 32)).toNat
            else
              Int.ofNat (ABI.bytesToWord ((bytes.drop 160).take 32)).toNat -
                Int.ofNat EVM.wordModulus) ] := by
  have haddr32 :
      decodeScalarWordWithMode? DecodeMode.legacySolc05 addr bytes 32 =
        some (.address (AccountAddress.ofNat
          (ABI.bytesToWord ((bytes.drop 32).take 32)).toNat), 32 + 32) := by
    simpa [addr] using
      decodeScalarWord_legacyAddress_ok (bytes := bytes) (start := 32) hlen32
  have haddr64 :
      decodeScalarWordWithMode? DecodeMode.legacySolc05 addr bytes 64 =
        some (.address (AccountAddress.ofNat
          (ABI.bytesToWord ((bytes.drop 64).take 32)).toNat), 64 + 32) := by
    simpa [addr] using
      decodeScalarWord_legacyAddress_ok (bytes := bytes) (start := 64) hlen64
  have haddr96 :
      decodeScalarWordWithMode? DecodeMode.legacySolc05 addr bytes 96 =
        some (.address (AccountAddress.ofNat
          (ABI.bytesToWord ((bytes.drop 96).take 32)).toNat), 96 + 32) := by
    simpa [addr] using
      decodeScalarWord_legacyAddress_ok (bytes := bytes) (start := 96) hlen96
  have hint128 :
      decodeScalarWordWithMode? DecodeMode.legacySolc05 int256 bytes 128 =
        some
          (.int
            (if (ABI.bytesToWord ((bytes.drop 128).take 32)).toNat < EVM.twoPow 255 then
              Int.ofNat (ABI.bytesToWord ((bytes.drop 128).take 32)).toNat
            else
              Int.ofNat (ABI.bytesToWord ((bytes.drop 128).take 32)).toNat -
                Int.ofNat EVM.wordModulus),
            128 + 32) :=
    vatDecodeScalarWordWithMode_legacyInt256_ok (bytes := bytes) (start := 128) hlen128
  have hint160 :
      decodeScalarWordWithMode? DecodeMode.legacySolc05 int256 bytes 160 =
        some
          (.int
            (if (ABI.bytesToWord ((bytes.drop 160).take 32)).toNat < EVM.twoPow 255 then
              Int.ofNat (ABI.bytesToWord ((bytes.drop 160).take 32)).toNat
            else
              Int.ofNat (ABI.bytesToWord ((bytes.drop 160).take 32)).toNat -
                Int.ofNat EVM.wordModulus),
            160 + 32) :=
    vatDecodeScalarWordWithMode_legacyInt256_ok (bytes := bytes) (start := 160) hlen160
  simp only [decodeScalarWordsWithMode?]
  norm_num
  rw [haddr32]
  simp only [Option.bind, bind]
  rw [haddr64]
  simp only [Option.bind, bind]
  rw [haddr96]
  simp only [Option.bind, bind]
  rw [hint128]
  simp only [Option.bind, bind]
  rw [hint160]
  rfl

set_option maxHeartbeats 0 in
theorem vatDecodeABIValues_bytes32_address_address_address_int256_int256_legacy_ok
    {bytes : List UInt8}
    (hlen0 : (bytes.take 32).length = 32)
    (hlen32 : ((bytes.drop 32).take 32).length = 32)
    (hlen64 : ((bytes.drop 64).take 32).length = 32)
    (hlen96 : ((bytes.drop 96).take 32).length = 32)
    (hlen128 : ((bytes.drop 128).take 32).length = 32)
    (hlen160 : ((bytes.drop 160).take 32).length = 32) :
    decodeABIValues? [bytes32, addr, addr, addr, int256, int256] bytes
      0 0 192 192 DecodeMode.legacySolc05 =
        some
          ([ .fixedBytes bytes32Width (bytes.take 32),
             .address (AccountAddress.ofNat
               (ABI.bytesToWord ((bytes.drop 32).take 32)).toNat),
           .address (AccountAddress.ofNat
             (ABI.bytesToWord ((bytes.drop 64).take 32)).toNat),
           .address (AccountAddress.ofNat
             (ABI.bytesToWord ((bytes.drop 96).take 32)).toNat),
           .int
             (if (ABI.bytesToWord ((bytes.drop 128).take 32)).toNat < EVM.twoPow 255 then
               Int.ofNat (ABI.bytesToWord ((bytes.drop 128).take 32)).toNat
             else
               Int.ofNat (ABI.bytesToWord ((bytes.drop 128).take 32)).toNat -
                 Int.ofNat EVM.wordModulus),
           .int
             (if (ABI.bytesToWord ((bytes.drop 160).take 32)).toNat < EVM.twoPow 255 then
               Int.ofNat (ABI.bytesToWord ((bytes.drop 160).take 32)).toNat
             else
                 Int.ofNat (ABI.bytesToWord ((bytes.drop 160).take 32)).toNat -
                   Int.ofNat EVM.wordModulus) ],
           192) := by
    have hbytes32 :
        decodeABIValue? (.elem (.bytes bytes32Width)) bytes 0 DecodeMode.legacySolc05 =
          some (.fixedBytes bytes32Width (bytes.take 32), 32) := by
      simp only [bytes32Width, decodeABIValue?, readBytes?, bind, Option.bind]
      rw [if_pos (by simpa using hlen0)]
      simp [zeroPadding?, readBytes?]
    have htail :
        decodeABIValues? [addr, addr, addr, int256, int256] bytes 0 32 192 192
          DecodeMode.legacySolc05 =
          some
            ([ .address (AccountAddress.ofNat
                (ABI.bytesToWord ((bytes.drop 32).take 32)).toNat),
               .address (AccountAddress.ofNat
                (ABI.bytesToWord ((bytes.drop 64).take 32)).toNat),
               .address (AccountAddress.ofNat
                (ABI.bytesToWord ((bytes.drop 96).take 32)).toNat),
               .int
                (if (ABI.bytesToWord ((bytes.drop 128).take 32)).toNat < EVM.twoPow 255 then
                  Int.ofNat (ABI.bytesToWord ((bytes.drop 128).take 32)).toNat
                else
                  Int.ofNat (ABI.bytesToWord ((bytes.drop 128).take 32)).toNat -
                    Int.ofNat EVM.wordModulus),
               .int
                (if (ABI.bytesToWord ((bytes.drop 160).take 32)).toNat < EVM.twoPow 255 then
                  Int.ofNat (ABI.bytesToWord ((bytes.drop 160).take 32)).toNat
                else
                  Int.ofNat (ABI.bytesToWord ((bytes.drop 160).take 32)).toNat -
                    Int.ofNat EVM.wordModulus) ],
             192) := by
      rw [decodeABIValues_scalarWordsWithMode_eq
        (mode := DecodeMode.legacySolc05)
        (types := [addr, addr, addr, int256, int256])
        (bytes := bytes) (cursor := 32) (total := 192)
        (by native_decide) (by norm_num)]
      rw [vatDecodeScalarWords_address_address_address_int256_int256_legacy_ok
        (bytes := bytes) hlen32 hlen64 hlen96 hlen128 hlen160]
    rw [decodeABIValues?]
    simp only [bytes32, isDynamicABIType, staticABIEncodedSize?, Bool.false_eq_true, if_false,
      Nat.zero_add, Option.bind, bind]
    rw [hbytes32]
    simp only [Option.bind, bind]
    rw [if_pos (by norm_num)]
    rw [show max 192 32 = 192 by norm_num]
    rw [htail]

set_option maxHeartbeats 0 in
theorem vatDecodeCalldata_legacyBytes32_address_address_address_int256_int256_ok
    {cd : ByteArray} {a b c d e f : Solm.Ident} (hsz196 : 196 ≤ cd.size) :
    decodeCalldataWithMode DecodeMode.legacySolc05 [a, b, c, d, e, f]
      [bytes32, addr, addr, addr, int256, int256] cd =
      some (((((((∅ : Store).insert a
        (.fixedBytes bytes32Width ((cd.toList.drop 4).take 32))).insert b
        (.address (AccountAddress.ofNat (calldataWord cd 36).toNat))).insert c
        (.address (AccountAddress.ofNat (calldataWord cd 68).toNat))).insert d
        (.address (AccountAddress.ofNat (calldataWord cd 100).toNat))).insert e
        (.int
          (if (calldataWord cd 132).toNat < EVM.twoPow 255 then
            Int.ofNat (calldataWord cd 132).toNat
          else
            Int.ofNat (calldataWord cd 132).toNat - Int.ofNat EVM.wordModulus))).insert f
        (.int
          (if (calldataWord cd 164).toNat < EVM.twoPow 255 then
            Int.ofNat (calldataWord cd 164).toNat
          else
            Int.ofNat (calldataWord cd 164).toNat - Int.ofNat EVM.wordModulus))) := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have htake4 : ((cd.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  have htake36 : ((cd.toList.drop 36).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  have htake68 : ((cd.toList.drop 68).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  have htake100 : ((cd.toList.drop 100).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  have htake132 : ((cd.toList.drop 132).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  have htake164 : ((cd.toList.drop 164).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  have hword36 : ABI.bytesToWord ((cd.toList.drop 36).take 32) = calldataWord cd 36 :=
    decode_word_at_eq cd 36 (by omega) (by norm_num)
  have hword68 : ABI.bytesToWord ((cd.toList.drop 68).take 32) = calldataWord cd 68 :=
    decode_word_at_eq cd 68 (by omega) (by norm_num)
  have hword100 : ABI.bytesToWord ((cd.toList.drop 100).take 32) = calldataWord cd 100 :=
    decode_word_at_eq cd 100 (by omega) (by norm_num)
  have hword132 : ABI.bytesToWord ((cd.toList.drop 132).take 32) = calldataWord cd 132 :=
    decode_word_at_eq cd 132 (by omega) (by norm_num)
  have hword164 : ABI.bytesToWord ((cd.toList.drop 164).take 32) = calldataWord cd 164 :=
    decode_word_at_eq cd 164 (by omega) (by norm_num)
  unfold decodeCalldataWithMode decodeCalldata
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  rw [if_neg (by simp [bytes32, addr, int256, isDynamicABIType])]
  simp only
  simp only [decodeCalldata.decodeArgs]
  rw [show abiTupleHeadSize? [bytes32, addr, addr, addr, int256, int256] =
      some 192 by native_decide]
  simp only [bind, Option.bind]
  rw [if_neg (by rw [List.length_drop, htlen]; omega :
    ¬ (cd.toList.drop 4).length < 192)]
  rw [vatDecodeABIValues_bytes32_address_address_address_int256_int256_legacy_ok
    (bytes := cd.toList.drop 4)
    (by simpa using htake4)
    (by simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
      using htake36)
    (by simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
      using htake68)
    (by simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
      using htake100)
    (by simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
      using htake132)
    (by simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
      using htake164)]
  rw [show ABI.bytesToWord (((cd.toList.drop 4).drop 32).take 32) =
      calldataWord cd 36 from by
    simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hword36]
  rw [show ABI.bytesToWord (((cd.toList.drop 4).drop 64).take 32) =
      calldataWord cd 68 from by
    simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hword68]
  rw [show ABI.bytesToWord (((cd.toList.drop 4).drop 96).take 32) =
      calldataWord cd 100 from by
    simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hword100]
  rw [show ABI.bytesToWord (((cd.toList.drop 4).drop 128).take 32) =
      calldataWord cd 132 from by
    simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hword132]
  rw [show ABI.bytesToWord (((cd.toList.drop 4).drop 160).take 32) =
      calldataWord cd 164 from by
    simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hword164]
  simp only [Option.bind, bind]
  change decodeCalldata.insertValues [a, b, c, d, e, f]
      [ .fixedBytes bytes32Width ((cd.toList.drop 4).take 32),
        .address (AccountAddress.ofNat (calldataWord cd 36).toNat),
        .address (AccountAddress.ofNat (calldataWord cd 68).toNat),
        .address (AccountAddress.ofNat (calldataWord cd 100).toNat),
        .int
          (if (calldataWord cd 132).toNat < EVM.twoPow 255 then
            Int.ofNat (calldataWord cd 132).toNat
          else
            Int.ofNat (calldataWord cd 132).toNat - Int.ofNat EVM.wordModulus),
        .int
          (if (calldataWord cd 164).toNat < EVM.twoPow 255 then
            Int.ofNat (calldataWord cd 164).toNat
          else
            Int.ofNat (calldataWord cd 164).toNat - Int.ofNat EVM.wordModulus) ] ∅ =
      some (((((((∅ : Store).insert a
        (.fixedBytes bytes32Width ((cd.toList.drop 4).take 32))).insert b
        (.address (AccountAddress.ofNat (calldataWord cd 36).toNat))).insert c
        (.address (AccountAddress.ofNat (calldataWord cd 68).toNat))).insert d
        (.address (AccountAddress.ofNat (calldataWord cd 100).toNat))).insert e
        (.int
          (if (calldataWord cd 132).toNat < EVM.twoPow 255 then
            Int.ofNat (calldataWord cd 132).toNat
          else
            Int.ofNat (calldataWord cd 132).toNat - Int.ofNat EVM.wordModulus))).insert f
        (.int
          (if (calldataWord cd 164).toNat < EVM.twoPow 255 then
            Int.ofNat (calldataWord cd 164).toNat
          else
            Int.ofNat (calldataWord cd 164).toNat - Int.ofNat EVM.wordModulus)))
  rfl

@[reducible] def solcSixWordThreeAddressExternalLoadAndJumpWf
    (code : ByteArray) (pc routine : UInt256) : Prop :=
  let p1 := pc + ⟨1⟩
  let p2 := p1 + ⟨1⟩
  let p3 := p2 + ⟨1⟩
  let p4 := p3 + ⟨1⟩
  let p5 := p4 + ⟨1⟩
  let p7 := p5 + UInt256.ofNat 2
  let p9 := p7 + UInt256.ofNat 2
  let p11 := p9 + UInt256.ofNat 2
  let p12 := p11 + ⟨1⟩
  let p13 := p12 + ⟨1⟩
  let p15 := p13 + UInt256.ofNat 2
  let p16 := p15 + ⟨1⟩
  let p17 := p16 + ⟨1⟩
  let p18 := p17 + ⟨1⟩
  let p19 := p18 + ⟨1⟩
  let p20 := p19 + ⟨1⟩
  let p21 := p20 + ⟨1⟩
  let p23 := p21 + UInt256.ofNat 2
  let p24 := p23 + ⟨1⟩
  let p25 := p24 + ⟨1⟩
  let p26 := p25 + ⟨1⟩
  let p27 := p26 + ⟨1⟩
  let p28 := p27 + ⟨1⟩
  let p29 := p28 + ⟨1⟩
  let p31 := p29 + UInt256.ofNat 2
  let p32 := p31 + ⟨1⟩
  let p33 := p32 + ⟨1⟩
  let p34 := p33 + ⟨1⟩
  let p35 := p34 + ⟨1⟩
  let p36 := p35 + ⟨1⟩
  let p38 := p36 + UInt256.ofNat 2
  let p39 := p38 + ⟨1⟩
  let p40 := p39 + ⟨1⟩
  let p41 := p40 + ⟨1⟩
  let p42 := p41 + ⟨1⟩
  let p44 := p42 + UInt256.ofNat 2
  let p45 := p44 + ⟨1⟩
  let p46 := p45 + ⟨1⟩
  let p49 := p46 + UInt256.ofNat 3
  decode code pc = some (.JUMPDEST, .none)
  ∧ decode code p1 = some (.POP, .none)
  ∧ decode code p2 = some (.DUP1, .none)
  ∧ decode code p3 = some (.CALLDATALOAD, .none)
  ∧ decode code p4 = some (.SWAP1, .none)
  ∧ decode code p5 = some (.Push .PUSH1, some (⟨1⟩, 1))
  ∧ decode code p7 = some (.Push .PUSH1, some (⟨1⟩, 1))
  ∧ decode code p9 = some (.Push .PUSH1, some (⟨160⟩, 1))
  ∧ decode code p11 = some (.SHL, .none)
  ∧ decode code p12 = some (.SUB, .none)
  ∧ decode code p13 = some (.Push .PUSH1, some (⟨32⟩, 1))
  ∧ decode code p15 = some (.DUP3, .none)
  ∧ decode code p16 = some (.ADD, .none)
  ∧ decode code p17 = some (.CALLDATALOAD, .none)
  ∧ decode code p18 = some (.DUP2, .none)
  ∧ decode code p19 = some (.AND, .none)
  ∧ decode code p20 = some (.SWAP2, .none)
  ∧ decode code p21 = some (.Push .PUSH1, some (⟨64⟩, 1))
  ∧ decode code p23 = some (.DUP2, .none)
  ∧ decode code p24 = some (.ADD, .none)
  ∧ decode code p25 = some (.CALLDATALOAD, .none)
  ∧ decode code p26 = some (.DUP3, .none)
  ∧ decode code p27 = some (.AND, .none)
  ∧ decode code p28 = some (.SWAP2, .none)
  ∧ decode code p29 = some (.Push .PUSH1, some (⟨96⟩, 1))
  ∧ decode code p31 = some (.DUP3, .none)
  ∧ decode code p32 = some (.ADD, .none)
  ∧ decode code p33 = some (.CALLDATALOAD, .none)
  ∧ decode code p34 = some (.AND, .none)
  ∧ decode code p35 = some (.SWAP1, .none)
  ∧ decode code p36 = some (.Push .PUSH1, some (⟨128⟩, 1))
  ∧ decode code p38 = some (.DUP2, .none)
  ∧ decode code p39 = some (.ADD, .none)
  ∧ decode code p40 = some (.CALLDATALOAD, .none)
  ∧ decode code p41 = some (.SWAP1, .none)
  ∧ decode code p42 = some (.Push .PUSH1, some (⟨160⟩, 1))
  ∧ decode code p44 = some (.ADD, .none)
  ∧ decode code p45 = some (.CALLDATALOAD, .none)
  ∧ decode code p46 = some (.Push .PUSH2, some (routine, 2))
  ∧ decode code p49 = some (.JUMP, .none)

set_option maxHeartbeats 1000000 in
theorem RD.solcSixWordThreeAddressExternalLoadAndJump {code : ByteArray} {g : Sat256}
    {s0 : State} {ee : ExecutionEnv} {k C : ℕ} {decoded ret routine de : UInt256}
    {R : List UInt256} {mem rdata : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD code ee g s0 decoded (de :: ⟨4⟩ :: ret :: R) mem aw rdata acc k C)
    (hwf : solcSixWordThreeAddressExternalLoadAndJumpWf code decoded routine)
    (hroutine : (D_J code 0).contains routine = true)
    (hov : R.length + 10 ≤ 1024) :
    ∃ k' C', RD code ee g s0 routine
      (calldataWord ee.calldata 164 ::
        calldataWord ee.calldata 132 ::
        UInt256.land solcAddrMask (calldataWord ee.calldata 100) ::
        UInt256.land solcAddrMask (calldataWord ee.calldata 68) ::
        UInt256.land solcAddrMask (calldataWord ee.calldata 36) ::
        calldataWord ee.calldata 4 :: ret :: R)
      mem aw rdata acc k' C' := by
  rcases hwf with
    ⟨hd0, hd1, hd2, hd3, hd4, hd5, hd7, hd9, hd11, hd12, hd13, hd15, hd16,
      hd17, hd18, hd19, hd20, hd21, hd23, hd24, hd25, hd26, hd27, hd28, hd29,
      hd31, hd32, hd33, hd34, hd35, hd36, hd38, hd39, hd40, hd41, hd42, hd44,
      hd45, hd46, hd49⟩
  have rd1 := h.jumpdest hd0 (by evm_ov)
  have rd2 := rd1.pop hd1 (by evm_ov)
  have rd3 := rd2.dup1 hd2 (by evm_ov)
  have rd4 := rd3.calldataload hd3 (by evm_ov)
  have rd5 := rd4.swap1 hd4 (by evm_ov)
  have rd7 := rd5.push1 ⟨1⟩ hd5 (by evm_ov)
  have rd9 := rd7.push1 ⟨1⟩ hd7 (by evm_ov)
  have rd11 := rd9.push1 ⟨160⟩ hd9 (by evm_ov)
  have rd12 := rd11.shl hd11 (by evm_ov)
  have rd13 := rd12.sub hd12 (by evm_ov)
  have rd15 := rd13.push1 ⟨32⟩ hd13 (by evm_ov)
  have rd16 := rd15.dup3 hd15 (by evm_ov)
  have rd17 := rd16.add hd16 (by evm_ov)
  have rd18 := rd17.calldataload hd17 (by evm_ov)
  have rd19 := rd18.dup2 hd18 (by evm_ov)
  have rd20 := rd19.and hd19 (by evm_ov)
  have rd21 := rd20.swap2 hd20 (by evm_ov)
  have rd23 := rd21.push1 ⟨64⟩ hd21 (by evm_ov)
  have rd24 := rd23.dup2 hd23 (by evm_ov)
  have rd25 := rd24.add hd24 (by evm_ov)
  have rd26 := rd25.calldataload hd25 (by evm_ov)
  have rd27 := rd26.dup3 hd26 (by evm_ov)
  have rd28 := rd27.and hd27 (by evm_ov)
  have rd29 := rd28.swap2 hd28 (by evm_ov)
  have rd31 := rd29.push1 ⟨96⟩ hd29 (by evm_ov)
  have rd32 := rd31.dup3 hd31 (by evm_ov)
  have rd33 := rd32.add hd32 (by evm_ov)
  have rd34 := rd33.calldataload hd33 (by evm_ov)
  have rd35 := rd34.and hd34 (by evm_ov)
  have rd36 := rd35.swap1 hd35 (by evm_ov)
  have rd38 := rd36.push1 ⟨128⟩ hd36 (by evm_ov)
  have rd39 := rd38.dup2 hd38 (by evm_ov)
  have rd40 := rd39.add hd39 (by evm_ov)
  have rd41 := rd40.calldataload hd40 (by evm_ov)
  have rd42 := rd41.swap1 hd41 (by evm_ov)
  have rd44 := rd42.push1 ⟨160⟩ hd42 (by evm_ov)
  have rd45 := rd44.add hd44 (by evm_ov)
  have rd46 := rd45.calldataload hd45 (by evm_ov)
  have rd49 := rd46.push2 routine hd46 (by evm_ov)
  exact ⟨_, _, by
    simpa [calldataWord, show (⟨4⟩ : UInt256).toNat = 4 from by decide,
      show ((⟨4⟩ : UInt256) + ⟨32⟩).toNat = 36 from by decide,
      show ((⟨4⟩ : UInt256) + ⟨64⟩).toNat = 68 from by decide,
      show ((⟨4⟩ : UInt256) + ⟨96⟩).toNat = 100 from by decide,
      show ((⟨4⟩ : UInt256) + ⟨128⟩).toNat = 132 from by decide,
      show ((⟨4⟩ : UInt256) + ⟨160⟩).toNat = 164 from by decide,
      show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
        solcAddrMask from by decide, u256_land_comm]
      using rd49.jump hd49 hroutine (by evm_ov)⟩

theorem vatUint256GetterBodyReturns (evm : EVM.State) (locals : Store)
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
      exact congrArg EvalResult.ok (vatStorageLocLoad_uint256 evm slot))

theorem vatUint256GetterBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    {transition : TransitionDecl} {entry returnPc routine slot : UInt256}
    (hcode : I.code = vatBytecode)
    (hdispatch : dispatchMsg contract I.calldata = some transition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (transition.params.map Param.name)
        (transitionSignature transition).paramTypes I.calldata = some ∅)
    (hreach : ∃ k C, RD vatBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) entry [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hentry : solcGetterEntryWf vatBytecode entry returnPc routine)
    (hgetter : solcWordSlotGetterWf vatBytecode routine slot)
    (hroutine : (D_J vatBytecode 0).contains routine = true)
    (hreturnJd : (D_J vatBytecode 0).contains returnPc = true)
    (hretmem : solcReturnWordFromMemWf vatBytecode returnPc)
    (hreturn : transition.returnType = [uint256])
    (hbody :
      ExecTransitionBody config contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅ transition.body
        (.returned { contract := contract, locals := ∅ }
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (some [(.int (Int.ofNat (vatSlotWord slot σ_solm I).toNat))]))) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hword : vatSlotWord slot σ_evm I = vatSlotWord slot σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner slot ⟨0⟩
  have hval :
      some [Value.int (Int.ofNat (vatSlotWord slot σ_solm I).toNat)] =
        some [Value.int (Int.ofNat (vatSlotWord slot σ_evm I).toNat)] := by
    rw [hword]
  have henc :
      returnEquiv (UInt256.toByteArray (vatSlotWord slot σ_evm I))
        (some [(.int (Int.ofNat (vatSlotWord slot σ_evm I).toNat))])
        transition.returnType := by
    rw [hreturn]
    exact returnEquiv_of_encode
      (by simpa [uint256] using uint256ReturnEncoding (vatSlotWord slot σ_evm I))
  have hret := RD.solcWordGetterExternal (code := vatBytecode) (g := Sat256.ofUInt256 g)
    (returnPc := returnPc) (entry := entry) (routine := routine) (slot := slot)
    hreach hentry hgetter hroutine hreturnJd hretmem
  have hret' :
      RDret vatBytecode (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) (cA, σ_evm)
        (UInt256.toByteArray (vatSlotWord slot σ_evm I)) := by
    simpa [vatSlotWord] using hret
  exact hret'.reEquivExecutionTransport hcode hdispatch hdecode hbody hval hAccounts henc

@[reducible] def solcZeroSlotMappingGetterWf (code : ByteArray) (pc : UInt256) : Prop :=
  let p1 := pc + ⟨1⟩
  let p3 := p1 + UInt256.ofNat 2
  let p5 := p3 + UInt256.ofNat 2
  let p6 := p5 + ⟨1⟩
  let p7 := p6 + ⟨1⟩
  let p8 := p7 + ⟨1⟩
  let p9 := p8 + ⟨1⟩
  let p10 := p9 + ⟨1⟩
  let p11 := p10 + ⟨1⟩
  let p13 := p11 + UInt256.ofNat 2
  let p14 := p13 + ⟨1⟩
  let p15 := p14 + ⟨1⟩
  let p16 := p15 + ⟨1⟩
  let p17 := p16 + ⟨1⟩
  decode code pc = some (.JUMPDEST, .none)
  ∧ decode code p1 = some (.Push .PUSH1, some (⟨0⟩, 1))
  ∧ decode code p3 = some (.Push .PUSH1, some (⟨32⟩, 1))
  ∧ decode code p5 = some (.DUP2, .none)
  ∧ decode code p6 = some (.SWAP1, .none)
  ∧ decode code p7 = some (.MSTORE, .none)
  ∧ decode code p8 = some (.SWAP1, .none)
  ∧ decode code p9 = some (.DUP2, .none)
  ∧ decode code p10 = some (.MSTORE, .none)
  ∧ decode code p11 = some (.Push .PUSH1, some (⟨64⟩, 1))
  ∧ decode code p13 = some (.SWAP1, .none)
  ∧ decode code p14 = some (.KECCAK256, .none)
  ∧ decode code p15 = some (.SLOAD, .none)
  ∧ decode code p16 = some (.DUP2, .none)
  ∧ decode code p17 = some (.JUMP, .none)

theorem RD.solcZeroSlotMappingGetter {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {pc key ret : UInt256} {R : List UInt256}
    {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD code ee g s0 pc (key :: ret :: R)
        solcFreePtrMem (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hwf : solcZeroSlotMappingGetterWf code pc)
    (hret : (D_J code 0).contains ret = true)
    (hov : R.length + 5 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ret
      (solcSlotWord σ ee (solcMappingSlot ⟨0⟩ key) :: ret :: R)
      (solcMappingHashMem ⟨0⟩ key) (UInt256.ofNat 3) rdata (cA, σ) k' C' := by
  rcases hwf with
    ⟨hd0, hd1, hd3, hd5, hd6, hd7, hd8, hd9, hd10, hd11, hd13, hd14, hd15,
      hd16, hd17⟩
  have rd1 := h.jumpdest hd0 (by simp only [List.length_cons]; omega)
  have rd3 := rd1.push1 ⟨0⟩ hd1 (by evm_ov)
  have rd5 := rd3.push1 ⟨32⟩ hd3 (by evm_ov)
  have rd6 := rd5.dup2 hd5 (by evm_ov)
  have rd7 := rd6.swap1 hd6 (by evm_ov)
  have rd8 := rd7.mstore 0 (solcMappingBaseSlotMem ⟨0⟩)
    (UInt256.ofNat 3) hd7 mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd9 := rd8.swap1 hd8 (by evm_ov)
  have rd10 := rd9.dup2 hd9 (by evm_ov)
  have rd11 := rd10.mstore 0 (solcMappingHashMem ⟨0⟩ key)
    (UInt256.ofNat 3) hd10 mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd13 := rd11.push1 ⟨64⟩ hd11 (by evm_ov)
  have rd14 := rd13.swap1 hd13 (by evm_ov)
  have hslot := solcMappingKeccakSlot ⟨0⟩ key
  have rd15 := rd14.keccak256 0 (solcMappingSlot ⟨0⟩ key)
    (UInt256.ofNat 3) hd14 mem_cost
    (by simpa [show (⟨0⟩ : UInt256).toNat = 0 from by decide,
      show (⟨64⟩ : UInt256).toNat = 64 from by decide] using hslot)
    (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd16⟩ := rd15.sload hd15 (by evm_ov)
  have rd17 := rd16.dup2 hd16 (by evm_ov)
  exact ⟨_, _, rd17.jump hd17 hret (by evm_ov)⟩

theorem RD.solcNestedMappingGetter {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ}
    {pc baseSlot owner spender ret : UInt256} {R : List UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD code ee g s0 pc (spender :: owner :: ret :: R)
        solcFreePtrMem (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hwf : solcNestedMappingGetterWf code pc baseSlot)
    (hret : (D_J code 0).contains ret = true)
    (hov : R.length + 7 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ret
      (solcSlotWord σ ee (solcMappingSlot (solcMappingSlot baseSlot owner) spender) ::
        ret :: R)
      (solcNestedMappingHashMem baseSlot owner spender)
      (UInt256.ofNat 3) rdata (cA, σ) k' C' := by
  obtain ⟨_, _, hinner⟩ := RD.solcNestedMappingInnerHash h hwf hov
  obtain ⟨_, _, houter⟩ := RD.solcNestedMappingOuterHash hinner hwf hov
  obtain ⟨_, _, hload⟩ := RD.solcNestedMappingLoadAndJump houter hwf hret (by omega)
  exact ⟨_, _, hload⟩

noncomputable def solcScratchReturn2Mem
    (scratch : ByteArray) (first second : UInt256) : ByteArray :=
  (UInt256.toByteArray second).write 0 (solcScratchReturnMem scratch first) 160 32

theorem solcScratchReturn2Mem_size {scratch : ByteArray} (first second : UInt256)
    (hscratch : scratch.size = 96) :
    (solcScratchReturn2Mem scratch first second).size = 192 := by
  unfold solcScratchReturn2Mem
  have hbase : (solcScratchReturnMem scratch first).size = 160 :=
    solcScratchReturnMem_size first hscratch
  exact toByteArray_write32_size_of_ge (solcScratchReturnMem scratch first) second 160 160 192
    hbase (by omega) (by norm_num) (by norm_num)

theorem solcScratchReturn2Mem_read64 {scratch : ByteArray} (first second : UInt256)
    (hscratch : scratch.size = 96)
    (hread64 : scratch.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (solcScratchReturn2Mem scratch first second).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold solcScratchReturn2Mem
  have hbase : (solcScratchReturnMem scratch first).size = 160 :=
    solcScratchReturnMem_size first hscratch
  rw [toByteArray_write_read_below_of_gap second (solcScratchReturnMem scratch first) 160 64]
  exact solcScratchReturnMem_read64 first hscratch hread64
  · rw [hbase]; omega
  · omega
  · rw [hbase]; norm_num

theorem solcScratchReturn2Mem_mload64 {scratch : ByteArray} (first second : UInt256)
    (hscratch : scratch.size = 96)
    (hread64 : scratch.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (if (⟨64⟩ : UInt256).toNat ≥ (solcScratchReturn2Mem scratch first second).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((solcScratchReturn2Mem scratch first second).readWithPadding
          (⟨64⟩ : UInt256).toNat 32)))
      = ⟨128⟩ :=
  mloadFreePtrValue (by rw [solcScratchReturn2Mem_size first second hscratch]; decide)
    (by decide) (solcScratchReturn2Mem_read64 first second hscratch hread64)

theorem solcScratchReturn2Mem_read128_64 {scratch : ByteArray} (first second : UInt256)
    (hscratch : scratch.size = 96) :
    (solcScratchReturn2Mem scratch first second).readWithPadding 128 64 =
      UInt256.toByteArray first ++ UInt256.toByteArray second := by
  unfold solcScratchReturn2Mem
  have hbase : (solcScratchReturnMem scratch first).size = 160 :=
    solcScratchReturnMem_size first hscratch
  rw [show (160 : Nat) = (solcScratchReturnMem scratch first).size by rw [hbase]]
  rw [write_at_end_eq (UInt256.toByteArray second) (solcScratchReturnMem scratch first) 32
    (by decide) (by rw [toByteArray_size])]
  rw [toByteArray_extract_all second]
  rw [readWithPadding_eq_extract' _ 128 64 (by norm_num) (by norm_num) (by
    rw [ByteArray.size_append, hbase, toByteArray_size])]
  rw [extract_append_span _ _ _ _ (by rw [hbase]; omega) (by rw [hbase]; omega)]
  have hleft :
      (solcScratchReturnMem scratch first).extract 128
          (solcScratchReturnMem scratch first).size =
        UInt256.toByteArray first := by
    rw [hbase]
    rw [← readWithPadding_eq_extract _ 128 (by rw [hbase])]
    exact solcScratchReturnMem_read128 first hscratch
  rw [hleft]
  rw [hbase]
  norm_num
  rw [toByteArray_extract_all second]

@[reducible] def solcTwoWordReturnFromMemWf (code : ByteArray) (pc : UInt256) : Prop :=
  let p1 := pc + ⟨1⟩
  let p3 := p1 + UInt256.ofNat 2
  let p4 := p3 + ⟨1⟩
  let p5 := p4 + ⟨1⟩
  let p6 := p5 + ⟨1⟩
  let p7 := p6 + ⟨1⟩
  let p8 := p7 + ⟨1⟩
  let p10 := p8 + UInt256.ofNat 2
  let p11 := p10 + ⟨1⟩
  let p12 := p11 + ⟨1⟩
  let p13 := p12 + ⟨1⟩
  let p14 := p13 + ⟨1⟩
  let p15 := p14 + ⟨1⟩
  let p16 := p15 + ⟨1⟩
  let p17 := p16 + ⟨1⟩
  let p18 := p17 + ⟨1⟩
  let p19 := p18 + ⟨1⟩
  let p20 := p19 + ⟨1⟩
  let p21 := p20 + ⟨1⟩
  let p22 := p21 + ⟨1⟩
  let p23 := p22 + ⟨1⟩
  let p24 := p23 + ⟨1⟩
  decode code pc = some (.JUMPDEST, .none)
  ∧ decode code p1 = some (.Push .PUSH1, some (⟨64⟩, 1))
  ∧ decode code p3 = some (.DUP1, .none)
  ∧ decode code p4 = some (.MLOAD, .none)
  ∧ decode code p5 = some (.SWAP3, .none)
  ∧ decode code p6 = some (.DUP4, .none)
  ∧ decode code p7 = some (.MSTORE, .none)
  ∧ decode code p8 = some (.Push .PUSH1, some (⟨32⟩, 1))
  ∧ decode code p10 = some (.DUP4, .none)
  ∧ decode code p11 = some (.ADD, .none)
  ∧ decode code p12 = some (.SWAP2, .none)
  ∧ decode code p13 = some (.SWAP1, .none)
  ∧ decode code p14 = some (.SWAP2, .none)
  ∧ decode code p15 = some (.MSTORE, .none)
  ∧ decode code p16 = some (.DUP1, .none)
  ∧ decode code p17 = some (.MLOAD, .none)
  ∧ decode code p18 = some (.SWAP2, .none)
  ∧ decode code p19 = some (.DUP3, .none)
  ∧ decode code p20 = some (.SWAP1, .none)
  ∧ decode code p21 = some (.SUB, .none)
  ∧ decode code p22 = some (.ADD, .none)
  ∧ decode code p23 = some (.SWAP1, .none)
  ∧ decode code p24 = some (.RETURN, .none)

theorem RD.solcTwoWordReturnFromMem {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {pc first second ret : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD code ee g s0 pc (second :: first :: ret :: R)
        mem (UInt256.ofNat 3) rdata acc k C)
    (hwf : solcTwoWordReturnFromMemWf code pc)
    (hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 3 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32)))
        = ⟨128⟩)
    (hscratch : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hov : R.length + 6 ≤ 1024) :
    RDret code g s0 acc (UInt256.toByteArray first ++ UInt256.toByteArray second) := by
  rcases hwf with
    ⟨hd0, hd1, hd3, hd4, hd5, hd6, hd7, hd8, hd10, hd11, hd12, hd13, hd14,
      hd15, hd16, hd17, hd18, hd19, hd20, hd21, hd22, hd23, hd24⟩
  exact evm_run h with [
    raw jumpdest hd0 (by evm_ov),
    raw push1 ⟨64⟩ hd1 (by evm_ov),
    raw dup1 hd3 (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) hd4 mem_cost hmload64 (by decide) (by evm_ov),
    raw swap3 hd5 (by evm_ov),
    raw dup4 hd6 (by evm_ov),
    raw mstore 6 (solcScratchReturnMem mem first) (UInt256.ofNat 5) hd7 mem_cost
      (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨32⟩ hd8 (by evm_ov),
    raw dup4 hd10 (by evm_ov),
    raw add hd11 (by evm_ov),
    raw swap2 hd12 (by evm_ov),
    raw swap1 hd13 (by evm_ov),
    raw swap2 hd14 (by evm_ov),
    raw mstore 3 (solcScratchReturn2Mem mem first second) (UInt256.ofNat 6) hd15 mem_cost
      (by rfl) (by decide) (by evm_ov),
    raw dup1 hd16 (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 6) hd17 mem_cost
      (solcScratchReturn2Mem_mload64 first second hscratch hread64) (by decide) (by evm_ov),
    raw swap2 hd18 (by evm_ov),
    raw dup3 hd19 (by evm_ov),
    raw swap1 hd20 (by evm_ov),
    raw sub hd21 (by evm_ov),
    raw add hd22 (by evm_ov),
    raw swap1 hd23 (by evm_ov),
    raw ret 0 (UInt256.toByteArray first ++ UInt256.toByteArray second) hd24 mem_cost
      (by
        rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide]
        rw [show (UInt256.sub (⟨128⟩ : UInt256) ⟨128⟩ + ⟨64⟩).toNat = 64
          from by decide]
        exact solcScratchReturn2Mem_read128_64 first second hscratch)
      (by evm_ov)]

theorem uint256PairReturnEncoding (first second : UInt256) :
    encodeReturnValues? [uint256, uint256]
      [.int (Int.ofNat first.toNat), .int (Int.ofNat second.toNat)] =
        some (UInt256.toByteArray first ++ UInt256.toByteArray second) := by
  have hencFirst :
      encodeABIValue? uint256 (.int (Int.ofNat first.toNat)) =
        some (EVM.Word.toBytesBE first) := by
    have hword : EVM.word first.toNat = first := by
      show UInt256.ofNat first.toNat = first
      exact u256_ofNat_toNat first
    have hlt : first.toNat < EVM.twoPow 256 := by
      change first.val.val < EVM.twoPow 256
      exact first.val.isLt
    simp [uint256, uint256Int, encodeABIValue?, encodeABIWord?, hword, hlt]
  have hencSecond :
      encodeABIValue? uint256 (.int (Int.ofNat second.toNat)) =
        some (EVM.Word.toBytesBE second) := by
    have hword : EVM.word second.toNat = second := by
      show UInt256.ofNat second.toNat = second
      exact u256_ofNat_toNat second
    have hlt : second.toNat < EVM.twoPow 256 := by
      change second.val.val < EVM.twoPow 256
      exact second.val.isLt
    simp [uint256, uint256Int, encodeABIValue?, encodeABIWord?, hword, hlt]
  rw [show UInt256.toByteArray first = (EVM.Word.toBytesBE first).toByteArray by
    exact (word_toBytesBE_toByteArray_eq_toByteArray first).symm]
  rw [show UInt256.toByteArray second = (EVM.Word.toBytesBE second).toByteArray by
    exact (word_toBytesBE_toByteArray_eq_toByteArray second).symm]
  unfold encodeReturnValues? encodeABIValues?
  rw [show abiTupleHeadSize? [uint256, uint256] = some 64 by native_decide]
  simp only [bind, Option.bind]
  unfold encodeABIValuesFrom?
  rw [hencFirst]
  simp only [bind, Option.bind]
  rw [show isDynamicABIType uint256 = false by native_decide]
  unfold encodeABIValuesFrom?
  rw [hencSecond]
  simp only [bind, Option.bind]
  rw [show isDynamicABIType uint256 = false by native_decide]
  unfold encodeABIValuesFrom?
  simp only [Bool.false_eq_true, if_false, List.nil_append, List.append_nil]
  apply congrArg some
  apply ByteArray.ext
  simp [ByteArray.data_append]

-- LIBRARY CANDIDATE: signed-division stepping wrapper analogous to Reasoning.Reach.RD.div.
theorem sdiv_xstep {s : State} {code : ByteArray} {pcv a b : UInt256} {t : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = pcv)
    (hdec : decode code pcv = some (.SDIV, .none))
    (hstk : s.machineState.stack = a :: b :: t) (hov : t.length + 1 ≤ 1024) :
    Xstep (D_J code 0) s
      = (if s.machineState.gasAvailable.toNat < 5 then .error .OutOfGass
         else .ok (stMul s (UInt256.sdiv a b) t, .none)) := by
  have hd : decode s.executionEnv.code s.machineState.pc = some (.SDIV, .none) := by
    rw [hcode, hpc]
    exact hdec
  rw [← hcode, step_sdiv s hd, hstk]
  have hov' : ¬ ((a :: b :: t).length - 2 + 1 > 1024) := by
    simp only [List.length_cons]
    omega
  simp only [if_neg hov', GasConstants.Glow, stMul]

-- LIBRARY CANDIDATE: signed-division RD step analogous to Reasoning.Reach.RD.div.
theorem RD.sdiv {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a b : UInt256} {t : List UInt256}
    (h : RD code ee g s0 pc (a :: b :: t) mem aw rdata acc k C)
    (hdec : decode code pc = some (.SDIV, .none)) (hov : t.length + 1 ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩) (UInt256.sdiv a b :: t) mem aw rdata acc (k + 1)
      (C + 5) := by
  unfold RD at h ⊢
  rcases h with hoog | ⟨s, hX, hcode, hpc, hstk, hgas, hk, hC, hmem, haw, hrdata, hacc, hee, hworld⟩
  · exact Or.inl hoog
  · have st := sdiv_xstep hcode hpc hdec hstk hov
    by_cases gg : g.toNat < C + 5
    · exact Or.inl (hX.trans (stepOOG hgas st hk hC (by omega)))
    · refine Or.inr ⟨stMul s (UInt256.sdiv a b) t,
        hX.trans (stepContinue hgas st hk (Nat.not_lt.mp gg)), ?_, ?_, ?_, ?_,
        by omega, by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [stMul]
        exact hcode
      · simp only [stMul]
        rw [hpc]
      · rfl
      · simp only [stMul]
        rw [hgas, Sat256.subNat_sub_add_of_sub_sub]
      · simp only [stMul]
        exact hmem
      · simp only [stMul]
        exact haw
      · simp only [stMul]
        exact hrdata
      · simp only [stMul]
        exact hacc
      · exact hee
      · exact hworld

theorem u256_eq_ne_zero_to_eq {a b : UInt256}
    (h : UInt256.eq a b ≠ ⟨0⟩) : a = b := by
  by_cases hab : a = b
  · exact hab
  · have hzero : UInt256.eq a b = ⟨0⟩ := u256_eq_of_ne hab
    exact False.elim (h hzero)

-- LIBRARY CANDIDATE: solc signed checked-multiply helper for optimized Vat bytecode.
theorem RD.vatSignedMulOk {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {x y ret : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {activeWords : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD vatBytecode ee g s0 ⟨6706⟩ (y :: x :: ret :: R) mem
      activeWords rdata acc k C)
    (hmax : UInt256.slt x ⟨0⟩ = ⟨0⟩)
    (hmul : y = ⟨0⟩ ∨ UInt256.eq (UInt256.sdiv (UInt256.mul y x) y) x ≠ ⟨0⟩)
    (hret : (D_J vatBytecode 0).contains ret = true)
    (hov : R.length + 9 ≤ 1024) :
    ∃ k' C', RD vatBytecode ee g s0 ret ((UInt256.mul y x) :: R) mem
      activeWords rdata acc k' C' := by
  let prod := UInt256.mul y x
  have rd6707 := h.jumpdest (by native_decide) (by evm_ov)
  have rd6708 := rd6707.dup2 (by native_decide) (by evm_ov)
  have rd6709 := rd6708.dup2 (by native_decide) (by evm_ov)
  have rd6710 := rd6709.mul (by native_decide) (by evm_ov)
  have rd6712 := rd6710.push1 ⟨0⟩ (by native_decide) (by evm_ov)
  have rd6713 := rd6712.dup4 (by native_decide) (by evm_ov)
  have rd6714 := rd6713.slt (by native_decide) (by evm_ov)
  have rd6715pre := rd6714.iszero (by native_decide) (by evm_ov)
  have rd6718pre := rd6715pre.push2 ⟨6723⟩ (by native_decide) (by evm_ov)
  have rd6723 := by
    rw [hmax, show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rd6718pre
    simpa [prod] using rd6718pre.jumpiT (by native_decide) one_ne_zero_uint
      (by jump_dest) (by evm_ov)
  have rd6724 := rd6723.jumpdest (by native_decide) (by evm_ov)
  have rd6725 := rd6724.dup2 (by native_decide) (by evm_ov)
  have rd6726 := rd6725.iszero (by native_decide) (by evm_ov)
  have rd6727 := rd6726.dup1 (by native_decide) (by evm_ov)
  have rd6730 := rd6727.push2 ⟨6697⟩ (by native_decide) (by evm_ov)
  by_cases hyzero : y = ⟨0⟩
  · have rd6697 := by
      rw [hyzero, show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rd6730
      simpa [prod] using rd6730.jumpiT (by native_decide) one_ne_zero_uint
        (by jump_dest) (by evm_ov)
    have rd6698 := rd6697.jumpdest (by native_decide) (by evm_ov)
    have rd6701 := rd6698.push2 ⟨6615⟩ (by native_decide) (by evm_ov)
    have rd6615 := rd6701.jumpiT (by native_decide) one_ne_zero_uint (by jump_dest)
      (by evm_ov)
    have rd6616 := rd6615.jumpdest (by native_decide) (by evm_ov)
    have rd6617 := rd6616.swap3 (by native_decide) (by evm_ov)
    have rd6618 := rd6617.swap2 (by native_decide) (by evm_ov)
    have rd6619 := rd6618.pop (by native_decide) (by evm_ov)
    have rd6620 := rd6619.pop (by native_decide) (by evm_ov)
    exact ⟨_, _, by
      simpa [prod, hyzero] using rd6620.jump (by native_decide) hret (by evm_ov)⟩
  · have rd6731 := by
      have hcond : UInt256.isZero y = ⟨0⟩ := isZero_eq_zero_of_ne hyzero
      rw [hcond] at rd6730
      simpa [prod] using rd6730.jumpiNT (by native_decide)
        (by decide : (⟨0⟩ : UInt256) = ⟨0⟩) (by evm_ov)
    have rd6732 := rd6731.pop (by native_decide) (by evm_ov)
    have rd6733 := rd6732.dup3 (by native_decide) (by evm_ov)
    have rd6734 := rd6733.dup3 (by native_decide) (by evm_ov)
    have rd6735 := rd6734.dup3 (by native_decide) (by evm_ov)
    have rd6736 := rd6735.dup2 (by native_decide)
      (by simp only [List.length_cons] at hov ⊢; omega)
    have rd6739 := rd6736.push2 ⟨6741⟩ (by native_decide)
      (by simp only [List.length_cons] at hov ⊢; omega)
    have rd6741 := by
      simpa [prod] using rd6739.jumpiT (by native_decide) hyzero (by jump_dest)
        (by evm_ov)
    have rd6742 := rd6741.jumpdest (by native_decide) (by evm_ov)
    have rd6743pre := Benchmarks.Dss.Vat.RD.sdiv rd6742 (by native_decide) (by evm_ov)
    have rd6744 := rd6743pre.eq (by native_decide) (by evm_ov)
    have rd6747 := rd6744.push2 ⟨6615⟩ (by native_decide) (by evm_ov)
    have heq : UInt256.eq (UInt256.sdiv prod y) x ≠ ⟨0⟩ := by
      simpa [prod] using hmul.resolve_left hyzero
    have rd6615 := rd6747.jumpiT (by native_decide) heq (by jump_dest) (by evm_ov)
    have rd6616 := rd6615.jumpdest (by native_decide) (by evm_ov)
    have rd6617 := rd6616.swap3 (by native_decide) (by evm_ov)
    have rd6618 := rd6617.swap2 (by native_decide) (by evm_ov)
    have rd6619 := rd6618.pop (by native_decide) (by evm_ov)
    have rd6620 := rd6619.pop (by native_decide) (by evm_ov)
    exact ⟨_, _, by simpa [prod] using rd6620.jump (by native_decide) hret (by evm_ov)⟩

theorem RD.vatSignedMulRevert {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {x y ret : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {activeWords : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD vatBytecode ee g s0 ⟨6706⟩ (y :: x :: ret :: R) mem
      activeWords rdata acc k C)
    (hfail :
      ¬ UInt256.slt x ⟨0⟩ = ⟨0⟩ ∨
      UInt256.slt x ⟨0⟩ = ⟨0⟩ ∧
        ¬ (y = ⟨0⟩ ∨ UInt256.eq (UInt256.sdiv (UInt256.mul y x) y) x ≠ ⟨0⟩))
    (hov : R.length + 9 ≤ 1024) :
    RDrev vatBytecode g s0 := by
  let prod := UInt256.mul y x
  have rd6707 := h.jumpdest (by native_decide) (by evm_ov)
  have rd6708 := rd6707.dup2 (by native_decide) (by evm_ov)
  have rd6709 := rd6708.dup2 (by native_decide) (by evm_ov)
  have rd6710 := rd6709.mul (by native_decide) (by evm_ov)
  have rd6712 := rd6710.push1 ⟨0⟩ (by native_decide) (by evm_ov)
  have rd6713 := rd6712.dup4 (by native_decide) (by evm_ov)
  have rd6714 := rd6713.slt (by native_decide) (by evm_ov)
  have rd6715pre := rd6714.iszero (by native_decide) (by evm_ov)
  have rd6718pre := rd6715pre.push2 ⟨6723⟩ (by native_decide) (by evm_ov)
  rcases hfail with hmaxFail | ⟨hmax, hmulFail⟩
  · have hsltNe : UInt256.slt x ⟨0⟩ ≠ ⟨0⟩ := by
      intro hslt
      exact hmaxFail hslt
    have rd6719 := by
      have hcond : UInt256.isZero (UInt256.slt x ⟨0⟩) = ⟨0⟩ :=
        isZero_eq_zero_of_ne hsltNe
      rw [hcond] at rd6718pre
      simpa [prod] using rd6718pre.jumpiNT (by native_decide)
        (by decide : (⟨0⟩ : UInt256) = ⟨0⟩) (by evm_ov)
    exact RD.uniswapPush1Dup1Revert0 rd6719
      (by native_decide) (by native_decide) (by native_decide)
      (by simp only [List.length_cons]; omega)
  · have rd6723 := by
      rw [hmax, show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rd6718pre
      simpa [prod] using rd6718pre.jumpiT (by native_decide) one_ne_zero_uint
        (by jump_dest) (by evm_ov)
    have rd6724 := rd6723.jumpdest (by native_decide) (by evm_ov)
    have rd6725 := rd6724.dup2 (by native_decide) (by evm_ov)
    have rd6726 := rd6725.iszero (by native_decide) (by evm_ov)
    have rd6727 := rd6726.dup1 (by native_decide) (by evm_ov)
    have rd6730 := rd6727.push2 ⟨6697⟩ (by native_decide) (by evm_ov)
    have hyNe : y ≠ ⟨0⟩ := by
      intro hy
      exact hmulFail (Or.inl hy)
    have rd6731 := by
      have hcond : UInt256.isZero y = ⟨0⟩ := isZero_eq_zero_of_ne hyNe
      rw [hcond] at rd6730
      simpa [prod] using rd6730.jumpiNT (by native_decide)
        (by decide : (⟨0⟩ : UInt256) = ⟨0⟩) (by evm_ov)
    have rd6732 := rd6731.pop (by native_decide) (by evm_ov)
    have rd6733 := rd6732.dup3 (by native_decide) (by evm_ov)
    have rd6734 := rd6733.dup3 (by native_decide) (by evm_ov)
    have rd6735 := rd6734.dup3 (by native_decide) (by evm_ov)
    have rd6736 := rd6735.dup2 (by native_decide)
      (by simp only [List.length_cons] at hov ⊢; omega)
    have rd6739 := rd6736.push2 ⟨6741⟩ (by native_decide)
      (by simp only [List.length_cons] at hov ⊢; omega)
    have rd6741 := by
      simpa [prod] using rd6739.jumpiT (by native_decide) hyNe (by jump_dest)
        (by evm_ov)
    have rd6742 := rd6741.jumpdest (by native_decide) (by evm_ov)
    have rd6743pre := Benchmarks.Dss.Vat.RD.sdiv rd6742 (by native_decide) (by evm_ov)
    have rd6744 := rd6743pre.eq (by native_decide) (by evm_ov)
    have rd6747 := rd6744.push2 ⟨6615⟩ (by native_decide) (by evm_ov)
    have heq0 : UInt256.eq (UInt256.sdiv prod y) x = ⟨0⟩ := by
      by_contra heqNe
      exact hmulFail (Or.inr (by simpa [prod] using heqNe))
    have rd6748 := by
      simpa [prod] using rd6747.jumpiNT (by native_decide) heq0 (by evm_ov)
    exact RD.uniswapPush1Dup1Revert0 rd6748
      (by native_decide) (by native_decide) (by native_decide)
      (by simp only [List.length_cons]; omega)

-- LIBRARY CANDIDATE: solc signed checked-subtract helper for optimized Vat bytecode.
theorem RD.vatSignedSubOk {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {x y ret : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {activeWords : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD vatBytecode ee g s0 ⟨6795⟩ (y :: x :: ret :: R) mem
      activeWords rdata acc k C)
    (hpos : UInt256.sgt y ⟨0⟩ = ⟨0⟩ ∨ UInt256.gt (UInt256.sub x y) x = ⟨0⟩)
    (hneg : UInt256.slt y ⟨0⟩ = ⟨0⟩ ∨ UInt256.lt (UInt256.sub x y) x = ⟨0⟩)
    (hret : (D_J vatBytecode 0).contains ret = true)
    (hov : R.length + 7 ≤ 1024) :
    ∃ k' C', RD vatBytecode ee g s0 ret ((UInt256.sub x y) :: R) mem
      activeWords rdata acc k' C' := by
  let diff := UInt256.sub x y
  have rd6796 := h.jumpdest (by native_decide) (by evm_ov)
  have rd6797 := rd6796.dup1 (by native_decide) (by evm_ov)
  have rd6798 := rd6797.dup3 (by native_decide) (by evm_ov)
  have rd6799 := rd6798.sub (by native_decide) (by evm_ov)
  have rd6801 := rd6799.push1 ⟨0⟩ (by native_decide) (by evm_ov)
  have rd6802 := rd6801.dup3 (by native_decide) (by evm_ov)
  have rd6803 := rd6802.sgt (by native_decide) (by evm_ov)
  have rd6804 := rd6803.iszero (by native_decide) (by evm_ov)
  have rd6805 := rd6804.dup1 (by native_decide) (by evm_ov)
  have rd6808 := rd6805.push2 ⟨6814⟩ (by native_decide) (by evm_ov)
  have hrd6814 :
      ∃ k' C', RD vatBytecode ee g s0 ⟨6814⟩ (⟨1⟩ :: diff :: y :: x :: ret :: R)
        mem activeWords rdata acc k' C' := by
    by_cases hypos0 : UInt256.sgt y ⟨0⟩ = ⟨0⟩
    · rw [hypos0, show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rd6808
      exact ⟨_, _, by
        simpa [diff] using rd6808.jumpiT (by native_decide) one_ne_zero_uint
          (by jump_dest) (by evm_ov)⟩
    · have rd6809 := by
        have hcond : UInt256.isZero (UInt256.sgt y ⟨0⟩) = ⟨0⟩ :=
          isZero_eq_zero_of_ne hypos0
        rw [hcond] at rd6808
        simpa [diff] using rd6808.jumpiNT (by native_decide)
          (by decide : (⟨0⟩ : UInt256) = ⟨0⟩) (by evm_ov)
      have rd6810 := rd6809.pop (by native_decide) (by evm_ov)
      have rd6811 := rd6810.dup3 (by native_decide) (by evm_ov)
      have rd6812 := rd6811.dup2 (by native_decide) (by evm_ov)
      have rd6813 := rd6812.gt (by native_decide) (by evm_ov)
      have rd6814pre := rd6813.iszero (by native_decide) (by evm_ov)
      have hgt0 : UInt256.gt diff x = ⟨0⟩ := by
        simpa [diff] using hpos.resolve_left hypos0
      rw [hgt0, show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rd6814pre
      exact ⟨_, _, rd6814pre⟩
  obtain ⟨_, _, rd6814⟩ := hrd6814
  have rd6815 := rd6814.jumpdest (by native_decide) (by evm_ov)
  have rd6818 := rd6815.push2 ⟨6823⟩ (by native_decide) (by evm_ov)
  have rd6823 := rd6818.jumpiT (by native_decide) one_ne_zero_uint (by jump_dest)
    (by evm_ov)
  have rd6824 := rd6823.jumpdest (by native_decide) (by evm_ov)
  have rd6826 := rd6824.push1 ⟨0⟩ (by native_decide) (by evm_ov)
  have rd6827 := rd6826.dup3 (by native_decide) (by evm_ov)
  have rd6828 := rd6827.slt (by native_decide) (by evm_ov)
  have rd6829 := rd6828.iszero (by native_decide) (by evm_ov)
  have rd6830 := rd6829.dup1 (by native_decide) (by evm_ov)
  have rd6833 := rd6830.push2 ⟨6697⟩ (by native_decide) (by evm_ov)
  by_cases hyneg0 : UInt256.slt y ⟨0⟩ = ⟨0⟩
  · have rd6697 := by
      rw [hyneg0, show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rd6833
      simpa [diff] using rd6833.jumpiT (by native_decide) one_ne_zero_uint
        (by jump_dest) (by evm_ov)
    have rd6698 := rd6697.jumpdest (by native_decide) (by evm_ov)
    have rd6701 := rd6698.push2 ⟨6615⟩ (by native_decide) (by evm_ov)
    have rd6615 := by
      simpa [diff] using rd6701.jumpiT (by native_decide) one_ne_zero_uint
        (by jump_dest) (by evm_ov)
    have rd6616 := rd6615.jumpdest (by native_decide) (by evm_ov)
    have rd6617 := rd6616.swap3 (by native_decide) (by evm_ov)
    have rd6618 := rd6617.swap2 (by native_decide) (by evm_ov)
    have rd6619 := rd6618.pop (by native_decide) (by evm_ov)
    have rd6620 := rd6619.pop (by native_decide) (by evm_ov)
    exact ⟨_, _, by simpa [diff] using rd6620.jump (by native_decide) hret (by evm_ov)⟩
  · have rd6834 := by
      have hcond : UInt256.isZero (UInt256.slt y ⟨0⟩) = ⟨0⟩ :=
        isZero_eq_zero_of_ne hyneg0
      rw [hcond] at rd6833
      simpa [diff] using rd6833.jumpiNT (by native_decide)
        (by decide : (⟨0⟩ : UInt256) = ⟨0⟩) (by evm_ov)
    have rd6835 := rd6834.pop (by native_decide) (by evm_ov)
    have rd6836 := rd6835.dup3 (by native_decide) (by evm_ov)
    have rd6837 := rd6836.dup2 (by native_decide) (by evm_ov)
    have rd6838 := rd6837.lt (by native_decide) (by evm_ov)
    have rd6839 := rd6838.iszero (by native_decide) (by evm_ov)
    have rd6842 := rd6839.push2 ⟨6615⟩ (by native_decide) (by evm_ov)
    have hlt0 : UInt256.lt diff x = ⟨0⟩ := by
      simpa [diff] using hneg.resolve_left hyneg0
    have rd6615 := by
      rw [hlt0, show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rd6842
      simpa [diff] using rd6842.jumpiT (by native_decide) one_ne_zero_uint
        (by jump_dest) (by evm_ov)
    have rd6616 := rd6615.jumpdest (by native_decide) (by evm_ov)
    have rd6617 := rd6616.swap3 (by native_decide) (by evm_ov)
    have rd6618 := rd6617.swap2 (by native_decide) (by evm_ov)
    have rd6619 := rd6618.pop (by native_decide) (by evm_ov)
    have rd6620 := rd6619.pop (by native_decide) (by evm_ov)
    exact ⟨_, _, by simpa [diff] using rd6620.jump (by native_decide) hret (by evm_ov)⟩

theorem RD.vatSignedSubRevert {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {x y ret : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {activeWords : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD vatBytecode ee g s0 ⟨6795⟩ (y :: x :: ret :: R) mem
      activeWords rdata acc k C)
    (hfail :
      ¬ (UInt256.sgt y ⟨0⟩ = ⟨0⟩ ∨ UInt256.gt (UInt256.sub x y) x = ⟨0⟩) ∨
      (UInt256.sgt y ⟨0⟩ = ⟨0⟩ ∨ UInt256.gt (UInt256.sub x y) x = ⟨0⟩) ∧
        ¬ (UInt256.slt y ⟨0⟩ = ⟨0⟩ ∨ UInt256.lt (UInt256.sub x y) x = ⟨0⟩))
    (hov : R.length + 7 ≤ 1024) :
    RDrev vatBytecode g s0 := by
  let diff := UInt256.sub x y
  have rd6796 := h.jumpdest (by native_decide) (by evm_ov)
  have rd6797 := rd6796.dup1 (by native_decide) (by evm_ov)
  have rd6798 := rd6797.dup3 (by native_decide) (by evm_ov)
  have rd6799 := rd6798.sub (by native_decide) (by evm_ov)
  have rd6801 := rd6799.push1 ⟨0⟩ (by native_decide) (by evm_ov)
  have rd6802 := rd6801.dup3 (by native_decide) (by evm_ov)
  have rd6803 := rd6802.sgt (by native_decide) (by evm_ov)
  have rd6804 := rd6803.iszero (by native_decide) (by evm_ov)
  have rd6805 := rd6804.dup1 (by native_decide) (by evm_ov)
  have rd6808 := rd6805.push2 ⟨6814⟩ (by native_decide) (by evm_ov)
  rcases hfail with hposFail | ⟨hpos, hnegFail⟩
  · have hyposNe : UInt256.sgt y ⟨0⟩ ≠ ⟨0⟩ := by
      intro hypos0
      exact hposFail (Or.inl hypos0)
    have rd6809 := by
      have hcond : UInt256.isZero (UInt256.sgt y ⟨0⟩) = ⟨0⟩ :=
        isZero_eq_zero_of_ne hyposNe
      rw [hcond] at rd6808
      simpa [diff] using rd6808.jumpiNT (by native_decide)
        (by decide : (⟨0⟩ : UInt256) = ⟨0⟩) (by evm_ov)
    have rd6810 := rd6809.pop (by native_decide) (by evm_ov)
    have rd6811 := rd6810.dup3 (by native_decide) (by evm_ov)
    have rd6812 := rd6811.dup2 (by native_decide) (by evm_ov)
    have rd6813 := rd6812.gt (by native_decide) (by evm_ov)
    have rd6814 := rd6813.iszero (by native_decide) (by evm_ov)
    have hgtNe : UInt256.gt diff x ≠ ⟨0⟩ := by
      intro hgt0
      exact hposFail (Or.inr (by simpa [diff] using hgt0))
    have rd6814zero : UInt256.isZero (UInt256.gt diff x) = ⟨0⟩ :=
      isZero_eq_zero_of_ne hgtNe
    rw [rd6814zero] at rd6814
    have rd6815 := rd6814.jumpdest (by native_decide) (by evm_ov)
    have rd6818 := rd6815.push2 ⟨6823⟩ (by native_decide) (by evm_ov)
    have rd6819 := rd6818.jumpiNT (by native_decide)
      (by decide : (⟨0⟩ : UInt256) = ⟨0⟩) (by evm_ov)
    exact RD.uniswapPush1Dup1Revert0 rd6819
      (by native_decide) (by native_decide) (by native_decide)
      (by simp only [List.length_cons]; omega)
  · have hrd6814 :
        ∃ k' C', RD vatBytecode ee g s0 ⟨6814⟩ (⟨1⟩ :: diff :: y :: x :: ret :: R)
          mem activeWords rdata acc k' C' := by
      by_cases hypos0 : UInt256.sgt y ⟨0⟩ = ⟨0⟩
      · rw [hypos0, show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rd6808
        exact ⟨_, _, by
          simpa [diff] using rd6808.jumpiT (by native_decide) one_ne_zero_uint
            (by jump_dest) (by evm_ov)⟩
      · have rd6809 := by
          have hcond : UInt256.isZero (UInt256.sgt y ⟨0⟩) = ⟨0⟩ :=
            isZero_eq_zero_of_ne hypos0
          rw [hcond] at rd6808
          simpa [diff] using rd6808.jumpiNT (by native_decide)
            (by decide : (⟨0⟩ : UInt256) = ⟨0⟩) (by evm_ov)
        have rd6810 := rd6809.pop (by native_decide) (by evm_ov)
        have rd6811 := rd6810.dup3 (by native_decide) (by evm_ov)
        have rd6812 := rd6811.dup2 (by native_decide) (by evm_ov)
        have rd6813 := rd6812.gt (by native_decide) (by evm_ov)
        have rd6814pre := rd6813.iszero (by native_decide) (by evm_ov)
        have hgt0 : UInt256.gt diff x = ⟨0⟩ := by
          simpa [diff] using hpos.resolve_left hypos0
        rw [hgt0, show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rd6814pre
        exact ⟨_, _, rd6814pre⟩
    obtain ⟨_, _, rd6814⟩ := hrd6814
    have rd6815 := rd6814.jumpdest (by native_decide) (by evm_ov)
    have rd6818 := rd6815.push2 ⟨6823⟩ (by native_decide) (by evm_ov)
    have rd6823 := rd6818.jumpiT (by native_decide) one_ne_zero_uint (by jump_dest)
      (by evm_ov)
    have rd6824 := rd6823.jumpdest (by native_decide) (by evm_ov)
    have rd6826 := rd6824.push1 ⟨0⟩ (by native_decide) (by evm_ov)
    have rd6827 := rd6826.dup3 (by native_decide) (by evm_ov)
    have rd6828 := rd6827.slt (by native_decide) (by evm_ov)
    have rd6829 := rd6828.iszero (by native_decide) (by evm_ov)
    have rd6830 := rd6829.dup1 (by native_decide) (by evm_ov)
    have rd6833 := rd6830.push2 ⟨6697⟩ (by native_decide) (by evm_ov)
    have hynegNe : UInt256.slt y ⟨0⟩ ≠ ⟨0⟩ := by
      intro hyneg0
      exact hnegFail (Or.inl hyneg0)
    have rd6834 := by
      have hcond : UInt256.isZero (UInt256.slt y ⟨0⟩) = ⟨0⟩ :=
        isZero_eq_zero_of_ne hynegNe
      rw [hcond] at rd6833
      simpa [diff] using rd6833.jumpiNT (by native_decide)
        (by decide : (⟨0⟩ : UInt256) = ⟨0⟩) (by evm_ov)
    have rd6835 := rd6834.pop (by native_decide) (by evm_ov)
    have rd6836 := rd6835.dup3 (by native_decide) (by evm_ov)
    have rd6837 := rd6836.dup2 (by native_decide) (by evm_ov)
    have rd6838 := rd6837.lt (by native_decide) (by evm_ov)
    have rd6839 := rd6838.iszero (by native_decide) (by evm_ov)
    have rd6842 := rd6839.push2 ⟨6615⟩ (by native_decide) (by evm_ov)
    have hltNe : UInt256.lt diff x ≠ ⟨0⟩ := by
      intro hlt0
      exact hnegFail (Or.inr (by simpa [diff] using hlt0))
    have hltIsZero : UInt256.isZero (UInt256.lt diff x) = ⟨0⟩ :=
      isZero_eq_zero_of_ne hltNe
    rw [hltIsZero] at rd6842
    have rd6843 := rd6842.jumpiNT (by native_decide)
      (by decide : (⟨0⟩ : UInt256) = ⟨0⟩) (by evm_ov)
    exact RD.uniswapPush1Dup1Revert0 rd6843
      (by native_decide) (by native_decide) (by native_decide)
      (by simp only [List.length_cons]; omega)

end Benchmarks.Dss.Vat
