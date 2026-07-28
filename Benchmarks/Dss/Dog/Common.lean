import Benchmarks.Dss.Dog.Bytecode
import Reasoning.ABI
import Reasoning.Theory
import Reasoning.Stepping
import Reasoning.Reach
import Reasoning.Solc
import Reasoning.Memory
import Reasoning.Storage
import Reasoning.Dispatch
import Reasoning.Initcode
import Reasoning.SolmBody
import Mathlib.Tactic.IntervalCases

/-!
# MakerDAO/Sky DSS Dog shared proof foundation

Contract-wide selector notation and constants for the optimized Dog runtime.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Dss.Dog.Immutables

set_option maxRecDepth 2000000

namespace Benchmarks.Dss.Dog

/-- The 4-byte selector word computed by `CALLDATALOAD(0); SHR 224`. -/
abbrev dogSelWord (I : ExecutionEnv) : UInt256 :=
  UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩

/-- The 4-byte selector of `I`'s calldata equals `sel`. -/
abbrev selIs (I : ExecutionEnv) (sel : ByteArray) : Prop :=
  (sel == I.calldata.extract 0 4) = true

/-- Function selectors in `(contract v).transitions` order. -/
def dogSelBytes : ℕ → ByteArray
  | 0 => ⟨#[0xed, 0xa6, 0xe1, 0x21]⟩ -- Dirt()
  | 1 => ⟨#[0xaf, 0x7c, 0xfe, 0xb1]⟩ -- Hole()
  | 2 => ⟨#[0xed, 0x99, 0x89, 0x08]⟩ -- bark(bytes32,address,address)
  | 3 => ⟨#[0x69, 0x24, 0x50, 0x09]⟩ -- cage()
  | 4 => ⟨#[0xd7, 0x92, 0x65, 0x38]⟩ -- chop(bytes32)
  | 5 => ⟨#[0x9c, 0x52, 0xa7, 0xf1]⟩ -- deny(address)
  | 6 => ⟨#[0xc8, 0x71, 0x93, 0xf4]⟩ -- digs(bytes32,uint256)
  | 7 => ⟨#[0x1a, 0x0b, 0x28, 0x7e]⟩ -- file(bytes32,bytes32,uint256)
  | 8 => ⟨#[0x29, 0xae, 0x81, 0x14]⟩ -- file(bytes32,uint256)
  | 9 => ⟨#[0xd4, 0xe8, 0xbe, 0x83]⟩ -- file(bytes32,address)
  | 10 => ⟨#[0xeb, 0xec, 0xb3, 0x9d]⟩ -- file(bytes32,bytes32,address)
  | 11 => ⟨#[0xd9, 0x63, 0x8d, 0x36]⟩ -- ilks(bytes32)
  | 12 => ⟨#[0x95, 0x7a, 0xa5, 0x8c]⟩ -- live()
  | 13 => ⟨#[0x65, 0xfa, 0xe3, 0x5e]⟩ -- rely(address)
  | 14 => ⟨#[0x36, 0x56, 0x9e, 0x77]⟩ -- vat()
  | 15 => ⟨#[0x62, 0x6c, 0xb3, 0xc5]⟩ -- vow()
  | _ => ⟨#[0xbf, 0x35, 0x3d, 0xbb]⟩ -- wards(address)

def dogSelectorWord : ℕ → UInt256
  | 0 => ⟨0xeda6e121⟩ -- Dirt()
  | 1 => ⟨0xaf7cfeb1⟩ -- Hole()
  | 2 => ⟨0xed998908⟩ -- bark(bytes32,address,address)
  | 3 => ⟨0x69245009⟩ -- cage()
  | 4 => ⟨0xd7926538⟩ -- chop(bytes32)
  | 5 => ⟨0x9c52a7f1⟩ -- deny(address)
  | 6 => ⟨0xc87193f4⟩ -- digs(bytes32,uint256)
  | 7 => ⟨0x1a0b287e⟩ -- file(bytes32,bytes32,uint256)
  | 8 => ⟨0x29ae8114⟩ -- file(bytes32,uint256)
  | 9 => ⟨0xd4e8be83⟩ -- file(bytes32,address)
  | 10 => ⟨0xebecb39d⟩ -- file(bytes32,bytes32,address)
  | 11 => ⟨0xd9638d36⟩ -- ilks(bytes32)
  | 12 => ⟨0x957aa58c⟩ -- live()
  | 13 => ⟨0x65fae35e⟩ -- rely(address)
  | 14 => ⟨0x36569e77⟩ -- vat()
  | 15 => ⟨0x626cb3c5⟩ -- vow()
  | _ => ⟨0xbf353dbb⟩ -- wards(address)

theorem dogEvmSelectorEq (I : ExecutionEnv) (hsz : 4 ≤ I.calldata.size)
    (i : ℕ) (hi : i < 17) :
    UInt256.eq (dogSelectorWord i) (solcSelectorWord I) =
      if (dogSelBytes i == I.calldata.extract 0 4) then ⟨1⟩ else ⟨0⟩ := by
  interval_cases i <;>
    simpa [dogSelectorWord, dogSelBytes, solcSelectorWord] using
      (evmSelectorDecode (cd := I.calldata) hsz _ _ _ _ _ (by native_decide))

theorem dogSelectorEqZero (I : ExecutionEnv) (hsz : 4 ≤ I.calldata.size)
    (hnm : ∀ i, i < 17 → (dogSelBytes i == I.calldata.extract 0 4) = false)
    (i : ℕ) (hi : i < 17) :
    UInt256.eq (dogSelectorWord i) (solcSelectorWord I) = ⟨0⟩ := by
  rw [dogEvmSelectorEq I hsz i hi, hnm i hi]
  rfl

theorem dogDecodeCalldataWithMode_legacyBytes32_ok {cd : ByteArray} {x : Ident}
    (hsz36 : 36 ≤ cd.size) :
    decodeCalldataWithMode DecodeMode.legacySolc05 [x] [abiBytes32] cd =
      some ((∅ : Store).insert x (.fixedBytes abiBytes32Width ((cd.toList.drop 4).take 32))) := by
  unfold decodeCalldataWithMode decodeCalldata
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have hnot4 : ¬ cd.toList.length < 4 := by
    rw [htlen]
    omega
  rw [if_neg hnot4]
  have hnotDyn : ¬ ([abiBytes32].any isDynamicABIType = true ∧ 2 ^ 255 ≤ cd.toList.length) := by
    simp [abiBytes32, isDynamicABIType]
  rw [if_neg hnotDyn]
  have hread : readBytes? (cd.toList.drop 4) 0 32 =
      some ((cd.toList.drop 4).take 32) := by
    unfold readBytes?
    have hlen : (((cd.toList.drop 4).drop 0).take 32).length = 32 := by
      rw [List.drop_zero, List.length_take, List.length_drop, htlen]
      omega
    rw [if_pos hlen, List.drop_zero]
  have hblen : ((cd.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  have hpad : zeroPadding? ((cd.toList.drop 4).take 32) 32 0 = some () := by
    unfold zeroPadding? readBytes?
    simp
  have htake : List.take 32 ((cd.toList.drop 4).take 32) = (cd.toList.drop 4).take 32 :=
    List.take_of_length_le (by rw [hblen])
  have hnotArgShort : ¬ cd.toList.length - 4 < 32 := by
    rw [htlen]
    omega
  simp [decodeCalldata.decodeArgs, decodeCalldata.insertValues, abiBytes32,
    ABI.decodeABIValues?, ABI.decodeABIValue?, isDynamicABIType, staticABIEncodedSize?,
    abiTupleHeadSize?, hread, abiBytes32Width, htake, hnotArgShort]

theorem dogDecodeCalldataWithMode_legacyBytes32_none_short {cd : ByteArray} {x : Ident}
    (hsz4 : 4 ≤ cd.size) (hshort : cd.size < 36) :
    decodeCalldataWithMode DecodeMode.legacySolc05 [x] [abiBytes32] cd = none := by
  unfold decodeCalldataWithMode decodeCalldata
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have hnot4 : ¬ cd.toList.length < 4 := by
    rw [htlen]
    omega
  rw [if_neg hnot4]
  have hnotDyn : ¬ ([abiBytes32].any isDynamicABIType = true ∧ 2 ^ 255 ≤ cd.toList.length) := by
    simp [abiBytes32, isDynamicABIType]
  rw [if_neg hnotDyn]
  have hread : readBytes? (cd.toList.drop 4) 0 32 = none := by
    unfold readBytes?
    have hlen : ¬ (((cd.toList.drop 4).drop 0).take 32).length = 32 := by
      rw [List.drop_zero, List.length_take, List.length_drop, htlen]
      omega
    rw [if_neg hlen]
  simp [decodeCalldata.decodeArgs, abiBytes32, ABI.decodeABIValues?, ABI.decodeABIValue?,
    isDynamicABIType, staticABIEncodedSize?, abiTupleHeadSize?, hread]

theorem dogDecodeABIValues_bytes32_uint256_legacy_ok {bytes : List UInt8}
    (hlen0 : (bytes.take 32).length = 32)
    (hlen32 : ((bytes.drop 32).take 32).length = 32) :
    decodeABIValues? [abiBytes32, abiUInt256] bytes 0 0 64 64 DecodeMode.legacySolc05 =
      some ([.fixedBytes abiBytes32Width (bytes.take 32),
        .int (Int.ofNat (ABI.bytesToWord ((bytes.drop 32).take 32)).toNat)], 64) := by
  simp [decodeABIValues?, abiBytes32, abiBytes32Width, abiUInt256, isDynamicABIType,
    staticABIEncodedSize?, decodeABIValue?, readBytes?, hlen0]
  simp [readWord?, readBytes?, decodeABIWord?, hlen32]
  rw [Int.emod_eq_of_lt]
  · simp [UInt256.toNat]
  · exact Int.natCast_nonneg _
  · exact_mod_cast (ABI.bytesToWord ((bytes.drop 32).take 32)).val.isLt

theorem dogDecodeABIValues_bytes32_uint256_legacy_none_short {bytes : List UInt8}
    (hshort : bytes.length < 64) :
    decodeABIValues? [abiBytes32, abiUInt256] bytes 0 0 64 64 DecodeMode.legacySolc05 =
      none := by
  simp only [decodeABIValues?, abiBytes32, abiBytes32Width, abiUInt256, isDynamicABIType,
    Bool.false_eq_true, if_false, staticABIEncodedSize?, bind, Option.bind, Nat.zero_add]
  by_cases h32 : bytes.length < 32
  · have htake0n : ¬ (bytes.take 32).length = 32 := by
      rw [List.length_take]
      omega
    have hnot : ¬ 32 ≤ bytes.length := by omega
    simp [decodeABIValue?, readBytes?, hnot]
  · have htake0 : (bytes.take 32).length = 32 := by
      rw [List.length_take]
      omega
    have htake32n : ¬ ((bytes.drop 32).take 32).length = 32 := by
      rw [List.length_take, List.length_drop]
      omega
    simp [decodeABIValue?, readBytes?, htake0]
    have hnot : ¬ 32 ≤ bytes.length - 32 := by
      rw [List.length_take, List.length_drop] at htake32n
      omega
    simp [readWord?, readBytes?, hnot]

theorem dogDecodeCalldataWithMode_legacyBytes32_uint256_ok {cd : ByteArray}
    {x y : Solm.Ident} (hsz68 : 68 ≤ cd.size) :
    decodeCalldataWithMode DecodeMode.legacySolc05 [x, y] [abiBytes32, abiUInt256] cd =
      some (((∅ : Solm.Store).insert x
        (.fixedBytes abiBytes32Width ((cd.toList.drop 4).take 32))).insert y
        (.int (Int.ofNat (calldataWord cd 36).toNat))) := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have htake4 : ((cd.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  have htake36 : ((cd.toList.drop 36).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  have hword36 : ABI.bytesToWord ((cd.toList.drop 36).take 32) = calldataWord cd 36 :=
    decode_word_at_eq cd 36 (by omega) (by norm_num)
  unfold decodeCalldataWithMode decodeCalldata
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  rw [if_neg (by simp [abiBytes32, abiUInt256, isDynamicABIType])]
  simp only [decodeCalldata.decodeArgs]
  rw [show abiTupleHeadSize? [abiBytes32, abiUInt256] = some 64 by native_decide]
  simp only [bind, Option.bind]
  rw [dogDecodeABIValues_bytes32_uint256_legacy_ok (bytes := cd.toList.drop 4)
    (by simpa using htake4)
    (by simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using htake36)]
  rw [if_neg (by rw [List.length_drop, htlen]; omega :
    ¬ (cd.toList.drop 4).length < 64)]
  simp [decodeCalldata.insertValues]
  rw [hword36]

theorem dogDecodeCalldataWithMode_legacyBytes32_uint256_none_short {cd : ByteArray}
    {x y : Solm.Ident} (hsz4 : 4 ≤ cd.size) (hshort : cd.size < 68) :
    decodeCalldataWithMode DecodeMode.legacySolc05 [x, y] [abiBytes32, abiUInt256] cd =
      none := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  unfold decodeCalldataWithMode decodeCalldata
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  rw [if_neg (by simp [abiBytes32, abiUInt256, isDynamicABIType])]
  simp only [decodeCalldata.decodeArgs]
  rw [show abiTupleHeadSize? [abiBytes32, abiUInt256] = some 64 by native_decide]
  simp only [bind, Option.bind]
  by_cases hbytes : (cd.toList.drop 4).length < 64
  · rw [if_pos hbytes]
  · rw [if_neg hbytes]
    rw [dogDecodeABIValues_bytes32_uint256_legacy_none_short
      (bytes := cd.toList.drop 4) (by
        rw [List.length_drop, htlen]
        omega)]

theorem dogDecodeABIValues_bytes32_address_legacy_ok {bytes : List UInt8}
    (hlen0 : (bytes.take 32).length = 32)
    (hlen32 : ((bytes.drop 32).take 32).length = 32) :
    decodeABIValues? [abiBytes32, abiAddress] bytes 0 0 64 64 DecodeMode.legacySolc05 =
      some ([.fixedBytes abiBytes32Width (bytes.take 32),
        .address (AccountAddress.ofNat
          (ABI.bytesToWord ((bytes.drop 32).take 32)).toNat)], 64) := by
  simp [decodeABIValues?, abiBytes32, abiBytes32Width, abiAddress, isDynamicABIType,
    staticABIEncodedSize?, decodeABIValue?, readBytes?, hlen0]
  simp [readWord?, readBytes?, decodeABIWord?, UInt256.toNat, hlen32]

theorem dogDecodeABIValues_bytes32_address_legacy_none_short {bytes : List UInt8}
    (hshort : bytes.length < 64) :
    decodeABIValues? [abiBytes32, abiAddress] bytes 0 0 64 64 DecodeMode.legacySolc05 =
      none := by
  simp only [decodeABIValues?, abiBytes32, abiBytes32Width, abiAddress, isDynamicABIType,
    Bool.false_eq_true, if_false, staticABIEncodedSize?, bind, Option.bind, Nat.zero_add]
  by_cases h32 : bytes.length < 32
  · have htake0n : ¬ (bytes.take 32).length = 32 := by
      rw [List.length_take]
      omega
    have hnot : ¬ 32 ≤ bytes.length := by omega
    simp [decodeABIValue?, readBytes?, hnot]
  · have htake0 : (bytes.take 32).length = 32 := by
      rw [List.length_take]
      omega
    have htake32n : ¬ ((bytes.drop 32).take 32).length = 32 := by
      rw [List.length_take, List.length_drop]
      omega
    simp [decodeABIValue?, readBytes?, htake0]
    have hnot : ¬ 32 ≤ bytes.length - 32 := by
      rw [List.length_take, List.length_drop] at htake32n
      omega
    simp [readWord?, readBytes?, hnot]

theorem dogDecodeCalldataWithMode_legacyBytes32_address_ok {cd : ByteArray}
    {x y : Solm.Ident} (hsz68 : 68 ≤ cd.size) :
    decodeCalldataWithMode DecodeMode.legacySolc05 [x, y] [abiBytes32, abiAddress] cd =
      some (((∅ : Solm.Store).insert x
        (.fixedBytes abiBytes32Width ((cd.toList.drop 4).take 32))).insert y
        (.address (AccountAddress.ofNat (calldataWord cd 36).toNat))) := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have htake4 : ((cd.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  have htake36 : ((cd.toList.drop 36).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  have hword36 : ABI.bytesToWord ((cd.toList.drop 36).take 32) = calldataWord cd 36 :=
    decode_word_at_eq cd 36 (by omega) (by norm_num)
  unfold decodeCalldataWithMode decodeCalldata
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  rw [if_neg (by simp [abiBytes32, abiAddress, isDynamicABIType])]
  simp only [decodeCalldata.decodeArgs]
  rw [show abiTupleHeadSize? [abiBytes32, abiAddress] = some 64 by native_decide]
  simp only [bind, Option.bind]
  rw [dogDecodeABIValues_bytes32_address_legacy_ok (bytes := cd.toList.drop 4)
    (by simpa using htake4)
    (by simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using htake36)]
  rw [if_neg (by rw [List.length_drop, htlen]; omega :
    ¬ (cd.toList.drop 4).length < 64)]
  simp [decodeCalldata.insertValues]
  rw [hword36]

theorem dogDecodeCalldataWithMode_legacyBytes32_address_none_short {cd : ByteArray}
    {x y : Solm.Ident} (hsz4 : 4 ≤ cd.size) (hshort : cd.size < 68) :
    decodeCalldataWithMode DecodeMode.legacySolc05 [x, y] [abiBytes32, abiAddress] cd =
      none := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  unfold decodeCalldataWithMode decodeCalldata
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  rw [if_neg (by simp [abiBytes32, abiAddress, isDynamicABIType])]
  simp only [decodeCalldata.decodeArgs]
  rw [show abiTupleHeadSize? [abiBytes32, abiAddress] = some 64 by native_decide]
  simp only [bind, Option.bind]
  by_cases hbytes : (cd.toList.drop 4).length < 64
  · rw [if_pos hbytes]
  · rw [if_neg hbytes]
    rw [dogDecodeABIValues_bytes32_address_legacy_none_short
      (bytes := cd.toList.drop 4) (by
        rw [List.length_drop, htlen]
        omega)]

def dogSlotWord (slot : UInt256) (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  solcSlotWord σ I slot

abbrev dogAddressReturnWord (slot : UInt256) (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.land (dogSlotWord slot σ I) solcAddrMask

theorem dogStorageLocLoad_address_offset0 (evm : EVM.State) (slot : UInt256) :
    storageLocLoad evm (addrLoc slot) =
      .address (AccountAddress.ofNat
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)
          solcAddrMask).toNat) := by
  simpa [addrLoc, addressOffset0Loc] using storageLocLoad_address_offset0 evm slot

theorem dogStorageLocLoad_uint256 (evm : EVM.State) (slot : UInt256) :
    storageLocLoad evm (wordLoc slot) =
      .int (Int.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot).toNat) := by
  simpa [wordLoc, uint256Loc] using storageLocLoad_uint256 evm slot

theorem dogAddressGetterBodyReturns (v : DogImmutables) (evm : EVM.State) (locals : Store)
    {ref : StorageRef} {er : EvaledStorageRef} {slot : UInt256}
    (h : evm.executionEnv.weiValue = ⟨0⟩)
    (hbase : locals.get? ref.base = none)
    (her : evalStorageRef (config v) { contract := contract v, locals := locals } evm ref = .ok er)
    (hty : storageTypeAt? (contract v).storage er = some (.elem .address))
    (hloc : (config v).storage.layout er = fun _ => some (addrLoc slot)) :
    ExecTransitionBody (config v) (contract v) evm locals (nonpayable ++ [ .return [(.storage ref)] ])
      (.returned { contract := contract v, locals := locals } evm
        (some [(.address (AccountAddress.ofNat
          (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)
            solcAddrMask).toNat))])) := by
  simpa [nonpayable] using
    nonpayableReturnExprBodyReturns (cfg := config v) (contract := contract v) h (by
      rw [evalExpr_storage_scalar (hbase := hbase) (her := her) (hty := hty) (hloc := hloc)]
      exact congrArg EvalResult.ok (dogStorageLocLoad_address_offset0 evm slot))

theorem dogUint256GetterBodyReturns (v : DogImmutables) (evm : EVM.State) (locals : Store)
    {ref : StorageRef} {er : EvaledStorageRef} {slot : UInt256}
    (h : evm.executionEnv.weiValue = ⟨0⟩)
    (hbase : locals.get? ref.base = none)
    (her : evalStorageRef (config v) { contract := contract v, locals := locals } evm ref = .ok er)
    (hty : storageTypeAt? (contract v).storage er = some (.elem (.int uint256Int)))
    (hloc : (config v).storage.layout er = fun _ => some (wordLoc slot)) :
    ExecTransitionBody (config v) (contract v) evm locals (nonpayable ++ [ .return [(.storage ref)] ])
      (.returned { contract := contract v, locals := locals } evm
        (some [(.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot).toNat))])) := by
  simpa [nonpayable] using
    nonpayableReturnExprBodyReturns (cfg := config v) (contract := contract v) h (by
      rw [evalExpr_storage_scalar (hbase := hbase) (her := her) (hty := hty) (hloc := hloc)]
      exact congrArg EvalResult.ok (dogStorageLocLoad_uint256 evm slot))

theorem dogAddressGetterBodyCore
    {v : DogImmutables} {code : ByteArray}
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    {transition : TransitionDecl} {entry returnPc routine slot : UInt256}
    (hcode : I.code = code)
    (hdispatch : dispatchMsg (contract v) I.calldata = some transition)
    (hdecode :
      decodeCalldataWithMode (config v).abiDecodeMode (transition.params.map Param.name)
        (transitionSignature transition).paramTypes I.calldata = some ∅)
    (hreach : ∃ k C, RD code I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) entry [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hentry : solcGetterEntryWf code entry returnPc routine)
    (hgetter : solcAddressSlotGetterWf code routine slot)
    (hroutine : (D_J code 0).contains routine = true)
    (hreturnJd : (D_J code 0).contains returnPc = true)
    (hretmem : solcReturnAddressFromMemWf code returnPc)
    (hreturn : transition.returnType = [addr])
    (hbody :
      ExecTransitionBody (config v) (contract v)
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅ transition.body
        (.returned { contract := contract v, locals := ∅ }
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (some [(.address (AccountAddress.ofNat
            (dogAddressReturnWord slot σ_solm I).toNat))]))) :
    runtimeEquivalenceFor (config v) (contract v) cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hword : dogSlotWord slot σ_evm I = dogSlotWord slot σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner slot ⟨0⟩
  have hval :
      some [Value.address (AccountAddress.ofNat (dogAddressReturnWord slot σ_solm I).toNat)] =
        some [Value.address (AccountAddress.ofNat (dogAddressReturnWord slot σ_evm I).toNat)] := by
    have hslot : dogSlotWord slot σ_solm I = dogSlotWord slot σ_evm I := hword.symm
    simp [dogAddressReturnWord, hslot]
  have henc :
      returnEquiv (UInt256.toByteArray (dogAddressReturnWord slot σ_evm I))
        (some [(.address (AccountAddress.ofNat (dogAddressReturnWord slot σ_evm I).toNat))])
        transition.returnType := by
    rw [hreturn]
    simpa [dogAddressReturnWord] using
      (returnEquiv_of_encode
        (solcAddressReturnEncoding (addrTy := addr) rfl (dogSlotWord slot σ_evm I)))
  have hret := RD.solcAddressGetterExternal (code := code) (g := Sat256.ofUInt256 g)
    (returnPc := returnPc) (entry := entry) (routine := routine) (slot := slot)
    hreach hentry hgetter hroutine hreturnJd hretmem
  have hret' :
      RDret code (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) (cA, σ_evm)
        (UInt256.toByteArray (dogAddressReturnWord slot σ_evm I)) := by
    simpa [dogAddressReturnWord, dogSlotWord] using hret
  exact hret'.reEquivExecutionTransport hcode hdispatch hdecode hbody hval hAccounts henc

theorem dogUint256GetterBodyCore
    {v : DogImmutables} {code : ByteArray}
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    {transition : TransitionDecl} {entry returnPc routine slot : UInt256}
    (hcode : I.code = code)
    (hdispatch : dispatchMsg (contract v) I.calldata = some transition)
    (hdecode :
      decodeCalldataWithMode (config v).abiDecodeMode (transition.params.map Param.name)
        (transitionSignature transition).paramTypes I.calldata = some ∅)
    (hreach : ∃ k C, RD code I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) entry [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hentry : solcGetterEntryWf code entry returnPc routine)
    (hgetter : solcWordSlotGetterWf code routine slot)
    (hroutine : (D_J code 0).contains routine = true)
    (hreturnJd : (D_J code 0).contains returnPc = true)
    (hretmem : solcReturnWordFromMemWf code returnPc)
    (hreturn : transition.returnType = [uint256])
    (hbody :
      ExecTransitionBody (config v) (contract v)
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅ transition.body
        (.returned { contract := contract v, locals := ∅ }
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (some [(.int (Int.ofNat (dogSlotWord slot σ_solm I).toNat))]))) :
    runtimeEquivalenceFor (config v) (contract v) cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hword : dogSlotWord slot σ_evm I = dogSlotWord slot σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner slot ⟨0⟩
  have hval :
      some [Value.int (Int.ofNat (dogSlotWord slot σ_solm I).toNat)] =
        some [Value.int (Int.ofNat (dogSlotWord slot σ_evm I).toNat)] := by
    rw [hword]
  have henc :
      returnEquiv (UInt256.toByteArray (dogSlotWord slot σ_evm I))
        (some [(.int (Int.ofNat (dogSlotWord slot σ_evm I).toNat))])
        transition.returnType := by
    rw [hreturn]
    exact returnEquiv_of_encode
      (by simpa [uint256] using uint256ReturnEncoding (dogSlotWord slot σ_evm I))
  have hret := RD.solcWordGetterExternal (code := code) (g := Sat256.ofUInt256 g)
    (returnPc := returnPc) (entry := entry) (routine := routine) (slot := slot)
    hreach hentry hgetter hroutine hreturnJd hretmem
  have hret' :
      RDret code (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) (cA, σ_evm)
        (UInt256.toByteArray (dogSlotWord slot σ_evm I)) := by
    simpa [dogSlotWord] using hret
  exact hret'.reEquivExecutionTransport hcode hdispatch hdecode hbody hval hAccounts henc

theorem dogAddressValueTransport (a : AccountAddress) :
    some [Value.address (AccountAddress.ofNat a.toNat)] =
      some [Value.address (AccountAddress.ofNat
        (UInt256.land (EVM.Word.ofNat a.toNat) solcAddrMask).toNat)] := by
  have hword : (EVM.Word.ofNat a.toNat).toNat = a.toNat := by
    unfold EVM.Word.ofNat UInt256.ofNat UInt256.toNat
    exact Nat.mod_eq_of_lt
      (lt_of_lt_of_le a.isLt (show AccountAddress.size ≤ UInt256.size from by decide))
  have hcanon : (EVM.Word.ofNat a.toNat).toNat < EVM.addressModulus := by
    rw [hword]
    change a.toNat < EVM.twoPow 160
    simp [EVM.twoPow, AccountAddress.size]
  rw [solcAddrMask_clean hcanon, hword]

theorem dogAddrLitEval {v : DogImmutables}
    {cA gh bl σ σ₀ A I} {g : Sat256} (a : EVM.Address) :
    evalExpr? (config v) { contract := contract v, locals := ∅ }
      (initState cA gh bl σ σ₀ g A I) (addrLit a) =
      .ok (Value.address (AccountAddress.ofNat a.toNat)) := by
  dsimp [addrLit]
  have hint :
      evalExpr? (config v) { contract := contract v, locals := ∅ }
        (initState cA gh bl σ σ₀ g A I) (.intLit (↑↑a)) =
        .ok (.int (↑↑a)) := by
    simp [evalExpr?, pure]
  unfold evalExpr?
  rw [hint]
  change (if (↑↑a : Int) < 0 then EvalResult.error EvalError.typeError
      else EvalResult.ok
        (Value.address (AccountAddress.ofNat (Int.toNat (↑↑a : Int))))) =
    EvalResult.ok (Value.address (AccountAddress.ofNat ↑a))
  rw [if_neg (by omega)]
  simp

/-! ### LOG2

The base reasoning library has LOG1/LOG3/LOG4 combinators; Dog emits two-topic auth logs.
-/

-- LIBRARY CANDIDATE: move to `Reasoning.Reach` beside `RD.log1`, `RD.log3`, and `RD.log4`.
def stLog2 (s : State) (a b c d : UInt256) (t : List UInt256) : State :=
  { s with
    substate.logSeries := s.substate.logSeries.push
      ⟨s.executionEnv.codeOwner, #[c, d], s.machineState.memory.readWithPadding a.toNat b.toNat⟩
    machineState.stack := t
    machineState.activeWords :=
      UInt256.ofNat (MachineState.M s.machineState.activeWords.toNat a.toNat b.toNat)
    machineState.gasAvailable :=
      (s.machineState.gasAvailable.subNat (memoryExpansionCost s .LOG2)).subNat
        (GasConstants.Glog + GasConstants.Glogdata * b.toNat + 2 * GasConstants.Glogtopic)
    machineState.pc := s.machineState.pc + ⟨1⟩
    machineState.execLength := s.machineState.execLength + 1 }

-- LIBRARY CANDIDATE: move to `Reasoning.Stepping` with `stLog2`.
theorem log2_xstep {s : State} {code : ByteArray} {pcv a b c d : UInt256}
    {t : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = pcv)
    (hdec : decode code pcv = some (.LOG2, .none)) (hperm : s.executionEnv.perm = true)
    (hstk : s.machineState.stack = a :: b :: c :: d :: t) (hov : t.length ≤ 1024) :
    Xstep (D_J code 0) s =
      (if s.machineState.gasAvailable.toNat < memoryExpansionCost s .LOG2 +
            (GasConstants.Glog + GasConstants.Glogdata * b.toNat + 2 * GasConstants.Glogtopic)
       then .error .OutOfGass else .ok (stLog2 s a b c d t, .none)) := by
  have hd : decode s.executionEnv.code s.machineState.pc = some (.LOG2, .none) := by
    rw [hcode, hpc]; exact hdec
  rw [← hcode, step_log2 s hd, hstk]
  have hov' : ¬ ((a :: b :: c :: d :: t).length - 4 + 0 > 1024) := by
    simp only [List.length_cons]; omega
  have hpermF : (¬ s.executionEnv.perm = true) = False := eq_false (by simp [hperm])
  simp only [collapse_two_stage, if_neg hov', hpermF, if_false, stLog2]

-- LIBRARY CANDIDATE: move to `Reasoning.Reach` beside `RD.log1`, `RD.log3`, and `RD.log4`.
theorem RD.log2 {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a b c d : UInt256} {t : List UInt256} (mcost : ℕ) (awout : UInt256)
    (h : RD code ee g s0 pc (a :: b :: c :: d :: t) mem aw rdata acc k C)
    (hdec : decode code pc = some (.LOG2, .none)) (hperm : ee.perm = true)
    (hmc : ∀ s : State, s.machineState.activeWords = aw →
        s.machineState.stack = a :: b :: c :: d :: t →
        memoryExpansionCost s .LOG2 = mcost)
    (hawout : UInt256.ofNat (MachineState.M aw.toNat a.toNat b.toNat) = awout)
    (hov : t.length ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩) t mem awout rdata acc (k + 1)
      (C + (mcost + (GasConstants.Glog + GasConstants.Glogdata * b.toNat
        + 2 * GasConstants.Glogtopic))) := by
  unfold RD at h ⊢
  rcases h with hoog | ⟨s, hX, hcode, hpc, hstk, hgas, hk, hC, hmem, haw, hrdata,
      hacc, hee, hworld⟩
  · exact Or.inl hoog
  · have hmcS : memoryExpansionCost s .LOG2 = mcost := hmc s haw hstk
    have hperms : s.executionEnv.perm = true := by rw [hee]; exact hperm
    have st := log2_xstep hcode hpc hdec hperms hstk hov
    rw [hmcS] at st
    by_cases gg : g.toNat < C + (mcost
        + (GasConstants.Glog + GasConstants.Glogdata * b.toNat + 2 * GasConstants.Glogtopic))
    · exact Or.inl (hX.trans (stepOOG hgas st hk hC (by omega)))
    · refine Or.inr ⟨stLog2 s a b c d t,
        hX.trans (stepContinue hgas st hk (Nat.not_lt.mp gg)), ?_, ?_, ?_, ?_,
          (by have : 1 ≤ GasConstants.Glog := (by decide); omega), by omega,
          ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [stLog2]; exact hcode
      · simp only [stLog2]; rw [hpc]
      · simp only [stLog2]
      · simp only [stLog2, hmcS]
        rw [hgas, Sat256.subNat_sub_add_of_sub_sub, Sat256.subNat_sub_add_of_sub_sub]
      · simp only [stLog2]; exact hmem
      · simp only [stLog2]; rw [haw, hawout]
      · simp only [stLog2]; exact hrdata
      · simp only [stLog2]; exact hacc
      · simp only [stLog2]; exact hee
      · simp only [stLog2]; exact hworld

abbrev dogCallerWardsSlot (I : ExecutionEnv) : UInt256 :=
  solcMappingSlot ⟨0⟩ (solcSourceWord I)

abbrev dogCallerWardsEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "wards", steps := [.mindex (.address I.source)] }

theorem dogCallerWardsEvaledRef_ok {v : DogImmutables}
    {cA gh bl σ σ₀ A I} {g : Sat256} {locals : Store}
    (_hbase : locals.get? "wards" = none) :
    evalStorageRef (config v) { contract := contract v, locals := locals }
      (initState cA gh bl σ σ₀ g A I) (wardsRef sender) =
        .ok (dogCallerWardsEvaledRef I) := by
  simp [dogCallerWardsEvaledRef, wardsRef, sender, evalStorageRef, evalStorageRefSteps,
    evalStorageRefStep, evalExpr?, envValue, valueToKey?, EvalResult.ofOption,
    EvalResult.bind, pure, bind, initState]

theorem dogAuthGuardEval_true {v : DogImmutables}
    {cA gh bl σ σ₀ A I} {g : Sat256} {locals : Store}
    (hbase : locals.get? "wards" = none)
    (hauth : dogSlotWord (dogCallerWardsSlot I) σ I = ⟨1⟩) :
    evalExpr? (config v) { contract := contract v, locals := locals }
      (initState cA gh bl σ σ₀ g A I)
      (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) = .ok (.bool true) := by
  have her := dogCallerWardsEvaledRef_ok (v := v) (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) (locals := locals) hbase
  have hload : Solm.EVM.storageLoad (initState cA gh bl σ σ₀ g A I) I.codeOwner
      (dogCallerWardsSlot I) = ⟨1⟩ := by
    simpa [dogSlotWord] using hauth
  rw [evalExpr?]
  simp only [EvalResult.bind, bind]
  rw [evalExpr_storage_scalar
    (t := .int uint256Int) (loc := wordLoc (dogCallerWardsSlot I))
    (hbase := by simpa [wardsRef] using hbase)
    (her := her)
    (hty := by simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, uint256St])
    (hloc := by
      funext evm
      simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw,
        dogCallerWardsEvaledRef, dogCallerWardsSlot, wardsSlot, mapSlot, solcMappingSlot,
        keyValueToWord_address, solcSourceWord])]
  rw [dogStorageLocLoad_uint256]
  simp only [initState] at hload ⊢
  rw [hload]
  simp [evalExpr?, evalBinaryOp?]
  all_goals native_decide

theorem dogAuthGuardEval_false {v : DogImmutables}
    {cA gh bl σ σ₀ A I} {g : Sat256} {locals : Store}
    (hbase : locals.get? "wards" = none)
    (hauth : dogSlotWord (dogCallerWardsSlot I) σ I ≠ ⟨1⟩) :
    evalExpr? (config v) { contract := contract v, locals := locals }
      (initState cA gh bl σ σ₀ g A I)
      (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) = .ok (.bool false) := by
  have her := dogCallerWardsEvaledRef_ok (v := v) (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) (locals := locals) hbase
  let w := Solm.EVM.storageLoad (initState cA gh bl σ σ₀ g A I) I.codeOwner
      (dogCallerWardsSlot I)
  have hload : w ≠ ⟨1⟩ := by
    intro hw
    exact hauth (by simpa [w, dogSlotWord] using hw)
  rw [evalExpr?]
  simp only [EvalResult.bind, bind]
  rw [evalExpr_storage_scalar
    (t := .int uint256Int) (loc := wordLoc (dogCallerWardsSlot I))
    (hbase := by simpa [wardsRef] using hbase)
    (her := her)
    (hty := by simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, uint256St])
    (hloc := by
      funext evm
      simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw,
        dogCallerWardsEvaledRef, dogCallerWardsSlot, wardsSlot, mapSlot, solcMappingSlot,
        keyValueToWord_address, solcSourceWord])]
  rw [dogStorageLocLoad_uint256]
  simp only [initState] at hload ⊢
  simp [evalExpr?, evalBinaryOp?]
  · intro hnat
    apply hload
    apply u256_inj
    simpa using hnat
  all_goals native_decide

theorem RD.solcAddressConstGetterExternal {code : ByteArray} {cA gh bl σ σ₀ A I}
    {g : Sat256} {sel entry routine returnPc val : UInt256} {width : Nat}
    {op : Operation.POp}
    (hreach : ∃ k C, RD code I g (initState cA gh bl σ σ₀ g A I) entry [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hentry : solcGetterEntryWf code entry returnPc routine)
    (hgetter : solcConstGetterWf code routine val width op)
    (hroutine : (D_J code 0).contains routine = true)
    (hret : (D_J code 0).contains returnPc = true)
    (hreturn : solcReturnAddressFromMemWf code returnPc) :
    RDret code g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray (UInt256.land val solcAddrMask)) := by
  obtain ⟨_, _, rdRoutine⟩ := RD.solcGetterThunk hreach hentry hroutine
  obtain ⟨_, _, rdReturn⟩ := RD.solcConstGetter (val := val) (width := width)
    (op := op) (R := [sel]) rdRoutine hgetter hret
    (by simp only [List.length_singleton]; omega)
  exact RD.solcReturnAddressFromMem rdReturn hreturn
    solcFreePtrMem_mload64
    (by rfl)
    (solcReturnMem_mload64 (UInt256.land val solcAddrMask))
    (solcReturnMem_read128 (UInt256.land val solcAddrMask))
    (by simp only [List.length_singleton]; omega)

@[reducible] def solcNoArgsExternalEntryWf
    (code : ByteArray) (pc ret routine : UInt256) : Prop :=
  let p1 := pc + ⟨1⟩
  let p4 := p1 + UInt256.ofNat 3
  let p7 := p4 + UInt256.ofNat 3
  decode code pc = some (.JUMPDEST, .none)
  ∧ decode code p1 = some (.Push .PUSH2, some (ret, 2))
  ∧ decode code p4 = some (.Push .PUSH2, some (routine, 2))
  ∧ decode code p7 = some (.JUMP, .none)

-- LIBRARY CANDIDATE: solc no-argument external entry thunk.
theorem RD.solcNoArgsExternalEntry {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {pc ret routine sel : UInt256}
    {mem rdata : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD code ee g s0 pc [sel] mem aw rdata acc k C)
    (hwf : solcNoArgsExternalEntryWf code pc ret routine)
    (hroutine : (D_J code 0).contains routine = true) :
    ∃ k' C', RD code ee g s0 routine [ret, sel] mem aw rdata acc k' C' := by
  rcases hwf with ⟨hd0, hd1, hd4, hd7⟩
  have rd1 := h.jumpdest hd0 (by evm_ov)
  have rd4 := rd1.push2 ret hd1 (by evm_ov)
  have rd7 := rd4.push2 routine hd4 (by evm_ov)
  exact ⟨_, _, rd7.jump hd7 hroutine (by evm_ov)⟩

@[reducible] def dogAuthTailPc (pc : UInt256) : UInt256 :=
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

@[reducible] def dogAuthCheckWf (code : ByteArray) (pc okPc : UInt256) : Prop :=
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

abbrev dogNotAuthorizedRawWord : UInt256 :=
  ⟨0x111bd9cbdb9bdd0b585d5d1a1bdc9a5e9959⟩

abbrev dogFileUnrecognizedRawWord : UInt256 :=
  ⟨30954105885628950283353179477659576776954465509597691851899989870914947776512⟩

@[reducible] def dogErrorStringRevertTailDirectWf
    (code : ByteArray) (pc len word : UInt256) (op : Operation.POp) (width : ℕ) :
    Prop :=
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
  let p68 := p27 + UInt256.ofNat width.succ
  let pDup3 := p68 + UInt256.ofNat 2
  let pAdd := pDup3 + ⟨1⟩
  let pMstore3 := pAdd + ⟨1⟩
  let pSwap := pMstore3 + ⟨1⟩
  let pMload := pSwap + ⟨1⟩
  let pSwap2 := pMload + ⟨1⟩
  let pDup2 := pSwap2 + ⟨1⟩
  let pSwap3 := pDup2 + ⟨1⟩
  let pSub := pSwap3 + ⟨1⟩
  let p100 := pSub + ⟨1⟩
  let pAdd2 := p100 + UInt256.ofNat 2
  let pSwap4 := pAdd2 + ⟨1⟩
  let pRev := pSwap4 + ⟨1⟩
  decode code pc = some (.Push .PUSH1, some (⟨64⟩, 1))
  ∧ decode code p2 = some (.DUP1, .none)
  ∧ decode code p3 = some (.MLOAD, .none)
  ∧ decode code p4 = some (.Push .PUSH3, some (⟨4594637⟩, 3))
  ∧ decode code p8 = some (.Push .PUSH1, some (⟨229⟩, 1))
  ∧ decode code p10 = some (.SHL, .none)
  ∧ decode code p11 = some (.DUP2, .none)
  ∧ decode code p12 = some (.MSTORE, .none)
  ∧ decode code p13 = some (.Push .PUSH1, some (⟨32⟩, 1))
  ∧ decode code p15 = some (.Push .PUSH1, some (⟨4⟩, 1))
  ∧ decode code p17 = some (.DUP3, .none)
  ∧ decode code p18 = some (.ADD, .none)
  ∧ decode code p19 = some (.MSTORE, .none)
  ∧ decode code p20 = some (.Push .PUSH1, some (len, 1))
  ∧ decode code p22 = some (.Push .PUSH1, some (⟨36⟩, 1))
  ∧ decode code p24 = some (.DUP3, .none)
  ∧ decode code p25 = some (.ADD, .none)
  ∧ decode code p26 = some (.MSTORE, .none)
  ∧ decode code p27 = some (.Push op, some (word, width))
  ∧ decode code p68 = some (.Push .PUSH1, some (⟨68⟩, 1))
  ∧ decode code pDup3 = some (.DUP3, .none)
  ∧ decode code pAdd = some (.ADD, .none)
  ∧ decode code pMstore3 = some (.MSTORE, .none)
  ∧ decode code pSwap = some (.SWAP1, .none)
  ∧ decode code pMload = some (.MLOAD, .none)
  ∧ decode code pSwap2 = some (.SWAP1, .none)
  ∧ decode code pDup2 = some (.DUP2, .none)
  ∧ decode code pSwap3 = some (.SWAP1, .none)
  ∧ decode code pSub = some (.SUB, .none)
  ∧ decode code p100 = some (.Push .PUSH1, some (⟨100⟩, 1))
  ∧ decode code pAdd2 = some (.ADD, .none)
  ∧ decode code pSwap4 = some (.SWAP1, .none)
  ∧ decode code pRev = some (.REVERT, .none)

theorem RD.dogErrorStringRevertTailDirect {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {pc len word : UInt256}
    {op : Operation.POp} {width : ℕ}
    {stk : List UInt256} {mem rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD code ee g s0 pc stk mem (UInt256.ofNat 3) rdata acc k C)
    (hwf : dogErrorStringRevertTailDirectWf code pc len word op width)
    (hpush : op ≠ .PUSH0)
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hov : stk.length + 5 ≤ 1024) :
    RDrev code g s0 := by
  rcases hwf with
    ⟨hd0, hd2, hd3, hd4, hd8, hd10, hd11, hd12, hd13, hd15, hd17, hd18,
      hd19, hd20, hd22, hd24, hd25, hd26, hd27, hd68, hdDup3, hdAdd,
      hdMstore3, hdSwap, hdMload, hdSwap2, hdDup2, hdSwap3, hdSub, hd100,
      hdAdd2, hdSwap4, hdRev⟩
  have rdMload := evm_run h with [
    raw push1 ⟨64⟩ hd0 (by evm_ov),
    raw dup1 hd2 (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) hd3
      mem_cost
      (mloadFreePtrValue (by rw [hmem]; decide) (by decide) hread64)
      (by decide) (by evm_ov)]
  have rdSelectorRaw := rdMload.pushConst (⟨4594637⟩ : UInt256)
    (width := 3) (op := .PUSH3) (by decide) hd4 (by simp only [List.length_cons]; omega)
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
    raw push1 len hd20 (by evm_ov),
    raw push1 ⟨36⟩ hd22 (by evm_ov),
    raw dup3 hd24 (by evm_ov),
    raw add hd25 (by evm_ov),
    raw mstore 3 (solcErrorStringMem2 len mem)
      (UInt256.ofNat 7) hd26 mem_cost (by rfl) (by decide) (by evm_ov)]
  have rdWord := rdPrefix.pushConst word (width := width) (op := op)
    hpush hd27 (by simp only [List.length_cons]; omega)
  exact evm_run rdWord with [
    raw push1 ⟨68⟩ hd68 (by evm_ov),
    raw dup3 hdDup3 (by evm_ov),
    raw add hdAdd (by evm_ov),
    raw mstore 3 (solcErrorStringMem3 len word mem)
      (UInt256.ofNat 8) hdMstore3 mem_cost (by rfl) (by decide) (by evm_ov),
    raw swap1 hdSwap (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 8) hdMload
      mem_cost
      (solcErrorStringMem3_mload64 len word hmem hread64)
      (by decide) (by evm_ov),
    raw swap1 hdSwap2 (by evm_ov),
    raw dup2 hdDup2 (by evm_ov),
    raw swap1 hdSwap3 (by evm_ov),
    raw sub hdSub (by evm_ov),
    raw push1 ⟨100⟩ hd100 (by evm_ov),
    raw add hdAdd2 (by evm_ov),
    raw swap1 hdSwap4 (by evm_ov),
    raw rev 0 hdRev mem_cost (by evm_ov)]

theorem RD.dogAuthCheckOk {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {pc okPc key ret : UInt256} {R : List UInt256}
    {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD code ee g s0 pc (key :: ret :: R)
        solcFreePtrMem (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hwf : dogAuthCheckWf code pc okPc)
    (hauth : solcSlotWord σ ee (solcMappingSlot ⟨0⟩ (solcSourceWord ee)) = ⟨1⟩)
    (hok : (D_J code 0).contains okPc = true)
    (hov : R.length + 7 ≤ 1024) :
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
        (fun acc => acc.storage.findD (solcMappingSlot ⟨0⟩ (solcSourceWord ee)) ⟨0⟩)) = ⟨1⟩ := by
    simpa [solcSlotWord] using hauth
  have rd20 := rd20₀
  rw [hauthRaw, uInt256_eq_self] at rd20
  have rd23 := rd20.push2 okPc hd20 (by evm_ov)
  exact ⟨_, _, rd23.jumpiT hd23 one_ne_zero_uint hok (by evm_ov)⟩

theorem RD.dogAuthCheckRevert {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {pc okPc key ret : UInt256} {R : List UInt256}
    {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD code ee g s0 pc (key :: ret :: R)
        solcFreePtrMem (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hwf : dogAuthCheckWf code pc okPc)
    (htail : solcErrorStringRevertTailWf code (dogAuthTailPc pc) ⟨18⟩
      dogNotAuthorizedRawWord ⟨114⟩ .PUSH18 18)
    (hauth : solcSlotWord σ ee (solcMappingSlot ⟨0⟩ (solcSourceWord ee)) ≠ ⟨1⟩)
    (hov : R.length + 7 ≤ 1024) :
    RDrev code g s0 := by
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
        (fun acc => acc.storage.findD (solcMappingSlot ⟨0⟩ (solcSourceWord ee)) ⟨0⟩)) ≠ ⟨1⟩ := by
    simpa [solcSlotWord] using hauth
  have heq0 :
      UInt256.eq ⟨1⟩
        (σ.find? ee.codeOwner |>.option ⟨0⟩
          (fun acc => acc.storage.findD (solcMappingSlot ⟨0⟩ (solcSourceWord ee)) ⟨0⟩)) = ⟨0⟩ := by
    exact u256_eq_of_ne (fun h1 => hauthRaw h1.symm)
  have rd20 := rd20₀
  rw [heq0] at rd20
  have rd23 := rd20.push2 okPc hd20 (by evm_ov)
  have rdTail₀ := rd23.jumpiNT hd23 (by decide : (⟨0⟩ : UInt256) = ⟨0⟩) (by evm_ov)
  exact RD.solcErrorStringRevertTail (by simpa [dogAuthTailPc] using rdTail₀) htail
    (by decide) (by rfl)
    (twoWordHashMem_size_96 (solcSourceWord ee) ⟨0⟩ solcFreePtrMem_size)
    (twoWordHashMem_read64 (solcSourceWord ee) ⟨0⟩ solcFreePtrMem_size solcFreePtrMem_read64)
    (by simp only [List.length_cons]; omega)

theorem RD.solcOneBytes32ExternalJump {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {decoded ret routine de : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD code ee g s0 decoded (de :: ⟨4⟩ :: ret :: R) mem aw rdata acc k C)
    (hd0 : decode code decoded = some (.JUMPDEST, .none))
    (hd1 : decode code (decoded + ⟨1⟩) = some (.POP, .none))
    (hd2 : decode code (decoded + ⟨1⟩ + ⟨1⟩) = some (.CALLDATALOAD, .none))
    (hd3 :
      decode code (decoded + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) =
        some (.Push .PUSH2, some (routine, 2)))
    (hd6 :
      decode code ((decoded + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) + UInt256.ofNat 3) =
        some (.JUMP, .none))
    (hroutine : (D_J code 0).contains routine = true)
    (hov : R.length + 4 ≤ 1024) :
    ∃ k' C', RD code ee g s0 routine (calldataWord ee.calldata 4 :: ret :: R)
      mem aw rdata acc k' C' := by
  have rd1 := h.jumpdest hd0 (by evm_ov)
  have rd2 := rd1.pop hd1 (by evm_ov)
  have rd3 := rd2.calldataload hd2 (by evm_ov)
  have rd6 := rd3.push2 routine hd3 (by evm_ov)
  exact ⟨_, _, by
    simpa [calldataWord, show (⟨4⟩ : UInt256).toNat = 4 from by decide] using
      rd6.jump hd6 hroutine (by evm_ov)⟩

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

@[reducible] def solcIlksChopGetterWf (code : ByteArray) (pc : UInt256) : Prop :=
  let p1 := pc + ⟨1⟩
  let p3 := p1 + UInt256.ofNat 2
  let p4 := p3 + ⟨1⟩
  let p5 := p4 + ⟨1⟩
  let p6 := p5 + ⟨1⟩
  let p8 := p6 + UInt256.ofNat 2
  let p10 := p8 + UInt256.ofNat 2
  let p11 := p10 + ⟨1⟩
  let p12 := p11 + ⟨1⟩
  let p13 := p12 + ⟨1⟩
  let p15 := p13 + UInt256.ofNat 2
  let p16 := p15 + ⟨1⟩
  let p17 := p16 + ⟨1⟩
  let p18 := p17 + ⟨1⟩
  let p19 := p18 + ⟨1⟩
  let p20 := p19 + ⟨1⟩
  let p21 := p20 + ⟨1⟩
  decode code pc = some (.JUMPDEST, .none)
  ∧ decode code p1 = some (.Push .PUSH1, some (⟨0⟩, 1))
  ∧ decode code p3 = some (.SWAP1, .none)
  ∧ decode code p4 = some (.DUP2, .none)
  ∧ decode code p5 = some (.MSTORE, .none)
  ∧ decode code p6 = some (.Push .PUSH1, some (⟨1⟩, 1))
  ∧ decode code p8 = some (.Push .PUSH1, some (⟨32⟩, 1))
  ∧ decode code p10 = some (.DUP2, .none)
  ∧ decode code p11 = some (.SWAP1, .none)
  ∧ decode code p12 = some (.MSTORE, .none)
  ∧ decode code p13 = some (.Push .PUSH1, some (⟨64⟩, 1))
  ∧ decode code p15 = some (.SWAP1, .none)
  ∧ decode code p16 = some (.SWAP2, .none)
  ∧ decode code p17 = some (.KECCAK256, .none)
  ∧ decode code p18 = some (.ADD, .none)
  ∧ decode code p19 = some (.SLOAD, .none)
  ∧ decode code p20 = some (.SWAP1, .none)
  ∧ decode code p21 = some (.JUMP, .none)

theorem RD.solcIlksChopGetter {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {pc key ret : UInt256} {R : List UInt256}
    {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD code ee g s0 pc (key :: ret :: R)
        solcFreePtrMem (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hwf : solcIlksChopGetterWf code pc)
    (hret : (D_J code 0).contains ret = true)
    (hov : R.length + 6 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ret
      (solcSlotWord σ ee (solcMappingSlot ⟨1⟩ key + ⟨1⟩) :: R)
      (twoWordHashMem key ⟨1⟩ solcFreePtrMem) (UInt256.ofNat 3) rdata
      (cA, σ) k' C' := by
  rcases hwf with
    ⟨hd0, hd1, hd3, hd4, hd5, hd6, hd8, hd10, hd11, hd12, hd13, hd15, hd16,
      hd17, hd18, hd19, hd20, hd21⟩
  have rd1 := h.jumpdest hd0 (by simp only [List.length_cons]; omega)
  have rd3 := rd1.push1 ⟨0⟩ hd1 (by evm_ov)
  have rd4 := rd3.swap1 hd3 (by evm_ov)
  have rd5 := rd4.dup2 hd4 (by evm_ov)
  have rd6 := rd5.mstore 0 (wordAt0Mem key solcFreePtrMem)
    (UInt256.ofNat 3) hd5 mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd8 := rd6.push1 ⟨1⟩ hd6 (by evm_ov)
  have rd10 := rd8.push1 ⟨32⟩ hd8 (by evm_ov)
  have rd11 := rd10.dup2 hd10 (by evm_ov)
  have rd12 := rd11.swap1 hd11 (by evm_ov)
  have rd13 := rd12.mstore 0 (twoWordHashMem key ⟨1⟩ solcFreePtrMem)
    (UInt256.ofNat 3) hd12 mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd15 := rd13.push1 ⟨64⟩ hd13 (by evm_ov)
  have rd16 := rd15.swap1 hd15 (by evm_ov)
  have rd17 := rd16.swap2 hd16 (by evm_ov)
  have hslot := twoWordHashMem_solcMappingSlot ⟨1⟩ key solcFreePtrMem_size
  have rd18 := rd17.keccak256 0 (solcMappingSlot ⟨1⟩ key)
    (UInt256.ofNat 3) hd17 mem_cost hslot (by native_decide) (by evm_ov)
  have rd19 := rd18.add hd18 (by evm_ov)
  obtain ⟨_, _, rd20⟩ := rd19.sload hd19 (by evm_ov)
  have rd21 := rd20.swap1 hd20 (by evm_ov)
  exact ⟨_, _, by simpa [solcSlotWord] using rd21.jump hd21 hret (by evm_ov)⟩

/-! ## Patched-runtime prefix facts -/

private theorem byteArray_prefix_suffix (b : ByteArray) (n : Nat) (hn : n ≤ b.size) :
    b.extract 0 n ++ b.extract n b.size = b := by
  rw [ByteArray.extract_append_extract]
  rw [show min 0 n = 0 by omega, show max n b.size = b.size by omega]
  exact byteArray_extract_self b

private theorem spliceBytes?_eq_pref_append {pref rest value out : ByteArray} {offset : Nat}
    (h : spliceBytes? (pref ++ rest) offset value = some out) (hoff : pref.size ≤ offset) :
    ∃ rest', out = pref ++ rest' := by
  unfold spliceBytes? at h
  split at h
  · cases h
    refine ⟨rest.extract 0 (offset - pref.size) ++ value ++
      (pref ++ rest).extract (offset + value.size) (pref ++ rest).size, ?_⟩
    rw [Reasoning.Theory.extract_append_span]
    · rw [Reasoning.Theory.byteArray_extract_self]
      simp only [ByteArray.append_assoc]
    · omega
    · omega
  · simp at h

private theorem patchRuntime_eq_pref_append_aux (ps : List (Nat × ByteArray))
    {pref acc out : ByteArray} (hacc : ∃ rest, acc = pref ++ rest)
    (hall : ∀ p ∈ ps, pref.size ≤ p.1)
    (h : ps.foldlM (fun acc p =>
      if p.2.size = 32 then spliceBytes? acc p.1 p.2 else none) acc = some out) :
    ∃ rest, out = pref ++ rest := by
  induction ps generalizing acc with
  | nil =>
      simp at h
      cases h
      exact hacc
  | cons p ps ih =>
      simp only [List.foldlM_cons] at h
      by_cases hsz : p.2.size = 32
      · rw [if_pos hsz] at h
        rcases hacc with ⟨rest, rfl⟩
        cases hsp : spliceBytes? (pref ++ rest) p.1 p.2 with
        | none => simp [hsp] at h
        | some acc' =>
            simp [hsp] at h
            exact ih (hacc := spliceBytes?_eq_pref_append hsp (hall p (by simp)))
              (hall := fun q hq => hall q (by simp [hq])) h
      · rw [if_neg hsz] at h
        simp at h

private theorem patchRuntime_eq_pref_append {template out : ByteArray}
    {ps : List (Nat × ByteArray)} {n : Nat} (hn : n ≤ template.size)
    (hall : ∀ p ∈ ps, n ≤ p.1) (h : patchRuntime template ps = some out) :
    ∃ rest, out = template.extract 0 n ++ rest := by
  unfold patchRuntime at h
  refine patchRuntime_eq_pref_append_aux ps ?_ ?_ h
  · exact ⟨template.extract n template.size, (byteArray_prefix_suffix template n hn).symm⟩
  · intro p hp
    simpa [ByteArray.size_extract, hn] using hall p hp

private theorem dog_patches_ge_1405 (v : DogImmutables) :
    ∀ p ∈ patches v, 1405 ≤ p.1 := by
  intro p hp
  simp [patches, patchesFrom, offsets, immValues, wordBytes?, valueToWord, List.lookup] at hp
  rcases hp with rfl | rfl | rfl | rfl <;> norm_num

theorem dogPatchedPrefix1405 {v : DogImmutables} {code : ByteArray}
    (hpatch : patchRuntime dogBytecode (patches v) = some code) :
    ∃ rest, code = dogBytecode.extract 0 1405 ++ rest := by
  exact patchRuntime_eq_pref_append (by native_decide) (dog_patches_ge_1405 v) hpatch

theorem dogDecodePatchedEqTemplate1405 {v : DogImmutables} {code : ByteArray} {pc : UInt256}
    (hpatch : patchRuntime dogBytecode (patches v) = some code) (hwin : pc.toNat + 33 ≤ 1405) :
    decode code pc = decode dogBytecode pc := by
  let pref := dogBytecode.extract 0 1405
  let tail0 := dogBytecode.extract 1405 dogBytecode.size
  obtain ⟨tail, htail⟩ := dogPatchedPrefix1405 hpatch
  have htemplate : dogBytecode = pref ++ tail0 := by
    dsimp [pref, tail0]
    exact (byteArray_prefix_suffix dogBytecode 1405 (by native_decide)).symm
  have hprefSize : pref.size = 1405 := by
    dsimp [pref]
    rw [ByteArray.size_extract]
    have hs : 1405 ≤ dogBytecode.size := by native_decide
    omega
  rw [htail]
  change decode (pref ++ tail) pc = decode dogBytecode pc
  rw [Reasoning.Theory.decode_append_left_window pref tail pc
    (by rw [hprefSize]; exact hwin) (by rw [hprefSize]; norm_num)]
  rw [htemplate]
  rw [Reasoning.Theory.decode_append_left_window pref tail0 pc
    (by rw [hprefSize]; exact hwin) (by rw [hprefSize]; norm_num)]

theorem dogDecodePatchedEqPrefix1405 {v : DogImmutables} {code : ByteArray} {pc : UInt256}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (hpc : pc.toNat < 1405)
    (hwin : ∀ b instr,
      (dogBytecode.extract 0 1405).get? pc.toNat = some b → parseInstr b = some instr →
        pc.toNat + 1 + argOnNBytesOfInstr instr ≤ 1405)
    (hwin64 : ∀ b instr,
      (dogBytecode.extract 0 1405).get? pc.toNat = some b → parseInstr b = some instr →
        pc.toNat + 1 + argOnNBytesOfInstr instr < 2 ^ 64) :
    decode code pc = decode dogBytecode pc := by
  let pref := dogBytecode.extract 0 1405
  let tail0 := dogBytecode.extract 1405 dogBytecode.size
  obtain ⟨tail, htail⟩ := dogPatchedPrefix1405 hpatch
  have htemplate : dogBytecode = pref ++ tail0 := by
    dsimp [pref, tail0]
    exact (byteArray_prefix_suffix dogBytecode 1405 (by native_decide)).symm
  have hprefSize : pref.size = 1405 := by
    dsimp [pref]
    rw [ByteArray.size_extract]
    have hs : 1405 ≤ dogBytecode.size := by native_decide
    omega
  have hleft : decode (pref ++ tail) pc = decode pref pc := by
    exact Reasoning.Theory.decode_append_left pref tail pc
      (by rw [hprefSize]; exact hpc)
      (by
        intro b instr hb hparse
        rw [hprefSize]
        exact hwin b instr (by simpa [pref] using hb) hparse)
      (by
        intro b instr hb hparse
        exact hwin64 b instr (by simpa [pref] using hb) hparse)
  have hright : decode dogBytecode pc = decode pref pc := by
    rw [htemplate]
    exact Reasoning.Theory.decode_append_left pref tail0 pc
      (by rw [hprefSize]; exact hpc)
      (by
        intro b instr hb hparse
        rw [hprefSize]
        exact hwin b instr (by simpa [pref] using hb) hparse)
      (by
        intro b instr hb hparse
        exact hwin64 b instr (by simpa [pref] using hb) hparse)
  rw [htail]
  change decode (pref ++ tail) pc = decode dogBytecode pc
  rw [hleft, hright]

def dogPrefixWindowLe1405 (pc : UInt256) : Bool :=
  match (dogBytecode.extract 0 1405).get? pc.toNat with
  | some b =>
      match parseInstr b with
      | some instr => decide (pc.toNat + 1 + argOnNBytesOfInstr instr ≤ 1405)
      | none => true
  | none => true

theorem dogPrefixWindowLe1405_of_true {pc : UInt256}
    (hok : dogPrefixWindowLe1405 pc = true) :
    ∀ b instr,
      (dogBytecode.extract 0 1405).get? pc.toNat = some b → parseInstr b = some instr →
        pc.toNat + 1 + argOnNBytesOfInstr instr ≤ 1405 := by
  intro b instr hb hparse
  unfold dogPrefixWindowLe1405 at hok
  rw [hb] at hok
  simp [hparse] at hok
  exact hok

def dogPrefixWindowLt64 (pc : UInt256) : Bool :=
  match (dogBytecode.extract 0 1405).get? pc.toNat with
  | some b =>
      match parseInstr b with
      | some instr => decide (pc.toNat + 1 + argOnNBytesOfInstr instr < 2 ^ 64)
      | none => true
  | none => true

theorem dogPrefixWindowLt64_of_true {pc : UInt256}
    (hok : dogPrefixWindowLt64 pc = true) :
    ∀ b instr,
      (dogBytecode.extract 0 1405).get? pc.toNat = some b → parseInstr b = some instr →
        pc.toNat + 1 + argOnNBytesOfInstr instr < 2 ^ 64 := by
  intro b instr hb hparse
  unfold dogPrefixWindowLt64 at hok
  rw [hb] at hok
  simp [hparse] at hok
  exact hok

theorem dogPushAtPatchedEqTemplate1405 {v : DogImmutables} {code : ByteArray} {pc : UInt256}
    (hpatch : patchRuntime dogBytecode (patches v) = some code) (hwin : pc.toNat + 33 ≤ 1405) :
    pushAt code pc = pushAt dogBytecode pc := by
  unfold pushAt
  rw [dogDecodePatchedEqTemplate1405 hpatch hwin]

theorem dogPatchedDJumpPrefix1405 {v : DogImmutables} {code : ByteArray} (target : UInt256)
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (hcontains : (D_J (dogBytecode.extract 0 1405) 0).contains target = true) :
    (D_J code 0).contains target = true := by
  let pref := dogBytecode.extract 0 1405
  obtain ⟨tail, htail⟩ := dogPatchedPrefix1405 hpatch
  rw [htail]
  change (D_J (pref ++ tail) 0).contains target = true
  exact Reasoning.Theory.D_J_contains_append_left pref tail target hcontains

private theorem spliceBytes?_extract_before {b val out : ByteArray} {offset start stop : Nat}
    (h : spliceBytes? b offset val = some out)
    (hbefore : stop ≤ offset) :
    out.extract start stop = b.extract start stop := by
  unfold spliceBytes? at h
  split at h
  · cases h
    rw [ByteArray.append_assoc]
    rw [extract_append_left (b.extract 0 offset) (val ++ b.extract (offset + val.size) b.size)
      start stop]
    · rw [extract_extract_BA]
      rw [show min (0 + stop) offset = stop by omega]
      simp
    · rw [ByteArray.size_extract]
      omega
  · simp at h

private theorem spliceBytes?_extract_after {b val out : ByteArray} {offset start stop : Nat}
    (h : spliceBytes? b offset val = some out)
    (hafter : offset + val.size ≤ start) (hle : start ≤ stop) (hstop : stop ≤ b.size) :
    out.extract start stop = b.extract start stop := by
  unfold spliceBytes? at h
  split at h
  · cases h
    rw [extract_append_right_window (b.extract 0 offset ++ val)
      (b.extract (offset + val.size) b.size) start stop]
    · rw [ByteArray.size_append, ByteArray.size_extract]
      rw [show min offset b.size = offset by omega]
      simp only [Nat.sub_zero]
      rw [extract_extract_BA]
      rw [show offset + val.size + (start - (offset + val.size)) = start by omega]
      rw [show min (offset + val.size + (stop - (offset + val.size))) b.size = stop by omega]
    · rw [ByteArray.size_append, ByteArray.size_extract]
      rw [show min offset b.size = offset by omega]
      omega
  · simp at h

private theorem spliceBytes?_extract_disjoint {b val out : ByteArray} {offset start stop : Nat}
    (h : spliceBytes? b offset val = some out)
    (hdisj : stop ≤ offset ∨ offset + val.size ≤ start) (hle : start ≤ stop)
    (hstop : stop ≤ b.size) :
    out.extract start stop = b.extract start stop := by
  rcases hdisj with hbefore | hafter
  · exact spliceBytes?_extract_before h hbefore
  · exact spliceBytes?_extract_after h hafter hle hstop

private theorem spliceBytes?_size_eq {b val out : ByteArray} {offset : Nat}
    (h : spliceBytes? b offset val = some out) :
    out.size = b.size := by
  unfold spliceBytes? at h
  split at h
  · cases h
    rw [ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
      ByteArray.size_extract]
    omega
  · simp at h

private theorem spliceBytes?_extract_patch {b val out : ByteArray} {offset : Nat}
    (h : spliceBytes? b offset val = some out) :
    out.extract offset (offset + val.size) = val := by
  unfold spliceBytes? at h
  split at h
  · cases h
    rw [ByteArray.append_assoc]
    rw [extract_append_right_window (b.extract 0 offset)
      (val ++ b.extract (offset + val.size) b.size) offset (offset + val.size)]
    · rw [ByteArray.size_extract]
      have hoff : offset ≤ b.size := by omega
      rw [show min offset b.size = offset by omega]
      rw [show offset - (offset - 0) = 0 by omega]
      rw [show offset + val.size - (offset - 0) = val.size by omega]
      rw [extract_append_left val (b.extract (offset + val.size) b.size) 0 val.size]
      · exact byteArray_extract_self val
      · omega
    · rw [ByteArray.size_extract]
      omega
  · simp at h

private theorem spliceBytes?_offset_add_size_le {b val out : ByteArray} {offset : Nat}
    (h : spliceBytes? b offset val = some out) :
    offset + val.size ≤ b.size := by
  unfold spliceBytes? at h
  split at h
  · assumption
  · simp at h

private theorem patchRuntime_extract_eq_aux (ps : List (Nat × ByteArray))
    {template acc out : ByteArray} {start stop : Nat}
    (hextract : acc.extract start stop = template.extract start stop)
    (hsize : acc.size = template.size)
    (hle : start ≤ stop) (hstop : stop ≤ template.size)
    (hdisj : ∀ p ∈ ps, stop ≤ p.1 ∨ p.1 + 32 ≤ start)
    (h : ps.foldlM (fun acc p =>
      if p.2.size = 32 then spliceBytes? acc p.1 p.2 else none) acc = some out) :
    out.extract start stop = template.extract start stop ∧ out.size = template.size := by
  induction ps generalizing acc with
  | nil =>
      simp at h
      cases h
      exact ⟨hextract, hsize⟩
  | cons p ps ih =>
      simp only [List.foldlM_cons] at h
      by_cases hszp : p.2.size = 32
      · rw [if_pos hszp] at h
        cases hsp : spliceBytes? acc p.1 p.2 with
        | none => simp [hsp] at h
        | some acc' =>
            simp [hsp] at h
            have hdisj' : stop ≤ p.1 ∨ p.1 + p.2.size ≤ start := by
              simpa [hszp] using hdisj p (by simp)
            have hacc' : acc'.extract start stop = template.extract start stop := by
              rw [spliceBytes?_extract_disjoint hsp hdisj' hle (by rw [hsize]; exact hstop)]
              exact hextract
            have hsize' : acc'.size = template.size := by
              rw [spliceBytes?_size_eq hsp, hsize]
            exact ih hacc' hsize'
              (fun q hq => hdisj q (List.mem_cons_of_mem p hq)) h
      · rw [if_neg hszp] at h
        simp at h

theorem patchRuntime_extract_eq {template out : ByteArray}
    {ps : List (Nat × ByteArray)} {start stop : Nat}
    (hle : start ≤ stop) (hstop : stop ≤ template.size)
    (hdisj : ∀ p ∈ ps, stop ≤ p.1 ∨ p.1 + 32 ≤ start)
    (h : patchRuntime template ps = some out) :
    out.extract start stop = template.extract start stop := by
  unfold patchRuntime at h
  exact (patchRuntime_extract_eq_aux ps (template := template) (acc := template)
    (out := out) (start := start) (stop := stop) rfl rfl hle hstop hdisj h).1

private theorem patchRuntime_size_eq {template out : ByteArray}
    {ps : List (Nat × ByteArray)}
    (h : patchRuntime template ps = some out) :
    out.size = template.size := by
  unfold patchRuntime at h
  exact (patchRuntime_extract_eq_aux ps (template := template) (acc := template)
    (out := out) (start := 0) (stop := 0) rfl rfl (by omega) (by omega)
    (fun p hp => Or.inl (by omega)) h).2

theorem dogPatchedSize {v : DogImmutables} {code : ByteArray}
    (hpatch : patchRuntime dogBytecode (patches v) = some code) :
    code.size = dogBytecode.size :=
  patchRuntime_size_eq hpatch

theorem patchRuntime_extract_patch {template out value : ByteArray}
    {pre post : List (Nat × ByteArray)} {offset : Nat}
    (hvalue : value.size = 32)
    (hpost : ∀ p ∈ post, offset + 32 ≤ p.1 ∨ p.1 + 32 ≤ offset)
    (h : patchRuntime template (pre ++ (offset, value) :: post) = some out) :
    out.extract offset (offset + 32) = value := by
  unfold patchRuntime at h
  rw [List.foldlM_append] at h
  cases hpre : List.foldlM
      (fun acc p => if p.2.size = 32 then spliceBytes? acc p.1 p.2 else none)
      template pre with
  | none => simp [hpre] at h
  | some accPre =>
      simp [hpre, hvalue] at h
      cases hsp : spliceBytes? accPre offset value with
      | none => simp [hsp] at h
      | some accTarget =>
          simp [hsp] at h
          have htarget : accTarget.extract offset (offset + 32) = value := by
            simpa [hvalue] using spliceBytes?_extract_patch hsp
          have htargetSize : offset + 32 ≤ accTarget.size := by
            rw [spliceBytes?_size_eq hsp]
            simpa [hvalue] using spliceBytes?_offset_add_size_le hsp
          have htail := patchRuntime_extract_eq_aux post (template := accTarget)
            (acc := accTarget) (out := out) (start := offset) (stop := offset + 32)
            rfl rfl (by omega) htargetSize hpost h
          exact htail.1.trans htarget

private theorem patchRuntime_extract'_eq {template out : ByteArray}
    {ps : List (Nat × ByteArray)} {start stop : Nat}
    (hle : start ≤ stop) (hstop : stop ≤ template.size)
    (hstart64 : start < 2 ^ 64) (hstop64 : stop < 2 ^ 64)
    (hdisj : ∀ p ∈ ps, stop ≤ p.1 ∨ p.1 + 32 ≤ start)
    (h : patchRuntime template ps = some out) :
    out.extract' start stop = template.extract' start stop := by
  unfold ByteArray.extract'
  have hguard : (decide (start < 2 ^ 64) && decide (stop < 2 ^ 64)) = true := by
    rw [decide_eq_true hstart64, decide_eq_true hstop64]
    rfl
  rw [if_pos hguard, if_pos hguard]
  exact patchRuntime_extract_eq hle hstop hdisj h

theorem get?_eq_of_extract_one {a b : ByteArray} {idx : Nat}
    (ha : idx < a.size) (hb : idx < b.size)
    (h : a.extract idx (idx + 1) = b.extract idx (idx + 1)) :
    a.get? idx = b.get? idx := by
  unfold ByteArray.get?
  simp only [dif_pos ha, dif_pos hb]
  have hdata := congrArg ByteArray.data h
  have hlist := congrArg Array.toList hdata
  rw [ByteArray.data_extract, ByteArray.data_extract, Array.toList_extract,
    Array.toList_extract, List.extract_eq_take_drop, List.extract_eq_take_drop] at hlist
  have hleft : (List.take (idx + 1 - idx) (List.drop idx a.data.toList))[0]? =
      some (a.get idx ha) := by
    simp [ByteArray.get]
  have hright : (List.take (idx + 1 - idx) (List.drop idx b.data.toList))[0]? =
      some (b.get idx hb) := by
    simp [ByteArray.get]
  have hget := congrArg (fun xs : List UInt8 => xs[0]?) hlist
  change (List.take (idx + 1 - idx) (List.drop idx a.data.toList))[0]? =
      (List.take (idx + 1 - idx) (List.drop idx b.data.toList))[0]? at hget
  rw [hleft, hright] at hget
  exact hget

theorem dogDecodePatchedEqTemplateDisjoint {v : DogImmutables} {code : ByteArray}
    {pc : UInt256}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (hwin : pc.toNat + 33 ≤ dogBytecode.size)
    (hdisj : ∀ p ∈ patches v, pc.toNat + 33 ≤ p.1 ∨ p.1 + 32 ≤ pc.toNat) :
    decode code pc = decode dogBytecode pc := by
  unfold decode
  have hsize := patchRuntime_size_eq hpatch
  have hsize64 : dogBytecode.size < 2 ^ 64 := by native_decide
  have hget : code.get? pc.toNat = dogBytecode.get? pc.toNat := by
    apply get?_eq_of_extract_one
    · rw [hsize]
      omega
    · omega
    · exact patchRuntime_extract_eq (start := pc.toNat) (stop := pc.toNat + 1)
        (by omega) (by omega)
        (by
          intro p hp
          rcases hdisj p hp with hbefore | hafter
          · exact Or.inl (by omega)
          · exact Or.inr hafter)
        hpatch
  rw [hget]
  cases hgetTemplate : dogBytecode.get? pc.toNat with
  | none => simp
  | some b =>
      cases hinstr : parseInstr b with
      | none => simp [hinstr]
      | some instr =>
          simp [hinstr]
          by_cases harg : argOnNBytesOfInstr instr = 0
          · simp [harg]
          · simp [harg]
            have hargpos : 0 < argOnNBytesOfInstr instr := Nat.pos_of_ne_zero harg
            have hargle := argOnNBytesOfInstr_le_32 instr
            rw [patchRuntime_extract'_eq (template := dogBytecode) (out := code)
              (ps := patches v) (start := pc.toNat.succ)
              (stop := pc.toNat.succ + argOnNBytesOfInstr instr)]
            · omega
            · omega
            · omega
            · omega
            · intro p hp
              rcases hdisj p hp with hbefore | hafter
              · exact Or.inl (by
                  omega)
              · exact Or.inr (by omega)
            · exact hpatch

def dogPatchOffsets : List Nat :=
  [1405, 2890, 3170, 3965]

theorem dogPatchOffsetMem (v : DogImmutables) :
    ∀ p ∈ patches v, p.1 ∈ dogPatchOffsets := by
  intro p hp
  simp [patches, patchesFrom, offsets, immValues, wordBytes?, valueToWord, List.lookup] at hp
  rcases hp with rfl | rfl | rfl | rfl <;> simp [dogPatchOffsets]

theorem dogDecodePatchedEqTemplateAway {v : DogImmutables} {code : ByteArray} {pc : UInt256}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (hwin : pc.toNat + 33 ≤ dogBytecode.size)
    (hoffsets : ∀ off ∈ dogPatchOffsets, pc.toNat + 33 ≤ off ∨ off + 32 ≤ pc.toNat) :
    decode code pc = decode dogBytecode pc :=
  dogDecodePatchedEqTemplateDisjoint hpatch hwin (by
    intro p hp
    exact hoffsets p.1 (dogPatchOffsetMem v p hp))

theorem dogDecodePatchedNoArg {v : DogImmutables} {code : ByteArray}
    {pc : UInt256} {byte : UInt8} {op : Operation}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (hwin : pc.toNat + 1 ≤ dogBytecode.size)
    (hoffsets : ∀ off ∈ dogPatchOffsets, pc.toNat + 1 ≤ off ∨ off + 32 ≤ pc.toNat)
    (hgetTemplate : dogBytecode.get? pc.toNat = some byte)
    (hparse : (some byte >>= parseInstr) = some op)
    (harg : argOnNBytesOfInstr op = 0) :
    decode code pc = some (op, .none) := by
  have hsize := dogPatchedSize hpatch
  have hget : code.get? pc.toNat = dogBytecode.get? pc.toNat := by
    apply get?_eq_of_extract_one
    · rw [hsize]
      omega
    · omega
    · exact patchRuntime_extract_eq (start := pc.toNat) (stop := pc.toNat + 1)
        (template := dogBytecode) (out := code) (ps := patches v)
        (by omega) hwin
        (by
          intro p hp
          exact hoffsets p.1 (dogPatchOffsetMem v p hp))
        hpatch
  unfold decode
  rw [hget, hgetTemplate, hparse]
  simp [harg]

private theorem lt_size_of_get?_bind_parseInstr_some {c : ByteArray} {i : ℕ}
    {instr : Operation} (h : c.get? i >>= parseInstr = some instr) : i < c.size := by
  rcases hb : c.get? i with _ | b
  · rw [hb] at h
    simp at h
  · rw [ByteArray.get?] at hb
    split at hb
    · assumption
    · simp at hb

set_option linter.unusedVariables false in
def D_J_auxPreservesTargetBool (template : ByteArray) (offsets : List Nat)
    (target : UInt256) (i : Nat) : Bool :=
  offsets.all (fun offset => decide (i + 1 ≤ offset ∨ offset + 32 ≤ i)) &&
    match hget : template.get? i >>= parseInstr with
    | none => false
    | some instr =>
        if instr = .JUMPDEST ∧ UInt256.ofNat i = target then
          true
        else
          D_J_auxPreservesTargetBool template offsets target (N i instr)
termination_by template.size - i
decreasing_by
  have hN : i < N i instr := by
    simp [N]
    omega
  have hi : i < template.size :=
    lt_size_of_get?_bind_parseInstr_some hget
  omega

private theorem patchRuntime_parse_eq_of_disjoint {template out : ByteArray}
    {ps : List (Nat × ByteArray)} {i : Nat}
    (hpatch : patchRuntime template ps = some out)
    (hdisj : ∀ p ∈ ps, i + 1 ≤ p.1 ∨ p.1 + 32 ≤ i) :
    out.get? i >>= parseInstr = template.get? i >>= parseInstr := by
  by_cases hi : i < template.size
  · have hsize := patchRuntime_size_eq hpatch
    have hget : out.get? i = template.get? i := by
      apply get?_eq_of_extract_one (by rw [hsize]; exact hi) hi
      exact patchRuntime_extract_eq (by omega) (by omega) hdisj hpatch
    rw [hget]
  · have hsize := patchRuntime_size_eq hpatch
    have hout : out.get? i = none := by
      rw [ByteArray.get?, dif_neg]
      rw [hsize]
      omega
    have htemplate : template.get? i = none := by
      rw [ByteArray.get?, dif_neg]
      omega
    rw [hout, htemplate]

private theorem D_J_aux_contains_push_target {code : ByteArray} {i : Nat}
    {result : Array UInt256} :
    (D_J_aux code (N i .JUMPDEST) (result.push (UInt256.ofNat i))).contains
      (UInt256.ofNat i) = true := by
  rw [D_J_aux_acc]
  rw [Array.contains_iff_mem]
  simp

theorem D_J_aux_contains_of_patchRuntime_preservesTarget {template out : ByteArray}
    {ps : List (Nat × ByteArray)} {offsets : List Nat} {target : UInt256} {i : Nat}
    {result : Array UInt256}
    (hpatch : patchRuntime template ps = some out)
    (hoffsets : ∀ p ∈ ps, p.1 ∈ offsets)
    (hscan : D_J_auxPreservesTargetBool template offsets target i = true) :
    (D_J_aux out i result).contains target = true := by
  rw [D_J_auxPreservesTargetBool] at hscan
  cases htemplate : template.get? i >>= parseInstr with
  | none =>
      rw [htemplate] at hscan
      simp at hscan
  | some instr =>
      rw [htemplate] at hscan
      simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hscan
      rcases hscan with ⟨hdisj, htail⟩
      have hpatchDisj : ∀ p ∈ ps, i + 1 ≤ p.1 ∨ p.1 + 32 ≤ i := by
        intro p hp
        exact hdisj p.1 (hoffsets p hp)
      have hparse := patchRuntime_parse_eq_of_disjoint hpatch hpatchDisj
      rw [D_J_aux_eq_some out i result instr (by rw [hparse, htemplate])]
      by_cases htarget : instr = .JUMPDEST ∧ UInt256.ofNat i = target
      · rw [if_pos htarget] at htail
        rcases htarget with ⟨rfl, htarget⟩
        rw [← htarget]
        exact D_J_aux_contains_push_target
      · rw [if_neg htarget] at htail
        exact D_J_aux_contains_of_patchRuntime_preservesTarget hpatch hoffsets htail
termination_by template.size - i
decreasing_by
  have hi := lt_size_of_get?_bind_parseInstr_some htemplate
  simp [N]
  omega

theorem dogPatchedJumpDest {v : DogImmutables} {code : ByteArray} {target : UInt256}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (hscan : D_J_auxPreservesTargetBool dogBytecode dogPatchOffsets target 0 = true) :
    (D_J code 0).contains target = true := by
  exact D_J_aux_contains_of_patchRuntime_preservesTarget hpatch
    (dogPatchOffsetMem v) hscan

end Benchmarks.Dss.Dog
