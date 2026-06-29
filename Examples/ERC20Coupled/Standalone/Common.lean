import Examples.ERC20Coupled.Standalone.Bytecode
import Reasoning.ABI
import Reasoning.Dispatch
import Reasoning.Solc
import Reasoning.SolmBody

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace ERC20Standalone

/-! ## ERC20-local storage and ABI helpers -/

/-- `ByteArray` `==` reflects equality. -/
theorem erc20ByteArray_eq_of_beq {a b : ByteArray} (h : (a == b) = true) : a = b := by
  apply ByteArray.ext
  exact eq_of_beq (by simpa [BEq.beq, ByteArray.instBEq] using h)

/-- The little-endian serialization used by `storageLocLoad` round-trips for a full EVM word. -/
theorem fromBytesLE_roundtrip (w : UInt256) :
    fromBytes' (EVM.Word.toBytesLEWithSizeProof w).1 = w.toNat := by
  show fromBytes' (toBytes' w.val ++ List.replicate (32 - (toBytes' w.val).length) 0) = w.toNat
  rw [fromBytes'_append_zeros, fromBytes'_toBytes']; rfl

/-- Loading an ERC20 full-slot `uint256` location is the source-level integer value of the same word. -/
theorem erc20StorageLocLoad_uint256 (evm : EVM.State) (slot : UInt256) :
    storageLocLoad evm (erc20Uint256Loc slot)
      = .int (Int.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot).toNat) := by
  have htake :
      (EVM.Word.toBytesLEWithSizeProof
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).1.extract 0 (32 : Fin 33).val =
        (EVM.Word.toBytesLEWithSizeProof
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).1 := by
    rw [List.extract_eq_take_drop, List.drop_zero]
    exact List.take_of_length_le (by
      rw [(EVM.Word.toBytesLEWithSizeProof
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).2]
      norm_num)
  unfold storageLocLoad erc20Uint256Loc wordToElem
  simp only [uint256Int, Fin.val_zero, Nat.zero_add]
  congr
  rw [htake, fromBytesLE_roundtrip]
  rfl

/-- ABI-encoding a Solm `uint256` return value produces exactly the EVM's returned word bytes. -/
theorem erc20Uint256ReturnEncoding (v : UInt256) :
    encodeReturnValue? uint256 (.int (Int.ofNat v.toNat)) =
      some (UInt256.toByteArray v) := by
  have hlt : Int.ofNat v.toNat < Int.ofNat (EVM.twoPow 256) := by
    simp only [Int.ofNat_eq_natCast, Nat.cast_lt, EVM.twoPow]
    exact v.val.isLt
  have hword : EVM.word v.toNat = v := by
    show UInt256.ofNat v.toNat = v
    exact u256_ofNat_toNat v
  have hval : encodeABIValue? uint256 (.int (Int.ofNat v.toNat))
                = some (EVM.Word.toBytesBE v) := by
    have hltNat : v.toNat < EVM.twoPow 256 := by
      change v.val.val < EVM.twoPow 256
      exact v.val.isLt
    simp [uint256, uint256Int, encodeABIValue?, encodeABIWord?, hword, hltNat]
  have hdyn : isDynamicABIType uint256 = false := rfl
  have hhead : abiTupleHeadSize? [uint256] = some 32 := by
    simp only [abiTupleHeadSize?, staticABIEncodedSize?, isDynamicABIType, uint256, bind,
      Option.bind]
    decide
  rw [toByteArray_eq_toBytesBE,
    show encodeReturnValue? uint256 (.int (Int.ofNat v.toNat))
        = encodeReturnValues? [uint256] [.int (Int.ofNat v.toNat)] from rfl]
  simp only [encodeReturnValues?, encodeABIValues?, hhead, encodeABIValuesFrom?, hval, hdyn,
    bind, Option.bind, if_false, Bool.false_eq_true, List.nil_append, List.append_nil]

/-- The shared solc return wrapper computes the fixed one-word return length. -/
theorem erc20SubRet32_toNat :
    (UInt256.sub ((⟨128⟩ : UInt256) + ⟨32⟩) ⟨128⟩).toNat = 32 := by
  decide

/-- ERC20 jump-destination proof macro. -/
macro "erc20_jd" : term => `(by jump_dest)

/-! ## Address canonicality helpers -/

/-- Address-mask literal (`PUSH20 0xff…ff`) used by solc address cleanup. -/
def erc20AddrMask : UInt256 := ⟨1461501637330902918203684832716283019655932542975⟩

theorem erc20Ueq_self (a : UInt256) : UInt256.eq a a = ⟨1⟩ := by
  have h : UInt256.eq a a = UInt256.ofNat 1 := by simp [UInt256.eq, UInt256.fromBool]
  rw [h]; rfl

theorem erc20Ueq_zero_of_ne {a b : UInt256} (h : ¬ UInt256.eq a b = ⟨1⟩) :
    UInt256.eq a b = ⟨0⟩ := by
  by_cases hab : a = b
  · subst hab; exact absurd (erc20Ueq_self a) h
  · show UInt256.fromBool (decide (a = b)) = ⟨0⟩
    rw [decide_eq_false hab]; rfl

theorem erc20Land_mask160 (n : ℕ) (h : n < 2 ^ 160) : Nat.land n (2 ^ 160 - 1) = n := by
  apply Nat.eq_of_testBit_eq; intro i
  show (n &&& (2 ^ 160 - 1)).testBit i = n.testBit i
  rw [Nat.testBit_and, Nat.testBit_two_pow_sub_one]
  by_cases hi : i < 160
  · rw [decide_eq_true hi, Bool.and_true]
  · rw [decide_eq_false hi, Bool.and_false]
    have : n < 2 ^ i := lt_of_lt_of_le h (Nat.pow_le_pow_right (by norm_num) (by omega))
    exact (Nat.testBit_lt_two_pow this).symm

theorem erc20Canon_eq {w : UInt256} (hcanon : w.toNat < EVM.addressModulus) :
    UInt256.eq w (UInt256.land w erc20AddrMask) = ⟨1⟩ := by
  have hland : UInt256.land w erc20AddrMask = w := by
    apply u256_inj
    show Nat.land w.toNat erc20AddrMask.toNat % EVM.twoPow 256 = w.toNat
    rw [show erc20AddrMask.toNat = 2 ^ 160 - 1 from by decide,
      erc20Land_mask160 _ (by
        rw [show EVM.addressModulus = 2 ^ 160 from by decide] at hcanon
        exact hcanon)]
    exact Nat.mod_eq_of_lt (by
      change w.val.val < EVM.twoPow 256
      exact w.val.isLt)
  rw [hland]; exact erc20Ueq_self w

theorem erc20Word_canonical_of_clean {w : UInt256}
    (hclean : UInt256.eq w (UInt256.land w erc20AddrMask) = ⟨1⟩) :
    w.toNat < EVM.addressModulus := by
  have heq : w = UInt256.land w erc20AddrMask := by
    by_contra hne
    simp only [UInt256.eq, UInt256.fromBool, Bool.toUInt256, hne, decide_false,
      Bool.false_eq_true, ↓reduceIte] at hclean
    exact absurd hclean (by decide)
  have hlandle : ∀ a b : ℕ, Nat.land a b ≤ b := by
    intro a b
    refine Nat.le_of_testBit fun i hi => ?_
    change (a &&& b).testBit i = true at hi
    rw [Nat.testBit_and] at hi
    simp only [Bool.and_eq_true] at hi
    exact hi.2
  have hland : w.toNat = Nat.land w.toNat erc20AddrMask.toNat % EVM.twoPow 256 := by
    conv_lhs => rw [heq]
    rfl
  have hmod : Nat.land w.toNat erc20AddrMask.toNat % EVM.twoPow 256 =
      Nat.land w.toNat erc20AddrMask.toNat :=
    Nat.mod_eq_of_lt (lt_of_le_of_lt (hlandle _ _) (by decide))
  have hmask : erc20AddrMask.toNat < EVM.addressModulus := by decide
  rw [hland, hmod]; exact lt_of_le_of_lt (hlandle _ _) hmask

theorem erc20KeyValueToWord_address_of_canonical (w : UInt256)
    (hcanon : w.toNat < EVM.addressModulus) :
    keyValueToWord (.address (AccountAddress.ofNat w.toNat)) = w := by
  apply u256_inj
  unfold keyValueToWord AccountAddress.ofNat
  exact Nat.mod_eq_of_lt (by
    simpa [EVM.addressModulus, EVM.twoPow, AccountAddress.size] using hcanon)

/-! ## Single-address calldata decoding -/

theorem decodeScalarWords_address_ok {bytes : List UInt8}
    (hlen0 : (bytes.take 32).length = 32)
    (hcanon : (ABI.bytesToWord (bytes.take 32)).toNat < EVM.addressModulus) :
    decodeScalarWords? [addr] bytes 0 =
      some [.address (Ethereum.AccountAddress.ofNat (ABI.bytesToWord (bytes.take 32)).toNat)] := by
  change decodeScalarWords? [.elem .address] bytes 0 =
    some [.address (Ethereum.AccountAddress.ofNat (ABI.bytesToWord (bytes.take 32)).toNat)]
  simp only [decodeScalarWords?]
  rw [decodeScalarWord_address_ok (start := 0) (by simpa using hlen0)
    (by simpa using hcanon)]
  rfl

theorem decodeScalarWords_address_none_noncanon {bytes : List UInt8}
    (hlen0 : (bytes.take 32).length = 32)
    (hnc : ¬ (ABI.bytesToWord (bytes.take 32)).toNat < EVM.addressModulus) :
    decodeScalarWords? [addr] bytes 0 = none := by
  change decodeScalarWords? [.elem .address] bytes 0 = none
  simp only [decodeScalarWords?]
  rw [decodeScalarWord_address_none_noncanon (start := 0) (by simpa using hlen0)
    (by simpa using hnc)]
  simp only [Option.bind, bind]

theorem decodeScalarWords_address_none_short {bytes : List UInt8}
    (hshort : bytes.length < 32) :
    decodeScalarWords? [addr] bytes 0 = none := by
  change decodeScalarWords? [.elem .address] bytes 0 = none
  simp only [decodeScalarWords?]
  have htake0n : ¬ (bytes.take 32).length = 32 := by
    rw [List.length_take]
    omega
  rw [decodeScalarWord_address_none_short (start := 0) (by simpa using htake0n)]
  simp only [Option.bind, bind]

theorem decodeCalldata_address_ok {cd : ByteArray} {x : Solm.Ident}
    (hsz36 : 36 ≤ cd.size) (hbig : cd.size < 2 ^ 255 + 4)
    (hcanon : (calldataWord cd 4).toNat < EVM.addressModulus) :
    decodeCalldata [x] [addr] cd =
      some ((∅ : Solm.Store).insert x
        (.address (Ethereum.AccountAddress.ofNat (calldataWord cd 4).toNat))) := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have htake4 : ((cd.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  have hword4 : ABI.bytesToWord ((cd.toList.drop 4).take 32) = calldataWord cd 4 :=
    decode_word_at_eq cd 4 (by omega) (by norm_num)
  rw [decodeCalldata_scalarWords_eq (names := [x]) (types := [addr]) (cd := cd) (by decide)]
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  rw [if_neg (by rintro ⟨_, hc⟩; rw [List.length_drop, htlen] at hc; omega)]
  rw [decodeScalarWords_address_ok (bytes := cd.toList.drop 4) htake4
    (by rw [hword4]; exact hcanon)]
  change decodeCalldata.insertValues [x]
      [.address (Ethereum.AccountAddress.ofNat
          (ABI.bytesToWord ((cd.toList.drop 4).take 32)).toNat)] ∅ =
    some ((∅ : Solm.Store).insert x
      (.address (Ethereum.AccountAddress.ofNat (calldataWord cd 4).toNat)))
  simp [decodeCalldata.insertValues]
  rw [hword4]

theorem decodeCalldata_address_none_noncanon {cd : ByteArray} {x : Solm.Ident}
    (hsz36 : 36 ≤ cd.size) (hbig : cd.size < 2 ^ 255 + 4)
    (hnc : ¬ (calldataWord cd 4).toNat < EVM.addressModulus) :
    decodeCalldata [x] [addr] cd = none := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have htake4 : ((cd.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  have hword4 : ABI.bytesToWord ((cd.toList.drop 4).take 32) = calldataWord cd 4 :=
    decode_word_at_eq cd 4 (by omega) (by norm_num)
  rw [decodeCalldata_scalarWords_eq (names := [x]) (types := [addr]) (cd := cd) (by decide)]
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  rw [if_neg (by rintro ⟨_, hc⟩; rw [List.length_drop, htlen] at hc; omega)]
  rw [decodeScalarWords_address_none_noncanon (bytes := cd.toList.drop 4) htake4
    (by rw [hword4]; exact hnc)]

theorem decodeCalldata_address_none_short {cd : ByteArray} {x : Solm.Ident}
    (hsz4 : 4 ≤ cd.size) (hshort : cd.size < 36) :
    decodeCalldata [x] [addr] cd = none := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  rw [decodeCalldata_scalarWords_eq (names := [x]) (types := [addr]) (cd := cd) (by decide)]
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  rw [if_neg (by rintro ⟨_, hc⟩; rw [List.length_drop, htlen] at hc; omega)]
  rw [decodeScalarWords_address_none_short (bytes := cd.toList.drop 4) (by
    rw [List.length_drop, htlen]
    omega)]

theorem decodeCalldata_address_none_huge {cd : ByteArray} {x : Solm.Ident}
    (hbig : 2 ^ 255 + 4 ≤ cd.size) :
    decodeCalldata [x] [addr] cd = none := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  rw [decodeCalldata_scalarWords_eq (names := [x]) (types := [addr]) (cd := cd) (by decide)]
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  rw [if_pos]
  · exact ⟨rfl, by decide, by rw [List.length_drop, htlen]; omega⟩

/-! ## Two-address calldata decoding -/

theorem decodeScalarWords_address_address_ok {bytes : List UInt8}
    (hlen0 : (bytes.take 32).length = 32)
    (hlen32 : ((bytes.drop 32).take 32).length = 32)
    (hcanon0 : (ABI.bytesToWord (bytes.take 32)).toNat < EVM.addressModulus)
    (hcanon32 : (ABI.bytesToWord ((bytes.drop 32).take 32)).toNat < EVM.addressModulus) :
    decodeScalarWords? [addr, addr] bytes 0 =
      some [.address (Ethereum.AccountAddress.ofNat (ABI.bytesToWord (bytes.take 32)).toNat),
        .address (Ethereum.AccountAddress.ofNat
          (ABI.bytesToWord ((bytes.drop 32).take 32)).toNat)] := by
  change decodeScalarWords? [.elem .address, .elem .address] bytes 0 =
    some [.address (Ethereum.AccountAddress.ofNat (ABI.bytesToWord (bytes.take 32)).toNat),
      .address (Ethereum.AccountAddress.ofNat
        (ABI.bytesToWord ((bytes.drop 32).take 32)).toNat)]
  simp only [decodeScalarWords?, Nat.zero_add]
  rw [decodeScalarWord_address_ok (start := 0) (by simpa using hlen0)
    (by simpa using hcanon0)]
  simp only [Option.bind, bind]
  rw [decodeScalarWord_address_ok (start := 32) hlen32 hcanon32]
  rfl

theorem decodeScalarWords_address_address_none_noncanon0 {bytes : List UInt8}
    (hlen0 : (bytes.take 32).length = 32)
    (hnc0 : ¬ (ABI.bytesToWord (bytes.take 32)).toNat < EVM.addressModulus) :
    decodeScalarWords? [addr, addr] bytes 0 = none := by
  change decodeScalarWords? [.elem .address, .elem .address] bytes 0 = none
  simp only [decodeScalarWords?, Nat.zero_add]
  rw [decodeScalarWord_address_none_noncanon (start := 0) (by simpa using hlen0)
    (by simpa using hnc0)]
  simp only [Option.bind, bind]

theorem decodeScalarWords_address_address_none_noncanon1 {bytes : List UInt8}
    (hlen0 : (bytes.take 32).length = 32)
    (hlen32 : ((bytes.drop 32).take 32).length = 32)
    (hcanon0 : (ABI.bytesToWord (bytes.take 32)).toNat < EVM.addressModulus)
    (hnc32 : ¬ (ABI.bytesToWord ((bytes.drop 32).take 32)).toNat < EVM.addressModulus) :
    decodeScalarWords? [addr, addr] bytes 0 = none := by
  change decodeScalarWords? [.elem .address, .elem .address] bytes 0 = none
  simp only [decodeScalarWords?, Nat.zero_add]
  rw [decodeScalarWord_address_ok (start := 0) (by simpa using hlen0)
    (by simpa using hcanon0)]
  simp only [Option.bind, bind]
  rw [decodeScalarWord_address_none_noncanon (start := 32) hlen32 hnc32]

theorem decodeScalarWords_address_address_none_short {bytes : List UInt8}
    (hshort : bytes.length < 64) :
    decodeScalarWords? [addr, addr] bytes 0 = none := by
  change decodeScalarWords? [.elem .address, .elem .address] bytes 0 = none
  simp only [decodeScalarWords?, Nat.zero_add]
  by_cases h32 : bytes.length < 32
  · have htake0n : ¬ (bytes.take 32).length = 32 := by
      rw [List.length_take]; omega
    rw [decodeScalarWord_address_none_short (start := 0) (by simpa using htake0n)]
    simp only [Option.bind, bind]
  · have htake0 : (bytes.take 32).length = 32 := by
      rw [List.length_take]; omega
    have htake32n : ¬ ((bytes.drop 32).take 32).length = 32 := by
      rw [List.length_take, List.length_drop]; omega
    by_cases hcanon0 : (ABI.bytesToWord (bytes.take 32)).toNat < EVM.addressModulus
    · rw [decodeScalarWord_address_ok (start := 0) (by simpa using htake0)
        (by simpa using hcanon0)]
      simp only [Option.bind, bind]
      rw [decodeScalarWord_address_none_short (start := 32) htake32n]
    · rw [decodeScalarWord_address_none_noncanon (start := 0) (by simpa using htake0)
        (by simpa using hcanon0)]
      simp only [Option.bind, bind]

theorem decodeCalldata_address_address_ok {cd : ByteArray} {x y : Solm.Ident}
    (hsz68 : 68 ≤ cd.size) (hbig : cd.size < 2 ^ 255 + 4)
    (hcanon0 : (calldataWord cd 4).toNat < EVM.addressModulus)
    (hcanon1 : (calldataWord cd 36).toNat < EVM.addressModulus) :
    decodeCalldata [x, y] [addr, addr] cd =
      some (((∅ : Solm.Store).insert x
        (.address (Ethereum.AccountAddress.ofNat (calldataWord cd 4).toNat))).insert y
        (.address (Ethereum.AccountAddress.ofNat (calldataWord cd 36).toNat))) := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  have htake4 : ((cd.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]; omega
  have htake36 : ((cd.toList.drop 36).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]; omega
  have hword4 : ABI.bytesToWord ((cd.toList.drop 4).take 32) = calldataWord cd 4 :=
    decode_word_at_eq cd 4 (by omega) (by norm_num)
  have hword36 : ABI.bytesToWord ((cd.toList.drop 36).take 32) = calldataWord cd 36 :=
    decode_word_at_eq cd 36 (by omega) (by norm_num)
  have htake36' : ((cd.toList.drop 4).drop 32 |>.take 32).length = 32 := by
    simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using htake36
  rw [decodeCalldata_scalarWords_eq (names := [x, y]) (types := [addr, addr]) (cd := cd)
    (by decide)]
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  rw [if_neg (by rintro ⟨_, hc⟩; rw [List.length_drop, htlen] at hc; omega)]
  rw [decodeScalarWords_address_address_ok (bytes := cd.toList.drop 4) htake4 htake36'
    (by rw [hword4]; exact hcanon0)
    (by rw [show ABI.bytesToWord (((cd.toList.drop 4).drop 32).take 32) =
        calldataWord cd 36 from by simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm,
          Nat.add_assoc] using hword36]; exact hcanon1)]
  change decodeCalldata.insertValues [x, y]
      [.address (Ethereum.AccountAddress.ofNat
          (ABI.bytesToWord ((cd.toList.drop 4).take 32)).toNat),
        .address (Ethereum.AccountAddress.ofNat
          (ABI.bytesToWord (((cd.toList.drop 4).drop 32).take 32)).toNat)] ∅ =
    some (((∅ : Solm.Store).insert x
      (.address (Ethereum.AccountAddress.ofNat (calldataWord cd 4).toNat))).insert y
      (.address (Ethereum.AccountAddress.ofNat (calldataWord cd 36).toNat)))
  simp [decodeCalldata.insertValues]
  rw [hword4]
  rw [hword36]

theorem decodeCalldata_address_address_none_noncanon0 {cd : ByteArray} {x y : Solm.Ident}
    (hsz68 : 68 ≤ cd.size) (hbig : cd.size < 2 ^ 255 + 4)
    (hnc0 : ¬ (calldataWord cd 4).toNat < EVM.addressModulus) :
    decodeCalldata [x, y] [addr, addr] cd = none := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  have htake4 : ((cd.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]; omega
  have hword4 : ABI.bytesToWord ((cd.toList.drop 4).take 32) = calldataWord cd 4 :=
    decode_word_at_eq cd 4 (by omega) (by norm_num)
  rw [decodeCalldata_scalarWords_eq (names := [x, y]) (types := [addr, addr]) (cd := cd)
    (by decide)]
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  rw [if_neg (by rintro ⟨_, hc⟩; rw [List.length_drop, htlen] at hc; omega)]
  rw [decodeScalarWords_address_address_none_noncanon0 (bytes := cd.toList.drop 4) htake4
    (by rw [hword4]; exact hnc0)]

theorem decodeCalldata_address_address_none_noncanon1 {cd : ByteArray} {x y : Solm.Ident}
    (hsz68 : 68 ≤ cd.size) (hbig : cd.size < 2 ^ 255 + 4)
    (hcanon0 : (calldataWord cd 4).toNat < EVM.addressModulus)
    (hnc1 : ¬ (calldataWord cd 36).toNat < EVM.addressModulus) :
    decodeCalldata [x, y] [addr, addr] cd = none := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  have htake4 : ((cd.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]; omega
  have htake36 : ((cd.toList.drop 36).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]; omega
  have hword4 : ABI.bytesToWord ((cd.toList.drop 4).take 32) = calldataWord cd 4 :=
    decode_word_at_eq cd 4 (by omega) (by norm_num)
  have hword36 : ABI.bytesToWord ((cd.toList.drop 36).take 32) = calldataWord cd 36 :=
    decode_word_at_eq cd 36 (by omega) (by norm_num)
  have htake36' : ((cd.toList.drop 4).drop 32 |>.take 32).length = 32 := by
    simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using htake36
  rw [decodeCalldata_scalarWords_eq (names := [x, y]) (types := [addr, addr]) (cd := cd)
    (by decide)]
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  rw [if_neg (by rintro ⟨_, hc⟩; rw [List.length_drop, htlen] at hc; omega)]
  rw [decodeScalarWords_address_address_none_noncanon1 (bytes := cd.toList.drop 4) htake4 htake36'
    (by rw [hword4]; exact hcanon0)
    (by rw [show ABI.bytesToWord (((cd.toList.drop 4).drop 32).take 32) =
        calldataWord cd 36 from by simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm,
          Nat.add_assoc] using hword36]; exact hnc1)]

theorem decodeCalldata_address_address_none_short {cd : ByteArray} {x y : Solm.Ident}
    (hsz4 : 4 ≤ cd.size) (hshort : cd.size < 68) :
    decodeCalldata [x, y] [addr, addr] cd = none := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  rw [decodeCalldata_scalarWords_eq (names := [x, y]) (types := [addr, addr]) (cd := cd)
    (by decide)]
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  rw [if_neg (by rintro ⟨_, hc⟩; rw [List.length_drop, htlen] at hc; omega)]
  rw [decodeScalarWords_address_address_none_short (bytes := cd.toList.drop 4) (by
    rw [List.length_drop, htlen]; omega)]

theorem decodeCalldata_address_address_none_huge {cd : ByteArray} {x y : Solm.Ident}
    (hbig : 2 ^ 255 + 4 ≤ cd.size) :
    decodeCalldata [x, y] [addr, addr] cd = none := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  rw [decodeCalldata_scalarWords_eq (names := [x, y]) (types := [addr, addr]) (cd := cd)
    (by decide)]
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  rw [if_pos]
  · exact ⟨rfl, by decide, by rw [List.length_drop, htlen]; omega⟩

end ERC20Standalone

namespace Reasoning.Reach

/-- ERC20's solc `cleanup_t_uint256` identity routine at pc 1894. -/
theorem RD.erc20Routine0766 {g : Sat256} {s0 : State} {ee : ExecutionEnv} {k C : ℕ}
    {v ret : UInt256} {R : List UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD erc20Bytecode ee g s0 ⟨1894⟩ (v :: ret :: R) mem aw rdata acc k C)
    (hret : (D_J erc20Bytecode 0).contains ret = true) (hov : R.length + 4 ≤ 1024) :
    RD erc20Bytecode ee g s0 ret (v :: R) mem aw rdata acc (k + 9) (C + 27) :=
  evm_run h with [
    jumpdest, push0, dup2, swap1, pop, swap2, swap1, pop,
    jump hret ]

/-- ERC20's shared solc ABI encoder for one `uint256` word at pc 2073. -/
theorem RD.erc20RoutineEncodeUint256 {g : Sat256} {s0 : State} {ee : ExecutionEnv} {k C : ℕ}
    {val ret : UInt256} {R : List UInt256}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD erc20Bytecode ee g s0 ⟨2073⟩ (⟨128⟩ :: val :: ret :: R)
        solcFreePtrMem (UInt256.ofNat 3) rdata acc k C)
    (hret : (D_J erc20Bytecode 0).contains ret = true) (hov : R.length + 11 ≤ 1024) :
    ∃ k' C', RD erc20Bytecode ee g s0 ret ((⟨128⟩ + ⟨32⟩) :: R)
      (solcReturnMem val) (UInt256.ofNat 5) rdata acc k' C' := by
  let rd := evm_run h with [
    jumpdest, push0, push1 ⟨32⟩, dup3, add, swap1, pop,
    push2 ⟨2092⟩, push0, dup4, add, dup5, push2 ⟨2058⟩,
    jump (by jump_dest),
    jumpdest, push2 ⟨2067⟩, dup2, push2 ⟨1894⟩,
    jump (by jump_dest),
    raw erc20Routine0766 (by jump_dest) (by evm_ov),
    jumpdest, dup3,
    raw mstore 6 (solcReturnMem val) (UInt256.ofNat 5) (by decide) mem_cost
      (by rw [show ((⟨128⟩ : UInt256) + ⟨0⟩).toNat = 128 from by decide]; rfl)
      (by decide) (by evm_ov),
    pop, pop,
    jump (by jump_dest),
    jumpdest, swap3, swap2, pop, pop,
    jump hret ]
  exact ⟨_, _, rd⟩

-- A merged routine: ~30 opcode steps in one proof, each generating a `decode erc20Bytecode pc`
-- `decide` over the large bytecode.  The original `dec*` chain spread these across four theorems,
-- each with its own default budget; one lemma collects them, so it needs a raised budget.
set_option maxHeartbeats 1000000 in
/-- ERC20's solc shared `abi_decode_address` load-and-mask routine, entered at pc 1874.

    From `[off, csize, ret] ++ R`, it loads the calldata word at byte-offset `off`, runs the 160-bit
    address-mask subroutine, and arrives at the canonicality check (pc 1861) with the stack
    `[mask(word), word, 1888, word, off, csize, ret] ++ R`.  This is the per-address-argument decoder
    body copied ~14× across the ERC20 function proofs; factoring it here lets each call site supply
    only the offset and overflow bound.  The single following step — the canonicality compare at pc
    1861 — is left to the caller because it branches: canonical addresses jump on to `ret`, while
    non-canonical ones revert.  `csize`, `ret`, and the working scratch are threaded untouched. -/
theorem RD.erc20DecodeAddrMask {g : Sat256} {s0 : State} {ee : ExecutionEnv} {k C : ℕ}
    {off csize ret : UInt256} {R : List UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD erc20Bytecode ee g s0 ⟨1874⟩ (off :: csize :: ret :: R) mem aw rdata acc k C)
    (hov : R.length + 14 ≤ 1024) :
    ∃ k' C', RD erc20Bytecode ee g s0 ⟨1861⟩
        (UInt256.land (uInt256OfByteArray (ee.calldata.readBytes off.toNat 32))
            ERC20Standalone.erc20AddrMask
          :: uInt256OfByteArray (ee.calldata.readBytes off.toNat 32) :: ⟨1888⟩
          :: uInt256OfByteArray (ee.calldata.readBytes off.toNat 32)
          :: off :: csize :: ret :: R) mem aw rdata acc k' C' := by
  -- load the word and step to the validator (pc 1852)
  have h1852 := evm_run h with [
    jumpdest, push0, dup2, calldataload, swap1, pop, push2 ⟨1888⟩, dup2,
    push2 ⟨1852⟩, jump (by jump_dest) ]
  -- enter the mask subroutine dispatch (pc 1835)
  have h1835 := evm_run h1852 with [
    jumpdest, push2 ⟨1861⟩, dup2, push2 ⟨1835⟩, jump (by jump_dest) ]
  -- run the 160-bit mask subroutine, landing at the canonicality check (pc 1861)
  exact ⟨_, _, evm_run h1835 with [
    jumpdest, push0, push2 ⟨1845⟩, dup3, push2 ⟨1804⟩, jump (by jump_dest),
    jumpdest, push0, push20 ERC20Standalone.erc20AddrMask, dup3, and, swap1, pop, swap2, swap1, pop,
    jump (by jump_dest),
    jumpdest, swap1, pop, swap2, swap1, pop, jump (by jump_dest) ]⟩

set_option maxHeartbeats 400000 in
/-- Success continuation of the shared address-argument decoder: from pc 1874 with
    `[off, csize, ret] ++ R`, decode a **canonical** address (`hcanon`) and return the decoded word to
    the dynamic return address `ret` as `[word] ++ R`.  Built on `erc20DecodeAddrMask` plus the
    canonicality-pass branch; shared by every successful ERC20 address decode. -/
theorem RD.erc20DecodeAddrOk {g : Sat256} {s0 : State} {ee : ExecutionEnv} {k C : ℕ}
    {off csize ret : UInt256} {R : List UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD erc20Bytecode ee g s0 ⟨1874⟩ (off :: csize :: ret :: R) mem aw rdata acc k C)
    (hcanon : (uInt256OfByteArray (ee.calldata.readBytes off.toNat 32)).toNat
        < EVM.addressModulus)
    (hret : (D_J erc20Bytecode 0).contains ret = true) (hov : R.length + 14 ≤ 1024) :
    ∃ k' C', RD erc20Bytecode ee g s0 ret
        (uInt256OfByteArray (ee.calldata.readBytes off.toNat 32) :: R) mem aw rdata acc k' C' := by
  obtain ⟨k', C', rd⟩ := RD.erc20DecodeAddrMask h hov
  have hclean : UInt256.eq (uInt256OfByteArray (ee.calldata.readBytes off.toNat 32))
      (UInt256.land (uInt256OfByteArray (ee.calldata.readBytes off.toNat 32))
        ERC20Standalone.erc20AddrMask) = ⟨1⟩ :=
    ERC20Standalone.erc20Canon_eq hcanon
  exact ⟨_, _, evm_run rd with [
    jumpdest, dup2, eq, push2 ⟨1871⟩, jumpiT (by rw [hclean]; decide) (by jump_dest),
    jumpdest, pop, jump (by jump_dest),
    jumpdest, swap3, swap2, pop, pop, jump hret ]⟩

/-- Revert continuation of the shared address-argument decoder: from pc 1874 with
    `[off, csize, ret] ++ R`, a **non-canonical** address (`hnc`) fails the canonicality check and
    reverts.  Built on `erc20DecodeAddrMask` plus the canonicality-fail branch; shared by every ERC20
    address-decode revert. -/
theorem RD.erc20DecodeAddrRevert {g : Sat256} {s0 : State} {ee : ExecutionEnv} {k C : ℕ}
    {off csize ret : UInt256} {R : List UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD erc20Bytecode ee g s0 ⟨1874⟩ (off :: csize :: ret :: R) mem aw rdata acc k C)
    (hnc : UInt256.eq (uInt256OfByteArray (ee.calldata.readBytes off.toNat 32))
        (UInt256.land (uInt256OfByteArray (ee.calldata.readBytes off.toNat 32))
          ERC20Standalone.erc20AddrMask) = ⟨0⟩)
    (hov : R.length + 14 ≤ 1024) :
    RDrev erc20Bytecode g s0 := by
  obtain ⟨k', C', rd⟩ := RD.erc20DecodeAddrMask h hov
  exact (evm_run rd with [
    jumpdest, dup2, eq, push2 ⟨1871⟩, jumpiNT (by rw [hnc]),
    raw revertStub (by decide) (by decide) (by decide) (by evm_ov) ] :
    RDrev erc20Bytecode g s0)

end Reasoning.Reach

namespace ERC20Standalone

/-- ERC20's shared uint256 encoder at pc 2073, generalized to an arbitrary incoming memory. -/
theorem erc20RoutineEncodeUint256FromMem {g : Sat256} {s0 : State} {ee : ExecutionEnv} {k C : ℕ}
    {val ret : UInt256} {R : List UInt256} {mem memout : ByteArray}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD erc20Bytecode ee g s0 ⟨2073⟩ (⟨128⟩ :: val :: ret :: R)
        mem (UInt256.ofNat 3) rdata acc k C)
    (hmemout : (UInt256.toByteArray val).write 0 mem 128 32 = memout)
    (hret : (D_J erc20Bytecode 0).contains ret = true) (hov : R.length + 11 ≤ 1024) :
    ∃ k' C', RD erc20Bytecode ee g s0 ret ((⟨128⟩ + ⟨32⟩) :: R)
      memout (UInt256.ofNat 5) rdata acc k' C' := by
  let rd := evm_run h with [
    jumpdest, push0, push1 ⟨32⟩, dup3, add, swap1, pop,
    push2 ⟨2092⟩, push0, dup4, add, dup5, push2 ⟨2058⟩,
    jump erc20_jd,
    jumpdest, push2 ⟨2067⟩, dup2, push2 ⟨1894⟩,
    jump erc20_jd,
    raw erc20Routine0766 erc20_jd (by evm_ov),
    jumpdest, dup3,
    raw mstore 6 memout (UInt256.ofNat 5) (by decide) mem_cost
      (by rw [show ((⟨128⟩ : UInt256) + ⟨0⟩).toNat = 128 from by decide]; exact hmemout)
      (by decide) (by evm_ov),
    pop, pop,
    jump erc20_jd,
    jumpdest, swap3, swap2, pop, pop,
    jump hret ]
  exact ⟨_, _, rd⟩

end ERC20Standalone
