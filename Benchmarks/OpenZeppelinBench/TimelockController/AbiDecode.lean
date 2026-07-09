import Benchmarks.OpenZeppelinBench.TimelockController.AbiEncode

/-!
# OpenZeppelin TimelockController `hashOperation` calldata decode reconciliation

Solm-side `decodeCalldataWithMode` facts for the 5-argument tuple
`(address, uint256, bytes, bytes32, bytes32)` of `hashOperation`.  These mirror the modern solc
`abi_decode_tuple_t_address_t_uint256_t_bytes_calldata_ptr_t_bytes32_t_bytes32` external decoder
(runtime @4600) and its four revert branches (short head / dirty address / bytes-offset > 2^64 /
bytes length-or-payload OOB).

Reusable `tlcAbiDec…` lemmas: the finite `decodeABIValues?` unfold for a head-`0xa0` tuple with a
single dynamic `bytes` member, with the offset/maxEnd bookkeeping done explicitly.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000
set_option maxHeartbeats 1600000

namespace OpenZeppelinBench.TimelockController

/-! ## Decoded argument components (calldata args base = 4) -/

/-- Relative offset (from args base 4) of the dynamic `bytes` payload, `= cd[68]`. -/
abbrev tlcHashOpArgOff (I : ExecutionEnv) : Nat := (calldataWord I.calldata 68).toNat

/-- The dynamic `bytes` length word, `= cd[4 + off]`. -/
abbrev tlcHashOpArgLen (I : ExecutionEnv) : Nat :=
  (calldataWord I.calldata (4 + tlcHashOpArgOff I)).toNat

/-- The decoded `bytes data` payload (calldata slice `[4+off+32, +len)`). -/
abbrev tlcHashOpData (I : ExecutionEnv) : ByteArray :=
  ⟨((I.calldata.toList.drop (4 + tlcHashOpArgOff I + 32)).take (tlcHashOpArgLen I)).toArray⟩

/-- The decoded `address target` (low 160 bits of `cd[4]`). -/
abbrev tlcHashOpTarget (I : ExecutionEnv) : EVM.Address :=
  AccountAddress.ofNat (calldataWord I.calldata 4).toNat

/-- The decoded `uint256 value` (`cd[36]`). -/
abbrev tlcHashOpValue (I : ExecutionEnv) : Int := Int.ofNat (calldataWord I.calldata 36).toNat

/-- The decoded `bytes32 predecessor` (`cd[100..132]`). -/
abbrev tlcHashOpPred (I : ExecutionEnv) : List UInt8 := (I.calldata.toList.drop 100).take 32

/-- The decoded `bytes32 salt` (`cd[132..164]`). -/
abbrev tlcHashOpSalt (I : ExecutionEnv) : List UInt8 := (I.calldata.toList.drop 132).take 32

/-- The decoded local store bound by `hashOperation(target, value, data, predecessor, salt)`. -/
def tlcHashOpStore (I : ExecutionEnv) : Store :=
  ((((((∅ : Store).insert "target" (.address (tlcHashOpTarget I))).insert
    "value" (.int (tlcHashOpValue I))).insert
    "data" (.bytes (tlcHashOpData I))).insert
    "predecessor" (.fixedBytes bytes32Width (tlcHashOpPred I))).insert
    "salt" (.fixedBytes bytes32Width (tlcHashOpSalt I)))

/-! ## The well-formedness conditions of a decodable `hashOperation` calldata -/

/-- The (execute-path) well-formedness conditions under which both the EVM external decoder
    accepts and the Solm `decodeCalldata` succeeds. -/
structure tlcHashOpWF (I : ExecutionEnv) : Prop where
  head : 164 ≤ I.calldata.size
  small : I.calldata.size < 2 ^ 255
  clean : (calldataWord I.calldata 4).toNat < EVM.addressModulus
  offMax : tlcHashOpArgOff I ≤ solcMaxU64
  lenWord : 4 + tlcHashOpArgOff I + 32 ≤ I.calldata.size
  lenMax : tlcHashOpArgLen I ≤ solcMaxU64
  payload : 4 + tlcHashOpArgOff I + 32 + tlcHashOpArgLen I ≤ I.calldata.size

/-! ## Guard-dispatch helper -/

/-- Common calldata length that fits the `hashOperation` head (5 words after the 4-byte selector). -/
private theorem tlc_enter {I : ExecutionEnv} (hhead : 164 ≤ I.calldata.size)
    (hsmall : I.calldata.size < 2 ^ 255) :
    decodeCalldataWithMode DecodeMode.modern ["target", "value", "data", "predecessor", "salt"]
      [addr, uint256, bytesTy, bytes32, bytes32] I.calldata =
    (match decodeABIValues? [addr, uint256, bytesTy, bytes32, bytes32]
        (I.calldata.toList.drop 4) 0 0 160 160 DecodeMode.modern with
      | some (values, _) =>
          decodeCalldata.insertValues ["target", "value", "data", "predecessor", "salt"] values ∅
      | none => none) := by
  unfold decodeCalldataWithMode decodeCalldata
  have htlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  rw [if_neg (show ¬ I.calldata.toList.length < 4 from by rw [htlen]; omega)]
  rw [if_neg (show ¬ ([addr, uint256, bytesTy, bytes32, bytes32].any isDynamicABIType = true ∧
    2 ^ 255 ≤ I.calldata.toList.length) from by rintro ⟨_, hc⟩; rw [htlen] at hc; omega)]
  rw [if_neg (show ¬ ([addr, uint256, bytesTy, bytes32, bytes32].isEmpty = false ∧
    2 ^ 255 ≤ (I.calldata.toList.drop 4).length) from by
      rintro ⟨_, hc⟩; rw [List.length_drop, htlen] at hc; omega)]
  rw [if_neg (show ¬ (solcTotalSizeDynamicGuard [addr, uint256, bytesTy, bytes32, bytes32] = true ∧
    2 ^ 255 ≤ I.calldata.toList.length) from by simp [solcTotalSizeDynamicGuard])]
  simp only [decodeCalldata.decodeArgs]
  rw [show abiTupleHeadSize? [addr, uint256, bytesTy, bytes32, bytes32] = some 160 from by
    native_decide]
  simp only [bind, Option.bind]
  rw [if_neg (show ¬ (I.calldata.toList.drop 4).length < 160 from by
    rw [List.length_drop, htlen]; omega)]
  cases hd : decodeABIValues? [addr, uint256, bytesTy, bytes32, bytes32]
      (I.calldata.toList.drop 4) 0 0 160 160 DecodeMode.modern with
  | none => rfl
  | some p =>
      obtain ⟨values, e⟩ := p
      dsimp only
      generalize decodeCalldata.insertValues ["target", "value", "data", "predecessor", "salt"]
        values ∅ = s
      cases s <;> rfl

/-! ## Per-member decode helpers -/

/-- A `readNat?` at a 32-byte-aligned calldata slot equals the big-endian word there. -/
private theorem tlc_readNat {I : ExecutionEnv}
    (htlen : I.calldata.toList.length = I.calldata.size) (k : ℕ)
    (hk : 4 + k + 32 ≤ I.calldata.size) :
    readNat? (I.calldata.toList.drop 4) k = some (calldataWord I.calldata (4 + k)).toNat := by
  unfold readNat? readWord? readBytes?
  have hlk : (((I.calldata.toList.drop 4).drop k).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, List.length_drop, htlen]; omega
  rw [if_pos hlk]
  have hword : ABI.bytesToWord (((I.calldata.toList.drop 4).drop k).take 32) =
      calldataWord I.calldata (4 + k) := by
    have h := decode_word_at_eq_any I.calldata (4 + k) (by omega)
    simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h
  simp only [Option.bind, bind, hword]
  rfl

/-- The `address target` member decodes cleanly to `tlcHashOpTarget`. -/
private theorem tlc_addr_ok {I : ExecutionEnv} (hhead : 36 ≤ I.calldata.size)
    (hclean : (calldataWord I.calldata 4).toNat < EVM.addressModulus) :
    decodeABIValue? (.elem .address) (I.calldata.toList.drop 4) 0 =
      some (.address (tlcHashOpTarget I), 32) := by
  have htlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  have hlen0 : (((I.calldata.toList.drop 4).drop 0).take 32).length = 32 := by
    rw [List.drop_zero, List.length_take, List.length_drop, htlen]; omega
  have hword4 : ABI.bytesToWord (((I.calldata.toList.drop 4).drop 0).take 32) =
      calldataWord I.calldata 4 := by
    rw [List.drop_zero]; exact decode_word_at_eq I.calldata 4 (by omega) (by norm_num)
  rw [decodeABIValue_address_ok hlen0 (by rw [hword4]; exact hclean), hword4]

/-- The `uint256 value` member always decodes to `tlcHashOpValue`. -/
private theorem tlc_uint256_ok {I : ExecutionEnv} (hhead : 68 ≤ I.calldata.size) :
    decodeABIValue? uint256 (I.calldata.toList.drop 4) 32 =
      some (.int (tlcHashOpValue I), 64) := by
  have htlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  have hlen32 : (((I.calldata.toList.drop 4).drop 32).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, List.length_drop, htlen]; omega
  have hword36 : ABI.bytesToWord (((I.calldata.toList.drop 4).drop 32).take 32) =
      calldataWord I.calldata 36 := by
    have h := decode_word_at_eq I.calldata 36 (by omega) (by norm_num)
    simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h
  rw [show uint256 = abiUInt256 from rfl, decodeABIValue_uint256_ok hlen32, hword36]

/-! ## Solm decode outcomes

`config.abiDecodeMode = .modern`, `hashOperationTransition.params.map Param.name =
["target","value","data","predecessor","salt"]`, and
`(transitionSignature hashOperationTransition).paramTypes = [addr, uint256, bytesTy, bytes32, bytes32]`
(all by `rfl`; use `show decodeCalldataWithMode DecodeMode.modern [...] [...] I.calldata = _`). -/

/-- Decode success on a well-formed `hashOperation` calldata. -/
theorem tlcDecodeHashOperation_ok {I : ExecutionEnv} (hwf : tlcHashOpWF I) :
    decodeCalldataWithMode config.abiDecodeMode (hashOperationTransition.params.map Param.name)
      (transitionSignature hashOperationTransition).paramTypes I.calldata
      = some (tlcHashOpStore I) := by
  obtain ⟨hhead, hsmall, hclean, hoffMax, hlenWord, hlenMax, hpayload⟩ := hwf
  show decodeCalldataWithMode DecodeMode.modern ["target", "value", "data", "predecessor", "salt"]
    [addr, uint256, bytesTy, bytes32, bytes32] I.calldata = some (tlcHashOpStore I)
  rw [tlc_enter hhead hsmall]
  have htlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  have haddr := tlc_addr_ok (I := I) (by omega) hclean
  have huint : decodeABIValue? (.elem (.int uint256Int)) (I.calldata.toList.drop 4) 32 =
      some (.int (tlcHashOpValue I), 64) := tlc_uint256_ok (by omega)
  have hoffRead : readNat? (I.calldata.toList.drop 4) 64 = some (tlcHashOpArgOff I) := by
    have h := tlc_readNat htlen 64 (by omega); simpa using h
  have hlenRead : readNat? (I.calldata.toList.drop 4) (tlcHashOpArgOff I) = some (tlcHashOpArgLen I) :=
    tlc_readNat htlen (tlcHashOpArgOff I) (by omega)
  have hdrop : (I.calldata.toList.drop 4).drop (tlcHashOpArgOff I + 32) =
      I.calldata.toList.drop (4 + tlcHashOpArgOff I + 32) := by
    rw [List.drop_drop, show 4 + (tlcHashOpArgOff I + 32) = 4 + tlcHashOpArgOff I + 32 from by omega]
  have hpayRead : readBytes? (I.calldata.toList.drop 4) (tlcHashOpArgOff I + 32)
      (tlcHashOpArgLen I) = some ((I.calldata.toList.drop (4 + tlcHashOpArgOff I + 32)).take
        (tlcHashOpArgLen I)) := by
    simp only [readBytes?, hdrop]
    rw [if_pos (show ((I.calldata.toList.drop (4 + tlcHashOpArgOff I + 32)).take
      (tlcHashOpArgLen I)).length = tlcHashOpArgLen I from by
        rw [List.length_take, List.length_drop, htlen]; omega)]
  have hbytesval : decodeABIValue? ABIType.bytes (I.calldata.toList.drop 4) (tlcHashOpArgOff I)
      = some (.bytes (tlcHashOpData I),
        tlcHashOpArgOff I + 32 + paddedSize (tlcHashOpArgLen I)) := by
    simp only [decodeABIValue?, hlenRead, bind, Option.bind, solcMaxLen_modern,
      if_neg (not_lt.mpr hlenMax), hpayRead, tlcHashOpData]
  have hbytes32pred : decodeABIValue? (.elem (.bytes bytes32Width)) (I.calldata.toList.drop 4) 96 =
      some (.fixedBytes bytes32Width (tlcHashOpPred I), 128) := by
    have hlen96 : (((I.calldata.toList.drop 4).drop 96).take 32).length = 32 := by
      rw [List.length_take, List.length_drop, List.length_drop, htlen]; omega
    have h := decodeABIValue_bytes32_ok (bytes := I.calldata.toList.drop 4) (start := 96) hlen96
    rw [show ((I.calldata.toList.drop 4).drop 96).take 32 = tlcHashOpPred I from by
      unfold tlcHashOpPred; rw [List.drop_drop]] at h
    exact h
  have hbytes32salt : decodeABIValue? (.elem (.bytes bytes32Width)) (I.calldata.toList.drop 4) 128 =
      some (.fixedBytes bytes32Width (tlcHashOpSalt I), 160) := by
    have hlen128 : (((I.calldata.toList.drop 4).drop 128).take 32).length = 32 := by
      rw [List.length_take, List.length_drop, List.length_drop, htlen]; omega
    have h := decodeABIValue_bytes32_ok (bytes := I.calldata.toList.drop 4) (start := 128) hlen128
    rw [show ((I.calldata.toList.drop 4).drop 128).take 32 = tlcHashOpSalt I from by
      unfold tlcHashOpSalt; rw [List.drop_drop]] at h
    exact h
  unfold decodeABIValues?
  simp only [addr, isDynamicABIType, staticABIEncodedSize?, Bool.false_eq_true, if_false, bind,
    Option.bind, Nat.add_zero, Nat.zero_add, reduceIte, haddr]
  unfold decodeABIValues?
  simp only [uint256, isDynamicABIType, staticABIEncodedSize?, Bool.false_eq_true, if_false, bind,
    Option.bind, Nat.reduceAdd, reduceIte, huint]
  unfold decodeABIValues?
  simp only [bytesTy, isDynamicABIType, bind, Option.bind, Nat.reduceAdd, reduceIte, hoffRead,
    solcMaxLen_modern, if_neg (not_lt.mpr hoffMax), Nat.zero_add, hbytesval]
  unfold decodeABIValues?
  simp only [bytes32, isDynamicABIType, staticABIEncodedSize?, Bool.false_eq_true, if_false, bind,
    Option.bind, Nat.reduceAdd, reduceIte, hbytes32pred]
  unfold decodeABIValues?
  simp only [isDynamicABIType, staticABIEncodedSize?, Bool.false_eq_true, if_false, bind,
    Option.bind, Nat.reduceAdd, reduceIte, hbytes32salt]
  unfold decodeABIValues?
  simp only [decodeCalldata.insertValues, tlcHashOpStore]

/-- Decode failure: calldata too large (modern signed-size guard, `2^255 ≤ size`). -/
theorem tlcDecodeHashOperation_none_huge {I : ExecutionEnv}
    (hbig : 2 ^ 255 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (hashOperationTransition.params.map Param.name)
      (transitionSignature hashOperationTransition).paramTypes I.calldata = none := by
  show decodeCalldataWithMode DecodeMode.modern ["target", "value", "data", "predecessor", "salt"]
    [addr, uint256, bytesTy, bytes32, bytes32] I.calldata = none
  unfold decodeCalldataWithMode decodeCalldata
  by_cases hlt4 : I.calldata.toList.length < 4
  · rw [if_pos hlt4]
  · rw [if_neg hlt4]
    have htlen : I.calldata.toList.length = I.calldata.size := by
      rw [byteArray_toList_eq, Array.length_toList]; rfl
    rw [if_pos (show [addr, uint256, bytesTy, bytes32, bytes32].any isDynamicABIType = true ∧
      2 ^ 255 ≤ I.calldata.toList.length from ⟨by decide, by rw [htlen]; exact hbig⟩)]

/-- Decode failure: the 5-word (`0xa0`) head is not fully present (`size < 164`). -/
theorem tlcDecodeHashOperation_none_short {I : ExecutionEnv}
    (hshort : I.calldata.size < 164) :
    decodeCalldataWithMode config.abiDecodeMode (hashOperationTransition.params.map Param.name)
      (transitionSignature hashOperationTransition).paramTypes I.calldata = none := by
  show decodeCalldataWithMode DecodeMode.modern ["target", "value", "data", "predecessor", "salt"]
    [addr, uint256, bytesTy, bytes32, bytes32] I.calldata = none
  unfold decodeCalldataWithMode decodeCalldata
  have htlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  by_cases hlt4 : I.calldata.toList.length < 4
  · rw [if_pos hlt4]
  · rw [if_neg hlt4]
    rw [if_neg (show ¬ ([addr, uint256, bytesTy, bytes32, bytes32].any isDynamicABIType = true ∧
      2 ^ 255 ≤ I.calldata.toList.length) from by rintro ⟨_, hc⟩; rw [htlen] at hc; omega)]
    rw [if_neg (show ¬ ([addr, uint256, bytesTy, bytes32, bytes32].isEmpty = false ∧
      2 ^ 255 ≤ (I.calldata.toList.drop 4).length) from by
        rintro ⟨_, hc⟩; rw [List.length_drop, htlen] at hc; omega)]
    rw [if_neg (show ¬ (solcTotalSizeDynamicGuard [addr, uint256, bytesTy, bytes32, bytes32] = true ∧
      2 ^ 255 ≤ I.calldata.toList.length) from by simp [solcTotalSizeDynamicGuard])]
    simp only [decodeCalldata.decodeArgs]
    rw [show abiTupleHeadSize? [addr, uint256, bytesTy, bytes32, bytes32] = some 160 from by
      native_decide]
    simp only [bind, Option.bind]
    rw [if_pos (show (I.calldata.toList.drop 4).length < 160 from by
      rw [List.length_drop, htlen]; omega)]

/-- Decode failure: dirty `address` (high 96 bits of `cd[4]` nonzero). -/
theorem tlcDecodeHashOperation_none_dirtyAddr {I : ExecutionEnv}
    (hhead : 164 ≤ I.calldata.size) (hsmall : I.calldata.size < 2 ^ 255)
    (hdirty : EVM.addressModulus ≤ (calldataWord I.calldata 4).toNat) :
    decodeCalldataWithMode config.abiDecodeMode (hashOperationTransition.params.map Param.name)
      (transitionSignature hashOperationTransition).paramTypes I.calldata = none := by
  show decodeCalldataWithMode DecodeMode.modern ["target", "value", "data", "predecessor", "salt"]
    [addr, uint256, bytesTy, bytes32, bytes32] I.calldata = none
  rw [tlc_enter hhead hsmall]
  have htlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  have hlen0 : ((I.calldata.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]; omega
  have hword4 : ABI.bytesToWord ((I.calldata.toList.drop 4).take 32) = calldataWord I.calldata 4 :=
    decode_word_at_eq I.calldata 4 (by omega) (by norm_num)
  have haddr : decodeABIValue? (.elem .address) (I.calldata.toList.drop 4) 0 = none := by
    apply decodeABIValue_address_none_noncanon
    · rw [List.drop_zero]; exact hlen0
    · rw [List.drop_zero, hword4]; exact not_lt.mpr hdirty
  have hDAV : decodeABIValues? [addr, uint256, bytesTy, bytes32, bytes32]
      (I.calldata.toList.drop 4) 0 0 160 160 DecodeMode.modern = none := by
    simp only [decodeABIValues?, addr, isDynamicABIType, staticABIEncodedSize?, Bool.false_eq_true,
      if_false, bind, Option.bind, Nat.add_zero, Nat.zero_add, haddr]
  rw [hDAV]

/-- Decode failure: the dynamic `bytes` offset exceeds `2^64-1`. -/
theorem tlcDecodeHashOperation_none_offset {I : ExecutionEnv}
    (hhead : 164 ≤ I.calldata.size) (hsmall : I.calldata.size < 2 ^ 255)
    (hclean : (calldataWord I.calldata 4).toNat < EVM.addressModulus)
    (hoff : solcMaxU64 < tlcHashOpArgOff I) :
    decodeCalldataWithMode config.abiDecodeMode (hashOperationTransition.params.map Param.name)
      (transitionSignature hashOperationTransition).paramTypes I.calldata = none := by
  show decodeCalldataWithMode DecodeMode.modern ["target", "value", "data", "predecessor", "salt"]
    [addr, uint256, bytesTy, bytes32, bytes32] I.calldata = none
  rw [tlc_enter hhead hsmall]
  have htlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  have haddr := tlc_addr_ok (I := I) (by omega) hclean
  have huint : decodeABIValue? (.elem (.int uint256Int)) (I.calldata.toList.drop 4) 32 =
      some (.int (tlcHashOpValue I), 64) := tlc_uint256_ok (by omega)
  have hoffRead : readNat? (I.calldata.toList.drop 4) 64 = some (tlcHashOpArgOff I) := by
    have h := tlc_readNat htlen 64 (by omega); simpa using h
  have hDAV : decodeABIValues? [addr, uint256, bytesTy, bytes32, bytes32]
      (I.calldata.toList.drop 4) 0 0 160 160 DecodeMode.modern = none := by
    simp only [decodeABIValues?, addr, uint256, bytesTy, isDynamicABIType, staticABIEncodedSize?,
      Bool.false_eq_true, if_false, bind, Option.bind, Nat.add_zero, Nat.zero_add, Nat.reduceAdd,
      reduceIte, haddr, huint, hoffRead, solcMaxLen_modern, if_pos hoff]
  rw [hDAV]

/-- Decode failure: the `bytes` length word is not present (`size < 4 + off + 32`). -/
theorem tlcDecodeHashOperation_none_lenWord {I : ExecutionEnv}
    (hhead : 164 ≤ I.calldata.size) (hsmall : I.calldata.size < 2 ^ 255)
    (hclean : (calldataWord I.calldata 4).toNat < EVM.addressModulus)
    (hoffMax : tlcHashOpArgOff I ≤ solcMaxU64)
    (hlenWord : I.calldata.size < 4 + tlcHashOpArgOff I + 32) :
    decodeCalldataWithMode config.abiDecodeMode (hashOperationTransition.params.map Param.name)
      (transitionSignature hashOperationTransition).paramTypes I.calldata = none := by
  show decodeCalldataWithMode DecodeMode.modern ["target", "value", "data", "predecessor", "salt"]
    [addr, uint256, bytesTy, bytes32, bytes32] I.calldata = none
  rw [tlc_enter hhead hsmall]
  have htlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  have haddr := tlc_addr_ok (I := I) (by omega) hclean
  have huint : decodeABIValue? (.elem (.int uint256Int)) (I.calldata.toList.drop 4) 32 =
      some (.int (tlcHashOpValue I), 64) := tlc_uint256_ok (by omega)
  have hoffRead : readNat? (I.calldata.toList.drop 4) 64 = some (tlcHashOpArgOff I) := by
    have h := tlc_readNat htlen 64 (by omega); simpa using h
  have hlenRead : readNat? (I.calldata.toList.drop 4) (tlcHashOpArgOff I) = none := by
    unfold readNat? readWord? readBytes?
    rw [if_neg (show ¬ (((I.calldata.toList.drop 4).drop (tlcHashOpArgOff I)).take 32).length = 32
      from by rw [List.length_take, List.length_drop, List.length_drop, htlen]; omega)]
    rfl
  have hbytesval : decodeABIValue? ABIType.bytes (I.calldata.toList.drop 4) (tlcHashOpArgOff I)
      = none := by
    simp only [decodeABIValue?, hlenRead, bind, Option.bind]
  have hDAV : decodeABIValues? [addr, uint256, bytesTy, bytes32, bytes32]
      (I.calldata.toList.drop 4) 0 0 160 160 DecodeMode.modern = none := by
    simp only [decodeABIValues?, addr, uint256, bytesTy, isDynamicABIType, staticABIEncodedSize?,
      Bool.false_eq_true, if_false, bind, Option.bind, Nat.add_zero, Nat.zero_add, Nat.reduceAdd,
      reduceIte, haddr, huint, hoffRead, solcMaxLen_modern, if_neg (not_lt.mpr hoffMax), hbytesval]
  rw [hDAV]

/-- Decode failure: the dynamic `bytes` length exceeds `2^64-1`. -/
theorem tlcDecodeHashOperation_none_lenBig {I : ExecutionEnv}
    (hhead : 164 ≤ I.calldata.size) (hsmall : I.calldata.size < 2 ^ 255)
    (hclean : (calldataWord I.calldata 4).toNat < EVM.addressModulus)
    (hoffMax : tlcHashOpArgOff I ≤ solcMaxU64)
    (hlenWord : 4 + tlcHashOpArgOff I + 32 ≤ I.calldata.size)
    (hlenBig : solcMaxU64 < tlcHashOpArgLen I) :
    decodeCalldataWithMode config.abiDecodeMode (hashOperationTransition.params.map Param.name)
      (transitionSignature hashOperationTransition).paramTypes I.calldata = none := by
  show decodeCalldataWithMode DecodeMode.modern ["target", "value", "data", "predecessor", "salt"]
    [addr, uint256, bytesTy, bytes32, bytes32] I.calldata = none
  rw [tlc_enter hhead hsmall]
  have htlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  have haddr := tlc_addr_ok (I := I) (by omega) hclean
  have huint : decodeABIValue? (.elem (.int uint256Int)) (I.calldata.toList.drop 4) 32 =
      some (.int (tlcHashOpValue I), 64) := tlc_uint256_ok (by omega)
  have hoffRead : readNat? (I.calldata.toList.drop 4) 64 = some (tlcHashOpArgOff I) := by
    have h := tlc_readNat htlen 64 (by omega); simpa using h
  have hlenRead : readNat? (I.calldata.toList.drop 4) (tlcHashOpArgOff I) = some (tlcHashOpArgLen I) :=
    tlc_readNat htlen (tlcHashOpArgOff I) (by omega)
  have hbytesval : decodeABIValue? ABIType.bytes (I.calldata.toList.drop 4) (tlcHashOpArgOff I)
      = none := by
    simp only [decodeABIValue?, hlenRead, bind, Option.bind, solcMaxLen_modern, if_pos hlenBig]
  have hDAV : decodeABIValues? [addr, uint256, bytesTy, bytes32, bytes32]
      (I.calldata.toList.drop 4) 0 0 160 160 DecodeMode.modern = none := by
    simp only [decodeABIValues?, addr, uint256, bytesTy, isDynamicABIType, staticABIEncodedSize?,
      Bool.false_eq_true, if_false, bind, Option.bind, Nat.add_zero, Nat.zero_add, Nat.reduceAdd,
      reduceIte, haddr, huint, hoffRead, solcMaxLen_modern, if_neg (not_lt.mpr hoffMax), hbytesval]
  rw [hDAV]

/-- Decode failure: the `bytes` payload is not fully present (`size < 4 + off + 32 + len`). -/
theorem tlcDecodeHashOperation_none_payload {I : ExecutionEnv}
    (hhead : 164 ≤ I.calldata.size) (hsmall : I.calldata.size < 2 ^ 255)
    (hclean : (calldataWord I.calldata 4).toNat < EVM.addressModulus)
    (hoffMax : tlcHashOpArgOff I ≤ solcMaxU64)
    (hlenWord : 4 + tlcHashOpArgOff I + 32 ≤ I.calldata.size)
    (hlenMax : tlcHashOpArgLen I ≤ solcMaxU64)
    (hpay : I.calldata.size < 4 + tlcHashOpArgOff I + 32 + tlcHashOpArgLen I) :
    decodeCalldataWithMode config.abiDecodeMode (hashOperationTransition.params.map Param.name)
      (transitionSignature hashOperationTransition).paramTypes I.calldata = none := by
  show decodeCalldataWithMode DecodeMode.modern ["target", "value", "data", "predecessor", "salt"]
    [addr, uint256, bytesTy, bytes32, bytes32] I.calldata = none
  rw [tlc_enter hhead hsmall]
  have htlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  have haddr := tlc_addr_ok (I := I) (by omega) hclean
  have huint : decodeABIValue? (.elem (.int uint256Int)) (I.calldata.toList.drop 4) 32 =
      some (.int (tlcHashOpValue I), 64) := tlc_uint256_ok (by omega)
  have hoffRead : readNat? (I.calldata.toList.drop 4) 64 = some (tlcHashOpArgOff I) := by
    have h := tlc_readNat htlen 64 (by omega); simpa using h
  have hlenRead : readNat? (I.calldata.toList.drop 4) (tlcHashOpArgOff I) = some (tlcHashOpArgLen I) :=
    tlc_readNat htlen (tlcHashOpArgOff I) (by omega)
  have hpayRead : readBytes? (I.calldata.toList.drop 4) (tlcHashOpArgOff I + 32)
      (tlcHashOpArgLen I) = none := by
    unfold readBytes?
    rw [if_neg (show ¬ (((I.calldata.toList.drop 4).drop (tlcHashOpArgOff I + 32)).take
      (tlcHashOpArgLen I)).length = tlcHashOpArgLen I from by
        rw [List.length_take, List.length_drop, List.length_drop, htlen]; omega)]
  have hbytesval : decodeABIValue? ABIType.bytes (I.calldata.toList.drop 4) (tlcHashOpArgOff I)
      = none := by
    simp only [decodeABIValue?, hlenRead, bind, Option.bind, solcMaxLen_modern,
      if_neg (not_lt.mpr hlenMax), hpayRead]
  have hDAV : decodeABIValues? [addr, uint256, bytesTy, bytes32, bytes32]
      (I.calldata.toList.drop 4) 0 0 160 160 DecodeMode.modern = none := by
    simp only [decodeABIValues?, addr, uint256, bytesTy, isDynamicABIType, staticABIEncodedSize?,
      Bool.false_eq_true, if_false, bind, Option.bind, Nat.add_zero, Nat.zero_add, Nat.reduceAdd,
      reduceIte, haddr, huint, hoffRead, solcMaxLen_modern, if_neg (not_lt.mpr hoffMax), hbytesval]
  rw [hDAV]

end OpenZeppelinBench.TimelockController
