import Benchmarks.WETH9.TransferFromBody

/-!
# WETH9 `transferFrom` shared definitions

ABI-decoded argument words/values/store, the wrapping-`sub` word lemma, ABI decode facts, and the
source⟺EVM storage-slot reconciliations for `balanceOf[src]`, `balanceOf[dst]`,
`allowance[src][msg.sender]`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

namespace Benchmarks.WETH9

/-! ## Argument words, values, store -/

abbrev tfSrcWord (I : ExecutionEnv) : UInt256 := calldataWord I.calldata 4
abbrev tfDstWord (I : ExecutionEnv) : UInt256 := calldataWord I.calldata 36
abbrev tfWadWord (I : ExecutionEnv) : UInt256 := calldataWord I.calldata 68
abbrev tfSrcMasked (I : ExecutionEnv) : UInt256 := UInt256.land solcAddrMask (tfSrcWord I)
abbrev tfDstMasked (I : ExecutionEnv) : UInt256 := UInt256.land solcAddrMask (tfDstWord I)

abbrev tfSrcVal (I : ExecutionEnv) : Value := .address (AccountAddress.ofNat (tfSrcWord I).toNat)
abbrev tfDstVal (I : ExecutionEnv) : Value := .address (AccountAddress.ofNat (tfDstWord I).toNat)
abbrev tfWadVal (I : ExecutionEnv) : Value := .int (Int.ofNat (tfWadWord I).toNat)

abbrev tfStore (I : ExecutionEnv) : Store :=
  (((∅ : Store).insert "src" (tfSrcVal I)).insert "dst" (tfDstVal I)).insert "wad" (tfWadVal I)

/-! ## Wrapping subtraction on store -/

/-- `wordOfInt (a − b) = a ⊖ b` (the wrapping `-=` truncation on store, valid when `b ≤ a`). -/
theorem wordOfInt_sub_words {a b : UInt256} (h : b.toNat ≤ a.toNat) :
    EVM.wordOfInt (Int.ofNat a.toNat - Int.ofNat b.toNat) = UInt256.sub a b := by
  have hcast : (Int.ofNat a.toNat - Int.ofNat b.toNat) = Int.ofNat (a.toNat - b.toNat) :=
    (Int.ofNat_sub h).symm
  rw [hcast, wordOfInt_ofNat_toNat_gen]
  apply u256_inj
  rw [usub_toNat h]
  exact ulit_toNat' _ (lt_of_le_of_lt (Nat.sub_le _ _) a.val.isLt)

/-! ## Canonicity of masked words -/

theorem tfSrcMasked_canonical (I : ExecutionEnv) : (tfSrcMasked I).toNat < EVM.addressModulus := by
  unfold tfSrcMasked; rw [u256_land_comm]; exact solcAddrMask_result_canonical (tfSrcWord I)

theorem tfDstMasked_canonical (I : ExecutionEnv) : (tfDstMasked I).toNat < EVM.addressModulus := by
  unfold tfDstMasked; rw [u256_land_comm]; exact solcAddrMask_result_canonical (tfDstWord I)

/-! ## ABI decode -/

theorem tfDecode_ok {I : ExecutionEnv} (hsz100 : 100 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (transferFromTransition.params.map Param.name)
      (transitionSignature transferFromTransition).paramTypes I.calldata = some (tfStore I) := by
  show decodeCalldataWithMode config.abiDecodeMode ["src", "dst", "wad"] [addr, addr, uint256]
    I.calldata = _
  simpa [tfStore, tfSrcVal, tfDstVal, tfWadVal, tfSrcWord, tfDstWord, tfWadWord, calldataWord]
    using decodeCalldata_legacyAddress_legacyAddress_uint256_ok
      (cd := I.calldata) (x := "src") (y := "dst") (z := "wad") hsz100

theorem tfDecode_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 100) :
    decodeCalldataWithMode config.abiDecodeMode (transferFromTransition.params.map Param.name)
      (transitionSignature transferFromTransition).paramTypes I.calldata = none := by
  show decodeCalldataWithMode config.abiDecodeMode ["src", "dst", "wad"] [addr, addr, uint256]
    I.calldata = none
  simpa using decodeCalldata_legacyAddress_legacyAddress_uint256_none_short
    (cd := I.calldata) (x := "src") (y := "dst") (z := "wad") hsz4 hshort

/-- `allowance[src][msg.sender]` after the debit `-= wad` (the spend-case intermediate map). -/
def tfAllowDebitMap (I : ExecutionEnv) (σ : AccountMap) : AccountMap :=
  sstoreAccountMap I.codeOwner σ (wtfAllowSlot I (tfSrcMasked I))
    (UInt256.sub (solcSlotWord σ I (wtfAllowSlot I (tfSrcMasked I))) (tfWadWord I))

/-! ## Storage-slot reconciliations (source `balanceOfSlot`/`allowanceSlot` ⟺ EVM keccak slots) -/

/-- `balanceOf[src]` source slot = the EVM `keccak(srcMasked ‖ 3)` slot. -/
theorem tfBalSrcSlot_eq (I : ExecutionEnv) :
    balanceOfSlot (.address (AccountAddress.ofNat (tfSrcWord I).toNat)) = wtfBalSlot (tfSrcMasked I) := by
  show mapSlot (keyValueToWord (.address (AccountAddress.ofNat (tfSrcWord I).toNat))) ⟨3⟩
    = solcMappingSlot ⟨3⟩ (tfSrcMasked I)
  unfold mapSlot solcMappingSlot tfSrcMasked
  rw [keyValueToWord_address_ofNat_mask]

/-- `balanceOf[dst]` source slot = the EVM `keccak(dstMasked ‖ 3)` slot. -/
theorem tfBalDstSlot_eq (I : ExecutionEnv) :
    balanceOfSlot (.address (AccountAddress.ofNat (tfDstWord I).toNat)) = wtfBalSlot (tfDstMasked I) := by
  show mapSlot (keyValueToWord (.address (AccountAddress.ofNat (tfDstWord I).toNat))) ⟨3⟩
    = solcMappingSlot ⟨3⟩ (tfDstMasked I)
  unfold mapSlot solcMappingSlot tfDstMasked
  rw [keyValueToWord_address_ofNat_mask]

/-- `allowance[src][msg.sender]` source slot = the EVM nested keccak slot. -/
theorem tfAllowSlot_eq (I : ExecutionEnv) :
    allowanceSlot (.address (AccountAddress.ofNat (tfSrcWord I).toNat)) (.address I.source) =
      wtfAllowSlot I (tfSrcMasked I) := by
  show mapSlot (keyValueToWord (.address I.source))
      (mapSlot (keyValueToWord (.address (AccountAddress.ofNat (tfSrcWord I).toNat))) ⟨4⟩)
    = solcMappingSlot (solcMappingSlot ⟨4⟩ (tfSrcMasked I)) (solcSourceWord I)
  unfold mapSlot solcMappingSlot tfSrcMasked
  rw [keyValueToWord_address_ofNat_mask, keyValueToWord_address]

end Benchmarks.WETH9
