import Reasoning.WordArithmetic
import Reasoning.EVMWord
import Examples.UniswapV2Pair.WordArithmeticSource
import Examples.UniswapV2Pair.ByteArrayWriteMemory
import Examples.UniswapV2Pair.ExternalCalls
import Examples.UniswapV2Pair.ExternalWrappers
import Examples.UniswapV2Pair.GetReserves
import Examples.UniswapV2Pair.MathRoutines
import Examples.UniswapV2Pair.MintFeeRoutines
import Examples.UniswapV2Pair.MintRoutines
import Examples.UniswapV2Pair.MutatorDispatch
import Examples.UniswapV2Pair.Routines
import Examples.UniswapV2Pair.Sync
import Examples.UniswapV2Pair.SyncRuntime
import Examples.UniswapV2Pair.UpdateRoutines
import Reasoning.ExternalCall
import Reasoning.ABIComposite

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace UniswapV2Pair

/-! ## `mint(address)` source slice and wrapper decode -/

/-- The raw ABI word for `mint`'s `to` argument. -/
abbrev mintToWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 4

abbrev mintToMaskedWord (I : ExecutionEnv) : UInt256 :=
  UInt256.land solcAddrMask (mintToWord I)

abbrev mintToValue (I : ExecutionEnv) : Value :=
  .address (AccountAddress.ofNat (mintToWord I).toNat)

abbrev mintToKey (I : ExecutionEnv) : KeyValue :=
  .address (AccountAddress.ofNat (mintToWord I).toNat)

abbrev mintStore (I : ExecutionEnv) : Store :=
  (∅ : Store).insert "to" (mintToValue I)

theorem mintToKey_word_masked (I : ExecutionEnv) :
    keyValueToWord (mintToKey I) = mintToMaskedWord I := by
  unfold mintToKey mintToMaskedWord
  rw [keyValueToWord_address_ofNat_mask]

theorem uniswapDecode_mint_ok {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (mintTransition.params.map Param.name)
      (transitionSignature mintTransition).paramTypes I.calldata = some (mintStore I) := by
  show decodeCalldataWithMode config.abiDecodeMode ["to"] [legacyAddr] I.calldata = _
  simpa [mintStore, mintToValue, mintToWord, calldataWord]
    using decodeCalldata_legacyAddress_ok (cd := I.calldata) (x := "to") hsz36

theorem uniswapDecode_mint_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36) :
    decodeCalldataWithMode config.abiDecodeMode (mintTransition.params.map Param.name)
      (transitionSignature mintTransition).paramTypes I.calldata = none := by
  show decodeCalldataWithMode config.abiDecodeMode ["to"] [legacyAddr] I.calldata = none
  simpa using decodeCalldata_legacyAddress_none_short (cd := I.calldata) (x := "to")
    hsz4 hshort

theorem mintStore_to (I : ExecutionEnv) :
    (mintStore I).get? "to" = some (mintToValue I) := by
  rw [mintStore, store_get_self]

theorem mintStore_balanceOf (I : ExecutionEnv) :
    (mintStore I).get? "balanceOf" = none := by
  rw [mintStore, store_get_ne _ _ (by decide)]
  simp

abbrev feeToSelectorWord : UInt256 := ⟨25067096⟩

abbrev feeToSelectorShifted : UInt256 :=
  UInt256.shiftLeft feeToSelectorWord ⟨224⟩

def feeToSelectorMem (base : ByteArray) : ByteArray :=
  (UInt256.toByteArray feeToSelectorShifted).write 0 base 128 32

def feeToStaticcallMem (base o : ByteArray) : ByteArray :=
  o.write 0 (feeToSelectorMem base) 128
    (min (⟨32⟩ : UInt256) (UInt256.ofNat o.size)).toNat

abbrev feeToStaticcallActiveWords : UInt256 :=
  balanceOfThisStaticcallActiveWords

abbrev mintFeeFactoryWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.land solcAddrMask (solcSlotWordAt ⟨5⟩ σ I)

abbrev mintFeeKLastSlotWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  solcSlotWordAt ⟨11⟩ σ I

theorem feeToSelectorMem_size_of_ge160 {mem : ByteArray} (hmem : 160 ≤ mem.size) :
    (feeToSelectorMem mem).size = mem.size := by
  exact toByteArray_write32_size_of_le mem feeToSelectorShifted 128 mem.size mem.size
    rfl (by omega) (by omega)

theorem feeToSelectorMem_read64_of_ge160 {mem : ByteArray} (hmem : 160 ≤ mem.size)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (feeToSelectorMem mem).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold feeToSelectorMem
  rw [write32_read_below _ _ 128 64 (by rw [toByteArray_size]) (by omega) (by omega)]
  exact hread64

theorem feeToSelectorMem_read128_4_of_ge160 {mem : ByteArray} (hmem : 160 ≤ mem.size) :
    (feeToSelectorMem mem).readWithPadding 128 4 = feeToSelector := by
  unfold feeToSelectorMem
  rw [write32_read_prefix_len _ _ 128 4 (by rw [toByteArray_size])
    (by omega) (by norm_num) (by norm_num) (by norm_num)]
  unfold feeToSelectorShifted feeToSelectorWord feeToSelector selectorBytes
  native_decide

theorem feeToStaticcallMem_size_of_ge160 {mem : ByteArray} (out : ByteArray)
    (hmem : 160 ≤ mem.size) (houtSize : out.size < UInt256.size) :
    (feeToStaticcallMem mem out).size = mem.size := by
  unfold feeToStaticcallMem
  have hlen : (min (⟨32⟩ : UInt256) (UInt256.ofNat out.size)).toNat = min 32 out.size := by
    by_cases hlo : 32 ≤ out.size
    · rw [balanceOfThisStaticcallWriteLen_of_size_ge out hlo houtSize, Nat.min_eq_left hlo]
    · rw [balanceOfThisStaticcallWriteLen_of_size_lt out (by omega) houtSize,
        Nat.min_eq_right (by omega)]
  rw [hlen, byteArray_write_size_of_inBounds _ _ 128 (min 32 out.size)
    (Nat.min_le_right _ _) (by rw [feeToSelectorMem_size_of_ge160 hmem]; omega),
    feeToSelectorMem_size_of_ge160 hmem]

theorem feeToStaticcallMem_read64_of_ge160 {mem : ByteArray} (out : ByteArray)
    (hmem : 160 ≤ mem.size) (houtSize : out.size < UInt256.size)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (feeToStaticcallMem mem out).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold feeToStaticcallMem
  by_cases hlo : 32 ≤ out.size
  · rw [balanceOfThisStaticcallWriteLen_of_size_ge out hlo houtSize,
      write32_read_below _ _ 128 64 hlo
        (by rw [feeToSelectorMem_size_of_ge160 hmem]; omega) (by omega)]
    exact feeToSelectorMem_read64_of_ge160 hmem hread64
  · rw [balanceOfThisStaticcallWriteLen_of_size_lt out (by omega) houtSize]
    by_cases hz : out.size = 0
    · rw [hz, byteArray_write_len_zero]
      exact feeToSelectorMem_read64_of_ge160 hmem hread64
    · rw [write_read_below_gen _ _ 128 out.size 64 hz le_rfl
        (by rw [feeToSelectorMem_size_of_ge160 hmem]; omega) (by omega)]
      exact feeToSelectorMem_read64_of_ge160 hmem hread64

theorem feeToStaticcallMem_read128_of_ge160 {mem : ByteArray} (out : ByteArray)
    (hmem : 160 ≤ mem.size) (houtlo : 32 ≤ out.size) (houtSize : out.size < UInt256.size) :
    (feeToStaticcallMem mem out).readWithPadding 128 32 = out.extract 0 32 := by
  unfold feeToStaticcallMem
  rw [balanceOfThisStaticcallWriteLen_of_size_ge out houtlo houtSize]
  exact write32_read_back out (feeToSelectorMem mem) 128 houtlo
    (by rw [feeToSelectorMem_size_of_ge160 hmem]; omega)


theorem feeToSelectorMem_size_of_rebuiltStaticcallMem
    (self : UInt256) (oPrev o : ByteArray)
    (hprevlo : 32 ≤ oPrev.size) (hprevhi : oPrev.size < UInt256.size)
    (hlo : 32 ≤ o.size) (hhi : o.size < UInt256.size) :
    (feeToSelectorMem (balanceOfThisRebuiltStaticcallMem self oPrev o)).size = 164 := by
  have hsize := balanceOfThisRebuiltStaticcallMem_size_of_size_ge self oPrev o hprevlo hprevhi hlo hhi
  exact (feeToSelectorMem_size_of_ge160 (by rw [hsize]; omega)).trans hsize

theorem feeToSelectorMem_read64_of_rebuiltStaticcallMem
    (self : UInt256) (oPrev o : ByteArray)
    (hprevlo : 32 ≤ oPrev.size) (hprevhi : oPrev.size < UInt256.size)
    (hlo : 32 ≤ o.size) (hhi : o.size < UInt256.size) :
    (feeToSelectorMem (balanceOfThisRebuiltStaticcallMem self oPrev o)).readWithPadding
      64 32 = UInt256.toByteArray ⟨128⟩ := by
  exact feeToSelectorMem_read64_of_ge160
    (by rw [balanceOfThisRebuiltStaticcallMem_size_of_size_ge self oPrev o hprevlo hprevhi hlo hhi]; omega)
    (balanceOfThisRebuiltStaticcallMem_read64_of_size_ge self oPrev o hprevlo hprevhi hlo hhi)

theorem feeToSelectorMem_read128_4_of_rebuiltStaticcallMem
    (self : UInt256) (oPrev o : ByteArray)
    (hprevlo : 32 ≤ oPrev.size) (hprevhi : oPrev.size < UInt256.size)
    (hlo : 32 ≤ o.size) (hhi : o.size < UInt256.size) :
    (feeToSelectorMem (balanceOfThisRebuiltStaticcallMem self oPrev o)).readWithPadding
      128 4 = feeToSelector := by
  exact feeToSelectorMem_read128_4_of_ge160
    (by rw [balanceOfThisRebuiltStaticcallMem_size_of_size_ge self oPrev o hprevlo hprevhi hlo hhi]; omega)

theorem feeToSelectorMem_mload64_of_rebuiltStaticcallMem
    (self : UInt256) (oPrev o : ByteArray)
    (hprevlo : 32 ≤ oPrev.size) (hprevhi : oPrev.size < UInt256.size)
    (hlo : 32 ≤ o.size) (hhi : o.size < UInt256.size) :
    (if (⟨64⟩ : UInt256).toNat ≥
          (feeToSelectorMem (balanceOfThisRebuiltStaticcallMem self oPrev o)).size then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((feeToSelectorMem (balanceOfThisRebuiltStaticcallMem self oPrev o)).readWithPadding
          (⟨64⟩ : UInt256).toNat 32))) =
      ⟨128⟩ := by
  exact mloadFreePtrValue
    (by
      rw [feeToSelectorMem_size_of_rebuiltStaticcallMem self oPrev o hprevlo hprevhi hlo hhi]
      decide)
    (feeToSelectorMem_read64_of_rebuiltStaticcallMem self oPrev o hprevlo hprevhi hlo hhi)

theorem uniswapMintFeeToTypedCall_source_of_mem
    {σ1 σ₀ I} {evm1S : EVM.State} {σ2 : AccountMap}
    {z2 : Bool} {out2 : ByteArray} {A_in2 : Substate} {callGas2 : UInt256}
    {mem : ByteArray}
    (hPost : Eq σ1 evm1S.accountMap)
    (hσ0 : evm1S.σ₀ = σ₀)
    (henv : evm1S.executionEnv = I)
    (hdepth : I.depth.val < 1024)
    (hmem : 160 ≤ mem.size)
    (hΘ :
      ∃ (g'' : UInt256) (A'_evm : Substate),
        (σ2, g'', A'_evm, z2, out2) = Ethereum.EVM.Θ
          σ1 σ₀ A_in2
          (AccountAddress.ofUInt256 (UInt256.ofNat I.codeOwner.val)) I.sender
          (AccountAddress.ofUInt256 (mintFeeFactoryWord σ1 I))
          (toExecute σ1 (AccountAddress.ofUInt256 (mintFeeFactoryWord σ1 I)))
          callGas2 (UInt256.ofNat I.gasPrice) ⟨0⟩ ⟨0⟩
          ((feeToSelectorMem
            mem)
            |>.readWithPadding 128 4)
          (I.depth + 1) I.header I.blobVersionedHashes I.blocks false) :
    ∃ evm2S : EVM.State,
      typedCallViaEVM config evm1S
        (EVM.address (uniswapAddressAtSlot evm1S ⟨5⟩))
        "feeTo" 0 [] (z2, evm2S, out2) false ∧
      Eq σ2 evm2S.accountMap ∧
      evm2S.σ₀ = σ₀ ∧
      evm2S.executionEnv = evm1S.executionEnv := by
  obtain ⟨g'', A'_evm, hΘeq⟩ := hΘ
  let factoryWord := solcSlotWordAt ⟨5⟩ σ1 I
  let factoryClean := UInt256.land solcAddrMask factoryWord
  have hslot : factoryWord = solcSlotWordAt ⟨5⟩ evm1S.accountMap evm1S.executionEnv := by
    simp [factoryWord, hPost, henv]
  have htargetSource :
      AccountAddress.ofUInt256 factoryClean = EVM.address (uniswapAddressAtSlot evm1S ⟨5⟩) := by
    have haddr :
        AccountAddress.ofUInt256 factoryClean = uniswapAddressAtSlot evm1S ⟨5⟩ := by
      simp [factoryClean, factoryWord, hslot, henv, Solm.EVM.storageLoad,
        State.lookupAccount, Account.lookupStorage, uniswapAddressAtSlot, solcSlotWordAt,
          solcSlotWord,
        accountAddress_ofUInt256_eq_ofNat_toNat, u256_land_comm]
    change AccountAddress.ofUInt256 factoryClean =
      EVM.address (uniswapAddressAtSlot evm1S ⟨5⟩)
    rw [haddr]
    symm
    change EVM.uintN 160 (uniswapAddressAtSlot evm1S ⟨5⟩).val =
      uniswapAddressAtSlot evm1S ⟨5⟩
    ext
    simp [EVM.uintN, EVM.twoPow, AccountAddress.size]
  let target : EVM.Address := EVM.address (uniswapAddressAtSlot evm1S ⟨5⟩)
  have hdepthS : evm1S.executionEnv.depth.val < 1024 := by
    simpa [henv] using hdepth
  have hdepthNe : evm1S.executionEnv.depth ≠ 1024 := by
    intro hEq
    rw [hEq] at hdepthS
    exact absurd hdepthS (by decide)
  have hcdE :
      config.externalABI.encode? "feeTo" [] =
        some ((feeToSelectorMem
          mem)
          |>.readWithPadding 128 4) := by
    rw [feeToSelectorMem_read128_4_of_ge160 hmem]
    change uniswapExternalABI.encode? "feeTo" [] = some feeToSelector
    simp [uniswapExternalABI]
  have hΘE :
      (σ2, g'', A'_evm, z2, out2) =
        Ethereum.EVM.Θ evm1S.accountMap evm1S.σ₀ A_in2
          (AccountAddress.ofUInt256 (UInt256.ofNat evm1S.executionEnv.codeOwner))
          evm1S.executionEnv.sender (AccountAddress.ofUInt256 (mintFeeFactoryWord σ1 I))
          (toExecute evm1S.accountMap (AccountAddress.ofUInt256 (mintFeeFactoryWord σ1 I)))
          callGas2 (UInt256.ofNat evm1S.executionEnv.gasPrice) ⟨0⟩ ⟨0⟩
          ((feeToSelectorMem
            mem)
            |>.readWithPadding 128 4)
          (evm1S.executionEnv.depth + 1) evm1S.executionEnv.header
          evm1S.executionEnv.blobVersionedHashes evm1S.executionEnv.blocks false := by
    simpa [← hPost, hσ0, henv] using hΘeq
  have hcallSolm :=
    callCoincides (cfg := config) (evm := evm1S)
      (tgt := target) (targetWord := mintFeeFactoryWord σ1 I)
      (name := "feeTo") (args := []) (σ' := σ2) (A' := A'_evm)
      (A_in := A_in2) (z := z2) (o := out2) (g'' := g'') (callGas := callGas2)
      (mem := feeToSelectorMem mem) (inOff := ⟨128⟩) (inSize := ⟨4⟩)
      (callPerm := false) hdepthNe
      (by simpa [target, mintFeeFactoryWord, factoryClean, factoryWord] using htargetSource.symm)
      hcdE hΘE
  let evm2S : EVM.State :=
    { evm1S with
      accountMap := σ2
      substate := A'_evm }
  refine ⟨evm2S, ?_, ?_, ?_, ?_⟩
  · simpa [evm2S, target] using hcallSolm
  · rfl
  · simp [evm2S, hσ0]
  · simp [evm2S]

theorem uniswapMintFeeToTypedCall_source
    {σ1 σ₀ I} {evm1S : EVM.State} {σ2 : AccountMap}
    {z2 : Bool} {out2 : ByteArray} {A_in2 : Substate} {callGas2 : UInt256}
    {oPrev o : ByteArray}
    (hPost : Eq σ1 evm1S.accountMap)
    (hσ0 : evm1S.σ₀ = σ₀)
    (henv : evm1S.executionEnv = I)
    (hdepth : I.depth.val < 1024)
    (hprevlo : 32 ≤ oPrev.size) (hprevhi : oPrev.size < UInt256.size)
    (hlo : 32 ≤ o.size) (hhi : o.size < UInt256.size)
    (hΘ :
      ∃ (g'' : UInt256) (A'_evm : Substate),
        (σ2, g'', A'_evm, z2, out2) = Ethereum.EVM.Θ
          σ1 σ₀ A_in2
          (AccountAddress.ofUInt256 (UInt256.ofNat I.codeOwner.val)) I.sender
          (AccountAddress.ofUInt256 (mintFeeFactoryWord σ1 I))
          (toExecute σ1 (AccountAddress.ofUInt256 (mintFeeFactoryWord σ1 I)))
          callGas2 (UInt256.ofNat I.gasPrice) ⟨0⟩ ⟨0⟩
          ((feeToSelectorMem
            (balanceOfThisRebuiltStaticcallMem (UInt256.ofNat I.codeOwner.val) oPrev o))
            |>.readWithPadding 128 4)
          (I.depth + 1) I.header I.blobVersionedHashes I.blocks false) :
    ∃ evm2S : EVM.State,
      typedCallViaEVM config evm1S
        (EVM.address (uniswapAddressAtSlot evm1S ⟨5⟩))
        "feeTo" 0 [] (z2, evm2S, out2) false ∧
      Eq σ2 evm2S.accountMap ∧
      evm2S.σ₀ = σ₀ ∧
      evm2S.executionEnv = evm1S.executionEnv := by
  exact uniswapMintFeeToTypedCall_source_of_mem hPost hσ0 henv
    hdepth (by
      rw [balanceOfThisRebuiltStaticcallMem_size_of_size_ge
        (UInt256.ofNat I.codeOwner.val) oPrev o hprevlo hprevhi hlo hhi]
      omega) hΘ

theorem feeToStaticcallMem_size_of_size_ge
    (self : UInt256) (oPrev o outFee : ByteArray)
    (hprevlo : 32 ≤ oPrev.size) (hprevhi : oPrev.size < UInt256.size)
    (hlo : 32 ≤ o.size) (hhi : o.size < UInt256.size)
    (houtlo : 32 ≤ outFee.size) (houthi : outFee.size < UInt256.size) :
    (feeToStaticcallMem (balanceOfThisRebuiltStaticcallMem self oPrev o) outFee).size =
      164 := by
  have hsize := balanceOfThisRebuiltStaticcallMem_size_of_size_ge self oPrev o hprevlo hprevhi hlo hhi
  exact (feeToStaticcallMem_size_of_ge160 outFee (by rw [hsize]; omega) houthi).trans hsize

theorem feeToStaticcallMem_read64_of_size_ge
    (self : UInt256) (oPrev o outFee : ByteArray)
    (hprevlo : 32 ≤ oPrev.size) (hprevhi : oPrev.size < UInt256.size)
    (hlo : 32 ≤ o.size) (hhi : o.size < UInt256.size)
    (houtlo : 32 ≤ outFee.size) (houthi : outFee.size < UInt256.size) :
    ByteArray.readWithPadding
      (feeToStaticcallMem (balanceOfThisRebuiltStaticcallMem self oPrev o) outFee) 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  exact feeToStaticcallMem_read64_of_ge160 outFee
    (by rw [balanceOfThisRebuiltStaticcallMem_size_of_size_ge self oPrev o hprevlo hprevhi hlo hhi]; omega) houthi
    (balanceOfThisRebuiltStaticcallMem_read64_of_size_ge self oPrev o hprevlo hprevhi hlo hhi)

theorem feeToStaticcallMem_mload64_of_size_ge
    (self : UInt256) (oPrev o outFee : ByteArray)
    (hprevlo : 32 ≤ oPrev.size) (hprevhi : oPrev.size < UInt256.size)
    (hlo : 32 ≤ o.size) (hhi : o.size < UInt256.size)
    (houtlo : 32 ≤ outFee.size) (houthi : outFee.size < UInt256.size) :
    (if (⟨64⟩ : UInt256).toNat ≥
          (feeToStaticcallMem (balanceOfThisRebuiltStaticcallMem self oPrev o) outFee).size then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        (ByteArray.readWithPadding
          (feeToStaticcallMem (balanceOfThisRebuiltStaticcallMem self oPrev o) outFee)
          (⟨64⟩ : UInt256).toNat 32))) =
      ⟨128⟩ :=
  mloadFreePtrValue
    (by
      rw [feeToStaticcallMem_size_of_size_ge self oPrev o outFee hprevlo hprevhi hlo hhi
        houtlo houthi]
      decide)
    (feeToStaticcallMem_read64_of_size_ge self oPrev o outFee hprevlo hprevhi hlo hhi
      houtlo houthi)

theorem feeToStaticcallMem_size_of_size_lt
    (self : UInt256) (oPrev o outFee : ByteArray)
    (hprevlo : 32 ≤ oPrev.size) (hprevhi : oPrev.size < UInt256.size)
    (hlo : 32 ≤ o.size) (hhi : o.size < UInt256.size)
    (houtshort : outFee.size < 32) (houthi : outFee.size < UInt256.size) :
    (feeToStaticcallMem (balanceOfThisRebuiltStaticcallMem self oPrev o) outFee).size =
      164 := by
  have hsize := balanceOfThisRebuiltStaticcallMem_size_of_size_ge self oPrev o hprevlo hprevhi hlo hhi
  exact (feeToStaticcallMem_size_of_ge160 outFee (by rw [hsize]; omega) houthi).trans hsize

theorem feeToStaticcallMem_read64_of_size_lt
    (self : UInt256) (oPrev o outFee : ByteArray)
    (hprevlo : 32 ≤ oPrev.size) (hprevhi : oPrev.size < UInt256.size)
    (hlo : 32 ≤ o.size) (hhi : o.size < UInt256.size)
    (houtshort : outFee.size < 32) (houthi : outFee.size < UInt256.size) :
    ByteArray.readWithPadding
      (feeToStaticcallMem (balanceOfThisRebuiltStaticcallMem self oPrev o) outFee) 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  exact feeToStaticcallMem_read64_of_ge160 outFee
    (by rw [balanceOfThisRebuiltStaticcallMem_size_of_size_ge self oPrev o hprevlo hprevhi hlo hhi]; omega) houthi
    (balanceOfThisRebuiltStaticcallMem_read64_of_size_ge self oPrev o hprevlo hprevhi hlo hhi)

theorem feeToStaticcallMem_mload64_of_size_lt
    (self : UInt256) (oPrev o outFee : ByteArray)
    (hprevlo : 32 ≤ oPrev.size) (hprevhi : oPrev.size < UInt256.size)
    (hlo : 32 ≤ o.size) (hhi : o.size < UInt256.size)
    (houtshort : outFee.size < 32) (houthi : outFee.size < UInt256.size) :
    (if (⟨64⟩ : UInt256).toNat ≥
          (feeToStaticcallMem (balanceOfThisRebuiltStaticcallMem self oPrev o) outFee).size then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        (ByteArray.readWithPadding
          (feeToStaticcallMem (balanceOfThisRebuiltStaticcallMem self oPrev o) outFee)
          (⟨64⟩ : UInt256).toNat 32))) =
      ⟨128⟩ :=
  mloadFreePtrValue
    (by
      rw [feeToStaticcallMem_size_of_size_lt self oPrev o outFee hprevlo hprevhi hlo hhi
        houtshort houthi]
      decide)
    (feeToStaticcallMem_read64_of_size_lt self oPrev o outFee hprevlo hprevhi hlo hhi
      houtshort houthi)

theorem feeToStaticcallMem_read128_of_size_ge
    (self : UInt256) (oPrev o outFee : ByteArray)
    (hprevlo : 32 ≤ oPrev.size) (hprevhi : oPrev.size < UInt256.size)
    (hlo : 32 ≤ o.size) (hhi : o.size < UInt256.size)
    (houtlo : 32 ≤ outFee.size) (houthi : outFee.size < UInt256.size) :
    ByteArray.readWithPadding
      (feeToStaticcallMem (balanceOfThisRebuiltStaticcallMem self oPrev o) outFee) 128 32 =
      outFee.extract 0 32 := by
  exact feeToStaticcallMem_read128_of_ge160 outFee
    (by rw [balanceOfThisRebuiltStaticcallMem_size_of_size_ge self oPrev o hprevlo hprevhi hlo hhi]; omega) houtlo houthi

theorem feeToStaticcallMem_mload128_of_size_ge
    (self : UInt256) (oPrev o outFee : ByteArray)
    (hprevlo : 32 ≤ oPrev.size) (hprevhi : oPrev.size < UInt256.size)
    (hlo : 32 ≤ o.size) (hhi : o.size < UInt256.size)
    (houtlo : 32 ≤ outFee.size) (houthi : outFee.size < UInt256.size) :
    (if (⟨128⟩ : UInt256).toNat ≥
          (feeToStaticcallMem (balanceOfThisRebuiltStaticcallMem self oPrev o) outFee).size then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        (ByteArray.readWithPadding
          (feeToStaticcallMem (balanceOfThisRebuiltStaticcallMem self oPrev o) outFee)
          (⟨128⟩ : UInt256).toNat 32))) =
      UInt256.ofNat (fromByteArrayBigEndian (outFee.extract 0 32)) := by
  rw [if_neg]
  · rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide,
      feeToStaticcallMem_read128_of_size_ge self oPrev o outFee hprevlo hprevhi hlo hhi
        houtlo houthi]
  · rw [feeToStaticcallMem_size_of_size_ge self oPrev o outFee hprevlo hprevhi hlo hhi
      houtlo houthi]
    decide

theorem mintFeeFactoryGuardFalse_of_noCode {σ : AccountMap}
    {evm : EVM.State} {I : ExecutionEnv} {reserve0 reserve1 : UInt256}
    (hPost : Eq σ evm.accountMap)
    (henv : evm.executionEnv = I)
    (hfactoryNoCode : extCodeSizeWord σ (mintFeeFactoryWord σ I) = ⟨0⟩) :
    evalExpr? config (mintFeeCallFrame reserve0 reserve1) evm
      (.binary .gt (.extCodeSize (.storage factoryRef)) (.intLit 0)) =
        .ok (.bool false) := by
  let factoryWordS := solcSlotWordAt ⟨5⟩ σ I
  let factoryWordE := solcSlotWordAt ⟨5⟩ evm.accountMap evm.executionEnv
  have hslot : factoryWordS = factoryWordE := by
    simp [factoryWordS, factoryWordE, hPost, henv]
  have hcodeEvm :
      extCodeSizeWord evm.accountMap (UInt256.land solcAddrMask factoryWordE) =
        ⟨0⟩ := by
    rw [← hslot, ← hPost]
    simpa [factoryWordS, mintFeeFactoryWord] using hfactoryNoCode
  have hstorage :
      evalExpr? config (mintFeeCallFrame reserve0 reserve1) evm (.storage factoryRef) =
        .ok (.address (uniswapAddressAtSlot evm ⟨5⟩)) := by
    exact evalExpr_mintFee_factory evm reserve0 reserve1
  have hcodeSource :
      (evm.lookupAccount (uniswapAddressAtSlot evm ⟨5⟩)).option (⟨0⟩ : UInt256)
          (fun acc => EVM.Word.ofNat acc.code.size) =
        ⟨0⟩ := by
    have hcodeEvmRight :
        extCodeSizeWord evm.accountMap (UInt256.land factoryWordE solcAddrMask) =
          ⟨0⟩ := by
      simpa [u256_land_comm] using hcodeEvm
    simpa [State.lookupAccount, Solm.EVM.storageLoad, Account.lookupStorage,
      uniswapAddressAtSlot, extCodeSizeWord, solcSlotWordAt, solcSlotWord, factoryWordE,
      accountAddress_ofUInt256_eq_ofNat_toNat] using hcodeEvmRight
  have hcodeSourceWord :
      EVM.Word.ofNat
          ((evm.lookupAccount (uniswapAddressAtSlot evm ⟨5⟩)).option 0
            (fun acc => acc.code.size)) =
        ⟨0⟩ := by
    cases hacc : evm.lookupAccount (uniswapAddressAtSlot evm ⟨5⟩) with
    | none =>
        exact UInt256_ofNat_0
    | some acc =>
        simpa [hacc, Option.option] using hcodeSource
  change
    evalExpr? config (mintFeeCallFrame reserve0 reserve1) evm
      (.binary .gt (.extCodeSize (.storage factoryRef)) (.intLit 0)) =
        .ok (.bool false)
  simp [evalExpr?, hstorage, EvalResult.bind, bind, pure, evalBinaryOp?, hcodeSourceWord]

theorem mintFeeFactoryGuardTrue_of_code {σ : AccountMap}
    {evm : EVM.State} {I : ExecutionEnv} {reserve0 reserve1 : UInt256}
    (hPost : Eq σ evm.accountMap)
    (henv : evm.executionEnv = I)
    (hfactoryCode : extCodeSizeWord σ (mintFeeFactoryWord σ I) ≠ ⟨0⟩) :
    evalExpr? config (mintFeeCallFrame reserve0 reserve1) evm
      (.binary .gt (.extCodeSize (.storage factoryRef)) (.intLit 0)) =
        .ok (.bool true) := by
  let factoryWordS := solcSlotWordAt ⟨5⟩ σ I
  let factoryWordE := solcSlotWordAt ⟨5⟩ evm.accountMap evm.executionEnv
  have hslot : factoryWordS = factoryWordE := by
    simp [factoryWordS, factoryWordE, hPost, henv]
  have hcodeEvm :
      extCodeSizeWord evm.accountMap (UInt256.land solcAddrMask factoryWordE) ≠
        ⟨0⟩ := by
    have hcodeS :
        extCodeSizeWord σ (UInt256.land solcAddrMask factoryWordS) ≠ ⟨0⟩ := by
      simpa [factoryWordS, mintFeeFactoryWord] using hfactoryCode
    intro hzero
    apply hcodeS
    rw [← hslot, ← hPost] at hzero
    exact hzero
  have hstorage :
      evalExpr? config (mintFeeCallFrame reserve0 reserve1) evm (.storage factoryRef) =
        .ok (.address (uniswapAddressAtSlot evm ⟨5⟩)) := by
    exact evalExpr_mintFee_factory evm reserve0 reserve1
  have hcodeSource :
      (evm.lookupAccount (uniswapAddressAtSlot evm ⟨5⟩)).option (⟨0⟩ : UInt256)
          (fun acc => EVM.Word.ofNat acc.code.size) ≠
        ⟨0⟩ := by
    have hcodeEvmRight :
        extCodeSizeWord evm.accountMap (UInt256.land factoryWordE solcAddrMask) ≠
          ⟨0⟩ := by
      simpa [u256_land_comm] using hcodeEvm
    intro hzero
    apply hcodeEvmRight
    simpa [State.lookupAccount, Solm.EVM.storageLoad, Account.lookupStorage,
      uniswapAddressAtSlot, extCodeSizeWord, solcSlotWordAt, solcSlotWord, factoryWordE,
      accountAddress_ofUInt256_eq_ofNat_toNat] using hzero
  have hcodeSourceWord :
      EVM.Word.ofNat
          ((evm.lookupAccount (uniswapAddressAtSlot evm ⟨5⟩)).option 0
            (fun acc => acc.code.size)) ≠
        ⟨0⟩ := by
    cases hacc : evm.lookupAccount (uniswapAddressAtSlot evm ⟨5⟩) with
    | none =>
        exact False.elim (hcodeSource (by simp [hacc, Option.option]))
    | some acc =>
        simpa [hacc, Option.option] using hcodeSource
  have hpositive :
      0 <
        (EVM.Word.ofNat
          ((evm.lookupAccount (uniswapAddressAtSlot evm ⟨5⟩)).option 0
            (fun acc => acc.code.size))).toNat := by
    exact Nat.pos_of_ne_zero (by
      intro hzeroNat
      apply hcodeSourceWord
      apply u256_inj
      simpa using hzeroNat)
  change
    evalExpr? config (mintFeeCallFrame reserve0 reserve1) evm
      (.binary .gt (.extCodeSize (.storage factoryRef)) (.intLit 0)) =
        .ok (.bool true)
  simp [evalExpr?, hstorage, EvalResult.bind, bind, pure, evalBinaryOp?]
  exact hpositive

theorem uniswapFeeToDecode_none_short {returndata : ByteArray}
    (hshort : returndata.size < 32) :
    config.externalABI.decode? "feeTo" returndata = none := by
  simpa [config, uniswapExternalABI, ExternalCallABI.decode?, addr, abiAddress] using
    (Reasoning.Theory.decodeReturnValue_legacyAddress_none_short hshort)

theorem uniswapFeeToDecode_ok {returndata : ByteArray}
    (hlo : 32 ≤ returndata.size) :
    config.externalABI.decode? "feeTo" returndata =
      some [.address (AccountAddress.ofNat
        (fromByteArrayBigEndian (returndata.extract 0 32)))] := by
  simpa [config, uniswapExternalABI, ExternalCallABI.decode?, addr, abiAddress] using
    (Reasoning.Theory.decodeReturnValue_legacyAddress_ok hlo)


theorem mintFeeKLastWord_eq_slot
    {σ : AccountMap} {evm : EVM.State} {I : ExecutionEnv}
    (hPost : Eq σ evm.accountMap) (henv : evm.executionEnv = I) :
    mintFeeKLastWord evm = mintFeeKLastSlotWord σ I := by
  simpa [mintFeeKLastWord, mintFeeKLastSlotWord, solcSlotWordAt, solcSlotWord, Solm.EVM.storageLoad,
    State.lookupAccount, Account.lookupStorage, henv, hPost]

theorem mintFunctionTotalSupplyWord_eq_slot
    {σ : AccountMap} {evm : EVM.State} {I : ExecutionEnv}
    (hPost : Eq σ evm.accountMap) (henv : evm.executionEnv = I) :
    mintFunctionTotalSupplyWord evm = solcSlotWordAt ⟨0⟩ σ I := by
  simpa [mintFunctionTotalSupplyWord, solcSlotWordAt, solcSlotWord, Solm.EVM.storageLoad,
    State.lookupAccount, Account.lookupStorage, henv, hPost]


/-! ## EVM wrapper prefix -/

/-- The optimized external wrapper for `mint(address)` masks legacy-address calldata and jumps to
    the external mint routine at pc 3283. -/
theorem uniswapMintX_decoded_masked {σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hreach : ∃ k C, RD uniswapV2PairBytecode I g
      (initState σ σ₀ g A I) ⟨1041⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C) :
    ∃ k C, RD uniswapV2PairBytecode I g (initState σ σ₀ g A I) ⟨3283⟩
      [mintToMaskedWord I, ⟨861⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C := by
  obtain ⟨_, _, rd1063⟩ := RD.uniswapOneAddressExternalLenOk
    (entry := ⟨1041⟩) (ret := ⟨861⟩) (routine := ⟨3283⟩) hreach
    uniswap_one_address_external_entry_wf (by jump_dest) hsz36 hsize
  obtain ⟨_, _, rd3283⟩ := RD.uniswapOneAddressExternalMaskAndJumpMasked
    (entry := ⟨1041⟩) (ret := ⟨861⟩) (routine := ⟨3283⟩) (R := [sel])
    rd1063 uniswap_one_address_external_entry_wf (by jump_dest)
    (by simp only [List.length_singleton]; omega)
  exact ⟨_, _, by simpa [mintToWord, mintToMaskedWord] using rd3283⟩

/-- Short-calldata path for `mint(address)` from the dispatcher body entry. -/
theorem uniswapMintX_shortarg {σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 36)
    (hreach : ∃ k C, RD uniswapV2PairBytecode I g
      (initState σ σ₀ g A I) ⟨1041⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C) :
    RDrev uniswapV2PairBytecode g (initState σ σ₀ g A I) := by
  exact RD.uniswapOneAddressExternalShort
    (entry := ⟨1041⟩) (ret := ⟨861⟩) (routine := ⟨3283⟩)
    hreach uniswap_one_address_external_entry_wf hsz4 hsize hshort

/-- After the external wrapper has decoded `to`, `mint(address)` reverts when the Uniswap lock is
already held. -/
theorem uniswapMintX_locked {σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hlocked :
      (σ.get? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.getD ⟨12⟩ ⟨0⟩)) ≠
        ⟨1⟩)
    (hdecoded : ∃ k C, RD uniswapV2PairBytecode I g
      (initState σ σ₀ g A I) ⟨3283⟩
      [mintToMaskedWord I, ⟨861⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C) :
    RDrev uniswapV2PairBytecode g (initState σ σ₀ g A I) := by
  obtain ⟨_, _, rd3283⟩ := hdecoded
  have rd3286 := evm_run rd3283 with [jumpdest, push1 ⟨0⟩]
  exact RD.uniswapLockEnterBodyLocked
    (okPc := ⟨3360⟩) (R := [⟨0⟩, mintToMaskedWord I, ⟨861⟩, sel])
    rd3286 uniswap_lock_enter_body_guard_wf uniswap_lock_body_revert_tail_wf hlocked
    (by simp only [List.length_cons, List.length_nil]; omega)

/-- After the external wrapper has decoded `to`, `mint(address)` successfully enters the
Uniswap lock when it is not already held. -/
theorem uniswapMintX_lockEntered {σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hperm : I.perm = true)
    (hunlocked :
      (σ.get? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.getD ⟨12⟩ ⟨0⟩)) =
        ⟨1⟩)
    (hdecoded : ∃ k C, RD uniswapV2PairBytecode I g
      (initState σ σ₀ g A I) ⟨3283⟩
      [mintToMaskedWord I, ⟨861⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C) :
    ∃ k C, RD uniswapV2PairBytecode I g (initState σ σ₀ g A I) ⟨3368⟩
      [⟨0⟩, ⟨0⟩, mintToMaskedWord I, ⟨861⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) k C := by
  obtain ⟨_, _, rd3283⟩ := hdecoded
  have rd3286 := evm_run rd3283 with [jumpdest, push1 ⟨0⟩]
  obtain ⟨_, _, rd3368⟩ := RD.uniswapLockEnterBodyOk
    (pc := ⟨3286⟩) (okPc := ⟨3360⟩)
    (R := [⟨0⟩, mintToMaskedWord I, ⟨861⟩, sel])
    rd3286 uniswap_lock_enter_body_ok_wf hperm hunlocked (by jump_dest)
      (by simp only [List.length_cons, List.length_nil]; omega)
  exact ⟨_, _, by simpa using rd3368⟩

/-- In a static call, `mint(address)` halts at the lock-entry `SSTORE`. -/
theorem uniswapMintX_lockEnteredStatic {σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hperm : I.perm = false)
    (hunlocked :
      (σ.get? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.getD ⟨12⟩ ⟨0⟩)) =
        ⟨1⟩)
    (hdecoded : ∃ k C, RD uniswapV2PairBytecode I g
      (initState σ σ₀ g A I) ⟨3283⟩
      [mintToMaskedWord I, ⟨861⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C) :
    RDstatic uniswapV2PairBytecode g (initState σ σ₀ g A I) := by
  obtain ⟨_, _, rd3283⟩ := hdecoded
  have rd3286 := evm_run rd3283 with [jumpdest, push1 ⟨0⟩]
  exact RD.uniswapLockEnterBodyOkStatic
    (pc := ⟨3286⟩) (okPc := ⟨3360⟩)
    (R := [⟨0⟩, mintToMaskedWord I, ⟨861⟩, sel])
    rd3286 uniswap_lock_enter_body_ok_wf hperm hunlocked (by jump_dest)
      (by simp only [List.length_cons, List.length_nil]; omega)

theorem uniswapMintBodyReverts_locked (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hlocked : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨12⟩ ≠ ⟨1⟩) :
    ExecTransitionBody config contract evm (mintStore I) mintTransition.body .reverted := by
  have hlock :=
    uniswapLockEnterLockedRevert evm (mintStore I) hwv (by simp [mintStore]) hlocked
  exact ExecFuncBody.execBlockRevert (by
    simpa [mintTransition, List.append_assoc] using
      (execBlock_append_term hlock (by intro f e h; cases h)))

theorem uniswapMintBodyStatic (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hunlocked : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨12⟩ = ⟨1⟩)
    (hperm : evm.executionEnv.perm = false) :
    ExecTransitionBody config contract evm (mintStore I) mintTransition.body
      .staticViolation := by
  have hlock := uniswapLockEnterStatic evm (mintStore I) hwv (by simp [mintStore]) hunlocked hperm
  exact ExecFuncBody.execBlockStatic (by
    simpa [mintTransition, List.append_assoc] using
      (execBlock_append_term hlock (by intro f e h; cases h)))

theorem uniswapMintLockEnterPrefix (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hunlocked : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨12⟩ = ⟨1⟩) :
    ExecBlock config { contract := contract, locals := mintStore I } evm lockEnter
      (.ok { contract := contract, locals := mintStore I } (uniswapLockEnteredState evm)) := by
  exact uniswapLockEnterPrefix evm (mintStore I) hwv (by simp [mintStore]) hunlocked

theorem uniswapMintLockExitSuffix (evm : EVM.State) (I : ExecutionEnv) :
    ExecBlock config { contract := contract, locals := mintStore I } evm lockExit
      (.ok { contract := contract, locals := mintStore I } (uniswapLockExitedState evm)) := by
  exact uniswapLockExitSuffix evm (mintStore I) (by simp [mintStore])

abbrev mintReserveStore (evm : EVM.State) (I : ExecutionEnv) : Store :=
  ((mintStore I).insert "_reserve0" (.int (Int.ofNat (uniswapReserve0Word evm).toNat))).insert
    "_reserve1" (.int (Int.ofNat (uniswapReserve1Word evm).toNat))

theorem mintReserveStore_reserve0 (evm : EVM.State) (I : ExecutionEnv) :
    (mintReserveStore evm I).get? "_reserve0" =
      some (.int (Int.ofNat (uniswapReserve0Word evm).toNat)) := by
  rw [mintReserveStore, store_get_ne _ _ (by decide), store_get_self]

theorem mintReserveStore_reserve1 (evm : EVM.State) (I : ExecutionEnv) :
    (mintReserveStore evm I).get? "_reserve1" =
      some (.int (Int.ofNat (uniswapReserve1Word evm).toNat)) := by
  rw [mintReserveStore, store_get_self]

theorem mintReserveStore_to (evm : EVM.State) (I : ExecutionEnv) :
    (mintReserveStore evm I).get? "to" = some (mintToValue I) := by
  rw [mintReserveStore, store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
    mintStore_to]

theorem mintToken0GuardFalse_initState_of_noCode
    {σ σ₀ A I} {g : Sat256}
    (htoken0NoCode :
      extCodeSizeWord (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩)
        (UInt256.land solcAddrMask
          (solcSlotWordAt ⟨6⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I)) =
        ⟨0⟩) :
    evalExpr? config
        { contract := contract,
          locals :=
            mintReserveStore
              (uniswapLockEnteredState (initState σ σ₀ g A I)) I }
        (uniswapLockEnteredState (initState σ σ₀ g A I))
        (.binary .gt (.extCodeSize (.storage token0Ref)) (.intLit 0)) =
      .ok (.bool false) := by
  have hguard := syncToken0GuardFalse_initState_of_noCode
    (σ₀ := σ₀) (A := A) (I := I) (g := g)
    htoken0NoCode
  let evmL := uniswapLockEnteredState (initState σ σ₀ g A I)
  have hresolve :
      resolveStorageRef? config
          { contract := contract, locals := mintReserveStore evmL I } evmL token0Ref =
        resolveStorageRef? config { contract := contract, locals := ∅ } evmL token0Ref := by
    simp [resolveStorageRef?, evalStorageRef, mintReserveStore, mintStore, token0Ref]
  unfold syncToken0GuardFalse at hguard
  simp only [evalExpr?, EvalResult.bind, bind, pure] at hguard ⊢
  rw [hresolve]
  exact hguard

theorem mintToken0GuardTrue_initState_of_code
    {σ σ₀ A I} {g : Sat256}
    (htoken0Code :
      extCodeSizeWord (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩)
        (UInt256.land solcAddrMask
          (solcSlotWordAt ⟨6⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I)) ≠
        ⟨0⟩) :
    evalExpr? config
        { contract := contract,
          locals :=
            mintReserveStore
              (uniswapLockEnteredState (initState σ σ₀ g A I)) I }
        (uniswapLockEnteredState (initState σ σ₀ g A I))
        (.binary .gt (.extCodeSize (.storage token0Ref)) (.intLit 0)) =
      .ok (.bool true) := by
  let σLockS := sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩
  let token0WordS := solcSlotWordAt ⟨6⟩ σLockS I
  have hcodeSolm :
      extCodeSizeWord σLockS (UInt256.land solcAddrMask token0WordS) ≠ ⟨0⟩ := by
    simpa [σLockS, token0WordS] using htoken0Code
  let evmS := initState σ σ₀ g A I
  let evmL := uniswapLockEnteredState evmS
  have hstorage :
      evalExpr? config { contract := contract, locals := mintReserveStore evmL I } evmL
        (.storage token0Ref) = .ok (.address (uniswapAddressAtSlot evmL ⟨6⟩)) := by
    exact evalExpr_uniswap_storage_address evmL (mintReserveStore evmL I)
      (er := { base := "token0", steps := [] }) (slot := ⟨6⟩)
      (by simp [mintReserveStore, mintStore, token0Ref])
      (by simp [evalStorageRef, evalStorageRefSteps, token0Ref, EvalResult.bind, pure, bind])
      (by decide) (by rfl)
  have hcodeSource :
      (evmL.lookupAccount (uniswapAddressAtSlot evmL ⟨6⟩)).option (⟨0⟩ : UInt256)
          (fun acc => EVM.Word.ofNat acc.code.size) ≠
        ⟨0⟩ := by
    have hcodeSolmRight :
        extCodeSizeWord σLockS (UInt256.land token0WordS solcAddrMask) ≠ ⟨0⟩ := by
      simpa [u256_land_comm] using hcodeSolm
    intro hzero
    apply hcodeSolmRight
    simpa [evmL, evmS, uniswapLockEnteredState, uniswapUnlockedState, initState,
      storageStore_accountMap, storageStore_executionEnv, State.lookupAccount, Solm.EVM.storageLoad,
      Account.lookupStorage, uniswapAddressAtSlot, extCodeSizeWord, solcSlotWordAt, solcSlotWord,
        σLockS,
      token0WordS, accountAddress_ofUInt256_eq_ofNat_toNat] using hzero
  have hcodeSourceWord :
      EVM.Word.ofNat
          ((evmL.lookupAccount (uniswapAddressAtSlot evmL ⟨6⟩)).option 0
            (fun acc => acc.code.size)) ≠
        ⟨0⟩ := by
    intro hzero
    apply hcodeSource
    cases hacc : evmL.lookupAccount (uniswapAddressAtSlot evmL ⟨6⟩) with
    | none =>
        simp [Option.option]
    | some acc =>
        simpa [hacc, Option.option] using hzero
  have hcodeSourceWordPos :
      0 <
        (EVM.Word.ofNat
          ((evmL.lookupAccount (uniswapAddressAtSlot evmL ⟨6⟩)).option 0
            (fun acc => acc.code.size))).toNat := by
    exact Nat.pos_of_ne_zero (by
      intro hzero
      exact hcodeSourceWord (uint256_toNat_eq_zero hzero))
  change
    evalExpr? config { contract := contract, locals := mintReserveStore evmL I } evmL
      (.binary .gt (.extCodeSize (.storage token0Ref)) (.intLit 0)) =
        .ok (.bool true)
  simp [evalExpr?, hstorage, EvalResult.bind, bind, pure, evalBinaryOp?, hcodeSourceWordPos]

theorem mintToken1GuardFalse_of_noCode {σ : AccountMap}
    {evm0 reserveEvm : EVM.State} {I : ExecutionEnv} {balance0 : Value}
    (hPost : Eq σ evm0.accountMap)
    (henv : evm0.executionEnv = I)
    (htoken1NoCode :
      extCodeSizeWord σ (UInt256.land solcAddrMask (solcSlotWordAt ⟨7⟩ σ I)) =
        ⟨0⟩) :
    evalExpr? config
      { contract := contract, locals := (mintReserveStore reserveEvm I).insert "balance0" balance0 }
      evm0 (.binary .gt (.extCodeSize (.storage token1Ref)) (.intLit 0)) =
        .ok (.bool false) := by
  let token1WordS := solcSlotWordAt ⟨7⟩ σ I
  let token1WordE := solcSlotWordAt ⟨7⟩ evm0.accountMap evm0.executionEnv
  have hslot : token1WordS = token1WordE := by
    simp [token1WordS, token1WordE, hPost, henv]
  have hcodeEvm :
      extCodeSizeWord evm0.accountMap (UInt256.land solcAddrMask token1WordE) =
        ⟨0⟩ := by
    rw [← hslot, ← hPost]
    simpa [token1WordS] using htoken1NoCode
  have hstorage :
      evalExpr? config
        { contract := contract,
          locals := (mintReserveStore reserveEvm I).insert "balance0" balance0 }
        evm0 (.storage token1Ref) = .ok (.address (uniswapAddressAtSlot evm0 ⟨7⟩)) := by
    exact evalExpr_uniswap_storage_address evm0
      ((mintReserveStore reserveEvm I).insert "balance0" balance0)
      (er := { base := "token1", steps := [] }) (slot := ⟨7⟩)
      (by simp [mintReserveStore, mintStore, token1Ref])
      (by simp [evalStorageRef, evalStorageRefSteps, token1Ref, EvalResult.bind, pure, bind])
      (by decide) (by rfl)
  have hcodeSource :
      (evm0.lookupAccount (uniswapAddressAtSlot evm0 ⟨7⟩)).option (⟨0⟩ : UInt256)
          (fun acc => EVM.Word.ofNat acc.code.size) =
        ⟨0⟩ := by
    have hcodeEvmRight :
        extCodeSizeWord evm0.accountMap (UInt256.land token1WordE solcAddrMask) =
          ⟨0⟩ := by
      simpa [u256_land_comm] using hcodeEvm
    simpa [State.lookupAccount, Solm.EVM.storageLoad, Account.lookupStorage,
      uniswapAddressAtSlot, extCodeSizeWord, solcSlotWordAt, solcSlotWord, token1WordE,
      accountAddress_ofUInt256_eq_ofNat_toNat] using hcodeEvmRight
  have hcodeSourceWord :
      EVM.Word.ofNat
          ((evm0.lookupAccount (uniswapAddressAtSlot evm0 ⟨7⟩)).option 0
            (fun acc => acc.code.size)) =
        ⟨0⟩ := by
    cases hacc : evm0.lookupAccount (uniswapAddressAtSlot evm0 ⟨7⟩) with
    | none =>
        exact UInt256_ofNat_0
    | some acc =>
        simpa [hacc, Option.option] using hcodeSource
  change
    evalExpr? config
      { contract := contract, locals := (mintReserveStore reserveEvm I).insert "balance0" balance0 }
      evm0 (.binary .gt (.extCodeSize (.storage token1Ref)) (.intLit 0)) =
        .ok (.bool false)
  simp [evalExpr?, hstorage, EvalResult.bind, bind, pure, evalBinaryOp?, hcodeSourceWord]

theorem mintToken1GuardTrue_of_code {σ : AccountMap}
    {evm0 reserveEvm : EVM.State} {I : ExecutionEnv} {balance0 : Value}
    (hPost : Eq σ evm0.accountMap)
    (henv : evm0.executionEnv = I)
    (htoken1Code :
      extCodeSizeWord σ (UInt256.land solcAddrMask (solcSlotWordAt ⟨7⟩ σ I)) ≠
        ⟨0⟩) :
    evalExpr? config
      { contract := contract, locals := (mintReserveStore reserveEvm I).insert "balance0" balance0 }
      evm0 (.binary .gt (.extCodeSize (.storage token1Ref)) (.intLit 0)) =
        .ok (.bool true) := by
  let token1WordS := solcSlotWordAt ⟨7⟩ σ I
  let token1WordE := solcSlotWordAt ⟨7⟩ evm0.accountMap evm0.executionEnv
  have hslot : token1WordS = token1WordE := by
    simp [token1WordS, token1WordE, hPost, henv]
  have hcodeEvm :
      extCodeSizeWord evm0.accountMap (UInt256.land solcAddrMask token1WordE) ≠
        ⟨0⟩ := by
    intro hzero
    rw [← hslot, ← hPost] at hzero
    exact htoken1Code (by simpa [token1WordS] using hzero)
  have hstorage :
      evalExpr? config
        { contract := contract,
          locals := (mintReserveStore reserveEvm I).insert "balance0" balance0 }
        evm0 (.storage token1Ref) = .ok (.address (uniswapAddressAtSlot evm0 ⟨7⟩)) := by
    exact evalExpr_uniswap_storage_address evm0
      ((mintReserveStore reserveEvm I).insert "balance0" balance0)
      (er := { base := "token1", steps := [] }) (slot := ⟨7⟩)
      (by simp [mintReserveStore, mintStore, token1Ref])
      (by simp [evalStorageRef, evalStorageRefSteps, token1Ref, EvalResult.bind, pure, bind])
      (by decide) (by rfl)
  have hcodeSource :
      (evm0.lookupAccount (uniswapAddressAtSlot evm0 ⟨7⟩)).option (⟨0⟩ : UInt256)
          (fun acc => EVM.Word.ofNat acc.code.size) ≠
        ⟨0⟩ := by
    have hcodeEvmRight :
        extCodeSizeWord evm0.accountMap (UInt256.land token1WordE solcAddrMask) ≠
          ⟨0⟩ := by
      simpa [u256_land_comm] using hcodeEvm
    intro hzero
    apply hcodeEvmRight
    simpa [State.lookupAccount, Solm.EVM.storageLoad, Account.lookupStorage,
      uniswapAddressAtSlot, extCodeSizeWord, solcSlotWordAt, solcSlotWord, token1WordE,
      accountAddress_ofUInt256_eq_ofNat_toNat] using hzero
  have hcodeSourceWord :
      EVM.Word.ofNat
          ((evm0.lookupAccount (uniswapAddressAtSlot evm0 ⟨7⟩)).option 0
            (fun acc => acc.code.size)) ≠
        ⟨0⟩ := by
    intro hzero
    apply hcodeSource
    cases hacc : evm0.lookupAccount (uniswapAddressAtSlot evm0 ⟨7⟩) with
    | none =>
        simp [Option.option]
    | some acc =>
        simpa [hacc, Option.option] using hzero
  have hcodeSourceWordPos :
      0 <
        (EVM.Word.ofNat
          ((evm0.lookupAccount (uniswapAddressAtSlot evm0 ⟨7⟩)).option 0
            (fun acc => acc.code.size))).toNat := by
    exact Nat.pos_of_ne_zero (by
      intro hzero
      exact hcodeSourceWord (uint256_toNat_eq_zero hzero))
  change
    evalExpr? config
      { contract := contract, locals := (mintReserveStore reserveEvm I).insert "balance0" balance0 }
      evm0 (.binary .gt (.extCodeSize (.storage token1Ref)) (.intLit 0)) =
        .ok (.bool true)
  simp [evalExpr?, hstorage, EvalResult.bind, bind, pure, evalBinaryOp?, hcodeSourceWordPos]

theorem mintReserve0Word_initState_eq_evm
    {σ σ₀ A I} {g : Sat256} :
    uniswapReserve0Word
        (uniswapLockEnteredState (initState σ σ₀ g A I)) =
      reserve0Word (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I := by
  let σLockS := sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩
  simpa [σLockS, uniswapReserve0Word, reserve0Word, getReservesSlotWord, solcSlotWordAt,
    solcSlotWord,
    uniswapLockEnteredState, uniswapUnlockedState, initState, storageStore_accountMap,
    storageStore_executionEnv, Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage]
    using (rfl : UInt256.land
      (σLockS.get? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.getD ⟨8⟩ ⟨0⟩))
      reserve112Mask = _)

theorem mintReserve1Word_initState_eq_evm
    {σ σ₀ A I} {g : Sat256} :
    uniswapReserve1Word
        (uniswapLockEnteredState (initState σ σ₀ g A I)) =
      reserve1Word (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I := by
  let σLockS := sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩
  simpa [σLockS, uniswapReserve1Word, reserve1Word, getReservesSlotWord, solcSlotWordAt,
    solcSlotWord,
    uniswapLockEnteredState, uniswapUnlockedState, initState, storageStore_accountMap,
    storageStore_executionEnv, Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage]
    using (rfl : UInt256.land (UInt256.div
      (σLockS.get? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.getD ⟨8⟩ ⟨0⟩))
      reserve112Shift) reserve112Mask = _)

theorem uniswapMintReservePrefix (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hunlocked : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨12⟩ = ⟨1⟩) :
    ExecBlock config { contract := contract, locals := mintStore I } evm
      (lockEnter ++
        [ .letDecl "_reserve0" (some uint112) (.storage reserve0Ref),
          .letDecl "_reserve1" (some uint112) (.storage reserve1Ref) ])
      (.ok { contract := contract, locals := mintReserveStore (uniswapLockEnteredState evm) I }
        (uniswapLockEnteredState evm)) := by
  let evmL := uniswapLockEnteredState evm
  have hlock := uniswapMintLockEnterPrefix evm I hwv hunlocked
  have hreserve0 :
      evalExpr? config { contract := contract, locals := mintStore I } evmL
        (.storage reserve0Ref) = .ok (.int (Int.ofNat (uniswapReserve0Word evmL).toNat)) := by
    exact evalExpr_uniswap_reserve0 evmL (mintStore I) (by simp [mintStore])
  have hreserve1 :
      evalExpr? config
        { contract := contract,
          locals := (mintStore I).insert "_reserve0"
            (.int (Int.ofNat (uniswapReserve0Word evmL).toNat)) } evmL
        (.storage reserve1Ref) = .ok (.int (Int.ofNat (uniswapReserve1Word evmL).toNat)) := by
    exact evalExpr_uniswap_reserve1 evmL
      ((mintStore I).insert "_reserve0" (.int (Int.ofNat (uniswapReserve0Word evmL).toNat)))
      (by simp [mintStore])
  have hreserves :
      ExecBlock config { contract := contract, locals := mintStore I } evmL
        [ .letDecl "_reserve0" (some uint112) (.storage reserve0Ref),
          .letDecl "_reserve1" (some uint112) (.storage reserve1Ref) ]
        (.ok { contract := contract, locals := mintReserveStore evmL I } evmL) := by
    refine ExecBlock.consNormal (ExecStmt.letDecl hreserve0) ?_
    exact ExecBlock.consNormal (ExecStmt.letDecl hreserve1) (by
      simpa [mintReserveStore] using
        (ExecBlock.nil : ExecBlock config
          { contract := contract, locals := mintReserveStore evmL I } evmL []
          (.ok { contract := contract, locals := mintReserveStore evmL I } evmL)))
  simpa [evmL, List.append_assoc] using execBlock_append hlock hreserves

abbrev mintBalanceStore
    (evm : EVM.State) (I : ExecutionEnv) (balance0 balance1 : UInt256) : Store :=
  uniswapBalanceOfStore (mintReserveStore evm I) (uniswapUint256Value balance0)
    (uniswapUint256Value balance1)

theorem mintBalanceStore_balance0
    (evm : EVM.State) (I : ExecutionEnv) (balance0 balance1 : UInt256) :
    (mintBalanceStore evm I balance0 balance1).get? "balance0" =
      some (uniswapUint256Value balance0) := by
  exact uniswapBalanceOfStore_balance0 (mintReserveStore evm I)
    (uniswapUint256Value balance0) (uniswapUint256Value balance1)

theorem mintBalanceStore_balance1
    (evm : EVM.State) (I : ExecutionEnv) (balance0 balance1 : UInt256) :
    (mintBalanceStore evm I balance0 balance1).get? "balance1" =
      some (uniswapUint256Value balance1) := by
  exact uniswapBalanceOfStore_balance1 (mintReserveStore evm I)
    (uniswapUint256Value balance0) (uniswapUint256Value balance1)

theorem mintBalanceStore_reserve0
    (evm : EVM.State) (I : ExecutionEnv) (balance0 balance1 : UInt256) :
    (mintBalanceStore evm I balance0 balance1).get? "_reserve0" =
      some (.int (Int.ofNat (uniswapReserve0Word evm).toNat)) := by
  rw [mintBalanceStore, uniswapBalanceOfStore, store_get_ne _ _ (by decide),
    store_get_ne _ _ (by decide), mintReserveStore_reserve0]

theorem mintBalanceStore_reserve1
    (evm : EVM.State) (I : ExecutionEnv) (balance0 balance1 : UInt256) :
    (mintBalanceStore evm I balance0 balance1).get? "_reserve1" =
      some (.int (Int.ofNat (uniswapReserve1Word evm).toNat)) := by
  rw [mintBalanceStore, uniswapBalanceOfStore, store_get_ne _ _ (by decide),
    store_get_ne _ _ (by decide), mintReserveStore_reserve1]

theorem mintBalanceStore_to
    (evm : EVM.State) (I : ExecutionEnv) (balance0 balance1 : UInt256) :
    (mintBalanceStore evm I balance0 balance1).get? "to" = some (mintToValue I) := by
  rw [mintBalanceStore, uniswapBalanceOfStore, store_get_ne _ _ (by decide),
    store_get_ne _ _ (by decide), mintReserveStore_to]

abbrev mintAmount0Word (evm : EVM.State) (balance0 : UInt256) : UInt256 :=
  UInt256.sub balance0 (uniswapReserve0Word evm)

abbrev mintAmount1Word (evm : EVM.State) (balance1 : UInt256) : UInt256 :=
  UInt256.sub balance1 (uniswapReserve1Word evm)

abbrev mintAmount0Value (evm : EVM.State) (balance0 : UInt256) : Value :=
  uniswapUint256Value (mintAmount0Word evm balance0)

abbrev mintAmount1Value (evm : EVM.State) (balance1 : UInt256) : Value :=
  uniswapUint256Value (mintAmount1Word evm balance1)

def mintAmountProductNat (amount0 amount1 : UInt256) : Nat :=
  amount0.toNat * amount1.toNat

def mintAmountProductWord (amount0 amount1 : UInt256) : UInt256 :=
  UInt256.ofNat (mintAmountProductNat amount0 amount1)

abbrev mintAmountProductValue (amount0 amount1 : UInt256) : Value :=
  uniswapUint256Value (mintAmountProductWord amount0 amount1)

theorem mintAmountProductWord_eq_mul
    (amount0 amount1 : UInt256)
    (hfit : mintAmountProductNat amount0 amount1 < UInt256.size) :
    mintAmountProductWord amount0 amount1 = UInt256.mul amount0 amount1 := by
  apply u256_inj
  rw [mintAmountProductWord, ulit_toNat' _ hfit, u256_mul_toNat]
  exact (Nat.mod_eq_of_lt hfit).symm

abbrev mintProportionalLiquidityWord
    (amount totalSupply reserve : UInt256) : UInt256 :=
  UInt256.div (mintAmountProductWord amount totalSupply) reserve

abbrev mintProportionalLiquidityValue
    (amount totalSupply reserve : UInt256) : Value :=
  uniswapUint256Value (mintProportionalLiquidityWord amount totalSupply reserve)

abbrev mintAmount0Store
    (evm : EVM.State) (I : ExecutionEnv) (balance0 balance1 : UInt256) : Store :=
  (mintBalanceStore evm I balance0 balance1).insert "amount0"
    (mintAmount0Value evm balance0)

abbrev mintAmountStore
    (evm : EVM.State) (I : ExecutionEnv) (balance0 balance1 : UInt256) : Store :=
  (mintAmount0Store evm I balance0 balance1).insert "amount1"
    (mintAmount1Value evm balance1)

theorem mintAmount0Store_amount0
    (evm : EVM.State) (I : ExecutionEnv) (balance0 balance1 : UInt256) :
    (mintAmount0Store evm I balance0 balance1).get? "amount0" =
      some (mintAmount0Value evm balance0) := by
  rw [mintAmount0Store, store_get_self]

theorem mintAmount0Store_balance1
    (evm : EVM.State) (I : ExecutionEnv) (balance0 balance1 : UInt256) :
    (mintAmount0Store evm I balance0 balance1).get? "balance1" =
      some (uniswapUint256Value balance1) := by
  rw [mintAmount0Store, store_get_ne _ _ (by decide), mintBalanceStore_balance1]

theorem mintAmount0Store_reserve1
    (evm : EVM.State) (I : ExecutionEnv) (balance0 balance1 : UInt256) :
    (mintAmount0Store evm I balance0 balance1).get? "_reserve1" =
      some (.int (Int.ofNat (uniswapReserve1Word evm).toNat)) := by
  rw [mintAmount0Store, store_get_ne _ _ (by decide), mintBalanceStore_reserve1]

theorem mintAmountStore_amount0
    (evm : EVM.State) (I : ExecutionEnv) (balance0 balance1 : UInt256) :
    (mintAmountStore evm I balance0 balance1).get? "amount0" =
      some (mintAmount0Value evm balance0) := by
  rw [mintAmountStore, store_get_ne _ _ (by decide), mintAmount0Store_amount0]

theorem mintAmountStore_amount1
    (evm : EVM.State) (I : ExecutionEnv) (balance0 balance1 : UInt256) :
    (mintAmountStore evm I balance0 balance1).get? "amount1" =
      some (mintAmount1Value evm balance1) := by
  rw [mintAmountStore, store_get_self]

theorem mintAmountStore_reserve0
    (evm : EVM.State) (I : ExecutionEnv) (balance0 balance1 : UInt256) :
    (mintAmountStore evm I balance0 balance1).get? "_reserve0" =
      some (.int (Int.ofNat (uniswapReserve0Word evm).toNat)) := by
  rw [mintAmountStore, store_get_ne _ _ (by decide), mintAmount0Store, store_get_ne _ _ (by decide),
    mintBalanceStore_reserve0]

theorem mintAmountStore_reserve1
    (evm : EVM.State) (I : ExecutionEnv) (balance0 balance1 : UInt256) :
    (mintAmountStore evm I balance0 balance1).get? "_reserve1" =
      some (.int (Int.ofNat (uniswapReserve1Word evm).toNat)) := by
  rw [mintAmountStore, store_get_ne _ _ (by decide), mintAmount0Store, store_get_ne _ _ (by decide),
    mintBalanceStore_reserve1]

theorem mintAmountStore_to
    (evm : EVM.State) (I : ExecutionEnv) (balance0 balance1 : UInt256) :
    (mintAmountStore evm I balance0 balance1).get? "to" = some (mintToValue I) := by
  rw [mintAmountStore, store_get_ne _ _ (by decide), mintAmount0Store,
    store_get_ne _ _ (by decide), mintBalanceStore_to]

theorem mintAmountStore_balance0
    (evm : EVM.State) (I : ExecutionEnv) (balance0 balance1 : UInt256) :
    (mintAmountStore evm I balance0 balance1).get? "balance0" =
      some (uniswapUint256Value balance0) := by
  rw [mintAmountStore, store_get_ne _ _ (by decide), mintAmount0Store,
    store_get_ne _ _ (by decide), mintBalanceStore_balance0]

theorem mintAmountStore_balance1
    (evm : EVM.State) (I : ExecutionEnv) (balance0 balance1 : UInt256) :
    (mintAmountStore evm I balance0 balance1).get? "balance1" =
      some (uniswapUint256Value balance1) := by
  rw [mintAmountStore, store_get_ne _ _ (by decide), mintAmount0Store_balance1]

theorem mintAmountStore_totalSupply
    (evm : EVM.State) (I : ExecutionEnv) (balance0 balance1 : UInt256) :
    (mintAmountStore evm I balance0 balance1).get? "totalSupply" = none := by
  rw [mintAmountStore, store_get_ne _ _ (by decide), mintAmount0Store,
    store_get_ne _ _ (by decide)]
  simp [mintBalanceStore, uniswapBalanceOfStore, mintReserveStore, mintStore]

theorem mintAmountStore_reserve0_base
    (evm : EVM.State) (I : ExecutionEnv) (balance0 balance1 : UInt256) :
    (mintAmountStore evm I balance0 balance1).get? "reserve0" = none := by
  rw [mintAmountStore, store_get_ne _ _ (by decide), mintAmount0Store,
    store_get_ne _ _ (by decide)]
  simp [mintBalanceStore, uniswapBalanceOfStore, mintReserveStore, mintStore]

theorem mintAmountStore_reserve1_base
    (evm : EVM.State) (I : ExecutionEnv) (balance0 balance1 : UInt256) :
    (mintAmountStore evm I balance0 balance1).get? "reserve1" = none := by
  rw [mintAmountStore, store_get_ne _ _ (by decide), mintAmount0Store,
    store_get_ne _ _ (by decide)]
  simp [mintBalanceStore, uniswapBalanceOfStore, mintReserveStore, mintStore]

theorem mintAmountStore_kLast
    (evm : EVM.State) (I : ExecutionEnv) (balance0 balance1 : UInt256) :
    (mintAmountStore evm I balance0 balance1).get? "kLast" = none := by
  rw [mintAmountStore, store_get_ne _ _ (by decide), mintAmount0Store,
    store_get_ne _ _ (by decide)]
  simp [mintBalanceStore, uniswapBalanceOfStore, mintReserveStore, mintStore]

theorem mintAmountStore_unlocked
    (evm : EVM.State) (I : ExecutionEnv) (balance0 balance1 : UInt256) :
    (mintAmountStore evm I balance0 balance1).get? "unlocked" = none := by
  rw [mintAmountStore, store_get_ne _ _ (by decide), mintAmount0Store,
    store_get_ne _ _ (by decide)]
  simp [mintBalanceStore, uniswapBalanceOfStore, mintReserveStore, mintStore]

theorem mintAfterMintFeeCallStore_amount0
    (evm : EVM.State) (I : ExecutionEnv) (balance0 balance1 : UInt256) (feeOn : Bool) :
    (resumeAfterInternalCall
      { contract := contract, locals := mintAmountStore evm I balance0 balance1 }
      "feeOn" (some [.bool feeOn])).locals.get? "amount0" =
        some (mintAmount0Value evm balance0) := by
  simp only [resumeAfterInternalCall]
  rw [store_get_ne _ _ (by decide), mintAmountStore_amount0]

theorem mintAfterMintFeeCallStore_amount1
    (evm : EVM.State) (I : ExecutionEnv) (balance0 balance1 : UInt256) (feeOn : Bool) :
    (resumeAfterInternalCall
      { contract := contract, locals := mintAmountStore evm I balance0 balance1 }
      "feeOn" (some [.bool feeOn])).locals.get? "amount1" =
        some (mintAmount1Value evm balance1) := by
  simp only [resumeAfterInternalCall]
  rw [store_get_ne _ _ (by decide), mintAmountStore_amount1]

theorem mintAfterMintFeeCallStore_to
    (evm : EVM.State) (I : ExecutionEnv) (balance0 balance1 : UInt256) (feeOn : Bool) :
    (resumeAfterInternalCall
      { contract := contract, locals := mintAmountStore evm I balance0 balance1 }
      "feeOn" (some [.bool feeOn])).locals.get? "to" = some (mintToValue I) := by
  simp only [resumeAfterInternalCall]
  rw [store_get_ne _ _ (by decide), mintAmountStore_to]

theorem mintAfterMintFeeCallStore_balance0
    (evm : EVM.State) (I : ExecutionEnv) (balance0 balance1 : UInt256) (feeOn : Bool) :
    (resumeAfterInternalCall
      { contract := contract, locals := mintAmountStore evm I balance0 balance1 }
      "feeOn" (some [.bool feeOn])).locals.get? "balance0" =
        some (uniswapUint256Value balance0) := by
  simp only [resumeAfterInternalCall]
  rw [store_get_ne _ _ (by decide), mintAmountStore_balance0]

theorem mintAfterMintFeeCallStore_balance1
    (evm : EVM.State) (I : ExecutionEnv) (balance0 balance1 : UInt256) (feeOn : Bool) :
    (resumeAfterInternalCall
      { contract := contract, locals := mintAmountStore evm I balance0 balance1 }
      "feeOn" (some [.bool feeOn])).locals.get? "balance1" =
        some (uniswapUint256Value balance1) := by
  simp only [resumeAfterInternalCall]
  rw [store_get_ne _ _ (by decide), mintAmountStore_balance1]

theorem mintAfterMintFeeCallStore_feeOn
    (evm : EVM.State) (I : ExecutionEnv) (balance0 balance1 : UInt256) (feeOn : Bool) :
    (resumeAfterInternalCall
      { contract := contract, locals := mintAmountStore evm I balance0 balance1 }
      "feeOn" (some [.bool feeOn])).locals.get? "feeOn" = some (.bool feeOn) := by
  simp [resumeAfterInternalCall, collapseReturns]

theorem mintAfterMintFeeCallStore_reserve0
    (evm : EVM.State) (I : ExecutionEnv) (balance0 balance1 : UInt256) (feeOn : Bool) :
    (resumeAfterInternalCall
      { contract := contract, locals := mintAmountStore evm I balance0 balance1 }
      "feeOn" (some [.bool feeOn])).locals.get? "_reserve0" =
        some (.int (Int.ofNat (uniswapReserve0Word evm).toNat)) := by
  simp only [resumeAfterInternalCall]
  rw [store_get_ne _ _ (by decide), mintAmountStore_reserve0]

theorem mintAfterMintFeeCallStore_reserve1
    (evm : EVM.State) (I : ExecutionEnv) (balance0 balance1 : UInt256) (feeOn : Bool) :
    (resumeAfterInternalCall
      { contract := contract, locals := mintAmountStore evm I balance0 balance1 }
      "feeOn" (some [.bool feeOn])).locals.get? "_reserve1" =
        some (.int (Int.ofNat (uniswapReserve1Word evm).toNat)) := by
  simp only [resumeAfterInternalCall]
  rw [store_get_ne _ _ (by decide), mintAmountStore_reserve1]

theorem mintAfterMintFeeCallStore_totalSupply
    (evm : EVM.State) (I : ExecutionEnv) (balance0 balance1 : UInt256) (feeOn : Bool) :
    (resumeAfterInternalCall
      { contract := contract, locals := mintAmountStore evm I balance0 balance1 }
      "feeOn" (some [.bool feeOn])).locals.get? "totalSupply" = none := by
  simp only [resumeAfterInternalCall]
  rw [store_get_ne _ _ (by decide), mintAmountStore_totalSupply]

theorem mintAfterMintFeeCallStore_reserve0_base
    (evm : EVM.State) (I : ExecutionEnv) (balance0 balance1 : UInt256) (feeOn : Bool) :
    (resumeAfterInternalCall
      { contract := contract, locals := mintAmountStore evm I balance0 balance1 }
      "feeOn" (some [.bool feeOn])).locals.get? "reserve0" = none := by
  simp only [resumeAfterInternalCall]
  rw [store_get_ne _ _ (by decide), mintAmountStore_reserve0_base]

theorem mintAfterMintFeeCallStore_reserve1_base
    (evm : EVM.State) (I : ExecutionEnv) (balance0 balance1 : UInt256) (feeOn : Bool) :
    (resumeAfterInternalCall
      { contract := contract, locals := mintAmountStore evm I balance0 balance1 }
      "feeOn" (some [.bool feeOn])).locals.get? "reserve1" = none := by
  simp only [resumeAfterInternalCall]
  rw [store_get_ne _ _ (by decide), mintAmountStore_reserve1_base]

theorem mintAfterMintFeeCallStore_kLast
    (evm : EVM.State) (I : ExecutionEnv) (balance0 balance1 : UInt256) (feeOn : Bool) :
    (resumeAfterInternalCall
      { contract := contract, locals := mintAmountStore evm I balance0 balance1 }
      "feeOn" (some [.bool feeOn])).locals.get? "kLast" = none := by
  simp only [resumeAfterInternalCall]
  rw [store_get_ne _ _ (by decide), mintAmountStore_kLast]

theorem mintAfterMintFeeCallStore_unlocked
    (evm : EVM.State) (I : ExecutionEnv) (balance0 balance1 : UInt256) (feeOn : Bool) :
    (resumeAfterInternalCall
      { contract := contract, locals := mintAmountStore evm I balance0 balance1 }
      "feeOn" (some [.bool feeOn])).locals.get? "unlocked" = none := by
  simp only [resumeAfterInternalCall]
  rw [store_get_ne _ _ (by decide), mintAmountStore_unlocked]

theorem evalExprs_mint_mintFeeArgs
    (reserveEvm callEvm : EVM.State) (I : ExecutionEnv) (balance0 balance1 : UInt256) :
    evalExprs? config
      { contract := contract, locals := mintAmountStore reserveEvm I balance0 balance1 } callEvm
      [.var "_reserve0", .var "_reserve1"] =
        .ok [mintFeeReserve0Value (uniswapReserve0Word reserveEvm),
          mintFeeReserve1Value (uniswapReserve1Word reserveEvm)] := by
  have hreserve0 :
      evalExpr? config
        { contract := contract, locals := mintAmountStore reserveEvm I balance0 balance1 }
        callEvm (.var "_reserve0") =
          .ok (mintFeeReserve0Value (uniswapReserve0Word reserveEvm)) := by
    simp only [evalExpr?, EvalResult.ofOption, mintFeeReserve0Value, uniswapUint256Value]
    rw [mintAmountStore_reserve0]
  have hreserve1 :
      evalExpr? config
        { contract := contract, locals := mintAmountStore reserveEvm I balance0 balance1 }
        callEvm (.var "_reserve1") =
          .ok (mintFeeReserve1Value (uniswapReserve1Word reserveEvm)) := by
    simp only [evalExpr?, EvalResult.ofOption, mintFeeReserve1Value, uniswapUint256Value]
    rw [mintAmountStore_reserve1]
  simp only [evalExprs?, hreserve0, hreserve1, EvalResult.bind, bind, pure]

theorem evalStorageRef_mint_totalSupply_of_get
    (evm : EVM.State) (locals : Store) :
    evalStorageRef config { contract := contract, locals := locals } evm totalSupplyRef =
      .ok ({ base := "totalSupply", steps := [] } : EvaledStorageRef) := by
  simp [evalStorageRef, evalStorageRefSteps, totalSupplyRef, EvalResult.bind, pure, bind]

theorem evalExpr_mint_totalSupply_of_get
    (evm : EVM.State) {locals : Store}
    (hbase : locals.get? "totalSupply" = none) :
    evalExpr? config { contract := contract, locals := locals } evm (.storage totalSupplyRef) =
      .ok (uniswapUint256Value (mintFunctionTotalSupplyWord evm)) := by
  rw [evalExpr_storage_scalar (t := .int uint256Int)
    (hbase := by simpa [totalSupplyRef] using hbase)
    (her := evalStorageRef_mint_totalSupply_of_get evm locals)
    (hty := by simp [storageTypeAt?, contract, storageDecls, uint256St])
    (hloc := by rfl)]
  exact congrArg EvalResult.ok (storageLocLoad_uint256 evm ⟨0⟩)

theorem uniswapMintTotalSupplyLet
    (evm : EVM.State) (locals : Store)
    (hbase : locals.get? "totalSupply" = none) :
    ExecBlock config { contract := contract, locals := locals } evm
      [ .letDecl "_totalSupply" (some uint256) (.storage totalSupplyRef) ]
      (.ok
        { contract := contract,
          locals := locals.insert "_totalSupply"
            (uniswapUint256Value (mintFunctionTotalSupplyWord evm)) }
        evm) := by
  exact ExecBlock.consNormal
    (ExecStmt.letDecl (evalExpr_mint_totalSupply_of_get evm hbase))
    ExecBlock.nil

theorem evalExpr_mint_totalSupply_eq_zero_true
    {locals : Store} (evm : EVM.State)
    (htotal : locals.get? "_totalSupply" = some (uniswapUint256Value (⟨0⟩ : UInt256))) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.binary .eq (.var "_totalSupply") (.intLit 0)) = .ok (.bool true) := by
  simp only [evalExpr?, EvalResult.ofOption, htotal, EvalResult.bind, bind, pure]
  simp [evalBinaryOp?, uniswapUint256Value, uint256Value]

theorem evalExpr_mint_totalSupply_eq_zero_false
    {locals : Store} (evm : EVM.State) (totalSupply : UInt256)
    (htotal : locals.get? "_totalSupply" = some (uniswapUint256Value totalSupply))
    (hzero : totalSupply ≠ ⟨0⟩) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.binary .eq (.var "_totalSupply") (.intLit 0)) = .ok (.bool false) := by
  have hnat : totalSupply.toNat ≠ 0 := by
    intro h
    exact hzero (uint256_toNat_eq_zero h)
  simp only [evalExpr?, EvalResult.ofOption, htotal, EvalResult.bind, bind, pure]
  simp [evalBinaryOp?, hnat]

theorem evalExpr_mint_amountProduct_of_get
    {locals : Store} (evm : EVM.State) (amount0 amount1 : UInt256)
    (hamount0 : locals.get? "amount0" = some (uniswapUint256Value amount0))
    (hamount1 : locals.get? "amount1" = some (uniswapUint256Value amount1))
    (hfit : mintAmountProductNat amount0 amount1 < UInt256.size) :
    evalExpr? config { contract := contract, locals := locals } evm
      (u256 (.binary .mul (.var "amount0") (.var "amount1"))) =
        .ok (mintAmountProductValue amount0 amount1) := by
  rw [mintAmountProductValue, mintAmountProductWord_eq_mul amount0 amount1 hfit]
  exact evalExpr_uint256_mul
    (by simp only [evalExpr?, EvalResult.ofOption, hamount0])
    (by simp only [evalExpr?, EvalResult.ofOption, hamount1]) hfit

theorem evalExpr_mint_namedProduct_of_get
    {locals : Store} (evm : EVM.State) (xName yName : Ident) (x y : UInt256)
    (hx : locals.get? xName = some (uniswapUint256Value x))
    (hy : locals.get? yName = some (uniswapUint256Value y))
    (hfit : mintAmountProductNat x y < UInt256.size) :
    evalExpr? config { contract := contract, locals := locals } evm
      (u256 (.binary .mul (.var xName) (.var yName))) =
        .ok (mintAmountProductValue x y) := by
  rw [mintAmountProductValue, mintAmountProductWord_eq_mul x y hfit]
  exact evalExpr_uint256_mul
    (by simp only [evalExpr?, EvalResult.ofOption, hx])
    (by simp only [evalExpr?, EvalResult.ofOption, hy]) hfit

theorem evalExprs_mint_initialSqrtArg_of_get
    {locals : Store} (evm : EVM.State) (amount0 amount1 : UInt256)
    (hamount0 : locals.get? "amount0" = some (uniswapUint256Value amount0))
    (hamount1 : locals.get? "amount1" = some (uniswapUint256Value amount1))
    (hfit : mintAmountProductNat amount0 amount1 < UInt256.size) :
    evalExprs? config { contract := contract, locals := locals } evm
      [u256 (.binary .mul (.var "amount0") (.var "amount1"))] =
        .ok [sqrtFunctionYValue (mintAmountProductWord amount0 amount1)] := by
  simp [evalExprs?, evalExpr_mint_amountProduct_of_get evm amount0 amount1 hamount0
    hamount1 hfit, sqrtFunctionYValue, mintAmountProductValue, EvalResult.bind, bind, pure]

theorem evalExpr_mint_proportionalLiquidity_of_get
    {locals : Store} (evm : EVM.State) (amountName reserveName : Ident)
    (amount totalSupply reserve : UInt256)
    (hamount : locals.get? amountName = some (uniswapUint256Value amount))
    (htotal : locals.get? "_totalSupply" = some (uniswapUint256Value totalSupply))
    (hreserve : locals.get? reserveName = some (.int (Int.ofNat reserve.toNat)))
    (hfit : mintAmountProductNat amount totalSupply < UInt256.size)
    (hreserveNonzero : reserve ≠ ⟨0⟩) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.binary .div
        (u256 (.binary .mul (.var amountName) (.var "_totalSupply")))
        (.var reserveName)) =
        .ok (mintProportionalLiquidityValue amount totalSupply reserve) := by
  have hmul :=
    evalExpr_mint_namedProduct_of_get (locals := locals) evm amountName "_totalSupply"
      amount totalSupply hamount htotal hfit
  have hreserveNat : reserve.toNat ≠ 0 := by
    intro h
    exact hreserveNonzero (uint256_toNat_eq_zero h)
  have hreserveInt : Int.ofNat reserve.toNat ≠ 0 := by
    intro h
    exact hreserveNat (Int.ofNat.inj h)
  simp only [evalExpr?, hmul, EvalResult.ofOption, hreserve, EvalResult.bind, bind]
  simp [evalBinaryOp?, mintProportionalLiquidityValue, uniswapUint256Value, uint256Value,
    mintProportionalLiquidityWord, hreserveNat, udiv_toNat]

abbrev mintInitialLiquidityBranchStmts : List Stmt :=
  [ .internalCall "sqrt" [u256 (.binary .mul (.var "amount0") (.var "amount1"))]
      "rootLiquidity",
    .letDecl "liquidity" (some uint256)
      (u256 (.binary .sub (.var "rootLiquidity") (.intLit minimumLiquidity))),
    .internalCall "_mint" [zeroAddr, (.intLit minimumLiquidity)] "_minimumMint" ]

abbrev mintProportionalLiquidityBranchStmts : List Stmt :=
  [ .letDecl "liquidity0" (some uint256)
      (.binary .div (u256 (.binary .mul (.var "amount0") (.var "_totalSupply")))
        (.var "_reserve0")),
    .letDecl "liquidity1" (some uint256)
      (.binary .div (u256 (.binary .mul (.var "amount1") (.var "_totalSupply")))
        (.var "_reserve1")),
    .internalCall "min" [.var "liquidity0", .var "liquidity1"] "liquidity" ]

abbrev mintLiquidityBranchStmt : Stmt :=
  .ite (.binary .eq (.var "_totalSupply") (.intLit 0))
    mintInitialLiquidityBranchStmts
    mintProportionalLiquidityBranchStmts

abbrev mintAfterLiquidityTailStmts : List Stmt :=
  [ .require (.binary .gt (.var "liquidity") (.intLit 0)),
    .internalCall "_mint" [.var "to", .var "liquidity"] "_mintResult" ] ++
  updateReservesStmtsWith (.var "balance0") (.var "balance1")
    (.var "_reserve0") (.var "_reserve1") ++
  [ .ite (.var "feeOn")
      [ .assign .storage kLastRef
          (u256 (.binary .mul (.storage reserve0Ref) (.storage reserve1Ref))) ]
      [] ] ++
  lockExit ++
  [ .return [(.var "liquidity")] ]

end UniswapV2Pair
