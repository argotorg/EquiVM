import Examples.UniswapV2Pair.ExternalWrappers
import Examples.UniswapV2Pair.Dispatch
import Reasoning.Refinement
import Reasoning.SolmBody

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000

namespace UniswapV2Pair

/-! ## `allowance(address,address)` canonical-success slice -/

/-- The raw ABI word for `allowance`'s `owner` argument. -/
abbrev allowanceOwnerWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 4

/-- The raw ABI word for `allowance`'s `spender` argument. -/
abbrev allowanceSpenderWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 36

abbrev allowanceOwnerValue (I : ExecutionEnv) : Value :=
  .address (AccountAddress.ofNat (allowanceOwnerWord I).toNat)

abbrev allowanceSpenderValue (I : ExecutionEnv) : Value :=
  .address (AccountAddress.ofNat (allowanceSpenderWord I).toNat)

abbrev allowanceOwnerKey (I : ExecutionEnv) : KeyValue :=
  .address (AccountAddress.ofNat (allowanceOwnerWord I).toNat)

abbrev allowanceSpenderKey (I : ExecutionEnv) : KeyValue :=
  .address (AccountAddress.ofNat (allowanceSpenderWord I).toNat)

abbrev allowanceStore (I : ExecutionEnv) : Store :=
  ((∅ : Store).insert "owner" (allowanceOwnerValue I)).insert "spender"
    (allowanceSpenderValue I)

theorem allowanceStore_owner (I : ExecutionEnv) :
    (allowanceStore I).get? "owner" = some (allowanceOwnerValue I) := by
  rw [allowanceStore, store_get_ne _ _ (by decide), store_get_self]

theorem allowanceStore_spender (I : ExecutionEnv) :
    (allowanceStore I).get? "spender" = some (allowanceSpenderValue I) := by
  rw [allowanceStore, store_get_self]

theorem allowanceStore_owner_getElem? (I : ExecutionEnv) :
    (allowanceStore I)["owner"]? = some (allowanceOwnerValue I) := by
  rw [← Std.HashMap.get?_eq_getElem?, allowanceStore_owner]

theorem allowanceStore_spender_getElem? (I : ExecutionEnv) :
    (allowanceStore I)["spender"]? = some (allowanceSpenderValue I) := by
  rw [← Std.HashMap.get?_eq_getElem?, allowanceStore_spender]

def allowanceStorageSlot (I : ExecutionEnv) : UInt256 :=
  allowanceSlot (allowanceOwnerKey I) (allowanceSpenderKey I)

abbrev allowanceEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "allowance",
    steps := [.mindex (allowanceOwnerKey I), .mindex (allowanceSpenderKey I)] }

def allowanceWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  σ.find? I.codeOwner |>.option ⟨0⟩
    (fun acc => acc.storage.findD (allowanceStorageSlot I) ⟨0⟩)

theorem allowanceStorageSlot_eq_mapSlot (I : ExecutionEnv)
    (hcanonOwner : (allowanceOwnerWord I).toNat < EVM.addressModulus)
    (hcanonSpender : (allowanceSpenderWord I).toNat < EVM.addressModulus) :
    allowanceStorageSlot I =
      mapSlot (allowanceSpenderWord I) (mapSlot (allowanceOwnerWord I) ⟨2⟩) := by
  unfold allowanceStorageSlot allowanceSlot allowanceOwnerSlot allowanceOwnerKey allowanceSpenderKey
  rw [keyValueToWord_address_of_canonical _ hcanonOwner,
    keyValueToWord_address_of_canonical _ hcanonSpender]

theorem uniswapDecode_allowance_ok {I : ExecutionEnv}
    (hsz68 : 68 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hcanonOwner : (allowanceOwnerWord I).toNat < EVM.addressModulus)
    (hcanonSpender : (allowanceSpenderWord I).toNat < EVM.addressModulus) :
    decodeCalldata (allowanceTransition.params.map Param.name)
      (transitionSignature allowanceTransition).paramTypes I.calldata = some (allowanceStore I) := by
  show decodeCalldata ["owner", "spender"] [addr, addr] I.calldata = _
  simpa [allowanceStore, allowanceOwnerValue, allowanceSpenderValue, allowanceOwnerWord,
    allowanceSpenderWord, calldataWord]
    using decodeCalldata_address_address_ok (cd := I.calldata) (x := "owner") (y := "spender")
      hsz68 hbig hcanonOwner hcanonSpender

theorem uniswapDecode_allowance_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 68) :
    decodeCalldata (allowanceTransition.params.map Param.name)
      (transitionSignature allowanceTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["owner", "spender"] [addr, addr] I.calldata = none
  simpa [addr] using decodeCalldata_address_address_none_short
    (cd := I.calldata) (x := "owner") (y := "spender") hsz4 hshort

theorem uniswapDecode_allowance_none_noncanon_owner {I : ExecutionEnv}
    (hsz68 : 68 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hncOwner : ¬ (allowanceOwnerWord I).toNat < EVM.addressModulus) :
    decodeCalldata (allowanceTransition.params.map Param.name)
      (transitionSignature allowanceTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["owner", "spender"] [addr, addr] I.calldata = none
  simpa [addr, allowanceOwnerWord, calldataWord]
    using decodeCalldata_address_address_none_noncanon0
      (cd := I.calldata) (x := "owner") (y := "spender") hsz68 hbig hncOwner

theorem uniswapDecode_allowance_none_noncanon_spender {I : ExecutionEnv}
    (hsz68 : 68 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hcanonOwner : (allowanceOwnerWord I).toNat < EVM.addressModulus)
    (hncSpender : ¬ (allowanceSpenderWord I).toNat < EVM.addressModulus) :
    decodeCalldata (allowanceTransition.params.map Param.name)
      (transitionSignature allowanceTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["owner", "spender"] [addr, addr] I.calldata = none
  simpa [addr, allowanceOwnerWord, allowanceSpenderWord, calldataWord]
    using decodeCalldata_address_address_none_noncanon1
      (cd := I.calldata) (x := "owner") (y := "spender")
      hsz68 hbig hcanonOwner hncSpender

theorem uniswapDecode_allowance_none_huge {I : ExecutionEnv}
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size) :
    decodeCalldata (allowanceTransition.params.map Param.name)
      (transitionSignature allowanceTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["owner", "spender"] [addr, addr] I.calldata = none
  simpa [addr] using decodeCalldata_address_address_none_huge
    (cd := I.calldata) (x := "owner") (y := "spender") hbig

/-- The Solm `allowance(address,address)` body returns `allowance[owner][spender]`. -/
theorem uniswapAllowanceBodyReturns (evm : EVM.State) (I : ExecutionEnv)
    (h : evm.executionEnv.weiValue = ⟨0⟩) :
    ExecTransitionBody config contract evm (allowanceStore I) allowanceTransition.body
      (.returned { contract := contract, locals := allowanceStore I } evm
        (some (.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
            (allowanceStorageSlot I)).toNat)))) := by
  have hgowner := allowanceStore_owner_getElem? I
  have hgspender := allowanceStore_spender_getElem? I
  exact ExecFuncBody.execBlockRet <|
    (ABlock.start.requireStep (evalCallvalueEq_true h)).returns (by
      rw [evalExpr_storage_scalar (t := .int uint256Int)
        (er := allowanceEvaledRef I)
        (loc := wordLoc (allowanceStorageSlot I))
        (hbase := by simp [allowanceStore, allowanceRef])
        (her := by
          simp only [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, allowanceRef,
            allowanceEvaledRef, evalExpr?, EvalResult.bind, EvalResult.ofOption, bind, pure,
            valueToKey?, Std.HashMap.get?_eq_getElem?, hgowner, hgspender,
            allowanceOwnerValue, allowanceSpenderValue, allowanceOwnerKey, allowanceSpenderKey])
        (hty := by rfl)
        (hloc := by rfl)]
      exact congrArg EvalResult.ok (uniswapStorageLocLoad_uint256 evm (allowanceStorageSlot I)))

/-! ## EVM trace -/

/-- The optimized external wrapper for `allowance(address,address)` accepts canonical calldata and
    jumps to the shared nested-mapping getter routine at pc 5987. -/
theorem uniswapAllowanceX_decoded {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hcanonOwner : (allowanceOwnerWord I).toNat < EVM.addressModulus)
    (hcanonSpender : (allowanceSpenderWord I).toNat < EVM.addressModulus)
    (hreach : ∃ k C, RD uniswapV2PairBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1421⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD uniswapV2PairBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨5987⟩
        [allowanceSpenderWord I, allowanceOwnerWord I, ⟨861⟩, sel]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd1443⟩ := RD.uniswapTwoAddressGetterLenOk
    (entry := ⟨1421⟩) (routine := ⟨5987⟩) hreach
    uniswap_two_address_getter_entry_wf (by jump_dest) hsz68 hsize
  obtain ⟨_, _, rd5987⟩ := RD.uniswapTwoAddressGetterMaskAndJump
    (entry := ⟨1421⟩) (routine := ⟨5987⟩) (R := [sel]) rd1443
    uniswap_two_address_getter_entry_wf
    (by simpa [allowanceOwnerWord] using hcanonOwner)
    (by simpa [allowanceSpenderWord] using hcanonSpender)
    (by jump_dest) (by simp only [List.length_singleton]; omega)
  exact ⟨_, _, by simpa [allowanceOwnerWord, allowanceSpenderWord] using rd5987⟩

/-- Short-calldata path for `allowance(address,address)` from the dispatcher body entry.

This covers calldata with a selector present but fewer than two ABI words. The dispatcher-level
`calldatasize < 4` branch remains in `Correct.lean`.
-/
theorem uniswapAllowanceX_shortarg {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 68)
    (hreach : ∃ k C, RD uniswapV2PairBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1421⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev uniswapV2PairBytecode g (initState cA gh bl σ σ₀ g A I) := by
  exact RD.uniswapTwoAddressGetterShort
    (entry := ⟨1421⟩) (routine := ⟨5987⟩)
    hreach uniswap_two_address_getter_entry_wf hsz4 hsize hshort

/-- The EVM `allowance(address,address)` success path loads the explicit nested mapping slot and
    returns it. -/
theorem uniswapX_allowance_ok {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hcanonOwner : (allowanceOwnerWord I).toNat < EVM.addressModulus)
    (hcanonSpender : (allowanceSpenderWord I).toNat < EVM.addressModulus)
    (hreach : ∃ k C, RD uniswapV2PairBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1421⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret uniswapV2PairBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray (allowanceWord σ I)) := by
  obtain ⟨_, _, rd5987⟩ := uniswapAllowanceX_decoded (g := g)
    hsz68 hsize hcanonOwner hcanonSpender hreach
  obtain ⟨_, _, rd6005⟩ := RD.uniswapNestedMappingInnerHash (pc := ⟨5987⟩)
    (baseSlot := ⟨2⟩) (owner := allowanceOwnerWord I) (spender := allowanceSpenderWord I)
    (ret := ⟨861⟩) (R := [sel]) rd5987 uniswap_nested_mapping_getter_wf
    (by simp only [List.length_singleton]; omega)
  obtain ⟨_, _, rd6013⟩ := RD.uniswapNestedMappingOuterHash (pc := ⟨5987⟩)
    (baseSlot := ⟨2⟩) (owner := allowanceOwnerWord I) (spender := allowanceSpenderWord I)
    (ret := ⟨861⟩) (R := [sel]) rd6005 uniswap_nested_mapping_getter_wf
    (by simp only [List.length_singleton]; omega)
  obtain ⟨k861, C861, rd861raw⟩ := RD.uniswapNestedMappingLoadAndJump
    (pc := ⟨5987⟩) (baseSlot := ⟨2⟩)
    (slot := mapSlot (allowanceSpenderWord I) (mapSlot (allowanceOwnerWord I) ⟨2⟩))
    (ret := ⟨861⟩) (R := [sel]) rd6013 uniswap_nested_mapping_getter_wf (by jump_dest)
    (by simp only [List.length_singleton]; omega)
  have hslot := allowanceStorageSlot_eq_mapSlot I hcanonOwner hcanonSpender
  have hword :
      (σ.find? I.codeOwner |>.option ⟨0⟩
          (fun acc => acc.storage.findD
            (mapSlot (allowanceSpenderWord I) (mapSlot (allowanceOwnerWord I) ⟨2⟩)) ⟨0⟩))
        = allowanceWord σ I := by
    unfold allowanceWord
    rw [hslot]
  have rd861 : RD uniswapV2PairBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨861⟩
      (allowanceWord σ I :: ⟨861⟩ :: [sel])
      (uniswapNestedMappingHashMem ⟨2⟩ (allowanceOwnerWord I) (allowanceSpenderWord I))
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k861 C861 := by
    simpa [hword] using rd861raw
  exact RD.uniswapReturnWord861FromMem
    (val := allowanceWord σ I) (ret := ⟨861⟩) (R := [sel])
    (mem := uniswapNestedMappingHashMem ⟨2⟩ (allowanceOwnerWord I) (allowanceSpenderWord I))
    (memout := uniswapNestedMappingReturnMem ⟨2⟩ (allowanceOwnerWord I)
      (allowanceSpenderWord I) (allowanceWord σ I))
    rd861
    (uniswapNestedMappingHashMem_mload64 ⟨2⟩ (allowanceOwnerWord I)
      (allowanceSpenderWord I))
    (by rfl)
    (uniswapNestedMappingReturnMem_mload64 ⟨2⟩ (allowanceOwnerWord I)
      (allowanceSpenderWord I) (allowanceWord σ I))
    (uniswapNestedMappingReturnMem_read128 ⟨2⟩ (allowanceOwnerWord I)
      (allowanceSpenderWord I) (allowanceWord σ I))
    (by simp only [List.length_singleton]; omega)

/-- Canonical-success refinement slice for `allowance(address,address)`.

The non-canonical address cases are intentionally not claimed here: the optimized bytecode masks the
address words, while the current ABI decoder rejects non-canonical address encodings.
-/
theorem uniswapAllowanceBodyCoreOk
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsz68 : 68 ≤ I.calldata.size) (_hbig : I.calldata.size < 2 ^ 255 + 4)
    (hcanonOwner : (allowanceOwnerWord I).toNat < EVM.addressModulus)
    (hcanonSpender : (allowanceSpenderWord I).toNat < EVM.addressModulus)
    (hdispatch : dispatchMsg contract I.calldata = some allowanceTransition)
    (hdecode :
      decodeCalldata (allowanceTransition.params.map Param.name)
        (transitionSignature allowanceTransition).paramTypes I.calldata = some (allowanceStore I))
    (hreach : ∃ k C, RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1421⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hword : allowanceWord σ_evm I = allowanceWord σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner (allowanceStorageSlot I) ⟨0⟩
  have hbody :
      ExecTransitionBody config contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (allowanceStore I)
        allowanceTransition.body
        (.returned { contract := contract, locals := allowanceStore I }
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (some (.int (Int.ofNat (allowanceWord σ_solm I).toNat)))) := by
    simpa [allowanceWord, allowanceStorageSlot, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using
      uniswapAllowanceBodyReturns
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I
        (by simp only [initState]; exact hwv)
  exact (uniswapX_allowance_ok (g := Sat256.ofUInt256 g)
      hsz68 hsize hcanonOwner hcanonSpender hreach)
    |>.reEquivExecutionTransport hcode hdispatch hdecode hbody (by rw [← hword])
      hAccounts
      (returnEquiv_of_encode
        (by simpa [uint256] using uint256ReturnEncoding (allowanceWord σ_evm I)))

/-- Short-calldata decode-failure refinement slice for `allowance(address,address)`.

The non-canonical and huge-calldata branches are intentionally not claimed here: the optimized
bytecode masks address words and uses an unsigned length check, while the current Solm ABI decoder
rejects those cases before execution.
-/
theorem uniswapAllowanceBodyCoreDecodeFailed_short
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 68)
    (hdispatch : dispatchMsg contract I.calldata = some allowanceTransition)
    (hreach : ∃ k C, RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1421⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hdec := uniswapDecode_allowance_none_short (I := I) hsz4 hshort
  exact (uniswapAllowanceX_shortarg (g := Sat256.ofUInt256 g)
      hsz4 hsize hshort hreach)
    |>.reEquivDecodingFailed hcode hdispatch hdec

/-- Canonical-success `allowance(address,address)` refinement slice, packaged from selector
dispatch through the body core. -/
theorem uniswapAllowanceBodyOk
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩) (hsel : selIs I ⟨#[0xdd, 0x62, 0xed, 0x3e]⟩)
    (hsz68 : 68 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hcanonOwner : (allowanceOwnerWord I).toNat < EVM.addressModulus)
    (hcanonSpender : (allowanceSpenderWord I).toNat < EVM.addressModulus)
    (hdispatch : dispatchMsg contract I.calldata = some allowanceTransition)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I ⟨#[0xdd, 0x62, 0xed, 0x3e]⟩ rfl hsel
  exact uniswapAllowanceBodyCoreOk hcode hsize hwv hsz68 hbig hcanonOwner hcanonSpender
    hdispatch
    (uniswapDecode_allowance_ok hsz68 hbig hcanonOwner hcanonSpender)
    (uniswapReachAllowanceBody (g := Sat256.ofUInt256 g) hcode hwv hsz4 hsize hsel)
    hAccounts

/-- Short-calldata decode-failure `allowance(address,address)` refinement slice, packaged from
selector dispatch through the body core. -/
theorem uniswapAllowanceBodyDecodeFailed_short
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩) (hsel : selIs I ⟨#[0xdd, 0x62, 0xed, 0x3e]⟩)
    (hshort : I.calldata.size < 68)
    (hdispatch : dispatchMsg contract I.calldata = some allowanceTransition) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I ⟨#[0xdd, 0x62, 0xed, 0x3e]⟩ rfl hsel
  exact uniswapAllowanceBodyCoreDecodeFailed_short hcode hsize hsz4 hshort hdispatch
    (uniswapReachAllowanceBody (g := Sat256.ofUInt256 g) hcode hwv hsz4 hsize hsel)

theorem uniswapAllowanceBody
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩) (hsel : selIs I ⟨#[0xdd, 0x62, 0xed, 0x3e]⟩)
    (hdispatch : dispatchMsg contract I.calldata = some allowanceTransition)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  by_cases hsz68 : 68 ≤ I.calldata.size
  · by_cases hbig : I.calldata.size < 2 ^ 255 + 4
    · by_cases hcanonOwner : (allowanceOwnerWord I).toNat < EVM.addressModulus
      · by_cases hcanonSpender : (allowanceSpenderWord I).toNat < EVM.addressModulus
        · exact uniswapAllowanceBodyOk hcode hsize hwv hsel hsz68 hbig hcanonOwner
            hcanonSpender hdispatch hAccounts
        · sorry
      · sorry
    · sorry
  · exact uniswapAllowanceBodyDecodeFailed_short hcode hsize hwv hsel (by omega) hdispatch

end UniswapV2Pair
