import Examples.UniswapV2Pair.ExternalWrappers
import Examples.UniswapV2Pair.BurnRoutines
import Examples.UniswapV2Pair.MutatorDispatch

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace UniswapV2Pair

/-! ## `burn(address)` source slice and wrapper decode -/

/-- The raw ABI word for `burn`'s `to` argument. -/
abbrev burnToWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 4

abbrev burnToMaskedWord (I : ExecutionEnv) : UInt256 :=
  UInt256.land solcAddrMask (burnToWord I)

abbrev burnToValue (I : ExecutionEnv) : Value :=
  .address (AccountAddress.ofNat (burnToWord I).toNat)

abbrev burnToKey (I : ExecutionEnv) : KeyValue :=
  .address (AccountAddress.ofNat (burnToWord I).toNat)

abbrev burnStore (I : ExecutionEnv) : Store :=
  (∅ : Store).insert "to" (burnToValue I)

theorem burnToKey_word_masked (I : ExecutionEnv) :
    keyValueToWord (burnToKey I) = burnToMaskedWord I := by
  unfold burnToKey burnToMaskedWord
  rw [keyValueToWord_address_ofNat_mask]

theorem uniswapDecode_burn_ok {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (burnTransition.params.map Param.name)
      (transitionSignature burnTransition).paramTypes I.calldata = some (burnStore I) := by
  show decodeCalldataWithMode config.abiDecodeMode ["to"] [legacyAddr] I.calldata = _
  simpa [burnStore, burnToValue, burnToWord, calldataWord]
    using decodeCalldata_legacyAddress_ok (cd := I.calldata) (x := "to") hsz36

theorem uniswapDecode_burn_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36) :
    decodeCalldataWithMode config.abiDecodeMode (burnTransition.params.map Param.name)
      (transitionSignature burnTransition).paramTypes I.calldata = none := by
  show decodeCalldataWithMode config.abiDecodeMode ["to"] [legacyAddr] I.calldata = none
  simpa using decodeCalldata_legacyAddress_none_short (cd := I.calldata) (x := "to")
    hsz4 hshort

theorem burnStore_to (I : ExecutionEnv) :
    (burnStore I).get? "to" = some (burnToValue I) := by
  rw [burnStore, store_get_self]

theorem burnStore_balanceOf (I : ExecutionEnv) :
    (burnStore I).get? "balanceOf" = none := by
  rw [burnStore, store_get_ne _ _ (by decide)]
  simp

/-! ## EVM wrapper prefix -/

/-- The optimized external wrapper for `burn(address)` masks legacy-address calldata and jumps to
    the external burn routine at pc 4093. -/
theorem uniswapBurnX_decoded_masked {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hreach : ∃ k C, RD uniswapV2PairBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1163⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD uniswapV2PairBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4093⟩
      [burnToMaskedWord I, ⟨1201⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd1185⟩ := RD.uniswapOneAddressExternalLenOk
    (entry := ⟨1163⟩) (ret := ⟨1201⟩) (routine := ⟨4093⟩) hreach
    uniswap_one_address_external_entry_wf (by jump_dest) hsz36 hsize
  obtain ⟨_, _, rd4093⟩ := RD.uniswapOneAddressExternalMaskAndJumpMasked
    (entry := ⟨1163⟩) (ret := ⟨1201⟩) (routine := ⟨4093⟩) (R := [sel])
    rd1185 uniswap_one_address_external_entry_wf (by jump_dest)
    (by simp only [List.length_singleton]; omega)
  exact ⟨_, _, by simpa [burnToWord, burnToMaskedWord] using rd4093⟩

/-- Short-calldata path for `burn(address)` from the dispatcher body entry. -/
theorem uniswapBurnX_shortarg {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 36)
    (hreach : ∃ k C, RD uniswapV2PairBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1163⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev uniswapV2PairBytecode g (initState cA gh bl σ σ₀ g A I) := by
  exact RD.uniswapOneAddressExternalShort
    (entry := ⟨1163⟩) (ret := ⟨1201⟩) (routine := ⟨4093⟩)
    hreach uniswap_one_address_external_entry_wf hsz4 hsize hshort

/-- After the external wrapper has decoded `to`, `burn(address)` reverts when the Uniswap lock is
already held. -/
theorem uniswapBurnX_locked {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hlocked :
      (σ.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD ⟨12⟩ ⟨0⟩)) ≠
        ⟨1⟩)
    (hdecoded : ∃ k C, RD uniswapV2PairBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨4093⟩
      [burnToMaskedWord I, ⟨1201⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev uniswapV2PairBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd4093⟩ := hdecoded
  have rd4097 := evm_run rd4093 with [jumpdest, push1 ⟨0⟩, dup1]
  exact RD.uniswapLockEnterBodyLocked
    (okPc := ⟨4171⟩)
    (R := [⟨0⟩, ⟨0⟩, burnToMaskedWord I, ⟨1201⟩, sel])
    rd4097 uniswap_lock_enter_body_guard_wf uniswap_lock_body_revert_tail_wf hlocked
    (by simp only [List.length_cons, List.length_nil]; omega)

/-- After the external wrapper has decoded `to`, `burn(address)` successfully enters the
Uniswap lock when it is not already held. -/
theorem uniswapBurnX_lockEntered {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hperm : I.perm = true)
    (hunlocked :
      (σ.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD ⟨12⟩ ⟨0⟩)) =
        ⟨1⟩)
    (hdecoded : ∃ k C, RD uniswapV2PairBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨4093⟩
      [burnToMaskedWord I, ⟨1201⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD uniswapV2PairBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4179⟩
      [⟨0⟩, ⟨0⟩, ⟨0⟩, burnToMaskedWord I, ⟨1201⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) k C := by
  obtain ⟨_, _, rd4093⟩ := hdecoded
  have rd4097 := evm_run rd4093 with [jumpdest, push1 ⟨0⟩, dup1]
  obtain ⟨_, _, rd4179⟩ := RD.uniswapLockEnterBodyOk
    (pc := ⟨4097⟩) (okPc := ⟨4171⟩)
    (R := [⟨0⟩, ⟨0⟩, burnToMaskedWord I, ⟨1201⟩, sel])
    rd4097 uniswap_lock_enter_body_ok_wf hperm hunlocked (by jump_dest)
      (by simp only [List.length_cons, List.length_nil]; omega)
  exact ⟨_, _, by simpa using rd4179⟩

theorem uniswapBurnBodyReverts_locked (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hlocked : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨12⟩ ≠ ⟨1⟩) :
    ExecTransitionBody config contract evm (burnStore I) burnTransition.body .reverted := by
  have hlock :=
    uniswapLockEnterLockedRevert evm (burnStore I) hwv (by simp [burnStore]) hlocked
  exact ExecFuncBody.execBlockRevert (by
    simpa [burnTransition, List.append_assoc] using
      (execBlock_append_term hlock (by intro f e h; cases h)))

theorem uniswapBurnBodyCoreDecodeFailed_short
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36)
    (hdispatch : dispatchMsg contract I.calldata = some burnTransition)
    (hreach : ∃ k C, RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1163⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hdec := uniswapDecode_burn_none_short (I := I) hsz4 hshort
  exact (uniswapBurnX_shortarg (g := Sat256.ofUInt256 g) hsz4 hsize hshort hreach)
    |>.reEquivDecodingFailed hcode hdispatch hdec

theorem uniswapBurnBodyCoreRevert_locked
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩) (hsz36 : 36 ≤ I.calldata.size)
    (hlocked :
      (σ_evm.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD ⟨12⟩ ⟨0⟩)) ≠
        ⟨1⟩)
    (hdispatch : dispatchMsg contract I.calldata = some burnTransition)
    (hreach : ∃ k C, RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1163⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let evmS := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hlockedSolm :
      Solm.EVM.storageLoad evmS evmS.executionEnv.codeOwner ⟨12⟩ ≠ ⟨1⟩ := by
    simpa [evmS] using
      (initState_codeOwner_storageLoad_ne_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
        (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
        (slot := ⟨12⟩) (val := ⟨1⟩) hAccounts hlocked)
  have hbody :
      ExecTransitionBody config contract evmS (burnStore I) burnTransition.body .reverted := by
    exact uniswapBurnBodyReverts_locked evmS I
      (by simp only [evmS, initState]; exact hwv)
      hlockedSolm
  exact (uniswapBurnX_locked (g := Sat256.ofUInt256 g) hlocked
      (uniswapBurnX_decoded_masked (g := Sat256.ofUInt256 g) hsz36 hsize hreach))
    |>.reEquivExecutionRevert hcode hdispatch (uniswapDecode_burn_ok hsz36) hbody

theorem uniswapBurnBodyDecodeFailed_short
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩) (hsel : selIs I ⟨#[0x89, 0xaf, 0xcb, 0x44]⟩)
    (hshort : I.calldata.size < 36)
    (hdispatch : dispatchMsg contract I.calldata = some burnTransition) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I ⟨#[0x89, 0xaf, 0xcb, 0x44]⟩ rfl hsel
  exact uniswapBurnBodyCoreDecodeFailed_short hcode hsize hsz4 hshort hdispatch
    (uniswapReachBurnBody (g := Sat256.ofUInt256 g) hcode hwv hsz4 hsize hsel)

theorem uniswapBurnBodyRevert_locked
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩) (hsel : selIs I ⟨#[0x89, 0xaf, 0xcb, 0x44]⟩)
    (hsz36 : 36 ≤ I.calldata.size)
    (hlocked :
      (σ_evm.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD ⟨12⟩ ⟨0⟩)) ≠
        ⟨1⟩)
    (hdispatch : dispatchMsg contract I.calldata = some burnTransition)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I ⟨#[0x89, 0xaf, 0xcb, 0x44]⟩ rfl hsel
  exact uniswapBurnBodyCoreRevert_locked hcode hsize hwv hsz36 hlocked hdispatch
    (uniswapReachBurnBody (g := Sat256.ofUInt256 g) hcode hwv hsz4 hsize hsel)
    hAccounts

end UniswapV2Pair
