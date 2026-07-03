import Examples.UniswapV2Pair.ExternalWrappers
import Examples.UniswapV2Pair.MathRoutines
import Examples.UniswapV2Pair.MintRoutines
import Examples.UniswapV2Pair.MutatorDispatch
import Reasoning.Refinement

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

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

/-! ## EVM wrapper prefix -/

/-- The optimized external wrapper for `mint(address)` masks legacy-address calldata and jumps to
    the external mint routine at pc 3283. -/
theorem uniswapMintX_decoded_masked {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hreach : ∃ k C, RD uniswapV2PairBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1041⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD uniswapV2PairBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3283⟩
      [mintToMaskedWord I, ⟨861⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd1063⟩ := RD.uniswapOneAddressExternalLenOk
    (entry := ⟨1041⟩) (ret := ⟨861⟩) (routine := ⟨3283⟩) hreach
    uniswap_one_address_external_entry_wf (by jump_dest) hsz36 hsize
  obtain ⟨_, _, rd3283⟩ := RD.uniswapOneAddressExternalMaskAndJumpMasked
    (entry := ⟨1041⟩) (ret := ⟨861⟩) (routine := ⟨3283⟩) (R := [sel])
    rd1063 uniswap_one_address_external_entry_wf (by jump_dest)
    (by simp only [List.length_singleton]; omega)
  exact ⟨_, _, by simpa [mintToWord, mintToMaskedWord] using rd3283⟩

/-- Short-calldata path for `mint(address)` from the dispatcher body entry. -/
theorem uniswapMintX_shortarg {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 36)
    (hreach : ∃ k C, RD uniswapV2PairBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1041⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev uniswapV2PairBytecode g (initState cA gh bl σ σ₀ g A I) := by
  exact RD.uniswapOneAddressExternalShort
    (entry := ⟨1041⟩) (ret := ⟨861⟩) (routine := ⟨3283⟩)
    hreach uniswap_one_address_external_entry_wf hsz4 hsize hshort

/-- After the external wrapper has decoded `to`, `mint(address)` reverts when the Uniswap lock is
already held. -/
theorem uniswapMintX_locked {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hlocked :
      (σ.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD ⟨12⟩ ⟨0⟩)) ≠
        ⟨1⟩)
    (hdecoded : ∃ k C, RD uniswapV2PairBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨3283⟩
      [mintToMaskedWord I, ⟨861⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev uniswapV2PairBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd3283⟩ := hdecoded
  have rd3286 := evm_run rd3283 with [jumpdest, push1 ⟨0⟩]
  exact RD.uniswapLockEnterBodyLocked
    (okPc := ⟨3360⟩) (R := [⟨0⟩, mintToMaskedWord I, ⟨861⟩, sel])
    rd3286 uniswap_lock_enter_body_guard_wf uniswap_lock_body_revert_tail_wf hlocked
    (by simp only [List.length_cons, List.length_nil]; omega)

/-- After the external wrapper has decoded `to`, `mint(address)` successfully enters the
Uniswap lock when it is not already held. -/
theorem uniswapMintX_lockEntered {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hperm : I.perm = true)
    (hunlocked :
      (σ.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD ⟨12⟩ ⟨0⟩)) =
        ⟨1⟩)
    (hdecoded : ∃ k C, RD uniswapV2PairBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨3283⟩
      [mintToMaskedWord I, ⟨861⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD uniswapV2PairBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3368⟩
      [⟨0⟩, ⟨0⟩, mintToMaskedWord I, ⟨861⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) k C := by
  obtain ⟨_, _, rd3283⟩ := hdecoded
  have rd3286 := evm_run rd3283 with [jumpdest, push1 ⟨0⟩]
  obtain ⟨_, _, rd3368⟩ := RD.uniswapLockEnterBodyOk
    (pc := ⟨3286⟩) (okPc := ⟨3360⟩)
    (R := [⟨0⟩, mintToMaskedWord I, ⟨861⟩, sel])
    rd3286 uniswap_lock_enter_body_ok_wf hperm hunlocked (by jump_dest)
      (by simp only [List.length_cons, List.length_nil]; omega)
  exact ⟨_, _, by simpa using rd3368⟩

theorem uniswapMintBodyReverts_locked (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hlocked : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨12⟩ ≠ ⟨1⟩) :
    ExecTransitionBody config contract evm (mintStore I) mintTransition.body .reverted := by
  have hlock :=
    uniswapLockEnterLockedRevert evm (mintStore I) hwv (by simp [mintStore]) hlocked
  exact ExecFuncBody.execBlockRevert (by
    simpa [mintTransition, List.append_assoc] using
      (execBlock_append_term hlock (by intro f e h; cases h)))

theorem uniswapMintBodyCoreDecodeFailed_short
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36)
    (hdispatch : dispatchMsg contract I.calldata = some mintTransition)
    (hreach : ∃ k C, RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1041⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hdec := uniswapDecode_mint_none_short (I := I) hsz4 hshort
  exact (uniswapMintX_shortarg (g := Sat256.ofUInt256 g) hsz4 hsize hshort hreach)
    |>.reEquivDecodingFailed hcode hdispatch hdec

theorem uniswapMintBodyCoreRevert_locked
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩) (hsz36 : 36 ≤ I.calldata.size)
    (hlocked :
      (σ_evm.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD ⟨12⟩ ⟨0⟩)) ≠
        ⟨1⟩)
    (hdispatch : dispatchMsg contract I.calldata = some mintTransition)
    (hreach : ∃ k C, RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1041⟩ [sel]
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
      ExecTransitionBody config contract evmS (mintStore I) mintTransition.body .reverted := by
    exact uniswapMintBodyReverts_locked evmS I
      (by simp only [evmS, initState]; exact hwv)
      hlockedSolm
  exact (uniswapMintX_locked (g := Sat256.ofUInt256 g) hlocked
      (uniswapMintX_decoded_masked (g := Sat256.ofUInt256 g) hsz36 hsize hreach))
    |>.reEquivExecutionRevert hcode hdispatch (uniswapDecode_mint_ok hsz36) hbody

theorem uniswapMintBodyDecodeFailed_short
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩) (hsel : selIs I ⟨#[0x6a, 0x62, 0x78, 0x42]⟩)
    (hshort : I.calldata.size < 36)
    (hdispatch : dispatchMsg contract I.calldata = some mintTransition) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I ⟨#[0x6a, 0x62, 0x78, 0x42]⟩ rfl hsel
  exact uniswapMintBodyCoreDecodeFailed_short hcode hsize hsz4 hshort hdispatch
    (uniswapReachMintBody (g := Sat256.ofUInt256 g) hcode hwv hsz4 hsize hsel)

theorem uniswapMintBodyRevert_locked
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩) (hsel : selIs I ⟨#[0x6a, 0x62, 0x78, 0x42]⟩)
    (hsz36 : 36 ≤ I.calldata.size)
    (hlocked :
      (σ_evm.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD ⟨12⟩ ⟨0⟩)) ≠
        ⟨1⟩)
    (hdispatch : dispatchMsg contract I.calldata = some mintTransition)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I ⟨#[0x6a, 0x62, 0x78, 0x42]⟩ rfl hsel
  exact uniswapMintBodyCoreRevert_locked hcode hsize hwv hsz36 hlocked hdispatch
    (uniswapReachMintBody (g := Sat256.ofUInt256 g) hcode hwv hsz4 hsize hsel)
    hAccounts

theorem uniswapMintBody
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x6a, 0x62, 0x78, 0x42]⟩)
    (hdispatch : dispatchMsg contract I.calldata = some mintTransition)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  by_cases hsz36 : 36 ≤ I.calldata.size
  · by_cases hlocked :
      (σ_evm.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD ⟨12⟩ ⟨0⟩)) ≠
        ⟨1⟩
    · exact uniswapMintBodyRevert_locked hcode hsize hwv hsel hsz36 hlocked hdispatch
        hAccounts
    · have hunlocked :
        (σ_evm.find? I.codeOwner |>.option ⟨0⟩
          (fun acc => acc.storage.findD ⟨12⟩ ⟨0⟩)) =
          ⟨1⟩ := by
        exact not_not.mp hlocked
      have hsz4 : 4 ≤ I.calldata.size :=
        calldata_size_ge_of_selIs I ⟨#[0x6a, 0x62, 0x78, 0x42]⟩ rfl hsel
      have hreach : ∃ k C, RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
          (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1041⟩
          [uniswapSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
          (cA, σ_evm) k C :=
        uniswapReachMintBody (g := Sat256.ofUInt256 g) hcode hwv hsz4 hsize hsel
      have hdecoded := uniswapMintX_decoded_masked (g := Sat256.ofUInt256 g)
        hsz36 hsize hreach
      have hlockEntered := uniswapMintX_lockEntered (g := Sat256.ofUInt256 g)
        hperm hunlocked hdecoded
      let evmS := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
      have hunlockedSolm :
          Solm.EVM.storageLoad evmS evmS.executionEnv.codeOwner ⟨12⟩ = ⟨1⟩ := by
        have hword := accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨12⟩ ⟨0⟩
        simpa [evmS, initState] using hword.symm.trans hunlocked
      sorry
  · exact uniswapMintBodyDecodeFailed_short hcode hsize hwv hsel (by omega) hdispatch

end UniswapV2Pair
