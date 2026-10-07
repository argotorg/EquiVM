import Examples.UniswapV2Pair.SkimDecoded

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace UniswapV2Pair

theorem uniswapSkimBody
    {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xbc, 0x25, 0xcf, 0x77]⟩)
    (hdispatch : dispatchMsg contract I.calldata = some skimTransition) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  by_cases hsz36 : 36 ≤ I.calldata.size
  · have hdecode : decodeCalldataWithMode config.abiDecodeMode
        (skimTransition.params.map Param.name)
        (transitionSignature skimTransition).paramTypes I.calldata = some (skimStore I) := by
      show decodeCalldataWithMode config.abiDecodeMode ["to"] [legacyAddr] I.calldata = _
      simpa only [skimStore, skimToValue, skimToWord, calldataWord]
        using decodeCalldata_legacyAddress_ok (cd := I.calldata) (x := "to") hsz36
    exact uniswapSkimBodyDecoded hcode hsize hperm hwv hsel hdispatch hsz36 hdecode
  · exact uniswapSkimBodyDecodeFailed_short hcode hsize hwv hsel (by omega) hdispatch

/-- `skim` with any call permission; a static call halts at the lock-entry `SSTORE`. -/
theorem uniswapSkimBodyAnyPerm
    {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xbc, 0x25, 0xcf, 0x77]⟩)
    (hdispatch : dispatchMsg contract I.calldata = some skimTransition) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  by_cases hperm : I.perm = true
  · exact uniswapSkimBody hcode hsize hperm hwv hsel hdispatch
  replace hperm : I.perm = false := by simpa using hperm
  by_cases hsz36 : 36 ≤ I.calldata.size
  · have hdecode : decodeCalldataWithMode config.abiDecodeMode
        (skimTransition.params.map Param.name)
        (transitionSignature skimTransition).paramTypes I.calldata = some (skimStore I) := by
      show decodeCalldataWithMode config.abiDecodeMode ["to"] [legacyAddr] I.calldata = _
      simpa only [skimStore, skimToValue, skimToWord, calldataWord]
        using decodeCalldata_legacyAddress_ok (cd := I.calldata) (x := "to") hsz36
    have hsz4 : 4 ≤ I.calldata.size :=
      calldata_size_ge_of_selIs I ⟨#[0xbc, 0x25, 0xcf, 0x77]⟩ rfl hsel
    have hdecoded :=
      uniswapSkimX_decoded_masked
        (σ := σ) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hsz36 hsize
        (uniswapReachSkimBody
          (σ := σ) (σ₀ := σ₀) (A := A)
          (I := I) (g := Sat256.ofUInt256 g) hcode hwv hsz4 hsize hsel)
    by_cases hlocked :
      (σ.get? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.getD ⟨12⟩ ⟨0⟩)) ≠ ⟨1⟩
    · exact uniswapSkimBodyRevert_locked
        (fun w : UInt256 => UInt256.land solcAddrMask w) hcode hwv hlocked hdispatch
        hdecode
        (uniswapSkimX_locked (g := Sat256.ofUInt256 g)
          (toWord := skimToMaskedWord I) hlocked hdecoded)
    · have hunlocked := not_not.mp hlocked
      let evmS := initState σ σ₀ (Sat256.ofUInt256 g) A I
      have hunlockedSolm :
          Solm.EVM.storageLoad evmS evmS.executionEnv.codeOwner ⟨12⟩ = ⟨1⟩ := by
        simpa [evmS, initState, Solm.EVM.storageLoad, State.lookupAccount,
          Account.lookupStorage] using hunlocked
      exact (uniswapSkimX_lockEnteredStatic hperm hunlocked hdecoded).reEquivStaticHalt
        hcode hdispatch hdecode
        (uniswapSkimBodyStatic evmS I (by simp only [evmS, initState]; exact hwv)
          hunlockedSolm (by simp only [evmS, initState]; exact hperm))
  · exact uniswapSkimBodyDecodeFailed_short hcode hsize hwv hsel (by omega) hdispatch

end UniswapV2Pair
