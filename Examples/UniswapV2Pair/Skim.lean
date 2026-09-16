import Examples.UniswapV2Pair.SkimDecoded

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace UniswapV2Pair

theorem uniswapSkimBody
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xbc, 0x25, 0xcf, 0x77]⟩)
    (hdispatch : dispatchMsg contract I.calldata = some skimTransition)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  by_cases hsz36 : 36 ≤ I.calldata.size
  · have hdecode : decodeCalldataWithMode config.abiDecodeMode
        (skimTransition.params.map Param.name)
        (transitionSignature skimTransition).paramTypes I.calldata = some (skimStore I) := by
      show decodeCalldataWithMode config.abiDecodeMode ["to"] [legacyAddr] I.calldata = _
      simpa only [skimStore, skimToValue, skimToWord, calldataWord]
        using decodeCalldata_legacyAddress_ok (cd := I.calldata) (x := "to") hsz36
    exact uniswapSkimBodyDecoded hcode hsize hperm hwv hsel hdispatch hAccounts hsz36 hdecode
  · exact uniswapSkimBodyDecodeFailed_short hcode hsize hwv hsel (by omega) hdispatch

end UniswapV2Pair
