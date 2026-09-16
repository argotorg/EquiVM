import Examples.UniswapV2Pair.ConstructorCode
import Examples.UniswapV2Pair.ConstructorEntry
import Examples.UniswapV2Pair.ConstructorLiteralsRuntime
import Examples.UniswapV2Pair.ConstructorCoupling
import Examples.UniswapV2Pair.ConstructorStorageCoupling

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace UniswapV2Pair

theorem uniswapConstructorBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = uniswapV2PairInitcode)
    (hcalldata : I.calldata = ByteArray.empty) (hperm : I.perm = true)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    constructorEquivalenceFor config contract [] cA gh bl σ_evm σ_solm σ₀ g A I
      uniswapV2PairBytecode := by
  rcases uniswapConstructorEntryCases (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
      (A := A) (g := Sat256.ofUInt256 g) hcode hperm with
    ⟨hwv, rdRev⟩ | ⟨hwv, _, _, rd23⟩
  · exact RDrev.constructorEquivalenceEmptyParams rdRev hcode rfl
      (uniswapConstructorSourceReverts _ hwv)
  · obtain ⟨_, _, rd49⟩ := RD.uniswapConstructorTypeHash rd23 (by decide)
    obtain ⟨_, _, rd100⟩ := RD.uniswapConstructorLiterals rd49 (by decide)
    obtain ⟨_, _, rd200⟩ := RD.uniswapConstructorDomainData rd100 (by decide)
    obtain ⟨_, _, rd225⟩ := RD.uniswapConstructorDomainHash rd200 (by decide)
    have rdRet := RD.uniswapConstructorStoreAndReturn rd225 hperm (by decide)
    let evmS := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
    have hbody := uniswapConstructorSourceReturns evmS hwv
    have haL : accountMapEquiv (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨1⟩)
        (uniswapLockExitedState evmS).accountMap := by
      simpa only [uniswapLockExitedState, uniswapUnlockedState, storageStore_accountMap,
        evmS, initState] using accountMapEquiv_sstoreAccountMap I.codeOwner ⟨12⟩ ⟨1⟩ hAccounts
    have heL : (uniswapLockExitedState evmS).executionEnv = I := by
      simp only [uniswapLockExitedState, uniswapUnlockedState, storageStore_executionEnv,
        evmS, initState]
    exact RDret.constructorEquivalenceEmptyParams rdRet hcode rfl hbody
      (by simp only [constructorFactoryState, constructorDomainState, uniswapLockExitedState,
        uniswapUnlockedState, storageStore_createdAccounts, evmS, initState])
      (constructorStoredAccountMap_equiv heL haL)

theorem uniswapV2PairConstructorCorrect :
    constructorEquivalence config uniswapV2PairInitcode contract uniswapV2PairBytecode := by
  refine constructorEquivalence.intro ?_
  intro cA gh bl σ_evm σ_solm σ₀ g A I args deployedInitcode hdeploy hcode hcalldata
    hperm hAccounts
  have hargs := emptyCtorDeployment_args_length (cfg := config) (contract := contract)
    rfl rfl hdeploy
  have hargsNil : args = [] := by simpa [contract, constructorDecl] using hargs
  have hinit := emptyCtorDeployment_eq_initcode (cfg := config) (contract := contract)
    rfl rfl hdeploy
  subst args
  rw [hinit] at hcode
  exact uniswapConstructorBodyCore hcode hcalldata hperm hAccounts

end UniswapV2Pair
