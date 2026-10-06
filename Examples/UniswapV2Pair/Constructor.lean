import Examples.UniswapV2Pair.ConstructorCode
import Examples.UniswapV2Pair.ConstructorEntry
import Examples.UniswapV2Pair.ConstructorLiteralsRuntime
import Examples.UniswapV2Pair.ConstructorCoupling
import Examples.UniswapV2Pair.ConstructorStorageCoupling

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace UniswapV2Pair

theorem uniswapConstructorBodyCore
    {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = uniswapV2PairInitcode)
    (hperm : I.perm = true) :
    constructorEquivalenceFor config contract [] σ σ₀ g A I
      uniswapV2PairBytecode := by
  rcases uniswapConstructorEntryCases (σ := σ) (σ₀ := σ₀)
      (A := A) (g := Sat256.ofUInt256 g) hcode hperm with
    ⟨hwv, rdRev⟩ | ⟨hwv, _, _, rd23⟩
  · exact RDrev.constructorEquivalenceEmptyParams rdRev hcode rfl
      (uniswapConstructorSourceReverts _ hwv)
  · obtain ⟨_, _, rd49⟩ := RD.uniswapConstructorTypeHash rd23 (by decide)
    obtain ⟨_, _, rd100⟩ := RD.uniswapConstructorLiterals rd49 (by decide)
    obtain ⟨_, _, rd200⟩ := RD.uniswapConstructorDomainData rd100 (by decide)
    obtain ⟨_, _, rd225⟩ := RD.uniswapConstructorDomainHash rd200 (by decide)
    have rdRet := RD.uniswapConstructorStoreAndReturn rd225 hperm (by decide)
    let evmS := initState σ σ₀ (Sat256.ofUInt256 g) A I
    have hbody := uniswapConstructorSourceReturns evmS hwv
    have haL : sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨1⟩ =
        (uniswapLockExitedState evmS).accountMap := by
      simp only [uniswapLockExitedState, uniswapUnlockedState, storageStore_accountMap,
        evmS, initState]
    have heL : (uniswapLockExitedState evmS).executionEnv = I := by
      simp only [uniswapLockExitedState, uniswapUnlockedState, storageStore_executionEnv,
        evmS, initState]
    exact RDret.constructorEquivalenceEmptyParams rdRet hcode rfl hbody
      (constructorStoredAccountMap_eq heL haL)

theorem uniswapV2PairConstructorCorrect :
    constructorEquivalence config uniswapV2PairInitcode contract uniswapV2PairBytecode := by
  refine constructorEquivalence.intro ?_
  intro σ σ₀ g A I args deployedInitcode hdeploy hcode _hcalldata
    hperm
  have hargs := emptyCtorDeployment_args_length (cfg := config) (contract := contract)
    rfl rfl hdeploy
  have hargsNil : args = [] := by simpa [contract, constructorDecl] using hargs
  have hinit := emptyCtorDeployment_eq_initcode (cfg := config) (contract := contract)
    rfl rfl hdeploy
  subst args
  rw [hinit] at hcode
  exact uniswapConstructorBodyCore hcode hperm

end UniswapV2Pair
