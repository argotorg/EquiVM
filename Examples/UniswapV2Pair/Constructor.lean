import Examples.UniswapV2Pair.ConstructorCode
import Reasoning.Constructor

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace UniswapV2Pair

theorem uniswapConstructorBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = uniswapV2PairInitcode)
    (hcalldata : I.calldata = ByteArray.empty) (hperm : I.perm = true)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    constructorEquivalenceFor config contract [] cA gh bl σ_evm σ_solm σ₀ g A I
      uniswapV2PairBytecode := by
  sorry

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
