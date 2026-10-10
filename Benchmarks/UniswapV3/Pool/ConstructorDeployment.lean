import Benchmarks.UniswapV3.Pool.ConstructorSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool

theorem constructorDeploymentShape (args : List Value) (code : ByteArray)
    (hdeploy : config.selfDeployment uniswapV3PoolCreationBytecode args = some code) :
    args = [] ∧ code = uniswapV3PoolCreationBytecode := by
  change genSolidityConstructorDeployment [] uniswapV3PoolCreationBytecode args = some code at hdeploy
  have hh : abiTupleHeadSize? [] = some 0 := abiTupleHeadSize_scalarWords_eq rfl
  cases args with
  | nil =>
    simp only [genSolidityConstructorDeployment, List.map_nil, encodeABIValues?, hh,
      encodeABIValuesFrom?, bind, Option.bind, pure, List.nil_append] at hdeploy
    have hz : ([] : List UInt8).toByteArray = ByteArray.empty := rfl
    rw [hz, ByteArray.append_empty] at hdeploy
    exact ⟨rfl, (Option.some.inj hdeploy).symm⟩
  | cons x xs =>
    simp only [genSolidityConstructorDeployment, List.map_nil, encodeABIValues?, hh,
      encodeABIValuesFrom?, bind, Option.bind, pure] at hdeploy
    cases hdeploy

theorem constructorSolmExec {σ σ₀ : AccountMap} {g : UInt256} {A : Substate}
    {I : ExecutionEnv} {result : ExecResult}
    (hbody : ExecFuncBody config constructorInitialFrame
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) contract.ctor.body result) :
    solmCtorExec config contract [] σ σ₀ g A I result := by
  refine solmCtorExec.intro
    (evmState := initState σ σ₀ (Sat256.ofUInt256 g) A I)
    (argsStore := ∅) rfl rfl ?_ hbody
  rfl

end Benchmarks.UniswapV3.Pool
