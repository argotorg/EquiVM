import Benchmarks.UniswapV3.Pool.ConstructorDeployment
import Benchmarks.UniswapV3.Pool.ConstructorImmutables

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool

-- GENERALIZES RDret.xiResult to a final account map that may differ from the initial map.
theorem constructorReturnXi {σ σ₀ σ' : AccountMap} {A : Substate} {I : ExecutionEnv}
    {g : UInt256} {code out : ByteArray} (hcode : I.code = code)
    (rd : RDret code (.ofUInt256 g) (initState σ σ₀ (.ofUInt256 g) A I) σ' out) :
    Ξ σ σ₀ g A I = .error .OutOfGass ∨
      ∃ g' A', Ξ σ σ₀ g A I = .ok (.success (σ', g', A') out) := by
  rcases rd with hg | ⟨s, hr, ha⟩
  · exact Or.inl (Xi_error_of_X (by simpa only [hcode] using hg))
  · have hx := Xi_success_of_X (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
      (s' := s) (o := out) (by simpa only [hcode] using hr)
    rw [ha] at hx
    exact Or.inr ⟨_, _, hx⟩

theorem constructorRefinesRevert {σ σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv}
    {g : UInt256} {code : ByteArray} (hcode : I.code = code)
    (rd : RDrev code (.ofUInt256 g) (initState σ σ₀ (.ofUInt256 g) A I))
    (hs : ExecFuncBody config constructorInitialFrame (initState σ σ₀ (.ofUInt256 g) A I)
      contract.ctor.body .reverted) :
    typedConstructorRefinementFor config contract [] σ σ₀ g A I
      (immutableLayout.deployed uniswapV3PoolBytecode) := by
  rcases rd with hg | ⟨g', out, hr⟩
  · exact .outOfGas (Xi_error_of_X (by simpa only [hcode] using hg))
  · exact .execution (Xi_revert_of_X (by simpa only [hcode] using hr))
      (constructorSolmExec hs) (.revert rfl rfl) trivial

theorem constructorRefinesInvalid {σ σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv}
    {g : UInt256} {code : ByteArray} (hcode : I.code = code)
    (rd : RDinvalid code (.ofUInt256 g) (initState σ σ₀ (.ofUInt256 g) A I))
    (hs : ExecFuncBody config constructorInitialFrame (initState σ σ₀ (.ofUInt256 g) A I)
      contract.ctor.body .reverted) :
    typedConstructorRefinementFor config contract [] σ σ₀ g A I
      (immutableLayout.deployed uniswapV3PoolBytecode) := by
  rcases rd with hg | hi
  · exact .outOfGas (Xi_error_of_X (by simpa only [hcode] using hg))
  · exact .execution (Xi_error_of_X (by simpa only [hcode] using hi))
      (constructorSolmExec hs) (.invalidHalt rfl rfl) trivial

theorem constructorRefinesReturn {σ σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv}
    {g : UInt256} {code out : ByteArray} {evm' : EVM.State} (hcode : I.code = code)
    (rd : RDret code (.ofUInt256 g) (initState σ σ₀ (.ofUInt256 g) A I) evm'.accountMap
      (deployedRuntime (constructorValuation I.codeOwner out)))
    (hs : ExecFuncBody config constructorInitialFrame (initState σ σ₀ (.ofUInt256 g) A I)
      contract.ctor.body (.returned (constructorFinalFrame I.codeOwner out) evm' none)) :
    typedConstructorRefinementFor config contract [] σ σ₀ g A I
      (immutableLayout.deployed uniswapV3PoolBytecode) := by
  rcases constructorReturnXi hcode rd with hg | ⟨g', A', hr⟩
  · exact .outOfGas hg
  · exact .execution hr (constructorSolmExec hs)
      (.success rfl rfl rfl (constructorFinalDeployed I.codeOwner out).symm)
      (constructorFinalFit I.codeOwner out)

end Benchmarks.UniswapV3.Pool
