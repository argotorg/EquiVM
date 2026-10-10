import Benchmarks.UniswapV3.Pool.ConstructorResults
import Benchmarks.UniswapV3.Pool.ConstructorCallTrace
import Benchmarks.UniswapV3.Pool.ConstructorFieldsTrace
import Benchmarks.UniswapV3.Pool.ConstructorFinishTrace

/-!
# UniswapV3Pool constructor correctness

Creation-code equivalence: the constructor's EVM trace (argument decode, stores, runtime-code
return) against the Solm constructor body, composed from the creation summaries.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV3.Pool.Immutables

namespace Benchmarks.UniswapV3.Pool

set_option maxRecDepth 1000 in
theorem uniswapV3PoolConstructorCorrect :
    typedConstructorRefinement config uniswapV3PoolCreationBytecode contract (immutableLayout.deployed uniswapV3PoolBytecode) := by
  intro σ σ₀ g A I args deployed hdeploy hcode _ _
  obtain ⟨rfl, rfl⟩ := constructorDeploymentShape args deployed hdeploy
  have hcode' : I.code = uniswapV3PoolCreationBytecode ++ ByteArray.empty := by
    simpa only [ByteArray.append_empty] using hcode
  let evm := initState σ σ₀ (.ofUInt256 g) A I
  have rd0 := RD.initState (σ := σ) (σ₀ := σ₀) (A := A) (g := .ofUInt256 g) hcode'
  by_cases hwv : I.weiValue = ⟨0⟩
  swap
  · exact constructorRefinesRevert hcode' (constructorNonpayableX rd0 hwv)
      (constructorRevertsNonpayable evm hwv)
  obtain ⟨_, _, _, rguard⟩ := constructorZeroValueX rd0 hwv
  by_cases hc : extCodeSizeWord σ (UInt256.ofNat I.source.val) = ⟨0⟩
  · exact constructorRefinesRevert hcode' (constructorNoCodeX rguard hc)
      (constructorRevertsNoCode evm hwv hc)
  obtain ⟨_, _, _, _, rcall⟩ := constructorBeforeCallX rguard hc
  obtain ⟨ok, out, σ', A', _, _, _, hcall, rdata, hb⟩ :=
    constructorCallX (evm := evm) rcall SourceState.init
  cases ok with
  | false =>
    exact constructorRefinesRevert hcode' (constructorCallFailedX rdata)
      (constructorRevertsCall evm _ out hwv hc hcall)
  | true =>
    obtain ⟨_, _, rdecode⟩ := constructorCallSuccessX rdata
    by_cases hlen : 160 ≤ out.size
    swap
    · have hshort : out.size < 160 := by omega
      exact constructorRefinesRevert hcode' (constructorShortDataX rdecode hshort)
        (constructorRevertsShort evm _ out hwv hc hcall hshort)
    obtain ⟨_, _, _, rfields⟩ := constructorBeforeFieldsX rdecode hlen hb
    rcases constructorBeforeRuntimeX rfields hlen with ⟨ri, hi⟩ | ⟨hn, hcount, _, _, _, rfinish⟩
    · exact constructorRefinesInvalid hcode' ri
        (constructorRevertsSpacing evm _ out hwv hc hcall hlen hi)
    · exact constructorRefinesReturn hcode' (constructorFinishX rfinish hlen)
        (constructorReturns evm _ out hwv hc hcall hlen hn hcount)

end Benchmarks.UniswapV3.Pool
