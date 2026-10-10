import Benchmarks.Morpho.MetaMorphoV1_1.Dispatch
import Benchmarks.Morpho.MetaMorphoV1_1.MarketRemovalEntry
import Benchmarks.Morpho.MetaMorphoV1_1.MarketRemovalGuards
import Benchmarks.Morpho.MetaMorphoV1_1.MarketRemovalStore
import Benchmarks.Morpho.MetaMorphoV1_1.MarketRemovalSource
import Benchmarks.Morpho.MetaMorphoV1_1.Mutation

/-!
# MetaMorphoV1_1 `submitMarketRemoval((address,address,address,address,uint256))`

Per-function proof: calldata decode facts, the EVM trace from the dispatcher arm through the
body, the Solm body evaluation, and the `…Body` theorem `Correct.lean` consumes.
Dispatcher arm entry: pc 5196; reach lemma `metaMorphoV1_1ReachSubmitMarketRemovalBody`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option maxRecDepth 2000

/-- `submitMarketRemoval((address,address,address,address,uint256))`: the theorem `Correct.lean` routes selector 39 to. -/
theorem metaMorphoV1_1SubmitMarketRemovalBody {σ σ₀ A I} {g : UInt256} (v : MetaMorphoV1_1Immutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (metaMorphoV1_1SelBytes 39)) :
    runtimeRefinementFor config contract σ σ₀ g A I (immStore v) := by
  have hsz : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (metaMorphoV1_1SelBytes 39) rfl hsel
  have hd : dispatchMsg contract I.calldata = some submitMarketRemovalTransition := by
    apply metaMorphoV1_1Dispatch_submitMarketRemoval <;>
      first | exact hsel | exact selectorMismatch hsel (by decide +kernel)
  obtain ⟨k, C, rd⟩ := metaMorphoV1_1ReachSubmitMarketRemovalBody
    (σ := σ) (σ₀ := σ₀) (A := A) (g := Sat256.ofUInt256 g) v hcode hsz hsize hsel
  by_cases hwv : I.weiValue = ⟨0⟩
  case neg =>
    exact dispatchedRevert hcode hd (marketRemovalNonpayable v (by simp) hwv rd)
      (fun _ ↦ bodyReverts_nonPayable hwv)
  rcases marketRemovalDecode v (by simp) hwv hsz hsize solcFreePtrMem_mload64
    (by decide +kernel) rd with ⟨hc, hrev⟩ | ⟨hc, aw1, k1, C1, r1⟩
  · have hdec := marketParamsCalldataDecode I.calldata "marketParams"
    simp only [hc, if_false] at hdec
    exact hrev.reEquivDecodingFailed hcode hd hdec
  · have hdec := marketParamsCalldataDecode I.calldata "marketParams"
    simp only [hc, if_true] at hdec
    let evm := initState σ σ₀ (Sat256.ofUInt256 g) A I
    let args := marketParamsArgs I.calldata
    by_cases hrole : curatorRoleAllowed evm
    case neg =>
      have hrev := marketRemovalRoleRevert (evm := evm) v (by simp) hrole r1
      exact hrev.reEquivExecutionRevert hcode hd hdec
        (marketRemovalBodyRevertsRole evm (immStore v) args hwv hc.1 hrole)
    obtain ⟨k2, C2, r2⟩ := marketRemovalRolePass (evm := evm) v (by simp) hrole r1
    rcases marketRemovalGuardsReach (evm := evm) v (by simp)
      (marketParamsCalldataMemory_hash _ _ _ hc) r2 with
      ⟨hbad, hrev⟩ | ⟨hgood, mem3, aw3, k3, C3, r3⟩
    · exact hrev.reEquivExecutionRevert hcode hd hdec
        (marketRemovalBodyRevertsGuards evm (immStore v) args hwv hc.1 hrole hbad)
    · rcases marketRemovalSchedule (evm := evm) v (by simp) r3 with
        ⟨hfit, hrev⟩ | ⟨hfit, hperm, hstatic⟩ | ⟨hfit, _hperm, hret⟩
      · exact hrev.reEquivExecutionRevert hcode hd hdec
          (marketRemovalBodyRevertsOverflow evm (immStore v) args hwv hc.1 hrole hgood hfit)
      · exact hstatic.reEquivStaticHalt hcode hd hdec
          (marketRemovalBodyStatic evm (immStore v) args hwv hc.1 hrole hgood hfit hperm)
      · obtain ⟨final, hbody⟩ := marketRemovalBodyReturns evm (immStore v) args
          hwv hc.1 hrole hgood hfit
        exact hret.reEquivExecutionGen hcode hd hdec hbody rfl voidReturnEquiv

end Benchmarks.Morpho.MetaMorphoV1_1
