import Benchmarks.Morpho.MetaMorphoV1_1.Dispatch
import Benchmarks.Morpho.MetaMorphoV1_1.SubmitCapEntry
import Benchmarks.Morpho.MetaMorphoV1_1.SubmitCapRole
import Benchmarks.Morpho.MetaMorphoV1_1.SubmitCapAsset
import Benchmarks.Morpho.MetaMorphoV1_1.SubmitCapPrefixSource
import Benchmarks.Morpho.MetaMorphoV1_1.SubmitCapTailSimulation
import Benchmarks.Morpho.MetaMorphoV1_1.LastUpdateSimulation
import Benchmarks.Morpho.MetaMorphoV1_1.MarketParamsCalldataMemory
import Benchmarks.Morpho.MetaMorphoV1_1.Mutation

/-!
# MetaMorphoV1_1 `submitCap((address,address,address,address,uint256),uint256)`

Per-function proof: calldata decode facts, the EVM trace from the dispatcher arm through the
body, the Solm body evaluation, and the `…Body` theorem `Correct.lean` consumes.
Dispatcher arm entry: pc 8864; reach lemma `metaMorphoV1_1ReachSubmitCapBody`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables

namespace Benchmarks.Morpho.MetaMorphoV1_1

open SourceMemory

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option maxRecDepth 2000

/-- `submitCap((address,address,address,address,uint256),uint256)`: the theorem `Correct.lean` routes selector 18 to. -/
theorem metaMorphoV1_1SubmitCapBody {σ σ₀ A I} {g : UInt256} (v : MetaMorphoV1_1Immutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (metaMorphoV1_1SelBytes 18)) :
    runtimeRefinementFor config contract σ σ₀ g A I (immStore v) := by
  have hsz : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (metaMorphoV1_1SelBytes 18) rfl hsel
  have hd : dispatchMsg contract I.calldata = some submitCapTransition := by
    apply metaMorphoV1_1Dispatch_submitCap <;>
      first | exact hsel | exact selectorMismatch hsel (by decide +kernel)
  obtain ⟨k, C, rd⟩ := metaMorphoV1_1ReachSubmitCapBody
    (σ := σ) (σ₀ := σ₀) (A := A) (g := Sat256.ofUInt256 g) v hcode hsz hsize hsel
  by_cases hwv : I.weiValue = ⟨0⟩
  case neg =>
    exact dispatchedRevert hcode hd (submitCapNonpayable v (by simp) hwv rd)
      (fun _ ↦ bodyReverts_nonPayable hwv)
  rcases submitCapDecode v (by simp) hwv hsz hsize solcFreePtrMem_mload64
    (by decide +kernel) rd with ⟨hc, hrev⟩ | ⟨hc, aw1, k1, C1, r1⟩
  · have hdec := submitCapCalldataDecode I.calldata
    simp only [hc, if_false] at hdec
    exact hrev.reEquivDecodingFailed hcode hd hdec
  · have hdec := submitCapCalldataDecode I.calldata
    simp only [hc, if_true] at hdec
    let evm := initState σ σ₀ (Sat256.ofUInt256 g) A I
    let args := marketParamsArgs I.calldata
    let p := marketParamsData args
    let cap := calldataWord I.calldata 164
    let mem1 := marketParamsCalldataMemory solcFreePtrMem ⟨128⟩ I.calldata
    have hm1 : 288 ≤ mem1.size :=
      marketParamsCalldataMemory_size solcFreePtrMem ⟨128⟩ I.calldata
    have hl1 : MarketParamsLoads mem1 ⟨128⟩ p :=
      marketParamsCalldataMemory_loads _ _ _ hc.2 (by decide)
    rcases submitCapRoleReach (evm := evm) v (by simp) r1 with
      ⟨hbad, hrev⟩ | ⟨hrole, k2, C2, r2⟩
    · exact hrev.reEquivExecutionRevert hcode hd hdec (by
        rw [submitCapBody_eq]
        exact submitCapBodyRoleReverts v evm args cap hwv hc.2.1 hbad)
    rcases submitCapAssetReach (mem := mem1) (params := ⟨128⟩) v p (by simp) hl1
      (marketParamsCalldataMemory_hash _ _ _ hc.2) r2 with
      ⟨hbad, hrev⟩ | ⟨ha, aw3, k3, C3, r3⟩
    · exact hrev.reEquivExecutionRevert hcode hd hdec (by
        rw [submitCapBody_eq]
        exact submitCapBodyAssetReverts v evm args cap hwv hc.2.1 hrole hbad)
    have hs : SourceState evm I σ evm := SourceState.init
    rcases lastUpdateSimulation (params := ⟨128⟩) (ptr := ⟨288⟩) (mem := mem1) v
      (by simp) hsize (marketParamsCalldataMemory_free _ _ _ (by decide)) (by decide)
      (by decide +kernel) hs r3 with
      ⟨hsource, hrev⟩ |
        ⟨evm', final, value, cursor, first, mem', out, hsource, hs', _, hf, hlo, _, hm,
          hpres, hmono, hlast, aw4, k4, C4, r4⟩
    · exact hrev.reEquivExecutionRevert hcode hd hdec (by
        rw [submitCapBody_eq]
        exact submitCapBodyReaderReverts v evm args cap hwv hc.2.1 hrole ha hsource)
    have hb : mem'.readWithPadding 128 160 = p.bytes := by
      rw [memoryPrefix_read_words hpres 5 128 (by decide) (by decide) hm1]
      exact marketParamsCalldataMemory_bytes _ _ _ hc.2
    have hl : MarketParamsLoads mem' ⟨128⟩ p :=
      hl1.prefix hpres (by decide) hm1 (by decide) (by decide)
    have hcompose (result : ExecResult)
        (htail : ExecBlock config (submitCapResultFrame v evm args cap value cursor) evm'
          (submitCapGuards ++ [submitCapBranch]) result) :
        ExecBlock config ⟨contract, submitCapInitialLocals args cap, immStore v⟩ evm
          submitCapBody result :=
      submitCapReaderContinue v evm evm' args cap value cursor final hwv hc.2.1 hrole ha
        hsource htail
    rcases submitCapTailSimulation (params := ⟨128⟩) (ptr := cursor) v (by simp)
      (submitCapResultFrame_ready v evm args cap value cursor) rfl hsize hf hlo hm
      (by decide) hmono hb hl hs' hlast r4 with
      ⟨htail, hrev⟩ | ⟨htail, hstatic⟩ | ⟨evm'', final', hs'', htail, hret⟩
    · exact hrev.reEquivExecutionRevert hcode hd hdec (by
        rw [submitCapBody_eq]
        exact ExecFuncBody.execBlockRevert (hcompose .reverted htail))
    · exact hstatic.reEquivStaticHalt hcode hd hdec (by
        rw [submitCapBody_eq]
        exact ExecFuncBody.execBlockStatic (hcompose .staticViolation htail))
    · exact hret.reEquivExecutionGen hcode hd hdec (by
        rw [submitCapBody_eq]
        exact ExecFuncBody.execBlockOK (hcompose (.ok final' evm'') htail)) rfl voidReturnEquiv

end Benchmarks.Morpho.MetaMorphoV1_1
