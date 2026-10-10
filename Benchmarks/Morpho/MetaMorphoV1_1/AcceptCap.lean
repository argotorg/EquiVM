import Benchmarks.Morpho.MetaMorphoV1_1.Dispatch
import Benchmarks.Morpho.MetaMorphoV1_1.AcceptCapEntry
import Benchmarks.Morpho.MetaMorphoV1_1.AcceptCapGuards
import Benchmarks.Morpho.MetaMorphoV1_1.MarketParamsCalldataMemory
import Benchmarks.Morpho.MetaMorphoV1_1.SetCapSimulation
import Benchmarks.Morpho.MetaMorphoV1_1.Mutation
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_013

/-!
# MetaMorphoV1_1 `acceptCap((address,address,address,address,uint256))`

Per-function proof: calldata decode facts, the EVM trace from the dispatcher arm through the
body, the Solm body evaluation, and the `…Body` theorem `Correct.lean` consumes.
Dispatcher arm entry: pc 7259; reach lemma `metaMorphoV1_1ReachAcceptCapBody`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables

namespace Benchmarks.Morpho.MetaMorphoV1_1

open SourceMemory metaMorphoV1_1Blocks

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option maxRecDepth 2000

/-- `acceptCap((address,address,address,address,uint256))`: the theorem `Correct.lean` routes selector 30 to. -/
theorem metaMorphoV1_1AcceptCapBody {σ σ₀ A I} {g : UInt256} (v : MetaMorphoV1_1Immutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (metaMorphoV1_1SelBytes 30)) :
    runtimeRefinementFor config contract σ σ₀ g A I (immStore v) := by
  have hsz : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (metaMorphoV1_1SelBytes 30) rfl hsel
  have hd : dispatchMsg contract I.calldata = some acceptCapTransition := by
    apply metaMorphoV1_1Dispatch_acceptCap <;>
      first | exact hsel | exact selectorMismatch hsel (by decide +kernel)
  obtain ⟨k, C, rd⟩ := metaMorphoV1_1ReachAcceptCapBody
    (σ := σ) (σ₀ := σ₀) (A := A) (g := Sat256.ofUInt256 g) v hcode hsz hsize hsel
  by_cases hwv : I.weiValue = ⟨0⟩
  case neg =>
    exact dispatchedRevert hcode hd (acceptCapNonpayable v (by simp) hwv rd)
      (fun _ ↦ bodyReverts_nonPayable hwv)
  rcases acceptCapDecode v (by simp) hwv hsz hsize solcFreePtrMem_mload64
      (by decide +kernel) rd with ⟨hc, hrev⟩ | ⟨hc, aw1, k1, C1, r1⟩
  · have hdec := marketParamsCalldataDecode I.calldata "marketParams"
    simp only [hc, if_false] at hdec
    exact hrev.reEquivDecodingFailed hcode hd hdec
  · have hdec := marketParamsCalldataDecode I.calldata "marketParams"
    simp only [hc, if_true] at hdec
    let evm := initState σ σ₀ (Sat256.ofUInt256 g) A I
    let args := marketParamsArgs I.calldata
    let p := marketParamsData args
    let mem1 := marketParamsCalldataMemory solcFreePtrMem ⟨128⟩ I.calldata
    have hm1 : 288 ≤ mem1.size :=
      marketParamsCalldataMemory_size solcFreePtrMem ⟨128⟩ I.calldata
    rcases acceptCapGuardsReach (evm := evm) (params := ⟨128⟩) (mem := mem1)
        v (by simp) (by decide) hm1
        (marketParamsCalldataMemory_hash _ _ _ hc) r1 with
      ⟨hbad, hrev⟩ | ⟨hgood, aw2, k2, C2, r2⟩
    · exact hrev.reEquivExecutionRevert hcode hd hdec (by
        rw [acceptCapBody_eq]
        exact acceptCapBodyRevertsGuards evm (immStore v) args hwv hc.1 hbad)
    · let mem2 := acceptCapGuardMemory mem1 p.id
      have hp : MemoryPrefix mem1 mem2 288 := acceptCapGuardMemory_prefix mem1 p.id 288
      have hf : memLoad ⟨64⟩ mem2 = ⟨288⟩ :=
        (acceptCapGuardMemory_free p.id (by omega : 96 ≤ mem1.size)).trans
          (marketParamsCalldataMemory_free _ _ _ (by decide))
      have hm2 : 288 ≤ mem2.size := le_trans hm1 hp.size
      have hb : mem2.readWithPadding 128 160 = p.bytes := by
        rw [memoryPrefix_read_words hp 5 128 (by decide) (by decide) hm1]
        exact marketParamsCalldataMemory_bytes _ _ _ hc
      have hl : MarketParamsLoads mem2 ⟨128⟩ p :=
        (marketParamsCalldataMemory_loads _ _ _ hc (by decide)).prefix hp
          (by decide) hm1 (by decide) (by decide)
      have hs : SourceState evm I σ evm := SourceState.init
      rcases setCapSimulation (params := ⟨128⟩) (ptr := ⟨288⟩) (ret := ⟨1867⟩)
          v p (by simp) hsize (acceptCapValue_bound evm p.id)
          hf (by decide) hm2 (by decide) (by decide) hb hl hs
          (pendingCapPresent hgood.1)
          (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) r2 with
        ⟨hsource, hrev⟩ | ⟨hsource, hstatic⟩ |
          ⟨evm', final, cursor, mem', out, hs', hsource, aw3, k3, C3, r3⟩
      · exact hrev.reEquivExecutionRevert hcode hd hdec (by
          rw [acceptCapBody_eq]
          exact acceptCapBodyCalleeRevert evm (immStore v) args hwv hc.1 hgood hsource)
      · exact hstatic.reEquivStaticHalt hcode hd hdec (by
          rw [acceptCapBody_eq]
          exact acceptCapBodyCalleeStatic evm (immStore v) args hwv hc.1 hgood hsource)
      · obtain ⟨frame', hbody⟩ := acceptCapBodyCalleeReturns evm evm' (immStore v) args
          final cursor hwv hc.1 hgood hsource
        have hret := metaMorphoV1_1_block_1867 (immWords := wordsOf (immStore v))
          (by simp) r3
        exact hret.reEquivExecutionGen hcode hd hdec (by
          rw [acceptCapBody_eq]; exact hbody) rfl voidReturnEquiv

end Benchmarks.Morpho.MetaMorphoV1_1
