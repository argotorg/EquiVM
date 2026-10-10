import Benchmarks.Morpho.MetaMorphoV1_1.Dispatch
import Benchmarks.Morpho.MetaMorphoV1_1.UpdateWithdrawQueueEntry
import Benchmarks.Morpho.MetaMorphoV1_1.UpdateWithdrawQueueRole
import Benchmarks.Morpho.MetaMorphoV1_1.UpdateWithdrawQueueSimulation
import Benchmarks.Morpho.MetaMorphoV1_1.Mutation

/-!
# MetaMorphoV1_1 `updateWithdrawQueue(uint256[])`

Per-function proof: calldata decode facts, the EVM trace from the dispatcher arm through the
body, the Solm body evaluation, and the `…Body` theorem `Correct.lean` consumes.
Dispatcher arm entry: pc 7984; reach lemma `metaMorphoV1_1ReachUpdateWithdrawQueueBody`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option maxRecDepth 2000

/-- `updateWithdrawQueue(uint256[])`: the theorem `Correct.lean` routes selector 20 to. -/
theorem metaMorphoV1_1UpdateWithdrawQueueBody {σ σ₀ A I} {g : UInt256}
    (v : MetaMorphoV1_1Immutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (metaMorphoV1_1SelBytes 20)) :
    runtimeRefinementFor config contract σ σ₀ g A I (immStore v) := by
  have hsz : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (metaMorphoV1_1SelBytes 20) rfl hsel
  have hd : dispatchMsg contract I.calldata = some updateWithdrawQueueTransition := by
    apply metaMorphoV1_1Dispatch_updateWithdrawQueue <;>
      first | exact hsel | exact selectorMismatch hsel (by decide +kernel)
  obtain ⟨k, C, rd⟩ := metaMorphoV1_1ReachUpdateWithdrawQueueBody
    (σ := σ) (σ₀ := σ₀) (A := A) (g := Sat256.ofUInt256 g) v hcode hsz hsize hsel
  by_cases hwv : I.weiValue = ⟨0⟩
  case neg =>
    exact dispatchedRevert hcode hd (updateWithdrawQueueNonpayable v (by simp) hwv rd)
      (fun _ ↦ bodyReverts_nonPayable hwv)
  rcases updateWithdrawQueueDecode v (by simp) hwv hsz hsize rd with
    ⟨hc, hrev⟩ | ⟨hc, k1, C1, r1⟩
  · exact hrev.reEquivDecodingFailed hcode hd (decodeCalldataUintArrayBad "indexes" hc)
  · have hdec := decodeCalldataUintArray "indexes" hc
    let evm := initState σ σ₀ (Sat256.ofUInt256 g) A I
    have hhi : I.calldata.size < 2 ^ 255 + 4 := lt_of_lt_of_le hc.size (by omega)
    rcases updateWithdrawQueueRole (evm := evm) v (by simp) r1 with
      ⟨hrole, hrev⟩ | ⟨hrole, aw2, k2, C2, r2⟩
    · exact hrev.reEquivExecutionRevert hcode hd hdec (by
        rw [updateWithdrawQueueBody_eq]
        exact updateWithdrawQueueBodyRoleReverts evm (immStore v)
          (calldataUintArrayValues I.calldata) hwv hhi hrole)
    · have hp := updateWithdrawQueuePrefix evm (immStore v)
        (calldataUintArrayValues I.calldata) hwv hhi hrole
      have hs : SourceState evm I evm.accountMap evm := SourceState.init
      rcases updateWithdrawQueueSimulation (evm := evm) v (by simp) hc
          (by rw [twoWordHashMem_size_96 _ _ solcFreePtrMem_size]; decide)
          (mappingScratch_mload64 _ _) hs r2 with
        ⟨htail, hrev⟩ | ⟨htail, hstatic⟩ | ⟨final, evm', htail, hret⟩
      · exact hrev.reEquivExecutionRevert hcode hd hdec (by
          rw [updateWithdrawQueueBody_eq]
          exact ExecFuncBody.execBlockRevert (hp.run htail))
      · exact hstatic.reEquivStaticHalt hcode hd hdec (by
          rw [updateWithdrawQueueBody_eq]
          exact ExecFuncBody.execBlockStatic (hp.run htail))
      · exact hret.reEquivExecutionGen hcode hd hdec (by
          rw [updateWithdrawQueueBody_eq]
          exact ExecFuncBody.execBlockOK (hp.run htail)) rfl voidReturnEquiv

end Benchmarks.Morpho.MetaMorphoV1_1
