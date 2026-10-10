import Benchmarks.Morpho.MetaMorphoV1_1.Dispatch
import Benchmarks.Morpho.MetaMorphoV1_1.SupplyQueueEntry
import Benchmarks.Morpho.MetaMorphoV1_1.SupplyQueueLength
import Benchmarks.Morpho.MetaMorphoV1_1.SupplyQueueStore
import Benchmarks.Morpho.MetaMorphoV1_1.SupplyQueueSource
import Benchmarks.Morpho.MetaMorphoV1_1.Mutation

/-!
# MetaMorphoV1_1 `setSupplyQueue(bytes32[])`

Per-function proof: calldata decode facts, the EVM trace from the dispatcher arm through the
body, the Solm body evaluation, and the `…Body` theorem `Correct.lean` consumes.
Dispatcher arm entry: pc 9964; reach lemma `metaMorphoV1_1ReachSetSupplyQueueBody`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option maxRecDepth 2000

/-- `setSupplyQueue(bytes32[])`: the theorem `Correct.lean` routes selector 10 to. -/
theorem metaMorphoV1_1SetSupplyQueueBody {σ σ₀ A I} {g : UInt256} (v : MetaMorphoV1_1Immutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (metaMorphoV1_1SelBytes 10)) :
    runtimeRefinementFor config contract σ σ₀ g A I (immStore v) := by
  have hsz : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (metaMorphoV1_1SelBytes 10) rfl hsel
  have hd : dispatchMsg contract I.calldata = some setSupplyQueueTransition := by
    apply metaMorphoV1_1Dispatch_setSupplyQueue <;>
      first | exact hsel | exact selectorMismatch hsel (by decide +kernel)
  obtain ⟨k, C, rd⟩ := metaMorphoV1_1ReachSetSupplyQueueBody
    (σ := σ) (σ₀ := σ₀) (A := A) (g := Sat256.ofUInt256 g) v hcode hsz hsize hsel
  by_cases hwv : I.weiValue = ⟨0⟩
  case neg =>
    exact dispatchedRevert hcode hd (supplyQueueNonpayable v (by simp) hwv rd)
      (fun _ ↦ bodyReverts_nonPayable hwv)
  rcases supplyQueueDecode v (by simp) hwv hsz hsize rd with
    ⟨hc, hrev⟩ | ⟨hc, k1, C1, r1⟩
  · exact hrev.reEquivDecodingFailed hcode hd (decodeCalldataWordArrayBad "newSupplyQueue" hc)
  · have hdec := decodeCalldataWordArray "newSupplyQueue" hc
    let evm := initState σ σ₀ (Sat256.ofUInt256 g) A I
    have hhi : I.calldata.size < 2 ^ 255 + 4 := lt_of_lt_of_le hc.size (by omega)
    rcases supplyQueueRole (evm := evm) v (by simp) r1 with
      ⟨hrole, hrev⟩ | ⟨hrole, aw2, k2, C2, r2⟩
    · exact hrev.reEquivExecutionRevert hcode hd hdec
        (supplyQueueBodyRevertsRole evm (immStore v) (calldataArrayValues I.calldata)
          hwv hhi hrole)
    · rcases supplyQueueLengthGuard v (by simp)
        (lt_of_le_of_lt hc.length (by decide)) r2 with ⟨hlen, hrev⟩ | ⟨hlen, k3, C3, r3⟩
      · exact hrev.reEquivExecutionRevert hcode hd hdec
          (supplyQueueBodyRevertsLength evm (immStore v) (calldataArrayValues I.calldata)
            hwv hhi hrole (by rw [calldataArrayValues_length]; exact hlen))
      · have hlenSource : (calldataArrayValues I.calldata).length ≤ 30 := by
          rw [calldataArrayValues_length]; exact hlen
        rcases supplyQueueLoopSimulation (evm := evm) v (calldataArrayLength I.calldata)
            (by simp) hc (supplyQueueInitialReady evm (immStore v) _) (Nat.zero_add _).symm
            (twoWordHashMem_size_96 _ _ solcFreePtrMem_size)
            (twoWordHashMem_read64 _ _ solcFreePtrMem_size solcFreePtrMem_read64) r3 with
          ⟨hloop, hrev⟩ | ⟨frame, mem4, hready, hmem, hfree, hloop, aw4, k4, C4, r4⟩
        · exact hrev.reEquivExecutionRevert hcode hd hdec
            (supplyQueueBodyRevertsLoop evm (immStore v) (calldataArrayValues I.calldata)
              hwv hhi hrole hlenSource hloop)
        · have hp := supplyQueueLoopPrefix evm (immStore v) (calldataArrayValues I.calldata)
            hwv hhi hrole hlenSource hloop
          obtain ⟨k5, C5, r5⟩ := supplyQueueStoreGuards v (by simp) hlen r4
          by_cases hperm : I.perm = true
          case neg =>
            have hf : I.perm = false := Bool.eq_false_of_not_eq_true hperm
            have hstatic := supplyQueueStoreStatic v (by simp) hf r5
            exact hstatic.reEquivStaticHalt hcode hd hdec
              (ExecFuncBody.execBlockStatic (hp.run (supplyQueueTailStatic hready hf)))
          have hret := supplyQueueStoreAndFinish (evm := evm) v (by simp)
            hc hlen hperm hmem hfree r5
          obtain ⟨final, ht⟩ := supplyQueueTailReturns hready
          exact hret.reEquivExecutionGen hcode hd hdec
            (ExecFuncBody.execBlockOK (hp.run ht)) rfl voidReturnEquiv

end Benchmarks.Morpho.MetaMorphoV1_1
