import Benchmarks.Morpho.MetaMorphoV1_1.Dispatch
import Benchmarks.Morpho.MetaMorphoV1_1.MaxDepositEntry
import Benchmarks.Morpho.MetaMorphoV1_1.MaxDepositBodySource

/-!
# MetaMorphoV1_1 `maxDeposit(address)`

Per-function proof: calldata decode facts, the EVM trace from the dispatcher arm through the
body, the Solm body evaluation, and the `…Body` theorem `Correct.lean` consumes.
Dispatcher arm entry: pc 8828; reach lemma `metaMorphoV1_1ReachMaxDepositBody`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables

namespace Benchmarks.Morpho.MetaMorphoV1_1

open SourceMemory

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option maxRecDepth 2000

/-- `maxDeposit(address)`: the theorem `Correct.lean` routes selector 19 to. -/
theorem metaMorphoV1_1MaxDepositBody {σ σ₀ A I} {g : UInt256} (v : MetaMorphoV1_1Immutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (metaMorphoV1_1SelBytes 19)) :
    runtimeRefinementFor config contract σ σ₀ g A I (immStore v) := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (metaMorphoV1_1SelBytes 19) rfl hsel
  have hd : dispatchMsg contract I.calldata = some maxDepositTransition := by
    apply metaMorphoV1_1Dispatch_maxDeposit <;>
      first | exact hsel | exact selectorMismatch hsel (by decide +kernel)
  obtain ⟨k, C, rd⟩ := metaMorphoV1_1ReachMaxDepositBody
    (σ := σ) (σ₀ := σ₀) (A := A) (g := Sat256.ofUInt256 g) v hcode hsz hsize hsel
  by_cases hwv : I.weiValue = ⟨0⟩
  · by_cases hlen : 36 ≤ I.calldata.size
    · by_cases hhi : I.calldata.size < 2 ^ 255 + 4
      · by_cases hcanon : (calldataWord I.calldata 4).toNat < EVM.addressModulus
        · have hdec := decodeCalldata_address_ok (x := "arg0") hlen hhi hcanon
          obtain ⟨aw1, k1, C1, h1⟩ := maxDepositReachFunction v (by simp)
            hwv hlen hhi hsize hcanon rd
          rcases maxDepositFunctionSimulation v (by simp) hsize solcFreePtrMem_mload64
              (by decide) (by rw [solcFreePtrMem_size]) SourceState.init
              (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) h1 with
            ⟨hbad, hrev⟩ | ⟨evm', frame', total, cursor, mem', out, hs', hbody,
              hfree, hlo, hmem, aw2, k2, C2, h2⟩
          · exact hrev.reEquivExecutionRevert hcode hd hdec
              (maxDepositBodyReverts v _ hwv hhi hbad)
          · exact (maxDepositEncodeReturn v (by simp) h2).reEquivExecutionGen hcode hd hdec
              (maxDepositBodyReturns v _ hwv hhi hbody) rfl
              (returnEquiv_of_encode (uint256ReturnEncoding _))
        · have hrev := maxDepositRevertNoncanonical v (by simp) hwv hlen hhi hsize hcanon rd
          exact hrev.reEquivDecodingFailed hcode hd
            (decodeCalldata_address_none_noncanon hlen hhi hcanon)
      · have hrev := maxDepositRevertLength v (by simp) hwv (by
          rw [calldataNot3_eq_sub hsz hsize,
            solcDecodeLenCheckHuge_4_32 (Nat.le_of_not_gt hhi) hsize]
          decide) rd
        exact hrev.reEquivDecodingFailed hcode hd
          (decodeCalldata_address_none_huge (Nat.le_of_not_gt hhi))
    · have hrev := maxDepositRevertLength v (by simp) hwv (by
        rw [calldataNot3_eq_sub hsz hsize,
          solcDecodeLenCheckShort_4_32 hsz (by omega) hsize]
        decide) rd
      exact hrev.reEquivDecodingFailed hcode hd (decodeCalldata_address_none_short hsz (by omega))
  · exact dispatchedRevert hcode hd (maxDepositRevertNonPayable v (by simp) hwv rd)
      (fun _ ↦ bodyReverts_nonPayable hwv)

end Benchmarks.Morpho.MetaMorphoV1_1
