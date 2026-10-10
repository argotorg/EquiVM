import Benchmarks.Morpho.MetaMorphoV1_1.Dispatch
import Benchmarks.Morpho.MetaMorphoV1_1.MarketRevocationEntry
import Benchmarks.Morpho.MetaMorphoV1_1.MarketRevocationStore

/-!
# MetaMorphoV1_1 `revokePendingMarketRemoval(bytes32)`

Per-function proof: calldata decode facts, the EVM trace from the dispatcher arm through the
body, the Solm body evaluation, and the `…Body` theorem `Correct.lean` consumes.
Dispatcher arm entry: pc 7739; reach lemma `metaMorphoV1_1ReachRevokePendingMarketRemovalBody`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables

namespace Benchmarks.Morpho.MetaMorphoV1_1

set_option maxRecDepth 2000000

/-- `revokePendingMarketRemoval(bytes32)`: the theorem `Correct.lean` routes selector 23 to. -/
theorem metaMorphoV1_1RevokePendingMarketRemovalBody {σ σ₀ A I} {g : UInt256}
    (v : MetaMorphoV1_1Immutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (metaMorphoV1_1SelBytes 23)) :
    runtimeRefinementFor config contract σ σ₀ g A I (immStore v) := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (metaMorphoV1_1SelBytes 23) rfl hsel
  have hd : dispatchMsg contract I.calldata = some revokePendingMarketRemovalTransition := by
    apply metaMorphoV1_1Dispatch_revokePendingMarketRemoval <;>
      first | exact hsel | exact selectorMismatch hsel (by decide +kernel)
  obtain ⟨k, C, rd⟩ := metaMorphoV1_1ReachRevokePendingMarketRemovalBody
    (σ := σ) (σ₀ := σ₀) (A := A) (g := Sat256.ofUInt256 g) v hcode hsz hsize hsel
  let evm := initState σ σ₀ (Sat256.ofUInt256 g) A I
  by_cases hwv : I.weiValue = ⟨0⟩
  · by_cases hlen : 36 ≤ I.calldata.size
    · by_cases hhi : I.calldata.size < 2 ^ 255 + 4
      · have hdec := decodeCalldata_bytes32_ok (x := "id") hlen hhi
        obtain ⟨_, _, r1⟩ := marketRevocationReachRole v false (by simp)
          hwv hlen hhi hsize rd
        by_cases hrole : curatorGuardianAllowed evm
        · obtain ⟨_, _, r2⟩ := marketRevocationReachStore (evm := evm) v false
            (by simp) hrole r1
          by_cases hperm : I.perm = true
          · obtain ⟨final, hbody⟩ := marketRevocationBodyReturns false evm
              ((∅ : Store).insert "id"
                (.fixedBytes abiBytes32Width ((I.calldata.toList.drop 4).take 32)))
              (immStore v) _ _ (calldata_first_word_length hlen) hwv hhi hrole
              (by simp [marketRevocationBase]) (store_get_self _ _ _) (calldataBytes32Key hlen)
            exact (marketRevocationStoreReturn v false (by simp) hperm r2).reEquivExecutionGen
              hcode hd hdec hbody (storageStore_accountMap evm _ _ _).symm voidReturnEquiv
          · have hp : I.perm = false := Bool.eq_false_of_not_eq_true hperm
            exact (marketRevocationStoreStatic v false (by simp) hp r2).reEquivStaticHalt
              hcode hd hdec (marketRevocationBodyStatic false evm _ (immStore v) _ _
                (calldata_first_word_length hlen) hwv hhi hrole
                (by simp [marketRevocationBase]) (store_get_self _ _ _)
                (calldataBytes32Key hlen) hp)
        · have hrev := marketRevocationRevertRole (evm := evm) v false (by simp) hrole r1
          exact hrev.reEquivExecutionRevert hcode hd hdec
            (marketRevocationBodyRevertsRole false evm _ (immStore v) hwv hhi hrole)
      · have hrev := marketRevocationRevertLength v false (by simp) hwv (by
          rw [calldataNot3_eq_sub hsz hsize,
            solcDecodeLenCheckHuge_4_32 (Nat.le_of_not_gt hhi) hsize]
          decide) rd
        exact hrev.reEquivDecodingFailed hcode hd
          (decodeCalldata_bytes32_none_huge (Nat.le_of_not_gt hhi))
    · have hrev := marketRevocationRevertLength v false (by simp) hwv (by
        rw [calldataNot3_eq_sub hsz hsize,
          solcDecodeLenCheckShort_4_32 hsz (by omega) hsize]
        decide) rd
      exact hrev.reEquivDecodingFailed hcode hd (decodeCalldata_bytes32_none_short hsz (by omega))
  · exact dispatchedRevert hcode hd (marketRevocationRevertNonPayable v false (by simp) hwv rd)
      (fun _ ↦ bodyReverts_nonPayable hwv)

end Benchmarks.Morpho.MetaMorphoV1_1
