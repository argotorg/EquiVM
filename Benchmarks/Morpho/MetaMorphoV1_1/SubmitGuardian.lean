import Benchmarks.Morpho.MetaMorphoV1_1.Dispatch
import Benchmarks.Morpho.MetaMorphoV1_1.SubmitGuardianRoutines

/-!
# MetaMorphoV1_1 `submitGuardian(address)`

Per-function proof: calldata decode facts, the EVM trace from the dispatcher arm through the
body, the Solm body evaluation, and the `…Body` theorem `Correct.lean` consumes.
Dispatcher arm entry: pc 4368; reach lemma `metaMorphoV1_1ReachSubmitGuardianBody`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables

namespace Benchmarks.Morpho.MetaMorphoV1_1

set_option maxRecDepth 2000000

/-- `submitGuardian(address)`: the theorem `Correct.lean` routes selector 45 to. -/
theorem metaMorphoV1_1SubmitGuardianBody {σ σ₀ A I} {g : UInt256} (v : MetaMorphoV1_1Immutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (metaMorphoV1_1SelBytes 45)) :
    runtimeRefinementFor config contract σ σ₀ g A I (immStore v) := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (metaMorphoV1_1SelBytes 45) rfl hsel
  have hd : dispatchMsg contract I.calldata = some submitGuardianTransition := by
    apply metaMorphoV1_1Dispatch_submitGuardian <;>
      first | exact hsel | exact selectorMismatch hsel (by decide +kernel)
  obtain ⟨k, C, rd⟩ := metaMorphoV1_1ReachSubmitGuardianBody
    (σ := σ) (σ₀ := σ₀) (A := A) (g := Sat256.ofUInt256 g) v hcode hsz hsize hsel
  let evm := initState σ σ₀ (Sat256.ofUInt256 g) A I
  let value := AccountAddress.ofNat (calldataWord I.calldata 4).toNat
  by_cases hwv : I.weiValue = ⟨0⟩
  · by_cases hlen : 36 ≤ I.calldata.size
    · by_cases hhi : I.calldata.size < 2 ^ 255 + 4
      · obtain ⟨_, _, rd11163⟩ := submitGuardianReachDecoder v (by simp) hwv hlen hhi hsize rd
        by_cases hcanon : (calldataWord I.calldata 4).toNat < EVM.addressModulus
        · have hdec := decodeCalldata_address_ok (x := "newGuardian") hlen hhi hcanon
          have hw : UInt256.ofNat value.val = calldataWord I.calldata 4 := by
            change EVM.word (AccountAddress.ofNat (calldataWord I.calldata 4).toNat).val = _
            rw [word_of_addressOfNat_eq_mask, solcAddrMask_clean hcanon]
          obtain ⟨_, _, rd12917⟩ := submitGuardianReachOwner v (by simp) hcanon rd11163
          by_cases howner : ownerAddress evm = I.source
          · obtain ⟨_, _, rd4401⟩ := checkOwnerReturn v (by simp) howner
              (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) rd12917
            rw [← hw] at rd4401
            by_cases hgood : submitGuardianAllowed evm value
            · obtain ⟨_, _, rd4445⟩ := submitGuardianReachBranch (evm := evm) v (by simp)
                hgood rd4401
              by_cases hperm : I.perm = true
              · by_cases hfit : submitGuardianFits evm
                · obtain ⟨final, hbody⟩ := submitGuardianBodyReturns evm (immStore v) value
                    hwv hhi howner hgood hfit
                  have hret := submitGuardianStoreReturn (evm := evm) v (by simp)
                    hperm hfit rd4445
                  exact hret.reEquivExecutionGen hcode hd hdec hbody rfl voidReturnEquiv
                · have hrev := submitGuardianRevertOverflow (evm := evm) v (by simp)
                    hperm hfit rd4445
                  exact hrev.reEquivExecutionRevert hcode hd hdec
                    (submitGuardianBodyRevertsOverflow evm (immStore v) value
                      hwv hhi howner hgood hfit)
              · have hp : I.perm = false := Bool.eq_false_of_not_eq_true hperm
                have hstatic := submitGuardianStoreStatic (evm := evm) v (by simp) hp rd4445
                exact hstatic.reEquivStaticHalt hcode hd hdec
                  (submitGuardianBodyStatic evm (immStore v) value hwv hhi howner hgood hp)
            · have hrev := submitGuardianRevertGuard (evm := evm) v (by simp) hgood rd4401
              exact hrev.reEquivExecutionRevert hcode hd hdec
                (submitGuardianBodyRevertsGuard evm (immStore v) value hwv hhi howner hgood)
          · exact (checkOwnerRevert v (by simp) howner rd12917).reEquivExecutionRevert
              hcode hd hdec (adminBodyRevertsOwner evm _ (immStore v) submitGuardianTail
                hwv hhi howner)
        · exact (decodeAddressAt4Revert v (by simp) hcanon rd11163).reEquivDecodingFailed
            hcode hd (decodeCalldata_address_none_noncanon hlen hhi hcanon)
      · have hrev := submitGuardianRevertLength v (by simp) hwv (by
          rw [calldataNot3_eq_sub hsz hsize,
            solcDecodeLenCheckHuge_4_32 (Nat.le_of_not_gt hhi) hsize]
          decide) rd
        exact hrev.reEquivDecodingFailed hcode hd
          (decodeCalldata_address_none_huge (Nat.le_of_not_gt hhi))
    · have hrev := submitGuardianRevertLength v (by simp) hwv (by
        rw [calldataNot3_eq_sub hsz hsize,
          solcDecodeLenCheckShort_4_32 hsz (by omega) hsize]
        decide) rd
      exact hrev.reEquivDecodingFailed hcode hd (decodeCalldata_address_none_short hsz (by omega))
  · exact dispatchedRevert hcode hd (submitGuardianRevertNonPayable v (by simp) hwv rd)
      (fun _ ↦ bodyReverts_nonPayable hwv)

end Benchmarks.Morpho.MetaMorphoV1_1
