import Benchmarks.Morpho.MetaMorphoV1_1.Dispatch
import Benchmarks.Morpho.MetaMorphoV1_1.ApproveEntry
import Benchmarks.Morpho.MetaMorphoV1_1.ApproveBodySource
import Benchmarks.Morpho.MetaMorphoV1_1.ApprovalRoutines

/-!
# MetaMorphoV1_1 `approve(address,uint256)`

Per-function proof: calldata decode facts, the EVM trace from the dispatcher arm through the
body, the Solm body evaluation, and the `…Body` theorem `Correct.lean` consumes.
Dispatcher arm entry: pc 10846; reach lemma `metaMorphoV1_1ReachApproveBody`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option maxRecDepth 2000

/-- `approve(address,uint256)`: the theorem `Correct.lean` routes selector 3 to. -/
theorem metaMorphoV1_1ApproveBody {σ σ₀ A I} {g : UInt256} (v : MetaMorphoV1_1Immutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (metaMorphoV1_1SelBytes 3)) :
    runtimeRefinementFor config contract σ σ₀ g A I (immStore v) := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (metaMorphoV1_1SelBytes 3) rfl hsel
  have hd : dispatchMsg contract I.calldata = some approveTransition := by
    apply metaMorphoV1_1Dispatch_approve <;>
      first | exact hsel | exact selectorMismatch hsel (by decide +kernel)
  obtain ⟨k, C, rd⟩ := metaMorphoV1_1ReachApproveBody
    (σ := σ) (σ₀ := σ₀) (A := A) (g := Sat256.ofUInt256 g) v hcode hsz hsize hsel
  by_cases hwv : I.weiValue = ⟨0⟩
  · by_cases hlen : 68 ≤ I.calldata.size
    · by_cases hhi : I.calldata.size < 2 ^ 255 + 4
      · by_cases hcanon : (calldataWord I.calldata 4).toNat < EVM.addressModulus
        · have hdec := decodeCalldata_addr_uint256_ok (x := "spender") (y := "value")
            hlen hhi hcanon
          let spender := AccountAddress.ofNat (calldataWord I.calldata 4).toNat
          let value := calldataWord I.calldata 36
          let locals := ((∅ : Store).insert "spender" (.address spender)).insert "value"
            (uint256Value value)
          have hs : locals.get? "spender" = some (.address spender) := by
            simp only [locals, store_get_ne _ _ (by decide : ("value" == "spender") = false),
              store_get_self]
          have hv : locals.get? "value" = some (uint256Value value) := store_get_self _ _ _
          obtain ⟨aw1, k1, C1, h1⟩ := approveReachFunction v (by simp)
            hwv hlen hhi hsize hcanon rd
          by_cases hgood : I.source ≠ ⟨0, by decide⟩ ∧ spender ≠ ⟨0, by decide⟩
          · obtain ⟨aw2, k2, C2, h2⟩ := approvalReachStore v (by simp) hgood.1 hgood.2 h1
            by_cases hperm : I.perm = true
            · obtain ⟨aw3, k3, C3, h3⟩ := approvalStoreReturn v (by simp) hperm
                (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) h2
              exact (approveEncodeReturn v (by simp) h3).reEquivExecutionGen hcode hd hdec
                (approvePublicBodyReturns v _ locals spender value hwv hhi hs hv hgood.1 hgood.2)
                (storageStore_accountMap (initState σ σ₀ (Sat256.ofUInt256 g) A I) _ _ _).symm
                (returnEquiv_of_encode boolTrueReturnEncoding)
            · have hp : I.perm = false := Bool.eq_false_of_not_eq_true hperm
              exact (approvalStoreStatic v (by simp) hp h2).reEquivStaticHalt hcode hd hdec
                (approvePublicBodyStatic v _ locals spender value hwv hhi hs hv hgood.1 hgood.2 hp)
          · exact (approvalRevertAddress v (by simp) hgood h1).reEquivExecutionRevert hcode hd hdec
              (approvePublicBodyReverts v _ locals spender value hwv hhi hs hv hgood)
        · exact (approveRevertNoncanonical v (by simp) hwv hlen hhi hsize hcanon rd)
            |>.reEquivDecodingFailed hcode hd
              (decodeCalldata_addr_uint256_none_noncanon hlen hhi hcanon)
      · have hrev := approveRevertLength v (by simp) hwv (by
          rw [calldataNot3_eq_sub hsz hsize,
            solcDecodeLenCheckHuge_4_64 (Nat.le_of_not_gt hhi) hsize]
          decide) rd
        exact hrev.reEquivDecodingFailed hcode hd
          (decodeCalldata_addr_uint256_none_huge (Nat.le_of_not_gt hhi))
    · have hrev := approveRevertLength v (by simp) hwv (by
        rw [calldataNot3_eq_sub hsz hsize,
          solcDecodeLenCheckShort_4_64 hsz (by omega) hsize]
        decide) rd
      exact hrev.reEquivDecodingFailed hcode hd
        (decodeCalldata_addr_uint256_none_short hsz (by omega))
  · exact dispatchedRevert hcode hd (approveRevertNonPayable v (by simp) hwv rd)
      (fun _ ↦ bodyReverts_nonPayable hwv)

end Benchmarks.Morpho.MetaMorphoV1_1
