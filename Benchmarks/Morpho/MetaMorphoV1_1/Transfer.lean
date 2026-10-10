import Benchmarks.Morpho.MetaMorphoV1_1.Dispatch
import Benchmarks.Morpho.MetaMorphoV1_1.TransferEntry
import Benchmarks.Morpho.MetaMorphoV1_1.TransferBodySource
import Benchmarks.Morpho.MetaMorphoV1_1.TransferRoutines
import Benchmarks.Morpho.MetaMorphoV1_1.TransferStatic

/-!
# MetaMorphoV1_1 `transfer(address,uint256)`

Per-function proof: calldata decode facts, the EVM trace from the dispatcher arm through the
body, the Solm body evaluation, and the `…Body` theorem `Correct.lean` consumes.
Dispatcher arm entry: pc 4123; reach lemma `metaMorphoV1_1ReachTransferBody`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option maxRecDepth 2000

/-- `transfer(address,uint256)`: the theorem `Correct.lean` routes selector 49 to. -/
theorem metaMorphoV1_1TransferBody {σ σ₀ A I} {g : UInt256} (v : MetaMorphoV1_1Immutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (metaMorphoV1_1SelBytes 49)) :
    runtimeRefinementFor config contract σ σ₀ g A I (immStore v) := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (metaMorphoV1_1SelBytes 49) rfl hsel
  have hd : dispatchMsg contract I.calldata = some transferTransition := by
    apply metaMorphoV1_1Dispatch_transfer <;>
      first | exact hsel | exact selectorMismatch hsel (by decide +kernel)
  obtain ⟨k, C, rd⟩ := metaMorphoV1_1ReachTransferBody
    (σ := σ) (σ₀ := σ₀) (A := A) (g := Sat256.ofUInt256 g) v hcode hsz hsize hsel
  by_cases hwv : I.weiValue = ⟨0⟩
  · by_cases hlen : 68 ≤ I.calldata.size
    · by_cases hhi : I.calldata.size < 2 ^ 255 + 4
      · by_cases hcanon : (calldataWord I.calldata 4).toNat < EVM.addressModulus
        · have hdec := decodeCalldata_addr_uint256_ok (x := "to") (y := "value") hlen hhi hcanon
          let recipient := AccountAddress.ofNat (calldataWord I.calldata 4).toNat
          let value := calldataWord I.calldata 36
          let evm := initState σ σ₀ (Sat256.ofUInt256 g) A I
          let locals := ((∅ : Store).insert "to" (.address recipient)).insert "value"
            (uint256Value value)
          have ht : locals.get? "to" = some (.address recipient) := by
            simp only [locals, store_get_ne _ _ (by decide : ("value" == "to") = false),
              store_get_self]
          have hv : locals.get? "value" = some (uint256Value value) := store_get_self _ _ _
          have hbalance : balanceWord evm I.source =
              codeOwnerStorageWord I σ (balanceSlot I.source) := codeOwnerStorageWord_initState _
          obtain ⟨aw1, k1, C1, h1⟩ := transferReachFunction v (by simp)
            hwv hlen hhi hsize hcanon rd
          by_cases haddr : I.source ≠ ⟨0, by decide⟩ ∧ recipient ≠ ⟨0, by decide⟩
          · obtain ⟨aw2, k2, C2, h2⟩ := transferReachBalance v (by simp) haddr.1 haddr.2 h1
            by_cases hbal : value.toNat ≤ (codeOwnerStorageWord I σ (balanceSlot I.source)).toNat
            · have hgood : transferAllowed evm I.source recipient value :=
                ⟨haddr.1, haddr.2, by rw [hbalance]; exact hbal⟩
              obtain ⟨aw3, k3, C3, h3⟩ := transferReadBalance v (by simp) hbal h2
              by_cases hperm : I.perm = true
              · obtain ⟨aw4, k4, C4, h4⟩ := transferStoreReturn v (by simp) hperm
                  (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) h3
                exact (approveEncodeReturn v (by simp) h4).reEquivExecutionGen hcode hd hdec
                  (transferPublicBodyReturns v evm locals recipient value hwv hhi ht hv hgood)
                  (balanceMoveState_accounts evm I.source recipient value).symm
                  (returnEquiv_of_encode boolTrueReturnEncoding)
              · have hp : I.perm = false := Bool.eq_false_of_not_eq_true hperm
                exact (transferStoreStatic v (by simp) hp h3).reEquivStaticHalt hcode hd hdec
                  (transferPublicBodyStatic v evm locals recipient value hwv hhi ht hv hgood hp)
            · have hbad : ¬ transferAllowed evm I.source recipient value := by
                intro hg
                exact hbal (hbalance ▸ hg.2.2)
              exact (transferRevertBalance v (by simp) hbal h2).reEquivExecutionRevert
                hcode hd hdec
                (transferPublicBodyReverts v evm locals recipient value hwv hhi ht hv hbad)
          · exact (transferRevertAddress v (by simp) haddr h1).reEquivExecutionRevert hcode hd hdec
              (transferPublicBodyReverts v evm locals recipient value hwv hhi ht hv
                (fun hg ↦ haddr ⟨hg.1, hg.2.1⟩))
        · exact (transferRevertNoncanonical v (by simp) hwv hlen hhi hsize hcanon rd)
            |>.reEquivDecodingFailed hcode hd
              (decodeCalldata_addr_uint256_none_noncanon hlen hhi hcanon)
      · have hrev := transferRevertLength v (by simp) hwv (by
          rw [calldataNot3_eq_sub hsz hsize,
            solcDecodeLenCheckHuge_4_64 (Nat.le_of_not_gt hhi) hsize]
          decide) rd
        exact hrev.reEquivDecodingFailed hcode hd
          (decodeCalldata_addr_uint256_none_huge (Nat.le_of_not_gt hhi))
    · have hrev := transferRevertLength v (by simp) hwv (by
        rw [calldataNot3_eq_sub hsz hsize,
          solcDecodeLenCheckShort_4_64 hsz (by omega) hsize]
        decide) rd
      exact hrev.reEquivDecodingFailed hcode hd
        (decodeCalldata_addr_uint256_none_short hsz (by omega))
  · exact dispatchedRevert hcode hd (transferRevertNonPayable v (by simp) hwv rd)
      (fun _ ↦ bodyReverts_nonPayable hwv)

end Benchmarks.Morpho.MetaMorphoV1_1
