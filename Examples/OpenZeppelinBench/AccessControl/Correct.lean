import Examples.OpenZeppelinBench.AccessControl.DefaultAdminRole
import Examples.OpenZeppelinBench.AccessControl.GetRoleAdmin
import Examples.OpenZeppelinBench.AccessControl.GrantRole
import Examples.OpenZeppelinBench.AccessControl.HasRole
import Examples.OpenZeppelinBench.AccessControl.RenounceRole
import Examples.OpenZeppelinBench.AccessControl.RevokeRole
import Examples.OpenZeppelinBench.AccessControl.SupportsInterface

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace OpenZeppelinBench.AccessControl

/-!
# AccessControl benchmark top-level correctness proof

This file routes through the optimizer-ON one-level binary-search dispatcher, then delegates each
matched body PC to its per-function proof.
-/

/-- `callvalue ≠ 0` makes the global non-payable guard revert before dispatch. -/
theorem accessControlNonPayable {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = accessControlBenchBytecode) (hwv : I.weiValue ≠ ⟨0⟩) :
    runtimeEquivalenceFor config contract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  exact (accessControlX_callvalue_ne (g := Sat256.ofUInt256 g) hcode hwv).reEquivElim hcode
    fun _ _ hrev => by
      by_cases hdisp : dispatchMsg contract I.calldata = none
      · exact reEquiv_noDispatch hdisp hrev
      · obtain ⟨t, ht⟩ := Option.ne_none_iff_exists'.mp hdisp
        have htmem : t ∈ contract.transitions := by
          rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl)] at ht
          exact dispatchList_some_mem ht
        by_cases hdec : decodeCalldata (t.params.map Param.name)
            (transitionSignature t).paramTypes I.calldata = none
        · exact reEquiv_decodingFailed ht hdec hrev
        · obtain ⟨callargs, hca⟩ := Option.ne_none_iff_exists'.mp hdec
          exact reEquiv_execution ht hca
            (accessControlBodyReverts_nonPayable t htmem
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
              callargs (by simp only [initState]; exact hwv))
            (by rw [hrev]; exact execResultsEquiv.revert rfl rfl)

/-- Calldata shorter than a selector (`size < 4`) reverts before Solm dispatch. -/
theorem accessControlShortRevert {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = accessControlBenchBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩) (hsz : I.calldata.size < 4) :
    runtimeEquivalenceFor config contract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  exact (accessControlX_short (g := Sat256.ofUInt256 g) hcode hwv hsz).reEquivNoDispatch
    hcode (accessControlDispatch_none_short hsz)

/-- `size ≥ 4` but no selector matches: no Solm dispatch and EVM fallthrough reverts. -/
theorem accessControlNoDispatch {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = accessControlBenchBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hnm : ∀ i, i < 7 → (accessControlSelBytes i == I.calldata.extract 0 4) = false) :
    runtimeEquivalenceFor config contract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  by_cases hsz : 4 ≤ I.calldata.size
  · exact (accessControlX_noMatch (g := Sat256.ofUInt256 g) hcode hwv hsz hsize hnm)
      |>.reEquivNoDispatch hcode (accessControlDispatch_none_nomatch hnm)
  · have hshort : I.calldata.size < 4 := by omega
    exact (accessControlX_short (g := Sat256.ofUInt256 g) hcode hwv hshort).reEquivNoDispatch
      hcode (accessControlDispatch_none_short hshort)

/-- The deployed AccessControl benchmark runtime bytecode refines the Solm specification. -/
theorem accessControlCorrect :
    runtimeEquivalence config accessControlBenchBytecode contract := by
  refine ⟨fun cA gh bl σ_evm σ_solm σ₀ g A I hcode hsize hperm hAccounts => ?_⟩
  by_cases hwv : I.weiValue = ⟨0⟩
  · by_cases hsz : 4 ≤ I.calldata.size
    · by_cases h0 : selIs I ⟨#[0x01, 0xff, 0xc9, 0xa7]⟩
      · exact accessControlSupportsInterfaceBody hcode hsize hperm hwv h0
          (accessControlReachLowBody 0 (by omega) ⟨126⟩ hcode hwv hsz hsize
            (accessControlPivotTaken 0 (by omega) hsz
              (by simpa [selIs, accessControlLowSelBytes] using h0))
            (accessControlLowMatches 0 (by omega) hsz
              (by simpa [selIs, accessControlLowSelBytes] using h0)).1
            (accessControlLowMatches 0 (by omega) hsz
              (by simpa [selIs, accessControlLowSelBytes] using h0)).2
            (by jump_dest) (by decide))
          hAccounts
      · by_cases h1 : selIs I ⟨#[0x24, 0x8a, 0x9c, 0xa3]⟩
        · exact accessControlGetRoleAdminBody hcode hsize hperm hwv h1
            (accessControlReachLowBody 1 (by omega) ⟨166⟩ hcode hwv hsz hsize
              (accessControlPivotTaken 1 (by omega) hsz
                (by simpa [selIs, accessControlLowSelBytes] using h1))
              (accessControlLowMatches 1 (by omega) hsz
                (by simpa [selIs, accessControlLowSelBytes] using h1)).1
              (accessControlLowMatches 1 (by omega) hsz
                (by simpa [selIs, accessControlLowSelBytes] using h1)).2
              (by jump_dest) (by decide))
            hAccounts
        · by_cases h2 : selIs I ⟨#[0x2f, 0x2f, 0xf1, 0x5d]⟩
          · exact accessControlGrantRoleBody hcode hsize hperm hwv h2
              (accessControlReachLowBody 2 (by omega) ⟨214⟩ hcode hwv hsz hsize
                (accessControlPivotTaken 2 (by omega) hsz
                  (by simpa [selIs, accessControlLowSelBytes] using h2))
                (accessControlLowMatches 2 (by omega) hsz
                  (by simpa [selIs, accessControlLowSelBytes] using h2)).1
                (accessControlLowMatches 2 (by omega) hsz
                  (by simpa [selIs, accessControlLowSelBytes] using h2)).2
                (by jump_dest) (by decide))
              hAccounts
          · by_cases h3 : selIs I ⟨#[0x36, 0x56, 0x8a, 0xbe]⟩
            · exact accessControlRenounceRoleBody hcode hsize hperm hwv h3
                (accessControlReachHighBody 0 (by omega) ⟨235⟩ hcode hwv hsz hsize
                  (accessControlPivotNotTaken 0 (by omega) hsz
                    (by simpa [selIs, accessControlHighSelBytes] using h3))
                  (accessControlHighMatches 0 (by omega) hsz
                    (by simpa [selIs, accessControlHighSelBytes] using h3)).1
                  (accessControlHighMatches 0 (by omega) hsz
                    (by simpa [selIs, accessControlHighSelBytes] using h3)).2
                  (by jump_dest) (by decide))
                hAccounts
            · by_cases h4 : selIs I ⟨#[0x91, 0xd1, 0x48, 0x54]⟩
              · exact accessControlHasRoleBody hcode hsize hperm hwv h4
                  (accessControlReachHighBody 1 (by omega) ⟨254⟩ hcode hwv hsz hsize
                    (accessControlPivotNotTaken 1 (by omega) hsz
                      (by simpa [selIs, accessControlHighSelBytes] using h4))
                    (accessControlHighMatches 1 (by omega) hsz
                      (by simpa [selIs, accessControlHighSelBytes] using h4)).1
                    (accessControlHighMatches 1 (by omega) hsz
                      (by simpa [selIs, accessControlHighSelBytes] using h4)).2
                    (by jump_dest) (by decide))
                  hAccounts
              · by_cases h5 : selIs I ⟨#[0xa2, 0x17, 0xfd, 0xdf]⟩
                · exact accessControlDefaultAdminRoleBody hcode hsize hperm hwv h5
                    (accessControlReachHighBody 2 (by omega) ⟨273⟩ hcode hwv hsz hsize
                      (accessControlPivotNotTaken 2 (by omega) hsz
                        (by simpa [selIs, accessControlHighSelBytes] using h5))
                      (accessControlHighMatches 2 (by omega) hsz
                        (by simpa [selIs, accessControlHighSelBytes] using h5)).1
                      (accessControlHighMatches 2 (by omega) hsz
                        (by simpa [selIs, accessControlHighSelBytes] using h5)).2
                      (by jump_dest) (by decide))
                    hAccounts
                · by_cases h6 : selIs I ⟨#[0xd5, 0x47, 0x74, 0x1f]⟩
                  · exact accessControlRevokeRoleBody hcode hsize hperm hwv h6
                      (accessControlReachHighBody 3 (by omega) ⟨280⟩ hcode hwv hsz hsize
                        (accessControlPivotNotTaken 3 (by omega) hsz
                          (by simpa [selIs, accessControlHighSelBytes] using h6))
                        (accessControlHighMatches 3 (by omega) hsz
                          (by simpa [selIs, accessControlHighSelBytes] using h6)).1
                        (accessControlHighMatches 3 (by omega) hsz
                          (by simpa [selIs, accessControlHighSelBytes] using h6)).2
                        (by jump_dest) (by decide))
                      hAccounts
                  · refine accessControlNoDispatch hcode hsize hperm hwv ?_
                    intro i hi
                    interval_cases i
                    · simpa [selIs, accessControlSelBytes] using h5
                    · simpa [selIs, accessControlSelBytes] using h1
                    · simpa [selIs, accessControlSelBytes] using h2
                    · simpa [selIs, accessControlSelBytes] using h4
                    · simpa [selIs, accessControlSelBytes] using h3
                    · simpa [selIs, accessControlSelBytes] using h6
                    · simpa [selIs, accessControlSelBytes] using h0
    · exact accessControlShortRevert hcode hsize hperm hwv (by omega)
  · exact accessControlNonPayable hcode hwv

end OpenZeppelinBench.AccessControl
