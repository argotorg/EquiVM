import Examples.SimpleAuction.Bid
import Examples.SimpleAuction.Withdraw
import Examples.SimpleAuction.AuctionEnd
import Examples.SimpleAuction.Beneficiary
import Examples.SimpleAuction.AuctionEndTime
import Examples.SimpleAuction.HighestBidder
import Examples.SimpleAuction.HighestBid
import Reasoning.Refinement

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000

namespace SimpleAuction

/-!
# SimpleAuction — top-level correctness proof

This file is intentionally thin: it drives the payable binary-search dispatcher to the matched body
PC, then hands control to one per-function body theorem.
-/

/-- Calldata shorter than a selector (`size < 4`) reverts before Solm dispatch. -/
theorem simpleAuctionShortRevert {cA gh bl σ_evm σ₀_evm σ_solm σ₀_solm A I} {g : UInt256}
    (hcode : I.code = simpleAuctionBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hsz : I.calldata.size < 4) :
    runtimeEquivalenceFor simpleAuctionConfig simpleAuctionContract cA gh bl
      σ_evm σ₀_evm σ_solm σ₀_solm g A I := by
  exact (simpleAuctionX_short (g := Sat256.ofUInt256 g) hcode hsz).reEquivNoDispatch hcode
    (simpleAuctionDispatch_none_short hsz)

/-- `size ≥ 4` but no selector matches: no Solm dispatch and EVM fallthrough reverts. -/
theorem simpleAuctionNoDispatch {cA gh bl σ_evm σ₀_evm σ_solm σ₀_solm A I} {g : UInt256}
    (hcode : I.code = simpleAuctionBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true)
    (hnm : ∀ i, i < 7 → (simpleAuctionSelBytes i == I.calldata.extract 0 4) = false) :
    runtimeEquivalenceFor simpleAuctionConfig simpleAuctionContract cA gh bl
      σ_evm σ₀_evm σ_solm σ₀_solm g A I := by
  by_cases hsz : 4 ≤ I.calldata.size
  · exact (simpleAuctionX_noMatch (g := Sat256.ofUInt256 g) hcode hsz hsize hnm)
      |>.reEquivNoDispatch hcode (simpleAuctionDispatch_none_nomatch hnm)
  · have hshort : I.calldata.size < 4 := by omega
    exact (simpleAuctionX_short (g := Sat256.ofUInt256 g) hcode hshort).reEquivNoDispatch hcode
      (simpleAuctionDispatch_none_short hshort)

/-- The deployed SimpleAuction runtime bytecode refines the Solm specification. -/
theorem simpleAuctionCorrect :
    runtimeEquivalence!?! simpleAuctionConfig simpleAuctionBytecode simpleAuctionContract := by
  refine ⟨fun cA gh bl σ_evm σ₀_evm σ_solm σ₀_solm g A I hcode hsize hperm
      hAccounts _hOriginalAccounts => ?_⟩
  by_cases hsz : 4 ≤ I.calldata.size
  · by_cases h0 : selIs I ⟨#[0x19, 0x98, 0xae, 0xef]⟩
    · exact simpleAuctionBidBody hcode hsize hperm h0
        (simpleAuctionReachLowBody 0 (by omega) ⟨114⟩ hcode hsz hsize
          (simpleAuctionPivotTaken 0 (by omega) hsz
            (by simpa [selIs, simpleAuctionLowSelBytes] using h0))
          (simpleAuctionLowMatches 0 (by omega) hsz
            (by simpa [selIs, simpleAuctionLowSelBytes] using h0)).1
          (simpleAuctionLowMatches 0 (by omega) hsz
            (by simpa [selIs, simpleAuctionLowSelBytes] using h0)).2
          (by jump_dest) (by decide))
        hAccounts
    · by_cases h1 : selIs I ⟨#[0x3c, 0xcf, 0xd6, 0x0b]⟩
      · exact simpleAuctionWithdrawBody hcode hsize hperm h1
          (simpleAuctionReachHighBody 0 (by omega) ⟨203⟩ hcode hsz hsize
            (simpleAuctionPivotNotTaken 0 (by omega) hsz
              (by simpa [selIs, simpleAuctionHighSelBytes] using h1))
            (simpleAuctionHighMatches 0 (by omega) hsz
              (by simpa [selIs, simpleAuctionHighSelBytes] using h1)).1
            (simpleAuctionHighMatches 0 (by omega) hsz
              (by simpa [selIs, simpleAuctionHighSelBytes] using h1)).2
            (by jump_dest) (by decide))
          hAccounts _hOriginalAccounts
      · by_cases h2 : selIs I ⟨#[0x2a, 0x24, 0xf4, 0x6c]⟩
        · exact simpleAuctionAuctionEndBody hcode hsize hperm h2
            (simpleAuctionReachLowBody 1 (by omega) ⟨124⟩ hcode hsz hsize
              (simpleAuctionPivotTaken 1 (by omega) hsz
                (by simpa [selIs, simpleAuctionLowSelBytes] using h2))
              (simpleAuctionLowMatches 1 (by omega) hsz
                (by simpa [selIs, simpleAuctionLowSelBytes] using h2)).1
              (simpleAuctionLowMatches 1 (by omega) hsz
                (by simpa [selIs, simpleAuctionLowSelBytes] using h2)).2
              (by jump_dest) (by decide))
            hAccounts _hOriginalAccounts
        · by_cases h3 : selIs I ⟨#[0x38, 0xaf, 0x3e, 0xed]⟩
          · exact simpleAuctionBeneficiaryBody hcode hsize hperm h3
              (simpleAuctionReachLowBody 2 (by omega) ⟨144⟩ hcode hsz hsize
                (simpleAuctionPivotTaken 2 (by omega) hsz
                  (by simpa [selIs, simpleAuctionLowSelBytes] using h3))
                (simpleAuctionLowMatches 2 (by omega) hsz
                  (by simpa [selIs, simpleAuctionLowSelBytes] using h3)).1
                (simpleAuctionLowMatches 2 (by omega) hsz
                  (by simpa [selIs, simpleAuctionLowSelBytes] using h3)).2
                (by jump_dest) (by decide))
              hAccounts
          · by_cases h4 : selIs I ⟨#[0x4b, 0x44, 0x9c, 0xba]⟩
            · exact simpleAuctionAuctionEndTimeBody hcode hsize hperm h4
                (simpleAuctionReachHighBody 1 (by omega) ⟨239⟩ hcode hsz hsize
                  (simpleAuctionPivotNotTaken 1 (by omega) hsz
                    (by simpa [selIs, simpleAuctionHighSelBytes] using h4))
                  (simpleAuctionHighMatches 1 (by omega) hsz
                    (by simpa [selIs, simpleAuctionHighSelBytes] using h4)).1
                  (simpleAuctionHighMatches 1 (by omega) hsz
                    (by simpa [selIs, simpleAuctionHighSelBytes] using h4)).2
                  (by jump_dest) (by decide))
                hAccounts
            · by_cases h5 : selIs I ⟨#[0x91, 0xf9, 0x01, 0x57]⟩
              · exact simpleAuctionHighestBidderBody hcode hsize hperm h5
                  (simpleAuctionReachHighBody 2 (by omega) ⟨274⟩ hcode hsz hsize
                    (simpleAuctionPivotNotTaken 2 (by omega) hsz
                      (by simpa [selIs, simpleAuctionHighSelBytes] using h5))
                    (simpleAuctionHighMatches 2 (by omega) hsz
                      (by simpa [selIs, simpleAuctionHighSelBytes] using h5)).1
                    (simpleAuctionHighMatches 2 (by omega) hsz
                      (by simpa [selIs, simpleAuctionHighSelBytes] using h5)).2
                    (by jump_dest) (by decide))
                  hAccounts
              · by_cases h6 : selIs I ⟨#[0xd5, 0x7b, 0xde, 0x79]⟩
                · exact simpleAuctionHighestBidBody hcode hsize hperm h6
                    (simpleAuctionReachHighBody 3 (by omega) ⟨305⟩ hcode hsz hsize
                      (simpleAuctionPivotNotTaken 3 (by omega) hsz
                        (by simpa [selIs, simpleAuctionHighSelBytes] using h6))
                      (simpleAuctionHighMatches 3 (by omega) hsz
                        (by simpa [selIs, simpleAuctionHighSelBytes] using h6)).1
                      (simpleAuctionHighMatches 3 (by omega) hsz
                        (by simpa [selIs, simpleAuctionHighSelBytes] using h6)).2
                      (by jump_dest) (by decide))
                    hAccounts
                · refine simpleAuctionNoDispatch hcode hsize hperm ?_
                  intro i hi
                  interval_cases i
                  · simpa [selIs, simpleAuctionSelBytes] using h0
                  · simpa [selIs, simpleAuctionSelBytes] using h1
                  · simpa [selIs, simpleAuctionSelBytes] using h2
                  · simpa [selIs, simpleAuctionSelBytes] using h3
                  · simpa [selIs, simpleAuctionSelBytes] using h4
                  · simpa [selIs, simpleAuctionSelBytes] using h5
                  · simpa [selIs, simpleAuctionSelBytes] using h6
  · exact simpleAuctionShortRevert hcode hsize hperm (by omega)

end SimpleAuction
