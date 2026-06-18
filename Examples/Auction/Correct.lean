import Examples.Auction.Bytecode
import Examples.Auction.Spec
import Solm.Equiv

/-!
# Auction — correctness statement (proof TODO)

The deployed `NounsAuctionHouse` runtime bytecode refines its Solm spec (`Auction.auctionContract`)
under the auction config (`auctionConfig`).  This file states the theorem only; the proof — and the
real `auctionBytecode` it needs — are future work.
-/

open Solm

/-- **Correctness of `NounsAuctionHouse` (statement only).**  Every external call to the deployed
    runtime bytecode behaves as its Solm specification prescribes.

    Proof is `sorry` for now: it depends on the real compiled `auctionBytecode`
    (see `Examples/Auction/Bytecode.lean`) and on discharging the per-transition refinement
    (dispatch + bodies, including the `mint` try/catch and the WETH-fallback low-level send). -/
theorem auctionCorrect :
    runtimeEquivalence!?! auctionConfig auctionBytecode Auction.auctionContract := by
  sorry
