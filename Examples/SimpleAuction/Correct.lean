import Examples.SimpleAuction.Bytecode
import Examples.SimpleAuction.Spec
import Solm.Equiv

/-!
# SimpleAuction — correctness statement (proof TODO)

The deployed `SimpleAuction` runtime bytecode (`simpleAuctionBytecode`) refines its Solm spec
(`SimpleAuction.simpleAuctionContract`) under `simpleAuctionConfig`.  This file states the theorem;
the proof is future work.

Remaining obligations to discharge the proof (cf. `Examples/ERC20/Correct.lean`, which carries the
fully-worked version of this scaffold):

* **selector / dispatch facts** — the trusted keccak selectors (already known from `solc --hashes`:
  `bid() = 0x1998aeef`, `withdraw() = 0x3ccfd60b`, `auctionEnd() = 0x2a24f46c`,
  `beneficiary() = 0x38af3eed`, `auctionEndTime() = 0x4b449cba`, `highestBidder() = 0x91f90157`,
  `highestBid() = 0xd57bde79`) and the bytecode-derived valid jump set (`D_J … by native_decide`);
* **per-transition body refinements** — one obligation per dispatched function, reached from its
  body entry PC, including the `bid` payable path (no callvalue guard) and the `withdraw` /
  `auctionEnd` low-level value sends (`lowLevelCall`);
* **revert paths** — `callvalue ≠ 0` on the non-payable entries, short calldata, and no-match.
-/

open Solm

/-- **Correctness of `SimpleAuction` (statement only).**  Every external call to the deployed
    runtime bytecode behaves as its Solm specification prescribes.

    Proof is `sorry` for now: it depends on the dispatch/selector facts and the per-transition
    body refinements listed above. -/
theorem simpleAuctionCorrect :
    runtimeEquivalence!?! simpleAuctionConfig simpleAuctionBytecode
      SimpleAuction.simpleAuctionContract := by
  sorry
