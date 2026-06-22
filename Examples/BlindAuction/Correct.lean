import Examples.BlindAuction.Bytecode
import Examples.BlindAuction.Spec
import Solm.Equiv

/-!
# BlindAuction — correctness statement (proof TODO)

The deployed `BlindAuction` runtime bytecode (`blindAuctionBytecode`) refines its Solm spec
(`BlindAuction.blindAuctionContract`) under `blindAuctionConfig`.  This file states the theorem;
the proof is future work.

Remaining obligations to discharge the proof (cf. `Examples/ERC20/Correct.lean`, the fully-worked
version of this scaffold):

* **selector / dispatch facts** — the trusted keccak selectors (from `solc --hashes`:
  `bid(bytes32) = 0x957bb1e0`, `reveal(uint256[],bool[],bytes32[]) = 0x900f080a`,
  `withdraw() = 0x3ccfd60b`, `auctionEnd() = 0x2a24f46c`, `beneficiary() = 0x38af3eed`,
  `biddingEnd() = 0x423b217f`, `revealEnd() = 0xa6e66477`, `ended() = 0x12fa6feb`,
  `highestBidder() = 0x91f90157`, `highestBid() = 0xd57bde79`, `bids(address,uint256) = 0x01495c1c`)
  and the bytecode-derived valid jump set (`D_J … by native_decide`);
* **per-transition body refinements** — one obligation per dispatched function, reached from its
  body entry PC.  The hard one is `reveal`: the `for` loop over `bids[msg.sender]`, the
  `keccak256(abi.encodePacked(value, fake, secret))` guard (the equivalence reduces to the packed
  bytes solc lays out in memory matching `encodePackedValue?`, since both sides hash via `ffi.KEC`),
  the internal `placeBid` call, and the refund `lowLevelCall`;
* **revert paths** — `callvalue ≠ 0` on the non-payable entries, short calldata, and no-match.
-/

open Solm

/-- **Correctness of `BlindAuction` (statement only).**  Every external call to the deployed runtime
    bytecode behaves as its Solm specification prescribes.

    Proof is `sorry` for now: it depends on the dispatch/selector facts and the per-transition body
    refinements listed above (notably the `reveal` hash/loop body). -/
theorem blindAuctionCorrect :
    runtimeEquivalence!?! blindAuctionConfig blindAuctionBytecode
      BlindAuction.blindAuctionContract := by
  sorry
