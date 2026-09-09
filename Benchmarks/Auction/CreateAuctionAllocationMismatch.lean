import Benchmarks.Auction.UnpauseCreateAuction
import Ethereum.Theory.ReturnDataBound

open Ethereum Ethereum.EVM

namespace Auction

/-!
The error-string allocator's default free-memory pointer is 128.
That matches the `_createAuction` call from `unpause`, but settlement first allocates
the auction snapshot and leaves the pointer at 320, even when no payout is needed.
See `auctionSettleAuctionBurnCallMem_read64` and the settlement event trace.

The bytecode reads the current pointer at PC 5941 and passes it to the allocator at
PC 5868. Its upper-bound check is therefore on `fmp + rounded`, while the source
default check is on `128 + rounded`. The arithmetic witness below passes that check
and fails the bytecode check with `fmp = 320`. The candidate return-data length also
satisfies the existing gas-derived size bound and the preceding decoder bounds.

This certifies the allocator-guard mismatch. It is not a constructed execution of
the whole contract, and does not claim to refute the top-level theorem by itself.
The corrected specification passes the pointer through `settleAuctionWithMemoryFn`
and `createAuctionWithMemoryFn`. This witness records why the default cannot be used
for that call path. The top-level theorem has no additional assumptions.
-/

set_option maxRecDepth 4096 in
theorem auctionCreateAuctionAllocation_guardMismatch :
    let off : Nat := 32
    let len : Nat := 2 ^ 64 - 256
    let outSize : Nat := 2 ^ 64 - 188
    let rounded := errorStringRoundedAllocNat off len
    68 ≤ outSize ∧ outSize ≤ maxReturnDataSizeByGas ∧
    off ≤ ABI.solcMaxU64 ∧ len ≤ ABI.solcMaxU64 ∧
    off + 36 ≤ outSize ∧ off + len + 36 ≤ outSize ∧
    errorStringNewFreeNat off len = 2 ^ 64 - 64 ∧
    128 ≤ errorStringNewFreeNat off len ∧
    errorStringNewFreeNat off len ≤ ABI.solcMaxU64 ∧
    320 + rounded = 2 ^ 64 + 128 ∧
    ABI.solcMaxU64 < 320 + rounded ∧
    UInt256.gt ((⟨320⟩ : UInt256) +
      UInt256.land (UInt256.lnot (⟨31⟩ : UInt256))
        (((UInt256.ofNat off + UInt256.ofNat len) + ⟨32⟩) + ⟨31⟩))
      ⟨0xffffffffffffffff⟩ = ⟨1⟩ := by
  decide

end Auction
