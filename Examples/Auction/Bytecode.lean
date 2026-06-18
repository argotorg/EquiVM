import Examples.Auction.Spec

open Solm

/-! ## The contract's runtime bytecode

**TODO — PLACEHOLDER.**  This is *not* the real bytecode.  The deployed runtime of
`NounsAuctionHouse` must be produced by compiling `NounsAuctionHouse.sol` (solc `^0.8.6`, with its
`@openzeppelin/contracts-upgradeable` / `INounsToken` / `IWETH` dependency tree and the project's
optimizer settings) and pasting the deployed runtime bytes here as a `ByteArray`, exactly as in the
other examples' `Bytecode.lean`.

Once the real bytecode is in place, this file should also gain (as in `Truth`/`Caller`):
* `@[valid_jumps] theorem auctionValidJumps : D_J auctionBytecode 0 = #[…]` (by `native_decide`);
* the trusted keccak selector axioms for the dispatched transitions.

The empty placeholder lets the correctness *statement* (`Examples/Auction/Correct.lean`) typecheck;
it is obviously insufficient for any proof. -/
def auctionBytecode : ByteArray := ⟨#[]⟩
