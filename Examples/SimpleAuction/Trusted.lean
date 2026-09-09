import Examples.SimpleAuction.Bytecode

open Solm Ethereum Ethereum.EVM

namespace SimpleAuction

/-!
# SimpleAuction trusted bytecode facts

These are the Phase 0 facts the proof needs but `Bytecode.lean` intentionally did not contain.
The selector facts are trusted because `ffi.KEC` is opaque to Lean.  The jump-destination table is
computed from the byte array by `decide +native`.
-/

/-- `keccak("bid()")[0:4] = 0x1998aeef`. -/
axiom simpleAuctionBidSelectorBytes :
    (ffi.KEC (String.toByteArray (Solm.transitionSigStr bidTransition))).extract 0 4 =
      ⟨#[0x19, 0x98, 0xae, 0xef]⟩

/-- `keccak("withdraw()")[0:4] = 0x3ccfd60b`. -/
axiom simpleAuctionWithdrawSelectorBytes :
    (ffi.KEC (String.toByteArray (Solm.transitionSigStr withdrawTransition))).extract 0 4 =
      ⟨#[0x3c, 0xcf, 0xd6, 0x0b]⟩

/-- `keccak("auctionEnd()")[0:4] = 0x2a24f46c`. -/
axiom simpleAuctionAuctionEndSelectorBytes :
    (ffi.KEC (String.toByteArray (Solm.transitionSigStr auctionEndTransition))).extract 0 4 =
      ⟨#[0x2a, 0x24, 0xf4, 0x6c]⟩

/-- `keccak("beneficiary()")[0:4] = 0x38af3eed`. -/
axiom simpleAuctionBeneficiarySelectorBytes :
    (ffi.KEC (String.toByteArray (Solm.transitionSigStr beneficiaryGetter))).extract 0 4 =
      ⟨#[0x38, 0xaf, 0x3e, 0xed]⟩

/-- `keccak("auctionEndTime()")[0:4] = 0x4b449cba`. -/
axiom simpleAuctionAuctionEndTimeSelectorBytes :
    (ffi.KEC (String.toByteArray (Solm.transitionSigStr auctionEndTimeGetter))).extract 0 4 =
      ⟨#[0x4b, 0x44, 0x9c, 0xba]⟩

/-- `keccak("highestBidder()")[0:4] = 0x91f90157`. -/
axiom simpleAuctionHighestBidderSelectorBytes :
    (ffi.KEC (String.toByteArray (Solm.transitionSigStr highestBidderGetter))).extract 0 4 =
      ⟨#[0x91, 0xf9, 0x01, 0x57]⟩

/-- `keccak("highestBid()")[0:4] = 0xd57bde79`. -/
axiom simpleAuctionHighestBidSelectorBytes :
    (ffi.KEC (String.toByteArray (Solm.transitionSigStr highestBidGetter))).extract 0 4 =
      ⟨#[0xd5, 0x7b, 0xde, 0x79]⟩

/-- The `JUMPDEST` set of `simpleAuctionBytecode`, confirmed from the bytecode disassembly. -/
@[valid_jumps] theorem simpleAuctionValidJumps :
    Ethereum.EVM.D_J simpleAuctionBytecode 0 =
      #[⟨76⟩, ⟨110⟩, ⟨114⟩, ⟨122⟩, ⟨124⟩, ⟨135⟩, ⟨144⟩, ⟨155⟩, ⟨174⟩,
        ⟨194⟩, ⟨203⟩, ⟨214⟩, ⟨223⟩, ⟨239⟩, ⟨250⟩, ⟨260⟩, ⟨274⟩, ⟨285⟩,
        ⟨305⟩, ⟨316⟩, ⟨326⟩, ⟨361⟩, ⟨401⟩, ⟨410⟩, ⟨462⟩, ⟨468⟩, ⟨555⟩,
        ⟨590⟩, ⟨626⟩, ⟨788⟩, ⟨793⟩, ⟨806⟩, ⟨809⟩, ⟨908⟩, ⟨913⟩, ⟨946⟩,
        ⟨948⟩, ⟨956⟩, ⟨987⟩] := by
  decide +native

end SimpleAuction
