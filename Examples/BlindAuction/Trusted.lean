import Examples.BlindAuction.Bytecode

open Solm Ethereum Ethereum.EVM

namespace BlindAuction

/-!
# BlindAuction trusted bytecode facts

These Phase 0 facts are kept out of `Bytecode.lean`.  The selector facts are trusted because
`ffi.KEC` is opaque to Lean; the valid jump table is computed from the byte array by `native_decide`.
-/

/-- `keccak("bid(bytes32)")[0:4] = 0x957bb1e0`. -/
axiom blindAuctionBidSelectorBytes :
    (ffi.KEC (String.toByteArray (Solm.transitionSigStr bidTransition))).extract 0 4 =
      ⟨#[0x95, 0x7b, 0xb1, 0xe0]⟩

/-- `keccak("reveal(uint256[],bool[],bytes32[])")[0:4] = 0x900f080a`. -/
axiom blindAuctionRevealSelectorBytes :
    (ffi.KEC (String.toByteArray (Solm.transitionSigStr revealTransition))).extract 0 4 =
      ⟨#[0x90, 0x0f, 0x08, 0x0a]⟩

/-- `keccak("withdraw()")[0:4] = 0x3ccfd60b`. -/
axiom blindAuctionWithdrawSelectorBytes :
    (ffi.KEC (String.toByteArray (Solm.transitionSigStr withdrawTransition))).extract 0 4 =
      ⟨#[0x3c, 0xcf, 0xd6, 0x0b]⟩

/-- `keccak("auctionEnd()")[0:4] = 0x2a24f46c`. -/
axiom blindAuctionAuctionEndSelectorBytes :
    (ffi.KEC (String.toByteArray (Solm.transitionSigStr auctionEndTransition))).extract 0 4 =
      ⟨#[0x2a, 0x24, 0xf4, 0x6c]⟩

/-- `keccak("beneficiary()")[0:4] = 0x38af3eed`. -/
axiom blindAuctionBeneficiarySelectorBytes :
    (ffi.KEC (String.toByteArray (Solm.transitionSigStr beneficiaryGetter))).extract 0 4 =
      ⟨#[0x38, 0xaf, 0x3e, 0xed]⟩

/-- `keccak("biddingEnd()")[0:4] = 0x423b217f`. -/
axiom blindAuctionBiddingEndSelectorBytes :
    (ffi.KEC (String.toByteArray (Solm.transitionSigStr biddingEndGetter))).extract 0 4 =
      ⟨#[0x42, 0x3b, 0x21, 0x7f]⟩

/-- `keccak("revealEnd()")[0:4] = 0xa6e66477`. -/
axiom blindAuctionRevealEndSelectorBytes :
    (ffi.KEC (String.toByteArray (Solm.transitionSigStr revealEndGetter))).extract 0 4 =
      ⟨#[0xa6, 0xe6, 0x64, 0x77]⟩

/-- `keccak("ended()")[0:4] = 0x12fa6feb`. -/
axiom blindAuctionEndedSelectorBytes :
    (ffi.KEC (String.toByteArray (Solm.transitionSigStr endedGetter))).extract 0 4 =
      ⟨#[0x12, 0xfa, 0x6f, 0xeb]⟩

/-- `keccak("highestBidder()")[0:4] = 0x91f90157`. -/
axiom blindAuctionHighestBidderSelectorBytes :
    (ffi.KEC (String.toByteArray (Solm.transitionSigStr highestBidderGetter))).extract 0 4 =
      ⟨#[0x91, 0xf9, 0x01, 0x57]⟩

/-- `keccak("highestBid()")[0:4] = 0xd57bde79`. -/
axiom blindAuctionHighestBidSelectorBytes :
    (ffi.KEC (String.toByteArray (Solm.transitionSigStr highestBidGetter))).extract 0 4 =
      ⟨#[0xd5, 0x7b, 0xde, 0x79]⟩

/-- `keccak("bids(address,uint256)")[0:4] = 0x01495c1c`. -/
axiom blindAuctionBidsSelectorBytes :
    (ffi.KEC (String.toByteArray (Solm.transitionSigStr bidsGetter))).extract 0 4 =
      ⟨#[0x01, 0x49, 0x5c, 0x1c]⟩

/-- The `JUMPDEST` set of `blindAuctionBytecode`, confirmed from the bytecode disassembly. -/
@[valid_jumps] theorem blindAuctionValidJumps :
    Ethereum.EVM.D_J blindAuctionBytecode 0 =
      #[⟨98⟩, ⟨154⟩, ⟨158⟩, ⟨169⟩, ⟨184⟩, ⟨189⟩, ⟨206⟩, ⟨215⟩, ⟨226⟩,
        ⟨240⟩, ⟨256⟩, ⟨267⟩, ⟨276⟩, ⟨278⟩, ⟨289⟩, ⟨308⟩, ⟨332⟩, ⟨343⟩,
        ⟨352⟩, ⟨363⟩, ⟨373⟩, ⟨387⟩, ⟨398⟩, ⟨413⟩, ⟨418⟩, ⟨429⟩, ⟨449⟩,
        ⟨463⟩, ⟨468⟩, ⟨479⟩, ⟨489⟩, ⟨500⟩, ⟨510⟩, ⟨535⟩, ⟨566⟩, ⟨600⟩,
        ⟨609⟩, ⟨645⟩, ⟨754⟩, ⟨812⟩, ⟨817⟩, ⟨830⟩, ⟨834⟩, ⟨884⟩, ⟨887⟩,
        ⟨925⟩, ⟨963⟩, ⟨989⟩, ⟨1000⟩, ⟨1011⟩, ⟨1014⟩, ⟨1054⟩, ⟨1089⟩,
        ⟨1114⟩, ⟨1135⟩, ⟨1153⟩, ⟨1207⟩, ⟨1247⟩, ⟨1262⟩, ⟨1282⟩,
        ⟨1297⟩, ⟨1312⟩, ⟨1315⟩, ⟨1323⟩, ⟨1331⟩, ⟨1395⟩, ⟨1400⟩,
        ⟨1413⟩, ⟨1426⟩, ⟨1464⟩, ⟨1534⟩, ⟨1551⟩, ⟨1612⟩, ⟨1618⟩,
        ⟨1654⟩, ⟨1660⟩, ⟨1677⟩, ⟨1699⟩, ⟨1713⟩, ⟨1729⟩, ⟨1752⟩,
        ⟨1778⟩, ⟨1785⟩, ⟨1806⟩, ⟨1828⟩, ⟨1840⟩, ⟨1871⟩, ⟨1883⟩,
        ⟨1914⟩, ⟨1926⟩, ⟨1944⟩, ⟨1960⟩, ⟨1967⟩, ⟨1987⟩, ⟨2003⟩,
        ⟨2018⟩, ⟨2025⟩, ⟨2045⟩, ⟨2064⟩] := by
  native_decide

end BlindAuction
