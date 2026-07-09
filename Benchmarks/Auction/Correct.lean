import Benchmarks.Auction.Constructor
import Solm.Equiv

/-!
# Auction benchmark correctness stub

The upstream Solidity source closure, optimized runtime bytecode, creation bytecode, storage layout,
and external-call ABI model are present. The runtime-equivalence proof is intentionally left as the
benchmark target. This file also exposes the whole-contract wrapper that combines constructor and
runtime targets.
-/

open Solm ABI Ethereum Ethereum.EVM

theorem auctionCorrect :
    runtimeEquivalence!?! auctionConfig auctionBytecode Auction.auctionContract := by
  sorry

theorem auctionContractCorrect :
    contractEquivalence auctionConfig auctionCreationBytecode auctionBytecode Auction.auctionContract :=
  contractEquivalence.intro auctionConstructorCorrect auctionCorrect
