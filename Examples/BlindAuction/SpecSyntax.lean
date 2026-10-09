import Examples.BlindAuction.Spec
import Solm.Notation

/-!
# BlindAuction spec in the Solidity-faithful Solm frontend

Covers the mapping-to-struct-array `push`, the storage alias inside `reveal`'s loop, the
`keccak256(abi.encodePacked(…))` guard (packed operands carry their ABI types as `T(e)`
annotations), the internal `placeBid` helper, and the two-key `bids(address,uint256)` getter.

One escape: the AST spec models `bidToCheck.blindedBid = bytes32(0)` as a *cast*
(`.cast (.intLit 0) bytes32St`), while surface `bytes32(0)` is the fixed-bytes literal — so that
single right-hand side is written with `${…}`.
-/

open Solm Solm.Notation

namespace BlindAuction.Syntax

def contractSyntax : ContractDecl := solidity% contract BlindAuction {
  struct Bid {
    bytes32 blindedBid;
    uint256 deposit;
  }

  address beneficiary;
  uint256 biddingEnd;
  uint256 revealEnd;
  bool ended;
  mapping(address => Bid[]) bids;
  address highestBidder;
  uint256 highestBid;
  mapping(address => uint256) pendingReturns;

  constructor(uint256 biddingTime, uint256 revealTime, address beneficiaryAddress) {
    beneficiary = beneficiaryAddress;
    biddingEnd = (block.timestamp + biddingTime) as uint256;
    revealEnd = (biddingEnd + revealTime) as uint256;
  }

  function placeBid(address bidder, uint256 value) internal returns (bool) {
    if (value <= highestBid) {
      return false;
    }
    if (highestBidder != address(0)) {
      pendingReturns[highestBidder] = (pendingReturns[highestBidder] + highestBid) as uint256;
    }
    highestBid = value;
    highestBidder = bidder;
    return true;
  }

  function bid(bytes32 blindedBid) external payable {
    require(block.timestamp < biddingEnd);
    bids[msg.sender].push(Bid({blindedBid: blindedBid, deposit: msg.value}));
  }

  function reveal(uint256[] calldata values, bool[] calldata fakes, bytes32[] calldata secrets) external {
    require(block.timestamp > biddingEnd);
    require(block.timestamp < revealEnd);
    uint256 length = bids[msg.sender].length;
    require(values.length == length);
    require(fakes.length == length);
    require(secrets.length == length);
    uint256 refund = 0;
    for (uint256 i = 0; i < length; i++) {
      Bid storage bidToCheck = bids[msg.sender][i];
      uint256 value = values[i];
      bool fake = fakes[i];
      bytes32 secret = secrets[i];
      if (bidToCheck.blindedBid != keccak256(abi.encodePacked(uint256(value), bool(fake), bytes32(secret)))) {
        continue;
      }
      refund = (refund + bidToCheck.deposit) as uint256;
      if (!fake && bidToCheck.deposit >= value) {
        var ok = placeBid(msg.sender, value);
        if (ok) {
          refund = (refund - value) as uint256;
        }
      }
      bidToCheck.blindedBid = ${Expr.cast (.intLit 0) BlindAuction.bytes32St};
    }
    (bool success, bytes memory _data) = msg.sender.call{value: refund}(new bytes(0));
    require(success);
  }

  function withdraw() external {
    uint256 amount = pendingReturns[msg.sender];
    if (amount > 0) {
      pendingReturns[msg.sender] = 0;
      (bool success, bytes memory _data) = msg.sender.call{value: amount}(new bytes(0));
      require(success);
    }
  }

  function auctionEnd() external {
    require(block.timestamp > revealEnd);
    require(!ended);
    ended = true;
    (bool success, bytes memory _data) = beneficiary.call{value: highestBid}(new bytes(0));
    require(success);
  }

  function beneficiary() external returns (address) {
    return beneficiary;
  }

  function biddingEnd() external returns (uint256) {
    return biddingEnd;
  }

  function revealEnd() external returns (uint256) {
    return revealEnd;
  }

  function ended() external returns (bool) {
    return ended;
  }

  function highestBidder() external returns (address) {
    return highestBidder;
  }

  function highestBid() external returns (uint256) {
    return highestBid;
  }

  function bids(address a, uint256 i) external returns (bytes32, uint256) {
    return (bids[a][i].blindedBid, bids[a][i].deposit);
  }
}

theorem contractSyntax_eq : contractSyntax = BlindAuction.blindAuctionContract := by rfl

end BlindAuction.Syntax
