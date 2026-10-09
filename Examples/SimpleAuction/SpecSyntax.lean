import Examples.SimpleAuction.Spec
import Solm.Notation

/-!
# SimpleAuction spec in the Solidity-faithful Solm frontend

The `if (cond) revert E();` sites of the source are `require(!cond)` here, as in the AST spec
(custom-error payloads are dropped).  `bid` is payable; every other entry point gets the implicit
non-payable guard.
-/

open Solm Solm.Notation

namespace SimpleAuction.Syntax

def contractSyntax : ContractDecl := solidity% contract SimpleAuction {
  address beneficiary;
  uint256 auctionEndTime;
  address highestBidder;
  uint256 highestBid;
  mapping(address => uint256) pendingReturns;
  bool ended;

  constructor(uint256 biddingTime, address beneficiaryAddress) {
    beneficiary = beneficiaryAddress;
    auctionEndTime = (block.timestamp + biddingTime) as uint256;
  }

  function bid() external payable {
    require(block.timestamp <= auctionEndTime);
    require(msg.value > highestBid);
    if (highestBid != 0) {
      pendingReturns[highestBidder] = (pendingReturns[highestBidder] + highestBid) as uint256;
    }
    highestBidder = msg.sender;
    highestBid = msg.value;
  }

  function withdraw() external returns (bool) {
    uint256 amount = pendingReturns[msg.sender];
    if (amount > 0) {
      pendingReturns[msg.sender] = 0;
      (bool success, bytes memory _data) = msg.sender.call{value: amount}(new bytes(0));
      if (!success) {
        pendingReturns[msg.sender] = amount;
        return false;
      }
    }
    return true;
  }

  function auctionEnd() external {
    require(block.timestamp >= auctionEndTime);
    require(!ended);
    ended = true;
    (bool success, bytes memory _data) = beneficiary.call{value: highestBid}(new bytes(0));
    require(success);
  }

  function beneficiary() external returns (address) {
    return beneficiary;
  }

  function auctionEndTime() external returns (uint256) {
    return auctionEndTime;
  }

  function highestBidder() external returns (address) {
    return highestBidder;
  }

  function highestBid() external returns (uint256) {
    return highestBid;
  }
}

theorem contractSyntax_eq : contractSyntax = SimpleAuction.simpleAuctionContract := by rfl

end SimpleAuction.Syntax
