import Solidity

/-! SimpleAuction (`Examples/SimpleAuction/SimpleAuction.sol`, Solidity docs "Simple Open
Auction") in the Solidity spec language. -/

namespace SimpleAuction.SoliditySpec

open _root_.Solidity _root_.Solidity.Notation

def simpleAuction : SourceUnit := sol% contract SimpleAuction {
  address payable public beneficiary;
  uint public auctionEndTime;

  address public highestBidder;
  uint public highestBid;

  mapping(address => uint) pendingReturns;

  bool ended;

  event HighestBidIncreased(address bidder, uint amount);
  event AuctionEnded(address winner, uint amount);

  error AuctionAlreadyEnded();
  error BidNotHighEnough(uint highestBid);
  error AuctionNotYetEnded();
  error AuctionEndAlreadyCalled();

  constructor(
    uint biddingTime,
    address payable beneficiaryAddress
  ) {
    beneficiary = beneficiaryAddress;
    auctionEndTime = block.timestamp + biddingTime;
  }

  function bid() external payable {
    if (block.timestamp > auctionEndTime)
      revert AuctionAlreadyEnded();

    if (msg.value <= highestBid)
      revert BidNotHighEnough(highestBid);

    if (highestBid != 0) {
      pendingReturns[highestBidder] += highestBid;
    }
    highestBidder = msg.sender;
    highestBid = msg.value;
    emit HighestBidIncreased(msg.sender, msg.value);
  }

  function withdraw() external returns (bool) {
    uint amount = pendingReturns[msg.sender];
    if (amount > 0) {
      pendingReturns[msg.sender] = 0;

      (bool success, ) = payable(msg.sender).call{value: amount}("");
      if (!success) {
        pendingReturns[msg.sender] = amount;
        return false;
      }
    }
    return true;
  }

  function auctionEnd() external {
    if (block.timestamp < auctionEndTime)
      revert AuctionNotYetEnded();
    if (ended)
      revert AuctionEndAlreadyCalled();

    ended = true;
    emit AuctionEnded(highestBidder, highestBid);

    (bool success, ) = beneficiary.call{value: highestBid}("");
    require(success);
  }
}

def program : Program := [simpleAuction]
def target : String := "SimpleAuction"

#guard (simpleAuction.contract?.map (·.functions.length)) = some 3
#guard (simpleAuction.contract?.map (·.errors.length)) = some 4

/-- Selectors as reported by `solc 0.8.35 --hashes` (checked natively by `solidity-diff --selectors`). -/
def selectors : List (String × String) :=
  [ ("auctionEnd()", "2a24f46c"),
    ("auctionEndTime()", "4b449cba"),
    ("beneficiary()", "38af3eed"),
    ("bid()", "1998aeef"),
    ("highestBid()", "d57bde79"),
    ("highestBidder()", "91f90157"),
    ("withdraw()", "3ccfd60b") ]

end SimpleAuction.SoliditySpec
