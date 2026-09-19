import Solidity

/-! BlindAuction (`Examples/BlindAuction/BlindAuction.sol`, Solidity docs "Blind Auction") in the
Solidity spec language. -/

namespace BlindAuction.SoliditySpec

open _root_.Solidity _root_.Solidity.Notation

def blindAuction : SourceUnit := sol% contract BlindAuction {
  struct Bid {
    bytes32 blindedBid;
    uint deposit;
  }

  address payable public beneficiary;
  uint public biddingEnd;
  uint public revealEnd;
  bool public ended;

  mapping(address => Bid[]) public bids;

  address public highestBidder;
  uint public highestBid;

  mapping(address => uint) pendingReturns;

  event AuctionEnded(address winner, uint highestBid);

  error TooEarly(uint time);
  error TooLate(uint time);
  error AuctionEndAlreadyCalled();

  modifier onlyBefore(uint time) {
    if (block.timestamp >= time) revert TooLate(time);
    _;
  }
  modifier onlyAfter(uint time) {
    if (block.timestamp <= time) revert TooEarly(time);
    _;
  }

  constructor(
    uint biddingTime,
    uint revealTime,
    address payable beneficiaryAddress
  ) {
    beneficiary = beneficiaryAddress;
    biddingEnd = block.timestamp + biddingTime;
    revealEnd = biddingEnd + revealTime;
  }

  function bid(bytes32 blindedBid)
    external
    payable
    onlyBefore(biddingEnd)
  {
    bids[msg.sender].push(Bid({
      blindedBid: blindedBid,
      deposit: msg.value
    }));
  }

  function reveal(
    uint[] calldata values,
    bool[] calldata fakes,
    bytes32[] calldata secrets
  )
    external
    onlyAfter(biddingEnd)
    onlyBefore(revealEnd)
  {
    uint length = bids[msg.sender].length;
    require(values.length == length);
    require(fakes.length == length);
    require(secrets.length == length);

    uint refund;
    for (uint i = 0; i < length; i++) {
      Bid storage bidToCheck = bids[msg.sender][i];
      (uint value, bool fake, bytes32 secret) =
          (values[i], fakes[i], secrets[i]);
      if (bidToCheck.blindedBid != keccak256(abi.encodePacked(value, fake, secret))) {
        continue;
      }
      refund += bidToCheck.deposit;
      if (!fake && bidToCheck.deposit >= value) {
        if (placeBid(msg.sender, value))
          refund -= value;
      }
      bidToCheck.blindedBid = bytes32(0);
    }
    (bool success, ) = payable(msg.sender).call{value: refund}("");
    require(success);
  }

  function withdraw() external {
    uint amount = pendingReturns[msg.sender];
    if (amount > 0) {
      pendingReturns[msg.sender] = 0;

      (bool success, ) = payable(msg.sender).call{value: amount}("");
      require(success);
    }
  }

  function auctionEnd()
    external
    onlyAfter(revealEnd)
  {
    if (ended) revert AuctionEndAlreadyCalled();
    emit AuctionEnded(highestBidder, highestBid);
    ended = true;
    (bool success, ) = beneficiary.call{value: highestBid}("");
    require(success);
  }

  function placeBid(address bidder, uint value) internal
      returns (bool success)
  {
    if (value <= highestBid) {
      return false;
    }
    if (highestBidder != address(0)) {
      pendingReturns[highestBidder] += highestBid;
    }
    highestBid = value;
    highestBidder = bidder;
    return true;
  }
}

def program : Program := [blindAuction]
def target : String := "BlindAuction"

#guard (blindAuction.contract?.map (·.functions.length)) = some 5
#guard (blindAuction.contract?.map (·.modifiers.length)) = some 2

/-- Selectors as reported by `solc 0.8.35 --hashes` (checked natively by `solidity-diff --selectors`). -/
def selectors : List (String × String) :=
  [ ("auctionEnd()", "2a24f46c"),
    ("beneficiary()", "38af3eed"),
    ("bid(bytes32)", "957bb1e0"),
    ("biddingEnd()", "423b217f"),
    ("bids(address,uint256)", "01495c1c"),
    ("ended()", "12fa6feb"),
    ("highestBid()", "d57bde79"),
    ("highestBidder()", "91f90157"),
    ("reveal(uint256[],bool[],bytes32[])", "900f080a"),
    ("revealEnd()", "a6e66477"),
    ("withdraw()", "3ccfd60b") ]

end BlindAuction.SoliditySpec
