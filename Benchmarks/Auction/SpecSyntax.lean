import Benchmarks.Auction.Spec
import Solm.Notation

/-!
# NounsAuctionHouse spec in the Solidity-faithful Solm frontend

The whole Nouns auction-house spec written with `solidity%` and proven definitionally equal to
the AST spec in `Spec.lean`.

Notes mirroring the AST spec:
* The flattened OpenZeppelin base storage (initializer flags, gaps, `_paused`, `_status`,
  `_owner`) is declared inline; the modifiers are the inlined `require`/assign prefixes.
* `_createAuction` carries the project's only `try/catch` (`nouns.mint()`); the `Error(string)`
  selector comparison splices the spec's `errorStringSelector` bytes literal.
* `_safeTransferETHWithFallback` is the raw low-level value send plus the WETH deposit/transfer
  fallback; `«to»` escapes the Lean keyword.
* Transition order matches `auctionContract.transitions`.
-/

open Solm Solm.Notation

namespace Auction.Syntax

def contractSyntax : ContractDecl := solidity% contract NounsAuctionHouse {
  struct Auction {
    uint256 nounId;
    uint256 amount;
    uint256 startTime;
    uint256 endTime;
    address bidder;
    bool settled;
  }

  bool _initialized;
  bool _initializing;
  uint256[50] __contextGap;
  bool _paused;
  uint256[49] __pausableGap;
  uint256 _status;
  uint256[49] __reentrancyGuardGap;
  address _owner;
  uint256[49] __ownableGap;
  address nouns;
  address weth;
  uint256 timeBuffer;
  uint256 reservePrice;
  uint8 minBidIncrementPercentage;
  uint256 duration;
  Auction auction;

  constructor() { }

  function _safeTransferETHWithFallback(address «to», uint256 amount) internal {
    (bool success, bytes memory _data) = «to».call{value: amount}(new bytes(0));
    if (!success) {
      require(weth.code.length > 0);
      var _dep = weth.deposit{value: amount}();
      var _xfer = weth.transfer(«to», amount);
    }
  }

  function _settleAuction() internal {
    var _auction = auction;
    require(_auction.startTime != 0);
    require(!_auction.settled);
    require(block.timestamp >= _auction.endTime);
    auction.settled = true;
    if (_auction.bidder == address(0)) {
      require(nouns.code.length > 0);
      var _burn = nouns.burn(_auction.nounId);
    } else {
      require(nouns.code.length > 0);
      var _tf = nouns.transferFrom(address(this), _auction.bidder, _auction.nounId);
    }
    if (_auction.amount > 0) {
      var _pay = _safeTransferETHWithFallback(_owner, _auction.amount);
    }
  }

  function _createAuction() internal {
    try nouns.mint() returns (nounId) {
      uint256 startTime = block.timestamp;
      uint256 endTime = (startTime + duration) as uint256;
      auction.nounId = nounId;
      auction.amount = 0;
      auction.startTime = startTime;
      auction.endTime = endTime;
      auction.bidder = address(0);
      auction.settled = false;
    } catch (err) {
      if (err[0 : 4] == ${Expr.bytesLit errorStringSelector}) {
        string _errString = abi.decode(err[4 : err.length], (string));
        require(!_paused);
        _paused = true;
      } else {
        require(false);
      }
    }
  }

  function «initialize»(address _nouns, address _weth, uint256 _timeBuffer,
      uint256 _reservePrice, uint8 _minBidIncrementPercentage, uint256 _duration) external {
    require(_initializing || !_initialized);
    bool isTopLevelCall = !_initializing;
    if (isTopLevelCall) {
      _initializing = true;
      _initialized = true;
    }
    _paused = false;
    _status = 1;
    _owner = msg.sender;
    require(!_paused);
    _paused = true;
    nouns = _nouns;
    weth = _weth;
    timeBuffer = _timeBuffer;
    reservePrice = _reservePrice;
    minBidIncrementPercentage = _minBidIncrementPercentage;
    duration = _duration;
    if (isTopLevelCall) {
      _initializing = false;
    }
  }

  function createBid(uint256 nounId) external payable {
    require(_status != 2);
    _status = 2;
    var _auction = auction;
    require(_auction.nounId == nounId);
    require(block.timestamp < _auction.endTime);
    require(msg.value >= reservePrice);
    require(msg.value >=
      ((_auction.amount + ((_auction.amount * minBidIncrementPercentage) as uint256) / 100) as uint256));
    address lastBidder = _auction.bidder;
    if (lastBidder != address(0)) {
      var _refund = _safeTransferETHWithFallback(lastBidder, _auction.amount);
    }
    auction.amount = msg.value;
    auction.bidder = msg.sender;
    bool extended = _auction.endTime - block.timestamp < timeBuffer;
    if (extended) {
      auction.endTime = (block.timestamp + timeBuffer) as uint256;
    }
    _status = 1;
  }

  function settleCurrentAndCreateNewAuction() external {
    require(_status != 2);
    _status = 2;
    require(!_paused);
    var _s = _settleAuction();
    var _c = _createAuction();
    _status = 1;
  }

  function settleAuction() external {
    require(_paused);
    require(_status != 2);
    _status = 2;
    var _s = _settleAuction();
    _status = 1;
  }

  function pause() external {
    require(msg.sender == _owner);
    require(!_paused);
    _paused = true;
  }

  function unpause() external {
    require(msg.sender == _owner);
    require(_paused);
    _paused = false;
    if (auction.startTime == 0 || auction.settled) {
      var _c = _createAuction();
    }
  }

  function setTimeBuffer(uint256 _timeBuffer) external {
    require(msg.sender == _owner);
    timeBuffer = _timeBuffer;
  }

  function setReservePrice(uint256 _reservePrice) external {
    require(msg.sender == _owner);
    reservePrice = _reservePrice;
  }

  function setMinBidIncrementPercentage(uint8 _minBidIncrementPercentage) external {
    require(msg.sender == _owner);
    minBidIncrementPercentage = _minBidIncrementPercentage;
  }

  function transferOwnership(address newOwner) external {
    require(msg.sender == _owner);
    require(newOwner != address(0));
    _owner = newOwner;
  }

  function renounceOwnership() external {
    require(msg.sender == _owner);
    _owner = address(0);
  }

  function owner() external returns (address) {
    return _owner;
  }

  function paused() external returns (bool) {
    return _paused;
  }

  function nouns() external returns (address) {
    return nouns;
  }

  function weth() external returns (address) {
    return weth;
  }

  function timeBuffer() external returns (uint256) {
    return timeBuffer;
  }

  function reservePrice() external returns (uint256) {
    return reservePrice;
  }

  function minBidIncrementPercentage() external returns (uint8) {
    return minBidIncrementPercentage;
  }

  function duration() external returns (uint256) {
    return duration;
  }

  function auction() external returns (uint256, uint256, uint256, uint256, address, bool) {
    return (auction.nounId, auction.amount, auction.startTime,
            auction.endTime, auction.bidder, auction.settled);
  }
}

theorem contractSyntax_eq : contractSyntax = Auction.auctionContract := by rfl

end Auction.Syntax
