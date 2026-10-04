import Solidity

/-! Consts (`Solidity/Test/Fixtures/Consts.sol`): typed constants and file-level constants, errors
and events.  Harness input only. -/

namespace Consts.SoliditySpec

open _root_.Solidity _root_.Solidity.Notation

def wad : SourceUnit := sol% uint256 constant WAD = 10 ** 18;
def small : SourceUnit := sol% uint8 constant SMALL = 200;
def emptyUid : SourceUnit := sol% bytes32 constant EMPTY_UID = 0;
def burn : SourceUnit := sol% address constant BURN = 0x000000000000000000000000000000000000dEaD;

def accessDenied : SourceUnit := sol% error AccessDenied();
def tooLarge : SourceUnit := sol% error TooLarge(uint256 got, uint256 max);
def noted : SourceUnit := sol% event Noted(address indexed who, uint256 value);

def consts : SourceUnit := sol% contract Consts {
  uint256 constant A = 7;
  uint256 constant B = 2;
  uint8 public constant LIMIT = 250;
  bytes16 constant HEX = "0123456789abcdef";
  string public constant NAME = "Consts";
  address public constant SINK = 0x1111111111111111111111111111111111111111;
  bytes4 constant SEL = 0x12345678;
  int256 constant NEG = -5;

  address public last;

  function mulSmall() external pure returns (uint256) { return SMALL * 2; }
  function divConsts() external pure returns (uint256) { return A / B; }
  function wadMul(uint256 x) external pure returns (uint256) { return x * WAD / 2; }
  function limitPlus(uint8 d) external pure returns (uint8) { return LIMIT + d; }
  function hexDigit(uint8 v) external pure returns (bytes1) { return HEX[v & 0xf]; }
  function isBurn(address a) external pure returns (bool) { return a == BURN; }
  function setLast() external { last = BURN; }
  function uid() external pure returns (bytes32) { return EMPTY_UID; }
  function sel() external pure returns (bytes4) { return SEL; }
  function neg(int256 x) external pure returns (int256) { return x + NEG; }
  function deny(bool b) external pure { if (b) revert AccessDenied(); }
  function check(uint256 v) external pure { if (v > LIMIT) revert TooLarge(v, LIMIT); }
  function note(uint256 v) external { emit Noted(msg.sender, v); }
}

def program : Program := [wad, small, emptyUid, burn, accessDenied, tooLarge, noted, consts]

end Consts.SoliditySpec
