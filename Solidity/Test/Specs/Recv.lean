import Solidity.Notation

/-! Recv (`Solidity/Test/Fixtures/Recv.sol`).  Harness input only. -/

namespace Recv.SoliditySpec

open _root_.Solidity _root_.Solidity.Notation

def recvFb : SourceUnit := sol% contract RecvFb {
  uint256 public got;
  uint256 public fb;
  bytes public data;
  receive() external payable { got += msg.value + 1; }
  fallback() external payable { fb += msg.value + 1; data = msg.data; }
  function f(uint256 x) external pure returns (uint256) { return x + 1; }
}

def fbOnly : SourceUnit := sol% contract FbOnly {
  uint256 public fb;
  fallback() external { fb += 1; }
  function f() external pure returns (uint256) { return 7; }
}

def fbData : SourceUnit := sol% contract FbData {
  uint256 public n;
  fallback(bytes calldata input) external payable returns (bytes memory) {
    n += 1;
    return abi.encodePacked(input, uint8(n));
  }
}

def recvOnly : SourceUnit := sol% contract RecvOnly {
  uint256 public got;
  receive() external payable { got += 1; }
  function g(uint256 x) external payable returns (uint256) { return x; }
}

def noFb : SourceUnit := sol% contract NoFb {
  function g(uint256 x) external pure returns (uint256) { return x; }
}

def programRecvFb : Program := [recvFb]
def programFbOnly : Program := [fbOnly]
def programFbData : Program := [fbData]
def programRecvOnly : Program := [recvOnly]
def programNoFb : Program := [noFb]

end Recv.SoliditySpec
