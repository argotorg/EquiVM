import Solidity

/-!
# OpenZeppelin utility bases (Solidity spec language)

Transcribed from `Examples/OpenZeppelinBench/vendor/openzeppelin-contracts/contracts/`:
`utils/Context.sol`, `utils/introspection/IERC165.sol`, `utils/introspection/ERC165.sol`,
`utils/Pausable.sol`.  Shared by the bench programs.
-/

namespace OpenZeppelinBench.OZ

open _root_.Solidity _root_.Solidity.Notation

def context : SourceUnit := sol% abstract contract Context {
  function _msgSender() internal view virtual returns (address) {
    return msg.sender;
  }

  function _msgData() internal view virtual returns (bytes calldata) {
    return msg.data;
  }

  function _contextSuffixLength() internal view virtual returns (uint256) {
    return 0;
  }
}

def ierc165 : SourceUnit := sol% interface IERC165 {
  function supportsInterface(bytes4 interfaceId) external view returns (bool);
}

def erc165 : SourceUnit := sol% abstract contract ERC165 is IERC165 {
  function supportsInterface(bytes4 interfaceId) public view virtual returns (bool) {
    return interfaceId == type(IERC165).interfaceId;
  }
}

def pausable : SourceUnit := sol% abstract contract Pausable is Context {
  bool private _paused;

  event Paused(address account);
  event Unpaused(address account);

  error EnforcedPause();
  error ExpectedPause();

  modifier whenNotPaused() {
    _requireNotPaused();
    _;
  }

  modifier whenPaused() {
    _requirePaused();
    _;
  }

  function paused() public view virtual returns (bool) {
    return _paused;
  }

  function _requireNotPaused() internal view virtual {
    if (paused()) {
      revert EnforcedPause();
    }
  }

  function _requirePaused() internal view virtual {
    if (!paused()) {
      revert ExpectedPause();
    }
  }

  function _pause() internal virtual whenNotPaused {
    _paused = true;
    emit Paused(_msgSender());
  }

  function _unpause() internal virtual whenPaused {
    _paused = false;
    emit Unpaused(_msgSender());
  }
}

end OpenZeppelinBench.OZ
