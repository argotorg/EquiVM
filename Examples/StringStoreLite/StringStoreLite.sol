// SPDX-License-Identifier: MIT
// Runtime bytecode can be generated with:
//   solc --bin-runtime --evm-version shanghai Examples/StringStoreLite/StringStoreLite.sol
// optimizer OFF.
pragma solidity ^0.8.20;

contract StringStoreLite {
    string private current; // slot 0: Solidity short/long string layout

    function set(string calldata value) external returns (uint256 currentBytes) {
        string memory copy = value;
        current = copy;
        currentBytes = bytes(copy).length;
    }

    function clearCurrent() external returns (uint256 oldBytes) {
        string memory copy = current;
        oldBytes = bytes(copy).length;
        delete current;
    }

    function currentLength() external view returns (uint256) {
        return bytes(current).length;
    }
}
