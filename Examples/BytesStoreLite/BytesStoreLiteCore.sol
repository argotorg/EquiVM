// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

contract BytesStoreLiteCore {
    bytes private current;

    function set(bytes calldata value) external returns (uint256 currentBytes) {
        bytes memory copy = value;
        current = copy;
        currentBytes = copy.length;
    }

    function clearCurrent() external returns (uint256 oldBytes) {
        bytes memory copy = current;
        oldBytes = copy.length;
        delete current;
    }

    function currentLength() external view returns (uint256) {
        return current.length;
    }
}
