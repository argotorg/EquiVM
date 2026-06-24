// SPDX-License-Identifier: MIT
// Runtime bytecode can be generated with:
//   solc --bin-runtime --evm-version shanghai Examples/StringStore/StringStore.sol
// optimizer OFF.
pragma solidity ^0.8.20;

contract StringStore {
    string private current;   // slot 0: Solidity short/long string layout
    string[] private history; // slot 1: dynamic array; each element is a string slot
    bytes private raw;        // slot 2: Solidity short/long bytes layout

    function set(string calldata value) external returns (uint256 currentBytes) {
        string memory copy = value;
        bytes memory rawCopy = bytes(copy);

        current = copy;
        history.push(copy);
        raw = rawCopy;

        currentBytes = rawCopy.length;
    }

    function appendToHistory(string calldata suffix) external returns (uint256 historyLength_) {
        string memory copy = suffix;

        history.push(copy);

        historyLength_ = history.length;
    }

    function replaceFromHistory(uint256 index) external returns (uint256 currentBytes) {
        string memory copy = history[index];
        bytes memory rawCopy = bytes(copy);

        current = copy;
        raw = rawCopy;

        currentBytes = rawCopy.length;
    }

    function dropLast() external returns (string memory removed) {
        uint256 length = history.length;
        require(length > 0);

        removed = history[length - 1];
        history.pop();
    }

    function clearCurrent() external returns (bytes32 oldDigest) {
        delete current;
        oldDigest = keccak256(new bytes(0));
    }

    function clearAll() external {
        delete current;
        delete raw;
        delete history;
    }

    function storeRaw(bytes calldata value) external returns (bytes32 digest) {
        bytes memory copy = value;
        raw = copy;

        if (copy.length != 0) {
            raw.push(copy[0]);
            raw.pop();
        }

        digest = keccak256(new bytes(0));
    }

    function currentLength() external view returns (uint256) {
        string memory copy = current;
        return bytes(copy).length;
    }

    function historyLength() external view returns (uint256) {
        return history.length;
    }

    function rawLength() external view returns (uint256) {
        return raw.length;
    }
}
