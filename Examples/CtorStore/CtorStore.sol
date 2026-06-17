// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.23;

contract CtorStore {
    uint256 private stored;

    constructor(uint256 x) payable {
        stored = x;
    }
}
