// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.23;

contract CtorTruth {
    constructor() payable { }

    function truth() external pure returns (bool) {
        return true;
    }
}
