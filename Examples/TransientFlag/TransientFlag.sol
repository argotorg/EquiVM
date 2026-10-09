// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

contract TransientFlag {
    uint256 transient flag;

    function setFlag(uint256 v) external {
        flag = v;
    }

    function getFlag() external view returns (uint256) {
        return flag;
    }
}
