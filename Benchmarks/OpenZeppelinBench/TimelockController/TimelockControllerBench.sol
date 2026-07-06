// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

import "../vendor/openzeppelin-contracts/contracts/governance/TimelockController.sol";

contract TimelockControllerBench is TimelockController {
    uint256 private constant INITIAL_MIN_DELAY = 1 days;

    constructor()
        payable
        TimelockController(INITIAL_MIN_DELAY, _singleton(msg.sender), _singleton(address(0)), msg.sender)
    {}

    function _singleton(address account) private pure returns (address[] memory values) {
        values = new address[](1);
        values[0] = account;
    }
}
