// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import {VestingWallet} from "../vendor/openzeppelin-contracts/contracts/finance/VestingWallet.sol";

contract VestingWalletBench is VestingWallet {
    constructor() payable VestingWallet(msg.sender, 0, 365 days) {}
}

