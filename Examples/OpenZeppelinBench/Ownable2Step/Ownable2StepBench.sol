// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import {Ownable2Step} from "../vendor/openzeppelin-contracts/contracts/access/Ownable2Step.sol";
import {Ownable} from "../vendor/openzeppelin-contracts/contracts/access/Ownable.sol";

contract Ownable2StepBench is Ownable2Step {
    constructor(address initialOwner) Ownable(initialOwner) {}
}

