// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import {AccessControl} from "../vendor/openzeppelin-contracts/contracts/access/AccessControl.sol";

contract AccessControlBench is AccessControl {
    constructor() {
        _grantRole(DEFAULT_ADMIN_ROLE, msg.sender);
    }
}

