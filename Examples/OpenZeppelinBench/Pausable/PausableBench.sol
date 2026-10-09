// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import {Pausable} from "../vendor/openzeppelin-contracts/contracts/utils/Pausable.sol";

contract PausableBench is Pausable {
    function pause() external {
        _pause();
    }

    function unpause() external {
        _unpause();
    }

    function guardedWhenNotPaused() external view whenNotPaused returns (bool) {
        return true;
    }

    function guardedWhenPaused() external view whenPaused returns (bool) {
        return true;
    }
}

