// SPDX-License-Identifier: MIT
// Compiled with the OPTIMIZER ON (this is the realistic target):
//   solc --optimize --evm-version shanghai --bin-runtime Examples/Ownable2Step/Ownable2Step.sol
// (solc 0.8.35, Shanghai => PUSH0).  Runtime bytecode + selector/jump facts live in Bytecode.lean.
//
// Flattened OpenZeppelin-style Ownable2Step (the recommended two-step ownership-transfer pattern).
// Inheritance/modifiers inlined.  Self-contained: no external calls, no loops.
pragma solidity ^0.8.20;

contract Ownable2Step {
    address private _owner;          // slot 0
    address private _pendingOwner;   // slot 1

    constructor() {
        _owner = msg.sender;
    }

    function owner() public view returns (address) {
        return _owner;
    }

    function pendingOwner() public view returns (address) {
        return _pendingOwner;
    }

    function transferOwnership(address newOwner) public {
        require(_owner == msg.sender, "NOT_OWNER");
        _pendingOwner = newOwner;
    }

    function acceptOwnership() public {
        require(_pendingOwner == msg.sender, "NOT_PENDING");
        _pendingOwner = address(0);
        _owner = msg.sender;
    }

    function renounceOwnership() public {
        require(_owner == msg.sender, "NOT_OWNER");
        _pendingOwner = address(0);
        _owner = address(0);
    }
}
