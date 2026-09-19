// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

contract Child {
    uint public x;
    address public creator;

    constructor(uint v) payable {
        require(v != 7, "seven");
        x = v;
        creator = msg.sender;
    }

    function get() external view returns (uint) {
        return x;
    }
}

contract Factory {
    address public last;
    uint public count;

    function make(uint v) external payable returns (address) {
        Child c = new Child{value: msg.value}(v);
        last = address(c);
        count += 1;
        return address(c);
    }

    function make2(uint v, bytes32 salt) external returns (address) {
        Child c = new Child{salt: salt}(v);
        last = address(c);
        return address(c);
    }

    function makeAndRead(uint v) external returns (uint) {
        Child c = new Child(v);
        return c.get() + 1;
    }
}
