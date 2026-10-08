// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

/// Differential-test fixture: the Solm statement forms no example or benchmark exercises
/// (contract creation with and without salt, `for` with `break`/`continue`, `try`/`catch`,
/// array `pop` and `delete`).

contract Child {
    uint256 public x;

    constructor(uint256 x_) payable {
        x = x_;
    }

    function get() external view returns (uint256) {
        return x;
    }
}

contract Factory {
    address[] public children;
    uint256 public total;

    function make(uint256 n, uint256 seed) external payable returns (address last) {
        for (uint256 i = 0; i < n; i++) {
            if (i == 4) break;
            if (seed % 2 == 1 && i == 1) continue;
            Child c = new Child{value: i}(seed + i);
            children.push(address(c));
            total += 1;
            last = address(c);
        }
    }

    function make2(bytes32 salt, uint256 v) external returns (address) {
        Child c = new Child{salt: salt}(v);
        children.push(address(c));
        return address(c);
    }

    function tryGet(address c) external view returns (bool ok, uint256 v) {
        try Child(c).get() returns (uint256 r) {
            return (true, r);
        } catch {
            return (false, 0);
        }
    }

    function popChild() external {
        children.pop();
    }

    function clear() external {
        delete children;
    }

    function count() external view returns (uint256) {
        return children.length;
    }
}
