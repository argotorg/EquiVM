// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

/// End-to-end validation contract for the scaffold pipeline: immutables set by a constructor
/// with arguments, a modifier, a mapping, a dynamic array with push and pop, typed external
/// calls with return values, events, checked arithmetic and revert strings.

interface IERC20 {
    function transfer(address to, uint256 amount) external returns (bool);
    function transferFrom(address from, address to, uint256 amount) external returns (bool);
    function balanceOf(address account) external view returns (uint256);
}

contract Vault {
    address public immutable owner;
    uint256 public immutable feeBps;
    IERC20 public token;
    mapping(address => uint256) public balances;
    address[] public depositors;
    uint256 public total;

    event Deposit(address indexed from, uint256 amount);
    event Withdraw(address indexed to, uint256 amount);

    modifier onlyOwner() {
        require(msg.sender == owner, "not owner");
        _;
    }

    constructor(address token_, uint256 feeBps_) {
        require(feeBps_ <= 10000, "fee");
        owner = msg.sender;
        feeBps = feeBps_;
        token = IERC20(token_);
    }

    function deposit(uint256 amount) external {
        require(amount > 0, "zero");
        require(token.transferFrom(msg.sender, address(this), amount), "transfer failed");
        uint256 net = amount - (amount * feeBps) / 10000;
        if (balances[msg.sender] == 0) {
            depositors.push(msg.sender);
        }
        balances[msg.sender] += net;
        total += net;
        emit Deposit(msg.sender, net);
    }

    function withdraw(uint256 amount) external {
        require(balances[msg.sender] >= amount, "insufficient");
        balances[msg.sender] -= amount;
        total -= amount;
        require(token.transfer(msg.sender, amount), "transfer failed");
        emit Withdraw(msg.sender, amount);
    }

    function sweep(address to) external onlyOwner {
        uint256 held = token.balanceOf(address(this));
        require(held > total, "nothing to sweep");
        require(token.transfer(to, held - total), "transfer failed");
    }

    function dropLast() external onlyOwner {
        depositors.pop();
    }

    function count() external view returns (uint256) {
        return depositors.length;
    }
}
