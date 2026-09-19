// SPDX-License-Identifier: MIT
pragma solidity 0.8.35;

contract TinyImmutable {
    address public immutable owner;
    uint256 public immutable scale;

    constructor(address _owner, uint256 _scale, bool useScale) {
        owner = _owner;
        if (useScale) {
            scale = _scale;
        }
    }

    function quote(uint256 amount) external view returns (uint256) {
        require(msg.sender == owner, "owner");
        unchecked {
            return amount * scale;
        }
    }
}
