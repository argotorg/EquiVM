// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

import {Blake2f} from "./Blake2f.sol";

/// @title Blake2fDeployed
/// @notice Drop-in replacement for the BLAKE2b F compression precompile (0x09).
/// @dev Deploy once, then staticcall with raw 213-byte EIP-152 input.
///      Returns raw 64 bytes — identical interface to the native precompile.
contract Blake2fDeployed {
    fallback() external {
        bytes memory input = msg.data;
        bytes memory output = Blake2f.compress(input);
        assembly {
            return(add(output, 0x20), mload(output))
        }
    }
}
