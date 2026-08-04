// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

import {Ripemd160} from "./Ripemd160.sol";

/// @title Ripemd160Deployed
/// @notice Drop-in replacement for the RIPEMD-160 precompile (0x03).
/// @dev Deploy once, then staticcall with raw input bytes.
///      Returns raw 32 bytes (12 zero bytes + 20-byte hash) — identical interface
///      to the native precompile.
contract Ripemd160Deployed {
    fallback() external {
        bytes memory data = msg.data;
        bytes20 digest = Ripemd160.hash(data);
        assembly {
            // Precompile returns 32 bytes: 12 zero bytes + 20-byte digest (right-aligned)
            mstore(0x00, shr(96, digest))
            return(0x00, 0x20)
        }
    }
}
