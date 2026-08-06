// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

import {Blake2f} from "./Blake2f.sol";

/// @title Blake2fDeployed
/// @notice Drop-in replacement for the BLAKE2b F compression precompile (0x09).
/// @dev Deploy once, then staticcall with raw 213-byte EIP-152 input.
///      Returns raw 64 bytes — identical interface to the native precompile.
///
/// Proof source note:
/// The fallback performs the EIP-152 length/final-flag validation directly on calldata before
/// materializing `msg.data` as `bytes memory`.  Without this guard, very large invalid calldata can
/// hit compiler-generated allocator panic `REVERT` before the library check.  `REVERT` is visible
/// at Θ through leftover gas, while the native precompile failure branch is modeled as a collapsed
/// exceptional bytecode result.  The explicit `invalid()` guards keep invalid precompile inputs on
/// the intended exceptional path.  Do not replace these guards with revert strings: revert payloads
/// and unused gas would become part of the caller-visible behavior being proved.
contract Blake2fDeployed {
    fallback() external {
        assembly {
            if iszero(eq(calldatasize(), 213)) {
                invalid()
            }

            let finalFlag := byte(0, calldataload(212))
            if gt(finalFlag, 1) {
                invalid()
            }
        }

        bytes memory input = msg.data;
        bytes memory output = Blake2f.compress(input);
        assembly {
            return(add(output, 0x20), mload(output))
        }
    }
}
