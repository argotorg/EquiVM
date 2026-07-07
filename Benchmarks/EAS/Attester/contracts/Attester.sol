// SPDX-License-Identifier: MIT

pragma solidity 0.8.26;

import { IEAS, AttestationRequest, AttestationRequestData, RevocationRequest, RevocationRequestData, MultiAttestationRequest, MultiRevocationRequest } from "@ethereum-attestation-service/eas-contracts/contracts/IEAS.sol";
import { NO_EXPIRATION_TIME, EMPTY_UID } from "@ethereum-attestation-service/eas-contracts/contracts/Common.sol";

/// @title Attester
/// @notice Ethereum Attestation Service - Example
contract Attester {
    error InvalidEAS();
    error InvalidInput();

    // The address of the global EAS contract.
    IEAS private immutable _eas;

    /// @notice Creates a new Attester instance.
    /// @param eas The address of the global EAS contract.
    constructor(IEAS eas) {
        if (address(eas) == address(0)) {
            revert InvalidEAS();
        }

        _eas = eas;
    }

    /// @notice Attests to a schema that receives a uint256 parameter.
    /// @param schema The schema UID to attest to.
    /// @param input The uint256 value to pass to to the resolver.
    /// @return The UID of the new attestation.
    function attest(bytes32 schema, uint256 input) external returns (bytes32) {
        return
            _eas.attest(
                AttestationRequest({
                    schema: schema,
                    data: AttestationRequestData({
                        recipient: address(0), // No recipient
                        expirationTime: NO_EXPIRATION_TIME, // No expiration time
                        revocable: true,
                        refUID: EMPTY_UID, // No referenced UID
                        data: abi.encode(input), // Encode a single uint256 as a parameter to the schema
                        value: 0 // No value/ETH
                    })
                })
            );
    }

    /// @notice Revokes an attestation of a schema that receives a uint256 parameter.
    /// @param schema The schema UID to attest to.
    /// @param uid The UID of the attestation to revoke.
    function revoke(bytes32 schema, bytes32 uid) external {
        _eas.revoke(RevocationRequest({ schema: schema, data: RevocationRequestData({ uid: uid, value: 0 }) }));
    }

    /// @notice Multi-attests to a schemas which receive a uint256 parameter.
    /// @param schemas The schema UIDs to attest to.
    /// @param schemaInputs The uint256 values to pass to to the resolver for each schema.
    /// @return The UIDs of new attestations.
    function multiAttest(
        bytes32[] calldata schemas,
        uint256[][] calldata schemaInputs
    ) external returns (bytes32[] memory) {
        uint256 schemaLength = schemas.length;
        if (schemaLength == 0 || schemaLength != schemaInputs.length) {
            revert InvalidInput();
        }

        MultiAttestationRequest[] memory multiRequests = new MultiAttestationRequest[](schemaLength);

        for (uint256 i = 0; i < schemaLength; ++i) {
            uint256[] calldata inputs = schemaInputs[i];

            uint256 inputLength = inputs.length;
            if (inputLength == 0) {
                revert InvalidInput();
            }

            AttestationRequestData[] memory data = new AttestationRequestData[](inputLength);
            for (uint256 j = 0; j < inputLength; ++j) {
                data[j] = AttestationRequestData({
                    recipient: address(0), // No recipient
                    expirationTime: NO_EXPIRATION_TIME, // No expiration time
                    revocable: true,
                    refUID: EMPTY_UID, // No referenced UID
                    data: abi.encode(inputs[j]), // Encode a single uint256 as a parameter to the schema
                    value: 0 // No value/ETH
                });
            }

            multiRequests[i] = MultiAttestationRequest({ schema: schemas[i], data: data });
        }

        return _eas.multiAttest(multiRequests);
    }

    /// @notice Multi-revokes an attestation of a schema that receives a uint256 parameter.
    /// @param schemas The schema UIDs to attest to.
    /// @param schemaUids The UIDs of the attestations to revoke for each schema.
    function multiRevoke(bytes32[] calldata schemas, bytes32[][] calldata schemaUids) external {
        uint256 schemaLength = schemas.length;
        if (schemaLength == 0 || schemaLength != schemaUids.length) {
            revert InvalidInput();
        }

        MultiRevocationRequest[] memory multiRequests = new MultiRevocationRequest[](schemaLength);

        for (uint256 i = 0; i < schemaLength; ++i) {
            bytes32[] calldata uids = schemaUids[i];

            uint256 uidLength = uids.length;
            if (uidLength == 0) {
                revert InvalidInput();
            }

            RevocationRequestData[] memory data = new RevocationRequestData[](uidLength);
            for (uint256 j = 0; j < uidLength; ++j) {
                data[j] = RevocationRequestData({ uid: uids[j], value: 0 });
            }

            multiRequests[i] = MultiRevocationRequest({ schema: schemas[i], data: data });
        }

        _eas.multiRevoke(multiRequests);
    }
}
