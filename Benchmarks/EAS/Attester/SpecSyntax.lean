import Solm.Notation

/-!
# EAS Attester surface specification

Source: eas-contracts-example d2864b166a08f9b3f9314f8b302316d67f227462, solc 0.8.26,
optimizer runs 1,000,000, Paris, legacy pipeline. This file is the authoritative contract body.

EAS request structs are ABI tuples in their Solidity field order. The ABI hook
`__abi_encode_uint256` followed by `[4 : 36]` implements the source's `abi.encode(input)`.
The local `eas` aliases the immutable receiver so typed calls use ordinary surface syntax.
No-return calls explicitly check code size, as required by this compiler's bytecode.
`multiAttest` exposes the raw call result to retain the compiler's allocation-overflow guard.
Its free-memory pointer before CALL is `160 + 192 * schemas.length + 480 * totalInputs`;
the return copy rounds its byte length up to 32 before allocating the decoded UID array.
Revert payloads are outside `contractRefinement`; all success/failure conditions remain present.
-/

open Solm Solm.Notation

namespace Benchmarks.EAS.Attester.Syntax

def contractSyntax : ContractDecl := solidity% contract Attester {
  address immutable _eas;

  constructor(address eas) {
    require(eas != address(0));
    _eas = eas;
  }

  function attest(bytes32 schema, uint256 input) external returns (bytes32) {
    address eas = _eas;
    bytes encodedCall = abi.encodeWithSelector(__abi_encode_uint256, input);
    bytes encodedInput = encodedCall[4 : 36];
    bytes32 uid = eas.attest(tuple(schema,
      tuple(address(0), 0, true, bytes32(0), encodedInput, 0)));
    return uid;
  }

  function multiAttest(bytes32[] calldata schemas, uint256[][] calldata schemaInputs)
      external returns (bytes32[]) {
    uint256 schemaLength = schemas.length;
    require(schemaLength != 0 && schemaLength == schemaInputs.length);
    (bytes32, (address, uint64, bool, bytes32, bytes, uint256)[])[] multiRequests =
      new (bytes32, (address, uint64, bool, bytes32, bytes, uint256)[])[](schemaLength);
    uint256 allocationEnd = 160 + 192 * schemaLength;
    for (uint256 i = 0; i < schemaLength; i = (i + 1) as uint256) {
      uint256[] calldata inputs = schemaInputs[i];
      uint256 inputLength = inputs.length;
      require(inputLength != 0);
      allocationEnd = allocationEnd + 480 * inputLength;
      (address, uint64, bool, bytes32, bytes, uint256)[] data =
        new (address, uint64, bool, bytes32, bytes, uint256)[](inputLength);
      for (uint256 j = 0; j < inputLength; j = (j + 1) as uint256) {
        bytes encodedCall = abi.encodeWithSelector(__abi_encode_uint256, inputs[j]);
        data[j] = tuple(address(0), 0, true, bytes32(0),
          encodedCall[4 : 36], 0);
      }
      multiRequests[i] = tuple(schemas[i], data);
    }
    address eas = _eas;
    bytes encodedRequest = abi.encodeWithSelector(multiAttest, multiRequests);
    (bool ok, bytes rawReturn) = eas.call(encodedRequest);
    require(ok);
    bytes32[] uids = ${Expr.abiDecode (.dynamicArray (.elem (.bytes ⟨31, by decide⟩)))
      (.var "rawReturn")};
    require(allocationEnd + 32 * ((rawReturn.length + 31) / 32) + 32 * (uids.length + 1)
      <= 18446744073709551615);
    return uids;
  }

  function multiRevoke(bytes32[] calldata schemas, bytes32[][] calldata schemaUids) external {
    uint256 schemaLength = schemas.length;
    require(schemaLength != 0 && schemaLength == schemaUids.length);
    (bytes32, (bytes32, uint256)[])[] multiRequests =
      new (bytes32, (bytes32, uint256)[])[](schemaLength);
    for (uint256 i = 0; i < schemaLength; i = (i + 1) as uint256) {
      bytes32[] calldata uids = schemaUids[i];
      uint256 uidLength = uids.length;
      require(uidLength != 0);
      (bytes32, uint256)[] data = new (bytes32, uint256)[](uidLength);
      for (uint256 j = 0; j < uidLength; j = (j + 1) as uint256) {
        data[j] = tuple(uids[j], 0);
      }
      multiRequests[i] = tuple(schemas[i], data);
    }
    address eas = _eas;
    require(eas.code.length > 0);
    var _multiRevoke = eas.multiRevoke(multiRequests);
  }

  function revoke(bytes32 schema, bytes32 uid) external {
    address eas = _eas;
    require(eas.code.length > 0);
    var _revoke = eas.revoke(tuple(schema, tuple(uid, 0)));
  }
}

end Benchmarks.EAS.Attester.Syntax
