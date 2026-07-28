import Benchmarks.EAS.Attester.Spec
import Solm.Notation

/-!
# EAS Attester spec in the Solidity-faithful Solm frontend

The whole Attester spec written with `solidity%`, parameterized by the immutable valuation
`v : AttesterImmutables`, and proven definitionally equal to the AST spec.

Escapes: the EAS calls (`${easCall …}`/`${checkedEASCallStmts …}` splices — the receiver is the
immutable `easExpr v`, not an identifier) with their binders read back via `${Expr.var …}`, and
`${zeroBytes32}` (the AST models it as a cast, while surface `bytes32(0)` is the fixed-bytes
literal).  The EAS request payloads are surface ABI tuples (`tuple(…)` literals with
`(bytes32, (address, uint64, bool, bytes32, bytes, uint256)[])[]`-typed locals).
-/

open Solm Solm.Notation
open Benchmarks.EAS.Attester Benchmarks.EAS.Attester.Immutables

namespace Benchmarks.EAS.Attester.Syntax

def contractSyntax (v : AttesterImmutables) : ContractDecl := solidity% contract Attester {
  constructor(address eas) {
    require(eas != address(0));
    address imm_eas = eas;
  }

  function attest(bytes32 schema, uint256 input) external returns (bytes32) {
    ${[easCall v "attest" [attestationRequest (.var "schema") (.var "input")] "uid"]}
    return ${Expr.var "uid"};
  }

  function multiAttest(bytes32[] schemas, uint256[][] schemaInputs) external returns (bytes32[]) {
    uint256 schemaLength = schemas.length;
    require(schemaLength != 0 && schemaLength == schemaInputs.length);
    (bytes32, (address, uint64, bool, bytes32, bytes, uint256)[])[] multiRequests =
      new (bytes32, (address, uint64, bool, bytes32, bytes, uint256)[])[](schemaLength);
    uint256 i = 0;
    while (i < schemaLength) {
      uint256[] inputs = schemaInputs[i];
      uint256 inputLength = inputs.length;
      require(inputLength != 0);
      (address, uint64, bool, bytes32, bytes, uint256)[] data =
        new (address, uint64, bool, bytes32, bytes, uint256)[](inputLength);
      uint256 j = 0;
      while (j < inputLength) {
        data[j] = tuple(address(0), 0, true, ${zeroBytes32},
          abi.encodeWithSelector(__abi_encode_uint256, inputs[j])[4 : 36], 0);
        j = (j + 1) as uint256;
      }
      multiRequests[i] = tuple(schemas[i], data);
      i = (i + 1) as uint256;
    }
    ${[easCall v "multiAttest" [.var "multiRequests"] "uids"]}
    return ${Expr.var "uids"};
  }

  function multiRevoke(bytes32[] schemas, bytes32[][] schemaUids) external {
    uint256 schemaLength = schemas.length;
    require(schemaLength != 0 && schemaLength == schemaUids.length);
    (bytes32, (bytes32, uint256)[])[] multiRequests =
      new (bytes32, (bytes32, uint256)[])[](schemaLength);
    uint256 i = 0;
    while (i < schemaLength) {
      bytes32[] uids = schemaUids[i];
      uint256 uidLength = uids.length;
      require(uidLength != 0);
      (bytes32, uint256)[] data = new (bytes32, uint256)[](uidLength);
      uint256 j = 0;
      while (j < uidLength) {
        data[j] = tuple(uids[j], 0);
        j = (j + 1) as uint256;
      }
      multiRequests[i] = tuple(schemas[i], data);
      i = (i + 1) as uint256;
    }
    ${checkedEASCallStmts v "multiRevoke" [.var "multiRequests"] "_multiRevoke"}
  }

  function revoke(bytes32 schema, bytes32 uid) external {
    ${checkedEASCallStmts v "revoke" [revocationRequest (.var "schema") (.var "uid")] "_revoke"}
  }
}

theorem contractSyntax_eq (v : AttesterImmutables) :
    contractSyntax v = Benchmarks.EAS.Attester.contract v := by rfl

end Benchmarks.EAS.Attester.Syntax
