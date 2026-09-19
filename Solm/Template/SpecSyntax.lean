import Solm.Notation

/-!
# Xxx surface spec (TEMPLATE)

The contract in `solidity%` surface syntax (surface language:
`Solm/Notation.lean` header). `Spec.lean` references `contractSyntax` and
derives everything else (named handles, layout, `Config`); the proof files never
look at this file directly.

Conventions: transitions in selector (dispatch) order; the non-payable guard is
implicit (mark `payable` only where the compiled body has no callvalue check);
bind call results explicitly; guillemet-escape Lean-keyword identifiers («from»,
«to», «end»); escapes `${e}`/`${stmts}`/`#c` only for immutable reads,
Expr-valued call receivers, and Lean constants.

Parameterized contracts (immutables): author `Immutables.lean` first, then `def
contractSyntax (v : XxxImmutables) : ContractDecl := solidity% contract Xxx { …
}`.

Alternative: hand-write the AST in `Spec.lean` instead, make this file `import
Benchmarks.Xxx.Spec`, and end it with `theorem contractSyntax_eq :
contractSyntax = Benchmarks.Xxx.contract := by rfl`. Either way exactly *one* of
the two files carries the spec content. The existing contracts provide both the
surface syntax in`SpecSyntax.lean`and the AST in `Spec.lean` (with a proof of
correspondence), but there is no reason for the user to provide both.

-/

open Solm Solm.Notation

namespace Benchmarks.Xxx.Syntax

def contractSyntax : ContractDecl := solidity% contract Xxx {
  mapping(address => uint256) wards;
  uint256 value;

  constructor() {
    wards[msg.sender] = 1;
  }

  function setValue(uint256 data) external {
    require(wards[msg.sender] == 1);
    value = data;
  }

  function value() external returns (uint256) {
    return value;
  }
}

end Benchmarks.Xxx.Syntax
