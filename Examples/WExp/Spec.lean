import Stele.Semantics
import Stele.SolidityLayout
import Stele.SolidityStorage
import Stele.MetaSolidityLayout

/-!
# WExp — the Stele specification for midnight's `TickLib.wExp`

Mirrors `src/libraries/TickLib.sol` (morpho midnight) as exposed by a `TickLibWrapper`-style
contract: an internal `wExp` function plus an external `wExp` transition that delegates to it.

```solidity
function wExp(int256 x) internal pure returns (uint256) {
    unchecked {
        if (x < 0) {
            return 1e36 / wExp(-x);
        } else {
            int256 ln2 = 0.693147180559945309e18;
            int256 offset = 0.32261121498945987e18;
            int256 q = (x + offset) / ln2;
            int256 r = x - q * ln2;
            int256 secondTerm = r * r / (2 * 1e18);
            int256 thirdTerm = secondTerm * r / (3 * 1e18);
            int256 expR = 1e18 + r + secondTerm + thirdTerm;
            return uint256(expR) << uint256(q);
        }
    }
}
```

Semantics notes:

* Stele arithmetic is unbounded `Int`. `.sdiv` is `Int.tdiv` (truncation toward zero), matching
  Solidity `/` on `int256`; `.div` is `Int.ediv`, which agrees with `uint256` division on
  non-negative operands (`1e36 / wExp(-x)`).
* `.shl` normalizes into the declared width (`uint256`), so the spec's `<<` faithfully wraps
  mod `2^256` exactly like the EVM. On the input range used by `tickToPrice` the result is
  `< 2^256`, so wrap never triggers.
* The `unchecked` source block performs no range checks; the spec likewise uses bare `.binary`
  arithmetic (no `as intN` narrowing) — faithful wherever the bytecode does not wrap.
-/

open Stele ABI

namespace WExp

def int256 : ABIType := .elem (.int (.sint ⟨256, by decide⟩))
def uint256 : ABIType := .elem (.int (.uint ⟨256, by decide⟩))
def uint256St : StorageType := .elem (.int (.uint ⟨256, by decide⟩))
def int256St : StorageType := .elem (.int (.sint ⟨256, by decide⟩))

/-- The `x < 0` branch: `__pos := wExp(-x); return 1e36 / __pos`. -/
def wExpThenBody : List Stmt :=
  [ .internalCall "wExp" [.unary .neg (.var "x")] "__pos",
    .return [.binary .div (.intLit 1000000000000000000000000000000000000) (.var "__pos")] ]

/-- The `x ≥ 0` branch: the Taylor-polynomial computation and `<<` shift. -/
def wExpElseBody : List Stmt :=
  [ -- q = (x + offset) / ln2
            .letDecl "q" (some int256)
              (.binary .sdiv (.binary .add (.var "x") (.intLit 322611214989459870))
                (.intLit 693147180559945309)),
            -- r = x - q * ln2
            .letDecl "r" (some int256)
              (.binary .sub (.var "x")
                (.binary .mul (.var "q") (.intLit 693147180559945309))),
            -- secondTerm = r * r / (2 * 1e18)
            .letDecl "secondTerm" (some int256)
              (.binary .sdiv (.binary .mul (.var "r") (.var "r"))
                (.intLit 2000000000000000000)),
            -- thirdTerm = secondTerm * r / (3 * 1e18)
            .letDecl "thirdTerm" (some int256)
              (.binary .sdiv (.binary .mul (.var "secondTerm") (.var "r"))
                (.intLit 3000000000000000000)),
            -- expR = 1e18 + r + secondTerm + thirdTerm
            .letDecl "expR" (some int256)
              (.binary .add
                (.binary .add (.binary .add (.intLit 1000000000000000000) (.var "r"))
                  (.var "secondTerm"))
                (.var "thirdTerm")),
            -- return uint256(expR) << uint256(q)
            .return
              [ .binary (.shl (.uint ⟨256, by decide⟩))
                  (.cast (.var "expR") uint256) (.cast (.var "q") uint256) ] ]

def wExpCond : Expr := .binary .lt (.var "x") (.intLit 0)

/-- `TickLib.wExp`, including the recursive internal call in the `x < 0` branch. -/
def wExpFunction : FunctionDecl :=
  { name := "wExp"
    params := [{ name := "x", ty := int256St }]
    returnType := [uint256St]
    body := [ .ite wExpCond wExpThenBody wExpElseBody ] }

/-- `TickLibWrapper.wExp`: delegates to the internal `wExp`. -/
def wExpExternal : TransitionDecl :=
  { name := "wExp"
    params := [{ name := "x", ty := int256 }]
    returnType := [uint256]
    body :=
      [ .internalCall "wExp" [.var "x"] "__w",
        .return [.var "__w"] ] }

/-- The wrapper contract: no storage, no constructor body. -/
def wexpContract : ContractDecl :=
  { name := "TickLibWrapper"
    storage := []
    ctor := { params := [], body := [] }
    functions := [wExpFunction]
    transitions := [wExpExternal] }

end WExp

/-- Verification config: empty storage backend, default external-call ABI. -/
def wexpConfig : Config :=
  { storageBackend := solidityStorage! [([] : List StructDecl)] [WExp.wexpContract.storage]
    externalABI := defaultExternalCallABI
    selfDeployment := genSolidityConstructorDeployment WExp.wexpContract.ctor.params }
