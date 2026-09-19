import Solm.Semantics
import Solm.SolidityLayout

/-!
# Pow — the Solm specification for `Pow.sol`'s `pow2(uint256 n)`

This is the Solm-level spec only (pure data — it compiles on its own; no bytecode yet).  It is the
analogue of `truthContract`/`truthTransition`, and the contract we'll use to work out the loop +
`Reaches`-combinator machinery, since it has a function argument and a `while` over a symbolic `n`.

The transition body mirrors the compiled `Pow.sol`:

* `require(callvalue == 0)` — the spec-level mirror of solc's non-payable guard (the function is
  `public pure`, so the bytecode contains the `CALLVALUE; ISZERO; …; REVERT` prologue).
* `require(n < 256)` — the source-level guard.  It is what makes the spec *faithful* to the
  bytecode: Solm's `evalBinaryOp?` is **unbounded `Int`** (no wrap mod `2^256`), so without this
  guard the `unchecked` `2^n` that wraps in the EVM would disagree with the spec for `n ≥ 256`.
  With it, `2^n < 2^256` throughout, EVM-wrapping and Solm-unbounded arithmetic coincide, and for
  `n ≥ 256` both sides revert.
* the loop: `r = 2^i`, `i` counts up to `n`; local updates are `letDecl` re-binds (the semantics
  is `locals.insert`, which overwrites — Solm has no separate local-assignment statement).
* `return r`.

Loop invariant we'll prove the EVM maintains, coupled to this `while`:
`r = 2^i  ∧  i ≤ n`  (variant `n - i`); at exit (`i = n`): `r = 2^n`.
-/

open Solm ABI

namespace Pow

/-- The ABI/Solm type `uint256`. -/
def uint256 : ABIType := .elem (.int (.uint ⟨256, by decide⟩))

/-- `pow2(uint256 n) → uint256`, returning `2^n` (guarded so `n < 256`). -/
def powTransition : TransitionDecl :=
  { name := "pow2"
    params := [{ name := "n", ty := uint256 }]
    returnType := [uint256]
    body :=
      [ -- non-payable guard (mirrors the compiled `CALLVALUE; ISZERO; …` prologue)
        .require (.binary .eq (.env .callvalue) (.intLit 0)),
        -- source guard: keep 2^n in range (and revert past it, matching the EVM)
        .require (.binary .lt (.var "n") (.intLit 256)),
        -- r := 1 ; i := 0
        .letDecl "r" (some uint256) (.intLit 1),
        .letDecl "i" (some uint256) (.intLit 0),
        -- while (i < n) { r := r * 2 ; i := i + 1 }
        .while (.binary .lt (.var "i") (.var "n"))
          [ .letDecl "r" (some uint256) (.binary .mul (.var "r") (.intLit 2)),
            .letDecl "i" (some uint256) (.binary .add (.var "i") (.intLit 1)) ],
        -- return r
        .return [(.var "r")] ] }

/-- Solm spec of the `Pow` contract: no storage, no constructor body, one transition. -/
def powContract : ContractDecl :=
  { name := "Pow"
    storage := []
    ctor := { params := [], body := [] }
    transitions := [powTransition] }

end Pow

/-- Verification config: empty storage layout, default external-call ABI. -/
def powConfig : Config :=
  { storage := { layout := fun _ _ => none }
    externalABI := defaultExternalCallABI
    selfDeployment := genSolidityConstructorDeployment Pow.powContract.ctor.params }
