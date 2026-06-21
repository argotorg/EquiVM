import Solm.Semantics
import Solm.SolidityLayout
import Examples.Pow.Spec

/-!
# Caller — Solm specification for `Caller.sol`'s `run(address t, uint256 n)`

`run` makes an **external call** to a `Pow` contract's `pow2(n)` and caches the result in a
single `uint256` storage slot (`stored`, slot 0).  This is the Solm-level spec only (pure data).

Two pieces are example-specific configuration (the default ABI / empty layout used by `Pow`/`Truth`
do not suffice here):

* `callerExternalABI` — the calldata the `Caller` bytecode builds for the sub-call is the 4-byte
  selector of `pow2(uint256)` followed by the 32-byte big-endian argument; the return value is a
  single `uint256` word.  `encode?`/`decode?` mirror exactly that.
* `callerStorageLayout` — `stored` lives whole-slot at slot 0 (`offset 0`, `size 32`).
-/

open Solm ABI Ethereum

namespace Caller

/-- The ABI/Solm type `address`. -/
def addr : ABIType := .elem .address

/-- The ABI/Solm type `uint256`. -/
abbrev uint256 : ABIType := .elem (.int (.uint ⟨256, by decide⟩))

/-- `keccak("pow2(uint256)")[0:4]` — the selector of the callee function. -/
def pow2Selector : ByteArray := ⟨#[0x44, 0x2b, 0x7f, 0xfb]⟩

/-- External-call ABI for `Caller`: `pow2(n)`'s calldata is `selector ++ word(n)`, and its return
    bytes decode (big-endian) to a single `uint256`. -/
def callerExternalABI : ExternalCallABI where
  encode? := fun name args =>
    if name = "pow2" then
      match args with
      | [.int n] => some (pow2Selector ++ Ethereum.UInt256.toByteArray (EVM.wordOfInt n))
      | _ => none
    else none
  decode? := defaultDecodeReturn?

/-- Storage layout: `stored` occupies the whole of slot 0. -/
def callerStorageLayout : StorageLayout where
  layout := fun ref _ =>
    if ref.base = "stored" ∧ ref.steps = [] then
      some { slot := ⟨0⟩, offset := 0, size := 32, hbound := by decide,
             bitOffset := .none,
             type := .int (.uint ⟨256, by decide⟩) }
    else none

/-- The single transition `run(address t, uint256 n)`:
    * `require(callvalue == 0)` — the compiler-inserted non-payable guard;
    * `tmp := t.pow2(n)` — the external call (`eth = 0`), result bound to local `tmp`;
    * `stored := tmp` — cache the result into storage slot 0.
    Returns nothing (void). -/
def runTransition : TransitionDecl :=
  { name := "run"
    params := [{ name := "t", ty := addr }, { name := "n", ty := uint256 }]
    returnType := none
    body :=
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
        .externalCall (.var "t") "pow2" (.intLit 0) [.var "n"] "tmp",
        .assign .storage { base := "stored" } (.var "tmp") ] }

/-- Solm spec of the `Caller` contract: one `uint256` storage field, no constructor body,
    a single transition. -/
def callerContract : ContractDecl :=
  { name := "Caller"
    storage := [{ name := "stored", ty := .elem (.int (.uint ⟨256, by decide⟩)) }]
    ctor := { params := [], body := [] }
    transitions := [runTransition] }

end Caller

/-- Verification config: `stored` at slot 0, and the `pow2` external-call ABI. -/
def callerConfig : Config :=
  { storage := Caller.callerStorageLayout
    externalABI := Caller.callerExternalABI
    selfDeployment := genSolidityConstructorDeployment Caller.callerContract.ctor.params }
