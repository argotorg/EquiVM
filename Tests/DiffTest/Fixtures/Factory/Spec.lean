import Solm.Semantics
import Solm.SolidityLayout
import Solm.SolidityStorage
import Solm.MetaSolidityLayout

/-!
# Factory — fixture specification for the differential suite

`Factory.sol` (solc 0.8.35, optimizer on, 200 runs) exercises the Solm statement forms no example
or benchmark reaches: contract creation with and without salt (`new`), `for` with `break` and
`continue`, `try`/`catch` (`checkedCall`), and array `pop`/`delete`.  The `Child` contract's
creation code is embedded verbatim in the factory's runtime; it is also the `creationCode` the
specification hands to `new`.
-/

open Solm ABI Ethereum

namespace Tests.DiffTest.Fixtures.Factory

def addr : ABIType := .elem .address
def uint256Int : IntType := .uint ⟨256, by decide⟩
abbrev uint256 : ABIType := .elem (.int uint256Int)
def bytes32 : ABIType := .elem (.bytes ⟨31, by decide⟩)
def addrSt : StorageType := .elem .address

/-- solc's checked arithmetic: revert outside the `uint256` range. -/
def u256 (e : Expr) : Expr := .inRange uint256Int e
def zeroAddr : Expr := .cast (.intLit 0) addrSt
def childrenRef : StorageRef := { base := "children" }
def totalRef : StorageRef := { base := "total" }
/-- the compiler's non-payable guard -/
def nonPayable : Stmt := .require (.binary .eq (.env .callvalue) (.intLit 0))

/-- `Child`'s creation code (165 bytes; embedded verbatim in `factoryBytecode`). -/
def childCreationBytecode : ByteArray := ⟨#[
    0x60, 0x80, 0x60, 0x40, 0x52, 0x60, 0x40, 0x51, 0x60, 0xa5, 0x38, 0x03, 0x80, 0x60, 0xa5, 0x83,
    0x39, 0x81, 0x01, 0x60, 0x40, 0x81, 0x90, 0x52, 0x60, 0x1e, 0x91, 0x60, 0x24, 0x56, 0x5b, 0x5f,
    0x55, 0x60, 0x3a, 0x56, 0x5b, 0x5f, 0x60, 0x20, 0x82, 0x84, 0x03, 0x12, 0x15, 0x60, 0x33, 0x57,
    0x5f, 0x5f, 0xfd, 0x5b, 0x50, 0x51, 0x91, 0x90, 0x50, 0x56, 0x5b, 0x60, 0x60, 0x80, 0x60, 0x45,
    0x5f, 0x39, 0x5f, 0xf3, 0xfe, 0x60, 0x80, 0x60, 0x40, 0x52, 0x34, 0x80, 0x15, 0x60, 0x0e, 0x57,
    0x5f, 0x5f, 0xfd, 0x5b, 0x50, 0x60, 0x04, 0x36, 0x10, 0x60, 0x30, 0x57, 0x5f, 0x35, 0x60, 0xe0,
    0x1c, 0x80, 0x63, 0x0c, 0x55, 0x69, 0x9c, 0x14, 0x60, 0x34, 0x57, 0x80, 0x63, 0x6d, 0x4c, 0xe6,
    0x3c, 0x14, 0x60, 0x4d, 0x57, 0x5b, 0x5f, 0x5f, 0xfd, 0x5b, 0x60, 0x3b, 0x5f, 0x54, 0x81, 0x56,
    0x5b, 0x60, 0x40, 0x51, 0x90, 0x81, 0x52, 0x60, 0x20, 0x01, 0x60, 0x40, 0x51, 0x80, 0x91, 0x03,
    0x90, 0xf3, 0x5b, 0x5f, 0x54, 0x60, 0x3b, 0x56, 0xfe, 0xa1, 0x64, 0x73, 0x6f, 0x6c, 0x63, 0x43,
    0x00, 0x08, 0x23, 0x00, 0x0a]⟩

/-- `Child`'s deployed code (96 bytes), for a callee that answers `get()`. -/
def childRuntimeBytecode : ByteArray := ⟨#[
    0x60, 0x80, 0x60, 0x40, 0x52, 0x34, 0x80, 0x15, 0x60, 0x0e, 0x57, 0x5f, 0x5f, 0xfd, 0x5b, 0x50,
    0x60, 0x04, 0x36, 0x10, 0x60, 0x30, 0x57, 0x5f, 0x35, 0x60, 0xe0, 0x1c, 0x80, 0x63, 0x0c, 0x55,
    0x69, 0x9c, 0x14, 0x60, 0x34, 0x57, 0x80, 0x63, 0x6d, 0x4c, 0xe6, 0x3c, 0x14, 0x60, 0x4d, 0x57,
    0x5b, 0x5f, 0x5f, 0xfd, 0x5b, 0x60, 0x3b, 0x5f, 0x54, 0x81, 0x56, 0x5b, 0x60, 0x40, 0x51, 0x90,
    0x81, 0x52, 0x60, 0x20, 0x01, 0x60, 0x40, 0x51, 0x80, 0x91, 0x03, 0x90, 0xf3, 0x5b, 0x5f, 0x54,
    0x60, 0x3b, 0x56, 0xfe, 0xa1, 0x64, 0x73, 0x6f, 0x6c, 0x63, 0x43, 0x00, 0x08, 0x23, 0x00, 0x0a]⟩

/-- `keccak("get()")[0:4]`. -/
def getSelector : ByteArray := ⟨#[0x6d, 0x4c, 0xe6, 0x3c]⟩

/-- `Child.get()` takes nothing and returns one `uint256` word. -/
def externalABI : ExternalCallABI where
  encode? := fun name args =>
    if name = "get" then (match args with | [] => some getSelector | _ => none) else none
  decode? := defaultDecodeReturn?

def countTransition : TransitionDecl :=
  { name := "count", params := [], returnType := [uint256],
    body := [nonPayable, .return [.arrayLength .storage childrenRef]] }

def popChildTransition : TransitionDecl :=
  { name := "popChild", params := [], returnType := [],
    body := [nonPayable, .pop childrenRef] }

def totalTransition : TransitionDecl :=
  { name := "total", params := [], returnType := [uint256],
    body := [nonPayable, .return [.storage totalRef]] }

def clearTransition : TransitionDecl :=
  { name := "clear", params := [], returnType := [],
    body := [nonPayable, .delete childrenRef] }

def childrenTransition : TransitionDecl :=
  { name := "children", params := [{ name := "i", ty := uint256 }], returnType := [addr],
    body := [nonPayable, .return [.storage { base := "children", steps := [.aindex (.var "i")] }]] }

/-- `try Child(c).get() returns (uint256 r) { return (true, r); } catch { return (false, 0); }`
    in a `view` function: a static call. -/
def tryGetTransition : TransitionDecl :=
  { name := "tryGet", params := [{ name := "c", ty := addr }], returnType := [.elem .bool, uint256],
    body :=
      [ nonPayable,
        .checkedCall (.var "c") "get" (.intLit 0) [] "r"
          [ .return [.boolLit true, .var "r"] ]
          "err"
          [ .return [.boolLit false, .intLit 0] ]
          (perm := false) ] }

/-- `for (uint i = 0; i < n; i++) { if (i == 4) break; if (seed % 2 == 1 && i == 1) continue;
    Child c = new Child{value: i}(seed + i); children.push(address(c)); total += 1; last = address(c); }` -/
def makeTransition : TransitionDecl :=
  { name := "make", params := [{ name := "n", ty := uint256 }, { name := "seed", ty := uint256 }],
    returnType := [addr],
    body :=
      [ .letDecl "last" (some addr) zeroAddr,
        .for [ .letDecl "i" (some uint256) (.intLit 0) ]
             (.binary .lt (.var "i") (.var "n"))
             [ .assign .localVar { base := "i" } (u256 (.binary .add (.var "i") (.intLit 1))) ]
             [ .ite (.binary .eq (.var "i") (.intLit 4)) [.break] [],
               .ite (.binary .and (.binary .eq (.binary .mod (.var "seed") (.intLit 2)) (.intLit 1))
                                  (.binary .eq (.var "i") (.intLit 1)))
                 [.continue] [],
               .new "Child" (.var "i") [u256 (.binary .add (.var "seed") (.var "i"))] "c",
               .push childrenRef (some (.var "c")),
               .assign .storage totalRef (u256 (.binary .add (.storage totalRef) (.intLit 1))),
               .assign .localVar { base := "last" } (.var "c") ],
        .return [.var "last"] ] }

/-- `Child c = new Child{salt: salt}(v); children.push(address(c)); return address(c);` -/
def make2Transition : TransitionDecl :=
  { name := "make2", params := [{ name := "salt", ty := bytes32 }, { name := "v", ty := uint256 }],
    returnType := [addr],
    body :=
      [ nonPayable,
        .new "Child" (.intLit 0) [.var "v"] "c" (salt := some (.var "salt")),
        .push childrenRef (some (.var "c")),
        .return [.var "c"] ] }

def contract : ContractDecl :=
  { name := "Factory"
    storage := [{ name := "children", ty := .dynamicArray addrSt }, { name := "total", ty := .elem (.int uint256Int) }]
    -- the implicit constructor is non-payable
    ctor := { params := [], body := [nonPayable] }
    transitions := [countTransition, popChildTransition, totalTransition, clearTransition, childrenTransition,
                    tryGetTransition, makeTransition, make2Transition] }

def storageLayout : StorageLayout := solidityLayout! [([] : List StructDecl)] [contract.storage]

def config : Config :=
  { storageBackend := solidityStorageBackend storageLayout
    externalABI := externalABI
    creationCode := fun name args =>
      if name = "Child" then genSolidityConstructorDeployment [{ name := "x_", ty := uint256 }] childCreationBytecode args
      else none
    selfDeployment := genSolidityConstructorDeployment contract.ctor.params }

end Tests.DiffTest.Fixtures.Factory
