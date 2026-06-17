import Examples.CtorStore.Spec
import Ethereum.Semantics
import Reasoning.JumpDest

open Solm Ethereum Ethereum.EVM

/-! ## Creation and runtime bytecode

This example uses intentionally minimal straight-line creation bytecode rather than solc's full ABI
decoder.  The pure initcode copies the one appended ABI word, stores it in slot 0, copies the runtime
from its embedded suffix, and returns it.
-/

/-- Pure creation/initcode for `CtorStore`, without appended constructor ABI arguments. -/
def ctorStoreInitcode : ByteArray :=
  ⟨#[
    0x60, 0x20, 0x60, 0x1c, 0x5f, 0x39, 0x5f, 0x51, 0x5f, 0x55, 0x60, 0x08,
    0x60, 0x14, 0x5f, 0x39, 0x60, 0x08, 0x5f, 0xf3, 0x60, 0x80, 0x60, 0x40,
    0x52, 0x5f, 0x5f, 0xfd
  ]⟩

/-- Deployed runtime bytecode of `CtorStore`. -/
def ctorStoreRuntimeBytecode : ByteArray :=
  ⟨#[0x60, 0x80, 0x60, 0x40, 0x52, 0x5f, 0x5f, 0xfd]⟩

/-- The `JUMPDEST` positions of `ctorStoreRuntimeBytecode`. -/
@[valid_jumps] theorem ctorStoreRuntimeValidJumps :
    Ethereum.EVM.D_J ctorStoreRuntimeBytecode 0 = #[]
  := by native_decide

/-- The `JUMPDEST` positions of the pure `ctorStoreInitcode`. -/
@[valid_jumps] theorem ctorStoreInitcodeValidJumps :
    Ethereum.EVM.D_J ctorStoreInitcode 0 = #[]
  := by native_decide
