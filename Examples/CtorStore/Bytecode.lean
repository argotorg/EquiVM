import Examples.CtorStore.Spec
import Ethereum.Semantics
import Reasoning.Initcode
import Reasoning.JumpDest

open Solm Ethereum Ethereum.EVM Reasoning.Theory

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

macro "ctor_store_decode_prefix" : tactic =>
  `(tactic|
    rw [decode_append_left ctorStoreInitcode _ _ (by native_decide)
      (by
        intro b instr hget hinstr
        cases instr <;> rename_i op <;> cases op <;> revert b <;> native_decide)
      (by
        intro b instr hget hinstr
        cases instr <;> rename_i op <;> cases op <;> revert b <;> native_decide)])

theorem ctorStoreDecode0 (tail : ByteArray) :
    decode (ctorStoreInitcode ++ tail) ⟨0⟩ = some (.Push .PUSH1, some (⟨32⟩, 1)) := by
  ctor_store_decode_prefix
  native_decide

theorem ctorStoreDecode2 (tail : ByteArray) :
    decode (ctorStoreInitcode ++ tail) ⟨2⟩ = some (.Push .PUSH1, some (⟨28⟩, 1)) := by
  ctor_store_decode_prefix
  native_decide

theorem ctorStoreDecode4 (tail : ByteArray) :
    decode (ctorStoreInitcode ++ tail) ⟨4⟩ = some (.PUSH0, .none) := by
  ctor_store_decode_prefix
  native_decide

theorem ctorStoreDecode5 (tail : ByteArray) :
    decode (ctorStoreInitcode ++ tail) ⟨5⟩ = some (.CODECOPY, .none) := by
  ctor_store_decode_prefix
  native_decide

theorem ctorStoreDecode6 (tail : ByteArray) :
    decode (ctorStoreInitcode ++ tail) ⟨6⟩ = some (.PUSH0, .none) := by
  ctor_store_decode_prefix
  native_decide

theorem ctorStoreDecode7 (tail : ByteArray) :
    decode (ctorStoreInitcode ++ tail) ⟨7⟩ = some (.MLOAD, .none) := by
  ctor_store_decode_prefix
  native_decide

theorem ctorStoreDecode8 (tail : ByteArray) :
    decode (ctorStoreInitcode ++ tail) ⟨8⟩ = some (.PUSH0, .none) := by
  ctor_store_decode_prefix
  native_decide

theorem ctorStoreDecode9 (tail : ByteArray) :
    decode (ctorStoreInitcode ++ tail) ⟨9⟩ = some (.SSTORE, .none) := by
  ctor_store_decode_prefix
  native_decide

theorem ctorStoreDecode10 (tail : ByteArray) :
    decode (ctorStoreInitcode ++ tail) ⟨10⟩ = some (.Push .PUSH1, some (⟨8⟩, 1)) := by
  ctor_store_decode_prefix
  native_decide

theorem ctorStoreDecode12 (tail : ByteArray) :
    decode (ctorStoreInitcode ++ tail) ⟨12⟩ = some (.Push .PUSH1, some (⟨20⟩, 1)) := by
  ctor_store_decode_prefix
  native_decide

theorem ctorStoreDecode14 (tail : ByteArray) :
    decode (ctorStoreInitcode ++ tail) ⟨14⟩ = some (.PUSH0, .none) := by
  ctor_store_decode_prefix
  native_decide

theorem ctorStoreDecode15 (tail : ByteArray) :
    decode (ctorStoreInitcode ++ tail) ⟨15⟩ = some (.CODECOPY, .none) := by
  ctor_store_decode_prefix
  native_decide

theorem ctorStoreDecode16 (tail : ByteArray) :
    decode (ctorStoreInitcode ++ tail) ⟨16⟩ = some (.Push .PUSH1, some (⟨8⟩, 1)) := by
  ctor_store_decode_prefix
  native_decide

theorem ctorStoreDecode18 (tail : ByteArray) :
    decode (ctorStoreInitcode ++ tail) ⟨18⟩ = some (.PUSH0, .none) := by
  ctor_store_decode_prefix
  native_decide

theorem ctorStoreDecode19 (tail : ByteArray) :
    decode (ctorStoreInitcode ++ tail) ⟨19⟩ = some (.RETURN, .none) := by
  ctor_store_decode_prefix
  native_decide
