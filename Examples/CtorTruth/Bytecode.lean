import Examples.CtorTruth.Spec
import Solm.Dispatch
import Ethereum.Semantics
import Reasoning.Initcode
import Reasoning.JumpDest

open Solm Ethereum Ethereum.EVM Reasoning.Theory

/-! ## Creation and runtime bytecode

Generated with:

```bash
solc --bin --bin-runtime --evm-version shanghai --no-cbor-metadata CtorTruth.sol
```
-/

/-- Pure creation/initcode for `CtorTruth`, without appended constructor ABI arguments. -/
def ctorTruthInitcode : ByteArray :=
  ⟨#[
    0x60, 0x80, 0x60, 0x40, 0x52, 0x60, 0x7b, 0x80, 0x60, 0x0f, 0x5f, 0x39,
    0x5f, 0xf3, 0xfe, 0x60, 0x80, 0x60, 0x40, 0x52, 0x34, 0x80, 0x15, 0x60,
    0x0e, 0x57, 0x5f, 0x5f, 0xfd, 0x5b, 0x50, 0x60, 0x04, 0x36, 0x10, 0x60,
    0x26, 0x57, 0x5f, 0x35, 0x60, 0xe0, 0x1c, 0x80, 0x63, 0x9e, 0x9f, 0x51,
    0xd2, 0x14, 0x60, 0x2a, 0x57, 0x5b, 0x5f, 0x5f, 0xfd, 0x5b, 0x60, 0x30,
    0x60, 0x44, 0x56, 0x5b, 0x60, 0x40, 0x51, 0x60, 0x3b, 0x91, 0x90, 0x60,
    0x64, 0x56, 0x5b, 0x60, 0x40, 0x51, 0x80, 0x91, 0x03, 0x90, 0xf3, 0x5b,
    0x5f, 0x60, 0x01, 0x90, 0x50, 0x90, 0x56, 0x5b, 0x5f, 0x81, 0x15, 0x15,
    0x90, 0x50, 0x91, 0x90, 0x50, 0x56, 0x5b, 0x60, 0x5e, 0x81, 0x60, 0x4c,
    0x56, 0x5b, 0x82, 0x52, 0x50, 0x50, 0x56, 0x5b, 0x5f, 0x60, 0x20, 0x82,
    0x01, 0x90, 0x50, 0x60, 0x75, 0x5f, 0x83, 0x01, 0x84, 0x60, 0x57, 0x56,
    0x5b, 0x92, 0x91, 0x50, 0x50, 0x56
  ]⟩

/-- Deployed runtime bytecode of `CtorTruth`. -/
def ctorTruthRuntimeBytecode : ByteArray :=
  ⟨#[
    0x60, 0x80, 0x60, 0x40, 0x52, 0x34, 0x80, 0x15, 0x60, 0x0e, 0x57, 0x5f,
    0x5f, 0xfd, 0x5b, 0x50, 0x60, 0x04, 0x36, 0x10, 0x60, 0x26, 0x57, 0x5f,
    0x35, 0x60, 0xe0, 0x1c, 0x80, 0x63, 0x9e, 0x9f, 0x51, 0xd2, 0x14, 0x60,
    0x2a, 0x57, 0x5b, 0x5f, 0x5f, 0xfd, 0x5b, 0x60, 0x30, 0x60, 0x44, 0x56,
    0x5b, 0x60, 0x40, 0x51, 0x60, 0x3b, 0x91, 0x90, 0x60, 0x64, 0x56, 0x5b,
    0x60, 0x40, 0x51, 0x80, 0x91, 0x03, 0x90, 0xf3, 0x5b, 0x5f, 0x60, 0x01,
    0x90, 0x50, 0x90, 0x56, 0x5b, 0x5f, 0x81, 0x15, 0x15, 0x90, 0x50, 0x91,
    0x90, 0x50, 0x56, 0x5b, 0x60, 0x5e, 0x81, 0x60, 0x4c, 0x56, 0x5b, 0x82,
    0x52, 0x50, 0x50, 0x56, 0x5b, 0x5f, 0x60, 0x20, 0x82, 0x01, 0x90, 0x50,
    0x60, 0x75, 0x5f, 0x83, 0x01, 0x84, 0x60, 0x57, 0x56, 0x5b, 0x92, 0x91,
    0x50, 0x50, 0x56
  ]⟩

/-- The 4-byte function selector of `truth()` is `0x9e9f51d2`. -/
axiom ctorTruthSelectorBytes :
    (ffi.KEC (String.toByteArray (Solm.transitionSigStr CtorTruth.truthTransition))).extract 0 4
      = ⟨#[0x9e, 0x9f, 0x51, 0xd2]⟩

/-- The `JUMPDEST` positions of `ctorTruthRuntimeBytecode`. -/
@[valid_jumps] theorem ctorTruthRuntimeValidJumps :
    Ethereum.EVM.D_J ctorTruthRuntimeBytecode 0
      = #[⟨14⟩, ⟨38⟩, ⟨42⟩, ⟨48⟩, ⟨59⟩, ⟨68⟩, ⟨76⟩, ⟨87⟩, ⟨94⟩, ⟨100⟩, ⟨117⟩]
  := by native_decide

/-- The `JUMPDEST` positions of `ctorTruthInitcode`. -/
@[valid_jumps] theorem ctorTruthInitcodeValidJumps :
    Ethereum.EVM.D_J ctorTruthInitcode 0
      = #[⟨29⟩, ⟨53⟩, ⟨57⟩, ⟨63⟩, ⟨74⟩, ⟨83⟩, ⟨91⟩, ⟨102⟩, ⟨109⟩,
          ⟨115⟩, ⟨132⟩]
  := by native_decide

macro "ctor_truth_decode_prefix" : tactic =>
  `(tactic|
    rw [decode_append_left ctorTruthInitcode _ _ (by native_decide)
      (by
        intro b instr hget hinstr
        cases instr <;> rename_i op <;> cases op <;> revert b <;> native_decide)
      (by
        intro b instr hget hinstr
        cases instr <;> rename_i op <;> cases op <;> revert b <;> native_decide)])

theorem ctorTruthDecode0_append (tail : ByteArray) :
    decode (ctorTruthInitcode ++ tail) ⟨0⟩ = some (.Push .PUSH1, some (⟨128⟩, 1)) := by
  ctor_truth_decode_prefix
  native_decide

theorem ctorTruthDecode2_append (tail : ByteArray) :
    decode (ctorTruthInitcode ++ tail) ⟨2⟩ = some (.Push .PUSH1, some (⟨64⟩, 1)) := by
  ctor_truth_decode_prefix
  native_decide

theorem ctorTruthDecode4_append (tail : ByteArray) :
    decode (ctorTruthInitcode ++ tail) ⟨4⟩ = some (.MSTORE, .none) := by
  ctor_truth_decode_prefix
  native_decide

theorem ctorTruthDecode5_append (tail : ByteArray) :
    decode (ctorTruthInitcode ++ tail) ⟨5⟩ = some (.Push .PUSH1, some (⟨123⟩, 1)) := by
  ctor_truth_decode_prefix
  native_decide

theorem ctorTruthDecode7_append (tail : ByteArray) :
    decode (ctorTruthInitcode ++ tail) ⟨7⟩ = some (.DUP1, .none) := by
  ctor_truth_decode_prefix
  native_decide

theorem ctorTruthDecode8_append (tail : ByteArray) :
    decode (ctorTruthInitcode ++ tail) ⟨8⟩ = some (.Push .PUSH1, some (⟨15⟩, 1)) := by
  ctor_truth_decode_prefix
  native_decide

theorem ctorTruthDecode10_append (tail : ByteArray) :
    decode (ctorTruthInitcode ++ tail) ⟨10⟩ = some (.PUSH0, .none) := by
  ctor_truth_decode_prefix
  native_decide

theorem ctorTruthDecode11_append (tail : ByteArray) :
    decode (ctorTruthInitcode ++ tail) ⟨11⟩ = some (.CODECOPY, .none) := by
  ctor_truth_decode_prefix
  native_decide

theorem ctorTruthDecode12_append (tail : ByteArray) :
    decode (ctorTruthInitcode ++ tail) ⟨12⟩ = some (.PUSH0, .none) := by
  ctor_truth_decode_prefix
  native_decide

theorem ctorTruthDecode13_append (tail : ByteArray) :
    decode (ctorTruthInitcode ++ tail) ⟨13⟩ = some (.RETURN, .none) := by
  ctor_truth_decode_prefix
  native_decide

theorem ctorTruthDecode0 :
    decode ctorTruthInitcode ⟨0⟩ = some (.Push .PUSH1, some (⟨128⟩, 1)) := by
  simpa [ByteArray.append_empty] using ctorTruthDecode0_append ByteArray.empty

theorem ctorTruthDecode2 :
    decode ctorTruthInitcode ⟨2⟩ = some (.Push .PUSH1, some (⟨64⟩, 1)) := by
  simpa [ByteArray.append_empty] using ctorTruthDecode2_append ByteArray.empty

theorem ctorTruthDecode4 :
    decode ctorTruthInitcode ⟨4⟩ = some (.MSTORE, .none) := by
  simpa [ByteArray.append_empty] using ctorTruthDecode4_append ByteArray.empty

theorem ctorTruthDecode5 :
    decode ctorTruthInitcode ⟨5⟩ = some (.Push .PUSH1, some (⟨123⟩, 1)) := by
  simpa [ByteArray.append_empty] using ctorTruthDecode5_append ByteArray.empty

theorem ctorTruthDecode7 :
    decode ctorTruthInitcode ⟨7⟩ = some (.DUP1, .none) := by
  simpa [ByteArray.append_empty] using ctorTruthDecode7_append ByteArray.empty

theorem ctorTruthDecode8 :
    decode ctorTruthInitcode ⟨8⟩ = some (.Push .PUSH1, some (⟨15⟩, 1)) := by
  simpa [ByteArray.append_empty] using ctorTruthDecode8_append ByteArray.empty

theorem ctorTruthDecode10 :
    decode ctorTruthInitcode ⟨10⟩ = some (.PUSH0, .none) := by
  simpa [ByteArray.append_empty] using ctorTruthDecode10_append ByteArray.empty

theorem ctorTruthDecode11 :
    decode ctorTruthInitcode ⟨11⟩ = some (.CODECOPY, .none) := by
  simpa [ByteArray.append_empty] using ctorTruthDecode11_append ByteArray.empty

theorem ctorTruthDecode12 :
    decode ctorTruthInitcode ⟨12⟩ = some (.PUSH0, .none) := by
  simpa [ByteArray.append_empty] using ctorTruthDecode12_append ByteArray.empty

theorem ctorTruthDecode13 :
    decode ctorTruthInitcode ⟨13⟩ = some (.RETURN, .none) := by
  simpa [ByteArray.append_empty] using ctorTruthDecode13_append ByteArray.empty
