import Mathlib.Data.Nat.Bitwise
import Examples.Precompiles.Blake2f.Fallback.ModelBridge

/-!
# BLAKE2F fallback output-buffer bridge: core definitions

Definitions and small algebra/readback helpers shared by the output bridge.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Blake2f

set_option maxRecDepth 500000
set_option maxHeartbeats 0

abbrev returnWordBytes (w : UInt256) : ByteArray :=
  (UInt256.toByteArray w).extract 0 8

theorem nat_xor_self_mod (n m : Nat) : Nat.xor n n % m = 0 := by
  rw [show Nat.xor n n = n ^^^ n from rfl, Nat.xor_self]
  simp

theorem nat_zero_xor_mod {n m : Nat} (h : n < m) : Nat.xor 0 n % m = n := by
  rw [show Nat.xor 0 n = 0 ^^^ n from rfl, Nat.zero_xor, Nat.mod_eq_of_lt h]

theorem nat_xor_zero_mod {n m : Nat} (h : n < m) : Nat.xor n 0 % m = n := by
  rw [show Nat.xor n 0 = n ^^^ 0 from rfl, Nat.xor_zero, Nat.mod_eq_of_lt h]

theorem uxor_self (x : UInt256) : UInt256.xor x x = ⟨0⟩ := by
  cases x with
  | mk xv =>
    unfold UInt256.xor Fin.xor
    apply congrArg UInt256.mk
    apply Fin.ext
    exact nat_xor_self_mod xv.val UInt256.size

theorem uxor_zero_left (x : UInt256) : UInt256.xor ⟨0⟩ x = x := by
  cases x with
  | mk xv =>
    unfold UInt256.xor Fin.xor
    apply congrArg UInt256.mk
    apply Fin.ext
    exact nat_zero_xor_mod xv.isLt

theorem uxor_zero_right (x : UInt256) : UInt256.xor x ⟨0⟩ = x := by
  cases x with
  | mk xv =>
    unfold UInt256.xor Fin.xor
    apply congrArg UInt256.mk
    apply Fin.ext
    exact nat_xor_zero_mod xv.isLt

theorem outputWord_xor_cancel (a b mask : UInt256) :
    UInt256.land (UInt256.xor (UInt256.xor a a) b) mask =
      UInt256.land b mask := by
  rw [uxor_self, uxor_zero_left]

abbrev outputReturnWord0 (mem : ByteArray) : UInt256 :=
  UInt256.shiftLeft (evmSwap64 (outputWord0 mem)) ⟨192⟩

abbrev outputReturnWord1 (mem : ByteArray) : UInt256 :=
  UInt256.shiftLeft (evmSwap64 (outputWord1 (outputWordsMem0 mem))) ⟨192⟩

abbrev outputReturnWord2 (mem : ByteArray) : UInt256 :=
  UInt256.shiftLeft (evmSwap64 (outputWord2 (outputWordsMem1 mem))) ⟨192⟩

abbrev outputReturnWord3 (mem : ByteArray) : UInt256 :=
  UInt256.shiftLeft (evmSwap64 (outputWord3 (outputWordsMem2 mem))) ⟨192⟩

abbrev outputReturnWord4 (mem : ByteArray) : UInt256 :=
  UInt256.shiftLeft (evmSwap64 (outputWord4 (outputWordsMem3 mem))) ⟨192⟩

abbrev outputReturnWord5 (mem : ByteArray) : UInt256 :=
  UInt256.shiftLeft (evmSwap64 (outputWord5 (outputWordsMem4 mem))) ⟨192⟩

abbrev outputReturnWord6 (mem : ByteArray) : UInt256 :=
  UInt256.shiftLeft (evmSwap64 (outputWord6 (outputWordsMem5 mem))) ⟨192⟩

abbrev outputReturnWord7 (mem : ByteArray) : UInt256 :=
  UInt256.shiftLeft (evmSwap64 (outputWord7 (outputWordsMem6 mem))) ⟨192⟩

def bytecodeOutputBytes (mem : ByteArray) : ByteArray :=
  returnWordBytes (outputReturnWord0 mem) ++
  returnWordBytes (outputReturnWord1 mem) ++
  returnWordBytes (outputReturnWord2 mem) ++
  returnWordBytes (outputReturnWord3 mem) ++
  returnWordBytes (outputReturnWord4 mem) ++
  returnWordBytes (outputReturnWord5 mem) ++
  returnWordBytes (outputReturnWord6 mem) ++
  returnWordBytes (outputReturnWord7 mem)

theorem fromByteArrayBigEndian_toByteArray_extract0_32 (w : UInt256) :
    fromByteArrayBigEndian ((UInt256.toByteArray w).extract 0 32) = w.toNat := by
  rw [toByteArray_extract_all, fromByteArrayBigEndian_toByteArray]

theorem toByteArray_write_read_self_extract32
    (w : UInt256) (mem : ByteArray) (off : Nat)
    (hgap : off - mem.size < USize.size) :
    ((UInt256.toByteArray w).write 0 mem off 32).readWithPadding off 32 =
      (UInt256.toByteArray w).extract 0 32 := by
  change ((UInt256.toByteArray w).write 0 mem off 32).readWithPadding
      (off + 0) 32 =
    (UInt256.toByteArray w).extract 0 (0 + 32)
  exact toByteArray_write_read_window_of_gap w mem off 0 32
    (by decide) (by decide) (by decide) hgap

theorem outputWordsMem0_size {mem : ByteArray} (hmem : mem.size = 1984) :
    (outputWordsMem0 mem).size = 1984 := by
  unfold outputWordsMem0
  exact outputWord0Mem_size hmem

theorem outputWordsMem1_size {mem : ByteArray} (hmem : mem.size = 1984) :
    (outputWordsMem1 mem).size = 1984 := by
  unfold outputWordsMem1
  exact outputWord1Mem_size (outputWordsMem0_size hmem)

theorem outputWordsMem2_size {mem : ByteArray} (hmem : mem.size = 1984) :
    (outputWordsMem2 mem).size = 1984 := by
  unfold outputWordsMem2
  exact outputWord2Mem_size (outputWordsMem1_size hmem)

theorem outputWordsMem3_size {mem : ByteArray} (hmem : mem.size = 1984) :
    (outputWordsMem3 mem).size = 1984 := by
  unfold outputWordsMem3
  exact outputWord3Mem_size (outputWordsMem2_size hmem)

theorem outputWordsMem4_size {mem : ByteArray} (hmem : mem.size = 1984) :
    (outputWordsMem4 mem).size = 1984 := by
  unfold outputWordsMem4
  exact outputWord4Mem_size (outputWordsMem3_size hmem)

theorem outputWordsMem5_size {mem : ByteArray} (hmem : mem.size = 1984) :
    (outputWordsMem5 mem).size = 1984 := by
  unfold outputWordsMem5
  exact outputWord5Mem_size (outputWordsMem4_size hmem)

theorem outputWordsMem6_size {mem : ByteArray} (hmem : mem.size = 1984) :
    (outputWordsMem6 mem).size = 1984 := by
  unfold outputWordsMem6
  exact outputWord6Mem_size (outputWordsMem5_size hmem)

theorem outputWordsMem7_size {mem : ByteArray} (hmem : mem.size = 1984) :
    (outputWordsMem7 mem).size = 1984 := by
  unfold outputWordsMem7
  exact outputWord7Mem_size (outputWordsMem6_size hmem)

theorem outputWordsMem_size {mem : ByteArray} (hmem : mem.size = 1984) :
    (outputWordsMem mem).size = 1984 := by
  unfold outputWordsMem
  exact outputWordsMem7_size hmem

end Blake2f
