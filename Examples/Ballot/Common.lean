import Examples.Ballot.Bytecode
import Reasoning.ABI
import Reasoning.Dispatch
import Reasoning.Memory
import Reasoning.Solc
import Reasoning.Storage
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Nat.Digits.Lemmas

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace Ballot

/-! ## Ballot-wide storage and ABI helpers -/

theorem ballotNat_lor_packed_address (a q : Nat) (ha : a < 2 ^ 160) :
    Nat.lor 1 (Nat.lor (a * 2 ^ 8) (q * 2 ^ 168)) =
      1 + a * 2 ^ 8 + q * 2 ^ 168 :=
  nat_lor_packed_bool_address_high a q ha

theorem ballotHigh168Mask_toNat (old : UInt256) :
    (UInt256.land (UInt256.ofNat (2 ^ 256 - 2 ^ 168)) old).toNat =
      (old.toNat / 2 ^ 168) * 2 ^ 168 :=
  u256_land_high_mask_toNat old 168 (by norm_num)

theorem ballotPackedAddressAfterBoolTrueWord_eq (old val : UInt256)
    (hcanon : val.toNat < EVM.addressModulus) :
    UInt256.lor ⟨1⟩
      (UInt256.lor
        (UInt256.mul (UInt256.land val solcAddrMask) ⟨256⟩)
        (UInt256.land
              (UInt256.lnot (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨168⟩) ⟨1⟩))
              old)) =
      UInt256.ofNat (1 + val.toNat * 2 ^ 8 + (old.toNat / 2 ^ 168) * 2 ^ 168) :=
  packedAddressAfterBoolTrueWord_eq old val hcanon

/-- Loading a Solidity `address` stored at byte offset 0 returns the low-160-bit address word. -/
theorem ballotStorageLocLoad_address_offset0 (evm : EVM.State) (slot : UInt256) :
    storageLocLoad evm
        { slot := slot, offset := 0, size := 20, hbound := by decide, type := .address }
      = .address (AccountAddress.ofNat
          (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)
            solcAddrMask).toNat) := by
  simpa [addressOffset0Loc] using storageLocLoad_address_offset0 evm slot

/-- Loading a full-slot Solidity `uint256` returns the source-level integer for that word. -/
theorem ballotStorageLocLoad_uint256 (evm : EVM.State) (slot : UInt256) :
    storageLocLoad evm (wordLoc slot)
      = .int (Int.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot).toNat) := by
  simpa [wordLoc, uint256Loc] using storageLocLoad_uint256 evm slot

/-- Loading a full-slot Solidity `bytes32` returns the big-endian fixed-bytes value. -/
theorem ballotStorageLocLoad_bytes32 (evm : EVM.State) (slot : UInt256) :
    storageLocLoad evm
        { slot := slot, offset := 0, size := 32, hbound := by decide,
          type := .bytes ⟨31, by decide⟩ }
      = .fixedBytes ⟨31, by decide⟩
          (EVM.Word.toBytesBE (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)) := by
  simpa [Reasoning.Theory.bytes32Loc] using storageLocLoad_bytes32 evm slot

/-- ABI-encoding a `Proposal` getter return list is exactly `name || voteCount`. -/
theorem ballotProposalReturnEncoding (name count : UInt256) :
    encodeReturnValues? [bytes32, uint256]
      [.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE name),
        .int (Int.ofNat count.toNat)] =
      some (UInt256.toByteArray name ++ UInt256.toByteArray count) := by
  have hnameLen : (EVM.Word.toBytesBE name).length = 32 := by
    simpa using word_toBytesBE_toByteArray_size name
  have hword : EVM.word count.toNat = count := u256_ofNat_toNat count
  have hlt : count.toNat < EVM.twoPow 256 := by
    change count.val.val < EVM.twoPow 256
    exact count.val.isLt
  have hencName :
      encodeABIValue? bytes32 (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE name)) =
        some (EVM.Word.toBytesBE name) := by
    simp only [bytes32, encodeABIValue?, hnameLen, zeroBytes]
    simp
  have hencCount :
      encodeABIValue? uint256 (.int (Int.ofNat count.toNat)) =
        some (EVM.Word.toBytesBE count) := by
    simp [uint256, uint256Int, encodeABIValue?, encodeABIWord?, hword, hlt]
  have hhead : abiTupleHeadSize? [bytes32, uint256] = some 64 := by native_decide
  have hdynBytes : isDynamicABIType bytes32 = false := by native_decide
  have hdynUint : isDynamicABIType uint256 = false := by native_decide
  rw [toByteArray_eq_toBytesBE name, toByteArray_eq_toBytesBE count]
  simp only [encodeReturnValues?, encodeABIValues?, encodeABIValuesFrom?,
    hhead, hencName, hencCount, hdynBytes, hdynUint, bind, Option.bind, Bool.false_eq_true, if_false,
    List.nil_append, List.append_nil]
  apply congrArg some
  apply ByteArray.ext
  apply Array.toList_inj.mp
  simp

theorem ballotStorageLoad_storageStore_self_nonzero (evm : EVM.State) (a : AccountAddress)
    (slot val : UInt256) {acc : Account} (hacc : evm.lookupAccount a = some acc)
    (_hval : (val == default) = false) :
    Solm.EVM.storageLoad (Solm.EVM.storageStore evm a slot val) a slot = val :=
  storageLoad_storageStore_same_present evm a (by simpa [State.lookupAccount] using hacc) slot val

/-- The shared solc return wrapper computes the fixed one-word return length. -/
abbrev ballotRetEnd : UInt256 := (⟨32⟩ : UInt256) + ⟨128⟩

theorem ballotSubRet32_toNat :
    (UInt256.sub ballotRetEnd ⟨128⟩).toNat = 32 := by
  decide

/-- The standard Solidity panic selector word. -/
def ballotPanicSelector : UInt256 :=
  UInt256.shiftLeft (⟨0x4e487b71⟩ : UInt256) ⟨224⟩

noncomputable def ballotPanicMem0 (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray ballotPanicSelector).write 0 mem 0 32

noncomputable def ballotPanicMem (panicCode : UInt256) (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray panicCode).write 0 (ballotPanicMem0 mem) 4 32

end Ballot

namespace Reasoning.Reach

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory

/-! ## Ballot-local return routines -/

/-- Ballot's Solidity `Panic(0x32)` array-bounds block at pc 1815. -/
theorem RD.ballotPanic32Revert1815 {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {R : List UInt256} {mem : ByteArray} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD ballotBytecode ee g s0 ⟨1815⟩ R mem (UInt256.ofNat 3) rdata acc k C)
    (hov : R.length + 2 ≤ 1024) :
    RDrev ballotBytecode g s0 := by
  have hsel :
      UInt256.shiftLeft (⟨0x4e487b71⟩ : UInt256) ⟨224⟩ = Ballot.ballotPanicSelector := by
    rfl
  have rd1824₀ := evm_run h with [
    jumpdest, push4 ⟨0x4e487b71⟩, push1 ⟨224⟩, shl, push0 ]
  have rd1824 := rd1824₀
  rw [hsel] at rd1824
  have rd1828 := evm_run rd1824 with [
    raw mstore 0 (Ballot.ballotPanicMem0 mem) (UInt256.ofNat 3)
      (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨0x32⟩, push1 ⟨4⟩ ]
  have rd1834 := evm_run rd1828 with [
    raw mstore 0 (Ballot.ballotPanicMem ⟨0x32⟩ mem) (UInt256.ofNat 3)
      (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨0x24⟩, push0 ]
  exact rd1834.rev 0 (by decide) mem_cost (by evm_ov)

/-- Ballot's Solidity `Panic(0x11)` checked-arithmetic block at pc 1847. -/
theorem RD.ballotPanic11Revert1847 {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {R : List UInt256} {mem : ByteArray} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD ballotBytecode ee g s0 ⟨1847⟩ R mem (UInt256.ofNat 3) rdata acc k C)
    (hov : R.length + 2 ≤ 1024) :
    RDrev ballotBytecode g s0 := by
  have hsel :
      UInt256.shiftLeft (⟨0x4e487b71⟩ : UInt256) ⟨224⟩ = Ballot.ballotPanicSelector := by
    rfl
  have rd1855₀ := evm_run h with [
    push4 ⟨0x4e487b71⟩, push1 ⟨224⟩, shl, push0 ]
  have rd1855 := rd1855₀
  rw [hsel] at rd1855
  have rd1859 := evm_run rd1855 with [
    raw mstore 0 (Ballot.ballotPanicMem0 mem) (UInt256.ofNat 3)
      (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨0x11⟩, push1 ⟨4⟩ ]
  have rd1865 := evm_run rd1859 with [
    raw mstore 0 (Ballot.ballotPanicMem ⟨0x11⟩ mem) (UInt256.ofNat 3)
      (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨0x24⟩, push0 ]
  exact rd1865.rev 0 (by decide) mem_cost (by evm_ov)

/-- Ballot's shared solc ABI encoder for one `address` word at pc 221. -/
theorem RD.ballotRoutineEncodeAddress {g : Sat256} {s0 : State} {ee : ExecutionEnv} {k C : ℕ}
    {val ret : UInt256} {R : List UInt256}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD ballotBytecode ee g s0 ⟨221⟩ (val :: ret :: R)
        solcFreePtrMem (UInt256.ofNat 3) rdata acc k C)
    (hov : R.length + 8 ≤ 1024) :
    ∃ k' C', RD ballotBytecode ee g s0 ⟨194⟩ (Ballot.ballotRetEnd :: ret :: R)
      (solcReturnMem (UInt256.land val solcAddrMask)) (UInt256.ofNat 5) rdata acc k' C' := by
  let rd := evm_run h with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide)
      mem_cost
      solcFreePtrMem_mload64
      (by decide) (by evm_ov),
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub,
    swap1, swap2, and, dup2,
    raw mstore 6 (solcReturnMem (UInt256.land val solcAddrMask)) (UInt256.ofNat 5)
      (by decide) mem_cost
      (by
        rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
          solcAddrMask from by decide]
        rfl)
      (by decide) (by evm_ov),
    push1 ⟨32⟩, add, push2 ⟨194⟩, jump (by jump_dest)]
  exact ⟨_, _, by simpa using rd⟩

/-- Ballot's shared one-word return tail at pc 194. -/
theorem RD.ballotReturnOneWord194 {g : Sat256} {s0 : State} {ee : ExecutionEnv} {k C : ℕ}
    {val : UInt256} {R : List UInt256}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD ballotBytecode ee g s0 ⟨194⟩ (Ballot.ballotRetEnd :: R)
        (solcReturnMem val) (UInt256.ofNat 5) rdata acc k C) (hov : R.length + 5 ≤ 1024) :
    RDret ballotBytecode g s0 acc (UInt256.toByteArray val) := by
  exact evm_run h with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 5) (by decide)
      mem_cost
      (solcReturnMem_mload64 val)
      (by decide) (by evm_ov),
    dup1, swap2, sub, swap1,
    raw ret 0 (UInt256.toByteArray val) (by decide)
      mem_cost
      (by
        rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide,
          Ballot.ballotSubRet32_toNat]
        simpa using solcReturnMem_read128 val)
      (by evm_ov) ]

/-- Ballot's shared one-word return tail at pc 194, generalized to any memory whose free pointer
    word is `0x80` and whose return word lives at `0x80`. -/
theorem RD.ballotReturnOneWord194OfMem {g : Sat256} {s0 : State} {ee : ExecutionEnv} {k C : ℕ}
    {val : UInt256} {R : List UInt256} {mem : ByteArray}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD ballotBytecode ee g s0 ⟨194⟩ (Ballot.ballotRetEnd :: R)
        mem (UInt256.ofNat 5) rdata acc k C)
    (hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 5 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
        (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩)
    (hread128 : mem.readWithPadding 128 32 = UInt256.toByteArray val)
    (hov : R.length + 5 ≤ 1024) :
    RDret ballotBytecode g s0 acc (UInt256.toByteArray val) := by
  exact evm_run h with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 5) (by decide)
      mem_cost
      hmload64
      (by decide) (by evm_ov),
    dup1, swap2, sub, swap1,
    raw ret 0 (UInt256.toByteArray val) (by decide)
      mem_cost
      (by
        rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide,
          Ballot.ballotSubRet32_toNat]
        exact hread128)
      (by evm_ov) ]

end Reasoning.Reach
