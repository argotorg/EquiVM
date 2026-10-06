import Reasoning.StateFacts
import Reasoning.ABIViews
import Reasoning.WordArithmetic
import Reasoning.EVMWord
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


/-- The shared solc return wrapper computes the fixed one-word return length. -/
abbrev ballotRetEnd : UInt256 := (⟨32⟩ : UInt256) + ⟨128⟩

theorem ballotSubRet32_toNat :
    (UInt256.sub ballotRetEnd ⟨128⟩).toNat = 32 := by
  decide

/-- The standard Solidity panic selector word. -/
def ballotPanicSelector : UInt256 :=
  UInt256.shiftLeft (⟨0x4e487b71⟩ : UInt256) ⟨224⟩

def ballotPanicMem0 (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray ballotPanicSelector).write 0 mem 0 32

def ballotPanicMem (panicCode : UInt256) (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray panicCode).write 0 (ballotPanicMem0 mem) 4 32

end Ballot

namespace Reasoning.Reach

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory

/-! ## Ballot-local return routines -/

/-- Ballot's Solidity `Panic(0x32)` array-bounds block at pc 1815. -/
theorem RD.ballotPanic32Revert1815 {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {R : List UInt256} {mem : ByteArray} {rdata : ByteArray}
    {acc : AccountMap}
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
    {acc : AccountMap}
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
    {rdata : ByteArray} {acc : AccountMap}
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
    {rdata : ByteArray} {acc : AccountMap}
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
    {rdata : ByteArray} {acc : AccountMap}
    (h : RD ballotBytecode ee g s0 ⟨194⟩ (Ballot.ballotRetEnd :: R)
        mem (UInt256.ofNat 5) rdata acc k C)
    (hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size then ⟨0⟩
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
