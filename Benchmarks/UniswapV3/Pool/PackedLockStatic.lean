import Benchmarks.UniswapV3.Pool.Common

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool

-- LIBRARY CANDIDATE: the static halt for a read-mask-write lock prefix, at any code offset.
theorem packedLockStaticX {code : ByteArray} {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {pc aw : UInt256} {k C : Nat} {mem rdata : ByteArray} {R : List UInt256}
    (slot mask shift : UInt256) (keepSlot : Bool)
    (h0 : decode code pc = some (.JUMPDEST, none))
    (h1 : decode code (pc + ⟨1⟩) = some (.Push .PUSH1, some (slot, 1)))
    (h3 : decode code (pc + ⟨3⟩) = some (.DUP1, none))
    (h4 : decode code (pc + ⟨4⟩) = some (.SLOAD, none))
    (h5 : decode code (pc + ⟨5⟩) = some (.Push .PUSH1, some (mask, 1)))
    (h7 : decode code (pc + ⟨7⟩) = some (.Push .PUSH1, some (shift, 1)))
    (h9 : decode code (pc + ⟨9⟩) = some (.SHL, none))
    (h10 : decode code (pc + ⟨10⟩) = some (.NOT, none))
    (h11 : decode code (pc + ⟨11⟩) = some (.AND, none))
    (h12 : decode code (pc + ⟨12⟩) = some ((if keepSlot then .DUP2 else .SWAP1), none))
    (h13 : decode code (pc + ⟨13⟩) = some (.SSTORE, none))
    (rd : RD code ee g s0 pc R mem aw rdata σ k C)
    (hperm : ee.perm = false) (hov : R.length + 4 ≤ 1024) : RDstatic code g s0 := by
  have r1 := rd.jumpdest h0 (by omega)
  have r2 := r1.push1 slot h1 (by evm_ov)
  have r3 := r2.dup1 (by simpa only [u256_add_assoc] using h3) (by evm_ov)
  obtain ⟨k4, C4, r4⟩ := r3.sload (by simpa only [u256_add_assoc] using h4) (by evm_ov)
  have r5 := r4.push1 mask (by simpa only [u256_add_assoc] using h5) (by evm_ov)
  have r6 := r5.push1 shift (by simpa only [u256_add_assoc] using h7) (by evm_ov)
  have r7 := r6.shl (by simpa only [u256_add_assoc] using h9) (by evm_ov)
  have r8 := r7.not (by simpa only [u256_add_assoc] using h10) (by evm_ov)
  have r9 := r8.and (by simpa only [u256_add_assoc] using h11) (by evm_ov)
  cases keepSlot with
  | false =>
    have r10 := r9.swap1 (by simpa only [Bool.false_eq_true, ↓reduceIte, u256_add_assoc] using h12)
      (by evm_ov)
    exact r10.sstoreStatic hperm (by simpa only [u256_add_assoc] using h13) (by evm_ov)
  | true =>
    have r10 := r9.dup2 (by simpa only [↓reduceIte, u256_add_assoc] using h12) (by evm_ov)
    exact r10.sstoreStatic hperm (by simpa only [u256_add_assoc] using h13) (by evm_ov)

end Benchmarks.UniswapV3.Pool
