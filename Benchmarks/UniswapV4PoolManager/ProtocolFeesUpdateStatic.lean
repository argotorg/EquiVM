import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_008

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
namespace Benchmarks.UniswapV4PoolManager
open poolManagerBlocks
set_option maxRecDepth 5000

-- The fee update halts at its first SSTORE in static mode.
theorem protocolFeesUpdateStatic {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256} {R : List UInt256}
    (hstack : R.length + 18 ≤ 1024)
    (hperm : ee.perm = false)
    (h : RD (immutableLayout.runtime poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 2003) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: R) mem aw rdata σ k C)
 :
    RDstatic (immutableLayout.runtime poolManagerBytecode immWords) g s0 := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨2003⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push20 (UInt256.ofNat 1461501637330902918203684832716283019655932542975) (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨2004⟩ : UInt256), UInt8.ofNat 115, .Push .PUSH20, some ((UInt256.ofNat 1461501637330902918203684832716283019655932542975), 20), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.and (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨2025⟩ : UInt256), UInt8.ofNat 22, .AND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push0 (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨2026⟩ : UInt256), UInt8.ofNat 95, .PUSH0, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := RD.genMstore r4 (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨2027⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 1) (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨2028⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.dup16 (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨2030⟩ : UInt256), UInt8.ofNat 143, .DUP16, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := RD.genMstore r7 (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨2031⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.push1 (UInt256.ofNat 64) (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨2032⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 64), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.push0 (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨2034⟩ : UInt256), UInt8.ofNat 95, .PUSH0, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := RD.genKeccak256 r10 (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨2035⟩ : UInt256), UInt8.ofNat 32, .KECCAK256, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r12 := r11.swap1 (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨2036⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r13 := r12.dup2 (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨2037⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  obtain ⟨_, _, r14⟩ := RD.sload r13 (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨2038⟩ : UInt256), UInt8.ofNat 84, .SLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r15 := r14.add (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨2039⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r16 := r15.swap1 (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨2040⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  exact RD.sstoreStatic r16 hperm
    (by immutable_decode(immutableLayout, poolManagerBytecode, immWords,
      (⟨2041⟩ : UInt256), UInt8.ofNat 85, .SSTORE, none, immutableLayout_inBounds, immutableTemplate_size64))
    (by evm_ov)

end Benchmarks.UniswapV4PoolManager
