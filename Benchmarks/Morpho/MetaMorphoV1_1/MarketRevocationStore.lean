import Benchmarks.Morpho.MetaMorphoV1_1.MarketRevocationRole

/-! Storage writes, event completion, and static halts for mapping revocations. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1Bytecode

set_option maxRecDepth 2000 in
theorem marketRevocationStoreReturn {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {R : List UInt256} {id : UInt256}
    (v : MetaMorphoV1_1Immutables) (cap : Bool) (hstack : R.length + 7 ≤ 1024)
    (hperm : I.perm = true)
    (rd : RD (deployedRuntime v) I g s0 (marketRevocationStorePC cap) (id :: R)
      mem aw rdata σ k C) :
    RDret (deployedRuntime v) g s0
      (sstoreAccountMap I.codeOwner σ (marketRevocationSlot cap id)
        (marketRevocationWord cap (codeOwnerStorageWord I σ (marketRevocationSlot cap id))))
      ByteArray.empty := by
  cases cap
  · have h := metaMorphoV1_1_block_7790 (immWords := wordsOf (immStore v)) hstack hperm rd
    have hh : keccakWord ⟨0⟩ (UInt256.ofNat 64)
        ((UInt256.ofNat 13).toByteArray.write 0
          (id.toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32) =
        solcMappingSlot ⟨13⟩ id := twoWordHashMem_solcMappingSlot_any _ _ _
    have hm : UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 192))
        (UInt256.ofNat 1) = UInt256.ofNat (2 ^ 192 - 1) := by decide
    rw [hh, hm] at h
    exact h
  · have h := metaMorphoV1_1_block_10711
      (immWords := wordsOf (immStore v)) (by omega) hperm rd
    have hh : keccakWord ⟨0⟩ (UInt256.ofNat 64)
        ((UInt256.ofNat 16).toByteArray.write 0
          (id.toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32) =
        solcMappingSlot ⟨16⟩ id := twoWordHashMem_solcMappingSlot_any _ _ _
    rw [hh] at h
    exact h

set_option maxRecDepth 2000 in
theorem marketRevocationStoreStatic {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {R : List UInt256} {id : UInt256}
    (v : MetaMorphoV1_1Immutables) (cap : Bool) (hstack : R.length + 7 ≤ 1024)
    (hperm : I.perm = false)
    (rd : RD (deployedRuntime v) I g s0 (marketRevocationStorePC cap) (id :: R)
      mem aw rdata σ k C) : RDstatic (deployedRuntime v) g s0 := by
  cases cap
  · let r0 := rd
    have r1 := r0.push0 (by
      immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
        (⟨7790⟩ : UInt256), UInt8.ofNat 95, .PUSH0, none,
        immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
    have r2 := r1.dup2 (by
      immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
        (⟨7791⟩ : UInt256), UInt8.ofNat 129, .DUP2, none,
        immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
    have r3 := r2.dup2 (by
      immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
        (⟨7792⟩ : UInt256), UInt8.ofNat 129, .DUP2, none,
        immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
    have r4 := RD.genMstore r3 (by
      immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
        (⟨7793⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none,
        immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
    have r5 := r4.push1 (UInt256.ofNat 13) (by
      immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
        (⟨7794⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 13), 1),
        immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
    have r6 := r5.push1 (UInt256.ofNat 32) (by
      immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
        (⟨7796⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 32), 1),
        immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
    have r7 := RD.genMstore r6 (by
      immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
        (⟨7798⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none,
        immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
    have r8 := r7.push1 (UInt256.ofNat 64) (by
      immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
        (⟨7799⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 64), 1),
        immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
    have r9 := r8.dup2 (by
      immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
        (⟨7801⟩ : UInt256), UInt8.ofNat 129, .DUP2, none,
        immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
    have r10 := RD.genKeccak256 r9 (by
      immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
        (⟨7802⟩ : UInt256), UInt8.ofNat 32, .KECCAK256, none,
        immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
    have r11 := r10.dup1 (by
      immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
        (⟨7803⟩ : UInt256), UInt8.ofNat 128, .DUP1, none,
        immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
    obtain ⟨_, _, r12⟩ := RD.sload r11 (by
      immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
        (⟨7804⟩ : UInt256), UInt8.ofNat 84, .SLOAD, none,
        immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
    have r13 := r12.push1 (UInt256.ofNat 1) (by
      immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
        (⟨7805⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1),
        immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
    have r14 := r13.push1 (UInt256.ofNat 1) (by
      immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
        (⟨7807⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1),
        immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
    have r15 := r14.push1 (UInt256.ofNat 192) (by
      immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
        (⟨7809⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 192), 1),
        immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
    have r16 := r15.shl (by
      immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
        (⟨7811⟩ : UInt256), UInt8.ofNat 27, .SHL, none,
        immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
    have r17 := r16.sub (by
      immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
        (⟨7812⟩ : UInt256), UInt8.ofNat 3, .SUB, none,
        immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
    have r18 := r17.and (by
      immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
        (⟨7813⟩ : UInt256), UInt8.ofNat 22, .AND, none,
        immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
    have r19 := r18.swap1 (by
      immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
        (⟨7814⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none,
        immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
    exact r19.sstoreStatic hperm (by
      immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
        (⟨7815⟩ : UInt256), UInt8.ofNat 85, .SSTORE, none,
        immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  · let r0 := rd
    have r1 := r0.dup1 (by
      immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
        (⟨10711⟩ : UInt256), UInt8.ofNat 128, .DUP1, none,
        immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
    have r2 := r1.push0 (by
      immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
        (⟨10712⟩ : UInt256), UInt8.ofNat 95, .PUSH0, none,
        immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
    have r3 := RD.genMstore r2 (by
      immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
        (⟨10713⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none,
        immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
    have r4 := r3.push1 (UInt256.ofNat 16) (by
      immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
        (⟨10714⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 16), 1),
        immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
    have r5 := r4.push1 (UInt256.ofNat 32) (by
      immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
        (⟨10716⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 32), 1),
        immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
    have r6 := RD.genMstore r5 (by
      immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
        (⟨10718⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none,
        immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
    have r7 := r6.push0 (by
      immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
        (⟨10719⟩ : UInt256), UInt8.ofNat 95, .PUSH0, none,
        immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
    have r8 := r7.push1 (UInt256.ofNat 64) (by
      immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
        (⟨10720⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 64), 1),
        immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
    have r9 := r8.dup2 (by
      immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
        (⟨10722⟩ : UInt256), UInt8.ofNat 129, .DUP2, none,
        immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
    have r10 := RD.genKeccak256 r9 (by
      immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
        (⟨10723⟩ : UInt256), UInt8.ofNat 32, .KECCAK256, none,
        immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
    exact r10.sstoreStatic hperm (by
      immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
        (⟨10724⟩ : UInt256), UInt8.ofNat 85, .SSTORE, none,
        immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)

end Benchmarks.Morpho.MetaMorphoV1_1
