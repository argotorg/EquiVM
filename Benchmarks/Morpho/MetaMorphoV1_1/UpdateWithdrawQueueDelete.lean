import Benchmarks.Morpho.MetaMorphoV1_1.MarketConfigDeletion
import Benchmarks.Morpho.MetaMorphoV1_1.UpdateWithdrawQueueHeap
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_043

/-! The configuration deletion, including its first static-mode violation. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option maxRecDepth 2000

theorem updateWithdrawQueueDeleteReturn {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem out : ByteArray} {aw : UInt256} {k C : Nat} {id : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 3 ≤ 1024) (hperm : I.perm = true)
    (hs : SourceState s0 I evm.accountMap evm)
    (rd : RD (deployedRuntime v) I g s0 ⟨8573⟩ (id :: R) mem aw out evm.accountMap k C) :
    SourceState s0 I (deletedMarketConfigState evm id).accountMap
      (deletedMarketConfigState evm id) ∧ ∃ aw' k' C',
      RD (deployedRuntime v) I g s0 ⟨8452⟩ R (twoWordHashMem id ⟨13⟩ mem) aw' out
        (deletedMarketConfigState evm id).accountMap k' C' := by
  have hs' := hs.storageWrite (solcMappingSlot ⟨13⟩ id) ⟨0⟩
  have hmap : (deletedMarketConfigState evm id).accountMap =
      sstoreAccountMap I.codeOwner evm.accountMap (solcMappingSlot ⟨13⟩ id) ⟨0⟩ := by
    rw [deletedMarketConfigState, storageStore_accountMap, hs.env]
  refine ⟨?_, ?_⟩
  · rw [hmap]
    simpa only [deletedMarketConfigState, hs.env] using hs'
  · obtain ⟨aw', k', C', r1⟩ := metaMorphoV1_1_block_8573_packed
      (immWords := wordsOf (immStore v)) hstack hperm
      (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
    have hh : keccakWord ⟨0⟩ (UInt256.ofNat 64)
        ((UInt256.ofNat 13).toByteArray.write 0
          (id.toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32) =
        solcMappingSlot ⟨13⟩ id := twoWordHashMem_solcMappingSlot_any _ _ _
    exact ⟨aw', k', C', by simpa only [hh, ← hmap] using r1⟩

theorem updateWithdrawQueueDeleteStatic {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem out : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {id : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 3 ≤ 1024) (hperm : I.perm = false)
    (rd : RD (deployedRuntime v) I g s0 ⟨8573⟩ (id :: R) mem aw out σ k C) :
    RDstatic (deployedRuntime v) g s0 := by
  have r1 := rd.jumpdest (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨8573⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none,
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push0 (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨8574⟩ : UInt256), UInt8.ofNat 95, .PUSH0, none,
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.swap1 (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨8575⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none,
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.dup2 (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨8576⟩ : UInt256), UInt8.ofNat 129, .DUP2, none,
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := RD.genMstore r4 (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨8577⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none,
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 13) (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨8578⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some (UInt256.ofNat 13, 1),
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 32) (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨8580⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some (UInt256.ofNat 32, 1),
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := RD.genMstore r7 (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨8582⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none,
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.push1 (UInt256.ofNat 64) (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨8583⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some (UInt256.ofNat 64, 1),
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.dup2 (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨8585⟩ : UInt256), UInt8.ofNat 129, .DUP2, none,
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := RD.genKeccak256 r10 (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨8586⟩ : UInt256), UInt8.ofNat 32, .KECCAK256, none,
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  exact RD.sstoreStatic r11 hperm (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨8587⟩ : UInt256), UInt8.ofNat 85, .SSTORE, none,
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)

end Benchmarks.Morpho.MetaMorphoV1_1
