import Benchmarks.Morpho.MetaMorphoV1_1.UpdateLastAssetsSource
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_075

/-! Bytecode execution of the last-total-assets store and event. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1Bytecode

set_option maxRecDepth 2000 in
theorem updateLastAssetsReturn {evm : EVM.State} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {k C : Nat}
    {R : List UInt256} {value ret : UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 6 ≤ 1024)
    (hperm : evm.executionEnv.perm = true)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD (deployedRuntime v) evm.executionEnv g s0 ⟨16830⟩ (value :: ret :: R)
      mem aw rdata evm.accountMap k C) :
    ∃ aw' k' C', RD (deployedRuntime v) evm.executionEnv g s0 ret R
      (writeWord mem (memLoad ⟨64⟩ mem).toNat value)
      aw' rdata (updateLastAssetsState evm value).accountMap k' C' := by
  simpa only [updateLastAssetsState, storageStore_accountMap] using
    (metaMorphoV1_1_block_16830_packed (immWords := wordsOf (immStore v)) hstack hperm hret rd)

set_option maxRecDepth 2000 in
theorem updateLastAssetsStatic {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {R : List UInt256} {value ret : UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 6 ≤ 1024)
    (hperm : I.perm = false)
    (rd : RD (deployedRuntime v) I g s0 ⟨16830⟩ (value :: ret :: R)
      mem aw rdata σ k C) : RDstatic (deployedRuntime v) g s0 := by
  have r1 := rd.jumpdest (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨16830⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none,
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 32) (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨16831⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 32), 1),
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  let topic : UInt256 :=
    UInt256.ofNat 9838079133031279594831247117274764939180011224231929840752444375652889487593
  have r3 := r2.pushConst topic (width := 32) (op := .PUSH32) (by decide) (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨16833⟩ : UInt256), UInt8.ofNat 127, .Push .PUSH32, some (topic, 32),
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.swap2 (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨16866⟩ : UInt256), UInt8.ofNat 145, .SWAP2, none,
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.dup1 (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨16867⟩ : UInt256), UInt8.ofNat 128, .DUP1, none,
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 22) (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨16868⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 22), 1),
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  exact r6.sstoreStatic hperm (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨16870⟩ : UInt256), UInt8.ofNat 85, .SSTORE, none,
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)

end Benchmarks.Morpho.MetaMorphoV1_1
