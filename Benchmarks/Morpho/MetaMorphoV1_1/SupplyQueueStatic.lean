import Benchmarks.Morpho.MetaMorphoV1_1.SupplyQueueStorePrepare

/-! Static-mode termination at the first queue-length store. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1Bytecode

theorem supplyQueueStoreStatic {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem out : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {len : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 4 ≤ 1024)
    (hperm : I.perm = false)
    (rd : RD (deployedRuntime v) I g s0 ⟨10089⟩ (len :: R) mem aw out σ k C) :
    RDstatic (deployedRuntime v) g s0 := by
  have r1 := rd.push1 (UInt256.ofNat 20) (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨10089⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 20), 1),
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  obtain ⟨_, _, r2⟩ := RD.sload r1 (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨10091⟩ : UInt256), UInt8.ofNat 84, .SLOAD, none, immutableLayout_inBounds,
      immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.dup2 (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨10092⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds,
      immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 20) (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨10093⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 20), 1),
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  exact RD.sstoreStatic r4 hperm (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨10095⟩ : UInt256), UInt8.ofNat 85, .SSTORE, none, immutableLayout_inBounds,
      immutableTemplate_size64)) (by evm_ov)

end Benchmarks.Morpho.MetaMorphoV1_1
