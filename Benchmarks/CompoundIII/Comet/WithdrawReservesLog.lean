import Benchmarks.CompoundIII.Comet.GetterCommon
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_033

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

-- The supplied LOG2 summary assumes permission; its prefix also proves the static halt.
theorem cometWithdrawReservesLogStatic {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem rdata : ByteArray} {aw : UInt256}
    {σ : AccountMap} {k C : Nat} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024) (hperm : ee.perm = false)
    (h : RD (deployedRuntime v) ee g s0 ⟨6302⟩ (x0 :: x1 :: x2 :: x3 :: R)
      mem aw rdata σ k C) : RDstatic (deployedRuntime v) g s0 := by
  let r0 := h
  have r1 := r0.jumpdest
    (by immutable_decode(immutableLayout, cometWithExtendedAssetListBytecode,
      wordsOf (immStore v), (⟨6302⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none,
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 64)
    (by immutable_decode(immutableLayout, cometWithExtendedAssetListBytecode,
      wordsOf (immStore v), (⟨6303⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1,
      some ((UInt256.ofNat 64), 1),
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := RD.genMload r2
    (by immutable_decode(immutableLayout, cometWithExtendedAssetListBytecode,
      wordsOf (immStore v), (⟨6305⟩ : UInt256), UInt8.ofNat 81, .MLOAD, none,
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.swap4
    (by immutable_decode(immutableLayout, cometWithExtendedAssetListBytecode,
      wordsOf (immStore v), (⟨6306⟩ : UInt256), UInt8.ofNat 147, .SWAP4, none,
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.dup5
    (by immutable_decode(immutableLayout, cometWithExtendedAssetListBytecode,
      wordsOf (immStore v), (⟨6307⟩ : UInt256), UInt8.ofNat 132, .DUP5, none,
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := RD.genMstore r5
    (by immutable_decode(immutableLayout, cometWithExtendedAssetListBytecode,
      wordsOf (immStore v), (⟨6308⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none,
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.and
    (by immutable_decode(immutableLayout, cometWithExtendedAssetListBytecode,
      wordsOf (immStore v), (⟨6309⟩ : UInt256), UInt8.ofNat 22, .AND, none,
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.swap2
    (by immutable_decode(immutableLayout, cometWithExtendedAssetListBytecode,
      wordsOf (immStore v), (⟨6310⟩ : UInt256), UInt8.ofNat 145, .SWAP2, none,
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.push1 (UInt256.ofNat 32)
    (by immutable_decode(immutableLayout, cometWithExtendedAssetListBytecode,
      wordsOf (immStore v), (⟨6311⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1,
      some ((UInt256.ofNat 32), 1),
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.swap1
    (by immutable_decode(immutableLayout, cometWithExtendedAssetListBytecode,
      wordsOf (immStore v), (⟨6313⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none,
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  exact RD.log2Static r10 hperm
    (by immutable_decode(immutableLayout, cometWithExtendedAssetListBytecode,
      wordsOf (immStore v), (⟨6314⟩ : UInt256), UInt8.ofNat 162, .LOG2, none,
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)

end Benchmarks.CompoundIII.Comet
