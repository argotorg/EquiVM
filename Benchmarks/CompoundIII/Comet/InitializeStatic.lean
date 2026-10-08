import Benchmarks.CompoundIII.Comet.Common
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_014

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables
open cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 10000

-- The supplied success summary requires write permission. Stop at its first SSTORE
-- to cover static-mode failure, using exactly the decoded prefix of block 1861.
theorem cometInitializeStatic {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem rdata : ByteArray}
    {aw : UInt256} {σ : AccountMap} {k C : Nat} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024) (hperm : ee.perm = false)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 1861)
      (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C) :
    RDstatic (deployedRuntime v) g s0 := by
  let r0 := h
  have r1 := r0.jumpdest 
    (by immutable_decode(immutableLayout, cometWithExtendedAssetListBytecode,
      wordsOf (immStore v), (⟨1861⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none,
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.pushConst (UInt256.ofNat 1099511627775) (width := 5) (op := .PUSH5) (by decide) 
    (by immutable_decode(immutableLayout, cometWithExtendedAssetListBytecode,
      wordsOf (immStore v), (⟨1862⟩ : UInt256), UInt8.ofNat 100, .Push .PUSH5, some ((UInt256.ofNat 1099511627775), 5),
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 208) 
    (by immutable_decode(immutableLayout, cometWithExtendedAssetListBytecode,
      wordsOf (immStore v), (⟨1868⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 208), 1),
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.shl 
    (by immutable_decode(immutableLayout, cometWithExtendedAssetListBytecode,
      wordsOf (immStore v), (⟨1870⟩ : UInt256), UInt8.ofNat 27, .SHL, none,
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.not 
    (by immutable_decode(immutableLayout, cometWithExtendedAssetListBytecode,
      wordsOf (immStore v), (⟨1871⟩ : UInt256), UInt8.ofNat 25, .NOT, none,
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.swap1 
    (by immutable_decode(immutableLayout, cometWithExtendedAssetListBytecode,
      wordsOf (immStore v), (⟨1872⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none,
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.swap3 
    (by immutable_decode(immutableLayout, cometWithExtendedAssetListBytecode,
      wordsOf (immStore v), (⟨1873⟩ : UInt256), UInt8.ofNat 146, .SWAP3, none,
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.and 
    (by immutable_decode(immutableLayout, cometWithExtendedAssetListBytecode,
      wordsOf (immStore v), (⟨1874⟩ : UInt256), UInt8.ofNat 22, .AND, none,
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.push1 (UInt256.ofNat 208) 
    (by immutable_decode(immutableLayout, cometWithExtendedAssetListBytecode,
      wordsOf (immStore v), (⟨1875⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 208), 1),
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.swap3 
    (by immutable_decode(immutableLayout, cometWithExtendedAssetListBytecode,
      wordsOf (immStore v), (⟨1877⟩ : UInt256), UInt8.ofNat 146, .SWAP3, none,
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.swap1 
    (by immutable_decode(immutableLayout, cometWithExtendedAssetListBytecode,
      wordsOf (immStore v), (⟨1878⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none,
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r12 := r11.swap3 
    (by immutable_decode(immutableLayout, cometWithExtendedAssetListBytecode,
      wordsOf (immStore v), (⟨1879⟩ : UInt256), UInt8.ofNat 146, .SWAP3, none,
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r13 := r12.shl 
    (by immutable_decode(immutableLayout, cometWithExtendedAssetListBytecode,
      wordsOf (immStore v), (⟨1880⟩ : UInt256), UInt8.ofNat 27, .SHL, none,
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r14 := r13.and 
    (by immutable_decode(immutableLayout, cometWithExtendedAssetListBytecode,
      wordsOf (immStore v), (⟨1881⟩ : UInt256), UInt8.ofNat 22, .AND, none,
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r15 := r14.or 
    (by immutable_decode(immutableLayout, cometWithExtendedAssetListBytecode,
      wordsOf (immStore v), (⟨1882⟩ : UInt256), UInt8.ofNat 23, .OR, none,
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r16 := r15.push1 (UInt256.ofNat 1) 
    (by immutable_decode(immutableLayout, cometWithExtendedAssetListBytecode,
      wordsOf (immStore v), (⟨1883⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1),
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  exact RD.sstoreStatic r16 hperm 
    (by immutable_decode(immutableLayout, cometWithExtendedAssetListBytecode,
      wordsOf (immStore v), (⟨1885⟩ : UInt256), UInt8.ofNat 85, .SSTORE, none,
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)

end Benchmarks.CompoundIII.Comet
