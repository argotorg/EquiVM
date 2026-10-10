import Benchmarks.Morpho.MetaMorphoV1_1.Common
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_017

/-! The final Skim log rejects a static entry, after both token calls have completed. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option autoImplicit false

theorem skimEventStatic {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {amount token : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 5 ≤ 1024) (hperm : I.perm = false)
    (rd : RD (deployedRuntime v) I g s0 ⟨2821⟩ (amount :: token :: R)
      mem aw rdata σ k C) : RDstatic (deployedRuntime v) g s0 := by
  change RD (immutableLayout.runtime metaMorphoV1_1Bytecode (wordsOf (immStore v)))
    I g s0 _ _ _ _ _ _ _ _ at rd
  have h1 := rd.jumpdest (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨2821⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none,
      metaMorphoV1_1Blocks.immutableLayout_inBounds,
      metaMorphoV1_1Blocks.immutableTemplate_size64)) (by evm_ov)
  have h2 := h1.push1 ⟨64⟩ (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨2822⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some (⟨64⟩, 1),
      metaMorphoV1_1Blocks.immutableLayout_inBounds,
      metaMorphoV1_1Blocks.immutableTemplate_size64)) (by evm_ov)
  have h3 := RD.genMload h2 (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨2824⟩ : UInt256), UInt8.ofNat 81, .MLOAD, none,
      metaMorphoV1_1Blocks.immutableLayout_inBounds,
      metaMorphoV1_1Blocks.immutableTemplate_size64)) (by evm_ov)
  have h4 := h3.swap1 (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨2825⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none,
      metaMorphoV1_1Blocks.immutableLayout_inBounds,
      metaMorphoV1_1Blocks.immutableTemplate_size64)) (by evm_ov)
  have h5 := h4.dup2 (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨2826⟩ : UInt256), UInt8.ofNat 129, .DUP2, none,
      metaMorphoV1_1Blocks.immutableLayout_inBounds,
      metaMorphoV1_1Blocks.immutableTemplate_size64)) (by evm_ov)
  have h6 := RD.genMstore h5 (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨2827⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none,
      metaMorphoV1_1Blocks.immutableLayout_inBounds,
      metaMorphoV1_1Blocks.immutableTemplate_size64)) (by evm_ov)
  have h7 := h6.pushConst
    ⟨19405579946696383609679024514635240689788502521367193485171035189342501644216⟩
    (width := 32) (op := .PUSH32) (by decide) (by
      immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
        (⟨2828⟩ : UInt256), UInt8.ofNat 127, .Push .PUSH32,
        some (⟨19405579946696383609679024514635240689788502521367193485171035189342501644216⟩, 32),
        metaMorphoV1_1Blocks.immutableLayout_inBounds,
        metaMorphoV1_1Blocks.immutableTemplate_size64)) (by evm_ov)
  have h8 := h7.push1 ⟨32⟩ (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨2861⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some (⟨32⟩, 1),
      metaMorphoV1_1Blocks.immutableLayout_inBounds,
      metaMorphoV1_1Blocks.immutableTemplate_size64)) (by evm_ov)
  have h9 := h8.caller (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨2863⟩ : UInt256), UInt8.ofNat 51, .CALLER, none,
      metaMorphoV1_1Blocks.immutableLayout_inBounds,
      metaMorphoV1_1Blocks.immutableTemplate_size64)) (by evm_ov)
  have h10 := h9.swap3 (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨2864⟩ : UInt256), UInt8.ofNat 146, .SWAP3, none,
      metaMorphoV1_1Blocks.immutableLayout_inBounds,
      metaMorphoV1_1Blocks.immutableTemplate_size64)) (by evm_ov)
  exact h10.log3Static hperm (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨2865⟩ : UInt256), UInt8.ofNat 163, .LOG3, none,
      metaMorphoV1_1Blocks.immutableLayout_inBounds,
      metaMorphoV1_1Blocks.immutableTemplate_size64)) (by evm_ov)

end Benchmarks.Morpho.MetaMorphoV1_1
