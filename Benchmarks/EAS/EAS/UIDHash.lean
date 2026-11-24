import Benchmarks.EAS.EAS.HashLength
import Benchmarks.EAS.EAS.UIDMemoryViews

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

theorem easUIDHash {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {lenPtr dataPtr : UInt256} {R : List UInt256} (v : EASImmutables) (site : UIDSite)
    (hstack : R.length+2 ≤ 1024)
    (rd : RD fork (deployedRuntime v) ee g s0 (uidHashPC site) (lenPtr::dataPtr::R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 (uidDonePC site)
      (keccakWord dataPtr (memLoad lenPtr mem) mem::R) mem aw' rdata σ k' C' := by
  cases site with
  | single s1 s2 s3 s4 s5 s6 s7 s8 =>
    obtain ⟨aw',k',C',rd'⟩ := hashLength hstack
      (by immutable_decode(immutableLayout, easBytecode, wordsOf (immStore v), (⟨8473⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, easBlocks.immutableLayout_inBounds, easBlocks.immutableTemplate_size64))
      (by immutable_decode(immutableLayout, easBytecode, wordsOf (immStore v), (⟨8474⟩ : UInt256), UInt8.ofNat 81, .MLOAD, none, easBlocks.immutableLayout_inBounds, easBlocks.immutableTemplate_size64))
      (by immutable_decode(immutableLayout, easBytecode, wordsOf (immStore v), (⟨8475⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, easBlocks.immutableLayout_inBounds, easBlocks.immutableTemplate_size64))
      (by immutable_decode(immutableLayout, easBytecode, wordsOf (immStore v), (⟨8476⟩ : UInt256), UInt8.ofNat 32, .KECCAK256, none, easBlocks.immutableLayout_inBounds, easBlocks.immutableTemplate_size64)) rd
    exact ⟨aw',k',C',rd'⟩
  | many s1 s2 s3 s4 s5 s6 =>
    obtain ⟨aw',k',C',rd'⟩ := hashLength hstack
      (by immutable_decode(immutableLayout, easBytecode, wordsOf (immStore v), (⟨10689⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, easBlocks.immutableLayout_inBounds, easBlocks.immutableTemplate_size64))
      (by immutable_decode(immutableLayout, easBytecode, wordsOf (immStore v), (⟨10690⟩ : UInt256), UInt8.ofNat 81, .MLOAD, none, easBlocks.immutableLayout_inBounds, easBlocks.immutableTemplate_size64))
      (by immutable_decode(immutableLayout, easBytecode, wordsOf (immStore v), (⟨10691⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, easBlocks.immutableLayout_inBounds, easBlocks.immutableTemplate_size64))
      (by immutable_decode(immutableLayout, easBytecode, wordsOf (immStore v), (⟨10692⟩ : UInt256), UInt8.ofNat 32, .KECCAK256, none, easBlocks.immutableLayout_inBounds, easBlocks.immutableTemplate_size64)) rd
    exact ⟨aw',k',C',rd'⟩

end Benchmarks.EAS.EAS
