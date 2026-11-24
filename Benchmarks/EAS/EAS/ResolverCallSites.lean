import Benchmarks.EAS.EAS.Entry

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

def resolverPreparePC (many rev : Bool) : UInt256 :=
  if many then (if rev then ⟨15183⟩ else ⟨14562⟩) else (if rev then ⟨15857⟩ else ⟨16068⟩)

def resolverCallPC (many rev : Bool) : UInt256 :=
  if many then (if rev then ⟨15187⟩ else ⟨14566⟩) else (if rev then ⟨15861⟩ else ⟨16072⟩)

theorem resolverPrepare {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {finish ptr target value : UInt256} {R : List UInt256} (v : EASImmutables) (many rev : Bool)
    (hstack : R.length+8 ≤ 1024)
    (rd : RD fork (deployedRuntime v) ee g s0 (resolverPreparePC many rev)
      (finish::ptr::value::ptr::target::ptr::⟨32⟩::ptr::R) mem aw rdata σ k C) :
    ∃ gasArg aw' k' C', RD fork (deployedRuntime v) ee g s0 (resolverCallPC many rev)
      (gasArg::target::value::ptr::UInt256.sub finish ptr::ptr::⟨32⟩::ptr::R) mem aw' rdata σ k' C' := by
  cases many with
  | false =>
    cases rev with
    | false =>
      obtain ⟨aw1,k1,C1,rd1⟩ := easBlocks.eas_block_16068_packed (immWords := wordsOf (immStore v))
        (by simp only [List.length_cons]; omega) rd
      exact ⟨_,aw1,k1,C1,rd1⟩
    | true =>
      obtain ⟨aw1,k1,C1,rd1⟩ := easBlocks.eas_block_15857_packed (immWords := wordsOf (immStore v))
        (by simp only [List.length_cons]; omega) rd
      exact ⟨_,aw1,k1,C1,rd1⟩
  | true =>
    cases rev with
    | false =>
      obtain ⟨aw1,k1,C1,rd1⟩ := easBlocks.eas_block_14562_packed (immWords := wordsOf (immStore v))
        (by simp only [List.length_cons]; omega) rd
      exact ⟨_,aw1,k1,C1,rd1⟩
    | true =>
      obtain ⟨aw1,k1,C1,rd1⟩ := easBlocks.eas_block_15183_packed (immWords := wordsOf (immStore v))
        (by simp only [List.length_cons]; omega) rd
      exact ⟨_,aw1,k1,C1,rd1⟩

theorem resolverCall_decode (v : EASImmutables) (many rev : Bool) :
    decode (deployedRuntime v) (resolverCallPC many rev) = some (.CALL, none) := by
  cases many with
  | false =>
    cases rev with
    | false =>
      change decode (immutableLayout.runtime easBytecode (wordsOf (immStore v))) (UInt256.ofNat 16072) = _
      immutable_decode(immutableLayout, easBytecode, wordsOf (immStore v), (⟨16072⟩ : UInt256), UInt8.ofNat 241,
        .CALL, none, easBlocks.immutableLayout_inBounds, easBlocks.immutableTemplate_size64)
    | true =>
      change decode (immutableLayout.runtime easBytecode (wordsOf (immStore v))) (UInt256.ofNat 15861) = _
      immutable_decode(immutableLayout, easBytecode, wordsOf (immStore v), (⟨15861⟩ : UInt256), UInt8.ofNat 241,
        .CALL, none, easBlocks.immutableLayout_inBounds, easBlocks.immutableTemplate_size64)
  | true =>
    cases rev with
    | false =>
      change decode (immutableLayout.runtime easBytecode (wordsOf (immStore v))) (UInt256.ofNat 14566) = _
      immutable_decode(immutableLayout, easBytecode, wordsOf (immStore v), (⟨14566⟩ : UInt256), UInt8.ofNat 241,
        .CALL, none, easBlocks.immutableLayout_inBounds, easBlocks.immutableTemplate_size64)
    | true =>
      change decode (immutableLayout.runtime easBytecode (wordsOf (immStore v))) (UInt256.ofNat 15187) = _
      immutable_decode(immutableLayout, easBytecode, wordsOf (immStore v), (⟨15187⟩ : UInt256), UInt8.ofNat 241,
        .CALL, none, easBlocks.immutableLayout_inBounds, easBlocks.immutableTemplate_size64)

end Benchmarks.EAS.EAS
