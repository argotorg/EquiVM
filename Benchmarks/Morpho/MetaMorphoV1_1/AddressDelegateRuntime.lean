import Benchmarks.Morpho.MetaMorphoV1_1.AddressDelegatePost

/-! Complete simulation of the Address delegate-call routine used by multicall. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option maxRecDepth 2000

theorem addressDelegateRoutine {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem data rdata : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {input ptr ret : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (imms : Store)
    (hstack : R.length + 11 ≤ 1024) (hptr : ptr.toNat < 2 ^ 64)
    (hs : SourceState s0 I σ evm) (hfree : memLoad ⟨64⟩ mem = ptr)
    (hzero : memLoad ⟨96⟩ mem = ⟨0⟩)
    (hdata : mem.readWithPadding (input + ⟨32⟩).toNat (memLoad input mem).toNat = data)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD (deployedRuntime v) I g s0 ⟨3951⟩ (input :: ⟨0⟩ :: ⟨0⟩ :: ret :: R)
      mem aw rdata σ k C) :
    (ExecFuncBody config (addressCallFrame imms I.codeOwner data ptr) evm
        allocatedDelegateCallFunction.body .reverted ∧ RDrev (deployedRuntime v) g s0) ∨
      ∃ (evm' : State) (out : ByteArray) (aw' : UInt256) (k' C' : Nat),
        SourceState s0 I evm'.accountMap evm' ∧ callReturnFits ptr out ∧
        ExecFuncBody config (addressCallFrame imms I.codeOwner data ptr) evm
          allocatedDelegateCallFunction.body
          (.returned (addressCallResultFrame imms I.codeOwner data ptr out) evm'
            (some [.bytes out, uint256Value (callReturnCursor ptr out)])) ∧
        RD (deployedRuntime v) I g s0 ret (callReturnPointer ptr out :: R)
          (callReturnMemory mem ptr out) aw' out evm'.accountMap k' C' := by
  obtain ⟨aw1, k1, C1, h1⟩ := metaMorphoV1_1_block_3951_packed
    (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega) rd
  simp only [metaMorphoV1_1_block_3951_stack] at h1
  have hdec : decode (deployedRuntime v) ⟨3960⟩ = some (.DELEGATECALL, none) := by
    change decode (immutableLayout.runtime metaMorphoV1_1Bytecode
      (wordsOf (immStore v))) _ = _
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨3960⟩ : UInt256), UInt8.ofNat 244, .DELEGATECALL, none,
      metaMorphoV1_1Blocks.immutableLayout_inBounds,
      metaMorphoV1_1Blocks.immutableTemplate_size64)
  obtain ⟨evm', ok, out, aw2, k2, C2, hcall, hs', hout, h2⟩ := delegateCallSimulation
    (by simp only [List.length_cons]; omega) hdec hs
    (accountAddress_roundtrip I.codeOwner).symm hdata h1
  have hm : callOutputMem mem out ⟨0⟩ ⟨0⟩ = mem := by
    unfold callOutputMem
    have hz : (⟨0⟩ : UInt256) ⊓ UInt256.ofNat out.size = ⟨0⟩ := rfl
    rw [hz]
    exact byteArray_write_len_zero ..
  rw [hm] at h2
  rcases addressDelegatePostSimulation v imms hstack hptr hout hfree hzero hcall hret h2 with
    hrev | ⟨_, hfit, hbody, aw3, k3, C3, h3⟩
  · exact .inl hrev
  · exact .inr ⟨evm', out, aw3, k3, C3, hs', hfit, hbody, h3⟩

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
