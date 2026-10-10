import Benchmarks.Morpho.MetaMorphoV1_1.AddressDelegateSource
import Benchmarks.Morpho.MetaMorphoV1_1.AddressVerifyBuffer
import Benchmarks.Morpho.MetaMorphoV1_1.AddressVerifyRoutines
import Benchmarks.Morpho.MetaMorphoV1_1.CallReturnRoutines
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_022

/-! Every post-DELEGATECALL branch of the Address helper. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option maxRecDepth 2000

theorem addressDelegatePostSimulation {I : ExecutionEnv} {g : Sat256} {s0 evm evm' : State}
    {mem data out : ByteArray} {aw : UInt256} {k C : Nat}
    {ptr ret : UInt256} {R : List UInt256} {ok : Bool}
    (v : MetaMorphoV1_1Immutables) (imms : Store)
    (hstack : R.length + 11 ≤ 1024) (hptr : ptr.toNat < 2 ^ 64)
    (hout : out.size < UInt256.size) (hfree : memLoad ⟨64⟩ mem = ptr)
    (hzero : memLoad ⟨96⟩ mem = ⟨0⟩)
    (hcall : delegateCallViaEVM evm I.codeOwner data (ok, evm', out))
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD (deployedRuntime v) I g s0 ⟨3961⟩
      ((if ok then ⟨1⟩ else ⟨0⟩) :: ret :: R) mem aw out evm'.accountMap k C) :
    (ExecFuncBody config (addressCallFrame imms I.codeOwner data ptr) evm
        allocatedDelegateCallFunction.body .reverted ∧ RDrev (deployedRuntime v) g s0) ∨
      (ok = true ∧ callReturnFits ptr out ∧
        ExecFuncBody config (addressCallFrame imms I.codeOwner data ptr) evm
          allocatedDelegateCallFunction.body
          (.returned (addressCallResultFrame imms I.codeOwner data ptr out) evm'
            (some [.bytes out, uint256Value (callReturnCursor ptr out)])) ∧
        ∃ aw' k' C', RD (deployedRuntime v) I g s0 ret (callReturnPointer ptr out :: R)
          (callReturnMemory mem ptr out) aw' out evm'.accountMap k' C') := by
  have h1 := metaMorphoV1_1_block_3961 (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
  rcases callReturnBuffer v (by
      simp only [List.length_cons]; omega) hptr hout hfree
      (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) h1 with
    ⟨hbad, hrev⟩ | ⟨hfit, aw2, k2, C2, h2⟩
  · exact .inl ⟨addressDelegateBodyReverts imms I.codeOwner data ptr ok out hcall
      (.inl hbad), hrev⟩
  · have h3 := metaMorphoV1_1_block_3968 (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega)
      (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h2
    cases ok with
    | false =>
        exact .inl ⟨addressDelegateBodyReverts imms I.codeOwner data ptr false out hcall
          (.inr (.inl rfl)), addressVerifyRevertCall v
            (by omega) h3⟩
    | true =>
        by_cases hv : addressReturnValid evm' I.codeOwner out
        · exact .inr ⟨rfl, hfit,
            addressDelegateBodyReturns imms I.codeOwner data ptr out hcall hfit hv,
            addressVerifyReturn v (by omega)
              ((addressReturnValid_memory hout hzero).mp hv) hret h3⟩
        · have hn := mt (addressReturnValid_memory (ptr := ptr) hout hzero).mpr hv
          have hb := not_or.mp hn
          exact .inl ⟨addressDelegateBodyReverts imms I.codeOwner data ptr true out hcall
            (.inr (.inr hv)), addressVerifyRevertCode v
              (by omega)
              (not_not.mp hb.1) (not_not.mp hb.2) h3⟩

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
