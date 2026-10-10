import Benchmarks.Morpho.MetaMorphoV1_1.OptionalCallSource
import Benchmarks.Morpho.MetaMorphoV1_1.OptionalReturnRoutines
import Benchmarks.Morpho.MetaMorphoV1_1.AddressVerifyRoutines
import Benchmarks.Morpho.MetaMorphoV1_1.CallReturnRoutines
import Benchmarks.Morpho.MetaMorphoV1_1.AddressVerifyBuffer

/-! Couple every post-CALL branch to the allocated SafeERC20 source helper. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option autoImplicit false
set_option maxRecDepth 2000

theorem optionalCallPostSimulation {I : ExecutionEnv} {g : Sat256} {s0 evm evm' : State}
    {mem data out : ByteArray} {aw : UInt256} {k C : Nat}
    {ptr ret : UInt256} {R : List UInt256} {ok : Bool}
    (v : MetaMorphoV1_1Immutables) (imms : Store) (token : AccountAddress)
    (hstack : R.length + 13 ≤ 1024) (hptr : ptr.toNat < 2 ^ 64)
    (hout : out.size < UInt256.size) (hfree : memLoad ⟨64⟩ mem = ptr)
    (hzero : memLoad ⟨96⟩ mem = ⟨0⟩)
    (hcall : callViaEVM evm token 0 data (ok, evm', out))
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD (deployedRuntime v) I g s0 ⟨18993⟩
      ((if ok then ⟨1⟩ else ⟨0⟩) :: ⟨19007⟩ :: UInt256.ofNat token.toNat :: ret :: R)
      mem aw out evm'.accountMap k C) :
    (ExecFuncBody config (optionalCallFrame imms token data ptr) evm
        allocatedOptionalReturnFunction.body .reverted ∧ RDrev (deployedRuntime v) g s0) ∨
      (ok = true ∧ callReturnFits ptr out ∧
        ExecFuncBody config (optionalCallFrame imms token data ptr) evm
          allocatedOptionalReturnFunction.body
          (.returned (optionalResultFrame imms token data ptr out) evm'
            (some [uint256Value (callReturnCursor ptr out)])) ∧
        ∃ aw' k' C', RD (deployedRuntime v) I g s0 ret R
          (callReturnMemory mem ptr out) aw' out evm'.accountMap k' C') := by
  have h1 := metaMorphoV1_1_block_18993 (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
  rcases callReturnBuffer v (by
      simp only [metaMorphoV1_1_block_18993_stack, List.length_cons]; omega) hptr hout hfree
      (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) h1 with
    ⟨hbad, hrev⟩ | ⟨hfit, aw2, k2, C2, h2⟩
  · exact .inl ⟨optionalCallBodyRevertsAddress imms token data ptr ok out hcall (.inl hbad), hrev⟩
  · have h3 := metaMorphoV1_1_block_19000 (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega)
      (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h2
    have hlen := callReturnMemory_length mem ptr out hzero
    have hword := callReturnMemory_word mem ptr out
    have hp32 : ptr.toNat + 32 < UInt256.size := by change _ < 2 ^ 256; omega
    cases ok with
    | false =>
        exact .inl ⟨optionalCallBodyRevertsAddress imms token data ptr false out hcall
            (.inr (.inl rfl)), addressVerifyRevertCall v
              (by simp only [List.length_cons]; omega) h3⟩
    | true =>
        by_cases hv : addressReturnValid evm' token out
        · obtain ⟨aw4, k4, C4, h4⟩ := addressVerifyReturn v
            (by simp only [List.length_cons]; omega)
            ((addressReturnValid_memory hout hzero).mp hv)
            (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) h3
          have hs : out.size < 2 ^ 64 := by rcases hfit with hz | ⟨hs, _⟩ <;> omega
          by_cases hb : optionalReturnValid out
          · exact .inr ⟨rfl, hfit,
              optionalCallBodyReturns imms token data ptr out hcall hfit hv hb,
              optionalReturnReturn v (by omega) hs hlen (fun hl ↦ hword hl hp32) hb hret h4⟩
          · exact .inl ⟨optionalCallBodyRevertsBool imms token data ptr out hcall hfit hv hb,
              optionalReturnReverts v (by omega) hs hlen (fun hl ↦ hword hl hp32) hb h4⟩
        · have hz : out.size = 0 := not_not.mp (fun hn ↦ hv (.inl hn))
          have hc : extCodeSizeWord evm'.accountMap (UInt256.ofNat token.toNat) = ⟨0⟩ :=
            not_not.mp (fun hn ↦ hv (.inr hn))
          exact .inl ⟨optionalCallBodyRevertsAddress imms token data ptr true out hcall
              (.inr (.inr hv)), addressVerifyRevertCode v
                (by simp only [List.length_cons]; omega) (by simpa only [hz] using hlen) hc h3⟩

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
