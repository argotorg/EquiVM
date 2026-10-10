import Benchmarks.Morpho.MetaMorphoV1_1.OptionalCallSimulation
import Benchmarks.Morpho.MetaMorphoV1_1.ZeroCallSimulation

/-! The complete optional-return call, sharing its opaque callee result with the source. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option autoImplicit false
set_option maxRecDepth 2000

theorem optionalCallSimulation {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem data rdata : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {ptr dataPtr ret : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (imms : Store) (token : AccountAddress)
    (hstack : R.length + 13 ≤ 1024) (hs : SourceState s0 I σ evm)
    (hptr : ptr.toNat < 2 ^ 64) (hlo : 96 ≤ ptr.toNat) (hdataSize : data.size < UInt256.size)
    (hfree : memLoad ⟨64⟩ mem = ptr) (hzero : memLoad ⟨96⟩ mem = ⟨0⟩)
    (hlen : memLoad dataPtr mem = UInt256.ofNat data.size)
    (hdata : mem.readWithPadding (dataPtr + UInt256.ofNat 32).toNat data.size = data)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD (deployedRuntime v) I g s0 ⟨18967⟩
      (UInt256.ofNat token.toNat :: dataPtr :: ret :: R) mem aw rdata σ k C) :
    (ExecFuncBody config (optionalCallFrame imms token data ptr) evm
        allocatedOptionalReturnFunction.body .reverted ∧ RDrev (deployedRuntime v) g s0) ∨
      ∃ (evm' : State) (out : ByteArray) (aw' : UInt256) (k' C' : Nat),
        SourceState s0 I evm'.accountMap evm' ∧ callReturnFits ptr out ∧
        ExecFuncBody config (optionalCallFrame imms token data ptr) evm
          allocatedOptionalReturnFunction.body
          (.returned (optionalResultFrame imms token data ptr out) evm'
            (some [uint256Value (callReturnCursor ptr out)])) ∧
        MemoryPrefix mem (callReturnMemory mem ptr out) ptr.toNat ∧
        memLoad ⟨64⟩ (callReturnMemory mem ptr out) = callReturnCursor ptr out ∧
        RD (deployedRuntime v) I g s0 ret R (callReturnMemory mem ptr out) aw' out
          evm'.accountMap k' C' := by
  obtain ⟨aw1, k1, C1, h1⟩ := metaMorphoV1_1_block_18967_packed
    (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega) rd
  have hmask : UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1)
      (UInt256.ofNat 160)) (UInt256.ofNat 1)) (UInt256.ofNat token.toNat) =
      UInt256.ofNat token.toNat := easWord_mask token
  simp only [metaMorphoV1_1_block_18967_stack, hmask, hlen] at h1
  have hdec : decode (deployedRuntime v) ⟨18992⟩ = some (.CALL, none) := by
    change decode (immutableLayout.runtime metaMorphoV1_1Bytecode
      (wordsOf (immStore v))) _ = _
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨18992⟩ : UInt256), UInt8.ofNat 241, .CALL, none,
      metaMorphoV1_1Blocks.immutableLayout_inBounds,
      metaMorphoV1_1Blocks.immutableTemplate_size64)
  obtain ⟨evm', ok, out, aw2, k2, C2, hcall, hs', hout, h2⟩ :=
    zeroCallSimulation (by simp only [List.length_cons]; omega) hdec hs
      (show token = AccountAddress.ofUInt256 (UInt256.ofNat token.toNat) by
        symm
        rw [accountAddress_ofUInt256_eq_ofNat_toNat]
        exact accountAddress_of_word_val token)
      (by simpa only [UInt256.toNat_ofNat_of_lt hdataSize] using hdata) h1
  have hmin : (min (⟨0⟩ : UInt256) (UInt256.ofNat out.size)).toNat = 0 := by
    have hle : (⟨0⟩ : UInt256) ≤ UInt256.ofNat out.size := by
      change 0 ≤ (UInt256.ofNat out.size).toNat
      omega
    simp [min, hle]
  rw [hmin, byteArray_write_len_zero] at h2
  rcases optionalCallPostSimulation v imms token hstack hptr hout hfree hzero hcall hret h2 with
    hbad | ⟨_, hfit, hsource, aw3, k3, C3, h3⟩
  · exact .inl hbad
  · exact .inr ⟨evm', out, aw3, k3, C3, hs', hfit, hsource,
      callReturnMemory_prefix mem ptr out, callReturnMemory_free mem ptr out hlo hfree, h3⟩

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
