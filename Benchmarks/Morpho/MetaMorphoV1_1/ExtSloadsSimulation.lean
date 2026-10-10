import Benchmarks.Morpho.MetaMorphoV1_1.ExtSloadsDecodeRoutines
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_018

/-! Couple the complete post-call path to the cursor-aware source helper, using the same call. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option autoImplicit false

theorem extSloadsReturnValues_length (out : ByteArray) :
    (extSloadsReturnValues out).length = extSloadsReturnCount out :=
  wordArrayValues_length _ _ _

theorem extSloadsReturnValues_cons {out : ByteArray} (hn : 0 < extSloadsReturnCount out) :
    ∃ values, extSloadsReturnValues out =
      wordBytes32Value (calldataWord out (extSloadsReturnOffset out + 32)) :: values := by
  cases hc : extSloadsReturnCount out with
  | zero => omega
  | succ n =>
      simp only [extSloadsReturnValues, Benchmarks.EAS.Attester.returnArrayValues,
        show Benchmarks.EAS.Attester.returnArrayCount out = n + 1 from hc,
        wordArrayValues, wordArrayWords, List.map_cons, Nat.mul_zero, Nat.add_zero]
      exact ⟨_, rfl⟩

theorem decodedArraySize_canonical (out : ByteArray) :
    decodedArraySize (extSloadsReturnValues out) = extSloadsArraySize out := by
  simp only [decodedArraySize, extSloadsReturnValues_length, extSloadsArraySize]

theorem extSloadsCanonicalDecode {out : ByteArray} (hout : out.size < 2 ^ 138)
    (hcheck : extSloadsReturnChecks out) :
    ABI.decodeReturnValueWithMode? config.abiDecodeMode
      (.dynamicArray (.elem (.bytes ⟨31, by decide⟩))) out =
        some (.array (extSloadsReturnValues out)) :=
  Benchmarks.EAS.Attester.returnArrayDecode_ok (by omega) hcheck

theorem extSloadsCanonicalSize {out : ByteArray} (hcheck : extSloadsReturnChecks out) :
    32 + 32 * (extSloadsReturnValues out).length < UInt256.size := by
  have hc : extSloadsReturnCount out ≤ 18446744073709551615 := hcheck.length
  rw [extSloadsReturnValues_length]
  change _ < 2 ^ 256
  omega

theorem extSloadsBodyDecoderReverts {frame : Frame} {evm evm' : State}
    {ptr : UInt256} {morpho : AccountAddress} {slot : UInt256} {out : ByteArray}
    (hlookup : lookupCallable? frame.contract allocateFunction.name =
      some allocateFunction.toCallable)
    (hcall : typedCallViaEVM config evm morpho "extSloads" 0 [.array [wordBytes32Value slot]]
      (true, evm', out) false)
    (hfit : allocationFits ptr (UInt256.ofNat out.size))
    (hbad : ¬ extSloadsReturnChecks out ∨
      ¬ allocationFits (nextCursor ptr (UInt256.ofNat out.size)) (extSloadsArraySize out)) :
    ExecFuncBody config (extSloadsFrame frame ptr morpho [wordBytes32Value slot]) evm
      extSloadsFunction.body .reverted := by
  have hout := extSloadsReturnSize hcall
  have hword : out.size < UInt256.size := by change _ < 2 ^ 256; omega
  by_cases hcheck : extSloadsReturnChecks out
  · have ha : ¬ allocationFits (nextCursor ptr (UInt256.ofNat out.size))
        (decodedArraySize (extSloadsReturnValues out)) := by
      rw [decodedArraySize_canonical]
      exact hbad.resolve_left (not_not_intro hcheck)
    exact extSloadsBodyArrayReverts ptr morpho _ _ out hlookup hcall hword hfit
      (extSloadsCanonicalDecode hout hcheck) (extSloadsCanonicalSize hcheck) ha
  · exact extSloadsBodyDecodeReverts ptr morpho _ out hlookup hcall hword hfit
      (Benchmarks.EAS.Attester.returnArrayDecode_bad (by omega) hcheck)

set_option maxRecDepth 2000 in
theorem extSloadsAfterBufferSimulation {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {out : ByteArray} {σ : AccountMap}
    {k C : Nat} {ptr ret : UInt256} {R : List UInt256}
    {frame : Frame} {evm evm' : State} {morpho : AccountAddress} {slot : UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 12 ≤ 1024)
    (hlo : 96 ≤ ptr.toNat) (hmem : ptr.toNat ≤ mem.size)
    (hlookup : lookupCallable? frame.contract allocateFunction.name =
      some allocateFunction.toCallable)
    (hcall : typedCallViaEVM config evm morpho "extSloads" 0 [.array [wordBytes32Value slot]]
      (true, evm', out) false)
    (hfit : allocationFits ptr (UInt256.ofNat out.size))
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD (deployedRuntime v) I g s0 ⟨13221⟩
      (ptr :: (ptr + UInt256.ofNat out.size) :: ret :: R)
      (extSloadsBufferMem mem ptr out) aw out σ k C) :
    (ExecFuncBody config (extSloadsFrame frame ptr morpho [wordBytes32Value slot]) evm
        extSloadsFunction.body .reverted ∧ RDrev (deployedRuntime v) g s0) ∨
      (extSloadsReturnChecks out ∧
        allocationFits (nextCursor ptr (UInt256.ofNat out.size)) (extSloadsArraySize out) ∧
        ExecFuncBody config (extSloadsFrame frame ptr morpho [wordBytes32Value slot]) evm
          extSloadsFunction.body
          (.returned (extSloadsResultFrame frame ptr morpho [wordBytes32Value slot]
            out (extSloadsReturnValues out)) evm'
            (some [.array (extSloadsReturnValues out),
              uint256Value (extSloadsFinalCursor ptr out (extSloadsReturnValues out))])) ∧
        ∃ aw' k' C', RD (deployedRuntime v) I g s0 ret
          (nextCursor ptr (UInt256.ofNat out.size) :: R)
          (extSloadsDecodedMem (extSloadsBufferMem mem ptr out)
            (nextCursor ptr (UInt256.ofNat out.size)) out) aw' out σ k' C') := by
  have hout := extSloadsReturnSize hcall
  have hword : out.size < UInt256.size := by change _ < 2 ^ 256; omega
  have hp : ptr.toNat < 2 ^ 64 := lt_of_le_of_lt hfit.2 hfit.1
  have hbound : ptr.toNat + out.size + 31 ≤ 2 ^ 200 := by omega
  have hsep : ptr.toNat + out.size ≤ (nextCursor ptr (UInt256.ofNat out.size)).toNat := by
    rw [nextCursor_returnReserve, returnReservePtr_toNat hbound]
    omega
  have r1 : RD (deployedRuntime v) I g s0 ⟨13221⟩
      (UInt256.ofNat ptr.toNat :: UInt256.ofNat (ptr.toNat + out.size) :: ret :: R)
      (extSloadsBufferMem mem ptr out) aw out σ k C := by
    simpa only [← ofNat_add_words, u256_ofNat_toNat] using rd
  rcases extSloadsDecodeReturn v hstack (by omega) hlo
      (by change ptr.toNat + out.size ≤ (extSloadsBufferMem mem ptr out).size
          rw [extSloadsBufferMem_eq hbound,
            Benchmarks.EAS.Attester.returnArrayInputMemory_size hlo hmem]
          omega) hsep
      (memLoad_write_same _ _ _ _ rfl) (extSloadsBufferMem_load hbound hlo hmem) hret r1 with
    ⟨hbad, hrev⟩ | ⟨hc, ha, hreturn⟩
  · exact .inl ⟨extSloadsBodyDecoderReverts hlookup hcall hfit hbad, hrev⟩
  · exact .inr ⟨hc, ha, extSloadsBodyReturns ptr morpho _ _ out hlookup hcall hword hfit
      (extSloadsCanonicalDecode hout hc) (extSloadsCanonicalSize hc)
      (by rwa [decodedArraySize_canonical]), hreturn⟩

set_option maxRecDepth 2000 in
theorem extSloadsPostCallSimulation {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {out : ByteArray} {σ : AccountMap}
    {k C : Nat} {ptr : UInt256} {R : List UInt256}
    {frame : Frame} {evm evm' : State} {morpho : AccountAddress} {slot : UInt256} {ok : Bool}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 14 ≤ 1024)
    (hlo : 96 ≤ ptr.toNat) (hmem : ptr.toNat ≤ mem.size)
    (hlookup : lookupCallable? frame.contract allocateFunction.name =
      some allocateFunction.toCallable)
    (hcall : typedCallViaEVM config evm morpho "extSloads" 0 [.array [wordBytes32Value slot]]
      (ok, evm', out) false)
    (rd : RD (deployedRuntime v) I g s0 ⟨14211⟩
      ((if ok then ⟨1⟩ else ⟨0⟩) :: ptr :: R) mem aw out σ k C) :
    (ExecFuncBody config (extSloadsFrame frame ptr morpho [wordBytes32Value slot]) evm
        extSloadsFunction.body .reverted ∧ RDrev (deployedRuntime v) g s0) ∨
      (ok = true ∧ extSloadsReturnChecks out ∧
        allocationFits ptr (UInt256.ofNat out.size) ∧
        allocationFits (nextCursor ptr (UInt256.ofNat out.size)) (extSloadsArraySize out) ∧
        ExecFuncBody config (extSloadsFrame frame ptr morpho [wordBytes32Value slot]) evm
          extSloadsFunction.body
          (.returned (extSloadsResultFrame frame ptr morpho [wordBytes32Value slot]
            out (extSloadsReturnValues out)) evm'
            (some [.array (extSloadsReturnValues out),
              uint256Value (extSloadsFinalCursor ptr out (extSloadsReturnValues out))])) ∧
        ∃ aw' k' C', RD (deployedRuntime v) I g s0 ⟨14256⟩
          (nextCursor ptr (UInt256.ofNat out.size) :: ⟨14232⟩ :: R)
          (extSloadsDecodedMem (extSloadsBufferMem mem ptr out)
            (nextCursor ptr (UInt256.ofNat out.size)) out) aw' out σ k' C') := by
  have hout := extSloadsReturnSize hcall
  have hword : out.size < UInt256.size := by change _ < 2 ^ 256; omega
  cases ok with
  | false =>
      have hfail := metaMorphoV1_1_block_14211_taken
        (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega)
        (by decide) (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
      exact .inl ⟨extSloadsBodyCallReverts ptr morpho _ out hcall,
        metaMorphoV1_1_block_2921 (immWords := wordsOf (immStore v))
          (by simp only [List.length_cons]; omega)
          (by change 0 + (UInt256.ofNat out.size).toNat ≤ out.size
              rw [UInt256.toNat_ofNat_of_lt hword, Nat.zero_add]) hfail⟩
  | true =>
      by_cases hfit : allocationFits ptr (UInt256.ofNat out.size)
      · obtain ⟨aw1, k1, C1, h1⟩ := extSloadsBufferReturn v (by omega) hword hfit rd
        rcases extSloadsAfterBufferSimulation v (by simp only [List.length_cons]; omega)
            hlo hmem hlookup hcall hfit
            (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) h1 with
          ⟨hsource, hrev⟩ | ⟨hc, ha, hsource, hreturn⟩
        · exact .inl ⟨hsource, hrev⟩
        · exact .inr ⟨rfl, hc, hfit, ha, hsource, hreturn⟩
      · exact .inl ⟨extSloadsBodyBufferReverts ptr morpho _ out hlookup hcall hword hfit,
          extSloadsBufferRevert v (by omega) hword hfit rd⟩

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
