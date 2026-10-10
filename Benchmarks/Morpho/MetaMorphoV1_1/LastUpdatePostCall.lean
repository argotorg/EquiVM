import Benchmarks.Morpho.MetaMorphoV1_1.ExtSloadsSimulation
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_045

/-! Last-update return-buffer allocation and the shared dynamic return decoder. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option maxRecDepth 2000

theorem lastUpdatePostCall {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {out : ByteArray} {σ : AccountMap}
    {k C : Nat} {ptr : UInt256} {R : List UInt256}
    {frame : Frame} {evm evm' : State} {morpho : AccountAddress} {slot : UInt256} {ok : Bool}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 14 ≤ 1024)
    (hlo : 96 ≤ ptr.toNat) (hmem : ptr.toNat ≤ mem.size)
    (hlookup : lookupCallable? frame.contract allocateFunction.name =
      some allocateFunction.toCallable)
    (hcall : typedCallViaEVM config evm morpho "extSloads" 0 [.array [wordBytes32Value slot]]
      (ok, evm', out) false)
    (rd : RD (deployedRuntime v) I g s0 ⟨9112⟩
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
        ∃ aw' k' C', RD (deployedRuntime v) I g s0 ⟨9447⟩
          (nextCursor ptr (UInt256.ofNat out.size) :: ⟨9144⟩ ::
            UInt256.ofNat (2 ^ 128 - 1) :: R)
          (extSloadsDecodedMem (extSloadsBufferMem mem ptr out)
            (nextCursor ptr (UInt256.ofNat out.size)) out) aw' out σ k' C') := by
  have hout := extSloadsReturnSize hcall
  have hword : out.size < UInt256.size := by change _ < 2 ^ 256; omega
  cases ok with
  | false =>
      have hfail := metaMorphoV1_1_block_9112_taken (immWords := wordsOf (immStore v))
        (by omega) (by decide)
        (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
      exact .inl ⟨extSloadsBodyCallReverts ptr morpho _ out hcall,
        metaMorphoV1_1_block_2921 (immWords := wordsOf (immStore v))
          (by simp only [metaMorphoV1_1_block_9112_taken_stack, List.length_cons]; omega)
          (by change 0 + (UInt256.ofNat out.size).toNat ≤ out.size
              rw [UInt256.toNat_ofNat_of_lt hword, Nat.zero_add]) hfail⟩
  | true =>
      have r1 := metaMorphoV1_1_block_9112_fallthrough (immWords := wordsOf (immStore v))
        (by omega) (by decide) rd
      have r2 := metaMorphoV1_1_block_9119_taken (immWords := wordsOf (immStore v))
        (by omega) (by decide)
        (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) r1
      have r3 := metaMorphoV1_1_block_9419 (immWords := wordsOf (immStore v))
        (by simp only [List.length_cons]; omega)
        (by change 0 + (UInt256.ofNat out.size).toNat ≤ out.size
            rw [UInt256.toNat_ofNat_of_lt hword, Nat.zero_add])
        (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) r2
      have hmask : UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128))
          (UInt256.ofNat 1) = UInt256.ofNat (2 ^ 128 - 1) := by decide +kernel
      simp only [metaMorphoV1_1_block_9419_stack, metaMorphoV1_1_block_9419_memory,
        hmask, show (⟨0⟩ : UInt256).toNat = 0 from rfl,
        UInt256.toNat_ofNat_of_lt hword] at r3
      by_cases hfit : allocationFits ptr (UInt256.ofNat out.size)
      · obtain ⟨aw4, k4, C4, r4⟩ := allocateRoundedReturn v
          (by simp only [List.length_cons]; omega) hfit
          (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) r3
        have r5 := metaMorphoV1_1_block_9439 (immWords := wordsOf (immStore v))
          (by simp only [List.length_cons]; omega)
          (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) r4
        rcases extSloadsAfterBufferSimulation v (by simp only [List.length_cons]; omega)
            hlo hmem hlookup hcall hfit
            (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) r5 with
          ⟨hsource, hrev⟩ | ⟨hc, ha, hsource, hreturn⟩
        · exact .inl ⟨hsource, hrev⟩
        · exact .inr ⟨rfl, hc, hfit, ha, hsource, hreturn⟩
      · exact .inl ⟨extSloadsBodyBufferReverts ptr morpho _ out hlookup hcall hword hfit,
          allocateRoundedRevert v (by simp only [List.length_cons]; omega) hfit r3⟩

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
