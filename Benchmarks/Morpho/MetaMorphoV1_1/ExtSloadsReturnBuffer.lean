import Benchmarks.Morpho.MetaMorphoV1_1.ExtSloadsAllocationRoutines
import Benchmarks.Morpho.MetaMorphoV1_1.ExtSloadsDecodeABI
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_046
import Benchmarks.EAS.Attester.ReturnArrayMemory

/-! Return-buffer reservation and the memory view used by the dynamic decoder. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option autoImplicit false

def extSloadsBufferMem (mem : ByteArray) (ptr : UInt256) (out : ByteArray) : ByteArray :=
  writeWord (out.write 0 mem ptr.toNat out.size) 64 (nextCursor ptr (UInt256.ofNat out.size))

theorem nextCursor_returnReserve (ptr : UInt256) (size : Nat) :
    nextCursor ptr (UInt256.ofNat size) = returnReservePtr ptr size := by
  unfold nextCursor roundedSize returnReservePtr returnReserveSize
  rw [u256_land_comm]

theorem extSloadsBufferMem_eq {mem out : ByteArray} {ptr : UInt256}
    (hbound : ptr.toNat + out.size + 31 ≤ 2 ^ 200) :
    extSloadsBufferMem mem ptr out =
      Benchmarks.EAS.Attester.returnArrayInputMemory mem ptr.toNat out := by
  have hcursor : nextCursor ptr (UInt256.ofNat out.size) =
      UInt256.ofNat (Benchmarks.EAS.Attester.returnArrayFree ptr.toNat out) := by
    apply u256_inj
    rw [nextCursor_returnReserve, returnReservePtr_toNat hbound,
      UInt256.toNat_ofNat_of_lt (by
        have hb := (Benchmarks.EAS.Attester.returnArrayFree_bounds ptr.toNat out).2
        change _ < 2 ^ 256
        omega)]
    rfl
  simp only [extSloadsBufferMem, hcursor, Benchmarks.EAS.Attester.returnArrayInputMemory]

theorem extSloadsBufferMem_load {mem out : ByteArray} {ptr : UInt256}
    (hbound : ptr.toNat + out.size + 31 ≤ 2 ^ 200)
    (hlo : 96 ≤ ptr.toNat) (hmem : ptr.toNat ≤ mem.size)
    (off : Nat) (hin : off + 32 ≤ out.size) :
    memLoad (UInt256.ofNat (ptr.toNat + off)) (extSloadsBufferMem mem ptr out) =
      calldataWord out off := by
  rw [extSloadsBufferMem_eq hbound]
  exact Benchmarks.EAS.Attester.returnArrayInputMemory_load hlo hmem hin
    (by change _ < 2 ^ 256; omega)

set_option maxRecDepth 2000 in
theorem extSloadsBufferReturn {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {out : ByteArray} {σ : AccountMap}
    {k C : Nat} {ptr : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 10 ≤ 1024)
    (hout : out.size < UInt256.size)
    (hfit : allocationFits ptr (UInt256.ofNat out.size))
    (rd : RD (deployedRuntime v) I g s0 ⟨14211⟩ (⟨1⟩ :: ptr :: R)
      mem aw out σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) I g s0 ⟨13221⟩
      (ptr :: (ptr + UInt256.ofNat out.size) :: ⟨14256⟩ :: ⟨14232⟩ :: R)
      (extSloadsBufferMem mem ptr out) aw' out σ k' C' := by
  have hbranch := metaMorphoV1_1_block_14211_fallthrough
    (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega)
    (by decide) rd
  have hcopy := metaMorphoV1_1_block_14217_taken
    (immWords := wordsOf (immStore v)) (by omega) (by decide)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) hbranch
  have halloc := metaMorphoV1_1_block_14236
    (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega)
    (by change 0 + (UInt256.ofNat out.size).toNat ≤ out.size
        rw [UInt256.toNat_ofNat_of_lt hout, Nat.zero_add])
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) hcopy
  obtain ⟨aw1, k1, C1, hreserve⟩ := allocateRoundedReturn v
    (by simp only [List.length_cons]; omega) hfit
    (by
      change (D_J (immutableLayout.runtime metaMorphoV1_1Bytecode
        (wordsOf (immStore v))) 0).contains (UInt256.ofNat 9439) = true
      rw [metaMorphoV1_1PatchedValidJumpsRuntime v]
      jump_dest) halloc
  obtain ⟨aw2, k2, C2, hdecode⟩ := metaMorphoV1_1_block_9439_packed
    (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) hreserve
  exact ⟨aw2, k2, C2, by
    simpa only [metaMorphoV1_1_block_9439_stack, metaMorphoV1_1_block_14236_memory,
      show (⟨0⟩ : UInt256).toNat = 0 from rfl, UInt256.toNat_ofNat_of_lt hout,
      extSloadsBufferMem] using hdecode⟩

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
