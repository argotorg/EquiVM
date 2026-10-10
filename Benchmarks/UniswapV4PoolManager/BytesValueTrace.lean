import Benchmarks.UniswapV4PoolManager.BytesValueMemory
import Benchmarks.UniswapV4PoolManager.MemoryGas
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_036

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

-- Generalizes the dynamic tail of encodeBytesCallTrace to an arbitrary ABI head.
theorem encodeBytesValueTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw dest src len ret : UInt256} {σ : AccountMap}
    {k C : Nat} {R : List UInt256} (v : PoolManagerImmutables) (hstack : R.length+10 ≤ 1024)
    (hfit : dest.toNat+len.toNat+64 < UInt256.size)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) I g s0 ⟨12396⟩ (src :: len :: dest :: ret :: R) mem aw rdata σ k C) :
    ∃ aw' k' C', (dest.toNat+len.toNat+95)/32 ≤ aw'.toNat ∧
      C+86+3*((len.toNat+31)/32)+Cₘ aw' ≤ C'+Cₘ aw ∧
      RD (deployedRuntime v) I g s0 ret
        (UInt256.ofNat (dest.toNat+32+paddedSize len.toNat) :: R)
        (bytesValueMemory I.calldata mem src.toNat dest.toNat len) aw' rdata σ k' C' := by
  have h32 := uadd_word_ofNat_toNat dest 32 (by omega : dest.toNat+32 < UInt256.size)
  have hlen : (dest+len).toNat = dest.toNat+len.toNat := by
    rw [uadd_toNat, Nat.mod_eq_of_lt (by omega)]
  have hend : ((dest+len)+UInt256.ofNat 32).toNat = dest.toNat+32+len.toNat := by
    rw [uadd_word_ofNat_toNat _ 32 (by rw [hlen]; omega), hlen]; omega
  have hp := paddedSize_le_add31 len.toNat
  have hpad := paddedWord_toNat len (by omega : len.toNat+31 < UInt256.size)
  have hout : (paddedWord len+dest)+UInt256.ofNat 32 = UInt256.ofNat (dest.toNat+32+paddedSize len.toNat) := by
    apply u256_inj
    rw [uadd_toNat, uadd_toNat, hpad,
      Nat.mod_eq_of_lt (by omega : paddedSize len.toNat+dest.toNat < UInt256.size)]
    change (paddedSize len.toNat+dest.toNat+32) % UInt256.size = _
    rw [Nat.mod_eq_of_lt (by omega), UInt256.toNat_ofNat_of_lt (by omega)]
    omega
  have hm : poolManagerBlocks.poolManager_block_12396_memory (ee := I) (mem := mem)
      (x0 := src) (x1 := len) (x2 := dest) = bytesValueMemory I.calldata mem src.toNat dest.toNat len := by
    change writeWord (I.calldata.write src.toNat (writeWord mem dest.toNat len)
      (dest+UInt256.ofNat 32).toNat len.toNat) ((dest+len)+UInt256.ofNat 32).toNat ⟨0⟩ = _
    rw [h32, hend]; rfl
  have hr := poolManagerBlocks.poolManager_block_12396 hstack hret h
  change RD _ _ _ _ ret (((paddedWord len+dest)+UInt256.ofNat 32) :: R) _ _ _ _ _ _ at hr
  rw [hout, hm] at hr
  refine ⟨_, _, _, ?_, ?_, hr⟩
  · have hs := memoryWords_ge_span (M (M aw dest ⟨32⟩) (dest+UInt256.ofNat 32) len)
      ((dest+len)+UInt256.ofNat 32) ⟨32⟩ (by decide)
    rw [hend] at hs
    change (dest.toNat+32+len.toNat+32+31)/32 ≤ _ at hs
    convert hs using 1 <;> congr 1 <;> omega
  · dsimp only [memExpansionCost]
    omega

end Benchmarks.UniswapV4PoolManager
