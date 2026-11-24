import Benchmarks.EAS.EAS.MultiDelegatedAttestAccess
import Benchmarks.EAS.EAS.CalldataAddress6240
import Benchmarks.EAS.EAS.MultiAttestControl
import Benchmarks.EAS.EAS.RuntimeBlocks_013

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

def multiDelegatedAttestSaved (n i : Nat) (base table available count : UInt256) (R : List UInt256) : List UInt256 :=
  [⟨3140⟩,⟨32⟩,count,⟨1⟩,UInt256.ofNat n,base,available,UInt256.ofNat n-⟨1⟩,table,UInt256.ofNat i]++R

def multiDelegatedAttestCopySaved (cd : ByteArray) (root : UInt256) (n i : Nat) (base table available count : UInt256) (R : List UInt256) : List UInt256 :=
  calldataWord cd root.toNat::calldataWord cd (root+UInt256.ofNat 96).toNat::available::multiAttestLastWord n i::⟨3131⟩::
    multiDelegatedAttestSaved n i base table available count R

theorem easMultiDelegatedAttestVerifyDone {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {out : ByteArray} {σ : AccountMap} {k C n i : Nat}
    {root base table available count : UInt256} {R : List UInt256}
    (v : EASImmutables) (hstack : R.length+23≤1024) (ha : delegatedBatchAddressClean ee.calldata root)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨2874⟩
      (multiDelegatedAttestVerifyStack ee.calldata (delegatedAttestationDataLength ee.calldata root).toNat root
        (delegatedAttestationDataOffset ee.calldata root) base (UInt256.ofNat n)
        (delegatedAttestationDataLength ee.calldata root) available table count (UInt256.ofNat i) (UInt256.ofNat n-⟨1⟩) R)
      mem aw out σ k C) :
    ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 ⟨5544⟩
      (delegatedAttestationDataOffset ee.calldata root::delegatedAttestationDataLength ee.calldata root::UInt256.ofNat ee.calldata.size::⟨3125⟩::
        multiDelegatedAttestCopySaved ee.calldata root n i base table available count R) mem aw' out σ k' C' := by
  simp only [multiDelegatedAttestVerifyStack,multiDelegatedAttestVerifyTail,List.cons_append,List.nil_append,u256_ofNat_toNat] at rd
  obtain ⟨a1,k1,C1,r1⟩ := easBlocks.eas_block_2874_taken_packed (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons];omega) (by rw [ult_zero (le_refl _)];decide)
    (by rw [easPatchedValidJumpsRuntime v];jump_dest) rd
  obtain ⟨a2,k2,C2,r2⟩ := easBlocks.eas_block_3076_packed (immWords := wordsOf (immStore v))
    (by omega) (by rw [easPatchedValidJumpsRuntime v];jump_dest) r1
  simp only [easBlocks.eas_block_3076_stack] at r2
  have haddr := easCalldataAddress6240 v (by simp only [List.length_cons];omega)
    (by rw [easPatchedValidJumps v];jump_dest) r2
  rw [if_pos (show (calldataWord ee.calldata (root+UInt256.ofNat 96).toNat).toNat<EVM.addressModulus from ha)] at haddr
  obtain ⟨a3,k3,C3,r3⟩ := haddr
  obtain ⟨a4,k4,C4,r4⟩ := easBlocks.eas_block_3117_packed (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons];omega) (by rw [easPatchedValidJumpsRuntime v];jump_dest) r3
  exact ⟨a4,k4,C4,r4⟩

end Benchmarks.EAS.EAS
