import Benchmarks.EAS.EAS.ResolveOnePayment

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

def resolveOneUsedValue (target : AccountAddress) (value : UInt256) : UInt256 :=
  if target = EVM.address 0 then ⟨0⟩ else value

theorem resolveOneRun {imms : Store} {ee : ExecutionEnv} {g : Sat256} {s0 evm : EVM.State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {schemaPtr src dataPtr available value ptr ret : UInt256} {R : List UInt256}
    {record : Value} {a : AttestationRecord} {target : AccountAddress} {rev last : Bool} (v : EASImmutables)
    (hfield : lookupField? record "resolver" = some (.address target))
    (ht : UInt256.land (memLoad (schemaPtr+UInt256.ofNat 32) mem) solcAddrMask = UInt256.ofNat target.val)
    (hstack : R.length+26 ≤ 1024) (hperm : ee.perm = true) (hs : SourceState s0 ee σ evm)
    (hview : AttestationMemoryView mem src dataPtr a)
    (hsrc : src.toNat+320 ≤ ptr.toNat) (hdata : dataPtr.toNat+32+32*((a.data.size+31)/32) ≤ ptr.toNat)
    (hheap : ptr.toNat ≤ 2^64-1) (hh : memLoad (UInt256.ofNat 64) mem = ptr)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨15724⟩
      (schemaPtr::src::value::rev.toUInt256::available::last.toUInt256::ret::R) mem aw rdata σ k C) :
    HeapReturnPost fork ((resolveOneUsedValue target value).toNat ≤ available.toNat) config (deployedRuntime v) ee g s0
      {contract := contract, locals := resolveOneArgs record a value rev available last ptr.toNat, immutables := imms}
      evm resolveOneFunction.body (.int (Int.ofNat (resolveOneUsedValue target value).toNat))
      ret (resolveOneUsedValue target value::R) mem ptr.toNat := by
  have hf := resolveOneLocals_args record a target value available rev last ptr.toNat
  have hfieldEval := resolveOneArgs_field (cfg := config) (imms := imms) (evm := evm)
    record a target value available rev last ptr.toNat hfield
  have hziff : UInt256.ofNat target.val = (⟨0⟩ : UInt256) ↔ target = EVM.address 0 := by
    have h := accountAddress_ofNat_zero_iff (word_val_addr_canonical target)
    rw [accountAddress_of_word_val] at h
    exact h.symm
  obtain ⟨aw1,k1,C1,rd1⟩ := resolveOneStart v (by simp only [List.length_cons]; omega) ht rd
  by_cases hz : target = EVM.address 0
  · rw [if_pos (hziff.mpr hz)] at rd1
    have hr := resolveOneZero v (by omega) hret rd1
    have hsource := resolveOneSource_zero (fork := fork) (cfg := config) (imms := imms)
      (by simpa only [hz] using hfieldEval)
      (by simpa only [store_get_ne _ _ (by decide : ("resolver" == "value") = false)] using hf.value)
      (by simpa only [store_get_ne _ _ (by decide : ("resolver" == "$EAS.freeMemory") = false)] using hf.heap)
    rw [resolveOneUsedValue, if_pos hz]
    refine HeapReturnRun.withPost ?_ (Nat.zero_le _)
    by_cases hv : value = ⟨0⟩
    · rw [if_pos hv] at hr hsource
      obtain ⟨aw2,k2,C2,rd2⟩ := hr
      exact Or.inl ⟨_,evm,σ,mem,rdata,aw2,k2,C2,ptr.toNat,hs,le_refl _,hheap,MemoryPrefix.refl _ _,
        by simpa only [u256_ofNat_toNat] using hh,hsource,rd2⟩
    · rw [if_neg hv] at hr hsource
      exact Or.inr ⟨hsource,hr⟩
  · rw [if_neg (fun he => hz (hziff.mp he))] at rd1
    have hrun := resolveOnePaymentRun (imms := imms) v hf hstack hperm hs hview hsrc hdata hheap hh hret rd1
    rw [resolveOneUsedValue, if_neg hz, resolveOne_body]
    exact hrun.prepend (resolveOnePrefixSource hfieldEval hz) (MemoryPrefix.refl _ _) (le_refl _)

end Benchmarks.EAS.EAS
