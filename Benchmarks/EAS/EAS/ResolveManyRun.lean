import Benchmarks.EAS.EAS.ResolveManyPrefix
import Benchmarks.EAS.EAS.ResolveManySingleRun
import Benchmarks.EAS.EAS.ResolveManyZeroRun
import Benchmarks.EAS.EAS.ResolveManyTailRun
import Benchmarks.EAS.EAS.HeapBranch

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

def resolveManyUsedValue (target : AccountAddress) (words : List UInt256) : UInt256 :=
  if target=EVM.address 0 then ⟨0⟩ else resolveManyTotal words words.length

theorem resolveManyUsedValue_single (target : AccountAddress) (value : UInt256) :
    resolveManyUsedValue target [value] = resolveOneUsedValue target value := by
  simp only [resolveManyUsedValue,resolveManyTotal,List.take_length,
    List.foldl_cons,List.foldl_nil,u256_zero_add,resolveOneUsedValue]

theorem resolveManyRun {imms : Store} {ee : ExecutionEnv} {g : Sat256} {s0 evm : EVM.State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {schema array values available ptr ret : UInt256} {R : List UInt256}
    {record : Value} {ats : List AttestationRecord} {words : List UInt256} {target : AccountAddress} {rev last : Bool}
    (v : EASImmutables) (hfield : lookupField? record "resolver" = some (.address target))
    (ht : UInt256.land (memLoad (schema+UInt256.ofNat 32) mem) solcAddrMask = UInt256.ofNat target.val)
    (hstack : R.length+36 ≤ 1024) (hperm : ee.perm = true ∨ ats = []) (hs : SourceState s0 ee σ evm)
    (harray : AttestationArrayMemoryView mem array ats ptr.toNat)
    (hvalues : WordArrayMemoryView mem values words ptr.toNat) (hlen : ats.length = words.length)
    (hheap : ptr.toNat ≤ 2^64-1) (hh : memLoad (UInt256.ofNat 64) mem = ptr)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD fork (deployedRuntime v) ee g s0 (resolveManyEntryPC rev)
      (schema::array::values::available::last.toUInt256::ret::R) mem aw rdata σ k C) :
    HeapReturnPostOrStatic fork ((resolveManyUsedValue target words).toNat ≤ available.toNat) config (deployedRuntime v) ee g s0
      {contract := contract, locals := resolveManyArgs record ats words rev available last ptr.toNat, immutables := imms}
      evm resolveManyFunction.body (.int (Int.ofNat (resolveManyUsedValue target words).toNat))
      ret (resolveManyUsedValue target words::R) mem ptr.toNat := by
  have hfit : ats.length < UInt256.size := by change ats.length < 2^256; have := harray.span; omega
  obtain ⟨a1,k1,C1,r1⟩ := resolveManyStart v rev (by simp only [List.length_cons]; omega) hfit harray.length rd
  by_cases hone : ats.length=1
  · rw [if_pos hone] at r1
    obtain ⟨a,rfl⟩ := List.length_eq_one_iff.mp hone
    have hwlen : words.length=1 := by simpa only [List.length_cons,List.length_nil] using hlen.symm
    obtain ⟨value,rfl⟩ := List.length_eq_one_iff.mp hwlen
    rw [resolveManyUsedValue_single]
    have hlength := resolveManyLengthSource (fork := fork) (cfg := config) (imms := imms) (evm := evm) (ats := [a])
      (locals := resolveManyArgs record [a] [value] rev available last ptr.toNat)
      (by simp (disch := decide) only [resolveManyArgs,store_get_self,store_get_ne])
    let L := resolveManyLengthLocals record [a] [value] rev available last ptr.toNat
    have he := resolveManySingleArgsSource (locals := L) (imms := imms) (evm := evm)
      (record := record) (a := a) (value := value) (available := available) (rev := rev) (last := last) (heap := ptr.toNat)
      (by simp (disch := decide) only [L,resolveManyLengthLocals,resolveManyArgs,store_get_self,store_get_ne])
      (by simp (disch := decide) only [L,resolveManyLengthLocals,resolveManyArgs,store_get_self,store_get_ne,List.map_cons,List.map_nil])
      (by simp (disch := decide) only [L,resolveManyLengthLocals,resolveManyArgs,store_get_self,store_get_ne,List.map_cons,List.map_nil])
      (by simp (disch := decide) only [L,resolveManyLengthLocals,resolveManyArgs,store_get_self,store_get_ne])
      (by simp (disch := decide) only [L,resolveManyLengthLocals,resolveManyArgs,store_get_self,store_get_ne])
      (by simp (disch := decide) only [L,resolveManyLengthLocals,resolveManyArgs,store_get_self,store_get_ne])
      (by simp (disch := decide) only [L,resolveManyLengthLocals,resolveManyArgs,store_get_self,store_get_ne])
    have hperm' : ee.perm = true := hperm.resolve_right (by simp)
    have hrun := resolveManySingleRun v he
      (by simp (disch := decide) only [L,resolveManyLengthLocals,resolveManyArgs,store_get_self,store_get_ne])
      hfield ht (by omega) hperm' hs harray hvalues hheap hh hret r1
    have hg : evalExpr? config {contract := contract, locals := L, immutables := imms} evm
        (.binary .eq (.var "length") (.intLit 1)) = .ok (.bool true) := by
      simpa only [decide_true] using resolveManySingleGuardSource (cfg := config) (imms := imms) (evm := evm)
        (len := 1) (show L.get? "length" = some (.int (Int.ofNat 1)) from store_get_self _ _ _)
    rw [resolveMany_body]
    exact Or.inl ((hrun.iteTrue (elseB := []) (suffix := [resolveManyResolverInit,resolveManyZero] ++ resolveManySuffix) hg).prepend (front := [resolveManyLength])
      hlength (MemoryPrefix.refl _ _) (le_refl _))
  · rw [if_neg hone] at r1
    have hprefix := resolveManyHeadSource (fork := fork) (imms := imms) (evm := evm) record ats words target rev available last ptr.toNat hfield hone
    obtain ⟨a2,k2,C2,r2⟩ := resolveManyLoad v rev (by simp only [List.length_cons]; omega) ht r1
    have he := resolveOneZeroExpr_eval (cfg := config) (evm := evm)
      (frame := {contract := contract, locals := resolveManyHeadLocals record ats words target rev available last ptr.toNat, immutables := imms})
      (target := target) (store_get_self _ _ _)
    have hziff : UInt256.ofNat target.val=⟨0⟩ ↔ target=EVM.address 0 := by
      have h := accountAddress_ofNat_zero_iff (word_val_addr_canonical target)
      rw [accountAddress_of_word_val] at h
      exact h.symm
    by_cases hz : target=EVM.address 0
    · rw [if_pos (hziff.mpr hz)] at r2
      obtain ⟨a3,k3,C3,r3⟩ := resolveManyInitZero v rev (by simp only [List.length_cons]; omega) r2
      rw [hlen] at r3
      have hrun := resolveManyZeroRun (imms := imms)
        (locals := resolveManyHeadLocals record ats words target rev available last ptr.toNat) v rev
        (by simp (disch := decide) only [resolveManyHeadLocals,resolveManyLengthLocals,resolveManyArgs,store_get_self,store_get_ne])
        (by simp (disch := decide) only [resolveManyHeadLocals,resolveManyLengthLocals,store_get_self,store_get_ne,hlen])
        (by simp (disch := decide) only [resolveManyHeadLocals,resolveManyLengthLocals,resolveManyArgs,store_get_self,store_get_ne])
        (by omega) hs hvalues hheap (by simpa only [u256_ofNat_toNat] using hh) hret r3
      have hrun := hrun.withPost (show (⟨0⟩ : UInt256).toNat ≤ available.toNat from Nat.zero_le _)
      rw [resolveMany_body,resolveManyUsedValue,if_pos hz]
      exact Or.inl ((hrun.iteTrue (elseB := []) (suffix := resolveManySuffix) (by simpa only [decide_eq_true hz] using he)).prepend (front := [resolveManyLength,resolveManySingle,resolveManyResolverInit])
        hprefix (MemoryPrefix.refl _ _) (le_refl _))
    · rw [if_neg (fun h => hz (hziff.mp h))] at r2
      obtain ⟨a3,k3,C3,r3⟩ := resolveManyInitLoop v rev (by simp only [List.length_cons]; omega) r2
      rw [hlen] at r3
      have hf := resolveManyLoopLocals_facts record ats words target rev available last ptr.toNat hlen
      have hperm' : ee.perm = true ∨ words = [] := by
        rcases hperm with hp | ha
        · exact Or.inl hp
        · exact Or.inr (by simpa only [ha,List.length_nil,List.length_eq_zero_iff] using hlen.symm)
      have hrun := resolveManyTailRun (imms := imms) v hf hstack hperm' hs harray hvalues hheap hh hret r3
      have hinit : ExecBlock fork config
          {contract := contract, locals := resolveManyHeadLocals record ats words target rev available last ptr.toNat, immutables := imms}
          evm [resolveManyZero,resolveManyTotalInit,resolveManyIndexInit]
          (.ok {contract := contract, locals := resolveManyLoopLocals record ats words target rev available last ptr.toNat, immutables := imms} evm) := by
        apply ExecBlock.consNormal (ExecStmt.iteFalse (by simpa only [decide_eq_false hz] using he) ExecBlock.nil)
        exact ExecBlock.consNormal (ExecStmt.letDecl (by simp only [evalExpr?]; rfl))
          (ExecBlock.consNormal (ExecStmt.letDecl (by simp only [evalExpr?]; rfl)) ExecBlock.nil)
      rw [resolveMany_body,resolveManyUsedValue,if_neg hz]
      exact (hrun.prepend hinit (MemoryPrefix.refl _ _) (le_refl _)).prepend (front := [resolveManyLength,resolveManySingle,resolveManyResolverInit])
        hprefix (MemoryPrefix.refl _ _) (le_refl _)

end Benchmarks.EAS.EAS
