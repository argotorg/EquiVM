import Benchmarks.EAS.EAS.CopyRequestArrayStep

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

theorem copyRequestArrayLoop {L : Store} {evm : EVM.State} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {offset array heap ret : UInt256} {rs : List AttestationRequestRecord} {i : Nat} {R : List UInt256}
    (v : EASImmutables) (hstack : R.length+23 ≤ 1024)
    (hc : RequestArrayCalldataView ee.calldata offset rs) (hsize : ee.calldata.size < 2^255+4)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (n : Nat) (hn : i+n = rs.length)
    (hf : CopyRequestArrayLocals L rs heap.toNat i) (hm : CopyRequestArrayMemory mem array rs i heap.toNat)
    (hh : heap.toNat ≤ 2^64-1) (hfree : memLoad (UInt256.ofNat 64) mem = heap)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨5594⟩
      (UInt256.ofNat (array.toNat+32+32*i)::UInt256.ofNat (offset.toNat+32*i)::offset::
        UInt256.ofNat (offset.toNat+32*rs.length)::UInt256.ofNat ee.calldata.size::ret::array::R) mem aw rdata σ k C) :
    (∃ L' mem' aw' k' C' next,
      heap.toNat ≤ next ∧ next ≤ 2^64-1 ∧ MemoryPrefix mem mem' array.toNat ∧
      CopyRequestArrayLocals L' rs next rs.length ∧ AttestationRequestArrayRegion mem' array rs array.toNat next ∧
      memLoad (UInt256.ofNat 64) mem' = UInt256.ofNat next ∧
      ExecStmt fork config {contract := contract,locals := L,immutables := immStore v} evm
        (.while copyRequestArrayGuard copyRequestArrayIteration)
        (.ok {contract := contract,locals := L',immutables := immStore v} evm) ∧
      RD fork (deployedRuntime v) ee g s0 ret (array::R) mem' aw' rdata σ k' C') ∨
    (ExecStmt fork config {contract := contract,locals := L,immutables := immStore v} evm
      (.while copyRequestArrayGuard copyRequestArrayIteration) .reverted ∧ RDrev fork (deployedRuntime v) g s0) := by
  induction n generalizing i L mem aw heap k C with
  | zero =>
    have hi : i = rs.length := by omega
    subst i
    obtain ⟨a1,k1,C1,r1⟩ := easCopyRequestArrayDone v (by omega) hret rd
    have hguard : evalExpr? config {contract := contract,locals := L,immutables := immStore v} evm copyRequestArrayGuard = .ok (.bool false) := by
      simpa only [decide_eq_false (Nat.lt_irrefl rs.length)] using copyRequestArrayGuardSource (imms := immStore v) (evm := evm) hf
    exact Or.inl ⟨L,mem,a1,k1,C1,heap.toNat,le_refl _,hh,MemoryPrefix.refl _ _,hf,hm.finish (le_refl _),
      by simpa only [u256_ofNat_toNat] using hfree,ExecStmt.whileFalse hguard,r1⟩
  | succ n ih =>
    have hi : i < rs.length := by omega
    have hguard : evalExpr? config {contract := contract,locals := L,immutables := immStore v} evm copyRequestArrayGuard = .ok (.bool true) := by
      simpa only [decide_eq_true hi] using copyRequestArrayGuardSource (imms := immStore v) (evm := evm) hf
    rcases copyRequestArrayStep v hstack hf hm hc hi hh hfree hsize rd with
      ⟨L1,m1,a1,k1,C1,next,hlo,hhi,hpre,hf1,hm1,hfree1,hsol1,r1⟩ | ⟨hsol,hrev⟩
    · have hword : (UInt256.ofNat next).toNat = next := ulit_toNat' _ (by change next < 2^256; omega)
      have hf2 : CopyRequestArrayLocals L1 rs (UInt256.ofNat next).toNat (i+1) := by rw [hword]; exact hf1
      have hm2 : CopyRequestArrayMemory m1 array rs (i+1) (UInt256.ofNat next).toNat := by rw [hword]; exact hm1
      have hh2 : (UInt256.ofNat next).toNat ≤ 2^64-1 := by rw [hword]; exact hhi
      rcases ih (by omega) hf2 hm2 hh2 hfree1 r1 with
        ⟨L2,m2,a2,k2,C2,last,hlast,hhfinal,hpre2,hff,hmf,hfreef,hsol2,r2⟩ | ⟨hsol2,hrev⟩
      · rw [hword] at hlast
        exact Or.inl ⟨L2,m2,a2,k2,C2,last,le_trans hlo hlast,hhfinal,hpre.trans hpre2,hff,hmf,hfreef,
          ExecStmt.whileTrue hguard hsol1 hsol2,r2⟩
      · exact Or.inr ⟨ExecStmt.whileTrue hguard hsol1 hsol2,hrev⟩
    · exact Or.inr ⟨ExecStmt.whileRevert hguard hsol,hrev⟩

end Benchmarks.EAS.EAS
