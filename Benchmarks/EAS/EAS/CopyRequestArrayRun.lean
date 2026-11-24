import Benchmarks.EAS.EAS.CopyRequestArrayLoop

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

theorem copyRequestArrayRun {L : Store} {evm : EVM.State} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {offset heap ret : UInt256} {rs : List AttestationRequestRecord} {R : List UInt256}
    (v : EASImmutables) (hstack : R.length+23 ≤ 1024)
    (hc : RequestArrayCalldataView ee.calldata offset rs) (hsize : ee.calldata.size < 2^255+4)
    (hd : L.get? "data" = some (.array (rs.map AttestationRequestRecord.tuple)))
    (hf : L.get? "$EAS.freeMemory" = some (.int (Int.ofNat heap.toNat)))
    (hlo : 96 ≤ heap.toNat) (hh : heap.toNat ≤ 2^64-1)
    (hfree : memLoad (UInt256.ofNat 64) mem = heap)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨5544⟩ (offset::UInt256.ofNat rs.length::UInt256.ofNat ee.calldata.size::ret::R) mem aw rdata σ k C) :
    (∃ L' mem' aw' k' C' next,
      heap.toNat ≤ next ∧ next ≤ 2^64-1 ∧ MemoryPrefix mem mem' heap.toNat ∧
      AttestationRequestArrayRegion mem' heap rs heap.toNat next ∧
      memLoad (UInt256.ofNat 64) mem' = UInt256.ofNat next ∧
      ExecFuncBody fork config {contract := contract,locals := L,immutables := immStore v} evm copyRequestArrayFunction.body
        (.returned {contract := contract,locals := L',immutables := immStore v} evm
          (some [.tuple [],.int (Int.ofNat next)])) ∧
      RD fork (deployedRuntime v) ee g s0 ret (heap::R) mem' aw' rdata σ k' C') ∨
    (ExecFuncBody fork config {contract := contract,locals := L,immutables := immStore v} evm copyRequestArrayFunction.body .reverted ∧
      RDrev fork (deployedRuntime v) g s0) := by
  have hb := hc.extent
  have hlenfit : rs.length < UInt256.size := by change _ < 2^256; omega
  have hlen : (UInt256.ofNat rs.length).toNat = rs.length := ulit_toNat' _ hlenfit
  have he : offset+UInt256.shiftLeft (UInt256.ofNat rs.length) (UInt256.ofNat 5) =
      UInt256.ofNat (offset.toNat+32*rs.length) := by
    change offset+UInt256.shiftLeft (UInt256.ofNat rs.length) ⟨5⟩ = _
    rw [shiftLeft5_ofNat_eq (n := rs.length) (by change _ < 2^256; omega)]
    apply u256_inj
    rw [uadd_word_ofNat_toNat _ _ (by change _ < 2^256; omega),ulit_toNat' _ (by change _ < 2^256; omega)]
  have hg : UInt256.gt (offset+UInt256.shiftLeft (UInt256.ofNat rs.length) (UInt256.ofNat 5)) (UInt256.ofNat ee.calldata.size) = ⟨0⟩ := by
    rw [he]
    apply ugt_zero
    rw [ulit_toNat' _ (by change _ < 2^256; omega),ulit_toNat' _ (by change _ < 2^256; omega)]
    exact hb
  have hhead := easCopyRequestArrayHead v (by omega) hfree rd
  have hprefix := copyRequestArrayPrefixSource (fork := fork) (imms := immStore v) (evm := evm) hd hf
  dsimp only at hprefix
  by_cases hv : rs.length ≤ 2^64-1 ∧
      (allocateNext heap.toNat (32+32*rs.length) ≤ 2^64-1 ∧ heap.toNat ≤ allocateNext heap.toNat (32+32*rs.length))
  · have hvhead : requestArrayHeadValid offset (UInt256.ofNat rs.length) (UInt256.ofNat ee.calldata.size) heap := by
      unfold requestArrayHeadValid
      rw [hlen]
      exact ⟨hv.1,hv.2,hg⟩
    obtain ⟨a1,k1,C1,r1⟩ := hhead.1 hvhead
    rw [hlen,he] at r1
    let next := allocateNext heap.toNat (32+32*rs.length)
    let m1 := arrayAllocationHeaderMemory mem heap rs.length
    let L1 := (allocateBlockLocals L next).insert "i" (.int 0)
    have hn : (UInt256.ofNat next).toNat = next := ulit_toNat' _ (by have := hv.2.1; change _ < 2^256; omega)
    have hdptr : heap+UInt256.ofNat 32 = UInt256.ofNat (heap.toNat+32) := by
      apply u256_inj
      rw [uadd_word_ofNat_toNat _ _ (by change _ < 2^256; omega),ulit_toNat' _ (by change _ < 2^256; omega)]
    rw [hdptr] at r1
    have hr1 : RD fork (deployedRuntime v) ee g s0 ⟨5594⟩
        (UInt256.ofNat (heap.toNat+32+32*0)::UInt256.ofNat (offset.toNat+32*0)::offset::
          UInt256.ofNat (offset.toNat+32*rs.length)::UInt256.ofNat ee.calldata.size::ret::heap::R) m1 a1 rdata σ k1 C1 := by
      simpa only [Nat.mul_zero,Nat.add_zero,u256_ofNat_toNat] using r1
    obtain ⟨hp0,hm0,hf0⟩ := copyRequestArrayMemory_init mem heap rs hlo hh hv.1
    have hs0 := hprefix.1 hv
    have hf1 : CopyRequestArrayLocals L1 rs (UInt256.ofNat next).toNat 0 := by rw [hn]; exact hs0.2
    have hm1 : CopyRequestArrayMemory m1 heap rs 0 (UInt256.ofNat next).toNat := by rw [hn]; exact hm0
    have hh1 : (UInt256.ofNat next).toNat ≤ 2^64-1 := by rw [hn]; exact hv.2.1
    rcases copyRequestArrayLoop v hstack hc hsize hret rs.length (by omega) hf1 hm1 hh1 hf0 hr1 with
      ⟨L2,m2,a2,k2,C2,last,hlo2,hhi2,hpre2,hfl,hml,hfree2,hsol2,r2⟩ | ⟨hsol2,hrev⟩
    · rw [hn] at hlo2
      have hreturn : ExecBlock fork config {contract := contract,locals := L2,immutables := immStore v} evm copyRequestReturn
          (.returned {contract := contract,locals := L2,immutables := immStore v} evm (some [.tuple [],.int (Int.ofNat last)])) := by
        apply ExecBlock.consReturn
        apply ExecStmt.return
        simp only [evalExprs?,evalExpr?,evalExprList?,hfl.heap,EvalResult.ofOption,EvalResult.bind,bind,pure]
      have hsol : ExecFuncBody fork config {contract := contract,locals := L,immutables := immStore v} evm copyRequestArrayFunction.body
          (.returned {contract := contract,locals := L2,immutables := immStore v} evm (some [.tuple [],.int (Int.ofNat last)])) := by
        rw [copyRequestArray_body]
        apply ExecFuncBody.execBlockRet
        exact execBlock_append hs0.1 (ExecBlock.consNormal hsol2 hreturn)
      exact Or.inl ⟨L2,m2,a2,k2,C2,last,le_trans hv.2.2 hlo2,hhi2,hp0.trans hpre2,hml,hfree2,hsol,r2⟩
    · refine Or.inr ⟨?_,hrev⟩
      rw [copyRequestArray_body]
      apply ExecFuncBody.execBlockRevert
      exact execBlock_append hs0.1 (ExecBlock.consRevert hsol2)
  · refine Or.inr ⟨?_,hhead.2 ?_⟩
    · rw [copyRequestArray_body]
      apply ExecFuncBody.execBlockRevert
      exact execBlock_append_term (hprefix.2 hv) (by intros; exact nofun)
    · intro h
      apply hv
      have h0 := h.1
      have h1 := h.2.1
      rw [hlen] at h0 h1
      exact ⟨h0,h1⟩

end Benchmarks.EAS.EAS
