import Benchmarks.Dss.GemJoin.ConstructorTraceCall

/-!
# MakerDAO/Sky DSS GemJoin constructor return trace
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Dss.GemJoin

set_option maxRecDepth 2000000

set_option maxHeartbeats 1000000 in
theorem gemJoinCtorReturnTrace
    {I : ExecutionEnv} {g : Sat256} {s0 : State} {mem rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {k C : Nat}
    (vat : AccountAddress) (ilk dec : UInt256) (gem : AccountAddress)
    (hperm : I.perm = true)
    (hMload64Value :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨64⟩ : UInt256) ≥ (UInt256.ofNat 8) * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨224⟩)
    (h : RD (gemJoinCtorCode vat ilk gem) I g s0 ⟨241⟩
      [dec, EVM.word gem.val, ilk, EVM.word vat.val]
      mem (UInt256.ofNat 8) rdata (cA, σ) k C) :
    RDret (gemJoinCtorCode vat ilk gem) g s0
      (cA, sstoreAccountMap I.codeOwner σ ⟨4⟩ dec) gemJoinBytecode := by
  have rd243 := gem_ctor_run h with [push1 ⟨4⟩]
  obtain ⟨_, _, rd244⟩ := rd243.sstore hperm (by gem_ctor_decode)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd249pre := gem_ctor_run rd244 with [
    push1 ⟨64⟩,
    raw mload 0 ⟨224⟩ (UInt256.ofNat 8) (by gem_ctor_decode) mem_cost
      hMload64Value (by decide +native) (by evm_ov),
    caller, swap1]
  have rd282 := rd249pre.pushConst
    (⟨0xdd0e34038ac38b2a1ce960229778ac48a8719bc900b6c4f8d0475c6e8b385a60⟩ : UInt256)
    (width := 32) (op := .PUSH32) (by decide) (by gem_ctor_decode) (by evm_ov)
  have rd286 := gem_ctor_run rd282 with [swap1, push1 ⟨0⟩, swap1]
  have rd287raw := RD.log2 0 (UInt256.ofNat 8) rd286
    (by gem_ctor_decode) hperm mem_cost (by decide +native)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd290 := gem_ctor_run rd287raw with [pop, pop, pop]
  let retMem := gemJoinCtorRuntimeReturnMem vat ilk gem mem
  have hcopy :
      (gemJoinCtorCode vat ilk gem).write 304 mem 0 2022 = retMem := by
    rfl
  have rd300 := gem_ctor_run rd290 with [
    push2 ⟨2022⟩, dup1, push2 ⟨304⟩, push1 ⟨0⟩,
    raw codecopy
      (Cₘ (UInt256.ofNat (MachineState.M (UInt256.ofNat 8).toNat 0 2022)) -
        Cₘ (UInt256.ofNat 8))
      retMem (UInt256.ofNat (MachineState.M (UInt256.ofNat 8).toNat 0 2022))
      (by gem_ctor_decode) mem_cost hcopy (by decide +native) (by evm_ov),
    push1 ⟨0⟩]
  exact rd300.ret 0 gemJoinBytecode
    (by gem_ctor_decode) mem_cost
    (by simpa [retMem] using gemJoinCtorRuntimeReturnMem_read vat ilk gem mem)
    (by evm_ov)

end Benchmarks.Dss.GemJoin
