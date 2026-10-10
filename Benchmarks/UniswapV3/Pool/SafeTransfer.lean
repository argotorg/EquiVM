import Benchmarks.UniswapV3.Pool.SafeTransferBuild
import Benchmarks.UniswapV3.Pool.SafeTransferCopy

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def safeTransferInputMem (mem : ByteArray) (p : UInt256) (recipient : AccountAddress)
    (value : UInt256) : ByteArray :=
  transferCopyMem3 (safeTransferBuildMem mem p (EVM.word recipient.val) value) p

theorem safeTransferPrepareX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw p value ret : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables} (token recipient : AccountAddress)
    (rd : RD (deployedRuntime v) ee g s0 ⟨15238⟩
      (value :: EVM.word recipient.val :: EVM.word token.val :: ret :: R) mem aw rdata σ k C)
    (hm : HeapMemory mem aw p) (hb : p.toNat + 196 ≤ 2 ^ 200) (hov : R.length + 20 ≤ 1024) :
    ∃ gasArg aw' k' C', RD (deployedRuntime v) ee g s0 ⟨15413⟩
      (gasArg :: EVM.word token.val :: ⟨0⟩ :: (p + ⟨100⟩) :: ⟨68⟩ :: (p + ⟨100⟩) :: ⟨0⟩ ::
        (UInt256.ofNat 68 + (p + ⟨100⟩)) :: EVM.word token.val :: ⟨0⟩ :: ⟨0⟩ ::
        value :: EVM.word recipient.val :: EVM.word token.val :: ret :: R)
      (safeTransferInputMem mem p recipient value) aw' rdata σ k' C' ∧
      HeapMemory (safeTransferInputMem mem p recipient value) aw' (p + ⟨100⟩) := by
  obtain ⟨awBuild, kBuild, CBuild, rdBuild, hmBuild⟩ :=
    safeTransferBuildX (v := v) recipient rd hm (by omega) (by evm_ov)
  have rdCopy := uniswapV3Pool_block_15319 (immWords := wordsOf (immStore v)) (by evm_ov) rdBuild
  simp only [uniswapV3Pool_block_15319_stack, addressWord_val_clean] at rdCopy
  exact transferCopyX (v := v) rdCopy hmBuild hb (by evm_ov)

theorem safeTransferInputMem_size (mem : ByteArray) (p : UInt256) (recipient : AccountAddress)
    (value : UInt256) (hp : 128 ≤ p.toNat) :
    (safeTransferInputMem mem p recipient value).size = max mem.size (p.toNat + 196) := by
  rw [safeTransferInputMem, transferCopyMem3_size, safeTransferBuildMem_size _ _ _ _ hp]
  omega

theorem safeTransferInputMem_prefix (mem : ByteArray) (p : UInt256) (recipient : AccountAddress)
    (value : UInt256) : MemoryPrefix mem (safeTransferInputMem mem p recipient value) p.toNat :=
  (safeTransferBuildMem_prefix mem p (EVM.word recipient.val) value).trans
    ((transferCopyMem3_prefix _ p).mono (by omega))

theorem safeTransferInputMem_calldata {mem : ByteArray} {aw p : UInt256}
    (hm : HeapMemory mem aw p) (recipient : AccountAddress) (value : UInt256)
    (hbound : p.toNat + 196 < UInt256.size) :
    (safeTransferInputMem mem p recipient value).readWithPadding (p.toNat + 100) 68 =
      safeTransferCalldata recipient value := by
  rw [safeTransferInputMem, transferCopyMem3_read _ p
    (by rw [safeTransferBuildMem_size _ _ _ _ hm.lower]; omega) hbound]
  exact safeTransferBuildMem_calldata hm recipient value (by omega)

theorem safeTransferInputMem_zero {mem : ByteArray} {aw p : UInt256}
    (hm : HeapMemory mem aw p) (recipient : AccountAddress) (value : UInt256)
    (hmem : 128 ≤ mem.size) (hzero : memLoad (UInt256.ofNat 96) mem = ⟨0⟩) :
    memLoad (UInt256.ofNat 96) (safeTransferInputMem mem p recipient value) = ⟨0⟩ := by
  have hpref := safeTransferInputMem_prefix mem p recipient value
  rw [MemoryPrefix.memLoad hpref (UInt256.ofNat 96) (by decide)
    (by change 128 ≤ p.toNat; exact hm.lower) (by exact hmem), hzero]

theorem safeTransferInputMem_bounds {mem : ByteArray} {aw p : UInt256}
    (hm : HeapMemory mem aw p) (recipient : AccountAddress) (value : UInt256)
    (hb : p.toNat + 2 ^ 138 + 195 ≤ 2 ^ 200) :
    (p + (⟨100⟩ : UInt256)).toNat + 32 ≤ (safeTransferInputMem mem p recipient value).size ∧
    (p + (⟨100⟩ : UInt256)).toNat + 2 ^ 138 + 95 ≤ 2 ^ 200 ∧
    (p + (⟨100⟩ : UInt256)).toNat + 68 ≤ 2 ^ 200 := by
  have hp100 : (p + (⟨100⟩ : UInt256)).toNat = p.toNat + 100 :=
    uadd_word_ofNat_toNat p 100 (by change _ < 2 ^ 256; omega)
  rw [hp100, safeTransferInputMem_size _ _ _ _ hm.lower]
  omega

theorem safeTransferInputMem_read {mem : ByteArray} {aw p : UInt256}
    (hm : HeapMemory mem aw p) (recipient : AccountAddress) (value : UInt256)
    (hb : p.toNat + 2 ^ 138 + 195 ≤ 2 ^ 200) :
    (safeTransferInputMem mem p recipient value).readWithPadding
      (p + (⟨100⟩ : UInt256)).toNat 68 = safeTransferCalldata recipient value := by
  have hp100 : (p + (⟨100⟩ : UInt256)).toNat = p.toNat + 100 :=
    uadd_word_ofNat_toNat p 100 (by change _ < 2 ^ 256; omega)
  rw [hp100]
  exact safeTransferInputMem_calldata hm recipient value (by change _ < 2 ^ 256; omega)

theorem safeTransferEntryCallGrowingX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 evm : EVM.State} {k C : Nat} {aw p value ret : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables} (imms : Store)
    (token recipient : AccountAddress)
    (rd : RD (deployedRuntime v) ee g s0 ⟨15238⟩
      (value :: EVM.word recipient.val :: EVM.word token.val :: ret :: R) mem aw rdata σ k C)
    (hs : SourceState s0 ee σ evm) (hperm : ee.perm = true)
    (hm : HeapMemory mem aw p) (hmem : 128 ≤ mem.size)
    (hzero : memLoad (UInt256.ofNat 96) mem = ⟨0⟩)
    (hb : p.toNat + 2 ^ 138 + 195 ≤ 2 ^ 200)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true) (hov : R.length + 20 ≤ 1024) :
    (RDrev (deployedRuntime v) g s0 ∧
      ExecFuncBody config (safeTransferFrame imms token recipient value) evm
        safeTransferFunction.body .reverted) ∨
    ∃ evm' σ' out mem' aw' next k' C', SourceState s0 ee σ' evm' ∧
      ExecFuncBody config (safeTransferFrame imms token recipient value) evm
        safeTransferFunction.body
        (.returned (safeTransferCallFrame imms token recipient value true out) evm' none) ∧
      RD (deployedRuntime v) ee g s0 ret R mem' aw' out σ' k' C' ∧
      HeapMemory mem' aw' next ∧
      MemoryPrefix (safeTransferInputMem mem p recipient value) mem' (p + ⟨100⟩).toNat ∧
      (p + ⟨100⟩).toNat ≤ next.toNat ∧
      next.toNat ≤ (p + ⟨100⟩).toNat + 2 ^ 138 + 63 := by
  obtain ⟨gasArg, awCall, kCall, CCall, rdCall, hmCall⟩ :=
    safeTransferPrepareX (v := v) token recipient rd hm (by omega) hov
  have hbounds := safeTransferInputMem_bounds hm recipient value hb
  have hz := safeTransferInputMem_zero hm recipient value hmem hzero
  have hcd := safeTransferInputMem_read hm recipient value hb
  generalize hmc : safeTransferInputMem mem p recipient value = mc at rdCall hmCall hbounds hz hcd ⊢
  exact safeTransferCallGrowingX (v := v) imms token recipient value rdCall hs hperm hcd
    hmCall hbounds.1 hz hbounds.2.1 hbounds.2.2 hret (by omega)

theorem safeTransferEntryCallX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 evm : EVM.State} {k C : Nat} {aw p value ret : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables} (imms : Store)
    (token recipient : AccountAddress)
    (rd : RD (deployedRuntime v) ee g s0 ⟨15238⟩
      (value :: EVM.word recipient.val :: EVM.word token.val :: ret :: R) mem aw rdata σ k C)
    (hs : SourceState s0 ee σ evm) (hperm : ee.perm = true)
    (hm : HeapMemory mem aw p) (hmem : 128 ≤ mem.size)
    (hzero : memLoad (UInt256.ofNat 96) mem = ⟨0⟩)
    (hb : p.toNat + 2 ^ 138 + 195 ≤ 2 ^ 200)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true) (hov : R.length + 20 ≤ 1024) :
    (RDrev (deployedRuntime v) g s0 ∧
      ExecFuncBody config (safeTransferFrame imms token recipient value) evm
        safeTransferFunction.body .reverted) ∨
    ∃ evm' σ' out mem' aw' next k' C', SourceState s0 ee σ' evm' ∧
      ExecFuncBody config (safeTransferFrame imms token recipient value) evm
        safeTransferFunction.body
        (.returned (safeTransferCallFrame imms token recipient value true out) evm' none) ∧
      RD (deployedRuntime v) ee g s0 ret R mem' aw' out σ' k' C' ∧
      HeapMemory mem' aw' next ∧
      MemoryPrefix (safeTransferInputMem mem p recipient value) mem' (p + ⟨100⟩).toNat ∧
      next.toNat ≤ (p + ⟨100⟩).toNat + 2 ^ 138 + 63 := by
  rcases safeTransferEntryCallGrowingX (v := v) imms token recipient rd hs hperm hm
      hmem hzero hb hret hov with
    hbad | ⟨evm', σ', out, mem', aw', next, k', C', hs', hbody, rr, hm', hpref, _, hnext⟩
  · exact Or.inl hbad
  · exact Or.inr ⟨evm', σ', out, mem', aw', next, k', C', hs', hbody, rr, hm', hpref, hnext⟩

theorem safeTransferInputMem_result {mem mem' : ByteArray} {p next : UInt256}
    (recipient : AccountAddress) (value : UInt256)
    (hb : p.toNat + 2 ^ 138 + 195 ≤ 2 ^ 200)
    (hpref : MemoryPrefix (safeTransferInputMem mem p recipient value) mem' (p + ⟨100⟩).toNat)
    (hnext : next.toNat ≤ (p + ⟨100⟩).toNat + 2 ^ 138 + 63) :
    MemoryPrefix mem mem' p.toNat ∧ next.toNat ≤ p.toNat + 2 ^ 138 + 163 := by
  have hp100 : (p + (⟨100⟩ : UInt256)).toNat = p.toNat + 100 :=
    uadd_word_ofNat_toNat p 100 (by change _ < 2 ^ 256; omega)
  exact ⟨(safeTransferInputMem_prefix mem p recipient value).trans
    (hpref.mono (by rw [hp100]; omega)), by
      simpa only [hp100, Nat.add_right_comm p.toNat 100 (2 ^ 138), Nat.add_assoc] using hnext⟩

theorem safeTransferGrowingX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 evm : EVM.State} {k C : Nat} {aw p value ret : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables} (imms : Store)
    (token recipient : AccountAddress)
    (rd : RD (deployedRuntime v) ee g s0 ⟨15238⟩
      (value :: EVM.word recipient.val :: EVM.word token.val :: ret :: R) mem aw rdata σ k C)
    (hs : SourceState s0 ee σ evm) (hperm : ee.perm = true)
    (hm : HeapMemory mem aw p) (hmem : 128 ≤ mem.size)
    (hzero : memLoad (UInt256.ofNat 96) mem = ⟨0⟩)
    (hb : p.toNat + 2 ^ 138 + 195 ≤ 2 ^ 200)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true) (hov : R.length + 20 ≤ 1024) :
    (RDrev (deployedRuntime v) g s0 ∧
      ExecFuncBody config (safeTransferFrame imms token recipient value) evm
        safeTransferFunction.body .reverted) ∨
    ∃ evm' σ' out mem' aw' next k' C', SourceState s0 ee σ' evm' ∧
      ExecFuncBody config (safeTransferFrame imms token recipient value) evm
        safeTransferFunction.body
        (.returned (safeTransferCallFrame imms token recipient value true out) evm' none) ∧
      RD (deployedRuntime v) ee g s0 ret R mem' aw' out σ' k' C' ∧
      HeapMemory mem' aw' next ∧ MemoryPrefix mem mem' p.toNat ∧
      p.toNat ≤ next.toNat ∧ next.toNat ≤ p.toNat + 2 ^ 138 + 163 := by
  rcases safeTransferEntryCallGrowingX (v := v) imms token recipient rd hs hperm hm hmem hzero hb
    hret hov with
    hbad | ⟨evm', σ', out, mem', aw', next, k', C', hs', hbody, rdDone, hm', hpref', hmono, hnext⟩
  · exact Or.inl hbad
  · obtain ⟨hpref, hbound⟩ := safeTransferInputMem_result recipient value hb hpref' hnext
    refine Or.inr ⟨evm', σ', out, mem', aw', next, k', C', hs', hbody, rdDone, hm', hpref, ?_,
      hbound⟩
    have hp100 : (p + (⟨100⟩ : UInt256)).toNat = p.toNat + 100 :=
      uadd_word_ofNat_toNat p 100 (by change _ < 2 ^ 256; omega)
    omega

theorem safeTransferX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 evm : EVM.State} {k C : Nat} {aw p value ret : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables} (imms : Store)
    (token recipient : AccountAddress)
    (rd : RD (deployedRuntime v) ee g s0 ⟨15238⟩
      (value :: EVM.word recipient.val :: EVM.word token.val :: ret :: R) mem aw rdata σ k C)
    (hs : SourceState s0 ee σ evm) (hperm : ee.perm = true)
    (hm : HeapMemory mem aw p) (hmem : 128 ≤ mem.size)
    (hzero : memLoad (UInt256.ofNat 96) mem = ⟨0⟩)
    (hb : p.toNat + 2 ^ 138 + 195 ≤ 2 ^ 200)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true) (hov : R.length + 20 ≤ 1024) :
    (RDrev (deployedRuntime v) g s0 ∧
      ExecFuncBody config (safeTransferFrame imms token recipient value) evm
        safeTransferFunction.body .reverted) ∨
    ∃ evm' σ' out mem' aw' next k' C', SourceState s0 ee σ' evm' ∧
      ExecFuncBody config (safeTransferFrame imms token recipient value) evm
        safeTransferFunction.body
        (.returned (safeTransferCallFrame imms token recipient value true out) evm' none) ∧
      RD (deployedRuntime v) ee g s0 ret R mem' aw' out σ' k' C' ∧
      HeapMemory mem' aw' next ∧ MemoryPrefix mem mem' p.toNat ∧
      next.toNat ≤ p.toNat + 2 ^ 138 + 163 := by
  rcases safeTransferGrowingX (v := v) imms token recipient rd hs hperm hm hmem hzero
      hb hret hov with
    hbad | ⟨evm', σ', out, mem', aw', next, k', C', hs', hbody, rr, hm', hpref, _, hnext⟩
  · exact Or.inl hbad
  · exact Or.inr ⟨evm', σ', out, mem', aw', next, k', C', hs', hbody, rr, hm', hpref, hnext⟩

end Benchmarks.UniswapV3.Pool
