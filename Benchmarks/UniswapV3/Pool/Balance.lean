import Benchmarks.UniswapV3.Pool.BalanceCopy
import Benchmarks.UniswapV3.Pool.BalanceCall

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def balanceInputMem (mem : ByteArray) (p : UInt256) (who : AccountAddress) : ByteArray :=
  balanceCopyMem2 (balanceBuildMem mem p (EVM.word who.val)) p

theorem balancePrepareX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw p ret : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables} (second : Bool)
    (rd : RD (deployedRuntime v) ee g s0 (balanceEntry second) (ret :: R) mem aw rdata σ k C)
    (hm : HeapMemory mem aw p) (hb : p.toNat + 132 ≤ 2 ^ 200) (hov : R.length + 18 ≤ 1024) :
    ∃ gasArg aw' k' C', RD (deployedRuntime v) ee g s0 ⟨15774⟩
      (gasArg :: EVM.word (balanceToken v second).val :: (p + ⟨68⟩) :: ⟨36⟩ ::
        (p + ⟨68⟩) :: ⟨0⟩ :: (UInt256.ofNat 36 + (p + ⟨68⟩)) ::
        EVM.word (balanceToken v second).val :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ret :: R)
      (balanceInputMem mem p ee.codeOwner) aw' rdata σ k' C' ∧
      HeapMemory (balanceInputMem mem p ee.codeOwner) aw' (p + ⟨68⟩) := by
  obtain ⟨awBuild, kBuild, CBuild, rdBuild, hmBuild⟩ :=
    balanceBuildX (v := v) second rd hm (by omega) (by evm_ov)
  exact balanceCopyX (v := v) second rdBuild hmBuild hb (by evm_ov)

theorem balanceInputMem_size (mem : ByteArray) (p : UInt256) (who : AccountAddress)
    (hp : 128 ≤ p.toNat) :
    (balanceInputMem mem p who).size = max mem.size (p.toNat + 132) := by
  rw [balanceInputMem, balanceCopyMem2_size, balanceBuildMem_size _ _ _ hp]
  omega

theorem balanceInputMem_prefix (mem : ByteArray) (p : UInt256) (who : AccountAddress) :
    MemoryPrefix mem (balanceInputMem mem p who) p.toNat :=
  (balanceBuildMem_prefix mem p (EVM.word who.val)).trans
    ((balanceCopyMem2_prefix _ p).mono (by omega))

theorem balanceInputMem_calldata {mem : ByteArray} {aw p : UInt256}
    (hm : HeapMemory mem aw p) (who : AccountAddress) (hb : p.toNat + 132 < UInt256.size) :
    (balanceInputMem mem p who).readWithPadding (p.toNat + 68) 36 = balanceCalldata who := by
  rw [balanceInputMem, balanceCopyMem2_read _ p
    (by rw [balanceBuildMem_size _ _ _ hm.lower]; omega) hb]
  exact balanceBuildMem_calldata hm who (by omega)

theorem balanceInputMem_zero {mem : ByteArray} {aw p : UInt256}
    (hm : HeapMemory mem aw p) (who : AccountAddress)
    (hmem : 128 ≤ mem.size) (hzero : memLoad (UInt256.ofNat 96) mem = ⟨0⟩) :
    memLoad (UInt256.ofNat 96) (balanceInputMem mem p who) = ⟨0⟩ := by
  rw [MemoryPrefix.memLoad (balanceInputMem_prefix mem p who) (UInt256.ofNat 96) (by decide)
    (by change 128 ≤ p.toNat; exact hm.lower) (by exact hmem), hzero]

theorem balanceInputMem_bounds {mem : ByteArray} {aw p : UInt256}
    (hm : HeapMemory mem aw p) (who : AccountAddress) (hb : p.toNat + 2 ^ 138 + 163 ≤ 2 ^ 200) :
    (p + (⟨68⟩ : UInt256)).toNat + 32 ≤ (balanceInputMem mem p who).size ∧
    (p + (⟨68⟩ : UInt256)).toNat + 2 ^ 138 + 95 ≤ 2 ^ 200 ∧
    (p + (⟨68⟩ : UInt256)).toNat + 36 ≤ 2 ^ 200 := by
  have hp68 : (p + (⟨68⟩ : UInt256)).toNat = p.toNat + 68 :=
    uadd_word_ofNat_toNat p 68 (by change _ < 2 ^ 256; omega)
  rw [hp68, balanceInputMem_size _ _ _ hm.lower]
  omega

theorem balanceInputMem_read {mem : ByteArray} {aw p : UInt256}
    (hm : HeapMemory mem aw p) (who : AccountAddress) (hb : p.toNat + 2 ^ 138 + 163 ≤ 2 ^ 200) :
    (balanceInputMem mem p who).readWithPadding (p + (⟨68⟩ : UInt256)).toNat 36 =
      balanceCalldata who := by
  rw [show (p + (⟨68⟩ : UInt256)).toNat = p.toNat + 68 from
    uadd_word_ofNat_toNat p 68 (by change _ < 2 ^ 256; omega)]
  exact balanceInputMem_calldata hm who (by change _ < 2 ^ 256; omega)

theorem balanceEntryCallGrowingX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 evm : EVM.State} {k C : Nat} {aw p ret : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables} (second : Bool)
    (rd : RD (deployedRuntime v) ee g s0 (balanceEntry second) (ret :: R) mem aw rdata σ k C)
    (hs : SourceState s0 ee σ evm) (hm : HeapMemory mem aw p)
    (hzero : memLoad (UInt256.ofNat 96) (balanceInputMem mem p ee.codeOwner) = ⟨0⟩)
    (hb : p.toNat + 2 ^ 138 + 163 ≤ 2 ^ 200)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true) (hov : R.length + 18 ≤ 1024) :
    (RDrev (deployedRuntime v) g s0 ∧
      ExecFuncBody config {contract := contract, locals := ∅, immutables := immStore v} evm
        (balanceFunction second).body .reverted) ∨
    ∃ evm' σ' out mem' aw' next k' C', SourceState s0 ee σ' evm' ∧
      ExecFuncBody config {contract := contract, locals := ∅, immutables := immStore v} evm
        (balanceFunction second).body
        (.returned (balanceCallFrame v second true out) evm'
          (some [.int (Int.ofNat (balanceValue out).toNat)])) ∧
      RD (deployedRuntime v) ee g s0 ret (balanceValue out :: R) mem' aw' out σ' k' C' ∧
      HeapMemory mem' aw' next ∧ MemoryPrefix (balanceInputMem mem p ee.codeOwner) mem' (p +
        ⟨68⟩).toNat ∧
      (p + ⟨68⟩).toNat ≤ next.toNat ∧ next.toNat ≤ (p + ⟨68⟩).toNat + 2 ^ 138 + 63 := by
  obtain ⟨gasArg, awCall, kCall, CCall, rdCall, hmCall⟩ :=
    balancePrepareX (v := v) second rd hm (by omega) hov
  have hbounds := balanceInputMem_bounds hm ee.codeOwner hb
  have hcd : (balanceInputMem mem p ee.codeOwner).readWithPadding
      (p + (⟨68⟩ : UInt256)).toNat 36 = balanceCalldata evm.executionEnv.codeOwner := by
    rw [hs.env]
    exact balanceInputMem_read hm ee.codeOwner hb
  generalize hmc : balanceInputMem mem p ee.codeOwner = memCall at rdCall hmCall hbounds hzero hcd ⊢
  exact balanceCallGrowingX (v := v) second rdCall hs hcd hmCall hbounds.1 hzero
    hbounds.2.1 hbounds.2.2 hret (by omega)

theorem balanceEntryCallX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 evm : EVM.State} {k C : Nat} {aw p ret : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables} (second : Bool)
    (rd : RD (deployedRuntime v) ee g s0 (balanceEntry second) (ret :: R) mem aw rdata σ k C)
    (hs : SourceState s0 ee σ evm) (hm : HeapMemory mem aw p)
    (hzero : memLoad (UInt256.ofNat 96) (balanceInputMem mem p ee.codeOwner) = ⟨0⟩)
    (hb : p.toNat + 2 ^ 138 + 163 ≤ 2 ^ 200)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true) (hov : R.length + 18 ≤ 1024) :
    (RDrev (deployedRuntime v) g s0 ∧
      ExecFuncBody config {contract := contract, locals := ∅, immutables := immStore v} evm
        (balanceFunction second).body .reverted) ∨
    ∃ evm' σ' out mem' aw' next k' C', SourceState s0 ee σ' evm' ∧
      ExecFuncBody config {contract := contract, locals := ∅, immutables := immStore v} evm
        (balanceFunction second).body
        (.returned (balanceCallFrame v second true out) evm'
          (some [.int (Int.ofNat (balanceValue out).toNat)])) ∧
      RD (deployedRuntime v) ee g s0 ret (balanceValue out :: R) mem' aw' out σ' k' C' ∧
      HeapMemory mem' aw' next ∧ MemoryPrefix (balanceInputMem mem p ee.codeOwner) mem' (p +
        ⟨68⟩).toNat ∧
      next.toNat ≤ (p + ⟨68⟩).toNat + 2 ^ 138 + 63 := by
  rcases balanceEntryCallGrowingX (v := v) second rd hs hm hzero hb hret hov with
    hbad | ⟨evm', σ', out, mem', aw', next, k', C', hs', hbody, rr, hm', hpref, _, hnext⟩
  · exact Or.inl hbad
  · exact Or.inr ⟨evm', σ', out, mem', aw', next, k', C', hs', hbody, rr, hm', hpref, hnext⟩

theorem balanceInputMem_result {mem mem' : ByteArray} {p next : UInt256}
    (who : AccountAddress) (hb : p.toNat + 2 ^ 138 + 163 ≤ 2 ^ 200)
    (hpref : MemoryPrefix (balanceInputMem mem p who) mem' (p + ⟨68⟩).toNat)
    (hnext : next.toNat ≤ (p + ⟨68⟩).toNat + 2 ^ 138 + 63) :
    MemoryPrefix mem mem' p.toNat ∧ next.toNat ≤ p.toNat + 2 ^ 138 + 131 := by
  have hp68 : (p + (⟨68⟩ : UInt256)).toNat = p.toNat + 68 :=
    uadd_word_ofNat_toNat p 68 (by change _ < 2 ^ 256; omega)
  exact ⟨(balanceInputMem_prefix mem p who).trans (hpref.mono (by rw [hp68]; omega)), by
    simpa only [hp68, Nat.add_right_comm p.toNat 68 (2 ^ 138), Nat.add_assoc] using hnext⟩

theorem balanceGrowingX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 evm : EVM.State} {k C : Nat} {aw p ret : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables} (second : Bool)
    (rd : RD (deployedRuntime v) ee g s0 (balanceEntry second) (ret :: R) mem aw rdata σ k C)
    (hs : SourceState s0 ee σ evm) (hm : HeapMemory mem aw p) (hmem : 128 ≤ mem.size)
    (hzero : memLoad (UInt256.ofNat 96) mem = ⟨0⟩)
    (hb : p.toNat + 2 ^ 138 + 163 ≤ 2 ^ 200)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true) (hov : R.length + 18 ≤ 1024) :
    (RDrev (deployedRuntime v) g s0 ∧
      ExecFuncBody config {contract := contract, locals := ∅, immutables := immStore v} evm
        (balanceFunction second).body .reverted) ∨
    ∃ evm' σ' out mem' aw' next k' C', SourceState s0 ee σ' evm' ∧
      ExecFuncBody config {contract := contract, locals := ∅, immutables := immStore v} evm
        (balanceFunction second).body
        (.returned (balanceCallFrame v second true out) evm'
          (some [.int (Int.ofNat (balanceValue out).toNat)])) ∧
      RD (deployedRuntime v) ee g s0 ret (balanceValue out :: R) mem' aw' out σ' k' C' ∧
      HeapMemory mem' aw' next ∧ MemoryPrefix mem mem' p.toNat ∧
      p.toNat ≤ next.toNat ∧ next.toNat ≤ p.toNat + 2 ^ 138 + 131 := by
  rcases balanceEntryCallGrowingX (v := v) second rd hs hm
      (balanceInputMem_zero hm ee.codeOwner hmem hzero) hb hret hov with
    hbad | ⟨evm', σ', out, mem', aw', next, k', C', hs', hbody, rdDone, hm', hpref', hmono, hnext⟩
  · exact Or.inl hbad
  · obtain ⟨hpref, hbound⟩ := balanceInputMem_result ee.codeOwner hb hpref' hnext
    refine Or.inr ⟨evm', σ', out, mem', aw', next, k', C', hs', hbody, rdDone, hm', hpref, ?_,
      hbound⟩
    have hp68 : (p + (⟨68⟩ : UInt256)).toNat = p.toNat + 68 :=
      uadd_word_ofNat_toNat p 68 (by change _ < 2 ^ 256; omega)
    omega

theorem balanceX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 evm : EVM.State} {k C : Nat} {aw p ret : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables} (second : Bool)
    (rd : RD (deployedRuntime v) ee g s0 (balanceEntry second) (ret :: R) mem aw rdata σ k C)
    (hs : SourceState s0 ee σ evm) (hm : HeapMemory mem aw p) (hmem : 128 ≤ mem.size)
    (hzero : memLoad (UInt256.ofNat 96) mem = ⟨0⟩)
    (hb : p.toNat + 2 ^ 138 + 163 ≤ 2 ^ 200)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true) (hov : R.length + 18 ≤ 1024) :
    (RDrev (deployedRuntime v) g s0 ∧
      ExecFuncBody config {contract := contract, locals := ∅, immutables := immStore v} evm
        (balanceFunction second).body .reverted) ∨
    ∃ evm' σ' out mem' aw' next k' C', SourceState s0 ee σ' evm' ∧
      ExecFuncBody config {contract := contract, locals := ∅, immutables := immStore v} evm
        (balanceFunction second).body
        (.returned (balanceCallFrame v second true out) evm'
          (some [.int (Int.ofNat (balanceValue out).toNat)])) ∧
      RD (deployedRuntime v) ee g s0 ret (balanceValue out :: R) mem' aw' out σ' k' C' ∧
      HeapMemory mem' aw' next ∧ MemoryPrefix mem mem' p.toNat ∧
      next.toNat ≤ p.toNat + 2 ^ 138 + 131 := by
  rcases balanceGrowingX (v := v) second rd hs hm hmem hzero hb hret hov with
    hbad | ⟨evm', σ', out, mem', aw', next, k', C', hs', hbody, rr, hm', hpref, _, hnext⟩
  · exact Or.inl hbad
  · exact Or.inr ⟨evm', σ', out, mem', aw', next, k', C', hs', hbody, rr, hm', hpref, hnext⟩

end Benchmarks.UniswapV3.Pool
