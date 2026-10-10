import Benchmarks.UniswapV3.Pool.BalanceReturn

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem balanceCalldata_size (who : AccountAddress) : (balanceCalldata who).size = 36 := by
  simp only [balanceCalldata, ByteArray.size_append, toByteArray_size]
  rfl

theorem balanceCallGrowingX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 evm : EVM.State} {k C : Nat}
    {aw ptr inOff gasArg junk0 junk1 junk2 junk3 junk4 ret : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables} (second : Bool)
    (rd : RD (deployedRuntime v) ee g s0 ⟨15774⟩
      (gasArg :: EVM.word (balanceToken v second).val :: inOff :: ⟨36⟩ :: inOff :: ⟨0⟩ ::
        junk0 :: junk1 :: junk2 :: junk3 :: junk4 :: ret :: R) mem aw rdata σ k C)
    (hs : SourceState s0 ee σ evm)
    (hcd : mem.readWithPadding inOff.toNat 36 = balanceCalldata evm.executionEnv.codeOwner)
    (hm : HeapMemory mem aw ptr) (hptr : ptr.toNat + 32 ≤ mem.size)
    (hzero : memLoad (UInt256.ofNat 96) mem = ⟨0⟩)
    (hbound : ptr.toNat + 2 ^ 138 + 95 ≤ 2 ^ 200) (hinOff : inOff.toNat + 36 ≤ 2 ^ 200)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true) (hov : R.length + 11 ≤ 1024) :
    (RDrev (deployedRuntime v) g s0 ∧
      ExecFuncBody config {contract := contract, locals := ∅, immutables := immStore v} evm
        (balanceFunction second).body .reverted) ∨
    ∃ evm' σ' out mem' aw' next k' C', SourceState s0 ee σ' evm' ∧
      ExecFuncBody config {contract := contract, locals := ∅, immutables := immStore v} evm
        (balanceFunction second).body
        (.returned (balanceCallFrame v second true out) evm'
          (some [.int (Int.ofNat (balanceValue out).toNat)])) ∧
      RD (deployedRuntime v) ee g s0 ret (balanceValue out :: R) mem' aw' out σ' k' C' ∧
      HeapMemory mem' aw' next ∧ MemoryPrefix mem mem' ptr.toNat ∧
      ptr.toNat ≤ next.toNat ∧ next.toNat ≤ ptr.toNat + 2 ^ 138 + 63 := by
  obtain ⟨ok, out, σ', A', kCall, CCall, hcall, rdAfter, hsize⟩ :=
    RD.staticcallSource (evm := evm) rd
      (by immutable_decode(immutableLayout, uniswapV3PoolBytecode, wordsOf (immStore v),
        (⟨15774⟩ : UInt256), (UInt8.ofNat 250), .STATICCALL, none,
        immutableLayout_inBounds, immutableTemplate_size64))
      (by evm_ov) hs.accounts.symm hs.world hs.env
  change callViaEVM evm (AccountAddress.ofUInt256 (EVM.word (balanceToken v second).val)) 0
    (mem.readWithPadding inOff.toNat 36)
    (ok, {evm with accountMap := σ', substate := A'}, out) false at hcall
  rw [show AccountAddress.ofUInt256 (EVM.word (balanceToken v second).val) =
    balanceToken v second from accountAddress_roundtrip _, hcd] at hcall
  have hout := callViaEVM_output_size hcall (by rw [balanceCalldata_size]; decide +kernel)
  rw [callOutputMem_zero] at rdAfter
  have hflag : (if ok then (⟨1⟩ : UInt256) else ⟨0⟩) = ok.toUInt256 := by cases ok <;> rfl
  rw [hflag] at rdAfter
  have hmCall : HeapMemory mem (callActiveWords aw inOff ⟨36⟩ inOff ⟨0⟩) ptr :=
    ⟨hm.size, hm.free, hm.lower, hm.gap,
      callActiveWords_active hm.active hinOff (by change inOff.toNat + 0 ≤ _; omega)⟩
  obtain ⟨dataPtr, next, mem', aw', kData, CData, rdReady, hm', hpref, hmono, hnext, hdataPtr, hlen,
    hword⟩ :=
    balanceReturndataGrowingX (v := v) rdAfter hmCall hptr hzero (by omega) hsize (by evm_ov)
  rcases balanceFinishX (v := v) ok rdReady hlen hword hsize hm'.active hdataPtr hret (by omega)
    with
    ⟨hbad, rdFail⟩ | ⟨hok, hlong, aw'', kFinal, CFinal, rdFinal, haFinal⟩
  · exact Or.inl ⟨rdFail, balanceReverts v second evm _ ok out hcall hbad⟩
  · subst ok
    exact Or.inr ⟨{evm with accountMap := σ', substate := A'}, σ', out, mem', aw'', next, kFinal,
      CFinal,
      ⟨hs.world, hs.env, rfl⟩, balanceReturns v second evm _ out hcall hlong, rdFinal,
      {hm' with active := haFinal}, hpref, hmono, by omega⟩

theorem balanceCallX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 evm : EVM.State} {k C : Nat}
    {aw ptr inOff gasArg junk0 junk1 junk2 junk3 junk4 ret : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables} (second : Bool)
    (rd : RD (deployedRuntime v) ee g s0 ⟨15774⟩
      (gasArg :: EVM.word (balanceToken v second).val :: inOff :: ⟨36⟩ :: inOff :: ⟨0⟩ ::
        junk0 :: junk1 :: junk2 :: junk3 :: junk4 :: ret :: R) mem aw rdata σ k C)
    (hs : SourceState s0 ee σ evm)
    (hcd : mem.readWithPadding inOff.toNat 36 = balanceCalldata evm.executionEnv.codeOwner)
    (hm : HeapMemory mem aw ptr) (hptr : ptr.toNat + 32 ≤ mem.size)
    (hzero : memLoad (UInt256.ofNat 96) mem = ⟨0⟩)
    (hbound : ptr.toNat + 2 ^ 138 + 95 ≤ 2 ^ 200) (hinOff : inOff.toNat + 36 ≤ 2 ^ 200)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true) (hov : R.length + 11 ≤ 1024) :
    (RDrev (deployedRuntime v) g s0 ∧
      ExecFuncBody config {contract := contract, locals := ∅, immutables := immStore v} evm
        (balanceFunction second).body .reverted) ∨
    ∃ evm' σ' out mem' aw' next k' C', SourceState s0 ee σ' evm' ∧
      ExecFuncBody config {contract := contract, locals := ∅, immutables := immStore v} evm
        (balanceFunction second).body
        (.returned (balanceCallFrame v second true out) evm'
          (some [.int (Int.ofNat (balanceValue out).toNat)])) ∧
      RD (deployedRuntime v) ee g s0 ret (balanceValue out :: R) mem' aw' out σ' k' C' ∧
      HeapMemory mem' aw' next ∧ MemoryPrefix mem mem' ptr.toNat ∧
      next.toNat ≤ ptr.toNat + 2 ^ 138 + 63 := by
  rcases balanceCallGrowingX (v := v) second rd hs hcd hm hptr hzero hbound hinOff
      hret hov with
    hbad | ⟨evm', σ', out, mem', aw', next, k', C', hs', hbody, rr, hm', hpref, _, hnext⟩
  · exact Or.inl hbad
  · exact Or.inr ⟨evm', σ', out, mem', aw', next, k', C', hs', hbody, rr, hm', hpref, hnext⟩

end Benchmarks.UniswapV3.Pool
