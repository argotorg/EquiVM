import Benchmarks.Morpho.MetaMorphoV1_1.BorrowRateEncodeMemory
import Benchmarks.Morpho.MetaMorphoV1_1.MarketParamsEncode

/-! The active-accrual branch's complete call-buffer construction. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option autoImplicit false

theorem MarketParamsLoads.prefix {before after : ByteArray} {src : UInt256}
    {p : MarketParamsData} {limit : Nat} (hloads : MarketParamsLoads before src p)
    (hprefix : MemoryPrefix before after limit) (hlo : 96 ≤ src.toNat)
    (hmem : src.toNat + 160 ≤ before.size) (hlimit : src.toNat + 160 ≤ limit)
    (hfit : src.toNat + 160 < UInt256.size) : MarketParamsLoads after src p := by
  have hr := wordWindowPrefix_load hprefix hlo hmem hlimit hfit
  have h0 : memLoad src after = memLoad src before := by
    simpa only [show UInt256.ofNat 0 = (⟨0⟩ : UInt256) from rfl, u256_add_zero] using
      hr 0 (by decide)
  exact ⟨h0.trans hloads.1, (hr 32 (by decide)).trans hloads.2.1,
    (hr 64 (by decide)).trans hloads.2.2.1, (hr 96 (by decide)).trans hloads.2.2.2.1,
    (hr 128 (by decide)).trans hloads.2.2.2.2⟩

theorem borrowRateCompleteMemory (mem : ByteArray) (ptr : UInt256) (p : MarketParamsData)
    (market : ByteArray) :
    writeWord (borrowRateFirstFiveMem
      (wordSequenceMemory (writeWord mem ptr.toNat borrowRateSelectorWord) (ptr.toNat + 4) p.words)
      ptr market) (ptr.toNat + 324) (calldataWord market 160) =
      borrowRateCallMem mem ptr.toNat p market := by
  simp only [borrowRateFirstFiveMem, borrowRateCallMem, wordCallMemory, MarketParamsData.words,
    marketWords, List.cons_append, List.nil_append, List.take, wordSequenceMemory,
    Nat.add_assoc, Nat.reduceAdd]

set_option maxRecDepth 2000 in
theorem borrowRateReachStaticcall {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem market : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {ptr params src elapsed : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (p : MarketParamsData) (hstack : R.length + 14 ≤ 1024)
    (hfree : memLoad ⟨64⟩ mem = ptr) (hptr : ptr.toNat < 2 ^ 64)
    (hin : ptr.toNat ≤ mem.size) (hparamslo : 96 ≤ params.toNat) (hsrclo : 96 ≤ src.toNat)
    (hparams : params.toNat + 160 ≤ ptr.toNat) (hsrc : src.toNat + 192 ≤ ptr.toNat)
    (hparamsRead : MarketParamsLoads mem params p) (hc : MarketChecks market)
    (hmarket : ∀ off, off + 32 ≤ 192 →
      memLoad (src + UInt256.ofNat off) mem = calldataWord market off)
    (rd : RD (deployedRuntime v) I g s0 ⟨17069⟩
      (params :: (src + UInt256.ofNat 128) :: elapsed :: src :: R) mem aw rdata σ k C) :
    ∃ gasArg aw' k' C', RD (deployedRuntime v) I g s0 ⟨17225⟩
      (gasArg :: UInt256.ofNat p.irm.toNat :: ptr :: ⟨356⟩ :: ptr :: ⟨32⟩ ::
        elapsed :: (src + UInt256.ofNat 160) :: ptr :: (src + UInt256.ofNat 64) ::
        (src + UInt256.ofNat 32) :: src :: R)
      (borrowRateCallMem mem ptr.toNat p market) aw' rdata σ k' C' := by
  have hword : ptr.toNat + 356 < UInt256.size := by change _ < 2 ^ 256; omega
  have hpf : params.toNat + 160 < UInt256.size := by omega
  have hsf : src.toNat + 192 < UInt256.size := by omega
  have h4 : (ptr + UInt256.ofNat 4).toNat = ptr.toNat + 4 :=
    uadd_word_ofNat_toNat ptr 4 (by omega)
  let m0 := writeWord mem ptr.toNat borrowRateSelectorWord
  have hp0 : MemoryPrefix mem m0 ptr.toNat :=
    memoryPrefix_sparse_writeWord _ _ _ _ (.inl (le_refl _))
  have hpr0 := hparamsRead.prefix hp0 hparamslo (by omega) hparams hpf
  obtain ⟨aw0, k0, C0, h0⟩ := metaMorphoV1_1_block_17069_packed
    (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
  have hf : memLoad (UInt256.ofNat 64) mem = ptr := hfree
  have hirm : UInt256.land (memLoad (params + UInt256.ofNat 96) mem)
      (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
        (UInt256.ofNat 1)) = UInt256.ofNat p.irm.toNat := by
    rw [hparamsRead.2.2.2.1]
    exact solcAddrMask_clean (addressWord_val_canonical p.irm)
  simp only [metaMorphoV1_1_block_17069_stack, metaMorphoV1_1_block_17069_memory, hf, hirm] at h0
  obtain ⟨aw1, k1, C1, h1⟩ := marketParamsEncodeRoutine v p
    (by simp only [List.length_cons]; omega)
    (by have hm := hp0.size; omega) (by rw [h4]; omega) (by rw [h4]; omega) hpr0
    (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) h0
  rw [h4] at h1
  let m1 := wordSequenceMemory m0 (ptr.toNat + 4) p.words
  have hp1 : MemoryPrefix mem m1 ptr.toNat :=
    hp0.trans ((wordSequenceMemory_prefix _ _ _).mono (by omega))
  have hmr1 : ∀ off, off + 32 ≤ 192 →
      memLoad (src + UInt256.ofNat off) m1 = calldataWord market off := by
    intro off hoff
    exact (wordWindowPrefix_load hp1 hsrclo (by omega) hsrc hsf off hoff).trans
      (hmarket off hoff)
  obtain ⟨aw2, k2, C2, h2⟩ := metaMorphoV1_1_block_17114_packed
    (immWords := wordsOf (immStore v)) (by omega) h1
  change RD (deployedRuntime v) I g s0 ⟨17198⟩
    (ptr :: ⟨32⟩ :: elapsed :: UInt256.ofNat p.irm.toNat :: ptr ::
      (src + UInt256.ofNat 64) :: (src + UInt256.ofNat 32) :: src :: R)
    (metaMorphoV1_1_block_17114_memory (mem := m1) (x1 := ptr)
      (x2 := src + UInt256.ofNat 128) (x4 := src)) aw2 rdata σ k2 C2 at h2
  rw [borrowRateFirstFiveMemory (by have hm := hp1.size; omega) hsrc hword hc hmr1] at h2
  let m2 := borrowRateFirstFiveMem m1 ptr market
  have hp2 : MemoryPrefix mem m2 ptr.toNat := hp1.trans (borrowRateFirstFiveMem_prefix _ _ _)
  have hfee : memLoad (src + UInt256.ofNat 160) m2 = calldataWord market 160 :=
    (wordWindowPrefix_load hp2 hsrclo (by omega) hsrc hsf 160 (by decide)).trans
      (hmarket 160 (by decide))
  have hfeeMask : UInt256.land (calldataWord market 160)
      (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128))
        (UInt256.ofNat 1)) = calldataWord market 160 :=
    u256LandMaskCleanOfToNat _ _ (by decide +kernel) hc.2.2.2.2.2.2
  obtain ⟨aw3, k3, C3, h3⟩ := metaMorphoV1_1_block_17198_packed
    (immWords := wordsOf (immStore v)) hstack h2
  have h324 : (ptr + UInt256.ofNat 324).toNat = ptr.toNat + 324 :=
    uadd_word_ofNat_toNat ptr 324 (by omega)
  change memLoad (src + UInt256.ofNat 160) (borrowRateFirstFiveMem m1 ptr market) = _ at hfee
  simp only [metaMorphoV1_1_block_17198_stack, metaMorphoV1_1_block_17198_memory,
    hfee, hfeeMask, h324] at h3
  have hm : (calldataWord market 160).toByteArray.write 0
      (borrowRateFirstFiveMem m1 ptr market) (ptr.toNat + 324) 32 =
      borrowRateCallMem mem ptr.toNat p market := borrowRateCompleteMemory mem ptr p market
  rw [hm] at h3
  exact ⟨_, aw3, k3, C3, h3⟩

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
