import Benchmarks.Morpho.MorphoBlue.Allocation
import Benchmarks.Morpho.MorphoBlue.BorrowRateABI
import Benchmarks.Morpho.MorphoBlue.RuntimeBlocks_015
import Reasoning.ExternalCall

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

theorem morphoCreateMarketDecodeResume {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {σ : AccountMap} {k C : Nat} {ptr : UInt256} (n : Nat) (hn : n ≤ 32)
    (hfit : ptr.toNat + 63 ≤ 2 ^ 64 - 1)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 5348)
      [UInt256.ofNat n, ptr, UInt256.ofNat 32, UInt256.ofNat 0] mem aw rdata σ k C) :
    if n = 32 then RDret (deployedRuntime v) g s0 σ ByteArray.empty
    else RDrev (deployedRuntime v) g s0 := by
  obtain ⟨aw1, k1, C1, rd1⟩ := morphoBlocks.morpho_block_5348_packed
    (immWords := wordsOf (immStore v)) (by simp)
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) h
  obtain ⟨aw2, k2, C2, rd2⟩ := morphoAllocDynamic (v := v) n (by simp)
    (by rw [morphoPatchedValidJumps v]; jump_dest) (by omega) rd1
  by_cases heq : n = 32
  · rw [if_pos heq]
    subst n
    have rd3 := morphoBlocks.morpho_block_5358_fallthrough
      (immWords := wordsOf (immStore v)) (by simp)
      (by rw [word_add_sub_left]; decide) rd2
    have rd4 := morphoBlocks.morpho_block_5367
      (immWords := wordsOf (immStore v)) (by simp [morphoBlocks.morpho_block_5358_fallthrough_stack])
      (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) rd3
    have ret := morphoBlocks.morpho_block_5333
      (immWords := wordsOf (immStore v)) (by simp) rd4
    simpa only [show (UInt256.ofNat 0).toNat = 0 from rfl,
      byteArray_readWithPadding_zero] using ret
  · rw [if_neg heq]
    have rd3 := morphoBlocks.morpho_block_5358_taken
      (immWords := wordsOf (immStore v)) (by simp)
      (by rw [word_add_sub_left, slt_ofNat_lit_one_low (by norm_num) (by omega)]; decide)
      (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) rd2
    exact morphoBlocks.morpho_block_712 (immWords := wordsOf (immStore v))
      (by simp [morphoBlocks.morpho_block_5358_taken_stack]) rd3

theorem morphoCreateMarketCallFalse {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {σ : AccountMap} {k C : Nat} {ptr : UInt256}
    (hsize : rdata.size < UInt256.size)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 5323)
      [UInt256.ofNat 0, ptr, UInt256.ofNat 32, UInt256.ofNat 0] mem aw rdata σ k C) :
    RDrev (deployedRuntime v) g s0 := by
  have rd1 := morphoBlocks.morpho_block_5323_taken
    (immWords := wordsOf (immStore v)) (by simp) (by decide)
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) h
  exact morphoBlocks.morpho_block_5380 (immWords := wordsOf (immStore v)) (by simp)
    (by rw [UInt256.toNat_ofNat_of_lt hsize]; change 0 + rdata.size ≤ rdata.size; omega) rd1

theorem morphoCreateMarketCallTrue {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {σ : AccountMap} {k C : Nat} {ptr : UInt256}
    (hsize : rdata.size < UInt256.size) (hfit : ptr.toNat + 63 ≤ 2 ^ 64 - 1)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 5323)
      [UInt256.ofNat 1, ptr, UInt256.ofNat 32, UInt256.ofNat 0] mem aw rdata σ k C) :
    if 32 ≤ rdata.size then RDret (deployedRuntime v) g s0 σ ByteArray.empty
    else RDrev (deployedRuntime v) g s0 := by
  have rd1 := morphoBlocks.morpho_block_5323_fallthrough
    (immWords := wordsOf (immStore v)) (by simp) (by decide) h
  have rd2 := morphoBlocks.morpho_block_5329_taken
    (immWords := wordsOf (immStore v)) (by simp) (by decide)
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) rd1
  by_cases hlen : 32 ≤ rdata.size
  · rw [if_pos hlen]
    have rd3 := morphoBlocks.morpho_block_5339_fallthrough
      (immWords := wordsOf (immStore v)) (by simp)
      (ugt_zero (by rw [UInt256.toNat_ofNat_of_lt hsize]; exact hlen)) rd2
    simpa only [if_pos rfl] using morphoCreateMarketDecodeResume (v := v) 32 (by omega) hfit rd3
  · rw [if_neg hlen]
    have rd3 := morphoBlocks.morpho_block_5339_taken
      (immWords := wordsOf (immStore v)) (by simp)
      (by rw [ugt_one (by rw [UInt256.toNat_ofNat_of_lt hsize]; change rdata.size < 32; omega)]; decide)
      (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) rd2
    have rd4 := morphoBlocks.morpho_block_5373
      (immWords := wordsOf (immStore v)) (by simp)
      (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) rd3
    simpa only [if_neg (show rdata.size ≠ 32 by omega)] using
      morphoCreateMarketDecodeResume (v := v) rdata.size (by omega) hfit rd4

theorem morphoCreateMarketCall {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {σ : AccountMap} {k C : Nat} {ptr gasArg id : UInt256} {evm : State}
    (p : MarketParamsWords) (hc : p.Canonical) (hs : SourceState s0 ee σ evm)
    (hperm : ee.perm = true) (hfit : ptr.toNat + 63 ≤ 2 ^ 64 - 1)
    (hcd : mem.readWithPadding ptr.toNat 356 = borrowRateCalldata p σ ee id)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 5322)
      [gasArg, p.irm, UInt256.ofNat 0, ptr, UInt256.ofNat 356,
       ptr, UInt256.ofNat 32, ptr, UInt256.ofNat 32, UInt256.ofNat 0] mem aw rdata σ k C) :
    ∃ evm' z out,
      typedCallViaEVM config evm (AccountAddress.ofNat p.irm.toNat) "borrowRate" 0
        [p.value, marketStateValue σ ee id] (z, evm', out) ∧
      SourceState s0 ee evm'.accountMap evm' ∧ out.size < 2 ^ 138 ∧
      (if z = true ∧ 32 ≤ out.size then
        RDret (deployedRuntime v) g s0 evm'.accountMap ByteArray.empty
       else RDrev (deployedRuntime v) g s0) := by
  obtain ⟨evm', σ', z, out, k', C', hcall, hs', rd, hout⟩ :=
    callBridge h hs hperm
      (by immutable_decode(immutableLayout, morphoBytecode, wordsOf (immStore v),
        (⟨5322⟩ : UInt256), UInt8.ofNat 241, .CALL, none,
        morphoBlocks.immutableLayout_inBounds, morphoBlocks.immutableTemplate_size64)) hcd
      (by rw [borrowRateCalldata_size]; decide) (by simp)
  have htyped : typedCallViaEVM config evm (AccountAddress.ofNat p.irm.toNat) "borrowRate" 0
      [p.value, marketStateValue σ ee id] (z, evm', out) := by
    refine ⟨borrowRateCalldata p σ ee id, encodeBorrowRate p hc σ ee id, ?_⟩
    simpa only [accountAddress_ofUInt256_eq_ofNat_toNat,
      show Int.ofNat (UInt256.ofNat 0).toNat = 0 from rfl] using hcall
  refine ⟨evm', z, out, htyped, ⟨hs'.world, hs'.env, rfl⟩, hout, ?_⟩
  have houtWord : out.size < UInt256.size := by change out.size < 2 ^ 256; omega
  cases z
  · simp only [Bool.false_eq_true, false_and, ↓reduceIte]
    exact morphoCreateMarketCallFalse (v := v) houtWord rd
  · simp only [true_and]
    rw [← hs'.accounts]
    exact morphoCreateMarketCallTrue (v := v) houtWord hfit rd

end Benchmarks.Morpho.MorphoBlue
