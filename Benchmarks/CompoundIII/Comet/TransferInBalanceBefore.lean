import Benchmarks.CompoundIII.Comet.BalanceWordDecode
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_061
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_063
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_012

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

theorem cometTransferInBalanceBefore {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem rdata : ByteArray} {aw : UInt256}
    {σ : AccountMap} {k C : Nat} {ptr amount : UInt256} {R : List UInt256}
    {asset sender : AccountAddress} {evm : EVM.State}
    (hstack : R.length + 15 ≤ 1024) (hfree : memLoad ⟨64⟩ mem = ptr) (hlo : 96 ≤ ptr.toNat)
    (hptr : ptr.toNat + 36 < 2^64) (hs : SourceState s0 ee σ evm)
    (h : RD (deployedRuntime v) ee g s0 ⟨13272⟩
      (EVM.word asset.val :: EVM.word sender.val :: amount :: R) mem aw rdata σ k C) :
    ∃ (evm' : EVM.State) (σ' : AccountMap) (z : Bool) (out : ByteArray),
      callViaEVM evm asset 0 (tokenBalancePayload evm.executionEnv.codeOwner)
        (z, evm', out) false ∧ SourceState s0 ee σ' evm' ∧ out.size < 2^138 ∧
      if z = true ∧ 32 ≤ out.size then
        ∃ aw' k' C' dummy, RD (deployedRuntime v) ee g s0 ⟨13340⟩
          (dummy :: EVM.word sender.val :: amount :: EVM.word asset.val :: ⟨32⟩ ::
            calldataWord out 0 :: tokenBalanceSelectorWord :: R)
          (tokenBalanceReturnMemory mem ptr ee.codeOwner out) aw' out σ' k' C'
      else RDrev (deployedRuntime v) g s0 := by
  have r1 := cometWithExtendedAssetList_block_13272 (immWords := wordsOf (immStore v))
    (by omega) (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
  have ha : UInt256.land
      (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))
      (EVM.word asset.val) = EVM.word asset.val :=
    solcAddrMask_clean_left (addressWord_val_canonical asset)
  have hf : memLoad (UInt256.ofNat 64) mem = ptr := hfree
  simp only [cometWithExtendedAssetList_block_13272_stack,
    cometWithExtendedAssetList_block_13272_memory, hf, ha] at r1
  have r2 := cometWithExtendedAssetList_block_1550 (immWords := wordsOf (immStore v))
    (by change R.length + 9 + 6 ≤ 1024; omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r1
  have r3 := cometWithExtendedAssetList_block_13319 (immWords := wordsOf (immStore v))
    (by change R.length + 3 + 9 ≤ 1024; omega) r2
  have ho : UInt256.land (UInt256.ofNat ee.codeOwner.val)
      (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) =
      EVM.word ee.codeOwner.val := addressWord_val_clean ee.codeOwner
  have hend : UInt256.sub ((UInt256.ofNat 32) + (ptr + UInt256.ofNat 4)) ptr =
      UInt256.ofNat 36 := by
    rw [u256_add_comm (UInt256.ofNat 32), uadd_assoc]
    exact word_add_sub_left ptr (UInt256.ofNat 36)
  simp only [cometWithExtendedAssetList_block_13319_stack,
    cometWithExtendedAssetList_block_1550_memory, ho, hend] at r3
  have hb : ptr.toNat + 36 < UInt256.size := by change ptr.toNat + 36 < 2^256; omega
  obtain ⟨evm', σ', z, out, k4, C4, hc, hs', r4, hh⟩ := staticCallBridge r3 hs
    (by immutable_decode(immutableLayout, cometWithExtendedAssetListBytecode,
      wordsOf (immStore v), (⟨13324⟩ : UInt256), UInt8.ofNat 250, .STATICCALL, none,
      immutableLayout_inBounds, immutableTemplate_size64))
    (tokenBalanceInputMemory_payload hb) (by rw [tokenBalancePayload_size]; decide)
    (by change R.length + 6 + 1 ≤ 1024; omega)
  have hc' : callViaEVM evm asset 0 (tokenBalancePayload evm.executionEnv.codeOwner)
      (z, evm', out) false := by
    have haddr : AccountAddress.ofUInt256 (EVM.word asset.val) = asset :=
      accountAddress_roundtrip asset
    simpa only [haddr, hs.env] using hc
  refine ⟨evm', σ', z, out, hc', hs', hh, ?_⟩
  cases z with
  | false =>
    rw [if_neg (by simp)]
    have r5 := cometWithExtendedAssetList_block_13325_taken
      (immWords := wordsOf (immStore v)) (by change R.length + 1 + 8 ≤ 1024; omega)
      (by decide) (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r4
    have r6 := cometWithExtendedAssetList_block_13637 (immWords := wordsOf (immStore v))
      (by change R.length + 7 + 2 ≤ 1024; omega)
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r5
    exact cometWithExtendedAssetList_block_7166 (immWords := wordsOf (immStore v))
      (by change R.length + 7 + 4 ≤ 1024; omega)
      (by change 0 + out.size % UInt256.size ≤ out.size; simpa using Nat.mod_le out.size _) r6
  | true =>
    have r5 := cometWithExtendedAssetList_block_13325_fallthrough
      (immWords := wordsOf (immStore v)) (by change R.length + 1 + 8 ≤ 1024; omega)
      (by decide) r4
    have r6 := cometWithExtendedAssetList_block_13332_taken
      (immWords := wordsOf (immStore v)) (by change R.length + 1 + 8 ≤ 1024; omega)
      (by decide) (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r5
    have hhi : out.size < UInt256.size := lt_trans hh (by change 2^138 < 2^256; decide)
    by_cases hlen : 32 ≤ out.size
    · rw [if_pos ⟨rfl, hlen⟩]
      have r7 := cometWithExtendedAssetList_block_13606_fallthrough
        (immWords := wordsOf (immStore v)) (by change R.length + 1 + 9 ≤ 1024; omega)
        (ugt_zero (by rw [UInt256.toNat_ofNat_of_lt hhi]; exact hlen)) r6
      have r8 := cometWithExtendedAssetList_block_13621 (immWords := wordsOf (immStore v))
        (by change R.length + 6 + 6 ≤ 1024; omega)
        (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r7
      obtain ⟨aw9, k9, C9, r9⟩ := cometAllocatedWordDecode (v := v)
        (by change R.length + 5 + 9 ≤ 1024; omega) (by omega)
        (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r8
      change RD _ _ _ _ ⟨13630⟩
        (memLoad ptr (tokenBalanceReturnMemory mem ptr ee.codeOwner out) :: amount ::
          EVM.word asset.val :: ⟨32⟩ :: EVM.word sender.val :: tokenBalanceSelectorWord :: R)
        (tokenBalanceReturnMemory mem ptr ee.codeOwner out) _ _ _ _ _ at r9
      rw [tokenBalanceReturnMemory_word hlo hb hlen hhi] at r9
      have r10 := cometWithExtendedAssetList_block_13630 (immWords := wordsOf (immStore v))
        (by change R.length + 1 + 7 ≤ 1024; omega)
        (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r9
      exact ⟨_, _, _, _, r10⟩
    · rw [if_neg (by simpa using hlen)]
      have r7 := cometWithExtendedAssetList_block_13606_taken
        (immWords := wordsOf (immStore v)) (by change R.length + 1 + 9 ≤ 1024; omega)
        (by
          rw [ugt_one (by
            rw [UInt256.toNat_ofNat_of_lt hhi]
            change out.size < 32
            omega)]
          decide)
        (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r6
      exact cometShortWordDecode (by change R.length + 6 + 8 ≤ 1024; omega)
        (by omega) (Nat.lt_of_not_ge hlen) r7

end Benchmarks.CompoundIII.Comet
