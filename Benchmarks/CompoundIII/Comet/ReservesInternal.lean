import Benchmarks.CompoundIII.Comet.ReservesSource
import Benchmarks.CompoundIII.Comet.ReservesStartEvm
import Benchmarks.CompoundIII.Comet.ReservesResponse
import Benchmarks.CompoundIII.Comet.ReservesMathEvm
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_012

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 10000

theorem cometReservesQuery {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem rdata : ByteArray} {aw : UInt256}
    {σ : AccountMap} {k C : Nat} {ptr ret w0 w1 time : UInt256} {R : List UInt256}
    {evm : EVM.State}
    (hstack : R.length + 19 ≤ 1024) (hfree : memLoad ⟨64⟩ mem = ptr) (hlo : 96 ≤ ptr.toNat)
    (hptr : ptr.toNat + 36 < 2^64) (hv : CurrentIndicesValid v w0 w1 time)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (hs : SourceState s0 ee σ evm)
    (h : RD (deployedRuntime v) ee g s0 ⟨9871⟩
      (currentIndex v w0 w1 time true :: currentIndex v w0 w1 time false ::
        w1 :: ⟨2425⟩ :: ret :: R) mem aw rdata σ k C) :
    ∃ (evm' : EVM.State) (σ' : AccountMap) (z : Bool) (out : ByteArray),
      callViaEVM evm v.baseToken 0 (tokenBalancePayload evm.executionEnv.codeOwner)
        (z, evm', out) false ∧ SourceState s0 ee σ' evm' ∧ out.size < 2^138 ∧
      if ReservesReplyValid v w0 w1 time z out then
        ∃ aw' k' C', RD (deployedRuntime v) ee g s0 ret
          (reservesWord v w0 w1 time (calldataWord out 0) :: R)
          (tokenBalanceReturnMemory mem ptr ee.codeOwner out) aw' out σ' k' C'
      else RDrev (deployedRuntime v) g s0 := by
  have r1 := cometWithExtendedAssetList_block_9871
    (immWords := wordsOf (immStore v)) (by change R.length + 2 + 11 ≤ 1024; omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
  have hf : memLoad (UInt256.ofNat 64) mem = ptr := hfree
  simp only [cometWithExtendedAssetList_block_9871_stack,
    cometWithExtendedAssetList_block_9871_memory, hf] at r1
  have r2 := cometWithExtendedAssetList_block_1550
    (immWords := wordsOf (immStore v)) (by change R.length + 9 + 6 ≤ 1024; omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r1
  have r3 := cometWithExtendedAssetList_block_9903
    (immWords := wordsOf (immStore v)) (by change R.length + 7 + 7 ≤ 1024; omega) r2
  have ht : UInt256.land
      (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))
      (EVM.Word.ofNat (↑v.baseToken : Nat)) = EVM.word v.baseToken.val :=
    solcAddrMask_clean_left (addressWord_val_canonical v.baseToken)
  have ho : UInt256.land (UInt256.ofNat ee.codeOwner.val)
      (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) =
      EVM.word ee.codeOwner.val := addressWord_val_clean ee.codeOwner
  have hend : UInt256.sub ((UInt256.ofNat 32) + (ptr + UInt256.ofNat 4)) ptr =
      UInt256.ofNat 36 := by
    rw [u256_add_comm (UInt256.ofNat 32), uadd_assoc]
    exact word_add_sub_left ptr (UInt256.ofNat 36)
  simp only [cometWithExtendedAssetList_block_9903_stack,
    cometWithExtendedAssetList_block_1550_stack, cometWithExtendedAssetList_block_1550_memory,
    wordsOf_immStore_baseToken, ht, ho, hend] at r3
  have hb : ptr.toNat + 36 < UInt256.size := by change ptr.toNat + 36 < 2^256; omega
  obtain ⟨evm', σ', z, out, k4, C4, hc, hs', r4, hsize⟩ := staticCallBridge r3 hs
    (by immutable_decode(immutableLayout, cometWithExtendedAssetListBytecode,
      wordsOf (immStore v), (⟨9949⟩ : UInt256), UInt8.ofNat 250, .STATICCALL, none,
      immutableLayout_inBounds, immutableTemplate_size64))
    (tokenBalanceInputMemory_payload hb)
    (by rw [tokenBalancePayload_size]; decide)
    (by change R.length + 6 + 1 ≤ 1024; omega)
  have hc' : callViaEVM evm v.baseToken 0 (tokenBalancePayload evm.executionEnv.codeOwner)
      (z, evm', out) false := by
    have ht' : AccountAddress.ofUInt256 (EVM.word v.baseToken.val) = v.baseToken :=
      accountAddress_roundtrip v.baseToken
    simpa only [ht', hs.env] using hc
  refine ⟨evm', σ', z, out, hc', hs', hsize, ?_⟩
  cases z with
  | false =>
      rw [if_neg (by intro h; exact Bool.false_ne_true h.1)]
      exact cometReservesCallFailed (v := v) (by change R.length + 2 + 9 ≤ 1024; omega) r4
  | true =>
      obtain ⟨k5, C5, r5⟩ := cometReservesResponseStart (v := v)
        (by change R.length + 2 + 7 ≤ 1024; omega) r4
      by_cases hlen : 32 ≤ out.size
      · obtain ⟨aw6, k6, C6, r6⟩ := cometReservesResponseFull (v := v)
          (by change R.length + 2 + 17 ≤ 1024; omega) hlo hptr hlen
          (lt_trans hsize (by change 2^138 < 2^256; decide)) r5
        obtain ⟨k7, C7, r7⟩ := cometReservesPresentValues (v := v)
          (by change R.length + 2 + 17 ≤ 1024; omega) hv r6
        have hr := cometReservesSigned (v := v) (by omega) hv hret r7
        simp only [ReservesReplyValid, hlen, and_self, true_and]
        split_ifs with hm
        · rw [if_pos hm] at hr
          obtain ⟨k8, C8, r8⟩ := hr
          exact ⟨_, _, _, r8⟩
        · rw [if_neg hm] at hr
          exact hr
      · rw [if_neg (fun hv ↦ hlen hv.2.1)]
        exact cometReservesResponseShort (v := v)
          (by change R.length + 2 + 17 ≤ 1024; omega) (by omega) (Nat.lt_of_not_ge hlen) r5

theorem cometReservesInternal {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem rdata : ByteArray} {aw : UInt256}
    {σ : AccountMap} {k C : Nat} {ptr ret : UInt256} {R : List UInt256} {evm : EVM.State}
    (hstack : R.length + 35 ≤ 1024) (hfree : memLoad ⟨64⟩ mem = ptr) (hlo : 96 ≤ ptr.toNat)
    (hptr : ptr.toNat + 36 < 2^64)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (hs : SourceState s0 ee σ evm)
    (h : RD (deployedRuntime v) ee g s0 ⟨9825⟩ (ret :: R) mem aw rdata σ k C) :
    let w0 := solcSlotWordAt ⟨0⟩ σ ee
    let w1 := solcSlotWordAt ⟨1⟩ σ ee
    let time := timestampWord ee
    if CurrentIndicesValid v w0 w1 time then
      ∃ (evm' : EVM.State) (σ' : AccountMap) (z : Bool) (out : ByteArray),
        callViaEVM evm v.baseToken 0 (tokenBalancePayload evm.executionEnv.codeOwner)
          (z, evm', out) false ∧ SourceState s0 ee σ' evm' ∧ out.size < 2^138 ∧
        if ReservesReplyValid v w0 w1 time z out then
          ∃ aw' k' C', RD (deployedRuntime v) ee g s0 ret
            (reservesWord v w0 w1 time (calldataWord out 0) :: R)
            (tokenBalanceReturnMemory mem ptr ee.codeOwner out) aw' out σ' k' C'
        else RDrev (deployedRuntime v) g s0
    else RDrev (deployedRuntime v) g s0 := by
  dsimp only
  have hr := cometReservesStart hstack h
  dsimp only at hr
  split_ifs with hv
  · rw [if_pos hv] at hr
    obtain ⟨k1, C1, r1⟩ := hr
    exact cometReservesQuery (by omega) hfree hlo hptr hv hret hs r1
  · rw [if_neg hv] at hr
    exact hr

end Benchmarks.CompoundIII.Comet
