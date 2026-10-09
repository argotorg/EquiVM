import Benchmarks.CompoundIII.Comet.CollateralReservesSource
import Benchmarks.CompoundIII.Comet.CollateralReservesArithmetic
import Benchmarks.CompoundIII.Comet.TokenBalanceResponse

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 10000

def collateralReservesMemory (mem : ByteArray) (ptr : UInt256) (owner asset : AccountAddress)
    (out : ByteArray) : ByteArray :=
  twoWordHashMem (EVM.word asset.val) ⟨2⟩ (tokenBalanceReturnMemory mem ptr owner out)

theorem cometCollateralReservesInternal {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem rdata : ByteArray} {aw : UInt256}
    {σ : AccountMap} {k C : Nat} {ptr ret : UInt256} {R : List UInt256}
    {asset : AccountAddress} {evm : EVM.State}
    (hstack : R.length + 11 ≤ 1024) (hfree : memLoad ⟨64⟩ mem = ptr) (hlo : 96 ≤ ptr.toNat)
    (hptr : ptr.toNat + 36 < 2^64)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (hs : SourceState s0 ee σ evm)
    (h : RD (deployedRuntime v) ee g s0 ⟨9561⟩ (EVM.word asset.val :: ret :: R)
      mem aw rdata σ k C) :
    ∃ (evm' : EVM.State) (σ' : AccountMap) (z : Bool) (out : ByteArray),
      callViaEVM evm asset 0 (tokenBalancePayload evm.executionEnv.codeOwner)
        (z, evm', out) false ∧ SourceState s0 ee σ' evm' ∧ out.size < 2^138 ∧
      if CollateralReservesValid evm' asset z out then
        ∃ aw' k' C', RD (deployedRuntime v) ee g s0 ret
          (collateralReservesValue evm' asset out :: R)
          (collateralReservesMemory mem ptr ee.codeOwner asset out) aw' out σ' k' C'
      else RDrev (deployedRuntime v) g s0 := by
  have r1 := cometWithExtendedAssetList_block_9561
    (immWords := wordsOf (immStore v)) (by change R.length + 1 + 8 ≤ 1024; omega) h
  have ht : UInt256.land
      (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))
      (EVM.word asset.val) = EVM.word asset.val :=
    solcAddrMask_clean_left (addressWord_val_canonical asset)
  have hf : memLoad (UInt256.ofNat 64) mem = ptr := hfree
  simp only [cometWithExtendedAssetList_block_9561_stack,
    cometWithExtendedAssetList_block_9561_memory, hf, ht] at r1
  have hb : ptr.toNat + 36 < UInt256.size := by change ptr.toNat + 36 < 2^256; omega
  obtain ⟨evm', σ', z, out, k2, C2, hc, hs', r2, hsize⟩ := staticCallBridge r1 hs
    (by immutable_decode(immutableLayout, cometWithExtendedAssetListBytecode,
      wordsOf (immStore v), (⟨9599⟩ : UInt256), UInt8.ofNat 250, .STATICCALL, none,
      immutableLayout_inBounds, immutableTemplate_size64))
    (tokenBalanceInputMemory_payload hb)
    (by rw [tokenBalancePayload_size]; decide)
    (by change R.length + 3 + 1 ≤ 1024; omega)
  have hc' : callViaEVM evm asset 0 (tokenBalancePayload evm.executionEnv.codeOwner)
      (z, evm', out) false := by
    have ht' : AccountAddress.ofUInt256 (EVM.word asset.val) = asset :=
      accountAddress_roundtrip asset
    simpa only [ht', hs.env] using hc
  refine ⟨evm', σ', z, out, hc', hs', hsize, ?_⟩
  cases z with
  | false =>
      rw [if_neg (by intro h; exact Bool.false_ne_true h.1)]
      exact cometTokenBalanceFailed (v := v) (by change R.length + 1 + 7 ≤ 1024; omega) r2
  | true =>
      obtain ⟨k3, C3, r3⟩ := cometTokenBalanceResponseStart (v := v)
        (by change R.length + 1 + 5 ≤ 1024; omega) r2
      by_cases hlen : 32 ≤ out.size
      · obtain ⟨aw4, k4, C4, dummy, r4⟩ := cometTokenBalanceFull (v := v)
          (by change R.length + 1 + 10 ≤ 1024; omega) hlo hptr hlen
          (lt_trans hsize (by change 2^138 < 2^256; decide)) r3
        have hr := cometCollateralSubtract (v := v) asset (by omega) hret r4
        have hsupply : collateralSupply evm' asset = low128 (totalsCollateralWord σ' ee asset) := by
          unfold collateralSupply
          rw [hs'.storageRead]
          rfl
        simpa only [CollateralReservesValid, hsupply, hlen, and_self, true_and,
          collateralReservesValue] using hr
      · rw [if_neg (fun hv ↦ hlen hv.2.1)]
        exact cometTokenBalanceShort (v := v)
          (by change R.length + 1 + 10 ≤ 1024; omega) (by omega) (Nat.lt_of_not_ge hlen) r3

end Benchmarks.CompoundIII.Comet
