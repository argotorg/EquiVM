import Benchmarks.CompoundIII.Comet.PriceResponseEvm

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 10000

theorem cometPriceInternal {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem rdata : ByteArray} {aw : UInt256}
    {σ : AccountMap} {k C : Nat} {ptr ret : UInt256} {R : List UInt256} {evm : EVM.State}
    (addr : AccountAddress) (hstack : R.length + 12 ≤ 1024)
    (hfree : memLoad ⟨64⟩ mem = ptr) (hlo : 96 ≤ ptr.toNat)
    (hgap : ptr.toNat ≤ mem.size + 32) (hptr : ptr.toNat + 160 < 2^64)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (hs : SourceState s0 ee σ evm)
    (h : RD (deployedRuntime v) ee g s0 ⟨9375⟩ (EVM.word addr.val :: ret :: R)
      mem aw rdata σ k C) :
    ∃ (evm' : EVM.State) (σ' : AccountMap) (z : Bool) (out : ByteArray),
      callViaEVM evm addr 0 pricePayload (z, evm', out) false ∧
      SourceState s0 ee σ' evm' ∧ out.size < 2^138 ∧
      if z = true ∧ PriceValid out then
        ∃ aw' k' C', RD (deployedRuntime v) ee g s0 ret (calldataWord out 32 :: R)
          (priceReturnMemory mem ptr out) aw' out σ' k' C'
      else RDrev (deployedRuntime v) g s0 := by
  have r1 := cometWithExtendedAssetList_block_9375
    (immWords := wordsOf (immStore v)) (by change R.length + 1 + 9 ≤ 1024; omega) h
  have hm : UInt256.land
      (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
        (UInt256.ofNat 1)) (EVM.word addr.val) = EVM.word addr.val :=
    solcAddrMask_clean_left (addressWord_val_canonical addr)
  have hf : memLoad (UInt256.ofNat 64) mem = ptr := hfree
  simp only [cometWithExtendedAssetList_block_9375_stack,
    cometWithExtendedAssetList_block_9375_memory, hf, hm] at r1
  obtain ⟨evm', σ', z, out, k2, C2, hc, hs', r2, hsize⟩ := staticCallBridge r1 hs
    (by immutable_decode(immutableLayout, cometWithExtendedAssetListBytecode,
      wordsOf (immStore v), (⟨9410⟩ : UInt256), UInt8.ofNat 250, .STATICCALL, none,
      immutableLayout_inBounds, immutableTemplate_size64))
    (priceInputMemory_payload hgap) (by decide)
    (by change R.length + 2 + 1 ≤ 1024; omega)
  have hc' : callViaEVM evm addr 0 pricePayload (z, evm', out) false := by
    have ht : AccountAddress.ofUInt256 (EVM.word addr.val) = addr := accountAddress_roundtrip addr
    simpa only [ht] using hc
  refine ⟨evm', σ', z, out, hc', hs', hsize, ?_⟩
  exact cometPriceResponse (v := v) hstack hlo hgap hptr
    (lt_trans hsize (by change 2^138 < 2^256; decide)) hret r2

end Benchmarks.CompoundIII.Comet
