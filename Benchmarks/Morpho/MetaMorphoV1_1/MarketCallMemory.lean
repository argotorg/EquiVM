import Benchmarks.Morpho.MetaMorphoV1_1.MarketParamsHashSource
import Benchmarks.Morpho.MetaMorphoV1_1.SingleWordCallMemory
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_076

/-! The market identifier hash, request bytes, and compiled STATICCALL setup. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option autoImplicit false

def marketSelector : ByteArray := ⟨#[0x5c, 0x60, 0xe3, 0x9a]⟩

def marketSelectorWord : UInt256 := UInt256.shiftLeft ⟨774926797⟩ ⟨225⟩

def marketCalldata (id : UInt256) : ByteArray := marketSelector ++ id.toByteArray

def marketCallMem (mem : ByteArray) (ptr : Nat) (id : UInt256) : ByteArray :=
  singleWordCallMem mem ptr marketSelectorWord id

theorem marketCalldata_size (id : UInt256) : (marketCalldata id).size = 36 := by
  simp only [marketCalldata, ByteArray.size_append, toByteArray_size]
  rfl

theorem marketEncode (id : UInt256) :
    config.externalABI.encode? "market" [wordBytes32Value id] = some (marketCalldata id) := by
  change encodeCallWithSelector?
    (ByteArray.mk ((EVM.Word.ofNat 0x5c60e39a).toBytesBE.drop 28).toArray)
    [abiBytes32] [wordBytes32Value id] = _
  rw [show ByteArray.mk ((EVM.Word.ofNat 0x5c60e39a).toBytesBE.drop 28).toArray =
    marketSelector from by decide +kernel]
  exact singleWordCallEncode marketSelector id

theorem marketCallMem_size (mem : ByteArray) (ptr : Nat) (id : UInt256) :
    (marketCallMem mem ptr id).size = max mem.size (ptr + 36) :=
  singleWordCallMem_size mem ptr marketSelectorWord id

theorem marketCallMem_read (mem : ByteArray) (ptr : Nat) (id : UInt256) :
    (marketCallMem mem ptr id).readWithPadding ptr 36 = marketCalldata id := by
  simpa only [show marketSelectorWord.toByteArray.extract 0 4 = marketSelector from by
    decide +kernel] using singleWordCallMem_read mem ptr marketSelectorWord id

theorem marketReachStaticcall {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {ptr params morpho : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (p : MarketParamsData) (hstack : R.length + 10 ≤ 1024)
    (hfree : memLoad ⟨64⟩ mem = ptr) (hptr : ptr.toNat < 2 ^ 64)
    (hparams : mem.readWithPadding params.toNat 160 = p.bytes)
    (rd : RD (deployedRuntime v) I g s0 ⟨16911⟩ (morpho :: params :: R)
      mem aw rdata σ k C) :
    ∃ gasArg aw' k' C', RD (deployedRuntime v) I g s0 ⟨16952⟩
      (gasArg :: UInt256.land solcAddrMask morpho :: ptr :: ⟨36⟩ :: ptr :: ⟨192⟩ ::
        params :: ptr :: R) (marketCallMem mem ptr.toNat p.id) aw' rdata σ k' C' := by
  obtain ⟨aw', k', C', hr⟩ := metaMorphoV1_1_block_16911_packed
    (immWords := wordsOf (immStore v)) hstack rd
  have hfree' : memLoad (UInt256.ofNat 64) mem = ptr := hfree
  have h4 : (ptr + UInt256.ofNat 4).toNat = ptr.toNat + 4 :=
    uadd_word_ofNat_toNat ptr 4 (by change _ < 2 ^ 256; omega)
  have hhash : keccakWord params (UInt256.ofNat 160) mem = p.id := by
    simp only [keccakWord, show (UInt256.ofNat 160).toNat = 160 from rfl, hparams,
      MarketParamsData.id, uInt256OfByteArray_eq]
  simp only [metaMorphoV1_1_block_16911_stack, metaMorphoV1_1_block_16911_memory,
    hfree', h4, hhash] at hr
  exact ⟨_, aw', k', C', hr⟩

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
