import Benchmarks.Morpho.MetaMorphoV1_1.BorrowRateABI
import Benchmarks.Morpho.MetaMorphoV1_1.WordCallMemory
import Benchmarks.Morpho.MetaMorphoV1_1.StaticCallSimulation
import Benchmarks.Morpho.MetaMorphoV1_1.ExtSloadsDecodeABI
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_076

/-! Same-call correspondence for the rate model's bounded-output STATICCALL. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option autoImplicit false

def borrowRateCallMem (mem : ByteArray) (ptr : Nat) (p : MarketParamsData)
    (market : ByteArray) : ByteArray :=
  wordCallMemory mem ptr borrowRateSelectorWord (p.words ++ marketWords market)

theorem borrowRateCallMem_size (mem : ByteArray) (ptr : Nat) (p : MarketParamsData)
    (market : ByteArray) :
    (borrowRateCallMem mem ptr p market).size = max mem.size (ptr + 356) := by
  rw [borrowRateCallMem, wordCallMemory_size _ _ _ (by simp [MarketParamsData.words])]
  simp only [List.length_append, MarketParamsData.words, marketWords, List.length_cons,
    List.length_nil, Nat.reduceAdd, Nat.reduceMul, Nat.add_assoc]

theorem borrowRateCallMem_read (mem : ByteArray) (ptr : Nat) (p : MarketParamsData)
    (market : ByteArray) :
    (borrowRateCallMem mem ptr p market).readWithPadding ptr 356 = borrowRateCalldata p market := by
  have hlen : 4 + 32 * (p.words ++ marketWords market).length = 356 := by
    simp only [List.length_append, MarketParamsData.words, marketWords, List.length_cons,
      List.length_nil]
  simpa only [hlen, show borrowRateSelectorWord.toByteArray.extract 0 4 = borrowRateSelector
      from by decide +kernel] using
    wordCallMemory_read mem ptr borrowRateSelectorWord (p.words ++ marketWords market)

theorem borrowRateCallMem_prefix (mem : ByteArray) (ptr : Nat) (p : MarketParamsData)
    (market : ByteArray) : MemoryPrefix mem (borrowRateCallMem mem ptr p market) ptr :=
  wordCallMemory_prefix _ _ _ _

theorem borrowRateReturnSize {evm evm' : State} {p : MarketParamsData}
    {market out : ByteArray} {ok : Bool} (hc : MarketChecks market)
    (hcall : typedCallViaEVM config evm p.irm "borrowRateView" 0 [p.value, marketValue market]
      (ok, evm', out) false) : out.size < 2 ^ 138 := by
  obtain ⟨input, he, hcall⟩ := hcall
  rw [borrowRateEncode p market hc, Option.some.injEq] at he
  subst input
  exact callViaEVM_output_bound hcall (by rw [borrowRateCalldata_size]; decide +kernel)

theorem borrowRateStaticcall {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem market : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {ptr gasArg : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (p : MarketParamsData)
    (hstack : R.length + 1 ≤ 1024) (hc : MarketChecks market)
    (hs : SourceState s0 I σ evm)
    (rd : RD (deployedRuntime v) I g s0 ⟨17225⟩
      (gasArg :: UInt256.ofNat p.irm.toNat :: ptr :: ⟨356⟩ :: ptr :: ⟨32⟩ :: R)
      (borrowRateCallMem mem ptr.toNat p market) aw rdata σ k C) :
    ∃ (evm' : State) (ok : Bool) (out : ByteArray) (aw' : UInt256) (k' C' : Nat),
      typedCallViaEVM config evm p.irm "borrowRateView" 0 [p.value, marketValue market]
        (ok, evm', out) false ∧
      SourceState s0 I evm'.accountMap evm' ∧ out.size < UInt256.size ∧
      RD (deployedRuntime v) I g s0 ⟨17226⟩ ((if ok then ⟨1⟩ else ⟨0⟩) :: R)
        (out.write 0 (borrowRateCallMem mem ptr.toNat p market) ptr.toNat
          (min (⟨32⟩ : UInt256) (UInt256.ofNat out.size)).toNat)
        aw' out evm'.accountMap k' C' := by
  have hdec : decode (deployedRuntime v) ⟨17225⟩ = some (.STATICCALL, none) := by
    change decode (immutableLayout.runtime metaMorphoV1_1Bytecode
      (wordsOf (immStore v))) _ = _
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨17225⟩ : UInt256), UInt8.ofNat 250, .STATICCALL, none,
      metaMorphoV1_1Blocks.immutableLayout_inBounds,
      metaMorphoV1_1Blocks.immutableTemplate_size64)
  exact typedStaticcallSimulation hstack hdec hs
    (by symm; rw [accountAddress_ofUInt256_eq_ofNat_toNat]
        exact accountAddress_of_word_val p.irm)
    (by change _ = some ((borrowRateCallMem mem ptr.toNat p market).readWithPadding
      ptr.toNat 356); rw [borrowRateEncode p market hc, borrowRateCallMem_read]) rd

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
