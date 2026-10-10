import Benchmarks.Morpho.MetaMorphoV1_1.MarketCallMemory
import Benchmarks.Morpho.MetaMorphoV1_1.StaticCallSimulation
import Benchmarks.Morpho.MetaMorphoV1_1.ExtSloadsDecodeABI

/-! Same-call correspondence for the market reader's bounded-output STATICCALL. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option autoImplicit false

def marketOutputMem (mem : ByteArray) (ptr : UInt256) (out : ByteArray) : ByteArray :=
  out.write 0 mem ptr.toNat (min (UInt256.ofNat 192) (UInt256.ofNat out.size)).toNat

theorem marketReturnSize {evm evm' : State} {target : AccountAddress}
    {id : UInt256} {out : ByteArray} {ok : Bool}
    (hcall : typedCallViaEVM config evm target "market" 0 [wordBytes32Value id]
      (ok, evm', out) false) : out.size < 2 ^ 138 := by
  obtain ⟨input, he, hcall⟩ := hcall
  rw [marketEncode, Option.some.injEq] at he
  subst input
  exact callViaEVM_output_bound hcall (by rw [marketCalldata_size]; decide +kernel)

theorem marketStaticcall {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {ptr params id morpho gasArg : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 3 ≤ 1024)
    (hs : SourceState s0 I σ evm)
    (rd : RD (deployedRuntime v) I g s0 ⟨16952⟩
      (gasArg :: UInt256.land solcAddrMask morpho :: ptr :: ⟨36⟩ :: ptr :: ⟨192⟩ ::
        params :: ptr :: R) (marketCallMem mem ptr.toNat id) aw rdata σ k C) :
    ∃ (evm' : State) (ok : Bool) (out : ByteArray) (aw' : UInt256) (k' C' : Nat),
      typedCallViaEVM config evm (AccountAddress.ofNat morpho.toNat) "market" 0
        [wordBytes32Value id] (ok, evm', out) false ∧
      SourceState s0 I evm'.accountMap evm' ∧ out.size < UInt256.size ∧
      RD (deployedRuntime v) I g s0 ⟨16953⟩
        ((if ok then ⟨1⟩ else ⟨0⟩) :: params :: ptr :: R)
        (marketOutputMem (marketCallMem mem ptr.toNat id) ptr out)
        aw' out evm'.accountMap k' C' := by
  have hdec : decode (deployedRuntime v) ⟨16952⟩ = some (.STATICCALL, none) := by
    change decode (immutableLayout.runtime metaMorphoV1_1Bytecode
      (wordsOf (immStore v))) _ = _
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨16952⟩ : UInt256), UInt8.ofNat 250, .STATICCALL, none,
      metaMorphoV1_1Blocks.immutableLayout_inBounds,
      metaMorphoV1_1Blocks.immutableTemplate_size64)
  have htgt : AccountAddress.ofNat morpho.toNat =
      AccountAddress.ofUInt256 (UInt256.land solcAddrMask morpho) := by
    rw [u256_land_comm solcAddrMask morpho, ← accountAddress_masked_ofNat_toNat,
      ← addressOfNat_eq_of_masked_word]
  exact typedStaticcallSimulation (by simpa only [List.length_cons] using hstack)
    hdec hs htgt (by change _ = some ((marketCallMem mem ptr.toNat id).readWithPadding
      ptr.toNat 36); rw [marketEncode, marketCallMem_read]) rd

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
