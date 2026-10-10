import Benchmarks.Morpho.MetaMorphoV1_1.MarketParamsAllocationSetup
import Benchmarks.Morpho.MetaMorphoV1_1.ExtSloadsDecodeABI
import Benchmarks.Morpho.MetaMorphoV1_1.StaticCallSimulation

/-! Share the market-parameter STATICCALL witness with the source semantics. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option autoImplicit false

def marketParamsOutputMem (mem : ByteArray) (ptr : UInt256) (out : ByteArray) : ByteArray :=
  out.write 0 mem ptr.toNat (min (UInt256.ofNat 160) (UInt256.ofNat out.size)).toNat

theorem marketParamsReturnSize {evm evm' : State} {target : AccountAddress}
    {id : UInt256} {out : ByteArray} {ok : Bool}
    (hcall : typedCallViaEVM config evm target "idToMarketParams" 0
      [wordBytes32Value id] (ok, evm', out) false) : out.size < 2 ^ 138 := by
  obtain ⟨input, he, hcall⟩ := hcall
  rw [marketParamsEncode, Option.some.injEq] at he
  subst input
  exact callViaEVM_output_bound hcall (by rw [marketParamsCalldata_size]; decide +kernel)

theorem marketParamsStaticcall {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {ptr id gasArg : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 2 ≤ 1024)
    (hs : SourceState s0 I σ evm)
    (rd : RD (deployedRuntime v) I g s0 ⟨16221⟩
      (gasArg :: UInt256.land (wordsOf (immStore v) "MORPHO") solcAddrMask ::
        ptr :: ⟨36⟩ :: ptr :: ⟨160⟩ :: ptr :: R)
      (marketParamsCallMem mem ptr.toNat id) aw rdata σ k C) :
    ∃ (evm' : State) (ok : Bool) (out : ByteArray) (aw' : UInt256) (k' C' : Nat),
      typedCallViaEVM config evm v.MORPHO "idToMarketParams" 0 [wordBytes32Value id]
        (ok, evm', out) false ∧
      SourceState s0 I evm'.accountMap evm' ∧ out.size < UInt256.size ∧
      RD (deployedRuntime v) I g s0 ⟨16222⟩
        ((if ok then ⟨1⟩ else ⟨0⟩) :: ptr :: R)
        (marketParamsOutputMem (marketParamsCallMem mem ptr.toNat id) ptr out)
        aw' out evm'.accountMap k' C' := by
  have hdec : decode (deployedRuntime v) ⟨16221⟩ = some (.STATICCALL, none) := by
    change decode (immutableLayout.runtime metaMorphoV1_1Bytecode
      (wordsOf (immStore v))) _ = _
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨16221⟩ : UInt256), UInt8.ofNat 250, .STATICCALL, none,
      metaMorphoV1_1Blocks.immutableLayout_inBounds,
      metaMorphoV1_1Blocks.immutableTemplate_size64)
  have htgt : v.MORPHO = AccountAddress.ofUInt256
      (UInt256.land (wordsOf (immStore v) "MORPHO") solcAddrMask) := by
    have hw : UInt256.land (wordsOf (immStore v) "MORPHO") solcAddrMask =
        EVM.word v.MORPHO.val := by
      rw [u256_land_comm, wordsOf_immStore_MORPHO]
      exact solcAddrMask_clean_left (addressWord_val_canonical v.MORPHO)
    rw [hw, accountAddress_ofUInt256_eq_ofNat_toNat]
    exact (accountAddress_of_addressWord_toNat v.MORPHO).symm
  have hcd : config.externalABI.encode? "idToMarketParams" [wordBytes32Value id] =
      some ((marketParamsCallMem mem ptr.toNat id).readWithPadding ptr.toNat
        (⟨36⟩ : UInt256).toNat) := by
    change _ = some ((marketParamsCallMem mem ptr.toNat id).readWithPadding ptr.toNat 36)
    rw [marketParamsEncode, marketParamsCallMem_read]
  exact typedStaticcallSimulation (by simpa only [List.length_cons] using hstack)
    hdec hs htgt hcd rd

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
