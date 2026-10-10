import Benchmarks.Morpho.MetaMorphoV1_1.SingleWordCallMemory
import Benchmarks.Morpho.MetaMorphoV1_1.BorrowRateABI
import Benchmarks.Morpho.MetaMorphoV1_1.StaticCallSimulation
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_088

/-! The token balance request and its exact bounded-output STATICCALL. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option autoImplicit false

def tokenBalanceSelector : ByteArray := ⟨#[0x70, 0xa0, 0x82, 0x31]⟩

def tokenBalanceSelectorWord : UInt256 := UInt256.shiftLeft ⟨1889567281⟩ ⟨224⟩

def tokenBalanceCalldata (owner : AccountAddress) : ByteArray :=
  tokenBalanceSelector ++ (UInt256.ofNat owner.toNat).toByteArray

theorem tokenBalanceCalldata_size (owner : AccountAddress) :
    (tokenBalanceCalldata owner).size = 36 := by
  simp only [tokenBalanceCalldata, ByteArray.size_append, toByteArray_size]
  rfl

-- LIBRARY CANDIDATE: a selector followed by one canonically encoded address.
theorem singleAddressCallEncode (selector : ByteArray) (owner : AccountAddress) :
    encodeCallWithSelector? selector [abiAddress] [.address owner] =
      some (selector ++ (UInt256.ofNat owner.toNat).toByteArray) := by
  simp only [encodeCallWithSelector?, encodeABIValues?, encodeABIValuesFrom?,
    encodeAddressWord,
    show abiTupleHeadSize? [abiAddress] = some 32 from by
      simp [abiTupleHeadSize?, isDynamicABIType, staticABIEncodedSize?, abiAddress],
    show isDynamicABIType abiAddress = false from rfl, bind, Option.bind,
    Bool.false_eq_true, if_false, List.nil_append, List.append_nil,
    byteArray_toList_toByteArray]

theorem tokenBalanceEncode (owner : AccountAddress) :
    config.externalABI.encode? "balanceOf" [.address owner] =
      some (tokenBalanceCalldata owner) := by
  change encodeCallWithSelector?
    (ByteArray.mk ((EVM.Word.ofNat 0x70a08231).toBytesBE.drop 28).toArray)
    [abiAddress] [.address owner] = _
  rw [show ByteArray.mk ((EVM.Word.ofNat 0x70a08231).toBytesBE.drop 28).toArray =
    tokenBalanceSelector from by decide +kernel]
  exact singleAddressCallEncode tokenBalanceSelector owner

def tokenBalanceCallMem (mem : ByteArray) (ptr : Nat) (owner : AccountAddress) : ByteArray :=
  singleWordCallMem mem ptr tokenBalanceSelectorWord (UInt256.ofNat owner.toNat)

theorem tokenBalanceCallMem_size (mem : ByteArray) (ptr : Nat) (owner : AccountAddress) :
    (tokenBalanceCallMem mem ptr owner).size = max mem.size (ptr + 36) :=
  singleWordCallMem_size mem ptr tokenBalanceSelectorWord (UInt256.ofNat owner.toNat)

theorem tokenBalanceCallMem_read (mem : ByteArray) (ptr : Nat) (owner : AccountAddress) :
    (tokenBalanceCallMem mem ptr owner).readWithPadding ptr 36 = tokenBalanceCalldata owner := by
  simpa only [show tokenBalanceSelectorWord.toByteArray.extract 0 4 =
    tokenBalanceSelector from by decide +kernel] using
      singleWordCallMem_read mem ptr tokenBalanceSelectorWord (UInt256.ofNat owner.toNat)

theorem tokenBalanceDecode {out : ByteArray} (hh : out.size < 2 ^ 255) :
    config.externalABI.decode? "balanceOf" out =
      if 32 ≤ out.size then some [uint256Value (calldataWord out 0)] else none :=
  borrowRateDecode hh

theorem tokenBalanceStaticcall {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {ptr gasArg : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (token owner : AccountAddress)
    (hstack : R.length + 1 ≤ 1024) (hs : SourceState s0 I σ evm)
    (rd : RD (deployedRuntime v) I g s0 ⟨19570⟩
      (gasArg :: UInt256.ofNat token.toNat :: ptr :: ⟨36⟩ :: ptr :: ⟨32⟩ :: R)
      (tokenBalanceCallMem mem ptr.toNat owner) aw rdata σ k C) :
    ∃ (evm' : State) (ok : Bool) (out : ByteArray) (aw' : UInt256) (k' C' : Nat),
      typedCallViaEVM config evm token "balanceOf" 0 [.address owner]
        (ok, evm', out) false ∧
      SourceState s0 I evm'.accountMap evm' ∧ out.size < UInt256.size ∧
      RD (deployedRuntime v) I g s0 ⟨19571⟩ ((if ok then ⟨1⟩ else ⟨0⟩) :: R)
        (out.write 0 (tokenBalanceCallMem mem ptr.toNat owner) ptr.toNat
          (min (⟨32⟩ : UInt256) (UInt256.ofNat out.size)).toNat)
        aw' out evm'.accountMap k' C' := by
  have hdec : decode (deployedRuntime v) ⟨19570⟩ = some (.STATICCALL, none) := by
    change decode (immutableLayout.runtime metaMorphoV1_1Bytecode
      (wordsOf (immStore v))) _ = _
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨19570⟩ : UInt256), UInt8.ofNat 250, .STATICCALL, none,
      metaMorphoV1_1Blocks.immutableLayout_inBounds,
      metaMorphoV1_1Blocks.immutableTemplate_size64)
  exact typedStaticcallSimulation hstack hdec hs
    (by symm; rw [accountAddress_ofUInt256_eq_ofNat_toNat]
        exact accountAddress_of_word_val token)
    (by change _ = some ((tokenBalanceCallMem mem ptr.toNat owner).readWithPadding
      ptr.toNat 36); rw [tokenBalanceEncode owner, tokenBalanceCallMem_read]) rd

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
