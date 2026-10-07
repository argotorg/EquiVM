import Examples.TinyImmutable.BlocksProof
import Reasoning.SolmBody

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open TinyImmutable.Immutables
open Reasoning.Immutables (wordsOf)

namespace TinyImmutable

/-! ## `owner()` -/

theorem tinyOwnerDecode_empty {v : TinyImmutables} {I : ExecutionEnv}
    (hsz : 4 ≤ I.calldata.size) :
    decodeCalldata (ownerTransition.params.map Param.name)
      (transitionSignature ownerTransition).paramTypes I.calldata = some ∅ := by
  show decodeCalldata [] [] I.calldata = some ∅
  exact decodeCalldata_empty_ok hsz

theorem tinyOwnerBodyReturns (v : TinyImmutables) (evm : EVM.State) (locals : Store)
    (h : evm.executionEnv.weiValue = ⟨0⟩) :
    ExecTransitionBody config contract evm locals ownerTransition.body
      (.returned { contract := contract, locals := locals, immutables := immStore v } evm
        (some [.address v.owner])) (immStore v) := by
  exact ExecFuncBody.execBlockRet <|
    (ABlock.start.requireStep (evalCallvalueEq_true h)).returns (by
      simp [evalExprs?, evalImmutable_owner, pure])

theorem tinyOwnerReturnEncoding (v : TinyImmutables) :
    encodeReturnValue? addr (.address v.owner) =
      some (UInt256.toByteArray (EVM.Word.ofNat (↑v.owner : Nat))) := by
  have hclean := tinyOwnerWord_clean v
  simpa [addr, hclean, tinyOwnerWord_toNat v, accountAddress_ofNat_val] using
    solcAddressReturnEncoding (addrTy := addr) rfl (EVM.Word.ofNat (↑v.owner : Nat))

theorem tinyOwnerX {σ σ₀ A I} {g : Sat256} (v : TinyImmutables)
    (hreach : ∃ k C, RD (patchedRuntime v) I g
      (initState σ σ₀ g A I) ⟨67⟩ [solcSelectorWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C) :
    RDret (patchedRuntime v) g (initState σ σ₀ g A I) σ
      (UInt256.toByteArray (EVM.Word.ofNat (↑v.owner : Nat))) := by
  obtain ⟨k, C, rd67⟩ := hreach
  have rd106 : RD (patchedRuntime v) I g (initState σ σ₀ g A I) ⟨106⟩
      [EVM.Word.ofNat (↑v.owner : Nat), ⟨106⟩, solcSelectorWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ (k + 5) (C + 18) := by
    have hvalid : (D_J (immutableLayout.runtime tinyImmutableBytecode (wordsOf (immStore v))) 0).contains
        (UInt256.ofNat 106) = true := by
      exact tinyContains106 v
    have h := tinyImmutableBlocks.tinyImmutable_block_67 (immWords := wordsOf (immStore v))
      (by simp) hvalid rd67
    simpa [tinyImmutableBlocks.tinyImmutable_block_67_stack, wordsOf_immStore_owner, wordsOf_immStore_scale,
      patchedRuntime] using h
  have hret := RD.tinyBlocksReturnAddress106 (v := v) (R := [solcSelectorWord I]) rd106
    (by simp only [List.length_singleton]; omega)
  simpa [tinyOwnerWord_clean v] using hret

theorem tinyOwnerBodyCore
    {σ σ₀ A I} {g : UInt256} (v : TinyImmutables)
    (hcode : I.code = patchedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : (ownerSelBytes == I.calldata.extract 0 4) = true) :
    runtimeRefinementFor config contract σ σ₀ g A I (immStore v) := by
  have hsz := tinyOwnerSelector_size hsel
  have hd := tinyDispatch_owner v hsel
  have hreach := tinyBlocksReachOwnerBody (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g) v hcode hwv hsz hsize
    hsel
  have hdec := tinyOwnerDecode_empty (v := v) (I := I) hsz
  have hbody :
      ExecTransitionBody config contract
        (initState σ σ₀ (Sat256.ofUInt256 g) A I) ∅
        ownerTransition.body
        (.returned { contract := contract, locals := ∅, immutables := immStore v }
          (initState σ σ₀ (Sat256.ofUInt256 g) A I)
          (some [.address v.owner])) (immStore v) := by
    exact tinyOwnerBodyReturns v
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) ∅
      (by simp only [initState]; exact hwv)
  exact (tinyOwnerX v hreach).reEquivExecution hcode hd hdec hbody
    (returnEquiv_of_encode (tinyOwnerReturnEncoding v))

end TinyImmutable
