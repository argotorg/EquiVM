import Examples.TinyImmutable.Common
import Reasoning.SolmBody

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open TinyImmutable.Immutables

namespace TinyImmutable

/-! ## `owner()` -/

theorem tinyOwnerDecode_empty {v : TinyImmutables} {I : ExecutionEnv}
    (hsz : 4 ≤ I.calldata.size) :
    decodeCalldata ((ownerTransition v).params.map Param.name)
      (transitionSignature (ownerTransition v)).paramTypes I.calldata = some ∅ := by
  show decodeCalldata [] [] I.calldata = some ∅
  exact decodeCalldata_empty_ok hsz

theorem tinyOwnerBodyReturns (v : TinyImmutables) (evm : EVM.State) (locals : Store)
    (h : evm.executionEnv.weiValue = ⟨0⟩) :
    ExecTransitionBody (config v) (contract v) evm locals (ownerTransition v).body
      (.returned { contract := contract v, locals := locals } evm (some [.address v.owner])) := by
  exact ExecFuncBody.execBlockRet <|
    (ABlock.start.requireStep (evalCallvalueEq_true h)).returns (by
      simpa [owner] using
        evalAddrLit (config v) { contract := contract v, locals := locals } evm v.owner)

theorem tinyOwnerReturnEncoding (v : TinyImmutables) :
    encodeReturnValue? addr (.address v.owner) =
      some (UInt256.toByteArray (EVM.Word.ofNat (↑v.owner : Nat))) := by
  have hclean := tinyOwnerWord_clean v
  simpa [addr, hclean, tinyOwnerWord_toNat v, accountAddress_ofNat_val] using
    solcAddressReturnEncoding (addrTy := addr) rfl (EVM.Word.ofNat (↑v.owner : Nat))

theorem tinyOwnerX {cA gh bl σ σ₀ A I} {g : Sat256} (v : TinyImmutables)
    (hreach : ∃ k C, RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) ⟨67⟩ [solcSelectorWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret (patchedRuntime v) g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray (EVM.Word.ofNat (↑v.owner : Nat))) := by
  obtain ⟨_, _, rd67⟩ := hreach
  have rd71 := evm_run rd67 with [
    raw jumpdest (by tiny_decode_at v, ⟨67⟩, 0x5b, .JUMPDEST) (by evm_ov),
    raw push2 ⟨106⟩ (by tiny_decode_at v, ⟨68⟩, 0x61, (.Push .PUSH2)) (by evm_ov)]
  have rd104 := rd71.pushConst (EVM.Word.ofNat (↑v.owner : Nat)) (width := 32)
    (op := .PUSH32) (by decide) (tinyDecodeOwnerWord1 v) (by evm_ov)
  have rd106 := evm_run rd104 with [
    raw dup2 (by tiny_decode_at v, ⟨104⟩, 0x81, .DUP2) (by evm_ov),
    raw jump (by tiny_decode_at v, ⟨105⟩, 0x56, .JUMP) (tinyContains106 v) (by evm_ov)]
  have hret := RD.tinyReturnAddress106 (v := v) (R := [solcSelectorWord I]) rd106
    (by simp only [List.length_singleton]; omega)
  simpa [tinyOwnerWord_clean v] using hret

theorem tinyOwnerBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} (v : TinyImmutables)
    (hcode : I.code = patchedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : (ownerSelBytes == I.calldata.extract 0 4) = true)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor (config v) (contract v) cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz := tinyOwnerSelector_size hsel
  have hd := tinyDispatch_owner v hsel
  have hreach := tinyReachOwnerBody (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
    (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g) v hcode hwv hsz hsize
    hsel
  have hdec := tinyOwnerDecode_empty (v := v) (I := I) hsz
  have hbody :
      ExecTransitionBody (config v) (contract v)
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅
        (ownerTransition v).body
        (.returned { contract := contract v, locals := ∅ }
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (some [.address v.owner])) := by
    exact tinyOwnerBodyReturns v
      (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅
      (by simp only [initState]; exact hwv)
  exact (tinyOwnerX v hreach).reEquivExecution hcode hd hdec hbody hAccounts
    (returnEquiv_of_encode (tinyOwnerReturnEncoding v))

end TinyImmutable
