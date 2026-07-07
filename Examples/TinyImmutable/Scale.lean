import Examples.TinyImmutable.Common
import Reasoning.SolmBody

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open TinyImmutable.Immutables

namespace TinyImmutable

/-! ## `scale()` -/

theorem tinyScaleDecode_empty {v : TinyImmutables} {I : ExecutionEnv}
    (hsz : 4 ≤ I.calldata.size) :
    decodeCalldata ((scaleTransition v).params.map Param.name)
      (transitionSignature (scaleTransition v)).paramTypes I.calldata = some ∅ := by
  show decodeCalldata [] [] I.calldata = some ∅
  exact decodeCalldata_empty_ok hsz

theorem tinyScaleBodyReturns (v : TinyImmutables) (evm : EVM.State) (locals : Store)
    (h : evm.executionEnv.weiValue = ⟨0⟩) :
    ExecTransitionBody (config v) (contract v) evm locals (scaleTransition v).body
      (.returned { contract := contract v, locals := locals } evm
        (some [.int (Int.ofNat v.scale.toNat)])) := by
  exact ExecFuncBody.execBlockRet <|
    (ABlock.start.requireStep (evalCallvalueEq_true h)).returns (by
      simp [scale, evalExpr?, pure])

theorem tinyScaleX {cA gh bl σ σ₀ A I} {g : Sat256} (v : TinyImmutables)
    (hreach : ∃ k C, RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) ⟨181⟩ [solcSelectorWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret (patchedRuntime v) g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray v.scale) := by
  obtain ⟨_, _, rd181⟩ := hreach
  have rd185 := evm_run rd181 with [
    raw jumpdest (by tiny_decode_at v, ⟨181⟩, 0x5b, .JUMPDEST) (by evm_ov),
    raw push2 ⟨167⟩ (by tiny_decode_at v, ⟨182⟩, 0x61, (.Push .PUSH2)) (by evm_ov)]
  have rd218 := rd185.pushConst (EVM.wordOfInt (Int.ofNat v.scale.toNat)) (width := 32)
    (op := .PUSH32) (by decide) (tinyDecodeScaleWord1 v) (by evm_ov)
  have rd167 := evm_run rd218 with [
    raw dup2 (by tiny_decode_at v, ⟨218⟩, 0x81, .DUP2) (by evm_ov),
    raw jump (by tiny_decode_at v, ⟨219⟩, 0x56, .JUMP) (tinyContains167 v) (by evm_ov)]
  have hret := RD.tinyReturnWord167 (v := v) (R := [⟨167⟩, solcSelectorWord I]) rd167
    (by simp)
  rw [wordOfInt_ofNat_toNat] at hret
  exact hret

theorem tinyScaleBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} (v : TinyImmutables)
    (hcode : I.code = patchedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (howner : (ownerSelBytes == I.calldata.extract 0 4) = false)
    (hquote : (quoteSelBytes == I.calldata.extract 0 4) = false)
    (hsel : (scaleSelBytes == I.calldata.extract 0 4) = true)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor (config v) (contract v) cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz := tinyScaleSelector_size hsel
  have hd := tinyDispatch_scale v howner hquote hsel
  have hreach := tinyReachScaleBody (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
    (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g) v hcode hwv hsz hsize
    howner hquote hsel
  have hdec := tinyScaleDecode_empty (v := v) (I := I) hsz
  have hbody :
      ExecTransitionBody (config v) (contract v)
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅
        (scaleTransition v).body
        (.returned { contract := contract v, locals := ∅ }
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (some [.int (Int.ofNat v.scale.toNat)])) := by
    exact tinyScaleBodyReturns v
      (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅
      (by simp only [initState]; exact hwv)
  exact (tinyScaleX v hreach).reEquivExecution hcode hd hdec hbody hAccounts
    (returnEquiv_of_encode (by simpa [uint256] using uint256ReturnEncoding v.scale))

end TinyImmutable
