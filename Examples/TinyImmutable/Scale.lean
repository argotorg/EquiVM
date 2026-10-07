import Examples.TinyImmutable.BlocksProof
import Reasoning.SolmBody

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open TinyImmutable.Immutables
open Reasoning.Immutables (wordsOf)

namespace TinyImmutable

/-! ## `scale()` -/

theorem tinyScaleDecode_empty {v : TinyImmutables} {I : ExecutionEnv}
    (hsz : 4 ≤ I.calldata.size) :
    decodeCalldata (scaleTransition.params.map Param.name)
      (transitionSignature scaleTransition).paramTypes I.calldata = some ∅ := by
  show decodeCalldata [] [] I.calldata = some ∅
  exact decodeCalldata_empty_ok hsz

theorem tinyScaleBodyReturns (v : TinyImmutables) (evm : EVM.State) (locals : Store)
    (h : evm.executionEnv.weiValue = ⟨0⟩) :
    ExecTransitionBody config contract evm locals scaleTransition.body
      (.returned { contract := contract, locals := locals, immutables := immStore v } evm
        (some [.int (Int.ofNat v.scale.toNat)])) (immStore v) := by
  exact ExecFuncBody.execBlockRet <|
    (ABlock.start.requireStep (evalCallvalueEq_true h)).returns (by
      simp [evalExprs?, evalImmutable_scale, pure])

theorem tinyScaleX {σ σ₀ A I} {g : Sat256} (v : TinyImmutables)
    (hreach : ∃ k C, RD (deployedRuntime v) I g
      (initState σ σ₀ g A I) ⟨181⟩ [solcSelectorWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C) :
    RDret (deployedRuntime v) g (initState σ σ₀ g A I) σ
      (UInt256.toByteArray v.scale) := by
  obtain ⟨k, C, rd181⟩ := hreach
  have rd167 : RD (deployedRuntime v) I g (initState σ σ₀ g A I) ⟨167⟩
      [EVM.wordOfInt (Int.ofNat v.scale.toNat), ⟨167⟩, solcSelectorWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ (k + 5) (C + 18) := by
    have hvalid : (D_J (immutableLayout.runtime tinyImmutableBytecode (wordsOf (immStore v))) 0).contains
        (UInt256.ofNat 167) = true := by
      exact tinyContains167 v
    have h := tinyImmutableBlocks.tinyImmutable_block_181 (immWords := wordsOf (immStore v))
      (by simp) hvalid rd181
    simpa [tinyImmutableBlocks.tinyImmutable_block_181_stack, wordsOf_immStore_owner, wordsOf_immStore_scale,
      deployedRuntime] using h
  have hret := RD.tinyBlocksReturnWord167 (v := v) (R := [⟨167⟩, solcSelectorWord I]) rd167
    (by simp)
  rw [wordOfInt_ofNat_toNat] at hret
  exact hret

theorem tinyScaleBodyCore
    {σ σ₀ A I} {g : UInt256} (v : TinyImmutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (howner : (ownerSelBytes == I.calldata.extract 0 4) = false)
    (hquote : (quoteSelBytes == I.calldata.extract 0 4) = false)
    (hsel : (scaleSelBytes == I.calldata.extract 0 4) = true) :
    runtimeRefinementFor config contract σ σ₀ g A I (immStore v) := by
  have hsz := tinyScaleSelector_size hsel
  have hd := tinyDispatch_scale v howner hquote hsel
  have hreach := tinyBlocksReachScaleBody (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g) v hcode hwv hsz hsize
    howner hquote hsel
  have hdec := tinyScaleDecode_empty (v := v) (I := I) hsz
  have hbody :
      ExecTransitionBody config contract
        (initState σ σ₀ (Sat256.ofUInt256 g) A I) ∅
        scaleTransition.body
        (.returned { contract := contract, locals := ∅, immutables := immStore v }
          (initState σ σ₀ (Sat256.ofUInt256 g) A I)
          (some [.int (Int.ofNat v.scale.toNat)])) (immStore v) := by
    exact tinyScaleBodyReturns v
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) ∅
      (by simp only [initState]; exact hwv)
  exact (tinyScaleX v hreach).reEquivExecution hcode hd hdec hbody
    (returnEquiv_of_encode (by simpa [uint256] using uint256ReturnEncoding v.scale))

end TinyImmutable
