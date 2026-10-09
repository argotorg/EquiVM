import Examples.TinyImmutable.BlocksProof
import Reasoning.SolmBody

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open TinyImmutable.Immutables
open Reasoning.Immutables (wordsOf)

namespace TinyImmutable

/-! ## `quote(uint256)` -/

def quoteAmountStore (I : ExecutionEnv) : Store :=
  (∅ : Store).insert "amount" (.int (Int.ofNat (calldataWord I.calldata 4).toNat))

def quoteAmountValue (I : ExecutionEnv) : Int :=
  Int.ofNat (calldataWord I.calldata 4).toNat

theorem tinyQuoteDecode_ok {v : TinyImmutables} {I : ExecutionEnv}
    (hsz36 : 36 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4) :
    decodeCalldata (quoteTransition.params.map Param.name)
      (transitionSignature quoteTransition).paramTypes I.calldata =
        some (quoteAmountStore I) := by
  show decodeCalldata ["amount"] [uint256] I.calldata = some (quoteAmountStore I)
  simpa [quoteAmountStore, uint256, calldataWord]
    using decodeCalldata_uint256_ok (cd := I.calldata) (x := "amount") hsz36 hbig

theorem tinyQuoteDecode_none_short {v : TinyImmutables} {I : ExecutionEnv}
    (hshort : I.calldata.size < 36) :
    decodeCalldata (quoteTransition.params.map Param.name)
      (transitionSignature quoteTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["amount"] [uint256] I.calldata = none
  simpa [uint256] using
    decodeCalldata_uint256_none_short (cd := I.calldata) (x := "amount") hshort

theorem tinyQuoteDecode_none_huge {v : TinyImmutables} {I : ExecutionEnv}
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size) :
    decodeCalldata (quoteTransition.params.map Param.name)
      (transitionSignature quoteTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["amount"] [uint256] I.calldata = none
  simpa [uint256] using
    decodeCalldata_uint256_none_huge (cd := I.calldata) (x := "amount") hbig

theorem tinyQuoteBodyReturns (v : TinyImmutables) (evm : EVM.State) (locals : Store)
    (amount : Int)
    (hcv : evm.executionEnv.weiValue = ⟨0⟩)
    (hcaller : evm.executionEnv.source = v.owner)
    (hamount : locals.get? "amount" = some (.int amount)) :
    ExecTransitionBody config contract evm locals quoteTransition.body
      (.returned { contract := contract, locals := locals, immutables := immStore v } evm
        (some [.int ((amount * Int.ofNat v.scale.toNat) % Int.ofNat EVM.wordModulus)]))
      (immStore v) := by
  exact ExecFuncBody.execBlockRet <|
    ((ABlock.start.requireStep (evalCallvalueEq_true hcv)).requireStep (by
      simp only [sender, evalExpr?, envValue, EvalResult.bind, bind, pure, immStore_get_owner,
        EvalResult.ofOption, hcaller]
      simp [evalBinaryOp?])).returns (by
        simp only [wrap256, evalExpr?, EvalResult.bind, bind, pure, immStore_get_scale]
        rw [hamount]
        simp only [EvalResult.ofOption, evalBinaryOp?]
        rw [if_neg]
        · norm_num [EVM.wordModulus, EVM.twoPow])

theorem tinyQuoteBodyRevertsUnauthorized (v : TinyImmutables) (evm : EVM.State) (locals : Store)
    (hcv : evm.executionEnv.weiValue = ⟨0⟩)
    (hcaller : evm.executionEnv.source ≠ v.owner) :
    ExecTransitionBody config contract evm locals quoteTransition.body .reverted
      (immStore v) := by
  exact ExecFuncBody.execBlockRevert <|
    (ABlock.start.requireStep (evalCallvalueEq_true hcv)).requireRevert (by
      simp only [sender, evalExpr?, envValue, EvalResult.bind, bind, pure, immStore_get_owner,
        EvalResult.ofOption]
      simp [evalBinaryOp?, hcaller])

theorem tinyOwnerWord_eq_source_of_caller {I : ExecutionEnv} {v : TinyImmutables}
    (hcaller : I.source = v.owner) :
    UInt256.land (EVM.Word.ofNat (↑v.owner : Nat)) solcAddrMask = solcSourceWord I := by
  unfold solcSourceWord
  rw [hcaller]
  exact tinyOwnerWord_clean v

theorem tinyOwnerWord_ne_source_of_caller_ne {I : ExecutionEnv} {v : TinyImmutables}
    (hcaller : I.source ≠ v.owner) :
    UInt256.land (EVM.Word.ofNat (↑v.owner : Nat)) solcAddrMask ≠ solcSourceWord I := by
  intro h
  apply hcaller
  have hs := solcMaskedAddress_eq_source_of_word_eq
    (w := EVM.Word.ofNat (↑v.owner : Nat)) (I := I) h
  have howner : AccountAddress.ofNat
      (UInt256.land (EVM.Word.ofNat (↑v.owner : Nat)) solcAddrMask).toNat = v.owner := by
    rw [tinyOwnerWord_clean v, tinyOwnerWord_toNat v]
    exact accountAddress_ofNat_val v.owner
  exact hs.symm.trans howner

theorem tinyQuoteReturnEncoding (v : TinyImmutables) (amount : UInt256) :
    encodeReturnValue? uint256
        (.int ((Int.ofNat amount.toNat * Int.ofNat v.scale.toNat) %
          Int.ofNat EVM.wordModulus)) =
      some (UInt256.toByteArray (UInt256.mul amount v.scale)) := by
  have hnat : (UInt256.mul amount v.scale).toNat =
      amount.toNat * v.scale.toNat % UInt256.size := u256_mul_toNat amount v.scale
  have hmod : Int.ofNat ((UInt256.mul amount v.scale).toNat) =
      (Int.ofNat amount.toNat * Int.ofNat v.scale.toNat) % Int.ofNat EVM.wordModulus := by
    rw [hnat]
    norm_num [EVM.wordModulus, EVM.twoPow, UInt256.size]
  rw [← hmod]
  simpa [uint256] using uint256ReturnEncoding (UInt256.mul amount v.scale)

theorem tinyQuoteX_toDecoder {σ σ₀ A I} {g : Sat256} (v : TinyImmutables)
    (hreach : ∃ k C, RD (deployedRuntime v) I g
      (initState σ σ₀ g A I) ⟨148⟩ [solcSelectorWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C) :
    ∃ k C, RD (deployedRuntime v) I g
      (initState σ σ₀ g A I) ⟨396⟩
      [⟨4⟩, UInt256.ofNat I.calldata.size, ⟨162⟩, ⟨167⟩, solcSelectorWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C := by
  obtain ⟨k, C, rd148⟩ := hreach
  have hvalid : (D_J (immutableLayout.runtime tinyImmutableBytecode (wordsOf (immStore v))) 0).contains
      (UInt256.ofNat 396) = true := by
    exact tinyContains396 v
  have h := tinyImmutableBlocks.tinyImmutable_block_148 (immWords := wordsOf (immStore v))
    (by simp) hvalid rd148
  exact ⟨k + 7, C + 23, by
    simpa [tinyImmutableBlocks.tinyImmutable_block_148_stack,
      deployedRuntime] using h⟩

theorem tinyQuoteX_decoded {σ σ₀ A I} {g : Sat256} (v : TinyImmutables)
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hreach : ∃ k C, RD (deployedRuntime v) I g
      (initState σ σ₀ g A I) ⟨148⟩ [solcSelectorWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C) :
    ∃ k C, RD (deployedRuntime v) I g
      (initState σ σ₀ g A I) ⟨220⟩
      [calldataWord I.calldata 4, ⟨167⟩, solcSelectorWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C := by
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ =
      ⟨0⟩ :=
    solcDecodeLenCheckOk_4_32 hsz36 hszhi hsize
  obtain ⟨_, _, rd396⟩ := tinyQuoteX_toDecoder (v := v) hreach
  have hvalid412 : (D_J (immutableLayout.runtime tinyImmutableBytecode (wordsOf (immStore v))) 0).contains
      (UInt256.ofNat 412) = true := by
    exact tinyContains412 v
  have hvalid162 : (D_J (immutableLayout.runtime tinyImmutableBytecode (wordsOf (immStore v))) 0).contains
      (UInt256.ofNat 162) = true := by
    exact tinyContains162 v
  have hvalid220 : (D_J (immutableLayout.runtime tinyImmutableBytecode (wordsOf (immStore v))) 0).contains
      (UInt256.ofNat 220) = true := by
    exact tinyContains220 v
  have rd412 := tinyImmutableBlocks.tinyImmutable_block_396_taken
    (immWords := wordsOf (immStore v)) (by simp) (by
      change UInt256.isZero (UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size)
        ⟨4⟩) ⟨32⟩) ≠ ⟨0⟩
      rw [hslt]
      decide) hvalid412 rd396
  have rd162 := tinyImmutableBlocks.tinyImmutable_block_412
    (immWords := wordsOf (immStore v))
    (by simp [tinyImmutableBlocks.tinyImmutable_block_396_taken_stack])
    hvalid162 rd412
  have rd220 := tinyImmutableBlocks.tinyImmutable_block_162
    (immWords := wordsOf (immStore v))
    (by simp [tinyImmutableBlocks.tinyImmutable_block_412_stack]) hvalid220 rd162
  exact ⟨_, _, by
    simpa [tinyImmutableBlocks.tinyImmutable_block_396_taken_stack,
      tinyImmutableBlocks.tinyImmutable_block_412_stack, calldataWord,
      deployedRuntime] using rd220⟩

theorem tinyQuoteX_decodeRevert {σ σ₀ A I} {g : Sat256} (v : TinyImmutables)
    (hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ =
      ⟨1⟩)
    (hreach : ∃ k C, RD (deployedRuntime v) I g
      (initState σ σ₀ g A I) ⟨148⟩ [solcSelectorWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C) :
    RDrev (deployedRuntime v) g (initState σ σ₀ g A I) := by
  obtain ⟨_, _, rd396⟩ := tinyQuoteX_toDecoder (v := v) hreach
  have rd409 := tinyImmutableBlocks.tinyImmutable_block_396_fallthrough
    (immWords := wordsOf (immStore v)) (by simp)
    (by
      change UInt256.isZero (UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size)
        ⟨4⟩) ⟨32⟩) = ⟨0⟩
      rw [hslt]
      decide) rd396
  have hrev := tinyImmutableBlocks.tinyImmutable_block_409 (immWords := wordsOf (immStore v))
    (by simp [tinyImmutableBlocks.tinyImmutable_block_396_fallthrough_stack]) rd409
  simpa using hrev

theorem tinyQuoteX_shortarg {σ σ₀ A I} {g : Sat256} (v : TinyImmutables)
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 36)
    (hreach : ∃ k C, RD (deployedRuntime v) I g
      (initState σ σ₀ g A I) ⟨148⟩ [solcSelectorWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C) :
    RDrev (deployedRuntime v) g (initState σ σ₀ g A I) := by
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ =
      ⟨1⟩ :=
    solcDecodeLenCheckShort_4_32 hsz4 hshort hsize
  exact tinyQuoteX_decodeRevert (v := v) hslt hreach

theorem tinyQuoteX_hugearg {σ σ₀ A I} {g : Sat256} (v : TinyImmutables)
    (hsize : I.calldata.size < UInt256.size)
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size)
    (hreach : ∃ k C, RD (deployedRuntime v) I g
      (initState σ σ₀ g A I) ⟨148⟩ [solcSelectorWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C) :
    RDrev (deployedRuntime v) g (initState σ σ₀ g A I) := by
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ =
      ⟨1⟩ :=
    solcDecodeLenCheckHuge_4_32 hbig hsize
  exact tinyQuoteX_decodeRevert (v := v) hslt hreach

set_option maxHeartbeats 1000000 in
theorem tinyQuoteX_success {σ σ₀ A I} {g : Sat256} (v : TinyImmutables)
    (hcaller : I.source = v.owner)
    (hreach : ∃ k C, RD (deployedRuntime v) I g
      (initState σ σ₀ g A I) ⟨220⟩
      [calldataWord I.calldata 4, ⟨167⟩, solcSelectorWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C) :
    RDret (deployedRuntime v) g (initState σ σ₀ g A I) σ
      (UInt256.toByteArray (UInt256.mul (calldataWord I.calldata 4) v.scale)) := by
  obtain ⟨k, C, rd220⟩ := hreach
  have heq : UInt256.eq
      (UInt256.land (EVM.Word.ofNat (↑v.owner : Nat)) solcAddrMask)
      (solcSourceWord I) = ⟨1⟩ := by
    rw [tinyOwnerWord_eq_source_of_caller hcaller]
    exact u256_eq_refl (solcSourceWord I)
  have hvalid358 : (D_J (immutableLayout.runtime tinyImmutableBytecode (wordsOf (immStore v))) 0).contains
      (UInt256.ofNat 358) = true := by
    exact tinyContains358 v
  have rd358 := tinyImmutableBlocks.tinyImmutable_block_220_taken
    (immWords := wordsOf (immStore v)) (by simp) (by
      rw [wordsOf_immStore_owner]
      change UInt256.eq (UInt256.land (EVM.Word.ofNat (↑v.owner : Nat)) solcAddrMask)
        (solcSourceWord I) ≠ ⟨0⟩
      rw [heq]
      decide) hvalid358 rd220
  have hvalid167 : (D_J (immutableLayout.runtime tinyImmutableBytecode (wordsOf (immStore v))) 0).contains
      (UInt256.ofNat 167) = true := by
    exact tinyContains167 v
  have rd167' := tinyImmutableBlocks.tinyImmutable_block_358 (immWords := wordsOf (immStore v))
    (by simp) hvalid167 rd358
  have rd167 : RD (deployedRuntime v) I g (initState σ σ₀ g A I) ⟨167⟩
      [EVM.wordOfInt (Int.ofNat v.scale.toNat) * calldataWord I.calldata 4,
        solcSelectorWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ (k + 9 + 6) (C + 30 + 22) := by
    simpa [tinyImmutableBlocks.tinyImmutable_block_358_stack,
      tinyImmutableBlocks.tinyImmutable_block_220_taken_stack, wordsOf_immStore_owner, wordsOf_immStore_scale,
      deployedRuntime] using rd167'
  have hret := RD.tinyBlocksReturnWord167 (v := v) (R := [solcSelectorWord I]) rd167
    (by simp)
  rw [wordOfInt_ofNat_toNat] at hret
  change RDret (deployedRuntime v) g (initState σ σ₀ g A I) σ
    (UInt256.toByteArray (UInt256.mul v.scale (calldataWord I.calldata 4))) at hret
  rw [u256_mul_comm v.scale (calldataWord I.calldata 4)] at hret
  exact hret

set_option maxHeartbeats 1000000 in
theorem tinyQuoteX_unauthorized {σ σ₀ A I} {g : Sat256} (v : TinyImmutables)
    (hcaller : I.source ≠ v.owner)
    (hreach : ∃ k C, RD (deployedRuntime v) I g
      (initState σ σ₀ g A I) ⟨220⟩
      [calldataWord I.calldata 4, ⟨167⟩, solcSelectorWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C) :
    RDrev (deployedRuntime v) g (initState σ σ₀ g A I) := by
  obtain ⟨_, _, rd220⟩ := hreach
  have heq : UInt256.eq
      (UInt256.land (EVM.Word.ofNat (↑v.owner : Nat)) solcAddrMask)
      (solcSourceWord I) = ⟨0⟩ := by
    exact u256_eq_of_ne (tinyOwnerWord_ne_source_of_caller_ne hcaller)
  have rd283 := tinyImmutableBlocks.tinyImmutable_block_220_fallthrough
    (immWords := wordsOf (immStore v)) (by simp) (by
      rw [wordsOf_immStore_owner]
      change UInt256.eq (UInt256.land (EVM.Word.ofNat (↑v.owner : Nat)) solcAddrMask)
        (solcSourceWord I) = ⟨0⟩
      exact heq) rd220
  have hrev := tinyImmutableBlocks.tinyImmutable_block_283 (immWords := wordsOf (immStore v))
    (by simp [tinyImmutableBlocks.tinyImmutable_block_220_fallthrough_stack]) rd283
  simpa using hrev

theorem tinyQuoteBodyCore
    {σ σ₀ A I} {g : UInt256} (v : TinyImmutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (howner : (ownerSelBytes == I.calldata.extract 0 4) = false)
    (hsel : (quoteSelBytes == I.calldata.extract 0 4) = true) :
    runtimeRefinementFor config contract σ σ₀ g A I (immStore v) := by
  have hsz4 := tinyQuoteSelector_size hsel
  have hd := tinyDispatch_quote v howner hsel
  have hreach := tinyBlocksReachQuoteBody (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g) v hcode hwv hsz4 hsize
    howner hsel
  by_cases hshort : I.calldata.size < 36
  · exact (tinyQuoteX_shortarg (g := Sat256.ofUInt256 g) v hsz4 hsize hshort hreach)
      |>.reEquivDecodingFailed hcode hd (tinyQuoteDecode_none_short (v := v) hshort)
  · have hsz36 : 36 ≤ I.calldata.size := by omega
    by_cases hbig : 2 ^ 255 + 4 ≤ I.calldata.size
    · exact (tinyQuoteX_hugearg (g := Sat256.ofUInt256 g) v hsize hbig hreach)
        |>.reEquivDecodingFailed hcode hd (tinyQuoteDecode_none_huge (v := v) hbig)
    · have hszhi : I.calldata.size < 2 ^ 255 + 4 := by omega
      have hdec := tinyQuoteDecode_ok (v := v) (I := I) hsz36 hszhi
      obtain ⟨_, _, rd220⟩ := tinyQuoteX_decoded (g := Sat256.ofUInt256 g) v hsz36
        hsize hszhi hreach
      by_cases hcaller : I.source = v.owner
      · have hbody :
            ExecTransitionBody config contract
              (initState σ σ₀ (Sat256.ofUInt256 g) A I)
              (quoteAmountStore I) quoteTransition.body
              (.returned
                { contract := contract, locals := quoteAmountStore I, immutables := immStore v }
                (initState σ σ₀ (Sat256.ofUInt256 g) A I)
                (some [.int ((quoteAmountValue I * Int.ofNat v.scale.toNat) %
                  Int.ofNat EVM.wordModulus)])) (immStore v) := by
          exact tinyQuoteBodyReturns v
            (initState σ σ₀ (Sat256.ofUInt256 g) A I) (quoteAmountStore I)
            (quoteAmountValue I)
            (by simp only [initState]; exact hwv)
            (by simp only [initState]; exact hcaller)
            (by simp [quoteAmountStore, quoteAmountValue])
        exact (tinyQuoteX_success (g := Sat256.ofUInt256 g) v hcaller ⟨_, _, rd220⟩)
          |>.reEquivExecution hcode hd hdec hbody
            (returnEquiv_of_encode
              (by simpa [quoteAmountValue] using
                tinyQuoteReturnEncoding v (calldataWord I.calldata 4)))
      · have hbody :
            ExecTransitionBody config contract
              (initState σ σ₀ (Sat256.ofUInt256 g) A I)
              (quoteAmountStore I) quoteTransition.body .reverted (immStore v) := by
          exact tinyQuoteBodyRevertsUnauthorized v
            (initState σ σ₀ (Sat256.ofUInt256 g) A I) (quoteAmountStore I)
            (by simp only [initState]; exact hwv)
            (by simp only [initState]; exact hcaller)
        exact (tinyQuoteX_unauthorized (g := Sat256.ofUInt256 g) v hcaller ⟨_, _, rd220⟩)
          |>.reEquivExecutionRevert hcode hd hdec hbody

end TinyImmutable
