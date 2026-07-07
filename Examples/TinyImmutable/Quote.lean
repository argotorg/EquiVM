import Examples.TinyImmutable.Common
import Reasoning.SolmBody

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open TinyImmutable.Immutables

namespace TinyImmutable

/-! ## `quote(uint256)` -/

def quoteAmountStore (I : ExecutionEnv) : Store :=
  (∅ : Store).insert "amount" (.int (Int.ofNat (calldataWord I.calldata 4).toNat))

def quoteAmountValue (I : ExecutionEnv) : Int :=
  Int.ofNat (calldataWord I.calldata 4).toNat

theorem tinyQuoteDecode_ok {v : TinyImmutables} {I : ExecutionEnv}
    (hsz36 : 36 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4) :
    decodeCalldata ((quoteTransition v).params.map Param.name)
      (transitionSignature (quoteTransition v)).paramTypes I.calldata =
        some (quoteAmountStore I) := by
  show decodeCalldata ["amount"] [uint256] I.calldata = some (quoteAmountStore I)
  simpa [quoteAmountStore, uint256, calldataWord]
    using decodeCalldata_uint256_ok (cd := I.calldata) (x := "amount") hsz36 hbig

theorem tinyQuoteDecode_none_short {v : TinyImmutables} {I : ExecutionEnv}
    (hshort : I.calldata.size < 36) :
    decodeCalldata ((quoteTransition v).params.map Param.name)
      (transitionSignature (quoteTransition v)).paramTypes I.calldata = none := by
  show decodeCalldata ["amount"] [uint256] I.calldata = none
  simpa [uint256] using
    decodeCalldata_uint256_none_short (cd := I.calldata) (x := "amount") hshort

theorem tinyQuoteDecode_none_huge {v : TinyImmutables} {I : ExecutionEnv}
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size) :
    decodeCalldata ((quoteTransition v).params.map Param.name)
      (transitionSignature (quoteTransition v)).paramTypes I.calldata = none := by
  show decodeCalldata ["amount"] [uint256] I.calldata = none
  simpa [uint256] using
    decodeCalldata_uint256_none_huge (cd := I.calldata) (x := "amount") hbig

theorem tinyQuoteBodyReturns (v : TinyImmutables) (evm : EVM.State) (locals : Store)
    (amount : Int)
    (hcv : evm.executionEnv.weiValue = ⟨0⟩)
    (hcaller : evm.executionEnv.source = v.owner)
    (hamount : locals.get? "amount" = some (.int amount)) :
    ExecTransitionBody (config v) (contract v) evm locals (quoteTransition v).body
      (.returned { contract := contract v, locals := locals } evm
        (some [.int ((amount * Int.ofNat v.scale.toNat) % Int.ofNat EVM.wordModulus)])) := by
  exact ExecFuncBody.execBlockRet <|
    ((ABlock.start.requireStep (evalCallvalueEq_true hcv)).requireStep (by
      simp only [sender, owner, evalExpr?, envValue, EvalResult.bind, bind, pure]
      rw [evalAddrLit (config v) { contract := contract v, locals := locals } evm v.owner,
        hcaller]
      simp [evalBinaryOp?])).returns (by
        simp only [wrap256, scale, evalExpr?, EvalResult.bind, bind, pure]
        rw [hamount]
        simp only [EvalResult.ofOption, evalBinaryOp?]
        rw [if_neg]
        · norm_num [EVM.wordModulus, EVM.twoPow])

theorem tinyQuoteBodyRevertsUnauthorized (v : TinyImmutables) (evm : EVM.State) (locals : Store)
    (hcv : evm.executionEnv.weiValue = ⟨0⟩)
    (hcaller : evm.executionEnv.source ≠ v.owner) :
    ExecTransitionBody (config v) (contract v) evm locals (quoteTransition v).body .reverted := by
  exact ExecFuncBody.execBlockRevert <|
    (ABlock.start.requireStep (evalCallvalueEq_true hcv)).requireRevert (by
      simp only [sender, owner, evalExpr?, envValue, EvalResult.bind, bind, pure]
      rw [evalAddrLit (config v) { contract := contract v, locals := locals } evm v.owner]
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

theorem tinyQuoteX_toDecoder {cA gh bl σ σ₀ A I} {g : Sat256} (v : TinyImmutables)
    (hreach : ∃ k C, RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) ⟨148⟩ [solcSelectorWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) ⟨396⟩
      [⟨4⟩, UInt256.ofNat I.calldata.size, ⟨162⟩, ⟨167⟩, solcSelectorWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd148⟩ := hreach
  exact ⟨_, _, evm_run rd148 with [
    raw jumpdest (by tiny_decode_at v, ⟨148⟩, 0x5b, .JUMPDEST) (by evm_ov),
    raw push2 ⟨167⟩ (by tiny_decode_at v, ⟨149⟩, 0x61, (.Push .PUSH2)) (by evm_ov),
    raw push2 ⟨162⟩ (by tiny_decode_at v, ⟨152⟩, 0x61, (.Push .PUSH2)) (by evm_ov),
    raw calldatasize (by tiny_decode_at v, ⟨155⟩, 0x36, .CALLDATASIZE) (by evm_ov),
    raw push1 ⟨4⟩ (by tiny_decode_at v, ⟨156⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw push2 ⟨396⟩ (by tiny_decode_at v, ⟨158⟩, 0x61, (.Push .PUSH2)) (by evm_ov),
    raw jump (by tiny_decode_at v, ⟨161⟩, 0x56, .JUMP) (tinyContains396 v) (by evm_ov)]⟩

theorem tinyQuoteX_decoded {cA gh bl σ σ₀ A I} {g : Sat256} (v : TinyImmutables)
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hreach : ∃ k C, RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) ⟨148⟩ [solcSelectorWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) ⟨220⟩
      [calldataWord I.calldata 4, ⟨167⟩, solcSelectorWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ =
      ⟨0⟩ :=
    solcDecodeLenCheckOk_4_32 hsz36 hszhi hsize
  obtain ⟨_, _, rd396⟩ := tinyQuoteX_toDecoder (v := v) hreach
  have rd162 := evm_run rd396 with [
    raw jumpdest (by tiny_decode_at v, ⟨396⟩, 0x5b, .JUMPDEST) (by evm_ov),
    raw push0 (by tiny_decode_at v, ⟨397⟩, 0x5f, .PUSH0) (by evm_ov),
    raw push1 ⟨32⟩ (by tiny_decode_at v, ⟨398⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw dup3 (by tiny_decode_at v, ⟨400⟩, 0x82, .DUP3) (by evm_ov),
    raw dup5 (by tiny_decode_at v, ⟨401⟩, 0x84, .DUP5) (by evm_ov),
    raw sub (by tiny_decode_at v, ⟨402⟩, 0x03, .SUB) (by evm_ov),
    raw slt (by tiny_decode_at v, ⟨403⟩, 0x12, .SLT) (by evm_ov),
    raw iszero (by tiny_decode_at v, ⟨404⟩, 0x15, .ISZERO) (by evm_ov),
    raw push2 ⟨412⟩ (by tiny_decode_at v, ⟨405⟩, 0x61, (.Push .PUSH2)) (by evm_ov),
    raw jumpiT (by tiny_decode_at v, ⟨408⟩, 0x57, .JUMPI)
      (by rw [hslt]; decide) (tinyContains412 v) (by evm_ov),
    raw jumpdest (by tiny_decode_at v, ⟨412⟩, 0x5b, .JUMPDEST) (by evm_ov),
    raw pop (by tiny_decode_at v, ⟨413⟩, 0x50, .POP) (by evm_ov),
    raw calldataload (by tiny_decode_at v, ⟨414⟩, 0x35, .CALLDATALOAD) (by evm_ov),
    raw swap2 (by tiny_decode_at v, ⟨415⟩, 0x91, .SWAP2) (by evm_ov),
    raw swap1 (by tiny_decode_at v, ⟨416⟩, 0x90, .SWAP1) (by evm_ov),
    raw pop (by tiny_decode_at v, ⟨417⟩, 0x50, .POP) (by evm_ov),
    raw jump (by tiny_decode_at v, ⟨418⟩, 0x56, .JUMP) (tinyContains162 v) (by evm_ov)]
  have rd220 := evm_run rd162 with [
    raw jumpdest (by tiny_decode_at v, ⟨162⟩, 0x5b, .JUMPDEST) (by evm_ov),
    raw push2 ⟨220⟩ (by tiny_decode_at v, ⟨163⟩, 0x61, (.Push .PUSH2)) (by evm_ov),
    raw jump (by tiny_decode_at v, ⟨166⟩, 0x56, .JUMP) (tinyContains220 v) (by evm_ov)]
  exact ⟨_, _, by
    simpa [calldataWord, show (⟨4⟩ : UInt256).toNat = 4 from by decide] using rd220⟩

theorem tinyQuoteX_decodeRevert {cA gh bl σ σ₀ A I} {g : Sat256} (v : TinyImmutables)
    (hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ =
      ⟨1⟩)
    (hreach : ∃ k C, RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) ⟨148⟩ [solcSelectorWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev (patchedRuntime v) g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd396⟩ := tinyQuoteX_toDecoder (v := v) hreach
  exact evm_run rd396 with [
    raw jumpdest (by tiny_decode_at v, ⟨396⟩, 0x5b, .JUMPDEST) (by evm_ov),
    raw push0 (by tiny_decode_at v, ⟨397⟩, 0x5f, .PUSH0) (by evm_ov),
    raw push1 ⟨32⟩ (by tiny_decode_at v, ⟨398⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw dup3 (by tiny_decode_at v, ⟨400⟩, 0x82, .DUP3) (by evm_ov),
    raw dup5 (by tiny_decode_at v, ⟨401⟩, 0x84, .DUP5) (by evm_ov),
    raw sub (by tiny_decode_at v, ⟨402⟩, 0x03, .SUB) (by evm_ov),
    raw slt (by tiny_decode_at v, ⟨403⟩, 0x12, .SLT) (by evm_ov),
    raw iszero (by tiny_decode_at v, ⟨404⟩, 0x15, .ISZERO) (by evm_ov),
    raw push2 ⟨412⟩ (by tiny_decode_at v, ⟨405⟩, 0x61, (.Push .PUSH2)) (by evm_ov),
    raw jumpiNT (by tiny_decode_at v, ⟨408⟩, 0x57, .JUMPI)
      (by rw [hslt]; decide) (by evm_ov),
    raw revertStub (by tiny_decode_at v, ⟨409⟩, 0x5f, .PUSH0)
      (by tiny_decode_at v, ⟨410⟩, 0x5f, .PUSH0)
      (by tiny_decode_at v, ⟨411⟩, 0xfd, .REVERT) (by evm_ov)]

theorem tinyQuoteX_shortarg {cA gh bl σ σ₀ A I} {g : Sat256} (v : TinyImmutables)
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 36)
    (hreach : ∃ k C, RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) ⟨148⟩ [solcSelectorWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev (patchedRuntime v) g (initState cA gh bl σ σ₀ g A I) := by
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ =
      ⟨1⟩ :=
    solcDecodeLenCheckShort_4_32 hsz4 hshort hsize
  exact tinyQuoteX_decodeRevert (v := v) hslt hreach

theorem tinyQuoteX_hugearg {cA gh bl σ σ₀ A I} {g : Sat256} (v : TinyImmutables)
    (hsize : I.calldata.size < UInt256.size)
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size)
    (hreach : ∃ k C, RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) ⟨148⟩ [solcSelectorWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev (patchedRuntime v) g (initState cA gh bl σ σ₀ g A I) := by
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ =
      ⟨1⟩ :=
    solcDecodeLenCheckHuge_4_32 hbig hsize
  exact tinyQuoteX_decodeRevert (v := v) hslt hreach

set_option maxHeartbeats 1000000 in
theorem tinyQuoteX_success {cA gh bl σ σ₀ A I} {g : Sat256} (v : TinyImmutables)
    (hcaller : I.source = v.owner)
    (hreach : ∃ k C, RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) ⟨220⟩
      [calldataWord I.calldata 4, ⟨167⟩, solcSelectorWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret (patchedRuntime v) g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray (UInt256.mul (calldataWord I.calldata 4) v.scale)) := by
  obtain ⟨_, _, rd220⟩ := hreach
  have heq : UInt256.eq
      (UInt256.land (EVM.Word.ofNat (↑v.owner : Nat)) solcAddrMask)
      (solcSourceWord I) = ⟨1⟩ := by
    rw [tinyOwnerWord_eq_source_of_caller hcaller]
    exact u256_eq_refl (solcSourceWord I)
  have rd244 := evm_run rd220 with [
    raw jumpdest (by tiny_decode_at v, ⟨220⟩, 0x5b, .JUMPDEST) (by evm_ov),
    raw push0 (by tiny_decode_at v, ⟨221⟩, 0x5f, .PUSH0) (by evm_ov),
    raw caller (by tiny_decode_at v, ⟨222⟩, 0x33, .CALLER) (by evm_ov),
    raw push20 solcAddrMask (by tiny_decode_at v, ⟨223⟩, 0x73, (.Push .PUSH20))
      (by evm_ov)]
  have rd277 := rd244.pushConst (EVM.Word.ofNat (↑v.owner : Nat)) (width := 32)
    (op := .PUSH32) (by decide) (tinyDecodeOwnerWord2 v) (by evm_ov)
  have rd358 := evm_run rd277 with [
    raw and (by tiny_decode_at v, ⟨277⟩, 0x16, .AND) (by evm_ov),
    raw eq (by tiny_decode_at v, ⟨278⟩, 0x14, .EQ) (by evm_ov),
    raw push2 ⟨358⟩ (by tiny_decode_at v, ⟨279⟩, 0x61, (.Push .PUSH2)) (by evm_ov),
    raw jumpiT (by tiny_decode_at v, ⟨282⟩, 0x57, .JUMPI)
      (by rw [heq]; decide) (tinyContains358 v) (by evm_ov)]
  have rd360 := evm_run rd358 with [
    raw jumpdest (by tiny_decode_at v, ⟨358⟩, 0x5b, .JUMPDEST) (by evm_ov),
    raw pop (by tiny_decode_at v, ⟨359⟩, 0x50, .POP) (by evm_ov)]
  have rd393 := rd360.pushConst (EVM.wordOfInt (Int.ofNat v.scale.toNat)) (width := 32)
    (op := .PUSH32) (by decide) (tinyDecodeScaleWord2 v) (by evm_ov)
  have rd167 := evm_run rd393 with [
    raw mul (by tiny_decode_at v, ⟨393⟩, 0x02, .MUL) (by evm_ov),
    raw swap1 (by tiny_decode_at v, ⟨394⟩, 0x90, .SWAP1) (by evm_ov),
    raw jump (by tiny_decode_at v, ⟨395⟩, 0x56, .JUMP) (tinyContains167 v) (by evm_ov)]
  have hret := RD.tinyReturnWord167 (v := v) (R := [solcSelectorWord I]) rd167
    (by simp)
  rw [wordOfInt_ofNat_toNat, u256_mul_comm v.scale (calldataWord I.calldata 4)] at hret
  exact hret

def tinyQuoteErrorSelector : UInt256 :=
  UInt256.shiftLeft (⟨0x461bcd⟩ : UInt256) ⟨229⟩

def tinyQuoteOwnerErrorMem1 : ByteArray :=
  UInt256.toByteArray tinyQuoteErrorSelector |>.write 0 solcFreePtrMem 128 32

def tinyQuoteOwnerErrorMem2 : ByteArray :=
  UInt256.toByteArray (⟨32⟩ : UInt256) |>.write 0 tinyQuoteOwnerErrorMem1 132 32

def tinyQuoteOwnerErrorMem3 : ByteArray :=
  UInt256.toByteArray (⟨5⟩ : UInt256) |>.write 0 tinyQuoteOwnerErrorMem2 164 32

def tinyQuoteOwnerErrorMem : ByteArray :=
  UInt256.toByteArray
      (⟨50417742920509558439106150551775209266858149941038353264781520106005609840640⟩ :
        UInt256) |>.write 0 tinyQuoteOwnerErrorMem3 196 32

theorem tinyQuoteOwnerErrorMem_mload64 :
    (if (⟨64⟩ : UInt256).toNat ≥ tinyQuoteOwnerErrorMem.size then ⟨0⟩
      else uInt256OfByteArray (tinyQuoteOwnerErrorMem.readWithPadding (⟨64⟩ : UInt256).toNat 32)) =
      ⟨128⟩ := by
  native_decide

set_option maxHeartbeats 1000000 in
theorem tinyQuoteX_unauthorized {cA gh bl σ σ₀ A I} {g : Sat256} (v : TinyImmutables)
    (hcaller : I.source ≠ v.owner)
    (hreach : ∃ k C, RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) ⟨220⟩
      [calldataWord I.calldata 4, ⟨167⟩, solcSelectorWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev (patchedRuntime v) g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd220⟩ := hreach
  have heq : UInt256.eq
      (UInt256.land (EVM.Word.ofNat (↑v.owner : Nat)) solcAddrMask)
      (solcSourceWord I) = ⟨0⟩ := by
    exact u256_eq_of_ne (tinyOwnerWord_ne_source_of_caller_ne hcaller)
  have rd244 := evm_run rd220 with [
    raw jumpdest (by tiny_decode_at v, ⟨220⟩, 0x5b, .JUMPDEST) (by evm_ov),
    raw push0 (by tiny_decode_at v, ⟨221⟩, 0x5f, .PUSH0) (by evm_ov),
    raw caller (by tiny_decode_at v, ⟨222⟩, 0x33, .CALLER) (by evm_ov),
    raw push20 solcAddrMask (by tiny_decode_at v, ⟨223⟩, 0x73, (.Push .PUSH20))
      (by evm_ov)]
  have rd277 := rd244.pushConst (EVM.Word.ofNat (↑v.owner : Nat)) (width := 32)
    (op := .PUSH32) (by decide) (tinyDecodeOwnerWord2 v) (by evm_ov)
  have rd283 := evm_run rd277 with [
    raw and (by tiny_decode_at v, ⟨277⟩, 0x16, .AND) (by evm_ov),
    raw eq (by tiny_decode_at v, ⟨278⟩, 0x14, .EQ) (by evm_ov),
    raw push2 ⟨358⟩ (by tiny_decode_at v, ⟨279⟩, 0x61, (.Push .PUSH2)) (by evm_ov),
    raw jumpiNT (by tiny_decode_at v, ⟨282⟩, 0x57, .JUMPI)
      heq (by evm_ov)]
  have rd286 := evm_run rd283 with [
    raw push1 ⟨64⟩ (by tiny_decode_at v, ⟨283⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by tiny_decode_at v, ⟨285⟩, 0x51, .MLOAD)
      mem_cost solcFreePtrMem_mload64 (by decide) (by evm_ov)]
  have rd290 := rd286.pushConst (⟨0x461bcd⟩ : UInt256) (width := 3) (op := .PUSH3)
    (by decide) (by tiny_decode_at v, ⟨286⟩, 0x62, (.Push .PUSH3)) (by evm_ov)
  have rd309 := evm_run rd290 with [
    raw push1 ⟨229⟩ (by tiny_decode_at v, ⟨290⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw shl (by tiny_decode_at v, ⟨292⟩, 0x1b, .SHL) (by evm_ov),
    raw dup2 (by tiny_decode_at v, ⟨293⟩, 0x81, .DUP2) (by evm_ov),
    raw mstore 6 tinyQuoteOwnerErrorMem1 (UInt256.ofNat 5)
      (by tiny_decode_at v, ⟨294⟩, 0x52, .MSTORE)
      mem_cost (by native_decide) (by decide) (by evm_ov),
    raw push1 ⟨32⟩ (by tiny_decode_at v, ⟨295⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw push1 ⟨4⟩ (by tiny_decode_at v, ⟨297⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw dup3 (by tiny_decode_at v, ⟨299⟩, 0x82, .DUP3) (by evm_ov),
    raw add (by tiny_decode_at v, ⟨300⟩, 0x01, .ADD) (by evm_ov),
    raw mstore 3 tinyQuoteOwnerErrorMem2 (UInt256.ofNat 6)
      (by tiny_decode_at v, ⟨301⟩, 0x52, .MSTORE)
      mem_cost (by native_decide) (by decide) (by evm_ov),
    raw push1 ⟨5⟩ (by tiny_decode_at v, ⟨302⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw push1 ⟨36⟩ (by tiny_decode_at v, ⟨304⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw dup3 (by tiny_decode_at v, ⟨306⟩, 0x82, .DUP3) (by evm_ov),
    raw add (by tiny_decode_at v, ⟨307⟩, 0x01, .ADD) (by evm_ov),
    raw mstore 3 tinyQuoteOwnerErrorMem3 (UInt256.ofNat 7)
      (by tiny_decode_at v, ⟨308⟩, 0x52, .MSTORE)
      mem_cost (by native_decide) (by decide) (by evm_ov)]
  have rd342 := rd309.pushConst
    (⟨50417742920509558439106150551775209266858149941038353264781520106005609840640⟩ :
      UInt256) (width := 32) (op := .PUSH32) (by decide)
    (by tiny_decode_at v, ⟨309⟩, 0x7f, (.Push .PUSH32)) (by evm_ov)
  have rd350 := evm_run rd342 with [
    raw push1 ⟨68⟩ (by tiny_decode_at v, ⟨342⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw dup3 (by tiny_decode_at v, ⟨344⟩, 0x82, .DUP3) (by evm_ov),
    raw add (by tiny_decode_at v, ⟨345⟩, 0x01, .ADD) (by evm_ov),
    raw mstore 3 tinyQuoteOwnerErrorMem (UInt256.ofNat 8)
      (by tiny_decode_at v, ⟨346⟩, 0x52, .MSTORE)
      mem_cost (by native_decide) (by decide) (by evm_ov),
    raw push1 ⟨100⟩ (by tiny_decode_at v, ⟨347⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw add (by tiny_decode_at v, ⟨349⟩, 0x01, .ADD) (by evm_ov)]
  have rd357 := evm_run rd350 with [
    raw push1 ⟨64⟩ (by tiny_decode_at v, ⟨350⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 8) (by tiny_decode_at v, ⟨352⟩, 0x51, .MLOAD)
      mem_cost (by native_decide) (by decide) (by evm_ov),
    raw dup1 (by tiny_decode_at v, ⟨353⟩, 0x80, .DUP1) (by evm_ov),
    raw swap2 (by tiny_decode_at v, ⟨354⟩, 0x91, .SWAP2) (by evm_ov),
    raw sub (by tiny_decode_at v, ⟨355⟩, 0x03, .SUB) (by evm_ov),
    raw swap1 (by tiny_decode_at v, ⟨356⟩, 0x90, .SWAP1) (by evm_ov)]
  exact rd357.rev 0 (by tiny_decode_at v, ⟨357⟩, 0xfd, .REVERT)
    mem_cost (by evm_ov)

theorem tinyQuoteBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} (v : TinyImmutables)
    (hcode : I.code = patchedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (howner : (ownerSelBytes == I.calldata.extract 0 4) = false)
    (hsel : (quoteSelBytes == I.calldata.extract 0 4) = true)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor (config v) (contract v) cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz4 := tinyQuoteSelector_size hsel
  have hd := tinyDispatch_quote v howner hsel
  have hreach := tinyReachQuoteBody (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
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
            ExecTransitionBody (config v) (contract v)
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
              (quoteAmountStore I) (quoteTransition v).body
              (.returned { contract := contract v, locals := quoteAmountStore I }
                (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                (some [.int ((quoteAmountValue I * Int.ofNat v.scale.toNat) %
                  Int.ofNat EVM.wordModulus)])) := by
          exact tinyQuoteBodyReturns v
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) (quoteAmountStore I)
            (quoteAmountValue I)
            (by simp only [initState]; exact hwv)
            (by simp only [initState]; exact hcaller)
            (by simp [quoteAmountStore, quoteAmountValue])
        exact (tinyQuoteX_success (g := Sat256.ofUInt256 g) v hcaller ⟨_, _, rd220⟩)
          |>.reEquivExecution hcode hd hdec hbody hAccounts
            (returnEquiv_of_encode
              (by simpa [quoteAmountValue] using
                tinyQuoteReturnEncoding v (calldataWord I.calldata 4)))
      · have hbody :
            ExecTransitionBody (config v) (contract v)
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
              (quoteAmountStore I) (quoteTransition v).body .reverted := by
          exact tinyQuoteBodyRevertsUnauthorized v
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) (quoteAmountStore I)
            (by simp only [initState]; exact hwv)
            (by simp only [initState]; exact hcaller)
        exact (tinyQuoteX_unauthorized (g := Sat256.ofUInt256 g) v hcaller ⟨_, _, rd220⟩)
          |>.reEquivExecutionRevert hcode hd hdec hbody

end TinyImmutable
