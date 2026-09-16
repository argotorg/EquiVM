import Examples.UniswapV2Pair.SafeTransferDynamicReturnRuntime
import Examples.UniswapV2Pair.SafeTransfer
import Examples.UniswapV2Pair.RawCallSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace UniswapV2Pair
set_option maxRecDepth 2000000

noncomputable def safeTransferDynamicFinalMem (base : ByteArray) (ptr toWord value : UInt256) (out : ByteArray) : ByteArray :=
  if out.size = 0 then safeTransferDynamicCallMem2 base ptr toWord value
  else solcReturnDataMem (safeTransferDynamicCallMem2 base ptr toWord value) (ptr + ⟨164⟩) out

noncomputable def safeTransferDynamicFinalWords (aw ptr : UInt256) (out : ByteArray) : UInt256 :=
  if out.size = 0 then safeTransferDynamicCallWords2 aw ptr
  else solcReturnDataActiveWords (safeTransferDynamicCallWords2 aw ptr) (ptr + ⟨164⟩) out

set_option maxHeartbeats 1000000 in
theorem uniswapSafeTransferDynamicReturnCases_of_zeroSlot
    {g : Sat256} {s0 : State} {I : ExecutionEnv}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {base out data : ByteArray} {ptr aw value toWord tokenWord ret : UInt256} {R : List UInt256} {k C : Nat}
    {caller : Frame} {tokenExpr toExpr valueExpr : Expr} {retVar : Ident} {z : Bool}
    (evm evm' : EVM.State) (token recipient : AccountAddress)
    (rd6595 : RD uniswapV2PairBytecode I g s0 ⟨6595⟩
      ((if z then ⟨1⟩ else ⟨0⟩) :: (ptr + ⟨232⟩) :: UInt256.land tokenWord solcAddrMask :: ⟨96⟩ :: ⟨0⟩ ::
        value :: toWord :: tokenWord :: ret :: R)
      (safeTransferDynamicCallMem2 base ptr toWord value) (safeTransferDynamicCallWords2 aw ptr) out acc k C)
    (hcaller : caller.contract = contract)
    (hargs : evalExprs? config caller evm [tokenExpr, toExpr, valueExpr] = .ok (safeTransferArgs token recipient value))
    (hdata : transferCalldata? recipient value = some data)
    (hcall : callViaEVM evm (EVM.address token) 0 data (z, evm', out))
    (hin : 96 ≤ base.size) (hgap : ptr.toNat - base.size < USize.size) (hptrLo : 128 ≤ ptr.toNat)
    (haw : aw.toNat * 32 < UInt256.size) (hfit : ptr.toNat + out.size + 355 < UInt256.size)
    (hzero : (safeTransferDynamicCallMem2 base ptr toWord value).readWithPadding 96 32 = (⟨0⟩ : UInt256).toByteArray) (hout : out.size < 2 ^ 255)
    (hret : (D_J uniswapV2PairBytecode 0).contains ret = true) (hov : R.length + 16 ≤ 1024) :
    (ExecStmt config caller evm (.internalCall "_safeTransfer" [tokenExpr, toExpr, valueExpr] retVar)
      .reverted ∧ RDrev uniswapV2PairBytecode g s0) ∨
    (ExecStmt config caller evm (.internalCall "_safeTransfer" [tokenExpr, toExpr, valueExpr] retVar)
      (.ok (resumeAfterInternalCall caller retVar none) evm') ∧ ∃ k' C', RD uniswapV2PairBytecode I g s0 ret R
        (safeTransferDynamicFinalMem base ptr toWord value out) (safeTransferDynamicFinalWords aw ptr out) out acc k' C') := by
  by_cases he : out.size = 0
  · cases z with
    | false => exact Or.inl ⟨safeTransferInternalCallReverts_callFailure caller evm evm' token recipient value
        hcaller hargs hdata hcall, RD.uniswapSafeTransferEmptyFailureReverts rd6595 he hov⟩
    | true =>
      obtain ⟨k', C', rdRet⟩ := RD.uniswapSafeTransferDynamicEmptyReturnToRet_of_zeroSlot rd6595 he hin hgap hptrLo haw (by omega) hzero hret hov
      refine Or.inr ⟨safeTransferInternalCallReturns_empty caller evm evm' token recipient value
        hcaller hargs hdata hcall he, k', C', ?_⟩
      simpa only [safeTransferDynamicFinalMem, safeTransferDynamicFinalWords, he, ite_true] using rdRet
  · have hp164 : (ptr + ⟨164⟩).toNat = ptr.toNat + 164 := uadd_word_ofNat_toNat ptr 164 (by omega)
    obtain ⟨_, _, ⟨hb2, hc2⟩⟩ := safeTransferDynamicCallWords_bounds aw ptr haw (by omega)
    have h96 : (⟨64⟩ : UInt256).toNat + 32 ≤ (safeTransferDynamicCallWords2 aw ptr).toNat * 32 := by change 64 + 32 ≤ _; omega
    have hload : memoryWordLoad (safeTransferDynamicCallMem2 base ptr toWord value)
        (safeTransferDynamicCallWords2 aw ptr) ⟨64⟩ = ptr + ⟨164⟩ := by
      apply mloadWordValue_of_readWithPadding
      · change 64 < _
        rw [safeTransferDynamicCallMem2_size ptr toWord value (by omega) hgap (by omega)]
        omega
      · exact UInt256_mload_haw_of_cover _ _ hb2 h96
      · exact safeTransferDynamicCallMem2_read64 ptr toWord value (by omega) hgap (by omega) (by omega)
    have hsize := safeTransferDynamicCallMem2_size ptr toWord value (by omega) hgap (by omega)
    rcases uniswapSafeTransferNonemptyReturnRuntimeCases rd6595 he hout hload
      (by rw [hsize]; omega) (by rw [hsize, hp164]; omega) (by rw [hp164]; omega) hb2
      (by rw [hp164]; omega) (by rw [hp164]; omega) hret hov with
      ⟨hbad, hrev⟩ | ⟨hz, hlo, hword, k', C', rdRet⟩
    · refine Or.inl ⟨?_, hrev⟩
      cases z with
      | false => exact safeTransferInternalCallReverts_callFailure caller evm evm' token recipient value hcaller hargs hdata hcall
      | true =>
        by_cases hs : out.size < 32
        · exact safeTransferInternalCallReverts_decode caller evm evm' token recipient value hcaller hargs hdata hcall he
            (decodeReturnValueWithMode_legacy_bool_none_short hs)
        · have hw : UInt256.ofNat (fromByteArrayBigEndian (out.extract 0 32)) = ⟨0⟩ := by
            rcases hbad with hfalse | hshort | hword
            · cases hfalse
            · exact (hs hshort).elim
            · exact hword
          exact safeTransferInternalCallReverts_decodeFalse caller evm evm' token recipient value hcaller hargs hdata hcall he
            (decodeReturnValueWithMode_legacy_bool_false (by omega) hout hw)
    · rw [hz] at hcall
      refine Or.inr ⟨safeTransferInternalCallReturns_decodeTrue caller evm evm' token recipient value hcaller hargs hdata hcall he
        (decodeReturnValueWithMode_legacy_bool_true hlo hout hword), k', C', ?_⟩
      simpa only [safeTransferDynamicFinalMem, safeTransferDynamicFinalWords, he, ite_false] using rdRet

end UniswapV2Pair
