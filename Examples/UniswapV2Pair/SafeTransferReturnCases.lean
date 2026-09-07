import Examples.UniswapV2Pair.SafeTransferRuntime
import Examples.UniswapV2Pair.SafeTransfer
import Examples.UniswapV2Pair.RawCallSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace UniswapV2Pair
set_option maxRecDepth 2000000

noncomputable def safeTransferRuntimeFinalMem
    (base : ByteArray) (toWord value : UInt256) (out : ByteArray) : ByteArray :=
  if out.size = 0 then safeTransferRuntimeCallMem2 base toWord value
  else safeTransferRuntimeReturnDataMem base toWord value out

noncomputable def safeTransferRuntimeFinalActiveWords (out : ByteArray) : UInt256 :=
  if out.size = 0 then UInt256.ofNat 13 else safeTransferRuntimeReturnDataActiveWords out

set_option maxHeartbeats 1000000 in
theorem uniswapSafeTransferReturnCases
    {g : Sat256} {s0 : State} {I : ExecutionEnv}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {base out data : ByteArray} {value toWord tokenWord ret : UInt256} {R : List UInt256} {k C : ℕ}
    {caller : Frame} {tokenExpr toExpr valueExpr : Expr} {retVar : Ident} {z : Bool}
    (evm evm' : EVM.State) (token recipient : AccountAddress)
    (rd6595 : RD uniswapV2PairBytecode I g s0 ⟨6595⟩
      ((if z then ⟨1⟩ else ⟨0⟩) :: ⟨360⟩ :: UInt256.land tokenWord solcAddrMask :: ⟨96⟩ :: ⟨0⟩ ::
        value :: toWord :: tokenWord :: ret :: R)
      (safeTransferRuntimeCallMem2 base toWord value) (UInt256.ofNat 13) out acc k C)
    (hcaller : caller.contract = contract)
    (hargs : evalExprs? config caller evm [tokenExpr, toExpr, valueExpr] =
      .ok (safeTransferArgs token recipient value))
    (hdata : transferCalldata? recipient value = some data)
    (hcall : callViaEVM evm (EVM.address token) 0 data (z, evm', out))
    (hbase : base.size = 164)
    (hbase96 : base.readWithPadding 96 32 = UInt256.toByteArray ⟨0⟩)
    (houtSize : out.size < UInt256.size)
    (hret : (D_J uniswapV2PairBytecode 0).contains ret = true)
    (hov : R.length + 16 ≤ 1024) :
    (ExecStmt config caller evm (.internalCall "_safeTransfer" [tokenExpr, toExpr, valueExpr] retVar)
        .reverted ∧ RDrev uniswapV2PairBytecode g s0) ∨
    (ExecStmt config caller evm (.internalCall "_safeTransfer" [tokenExpr, toExpr, valueExpr] retVar)
        (.ok (resumeAfterInternalCall caller retVar none) evm') ∧
      out.size < 2 ^ 255 ∧ ∃ k' C', RD uniswapV2PairBytecode I g s0 ret R
        (safeTransferRuntimeFinalMem base toWord value out) (safeTransferRuntimeFinalActiveWords out)
        out acc k' C') := by
  cases z with
  | false =>
    refine Or.inl ⟨safeTransferInternalCallReverts_callFailure caller evm evm' token recipient value
      hcaller hargs hdata hcall, ?_⟩
    by_cases he : out.size = 0
    · exact RD.uniswapSafeTransferEmptyFailureReverts rd6595 he hov
    · by_cases hs : out.size < 2 ^ 255
      · exact RD.uniswapSafeTransferCallMem2NonemptyFailureReverts rd6595 he hs hbase hov
      · exact RD.uniswapSafeTransferCallMem2NonemptyHugeReverts rd6595 he (by omega) houtSize hbase hov
  | true =>
    by_cases he : out.size = 0
    · obtain ⟨k', C', rdRet⟩ := RD.uniswapSafeTransferEmptyReturnToRet rd6595 he
        (safeTransferRuntimeCallMem2_mload96_zero toWord value hbase hbase96)
        (by native_decide) hret hov
      refine Or.inr ⟨safeTransferInternalCallReturns_empty caller evm evm' token recipient value
        hcaller hargs hdata hcall he, by omega, k', C', ?_⟩
      simpa only [safeTransferRuntimeFinalMem, safeTransferRuntimeFinalActiveWords, he, ite_true] using rdRet
    · by_cases hs : out.size < 2 ^ 255
      · by_cases hshort : out.size < 32
        · exact Or.inl ⟨safeTransferInternalCallReverts_decode caller evm evm' token recipient value
            hcaller hargs hdata hcall he (decodeReturnValueWithMode_legacy_bool_none_short hshort),
            RD.uniswapSafeTransferCallMem2NonemptyShortReverts rd6595 he hshort hs hbase hov⟩
        · have hlo : 32 ≤ out.size := by omega
          by_cases hz : UInt256.ofNat (fromByteArrayBigEndian (out.extract 0 32)) = ⟨0⟩
          · exact Or.inl ⟨safeTransferInternalCallReverts_decodeFalse caller evm evm' token recipient value
              hcaller hargs hdata hcall he (decodeReturnValueWithMode_legacy_bool_false hlo hs hz),
              RD.uniswapSafeTransferCallMem2NonemptyFalseReverts rd6595 he hlo hs hz hbase hov⟩
          · obtain ⟨k', C', rdRet⟩ := RD.uniswapSafeTransferCallMem2NonemptyTrueToRet rd6595 he hlo hs hz
              hbase hov hret
            refine Or.inr ⟨safeTransferInternalCallReturns_decodeTrue caller evm evm' token recipient value
              hcaller hargs hdata hcall he (decodeReturnValueWithMode_legacy_bool_true hlo hs hz),
              hs, k', C', ?_⟩
            simpa only [safeTransferRuntimeFinalMem, safeTransferRuntimeFinalActiveWords, he, ite_false] using rdRet
      · exact Or.inl ⟨safeTransferInternalCallReverts_decode caller evm evm' token recipient value
          hcaller hargs hdata hcall he (decodeReturnValueWithMode_legacy_bool_none_huge (by omega)),
          RD.uniswapSafeTransferCallMem2NonemptyHugeReverts rd6595 he (by omega) houtSize hbase hov⟩

end UniswapV2Pair
