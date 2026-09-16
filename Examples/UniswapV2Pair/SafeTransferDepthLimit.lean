import Examples.UniswapV2Pair.CallDepthLimit
import Examples.UniswapV2Pair.SafeTransferCallPrepare
import Examples.UniswapV2Pair.SafeTransfer
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace UniswapV2Pair
set_option maxRecDepth 2000000

theorem RD.uniswapSafeTransferDynamicDepthReverts
    {g : Sat256} {s0 : State} {I : ExecutionEnv}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {base rdata : ByteArray} {ptr aw value toWord token ret : UInt256} {R : List UInt256} {k C : Nat}
    (rd6370 : RD uniswapV2PairBytecode I g s0 ⟨6370⟩ (value :: toWord :: token :: ret :: R)
      base aw rdata (cA, σ) k C)
    (hload : memoryWordLoad base aw ⟨64⟩ = ptr) (haw64 : memoryWordActiveWords aw ⟨64⟩ = aw)
    (hin : 96 ≤ base.size) (hgap : ptr.toNat - base.size < USize.size) (hptrLo : 96 ≤ ptr.toNat)
    (hbase : base.size ≤ ptr.toNat + 228)
    (haw : aw.toNat * 32 < UInt256.size) (hptr : ptr.toNat + 291 < UInt256.size)
    (hdepth : I.depth = 1024) (hov : R.length + 20 ≤ 1024) :
    RDrev uniswapV2PairBytecode g s0 := by
  obtain ⟨_, _, _, rd6594⟩ := RD.uniswapSafeTransferDynamicEntryToCallPrepared rd6370
    hload haw64 hin hgap hptrLo hbase haw hptr hov
  obtain ⟨_, _, rd6595⟩ := RD.solcCallDepthLimit rd6594 (by native_decide) hdepth
    (by simp only [List.length_cons]; omega)
  exact RD.uniswapSafeTransferEmptyFailureReverts rd6595 rfl (by omega)

theorem safeTransferInternalCallReverts_depthLimit (caller : Frame) (evm : EVM.State)
    {tokenExpr toExpr valueExpr : Expr} {retVar : Ident}
    (token recipient : AccountAddress) (value : UInt256)
    (hcaller : caller.contract = contract)
    (hargs : evalExprs? config caller evm [tokenExpr, toExpr, valueExpr] = .ok (safeTransferArgs token recipient value))
    (hdepth : evm.executionEnv.depth = 1024) :
    ExecStmt config caller evm (.internalCall "_safeTransfer" [tokenExpr, toExpr, valueExpr] retVar) .reverted := by
  have hcall : callViaEVM evm (EVM.address token) 0
      ((transferCalldataMem (UInt256.ofNat recipient.val) value).readWithPadding 128 68)
      (false, { evm with substate := (evm.addAccessedAccount (EVM.address token)).substate }, ByteArray.empty) := by
    apply callViaEVM.callNotMade rfl rfl
    rintro ⟨_, hne⟩
    exact hne hdepth
  exact safeTransferInternalCallReverts_callFailure caller evm _ token recipient value hcaller hargs
    (transferCalldataMem_encode recipient value) hcall

end UniswapV2Pair
