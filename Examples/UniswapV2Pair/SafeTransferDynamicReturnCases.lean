import Examples.UniswapV2Pair.SafeTransferReturnCore
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace UniswapV2Pair
set_option maxRecDepth 2000000

set_option maxHeartbeats 1000000 in
theorem uniswapSafeTransferDynamicReturnCases
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
    (hin : 128 ≤ base.size) (hgap : ptr.toNat - base.size < USize.size) (hptrLo : 128 ≤ ptr.toNat)
    (haw : aw.toNat * 32 < UInt256.size) (hfit : ptr.toNat + out.size + 355 < UInt256.size)
    (hzero : base.readWithPadding 96 32 = (⟨0⟩ : UInt256).toByteArray) (hout : out.size < 2 ^ 255)
    (hret : (D_J uniswapV2PairBytecode 0).contains ret = true) (hov : R.length + 16 ≤ 1024) :
    (ExecStmt config caller evm (.internalCall "_safeTransfer" [tokenExpr, toExpr, valueExpr] retVar)
      .reverted ∧ RDrev uniswapV2PairBytecode g s0) ∨
    (ExecStmt config caller evm (.internalCall "_safeTransfer" [tokenExpr, toExpr, valueExpr] retVar)
      (.ok (resumeAfterInternalCall caller retVar none) evm') ∧ ∃ k' C', RD uniswapV2PairBytecode I g s0 ret R
        (safeTransferDynamicFinalMem base ptr toWord value out) (safeTransferDynamicFinalWords aw ptr out) out acc k' C') := by
  exact uniswapSafeTransferDynamicReturnCases_of_zeroSlot evm evm' token recipient rd6595
    hcaller hargs hdata hcall (by omega) hgap hptrLo haw hfit
    ((safeTransferDynamicCallMem2_read96 ptr toWord value hin hgap hptrLo (by omega)).trans hzero)
    hout hret hov

end UniswapV2Pair
