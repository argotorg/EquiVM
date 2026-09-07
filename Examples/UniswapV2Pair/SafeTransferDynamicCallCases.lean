import Examples.UniswapV2Pair.SafeTransferCallCore
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace UniswapV2Pair
set_option maxRecDepth 2000000

set_option maxHeartbeats 1000000 in
theorem uniswapSafeTransferDynamicCallRuntimeCases
    {g : Sat256} {s0 : State} {I : ExecutionEnv}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {mem rdata : ByteArray} {ptr aw value toWord tokenWord ret : UInt256} {R : List UInt256} {k C : Nat}
    {caller : Frame} {tokenExpr toExpr valueExpr : Expr} {retVar : Ident}
    (evm : EVM.State) (token recipient : AccountAddress)
    (rd6370 : RD uniswapV2PairBytecode I g s0 ⟨6370⟩
      (value :: toWord :: tokenWord :: ret :: R) mem aw rdata (cA, σ) k C)
    (hAccounts : accountMapEquiv σ evm.accountMap) (henv : evm.executionEnv = I)
    (hcreated : evm.createdAccounts = cA) (hσ0 : evm.σ₀ = s0.σ₀)
    (hgenesis : evm.genesisBlockHeader = s0.genesisBlockHeader) (hblocks : evm.blocks = s0.blocks)
    (hcaller : caller.contract = contract)
    (hargs : evalExprs? config caller evm [tokenExpr, toExpr, valueExpr] = .ok (safeTransferArgs token recipient value))
    (htoken : EVM.address token = AccountAddress.ofUInt256 (UInt256.land tokenWord solcAddrMask))
    (hrecipient : UInt256.ofNat recipient.val = UInt256.land solcAddrMask toWord)
    (hdepth : I.depth.val < 1024) (hperm : I.perm = true)
    (hin : 128 ≤ mem.size) (hgap : ptr.toNat - mem.size < USize.size) (hptrLo : 128 ≤ ptr.toNat)
    (hbase : mem.size ≤ ptr.toNat + 132) (hptrCap : ptr.toNat ≤ 2 ^ 255 + 1024)
    (haw : aw.toNat * 32 < UInt256.size) (hawLo : 128 ≤ aw.toNat * 32)
    (h64 : mem.readWithPadding 64 32 = ptr.toByteArray) (h96 : mem.readWithPadding 96 32 = (⟨0⟩ : UInt256).toByteArray)
    (hret : (D_J uniswapV2PairBytecode 0).contains ret = true) (hov : R.length + 20 ≤ 1024) :
    (ExecStmt config caller evm (.internalCall "_safeTransfer" [tokenExpr, toExpr, valueExpr] retVar)
      .reverted ∧ RDrev uniswapV2PairBytecode g s0) ∨
    (∃ evm' σ' cA' out k' C',
      ExecStmt config caller evm (.internalCall "_safeTransfer" [tokenExpr, toExpr, valueExpr] retVar)
        (.ok (resumeAfterInternalCall caller retVar none) evm') ∧
      accountMapEquiv σ' evm'.accountMap ∧ evm'.createdAccounts = cA' ∧ evm'.σ₀ = s0.σ₀ ∧
      evm'.genesisBlockHeader = s0.genesisBlockHeader ∧ evm'.blocks = s0.blocks ∧ evm'.executionEnv = I ∧
      out.size < 2 ^ 138 ∧ RD uniswapV2PairBytecode I g s0 ret R
        (safeTransferDynamicFinalMem mem ptr toWord value out) (safeTransferDynamicFinalWords aw ptr out) out (cA', σ') k' C') := by
  have hnum : 2 ^ 255 + 1024 + 228 < UInt256.size := by native_decide
  exact uniswapSafeTransferDynamicCallRuntimeCases_of_zeroSlot evm token recipient rd6370
    hAccounts henv hcreated hσ0 hgenesis hblocks hcaller hargs htoken hrecipient hdepth hperm
    (by omega) hgap hptrLo hbase hptrCap haw (by omega) h64
    ((safeTransferDynamicCallMem2_read96 ptr toWord value hin hgap hptrLo (by omega)).trans h96)
    hret hov

end UniswapV2Pair
