import Examples.UniswapV2Pair.SafeTransferMemoryReady
import Examples.UniswapV2Pair.OptionalSafeTransferFrame
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace UniswapV2Pair
set_option maxRecDepth 2000000

set_option maxHeartbeats 1000000 in
theorem uniswapOptionalSafeTransferCases
    {g : Sat256} {s0 : State} {I : ExecutionEnv}
    {σ : AccountMap}
    {mem rdata : ByteArray} {ptr aw value toWord tokenWord ret : UInt256} {R : List UInt256}
    {caller : Frame} {condition tokenExpr toExpr valueExpr : Expr} {retVar : Ident}
    (evm : EVM.State) (token recipient : AccountAddress)
    (hentry : (value = ⟨0⟩ ∧ ∃ k C, RD uniswapV2PairBytecode I g s0 ret R mem aw rdata σ k C) ∨
      (value ≠ ⟨0⟩ ∧ ∃ k C, RD uniswapV2PairBytecode I g s0 ⟨6370⟩
        (value :: toWord :: tokenWord :: ret :: R) mem aw rdata σ k C))
    (hAccounts : σ = evm.accountMap) (henv : evm.executionEnv = I)
    (hσ0 : evm.σ₀ = s0.σ₀)
    (hcaller : caller.contract = contract)
    (hcond : evalExpr? config caller evm condition = .ok (.bool (decide (0 < value.toNat))))
    (hargs : evalExprs? config caller evm [tokenExpr, toExpr, valueExpr] = .ok (safeTransferArgs token recipient value))
    (htoken : EVM.address token = AccountAddress.ofUInt256 (UInt256.land tokenWord solcAddrMask))
    (hrecipient : UInt256.ofNat recipient.val = UInt256.land solcAddrMask toWord)
    (hdepth : I.depth.val < 1024) (hperm : I.perm = true)
    (hready : SafeTransferMemoryReady mem aw ptr) (hptrCap : ptr.toNat ≤ 2 ^ 255 + 1024)
    (hret : (D_J uniswapV2PairBytecode 0).contains ret = true) (hov : R.length + 20 ≤ 1024)
    (himm : caller.immutables = ∅ := by first | rfl | assumption) :
    (ExecStmt config caller evm (.ite condition [.internalCall "_safeTransfer" [tokenExpr, toExpr, valueExpr] retVar] [])
      .reverted ∧ RDrev uniswapV2PairBytecode g s0) ∨
    (∃ evm' σ' mem' aw' ptr' data' k' C',
      ExecStmt config caller evm (.ite condition [.internalCall "_safeTransfer" [tokenExpr, toExpr, valueExpr] retVar] [])
        (.ok (optionalSafeTransferFrame caller retVar value) evm') ∧
      σ' = evm'.accountMap ∧ evm'.σ₀ = s0.σ₀ ∧ evm'.executionEnv = I ∧
      SafeTransferMemoryReady mem' aw' ptr' ∧ ptr'.toNat ≤ ptr.toNat + 2 ^ 138 + 227 ∧
      RD uniswapV2PairBytecode I g s0 ret R mem' aw' data' σ' k' C') := by
  rcases hentry with ⟨hz, k, C, rdRet⟩ | ⟨hnz, k, C, rd6370⟩
  · have hc : evalExpr? config caller evm condition = .ok (.bool false) := by
      simpa only [hz] using hcond
    have hstmt : ExecStmt config caller evm
        (.ite condition [.internalCall "_safeTransfer" [tokenExpr, toExpr, valueExpr] retVar] [])
        (.ok (optionalSafeTransferFrame caller retVar value) evm) := optionalSafeTransferSkip hz hc
    exact Or.inr ⟨evm, σ, mem, aw, ptr, rdata, k, C, hstmt,
      hAccounts, hσ0, henv, hready, by omega, rdRet⟩
  · have hpos : 0 < value.toNat := Nat.pos_of_ne_zero (fun h ↦ hnz (uint256_toNat_eq_zero h))
    have hc : evalExpr? config caller evm condition = .ok (.bool true) := by
      simpa only [decide_eq_true hpos] using hcond
    rcases uniswapSafeTransferDynamicCallRuntimeCases_of_zeroSlot evm token recipient rd6370
        hAccounts henv hσ0 hcaller hargs htoken hrecipient hdepth hperm
        hready.sizeLo hready.gap hready.ptrLo hready.sizeHi hptrCap hready.wordsHi hready.wordsLo
        hready.read64 (hready.zeroSlot toWord value) hret hov with
      ⟨hcall, rdRev⟩ | ⟨evm', σ', out, k', C', hcall, hpost, hs, he, hout, rdRet⟩
    · exact Or.inl ⟨ExecStmt.iteTrue hc (ExecBlock.consRevert hcall), rdRev⟩
    · have hnum : 2 ^ 255 + 1024 + 2 ^ 138 + 455 < UInt256.size := by native_decide
      obtain ⟨next, hnext, hcap⟩ := safeTransferMemoryReady_after_call hready toWord value out (by omega)
      have hstmt : ExecStmt config caller evm
          (.ite condition [.internalCall "_safeTransfer" [tokenExpr, toExpr, valueExpr] retVar] [])
          (.ok (optionalSafeTransferFrame caller retVar value) evm') := by
        rw [optionalSafeTransferFrame, if_neg hnz]
        exact ExecStmt.iteTrue hc (ExecBlock.consNormal hcall ExecBlock.nil)
      exact Or.inr ⟨evm', σ', _, _, next, out, k', C', hstmt, hpost, hs, he,
        hnext, by omega, rdRet⟩

end UniswapV2Pair
