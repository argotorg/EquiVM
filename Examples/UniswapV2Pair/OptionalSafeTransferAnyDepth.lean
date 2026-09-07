import Examples.UniswapV2Pair.OptionalSafeTransferCases
import Examples.UniswapV2Pair.SafeTransferDepthLimit
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace UniswapV2Pair
set_option maxRecDepth 2000000

set_option maxHeartbeats 1000000 in
theorem uniswapOptionalSafeTransferAnyDepthCases
    {g : Sat256} {s0 : State} {I : ExecutionEnv}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {mem rdata : ByteArray} {ptr aw value toWord tokenWord ret : UInt256} {R : List UInt256}
    {caller : Frame} {condition tokenExpr toExpr valueExpr : Expr} {retVar : Ident}
    (evm : EVM.State) (token recipient : AccountAddress)
    (hentry : (value = ⟨0⟩ ∧ ∃ k C, RD uniswapV2PairBytecode I g s0 ret R mem aw rdata (cA, σ) k C) ∨
      (value ≠ ⟨0⟩ ∧ ∃ k C, RD uniswapV2PairBytecode I g s0 ⟨6370⟩
        (value :: toWord :: tokenWord :: ret :: R) mem aw rdata (cA, σ) k C))
    (hAccounts : accountMapEquiv σ evm.accountMap) (henv : evm.executionEnv = I)
    (hcreated : evm.createdAccounts = cA) (hσ0 : evm.σ₀ = s0.σ₀)
    (hgenesis : evm.genesisBlockHeader = s0.genesisBlockHeader) (hblocks : evm.blocks = s0.blocks)
    (hcaller : caller.contract = contract)
    (hcond : evalExpr? config caller evm condition = .ok (.bool (decide (0 < value.toNat))))
    (hargs : evalExprs? config caller evm [tokenExpr, toExpr, valueExpr] = .ok (safeTransferArgs token recipient value))
    (htoken : EVM.address token = AccountAddress.ofUInt256 (UInt256.land tokenWord solcAddrMask))
    (hrecipient : UInt256.ofNat recipient.val = UInt256.land solcAddrMask toWord)
    (hperm : I.perm = true)
    (hready : SafeTransferMemoryReady mem aw ptr) (hptrCap : ptr.toNat ≤ 2 ^ 255 + 1024)
    (hret : (D_J uniswapV2PairBytecode 0).contains ret = true) (hov : R.length + 20 ≤ 1024) :
    (ExecStmt config caller evm (.ite condition [.internalCall "_safeTransfer" [tokenExpr, toExpr, valueExpr] retVar] [])
      .reverted ∧ RDrev uniswapV2PairBytecode g s0) ∨
    (∃ evm' σ' cA' mem' aw' ptr' data' k' C',
      ExecStmt config caller evm (.ite condition [.internalCall "_safeTransfer" [tokenExpr, toExpr, valueExpr] retVar] [])
        (.ok (optionalSafeTransferFrame caller retVar value) evm') ∧
      accountMapEquiv σ' evm'.accountMap ∧ evm'.createdAccounts = cA' ∧ evm'.σ₀ = s0.σ₀ ∧
      evm'.genesisBlockHeader = s0.genesisBlockHeader ∧ evm'.blocks = s0.blocks ∧ evm'.executionEnv = I ∧
      SafeTransferMemoryReady mem' aw' ptr' ∧ ptr'.toNat ≤ ptr.toNat + 2 ^ 138 + 227 ∧
      RD uniswapV2PairBytecode I g s0 ret R mem' aw' data' (cA', σ') k' C') := by
  by_cases hdepth : I.depth.val < 1024
  · exact uniswapOptionalSafeTransferCases evm token recipient hentry hAccounts henv
      hcreated hσ0 hgenesis hblocks hcaller hcond hargs htoken hrecipient hdepth hperm hready hptrCap hret hov
  · have hd : I.depth = 1024 := Fin.ext (by have := I.depth.isLt; omega)
    rcases hentry with ⟨hz, k, C, rdRet⟩ | ⟨hnz, k, C, rd6370⟩
    · have hc : evalExpr? config caller evm condition = .ok (.bool false) := by simpa only [hz] using hcond
      exact Or.inr ⟨evm, σ, cA, mem, aw, ptr, rdata, k, C, optionalSafeTransferSkip hz hc,
        hAccounts, hcreated, hσ0, hgenesis, hblocks, henv, hready, by omega, rdRet⟩
    · have hpos : 0 < value.toNat := Nat.pos_of_ne_zero (fun h ↦ hnz (uint256_toNat_eq_zero h))
      have hc : evalExpr? config caller evm condition = .ok (.bool true) := by
        simpa only [decide_eq_true hpos] using hcond
      have hcallee := safeTransferInternalCallReverts_depthLimit (retVar := retVar) caller evm token recipient value
        hcaller hargs (by rw [henv]; exact hd)
      have hcover : (⟨64⟩ : UInt256).toNat + 32 ≤ aw.toNat * 32 := hready.wordsLo
      have hload : memoryWordLoad mem aw ⟨64⟩ = ptr :=
        mloadWordValue_of_readWithPadding (by change 64 < _; have := hready.sizeLo; omega)
          (UInt256_mload_haw_of_cover _ _ hready.wordsHi hcover) hready.read64
      have hw64 : memoryWordActiveWords aw ⟨64⟩ = aw := UInt256_M_same_of_cover _ _ hready.wordsHi hcover
      have hnum : 2 ^ 255 + 1024 + 291 < UInt256.size := by native_decide
      have rdRev := RD.uniswapSafeTransferDynamicDepthReverts rd6370 hload hw64
        hready.sizeLo hready.gap (by have := hready.ptrLo; omega) (by have := hready.sizeHi; omega)
        hready.wordsHi (by omega) hd hov
      exact Or.inl ⟨ExecStmt.iteTrue hc (ExecBlock.consRevert hcallee), rdRev⟩

end UniswapV2Pair
