import Examples.UniswapV2Pair.SafeTransferReturnCore

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace UniswapV2Pair
set_option maxRecDepth 2000000

set_option maxHeartbeats 1000000 in
theorem uniswapSafeTransferDynamicCallRuntimeCases_of_zeroSlot
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
    (hin : 96 ≤ mem.size) (hgap : ptr.toNat - mem.size < USize.size) (hptrLo : 128 ≤ ptr.toNat)
    (hbase : mem.size ≤ ptr.toNat + 132) (hptrCap : ptr.toNat ≤ 2 ^ 255 + 1024)
    (haw : aw.toNat * 32 < UInt256.size) (hawLo : 96 ≤ aw.toNat * 32)
    (h64 : mem.readWithPadding 64 32 = ptr.toByteArray) (h96 : (safeTransferDynamicCallMem2 mem ptr toWord value).readWithPadding 96 32 = (⟨0⟩ : UInt256).toByteArray)
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
  have hnumeric : 2 ^ 255 + 1024 + 2 ^ 138 + 355 < UInt256.size := by native_decide
  have hc64 : (⟨64⟩ : UInt256).toNat + 32 ≤ aw.toNat * 32 := by change 64 + 32 ≤ _; omega
  have hmload : memoryWordLoad mem aw ⟨64⟩ = ptr := by
    exact mloadWordValue_of_readWithPadding (by change 64 < _; omega)
      (UInt256_mload_haw_of_cover _ _ haw hc64) h64
  have haw64 : memoryWordActiveWords aw ⟨64⟩ = aw := UInt256_M_same_of_cover _ _ haw hc64
  obtain ⟨cA', σ', z, out, A_in, callGas, _, _, hΘ, rd6595, hout⟩ :=
    RD.uniswapSafeTransferDynamicEntryToCallMadeBounded rd6370 hmload haw64 (by omega) hgap (by omega) hbase haw (by omega) hdepth hov
  obtain ⟨evm', hcallRaw, ha, hc, hs, hg, hb, he⟩ := rawZeroCall_source_of_theta
    (storage := config.storage) hAccounts henv hcreated hσ0 hgenesis hblocks hdepth hperm hΘ
  have hcall : callViaEVM evm (EVM.address token) 0
      ((transferCalldataMem (UInt256.land solcAddrMask toWord) value).readWithPadding 128 68) (z, evm', out) := by
    simpa only [htoken] using hcallRaw
  have hdata : transferCalldata? recipient value =
      some ((transferCalldataMem (UInt256.land solcAddrMask toWord) value).readWithPadding 128 68) := by
    rw [← hrecipient]
    exact transferCalldataMem_encode recipient value
  have hsign : out.size < 2 ^ 255 := by
    have hb : 2 ^ 138 < (2 : Nat) ^ 255 := by native_decide
    omega
  rcases uniswapSafeTransferDynamicReturnCases_of_zeroSlot evm evm' token recipient rd6595 hcaller hargs hdata hcall
    hin hgap hptrLo haw (by omega) h96 hsign hret (by omega) with hrev | ⟨hstmt, k', C', rdRet⟩
  · exact Or.inl hrev
  · exact Or.inr ⟨evm', σ', cA', out, k', C', hstmt, ha, hc, hs, hg, hb, he, hout, rdRet⟩

end UniswapV2Pair
