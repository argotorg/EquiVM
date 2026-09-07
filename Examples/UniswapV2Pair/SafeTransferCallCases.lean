import Examples.UniswapV2Pair.SafeTransferReturnCases

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace UniswapV2Pair
set_option maxRecDepth 2000000

set_option maxHeartbeats 1000000 in
theorem uniswapSafeTransferCallRuntimeCases
    {g : Sat256} {s0 : State} {I : ExecutionEnv}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {mem rdata : ByteArray} {value toWord tokenWord ret : UInt256} {R : List UInt256} {k C : ℕ}
    {caller : Frame} {tokenExpr toExpr valueExpr : Expr} {retVar : Ident}
    (evm : EVM.State) (token recipient : AccountAddress)
    (rd6370 : RD uniswapV2PairBytecode I g s0 ⟨6370⟩
      (value :: toWord :: tokenWord :: ret :: R) mem balanceOfThisStaticcallActiveWords rdata (cA, σ) k C)
    (hAccounts : accountMapEquiv σ evm.accountMap) (henv : evm.executionEnv = I)
    (hcreated : evm.createdAccounts = cA) (hσ0 : evm.σ₀ = s0.σ₀)
    (hgenesis : evm.genesisBlockHeader = s0.genesisBlockHeader) (hblocks : evm.blocks = s0.blocks)
    (hcaller : caller.contract = contract)
    (hargs : evalExprs? config caller evm [tokenExpr, toExpr, valueExpr] =
      .ok (safeTransferArgs token recipient value))
    (htoken : EVM.address token = AccountAddress.ofUInt256 (UInt256.land tokenWord solcAddrMask))
    (hrecipient : UInt256.ofNat recipient.val = UInt256.land solcAddrMask toWord)
    (hdepth : I.depth.val < 1024) (hperm : I.perm = true)
    (hmem : mem.size = 164)
    (h64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (h96 : mem.readWithPadding 96 32 = UInt256.toByteArray ⟨0⟩)
    (hret : (D_J uniswapV2PairBytecode 0).contains ret = true)
    (hov : R.length + 20 ≤ 1024) :
    (ExecStmt config caller evm (.internalCall "_safeTransfer" [tokenExpr, toExpr, valueExpr] retVar)
        .reverted ∧ RDrev uniswapV2PairBytecode g s0) ∨
    (∃ evm' σ' cA' out k' C',
      ExecStmt config caller evm (.internalCall "_safeTransfer" [tokenExpr, toExpr, valueExpr] retVar)
        (.ok (resumeAfterInternalCall caller retVar none) evm') ∧
      accountMapEquiv σ' evm'.accountMap ∧ evm'.createdAccounts = cA' ∧
      evm'.σ₀ = s0.σ₀ ∧ evm'.genesisBlockHeader = s0.genesisBlockHeader ∧
      evm'.blocks = s0.blocks ∧ evm'.executionEnv = I ∧ out.size < 2 ^ 255 ∧
      RD uniswapV2PairBytecode I g s0 ret R
        (safeTransferRuntimeFinalMem mem toWord value out) (safeTransferRuntimeFinalActiveWords out)
        out (cA', σ') k' C') := by
  have hmload := mloadFreePtrValue (aw := balanceOfThisStaticcallActiveWords)
    (by rw [hmem]; decide) (by native_decide) h64
  obtain ⟨cA', σ', z, out, A_in, callGas, _, _, _, hΘ, rd6595, houtSize⟩ :=
    RD.uniswapSafeTransferEntryToCallMade rd6370 hmem hmload hdepth hov
  obtain ⟨evm', hcallRaw, ha, hc, hs, hg, hb, he⟩ := rawZeroCall_source_of_theta
    (storage := config.storage) hAccounts henv hcreated hσ0 hgenesis hblocks hdepth hperm hΘ
  have hcall : callViaEVM evm (EVM.address token) 0
      ((safeTransferRuntimeCallMem2 mem toWord value).readWithPadding 292 68) (z, evm', out) := by
    simpa only [htoken] using hcallRaw
  have hdata : transferCalldata? recipient value =
      some ((safeTransferRuntimeCallMem2 mem toWord value).readWithPadding 292 68) := by
    rw [safeTransferRuntimeCallMem2_read292_68 toWord value hmem, ← hrecipient]
    exact transferCalldataMem_encode recipient value
  rcases uniswapSafeTransferReturnCases evm evm' token recipient rd6595
      hcaller hargs hdata hcall hmem h96 houtSize hret (by omega) with
    hrev | ⟨hstmt, houtSmall, k', C', rdRet⟩
  · exact Or.inl hrev
  · exact Or.inr ⟨evm', σ', cA', out, k', C', hstmt, ha, hc, hs, hg, hb, he, houtSmall, rdRet⟩

end UniswapV2Pair
