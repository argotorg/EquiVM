import Examples.UniswapV2Pair.SwapCallbackPrepare
import Examples.UniswapV2Pair.SwapCallbackSource
import Examples.UniswapV2Pair.SwapCallbackBranchRuntime
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace UniswapV2Pair
set_option maxRecDepth 2000000

abbrev swapAfterCallbackFrame (caller : Frame) (dataLen : UInt256) : Frame :=
  if dataLen = ⟨0⟩ then caller else { caller with locals := caller.locals.insert "_callback" (collapseReturns []) }

set_option maxHeartbeats 1000000 in
theorem uniswapSwapCallbackCases
    {g : Sat256} {s0 : State} {I : ExecutionEnv}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {mem rdata : ByteArray} {ptr aw token1 token0 scratch1 scratch0 reserve1 reserve0
      dataLen dataPtr toWord amount1Out amount0Out : UInt256} {R : List UInt256} {k C : Nat}
    {caller : Frame} (evm : EVM.State) (recipient : AccountAddress)
    (rd1904 : RD uniswapV2PairBytecode I g s0 ⟨1904⟩
      (token1 :: token0 :: scratch1 :: scratch0 :: reserve1 :: reserve0 :: dataLen :: dataPtr ::
        toWord :: amount1Out :: amount0Out :: R) mem aw rdata (cA, σ) k C)
    (hAccounts : accountMapEquiv σ evm.accountMap) (henv : evm.executionEnv = I)
    (hcreated : evm.createdAccounts = cA) (hσ0 : evm.σ₀ = s0.σ₀)
    (hgenesis : evm.genesisBlockHeader = s0.genesisBlockHeader) (hblocks : evm.blocks = s0.blocks)
    (hto : caller.locals.get? "to" = some (.address recipient))
    (ha0 : caller.locals.get? "amount0Out" = some (uniswapUint256Value amount0Out))
    (ha1 : caller.locals.get? "amount1Out" = some (uniswapUint256Value amount1Out))
    (hbytes : caller.locals.get? "data" = some (.bytes (I.calldata.extract dataPtr.toNat (dataPtr.toNat + dataLen.toNat))))
    (htarget : EVM.address recipient = AccountAddress.ofUInt256 (UInt256.land solcAddrMask toWord))
    (hready : SafeTransferMemoryReady mem aw ptr)
    (hdata : dataPtr.toNat + dataLen.toNat ≤ I.calldata.size)
    (hfit : ptr.toNat + dataLen.toNat + 227 < UInt256.size) (hsmall : dataLen.toNat + 196 < 2 ^ 64)
    (hperm : I.perm = true) (hov : R.length + 29 ≤ 1024) :
    (ExecStmt config caller evm swapCallbackStmt .reverted ∧ RDrev uniswapV2PairBytecode g s0) ∨
    (∃ evm' σ' cA' mem' aw' out k' C',
      ExecStmt config caller evm swapCallbackStmt (.ok (swapAfterCallbackFrame caller dataLen) evm') ∧
      accountMapEquiv σ' evm'.accountMap ∧ evm'.createdAccounts = cA' ∧ evm'.σ₀ = s0.σ₀ ∧
      evm'.genesisBlockHeader = s0.genesisBlockHeader ∧ evm'.blocks = s0.blocks ∧ evm'.executionEnv = I ∧
      96 ≤ mem'.size ∧ ptr.toNat - mem'.size < USize.size ∧
      aw'.toNat * 32 < UInt256.size ∧ 96 ≤ aw'.toNat * 32 ∧ mem'.readWithPadding 64 32 = ptr.toByteArray ∧
      RD uniswapV2PairBytecode I g s0 ⟨2091⟩
        (token1 :: token0 :: scratch1 :: scratch0 :: reserve1 :: reserve0 :: dataLen :: dataPtr ::
          toWord :: amount1Out :: amount0Out :: R) mem' aw' out (cA', σ') k' C') := by
  have hsize : (I.calldata.extract dataPtr.toNat (dataPtr.toNat + dataLen.toNat)).size = dataLen.toNat := by
    rw [ByteArray.size_extract]; omega
  have hcond := evalExpr_swap_callbackCondition evm _ hbytes
  rw [hsize] at hcond
  rcases uniswapSwapRuntimeCallbackBranchCases rd1904 (by omega) with ⟨hz, k', C', rd2091⟩ | ⟨hnz, _, _, rd1911⟩
  · have hc : evalExpr? config caller evm swapCallbackCondition = .ok (.bool false) := by simpa only [hz] using hcond
    exact Or.inr ⟨evm, σ, cA, mem, aw, rdata, k', C', by
      simpa only [swapAfterCallbackFrame, if_pos hz] using uniswapSwapCallbackSkip hc,
      hAccounts, hcreated, hσ0, hgenesis, hblocks, henv, hready.sizeLo, hready.gap,
      hready.wordsHi, hready.wordsLo, hready.read64, rd2091⟩
  · have hlen : dataLen.toNat ≠ 0 := fun h ↦ hnz (uint256_toNat_eq_zero h)
    have hpos := Nat.pos_of_ne_zero hlen
    have hc : evalExpr? config caller evm swapCallbackCondition = .ok (.bool true) := by
      simpa only [decide_eq_true hpos] using hcond
    have hargs := evalExprs_swap_callbackArgs evm amount0Out amount1Out _ ha0 ha1 hbytes
    rw [henv] at hargs
    have hguard := evalExpr_uniswap_codeGuard hAccounts (by simpa only [uniswapAddress_self] using htarget)
      (show evalExpr? config caller evm (.var "to") = .ok (.address recipient) from by
        simp only [evalExpr?, EvalResult.ofOption, hto])
    obtain ⟨_, _, rd2054⟩ := uniswapSwapCallbackPrepared rd1911 hready hdata hlen hfit hov
    by_cases hcode : extCodeSizeWord σ (UInt256.land solcAddrMask toWord) = ⟨0⟩
    · have hg : evalExpr? config caller evm (.binary .gt (.extCodeSize (.var "to")) (.intLit 0)) = .ok (.bool false) := by
        simpa only [hcode] using hguard
      exact Or.inl ⟨uniswapSwapCallbackNoCode hc hg,
        uniswapSwapCallbackCannotCallReverts rd2054 (Or.inl hcode) (by simp only [List.length_cons]; omega)⟩
    · have hcodePos : 0 < (extCodeSizeWord σ (UInt256.land solcAddrMask toWord)).toNat :=
        Nat.pos_of_ne_zero (fun h ↦ hcode (uint256_toNat_eq_zero h))
      have hg : evalExpr? config caller evm (.binary .gt (.extCodeSize (.var "to")) (.intLit 0)) = .ok (.bool true) := by
        simpa only [decide_eq_true hcodePos] using hguard
      by_cases hdepth : I.depth.val < 1024
      · obtain ⟨hbMem, hcMem⟩ := swapCallbackWords_bounds aw ptr dataLen hready.wordsHi hfit
        have hround := swapCallbackPaddedLen_bounds dataLen (by omega)
        have hcover : ptr.toNat + (swapCallbackCallLen ptr dataLen).toNat ≤
            (swapCallbackWords aw ptr dataLen).toNat * 32 := by
          rw [swapCallbackCallLen_toNat ptr dataLen (by omega)]; omega
        obtain ⟨cA', σ', z, out, A_in, callGas, _, _, hΘ, rd2070, hout⟩ :=
          uniswapSwapCallbackCallMade rd2054 hcode hdepth hcover (by simp only [List.length_cons]; omega)
        obtain ⟨evm', hraw, ha, hcr, hs, hge, hbl, he⟩ := rawZeroCall_source_of_theta
          (storage := config.storage) hAccounts henv hcreated hσ0 hgenesis hblocks hdepth hperm hΘ
        have hcall : typedCallViaEVM config evm (EVM.address recipient) "uniswapV2Call" 0
            (swapCallbackArgs I.source amount0Out amount1Out (I.calldata.extract dataPtr.toNat (dataPtr.toNat + dataLen.toNat)))
            (z, evm', out) true := by
          refine ⟨_, swapCallbackCalldata_encode _ _ _ _, ?_⟩
          rw [htarget]
          rw [swapCallbackMem_calldata _ _ _ _ _ hready hdata hlen hfit hsmall] at hraw
          exact hraw
        rcases uniswapSwapCallbackCallResultCases rd2070 hout (by simp only [List.length_cons]; omega) with
          ⟨hz, rdRev⟩ | ⟨hz, k', C', rd2091⟩
        · rw [hz] at hcall
          exact Or.inl ⟨uniswapSwapCallbackFailure hc hg hto hargs hcall, rdRev⟩
        · rw [hz] at hcall
          have hstmt := uniswapSwapCallbackSuccess hc hg hto hargs hcall
          have hmemSize := swapCallbackMem_size ptr amount0Out amount1Out dataPtr dataLen hready hdata hlen hfit
          have hread := swapCallbackMem_read64 ptr amount0Out amount1Out dataPtr dataLen hready hdata hlen hfit
          have hu : 0 < USize.size := lt_usize 0 (by omega)
          exact Or.inr ⟨evm', σ', cA', _, _, out, k', C', by
            simpa only [swapAfterCallbackFrame, if_neg hnz] using hstmt,
            ha, hcr, hs, hge, hbl, he, by rw [hmemSize]; omega, by rw [hmemSize]; omega,
            hbMem, by omega, hread, rd2091⟩
      · have hd : I.depth = 1024 := Fin.ext (by have := I.depth.isLt; omega)
        have hcall : typedCallViaEVM config evm (EVM.address recipient) "uniswapV2Call" 0
            (swapCallbackArgs I.source amount0Out amount1Out (I.calldata.extract dataPtr.toNat (dataPtr.toNat + dataLen.toNat)))
            (false, { evm with substate := (evm.addAccessedAccount (EVM.address recipient)).substate }, ByteArray.empty) true := by
          refine ⟨_, swapCallbackCalldata_encode _ _ _ _, ?_⟩
          apply callViaEVM.callNotMade rfl rfl
          rintro ⟨_, hne⟩
          exact hne (by rw [henv]; exact hd)
        exact Or.inl ⟨uniswapSwapCallbackFailure hc hg hto hargs hcall,
          uniswapSwapCallbackCannotCallReverts rd2054 (Or.inr hd) (by simp only [List.length_cons]; omega)⟩

end UniswapV2Pair
