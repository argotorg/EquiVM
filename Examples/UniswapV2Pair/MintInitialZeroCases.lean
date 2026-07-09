import Examples.UniswapV2Pair.MintInitialCases
import Examples.UniswapV2Pair.MintLiquidityZeroRuntime

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000

namespace UniswapV2Pair

set_option maxHeartbeats 1000000 in
theorem uniswapMintInitialAfterMintFeeLiquidityZeroRevertCase
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {cAFee : Batteries.RBSet AccountAddress compare} {σFee : AccountMap}
    {evm0S evm1S evmAfter : EVM.State}
    {out0 out1 mem rdata : ByteArray} {k C : ℕ}
    {feeOn amount0 amount1 balance0 balance1 reserve0 reserve1 liquidity toWord sel : UInt256}
    (nextLocals : Store) (rootLiquidity : Int)
    (hcode : I.code = uniswapV2PairBytecode)
    (hdispatch : dispatchMsg contract I.calldata = some mintTransition)
    (hsz36 : 36 ≤ I.calldata.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hunlockedSolm :
      Solm.EVM.storageLoad
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
          ⟨12⟩ =
        ⟨1⟩)
    (hguard0 :
      evalExpr? config
        { contract := contract,
          locals :=
            mintReserveStore
              (uniswapLockEnteredState
                (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)) I }
        (uniswapLockEnteredState
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I))
        (.binary .gt (.extCodeSize (.storage token0Ref)) (.intLit 0)) = .ok (.bool true))
    (hguard1 :
      evalExpr? config
        { contract := contract,
          locals :=
            (mintReserveStore
                (uniswapLockEnteredState
                  (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)) I).insert
              "balance0" (uniswapUint256Value balance0) }
        evm0S (.binary .gt (.extCodeSize (.storage token1Ref)) (.intLit 0)) =
          .ok (.bool true))
    (hcall0 : typedCallViaEVM config
      (uniswapLockEnteredState
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I))
      (EVM.address
        (uniswapAddressAtSlot
          (uniswapLockEnteredState
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)) ⟨6⟩))
      "balanceOf" 0
      [.address
        (uniswapLockEnteredState
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)).executionEnv.codeOwner]
      (true, evm0S, out0) false)
    (hdec0 :
      config.externalABI.decode? "balanceOf" out0 = some [uniswapUint256Value balance0])
    (hcall1 : typedCallViaEVM config evm0S
      (EVM.address (uniswapAddressAtSlot evm0S ⟨7⟩)) "balanceOf" 0
      [.address evm0S.executionEnv.codeOwner] (true, evm1S, out1) false)
    (hdec1 :
      config.externalABI.decode? "balanceOf" out1 = some [uniswapUint256Value balance1])
    (henough0 :
      (uniswapReserve0Word
        (uniswapLockEnteredState
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I))).toNat ≤
          balance0.toNat)
    (henough1 :
      (uniswapReserve1Word
        (uniswapLockEnteredState
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I))).toNat ≤
          balance1.toNat)
    (hfee :
      ExecStmt config
        { contract := contract,
          locals :=
            mintAmountStore
              (uniswapLockEnteredState
                (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)) I balance0
              balance1 }
        evm1S (.internalCall "_mintFee" [.var "_reserve0", .var "_reserve1"] "feeOn")
        (.ok { contract := contract, locals := nextLocals } evmAfter))
    (hbase : nextLocals.get? "totalSupply" = none)
    (htotalZero : mintFunctionTotalSupplyWord evmAfter = ⟨0⟩)
    (hsqrt :
      ExecStmt config
        { contract := contract,
          locals :=
            nextLocals.insert "_totalSupply"
              (uniswapUint256Value (mintFunctionTotalSupplyWord evmAfter)) }
        evmAfter
        (.internalCall "sqrt" [u256 (.binary .mul (.var "amount0") (.var "amount1"))]
          "rootLiquidity")
        (.ok
          (resumeAfterInternalCall
            { contract := contract,
              locals :=
                nextLocals.insert "_totalSupply"
                  (uniswapUint256Value (mintFunctionTotalSupplyWord evmAfter)) }
            "rootLiquidity" (some [.int rootLiquidity]))
          evmAfter))
    (rd2531 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨2531⟩
      [UInt256.ofNat rootLiquidity.toNat, ⟨1000⟩, ⟨3742⟩, ⟨0⟩, feeOn, amount1,
        amount0, balance1, balance0, reserve1, reserve0, ⟨0⟩, toWord, ⟨861⟩, sel]
      mem feeToStaticcallActiveWords rdata (cAFee, σFee) k C)
    (hrootSize : rootLiquidity.toNat < UInt256.size)
    (hrootGeMin : minimumLiquidity ≤ rootLiquidity)
    (hliquiditySource : liquidity = UInt256.ofNat (rootLiquidity - minimumLiquidity).toNat)
    (hliquidityZero : liquidity = ⟨0⟩)
    (hfitSupplyMinSource :
      mintFunctionTotalSupplyNewNat evmAfter (⟨1000⟩ : UInt256) < UInt256.size)
    (hfitBalanceMinSource :
      mintFunctionToBalanceNewNat evmAfter (AccountAddress.ofNat 0)
          (⟨1000⟩ : UInt256) <
        UInt256.size)
    (htotalFitMin :
      (uniswapSlotWord ⟨0⟩ σFee I).toNat + (⟨1000⟩ : UInt256).toNat < UInt256.size)
    (hbalanceFitMin :
      (uniswapCodeOwnerStorageWord I
        (sstoreAccountMap I.codeOwner σFee ⟨0⟩
          (uniswapSlotWord ⟨0⟩ σFee I + (⟨1000⟩ : UInt256)))
        (uniswapInternalMintBalanceHashSlot ⟨0⟩ mem)).toNat +
          (⟨1000⟩ : UInt256).toNat < UInt256.size)
    (hperm : I.perm = true)
    (hmem : mem.size = 164)
    (hmem64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let evmS := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let afterTotalSupplyLocals :=
    nextLocals.insert "_totalSupply"
      (uniswapUint256Value (mintFunctionTotalSupplyWord evmAfter))
  let caller : Frame := { contract := contract, locals := afterTotalSupplyLocals }
  let afterRoot := resumeAfterInternalCall caller "rootLiquidity" (some [.int rootLiquidity])
  let afterLiquidity : Frame :=
    { contract := contract,
      locals := afterRoot.locals.insert "liquidity" (uniswapUint256Value liquidity) }
  let afterMinimum := resumeAfterInternalCall afterLiquidity "_minimumMint" none
  let evmMinimum := mintFunctionPostState evmAfter (AccountAddress.ofNat 0)
    (⟨1000⟩ : UInt256)
  have hprefix :=
    uniswapMintAfterMintFeeTotalSupplyPrefix_of_call evmS evm0S evm1S evmAfter I
      nextLocals (by simp only [evmS, initState]; exact hwv) hunlockedSolm hguard0
      hguard1 hcall0 hdec0 hcall1 hdec1 henough0 henough1 hfee hbase
  have htotal :
      afterTotalSupplyLocals.get? "_totalSupply" =
        some (uniswapUint256Value (⟨0⟩ : UInt256)) := by
    simp [afterTotalSupplyLocals, htotalZero]
  have hfitSub : rootLiquidity - minimumLiquidity < (2 : Int) ^ 256 := by
    have hrootNonneg : 0 ≤ rootLiquidity := by
      have hge : (1000 : Int) ≤ rootLiquidity := by
        simpa [minimumLiquidity] using hrootGeMin
      omega
    have hrootLt : rootLiquidity < (UInt256.size : Int) := by
      have h : (rootLiquidity.toNat : Int) < (UInt256.size : Int) := by
        exact_mod_cast hrootSize
      simpa [Int.toNat_of_nonneg hrootNonneg] using h
    norm_num [minimumLiquidity, UInt256.size] at hrootLt ⊢
    omega
  have hbranchStmt :
      ExecStmt config caller evmAfter mintLiquidityBranchStmt
        (.ok afterMinimum evmMinimum) := by
    simpa [caller, afterRoot, afterLiquidity, afterMinimum, evmMinimum,
      afterTotalSupplyLocals] using
      uniswapMintInitialLiquidityBranchStmtPrefix evmAfter rootLiquidity liquidity htotal
        (by simpa [afterTotalSupplyLocals] using hsqrt) hrootGeMin hfitSub
        hliquiditySource hfitSupplyMinSource hfitBalanceMinSource
  have hbranch :
      ExecBlock config caller evmAfter [mintLiquidityBranchStmt]
        (.ok afterMinimum evmMinimum) :=
    ExecBlock.consNormal hbranchStmt ExecBlock.nil
  have hliqAfter :
      afterMinimum.locals.get? "liquidity" =
        some (uniswapUint256Value (⟨0⟩ : UInt256)) := by
    change (((afterTotalSupplyLocals.insert "rootLiquidity" (.int rootLiquidity)).insert
      "liquidity" (uniswapUint256Value liquidity)).insert "_minimumMint" Value.unit).get?
        "liquidity" = some (uniswapUint256Value (⟨0⟩ : UInt256))
    rw [store_get_ne _ _ (by decide), store_get_self]
    simp [hliquidityZero]
  have htail :
      ExecBlock config afterMinimum evmMinimum mintAfterLiquidityTailStmts .reverted := by
    simpa [afterMinimum] using
      uniswapMintAfterLiquidityZeroReverts (locals := afterMinimum.locals) evmMinimum
        hliqAfter
  have hthrough := execBlock_append hprefix (execBlock_append hbranch htail)
  have hbody :
      ExecTransitionBody config contract evmS (mintStore I) mintTransition.body .reverted := by
    exact ExecFuncBody.execBlockRevert (by
      simpa [mintTransition, mintLiquidityBranchStmt, mintInitialLiquidityBranchStmts,
        mintProportionalLiquidityBranchStmts, mintAfterLiquidityTailStmts,
        List.append_assoc, caller, afterTotalSupplyLocals] using hthrough)
  have hrootGeWord :
      (⟨1000⟩ : UInt256).toNat ≤ (UInt256.ofNat rootLiquidity.toNat).toNat := by
    rw [ulit_toNat' _ hrootSize]
    have hge : (1000 : Int) ≤ rootLiquidity := by
      simpa [minimumLiquidity] using hrootGeMin
    have hrootNatGe : 1000 ≤ rootLiquidity.toNat := by
      have hrootNonneg : 0 ≤ rootLiquidity := by omega
      have h : (1000 : Int) ≤ (rootLiquidity.toNat : Int) := by
        simpa [Int.toNat_of_nonneg hrootNonneg] using hge
      exact_mod_cast h
    simpa using hrootNatGe
  have hliquidityRuntime :
      liquidity = UInt256.sub (UInt256.ofNat rootLiquidity.toNat) (⟨1000⟩ : UInt256) := by
    apply u256_inj
    have hrootWordToNat :
        (UInt256.ofNat rootLiquidity.toNat).toNat = rootLiquidity.toNat :=
      ulit_toNat' _ hrootSize
    have hsubToNat :
        (UInt256.sub (UInt256.ofNat rootLiquidity.toNat) (⟨1000⟩ : UInt256)).toNat =
          rootLiquidity.toNat - 1000 := by
      rw [usub_toNat hrootGeWord, hrootWordToNat]
      change rootLiquidity.toNat - 1000 = rootLiquidity.toNat - 1000
      rfl
    rw [hliquiditySource, hsubToNat]
    have hnonneg : 0 ≤ rootLiquidity - minimumLiquidity := by
      have hge : (1000 : Int) ≤ rootLiquidity := by
        simpa [minimumLiquidity] using hrootGeMin
      simp [minimumLiquidity]
      omega
    have htoNatEq : (rootLiquidity - minimumLiquidity).toNat = rootLiquidity.toNat - 1000 := by
      have hrootNonneg : 0 ≤ rootLiquidity := by
        have hge : (1000 : Int) ≤ rootLiquidity := by
          simpa [minimumLiquidity] using hrootGeMin
        omega
      have hrootCast : (rootLiquidity.toNat : Int) = rootLiquidity :=
        Int.toNat_of_nonneg hrootNonneg
      calc
        (rootLiquidity - minimumLiquidity).toNat =
            (rootLiquidity - (1000 : Int)).toNat := by simp [minimumLiquidity]
        _ = (((rootLiquidity.toNat : Nat) : Int) - (1000 : Int)).toNat := by
          rw [hrootCast]
        _ = rootLiquidity.toNat - 1000 := by
          exact Int.toNat_sub rootLiquidity.toNat 1000
    rw [UInt256.toNat_ofNat_of_lt]
    · exact htoNatEq
    · simpa [htoNatEq, UInt256.size] using
        lt_of_le_of_lt (Nat.sub_le rootLiquidity.toNat 1000) hrootSize
  obtain ⟨_, _, rd3841⟩ :=
    uniswapMintRuntimeInitialLiquidityAfterRootEntry rd2531 hliquidityRuntime hrootGeWord
      hperm htotalFitMin hbalanceFitMin hmem hmem64
  let minimumMem :=
    uniswapInternalMintLogMem (⟨1000⟩ : UInt256)
      (uniswapInternalMintBalanceHashMem ⟨0⟩
        (uniswapInternalMintBalanceHashMem ⟨0⟩ mem))
  have hminimumMemSize : minimumMem.size = 164 := by
    simpa [minimumMem, hmem] using
      uniswapInternalMintSuccessMem_size_of_ge160 ⟨0⟩ (⟨1000⟩ : UInt256)
        (mem := mem) (by rw [hmem]; omega)
  have hminimumMem64 : minimumMem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
    simpa [minimumMem] using
      uniswapInternalMintSuccessMem_read64_of_ge160 ⟨0⟩ (⟨1000⟩ : UInt256)
        (mem := mem) (by rw [hmem]; omega) hmem64
  exact (uniswapMintRuntimeLiquidityZeroReverts rd3841 hliquidityZero
      (by simpa [minimumMem] using hminimumMemSize)
      (by simpa [minimumMem] using hminimumMem64))
    |>.reEquivExecutionRevert hcode hdispatch (uniswapDecode_mint_ok hsz36) hbody

end UniswapV2Pair
