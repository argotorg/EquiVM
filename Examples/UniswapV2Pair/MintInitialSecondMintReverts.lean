import Examples.UniswapV2Pair.MintInitialMinimumMintReverts

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000

namespace UniswapV2Pair

theorem uniswapMintAfterLiquidityMintTotalSupplyOverflowReverts
    {locals : Store} (evm : EVM.State) (recipient : AccountAddress)
    (liquidity : UInt256)
    (hto : locals.get? "to" = some (.address recipient))
    (hliq : locals.get? "liquidity" = some (uniswapUint256Value liquidity))
    (hliqNonzero : liquidity ≠ ⟨0⟩)
    (hover : UInt256.size ≤ mintFunctionTotalSupplyNewNat evm liquidity) :
    ExecBlock config { contract := contract, locals := locals } evm
      mintAfterLiquidityTailStmts .reverted := by
  have hreq :=
    evalExpr_mint_liquidity_gt_zero_true
      (solm := { contract := contract, locals := locals }) evm liquidity
      (by simpa using hliq) hliqNonzero
  have hargs :
      evalExprs? config { contract := contract, locals := locals } evm
        [.var "to", .var "liquidity"] =
          .ok [mintFunctionToValue recipient, mintFunctionValueValue liquidity] := by
    exact evalExprs_mint_finalMintArgs_of_get evm recipient liquidity hto
      (by simpa [mintFunctionValueValue] using hliq)
  change ExecBlock config { contract := contract, locals := locals } evm
    (.require (.binary .gt (.var "liquidity") (.intLit 0)) ::
      ([ .internalCall "_mint" [.var "to", .var "liquidity"] "_mintResult" ] ++
        updateReservesStmtsWith (.var "balance0") (.var "balance1")
          (.var "_reserve0") (.var "_reserve1") ++
        [ .ite (.var "feeOn")
            [ .assign .storage kLastRef
                (u256 (.binary .mul (.storage reserve0Ref) (.storage reserve1Ref))) ]
            [] ] ++
        lockExit ++
        [ .return [(.var "liquidity")] ]))
    .reverted
  refine ExecBlock.consNormal (ExecStmt.requireTrue hreq) ?_
  exact ExecBlock.consRevert
    (uniswapMintFunctionCallRevert_totalSupplyOverflow
      (caller := { contract := contract, locals := locals }) (evm := evm)
      (recipient := recipient) (value := liquidity)
      (args := [.var "to", .var "liquidity"]) (retVar := "_mintResult")
      rfl hargs hover)

theorem uniswapMintAfterLiquidityMintBalanceOverflowReverts
    {locals : Store} (evm : EVM.State) (recipient : AccountAddress)
    (liquidity : UInt256)
    (hto : locals.get? "to" = some (.address recipient))
    (hliq : locals.get? "liquidity" = some (uniswapUint256Value liquidity))
    (hliqNonzero : liquidity ≠ ⟨0⟩)
    (hfitSupply : mintFunctionTotalSupplyNewNat evm liquidity < UInt256.size)
    (hover : UInt256.size ≤ mintFunctionToBalanceNewNat evm recipient liquidity) :
    ExecBlock config { contract := contract, locals := locals } evm
      mintAfterLiquidityTailStmts .reverted := by
  have hreq :=
    evalExpr_mint_liquidity_gt_zero_true
      (solm := { contract := contract, locals := locals }) evm liquidity
      (by simpa using hliq) hliqNonzero
  have hargs :
      evalExprs? config { contract := contract, locals := locals } evm
        [.var "to", .var "liquidity"] =
          .ok [mintFunctionToValue recipient, mintFunctionValueValue liquidity] := by
    exact evalExprs_mint_finalMintArgs_of_get evm recipient liquidity hto
      (by simpa [mintFunctionValueValue] using hliq)
  change ExecBlock config { contract := contract, locals := locals } evm
    (.require (.binary .gt (.var "liquidity") (.intLit 0)) ::
      ([ .internalCall "_mint" [.var "to", .var "liquidity"] "_mintResult" ] ++
        updateReservesStmtsWith (.var "balance0") (.var "balance1")
          (.var "_reserve0") (.var "_reserve1") ++
        [ .ite (.var "feeOn")
            [ .assign .storage kLastRef
                (u256 (.binary .mul (.storage reserve0Ref) (.storage reserve1Ref))) ]
            [] ] ++
        lockExit ++
        [ .return [(.var "liquidity")] ]))
    .reverted
  refine ExecBlock.consNormal (ExecStmt.requireTrue hreq) ?_
  exact ExecBlock.consRevert
    (uniswapMintFunctionCallRevert_balanceOverflow
      (caller := { contract := contract, locals := locals }) (evm := evm)
      (recipient := recipient) (value := liquidity)
      (args := [.var "to", .var "liquidity"]) (retVar := "_mintResult")
      rfl hargs hfitSupply hover)

set_option maxHeartbeats 1000000 in
theorem uniswapMintInitialAfterMintFeeSecondMintTotalSupplyOverflowRevertCase
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {cAFee : Batteries.RBSet AccountAddress compare} {σFee : AccountMap}
    {evm0S evm1S evmAfter : EVM.State}
    {out0 out1 mem rdata : ByteArray} {k C : ℕ}
    {feeOn amount0 amount1 balance0 balance1 reserve0 reserve1 liquidity toWord sel :
      UInt256}
    (nextLocals : Store) (rootLiquidity : Int) (recipient : AccountAddress)
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
    (hto : nextLocals.get? "to" = some (.address recipient))
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
      [UInt256.ofNat rootLiquidity.toNat, ⟨1000⟩, ⟨3742⟩, ⟨0⟩, feeOn,
        amount1, amount0, balance1, balance0, reserve1, reserve0, ⟨0⟩, toWord,
        ⟨861⟩, sel]
      mem feeToStaticcallActiveWords rdata (cAFee, σFee) k C)
    (hrootSize : rootLiquidity.toNat < UInt256.size)
    (hrootGeMin : minimumLiquidity ≤ rootLiquidity)
    (hliquiditySource : liquidity = UInt256.ofNat (rootLiquidity - minimumLiquidity).toNat)
    (hliqNonzero : liquidity ≠ ⟨0⟩)
    (hfitSupplyMinSource :
      mintFunctionTotalSupplyNewNat evmAfter (⟨1000⟩ : UInt256) < UInt256.size)
    (hfitBalanceMinSource :
      mintFunctionToBalanceNewNat evmAfter (AccountAddress.ofNat 0)
          (⟨1000⟩ : UInt256) <
        UInt256.size)
    (htotalFitMin :
      (uniswapSlotWord ⟨0⟩ σFee I).toNat + (⟨1000⟩ : UInt256).toNat <
        UInt256.size)
    (hbalanceFitMin :
      (uniswapCodeOwnerStorageWord I
        (sstoreAccountMap I.codeOwner σFee ⟨0⟩
          (uniswapSlotWord ⟨0⟩ σFee I + (⟨1000⟩ : UInt256)))
        (uniswapInternalMintBalanceHashSlot ⟨0⟩ mem)).toNat +
          (⟨1000⟩ : UInt256).toNat <
        UInt256.size)
    (hsourceOverflow :
      UInt256.size ≤
        mintFunctionTotalSupplyNewNat
          (mintFunctionPostState evmAfter (AccountAddress.ofNat 0) (⟨1000⟩ : UInt256))
          liquidity)
    (hruntimeOverflow :
      let σAfterMinimum :=
        sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner σFee ⟨0⟩
            (uniswapSlotWord ⟨0⟩ σFee I + (⟨1000⟩ : UInt256)))
          (uniswapInternalMintBalanceHashSlot ⟨0⟩
            (uniswapInternalMintBalanceHashMem ⟨0⟩ mem))
          (uniswapCodeOwnerStorageWord I
            (sstoreAccountMap I.codeOwner σFee ⟨0⟩
              (uniswapSlotWord ⟨0⟩ σFee I + (⟨1000⟩ : UInt256)))
            (uniswapInternalMintBalanceHashSlot ⟨0⟩ mem) + (⟨1000⟩ : UInt256))
      UInt256.size ≤ (uniswapSlotWord ⟨0⟩ σAfterMinimum I).toNat + liquidity.toNat)
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
  have htoAfter :
      afterMinimum.locals.get? "to" = some (.address recipient) := by
    change (((afterTotalSupplyLocals.insert "rootLiquidity" (.int rootLiquidity)).insert
      "liquidity" (uniswapUint256Value liquidity)).insert "_minimumMint" Value.unit).get?
        "to" = some (.address recipient)
    rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
      store_get_ne _ _ (by decide)]
    dsimp [afterTotalSupplyLocals]
    change (Std.HashMap.insert nextLocals "_totalSupply"
        (uniswapUint256Value (mintFunctionTotalSupplyWord evmAfter))).get? "to" =
      some (.address recipient)
    rw [store_get_ne nextLocals (k := "_totalSupply") (a := "to")
      (uniswapUint256Value (mintFunctionTotalSupplyWord evmAfter)) (by decide)]
    exact hto
  have hliqAfter :
      afterMinimum.locals.get? "liquidity" = some (uniswapUint256Value liquidity) := by
    change (((afterTotalSupplyLocals.insert "rootLiquidity" (.int rootLiquidity)).insert
      "liquidity" (uniswapUint256Value liquidity)).insert "_minimumMint" Value.unit).get?
        "liquidity" = some (uniswapUint256Value liquidity)
    rw [store_get_ne _ _ (by decide), store_get_self]
  have htail :
      ExecBlock config afterMinimum evmMinimum mintAfterLiquidityTailStmts .reverted := by
    exact uniswapMintAfterLiquidityMintTotalSupplyOverflowReverts evmMinimum recipient
      liquidity htoAfter hliqAfter hliqNonzero hsourceOverflow
  have hthrough := execBlock_append hprefix (execBlock_append hbranch htail)
  have hbody :
      ExecTransitionBody config contract evmS (mintStore I) mintTransition.body .reverted := by
    exact ExecFuncBody.execBlockRevert (by
      simpa [mintTransition, mintLiquidityBranchStmt, mintInitialLiquidityBranchStmts,
        mintProportionalLiquidityBranchStmts, mintAfterLiquidityTailStmts,
        List.append_assoc, caller, afterTotalSupplyLocals] using hthrough)
  let minimumMem :=
    uniswapInternalMintLogMem (⟨1000⟩ : UInt256)
      (uniswapInternalMintBalanceHashMem ⟨0⟩
        (uniswapInternalMintBalanceHashMem ⟨0⟩ mem))
  let σAfterMinimum :=
    sstoreAccountMap I.codeOwner
      (sstoreAccountMap I.codeOwner σFee ⟨0⟩
        (uniswapSlotWord ⟨0⟩ σFee I + (⟨1000⟩ : UInt256)))
      (uniswapInternalMintBalanceHashSlot ⟨0⟩
        (uniswapInternalMintBalanceHashMem ⟨0⟩ mem))
      (uniswapCodeOwnerStorageWord I
        (sstoreAccountMap I.codeOwner σFee ⟨0⟩
          (uniswapSlotWord ⟨0⟩ σFee I + (⟨1000⟩ : UInt256)))
        (uniswapInternalMintBalanceHashSlot ⟨0⟩ mem) + (⟨1000⟩ : UInt256))
  rcases mintInitialRootLiquidityRuntimeFacts hrootSize hrootGeMin hliquiditySource with
    ⟨hrootGeWord, hliquidityRuntime⟩
  obtain ⟨_, _, rd3841⟩ :=
    uniswapMintRuntimeInitialLiquidityAfterRootEntry rd2531 hliquidityRuntime
      hrootGeWord hperm htotalFitMin hbalanceFitMin hmem hmem64
  obtain ⟨_, _, rd8128⟩ :=
    uniswapMintRuntimeLiquidityMintEntry rd3841 hliqNonzero
  have hminimumMemSize : minimumMem.size = 164 := by
    simpa [minimumMem, hmem] using
      uniswapInternalMintSuccessMem_size_of_ge160 ⟨0⟩ (⟨1000⟩ : UInt256)
        (mem := mem) (by rw [hmem]; omega)
  have hminimumMem64 : minimumMem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
    simpa [minimumMem] using
      uniswapInternalMintSuccessMem_read64_of_ge160 ⟨0⟩ (⟨1000⟩ : UInt256)
        (by rw [hmem]; omega) hmem64
  have rdRev :
      RDrev uniswapV2PairBytecode (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) :=
    uniswapInternalMintRuntimeTotalSupplyOverflowReverts
      (value := liquidity) (recipient := toWord) (ret := ⟨3914⟩)
      (R := [⟨0⟩, feeOn, amount1, amount0, balance1, balance0, reserve1, reserve0,
        liquidity, toWord, ⟨861⟩, sel])
      (σ := σAfterMinimum) rd8128 (by simpa [minimumMem, σAfterMinimum] using
        hruntimeOverflow)
      hminimumMemSize hminimumMem64
      (by simp only [List.length_cons, List.length_nil]; omega)
  exact rdRev.reEquivExecutionRevert hcode hdispatch (uniswapDecode_mint_ok hsz36) hbody

set_option maxHeartbeats 1000000 in
theorem uniswapMintInitialAfterMintFeeSecondMintBalanceOverflowRevertCase
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {cAFee : Batteries.RBSet AccountAddress compare} {σFee : AccountMap}
    {evm0S evm1S evmAfter : EVM.State}
    {out0 out1 mem rdata : ByteArray} {k C : ℕ}
    {feeOn amount0 amount1 balance0 balance1 reserve0 reserve1 liquidity toWord sel :
      UInt256}
    (nextLocals : Store) (rootLiquidity : Int) (recipient : AccountAddress)
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
    (hto : nextLocals.get? "to" = some (.address recipient))
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
      [UInt256.ofNat rootLiquidity.toNat, ⟨1000⟩, ⟨3742⟩, ⟨0⟩, feeOn,
        amount1, amount0, balance1, balance0, reserve1, reserve0, ⟨0⟩, toWord,
        ⟨861⟩, sel]
      mem feeToStaticcallActiveWords rdata (cAFee, σFee) k C)
    (hrootSize : rootLiquidity.toNat < UInt256.size)
    (hrootGeMin : minimumLiquidity ≤ rootLiquidity)
    (hliquiditySource : liquidity = UInt256.ofNat (rootLiquidity - minimumLiquidity).toNat)
    (hliqNonzero : liquidity ≠ ⟨0⟩)
    (hfitSupplyMinSource :
      mintFunctionTotalSupplyNewNat evmAfter (⟨1000⟩ : UInt256) < UInt256.size)
    (hfitBalanceMinSource :
      mintFunctionToBalanceNewNat evmAfter (AccountAddress.ofNat 0)
          (⟨1000⟩ : UInt256) <
        UInt256.size)
    (htotalFitMin :
      (uniswapSlotWord ⟨0⟩ σFee I).toNat + (⟨1000⟩ : UInt256).toNat <
        UInt256.size)
    (hbalanceFitMin :
      (uniswapCodeOwnerStorageWord I
        (sstoreAccountMap I.codeOwner σFee ⟨0⟩
          (uniswapSlotWord ⟨0⟩ σFee I + (⟨1000⟩ : UInt256)))
        (uniswapInternalMintBalanceHashSlot ⟨0⟩ mem)).toNat +
          (⟨1000⟩ : UInt256).toNat <
        UInt256.size)
    (hfitSupplySource :
      mintFunctionTotalSupplyNewNat
          (mintFunctionPostState evmAfter (AccountAddress.ofNat 0) (⟨1000⟩ : UInt256))
          liquidity <
        UInt256.size)
    (hsourceOverflow :
      UInt256.size ≤
        mintFunctionToBalanceNewNat
          (mintFunctionPostState evmAfter (AccountAddress.ofNat 0) (⟨1000⟩ : UInt256))
          recipient liquidity)
    (hruntimeSupplyFit :
      let σAfterMinimum :=
        sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner σFee ⟨0⟩
            (uniswapSlotWord ⟨0⟩ σFee I + (⟨1000⟩ : UInt256)))
          (uniswapInternalMintBalanceHashSlot ⟨0⟩
            (uniswapInternalMintBalanceHashMem ⟨0⟩ mem))
          (uniswapCodeOwnerStorageWord I
            (sstoreAccountMap I.codeOwner σFee ⟨0⟩
              (uniswapSlotWord ⟨0⟩ σFee I + (⟨1000⟩ : UInt256)))
            (uniswapInternalMintBalanceHashSlot ⟨0⟩ mem) + (⟨1000⟩ : UInt256))
      (uniswapSlotWord ⟨0⟩ σAfterMinimum I).toNat + liquidity.toNat < UInt256.size)
    (hruntimeOverflow :
      let minimumMem :=
        uniswapInternalMintLogMem (⟨1000⟩ : UInt256)
          (uniswapInternalMintBalanceHashMem ⟨0⟩
            (uniswapInternalMintBalanceHashMem ⟨0⟩ mem))
      let σAfterMinimum :=
        sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner σFee ⟨0⟩
            (uniswapSlotWord ⟨0⟩ σFee I + (⟨1000⟩ : UInt256)))
          (uniswapInternalMintBalanceHashSlot ⟨0⟩
            (uniswapInternalMintBalanceHashMem ⟨0⟩ mem))
          (uniswapCodeOwnerStorageWord I
            (sstoreAccountMap I.codeOwner σFee ⟨0⟩
              (uniswapSlotWord ⟨0⟩ σFee I + (⟨1000⟩ : UInt256)))
            (uniswapInternalMintBalanceHashSlot ⟨0⟩ mem) + (⟨1000⟩ : UInt256))
      UInt256.size ≤
        (uniswapCodeOwnerStorageWord I
          (sstoreAccountMap I.codeOwner σAfterMinimum ⟨0⟩
            (uniswapSlotWord ⟨0⟩ σAfterMinimum I + liquidity))
          (uniswapInternalMintBalanceHashSlot toWord minimumMem)).toNat + liquidity.toNat)
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
  have htoAfter :
      afterMinimum.locals.get? "to" = some (.address recipient) := by
    change (((afterTotalSupplyLocals.insert "rootLiquidity" (.int rootLiquidity)).insert
      "liquidity" (uniswapUint256Value liquidity)).insert "_minimumMint" Value.unit).get?
        "to" = some (.address recipient)
    rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
      store_get_ne _ _ (by decide)]
    dsimp [afterTotalSupplyLocals]
    change (Std.HashMap.insert nextLocals "_totalSupply"
        (uniswapUint256Value (mintFunctionTotalSupplyWord evmAfter))).get? "to" =
      some (.address recipient)
    rw [store_get_ne nextLocals (k := "_totalSupply") (a := "to")
      (uniswapUint256Value (mintFunctionTotalSupplyWord evmAfter)) (by decide)]
    exact hto
  have hliqAfter :
      afterMinimum.locals.get? "liquidity" = some (uniswapUint256Value liquidity) := by
    change (((afterTotalSupplyLocals.insert "rootLiquidity" (.int rootLiquidity)).insert
      "liquidity" (uniswapUint256Value liquidity)).insert "_minimumMint" Value.unit).get?
        "liquidity" = some (uniswapUint256Value liquidity)
    rw [store_get_ne _ _ (by decide), store_get_self]
  have htail :
      ExecBlock config afterMinimum evmMinimum mintAfterLiquidityTailStmts .reverted := by
    exact uniswapMintAfterLiquidityMintBalanceOverflowReverts evmMinimum recipient liquidity
      htoAfter hliqAfter hliqNonzero hfitSupplySource hsourceOverflow
  have hthrough := execBlock_append hprefix (execBlock_append hbranch htail)
  have hbody :
      ExecTransitionBody config contract evmS (mintStore I) mintTransition.body .reverted := by
    exact ExecFuncBody.execBlockRevert (by
      simpa [mintTransition, mintLiquidityBranchStmt, mintInitialLiquidityBranchStmts,
        mintProportionalLiquidityBranchStmts, mintAfterLiquidityTailStmts,
        List.append_assoc, caller, afterTotalSupplyLocals] using hthrough)
  let minimumMem :=
    uniswapInternalMintLogMem (⟨1000⟩ : UInt256)
      (uniswapInternalMintBalanceHashMem ⟨0⟩
        (uniswapInternalMintBalanceHashMem ⟨0⟩ mem))
  let σAfterMinimum :=
    sstoreAccountMap I.codeOwner
      (sstoreAccountMap I.codeOwner σFee ⟨0⟩
        (uniswapSlotWord ⟨0⟩ σFee I + (⟨1000⟩ : UInt256)))
      (uniswapInternalMintBalanceHashSlot ⟨0⟩
        (uniswapInternalMintBalanceHashMem ⟨0⟩ mem))
      (uniswapCodeOwnerStorageWord I
        (sstoreAccountMap I.codeOwner σFee ⟨0⟩
          (uniswapSlotWord ⟨0⟩ σFee I + (⟨1000⟩ : UInt256)))
        (uniswapInternalMintBalanceHashSlot ⟨0⟩ mem) + (⟨1000⟩ : UInt256))
  rcases mintInitialRootLiquidityRuntimeFacts hrootSize hrootGeMin hliquiditySource with
    ⟨hrootGeWord, hliquidityRuntime⟩
  obtain ⟨_, _, rd3841⟩ :=
    uniswapMintRuntimeInitialLiquidityAfterRootEntry rd2531 hliquidityRuntime
      hrootGeWord hperm htotalFitMin hbalanceFitMin hmem hmem64
  obtain ⟨_, _, rd8128⟩ :=
    uniswapMintRuntimeLiquidityMintEntry rd3841 hliqNonzero
  have hminimumMemSize : minimumMem.size = 164 := by
    simpa [minimumMem, hmem] using
      uniswapInternalMintSuccessMem_size_of_ge160 ⟨0⟩ (⟨1000⟩ : UInt256)
        (mem := mem) (by rw [hmem]; omega)
  have hminimumMem64 : minimumMem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
    simpa [minimumMem] using
      uniswapInternalMintSuccessMem_read64_of_ge160 ⟨0⟩ (⟨1000⟩ : UInt256)
        (by rw [hmem]; omega) hmem64
  have rdRev :
      RDrev uniswapV2PairBytecode (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) :=
    uniswapInternalMintRuntimeBalanceOverflowReverts
      (value := liquidity) (recipient := toWord) (ret := ⟨3914⟩)
      (R := [⟨0⟩, feeOn, amount1, amount0, balance1, balance0, reserve1, reserve0,
        liquidity, toWord, ⟨861⟩, sel])
      (σ := σAfterMinimum) rd8128 hperm
      (by simpa [minimumMem, σAfterMinimum] using hruntimeSupplyFit)
      (by simpa [minimumMem, σAfterMinimum] using hruntimeOverflow)
      hminimumMemSize hminimumMem64
      (by simp only [List.length_cons, List.length_nil]; omega)
  exact rdRev.reEquivExecutionRevert hcode hdispatch (uniswapDecode_mint_ok hsz36) hbody

end UniswapV2Pair
