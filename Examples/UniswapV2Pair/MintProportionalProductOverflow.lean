import Examples.UniswapV2Pair.MintInitialProductOverflow
import Examples.UniswapV2Pair.MintLiquidityZeroCases

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace UniswapV2Pair

def mintProportionalProductOverflowCase
    (feeToWord totalSupply totalSupplyCleared amount0 amount1 reserve0 reserve1 : UInt256)
    (σFee : AccountMap) (I : ExecutionEnv) : Prop :=
  (UInt256.land feeToWord solcAddrMask = ⟨0⟩ ∧
    mintFeeKLastSlotWord σFee I = ⟨0⟩ ∧
    totalSupply ≠ ⟨0⟩ ∧
    (UInt256.size ≤ amount0.toNat * totalSupply.toNat ∨
      amount0.toNat * totalSupply.toNat < UInt256.size ∧
        reserve0 ≠ ⟨0⟩ ∧ UInt256.size ≤ amount1.toNat * totalSupply.toNat)) ∨
  (UInt256.land feeToWord solcAddrMask ≠ ⟨0⟩ ∧
    mintFeeKLastSlotWord σFee I = ⟨0⟩ ∧
    totalSupply ≠ ⟨0⟩ ∧
    (UInt256.size ≤ amount0.toNat * totalSupply.toNat ∨
      amount0.toNat * totalSupply.toNat < UInt256.size ∧
        reserve0 ≠ ⟨0⟩ ∧ UInt256.size ≤ amount1.toNat * totalSupply.toNat)) ∨
  (UInt256.land feeToWord solcAddrMask = ⟨0⟩ ∧
    mintFeeKLastSlotWord σFee I ≠ ⟨0⟩ ∧
    totalSupplyCleared ≠ ⟨0⟩ ∧
    (UInt256.size ≤ amount0.toNat * totalSupplyCleared.toNat ∨
      amount0.toNat * totalSupplyCleared.toNat < UInt256.size ∧
        reserve0 ≠ ⟨0⟩ ∧ UInt256.size ≤ amount1.toNat * totalSupplyCleared.toNat))

theorem evalExpr_mint_namedProduct_overflow
    {locals : Store} (evm : EVM.State) (xName yName : Ident) (x y : UInt256)
    (hx : locals.get? xName = some (uniswapUint256Value x))
    (hy : locals.get? yName = some (uniswapUint256Value y))
    (hover : UInt256.size ≤ x.toNat * y.toNat) :
    evalExpr? config { contract := contract, locals := locals } evm
      (u256 (.binary .mul (.var xName) (.var yName))) = .revert := by
  have hge : Int.ofNat (x.toNat * y.toNat) ≥ (2 : Int) ^ 256 := by
    rw [UInt256.size] at hover
    exact Int.ofNat_le.mpr hover
  simp only [u256, evalExpr?, EvalResult.ofOption, hx, hy, EvalResult.bind, bind, pure]
  simp only [evalBinaryOp?, uint256Int]
  rw [if_pos]
  simp only [Bool.or_eq_true, decide_eq_true_eq]
  exact Or.inr (by simpa [Nat.cast_mul] using hge)

theorem evalExpr_mint_proportionalLiquidity0_overflow
    {locals : Store} (evm : EVM.State) (amount0 totalSupply : UInt256)
    (hamount0 : locals.get? "amount0" = some (uniswapUint256Value amount0))
    (htotal : locals.get? "_totalSupply" = some (uniswapUint256Value totalSupply))
    (hover : UInt256.size ≤ amount0.toNat * totalSupply.toNat) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.binary .div
        (u256 (.binary .mul (.var "amount0") (.var "_totalSupply")))
        (.var "_reserve0")) = .revert := by
  have hmul :=
    evalExpr_mint_namedProduct_overflow (locals := locals) evm "amount0" "_totalSupply"
      amount0 totalSupply hamount0 htotal hover
  simp only [evalExpr?, hmul, EvalResult.bind, bind]

theorem evalExpr_mint_proportionalLiquidity1_overflow
    {locals : Store} (evm : EVM.State) (amount1 totalSupply : UInt256)
    (hamount1 : locals.get? "amount1" = some (uniswapUint256Value amount1))
    (htotal : locals.get? "_totalSupply" = some (uniswapUint256Value totalSupply))
    (hover : UInt256.size ≤ amount1.toNat * totalSupply.toNat) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.binary .div
        (u256 (.binary .mul (.var "amount1") (.var "_totalSupply")))
        (.var "_reserve1")) = .revert := by
  have hmul :=
    evalExpr_mint_namedProduct_overflow (locals := locals) evm "amount1" "_totalSupply"
      amount1 totalSupply hamount1 htotal hover
  simp only [evalExpr?, hmul, EvalResult.bind, bind]

theorem uniswapMintProportionalLiquidity0ProductOverflowReverts
    {locals : Store} (evm : EVM.State)
    (amount0 totalSupply : UInt256)
    (htotal : locals.get? "_totalSupply" = some (uniswapUint256Value totalSupply))
    (htotalNonzero : totalSupply ≠ ⟨0⟩)
    (hamount0 : locals.get? "amount0" = some (uniswapUint256Value amount0))
    (hover : UInt256.size ≤ amount0.toNat * totalSupply.toNat) :
    ExecStmt config { contract := contract, locals := locals } evm
      mintLiquidityBranchStmt .reverted := by
  have hcond := evalExpr_mint_totalSupply_eq_zero_false evm totalSupply htotal htotalNonzero
  have hliq0 :=
    evalExpr_mint_proportionalLiquidity0_overflow (locals := locals) evm amount0
      totalSupply hamount0 htotal hover
  refine ExecStmt.iteFalse hcond ?_
  change ExecBlock config { contract := contract, locals := locals } evm
    mintProportionalLiquidityBranchStmts .reverted
  exact ExecBlock.consRevert (ExecStmt.letDeclRevert hliq0)

theorem uniswapMintProportionalLiquidity1ProductOverflowReverts
    {locals : Store} (evm : EVM.State)
    (amount0 amount1 totalSupply reserve0 : UInt256)
    (htotal : locals.get? "_totalSupply" = some (uniswapUint256Value totalSupply))
    (htotalNonzero : totalSupply ≠ ⟨0⟩)
    (hamount0 : locals.get? "amount0" = some (uniswapUint256Value amount0))
    (hamount1 : locals.get? "amount1" = some (uniswapUint256Value amount1))
    (hreserve0 : locals.get? "_reserve0" = some (.int (Int.ofNat reserve0.toNat)))
    (hfit0 : mintAmountProductNat amount0 totalSupply < UInt256.size)
    (hreserve0Nonzero : reserve0 ≠ ⟨0⟩)
    (hover : UInt256.size ≤ amount1.toNat * totalSupply.toNat) :
    ExecStmt config { contract := contract, locals := locals } evm
      mintLiquidityBranchStmt .reverted := by
  let liquidity0 := mintProportionalLiquidityWord amount0 totalSupply reserve0
  let locals0 :=
    locals.insert "liquidity0" (mintProportionalLiquidityValue amount0 totalSupply reserve0)
  have hcond := evalExpr_mint_totalSupply_eq_zero_false evm totalSupply htotal htotalNonzero
  have hliq0 :
      evalExpr? config { contract := contract, locals := locals } evm
        (.binary .div
          (u256 (.binary .mul (.var "amount0") (.var "_totalSupply")))
          (.var "_reserve0")) =
          .ok (mintProportionalLiquidityValue amount0 totalSupply reserve0) :=
    evalExpr_mint_proportionalLiquidity_of_get evm "amount0" "_reserve0" amount0
      totalSupply reserve0 hamount0 htotal hreserve0 hfit0 hreserve0Nonzero
  have hamount1' :
      locals0.get? "amount1" = some (uniswapUint256Value amount1) := by
    change (locals.insert "liquidity0"
      (mintProportionalLiquidityValue amount0 totalSupply reserve0)).get? "amount1" =
        some (uniswapUint256Value amount1)
    rw [store_get_ne _ _ (by decide), hamount1]
  have htotal' :
      locals0.get? "_totalSupply" = some (uniswapUint256Value totalSupply) := by
    change (locals.insert "liquidity0"
      (mintProportionalLiquidityValue amount0 totalSupply reserve0)).get? "_totalSupply" =
        some (uniswapUint256Value totalSupply)
    rw [store_get_ne _ _ (by decide), htotal]
  have hliq1 :=
    evalExpr_mint_proportionalLiquidity1_overflow (locals := locals0) evm amount1
      totalSupply hamount1' htotal' hover
  refine ExecStmt.iteFalse hcond ?_
  change ExecBlock config { contract := contract, locals := locals } evm
    mintProportionalLiquidityBranchStmts .reverted
  refine ExecBlock.consNormal (ExecStmt.letDecl hliq0) ?_
  exact ExecBlock.consRevert (ExecStmt.letDeclRevert hliq1)

set_option maxHeartbeats 1000000 in
theorem uniswapMintRuntimeProportionalLiquidity0ProductOverflowReverts
    {cA gh bl σ σ₀ A I} {g : UInt256}
    {cAFee : Batteries.RBSet AccountAddress compare} {σFee : AccountMap}
    {mem rdata : ByteArray} {k C : ℕ}
    {feeOn totalSupply amount0 amount1 balance0 balance1 reserve0 reserve1 toWord sel :
      UInt256}
    (rd3762 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨3762⟩
      [totalSupply, feeOn, amount1, amount0, balance1, balance0, reserve1, reserve0, ⟨0⟩,
        toWord, ⟨861⟩, sel]
      mem feeToStaticcallActiveWords rdata (cAFee, σFee) k C)
    (hclean0 : UInt256.land reserve0 reserve112Mask = reserve0)
    (hover : UInt256.size ≤ amount0.toNat * totalSupply.toNat)
    (hmem : mem.size = 164)
    (hmem64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    RDrev uniswapV2PairBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) := by
  have rd6780pre := evm_run rd3762 with [
    jumpdest, push2 ⟨3838⟩, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨112⟩, shl, sub,
    dup10, and, push2 ⟨3791⟩, dup7, dup5, push4 ⟨0xffffffff⟩, push2 ⟨6780⟩,
    and]
  rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨112⟩) ⟨1⟩ =
      reserve112Mask from by rfl,
    hclean0,
    show UInt256.land (⟨6780⟩ : UInt256) ⟨0xffffffff⟩ = ⟨6780⟩ from by decide]
    at rd6780pre
  have rd6780 := rd6780pre.jump (by native_decide) (by jump_dest) (by evm_ov)
  exact RD.uniswapSafeMathMulOverflow_feeToStaticcall_size164
    (a := amount0) (b := totalSupply) rd6780 hover hmem hmem64
    (by simp only [List.length_cons, List.length_nil]; omega)

set_option maxHeartbeats 1000000 in
theorem uniswapMintRuntimeProportionalLiquidity1ProductOverflowReverts
    {cA gh bl σ σ₀ A I} {g : UInt256}
    {cAFee : Batteries.RBSet AccountAddress compare} {σFee : AccountMap}
    {mem rdata : ByteArray} {k C : ℕ}
    {feeOn totalSupply amount0 amount1 balance0 balance1 reserve0 reserve1 toWord sel :
      UInt256}
    (rd3762 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨3762⟩
      [totalSupply, feeOn, amount1, amount0, balance1, balance0, reserve1, reserve0, ⟨0⟩,
        toWord, ⟨861⟩, sel]
      mem feeToStaticcallActiveWords rdata (cAFee, σFee) k C)
    (hclean0 : UInt256.land reserve0 reserve112Mask = reserve0)
    (hclean1 : UInt256.land reserve1 reserve112Mask = reserve1)
    (hfit0 : amount0.toNat * totalSupply.toNat < UInt256.size)
    (hreserve0Nonzero : reserve0 ≠ ⟨0⟩)
    (hover : UInt256.size ≤ amount1.toNat * totalSupply.toNat)
    (hmem : mem.size = 164)
    (hmem64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    RDrev uniswapV2PairBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) := by
  obtain ⟨_, _, rd3800⟩ :=
    uniswapMintRuntimeProportionalLiquidity0Entry rd3762 hclean0 hfit0 hreserve0Nonzero
  have rd6780pre := evm_run rd3800 with [
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨112⟩, shl, sub, dup10, and,
    push2 ⟨3825⟩, dup7, dup6, push4 ⟨0xffffffff⟩, push2 ⟨6780⟩, and]
  rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨112⟩) ⟨1⟩ =
      reserve112Mask from by rfl,
    hclean1,
    show UInt256.land (⟨6780⟩ : UInt256) ⟨0xffffffff⟩ = ⟨6780⟩ from by decide]
    at rd6780pre
  have rd6780 := rd6780pre.jump (by native_decide) (by jump_dest) (by evm_ov)
  exact RD.uniswapSafeMathMulOverflow_feeToStaticcall_size164
    (a := amount1) (b := totalSupply) rd6780 hover hmem hmem64
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem uniswapMintAfterMintFeeProportionalProduct0OverflowReverts_of_call
    (evm evm0 evm1 evmAfter : EVM.State) (I : ExecutionEnv) (nextLocals : Store)
    {out0 out1 : ByteArray} {balance0 balance1 amount0 : UInt256}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hunlocked : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨12⟩ = ⟨1⟩)
    (hguard0 :
      evalExpr? config
        { contract := contract, locals := mintReserveStore (uniswapLockEnteredState evm) I }
        (uniswapLockEnteredState evm)
        (.binary .gt (.extCodeSize (.storage token0Ref)) (.intLit 0)) = .ok (.bool true))
    (hguard1 :
      evalExpr? config
        { contract := contract,
          locals := (mintReserveStore (uniswapLockEnteredState evm) I).insert "balance0"
            (uniswapUint256Value balance0) } evm0
        (.binary .gt (.extCodeSize (.storage token1Ref)) (.intLit 0)) = .ok (.bool true))
    (hcall0 : typedCallViaEVM config (uniswapLockEnteredState evm)
      (EVM.address (uniswapAddressAtSlot (uniswapLockEnteredState evm) ⟨6⟩))
      "balanceOf" 0 [.address (uniswapLockEnteredState evm).executionEnv.codeOwner]
      (true, evm0, out0) false)
    (hdec0 :
      config.externalABI.decode? "balanceOf" out0 = some [uniswapUint256Value balance0])
    (hcall1 : typedCallViaEVM config evm0
      (EVM.address (uniswapAddressAtSlot evm0 ⟨7⟩)) "balanceOf" 0
      [.address evm0.executionEnv.codeOwner] (true, evm1, out1) false)
    (hdec1 :
      config.externalABI.decode? "balanceOf" out1 = some [uniswapUint256Value balance1])
    (henough0 : (uniswapReserve0Word (uniswapLockEnteredState evm)).toNat ≤ balance0.toNat)
    (henough1 : (uniswapReserve1Word (uniswapLockEnteredState evm)).toNat ≤ balance1.toNat)
    (hfee :
      ExecStmt config
        { contract := contract,
          locals := mintAmountStore (uniswapLockEnteredState evm) I balance0 balance1 }
        evm1 (.internalCall "_mintFee" [.var "_reserve0", .var "_reserve1"] "feeOn")
        (.ok { contract := contract, locals := nextLocals } evmAfter))
    (htotalBase : nextLocals.get? "totalSupply" = none)
    (hamount0 : nextLocals.get? "amount0" = some (uniswapUint256Value amount0))
    (htotalNonzero : mintFunctionTotalSupplyWord evmAfter ≠ ⟨0⟩)
    (hover :
      UInt256.size ≤ amount0.toNat * (mintFunctionTotalSupplyWord evmAfter).toNat) :
    ExecBlock config { contract := contract, locals := mintStore I } evm
      mintTransition.body .reverted := by
  let totalSupply := mintFunctionTotalSupplyWord evmAfter
  let afterTotalSupplyLocals :=
    nextLocals.insert "_totalSupply" (uniswapUint256Value totalSupply)
  have hprefix :=
    uniswapMintAfterMintFeeTotalSupplyPrefix_of_call evm evm0 evm1 evmAfter I nextLocals
      hwv hunlocked hguard0 hguard1 hcall0 hdec0 hcall1 hdec1 henough0 henough1 hfee
      htotalBase
  have htotal' :
      afterTotalSupplyLocals.get? "_totalSupply" =
        some (uniswapUint256Value totalSupply) := by
    change (nextLocals.insert "_totalSupply" (uniswapUint256Value totalSupply)).get?
      "_totalSupply" = some (uniswapUint256Value totalSupply)
    rw [store_get_self]
  have hamount0' :
      afterTotalSupplyLocals.get? "amount0" = some (uniswapUint256Value amount0) := by
    change (nextLocals.insert "_totalSupply" (uniswapUint256Value totalSupply)).get?
      "amount0" = some (uniswapUint256Value amount0)
    rw [store_get_ne _ _ (by decide), hamount0]
  have htail :
      ExecBlock config { contract := contract, locals := afterTotalSupplyLocals } evmAfter
        ([mintLiquidityBranchStmt] ++ mintAfterLiquidityTailStmts) .reverted := by
    have hstmt :
        ExecStmt config { contract := contract, locals := afterTotalSupplyLocals } evmAfter
          mintLiquidityBranchStmt .reverted :=
      uniswapMintProportionalLiquidity0ProductOverflowReverts
        (locals := afterTotalSupplyLocals) evmAfter amount0 totalSupply htotal'
        (by simpa [totalSupply] using htotalNonzero) hamount0'
        (by simpa [totalSupply] using hover)
    exact ExecBlock.consRevert hstmt
  have hthrough := execBlock_append hprefix htail
  simpa [mintTransition, mintAfterLiquidityTailStmts, afterTotalSupplyLocals,
    totalSupply, List.append_assoc] using hthrough

theorem uniswapMintAfterMintFeeProportionalProduct1OverflowReverts_of_call
    (evm evm0 evm1 evmAfter : EVM.State) (I : ExecutionEnv) (nextLocals : Store)
    {out0 out1 : ByteArray} {balance0 balance1 amount0 amount1 reserve0 : UInt256}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hunlocked : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨12⟩ = ⟨1⟩)
    (hguard0 :
      evalExpr? config
        { contract := contract, locals := mintReserveStore (uniswapLockEnteredState evm) I }
        (uniswapLockEnteredState evm)
        (.binary .gt (.extCodeSize (.storage token0Ref)) (.intLit 0)) = .ok (.bool true))
    (hguard1 :
      evalExpr? config
        { contract := contract,
          locals := (mintReserveStore (uniswapLockEnteredState evm) I).insert "balance0"
            (uniswapUint256Value balance0) } evm0
        (.binary .gt (.extCodeSize (.storage token1Ref)) (.intLit 0)) = .ok (.bool true))
    (hcall0 : typedCallViaEVM config (uniswapLockEnteredState evm)
      (EVM.address (uniswapAddressAtSlot (uniswapLockEnteredState evm) ⟨6⟩))
      "balanceOf" 0 [.address (uniswapLockEnteredState evm).executionEnv.codeOwner]
      (true, evm0, out0) false)
    (hdec0 :
      config.externalABI.decode? "balanceOf" out0 = some [uniswapUint256Value balance0])
    (hcall1 : typedCallViaEVM config evm0
      (EVM.address (uniswapAddressAtSlot evm0 ⟨7⟩)) "balanceOf" 0
      [.address evm0.executionEnv.codeOwner] (true, evm1, out1) false)
    (hdec1 :
      config.externalABI.decode? "balanceOf" out1 = some [uniswapUint256Value balance1])
    (henough0 : (uniswapReserve0Word (uniswapLockEnteredState evm)).toNat ≤ balance0.toNat)
    (henough1 : (uniswapReserve1Word (uniswapLockEnteredState evm)).toNat ≤ balance1.toNat)
    (hfee :
      ExecStmt config
        { contract := contract,
          locals := mintAmountStore (uniswapLockEnteredState evm) I balance0 balance1 }
        evm1 (.internalCall "_mintFee" [.var "_reserve0", .var "_reserve1"] "feeOn")
        (.ok { contract := contract, locals := nextLocals } evmAfter))
    (htotalBase : nextLocals.get? "totalSupply" = none)
    (hamount0 : nextLocals.get? "amount0" = some (uniswapUint256Value amount0))
    (hamount1 : nextLocals.get? "amount1" = some (uniswapUint256Value amount1))
    (hreserve0 : nextLocals.get? "_reserve0" = some (.int (Int.ofNat reserve0.toNat)))
    (htotalNonzero : mintFunctionTotalSupplyWord evmAfter ≠ ⟨0⟩)
    (hfit0 :
      mintAmountProductNat amount0 (mintFunctionTotalSupplyWord evmAfter) < UInt256.size)
    (hreserve0Nonzero : reserve0 ≠ ⟨0⟩)
    (hover :
      UInt256.size ≤ amount1.toNat * (mintFunctionTotalSupplyWord evmAfter).toNat) :
    ExecBlock config { contract := contract, locals := mintStore I } evm
      mintTransition.body .reverted := by
  let totalSupply := mintFunctionTotalSupplyWord evmAfter
  let afterTotalSupplyLocals :=
    nextLocals.insert "_totalSupply" (uniswapUint256Value totalSupply)
  have hprefix :=
    uniswapMintAfterMintFeeTotalSupplyPrefix_of_call evm evm0 evm1 evmAfter I nextLocals
      hwv hunlocked hguard0 hguard1 hcall0 hdec0 hcall1 hdec1 henough0 henough1 hfee
      htotalBase
  have htotal' :
      afterTotalSupplyLocals.get? "_totalSupply" =
        some (uniswapUint256Value totalSupply) := by
    change (nextLocals.insert "_totalSupply" (uniswapUint256Value totalSupply)).get?
      "_totalSupply" = some (uniswapUint256Value totalSupply)
    rw [store_get_self]
  have hamount0' :
      afterTotalSupplyLocals.get? "amount0" = some (uniswapUint256Value amount0) := by
    change (nextLocals.insert "_totalSupply" (uniswapUint256Value totalSupply)).get?
      "amount0" = some (uniswapUint256Value amount0)
    rw [store_get_ne _ _ (by decide), hamount0]
  have hamount1' :
      afterTotalSupplyLocals.get? "amount1" = some (uniswapUint256Value amount1) := by
    change (nextLocals.insert "_totalSupply" (uniswapUint256Value totalSupply)).get?
      "amount1" = some (uniswapUint256Value amount1)
    rw [store_get_ne _ _ (by decide), hamount1]
  have hreserve0' :
      afterTotalSupplyLocals.get? "_reserve0" =
        some (.int (Int.ofNat reserve0.toNat)) := by
    change (nextLocals.insert "_totalSupply" (uniswapUint256Value totalSupply)).get?
      "_reserve0" = some (.int (Int.ofNat reserve0.toNat))
    rw [store_get_ne _ _ (by decide), hreserve0]
  have htail :
      ExecBlock config { contract := contract, locals := afterTotalSupplyLocals } evmAfter
        ([mintLiquidityBranchStmt] ++ mintAfterLiquidityTailStmts) .reverted := by
    have hstmt :
        ExecStmt config { contract := contract, locals := afterTotalSupplyLocals } evmAfter
          mintLiquidityBranchStmt .reverted :=
      uniswapMintProportionalLiquidity1ProductOverflowReverts
        (locals := afterTotalSupplyLocals) evmAfter amount0 amount1 totalSupply reserve0
        htotal' (by simpa [totalSupply] using htotalNonzero) hamount0' hamount1'
        hreserve0' (by simpa [totalSupply] using hfit0) hreserve0Nonzero
        (by simpa [totalSupply] using hover)
    exact ExecBlock.consRevert hstmt
  have hthrough := execBlock_append hprefix htail
  simpa [mintTransition, mintAfterLiquidityTailStmts, afterTotalSupplyLocals,
    totalSupply, List.append_assoc] using hthrough

set_option maxHeartbeats 1000000 in
theorem uniswapMintProportionalProduct0OverflowAfterMintFeeCase
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {cAFee : Batteries.RBSet AccountAddress compare} {σFee : AccountMap}
    {evm0S evm1S evmFeeS : EVM.State}
    {out0 out1 mem rdata : ByteArray} {k C : ℕ}
    {feeOnFlag totalSupply amount0 amount1 balance0 balance1 reserve0 reserve1 toWord sel :
      UInt256}
    (nextLocals : Store)
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
    (hle0Source :
      (uniswapReserve0Word
        (uniswapLockEnteredState
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I))).toNat ≤
          balance0.toNat)
    (hle1Source :
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
                (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)) I balance0 balance1 }
        evm1S (.internalCall "_mintFee" [.var "_reserve0", .var "_reserve1"] "feeOn")
        (.ok { contract := contract, locals := nextLocals } evmFeeS))
    (rd3701 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨3701⟩
      [feeOnFlag, ⟨0⟩, amount1, amount0, balance1, balance0, reserve1, reserve0, ⟨0⟩,
        toWord, ⟨861⟩, sel]
      mem feeToStaticcallActiveWords rdata (cAFee, σFee) k C)
    (htotalBase : nextLocals.get? "totalSupply" = none)
    (hamount0 : nextLocals.get? "amount0" = some (uniswapUint256Value amount0))
    (htotalEq : mintFunctionTotalSupplyWord evmFeeS = totalSupply)
    (htotalSlot : uniswapSlotWord ⟨0⟩ σFee I = totalSupply)
    (htotalNonzero : totalSupply ≠ ⟨0⟩)
    (hclean0 : UInt256.land reserve0 reserve112Mask = reserve0)
    (hover : UInt256.size ≤ amount0.toNat * totalSupply.toNat)
    (hmem : mem.size = 164)
    (hmem64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let evmS := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hbody :
      ExecTransitionBody config contract evmS (mintStore I) mintTransition.body .reverted := by
    exact ExecFuncBody.execBlockRevert
      (uniswapMintAfterMintFeeProportionalProduct0OverflowReverts_of_call
        evmS evm0S evm1S evmFeeS I nextLocals
        (by simp only [evmS, initState]; exact hwv) hunlockedSolm hguard0 hguard1
        hcall0 hdec0 hcall1 hdec1 hle0Source hle1Source
        (by simpa [evmS] using hfee) htotalBase hamount0
        (by simpa [htotalEq] using htotalNonzero)
        (by simpa [htotalEq] using hover))
  obtain ⟨_, _, rd3762⟩ :=
    uniswapMintRuntimeAfterMintFeeTotalSupplyNonzero rd3701 htotalSlot htotalNonzero
  have rdRev :
      RDrev uniswapV2PairBytecode (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) :=
    uniswapMintRuntimeProportionalLiquidity0ProductOverflowReverts rd3762 hclean0 hover
      hmem hmem64
  exact rdRev.reEquivExecutionRevert hcode hdispatch (uniswapDecode_mint_ok hsz36) hbody

set_option maxHeartbeats 1000000 in
theorem uniswapMintProportionalProduct1OverflowAfterMintFeeCase
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {cAFee : Batteries.RBSet AccountAddress compare} {σFee : AccountMap}
    {evm0S evm1S evmFeeS : EVM.State}
    {out0 out1 mem rdata : ByteArray} {k C : ℕ}
    {feeOnFlag totalSupply amount0 amount1 balance0 balance1 reserve0 reserve1 toWord sel :
      UInt256}
    (nextLocals : Store)
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
    (hle0Source :
      (uniswapReserve0Word
        (uniswapLockEnteredState
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I))).toNat ≤
          balance0.toNat)
    (hle1Source :
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
                (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)) I balance0 balance1 }
        evm1S (.internalCall "_mintFee" [.var "_reserve0", .var "_reserve1"] "feeOn")
        (.ok { contract := contract, locals := nextLocals } evmFeeS))
    (rd3701 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨3701⟩
      [feeOnFlag, ⟨0⟩, amount1, amount0, balance1, balance0, reserve1, reserve0, ⟨0⟩,
        toWord, ⟨861⟩, sel]
      mem feeToStaticcallActiveWords rdata (cAFee, σFee) k C)
    (htotalBase : nextLocals.get? "totalSupply" = none)
    (hamount0 : nextLocals.get? "amount0" = some (uniswapUint256Value amount0))
    (hamount1 : nextLocals.get? "amount1" = some (uniswapUint256Value amount1))
    (hreserve0 : nextLocals.get? "_reserve0" = some (.int (Int.ofNat reserve0.toNat)))
    (htotalEq : mintFunctionTotalSupplyWord evmFeeS = totalSupply)
    (htotalSlot : uniswapSlotWord ⟨0⟩ σFee I = totalSupply)
    (htotalNonzero : totalSupply ≠ ⟨0⟩)
    (hclean0 : UInt256.land reserve0 reserve112Mask = reserve0)
    (hclean1 : UInt256.land reserve1 reserve112Mask = reserve1)
    (hfit0 : amount0.toNat * totalSupply.toNat < UInt256.size)
    (hreserve0Nonzero : reserve0 ≠ ⟨0⟩)
    (hover : UInt256.size ≤ amount1.toNat * totalSupply.toNat)
    (hmem : mem.size = 164)
    (hmem64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let evmS := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hbody :
      ExecTransitionBody config contract evmS (mintStore I) mintTransition.body .reverted := by
    exact ExecFuncBody.execBlockRevert
      (uniswapMintAfterMintFeeProportionalProduct1OverflowReverts_of_call
        evmS evm0S evm1S evmFeeS I nextLocals
        (by simp only [evmS, initState]; exact hwv) hunlockedSolm hguard0 hguard1
        hcall0 hdec0 hcall1 hdec1 hle0Source hle1Source
        (by simpa [evmS] using hfee) htotalBase hamount0 hamount1 hreserve0
        (by simpa [htotalEq] using htotalNonzero)
        (by simpa [mintAmountProductNat, htotalEq] using hfit0) hreserve0Nonzero
        (by simpa [htotalEq] using hover))
  obtain ⟨_, _, rd3762⟩ :=
    uniswapMintRuntimeAfterMintFeeTotalSupplyNonzero rd3701 htotalSlot htotalNonzero
  have rdRev :
      RDrev uniswapV2PairBytecode (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) :=
    uniswapMintRuntimeProportionalLiquidity1ProductOverflowReverts rd3762 hclean0 hclean1
      hfit0 hreserve0Nonzero hover hmem hmem64
  exact rdRev.reEquivExecutionRevert hcode hdispatch (uniswapDecode_mint_ok hsz36) hbody

set_option maxHeartbeats 1000000 in
theorem uniswapMintProportionalFeeOffKLastZeroProductOverflowFromFactoryCase
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {cAFee : Batteries.RBSet AccountAddress compare} {σFee σ'' : AccountMap}
    {evm0S evm1S evmFeeS : EVM.State}
    {out0 out1 outFee o o1 : ByteArray} {k C : ℕ}
    {totalSupply amount0 amount1 balance0 balance1 reserve0 reserve1 toWord sel : UInt256}
    {zFee : Bool}
    (feeTo : AccountAddress)
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
    (hle0Source :
      (uniswapReserve0Word
        (uniswapLockEnteredState
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I))).toNat ≤
          balance0.toNat)
    (hle1Source :
      (uniswapReserve1Word
        (uniswapLockEnteredState
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I))).toNat ≤
          balance1.toNat)
    (hfeeGuard :
      evalExpr? config
        (mintFeeCallFrame
          (uniswapReserve0Word
            (uniswapLockEnteredState
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)))
          (uniswapReserve1Word
            (uniswapLockEnteredState
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I))))
        evm1S (.binary .gt (.extCodeSize (.storage factoryRef)) (.intLit 0)) =
          .ok (.bool true))
    (hfeeCall : typedCallViaEVM config evm1S
      (EVM.address (uniswapAddressAtSlot evm1S ⟨5⟩)) "feeTo" 0 []
      (true, evmFeeS, outFee) false)
    (hfeeDec : config.externalABI.decode? "feeTo" outFee = some [.address feeTo])
    (hfeeToEq : feeTo = AccountAddress.ofNat (fromByteArrayBigEndian (outFee.extract 0 32)))
    (rd7781 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨7781⟩
      [(if zFee then (⟨1⟩ : UInt256) else ⟨0⟩), ⟨132⟩,
        feeToSelectorWord, mintFeeFactoryWord σ'' I, ⟨0⟩, ⟨0⟩,
        reserve1Word (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩) I,
        reserve0Word (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩) I,
        ⟨3701⟩, ⟨0⟩, amount1, amount0, balance1, balance0,
        reserve1Word (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩) I,
        reserve0Word (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩) I,
        ⟨0⟩, toWord, ⟨861⟩, sel]
      (feeToStaticcallMem
        (balanceOfThisRebuiltStaticcallMem (UInt256.ofNat I.codeOwner.val) o o1)
        outFee)
      feeToStaticcallActiveWords outFee (cAFee, σFee) k C)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (ho132 : 32 ≤ o1.size) (ho1Size : o1.size < UInt256.size)
    (houtFeeSize : outFee.size < UInt256.size)
    (hzFeeTrue : zFee = true)
    (houtFee32 : 32 ≤ outFee.size)
    (hkLastEq : mintFeeKLastWord evmFeeS = mintFeeKLastSlotWord σFee I)
    (htotalEq : mintFunctionTotalSupplyWord evmFeeS = totalSupply)
    (htotalSlot : uniswapSlotWord ⟨0⟩ σFee I = totalSupply)
    (hreserve0Eq :
      uniswapReserve0Word
          (uniswapLockEnteredState
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)) =
        reserve0)
    (hreserve1Eq :
      uniswapReserve1Word
          (uniswapLockEnteredState
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)) =
        reserve1)
    (hruntimeReserve0 :
      reserve0Word (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩) I = reserve0)
    (hruntimeReserve1 :
      reserve1Word (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩) I = reserve1)
    (hamount0Eq :
      mintAmount0Word
          (uniswapLockEnteredState
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)) balance0 =
        amount0)
    (hamount1Eq :
      mintAmount1Word
          (uniswapLockEnteredState
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)) balance1 =
        amount1)
    (hfeeToZero :
      UInt256.land (UInt256.ofNat (fromByteArrayBigEndian (outFee.extract 0 32)))
          solcAddrMask =
        ⟨0⟩)
    (hkLastZero : mintFeeKLastSlotWord σFee I = ⟨0⟩)
    (htotalNonzero : totalSupply ≠ ⟨0⟩)
    (hover :
      UInt256.size ≤ amount0.toNat * totalSupply.toNat ∨
        amount0.toNat * totalSupply.toNat < UInt256.size ∧
          reserve0 ≠ ⟨0⟩ ∧ UInt256.size ≤ amount1.toNat * totalSupply.toNat) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let evmS := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmL := uniswapLockEnteredState evmS
  let nextFrame :=
    resumeAfterInternalCall
      { contract := contract, locals := mintAmountStore evmL I balance0 balance1 }
      "feeOn" (some [.bool false])
  let memFee :=
    feeToStaticcallMem
      (balanceOfThisRebuiltStaticcallMem (UInt256.ofNat I.codeOwner.val) o o1)
      outFee
  have hmem : memFee.size = 164 := by
    dsimp [memFee]
    exact feeToStaticcallMem_size_of_size_ge
      (UInt256.ofNat I.codeOwner.val) o o1 outFee ho32 hoSize ho132 ho1Size houtFee32
      houtFeeSize
  have hmem64 : memFee.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
    dsimp [memFee]
    exact feeToStaticcallMem_read64_of_size_ge
      (UInt256.ofNat I.codeOwner.val) o o1 outFee ho32 hoSize ho132 ho1Size houtFee32
      houtFeeSize
  have hfeeToAddr : feeTo = AccountAddress.ofNat 0 := by
    rw [hfeeToEq]
    exact accountAddress_ofNat_eq_zero_of_land_solcAddrMask_eq_zero
      (fromByteArrayBigEndian_extract0_32_lt houtFee32) hfeeToZero
  have hkLastSource : (mintFeeKLastWord evmFeeS).toNat = 0 := by
    rw [hkLastEq, hkLastZero]
    rfl
  obtain ⟨_, _, rd3701⟩ :=
    uniswapMintFeeRuntimeFactoryResultFeeOffKLastZeroReturn
      rd7781 ho32 hoSize ho132 ho1Size houtFeeSize hzFeeTrue houtFee32 hfeeToZero
      hkLastZero
  have hfee :
      ExecStmt config
        { contract := contract, locals := mintAmountStore evmL I balance0 balance1 }
        evm1S (.internalCall "_mintFee" [.var "_reserve0", .var "_reserve1"] "feeOn")
        (.ok { contract := contract, locals := nextFrame.locals } evmFeeS) := by
    simpa [nextFrame, evmL, evmS, resumeAfterInternalCall] using
      uniswapMintFeeCallFromMint_feeOff_kLastZero evmL evm1S evmFeeS I balance0
        balance1 feeTo (by simpa [evmL, evmS] using hfeeGuard) hfeeCall hfeeDec
        hfeeToAddr hkLastSource
  have hbase : nextFrame.locals.get? "totalSupply" = none := by
    simpa [nextFrame, evmL, evmS] using
      mintAfterMintFeeCallStore_totalSupply evmL I balance0 balance1 false
  have hamount0Get : nextFrame.locals.get? "amount0" = some (uniswapUint256Value amount0) := by
    simpa [nextFrame, evmL, evmS, mintAmount0Value, hamount0Eq] using
      mintAfterMintFeeCallStore_amount0 evmL I balance0 balance1 false
  have hclean0 : UInt256.land reserve0 reserve112Mask = reserve0 :=
    reserve112Mask_clean_of_lt _ (by
      rw [← hruntimeReserve0]
      dsimp [reserve0Word]
      exact reserve112Word_lt _)
  rcases hover with hover0 | hover1
  · exact uniswapMintProportionalProduct0OverflowAfterMintFeeCase nextFrame.locals
      hcode hdispatch hsz36 hwv hunlockedSolm hguard0 hguard1 hcall0 hdec0 hcall1 hdec1
      hle0Source hle1Source hfee (by
        simpa [memFee, hruntimeReserve0, hruntimeReserve1] using rd3701)
      hbase hamount0Get htotalEq htotalSlot htotalNonzero hclean0 hover0 hmem hmem64
  · rcases hover1 with ⟨hfit0, hreserve0Nonzero, hover1⟩
    have hamount1Get :
        nextFrame.locals.get? "amount1" = some (uniswapUint256Value amount1) := by
      simpa [nextFrame, evmL, evmS, mintAmount1Value, hamount1Eq] using
        mintAfterMintFeeCallStore_amount1 evmL I balance0 balance1 false
    have hreserve0Get :
        nextFrame.locals.get? "_reserve0" = some (.int (Int.ofNat reserve0.toNat)) := by
      simpa [nextFrame, evmL, evmS, hreserve0Eq] using
        mintAfterMintFeeCallStore_reserve0 evmL I balance0 balance1 false
    have hclean1 : UInt256.land reserve1 reserve112Mask = reserve1 :=
      reserve112Mask_clean_of_lt _ (by
        rw [← hruntimeReserve1]
        dsimp [reserve1Word]
        exact reserve112Word_lt _)
    exact uniswapMintProportionalProduct1OverflowAfterMintFeeCase nextFrame.locals
      hcode hdispatch hsz36 hwv hunlockedSolm hguard0 hguard1 hcall0 hdec0 hcall1 hdec1
      hle0Source hle1Source hfee (by
        simpa [memFee, hruntimeReserve0, hruntimeReserve1] using rd3701)
      hbase hamount0Get hamount1Get hreserve0Get htotalEq htotalSlot htotalNonzero hclean0
      hclean1 hfit0 hreserve0Nonzero hover1 hmem hmem64

set_option maxHeartbeats 1000000 in
theorem uniswapMintProportionalFeeOnKLastZeroProductOverflowFromFactoryCase
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {cAFee : Batteries.RBSet AccountAddress compare} {σFee σ'' : AccountMap}
    {evm0S evm1S evmFeeS : EVM.State}
    {out0 out1 outFee o o1 : ByteArray} {k C : ℕ}
    {totalSupply amount0 amount1 balance0 balance1 reserve0 reserve1 toWord sel : UInt256}
    {zFee : Bool}
    (feeTo : AccountAddress)
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
    (hle0Source :
      (uniswapReserve0Word
        (uniswapLockEnteredState
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I))).toNat ≤
          balance0.toNat)
    (hle1Source :
      (uniswapReserve1Word
        (uniswapLockEnteredState
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I))).toNat ≤
          balance1.toNat)
    (hfeeGuard :
      evalExpr? config
        (mintFeeCallFrame
          (uniswapReserve0Word
            (uniswapLockEnteredState
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)))
          (uniswapReserve1Word
            (uniswapLockEnteredState
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I))))
        evm1S (.binary .gt (.extCodeSize (.storage factoryRef)) (.intLit 0)) =
          .ok (.bool true))
    (hfeeCall : typedCallViaEVM config evm1S
      (EVM.address (uniswapAddressAtSlot evm1S ⟨5⟩)) "feeTo" 0 []
      (true, evmFeeS, outFee) false)
    (hfeeDec : config.externalABI.decode? "feeTo" outFee = some [.address feeTo])
    (hfeeToEq : feeTo = AccountAddress.ofNat (fromByteArrayBigEndian (outFee.extract 0 32)))
    (rd7781 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨7781⟩
      [(if zFee then (⟨1⟩ : UInt256) else ⟨0⟩), ⟨132⟩,
        feeToSelectorWord, mintFeeFactoryWord σ'' I, ⟨0⟩, ⟨0⟩,
        reserve1Word (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩) I,
        reserve0Word (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩) I,
        ⟨3701⟩, ⟨0⟩, amount1, amount0, balance1, balance0,
        reserve1Word (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩) I,
        reserve0Word (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩) I,
        ⟨0⟩, toWord, ⟨861⟩, sel]
      (feeToStaticcallMem
        (balanceOfThisRebuiltStaticcallMem (UInt256.ofNat I.codeOwner.val) o o1)
        outFee)
      feeToStaticcallActiveWords outFee (cAFee, σFee) k C)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (ho132 : 32 ≤ o1.size) (ho1Size : o1.size < UInt256.size)
    (houtFeeSize : outFee.size < UInt256.size)
    (hzFeeTrue : zFee = true)
    (houtFee32 : 32 ≤ outFee.size)
    (hkLastEq : mintFeeKLastWord evmFeeS = mintFeeKLastSlotWord σFee I)
    (htotalEq : mintFunctionTotalSupplyWord evmFeeS = totalSupply)
    (htotalSlot : uniswapSlotWord ⟨0⟩ σFee I = totalSupply)
    (hreserve0Eq :
      uniswapReserve0Word
          (uniswapLockEnteredState
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)) =
        reserve0)
    (hruntimeReserve0 :
      reserve0Word (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩) I = reserve0)
    (hruntimeReserve1 :
      reserve1Word (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩) I = reserve1)
    (hamount0Eq :
      mintAmount0Word
          (uniswapLockEnteredState
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)) balance0 =
        amount0)
    (hamount1Eq :
      mintAmount1Word
          (uniswapLockEnteredState
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)) balance1 =
        amount1)
    (hfeeToNonzero :
      UInt256.land (UInt256.ofNat (fromByteArrayBigEndian (outFee.extract 0 32)))
          solcAddrMask ≠
        ⟨0⟩)
    (hkLastZero : mintFeeKLastSlotWord σFee I = ⟨0⟩)
    (htotalNonzero : totalSupply ≠ ⟨0⟩)
    (hover :
      UInt256.size ≤ amount0.toNat * totalSupply.toNat ∨
        amount0.toNat * totalSupply.toNat < UInt256.size ∧
          reserve0 ≠ ⟨0⟩ ∧ UInt256.size ≤ amount1.toNat * totalSupply.toNat) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let evmS := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmL := uniswapLockEnteredState evmS
  let nextFrame :=
    resumeAfterInternalCall
      { contract := contract, locals := mintAmountStore evmL I balance0 balance1 }
      "feeOn" (some [.bool true])
  let memFee :=
    feeToStaticcallMem
      (balanceOfThisRebuiltStaticcallMem (UInt256.ofNat I.codeOwner.val) o o1)
      outFee
  have hmem : memFee.size = 164 := by
    dsimp [memFee]
    exact feeToStaticcallMem_size_of_size_ge
      (UInt256.ofNat I.codeOwner.val) o o1 outFee ho32 hoSize ho132 ho1Size houtFee32
      houtFeeSize
  have hmem64 : memFee.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
    dsimp [memFee]
    exact feeToStaticcallMem_read64_of_size_ge
      (UInt256.ofNat I.codeOwner.val) o o1 outFee ho32 hoSize ho132 ho1Size houtFee32
      houtFeeSize
  have hfeeToAddr : feeTo ≠ AccountAddress.ofNat 0 := by
    rw [hfeeToEq]
    exact accountAddress_ofNat_ne_zero_of_land_solcAddrMask_ne_zero
      (fromByteArrayBigEndian_extract0_32_lt houtFee32) hfeeToNonzero
  have hkLastSource : (mintFeeKLastWord evmFeeS).toNat = 0 := by
    rw [hkLastEq, hkLastZero]
    rfl
  obtain ⟨_, _, rd3701⟩ :=
    uniswapMintFeeRuntimeFactoryResultFeeOnKLastZeroReturn
      rd7781 ho32 hoSize ho132 ho1Size houtFeeSize hzFeeTrue houtFee32 hfeeToNonzero
      hkLastZero
  have hfee :
      ExecStmt config
        { contract := contract, locals := mintAmountStore evmL I balance0 balance1 }
        evm1S (.internalCall "_mintFee" [.var "_reserve0", .var "_reserve1"] "feeOn")
        (.ok { contract := contract, locals := nextFrame.locals } evmFeeS) := by
    simpa [nextFrame, evmL, evmS, resumeAfterInternalCall] using
      uniswapMintFeeCallFromMint_feeOn_kLastZero evmL evm1S evmFeeS I balance0
        balance1 feeTo (by simpa [evmL, evmS] using hfeeGuard) hfeeCall hfeeDec
        hfeeToAddr hkLastSource
  have hbase : nextFrame.locals.get? "totalSupply" = none := by
    simpa [nextFrame, evmL, evmS] using
      mintAfterMintFeeCallStore_totalSupply evmL I balance0 balance1 true
  have hamount0Get : nextFrame.locals.get? "amount0" = some (uniswapUint256Value amount0) := by
    simpa [nextFrame, evmL, evmS, mintAmount0Value, hamount0Eq] using
      mintAfterMintFeeCallStore_amount0 evmL I balance0 balance1 true
  have hclean0 : UInt256.land reserve0 reserve112Mask = reserve0 :=
    reserve112Mask_clean_of_lt _ (by
      rw [← hruntimeReserve0]
      dsimp [reserve0Word]
      exact reserve112Word_lt _)
  rcases hover with hover0 | hover1
  · exact uniswapMintProportionalProduct0OverflowAfterMintFeeCase nextFrame.locals
      hcode hdispatch hsz36 hwv hunlockedSolm hguard0 hguard1 hcall0 hdec0 hcall1 hdec1
      hle0Source hle1Source hfee (by
        simpa [memFee, hruntimeReserve0, hruntimeReserve1] using rd3701)
      hbase hamount0Get htotalEq htotalSlot htotalNonzero hclean0 hover0 hmem hmem64
  · rcases hover1 with ⟨hfit0, hreserve0Nonzero, hover1⟩
    have hamount1Get :
        nextFrame.locals.get? "amount1" = some (uniswapUint256Value amount1) := by
      simpa [nextFrame, evmL, evmS, mintAmount1Value, hamount1Eq] using
        mintAfterMintFeeCallStore_amount1 evmL I balance0 balance1 true
    have hreserve0Get :
        nextFrame.locals.get? "_reserve0" = some (.int (Int.ofNat reserve0.toNat)) := by
      simpa [nextFrame, evmL, evmS, hreserve0Eq] using
        mintAfterMintFeeCallStore_reserve0 evmL I balance0 balance1 true
    have hclean1 : UInt256.land reserve1 reserve112Mask = reserve1 :=
      reserve112Mask_clean_of_lt _ (by
        rw [← hruntimeReserve1]
        dsimp [reserve1Word]
        exact reserve112Word_lt _)
    exact uniswapMintProportionalProduct1OverflowAfterMintFeeCase nextFrame.locals
      hcode hdispatch hsz36 hwv hunlockedSolm hguard0 hguard1 hcall0 hdec0 hcall1 hdec1
      hle0Source hle1Source hfee (by
        simpa [memFee, hruntimeReserve0, hruntimeReserve1] using rd3701)
      hbase hamount0Get hamount1Get hreserve0Get htotalEq htotalSlot htotalNonzero hclean0
      hclean1 hfit0 hreserve0Nonzero hover1 hmem hmem64

set_option maxHeartbeats 1000000 in
theorem uniswapMintProportionalFeeOffKLastNonzeroProductOverflowFromFactoryCase
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {cAFee : Batteries.RBSet AccountAddress compare} {σFee σCleared σ'' : AccountMap}
    {evm0S evm1S evmFeeS : EVM.State}
    {out0 out1 outFee o o1 : ByteArray} {k C : ℕ}
    {totalSupply amount0 amount1 balance0 balance1 reserve0 reserve1 toWord sel : UInt256}
    {zFee : Bool}
    (feeTo : AccountAddress)
    (hcode : I.code = uniswapV2PairBytecode)
    (hdispatch : dispatchMsg contract I.calldata = some mintTransition)
    (hsz36 : 36 ≤ I.calldata.size)
    (hperm : I.perm = true)
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
    (hle0Source :
      (uniswapReserve0Word
        (uniswapLockEnteredState
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I))).toNat ≤
          balance0.toNat)
    (hle1Source :
      (uniswapReserve1Word
        (uniswapLockEnteredState
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I))).toNat ≤
          balance1.toNat)
    (hfeeGuard :
      evalExpr? config
        (mintFeeCallFrame
          (uniswapReserve0Word
            (uniswapLockEnteredState
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)))
          (uniswapReserve1Word
            (uniswapLockEnteredState
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I))))
        evm1S (.binary .gt (.extCodeSize (.storage factoryRef)) (.intLit 0)) =
          .ok (.bool true))
    (hfeeCall : typedCallViaEVM config evm1S
      (EVM.address (uniswapAddressAtSlot evm1S ⟨5⟩)) "feeTo" 0 []
      (true, evmFeeS, outFee) false)
    (hfeeDec : config.externalABI.decode? "feeTo" outFee = some [.address feeTo])
    (hfeeToEq : feeTo = AccountAddress.ofNat (fromByteArrayBigEndian (outFee.extract 0 32)))
    (hPostAccountsFee : accountMapEquiv σFee evmFeeS.accountMap)
    (henvFeeI : evmFeeS.executionEnv = I)
    (hcleared : sstoreAccountMap I.codeOwner σFee ⟨11⟩ ⟨0⟩ = σCleared)
    (rd7781 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨7781⟩
      [(if zFee then (⟨1⟩ : UInt256) else ⟨0⟩), ⟨132⟩,
        feeToSelectorWord, mintFeeFactoryWord σ'' I, ⟨0⟩, ⟨0⟩,
        reserve1Word (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩) I,
        reserve0Word (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩) I,
        ⟨3701⟩, ⟨0⟩, amount1, amount0, balance1, balance0,
        reserve1Word (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩) I,
        reserve0Word (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩) I,
        ⟨0⟩, toWord, ⟨861⟩, sel]
      (feeToStaticcallMem
        (balanceOfThisRebuiltStaticcallMem (UInt256.ofNat I.codeOwner.val) o o1)
        outFee)
      feeToStaticcallActiveWords outFee (cAFee, σFee) k C)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (ho132 : 32 ≤ o1.size) (ho1Size : o1.size < UInt256.size)
    (houtFeeSize : outFee.size < UInt256.size)
    (hzFeeTrue : zFee = true)
    (houtFee32 : 32 ≤ outFee.size)
    (hkLastEq : mintFeeKLastWord evmFeeS = mintFeeKLastSlotWord σFee I)
    (htotalSlot : uniswapSlotWord ⟨0⟩ σCleared I = totalSupply)
    (hreserve0Eq :
      uniswapReserve0Word
          (uniswapLockEnteredState
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)) =
        reserve0)
    (hruntimeReserve0 :
      reserve0Word (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩) I = reserve0)
    (hruntimeReserve1 :
      reserve1Word (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩) I = reserve1)
    (hamount0Eq :
      mintAmount0Word
          (uniswapLockEnteredState
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)) balance0 =
        amount0)
    (hamount1Eq :
      mintAmount1Word
          (uniswapLockEnteredState
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)) balance1 =
        amount1)
    (hfeeToZero :
      UInt256.land (UInt256.ofNat (fromByteArrayBigEndian (outFee.extract 0 32)))
          solcAddrMask =
        ⟨0⟩)
    (hkLastNonzero : mintFeeKLastSlotWord σFee I ≠ ⟨0⟩)
    (htotalNonzero : totalSupply ≠ ⟨0⟩)
    (hover :
      UInt256.size ≤ amount0.toNat * totalSupply.toNat ∨
        amount0.toNat * totalSupply.toNat < UInt256.size ∧
          reserve0 ≠ ⟨0⟩ ∧ UInt256.size ≤ amount1.toNat * totalSupply.toNat) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let evmS := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmL := uniswapLockEnteredState evmS
  let evmAfterFee := mintFeeKLastClearedState evmFeeS
  let nextFrame :=
    resumeAfterInternalCall
      { contract := contract, locals := mintAmountStore evmL I balance0 balance1 }
      "feeOn" (some [.bool false])
  let memFee :=
    feeToStaticcallMem
      (balanceOfThisRebuiltStaticcallMem (UInt256.ofNat I.codeOwner.val) o o1)
      outFee
  have hmem : memFee.size = 164 := by
    dsimp [memFee]
    exact feeToStaticcallMem_size_of_size_ge
      (UInt256.ofNat I.codeOwner.val) o o1 outFee ho32 hoSize ho132 ho1Size houtFee32
      houtFeeSize
  have hmem64 : memFee.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
    dsimp [memFee]
    exact feeToStaticcallMem_read64_of_size_ge
      (UInt256.ofNat I.codeOwner.val) o o1 outFee ho32 hoSize ho132 ho1Size houtFee32
      houtFeeSize
  have hfeeToAddr : feeTo = AccountAddress.ofNat 0 := by
    rw [hfeeToEq]
    exact accountAddress_ofNat_eq_zero_of_land_solcAddrMask_eq_zero
      (fromByteArrayBigEndian_extract0_32_lt houtFee32) hfeeToZero
  have hkLastSource : (mintFeeKLastWord evmFeeS).toNat ≠ 0 := by
    intro hzero
    apply hkLastNonzero
    rw [← hkLastEq]
    exact uint256_toNat_eq_zero hzero
  have hPostCleared : accountMapEquiv σCleared evmAfterFee.accountMap := by
    have hstore := accountMapEquiv_sstoreAccountMap I.codeOwner ⟨11⟩ ⟨0⟩
      hPostAccountsFee
    simpa [← hcleared, evmAfterFee, mintFeeKLastClearedState, henvFeeI,
      storageStore_accountMap] using hstore
  have henvCleared : evmAfterFee.executionEnv = I := by
    simp [evmAfterFee, mintFeeKLastClearedState, henvFeeI, storageStore_executionEnv]
  have htotalEq :
      mintFunctionTotalSupplyWord evmAfterFee = totalSupply := by
    have hword := mintFunctionTotalSupplyWord_eq_slot_of_accountMapEquiv
      hPostCleared henvCleared
    simpa [htotalSlot] using hword
  obtain ⟨_, _, rd3701⟩ :=
    uniswapMintFeeRuntimeFactoryResultFeeOffKLastNonzeroReturn
      rd7781 ho32 hoSize ho132 ho1Size houtFeeSize hzFeeTrue houtFee32 hfeeToZero hperm
      hkLastNonzero
  have hfee :
      ExecStmt config
        { contract := contract, locals := mintAmountStore evmL I balance0 balance1 }
        evm1S (.internalCall "_mintFee" [.var "_reserve0", .var "_reserve1"] "feeOn")
        (.ok { contract := contract, locals := nextFrame.locals } evmAfterFee) := by
    simpa [nextFrame, evmL, evmS, evmAfterFee, resumeAfterInternalCall] using
      uniswapMintFeeCallFromMint_feeOff_kLastNonzero evmL evm1S evmFeeS I balance0
        balance1 feeTo (by simpa [evmL, evmS] using hfeeGuard) hfeeCall hfeeDec
        hfeeToAddr hkLastSource
  have hbase : nextFrame.locals.get? "totalSupply" = none := by
    simpa [nextFrame, evmL, evmS] using
      mintAfterMintFeeCallStore_totalSupply evmL I balance0 balance1 false
  have hamount0Get : nextFrame.locals.get? "amount0" = some (uniswapUint256Value amount0) := by
    simpa [nextFrame, evmL, evmS, mintAmount0Value, hamount0Eq] using
      mintAfterMintFeeCallStore_amount0 evmL I balance0 balance1 false
  have hclean0 : UInt256.land reserve0 reserve112Mask = reserve0 :=
    reserve112Mask_clean_of_lt _ (by
      rw [← hruntimeReserve0]
      dsimp [reserve0Word]
      exact reserve112Word_lt _)
  rcases hover with hover0 | hover1
  · exact uniswapMintProportionalProduct0OverflowAfterMintFeeCase
      (σFee := σCleared) (evmFeeS := evmAfterFee) nextFrame.locals
      hcode hdispatch hsz36 hwv hunlockedSolm hguard0 hguard1 hcall0 hdec0 hcall1 hdec1
      hle0Source hle1Source hfee (by
        simpa [memFee, hcleared, hruntimeReserve0, hruntimeReserve1] using rd3701)
      hbase hamount0Get htotalEq htotalSlot htotalNonzero hclean0 hover0 hmem hmem64
  · rcases hover1 with ⟨hfit0, hreserve0Nonzero, hover1⟩
    have hamount1Get :
        nextFrame.locals.get? "amount1" = some (uniswapUint256Value amount1) := by
      simpa [nextFrame, evmL, evmS, mintAmount1Value, hamount1Eq] using
        mintAfterMintFeeCallStore_amount1 evmL I balance0 balance1 false
    have hreserve0Get :
        nextFrame.locals.get? "_reserve0" = some (.int (Int.ofNat reserve0.toNat)) := by
      simpa [nextFrame, evmL, evmS, hreserve0Eq] using
        mintAfterMintFeeCallStore_reserve0 evmL I balance0 balance1 false
    have hclean1 : UInt256.land reserve1 reserve112Mask = reserve1 :=
      reserve112Mask_clean_of_lt _ (by
        rw [← hruntimeReserve1]
        dsimp [reserve1Word]
        exact reserve112Word_lt _)
    exact uniswapMintProportionalProduct1OverflowAfterMintFeeCase
      (σFee := σCleared) (evmFeeS := evmAfterFee) nextFrame.locals
      hcode hdispatch hsz36 hwv hunlockedSolm hguard0 hguard1 hcall0 hdec0 hcall1 hdec1
      hle0Source hle1Source hfee (by
        simpa [memFee, hcleared, hruntimeReserve0, hruntimeReserve1] using rd3701)
      hbase hamount0Get hamount1Get hreserve0Get htotalEq htotalSlot htotalNonzero hclean0
      hclean1 hfit0 hreserve0Nonzero hover1 hmem hmem64

set_option maxHeartbeats 1000000 in
theorem uniswapMintProportionalProductOverflowFromFactoryCases
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {cAFee : Batteries.RBSet AccountAddress compare} {σFee σCleared σ'' : AccountMap}
    {evm0S evm1S evmFeeS : EVM.State}
    {out0 out1 outFee o o1 : ByteArray} {k C : ℕ}
    {totalSupply totalSupplyCleared amount0 amount1 balance0 balance1 reserve0 reserve1
      toWord sel feeToWord : UInt256}
    {zFee : Bool}
    (feeTo : AccountAddress)
    (hcode : I.code = uniswapV2PairBytecode)
    (hdispatch : dispatchMsg contract I.calldata = some mintTransition)
    (hsz36 : 36 ≤ I.calldata.size)
    (hperm : I.perm = true)
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
    (hle0Source :
      (uniswapReserve0Word
        (uniswapLockEnteredState
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I))).toNat ≤
          balance0.toNat)
    (hle1Source :
      (uniswapReserve1Word
        (uniswapLockEnteredState
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I))).toNat ≤
          balance1.toNat)
    (hfeeGuard :
      evalExpr? config
        (mintFeeCallFrame
          (uniswapReserve0Word
            (uniswapLockEnteredState
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)))
          (uniswapReserve1Word
            (uniswapLockEnteredState
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I))))
        evm1S (.binary .gt (.extCodeSize (.storage factoryRef)) (.intLit 0)) =
          .ok (.bool true))
    (hfeeCall : typedCallViaEVM config evm1S
      (EVM.address (uniswapAddressAtSlot evm1S ⟨5⟩)) "feeTo" 0 []
      (true, evmFeeS, outFee) false)
    (hfeeDec : config.externalABI.decode? "feeTo" outFee = some [.address feeTo])
    (hfeeToEq : feeTo = AccountAddress.ofNat (fromByteArrayBigEndian (outFee.extract 0 32)))
    (hPostAccountsFee : accountMapEquiv σFee evmFeeS.accountMap)
    (henvFeeI : evmFeeS.executionEnv = I)
    (hcleared : sstoreAccountMap I.codeOwner σFee ⟨11⟩ ⟨0⟩ = σCleared)
    (rd7781 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨7781⟩
      [(if zFee then (⟨1⟩ : UInt256) else ⟨0⟩), ⟨132⟩,
        feeToSelectorWord, mintFeeFactoryWord σ'' I, ⟨0⟩, ⟨0⟩,
        reserve1Word (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩) I,
        reserve0Word (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩) I,
        ⟨3701⟩, ⟨0⟩, amount1, amount0, balance1, balance0,
        reserve1Word (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩) I,
        reserve0Word (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩) I,
        ⟨0⟩, toWord, ⟨861⟩, sel]
      (feeToStaticcallMem
        (balanceOfThisRebuiltStaticcallMem (UInt256.ofNat I.codeOwner.val) o o1)
        outFee)
      feeToStaticcallActiveWords outFee (cAFee, σFee) k C)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (ho132 : 32 ≤ o1.size) (ho1Size : o1.size < UInt256.size)
    (houtFeeSize : outFee.size < UInt256.size)
    (hzFeeTrue : zFee = true)
    (houtFee32 : 32 ≤ outFee.size)
    (hkLastEq : mintFeeKLastWord evmFeeS = mintFeeKLastSlotWord σFee I)
    (htotalEq : mintFunctionTotalSupplyWord evmFeeS = totalSupply)
    (htotalSlot : uniswapSlotWord ⟨0⟩ σFee I = totalSupply)
    (htotalClearedSlot : uniswapSlotWord ⟨0⟩ σCleared I = totalSupplyCleared)
    (hreserve0Eq :
      uniswapReserve0Word
          (uniswapLockEnteredState
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)) =
        reserve0)
    (hreserve1Eq :
      uniswapReserve1Word
          (uniswapLockEnteredState
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)) =
        reserve1)
    (hruntimeReserve0 :
      reserve0Word (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩) I = reserve0)
    (hruntimeReserve1 :
      reserve1Word (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩) I = reserve1)
    (hamount0Eq :
      mintAmount0Word
          (uniswapLockEnteredState
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)) balance0 =
        amount0)
    (hamount1Eq :
      mintAmount1Word
          (uniswapLockEnteredState
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)) balance1 =
        amount1)
    (hfeeToWord :
      feeToWord = UInt256.ofNat (fromByteArrayBigEndian (outFee.extract 0 32)))
    (hcase :
      mintProportionalProductOverflowCase feeToWord totalSupply totalSupplyCleared amount0
        amount1 reserve0 reserve1 σFee I) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  rcases hcase with hfeeOff | hrest
  · rcases hfeeOff with ⟨hfeeToZero, hkLastZero, htotalNonzero, hover⟩
    exact uniswapMintProportionalFeeOffKLastZeroProductOverflowFromFactoryCase feeTo
      hcode hdispatch hsz36 hwv hunlockedSolm hguard0 hguard1 hcall0 hdec0 hcall1 hdec1
      hle0Source hle1Source hfeeGuard hfeeCall hfeeDec hfeeToEq rd7781 ho32 hoSize
      ho132 ho1Size houtFeeSize hzFeeTrue houtFee32 hkLastEq htotalEq htotalSlot
      hreserve0Eq hreserve1Eq hruntimeReserve0 hruntimeReserve1 hamount0Eq hamount1Eq
      (by simpa [hfeeToWord] using hfeeToZero) hkLastZero htotalNonzero hover
  · rcases hrest with hfeeOn | hfeeOffCleared
    · rcases hfeeOn with ⟨hfeeToNonzero, hkLastZero, htotalNonzero, hover⟩
      exact uniswapMintProportionalFeeOnKLastZeroProductOverflowFromFactoryCase feeTo
        hcode hdispatch hsz36 hwv hunlockedSolm hguard0 hguard1 hcall0 hdec0 hcall1
        hdec1 hle0Source hle1Source hfeeGuard hfeeCall hfeeDec hfeeToEq rd7781 ho32
        hoSize ho132 ho1Size houtFeeSize hzFeeTrue houtFee32 hkLastEq htotalEq
        htotalSlot hreserve0Eq hruntimeReserve0 hruntimeReserve1 hamount0Eq hamount1Eq
        (by simpa [hfeeToWord] using hfeeToNonzero) hkLastZero htotalNonzero hover
    · rcases hfeeOffCleared with ⟨hfeeToZero, hkLastNonzero, htotalNonzero, hover⟩
      exact uniswapMintProportionalFeeOffKLastNonzeroProductOverflowFromFactoryCase feeTo
        hcode hdispatch hsz36 hperm hwv hunlockedSolm hguard0 hguard1 hcall0 hdec0
        hcall1 hdec1 hle0Source hle1Source hfeeGuard hfeeCall hfeeDec hfeeToEq
        hPostAccountsFee henvFeeI hcleared rd7781 ho32 hoSize ho132 ho1Size houtFeeSize
        hzFeeTrue houtFee32 hkLastEq htotalClearedSlot hreserve0Eq hruntimeReserve0
        hruntimeReserve1 hamount0Eq hamount1Eq (by simpa [hfeeToWord] using hfeeToZero)
        hkLastNonzero htotalNonzero hover

end UniswapV2Pair
