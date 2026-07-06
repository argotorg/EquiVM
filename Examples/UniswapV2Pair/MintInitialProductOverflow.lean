import Examples.UniswapV2Pair.MintInitialFactoryOverflowCases

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000

namespace UniswapV2Pair

def uniswapSafeMathMulOverflowStringWord : UInt256 :=
  UInt256.shiftLeft
    (⟨573467620053399432674451404801797420674347462519⟩ : UInt256) ⟨96⟩

theorem uint256_mul_div_eq_zero_of_overflow {a b : UInt256}
    (hover : UInt256.size ≤ a.toNat * b.toNat) :
    UInt256.eq (UInt256.div (UInt256.mul a b) b) a = ⟨0⟩ := by
  have hbNat : b.toNat ≠ 0 := by
    intro hb
    have hprod : a.toNat * b.toNat = 0 := by simp [hb]
    have hpos : 0 < UInt256.size := by norm_num [UInt256.size]
    omega
  apply u256_eq_of_ne
  intro heq
  have hnat := congrArg UInt256.toNat heq
  have hdivNat : (UInt256.div (UInt256.mul a b) b).toNat =
      ((a.toNat * b.toNat) % UInt256.size) / b.toNat := by
    unfold UInt256.div UInt256.toNat
    simp only
    change (UInt256.mul a b).toNat / b.toNat =
      (a.toNat * b.toNat) % UInt256.size / b.toNat
    rw [u256_mul_toNat]
  have hdivEq : ((a.toNat * b.toNat) % UInt256.size) / b.toNat = a.toNat := by
    simpa [hdivNat] using hnat
  have hle : a.toNat * b.toNat ≤ (a.toNat * b.toNat) % UInt256.size := by
    calc
      a.toNat * b.toNat =
          (((a.toNat * b.toNat) % UInt256.size) / b.toNat) * b.toNat := by
        rw [hdivEq]
      _ ≤ (a.toNat * b.toNat) % UInt256.size := Nat.div_mul_le_self _ _
  have hmodLt : (a.toNat * b.toNat) % UInt256.size < a.toNat * b.toNat := by
    exact lt_of_lt_of_le (Nat.mod_lt _ (by norm_num [UInt256.size])) hover
  omega

theorem evalExpr_mint_amountProduct_overflow
    {locals : Store} (evm : EVM.State) (amount0 amount1 : UInt256)
    (hamount0 : locals.get? "amount0" = some (uniswapUint256Value amount0))
    (hamount1 : locals.get? "amount1" = some (uniswapUint256Value amount1))
    (hover : UInt256.size ≤ amount0.toNat * amount1.toNat) :
    evalExpr? config { contract := contract, locals := locals } evm
      (u256 (.binary .mul (.var "amount0") (.var "amount1"))) = .revert := by
  have hge : Int.ofNat (amount0.toNat * amount1.toNat) ≥ (2 : Int) ^ 256 := by
    rw [UInt256.size] at hover
    exact Int.ofNat_le.mpr hover
  simp only [u256, evalExpr?, EvalResult.ofOption, hamount0, hamount1, EvalResult.bind,
    bind, pure]
  simp only [evalBinaryOp?, uint256Int]
  rw [if_pos]
  simp only [Bool.or_eq_true, decide_eq_true_eq]
  exact Or.inr (by simpa [Nat.cast_mul] using hge)

theorem evalExprs_mint_initialSqrtArg_overflow
    {locals : Store} (evm : EVM.State) (amount0 amount1 : UInt256)
    (hamount0 : locals.get? "amount0" = some (uniswapUint256Value amount0))
    (hamount1 : locals.get? "amount1" = some (uniswapUint256Value amount1))
    (hover : UInt256.size ≤ amount0.toNat * amount1.toNat) :
    evalExprs? config { contract := contract, locals := locals } evm
      [u256 (.binary .mul (.var "amount0") (.var "amount1"))] = .revert := by
  simp only [evalExprs?, evalExpr_mint_amountProduct_overflow evm amount0 amount1
    hamount0 hamount1 hover, EvalResult.bind, bind]

theorem uniswapMintInitialLiquidityBranchStmtProductOverflowReverts
    {locals : Store} (evm : EVM.State) (amount0 amount1 : UInt256)
    (htotal : locals.get? "_totalSupply" = some (uniswapUint256Value (⟨0⟩ : UInt256)))
    (hamount0 : locals.get? "amount0" = some (uniswapUint256Value amount0))
    (hamount1 : locals.get? "amount1" = some (uniswapUint256Value amount1))
    (hover : UInt256.size ≤ amount0.toNat * amount1.toNat) :
    ExecStmt config { contract := contract, locals := locals } evm mintLiquidityBranchStmt
      .reverted := by
  let caller : Frame := { contract := contract, locals := locals }
  have hcond := evalExpr_mint_totalSupply_eq_zero_true evm htotal
  have hargs :
      evalExprs? config caller evm
        [u256 (.binary .mul (.var "amount0") (.var "amount1"))] = .revert := by
    simpa [caller] using
      evalExprs_mint_initialSqrtArg_overflow evm amount0 amount1 hamount0 hamount1
        hover
  have hsqrt :
      ExecStmt config caller evm
        (.internalCall "sqrt" [u256 (.binary .mul (.var "amount0") (.var "amount1"))]
          "rootLiquidity") .reverted :=
    ExecStmt.internalCallArgsRevert hargs
  refine ExecStmt.iteTrue hcond ?_
  change ExecBlock config caller evm mintInitialLiquidityBranchStmts .reverted
  exact ExecBlock.consRevert hsqrt

set_option maxHeartbeats 1000000 in
theorem RD.uniswapSafeMathMulOverflow_feeToStaticcall_size164
    {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {a b ret : UInt256} {R : List UInt256} {mem : ByteArray}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD uniswapV2PairBytecode ee g s0 ⟨6780⟩ (b :: a :: ret :: R)
      mem feeToStaticcallActiveWords rdata acc k C)
    (hover : UInt256.size ≤ a.toNat * b.toNat)
    (hmem : mem.size = 164)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hov : R.length + 9 ≤ 1024) :
    RDrev uniswapV2PairBytecode g s0 := by
  have hb : b ≠ ⟨0⟩ := by
    intro hb
    subst b
    have hle0 : UInt256.size ≤ 0 := by simpa using hover
    norm_num [UInt256.size] at hle0
  have heq : UInt256.eq (UInt256.div (UInt256.mul a b) b) a = ⟨0⟩ :=
    uint256_mul_div_eq_zero_of_overflow hover
  have rd6804pre := evm_run h with [jumpdest, push1 ⟨0⟩, dup2, iszero, dup1,
    push2 ⟨6807⟩]
  rw [isZero_eq_zero_of_ne hb] at rd6804pre
  have rd6804 := evm_run rd6804pre with [
    jumpiNT (by native_decide), pop, pop, dup1, dup3, mul, dup3, dup3, dup3,
    dup2, push2 ⟨6804⟩, jumpiT hb (by jump_dest)]
  have rd6807 := evm_run rd6804 with [jumpdest, div, eq]
  rw [heq] at rd6807
  have rdTail := evm_run rd6807 with [jumpdest, push2 ⟨2911⟩,
    jumpiNT (by native_decide)]
  exact RD.solcErrorStringRevertTail_feeToStaticcall_size164
    (code := uniswapV2PairBytecode) (pc := ⟨6812⟩) (len := ⟨20⟩)
    (rawWord := (⟨573467620053399432674451404801797420674347462519⟩ : UInt256))
    (shift := ⟨96⟩) (word := uniswapSafeMathMulOverflowStringWord)
    (op := .PUSH20) (width := 20) rdTail
    (by
      unfold solcErrorStringRevertTailWf
      repeat' first | apply And.intro | native_decide)
    (by decide) (by rfl) hmem hread64 (by simp only [List.length_cons]; omega)

set_option maxHeartbeats 1000000 in
theorem uniswapMintRuntimeInitialLiquidityProductOverflowReverts
    {cA gh bl σ σ₀ A I} {g : UInt256}
    {cAFee : Batteries.RBSet AccountAddress compare} {σFee : AccountMap}
    {mem rdata : ByteArray} {k C : ℕ}
    {feeOn amount0 amount1 balance0 balance1 reserve0 reserve1 toWord sel : UInt256}
    (rd3713 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨3713⟩
      [⟨0⟩, feeOn, amount1, amount0, balance1, balance0, reserve1, reserve0, ⟨0⟩,
        toWord, ⟨861⟩, sel]
      mem feeToStaticcallActiveWords rdata (cAFee, σFee) k C)
    (hover : UInt256.size ≤ amount0.toNat * amount1.toNat)
    (hmem : mem.size = 164)
    (hmem64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    RDrev uniswapV2PairBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) := by
  have rd6780pre := evm_run rd3713 with [
    push2 ⟨3742⟩, push2 ⟨1000⟩, push2 ⟨2531⟩, push2 ⟨3737⟩, dup8,
    dup8, push4 ⟨0xffffffff⟩, push2 ⟨6780⟩, and]
  rw [show UInt256.land (⟨6780⟩ : UInt256) ⟨0xffffffff⟩ = ⟨6780⟩ from by decide]
    at rd6780pre
  have rd6780 := rd6780pre.jump (by native_decide) (by jump_dest) (by evm_ov)
  exact RD.uniswapSafeMathMulOverflow_feeToStaticcall_size164
    (a := amount0) (b := amount1) (ret := ⟨3737⟩)
    (R := [⟨2531⟩, ⟨1000⟩, ⟨3742⟩, ⟨0⟩, feeOn, amount1, amount0, balance1,
      balance0, reserve1, reserve0, ⟨0⟩, toWord, ⟨861⟩, sel])
    rd6780 hover hmem hmem64 (by simp only [List.length_cons, List.length_nil]; omega)

set_option maxHeartbeats 1000000 in
theorem uniswapMintInitialProductOverflowFromAfterFeeCase
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {cAFee : Batteries.RBSet AccountAddress compare} {σFee : AccountMap}
    {evm0S evm1S evmAfter : EVM.State}
    {out0 out1 mem rdata : ByteArray} {k C : ℕ}
    {feeOn amount0 amount1 balance0 balance1 reserve0 reserve1 toWord sel : UInt256}
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
      config.externalABI.decode? "balanceOf" out0 = some (uniswapUint256Value balance0))
    (hcall1 : typedCallViaEVM config evm0S
      (EVM.address (uniswapAddressAtSlot evm0S ⟨7⟩)) "balanceOf" 0
      [.address evm0S.executionEnv.codeOwner] (true, evm1S, out1) false)
    (hdec1 :
      config.externalABI.decode? "balanceOf" out1 = some (uniswapUint256Value balance1))
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
    (hamount0Get : nextLocals.get? "amount0" = some (uniswapUint256Value amount0))
    (hamount1Get : nextLocals.get? "amount1" = some (uniswapUint256Value amount1))
    (htotalSource : mintFunctionTotalSupplyWord evmAfter = ⟨0⟩)
    (htotalRuntimeZero : uniswapSlotWord ⟨0⟩ σFee I = ⟨0⟩)
    (hover : UInt256.size ≤ amount0.toNat * amount1.toNat)
    (rd3701 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨3701⟩
      [feeOn, ⟨0⟩, amount1, amount0, balance1, balance0, reserve1, reserve0, ⟨0⟩,
        toWord, ⟨861⟩, sel]
      mem feeToStaticcallActiveWords rdata (cAFee, σFee) k C)
    (hmem : mem.size = 164)
    (hmem64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let afterTotalSupplyLocals :=
    nextLocals.insert "_totalSupply" (uniswapUint256Value (mintFunctionTotalSupplyWord evmAfter))
  have hamount0After :
      afterTotalSupplyLocals.get? "amount0" = some (uniswapUint256Value amount0) := by
    dsimp [afterTotalSupplyLocals]
    change (Std.HashMap.insert nextLocals "_totalSupply"
        (uniswapUint256Value (mintFunctionTotalSupplyWord evmAfter))).get? "amount0" =
      some (uniswapUint256Value amount0)
    rw [store_get_ne nextLocals (k := "_totalSupply") (a := "amount0")
      (uniswapUint256Value (mintFunctionTotalSupplyWord evmAfter)) (by decide)]
    exact hamount0Get
  have hamount1After :
      afterTotalSupplyLocals.get? "amount1" = some (uniswapUint256Value amount1) := by
    dsimp [afterTotalSupplyLocals]
    change (Std.HashMap.insert nextLocals "_totalSupply"
        (uniswapUint256Value (mintFunctionTotalSupplyWord evmAfter))).get? "amount1" =
      some (uniswapUint256Value amount1)
    rw [store_get_ne nextLocals (k := "_totalSupply") (a := "amount1")
      (uniswapUint256Value (mintFunctionTotalSupplyWord evmAfter)) (by decide)]
    exact hamount1Get
  have htotalAfter :
      afterTotalSupplyLocals.get? "_totalSupply" =
        some (uniswapUint256Value (⟨0⟩ : UInt256)) := by
    dsimp [afterTotalSupplyLocals]
    change (Std.HashMap.insert nextLocals "_totalSupply"
        (uniswapUint256Value (mintFunctionTotalSupplyWord evmAfter))).get? "_totalSupply" =
      some (uniswapUint256Value (⟨0⟩ : UInt256))
    rw [store_get_self]
    rw [htotalSource]
  have hbranch :
      ExecStmt config { contract := contract, locals := afterTotalSupplyLocals } evmAfter
        mintLiquidityBranchStmt .reverted :=
    uniswapMintInitialLiquidityBranchStmtProductOverflowReverts evmAfter amount0 amount1
      htotalAfter hamount0After hamount1After hover
  have hbody :
      ExecTransitionBody config contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) (mintStore I)
        mintTransition.body .reverted :=
    uniswapMintAfterMintFeeInitialBranchStmtReverts_of_call nextLocals hwv hunlockedSolm
      hguard0 hguard1 hcall0 hdec0 hcall1 hdec1 henough0 henough1 hfee hbase
      (by simpa [afterTotalSupplyLocals] using hbranch)
  obtain ⟨_, _, rd3713⟩ :=
    uniswapMintRuntimeAfterMintFeeTotalSupplyZero rd3701 htotalRuntimeZero
  have rdRev :
      RDrev uniswapV2PairBytecode (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) :=
    uniswapMintRuntimeInitialLiquidityProductOverflowReverts rd3713 hover hmem hmem64
  exact rdRev.reEquivExecutionRevert hcode hdispatch (uniswapDecode_mint_ok hsz36) hbody

set_option maxHeartbeats 1000000 in
theorem uniswapMintInitialFeeOffKLastZeroProductOverflowFromFactoryCase
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {cAFee : Batteries.RBSet AccountAddress compare} {σFee σ'' : AccountMap}
    {evm0S evm1S evmFeeS : EVM.State}
    {out0 out1 outFee o o1 : ByteArray} {k C : ℕ}
    {amount0 amount1 balance0 balance1 toWord sel : UInt256} {zFee : Bool}
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
      config.externalABI.decode? "balanceOf" out0 = some (uniswapUint256Value balance0))
    (hcall1 : typedCallViaEVM config evm0S
      (EVM.address (uniswapAddressAtSlot evm0S ⟨7⟩)) "balanceOf" 0
      [.address evm0S.executionEnv.codeOwner] (true, evm1S, out1) false)
    (hdec1 :
      config.externalABI.decode? "balanceOf" out1 = some (uniswapUint256Value balance1))
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
    (hfeeDec : config.externalABI.decode? "feeTo" outFee = some (.address feeTo))
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
    (htotalEq : mintFunctionTotalSupplyWord evmFeeS = uniswapSlotWord ⟨0⟩ σFee I)
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
    (htotalZero : uniswapSlotWord ⟨0⟩ σFee I = ⟨0⟩)
    (hover : UInt256.size ≤ amount0.toNat * amount1.toNat) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let evmS := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmL := uniswapLockEnteredState evmS
  let nextFrame :=
    resumeAfterInternalCall
      { contract := contract, locals := mintAmountStore evmL I balance0 balance1 }
      "feeOn" (some (.bool false))
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
  have htotalSource : mintFunctionTotalSupplyWord evmFeeS = ⟨0⟩ := by
    rw [htotalEq, htotalZero]
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
  have hamount1Get : nextFrame.locals.get? "amount1" = some (uniswapUint256Value amount1) := by
    simpa [nextFrame, evmL, evmS, mintAmount1Value, hamount1Eq] using
      mintAfterMintFeeCallStore_amount1 evmL I balance0 balance1 false
  exact uniswapMintInitialProductOverflowFromAfterFeeCase nextFrame.locals
    hcode hdispatch hsz36 hwv hunlockedSolm hguard0 hguard1 hcall0 hdec0 hcall1 hdec1
    hle0Source hle1Source hfee hbase hamount0Get hamount1Get htotalSource htotalZero
    hover (by simpa [memFee] using rd3701) hmem hmem64

set_option maxHeartbeats 1000000 in
theorem uniswapMintInitialFeeOnKLastZeroProductOverflowFromFactoryCase
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {cAFee : Batteries.RBSet AccountAddress compare} {σFee σ'' : AccountMap}
    {evm0S evm1S evmFeeS : EVM.State}
    {out0 out1 outFee o o1 : ByteArray} {k C : ℕ}
    {amount0 amount1 balance0 balance1 toWord sel : UInt256} {zFee : Bool}
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
      config.externalABI.decode? "balanceOf" out0 = some (uniswapUint256Value balance0))
    (hcall1 : typedCallViaEVM config evm0S
      (EVM.address (uniswapAddressAtSlot evm0S ⟨7⟩)) "balanceOf" 0
      [.address evm0S.executionEnv.codeOwner] (true, evm1S, out1) false)
    (hdec1 :
      config.externalABI.decode? "balanceOf" out1 = some (uniswapUint256Value balance1))
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
    (hfeeDec : config.externalABI.decode? "feeTo" outFee = some (.address feeTo))
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
    (htotalEq : mintFunctionTotalSupplyWord evmFeeS = uniswapSlotWord ⟨0⟩ σFee I)
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
    (htotalZero : uniswapSlotWord ⟨0⟩ σFee I = ⟨0⟩)
    (hover : UInt256.size ≤ amount0.toNat * amount1.toNat) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let evmS := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmL := uniswapLockEnteredState evmS
  let nextFrame :=
    resumeAfterInternalCall
      { contract := contract, locals := mintAmountStore evmL I balance0 balance1 }
      "feeOn" (some (.bool true))
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
  have htotalSource : mintFunctionTotalSupplyWord evmFeeS = ⟨0⟩ := by
    rw [htotalEq, htotalZero]
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
  have hamount1Get : nextFrame.locals.get? "amount1" = some (uniswapUint256Value amount1) := by
    simpa [nextFrame, evmL, evmS, mintAmount1Value, hamount1Eq] using
      mintAfterMintFeeCallStore_amount1 evmL I balance0 balance1 true
  exact uniswapMintInitialProductOverflowFromAfterFeeCase nextFrame.locals
    hcode hdispatch hsz36 hwv hunlockedSolm hguard0 hguard1 hcall0 hdec0 hcall1 hdec1
    hle0Source hle1Source hfee hbase hamount0Get hamount1Get htotalSource htotalZero
    hover (by simpa [memFee] using rd3701) hmem hmem64

set_option maxHeartbeats 1000000 in
theorem uniswapMintInitialFeeOffKLastNonzeroProductOverflowFromFactoryCase
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {cAFee : Batteries.RBSet AccountAddress compare} {σFee σ'' : AccountMap}
    {evm0S evm1S evmFeeS : EVM.State}
    {out0 out1 outFee o o1 : ByteArray} {k C : ℕ}
    {amount0 amount1 balance0 balance1 toWord sel : UInt256} {zFee : Bool}
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
      config.externalABI.decode? "balanceOf" out0 = some (uniswapUint256Value balance0))
    (hcall1 : typedCallViaEVM config evm0S
      (EVM.address (uniswapAddressAtSlot evm0S ⟨7⟩)) "balanceOf" 0
      [.address evm0S.executionEnv.codeOwner] (true, evm1S, out1) false)
    (hdec1 :
      config.externalABI.decode? "balanceOf" out1 = some (uniswapUint256Value balance1))
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
    (hfeeDec : config.externalABI.decode? "feeTo" outFee = some (.address feeTo))
    (hfeeToEq : feeTo = AccountAddress.ofNat (fromByteArrayBigEndian (outFee.extract 0 32)))
    (hPostAccountsFee : accountMapEquiv σFee evmFeeS.accountMap)
    (henvFeeI : evmFeeS.executionEnv = I)
    (hperm : I.perm = true)
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
    (htotalZero :
      uniswapSlotWord ⟨0⟩ (sstoreAccountMap I.codeOwner σFee ⟨11⟩ ⟨0⟩) I = ⟨0⟩)
    (hover : UInt256.size ≤ amount0.toNat * amount1.toNat) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let evmS := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmL := uniswapLockEnteredState evmS
  let σCleared := sstoreAccountMap I.codeOwner σFee ⟨11⟩ ⟨0⟩
  let evmAfterFee := mintFeeKLastClearedState evmFeeS
  let nextFrame :=
    resumeAfterInternalCall
      { contract := contract, locals := mintAmountStore evmL I balance0 balance1 }
      "feeOn" (some (.bool false))
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
    simpa [σCleared, evmAfterFee, mintFeeKLastClearedState, henvFeeI,
      storageStore_accountMap] using hstore
  have henvCleared : evmAfterFee.executionEnv = I := by
    simp [evmAfterFee, mintFeeKLastClearedState, henvFeeI, storageStore_executionEnv]
  have htotalEqCleared :
      mintFunctionTotalSupplyWord evmAfterFee = uniswapSlotWord ⟨0⟩ σCleared I := by
    simpa [σCleared] using
      mintFunctionTotalSupplyWord_eq_slot_of_accountMapEquiv hPostCleared henvCleared
  have htotalSource : mintFunctionTotalSupplyWord evmAfterFee = ⟨0⟩ := by
    rw [htotalEqCleared]
    exact htotalZero
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
  have hamount1Get : nextFrame.locals.get? "amount1" = some (uniswapUint256Value amount1) := by
    simpa [nextFrame, evmL, evmS, mintAmount1Value, hamount1Eq] using
      mintAfterMintFeeCallStore_amount1 evmL I balance0 balance1 false
  exact uniswapMintInitialProductOverflowFromAfterFeeCase
    (σFee := σCleared) (evmAfter := evmAfterFee) nextFrame.locals hcode hdispatch hsz36
    hwv hunlockedSolm hguard0 hguard1 hcall0 hdec0 hcall1 hdec1 hle0Source hle1Source
    hfee hbase hamount0Get hamount1Get htotalSource (by simpa [σCleared] using htotalZero)
    hover (by simpa [σCleared, memFee] using rd3701) hmem hmem64

set_option maxHeartbeats 1000000 in
theorem uniswapMintInitialProductOverflowFromFactoryCases
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {cAFee : Batteries.RBSet AccountAddress compare} {σFee σ'' : AccountMap}
    {evm0S evm1S evmFeeS : EVM.State}
    {out0 out1 outFee o o1 : ByteArray} {k C : ℕ}
    {amount0 amount1 balance0 balance1 toWord sel : UInt256} {zFee : Bool}
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
      config.externalABI.decode? "balanceOf" out0 = some (uniswapUint256Value balance0))
    (hcall1 : typedCallViaEVM config evm0S
      (EVM.address (uniswapAddressAtSlot evm0S ⟨7⟩)) "balanceOf" 0
      [.address evm0S.executionEnv.codeOwner] (true, evm1S, out1) false)
    (hdec1 :
      config.externalABI.decode? "balanceOf" out1 = some (uniswapUint256Value balance1))
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
    (hfeeDec : config.externalABI.decode? "feeTo" outFee = some (.address feeTo))
    (hfeeToEq : feeTo = AccountAddress.ofNat (fromByteArrayBigEndian (outFee.extract 0 32)))
    (hPostAccountsFee : accountMapEquiv σFee evmFeeS.accountMap)
    (henvFeeI : evmFeeS.executionEnv = I)
    (hperm : I.perm = true)
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
    (htotalEq : mintFunctionTotalSupplyWord evmFeeS = uniswapSlotWord ⟨0⟩ σFee I)
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
    (hcase :
      (UInt256.land (UInt256.ofNat (fromByteArrayBigEndian (outFee.extract 0 32)))
            solcAddrMask =
          ⟨0⟩ ∧
        mintFeeKLastSlotWord σFee I = ⟨0⟩ ∧
        uniswapSlotWord ⟨0⟩ σFee I = ⟨0⟩ ∧
        UInt256.size ≤ amount0.toNat * amount1.toNat) ∨
      (UInt256.land (UInt256.ofNat (fromByteArrayBigEndian (outFee.extract 0 32)))
            solcAddrMask ≠
          ⟨0⟩ ∧
        mintFeeKLastSlotWord σFee I = ⟨0⟩ ∧
        uniswapSlotWord ⟨0⟩ σFee I = ⟨0⟩ ∧
        UInt256.size ≤ amount0.toNat * amount1.toNat) ∨
      (UInt256.land (UInt256.ofNat (fromByteArrayBigEndian (outFee.extract 0 32)))
            solcAddrMask =
          ⟨0⟩ ∧
        mintFeeKLastSlotWord σFee I ≠ ⟨0⟩ ∧
        uniswapSlotWord ⟨0⟩ (sstoreAccountMap I.codeOwner σFee ⟨11⟩ ⟨0⟩) I =
          ⟨0⟩ ∧
        UInt256.size ≤ amount0.toNat * amount1.toNat)) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  rcases hcase with hfeeOff | hrest
  · rcases hfeeOff with ⟨hfeeToZero, hkLastZero, htotalZero, hover⟩
    exact uniswapMintInitialFeeOffKLastZeroProductOverflowFromFactoryCase feeTo
      hcode hdispatch hsz36 hwv hunlockedSolm hguard0 hguard1 hcall0 hdec0 hcall1 hdec1
      hle0Source hle1Source hfeeGuard hfeeCall hfeeDec hfeeToEq rd7781 ho32 hoSize
      ho132 ho1Size houtFeeSize hzFeeTrue houtFee32 hkLastEq htotalEq hamount0Eq
      hamount1Eq hfeeToZero hkLastZero htotalZero hover
  · rcases hrest with hfeeOn | hfeeOffCleared
    · rcases hfeeOn with ⟨hfeeToNonzero, hkLastZero, htotalZero, hover⟩
      exact uniswapMintInitialFeeOnKLastZeroProductOverflowFromFactoryCase feeTo
        hcode hdispatch hsz36 hwv hunlockedSolm hguard0 hguard1 hcall0 hdec0 hcall1 hdec1
        hle0Source hle1Source hfeeGuard hfeeCall hfeeDec hfeeToEq rd7781 ho32 hoSize
        ho132 ho1Size houtFeeSize hzFeeTrue houtFee32 hkLastEq htotalEq hamount0Eq
        hamount1Eq hfeeToNonzero hkLastZero htotalZero hover
    · rcases hfeeOffCleared with ⟨hfeeToZero, hkLastNonzero, htotalZero, hover⟩
      exact uniswapMintInitialFeeOffKLastNonzeroProductOverflowFromFactoryCase feeTo
        hcode hdispatch hsz36 hwv hunlockedSolm hguard0 hguard1 hcall0 hdec0 hcall1 hdec1
        hle0Source hle1Source hfeeGuard hfeeCall hfeeDec hfeeToEq hPostAccountsFee henvFeeI
        hperm rd7781 ho32 hoSize ho132 ho1Size houtFeeSize hzFeeTrue houtFee32 hkLastEq
        hamount0Eq hamount1Eq hfeeToZero hkLastNonzero htotalZero hover

end UniswapV2Pair
