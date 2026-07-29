import Examples.UniswapV2Pair.MintInternalMintRuntime

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace UniswapV2Pair

def mintSafeMathAddOverflowStringWord : UInt256 :=
  UInt256.shiftLeft
    (⟨573467620053399432670716995166075968196518375287⟩ : UInt256) ⟨96⟩

theorem evalExpr_mintFunction_totalSupply_add_revert
    (evm : EVM.State) (recipient : AccountAddress) (value : UInt256)
    (hover : UInt256.size ≤ mintFunctionTotalSupplyNewNat evm value) :
    evalExpr? config { contract := contract, locals := mintFunctionCallStore recipient value } evm
      (u256 (.binary .add (.storage totalSupplyRef) (.var "value"))) = .revert := by
  have hge : Int.ofNat (mintFunctionTotalSupplyNewNat evm value) ≥ (2 : Int) ^ 256 := by
    rw [UInt256.size] at hover
    exact Int.ofNat_le.mpr hover
  simp only [u256, evalExpr?, evalExpr_mintFunction_totalSupply evm recipient value,
    evalExpr_mintFunction_value evm recipient value, EvalResult.bind, bind, pure]
  simp [evalBinaryOp?, uint256Int]
  intro _
  simpa [mintFunctionTotalSupplyNewNat] using hge

theorem evalExpr_mintFunction_to_balance_add_revert
    (evm : EVM.State) (recipient : AccountAddress) (value : UInt256)
    (hover : UInt256.size ≤ mintFunctionToBalanceNewNat evm recipient value) :
    evalExpr? config { contract := contract, locals := mintFunctionCallStore recipient value }
      (mintFunctionAfterTotalSupplyState evm value)
      (u256 (.binary .add (.storage (balanceOfRef (.var "to"))) (.var "value"))) =
        .revert := by
  have hge : Int.ofNat (mintFunctionToBalanceNewNat evm recipient value) ≥ (2 : Int) ^ 256 := by
    rw [UInt256.size] at hover
    exact Int.ofNat_le.mpr hover
  simp only [u256, evalExpr?, evalExpr_mintFunction_to_balance evm recipient value,
    evalExpr_mintFunction_value (mintFunctionAfterTotalSupplyState evm value) recipient value,
    EvalResult.bind, bind, pure]
  simp [evalBinaryOp?, uint256Int]
  intro _
  simpa [mintFunctionToBalanceNewNat] using hge

theorem uniswapMintFunctionBodyReverts_totalSupplyOverflow
    (evm : EVM.State) (recipient : AccountAddress) (value : UInt256)
    (hover : UInt256.size ≤ mintFunctionTotalSupplyNewNat evm value) :
    ExecFuncBody config { contract := contract, locals := mintFunctionCallStore recipient value }
      evm mintFunction.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  change ExecBlock config { contract := contract, locals := mintFunctionCallStore recipient value }
    evm
    [ .assign .storage totalSupplyRef
        (u256 (.binary .add (.storage totalSupplyRef) (.var "value"))),
      .assign .storage (balanceOfRef (.var "to"))
        (u256 (.binary .add (.storage (balanceOfRef (.var "to"))) (.var "value"))) ]
    .reverted
  exact ExecBlock.consRevert
    (ExecStmt.assignExprRevert
      (evalExpr_mintFunction_totalSupply_add_revert evm recipient value hover))

theorem uniswapMintFunctionBodyReverts_balanceOverflow
    (evm : EVM.State) (recipient : AccountAddress) (value : UInt256)
    (hfitSupply : mintFunctionTotalSupplyNewNat evm value < UInt256.size)
    (hover : UInt256.size ≤ mintFunctionToBalanceNewNat evm recipient value) :
    ExecFuncBody config { contract := contract, locals := mintFunctionCallStore recipient value }
      evm mintFunction.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  change ExecBlock config { contract := contract, locals := mintFunctionCallStore recipient value }
    evm
    [ .assign .storage totalSupplyRef
        (u256 (.binary .add (.storage totalSupplyRef) (.var "value"))),
      .assign .storage (balanceOfRef (.var "to"))
        (u256 (.binary .add (.storage (balanceOfRef (.var "to"))) (.var "value"))) ]
    .reverted
  refine ExecBlock.consNormal
    (ExecStmt.assign
      (evalExpr_mintFunction_totalSupply_add evm recipient value hfitSupply)
      (mintFunctionAssignTotalSupply evm recipient value)) ?_
  exact ExecBlock.consRevert
    (ExecStmt.assignExprRevert
      (evalExpr_mintFunction_to_balance_add_revert evm recipient value hover))

theorem uniswapMintFunctionCallRevert_totalSupplyOverflow
    {caller : Frame} {evm : EVM.State}
    {recipient : AccountAddress} {value : UInt256} {args : List Expr} {retVar : Ident}
    (hcontract : caller.contract = contract)
    (hargs : evalExprs? config caller evm args =
      .ok [mintFunctionToValue recipient, mintFunctionValueValue value])
    (hover : UInt256.size ≤ mintFunctionTotalSupplyNewNat evm value) :
    ExecStmt config caller evm (.internalCall "_mint" args retVar) .reverted := by
  exact internalCallFunctionRevert
    (cfg := config) (caller := caller) (evm := evm)
    (name := "_mint") (retVar := retVar) (args := args)
    (argVals := [mintFunctionToValue recipient, mintFunctionValueValue value])
    (callee := mintFunction) (locals := mintFunctionCallStore recipient value)
    hargs (by simpa [hcontract] using uniswapLookupMintFunction)
    (bindParams_mintFunction_call recipient value)
    (by
      simpa [hcontract] using
        (uniswapMintFunctionBodyReverts_totalSupplyOverflow evm recipient value hover))

theorem uniswapMintFunctionCallRevert_balanceOverflow
    {caller : Frame} {evm : EVM.State}
    {recipient : AccountAddress} {value : UInt256} {args : List Expr} {retVar : Ident}
    (hcontract : caller.contract = contract)
    (hargs : evalExprs? config caller evm args =
      .ok [mintFunctionToValue recipient, mintFunctionValueValue value])
    (hfitSupply : mintFunctionTotalSupplyNewNat evm value < UInt256.size)
    (hover : UInt256.size ≤ mintFunctionToBalanceNewNat evm recipient value) :
    ExecStmt config caller evm (.internalCall "_mint" args retVar) .reverted := by
  exact internalCallFunctionRevert
    (cfg := config) (caller := caller) (evm := evm)
    (name := "_mint") (retVar := retVar) (args := args)
    (argVals := [mintFunctionToValue recipient, mintFunctionValueValue value])
    (callee := mintFunction) (locals := mintFunctionCallStore recipient value)
    hargs (by simpa [hcontract] using uniswapLookupMintFunction)
    (bindParams_mintFunction_call recipient value)
    (by
      simpa [hcontract] using
        (uniswapMintFunctionBodyReverts_balanceOverflow evm recipient value hfitSupply hover))

set_option maxHeartbeats 1000000 in
theorem RD.solcErrorStringRevertTail_feeToStaticcall_size164
    {code : ByteArray} {g : Sat256} {s0 : State} {ee : ExecutionEnv} {k C : ℕ}
    {pc len rawWord shift word : UInt256} {op : Operation.POp} {width : ℕ}
    {stk : List UInt256} {mem rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD code ee g s0 pc stk mem feeToStaticcallActiveWords rdata acc k C)
    (hwf : solcErrorStringRevertTailWf code pc len rawWord shift op width)
    (hpush : op ≠ .PUSH0)
    (hword : UInt256.shiftLeft rawWord shift = word)
    (hmem : mem.size = 164)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hov : stk.length + 5 ≤ 1024) :
    RDrev code g s0 := by
  rcases hwf with
    ⟨hd0, hd2, hd3, hd4, hd8, hd10, hd11, hd12, hd13, hd15, hd17, hd18,
      hd19, hd20, hd22, hd24, hd25, hd26, hd27, hdRawOut, hdShl, hd68,
      hdDup3, hdAdd, hdMstore3, hdSwap, hdMload, hdSwap2, hdDup2, hdSwap3,
      hdSub, hd100, hdAdd2, hdSwap4, hdRev⟩
  have hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨64⟩ : UInt256) ≥ feeToStaticcallActiveWords * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
        (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (aw := feeToStaticcallActiveWords)
      (by rw [hmem]; decide) (by native_decide) hread64
  have rdMload := evm_run h with [
    raw push1 ⟨64⟩ hd0 (by evm_ov),
    raw dup1 hd2 (by evm_ov),
    raw mload 0 ⟨128⟩ feeToStaticcallActiveWords hd3
      mem_cost hmload64 (by native_decide) (by evm_ov)]
  have rdSelectorRaw := rdMload.pushConst (⟨4594637⟩ : UInt256)
    (width := 3) (op := .PUSH3) (by decide) hd4 (by simp only [List.length_cons]; omega)
  have rdPrefix := evm_run rdSelectorRaw with [
    raw push1 ⟨229⟩ hd8 (by evm_ov),
    raw shl hd10 (by evm_ov),
    raw dup2 hd11 (by evm_ov),
    raw mstore 0 (solcErrorStringMem0 mem) feeToStaticcallActiveWords
      hd12 mem_cost (by rfl) (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ hd13 (by evm_ov),
    raw push1 ⟨4⟩ hd15 (by evm_ov),
    raw dup3 hd17 (by evm_ov),
    raw add hd18 (by evm_ov),
    raw mstore 0 (solcErrorStringMem1 mem) feeToStaticcallActiveWords
      hd19 mem_cost (by rfl) (by native_decide) (by evm_ov),
    raw push1 len hd20 (by evm_ov),
    raw push1 ⟨36⟩ hd22 (by evm_ov),
    raw dup3 hd24 (by evm_ov),
    raw add hd25 (by evm_ov),
    raw mstore 3 (solcErrorStringMem2 len mem)
      (UInt256.ofNat 7) hd26 mem_cost (by rfl) (by native_decide) (by evm_ov)]
  have rdRaw := rdPrefix.pushConst rawWord (width := width) (op := op)
    hpush hd27 (by simp only [List.length_cons]; omega)
  have rdWord := evm_run rdRaw with [
    raw push1 shift hdRawOut (by evm_ov),
    raw shl hdShl (by evm_ov)]
  rw [hword] at rdWord
  exact evm_run rdWord with [
    raw push1 ⟨68⟩ hd68 (by evm_ov),
    raw dup3 hdDup3 (by evm_ov),
    raw add hdAdd (by evm_ov),
    raw mstore 3 (solcErrorStringMem3 len word mem)
      (UInt256.ofNat 8) hdMstore3 mem_cost (by rfl) (by native_decide) (by evm_ov),
    raw swap1 hdSwap (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 8) hdMload
      mem_cost
      (solcErrorStringMem3_mload64_of_size164 len word hmem hread64)
      (by native_decide) (by evm_ov),
    raw swap1 hdSwap2 (by evm_ov),
    raw dup2 hdDup2 (by evm_ov),
    raw swap1 hdSwap3 (by evm_ov),
    raw sub hdSub (by evm_ov),
    raw push1 ⟨100⟩ hd100 (by evm_ov),
    raw add hdAdd2 (by evm_ov),
    raw swap1 hdSwap4 (by evm_ov),
    raw rev 0 hdRev mem_cost (by evm_ov)]

set_option maxHeartbeats 1000000 in
-- GENERALIZES Reasoning.Reach.RD.solcErrorStringRevertTail — parameterize the initial
-- memory size/read preservation instead of fixing it to 96 bytes.
theorem RD.solcErrorStringRevertTail_size164 {code : ByteArray} {g : Sat256}
    {s0 : State} {ee : ExecutionEnv} {k C : ℕ}
    {pc len rawWord shift word : UInt256} {op : Operation.POp} {width : ℕ}
    {stk : List UInt256} {mem rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD code ee g s0 pc stk mem (UInt256.ofNat 3) rdata acc k C)
    (hwf : solcErrorStringRevertTailWf code pc len rawWord shift op width)
    (hpush : op ≠ .PUSH0)
    (hword : UInt256.shiftLeft rawWord shift = word)
    (hmem : mem.size = 164)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hov : stk.length + 5 ≤ 1024) :
    RDrev code g s0 := by
  rcases hwf with
    ⟨hd0, hd2, hd3, hd4, hd8, hd10, hd11, hd12, hd13, hd15, hd17, hd18,
      hd19, hd20, hd22, hd24, hd25, hd26, hd27, hdRawOut, hdShl, hd68,
      hdDup3, hdAdd, hdMstore3, hdSwap, hdMload, hdSwap2, hdDup2, hdSwap3,
      hdSub, hd100, hdAdd2, hdSwap4, hdRev⟩
  have rdMload := evm_run h with [
    raw push1 ⟨64⟩ hd0 (by evm_ov),
    raw dup1 hd2 (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) hd3
      mem_cost
      (mloadFreePtrValue (by rw [hmem]; decide) (by decide) hread64)
      (by decide) (by evm_ov)]
  have rdSelectorRaw := rdMload.pushConst (⟨4594637⟩ : UInt256)
    (width := 3) (op := .PUSH3) (by decide) hd4 (by simp only [List.length_cons]; omega)
  have rdPrefix := evm_run rdSelectorRaw with [
    raw push1 ⟨229⟩ hd8 (by evm_ov),
    raw shl hd10 (by evm_ov),
    raw dup2 hd11 (by evm_ov),
    raw mstore 6 (solcErrorStringMem0 mem) (UInt256.ofNat 5)
      hd12 mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨32⟩ hd13 (by evm_ov),
    raw push1 ⟨4⟩ hd15 (by evm_ov),
    raw dup3 hd17 (by evm_ov),
    raw add hd18 (by evm_ov),
    raw mstore 3 (solcErrorStringMem1 mem) (UInt256.ofNat 6)
      hd19 mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 len hd20 (by evm_ov),
    raw push1 ⟨36⟩ hd22 (by evm_ov),
    raw dup3 hd24 (by evm_ov),
    raw add hd25 (by evm_ov),
    raw mstore 3 (solcErrorStringMem2 len mem)
      (UInt256.ofNat 7) hd26 mem_cost (by rfl) (by decide) (by evm_ov)]
  have rdRaw := rdPrefix.pushConst rawWord (width := width) (op := op)
    hpush hd27 (by simp only [List.length_cons]; omega)
  have rdWord := evm_run rdRaw with [
    raw push1 shift hdRawOut (by evm_ov),
    raw shl hdShl (by evm_ov)]
  rw [hword] at rdWord
  exact evm_run rdWord with [
    raw push1 ⟨68⟩ hd68 (by evm_ov),
    raw dup3 hdDup3 (by evm_ov),
    raw add hdAdd (by evm_ov),
    raw mstore 3 (solcErrorStringMem3 len word mem)
      (UInt256.ofNat 8) hdMstore3 mem_cost (by rfl) (by decide) (by evm_ov),
    raw swap1 hdSwap (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 8) hdMload
      mem_cost
      (solcErrorStringMem3_mload64_of_size164 len word hmem hread64)
      (by decide) (by evm_ov),
    raw swap1 hdSwap2 (by evm_ov),
    raw dup2 hdDup2 (by evm_ov),
    raw swap1 hdSwap3 (by evm_ov),
    raw sub hdSub (by evm_ov),
    raw push1 ⟨100⟩ hd100 (by evm_ov),
    raw add hdAdd2 (by evm_ov),
    raw swap1 hdSwap4 (by evm_ov),
    raw rev 0 hdRev mem_cost (by evm_ov)]

set_option maxHeartbeats 1000000 in
-- GENERALIZES Reasoning.Reach.RD.solcCheckedAddStringRevert — use the size-164 revert tail.
theorem RD.solcCheckedAddStringRevert_size164 {code : ByteArray} {g : Sat256}
    {s0 : State} {ee : ExecutionEnv} {k C : ℕ}
    {pc okPc len rawWord shift word : UInt256} {op : Operation.POp} {width : ℕ}
    {a b ret : UInt256} {R : List UInt256} {mem rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD code ee g s0 pc (b :: a :: ret :: R) mem (UInt256.ofNat 3) rdata acc k C)
    (hadd : solcCheckedAddSuccessWf code pc okPc)
    (htail : solcErrorStringRevertTailWf code (solcCheckedArithmeticRevertPc pc)
      len rawWord shift op width)
    (hpush : op ≠ .PUSH0)
    (hover : UInt256.size ≤ a.toNat + b.toNat)
    (hword : UInt256.shiftLeft rawWord shift = word)
    (hmem : mem.size = 164)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hov : R.length + 9 ≤ 1024) :
    RDrev code g s0 := by
  rcases hadd with
    ⟨hd0, hd1, hd2, hd3, hd4, hd5, hd6, hd7, hd8, hd11, _, _, _, _, _, _⟩
  have hsum_lt2 : a.toNat + b.toNat < 2 * UInt256.size := by
    have ha : a.toNat < UInt256.size := a.val.isLt
    have hb : b.toNat < UInt256.size := b.val.isLt
    omega
  have hmod : (a.toNat + b.toNat) % UInt256.size =
      a.toNat + b.toNat - UInt256.size := by
    rw [Nat.mod_eq_sub_mod hover]
    exact Nat.mod_eq_of_lt (by omega)
  have haddNat : (a + b).toNat = a.toNat + b.toNat - UInt256.size := by
    rw [uadd_toNat, hmod]
  have hlt : UInt256.lt (a + b) a = ⟨1⟩ := by
    apply ult_one
    rw [haddNat]
    have hb : b.toNat < UInt256.size := b.val.isLt
    omega
  have rd6 := evm_run h with [
    raw jumpdest hd0 (by evm_ov),
    raw dup1 hd1 (by evm_ov),
    raw dup3 hd2 (by evm_ov),
    raw add hd3 (by evm_ov),
    raw dup3 hd4 (by evm_ov),
    raw dup2 hd5 (by evm_ov)]
  have rd7₀ := evm_run rd6 with [raw lt hd6 (by evm_ov)]
  have rd7 := rd7₀
  rw [hlt] at rd7
  have rd8₀ := evm_run rd7 with [raw iszero hd7 (by evm_ov)]
  have rd8 := rd8₀
  rw [show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at rd8
  have rdPush := evm_run rd8 with [raw push2 okPc hd8 (by evm_ov)]
  have rdTail₀ := rdPush.jumpiNT hd11 (by decide) (by simp only [List.length_cons]; omega)
  have rdTail := by
    simpa [solcCheckedArithmeticRevertPc] using rdTail₀
  exact RD.solcErrorStringRevertTail_size164 rdTail htail hpush hword hmem hread64
    (by simp only [List.length_cons]; omega)

set_option maxHeartbeats 1000000 in
theorem RD.solcCheckedAddStringRevert_feeToStaticcall_size164
    {code : ByteArray} {g : Sat256} {s0 : State} {ee : ExecutionEnv} {k C : ℕ}
    {pc okPc len rawWord shift word : UInt256} {op : Operation.POp} {width : ℕ}
    {a b ret : UInt256} {R : List UInt256} {mem rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD code ee g s0 pc (b :: a :: ret :: R) mem feeToStaticcallActiveWords rdata acc k C)
    (hadd : solcCheckedAddSuccessWf code pc okPc)
    (htail : solcErrorStringRevertTailWf code (solcCheckedArithmeticRevertPc pc)
      len rawWord shift op width)
    (hpush : op ≠ .PUSH0)
    (hover : UInt256.size ≤ a.toNat + b.toNat)
    (hword : UInt256.shiftLeft rawWord shift = word)
    (hmem : mem.size = 164)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hov : R.length + 9 ≤ 1024) :
    RDrev code g s0 := by
  rcases hadd with
    ⟨hd0, hd1, hd2, hd3, hd4, hd5, hd6, hd7, hd8, hd11, _, _, _, _, _, _⟩
  have hsum_lt2 : a.toNat + b.toNat < 2 * UInt256.size := by
    have ha : a.toNat < UInt256.size := a.val.isLt
    have hb : b.toNat < UInt256.size := b.val.isLt
    omega
  have hmod : (a.toNat + b.toNat) % UInt256.size =
      a.toNat + b.toNat - UInt256.size := by
    rw [Nat.mod_eq_sub_mod hover]
    exact Nat.mod_eq_of_lt (by omega)
  have haddNat : (a + b).toNat = a.toNat + b.toNat - UInt256.size := by
    rw [uadd_toNat, hmod]
  have hlt : UInt256.lt (a + b) a = ⟨1⟩ := by
    apply ult_one
    rw [haddNat]
    have hb : b.toNat < UInt256.size := b.val.isLt
    omega
  have rd6 := evm_run h with [
    raw jumpdest hd0 (by evm_ov),
    raw dup1 hd1 (by evm_ov),
    raw dup3 hd2 (by evm_ov),
    raw add hd3 (by evm_ov),
    raw dup3 hd4 (by evm_ov),
    raw dup2 hd5 (by evm_ov)]
  have rd7₀ := evm_run rd6 with [raw lt hd6 (by evm_ov)]
  have rd7 := rd7₀
  rw [hlt] at rd7
  have rd8₀ := evm_run rd7 with [raw iszero hd7 (by evm_ov)]
  have rd8 := rd8₀
  rw [show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at rd8
  have rdPush := evm_run rd8 with [raw push2 okPc hd8 (by evm_ov)]
  have rdTail₀ := rdPush.jumpiNT hd11 (by decide) (by simp only [List.length_cons]; omega)
  have rdTail := by
    simpa [solcCheckedArithmeticRevertPc] using rdTail₀
  exact RD.solcErrorStringRevertTail_feeToStaticcall_size164 rdTail htail hpush hword
    hmem hread64 (by simp only [List.length_cons]; omega)

set_option maxHeartbeats 1000000 in
theorem RD.uniswapSafeMathAddOverflow_feeToStaticcall_size164
    {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {a b ret : UInt256} {R : List UInt256} {mem : ByteArray}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD uniswapV2PairBytecode ee g s0 ⟨8515⟩ (b :: a :: ret :: R)
      mem feeToStaticcallActiveWords rdata acc k C)
    (hover : UInt256.size ≤ a.toNat + b.toNat)
    (hmem : mem.size = 164)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hov : R.length + 9 ≤ 1024) :
    RDrev uniswapV2PairBytecode g s0 := by
  exact RD.solcCheckedAddStringRevert_feeToStaticcall_size164
    (code := uniswapV2PairBytecode) (pc := ⟨8515⟩) (okPc := ⟨2911⟩)
    (len := ⟨20⟩)
    (rawWord := (⟨573467620053399432670716995166075968196518375287⟩ : UInt256))
    (shift := ⟨96⟩) (word := mintSafeMathAddOverflowStringWord)
    (op := .PUSH20) (width := 20) (a := a) (b := b) (ret := ret)
    (R := R) (mem := mem) h
    (by
      unfold solcCheckedAddSuccessWf
      repeat' first | apply And.intro | native_decide)
    (by
      unfold solcErrorStringRevertTailWf solcCheckedArithmeticRevertPc
      repeat' first | apply And.intro | native_decide)
    (by decide) hover (by rfl) hmem hread64 hov

set_option maxHeartbeats 1000000 in
theorem uniswapInternalMintRuntimeTotalSupplyOverflowReverts
    {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {mem rdata : ByteArray} {k C : ℕ}
    {value recipient ret : UInt256} {R : List UInt256}
    (rd8128 : RD uniswapV2PairBytecode ee g s0 ⟨8128⟩
      (value :: recipient :: ret :: R) mem feeToStaticcallActiveWords rdata (cA, σ) k C)
    (hover : UInt256.size ≤ (uniswapSlotWord ⟨0⟩ σ ee).toNat + value.toNat)
    (hmem : mem.size = 164)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hov : R.length + 12 ≤ 1024) :
    RDrev uniswapV2PairBytecode g s0 := by
  obtain ⟨_, _, rd8515⟩ :=
    uniswapInternalMintRuntimeTotalSupplyAddEntry rd8128 (by omega)
  exact RD.uniswapSafeMathAddOverflow_feeToStaticcall_size164
    (a := uniswapSlotWord ⟨0⟩ σ ee) (b := value) (ret := ⟨8147⟩)
    (R := value :: recipient :: ret :: R) rd8515 hover hmem hread64
    (by simp only [List.length_cons]; omega)

set_option maxHeartbeats 1000000 in
theorem uniswapInternalMintRuntimeBalanceOverflowReverts
    {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {mem rdata : ByteArray} {k C : ℕ}
    {value recipient ret : UInt256} {R : List UInt256}
    (rd8128 : RD uniswapV2PairBytecode ee g s0 ⟨8128⟩
      (value :: recipient :: ret :: R) mem feeToStaticcallActiveWords rdata (cA, σ) k C)
    (hperm : ee.perm = true)
    (htotalFit : (uniswapSlotWord ⟨0⟩ σ ee).toNat + value.toNat < UInt256.size)
    (hover :
      UInt256.size ≤
        (uniswapCodeOwnerStorageWord ee
          (sstoreAccountMap ee.codeOwner σ ⟨0⟩ (uniswapSlotWord ⟨0⟩ σ ee + value))
          (uniswapInternalMintBalanceHashSlot recipient mem)).toNat + value.toNat)
    (hmem : mem.size = 164)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hov : R.length + 16 ≤ 1024) :
    RDrev uniswapV2PairBytecode g s0 := by
  obtain ⟨_, _, rd8515Total⟩ :=
    uniswapInternalMintRuntimeTotalSupplyAddEntry rd8128 (by omega)
  obtain ⟨_, _, rd8147⟩ :=
    uniswapInternalMintRuntimeTotalSupplyAddedEntry rd8515Total htotalFit (by omega)
  obtain ⟨_, _, rd8153⟩ :=
    uniswapInternalMintRuntimeTotalSupplyStoredEntry rd8147 hperm (by omega)
  obtain ⟨_, _, rd8515Balance⟩ :=
    uniswapInternalMintRuntimeRecipientBalanceAddEntry rd8153 (by omega)
  have hmemHash : (uniswapInternalMintBalanceHashMem recipient mem).size = 164 := by
    rw [uniswapInternalMintBalanceHashMem_size_of_ge64 recipient (by rw [hmem]; omega),
      hmem]
  have hread64Hash :
      (uniswapInternalMintBalanceHashMem recipient mem).readWithPadding 64 32 =
        UInt256.toByteArray ⟨128⟩ :=
    uniswapInternalMintBalanceHashMem_read64_of_ge96 recipient (by rw [hmem]; omega) hread64
  exact RD.uniswapSafeMathAddOverflow_feeToStaticcall_size164
    (a :=
      uniswapCodeOwnerStorageWord ee
        (sstoreAccountMap ee.codeOwner σ ⟨0⟩ (uniswapSlotWord ⟨0⟩ σ ee + value))
        (uniswapInternalMintBalanceHashSlot recipient mem))
    (b := value) (ret := ⟨8190⟩) (R := value :: recipient :: ret :: R)
    rd8515Balance hover hmemHash hread64Hash
    (by simp only [List.length_cons]; omega)

end UniswapV2Pair
