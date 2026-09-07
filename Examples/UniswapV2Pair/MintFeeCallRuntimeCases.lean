import Examples.UniswapV2Pair.MintFeeFactoryCallRuntime
import Examples.UniswapV2Pair.MintFeeAfterFactoryCases

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace UniswapV2Pair

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 1000000 in
theorem uniswapMintFeeFunctionBodyRuntimeCasesWithMemory
    {g : Sat256} {s0 : State} {I : ExecutionEnv}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {mem rdata : ByteArray} {k C : ℕ}
    {reserve0 reserve1 ret : UInt256} {R : List UInt256}
    (evm : EVM.State)
    (rd7696 : RD uniswapV2PairBytecode I g s0 ⟨7696⟩
      (reserve1 :: reserve0 :: ret :: R) mem feeToStaticcallActiveWords rdata (cA, σ) k C)
    (hAccounts : accountMapEquiv σ evm.accountMap) (henv : evm.executionEnv = I)
    (hcreated : evm.createdAccounts = cA) (hσ0 : evm.σ₀ = s0.σ₀)
    (hgenesis : evm.genesisBlockHeader = s0.genesisBlockHeader)
    (hblocks : evm.blocks = s0.blocks) (hdepth : I.depth.val < 1024)
    (hclean0 : UInt256.land reserve0 reserve112Mask = reserve0)
    (hclean1 : UInt256.land reserve1 reserve112Mask = reserve1)
    (hperm : I.perm = true) (hmem : mem.size = 164)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hret : (D_J uniswapV2PairBytecode 0).contains ret = true)
    (hov : R.length + 32 ≤ 1024) :
    (ExecFuncBody config (mintFeeCallFrame reserve0 reserve1) evm mintFeeFunction.body
      .reverted ∧ RDrev uniswapV2PairBytecode g s0) ∨
    (∃ feeOn : Bool, ∃ frame' evm' σ' cA' mem' rdata' k' C',
      ExecFuncBody config (mintFeeCallFrame reserve0 reserve1) evm mintFeeFunction.body
        (.returned frame' evm' (some [.bool feeOn])) ∧
      accountMapEquiv σ' evm'.accountMap ∧ evm'.executionEnv = I ∧
      evm'.createdAccounts = cA' ∧ evm'.σ₀ = s0.σ₀ ∧
      evm'.genesisBlockHeader = s0.genesisBlockHeader ∧ evm'.blocks = s0.blocks ∧
      RD uniswapV2PairBytecode I g s0 ret ((if feeOn then ⟨1⟩ else ⟨0⟩) :: R)
        mem' feeToStaticcallActiveWords rdata' (cA', σ') k' C' ∧
      mem'.size = 164 ∧ mem'.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ ∧
      mem'.readWithPadding 96 32 = mem.readWithPadding 96 32) := by
  have h160 : 160 ≤ mem.size := by omega
  obtain ⟨_, _, rd7765⟩ := uniswapMintFeeRuntimeFactoryExtcodesizeOfTail rd7696 h160 hread64 hov
  by_cases hnoCode : extCodeSizeWord σ (mintFeeFactoryWord σ I) = ⟨0⟩
  · exact Or.inl ⟨uniswapMintFeeFunctionBody_reverts_noCode evm reserve0 reserve1
      (mintFeeFactoryGuardFalse_of_noCode hAccounts henv hnoCode),
      uniswapMintFeeRuntimeFactoryMissingCodeRevertsOfTail rd7765 hnoCode hov⟩
  · have hguard := mintFeeFactoryGuardTrue_of_code (reserve0 := reserve0)
      (reserve1 := reserve1) hAccounts henv hnoCode
    obtain ⟨cAFee, σFee, zFee, outFee, A_in, callGas, _, _, hΘ, rd7781, houtSize⟩ :=
      uniswapMintFeeRuntimeFactoryStaticcallMadeOfTail rd7765 hdepth hnoCode hov
    obtain ⟨evmFee, hcallAll, hpost, hcFee, hsFee, hgFee, hbFee, heFee⟩ :=
      uniswapMintFeeToTypedCall_source_of_mem hAccounts hcreated hσ0 hgenesis hblocks
        henv hdepth h160 hΘ
    obtain ⟨hrev, hshortRev, hcont⟩ := uniswapMintFeeRuntimeFactoryResultBranchesFromCallOfTail
      rd7781 h160 hread64 houtSize hov
    cases hz : zFee with
    | false =>
      exact Or.inl ⟨uniswapMintFeeFunctionBody_reverts_callFailure evm evmFee reserve0 reserve1
        hguard (by simpa only [hz] using hcallAll), hrev hz⟩
    | true =>
      have hcall : typedCallViaEVM config evm (EVM.address (uniswapAddressAtSlot evm ⟨5⟩))
          "feeTo" 0 [] (true, evmFee, outFee) false := by simpa only [hz] using hcallAll
      by_cases hshort : outFee.size < 32
      · exact Or.inl ⟨uniswapMintFeeFunctionBody_reverts_decode evm evmFee reserve0 reserve1
          hguard hcall (uniswapFeeToDecode_none_short hshort), hshortRev hz hshort⟩
      · have hout32 : 32 ≤ outFee.size := by omega
        obtain ⟨_, _, rd7825⟩ := hcont hz hout32
        have heFeeI := heFee.trans henv
        rw [← mintFeeKLastWord_eq_slot_of_accountMapEquiv hpost heFeeI] at rd7825
        have hrecipient : AccountAddress.ofNat (fromByteArrayBigEndian (outFee.extract 0 32)) =
            AccountAddress.ofNat (UInt256.ofNat
              (fromByteArrayBigEndian (outFee.extract 0 32))).toNat := by
          rw [UInt256.toNat_ofNat_of_lt (fromByteArrayBigEndian_extract0_32_lt hout32)]
        rcases uniswapMintFeeFunctionBodyRuntimeAfterFactoryCasesWithMemory evm evmFee
            (AccountAddress.ofNat (fromByteArrayBigEndian (outFee.extract 0 32)))
            rd7825 hguard hcall (uniswapFeeToDecode_ok hout32) hrecipient hpost heFeeI
            hclean0 hclean1 hperm
            ((feeToStaticcallMem_size_of_ge160 outFee h160 houtSize).trans hmem)
            (feeToStaticcallMem_read64_of_ge160 outFee h160 houtSize hread64) hret hov with
          hrev | ⟨feeOn, frame', evm', σ', mem', k', C', hbody, ha, he, hc,
            rdRet, hm, h64, hs, hg, hb, h96⟩
        · exact Or.inl hrev
        · exact Or.inr ⟨feeOn, frame', evm', σ', cAFee, mem', outFee, k', C',
            hbody, ha, he, hc.trans hcFee, hs.trans hsFee, hg.trans hgFee, hb.trans hbFee,
            rdRet, hm, h64, h96.trans (feeToStaticcallMem_read96 outFee h160 hout32 houtSize)⟩

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 1000000 in
theorem uniswapMintFeeCallRuntimeCasesWithMemory
    {g : Sat256} {s0 : State} {I : ExecutionEnv}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {mem rdata : ByteArray} {k C : ℕ}
    {reserve0 reserve1 ret : UInt256} {R : List UInt256}
    {caller : Frame} {args : List Expr} {retVar : Ident}
    (evm : EVM.State)
    (hcontract : caller.contract = contract)
    (hargs : evalExprs? config caller evm args =
      .ok [mintFeeReserve0Value reserve0, mintFeeReserve1Value reserve1])
    (rd7696 : RD uniswapV2PairBytecode I g s0 ⟨7696⟩
      (reserve1 :: reserve0 :: ret :: R) mem feeToStaticcallActiveWords rdata (cA, σ) k C)
    (hAccounts : accountMapEquiv σ evm.accountMap) (henv : evm.executionEnv = I)
    (hcreated : evm.createdAccounts = cA) (hσ0 : evm.σ₀ = s0.σ₀)
    (hgenesis : evm.genesisBlockHeader = s0.genesisBlockHeader)
    (hblocks : evm.blocks = s0.blocks) (hdepth : I.depth.val < 1024)
    (hclean0 : UInt256.land reserve0 reserve112Mask = reserve0)
    (hclean1 : UInt256.land reserve1 reserve112Mask = reserve1)
    (hperm : I.perm = true) (hmem : mem.size = 164)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hret : (D_J uniswapV2PairBytecode 0).contains ret = true)
    (hov : R.length + 32 ≤ 1024) :
    (ExecStmt config caller evm (.internalCall "_mintFee" args retVar) .reverted ∧ RDrev uniswapV2PairBytecode g s0) ∨
    (∃ feeOn : Bool, ∃ evm' σ' cA' mem' rdata' k' C',
      ExecStmt config caller evm (.internalCall "_mintFee" args retVar)
        (.ok (resumeAfterInternalCall caller retVar (some [.bool feeOn])) evm') ∧
      accountMapEquiv σ' evm'.accountMap ∧ evm'.executionEnv = I ∧
      evm'.createdAccounts = cA' ∧ evm'.σ₀ = s0.σ₀ ∧
      evm'.genesisBlockHeader = s0.genesisBlockHeader ∧ evm'.blocks = s0.blocks ∧
      RD uniswapV2PairBytecode I g s0 ret ((if feeOn then ⟨1⟩ else ⟨0⟩) :: R)
        mem' feeToStaticcallActiveWords rdata' (cA', σ') k' C' ∧
      mem'.size = 164 ∧ mem'.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ ∧
      mem'.readWithPadding 96 32 = mem.readWithPadding 96 32) := by
  rcases uniswapMintFeeFunctionBodyRuntimeCasesWithMemory evm rd7696 hAccounts henv hcreated hσ0
      hgenesis hblocks hdepth hclean0 hclean1 hperm hmem hread64 hret hov with
    ⟨hbody, rdRev⟩ | ⟨feeOn, f, e, σ', cA', m, data, k', C', hbody, ha, he, hc,
      hs, hg, hb, rd, hm, h64, h96⟩
  · refine Or.inl ⟨?_, rdRev⟩
    exact internalCallFunctionRevert (callee := mintFeeFunction)
      (locals := mintFeeCallStore reserve0 reserve1) hargs
      (by simpa only [hcontract] using uniswapLookupMintFeeFunction)
      (bindParams_mintFeeFunction_call reserve0 reserve1)
      (by simpa only [hcontract] using hbody)
  · refine Or.inr ⟨feeOn, e, σ', cA', m, data, k', C', ?_, ha, he, hc, hs, hg, hb, rd, hm, h64, h96⟩
    exact internalCallFunctionReturn (callee := mintFeeFunction) (calleeSolm := f)
      (locals := mintFeeCallStore reserve0 reserve1) hargs
      (by simpa only [hcontract] using uniswapLookupMintFeeFunction)
      (bindParams_mintFeeFunction_call reserve0 reserve1)
      (by simpa only [hcontract] using hbody)


set_option maxRecDepth 2000000 in
set_option maxHeartbeats 1000000 in
theorem uniswapMintFeeFunctionBodyRuntimeCases
    {g : Sat256} {s0 : State} {I : ExecutionEnv}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {mem rdata : ByteArray} {k C : ℕ}
    {reserve0 reserve1 ret : UInt256} {R : List UInt256}
    (evm : EVM.State)
    (rd7696 : RD uniswapV2PairBytecode I g s0 ⟨7696⟩
      (reserve1 :: reserve0 :: ret :: R) mem feeToStaticcallActiveWords rdata (cA, σ) k C)
    (hAccounts : accountMapEquiv σ evm.accountMap) (henv : evm.executionEnv = I)
    (hcreated : evm.createdAccounts = cA) (hσ0 : evm.σ₀ = s0.σ₀)
    (hgenesis : evm.genesisBlockHeader = s0.genesisBlockHeader)
    (hblocks : evm.blocks = s0.blocks) (hdepth : I.depth.val < 1024)
    (hclean0 : UInt256.land reserve0 reserve112Mask = reserve0)
    (hclean1 : UInt256.land reserve1 reserve112Mask = reserve1)
    (hperm : I.perm = true) (hmem : mem.size = 164)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hret : (D_J uniswapV2PairBytecode 0).contains ret = true)
    (hov : R.length + 32 ≤ 1024) :
    (ExecFuncBody config (mintFeeCallFrame reserve0 reserve1) evm mintFeeFunction.body
      .reverted ∧ RDrev uniswapV2PairBytecode g s0) ∨
    (∃ feeOn : Bool, ∃ frame' evm' σ' cA' mem' rdata' k' C',
      ExecFuncBody config (mintFeeCallFrame reserve0 reserve1) evm mintFeeFunction.body
        (.returned frame' evm' (some [.bool feeOn])) ∧
      accountMapEquiv σ' evm'.accountMap ∧ evm'.executionEnv = I ∧
      evm'.createdAccounts = cA' ∧ evm'.σ₀ = s0.σ₀ ∧
      evm'.genesisBlockHeader = s0.genesisBlockHeader ∧ evm'.blocks = s0.blocks ∧
      RD uniswapV2PairBytecode I g s0 ret ((if feeOn then ⟨1⟩ else ⟨0⟩) :: R)
        mem' feeToStaticcallActiveWords rdata' (cA', σ') k' C' ∧
      mem'.size = 164 ∧ mem'.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) := by
  rcases uniswapMintFeeFunctionBodyRuntimeCasesWithMemory evm rd7696 hAccounts henv hcreated
      hσ0 hgenesis hblocks hdepth hclean0 hclean1 hperm hmem hread64 hret hov with
    hrev | ⟨b, f, e, σ', ca, m, data, k', C', hb, ha, he, hc, hs, hg, hbl, rd, hm, h64, _⟩
  · exact Or.inl hrev
  · exact Or.inr ⟨b, f, e, σ', ca, m, data, k', C', hb, ha, he, hc, hs, hg, hbl, rd, hm, h64⟩


set_option maxRecDepth 2000000 in
set_option maxHeartbeats 1000000 in
theorem uniswapMintFeeCallRuntimeCases
    {g : Sat256} {s0 : State} {I : ExecutionEnv}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {mem rdata : ByteArray} {k C : ℕ}
    {reserve0 reserve1 ret : UInt256} {R : List UInt256}
    {caller : Frame} {args : List Expr} {retVar : Ident}
    (evm : EVM.State)
    (hcontract : caller.contract = contract)
    (hargs : evalExprs? config caller evm args =
      .ok [mintFeeReserve0Value reserve0, mintFeeReserve1Value reserve1])
    (rd7696 : RD uniswapV2PairBytecode I g s0 ⟨7696⟩
      (reserve1 :: reserve0 :: ret :: R) mem feeToStaticcallActiveWords rdata (cA, σ) k C)
    (hAccounts : accountMapEquiv σ evm.accountMap) (henv : evm.executionEnv = I)
    (hcreated : evm.createdAccounts = cA) (hσ0 : evm.σ₀ = s0.σ₀)
    (hgenesis : evm.genesisBlockHeader = s0.genesisBlockHeader)
    (hblocks : evm.blocks = s0.blocks) (hdepth : I.depth.val < 1024)
    (hclean0 : UInt256.land reserve0 reserve112Mask = reserve0)
    (hclean1 : UInt256.land reserve1 reserve112Mask = reserve1)
    (hperm : I.perm = true) (hmem : mem.size = 164)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hret : (D_J uniswapV2PairBytecode 0).contains ret = true)
    (hov : R.length + 32 ≤ 1024) :
    (ExecStmt config caller evm (.internalCall "_mintFee" args retVar) .reverted ∧ RDrev uniswapV2PairBytecode g s0) ∨
    (∃ feeOn : Bool, ∃ evm' σ' cA' mem' rdata' k' C',
      ExecStmt config caller evm (.internalCall "_mintFee" args retVar)
        (.ok (resumeAfterInternalCall caller retVar (some [.bool feeOn])) evm') ∧
      accountMapEquiv σ' evm'.accountMap ∧ evm'.executionEnv = I ∧
      evm'.createdAccounts = cA' ∧ evm'.σ₀ = s0.σ₀ ∧
      evm'.genesisBlockHeader = s0.genesisBlockHeader ∧ evm'.blocks = s0.blocks ∧
      RD uniswapV2PairBytecode I g s0 ret ((if feeOn then ⟨1⟩ else ⟨0⟩) :: R)
        mem' feeToStaticcallActiveWords rdata' (cA', σ') k' C' ∧
      mem'.size = 164 ∧ mem'.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) := by
  rcases uniswapMintFeeCallRuntimeCasesWithMemory evm hcontract hargs rd7696 hAccounts henv hcreated
      hσ0 hgenesis hblocks hdepth hclean0 hclean1 hperm hmem hread64 hret hov with
    hrev | ⟨b, e, σ', ca, m, data, k', C', hb, ha, he, hc, hs, hg, hbl, rd, hm, h64, _⟩
  · exact Or.inl hrev
  · exact Or.inr ⟨b, e, σ', ca, m, data, k', C', hb, ha, he, hc, hs, hg, hbl, rd, hm, h64⟩

end UniswapV2Pair
