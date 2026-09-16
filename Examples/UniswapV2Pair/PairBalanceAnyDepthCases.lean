import Examples.UniswapV2Pair.PairBalanceCallCases
import Examples.UniswapV2Pair.PairBalanceDepthRuntime
import Examples.UniswapV2Pair.BurnInitialSource
import Examples.UniswapV2Pair.BalanceCallSource
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace UniswapV2Pair
set_option maxRecDepth 2000000

set_option maxHeartbeats 1000000 in
theorem uniswapPairBalanceCallRuntimeAnyDepthCases
    {g : Sat256} {s0 : State} {I : ExecutionEnv} {site : PairBalanceCallSite}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {base rdata : ByteArray} {aw ptr target : UInt256} {R : List UInt256} {k C : Nat}
    (evm : EVM.State) (token : AccountAddress) (locals : Store) (var retVar : Ident)
    (rd : RD uniswapV2PairBytecode I g s0 (site.pc)
      (target :: target :: ptr :: ⟨36⟩ :: ptr :: ⟨32⟩ :: (ptr + ⟨36⟩) :: balanceOfSelectorWord :: target :: R)
      (balanceDynamicCalldataMem base ptr (UInt256.ofNat I.codeOwner.val))
      (balanceDynamicCalldataWords aw ptr) rdata (cA, σ) k C)
    (ha : accountMapEquiv σ evm.accountMap) (he : evm.executionEnv = I)
    (hc : evm.createdAccounts = cA) (hs : evm.σ₀ = s0.σ₀)
    (hg : evm.genesisBlockHeader = s0.genesisBlockHeader) (hb : evm.blocks = s0.blocks)
    (hreceiver : evalExpr? config { contract := contract, locals := locals } evm (.var var) = .ok (.address token))
    (htoken : token = AccountAddress.ofUInt256 target)
    (hin : 96 ≤ base.size) (hgap : ptr.toNat - base.size < USize.size) (hlo : 96 ≤ ptr.toNat)
    (haw : aw.toNat * 32 < UInt256.size) (hfit : ptr.toNat + 67 < UInt256.size)
    (hread : base.readWithPadding 64 32 = ptr.toByteArray) (hov : R.length + 12 ≤ 1024) :
    (ExecBlock config { contract := contract, locals := locals } evm (balanceOfThisStmts (.var var) retVar) .reverted ∧
      RDrev uniswapV2PairBytecode g s0) ∨
    ∃ (evm' : EVM.State) (σ' : AccountMap) (cA' : Batteries.RBSet AccountAddress compare) (out : ByteArray) (k' C' : Nat),
      ExecBlock config { contract := contract, locals := locals } evm (balanceOfThisStmts (.var var) retVar)
        (.ok { contract := contract, locals := locals.insert retVar (uniswapUint256Value
          (UInt256.ofNat (fromByteArrayBigEndian (out.extract 0 32)))) } evm') ∧
      accountMapEquiv σ' evm'.accountMap ∧ evm'.createdAccounts = cA' ∧ evm'.σ₀ = s0.σ₀ ∧
      evm'.genesisBlockHeader = s0.genesisBlockHeader ∧ evm'.blocks = s0.blocks ∧ evm'.executionEnv = I ∧
      32 ≤ out.size ∧ out.size < UInt256.size ∧
      RD uniswapV2PairBytecode I g s0 (site.pc + ⟨57⟩)
        (UInt256.ofNat (fromByteArrayBigEndian (out.extract 0 32)) :: R)
        (balanceDynamicReturnMem base ptr (UInt256.ofNat I.codeOwner.val) out)
        (balanceDynamicCalldataWords aw ptr) out (cA', σ') k' C' := by
  by_cases hdepth : I.depth.val < 1024
  · exact uniswapPairBalanceCallRuntimeCases evm token locals var retVar rd ha he hc hs hg hb
      hreceiver htoken hdepth hin hgap hlo haw hfit hread hov
  · have hd : I.depth = 1024 := Fin.ext (by have := I.depth.isLt; omega)
    have hguard := evalExpr_uniswap_codeGuard ha htoken hreceiver
    by_cases hcode : extCodeSizeWord σ target = ⟨0⟩
    · refine Or.inl ⟨?_, RD.uniswapPairBalanceNoCodeReverts rd hcode (by simp only [List.length_cons]; omega)⟩
      exact checkedExternalCallVarNoCode (retVar := retVar) (name := "balanceOf")
        (sendVal := 0) (args := [this]) (perm := false) (by simpa only [hcode] using hguard)
    · have hpos : 0 < (extCodeSizeWord σ target).toNat :=
        Nat.pos_of_ne_zero (fun hz ↦ hcode (uint256_toNat_eq_zero hz))
      have hguard' : evalExpr? config { contract := contract, locals := locals } evm
          (.binary .gt (.extCodeSize (.var var)) (.intLit 0)) = .ok (.bool true) := by
        simpa only [decide_eq_true hpos] using hguard
      have hargs := evalExprs_uniswap_this_single evm locals
      have hcall : typedCallViaEVM config evm (EVM.address token) "balanceOf" 0
          [.address evm.executionEnv.codeOwner]
          (false, { evm with substate := (evm.addAccessedAccount (EVM.address token)).substate }, ByteArray.empty) false := by
        refine ⟨_, balanceOfThisCalldataMem_encode evm.executionEnv.codeOwner, ?_⟩
        apply callViaEVM.callNotMade rfl rfl
        rintro ⟨_, hne⟩
        exact hne (by rw [he]; exact hd)
      exact Or.inl ⟨checkedExternalCallFailure (retVar := retVar) hguard' hreceiver hargs hcall,
        RD.uniswapPairBalanceDepthReverts rd hcode hd hov⟩

end UniswapV2Pair
