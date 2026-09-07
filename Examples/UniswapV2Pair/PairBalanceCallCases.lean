import Examples.UniswapV2Pair.PairBalanceCallRuntime
import Examples.UniswapV2Pair.BurnInitialSource
import Examples.UniswapV2Pair.BalanceCallSource
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace UniswapV2Pair
set_option maxRecDepth 2000000

set_option maxHeartbeats 1000000 in
theorem uniswapPairBalanceCallRuntimeCases
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
    (htoken : token = AccountAddress.ofUInt256 target) (hdepth : I.depth.val < 1024)
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
  have hguard := evalExpr_uniswap_codeGuard ha htoken hreceiver
  have hargs := evalExprs_uniswap_this_single evm locals
  by_cases hcode : extCodeSizeWord σ target = ⟨0⟩
  · refine Or.inl ⟨?_, RD.uniswapPairBalanceNoCodeReverts rd hcode (by simp only [List.length_cons]; omega)⟩
    exact checkedExternalCallVarNoCode (retVar := retVar) (name := "balanceOf")
      (sendVal := 0) (args := [this]) (perm := false) (by simpa only [hcode] using hguard)
  · have hpositive : 0 < (extCodeSizeWord σ target).toNat :=
      Nat.pos_of_ne_zero (fun hz => hcode (uint256_toNat_eq_zero hz))
    simp only [hpositive, decide_true] at hguard
    obtain ⟨cA', σ', z, out, A_in, callGas, k', C', hTheta, rdResult, hout⟩ :=
      RD.uniswapPairBalanceCallMade rd hcode hdepth hgap haw hfit hov
    obtain ⟨evm', hcallRaw, ha', hc', hs', hg', hb', he'⟩ :=
      uniswapBalanceTypedCallFromState_source (evm1S := evm) (inOff := ⟨128⟩)
        ha hc hs hg hb he hdepth (balanceOfThisCalldataMem_encode I.codeOwner) hTheta
    have hcall : typedCallViaEVM config evm (EVM.address token) "balanceOf" 0
        [.address evm.executionEnv.codeOwner] (z, evm', out) false := by
      rw [balanceCallAddress_self, htoken]
      exact hcallRaw
    rcases RD.uniswapPairBalanceCallResultCases rdResult hin hgap hlo haw hfit hread hout (by omega) with
      ⟨hbad, rdRev⟩ | ⟨hz, ho32, kr, Cr, rdRet⟩
    · refine Or.inl ⟨?_, rdRev⟩
      cases z with
      | false => exact checkedExternalCallFailure (retVar := retVar) hguard hreceiver hargs hcall
      | true =>
        have hshort : out.size < 32 := by rcases hbad with heq | hshort; cases heq; exact hshort
        have hdec : config.externalABI.decode? "balanceOf" out = none := by
          change uniswapExternalABI.decode? "balanceOf" out = none
          simpa [uniswapExternalABI, uint256, uint256Int, abiUInt256] using
            decodeReturnValueWithMode_legacy_uint256_none_short (returndata := out) hshort
        exact checkedExternalCallDecodeRevert (retVar := retVar) hguard hreceiver hargs hcall hdec
    · refine Or.inr ⟨evm', σ', cA', out, kr, Cr, ?_, ha', hc', hs', hg', hb', he'.trans he, ho32, hout, rdRet⟩
      exact checkedExternalCallSuccess (value := [uniswapUint256Value
        (UInt256.ofNat (fromByteArrayBigEndian (out.extract 0 32)))])
        (retVar := retVar) hguard hreceiver hargs (by simpa only [hz] using hcall) (uniswapBalanceOfDecode_ok ho32)

end UniswapV2Pair
