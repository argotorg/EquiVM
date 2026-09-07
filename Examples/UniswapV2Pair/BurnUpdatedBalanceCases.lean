import Examples.UniswapV2Pair.BurnUpdatedBalanceCallRuntime
import Examples.UniswapV2Pair.PairBalanceCallCases
import Examples.UniswapV2Pair.BalanceCallSource
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace UniswapV2Pair
set_option maxRecDepth 2000000

set_option maxHeartbeats 1000000 in
theorem uniswapBurnUpdatedBalanceCallRuntimeCases
    {g : Sat256} {s0 : State} {I : ExecutionEnv} {second : Bool}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {base rdata : ByteArray} {aw ptr target : UInt256} {R : List UInt256} {k C : Nat}
    (evm : EVM.State) (token : AccountAddress) (locals : Store) (var retVar : Ident)
    (rd : RD uniswapV2PairBytecode I g s0 (if second then ⟨4815⟩ else ⟨4697⟩)
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
      RD uniswapV2PairBytecode I g s0 (if second then ⟨4872⟩ else ⟨4754⟩)
        (UInt256.ofNat (fromByteArrayBigEndian (out.extract 0 32)) :: R)
        (balanceDynamicReturnMem base ptr (UInt256.ofNat I.codeOwner.val) out)
        (balanceDynamicCalldataWords aw ptr) out (cA', σ') k' C' := by
  cases second with
  | false =>
    exact uniswapPairBalanceCallRuntimeCases (site := .burn0) evm token locals var retVar rd
      ha he hc hs hg hb hreceiver htoken hdepth hin hgap hlo haw hfit hread hov
  | true =>
    exact uniswapPairBalanceCallRuntimeCases (site := .burn1) evm token locals var retVar rd
      ha he hc hs hg hb hreceiver htoken hdepth hin hgap hlo haw hfit hread hov

end UniswapV2Pair
