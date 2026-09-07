import Examples.UniswapV2Pair.BurnUpdatedBalanceRuntime
import Examples.UniswapV2Pair.PairBalanceCallRuntime
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace UniswapV2Pair
set_option maxRecDepth 2000000

set_option maxHeartbeats 1000000 in
theorem RD.uniswapBurnUpdatedBalanceCallMade
    {g : Sat256} {s0 : State} {I : ExecutionEnv} {second : Bool}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {base rdata : ByteArray} {aw ptr target : UInt256} {R : List UInt256} {k C : Nat}
    (rd4697 : RD uniswapV2PairBytecode I g s0 (if second then ⟨4815⟩ else ⟨4697⟩)
      (target :: target :: ptr :: ⟨36⟩ :: ptr :: ⟨32⟩ :: (ptr + ⟨36⟩) :: balanceOfSelectorWord :: target :: R)
      (balanceDynamicCalldataMem base ptr (UInt256.ofNat I.codeOwner.val)) (balanceDynamicCalldataWords aw ptr) rdata (cA, σ) k C)
    (hcode : extCodeSizeWord σ target ≠ ⟨0⟩) (hdepth : I.depth.val < 1024)
    (hgap : ptr.toNat - base.size < USize.size) (haw : aw.toNat * 32 < UInt256.size)
    (hfit : ptr.toNat + 67 < UInt256.size) (hov : R.length + 12 ≤ 1024) :
    ∃ (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap) (z : Bool) (out : ByteArray)
      (A_in : Substate) (callGas : UInt256) (k' C' : Nat),
      (∃ (g'' : UInt256) (A' : Substate),
        (cA', σ', g'', A', z, out) = Ethereum.EVM.Θ I.blobVersionedHashes
          cA s0.genesisBlockHeader s0.blocks σ s0.σ₀ A_in
          (AccountAddress.ofUInt256 (UInt256.ofNat I.codeOwner.val)) I.sender
          (AccountAddress.ofUInt256 target) (toExecute σ (AccountAddress.ofUInt256 target))
          callGas (UInt256.ofNat I.gasPrice) ⟨0⟩ ⟨0⟩
          ((balanceOfThisCalldataMem (UInt256.ofNat I.codeOwner.val)).readWithPadding 128 36)
          (I.depth + 1) I.header false) ∧
      RD uniswapV2PairBytecode I g s0 (if second then ⟨4831⟩ else ⟨4713⟩)
        ((if z then ⟨1⟩ else ⟨0⟩) :: (ptr + ⟨36⟩) :: balanceOfSelectorWord :: target :: R)
        (balanceDynamicReturnMem base ptr (UInt256.ofNat I.codeOwner.val) out)
        (balanceDynamicCalldataWords aw ptr) out (cA', σ') k' C' ∧ out.size < UInt256.size := by
  cases second with
  | false => exact RD.uniswapPairBalanceCallMade (site := .burn0) rd4697 hcode hdepth hgap haw hfit hov
  | true => exact RD.uniswapPairBalanceCallMade (site := .burn1) rd4697 hcode hdepth hgap haw hfit hov

set_option maxHeartbeats 1000000 in
theorem RD.uniswapBurnUpdatedBalanceCallResultCases
    {g : Sat256} {s0 : State} {I : ExecutionEnv} {second : Bool}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {base out : ByteArray} {aw ptr target : UInt256} {z : Bool} {R : List UInt256} {k C : Nat}
    (rd4713 : RD uniswapV2PairBytecode I g s0 (if second then ⟨4831⟩ else ⟨4713⟩)
      ((if z then ⟨1⟩ else ⟨0⟩) :: (ptr + ⟨36⟩) :: balanceOfSelectorWord :: target :: R)
      (balanceDynamicReturnMem base ptr (UInt256.ofNat I.codeOwner.val) out)
      (balanceDynamicCalldataWords aw ptr) out acc k C)
    (hin : 96 ≤ base.size) (hgap : ptr.toNat - base.size < USize.size) (hlo : 96 ≤ ptr.toNat)
    (haw : aw.toNat * 32 < UInt256.size) (hfit : ptr.toNat + 67 < UInt256.size)
    (hread : base.readWithPadding 64 32 = ptr.toByteArray) (hout : out.size < UInt256.size)
    (hov : R.length + 8 ≤ 1024) :
    ((z = false ∨ out.size < 32) ∧ RDrev uniswapV2PairBytecode g s0) ∨
      (z = true ∧ 32 ≤ out.size ∧ ∃ k' C', RD uniswapV2PairBytecode I g s0 (if second then ⟨4872⟩ else ⟨4754⟩)
        (UInt256.ofNat (fromByteArrayBigEndian (out.extract 0 32)) :: R)
        (balanceDynamicReturnMem base ptr (UInt256.ofNat I.codeOwner.val) out)
        (balanceDynamicCalldataWords aw ptr) out acc k' C') := by
  cases second with
  | false => exact RD.uniswapPairBalanceCallResultCases (site := .burn0) rd4713 hin hgap hlo haw hfit hread hout hov
  | true => exact RD.uniswapPairBalanceCallResultCases (site := .burn1) rd4713 hin hgap hlo haw hfit hread hout hov

set_option maxHeartbeats 1000000 in
theorem RD.uniswapBurnUpdatedBalanceNoCodeReverts
    {g : Sat256} {s0 : State} {I : ExecutionEnv} {second : Bool}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {mem rdata : ByteArray} {aw target : UInt256} {R : List UInt256} {k C : Nat}
    (rd : RD uniswapV2PairBytecode I g s0 (if second then ⟨4815⟩ else ⟨4697⟩)
      (target :: target :: R) mem aw rdata (cA, σ) k C)
    (hcode : extCodeSizeWord σ target = ⟨0⟩) (hov : R.length + 4 ≤ 1024) : RDrev uniswapV2PairBytecode g s0 := by
  cases second with
  | false => exact RD.uniswapPairBalanceNoCodeReverts (site := .burn0) rd hcode hov
  | true => exact RD.uniswapPairBalanceNoCodeReverts (site := .burn1) rd hcode hov

end UniswapV2Pair
