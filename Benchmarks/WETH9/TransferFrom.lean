import Benchmarks.WETH9.TransferFromBody

/-! # WETH9 `transferFrom(address,address,uint256)` refinement -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

namespace Benchmarks.WETH9

/-! ## Reach the shared body from the public `transferFrom` dispatch entry (pc 420) -/

/-- Peel the callvalue guard, pass the 3-word length check, decode `(src, dst, wad)`, and jump to the
    shared internal body (pc 1087) with `[wad, dstMasked, srcMasked, 361, sel]`. -/
theorem weth9TFReachBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = weth9Bytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz100 : 100 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (weth9SelBytes 3)) :
    ∃ k C, RD weth9Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1087⟩
      (calldataWord I.calldata 68 :: UInt256.land solcAddrMask (calldataWord I.calldata 36) ::
        UInt256.land solcAddrMask (calldataWord I.calldata 4) :: ⟨361⟩ :: [weth9SelWord I])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hsz4 : 4 ≤ I.calldata.size := by omega
  obtain ⟨_, _, h420⟩ := weth9ReachTransferFrom (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hsz4 hsize hsel
  obtain ⟨_, _, h434⟩ := weth9GuardPeelOk (gt := ⟨432⟩) h420 hwv
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by jump_dest) (by native_decide) (by native_decide)
  have hlt : UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨96⟩ = ⟨0⟩ :=
    solcDecodeLenCheckOkUnsigned (by simpa using hsz100) hsize
  have h455 := h434.pushConst (⟨361⟩ : UInt256) (op := .PUSH2) (width := 2) (by decide)
      (by native_decide) (by simp)
    |>.push1 ⟨4⟩ (by native_decide) (by simp)
    |>.dup1 (by native_decide) (by simp)
    |>.calldatasize (by native_decide) (by simp)
    |>.sub (by native_decide) (by simp)
    |>.push1 ⟨96⟩ (by native_decide) (by simp)
    |>.dup2 (by native_decide) (by simp)
    |>.lt (by native_decide) (by simp)
    |>.iszero (by native_decide) (by simp)
    |>.pushConst (⟨455⟩ : UInt256) (op := .PUSH2) (width := 2) (by decide) (by native_decide)
        (by simp)
    |>.jumpiT (by native_decide) (by rw [hlt]; decide) (by jump_dest) (by simp)
  exact RD.solcAddressAddressUint256ExternalMaskAndJumpMasked (routine := ⟨1087⟩) h455
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by jump_dest) (by simp only [List.length_singleton]; omega)

end Benchmarks.WETH9
