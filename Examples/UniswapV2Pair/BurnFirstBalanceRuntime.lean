import Examples.UniswapV2Pair.BurnInitialRuntime

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace UniswapV2Pair
set_option maxRecDepth 2000000

set_option maxHeartbeats 1000000 in
theorem uniswapBurnRuntimeFirstBalanceOfStaticcallMadeOfTail
    {g : Sat256} {s0 : State} {I : ExecutionEnv}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {rdata : ByteArray} {target : UInt256} {R : List UInt256} {k C : ℕ}
    (rd4267 : RD uniswapV2PairBytecode I g s0 ⟨4267⟩
      (target :: target :: ⟨128⟩ :: ⟨36⟩ :: ⟨128⟩ :: ⟨32⟩ :: ⟨164⟩ ::
        balanceOfSelectorWord :: target :: R)
      (balanceOfThisCalldataMem (UInt256.ofNat I.codeOwner.val)) (UInt256.ofNat 6)
      rdata (cA, σ) k C)
    (hdepth : I.depth.val < 1024) (hcode : extCodeSizeWord σ target ≠ ⟨0⟩)
    (hov : R.length + 20 ≤ 1024) :
    ∃ (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap)
      (z : Bool) (o : ByteArray) (A_in : Substate) (callGas : UInt256) (k' C' : ℕ),
      (∃ (g'' : UInt256) (A' : Substate),
        (cA', σ', g'', A', z, o) = Ethereum.EVM.Θ I.blobVersionedHashes
          cA s0.genesisBlockHeader s0.blocks σ s0.σ₀ A_in
          (AccountAddress.ofUInt256 (UInt256.ofNat I.codeOwner.val)) I.sender
          (AccountAddress.ofUInt256 target) (toExecute σ (AccountAddress.ofUInt256 target))
          callGas (UInt256.ofNat I.gasPrice) ⟨0⟩ ⟨0⟩
          ((balanceOfThisCalldataMem (UInt256.ofNat I.codeOwner.val)).readWithPadding 128 36)
          (I.depth + 1) I.header false)
      ∧ RD uniswapV2PairBytecode I g s0 ⟨4283⟩
        ((if z then ⟨1⟩ else ⟨0⟩) :: ⟨164⟩ :: balanceOfSelectorWord :: target :: R)
        (balanceOfThisStaticcallMem (UInt256.ofNat I.codeOwner.val) o)
        balanceOfThisStaticcallActiveWords o (cA', σ') k' C' ∧ o.size < UInt256.size := by
  obtain ⟨_, _, _, rd4282⟩ := RD.solcExtcodesizeGuardOkGas (okPc := ⟨4279⟩) rd4267 hcode
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by jump_dest) (by native_decide)
    (by native_decide) (by native_decide) (by simp only [List.length_cons]; omega)
  obtain ⟨cA', σ', z, o, A_in, callGas, k', C', hΘ, rd4283, hoSize⟩ :=
    RD.solcStaticcall rd4282 (by native_decide) hdepth
      (by simp only [List.length_cons]; omega)
  exact ⟨cA', σ', z, o, A_in, callGas, k', C', hΘ,
    by simpa only [balanceOfThisStaticcallMem, balanceOfThisStaticcallActiveWords] using rd4283,
    hoSize⟩

set_option maxHeartbeats 1000000 in
theorem uniswapBurnRuntimeFirstBalanceOfResultBranchesOfTail
    {g : Sat256} {s0 : State} {I : ExecutionEnv}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {rdata : ByteArray} {target : UInt256} {R : List UInt256} {k C : ℕ}
    (rd4267 : RD uniswapV2PairBytecode I g s0 ⟨4267⟩
      (target :: target :: ⟨128⟩ :: ⟨36⟩ :: ⟨128⟩ :: ⟨32⟩ :: ⟨164⟩ ::
        balanceOfSelectorWord :: target :: R)
      (balanceOfThisCalldataMem (UInt256.ofNat I.codeOwner.val)) (UInt256.ofNat 6)
      rdata (cA, σ) k C)
    (hdepth : I.depth.val < 1024) (hcode : extCodeSizeWord σ target ≠ ⟨0⟩)
    (hov : R.length + 20 ≤ 1024) :
    ∃ (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap)
      (z : Bool) (o : ByteArray) (A_in : Substate) (callGas : UInt256),
      (∃ (g'' : UInt256) (A' : Substate),
        (cA', σ', g'', A', z, o) = Ethereum.EVM.Θ I.blobVersionedHashes
          cA s0.genesisBlockHeader s0.blocks σ s0.σ₀ A_in
          (AccountAddress.ofUInt256 (UInt256.ofNat I.codeOwner.val)) I.sender
          (AccountAddress.ofUInt256 target) (toExecute σ (AccountAddress.ofUInt256 target))
          callGas (UInt256.ofNat I.gasPrice) ⟨0⟩ ⟨0⟩
          ((balanceOfThisCalldataMem (UInt256.ofNat I.codeOwner.val)).readWithPadding 128 36)
          (I.depth + 1) I.header false)
      ∧ (z = false → RDrev uniswapV2PairBytecode g s0)
      ∧ (z = true → o.size < 32 → RDrev uniswapV2PairBytecode g s0)
      ∧ (z = true → 32 ≤ o.size → ∃ k' C',
        RD uniswapV2PairBytecode I g s0 ⟨4324⟩
          (UInt256.ofNat (fromByteArrayBigEndian (o.extract 0 32)) :: R)
          (balanceOfThisStaticcallMem (UInt256.ofNat I.codeOwner.val) o)
          balanceOfThisStaticcallActiveWords o (cA', σ') k' C')
      ∧ o.size < UInt256.size := by
  obtain ⟨cA', σ', z, o, A_in, callGas, k, C, hΘ, rd4283, hoSize⟩ :=
    uniswapBurnRuntimeFirstBalanceOfStaticcallMadeOfTail rd4267 hdepth hcode hov
  refine ⟨cA', σ', z, o, A_in, callGas, hΘ, ?_, ?_, ?_, hoSize⟩
  · intro hz
    have hstatus : (if z then (⟨1⟩ : UInt256) else ⟨0⟩) = ⟨0⟩ := by
      simp [hz]
    exact RD.solcCallSuccessGuardMissing (okPc := ⟨4299⟩) rd4283 hstatus
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) hoSize
      (by simp only [List.length_cons]; omega)
  · intro hz hshort
    have hstatus : (if z then (⟨1⟩ : UInt256) else ⟨0⟩) ≠ ⟨0⟩ := by
      rw [hz]
      decide
    obtain ⟨_, _, rd4301⟩ :=
      RD.solcCallSuccessGuardOk (okPc := ⟨4299⟩) rd4283 hstatus
        (by native_decide) (by native_decide) (by native_decide) (by native_decide)
        (by native_decide) (by jump_dest) (by native_decide) (by native_decide)
        (by simp only [List.length_cons]; omega)
    exact RD.uniswapBalanceOfReturnWordDecodeShortReverts
      (pc := ⟨4301⟩) (okPc := ⟨4321⟩) (self := UInt256.ofNat I.codeOwner.val)
      rd4301 hshort hoSize
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
      (by omega)
  · intro hz ho32
    have hstatus : (if z then (⟨1⟩ : UInt256) else ⟨0⟩) ≠ ⟨0⟩ := by
      rw [hz]
      decide
    obtain ⟨_, _, rd4301⟩ :=
      RD.solcCallSuccessGuardOk (okPc := ⟨4299⟩) rd4283 hstatus
        (by native_decide) (by native_decide) (by native_decide) (by native_decide)
        (by native_decide) (by jump_dest) (by native_decide) (by native_decide)
        (by simp only [List.length_cons]; omega)
    obtain ⟨k', C', rd4324⟩ :=
      RD.uniswapBalanceOfReturnWordDecodeOk
        (pc := ⟨4301⟩) (okPc := ⟨4321⟩) (self := UInt256.ofNat I.codeOwner.val)
        rd4301 ho32 hoSize
        (by native_decide) (by native_decide) (by native_decide) (by native_decide)
        (by native_decide) (by native_decide) (by native_decide) (by native_decide)
        (by native_decide) (by native_decide) (by native_decide) (by native_decide)
        (by jump_dest) (by native_decide) (by native_decide) (by native_decide)
        (by omega)
    exact ⟨k', C', rd4324⟩

set_option maxHeartbeats 1000000 in
theorem uniswapBurnRuntimeFirstBalanceOfDepthReverts
    {g : Sat256} {s0 : State} {I : ExecutionEnv}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {mem rdata : ByteArray} {aw target inOffset inSize outOffset outSize : UInt256}
    {R : List UInt256} {k C : ℕ}
    (rd4267 : RD uniswapV2PairBytecode I g s0 ⟨4267⟩
      (target :: target :: inOffset :: inSize :: outOffset :: outSize :: R)
      mem aw rdata (cA, σ) k C)
    (hdepth : I.depth = 1024) (hcode : extCodeSizeWord σ target ≠ ⟨0⟩)
    (hov : R.length + 20 ≤ 1024) : RDrev uniswapV2PairBytecode g s0 := by
  obtain ⟨_, _, _, rd4282⟩ := RD.solcExtcodesizeGuardOkGas (okPc := ⟨4279⟩) rd4267 hcode
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by jump_dest) (by native_decide)
    (by native_decide) (by native_decide) (by simp only [List.length_cons]; omega)
  obtain ⟨_, _, rd4283⟩ := RD.solcStaticcallDepthLimit rd4282 (by native_decide) hdepth (by omega)
  exact RD.solcCallSuccessGuardMissing (okPc := ⟨4299⟩) rd4283 rfl
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by decide) (by omega)

end UniswapV2Pair
