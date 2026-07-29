import Examples.UniswapV2Pair.SkimSafeTransferRuntime

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace UniswapV2Pair

/-!
  Dynamic `_safeTransfer` return-data tails for the Uniswap runtime.

  The control-flow idea is contract-independent, but these statements are still tied to
  Uniswap bytecode PCs and Skim memory layouts.
-/

set_option maxHeartbeats 1000000 in
theorem RD.uniswapSafeTransferReturnNonemptyHugeReverts {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ}
    {status returnPc base gasMarker value toWord token ret : UInt256}
    {R : List UInt256} {callMem out : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨6595⟩
      (status :: returnPc :: UInt256.land token solcAddrMask :: ⟨96⟩ :: ⟨0⟩ ::
        value :: toWord :: token :: ret :: R)
      callMem gasMarker out acc k C)
    (houtNe : out.size ≠ 0) (houtSize : out.size < UInt256.size)
    (hcallMem64 :
      (if (⟨64⟩ : UInt256).toNat ≥ callMem.size ∨
          (⟨64⟩ : UInt256) ≥ gasMarker * ⟨32⟩
       then ⟨0⟩
       else UInt256.ofNat
        (fromByteArrayBigEndian (callMem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
      base)
    (haw64 :
      UInt256.ofNat (MachineState.M gasMarker.toNat (⟨64⟩ : UInt256).toNat 32) =
        gasMarker)
    (hawBase :
      UInt256.ofNat (MachineState.M gasMarker.toNat base.toNat 32) = gasMarker)
    (hHugeCost : g.toNat <
      Cₘ (UInt256.ofNat (MachineState.M gasMarker.toNat ((base + ⟨32⟩).toNat) out.size)) -
        Cₘ gasMarker)
    (hR : R.length + 16 ≤ 1024) :
    RDrev UniswapV2Pair.uniswapV2PairBytecode g s0 := by
  let rdsz : UInt256 := UInt256.ofNat out.size
  have hrdsz_ne : rdsz ≠ ⟨0⟩ := by
    intro hzero
    have hnat : rdsz.toNat = 0 := by rw [hzero]; rfl
    rw [show rdsz.toNat = out.size by
      dsimp [rdsz]
      exact UInt256.toNat_ofNat_of_lt houtSize] at hnat
    exact houtNe hnat
  have heq0 : UInt256.eq rdsz (⟨0⟩ : UInt256) = ⟨0⟩ := u256_eq_of_ne hrdsz_ne
  have rd6607 := evm_run h with [
    swap2, pop, pop, returndatasize, dup1, push1 ⟨0⟩, dup2, eq, push2 ⟨6641⟩]
  change UInt256.eq rdsz (⟨0⟩ : UInt256) = ⟨0⟩ at heq0
  rw [show UInt256.ofNat out.size = rdsz from rfl, heq0] at rd6607
  have rd6610 := evm_run rd6607 with [jumpiNT (by native_decide), push1 ⟨64⟩]
  have rd6611 := RD.mload 0 base gasMarker rd6610 (by native_decide)
    (by intro s haw hstk; simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk, haw64])
    hcallMem64 haw64
    (by simp only [List.length_cons]; omega)
  let rounded : UInt256 := UInt256.land (UInt256.add rdsz ⟨63⟩) (UInt256.lnot ⟨31⟩)
  let mem2 : ByteArray := ((base + rounded).toByteArray).write 0 callMem 64 32
  have rd6626pre := evm_run rd6611 with [
    swap2, pop, push1 ⟨31⟩, not, push1 ⟨63⟩, returndatasize, add, and,
    dup3, add, push1 ⟨64⟩]
  have rd6626 := RD.mstore 0 mem2 gasMarker rd6626pre (by native_decide)
    (by intro s haw hstk; simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk, haw64])
    (by dsimp [mem2]; rfl)
    haw64
    (by simp only [List.length_cons]; omega)
  let mem3 : ByteArray := rdsz.toByteArray.write 0 mem2 base.toNat 32
  have rd6629pre := evm_run rd6626 with [returndatasize, dup3]
  have rd6629 := RD.mstore 0 mem3 gasMarker rd6629pre (by native_decide)
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk, hawBase])
    (by dsimp [mem3])
    hawBase
    (by simp only [List.length_cons]; omega)
  have rd6636 := evm_run rd6629 with [returndatasize, push1 ⟨0⟩, push1 ⟨32⟩, dup5, add]
  exact RD.returndatacopyOOG
    (Cₘ (UInt256.ofNat (MachineState.M gasMarker.toNat ((base + ⟨32⟩).toNat) out.size)) -
      Cₘ gasMarker)
    rd6636 (by native_decide)
    (by rw [show (⟨0⟩ : UInt256).toNat = 0 from rfl, UInt256.toNat_ofNat_of_lt houtSize]; omega)
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk,
        UInt256.toNat_ofNat_of_lt houtSize])
    hHugeCost
    (by simp only [List.length_cons]; omega)

set_option maxHeartbeats 1000000 in
theorem RD.uniswapSafeTransferReturnFailureMessageFrom6697Reverts {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {base status value toWord token ret : UInt256}
    {R : List UInt256} {mem0 out : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {aw0 : UInt256}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨6697⟩
      (base :: status :: value :: toWord :: token :: ret :: R) mem0 aw0 out acc k C)
    (hR : R.length + 16 ≤ 1024) :
    RDrev UniswapV2Pair.uniswapV2PairBytecode g s0 := by
  let fp0 : UInt256 :=
    if (⟨64⟩ : UInt256).toNat ≥ mem0.size ∨ (⟨64⟩ : UInt256) ≥ aw0 * ⟨32⟩ then
      ⟨0⟩
    else UInt256.ofNat (fromByteArrayBigEndian (mem0.readWithPadding 64 32))
  let aw1 : UInt256 := UInt256.ofNat (MachineState.M aw0.toNat (⟨64⟩ : UInt256).toNat 32)
  have rd6701 := evm_run h with [push1 ⟨64⟩, dup1]
  have rd6701' := RD.mload
    (Cₘ aw1 - Cₘ aw0) fp0 aw1 rd6701 (by native_decide)
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk, aw1])
    (by rfl)
    (by rfl)
    (by simp only [List.length_cons]; omega)
  have rd6705 := rd6701'.pushConst (⟨4594637⟩ : UInt256)
    (width := 3) (op := .PUSH3) (by native_decide) (by native_decide) (by evm_ov)
  have rd6708 := evm_run rd6705 with [push1 ⟨229⟩, shl, dup2]
  let err0 : ByteArray := (UInt256.toByteArray uniswapErrorStringSelector).write 0 mem0 fp0.toNat 32
  let aw2 : UInt256 := UInt256.ofNat (MachineState.M aw1.toNat fp0.toNat 32)
  have rd6710 := RD.mstore
    (Cₘ aw2 - Cₘ aw1) err0 aw2 rd6708 (by native_decide)
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk, aw1, aw2])
    (by simp [err0, uniswapErrorStringSelector, solcErrorStringSelector])
    (by rfl)
    (by simp only [List.length_cons]; omega)
  have rd6716 := evm_run rd6710 with [push1 ⟨32⟩, push1 ⟨4⟩, dup3, add]
  let off1 : UInt256 := fp0 + ⟨4⟩
  let err1 : ByteArray := (UInt256.toByteArray (⟨32⟩ : UInt256)).write 0 err0 off1.toNat 32
  let aw3 : UInt256 := UInt256.ofNat (MachineState.M aw2.toNat off1.toNat 32)
  have rd6717 := RD.mstore
    (Cₘ aw3 - Cₘ aw2) err1 aw3 rd6716 (by native_decide)
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk, aw2, aw3, off1])
    (by simp [err1, off1])
    (by rfl)
    (by simp only [List.length_cons]; omega)
  have rd6723 := evm_run rd6717 with [push1 ⟨26⟩, push1 ⟨36⟩, dup3, add]
  let off2 : UInt256 := fp0 + ⟨36⟩
  let err2 : ByteArray := (UInt256.toByteArray (⟨26⟩ : UInt256)).write 0 err1 off2.toNat 32
  let aw4 : UInt256 := UInt256.ofNat (MachineState.M aw3.toNat off2.toNat 32)
  have rd6724 := RD.mstore
    (Cₘ aw4 - Cₘ aw3) err2 aw4 rd6723 (by native_decide)
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk, aw3, aw4, off2])
    (by simp [err2, off2])
    (by rfl)
    (by simp only [List.length_cons]; omega)
  have rd6757 := rd6724.pushConst uniswapSafeTransferFailedStringWord
    (width := 32) (op := .PUSH32) (by native_decide) (by native_decide) (by evm_ov)
  have rd6760 := evm_run rd6757 with [push1 ⟨68⟩, dup3, add]
  let off3 : UInt256 := fp0 + ⟨68⟩
  let err3 : ByteArray := (UInt256.toByteArray uniswapSafeTransferFailedStringWord).write 0
    err2 off3.toNat 32
  let aw5 : UInt256 := UInt256.ofNat (MachineState.M aw4.toNat off3.toNat 32)
  have rd6762 := RD.mstore
    (Cₘ aw5 - Cₘ aw4) err3 aw5 rd6760 (by native_decide)
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk, aw4, aw5, off3])
    (by simp [err3, off3])
    (by rfl)
    (by simp only [List.length_cons]; omega)
  have rd6763 := evm_run rd6762 with [swap1]
  let fp1 : UInt256 :=
    if (⟨64⟩ : UInt256).toNat ≥ err3.size ∨ (⟨64⟩ : UInt256) ≥ aw5 * ⟨32⟩ then
      ⟨0⟩
    else UInt256.ofNat (fromByteArrayBigEndian (err3.readWithPadding 64 32))
  let aw6 : UInt256 := UInt256.ofNat (MachineState.M aw5.toNat (⟨64⟩ : UInt256).toNat 32)
  have rd6764 := RD.mload
    (Cₘ aw6 - Cₘ aw5) fp1 aw6 rd6763 (by native_decide)
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk, aw5, aw6])
    (by rfl)
    (by rfl)
    (by simp only [List.length_cons]; omega)
  have rd6772 := evm_run rd6764 with [
    swap1, dup2, swap1, sub, push1 ⟨100⟩, add, swap1]
  exact RD.rev
    (Cₘ (UInt256.ofNat
      (MachineState.M aw6.toNat fp1.toNat ((⟨100⟩ : UInt256) + fp0.sub fp1).toNat)) -
      Cₘ aw6)
    rd6772 (by native_decide)
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk])
    (by simp only [List.length_cons]; omega)

set_option maxHeartbeats 1000000 in
theorem RD.uniswapSafeTransferReturnNonemptyFailureReverts {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {base value toWord token ret : UInt256}
    {R : List UInt256} {mem0 out : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {aw0 : UInt256}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨6652⟩
      (base :: ⟨0⟩ :: value :: toWord :: token :: ret :: R) mem0 aw0 out acc k C)
    (hR : R.length + 16 ≤ 1024) :
    RDrev UniswapV2Pair.uniswapV2PairBytecode g s0 := by
  have rd6692 := evm_run h with [
    dup2, dup1, iszero, push2 ⟨6692⟩, jumpiT (by native_decide) (by jump_dest)]
  have rd6697 := evm_run rd6692 with [
    jumpdest, push2 ⟨6773⟩, jumpiNT (by native_decide)]
  exact RD.uniswapSafeTransferReturnFailureMessageFrom6697Reverts (R := R) rd6697 hR

set_option maxHeartbeats 1000000 in
theorem RD.uniswapSafeTransferReturnNonemptyTrueStatusToLengthLoaded {g : Sat256}
    {s0 : State} {ee : ExecutionEnv} {k C : ℕ}
    {base retPtr value toWord token ret : UInt256}
    {R : List UInt256} {mem0 out : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {aw0 : UInt256}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨6652⟩
      (base :: ⟨1⟩ :: value :: toWord :: token :: ret :: R) mem0 aw0 out acc k C)
    (houtNe : out.size ≠ 0) (houtSize : out.size < 2 ^ 255)
    (hloadBase :
      (if base.toNat ≥ mem0.size ∨ base ≥ aw0 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat (fromByteArrayBigEndian (mem0.readWithPadding base.toNat 32))) =
      UInt256.ofNat out.size)
    (hawBase : UInt256.ofNat (MachineState.M aw0.toNat base.toNat 32) = aw0)
    (hretPtr : (⟨32⟩ : UInt256) + base = retPtr)
    (hR : R.length + 16 ≤ 1024) :
    ∃ k' C', RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨6676⟩
      (UInt256.ofNat out.size :: retPtr :: base :: ⟨1⟩ ::
        value :: toWord :: token :: ret :: R)
      mem0 aw0 out acc k' C' := by
  have hsizeNe : UInt256.ofNat out.size ≠ ⟨0⟩ := by
    intro hzero
    have hnat : (UInt256.ofNat out.size).toNat = 0 := by rw [hzero]; rfl
    rw [UInt256.toNat_ofNat_of_lt (lt_size_of_lt_sign houtSize)] at hnat
    exact houtNe hnat
  have hsizeIsZero : UInt256.isZero (UInt256.ofNat out.size) = ⟨0⟩ :=
    isZero_eq_zero_of_ne hsizeNe
  have rd6661 := evm_run h with [
    dup2, dup1, iszero, push2 ⟨6692⟩, jumpiNT (by native_decide), pop, dup1]
  have rd6662 := RD.mload 0 (UInt256.ofNat out.size) aw0 rd6661 (by native_decide)
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk, hawBase])
    hloadBase hawBase
    (by simp only [List.length_cons]; omega)
  have rd6675 := evm_run rd6662 with [
    iszero, dup1, push2 ⟨6692⟩, jumpiNT hsizeIsZero, pop, dup1, dup1,
    push1 ⟨32⟩, add, swap1]
  have rd6676 := RD.mload 0 (UInt256.ofNat out.size) aw0 rd6675 (by native_decide)
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk, hawBase])
    hloadBase hawBase
    (by simp only [List.length_cons]; omega)
  exact ⟨_, _, by simpa [hretPtr] using rd6676⟩

set_option maxHeartbeats 1000000 in
theorem RD.uniswapSafeTransferReturnNonemptyShortReverts {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {next : UInt256} {T : List UInt256} {mem0 out : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {aw0 : UInt256}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨6676⟩
      (UInt256.ofNat out.size :: next :: T) mem0 aw0 out acc k C)
    (hs : out.size < 32) (ho : out.size < 2 ^ 255) (hT : T.length + 4 ≤ 1024) :
    RDrev UniswapV2Pair.uniswapV2PairBytecode g s0 := by
  have rd6684₀ := evm_run h with [push1 ⟨32⟩, dup2, lt, iszero, push2 ⟨6689⟩]
  have hlt : UInt256.lt (UInt256.ofNat out.size) (⟨32⟩ : UInt256) = ⟨1⟩ :=
    Reasoning.Theory.ult_one (by
    rw [show (⟨32⟩ : UInt256).toNat = 32 from by decide,
      UInt256.toNat_ofNat_of_lt (lt_size_of_lt_sign ho)]
    exact hs)
  have rd6684 := rd6684₀
  rw [hlt, show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at rd6684
  have rd6685 := evm_run rd6684 with [jumpiNT (by native_decide)]
  exact RD.solcPush1Dup1Revert0 rd6685 (by native_decide) (by native_decide)
    (by native_decide) (by simp only [List.length_cons]; omega)

set_option maxHeartbeats 1000000 in
theorem RD.uniswapSafeTransferReturnNonemptyFalseReverts {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {base retPtr value toWord token ret : UInt256}
    {R : List UInt256} {mem0 out : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {aw0 : UInt256}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨6676⟩
      (UInt256.ofNat out.size :: retPtr :: base :: ⟨1⟩ :: value :: toWord :: token ::
        ret :: R)
      mem0 aw0 out acc k C)
    (hout32 : 32 ≤ out.size) (houtSize : out.size < 2 ^ 255)
    (hword : UInt256.ofNat (fromByteArrayBigEndian (out.extract 0 32)) = ⟨0⟩)
    (hloadRet :
      (if retPtr.toNat ≥ mem0.size ∨ retPtr ≥ aw0 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat (fromByteArrayBigEndian (mem0.readWithPadding retPtr.toNat 32))) =
      UInt256.ofNat (fromByteArrayBigEndian (out.extract 0 32)))
    (hawRet : UInt256.ofNat (MachineState.M aw0.toNat retPtr.toNat 32) = aw0)
    (hR : R.length + 16 ≤ 1024) :
    RDrev UniswapV2Pair.uniswapV2PairBytecode g s0 := by
  have rd6684₀ := evm_run h with [push1 ⟨32⟩, dup2, lt, iszero, push2 ⟨6689⟩]
  have hlt : UInt256.lt (UInt256.ofNat out.size) (⟨32⟩ : UInt256) = ⟨0⟩ := by
    apply Reasoning.Theory.ult_zero
    rw [show (⟨32⟩ : UInt256).toNat = 32 from by decide,
      UInt256.toNat_ofNat_of_lt (lt_size_of_lt_sign houtSize)]
    exact hout32
  have rd6684 := rd6684₀
  rw [hlt, show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rd6684
  have rd6691 := evm_run rd6684 with [jumpiT (by native_decide) (by jump_dest), jumpdest, pop]
  have rd6692₀ := RD.mload
    0 (UInt256.ofNat (fromByteArrayBigEndian (out.extract 0 32))) aw0
    rd6691 (by native_decide)
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk, hawRet])
    hloadRet hawRet
    (by simp only [List.length_cons]; omega)
  have rd6692 := rd6692₀
  rw [hword] at rd6692
  have rd6697 := evm_run rd6692 with [
    jumpdest, push2 ⟨6773⟩, jumpiNT (by native_decide)]
  exact RD.uniswapSafeTransferReturnFailureMessageFrom6697Reverts (R := R) rd6697 hR

set_option maxHeartbeats 1000000 in
theorem RD.uniswapSafeTransferReturnNonemptyTrueToRet {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {base retPtr value toWord token ret : UInt256}
    {R : List UInt256} {mem0 out : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {aw0 : UInt256}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨6676⟩
      (UInt256.ofNat out.size :: retPtr :: base :: ⟨1⟩ :: value :: toWord :: token ::
        ret :: R)
      mem0 aw0 out acc k C)
    (hout32 : 32 ≤ out.size) (houtSize : out.size < 2 ^ 255)
    (hword : UInt256.ofNat (fromByteArrayBigEndian (out.extract 0 32)) ≠ ⟨0⟩)
    (hloadRet :
      (if retPtr.toNat ≥ mem0.size ∨ retPtr ≥ aw0 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat (fromByteArrayBigEndian (mem0.readWithPadding retPtr.toNat 32))) =
      UInt256.ofNat (fromByteArrayBigEndian (out.extract 0 32)))
    (hawRet : UInt256.ofNat (MachineState.M aw0.toNat retPtr.toNat 32) = aw0)
    (hret : (D_J UniswapV2Pair.uniswapV2PairBytecode 0).contains ret = true)
    (hR : R.length + 16 ≤ 1024) :
    ∃ k' C', RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ret R mem0 aw0 out acc k' C' := by
  have rd6684₀ := evm_run h with [push1 ⟨32⟩, dup2, lt, iszero, push2 ⟨6689⟩]
  have hlt : UInt256.lt (UInt256.ofNat out.size) (⟨32⟩ : UInt256) = ⟨0⟩ := by
    apply Reasoning.Theory.ult_zero
    rw [show (⟨32⟩ : UInt256).toNat = 32 from by decide,
      UInt256.toNat_ofNat_of_lt (lt_size_of_lt_sign houtSize)]
    exact hout32
  have rd6684 := rd6684₀
  rw [hlt, show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rd6684
  have rd6691 := evm_run rd6684 with [jumpiT (by native_decide) (by jump_dest), jumpdest, pop]
  have rd6692 := RD.mload
    0 (UInt256.ofNat (fromByteArrayBigEndian (out.extract 0 32))) aw0
    rd6691 (by native_decide)
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk, hawRet])
    hloadRet hawRet
    (by simp only [List.length_cons]; omega)
  have rd6773 := evm_run rd6692 with [
    jumpdest, push2 ⟨6773⟩, jumpiT hword (by jump_dest)]
  exact ⟨_, _, evm_run rd6773 with [jumpdest, pop, pop, pop, pop, pop, jump hret]⟩

set_option maxHeartbeats 1000000 in
theorem RD.uniswapSafeTransferReturnNonemptyReturnToCheck {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ}
    {status callRetOffset maskedToken value toWord token ret dataPtr finalAw : UInt256}
    {R : List UInt256} {mem0 memFinal out : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {aw0 : UInt256}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨6595⟩
      (status :: callRetOffset :: maskedToken :: ⟨96⟩ :: ⟨0⟩ ::
        value :: toWord :: token :: ret :: R) mem0 aw0 out acc k C)
    (houtNe : out.size ≠ 0) (houtSize : out.size < 2 ^ 255)
    (hloadPtr :
      (if (⟨64⟩ : UInt256).toNat ≥ mem0.size ∨ (⟨64⟩ : UInt256) ≥ aw0 * ⟨32⟩
       then ⟨0⟩
       else UInt256.ofNat
        (fromByteArrayBigEndian (mem0.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
      dataPtr)
    (haw64 : UInt256.ofNat (MachineState.M aw0.toNat (⟨64⟩ : UInt256).toNat 32) = aw0)
    (hawDataPtr : UInt256.ofNat (MachineState.M aw0.toNat dataPtr.toNat 32) = aw0)
    (hmemFinal :
      out.write 0
        ((UInt256.toByteArray (UInt256.ofNat out.size)).write 0
          ((UInt256.toByteArray
            (dataPtr +
              (UInt256.land (UInt256.ofNat out.size + ⟨63⟩)
                (UInt256.lnot ⟨31⟩)))).write 0 mem0 64 32)
          dataPtr.toNat 32)
        ((dataPtr + ⟨32⟩).toNat) out.size =
      memFinal)
    (hawFinal :
      UInt256.ofNat
        (MachineState.M aw0.toNat ((dataPtr + ⟨32⟩).toNat) out.size) =
      finalAw)
    (hR : R.length + 16 ≤ 1024) :
    ∃ k' C', RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨6652⟩
      (dataPtr :: status :: value :: toWord :: token :: ret :: R)
      memFinal finalAw out acc k' C' := by
  let rdsz : UInt256 := UInt256.ofNat out.size
  have hrdsz_toNat : rdsz.toNat = out.size := by
    dsimp [rdsz]
    exact UInt256.toNat_ofNat_of_lt (lt_size_of_lt_sign houtSize)
  have hrdsz_ne : rdsz ≠ ⟨0⟩ := by
    intro hzero
    have hnat : rdsz.toNat = 0 := by rw [hzero]; rfl
    rw [hrdsz_toNat] at hnat
    exact houtNe hnat
  have heq0 : UInt256.eq rdsz (⟨0⟩ : UInt256) = ⟨0⟩ := u256_eq_of_ne hrdsz_ne
  have rd6607 := evm_run h with [
    swap2, pop, pop, returndatasize, dup1, push1 ⟨0⟩, dup2, eq, push2 ⟨6641⟩]
  have rd6608 := rd6607
  change UInt256.eq rdsz (⟨0⟩ : UInt256) = ⟨0⟩ at heq0
  rw [show UInt256.ofNat out.size = rdsz from rfl, heq0] at rd6608
  have rd6610 := evm_run rd6608 with [jumpiNT (by native_decide), push1 ⟨64⟩]
  have rd6611 := RD.mload 0 dataPtr aw0 rd6610 (by native_decide)
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk, haw64])
    hloadPtr haw64
    (by simp only [List.length_cons]; omega)
  let rounded : UInt256 := UInt256.land (rdsz + ⟨63⟩) (UInt256.lnot ⟨31⟩)
  let mem2 : ByteArray := (UInt256.toByteArray (dataPtr + rounded)).write 0
    mem0 64 32
  have rd6625 := evm_run rd6611 with [
    swap2, pop, push1 ⟨31⟩, not, push1 ⟨63⟩, returndatasize, add, and,
    dup3, add, push1 ⟨64⟩]
  have rd6626 := RD.mstore 0 mem2 aw0 rd6625 (by native_decide)
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk, haw64])
    (by
      rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide])
    haw64
    (by simp only [List.length_cons]; omega)
  let mem3 : ByteArray := (UInt256.toByteArray rdsz).write 0 mem2 dataPtr.toNat 32
  have rd6628 := evm_run rd6626 with [returndatasize, dup3]
  have rd6629 := RD.mstore 0 mem3 aw0 rd6628 (by native_decide)
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk, hawDataPtr])
    (by dsimp [mem3])
    hawDataPtr
    (by simp only [List.length_cons]; omega)
  have rd6636 := evm_run rd6629 with [returndatasize, push1 ⟨0⟩, push1 ⟨32⟩, dup5, add]
  let copyDest : UInt256 := dataPtr + ⟨32⟩
  let copyLen : UInt256 := UInt256.ofNat out.size
  have hcopyLen_toNat : copyLen.toNat = out.size := by
    simpa [copyLen] using UInt256.toNat_ofNat_of_lt (lt_size_of_lt_sign houtSize)
  let mem4 : ByteArray := out.write 0 mem3 copyDest.toNat copyLen.toNat
  have hmem4 : mem4 = memFinal := by
    simpa [mem4, mem3, mem2, copyDest, copyLen, rdsz, rounded, hcopyLen_toNat]
      using hmemFinal
  have haw4 :
      UInt256.ofNat (MachineState.M aw0.toNat copyDest.toNat copyLen.toNat) =
        finalAw := by
    simpa [copyDest, copyLen, hcopyLen_toNat] using hawFinal
  have haw4' :
      UInt256.ofNat (MachineState.M aw0.toNat (dataPtr + ⟨32⟩).toNat out.size) =
        finalAw := by
    simpa [copyDest, copyLen, hcopyLen_toNat] using haw4
  have rd6637 := RD.returndatacopy (Cₘ finalAw - Cₘ aw0) mem4 finalAw
    rd6636 (by native_decide)
    (by rw [show (⟨0⟩ : UInt256).toNat = 0 from rfl, hcopyLen_toNat]; omega)
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
      rw [UInt256.toNat_ofNat_of_lt (lt_size_of_lt_sign houtSize), haw4'])
    (by rfl)
    haw4
    (by evm_ov)
  have rd6646 := evm_run rd6637 with [push2 ⟨6646⟩, jump (by jump_dest), jumpdest]
  have rd6652 := evm_run rd6646 with [pop, swap2, pop, swap2, pop]
  rw [hmem4] at rd6652
  exact ⟨_, _, by simpa using rd6652⟩

set_option maxHeartbeats 1000000 in
theorem RD.uniswapSkimSafeTransferNonemptyReturnToCheck {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {self value toWord token token1 ret sel status : UInt256}
    {o out : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨6595⟩
      (status :: ⟨360⟩ :: UInt256.land token solcAddrMask :: ⟨96⟩ :: ⟨0⟩ ::
        value :: toWord :: token :: ret :: token1 :: token :: toWord :: ⟨570⟩ ::
        sel :: [])
      (skimSafeTransferCallMem2 self o toWord value) (UInt256.ofNat 13) out acc k C)
    (houtNe : out.size ≠ 0) (houtSize : out.size < 2 ^ 255)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size) :
    ∃ k' C', RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨6652⟩
      (⟨292⟩ :: status :: value :: toWord :: token :: ret :: token1 :: token :: toWord ::
        ⟨570⟩ :: sel :: [])
      (skimSafeTransferReturnDataMem self o toWord value out)
      (skimSafeTransferReturnDataActiveWords out) out acc k' C' := by
  exact RD.uniswapSafeTransferReturnNonemptyReturnToCheck
    (R := token1 :: token :: toWord :: ⟨570⟩ :: sel :: [])
    h houtNe houtSize
    (skimSafeTransferCallMem2_mload64 self toWord value ho32 hoSize)
    (by native_decide)
    (by native_decide)
    (by
      rw [
        show (UInt256.ofNat out.size + ⟨63⟩) =
          UInt256.add (UInt256.ofNat out.size) ⟨63⟩ from rfl,
        show (⟨292⟩ : UInt256).toNat = 292 from by decide,
        show ((⟨292⟩ : UInt256) + ⟨32⟩).toNat = 324 from by decide]
      rfl)
    (by
      rw [show ((⟨292⟩ : UInt256) + ⟨32⟩).toNat = 324 from by decide]
      rfl)
    (by simp only [List.length_cons, List.length_nil]; omega)
end UniswapV2Pair
