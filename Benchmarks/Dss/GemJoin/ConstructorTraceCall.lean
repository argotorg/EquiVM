import Benchmarks.Dss.GemJoin.ConstructorTraceStores

/-!
# MakerDAO/Sky DSS GemJoin constructor decimals staticcall trace
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Dss.GemJoin

set_option maxRecDepth 2000000

abbrev gemJoinCtorGemTargetOfStored (stored : UInt256) : UInt256 :=
  UInt256.land solcAddrMask stored

theorem gemJoinCtorDecimalsSetupReach
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ σStored σAcc σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g0 : Sat256}
    (vat : AccountAddress) (ilk : UInt256) (gem : AccountAddress) {k C : ℕ}
    (rd141 :
      RD (gemJoinCtorCode vat ilk gem) I g0
        (initState createdAccounts genesisBlockHeader blocks σ σ₀ g0 A I) ⟨141⟩
        [gemJoinCtorGemStored σStored I gem, solcAddrMask, EVM.word gem.val, ilk, ⟨32⟩,
          EVM.word vat.val, ⟨64⟩]
        (gemJoinCtorWardsHashMem I vat ilk gem) (UInt256.ofNat 7) ByteArray.empty
        (createdAccounts, σAcc) k C) :
    ∃ k' C', RD (gemJoinCtorCode vat ilk gem) I g0
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g0 A I) ⟨184⟩
      [gemJoinCtorGemTargetOfStored (gemJoinCtorGemStored σStored I gem),
        gemJoinCtorGemTargetOfStored (gemJoinCtorGemStored σStored I gem),
        ⟨224⟩, ⟨4⟩, ⟨224⟩, ⟨32⟩, ⟨228⟩, ⟨826074471⟩,
        gemJoinCtorGemTargetOfStored (gemJoinCtorGemStored σStored I gem),
        EVM.word gem.val, ilk, EVM.word vat.val]
      (gemJoinCtorDecimalsCalldataMem I vat ilk gem) (UInt256.ofNat 8) ByteArray.empty
      (createdAccounts, σAcc) k' C' := by
  have rd151pre := gem_ctor_run rd141 with [
    dup7,
    raw mload 0 ⟨224⟩ (UInt256.ofNat 7) (by gem_ctor_decode) mem_cost
      (gemJoinCtorWardsHashMem_mload64 I vat ilk gem) (by decide) (by evm_ov),
    push4 ⟨826074471⟩, push1 ⟨224⟩, shl, dup2]
  have rd153 := rd151pre.mstore 3 (gemJoinCtorDecimalsCalldataMem I vat ilk gem)
    (UInt256.ofNat 8) (by gem_ctor_decode) mem_cost (by rfl) (by decide +native) (by evm_ov)
  have hread64 :
      (gemJoinCtorDecimalsCalldataMem I vat ilk gem).readWithPadding 64 32 =
        UInt256.toByteArray ⟨224⟩ := by
    unfold gemJoinCtorDecimalsCalldataMem
    rw [toByteArray_write_read_below_of_gap gemJoinCtorDecimalsSelectorShifted
      (gemJoinCtorWardsHashMem I vat ilk gem) 224 64
      (by rw [gemJoinCtorWardsHashMem_size]; omega)
      (by omega)
      (by rw [gemJoinCtorWardsHashMem_size]; decide +native)]
    exact gemJoinCtorWardsHashMem_read64 I vat ilk gem
  have hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ (gemJoinCtorDecimalsCalldataMem I vat ilk gem).size ∨
          (⟨64⟩ : UInt256) ≥ UInt256.ofNat 8 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
          ((gemJoinCtorDecimalsCalldataMem I vat ilk gem).readWithPadding 64 32))) = ⟨224⟩ := by
    exact mloadWordValue_of_readWithPadding
      (mem := gemJoinCtorDecimalsCalldataMem I vat ilk gem) (aw := UInt256.ofNat 8)
      (off := ⟨64⟩) (v := ⟨224⟩)
      (by rw [gemJoinCtorDecimalsCalldataMem_size]; decide)
      (by decide)
      hread64
  have rd184 := gem_ctor_run rd153 with [
    swap7,
    raw mload 0 ⟨224⟩ (UInt256.ofNat 8) (by gem_ctor_decode) mem_cost
      hmload64 (by decide) (by evm_ov),
    swap6, swap7, swap4, swap6, swap3, swap5, swap2,
    raw and (by gem_ctor_decode) (by evm_ov),
    swap3, push4 ⟨826074471⟩, swap3, push1 ⟨4⟩, dup3, dup2, add, swap4,
    swap3, dup3, swap1, sub, add, dup2, dup7, dup1]
  exact ⟨_, _, by
    simpa [gemJoinCtorGemTargetOfStored, gemJoinCtorDecimalsSelectorShifted,
      show UInt256.shiftLeft (⟨826074471⟩ : UInt256) ⟨224⟩ =
        gemJoinCtorDecimalsSelectorShifted from rfl,
        show (⟨141⟩ : UInt256) + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 5 + UInt256.ofNat 2 +
            ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
            ⟨1⟩ + UInt256.ofNat 5 + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
            ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
            ⟨1⟩ + ⟨1⟩ = ⟨184⟩
        from by decide +native] using rd184⟩

theorem gemJoinCtorDecimalsStaticcallReach
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ σAcc σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g0 : Sat256}
    (vat : AccountAddress) (ilk : UInt256) (gem : AccountAddress) {k C : ℕ}
    (gemTarget : UInt256)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σAcc gemTarget ≠ ⟨0⟩)
    (hdepth : I.depth.val < 1024)
    (rd184 :
      RD (gemJoinCtorCode vat ilk gem) I g0
        (initState createdAccounts genesisBlockHeader blocks σ σ₀ g0 A I) ⟨184⟩
        [gemTarget, gemTarget,
          ⟨224⟩, ⟨4⟩, ⟨224⟩, ⟨32⟩, ⟨228⟩, ⟨826074471⟩,
          gemTarget, EVM.word gem.val, ilk, EVM.word vat.val]
        (gemJoinCtorDecimalsCalldataMem I vat ilk gem) (UInt256.ofNat 8) ByteArray.empty
        (createdAccounts, σAcc) k C) :
    ∃ (createdAccounts' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap)
      (z : Bool) (out : ByteArray) (Ain : Substate) (callGas : UInt256) (k' C' : ℕ),
      (∃ (g'' : UInt256) (A' : Substate),
        (createdAccounts', σ', g'', A', z, out) =
          Ethereum.EVM.Θ I.blobVersionedHashes createdAccounts genesisBlockHeader blocks
            σAcc σ₀ Ain
            (AccountAddress.ofUInt256 (UInt256.ofNat I.codeOwner)) I.sender
            (AccountAddress.ofUInt256 gemTarget)
            (toExecute σAcc (AccountAddress.ofUInt256 gemTarget))
            callGas (UInt256.ofNat I.gasPrice) ⟨0⟩ ⟨0⟩
            ((gemJoinCtorDecimalsCalldataMem I vat ilk gem).readWithPadding 224 4)
            (I.depth + 1) I.header false) ∧
      RD (gemJoinCtorCode vat ilk gem) I g0
        (initState createdAccounts genesisBlockHeader blocks σ σ₀ g0 A I) ⟨200⟩
        ((if z then ⟨1⟩ else ⟨0⟩) :: [⟨228⟩, ⟨826074471⟩,
          gemTarget, EVM.word gem.val, ilk, EVM.word vat.val])
        (out.write 0 (gemJoinCtorDecimalsCalldataMem I vat ilk gem) 224
          (min (⟨32⟩ : UInt256) (UInt256.ofNat out.size)).toNat)
        (UInt256.ofNat
          (MachineState.M
            (MachineState.M (UInt256.ofNat 8).toNat (⟨224⟩ : UInt256).toNat
              (⟨4⟩ : UInt256).toNat)
            (⟨224⟩ : UInt256).toNat (⟨32⟩ : UInt256).toNat))
        out (createdAccounts', σ') k' C' ∧
      out.size < UInt256.size := by
  obtain ⟨gasWord, kGas, CGas, rd199⟩ :=
    RD.solcExtcodesizeGuardOkGas
      (pc := ⟨184⟩) (okPc := ⟨196⟩)
      rd184 hcodeSize
      (by gem_ctor_decode) (by gem_ctor_decode) (by gem_ctor_decode) (by gem_ctor_decode)
      (by gem_ctor_decode) (by gem_ctor_decode) (by gem_ctor_jd)
      (by gem_ctor_decode) (by gem_ctor_decode) (by gem_ctor_decode) (by evm_ov)
  obtain ⟨createdAccounts', σ', z, out, Ain, callGas, k', C', hTheta, rd200, houtSize⟩ :=
    RD.solcStaticcall rd199 (by gem_ctor_decode) hdepth (by evm_ov)
  exact ⟨createdAccounts', σ', z, out, Ain, callGas, k', C', hTheta, by
    simpa [show (⟨199⟩ : UInt256) + ⟨1⟩ = ⟨200⟩ from by decide +native] using rd200,
    houtSize⟩

theorem gemJoinCtorDecimalsStaticcallDepthLimitReach
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ σAcc σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g0 : Sat256}
    (vat : AccountAddress) (ilk : UInt256) (gem : AccountAddress) {k C : ℕ}
    (gemTarget : UInt256)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σAcc gemTarget ≠ ⟨0⟩)
    (hdepth : I.depth = 1024)
    (rd184 :
      RD (gemJoinCtorCode vat ilk gem) I g0
        (initState createdAccounts genesisBlockHeader blocks σ σ₀ g0 A I) ⟨184⟩
        [gemTarget, gemTarget,
          ⟨224⟩, ⟨4⟩, ⟨224⟩, ⟨32⟩, ⟨228⟩, ⟨826074471⟩,
          gemTarget, EVM.word gem.val, ilk, EVM.word vat.val]
        (gemJoinCtorDecimalsCalldataMem I vat ilk gem) (UInt256.ofNat 8) ByteArray.empty
        (createdAccounts, σAcc) k C) :
    ∃ k' C', RD (gemJoinCtorCode vat ilk gem) I g0
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g0 A I) ⟨200⟩
      (⟨0⟩ :: [⟨228⟩, ⟨826074471⟩,
        gemTarget, EVM.word gem.val, ilk, EVM.word vat.val])
      (ByteArray.empty.write 0 (gemJoinCtorDecimalsCalldataMem I vat ilk gem) 224
        (min (⟨32⟩ : UInt256) (UInt256.ofNat ByteArray.empty.size)).toNat)
      (UInt256.ofNat
        (MachineState.M
          (MachineState.M (UInt256.ofNat 8).toNat (⟨224⟩ : UInt256).toNat
            (⟨4⟩ : UInt256).toNat)
          (⟨224⟩ : UInt256).toNat (⟨32⟩ : UInt256).toNat))
      ByteArray.empty (createdAccounts, σAcc) k' C' := by
  obtain ⟨gasWord, kGas, CGas, rd199⟩ :=
    RD.solcExtcodesizeGuardOkGas
      (pc := ⟨184⟩) (okPc := ⟨196⟩)
      rd184 hcodeSize
      (by gem_ctor_decode) (by gem_ctor_decode) (by gem_ctor_decode) (by gem_ctor_decode)
      (by gem_ctor_decode) (by gem_ctor_decode) (by gem_ctor_jd)
      (by gem_ctor_decode) (by gem_ctor_decode) (by gem_ctor_decode) (by evm_ov)
  obtain ⟨k', C', rd200⟩ :=
    RD.solcStaticcallDepthLimit rd199 (by gem_ctor_decode) hdepth (by evm_ov)
  exact ⟨k', C', by
    simpa [show (⟨199⟩ : UInt256) + ⟨1⟩ = ⟨200⟩ from by decide +native]
      using rd200⟩

theorem gemJoinCtorDecimalsNoCodeReverts
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ σAcc σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g0 : Sat256}
    (vat : AccountAddress) (ilk : UInt256) (gem : AccountAddress) {k C : ℕ}
    (gemTarget : UInt256)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σAcc gemTarget = ⟨0⟩)
    (rd184 :
      RD (gemJoinCtorCode vat ilk gem) I g0
        (initState createdAccounts genesisBlockHeader blocks σ σ₀ g0 A I) ⟨184⟩
        [gemTarget, gemTarget,
          ⟨224⟩, ⟨4⟩, ⟨224⟩, ⟨32⟩, ⟨228⟩, ⟨826074471⟩,
          gemTarget, EVM.word gem.val, ilk, EVM.word vat.val]
        (gemJoinCtorDecimalsCalldataMem I vat ilk gem) (UInt256.ofNat 8) ByteArray.empty
        (createdAccounts, σAcc) k C) :
    RDrev (gemJoinCtorCode vat ilk gem) g0
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g0 A I) := by
  exact RD.solcExtcodesizeGuardMissing
    (pc := ⟨184⟩) (okPc := ⟨196⟩)
    rd184 hcodeSize
    (by gem_ctor_decode) (by gem_ctor_decode) (by gem_ctor_decode) (by gem_ctor_decode)
    (by gem_ctor_decode) (by gem_ctor_decode)
    (by gem_ctor_decode) (by gem_ctor_decode) (by gem_ctor_decode)
    (by simp only [List.length_cons, List.length_nil]; omega)

abbrev gemJoinCtorDecimalsReturnWord (out : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (out.extract 0 32))

theorem byteArray_toList_toByteArray_gemJoin (b : ByteArray) :
    b.toList.toByteArray = b := by
  apply ByteArray.ext
  apply Array.toList_inj.mp
  rw [byteArray_toList_eq]
  simp

theorem toByteArray_uInt256OfByteArray_of_size_gemJoin {arr : ByteArray}
    (hsize : arr.size = 32) :
    UInt256.toByteArray (uInt256OfByteArray arr) = arr := by
  rw [← word_toBytesBE_toByteArray_eq_toByteArray (uInt256OfByteArray arr),
    toBytesBE_uInt256OfByteArray_of_size hsize, byteArray_toList_toByteArray_gemJoin]

theorem gemJoinCtorMin32_toNat_of_ge {n : ℕ}
    (h32 : 32 ≤ n) (hsize : n < UInt256.size) :
    (min (⟨32⟩ : UInt256) (UInt256.ofNat n)).toNat = 32 := by
  show (if (⟨32⟩ : UInt256) ≤ UInt256.ofNat n then (⟨32⟩ : UInt256)
    else UInt256.ofNat n).toNat = 32
  rw [if_pos]
  · rfl
  · show (32 : ℕ) ≤ (UInt256.ofNat n).val.val
    rw [show (UInt256.ofNat n).val.val = (UInt256.ofNat n).toNat from rfl,
      ulit_toNat' n hsize]
    exact h32

theorem gemJoinCtorMin32_toNat_of_lt {n : ℕ} (h : n < 32) :
    (min (⟨32⟩ : UInt256) (UInt256.ofNat n)).toNat = n := by
  show (if (⟨32⟩ : UInt256) ≤ UInt256.ofNat n then (⟨32⟩ : UInt256)
    else UInt256.ofNat n).toNat = n
  have hnsize : n < UInt256.size := by
    have h32 : 32 < UInt256.size := by norm_num [UInt256.size]
    omega
  rw [if_neg, ulit_toNat' n hnsize]
  · show ¬ (32 : ℕ) ≤ (UInt256.ofNat n).val.val
    rw [show (UInt256.ofNat n).val.val = (UInt256.ofNat n).toNat from rfl,
      ulit_toNat' n hnsize]
    omega

theorem gemJoinCtorDecimalsReturnWrite_read64 {base out : ByteArray} (L : ℕ)
    (hbase : base.size = 256)
    (hread64 : base.readWithPadding 64 32 = UInt256.toByteArray ⟨224⟩)
    (hL : L ≤ 32) (hLo : L ≤ out.size) :
    (out.write 0 base 224 L).readWithPadding 64 32 = UInt256.toByteArray ⟨224⟩ := by
  rcases Nat.eq_zero_or_pos L with h | h
  · subst h
    rw [byteArray_write_len_zero]
    exact hread64
  · rw [write_read_below_gen out base 224 L 64 (by omega) hLo
      (by rw [hbase]; omega) (by omega), hread64]

theorem gemJoinCtorDecimalsReturnWrite_size {base out : ByteArray} (L : ℕ)
    (hbase : base.size = 256) (hL : L ≤ 32) (hLo : L ≤ out.size) :
    (out.write 0 base 224 L).size = 256 := by
  rcases Nat.eq_zero_or_pos L with h | h
  · subst h
    rw [byteArray_write_len_zero]
    exact hbase
  · rw [write_eq_gen out base 224 L (by omega) hLo (by rw [hbase]; omega),
      ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
      ByteArray.size_extract, ByteArray.size_extract, hbase]
    omega

theorem gemJoinCtorDecimalsReturnWrite_read224_32 {base out : ByteArray}
    (hbase : base.size = 256) (ho32 : 32 ≤ out.size) :
    (out.write 0 base 224 32).readWithPadding 224 32 =
      out.extract 0 32 :=
  write32_read_back out base 224 ho32 (by rw [hbase]; omega)

theorem gemJoinCtorDecimalsStatusOkReach
    {s0 : State} {I : ExecutionEnv} {g0 : Sat256}
    (vat : AccountAddress) (ilk : UInt256) (gem : AccountAddress)
    (gemTarget : UInt256) {mem out : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {z : Bool} {k C : ℕ}
    (hz : z = true)
    (rd200 :
      RD (gemJoinCtorCode vat ilk gem) I g0 s0 ⟨200⟩
        ((if z then ⟨1⟩ else ⟨0⟩) :: [⟨228⟩, ⟨826074471⟩,
          gemTarget, EVM.word gem.val, ilk, EVM.word vat.val])
        mem aw out acc k C) :
    ∃ k' C', RD (gemJoinCtorCode vat ilk gem) I g0 s0 ⟨218⟩
      [⟨228⟩, ⟨826074471⟩, gemTarget, EVM.word gem.val, ilk, EVM.word vat.val]
      mem aw out acc k' C' := by
  subst z
  exact RD.solcCallSuccessGuardOk
    (pc := ⟨200⟩) (okPc := ⟨216⟩) rd200
    (by decide)
    (by gem_ctor_decode) (by gem_ctor_decode) (by gem_ctor_decode)
    (by gem_ctor_decode) (by gem_ctor_decode) (by gem_ctor_jd)
    (by gem_ctor_decode) (by gem_ctor_decode)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem gemJoinCtorDecimalsStatusFailReverts
    {s0 : State} {I : ExecutionEnv} {g0 : Sat256}
    (vat : AccountAddress) (ilk : UInt256) (gem : AccountAddress)
    (gemTarget : UInt256) {mem out : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {z : Bool} {k C : ℕ}
    (hz : z = false) (houtSize : out.size < UInt256.size)
    (rd200 :
      RD (gemJoinCtorCode vat ilk gem) I g0 s0 ⟨200⟩
        ((if z then ⟨1⟩ else ⟨0⟩) :: [⟨228⟩, ⟨826074471⟩,
          gemTarget, EVM.word gem.val, ilk, EVM.word vat.val])
        mem aw out acc k C) :
    RDrev (gemJoinCtorCode vat ilk gem) g0 s0 := by
  subst z
  exact RD.solcCallSuccessGuardMissing
    (pc := ⟨200⟩) (okPc := ⟨216⟩) rd200 rfl
    (by gem_ctor_decode) (by gem_ctor_decode) (by gem_ctor_decode)
    (by gem_ctor_decode) (by gem_ctor_decode) (by gem_ctor_decode)
    (by gem_ctor_decode) (by gem_ctor_decode) (by gem_ctor_decode)
    (by gem_ctor_decode) (by gem_ctor_decode) (by gem_ctor_decode)
    houtSize (by simp only [List.length_cons, List.length_nil]; omega)

set_option maxHeartbeats 2000000 in
theorem gemJoinCtorDecimalsReturnDecodeOkReach
    {s0 : State} {I : ExecutionEnv} {g0 : Sat256}
    (vat : AccountAddress) (ilk : UInt256) (gem : AccountAddress)
    (gemTarget retWord : UInt256) {mem out : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (hlo : 32 ≤ out.size) (hhi : out.size < UInt256.size)
    (hMload64Cost :
      ∀ s : State, s.machineState.activeWords = aw →
        s.machineState.stack =
          (⟨64⟩ : UInt256) :: [EVM.word gem.val, ilk, EVM.word vat.val] →
        memoryExpansionCost s .MLOAD = 0)
    (hMload64Aw : UInt256.ofNat (MachineState.M aw.toNat 64 32) = aw)
    (hMload64Value :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨224⟩)
    (hMload224Value :
      (if (⟨224⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨224⟩ : UInt256) ≥ aw * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (mem.readWithPadding (⟨224⟩ : UInt256).toNat 32))) =
        retWord)
    (hMload224Cost :
      ∀ s : State, s.machineState.activeWords = aw →
        s.machineState.stack =
          (⟨224⟩ : UInt256) :: [EVM.word gem.val, ilk, EVM.word vat.val] →
        memoryExpansionCost s .MLOAD = 0)
    (hMload224Aw : UInt256.ofNat (MachineState.M aw.toNat 224 32) = aw)
    (rd218 :
      RD (gemJoinCtorCode vat ilk gem) I g0 s0 ⟨218⟩
        [⟨228⟩, ⟨826074471⟩, gemTarget, EVM.word gem.val, ilk, EVM.word vat.val]
        mem aw out acc k C) :
    ∃ k' C', RD (gemJoinCtorCode vat ilk gem) I g0 s0 ⟨241⟩
      [retWord, EVM.word gem.val, ilk, EVM.word vat.val]
      mem aw out acc k' C' := by
  have rdPop0 := RD.pop rd218 (by gem_ctor_decode)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdPop1 := RD.pop rdPop0 (by gem_ctor_decode)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdPop2 := RD.pop rdPop1 (by gem_ctor_decode)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdPush64 := RD.push1 rdPop2 ⟨64⟩ (by gem_ctor_decode)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdMload64 := RD.mload 0 ⟨224⟩ aw rdPush64 (by gem_ctor_decode)
    hMload64Cost hMload64Value hMload64Aw
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdReturndatasize := RD.returndatasize rdMload64 (by gem_ctor_decode)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdPush32 := RD.push1 rdReturndatasize ⟨32⟩ (by gem_ctor_decode)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdDup2 := RD.dup2 rdPush32 (by gem_ctor_decode)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdLt := RD.lt rdDup2 (by gem_ctor_decode)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have hlt : UInt256.lt (UInt256.ofNat out.size) (⟨32⟩ : UInt256) = ⟨0⟩ := by
    apply Reasoning.Theory.ult_zero
    rw [show (⟨32⟩ : UInt256).toNat = 32 from by decide, ulit_toNat' out.size hhi]
    exact hlo
  have rdIszero := RD.iszero rdLt (by gem_ctor_decode)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdPushOk := RD.push2 rdIszero ⟨238⟩ (by gem_ctor_decode)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have hcond :
      UInt256.isZero (UInt256.lt (UInt256.ofNat out.size) (⟨32⟩ : UInt256)) ≠ ⟨0⟩ := by
    rw [hlt]
    decide
  have rdJumpi := RD.jumpiT rdPushOk (by gem_ctor_decode) hcond (by gem_ctor_jd)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdJumpdest := RD.jumpdest rdJumpi (by gem_ctor_decode)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdPopLen := RD.pop rdJumpdest (by gem_ctor_decode)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdMload224 := RD.mload 0 retWord aw rdPopLen (by gem_ctor_decode)
    hMload224Cost hMload224Value hMload224Aw
    (by simp only [List.length_cons, List.length_nil]; omega)
  exact ⟨_, _, by
    simpa [show (⟨238⟩ : UInt256) + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ = ⟨241⟩ from by decide +native]
      using rdMload224⟩

set_option maxHeartbeats 2000000 in
theorem gemJoinCtorDecimalsReturnDecodeShortReverts
    {s0 : State} {I : ExecutionEnv} {g0 : Sat256}
    (vat : AccountAddress) (ilk : UInt256) (gem : AccountAddress)
    (gemTarget : UInt256) {mem out : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (hshort : out.size < 32) (hhi : out.size < UInt256.size)
    (hMload64Cost :
      ∀ s : State, s.machineState.activeWords = aw →
        s.machineState.stack =
          (⟨64⟩ : UInt256) :: [EVM.word gem.val, ilk, EVM.word vat.val] →
        memoryExpansionCost s .MLOAD = 0)
    (hMload64Aw : UInt256.ofNat (MachineState.M aw.toNat 64 32) = aw)
    (hMload64Value :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨224⟩)
    (rd218 :
      RD (gemJoinCtorCode vat ilk gem) I g0 s0 ⟨218⟩
        [⟨228⟩, ⟨826074471⟩, gemTarget, EVM.word gem.val, ilk, EVM.word vat.val]
        mem aw out acc k C) :
    RDrev (gemJoinCtorCode vat ilk gem) g0 s0 := by
  have rdPop0 := RD.pop rd218 (by gem_ctor_decode)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdPop1 := RD.pop rdPop0 (by gem_ctor_decode)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdPop2 := RD.pop rdPop1 (by gem_ctor_decode)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdPush64 := RD.push1 rdPop2 ⟨64⟩ (by gem_ctor_decode)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdMload64 := RD.mload 0 ⟨224⟩ aw rdPush64 (by gem_ctor_decode)
    hMload64Cost hMload64Value hMload64Aw
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdReturndatasize := RD.returndatasize rdMload64 (by gem_ctor_decode)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdPush32 := RD.push1 rdReturndatasize ⟨32⟩ (by gem_ctor_decode)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdDup2 := RD.dup2 rdPush32 (by gem_ctor_decode)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdLt := RD.lt rdDup2 (by gem_ctor_decode)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have hlt : UInt256.lt (UInt256.ofNat out.size) (⟨32⟩ : UInt256) = ⟨1⟩ := by
    apply Reasoning.Theory.ult_one
    rw [show (⟨32⟩ : UInt256).toNat = 32 from by decide, ulit_toNat' out.size hhi]
    exact hshort
  have rdIszero := RD.iszero rdLt (by gem_ctor_decode)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdPushOk := RD.push2 rdIszero ⟨238⟩ (by gem_ctor_decode)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have hcond :
      UInt256.isZero (UInt256.lt (UInt256.ofNat out.size) (⟨32⟩ : UInt256)) = ⟨0⟩ := by
    rw [hlt]
    decide
  have rdFallthrough := RD.jumpiNT rdPushOk (by gem_ctor_decode) hcond
    (by simp only [List.length_cons, List.length_nil]; omega)
  exact RD.solcPush1Dup1Revert0 rdFallthrough
    (by gem_ctor_decode) (by gem_ctor_decode) (by gem_ctor_decode)
    (by simp only [List.length_cons, List.length_nil]; omega)

end Benchmarks.Dss.GemJoin
