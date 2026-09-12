import Benchmarks.Dss.Clipper.ConstructorBase

/-!
# MakerDAO/Sky DSS Clipper constructor creation-bytecode trace
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Dss.Clipper

set_option maxRecDepth 2000000
set_option maxHeartbeats 2000000

abbrev clipperCtorRelyLogTopic : UInt256 :=
  ⟨0xdd0e34038ac38b2a1ce960229778ac48a8719bc900b6c4f8d0475c6e8b385a60⟩

theorem RDret.xiResultAcc {cA gh bl σ σ₀ A I} {g : Sat256} {code o : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (hcode : I.code = code)
    (h : RDret code g (initState cA gh bl σ σ₀ g A I) acc o) :
    Ξ cA gh bl σ σ₀ g.toUInt256 A I = .error .OutOfGass ∨
      ∃ (g' : UInt256) (A' : Substate),
        Ξ cA gh bl σ σ₀ g.toUInt256 A I =
          .ok (.success (acc.1, acc.2, g', A') o) := by
  rcases h with hOOG | ⟨s, hX, hacc⟩
  · exact Or.inl (Xi_error_of_X (g := g.toUInt256) (by
      rw [← hcode] at hOOG
      simpa [initState, Sat256.ofUInt256, Sat256.toUInt256] using hOOG))
  · have hcA : s.createdAccounts = acc.1 := congrArg Prod.fst hacc
    have hσ : s.accountMap = acc.2 := congrArg Prod.snd hacc
    have hxi := Xi_success_of_X (g := g.toUInt256) (by
      rw [← hcode] at hX
      simpa [initState, Sat256.ofUInt256, Sat256.toUInt256] using hX)
    rw [hcA, hσ] at hxi
    exact Or.inr ⟨_, _, hxi⟩

theorem clipperCtorSetAddressWord_eq (old data : UInt256) :
    UInt256.lor (UInt256.land data solcAddrMask)
        (UInt256.land (UInt256.lnot solcAddrMask) old) =
      setAddressOffset0Word old data := by
  calc
    UInt256.lor (UInt256.land data solcAddrMask)
        (UInt256.land (UInt256.lnot solcAddrMask) old) =
        UInt256.lor (UInt256.land data solcAddrMask)
          (UInt256.land old (UInt256.lnot solcAddrMask)) := by
            rw [u256_land_comm (UInt256.lnot solcAddrMask) old]
    _ = UInt256.lor (UInt256.land old (UInt256.lnot solcAddrMask))
          (UInt256.land data solcAddrMask) := u256_lor_comm _ _
    _ = setAddressOffset0Word old data := rfl

theorem clipperCtorStoppedReach
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : Sat256}
    (vat spotter dog : AccountAddress) (ilk : List UInt8)
    (hcode : I.code = clipperCtorCode vat spotter dog ilk) (hperm : I.perm = true) :
    ∃ k C, RD (clipperCtorCode vat spotter dog ilk) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨10⟩ []
      clipperCtorFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (createdAccounts, sstoreAccountMap I.codeOwner σ ⟨14⟩ ⟨0⟩) k C := by
  have rd0 : RD (clipperCtorCode vat spotter dog ilk) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨0⟩ []
      ByteArray.empty (UInt256.ofNat 0) ByteArray.empty (createdAccounts, σ) 0 0 :=
    RD.initState hcode
  have rdBeforeStore := clipper_ctor_run rd0 with [
    push1 ⟨192⟩, push1 ⟨64⟩,
    raw mstore 9 clipperCtorFreePtrMem (UInt256.ofNat 3)
      (by clipper_ctor_decode) mem_cost
      (by
        unfold clipperCtorFreePtrMem Reasoning.Theory.writeWord
        rw [show (⟨64⟩ : UInt256).toNat = 64 by decide])
      (by decide) (by evm_ov),
    push1 ⟨0⟩, push1 ⟨14⟩]
  obtain ⟨k, C, rd10⟩ := rdBeforeStore.sstore hperm (by clipper_ctor_decode) (by evm_ov)
  exact ⟨k, C, by simpa using rd10⟩

theorem clipperInitcodeNonpayableRevert
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : Sat256}
    (vat spotter dog : AccountAddress) (ilk : List UInt8)
    (hcode : I.code = clipperCtorCode vat spotter dog ilk)
    (hperm : I.perm = true) (hwv : I.weiValue ≠ ⟨0⟩) :
    RDrev (clipperCtorCode vat spotter dog ilk) g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) := by
  obtain ⟨_, _, rd10⟩ := clipperCtorStoppedReach
    (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
    (blocks := blocks) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    vat spotter dog ilk hcode hperm
  have rd17 := clipper_ctor_run rd10 with [
    callvalue, dup1, iszero, push2 ⟨21⟩, jumpiNT (isZero_eq_zero_of_ne hwv)]
  exact clipper_ctor_run rd17 with [
    push1 ⟨0⟩, dup1,
    raw rev 0 (by clipper_ctor_decode) mem_cost (by evm_ov)]

theorem clipperCtorArgsReach
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : Sat256}
    (vat spotter dog : AccountAddress) (ilk : List UInt8) (hilk : ilk.length = 32)
    (hcode : I.code = clipperCtorCode vat spotter dog ilk)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩) :
    ∃ k C, RD (clipperCtorCode vat spotter dog ilk) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨78⟩
      [ABI.bytesToWord ilk, EVM.word dog.val, ⟨64⟩, EVM.word spotter.val,
        ⟨32⟩, EVM.word vat.val, ⟨96⟩]
      (clipperCtorArgFreeMem vat spotter dog ilk) (UInt256.ofNat 10) ByteArray.empty
      (createdAccounts, sstoreAccountMap I.codeOwner σ ⟨14⟩ ⟨0⟩) k C := by
  obtain ⟨_, _, rd10⟩ := clipperCtorStoppedReach
    (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
    (blocks := blocks) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    vat spotter dog ilk hcode hperm
  have rd23 := clipper_ctor_run rd10 with [
    callvalue, dup1, iszero, push2 ⟨21⟩,
    jumpiT (by rw [hwv]; decide) (by clipper_ctor_jd), jumpdest, pop]
  have hcopy : (clipperCtorCode vat spotter dog ilk).write 9707
      clipperCtorFreePtrMem 192 128 = clipperCtorArgMem vat spotter dog ilk := rfl
  have hfree :
      (((UInt256.ofNat (clipperCtorCode vat spotter dog ilk).size).sub ⟨9707⟩ +
          (⟨192⟩ : UInt256)).toByteArray).write
          0 (clipperCtorArgMem vat spotter dog ilk) 64 32 =
        clipperCtorArgFreeMem vat spotter dog ilk := by
    rw [clipperCtorArgLen_eq _ _ _ _ hilk]
    rfl
  have rd43 := clipper_ctor_run rd23 with [
    push1 ⟨64⟩,
    raw mload 0 ⟨192⟩ (UInt256.ofNat 3) (by clipper_ctor_decode)
      mem_cost clipperCtorFreePtrMem_mload64 (by decide) (by evm_ov),
    push2 ⟨9707⟩, codesize, sub, dup1, push2 ⟨9707⟩, dup4,
    raw codecopy 21 (clipperCtorArgMem vat spotter dog ilk) (UInt256.ofNat 10)
      (by clipper_ctor_decode)
      (fun s haws hstks => by
        simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstks,
          List.getElem!_cons_zero, List.getElem!_cons_succ]
        rw [clipperCtorArgLen_eq _ _ _ _ hilk]
        decide)
      (by
        rw [show ((UInt256.ofNat (clipperCtorCode vat spotter dog ilk).size).sub
          (⟨9707⟩ : UInt256)).toNat = 128 by
            rw [clipperCtorCode_size _ _ _ _ hilk]
            decide]
        exact hcopy)
      (by rw [clipperCtorCode_size _ _ _ _ hilk]; decide) (by evm_ov),
    dup2, dup2, add, push1 ⟨64⟩,
    raw mstore 0 (clipperCtorArgFreeMem vat spotter dog ilk) (UInt256.ofNat 10)
      (by clipper_ctor_decode) mem_cost
      hfree
      (by decide) (by evm_ov)]
  have rdBeforeJump := clipper_ctor_run rd43 with [
    push1 ⟨128⟩, dup2, lt, iszero, push2 ⟨56⟩]
  have rd56 := rdBeforeJump.jumpiT (by clipper_ctor_decode)
    (by rw [clipperCtorArgLen_eq _ _ _ _ hilk]; decide)
    (by clipper_ctor_jd) (by evm_ov)
  have rd58 := clipper_ctor_run rd56 with [jumpdest, pop]
  have rd78 := clipper_ctor_run rd58 with [
    dup1,
    raw mload 0 (EVM.word vat.val) (UInt256.ofNat 10)
      (by clipper_ctor_decode) mem_cost
      (clipperCtorArgFreeMem_mload192 vat spotter dog ilk hilk) (by decide) (by evm_ov),
    push1 ⟨32⟩, dup1, dup4, add,
    raw mload 0 (EVM.word spotter.val) (UInt256.ofNat 10)
      (by clipper_ctor_decode) mem_cost
      (clipperCtorArgFreeMem_mload224 vat spotter dog ilk hilk) (by decide) (by evm_ov),
    push1 ⟨64⟩, dup1, dup6, add,
    raw mload 0 (EVM.word dog.val) (UInt256.ofNat 10)
      (by clipper_ctor_decode) mem_cost
      (clipperCtorArgFreeMem_mload256 vat spotter dog ilk hilk) (by decide) (by evm_ov),
    push1 ⟨96⟩, swap6, dup7, add,
    raw mload 0 (ABI.bytesToWord ilk) (UInt256.ofNat 10)
      (by clipper_ctor_decode) mem_cost
      (clipperCtorArgFreeMem_mload288 vat spotter dog ilk hilk) (by decide) (by evm_ov)]
  exact ⟨_, _, rd78⟩

theorem clipperCtorVatDecodeReach
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ σStopped σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : Sat256}
    (vat spotter dog : AccountAddress) (ilk : List UInt8) {k C : Nat}
    (rd78 : RD (clipperCtorCode vat spotter dog ilk) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨78⟩
      [ABI.bytesToWord ilk, EVM.word dog.val, ⟨64⟩, EVM.word spotter.val,
        ⟨32⟩, EVM.word vat.val, ⟨96⟩]
      (clipperCtorArgFreeMem vat spotter dog ilk) (UInt256.ofNat 10) ByteArray.empty
      (createdAccounts, σStopped) k C) :
    ∃ k' C', RD (clipperCtorCode vat spotter dog ilk) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨95⟩
      [EVM.word dog.val, ⟨64⟩, EVM.word spotter.val, ⟨32⟩,
        EVM.word vat.val, ABI.bytesToWord ilk]
      (clipperCtorVatMem vat spotter dog ilk) (UInt256.ofNat 10) ByteArray.empty
      (createdAccounts, σStopped) k' C' := by
  have hvatmem :
      (UInt256.land
          (UInt256.lnot (UInt256.sub
            (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨96⟩) ⟨1⟩))
          (UInt256.shiftLeft (EVM.word vat.val) ⟨96⟩)).toByteArray.write
          0 (clipperCtorArgFreeMem vat spotter dog ilk) (⟨160⟩ : UInt256).toNat 32 =
        clipperCtorVatMem vat spotter dog ilk := by
    rw [u256_land_comm]
    rw [show (⟨160⟩ : UInt256).toNat = 160 by decide]
    exact clipperCtorVatMem_mstore160 vat spotter dog ilk
  have rd94 := clipper_ctor_run rd78 with [
    swap6, dup6, swap1, shl, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨96⟩, shl, sub,
    not, and, push1 ⟨160⟩]
  have rd95 := rd94.mstore 0 (clipperCtorVatMem vat spotter dog ilk)
    (UInt256.ofNat 10) (by clipper_ctor_decode) mem_cost hvatmem
    (by decide) (by evm_ov)
  exact ⟨_, _, rd95⟩

theorem clipperCtorSpotterStoreReach
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ σStopped σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : Sat256}
    (vat spotter dog : AccountAddress) (ilk : List UInt8) {k C : Nat}
    (hperm : I.perm = true)
    (rd95 : RD (clipperCtorCode vat spotter dog ilk) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨95⟩
      [EVM.word dog.val, ⟨64⟩, EVM.word spotter.val, ⟨32⟩,
        EVM.word vat.val, ABI.bytesToWord ilk]
      (clipperCtorVatMem vat spotter dog ilk) (UInt256.ofNat 10) ByteArray.empty
      (createdAccounts, σStopped) k C) :
    ∃ k' C', RD (clipperCtorCode vat spotter dog ilk) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨129⟩
      [UInt256.lnot solcAddrMask, solcAddrMask, EVM.word dog.val, ⟨64⟩,
        EVM.word spotter.val, ⟨32⟩, EVM.word vat.val, ABI.bytesToWord ilk]
      (clipperCtorVatMem vat spotter dog ilk) (UInt256.ofNat 10) ByteArray.empty
      (createdAccounts, sstoreAccountMap I.codeOwner σStopped ⟨3⟩
        (setAddressOffset0Word (solcSlotWord σStopped I ⟨3⟩)
          (EVM.word spotter.val))) k' C' := by
  have rdBeforeSload := clipper_ctor_run rd95 with [push1 ⟨3⟩, dup1]
  obtain ⟨k99, C99, rd99raw⟩ := rdBeforeSload.sload (by clipper_ctor_decode) (by evm_ov)
  have rd99 : RD (clipperCtorCode vat spotter dog ilk) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨99⟩
      [solcSlotWord σStopped I ⟨3⟩, ⟨3⟩, EVM.word dog.val, ⟨64⟩,
        EVM.word spotter.val, ⟨32⟩, EVM.word vat.val, ABI.bytesToWord ilk]
      (clipperCtorVatMem vat spotter dog ilk) (UInt256.ofNat 10) ByteArray.empty
      (createdAccounts, σStopped) k99 C99 := by
    simpa [solcSlotWord] using rd99raw
  have rdBeforeStore := clipper_ctor_run rd99 with [
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, not, swap1, dup2, and,
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup1, dup8, and,
    swap2, swap1, swap2, or, swap1, swap3]
  obtain ⟨k', C', rd129raw⟩ := rdBeforeStore.sstore hperm
    (by clipper_ctor_decode) (by evm_ov)
  exact ⟨k', C', by
    simpa [clipperCtorSetAddressWord_eq,
      show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
        solcAddrMask by decide] using rd129raw⟩

theorem clipperCtorDogStoreReach
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ σSpotter σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : Sat256}
    (vat spotter dog : AccountAddress) (ilk : List UInt8) {k C : Nat}
    (hperm : I.perm = true)
    (rd129 : RD (clipperCtorCode vat spotter dog ilk) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨129⟩
      [UInt256.lnot solcAddrMask, solcAddrMask, EVM.word dog.val, ⟨64⟩,
        EVM.word spotter.val, ⟨32⟩, EVM.word vat.val, ABI.bytesToWord ilk]
      (clipperCtorVatMem vat spotter dog ilk) (UInt256.ofNat 10) ByteArray.empty
      (createdAccounts, σSpotter) k C) :
    ∃ k' C', RD (clipperCtorCode vat spotter dog ilk) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨145⟩
      [⟨1⟩, EVM.word dog.val, ⟨64⟩, EVM.word spotter.val, ⟨32⟩,
        EVM.word vat.val, ABI.bytesToWord ilk]
      (clipperCtorVatMem vat spotter dog ilk) (UInt256.ofNat 10) ByteArray.empty
      (createdAccounts, sstoreAccountMap I.codeOwner σSpotter ⟨1⟩
        (setAddressOffset0Word (solcSlotWord σSpotter I ⟨1⟩)
          (EVM.word dog.val))) k' C' := by
  have rdBeforeSload := clipper_ctor_run rd129 with [push1 ⟨1⟩, dup1]
  obtain ⟨k133, C133, rd133raw⟩ := rdBeforeSload.sload (by clipper_ctor_decode) (by evm_ov)
  have rd133 : RD (clipperCtorCode vat spotter dog ilk) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨133⟩
      [solcSlotWord σSpotter I ⟨1⟩, ⟨1⟩, UInt256.lnot solcAddrMask,
        solcAddrMask, EVM.word dog.val, ⟨64⟩, EVM.word spotter.val, ⟨32⟩,
        EVM.word vat.val, ABI.bytesToWord ilk]
      (clipperCtorVatMem vat spotter dog ilk) (UInt256.ofNat 10) ByteArray.empty
      (createdAccounts, σSpotter) k133 C133 := by
    simpa [solcSlotWord] using rd133raw
  have rdBeforeStore := clipper_ctor_run rd133 with [
    swap1, swap2, and, swap2, dup4, and, swap2, swap1, swap2, or, dup2]
  obtain ⟨k', C', rd145raw⟩ := rdBeforeStore.sstore hperm
    (by clipper_ctor_decode) (by evm_ov)
  exact ⟨k', C', by
    simpa [clipperCtorSetAddressWord_eq] using rd145raw⟩

theorem clipperCtorBufWardsReach
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ σDog σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : Sat256}
    (vat spotter dog : AccountAddress) (ilk : List UInt8) (hilk : ilk.length = 32)
    {k C : Nat} (hperm : I.perm = true)
    (rd145 : RD (clipperCtorCode vat spotter dog ilk) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨145⟩
      [⟨1⟩, EVM.word dog.val, ⟨64⟩, EVM.word spotter.val, ⟨32⟩,
        EVM.word vat.val, ABI.bytesToWord ilk]
      (clipperCtorVatMem vat spotter dog ilk) (UInt256.ofNat 10) ByteArray.empty
      (createdAccounts, σDog) k C) :
    ∃ k' C', RD (clipperCtorCode vat spotter dog ilk) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨183⟩
      [solcSourceWord I, EVM.word dog.val, ⟨64⟩, EVM.word spotter.val,
        ⟨0⟩, EVM.word vat.val, ABI.bytesToWord ilk]
      (clipperCtorWardsHashMem I vat spotter dog ilk) (UInt256.ofNat 10) ByteArray.empty
      (createdAccounts,
        sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner σDog ⟨5⟩ clipperCtorRayWord)
          (clipperCtorCallerWardsSlot I) ⟨1⟩) k' C' := by
  have hilkmem :
      (ABI.bytesToWord ilk).toByteArray.write 0
          (clipperCtorVatMem vat spotter dog ilk) (⟨128⟩ : UInt256).toNat 32 =
        clipperCtorIlkMem vat spotter dog ilk := by
    rw [show (⟨128⟩ : UInt256).toNat = 128 by decide]
    rfl
  have rd149 : RD (clipperCtorCode vat spotter dog ilk) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨149⟩
      [⟨128⟩, ABI.bytesToWord ilk, ⟨1⟩, EVM.word dog.val, ⟨64⟩,
        EVM.word spotter.val, ⟨32⟩, EVM.word vat.val, ABI.bytesToWord ilk]
      (clipperCtorVatMem vat spotter dog ilk) (UInt256.ofNat 10) ByteArray.empty
      (createdAccounts, σDog) (k + 3) (C + 9) := by
    simpa using clipper_ctor_run rd145 with [push1 ⟨128⟩, dup8, swap1]
  have rd150 := rd149.mstore 0 (clipperCtorIlkMem vat spotter dog ilk)
    (UInt256.ofNat 10) (by clipper_ctor_decode) mem_cost hilkmem
    (by decide) (by evm_ov)
  have rd163 := rd150.pushConst clipperCtorRayWord (width := 12) (op := .PUSH12)
    (by decide) (by clipper_ctor_decode) (by evm_ov)
  have rdBeforeBuf := clipper_ctor_run rd163 with [push1 ⟨5⟩]
  obtain ⟨k166, C166, rd166⟩ := rdBeforeBuf.sstore hperm
    (by clipper_ctor_decode) (by evm_ov)
  have rdBeforeHash := clipper_ctor_run rd166 with [
    caller, push1 ⟨0⟩, dup2, dup2,
    raw mstore 0 (wordAt0Mem (solcSourceWord I)
        (clipperCtorIlkMem vat spotter dog ilk)) (UInt256.ofNat 10)
      (by clipper_ctor_decode) mem_cost rfl (by decide) (by evm_ov),
    swap6, dup7, swap1,
    raw mstore 0 (clipperCtorWardsHashMem I vat spotter dog ilk) (UInt256.ofNat 10)
      (by clipper_ctor_decode) mem_cost rfl (by decide) (by evm_ov),
    dup4, dup7]
  have rdSlot := rdBeforeHash.keccak256 0 (clipperCtorCallerWardsSlot I)
    (UInt256.ofNat 10) (by clipper_ctor_decode) mem_cost
    (clipperCtorWardsHashSlot I vat spotter dog ilk hilk) (by decide) (by evm_ov)
  have rdBeforeWards := clipper_ctor_run rdSlot with [swap2, swap1, swap2]
  obtain ⟨k', C', rd183⟩ := rdBeforeWards.sstore hperm
    (by clipper_ctor_decode) (by evm_ov)
  exact ⟨k', C', by simpa using rd183⟩

theorem clipperCtorRelyLogReach
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ σWards σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : Sat256}
    (vat spotter dog : AccountAddress) (ilk : List UInt8) (hilk : ilk.length = 32)
    {k C : Nat} (hperm : I.perm = true)
    (rd183 : RD (clipperCtorCode vat spotter dog ilk) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨183⟩
      [solcSourceWord I, EVM.word dog.val, ⟨64⟩, EVM.word spotter.val,
        ⟨0⟩, EVM.word vat.val, ABI.bytesToWord ilk]
      (clipperCtorWardsHashMem I vat spotter dog ilk) (UInt256.ofNat 10) ByteArray.empty
      (createdAccounts, σWards) k C) :
    ∃ k' C', RD (clipperCtorCode vat spotter dog ilk) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨230⟩ []
      (clipperCtorWardsHashMem I vat spotter dog ilk) (UInt256.ofNat 10) ByteArray.empty
      (createdAccounts, σWards) k' C' := by
  have rdMload := clipper_ctor_run rd183 with [
    swap2,
    raw mload 0 ⟨320⟩ (UInt256.ofNat 10)
      (by clipper_ctor_decode) mem_cost
      (clipperCtorWardsHashMem_mload64 I vat spotter dog ilk hilk)
      (by decide) (by evm_ov),
    swap5, swap6, swap3, swap5, swap1, swap4]
  have rdTopic := rdMload.pushConst clipperCtorRelyLogTopic
    (width := 32) (op := .PUSH32) (by decide) (by clipper_ctor_decode) (by evm_ov)
  have rdLogStack := clipper_ctor_run rdTopic with [swap2]
  have rdLog := RD.log2 0 (UInt256.ofNat 10) rdLogStack
    (by clipper_ctor_decode) hperm mem_cost (by decide) (by evm_ov)
  have rd230 := clipper_ctor_run rdLog with [pop, pop, pop, pop]
  exact ⟨_, _, rd230⟩

noncomputable def clipperCtorPatch01 (vat : AccountAddress) : ByteArray :=
  writeWord clipperBytecode 1463 (EVM.word vat.val)
noncomputable def clipperCtorPatch02 (vat : AccountAddress) : ByteArray :=
  writeWord (clipperCtorPatch01 vat) 2437 (EVM.word vat.val)
noncomputable def clipperCtorPatch03 (vat : AccountAddress) : ByteArray :=
  writeWord (clipperCtorPatch02 vat) 3145 (EVM.word vat.val)
noncomputable def clipperCtorPatch04 (vat : AccountAddress) : ByteArray :=
  writeWord (clipperCtorPatch03 vat) 4318 (EVM.word vat.val)
noncomputable def clipperCtorPatch05 (vat : AccountAddress) : ByteArray :=
  writeWord (clipperCtorPatch04 vat) 4441 (EVM.word vat.val)
noncomputable def clipperCtorPatch06 (vat : AccountAddress) : ByteArray :=
  writeWord (clipperCtorPatch05 vat) 4751 (EVM.word vat.val)
noncomputable def clipperCtorPatch07 (vat : AccountAddress) : ByteArray :=
  writeWord (clipperCtorPatch06 vat) 5115 (EVM.word vat.val)
noncomputable def clipperCtorPatch08 (vat : AccountAddress) : ByteArray :=
  writeWord (clipperCtorPatch07 vat) 6295 (EVM.word vat.val)
noncomputable def clipperCtorPatch09 (vat : AccountAddress) : ByteArray :=
  writeWord (clipperCtorPatch08 vat) 7936 (EVM.word vat.val)
noncomputable def clipperCtorPatch10 (vat : AccountAddress) (ilk : List UInt8) : ByteArray :=
  writeWord (clipperCtorPatch09 vat) 1510 (ABI.bytesToWord ilk)
noncomputable def clipperCtorPatch11 (vat : AccountAddress) (ilk : List UInt8) : ByteArray :=
  writeWord (clipperCtorPatch10 vat ilk) 1661 (ABI.bytesToWord ilk)
noncomputable def clipperCtorPatch12 (vat : AccountAddress) (ilk : List UInt8) : ByteArray :=
  writeWord (clipperCtorPatch11 vat ilk) 2221 (ABI.bytesToWord ilk)
noncomputable def clipperCtorPatch13 (vat : AccountAddress) (ilk : List UInt8) : ByteArray :=
  writeWord (clipperCtorPatch12 vat ilk) 2369 (ABI.bytesToWord ilk)
noncomputable def clipperCtorPatch14 (vat : AccountAddress) (ilk : List UInt8) : ByteArray :=
  writeWord (clipperCtorPatch13 vat ilk) 4239 (ABI.bytesToWord ilk)
noncomputable def clipperCtorPatch15 (vat : AccountAddress) (ilk : List UInt8) : ByteArray :=
  writeWord (clipperCtorPatch14 vat ilk) 4866 (ABI.bytesToWord ilk)
noncomputable def clipperCtorPatch16 (vat : AccountAddress) (ilk : List UInt8) : ByteArray :=
  writeWord (clipperCtorPatch15 vat ilk) 5046 (ABI.bytesToWord ilk)
noncomputable def clipperCtorPatch17 (vat : AccountAddress) (ilk : List UInt8) : ByteArray :=
  writeWord (clipperCtorPatch16 vat ilk) 6800 (ABI.bytesToWord ilk)
noncomputable def clipperCtorPatch18 (vat : AccountAddress) (ilk : List UInt8) : ByteArray :=
  writeWord (clipperCtorPatch17 vat ilk) 8747 (ABI.bytesToWord ilk)

theorem clipperCtorPatch18_eq (vat : AccountAddress) (ilk : List UInt8) :
    clipperCtorPatch18 vat ilk = clipperCtorPatchedRuntime vat ilk := by
  rfl

set_option maxHeartbeats 3000000 in
theorem clipperCtorReturnTrace
    {I : ExecutionEnv} {g : Sat256} {s0 : State} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    (vat spotter dog : AccountAddress) (ilk : List UInt8) (hilk : ilk.length = 32)
    (h : RD (clipperCtorCode vat spotter dog ilk) I g s0 ⟨230⟩ []
      (clipperCtorWardsHashMem I vat spotter dog ilk) (UInt256.ofNat 10)
      rdata acc k C) :
    RDret (clipperCtorCode vat spotter dog ilk) g s0 acc
      (clipperCtorPatchedRuntime vat ilk) := by
  have hvatload :
      (if (⟨160⟩ : UInt256).toNat ≥
            (clipperCtorWardsHashMem I vat spotter dog ilk).size ∨
          (⟨160⟩ : UInt256) ≥ UInt256.ofNat 10 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat (fromByteArrayBigEndian
          ((clipperCtorWardsHashMem I vat spotter dog ilk).readWithPadding 160 32))) =
        UInt256.shiftLeft (EVM.word vat.val) ⟨96⟩ := by
    apply mloadWordValue_of_readWithPadding
    · rw [clipperCtorWardsHashMem_size _ _ _ _ _ hilk]
      decide
    · decide
    · simpa using clipperCtorWardsHashMem_read160 I vat spotter dog ilk hilk
  have rdVatRaw := clipper_ctor_run h with [
    push1 ⟨128⟩,
    raw mload 0 (ABI.bytesToWord ilk) (UInt256.ofNat 10)
      (by clipper_ctor_decode) mem_cost
      (clipperCtorWardsHashMem_mload128 I vat spotter dog ilk hilk)
      (by decide) (by evm_ov),
    push1 ⟨160⟩,
    raw mload 0 (UInt256.shiftLeft (EVM.word vat.val) ⟨96⟩) (UInt256.ofNat 10)
      (by clipper_ctor_decode) mem_cost hvatload (by decide) (by evm_ov),
    push1 ⟨96⟩, shr]
  have rdVat := by
    simpa [clipperCtorAddressHighShiftDecode vat] using rdVatRaw
  have hcopy : (clipperCtorCode vat spotter dog ilk).write 347
      (clipperCtorWardsHashMem I vat spotter dog ilk) 0 9360 = clipperBytecode :=
    clipperCtorRuntime_codecopy_mem I vat spotter dog ilk hilk
  have rd248 := clipper_ctor_run rdVat with [
    push2 ⟨9360⟩, push2 ⟨347⟩, push1 ⟨0⟩,
    raw codecopy
      (Cₘ (UInt256.ofNat (MachineState.M (UInt256.ofNat 10).toNat 0 9360)) -
        Cₘ (UInt256.ofNat 10))
      clipperBytecode (UInt256.ofNat 293)
      (by clipper_ctor_decode) mem_cost hcopy (by decide) (by evm_ov)]
  have rd293 := clipper_ctor_run rd248 with [
    dup1, push2 ⟨1463⟩,
    raw mstore 0 (clipperCtorPatch01 vat) (UInt256.ofNat 293)
      (by clipper_ctor_decode) mem_cost
      (by unfold clipperCtorPatch01 Reasoning.Theory.writeWord;
          rw [show (⟨1463⟩ : UInt256).toNat = 1463 by decide])
      (by decide) (by evm_ov),
    dup1, push2 ⟨2437⟩,
    raw mstore 0 (clipperCtorPatch02 vat) (UInt256.ofNat 293)
      (by clipper_ctor_decode) mem_cost
      (by unfold clipperCtorPatch02 Reasoning.Theory.writeWord;
          rw [show (⟨2437⟩ : UInt256).toNat = 2437 by decide])
      (by decide) (by evm_ov),
    dup1, push2 ⟨3145⟩,
    raw mstore 0 (clipperCtorPatch03 vat) (UInt256.ofNat 293)
      (by clipper_ctor_decode) mem_cost
      (by unfold clipperCtorPatch03 Reasoning.Theory.writeWord;
          rw [show (⟨3145⟩ : UInt256).toNat = 3145 by decide])
      (by decide) (by evm_ov),
    dup1, push2 ⟨4318⟩,
    raw mstore 0 (clipperCtorPatch04 vat) (UInt256.ofNat 293)
      (by clipper_ctor_decode) mem_cost
      (by unfold clipperCtorPatch04 Reasoning.Theory.writeWord;
          rw [show (⟨4318⟩ : UInt256).toNat = 4318 by decide])
      (by decide) (by evm_ov),
    dup1, push2 ⟨4441⟩,
    raw mstore 0 (clipperCtorPatch05 vat) (UInt256.ofNat 293)
      (by clipper_ctor_decode) mem_cost
      (by unfold clipperCtorPatch05 Reasoning.Theory.writeWord;
          rw [show (⟨4441⟩ : UInt256).toNat = 4441 by decide])
      (by decide) (by evm_ov),
    dup1, push2 ⟨4751⟩,
    raw mstore 0 (clipperCtorPatch06 vat) (UInt256.ofNat 293)
      (by clipper_ctor_decode) mem_cost
      (by unfold clipperCtorPatch06 Reasoning.Theory.writeWord;
          rw [show (⟨4751⟩ : UInt256).toNat = 4751 by decide])
      (by decide) (by evm_ov),
    dup1, push2 ⟨5115⟩,
    raw mstore 0 (clipperCtorPatch07 vat) (UInt256.ofNat 293)
      (by clipper_ctor_decode) mem_cost
      (by unfold clipperCtorPatch07 Reasoning.Theory.writeWord;
          rw [show (⟨5115⟩ : UInt256).toNat = 5115 by decide])
      (by decide) (by evm_ov),
    dup1, push2 ⟨6295⟩,
    raw mstore 0 (clipperCtorPatch08 vat) (UInt256.ofNat 293)
      (by clipper_ctor_decode) mem_cost
      (by unfold clipperCtorPatch08 Reasoning.Theory.writeWord;
          rw [show (⟨6295⟩ : UInt256).toNat = 6295 by decide])
      (by decide) (by evm_ov),
    dup1, push2 ⟨7936⟩,
    raw mstore 0 (clipperCtorPatch09 vat) (UInt256.ofNat 293)
      (by clipper_ctor_decode) mem_cost
      (by unfold clipperCtorPatch09 Reasoning.Theory.writeWord;
          rw [show (⟨7936⟩ : UInt256).toNat = 7936 by decide])
      (by decide) (by evm_ov)]
  have rd294 := clipper_ctor_run rd293 with [pop]
  have rd339 := clipper_ctor_run rd294 with [
    dup1, push2 ⟨1510⟩,
    raw mstore 0 (clipperCtorPatch10 vat ilk) (UInt256.ofNat 293)
      (by clipper_ctor_decode) mem_cost
      (by unfold clipperCtorPatch10 Reasoning.Theory.writeWord;
          rw [show (⟨1510⟩ : UInt256).toNat = 1510 by decide])
      (by decide) (by evm_ov),
    dup1, push2 ⟨1661⟩,
    raw mstore 0 (clipperCtorPatch11 vat ilk) (UInt256.ofNat 293)
      (by clipper_ctor_decode) mem_cost
      (by unfold clipperCtorPatch11 Reasoning.Theory.writeWord;
          rw [show (⟨1661⟩ : UInt256).toNat = 1661 by decide])
      (by decide) (by evm_ov),
    dup1, push2 ⟨2221⟩,
    raw mstore 0 (clipperCtorPatch12 vat ilk) (UInt256.ofNat 293)
      (by clipper_ctor_decode) mem_cost
      (by unfold clipperCtorPatch12 Reasoning.Theory.writeWord;
          rw [show (⟨2221⟩ : UInt256).toNat = 2221 by decide])
      (by decide) (by evm_ov),
    dup1, push2 ⟨2369⟩,
    raw mstore 0 (clipperCtorPatch13 vat ilk) (UInt256.ofNat 293)
      (by clipper_ctor_decode) mem_cost
      (by unfold clipperCtorPatch13 Reasoning.Theory.writeWord;
          rw [show (⟨2369⟩ : UInt256).toNat = 2369 by decide])
      (by decide) (by evm_ov),
    dup1, push2 ⟨4239⟩,
    raw mstore 0 (clipperCtorPatch14 vat ilk) (UInt256.ofNat 293)
      (by clipper_ctor_decode) mem_cost
      (by unfold clipperCtorPatch14 Reasoning.Theory.writeWord;
          rw [show (⟨4239⟩ : UInt256).toNat = 4239 by decide])
      (by decide) (by evm_ov),
    dup1, push2 ⟨4866⟩,
    raw mstore 0 (clipperCtorPatch15 vat ilk) (UInt256.ofNat 293)
      (by clipper_ctor_decode) mem_cost
      (by unfold clipperCtorPatch15 Reasoning.Theory.writeWord;
          rw [show (⟨4866⟩ : UInt256).toNat = 4866 by decide])
      (by decide) (by evm_ov),
    dup1, push2 ⟨5046⟩,
    raw mstore 0 (clipperCtorPatch16 vat ilk) (UInt256.ofNat 293)
      (by clipper_ctor_decode) mem_cost
      (by unfold clipperCtorPatch16 Reasoning.Theory.writeWord;
          rw [show (⟨5046⟩ : UInt256).toNat = 5046 by decide])
      (by decide) (by evm_ov),
    dup1, push2 ⟨6800⟩,
    raw mstore 0 (clipperCtorPatch17 vat ilk) (UInt256.ofNat 293)
      (by clipper_ctor_decode) mem_cost
      (by unfold clipperCtorPatch17 Reasoning.Theory.writeWord;
          rw [show (⟨6800⟩ : UInt256).toNat = 6800 by decide])
      (by decide) (by evm_ov),
    dup1, push2 ⟨8747⟩,
    raw mstore 0 (clipperCtorPatch18 vat ilk) (UInt256.ofNat 293)
      (by clipper_ctor_decode) mem_cost
      (by unfold clipperCtorPatch18 Reasoning.Theory.writeWord;
          rw [show (⟨8747⟩ : UInt256).toNat = 8747 by decide])
      (by decide) (by evm_ov)]
  rw [clipperCtorPatch18_eq vat ilk] at rd339
  have rdBeforeReturn := clipper_ctor_run rd339 with [pop, push2 ⟨9360⟩, push1 ⟨0⟩]
  exact rdBeforeReturn.ret 0 (clipperCtorPatchedRuntime vat ilk)
    (by clipper_ctor_decode) mem_cost (clipperCtorPatchedRuntime_read vat ilk) (by evm_ov)

theorem clipperInitcodeSuccess
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : Sat256}
    (vat spotter dog : AccountAddress) (ilk : List UInt8) (hilk : ilk.length = 32)
    (hcode : I.code = clipperCtorCode vat spotter dog ilk)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩) :
    RDret (clipperCtorCode vat spotter dog ilk) g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
      (createdAccounts,
        sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner
            (sstoreAccountMap I.codeOwner
              (sstoreAccountMap I.codeOwner
                (sstoreAccountMap I.codeOwner σ ⟨14⟩ ⟨0⟩)
                ⟨3⟩
                (setAddressOffset0Word
                  (solcSlotWord (sstoreAccountMap I.codeOwner σ ⟨14⟩ ⟨0⟩) I ⟨3⟩)
                  (EVM.word spotter.val)))
              ⟨1⟩
              (setAddressOffset0Word
                (solcSlotWord
                  (sstoreAccountMap I.codeOwner
                    (sstoreAccountMap I.codeOwner σ ⟨14⟩ ⟨0⟩) ⟨3⟩
                    (setAddressOffset0Word
                      (solcSlotWord (sstoreAccountMap I.codeOwner σ ⟨14⟩ ⟨0⟩) I ⟨3⟩)
                      (EVM.word spotter.val))) I ⟨1⟩)
                (EVM.word dog.val)))
            ⟨5⟩ clipperCtorRayWord)
          (clipperCtorCallerWardsSlot I) ⟨1⟩)
      (clipperCtorPatchedRuntime vat ilk) := by
  obtain ⟨_, _, rd78⟩ := clipperCtorArgsReach
    (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
    (blocks := blocks) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    vat spotter dog ilk hilk hcode hperm hwv
  obtain ⟨_, _, rd95⟩ := clipperCtorVatDecodeReach vat spotter dog ilk rd78
  obtain ⟨_, _, rd129⟩ := clipperCtorSpotterStoreReach vat spotter dog ilk hperm rd95
  obtain ⟨_, _, rd145⟩ := clipperCtorDogStoreReach vat spotter dog ilk hperm rd129
  obtain ⟨_, _, rd183⟩ := clipperCtorBufWardsReach vat spotter dog ilk hilk hperm rd145
  obtain ⟨_, _, rd230⟩ := clipperCtorRelyLogReach vat spotter dog ilk hilk hperm rd183
  exact clipperCtorReturnTrace vat spotter dog ilk hilk rd230

end Benchmarks.Dss.Clipper
