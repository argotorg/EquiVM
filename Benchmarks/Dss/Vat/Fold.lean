import Benchmarks.Dss.Vat.FoldTail

namespace Benchmarks.Dss.Vat

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

theorem RD.vatFoldRateStoreOk
    {cA gh bl σ σ₀ A I} {g : Sat256} {k C : ℕ} {sel : UInt256}
    {mem : ByteArray}
    (h : RD vatBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨5733⟩
      [foldRateWord I, foldUsrMaskedWord I, foldIlkWord I, ⟨524⟩, sel]
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hmem : mem.size = 96)
    (hneg :
      UInt256.slt (foldRateWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.gt
          (foldRateWord I + solcSlotWord σ I (solcMappingSlot ⟨2⟩ (foldIlkWord I) + ⟨1⟩))
          (solcSlotWord σ I (solcMappingSlot ⟨2⟩ (foldIlkWord I) + ⟨1⟩)) = ⟨0⟩)
    (hpos :
      UInt256.sgt (foldRateWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.lt
          (foldRateWord I + solcSlotWord σ I (solcMappingSlot ⟨2⟩ (foldIlkWord I) + ⟨1⟩))
          (solcSlotWord σ I (solcMappingSlot ⟨2⟩ (foldIlkWord I) + ⟨1⟩)) = ⟨0⟩)
    (hperm : I.perm = true) :
    ∃ k' C', RD vatBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨5768⟩
      [solcMappingSlot ⟨2⟩ (foldIlkWord I), foldRateWord I, foldUsrMaskedWord I,
        foldIlkWord I, ⟨524⟩, sel]
      (twoWordHashMem (foldIlkWord I) ⟨2⟩ mem)
      (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ
        (solcMappingSlot ⟨2⟩ (foldIlkWord I) + ⟨1⟩)
        (foldRateWord I + solcSlotWord σ I
          (solcMappingSlot ⟨2⟩ (foldIlkWord I) + ⟨1⟩))) k' C' := by
  let base := solcMappingSlot ⟨2⟩ (foldIlkWord I)
  let old := solcSlotWord σ I (base + ⟨1⟩)
  let sum := foldRateWord I + old
  have rd5734 := h.jumpdest (by decide +native) (by evm_ov)
  have rd5736 := rd5734.push1 ⟨0⟩ (by decide +native) (by evm_ov)
  have rd5737 := rd5736.dup4 (by decide +native) (by evm_ov)
  have rd5738 := rd5737.dup2 (by decide +native) (by evm_ov)
  have rd5739 := rd5738.mstore 0 (wordAt0Mem (foldIlkWord I) mem)
    (UInt256.ofNat 3) (by decide +native) mem_cost (by rfl) (by decide +native)
    (by evm_ov)
  have rd5741 := rd5739.push1 ⟨2⟩ (by decide +native) (by evm_ov)
  have rd5743 := rd5741.push1 ⟨32⟩ (by decide +native) (by evm_ov)
  have rd5744 := rd5743.mstore 0 (twoWordHashMem (foldIlkWord I) ⟨2⟩ mem)
    (UInt256.ofNat 3) (by decide +native) mem_cost (by rfl) (by decide +native)
    (by evm_ov)
  have rd5746 := rd5744.push1 ⟨64⟩ (by decide +native) (by evm_ov)
  have rd5747 := rd5746.swap1 (by decide +native) (by evm_ov)
  have hbase :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((twoWordHashMem (foldIlkWord I) ⟨2⟩ mem).readWithPadding 0 64))) =
        base := by
    simpa [base] using twoWordHashMem_solcMappingSlot ⟨2⟩ (foldIlkWord I) hmem
  have rd5748 := rd5747.keccak256 0 base (UInt256.ofNat 3) (by decide +native)
    mem_cost hbase (by decide +native) (by evm_ov)
  have rd5750 := rd5748.push1 ⟨1⟩ (by decide +native) (by evm_ov)
  have rd5751 := rd5750.dup2 (by decide +native) (by evm_ov)
  have rd5752 := rd5751.add (by decide +native) (by evm_ov)
  obtain ⟨_, _, rd5753raw⟩ := rd5752.sload (by decide +native) (by evm_ov)
  have hold :
      (σ.find? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD (base + ⟨1⟩) ⟨0⟩)) = old := by
    simp [old, solcSlotWord]
  have rd5753 := rd5753raw
  rw [hold] at rd5753
  have rd5756 := rd5753.push2 ⟨5762⟩ (by decide +native) (by evm_ov)
  have rd5757 := rd5756.swap1 (by decide +native) (by evm_ov)
  have rd5758 := rd5757.dup4 (by decide +native) (by evm_ov)
  have rd5761 := rd5758.push2 ⟨6653⟩ (by decide +native) (by evm_ov)
  have rd6653 := rd5761.jump (by decide +native) (by jump_dest) (by evm_ov)
  obtain ⟨_, _, rd5762⟩ := RD.vatSignedAddOk
    (x := old) (y := foldRateWord I) (ret := ⟨5762⟩)
    (R := [base, foldRateWord I, foldUsrMaskedWord I, foldIlkWord I, ⟨524⟩, sel])
    rd6653 (by simpa [old, base] using hneg) (by simpa [old, base] using hpos)
    (by jump_dest) (by simp)
  have rd5763 := rd5762.jumpdest (by decide +native) (by evm_ov)
  have rd5765 := rd5763.push1 ⟨1⟩ (by decide +native) (by evm_ov)
  have rd5766 := rd5765.dup3 (by decide +native) (by evm_ov)
  have rd5767 := rd5766.add (by decide +native) (by evm_ov)
  obtain ⟨_, _, rd5768⟩ := rd5767.sstore hperm (by decide +native)
    (by norm_num)
  exact ⟨_, _, by simpa [base, old, sum] using rd5768⟩

theorem RD.vatFoldRateStoreRevert
    {cA gh bl σ σ₀ A I} {g : Sat256} {k C : ℕ} {sel : UInt256}
    {mem : ByteArray}
    (h : RD vatBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨5733⟩
      [foldRateWord I, foldUsrMaskedWord I, foldIlkWord I, ⟨524⟩, sel]
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hmem : mem.size = 96)
    (hfail :
      ¬ (UInt256.slt (foldRateWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.gt
          (foldRateWord I + solcSlotWord σ I
            (solcMappingSlot ⟨2⟩ (foldIlkWord I) + ⟨1⟩))
          (solcSlotWord σ I (solcMappingSlot ⟨2⟩ (foldIlkWord I) + ⟨1⟩)) = ⟨0⟩) ∨
      (UInt256.slt (foldRateWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.gt
          (foldRateWord I + solcSlotWord σ I
            (solcMappingSlot ⟨2⟩ (foldIlkWord I) + ⟨1⟩))
          (solcSlotWord σ I (solcMappingSlot ⟨2⟩ (foldIlkWord I) + ⟨1⟩)) = ⟨0⟩) ∧
        ¬ (UInt256.sgt (foldRateWord I) ⟨0⟩ = ⟨0⟩ ∨
          UInt256.lt
            (foldRateWord I + solcSlotWord σ I
              (solcMappingSlot ⟨2⟩ (foldIlkWord I) + ⟨1⟩))
            (solcSlotWord σ I (solcMappingSlot ⟨2⟩ (foldIlkWord I) + ⟨1⟩)) =
              ⟨0⟩)) :
    RDrev vatBytecode g (initState cA gh bl σ σ₀ g A I) := by
  let base := solcMappingSlot ⟨2⟩ (foldIlkWord I)
  let old := solcSlotWord σ I (base + ⟨1⟩)
  let sum := foldRateWord I + old
  have rd5734 := h.jumpdest (by decide +native) (by evm_ov)
  have rd5736 := rd5734.push1 ⟨0⟩ (by decide +native) (by evm_ov)
  have rd5737 := rd5736.dup4 (by decide +native) (by evm_ov)
  have rd5738 := rd5737.dup2 (by decide +native) (by evm_ov)
  have rd5739 := rd5738.mstore 0 (wordAt0Mem (foldIlkWord I) mem)
    (UInt256.ofNat 3) (by decide +native) mem_cost (by rfl) (by decide +native)
    (by evm_ov)
  have rd5741 := rd5739.push1 ⟨2⟩ (by decide +native) (by evm_ov)
  have rd5743 := rd5741.push1 ⟨32⟩ (by decide +native) (by evm_ov)
  have rd5744 := rd5743.mstore 0 (twoWordHashMem (foldIlkWord I) ⟨2⟩ mem)
    (UInt256.ofNat 3) (by decide +native) mem_cost (by rfl) (by decide +native)
    (by evm_ov)
  have rd5746 := rd5744.push1 ⟨64⟩ (by decide +native) (by evm_ov)
  have rd5747 := rd5746.swap1 (by decide +native) (by evm_ov)
  have hbase :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((twoWordHashMem (foldIlkWord I) ⟨2⟩ mem).readWithPadding 0 64))) =
        base := by
    simpa [base] using twoWordHashMem_solcMappingSlot ⟨2⟩ (foldIlkWord I) hmem
  have rd5748 := rd5747.keccak256 0 base (UInt256.ofNat 3) (by decide +native)
    mem_cost hbase (by decide +native) (by evm_ov)
  have rd5750 := rd5748.push1 ⟨1⟩ (by decide +native) (by evm_ov)
  have rd5751 := rd5750.dup2 (by decide +native) (by evm_ov)
  have rd5752 := rd5751.add (by decide +native) (by evm_ov)
  obtain ⟨_, _, rd5753raw⟩ := rd5752.sload (by decide +native) (by evm_ov)
  have hold :
      (σ.find? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD (base + ⟨1⟩) ⟨0⟩)) = old := by
    simp [old, solcSlotWord]
  have rd5753 := rd5753raw
  rw [hold] at rd5753
  have rd5756 := rd5753.push2 ⟨5762⟩ (by decide +native) (by evm_ov)
  have rd5757 := rd5756.swap1 (by decide +native) (by evm_ov)
  have rd5758 := rd5757.dup4 (by decide +native) (by evm_ov)
  have rd5761 := rd5758.push2 ⟨6653⟩ (by decide +native) (by evm_ov)
  have rd6653 := rd5761.jump (by decide +native) (by jump_dest) (by evm_ov)
  exact RD.vatSignedAddRevert
    (x := old) (y := foldRateWord I) (ret := ⟨5762⟩)
    (R := [base, foldRateWord I, foldUsrMaskedWord I, foldIlkWord I, ⟨524⟩, sel])
    rd6653 (by simpa [old, base, sum] using hfail) (by simp)

theorem RD.vatFoldArtMulOk
    {cA gh bl σInit σ σ₀ A I} {g : Sat256} {k C : ℕ} {sel : UInt256}
    {mem : ByteArray}
    (h : RD vatBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨5768⟩
      [solcMappingSlot ⟨2⟩ (foldIlkWord I), foldRateWord I, foldUsrMaskedWord I,
        foldIlkWord I, ⟨524⟩, sel]
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hmax :
      UInt256.slt (solcSlotWord σ I (solcMappingSlot ⟨2⟩ (foldIlkWord I))) ⟨0⟩ =
        ⟨0⟩)
    (hmul :
      foldRateWord I = ⟨0⟩ ∨
        UInt256.eq
          (UInt256.sdiv
            (UInt256.mul (foldRateWord I)
              (solcSlotWord σ I (solcMappingSlot ⟨2⟩ (foldIlkWord I))))
            (foldRateWord I))
          (solcSlotWord σ I (solcMappingSlot ⟨2⟩ (foldIlkWord I))) ≠ ⟨0⟩) :
    ∃ k' C', RD vatBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨5782⟩
      [UInt256.mul (foldRateWord I)
        (solcSlotWord σ I (solcMappingSlot ⟨2⟩ (foldIlkWord I))),
        ⟨0⟩, solcMappingSlot ⟨2⟩ (foldIlkWord I), foldRateWord I, foldUsrMaskedWord I,
        foldIlkWord I, ⟨524⟩, sel]
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  let base := solcMappingSlot ⟨2⟩ (foldIlkWord I)
  let art := solcSlotWord σ I base
  let rad := UInt256.mul (foldRateWord I) art
  have rd5769 := h.dup1 (by decide +native) (by evm_ov)
  obtain ⟨_, _, rd5770raw⟩ := rd5769.sload (by decide +native) (by evm_ov)
  have hart :
      (σ.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD base ⟨0⟩)) =
        art := by
    simp [art, solcSlotWord]
  have rd5770 := rd5770raw
  rw [hart] at rd5770
  have rd5772 := rd5770.push1 ⟨0⟩ (by decide +native) (by evm_ov)
  have rd5773 := rd5772.swap1 (by decide +native) (by evm_ov)
  have rd5776 := rd5773.push2 ⟨5782⟩ (by decide +native) (by evm_ov)
  have rd5777 := rd5776.swap1 (by decide +native) (by evm_ov)
  have rd5778 := rd5777.dup5 (by decide +native) (by evm_ov)
  have rd5781 := rd5778.push2 ⟨6706⟩ (by decide +native) (by evm_ov)
  have rd6706 := rd5781.jump (by decide +native) (by jump_dest) (by evm_ov)
  obtain ⟨_, _, rd5782⟩ := Benchmarks.Dss.Vat.RD.vatSignedMulOk
    (x := art) (y := foldRateWord I) (ret := ⟨5782⟩)
    (R := [⟨0⟩, base, foldRateWord I, foldUsrMaskedWord I, foldIlkWord I, ⟨524⟩, sel])
    rd6706 (by simpa [art, base] using hmax) (by simpa [art, base] using hmul)
    (by jump_dest) (by simp)
  exact ⟨_, _, by simpa [base, art, rad] using rd5782⟩

theorem RD.vatFoldArtMulRevert
    {cA gh bl σInit σ σ₀ A I} {g : Sat256} {k C : ℕ} {sel : UInt256}
    {mem : ByteArray}
    (h : RD vatBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨5768⟩
      [solcMappingSlot ⟨2⟩ (foldIlkWord I), foldRateWord I, foldUsrMaskedWord I,
        foldIlkWord I, ⟨524⟩, sel]
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hfail :
      ¬ UInt256.slt (solcSlotWord σ I (solcMappingSlot ⟨2⟩ (foldIlkWord I))) ⟨0⟩ = ⟨0⟩ ∨
      UInt256.slt (solcSlotWord σ I (solcMappingSlot ⟨2⟩ (foldIlkWord I))) ⟨0⟩ = ⟨0⟩ ∧
        ¬ (foldRateWord I = ⟨0⟩ ∨
          UInt256.eq
            (UInt256.sdiv
              (UInt256.mul (foldRateWord I)
                (solcSlotWord σ I (solcMappingSlot ⟨2⟩ (foldIlkWord I))))
              (foldRateWord I))
            (solcSlotWord σ I (solcMappingSlot ⟨2⟩ (foldIlkWord I))) ≠ ⟨0⟩)) :
    RDrev vatBytecode g (initState cA gh bl σInit σ₀ g A I) := by
  let base := solcMappingSlot ⟨2⟩ (foldIlkWord I)
  let art := solcSlotWord σ I base
  have rd5769 := h.dup1 (by decide +native) (by evm_ov)
  obtain ⟨_, _, rd5770raw⟩ := rd5769.sload (by decide +native) (by evm_ov)
  have hart :
      (σ.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD base ⟨0⟩)) =
        art := by
    simp [art, solcSlotWord]
  have rd5770 := rd5770raw
  rw [hart] at rd5770
  have rd5772 := rd5770.push1 ⟨0⟩ (by decide +native) (by evm_ov)
  have rd5773 := rd5772.swap1 (by decide +native) (by evm_ov)
  have rd5776 := rd5773.push2 ⟨5782⟩ (by decide +native) (by evm_ov)
  have rd5777 := rd5776.swap1 (by decide +native) (by evm_ov)
  have rd5778 := rd5777.dup5 (by decide +native) (by evm_ov)
  have rd5781 := rd5778.push2 ⟨6706⟩ (by decide +native) (by evm_ov)
  have rd6706 := rd5781.jump (by decide +native) (by jump_dest) (by evm_ov)
  exact Benchmarks.Dss.Vat.RD.vatSignedMulRevert
    (x := art) (y := foldRateWord I) (ret := ⟨5782⟩)
    (R := [⟨0⟩, base, foldRateWord I, foldUsrMaskedWord I, foldIlkWord I, ⟨524⟩, sel])
    rd6706 (by simpa [art, base] using hfail) (by simp)

theorem vatFoldFinishSuccess
    {cA gh bl σ_evm σ_solm σ₀ A I} {g sel : UInt256}
    {mem : ByteArray} {k C : ℕ}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {cs : Frame} {evmOut : EVM.State}
    (hcode : I.code = vatBytecode)
    (hdispatch : dispatchMsg contract I.calldata = some foldTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (foldTransition.params.map Param.name)
        (transitionSignature foldTransition).paramTypes I.calldata = some (foldStore I))
    (hbody :
      ExecTransitionBody config contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (foldStore I) foldTransition.body (.returned cs evmOut none))
    (hcreated : acc.1 = evmOut.createdAccounts)
    (haccounts : accountMapEquiv acc.2 evmOut.accountMap)
    (hretPc : RD vatBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨524⟩ [sel]
      mem (UInt256.ofNat 3) ByteArray.empty acc k C) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hretPc' := hretPc.jumpdest (by decide +native) (by evm_ov)
  have hret :
      RDret vatBytecode (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        acc ByteArray.empty := by
    simpa using RD.stop hretPc' (by decide +native) (by simp)
  have henc : returnEquiv ByteArray.empty none foldTransition.returnType := by
    rw [show foldTransition.returnType = [] by rfl]
    exact returnEquiv.fallthrough rfl (by rfl) (by decide +native)
  exact hret.reEquivExecutionGenAccountMapEquiv hcode hdispatch hdecode hbody
    hcreated haccounts henc

set_option maxHeartbeats 0 in
theorem vatFoldBodyCore : VatBodyTheorem 9 := by
  intro cA gh bl σ_evm σ_solm σ₀ A I g hcode hsize hperm hwv hsel hAccounts
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (vatSelBytes 9) rfl hsel
  have hdispatch : dispatchMsg contract I.calldata = some foldTransition :=
    vatDispatchFold hsel
  have hreach := vatReachFoldBody (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
    (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz4 hsize hsel
  by_cases hsz100 : 100 ≤ I.calldata.size
  · have hdecode := vatDecode_fold_ok (I := I) hsz100
    obtain ⟨_, _, hdecoded⟩ := vatFoldX_decoded
      (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
      (A := A) (I := I) (g := Sat256.ofUInt256 g)
      hsz100 hsize hreach
    let callerSlot := vatCallerWardsSlot I
    have hcallerWord : vatSlotWord callerSlot σ_evm I = vatSlotWord callerSlot σ_solm I :=
      accountMapEquiv_storage_findD hAccounts I.codeOwner callerSlot ⟨0⟩
    by_cases hauthEvm : vatSlotWord callerSlot σ_evm I = ⟨1⟩
    · have hauthSolm : vatSlotWord callerSlot σ_solm I = ⟨1⟩ := by
        rw [← hcallerWord]
        exact hauthEvm
      have hauthSolc :
          solcSlotWord σ_evm I (solcMappingSlot ⟨0⟩ (hopeSourceWord I)) = ⟨1⟩ := by
        simpa [callerSlot, vatCallerWardsSlot, vatSlotWord] using hauthEvm
      obtain ⟨_, _, hafterAuth⟩ := RD.vatAuthCheckOk
        (code := vatBytecode) (pc := ⟨5581⟩) (okPc := ⟨5663⟩)
        (key := foldRateWord I) (ret := foldUsrMaskedWord I)
        (R := [foldIlkWord I, ⟨524⟩, vatSelWord I])
        (by simpa using hdecoded)
        (by unfold vatAuthCheckWf; repeat' first | apply And.intro | decide +native)
        hauthSolc (by jump_dest) (by simp)
      let liveSlot : UInt256 := ⟨10⟩
      have hliveWord : vatSlotWord liveSlot σ_evm I = vatSlotWord liveSlot σ_solm I :=
        accountMapEquiv_storage_findD hAccounts I.codeOwner liveSlot ⟨0⟩
      by_cases hliveEvm : vatSlotWord liveSlot σ_evm I = ⟨1⟩
      · have hliveSolm : vatSlotWord liveSlot σ_solm I = ⟨1⟩ := by
          rw [← hliveWord]
          exact hliveEvm
        have hliveSolc : solcSlotWord σ_evm I ⟨10⟩ = ⟨1⟩ := by
          simpa [liveSlot, vatSlotWord] using hliveEvm
        obtain ⟨_, _, hafterLive⟩ := RD.vatLiveGuardOk
          (code := vatBytecode) (pc := ⟨5663⟩) (okPc := ⟨5733⟩)
          (key := foldRateWord I) (ret := foldUsrMaskedWord I)
          (R := [foldIlkWord I, ⟨524⟩, vatSelWord I]) hafterAuth
          (by unfold vatLiveGuardWf; repeat' first | apply And.intro | decide +native)
          hliveSolc (by jump_dest) (by simp)
        let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
        let rateSlotE := solcMappingSlot ⟨2⟩ (foldIlkWord I) + ⟨1⟩
        let rateSlotS := foldRateSlot I
        let rateOldE := vatSlotWord rateSlotE σ_evm I
        let rateOldS := vatSlotWord rateSlotS σ_solm I
        have hrateSlotEq : rateSlotS = rateSlotE := by
          simpa [rateSlotS, rateSlotE] using foldRateSlot_eq I hsz100
        have hrateWord : rateOldE = rateOldS := by
          simpa [rateOldE, rateOldS, rateSlotS, hrateSlotEq] using
            accountMapEquiv_storage_findD hAccounts I.codeOwner rateSlotE ⟨0⟩
        have hloadRateS :
            Solm.EVM.storageLoad evm0 evm0.executionEnv.codeOwner rateSlotS = rateOldS := by
          simp [evm0, rateOldS, rateSlotS, vatSlotWord, solcSlotWord, initState,
            Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage]
        have hguardAuth := vatAuthGuardEval_true (cA := cA) (gh := gh) (bl := bl)
          (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
          (g := Sat256.ofUInt256 g) (locals := foldStore I)
          (foldStore_wards I) (by simpa [callerSlot] using hauthSolm)
        have hguardLive := vatLiveGuardEval_true (cA := cA) (gh := gh) (bl := bl)
          (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
          (g := Sat256.ofUInt256 g) (locals := foldStore I)
          (foldStore_live I) (by simpa [liveSlot] using hliveSolm)
        have hmemLive :
            (twoWordHashMem (hopeSourceWord I) ⟨0⟩ solcFreePtrMem).size = 96 :=
          twoWordHashMem_size_96 (hopeSourceWord I) ⟨0⟩ solcFreePtrMem_size
        let rateNewE := foldRateWord I + rateOldE
        let rateNewS := foldRateWord I + rateOldS
        have hrateVar :
            evalExpr? config { contract := contract, locals := foldStoreRateNew I rateNewS }
              evm0 (.var "rate") = .ok (.int (foldRateInt I)) :=
          vatEvalExpr_varInt (foldStoreRateNew_get_rate I rateNewS)
        have hrateNewVar :
            evalExpr? config { contract := contract, locals := foldStoreRateNew I rateNewS }
              evm0 (.var "rateNew") = .ok (.int (Int.ofNat rateNewS.toNat)) :=
          vatEvalExpr_varUInt256 (foldStoreRateNew_get_rateNew I rateNewS)
        have hrateLoadEval :
            evalExpr? config { contract := contract, locals := foldStoreRateNew I rateNewS }
                evm0 (.storage (ilksF (.var "i") "rate")) =
              .ok (.int (Int.ofNat rateOldS.toNat)) := by
          rw [evalExpr_fold_ilks_rate evm0 I (foldStoreRateNew I rateNewS) hsz100
            (foldStoreRateNew_get_i I rateNewS) (foldStoreRateNew_ilks I rateNewS)]
          rw [hloadRateS]
        have hrateOldBase :
            evalExpr? config { contract := contract, locals := foldStore I } evm0
                (.storage (ilksF (.var "i") "rate")) =
              .ok (.int (Int.ofNat rateOldS.toNat)) := by
          rw [evalExpr_fold_ilks_rate evm0 I (foldStore I) hsz100
            (foldStore_get_i I) (foldStore_ilks I)]
          rw [hloadRateS]
        have hrateLet :
            evalExpr? config { contract := contract, locals := foldStore I } evm0
              (wordWrap256 (.binary .add (.storage (ilksF (.var "i") "rate"))
                (.var "rate"))) = .ok (.int (Int.ofNat rateNewS.toNat)) :=
          evalExpr_fold_wordWrapAdd_ok hrateOldBase
            (vatEvalExpr_varInt (foldStore_get_rate I)) (foldRateInt_mod_word I) (by rfl)
        by_cases hRateNeg :
            UInt256.slt (foldRateWord I) ⟨0⟩ = ⟨0⟩ ∨
              UInt256.gt rateNewE rateOldE = ⟨0⟩
        · by_cases hRatePos :
              UInt256.sgt (foldRateWord I) ⟨0⟩ = ⟨0⟩ ∨
                UInt256.lt rateNewE rateOldE = ⟨0⟩
          · have hRateNegSolc :
                UInt256.slt (foldRateWord I) ⟨0⟩ = ⟨0⟩ ∨
                  UInt256.gt
                    (foldRateWord I +
                      solcSlotWord σ_evm I
                        (solcMappingSlot ⟨2⟩ (foldIlkWord I) + ⟨1⟩))
                    (solcSlotWord σ_evm I
                      (solcMappingSlot ⟨2⟩ (foldIlkWord I) + ⟨1⟩)) = ⟨0⟩ := by
              simpa [rateNewE, rateOldE, rateSlotE, vatSlotWord] using hRateNeg
            have hRatePosSolc :
                UInt256.sgt (foldRateWord I) ⟨0⟩ = ⟨0⟩ ∨
                  UInt256.lt
                    (foldRateWord I +
                      solcSlotWord σ_evm I
                        (solcMappingSlot ⟨2⟩ (foldIlkWord I) + ⟨1⟩))
                    (solcSlotWord σ_evm I
                      (solcMappingSlot ⟨2⟩ (foldIlkWord I) + ⟨1⟩)) = ⟨0⟩ := by
              simpa [rateNewE, rateOldE, rateSlotE, vatSlotWord] using hRatePos
            have hRateNegSource :
                0 ≤ foldRateInt I ∨ rateNewS.toNat ≤ rateOldS.toNat := by
              cases hRateNeg with
              | inl hslt =>
                  exact Or.inl (by
                    simpa [foldRateInt] using
                      slt_zero_eq_zero_to_nonneg (foldRateWord I) hslt)
              | inr hgt =>
                  exact Or.inr (by
                    have hle := ugt_eq_zero_to_le hgt
                    simpa [rateNewE, rateNewS, rateOldE, rateOldS, hrateWord] using hle)
            have hRatePosSource :
                foldRateInt I ≤ 0 ∨ rateOldS.toNat ≤ rateNewS.toNat := by
              cases hRatePos with
              | inl hsgt =>
                  exact Or.inl (by
                    simpa [foldRateInt] using
                      sgt_zero_eq_zero_to_nonpos (foldRateWord I) hsgt)
              | inr hlt =>
                  exact Or.inr (by
                    have hle := ult_eq_zero_to_le hlt
                    simpa [rateNewE, rateNewS, rateOldE, rateOldS, hrateWord] using hle)
            have hRateGuardNeg :
                evalExpr? config { contract := contract, locals := foldStoreRateNew I rateNewS }
                  evm0
                  (eitherExpr (.binary .ge (.var "rate") (.intLit 0))
                    (.binary .le (.var "rateNew")
                      (.storage (ilksF (.var "i") "rate")))) =
                  .ok (.bool true) :=
              evalSignedAddGuardNeg_true hrateVar hrateNewVar hrateLoadEval hRateNegSource
            have hRateGuardPos :
                evalExpr? config { contract := contract, locals := foldStoreRateNew I rateNewS }
                  evm0
                  (eitherExpr (.binary .le (.var "rate") (.intLit 0))
                    (.binary .ge (.var "rateNew")
                      (.storage (ilksF (.var "i") "rate")))) =
                  .ok (.bool true) :=
              evalSignedAddGuardPos_true hrateVar hrateNewVar hrateLoadEval hRatePosSource
            obtain ⟨_, _, hafterRate⟩ := RD.vatFoldRateStoreOk
              (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
              (A := A) (I := I) (g := Sat256.ofUInt256 g)
              (sel := vatSelWord I)
              hafterLive hmemLive hRateNegSolc hRatePosSolc hperm
            let evmRate := Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner
              rateSlotS rateNewS
            let artSlotE := solcMappingSlot ⟨2⟩ (foldIlkWord I)
            let artOldE := solcSlotWord
              (sstoreAccountMap I.codeOwner σ_evm rateSlotE rateNewE) I artSlotE
            let artOldS :=
              Solm.EVM.storageLoad evmRate evmRate.executionEnv.codeOwner (foldArtSlot I)
            have hrateNewWord : rateNewE = rateNewS := by
              simp [rateNewE, rateNewS, hrateWord]
            have hAccountsRate :
                accountMapEquiv
                  (sstoreAccountMap I.codeOwner σ_evm rateSlotE rateNewE)
                  evmRate.accountMap := by
              simpa [evmRate, evm0, initState, storageStore_accountMap,
                rateSlotS, hrateSlotEq, hrateNewWord] using
                accountMapEquiv_sstoreAccountMap I.codeOwner rateSlotE rateNewE hAccounts
            have hartSlotEq : foldArtSlot I = artSlotE := by
              simpa [artSlotE] using foldArtSlot_eq I hsz100
            have hArtWord : artOldE = artOldS := by
              have h := accountMapEquiv_storage_findD hAccountsRate I.codeOwner
                (foldArtSlot I) ⟨0⟩
              simpa [artOldE, artOldS, artSlotE, hartSlotEq, evmRate, vatSlotWord,
                solcSlotWord, Solm.EVM.storageLoad, State.lookupAccount,
                Account.lookupStorage, storageStore_executionEnv] using h
            by_cases hArtMaxE : UInt256.slt artOldE ⟨0⟩ = ⟨0⟩
            · have hArtMaxSolc :
                  UInt256.slt
                    (solcSlotWord (sstoreAccountMap I.codeOwner σ_evm rateSlotE rateNewE)
                      I (solcMappingSlot ⟨2⟩ (foldIlkWord I))) ⟨0⟩ = ⟨0⟩ := by
                simpa [artOldE, artSlotE] using hArtMaxE
              by_cases hMulE :
                  foldRateWord I = ⟨0⟩ ∨
                    UInt256.eq
                      (UInt256.sdiv (UInt256.mul (foldRateWord I) artOldE)
                        (foldRateWord I)) artOldE ≠ ⟨0⟩
              · have hMulSolc :
                    foldRateWord I = ⟨0⟩ ∨
                      UInt256.eq
                        (UInt256.sdiv
                          (UInt256.mul (foldRateWord I)
                            (solcSlotWord
                              (sstoreAccountMap I.codeOwner σ_evm rateSlotE rateNewE)
                              I (solcMappingSlot ⟨2⟩ (foldIlkWord I))))
                          (foldRateWord I))
                        (solcSlotWord
                          (sstoreAccountMap I.codeOwner σ_evm rateSlotE rateNewE)
                          I (solcMappingSlot ⟨2⟩ (foldIlkWord I))) ≠ ⟨0⟩ := by
                  simpa [artOldE, artSlotE] using hMulE
                obtain ⟨_, _, hafterArt⟩ := RD.vatFoldArtMulOk
                  (cA := cA) (gh := gh) (bl := bl)
                  (σInit := σ_evm)
                  (σ := sstoreAccountMap I.codeOwner σ_evm rateSlotE rateNewE)
                  (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
                  (sel := vatSelWord I) hafterRate hArtMaxSolc hMulSolc
                by_cases hRateZeroE : foldRateWord I = ⟨0⟩
                · have hRateZeroS : foldRateWord I = ⟨0⟩ := hRateZeroE
                  have hRateIntZero : foldRateInt I = 0 :=
                    foldRateInt_zero_of_word_zero I hRateZeroS
                  have hRadE :
                      UInt256.mul (foldRateWord I) artOldE = ⟨0⟩ := by
                    simpa [hRateZeroE] using u256_mul_zero_left artOldE
                  have hmemArt :
                      (twoWordHashMem (foldIlkWord I) ⟨2⟩
                        (twoWordHashMem (hopeSourceWord I) ⟨0⟩ solcFreePtrMem)).size = 96 :=
                    twoWordHashMem_size_96 (foldIlkWord I) ⟨2⟩ hmemLive
                  let daiSlotE := solcMappingSlot ⟨5⟩ (foldUsrMaskedWord I)
                  let daiOldE := solcSlotWord
                    (sstoreAccountMap I.codeOwner σ_evm rateSlotE rateNewE) I daiSlotE
                  let daiOldS :=
                    Solm.EVM.storageLoad evmRate evmRate.executionEnv.codeOwner
                      (foldDaiSlot I)
                  have hdaiSlotEq : foldDaiSlot I = daiSlotE := by
                    simpa [daiSlotE] using foldDaiSlot_eq I
                  have hDaiWord : daiOldE = daiOldS := by
                    have h := accountMapEquiv_storage_findD hAccountsRate I.codeOwner
                      (foldDaiSlot I) ⟨0⟩
                    simpa [daiOldE, daiOldS, daiSlotE, hdaiSlotEq, evmRate,
                      vatSlotWord, solcSlotWord, Solm.EVM.storageLoad,
                      State.lookupAccount, Account.lookupStorage, storageStore_executionEnv]
                      using h
                  have hDaiWordSlot :
                      solcSlotWord
                        (sstoreAccountMap I.codeOwner σ_evm rateSlotE rateNewE)
                        I (solcMappingSlot ⟨5⟩ (foldUsrMaskedWord I)) = daiOldS := by
                    simpa [daiOldE, daiSlotE] using hDaiWord
                  have hDaiNegSolc :
                      UInt256.slt (⟨0⟩ : UInt256) ⟨0⟩ = ⟨0⟩ ∨
                        UInt256.gt
                          ((⟨0⟩ : UInt256) +
                            solcSlotWord
                              (sstoreAccountMap I.codeOwner σ_evm rateSlotE rateNewE)
                              I (solcMappingSlot ⟨5⟩ (foldUsrMaskedWord I)))
                          (solcSlotWord
                            (sstoreAccountMap I.codeOwner σ_evm rateSlotE rateNewE)
                            I (solcMappingSlot ⟨5⟩ (foldUsrMaskedWord I))) = ⟨0⟩ := by
                    exact Or.inl (by decide +native)
                  have hDaiPosSolc :
                      UInt256.sgt (⟨0⟩ : UInt256) ⟨0⟩ = ⟨0⟩ ∨
                        UInt256.lt
                          ((⟨0⟩ : UInt256) +
                            solcSlotWord
                              (sstoreAccountMap I.codeOwner σ_evm rateSlotE rateNewE)
                              I (solcMappingSlot ⟨5⟩ (foldUsrMaskedWord I)))
                          (solcSlotWord
                            (sstoreAccountMap I.codeOwner σ_evm rateSlotE rateNewE)
                            I (solcMappingSlot ⟨5⟩ (foldUsrMaskedWord I))) = ⟨0⟩ := by
                    exact Or.inl (by decide +native)
                  obtain ⟨_, _, hafterDai⟩ := RD.vatFoldDaiStoreOk
                    (rad := ⟨0⟩) (base := solcMappingSlot ⟨2⟩ (foldIlkWord I))
                    (by simpa [artOldE, artSlotE, hRadE] using hafterArt)
                    hmemArt hDaiNegSolc hDaiPosSolc hperm
                  let evmDai := Solm.EVM.storageStore evmRate evmRate.executionEnv.codeOwner
                    (foldDaiSlot I) daiOldS
                  have hAccountsDai :
                      accountMapEquiv
                        (sstoreAccountMap I.codeOwner
                          (sstoreAccountMap I.codeOwner σ_evm rateSlotE rateNewE)
                          daiSlotE
                          ((⟨0⟩ : UInt256) +
                            solcSlotWord
                              (sstoreAccountMap I.codeOwner σ_evm rateSlotE rateNewE)
                              I daiSlotE))
                        evmDai.accountMap := by
                    simpa [evmDai, evmRate, evm0, initState, storageStore_accountMap,
                      storageStore_executionEnv, daiSlotE, daiOldE, hdaiSlotEq, hDaiWord,
                      u256_zero_add] using
                      accountMapEquiv_sstoreAccountMap I.codeOwner daiSlotE daiOldE
                        hAccountsRate
                  let debtOldE := solcSlotWord
                    (sstoreAccountMap I.codeOwner
                      (sstoreAccountMap I.codeOwner σ_evm rateSlotE rateNewE)
                      daiSlotE
                      ((⟨0⟩ : UInt256) +
                        solcSlotWord
                          (sstoreAccountMap I.codeOwner σ_evm rateSlotE rateNewE)
                          I daiSlotE))
                    I ⟨7⟩
                  let debtOldS :=
                    Solm.EVM.storageLoad evmDai evmDai.executionEnv.codeOwner foldDebtSlot
                  have hDebtWord : debtOldE = debtOldS := by
                    have h := accountMapEquiv_storage_findD hAccountsDai I.codeOwner
                      foldDebtSlot ⟨0⟩
                    simpa [debtOldE, debtOldS, evmDai, evmRate, evm0, initState,
                      foldDebtSlot, vatSlotWord, solcSlotWord, Solm.EVM.storageLoad,
                      State.lookupAccount,
                      Account.lookupStorage, storageStore_executionEnv] using h
                  have hDebtWordSimple :
                      solcSlotWord
                        (sstoreAccountMap I.codeOwner
                          (sstoreAccountMap I.codeOwner σ_evm rateSlotE rateNewE)
                          daiSlotE daiOldS) I ⟨7⟩ = debtOldS := by
                    simpa [debtOldE, daiSlotE, hDaiWordSlot, u256_zero_add] using hDebtWord
                  have hDebtNegSolc :
                      UInt256.slt (⟨0⟩ : UInt256) ⟨0⟩ = ⟨0⟩ ∨
                        UInt256.gt
                          ((⟨0⟩ : UInt256) +
                            solcSlotWord
                              (sstoreAccountMap I.codeOwner
                                (sstoreAccountMap I.codeOwner σ_evm rateSlotE rateNewE)
                                daiSlotE
                                ((⟨0⟩ : UInt256) +
                                  solcSlotWord
                                    (sstoreAccountMap I.codeOwner σ_evm rateSlotE rateNewE)
                                    I daiSlotE))
                              I ⟨7⟩)
                          (solcSlotWord
                            (sstoreAccountMap I.codeOwner
                              (sstoreAccountMap I.codeOwner σ_evm rateSlotE rateNewE)
                              daiSlotE
                              ((⟨0⟩ : UInt256) +
                                solcSlotWord
                                  (sstoreAccountMap I.codeOwner σ_evm rateSlotE rateNewE)
                                  I daiSlotE))
                            I ⟨7⟩) = ⟨0⟩ := by
                    exact Or.inl (by decide +native)
                  have hDebtPosSolc :
                      UInt256.sgt (⟨0⟩ : UInt256) ⟨0⟩ = ⟨0⟩ ∨
                        UInt256.lt
                          ((⟨0⟩ : UInt256) +
                            solcSlotWord
                              (sstoreAccountMap I.codeOwner
                                (sstoreAccountMap I.codeOwner σ_evm rateSlotE rateNewE)
                                daiSlotE
                                ((⟨0⟩ : UInt256) +
                                  solcSlotWord
                                    (sstoreAccountMap I.codeOwner σ_evm rateSlotE rateNewE)
                                    I daiSlotE))
                              I ⟨7⟩)
                          (solcSlotWord
                            (sstoreAccountMap I.codeOwner
                              (sstoreAccountMap I.codeOwner σ_evm rateSlotE rateNewE)
                              daiSlotE
                              ((⟨0⟩ : UInt256) +
                                solcSlotWord
                                  (sstoreAccountMap I.codeOwner σ_evm rateSlotE rateNewE)
                                  I daiSlotE))
                            I ⟨7⟩) = ⟨0⟩ := by
                    exact Or.inl (by decide +native)
                  obtain ⟨_, _, hafterDebt⟩ := RD.vatFoldDebtStoreReturnOk
                    (rad := ⟨0⟩) (base := solcMappingSlot ⟨2⟩ (foldIlkWord I))
                    hafterDai hDebtNegSolc hDebtPosSolc hperm
                  let evmDebt := Solm.EVM.storageStore evmDai evmDai.executionEnv.codeOwner
                    foldDebtSlot debtOldS
                  have hAccountsDebt :
                      accountMapEquiv
                        (sstoreAccountMap I.codeOwner
                          (sstoreAccountMap I.codeOwner
                            (sstoreAccountMap I.codeOwner σ_evm rateSlotE rateNewE)
                            daiSlotE
                            daiOldE)
                          ⟨7⟩ debtOldS)
                        evmDebt.accountMap := by
                    simpa [evmDebt, evmDai, evmRate, evm0, initState,
                      storageStore_accountMap, foldDebtSlot, storageStore_executionEnv,
                      daiSlotE, hdaiSlotEq, daiOldE, hDaiWord, u256_zero_add] using
                      accountMapEquiv_sstoreAccountMap I.codeOwner foldDebtSlot debtOldS
                        hAccountsDai
                  have hArtMaxS : UInt256.slt artOldS ⟨0⟩ = ⟨0⟩ := by
                    simpa [hArtWord] using hArtMaxE
                  have hloadArtS :
                      Solm.EVM.storageLoad
                          (Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner
                            (foldRateSlot I) rateNewS)
                          evm0.executionEnv.codeOwner (foldArtSlot I) = artOldS := by
                    simp [artOldS, evmRate, rateSlotS, storageStore_executionEnv]
                  have hmulGuardMax :
                      evalExpr? config
                        { contract := contract, locals := foldStoreRad I rateNewS 0 }
                        (Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner
                          (foldRateSlot I) rateNewS)
                        (.binary .le (.storage (ilksF (.var "i") "Art"))
                          (.intLit maxInt256)) =
                        .ok (.bool true) := by
                    have hart :
                        evalExpr? config
                          { contract := contract, locals := foldStoreRad I rateNewS 0 }
                          evmRate (.storage (ilksF (.var "i") "Art")) =
                        .ok (.int (Int.ofNat artOldS.toNat)) := by
                      rw [evalExpr_fold_ilks_art evmRate I
                        (foldStoreRad I rateNewS 0) hsz100
                        (foldStoreRad_get_i I rateNewS 0)
                        (foldStoreRad_ilks I rateNewS 0)]
                    have hmaxLit :
                        evalExpr? config
                          { contract := contract, locals := foldStoreRad I rateNewS 0 }
                          evmRate (.intLit maxInt256) = .ok (.int maxInt256) := by
                      simp [evalExpr?, pure]
                    simpa [evmRate] using
                      vatEvalExpr_le_int_true hart hmaxLit
                        (uintWordLeMaxInt256_of_slt_zero hArtMaxS)
                  have hmulGuard :
                      evalExpr? config
                        { contract := contract, locals := foldStoreRad I rateNewS 0 }
                        (Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner
                          (foldRateSlot I) rateNewS)
                        (eitherExpr (.binary .eq (.var "rate") (.intLit 0))
                          (.binary .eq (.binary .div (.var "rad") (.var "rate"))
                            (.storage (ilksF (.var "i") "Art")))) =
                        .ok (.bool true) := by
                    simpa [evmRate] using
                      evalExpr_fold_mul_guard_rate_zero_true evmRate I rateNewS 0
                        hRateIntZero
                  have hloadDaiS :
                      Solm.EVM.storageLoad
                          (Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner
                            (foldRateSlot I) rateNewS)
                          evm0.executionEnv.codeOwner (foldDaiSlot I) = daiOldS := by
                    simp [daiOldS, evmRate, rateSlotS, storageStore_executionEnv]
                  have hradWordZero :
                      (0 : Int) % (Int.ofNat EVM.wordModulus) =
                        Int.ofNat (⟨0⟩ : UInt256).toNat := by
                    simp
                  have hDaiGuardNeg :
                      evalExpr? config
                        { contract := contract,
                          locals := foldStoreDaiNew I rateNewS 0 daiOldS }
                        (Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner
                          (foldRateSlot I) rateNewS)
                        (eitherExpr (.binary .ge (.var "rad") (.intLit 0))
                          (.binary .le (.var "daiNew") (.storage (daiRef (.var "u"))))) =
                        .ok (.bool true) := by
                    have hrad0 := vatEvalExpr_varInt (evm := evmRate)
                      (foldStoreDaiNew_get_rad I rateNewS 0 daiOldS)
                    have hdaiNewVar := vatEvalExpr_varUInt256 (evm := evmRate)
                      (foldStoreDaiNew_get_daiNew I rateNewS 0 daiOldS)
                    have hdaiLoad :
                        evalExpr? config
                          { contract := contract,
                            locals := foldStoreDaiNew I rateNewS 0 daiOldS }
                          evmRate (.storage (daiRef (.var "u"))) =
                        .ok (.int (Int.ofNat daiOldS.toNat)) := by
                      rw [evalExpr_fold_dai_u evmRate I
                        (foldStoreDaiNew I rateNewS 0 daiOldS)
                        (foldStoreDaiNew_get_u I rateNewS 0 daiOldS)
                        (foldStoreDaiNew_dai I rateNewS 0 daiOldS)]
                    simpa [evmRate] using
                      evalSignedAddGuardNeg_true hrad0 hdaiNewVar hdaiLoad
                        (Or.inl (by norm_num))
                  have hDaiGuardPos :
                      evalExpr? config
                        { contract := contract,
                          locals := foldStoreDaiNew I rateNewS 0 daiOldS }
                        (Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner
                          (foldRateSlot I) rateNewS)
                        (eitherExpr (.binary .le (.var "rad") (.intLit 0))
                          (.binary .ge (.var "daiNew") (.storage (daiRef (.var "u"))))) =
                        .ok (.bool true) := by
                    have hrad0 := vatEvalExpr_varInt (evm := evmRate)
                      (foldStoreDaiNew_get_rad I rateNewS 0 daiOldS)
                    have hdaiNewVar := vatEvalExpr_varUInt256 (evm := evmRate)
                      (foldStoreDaiNew_get_daiNew I rateNewS 0 daiOldS)
                    have hdaiLoad :
                        evalExpr? config
                          { contract := contract,
                            locals := foldStoreDaiNew I rateNewS 0 daiOldS }
                          evmRate (.storage (daiRef (.var "u"))) =
                        .ok (.int (Int.ofNat daiOldS.toNat)) := by
                      rw [evalExpr_fold_dai_u evmRate I
                        (foldStoreDaiNew I rateNewS 0 daiOldS)
                        (foldStoreDaiNew_get_u I rateNewS 0 daiOldS)
                        (foldStoreDaiNew_dai I rateNewS 0 daiOldS)]
                    simpa [evmRate] using
                      evalSignedAddGuardPos_true hrad0 hdaiNewVar hdaiLoad
                        (Or.inl (by norm_num))
                  have hloadDebtS :
                      Solm.EVM.storageLoad
                          (Solm.EVM.storageStore
                          (Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner
                              (foldRateSlot I) rateNewS)
                            evm0.executionEnv.codeOwner (foldDaiSlot I) daiOldS)
                          evm0.executionEnv.codeOwner foldDebtSlot = debtOldS := by
                    simp [debtOldS, evmDai, evmRate, rateSlotS, storageStore_executionEnv]
                  have hDebtGuardNeg :
                      evalExpr? config
                        { contract := contract,
                          locals := foldStoreDebtNew I rateNewS 0 daiOldS debtOldS }
                        (Solm.EVM.storageStore
                          (Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner
                            (foldRateSlot I) rateNewS)
                          evm0.executionEnv.codeOwner (foldDaiSlot I) daiOldS)
                        (eitherExpr (.binary .ge (.var "rad") (.intLit 0))
                          (.binary .le (.var "debtNew") (.storage debtRef))) =
                        .ok (.bool true) := by
                    have hrad0 := vatEvalExpr_varInt (evm := evmDai)
                      (foldStoreDebtNew_get_rad I rateNewS 0 daiOldS debtOldS)
                    have hdebtNewVar := vatEvalExpr_varUInt256 (evm := evmDai)
                      (foldStoreDebtNew_get_debtNew I rateNewS 0 daiOldS debtOldS)
                    have hdebtLoad :
                        evalExpr? config
                          { contract := contract,
                            locals := foldStoreDebtNew I rateNewS 0 daiOldS debtOldS }
                          evmDai (.storage debtRef) =
                        .ok (.int (Int.ofNat debtOldS.toNat)) := by
                      rw [evalExpr_fold_debt evmDai
                        (foldStoreDebtNew I rateNewS 0 daiOldS debtOldS)
                        (foldStoreDebtNew_debt I rateNewS 0 daiOldS debtOldS)]
                    simpa [evmDai, evmRate, storageStore_executionEnv] using
                      evalSignedAddGuardNeg_true hrad0 hdebtNewVar hdebtLoad
                        (Or.inl (by norm_num))
                  have hDebtGuardPos :
                      evalExpr? config
                        { contract := contract,
                          locals := foldStoreDebtNew I rateNewS 0 daiOldS debtOldS }
                        (Solm.EVM.storageStore
                          (Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner
                            (foldRateSlot I) rateNewS)
                          evm0.executionEnv.codeOwner (foldDaiSlot I) daiOldS)
                        (eitherExpr (.binary .le (.var "rad") (.intLit 0))
                          (.binary .ge (.var "debtNew") (.storage debtRef))) =
                        .ok (.bool true) := by
                    have hrad0 := vatEvalExpr_varInt (evm := evmDai)
                      (foldStoreDebtNew_get_rad I rateNewS 0 daiOldS debtOldS)
                    have hdebtNewVar := vatEvalExpr_varUInt256 (evm := evmDai)
                      (foldStoreDebtNew_get_debtNew I rateNewS 0 daiOldS debtOldS)
                    have hdebtLoad :
                        evalExpr? config
                          { contract := contract,
                            locals := foldStoreDebtNew I rateNewS 0 daiOldS debtOldS }
                          evmDai (.storage debtRef) =
                        .ok (.int (Int.ofNat debtOldS.toNat)) := by
                      rw [evalExpr_fold_debt evmDai
                        (foldStoreDebtNew I rateNewS 0 daiOldS debtOldS)
                        (foldStoreDebtNew_debt I rateNewS 0 daiOldS debtOldS)]
                    simpa [evmDai, evmRate, storageStore_executionEnv] using
                      evalSignedAddGuardPos_true hrad0 hdebtNewVar hdebtLoad
                        (Or.inl (by norm_num))
                  have hbody := vatFoldSourceSuccess evm0 I hwv hsz100
                    hguardAuth hguardLive hloadRateS (by rfl)
                    hRateGuardNeg hRateGuardPos hloadArtS
                    (by simp [hRateIntZero]) (by norm_num) (by norm_num)
                    hmulGuardMax hmulGuard hloadDaiS hradWordZero
                    (by simp [u256_zero_add]) hDaiGuardNeg hDaiGuardPos hloadDebtS
                    (by simp [u256_zero_add]) hDebtGuardNeg hDebtGuardPos
                  exact vatFoldFinishSuccess hcode hdispatch hdecode hbody
                    (by
                      simp [foldPostState, evm0, initState, storageStore_createdAccounts])
                    (by
                      simpa [foldPostState, evmDebt, evmDai, evmRate,
                        storageStore_executionEnv, daiSlotE, hdaiSlotEq, daiOldE,
                        hDaiWord, hDebtWordSimple, u256_zero_add] using
                        hAccountsDebt)
                    hafterDebt
                · have hMulNonzeroE :
                      UInt256.eq
                        (UInt256.sdiv (UInt256.mul (foldRateWord I) artOldE)
                          (foldRateWord I)) artOldE ≠ ⟨0⟩ :=
                    hMulE.resolve_left hRateZeroE
                  have hMulEqE :
                      UInt256.sdiv (UInt256.mul (foldRateWord I) artOldE)
                          (foldRateWord I) = artOldE :=
                    u256_eq_ne_zero_to_eq hMulNonzeroE
                  let radWord := UInt256.mul (foldRateWord I) artOldE
                  let rad := Int.ofNat artOldS.toNat * foldRateInt I
                  have hRateIntNe : foldRateInt I ≠ 0 :=
                    foldRateInt_ne_zero_of_word_ne_zero I hRateZeroE
                  have hArtMaxS : UInt256.slt artOldS ⟨0⟩ = ⟨0⟩ := by
                    simpa [hArtWord] using hArtMaxE
                  have hArtLowE : artOldE.toNat < EVM.twoPow 255 :=
                    u256_toNat_lt_sign_of_slt_zero hArtMaxE
                  have hArtLowS : artOldS.toNat < EVM.twoPow 255 := by
                    simpa [hArtWord] using hArtLowE
                  have hloadArtS :
                      Solm.EVM.storageLoad
                          (Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner
                            (foldRateSlot I) rateNewS)
                          evm0.executionEnv.codeOwner (foldArtSlot I) = artOldS := by
                    simp [artOldS, evmRate, rateSlotS, storageStore_executionEnv]
                  have hmulGuardMax :
                      evalExpr? config
                        { contract := contract, locals := foldStoreRad I rateNewS rad }
                        (Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner
                          (foldRateSlot I) rateNewS)
                        (.binary .le (.storage (ilksF (.var "i") "Art"))
                          (.intLit maxInt256)) =
                        .ok (.bool true) := by
                    have hart :
                        evalExpr? config
                          { contract := contract, locals := foldStoreRad I rateNewS rad }
                          evmRate (.storage (ilksF (.var "i") "Art")) =
                        .ok (.int (Int.ofNat artOldS.toNat)) := by
                      rw [evalExpr_fold_ilks_art evmRate I
                        (foldStoreRad I rateNewS rad) hsz100
                        (foldStoreRad_get_i I rateNewS rad)
                        (foldStoreRad_ilks I rateNewS rad)]
                    have hmaxLit :
                        evalExpr? config
                          { contract := contract, locals := foldStoreRad I rateNewS rad }
                          evmRate (.intLit maxInt256) = .ok (.int maxInt256) := by
                      simp [evalExpr?, pure]
                    simpa [evmRate] using
                      vatEvalExpr_le_int_true hart hmaxLit
                        (uintWordLeMaxInt256_of_slt_zero hArtMaxS)
                  have hmulDiv :
                      rad / foldRateInt I = Int.ofNat artOldS.toNat := by
                    dsimp [rad]
                    rw [mul_comm]
                    exact Int.mul_ediv_cancel_left (Int.ofNat artOldS.toNat) hRateIntNe
                  have hmulGuard :
                      evalExpr? config
                        { contract := contract, locals := foldStoreRad I rateNewS rad }
                        (Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner
                          (foldRateSlot I) rateNewS)
                        (eitherExpr (.binary .eq (.var "rate") (.intLit 0))
                          (.binary .eq (.binary .div (.var "rad") (.var "rate"))
                            (.storage (ilksF (.var "i") "Art")))) =
                        .ok (.bool true) := by
                    have hart :
                        evalExpr? config
                          { contract := contract, locals := foldStoreRad I rateNewS rad }
                          evmRate (.storage (ilksF (.var "i") "Art")) =
                        .ok (.int (Int.ofNat artOldS.toNat)) := by
                      rw [evalExpr_fold_ilks_art evmRate I
                        (foldStoreRad I rateNewS rad) hsz100
                        (foldStoreRad_get_i I rateNewS rad)
                        (foldStoreRad_ilks I rateNewS rad)]
                    simpa [evmRate] using
                      evalExpr_fold_mul_guard_exact_true evmRate I rateNewS rad
                        hRateIntNe hmulDiv hart
                  have hradWord :
                      rad % (Int.ofNat EVM.wordModulus) =
                        Int.ofNat radWord.toNat := by
                    dsimp [rad, radWord]
                    simpa [hArtWord] using fold_rad_mod_word I artOldS
                  have hradRange :=
                    fold_mul_word_product_range_of_guard I hArtLowE hMulEqE
                  have hradLo : -((2 : Int) ^ 255) ≤ rad := by
                    simpa [rad, hArtWord] using hradRange.1
                  have hradHi : rad < (2 : Int) ^ 255 := by
                    simpa [rad, hArtWord] using hradRange.2
                  have hradBlock :=
                    vatFoldRadMulOk evmRate I hsz100
                      (by simpa [evmRate, storageStore_executionEnv] using hloadArtS)
                      (by rfl) hradLo hradHi
                      (by simpa [evmRate] using hmulGuardMax)
                      (by simpa [evmRate] using hmulGuard)
                  have hrateBlock := vatFoldRateAddAssignOk evm0 I hsz100 hloadRateS
                    (by rfl) hRateGuardNeg hRateGuardPos
                  have hmemArt :
                      (twoWordHashMem (foldIlkWord I) ⟨2⟩
                        (twoWordHashMem (hopeSourceWord I) ⟨0⟩ solcFreePtrMem)).size =
                        96 :=
                    twoWordHashMem_size_96 (foldIlkWord I) ⟨2⟩ hmemLive
                  let daiSlotE := solcMappingSlot ⟨5⟩ (foldUsrMaskedWord I)
                  let daiOldE := solcSlotWord
                    (sstoreAccountMap I.codeOwner σ_evm rateSlotE rateNewE) I daiSlotE
                  let daiOldS :=
                    Solm.EVM.storageLoad evmRate evmRate.executionEnv.codeOwner
                      (foldDaiSlot I)
                  have hdaiSlotEq : foldDaiSlot I = daiSlotE := by
                    simpa [daiSlotE] using foldDaiSlot_eq I
                  have hDaiWord : daiOldE = daiOldS := by
                    have h := accountMapEquiv_storage_findD hAccountsRate I.codeOwner
                      (foldDaiSlot I) ⟨0⟩
                    simpa [daiOldE, daiOldS, evmRate, evm0, initState, daiSlotE,
                      hdaiSlotEq, vatSlotWord, solcSlotWord, Solm.EVM.storageLoad,
                      State.lookupAccount, Account.lookupStorage,
                      storageStore_executionEnv] using h
                  let daiNewE := radWord + daiOldE
                  let daiNewS := radWord + daiOldS
                  by_cases hDaiNegE :
                      UInt256.slt radWord ⟨0⟩ = ⟨0⟩ ∨
                        UInt256.gt daiNewE daiOldE = ⟨0⟩
                  · by_cases hDaiPosE :
                        UInt256.sgt radWord ⟨0⟩ = ⟨0⟩ ∨
                          UInt256.lt daiNewE daiOldE = ⟨0⟩
                    · have hDaiNegSolc :
                          UInt256.slt radWord ⟨0⟩ = ⟨0⟩ ∨
                            UInt256.gt
                              (radWord + solcSlotWord
                                (sstoreAccountMap I.codeOwner σ_evm rateSlotE rateNewE)
                                I (solcMappingSlot ⟨5⟩ (foldUsrMaskedWord I)))
                              (solcSlotWord
                                (sstoreAccountMap I.codeOwner σ_evm rateSlotE rateNewE)
                                I (solcMappingSlot ⟨5⟩ (foldUsrMaskedWord I))) = ⟨0⟩ := by
                        simpa [daiOldE, daiNewE, daiSlotE] using hDaiNegE
                      have hDaiPosSolc :
                          UInt256.sgt radWord ⟨0⟩ = ⟨0⟩ ∨
                            UInt256.lt
                              (radWord + solcSlotWord
                                (sstoreAccountMap I.codeOwner σ_evm rateSlotE rateNewE)
                                I (solcMappingSlot ⟨5⟩ (foldUsrMaskedWord I)))
                              (solcSlotWord
                                (sstoreAccountMap I.codeOwner σ_evm rateSlotE rateNewE)
                                I (solcMappingSlot ⟨5⟩ (foldUsrMaskedWord I))) = ⟨0⟩ := by
                        simpa [daiOldE, daiNewE, daiSlotE] using hDaiPosE
                      obtain ⟨_, _, hafterDai⟩ := RD.vatFoldDaiStoreOk
                        (rad := radWord) (base := solcMappingSlot ⟨2⟩ (foldIlkWord I))
                        hafterArt hmemArt hDaiNegSolc hDaiPosSolc hperm
                      let evmDai := Solm.EVM.storageStore evmRate
                        evmRate.executionEnv.codeOwner (foldDaiSlot I) daiNewS
                      have hAccountsDai :
                          accountMapEquiv
                            (sstoreAccountMap I.codeOwner
                              (sstoreAccountMap I.codeOwner σ_evm rateSlotE rateNewE)
                              daiSlotE daiNewE)
                            evmDai.accountMap := by
                        simpa [evmDai, evmRate, evm0, initState,
                          storageStore_accountMap, storageStore_executionEnv,
                          daiSlotE, hdaiSlotEq, daiOldE, daiNewE, daiNewS, hDaiWord]
                          using accountMapEquiv_sstoreAccountMap I.codeOwner
                            daiSlotE daiNewE hAccountsRate
                      let debtOldE := solcSlotWord
                        (sstoreAccountMap I.codeOwner
                          (sstoreAccountMap I.codeOwner σ_evm rateSlotE rateNewE)
                          daiSlotE daiNewE) I ⟨7⟩
                      let debtOldS :=
                        Solm.EVM.storageLoad evmDai evmDai.executionEnv.codeOwner
                          foldDebtSlot
                      have hDebtWord : debtOldE = debtOldS := by
                        have h := accountMapEquiv_storage_findD hAccountsDai I.codeOwner
                          foldDebtSlot ⟨0⟩
                        simpa [debtOldE, debtOldS, evmDai, evmRate, evm0, initState,
                          foldDebtSlot, vatSlotWord, solcSlotWord,
                          Solm.EVM.storageLoad, State.lookupAccount,
                          Account.lookupStorage, storageStore_executionEnv] using h
                      let debtNewE := radWord + debtOldE
                      let debtNewS := radWord + debtOldS
                      by_cases hDebtNegE :
                          UInt256.slt radWord ⟨0⟩ = ⟨0⟩ ∨
                            UInt256.gt debtNewE debtOldE = ⟨0⟩
                      · by_cases hDebtPosE :
                            UInt256.sgt radWord ⟨0⟩ = ⟨0⟩ ∨
                              UInt256.lt debtNewE debtOldE = ⟨0⟩
                        · have hDebtNegSolc :
                              UInt256.slt radWord ⟨0⟩ = ⟨0⟩ ∨
                                UInt256.gt
                                  (radWord + solcSlotWord
                                    (sstoreAccountMap I.codeOwner
                                      (sstoreAccountMap I.codeOwner σ_evm rateSlotE
                                        rateNewE)
                                      daiSlotE daiNewE) I ⟨7⟩)
                                  (solcSlotWord
                                    (sstoreAccountMap I.codeOwner
                                      (sstoreAccountMap I.codeOwner σ_evm rateSlotE
                                        rateNewE)
                                      daiSlotE daiNewE) I ⟨7⟩) = ⟨0⟩ := by
                            simpa [debtOldE, debtNewE] using hDebtNegE
                          have hDebtPosSolc :
                              UInt256.sgt radWord ⟨0⟩ = ⟨0⟩ ∨
                                UInt256.lt
                                  (radWord + solcSlotWord
                                    (sstoreAccountMap I.codeOwner
                                      (sstoreAccountMap I.codeOwner σ_evm rateSlotE
                                        rateNewE)
                                      daiSlotE daiNewE) I ⟨7⟩)
                                  (solcSlotWord
                                    (sstoreAccountMap I.codeOwner
                                      (sstoreAccountMap I.codeOwner σ_evm rateSlotE
                                        rateNewE)
                                      daiSlotE daiNewE) I ⟨7⟩) = ⟨0⟩ := by
                            simpa [debtOldE, debtNewE] using hDebtPosE
                          obtain ⟨_, _, hafterDebt⟩ := RD.vatFoldDebtStoreReturnOk
                            (rad := radWord) (base := solcMappingSlot ⟨2⟩ (foldIlkWord I))
                            hafterDai hDebtNegSolc hDebtPosSolc hperm
                          let evmDebt := Solm.EVM.storageStore evmDai
                            evmDai.executionEnv.codeOwner foldDebtSlot debtNewS
                          have hAccountsDebt :
                              accountMapEquiv
                                (sstoreAccountMap I.codeOwner
                                  (sstoreAccountMap I.codeOwner
                                    (sstoreAccountMap I.codeOwner σ_evm rateSlotE
                                      rateNewE)
                                    daiSlotE daiNewE)
                                  ⟨7⟩ debtNewE)
                                evmDebt.accountMap := by
                            simpa [evmDebt, evmDai, evmRate, evm0, initState,
                              storageStore_accountMap, foldDebtSlot,
                              storageStore_executionEnv, debtOldE, debtNewE, debtNewS,
                              hDebtWord] using
                              accountMapEquiv_sstoreAccountMap I.codeOwner foldDebtSlot
                                debtNewE hAccountsDai
                          have hloadDaiS :
                              Solm.EVM.storageLoad
                                  (Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner
                                    (foldRateSlot I) rateNewS)
                                  evm0.executionEnv.codeOwner (foldDaiSlot I) =
                                daiOldS := by
                            simp [daiOldS, evmRate, rateSlotS,
                              storageStore_executionEnv]
                          have hDaiGuardNeg :
                              evalExpr? config
                                { contract := contract,
                                  locals := foldStoreDaiNew I rateNewS rad daiNewS }
                                (Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner
                                  (foldRateSlot I) rateNewS)
                                (eitherExpr (.binary .ge (.var "rad") (.intLit 0))
                                  (.binary .le (.var "daiNew")
                                    (.storage (daiRef (.var "u"))))) =
                                .ok (.bool true) := by
                            have hradv := vatEvalExpr_varInt (evm := evmRate)
                              (foldStoreDaiNew_get_rad I rateNewS rad daiNewS)
                            have hnewv := vatEvalExpr_varUInt256 (evm := evmRate)
                              (foldStoreDaiNew_get_daiNew I rateNewS rad daiNewS)
                            have hloadv :
                                evalExpr? config
                                  { contract := contract,
                                    locals := foldStoreDaiNew I rateNewS rad daiNewS }
                                  evmRate (.storage (daiRef (.var "u"))) =
                                .ok (.int (Int.ofNat daiOldS.toNat)) := by
                              rw [evalExpr_fold_dai_u evmRate I
                                (foldStoreDaiNew I rateNewS rad daiNewS)
                                (foldStoreDaiNew_get_u I rateNewS rad daiNewS)
                                (foldStoreDaiNew_dai I rateNewS rad daiNewS)]
                            have hcond := signedAddGuardNegCond_of_word
                              hradLo hradHi hradWord
                              (by simpa [daiNewS, daiNewE, hDaiWord] using hDaiNegE)
                            simpa [evmRate] using
                              evalSignedAddGuardNeg_true hradv hnewv hloadv hcond
                          have hDaiGuardPos :
                              evalExpr? config
                                { contract := contract,
                                  locals := foldStoreDaiNew I rateNewS rad daiNewS }
                                (Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner
                                  (foldRateSlot I) rateNewS)
                                (eitherExpr (.binary .le (.var "rad") (.intLit 0))
                                  (.binary .ge (.var "daiNew")
                                    (.storage (daiRef (.var "u"))))) =
                                .ok (.bool true) := by
                            have hradv := vatEvalExpr_varInt (evm := evmRate)
                              (foldStoreDaiNew_get_rad I rateNewS rad daiNewS)
                            have hnewv := vatEvalExpr_varUInt256 (evm := evmRate)
                              (foldStoreDaiNew_get_daiNew I rateNewS rad daiNewS)
                            have hloadv :
                                evalExpr? config
                                  { contract := contract,
                                    locals := foldStoreDaiNew I rateNewS rad daiNewS }
                                  evmRate (.storage (daiRef (.var "u"))) =
                                .ok (.int (Int.ofNat daiOldS.toNat)) := by
                              rw [evalExpr_fold_dai_u evmRate I
                                (foldStoreDaiNew I rateNewS rad daiNewS)
                                (foldStoreDaiNew_get_u I rateNewS rad daiNewS)
                                (foldStoreDaiNew_dai I rateNewS rad daiNewS)]
                            have hcond := signedAddGuardPosCond_of_word
                              hradLo hradHi hradWord
                              (by simpa [daiNewS, daiNewE, hDaiWord] using hDaiPosE)
                            simpa [evmRate] using
                              evalSignedAddGuardPos_true hradv hnewv hloadv hcond
                          have hloadDebtS :
                              Solm.EVM.storageLoad
                                  (Solm.EVM.storageStore
                                    (Solm.EVM.storageStore evm0
                                      evm0.executionEnv.codeOwner (foldRateSlot I)
                                      rateNewS)
                                    evm0.executionEnv.codeOwner (foldDaiSlot I) daiNewS)
                                  evm0.executionEnv.codeOwner foldDebtSlot = debtOldS := by
                            simp [debtOldS, evmDai, evmRate, rateSlotS,
                              storageStore_executionEnv]
                          have hDebtGuardNeg :
                              evalExpr? config
                                { contract := contract,
                                  locals :=
                                    foldStoreDebtNew I rateNewS rad daiNewS debtNewS }
                                (Solm.EVM.storageStore
                                  (Solm.EVM.storageStore evm0
                                    evm0.executionEnv.codeOwner (foldRateSlot I)
                                    rateNewS)
                                  evm0.executionEnv.codeOwner (foldDaiSlot I) daiNewS)
                                (eitherExpr (.binary .ge (.var "rad") (.intLit 0))
                                  (.binary .le (.var "debtNew") (.storage debtRef))) =
                                .ok (.bool true) := by
                            have hradv := vatEvalExpr_varInt (evm := evmDai)
                              (foldStoreDebtNew_get_rad I rateNewS rad daiNewS debtNewS)
                            have hnewv := vatEvalExpr_varUInt256 (evm := evmDai)
                              (foldStoreDebtNew_get_debtNew I rateNewS rad daiNewS
                                debtNewS)
                            have hloadv :
                                evalExpr? config
                                  { contract := contract,
                                    locals :=
                                      foldStoreDebtNew I rateNewS rad daiNewS debtNewS }
                                  evmDai (.storage debtRef) =
                                .ok (.int (Int.ofNat debtOldS.toNat)) := by
                              rw [evalExpr_fold_debt evmDai
                                (foldStoreDebtNew I rateNewS rad daiNewS debtNewS)
                                (foldStoreDebtNew_debt I rateNewS rad daiNewS debtNewS)]
                            have hcond := signedAddGuardNegCond_of_word
                              hradLo hradHi hradWord
                              (by simpa [debtNewS, debtNewE, hDebtWord] using
                                hDebtNegE)
                            simpa [evmDai, evmRate, storageStore_executionEnv] using
                              evalSignedAddGuardNeg_true hradv hnewv hloadv hcond
                          have hDebtGuardPos :
                              evalExpr? config
                                { contract := contract,
                                  locals :=
                                    foldStoreDebtNew I rateNewS rad daiNewS debtNewS }
                                (Solm.EVM.storageStore
                                  (Solm.EVM.storageStore evm0
                                    evm0.executionEnv.codeOwner (foldRateSlot I)
                                    rateNewS)
                                  evm0.executionEnv.codeOwner (foldDaiSlot I) daiNewS)
                                (eitherExpr (.binary .le (.var "rad") (.intLit 0))
                                  (.binary .ge (.var "debtNew") (.storage debtRef))) =
                                .ok (.bool true) := by
                            have hradv := vatEvalExpr_varInt (evm := evmDai)
                              (foldStoreDebtNew_get_rad I rateNewS rad daiNewS debtNewS)
                            have hnewv := vatEvalExpr_varUInt256 (evm := evmDai)
                              (foldStoreDebtNew_get_debtNew I rateNewS rad daiNewS
                                debtNewS)
                            have hloadv :
                                evalExpr? config
                                  { contract := contract,
                                    locals :=
                                      foldStoreDebtNew I rateNewS rad daiNewS debtNewS }
                                  evmDai (.storage debtRef) =
                                .ok (.int (Int.ofNat debtOldS.toNat)) := by
                              rw [evalExpr_fold_debt evmDai
                                (foldStoreDebtNew I rateNewS rad daiNewS debtNewS)
                                (foldStoreDebtNew_debt I rateNewS rad daiNewS debtNewS)]
                            have hcond := signedAddGuardPosCond_of_word
                              hradLo hradHi hradWord
                              (by simpa [debtNewS, debtNewE, hDebtWord] using
                                hDebtPosE)
                            simpa [evmDai, evmRate, storageStore_executionEnv] using
                              evalSignedAddGuardPos_true hradv hnewv hloadv hcond
                          have hbody := vatFoldSourceSuccess evm0 I hwv hsz100
                            hguardAuth hguardLive hloadRateS (by rfl)
                            hRateGuardNeg hRateGuardPos hloadArtS (by rfl)
                            hradLo hradHi hmulGuardMax hmulGuard hloadDaiS
                            hradWord (by rfl) hDaiGuardNeg hDaiGuardPos hloadDebtS
                            (by rfl) hDebtGuardNeg hDebtGuardPos
                          have hDebtWordSimple :
                              solcSlotWord
                                (sstoreAccountMap I.codeOwner
                                  (sstoreAccountMap I.codeOwner σ_evm rateSlotE rateNewE)
                                  daiSlotE daiNewE) I ⟨7⟩ = debtOldS := by
                            simpa [debtOldE] using hDebtWord
                          have hDebtWordFinal :
                              solcSlotWord
                                (sstoreAccountMap I.codeOwner
                                  (sstoreAccountMap I.codeOwner σ_evm rateSlotE rateNewE)
                                  (solcMappingSlot ⟨5⟩ (foldUsrMaskedWord I))
                                  (radWord + daiOldS)) I ⟨7⟩ = debtOldS := by
                            simpa [daiSlotE, daiNewE, hDaiWord] using hDebtWordSimple
                          exact vatFoldFinishSuccess hcode hdispatch hdecode hbody
                            (by
                              simp [foldPostState, evm0, initState,
                                storageStore_createdAccounts])
                            (by
                              simpa [foldPostState, evmDebt, evmDai, evmRate,
                                storageStore_executionEnv, rateSlotS, daiSlotE, hdaiSlotEq,
                                daiOldE, daiNewE, daiNewS, hDaiWord, debtOldE,
                                debtNewE, debtNewS, hDebtWordFinal] using
                                hAccountsDebt)
                            hafterDebt
                        · have hDebtNegSolc :
                              UInt256.slt radWord ⟨0⟩ = ⟨0⟩ ∨
                                UInt256.gt
                                  (radWord + solcSlotWord
                                    (sstoreAccountMap I.codeOwner
                                      (sstoreAccountMap I.codeOwner σ_evm rateSlotE
                                        rateNewE)
                                      daiSlotE daiNewE) I ⟨7⟩)
                                  (solcSlotWord
                                    (sstoreAccountMap I.codeOwner
                                      (sstoreAccountMap I.codeOwner σ_evm rateSlotE
                                        rateNewE)
                                      daiSlotE daiNewE) I ⟨7⟩) = ⟨0⟩ := by
                            simpa [debtOldE, debtNewE] using hDebtNegE
                          have hDebtPosFailSolc :
                              ¬ (UInt256.sgt radWord ⟨0⟩ = ⟨0⟩ ∨
                                UInt256.lt
                                  (radWord + solcSlotWord
                                    (sstoreAccountMap I.codeOwner
                                      (sstoreAccountMap I.codeOwner σ_evm rateSlotE
                                        rateNewE)
                                      daiSlotE daiNewE) I ⟨7⟩)
                                  (solcSlotWord
                                    (sstoreAccountMap I.codeOwner
                                      (sstoreAccountMap I.codeOwner σ_evm rateSlotE
                                        rateNewE)
                                      daiSlotE daiNewE) I ⟨7⟩) = ⟨0⟩) := by
                            intro h
                            exact hDebtPosE (by simpa [debtOldE, debtNewE] using h)
                          have hrev := RD.vatFoldDebtStoreRevert
                            (rad := radWord) (base := solcMappingSlot ⟨2⟩ (foldIlkWord I))
                            hafterDai (Or.inr ⟨hDebtNegSolc, hDebtPosFailSolc⟩)
                          have hloadDaiS :
                              Solm.EVM.storageLoad
                                  (Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner
                                    (foldRateSlot I) rateNewS)
                                  evm0.executionEnv.codeOwner (foldDaiSlot I) =
                                daiOldS := by
                            simp [daiOldS, evmRate, rateSlotS,
                              storageStore_executionEnv]
                          have hDaiGuardNeg :
                              evalExpr? config
                                { contract := contract,
                                  locals := foldStoreDaiNew I rateNewS rad daiNewS }
                                evmRate
                                (eitherExpr (.binary .ge (.var "rad") (.intLit 0))
                                  (.binary .le (.var "daiNew")
                                    (.storage (daiRef (.var "u"))))) =
                                .ok (.bool true) := by
                            have hradv := vatEvalExpr_varInt (evm := evmRate)
                              (foldStoreDaiNew_get_rad I rateNewS rad daiNewS)
                            have hnewv := vatEvalExpr_varUInt256 (evm := evmRate)
                              (foldStoreDaiNew_get_daiNew I rateNewS rad daiNewS)
                            have hloadv :
                                evalExpr? config
                                  { contract := contract,
                                    locals := foldStoreDaiNew I rateNewS rad daiNewS }
                                  evmRate (.storage (daiRef (.var "u"))) =
                                .ok (.int (Int.ofNat daiOldS.toNat)) := by
                              rw [evalExpr_fold_dai_u evmRate I
                                (foldStoreDaiNew I rateNewS rad daiNewS)
                                (foldStoreDaiNew_get_u I rateNewS rad daiNewS)
                                (foldStoreDaiNew_dai I rateNewS rad daiNewS)]
                            exact evalSignedAddGuardNeg_true hradv hnewv hloadv
                              (signedAddGuardNegCond_of_word hradLo hradHi hradWord
                                (by simpa [daiNewS, daiNewE, hDaiWord] using hDaiNegE))
                          have hDaiGuardPos :
                              evalExpr? config
                                { contract := contract,
                                  locals := foldStoreDaiNew I rateNewS rad daiNewS }
                                evmRate
                                (eitherExpr (.binary .le (.var "rad") (.intLit 0))
                                  (.binary .ge (.var "daiNew")
                                    (.storage (daiRef (.var "u"))))) =
                                .ok (.bool true) := by
                            have hradv := vatEvalExpr_varInt (evm := evmRate)
                              (foldStoreDaiNew_get_rad I rateNewS rad daiNewS)
                            have hnewv := vatEvalExpr_varUInt256 (evm := evmRate)
                              (foldStoreDaiNew_get_daiNew I rateNewS rad daiNewS)
                            have hloadv :
                                evalExpr? config
                                  { contract := contract,
                                    locals := foldStoreDaiNew I rateNewS rad daiNewS }
                                  evmRate (.storage (daiRef (.var "u"))) =
                                .ok (.int (Int.ofNat daiOldS.toNat)) := by
                              rw [evalExpr_fold_dai_u evmRate I
                                (foldStoreDaiNew I rateNewS rad daiNewS)
                                (foldStoreDaiNew_get_u I rateNewS rad daiNewS)
                                (foldStoreDaiNew_dai I rateNewS rad daiNewS)]
                            exact evalSignedAddGuardPos_true hradv hnewv hloadv
                              (signedAddGuardPosCond_of_word hradLo hradHi hradWord
                                (by simpa [daiNewS, daiNewE, hDaiWord] using hDaiPosE))
                          have hdaiOk := vatFoldDaiAddOk evmRate I
                            (by simpa [evmRate, storageStore_executionEnv] using hloadDaiS)
                            hradWord (by rfl) hDaiGuardNeg hDaiGuardPos
                          have hdaiAssign := vatFoldAssignDaiOk evmRate I
                            (rateNew := rateNewS) (rad := rad) (daiNew := daiNewS)
                          have hloadDebtS :
                              Solm.EVM.storageLoad evmDai evmDai.executionEnv.codeOwner
                                foldDebtSlot = debtOldS := by
                            simp [debtOldS]
                          have hDebtGuardNeg :
                              evalExpr? config
                                { contract := contract,
                                  locals :=
                                    foldStoreDebtNew I rateNewS rad daiNewS debtNewS }
                                evmDai
                                (eitherExpr (.binary .ge (.var "rad") (.intLit 0))
                                  (.binary .le (.var "debtNew") (.storage debtRef))) =
                                .ok (.bool true) := by
                            have hradv := vatEvalExpr_varInt (evm := evmDai)
                              (foldStoreDebtNew_get_rad I rateNewS rad daiNewS debtNewS)
                            have hnewv := vatEvalExpr_varUInt256 (evm := evmDai)
                              (foldStoreDebtNew_get_debtNew I rateNewS rad daiNewS
                                debtNewS)
                            have hloadv :
                                evalExpr? config
                                  { contract := contract,
                                    locals :=
                                      foldStoreDebtNew I rateNewS rad daiNewS debtNewS }
                                  evmDai (.storage debtRef) =
                                .ok (.int (Int.ofNat debtOldS.toNat)) := by
                              rw [evalExpr_fold_debt evmDai
                                (foldStoreDebtNew I rateNewS rad daiNewS debtNewS)
                                (foldStoreDebtNew_debt I rateNewS rad daiNewS debtNewS)]
                            exact evalSignedAddGuardNeg_true hradv hnewv hloadv
                              (signedAddGuardNegCond_of_word hradLo hradHi hradWord
                                (by simpa [debtNewS, debtNewE, hDebtWord] using
                                  hDebtNegE))
                          have hDebtGuardPos :
                              evalExpr? config
                                { contract := contract,
                                  locals :=
                                    foldStoreDebtNew I rateNewS rad daiNewS debtNewS }
                                evmDai
                                (eitherExpr (.binary .le (.var "rad") (.intLit 0))
                                  (.binary .ge (.var "debtNew") (.storage debtRef))) =
                                .ok (.bool false) := by
                            have hradv := vatEvalExpr_varInt (evm := evmDai)
                              (foldStoreDebtNew_get_rad I rateNewS rad daiNewS debtNewS)
                            have hnewv := vatEvalExpr_varUInt256 (evm := evmDai)
                              (foldStoreDebtNew_get_debtNew I rateNewS rad daiNewS
                                debtNewS)
                            have hloadv :
                                evalExpr? config
                                  { contract := contract,
                                    locals :=
                                      foldStoreDebtNew I rateNewS rad daiNewS debtNewS }
                                  evmDai (.storage debtRef) =
                                .ok (.int (Int.ofNat debtOldS.toNat)) := by
                              rw [evalExpr_fold_debt evmDai
                                (foldStoreDebtNew I rateNewS rad daiNewS debtNewS)
                                (foldStoreDebtNew_debt I rateNewS rad daiNewS debtNewS)]
                            exact evalSignedAddGuardPos_false hradv hnewv hloadv
                              (signedAddGuardPosFalseCond_of_word hradLo hradHi hradWord
                                (by
                                  intro h
                                  exact hDebtPosE
                                    (by simpa [debtNewS, debtNewE, hDebtWord] using h)))
                          have hdebtRev := vatFoldDebtAddRevertGuardPos evmDai I
                            hloadDebtS hradWord (by rfl) hDebtGuardNeg hDebtGuardPos
                          have hbody := vatFoldSourceRevertAfterDebtBlock evm0 evmRate
                            evmDai I hwv hguardAuth hguardLive hrateBlock hradBlock
                            hdaiOk hdaiAssign hdebtRev
                          exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody
                      · have hDebtNegFailSolc :
                            ¬ (UInt256.slt radWord ⟨0⟩ = ⟨0⟩ ∨
                              UInt256.gt
                                (radWord + solcSlotWord
                                  (sstoreAccountMap I.codeOwner
                                    (sstoreAccountMap I.codeOwner σ_evm rateSlotE
                                      rateNewE)
                                    daiSlotE daiNewE) I ⟨7⟩)
                                (solcSlotWord
                                  (sstoreAccountMap I.codeOwner
                                    (sstoreAccountMap I.codeOwner σ_evm rateSlotE
                                      rateNewE)
                                    daiSlotE daiNewE) I ⟨7⟩) = ⟨0⟩) := by
                          intro h
                          exact hDebtNegE (by simpa [debtOldE, debtNewE] using h)
                        have hrev := RD.vatFoldDebtStoreRevert
                          (rad := radWord) (base := solcMappingSlot ⟨2⟩ (foldIlkWord I))
                          hafterDai (Or.inl hDebtNegFailSolc)
                        have hloadDaiS :
                            Solm.EVM.storageLoad
                                (Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner
                                  (foldRateSlot I) rateNewS)
                                evm0.executionEnv.codeOwner (foldDaiSlot I) = daiOldS := by
                          simp [daiOldS, evmRate, rateSlotS, storageStore_executionEnv]
                        have hDaiGuardNeg :
                            evalExpr? config
                              { contract := contract,
                                locals := foldStoreDaiNew I rateNewS rad daiNewS } evmRate
                              (eitherExpr (.binary .ge (.var "rad") (.intLit 0))
                                (.binary .le (.var "daiNew")
                                  (.storage (daiRef (.var "u"))))) =
                              .ok (.bool true) := by
                          have hradv := vatEvalExpr_varInt (evm := evmRate)
                            (foldStoreDaiNew_get_rad I rateNewS rad daiNewS)
                          have hnewv := vatEvalExpr_varUInt256 (evm := evmRate)
                            (foldStoreDaiNew_get_daiNew I rateNewS rad daiNewS)
                          have hloadv :
                              evalExpr? config
                                { contract := contract,
                                  locals := foldStoreDaiNew I rateNewS rad daiNewS }
                                evmRate (.storage (daiRef (.var "u"))) =
                              .ok (.int (Int.ofNat daiOldS.toNat)) := by
                            rw [evalExpr_fold_dai_u evmRate I
                              (foldStoreDaiNew I rateNewS rad daiNewS)
                              (foldStoreDaiNew_get_u I rateNewS rad daiNewS)
                              (foldStoreDaiNew_dai I rateNewS rad daiNewS)]
                          exact evalSignedAddGuardNeg_true hradv hnewv hloadv
                            (signedAddGuardNegCond_of_word hradLo hradHi hradWord
                              (by simpa [daiNewS, daiNewE, hDaiWord] using hDaiNegE))
                        have hDaiGuardPos :
                            evalExpr? config
                              { contract := contract,
                                locals := foldStoreDaiNew I rateNewS rad daiNewS } evmRate
                              (eitherExpr (.binary .le (.var "rad") (.intLit 0))
                                (.binary .ge (.var "daiNew")
                                  (.storage (daiRef (.var "u"))))) =
                              .ok (.bool true) := by
                          have hradv := vatEvalExpr_varInt (evm := evmRate)
                            (foldStoreDaiNew_get_rad I rateNewS rad daiNewS)
                          have hnewv := vatEvalExpr_varUInt256 (evm := evmRate)
                            (foldStoreDaiNew_get_daiNew I rateNewS rad daiNewS)
                          have hloadv :
                              evalExpr? config
                                { contract := contract,
                                  locals := foldStoreDaiNew I rateNewS rad daiNewS }
                                evmRate (.storage (daiRef (.var "u"))) =
                              .ok (.int (Int.ofNat daiOldS.toNat)) := by
                            rw [evalExpr_fold_dai_u evmRate I
                              (foldStoreDaiNew I rateNewS rad daiNewS)
                              (foldStoreDaiNew_get_u I rateNewS rad daiNewS)
                              (foldStoreDaiNew_dai I rateNewS rad daiNewS)]
                          exact evalSignedAddGuardPos_true hradv hnewv hloadv
                            (signedAddGuardPosCond_of_word hradLo hradHi hradWord
                              (by simpa [daiNewS, daiNewE, hDaiWord] using hDaiPosE))
                        have hdaiOk := vatFoldDaiAddOk evmRate I
                          (by simpa [evmRate, storageStore_executionEnv] using hloadDaiS)
                          hradWord (by rfl) hDaiGuardNeg hDaiGuardPos
                        have hdaiAssign := vatFoldAssignDaiOk evmRate I
                          (rateNew := rateNewS) (rad := rad) (daiNew := daiNewS)
                        have hloadDebtS :
                            Solm.EVM.storageLoad evmDai evmDai.executionEnv.codeOwner
                              foldDebtSlot = debtOldS := by
                          simp [debtOldS]
                        have hDebtGuardNeg :
                            evalExpr? config
                              { contract := contract,
                                locals :=
                                  foldStoreDebtNew I rateNewS rad daiNewS debtNewS }
                              evmDai
                              (eitherExpr (.binary .ge (.var "rad") (.intLit 0))
                                (.binary .le (.var "debtNew") (.storage debtRef))) =
                              .ok (.bool false) := by
                          have hradv := vatEvalExpr_varInt (evm := evmDai)
                            (foldStoreDebtNew_get_rad I rateNewS rad daiNewS debtNewS)
                          have hnewv := vatEvalExpr_varUInt256 (evm := evmDai)
                            (foldStoreDebtNew_get_debtNew I rateNewS rad daiNewS
                              debtNewS)
                          have hloadv :
                              evalExpr? config
                                { contract := contract,
                                  locals :=
                                    foldStoreDebtNew I rateNewS rad daiNewS debtNewS }
                                evmDai (.storage debtRef) =
                              .ok (.int (Int.ofNat debtOldS.toNat)) := by
                            rw [evalExpr_fold_debt evmDai
                              (foldStoreDebtNew I rateNewS rad daiNewS debtNewS)
                              (foldStoreDebtNew_debt I rateNewS rad daiNewS debtNewS)]
                          exact evalSignedAddGuardNeg_false hradv hnewv hloadv
                            (signedAddGuardNegFalseCond_of_word hradLo hradHi hradWord
                              (by
                                intro h
                                exact hDebtNegE
                                  (by simpa [debtNewS, debtNewE, hDebtWord] using h)))
                        have hdebtRev := vatFoldDebtAddRevertGuardNeg evmDai I
                          hloadDebtS hradWord (by rfl) hDebtGuardNeg
                        have hbody := vatFoldSourceRevertAfterDebtBlock evm0 evmRate
                          evmDai I hwv hguardAuth hguardLive hrateBlock hradBlock
                          hdaiOk hdaiAssign hdebtRev
                        exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody
                    · have hDaiNegSolc :
                          UInt256.slt radWord ⟨0⟩ = ⟨0⟩ ∨
                            UInt256.gt
                              (radWord + solcSlotWord
                                (sstoreAccountMap I.codeOwner σ_evm rateSlotE rateNewE)
                                I (solcMappingSlot ⟨5⟩ (foldUsrMaskedWord I)))
                              (solcSlotWord
                                (sstoreAccountMap I.codeOwner σ_evm rateSlotE rateNewE)
                                I (solcMappingSlot ⟨5⟩ (foldUsrMaskedWord I))) = ⟨0⟩ := by
                        simpa [daiOldE, daiNewE, daiSlotE] using hDaiNegE
                      have hDaiPosFailSolc :
                          ¬ (UInt256.sgt radWord ⟨0⟩ = ⟨0⟩ ∨
                            UInt256.lt
                              (radWord + solcSlotWord
                                (sstoreAccountMap I.codeOwner σ_evm rateSlotE rateNewE)
                                I (solcMappingSlot ⟨5⟩ (foldUsrMaskedWord I)))
                              (solcSlotWord
                                (sstoreAccountMap I.codeOwner σ_evm rateSlotE rateNewE)
                                I (solcMappingSlot ⟨5⟩ (foldUsrMaskedWord I))) = ⟨0⟩) := by
                        intro h
                        exact hDaiPosE (by simpa [daiOldE, daiNewE, daiSlotE] using h)
                      have hrev := RD.vatFoldDaiStoreRevert
                        (rad := radWord) (base := solcMappingSlot ⟨2⟩ (foldIlkWord I))
                        hafterArt hmemArt (Or.inr ⟨hDaiNegSolc, hDaiPosFailSolc⟩)
                      have hloadDaiS :
                          Solm.EVM.storageLoad
                              (Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner
                                (foldRateSlot I) rateNewS)
                              evm0.executionEnv.codeOwner (foldDaiSlot I) = daiOldS := by
                        simp [daiOldS, evmRate, rateSlotS, storageStore_executionEnv]
                      have hDaiGuardNeg :
                          evalExpr? config
                            { contract := contract,
                              locals := foldStoreDaiNew I rateNewS rad daiNewS } evmRate
                            (eitherExpr (.binary .ge (.var "rad") (.intLit 0))
                              (.binary .le (.var "daiNew")
                                (.storage (daiRef (.var "u"))))) =
                            .ok (.bool true) := by
                        have hradv := vatEvalExpr_varInt (evm := evmRate)
                          (foldStoreDaiNew_get_rad I rateNewS rad daiNewS)
                        have hnewv := vatEvalExpr_varUInt256 (evm := evmRate)
                          (foldStoreDaiNew_get_daiNew I rateNewS rad daiNewS)
                        have hloadv :
                            evalExpr? config
                              { contract := contract,
                                locals := foldStoreDaiNew I rateNewS rad daiNewS }
                              evmRate (.storage (daiRef (.var "u"))) =
                            .ok (.int (Int.ofNat daiOldS.toNat)) := by
                          rw [evalExpr_fold_dai_u evmRate I
                            (foldStoreDaiNew I rateNewS rad daiNewS)
                            (foldStoreDaiNew_get_u I rateNewS rad daiNewS)
                            (foldStoreDaiNew_dai I rateNewS rad daiNewS)]
                        exact evalSignedAddGuardNeg_true hradv hnewv hloadv
                          (signedAddGuardNegCond_of_word hradLo hradHi hradWord
                            (by simpa [daiNewS, daiNewE, hDaiWord] using hDaiNegE))
                      have hDaiGuardPos :
                          evalExpr? config
                            { contract := contract,
                              locals := foldStoreDaiNew I rateNewS rad daiNewS } evmRate
                            (eitherExpr (.binary .le (.var "rad") (.intLit 0))
                              (.binary .ge (.var "daiNew")
                                (.storage (daiRef (.var "u"))))) =
                            .ok (.bool false) := by
                        have hradv := vatEvalExpr_varInt (evm := evmRate)
                          (foldStoreDaiNew_get_rad I rateNewS rad daiNewS)
                        have hnewv := vatEvalExpr_varUInt256 (evm := evmRate)
                          (foldStoreDaiNew_get_daiNew I rateNewS rad daiNewS)
                        have hloadv :
                            evalExpr? config
                              { contract := contract,
                                locals := foldStoreDaiNew I rateNewS rad daiNewS }
                              evmRate (.storage (daiRef (.var "u"))) =
                            .ok (.int (Int.ofNat daiOldS.toNat)) := by
                          rw [evalExpr_fold_dai_u evmRate I
                            (foldStoreDaiNew I rateNewS rad daiNewS)
                            (foldStoreDaiNew_get_u I rateNewS rad daiNewS)
                            (foldStoreDaiNew_dai I rateNewS rad daiNewS)]
                        exact evalSignedAddGuardPos_false hradv hnewv hloadv
                          (signedAddGuardPosFalseCond_of_word hradLo hradHi hradWord
                            (by
                              intro h
                              exact hDaiPosE
                                (by simpa [daiNewS, daiNewE, hDaiWord] using h)))
                      have hdaiRev := vatFoldDaiAddRevertGuardPos evmRate I
                        (by simpa [evmRate, storageStore_executionEnv] using hloadDaiS)
                        hradWord (by rfl) hDaiGuardNeg hDaiGuardPos
                      have hbody := vatFoldSourceRevertAfterDaiBlock evm0 evmRate I hwv
                        hguardAuth hguardLive hrateBlock hradBlock hdaiRev
                      exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody
                  · have hDaiNegFailSolc :
                        ¬ (UInt256.slt radWord ⟨0⟩ = ⟨0⟩ ∨
                          UInt256.gt
                            (radWord + solcSlotWord
                              (sstoreAccountMap I.codeOwner σ_evm rateSlotE rateNewE)
                              I (solcMappingSlot ⟨5⟩ (foldUsrMaskedWord I)))
                            (solcSlotWord
                              (sstoreAccountMap I.codeOwner σ_evm rateSlotE rateNewE)
                              I (solcMappingSlot ⟨5⟩ (foldUsrMaskedWord I))) = ⟨0⟩) := by
                      intro h
                      exact hDaiNegE (by simpa [daiOldE, daiNewE, daiSlotE] using h)
                    have hrev := RD.vatFoldDaiStoreRevert
                      (rad := radWord) (base := solcMappingSlot ⟨2⟩ (foldIlkWord I))
                      hafterArt hmemArt (Or.inl hDaiNegFailSolc)
                    have hloadDaiS :
                        Solm.EVM.storageLoad
                            (Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner
                              (foldRateSlot I) rateNewS)
                            evm0.executionEnv.codeOwner (foldDaiSlot I) = daiOldS := by
                      simp [daiOldS, evmRate, rateSlotS, storageStore_executionEnv]
                    have hDaiGuardNeg :
                        evalExpr? config
                          { contract := contract,
                            locals := foldStoreDaiNew I rateNewS rad daiNewS } evmRate
                          (eitherExpr (.binary .ge (.var "rad") (.intLit 0))
                            (.binary .le (.var "daiNew")
                              (.storage (daiRef (.var "u"))))) =
                          .ok (.bool false) := by
                      have hradv := vatEvalExpr_varInt (evm := evmRate)
                        (foldStoreDaiNew_get_rad I rateNewS rad daiNewS)
                      have hnewv := vatEvalExpr_varUInt256 (evm := evmRate)
                        (foldStoreDaiNew_get_daiNew I rateNewS rad daiNewS)
                      have hloadv :
                          evalExpr? config
                            { contract := contract,
                              locals := foldStoreDaiNew I rateNewS rad daiNewS }
                            evmRate (.storage (daiRef (.var "u"))) =
                          .ok (.int (Int.ofNat daiOldS.toNat)) := by
                        rw [evalExpr_fold_dai_u evmRate I
                          (foldStoreDaiNew I rateNewS rad daiNewS)
                          (foldStoreDaiNew_get_u I rateNewS rad daiNewS)
                          (foldStoreDaiNew_dai I rateNewS rad daiNewS)]
                      exact evalSignedAddGuardNeg_false hradv hnewv hloadv
                        (signedAddGuardNegFalseCond_of_word hradLo hradHi hradWord
                          (by
                            intro h
                            exact hDaiNegE
                              (by simpa [daiNewS, daiNewE, hDaiWord] using h)))
                    have hdaiRev := vatFoldDaiAddRevertGuardNeg evmRate I
                      (by simpa [evmRate, storageStore_executionEnv] using hloadDaiS)
                      hradWord (by rfl) hDaiGuardNeg
                    have hbody := vatFoldSourceRevertAfterDaiBlock evm0 evmRate I hwv
                      hguardAuth hguardLive hrateBlock hradBlock hdaiRev
                    exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody
              · have hMulFailSolc :
                    ¬ (foldRateWord I = ⟨0⟩ ∨
                      UInt256.eq
                        (UInt256.sdiv
                          (UInt256.mul (foldRateWord I)
                            (solcSlotWord
                              (sstoreAccountMap I.codeOwner σ_evm rateSlotE rateNewE)
                              I (solcMappingSlot ⟨2⟩ (foldIlkWord I))))
                          (foldRateWord I))
                        (solcSlotWord
                          (sstoreAccountMap I.codeOwner σ_evm rateSlotE rateNewE)
                          I (solcMappingSlot ⟨2⟩ (foldIlkWord I))) ≠ ⟨0⟩) := by
                  intro h
                  exact hMulE (by simpa [artOldE, artSlotE] using h)
                have hArtNonzeroE : artOldE ≠ ⟨0⟩ := by
                  intro hzero
                  exact hMulE (fold_mul_word_guard_true_of_art_zero I hzero)
                have hrev := RD.vatFoldArtMulRevert
                  (cA := cA) (gh := gh) (bl := bl) (σInit := σ_evm)
                  (σ := sstoreAccountMap I.codeOwner σ_evm rateSlotE rateNewE)
                  (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
                  (sel := vatSelWord I) hafterRate
                  (Or.inr ⟨hArtMaxSolc, hMulFailSolc⟩)
                by_cases hbadRange :
                    Int.ofNat artOldS.toNat * foldRateInt I < -((2 : Int) ^ 255) ∨
                      Int.ofNat artOldS.toNat * foldRateInt I ≥ (2 : Int) ^ 255
                · have hradRevert := vatFoldRadMulRevertRange evmRate I
                    (rateNew := rateNewS) (artOld := artOldS) hsz100 (by rfl)
                    hbadRange
                  have hbody := vatFoldSourceRevertAfterRadBlock evm0 evmRate I hwv
                    hguardAuth hguardLive
                    (by
                      simpa [evmRate, rateSlotS] using
                        vatFoldRateAddAssignOk evm0 I hsz100 hloadRateS (by rfl)
                          hRateGuardNeg hRateGuardPos)
                    hradRevert
                  exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody
                · have hRateWordNe : foldRateWord I ≠ ⟨0⟩ := by
                    intro hzero
                    exact hMulE (Or.inl hzero)
                  have hprodHiS :
                      Int.ofNat artOldS.toNat * foldRateInt I < (2 : Int) ^ 255 := by
                    exact not_le.mp (fun hhi => hbadRange (Or.inr hhi))
                  have hprodHiE :
                      Int.ofNat artOldE.toNat * foldRateInt I < (2 : Int) ^ 255 := by
                    simpa [hArtWord] using hprodHiS
                  by_cases hrateLow : (foldRateWord I).toNat < EVM.twoPow 255
                  · have hguardTrue :=
                      fold_mul_word_guard_true_of_range_pos I (art := artOldE)
                        hrateLow hRateWordNe hprodHiE
                    exact False.elim (hMulE hguardTrue)
                  · have hprodLoS :
                        -((2 : Int) ^ 255) ≤ Int.ofNat artOldS.toNat * foldRateInt I := by
                      exact not_lt.mp (fun hlo => hbadRange (Or.inl hlo))
                    have hprodLoE :
                        -((2 : Int) ^ 255) ≤ Int.ofNat artOldE.toNat * foldRateInt I := by
                      simpa [hArtWord] using hprodLoS
                    have hguardTrue :=
                      fold_mul_word_guard_true_of_range_neg I (art := artOldE)
                        (not_lt.mp hrateLow) hArtNonzeroE hprodLoE
                    exact False.elim (hMulE hguardTrue)
            · have hArtMaxFailSolc :
                  ¬ UInt256.slt
                    (solcSlotWord (sstoreAccountMap I.codeOwner σ_evm rateSlotE rateNewE)
                      I (solcMappingSlot ⟨2⟩ (foldIlkWord I))) ⟨0⟩ = ⟨0⟩ := by
                intro h
                exact hArtMaxE (by simpa [artOldE, artSlotE] using h)
              have hArtMaxSNe : UInt256.slt artOldS ⟨0⟩ ≠ ⟨0⟩ := by
                intro h
                exact hArtMaxE (by simpa [hArtWord] using h)
              have hradRevert := vatFoldRadMulRevertMax evmRate I
                (rateNew := rateNewS) (artOld := artOldS) hsz100
                (by rfl) (uintWordGtMaxInt256_of_slt_ne_zero hArtMaxSNe)
              have hbody := vatFoldSourceRevertAfterRadBlock evm0 evmRate I hwv
                hguardAuth hguardLive
                (by
                  simpa [evmRate, rateSlotS] using
                    vatFoldRateAddAssignOk evm0 I hsz100 hloadRateS (by rfl)
                      hRateGuardNeg hRateGuardPos)
                hradRevert
              have hrev := RD.vatFoldArtMulRevert
                (cA := cA) (gh := gh) (bl := bl) (σInit := σ_evm)
                (σ := sstoreAccountMap I.codeOwner σ_evm rateSlotE rateNewE)
                (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
                (sel := vatSelWord I) hafterRate (Or.inl hArtMaxFailSolc)
              exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody
          · have hRateNegSolc :
                UInt256.slt (foldRateWord I) ⟨0⟩ = ⟨0⟩ ∨
                  UInt256.gt
                    (foldRateWord I +
                      solcSlotWord σ_evm I
                        (solcMappingSlot ⟨2⟩ (foldIlkWord I) + ⟨1⟩))
                    (solcSlotWord σ_evm I
                      (solcMappingSlot ⟨2⟩ (foldIlkWord I) + ⟨1⟩)) = ⟨0⟩ := by
              simpa [rateNewE, rateOldE, rateSlotE, vatSlotWord] using hRateNeg
            have hRatePosFailSolc :
                ¬ (UInt256.sgt (foldRateWord I) ⟨0⟩ = ⟨0⟩ ∨
                  UInt256.lt
                    (foldRateWord I +
                      solcSlotWord σ_evm I
                        (solcMappingSlot ⟨2⟩ (foldIlkWord I) + ⟨1⟩))
                    (solcSlotWord σ_evm I
                      (solcMappingSlot ⟨2⟩ (foldIlkWord I) + ⟨1⟩)) = ⟨0⟩) := by
              intro hp
              exact hRatePos (by simpa [rateNewE, rateOldE, rateSlotE, vatSlotWord] using hp)
            have hRateNegSource :
                0 ≤ foldRateInt I ∨ rateNewS.toNat ≤ rateOldS.toNat := by
              cases hRateNeg with
              | inl hslt =>
                  exact Or.inl (by
                    simpa [foldRateInt] using
                      slt_zero_eq_zero_to_nonneg (foldRateWord I) hslt)
              | inr hgt =>
                  exact Or.inr (by
                    have hle := ugt_eq_zero_to_le hgt
                    simpa [rateNewE, rateNewS, rateOldE, rateOldS, hrateWord] using hle)
            have hRateGuardNeg :
                evalExpr? config { contract := contract, locals := foldStoreRateNew I rateNewS }
                  evm0
                  (eitherExpr (.binary .ge (.var "rate") (.intLit 0))
                    (.binary .le (.var "rateNew")
                      (.storage (ilksF (.var "i") "rate")))) =
                  .ok (.bool true) :=
              evalSignedAddGuardNeg_true hrateVar hrateNewVar hrateLoadEval hRateNegSource
            have hRatePosFalseCond :
                0 < foldRateInt I ∧ rateNewS.toNat < rateOldS.toNat := by
              constructor
              · have hsgtNe : UInt256.sgt (foldRateWord I) ⟨0⟩ ≠ ⟨0⟩ := by
                  intro hsgt
                  exact hRatePos (Or.inl hsgt)
                simpa [foldRateInt] using sgt_zero_ne_zero_to_pos (foldRateWord I) hsgtNe
              · have hltNe : UInt256.lt rateNewE rateOldE ≠ ⟨0⟩ := by
                  intro hlt
                  exact hRatePos (Or.inr hlt)
                have hltNat := ult_ne_zero_to_lt hltNe
                simpa [rateNewE, rateNewS, rateOldE, rateOldS, hrateWord] using hltNat
            have hRateGuardPosFalse :
                evalExpr? config { contract := contract, locals := foldStoreRateNew I rateNewS }
                  evm0
                  (eitherExpr (.binary .le (.var "rate") (.intLit 0))
                    (.binary .ge (.var "rateNew")
                      (.storage (ilksF (.var "i") "rate")))) =
                  .ok (.bool false) :=
              evalSignedAddGuardPos_false hrateVar hrateNewVar hrateLoadEval
                hRatePosFalseCond
            have hrateRevert :
                ExecBlock config { contract := contract, locals := foldStore I } evm0
                  (checkedAddSignedInto "rateNew" (.storage (ilksF (.var "i") "rate"))
                    (.var "rate")) .reverted := by
              change ExecBlock config { contract := contract, locals := foldStore I } evm0
                [ .letDecl "rateNew" (some uint256)
                    (wordWrap256 (.binary .add
                      (.storage (ilksF (.var "i") "rate")) (.var "rate"))),
                  .require (eitherExpr (.binary .ge (.var "rate") (.intLit 0))
                    (.binary .le (.var "rateNew") (.storage (ilksF (.var "i") "rate")))),
                  .require (eitherExpr (.binary .le (.var "rate") (.intLit 0))
                    (.binary .ge (.var "rateNew") (.storage (ilksF (.var "i") "rate")))) ]
                .reverted
              refine ExecBlock.consNormal (ExecStmt.letDecl hrateLet) ?_
              refine ExecBlock.consNormal (ExecStmt.requireTrue hRateGuardNeg) ?_
              exact ExecBlock.consRevert (ExecStmt.requireFalse hRateGuardPosFalse)
            have hbody := vatFoldSourceRevertAfterRateBlock evm0 I hwv
              hguardAuth hguardLive hrateRevert
            have hrev := RD.vatFoldRateStoreRevert
              (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
              (A := A) (I := I) (g := Sat256.ofUInt256 g) (sel := vatSelWord I)
              hafterLive hmemLive (Or.inr ⟨hRateNegSolc, hRatePosFailSolc⟩)
            exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody
        · have hRateNegFailSolc :
              ¬ (UInt256.slt (foldRateWord I) ⟨0⟩ = ⟨0⟩ ∨
                UInt256.gt
                  (foldRateWord I +
                    solcSlotWord σ_evm I
                      (solcMappingSlot ⟨2⟩ (foldIlkWord I) + ⟨1⟩))
                  (solcSlotWord σ_evm I
                    (solcMappingSlot ⟨2⟩ (foldIlkWord I) + ⟨1⟩)) = ⟨0⟩) := by
            intro hn
            exact hRateNeg (by simpa [rateNewE, rateOldE, rateSlotE, vatSlotWord] using hn)
          have hRateNegFalseCond :
              foldRateInt I < 0 ∧ rateOldS.toNat < rateNewS.toNat := by
            constructor
            · have hsltNe : UInt256.slt (foldRateWord I) ⟨0⟩ ≠ ⟨0⟩ := by
                intro hslt
                exact hRateNeg (Or.inl hslt)
              simpa [foldRateInt] using slt_zero_ne_zero_to_neg (foldRateWord I) hsltNe
            · have hgtNe : UInt256.gt rateNewE rateOldE ≠ ⟨0⟩ := by
                intro hgt
                exact hRateNeg (Or.inr hgt)
              have hgtNat := ugt_ne_zero_to_gt hgtNe
              simpa [rateNewE, rateNewS, rateOldE, rateOldS, hrateWord] using hgtNat
          have hRateGuardNegFalse :
              evalExpr? config { contract := contract, locals := foldStoreRateNew I rateNewS }
                evm0
                (eitherExpr (.binary .ge (.var "rate") (.intLit 0))
                  (.binary .le (.var "rateNew")
                    (.storage (ilksF (.var "i") "rate")))) =
                .ok (.bool false) :=
            evalSignedAddGuardNeg_false hrateVar hrateNewVar hrateLoadEval
              hRateNegFalseCond
          have hrateRevert :
              ExecBlock config { contract := contract, locals := foldStore I } evm0
                (checkedAddSignedInto "rateNew" (.storage (ilksF (.var "i") "rate"))
                  (.var "rate")) .reverted := by
            change ExecBlock config { contract := contract, locals := foldStore I } evm0
              [ .letDecl "rateNew" (some uint256)
                  (wordWrap256 (.binary .add
                    (.storage (ilksF (.var "i") "rate")) (.var "rate"))),
                .require (eitherExpr (.binary .ge (.var "rate") (.intLit 0))
                  (.binary .le (.var "rateNew") (.storage (ilksF (.var "i") "rate")))),
                .require (eitherExpr (.binary .le (.var "rate") (.intLit 0))
                  (.binary .ge (.var "rateNew") (.storage (ilksF (.var "i") "rate")))) ]
              .reverted
            refine ExecBlock.consNormal (ExecStmt.letDecl hrateLet) ?_
            exact ExecBlock.consRevert (ExecStmt.requireFalse hRateGuardNegFalse)
          have hbody := vatFoldSourceRevertAfterRateBlock evm0 I hwv
            hguardAuth hguardLive hrateRevert
          have hrev := RD.vatFoldRateStoreRevert
            (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
            (A := A) (I := I) (g := Sat256.ofUInt256 g) (sel := vatSelWord I)
            hafterLive hmemLive (Or.inl hRateNegFailSolc)
          exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody
      · have hliveSolm : vatSlotWord liveSlot σ_solm I ≠ ⟨1⟩ := by
          intro hsolm
          exact hliveEvm (by rw [hliveWord, hsolm])
        let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
        have hbody :
            ExecTransitionBody config contract evm0 (foldStore I) foldTransition.body .reverted := by
          have hguardAuth := vatAuthGuardEval_true (cA := cA) (gh := gh) (bl := bl)
            (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
            (g := Sat256.ofUInt256 g) (locals := foldStore I)
            (foldStore_wards I) (by simpa [callerSlot] using hauthSolm)
          have hguardLive := vatLiveGuardEval_false (cA := cA) (gh := gh) (bl := bl)
            (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
            (g := Sat256.ofUInt256 g) (locals := foldStore I)
            (foldStore_live I) (by simpa [liveSlot] using hliveSolm)
          have hblock :
              ExecBlock config { contract := contract, locals := foldStore I } evm0
                ([ .require (.binary .eq (.env .callvalue) (.intLit 0)),
                   .require (.binary .eq (.storage (wardsRef sender)) (.intLit 1)),
                   .require (.binary .eq (.storage liveRef) (.intLit 1)) ] ++
                  checkedAddSignedInto "rateNew" (.storage (ilksF (.var "i") "rate"))
                    (.var "rate") ++
                  [ .assign .storage (ilksF (.var "i") "rate") (.var "rateNew") ] ++
                  checkedMulSignedInto "rad" (.storage (ilksF (.var "i") "Art"))
                    (.var "rate") ++
                  checkedAddSignedInto "daiNew" (.storage (daiRef (.var "u"))) (.var "rad") ++
                  [ .assign .storage (daiRef (.var "u")) (.var "daiNew") ] ++
                  checkedAddSignedInto "debtNew" (.storage debtRef) (.var "rad") ++
                  [ .assign .storage debtRef (.var "debtNew") ])
                .reverted := by
            refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
            · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
            refine ExecBlock.consNormal (ExecStmt.requireTrue hguardAuth) ?_
            exact ExecBlock.consRevert (ExecStmt.requireFalse hguardLive)
          simpa [ExecTransitionBody, foldTransition, nonpayable, auth, requireLive, evm0,
            List.append_assoc] using ExecFuncBody.execBlockRevert hblock
        have hliveSolc : solcSlotWord σ_evm I ⟨10⟩ ≠ ⟨1⟩ := by
          simpa [liveSlot, vatSlotWord] using hliveEvm
        have hmemAuth :
            (twoWordHashMem (hopeSourceWord I) ⟨0⟩ solcFreePtrMem).size = 96 :=
          twoWordHashMem_size_96 (hopeSourceWord I) ⟨0⟩ solcFreePtrMem_size
        have hread64 :
            (twoWordHashMem (hopeSourceWord I) ⟨0⟩ solcFreePtrMem).readWithPadding 64 32 =
              UInt256.toByteArray ⟨128⟩ :=
          twoWordHashMem_read64 (hopeSourceWord I) ⟨0⟩ solcFreePtrMem_size
            solcFreePtrMem_read64
        have hrev := RD.vatLiveGuardRevert
          (code := vatBytecode) (pc := ⟨5663⟩) (okPc := ⟨5733⟩)
          (key := foldRateWord I) (ret := foldUsrMaskedWord I)
          (R := [foldIlkWord I, ⟨524⟩, vatSelWord I]) hafterAuth
          (by unfold vatLiveGuardWf; repeat' first | apply And.intro | decide +native)
          (by
            unfold solcErrorStringRevertTailWf vatLiveGuardTailPc vatNotLiveRawWord
            repeat' first | apply And.intro | decide +native)
          hliveSolc hmemAuth hread64 (by simp)
        exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody
    · have hauthSolm : vatSlotWord callerSlot σ_solm I ≠ ⟨1⟩ := by
        intro hsolm
        exact hauthEvm (by rw [hcallerWord, hsolm])
      let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
      have hbody :
          ExecTransitionBody config contract evm0 (foldStore I) foldTransition.body .reverted := by
        have hguard := vatAuthGuardEval_false (cA := cA) (gh := gh) (bl := bl)
          (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
          (g := Sat256.ofUInt256 g) (locals := foldStore I)
          (foldStore_wards I) (by simpa [callerSlot] using hauthSolm)
        have hblock := nonpayableSecondRequireReverts
          (cfg := config) (solm := { contract := contract, locals := foldStore I })
          (evm := evm0)
          (guard := .binary .eq (.storage (wardsRef sender)) (.intLit 1))
          (rest :=
            requireLive ++
            checkedAddSignedInto "rateNew" (.storage (ilksF (.var "i") "rate"))
              (.var "rate") ++
            [ .assign .storage (ilksF (.var "i") "rate") (.var "rateNew") ] ++
            checkedMulSignedInto "rad" (.storage (ilksF (.var "i") "Art")) (.var "rate") ++
            checkedAddSignedInto "daiNew" (.storage (daiRef (.var "u"))) (.var "rad") ++
            [ .assign .storage (daiRef (.var "u")) (.var "daiNew") ] ++
            checkedAddSignedInto "debtNew" (.storage debtRef) (.var "rad") ++
            [ .assign .storage debtRef (.var "debtNew") ])
          (by simp [evm0, initState]; exact hwv)
          hguard
        simpa [ExecTransitionBody, foldTransition, nonpayable, auth, requireLive, evm0,
          List.append_assoc] using ExecFuncBody.execBlockRevert hblock
      have hauthSolc :
          solcSlotWord σ_evm I (solcMappingSlot ⟨0⟩ (hopeSourceWord I)) ≠ ⟨1⟩ := by
        simpa [callerSlot, vatCallerWardsSlot, vatSlotWord] using hauthEvm
      have hrev := RD.vatAuthCheckRevert
        (pc := ⟨5581⟩) (okPc := ⟨5663⟩) (key := foldRateWord I)
        (ret := foldUsrMaskedWord I) (R := [foldIlkWord I, ⟨524⟩, vatSelWord I])
        (by simpa using hdecoded)
        (by unfold vatAuthCheckWf; repeat' first | apply And.intro | decide +native)
        (by unfold vatAuthRevertTailWf vatAuthTailPc; repeat' first | apply And.intro | decide +native)
        hauthSolc (by simp)
      exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody
  · exact vatFoldBodyCoreDecodeFailed_short hcode hsize hsz4 (by omega) hsel hreach

end Benchmarks.Dss.Vat
