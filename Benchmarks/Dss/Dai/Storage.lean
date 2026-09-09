import Benchmarks.Dss.Dai.Common

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace Benchmarks.Dss.Dai

/-! ## Single-mapping scratch memory -/

noncomputable abbrev daiMappingBaseSlotMem (baseSlot : UInt256) : ByteArray :=
  solcMappingBaseSlotMem baseSlot

noncomputable abbrev daiMappingHashMem (baseSlot key : UInt256) : ByteArray :=
  solcMappingHashMem baseSlot key

theorem daiMappingHashMem_mload64 (baseSlot key : UInt256) :
    (if (⟨64⟩ : UInt256).toNat ≥ (daiMappingHashMem baseSlot key).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 3 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((daiMappingHashMem baseSlot key).readWithPadding (⟨64⟩ : UInt256).toNat 32)))
      = ⟨128⟩ := by
  exact solcMappingHashMem_mload64 baseSlot key

/-! ## Return memory after a mapping getter -/

noncomputable abbrev daiMappingReturnMem (baseSlot key val : UInt256) : ByteArray :=
  solcScratchReturnMem (daiMappingHashMem baseSlot key) val

theorem daiMappingReturnMem_mload64 (baseSlot key val : UInt256) :
    (if (⟨64⟩ : UInt256).toNat ≥ (daiMappingReturnMem baseSlot key val).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 5 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((daiMappingReturnMem baseSlot key val).readWithPadding
          (⟨64⟩ : UInt256).toNat 32)))
      = ⟨128⟩ := by
  exact solcScratchReturnMem_mload64 val (solcMappingHashMem_size baseSlot key)
    (solcMappingHashMem_read64 baseSlot key)

theorem daiMappingReturnMem_read128 (baseSlot key val : UInt256) :
    (daiMappingReturnMem baseSlot key val).readWithPadding 128 32 =
      UInt256.toByteArray val := by
  exact solcScratchReturnMem_read128 val (solcMappingHashMem_size baseSlot key)

/-! ## Nested-mapping scratch memory -/

noncomputable abbrev daiNestedMappingHashMem
    (baseSlot owner spender : UInt256) : ByteArray :=
  solcNestedMappingHashMem baseSlot owner spender

theorem daiNestedMappingHashMem_mload64 (baseSlot owner spender : UInt256) :
    (if (⟨64⟩ : UInt256).toNat ≥ (daiNestedMappingHashMem baseSlot owner spender).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 3 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((daiNestedMappingHashMem baseSlot owner spender).readWithPadding
          (⟨64⟩ : UInt256).toNat 32)))
      = ⟨128⟩ := by
  exact solcNestedMappingHashMem_mload64 baseSlot owner spender

/-! ## Return memory after a nested-mapping getter -/

noncomputable abbrev daiNestedMappingReturnMem
    (baseSlot owner spender val : UInt256) : ByteArray :=
  solcScratchReturnMem (daiNestedMappingHashMem baseSlot owner spender) val

theorem daiNestedMappingReturnMem_mload64
    (baseSlot owner spender val : UInt256) :
    (if (⟨64⟩ : UInt256).toNat ≥
          (daiNestedMappingReturnMem baseSlot owner spender val).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 5 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((daiNestedMappingReturnMem baseSlot owner spender val).readWithPadding
          (⟨64⟩ : UInt256).toNat 32)))
      = ⟨128⟩ := by
  exact solcScratchReturnMem_mload64 val
    (solcNestedMappingHashMem_size baseSlot owner spender)
    (solcNestedMappingHashMem_read64 baseSlot owner spender)

theorem daiNestedMappingReturnMem_read128
    (baseSlot owner spender val : UInt256) :
    (daiNestedMappingReturnMem baseSlot owner spender val).readWithPadding 128 32 =
      UInt256.toByteArray val := by
  exact solcScratchReturnMem_read128 val
    (solcNestedMappingHashMem_size baseSlot owner spender)

end Benchmarks.Dss.Dai

namespace Reasoning.Reach

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Benchmarks.Dss.Dai

/-! ## Shared single-mapping getter routine -/

@[reducible] def daiSingleMappingGetterWf (pc baseSlot : UInt256) : Prop :=
  solcSingleMappingGetterWf Benchmarks.Dss.Dai.daiBytecode pc baseSlot

macro "dai_single_mapping_getter_wf" : term =>
  `(by
    unfold Reasoning.Reach.daiSingleMappingGetterWf
      Reasoning.Reach.solcSingleMappingGetterWf
    repeat' first | apply And.intro | decide +native)

theorem RD.daiSingleMappingGetter {g : Sat256} {s0 : State} {ee : ExecutionEnv} {k C : ℕ}
    {pc baseSlot key ret : UInt256} {R : List UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD Benchmarks.Dss.Dai.daiBytecode ee g s0 pc (key :: ret :: R)
        solcFreePtrMem (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hwf : daiSingleMappingGetterWf pc baseSlot)
    (hret : (D_J Benchmarks.Dss.Dai.daiBytecode 0).contains ret = true)
    (hov : R.length + 4 ≤ 1024) :
    ∃ k' C', RD Benchmarks.Dss.Dai.daiBytecode ee g s0 ret
      ((σ.find? ee.codeOwner |>.option ⟨0⟩
          (fun acc => acc.storage.findD (Benchmarks.Dss.Dai.mapSlot key baseSlot) ⟨0⟩))
        :: ret :: R)
      (Benchmarks.Dss.Dai.daiMappingHashMem baseSlot key)
      (UInt256.ofNat 3) rdata (cA, σ) k' C' := by
  simpa [solcSlotWord, Benchmarks.Dss.Dai.daiMappingHashMem,
    Benchmarks.Dss.Dai.mapSlot, solcMappingSlot] using
      RD.solcSingleMappingGetter h hwf hret hov

/-! ## Shared zero-base single-mapping getter routine -/

@[reducible] def daiZeroSlotSingleMappingGetterWf (pc : UInt256) : Prop :=
  let p1 := pc + ⟨1⟩
  let p3 := p1 + UInt256.ofNat 2
  let p5 := p3 + UInt256.ofNat 2
  let p6 := p5 + ⟨1⟩
  let p7 := p6 + ⟨1⟩
  let p8 := p7 + ⟨1⟩
  let p9 := p8 + ⟨1⟩
  let p10 := p9 + ⟨1⟩
  let p11 := p10 + ⟨1⟩
  let p13 := p11 + UInt256.ofNat 2
  let p14 := p13 + ⟨1⟩
  let p15 := p14 + ⟨1⟩
  let p16 := p15 + ⟨1⟩
  let p17 := p16 + ⟨1⟩
  decode Benchmarks.Dss.Dai.daiBytecode pc = some (.JUMPDEST, .none)
  ∧ decode Benchmarks.Dss.Dai.daiBytecode p1 =
      some (.Push .PUSH1, some (⟨0⟩, 1))
  ∧ decode Benchmarks.Dss.Dai.daiBytecode p3 =
      some (.Push .PUSH1, some (⟨32⟩, 1))
  ∧ decode Benchmarks.Dss.Dai.daiBytecode p5 = some (.DUP2, .none)
  ∧ decode Benchmarks.Dss.Dai.daiBytecode p6 = some (.SWAP1, .none)
  ∧ decode Benchmarks.Dss.Dai.daiBytecode p7 = some (.MSTORE, .none)
  ∧ decode Benchmarks.Dss.Dai.daiBytecode p8 = some (.SWAP1, .none)
  ∧ decode Benchmarks.Dss.Dai.daiBytecode p9 = some (.DUP2, .none)
  ∧ decode Benchmarks.Dss.Dai.daiBytecode p10 = some (.MSTORE, .none)
  ∧ decode Benchmarks.Dss.Dai.daiBytecode p11 =
      some (.Push .PUSH1, some (⟨64⟩, 1))
  ∧ decode Benchmarks.Dss.Dai.daiBytecode p13 = some (.SWAP1, .none)
  ∧ decode Benchmarks.Dss.Dai.daiBytecode p14 = some (.KECCAK256, .none)
  ∧ decode Benchmarks.Dss.Dai.daiBytecode p15 = some (.SLOAD, .none)
  ∧ decode Benchmarks.Dss.Dai.daiBytecode p16 = some (.DUP2, .none)
  ∧ decode Benchmarks.Dss.Dai.daiBytecode p17 = some (.JUMP, .none)

macro "dai_zero_slot_single_mapping_getter_wf" : term =>
  `(by
    unfold Reasoning.Reach.daiZeroSlotSingleMappingGetterWf
    repeat' first | apply And.intro | decide +native)

theorem RD.daiZeroSlotSingleMappingGetter {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {pc key ret : UInt256} {R : List UInt256}
    {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD Benchmarks.Dss.Dai.daiBytecode ee g s0 pc (key :: ret :: R)
        solcFreePtrMem (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hwf : daiZeroSlotSingleMappingGetterWf pc)
    (hret : (D_J Benchmarks.Dss.Dai.daiBytecode 0).contains ret = true)
    (hov : R.length + 5 ≤ 1024) :
    ∃ k' C', RD Benchmarks.Dss.Dai.daiBytecode ee g s0 ret
      ((σ.find? ee.codeOwner |>.option ⟨0⟩
          (fun acc => acc.storage.findD (Benchmarks.Dss.Dai.mapSlot key ⟨0⟩) ⟨0⟩))
        :: ret :: R)
      (Benchmarks.Dss.Dai.daiMappingHashMem ⟨0⟩ key)
      (UInt256.ofNat 3) rdata (cA, σ) k' C' := by
  rcases hwf with
    ⟨hd0, hd1, hd3, hd5, hd6, hd7, hd8, hd9, hd10, hd11, hd13, hd14, hd15,
      hd16, hd17⟩
  have rd1 := h.jumpdest hd0 (by simp only [List.length_cons]; omega)
  have rd3 := rd1.push1 ⟨0⟩ hd1 (by evm_ov)
  have rd5 := rd3.push1 ⟨32⟩ hd3 (by evm_ov)
  have rd6 := rd5.dup2 hd5 (by simp only [List.length_cons]; omega)
  have rd7 := rd6.swap1 hd6 (by simp only [List.length_cons]; omega)
  have rd8 := rd7.mstore 0 (solcMappingBaseSlotMem ⟨0⟩)
    (UInt256.ofNat 3) hd7 mem_cost (by rfl) (by decide +native) (by evm_ov)
  have rd9 := rd8.swap1 hd8 (by evm_ov)
  have rd10 := rd9.dup2 hd9 (by evm_ov)
  have rd11 := rd10.mstore 0 (solcMappingHashMem ⟨0⟩ key)
    (UInt256.ofNat 3) hd10 mem_cost (by rfl) (by decide +native) (by evm_ov)
  have rd13 := rd11.push1 ⟨64⟩ hd11 (by evm_ov)
  have rd14 := rd13.swap1 hd13 (by evm_ov)
  have hslot := solcMappingKeccakSlot ⟨0⟩ key
  have rd15 := rd14.keccak256 0 (solcMappingSlot ⟨0⟩ key)
    (UInt256.ofNat 3) hd14 mem_cost
    (by simpa [show (⟨0⟩ : UInt256).toNat = 0 from by decide,
      show (⟨64⟩ : UInt256).toNat = 64 from by decide] using hslot)
    (by decide +native) (by evm_ov)
  obtain ⟨k16, C16, rd16⟩ := rd15.sload hd15 (by evm_ov)
  have rd17 := rd16.dup2 hd16 (by evm_ov)
  have rd18 := rd17.jump hd17 hret (by evm_ov)
  exact ⟨k16 + 1 + 1, C16 + 3 + 8, by
    simpa [solcSlotWord, Benchmarks.Dss.Dai.daiMappingHashMem,
      Benchmarks.Dss.Dai.mapSlot, solcMappingSlot] using rd18⟩

/-! ## Shared nested-mapping getter routine -/

@[reducible] def daiNestedMappingGetterWf (pc baseSlot : UInt256) : Prop :=
  solcNestedMappingGetterWf Benchmarks.Dss.Dai.daiBytecode pc baseSlot

macro "dai_nested_mapping_getter_wf" : term =>
  `(by
    unfold Reasoning.Reach.daiNestedMappingGetterWf
      Reasoning.Reach.solcNestedMappingGetterWf
    repeat' first | apply And.intro | decide +native)

theorem RD.daiNestedMappingInnerHash {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ}
    {pc baseSlot owner spender ret : UInt256} {R : List UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD Benchmarks.Dss.Dai.daiBytecode ee g s0 pc (spender :: owner :: ret :: R)
        solcFreePtrMem (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hwf : daiNestedMappingGetterWf pc baseSlot)
    (hov : R.length + 7 ≤ 1024) :
    ∃ k' C', RD Benchmarks.Dss.Dai.daiBytecode ee g s0
      (solcNestedMappingGetterAfterInnerHashPc pc)
      (Benchmarks.Dss.Dai.mapSlot owner baseSlot :: ⟨64⟩ :: ⟨32⟩ :: spender ::
        ⟨0⟩ :: ret :: R)
      (Benchmarks.Dss.Dai.daiMappingHashMem baseSlot owner)
      (UInt256.ofNat 3) rdata (cA, σ) k' C' := by
  simpa [Benchmarks.Dss.Dai.daiMappingHashMem, Benchmarks.Dss.Dai.mapSlot,
    solcMappingSlot] using
      RD.solcNestedMappingInnerHash h hwf hov

theorem RD.daiNestedMappingOuterHash {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ}
    {pc baseSlot owner spender ret : UInt256} {R : List UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD Benchmarks.Dss.Dai.daiBytecode ee g s0
      (solcNestedMappingGetterAfterInnerHashPc pc)
      (Benchmarks.Dss.Dai.mapSlot owner baseSlot :: ⟨64⟩ :: ⟨32⟩ :: spender ::
        ⟨0⟩ :: ret :: R)
      (Benchmarks.Dss.Dai.daiMappingHashMem baseSlot owner)
      (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hwf : daiNestedMappingGetterWf pc baseSlot)
    (hov : R.length + 7 ≤ 1024) :
    ∃ k' C', RD Benchmarks.Dss.Dai.daiBytecode ee g s0
      (solcNestedMappingGetterSloadPc pc)
      (Benchmarks.Dss.Dai.mapSlot spender (Benchmarks.Dss.Dai.mapSlot owner baseSlot) ::
        ret :: R)
      (Benchmarks.Dss.Dai.daiNestedMappingHashMem baseSlot owner spender)
      (UInt256.ofNat 3) rdata (cA, σ) k' C' := by
  simpa [Benchmarks.Dss.Dai.daiMappingHashMem,
    Benchmarks.Dss.Dai.daiNestedMappingHashMem, Benchmarks.Dss.Dai.mapSlot,
    solcMappingSlot] using
      RD.solcNestedMappingOuterHash h hwf hov

theorem RD.daiNestedMappingLoadAndJump {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {pc baseSlot slot ret : UInt256} {R : List UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD Benchmarks.Dss.Dai.daiBytecode ee g s0
      (solcNestedMappingGetterSloadPc pc) (slot :: ret :: R)
      mem aw rdata (cA, σ) k C)
    (hwf : daiNestedMappingGetterWf pc baseSlot)
    (hret : (D_J Benchmarks.Dss.Dai.daiBytecode 0).contains ret = true)
    (hov : R.length + 3 ≤ 1024) :
    ∃ k' C', RD Benchmarks.Dss.Dai.daiBytecode ee g s0 ret
      ((σ.find? ee.codeOwner |>.option ⟨0⟩
          (fun acc => acc.storage.findD slot ⟨0⟩)) :: ret :: R)
      mem aw rdata (cA, σ) k' C' := by
  simpa [solcSlotWord] using
    RD.solcNestedMappingLoadAndJump h hwf hret hov

theorem RD.daiNestedMappingGetter {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ}
    {pc baseSlot owner spender ret : UInt256} {R : List UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD Benchmarks.Dss.Dai.daiBytecode ee g s0 pc (spender :: owner :: ret :: R)
        solcFreePtrMem (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hwf : daiNestedMappingGetterWf pc baseSlot)
    (hret : (D_J Benchmarks.Dss.Dai.daiBytecode 0).contains ret = true)
    (hov : R.length + 7 ≤ 1024) :
    ∃ k' C', RD Benchmarks.Dss.Dai.daiBytecode ee g s0 ret
      ((σ.find? ee.codeOwner |>.option ⟨0⟩
          (fun acc => acc.storage.findD
            (Benchmarks.Dss.Dai.mapSlot spender
              (Benchmarks.Dss.Dai.mapSlot owner baseSlot)) ⟨0⟩)) :: ret :: R)
      (Benchmarks.Dss.Dai.daiNestedMappingHashMem baseSlot owner spender)
      (UInt256.ofNat 3) rdata (cA, σ) k' C' := by
  obtain ⟨_, _, hinner⟩ := RD.daiNestedMappingInnerHash h hwf hov
  obtain ⟨_, _, houter⟩ := RD.daiNestedMappingOuterHash hinner hwf hov
  obtain ⟨_, _, hload⟩ := RD.daiNestedMappingLoadAndJump houter hwf hret (by omega)
  exact ⟨_, _, hload⟩

/-! ## Shared one-address external wrapper -/

@[reducible] def daiOneAddressExternalDecodedPc (pc : UInt256) : UInt256 :=
  let p1 := pc + ⟨1⟩
  let p4 := p1 + UInt256.ofNat 3
  let p6 := p4 + UInt256.ofNat 2
  let p7 := p6 + ⟨1⟩
  let p8 := p7 + ⟨1⟩
  let p9 := p8 + ⟨1⟩
  let p11 := p9 + UInt256.ofNat 2
  let p12 := p11 + ⟨1⟩
  let p13 := p12 + ⟨1⟩
  let p14 := p13 + ⟨1⟩
  let p17 := p14 + UInt256.ofNat 3
  let p18 := p17 + ⟨1⟩
  let p20 := p18 + UInt256.ofNat 2
  let p21 := p20 + ⟨1⟩
  p21 + ⟨1⟩

@[reducible] def daiOneAddressExternalEntryWf (pc ret routine : UInt256) : Prop :=
  let p1 := pc + ⟨1⟩
  let p4 := p1 + UInt256.ofNat 3
  let p6 := p4 + UInt256.ofNat 2
  let p7 := p6 + ⟨1⟩
  let p8 := p7 + ⟨1⟩
  let p9 := p8 + ⟨1⟩
  let p11 := p9 + UInt256.ofNat 2
  let p12 := p11 + ⟨1⟩
  let p13 := p12 + ⟨1⟩
  let p14 := p13 + ⟨1⟩
  let p17 := p14 + UInt256.ofNat 3
  let p18 := p17 + ⟨1⟩
  let p20 := p18 + UInt256.ofNat 2
  let p21 := p20 + ⟨1⟩
  let p22 := daiOneAddressExternalDecodedPc pc
  let p23 := p22 + ⟨1⟩
  let p24 := p23 + ⟨1⟩
  let p25 := p24 + ⟨1⟩
  let p27 := p25 + UInt256.ofNat 2
  let p29 := p27 + UInt256.ofNat 2
  let p31 := p29 + UInt256.ofNat 2
  let p32 := p31 + ⟨1⟩
  let p33 := p32 + ⟨1⟩
  let p34 := p33 + ⟨1⟩
  let p37 := p34 + UInt256.ofNat 3
  decode Benchmarks.Dss.Dai.daiBytecode pc = some (.JUMPDEST, .none)
  ∧ decode Benchmarks.Dss.Dai.daiBytecode p1 =
      some (.Push .PUSH2, some (ret, 2))
  ∧ decode Benchmarks.Dss.Dai.daiBytecode p4 =
      some (.Push .PUSH1, some (⟨4⟩, 1))
  ∧ decode Benchmarks.Dss.Dai.daiBytecode p6 = some (.DUP1, .none)
  ∧ decode Benchmarks.Dss.Dai.daiBytecode p7 = some (.CALLDATASIZE, .none)
  ∧ decode Benchmarks.Dss.Dai.daiBytecode p8 = some (.SUB, .none)
  ∧ decode Benchmarks.Dss.Dai.daiBytecode p9 =
      some (.Push .PUSH1, some (⟨32⟩, 1))
  ∧ decode Benchmarks.Dss.Dai.daiBytecode p11 = some (.DUP2, .none)
  ∧ decode Benchmarks.Dss.Dai.daiBytecode p12 = some (.LT, .none)
  ∧ decode Benchmarks.Dss.Dai.daiBytecode p13 = some (.ISZERO, .none)
  ∧ decode Benchmarks.Dss.Dai.daiBytecode p14 =
      some (.Push .PUSH2, some (p22, 2))
  ∧ decode Benchmarks.Dss.Dai.daiBytecode p17 = some (.JUMPI, .none)
  ∧ decode Benchmarks.Dss.Dai.daiBytecode p18 =
      some (.Push .PUSH1, some (⟨0⟩, 1))
  ∧ decode Benchmarks.Dss.Dai.daiBytecode p20 = some (.DUP1, .none)
  ∧ decode Benchmarks.Dss.Dai.daiBytecode p21 = some (.REVERT, .none)
  ∧ decode Benchmarks.Dss.Dai.daiBytecode p22 = some (.JUMPDEST, .none)
  ∧ decode Benchmarks.Dss.Dai.daiBytecode p23 = some (.POP, .none)
  ∧ decode Benchmarks.Dss.Dai.daiBytecode p24 = some (.CALLDATALOAD, .none)
  ∧ decode Benchmarks.Dss.Dai.daiBytecode p25 =
      some (.Push .PUSH1, some (⟨1⟩, 1))
  ∧ decode Benchmarks.Dss.Dai.daiBytecode p27 =
      some (.Push .PUSH1, some (⟨1⟩, 1))
  ∧ decode Benchmarks.Dss.Dai.daiBytecode p29 =
      some (.Push .PUSH1, some (⟨160⟩, 1))
  ∧ decode Benchmarks.Dss.Dai.daiBytecode p31 = some (.SHL, .none)
  ∧ decode Benchmarks.Dss.Dai.daiBytecode p32 = some (.SUB, .none)
  ∧ decode Benchmarks.Dss.Dai.daiBytecode p33 = some (.AND, .none)
  ∧ decode Benchmarks.Dss.Dai.daiBytecode p34 =
      some (.Push .PUSH2, some (routine, 2))
  ∧ decode Benchmarks.Dss.Dai.daiBytecode p37 = some (.JUMP, .none)

macro "dai_one_address_external_entry_wf" : term =>
  `(by
    unfold Reasoning.Reach.daiOneAddressExternalEntryWf
      Reasoning.Reach.daiOneAddressExternalDecodedPc
    repeat' first | apply And.intro | decide +native)

set_option maxHeartbeats 1000000 in
theorem RD.daiOneAddressExternalLenOk {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    {entry ret routine : UInt256}
    (hreach : ∃ k C, RD Benchmarks.Dss.Dai.daiBytecode I g
      (Reasoning.Theory.initState cA gh bl σ σ₀ g A I) entry [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hwf : daiOneAddressExternalEntryWf entry ret routine)
    (hdecoded : (D_J Benchmarks.Dss.Dai.daiBytecode 0).contains
      (daiOneAddressExternalDecodedPc entry) = true)
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size) :
    ∃ k C, RD Benchmarks.Dss.Dai.daiBytecode I g
      (Reasoning.Theory.initState cA gh bl σ σ₀ g A I)
      (daiOneAddressExternalDecodedPc entry)
      (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩ :: ⟨4⟩ :: ret :: [sel])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  rcases hwf with
    ⟨hd0, hd1, hd4, hd6, hd7, hd8, hd9, hd11, hd12, hd13, hd14, hd17, _hd18,
      _hd20, _hd21, _hd22, _hd23, _hd24, _hd25, _hd27, _hd29, _hd31, _hd32,
      _hd33, _hd34, _hd37⟩
  exact RD.solcOneAddressExternalLenOk hreach hd0 hd1 hd4 hd6 hd7 hd8 hd9 hd11
    hd12 hd13 hd14 hd17 hdecoded hsz36 hsize

set_option maxHeartbeats 1000000 in
theorem RD.daiOneAddressExternalMaskAndJumpMasked {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {entry ret routine de : UInt256} {R : List UInt256}
    {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD Benchmarks.Dss.Dai.daiBytecode ee g s0
      (daiOneAddressExternalDecodedPc entry) (de :: ⟨4⟩ :: ret :: R)
      solcFreePtrMem (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hwf : daiOneAddressExternalEntryWf entry ret routine)
    (hroutine : (D_J Benchmarks.Dss.Dai.daiBytecode 0).contains routine = true)
    (hov : R.length + 5 ≤ 1024) :
    ∃ k' C', RD Benchmarks.Dss.Dai.daiBytecode ee g s0 routine
      (UInt256.land solcAddrMask (calldataWord ee.calldata 4) :: ret :: R)
      solcFreePtrMem (UInt256.ofNat 3) rdata (cA, σ) k' C' := by
  rcases hwf with
    ⟨_hd0, _hd1, _hd4, _hd6, _hd7, _hd8, _hd9, _hd11, _hd12, _hd13, _hd14,
      _hd17, _hd18, _hd20, _hd21, hd22, hd23, hd24, hd25, hd27, hd29, hd31,
      hd32, hd33, hd34, hd37⟩
  exact RD.solcOneAddressExternalMaskAndJumpMasked h hd22 hd23 hd24 hd25 hd27 hd29
    hd31 hd32 hd33 hd34 hd37 hroutine hov

set_option maxHeartbeats 1000000 in
theorem RD.daiOneAddressExternalShort {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel entry ret routine : UInt256}
    (hreach : ∃ k C, RD Benchmarks.Dss.Dai.daiBytecode I g
      (Reasoning.Theory.initState cA gh bl σ σ₀ g A I) entry [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hwf : daiOneAddressExternalEntryWf entry ret routine)
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 36) :
    RDrev Benchmarks.Dss.Dai.daiBytecode g
      (Reasoning.Theory.initState cA gh bl σ σ₀ g A I) := by
  have hlt :
      UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨1⟩ := by
    apply ult_one
    rw [show (⟨32⟩ : UInt256).toNat = 32 from by decide,
      usub_ofNat_word_toNat (c := (⟨4⟩ : UInt256)) (by simpa using hsz4) hsize,
      show (⟨4⟩ : UInt256).toNat = 4 from by decide]
    omega
  rcases hwf with
    ⟨hd0, hd1, hd4, hd6, hd7, hd8, hd9, hd11, hd12, hd13, hd14, hd17, hd18,
      hd20, hd21, _hd22, _hd23, _hd24, _hd25, _hd27, _hd29, _hd31, _hd32,
      _hd33, _hd34, _hd37⟩
  exact RD.solcExternalStaticArgsShortReverts hreach hd0 hd1 hd4 hd6 hd7 hd8 hd9
    hd11 hd12 hd13 hd14 hd17 hd18 hd20 hd21 hlt

/-! ## Shared two-address external wrapper -/

@[reducible] def daiTwoAddressExternalDecodedPc (pc : UInt256) : UInt256 :=
  let p1 := pc + ⟨1⟩
  let p4 := p1 + UInt256.ofNat 3
  let p6 := p4 + UInt256.ofNat 2
  let p7 := p6 + ⟨1⟩
  let p8 := p7 + ⟨1⟩
  let p9 := p8 + ⟨1⟩
  let p11 := p9 + UInt256.ofNat 2
  let p12 := p11 + ⟨1⟩
  let p13 := p12 + ⟨1⟩
  let p14 := p13 + ⟨1⟩
  let p17 := p14 + UInt256.ofNat 3
  let p18 := p17 + ⟨1⟩
  let p20 := p18 + UInt256.ofNat 2
  let p21 := p20 + ⟨1⟩
  p21 + ⟨1⟩

@[reducible] def daiTwoAddressExternalEntryWf (pc ret routine : UInt256) : Prop :=
  let p1 := pc + ⟨1⟩
  let p4 := p1 + UInt256.ofNat 3
  let p6 := p4 + UInt256.ofNat 2
  let p7 := p6 + ⟨1⟩
  let p8 := p7 + ⟨1⟩
  let p9 := p8 + ⟨1⟩
  let p11 := p9 + UInt256.ofNat 2
  let p12 := p11 + ⟨1⟩
  let p13 := p12 + ⟨1⟩
  let p14 := p13 + ⟨1⟩
  let p17 := p14 + UInt256.ofNat 3
  let p18 := p17 + ⟨1⟩
  let p20 := p18 + UInt256.ofNat 2
  let p21 := p20 + ⟨1⟩
  let p22 := daiTwoAddressExternalDecodedPc pc
  let p23 := p22 + ⟨1⟩
  let p24 := p23 + ⟨1⟩
  let p26 := p24 + UInt256.ofNat 2
  let p28 := p26 + UInt256.ofNat 2
  let p30 := p28 + UInt256.ofNat 2
  let p31 := p30 + ⟨1⟩
  let p32 := p31 + ⟨1⟩
  let p33 := p32 + ⟨1⟩
  let p34 := p33 + ⟨1⟩
  let p35 := p34 + ⟨1⟩
  let p36 := p35 + ⟨1⟩
  let p37 := p36 + ⟨1⟩
  let p39 := p37 + UInt256.ofNat 2
  let p40 := p39 + ⟨1⟩
  let p41 := p40 + ⟨1⟩
  let p42 := p41 + ⟨1⟩
  let p45 := p42 + UInt256.ofNat 3
  decode Benchmarks.Dss.Dai.daiBytecode pc = some (.JUMPDEST, .none)
  ∧ decode Benchmarks.Dss.Dai.daiBytecode p1 =
      some (.Push .PUSH2, some (ret, 2))
  ∧ decode Benchmarks.Dss.Dai.daiBytecode p4 =
      some (.Push .PUSH1, some (⟨4⟩, 1))
  ∧ decode Benchmarks.Dss.Dai.daiBytecode p6 = some (.DUP1, .none)
  ∧ decode Benchmarks.Dss.Dai.daiBytecode p7 = some (.CALLDATASIZE, .none)
  ∧ decode Benchmarks.Dss.Dai.daiBytecode p8 = some (.SUB, .none)
  ∧ decode Benchmarks.Dss.Dai.daiBytecode p9 =
      some (.Push .PUSH1, some (⟨64⟩, 1))
  ∧ decode Benchmarks.Dss.Dai.daiBytecode p11 = some (.DUP2, .none)
  ∧ decode Benchmarks.Dss.Dai.daiBytecode p12 = some (.LT, .none)
  ∧ decode Benchmarks.Dss.Dai.daiBytecode p13 = some (.ISZERO, .none)
  ∧ decode Benchmarks.Dss.Dai.daiBytecode p14 =
      some (.Push .PUSH2, some (p22, 2))
  ∧ decode Benchmarks.Dss.Dai.daiBytecode p17 = some (.JUMPI, .none)
  ∧ decode Benchmarks.Dss.Dai.daiBytecode p18 =
      some (.Push .PUSH1, some (⟨0⟩, 1))
  ∧ decode Benchmarks.Dss.Dai.daiBytecode p20 = some (.DUP1, .none)
  ∧ decode Benchmarks.Dss.Dai.daiBytecode p21 = some (.REVERT, .none)
  ∧ decode Benchmarks.Dss.Dai.daiBytecode p22 = some (.JUMPDEST, .none)
  ∧ decode Benchmarks.Dss.Dai.daiBytecode p23 = some (.POP, .none)
  ∧ decode Benchmarks.Dss.Dai.daiBytecode p24 =
      some (.Push .PUSH1, some (⟨1⟩, 1))
  ∧ decode Benchmarks.Dss.Dai.daiBytecode p26 =
      some (.Push .PUSH1, some (⟨1⟩, 1))
  ∧ decode Benchmarks.Dss.Dai.daiBytecode p28 =
      some (.Push .PUSH1, some (⟨160⟩, 1))
  ∧ decode Benchmarks.Dss.Dai.daiBytecode p30 = some (.SHL, .none)
  ∧ decode Benchmarks.Dss.Dai.daiBytecode p31 = some (.SUB, .none)
  ∧ decode Benchmarks.Dss.Dai.daiBytecode p32 = some (.DUP2, .none)
  ∧ decode Benchmarks.Dss.Dai.daiBytecode p33 = some (.CALLDATALOAD, .none)
  ∧ decode Benchmarks.Dss.Dai.daiBytecode p34 = some (.DUP2, .none)
  ∧ decode Benchmarks.Dss.Dai.daiBytecode p35 = some (.AND, .none)
  ∧ decode Benchmarks.Dss.Dai.daiBytecode p36 = some (.SWAP2, .none)
  ∧ decode Benchmarks.Dss.Dai.daiBytecode p37 =
      some (.Push .PUSH1, some (⟨32⟩, 1))
  ∧ decode Benchmarks.Dss.Dai.daiBytecode p39 = some (.ADD, .none)
  ∧ decode Benchmarks.Dss.Dai.daiBytecode p40 = some (.CALLDATALOAD, .none)
  ∧ decode Benchmarks.Dss.Dai.daiBytecode p41 = some (.AND, .none)
  ∧ decode Benchmarks.Dss.Dai.daiBytecode p42 =
      some (.Push .PUSH2, some (routine, 2))
  ∧ decode Benchmarks.Dss.Dai.daiBytecode p45 = some (.JUMP, .none)

macro "dai_two_address_external_entry_wf" : term =>
  `(by
    unfold Reasoning.Reach.daiTwoAddressExternalEntryWf
      Reasoning.Reach.daiTwoAddressExternalDecodedPc
    repeat' first | apply And.intro | decide +native)

set_option maxHeartbeats 1000000 in
theorem RD.daiTwoAddressExternalLenOk {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel entry ret routine : UInt256}
    (hreach : ∃ k C, RD Benchmarks.Dss.Dai.daiBytecode I g
      (Reasoning.Theory.initState cA gh bl σ σ₀ g A I) entry [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hwf : daiTwoAddressExternalEntryWf entry ret routine)
    (hdecoded : (D_J Benchmarks.Dss.Dai.daiBytecode 0).contains
      (daiTwoAddressExternalDecodedPc entry) = true)
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size) :
    ∃ k C, RD Benchmarks.Dss.Dai.daiBytecode I g
      (Reasoning.Theory.initState cA gh bl σ σ₀ g A I)
      (daiTwoAddressExternalDecodedPc entry)
      (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩ :: ⟨4⟩ :: ret :: [sel])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  rcases hwf with
    ⟨hd0, hd1, hd4, hd6, hd7, hd8, hd9, hd11, hd12, hd13, hd14, hd17, _hd18,
      _hd20, _hd21, _hd22, _hd23, _hd24, _hd26, _hd28, _hd30, _hd31, _hd32,
      _hd33, _hd34, _hd35, _hd36, _hd37, _hd39, _hd40, _hd41, _hd42, _hd45⟩
  exact RD.solcTwoAddressExternalLenOk hreach hd0 hd1 hd4 hd6 hd7 hd8 hd9 hd11
    hd12 hd13 hd14 hd17 hdecoded hsz68 hsize

set_option maxHeartbeats 1000000 in
theorem RD.daiTwoAddressExternalMaskAndJumpMasked {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {entry ret routine de : UInt256} {R : List UInt256}
    {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD Benchmarks.Dss.Dai.daiBytecode ee g s0
      (daiTwoAddressExternalDecodedPc entry) (de :: ⟨4⟩ :: ret :: R)
      solcFreePtrMem (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hwf : daiTwoAddressExternalEntryWf entry ret routine)
    (hroutine : (D_J Benchmarks.Dss.Dai.daiBytecode 0).contains routine = true)
    (hov : R.length + 7 ≤ 1024) :
    ∃ k' C', RD Benchmarks.Dss.Dai.daiBytecode ee g s0 routine
      (UInt256.land solcAddrMask (calldataWord ee.calldata 36) ::
        UInt256.land solcAddrMask (calldataWord ee.calldata 4) :: ret :: R)
      solcFreePtrMem (UInt256.ofNat 3) rdata (cA, σ) k' C' := by
  rcases hwf with
    ⟨_hd0, _hd1, _hd4, _hd6, _hd7, _hd8, _hd9, _hd11, _hd12, _hd13, _hd14,
      _hd17, _hd18, _hd20, _hd21, hd22, hd23, hd24, hd26, hd28, hd30, hd31,
      hd32, hd33, hd34, hd35, hd36, hd37, hd39, hd40, hd41, hd42, hd45⟩
  exact RD.solcTwoAddressExternalMaskAndJumpMasked h hd22 hd23 hd24 hd26 hd28
    hd30 hd31 hd32 hd33 hd34 hd35 hd36 hd37 hd39 hd40 hd41 hd42 hd45
    hroutine hov

set_option maxHeartbeats 1000000 in
theorem RD.daiTwoAddressExternalShort {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel entry ret routine : UInt256}
    (hreach : ∃ k C, RD Benchmarks.Dss.Dai.daiBytecode I g
      (Reasoning.Theory.initState cA gh bl σ σ₀ g A I) entry [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hwf : daiTwoAddressExternalEntryWf entry ret routine)
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 68) :
    RDrev Benchmarks.Dss.Dai.daiBytecode g
      (Reasoning.Theory.initState cA gh bl σ σ₀ g A I) := by
  have hlt :
      UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ = ⟨1⟩ := by
    apply ult_one
    rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide,
      usub_ofNat_word_toNat (c := (⟨4⟩ : UInt256)) (by simpa using hsz4) hsize,
      show (⟨4⟩ : UInt256).toNat = 4 from by decide]
    omega
  rcases hwf with
    ⟨hd0, hd1, hd4, hd6, hd7, hd8, hd9, hd11, hd12, hd13, hd14, hd17, hd18,
      hd20, hd21, _hd22, _hd23, _hd24, _hd26, _hd28, _hd30, _hd31, _hd32,
      _hd33, _hd34, _hd35, _hd36, _hd37, _hd39, _hd40, _hd41, _hd42, _hd45⟩
  exact RD.solcExternalStaticArgsShortReverts hreach hd0 hd1 hd4 hd6 hd7 hd8 hd9
    hd11 hd12 hd13 hd14 hd17 hd18 hd20 hd21 hlt

/-! ## Shared address,uint256 external wrapper -/

@[reducible] def daiAddressUint256ExternalDecodedPc (pc : UInt256) : UInt256 :=
  let p1 := pc + ⟨1⟩
  let p4 := p1 + UInt256.ofNat 3
  let p6 := p4 + UInt256.ofNat 2
  let p7 := p6 + ⟨1⟩
  let p8 := p7 + ⟨1⟩
  let p9 := p8 + ⟨1⟩
  let p11 := p9 + UInt256.ofNat 2
  let p12 := p11 + ⟨1⟩
  let p13 := p12 + ⟨1⟩
  let p14 := p13 + ⟨1⟩
  let p17 := p14 + UInt256.ofNat 3
  let p18 := p17 + ⟨1⟩
  let p20 := p18 + UInt256.ofNat 2
  let p21 := p20 + ⟨1⟩
  p21 + ⟨1⟩

@[reducible] def daiAddressUint256ExternalEntryWf
    (pc ret routine : UInt256) : Prop :=
  let p1 := pc + ⟨1⟩
  let p4 := p1 + UInt256.ofNat 3
  let p6 := p4 + UInt256.ofNat 2
  let p7 := p6 + ⟨1⟩
  let p8 := p7 + ⟨1⟩
  let p9 := p8 + ⟨1⟩
  let p11 := p9 + UInt256.ofNat 2
  let p12 := p11 + ⟨1⟩
  let p13 := p12 + ⟨1⟩
  let p14 := p13 + ⟨1⟩
  let p17 := p14 + UInt256.ofNat 3
  let p18 := p17 + ⟨1⟩
  let p20 := p18 + UInt256.ofNat 2
  let p21 := p20 + ⟨1⟩
  let p22 := daiAddressUint256ExternalDecodedPc pc
  let p23 := p22 + ⟨1⟩
  let p24 := p23 + ⟨1⟩
  let p26 := p24 + UInt256.ofNat 2
  let p28 := p26 + UInt256.ofNat 2
  let p30 := p28 + UInt256.ofNat 2
  let p31 := p30 + ⟨1⟩
  let p32 := p31 + ⟨1⟩
  let p33 := p32 + ⟨1⟩
  let p34 := p33 + ⟨1⟩
  let p35 := p34 + ⟨1⟩
  let p36 := p35 + ⟨1⟩
  let p38 := p36 + UInt256.ofNat 2
  let p39 := p38 + ⟨1⟩
  let p40 := p39 + ⟨1⟩
  let p43 := p40 + UInt256.ofNat 3
  decode Benchmarks.Dss.Dai.daiBytecode pc = some (.JUMPDEST, .none)
  ∧ decode Benchmarks.Dss.Dai.daiBytecode p1 =
      some (.Push .PUSH2, some (ret, 2))
  ∧ decode Benchmarks.Dss.Dai.daiBytecode p4 =
      some (.Push .PUSH1, some (⟨4⟩, 1))
  ∧ decode Benchmarks.Dss.Dai.daiBytecode p6 = some (.DUP1, .none)
  ∧ decode Benchmarks.Dss.Dai.daiBytecode p7 = some (.CALLDATASIZE, .none)
  ∧ decode Benchmarks.Dss.Dai.daiBytecode p8 = some (.SUB, .none)
  ∧ decode Benchmarks.Dss.Dai.daiBytecode p9 =
      some (.Push .PUSH1, some (⟨64⟩, 1))
  ∧ decode Benchmarks.Dss.Dai.daiBytecode p11 = some (.DUP2, .none)
  ∧ decode Benchmarks.Dss.Dai.daiBytecode p12 = some (.LT, .none)
  ∧ decode Benchmarks.Dss.Dai.daiBytecode p13 = some (.ISZERO, .none)
  ∧ decode Benchmarks.Dss.Dai.daiBytecode p14 =
      some (.Push .PUSH2, some (p22, 2))
  ∧ decode Benchmarks.Dss.Dai.daiBytecode p17 = some (.JUMPI, .none)
  ∧ decode Benchmarks.Dss.Dai.daiBytecode p18 =
      some (.Push .PUSH1, some (⟨0⟩, 1))
  ∧ decode Benchmarks.Dss.Dai.daiBytecode p20 = some (.DUP1, .none)
  ∧ decode Benchmarks.Dss.Dai.daiBytecode p21 = some (.REVERT, .none)
  ∧ decode Benchmarks.Dss.Dai.daiBytecode p22 = some (.JUMPDEST, .none)
  ∧ decode Benchmarks.Dss.Dai.daiBytecode p23 = some (.POP, .none)
  ∧ decode Benchmarks.Dss.Dai.daiBytecode p24 =
      some (.Push .PUSH1, some (⟨1⟩, 1))
  ∧ decode Benchmarks.Dss.Dai.daiBytecode p26 =
      some (.Push .PUSH1, some (⟨1⟩, 1))
  ∧ decode Benchmarks.Dss.Dai.daiBytecode p28 =
      some (.Push .PUSH1, some (⟨160⟩, 1))
  ∧ decode Benchmarks.Dss.Dai.daiBytecode p30 = some (.SHL, .none)
  ∧ decode Benchmarks.Dss.Dai.daiBytecode p31 = some (.SUB, .none)
  ∧ decode Benchmarks.Dss.Dai.daiBytecode p32 = some (.DUP2, .none)
  ∧ decode Benchmarks.Dss.Dai.daiBytecode p33 = some (.CALLDATALOAD, .none)
  ∧ decode Benchmarks.Dss.Dai.daiBytecode p34 = some (.AND, .none)
  ∧ decode Benchmarks.Dss.Dai.daiBytecode p35 = some (.SWAP1, .none)
  ∧ decode Benchmarks.Dss.Dai.daiBytecode p36 =
      some (.Push .PUSH1, some (⟨32⟩, 1))
  ∧ decode Benchmarks.Dss.Dai.daiBytecode p38 = some (.ADD, .none)
  ∧ decode Benchmarks.Dss.Dai.daiBytecode p39 = some (.CALLDATALOAD, .none)
  ∧ decode Benchmarks.Dss.Dai.daiBytecode p40 =
      some (.Push .PUSH2, some (routine, 2))
  ∧ decode Benchmarks.Dss.Dai.daiBytecode p43 = some (.JUMP, .none)

macro "dai_address_uint256_external_entry_wf" : term =>
  `(by
    unfold Reasoning.Reach.daiAddressUint256ExternalEntryWf
      Reasoning.Reach.daiAddressUint256ExternalDecodedPc
    repeat' first | apply And.intro | decide +native)

set_option maxHeartbeats 1000000 in
theorem RD.daiAddressUint256ExternalLenOk {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel entry ret routine : UInt256}
    (hreach : ∃ k C, RD Benchmarks.Dss.Dai.daiBytecode I g
      (Reasoning.Theory.initState cA gh bl σ σ₀ g A I) entry [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hwf : daiAddressUint256ExternalEntryWf entry ret routine)
    (hdecoded : (D_J Benchmarks.Dss.Dai.daiBytecode 0).contains
      (daiAddressUint256ExternalDecodedPc entry) = true)
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size) :
    ∃ k C, RD Benchmarks.Dss.Dai.daiBytecode I g
      (Reasoning.Theory.initState cA gh bl σ σ₀ g A I)
      (daiAddressUint256ExternalDecodedPc entry)
      (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩ :: ⟨4⟩ :: ret :: [sel])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  rcases hwf with
    ⟨hd0, hd1, hd4, hd6, hd7, hd8, hd9, hd11, hd12, hd13, hd14, hd17, _hd18,
      _hd20, _hd21, _hd22, _hd23, _hd24, _hd26, _hd28, _hd30, _hd31, _hd32,
      _hd33, _hd34, _hd35, _hd36, _hd38, _hd39, _hd40, _hd43⟩
  exact RD.solcTwoAddressExternalLenOk hreach hd0 hd1 hd4 hd6 hd7 hd8 hd9
    hd11 hd12 hd13 hd14 hd17 hdecoded hsz68 hsize

set_option maxHeartbeats 1000000 in
theorem RD.daiAddressUint256ExternalMaskAndJumpMasked {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {entry ret routine de : UInt256} {R : List UInt256}
    {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD Benchmarks.Dss.Dai.daiBytecode ee g s0
      (daiAddressUint256ExternalDecodedPc entry) (de :: ⟨4⟩ :: ret :: R)
      solcFreePtrMem (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hwf : daiAddressUint256ExternalEntryWf entry ret routine)
    (hroutine : (D_J Benchmarks.Dss.Dai.daiBytecode 0).contains routine = true)
    (hov : R.length + 6 ≤ 1024) :
    ∃ k' C', RD Benchmarks.Dss.Dai.daiBytecode ee g s0 routine
      (calldataWord ee.calldata 36 ::
        UInt256.land solcAddrMask (calldataWord ee.calldata 4) :: ret :: R)
      solcFreePtrMem (UInt256.ofNat 3) rdata (cA, σ) k' C' := by
  rcases hwf with
    ⟨_hd0, _hd1, _hd4, _hd6, _hd7, _hd8, _hd9, _hd11, _hd12, _hd13, _hd14,
      _hd17, _hd18, _hd20, _hd21, hd22, hd23, hd24, hd26, hd28, hd30, hd31,
      hd32, hd33, hd34, hd35, hd36, hd38, hd39, hd40, hd43⟩
  exact RD.solcAddressUint256ExternalMaskAndJumpMasked h hd22 hd23 hd24 hd26
    hd28 hd30 hd31 hd32 hd33 hd34 hd35 hd36 hd38 hd39 hd40 hd43 hroutine hov

set_option maxHeartbeats 1000000 in
theorem RD.daiAddressUint256ExternalShort {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel entry ret routine : UInt256}
    (hreach : ∃ k C, RD Benchmarks.Dss.Dai.daiBytecode I g
      (Reasoning.Theory.initState cA gh bl σ σ₀ g A I) entry [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hwf : daiAddressUint256ExternalEntryWf entry ret routine)
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 68) :
    RDrev Benchmarks.Dss.Dai.daiBytecode g
      (Reasoning.Theory.initState cA gh bl σ σ₀ g A I) := by
  have hlt :
      UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ = ⟨1⟩ := by
    apply ult_one
    rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide,
      usub_ofNat_word_toNat (c := (⟨4⟩ : UInt256)) (by simpa using hsz4) hsize,
      show (⟨4⟩ : UInt256).toNat = 4 from by decide]
    omega
  rcases hwf with
    ⟨hd0, hd1, hd4, hd6, hd7, hd8, hd9, hd11, hd12, hd13, hd14, hd17, hd18,
      hd20, hd21, _hd22, _hd23, _hd24, _hd26, _hd28, _hd30, _hd31, _hd32,
      _hd33, _hd34, _hd35, _hd36, _hd38, _hd39, _hd40, _hd43⟩
  exact RD.solcExternalStaticArgsShortReverts hreach hd0 hd1 hd4 hd6 hd7 hd8
    hd9 hd11 hd12 hd13 hd14 hd17 hd18 hd20 hd21 hlt

/-! ## Shared address,address,uint256 external wrapper -/

@[reducible] def daiAddressAddressUint256ExternalDecodedPc (pc : UInt256) : UInt256 :=
  let p1 := pc + ⟨1⟩
  let p4 := p1 + UInt256.ofNat 3
  let p6 := p4 + UInt256.ofNat 2
  let p7 := p6 + ⟨1⟩
  let p8 := p7 + ⟨1⟩
  let p9 := p8 + ⟨1⟩
  let p11 := p9 + UInt256.ofNat 2
  let p12 := p11 + ⟨1⟩
  let p13 := p12 + ⟨1⟩
  let p14 := p13 + ⟨1⟩
  let p17 := p14 + UInt256.ofNat 3
  let p18 := p17 + ⟨1⟩
  let p20 := p18 + UInt256.ofNat 2
  let p21 := p20 + ⟨1⟩
  p21 + ⟨1⟩

@[reducible] def daiAddressAddressUint256ExternalEntryWf
    (pc ret routine : UInt256) : Prop :=
  let p1 := pc + ⟨1⟩
  let p4 := p1 + UInt256.ofNat 3
  let p6 := p4 + UInt256.ofNat 2
  let p7 := p6 + ⟨1⟩
  let p8 := p7 + ⟨1⟩
  let p9 := p8 + ⟨1⟩
  let p11 := p9 + UInt256.ofNat 2
  let p12 := p11 + ⟨1⟩
  let p13 := p12 + ⟨1⟩
  let p14 := p13 + ⟨1⟩
  let p17 := p14 + UInt256.ofNat 3
  let p18 := p17 + ⟨1⟩
  let p20 := p18 + UInt256.ofNat 2
  let p21 := p20 + ⟨1⟩
  let p22 := daiAddressAddressUint256ExternalDecodedPc pc
  let p23 := p22 + ⟨1⟩
  let p24 := p23 + ⟨1⟩
  let p26 := p24 + UInt256.ofNat 2
  let p28 := p26 + UInt256.ofNat 2
  let p30 := p28 + UInt256.ofNat 2
  let p31 := p30 + ⟨1⟩
  let p32 := p31 + ⟨1⟩
  let p33 := p32 + ⟨1⟩
  let p34 := p33 + ⟨1⟩
  let p35 := p34 + ⟨1⟩
  let p36 := p35 + ⟨1⟩
  let p37 := p36 + ⟨1⟩
  let p39 := p37 + UInt256.ofNat 2
  let p40 := p39 + ⟨1⟩
  let p41 := p40 + ⟨1⟩
  let p42 := p41 + ⟨1⟩
  let p43 := p42 + ⟨1⟩
  let p44 := p43 + ⟨1⟩
  let p45 := p44 + ⟨1⟩
  let p46 := p45 + ⟨1⟩
  let p48 := p46 + UInt256.ofNat 2
  let p49 := p48 + ⟨1⟩
  let p50 := p49 + ⟨1⟩
  let p53 := p50 + UInt256.ofNat 3
  decode Benchmarks.Dss.Dai.daiBytecode pc = some (.JUMPDEST, .none)
  ∧ decode Benchmarks.Dss.Dai.daiBytecode p1 =
      some (.Push .PUSH2, some (ret, 2))
  ∧ decode Benchmarks.Dss.Dai.daiBytecode p4 =
      some (.Push .PUSH1, some (⟨4⟩, 1))
  ∧ decode Benchmarks.Dss.Dai.daiBytecode p6 = some (.DUP1, .none)
  ∧ decode Benchmarks.Dss.Dai.daiBytecode p7 = some (.CALLDATASIZE, .none)
  ∧ decode Benchmarks.Dss.Dai.daiBytecode p8 = some (.SUB, .none)
  ∧ decode Benchmarks.Dss.Dai.daiBytecode p9 =
      some (.Push .PUSH1, some (⟨96⟩, 1))
  ∧ decode Benchmarks.Dss.Dai.daiBytecode p11 = some (.DUP2, .none)
  ∧ decode Benchmarks.Dss.Dai.daiBytecode p12 = some (.LT, .none)
  ∧ decode Benchmarks.Dss.Dai.daiBytecode p13 = some (.ISZERO, .none)
  ∧ decode Benchmarks.Dss.Dai.daiBytecode p14 =
      some (.Push .PUSH2, some (p22, 2))
  ∧ decode Benchmarks.Dss.Dai.daiBytecode p17 = some (.JUMPI, .none)
  ∧ decode Benchmarks.Dss.Dai.daiBytecode p18 =
      some (.Push .PUSH1, some (⟨0⟩, 1))
  ∧ decode Benchmarks.Dss.Dai.daiBytecode p20 = some (.DUP1, .none)
  ∧ decode Benchmarks.Dss.Dai.daiBytecode p21 = some (.REVERT, .none)
  ∧ decode Benchmarks.Dss.Dai.daiBytecode p22 = some (.JUMPDEST, .none)
  ∧ decode Benchmarks.Dss.Dai.daiBytecode p23 = some (.POP, .none)
  ∧ decode Benchmarks.Dss.Dai.daiBytecode p24 =
      some (.Push .PUSH1, some (⟨1⟩, 1))
  ∧ decode Benchmarks.Dss.Dai.daiBytecode p26 =
      some (.Push .PUSH1, some (⟨1⟩, 1))
  ∧ decode Benchmarks.Dss.Dai.daiBytecode p28 =
      some (.Push .PUSH1, some (⟨160⟩, 1))
  ∧ decode Benchmarks.Dss.Dai.daiBytecode p30 = some (.SHL, .none)
  ∧ decode Benchmarks.Dss.Dai.daiBytecode p31 = some (.SUB, .none)
  ∧ decode Benchmarks.Dss.Dai.daiBytecode p32 = some (.DUP2, .none)
  ∧ decode Benchmarks.Dss.Dai.daiBytecode p33 = some (.CALLDATALOAD, .none)
  ∧ decode Benchmarks.Dss.Dai.daiBytecode p34 = some (.DUP2, .none)
  ∧ decode Benchmarks.Dss.Dai.daiBytecode p35 = some (.AND, .none)
  ∧ decode Benchmarks.Dss.Dai.daiBytecode p36 = some (.SWAP2, .none)
  ∧ decode Benchmarks.Dss.Dai.daiBytecode p37 =
      some (.Push .PUSH1, some (⟨32⟩, 1))
  ∧ decode Benchmarks.Dss.Dai.daiBytecode p39 = some (.DUP2, .none)
  ∧ decode Benchmarks.Dss.Dai.daiBytecode p40 = some (.ADD, .none)
  ∧ decode Benchmarks.Dss.Dai.daiBytecode p41 = some (.CALLDATALOAD, .none)
  ∧ decode Benchmarks.Dss.Dai.daiBytecode p42 = some (.SWAP1, .none)
  ∧ decode Benchmarks.Dss.Dai.daiBytecode p43 = some (.SWAP2, .none)
  ∧ decode Benchmarks.Dss.Dai.daiBytecode p44 = some (.AND, .none)
  ∧ decode Benchmarks.Dss.Dai.daiBytecode p45 = some (.SWAP1, .none)
  ∧ decode Benchmarks.Dss.Dai.daiBytecode p46 =
      some (.Push .PUSH1, some (⟨64⟩, 1))
  ∧ decode Benchmarks.Dss.Dai.daiBytecode p48 = some (.ADD, .none)
  ∧ decode Benchmarks.Dss.Dai.daiBytecode p49 = some (.CALLDATALOAD, .none)
  ∧ decode Benchmarks.Dss.Dai.daiBytecode p50 =
      some (.Push .PUSH2, some (routine, 2))
  ∧ decode Benchmarks.Dss.Dai.daiBytecode p53 = some (.JUMP, .none)

macro "dai_address_address_uint256_external_entry_wf" : term =>
  `(by
    unfold Reasoning.Reach.daiAddressAddressUint256ExternalEntryWf
      Reasoning.Reach.daiAddressAddressUint256ExternalDecodedPc
    repeat' first | apply And.intro | decide +native)

set_option maxHeartbeats 1000000 in
theorem RD.daiAddressAddressUint256ExternalLenOk {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel entry ret routine : UInt256}
    (hreach : ∃ k C, RD Benchmarks.Dss.Dai.daiBytecode I g
      (Reasoning.Theory.initState cA gh bl σ σ₀ g A I) entry [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hwf : daiAddressAddressUint256ExternalEntryWf entry ret routine)
    (hdecoded : (D_J Benchmarks.Dss.Dai.daiBytecode 0).contains
      (daiAddressAddressUint256ExternalDecodedPc entry) = true)
    (hsz100 : 100 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size) :
    ∃ k C, RD Benchmarks.Dss.Dai.daiBytecode I g
      (Reasoning.Theory.initState cA gh bl σ σ₀ g A I)
      (daiAddressAddressUint256ExternalDecodedPc entry)
      (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩ :: ⟨4⟩ :: ret :: [sel])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hlt :
      UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨96⟩ = ⟨0⟩ := by
    exact solcDecodeLenCheckOkUnsigned (by simpa using hsz100) hsize
  rcases hwf with
    ⟨hd0, hd1, hd4, hd6, hd7, hd8, hd9, hd11, hd12, hd13, hd14, hd17, _hd18,
      _hd20, _hd21, _hd22, _hd23, _hd24, _hd26, _hd28, _hd30, _hd31, _hd32,
      _hd33, _hd34, _hd35, _hd36, _hd37, _hd39, _hd40, _hd41, _hd42, _hd43,
      _hd44, _hd45, _hd46, _hd48, _hd49, _hd50, _hd53⟩
  exact RD.solcExternalStaticArgsLenOk hreach hd0 hd1 hd4 hd6 hd7 hd8 hd9
    hd11 hd12 hd13 hd14 hd17 hdecoded hlt

set_option maxHeartbeats 1000000 in
theorem RD.daiAddressAddressUint256ExternalMaskAndJumpMasked {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {entry ret routine de : UInt256} {R : List UInt256}
    {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD Benchmarks.Dss.Dai.daiBytecode ee g s0
      (daiAddressAddressUint256ExternalDecodedPc entry) (de :: ⟨4⟩ :: ret :: R)
      solcFreePtrMem (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hwf : daiAddressAddressUint256ExternalEntryWf entry ret routine)
    (hroutine : (D_J Benchmarks.Dss.Dai.daiBytecode 0).contains routine = true)
    (hov : R.length + 7 ≤ 1024) :
    ∃ k' C', RD Benchmarks.Dss.Dai.daiBytecode ee g s0 routine
      (calldataWord ee.calldata 68 ::
        UInt256.land solcAddrMask (calldataWord ee.calldata 36) ::
        UInt256.land solcAddrMask (calldataWord ee.calldata 4) :: ret :: R)
      solcFreePtrMem (UInt256.ofNat 3) rdata (cA, σ) k' C' := by
  rcases hwf with
    ⟨_hd0, _hd1, _hd4, _hd6, _hd7, _hd8, _hd9, _hd11, _hd12, _hd13, _hd14,
      _hd17, _hd18, _hd20, _hd21, hd22, hd23, hd24, hd26, hd28, hd30, hd31,
      hd32, hd33, hd34, hd35, hd36, hd37, hd39, hd40, hd41, hd42, hd43, hd44,
      hd45, hd46, hd48, hd49, hd50, hd53⟩
  exact RD.solcAddressAddressUint256ExternalMaskAndJumpMasked h hd22 hd23 hd24
    hd26 hd28 hd30 hd31 hd32 hd33 hd34 hd35 hd36 hd37 hd39 hd40 hd41 hd42
    hd43 hd44 hd45 hd46 hd48 hd49 hd50 hd53 hroutine hov

set_option maxHeartbeats 1000000 in
theorem RD.daiAddressAddressUint256ExternalShort {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel entry ret routine : UInt256}
    (hreach : ∃ k C, RD Benchmarks.Dss.Dai.daiBytecode I g
      (Reasoning.Theory.initState cA gh bl σ σ₀ g A I) entry [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hwf : daiAddressAddressUint256ExternalEntryWf entry ret routine)
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 100) :
    RDrev Benchmarks.Dss.Dai.daiBytecode g
      (Reasoning.Theory.initState cA gh bl σ σ₀ g A I) := by
  have hlt :
      UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨96⟩ = ⟨1⟩ := by
    apply ult_one
    rw [show (⟨96⟩ : UInt256).toNat = 96 from by decide,
      usub_ofNat_word_toNat (c := (⟨4⟩ : UInt256)) (by simpa using hsz4) hsize,
      show (⟨4⟩ : UInt256).toNat = 4 from by decide]
    omega
  rcases hwf with
    ⟨hd0, hd1, hd4, hd6, hd7, hd8, hd9, hd11, hd12, hd13, hd14, hd17, hd18,
      hd20, hd21, _hd22, _hd23, _hd24, _hd26, _hd28, _hd30, _hd31, _hd32,
      _hd33, _hd34, _hd35, _hd36, _hd37, _hd39, _hd40, _hd41, _hd42, _hd43,
      _hd44, _hd45, _hd46, _hd48, _hd49, _hd50, _hd53⟩
  exact RD.solcExternalStaticArgsShortReverts hreach hd0 hd1 hd4 hd6 hd7 hd8
    hd9 hd11 hd12 hd13 hd14 hd17 hd18 hd20 hd21 hlt

/-! ## Shared word return block -/

@[reducible] def daiReturnWordFromMemWf (pc : UInt256) : Prop :=
  solcReturnWordFromMemWf Benchmarks.Dss.Dai.daiBytecode pc

macro "dai_return_word_from_mem_wf" : term =>
  `(by
    unfold Reasoning.Reach.daiReturnWordFromMemWf
      Reasoning.Reach.solcReturnWordFromMemWf
    repeat' first | apply And.intro | decide +native)

theorem RD.daiReturnWordFromMem {g : Sat256} {s0 : State} {ee : ExecutionEnv} {k C : ℕ}
    {pc val ret : UInt256} {R : List UInt256} {mem memout rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD Benchmarks.Dss.Dai.daiBytecode ee g s0 pc (val :: ret :: R) mem
      (UInt256.ofNat 3) rdata acc k C)
    (hwf : daiReturnWordFromMemWf pc)
    (hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 3 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32)))
        = ⟨128⟩)
    (hmemout : (UInt256.toByteArray val).write 0 mem 128 32 = memout)
    (hmemoutLoad64 :
      (if (⟨64⟩ : UInt256).toNat ≥ memout.size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 5 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (memout.readWithPadding (⟨64⟩ : UInt256).toNat 32)))
        = ⟨128⟩)
    (hread128 : memout.readWithPadding 128 32 = UInt256.toByteArray val)
    (hov : R.length + 5 ≤ 1024) :
    RDret Benchmarks.Dss.Dai.daiBytecode g s0 acc (UInt256.toByteArray val) := by
  exact RD.solcReturnWordFromMem h hwf hmload64 hmemout hmemoutLoad64 hread128 hov

/-! ## Shared no-argument storage-word getter -/

@[reducible] def daiGetterEntryWf (pc returnPc routine : UInt256) : Prop :=
  solcGetterEntryWf Benchmarks.Dss.Dai.daiBytecode pc returnPc routine

macro "dai_getter_entry_wf" : term =>
  `(by
    unfold Reasoning.Reach.daiGetterEntryWf
      Reasoning.Reach.solcGetterEntryWf
    repeat' first | apply And.intro | decide +native)

@[reducible] def daiWordSlotGetterWf (pc slot : UInt256) : Prop :=
  solcWordSlotGetterWf Benchmarks.Dss.Dai.daiBytecode pc slot

macro "dai_word_slot_getter_wf" : term =>
  `(by
    unfold Reasoning.Reach.daiWordSlotGetterWf
      Reasoning.Reach.solcWordSlotGetterWf
    repeat' first | apply And.intro | decide +native)

@[reducible] def daiConstGetterWf
    (pc val : UInt256) (width : Nat) (op : Operation.POp) : Prop :=
  solcConstGetterWf Benchmarks.Dss.Dai.daiBytecode pc val width op

macro "dai_const_getter_wf" : term =>
  `(by
    unfold Reasoning.Reach.daiConstGetterWf
      Reasoning.Reach.solcConstGetterWf
    repeat' first | apply And.intro | decide +native)

@[reducible] def daiReturnUint8FromMemWf (pc : UInt256) : Prop :=
  solcReturnUint8FromMemWf Benchmarks.Dss.Dai.daiBytecode pc

macro "dai_return_uint8_from_mem_wf" : term =>
  `(by
    unfold Reasoning.Reach.daiReturnUint8FromMemWf
      Reasoning.Reach.solcReturnUint8FromMemWf
    repeat' first | apply And.intro | decide +native)

theorem RD.daiWordGetterExternal {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel entry routine slot returnPc : UInt256}
    (hreach : ∃ k C, RD Benchmarks.Dss.Dai.daiBytecode I g
      (Reasoning.Theory.initState cA gh bl σ σ₀ g A I) entry [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hentry : daiGetterEntryWf entry returnPc routine)
    (hgetter : daiWordSlotGetterWf routine slot)
    (hroutine : (D_J Benchmarks.Dss.Dai.daiBytecode 0).contains routine = true)
    (hret : (D_J Benchmarks.Dss.Dai.daiBytecode 0).contains returnPc = true)
    (hreturn : daiReturnWordFromMemWf returnPc) :
    RDret Benchmarks.Dss.Dai.daiBytecode g
      (Reasoning.Theory.initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray
        (σ.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD slot ⟨0⟩))) := by
  simpa [daiGetterEntryWf, daiWordSlotGetterWf, daiReturnWordFromMemWf, solcSlotWord] using
    RD.solcWordGetterExternal hreach hentry hgetter hroutine hret hreturn

theorem RD.daiWordConstGetterExternal {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel entry routine returnPc val : UInt256} {width : Nat} {op : Operation.POp}
    (hreach : ∃ k C, RD Benchmarks.Dss.Dai.daiBytecode I g
      (Reasoning.Theory.initState cA gh bl σ σ₀ g A I) entry [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hentry : daiGetterEntryWf entry returnPc routine)
    (hgetter : daiConstGetterWf routine val width op)
    (hroutine : (D_J Benchmarks.Dss.Dai.daiBytecode 0).contains routine = true)
    (hret : (D_J Benchmarks.Dss.Dai.daiBytecode 0).contains returnPc = true)
    (hreturn : daiReturnWordFromMemWf returnPc) :
    RDret Benchmarks.Dss.Dai.daiBytecode g
      (Reasoning.Theory.initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray val) := by
  simpa [daiGetterEntryWf, daiConstGetterWf, daiReturnWordFromMemWf] using
    RD.solcWordConstGetterExternal hreach hentry hgetter hroutine hret hreturn

theorem RD.daiUint8ConstGetterExternal {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel entry routine returnPc val : UInt256} {width : Nat} {op : Operation.POp}
    (hreach : ∃ k C, RD Benchmarks.Dss.Dai.daiBytecode I g
      (Reasoning.Theory.initState cA gh bl σ σ₀ g A I) entry [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hentry : daiGetterEntryWf entry returnPc routine)
    (hgetter : daiConstGetterWf routine val width op)
    (hroutine : (D_J Benchmarks.Dss.Dai.daiBytecode 0).contains routine = true)
    (hret : (D_J Benchmarks.Dss.Dai.daiBytecode 0).contains returnPc = true)
    (hreturn : daiReturnUint8FromMemWf returnPc) :
    RDret Benchmarks.Dss.Dai.daiBytecode g
      (Reasoning.Theory.initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray (UInt256.land val ⟨255⟩)) := by
  simpa [daiGetterEntryWf, daiConstGetterWf, daiReturnUint8FromMemWf] using
    RD.solcUint8ConstGetterExternal hreach hentry hgetter hroutine hret hreturn

end Reasoning.Reach
