import Benchmarks.Dss.Dog.Dispatch

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Dss.Dog.Immutables

namespace Benchmarks.Dss.Dog

theorem dogDecode_vat {v : DogImmutables} {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size) :
    decodeCalldataWithMode (config v).abiDecodeMode ((vatTransition v).params.map Param.name)
      (transitionSignature (vatTransition v)).paramTypes I.calldata = some ∅ := by
  show decodeCalldataWithMode DecodeMode.legacySolc05 [] [] I.calldata = some ∅
  exact decodeCalldata_empty_ok hsz

theorem dogReachVatBody {v : DogImmutables} {code : ByteArray}
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (hcode : I.code = code) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (dogSelBytes 14)) :
    ∃ k C, RD code I g (initState cA gh bl σ σ₀ g A I) ⟨350⟩
      [solcSelectorWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hword : solcSelectorWord I = ⟨0x36569e77⟩ :=
    solcSelectorWord_eq_of_beq I hsz 0x36 0x56 0x9e 0x77 ⟨0x36569e77⟩
      (by decide +native) (by simpa [dogSelBytes] using hsel)
  obtain ⟨k32, C32, h32⟩ :=
    dogReachSelector (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hpatch hcode hwv hsz hsize
  have hrootTgt : armTgt code (⟨32⟩ : UInt256) = ⟨162⟩ := by
    dsimp [armTgt]
    rw [dogPushAtPatchedEqTemplate1405 (pc := selArmPushTgtPc (⟨32⟩ : UInt256))
      hpatch (by decide +native)]
    decide +native
  have hlowTgt : armTgt code (⟨163⟩ : UInt256) = ⟨222⟩ := by
    dsimp [armTgt]
    rw [dogPushAtPatchedEqTemplate1405 (pc := selArmPushTgtPc (⟨163⟩ : UInt256))
      hpatch (by decide +native)]
    decide +native
  have hroot :
      UInt256.gt (armSelNat code (⟨32⟩ : UInt256)) (solcSelectorWord I) ≠ ⟨0⟩ := by
    rw [hword]
    dsimp [armSelNat]
    rw [dogPushAtPatchedEqTemplate1405 (pc := selArmPush4Pc (⟨32⟩ : UInt256))
      hpatch (by decide +native)]
    decide +native
  have h162 : RD code I g (initState cA gh bl σ σ₀ g A I) ⟨162⟩
      [solcSelectorWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) (k32 + 5) (C32 + 22) := by
    simpa [hrootTgt] using
      RD.selectorSplitTakenAuto h32 (dogRootSplitWellFormed hpatch) hroot
        (by
          rw [hrootTgt]
          exact dogPatchedDJumpPrefix1405 ⟨162⟩ hpatch (by decide +native))
        (by simp)
  have h163 : RD code I g (initState cA gh bl σ σ₀ g A I) ⟨163⟩
      [solcSelectorWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) (k32 + 5 + 1) (C32 + 22 + 1) := by
    simpa using
      h162.jumpdest
        (by
          rw [dogDecodePatchedEqTemplate1405 (pc := ⟨162⟩) hpatch (by decide +native)]
          decide +native)
        (by simp only [List.length_singleton]; omega)
  have hlow :
      UInt256.gt (armSelNat code (⟨163⟩ : UInt256)) (solcSelectorWord I) ≠ ⟨0⟩ := by
    rw [hword]
    dsimp [armSelNat]
    rw [dogPushAtPatchedEqTemplate1405 (pc := selArmPush4Pc (⟨163⟩ : UInt256))
      hpatch (by decide +native)]
    decide +native
  have h222 : RD code I g (initState cA gh bl σ σ₀ g A I) ⟨222⟩
      [solcSelectorWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) (k32 + 5 + 1 + 5) (C32 + 22 + 1 + 22) := by
    simpa [hlowTgt] using
      RD.selectorSplitTakenAuto h163 (dogLowSplitWellFormed hpatch) hlow
        (by
          rw [hlowTgt]
          exact dogPatchedDJumpPrefix1405 ⟨222⟩ hpatch (by decide +native))
        (by simp)
  have h223 : RD code I g (initState cA gh bl σ σ₀ g A I) ⟨223⟩
      [solcSelectorWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) (k32 + 5 + 1 + 5 + 1) (C32 + 22 + 1 + 22 + 1) := by
    simpa using
      h222.jumpdest
        (by
          rw [dogDecodePatchedEqTemplate1405 (pc := ⟨222⟩) hpatch (by decide +native)]
          decide +native)
        (by simp only [List.length_singleton]; omega)
  have hfileIlkUint : UInt256.eq (dogSelectorWord 7) (solcSelectorWord I) = ⟨0⟩ := by
    rw [hword]
    decide +native
  have hfileUint : UInt256.eq (dogSelectorWord 8) (solcSelectorWord I) = ⟨0⟩ := by
    rw [hword]
    decide +native
  have hvat : UInt256.eq (dogSelectorWord 14) (solcSelectorWord I) ≠ ⟨0⟩ := by
    rw [hword]
    decide +native
  have h234 := by
    simpa [selArmNextPc] using
      h223.selectorArmNotTaken (selNat := dogSelectorWord 7) (tgt := (⟨272⟩ : UInt256))
        (width := 2) (op := .PUSH2)
        (by
          rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]
          decide +native)
        (by
          rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]
          decide +native)
        (by
          rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]
          decide +native)
        (by decide)
        (by
          rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]
          decide +native)
        (by
          rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]
          decide +native)
        hfileIlkUint
        (by simp)
  have h245 := by
    simpa [selArmNextPc] using
      h234.selectorArmNotTaken (selNat := dogSelectorWord 8) (tgt := (⟨315⟩ : UInt256))
        (width := 2) (op := .PUSH2)
        (by
          rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]
          decide +native)
        (by
          rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]
          decide +native)
        (by
          rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]
          decide +native)
        (by decide)
        (by
          rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]
          decide +native)
        (by
          rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]
          decide +native)
        hfileUint
        (by simp)
  have h350 := by
    simpa using
      h245.selectorArmTaken (selNat := dogSelectorWord 14) (tgt := (⟨350⟩ : UInt256))
        (width := 2) (op := .PUSH2)
        (by
          rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]
          decide +native)
        (by
          rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]
          decide +native)
        (by
          rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]
          decide +native)
        (by decide)
        (by
          rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]
          decide +native)
        (by
          rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]
          decide +native)
        hvat
        (dogPatchedDJumpPrefix1405 ⟨350⟩ hpatch (by decide +native))
        (by simp)
  exact ⟨_, _, h350⟩

theorem dogVatPatchWord {v : DogImmutables} {code : ByteArray}
    (hpatch : patchRuntime dogBytecode (patches v) = some code) :
    code.extract 1405 1437 = UInt256.toByteArray (EVM.Word.ofNat v.vat.toNat) := by
  let value := UInt256.toByteArray (EVM.Word.ofNat v.vat.toNat)
  let post : List (Nat × ByteArray) := [(2890, value), (3170, value), (3965, value)]
  have hpatch' : patchRuntime dogBytecode ((1405, value) :: post) = some code := by
    dsimp [post, value]
    simpa [patches, patchesFrom, offsets, immValues, wordBytes?, valueToWord, List.lookup,
      toByteArray_eq_toBytesBE] using hpatch
  have hpost : ∀ p ∈ post, 1405 + 32 ≤ p.1 ∨ p.1 + 32 ≤ 1405 := by
    intro p hp
    dsimp [post] at hp
    simp at hp
    rcases hp with rfl | rfl | rfl <;> omega
  have hsize : value.size = 32 := by
    dsimp [value]
    exact toByteArray_size _
  exact patchRuntime_extract_patch (template := dogBytecode) (out := code)
    (value := value) (pre := []) (post := post) (offset := 1405) hsize hpost hpatch'

theorem dogVatGetterJumpdestDecode {v : DogImmutables} {code : ByteArray}
    (hpatch : patchRuntime dogBytecode (patches v) = some code) :
    decode code ⟨1403⟩ = some (.JUMPDEST, .none) := by
  refine dogDecodePatchedNoArg (pc := ⟨1403⟩) (byte := 0x5b) (op := .JUMPDEST)
    hpatch (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native)

theorem dogVatConstDecode {v : DogImmutables} {code : ByteArray}
    (hpatch : patchRuntime dogBytecode (patches v) = some code) :
    decode code ⟨1404⟩ =
      some (.Push .PUSH32, some (EVM.Word.ofNat v.vat.toNat, 32)) := by
  have hsize := dogPatchedSize hpatch
  have hget : code.get? ({ val := 1404 } : UInt256).toNat =
      dogBytecode.get? ({ val := 1404 } : UInt256).toNat := by
    change code.get? 1404 = dogBytecode.get? 1404
    apply get?_eq_of_extract_one
    · rw [hsize]
      decide +native
    · decide +native
    · exact patchRuntime_extract_eq (start := 1404) (stop := 1405)
        (template := dogBytecode) (out := code) (ps := patches v)
        (by omega) (by decide +native)
        (by
          intro p hp
          have hm := dogPatchOffsetMem v p hp
          simp [dogPatchOffsets] at hm
          rcases hm with h | h | h | h
          · rw [h]
            omega
          · rw [h]
            omega
          · rw [h]
            omega
          · rw [h]
            omega)
        hpatch
  have hextract : code.extract' ({ val := 1404 } : UInt256).toNat.succ
      (({ val := 1404 } : UInt256).toNat.succ + 32) =
      UInt256.toByteArray (EVM.Word.ofNat v.vat.toNat) := by
    change code.extract' 1405 1437 = UInt256.toByteArray (EVM.Word.ofNat v.vat.toNat)
    unfold ByteArray.extract'
    have hguard : (decide (1405 < 2 ^ 64) && decide (1437 < 2 ^ 64)) = true := by
      decide +native
    rw [if_pos hguard]
    exact dogVatPatchWord hpatch
  have hgetSome : code.get? ({ val := 1404 } : UInt256).toNat = some 0x7f := by
    rw [hget]
    decide +native
  have hparse : (some (0x7f : UInt8) >>= parseInstr) = some (.Push .PUSH32) := by
    decide +native
  unfold decode
  rw [hgetSome, hparse]
  change some (Operation.Push Operation.POp.PUSH32,
      some (uInt256OfByteArray
        (code.extract' ({ val := 1404 } : UInt256).toNat.succ
          (({ val := 1404 } : UInt256).toNat.succ + 32)), 32)) =
    some (Operation.Push Operation.POp.PUSH32, some (EVM.Word.ofNat v.vat.toNat, 32))
  rw [hextract, uInt256OfByteArray_eq, fromByteArrayBigEndian_toByteArray, u256_ofNat_toNat]

theorem dogVatGetterDupDecode {v : DogImmutables} {code : ByteArray}
    (hpatch : patchRuntime dogBytecode (patches v) = some code) :
    decode code ⟨1437⟩ = some (.DUP2, .none) := by
  refine dogDecodePatchedNoArg (pc := ⟨1437⟩) (byte := 0x81) (op := .DUP2)
    hpatch (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native)

theorem dogVatGetterJumpDecode {v : DogImmutables} {code : ByteArray}
    (hpatch : patchRuntime dogBytecode (patches v) = some code) :
    decode code ⟨1438⟩ = some (.JUMP, .none) := by
  refine dogDecodePatchedNoArg (pc := ⟨1438⟩) (byte := 0x56) (op := .JUMP)
    hpatch (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native)

theorem dogVatGetterWf {v : DogImmutables} {code : ByteArray}
    (hpatch : patchRuntime dogBytecode (patches v) = some code) :
    solcConstGetterWf code ⟨1403⟩ (EVM.Word.ofNat v.vat.toNat) 32 .PUSH32 := by
  dsimp [solcConstGetterWf]
  exact ⟨dogVatGetterJumpdestDecode hpatch, by decide +native, dogVatConstDecode hpatch,
    dogVatGetterDupDecode hpatch, dogVatGetterJumpDecode hpatch⟩

theorem dogVatBodyCore {v : DogImmutables} {code : ByteArray}
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (_hpatch : patchRuntime dogBytecode (patches v) = some code)
    (_hcode : I.code = code)
    (_hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true)
    (_hwv : I.weiValue = ⟨0⟩)
    (_hsel : selIs I (dogSelBytes 14))
    (_hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor (config v) (contract v) cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (dogSelBytes 14) rfl _hsel
  have hbody :
      ExecTransitionBody (config v) (contract v)
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅
        (vatTransition v).body
        (.returned { contract := contract v, locals := ∅ }
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (some [(.address (AccountAddress.ofNat v.vat.toNat))])) := by
    simpa [vatTransition, vatExpr, nonpayable] using
      nonpayableReturnExprBodyReturns (cfg := config v) (contract := contract v)
        (evm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (locals := (∅ : Store)) (expr := addrLit v.vat)
        (value := Value.address (AccountAddress.ofNat v.vat.toNat))
        (by simp only [initState]; exact _hwv)
        (by
          exact dogAddrLitEval (v := v) (cA := cA) (gh := gh) (bl := bl)
            (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
            (g := Sat256.ofUInt256 g) v.vat)
  have hreach : ∃ k C, RD code I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨350⟩
      [solcSelectorWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ_evm) k C :=
    dogReachVatBody (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
      (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
      _hpatch _hcode _hwv hsz _hsize _hsel
  have hret :
      RDret code (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) (cA, σ_evm)
        (UInt256.toByteArray (UInt256.land (EVM.Word.ofNat v.vat.toNat) solcAddrMask)) :=
    RD.solcAddressConstGetterExternal
    (code := code) (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
    (A := A) (I := I) (g := Sat256.ofUInt256 g)
    (sel := solcSelectorWord I) (entry := ⟨350⟩) (routine := ⟨1403⟩)
    (returnPc := ⟨358⟩) (val := EVM.Word.ofNat v.vat.toNat) (width := 32)
    (op := .PUSH32) hreach
    (by
      unfold solcGetterEntryWf
      repeat' first
        | apply And.intro
        | rw [dogDecodePatchedEqTemplate1405 _hpatch (by decide +native)]
          decide +native)
    (dogVatGetterWf _hpatch)
    (dogPatchedJumpDest _hpatch (by decide +native))
    (dogPatchedDJumpPrefix1405 ⟨358⟩ _hpatch (by decide +native))
    (by
      unfold solcReturnAddressFromMemWf
      repeat' first
        | apply And.intro
        | rw [dogDecodePatchedEqTemplate1405 _hpatch (by decide +native)]
          decide +native)
  have henc :
      returnEquiv
        (UInt256.toByteArray (UInt256.land (EVM.Word.ofNat v.vat.toNat) solcAddrMask))
        (some [(.address (AccountAddress.ofNat
          (UInt256.land (EVM.Word.ofNat v.vat.toNat) solcAddrMask).toNat))])
        (vatTransition v).returnType := by
    rw [show (vatTransition v).returnType = [addr] by rfl]
    exact returnEquiv_of_encode
      (solcAddressReturnEncoding (addrTy := addr) rfl (EVM.Word.ofNat v.vat.toNat))
  exact hret.reEquivExecutionTransport _hcode (dogDispatchVat _hsel)
    (dogDecode_vat (v := v) hsz) hbody (dogAddressValueTransport v.vat) _hAccounts henc

end Benchmarks.Dss.Dog
