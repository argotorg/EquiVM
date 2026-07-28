import Benchmarks.Dss.Cat.BiteBody

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

namespace Benchmarks.Dss.Cat

/-! # Cat `bite` — reusable revert-branch composite (`catBiteMapUrns`)

The revert analog of `catBiteSuccessBranch`'s call-mapping prefix: given the EVM-side `ilks`+`urns`
STATICCALLs (in the exact `{ initState σ_evm … with … }` shapes the reach wrappers produce), map both
to the σ_solm side (`catBiteMapIlksCall`/`catBiteMapCall`), reshaping the targets to the
`EVM.address (biteVatAddr …)` forms the `catBiteSource*Revert` lemmas expect, and expose the
`EVMStateEquiv` coupling on the `urns` state so each divergence branch can transfer its state-dependent
side-conditions.  Every post-`urns` divergence leaf (guard-fails + grab/fess/kick call-fails) shares
this prefix. -/

/-- `catSlotWord` transports across `EVMStateEquiv` (same codeOwner storage view). -/
theorem biteSlotEqOfEquiv {a b : EVM.State} (h : EVMStateEquiv a b) (s : UInt256) :
    catSlotWord s a.accountMap a.executionEnv = catSlotWord s b.accountMap b.executionEnv := by
  simp only [catSlotWord, solcSlotWord]
  rw [h.executionEnv]
  exact accountMapEquiv_storage_findD h.accountMap b.executionEnv.codeOwner s ⟨0⟩

theorem biteBoxW_eq_of_equiv {a b : EVM.State} (h : EVMStateEquiv a b) :
    biteBoxW a = biteBoxW b := by simp only [biteBoxW, biteSlotEqOfEquiv h]

theorem biteLitW_eq_of_equiv {a b : EVM.State} (h : EVMStateEquiv a b) :
    biteLitW a = biteLitW b := by simp only [biteLitW, biteSlotEqOfEquiv h]

theorem biteChopW_eq_of_equiv {I} {a b : EVM.State} (h : EVMStateEquiv a b) :
    biteChopW I a = biteChopW I b := by simp only [biteChopW, biteSlotEqOfEquiv h]

theorem biteRoomV_eq_of_equiv {a b : EVM.State} (h : EVMStateEquiv a b) :
    biteRoomV a = biteRoomV b := by
  simp only [biteRoomV, biteBoxW, biteLitW, biteSlotEqOfEquiv h]

theorem biteDunkRoomV_eq_of_equiv {I} {a b : EVM.State} (h : EVMStateEquiv a b) :
    biteDunkRoomV I a = biteDunkRoomV I b := by
  simp only [biteDunkRoomV, biteDunkW, biteRoomV, biteBoxW, biteLitW, biteSlotEqOfEquiv h]

theorem biteDartV_eq_of_equiv {I} {a b : EVM.State} (h : EVMStateEquiv a b) (r art : UInt256) :
    biteDartV I a r art = biteDartV I b r art := by
  simp only [biteDartV, biteDartCandV, biteDartDenomV, biteDunkRoomWadV, biteDunkRoomV, biteDunkW,
    biteRoomV, biteBoxW, biteLitW, biteChopW, biteSlotEqOfEquiv h]

theorem biteDinkV_eq_of_equiv {I} {a b : EVM.State} (h : EVMStateEquiv a b) (r art ink : UInt256) :
    biteDinkV I a r art ink = biteDinkV I b r art ink := by
  simp only [biteDinkV, biteDinkCandV, biteInkDartV, biteDartV, biteDartCandV, biteDartDenomV,
    biteDunkRoomWadV, biteDunkRoomV, biteDunkW, biteRoomV, biteBoxW, biteLitW, biteChopW,
    biteSlotEqOfEquiv h]

theorem biteDartRateV_eq_of_equiv {I} {a b : EVM.State} (h : EVMStateEquiv a b) (r art : UInt256) :
    biteDartRateV I a r art = biteDartRateV I b r art := by
  simp only [biteDartRateV, biteDartV, biteDartCandV, biteDartDenomV, biteDunkRoomWadV,
    biteDunkRoomV, biteDunkW, biteRoomV, biteBoxW, biteLitW, biteChopW, biteSlotEqOfEquiv h]

theorem biteTabV_eq_of_equiv {I} {a b : EVM.State} (h : EVMStateEquiv a b) (r art : UInt256) :
    biteTabV I a r art = biteTabV I b r art := by
  simp only [biteTabV, biteTabBaseV, biteDartRateV, biteDartV, biteDartCandV, biteDartDenomV,
    biteDunkRoomWadV, biteDunkRoomV, biteDunkW, biteRoomV, biteBoxW, biteLitW, biteChopW,
    biteSlotEqOfEquiv h]

theorem biteLitterNewV_eq_of_equiv {I} {au bu af bf : EVM.State}
    (hu : EVMStateEquiv au bu) (hf : EVMStateEquiv af bf) (r art : UInt256) :
    biteLitterNewV I au af r art = biteLitterNewV I bu bf r art := by
  simp only [biteLitterNewV, biteLitW, biteTabV, biteTabBaseV, biteDartRateV, biteDartV,
    biteDartCandV, biteDartDenomV, biteDunkRoomWadV, biteDunkRoomV, biteDunkW, biteRoomV, biteBoxW,
    biteChopW, biteSlotEqOfEquiv hu, biteSlotEqOfEquiv hf]

theorem biteVatAddr_eq_of_equiv {a b : EVM.State} (h : EVMStateEquiv a b) :
    biteVatAddr a = biteVatAddr b := by simp only [biteVatAddr, biteSlotEqOfEquiv h]

theorem biteVowAddrV_eq_of_equiv {a b : EVM.State} (h : EVMStateEquiv a b) :
    biteVowAddrV a = biteVowAddrV b := by simp only [biteVowAddrV, biteSlotEqOfEquiv h]

theorem biteFlipAddrV_eq_of_equiv {I} {a b : EVM.State} (h : EVMStateEquiv a b) :
    biteFlipAddrV I a = biteFlipAddrV I b := by simp only [biteFlipAddrV, biteSlotEqOfEquiv h]

/-- Code size at an address transports across `EVMStateEquiv` (`accountMapEquiv` preserves code). -/
theorem biteCodeW_eq_of_equiv {a b : EVM.State} (addr : AccountAddress) (h : EVMStateEquiv a b) :
    UInt256.ofNat ((a.lookupAccount addr).option 0 (fun acc => acc.code.size)) =
      UInt256.ofNat ((b.lookupAccount addr).option 0 (fun acc => acc.code.size)) := by
  have hw := accountMapEquiv_code_size_word h.accountMap addr
  simp only [State.lookupAccount]
  cases ha : a.accountMap.find? addr <;> cases hb : b.accountMap.find? addr <;>
    rw [ha, hb] at hw <;> simpa [Option.option, EVM.Word.ofNat] using hw

/-- **Map the `ilks`+`urns` STATICCALLs to the σ_solm side.**  Takes the EVM-side calls in the walk's
shapes (both `false`-perm STATICCALLs), returns the two σ_solm calls in the `EVM.address (biteVatAddr …)`
target form the source-revert lemmas expect, plus the `EVMStateEquiv` coupling of the two `urns`
states (for transferring the arithmetic side-conditions) and the σ_solm-side ilks vat-code guard. -/
theorem catBiteMapUrns {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {σ' σu : AccountMap} {A' Au : Substate}
    {cA' cAu : Batteries.RBSet AccountAddress compare} {o' ou : ByteArray}
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hdepthNe : I.depth ≠ 1024)
    (hUrnsVatCode :
      ¬ Reasoning.Theory.extCodeSizeWord σ' ((catSlotWord ⟨3⟩ σ' I).land biteAddrMaskWord) = ⟨0⟩)
    (hIlksCall :
      typedCallViaEVM config (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        (AccountAddress.ofUInt256 (catBiteVatTargetWord σ_evm I)) "ilks" 0 [biteIlkVal I]
        (true, { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
                  accountMap := σ', substate := A', createdAccounts := cA' }, o') false)
    (hUrnsCall :
      typedCallViaEVM config
        { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
            accountMap := σ', createdAccounts := cA' }
        (AccountAddress.ofUInt256 ((catSlotWord ⟨3⟩ σ' I).land biteAddrMaskWord)) "urns" 0
        [biteIlkVal I, biteUrnVal I]
        (true, { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
                  accountMap := σu, substate := Au, createdAccounts := cAu }, ou) false) :
    ∃ (σs : AccountMap) (As : Substate) (σus : AccountMap) (Aus : Substate),
      typedCallViaEVM config (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (biteVatAddr (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I))) "ilks" 0
        [biteIlkVal I]
        (true, { initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I with
                  accountMap := σs, substate := As, createdAccounts := cA' }, o') false ∧
      typedCallViaEVM config
        { initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I with
            accountMap := σs, substate := As, createdAccounts := cA' }
        (EVM.address (biteVatAddr
          { initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I with
              accountMap := σs, substate := As, createdAccounts := cA' })) "urns" 0
        [biteIlkVal I, biteUrnVal I]
        (true, { initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I with
                  accountMap := σus, substate := Aus, createdAccounts := cAu }, ou) false ∧
      accountMapEquiv σu σus ∧
      0 < (UInt256.ofNat
        ((({ initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I with
              accountMap := σs, substate := As, createdAccounts := cA' } : EVM.State).lookupAccount
          (biteVatAddr { initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I with
              accountMap := σs, substate := As, createdAccounts := cA' })).option 0
          (fun acc => acc.code.size))).toNat := by
  have hmask : biteAddrMaskWord = solcAddrMask := by native_decide
  have hposNe : ∀ w : UInt256, w ≠ ⟨0⟩ → 0 < w.toNat :=
    fun w hw => Nat.pos_of_ne_zero (fun h => hw (uint256_toNat_eq_zero h))
  have addrId : ∀ a : AccountAddress, EVM.address a.val = a := by
    intro a; apply Fin.ext
    show a.val % EVM.addressModulus = a.val
    rw [show EVM.addressModulus = AccountAddress.size from by decide]
    exact Nat.mod_eq_of_lt a.isLt
  have codePos : ∀ (e : EVM.State) (w : UInt256),
      extCodeSizeWord e.accountMap w ≠ ⟨0⟩ →
      0 < (UInt256.ofNat ((e.lookupAccount
        (AccountAddress.ofUInt256 w)).option 0 (fun acc => acc.code.size))).toNat := by
    intro e w hw
    unfold extCodeSizeWord at hw
    simp only [State.lookupAccount]
    cases hf : e.accountMap.find? (AccountAddress.ofUInt256 w) with
    | none => rw [hf] at hw; simp [Option.option] at hw
    | some acc =>
        rw [hf] at hw
        simp only [Option.option, Function.comp] at hw ⊢
        exact hposNe _ hw
  obtain ⟨σs, As, hIlksSolm, hEqIlk⟩ := catBiteMapIlksCall hAccounts hIlksCall
  have htw : catBiteVatTargetWord σ_evm I = catBiteVatTargetWord σ_solm I := by
    simp only [catBiteVatTargetWord, catAddressReturnWord, catSlotWord, solcSlotWord]
    rw [accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨3⟩ ⟨0⟩]
  have htgt : (AccountAddress.ofUInt256 (catBiteVatTargetWord σ_evm I))
      = EVM.address (biteVatAddr (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)) := by
    rw [htw]; exact catBiteVatEvmAddr_eq_target.symm
  rw [htgt] at hIlksSolm
  obtain ⟨AU, hUrnsCall'⟩ :=
    biteTypedCallZeroSetSubstate hUrnsCall (by simpa [initState] using hdepthNe) A'
  obtain ⟨σus, Aus, hUrnsSolm, hEqUrn⟩ := catBiteMapCall hEqIlk hUrnsCall' hdepthNe
  have hslot3 : catSlotWord ⟨3⟩ σ' I = catSlotWord ⟨3⟩ σs I := by
    simp only [catSlotWord, solcSlotWord]
    rw [accountMapEquiv_storage_findD hEqIlk.accountMap I.codeOwner ⟨3⟩ ⟨0⟩]
  set eI := { initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I with
    accountMap := σs, substate := As, createdAccounts := cA' } with heIdef
  have heIam : eI.accountMap = σs := rfl
  have heIee : eI.executionEnv = I := rfl
  have haddr : EVM.address (biteVatAddr eI).val
      = AccountAddress.ofUInt256 ((catSlotWord ⟨3⟩ σs I).land biteAddrMaskWord) := by
    rw [addrId, accountAddress_ofUInt256_eq_ofNat_toNat]
    simp only [biteVatAddr, catSlotWord, heIam, heIee, hmask]
  rw [hslot3, ← haddr] at hUrnsSolm
  have hvatCodeIlk : 0 < (UInt256.ofNat
      ((eI.lookupAccount (biteVatAddr eI)).option 0 (fun acc => acc.code.size))).toNat := by
    have hva : biteVatAddr eI = AccountAddress.ofUInt256 (catBiteVatTargetWord σs I) := by
      rw [accountAddress_ofUInt256_eq_ofNat_toNat]
      simp only [biteVatAddr, catBiteVatTargetWord, catAddressReturnWord, catSlotWord, heIam, heIee]
    rw [hva]
    refine codePos eI (catBiteVatTargetWord σs I) ?_
    rw [heIam, show catBiteVatTargetWord σs I = (catSlotWord ⟨3⟩ σs I).land biteAddrMaskWord from by
        simp only [catBiteVatTargetWord, catAddressReturnWord, hmask],
      ← hslot3, ← extCodeSizeWord_accountMapEquiv hEqIlk.accountMap]
    exact hUrnsVatCode
  exact ⟨σs, As, σus, Aus, hIlksSolm, hUrnsSolm, hEqUrn.accountMap, hvatCodeIlk⟩


set_option maxHeartbeats 2000000 in
/-- **grab-fail branch (extracted).** The `grab` CALL returns `success = 0`; maps ilks+urns to σ_solm
(`catBiteMapUrns`), maps the failed grab, transfers the arith conditions, and fires
`catBiteGrabFailLeaf` + `catBiteSourceGrabFailRevert`. Lifted out of `catBiteBodyImpl` (own heartbeat
budget). -/
theorem catBiteRevertGrabFail {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {σ' σu σg : AccountMap} {A' Au Ag : Substate}
    {cA' cAu cAg : Batteries.RBSet AccountAddress compare} {o' ou og : ByteArray}
    {mem : ByteArray} {aw : UInt256} {R : List UInt256} {k C : ℕ}
    {art ink iSpot iRate iDust room milkDunk milkChop dunkRoom dunkRoomWad
      dartDenomRate dartCandidate dart inkDart dinkCandidate dink : UInt256}
    (hcode : I.code = catBytecode)
    (hdispatch : dispatchMsg contract I.calldata = some biteTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (biteTransition.params.map Param.name)
        (transitionSignature biteTransition).paramTypes I.calldata = some (biteLocals I))
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hwv : I.weiValue = ⟨0⟩) (hperm : I.perm = true) (hsz36 : 36 ≤ I.calldata.size)
    (hdepth : (I.depth : ℕ) < 1024)
    (hurn : biteAddrMaskWord.land (biteAddrMaskWord.land (calldataWord I.calldata 36)) = biteUrnWord I)
    (hilkslen : 160 ≤ o'.size) (hurnslen : 64 ≤ ou.size)
    (hlive : catSlotWord ⟨2⟩ σu I = ⟨1⟩)
    (hvatCode : ¬ Reasoning.Theory.extCodeSizeWord σ_evm (catBiteVatTargetWord σ_evm I) = ⟨0⟩)
    (hUrnsVatCode :
      ¬ Reasoning.Theory.extCodeSizeWord σ' ((catSlotWord ⟨3⟩ σ' I).land biteAddrMaskWord) = ⟨0⟩)
    (hGrabCode :
      ¬ Reasoning.Theory.extCodeSizeWord σu ((solcSlotWord σu I ⟨3⟩).land biteAddrMaskWord) = ⟨0⟩)
    (hIlksCall :
      typedCallViaEVM config (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        (AccountAddress.ofUInt256 (catBiteVatTargetWord σ_evm I)) "ilks" 0 [biteIlkVal I]
        (true, { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
                  accountMap := σ', substate := A', createdAccounts := cA' }, o') false)
    (hUrnsCall :
      typedCallViaEVM config
        { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
            accountMap := σ', createdAccounts := cA' }
        (AccountAddress.ofUInt256 ((catSlotWord ⟨3⟩ σ' I).land biteAddrMaskWord)) "urns" 0
        [biteIlkVal I, biteUrnVal I]
        (true, { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
                  accountMap := σu, substate := Au, createdAccounts := cAu }, ou) false)
    (hGrabCall :
      typedCallViaEVM config
        { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
            accountMap := σu, createdAccounts := cAu }
        (AccountAddress.ofUInt256 ((solcSlotWord σu I ⟨3⟩).land biteAddrMaskWord)) "grab" 0
        [Value.fixedBytes bytes32Width (EVM.Word.toBytesBE (biteIlkWord I)),
          Value.address (AccountAddress.ofNat
            (biteAddrMaskWord.land (biteAddrMaskWord.land (calldataWord I.calldata 36))).toNat),
          Value.address (AccountAddress.ofNat (UInt256.ofNat I.codeOwner.val).toNat),
          Value.address (AccountAddress.ofNat (biteAddrMaskWord.land (solcSlotWord σu I ⟨4⟩)).toNat),
          Value.int (-Int.ofNat dink.toNat), Value.int (-Int.ofNat dart.toNat)]
        (false, { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
                  accountMap := σg, substate := Ag, createdAccounts := cAg }, og) I.perm)
    (rd2193 :
      RD catBytecode I (Sat256.ofUInt256 g) (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        ⟨2193⟩ (⟨0⟩ :: R) mem aw og (cAg, σg) k C)
    (hoszg : og.size < UInt256.size) (hov : R.length + 5 ≤ 1024)
    (hart : art = UInt256.ofNat (fromByteArrayBigEndian (ou.extract 32 64)))
    (hink : ink = UInt256.ofNat (fromByteArrayBigEndian (ou.extract 0 32)))
    (hiSpot : iSpot = UInt256.ofNat (fromByteArrayBigEndian (o'.extract 64 96)))
    (hiRate : iRate = UInt256.ofNat (fromByteArrayBigEndian (o'.extract 32 64)))
    (hiDustDef : iDust = UInt256.ofNat (fromByteArrayBigEndian (o'.extract 128 160)))
    (hroomDef : room = (solcSlotWord σu I ⟨5⟩).sub (solcSlotWord σu I ⟨6⟩))
    (hmilkDunkDef : milkDunk = solcSlotWord σu I (solcMappingSlot ⟨1⟩ (biteIlkWord I) + ⟨2⟩))
    (hmilkChopDef : milkChop = solcSlotWord σu I (solcMappingSlot ⟨1⟩ (biteIlkWord I) + ⟨1⟩))
    (hdunkRoomDef : dunkRoom = if milkDunk.gt room = ⟨0⟩ then milkDunk else room)
    (hdunkRoomWadDef : dunkRoomWad = dunkRoom.mul ⟨1000000000000000000⟩)
    (hdartDenomDef : dartDenomRate = dunkRoomWad.div iRate)
    (hdartCandDef : dartCandidate = dartDenomRate.div milkChop)
    (hdartDef : dart = if art.gt dartCandidate = ⟨0⟩ then art else dartCandidate)
    (hinkDartDef : inkDart = ink.mul dart)
    (hdinkCandDef : dinkCandidate = inkDart.div art)
    (hdinkDef : dink = if ink.gt dinkCandidate = ⟨0⟩ then ink else dinkCandidate)
    (hspotPos : 0 < iSpot.toNat) (hfitArtRate : art.toNat * iRate.toNat < UInt256.size)
    (hfitInkSpot : ink.toNat * iSpot.toNat < UInt256.size)
    (hunsafe : (ink * iSpot).toNat < (art * iRate).toNat)
    (hlitterbox : (solcSlotWord σu I ⟨6⟩).toNat < (solcSlotWord σu I ⟨5⟩).toNat)
    (hroomdust : iDust.toNat ≤ room.toNat)
    (hRatePos : iRate ≠ ⟨0⟩) (hChopPos : milkChop ≠ ⟨0⟩)
    (hFitWad : (⟨1000000000000000000⟩ : UInt256).toNat * dunkRoom.toNat < UInt256.size)
    (hArtPos : art ≠ ⟨0⟩) (hFitInkDart : dart.toNat * ink.toNat < UInt256.size)
    (hDartPos : 0 < dart.toNat) (hDinkPos : 0 < dink.toNat)
    (hDartLim : dart.toNat ≤ (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨255⟩).toNat)
    (hDinkLim : dink.toNat ≤ (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨255⟩).toNat) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hdepthNe : I.depth ≠ 1024 := by omega
  have hmask : biteAddrMaskWord = solcAddrMask := by native_decide
  have hposNe : ∀ w : UInt256, w ≠ ⟨0⟩ → 0 < w.toNat :=
    fun w hw => Nat.pos_of_ne_zero (fun h => hw (uint256_toNat_eq_zero h))
  have addrId : ∀ a : AccountAddress, EVM.address a.val = a := by
    intro a; apply Fin.ext
    show a.val % EVM.addressModulus = a.val
    rw [show EVM.addressModulus = AccountAddress.size from by decide]
    exact Nat.mod_eq_of_lt a.isLt
  have codePos : ∀ (e : EVM.State) (w : UInt256),
      extCodeSizeWord e.accountMap w ≠ ⟨0⟩ →
      0 < (UInt256.ofNat ((e.lookupAccount
        (AccountAddress.ofUInt256 w)).option 0
        (fun acc => acc.code.size))).toNat := by
    intro e w hw
    unfold extCodeSizeWord at hw
    simp only [State.lookupAccount]
    cases hf : e.accountMap.find? (AccountAddress.ofUInt256 w) with
    | none => rw [hf] at hw; simp [Option.option] at hw
    | some acc =>
        rw [hf] at hw
        simp only [Option.option, Function.comp] at hw ⊢
        exact hposNe _ hw
  have hAddrRT : ∀ a : AccountAddress,
      AccountAddress.ofNat (UInt256.ofNat a.val).toNat = a := by
    intro a
    have h1 : (UInt256.ofNat a.val).toNat = a.val :=
      UInt256.toNat_ofNat_of_lt (lt_of_lt_of_le a.isLt
        (show AccountAddress.size ≤ UInt256.size from by decide))
    rw [h1]; apply Fin.ext
    simp only [AccountAddress.ofNat, Fin.ofNat]
    exact Nat.mod_eq_of_lt a.isLt
  have hbytes : biteIlkBytes I = EVM.Word.toBytesBE (biteIlkWord I) := by
    have hlen32 : (biteIlkBytes I).length = 32 := by
      simp only [biteIlkBytes, List.length_take, List.length_drop]
      have htlen : I.calldata.toList.length = I.calldata.size := by
        rw [byteArray_toList_eq, Array.length_toList]; rfl
      rw [htlen]; omega
    have hword : ABI.bytesToWord (biteIlkBytes I) = biteIlkWord I := by
      simpa [biteIlkBytes, biteIlkWord] using
        (decode_word_at_eq_any I.calldata 4 (by simpa using hsz36))
    have hto := toBytesBE_bytesToWord_of_length (bs := biteIlkBytes I) hlen32
    rw [hword] at hto; exact hto.symm
  have uminEq : ∀ a b : UInt256,
      (if UInt256.gt a b = ⟨0⟩ then a else b) = umin a b := by
    intro a b; unfold umin
    by_cases h : a.toNat ≤ b.toNat
    · rw [if_pos (ugt_zero h), if_pos h]
    · rw [if_neg (by rw [ugt_one (by omega)]; decide), if_neg h]
  have hwad : wadU = ⟨1000000000000000000⟩ := by native_decide
  have hsl : (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨255⟩).toNat =
      57896044618658097711785492504343953926634992332820282019728792003956564819968 := by
    native_decide
  have hbr : ∀ (o : ByteArray) (k : ℕ), k + 32 ≤ o.size →
      ABI.bytesToWord ((o.toList.drop k).take 32) =
        UInt256.ofNat (fromByteArrayBigEndian (o.extract k (k + 32))) := by
    intro o k h
    rw [decode_word_at_eq_any o k h, uInt256OfByteArray_eq]
    congr 1; unfold fromByteArrayBigEndian; congr 1
    rw [byteArray_toList_eq (o.readBytes k 32),
      readBytes_at_toList_any o k h,
      byteArray_toList_eq (o.extract k (k + 32)),
      ByteArray.data_extract, Array.toList_extract,
      List.extract_eq_take_drop]
    simp
  obtain ⟨σs, As, σus, Aus, hIlksSolm, hUrnsSolm, hAmEq, hvatCodeIlkS⟩ :=
    catBiteMapUrns hAccounts hdepthNe hUrnsVatCode hIlksCall hUrnsCall
  have slotEqUS : ∀ s : UInt256, solcSlotWord σus I s = solcSlotWord σu I s := by
    intro s; simp only [solcSlotWord]
    rw [accountMapEquiv_storage_findD hAmEq I.codeOwner s ⟨0⟩]
  set eUrnE := { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
    accountMap := σu, substate := Au, createdAccounts := cAu } with heUrnEdef
  set eUrnS := { initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I with
    accountMap := σus, substate := Aus, createdAccounts := cAu } with heUrnSdef
  have hEqU : EVMStateEquiv eUrnE eUrnS := ⟨rfl, rfl, hAmEq⟩
  have heUEam : eUrnE.accountMap = σu := rfl
  have heUEee : eUrnE.executionEnv = I := rfl
  have heUSam : eUrnS.accountMap = σus := rfl
  have heUSee : eUrnS.executionEnv = I := rfl
  -- eUrnE-side named quantities (identical to the walk's `set` values).
  have hboxB : biteBoxW eUrnE = solcSlotWord σu I ⟨5⟩ := by
    simp only [biteBoxW, catSlotWord, heUEam, heUEee]
  have hlitB : biteLitW eUrnE = solcSlotWord σu I ⟨6⟩ := by
    simp only [biteLitW, catSlotWord, heUEam, heUEee]
  have hchopB : biteChopW I eUrnE = milkChop := by
    rw [hmilkChopDef]
    simp only [biteChopW, catSlotWord, heUEam, heUEee, biteChopSlot,
      biteFlipSlot_eq hsz36]
  have hdunkB : biteDunkW I eUrnE = milkDunk := by
    rw [hmilkDunkDef]
    simp only [biteDunkW, catSlotWord, heUEam, heUEee, biteDunkSlot,
      biteFlipSlot_eq hsz36]
  have hroomB : biteRoomV eUrnE = room := by
    rw [hroomDef]
    simp only [biteRoomV, biteBoxW, biteLitW, catSlotWord, heUEam, heUEee]
  have hdunkroomB : biteDunkRoomV I eUrnE = dunkRoom := by
    rw [hdunkRoomDef, uminEq milkDunk room]
    simp only [biteDunkRoomV, hdunkB, hroomB]
  have hdartvB : biteDartV I eUrnE iRate art = dart := by
    have hcand : biteDartCandV I eUrnE iRate = dartCandidate := by
      simp only [biteDartCandV, biteDartDenomV, biteDunkRoomWadV,
        hchopB, hdunkroomB, hwad, hdartCandDef, hdartDenomDef,
        hdunkRoomWadDef]
      rfl
    rw [hdartDef, uminEq art dartCandidate]
    simp only [biteDartV, hcand]
  have hdinkvB : biteDinkV I eUrnE iRate art ink = dink := by
    have hcand : biteDinkCandV I eUrnE iRate art ink = dinkCandidate := by
      simp only [biteDinkCandV, biteInkDartV, hdartvB, hdinkCandDef,
        hinkDartDef]
      rfl
    rw [hdinkDef, uminEq ink dinkCandidate]
    simp only [biteDinkV, hcand]
  -- ilks / urns decode on the σ_solm side (same output bytes).
  have hIlksDec : config.externalABI.decode? "ilks" o' =
      some [bw (UInt256.ofNat (fromByteArrayBigEndian (o'.extract 0 32))),
        bw iRate, bw iSpot,
        bw (UInt256.ofNat (fromByteArrayBigEndian (o'.extract 96 128))),
        bw iDust] := by
    have h := catBiteIlksDecode_ok hilkslen
    rw [hbr o' 0 (by omega), hbr o' 32 (by omega), hbr o' 64 (by omega),
      hbr o' 96 (by omega), hbr o' 128 (by omega)] at h
    rw [hiRate, hiSpot, hiDustDef]; exact h
  have hUrnsDec : config.externalABI.decode? "urns" ou =
      some [bw ink, bw art] := by
    have h := catBiteUrnsDecode_ok hurnslen
    rw [hbr ou 0 (by omega), hbr ou 32 (by omega)] at h
    rw [hink, hart]; exact h
  -- map the (failed) grab CALL to σ_solm.
  obtain ⟨AG, hGrabCall'⟩ :=
    biteTypedCallZeroSetSubstate hGrabCall
      (by simpa [initState] using hdepthNe) Au
  obtain ⟨σgs, Ags, hGrabSolm, _hEqGrab⟩ :=
    catBiteMapCall hEqU hGrabCall' hdepthNe
  -- reshape target + args of the mapped grab call to source-revert form.
  have htgtU : EVM.address (biteVatAddr eUrnS).val =
      AccountAddress.ofUInt256 ((solcSlotWord σu I ⟨3⟩).land biteAddrMaskWord) := by
    rw [← biteVatAddr_eq_of_equiv hEqU, addrId,
      accountAddress_ofUInt256_eq_ofNat_toNat, hmask]
    simp only [biteVatAddr, catSlotWord, heUEam, heUEee]
  have h1 : biteIlkVal I =
      Value.fixedBytes bytes32Width (EVM.Word.toBytesBE (biteIlkWord I)) := by
    simp only [biteIlkVal, hbytes]
  have h2 : biteUrnVal I = Value.address (AccountAddress.ofNat
      (biteAddrMaskWord.land
        (biteAddrMaskWord.land (calldataWord I.calldata 36))).toNat) := by
    rw [hurn]
    simp only [biteUrnVal, biteUrnWord, biteUrnAddr, hAddrRT]
  have h3 : (eUrnS.executionEnv.codeOwner : AccountAddress) =
      AccountAddress.ofNat (UInt256.ofNat I.codeOwner.val).toNat := by
    rw [heUSee]; exact (hAddrRT I.codeOwner).symm
  have h4 : biteVowAddrV eUrnS = AccountAddress.ofNat
      (biteAddrMaskWord.land (solcSlotWord σu I ⟨4⟩)).toNat := by
    rw [← biteVowAddrV_eq_of_equiv hEqU]
    simp only [biteVowAddrV, catSlotWord, heUEam, heUEee, hmask]
    rw [u256_land_comm]
  have hdartvBS : biteDartV I eUrnS iRate art = dart := by
    rw [← biteDartV_eq_of_equiv hEqU]; exact hdartvB
  have hdinkvBS : biteDinkV I eUrnS iRate art ink = dink := by
    rw [← biteDinkV_eq_of_equiv hEqU]; exact hdinkvB
  have hGrabCodeS :
      ¬ Reasoning.Theory.extCodeSizeWord σus
        ((solcSlotWord σus I ⟨3⟩).land biteAddrMaskWord) = ⟨0⟩ := by
    rw [slotEqUS ⟨3⟩, ← extCodeSizeWord_accountMapEquiv hAmEq]
    exact hGrabCode
  -- reshape the mapped grab call to the source-revert form.
  rw [hperm, ← htgtU, ← h1, ← h2, ← h3, ← h4, ← hdinkvBS, ← hdartvBS]
    at hGrabSolm
  -- feed the leaf + source-revert.
  have hlive' : catSlotWord ⟨2⟩ eUrnS.accountMap eUrnS.executionEnv = ⟨1⟩ := by
    rw [← biteSlotEqOfEquiv hEqU ⟨2⟩]; exact hlive
  refine catBiteGrabFailLeaf hcode hdispatch hdecode rd2193 hoszg hov ?_
  refine catBiteSourceGrabFailRevert hwv
    (catBiteVatCodePos_of_uniswap hAccounts hvatCode) hIlksSolm hIlksDec
    hvatCodeIlkS hUrnsSolm hUrnsDec hlive' hsz36 hfitInkSpot hfitArtRate
    hspotPos (hposNe iRate hRatePos) hunsafe ?_ ?_ ?_ ?_ ?_
    (hposNe art hArtPos) ?_ ?_ ?_ ?_ ?_ hGrabSolm
  · -- hlitLtBox
    rw [← biteLitW_eq_of_equiv hEqU, ← biteBoxW_eq_of_equiv hEqU, hlitB, hboxB]
    exact hlitterbox
  · -- hroomGeDust
    rw [← biteRoomV_eq_of_equiv hEqU, hroomB]; exact hroomdust
  · -- hfitDunkRoomWad
    rw [← biteDunkRoomV_eq_of_equiv hEqU, hdunkroomB, hwad, Nat.mul_comm]
    exact hFitWad
  · -- hmilkChopPos
    rw [← biteChopW_eq_of_equiv hEqU, hchopB]; exact hposNe milkChop hChopPos
  · -- hfitInkDart
    rw [← biteDartV_eq_of_equiv hEqU, hdartvB, Nat.mul_comm]; exact hFitInkDart
  · -- hdartPos
    rw [← biteDartV_eq_of_equiv hEqU, hdartvB]; exact hDartPos
  · -- hdinkPos
    rw [← biteDinkV_eq_of_equiv hEqU, hdinkvB]; exact hDinkPos
  · -- hdartLim
    rw [← biteDartV_eq_of_equiv hEqU, hdartvB]; simp only [int256Limit]
    exact Int.ofNat_le.mpr (hDartLim.trans_eq hsl)
  · -- hdinkLim
    rw [← biteDinkV_eq_of_equiv hEqU, hdinkvB]; simp only [int256Limit]
    exact Int.ofNat_le.mpr (hDinkLim.trans_eq hsl)
  · -- hvatCodeMid
    have haddr : biteVatAddr eUrnS =
        AccountAddress.ofUInt256 (catBiteVatTargetWord σus I) := by
      rw [accountAddress_ofUInt256_eq_ofNat_toNat]
      simp only [biteVatAddr, catBiteVatTargetWord, catAddressReturnWord,
        catSlotWord, heUSam, heUSee]
    rw [haddr]
    refine codePos eUrnS (catBiteVatTargetWord σus I) ?_
    rw [heUSam, show catBiteVatTargetWord σus I =
          (solcSlotWord σus I ⟨3⟩).land biteAddrMaskWord from by
        simp only [catBiteVatTargetWord, catAddressReturnWord, catSlotWord,
          hmask]]
    exact hGrabCodeS


set_option maxHeartbeats 2000000 in
/-- **fess-fail branch (extracted).** grab succeeds, `fess` CALL returns `success = 0`; maps
ilks+urns+grab, maps the failed fess, fires `catBiteFessFailLeaf` + `catBiteSourceFessFailRevert`. -/
theorem catBiteRevertFessFail {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {σ' σu σg σf : AccountMap} {A' Au Ag Af : Substate}
    {cA' cAu cAg cAf : Batteries.RBSet AccountAddress compare} {o' ou og ofb : ByteArray}
    {mem2 : ByteArray} {aw2 : UInt256} {R2 : List UInt256} {k2 C2 : ℕ} {zf : Bool}
    {art ink iSpot iRate iDust room milkDunk milkChop dunkRoom dunkRoomWad
      dartDenomRate dartCandidate dart inkDart dinkCandidate dink : UInt256}
    (hcode : I.code = catBytecode)
    (hdispatch : dispatchMsg contract I.calldata = some biteTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (biteTransition.params.map Param.name)
        (transitionSignature biteTransition).paramTypes I.calldata = some (biteLocals I))
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hwv : I.weiValue = ⟨0⟩) (hperm : I.perm = true) (hsz36 : 36 ≤ I.calldata.size)
    (hdepth : (I.depth : ℕ) < 1024)
    (hurn : biteAddrMaskWord.land (biteAddrMaskWord.land (calldataWord I.calldata 36)) = biteUrnWord I)
    (hilkslen : 160 ≤ o'.size) (hurnslen : 64 ≤ ou.size)
    (hlive : catSlotWord ⟨2⟩ σu I = ⟨1⟩)
    (hvatCode : ¬ Reasoning.Theory.extCodeSizeWord σ_evm (catBiteVatTargetWord σ_evm I) = ⟨0⟩)
    (hUrnsVatCode :
      ¬ Reasoning.Theory.extCodeSizeWord σ' ((catSlotWord ⟨3⟩ σ' I).land biteAddrMaskWord) = ⟨0⟩)
    (hGrabCode :
      ¬ Reasoning.Theory.extCodeSizeWord σu ((solcSlotWord σu I ⟨3⟩).land biteAddrMaskWord) = ⟨0⟩)
    (hFessCode :
      ¬ Reasoning.Theory.extCodeSizeWord σg (biteAddrMaskWord.land (solcSlotWord σg I ⟨4⟩)) = ⟨0⟩)
    (hIlksCall :
      typedCallViaEVM config (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        (AccountAddress.ofUInt256 (catBiteVatTargetWord σ_evm I)) "ilks" 0 [biteIlkVal I]
        (true, { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
                  accountMap := σ', substate := A', createdAccounts := cA' }, o') false)
    (hUrnsCall :
      typedCallViaEVM config
        { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
            accountMap := σ', createdAccounts := cA' }
        (AccountAddress.ofUInt256 ((catSlotWord ⟨3⟩ σ' I).land biteAddrMaskWord)) "urns" 0
        [biteIlkVal I, biteUrnVal I]
        (true, { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
                  accountMap := σu, substate := Au, createdAccounts := cAu }, ou) false)
    (hGrabCall :
      typedCallViaEVM config
        { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
            accountMap := σu, createdAccounts := cAu }
        (AccountAddress.ofUInt256 ((solcSlotWord σu I ⟨3⟩).land biteAddrMaskWord)) "grab" 0
        [Value.fixedBytes bytes32Width (EVM.Word.toBytesBE (biteIlkWord I)),
          Value.address (AccountAddress.ofNat
            (biteAddrMaskWord.land (biteAddrMaskWord.land (calldataWord I.calldata 36))).toNat),
          Value.address (AccountAddress.ofNat (UInt256.ofNat I.codeOwner.val).toNat),
          Value.address (AccountAddress.ofNat (biteAddrMaskWord.land (solcSlotWord σu I ⟨4⟩)).toNat),
          Value.int (-Int.ofNat dink.toNat), Value.int (-Int.ofNat dart.toNat)]
        (true, { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
                  accountMap := σg, substate := Ag, createdAccounts := cAg }, og) I.perm)
    (hFessCall :
      typedCallViaEVM config
        { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
            accountMap := σg, createdAccounts := cAg }
        (AccountAddress.ofUInt256 (biteAddrMaskWord.land (solcSlotWord σg I ⟨4⟩))) "fess" 0
        [Value.int (Int.ofNat (dart.mul iRate).toNat)]
        (zf, { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
                accountMap := σf, substate := Af, createdAccounts := cAf }, ofb) I.perm)
    (rd2300 :
      RD catBytecode I (Sat256.ofUInt256 g) (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        ⟨2300⟩ (⟨0⟩ :: R2) mem2 aw2 ofb (cAf, σf) k2 C2)
    (hoszf : ofb.size < UInt256.size) (hov2 : R2.length + 5 ≤ 1024) (hzff : zf = false)
    (hRateFit : iRate.toNat * dart.toNat < UInt256.size)
    (hart : art = UInt256.ofNat (fromByteArrayBigEndian (ou.extract 32 64)))
    (hink : ink = UInt256.ofNat (fromByteArrayBigEndian (ou.extract 0 32)))
    (hiSpot : iSpot = UInt256.ofNat (fromByteArrayBigEndian (o'.extract 64 96)))
    (hiRate : iRate = UInt256.ofNat (fromByteArrayBigEndian (o'.extract 32 64)))
    (hiDustDef : iDust = UInt256.ofNat (fromByteArrayBigEndian (o'.extract 128 160)))
    (hroomDef : room = (solcSlotWord σu I ⟨5⟩).sub (solcSlotWord σu I ⟨6⟩))
    (hmilkDunkDef : milkDunk = solcSlotWord σu I (solcMappingSlot ⟨1⟩ (biteIlkWord I) + ⟨2⟩))
    (hmilkChopDef : milkChop = solcSlotWord σu I (solcMappingSlot ⟨1⟩ (biteIlkWord I) + ⟨1⟩))
    (hdunkRoomDef : dunkRoom = if milkDunk.gt room = ⟨0⟩ then milkDunk else room)
    (hdunkRoomWadDef : dunkRoomWad = dunkRoom.mul ⟨1000000000000000000⟩)
    (hdartDenomDef : dartDenomRate = dunkRoomWad.div iRate)
    (hdartCandDef : dartCandidate = dartDenomRate.div milkChop)
    (hdartDef : dart = if art.gt dartCandidate = ⟨0⟩ then art else dartCandidate)
    (hinkDartDef : inkDart = ink.mul dart)
    (hdinkCandDef : dinkCandidate = inkDart.div art)
    (hdinkDef : dink = if ink.gt dinkCandidate = ⟨0⟩ then ink else dinkCandidate)
    (hspotPos : 0 < iSpot.toNat) (hfitArtRate : art.toNat * iRate.toNat < UInt256.size)
    (hfitInkSpot : ink.toNat * iSpot.toNat < UInt256.size)
    (hunsafe : (ink * iSpot).toNat < (art * iRate).toNat)
    (hlitterbox : (solcSlotWord σu I ⟨6⟩).toNat < (solcSlotWord σu I ⟨5⟩).toNat)
    (hroomdust : iDust.toNat ≤ room.toNat)
    (hRatePos : iRate ≠ ⟨0⟩) (hChopPos : milkChop ≠ ⟨0⟩)
    (hFitWad : (⟨1000000000000000000⟩ : UInt256).toNat * dunkRoom.toNat < UInt256.size)
    (hArtPos : art ≠ ⟨0⟩) (hFitInkDart : dart.toNat * ink.toNat < UInt256.size)
    (hDartPos : 0 < dart.toNat) (hDinkPos : 0 < dink.toNat)
    (hDartLim : dart.toNat ≤ (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨255⟩).toNat)
    (hDinkLim : dink.toNat ≤ (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨255⟩).toNat) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hdepthNe : I.depth ≠ 1024 := by omega
  have hmask : biteAddrMaskWord = solcAddrMask := by native_decide
  have hposNe : ∀ w : UInt256, w ≠ ⟨0⟩ → 0 < w.toNat :=
    fun w hw => Nat.pos_of_ne_zero (fun h => hw (uint256_toNat_eq_zero h))
  have codePos : ∀ (e : EVM.State) (w : UInt256),
      extCodeSizeWord e.accountMap w ≠ ⟨0⟩ →
      0 < (UInt256.ofNat ((e.lookupAccount
        (AccountAddress.ofUInt256 w)).option 0
        (fun acc => acc.code.size))).toNat := by
    intro e w hw
    unfold extCodeSizeWord at hw
    simp only [State.lookupAccount]
    cases hf : e.accountMap.find? (AccountAddress.ofUInt256 w) with
    | none => rw [hf] at hw; simp [Option.option] at hw
    | some acc =>
        rw [hf] at hw
        simp only [Option.option, Function.comp] at hw ⊢
        exact hposNe _ hw
  have addrId : ∀ a : AccountAddress, EVM.address a.val = a := by
    intro a; apply Fin.ext
    show a.val % EVM.addressModulus = a.val
    rw [show EVM.addressModulus = AccountAddress.size from by decide]
    exact Nat.mod_eq_of_lt a.isLt
  have hAddrRT : ∀ a : AccountAddress,
      AccountAddress.ofNat (UInt256.ofNat a.val).toNat = a := by
    intro a
    have h1 : (UInt256.ofNat a.val).toNat = a.val :=
      UInt256.toNat_ofNat_of_lt (lt_of_lt_of_le a.isLt
        (show AccountAddress.size ≤ UInt256.size from by decide))
    rw [h1]; apply Fin.ext
    simp only [AccountAddress.ofNat, Fin.ofNat]
    exact Nat.mod_eq_of_lt a.isLt
  have hbytes : biteIlkBytes I = EVM.Word.toBytesBE (biteIlkWord I) := by
    have hlen32 : (biteIlkBytes I).length = 32 := by
      simp only [biteIlkBytes, List.length_take, List.length_drop]
      have htlen : I.calldata.toList.length = I.calldata.size := by
        rw [byteArray_toList_eq, Array.length_toList]; rfl
      rw [htlen]; omega
    have hword : ABI.bytesToWord (biteIlkBytes I) = biteIlkWord I := by
      simpa [biteIlkBytes, biteIlkWord] using
        (decode_word_at_eq_any I.calldata 4 (by simpa using hsz36))
    have hto := toBytesBE_bytesToWord_of_length (bs := biteIlkBytes I) hlen32
    rw [hword] at hto; exact hto.symm
  have uminEq : ∀ a b : UInt256,
      (if UInt256.gt a b = ⟨0⟩ then a else b) = umin a b := by
    intro a b; unfold umin
    by_cases h : a.toNat ≤ b.toNat
    · rw [if_pos (ugt_zero h), if_pos h]
    · rw [if_neg (by rw [ugt_one (by omega)]; decide), if_neg h]
  have hwad : wadU = ⟨1000000000000000000⟩ := by native_decide
  have hsl : (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨255⟩).toNat =
      57896044618658097711785492504343953926634992332820282019728792003956564819968 := by
    native_decide
  have hbr : ∀ (o : ByteArray) (k : ℕ), k + 32 ≤ o.size →
      ABI.bytesToWord ((o.toList.drop k).take 32) =
        UInt256.ofNat (fromByteArrayBigEndian (o.extract k (k + 32))) := by
    intro o k h
    rw [decode_word_at_eq_any o k h, uInt256OfByteArray_eq]
    congr 1; unfold fromByteArrayBigEndian; congr 1
    rw [byteArray_toList_eq (o.readBytes k 32),
      readBytes_at_toList_any o k h,
      byteArray_toList_eq (o.extract k (k + 32)),
      ByteArray.data_extract, Array.toList_extract,
      List.extract_eq_take_drop]
    simp
  obtain ⟨σs, As, σus, Aus, hIlksSolm, hUrnsSolm, hAmEq, hvatCodeIlkS⟩ :=
    catBiteMapUrns hAccounts hdepthNe hUrnsVatCode hIlksCall hUrnsCall
  have slotEqUS : ∀ s : UInt256, solcSlotWord σus I s = solcSlotWord σu I s := by
    intro s; simp only [solcSlotWord]
    rw [accountMapEquiv_storage_findD hAmEq I.codeOwner s ⟨0⟩]
  set eUrnE := { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
    accountMap := σu, substate := Au, createdAccounts := cAu } with heUrnEdef
  set eUrnS := { initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I with
    accountMap := σus, substate := Aus, createdAccounts := cAu } with heUrnSdef
  have hEqU : EVMStateEquiv eUrnE eUrnS := ⟨rfl, rfl, hAmEq⟩
  have heUEam : eUrnE.accountMap = σu := rfl
  have heUEee : eUrnE.executionEnv = I := rfl
  have heUSam : eUrnS.accountMap = σus := rfl
  have heUSee : eUrnS.executionEnv = I := rfl
  have hboxB : biteBoxW eUrnE = solcSlotWord σu I ⟨5⟩ := by
    simp only [biteBoxW, catSlotWord, heUEam, heUEee]
  have hlitB : biteLitW eUrnE = solcSlotWord σu I ⟨6⟩ := by
    simp only [biteLitW, catSlotWord, heUEam, heUEee]
  have hchopB : biteChopW I eUrnE = milkChop := by
    rw [hmilkChopDef]
    simp only [biteChopW, catSlotWord, heUEam, heUEee, biteChopSlot,
      biteFlipSlot_eq hsz36]
  have hdunkB : biteDunkW I eUrnE = milkDunk := by
    rw [hmilkDunkDef]
    simp only [biteDunkW, catSlotWord, heUEam, heUEee, biteDunkSlot,
      biteFlipSlot_eq hsz36]
  have hroomB : biteRoomV eUrnE = room := by
    rw [hroomDef]
    simp only [biteRoomV, biteBoxW, biteLitW, catSlotWord, heUEam, heUEee]
  have hdunkroomB : biteDunkRoomV I eUrnE = dunkRoom := by
    rw [hdunkRoomDef, uminEq milkDunk room]
    simp only [biteDunkRoomV, hdunkB, hroomB]
  have hdartvB : biteDartV I eUrnE iRate art = dart := by
    have hcand : biteDartCandV I eUrnE iRate = dartCandidate := by
      simp only [biteDartCandV, biteDartDenomV, biteDunkRoomWadV,
        hchopB, hdunkroomB, hwad, hdartCandDef, hdartDenomDef,
        hdunkRoomWadDef]
      rfl
    rw [hdartDef, uminEq art dartCandidate]
    simp only [biteDartV, hcand]
  have hdinkvB : biteDinkV I eUrnE iRate art ink = dink := by
    have hcand : biteDinkCandV I eUrnE iRate art ink = dinkCandidate := by
      simp only [biteDinkCandV, biteInkDartV, hdartvB, hdinkCandDef,
        hinkDartDef]
      rfl
    rw [hdinkDef, uminEq ink dinkCandidate]
    simp only [biteDinkV, hcand]
  have hIlksDec : config.externalABI.decode? "ilks" o' =
      some [bw (UInt256.ofNat (fromByteArrayBigEndian (o'.extract 0 32))),
        bw iRate, bw iSpot,
        bw (UInt256.ofNat (fromByteArrayBigEndian (o'.extract 96 128))),
        bw iDust] := by
    have h := catBiteIlksDecode_ok hilkslen
    rw [hbr o' 0 (by omega), hbr o' 32 (by omega), hbr o' 64 (by omega),
      hbr o' 96 (by omega), hbr o' 128 (by omega)] at h
    rw [hiRate, hiSpot, hiDustDef]; exact h
  have hUrnsDec : config.externalABI.decode? "urns" ou =
      some [bw ink, bw art] := by
    have h := catBiteUrnsDecode_ok hurnslen
    rw [hbr ou 0 (by omega), hbr ou 32 (by omega)] at h
    rw [hink, hart]; exact h
  -- map the (successful) grab CALL, keeping the coupling.
  obtain ⟨AG, hGrabCall'⟩ :=
    biteTypedCallZeroSetSubstate hGrabCall
      (by simpa [initState] using hdepthNe) Au
  obtain ⟨σgs, Ags, hGrabSolm, hEqGrab⟩ :=
    catBiteMapCall hEqU hGrabCall' hdepthNe
  set eGrabE := { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
    accountMap := σg, substate := AG, createdAccounts := cAg } with heGrabEdef
  set eGrabS := { initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I with
    accountMap := σgs, substate := Ags, createdAccounts := cAg } with heGrabSdef
  have heGEam : eGrabE.accountMap = σg := rfl
  have heGEee : eGrabE.executionEnv = I := rfl
  have htgtU : EVM.address (biteVatAddr eUrnS).val =
      AccountAddress.ofUInt256 ((solcSlotWord σu I ⟨3⟩).land biteAddrMaskWord) := by
    rw [← biteVatAddr_eq_of_equiv hEqU, addrId,
      accountAddress_ofUInt256_eq_ofNat_toNat, hmask]
    simp only [biteVatAddr, catSlotWord, heUEam, heUEee]
  have h1 : biteIlkVal I =
      Value.fixedBytes bytes32Width (EVM.Word.toBytesBE (biteIlkWord I)) := by
    simp only [biteIlkVal, hbytes]
  have h2 : biteUrnVal I = Value.address (AccountAddress.ofNat
      (biteAddrMaskWord.land
        (biteAddrMaskWord.land (calldataWord I.calldata 36))).toNat) := by
    rw [hurn]
    simp only [biteUrnVal, biteUrnWord, biteUrnAddr, hAddrRT]
  have h3 : (eUrnS.executionEnv.codeOwner : AccountAddress) =
      AccountAddress.ofNat (UInt256.ofNat I.codeOwner.val).toNat := by
    rw [heUSee]; exact (hAddrRT I.codeOwner).symm
  have h4 : biteVowAddrV eUrnS = AccountAddress.ofNat
      (biteAddrMaskWord.land (solcSlotWord σu I ⟨4⟩)).toNat := by
    rw [← biteVowAddrV_eq_of_equiv hEqU]
    simp only [biteVowAddrV, catSlotWord, heUEam, heUEee, hmask]
    rw [u256_land_comm]
  have hdartvBS : biteDartV I eUrnS iRate art = dart := by
    rw [← biteDartV_eq_of_equiv hEqU]; exact hdartvB
  have hdinkvBS : biteDinkV I eUrnS iRate art ink = dink := by
    rw [← biteDinkV_eq_of_equiv hEqU]; exact hdinkvB
  have hdartrateBS : biteDartRateV I eUrnS iRate art = dart.mul iRate := by
    rw [← biteDartRateV_eq_of_equiv hEqU]
    simp only [biteDartRateV, hdartvB]; rfl
  have hGrabCodeS :
      ¬ Reasoning.Theory.extCodeSizeWord σus
        ((solcSlotWord σus I ⟨3⟩).land biteAddrMaskWord) = ⟨0⟩ := by
    rw [slotEqUS ⟨3⟩, ← extCodeSizeWord_accountMapEquiv hAmEq]
    exact hGrabCode
  rw [hperm, ← htgtU, ← h1, ← h2, ← h3, ← h4, ← hdinkvBS, ← hdartvBS]
    at hGrabSolm
  have hGrabDec : config.externalABI.decode? "grab" og = some [] := by
    simp [config, externalABI, decodeVoid?]
  -- map the (failed) fess CALL from the grab-output coupling.
  obtain ⟨AF, hFessCall'⟩ :=
    biteTypedCallZeroSetSubstate hFessCall
      (by simpa [initState] using hdepthNe) AG
  obtain ⟨σfs, Afs, hFessSolm, _hEqFess⟩ :=
    catBiteMapCall hEqGrab hFessCall' hdepthNe
  have htgtF : EVM.address (biteVowAddrV eGrabS).val =
      AccountAddress.ofUInt256 (biteAddrMaskWord.land (solcSlotWord σg I ⟨4⟩)) := by
    rw [← biteVowAddrV_eq_of_equiv hEqGrab, addrId,
      accountAddress_ofUInt256_eq_ofNat_toNat, hmask, u256_land_comm]
    simp only [biteVowAddrV, catSlotWord, heGEam, heGEee]
  have hfessArg : bw (biteDartRateV I eUrnS iRate art) =
      Value.int (Int.ofNat (dart.mul iRate).toNat) := by rw [hdartrateBS]
  rw [hzff, hperm, ← htgtF, ← hfessArg] at hFessSolm
  have hvowCodeS : 0 < (UInt256.ofNat
      ((eGrabS.lookupAccount (biteVowAddrV eGrabS)).option 0
        (fun acc => acc.code.size))).toNat := by
    rw [← biteVowAddrV_eq_of_equiv hEqGrab,
      ← biteCodeW_eq_of_equiv (biteVowAddrV eGrabE) hEqGrab]
    have haddr : biteVowAddrV eGrabE =
        AccountAddress.ofUInt256 ((solcSlotWord σg I ⟨4⟩).land solcAddrMask) := by
      rw [accountAddress_ofUInt256_eq_ofNat_toNat]
      simp only [biteVowAddrV, catSlotWord, heGEam, heGEee]
    rw [haddr]
    refine codePos eGrabE ((solcSlotWord σg I ⟨4⟩).land solcAddrMask) ?_
    rw [heGEam, u256_land_comm, ← hmask]; exact hFessCode
  have hlive' : catSlotWord ⟨2⟩ eUrnS.accountMap eUrnS.executionEnv = ⟨1⟩ := by
    rw [← biteSlotEqOfEquiv hEqU ⟨2⟩]; exact hlive
  refine catBiteFessFailLeaf hcode hdispatch hdecode rd2300 hoszf hov2 ?_
  refine catBiteSourceFessFailRevert hwv
    (catBiteVatCodePos_of_uniswap hAccounts hvatCode) hIlksSolm hIlksDec
    hvatCodeIlkS hUrnsSolm hUrnsDec hlive' hsz36 hfitInkSpot hfitArtRate
    hspotPos (hposNe iRate hRatePos) hunsafe ?_ ?_ ?_ ?_ ?_
    (hposNe art hArtPos) ?_ ?_ ?_ ?_ ?_ hGrabSolm hGrabDec ?_ hvowCodeS
    hFessSolm
  · rw [← biteLitW_eq_of_equiv hEqU, ← biteBoxW_eq_of_equiv hEqU, hlitB, hboxB]
    exact hlitterbox
  · rw [← biteRoomV_eq_of_equiv hEqU, hroomB]; exact hroomdust
  · rw [← biteDunkRoomV_eq_of_equiv hEqU, hdunkroomB, hwad, Nat.mul_comm]
    exact hFitWad
  · rw [← biteChopW_eq_of_equiv hEqU, hchopB]; exact hposNe milkChop hChopPos
  · rw [← biteDartV_eq_of_equiv hEqU, hdartvB, Nat.mul_comm]; exact hFitInkDart
  · rw [← biteDartV_eq_of_equiv hEqU, hdartvB]; exact hDartPos
  · rw [← biteDinkV_eq_of_equiv hEqU, hdinkvB]; exact hDinkPos
  · rw [← biteDartV_eq_of_equiv hEqU, hdartvB]; simp only [int256Limit]
    exact Int.ofNat_le.mpr (hDartLim.trans_eq hsl)
  · rw [← biteDinkV_eq_of_equiv hEqU, hdinkvB]; simp only [int256Limit]
    exact Int.ofNat_le.mpr (hDinkLim.trans_eq hsl)
  · have haddr : biteVatAddr eUrnS =
        AccountAddress.ofUInt256 (catBiteVatTargetWord σus I) := by
      rw [accountAddress_ofUInt256_eq_ofNat_toNat]
      simp only [biteVatAddr, catBiteVatTargetWord, catAddressReturnWord,
        catSlotWord, heUSam, heUSee]
    rw [haddr]
    refine codePos eUrnS (catBiteVatTargetWord σus I) ?_
    rw [heUSam, show catBiteVatTargetWord σus I =
          (solcSlotWord σus I ⟨3⟩).land biteAddrMaskWord from by
        simp only [catBiteVatTargetWord, catAddressReturnWord, catSlotWord,
          hmask]]
    exact hGrabCodeS
  · -- hfitDartRate
    rw [← biteDartV_eq_of_equiv hEqU, hdartvB, Nat.mul_comm]; exact hRateFit


set_option maxHeartbeats 4000000 in
/-- **kick-fail branch (extracted).** grab+fess succeed, litter is stored, `kick` CALL returns
`success = 0`; maps the full 4-call chain + the litter SSTORE, fires `catBiteKickFailLeaf` +
`catBiteSourceKickFailRevert`. -/
theorem catBiteRevertKickFail {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {σ' σu σg σf σk : AccountMap} {A' Au Ag Af Ak : Substate}
    {cA' cAu cAg cAf cAk : Batteries.RBSet AccountAddress compare} {o' ou og ofb ok : ByteArray}
    {mem3 : ByteArray} {aw3 : UInt256} {R3 : List UInt256} {k3 C3 : ℕ} {zk : Bool}
    {flipW dartRate tabBase tab litterNew : UInt256}
    {art ink iSpot iRate iDust room milkDunk milkChop dunkRoom dunkRoomWad
      dartDenomRate dartCandidate dart inkDart dinkCandidate dink : UInt256}
    (hcode : I.code = catBytecode)
    (hdispatch : dispatchMsg contract I.calldata = some biteTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (biteTransition.params.map Param.name)
        (transitionSignature biteTransition).paramTypes I.calldata = some (biteLocals I))
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hwv : I.weiValue = ⟨0⟩) (hperm : I.perm = true) (hsz36 : 36 ≤ I.calldata.size)
    (hdepth : (I.depth : ℕ) < 1024)
    (hurn : biteAddrMaskWord.land (biteAddrMaskWord.land (calldataWord I.calldata 36)) = biteUrnWord I)
    (hilkslen : 160 ≤ o'.size) (hurnslen : 64 ≤ ou.size)
    (hlive : catSlotWord ⟨2⟩ σu I = ⟨1⟩)
    (hvatCode : ¬ Reasoning.Theory.extCodeSizeWord σ_evm (catBiteVatTargetWord σ_evm I) = ⟨0⟩)
    (hUrnsVatCode :
      ¬ Reasoning.Theory.extCodeSizeWord σ' ((catSlotWord ⟨3⟩ σ' I).land biteAddrMaskWord) = ⟨0⟩)
    (hGrabCode :
      ¬ Reasoning.Theory.extCodeSizeWord σu ((solcSlotWord σu I ⟨3⟩).land biteAddrMaskWord) = ⟨0⟩)
    (hFessCode :
      ¬ Reasoning.Theory.extCodeSizeWord σg (biteAddrMaskWord.land (solcSlotWord σg I ⟨4⟩)) = ⟨0⟩)
    (hKickCode :
      ¬ Reasoning.Theory.extCodeSizeWord (sstoreAccountMap I.codeOwner σf ⟨6⟩ litterNew)
        (biteAddrMaskWord.land flipW) = ⟨0⟩)
    (hIlksCall :
      typedCallViaEVM config (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        (AccountAddress.ofUInt256 (catBiteVatTargetWord σ_evm I)) "ilks" 0 [biteIlkVal I]
        (true, { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
                  accountMap := σ', substate := A', createdAccounts := cA' }, o') false)
    (hUrnsCall :
      typedCallViaEVM config
        { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
            accountMap := σ', createdAccounts := cA' }
        (AccountAddress.ofUInt256 ((catSlotWord ⟨3⟩ σ' I).land biteAddrMaskWord)) "urns" 0
        [biteIlkVal I, biteUrnVal I]
        (true, { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
                  accountMap := σu, substate := Au, createdAccounts := cAu }, ou) false)
    (hGrabCall :
      typedCallViaEVM config
        { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
            accountMap := σu, createdAccounts := cAu }
        (AccountAddress.ofUInt256 ((solcSlotWord σu I ⟨3⟩).land biteAddrMaskWord)) "grab" 0
        [Value.fixedBytes bytes32Width (EVM.Word.toBytesBE (biteIlkWord I)),
          Value.address (AccountAddress.ofNat
            (biteAddrMaskWord.land (biteAddrMaskWord.land (calldataWord I.calldata 36))).toNat),
          Value.address (AccountAddress.ofNat (UInt256.ofNat I.codeOwner.val).toNat),
          Value.address (AccountAddress.ofNat (biteAddrMaskWord.land (solcSlotWord σu I ⟨4⟩)).toNat),
          Value.int (-Int.ofNat dink.toNat), Value.int (-Int.ofNat dart.toNat)]
        (true, { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
                  accountMap := σg, substate := Ag, createdAccounts := cAg }, og) I.perm)
    (hFessCall :
      typedCallViaEVM config
        { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
            accountMap := σg, createdAccounts := cAg }
        (AccountAddress.ofUInt256 (biteAddrMaskWord.land (solcSlotWord σg I ⟨4⟩))) "fess" 0
        [Value.int (Int.ofNat (dart.mul iRate).toNat)]
        (true, { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
                accountMap := σf, substate := Af, createdAccounts := cAf }, ofb) I.perm)
    (hKickCall :
      typedCallViaEVM config
        { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
            accountMap := sstoreAccountMap I.codeOwner σf ⟨6⟩ litterNew, createdAccounts := cAf }
        (AccountAddress.ofUInt256 (biteAddrMaskWord.land flipW)) "kick" 0
        (seg8KickArgs (sstoreAccountMap I.codeOwner σf ⟨6⟩ litterNew) I
          (biteAddrMaskWord.land (calldataWord I.calldata 36)) tab dink)
        (zk, { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
                accountMap := σk, substate := Ak, createdAccounts := cAk }, ok) I.perm)
    (rd2532 :
      RD catBytecode I (Sat256.ofUInt256 g) (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        ⟨2532⟩ (⟨0⟩ :: R3) mem3 aw3 ok (cAk, σk) k3 C3)
    (hoszk : ok.size < UInt256.size) (hov3 : R3.length + 5 ≤ 1024) (hzkf : zk = false)
    (hRateFit : iRate.toNat * dart.toNat < UInt256.size)
    (hflipWDef : flipW = biteAddrMaskWord.land (solcSlotWord σu I (solcMappingSlot ⟨1⟩ (biteIlkWord I))))
    (hdartRateDef : dartRate = dart.mul iRate)
    (htabBaseDef : tabBase = dartRate.mul milkChop)
    (htabDef : tab = tabBase.div ⟨1000000000000000000⟩)
    (hlitterNewDef : litterNew = solcSlotWord σf I ⟨6⟩ + tab)
    (hChopFit : milkChop.toNat * dartRate.toNat < UInt256.size)
    (hLitFit : (solcSlotWord σf I ⟨6⟩).toNat + tab.toNat < UInt256.size)
    (hart : art = UInt256.ofNat (fromByteArrayBigEndian (ou.extract 32 64)))
    (hink : ink = UInt256.ofNat (fromByteArrayBigEndian (ou.extract 0 32)))
    (hiSpot : iSpot = UInt256.ofNat (fromByteArrayBigEndian (o'.extract 64 96)))
    (hiRate : iRate = UInt256.ofNat (fromByteArrayBigEndian (o'.extract 32 64)))
    (hiDustDef : iDust = UInt256.ofNat (fromByteArrayBigEndian (o'.extract 128 160)))
    (hroomDef : room = (solcSlotWord σu I ⟨5⟩).sub (solcSlotWord σu I ⟨6⟩))
    (hmilkDunkDef : milkDunk = solcSlotWord σu I (solcMappingSlot ⟨1⟩ (biteIlkWord I) + ⟨2⟩))
    (hmilkChopDef : milkChop = solcSlotWord σu I (solcMappingSlot ⟨1⟩ (biteIlkWord I) + ⟨1⟩))
    (hdunkRoomDef : dunkRoom = if milkDunk.gt room = ⟨0⟩ then milkDunk else room)
    (hdunkRoomWadDef : dunkRoomWad = dunkRoom.mul ⟨1000000000000000000⟩)
    (hdartDenomDef : dartDenomRate = dunkRoomWad.div iRate)
    (hdartCandDef : dartCandidate = dartDenomRate.div milkChop)
    (hdartDef : dart = if art.gt dartCandidate = ⟨0⟩ then art else dartCandidate)
    (hinkDartDef : inkDart = ink.mul dart)
    (hdinkCandDef : dinkCandidate = inkDart.div art)
    (hdinkDef : dink = if ink.gt dinkCandidate = ⟨0⟩ then ink else dinkCandidate)
    (hspotPos : 0 < iSpot.toNat) (hfitArtRate : art.toNat * iRate.toNat < UInt256.size)
    (hfitInkSpot : ink.toNat * iSpot.toNat < UInt256.size)
    (hunsafe : (ink * iSpot).toNat < (art * iRate).toNat)
    (hlitterbox : (solcSlotWord σu I ⟨6⟩).toNat < (solcSlotWord σu I ⟨5⟩).toNat)
    (hroomdust : iDust.toNat ≤ room.toNat)
    (hRatePos : iRate ≠ ⟨0⟩) (hChopPos : milkChop ≠ ⟨0⟩)
    (hFitWad : (⟨1000000000000000000⟩ : UInt256).toNat * dunkRoom.toNat < UInt256.size)
    (hArtPos : art ≠ ⟨0⟩) (hFitInkDart : dart.toNat * ink.toNat < UInt256.size)
    (hDartPos : 0 < dart.toNat) (hDinkPos : 0 < dink.toNat)
    (hDartLim : dart.toNat ≤ (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨255⟩).toNat)
    (hDinkLim : dink.toNat ≤ (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨255⟩).toNat) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hdepthNe : I.depth ≠ 1024 := by omega
  have hmask : biteAddrMaskWord = solcAddrMask := by native_decide
  have hposNe : ∀ w : UInt256, w ≠ ⟨0⟩ → 0 < w.toNat :=
    fun w hw => Nat.pos_of_ne_zero (fun h => hw (uint256_toNat_eq_zero h))
  have codePos : ∀ (e : EVM.State) (w : UInt256),
      extCodeSizeWord e.accountMap w ≠ ⟨0⟩ →
      0 < (UInt256.ofNat ((e.lookupAccount
        (AccountAddress.ofUInt256 w)).option 0
        (fun acc => acc.code.size))).toNat := by
    intro e w hw
    unfold extCodeSizeWord at hw
    simp only [State.lookupAccount]
    cases hf : e.accountMap.find? (AccountAddress.ofUInt256 w) with
    | none => rw [hf] at hw; simp [Option.option] at hw
    | some acc =>
        rw [hf] at hw
        simp only [Option.option, Function.comp] at hw ⊢
        exact hposNe _ hw
  have addrId : ∀ a : AccountAddress, EVM.address a.val = a := by
    intro a; apply Fin.ext
    show a.val % EVM.addressModulus = a.val
    rw [show EVM.addressModulus = AccountAddress.size from by decide]
    exact Nat.mod_eq_of_lt a.isLt
  have hAddrRT : ∀ a : AccountAddress,
      AccountAddress.ofNat (UInt256.ofNat a.val).toNat = a := by
    intro a
    have h1 : (UInt256.ofNat a.val).toNat = a.val :=
      UInt256.toNat_ofNat_of_lt (lt_of_lt_of_le a.isLt
        (show AccountAddress.size ≤ UInt256.size from by decide))
    rw [h1]; apply Fin.ext
    simp only [AccountAddress.ofNat, Fin.ofNat]
    exact Nat.mod_eq_of_lt a.isLt
  have hbytes : biteIlkBytes I = EVM.Word.toBytesBE (biteIlkWord I) := by
    have hlen32 : (biteIlkBytes I).length = 32 := by
      simp only [biteIlkBytes, List.length_take, List.length_drop]
      have htlen : I.calldata.toList.length = I.calldata.size := by
        rw [byteArray_toList_eq, Array.length_toList]; rfl
      rw [htlen]; omega
    have hword : ABI.bytesToWord (biteIlkBytes I) = biteIlkWord I := by
      simpa [biteIlkBytes, biteIlkWord] using
        (decode_word_at_eq_any I.calldata 4 (by simpa using hsz36))
    have hto := toBytesBE_bytesToWord_of_length (bs := biteIlkBytes I) hlen32
    rw [hword] at hto; exact hto.symm
  have uminEq : ∀ a b : UInt256,
      (if UInt256.gt a b = ⟨0⟩ then a else b) = umin a b := by
    intro a b; unfold umin
    by_cases h : a.toNat ≤ b.toNat
    · rw [if_pos (ugt_zero h), if_pos h]
    · rw [if_neg (by rw [ugt_one (by omega)]; decide), if_neg h]
  have hwad : wadU = ⟨1000000000000000000⟩ := by native_decide
  have hsl : (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨255⟩).toNat =
      57896044618658097711785492504343953926634992332820282019728792003956564819968 := by
    native_decide
  have storeFlat : ∀ (ev : EVM.State) (aa : AccountAddress) (k v : UInt256),
      Solm.EVM.storageStore ev aa k v =
        { ev with accountMap := sstoreAccountMap aa ev.accountMap k v } := by
    intro ev aa k v
    simp only [Solm.EVM.storageStore, sstoreAccountMap, State.lookupAccount]
    cases h : ev.accountMap.find? aa with
    | none => simp [Option.option]
    | some acc => simp [Option.option, State.setAccount, Account.updateStorage]
  have hbr : ∀ (o : ByteArray) (k : ℕ), k + 32 ≤ o.size →
      ABI.bytesToWord ((o.toList.drop k).take 32) =
        UInt256.ofNat (fromByteArrayBigEndian (o.extract k (k + 32))) := by
    intro o k h
    rw [decode_word_at_eq_any o k h, uInt256OfByteArray_eq]
    congr 1; unfold fromByteArrayBigEndian; congr 1
    rw [byteArray_toList_eq (o.readBytes k 32),
      readBytes_at_toList_any o k h,
      byteArray_toList_eq (o.extract k (k + 32)),
      ByteArray.data_extract, Array.toList_extract,
      List.extract_eq_take_drop]
    simp
  obtain ⟨σs, As, σus, Aus, hIlksSolm, hUrnsSolm, hAmEq, hvatCodeIlkS⟩ :=
    catBiteMapUrns hAccounts hdepthNe hUrnsVatCode hIlksCall hUrnsCall
  have slotEqUS : ∀ s : UInt256, solcSlotWord σus I s = solcSlotWord σu I s := by
    intro s; simp only [solcSlotWord]
    rw [accountMapEquiv_storage_findD hAmEq I.codeOwner s ⟨0⟩]
  set eUrnE := { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
    accountMap := σu, substate := Au, createdAccounts := cAu } with heUrnEdef
  set eUrnS := { initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I with
    accountMap := σus, substate := Aus, createdAccounts := cAu } with heUrnSdef
  have hEqU : EVMStateEquiv eUrnE eUrnS := ⟨rfl, rfl, hAmEq⟩
  have heUEam : eUrnE.accountMap = σu := rfl
  have heUEee : eUrnE.executionEnv = I := rfl
  have heUSam : eUrnS.accountMap = σus := rfl
  have heUSee : eUrnS.executionEnv = I := rfl
  have hboxB : biteBoxW eUrnE = solcSlotWord σu I ⟨5⟩ := by
    simp only [biteBoxW, catSlotWord, heUEam, heUEee]
  have hlitB : biteLitW eUrnE = solcSlotWord σu I ⟨6⟩ := by
    simp only [biteLitW, catSlotWord, heUEam, heUEee]
  have hchopB : biteChopW I eUrnE = milkChop := by
    rw [hmilkChopDef]
    simp only [biteChopW, catSlotWord, heUEam, heUEee, biteChopSlot,
      biteFlipSlot_eq hsz36]
  have hdunkB : biteDunkW I eUrnE = milkDunk := by
    rw [hmilkDunkDef]
    simp only [biteDunkW, catSlotWord, heUEam, heUEee, biteDunkSlot,
      biteFlipSlot_eq hsz36]
  have hroomB : biteRoomV eUrnE = room := by
    rw [hroomDef]
    simp only [biteRoomV, biteBoxW, biteLitW, catSlotWord, heUEam, heUEee]
  have hdunkroomB : biteDunkRoomV I eUrnE = dunkRoom := by
    rw [hdunkRoomDef, uminEq milkDunk room]
    simp only [biteDunkRoomV, hdunkB, hroomB]
  have hdartvB : biteDartV I eUrnE iRate art = dart := by
    have hcand : biteDartCandV I eUrnE iRate = dartCandidate := by
      simp only [biteDartCandV, biteDartDenomV, biteDunkRoomWadV,
        hchopB, hdunkroomB, hwad, hdartCandDef, hdartDenomDef,
        hdunkRoomWadDef]
      rfl
    rw [hdartDef, uminEq art dartCandidate]
    simp only [biteDartV, hcand]
  have hdinkvB : biteDinkV I eUrnE iRate art ink = dink := by
    have hcand : biteDinkCandV I eUrnE iRate art ink = dinkCandidate := by
      simp only [biteDinkCandV, biteInkDartV, hdartvB, hdinkCandDef,
        hinkDartDef]
      rfl
    rw [hdinkDef, uminEq ink dinkCandidate]
    simp only [biteDinkV, hcand]
  have hdartrateBE : biteDartRateV I eUrnE iRate art = dartRate := by
    rw [hdartRateDef]; simp only [biteDartRateV, hdartvB]; rfl
  have htabB : biteTabV I eUrnE iRate art = tab := by
    rw [htabDef, htabBaseDef]
    simp only [biteTabV, biteTabBaseV, hdartrateBE, hchopB, hwad]; rfl
  have hIlksDec : config.externalABI.decode? "ilks" o' =
      some [bw (UInt256.ofNat (fromByteArrayBigEndian (o'.extract 0 32))),
        bw iRate, bw iSpot,
        bw (UInt256.ofNat (fromByteArrayBigEndian (o'.extract 96 128))),
        bw iDust] := by
    have h := catBiteIlksDecode_ok hilkslen
    rw [hbr o' 0 (by omega), hbr o' 32 (by omega), hbr o' 64 (by omega),
      hbr o' 96 (by omega), hbr o' 128 (by omega)] at h
    rw [hiRate, hiSpot, hiDustDef]; exact h
  have hUrnsDec : config.externalABI.decode? "urns" ou =
      some [bw ink, bw art] := by
    have h := catBiteUrnsDecode_ok hurnslen
    rw [hbr ou 0 (by omega), hbr ou 32 (by omega)] at h
    rw [hink, hart]; exact h
  obtain ⟨AG, hGrabCall'⟩ :=
    biteTypedCallZeroSetSubstate hGrabCall
      (by simpa [initState] using hdepthNe) Au
  obtain ⟨σgs, Ags, hGrabSolm, hEqGrab⟩ :=
    catBiteMapCall hEqU hGrabCall' hdepthNe
  set eGrabE := { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
    accountMap := σg, substate := AG, createdAccounts := cAg } with heGrabEdef
  set eGrabS := { initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I with
    accountMap := σgs, substate := Ags, createdAccounts := cAg } with heGrabSdef
  have heGEam : eGrabE.accountMap = σg := rfl
  have heGEee : eGrabE.executionEnv = I := rfl
  have htgtU : EVM.address (biteVatAddr eUrnS).val =
      AccountAddress.ofUInt256 ((solcSlotWord σu I ⟨3⟩).land biteAddrMaskWord) := by
    rw [← biteVatAddr_eq_of_equiv hEqU, addrId,
      accountAddress_ofUInt256_eq_ofNat_toNat, hmask]
    simp only [biteVatAddr, catSlotWord, heUEam, heUEee]
  have h1 : biteIlkVal I =
      Value.fixedBytes bytes32Width (EVM.Word.toBytesBE (biteIlkWord I)) := by
    simp only [biteIlkVal, hbytes]
  have h2 : biteUrnVal I = Value.address (AccountAddress.ofNat
      (biteAddrMaskWord.land
        (biteAddrMaskWord.land (calldataWord I.calldata 36))).toNat) := by
    rw [hurn]
    simp only [biteUrnVal, biteUrnWord, biteUrnAddr, hAddrRT]
  have h3 : (eUrnS.executionEnv.codeOwner : AccountAddress) =
      AccountAddress.ofNat (UInt256.ofNat I.codeOwner.val).toNat := by
    rw [heUSee]; exact (hAddrRT I.codeOwner).symm
  have h4 : biteVowAddrV eUrnS = AccountAddress.ofNat
      (biteAddrMaskWord.land (solcSlotWord σu I ⟨4⟩)).toNat := by
    rw [← biteVowAddrV_eq_of_equiv hEqU]
    simp only [biteVowAddrV, catSlotWord, heUEam, heUEee, hmask]
    rw [u256_land_comm]
  have hdartvBS : biteDartV I eUrnS iRate art = dart := by
    rw [← biteDartV_eq_of_equiv hEqU]; exact hdartvB
  have hdinkvBS : biteDinkV I eUrnS iRate art ink = dink := by
    rw [← biteDinkV_eq_of_equiv hEqU]; exact hdinkvB
  have hdartrateBS : biteDartRateV I eUrnS iRate art = dart.mul iRate := by
    rw [← biteDartRateV_eq_of_equiv hEqU]
    simp only [biteDartRateV, hdartvB]; rfl
  have htabBS : biteTabV I eUrnS iRate art = tab := by
    rw [← biteTabV_eq_of_equiv hEqU]; exact htabB
  have hGrabCodeS :
      ¬ Reasoning.Theory.extCodeSizeWord σus
        ((solcSlotWord σus I ⟨3⟩).land biteAddrMaskWord) = ⟨0⟩ := by
    rw [slotEqUS ⟨3⟩, ← extCodeSizeWord_accountMapEquiv hAmEq]
    exact hGrabCode
  rw [hperm, ← htgtU, ← h1, ← h2, ← h3, ← h4, ← hdinkvBS, ← hdartvBS]
    at hGrabSolm
  have hGrabDec : config.externalABI.decode? "grab" og = some [] := by
    simp [config, externalABI, decodeVoid?]
  obtain ⟨AF, hFessCall'⟩ :=
    biteTypedCallZeroSetSubstate hFessCall
      (by simpa [initState] using hdepthNe) AG
  obtain ⟨σfs, Afs, hFessSolm, hEqFess⟩ :=
    catBiteMapCall hEqGrab hFessCall' hdepthNe
  set eFessE := { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
    accountMap := σf, substate := AF, createdAccounts := cAf } with heFessEdef
  set eFessS := { initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I with
    accountMap := σfs, substate := Afs, createdAccounts := cAf } with heFessSdef
  have heFEam : eFessE.accountMap = σf := rfl
  have heFEee : eFessE.executionEnv = I := rfl
  have htgtF : EVM.address (biteVowAddrV eGrabS).val =
      AccountAddress.ofUInt256 (biteAddrMaskWord.land (solcSlotWord σg I ⟨4⟩)) := by
    rw [← biteVowAddrV_eq_of_equiv hEqGrab, addrId,
      accountAddress_ofUInt256_eq_ofNat_toNat, hmask, u256_land_comm]
    simp only [biteVowAddrV, catSlotWord, heGEam, heGEee]
  have hfessArg : bw (biteDartRateV I eUrnS iRate art) =
      Value.int (Int.ofNat (dart.mul iRate).toNat) := by rw [hdartrateBS]
  rw [hperm, ← htgtF, ← hfessArg] at hFessSolm
  have hFessDec : config.externalABI.decode? "fess" ofb = some [] := by
    simp [config, externalABI, decodeVoid?]
  have hvowCodeS : 0 < (UInt256.ofNat
      ((eGrabS.lookupAccount (biteVowAddrV eGrabS)).option 0
        (fun acc => acc.code.size))).toNat := by
    rw [← biteVowAddrV_eq_of_equiv hEqGrab,
      ← biteCodeW_eq_of_equiv (biteVowAddrV eGrabE) hEqGrab]
    have haddr : biteVowAddrV eGrabE =
        AccountAddress.ofUInt256 ((solcSlotWord σg I ⟨4⟩).land solcAddrMask) := by
      rw [accountAddress_ofUInt256_eq_ofNat_toNat]
      simp only [biteVowAddrV, catSlotWord, heGEam, heGEee]
    rw [haddr]
    refine codePos eGrabE ((solcSlotWord σg I ⟨4⟩).land solcAddrMask) ?_
    rw [heGEam, u256_land_comm, ← hmask]; exact hFessCode
  have hlitFB : biteLitW eFessE = solcSlotWord σf I ⟨6⟩ := by
    simp only [biteLitW, catSlotWord, heFEam, heFEee]
  have hlitternewE : biteLitterNewV I eUrnE eFessE iRate art = litterNew := by
    rw [hlitterNewDef]
    simp only [biteLitterNewV, hlitFB, htabB]
  set hLitVal := biteLitterNewV I eUrnS eFessS iRate art with hLitValDef
  have hLitValEq : litterNew = hLitVal :=
    hlitternewE.symm.trans (biteLitterNewV_eq_of_equiv hEqU hEqFess iRate art)
  obtain ⟨AK, hKickCall'⟩ :=
    biteTypedCallZeroSetSubstate hKickCall
      (by simpa [initState] using hdepthNe) AF
  rw [hLitValEq] at hKickCall'
  have hStateLit : EVMStateEquiv
      { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
        accountMap := sstoreAccountMap I.codeOwner σf ⟨6⟩ hLitVal,
        substate := AF, createdAccounts := cAf }
      { initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I with
        accountMap := sstoreAccountMap I.codeOwner σfs ⟨6⟩ hLitVal,
        substate := Afs, createdAccounts := cAf } :=
    ⟨rfl, rfl,
      accountMapEquiv_sstoreAccountMap I.codeOwner ⟨6⟩ hLitVal hEqFess.accountMap⟩
  obtain ⟨σks, Aks, hKickSolm, _hEqKick⟩ :=
    catBiteMapCall hStateLit hKickCall' hdepthNe
  set eLitS := { initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I with
    accountMap := sstoreAccountMap I.codeOwner σfs ⟨6⟩ hLitVal,
    substate := Afs, createdAccounts := cAf } with heLitSdef
  have heLSam : eLitS.accountMap =
    sstoreAccountMap I.codeOwner σfs ⟨6⟩ hLitVal := rfl
  have heLSee : eLitS.executionEnv = I := rfl
  have hflipAddrS : biteFlipAddrV I eUrnS =
      AccountAddress.ofUInt256 (biteAddrMaskWord.land flipW) := by
    rw [← biteFlipAddrV_eq_of_equiv hEqU,
      accountAddress_ofUInt256_eq_ofNat_toNat, hflipWDef, hmask]
    simp only [biteFlipAddrV, catSlotWord, heUEam, heUEee,
      biteFlipSlot_eq hsz36]
    rw [solcAddrMask_clean_left
      (by rw [u256_land_comm]; exact solcAddrMask_result_canonical _),
      u256_land_comm]
  have htgtK : EVM.address (biteFlipAddrV I eUrnS).val =
      AccountAddress.ofUInt256 (biteAddrMaskWord.land flipW) := by
    rw [addrId]; exact hflipAddrS
  have hexp : UInt256.exp (⟨256⟩ : UInt256) ⟨0⟩ = ⟨1⟩ := by native_decide
  have hdiv1 : ∀ y : UInt256, UInt256.div y ⟨1⟩ = y := fun y => by
    apply u256_inj
    rw [udiv_toNat, show (⟨1⟩ : UInt256).toNat = 1 from by native_decide,
      Nat.div_one]
  have hvowW : ∀ σx : AccountMap,
      UInt256.land (solcSlotWord σx I ⟨4⟩) solcAddrMask = seg8VowM σx I := by
    intro σx
    simp only [seg8VowM, hmask, hexp, hdiv1]
    rw [solcAddrMask_clean_left
      (by rw [u256_land_comm]; exact solcAddrMask_result_canonical _),
      u256_land_comm]
  have hslot4 :
      solcSlotWord (sstoreAccountMap I.codeOwner σfs ⟨6⟩ hLitVal) I ⟨4⟩ =
      solcSlotWord (sstoreAccountMap I.codeOwner σf ⟨6⟩ hLitVal) I ⟨4⟩ := by
    simp only [solcSlotWord]
    exact (accountMapEquiv_storage_findD
      (accountMapEquiv_sstoreAccountMap I.codeOwner ⟨6⟩ hLitVal hEqFess.accountMap)
      I.codeOwner ⟨4⟩ ⟨0⟩).symm
  have hvowLit : biteVowAddrV eLitS =
      AccountAddress.ofNat
        (seg8VowM (sstoreAccountMap I.codeOwner σf ⟨6⟩ hLitVal) I).toNat := by
    simp only [biteVowAddrV, catSlotWord, heLSam, heLSee, hmask]
    rw [hslot4, hvowW]
  simp only [seg8KickArgs, seg8UrnM] at hKickSolm
  rw [hzkf, hperm, ← htgtK, ← h2, ← hvowLit, ← htabBS, ← hdinkvBS] at hKickSolm
  have hflipCodeS : 0 < (UInt256.ofNat
      ((eLitS.lookupAccount (biteFlipAddrV I eUrnS)).option 0
        (fun acc => acc.code.size))).toNat := by
    rw [hflipAddrS]
    refine codePos eLitS (biteAddrMaskWord.land flipW) ?_
    rw [heLSam, ← extCodeSizeWord_accountMapEquiv
        (accountMapEquiv_sstoreAccountMap I.codeOwner ⟨6⟩ hLitVal
          hEqFess.accountMap), ← hLitValEq]
    exact hKickCode
  have hlive' : catSlotWord ⟨2⟩ eUrnS.accountMap eUrnS.executionEnv = ⟨1⟩ := by
    rw [← biteSlotEqOfEquiv hEqU ⟨2⟩]; exact hlive
  have hLitStoreS :
      storageLocStore eFessS (wordLoc ⟨6⟩)
        (.int (Int.ofNat hLitVal.toNat)) = some eLitS := by
    have h := storageLocStore_uint256 eFessS ⟨6⟩ hLitVal
    rw [storeFlat] at h
    exact h
  refine catBiteKickFailLeaf hcode hdispatch hdecode rd2532 hoszk hov3 ?_
  refine catBiteSourceKickFailRevert hwv
    (catBiteVatCodePos_of_uniswap hAccounts hvatCode) hIlksSolm hIlksDec
    hvatCodeIlkS hUrnsSolm hUrnsDec hlive' hsz36 hfitInkSpot hfitArtRate
    hspotPos (hposNe iRate hRatePos) hunsafe ?_ ?_ ?_ ?_ ?_
    (hposNe art hArtPos) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hGrabSolm hGrabDec
    hvowCodeS hFessSolm hFessDec hLitStoreS hflipCodeS hKickSolm
  · rw [← biteLitW_eq_of_equiv hEqU, ← biteBoxW_eq_of_equiv hEqU, hlitB, hboxB]
    exact hlitterbox
  · rw [← biteRoomV_eq_of_equiv hEqU, hroomB]; exact hroomdust
  · rw [← biteDunkRoomV_eq_of_equiv hEqU, hdunkroomB, hwad, Nat.mul_comm]
    exact hFitWad
  · rw [← biteChopW_eq_of_equiv hEqU, hchopB]; exact hposNe milkChop hChopPos
  · rw [← biteDartV_eq_of_equiv hEqU, hdartvB, Nat.mul_comm]; exact hFitInkDart
  · rw [← biteDartV_eq_of_equiv hEqU, hdartvB]; exact hDartPos
  · rw [← biteDinkV_eq_of_equiv hEqU, hdinkvB]; exact hDinkPos
  · rw [← biteDartV_eq_of_equiv hEqU, hdartvB]; simp only [int256Limit]
    exact Int.ofNat_le.mpr (hDartLim.trans_eq hsl)
  · rw [← biteDinkV_eq_of_equiv hEqU, hdinkvB]; simp only [int256Limit]
    exact Int.ofNat_le.mpr (hDinkLim.trans_eq hsl)
  · have haddr : biteVatAddr eUrnS =
        AccountAddress.ofUInt256 (catBiteVatTargetWord σus I) := by
      rw [accountAddress_ofUInt256_eq_ofNat_toNat]
      simp only [biteVatAddr, catBiteVatTargetWord, catAddressReturnWord,
        catSlotWord, heUSam, heUSee]
    rw [haddr]
    refine codePos eUrnS (catBiteVatTargetWord σus I) ?_
    rw [heUSam, show catBiteVatTargetWord σus I =
          (solcSlotWord σus I ⟨3⟩).land biteAddrMaskWord from by
        simp only [catBiteVatTargetWord, catAddressReturnWord, catSlotWord,
          hmask]]
    exact hGrabCodeS
  · rw [← biteDartV_eq_of_equiv hEqU, hdartvB, Nat.mul_comm]; exact hRateFit
  · rw [← biteDartRateV_eq_of_equiv hEqU, ← biteChopW_eq_of_equiv hEqU,
      hdartrateBE, hchopB, Nat.mul_comm]; exact hChopFit
  · rw [← biteLitW_eq_of_equiv hEqFess, ← biteTabV_eq_of_equiv hEqU,
      hlitFB, htabB]; exact hLitFit

set_option maxHeartbeats 4000000 in
/-- **kick return-decode-short branch (extracted).** grab+fess+kick succeed but `kick` returns
`< 32` bytes; same chain, fires `catBiteKickReturnDecodeShortLeaf` + `catBiteSourceKickDecodeRevert`.
Mem facts (`hMloadFree*`) taken as hypotheses so the walk supplies them. -/
theorem catBiteRevertKickDecode {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {σ' σu σg σf σk : AccountMap} {A' Au Ag Af Ak : Substate}
    {cA' cAu cAg cAf cAk : Batteries.RBSet AccountAddress compare} {o' ou og ofb ok : ByteArray}
    {mem3 : ByteArray} {aw3 : UInt256} {R3 : List UInt256} {k3 C3 : ℕ} {zk : Bool}
    {status d0 d1 d2 fp : UInt256}
    {flipW dartRate tabBase tab litterNew : UInt256}
    {art ink iSpot iRate iDust room milkDunk milkChop dunkRoom dunkRoomWad
      dartDenomRate dartCandidate dart inkDart dinkCandidate dink : UInt256}
    (hcode : I.code = catBytecode)
    (hdispatch : dispatchMsg contract I.calldata = some biteTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (biteTransition.params.map Param.name)
        (transitionSignature biteTransition).paramTypes I.calldata = some (biteLocals I))
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hwv : I.weiValue = ⟨0⟩) (hperm : I.perm = true) (hsz36 : 36 ≤ I.calldata.size)
    (hdepth : (I.depth : ℕ) < 1024)
    (hurn : biteAddrMaskWord.land (biteAddrMaskWord.land (calldataWord I.calldata 36)) = biteUrnWord I)
    (hilkslen : 160 ≤ o'.size) (hurnslen : 64 ≤ ou.size)
    (hlive : catSlotWord ⟨2⟩ σu I = ⟨1⟩)
    (hvatCode : ¬ Reasoning.Theory.extCodeSizeWord σ_evm (catBiteVatTargetWord σ_evm I) = ⟨0⟩)
    (hUrnsVatCode :
      ¬ Reasoning.Theory.extCodeSizeWord σ' ((catSlotWord ⟨3⟩ σ' I).land biteAddrMaskWord) = ⟨0⟩)
    (hGrabCode :
      ¬ Reasoning.Theory.extCodeSizeWord σu ((solcSlotWord σu I ⟨3⟩).land biteAddrMaskWord) = ⟨0⟩)
    (hFessCode :
      ¬ Reasoning.Theory.extCodeSizeWord σg (biteAddrMaskWord.land (solcSlotWord σg I ⟨4⟩)) = ⟨0⟩)
    (hKickCode :
      ¬ Reasoning.Theory.extCodeSizeWord (sstoreAccountMap I.codeOwner σf ⟨6⟩ litterNew)
        (biteAddrMaskWord.land flipW) = ⟨0⟩)
    (hIlksCall :
      typedCallViaEVM config (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        (AccountAddress.ofUInt256 (catBiteVatTargetWord σ_evm I)) "ilks" 0 [biteIlkVal I]
        (true, { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
                  accountMap := σ', substate := A', createdAccounts := cA' }, o') false)
    (hUrnsCall :
      typedCallViaEVM config
        { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
            accountMap := σ', createdAccounts := cA' }
        (AccountAddress.ofUInt256 ((catSlotWord ⟨3⟩ σ' I).land biteAddrMaskWord)) "urns" 0
        [biteIlkVal I, biteUrnVal I]
        (true, { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
                  accountMap := σu, substate := Au, createdAccounts := cAu }, ou) false)
    (hGrabCall :
      typedCallViaEVM config
        { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
            accountMap := σu, createdAccounts := cAu }
        (AccountAddress.ofUInt256 ((solcSlotWord σu I ⟨3⟩).land biteAddrMaskWord)) "grab" 0
        [Value.fixedBytes bytes32Width (EVM.Word.toBytesBE (biteIlkWord I)),
          Value.address (AccountAddress.ofNat
            (biteAddrMaskWord.land (biteAddrMaskWord.land (calldataWord I.calldata 36))).toNat),
          Value.address (AccountAddress.ofNat (UInt256.ofNat I.codeOwner.val).toNat),
          Value.address (AccountAddress.ofNat (biteAddrMaskWord.land (solcSlotWord σu I ⟨4⟩)).toNat),
          Value.int (-Int.ofNat dink.toNat), Value.int (-Int.ofNat dart.toNat)]
        (true, { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
                  accountMap := σg, substate := Ag, createdAccounts := cAg }, og) I.perm)
    (hFessCall :
      typedCallViaEVM config
        { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
            accountMap := σg, createdAccounts := cAg }
        (AccountAddress.ofUInt256 (biteAddrMaskWord.land (solcSlotWord σg I ⟨4⟩))) "fess" 0
        [Value.int (Int.ofNat (dart.mul iRate).toNat)]
        (true, { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
                accountMap := σf, substate := Af, createdAccounts := cAf }, ofb) I.perm)
    (hKickCall :
      typedCallViaEVM config
        { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
            accountMap := sstoreAccountMap I.codeOwner σf ⟨6⟩ litterNew, createdAccounts := cAf }
        (AccountAddress.ofUInt256 (biteAddrMaskWord.land flipW)) "kick" 0
        (seg8KickArgs (sstoreAccountMap I.codeOwner σf ⟨6⟩ litterNew) I
          (biteAddrMaskWord.land (calldataWord I.calldata 36)) tab dink)
        (zk, { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
                accountMap := σk, substate := Ak, createdAccounts := cAk }, ok) I.perm)
    (rd2532 :
      RD catBytecode I (Sat256.ofUInt256 g) (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        ⟨2532⟩ (status :: d0 :: d1 :: d2 :: R3) mem3 aw3 ok (cAk, σk) k3 C3)
    (hoszk : ok.size < UInt256.size) (hov3 : R3.length + 6 ≤ 1024) (hzk : zk = true)
    (hstatus : status ≠ ⟨0⟩) (hshort : ok.size < 32)
    (hMloadFreeValue :
      (if (⟨64⟩ : UInt256).toNat ≥ mem3.size ∨ (⟨64⟩ : UInt256) ≥ aw3 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat (fromByteArrayBigEndian (mem3.readWithPadding (⟨64⟩ : UInt256).toNat 32)))
        = fp)
    (hMloadFreeCost : ∀ s : State, s.machineState.activeWords = aw3 →
        s.machineState.stack = (⟨64⟩ : UInt256) :: R3 → memoryExpansionCost s .MLOAD = 0)
    (hMloadFreeAw : UInt256.ofNat (MachineState.M aw3.toNat 64 32) = aw3)
    (hRateFit : iRate.toNat * dart.toNat < UInt256.size)
    (hflipWDef : flipW = biteAddrMaskWord.land (solcSlotWord σu I (solcMappingSlot ⟨1⟩ (biteIlkWord I))))
    (hdartRateDef : dartRate = dart.mul iRate)
    (htabBaseDef : tabBase = dartRate.mul milkChop)
    (htabDef : tab = tabBase.div ⟨1000000000000000000⟩)
    (hlitterNewDef : litterNew = solcSlotWord σf I ⟨6⟩ + tab)
    (hChopFit : milkChop.toNat * dartRate.toNat < UInt256.size)
    (hLitFit : (solcSlotWord σf I ⟨6⟩).toNat + tab.toNat < UInt256.size)
    (hart : art = UInt256.ofNat (fromByteArrayBigEndian (ou.extract 32 64)))
    (hink : ink = UInt256.ofNat (fromByteArrayBigEndian (ou.extract 0 32)))
    (hiSpot : iSpot = UInt256.ofNat (fromByteArrayBigEndian (o'.extract 64 96)))
    (hiRate : iRate = UInt256.ofNat (fromByteArrayBigEndian (o'.extract 32 64)))
    (hiDustDef : iDust = UInt256.ofNat (fromByteArrayBigEndian (o'.extract 128 160)))
    (hroomDef : room = (solcSlotWord σu I ⟨5⟩).sub (solcSlotWord σu I ⟨6⟩))
    (hmilkDunkDef : milkDunk = solcSlotWord σu I (solcMappingSlot ⟨1⟩ (biteIlkWord I) + ⟨2⟩))
    (hmilkChopDef : milkChop = solcSlotWord σu I (solcMappingSlot ⟨1⟩ (biteIlkWord I) + ⟨1⟩))
    (hdunkRoomDef : dunkRoom = if milkDunk.gt room = ⟨0⟩ then milkDunk else room)
    (hdunkRoomWadDef : dunkRoomWad = dunkRoom.mul ⟨1000000000000000000⟩)
    (hdartDenomDef : dartDenomRate = dunkRoomWad.div iRate)
    (hdartCandDef : dartCandidate = dartDenomRate.div milkChop)
    (hdartDef : dart = if art.gt dartCandidate = ⟨0⟩ then art else dartCandidate)
    (hinkDartDef : inkDart = ink.mul dart)
    (hdinkCandDef : dinkCandidate = inkDart.div art)
    (hdinkDef : dink = if ink.gt dinkCandidate = ⟨0⟩ then ink else dinkCandidate)
    (hspotPos : 0 < iSpot.toNat) (hfitArtRate : art.toNat * iRate.toNat < UInt256.size)
    (hfitInkSpot : ink.toNat * iSpot.toNat < UInt256.size)
    (hunsafe : (ink * iSpot).toNat < (art * iRate).toNat)
    (hlitterbox : (solcSlotWord σu I ⟨6⟩).toNat < (solcSlotWord σu I ⟨5⟩).toNat)
    (hroomdust : iDust.toNat ≤ room.toNat)
    (hRatePos : iRate ≠ ⟨0⟩) (hChopPos : milkChop ≠ ⟨0⟩)
    (hFitWad : (⟨1000000000000000000⟩ : UInt256).toNat * dunkRoom.toNat < UInt256.size)
    (hArtPos : art ≠ ⟨0⟩) (hFitInkDart : dart.toNat * ink.toNat < UInt256.size)
    (hDartPos : 0 < dart.toNat) (hDinkPos : 0 < dink.toNat)
    (hDartLim : dart.toNat ≤ (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨255⟩).toNat)
    (hDinkLim : dink.toNat ≤ (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨255⟩).toNat) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hdepthNe : I.depth ≠ 1024 := by omega
  have hmask : biteAddrMaskWord = solcAddrMask := by native_decide
  have hposNe : ∀ w : UInt256, w ≠ ⟨0⟩ → 0 < w.toNat :=
    fun w hw => Nat.pos_of_ne_zero (fun h => hw (uint256_toNat_eq_zero h))
  have codePos : ∀ (e : EVM.State) (w : UInt256),
      extCodeSizeWord e.accountMap w ≠ ⟨0⟩ →
      0 < (UInt256.ofNat ((e.lookupAccount
        (AccountAddress.ofUInt256 w)).option 0
        (fun acc => acc.code.size))).toNat := by
    intro e w hw
    unfold extCodeSizeWord at hw
    simp only [State.lookupAccount]
    cases hf : e.accountMap.find? (AccountAddress.ofUInt256 w) with
    | none => rw [hf] at hw; simp [Option.option] at hw
    | some acc =>
        rw [hf] at hw
        simp only [Option.option, Function.comp] at hw ⊢
        exact hposNe _ hw
  have addrId : ∀ a : AccountAddress, EVM.address a.val = a := by
    intro a; apply Fin.ext
    show a.val % EVM.addressModulus = a.val
    rw [show EVM.addressModulus = AccountAddress.size from by decide]
    exact Nat.mod_eq_of_lt a.isLt
  have hAddrRT : ∀ a : AccountAddress,
      AccountAddress.ofNat (UInt256.ofNat a.val).toNat = a := by
    intro a
    have h1 : (UInt256.ofNat a.val).toNat = a.val :=
      UInt256.toNat_ofNat_of_lt (lt_of_lt_of_le a.isLt
        (show AccountAddress.size ≤ UInt256.size from by decide))
    rw [h1]; apply Fin.ext
    simp only [AccountAddress.ofNat, Fin.ofNat]
    exact Nat.mod_eq_of_lt a.isLt
  have hbytes : biteIlkBytes I = EVM.Word.toBytesBE (biteIlkWord I) := by
    have hlen32 : (biteIlkBytes I).length = 32 := by
      simp only [biteIlkBytes, List.length_take, List.length_drop]
      have htlen : I.calldata.toList.length = I.calldata.size := by
        rw [byteArray_toList_eq, Array.length_toList]; rfl
      rw [htlen]; omega
    have hword : ABI.bytesToWord (biteIlkBytes I) = biteIlkWord I := by
      simpa [biteIlkBytes, biteIlkWord] using
        (decode_word_at_eq_any I.calldata 4 (by simpa using hsz36))
    have hto := toBytesBE_bytesToWord_of_length (bs := biteIlkBytes I) hlen32
    rw [hword] at hto; exact hto.symm
  have uminEq : ∀ a b : UInt256,
      (if UInt256.gt a b = ⟨0⟩ then a else b) = umin a b := by
    intro a b; unfold umin
    by_cases h : a.toNat ≤ b.toNat
    · rw [if_pos (ugt_zero h), if_pos h]
    · rw [if_neg (by rw [ugt_one (by omega)]; decide), if_neg h]
  have hwad : wadU = ⟨1000000000000000000⟩ := by native_decide
  have hsl : (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨255⟩).toNat =
      57896044618658097711785492504343953926634992332820282019728792003956564819968 := by
    native_decide
  have storeFlat : ∀ (ev : EVM.State) (aa : AccountAddress) (k v : UInt256),
      Solm.EVM.storageStore ev aa k v =
        { ev with accountMap := sstoreAccountMap aa ev.accountMap k v } := by
    intro ev aa k v
    simp only [Solm.EVM.storageStore, sstoreAccountMap, State.lookupAccount]
    cases h : ev.accountMap.find? aa with
    | none => simp [Option.option]
    | some acc => simp [Option.option, State.setAccount, Account.updateStorage]
  have hbr : ∀ (o : ByteArray) (k : ℕ), k + 32 ≤ o.size →
      ABI.bytesToWord ((o.toList.drop k).take 32) =
        UInt256.ofNat (fromByteArrayBigEndian (o.extract k (k + 32))) := by
    intro o k h
    rw [decode_word_at_eq_any o k h, uInt256OfByteArray_eq]
    congr 1; unfold fromByteArrayBigEndian; congr 1
    rw [byteArray_toList_eq (o.readBytes k 32),
      readBytes_at_toList_any o k h,
      byteArray_toList_eq (o.extract k (k + 32)),
      ByteArray.data_extract, Array.toList_extract,
      List.extract_eq_take_drop]
    simp
  obtain ⟨σs, As, σus, Aus, hIlksSolm, hUrnsSolm, hAmEq, hvatCodeIlkS⟩ :=
    catBiteMapUrns hAccounts hdepthNe hUrnsVatCode hIlksCall hUrnsCall
  have slotEqUS : ∀ s : UInt256, solcSlotWord σus I s = solcSlotWord σu I s := by
    intro s; simp only [solcSlotWord]
    rw [accountMapEquiv_storage_findD hAmEq I.codeOwner s ⟨0⟩]
  set eUrnE := { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
    accountMap := σu, substate := Au, createdAccounts := cAu } with heUrnEdef
  set eUrnS := { initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I with
    accountMap := σus, substate := Aus, createdAccounts := cAu } with heUrnSdef
  have hEqU : EVMStateEquiv eUrnE eUrnS := ⟨rfl, rfl, hAmEq⟩
  have heUEam : eUrnE.accountMap = σu := rfl
  have heUEee : eUrnE.executionEnv = I := rfl
  have heUSam : eUrnS.accountMap = σus := rfl
  have heUSee : eUrnS.executionEnv = I := rfl
  have hboxB : biteBoxW eUrnE = solcSlotWord σu I ⟨5⟩ := by
    simp only [biteBoxW, catSlotWord, heUEam, heUEee]
  have hlitB : biteLitW eUrnE = solcSlotWord σu I ⟨6⟩ := by
    simp only [biteLitW, catSlotWord, heUEam, heUEee]
  have hchopB : biteChopW I eUrnE = milkChop := by
    rw [hmilkChopDef]
    simp only [biteChopW, catSlotWord, heUEam, heUEee, biteChopSlot,
      biteFlipSlot_eq hsz36]
  have hdunkB : biteDunkW I eUrnE = milkDunk := by
    rw [hmilkDunkDef]
    simp only [biteDunkW, catSlotWord, heUEam, heUEee, biteDunkSlot,
      biteFlipSlot_eq hsz36]
  have hroomB : biteRoomV eUrnE = room := by
    rw [hroomDef]
    simp only [biteRoomV, biteBoxW, biteLitW, catSlotWord, heUEam, heUEee]
  have hdunkroomB : biteDunkRoomV I eUrnE = dunkRoom := by
    rw [hdunkRoomDef, uminEq milkDunk room]
    simp only [biteDunkRoomV, hdunkB, hroomB]
  have hdartvB : biteDartV I eUrnE iRate art = dart := by
    have hcand : biteDartCandV I eUrnE iRate = dartCandidate := by
      simp only [biteDartCandV, biteDartDenomV, biteDunkRoomWadV,
        hchopB, hdunkroomB, hwad, hdartCandDef, hdartDenomDef,
        hdunkRoomWadDef]
      rfl
    rw [hdartDef, uminEq art dartCandidate]
    simp only [biteDartV, hcand]
  have hdinkvB : biteDinkV I eUrnE iRate art ink = dink := by
    have hcand : biteDinkCandV I eUrnE iRate art ink = dinkCandidate := by
      simp only [biteDinkCandV, biteInkDartV, hdartvB, hdinkCandDef,
        hinkDartDef]
      rfl
    rw [hdinkDef, uminEq ink dinkCandidate]
    simp only [biteDinkV, hcand]
  have hdartrateBE : biteDartRateV I eUrnE iRate art = dartRate := by
    rw [hdartRateDef]; simp only [biteDartRateV, hdartvB]; rfl
  have htabB : biteTabV I eUrnE iRate art = tab := by
    rw [htabDef, htabBaseDef]
    simp only [biteTabV, biteTabBaseV, hdartrateBE, hchopB, hwad]; rfl
  have hIlksDec : config.externalABI.decode? "ilks" o' =
      some [bw (UInt256.ofNat (fromByteArrayBigEndian (o'.extract 0 32))),
        bw iRate, bw iSpot,
        bw (UInt256.ofNat (fromByteArrayBigEndian (o'.extract 96 128))),
        bw iDust] := by
    have h := catBiteIlksDecode_ok hilkslen
    rw [hbr o' 0 (by omega), hbr o' 32 (by omega), hbr o' 64 (by omega),
      hbr o' 96 (by omega), hbr o' 128 (by omega)] at h
    rw [hiRate, hiSpot, hiDustDef]; exact h
  have hUrnsDec : config.externalABI.decode? "urns" ou =
      some [bw ink, bw art] := by
    have h := catBiteUrnsDecode_ok hurnslen
    rw [hbr ou 0 (by omega), hbr ou 32 (by omega)] at h
    rw [hink, hart]; exact h
  obtain ⟨AG, hGrabCall'⟩ :=
    biteTypedCallZeroSetSubstate hGrabCall
      (by simpa [initState] using hdepthNe) Au
  obtain ⟨σgs, Ags, hGrabSolm, hEqGrab⟩ :=
    catBiteMapCall hEqU hGrabCall' hdepthNe
  set eGrabE := { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
    accountMap := σg, substate := AG, createdAccounts := cAg } with heGrabEdef
  set eGrabS := { initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I with
    accountMap := σgs, substate := Ags, createdAccounts := cAg } with heGrabSdef
  have heGEam : eGrabE.accountMap = σg := rfl
  have heGEee : eGrabE.executionEnv = I := rfl
  have htgtU : EVM.address (biteVatAddr eUrnS).val =
      AccountAddress.ofUInt256 ((solcSlotWord σu I ⟨3⟩).land biteAddrMaskWord) := by
    rw [← biteVatAddr_eq_of_equiv hEqU, addrId,
      accountAddress_ofUInt256_eq_ofNat_toNat, hmask]
    simp only [biteVatAddr, catSlotWord, heUEam, heUEee]
  have h1 : biteIlkVal I =
      Value.fixedBytes bytes32Width (EVM.Word.toBytesBE (biteIlkWord I)) := by
    simp only [biteIlkVal, hbytes]
  have h2 : biteUrnVal I = Value.address (AccountAddress.ofNat
      (biteAddrMaskWord.land
        (biteAddrMaskWord.land (calldataWord I.calldata 36))).toNat) := by
    rw [hurn]
    simp only [biteUrnVal, biteUrnWord, biteUrnAddr, hAddrRT]
  have h3 : (eUrnS.executionEnv.codeOwner : AccountAddress) =
      AccountAddress.ofNat (UInt256.ofNat I.codeOwner.val).toNat := by
    rw [heUSee]; exact (hAddrRT I.codeOwner).symm
  have h4 : biteVowAddrV eUrnS = AccountAddress.ofNat
      (biteAddrMaskWord.land (solcSlotWord σu I ⟨4⟩)).toNat := by
    rw [← biteVowAddrV_eq_of_equiv hEqU]
    simp only [biteVowAddrV, catSlotWord, heUEam, heUEee, hmask]
    rw [u256_land_comm]
  have hdartvBS : biteDartV I eUrnS iRate art = dart := by
    rw [← biteDartV_eq_of_equiv hEqU]; exact hdartvB
  have hdinkvBS : biteDinkV I eUrnS iRate art ink = dink := by
    rw [← biteDinkV_eq_of_equiv hEqU]; exact hdinkvB
  have hdartrateBS : biteDartRateV I eUrnS iRate art = dart.mul iRate := by
    rw [← biteDartRateV_eq_of_equiv hEqU]
    simp only [biteDartRateV, hdartvB]; rfl
  have htabBS : biteTabV I eUrnS iRate art = tab := by
    rw [← biteTabV_eq_of_equiv hEqU]; exact htabB
  have hGrabCodeS :
      ¬ Reasoning.Theory.extCodeSizeWord σus
        ((solcSlotWord σus I ⟨3⟩).land biteAddrMaskWord) = ⟨0⟩ := by
    rw [slotEqUS ⟨3⟩, ← extCodeSizeWord_accountMapEquiv hAmEq]
    exact hGrabCode
  rw [hperm, ← htgtU, ← h1, ← h2, ← h3, ← h4, ← hdinkvBS, ← hdartvBS]
    at hGrabSolm
  have hGrabDec : config.externalABI.decode? "grab" og = some [] := by
    simp [config, externalABI, decodeVoid?]
  obtain ⟨AF, hFessCall'⟩ :=
    biteTypedCallZeroSetSubstate hFessCall
      (by simpa [initState] using hdepthNe) AG
  obtain ⟨σfs, Afs, hFessSolm, hEqFess⟩ :=
    catBiteMapCall hEqGrab hFessCall' hdepthNe
  set eFessE := { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
    accountMap := σf, substate := AF, createdAccounts := cAf } with heFessEdef
  set eFessS := { initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I with
    accountMap := σfs, substate := Afs, createdAccounts := cAf } with heFessSdef
  have heFEam : eFessE.accountMap = σf := rfl
  have heFEee : eFessE.executionEnv = I := rfl
  have htgtF : EVM.address (biteVowAddrV eGrabS).val =
      AccountAddress.ofUInt256 (biteAddrMaskWord.land (solcSlotWord σg I ⟨4⟩)) := by
    rw [← biteVowAddrV_eq_of_equiv hEqGrab, addrId,
      accountAddress_ofUInt256_eq_ofNat_toNat, hmask, u256_land_comm]
    simp only [biteVowAddrV, catSlotWord, heGEam, heGEee]
  have hfessArg : bw (biteDartRateV I eUrnS iRate art) =
      Value.int (Int.ofNat (dart.mul iRate).toNat) := by rw [hdartrateBS]
  rw [hperm, ← htgtF, ← hfessArg] at hFessSolm
  have hFessDec : config.externalABI.decode? "fess" ofb = some [] := by
    simp [config, externalABI, decodeVoid?]
  have hvowCodeS : 0 < (UInt256.ofNat
      ((eGrabS.lookupAccount (biteVowAddrV eGrabS)).option 0
        (fun acc => acc.code.size))).toNat := by
    rw [← biteVowAddrV_eq_of_equiv hEqGrab,
      ← biteCodeW_eq_of_equiv (biteVowAddrV eGrabE) hEqGrab]
    have haddr : biteVowAddrV eGrabE =
        AccountAddress.ofUInt256 ((solcSlotWord σg I ⟨4⟩).land solcAddrMask) := by
      rw [accountAddress_ofUInt256_eq_ofNat_toNat]
      simp only [biteVowAddrV, catSlotWord, heGEam, heGEee]
    rw [haddr]
    refine codePos eGrabE ((solcSlotWord σg I ⟨4⟩).land solcAddrMask) ?_
    rw [heGEam, u256_land_comm, ← hmask]; exact hFessCode
  have hlitFB : biteLitW eFessE = solcSlotWord σf I ⟨6⟩ := by
    simp only [biteLitW, catSlotWord, heFEam, heFEee]
  have hlitternewE : biteLitterNewV I eUrnE eFessE iRate art = litterNew := by
    rw [hlitterNewDef]
    simp only [biteLitterNewV, hlitFB, htabB]
  set hLitVal := biteLitterNewV I eUrnS eFessS iRate art with hLitValDef
  have hLitValEq : litterNew = hLitVal :=
    hlitternewE.symm.trans (biteLitterNewV_eq_of_equiv hEqU hEqFess iRate art)
  obtain ⟨AK, hKickCall'⟩ :=
    biteTypedCallZeroSetSubstate hKickCall
      (by simpa [initState] using hdepthNe) AF
  rw [hLitValEq] at hKickCall'
  have hStateLit : EVMStateEquiv
      { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
        accountMap := sstoreAccountMap I.codeOwner σf ⟨6⟩ hLitVal,
        substate := AF, createdAccounts := cAf }
      { initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I with
        accountMap := sstoreAccountMap I.codeOwner σfs ⟨6⟩ hLitVal,
        substate := Afs, createdAccounts := cAf } :=
    ⟨rfl, rfl,
      accountMapEquiv_sstoreAccountMap I.codeOwner ⟨6⟩ hLitVal hEqFess.accountMap⟩
  obtain ⟨σks, Aks, hKickSolm, _hEqKick⟩ :=
    catBiteMapCall hStateLit hKickCall' hdepthNe
  set eLitS := { initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I with
    accountMap := sstoreAccountMap I.codeOwner σfs ⟨6⟩ hLitVal,
    substate := Afs, createdAccounts := cAf } with heLitSdef
  have heLSam : eLitS.accountMap =
    sstoreAccountMap I.codeOwner σfs ⟨6⟩ hLitVal := rfl
  have heLSee : eLitS.executionEnv = I := rfl
  have hflipAddrS : biteFlipAddrV I eUrnS =
      AccountAddress.ofUInt256 (biteAddrMaskWord.land flipW) := by
    rw [← biteFlipAddrV_eq_of_equiv hEqU,
      accountAddress_ofUInt256_eq_ofNat_toNat, hflipWDef, hmask]
    simp only [biteFlipAddrV, catSlotWord, heUEam, heUEee,
      biteFlipSlot_eq hsz36]
    rw [solcAddrMask_clean_left
      (by rw [u256_land_comm]; exact solcAddrMask_result_canonical _),
      u256_land_comm]
  have htgtK : EVM.address (biteFlipAddrV I eUrnS).val =
      AccountAddress.ofUInt256 (biteAddrMaskWord.land flipW) := by
    rw [addrId]; exact hflipAddrS
  have hexp : UInt256.exp (⟨256⟩ : UInt256) ⟨0⟩ = ⟨1⟩ := by native_decide
  have hdiv1 : ∀ y : UInt256, UInt256.div y ⟨1⟩ = y := fun y => by
    apply u256_inj
    rw [udiv_toNat, show (⟨1⟩ : UInt256).toNat = 1 from by native_decide,
      Nat.div_one]
  have hvowW : ∀ σx : AccountMap,
      UInt256.land (solcSlotWord σx I ⟨4⟩) solcAddrMask = seg8VowM σx I := by
    intro σx
    simp only [seg8VowM, hmask, hexp, hdiv1]
    rw [solcAddrMask_clean_left
      (by rw [u256_land_comm]; exact solcAddrMask_result_canonical _),
      u256_land_comm]
  have hslot4 :
      solcSlotWord (sstoreAccountMap I.codeOwner σfs ⟨6⟩ hLitVal) I ⟨4⟩ =
      solcSlotWord (sstoreAccountMap I.codeOwner σf ⟨6⟩ hLitVal) I ⟨4⟩ := by
    simp only [solcSlotWord]
    exact (accountMapEquiv_storage_findD
      (accountMapEquiv_sstoreAccountMap I.codeOwner ⟨6⟩ hLitVal hEqFess.accountMap)
      I.codeOwner ⟨4⟩ ⟨0⟩).symm
  have hvowLit : biteVowAddrV eLitS =
      AccountAddress.ofNat
        (seg8VowM (sstoreAccountMap I.codeOwner σf ⟨6⟩ hLitVal) I).toNat := by
    simp only [biteVowAddrV, catSlotWord, heLSam, heLSee, hmask]
    rw [hslot4, hvowW]
  simp only [seg8KickArgs, seg8UrnM] at hKickSolm
  rw [hzk, hperm, ← htgtK, ← h2, ← hvowLit, ← htabBS, ← hdinkvBS] at hKickSolm
  have hflipCodeS : 0 < (UInt256.ofNat
      ((eLitS.lookupAccount (biteFlipAddrV I eUrnS)).option 0
        (fun acc => acc.code.size))).toNat := by
    rw [hflipAddrS]
    refine codePos eLitS (biteAddrMaskWord.land flipW) ?_
    rw [heLSam, ← extCodeSizeWord_accountMapEquiv
        (accountMapEquiv_sstoreAccountMap I.codeOwner ⟨6⟩ hLitVal
          hEqFess.accountMap), ← hLitValEq]
    exact hKickCode
  have hlive' : catSlotWord ⟨2⟩ eUrnS.accountMap eUrnS.executionEnv = ⟨1⟩ := by
    rw [← biteSlotEqOfEquiv hEqU ⟨2⟩]; exact hlive
  have hLitStoreS :
      storageLocStore eFessS (wordLoc ⟨6⟩)
        (.int (Int.ofNat hLitVal.toNat)) = some eLitS := by
    have h := storageLocStore_uint256 eFessS ⟨6⟩ hLitVal
    rw [storeFlat] at h
    exact h
  have hKickDec : config.externalABI.decode? "kick" ok = none := catBiteKickDecode_none hshort
  refine catBiteKickReturnDecodeShortLeaf hcode hdispatch hdecode rd2532 hstatus hshort hoszk
    hMloadFreeValue hMloadFreeCost hMloadFreeAw hov3 ?_
  refine catBiteSourceKickDecodeRevert hwv
    (catBiteVatCodePos_of_uniswap hAccounts hvatCode) hIlksSolm hIlksDec
    hvatCodeIlkS hUrnsSolm hUrnsDec hlive' hsz36 hfitInkSpot hfitArtRate
    hspotPos (hposNe iRate hRatePos) hunsafe ?_ ?_ ?_ ?_ ?_
    (hposNe art hArtPos) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hGrabSolm hGrabDec
    hvowCodeS hFessSolm hFessDec hLitStoreS hflipCodeS hKickSolm hKickDec
  · rw [← biteLitW_eq_of_equiv hEqU, ← biteBoxW_eq_of_equiv hEqU, hlitB, hboxB]
    exact hlitterbox
  · rw [← biteRoomV_eq_of_equiv hEqU, hroomB]; exact hroomdust
  · rw [← biteDunkRoomV_eq_of_equiv hEqU, hdunkroomB, hwad, Nat.mul_comm]
    exact hFitWad
  · rw [← biteChopW_eq_of_equiv hEqU, hchopB]; exact hposNe milkChop hChopPos
  · rw [← biteDartV_eq_of_equiv hEqU, hdartvB, Nat.mul_comm]; exact hFitInkDart
  · rw [← biteDartV_eq_of_equiv hEqU, hdartvB]; exact hDartPos
  · rw [← biteDinkV_eq_of_equiv hEqU, hdinkvB]; exact hDinkPos
  · rw [← biteDartV_eq_of_equiv hEqU, hdartvB]; simp only [int256Limit]
    exact Int.ofNat_le.mpr (hDartLim.trans_eq hsl)
  · rw [← biteDinkV_eq_of_equiv hEqU, hdinkvB]; simp only [int256Limit]
    exact Int.ofNat_le.mpr (hDinkLim.trans_eq hsl)
  · have haddr : biteVatAddr eUrnS =
        AccountAddress.ofUInt256 (catBiteVatTargetWord σus I) := by
      rw [accountAddress_ofUInt256_eq_ofNat_toNat]
      simp only [biteVatAddr, catBiteVatTargetWord, catAddressReturnWord,
        catSlotWord, heUSam, heUSee]
    rw [haddr]
    refine codePos eUrnS (catBiteVatTargetWord σus I) ?_
    rw [heUSam, show catBiteVatTargetWord σus I =
          (solcSlotWord σus I ⟨3⟩).land biteAddrMaskWord from by
        simp only [catBiteVatTargetWord, catAddressReturnWord, catSlotWord,
          hmask]]
    exact hGrabCodeS
  · rw [← biteDartV_eq_of_equiv hEqU, hdartvB, Nat.mul_comm]; exact hRateFit
  · rw [← biteDartRateV_eq_of_equiv hEqU, ← biteChopW_eq_of_equiv hEqU,
      hdartrateBE, hchopB, Nat.mul_comm]; exact hChopFit
  · rw [← biteLitW_eq_of_equiv hEqFess, ← biteTabV_eq_of_equiv hEqU,
      hlitFB, htabB]; exact hLitFit


set_option maxHeartbeats 4000000 in
/-- **kick return-decode-short branch (walk wrapper).** Same conclusion as `catBiteRevertKickDecode`
but the three free-ptr `MLOAD` facts are built HERE (own budget) from the raw free-ptr read
`hread64` + memory bound `hpmem`, with `baseMem`/`kvow` kept generic so the walk supplies `rd2532`
by cheap metavar assignment (no `whnf` of the litter-SSTORE vow read / the calldata overlay). -/
theorem catBiteRevertKickDecodeW {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {σ' σu σg σf σk : AccountMap} {A' Au Ag Af Ak : Substate}
    {cA' cAu cAg cAf cAk : Batteries.RBSet AccountAddress compare} {o' ou og ofb ok : ByteArray}
    {baseMem : ByteArray} {p kvow : UInt256}
    {R3 : List UInt256} {k3 C3 : ℕ} {zk : Bool}
    {flipW dartRate tabBase tab litterNew : UInt256}
    {art ink iSpot iRate iDust room milkDunk milkChop dunkRoom dunkRoomWad
      dartDenomRate dartCandidate dart inkDart dinkCandidate dink : UInt256}
    (hcode : I.code = catBytecode)
    (hdispatch : dispatchMsg contract I.calldata = some biteTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (biteTransition.params.map Param.name)
        (transitionSignature biteTransition).paramTypes I.calldata = some (biteLocals I))
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hwv : I.weiValue = ⟨0⟩) (hperm : I.perm = true) (hsz36 : 36 ≤ I.calldata.size)
    (hdepth : (I.depth : ℕ) < 1024)
    (hurn : biteAddrMaskWord.land (biteAddrMaskWord.land (calldataWord I.calldata 36)) = biteUrnWord I)
    (hilkslen : 160 ≤ o'.size) (hurnslen : 64 ≤ ou.size)
    (hlive : catSlotWord ⟨2⟩ σu I = ⟨1⟩)
    (hvatCode : ¬ Reasoning.Theory.extCodeSizeWord σ_evm (catBiteVatTargetWord σ_evm I) = ⟨0⟩)
    (hUrnsVatCode :
      ¬ Reasoning.Theory.extCodeSizeWord σ' ((catSlotWord ⟨3⟩ σ' I).land biteAddrMaskWord) = ⟨0⟩)
    (hGrabCode :
      ¬ Reasoning.Theory.extCodeSizeWord σu ((solcSlotWord σu I ⟨3⟩).land biteAddrMaskWord) = ⟨0⟩)
    (hFessCode :
      ¬ Reasoning.Theory.extCodeSizeWord σg (biteAddrMaskWord.land (solcSlotWord σg I ⟨4⟩)) = ⟨0⟩)
    (hKickCode :
      ¬ Reasoning.Theory.extCodeSizeWord (sstoreAccountMap I.codeOwner σf ⟨6⟩ litterNew)
        (biteAddrMaskWord.land flipW) = ⟨0⟩)
    (hIlksCall :
      typedCallViaEVM config (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        (AccountAddress.ofUInt256 (catBiteVatTargetWord σ_evm I)) "ilks" 0 [biteIlkVal I]
        (true, { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
                  accountMap := σ', substate := A', createdAccounts := cA' }, o') false)
    (hUrnsCall :
      typedCallViaEVM config
        { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
            accountMap := σ', createdAccounts := cA' }
        (AccountAddress.ofUInt256 ((catSlotWord ⟨3⟩ σ' I).land biteAddrMaskWord)) "urns" 0
        [biteIlkVal I, biteUrnVal I]
        (true, { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
                  accountMap := σu, substate := Au, createdAccounts := cAu }, ou) false)
    (hGrabCall :
      typedCallViaEVM config
        { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
            accountMap := σu, createdAccounts := cAu }
        (AccountAddress.ofUInt256 ((solcSlotWord σu I ⟨3⟩).land biteAddrMaskWord)) "grab" 0
        [Value.fixedBytes bytes32Width (EVM.Word.toBytesBE (biteIlkWord I)),
          Value.address (AccountAddress.ofNat
            (biteAddrMaskWord.land (biteAddrMaskWord.land (calldataWord I.calldata 36))).toNat),
          Value.address (AccountAddress.ofNat (UInt256.ofNat I.codeOwner.val).toNat),
          Value.address (AccountAddress.ofNat (biteAddrMaskWord.land (solcSlotWord σu I ⟨4⟩)).toNat),
          Value.int (-Int.ofNat dink.toNat), Value.int (-Int.ofNat dart.toNat)]
        (true, { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
                  accountMap := σg, substate := Ag, createdAccounts := cAg }, og) I.perm)
    (hFessCall :
      typedCallViaEVM config
        { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
            accountMap := σg, createdAccounts := cAg }
        (AccountAddress.ofUInt256 (biteAddrMaskWord.land (solcSlotWord σg I ⟨4⟩))) "fess" 0
        [Value.int (Int.ofNat (dart.mul iRate).toNat)]
        (true, { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
                accountMap := σf, substate := Af, createdAccounts := cAf }, ofb) I.perm)
    (hKickCall :
      typedCallViaEVM config
        { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
            accountMap := sstoreAccountMap I.codeOwner σf ⟨6⟩ litterNew, createdAccounts := cAf }
        (AccountAddress.ofUInt256 (biteAddrMaskWord.land flipW)) "kick" 0
        (seg8KickArgs (sstoreAccountMap I.codeOwner σf ⟨6⟩ litterNew) I
          (biteAddrMaskWord.land (calldataWord I.calldata 36)) tab dink)
        (zk, { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
                accountMap := σk, substate := Ak, createdAccounts := cAk }, ok) I.perm)
    (rd2532 :
      RD catBytecode I (Sat256.ofUInt256 g) (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        ⟨2532⟩
        ((if zk = true then (⟨1⟩ : UInt256) else ⟨0⟩) ::
          (p + ⟨164⟩) :: ⟨891151872⟩ :: (biteAddrMaskWord.land flipW) :: R3)
        (ok.write 0 (kickCalldataMemP p
            (biteAddrMaskWord.land (biteAddrMaskWord.land (calldataWord I.calldata 36))) kvow tab dink
            baseMem)
          p.toNat (min (⟨32⟩ : UInt256) (UInt256.ofNat ok.size)).toNat)
        ⟨17⟩ ok (cAk, σk) k3 C3)
    (hpmem : p.toNat + 164 ≤ baseMem.size)
    (hread64 : baseMem.readWithPadding 64 32 = UInt256.toByteArray p)
    (hp96 : 96 ≤ p.toNat) (hpsz : p.toNat + 164 < UInt256.size)
    (hp160aw : p.toNat + 160 ≤ (⟨17⟩ : UInt256).toNat * 32)
    (hoszk : ok.size < UInt256.size) (hov3 : R3.length + 6 ≤ 1024) (hzk : zk = true)
    (hstatus : (if zk = true then (⟨1⟩ : UInt256) else ⟨0⟩) ≠ ⟨0⟩) (hshort : ok.size < 32)
    (hRateFit : iRate.toNat * dart.toNat < UInt256.size)
    (hflipWDef : flipW = biteAddrMaskWord.land (solcSlotWord σu I (solcMappingSlot ⟨1⟩ (biteIlkWord I))))
    (hdartRateDef : dartRate = dart.mul iRate)
    (htabBaseDef : tabBase = dartRate.mul milkChop)
    (htabDef : tab = tabBase.div ⟨1000000000000000000⟩)
    (hlitterNewDef : litterNew = solcSlotWord σf I ⟨6⟩ + tab)
    (hChopFit : milkChop.toNat * dartRate.toNat < UInt256.size)
    (hLitFit : (solcSlotWord σf I ⟨6⟩).toNat + tab.toNat < UInt256.size)
    (hart : art = UInt256.ofNat (fromByteArrayBigEndian (ou.extract 32 64)))
    (hink : ink = UInt256.ofNat (fromByteArrayBigEndian (ou.extract 0 32)))
    (hiSpot : iSpot = UInt256.ofNat (fromByteArrayBigEndian (o'.extract 64 96)))
    (hiRate : iRate = UInt256.ofNat (fromByteArrayBigEndian (o'.extract 32 64)))
    (hiDustDef : iDust = UInt256.ofNat (fromByteArrayBigEndian (o'.extract 128 160)))
    (hroomDef : room = (solcSlotWord σu I ⟨5⟩).sub (solcSlotWord σu I ⟨6⟩))
    (hmilkDunkDef : milkDunk = solcSlotWord σu I (solcMappingSlot ⟨1⟩ (biteIlkWord I) + ⟨2⟩))
    (hmilkChopDef : milkChop = solcSlotWord σu I (solcMappingSlot ⟨1⟩ (biteIlkWord I) + ⟨1⟩))
    (hdunkRoomDef : dunkRoom = if milkDunk.gt room = ⟨0⟩ then milkDunk else room)
    (hdunkRoomWadDef : dunkRoomWad = dunkRoom.mul ⟨1000000000000000000⟩)
    (hdartDenomDef : dartDenomRate = dunkRoomWad.div iRate)
    (hdartCandDef : dartCandidate = dartDenomRate.div milkChop)
    (hdartDef : dart = if art.gt dartCandidate = ⟨0⟩ then art else dartCandidate)
    (hinkDartDef : inkDart = ink.mul dart)
    (hdinkCandDef : dinkCandidate = inkDart.div art)
    (hdinkDef : dink = if ink.gt dinkCandidate = ⟨0⟩ then ink else dinkCandidate)
    (hspotPos : 0 < iSpot.toNat) (hfitArtRate : art.toNat * iRate.toNat < UInt256.size)
    (hfitInkSpot : ink.toNat * iSpot.toNat < UInt256.size)
    (hunsafe : (ink * iSpot).toNat < (art * iRate).toNat)
    (hlitterbox : (solcSlotWord σu I ⟨6⟩).toNat < (solcSlotWord σu I ⟨5⟩).toNat)
    (hroomdust : iDust.toNat ≤ room.toNat)
    (hRatePos : iRate ≠ ⟨0⟩) (hChopPos : milkChop ≠ ⟨0⟩)
    (hFitWad : (⟨1000000000000000000⟩ : UInt256).toNat * dunkRoom.toNat < UInt256.size)
    (hArtPos : art ≠ ⟨0⟩) (hFitInkDart : dart.toNat * ink.toNat < UInt256.size)
    (hDartPos : 0 < dart.toNat) (hDinkPos : 0 < dink.toNat)
    (hDartLim : dart.toNat ≤ (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨255⟩).toNat)
    (hDinkLim : dink.toNat ≤ (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨255⟩).toNat) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hMloadFreeAw : UInt256.ofNat (MachineState.M (⟨17⟩ : UInt256).toNat 64 32) = ⟨17⟩ := by
    native_decide
  have hMloadFreeValue := catBiteKickPostCallMemP_mload64_short p
    (biteAddrMaskWord.land (biteAddrMaskWord.land (calldataWord I.calldata 36))) kvow tab dink ok
    (aw8 := ⟨17⟩) hp96 hpmem hpsz hshort hread64 hp160aw (by native_decide)
  exact catBiteRevertKickDecode hcode hdispatch hdecode hAccounts hwv hperm hsz36 hdepth hurn
    hilkslen hurnslen hlive hvatCode hUrnsVatCode hGrabCode hFessCode hKickCode hIlksCall
    hUrnsCall hGrabCall hFessCall hKickCall rd2532 hoszk hov3 hzk hstatus hshort
    hMloadFreeValue (catBiteMloadCost0 hMloadFreeAw) hMloadFreeAw hRateFit hflipWDef hdartRateDef
    htabBaseDef htabDef hlitterNewDef hChopFit hLitFit hart hink hiSpot hiRate hiDustDef hroomDef
    hmilkDunkDef hmilkChopDef hdunkRoomDef hdunkRoomWadDef hdartDenomDef hdartCandDef hdartDef
    hinkDartDef hdinkCandDef hdinkDef hspotPos hfitArtRate hfitInkSpot hunsafe hlitterbox hroomdust
    hRatePos hChopPos hFitWad hArtPos hFitInkDart hDartPos hDinkPos hDartLim hDinkLim


set_option maxHeartbeats 2000000 in
/-- **aw-correct reach 1620 → 3762** (the room-`sub(box,litter)` subroutine entry, exposing the
grown active-words ⟨10⟩). Verbatim `catBiteReachSeg6Aw` prefix (which grows aw 9→10 at the dunk
MSTORE @288) but STOPS at pc 3762 instead of stepping the sub-success — for the underflow
(box < litter) divergence. -/
theorem catBiteReachGuardRoomSubAw {cA gh bl σ σ₀ A I} {g : UInt256}
    {cA' : Batteries.RBSet AccountAddress compare} {σ' : AccountMap}
    {art ink iDust iSpot iRate urn ilk fp q : UInt256} {R : List UInt256}
    {mem o : ByteArray} {k C : ℕ}
    (rd : RD catBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1620⟩
      (art :: ink :: iDust :: iSpot :: iRate :: ⟨0⟩ :: urn :: ilk :: R) mem ⟨9⟩ o (cA', σ') k C)
    (hqNat : q.toNat = 224)
    (hFp : (if (⟨64⟩ : UInt256).toNat ≥ mem.size ∨ (⟨64⟩ : UInt256) ≥ (⟨9⟩ : UInt256) * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32)))
        = fp)
    (hQ : (if (⟨64⟩ : UInt256).toNat ≥ (catBiteScratchMem mem fp ilk).size
          ∨ (⟨64⟩ : UInt256) ≥ (⟨9⟩ : UInt256) * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat (fromByteArrayBigEndian
        ((catBiteScratchMem mem fp ilk).readWithPadding (⟨64⟩ : UInt256).toNat 32)))
        = q)
    (hKec : (catBiteScratchMem mem fp ilk).readWithPadding 0 64 =
        UInt256.toByteArray ilk ++ UInt256.toByteArray ⟨1⟩)
    (hawFp : fp.toNat + 96 ≤ (⟨9⟩ : UInt256).toNat * 32)
    (hfpsz : fp.toNat + 96 < UInt256.size)
    (hqsz : q.toNat + 96 < UInt256.size)
    (hov : R.length + 20 ≤ 1024) :
    ∃ k' C', RD catBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨3762⟩
      (solcSlotWord σ' I ⟨6⟩ :: solcSlotWord σ' I ⟨5⟩ :: ⟨1708⟩ ::
        ⟨0⟩ :: ⟨0⟩ :: q :: art :: ink :: iDust :: iSpot :: iRate :: ⟨0⟩ :: urn :: ilk :: R)
      (catBiteMilkMem mem fp ilk q
        (UInt256.land biteAddrMaskWord (solcSlotWord σ' I (solcMappingSlot ⟨1⟩ ilk)))
        (solcSlotWord σ' I (solcMappingSlot ⟨1⟩ ilk + ⟨1⟩))
        (solcSlotWord σ' I (solcMappingSlot ⟨1⟩ ilk + ⟨2⟩)))
      ⟨10⟩ o (cA', σ') k' C' := by
  have h9 : (⟨9⟩ : UInt256).toNat = 9 := by native_decide
  -- offset arithmetic
  have e32fp : (⟨32⟩ + fp).toNat = fp.toNat + 32 := uadd_lit32_toNat fp (by omega)
  have e64fp : (⟨32⟩ + (⟨32⟩ + fp)).toNat = fp.toNat + 64 := by
    rw [uadd_lit32_toNat _ (by omega)]; omega
  have eq32 : (q + ⟨32⟩).toNat = q.toNat + 32 := uadd_word_lit32_toNat q (by omega)
  have eq64 : (q + ⟨64⟩).toNat = q.toNat + 64 := by
    rw [uadd_toNat, show (⟨64⟩ : UInt256).toNat = 64 from by decide, Nat.mod_eq_of_lt (by omega)]
  -- active-words invariance witnesses (all within aw=9 EXCEPT the dunk, handled by growth)
  have hM0 : UInt256.ofNat (MachineState.M (⟨9⟩ : UInt256).toNat 0 32) = ⟨9⟩ := catBiteAwMInv32 ⟨9⟩ (by omega)
  have hM32 : UInt256.ofNat (MachineState.M (⟨9⟩ : UInt256).toNat 32 32) = ⟨9⟩ := catBiteAwMInv32 ⟨9⟩ (by omega)
  have hM64 : UInt256.ofNat (MachineState.M (⟨9⟩ : UInt256).toNat 64 32) = ⟨9⟩ := catBiteAwMInv32 ⟨9⟩ (by omega)
  have hMfp : UInt256.ofNat (MachineState.M (⟨9⟩ : UInt256).toNat fp.toNat 32) = ⟨9⟩ := catBiteAwMInv32 ⟨9⟩ (by omega)
  have hM32fp : UInt256.ofNat (MachineState.M (⟨9⟩ : UInt256).toNat (⟨32⟩ + fp).toNat 32) = ⟨9⟩ :=
    catBiteAwMInv32 ⟨9⟩ (by omega)
  have hM64fp : UInt256.ofNat (MachineState.M (⟨9⟩ : UInt256).toNat (⟨32⟩ + (⟨32⟩ + fp)).toNat 32) = ⟨9⟩ :=
    catBiteAwMInv32 ⟨9⟩ (by omega)
  have hMq : UInt256.ofNat (MachineState.M (⟨9⟩ : UInt256).toNat q.toNat 32) = ⟨9⟩ := catBiteAwMInv32 ⟨9⟩ (by omega)
  have hMq32 : UInt256.ofNat (MachineState.M (⟨9⟩ : UInt256).toNat (q + ⟨32⟩).toNat 32) = ⟨9⟩ :=
    catBiteAwMInv32 ⟨9⟩ (by omega)
  have hMkec : UInt256.ofNat (MachineState.M (⟨9⟩ : UInt256).toNat 0 64) = ⟨9⟩ := catBiteAwMInv64 ⟨9⟩ (by omega)
  have hmask0 : UInt256.land (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩) ⟨0⟩ = ⟨0⟩ :=
    by native_decide
  have hDunkOff : (q + ⟨64⟩).toNat = 288 := by rw [eq64, hqNat]
  -- 1620 → 3818 (call the 96-byte allocator)
  have rd1621 := rd.jumpdest (by native_decide) (by evm_ov)
  have rd1624 := rd1621.push2 ⟨1628⟩ (by native_decide) (by evm_ov)
  have rd1627 := rd1624.push2 ⟨3818⟩ (by native_decide) (by evm_ov)
  have rd3818 := rd1627.jump (by native_decide) (by jump_dest) (by evm_ov)
  have rd3819 := rd3818.jumpdest (by native_decide) (by evm_ov)
  have rd3821 := rd3819.push1 ⟨64⟩ (by native_decide) (by evm_ov)
  have rd3822 := RD.mload 0 fp ⟨9⟩ rd3821 (by native_decide) (catBiteMloadCost0 hM64) hFp hM64
    (by evm_ov)
  have rd3823 := rd3822.dup1 (by native_decide) (by evm_ov)
  have rd3825 := rd3823.push1 ⟨96⟩ (by native_decide) (by evm_ov)
  have rd3826 := rd3825.add (by native_decide) (by evm_ov)
  have rd3828 := rd3826.push1 ⟨64⟩ (by native_decide) (by evm_ov)
  have rd3829 := RD.mstore 0 ((UInt256.toByteArray (⟨96⟩ + fp)).write 0 mem 64 32) ⟨9⟩ rd3828
    (by native_decide) (catBiteMstoreCost0 hM64) (by rfl) hM64 (by evm_ov)
  have rd3830 := rd3829.dup1 (by native_decide) (by evm_ov)
  have rd3832 := rd3830.push1 ⟨0⟩ (by native_decide) (by evm_ov)
  have rd3834 := rd3832.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  have rd3836 := rd3834.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  have rd3838 := rd3836.push1 ⟨160⟩ (by native_decide) (by evm_ov)
  have rd3839 := rd3838.shl (by native_decide) (by evm_ov)
  have rd3840 := rd3839.sub (by native_decide) (by evm_ov)
  have rd3841 := rd3840.and (by native_decide) (by evm_ov)
  rw [hmask0] at rd3841
  have rd3842 := rd3841.dup2 (by native_decide) (by evm_ov)
  have rd3843 := RD.mstore 0 ((UInt256.toByteArray ⟨0⟩).write 0
      ((UInt256.toByteArray (⟨96⟩ + fp)).write 0 mem 64 32) fp.toNat 32) ⟨9⟩ rd3842
    (by native_decide) (catBiteMstoreCost0 hMfp) (by rfl) hMfp (by evm_ov)
  have rd3845 := rd3843.push1 ⟨32⟩ (by native_decide) (by evm_ov)
  have rd3846 := rd3845.add (by native_decide) (by evm_ov)
  have rd3848 := rd3846.push1 ⟨0⟩ (by native_decide) (by evm_ov)
  have rd3849 := rd3848.dup2 (by native_decide) (by evm_ov)
  have rd3850 := RD.mstore 0 ((UInt256.toByteArray ⟨0⟩).write 0
      ((UInt256.toByteArray ⟨0⟩).write 0
        ((UInt256.toByteArray (⟨96⟩ + fp)).write 0 mem 64 32) fp.toNat 32)
      (⟨32⟩ + fp).toNat 32) ⟨9⟩ rd3849
    (by native_decide) (catBiteMstoreCost0 hM32fp) (by rfl) hM32fp (by evm_ov)
  have rd3852 := rd3850.push1 ⟨32⟩ (by native_decide) (by evm_ov)
  have rd3853 := rd3852.add (by native_decide) (by evm_ov)
  have rd3855 := rd3853.push1 ⟨0⟩ (by native_decide) (by evm_ov)
  have rd3856 := rd3855.dup2 (by native_decide) (by evm_ov)
  have rd3857 := RD.mstore 0 (catBiteHelperMem mem fp) ⟨9⟩ rd3856
    (by native_decide) (catBiteMstoreCost0 hM64fp) (by rfl) hM64fp (by evm_ov)
  have rd3858 := rd3857.pop (by native_decide) (by evm_ov)
  have rd3859 := rd3858.swap1 (by native_decide) (by evm_ov)
  have rd1628 := rd3859.jump (by native_decide) (by jump_dest) (by evm_ov)
  have rd1629 := rd1628.jumpdest (by native_decide) (by evm_ov)
  have rd1630 := rd1629.pop (by native_decide) (by evm_ov)
  have rd1632 := rd1630.push1 ⟨0⟩ (by native_decide) (by evm_ov)
  have rd1633 := rd1632.dup9 (by native_decide) (by evm_ov)
  have rd1634 := rd1633.dup2 (by native_decide) (by evm_ov)
  have rd1635 := RD.mstore 0 ((UInt256.toByteArray ilk).write 0 (catBiteHelperMem mem fp) 0 32)
    ⟨9⟩ rd1634 (by native_decide) (catBiteMstoreCost0 hM0) (by rfl) hM0 (by evm_ov)
  have rd1637 := rd1635.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  have rd1639 := rd1637.push1 ⟨32⟩ (by native_decide) (by evm_ov)
  have rd1640 := rd1639.dup2 (by native_decide) (by evm_ov)
  have rd1641 := rd1640.dup2 (by native_decide) (by evm_ov)
  have rd1642 := RD.mstore 0 (catBiteScratchMem mem fp ilk) ⟨9⟩ rd1641
    (by native_decide) (catBiteMstoreCost0 hM32) (by rfl) hM32 (by evm_ov)
  have rd1644 := rd1642.push1 ⟨64⟩ (by native_decide) (by evm_ov)
  have rd1645 := rd1644.dup1 (by native_decide) (by evm_ov)
  have rd1646 := rd1645.dup5 (by native_decide) (by evm_ov)
  have rd1647 := rd1646.keccak256 0 (solcMappingSlot ⟨1⟩ ilk) ⟨9⟩ (by native_decide)
    (catBiteKeccakCost0 hMkec)
    (by simp only [show (⟨0⟩ : UInt256).toNat = 0 from by decide,
      show (⟨64⟩ : UInt256).toNat = 64 from by decide, hKec]; exact mappingSlot_single ilk ⟨1⟩)
    hMkec (by evm_ov)
  have rd1648 := rd1647.dup2 (by native_decide) (by evm_ov)
  have rd1649 := RD.mload 0 q ⟨9⟩ rd1648 (by native_decide) (catBiteMloadCost0 hM64) hQ hM64
    (by evm_ov)
  have rd1651 := rd1649.push1 ⟨96⟩ (by native_decide) (by evm_ov)
  have rd1652 := rd1651.dup2 (by native_decide) (by evm_ov)
  have rd1653 := rd1652.add (by native_decide) (by evm_ov)
  have rd1654 := rd1653.dup4 (by native_decide) (by evm_ov)
  have rd1655 := RD.mstore 0 ((UInt256.toByteArray (q + ⟨96⟩)).write 0
      (catBiteScratchMem mem fp ilk) 64 32) ⟨9⟩ rd1654
    (by native_decide) (catBiteMstoreCost0 hM64) (by rfl) hM64 (by evm_ov)
  have rd1656 := rd1655.dup2 (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd1657⟩ := rd1656.sload (by native_decide) (by evm_ov)
  have rd1659 := rd1657.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  have rd1661 := rd1659.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  have rd1663 := rd1661.push1 ⟨160⟩ (by native_decide) (by evm_ov)
  have rd1664 := rd1663.shl (by native_decide) (by evm_ov)
  have rd1665 := rd1664.sub (by native_decide) (by evm_ov)
  have rd1666 := rd1665.and (by native_decide) (by evm_ov)
  have rd1667 := rd1666.dup2 (by native_decide) (by evm_ov)
  have rd1668 := RD.mstore 0 ((UInt256.toByteArray
      (UInt256.land biteAddrMaskWord (solcSlotWord σ' I (solcMappingSlot ⟨1⟩ ilk)))).write 0
      ((UInt256.toByteArray (q + ⟨96⟩)).write 0 (catBiteScratchMem mem fp ilk) 64 32) q.toNat 32)
    ⟨9⟩ rd1667 (by native_decide) (catBiteMstoreCost0 hMq) (by rfl) hMq (by evm_ov)
  have rd1669 := rd1668.swap4 (by native_decide) (by evm_ov)
  have rd1670 := rd1669.dup2 (by native_decide) (by evm_ov)
  have rd1671 := rd1670.add (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd1672⟩ := rd1671.sload (by native_decide) (by evm_ov)
  have rd1673 := rd1672.swap3 (by native_decide) (by evm_ov)
  have rd1674 := rd1673.dup5 (by native_decide) (by evm_ov)
  have rd1675 := rd1674.add (by native_decide) (by evm_ov)
  have rd1676 := rd1675.swap3 (by native_decide) (by evm_ov)
  have rd1677 := rd1676.swap1 (by native_decide) (by evm_ov)
  have rd1678 := rd1677.swap3 (by native_decide) (by evm_ov)
  have rd1679 := RD.mstore 0 ((UInt256.toByteArray
      (solcSlotWord σ' I (solcMappingSlot ⟨1⟩ ilk + ⟨1⟩))).write 0
      ((UInt256.toByteArray
        (UInt256.land biteAddrMaskWord (solcSlotWord σ' I (solcMappingSlot ⟨1⟩ ilk)))).write 0
        ((UInt256.toByteArray (q + ⟨96⟩)).write 0 (catBiteScratchMem mem fp ilk) 64 32) q.toNat 32)
      (q + ⟨32⟩).toNat 32) ⟨9⟩ rd1678
    (by native_decide) (catBiteMstoreCost0 hMq32) (by rfl) hMq32 (by evm_ov)
  have rd1681 := rd1679.push1 ⟨2⟩ (by native_decide) (by evm_ov)
  have rd1682 := rd1681.swap1 (by native_decide) (by evm_ov)
  have rd1683 := rd1682.swap2 (by native_decide) (by evm_ov)
  have rd1684 := rd1683.add (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd1685⟩ := rd1684.sload (by native_decide) (by evm_ov)
  have rd1686 := rd1685.swap1 (by native_decide) (by evm_ov)
  have rd1687 := rd1686.dup3 (by native_decide) (by evm_ov)
  have rd1688 := rd1687.add (by native_decide) (by evm_ov)
  -- the `dunk` MSTORE @q+64=288 GROWS aw 9 → 10 (write [288,320) extends past aw=9's [0,288))
  have rd1689 := RD.mstore 3 (catBiteMilkMem mem fp ilk q
      (UInt256.land biteAddrMaskWord (solcSlotWord σ' I (solcMappingSlot ⟨1⟩ ilk)))
      (solcSlotWord σ' I (solcMappingSlot ⟨1⟩ ilk + ⟨1⟩))
      (solcSlotWord σ' I (solcMappingSlot ⟨1⟩ ilk + ⟨2⟩))) ⟨10⟩ rd1688
    (by native_decide)
    (fun s hs hst => mstoreCost_of_stack hs hst (by rw [hDunkOff]; native_decide))
    (by rfl) (by rw [hDunkOff]; native_decide) (by evm_ov)
  have rd1691 := rd1689.push1 ⟨5⟩ (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd1692⟩ := rd1691.sload (by native_decide) (by evm_ov)
  have rd1694 := rd1692.push1 ⟨6⟩ (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd1695⟩ := rd1694.sload (by native_decide) (by evm_ov)
  have rd1696 := rd1695.swap2 (by native_decide) (by evm_ov)
  have rd1697 := rd1696.swap3 (by native_decide) (by evm_ov)
  have rd1698 := rd1697.swap2 (by native_decide) (by evm_ov)
  have rd1699 := rd1698.dup3 (by native_decide) (by evm_ov)
  have rd1700 := rd1699.swap2 (by native_decide) (by evm_ov)
  have rd1703 := rd1700.push2 ⟨1708⟩ (by native_decide) (by evm_ov)
  have rd1704 := rd1703.swap2 (by native_decide) (by evm_ov)
  have rd1707 := rd1704.push2 ⟨3762⟩ (by native_decide) (by evm_ov)
  have rd3762 := rd1707.jump (by native_decide) (by jump_dest) (by evm_ov)
  exact ⟨_, _, rd3762⟩

/-! ## checked-`sub` EMPTY-revert (DSMath `sub` underflow → `revert(0,0)`) -/

/-- **checked-`sub` underflow → empty `revert(0,0)`.** solc 0.6.12 compiles the DSMath `sub`
underflow guard's false branch as `PUSH1 0; DUP1; REVERT` (empty revert), NOT an error string
(unlike `RD.solcCheckedSubStringRevertGrown`). Same success-guard prefix; the tail fires
`RD.solcPush1Dup1Revert0`. -/
theorem RD.solcCheckedSubEmptyRevert {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {pc okPc : UInt256}
    {a b ret : UInt256} {R : List UInt256} {mem rdata : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD code ee g s0 pc (b :: a :: ret :: R) mem aw rdata acc k C)
    (hsub : solcCheckedSubSuccessWf code pc okPc)
    (hd0 : decode code (solcCheckedArithmeticRevertPc pc) = some (.Push .PUSH1, some (⟨0⟩, 1)))
    (hd1 : decode code (solcCheckedArithmeticRevertPc pc + UInt256.ofNat 2) = some (.DUP1, .none))
    (hd2 : decode code (solcCheckedArithmeticRevertPc pc + UInt256.ofNat 2 + ⟨1⟩) =
      some (.REVERT, .none))
    (hlt : a.toNat < b.toNat) (hov : R.length + 9 ≤ 1024) :
    RDrev code g s0 := by
  rcases hsub with
    ⟨hd0', hd1', hd2', hd3', hd4', hd5', hd6', hd7', hd8', hd11, _, _, _, _, _, _⟩
  have hsubNat : (UInt256.sub a b).toNat = UInt256.size + a.toNat - b.toNat :=
    usub_toNat_underflow hlt
  have hgt : UInt256.gt (UInt256.sub a b) a = ⟨1⟩ := by
    show UInt256.fromBool (decide (UInt256.sub a b > a)) = ⟨1⟩
    rw [decide_eq_true]
    · rfl
    · show (UInt256.sub a b).toNat > a.toNat
      rw [hsubNat]
      have hb : b.toNat < UInt256.size := b.val.isLt
      omega
  have rd6 := evm_run h with [
    raw jumpdest hd0' (by evm_ov),
    raw dup1 hd1' (by evm_ov),
    raw dup3 hd2' (by evm_ov),
    raw sub hd3' (by evm_ov),
    raw dup3 hd4' (by evm_ov),
    raw dup2 hd5' (by evm_ov)]
  have rd7₀ := evm_run rd6 with [raw gt hd6' (by evm_ov)]
  have rd7 := rd7₀
  rw [hgt] at rd7
  have rd8₀ := evm_run rd7 with [raw iszero hd7' (by evm_ov)]
  have rd8 := rd8₀
  rw [show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at rd8
  have rdPush := evm_run rd8 with [raw push2 okPc hd8' (by evm_ov)]
  have rdTail₀ := rdPush.jumpiNT hd11 (by decide) (by simp only [List.length_cons]; omega)
  have rdTail := by
    simpa [solcCheckedArithmeticRevertPc] using rdTail₀
  exact RD.solcPush1Dup1Revert0 rdTail hd0 hd1 hd2 (by simp only [List.length_cons]; omega)

/-- **room-underflow (box < litter) empty-revert leaf.** `room = box - litter` underflows; the
checked-`sub` reverts `revert(0,0)`. EVM side via `RD.solcCheckedSubEmptyRevert`, Solm side fed as
`hbody` (`catBiteSourceRoomUnderflowRevert`). -/
theorem catBiteRoomUnderflowEmptyRevertLeaf {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {mem rdata : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {a b ret okPc : UInt256} {R : List UInt256} {k C : ℕ}
    (hcode : I.code = catBytecode)
    (hdispatch : dispatchMsg contract I.calldata = some biteTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (biteTransition.params.map Param.name)
        (transitionSignature biteTransition).paramTypes I.calldata = some (biteLocals I))
    (rd : RD catBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨3762⟩
      (b :: a :: ret :: R) mem aw rdata acc k C)
    (hsub : solcCheckedSubSuccessWf catBytecode ⟨3762⟩ okPc)
    (hlt : a.toNat < b.toNat) (hov : R.length + 9 ≤ 1024)
    (hbody :
      ExecTransitionBody config contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) (biteLocals I)
        biteTransition.body .reverted) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hrev := RD.solcCheckedSubEmptyRevert rd hsub (by native_decide) (by native_decide)
    (by native_decide) hlt hov
  simpa using hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody


set_option maxHeartbeats 2000000 in
/-- **room-underflow (box < litter) branch (extracted).** Reaches the room-`sub` subroutine at pc
3762 (aw grown 9→10 by the milk-struct write) via `catBiteReachGuardRoomSubAw`, maps the ilks+urns
calls to σ_solm, and fires `catBiteRoomUnderflowEmptyRevertLeaf` (empty `revert(0,0)`) +
`catBiteSourceRoomUnderflowRevert`. -/
theorem catBiteRevertRoomSub {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {σ' σu : AccountMap} {A' Au : Substate}
    {cA' cAu : Batteries.RBSet AccountAddress compare} {o' ou : ByteArray} {ku Cu : ℕ}
    {art ink iSpot iRate iDust : UInt256}
    (hcode : I.code = catBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hdispatch : dispatchMsg contract I.calldata = some biteTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (biteTransition.params.map Param.name)
        (transitionSignature biteTransition).paramTypes I.calldata = some (biteLocals I))
    (hAccounts : accountMapEquiv σ_evm σ_solm) (hsz36 : 36 ≤ I.calldata.size)
    (hdepth : (I.depth : ℕ) < 1024)
    (hvatCode : ¬ Reasoning.Theory.extCodeSizeWord σ_evm (catBiteVatTargetWord σ_evm I) = ⟨0⟩)
    (hUrnsVatCode :
      ¬ Reasoning.Theory.extCodeSizeWord σ' ((catSlotWord ⟨3⟩ σ' I).land biteAddrMaskWord) = ⟨0⟩)
    (hIlksCall :
      typedCallViaEVM config (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        (AccountAddress.ofUInt256 (catBiteVatTargetWord σ_evm I)) "ilks" 0 [biteIlkVal I]
        (true, { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
                  accountMap := σ', substate := A', createdAccounts := cA' }, o') false)
    (hUrnsCall :
      typedCallViaEVM config
        { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
            accountMap := σ', createdAccounts := cA' }
        (AccountAddress.ofUInt256 ((catSlotWord ⟨3⟩ σ' I).land biteAddrMaskWord)) "urns" 0
        [biteIlkVal I, biteUrnVal I]
        (true, { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
                  accountMap := σu, substate := Au, createdAccounts := cAu }, ou) false)
    (hilkslen : 160 ≤ o'.size) (hurnslen : 64 ≤ ou.size)
    (hosz : o'.size < UInt256.size) (hoszu : ou.size < UInt256.size)
    (hurn : biteAddrMaskWord.land (biteAddrMaskWord.land (calldataWord I.calldata 36)) = biteUrnWord I)
    (hlive : catSlotWord ⟨2⟩ σu I = ⟨1⟩)
    (hmemI : 196 ≤ (catBiteIlksPostCallMem I o').size)
    (hmemUsz : 224 ≤ (catBiteUrnsPostCallMem I (catBiteIlksPostCallMem I o') ou).size)
    (rd1620 : RD catBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1620⟩
      (art :: ink :: iDust :: iSpot :: iRate :: ⟨0⟩ ::
        biteAddrMaskWord.land (calldataWord I.calldata 36) :: biteIlkWord I :: ⟨419⟩ :: catSelWord I :: [])
      (catBiteUrnsPostCallMem I (catBiteIlksPostCallMem I o') ou) ⟨9⟩ ou (cAu, σu) ku Cu)
    (hle : ¬ (solcSlotWord σu I ⟨6⟩).toNat ≤ (solcSlotWord σu I ⟨5⟩).toNat)
    (hunsafe : (ink * iSpot).toNat < (art * iRate).toNat)
    (hfitArtRate : art.toNat * iRate.toNat < UInt256.size)
    (hfitInkSpot : ink.toNat * iSpot.toNat < UInt256.size)
    (hspotPos : 0 < iSpot.toNat)
    (hart : art = UInt256.ofNat (fromByteArrayBigEndian (ou.extract 32 64)))
    (hink : ink = UInt256.ofNat (fromByteArrayBigEndian (ou.extract 0 32)))
    (hiSpot : iSpot = UInt256.ofNat (fromByteArrayBigEndian (o'.extract 64 96)))
    (hiRate : iRate = UInt256.ofNat (fromByteArrayBigEndian (o'.extract 32 64)))
    (hiDust : iDust = UInt256.ofNat (fromByteArrayBigEndian (o'.extract 128 160))) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hdepthNe : I.depth ≠ 1024 := by omega
  have h64 : (⟨64⟩ : UInt256).toNat = 64 := by native_decide
  have h128 : (⟨128⟩ : UInt256).toNat = 128 := by native_decide
  -- reach the room-`sub` subroutine at pc 3762 (aw grows 9→10)
  obtain ⟨_, _, rd3762⟩ := catBiteReachGuardRoomSubAw (fp := ⟨128⟩) rd1620
    (by native_decide)
    (mloadWordValue_of_readWithPadding (off := ⟨64⟩) (v := ⟨128⟩)
      (by rw [h64]; have := hmemUsz; omega) (by native_decide)
      (catBiteUrnsPostCallMem_read64 I ou hmemI
        (catBiteIlksPostCallMem_read64 I o' hilkslen hosz) hurnslen hoszu))
    (catBiteScratchMem_mload64 (catBiteUrnsPostCallMem I (catBiteIlksPostCallMem I o') ou)
      ⟨128⟩ (biteIlkWord I) (by rw [h128]; have := hmemUsz; omega) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide))
    (catBiteScratchMem_read0_64 (catBiteUrnsPostCallMem I (catBiteIlksPostCallMem I o') ou)
      ⟨128⟩ (biteIlkWord I) (by rw [h128]; have := hmemUsz; omega) (by native_decide))
    (by native_decide) (by native_decide) (by native_decide) (by simp)
  -- Solm-side ilks+urns calls
  obtain ⟨σs, As, σus, Aus, hIlksSolm, hUrnsSolm, hAmEq, hvatCodeIlkS⟩ :=
    catBiteMapUrns hAccounts hdepthNe hUrnsVatCode hIlksCall hUrnsCall
  set eUrnS := { initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I with
    accountMap := σus, substate := Aus, createdAccounts := cAu } with heUrnSdef
  have heUSam : eUrnS.accountMap = σus := rfl
  have heUSee : eUrnS.executionEnv = I := rfl
  have slotEqUS : ∀ s : UInt256, solcSlotWord σus I s = solcSlotWord σu I s := by
    intro s; simp only [solcSlotWord]
    rw [accountMapEquiv_storage_findD hAmEq I.codeOwner s ⟨0⟩]
  have hbr : ∀ (o : ByteArray) (k : ℕ), k + 32 ≤ o.size →
      ABI.bytesToWord ((o.toList.drop k).take 32) =
        UInt256.ofNat (fromByteArrayBigEndian (o.extract k (k + 32))) := by
    intro o k h
    rw [decode_word_at_eq_any o k h, uInt256OfByteArray_eq]
    congr 1; unfold fromByteArrayBigEndian; congr 1
    rw [byteArray_toList_eq (o.readBytes k 32), readBytes_at_toList_any o k h,
      byteArray_toList_eq (o.extract k (k + 32)), ByteArray.data_extract, Array.toList_extract,
      List.extract_eq_take_drop]
    simp
  have hIlksDec : config.externalABI.decode? "ilks" o' =
      some [bw (UInt256.ofNat (fromByteArrayBigEndian (o'.extract 0 32))), bw iRate, bw iSpot,
        bw (UInt256.ofNat (fromByteArrayBigEndian (o'.extract 96 128))), bw iDust] := by
    have h := catBiteIlksDecode_ok hilkslen
    rw [hbr o' 0 (by omega), hbr o' 32 (by omega), hbr o' 64 (by omega),
      hbr o' 96 (by omega), hbr o' 128 (by omega)] at h
    rw [hiRate, hiSpot, hiDust]; exact h
  have hUrnsDec : config.externalABI.decode? "urns" ou = some [bw ink, bw art] := by
    have h := catBiteUrnsDecode_ok hurnslen
    rw [hbr ou 0 (by omega), hbr ou 32 (by omega)] at h
    rw [hink, hart]; exact h
  have hlive' : catSlotWord ⟨2⟩ eUrnS.accountMap eUrnS.executionEnv = ⟨1⟩ := by
    rw [heUSam, heUSee]
    simp only [catSlotWord]; rw [slotEqUS ⟨2⟩]
    simpa only [catSlotWord] using hlive
  have hratePos : 0 < iRate.toNat := by
    by_contra hc
    have hr0 : iRate.toNat = 0 := by omega
    have hz : (art * iRate).toNat = 0 := by
      rw [u256_mul_op_toNat, hr0, Nat.mul_zero, Nat.zero_mod]
    omega
  have hlitGtBox : (biteBoxW eUrnS).toNat < (biteLitW eUrnS).toNat := by
    simp only [biteBoxW, biteLitW, catSlotWord, heUSam, heUSee]
    rw [slotEqUS ⟨5⟩, slotEqUS ⟨6⟩]; omega
  have hbody := catBiteSourceRoomUnderflowRevert hwv
    (catBiteVatCodePos_of_uniswap hAccounts hvatCode) hIlksSolm hIlksDec hvatCodeIlkS
    hUrnsSolm hUrnsDec hlive' hsz36 hfitInkSpot hfitArtRate hspotPos hratePos hunsafe hlitGtBox
  exact catBiteRoomUnderflowEmptyRevertLeaf (okPc := ⟨3756⟩) hcode hdispatch hdecode rd3762
    (by unfold solcCheckedSubSuccessWf; repeat' first | apply And.intro | native_decide)
    (by omega) (by simp only [List.length_cons, List.length_nil]; omega) hbody


set_option maxHeartbeats 2000000 in
/-- **dunkRoom·WAD checkedMul-overflow branch (extracted).** Post-milk (aw=10) guard: reaches the
`dunkRoom * WAD` `checkedMul` frame at pc 3720 (via `catBiteTraceSeg7a` + `catBiteReachGuardDunkRoomWad`),
fires `catBiteMulOverflowRevertLeaf` + `catBiteSourceDunkRoomWadOverflowRevert`. -/
theorem catBiteRevertDunkRoomWad {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {σ' σu : AccountMap} {A' Au : Substate}
    {cA' cAu : Batteries.RBSet AccountAddress compare} {o' ou : ByteArray} {ku Cu : ℕ}
    {art ink iSpot iRate iDust room milkChop milkDunk dunkRoom q : UInt256}
    (hcode : I.code = catBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hdispatch : dispatchMsg contract I.calldata = some biteTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (biteTransition.params.map Param.name)
        (transitionSignature biteTransition).paramTypes I.calldata = some (biteLocals I))
    (hAccounts : accountMapEquiv σ_evm σ_solm) (hsz36 : 36 ≤ I.calldata.size)
    (hdepth : (I.depth : ℕ) < 1024)
    (hvatCode : ¬ Reasoning.Theory.extCodeSizeWord σ_evm (catBiteVatTargetWord σ_evm I) = ⟨0⟩)
    (hUrnsVatCode :
      ¬ Reasoning.Theory.extCodeSizeWord σ' ((catSlotWord ⟨3⟩ σ' I).land biteAddrMaskWord) = ⟨0⟩)
    (hIlksCall :
      typedCallViaEVM config (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        (AccountAddress.ofUInt256 (catBiteVatTargetWord σ_evm I)) "ilks" 0 [biteIlkVal I]
        (true, { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
                  accountMap := σ', substate := A', createdAccounts := cA' }, o') false)
    (hUrnsCall :
      typedCallViaEVM config
        { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
            accountMap := σ', createdAccounts := cA' }
        (AccountAddress.ofUInt256 ((catSlotWord ⟨3⟩ σ' I).land biteAddrMaskWord)) "urns" 0
        [biteIlkVal I, biteUrnVal I]
        (true, { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
                  accountMap := σu, substate := Au, createdAccounts := cAu }, ou) false)
    (hilkslen : 160 ≤ o'.size) (hurnslen : 64 ≤ ou.size)
    (hosz : o'.size < UInt256.size) (hoszu : ou.size < UInt256.size)
    (hurn : biteAddrMaskWord.land (biteAddrMaskWord.land (calldataWord I.calldata 36)) = biteUrnWord I)
    (hlive : catSlotWord ⟨2⟩ σu I = ⟨1⟩)
    (hmemI : 196 ≤ (catBiteIlksPostCallMem I o').size)
    (hmemUsz : 224 ≤ (catBiteUrnsPostCallMem I (catBiteIlksPostCallMem I o') ou).size)
    (hqNat : q.toNat = 224)
    (rd1708 : RD catBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1708⟩
      (room :: ⟨0⟩ :: ⟨0⟩ :: q :: art :: ink :: iDust :: iSpot :: iRate :: ⟨0⟩ ::
        biteAddrMaskWord.land (calldataWord I.calldata 36) :: biteIlkWord I :: ⟨419⟩ :: catSelWord I :: [])
      (catBiteMilkMem (catBiteUrnsPostCallMem I (catBiteIlksPostCallMem I o') ou) ⟨128⟩ (biteIlkWord I) q
        (biteAddrMaskWord.land (solcSlotWord σu I (solcMappingSlot ⟨1⟩ (biteIlkWord I)))) milkChop milkDunk)
      ⟨10⟩ ou (cAu, σu) ku Cu)
    (hChop : (if (⟨32⟩ + q).toNat ≥
          (catBiteMilkMem (catBiteUrnsPostCallMem I (catBiteIlksPostCallMem I o') ou) ⟨128⟩ (biteIlkWord I) q
            (biteAddrMaskWord.land (solcSlotWord σu I (solcMappingSlot ⟨1⟩ (biteIlkWord I)))) milkChop
            milkDunk).size ∨ (⟨32⟩ + q) ≥ (⟨10⟩ : UInt256) * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat (fromByteArrayBigEndian
        ((catBiteMilkMem (catBiteUrnsPostCallMem I (catBiteIlksPostCallMem I o') ou) ⟨128⟩ (biteIlkWord I) q
            (biteAddrMaskWord.land (solcSlotWord σu I (solcMappingSlot ⟨1⟩ (biteIlkWord I)))) milkChop
            milkDunk).readWithPadding (⟨32⟩ + q).toNat 32))) = milkChop)
    (hDunk : (if (⟨64⟩ + q).toNat ≥
          (catBiteMilkMem (catBiteUrnsPostCallMem I (catBiteIlksPostCallMem I o') ou) ⟨128⟩ (biteIlkWord I) q
            (biteAddrMaskWord.land (solcSlotWord σu I (solcMappingSlot ⟨1⟩ (biteIlkWord I)))) milkChop
            milkDunk).size ∨ (⟨64⟩ + q) ≥ (⟨10⟩ : UInt256) * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat (fromByteArrayBigEndian
        ((catBiteMilkMem (catBiteUrnsPostCallMem I (catBiteIlksPostCallMem I o') ou) ⟨128⟩ (biteIlkWord I) q
            (biteAddrMaskWord.land (solcSlotWord σu I (solcMappingSlot ⟨1⟩ (biteIlkWord I)))) milkChop
            milkDunk).readWithPadding (⟨64⟩ + q).toNat 32))) = milkDunk)
    (hlitterbox : (solcSlotWord σu I ⟨6⟩).toNat < (solcSlotWord σu I ⟨5⟩).toNat)
    (hroomdust : iDust.toNat ≤ room.toNat)
    (hunsafe : (ink * iSpot).toNat < (art * iRate).toNat)
    (hfitArtRate : art.toNat * iRate.toNat < UInt256.size)
    (hfitInkSpot : ink.toNat * iSpot.toNat < UInt256.size)
    (hspotPos : 0 < iSpot.toNat) (hRatePos : iRate ≠ ⟨0⟩)
    (hFitWad : ¬ (⟨1000000000000000000⟩ : UInt256).toNat * dunkRoom.toNat < UInt256.size)
    (hart : art = UInt256.ofNat (fromByteArrayBigEndian (ou.extract 32 64)))
    (hink : ink = UInt256.ofNat (fromByteArrayBigEndian (ou.extract 0 32)))
    (hiSpot : iSpot = UInt256.ofNat (fromByteArrayBigEndian (o'.extract 64 96)))
    (hiRate : iRate = UInt256.ofNat (fromByteArrayBigEndian (o'.extract 32 64)))
    (hiDust : iDust = UInt256.ofNat (fromByteArrayBigEndian (o'.extract 128 160)))
    (hroomDef : room = (solcSlotWord σu I ⟨5⟩).sub (solcSlotWord σu I ⟨6⟩))
    (hmilkDunkDef : milkDunk = solcSlotWord σu I (solcMappingSlot ⟨1⟩ (biteIlkWord I) + ⟨2⟩))
    (hmilkChopDef : milkChop = solcSlotWord σu I (solcMappingSlot ⟨1⟩ (biteIlkWord I) + ⟨1⟩))
    (hdunkRoomDef : dunkRoom = if milkDunk.gt room = ⟨0⟩ then milkDunk else room) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hdepthNe : I.depth ≠ 1024 := by omega
  obtain ⟨_, _, rd1810⟩ := catBiteTraceSeg7a rd1708 hlitterbox hroomdust (by simp)
  obtain ⟨_, _, rd3720⟩ := catBiteReachGuardDunkRoomWad rd1810 hChop hDunk
    (by rw [hqNat]; native_decide) (by rw [hqNat]; native_decide) hdunkRoomDef.symm (by simp)
  obtain ⟨σs, As, σus, Aus, hIlksSolm, hUrnsSolm, hAmEq, hvatCodeIlkS⟩ :=
    catBiteMapUrns hAccounts hdepthNe hUrnsVatCode hIlksCall hUrnsCall
  set eUrnS := { initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I with
    accountMap := σus, substate := Aus, createdAccounts := cAu } with heUrnSdef
  have heUSam : eUrnS.accountMap = σus := rfl
  have heUSee : eUrnS.executionEnv = I := rfl
  have slotEqUS : ∀ s : UInt256, solcSlotWord σus I s = solcSlotWord σu I s := by
    intro s; simp only [solcSlotWord]
    rw [accountMapEquiv_storage_findD hAmEq I.codeOwner s ⟨0⟩]
  have uminEq : ∀ a b : UInt256, (if UInt256.gt a b = ⟨0⟩ then a else b) = umin a b := by
    intro a b; unfold umin
    by_cases h : a.toNat ≤ b.toNat
    · rw [if_pos (ugt_zero h), if_pos h]
    · rw [if_neg (by rw [ugt_one (by omega)]; decide), if_neg h]
  have hbr : ∀ (o : ByteArray) (k : ℕ), k + 32 ≤ o.size →
      ABI.bytesToWord ((o.toList.drop k).take 32) =
        UInt256.ofNat (fromByteArrayBigEndian (o.extract k (k + 32))) := by
    intro o k h
    rw [decode_word_at_eq_any o k h, uInt256OfByteArray_eq]
    congr 1; unfold fromByteArrayBigEndian; congr 1
    rw [byteArray_toList_eq (o.readBytes k 32), readBytes_at_toList_any o k h,
      byteArray_toList_eq (o.extract k (k + 32)), ByteArray.data_extract, Array.toList_extract,
      List.extract_eq_take_drop]
    simp
  have hIlksDec : config.externalABI.decode? "ilks" o' =
      some [bw (UInt256.ofNat (fromByteArrayBigEndian (o'.extract 0 32))), bw iRate, bw iSpot,
        bw (UInt256.ofNat (fromByteArrayBigEndian (o'.extract 96 128))), bw iDust] := by
    have h := catBiteIlksDecode_ok hilkslen
    rw [hbr o' 0 (by omega), hbr o' 32 (by omega), hbr o' 64 (by omega),
      hbr o' 96 (by omega), hbr o' 128 (by omega)] at h
    rw [hiRate, hiSpot, hiDust]; exact h
  have hUrnsDec : config.externalABI.decode? "urns" ou = some [bw ink, bw art] := by
    have h := catBiteUrnsDecode_ok hurnslen
    rw [hbr ou 0 (by omega), hbr ou 32 (by omega)] at h
    rw [hink, hart]; exact h
  have hlive' : catSlotWord ⟨2⟩ eUrnS.accountMap eUrnS.executionEnv = ⟨1⟩ := by
    rw [heUSam, heUSee]; simp only [catSlotWord]; rw [slotEqUS ⟨2⟩]
    simpa only [catSlotWord] using hlive
  have hratePos : 0 < iRate.toNat := by
    by_contra hc
    have hr0 : iRate.toNat = 0 := by omega
    have hz : (art * iRate).toNat = 0 := by
      rw [u256_mul_op_toNat, hr0, Nat.mul_zero, Nat.zero_mod]
    omega
  have hboxB : biteBoxW eUrnS = solcSlotWord σu I ⟨5⟩ := by
    simp only [biteBoxW, catSlotWord, heUSam, heUSee]; exact slotEqUS ⟨5⟩
  have hlitB : biteLitW eUrnS = solcSlotWord σu I ⟨6⟩ := by
    simp only [biteLitW, catSlotWord, heUSam, heUSee]; exact slotEqUS ⟨6⟩
  have hroomB : biteRoomV eUrnS = room := by
    rw [hroomDef]; simp only [biteRoomV, hboxB, hlitB]
  have hdunkB : biteDunkW I eUrnS = milkDunk := by
    rw [hmilkDunkDef]
    simp only [biteDunkW, catSlotWord, heUSam, heUSee, biteDunkSlot, biteFlipSlot_eq hsz36]
    exact slotEqUS _
  have hdunkroomB : biteDunkRoomV I eUrnS = dunkRoom := by
    rw [hdunkRoomDef, uminEq milkDunk room]
    simp only [biteDunkRoomV, hdunkB, hroomB]
  have hlitLtBox : (biteLitW eUrnS).toNat < (biteBoxW eUrnS).toNat := by
    rw [hlitB, hboxB]; exact hlitterbox
  have hroomGeDust : iDust.toNat ≤ (biteRoomV eUrnS).toNat := by rw [hroomB]; exact hroomdust
  have hwad : wadU = ⟨1000000000000000000⟩ := by native_decide
  have hbody := catBiteSourceDunkRoomWadOverflowRevert hwv
    (catBiteVatCodePos_of_uniswap hAccounts hvatCode) hIlksSolm hIlksDec hvatCodeIlkS
    hUrnsSolm hUrnsDec hlive' hsz36 hfitInkSpot hfitArtRate hspotPos hratePos hunsafe hlitLtBox
    hroomGeDust (by rw [hdunkroomB, hwad, Nat.mul_comm]; exact Nat.le_of_not_lt hFitWad)
  exact catBiteMulOverflowRevertLeaf hcode hdispatch hdecode rd3720
    (Nat.le_of_not_lt hFitWad) (by simp only [List.length_cons, List.length_nil]; omega) hbody


set_option maxHeartbeats 2000000 in
/-- **milkChop div-by-zero `INVALID` branch (extracted).** Post-milk (aw=10) guard on the
`milkChop = 0` branch: past the `dunkRoom*WAD` `checkedMul` (`hFitWad` holds) and `rate != 0` guard,
reaches the `INVALID` at pc 1865 (`catBiteTraceSeg7a` + `catBiteReachGuardMilkChopZero`), fires
`catBiteMilkChopZeroRevertLeaf` + `catBiteSourceMilkChopZeroRevert`. -/
theorem catBiteRevertMilkChopZero {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {σ' σu : AccountMap} {A' Au : Substate}
    {cA' cAu : Batteries.RBSet AccountAddress compare} {o' ou : ByteArray} {ku Cu : ℕ}
    {art ink iSpot iRate iDust room milkChop milkDunk dunkRoom dunkRoomWad dartDenomRate q : UInt256}
    (hcode : I.code = catBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hdispatch : dispatchMsg contract I.calldata = some biteTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (biteTransition.params.map Param.name)
        (transitionSignature biteTransition).paramTypes I.calldata = some (biteLocals I))
    (hAccounts : accountMapEquiv σ_evm σ_solm) (hsz36 : 36 ≤ I.calldata.size)
    (hdepth : (I.depth : ℕ) < 1024)
    (hvatCode : ¬ Reasoning.Theory.extCodeSizeWord σ_evm (catBiteVatTargetWord σ_evm I) = ⟨0⟩)
    (hUrnsVatCode :
      ¬ Reasoning.Theory.extCodeSizeWord σ' ((catSlotWord ⟨3⟩ σ' I).land biteAddrMaskWord) = ⟨0⟩)
    (hIlksCall :
      typedCallViaEVM config (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        (AccountAddress.ofUInt256 (catBiteVatTargetWord σ_evm I)) "ilks" 0 [biteIlkVal I]
        (true, { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
                  accountMap := σ', substate := A', createdAccounts := cA' }, o') false)
    (hUrnsCall :
      typedCallViaEVM config
        { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
            accountMap := σ', createdAccounts := cA' }
        (AccountAddress.ofUInt256 ((catSlotWord ⟨3⟩ σ' I).land biteAddrMaskWord)) "urns" 0
        [biteIlkVal I, biteUrnVal I]
        (true, { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
                  accountMap := σu, substate := Au, createdAccounts := cAu }, ou) false)
    (hilkslen : 160 ≤ o'.size) (hurnslen : 64 ≤ ou.size)
    (hosz : o'.size < UInt256.size) (hoszu : ou.size < UInt256.size)
    (hurn : biteAddrMaskWord.land (biteAddrMaskWord.land (calldataWord I.calldata 36)) = biteUrnWord I)
    (hlive : catSlotWord ⟨2⟩ σu I = ⟨1⟩)
    (hmemI : 196 ≤ (catBiteIlksPostCallMem I o').size)
    (hmemUsz : 224 ≤ (catBiteUrnsPostCallMem I (catBiteIlksPostCallMem I o') ou).size)
    (hqNat : q.toNat = 224)
    (rd1708 : RD catBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1708⟩
      (room :: ⟨0⟩ :: ⟨0⟩ :: q :: art :: ink :: iDust :: iSpot :: iRate :: ⟨0⟩ ::
        biteAddrMaskWord.land (calldataWord I.calldata 36) :: biteIlkWord I :: ⟨419⟩ :: catSelWord I :: [])
      (catBiteMilkMem (catBiteUrnsPostCallMem I (catBiteIlksPostCallMem I o') ou) ⟨128⟩ (biteIlkWord I) q
        (biteAddrMaskWord.land (solcSlotWord σu I (solcMappingSlot ⟨1⟩ (biteIlkWord I)))) milkChop milkDunk)
      ⟨10⟩ ou (cAu, σu) ku Cu)
    (hChop : (if (⟨32⟩ + q).toNat ≥
          (catBiteMilkMem (catBiteUrnsPostCallMem I (catBiteIlksPostCallMem I o') ou) ⟨128⟩ (biteIlkWord I) q
            (biteAddrMaskWord.land (solcSlotWord σu I (solcMappingSlot ⟨1⟩ (biteIlkWord I)))) milkChop
            milkDunk).size ∨ (⟨32⟩ + q) ≥ (⟨10⟩ : UInt256) * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat (fromByteArrayBigEndian
        ((catBiteMilkMem (catBiteUrnsPostCallMem I (catBiteIlksPostCallMem I o') ou) ⟨128⟩ (biteIlkWord I) q
            (biteAddrMaskWord.land (solcSlotWord σu I (solcMappingSlot ⟨1⟩ (biteIlkWord I)))) milkChop
            milkDunk).readWithPadding (⟨32⟩ + q).toNat 32))) = milkChop)
    (hDunk : (if (⟨64⟩ + q).toNat ≥
          (catBiteMilkMem (catBiteUrnsPostCallMem I (catBiteIlksPostCallMem I o') ou) ⟨128⟩ (biteIlkWord I) q
            (biteAddrMaskWord.land (solcSlotWord σu I (solcMappingSlot ⟨1⟩ (biteIlkWord I)))) milkChop
            milkDunk).size ∨ (⟨64⟩ + q) ≥ (⟨10⟩ : UInt256) * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat (fromByteArrayBigEndian
        ((catBiteMilkMem (catBiteUrnsPostCallMem I (catBiteIlksPostCallMem I o') ou) ⟨128⟩ (biteIlkWord I) q
            (biteAddrMaskWord.land (solcSlotWord σu I (solcMappingSlot ⟨1⟩ (biteIlkWord I)))) milkChop
            milkDunk).readWithPadding (⟨64⟩ + q).toNat 32))) = milkDunk)
    (hlitterbox : (solcSlotWord σu I ⟨6⟩).toNat < (solcSlotWord σu I ⟨5⟩).toNat)
    (hroomdust : iDust.toNat ≤ room.toNat)
    (hunsafe : (ink * iSpot).toNat < (art * iRate).toNat)
    (hfitArtRate : art.toNat * iRate.toNat < UInt256.size)
    (hfitInkSpot : ink.toNat * iSpot.toNat < UInt256.size)
    (hspotPos : 0 < iSpot.toNat) (hRatePos : iRate ≠ ⟨0⟩)
    (hFitWad : (⟨1000000000000000000⟩ : UInt256).toNat * dunkRoom.toNat < UInt256.size)
    (hChopZero : milkChop = ⟨0⟩)
    (hart : art = UInt256.ofNat (fromByteArrayBigEndian (ou.extract 32 64)))
    (hink : ink = UInt256.ofNat (fromByteArrayBigEndian (ou.extract 0 32)))
    (hiSpot : iSpot = UInt256.ofNat (fromByteArrayBigEndian (o'.extract 64 96)))
    (hiRate : iRate = UInt256.ofNat (fromByteArrayBigEndian (o'.extract 32 64)))
    (hiDust : iDust = UInt256.ofNat (fromByteArrayBigEndian (o'.extract 128 160)))
    (hroomDef : room = (solcSlotWord σu I ⟨5⟩).sub (solcSlotWord σu I ⟨6⟩))
    (hmilkDunkDef : milkDunk = solcSlotWord σu I (solcMappingSlot ⟨1⟩ (biteIlkWord I) + ⟨2⟩))
    (hmilkChopDef : milkChop = solcSlotWord σu I (solcMappingSlot ⟨1⟩ (biteIlkWord I) + ⟨1⟩))
    (hdunkRoomDef : dunkRoom = if milkDunk.gt room = ⟨0⟩ then milkDunk else room)
    (hdunkRoomWadDef : dunkRoomWad = dunkRoom.mul ⟨1000000000000000000⟩)
    (hdartDenomDef : dartDenomRate = dunkRoomWad.div iRate) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hdepthNe : I.depth ≠ 1024 := by omega
  obtain ⟨_, _, rd1810⟩ := catBiteTraceSeg7a rd1708 hlitterbox hroomdust (by simp)
  obtain ⟨_, _, rd1865⟩ := catBiteReachGuardMilkChopZero rd1810 hChop hDunk
    (by rw [hqNat]; native_decide) (by rw [hqNat]; native_decide) hRatePos hdunkRoomDef.symm
    hFitWad hdunkRoomWadDef.symm hdartDenomDef.symm hChopZero (by simp)
  obtain ⟨σs, As, σus, Aus, hIlksSolm, hUrnsSolm, hAmEq, hvatCodeIlkS⟩ :=
    catBiteMapUrns hAccounts hdepthNe hUrnsVatCode hIlksCall hUrnsCall
  set eUrnS := { initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I with
    accountMap := σus, substate := Aus, createdAccounts := cAu } with heUrnSdef
  have heUSam : eUrnS.accountMap = σus := rfl
  have heUSee : eUrnS.executionEnv = I := rfl
  have slotEqUS : ∀ s : UInt256, solcSlotWord σus I s = solcSlotWord σu I s := by
    intro s; simp only [solcSlotWord]
    rw [accountMapEquiv_storage_findD hAmEq I.codeOwner s ⟨0⟩]
  have uminEq : ∀ a b : UInt256, (if UInt256.gt a b = ⟨0⟩ then a else b) = umin a b := by
    intro a b; unfold umin
    by_cases h : a.toNat ≤ b.toNat
    · rw [if_pos (ugt_zero h), if_pos h]
    · rw [if_neg (by rw [ugt_one (by omega)]; decide), if_neg h]
  have hbr : ∀ (o : ByteArray) (k : ℕ), k + 32 ≤ o.size →
      ABI.bytesToWord ((o.toList.drop k).take 32) =
        UInt256.ofNat (fromByteArrayBigEndian (o.extract k (k + 32))) := by
    intro o k h
    rw [decode_word_at_eq_any o k h, uInt256OfByteArray_eq]
    congr 1; unfold fromByteArrayBigEndian; congr 1
    rw [byteArray_toList_eq (o.readBytes k 32), readBytes_at_toList_any o k h,
      byteArray_toList_eq (o.extract k (k + 32)), ByteArray.data_extract, Array.toList_extract,
      List.extract_eq_take_drop]
    simp
  have hIlksDec : config.externalABI.decode? "ilks" o' =
      some [bw (UInt256.ofNat (fromByteArrayBigEndian (o'.extract 0 32))), bw iRate, bw iSpot,
        bw (UInt256.ofNat (fromByteArrayBigEndian (o'.extract 96 128))), bw iDust] := by
    have h := catBiteIlksDecode_ok hilkslen
    rw [hbr o' 0 (by omega), hbr o' 32 (by omega), hbr o' 64 (by omega),
      hbr o' 96 (by omega), hbr o' 128 (by omega)] at h
    rw [hiRate, hiSpot, hiDust]; exact h
  have hUrnsDec : config.externalABI.decode? "urns" ou = some [bw ink, bw art] := by
    have h := catBiteUrnsDecode_ok hurnslen
    rw [hbr ou 0 (by omega), hbr ou 32 (by omega)] at h
    rw [hink, hart]; exact h
  have hlive' : catSlotWord ⟨2⟩ eUrnS.accountMap eUrnS.executionEnv = ⟨1⟩ := by
    rw [heUSam, heUSee]; simp only [catSlotWord]; rw [slotEqUS ⟨2⟩]
    simpa only [catSlotWord] using hlive
  have hratePos : 0 < iRate.toNat := by
    by_contra hc
    have hr0 : iRate.toNat = 0 := by omega
    have hz : (art * iRate).toNat = 0 := by
      rw [u256_mul_op_toNat, hr0, Nat.mul_zero, Nat.zero_mod]
    omega
  have hboxB : biteBoxW eUrnS = solcSlotWord σu I ⟨5⟩ := by
    simp only [biteBoxW, catSlotWord, heUSam, heUSee]; exact slotEqUS ⟨5⟩
  have hlitB : biteLitW eUrnS = solcSlotWord σu I ⟨6⟩ := by
    simp only [biteLitW, catSlotWord, heUSam, heUSee]; exact slotEqUS ⟨6⟩
  have hroomB : biteRoomV eUrnS = room := by
    rw [hroomDef]; simp only [biteRoomV, hboxB, hlitB]
  have hdunkB : biteDunkW I eUrnS = milkDunk := by
    rw [hmilkDunkDef]
    simp only [biteDunkW, catSlotWord, heUSam, heUSee, biteDunkSlot, biteFlipSlot_eq hsz36]
    exact slotEqUS _
  have hchopBS : biteChopW I eUrnS = milkChop := by
    rw [hmilkChopDef]
    simp only [biteChopW, catSlotWord, heUSam, heUSee, biteChopSlot, biteFlipSlot_eq hsz36]
    exact slotEqUS _
  have hdunkroomB : biteDunkRoomV I eUrnS = dunkRoom := by
    rw [hdunkRoomDef, uminEq milkDunk room]
    simp only [biteDunkRoomV, hdunkB, hroomB]
  have hlitLtBox : (biteLitW eUrnS).toNat < (biteBoxW eUrnS).toNat := by
    rw [hlitB, hboxB]; exact hlitterbox
  have hroomGeDust : iDust.toNat ≤ (biteRoomV eUrnS).toNat := by rw [hroomB]; exact hroomdust
  have hwad : wadU = ⟨1000000000000000000⟩ := by native_decide
  have hbody := catBiteSourceMilkChopZeroRevert hwv
    (catBiteVatCodePos_of_uniswap hAccounts hvatCode) hIlksSolm hIlksDec hvatCodeIlkS
    hUrnsSolm hUrnsDec hlive' hsz36 hfitInkSpot hfitArtRate hspotPos hratePos hunsafe hlitLtBox
    hroomGeDust (by rw [hdunkroomB, hwad, Nat.mul_comm]; exact hFitWad)
    (by rw [hchopBS, hChopZero]; rfl)
  exact catBiteMilkChopZeroRevertLeaf hcode hdispatch hdecode rd1865 (by native_decide) hbody


set_option maxHeartbeats 2000000 in
/-- **inkSpot (ink·spot) checkedMul-overflow branch (extracted).** Pre-milk (aw=9) `Seg5` guard:
`ink * spot` overflows.  `spot > 0` is forced by the overflow (`spot = 0 ⇒ ink*spot = 0 < size`), so
reach the `ink*spot` `checkedMul` frame at pc 3720 (`catBiteReachGuardInkSpot`, past the passing
`art*rate` mul), fires `catBiteMulOverflowRevertLeaf` + `catBiteSourceInkSpotOverflowRevert`. -/
theorem catBiteRevertInkSpot {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {σ' σu : AccountMap} {A' Au : Substate}
    {cA' cAu : Batteries.RBSet AccountAddress compare} {o' ou : ByteArray} {ku Cu : ℕ}
    {mem2 : ByteArray} {aw2 : UInt256}
    {art ink iSpot iRate iDust : UInt256}
    (hcode : I.code = catBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hdispatch : dispatchMsg contract I.calldata = some biteTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (biteTransition.params.map Param.name)
        (transitionSignature biteTransition).paramTypes I.calldata = some (biteLocals I))
    (hAccounts : accountMapEquiv σ_evm σ_solm) (hsz36 : 36 ≤ I.calldata.size)
    (hdepth : (I.depth : ℕ) < 1024)
    (hvatCode : ¬ Reasoning.Theory.extCodeSizeWord σ_evm (catBiteVatTargetWord σ_evm I) = ⟨0⟩)
    (hUrnsVatCode :
      ¬ Reasoning.Theory.extCodeSizeWord σ' ((catSlotWord ⟨3⟩ σ' I).land biteAddrMaskWord) = ⟨0⟩)
    (hIlksCall :
      typedCallViaEVM config (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        (AccountAddress.ofUInt256 (catBiteVatTargetWord σ_evm I)) "ilks" 0 [biteIlkVal I]
        (true, { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
                  accountMap := σ', substate := A', createdAccounts := cA' }, o') false)
    (hUrnsCall :
      typedCallViaEVM config
        { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
            accountMap := σ', createdAccounts := cA' }
        (AccountAddress.ofUInt256 ((catSlotWord ⟨3⟩ σ' I).land biteAddrMaskWord)) "urns" 0
        [biteIlkVal I, biteUrnVal I]
        (true, { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
                  accountMap := σu, substate := Au, createdAccounts := cAu }, ou) false)
    (hilkslen : 160 ≤ o'.size) (hurnslen : 64 ≤ ou.size)
    (hurn : biteAddrMaskWord.land (biteAddrMaskWord.land (calldataWord I.calldata 36)) = biteUrnWord I)
    (hlive : catSlotWord ⟨2⟩ σu I = ⟨1⟩)
    (rd1521 : RD catBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1521⟩
      (art :: ink :: iDust :: iSpot :: iRate :: ⟨0⟩ ::
        biteAddrMaskWord.land (calldataWord I.calldata 36) :: biteIlkWord I :: ⟨419⟩ :: catSelWord I :: [])
      mem2 aw2 ou (cAu, σu) ku Cu)
    (hfitArtRate : art.toNat * iRate.toNat < UInt256.size)
    (hart : art = UInt256.ofNat (fromByteArrayBigEndian (ou.extract 32 64)))
    (hink : ink = UInt256.ofNat (fromByteArrayBigEndian (ou.extract 0 32)))
    (hiSpot : iSpot = UInt256.ofNat (fromByteArrayBigEndian (o'.extract 64 96)))
    (hiRate : iRate = UInt256.ofNat (fromByteArrayBigEndian (o'.extract 32 64)))
    (hiDust : iDust = UInt256.ofNat (fromByteArrayBigEndian (o'.extract 128 160)))
    (hInkSpotNofit : ¬ ink.toNat * iSpot.toNat < UInt256.size) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hdepthNe : I.depth ≠ 1024 := by omega
  have hsz_pos : 0 < UInt256.size := by rw [show UInt256.size = 2 ^ 256 from rfl]; positivity
  have hspotPos : 0 < iSpot.toNat := by
    by_contra hc
    have h0 : iSpot.toNat = 0 := Nat.le_zero.mp (Nat.not_lt.mp hc)
    exact hInkSpotNofit (by rw [h0, Nat.mul_zero]; exact hsz_pos)
  obtain ⟨_, _, rd3720⟩ := catBiteReachGuardInkSpot rd1521 hspotPos hfitArtRate (by simp)
  obtain ⟨σs, As, σus, Aus, hIlksSolm, hUrnsSolm, hAmEq, hvatCodeIlkS⟩ :=
    catBiteMapUrns hAccounts hdepthNe hUrnsVatCode hIlksCall hUrnsCall
  set eUrnS := { initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I with
    accountMap := σus, substate := Aus, createdAccounts := cAu } with heUrnSdef
  have heUSam : eUrnS.accountMap = σus := rfl
  have heUSee : eUrnS.executionEnv = I := rfl
  have slotEqUS : ∀ s : UInt256, solcSlotWord σus I s = solcSlotWord σu I s := by
    intro s; simp only [solcSlotWord]
    rw [accountMapEquiv_storage_findD hAmEq I.codeOwner s ⟨0⟩]
  have hbr : ∀ (o : ByteArray) (k : ℕ), k + 32 ≤ o.size →
      ABI.bytesToWord ((o.toList.drop k).take 32) =
        UInt256.ofNat (fromByteArrayBigEndian (o.extract k (k + 32))) := by
    intro o k h
    rw [decode_word_at_eq_any o k h, uInt256OfByteArray_eq]
    congr 1; unfold fromByteArrayBigEndian; congr 1
    rw [byteArray_toList_eq (o.readBytes k 32), readBytes_at_toList_any o k h,
      byteArray_toList_eq (o.extract k (k + 32)), ByteArray.data_extract, Array.toList_extract,
      List.extract_eq_take_drop]
    simp
  have hIlksDec : config.externalABI.decode? "ilks" o' =
      some [bw (UInt256.ofNat (fromByteArrayBigEndian (o'.extract 0 32))), bw iRate, bw iSpot,
        bw (UInt256.ofNat (fromByteArrayBigEndian (o'.extract 96 128))), bw iDust] := by
    have h := catBiteIlksDecode_ok hilkslen
    rw [hbr o' 0 (by omega), hbr o' 32 (by omega), hbr o' 64 (by omega),
      hbr o' 96 (by omega), hbr o' 128 (by omega)] at h
    rw [hiRate, hiSpot, hiDust]; exact h
  have hUrnsDec : config.externalABI.decode? "urns" ou = some [bw ink, bw art] := by
    have h := catBiteUrnsDecode_ok hurnslen
    rw [hbr ou 0 (by omega), hbr ou 32 (by omega)] at h
    rw [hink, hart]; exact h
  have hlive' : catSlotWord ⟨2⟩ eUrnS.accountMap eUrnS.executionEnv = ⟨1⟩ := by
    rw [heUSam, heUSee]; simp only [catSlotWord]; rw [slotEqUS ⟨2⟩]
    simpa only [catSlotWord] using hlive
  have hbody := catBiteSourceInkSpotOverflowRevert hwv
    (catBiteVatCodePos_of_uniswap hAccounts hvatCode) hIlksSolm hIlksDec hvatCodeIlkS
    hUrnsSolm hUrnsDec hlive' (Nat.le_of_not_lt hInkSpotNofit)
  exact catBiteMulOverflowRevertLeaf hcode hdispatch hdecode rd3720
    (by rw [Nat.mul_comm]; exact Nat.le_of_not_lt hInkSpotNofit)
    (by simp only [List.length_cons, List.length_nil]; omega) hbody


set_option maxHeartbeats 2000000 in
/-- **`live != 1` require-string revert branch (extracted).** Pre-milk (aw=9): `require(live == 1,
"Cat/not-live")` fails.  Reconstructs `Seg3` (urns return decode) to pc 1447 (`catBiteTraceSeg3`),
reaches the `live == 1` guard at pc 1458 (`catBiteReachGuardLive`), fires `catBiteRequireStringRevertLeaf`
(free ptr `0x80` intact pre-milk) + `catBiteSourceLiveRevert`. -/
theorem catBiteRevertLive {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {σ' σu : AccountMap} {A' Au : Substate}
    {cA' cAu : Batteries.RBSet AccountAddress compare} {o' ou : ByteArray} {ku Cu : ℕ}
    {aw status urnsTgt iRate iSpot iDust : UInt256}
    (hcode : I.code = catBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hdispatch : dispatchMsg contract I.calldata = some biteTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (biteTransition.params.map Param.name)
        (transitionSignature biteTransition).paramTypes I.calldata = some (biteLocals I))
    (hAccounts : accountMapEquiv σ_evm σ_solm) (hsz36 : 36 ≤ I.calldata.size)
    (hdepth : (I.depth : ℕ) < 1024)
    (hvatCode : ¬ Reasoning.Theory.extCodeSizeWord σ_evm (catBiteVatTargetWord σ_evm I) = ⟨0⟩)
    (hUrnsVatCode :
      ¬ Reasoning.Theory.extCodeSizeWord σ' ((catSlotWord ⟨3⟩ σ' I).land biteAddrMaskWord) = ⟨0⟩)
    (hIlksCall :
      typedCallViaEVM config (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        (AccountAddress.ofUInt256 (catBiteVatTargetWord σ_evm I)) "ilks" 0 [biteIlkVal I]
        (true, { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
                  accountMap := σ', substate := A', createdAccounts := cA' }, o') false)
    (hUrnsCall :
      typedCallViaEVM config
        { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
            accountMap := σ', createdAccounts := cA' }
        (AccountAddress.ofUInt256 ((catSlotWord ⟨3⟩ σ' I).land biteAddrMaskWord)) "urns" 0
        [biteIlkVal I, biteUrnVal I]
        (true, { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
                  accountMap := σu, substate := Au, createdAccounts := cAu }, ou) false)
    (hilkslen : 160 ≤ o'.size) (hosz : o'.size < UInt256.size)
    (hurnslen : 64 ≤ ou.size) (hoszu : ou.size < UInt256.size)
    (hurn : biteAddrMaskWord.land (biteAddrMaskWord.land (calldataWord I.calldata 36)) = biteUrnWord I)
    (rd1399 : RD catBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1399⟩
      (status :: ⟨196⟩ :: ⟨606387804⟩ :: urnsTgt :: ⟨0⟩ :: ⟨0⟩ :: iDust :: iSpot :: iRate :: ⟨0⟩ ::
        biteAddrMaskWord.land (calldataWord I.calldata 36) :: biteIlkWord I :: ⟨419⟩ :: catSelWord I :: [])
      (catBiteUrnsPostCallMem I (catBiteIlksPostCallMem I o') ou) aw ou (cAu, σu) ku Cu)
    (hstatus : status ≠ ⟨0⟩)
    (haw : 288 ≤ aw.toNat * 32) (hawsz : aw.toNat * 32 < UInt256.size)
    (hiRate : iRate = UInt256.ofNat (fromByteArrayBigEndian (o'.extract 32 64)))
    (hiSpot : iSpot = UInt256.ofNat (fromByteArrayBigEndian (o'.extract 64 96)))
    (hiDust : iDust = UInt256.ofNat (fromByteArrayBigEndian (o'.extract 128 160)))
    (hlive : catSlotWord ⟨2⟩ σu I ≠ ⟨1⟩) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hdepthNe : I.depth ≠ 1024 := by omega
  have hmemI : 196 ≤ (catBiteIlksPostCallMem I o').size := by
    have h := catBiteIlksPostCallMem_size I o' hilkslen hosz; omega
  have hbaseSz : (biteUrnsCalldataMem (biteIlkWord I) (biteUrnWord I)
      (catBiteIlksPostCallMem I o')).size = 288 := by
    rw [biteUrnsCalldataMem_size hmemI, catBiteIlksPostCallMem_size I o' hilkslen hosz]
  have hlen64 : ((⟨64⟩ : UInt256) ⊓ UInt256.ofNat ou.size).toNat = 64 :=
    umin_ofNat_right_toNat_of_ge (c := 64) (n := ou.size) (by decide) hurnslen hoszu
  have hmemsz : 228 ≤ (catBiteUrnsPostCallMem I (catBiteIlksPostCallMem I o') ou).size := by
    unfold catBiteUrnsPostCallMem
    rw [hlen64, show (⟨128⟩ : UInt256).toNat = 128 from by native_decide,
      write_eq_gen ou _ 128 64 (by decide) (by omega) (by rw [hbaseSz]; omega),
      ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
      ByteArray.size_extract, ByteArray.size_extract, hbaseSz]
    omega
  have hFree64 : (catBiteUrnsPostCallMem I (catBiteIlksPostCallMem I o') ou).readWithPadding 64 32
      = UInt256.toByteArray ⟨128⟩ :=
    catBiteUrnsPostCallMem_read64 I ou hmemI (catBiteIlksPostCallMem_read64 I o' hilkslen hosz)
      hurnslen hoszu
  set art := UInt256.ofNat (fromByteArrayBigEndian (ou.extract 32 64)) with hart
  set ink := UInt256.ofNat (fromByteArrayBigEndian (ou.extract 0 32)) with hink
  have hInk : (catBiteUrnsPostCallMem I (catBiteIlksPostCallMem I o') ou).readWithPadding 128 32
      = UInt256.toByteArray ink :=
    catBiteUrnsPostCallMem_read128 I ou hmemI hurnslen hoszu
  have hArt : (catBiteUrnsPostCallMem I (catBiteIlksPostCallMem I o') ou).readWithPadding 160 32
      = UInt256.toByteArray art :=
    catBiteUrnsPostCallMem_read160 I ou hmemI hurnslen hoszu
  -- Seg3 mload-value facts (fp / ink / art).
  have hnotge : ∀ off : UInt256, off.toNat ≤ 160 → ¬ (off ≥ aw * ⟨32⟩) := by
    intro off hoff hh
    have hle : (aw * ⟨32⟩).toNat ≤ off.toNat := hh
    rw [u256_mul_op_toNat, show (⟨32⟩ : UInt256).toNat = 32 from by decide,
      Nat.mod_eq_of_lt hawsz] at hle
    omega
  have h64Aw : UInt256.ofNat (MachineState.M aw.toNat 64 32) = aw := awInv32 aw (by omega)
  have h128Aw : UInt256.ofNat (MachineState.M aw.toNat 128 32) = aw := awInv32 aw (by omega)
  have h160Aw : UInt256.ofNat (MachineState.M aw.toNat 160 32) = aw := awInv32 aw (by omega)
  have hV64 : (if (⟨64⟩ : UInt256).toNat ≥
        (catBiteUrnsPostCallMem I (catBiteIlksPostCallMem I o') ou).size ∨ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩
      then ⟨0⟩ else UInt256.ofNat (fromByteArrayBigEndian
        ((catBiteUrnsPostCallMem I (catBiteIlksPostCallMem I o') ou).readWithPadding
          (⟨64⟩ : UInt256).toNat 32))) = ⟨128⟩ :=
    mloadWordValue_of_readWithPadding (off := ⟨64⟩) (v := ⟨128⟩) (by
      show (64 : ℕ) < (catBiteUrnsPostCallMem I (catBiteIlksPostCallMem I o') ou).size; omega)
      (hnotge ⟨64⟩ (by decide))
      (by rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide]; exact hFree64)
  have hVInk : (if (⟨128⟩ : UInt256).toNat ≥
        (catBiteUrnsPostCallMem I (catBiteIlksPostCallMem I o') ou).size ∨ (⟨128⟩ : UInt256) ≥ aw * ⟨32⟩
      then ⟨0⟩ else UInt256.ofNat (fromByteArrayBigEndian
        ((catBiteUrnsPostCallMem I (catBiteIlksPostCallMem I o') ou).readWithPadding
          (⟨128⟩ : UInt256).toNat 32))) = ink :=
    mloadWordValue_of_readWithPadding (off := ⟨128⟩) (v := ink) (by
      show (128 : ℕ) < (catBiteUrnsPostCallMem I (catBiteIlksPostCallMem I o') ou).size; omega)
      (hnotge ⟨128⟩ (by decide))
      (by rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide]; exact hInk)
  have hVArt : (if (⟨160⟩ : UInt256).toNat ≥
        (catBiteUrnsPostCallMem I (catBiteIlksPostCallMem I o') ou).size ∨ (⟨160⟩ : UInt256) ≥ aw * ⟨32⟩
      then ⟨0⟩ else UInt256.ofNat (fromByteArrayBigEndian
        ((catBiteUrnsPostCallMem I (catBiteIlksPostCallMem I o') ou).readWithPadding
          (⟨160⟩ : UInt256).toNat 32))) = art :=
    mloadWordValue_of_readWithPadding (off := ⟨160⟩) (v := art) (by
      show (160 : ℕ) < (catBiteUrnsPostCallMem I (catBiteIlksPostCallMem I o') ou).size; omega)
      (hnotge ⟨160⟩ (by decide))
      (by rw [show (⟨160⟩ : UInt256).toNat = 160 from by decide]; exact hArt)
  obtain ⟨_, _, rd1447⟩ := catBiteTraceSeg3 rd1399 hstatus hurnslen hoszu hV64
    (mloadCost0 h64Aw) h64Aw hVInk (mloadCost0 h128Aw) h128Aw hVArt (mloadCost0 h160Aw) h160Aw
    (by simp)
  obtain ⟨_, _, rd1458⟩ := catBiteReachGuardLive rd1447 (by simp)
  -- Solm-side ilks+urns + live-fail source.
  obtain ⟨σs, As, σus, Aus, hIlksSolm, hUrnsSolm, hAmEq, hvatCodeIlkS⟩ :=
    catBiteMapUrns hAccounts hdepthNe hUrnsVatCode hIlksCall hUrnsCall
  set eUrnS := { initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I with
    accountMap := σus, substate := Aus, createdAccounts := cAu } with heUrnSdef
  have heUSam : eUrnS.accountMap = σus := rfl
  have heUSee : eUrnS.executionEnv = I := rfl
  have slotEqUS : ∀ s : UInt256, solcSlotWord σus I s = solcSlotWord σu I s := by
    intro s; simp only [solcSlotWord]
    rw [accountMapEquiv_storage_findD hAmEq I.codeOwner s ⟨0⟩]
  have hbr : ∀ (o : ByteArray) (k : ℕ), k + 32 ≤ o.size →
      ABI.bytesToWord ((o.toList.drop k).take 32) =
        UInt256.ofNat (fromByteArrayBigEndian (o.extract k (k + 32))) := by
    intro o k h
    rw [decode_word_at_eq_any o k h, uInt256OfByteArray_eq]
    congr 1; unfold fromByteArrayBigEndian; congr 1
    rw [byteArray_toList_eq (o.readBytes k 32), readBytes_at_toList_any o k h,
      byteArray_toList_eq (o.extract k (k + 32)), ByteArray.data_extract, Array.toList_extract,
      List.extract_eq_take_drop]
    simp
  have hIlksDec : config.externalABI.decode? "ilks" o' =
      some [bw (UInt256.ofNat (fromByteArrayBigEndian (o'.extract 0 32))), bw iRate, bw iSpot,
        bw (UInt256.ofNat (fromByteArrayBigEndian (o'.extract 96 128))), bw iDust] := by
    have h := catBiteIlksDecode_ok hilkslen
    rw [hbr o' 0 (by omega), hbr o' 32 (by omega), hbr o' 64 (by omega),
      hbr o' 96 (by omega), hbr o' 128 (by omega)] at h
    rw [hiRate, hiSpot, hiDust]; exact h
  have hUrnsDec : config.externalABI.decode? "urns" ou = some [bw ink, bw art] := by
    have h := catBiteUrnsDecode_ok hurnslen
    rw [hbr ou 0 (by omega), hbr ou 32 (by omega)] at h
    rw [hink, hart]; exact h
  have hliveS : catSlotWord ⟨2⟩ eUrnS.accountMap eUrnS.executionEnv ≠ ⟨1⟩ := by
    rw [heUSam, heUSee]; simp only [catSlotWord]; rw [slotEqUS ⟨2⟩]
    simpa only [catSlotWord] using hlive
  have hcond : UInt256.eq ⟨1⟩ (catSlotWord ⟨2⟩ σu I) = ⟨0⟩ :=
    u256_eq_of_ne (fun h => hlive h.symm)
  have hbody := catBiteSourceLiveRevert hsz36 hwv
    (catBiteVatCodePos_of_uniswap hAccounts hvatCode) hIlksSolm hIlksDec hvatCodeIlkS
    hUrnsSolm hUrnsDec hliveS
  exact catBiteRequireStringRevertLeaf (okPc := ⟨1521⟩) (len := ⟨12⟩)
    (rawWord := ⟨0x4361742f6e6f742d6c697665⟩) (shift := ⟨160⟩) (op := .PUSH12) (width := 12)
    hcode hdispatch hdecode rd1458 hcond (by native_decide) (by native_decide)
    (by unfold solcErrorStringRevertTailWf; repeat' first | apply And.intro | native_decide)
    (by decide) rfl hmemsz (by omega) hawsz hFree64
    (by simp only [List.length_cons, List.length_nil]; omega) hbody


set_option maxHeartbeats 2000000 in
/-- **`unsafe` (`ink*spot ≥ art*rate`) require-string revert branch (extracted).** Pre-milk (aw=9)
`Seg5` guard: `require(spot > 0 && ink*spot < art*rate, "Cat/not-unsafe")` fails on the second
conjunct.  Reaches the guard at pc 1555 (`catBiteReachGuardUnsafe`, past `spot>0` + both muls), fires
`catBiteRequireStringRevertLeaf` (free ptr `0x80`) + `catBiteSourceInkSpotGeRevert` (or its `rate=0`
variant, split internally since `rate` is not yet known positive). -/
theorem catBiteRevertUnsafe {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {σ' σu : AccountMap} {A' Au : Substate}
    {cA' cAu : Batteries.RBSet AccountAddress compare} {o' ou : ByteArray} {ku Cu : ℕ}
    {aw : UInt256} {art ink iSpot iRate iDust : UInt256}
    (hcode : I.code = catBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hdispatch : dispatchMsg contract I.calldata = some biteTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (biteTransition.params.map Param.name)
        (transitionSignature biteTransition).paramTypes I.calldata = some (biteLocals I))
    (hAccounts : accountMapEquiv σ_evm σ_solm) (hsz36 : 36 ≤ I.calldata.size)
    (hdepth : (I.depth : ℕ) < 1024)
    (hvatCode : ¬ Reasoning.Theory.extCodeSizeWord σ_evm (catBiteVatTargetWord σ_evm I) = ⟨0⟩)
    (hUrnsVatCode :
      ¬ Reasoning.Theory.extCodeSizeWord σ' ((catSlotWord ⟨3⟩ σ' I).land biteAddrMaskWord) = ⟨0⟩)
    (hIlksCall :
      typedCallViaEVM config (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        (AccountAddress.ofUInt256 (catBiteVatTargetWord σ_evm I)) "ilks" 0 [biteIlkVal I]
        (true, { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
                  accountMap := σ', substate := A', createdAccounts := cA' }, o') false)
    (hUrnsCall :
      typedCallViaEVM config
        { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
            accountMap := σ', createdAccounts := cA' }
        (AccountAddress.ofUInt256 ((catSlotWord ⟨3⟩ σ' I).land biteAddrMaskWord)) "urns" 0
        [biteIlkVal I, biteUrnVal I]
        (true, { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
                  accountMap := σu, substate := Au, createdAccounts := cAu }, ou) false)
    (hilkslen : 160 ≤ o'.size) (hosz : o'.size < UInt256.size)
    (hurnslen : 64 ≤ ou.size) (hoszu : ou.size < UInt256.size)
    (hurn : biteAddrMaskWord.land (biteAddrMaskWord.land (calldataWord I.calldata 36)) = biteUrnWord I)
    (hlive : catSlotWord ⟨2⟩ σu I = ⟨1⟩)
    (rd1521 : RD catBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1521⟩
      (art :: ink :: iDust :: iSpot :: iRate :: ⟨0⟩ ::
        biteAddrMaskWord.land (calldataWord I.calldata 36) :: biteIlkWord I :: ⟨419⟩ :: catSelWord I :: [])
      (catBiteUrnsPostCallMem I (catBiteIlksPostCallMem I o') ou) aw ou (cAu, σu) ku Cu)
    (haw : 288 ≤ aw.toNat * 32) (hawsz : aw.toNat * 32 < UInt256.size)
    (hspotPos : 0 < iSpot.toNat)
    (hfitArtRate : art.toNat * iRate.toNat < UInt256.size)
    (hfitInkSpot : ink.toNat * iSpot.toNat < UInt256.size)
    (hart : art = UInt256.ofNat (fromByteArrayBigEndian (ou.extract 32 64)))
    (hink : ink = UInt256.ofNat (fromByteArrayBigEndian (ou.extract 0 32)))
    (hiSpot : iSpot = UInt256.ofNat (fromByteArrayBigEndian (o'.extract 64 96)))
    (hiRate : iRate = UInt256.ofNat (fromByteArrayBigEndian (o'.extract 32 64)))
    (hiDust : iDust = UInt256.ofNat (fromByteArrayBigEndian (o'.extract 128 160)))
    (hunsafeF : ¬ (ink * iSpot).toNat < (art * iRate).toNat) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hdepthNe : I.depth ≠ 1024 := by omega
  have hmemI : 196 ≤ (catBiteIlksPostCallMem I o').size := by
    have h := catBiteIlksPostCallMem_size I o' hilkslen hosz; omega
  have hbaseSz : (biteUrnsCalldataMem (biteIlkWord I) (biteUrnWord I)
      (catBiteIlksPostCallMem I o')).size = 288 := by
    rw [biteUrnsCalldataMem_size hmemI, catBiteIlksPostCallMem_size I o' hilkslen hosz]
  have hlen64 : ((⟨64⟩ : UInt256) ⊓ UInt256.ofNat ou.size).toNat = 64 :=
    umin_ofNat_right_toNat_of_ge (c := 64) (n := ou.size) (by decide) hurnslen hoszu
  have hmemsz : 228 ≤ (catBiteUrnsPostCallMem I (catBiteIlksPostCallMem I o') ou).size := by
    unfold catBiteUrnsPostCallMem
    rw [hlen64, show (⟨128⟩ : UInt256).toNat = 128 from by native_decide,
      write_eq_gen ou _ 128 64 (by decide) (by omega) (by rw [hbaseSz]; omega),
      ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
      ByteArray.size_extract, ByteArray.size_extract, hbaseSz]
    omega
  have hFree64 : (catBiteUrnsPostCallMem I (catBiteIlksPostCallMem I o') ou).readWithPadding 64 32
      = UInt256.toByteArray ⟨128⟩ :=
    catBiteUrnsPostCallMem_read64 I ou hmemI (catBiteIlksPostCallMem_read64 I o' hilkslen hosz)
      hurnslen hoszu
  obtain ⟨_, _, rd1555⟩ := catBiteReachGuardUnsafe rd1521 hspotPos hfitArtRate hfitInkSpot (by simp)
  obtain ⟨σs, As, σus, Aus, hIlksSolm, hUrnsSolm, hAmEq, hvatCodeIlkS⟩ :=
    catBiteMapUrns hAccounts hdepthNe hUrnsVatCode hIlksCall hUrnsCall
  set eUrnS := { initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I with
    accountMap := σus, substate := Aus, createdAccounts := cAu } with heUrnSdef
  have heUSam : eUrnS.accountMap = σus := rfl
  have heUSee : eUrnS.executionEnv = I := rfl
  have slotEqUS : ∀ s : UInt256, solcSlotWord σus I s = solcSlotWord σu I s := by
    intro s; simp only [solcSlotWord]
    rw [accountMapEquiv_storage_findD hAmEq I.codeOwner s ⟨0⟩]
  have hbr : ∀ (o : ByteArray) (k : ℕ), k + 32 ≤ o.size →
      ABI.bytesToWord ((o.toList.drop k).take 32) =
        UInt256.ofNat (fromByteArrayBigEndian (o.extract k (k + 32))) := by
    intro o k h
    rw [decode_word_at_eq_any o k h, uInt256OfByteArray_eq]
    congr 1; unfold fromByteArrayBigEndian; congr 1
    rw [byteArray_toList_eq (o.readBytes k 32), readBytes_at_toList_any o k h,
      byteArray_toList_eq (o.extract k (k + 32)), ByteArray.data_extract, Array.toList_extract,
      List.extract_eq_take_drop]
    simp
  have hIlksDec : config.externalABI.decode? "ilks" o' =
      some [bw (UInt256.ofNat (fromByteArrayBigEndian (o'.extract 0 32))), bw iRate, bw iSpot,
        bw (UInt256.ofNat (fromByteArrayBigEndian (o'.extract 96 128))), bw iDust] := by
    have h := catBiteIlksDecode_ok hilkslen
    rw [hbr o' 0 (by omega), hbr o' 32 (by omega), hbr o' 64 (by omega),
      hbr o' 96 (by omega), hbr o' 128 (by omega)] at h
    rw [hiRate, hiSpot, hiDust]; exact h
  have hUrnsDec : config.externalABI.decode? "urns" ou = some [bw ink, bw art] := by
    have h := catBiteUrnsDecode_ok hurnslen
    rw [hbr ou 0 (by omega), hbr ou 32 (by omega)] at h
    rw [hink, hart]; exact h
  have hlive' : catSlotWord ⟨2⟩ eUrnS.accountMap eUrnS.executionEnv = ⟨1⟩ := by
    rw [heUSam, heUSee]; simp only [catSlotWord]; rw [slotEqUS ⟨2⟩]
    simpa only [catSlotWord] using hlive
  have hge : (art * iRate).toNat ≤ (ink * iSpot).toNat := Nat.le_of_not_lt hunsafeF
  have hcond : UInt256.lt (UInt256.mul ink iSpot) (UInt256.mul art iRate) = ⟨0⟩ := ult_zero hge
  have hbody :
      ExecTransitionBody config contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) (biteLocals I)
        biteTransition.body .reverted := by
    by_cases hRatePos : 0 < iRate.toNat
    · exact catBiteSourceInkSpotGeRevert hwv
        (catBiteVatCodePos_of_uniswap hAccounts hvatCode) hIlksSolm hIlksDec hvatCodeIlkS
        hUrnsSolm hUrnsDec hlive' hfitInkSpot hfitArtRate hspotPos hRatePos hge
    · exact catBiteSourceInkSpotGeRateZeroRevert hwv
        (catBiteVatCodePos_of_uniswap hAccounts hvatCode) hIlksSolm hIlksDec hvatCodeIlkS
        hUrnsSolm hUrnsDec hlive' hfitInkSpot hfitArtRate hspotPos (by omega) hge
  exact catBiteRequireStringRevertLeaf (okPc := ⟨1620⟩) (len := ⟨14⟩)
    (rawWord := ⟨0x4361742f6e6f742d756e73616665⟩) (shift := ⟨144⟩) (op := .PUSH14) (width := 14)
    hcode hdispatch hdecode rd1555 hcond (by native_decide) (by native_decide)
    (by unfold solcErrorStringRevertTailWf; repeat' first | apply And.intro | native_decide)
    (by decide) rfl hmemsz (by omega) hawsz hFree64
    (by simp only [List.length_cons, List.length_nil]; omega) hbody


set_option maxHeartbeats 2000000 in
/-- **`spot = 0` short-circuit require-string revert branch (extracted).** Pre-milk (aw=9) `Seg5`
guard: `require(spot > 0 && …, "Cat/not-unsafe")` fails on the FIRST conjunct (`spot = 0`
short-circuit).  Reaches the guard at pc 1555 (`catBiteReachGuardSpot`) with `cond = ⟨0⟩`, fires
`catBiteRequireStringRevertLeaf` + `catBiteSourceSpotZeroRevert` (or its `rate=0` variant). -/
theorem catBiteRevertSpotZero {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {σ' σu : AccountMap} {A' Au : Substate}
    {cA' cAu : Batteries.RBSet AccountAddress compare} {o' ou : ByteArray} {ku Cu : ℕ}
    {aw : UInt256} {art ink iSpot iRate iDust : UInt256}
    (hcode : I.code = catBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hdispatch : dispatchMsg contract I.calldata = some biteTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (biteTransition.params.map Param.name)
        (transitionSignature biteTransition).paramTypes I.calldata = some (biteLocals I))
    (hAccounts : accountMapEquiv σ_evm σ_solm) (hsz36 : 36 ≤ I.calldata.size)
    (hdepth : (I.depth : ℕ) < 1024)
    (hvatCode : ¬ Reasoning.Theory.extCodeSizeWord σ_evm (catBiteVatTargetWord σ_evm I) = ⟨0⟩)
    (hUrnsVatCode :
      ¬ Reasoning.Theory.extCodeSizeWord σ' ((catSlotWord ⟨3⟩ σ' I).land biteAddrMaskWord) = ⟨0⟩)
    (hIlksCall :
      typedCallViaEVM config (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        (AccountAddress.ofUInt256 (catBiteVatTargetWord σ_evm I)) "ilks" 0 [biteIlkVal I]
        (true, { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
                  accountMap := σ', substate := A', createdAccounts := cA' }, o') false)
    (hUrnsCall :
      typedCallViaEVM config
        { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
            accountMap := σ', createdAccounts := cA' }
        (AccountAddress.ofUInt256 ((catSlotWord ⟨3⟩ σ' I).land biteAddrMaskWord)) "urns" 0
        [biteIlkVal I, biteUrnVal I]
        (true, { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
                  accountMap := σu, substate := Au, createdAccounts := cAu }, ou) false)
    (hilkslen : 160 ≤ o'.size) (hosz : o'.size < UInt256.size)
    (hurnslen : 64 ≤ ou.size) (hoszu : ou.size < UInt256.size)
    (hurn : biteAddrMaskWord.land (biteAddrMaskWord.land (calldataWord I.calldata 36)) = biteUrnWord I)
    (hlive : catSlotWord ⟨2⟩ σu I = ⟨1⟩)
    (rd1521 : RD catBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1521⟩
      (art :: ink :: iDust :: iSpot :: iRate :: ⟨0⟩ ::
        biteAddrMaskWord.land (calldataWord I.calldata 36) :: biteIlkWord I :: ⟨419⟩ :: catSelWord I :: [])
      (catBiteUrnsPostCallMem I (catBiteIlksPostCallMem I o') ou) aw ou (cAu, σu) ku Cu)
    (haw : 288 ≤ aw.toNat * 32) (hawsz : aw.toNat * 32 < UInt256.size)
    (hspot0 : iSpot = ⟨0⟩)
    (hfitArtRate : art.toNat * iRate.toNat < UInt256.size)
    (hfitInkSpot : ink.toNat * iSpot.toNat < UInt256.size)
    (hart : art = UInt256.ofNat (fromByteArrayBigEndian (ou.extract 32 64)))
    (hink : ink = UInt256.ofNat (fromByteArrayBigEndian (ou.extract 0 32)))
    (hiSpot : iSpot = UInt256.ofNat (fromByteArrayBigEndian (o'.extract 64 96)))
    (hiRate : iRate = UInt256.ofNat (fromByteArrayBigEndian (o'.extract 32 64)))
    (hiDust : iDust = UInt256.ofNat (fromByteArrayBigEndian (o'.extract 128 160))) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hdepthNe : I.depth ≠ 1024 := by omega
  have hspot0N : iSpot.toNat = 0 := by rw [hspot0]; native_decide
  have hmemI : 196 ≤ (catBiteIlksPostCallMem I o').size := by
    have h := catBiteIlksPostCallMem_size I o' hilkslen hosz; omega
  have hbaseSz : (biteUrnsCalldataMem (biteIlkWord I) (biteUrnWord I)
      (catBiteIlksPostCallMem I o')).size = 288 := by
    rw [biteUrnsCalldataMem_size hmemI, catBiteIlksPostCallMem_size I o' hilkslen hosz]
  have hlen64 : ((⟨64⟩ : UInt256) ⊓ UInt256.ofNat ou.size).toNat = 64 :=
    umin_ofNat_right_toNat_of_ge (c := 64) (n := ou.size) (by decide) hurnslen hoszu
  have hmemsz : 228 ≤ (catBiteUrnsPostCallMem I (catBiteIlksPostCallMem I o') ou).size := by
    unfold catBiteUrnsPostCallMem
    rw [hlen64, show (⟨128⟩ : UInt256).toNat = 128 from by native_decide,
      write_eq_gen ou _ 128 64 (by decide) (by omega) (by rw [hbaseSz]; omega),
      ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
      ByteArray.size_extract, ByteArray.size_extract, hbaseSz]
    omega
  have hFree64 : (catBiteUrnsPostCallMem I (catBiteIlksPostCallMem I o') ou).readWithPadding 64 32
      = UInt256.toByteArray ⟨128⟩ :=
    catBiteUrnsPostCallMem_read64 I ou hmemI (catBiteIlksPostCallMem_read64 I o' hilkslen hosz)
      hurnslen hoszu
  obtain ⟨_, _, rd1555⟩ := catBiteReachGuardSpot rd1521 hspot0 (by simp)
  obtain ⟨σs, As, σus, Aus, hIlksSolm, hUrnsSolm, hAmEq, hvatCodeIlkS⟩ :=
    catBiteMapUrns hAccounts hdepthNe hUrnsVatCode hIlksCall hUrnsCall
  set eUrnS := { initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I with
    accountMap := σus, substate := Aus, createdAccounts := cAu } with heUrnSdef
  have heUSam : eUrnS.accountMap = σus := rfl
  have heUSee : eUrnS.executionEnv = I := rfl
  have slotEqUS : ∀ s : UInt256, solcSlotWord σus I s = solcSlotWord σu I s := by
    intro s; simp only [solcSlotWord]
    rw [accountMapEquiv_storage_findD hAmEq I.codeOwner s ⟨0⟩]
  have hbr : ∀ (o : ByteArray) (k : ℕ), k + 32 ≤ o.size →
      ABI.bytesToWord ((o.toList.drop k).take 32) =
        UInt256.ofNat (fromByteArrayBigEndian (o.extract k (k + 32))) := by
    intro o k h
    rw [decode_word_at_eq_any o k h, uInt256OfByteArray_eq]
    congr 1; unfold fromByteArrayBigEndian; congr 1
    rw [byteArray_toList_eq (o.readBytes k 32), readBytes_at_toList_any o k h,
      byteArray_toList_eq (o.extract k (k + 32)), ByteArray.data_extract, Array.toList_extract,
      List.extract_eq_take_drop]
    simp
  have hIlksDec : config.externalABI.decode? "ilks" o' =
      some [bw (UInt256.ofNat (fromByteArrayBigEndian (o'.extract 0 32))), bw iRate, bw iSpot,
        bw (UInt256.ofNat (fromByteArrayBigEndian (o'.extract 96 128))), bw iDust] := by
    have h := catBiteIlksDecode_ok hilkslen
    rw [hbr o' 0 (by omega), hbr o' 32 (by omega), hbr o' 64 (by omega),
      hbr o' 96 (by omega), hbr o' 128 (by omega)] at h
    rw [hiRate, hiSpot, hiDust]; exact h
  have hUrnsDec : config.externalABI.decode? "urns" ou = some [bw ink, bw art] := by
    have h := catBiteUrnsDecode_ok hurnslen
    rw [hbr ou 0 (by omega), hbr ou 32 (by omega)] at h
    rw [hink, hart]; exact h
  have hlive' : catSlotWord ⟨2⟩ eUrnS.accountMap eUrnS.executionEnv = ⟨1⟩ := by
    rw [heUSam, heUSee]; simp only [catSlotWord]; rw [slotEqUS ⟨2⟩]
    simpa only [catSlotWord] using hlive
  have hbody :
      ExecTransitionBody config contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) (biteLocals I)
        biteTransition.body .reverted := by
    by_cases hRatePos : 0 < iRate.toNat
    · exact catBiteSourceSpotZeroRevert hwv
        (catBiteVatCodePos_of_uniswap hAccounts hvatCode) hIlksSolm hIlksDec hvatCodeIlkS
        hUrnsSolm hUrnsDec hlive' hfitInkSpot hfitArtRate hRatePos hspot0N
    · exact catBiteSourceSpotZeroRateZeroRevert hwv
        (catBiteVatCodePos_of_uniswap hAccounts hvatCode) hIlksSolm hIlksDec hvatCodeIlkS
        hUrnsSolm hUrnsDec hlive' hfitInkSpot hfitArtRate (by omega) hspot0N
  exact catBiteRequireStringRevertLeaf (okPc := ⟨1620⟩) (len := ⟨14⟩)
    (rawWord := ⟨0x4361742f6e6f742d756e73616665⟩) (shift := ⟨144⟩) (op := .PUSH14) (width := 14)
    hcode hdispatch hdecode rd1555 rfl (by native_decide) (by native_decide)
    (by unfold solcErrorStringRevertTailWf; repeat' first | apply And.intro | native_decide)
    (by decide) rfl hmemsz (by omega) hawsz hFree64
    (by simp only [List.length_cons, List.length_nil]; omega) hbody


set_option maxHeartbeats 2000000 in
/-- **artRate (art·rate) checkedMul-overflow branch (extracted).** Pre-milk (aw=9) `Seg5`: `art*rate`
overflows.  EVM evaluates `art*rate` first, so on `spot > 0` it reaches the `@3720` `checkedMul`
(`catBiteReachGuardArtRate`) and mul-overflow-reverts (Solm body split on whether `ink*spot` also
overflows); on `spot = 0` it short-circuits to the `"Cat/not-unsafe"` string revert
(`catBiteReachGuardSpot`, Solm reverts on `art*rate` via `catBiteSourceArtRateOverflowSpotZeroRevert`). -/
theorem catBiteRevertArtRate {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {σ' σu : AccountMap} {A' Au : Substate}
    {cA' cAu : Batteries.RBSet AccountAddress compare} {o' ou : ByteArray} {ku Cu : ℕ}
    {aw : UInt256} {art ink iSpot iRate iDust : UInt256}
    (hcode : I.code = catBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hdispatch : dispatchMsg contract I.calldata = some biteTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (biteTransition.params.map Param.name)
        (transitionSignature biteTransition).paramTypes I.calldata = some (biteLocals I))
    (hAccounts : accountMapEquiv σ_evm σ_solm) (hsz36 : 36 ≤ I.calldata.size)
    (hdepth : (I.depth : ℕ) < 1024)
    (hvatCode : ¬ Reasoning.Theory.extCodeSizeWord σ_evm (catBiteVatTargetWord σ_evm I) = ⟨0⟩)
    (hUrnsVatCode :
      ¬ Reasoning.Theory.extCodeSizeWord σ' ((catSlotWord ⟨3⟩ σ' I).land biteAddrMaskWord) = ⟨0⟩)
    (hIlksCall :
      typedCallViaEVM config (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        (AccountAddress.ofUInt256 (catBiteVatTargetWord σ_evm I)) "ilks" 0 [biteIlkVal I]
        (true, { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
                  accountMap := σ', substate := A', createdAccounts := cA' }, o') false)
    (hUrnsCall :
      typedCallViaEVM config
        { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
            accountMap := σ', createdAccounts := cA' }
        (AccountAddress.ofUInt256 ((catSlotWord ⟨3⟩ σ' I).land biteAddrMaskWord)) "urns" 0
        [biteIlkVal I, biteUrnVal I]
        (true, { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
                  accountMap := σu, substate := Au, createdAccounts := cAu }, ou) false)
    (hilkslen : 160 ≤ o'.size) (hosz : o'.size < UInt256.size)
    (hurnslen : 64 ≤ ou.size) (hoszu : ou.size < UInt256.size)
    (hurn : biteAddrMaskWord.land (biteAddrMaskWord.land (calldataWord I.calldata 36)) = biteUrnWord I)
    (hlive : catSlotWord ⟨2⟩ σu I = ⟨1⟩)
    (rd1521 : RD catBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1521⟩
      (art :: ink :: iDust :: iSpot :: iRate :: ⟨0⟩ ::
        biteAddrMaskWord.land (calldataWord I.calldata 36) :: biteIlkWord I :: ⟨419⟩ :: catSelWord I :: [])
      (catBiteUrnsPostCallMem I (catBiteIlksPostCallMem I o') ou) aw ou (cAu, σu) ku Cu)
    (haw : 288 ≤ aw.toNat * 32) (hawsz : aw.toNat * 32 < UInt256.size)
    (hart : art = UInt256.ofNat (fromByteArrayBigEndian (ou.extract 32 64)))
    (hink : ink = UInt256.ofNat (fromByteArrayBigEndian (ou.extract 0 32)))
    (hiSpot : iSpot = UInt256.ofNat (fromByteArrayBigEndian (o'.extract 64 96)))
    (hiRate : iRate = UInt256.ofNat (fromByteArrayBigEndian (o'.extract 32 64)))
    (hiDust : iDust = UInt256.ofNat (fromByteArrayBigEndian (o'.extract 128 160)))
    (hfitArtRateF : ¬ art.toNat * iRate.toNat < UInt256.size) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hdepthNe : I.depth ≠ 1024 := by omega
  have hsz_pos : 0 < UInt256.size := by rw [show UInt256.size = 2 ^ 256 from rfl]; positivity
  have hover : UInt256.size ≤ art.toNat * iRate.toNat := Nat.le_of_not_lt hfitArtRateF
  obtain ⟨σs, As, σus, Aus, hIlksSolm, hUrnsSolm, hAmEq, hvatCodeIlkS⟩ :=
    catBiteMapUrns hAccounts hdepthNe hUrnsVatCode hIlksCall hUrnsCall
  set eUrnS := { initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I with
    accountMap := σus, substate := Aus, createdAccounts := cAu } with heUrnSdef
  have heUSam : eUrnS.accountMap = σus := rfl
  have heUSee : eUrnS.executionEnv = I := rfl
  have slotEqUS : ∀ s : UInt256, solcSlotWord σus I s = solcSlotWord σu I s := by
    intro s; simp only [solcSlotWord]
    rw [accountMapEquiv_storage_findD hAmEq I.codeOwner s ⟨0⟩]
  have hbr : ∀ (o : ByteArray) (k : ℕ), k + 32 ≤ o.size →
      ABI.bytesToWord ((o.toList.drop k).take 32) =
        UInt256.ofNat (fromByteArrayBigEndian (o.extract k (k + 32))) := by
    intro o k h
    rw [decode_word_at_eq_any o k h, uInt256OfByteArray_eq]
    congr 1; unfold fromByteArrayBigEndian; congr 1
    rw [byteArray_toList_eq (o.readBytes k 32), readBytes_at_toList_any o k h,
      byteArray_toList_eq (o.extract k (k + 32)), ByteArray.data_extract, Array.toList_extract,
      List.extract_eq_take_drop]
    simp
  have hIlksDec : config.externalABI.decode? "ilks" o' =
      some [bw (UInt256.ofNat (fromByteArrayBigEndian (o'.extract 0 32))), bw iRate, bw iSpot,
        bw (UInt256.ofNat (fromByteArrayBigEndian (o'.extract 96 128))), bw iDust] := by
    have h := catBiteIlksDecode_ok hilkslen
    rw [hbr o' 0 (by omega), hbr o' 32 (by omega), hbr o' 64 (by omega),
      hbr o' 96 (by omega), hbr o' 128 (by omega)] at h
    rw [hiRate, hiSpot, hiDust]; exact h
  have hUrnsDec : config.externalABI.decode? "urns" ou = some [bw ink, bw art] := by
    have h := catBiteUrnsDecode_ok hurnslen
    rw [hbr ou 0 (by omega), hbr ou 32 (by omega)] at h
    rw [hink, hart]; exact h
  have hlive' : catSlotWord ⟨2⟩ eUrnS.accountMap eUrnS.executionEnv = ⟨1⟩ := by
    rw [heUSam, heUSee]; simp only [catSlotWord]; rw [slotEqUS ⟨2⟩]
    simpa only [catSlotWord] using hlive
  by_cases hspotPos : 0 < iSpot.toNat
  · obtain ⟨_, _, rd3720⟩ := catBiteReachGuardArtRate rd1521 hspotPos (by simp)
    have hbody :
        ExecTransitionBody config contract
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) (biteLocals I)
          biteTransition.body .reverted := by
      by_cases hfitInkSpot : ink.toNat * iSpot.toNat < UInt256.size
      · exact catBiteSourceArtRateOverflowRevert hwv
          (catBiteVatCodePos_of_uniswap hAccounts hvatCode) hIlksSolm hIlksDec hvatCodeIlkS
          hUrnsSolm hUrnsDec hlive' hfitInkSpot hspotPos hover
      · exact catBiteSourceInkSpotOverflowRevert hwv
          (catBiteVatCodePos_of_uniswap hAccounts hvatCode) hIlksSolm hIlksDec hvatCodeIlkS
          hUrnsSolm hUrnsDec hlive' (Nat.le_of_not_lt hfitInkSpot)
    exact catBiteMulOverflowRevertLeaf hcode hdispatch hdecode rd3720
      (by rw [Nat.mul_comm]; exact hover)
      (by simp only [List.length_cons, List.length_nil]; omega) hbody
  · have hspot0N : iSpot.toNat = 0 := Nat.le_zero.mp (Nat.not_lt.mp hspotPos)
    have hspot0 : iSpot = ⟨0⟩ := uint256_toNat_eq_zero hspot0N
    have hfitInkSpot0 : ink.toNat * iSpot.toNat < UInt256.size := by
      rw [hspot0N, Nat.mul_zero]; exact hsz_pos
    have hmemI : 196 ≤ (catBiteIlksPostCallMem I o').size := by
      have h := catBiteIlksPostCallMem_size I o' hilkslen hosz; omega
    have hbaseSz : (biteUrnsCalldataMem (biteIlkWord I) (biteUrnWord I)
        (catBiteIlksPostCallMem I o')).size = 288 := by
      rw [biteUrnsCalldataMem_size hmemI, catBiteIlksPostCallMem_size I o' hilkslen hosz]
    have hlen64 : ((⟨64⟩ : UInt256) ⊓ UInt256.ofNat ou.size).toNat = 64 :=
      umin_ofNat_right_toNat_of_ge (c := 64) (n := ou.size) (by decide) hurnslen hoszu
    have hmemsz : 228 ≤ (catBiteUrnsPostCallMem I (catBiteIlksPostCallMem I o') ou).size := by
      unfold catBiteUrnsPostCallMem
      rw [hlen64, show (⟨128⟩ : UInt256).toNat = 128 from by native_decide,
        write_eq_gen ou _ 128 64 (by decide) (by omega) (by rw [hbaseSz]; omega),
        ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
        ByteArray.size_extract, ByteArray.size_extract, hbaseSz]
      omega
    have hFree64 : (catBiteUrnsPostCallMem I (catBiteIlksPostCallMem I o') ou).readWithPadding 64 32
        = UInt256.toByteArray ⟨128⟩ :=
      catBiteUrnsPostCallMem_read64 I ou hmemI (catBiteIlksPostCallMem_read64 I o' hilkslen hosz)
        hurnslen hoszu
    obtain ⟨_, _, rd1555⟩ := catBiteReachGuardSpot rd1521 hspot0 (by simp)
    have hbody := catBiteSourceArtRateOverflowSpotZeroRevert hwv
      (catBiteVatCodePos_of_uniswap hAccounts hvatCode) hIlksSolm hIlksDec hvatCodeIlkS
      hUrnsSolm hUrnsDec hlive' hfitInkSpot0 hspot0N hover
    exact catBiteRequireStringRevertLeaf (okPc := ⟨1620⟩) (len := ⟨14⟩)
      (rawWord := ⟨0x4361742f6e6f742d756e73616665⟩) (shift := ⟨144⟩) (op := .PUSH14) (width := 14)
      hcode hdispatch hdecode rd1555 rfl (by native_decide) (by native_decide)
      (by unfold solcErrorStringRevertTailWf; repeat' first | apply And.intro | native_decide)
      (by decide) rfl hmemsz (by omega) hawsz hFree64
      (by simp only [List.length_cons, List.length_nil]; omega) hbody


set_option maxHeartbeats 2000000 in
/-- **ink·dart checkedMul-overflow branch (extracted).** Post-milk (aw=10) guard: reaches the
`ink * dart` `checkedMul` frame at pc 3720 (via `catBiteTraceSeg7a`/`Seg7b` + `catBiteReachGuardInkDart`),
fires `catBiteMulOverflowRevertLeaf` + `catBiteSourceInkDartOverflowRevert`. -/
theorem catBiteRevertInkDart {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {σ' σu : AccountMap} {A' Au : Substate}
    {cA' cAu : Batteries.RBSet AccountAddress compare} {o' ou : ByteArray} {ku Cu : ℕ}
    {art ink iSpot iRate iDust room milkChop milkDunk dunkRoom dunkRoomWad dartDenomRate
      dartCandidate dart q : UInt256}
    (hcode : I.code = catBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hdispatch : dispatchMsg contract I.calldata = some biteTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (biteTransition.params.map Param.name)
        (transitionSignature biteTransition).paramTypes I.calldata = some (biteLocals I))
    (hAccounts : accountMapEquiv σ_evm σ_solm) (hsz36 : 36 ≤ I.calldata.size)
    (hdepth : (I.depth : ℕ) < 1024)
    (hvatCode : ¬ Reasoning.Theory.extCodeSizeWord σ_evm (catBiteVatTargetWord σ_evm I) = ⟨0⟩)
    (hUrnsVatCode :
      ¬ Reasoning.Theory.extCodeSizeWord σ' ((catSlotWord ⟨3⟩ σ' I).land biteAddrMaskWord) = ⟨0⟩)
    (hIlksCall :
      typedCallViaEVM config (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        (AccountAddress.ofUInt256 (catBiteVatTargetWord σ_evm I)) "ilks" 0 [biteIlkVal I]
        (true, { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
                  accountMap := σ', substate := A', createdAccounts := cA' }, o') false)
    (hUrnsCall :
      typedCallViaEVM config
        { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
            accountMap := σ', createdAccounts := cA' }
        (AccountAddress.ofUInt256 ((catSlotWord ⟨3⟩ σ' I).land biteAddrMaskWord)) "urns" 0
        [biteIlkVal I, biteUrnVal I]
        (true, { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
                  accountMap := σu, substate := Au, createdAccounts := cAu }, ou) false)
    (hilkslen : 160 ≤ o'.size) (hurnslen : 64 ≤ ou.size)
    (hosz : o'.size < UInt256.size) (hoszu : ou.size < UInt256.size)
    (hurn : biteAddrMaskWord.land (biteAddrMaskWord.land (calldataWord I.calldata 36)) = biteUrnWord I)
    (hlive : catSlotWord ⟨2⟩ σu I = ⟨1⟩)
    (hmemI : 196 ≤ (catBiteIlksPostCallMem I o').size)
    (hmemUsz : 224 ≤ (catBiteUrnsPostCallMem I (catBiteIlksPostCallMem I o') ou).size)
    (hqNat : q.toNat = 224)
    (rd1708 : RD catBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1708⟩
      (room :: ⟨0⟩ :: ⟨0⟩ :: q :: art :: ink :: iDust :: iSpot :: iRate :: ⟨0⟩ ::
        biteAddrMaskWord.land (calldataWord I.calldata 36) :: biteIlkWord I :: ⟨419⟩ :: catSelWord I :: [])
      (catBiteMilkMem (catBiteUrnsPostCallMem I (catBiteIlksPostCallMem I o') ou) ⟨128⟩ (biteIlkWord I) q
        (biteAddrMaskWord.land (solcSlotWord σu I (solcMappingSlot ⟨1⟩ (biteIlkWord I)))) milkChop milkDunk)
      ⟨10⟩ ou (cAu, σu) ku Cu)
    (hChop : (if (⟨32⟩ + q).toNat ≥
          (catBiteMilkMem (catBiteUrnsPostCallMem I (catBiteIlksPostCallMem I o') ou) ⟨128⟩ (biteIlkWord I) q
            (biteAddrMaskWord.land (solcSlotWord σu I (solcMappingSlot ⟨1⟩ (biteIlkWord I)))) milkChop
            milkDunk).size ∨ (⟨32⟩ + q) ≥ (⟨10⟩ : UInt256) * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat (fromByteArrayBigEndian
        ((catBiteMilkMem (catBiteUrnsPostCallMem I (catBiteIlksPostCallMem I o') ou) ⟨128⟩ (biteIlkWord I) q
            (biteAddrMaskWord.land (solcSlotWord σu I (solcMappingSlot ⟨1⟩ (biteIlkWord I)))) milkChop
            milkDunk).readWithPadding (⟨32⟩ + q).toNat 32))) = milkChop)
    (hDunk : (if (⟨64⟩ + q).toNat ≥
          (catBiteMilkMem (catBiteUrnsPostCallMem I (catBiteIlksPostCallMem I o') ou) ⟨128⟩ (biteIlkWord I) q
            (biteAddrMaskWord.land (solcSlotWord σu I (solcMappingSlot ⟨1⟩ (biteIlkWord I)))) milkChop
            milkDunk).size ∨ (⟨64⟩ + q) ≥ (⟨10⟩ : UInt256) * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat (fromByteArrayBigEndian
        ((catBiteMilkMem (catBiteUrnsPostCallMem I (catBiteIlksPostCallMem I o') ou) ⟨128⟩ (biteIlkWord I) q
            (biteAddrMaskWord.land (solcSlotWord σu I (solcMappingSlot ⟨1⟩ (biteIlkWord I)))) milkChop
            milkDunk).readWithPadding (⟨64⟩ + q).toNat 32))) = milkDunk)
    (hlitterbox : (solcSlotWord σu I ⟨6⟩).toNat < (solcSlotWord σu I ⟨5⟩).toNat)
    (hroomdust : iDust.toNat ≤ room.toNat)
    (hunsafe : (ink * iSpot).toNat < (art * iRate).toNat)
    (hfitArtRate : art.toNat * iRate.toNat < UInt256.size)
    (hfitInkSpot : ink.toNat * iSpot.toNat < UInt256.size)
    (hspotPos : 0 < iSpot.toNat) (hRatePos : iRate ≠ ⟨0⟩) (hChopPos : milkChop ≠ ⟨0⟩)
    (hFitWad : (⟨1000000000000000000⟩ : UInt256).toNat * dunkRoom.toNat < UInt256.size)
    (hArtPos : art ≠ ⟨0⟩)
    (hFitInkDart : ¬ dart.toNat * ink.toNat < UInt256.size)
    (hart : art = UInt256.ofNat (fromByteArrayBigEndian (ou.extract 32 64)))
    (hink : ink = UInt256.ofNat (fromByteArrayBigEndian (ou.extract 0 32)))
    (hiSpot : iSpot = UInt256.ofNat (fromByteArrayBigEndian (o'.extract 64 96)))
    (hiRate : iRate = UInt256.ofNat (fromByteArrayBigEndian (o'.extract 32 64)))
    (hiDust : iDust = UInt256.ofNat (fromByteArrayBigEndian (o'.extract 128 160)))
    (hroomDef : room = (solcSlotWord σu I ⟨5⟩).sub (solcSlotWord σu I ⟨6⟩))
    (hmilkDunkDef : milkDunk = solcSlotWord σu I (solcMappingSlot ⟨1⟩ (biteIlkWord I) + ⟨2⟩))
    (hmilkChopDef : milkChop = solcSlotWord σu I (solcMappingSlot ⟨1⟩ (biteIlkWord I) + ⟨1⟩))
    (hdunkRoomDef : dunkRoom = if milkDunk.gt room = ⟨0⟩ then milkDunk else room)
    (hdunkRoomWadDef : dunkRoomWad = dunkRoom.mul ⟨1000000000000000000⟩)
    (hdartDenomDef : dartDenomRate = dunkRoomWad.div iRate)
    (hdartCandDef : dartCandidate = dartDenomRate.div milkChop)
    (hdartDef : dart = if art.gt dartCandidate = ⟨0⟩ then art else dartCandidate) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hdepthNe : I.depth ≠ 1024 := by omega
  have hposNe : ∀ w : UInt256, w ≠ ⟨0⟩ → 0 < w.toNat :=
    fun w hw => Nat.pos_of_ne_zero (fun h => hw (uint256_toNat_eq_zero h))
  obtain ⟨_, _, rd1810⟩ := catBiteTraceSeg7a rd1708 hlitterbox hroomdust (by simp)
  obtain ⟨_, _, rd1872⟩ := catBiteTraceSeg7b rd1810 hChop hDunk (by rw [hqNat]; native_decide)
    (by rw [hqNat]; native_decide) hRatePos hChopPos hdunkRoomDef.symm hFitWad hdunkRoomWadDef.symm
    hdartDenomDef.symm hdartCandDef.symm hdartDef.symm (by simp)
  obtain ⟨_, _, rd3720⟩ := catBiteReachGuardInkDart rd1872 (by simp)
  obtain ⟨σs, As, σus, Aus, hIlksSolm, hUrnsSolm, hAmEq, hvatCodeIlkS⟩ :=
    catBiteMapUrns hAccounts hdepthNe hUrnsVatCode hIlksCall hUrnsCall
  set eUrnS := { initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I with
    accountMap := σus, substate := Aus, createdAccounts := cAu } with heUrnSdef
  have heUSam : eUrnS.accountMap = σus := rfl
  have heUSee : eUrnS.executionEnv = I := rfl
  have slotEqUS : ∀ s : UInt256, solcSlotWord σus I s = solcSlotWord σu I s := by
    intro s; simp only [solcSlotWord]
    rw [accountMapEquiv_storage_findD hAmEq I.codeOwner s ⟨0⟩]
  have uminEq : ∀ a b : UInt256, (if UInt256.gt a b = ⟨0⟩ then a else b) = umin a b := by
    intro a b; unfold umin
    by_cases h : a.toNat ≤ b.toNat
    · rw [if_pos (ugt_zero h), if_pos h]
    · rw [if_neg (by rw [ugt_one (by omega)]; decide), if_neg h]
  have hbr : ∀ (o : ByteArray) (k : ℕ), k + 32 ≤ o.size →
      ABI.bytesToWord ((o.toList.drop k).take 32) =
        UInt256.ofNat (fromByteArrayBigEndian (o.extract k (k + 32))) := by
    intro o k h
    rw [decode_word_at_eq_any o k h, uInt256OfByteArray_eq]
    congr 1; unfold fromByteArrayBigEndian; congr 1
    rw [byteArray_toList_eq (o.readBytes k 32), readBytes_at_toList_any o k h,
      byteArray_toList_eq (o.extract k (k + 32)), ByteArray.data_extract, Array.toList_extract,
      List.extract_eq_take_drop]
    simp
  have hIlksDec : config.externalABI.decode? "ilks" o' =
      some [bw (UInt256.ofNat (fromByteArrayBigEndian (o'.extract 0 32))), bw iRate, bw iSpot,
        bw (UInt256.ofNat (fromByteArrayBigEndian (o'.extract 96 128))), bw iDust] := by
    have h := catBiteIlksDecode_ok hilkslen
    rw [hbr o' 0 (by omega), hbr o' 32 (by omega), hbr o' 64 (by omega),
      hbr o' 96 (by omega), hbr o' 128 (by omega)] at h
    rw [hiRate, hiSpot, hiDust]; exact h
  have hUrnsDec : config.externalABI.decode? "urns" ou = some [bw ink, bw art] := by
    have h := catBiteUrnsDecode_ok hurnslen
    rw [hbr ou 0 (by omega), hbr ou 32 (by omega)] at h
    rw [hink, hart]; exact h
  have hlive' : catSlotWord ⟨2⟩ eUrnS.accountMap eUrnS.executionEnv = ⟨1⟩ := by
    rw [heUSam, heUSee]; simp only [catSlotWord]; rw [slotEqUS ⟨2⟩]
    simpa only [catSlotWord] using hlive
  have hratePos : 0 < iRate.toNat := by
    by_contra hc
    have hr0 : iRate.toNat = 0 := by omega
    have hz : (art * iRate).toNat = 0 := by
      rw [u256_mul_op_toNat, hr0, Nat.mul_zero, Nat.zero_mod]
    omega
  have hboxB : biteBoxW eUrnS = solcSlotWord σu I ⟨5⟩ := by
    simp only [biteBoxW, catSlotWord, heUSam, heUSee]; exact slotEqUS ⟨5⟩
  have hlitB : biteLitW eUrnS = solcSlotWord σu I ⟨6⟩ := by
    simp only [biteLitW, catSlotWord, heUSam, heUSee]; exact slotEqUS ⟨6⟩
  have hroomB : biteRoomV eUrnS = room := by
    rw [hroomDef]; simp only [biteRoomV, hboxB, hlitB]
  have hdunkB : biteDunkW I eUrnS = milkDunk := by
    rw [hmilkDunkDef]
    simp only [biteDunkW, catSlotWord, heUSam, heUSee, biteDunkSlot, biteFlipSlot_eq hsz36]
    exact slotEqUS _
  have hchopB : biteChopW I eUrnS = milkChop := by
    rw [hmilkChopDef]
    simp only [biteChopW, catSlotWord, heUSam, heUSee, biteChopSlot, biteFlipSlot_eq hsz36]
    exact slotEqUS _
  have hdunkroomB : biteDunkRoomV I eUrnS = dunkRoom := by
    rw [hdunkRoomDef, uminEq milkDunk room]
    simp only [biteDunkRoomV, hdunkB, hroomB]
  have hwad : wadU = ⟨1000000000000000000⟩ := by native_decide
  have hdartvB : biteDartV I eUrnS iRate art = dart := by
    have hcand : biteDartCandV I eUrnS iRate = dartCandidate := by
      simp only [biteDartCandV, biteDartDenomV, biteDunkRoomWadV, hchopB, hdunkroomB, hwad,
        hdartCandDef, hdartDenomDef, hdunkRoomWadDef]
      rfl
    rw [hdartDef, uminEq art dartCandidate]
    simp only [biteDartV, hcand]
  have hlitLtBox : (biteLitW eUrnS).toNat < (biteBoxW eUrnS).toNat := by
    rw [hlitB, hboxB]; exact hlitterbox
  have hroomGeDust : iDust.toNat ≤ (biteRoomV eUrnS).toNat := by rw [hroomB]; exact hroomdust
  have hbody := catBiteSourceInkDartOverflowRevert hwv
    (catBiteVatCodePos_of_uniswap hAccounts hvatCode) hIlksSolm hIlksDec hvatCodeIlkS
    hUrnsSolm hUrnsDec hlive' hsz36 hfitInkSpot hfitArtRate hspotPos hratePos hunsafe hlitLtBox
    hroomGeDust (by rw [hdunkroomB, hwad, Nat.mul_comm]; exact hFitWad)
    (by rw [hchopB]; exact hposNe milkChop hChopPos)
    (by rw [hdartvB]; exact Nat.le_of_not_lt (by rw [Nat.mul_comm]; exact hFitInkDart))
  exact catBiteMulOverflowRevertLeaf hcode hdispatch hdecode rd3720
    (Nat.le_of_not_lt hFitInkDart) (by simp only [List.length_cons, List.length_nil]; omega) hbody


set_option maxHeartbeats 2000000 in
/-- **tabBase (dartRate·chop) checkedMul-overflow branch (extracted).** grab+fess succeed;
`tabBase = mul(dartRate, chop)` overflows.  Maps ilks+urns+grab+fess to σ_solm, reaches the shared
`@3720` `checkedMul` frame from the fess-success cursor (`catBiteTraceSeg7h` +
`catBiteReachGuardTabBase`), fires `catBiteMulOverflowRevertLeaf` +
`catBiteSourceTabBaseOverflowRevert`. -/
theorem catBiteRevertTabBase {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {σ' σu σg σf : AccountMap} {A' Au Ag Af : Substate}
    {cA' cAu cAg cAf : Batteries.RBSet AccountAddress compare} {o' ou og ofb : ByteArray}
    {mem2 : ByteArray} {aw2 : UInt256} {k2 C2 : ℕ}
    {status f0 f1 f2 q urn : UInt256}
    {art ink iSpot iRate iDust room milkDunk milkChop dunkRoom dunkRoomWad
      dartDenomRate dartCandidate dart inkDart dinkCandidate dink dartRate : UInt256}
    (hcode : I.code = catBytecode)
    (hdispatch : dispatchMsg contract I.calldata = some biteTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (biteTransition.params.map Param.name)
        (transitionSignature biteTransition).paramTypes I.calldata = some (biteLocals I))
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hwv : I.weiValue = ⟨0⟩) (hperm : I.perm = true) (hsz36 : 36 ≤ I.calldata.size)
    (hdepth : (I.depth : ℕ) < 1024)
    (hurn : biteAddrMaskWord.land (biteAddrMaskWord.land (calldataWord I.calldata 36)) = biteUrnWord I)
    (hilkslen : 160 ≤ o'.size) (hurnslen : 64 ≤ ou.size)
    (hlive : catSlotWord ⟨2⟩ σu I = ⟨1⟩)
    (hvatCode : ¬ Reasoning.Theory.extCodeSizeWord σ_evm (catBiteVatTargetWord σ_evm I) = ⟨0⟩)
    (hUrnsVatCode :
      ¬ Reasoning.Theory.extCodeSizeWord σ' ((catSlotWord ⟨3⟩ σ' I).land biteAddrMaskWord) = ⟨0⟩)
    (hGrabCode :
      ¬ Reasoning.Theory.extCodeSizeWord σu ((solcSlotWord σu I ⟨3⟩).land biteAddrMaskWord) = ⟨0⟩)
    (hFessCode :
      ¬ Reasoning.Theory.extCodeSizeWord σg (biteAddrMaskWord.land (solcSlotWord σg I ⟨4⟩)) = ⟨0⟩)
    (hIlksCall :
      typedCallViaEVM config (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        (AccountAddress.ofUInt256 (catBiteVatTargetWord σ_evm I)) "ilks" 0 [biteIlkVal I]
        (true, { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
                  accountMap := σ', substate := A', createdAccounts := cA' }, o') false)
    (hUrnsCall :
      typedCallViaEVM config
        { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
            accountMap := σ', createdAccounts := cA' }
        (AccountAddress.ofUInt256 ((catSlotWord ⟨3⟩ σ' I).land biteAddrMaskWord)) "urns" 0
        [biteIlkVal I, biteUrnVal I]
        (true, { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
                  accountMap := σu, substate := Au, createdAccounts := cAu }, ou) false)
    (hGrabCall :
      typedCallViaEVM config
        { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
            accountMap := σu, createdAccounts := cAu }
        (AccountAddress.ofUInt256 ((solcSlotWord σu I ⟨3⟩).land biteAddrMaskWord)) "grab" 0
        [Value.fixedBytes bytes32Width (EVM.Word.toBytesBE (biteIlkWord I)),
          Value.address (AccountAddress.ofNat
            (biteAddrMaskWord.land (biteAddrMaskWord.land (calldataWord I.calldata 36))).toNat),
          Value.address (AccountAddress.ofNat (UInt256.ofNat I.codeOwner.val).toNat),
          Value.address (AccountAddress.ofNat (biteAddrMaskWord.land (solcSlotWord σu I ⟨4⟩)).toNat),
          Value.int (-Int.ofNat dink.toNat), Value.int (-Int.ofNat dart.toNat)]
        (true, { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
                  accountMap := σg, substate := Ag, createdAccounts := cAg }, og) I.perm)
    (hFessCall :
      typedCallViaEVM config
        { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
            accountMap := σg, createdAccounts := cAg }
        (AccountAddress.ofUInt256 (biteAddrMaskWord.land (solcSlotWord σg I ⟨4⟩))) "fess" 0
        [Value.int (Int.ofNat dartRate.toNat)]
        (true, { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
                accountMap := σf, substate := Af, createdAccounts := cAf }, ofb) I.perm)
    (rd2300 :
      RD catBytecode I (Sat256.ofUInt256 g) (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        ⟨2300⟩ (status :: f0 :: f1 :: f2 :: dink :: dart :: q :: art :: ink :: iDust :: iSpot :: iRate ::
          ⟨0⟩ :: urn :: biteIlkWord I :: ⟨419⟩ :: catSelWord I :: []) mem2 aw2 ofb (cAf, σf) k2 C2)
    (hstatus : status ≠ ⟨0⟩)
    (hChop : (if (⟨32⟩ + q).toNat ≥ mem2.size ∨ (⟨32⟩ + q) ≥ aw2 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat (fromByteArrayBigEndian (mem2.readWithPadding (⟨32⟩ + q).toNat 32))) = milkChop)
    (haw : q.toNat + 64 ≤ aw2.toNat * 32) (hqsz : q.toNat + 64 < UInt256.size)
    (hRateFit : iRate.toNat * dart.toNat < UInt256.size)
    (hart : art = UInt256.ofNat (fromByteArrayBigEndian (ou.extract 32 64)))
    (hink : ink = UInt256.ofNat (fromByteArrayBigEndian (ou.extract 0 32)))
    (hiSpot : iSpot = UInt256.ofNat (fromByteArrayBigEndian (o'.extract 64 96)))
    (hiRate : iRate = UInt256.ofNat (fromByteArrayBigEndian (o'.extract 32 64)))
    (hiDustDef : iDust = UInt256.ofNat (fromByteArrayBigEndian (o'.extract 128 160)))
    (hroomDef : room = (solcSlotWord σu I ⟨5⟩).sub (solcSlotWord σu I ⟨6⟩))
    (hmilkDunkDef : milkDunk = solcSlotWord σu I (solcMappingSlot ⟨1⟩ (biteIlkWord I) + ⟨2⟩))
    (hmilkChopDef : milkChop = solcSlotWord σu I (solcMappingSlot ⟨1⟩ (biteIlkWord I) + ⟨1⟩))
    (hdunkRoomDef : dunkRoom = if milkDunk.gt room = ⟨0⟩ then milkDunk else room)
    (hdunkRoomWadDef : dunkRoomWad = dunkRoom.mul ⟨1000000000000000000⟩)
    (hdartDenomDef : dartDenomRate = dunkRoomWad.div iRate)
    (hdartCandDef : dartCandidate = dartDenomRate.div milkChop)
    (hdartDef : dart = if art.gt dartCandidate = ⟨0⟩ then art else dartCandidate)
    (hinkDartDef : inkDart = ink.mul dart)
    (hdinkCandDef : dinkCandidate = inkDart.div art)
    (hdinkDef : dink = if ink.gt dinkCandidate = ⟨0⟩ then ink else dinkCandidate)
    (hdartRateDef : dartRate = dart.mul iRate)
    (hspotPos : 0 < iSpot.toNat) (hfitArtRate : art.toNat * iRate.toNat < UInt256.size)
    (hfitInkSpot : ink.toNat * iSpot.toNat < UInt256.size)
    (hunsafe : (ink * iSpot).toNat < (art * iRate).toNat)
    (hlitterbox : (solcSlotWord σu I ⟨6⟩).toNat < (solcSlotWord σu I ⟨5⟩).toNat)
    (hroomdust : iDust.toNat ≤ room.toNat)
    (hRatePos : iRate ≠ ⟨0⟩) (hChopPos : milkChop ≠ ⟨0⟩)
    (hFitWad : (⟨1000000000000000000⟩ : UInt256).toNat * dunkRoom.toNat < UInt256.size)
    (hArtPos : art ≠ ⟨0⟩) (hFitInkDart : dart.toNat * ink.toNat < UInt256.size)
    (hDartPos : 0 < dart.toNat) (hDinkPos : 0 < dink.toNat)
    (hDartLim : dart.toNat ≤ (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨255⟩).toNat)
    (hDinkLim : dink.toNat ≤ (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨255⟩).toNat)
    (hChopNofit : ¬ milkChop.toNat * dartRate.toNat < UInt256.size) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hdepthNe : I.depth ≠ 1024 := by omega
  have hmask : biteAddrMaskWord = solcAddrMask := by native_decide
  have hposNe : ∀ w : UInt256, w ≠ ⟨0⟩ → 0 < w.toNat :=
    fun w hw => Nat.pos_of_ne_zero (fun h => hw (uint256_toNat_eq_zero h))
  have codePos : ∀ (e : EVM.State) (w : UInt256),
      extCodeSizeWord e.accountMap w ≠ ⟨0⟩ →
      0 < (UInt256.ofNat ((e.lookupAccount
        (AccountAddress.ofUInt256 w)).option 0
        (fun acc => acc.code.size))).toNat := by
    intro e w hw
    unfold extCodeSizeWord at hw
    simp only [State.lookupAccount]
    cases hf : e.accountMap.find? (AccountAddress.ofUInt256 w) with
    | none => rw [hf] at hw; simp [Option.option] at hw
    | some acc =>
        rw [hf] at hw
        simp only [Option.option, Function.comp] at hw ⊢
        exact hposNe _ hw
  have addrId : ∀ a : AccountAddress, EVM.address a.val = a := by
    intro a; apply Fin.ext
    show a.val % EVM.addressModulus = a.val
    rw [show EVM.addressModulus = AccountAddress.size from by decide]
    exact Nat.mod_eq_of_lt a.isLt
  have hAddrRT : ∀ a : AccountAddress,
      AccountAddress.ofNat (UInt256.ofNat a.val).toNat = a := by
    intro a
    have h1 : (UInt256.ofNat a.val).toNat = a.val :=
      UInt256.toNat_ofNat_of_lt (lt_of_lt_of_le a.isLt
        (show AccountAddress.size ≤ UInt256.size from by decide))
    rw [h1]; apply Fin.ext
    simp only [AccountAddress.ofNat, Fin.ofNat]
    exact Nat.mod_eq_of_lt a.isLt
  have hbytes : biteIlkBytes I = EVM.Word.toBytesBE (biteIlkWord I) := by
    have hlen32 : (biteIlkBytes I).length = 32 := by
      simp only [biteIlkBytes, List.length_take, List.length_drop]
      have htlen : I.calldata.toList.length = I.calldata.size := by
        rw [byteArray_toList_eq, Array.length_toList]; rfl
      rw [htlen]; omega
    have hword : ABI.bytesToWord (biteIlkBytes I) = biteIlkWord I := by
      simpa [biteIlkBytes, biteIlkWord] using
        (decode_word_at_eq_any I.calldata 4 (by simpa using hsz36))
    have hto := toBytesBE_bytesToWord_of_length (bs := biteIlkBytes I) hlen32
    rw [hword] at hto; exact hto.symm
  have uminEq : ∀ a b : UInt256,
      (if UInt256.gt a b = ⟨0⟩ then a else b) = umin a b := by
    intro a b; unfold umin
    by_cases h : a.toNat ≤ b.toNat
    · rw [if_pos (ugt_zero h), if_pos h]
    · rw [if_neg (by rw [ugt_one (by omega)]; decide), if_neg h]
  have hwad : wadU = ⟨1000000000000000000⟩ := by native_decide
  have hsl : (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨255⟩).toNat =
      57896044618658097711785492504343953926634992332820282019728792003956564819968 := by
    native_decide
  have hbr : ∀ (o : ByteArray) (k : ℕ), k + 32 ≤ o.size →
      ABI.bytesToWord ((o.toList.drop k).take 32) =
        UInt256.ofNat (fromByteArrayBigEndian (o.extract k (k + 32))) := by
    intro o k h
    rw [decode_word_at_eq_any o k h, uInt256OfByteArray_eq]
    congr 1; unfold fromByteArrayBigEndian; congr 1
    rw [byteArray_toList_eq (o.readBytes k 32),
      readBytes_at_toList_any o k h,
      byteArray_toList_eq (o.extract k (k + 32)),
      ByteArray.data_extract, Array.toList_extract,
      List.extract_eq_take_drop]
    simp
  obtain ⟨σs, As, σus, Aus, hIlksSolm, hUrnsSolm, hAmEq, hvatCodeIlkS⟩ :=
    catBiteMapUrns hAccounts hdepthNe hUrnsVatCode hIlksCall hUrnsCall
  have slotEqUS : ∀ s : UInt256, solcSlotWord σus I s = solcSlotWord σu I s := by
    intro s; simp only [solcSlotWord]
    rw [accountMapEquiv_storage_findD hAmEq I.codeOwner s ⟨0⟩]
  set eUrnE := { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
    accountMap := σu, substate := Au, createdAccounts := cAu } with heUrnEdef
  set eUrnS := { initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I with
    accountMap := σus, substate := Aus, createdAccounts := cAu } with heUrnSdef
  have hEqU : EVMStateEquiv eUrnE eUrnS := ⟨rfl, rfl, hAmEq⟩
  have heUEam : eUrnE.accountMap = σu := rfl
  have heUEee : eUrnE.executionEnv = I := rfl
  have heUSam : eUrnS.accountMap = σus := rfl
  have heUSee : eUrnS.executionEnv = I := rfl
  have hboxB : biteBoxW eUrnE = solcSlotWord σu I ⟨5⟩ := by
    simp only [biteBoxW, catSlotWord, heUEam, heUEee]
  have hlitB : biteLitW eUrnE = solcSlotWord σu I ⟨6⟩ := by
    simp only [biteLitW, catSlotWord, heUEam, heUEee]
  have hchopB : biteChopW I eUrnE = milkChop := by
    rw [hmilkChopDef]
    simp only [biteChopW, catSlotWord, heUEam, heUEee, biteChopSlot,
      biteFlipSlot_eq hsz36]
  have hdunkB : biteDunkW I eUrnE = milkDunk := by
    rw [hmilkDunkDef]
    simp only [biteDunkW, catSlotWord, heUEam, heUEee, biteDunkSlot,
      biteFlipSlot_eq hsz36]
  have hroomB : biteRoomV eUrnE = room := by
    rw [hroomDef]
    simp only [biteRoomV, biteBoxW, biteLitW, catSlotWord, heUEam, heUEee]
  have hdunkroomB : biteDunkRoomV I eUrnE = dunkRoom := by
    rw [hdunkRoomDef, uminEq milkDunk room]
    simp only [biteDunkRoomV, hdunkB, hroomB]
  have hdartvB : biteDartV I eUrnE iRate art = dart := by
    have hcand : biteDartCandV I eUrnE iRate = dartCandidate := by
      simp only [biteDartCandV, biteDartDenomV, biteDunkRoomWadV,
        hchopB, hdunkroomB, hwad, hdartCandDef, hdartDenomDef,
        hdunkRoomWadDef]
      rfl
    rw [hdartDef, uminEq art dartCandidate]
    simp only [biteDartV, hcand]
  have hdinkvB : biteDinkV I eUrnE iRate art ink = dink := by
    have hcand : biteDinkCandV I eUrnE iRate art ink = dinkCandidate := by
      simp only [biteDinkCandV, biteInkDartV, hdartvB, hdinkCandDef,
        hinkDartDef]
      rfl
    rw [hdinkDef, uminEq ink dinkCandidate]
    simp only [biteDinkV, hcand]
  have hdartrateBE : biteDartRateV I eUrnE iRate art = dartRate := by
    rw [hdartRateDef]; simp only [biteDartRateV, hdartvB]; rfl
  have hIlksDec : config.externalABI.decode? "ilks" o' =
      some [bw (UInt256.ofNat (fromByteArrayBigEndian (o'.extract 0 32))),
        bw iRate, bw iSpot,
        bw (UInt256.ofNat (fromByteArrayBigEndian (o'.extract 96 128))),
        bw iDust] := by
    have h := catBiteIlksDecode_ok hilkslen
    rw [hbr o' 0 (by omega), hbr o' 32 (by omega), hbr o' 64 (by omega),
      hbr o' 96 (by omega), hbr o' 128 (by omega)] at h
    rw [hiRate, hiSpot, hiDustDef]; exact h
  have hUrnsDec : config.externalABI.decode? "urns" ou =
      some [bw ink, bw art] := by
    have h := catBiteUrnsDecode_ok hurnslen
    rw [hbr ou 0 (by omega), hbr ou 32 (by omega)] at h
    rw [hink, hart]; exact h
  obtain ⟨AG, hGrabCall'⟩ :=
    biteTypedCallZeroSetSubstate hGrabCall
      (by simpa [initState] using hdepthNe) Au
  obtain ⟨σgs, Ags, hGrabSolm, hEqGrab⟩ :=
    catBiteMapCall hEqU hGrabCall' hdepthNe
  set eGrabE := { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
    accountMap := σg, substate := AG, createdAccounts := cAg } with heGrabEdef
  set eGrabS := { initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I with
    accountMap := σgs, substate := Ags, createdAccounts := cAg } with heGrabSdef
  have heGEam : eGrabE.accountMap = σg := rfl
  have heGEee : eGrabE.executionEnv = I := rfl
  have htgtU : EVM.address (biteVatAddr eUrnS).val =
      AccountAddress.ofUInt256 ((solcSlotWord σu I ⟨3⟩).land biteAddrMaskWord) := by
    rw [← biteVatAddr_eq_of_equiv hEqU, addrId,
      accountAddress_ofUInt256_eq_ofNat_toNat, hmask]
    simp only [biteVatAddr, catSlotWord, heUEam, heUEee]
  have h1 : biteIlkVal I =
      Value.fixedBytes bytes32Width (EVM.Word.toBytesBE (biteIlkWord I)) := by
    simp only [biteIlkVal, hbytes]
  have h2 : biteUrnVal I = Value.address (AccountAddress.ofNat
      (biteAddrMaskWord.land
        (biteAddrMaskWord.land (calldataWord I.calldata 36))).toNat) := by
    rw [hurn]
    simp only [biteUrnVal, biteUrnWord, biteUrnAddr, hAddrRT]
  have h3 : (eUrnS.executionEnv.codeOwner : AccountAddress) =
      AccountAddress.ofNat (UInt256.ofNat I.codeOwner.val).toNat := by
    rw [heUSee]; exact (hAddrRT I.codeOwner).symm
  have h4 : biteVowAddrV eUrnS = AccountAddress.ofNat
      (biteAddrMaskWord.land (solcSlotWord σu I ⟨4⟩)).toNat := by
    rw [← biteVowAddrV_eq_of_equiv hEqU]
    simp only [biteVowAddrV, catSlotWord, heUEam, heUEee, hmask]
    rw [u256_land_comm]
  have hdartvBS : biteDartV I eUrnS iRate art = dart := by
    rw [← biteDartV_eq_of_equiv hEqU]; exact hdartvB
  have hdinkvBS : biteDinkV I eUrnS iRate art ink = dink := by
    rw [← biteDinkV_eq_of_equiv hEqU]; exact hdinkvB
  have hdartrateBS : biteDartRateV I eUrnS iRate art = dartRate := by
    rw [← biteDartRateV_eq_of_equiv hEqU]; exact hdartrateBE
  have hGrabCodeS :
      ¬ Reasoning.Theory.extCodeSizeWord σus
        ((solcSlotWord σus I ⟨3⟩).land biteAddrMaskWord) = ⟨0⟩ := by
    rw [slotEqUS ⟨3⟩, ← extCodeSizeWord_accountMapEquiv hAmEq]
    exact hGrabCode
  rw [hperm, ← htgtU, ← h1, ← h2, ← h3, ← h4, ← hdinkvBS, ← hdartvBS]
    at hGrabSolm
  have hGrabDec : config.externalABI.decode? "grab" og = some [] := by
    simp [config, externalABI, decodeVoid?]
  obtain ⟨AF, hFessCall'⟩ :=
    biteTypedCallZeroSetSubstate hFessCall
      (by simpa [initState] using hdepthNe) AG
  obtain ⟨σfs, Afs, hFessSolm, _hEqFess⟩ :=
    catBiteMapCall hEqGrab hFessCall' hdepthNe
  have htgtF : EVM.address (biteVowAddrV eGrabS).val =
      AccountAddress.ofUInt256 (biteAddrMaskWord.land (solcSlotWord σg I ⟨4⟩)) := by
    rw [← biteVowAddrV_eq_of_equiv hEqGrab, addrId,
      accountAddress_ofUInt256_eq_ofNat_toNat, hmask, u256_land_comm]
    simp only [biteVowAddrV, catSlotWord, heGEam, heGEee]
  have hfessArg : bw (biteDartRateV I eUrnS iRate art) =
      Value.int (Int.ofNat dartRate.toNat) := by rw [hdartrateBS]
  rw [hperm, ← htgtF, ← hfessArg] at hFessSolm
  have hFessDec : config.externalABI.decode? "fess" ofb = some [] := by
    simp [config, externalABI, decodeVoid?]
  have hvowCodeS : 0 < (UInt256.ofNat
      ((eGrabS.lookupAccount (biteVowAddrV eGrabS)).option 0
        (fun acc => acc.code.size))).toNat := by
    rw [← biteVowAddrV_eq_of_equiv hEqGrab,
      ← biteCodeW_eq_of_equiv (biteVowAddrV eGrabE) hEqGrab]
    have haddr : biteVowAddrV eGrabE =
        AccountAddress.ofUInt256 ((solcSlotWord σg I ⟨4⟩).land solcAddrMask) := by
      rw [accountAddress_ofUInt256_eq_ofNat_toNat]
      simp only [biteVowAddrV, catSlotWord, heGEam, heGEee]
    rw [haddr]
    refine codePos eGrabE ((solcSlotWord σg I ⟨4⟩).land solcAddrMask) ?_
    rw [heGEam, u256_land_comm, ← hmask]; exact hFessCode
  have hlive' : catSlotWord ⟨2⟩ eUrnS.accountMap eUrnS.executionEnv = ⟨1⟩ := by
    rw [← biteSlotEqOfEquiv hEqU ⟨2⟩]; exact hlive
  -- Reach the shared `@3720` `checkedMul` frame from the fess-success cursor.
  obtain ⟨_, _, rd2321⟩ := catBiteTraceSeg7h rd2300 hstatus (by simp)
  obtain ⟨_, _, rd3720⟩ :=
    catBiteReachGuardTabBase rd2321 hChop haw hqsz hRateFit hdartRateDef.symm (by simp)
  refine catBiteMulOverflowRevertLeaf hcode hdispatch hdecode rd3720
    (Nat.le_of_not_lt hChopNofit)
    (by simp only [List.length_cons, List.length_nil]; omega) ?_
  refine catBiteSourceTabBaseOverflowRevert hwv
    (catBiteVatCodePos_of_uniswap hAccounts hvatCode) hIlksSolm hIlksDec
    hvatCodeIlkS hUrnsSolm hUrnsDec hlive' hsz36 hfitInkSpot hfitArtRate
    hspotPos (hposNe iRate hRatePos) hunsafe ?_ ?_ ?_ ?_ ?_
    (hposNe art hArtPos) ?_ ?_ ?_ ?_ ?_ hGrabSolm hGrabDec ?_ hvowCodeS hFessSolm hFessDec ?_
  · rw [← biteLitW_eq_of_equiv hEqU, ← biteBoxW_eq_of_equiv hEqU, hlitB, hboxB]
    exact hlitterbox
  · rw [← biteRoomV_eq_of_equiv hEqU, hroomB]; exact hroomdust
  · rw [← biteDunkRoomV_eq_of_equiv hEqU, hdunkroomB, hwad, Nat.mul_comm]
    exact hFitWad
  · rw [← biteChopW_eq_of_equiv hEqU, hchopB]; exact hposNe milkChop hChopPos
  · rw [← biteDartV_eq_of_equiv hEqU, hdartvB, Nat.mul_comm]; exact hFitInkDart
  · rw [← biteDartV_eq_of_equiv hEqU, hdartvB]; exact hDartPos
  · rw [← biteDinkV_eq_of_equiv hEqU, hdinkvB]; exact hDinkPos
  · rw [← biteDartV_eq_of_equiv hEqU, hdartvB]; simp only [int256Limit]
    exact Int.ofNat_le.mpr (hDartLim.trans_eq hsl)
  · rw [← biteDinkV_eq_of_equiv hEqU, hdinkvB]; simp only [int256Limit]
    exact Int.ofNat_le.mpr (hDinkLim.trans_eq hsl)
  · have haddr : biteVatAddr eUrnS =
        AccountAddress.ofUInt256 (catBiteVatTargetWord σus I) := by
      rw [accountAddress_ofUInt256_eq_ofNat_toNat]
      simp only [biteVatAddr, catBiteVatTargetWord, catAddressReturnWord,
        catSlotWord, heUSam, heUSee]
    rw [haddr]
    refine codePos eUrnS (catBiteVatTargetWord σus I) ?_
    rw [heUSam, show catBiteVatTargetWord σus I =
          (solcSlotWord σus I ⟨3⟩).land biteAddrMaskWord from by
        simp only [catBiteVatTargetWord, catAddressReturnWord, catSlotWord,
          hmask]]
    exact hGrabCodeS
  · rw [← biteDartV_eq_of_equiv hEqU, hdartvB, Nat.mul_comm]; exact hRateFit
  · rw [← biteDartRateV_eq_of_equiv hEqU, ← biteChopW_eq_of_equiv hEqU,
      hdartrateBE, hchopB, Nat.mul_comm]
    exact Nat.le_of_not_lt hChopNofit


/-! ## `ilks` return-decode-short extraction -/

/-- **`ilks` return-decode short.** A `< 160`-byte return does not ABI-decode to the 5-word
`(uint256,uint256,uint256,uint256,uint256)` tuple. Dual of `catBiteIlksDecode_ok`. -/
theorem catBiteIlksDecode_none {o : ByteArray} (hoLt : o.size < 160) :
    config.externalABI.decode? "ilks" o = none := by
  show ABI.decodeReturnValuesWithMode? DecodeMode.legacySolc05
    [abiUInt256, abiUInt256, abiUInt256, abiUInt256, abiUInt256] o = none
  have holen : o.toList.length = o.size := by rw [byteArray_toList_eq, Array.length_toList]; rfl
  have hnone : decodeScalarWordsWithMode? DecodeMode.legacySolc05
      [abiUInt256, abiUInt256, abiUInt256, abiUInt256, abiUInt256] o.toList 0 = none := by
    cases h : decodeScalarWordsWithMode? DecodeMode.legacySolc05
        [abiUInt256, abiUInt256, abiUInt256, abiUInt256, abiUInt256] o.toList 0 with
    | none => rfl
    | some vals =>
        exfalso
        have hlen := decodeScalarWordsWithMode?_some_length (by simp) h
        rw [holen] at hlen
        simp only [List.length_cons, List.length_nil] at hlen
        omega
  unfold ABI.decodeReturnValuesWithMode?
  rw [abiTupleHeadSize_scalarWords_eq
    (types := [abiUInt256, abiUInt256, abiUInt256, abiUInt256, abiUInt256]) (by decide)]
  simp only [bind, Option.bind]
  rw [decodeABIValues_scalarWordsWithMode_eq (mode := DecodeMode.legacySolc05)
    (types := [abiUInt256, abiUInt256, abiUInt256, abiUInt256, abiUInt256]) (bytes := o.toList)
    (cursor := 0)
    (total := 32 * [abiUInt256, abiUInt256, abiUInt256, abiUInt256, abiUInt256].length)
    (by decide) (by simp), hnone]

/-- The `ilks` post-call scratch mem's free-pointer `MLOAD` (`mem[0x40] = 0x80`) survives the
`< 160`-byte return copy (which lands at `0x80`, entirely above `0x40`). -/
private theorem catBiteIlksPostCallMem_mload64_short (I : ExecutionEnv) (o : ByteArray)
    {aw : UInt256} (hoLt : o.size < 160) (hout : o.size < UInt256.size)
    (haw : 96 ≤ aw.toNat * 32) (hawsz : aw.toNat * 32 < UInt256.size) :
    (if (⟨64⟩ : UInt256).toNat ≥ (catBiteIlksPostCallMem I o).size ∨ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩
        then ⟨0⟩
     else UInt256.ofNat (fromByteArrayBigEndian
       ((catBiteIlksPostCallMem I o).readWithPadding (⟨64⟩ : UInt256).toNat 32))) = ⟨128⟩ := by
  have hbaseSz : (catBiteIlksCalldataMem (biteIlkWord I) solcFreePtrMem).size = 164 :=
    catBiteIlksCalldataMem_size (biteIlkWord I) solcFreePtrMem_size
  have hbaseRead :
      (catBiteIlksCalldataMem (biteIlkWord I) solcFreePtrMem).readWithPadding 64 32 =
        UInt256.toByteArray ⟨128⟩ :=
    catBiteIlksCalldataMem_read64 (biteIlkWord I) solcFreePtrMem_size solcFreePtrMem_read64
  have hlen : (min catBiteIlksOutSize (UInt256.ofNat o.size)).toNat = o.size :=
    umin_ofNat_right_toNat_of_lt (c := 160) (n := o.size) (by decide) hoLt hout
  have hread : (catBiteIlksPostCallMem I o).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
    unfold catBiteIlksPostCallMem
    rw [hlen, show catBiteIlksOutPtr.toNat = 128 from by native_decide]
    rcases Nat.eq_zero_or_pos o.size with h0 | h0
    · rw [h0, byteArray_write_len_zero]; exact hbaseRead
    · rw [write_read_below_gen_extend o (catBiteIlksCalldataMem (biteIlkWord I) solcFreePtrMem)
        128 o.size 64 (by omega) (le_refl _) (by rw [hbaseSz]; omega) (by omega)]
      exact hbaseRead
  have hsz : 64 < (catBiteIlksPostCallMem I o).size := by
    unfold catBiteIlksPostCallMem
    rw [hlen, show catBiteIlksOutPtr.toNat = 128 from by native_decide]
    rcases Nat.eq_zero_or_pos o.size with h0 | h0
    · rw [h0, byteArray_write_len_zero, hbaseSz]; omega
    · by_cases hext : (catBiteIlksCalldataMem (biteIlkWord I) solcFreePtrMem).size < 128 + o.size
      · rw [write_eq_gen_extend o (catBiteIlksCalldataMem (biteIlkWord I) solcFreePtrMem)
            128 o.size (by omega) (le_refl _) (by rw [hbaseSz]; omega) hext,
          ByteArray.size_append, ByteArray.size_extract, ByteArray.size_extract, hbaseSz]
        omega
      · push_neg at hext
        rw [write_eq_gen o (catBiteIlksCalldataMem (biteIlkWord I) solcFreePtrMem)
            128 o.size (by omega) (le_refl _) hext,
          ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
          ByteArray.size_extract, ByteArray.size_extract, hbaseSz]
        omega
  refine mloadWordValue_of_readWithPadding (off := ⟨64⟩) (v := ⟨128⟩) ?_ ?_ ?_
  · rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide]; exact hsz
  · intro hh
    have hle : (aw * ⟨32⟩).toNat ≤ (⟨64⟩ : UInt256).toNat := hh
    rw [u256_mul_op_toNat, show (⟨32⟩ : UInt256).toNat = 32 from by decide,
      Nat.mod_eq_of_lt hawsz, show (⟨64⟩ : UInt256).toNat = 64 from by decide] at hle
    omega
  · rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide]; exact hread

set_option maxHeartbeats 800000 in
/-- **ilks return-decode-short branch (extracted).** ilks STATICCALL succeeds but returns `< 160`
bytes; fires `catBiteIlksDecodeShortLeaf` + `catBiteSourceIlksDecodeRevert`. -/
theorem catBiteRevertIlksDecode {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {σ' : AccountMap} {cA' : Batteries.RBSet AccountAddress compare}
    {A' : Substate} {o' : ByteArray} {awout : UInt256} {k' C' : ℕ} {status : UInt256}
    (hcode : I.code = catBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hdispatch : dispatchMsg contract I.calldata = some biteTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (biteTransition.params.map Param.name)
        (transitionSignature biteTransition).paramTypes I.calldata = some (biteLocals I))
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hvatCode :
      ¬ Reasoning.Theory.extCodeSizeWord σ_evm (catBiteVatTargetWord σ_evm I) = ⟨0⟩)
    (hIlksCall :
      typedCallViaEVM config (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        (AccountAddress.ofUInt256 (catBiteVatTargetWord σ_evm I)) "ilks" 0 [biteIlkVal I]
        (true, { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
                  accountMap := σ', substate := A', createdAccounts := cA' }, o') false)
    (rd1249 : RD catBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1249⟩
      (status :: catBiteIlksEndPtr :: catBiteIlksSelectorWord :: catBiteVatTargetWord σ_evm I ::
        ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: UInt256.land biteAddrMaskWord (calldataWord I.calldata 36) ::
        biteIlkWord I :: ⟨419⟩ :: catSelWord I :: [])
      (catBiteIlksPostCallMem I o') awout o' (cA', σ') k' C')
    (hstatus : status ≠ ⟨0⟩)
    (hosz : o'.size < UInt256.size) (hawout9 : awout = ⟨9⟩)
    (hilkslen : ¬ 160 ≤ o'.size) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  subst hawout9
  obtain ⟨σs, As, hIlksSolm, _hEq⟩ := catBiteMapIlksCall hAccounts hIlksCall
  have htw : catBiteVatTargetWord σ_evm I = catBiteVatTargetWord σ_solm I := by
    simp only [catBiteVatTargetWord, catAddressReturnWord, catSlotWord, solcSlotWord]
    rw [accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨3⟩ ⟨0⟩]
  have htgt : (AccountAddress.ofUInt256 (catBiteVatTargetWord σ_evm I))
      = EVM.address (biteVatAddr (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)) := by
    rw [htw]; exact (catBiteVatEvmAddr_eq_target).symm
  rw [htgt] at hIlksSolm
  exact catBiteIlksDecodeShortLeaf hcode hdispatch hdecode rd1249 hstatus (by omega) hosz
    (catBiteIlksPostCallMem_mload64_short I o' (by omega) hosz (by native_decide) (by native_decide))
    (catBiteMloadCost0 (catBiteAwMInv32 (⟨9⟩ : UInt256) (by native_decide)))
    (catBiteAwMInv32 (⟨9⟩ : UInt256) (by native_decide))
    (by simp only [List.length_cons, List.length_nil]; omega)
    (catBiteSourceIlksDecodeRevert hwv (catBiteVatCodePos_of_uniswap hAccounts hvatCode)
      hIlksSolm (catBiteIlksDecode_none (by omega)))


/-! ## Post-milk `require`-string revert leaves (dart/dink `> 0` / `≤ 2²⁵⁵`)

These four `require`s fire after the `milk`-struct build (`aw = ⟨10⟩`, free pointer `mem[0x40] = 320`,
`mem.size = 320`), so they route through the fp=320 `Error(string)` tail
`RD.catBiteMilkErrorStringRevertTail` rather than the pre-milk fp=128 tail. -/

/-- `catBiteUrnsPostCallMem` (the urns-output overlay over the 288-byte urns-calldata frame) writes
64 bytes at offset 128 in bounds, so its size stays 288. -/
theorem catBiteUrnsPostCallMem_size288 {I : ExecutionEnv} {o' ou : ByteArray}
    (hilkslen : 160 ≤ o'.size) (hosz : o'.size < UInt256.size)
    (hurnslen : 64 ≤ ou.size) (hoszu : ou.size < UInt256.size) :
    (catBiteUrnsPostCallMem I (catBiteIlksPostCallMem I o') ou).size = 288 := by
  have hmemI : 196 ≤ (catBiteIlksPostCallMem I o').size := by
    have h := catBiteIlksPostCallMem_size I o' hilkslen hosz; omega
  have hbaseSz : (biteUrnsCalldataMem (biteIlkWord I) (biteUrnWord I)
      (catBiteIlksPostCallMem I o')).size = 288 := by
    rw [biteUrnsCalldataMem_size hmemI, catBiteIlksPostCallMem_size I o' hilkslen hosz]
  have hlen64 : ((⟨64⟩ : UInt256) ⊓ UInt256.ofNat ou.size).toNat = 64 :=
    umin_ofNat_right_toNat_of_ge (c := 64) (n := ou.size) (by decide) hurnslen hoszu
  unfold catBiteUrnsPostCallMem
  rw [hlen64, show (⟨128⟩ : UInt256).toNat = 128 from by native_decide,
    write_eq_gen ou _ 128 64 (by decide) (by omega) (by rw [hbaseSz]; omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract, hbaseSz]
  omega

/-- The post-milk memory (`catBiteMilkMem` over the 288-byte urns overlay, `q = 96+128`) has size
`max 288 320 = 320`. Discharges the `hmem` obligation of `RD.catBiteMilkErrorStringRevertTail`. -/
theorem catBiteMilkSize320 {I : ExecutionEnv} {o' ou : ByteArray} {q flip chop dunk : UInt256}
    (hqfp : q = ⟨96⟩ + ⟨128⟩)
    (hilkslen : 160 ≤ o'.size) (hosz : o'.size < UInt256.size)
    (hurnslen : 64 ≤ ou.size) (hoszu : ou.size < UInt256.size) :
    (catBiteMilkMem (catBiteUrnsPostCallMem I (catBiteIlksPostCallMem I o') ou) ⟨128⟩
      (biteIlkWord I) q flip chop dunk).size = 320 := by
  have hurnsSz := catBiteUrnsPostCallMem_size288 (I := I) hilkslen hosz hurnslen hoszu
  rw [catBiteMilkMem_size (catBiteUrnsPostCallMem I (catBiteIlksPostCallMem I o') ou) ⟨128⟩
      (biteIlkWord I) q flip chop dunk (by rw [hurnsSz]; native_decide) hqfp (by native_decide)
      (by rw [hqfp]; native_decide), hurnsSz, hqfp]
  native_decide

/-- The post-milk free pointer `mem[0x40] = q + 96 = 320` survives (needed as the `hread64`
obligation of `RD.catBiteMilkErrorStringRevertTail`). -/
theorem catBiteMilkRead64_320 {I : ExecutionEnv} {o' ou : ByteArray} {q flip chop dunk : UInt256}
    (hqfp : q = ⟨96⟩ + ⟨128⟩)
    (hilkslen : 160 ≤ o'.size) (hosz : o'.size < UInt256.size)
    (hurnslen : 64 ≤ ou.size) (hoszu : ou.size < UInt256.size) :
    (catBiteMilkMem (catBiteUrnsPostCallMem I (catBiteIlksPostCallMem I o') ou) ⟨128⟩
      (biteIlkWord I) q flip chop dunk).readWithPadding 64 32 = UInt256.toByteArray ⟨320⟩ := by
  have hurnsSz := catBiteUrnsPostCallMem_size288 (I := I) hilkslen hosz hurnslen hoszu
  rw [catBiteMilkMem_read64 (catBiteUrnsPostCallMem I (catBiteIlksPostCallMem I o') ou) ⟨128⟩
      (biteIlkWord I) q flip chop dunk (by rw [hurnsSz]; native_decide) hqfp (by native_decide)
      (by rw [hqfp]; native_decide), hqfp]
  congr 1

/-- **Post-milk generic `require(cond, "msg")`-false → `Error(string)` revert leaf.** fp=320 / `aw=⟨10⟩`
analogue of `catBiteRequireStringRevertLeaf`: hand-trace `PUSH2 okPc; JUMPI`-not-taken into the milk
`Error(string)` tail (`RD.catBiteMilkErrorStringRevertTail`) and bridge to the Solm `.reverted` body. -/
theorem catBiteMilkRequireStringRevertLeaf {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {mem rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {cond okPc : UInt256} {R : List UInt256} {k C : ℕ}
    {guardPc len rawWord shift word : UInt256} {op : Operation.POp} {width : ℕ}
    (hcode : I.code = catBytecode)
    (hdispatch : dispatchMsg contract I.calldata = some biteTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (biteTransition.params.map Param.name)
        (transitionSignature biteTransition).paramTypes I.calldata = some (biteLocals I))
    (rd : RD catBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) guardPc
      (cond :: R) mem ⟨10⟩ rdata acc k C)
    (hcond : cond = ⟨0⟩)
    (hpush2 : decode catBytecode guardPc = some (.Push .PUSH2, some (okPc, 2)))
    (hjumpi : decode catBytecode (guardPc + UInt256.ofNat 3) = some (.JUMPI, .none))
    (htail : solcErrorStringRevertTailWf catBytecode (guardPc + UInt256.ofNat 3 + ⟨1⟩)
      len rawWord shift op width)
    (hpush : op ≠ .PUSH0) (hword : UInt256.shiftLeft rawWord shift = word)
    (hmem : mem.size = 320)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨320⟩)
    (hov : R.length + 5 ≤ 1024)
    (hbody :
      ExecTransitionBody config contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) (biteLocals I)
        biteTransition.body .reverted) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have rd2 := rd.push2 okPc hpush2 (by simp only [List.length_cons]; omega)
  have rd3 := rd2.jumpiNT hjumpi hcond (by omega)
  have hrev := RD.catBiteMilkErrorStringRevertTail rd3 htail hpush hword hmem hread64 hov
  simpa using hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody

set_option maxHeartbeats 2000000 in
/-- **`dart = 0` require-string revert branch (extracted).** Post-milk (`aw=10`) `require(dart > 0 &&
dink > 0, …)` fails on the first conjunct (`dart = 0`): reaches the `PUSH2 1985` guard at pc 1918
(via `Seg7a`/`Seg7b`/`catBiteReachGuardDartPos`), fires the fp=320 milk string-revert tail +
`catBiteSourceDartZeroRevert`. -/
theorem catBiteRevertDartZero {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {σ' σu : AccountMap} {A' Au : Substate}
    {cA' cAu : Batteries.RBSet AccountAddress compare} {o' ou : ByteArray} {ku Cu : ℕ}
    {art ink iSpot iRate iDust room milkChop milkDunk dunkRoom dunkRoomWad dartDenomRate
      dartCandidate dart inkDart dinkCandidate dink q : UInt256}
    (hcode : I.code = catBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hdispatch : dispatchMsg contract I.calldata = some biteTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (biteTransition.params.map Param.name)
        (transitionSignature biteTransition).paramTypes I.calldata = some (biteLocals I))
    (hAccounts : accountMapEquiv σ_evm σ_solm) (hsz36 : 36 ≤ I.calldata.size)
    (hdepth : (I.depth : ℕ) < 1024)
    (hvatCode : ¬ Reasoning.Theory.extCodeSizeWord σ_evm (catBiteVatTargetWord σ_evm I) = ⟨0⟩)
    (hUrnsVatCode :
      ¬ Reasoning.Theory.extCodeSizeWord σ' ((catSlotWord ⟨3⟩ σ' I).land biteAddrMaskWord) = ⟨0⟩)
    (hIlksCall :
      typedCallViaEVM config (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        (AccountAddress.ofUInt256 (catBiteVatTargetWord σ_evm I)) "ilks" 0 [biteIlkVal I]
        (true, { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
                  accountMap := σ', substate := A', createdAccounts := cA' }, o') false)
    (hUrnsCall :
      typedCallViaEVM config
        { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
            accountMap := σ', createdAccounts := cA' }
        (AccountAddress.ofUInt256 ((catSlotWord ⟨3⟩ σ' I).land biteAddrMaskWord)) "urns" 0
        [biteIlkVal I, biteUrnVal I]
        (true, { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
                  accountMap := σu, substate := Au, createdAccounts := cAu }, ou) false)
    (hilkslen : 160 ≤ o'.size) (hurnslen : 64 ≤ ou.size)
    (hosz : o'.size < UInt256.size) (hoszu : ou.size < UInt256.size)
    (hurn : biteAddrMaskWord.land (biteAddrMaskWord.land (calldataWord I.calldata 36)) = biteUrnWord I)
    (hlive : catSlotWord ⟨2⟩ σu I = ⟨1⟩)
    (hmemI : 196 ≤ (catBiteIlksPostCallMem I o').size)
    (hmemUsz : 224 ≤ (catBiteUrnsPostCallMem I (catBiteIlksPostCallMem I o') ou).size)
    (hqfp : q = ⟨96⟩ + ⟨128⟩)
    (rd1708 : RD catBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1708⟩
      (room :: ⟨0⟩ :: ⟨0⟩ :: q :: art :: ink :: iDust :: iSpot :: iRate :: ⟨0⟩ ::
        biteAddrMaskWord.land (calldataWord I.calldata 36) :: biteIlkWord I :: ⟨419⟩ :: catSelWord I :: [])
      (catBiteMilkMem (catBiteUrnsPostCallMem I (catBiteIlksPostCallMem I o') ou) ⟨128⟩ (biteIlkWord I) q
        (biteAddrMaskWord.land (solcSlotWord σu I (solcMappingSlot ⟨1⟩ (biteIlkWord I)))) milkChop milkDunk)
      ⟨10⟩ ou (cAu, σu) ku Cu)
    (hChop : (if (⟨32⟩ + q).toNat ≥
          (catBiteMilkMem (catBiteUrnsPostCallMem I (catBiteIlksPostCallMem I o') ou) ⟨128⟩ (biteIlkWord I) q
            (biteAddrMaskWord.land (solcSlotWord σu I (solcMappingSlot ⟨1⟩ (biteIlkWord I)))) milkChop
            milkDunk).size ∨ (⟨32⟩ + q) ≥ (⟨10⟩ : UInt256) * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat (fromByteArrayBigEndian
        ((catBiteMilkMem (catBiteUrnsPostCallMem I (catBiteIlksPostCallMem I o') ou) ⟨128⟩ (biteIlkWord I) q
            (biteAddrMaskWord.land (solcSlotWord σu I (solcMappingSlot ⟨1⟩ (biteIlkWord I)))) milkChop
            milkDunk).readWithPadding (⟨32⟩ + q).toNat 32))) = milkChop)
    (hDunk : (if (⟨64⟩ + q).toNat ≥
          (catBiteMilkMem (catBiteUrnsPostCallMem I (catBiteIlksPostCallMem I o') ou) ⟨128⟩ (biteIlkWord I) q
            (biteAddrMaskWord.land (solcSlotWord σu I (solcMappingSlot ⟨1⟩ (biteIlkWord I)))) milkChop
            milkDunk).size ∨ (⟨64⟩ + q) ≥ (⟨10⟩ : UInt256) * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat (fromByteArrayBigEndian
        ((catBiteMilkMem (catBiteUrnsPostCallMem I (catBiteIlksPostCallMem I o') ou) ⟨128⟩ (biteIlkWord I) q
            (biteAddrMaskWord.land (solcSlotWord σu I (solcMappingSlot ⟨1⟩ (biteIlkWord I)))) milkChop
            milkDunk).readWithPadding (⟨64⟩ + q).toNat 32))) = milkDunk)
    (hlitterbox : (solcSlotWord σu I ⟨6⟩).toNat < (solcSlotWord σu I ⟨5⟩).toNat)
    (hroomdust : iDust.toNat ≤ room.toNat)
    (hunsafe : (ink * iSpot).toNat < (art * iRate).toNat)
    (hfitArtRate : art.toNat * iRate.toNat < UInt256.size)
    (hfitInkSpot : ink.toNat * iSpot.toNat < UInt256.size)
    (hspotPos : 0 < iSpot.toNat) (hRatePos : iRate ≠ ⟨0⟩) (hChopPos : milkChop ≠ ⟨0⟩)
    (hFitWad : (⟨1000000000000000000⟩ : UInt256).toNat * dunkRoom.toNat < UInt256.size)
    (hArtPos : art ≠ ⟨0⟩)
    (hFitInkDart : dart.toNat * ink.toNat < UInt256.size)
    (hart : art = UInt256.ofNat (fromByteArrayBigEndian (ou.extract 32 64)))
    (hink : ink = UInt256.ofNat (fromByteArrayBigEndian (ou.extract 0 32)))
    (hiSpot : iSpot = UInt256.ofNat (fromByteArrayBigEndian (o'.extract 64 96)))
    (hiRate : iRate = UInt256.ofNat (fromByteArrayBigEndian (o'.extract 32 64)))
    (hiDust : iDust = UInt256.ofNat (fromByteArrayBigEndian (o'.extract 128 160)))
    (hroomDef : room = (solcSlotWord σu I ⟨5⟩).sub (solcSlotWord σu I ⟨6⟩))
    (hmilkDunkDef : milkDunk = solcSlotWord σu I (solcMappingSlot ⟨1⟩ (biteIlkWord I) + ⟨2⟩))
    (hmilkChopDef : milkChop = solcSlotWord σu I (solcMappingSlot ⟨1⟩ (biteIlkWord I) + ⟨1⟩))
    (hdunkRoomDef : dunkRoom = if milkDunk.gt room = ⟨0⟩ then milkDunk else room)
    (hdunkRoomWadDef : dunkRoomWad = dunkRoom.mul ⟨1000000000000000000⟩)
    (hdartDenomDef : dartDenomRate = dunkRoomWad.div iRate)
    (hdartCandDef : dartCandidate = dartDenomRate.div milkChop)
    (hdartDef : dart = if art.gt dartCandidate = ⟨0⟩ then art else dartCandidate)
    (hinkDartDef : inkDart = UInt256.mul ink dart)
    (hdinkCandDef : dinkCandidate = UInt256.div inkDart art)
    (hdinkDef : dink = if UInt256.gt ink dinkCandidate = ⟨0⟩ then ink else dinkCandidate)
    (hDartPos : ¬ (0 < dart.toNat)) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hdepthNe : I.depth ≠ 1024 := by omega
  have hposNe : ∀ w : UInt256, w ≠ ⟨0⟩ → 0 < w.toNat :=
    fun w hw => Nat.pos_of_ne_zero (fun h => hw (uint256_toNat_eq_zero h))
  have hqNat : q.toNat = 224 := by rw [hqfp]; native_decide
  have hDartZero : dart = ⟨0⟩ := uint256_toNat_eq_zero (by omega)
  obtain ⟨_, _, rd1810⟩ := catBiteTraceSeg7a rd1708 hlitterbox hroomdust (by simp)
  obtain ⟨_, _, rd1872⟩ := catBiteTraceSeg7b rd1810 hChop hDunk (by rw [hqNat]; native_decide)
    (by rw [hqNat]; native_decide) hRatePos hChopPos hdunkRoomDef.symm hFitWad hdunkRoomWadDef.symm
    hdartDenomDef.symm hdartCandDef.symm hdartDef.symm (by simp)
  obtain ⟨_, _, rd1918⟩ := catBiteReachGuardDartPos rd1872 hArtPos hFitInkDart hinkDartDef.symm
    hdinkCandDef.symm hdinkDef.symm hDartZero (by simp)
  obtain ⟨σs, As, σus, Aus, hIlksSolm, hUrnsSolm, hAmEq, hvatCodeIlkS⟩ :=
    catBiteMapUrns hAccounts hdepthNe hUrnsVatCode hIlksCall hUrnsCall
  set eUrnS := { initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I with
    accountMap := σus, substate := Aus, createdAccounts := cAu } with heUrnSdef
  have heUSam : eUrnS.accountMap = σus := rfl
  have heUSee : eUrnS.executionEnv = I := rfl
  have slotEqUS : ∀ s : UInt256, solcSlotWord σus I s = solcSlotWord σu I s := by
    intro s; simp only [solcSlotWord]
    rw [accountMapEquiv_storage_findD hAmEq I.codeOwner s ⟨0⟩]
  have uminEq : ∀ a b : UInt256, (if UInt256.gt a b = ⟨0⟩ then a else b) = umin a b := by
    intro a b; unfold umin
    by_cases h : a.toNat ≤ b.toNat
    · rw [if_pos (ugt_zero h), if_pos h]
    · rw [if_neg (by rw [ugt_one (by omega)]; decide), if_neg h]
  have hbr : ∀ (o : ByteArray) (k : ℕ), k + 32 ≤ o.size →
      ABI.bytesToWord ((o.toList.drop k).take 32) =
        UInt256.ofNat (fromByteArrayBigEndian (o.extract k (k + 32))) := by
    intro o k h
    rw [decode_word_at_eq_any o k h, uInt256OfByteArray_eq]
    congr 1; unfold fromByteArrayBigEndian; congr 1
    rw [byteArray_toList_eq (o.readBytes k 32), readBytes_at_toList_any o k h,
      byteArray_toList_eq (o.extract k (k + 32)), ByteArray.data_extract, Array.toList_extract,
      List.extract_eq_take_drop]
    simp
  have hIlksDec : config.externalABI.decode? "ilks" o' =
      some [bw (UInt256.ofNat (fromByteArrayBigEndian (o'.extract 0 32))), bw iRate, bw iSpot,
        bw (UInt256.ofNat (fromByteArrayBigEndian (o'.extract 96 128))), bw iDust] := by
    have h := catBiteIlksDecode_ok hilkslen
    rw [hbr o' 0 (by omega), hbr o' 32 (by omega), hbr o' 64 (by omega),
      hbr o' 96 (by omega), hbr o' 128 (by omega)] at h
    rw [hiRate, hiSpot, hiDust]; exact h
  have hUrnsDec : config.externalABI.decode? "urns" ou = some [bw ink, bw art] := by
    have h := catBiteUrnsDecode_ok hurnslen
    rw [hbr ou 0 (by omega), hbr ou 32 (by omega)] at h
    rw [hink, hart]; exact h
  have hlive' : catSlotWord ⟨2⟩ eUrnS.accountMap eUrnS.executionEnv = ⟨1⟩ := by
    rw [heUSam, heUSee]; simp only [catSlotWord]; rw [slotEqUS ⟨2⟩]
    simpa only [catSlotWord] using hlive
  have hratePos : 0 < iRate.toNat := by
    by_contra hc
    have hr0 : iRate.toNat = 0 := by omega
    have hz : (art * iRate).toNat = 0 := by
      rw [u256_mul_op_toNat, hr0, Nat.mul_zero, Nat.zero_mod]
    omega
  have hboxB : biteBoxW eUrnS = solcSlotWord σu I ⟨5⟩ := by
    simp only [biteBoxW, catSlotWord, heUSam, heUSee]; exact slotEqUS ⟨5⟩
  have hlitB : biteLitW eUrnS = solcSlotWord σu I ⟨6⟩ := by
    simp only [biteLitW, catSlotWord, heUSam, heUSee]; exact slotEqUS ⟨6⟩
  have hroomB : biteRoomV eUrnS = room := by
    rw [hroomDef]; simp only [biteRoomV, hboxB, hlitB]
  have hdunkB : biteDunkW I eUrnS = milkDunk := by
    rw [hmilkDunkDef]
    simp only [biteDunkW, catSlotWord, heUSam, heUSee, biteDunkSlot, biteFlipSlot_eq hsz36]
    exact slotEqUS _
  have hchopB : biteChopW I eUrnS = milkChop := by
    rw [hmilkChopDef]
    simp only [biteChopW, catSlotWord, heUSam, heUSee, biteChopSlot, biteFlipSlot_eq hsz36]
    exact slotEqUS _
  have hdunkroomB : biteDunkRoomV I eUrnS = dunkRoom := by
    rw [hdunkRoomDef, uminEq milkDunk room]
    simp only [biteDunkRoomV, hdunkB, hroomB]
  have hwad : wadU = ⟨1000000000000000000⟩ := by native_decide
  have hdartvB : biteDartV I eUrnS iRate art = dart := by
    have hcand : biteDartCandV I eUrnS iRate = dartCandidate := by
      simp only [biteDartCandV, biteDartDenomV, biteDunkRoomWadV, hchopB, hdunkroomB, hwad,
        hdartCandDef, hdartDenomDef, hdunkRoomWadDef]
      rfl
    rw [hdartDef, uminEq art dartCandidate]
    simp only [biteDartV, hcand]
  have hlitLtBox : (biteLitW eUrnS).toNat < (biteBoxW eUrnS).toNat := by
    rw [hlitB, hboxB]; exact hlitterbox
  have hroomGeDust : iDust.toNat ≤ (biteRoomV eUrnS).toNat := by rw [hroomB]; exact hroomdust
  have hbody := catBiteSourceDartZeroRevert hwv
    (catBiteVatCodePos_of_uniswap hAccounts hvatCode) hIlksSolm hIlksDec hvatCodeIlkS
    hUrnsSolm hUrnsDec hlive' hsz36 hfitInkSpot hfitArtRate hspotPos hratePos hunsafe hlitLtBox
    hroomGeDust (by rw [hdunkroomB, hwad, Nat.mul_comm]; exact hFitWad)
    (by rw [hchopB]; exact hposNe milkChop hChopPos)
    (by rw [hdartvB, Nat.mul_comm]; exact hFitInkDart) (hposNe art hArtPos)
    (by rw [hdartvB]; omega)
  exact catBiteMilkRequireStringRevertLeaf (okPc := ⟨1985⟩) (len := ⟨16⟩)
    (rawWord := ⟨0x21b0ba17b73ab63616b0bab1ba34b7b7⟩) (shift := ⟨129⟩) (op := .PUSH16) (width := 16)
    hcode hdispatch hdecode rd1918 rfl (by native_decide) (by native_decide)
    (by unfold solcErrorStringRevertTailWf; repeat' first | apply And.intro | native_decide)
    (by decide) rfl (catBiteMilkSize320 hqfp hilkslen hosz hurnslen hoszu)
    (catBiteMilkRead64_320 hqfp hilkslen hosz hurnslen hoszu)
    (by simp only [List.length_cons, List.length_nil]; omega) hbody

set_option maxHeartbeats 2000000 in
/-- **`dink = 0` require-string revert branch (extracted).** Post-milk (`aw=10`) `require(dart > 0 &&
dink > 0, …)` fails on the second conjunct (`dink = 0`, with `dart > 0`): reaches the `PUSH2 1985`
guard at pc 1918 (via `Seg7a`/`Seg7b`/`catBiteReachGuardDinkPos`), fires the fp=320 milk string-revert
tail + `catBiteSourceDinkZeroRevert`. -/
theorem catBiteRevertDinkZero {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {σ' σu : AccountMap} {A' Au : Substate}
    {cA' cAu : Batteries.RBSet AccountAddress compare} {o' ou : ByteArray} {ku Cu : ℕ}
    {art ink iSpot iRate iDust room milkChop milkDunk dunkRoom dunkRoomWad dartDenomRate
      dartCandidate dart inkDart dinkCandidate dink q : UInt256}
    (hcode : I.code = catBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hdispatch : dispatchMsg contract I.calldata = some biteTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (biteTransition.params.map Param.name)
        (transitionSignature biteTransition).paramTypes I.calldata = some (biteLocals I))
    (hAccounts : accountMapEquiv σ_evm σ_solm) (hsz36 : 36 ≤ I.calldata.size)
    (hdepth : (I.depth : ℕ) < 1024)
    (hvatCode : ¬ Reasoning.Theory.extCodeSizeWord σ_evm (catBiteVatTargetWord σ_evm I) = ⟨0⟩)
    (hUrnsVatCode :
      ¬ Reasoning.Theory.extCodeSizeWord σ' ((catSlotWord ⟨3⟩ σ' I).land biteAddrMaskWord) = ⟨0⟩)
    (hIlksCall :
      typedCallViaEVM config (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        (AccountAddress.ofUInt256 (catBiteVatTargetWord σ_evm I)) "ilks" 0 [biteIlkVal I]
        (true, { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
                  accountMap := σ', substate := A', createdAccounts := cA' }, o') false)
    (hUrnsCall :
      typedCallViaEVM config
        { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
            accountMap := σ', createdAccounts := cA' }
        (AccountAddress.ofUInt256 ((catSlotWord ⟨3⟩ σ' I).land biteAddrMaskWord)) "urns" 0
        [biteIlkVal I, biteUrnVal I]
        (true, { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
                  accountMap := σu, substate := Au, createdAccounts := cAu }, ou) false)
    (hilkslen : 160 ≤ o'.size) (hurnslen : 64 ≤ ou.size)
    (hosz : o'.size < UInt256.size) (hoszu : ou.size < UInt256.size)
    (hurn : biteAddrMaskWord.land (biteAddrMaskWord.land (calldataWord I.calldata 36)) = biteUrnWord I)
    (hlive : catSlotWord ⟨2⟩ σu I = ⟨1⟩)
    (hmemI : 196 ≤ (catBiteIlksPostCallMem I o').size)
    (hmemUsz : 224 ≤ (catBiteUrnsPostCallMem I (catBiteIlksPostCallMem I o') ou).size)
    (hqfp : q = ⟨96⟩ + ⟨128⟩)
    (rd1708 : RD catBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1708⟩
      (room :: ⟨0⟩ :: ⟨0⟩ :: q :: art :: ink :: iDust :: iSpot :: iRate :: ⟨0⟩ ::
        biteAddrMaskWord.land (calldataWord I.calldata 36) :: biteIlkWord I :: ⟨419⟩ :: catSelWord I :: [])
      (catBiteMilkMem (catBiteUrnsPostCallMem I (catBiteIlksPostCallMem I o') ou) ⟨128⟩ (biteIlkWord I) q
        (biteAddrMaskWord.land (solcSlotWord σu I (solcMappingSlot ⟨1⟩ (biteIlkWord I)))) milkChop milkDunk)
      ⟨10⟩ ou (cAu, σu) ku Cu)
    (hChop : (if (⟨32⟩ + q).toNat ≥
          (catBiteMilkMem (catBiteUrnsPostCallMem I (catBiteIlksPostCallMem I o') ou) ⟨128⟩ (biteIlkWord I) q
            (biteAddrMaskWord.land (solcSlotWord σu I (solcMappingSlot ⟨1⟩ (biteIlkWord I)))) milkChop
            milkDunk).size ∨ (⟨32⟩ + q) ≥ (⟨10⟩ : UInt256) * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat (fromByteArrayBigEndian
        ((catBiteMilkMem (catBiteUrnsPostCallMem I (catBiteIlksPostCallMem I o') ou) ⟨128⟩ (biteIlkWord I) q
            (biteAddrMaskWord.land (solcSlotWord σu I (solcMappingSlot ⟨1⟩ (biteIlkWord I)))) milkChop
            milkDunk).readWithPadding (⟨32⟩ + q).toNat 32))) = milkChop)
    (hDunk : (if (⟨64⟩ + q).toNat ≥
          (catBiteMilkMem (catBiteUrnsPostCallMem I (catBiteIlksPostCallMem I o') ou) ⟨128⟩ (biteIlkWord I) q
            (biteAddrMaskWord.land (solcSlotWord σu I (solcMappingSlot ⟨1⟩ (biteIlkWord I)))) milkChop
            milkDunk).size ∨ (⟨64⟩ + q) ≥ (⟨10⟩ : UInt256) * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat (fromByteArrayBigEndian
        ((catBiteMilkMem (catBiteUrnsPostCallMem I (catBiteIlksPostCallMem I o') ou) ⟨128⟩ (biteIlkWord I) q
            (biteAddrMaskWord.land (solcSlotWord σu I (solcMappingSlot ⟨1⟩ (biteIlkWord I)))) milkChop
            milkDunk).readWithPadding (⟨64⟩ + q).toNat 32))) = milkDunk)
    (hlitterbox : (solcSlotWord σu I ⟨6⟩).toNat < (solcSlotWord σu I ⟨5⟩).toNat)
    (hroomdust : iDust.toNat ≤ room.toNat)
    (hunsafe : (ink * iSpot).toNat < (art * iRate).toNat)
    (hfitArtRate : art.toNat * iRate.toNat < UInt256.size)
    (hfitInkSpot : ink.toNat * iSpot.toNat < UInt256.size)
    (hspotPos : 0 < iSpot.toNat) (hRatePos : iRate ≠ ⟨0⟩) (hChopPos : milkChop ≠ ⟨0⟩)
    (hFitWad : (⟨1000000000000000000⟩ : UInt256).toNat * dunkRoom.toNat < UInt256.size)
    (hArtPos : art ≠ ⟨0⟩)
    (hFitInkDart : dart.toNat * ink.toNat < UInt256.size)
    (hart : art = UInt256.ofNat (fromByteArrayBigEndian (ou.extract 32 64)))
    (hink : ink = UInt256.ofNat (fromByteArrayBigEndian (ou.extract 0 32)))
    (hiSpot : iSpot = UInt256.ofNat (fromByteArrayBigEndian (o'.extract 64 96)))
    (hiRate : iRate = UInt256.ofNat (fromByteArrayBigEndian (o'.extract 32 64)))
    (hiDust : iDust = UInt256.ofNat (fromByteArrayBigEndian (o'.extract 128 160)))
    (hroomDef : room = (solcSlotWord σu I ⟨5⟩).sub (solcSlotWord σu I ⟨6⟩))
    (hmilkDunkDef : milkDunk = solcSlotWord σu I (solcMappingSlot ⟨1⟩ (biteIlkWord I) + ⟨2⟩))
    (hmilkChopDef : milkChop = solcSlotWord σu I (solcMappingSlot ⟨1⟩ (biteIlkWord I) + ⟨1⟩))
    (hdunkRoomDef : dunkRoom = if milkDunk.gt room = ⟨0⟩ then milkDunk else room)
    (hdunkRoomWadDef : dunkRoomWad = dunkRoom.mul ⟨1000000000000000000⟩)
    (hdartDenomDef : dartDenomRate = dunkRoomWad.div iRate)
    (hdartCandDef : dartCandidate = dartDenomRate.div milkChop)
    (hdartDef : dart = if art.gt dartCandidate = ⟨0⟩ then art else dartCandidate)
    (hinkDartDef : inkDart = UInt256.mul ink dart)
    (hdinkCandDef : dinkCandidate = UInt256.div inkDart art)
    (hdinkDef : dink = if UInt256.gt ink dinkCandidate = ⟨0⟩ then ink else dinkCandidate)
    (hDartPos : 0 < dart.toNat) (hDinkPos : ¬ (0 < dink.toNat)) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hdepthNe : I.depth ≠ 1024 := by omega
  have hposNe : ∀ w : UInt256, w ≠ ⟨0⟩ → 0 < w.toNat :=
    fun w hw => Nat.pos_of_ne_zero (fun h => hw (uint256_toNat_eq_zero h))
  have hqNat : q.toNat = 224 := by rw [hqfp]; native_decide
  obtain ⟨_, _, rd1810⟩ := catBiteTraceSeg7a rd1708 hlitterbox hroomdust (by simp)
  obtain ⟨_, _, rd1872⟩ := catBiteTraceSeg7b rd1810 hChop hDunk (by rw [hqNat]; native_decide)
    (by rw [hqNat]; native_decide) hRatePos hChopPos hdunkRoomDef.symm hFitWad hdunkRoomWadDef.symm
    hdartDenomDef.symm hdartCandDef.symm hdartDef.symm (by simp)
  obtain ⟨_, _, rd1918⟩ := catBiteReachGuardDinkPos rd1872 hArtPos hFitInkDart hinkDartDef.symm
    hdinkCandDef.symm hdinkDef.symm hDartPos (by simp)
  obtain ⟨σs, As, σus, Aus, hIlksSolm, hUrnsSolm, hAmEq, hvatCodeIlkS⟩ :=
    catBiteMapUrns hAccounts hdepthNe hUrnsVatCode hIlksCall hUrnsCall
  set eUrnS := { initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I with
    accountMap := σus, substate := Aus, createdAccounts := cAu } with heUrnSdef
  have heUSam : eUrnS.accountMap = σus := rfl
  have heUSee : eUrnS.executionEnv = I := rfl
  have slotEqUS : ∀ s : UInt256, solcSlotWord σus I s = solcSlotWord σu I s := by
    intro s; simp only [solcSlotWord]
    rw [accountMapEquiv_storage_findD hAmEq I.codeOwner s ⟨0⟩]
  have uminEq : ∀ a b : UInt256, (if UInt256.gt a b = ⟨0⟩ then a else b) = umin a b := by
    intro a b; unfold umin
    by_cases h : a.toNat ≤ b.toNat
    · rw [if_pos (ugt_zero h), if_pos h]
    · rw [if_neg (by rw [ugt_one (by omega)]; decide), if_neg h]
  have hbr : ∀ (o : ByteArray) (k : ℕ), k + 32 ≤ o.size →
      ABI.bytesToWord ((o.toList.drop k).take 32) =
        UInt256.ofNat (fromByteArrayBigEndian (o.extract k (k + 32))) := by
    intro o k h
    rw [decode_word_at_eq_any o k h, uInt256OfByteArray_eq]
    congr 1; unfold fromByteArrayBigEndian; congr 1
    rw [byteArray_toList_eq (o.readBytes k 32), readBytes_at_toList_any o k h,
      byteArray_toList_eq (o.extract k (k + 32)), ByteArray.data_extract, Array.toList_extract,
      List.extract_eq_take_drop]
    simp
  have hIlksDec : config.externalABI.decode? "ilks" o' =
      some [bw (UInt256.ofNat (fromByteArrayBigEndian (o'.extract 0 32))), bw iRate, bw iSpot,
        bw (UInt256.ofNat (fromByteArrayBigEndian (o'.extract 96 128))), bw iDust] := by
    have h := catBiteIlksDecode_ok hilkslen
    rw [hbr o' 0 (by omega), hbr o' 32 (by omega), hbr o' 64 (by omega),
      hbr o' 96 (by omega), hbr o' 128 (by omega)] at h
    rw [hiRate, hiSpot, hiDust]; exact h
  have hUrnsDec : config.externalABI.decode? "urns" ou = some [bw ink, bw art] := by
    have h := catBiteUrnsDecode_ok hurnslen
    rw [hbr ou 0 (by omega), hbr ou 32 (by omega)] at h
    rw [hink, hart]; exact h
  have hlive' : catSlotWord ⟨2⟩ eUrnS.accountMap eUrnS.executionEnv = ⟨1⟩ := by
    rw [heUSam, heUSee]; simp only [catSlotWord]; rw [slotEqUS ⟨2⟩]
    simpa only [catSlotWord] using hlive
  have hratePos : 0 < iRate.toNat := by
    by_contra hc
    have hr0 : iRate.toNat = 0 := by omega
    have hz : (art * iRate).toNat = 0 := by
      rw [u256_mul_op_toNat, hr0, Nat.mul_zero, Nat.zero_mod]
    omega
  have hboxB : biteBoxW eUrnS = solcSlotWord σu I ⟨5⟩ := by
    simp only [biteBoxW, catSlotWord, heUSam, heUSee]; exact slotEqUS ⟨5⟩
  have hlitB : biteLitW eUrnS = solcSlotWord σu I ⟨6⟩ := by
    simp only [biteLitW, catSlotWord, heUSam, heUSee]; exact slotEqUS ⟨6⟩
  have hroomB : biteRoomV eUrnS = room := by
    rw [hroomDef]; simp only [biteRoomV, hboxB, hlitB]
  have hdunkB : biteDunkW I eUrnS = milkDunk := by
    rw [hmilkDunkDef]
    simp only [biteDunkW, catSlotWord, heUSam, heUSee, biteDunkSlot, biteFlipSlot_eq hsz36]
    exact slotEqUS _
  have hchopB : biteChopW I eUrnS = milkChop := by
    rw [hmilkChopDef]
    simp only [biteChopW, catSlotWord, heUSam, heUSee, biteChopSlot, biteFlipSlot_eq hsz36]
    exact slotEqUS _
  have hdunkroomB : biteDunkRoomV I eUrnS = dunkRoom := by
    rw [hdunkRoomDef, uminEq milkDunk room]
    simp only [biteDunkRoomV, hdunkB, hroomB]
  have hwad : wadU = ⟨1000000000000000000⟩ := by native_decide
  have hdartvB : biteDartV I eUrnS iRate art = dart := by
    have hcand : biteDartCandV I eUrnS iRate = dartCandidate := by
      simp only [biteDartCandV, biteDartDenomV, biteDunkRoomWadV, hchopB, hdunkroomB, hwad,
        hdartCandDef, hdartDenomDef, hdunkRoomWadDef]
      rfl
    rw [hdartDef, uminEq art dartCandidate]
    simp only [biteDartV, hcand]
  have hdinkvB : biteDinkV I eUrnS iRate art ink = dink := by
    have hcand : biteDinkCandV I eUrnS iRate art ink = dinkCandidate := by
      simp only [biteDinkCandV, biteInkDartV, hdartvB, hdinkCandDef, hinkDartDef]
      rfl
    rw [hdinkDef, uminEq ink dinkCandidate]
    simp only [biteDinkV, hcand]
  have hlitLtBox : (biteLitW eUrnS).toNat < (biteBoxW eUrnS).toNat := by
    rw [hlitB, hboxB]; exact hlitterbox
  have hroomGeDust : iDust.toNat ≤ (biteRoomV eUrnS).toNat := by rw [hroomB]; exact hroomdust
  have hcondDink : UInt256.gt dink ⟨0⟩ = ⟨0⟩ := by
    refine ugt_zero ?_
    have h0 : (⟨0⟩ : UInt256).toNat = 0 := by native_decide
    omega
  have hbody := catBiteSourceDinkZeroRevert hwv
    (catBiteVatCodePos_of_uniswap hAccounts hvatCode) hIlksSolm hIlksDec hvatCodeIlkS
    hUrnsSolm hUrnsDec hlive' hsz36 hfitInkSpot hfitArtRate hspotPos hratePos hunsafe hlitLtBox
    hroomGeDust (by rw [hdunkroomB, hwad, Nat.mul_comm]; exact hFitWad)
    (by rw [hchopB]; exact hposNe milkChop hChopPos)
    (by rw [hdartvB, Nat.mul_comm]; exact hFitInkDart) (hposNe art hArtPos)
    (by rw [hdartvB]; exact hDartPos) (by rw [hdinkvB]; omega)
  exact catBiteMilkRequireStringRevertLeaf (okPc := ⟨1985⟩) (len := ⟨16⟩)
    (rawWord := ⟨0x21b0ba17b73ab63616b0bab1ba34b7b7⟩) (shift := ⟨129⟩) (op := .PUSH16) (width := 16)
    hcode hdispatch hdecode rd1918 hcondDink (by native_decide) (by native_decide)
    (by unfold solcErrorStringRevertTailWf; repeat' first | apply And.intro | native_decide)
    (by decide) rfl (catBiteMilkSize320 hqfp hilkslen hosz hurnslen hoszu)
    (catBiteMilkRead64_320 hqfp hilkslen hosz hurnslen hoszu)
    (by simp only [List.length_cons, List.length_nil]; omega) hbody

set_option maxHeartbeats 2000000 in
/-- **`dart > 2²⁵⁵` require-string revert branch (extracted).** Post-milk (`aw=10`)
`require(dart ≤ 2²⁵⁵ && dink ≤ 2²⁵⁵, "Cat/overflow")` fails on the first conjunct: reaches the
`PUSH2 2073` guard at pc 2010 (via `Seg7a`/`Seg7b`/`Seg7c`/`catBiteReachGuardDartLimit`), fires the
fp=320 milk string-revert tail + `catBiteSourceDartLimitRevert`. -/
theorem catBiteRevertDartLimit {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {σ' σu : AccountMap} {A' Au : Substate}
    {cA' cAu : Batteries.RBSet AccountAddress compare} {o' ou : ByteArray} {ku Cu : ℕ}
    {art ink iSpot iRate iDust room milkChop milkDunk dunkRoom dunkRoomWad dartDenomRate
      dartCandidate dart inkDart dinkCandidate dink q : UInt256}
    (hcode : I.code = catBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hdispatch : dispatchMsg contract I.calldata = some biteTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (biteTransition.params.map Param.name)
        (transitionSignature biteTransition).paramTypes I.calldata = some (biteLocals I))
    (hAccounts : accountMapEquiv σ_evm σ_solm) (hsz36 : 36 ≤ I.calldata.size)
    (hdepth : (I.depth : ℕ) < 1024)
    (hvatCode : ¬ Reasoning.Theory.extCodeSizeWord σ_evm (catBiteVatTargetWord σ_evm I) = ⟨0⟩)
    (hUrnsVatCode :
      ¬ Reasoning.Theory.extCodeSizeWord σ' ((catSlotWord ⟨3⟩ σ' I).land biteAddrMaskWord) = ⟨0⟩)
    (hIlksCall :
      typedCallViaEVM config (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        (AccountAddress.ofUInt256 (catBiteVatTargetWord σ_evm I)) "ilks" 0 [biteIlkVal I]
        (true, { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
                  accountMap := σ', substate := A', createdAccounts := cA' }, o') false)
    (hUrnsCall :
      typedCallViaEVM config
        { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
            accountMap := σ', createdAccounts := cA' }
        (AccountAddress.ofUInt256 ((catSlotWord ⟨3⟩ σ' I).land biteAddrMaskWord)) "urns" 0
        [biteIlkVal I, biteUrnVal I]
        (true, { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
                  accountMap := σu, substate := Au, createdAccounts := cAu }, ou) false)
    (hilkslen : 160 ≤ o'.size) (hurnslen : 64 ≤ ou.size)
    (hosz : o'.size < UInt256.size) (hoszu : ou.size < UInt256.size)
    (hurn : biteAddrMaskWord.land (biteAddrMaskWord.land (calldataWord I.calldata 36)) = biteUrnWord I)
    (hlive : catSlotWord ⟨2⟩ σu I = ⟨1⟩)
    (hmemI : 196 ≤ (catBiteIlksPostCallMem I o').size)
    (hmemUsz : 224 ≤ (catBiteUrnsPostCallMem I (catBiteIlksPostCallMem I o') ou).size)
    (hqfp : q = ⟨96⟩ + ⟨128⟩)
    (rd1708 : RD catBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1708⟩
      (room :: ⟨0⟩ :: ⟨0⟩ :: q :: art :: ink :: iDust :: iSpot :: iRate :: ⟨0⟩ ::
        biteAddrMaskWord.land (calldataWord I.calldata 36) :: biteIlkWord I :: ⟨419⟩ :: catSelWord I :: [])
      (catBiteMilkMem (catBiteUrnsPostCallMem I (catBiteIlksPostCallMem I o') ou) ⟨128⟩ (biteIlkWord I) q
        (biteAddrMaskWord.land (solcSlotWord σu I (solcMappingSlot ⟨1⟩ (biteIlkWord I)))) milkChop milkDunk)
      ⟨10⟩ ou (cAu, σu) ku Cu)
    (hChop : (if (⟨32⟩ + q).toNat ≥
          (catBiteMilkMem (catBiteUrnsPostCallMem I (catBiteIlksPostCallMem I o') ou) ⟨128⟩ (biteIlkWord I) q
            (biteAddrMaskWord.land (solcSlotWord σu I (solcMappingSlot ⟨1⟩ (biteIlkWord I)))) milkChop
            milkDunk).size ∨ (⟨32⟩ + q) ≥ (⟨10⟩ : UInt256) * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat (fromByteArrayBigEndian
        ((catBiteMilkMem (catBiteUrnsPostCallMem I (catBiteIlksPostCallMem I o') ou) ⟨128⟩ (biteIlkWord I) q
            (biteAddrMaskWord.land (solcSlotWord σu I (solcMappingSlot ⟨1⟩ (biteIlkWord I)))) milkChop
            milkDunk).readWithPadding (⟨32⟩ + q).toNat 32))) = milkChop)
    (hDunk : (if (⟨64⟩ + q).toNat ≥
          (catBiteMilkMem (catBiteUrnsPostCallMem I (catBiteIlksPostCallMem I o') ou) ⟨128⟩ (biteIlkWord I) q
            (biteAddrMaskWord.land (solcSlotWord σu I (solcMappingSlot ⟨1⟩ (biteIlkWord I)))) milkChop
            milkDunk).size ∨ (⟨64⟩ + q) ≥ (⟨10⟩ : UInt256) * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat (fromByteArrayBigEndian
        ((catBiteMilkMem (catBiteUrnsPostCallMem I (catBiteIlksPostCallMem I o') ou) ⟨128⟩ (biteIlkWord I) q
            (biteAddrMaskWord.land (solcSlotWord σu I (solcMappingSlot ⟨1⟩ (biteIlkWord I)))) milkChop
            milkDunk).readWithPadding (⟨64⟩ + q).toNat 32))) = milkDunk)
    (hlitterbox : (solcSlotWord σu I ⟨6⟩).toNat < (solcSlotWord σu I ⟨5⟩).toNat)
    (hroomdust : iDust.toNat ≤ room.toNat)
    (hunsafe : (ink * iSpot).toNat < (art * iRate).toNat)
    (hfitArtRate : art.toNat * iRate.toNat < UInt256.size)
    (hfitInkSpot : ink.toNat * iSpot.toNat < UInt256.size)
    (hspotPos : 0 < iSpot.toNat) (hRatePos : iRate ≠ ⟨0⟩) (hChopPos : milkChop ≠ ⟨0⟩)
    (hFitWad : (⟨1000000000000000000⟩ : UInt256).toNat * dunkRoom.toNat < UInt256.size)
    (hArtPos : art ≠ ⟨0⟩)
    (hFitInkDart : dart.toNat * ink.toNat < UInt256.size)
    (hart : art = UInt256.ofNat (fromByteArrayBigEndian (ou.extract 32 64)))
    (hink : ink = UInt256.ofNat (fromByteArrayBigEndian (ou.extract 0 32)))
    (hiSpot : iSpot = UInt256.ofNat (fromByteArrayBigEndian (o'.extract 64 96)))
    (hiRate : iRate = UInt256.ofNat (fromByteArrayBigEndian (o'.extract 32 64)))
    (hiDust : iDust = UInt256.ofNat (fromByteArrayBigEndian (o'.extract 128 160)))
    (hroomDef : room = (solcSlotWord σu I ⟨5⟩).sub (solcSlotWord σu I ⟨6⟩))
    (hmilkDunkDef : milkDunk = solcSlotWord σu I (solcMappingSlot ⟨1⟩ (biteIlkWord I) + ⟨2⟩))
    (hmilkChopDef : milkChop = solcSlotWord σu I (solcMappingSlot ⟨1⟩ (biteIlkWord I) + ⟨1⟩))
    (hdunkRoomDef : dunkRoom = if milkDunk.gt room = ⟨0⟩ then milkDunk else room)
    (hdunkRoomWadDef : dunkRoomWad = dunkRoom.mul ⟨1000000000000000000⟩)
    (hdartDenomDef : dartDenomRate = dunkRoomWad.div iRate)
    (hdartCandDef : dartCandidate = dartDenomRate.div milkChop)
    (hdartDef : dart = if art.gt dartCandidate = ⟨0⟩ then art else dartCandidate)
    (hinkDartDef : inkDart = UInt256.mul ink dart)
    (hdinkCandDef : dinkCandidate = UInt256.div inkDart art)
    (hdinkDef : dink = if UInt256.gt ink dinkCandidate = ⟨0⟩ then ink else dinkCandidate)
    (hDartPos : 0 < dart.toNat) (hDinkPos : 0 < dink.toNat)
    (hDartLim : ¬ (dart.toNat ≤ (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨255⟩).toNat)) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hdepthNe : I.depth ≠ 1024 := by omega
  have hposNe : ∀ w : UInt256, w ≠ ⟨0⟩ → 0 < w.toNat :=
    fun w hw => Nat.pos_of_ne_zero (fun h => hw (uint256_toNat_eq_zero h))
  have hqNat : q.toNat = 224 := by rw [hqfp]; native_decide
  have hlimEq : int256Limit = Int.ofNat ((UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨255⟩).toNat) := by
    native_decide
  obtain ⟨_, _, rd1810⟩ := catBiteTraceSeg7a rd1708 hlitterbox hroomdust (by simp)
  obtain ⟨_, _, rd1872⟩ := catBiteTraceSeg7b rd1810 hChop hDunk (by rw [hqNat]; native_decide)
    (by rw [hqNat]; native_decide) hRatePos hChopPos hdunkRoomDef.symm hFitWad hdunkRoomWadDef.symm
    hdartDenomDef.symm hdartCandDef.symm hdartDef.symm (by simp)
  obtain ⟨_, _, rd1985⟩ := catBiteTraceSeg7c rd1872 hArtPos hFitInkDart hinkDartDef.symm
    hdinkCandDef.symm hdinkDef.symm hDartPos hDinkPos (by simp)
  obtain ⟨_, _, rd2010⟩ := catBiteReachGuardDartLimit rd1985 (by omega) (by simp)
  obtain ⟨σs, As, σus, Aus, hIlksSolm, hUrnsSolm, hAmEq, hvatCodeIlkS⟩ :=
    catBiteMapUrns hAccounts hdepthNe hUrnsVatCode hIlksCall hUrnsCall
  set eUrnS := { initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I with
    accountMap := σus, substate := Aus, createdAccounts := cAu } with heUrnSdef
  have heUSam : eUrnS.accountMap = σus := rfl
  have heUSee : eUrnS.executionEnv = I := rfl
  have slotEqUS : ∀ s : UInt256, solcSlotWord σus I s = solcSlotWord σu I s := by
    intro s; simp only [solcSlotWord]
    rw [accountMapEquiv_storage_findD hAmEq I.codeOwner s ⟨0⟩]
  have uminEq : ∀ a b : UInt256, (if UInt256.gt a b = ⟨0⟩ then a else b) = umin a b := by
    intro a b; unfold umin
    by_cases h : a.toNat ≤ b.toNat
    · rw [if_pos (ugt_zero h), if_pos h]
    · rw [if_neg (by rw [ugt_one (by omega)]; decide), if_neg h]
  have hbr : ∀ (o : ByteArray) (k : ℕ), k + 32 ≤ o.size →
      ABI.bytesToWord ((o.toList.drop k).take 32) =
        UInt256.ofNat (fromByteArrayBigEndian (o.extract k (k + 32))) := by
    intro o k h
    rw [decode_word_at_eq_any o k h, uInt256OfByteArray_eq]
    congr 1; unfold fromByteArrayBigEndian; congr 1
    rw [byteArray_toList_eq (o.readBytes k 32), readBytes_at_toList_any o k h,
      byteArray_toList_eq (o.extract k (k + 32)), ByteArray.data_extract, Array.toList_extract,
      List.extract_eq_take_drop]
    simp
  have hIlksDec : config.externalABI.decode? "ilks" o' =
      some [bw (UInt256.ofNat (fromByteArrayBigEndian (o'.extract 0 32))), bw iRate, bw iSpot,
        bw (UInt256.ofNat (fromByteArrayBigEndian (o'.extract 96 128))), bw iDust] := by
    have h := catBiteIlksDecode_ok hilkslen
    rw [hbr o' 0 (by omega), hbr o' 32 (by omega), hbr o' 64 (by omega),
      hbr o' 96 (by omega), hbr o' 128 (by omega)] at h
    rw [hiRate, hiSpot, hiDust]; exact h
  have hUrnsDec : config.externalABI.decode? "urns" ou = some [bw ink, bw art] := by
    have h := catBiteUrnsDecode_ok hurnslen
    rw [hbr ou 0 (by omega), hbr ou 32 (by omega)] at h
    rw [hink, hart]; exact h
  have hlive' : catSlotWord ⟨2⟩ eUrnS.accountMap eUrnS.executionEnv = ⟨1⟩ := by
    rw [heUSam, heUSee]; simp only [catSlotWord]; rw [slotEqUS ⟨2⟩]
    simpa only [catSlotWord] using hlive
  have hratePos : 0 < iRate.toNat := by
    by_contra hc
    have hr0 : iRate.toNat = 0 := by omega
    have hz : (art * iRate).toNat = 0 := by
      rw [u256_mul_op_toNat, hr0, Nat.mul_zero, Nat.zero_mod]
    omega
  have hboxB : biteBoxW eUrnS = solcSlotWord σu I ⟨5⟩ := by
    simp only [biteBoxW, catSlotWord, heUSam, heUSee]; exact slotEqUS ⟨5⟩
  have hlitB : biteLitW eUrnS = solcSlotWord σu I ⟨6⟩ := by
    simp only [biteLitW, catSlotWord, heUSam, heUSee]; exact slotEqUS ⟨6⟩
  have hroomB : biteRoomV eUrnS = room := by
    rw [hroomDef]; simp only [biteRoomV, hboxB, hlitB]
  have hdunkB : biteDunkW I eUrnS = milkDunk := by
    rw [hmilkDunkDef]
    simp only [biteDunkW, catSlotWord, heUSam, heUSee, biteDunkSlot, biteFlipSlot_eq hsz36]
    exact slotEqUS _
  have hchopB : biteChopW I eUrnS = milkChop := by
    rw [hmilkChopDef]
    simp only [biteChopW, catSlotWord, heUSam, heUSee, biteChopSlot, biteFlipSlot_eq hsz36]
    exact slotEqUS _
  have hdunkroomB : biteDunkRoomV I eUrnS = dunkRoom := by
    rw [hdunkRoomDef, uminEq milkDunk room]
    simp only [biteDunkRoomV, hdunkB, hroomB]
  have hwad : wadU = ⟨1000000000000000000⟩ := by native_decide
  have hdartvB : biteDartV I eUrnS iRate art = dart := by
    have hcand : biteDartCandV I eUrnS iRate = dartCandidate := by
      simp only [biteDartCandV, biteDartDenomV, biteDunkRoomWadV, hchopB, hdunkroomB, hwad,
        hdartCandDef, hdartDenomDef, hdunkRoomWadDef]
      rfl
    rw [hdartDef, uminEq art dartCandidate]
    simp only [biteDartV, hcand]
  have hdinkvB : biteDinkV I eUrnS iRate art ink = dink := by
    have hcand : biteDinkCandV I eUrnS iRate art ink = dinkCandidate := by
      simp only [biteDinkCandV, biteInkDartV, hdartvB, hdinkCandDef, hinkDartDef]
      rfl
    rw [hdinkDef, uminEq ink dinkCandidate]
    simp only [biteDinkV, hcand]
  have hlitLtBox : (biteLitW eUrnS).toNat < (biteBoxW eUrnS).toNat := by
    rw [hlitB, hboxB]; exact hlitterbox
  have hroomGeDust : iDust.toNat ≤ (biteRoomV eUrnS).toNat := by rw [hroomB]; exact hroomdust
  have hbody := catBiteSourceDartLimitRevert hwv
    (catBiteVatCodePos_of_uniswap hAccounts hvatCode) hIlksSolm hIlksDec hvatCodeIlkS
    hUrnsSolm hUrnsDec hlive' hsz36 hfitInkSpot hfitArtRate hspotPos hratePos hunsafe hlitLtBox
    hroomGeDust (by rw [hdunkroomB, hwad, Nat.mul_comm]; exact hFitWad)
    (by rw [hchopB]; exact hposNe milkChop hChopPos)
    (by rw [hdartvB, Nat.mul_comm]; exact hFitInkDart) (hposNe art hArtPos)
    (by rw [hdartvB]; exact hDartPos) (by rw [hdinkvB]; exact hDinkPos)
    (by rw [hdartvB, hlimEq]; exact Int.ofNat_lt.mpr (by omega))
  exact catBiteMilkRequireStringRevertLeaf (okPc := ⟨2073⟩) (len := ⟨12⟩)
    (rawWord := ⟨0x4361742f6f766572666c6f77⟩) (shift := ⟨160⟩) (op := .PUSH12) (width := 12)
    hcode hdispatch hdecode rd2010 rfl (by native_decide) (by native_decide)
    (by unfold solcErrorStringRevertTailWf; repeat' first | apply And.intro | native_decide)
    (by decide) rfl (catBiteMilkSize320 hqfp hilkslen hosz hurnslen hoszu)
    (catBiteMilkRead64_320 hqfp hilkslen hosz hurnslen hoszu)
    (by simp only [List.length_cons, List.length_nil]; omega) hbody

set_option maxHeartbeats 2000000 in
/-- **`dink > 2²⁵⁵` require-string revert branch (extracted).** Post-milk (`aw=10`)
`require(dart ≤ 2²⁵⁵ && dink ≤ 2²⁵⁵, "Cat/overflow")` fails on the second conjunct (with
`dart ≤ 2²⁵⁵`): reaches the `PUSH2 2073` guard at pc 2010 (via
`Seg7a`/`Seg7b`/`Seg7c`/`catBiteReachGuardDinkLimit`), fires the fp=320 milk string-revert tail +
`catBiteSourceDinkLimitRevert`. -/
theorem catBiteRevertDinkLimit {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {σ' σu : AccountMap} {A' Au : Substate}
    {cA' cAu : Batteries.RBSet AccountAddress compare} {o' ou : ByteArray} {ku Cu : ℕ}
    {art ink iSpot iRate iDust room milkChop milkDunk dunkRoom dunkRoomWad dartDenomRate
      dartCandidate dart inkDart dinkCandidate dink q : UInt256}
    (hcode : I.code = catBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hdispatch : dispatchMsg contract I.calldata = some biteTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (biteTransition.params.map Param.name)
        (transitionSignature biteTransition).paramTypes I.calldata = some (biteLocals I))
    (hAccounts : accountMapEquiv σ_evm σ_solm) (hsz36 : 36 ≤ I.calldata.size)
    (hdepth : (I.depth : ℕ) < 1024)
    (hvatCode : ¬ Reasoning.Theory.extCodeSizeWord σ_evm (catBiteVatTargetWord σ_evm I) = ⟨0⟩)
    (hUrnsVatCode :
      ¬ Reasoning.Theory.extCodeSizeWord σ' ((catSlotWord ⟨3⟩ σ' I).land biteAddrMaskWord) = ⟨0⟩)
    (hIlksCall :
      typedCallViaEVM config (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        (AccountAddress.ofUInt256 (catBiteVatTargetWord σ_evm I)) "ilks" 0 [biteIlkVal I]
        (true, { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
                  accountMap := σ', substate := A', createdAccounts := cA' }, o') false)
    (hUrnsCall :
      typedCallViaEVM config
        { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
            accountMap := σ', createdAccounts := cA' }
        (AccountAddress.ofUInt256 ((catSlotWord ⟨3⟩ σ' I).land biteAddrMaskWord)) "urns" 0
        [biteIlkVal I, biteUrnVal I]
        (true, { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
                  accountMap := σu, substate := Au, createdAccounts := cAu }, ou) false)
    (hilkslen : 160 ≤ o'.size) (hurnslen : 64 ≤ ou.size)
    (hosz : o'.size < UInt256.size) (hoszu : ou.size < UInt256.size)
    (hurn : biteAddrMaskWord.land (biteAddrMaskWord.land (calldataWord I.calldata 36)) = biteUrnWord I)
    (hlive : catSlotWord ⟨2⟩ σu I = ⟨1⟩)
    (hmemI : 196 ≤ (catBiteIlksPostCallMem I o').size)
    (hmemUsz : 224 ≤ (catBiteUrnsPostCallMem I (catBiteIlksPostCallMem I o') ou).size)
    (hqfp : q = ⟨96⟩ + ⟨128⟩)
    (rd1708 : RD catBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1708⟩
      (room :: ⟨0⟩ :: ⟨0⟩ :: q :: art :: ink :: iDust :: iSpot :: iRate :: ⟨0⟩ ::
        biteAddrMaskWord.land (calldataWord I.calldata 36) :: biteIlkWord I :: ⟨419⟩ :: catSelWord I :: [])
      (catBiteMilkMem (catBiteUrnsPostCallMem I (catBiteIlksPostCallMem I o') ou) ⟨128⟩ (biteIlkWord I) q
        (biteAddrMaskWord.land (solcSlotWord σu I (solcMappingSlot ⟨1⟩ (biteIlkWord I)))) milkChop milkDunk)
      ⟨10⟩ ou (cAu, σu) ku Cu)
    (hChop : (if (⟨32⟩ + q).toNat ≥
          (catBiteMilkMem (catBiteUrnsPostCallMem I (catBiteIlksPostCallMem I o') ou) ⟨128⟩ (biteIlkWord I) q
            (biteAddrMaskWord.land (solcSlotWord σu I (solcMappingSlot ⟨1⟩ (biteIlkWord I)))) milkChop
            milkDunk).size ∨ (⟨32⟩ + q) ≥ (⟨10⟩ : UInt256) * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat (fromByteArrayBigEndian
        ((catBiteMilkMem (catBiteUrnsPostCallMem I (catBiteIlksPostCallMem I o') ou) ⟨128⟩ (biteIlkWord I) q
            (biteAddrMaskWord.land (solcSlotWord σu I (solcMappingSlot ⟨1⟩ (biteIlkWord I)))) milkChop
            milkDunk).readWithPadding (⟨32⟩ + q).toNat 32))) = milkChop)
    (hDunk : (if (⟨64⟩ + q).toNat ≥
          (catBiteMilkMem (catBiteUrnsPostCallMem I (catBiteIlksPostCallMem I o') ou) ⟨128⟩ (biteIlkWord I) q
            (biteAddrMaskWord.land (solcSlotWord σu I (solcMappingSlot ⟨1⟩ (biteIlkWord I)))) milkChop
            milkDunk).size ∨ (⟨64⟩ + q) ≥ (⟨10⟩ : UInt256) * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat (fromByteArrayBigEndian
        ((catBiteMilkMem (catBiteUrnsPostCallMem I (catBiteIlksPostCallMem I o') ou) ⟨128⟩ (biteIlkWord I) q
            (biteAddrMaskWord.land (solcSlotWord σu I (solcMappingSlot ⟨1⟩ (biteIlkWord I)))) milkChop
            milkDunk).readWithPadding (⟨64⟩ + q).toNat 32))) = milkDunk)
    (hlitterbox : (solcSlotWord σu I ⟨6⟩).toNat < (solcSlotWord σu I ⟨5⟩).toNat)
    (hroomdust : iDust.toNat ≤ room.toNat)
    (hunsafe : (ink * iSpot).toNat < (art * iRate).toNat)
    (hfitArtRate : art.toNat * iRate.toNat < UInt256.size)
    (hfitInkSpot : ink.toNat * iSpot.toNat < UInt256.size)
    (hspotPos : 0 < iSpot.toNat) (hRatePos : iRate ≠ ⟨0⟩) (hChopPos : milkChop ≠ ⟨0⟩)
    (hFitWad : (⟨1000000000000000000⟩ : UInt256).toNat * dunkRoom.toNat < UInt256.size)
    (hArtPos : art ≠ ⟨0⟩)
    (hFitInkDart : dart.toNat * ink.toNat < UInt256.size)
    (hart : art = UInt256.ofNat (fromByteArrayBigEndian (ou.extract 32 64)))
    (hink : ink = UInt256.ofNat (fromByteArrayBigEndian (ou.extract 0 32)))
    (hiSpot : iSpot = UInt256.ofNat (fromByteArrayBigEndian (o'.extract 64 96)))
    (hiRate : iRate = UInt256.ofNat (fromByteArrayBigEndian (o'.extract 32 64)))
    (hiDust : iDust = UInt256.ofNat (fromByteArrayBigEndian (o'.extract 128 160)))
    (hroomDef : room = (solcSlotWord σu I ⟨5⟩).sub (solcSlotWord σu I ⟨6⟩))
    (hmilkDunkDef : milkDunk = solcSlotWord σu I (solcMappingSlot ⟨1⟩ (biteIlkWord I) + ⟨2⟩))
    (hmilkChopDef : milkChop = solcSlotWord σu I (solcMappingSlot ⟨1⟩ (biteIlkWord I) + ⟨1⟩))
    (hdunkRoomDef : dunkRoom = if milkDunk.gt room = ⟨0⟩ then milkDunk else room)
    (hdunkRoomWadDef : dunkRoomWad = dunkRoom.mul ⟨1000000000000000000⟩)
    (hdartDenomDef : dartDenomRate = dunkRoomWad.div iRate)
    (hdartCandDef : dartCandidate = dartDenomRate.div milkChop)
    (hdartDef : dart = if art.gt dartCandidate = ⟨0⟩ then art else dartCandidate)
    (hinkDartDef : inkDart = UInt256.mul ink dart)
    (hdinkCandDef : dinkCandidate = UInt256.div inkDart art)
    (hdinkDef : dink = if UInt256.gt ink dinkCandidate = ⟨0⟩ then ink else dinkCandidate)
    (hDartPos : 0 < dart.toNat) (hDinkPos : 0 < dink.toNat)
    (hDartLim : dart.toNat ≤ (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨255⟩).toNat)
    (hDinkLim : ¬ (dink.toNat ≤ (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨255⟩).toNat)) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hdepthNe : I.depth ≠ 1024 := by omega
  have hposNe : ∀ w : UInt256, w ≠ ⟨0⟩ → 0 < w.toNat :=
    fun w hw => Nat.pos_of_ne_zero (fun h => hw (uint256_toNat_eq_zero h))
  have hqNat : q.toNat = 224 := by rw [hqfp]; native_decide
  have hlimEq : int256Limit = Int.ofNat ((UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨255⟩).toNat) := by
    native_decide
  obtain ⟨_, _, rd1810⟩ := catBiteTraceSeg7a rd1708 hlitterbox hroomdust (by simp)
  obtain ⟨_, _, rd1872⟩ := catBiteTraceSeg7b rd1810 hChop hDunk (by rw [hqNat]; native_decide)
    (by rw [hqNat]; native_decide) hRatePos hChopPos hdunkRoomDef.symm hFitWad hdunkRoomWadDef.symm
    hdartDenomDef.symm hdartCandDef.symm hdartDef.symm (by simp)
  obtain ⟨_, _, rd1985⟩ := catBiteTraceSeg7c rd1872 hArtPos hFitInkDart hinkDartDef.symm
    hdinkCandDef.symm hdinkDef.symm hDartPos hDinkPos (by simp)
  obtain ⟨_, _, rd2010⟩ := catBiteReachGuardDinkLimit rd1985 hDartLim (by simp)
  obtain ⟨σs, As, σus, Aus, hIlksSolm, hUrnsSolm, hAmEq, hvatCodeIlkS⟩ :=
    catBiteMapUrns hAccounts hdepthNe hUrnsVatCode hIlksCall hUrnsCall
  set eUrnS := { initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I with
    accountMap := σus, substate := Aus, createdAccounts := cAu } with heUrnSdef
  have heUSam : eUrnS.accountMap = σus := rfl
  have heUSee : eUrnS.executionEnv = I := rfl
  have slotEqUS : ∀ s : UInt256, solcSlotWord σus I s = solcSlotWord σu I s := by
    intro s; simp only [solcSlotWord]
    rw [accountMapEquiv_storage_findD hAmEq I.codeOwner s ⟨0⟩]
  have uminEq : ∀ a b : UInt256, (if UInt256.gt a b = ⟨0⟩ then a else b) = umin a b := by
    intro a b; unfold umin
    by_cases h : a.toNat ≤ b.toNat
    · rw [if_pos (ugt_zero h), if_pos h]
    · rw [if_neg (by rw [ugt_one (by omega)]; decide), if_neg h]
  have hbr : ∀ (o : ByteArray) (k : ℕ), k + 32 ≤ o.size →
      ABI.bytesToWord ((o.toList.drop k).take 32) =
        UInt256.ofNat (fromByteArrayBigEndian (o.extract k (k + 32))) := by
    intro o k h
    rw [decode_word_at_eq_any o k h, uInt256OfByteArray_eq]
    congr 1; unfold fromByteArrayBigEndian; congr 1
    rw [byteArray_toList_eq (o.readBytes k 32), readBytes_at_toList_any o k h,
      byteArray_toList_eq (o.extract k (k + 32)), ByteArray.data_extract, Array.toList_extract,
      List.extract_eq_take_drop]
    simp
  have hIlksDec : config.externalABI.decode? "ilks" o' =
      some [bw (UInt256.ofNat (fromByteArrayBigEndian (o'.extract 0 32))), bw iRate, bw iSpot,
        bw (UInt256.ofNat (fromByteArrayBigEndian (o'.extract 96 128))), bw iDust] := by
    have h := catBiteIlksDecode_ok hilkslen
    rw [hbr o' 0 (by omega), hbr o' 32 (by omega), hbr o' 64 (by omega),
      hbr o' 96 (by omega), hbr o' 128 (by omega)] at h
    rw [hiRate, hiSpot, hiDust]; exact h
  have hUrnsDec : config.externalABI.decode? "urns" ou = some [bw ink, bw art] := by
    have h := catBiteUrnsDecode_ok hurnslen
    rw [hbr ou 0 (by omega), hbr ou 32 (by omega)] at h
    rw [hink, hart]; exact h
  have hlive' : catSlotWord ⟨2⟩ eUrnS.accountMap eUrnS.executionEnv = ⟨1⟩ := by
    rw [heUSam, heUSee]; simp only [catSlotWord]; rw [slotEqUS ⟨2⟩]
    simpa only [catSlotWord] using hlive
  have hratePos : 0 < iRate.toNat := by
    by_contra hc
    have hr0 : iRate.toNat = 0 := by omega
    have hz : (art * iRate).toNat = 0 := by
      rw [u256_mul_op_toNat, hr0, Nat.mul_zero, Nat.zero_mod]
    omega
  have hboxB : biteBoxW eUrnS = solcSlotWord σu I ⟨5⟩ := by
    simp only [biteBoxW, catSlotWord, heUSam, heUSee]; exact slotEqUS ⟨5⟩
  have hlitB : biteLitW eUrnS = solcSlotWord σu I ⟨6⟩ := by
    simp only [biteLitW, catSlotWord, heUSam, heUSee]; exact slotEqUS ⟨6⟩
  have hroomB : biteRoomV eUrnS = room := by
    rw [hroomDef]; simp only [biteRoomV, hboxB, hlitB]
  have hdunkB : biteDunkW I eUrnS = milkDunk := by
    rw [hmilkDunkDef]
    simp only [biteDunkW, catSlotWord, heUSam, heUSee, biteDunkSlot, biteFlipSlot_eq hsz36]
    exact slotEqUS _
  have hchopB : biteChopW I eUrnS = milkChop := by
    rw [hmilkChopDef]
    simp only [biteChopW, catSlotWord, heUSam, heUSee, biteChopSlot, biteFlipSlot_eq hsz36]
    exact slotEqUS _
  have hdunkroomB : biteDunkRoomV I eUrnS = dunkRoom := by
    rw [hdunkRoomDef, uminEq milkDunk room]
    simp only [biteDunkRoomV, hdunkB, hroomB]
  have hwad : wadU = ⟨1000000000000000000⟩ := by native_decide
  have hdartvB : biteDartV I eUrnS iRate art = dart := by
    have hcand : biteDartCandV I eUrnS iRate = dartCandidate := by
      simp only [biteDartCandV, biteDartDenomV, biteDunkRoomWadV, hchopB, hdunkroomB, hwad,
        hdartCandDef, hdartDenomDef, hdunkRoomWadDef]
      rfl
    rw [hdartDef, uminEq art dartCandidate]
    simp only [biteDartV, hcand]
  have hdinkvB : biteDinkV I eUrnS iRate art ink = dink := by
    have hcand : biteDinkCandV I eUrnS iRate art ink = dinkCandidate := by
      simp only [biteDinkCandV, biteInkDartV, hdartvB, hdinkCandDef, hinkDartDef]
      rfl
    rw [hdinkDef, uminEq ink dinkCandidate]
    simp only [biteDinkV, hcand]
  have hlitLtBox : (biteLitW eUrnS).toNat < (biteBoxW eUrnS).toNat := by
    rw [hlitB, hboxB]; exact hlitterbox
  have hroomGeDust : iDust.toNat ≤ (biteRoomV eUrnS).toNat := by rw [hroomB]; exact hroomdust
  have hcondDinkLim : UInt256.isZero (UInt256.gt dink (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨255⟩))
      = ⟨0⟩ := by
    rw [ugt_one (show (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨255⟩).toNat < dink.toNat from by omega)]
    native_decide
  have hbody := catBiteSourceDinkLimitRevert hwv
    (catBiteVatCodePos_of_uniswap hAccounts hvatCode) hIlksSolm hIlksDec hvatCodeIlkS
    hUrnsSolm hUrnsDec hlive' hsz36 hfitInkSpot hfitArtRate hspotPos hratePos hunsafe hlitLtBox
    hroomGeDust (by rw [hdunkroomB, hwad, Nat.mul_comm]; exact hFitWad)
    (by rw [hchopB]; exact hposNe milkChop hChopPos)
    (by rw [hdartvB, Nat.mul_comm]; exact hFitInkDart) (hposNe art hArtPos)
    (by rw [hdartvB]; exact hDartPos) (by rw [hdinkvB]; exact hDinkPos)
    (by rw [hdartvB, hlimEq]; exact Int.ofNat_le.mpr (by omega))
    (by rw [hdinkvB, hlimEq]; exact Int.ofNat_lt.mpr (by omega))
  exact catBiteMilkRequireStringRevertLeaf (okPc := ⟨2073⟩) (len := ⟨12⟩)
    (rawWord := ⟨0x4361742f6f766572666c6f77⟩) (shift := ⟨160⟩) (op := .PUSH12) (width := 12)
    hcode hdispatch hdecode rd2010 hcondDinkLim (by native_decide) (by native_decide)
    (by unfold solcErrorStringRevertTailWf; repeat' first | apply And.intro | native_decide)
    (by decide) rfl (catBiteMilkSize320 hqfp hilkslen hosz hurnslen hoszu)
    (catBiteMilkRead64_320 hqfp hilkslen hosz hurnslen hoszu)
    (by simp only [List.length_cons, List.length_nil]; omega) hbody

/-! ## Post-milk full-word (`PUSH32`, no shift) `Error(string)` revert leaf

The `require(litter < box && room >= dust, "Cat/liquidation-limit-hit")` guard (pc 1730) pushes its
25-byte message as a single `PUSH32 word` (left-aligned, no `PUSH1 shift; SHL`), so it uses a
different tail bytecode than the ≤16-byte dart/dink strings.  This is the fp=320 / `aw=⟨10⟩` analogue
of `Reasoning`'s full-word tail — it reuses the same `catBiteMilkErrMem0-3` overlay. -/

@[reducible] def catBiteMilkFullWordRevertTailWf
    (code : ByteArray) (pc len word : UInt256) : Prop :=
  let p2 := pc + UInt256.ofNat 2
  let p3 := p2 + ⟨1⟩
  let p4 := p3 + ⟨1⟩
  let p8 := p4 + UInt256.ofNat 4
  let p10 := p8 + UInt256.ofNat 2
  let p11 := p10 + ⟨1⟩
  let p12 := p11 + ⟨1⟩
  let p13 := p12 + ⟨1⟩
  let p15 := p13 + UInt256.ofNat 2
  let p17 := p15 + UInt256.ofNat 2
  let p18 := p17 + ⟨1⟩
  let p19 := p18 + ⟨1⟩
  let p20 := p19 + ⟨1⟩
  let p22 := p20 + UInt256.ofNat 2
  let p24 := p22 + UInt256.ofNat 2
  let p25 := p24 + ⟨1⟩
  let p26 := p25 + ⟨1⟩
  let p27 := p26 + ⟨1⟩
  let p68 := p27 + UInt256.ofNat 33
  let pDup3 := p68 + UInt256.ofNat 2
  let pAdd := pDup3 + ⟨1⟩
  let pMstore3 := pAdd + ⟨1⟩
  let pSwap := pMstore3 + ⟨1⟩
  let pMload := pSwap + ⟨1⟩
  let pSwap2 := pMload + ⟨1⟩
  let pDup2 := pSwap2 + ⟨1⟩
  let pSwap3 := pDup2 + ⟨1⟩
  let pSub := pSwap3 + ⟨1⟩
  let p100 := pSub + ⟨1⟩
  let pAdd2 := p100 + UInt256.ofNat 2
  let pSwap4 := pAdd2 + ⟨1⟩
  let pRev := pSwap4 + ⟨1⟩
  decode code pc = some (.Push .PUSH1, some (⟨64⟩, 1))
  ∧ decode code p2 = some (.DUP1, .none)
  ∧ decode code p3 = some (.MLOAD, .none)
  ∧ decode code p4 = some (.Push .PUSH3, some (⟨4594637⟩, 3))
  ∧ decode code p8 = some (.Push .PUSH1, some (⟨229⟩, 1))
  ∧ decode code p10 = some (.SHL, .none)
  ∧ decode code p11 = some (.DUP2, .none)
  ∧ decode code p12 = some (.MSTORE, .none)
  ∧ decode code p13 = some (.Push .PUSH1, some (⟨32⟩, 1))
  ∧ decode code p15 = some (.Push .PUSH1, some (⟨4⟩, 1))
  ∧ decode code p17 = some (.DUP3, .none)
  ∧ decode code p18 = some (.ADD, .none)
  ∧ decode code p19 = some (.MSTORE, .none)
  ∧ decode code p20 = some (.Push .PUSH1, some (len, 1))
  ∧ decode code p22 = some (.Push .PUSH1, some (⟨36⟩, 1))
  ∧ decode code p24 = some (.DUP3, .none)
  ∧ decode code p25 = some (.ADD, .none)
  ∧ decode code p26 = some (.MSTORE, .none)
  ∧ decode code p27 = some (.Push .PUSH32, some (word, 32))
  ∧ decode code p68 = some (.Push .PUSH1, some (⟨68⟩, 1))
  ∧ decode code pDup3 = some (.DUP3, .none)
  ∧ decode code pAdd = some (.ADD, .none)
  ∧ decode code pMstore3 = some (.MSTORE, .none)
  ∧ decode code pSwap = some (.SWAP1, .none)
  ∧ decode code pMload = some (.MLOAD, .none)
  ∧ decode code pSwap2 = some (.SWAP1, .none)
  ∧ decode code pDup2 = some (.DUP2, .none)
  ∧ decode code pSwap3 = some (.SWAP1, .none)
  ∧ decode code pSub = some (.SUB, .none)
  ∧ decode code p100 = some (.Push .PUSH1, some (⟨100⟩, 1))
  ∧ decode code pAdd2 = some (.ADD, .none)
  ∧ decode code pSwap4 = some (.SWAP1, .none)
  ∧ decode code pRev = some (.REVERT, .none)

set_option maxHeartbeats 2000000 in
/-- **Post-milk (`fp = 320`, `aw = ⟨10⟩`) full-word (`PUSH32`) `Error(string)` revert tail.** Like
`RD.catBiteMilkErrorStringRevertTail` but the 25-byte message is a single `PUSH32 word` (no
`PUSH1 shift; SHL`); reuses the `catBiteMilkErrMem0-3` overlay. -/
theorem RD.catBiteMilkErrorStringFullWordRevertTail {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {pc len word : UInt256}
    {stk : List UInt256} {mem rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD code ee g s0 pc stk mem ⟨10⟩ rdata acc k C)
    (hwf : catBiteMilkFullWordRevertTailWf code pc len word)
    (hmem : mem.size = 320)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨320⟩)
    (hov : stk.length + 5 ≤ 1024) :
    RDrev code g s0 := by
  rcases hwf with
    ⟨hd0, hd2, hd3, hd4, hd8, hd10, hd11, hd12, hd13, hd15, hd17, hd18,
      hd19, hd20, hd22, hd24, hd25, hd26, hd27, hd68, hdDup3, hdAdd,
      hdMstore3, hdSwap, hdMload, hdSwap2, hdDup2, hdSwap3, hdSub, hd100,
      hdAdd2, hdSwap4, hdRev⟩
  have rdMload := evm_run h with [
    raw push1 ⟨64⟩ hd0 (by evm_ov),
    raw dup1 hd2 (by evm_ov),
    raw mload 0 ⟨320⟩ (UInt256.ofNat 10) hd3 mem_cost
      (mloadWordValue_of_readWithPadding (off := ⟨64⟩) (aw := ⟨10⟩) (v := ⟨320⟩)
        (by rw [hmem]; decide) (by decide) hread64)
      (by decide) (by evm_ov)]
  have rdSelectorRaw := rdMload.pushConst (⟨4594637⟩ : UInt256)
    (width := 3) (op := .PUSH3) (by decide) hd4 (by simp only [List.length_cons]; omega)
  have rdPrefix := evm_run rdSelectorRaw with [
    raw push1 ⟨229⟩ hd8 (by evm_ov),
    raw shl hd10 (by evm_ov),
    raw dup2 hd11 (by evm_ov),
    raw mstore 3 (catBiteMilkErrMem0 mem) (UInt256.ofNat 11)
      hd12 mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨32⟩ hd13 (by evm_ov),
    raw push1 ⟨4⟩ hd15 (by evm_ov),
    raw dup3 hd17 (by evm_ov),
    raw add hd18 (by evm_ov),
    raw mstore 3 (catBiteMilkErrMem1 mem) (UInt256.ofNat 12)
      hd19 mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 len hd20 (by evm_ov),
    raw push1 ⟨36⟩ hd22 (by evm_ov),
    raw dup3 hd24 (by evm_ov),
    raw add hd25 (by evm_ov),
    raw mstore 3 (catBiteMilkErrMem2 len mem) (UInt256.ofNat 13)
      hd26 mem_cost (by rfl) (by decide) (by evm_ov)]
  have rdRaw := rdPrefix.pushConst word (width := 32) (op := .PUSH32)
    (by decide) hd27 (by simp only [List.length_cons]; omega)
  exact evm_run rdRaw with [
    raw push1 ⟨68⟩ hd68 (by evm_ov),
    raw dup3 hdDup3 (by evm_ov),
    raw add hdAdd (by evm_ov),
    raw mstore 3 (catBiteMilkErrMem3 len word mem)
      (UInt256.ofNat 14) hdMstore3 mem_cost (by rfl) (by decide) (by evm_ov),
    raw swap1 hdSwap (by evm_ov),
    raw mload 0 ⟨320⟩ (UInt256.ofNat 14) hdMload
      mem_cost
      (catBiteMilkErrMem3_mload64 len word (UInt256.ofNat 14) hmem (by decide) hread64)
      (by decide) (by evm_ov),
    raw swap1 hdSwap2 (by evm_ov),
    raw dup2 hdDup2 (by evm_ov),
    raw swap1 hdSwap3 (by evm_ov),
    raw sub hdSub (by evm_ov),
    raw push1 ⟨100⟩ hd100 (by evm_ov),
    raw add hdAdd2 (by evm_ov),
    raw swap1 hdSwap4 (by evm_ov),
    raw rev 0 hdRev mem_cost (by evm_ov)]

/-- **Post-milk full-word `require(cond, "msg")`-false → `Error(string)` revert leaf.** Full-word
(`PUSH32`) analogue of `catBiteMilkRequireStringRevertLeaf`. -/
theorem catBiteMilkRequireStringFullWordRevertLeaf {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {mem rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {cond okPc : UInt256} {R : List UInt256} {k C : ℕ}
    {guardPc len word : UInt256}
    (hcode : I.code = catBytecode)
    (hdispatch : dispatchMsg contract I.calldata = some biteTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (biteTransition.params.map Param.name)
        (transitionSignature biteTransition).paramTypes I.calldata = some (biteLocals I))
    (rd : RD catBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) guardPc
      (cond :: R) mem ⟨10⟩ rdata acc k C)
    (hcond : cond = ⟨0⟩)
    (hpush2 : decode catBytecode guardPc = some (.Push .PUSH2, some (okPc, 2)))
    (hjumpi : decode catBytecode (guardPc + UInt256.ofNat 3) = some (.JUMPI, .none))
    (htail : catBiteMilkFullWordRevertTailWf catBytecode (guardPc + UInt256.ofNat 3 + ⟨1⟩) len word)
    (hmem : mem.size = 320)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨320⟩)
    (hov : R.length + 5 ≤ 1024)
    (hbody :
      ExecTransitionBody config contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) (biteLocals I)
        biteTransition.body .reverted) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have rd2 := rd.push2 okPc hpush2 (by simp only [List.length_cons]; omega)
  have rd3 := rd2.jumpiNT hjumpi hcond (by omega)
  have hrev := RD.catBiteMilkErrorStringFullWordRevertTail rd3 htail hmem hread64 hov
  simpa using hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody

set_option maxHeartbeats 2000000 in
/-- **`box ≤ litter` (room-require short-circuit) revert branch (extracted).** After the `Seg6`
`checkedSub` succeeded (`litter ≤ box`), `box ≤ litter` forces `litter = box`, so `room = 0` and the
`require(litter < box && …, "Cat/liquidation-limit-hit")` first conjunct fails.  Reaches the guard at
pc 1730 (`catBiteReachGuardLitter`), fires the fp=320 full-word tail + `catBiteSourceLitterGeBoxRevert`. -/
theorem catBiteRevertLitterGeBox {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {σ' σu : AccountMap} {A' Au : Substate}
    {cA' cAu : Batteries.RBSet AccountAddress compare} {o' ou : ByteArray} {ku Cu : ℕ}
    {art ink iSpot iRate iDust room milkChop milkDunk q : UInt256}
    (hcode : I.code = catBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hdispatch : dispatchMsg contract I.calldata = some biteTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (biteTransition.params.map Param.name)
        (transitionSignature biteTransition).paramTypes I.calldata = some (biteLocals I))
    (hAccounts : accountMapEquiv σ_evm σ_solm) (hsz36 : 36 ≤ I.calldata.size)
    (hdepth : (I.depth : ℕ) < 1024)
    (hvatCode : ¬ Reasoning.Theory.extCodeSizeWord σ_evm (catBiteVatTargetWord σ_evm I) = ⟨0⟩)
    (hUrnsVatCode :
      ¬ Reasoning.Theory.extCodeSizeWord σ' ((catSlotWord ⟨3⟩ σ' I).land biteAddrMaskWord) = ⟨0⟩)
    (hIlksCall :
      typedCallViaEVM config (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        (AccountAddress.ofUInt256 (catBiteVatTargetWord σ_evm I)) "ilks" 0 [biteIlkVal I]
        (true, { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
                  accountMap := σ', substate := A', createdAccounts := cA' }, o') false)
    (hUrnsCall :
      typedCallViaEVM config
        { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
            accountMap := σ', createdAccounts := cA' }
        (AccountAddress.ofUInt256 ((catSlotWord ⟨3⟩ σ' I).land biteAddrMaskWord)) "urns" 0
        [biteIlkVal I, biteUrnVal I]
        (true, { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
                  accountMap := σu, substate := Au, createdAccounts := cAu }, ou) false)
    (hilkslen : 160 ≤ o'.size) (hurnslen : 64 ≤ ou.size)
    (hosz : o'.size < UInt256.size) (hoszu : ou.size < UInt256.size)
    (hurn : biteAddrMaskWord.land (biteAddrMaskWord.land (calldataWord I.calldata 36)) = biteUrnWord I)
    (hlive : catSlotWord ⟨2⟩ σu I = ⟨1⟩)
    (hmemI : 196 ≤ (catBiteIlksPostCallMem I o').size)
    (hmemUsz : 224 ≤ (catBiteUrnsPostCallMem I (catBiteIlksPostCallMem I o') ou).size)
    (hqfp : q = ⟨96⟩ + ⟨128⟩)
    (rd1708 : RD catBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1708⟩
      (room :: ⟨0⟩ :: ⟨0⟩ :: q :: art :: ink :: iDust :: iSpot :: iRate :: ⟨0⟩ ::
        biteAddrMaskWord.land (calldataWord I.calldata 36) :: biteIlkWord I :: ⟨419⟩ :: catSelWord I :: [])
      (catBiteMilkMem (catBiteUrnsPostCallMem I (catBiteIlksPostCallMem I o') ou) ⟨128⟩ (biteIlkWord I) q
        (biteAddrMaskWord.land (solcSlotWord σu I (solcMappingSlot ⟨1⟩ (biteIlkWord I)))) milkChop milkDunk)
      ⟨10⟩ ou (cAu, σu) ku Cu)
    (hunsafe : (ink * iSpot).toNat < (art * iRate).toNat)
    (hfitArtRate : art.toNat * iRate.toNat < UInt256.size)
    (hfitInkSpot : ink.toNat * iSpot.toNat < UInt256.size)
    (hspotPos : 0 < iSpot.toNat)
    (hart : art = UInt256.ofNat (fromByteArrayBigEndian (ou.extract 32 64)))
    (hink : ink = UInt256.ofNat (fromByteArrayBigEndian (ou.extract 0 32)))
    (hiSpot : iSpot = UInt256.ofNat (fromByteArrayBigEndian (o'.extract 64 96)))
    (hiRate : iRate = UInt256.ofNat (fromByteArrayBigEndian (o'.extract 32 64)))
    (hiDust : iDust = UInt256.ofNat (fromByteArrayBigEndian (o'.extract 128 160)))
    (hle : (solcSlotWord σu I ⟨6⟩).toNat ≤ (solcSlotWord σu I ⟨5⟩).toNat)
    (hlitterbox : ¬ ((solcSlotWord σu I ⟨6⟩).toNat < (solcSlotWord σu I ⟨5⟩).toNat)) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hdepthNe : I.depth ≠ 1024 := by omega
  have hposNe : ∀ w : UInt256, w ≠ ⟨0⟩ → 0 < w.toNat :=
    fun w hw => Nat.pos_of_ne_zero (fun h => hw (uint256_toNat_eq_zero h))
  have hLitterFail : (solcSlotWord σu I ⟨5⟩).toNat ≤ (solcSlotWord σu I ⟨6⟩).toNat := by omega
  obtain ⟨_, _, rd1730⟩ := catBiteReachGuardLitter rd1708 hLitterFail (by simp)
  obtain ⟨σs, As, σus, Aus, hIlksSolm, hUrnsSolm, hAmEq, hvatCodeIlkS⟩ :=
    catBiteMapUrns hAccounts hdepthNe hUrnsVatCode hIlksCall hUrnsCall
  set eUrnS := { initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I with
    accountMap := σus, substate := Aus, createdAccounts := cAu } with heUrnSdef
  have heUSam : eUrnS.accountMap = σus := rfl
  have heUSee : eUrnS.executionEnv = I := rfl
  have slotEqUS : ∀ s : UInt256, solcSlotWord σus I s = solcSlotWord σu I s := by
    intro s; simp only [solcSlotWord]
    rw [accountMapEquiv_storage_findD hAmEq I.codeOwner s ⟨0⟩]
  have hbr : ∀ (o : ByteArray) (k : ℕ), k + 32 ≤ o.size →
      ABI.bytesToWord ((o.toList.drop k).take 32) =
        UInt256.ofNat (fromByteArrayBigEndian (o.extract k (k + 32))) := by
    intro o k h
    rw [decode_word_at_eq_any o k h, uInt256OfByteArray_eq]
    congr 1; unfold fromByteArrayBigEndian; congr 1
    rw [byteArray_toList_eq (o.readBytes k 32), readBytes_at_toList_any o k h,
      byteArray_toList_eq (o.extract k (k + 32)), ByteArray.data_extract, Array.toList_extract,
      List.extract_eq_take_drop]
    simp
  have hIlksDec : config.externalABI.decode? "ilks" o' =
      some [bw (UInt256.ofNat (fromByteArrayBigEndian (o'.extract 0 32))), bw iRate, bw iSpot,
        bw (UInt256.ofNat (fromByteArrayBigEndian (o'.extract 96 128))), bw iDust] := by
    have h := catBiteIlksDecode_ok hilkslen
    rw [hbr o' 0 (by omega), hbr o' 32 (by omega), hbr o' 64 (by omega),
      hbr o' 96 (by omega), hbr o' 128 (by omega)] at h
    rw [hiRate, hiSpot, hiDust]; exact h
  have hUrnsDec : config.externalABI.decode? "urns" ou = some [bw ink, bw art] := by
    have h := catBiteUrnsDecode_ok hurnslen
    rw [hbr ou 0 (by omega), hbr ou 32 (by omega)] at h
    rw [hink, hart]; exact h
  have hlive' : catSlotWord ⟨2⟩ eUrnS.accountMap eUrnS.executionEnv = ⟨1⟩ := by
    rw [heUSam, heUSee]; simp only [catSlotWord]; rw [slotEqUS ⟨2⟩]
    simpa only [catSlotWord] using hlive
  have hratePos : 0 < iRate.toNat := by
    by_contra hc
    have hr0 : iRate.toNat = 0 := by omega
    have hz : (art * iRate).toNat = 0 := by
      rw [u256_mul_op_toNat, hr0, Nat.mul_zero, Nat.zero_mod]
    omega
  have hboxB : biteBoxW eUrnS = solcSlotWord σu I ⟨5⟩ := by
    simp only [biteBoxW, catSlotWord, heUSam, heUSee]; exact slotEqUS ⟨5⟩
  have hlitB : biteLitW eUrnS = solcSlotWord σu I ⟨6⟩ := by
    simp only [biteLitW, catSlotWord, heUSam, heUSee]; exact slotEqUS ⟨6⟩
  have hlitEqBox : (biteLitW eUrnS).toNat = (biteBoxW eUrnS).toNat := by rw [hlitB, hboxB]; omega
  have hbody := catBiteSourceLitterGeBoxRevert hwv
    (catBiteVatCodePos_of_uniswap hAccounts hvatCode) hIlksSolm hIlksDec hvatCodeIlkS
    hUrnsSolm hUrnsDec hlive' hsz36 hfitInkSpot hfitArtRate hspotPos hratePos hunsafe hlitEqBox
  exact catBiteMilkRequireStringFullWordRevertLeaf (okPc := ⟨1810⟩) (len := ⟨25⟩)
    (word := ⟨0x4361742f6c69717569646174696f6e2d6c696d69742d68697400000000000000⟩)
    hcode hdispatch hdecode rd1730 rfl (by native_decide) (by native_decide)
    (by unfold catBiteMilkFullWordRevertTailWf; repeat' first | apply And.intro | native_decide)
    (catBiteMilkSize320 hqfp hilkslen hosz hurnslen hoszu)
    (catBiteMilkRead64_320 hqfp hilkslen hosz hurnslen hoszu)
    (by simp only [List.length_cons, List.length_nil]; omega) hbody

set_option maxHeartbeats 2000000 in
/-- **`dust > room` (`room < dust`) require revert branch (extracted).** After `litter < box`, the
second conjunct of `require(litter < box && room >= dust, "Cat/liquidation-limit-hit")` fails
(`room < dust`).  Reaches the guard at pc 1730 (`catBiteReachGuardRoomDust`), fires the fp=320
full-word tail + `catBiteSourceRoomLtDustRevert`. -/
theorem catBiteRevertRoomDust {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {σ' σu : AccountMap} {A' Au : Substate}
    {cA' cAu : Batteries.RBSet AccountAddress compare} {o' ou : ByteArray} {ku Cu : ℕ}
    {art ink iSpot iRate iDust room milkChop milkDunk q : UInt256}
    (hcode : I.code = catBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hdispatch : dispatchMsg contract I.calldata = some biteTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (biteTransition.params.map Param.name)
        (transitionSignature biteTransition).paramTypes I.calldata = some (biteLocals I))
    (hAccounts : accountMapEquiv σ_evm σ_solm) (hsz36 : 36 ≤ I.calldata.size)
    (hdepth : (I.depth : ℕ) < 1024)
    (hvatCode : ¬ Reasoning.Theory.extCodeSizeWord σ_evm (catBiteVatTargetWord σ_evm I) = ⟨0⟩)
    (hUrnsVatCode :
      ¬ Reasoning.Theory.extCodeSizeWord σ' ((catSlotWord ⟨3⟩ σ' I).land biteAddrMaskWord) = ⟨0⟩)
    (hIlksCall :
      typedCallViaEVM config (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        (AccountAddress.ofUInt256 (catBiteVatTargetWord σ_evm I)) "ilks" 0 [biteIlkVal I]
        (true, { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
                  accountMap := σ', substate := A', createdAccounts := cA' }, o') false)
    (hUrnsCall :
      typedCallViaEVM config
        { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
            accountMap := σ', createdAccounts := cA' }
        (AccountAddress.ofUInt256 ((catSlotWord ⟨3⟩ σ' I).land biteAddrMaskWord)) "urns" 0
        [biteIlkVal I, biteUrnVal I]
        (true, { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
                  accountMap := σu, substate := Au, createdAccounts := cAu }, ou) false)
    (hilkslen : 160 ≤ o'.size) (hurnslen : 64 ≤ ou.size)
    (hosz : o'.size < UInt256.size) (hoszu : ou.size < UInt256.size)
    (hurn : biteAddrMaskWord.land (biteAddrMaskWord.land (calldataWord I.calldata 36)) = biteUrnWord I)
    (hlive : catSlotWord ⟨2⟩ σu I = ⟨1⟩)
    (hmemI : 196 ≤ (catBiteIlksPostCallMem I o').size)
    (hmemUsz : 224 ≤ (catBiteUrnsPostCallMem I (catBiteIlksPostCallMem I o') ou).size)
    (hqfp : q = ⟨96⟩ + ⟨128⟩)
    (rd1708 : RD catBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1708⟩
      (room :: ⟨0⟩ :: ⟨0⟩ :: q :: art :: ink :: iDust :: iSpot :: iRate :: ⟨0⟩ ::
        biteAddrMaskWord.land (calldataWord I.calldata 36) :: biteIlkWord I :: ⟨419⟩ :: catSelWord I :: [])
      (catBiteMilkMem (catBiteUrnsPostCallMem I (catBiteIlksPostCallMem I o') ou) ⟨128⟩ (biteIlkWord I) q
        (biteAddrMaskWord.land (solcSlotWord σu I (solcMappingSlot ⟨1⟩ (biteIlkWord I)))) milkChop milkDunk)
      ⟨10⟩ ou (cAu, σu) ku Cu)
    (hunsafe : (ink * iSpot).toNat < (art * iRate).toNat)
    (hfitArtRate : art.toNat * iRate.toNat < UInt256.size)
    (hfitInkSpot : ink.toNat * iSpot.toNat < UInt256.size)
    (hspotPos : 0 < iSpot.toNat)
    (hart : art = UInt256.ofNat (fromByteArrayBigEndian (ou.extract 32 64)))
    (hink : ink = UInt256.ofNat (fromByteArrayBigEndian (ou.extract 0 32)))
    (hiSpot : iSpot = UInt256.ofNat (fromByteArrayBigEndian (o'.extract 64 96)))
    (hiRate : iRate = UInt256.ofNat (fromByteArrayBigEndian (o'.extract 32 64)))
    (hiDust : iDust = UInt256.ofNat (fromByteArrayBigEndian (o'.extract 128 160)))
    (hroomDef : room = (solcSlotWord σu I ⟨5⟩).sub (solcSlotWord σu I ⟨6⟩))
    (hlitterbox : (solcSlotWord σu I ⟨6⟩).toNat < (solcSlotWord σu I ⟨5⟩).toNat)
    (hroomdust : ¬ (iDust.toNat ≤ room.toNat)) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hdepthNe : I.depth ≠ 1024 := by omega
  have hposNe : ∀ w : UInt256, w ≠ ⟨0⟩ → 0 < w.toNat :=
    fun w hw => Nat.pos_of_ne_zero (fun h => hw (uint256_toNat_eq_zero h))
  obtain ⟨_, _, rd1730⟩ := catBiteReachGuardRoomDust rd1708 hlitterbox (by simp)
  obtain ⟨σs, As, σus, Aus, hIlksSolm, hUrnsSolm, hAmEq, hvatCodeIlkS⟩ :=
    catBiteMapUrns hAccounts hdepthNe hUrnsVatCode hIlksCall hUrnsCall
  set eUrnS := { initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I with
    accountMap := σus, substate := Aus, createdAccounts := cAu } with heUrnSdef
  have heUSam : eUrnS.accountMap = σus := rfl
  have heUSee : eUrnS.executionEnv = I := rfl
  have slotEqUS : ∀ s : UInt256, solcSlotWord σus I s = solcSlotWord σu I s := by
    intro s; simp only [solcSlotWord]
    rw [accountMapEquiv_storage_findD hAmEq I.codeOwner s ⟨0⟩]
  have hbr : ∀ (o : ByteArray) (k : ℕ), k + 32 ≤ o.size →
      ABI.bytesToWord ((o.toList.drop k).take 32) =
        UInt256.ofNat (fromByteArrayBigEndian (o.extract k (k + 32))) := by
    intro o k h
    rw [decode_word_at_eq_any o k h, uInt256OfByteArray_eq]
    congr 1; unfold fromByteArrayBigEndian; congr 1
    rw [byteArray_toList_eq (o.readBytes k 32), readBytes_at_toList_any o k h,
      byteArray_toList_eq (o.extract k (k + 32)), ByteArray.data_extract, Array.toList_extract,
      List.extract_eq_take_drop]
    simp
  have hIlksDec : config.externalABI.decode? "ilks" o' =
      some [bw (UInt256.ofNat (fromByteArrayBigEndian (o'.extract 0 32))), bw iRate, bw iSpot,
        bw (UInt256.ofNat (fromByteArrayBigEndian (o'.extract 96 128))), bw iDust] := by
    have h := catBiteIlksDecode_ok hilkslen
    rw [hbr o' 0 (by omega), hbr o' 32 (by omega), hbr o' 64 (by omega),
      hbr o' 96 (by omega), hbr o' 128 (by omega)] at h
    rw [hiRate, hiSpot, hiDust]; exact h
  have hUrnsDec : config.externalABI.decode? "urns" ou = some [bw ink, bw art] := by
    have h := catBiteUrnsDecode_ok hurnslen
    rw [hbr ou 0 (by omega), hbr ou 32 (by omega)] at h
    rw [hink, hart]; exact h
  have hlive' : catSlotWord ⟨2⟩ eUrnS.accountMap eUrnS.executionEnv = ⟨1⟩ := by
    rw [heUSam, heUSee]; simp only [catSlotWord]; rw [slotEqUS ⟨2⟩]
    simpa only [catSlotWord] using hlive
  have hratePos : 0 < iRate.toNat := by
    by_contra hc
    have hr0 : iRate.toNat = 0 := by omega
    have hz : (art * iRate).toNat = 0 := by
      rw [u256_mul_op_toNat, hr0, Nat.mul_zero, Nat.zero_mod]
    omega
  have hboxB : biteBoxW eUrnS = solcSlotWord σu I ⟨5⟩ := by
    simp only [biteBoxW, catSlotWord, heUSam, heUSee]; exact slotEqUS ⟨5⟩
  have hlitB : biteLitW eUrnS = solcSlotWord σu I ⟨6⟩ := by
    simp only [biteLitW, catSlotWord, heUSam, heUSee]; exact slotEqUS ⟨6⟩
  have hroomB : biteRoomV eUrnS = room := by
    rw [hroomDef]; simp only [biteRoomV, hboxB, hlitB]
  have hlitLtBox : (biteLitW eUrnS).toNat < (biteBoxW eUrnS).toNat := by rw [hlitB, hboxB]; exact hlitterbox
  have hroomLtDust : (biteRoomV eUrnS).toNat < iDust.toNat := by rw [hroomB]; omega
  have hcond : UInt256.isZero (UInt256.lt room iDust) = ⟨0⟩ := by
    rw [ult_one (show room.toNat < iDust.toNat from by omega)]; native_decide
  have hbody := catBiteSourceRoomLtDustRevert hwv
    (catBiteVatCodePos_of_uniswap hAccounts hvatCode) hIlksSolm hIlksDec hvatCodeIlkS
    hUrnsSolm hUrnsDec hlive' hsz36 hfitInkSpot hfitArtRate hspotPos hratePos hunsafe hlitLtBox
    hroomLtDust
  exact catBiteMilkRequireStringFullWordRevertLeaf (okPc := ⟨1810⟩) (len := ⟨25⟩)
    (word := ⟨0x4361742f6c69717569646174696f6e2d6c696d69742d68697400000000000000⟩)
    hcode hdispatch hdecode rd1730 hcond (by native_decide) (by native_decide)
    (by unfold catBiteMilkFullWordRevertTailWf; repeat' first | apply And.intro | native_decide)
    (catBiteMilkSize320 hqfp hilkslen hosz hurnslen hoszu)
    (catBiteMilkRead64_320 hqfp hilkslen hosz hurnslen hoszu)
    (by simp only [List.length_cons, List.length_nil]; omega) hbody


set_option maxHeartbeats 4000000 in
/-- **fess no-code branch (extracted).** grab succeeds; the `EXTCODESIZE(vow)` guard before the
`vow.fess(...)` CALL is false (empty code), so the EVM reverts at pc `2284` before any call. Maps
ilks+urns+grab to σ_solm, fires the generic `RD.solcExtcodesizeGuardMissing` at the abstract
post-grab account map + `catBiteSourceFessNoCodeRevert`. Dual of `catBiteRevertFessFail`. -/
theorem catBiteRevertFessNoCode {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {σ' σu σg : AccountMap} {A' Au Ag : Substate}
    {cA' cAu cAg : Batteries.RBSet AccountAddress compare} {o' ou og o2 : ByteArray}
    {mem2 : ByteArray} {aw2 : UInt256} {R2 : List UInt256} {k2 C2 : ℕ}
    {art ink iSpot iRate iDust room milkDunk milkChop dunkRoom dunkRoomWad
      dartDenomRate dartCandidate dart inkDart dinkCandidate dink : UInt256}
    (hcode : I.code = catBytecode)
    (hdispatch : dispatchMsg contract I.calldata = some biteTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (biteTransition.params.map Param.name)
        (transitionSignature biteTransition).paramTypes I.calldata = some (biteLocals I))
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hwv : I.weiValue = ⟨0⟩) (hperm : I.perm = true) (hsz36 : 36 ≤ I.calldata.size)
    (hdepth : (I.depth : ℕ) < 1024)
    (hurn : biteAddrMaskWord.land (biteAddrMaskWord.land (calldataWord I.calldata 36)) = biteUrnWord I)
    (hilkslen : 160 ≤ o'.size) (hurnslen : 64 ≤ ou.size)
    (hlive : catSlotWord ⟨2⟩ σu I = ⟨1⟩)
    (hvatCode : ¬ Reasoning.Theory.extCodeSizeWord σ_evm (catBiteVatTargetWord σ_evm I) = ⟨0⟩)
    (hUrnsVatCode :
      ¬ Reasoning.Theory.extCodeSizeWord σ' ((catSlotWord ⟨3⟩ σ' I).land biteAddrMaskWord) = ⟨0⟩)
    (hGrabCode :
      ¬ Reasoning.Theory.extCodeSizeWord σu ((solcSlotWord σu I ⟨3⟩).land biteAddrMaskWord) = ⟨0⟩)
    (hFessCode :
      Reasoning.Theory.extCodeSizeWord σg (biteAddrMaskWord.land (solcSlotWord σg I ⟨4⟩)) = ⟨0⟩)
    (hIlksCall :
      typedCallViaEVM config (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        (AccountAddress.ofUInt256 (catBiteVatTargetWord σ_evm I)) "ilks" 0 [biteIlkVal I]
        (true, { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
                  accountMap := σ', substate := A', createdAccounts := cA' }, o') false)
    (hUrnsCall :
      typedCallViaEVM config
        { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
            accountMap := σ', createdAccounts := cA' }
        (AccountAddress.ofUInt256 ((catSlotWord ⟨3⟩ σ' I).land biteAddrMaskWord)) "urns" 0
        [biteIlkVal I, biteUrnVal I]
        (true, { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
                  accountMap := σu, substate := Au, createdAccounts := cAu }, ou) false)
    (hGrabCall :
      typedCallViaEVM config
        { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
            accountMap := σu, createdAccounts := cAu }
        (AccountAddress.ofUInt256 ((solcSlotWord σu I ⟨3⟩).land biteAddrMaskWord)) "grab" 0
        [Value.fixedBytes bytes32Width (EVM.Word.toBytesBE (biteIlkWord I)),
          Value.address (AccountAddress.ofNat
            (biteAddrMaskWord.land (biteAddrMaskWord.land (calldataWord I.calldata 36))).toNat),
          Value.address (AccountAddress.ofNat (UInt256.ofNat I.codeOwner.val).toNat),
          Value.address (AccountAddress.ofNat (biteAddrMaskWord.land (solcSlotWord σu I ⟨4⟩)).toNat),
          Value.int (-Int.ofNat dink.toNat), Value.int (-Int.ofNat dart.toNat)]
        (true, { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
                  accountMap := σg, substate := Ag, createdAccounts := cAg }, og) I.perm)
    (rd2284 :
      RD catBytecode I (Sat256.ofUInt256 g) (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        ⟨2284⟩ (biteAddrMaskWord.land (solcSlotWord σg I ⟨4⟩) ::
          biteAddrMaskWord.land (solcSlotWord σg I ⟨4⟩) :: R2) mem2 aw2 o2 (cAg, σg) k2 C2)
    (hov2 : R2.length + 4 ≤ 1024)
    (hRateFit : iRate.toNat * dart.toNat < UInt256.size)
    (hart : art = UInt256.ofNat (fromByteArrayBigEndian (ou.extract 32 64)))
    (hink : ink = UInt256.ofNat (fromByteArrayBigEndian (ou.extract 0 32)))
    (hiSpot : iSpot = UInt256.ofNat (fromByteArrayBigEndian (o'.extract 64 96)))
    (hiRate : iRate = UInt256.ofNat (fromByteArrayBigEndian (o'.extract 32 64)))
    (hiDustDef : iDust = UInt256.ofNat (fromByteArrayBigEndian (o'.extract 128 160)))
    (hroomDef : room = (solcSlotWord σu I ⟨5⟩).sub (solcSlotWord σu I ⟨6⟩))
    (hmilkDunkDef : milkDunk = solcSlotWord σu I (solcMappingSlot ⟨1⟩ (biteIlkWord I) + ⟨2⟩))
    (hmilkChopDef : milkChop = solcSlotWord σu I (solcMappingSlot ⟨1⟩ (biteIlkWord I) + ⟨1⟩))
    (hdunkRoomDef : dunkRoom = if milkDunk.gt room = ⟨0⟩ then milkDunk else room)
    (hdunkRoomWadDef : dunkRoomWad = dunkRoom.mul ⟨1000000000000000000⟩)
    (hdartDenomDef : dartDenomRate = dunkRoomWad.div iRate)
    (hdartCandDef : dartCandidate = dartDenomRate.div milkChop)
    (hdartDef : dart = if art.gt dartCandidate = ⟨0⟩ then art else dartCandidate)
    (hinkDartDef : inkDart = ink.mul dart)
    (hdinkCandDef : dinkCandidate = inkDart.div art)
    (hdinkDef : dink = if ink.gt dinkCandidate = ⟨0⟩ then ink else dinkCandidate)
    (hspotPos : 0 < iSpot.toNat) (hfitArtRate : art.toNat * iRate.toNat < UInt256.size)
    (hfitInkSpot : ink.toNat * iSpot.toNat < UInt256.size)
    (hunsafe : (ink * iSpot).toNat < (art * iRate).toNat)
    (hlitterbox : (solcSlotWord σu I ⟨6⟩).toNat < (solcSlotWord σu I ⟨5⟩).toNat)
    (hroomdust : iDust.toNat ≤ room.toNat)
    (hRatePos : iRate ≠ ⟨0⟩) (hChopPos : milkChop ≠ ⟨0⟩)
    (hFitWad : (⟨1000000000000000000⟩ : UInt256).toNat * dunkRoom.toNat < UInt256.size)
    (hArtPos : art ≠ ⟨0⟩) (hFitInkDart : dart.toNat * ink.toNat < UInt256.size)
    (hDartPos : 0 < dart.toNat) (hDinkPos : 0 < dink.toNat)
    (hDartLim : dart.toNat ≤ (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨255⟩).toNat)
    (hDinkLim : dink.toNat ≤ (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨255⟩).toNat) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hdepthNe : I.depth ≠ 1024 := by omega
  have hmask : biteAddrMaskWord = solcAddrMask := by native_decide
  have hposNe : ∀ w : UInt256, w ≠ ⟨0⟩ → 0 < w.toNat :=
    fun w hw => Nat.pos_of_ne_zero (fun h => hw (uint256_toNat_eq_zero h))
  have codePos : ∀ (e : EVM.State) (w : UInt256),
      extCodeSizeWord e.accountMap w ≠ ⟨0⟩ →
      0 < (UInt256.ofNat ((e.lookupAccount
        (AccountAddress.ofUInt256 w)).option 0
        (fun acc => acc.code.size))).toNat := by
    intro e w hw
    unfold extCodeSizeWord at hw
    simp only [State.lookupAccount]
    cases hf : e.accountMap.find? (AccountAddress.ofUInt256 w) with
    | none => rw [hf] at hw; simp [Option.option] at hw
    | some acc =>
        rw [hf] at hw
        simp only [Option.option, Function.comp] at hw ⊢
        exact hposNe _ hw
  have addrId : ∀ a : AccountAddress, EVM.address a.val = a := by
    intro a; apply Fin.ext
    show a.val % EVM.addressModulus = a.val
    rw [show EVM.addressModulus = AccountAddress.size from by decide]
    exact Nat.mod_eq_of_lt a.isLt
  have hAddrRT : ∀ a : AccountAddress,
      AccountAddress.ofNat (UInt256.ofNat a.val).toNat = a := by
    intro a
    have h1 : (UInt256.ofNat a.val).toNat = a.val :=
      UInt256.toNat_ofNat_of_lt (lt_of_lt_of_le a.isLt
        (show AccountAddress.size ≤ UInt256.size from by decide))
    rw [h1]; apply Fin.ext
    simp only [AccountAddress.ofNat, Fin.ofNat]
    exact Nat.mod_eq_of_lt a.isLt
  have hbytes : biteIlkBytes I = EVM.Word.toBytesBE (biteIlkWord I) := by
    have hlen32 : (biteIlkBytes I).length = 32 := by
      simp only [biteIlkBytes, List.length_take, List.length_drop]
      have htlen : I.calldata.toList.length = I.calldata.size := by
        rw [byteArray_toList_eq, Array.length_toList]; rfl
      rw [htlen]; omega
    have hword : ABI.bytesToWord (biteIlkBytes I) = biteIlkWord I := by
      simpa [biteIlkBytes, biteIlkWord] using
        (decode_word_at_eq_any I.calldata 4 (by simpa using hsz36))
    have hto := toBytesBE_bytesToWord_of_length (bs := biteIlkBytes I) hlen32
    rw [hword] at hto; exact hto.symm
  have uminEq : ∀ a b : UInt256,
      (if UInt256.gt a b = ⟨0⟩ then a else b) = umin a b := by
    intro a b; unfold umin
    by_cases h : a.toNat ≤ b.toNat
    · rw [if_pos (ugt_zero h), if_pos h]
    · rw [if_neg (by rw [ugt_one (by omega)]; decide), if_neg h]
  have hwad : wadU = ⟨1000000000000000000⟩ := by native_decide
  have hsl : (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨255⟩).toNat =
      57896044618658097711785492504343953926634992332820282019728792003956564819968 := by
    native_decide
  have hbr : ∀ (o : ByteArray) (k : ℕ), k + 32 ≤ o.size →
      ABI.bytesToWord ((o.toList.drop k).take 32) =
        UInt256.ofNat (fromByteArrayBigEndian (o.extract k (k + 32))) := by
    intro o k h
    rw [decode_word_at_eq_any o k h, uInt256OfByteArray_eq]
    congr 1; unfold fromByteArrayBigEndian; congr 1
    rw [byteArray_toList_eq (o.readBytes k 32),
      readBytes_at_toList_any o k h,
      byteArray_toList_eq (o.extract k (k + 32)),
      ByteArray.data_extract, Array.toList_extract,
      List.extract_eq_take_drop]
    simp
  obtain ⟨σs, As, σus, Aus, hIlksSolm, hUrnsSolm, hAmEq, hvatCodeIlkS⟩ :=
    catBiteMapUrns hAccounts hdepthNe hUrnsVatCode hIlksCall hUrnsCall
  have slotEqUS : ∀ s : UInt256, solcSlotWord σus I s = solcSlotWord σu I s := by
    intro s; simp only [solcSlotWord]
    rw [accountMapEquiv_storage_findD hAmEq I.codeOwner s ⟨0⟩]
  set eUrnE := { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
    accountMap := σu, substate := Au, createdAccounts := cAu } with heUrnEdef
  set eUrnS := { initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I with
    accountMap := σus, substate := Aus, createdAccounts := cAu } with heUrnSdef
  have hEqU : EVMStateEquiv eUrnE eUrnS := ⟨rfl, rfl, hAmEq⟩
  have heUEam : eUrnE.accountMap = σu := rfl
  have heUEee : eUrnE.executionEnv = I := rfl
  have heUSam : eUrnS.accountMap = σus := rfl
  have heUSee : eUrnS.executionEnv = I := rfl
  have hboxB : biteBoxW eUrnE = solcSlotWord σu I ⟨5⟩ := by
    simp only [biteBoxW, catSlotWord, heUEam, heUEee]
  have hlitB : biteLitW eUrnE = solcSlotWord σu I ⟨6⟩ := by
    simp only [biteLitW, catSlotWord, heUEam, heUEee]
  have hchopB : biteChopW I eUrnE = milkChop := by
    rw [hmilkChopDef]
    simp only [biteChopW, catSlotWord, heUEam, heUEee, biteChopSlot,
      biteFlipSlot_eq hsz36]
  have hdunkB : biteDunkW I eUrnE = milkDunk := by
    rw [hmilkDunkDef]
    simp only [biteDunkW, catSlotWord, heUEam, heUEee, biteDunkSlot,
      biteFlipSlot_eq hsz36]
  have hroomB : biteRoomV eUrnE = room := by
    rw [hroomDef]
    simp only [biteRoomV, biteBoxW, biteLitW, catSlotWord, heUEam, heUEee]
  have hdunkroomB : biteDunkRoomV I eUrnE = dunkRoom := by
    rw [hdunkRoomDef, uminEq milkDunk room]
    simp only [biteDunkRoomV, hdunkB, hroomB]
  have hdartvB : biteDartV I eUrnE iRate art = dart := by
    have hcand : biteDartCandV I eUrnE iRate = dartCandidate := by
      simp only [biteDartCandV, biteDartDenomV, biteDunkRoomWadV,
        hchopB, hdunkroomB, hwad, hdartCandDef, hdartDenomDef,
        hdunkRoomWadDef]
      rfl
    rw [hdartDef, uminEq art dartCandidate]
    simp only [biteDartV, hcand]
  have hdinkvB : biteDinkV I eUrnE iRate art ink = dink := by
    have hcand : biteDinkCandV I eUrnE iRate art ink = dinkCandidate := by
      simp only [biteDinkCandV, biteInkDartV, hdartvB, hdinkCandDef,
        hinkDartDef]
      rfl
    rw [hdinkDef, uminEq ink dinkCandidate]
    simp only [biteDinkV, hcand]
  have hIlksDec : config.externalABI.decode? "ilks" o' =
      some [bw (UInt256.ofNat (fromByteArrayBigEndian (o'.extract 0 32))),
        bw iRate, bw iSpot,
        bw (UInt256.ofNat (fromByteArrayBigEndian (o'.extract 96 128))),
        bw iDust] := by
    have h := catBiteIlksDecode_ok hilkslen
    rw [hbr o' 0 (by omega), hbr o' 32 (by omega), hbr o' 64 (by omega),
      hbr o' 96 (by omega), hbr o' 128 (by omega)] at h
    rw [hiRate, hiSpot, hiDustDef]; exact h
  have hUrnsDec : config.externalABI.decode? "urns" ou =
      some [bw ink, bw art] := by
    have h := catBiteUrnsDecode_ok hurnslen
    rw [hbr ou 0 (by omega), hbr ou 32 (by omega)] at h
    rw [hink, hart]; exact h
  -- map the (successful) grab CALL, keeping the coupling.
  obtain ⟨AG, hGrabCall'⟩ :=
    biteTypedCallZeroSetSubstate hGrabCall
      (by simpa [initState] using hdepthNe) Au
  obtain ⟨σgs, Ags, hGrabSolm, hEqGrab⟩ :=
    catBiteMapCall hEqU hGrabCall' hdepthNe
  set eGrabE := { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
    accountMap := σg, substate := AG, createdAccounts := cAg } with heGrabEdef
  set eGrabS := { initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I with
    accountMap := σgs, substate := Ags, createdAccounts := cAg } with heGrabSdef
  have heGEam : eGrabE.accountMap = σg := rfl
  have heGEee : eGrabE.executionEnv = I := rfl
  have htgtU : EVM.address (biteVatAddr eUrnS).val =
      AccountAddress.ofUInt256 ((solcSlotWord σu I ⟨3⟩).land biteAddrMaskWord) := by
    rw [← biteVatAddr_eq_of_equiv hEqU, addrId,
      accountAddress_ofUInt256_eq_ofNat_toNat, hmask]
    simp only [biteVatAddr, catSlotWord, heUEam, heUEee]
  have h1 : biteIlkVal I =
      Value.fixedBytes bytes32Width (EVM.Word.toBytesBE (biteIlkWord I)) := by
    simp only [biteIlkVal, hbytes]
  have h2 : biteUrnVal I = Value.address (AccountAddress.ofNat
      (biteAddrMaskWord.land
        (biteAddrMaskWord.land (calldataWord I.calldata 36))).toNat) := by
    rw [hurn]
    simp only [biteUrnVal, biteUrnWord, biteUrnAddr, hAddrRT]
  have h3 : (eUrnS.executionEnv.codeOwner : AccountAddress) =
      AccountAddress.ofNat (UInt256.ofNat I.codeOwner.val).toNat := by
    rw [heUSee]; exact (hAddrRT I.codeOwner).symm
  have h4 : biteVowAddrV eUrnS = AccountAddress.ofNat
      (biteAddrMaskWord.land (solcSlotWord σu I ⟨4⟩)).toNat := by
    rw [← biteVowAddrV_eq_of_equiv hEqU]
    simp only [biteVowAddrV, catSlotWord, heUEam, heUEee, hmask]
    rw [u256_land_comm]
  have hdartvBS : biteDartV I eUrnS iRate art = dart := by
    rw [← biteDartV_eq_of_equiv hEqU]; exact hdartvB
  have hdinkvBS : biteDinkV I eUrnS iRate art ink = dink := by
    rw [← biteDinkV_eq_of_equiv hEqU]; exact hdinkvB
  have hdartrateBS : biteDartRateV I eUrnS iRate art = dart.mul iRate := by
    rw [← biteDartRateV_eq_of_equiv hEqU]
    simp only [biteDartRateV, hdartvB]; rfl
  have hGrabCodeS :
      ¬ Reasoning.Theory.extCodeSizeWord σus
        ((solcSlotWord σus I ⟨3⟩).land biteAddrMaskWord) = ⟨0⟩ := by
    rw [slotEqUS ⟨3⟩, ← extCodeSizeWord_accountMapEquiv hAmEq]
    exact hGrabCode
  rw [hperm, ← htgtU, ← h1, ← h2, ← h3, ← h4, ← hdinkvBS, ← hdartvBS]
    at hGrabSolm
  have hGrabDec : config.externalABI.decode? "grab" og = some [] := by
    simp [config, externalABI, decodeVoid?]
  have hlive' : catSlotWord ⟨2⟩ eUrnS.accountMap eUrnS.executionEnv = ⟨1⟩ := by
    rw [← biteSlotEqOfEquiv hEqU ⟨2⟩]; exact hlive
  have codeZero : ∀ (e : EVM.State) (w : UInt256),
      extCodeSizeWord e.accountMap w = ⟨0⟩ →
      (UInt256.ofNat ((e.lookupAccount
        (AccountAddress.ofUInt256 w)).option 0
        (fun acc => acc.code.size))).toNat = 0 := by
    intro e w hw
    unfold extCodeSizeWord at hw
    simp only [State.lookupAccount]
    cases hf : e.accountMap.find? (AccountAddress.ofUInt256 w) with
    | none => native_decide
    | some acc =>
        rw [hf] at hw
        simpa [Option.option] using congrArg UInt256.toNat hw
  have hbody :
      ExecTransitionBody config contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) (biteLocals I)
        biteTransition.body .reverted := by
    refine catBiteSourceFessNoCodeRevert hwv
      (catBiteVatCodePos_of_uniswap hAccounts hvatCode) hIlksSolm hIlksDec
      hvatCodeIlkS hUrnsSolm hUrnsDec hlive' hsz36 hfitInkSpot hfitArtRate
      hspotPos (hposNe iRate hRatePos) hunsafe ?_ ?_ ?_ ?_ ?_
      (hposNe art hArtPos) ?_ ?_ ?_ ?_ ?_ ?_ hGrabSolm hGrabDec ?_
    · rw [← biteLitW_eq_of_equiv hEqU, ← biteBoxW_eq_of_equiv hEqU, hlitB, hboxB]
      exact hlitterbox
    · rw [← biteRoomV_eq_of_equiv hEqU, hroomB]; exact hroomdust
    · rw [← biteDunkRoomV_eq_of_equiv hEqU, hdunkroomB, hwad, Nat.mul_comm]
      exact hFitWad
    · rw [← biteChopW_eq_of_equiv hEqU, hchopB]; exact hposNe milkChop hChopPos
    · rw [← biteDartV_eq_of_equiv hEqU, hdartvB, Nat.mul_comm]; exact hFitInkDart
    · rw [← biteDartV_eq_of_equiv hEqU, hdartvB]; exact hDartPos
    · rw [← biteDinkV_eq_of_equiv hEqU, hdinkvB]; exact hDinkPos
    · rw [← biteDartV_eq_of_equiv hEqU, hdartvB]; simp only [int256Limit]
      exact Int.ofNat_le.mpr (hDartLim.trans_eq hsl)
    · rw [← biteDinkV_eq_of_equiv hEqU, hdinkvB]; simp only [int256Limit]
      exact Int.ofNat_le.mpr (hDinkLim.trans_eq hsl)
    · have haddr : biteVatAddr eUrnS =
          AccountAddress.ofUInt256 (catBiteVatTargetWord σus I) := by
        rw [accountAddress_ofUInt256_eq_ofNat_toNat]
        simp only [biteVatAddr, catBiteVatTargetWord, catAddressReturnWord,
          catSlotWord, heUSam, heUSee]
      rw [haddr]
      refine codePos eUrnS (catBiteVatTargetWord σus I) ?_
      rw [heUSam, show catBiteVatTargetWord σus I =
            (solcSlotWord σus I ⟨3⟩).land biteAddrMaskWord from by
          simp only [catBiteVatTargetWord, catAddressReturnWord, catSlotWord,
            hmask]]
      exact hGrabCodeS
    · rw [← biteDartV_eq_of_equiv hEqU, hdartvB, Nat.mul_comm]; exact hRateFit
    · rw [← biteVowAddrV_eq_of_equiv hEqGrab,
        ← biteCodeW_eq_of_equiv (biteVowAddrV eGrabE) hEqGrab]
      have haddr : biteVowAddrV eGrabE =
          AccountAddress.ofUInt256 ((solcSlotWord σg I ⟨4⟩).land solcAddrMask) := by
        rw [accountAddress_ofUInt256_eq_ofNat_toNat]
        simp only [biteVowAddrV, catSlotWord, heGEam, heGEee]
      rw [haddr]
      refine codeZero eGrabE ((solcSlotWord σg I ⟨4⟩).land solcAddrMask) ?_
      rw [heGEam, u256_land_comm, ← hmask]; exact hFessCode
  have hrev : RDrev catBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) :=
    RD.solcExtcodesizeGuardMissing (pc := ⟨2284⟩) (okPc := ⟨2296⟩) rd2284 hFessCode
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) hov2
  simpa using hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody



set_option maxHeartbeats 4000000 in
/-- **kick no-code branch (extracted).** grab+fess succeed, litter is stored, but the
`EXTCODESIZE(flip)` guard before the `flip.kick(...)` CALL is false (empty code), so the EVM reverts
at pc `2516` before any call. Maps the 4-call chain + the litter SSTORE, fires the generic
`RD.solcExtcodesizeGuardMissing` at the post-SSTORE account map + `catBiteSourceKickNoCodeRevert`.
Dual of `catBiteRevertKickFail`. -/
theorem catBiteRevertKickNoCode {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {σ' σu σg σf : AccountMap} {A' Au Ag Af : Substate}
    {cA' cAu cAg cAf : Batteries.RBSet AccountAddress compare} {o' ou og ofb rdata3 : ByteArray}
    {mem3 : ByteArray} {aw3 : UInt256} {R3 : List UInt256} {k3 C3 : ℕ}
    {flipW dartRate tabBase tab litterNew : UInt256}
    {art ink iSpot iRate iDust room milkDunk milkChop dunkRoom dunkRoomWad
      dartDenomRate dartCandidate dart inkDart dinkCandidate dink : UInt256}
    (hcode : I.code = catBytecode)
    (hdispatch : dispatchMsg contract I.calldata = some biteTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (biteTransition.params.map Param.name)
        (transitionSignature biteTransition).paramTypes I.calldata = some (biteLocals I))
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hwv : I.weiValue = ⟨0⟩) (hperm : I.perm = true) (hsz36 : 36 ≤ I.calldata.size)
    (hdepth : (I.depth : ℕ) < 1024)
    (hurn : biteAddrMaskWord.land (biteAddrMaskWord.land (calldataWord I.calldata 36)) = biteUrnWord I)
    (hilkslen : 160 ≤ o'.size) (hurnslen : 64 ≤ ou.size)
    (hlive : catSlotWord ⟨2⟩ σu I = ⟨1⟩)
    (hvatCode : ¬ Reasoning.Theory.extCodeSizeWord σ_evm (catBiteVatTargetWord σ_evm I) = ⟨0⟩)
    (hUrnsVatCode :
      ¬ Reasoning.Theory.extCodeSizeWord σ' ((catSlotWord ⟨3⟩ σ' I).land biteAddrMaskWord) = ⟨0⟩)
    (hGrabCode :
      ¬ Reasoning.Theory.extCodeSizeWord σu ((solcSlotWord σu I ⟨3⟩).land biteAddrMaskWord) = ⟨0⟩)
    (hFessCode :
      ¬ Reasoning.Theory.extCodeSizeWord σg (biteAddrMaskWord.land (solcSlotWord σg I ⟨4⟩)) = ⟨0⟩)
    (hKickCode :
      Reasoning.Theory.extCodeSizeWord (sstoreAccountMap I.codeOwner σf ⟨6⟩ litterNew)
        (biteAddrMaskWord.land flipW) = ⟨0⟩)
    (hIlksCall :
      typedCallViaEVM config (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        (AccountAddress.ofUInt256 (catBiteVatTargetWord σ_evm I)) "ilks" 0 [biteIlkVal I]
        (true, { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
                  accountMap := σ', substate := A', createdAccounts := cA' }, o') false)
    (hUrnsCall :
      typedCallViaEVM config
        { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
            accountMap := σ', createdAccounts := cA' }
        (AccountAddress.ofUInt256 ((catSlotWord ⟨3⟩ σ' I).land biteAddrMaskWord)) "urns" 0
        [biteIlkVal I, biteUrnVal I]
        (true, { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
                  accountMap := σu, substate := Au, createdAccounts := cAu }, ou) false)
    (hGrabCall :
      typedCallViaEVM config
        { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
            accountMap := σu, createdAccounts := cAu }
        (AccountAddress.ofUInt256 ((solcSlotWord σu I ⟨3⟩).land biteAddrMaskWord)) "grab" 0
        [Value.fixedBytes bytes32Width (EVM.Word.toBytesBE (biteIlkWord I)),
          Value.address (AccountAddress.ofNat
            (biteAddrMaskWord.land (biteAddrMaskWord.land (calldataWord I.calldata 36))).toNat),
          Value.address (AccountAddress.ofNat (UInt256.ofNat I.codeOwner.val).toNat),
          Value.address (AccountAddress.ofNat (biteAddrMaskWord.land (solcSlotWord σu I ⟨4⟩)).toNat),
          Value.int (-Int.ofNat dink.toNat), Value.int (-Int.ofNat dart.toNat)]
        (true, { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
                  accountMap := σg, substate := Ag, createdAccounts := cAg }, og) I.perm)
    (hFessCall :
      typedCallViaEVM config
        { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
            accountMap := σg, createdAccounts := cAg }
        (AccountAddress.ofUInt256 (biteAddrMaskWord.land (solcSlotWord σg I ⟨4⟩))) "fess" 0
        [Value.int (Int.ofNat (dart.mul iRate).toNat)]
        (true, { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
                accountMap := σf, substate := Af, createdAccounts := cAf }, ofb) I.perm)
    (rd2516 :
      RD catBytecode I (Sat256.ofUInt256 g) (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        ⟨2516⟩ (biteAddrMaskWord.land flipW :: biteAddrMaskWord.land flipW :: R3) mem3 aw3 rdata3
        (cAf, sstoreAccountMap I.codeOwner σf ⟨6⟩ litterNew) k3 C3)
    (hov3 : R3.length + 4 ≤ 1024)
    (hRateFit : iRate.toNat * dart.toNat < UInt256.size)
    (hflipWDef : flipW = biteAddrMaskWord.land (solcSlotWord σu I (solcMappingSlot ⟨1⟩ (biteIlkWord I))))
    (hdartRateDef : dartRate = dart.mul iRate)
    (htabBaseDef : tabBase = dartRate.mul milkChop)
    (htabDef : tab = tabBase.div ⟨1000000000000000000⟩)
    (hlitterNewDef : litterNew = solcSlotWord σf I ⟨6⟩ + tab)
    (hChopFit : milkChop.toNat * dartRate.toNat < UInt256.size)
    (hLitFit : (solcSlotWord σf I ⟨6⟩).toNat + tab.toNat < UInt256.size)
    (hart : art = UInt256.ofNat (fromByteArrayBigEndian (ou.extract 32 64)))
    (hink : ink = UInt256.ofNat (fromByteArrayBigEndian (ou.extract 0 32)))
    (hiSpot : iSpot = UInt256.ofNat (fromByteArrayBigEndian (o'.extract 64 96)))
    (hiRate : iRate = UInt256.ofNat (fromByteArrayBigEndian (o'.extract 32 64)))
    (hiDustDef : iDust = UInt256.ofNat (fromByteArrayBigEndian (o'.extract 128 160)))
    (hroomDef : room = (solcSlotWord σu I ⟨5⟩).sub (solcSlotWord σu I ⟨6⟩))
    (hmilkDunkDef : milkDunk = solcSlotWord σu I (solcMappingSlot ⟨1⟩ (biteIlkWord I) + ⟨2⟩))
    (hmilkChopDef : milkChop = solcSlotWord σu I (solcMappingSlot ⟨1⟩ (biteIlkWord I) + ⟨1⟩))
    (hdunkRoomDef : dunkRoom = if milkDunk.gt room = ⟨0⟩ then milkDunk else room)
    (hdunkRoomWadDef : dunkRoomWad = dunkRoom.mul ⟨1000000000000000000⟩)
    (hdartDenomDef : dartDenomRate = dunkRoomWad.div iRate)
    (hdartCandDef : dartCandidate = dartDenomRate.div milkChop)
    (hdartDef : dart = if art.gt dartCandidate = ⟨0⟩ then art else dartCandidate)
    (hinkDartDef : inkDart = ink.mul dart)
    (hdinkCandDef : dinkCandidate = inkDart.div art)
    (hdinkDef : dink = if ink.gt dinkCandidate = ⟨0⟩ then ink else dinkCandidate)
    (hspotPos : 0 < iSpot.toNat) (hfitArtRate : art.toNat * iRate.toNat < UInt256.size)
    (hfitInkSpot : ink.toNat * iSpot.toNat < UInt256.size)
    (hunsafe : (ink * iSpot).toNat < (art * iRate).toNat)
    (hlitterbox : (solcSlotWord σu I ⟨6⟩).toNat < (solcSlotWord σu I ⟨5⟩).toNat)
    (hroomdust : iDust.toNat ≤ room.toNat)
    (hRatePos : iRate ≠ ⟨0⟩) (hChopPos : milkChop ≠ ⟨0⟩)
    (hFitWad : (⟨1000000000000000000⟩ : UInt256).toNat * dunkRoom.toNat < UInt256.size)
    (hArtPos : art ≠ ⟨0⟩) (hFitInkDart : dart.toNat * ink.toNat < UInt256.size)
    (hDartPos : 0 < dart.toNat) (hDinkPos : 0 < dink.toNat)
    (hDartLim : dart.toNat ≤ (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨255⟩).toNat)
    (hDinkLim : dink.toNat ≤ (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨255⟩).toNat) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hdepthNe : I.depth ≠ 1024 := by omega
  have hmask : biteAddrMaskWord = solcAddrMask := by native_decide
  have hposNe : ∀ w : UInt256, w ≠ ⟨0⟩ → 0 < w.toNat :=
    fun w hw => Nat.pos_of_ne_zero (fun h => hw (uint256_toNat_eq_zero h))
  have codePos : ∀ (e : EVM.State) (w : UInt256),
      extCodeSizeWord e.accountMap w ≠ ⟨0⟩ →
      0 < (UInt256.ofNat ((e.lookupAccount
        (AccountAddress.ofUInt256 w)).option 0
        (fun acc => acc.code.size))).toNat := by
    intro e w hw
    unfold extCodeSizeWord at hw
    simp only [State.lookupAccount]
    cases hf : e.accountMap.find? (AccountAddress.ofUInt256 w) with
    | none => rw [hf] at hw; simp [Option.option] at hw
    | some acc =>
        rw [hf] at hw
        simp only [Option.option, Function.comp] at hw ⊢
        exact hposNe _ hw
  have addrId : ∀ a : AccountAddress, EVM.address a.val = a := by
    intro a; apply Fin.ext
    show a.val % EVM.addressModulus = a.val
    rw [show EVM.addressModulus = AccountAddress.size from by decide]
    exact Nat.mod_eq_of_lt a.isLt
  have hAddrRT : ∀ a : AccountAddress,
      AccountAddress.ofNat (UInt256.ofNat a.val).toNat = a := by
    intro a
    have h1 : (UInt256.ofNat a.val).toNat = a.val :=
      UInt256.toNat_ofNat_of_lt (lt_of_lt_of_le a.isLt
        (show AccountAddress.size ≤ UInt256.size from by decide))
    rw [h1]; apply Fin.ext
    simp only [AccountAddress.ofNat, Fin.ofNat]
    exact Nat.mod_eq_of_lt a.isLt
  have hbytes : biteIlkBytes I = EVM.Word.toBytesBE (biteIlkWord I) := by
    have hlen32 : (biteIlkBytes I).length = 32 := by
      simp only [biteIlkBytes, List.length_take, List.length_drop]
      have htlen : I.calldata.toList.length = I.calldata.size := by
        rw [byteArray_toList_eq, Array.length_toList]; rfl
      rw [htlen]; omega
    have hword : ABI.bytesToWord (biteIlkBytes I) = biteIlkWord I := by
      simpa [biteIlkBytes, biteIlkWord] using
        (decode_word_at_eq_any I.calldata 4 (by simpa using hsz36))
    have hto := toBytesBE_bytesToWord_of_length (bs := biteIlkBytes I) hlen32
    rw [hword] at hto; exact hto.symm
  have uminEq : ∀ a b : UInt256,
      (if UInt256.gt a b = ⟨0⟩ then a else b) = umin a b := by
    intro a b; unfold umin
    by_cases h : a.toNat ≤ b.toNat
    · rw [if_pos (ugt_zero h), if_pos h]
    · rw [if_neg (by rw [ugt_one (by omega)]; decide), if_neg h]
  have hwad : wadU = ⟨1000000000000000000⟩ := by native_decide
  have hsl : (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨255⟩).toNat =
      57896044618658097711785492504343953926634992332820282019728792003956564819968 := by
    native_decide
  have storeFlat : ∀ (ev : EVM.State) (aa : AccountAddress) (k v : UInt256),
      Solm.EVM.storageStore ev aa k v =
        { ev with accountMap := sstoreAccountMap aa ev.accountMap k v } := by
    intro ev aa k v
    simp only [Solm.EVM.storageStore, sstoreAccountMap, State.lookupAccount]
    cases h : ev.accountMap.find? aa with
    | none => simp [Option.option]
    | some acc => simp [Option.option, State.setAccount, Account.updateStorage]
  have hbr : ∀ (o : ByteArray) (k : ℕ), k + 32 ≤ o.size →
      ABI.bytesToWord ((o.toList.drop k).take 32) =
        UInt256.ofNat (fromByteArrayBigEndian (o.extract k (k + 32))) := by
    intro o k h
    rw [decode_word_at_eq_any o k h, uInt256OfByteArray_eq]
    congr 1; unfold fromByteArrayBigEndian; congr 1
    rw [byteArray_toList_eq (o.readBytes k 32),
      readBytes_at_toList_any o k h,
      byteArray_toList_eq (o.extract k (k + 32)),
      ByteArray.data_extract, Array.toList_extract,
      List.extract_eq_take_drop]
    simp
  obtain ⟨σs, As, σus, Aus, hIlksSolm, hUrnsSolm, hAmEq, hvatCodeIlkS⟩ :=
    catBiteMapUrns hAccounts hdepthNe hUrnsVatCode hIlksCall hUrnsCall
  have slotEqUS : ∀ s : UInt256, solcSlotWord σus I s = solcSlotWord σu I s := by
    intro s; simp only [solcSlotWord]
    rw [accountMapEquiv_storage_findD hAmEq I.codeOwner s ⟨0⟩]
  set eUrnE := { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
    accountMap := σu, substate := Au, createdAccounts := cAu } with heUrnEdef
  set eUrnS := { initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I with
    accountMap := σus, substate := Aus, createdAccounts := cAu } with heUrnSdef
  have hEqU : EVMStateEquiv eUrnE eUrnS := ⟨rfl, rfl, hAmEq⟩
  have heUEam : eUrnE.accountMap = σu := rfl
  have heUEee : eUrnE.executionEnv = I := rfl
  have heUSam : eUrnS.accountMap = σus := rfl
  have heUSee : eUrnS.executionEnv = I := rfl
  have hboxB : biteBoxW eUrnE = solcSlotWord σu I ⟨5⟩ := by
    simp only [biteBoxW, catSlotWord, heUEam, heUEee]
  have hlitB : biteLitW eUrnE = solcSlotWord σu I ⟨6⟩ := by
    simp only [biteLitW, catSlotWord, heUEam, heUEee]
  have hchopB : biteChopW I eUrnE = milkChop := by
    rw [hmilkChopDef]
    simp only [biteChopW, catSlotWord, heUEam, heUEee, biteChopSlot,
      biteFlipSlot_eq hsz36]
  have hdunkB : biteDunkW I eUrnE = milkDunk := by
    rw [hmilkDunkDef]
    simp only [biteDunkW, catSlotWord, heUEam, heUEee, biteDunkSlot,
      biteFlipSlot_eq hsz36]
  have hroomB : biteRoomV eUrnE = room := by
    rw [hroomDef]
    simp only [biteRoomV, biteBoxW, biteLitW, catSlotWord, heUEam, heUEee]
  have hdunkroomB : biteDunkRoomV I eUrnE = dunkRoom := by
    rw [hdunkRoomDef, uminEq milkDunk room]
    simp only [biteDunkRoomV, hdunkB, hroomB]
  have hdartvB : biteDartV I eUrnE iRate art = dart := by
    have hcand : biteDartCandV I eUrnE iRate = dartCandidate := by
      simp only [biteDartCandV, biteDartDenomV, biteDunkRoomWadV,
        hchopB, hdunkroomB, hwad, hdartCandDef, hdartDenomDef,
        hdunkRoomWadDef]
      rfl
    rw [hdartDef, uminEq art dartCandidate]
    simp only [biteDartV, hcand]
  have hdinkvB : biteDinkV I eUrnE iRate art ink = dink := by
    have hcand : biteDinkCandV I eUrnE iRate art ink = dinkCandidate := by
      simp only [biteDinkCandV, biteInkDartV, hdartvB, hdinkCandDef,
        hinkDartDef]
      rfl
    rw [hdinkDef, uminEq ink dinkCandidate]
    simp only [biteDinkV, hcand]
  have hdartrateBE : biteDartRateV I eUrnE iRate art = dartRate := by
    rw [hdartRateDef]; simp only [biteDartRateV, hdartvB]; rfl
  have htabB : biteTabV I eUrnE iRate art = tab := by
    rw [htabDef, htabBaseDef]
    simp only [biteTabV, biteTabBaseV, hdartrateBE, hchopB, hwad]; rfl
  have hIlksDec : config.externalABI.decode? "ilks" o' =
      some [bw (UInt256.ofNat (fromByteArrayBigEndian (o'.extract 0 32))),
        bw iRate, bw iSpot,
        bw (UInt256.ofNat (fromByteArrayBigEndian (o'.extract 96 128))),
        bw iDust] := by
    have h := catBiteIlksDecode_ok hilkslen
    rw [hbr o' 0 (by omega), hbr o' 32 (by omega), hbr o' 64 (by omega),
      hbr o' 96 (by omega), hbr o' 128 (by omega)] at h
    rw [hiRate, hiSpot, hiDustDef]; exact h
  have hUrnsDec : config.externalABI.decode? "urns" ou =
      some [bw ink, bw art] := by
    have h := catBiteUrnsDecode_ok hurnslen
    rw [hbr ou 0 (by omega), hbr ou 32 (by omega)] at h
    rw [hink, hart]; exact h
  obtain ⟨AG, hGrabCall'⟩ :=
    biteTypedCallZeroSetSubstate hGrabCall
      (by simpa [initState] using hdepthNe) Au
  obtain ⟨σgs, Ags, hGrabSolm, hEqGrab⟩ :=
    catBiteMapCall hEqU hGrabCall' hdepthNe
  set eGrabE := { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
    accountMap := σg, substate := AG, createdAccounts := cAg } with heGrabEdef
  set eGrabS := { initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I with
    accountMap := σgs, substate := Ags, createdAccounts := cAg } with heGrabSdef
  have heGEam : eGrabE.accountMap = σg := rfl
  have heGEee : eGrabE.executionEnv = I := rfl
  have htgtU : EVM.address (biteVatAddr eUrnS).val =
      AccountAddress.ofUInt256 ((solcSlotWord σu I ⟨3⟩).land biteAddrMaskWord) := by
    rw [← biteVatAddr_eq_of_equiv hEqU, addrId,
      accountAddress_ofUInt256_eq_ofNat_toNat, hmask]
    simp only [biteVatAddr, catSlotWord, heUEam, heUEee]
  have h1 : biteIlkVal I =
      Value.fixedBytes bytes32Width (EVM.Word.toBytesBE (biteIlkWord I)) := by
    simp only [biteIlkVal, hbytes]
  have h2 : biteUrnVal I = Value.address (AccountAddress.ofNat
      (biteAddrMaskWord.land
        (biteAddrMaskWord.land (calldataWord I.calldata 36))).toNat) := by
    rw [hurn]
    simp only [biteUrnVal, biteUrnWord, biteUrnAddr, hAddrRT]
  have h3 : (eUrnS.executionEnv.codeOwner : AccountAddress) =
      AccountAddress.ofNat (UInt256.ofNat I.codeOwner.val).toNat := by
    rw [heUSee]; exact (hAddrRT I.codeOwner).symm
  have h4 : biteVowAddrV eUrnS = AccountAddress.ofNat
      (biteAddrMaskWord.land (solcSlotWord σu I ⟨4⟩)).toNat := by
    rw [← biteVowAddrV_eq_of_equiv hEqU]
    simp only [biteVowAddrV, catSlotWord, heUEam, heUEee, hmask]
    rw [u256_land_comm]
  have hdartvBS : biteDartV I eUrnS iRate art = dart := by
    rw [← biteDartV_eq_of_equiv hEqU]; exact hdartvB
  have hdinkvBS : biteDinkV I eUrnS iRate art ink = dink := by
    rw [← biteDinkV_eq_of_equiv hEqU]; exact hdinkvB
  have hdartrateBS : biteDartRateV I eUrnS iRate art = dart.mul iRate := by
    rw [← biteDartRateV_eq_of_equiv hEqU]
    simp only [biteDartRateV, hdartvB]; rfl
  have htabBS : biteTabV I eUrnS iRate art = tab := by
    rw [← biteTabV_eq_of_equiv hEqU]; exact htabB
  have hGrabCodeS :
      ¬ Reasoning.Theory.extCodeSizeWord σus
        ((solcSlotWord σus I ⟨3⟩).land biteAddrMaskWord) = ⟨0⟩ := by
    rw [slotEqUS ⟨3⟩, ← extCodeSizeWord_accountMapEquiv hAmEq]
    exact hGrabCode
  rw [hperm, ← htgtU, ← h1, ← h2, ← h3, ← h4, ← hdinkvBS, ← hdartvBS]
    at hGrabSolm
  have hGrabDec : config.externalABI.decode? "grab" og = some [] := by
    simp [config, externalABI, decodeVoid?]
  obtain ⟨AF, hFessCall'⟩ :=
    biteTypedCallZeroSetSubstate hFessCall
      (by simpa [initState] using hdepthNe) AG
  obtain ⟨σfs, Afs, hFessSolm, hEqFess⟩ :=
    catBiteMapCall hEqGrab hFessCall' hdepthNe
  set eFessE := { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
    accountMap := σf, substate := AF, createdAccounts := cAf } with heFessEdef
  set eFessS := { initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I with
    accountMap := σfs, substate := Afs, createdAccounts := cAf } with heFessSdef
  have heFEam : eFessE.accountMap = σf := rfl
  have heFEee : eFessE.executionEnv = I := rfl
  have htgtF : EVM.address (biteVowAddrV eGrabS).val =
      AccountAddress.ofUInt256 (biteAddrMaskWord.land (solcSlotWord σg I ⟨4⟩)) := by
    rw [← biteVowAddrV_eq_of_equiv hEqGrab, addrId,
      accountAddress_ofUInt256_eq_ofNat_toNat, hmask, u256_land_comm]
    simp only [biteVowAddrV, catSlotWord, heGEam, heGEee]
  have hfessArg : bw (biteDartRateV I eUrnS iRate art) =
      Value.int (Int.ofNat (dart.mul iRate).toNat) := by rw [hdartrateBS]
  rw [hperm, ← htgtF, ← hfessArg] at hFessSolm
  have hFessDec : config.externalABI.decode? "fess" ofb = some [] := by
    simp [config, externalABI, decodeVoid?]
  have hvowCodeS : 0 < (UInt256.ofNat
      ((eGrabS.lookupAccount (biteVowAddrV eGrabS)).option 0
        (fun acc => acc.code.size))).toNat := by
    rw [← biteVowAddrV_eq_of_equiv hEqGrab,
      ← biteCodeW_eq_of_equiv (biteVowAddrV eGrabE) hEqGrab]
    have haddr : biteVowAddrV eGrabE =
        AccountAddress.ofUInt256 ((solcSlotWord σg I ⟨4⟩).land solcAddrMask) := by
      rw [accountAddress_ofUInt256_eq_ofNat_toNat]
      simp only [biteVowAddrV, catSlotWord, heGEam, heGEee]
    rw [haddr]
    refine codePos eGrabE ((solcSlotWord σg I ⟨4⟩).land solcAddrMask) ?_
    rw [heGEam, u256_land_comm, ← hmask]; exact hFessCode
  have hlitFB : biteLitW eFessE = solcSlotWord σf I ⟨6⟩ := by
    simp only [biteLitW, catSlotWord, heFEam, heFEee]
  have hlitternewE : biteLitterNewV I eUrnE eFessE iRate art = litterNew := by
    rw [hlitterNewDef]
    simp only [biteLitterNewV, hlitFB, htabB]
  set hLitVal := biteLitterNewV I eUrnS eFessS iRate art with hLitValDef
  have hLitValEq : litterNew = hLitVal :=
    hlitternewE.symm.trans (biteLitterNewV_eq_of_equiv hEqU hEqFess iRate art)
  have codeZero : ∀ (e : EVM.State) (w : UInt256),
      extCodeSizeWord e.accountMap w = ⟨0⟩ →
      (UInt256.ofNat ((e.lookupAccount
        (AccountAddress.ofUInt256 w)).option 0
        (fun acc => acc.code.size))).toNat = 0 := by
    intro e w hw
    unfold extCodeSizeWord at hw
    simp only [State.lookupAccount]
    cases hf : e.accountMap.find? (AccountAddress.ofUInt256 w) with
    | none => native_decide
    | some acc =>
        rw [hf] at hw
        simpa [Option.option] using congrArg UInt256.toNat hw
  set eLitS := { initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I with
    accountMap := sstoreAccountMap I.codeOwner σfs ⟨6⟩ hLitVal,
    substate := Afs, createdAccounts := cAf } with heLitSdef
  have heLSam : eLitS.accountMap =
    sstoreAccountMap I.codeOwner σfs ⟨6⟩ hLitVal := rfl
  have heLSee : eLitS.executionEnv = I := rfl
  have hflipAddrS : biteFlipAddrV I eUrnS =
      AccountAddress.ofUInt256 (biteAddrMaskWord.land flipW) := by
    rw [← biteFlipAddrV_eq_of_equiv hEqU,
      accountAddress_ofUInt256_eq_ofNat_toNat, hflipWDef, hmask]
    simp only [biteFlipAddrV, catSlotWord, heUEam, heUEee,
      biteFlipSlot_eq hsz36]
    rw [solcAddrMask_clean_left
      (by rw [u256_land_comm]; exact solcAddrMask_result_canonical _),
      u256_land_comm]
  have hflipCode0 : (UInt256.ofNat
      ((eLitS.lookupAccount (biteFlipAddrV I eUrnS)).option 0
        (fun acc => acc.code.size))).toNat = 0 := by
    rw [hflipAddrS]
    refine codeZero eLitS (biteAddrMaskWord.land flipW) ?_
    rw [heLSam, ← extCodeSizeWord_accountMapEquiv
        (accountMapEquiv_sstoreAccountMap I.codeOwner ⟨6⟩ hLitVal
          hEqFess.accountMap), ← hLitValEq]
    exact hKickCode
  have hlive' : catSlotWord ⟨2⟩ eUrnS.accountMap eUrnS.executionEnv = ⟨1⟩ := by
    rw [← biteSlotEqOfEquiv hEqU ⟨2⟩]; exact hlive
  have hLitStoreS :
      storageLocStore eFessS (wordLoc ⟨6⟩)
        (.int (Int.ofNat hLitVal.toNat)) = some eLitS := by
    have h := storageLocStore_uint256 eFessS ⟨6⟩ hLitVal
    rw [storeFlat] at h
    exact h
  have hbody :
      ExecTransitionBody config contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) (biteLocals I)
        biteTransition.body .reverted := by
    refine catBiteSourceKickNoCodeRevert hwv
      (catBiteVatCodePos_of_uniswap hAccounts hvatCode) hIlksSolm hIlksDec
      hvatCodeIlkS hUrnsSolm hUrnsDec hlive' hsz36 hfitInkSpot hfitArtRate
      hspotPos (hposNe iRate hRatePos) hunsafe ?_ ?_ ?_ ?_ ?_
      (hposNe art hArtPos) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hGrabSolm hGrabDec
      hvowCodeS hFessSolm hFessDec hLitStoreS hflipCode0
    · rw [← biteLitW_eq_of_equiv hEqU, ← biteBoxW_eq_of_equiv hEqU, hlitB, hboxB]
      exact hlitterbox
    · rw [← biteRoomV_eq_of_equiv hEqU, hroomB]; exact hroomdust
    · rw [← biteDunkRoomV_eq_of_equiv hEqU, hdunkroomB, hwad, Nat.mul_comm]
      exact hFitWad
    · rw [← biteChopW_eq_of_equiv hEqU, hchopB]; exact hposNe milkChop hChopPos
    · rw [← biteDartV_eq_of_equiv hEqU, hdartvB, Nat.mul_comm]; exact hFitInkDart
    · rw [← biteDartV_eq_of_equiv hEqU, hdartvB]; exact hDartPos
    · rw [← biteDinkV_eq_of_equiv hEqU, hdinkvB]; exact hDinkPos
    · rw [← biteDartV_eq_of_equiv hEqU, hdartvB]; simp only [int256Limit]
      exact Int.ofNat_le.mpr (hDartLim.trans_eq hsl)
    · rw [← biteDinkV_eq_of_equiv hEqU, hdinkvB]; simp only [int256Limit]
      exact Int.ofNat_le.mpr (hDinkLim.trans_eq hsl)
    · have haddr : biteVatAddr eUrnS =
          AccountAddress.ofUInt256 (catBiteVatTargetWord σus I) := by
        rw [accountAddress_ofUInt256_eq_ofNat_toNat]
        simp only [biteVatAddr, catBiteVatTargetWord, catAddressReturnWord,
          catSlotWord, heUSam, heUSee]
      rw [haddr]
      refine codePos eUrnS (catBiteVatTargetWord σus I) ?_
      rw [heUSam, show catBiteVatTargetWord σus I =
            (solcSlotWord σus I ⟨3⟩).land biteAddrMaskWord from by
          simp only [catBiteVatTargetWord, catAddressReturnWord, catSlotWord,
            hmask]]
      exact hGrabCodeS
    · rw [← biteDartV_eq_of_equiv hEqU, hdartvB, Nat.mul_comm]; exact hRateFit
    · rw [← biteDartRateV_eq_of_equiv hEqU, ← biteChopW_eq_of_equiv hEqU,
        hdartrateBE, hchopB, Nat.mul_comm]; exact hChopFit
    · rw [← biteLitW_eq_of_equiv hEqFess, ← biteTabV_eq_of_equiv hEqU,
        hlitFB, htabB]; exact hLitFit
  have hrev : RDrev catBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) :=
    RD.solcExtcodesizeGuardMissing (pc := ⟨2516⟩) (okPc := ⟨2528⟩) rd2516 hKickCode
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) hov3
  simpa using hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody

set_option maxHeartbeats 1000000 in
/-- The shared DSMath checked-add routine `@3802` on the **overflow** path (empty `revert(0,0)`
stub): when `a+b ≥ 2^256` the `(a+b) < a` guard is `1`, the `ISZERO` gives `0`, the `JUMPI` falls
through, and the `PUSH1 0; DUP1; REVERT` stub fires. Cat's `checked-add EMPTY-revert` primitive. -/
theorem RD.catBiteCheckedAddRevert {cA gh bl σ σ₀ A I} {g : Sat256}
    {mem rdata : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {a b ret : UInt256} {R : List UInt256} {k C : ℕ}
    (rd : RD catBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3802⟩
      (b :: a :: ret :: R) mem aw rdata acc k C)
    (hover : UInt256.size ≤ a.toNat + b.toNat)
    (hov : R.length + 9 ≤ 1024) :
    RDrev catBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have ha : a.toNat < UInt256.size := a.val.isLt
  have hb : b.toNat < UInt256.size := b.val.isLt
  have haddNat : (a + b).toNat = a.toNat + b.toNat - UInt256.size := by
    rw [uadd_toNat, Nat.mod_eq_sub_mod hover, Nat.mod_eq_of_lt (by omega)]
  have hlt : UInt256.lt (a + b) a = ⟨1⟩ := by
    apply Reasoning.Theory.ult_one; rw [haddNat]; omega
  have rd3803 := rd.jumpdest (by native_decide) (by evm_ov)
  have rd3804 := rd3803.dup1 (by native_decide) (by evm_ov)
  have rd3805 := rd3804.dup3 (by native_decide) (by evm_ov)
  have rd3806 := rd3805.add (by native_decide) (by evm_ov)
  have rd3807 := rd3806.dup3 (by native_decide) (by evm_ov)
  have rd3808 := rd3807.dup2 (by native_decide) (by evm_ov)
  have rd3809 := rd3808.lt (by native_decide) (by evm_ov)
  rw [hlt] at rd3809
  have rd3810 := rd3809.iszero (by native_decide) (by evm_ov)
  rw [show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at rd3810
  have rd3813 := rd3810.push2 ⟨3756⟩ (by native_decide) (by evm_ov)
  have rd3814 := rd3813.jumpiNT (by native_decide) rfl (by evm_ov)
  exact RD.solcPush1Dup1Revert0 rd3814
    (by native_decide) (by native_decide) (by native_decide) (by evm_ov)

set_option maxHeartbeats 4000000 in
/-- **`litter + tab` checked-add overflow branch (extracted).** grab+fess succeed and `tab` is
computed, but `litter + tab` overflows (`¬ hLitFit`); solc's DSMath `add` reverts (empty) at the
shared `@3802` routine. Maps ilks+urns+grab+fess to σ_solm, reaches the `@3802` add frame from the
fess-success cursor (`catBiteTraceSeg7h` + inline `Seg7i` prefix), fires
`RD.catBiteCheckedAddRevert` + an inline `catBiteSource`-style litter-add revert. -/
theorem catBiteRevertLitterAdd {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {σ' σu σg σf : AccountMap} {A' Au Ag Af : Substate}
    {cA' cAu cAg cAf : Batteries.RBSet AccountAddress compare} {o' ou og ofb : ByteArray}
    {mem2 : ByteArray} {aw2 : UInt256} {k2 C2 : ℕ}
    {status f0 f1 f2 q urn : UInt256}
    {dartRate tabBase tab : UInt256}
    {art ink iSpot iRate iDust room milkDunk milkChop dunkRoom dunkRoomWad
      dartDenomRate dartCandidate dart inkDart dinkCandidate dink : UInt256}
    (hcode : I.code = catBytecode)
    (hdispatch : dispatchMsg contract I.calldata = some biteTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (biteTransition.params.map Param.name)
        (transitionSignature biteTransition).paramTypes I.calldata = some (biteLocals I))
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hwv : I.weiValue = ⟨0⟩) (hperm : I.perm = true) (hsz36 : 36 ≤ I.calldata.size)
    (hdepth : (I.depth : ℕ) < 1024)
    (hurn : biteAddrMaskWord.land (biteAddrMaskWord.land (calldataWord I.calldata 36)) = biteUrnWord I)
    (hilkslen : 160 ≤ o'.size) (hurnslen : 64 ≤ ou.size)
    (hlive : catSlotWord ⟨2⟩ σu I = ⟨1⟩)
    (hvatCode : ¬ Reasoning.Theory.extCodeSizeWord σ_evm (catBiteVatTargetWord σ_evm I) = ⟨0⟩)
    (hUrnsVatCode :
      ¬ Reasoning.Theory.extCodeSizeWord σ' ((catSlotWord ⟨3⟩ σ' I).land biteAddrMaskWord) = ⟨0⟩)
    (hGrabCode :
      ¬ Reasoning.Theory.extCodeSizeWord σu ((solcSlotWord σu I ⟨3⟩).land biteAddrMaskWord) = ⟨0⟩)
    (hFessCode :
      ¬ Reasoning.Theory.extCodeSizeWord σg (biteAddrMaskWord.land (solcSlotWord σg I ⟨4⟩)) = ⟨0⟩)
    (hIlksCall :
      typedCallViaEVM config (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        (AccountAddress.ofUInt256 (catBiteVatTargetWord σ_evm I)) "ilks" 0 [biteIlkVal I]
        (true, { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
                  accountMap := σ', substate := A', createdAccounts := cA' }, o') false)
    (hUrnsCall :
      typedCallViaEVM config
        { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
            accountMap := σ', createdAccounts := cA' }
        (AccountAddress.ofUInt256 ((catSlotWord ⟨3⟩ σ' I).land biteAddrMaskWord)) "urns" 0
        [biteIlkVal I, biteUrnVal I]
        (true, { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
                  accountMap := σu, substate := Au, createdAccounts := cAu }, ou) false)
    (hGrabCall :
      typedCallViaEVM config
        { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
            accountMap := σu, createdAccounts := cAu }
        (AccountAddress.ofUInt256 ((solcSlotWord σu I ⟨3⟩).land biteAddrMaskWord)) "grab" 0
        [Value.fixedBytes bytes32Width (EVM.Word.toBytesBE (biteIlkWord I)),
          Value.address (AccountAddress.ofNat
            (biteAddrMaskWord.land (biteAddrMaskWord.land (calldataWord I.calldata 36))).toNat),
          Value.address (AccountAddress.ofNat (UInt256.ofNat I.codeOwner.val).toNat),
          Value.address (AccountAddress.ofNat (biteAddrMaskWord.land (solcSlotWord σu I ⟨4⟩)).toNat),
          Value.int (-Int.ofNat dink.toNat), Value.int (-Int.ofNat dart.toNat)]
        (true, { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
                  accountMap := σg, substate := Ag, createdAccounts := cAg }, og) I.perm)
    (hFessCall :
      typedCallViaEVM config
        { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
            accountMap := σg, createdAccounts := cAg }
        (AccountAddress.ofUInt256 (biteAddrMaskWord.land (solcSlotWord σg I ⟨4⟩))) "fess" 0
        [Value.int (Int.ofNat (dart.mul iRate).toNat)]
        (true, { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
                accountMap := σf, substate := Af, createdAccounts := cAf }, ofb) I.perm)
    (rd2300 :
      RD catBytecode I (Sat256.ofUInt256 g) (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        ⟨2300⟩ (status :: f0 :: f1 :: f2 :: dink :: dart :: q :: art :: ink :: iDust :: iSpot :: iRate ::
          ⟨0⟩ :: urn :: biteIlkWord I :: ⟨419⟩ :: catSelWord I :: []) mem2 aw2 ofb (cAf, σf) k2 C2)
    (hstatus : status ≠ ⟨0⟩)
    (hChop : (if (⟨32⟩ + q).toNat ≥ mem2.size ∨ (⟨32⟩ + q) ≥ aw2 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat (fromByteArrayBigEndian (mem2.readWithPadding (⟨32⟩ + q).toNat 32))) = milkChop)
    (haw : q.toNat + 64 ≤ aw2.toNat * 32) (hqsz : q.toNat + 64 < UInt256.size)
    (hRateFit : iRate.toNat * dart.toNat < UInt256.size)
    (hChopFit : milkChop.toNat * dartRate.toNat < UInt256.size)
    (hLitNofit : ¬ (solcSlotWord σf I ⟨6⟩).toNat + tab.toNat < UInt256.size)
    (hdartRateDef : dartRate = dart.mul iRate)
    (htabBaseDef : tabBase = dartRate.mul milkChop)
    (htabDef : tab = tabBase.div ⟨1000000000000000000⟩)
    (hart : art = UInt256.ofNat (fromByteArrayBigEndian (ou.extract 32 64)))
    (hink : ink = UInt256.ofNat (fromByteArrayBigEndian (ou.extract 0 32)))
    (hiSpot : iSpot = UInt256.ofNat (fromByteArrayBigEndian (o'.extract 64 96)))
    (hiRate : iRate = UInt256.ofNat (fromByteArrayBigEndian (o'.extract 32 64)))
    (hiDustDef : iDust = UInt256.ofNat (fromByteArrayBigEndian (o'.extract 128 160)))
    (hroomDef : room = (solcSlotWord σu I ⟨5⟩).sub (solcSlotWord σu I ⟨6⟩))
    (hmilkDunkDef : milkDunk = solcSlotWord σu I (solcMappingSlot ⟨1⟩ (biteIlkWord I) + ⟨2⟩))
    (hmilkChopDef : milkChop = solcSlotWord σu I (solcMappingSlot ⟨1⟩ (biteIlkWord I) + ⟨1⟩))
    (hdunkRoomDef : dunkRoom = if milkDunk.gt room = ⟨0⟩ then milkDunk else room)
    (hdunkRoomWadDef : dunkRoomWad = dunkRoom.mul ⟨1000000000000000000⟩)
    (hdartDenomDef : dartDenomRate = dunkRoomWad.div iRate)
    (hdartCandDef : dartCandidate = dartDenomRate.div milkChop)
    (hdartDef : dart = if art.gt dartCandidate = ⟨0⟩ then art else dartCandidate)
    (hinkDartDef : inkDart = ink.mul dart)
    (hdinkCandDef : dinkCandidate = inkDart.div art)
    (hdinkDef : dink = if ink.gt dinkCandidate = ⟨0⟩ then ink else dinkCandidate)
    (hspotPos : 0 < iSpot.toNat) (hfitArtRate : art.toNat * iRate.toNat < UInt256.size)
    (hfitInkSpot : ink.toNat * iSpot.toNat < UInt256.size)
    (hunsafe : (ink * iSpot).toNat < (art * iRate).toNat)
    (hlitterbox : (solcSlotWord σu I ⟨6⟩).toNat < (solcSlotWord σu I ⟨5⟩).toNat)
    (hroomdust : iDust.toNat ≤ room.toNat)
    (hRatePos : iRate ≠ ⟨0⟩) (hChopPos : milkChop ≠ ⟨0⟩)
    (hFitWad : (⟨1000000000000000000⟩ : UInt256).toNat * dunkRoom.toNat < UInt256.size)
    (hArtPos : art ≠ ⟨0⟩) (hFitInkDart : dart.toNat * ink.toNat < UInt256.size)
    (hDartPos : 0 < dart.toNat) (hDinkPos : 0 < dink.toNat)
    (hDartLim : dart.toNat ≤ (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨255⟩).toNat)
    (hDinkLim : dink.toNat ≤ (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨255⟩).toNat) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hdepthNe : I.depth ≠ 1024 := by omega
  have hmask : biteAddrMaskWord = solcAddrMask := by native_decide
  have hposNe : ∀ w : UInt256, w ≠ ⟨0⟩ → 0 < w.toNat :=
    fun w hw => Nat.pos_of_ne_zero (fun h => hw (uint256_toNat_eq_zero h))
  have codePos : ∀ (e : EVM.State) (w : UInt256),
      extCodeSizeWord e.accountMap w ≠ ⟨0⟩ →
      0 < (UInt256.ofNat ((e.lookupAccount
        (AccountAddress.ofUInt256 w)).option 0
        (fun acc => acc.code.size))).toNat := by
    intro e w hw
    unfold extCodeSizeWord at hw
    simp only [State.lookupAccount]
    cases hf : e.accountMap.find? (AccountAddress.ofUInt256 w) with
    | none => rw [hf] at hw; simp [Option.option] at hw
    | some acc =>
        rw [hf] at hw
        simp only [Option.option, Function.comp] at hw ⊢
        exact hposNe _ hw
  have addrId : ∀ a : AccountAddress, EVM.address a.val = a := by
    intro a; apply Fin.ext
    show a.val % EVM.addressModulus = a.val
    rw [show EVM.addressModulus = AccountAddress.size from by decide]
    exact Nat.mod_eq_of_lt a.isLt
  have hAddrRT : ∀ a : AccountAddress,
      AccountAddress.ofNat (UInt256.ofNat a.val).toNat = a := by
    intro a
    have h1 : (UInt256.ofNat a.val).toNat = a.val :=
      UInt256.toNat_ofNat_of_lt (lt_of_lt_of_le a.isLt
        (show AccountAddress.size ≤ UInt256.size from by decide))
    rw [h1]; apply Fin.ext
    simp only [AccountAddress.ofNat, Fin.ofNat]
    exact Nat.mod_eq_of_lt a.isLt
  have hbytes : biteIlkBytes I = EVM.Word.toBytesBE (biteIlkWord I) := by
    have hlen32 : (biteIlkBytes I).length = 32 := by
      simp only [biteIlkBytes, List.length_take, List.length_drop]
      have htlen : I.calldata.toList.length = I.calldata.size := by
        rw [byteArray_toList_eq, Array.length_toList]; rfl
      rw [htlen]; omega
    have hword : ABI.bytesToWord (biteIlkBytes I) = biteIlkWord I := by
      simpa [biteIlkBytes, biteIlkWord] using
        (decode_word_at_eq_any I.calldata 4 (by simpa using hsz36))
    have hto := toBytesBE_bytesToWord_of_length (bs := biteIlkBytes I) hlen32
    rw [hword] at hto; exact hto.symm
  have uminEq : ∀ a b : UInt256,
      (if UInt256.gt a b = ⟨0⟩ then a else b) = umin a b := by
    intro a b; unfold umin
    by_cases h : a.toNat ≤ b.toNat
    · rw [if_pos (ugt_zero h), if_pos h]
    · rw [if_neg (by rw [ugt_one (by omega)]; decide), if_neg h]
  have hwad : wadU = ⟨1000000000000000000⟩ := by native_decide
  have hsl : (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨255⟩).toNat =
      57896044618658097711785492504343953926634992332820282019728792003956564819968 := by
    native_decide
  have storeFlat : ∀ (ev : EVM.State) (aa : AccountAddress) (k v : UInt256),
      Solm.EVM.storageStore ev aa k v =
        { ev with accountMap := sstoreAccountMap aa ev.accountMap k v } := by
    intro ev aa k v
    simp only [Solm.EVM.storageStore, sstoreAccountMap, State.lookupAccount]
    cases h : ev.accountMap.find? aa with
    | none => simp [Option.option]
    | some acc => simp [Option.option, State.setAccount, Account.updateStorage]
  have hbr : ∀ (o : ByteArray) (k : ℕ), k + 32 ≤ o.size →
      ABI.bytesToWord ((o.toList.drop k).take 32) =
        UInt256.ofNat (fromByteArrayBigEndian (o.extract k (k + 32))) := by
    intro o k h
    rw [decode_word_at_eq_any o k h, uInt256OfByteArray_eq]
    congr 1; unfold fromByteArrayBigEndian; congr 1
    rw [byteArray_toList_eq (o.readBytes k 32),
      readBytes_at_toList_any o k h,
      byteArray_toList_eq (o.extract k (k + 32)),
      ByteArray.data_extract, Array.toList_extract,
      List.extract_eq_take_drop]
    simp
  obtain ⟨σs, As, σus, Aus, hIlksSolm, hUrnsSolm, hAmEq, hvatCodeIlkS⟩ :=
    catBiteMapUrns hAccounts hdepthNe hUrnsVatCode hIlksCall hUrnsCall
  have slotEqUS : ∀ s : UInt256, solcSlotWord σus I s = solcSlotWord σu I s := by
    intro s; simp only [solcSlotWord]
    rw [accountMapEquiv_storage_findD hAmEq I.codeOwner s ⟨0⟩]
  set eUrnE := { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
    accountMap := σu, substate := Au, createdAccounts := cAu } with heUrnEdef
  set eUrnS := { initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I with
    accountMap := σus, substate := Aus, createdAccounts := cAu } with heUrnSdef
  have hEqU : EVMStateEquiv eUrnE eUrnS := ⟨rfl, rfl, hAmEq⟩
  have heUEam : eUrnE.accountMap = σu := rfl
  have heUEee : eUrnE.executionEnv = I := rfl
  have heUSam : eUrnS.accountMap = σus := rfl
  have heUSee : eUrnS.executionEnv = I := rfl
  have hboxB : biteBoxW eUrnE = solcSlotWord σu I ⟨5⟩ := by
    simp only [biteBoxW, catSlotWord, heUEam, heUEee]
  have hlitB : biteLitW eUrnE = solcSlotWord σu I ⟨6⟩ := by
    simp only [biteLitW, catSlotWord, heUEam, heUEee]
  have hchopB : biteChopW I eUrnE = milkChop := by
    rw [hmilkChopDef]
    simp only [biteChopW, catSlotWord, heUEam, heUEee, biteChopSlot,
      biteFlipSlot_eq hsz36]
  have hdunkB : biteDunkW I eUrnE = milkDunk := by
    rw [hmilkDunkDef]
    simp only [biteDunkW, catSlotWord, heUEam, heUEee, biteDunkSlot,
      biteFlipSlot_eq hsz36]
  have hroomB : biteRoomV eUrnE = room := by
    rw [hroomDef]
    simp only [biteRoomV, biteBoxW, biteLitW, catSlotWord, heUEam, heUEee]
  have hdunkroomB : biteDunkRoomV I eUrnE = dunkRoom := by
    rw [hdunkRoomDef, uminEq milkDunk room]
    simp only [biteDunkRoomV, hdunkB, hroomB]
  have hdartvB : biteDartV I eUrnE iRate art = dart := by
    have hcand : biteDartCandV I eUrnE iRate = dartCandidate := by
      simp only [biteDartCandV, biteDartDenomV, biteDunkRoomWadV,
        hchopB, hdunkroomB, hwad, hdartCandDef, hdartDenomDef,
        hdunkRoomWadDef]
      rfl
    rw [hdartDef, uminEq art dartCandidate]
    simp only [biteDartV, hcand]
  have hdinkvB : biteDinkV I eUrnE iRate art ink = dink := by
    have hcand : biteDinkCandV I eUrnE iRate art ink = dinkCandidate := by
      simp only [biteDinkCandV, biteInkDartV, hdartvB, hdinkCandDef,
        hinkDartDef]
      rfl
    rw [hdinkDef, uminEq ink dinkCandidate]
    simp only [biteDinkV, hcand]
  have hdartrateBE : biteDartRateV I eUrnE iRate art = dartRate := by
    rw [hdartRateDef]; simp only [biteDartRateV, hdartvB]; rfl
  have htabB : biteTabV I eUrnE iRate art = tab := by
    rw [htabDef, htabBaseDef]
    simp only [biteTabV, biteTabBaseV, hdartrateBE, hchopB, hwad]; rfl
  have hIlksDec : config.externalABI.decode? "ilks" o' =
      some [bw (UInt256.ofNat (fromByteArrayBigEndian (o'.extract 0 32))),
        bw iRate, bw iSpot,
        bw (UInt256.ofNat (fromByteArrayBigEndian (o'.extract 96 128))),
        bw iDust] := by
    have h := catBiteIlksDecode_ok hilkslen
    rw [hbr o' 0 (by omega), hbr o' 32 (by omega), hbr o' 64 (by omega),
      hbr o' 96 (by omega), hbr o' 128 (by omega)] at h
    rw [hiRate, hiSpot, hiDustDef]; exact h
  have hUrnsDec : config.externalABI.decode? "urns" ou =
      some [bw ink, bw art] := by
    have h := catBiteUrnsDecode_ok hurnslen
    rw [hbr ou 0 (by omega), hbr ou 32 (by omega)] at h
    rw [hink, hart]; exact h
  obtain ⟨AG, hGrabCall'⟩ :=
    biteTypedCallZeroSetSubstate hGrabCall
      (by simpa [initState] using hdepthNe) Au
  obtain ⟨σgs, Ags, hGrabSolm, hEqGrab⟩ :=
    catBiteMapCall hEqU hGrabCall' hdepthNe
  set eGrabE := { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
    accountMap := σg, substate := AG, createdAccounts := cAg } with heGrabEdef
  set eGrabS := { initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I with
    accountMap := σgs, substate := Ags, createdAccounts := cAg } with heGrabSdef
  have heGEam : eGrabE.accountMap = σg := rfl
  have heGEee : eGrabE.executionEnv = I := rfl
  have htgtU : EVM.address (biteVatAddr eUrnS).val =
      AccountAddress.ofUInt256 ((solcSlotWord σu I ⟨3⟩).land biteAddrMaskWord) := by
    rw [← biteVatAddr_eq_of_equiv hEqU, addrId,
      accountAddress_ofUInt256_eq_ofNat_toNat, hmask]
    simp only [biteVatAddr, catSlotWord, heUEam, heUEee]
  have h1 : biteIlkVal I =
      Value.fixedBytes bytes32Width (EVM.Word.toBytesBE (biteIlkWord I)) := by
    simp only [biteIlkVal, hbytes]
  have h2 : biteUrnVal I = Value.address (AccountAddress.ofNat
      (biteAddrMaskWord.land
        (biteAddrMaskWord.land (calldataWord I.calldata 36))).toNat) := by
    rw [hurn]
    simp only [biteUrnVal, biteUrnWord, biteUrnAddr, hAddrRT]
  have h3 : (eUrnS.executionEnv.codeOwner : AccountAddress) =
      AccountAddress.ofNat (UInt256.ofNat I.codeOwner.val).toNat := by
    rw [heUSee]; exact (hAddrRT I.codeOwner).symm
  have h4 : biteVowAddrV eUrnS = AccountAddress.ofNat
      (biteAddrMaskWord.land (solcSlotWord σu I ⟨4⟩)).toNat := by
    rw [← biteVowAddrV_eq_of_equiv hEqU]
    simp only [biteVowAddrV, catSlotWord, heUEam, heUEee, hmask]
    rw [u256_land_comm]
  have hdartvBS : biteDartV I eUrnS iRate art = dart := by
    rw [← biteDartV_eq_of_equiv hEqU]; exact hdartvB
  have hdinkvBS : biteDinkV I eUrnS iRate art ink = dink := by
    rw [← biteDinkV_eq_of_equiv hEqU]; exact hdinkvB
  have hdartrateBS : biteDartRateV I eUrnS iRate art = dart.mul iRate := by
    rw [← biteDartRateV_eq_of_equiv hEqU]
    simp only [biteDartRateV, hdartvB]; rfl
  have htabBS : biteTabV I eUrnS iRate art = tab := by
    rw [← biteTabV_eq_of_equiv hEqU]; exact htabB
  have hGrabCodeS :
      ¬ Reasoning.Theory.extCodeSizeWord σus
        ((solcSlotWord σus I ⟨3⟩).land biteAddrMaskWord) = ⟨0⟩ := by
    rw [slotEqUS ⟨3⟩, ← extCodeSizeWord_accountMapEquiv hAmEq]
    exact hGrabCode
  rw [hperm, ← htgtU, ← h1, ← h2, ← h3, ← h4, ← hdinkvBS, ← hdartvBS]
    at hGrabSolm
  have hGrabDec : config.externalABI.decode? "grab" og = some [] := by
    simp [config, externalABI, decodeVoid?]
  obtain ⟨AF, hFessCall'⟩ :=
    biteTypedCallZeroSetSubstate hFessCall
      (by simpa [initState] using hdepthNe) AG
  obtain ⟨σfs, Afs, hFessSolm, hEqFess⟩ :=
    catBiteMapCall hEqGrab hFessCall' hdepthNe
  set eFessE := { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
    accountMap := σf, substate := AF, createdAccounts := cAf } with heFessEdef
  set eFessS := { initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I with
    accountMap := σfs, substate := Afs, createdAccounts := cAf } with heFessSdef
  have heFEam : eFessE.accountMap = σf := rfl
  have heFEee : eFessE.executionEnv = I := rfl
  have htgtF : EVM.address (biteVowAddrV eGrabS).val =
      AccountAddress.ofUInt256 (biteAddrMaskWord.land (solcSlotWord σg I ⟨4⟩)) := by
    rw [← biteVowAddrV_eq_of_equiv hEqGrab, addrId,
      accountAddress_ofUInt256_eq_ofNat_toNat, hmask, u256_land_comm]
    simp only [biteVowAddrV, catSlotWord, heGEam, heGEee]
  have hfessArg : bw (biteDartRateV I eUrnS iRate art) =
      Value.int (Int.ofNat (dart.mul iRate).toNat) := by rw [hdartrateBS]
  rw [hperm, ← htgtF, ← hfessArg] at hFessSolm
  have hFessDec : config.externalABI.decode? "fess" ofb = some [] := by
    simp [config, externalABI, decodeVoid?]
  have hvowCodeS : 0 < (UInt256.ofNat
      ((eGrabS.lookupAccount (biteVowAddrV eGrabS)).option 0
        (fun acc => acc.code.size))).toNat := by
    rw [← biteVowAddrV_eq_of_equiv hEqGrab,
      ← biteCodeW_eq_of_equiv (biteVowAddrV eGrabE) hEqGrab]
    have haddr : biteVowAddrV eGrabE =
        AccountAddress.ofUInt256 ((solcSlotWord σg I ⟨4⟩).land solcAddrMask) := by
      rw [accountAddress_ofUInt256_eq_ofNat_toNat]
      simp only [biteVowAddrV, catSlotWord, heGEam, heGEee]
    rw [haddr]
    refine codePos eGrabE ((solcSlotWord σg I ⟨4⟩).land solcAddrMask) ?_
    rw [heGEam, u256_land_comm, ← hmask]; exact hFessCode
  have hlitFB : biteLitW eFessE = solcSlotWord σf I ⟨6⟩ := by
    simp only [biteLitW, catSlotWord, heFEam, heFEee]
  have hlive' : catSlotWord ⟨2⟩ eUrnS.accountMap eUrnS.executionEnv = ⟨1⟩ := by
    rw [← biteSlotEqOfEquiv hEqU ⟨2⟩]; exact hlive
  have hlitFBS : biteLitW eFessS = solcSlotWord σf I ⟨6⟩ := by
    rw [← biteLitW_eq_of_equiv hEqFess]; exact hlitFB
  set iArt := UInt256.ofNat (fromByteArrayBigEndian (o'.extract 0 32)) with hiArtDef
  set iLine := UInt256.ofNat (fromByteArrayBigEndian (o'.extract 96 128)) with hiLineDef
  have hratePos : 0 < iRate.toNat := hposNe iRate hRatePos
  have hartPos : 0 < art.toNat := hposNe art hArtPos
  have hlitLtBox : (biteLitW eUrnS).toNat < (biteBoxW eUrnS).toNat := by
    rw [← biteLitW_eq_of_equiv hEqU, ← biteBoxW_eq_of_equiv hEqU, hlitB, hboxB]; exact hlitterbox
  have hroomGeDust : iDust.toNat ≤ (biteRoomV eUrnS).toNat := by
    rw [← biteRoomV_eq_of_equiv hEqU, hroomB]; exact hroomdust
  have hfitDunkRoomWad : (biteDunkRoomV I eUrnS).toNat * wadU.toNat < UInt256.size := by
    rw [← biteDunkRoomV_eq_of_equiv hEqU, hdunkroomB, hwad, Nat.mul_comm]; exact hFitWad
  have hmilkChopPos : 0 < (biteChopW I eUrnS).toNat := by
    rw [← biteChopW_eq_of_equiv hEqU, hchopB]; exact hposNe milkChop hChopPos
  have hfitInkDart : ink.toNat * (biteDartV I eUrnS iRate art).toNat < UInt256.size := by
    rw [← biteDartV_eq_of_equiv hEqU, hdartvB, Nat.mul_comm]; exact hFitInkDart
  have hdartPos : 0 < (biteDartV I eUrnS iRate art).toNat := by
    rw [← biteDartV_eq_of_equiv hEqU, hdartvB]; exact hDartPos
  have hdinkPos : 0 < (biteDinkV I eUrnS iRate art ink).toNat := by
    rw [← biteDinkV_eq_of_equiv hEqU, hdinkvB]; exact hDinkPos
  have hdartLim : Int.ofNat (biteDartV I eUrnS iRate art).toNat ≤ int256Limit := by
    rw [← biteDartV_eq_of_equiv hEqU, hdartvB]; simp only [int256Limit]
    exact Int.ofNat_le.mpr (hDartLim.trans_eq hsl)
  have hdinkLim : Int.ofNat (biteDinkV I eUrnS iRate art ink).toNat ≤ int256Limit := by
    rw [← biteDinkV_eq_of_equiv hEqU, hdinkvB]; simp only [int256Limit]
    exact Int.ofNat_le.mpr (hDinkLim.trans_eq hsl)
  have hfitDartRate : (biteDartV I eUrnS iRate art).toNat * iRate.toNat < UInt256.size := by
    rw [← biteDartV_eq_of_equiv hEqU, hdartvB, Nat.mul_comm]; exact hRateFit
  have hfitTabBase :
      (biteDartRateV I eUrnS iRate art).toNat * (biteChopW I eUrnS).toNat < UInt256.size := by
    rw [← biteDartRateV_eq_of_equiv hEqU, ← biteChopW_eq_of_equiv hEqU, hdartrateBE, hchopB,
      Nat.mul_comm]; exact hChopFit
  have hvowCode := hvowCodeS
  have hvatCodeMid : 0 < (UInt256.ofNat
      ((eUrnS.lookupAccount (biteVatAddr eUrnS)).option 0 (fun acc => acc.code.size))).toNat := by
    have haddr : biteVatAddr eUrnS = AccountAddress.ofUInt256 (catBiteVatTargetWord σus I) := by
      rw [accountAddress_ofUInt256_eq_ofNat_toNat]
      simp only [biteVatAddr, catBiteVatTargetWord, catAddressReturnWord, catSlotWord, heUSam, heUSee]
    rw [haddr]
    refine codePos eUrnS (catBiteVatTargetWord σus I) ?_
    rw [heUSam, show catBiteVatTargetWord σus I = (solcSlotWord σus I ⟨3⟩).land biteAddrMaskWord from by
        simp only [catBiteVatTargetWord, catAddressReturnWord, catSlotWord, hmask]]
    exact hGrabCodeS
  have hover : UInt256.size ≤
      (catSlotWord ⟨6⟩ eFessS.accountMap eFessS.executionEnv).toNat
        + (biteTabV I eUrnS iRate art).toNat := by
    have e1 : catSlotWord ⟨6⟩ eFessS.accountMap eFessS.executionEnv = solcSlotWord σf I ⟨6⟩ := by
      rw [show catSlotWord ⟨6⟩ eFessS.accountMap eFessS.executionEnv = biteLitW eFessS from by
            simp only [biteLitW], hlitFBS]
    rw [e1, htabBS]; exact Nat.le_of_not_lt hLitNofit
  have hbody :
      ExecTransitionBody config contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) (biteLocals I)
        biteTransition.body .reverted := by
    rw [ExecTransitionBody, biteBody_split]
    refine ExecFuncBody.execBlockRevert
      (execBlock_append (catBiteSourcePreLive hwv
          (catBiteVatCodePos_of_uniswap hAccounts hvatCode) hIlksSolm hIlksDec hvatCodeIlkS
          hUrnsSolm hUrnsDec hlive')
        (execBlock_append (catBiteSourceArith1 hsz36 hfitInkSpot hfitArtRate hspotPos hratePos
            hunsafe hlitLtBox hroomGeDust)
          (execBlock_append (catBiteSourceArith2 hratePos hartPos hmilkChopPos hfitDunkRoomWad
              hfitInkDart hdartPos hdinkPos hdartLim hdinkLim)
            ?_)))
    refine ExecBlock.consNormal (ExecStmt.requireTrue
      (biteVatGuard_true (bsDink_get_vat I eUrnS iArt iRate iSpot iLine iDust ink art) hvatCodeMid)) ?_
    refine ExecBlock.consNormal (biteGrabSuccessStmt hGrabSolm hGrabDec) ?_
    refine ExecBlock.consNormal
      (ExecStmt.letDecl (evalExpr_mul256_ok (evalExpr_varUInt256 (btGrab_get_dart I eUrnS iArt iRate iSpot iLine iDust ink art))
        (evalExpr_varUInt256 (btGrab_get_rate I eUrnS iArt iRate iSpot iLine iDust ink art)) rfl hfitDartRate)) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue
      (evalExpr_checkedMulCheck_true (evalExpr_varUInt256 (btDartRate_get_dart I eUrnS iArt iRate iSpot iLine iDust ink art))
        (evalExpr_varUInt256 (btDartRate_get_rate I eUrnS iArt iRate iSpot iLine iDust ink art))
        (btDartRate_get_dartRate I eUrnS iArt iRate iSpot iLine iDust ink art) rfl hfitDartRate hratePos)) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue
      (biteVowGuard_true (btDartRate_get_vow I eUrnS iArt iRate iSpot iLine iDust ink art) hvowCode)) ?_
    refine ExecBlock.consNormal (biteFessSuccessStmt hFessSolm hFessDec) ?_
    refine ExecBlock.consNormal
      (ExecStmt.letDecl (evalExpr_mul256_ok (evalExpr_varUInt256 (btFess_get_dartRate I eUrnS iArt iRate iSpot iLine iDust ink art))
        (evalExpr_varUInt256 (btFess_get_milkChop I eUrnS iArt iRate iSpot iLine iDust ink art)) rfl hfitTabBase)) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue
      (evalExpr_checkedMulCheck_true (evalExpr_varUInt256 (btTabBase_get_dartRate I eUrnS iArt iRate iSpot iLine iDust ink art))
        (evalExpr_varUInt256 (btTabBase_get_milkChop I eUrnS iArt iRate iSpot iLine iDust ink art))
        (btTabBase_get_tabBase I eUrnS iArt iRate iSpot iLine iDust ink art) rfl hfitTabBase hmilkChopPos)) ?_
    refine ExecBlock.consNormal
      (ExecStmt.letDecl (evalExpr_div256_ok (evalExpr_varUInt256 (btTabBase_get_tabBase I eUrnS iArt iRate iSpot iLine iDust ink art))
        evalExpr_wad wadU_pos)) ?_
    exact ExecBlock.consRevert (ExecStmt.letDeclRevert
      (evalExpr_add256_revert
        (biteLitterRead (btTab_get_litter I eUrnS iArt iRate iSpot iLine iDust ink art))
        (evalExpr_varUInt256 (btTab_get_tab I eUrnS iArt iRate iSpot iLine iDust ink art)) hover))
  have hDartRate : UInt256.mul dart iRate = dartRate := hdartRateDef.symm
  have hTabBase : UInt256.mul dartRate milkChop = tabBase := htabBaseDef.symm
  have hTab : UInt256.div tabBase ⟨1000000000000000000⟩ = tab := htabDef.symm
  obtain ⟨_, _, rd2321f⟩ := catBiteTraceSeg7h rd2300 hstatus (by simp)
  have e32q : (⟨32⟩ + q).toNat = q.toNat + 32 := uadd_lit32_toNat q (by omega)
  have hChopAw : UInt256.ofNat (MachineState.M aw2.toNat (⟨32⟩ + q).toNat 32) = aw2 :=
    catBiteAwMInv32 aw2 (by rw [e32q]; omega)
  have rd2321 := rd2321f.push1 ⟨0⟩ (by native_decide) (by evm_ov)
  have rd2323 := RD.push8 rd2321 ⟨1000000000000000000⟩ (by native_decide) (by evm_ov)
  have rd2332 := rd2323.push2 ⟨2354⟩ (by native_decide) (by evm_ov)
  have rd2335 := rd2332.push2 ⟨2344⟩ (by native_decide) (by evm_ov)
  have rd2338 := rd2335.dup6 (by native_decide) (by evm_ov)
  have rd2339 := rd2338.dup13 (by native_decide) (by evm_ov)
  have rd2340 := rd2339.push2 ⟨3720⟩ (by native_decide) (by evm_ov)
  have rd3720a := rd2340.jump (by native_decide) (by jump_dest) (by evm_ov)
  obtain ⟨_, _, rd2344⟩ := RD.catBiteCheckedMul rd3720a hRateFit (by native_decide) (by evm_ov)
  rw [hDartRate] at rd2344
  have rd2344j := rd2344.jumpdest (by native_decide) (by evm_ov)
  have rd2345 := rd2344j.dup7 (by native_decide) (by evm_ov)
  have rd2346 := rd2345.push1 ⟨32⟩ (by native_decide) (by evm_ov)
  have rd2348 := rd2346.add (by native_decide) (by evm_ov)
  have rd2349 := RD.mload 0 milkChop aw2 rd2348 (by native_decide) (catBiteMloadCost0 hChopAw)
    hChop hChopAw (by evm_ov)
  have rd2350 := rd2349.push2 ⟨3720⟩ (by native_decide) (by evm_ov)
  have rd3720b := rd2350.jump (by native_decide) (by jump_dest) (by evm_ov)
  obtain ⟨_, _, rd2354⟩ := RD.catBiteCheckedMul rd3720b hChopFit (by native_decide) (by evm_ov)
  rw [hTabBase] at rd2354
  have rd2354j := rd2354.jumpdest (by native_decide) (by evm_ov)
  have rd2355 := rd2354j.dup2 (by native_decide) (by evm_ov)
  have rd2356 := rd2355.push2 ⟨2361⟩ (by native_decide) (by evm_ov)
  have rd2361 := rd2356.jumpiT (by native_decide) (by decide) (by jump_dest) (by evm_ov)
  have rd2361j := rd2361.jumpdest (by native_decide) (by evm_ov)
  have rd2362 := rd2361j.div (by native_decide) (by evm_ov)
  rw [hTab] at rd2362
  have rd2363 := rd2362.swap1 (by native_decide) (by evm_ov)
  have rd2364 := rd2363.pop (by native_decide) (by evm_ov)
  have rd2365 := rd2364.push2 ⟨2376⟩ (by native_decide) (by evm_ov)
  have rd2368 := rd2365.push1 ⟨6⟩ (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd2370raw⟩ := rd2368.sload (by native_decide) (by evm_ov)
  have rd2371 := rd2370raw.dup3 (by native_decide) (by evm_ov)
  have rd2372 := rd2371.push2 ⟨3802⟩ (by native_decide) (by evm_ov)
  have rd3802 := rd2372.jump (by native_decide) (by jump_dest) (by evm_ov)
  have hrev := RD.catBiteCheckedAddRevert rd3802 (Nat.le_of_not_lt hLitNofit)
    (by simp only [List.length_cons, List.length_nil]; omega)
  simpa using hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody

end Benchmarks.Dss.Cat
