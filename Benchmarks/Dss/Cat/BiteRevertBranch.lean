import Benchmarks.Dss.Cat.BiteBody

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

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
      ¬ Reasoning.Theory.uniswapExtCodeSizeWord σ' ((catSlotWord ⟨3⟩ σ' I).land biteAddrMaskWord) = ⟨0⟩)
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
      uniswapExtCodeSizeWord e.accountMap w ≠ ⟨0⟩ →
      0 < (UInt256.ofNat ((e.lookupAccount
        (AccountAddress.ofUInt256 w)).option 0 (fun acc => acc.code.size))).toNat := by
    intro e w hw
    unfold uniswapExtCodeSizeWord at hw
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
      ← hslot3, ← uniswapExtCodeSizeWord_accountMapEquiv hEqIlk.accountMap]
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
    (hvatCode : ¬ Reasoning.Theory.uniswapExtCodeSizeWord σ_evm (catBiteVatTargetWord σ_evm I) = ⟨0⟩)
    (hUrnsVatCode :
      ¬ Reasoning.Theory.uniswapExtCodeSizeWord σ' ((catSlotWord ⟨3⟩ σ' I).land biteAddrMaskWord) = ⟨0⟩)
    (hGrabCode :
      ¬ Reasoning.Theory.uniswapExtCodeSizeWord σu ((solcSlotWord σu I ⟨3⟩).land biteAddrMaskWord) = ⟨0⟩)
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
      uniswapExtCodeSizeWord e.accountMap w ≠ ⟨0⟩ →
      0 < (UInt256.ofNat ((e.lookupAccount
        (AccountAddress.ofUInt256 w)).option 0
        (fun acc => acc.code.size))).toNat := by
    intro e w hw
    unfold uniswapExtCodeSizeWord at hw
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
      ¬ Reasoning.Theory.uniswapExtCodeSizeWord σus
        ((solcSlotWord σus I ⟨3⟩).land biteAddrMaskWord) = ⟨0⟩ := by
    rw [slotEqUS ⟨3⟩, ← uniswapExtCodeSizeWord_accountMapEquiv hAmEq]
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

end Benchmarks.Dss.Cat
