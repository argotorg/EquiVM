import Benchmarks.Dss.Cat.BiteConnect

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

namespace Benchmarks.Dss.Cat

/-! # Cat `bite` — the success branch of `catBiteBody`

`catBiteSuccessBranch` is the all-`z=true` leaf: given the 5 σ_evm-side calls (in the concrete
`{ initState … with … }` shapes the reach-wrappers produce) plus the decoded values / arithmetic
conditions and the chained `RDret`, it threads the σ_evm→σ_solm coupling across the 5 calls
(`catBiteMapIlksCall` then 4× `catBiteMapCall`, with the litter `SSTORE` in the middle via
`EVMStateEquiv.storageStore_codeOwner`) and feeds `catBiteSuccessLeaf`.

The σ_evm-side scenario is exactly `catBiteSourceSuccess`'s hypothesis set instantiated at `σ_evm`,
with the intermediate EVM states pinned to `{ initState … with accountMap/substate/createdAccounts }`
so that `catBiteMapCall`'s pattern matches for the chained calls.  The map lemmas produce the
σ_solm-side intermediate states existentially; the remaining work — established after the mapping —
is transferring each `catBiteSourceSuccess` side-condition (code-size guards, `live == 1`, the
arithmetic bounds, the storage reads) from the σ_evm states to the `accountMapEquiv`/`EVMStateEquiv`-
coupled σ_solm states, then invoking `catBiteSuccessLeaf`.  That transfer is the single remaining
step (the one remaining gap below): every needed coupling accessor is green
(`EVMStateEquiv.{accountMap,executionEnv,createdAccounts,storageLoad_codeOwner}`,
`accountMapEquiv_storage_findD`, `uniswapExtCodeSizeWord_accountMapEquiv`,
`typedCallViaEVM_static_storage_findD_of_accountMapEquiv`), and the values coincide because the
mapped calls return the identical `out`/`z`, so the decode lemmas give equal `iRate`/`ink`/… on both
sides.

`catBiteSuccessBranch` takes the σ_evm scenario + `RDret` + `accountMapEquiv` and concludes the
`runtimeEquivalenceFor` goal — the caller (`catBiteBody`) chains the reach-wrappers, `cases z`→true,
and discharges the wrapper memory hypotheses (via `writeReturnCopy_read32` +
`readWithPadding_eq_toByteArray_ofNat` + the decode lemmas) to supply this lemma's inputs. -/
theorem catBiteSuccessBranch {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {evmIlk evmUrn evmGrab evmFess evmLit evmKick : EVM.State}
    {ilksOut urnsOut grabOut fessOut kickOut : ByteArray}
    {iArt iRate iSpot iLine iDust ink art id : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (hcode : I.code = catBytecode)
    (hret : RDret catBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) acc (UInt256.toByteArray id))
    (hdispatch : dispatchMsg contract I.calldata = some biteTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (biteTransition.params.map Param.name)
        (transitionSignature biteTransition).paramTypes I.calldata = some (biteLocals I))
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsz36 : 36 ≤ I.calldata.size) (hwv : I.weiValue = ⟨0⟩)
    (hvatCode0 :
      0 < (UInt256.ofNat
        (((initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
          (biteVatAddr (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I))).option 0
          (fun acc => acc.code.size))).toNat)
    (hIlksCall :
      typedCallViaEVM config (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (biteVatAddr (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)))
        "ilks" 0 [biteIlkVal I] (true, evmIlk, ilksOut) false)
    (hIlksDec :
      config.externalABI.decode? "ilks" ilksOut =
        some [bw iArt, bw iRate, bw iSpot, bw iLine, bw iDust])
    (hvatCodeIlk :
      0 < (UInt256.ofNat
        ((evmIlk.lookupAccount (biteVatAddr evmIlk)).option 0 (fun acc => acc.code.size))).toNat)
    (hUrnsCall :
      typedCallViaEVM config evmIlk (EVM.address (biteVatAddr evmIlk))
        "urns" 0 [biteIlkVal I, biteUrnVal I] (true, evmUrn, urnsOut) false)
    (hUrnsDec : config.externalABI.decode? "urns" urnsOut = some [bw ink, bw art])
    (hlive : catSlotWord ⟨2⟩ evmUrn.accountMap evmUrn.executionEnv = ⟨1⟩)
    (hfitInkSpot : ink.toNat * iSpot.toNat < UInt256.size)
    (hfitArtRate : art.toNat * iRate.toNat < UInt256.size)
    (hfitDunkRoomWad : (biteDunkRoomV I evmUrn).toNat * wadU.toNat < UInt256.size)
    (hfitInkDart : ink.toNat * (biteDartV I evmUrn iRate art).toNat < UInt256.size)
    (hfitDartRate : (biteDartV I evmUrn iRate art).toNat * iRate.toNat < UInt256.size)
    (hfitTabBase :
      (biteDartRateV I evmUrn iRate art).toNat * (biteChopW I evmUrn).toNat < UInt256.size)
    (hfitLitterNew : (biteLitW evmFess).toNat + (biteTabV I evmUrn iRate art).toNat < UInt256.size)
    (hspotPos : 0 < iSpot.toNat) (hratePos : 0 < iRate.toNat) (hartPos : 0 < art.toNat)
    (hmilkChopPos : 0 < (biteChopW I evmUrn).toNat)
    (hunsafe : (ink * iSpot).toNat < (art * iRate).toNat)
    (hlitLtBox : (biteLitW evmUrn).toNat < (biteBoxW evmUrn).toNat)
    (hroomGeDust : iDust.toNat ≤ (biteRoomV evmUrn).toNat)
    (hdartPos : 0 < (biteDartV I evmUrn iRate art).toNat)
    (hdinkPos : 0 < (biteDinkV I evmUrn iRate art ink).toNat)
    (hdartLim : Int.ofNat (biteDartV I evmUrn iRate art).toNat ≤ int256Limit)
    (hdinkLim : Int.ofNat (biteDinkV I evmUrn iRate art ink).toNat ≤ int256Limit)
    (hvatCodeMid :
      0 < (UInt256.ofNat
        ((evmUrn.lookupAccount (biteVatAddr evmUrn)).option 0 (fun acc => acc.code.size))).toNat)
    (hGrabCall :
      typedCallViaEVM config evmUrn (EVM.address (biteVatAddr evmUrn)) "grab" 0
        [biteIlkVal I, biteUrnVal I, .address evmUrn.executionEnv.codeOwner,
          .address (biteVowAddrV evmUrn), .int (-(Int.ofNat (biteDinkV I evmUrn iRate art ink).toNat)),
          .int (-(Int.ofNat (biteDartV I evmUrn iRate art).toNat))] (true, evmGrab, grabOut) true)
    (hGrabDec : config.externalABI.decode? "grab" grabOut = some [])
    (hvowCode :
      0 < (UInt256.ofNat
        ((evmGrab.lookupAccount (biteVowAddrV evmGrab)).option 0 (fun acc => acc.code.size))).toNat)
    (hFessCall :
      typedCallViaEVM config evmGrab (EVM.address (biteVowAddrV evmGrab)) "fess" 0
        [bw (biteDartRateV I evmUrn iRate art)] (true, evmFess, fessOut) true)
    (hFessDec : config.externalABI.decode? "fess" fessOut = some [])
    (hLitStore :
      storageLocStore evmFess (wordLoc ⟨6⟩)
        (.int (Int.ofNat (biteLitterNewV I evmUrn evmFess iRate art).toNat)) = some evmLit)
    (hflipCode :
      0 < (UInt256.ofNat
        ((evmLit.lookupAccount (biteFlipAddrV I evmUrn)).option 0 (fun acc => acc.code.size))).toNat)
    (hKickCall :
      typedCallViaEVM config evmLit (EVM.address (biteFlipAddrV I evmUrn)) "kick" 0
        [biteUrnVal I, .address (biteVowAddrV evmLit), bw (biteTabV I evmUrn iRate art),
          bw (biteDinkV I evmUrn iRate art ink), .int 0] (true, evmKick, kickOut) true)
    (hKickDec : config.externalABI.decode? "kick" kickOut = some [bw id])
    (hcreated : acc.1 = evmKick.createdAccounts)
    (hAccountsFinal : accountMapEquiv acc.2 evmKick.accountMap) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  -- The σ_evm-side scenario coincides with `catBiteSourceSuccess` at `σ := σ_evm`; feeding it to
  -- `catBiteSuccessLeaf` requires the same scenario transported to `σ_solm` via the 5-call
  -- `EVMStateEquiv` thread (`catBiteMapIlksCall`/`catBiteMapCall`, litter `SSTORE` in the middle),
  -- with every side-condition re-derived from the couplings.
  have hdepthNe : I.depth ≠ 1024 := by
    obtain ⟨_, _, hraw⟩ := hIlksCall
    cases hraw with
    | callMade _ _ _ _ hd => simpa [initState] using hd
  -- Every `callMade`/`callNotMade` result is a record-update of the caller state.
  have callShape : ∀ {ev ev' : EVM.State} {t : EVM.Address} {nm : Ident}
      {ar : List Value} {zz pp : Bool} {oo : ByteArray},
      typedCallViaEVM config ev t nm 0 ar (zz, ev', oo) pp →
      ∃ σ AA c, ev' = { ev with accountMap := σ, substate := AA, createdAccounts := c } := by
    intro ev ev' t nm ar zz pp oo hc
    obtain ⟨cd, henc, hraw⟩ := hc
    cases hraw with
    | callMade _ _ hevm' _ _ => exact ⟨_, _, _, hevm'⟩
    | callNotMade _ hevm' _ => exact ⟨ev.accountMap, _, ev.createdAccounts, hevm'⟩
  -- Flatten shape for calls whose input is already an `initState σ_evm` record-update.
  have flatShape : ∀ {σx : AccountMap} {Ax : Substate}
      {cx : Batteries.RBSet AccountAddress compare} {ev' : EVM.State} {t : EVM.Address} {nm : Ident}
      {ar : List Value} {zz pp : Bool} {oo : ByteArray},
      typedCallViaEVM config
        { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
            accountMap := σx, substate := Ax, createdAccounts := cx } t nm 0 ar (zz, ev', oo) pp →
      ∃ σ AA c, ev' =
        { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
            accountMap := σ, substate := AA, createdAccounts := c } := by
    intro σx Ax cx ev' t nm ar zz pp oo hc
    obtain ⟨σ, AA, c, h⟩ := callShape hc
    exact ⟨σ, AA, c, h⟩
  -- `catSlotWord` transports across `EVMStateEquiv` (same codeOwner storage view).
  have slotEq : ∀ {a b : EVM.State}, EVMStateEquiv a b → ∀ s : UInt256,
      catSlotWord s a.accountMap a.executionEnv = catSlotWord s b.accountMap b.executionEnv := by
    intro a b h s
    simp only [catSlotWord, solcSlotWord]
    rw [h.executionEnv]
    exact accountMapEquiv_storage_findD h.accountMap b.executionEnv.codeOwner s ⟨0⟩
  -- Derived-quantity transfers across `EVMStateEquiv` (all read `catSlotWord`).
  have eVat : ∀ {a b : EVM.State}, EVMStateEquiv a b → biteVatAddr a = biteVatAddr b := by
    intro a b h; simp only [biteVatAddr, slotEq h]
  have eVow : ∀ {a b : EVM.State}, EVMStateEquiv a b → biteVowAddrV a = biteVowAddrV b := by
    intro a b h; simp only [biteVowAddrV, slotEq h]
  have eFlip : ∀ {a b : EVM.State}, EVMStateEquiv a b → biteFlipAddrV I a = biteFlipAddrV I b := by
    intro a b h; simp only [biteFlipAddrV, slotEq h]
  have eBox : ∀ {a b : EVM.State}, EVMStateEquiv a b → biteBoxW a = biteBoxW b := by
    intro a b h; simp only [biteBoxW, slotEq h]
  have eLit : ∀ {a b : EVM.State}, EVMStateEquiv a b → biteLitW a = biteLitW b := by
    intro a b h; simp only [biteLitW, slotEq h]
  have eChop : ∀ {a b : EVM.State}, EVMStateEquiv a b → biteChopW I a = biteChopW I b := by
    intro a b h; simp only [biteChopW, slotEq h]
  have eRoom : ∀ {a b : EVM.State}, EVMStateEquiv a b → biteRoomV a = biteRoomV b := by
    intro a b h; simp only [biteRoomV, biteBoxW, biteLitW, slotEq h]
  have eDunkRoom : ∀ {a b : EVM.State}, EVMStateEquiv a b → biteDunkRoomV I a = biteDunkRoomV I b := by
    intro a b h; simp only [biteDunkRoomV, biteDunkW, biteRoomV, biteBoxW, biteLitW, slotEq h]
  have eDart : ∀ {a b : EVM.State}, EVMStateEquiv a b → ∀ r art,
      biteDartV I a r art = biteDartV I b r art := by
    intro a b h r art
    simp only [biteDartV, biteDartCandV, biteDartDenomV, biteDunkRoomWadV, biteDunkRoomV, biteDunkW,
      biteRoomV, biteBoxW, biteLitW, biteChopW, slotEq h]
  have eDink : ∀ {a b : EVM.State}, EVMStateEquiv a b → ∀ r art ink,
      biteDinkV I a r art ink = biteDinkV I b r art ink := by
    intro a b h r art ink
    simp only [biteDinkV, biteDinkCandV, biteInkDartV, biteDartV, biteDartCandV, biteDartDenomV,
      biteDunkRoomWadV, biteDunkRoomV, biteDunkW, biteRoomV, biteBoxW, biteLitW, biteChopW, slotEq h]
  have eDartRate : ∀ {a b : EVM.State}, EVMStateEquiv a b → ∀ r art,
      biteDartRateV I a r art = biteDartRateV I b r art := by
    intro a b h r art
    simp only [biteDartRateV, biteDartV, biteDartCandV, biteDartDenomV, biteDunkRoomWadV,
      biteDunkRoomV, biteDunkW, biteRoomV, biteBoxW, biteLitW, biteChopW, slotEq h]
  have eTab : ∀ {a b : EVM.State}, EVMStateEquiv a b → ∀ r art,
      biteTabV I a r art = biteTabV I b r art := by
    intro a b h r art
    simp only [biteTabV, biteTabBaseV, biteDartRateV, biteDartV, biteDartCandV, biteDartDenomV,
      biteDunkRoomWadV, biteDunkRoomV, biteDunkW, biteRoomV, biteBoxW, biteLitW, biteChopW, slotEq h]
  have eLitterNew : ∀ {au bu af bf : EVM.State}, EVMStateEquiv au bu → EVMStateEquiv af bf →
      ∀ r art, biteLitterNewV I au af r art = biteLitterNewV I bu bf r art := by
    intro au bu af bf hu hf r art
    simp only [biteLitterNewV, biteLitW, biteTabV, biteTabBaseV, biteDartRateV, biteDartV,
      biteDartCandV, biteDartDenomV, biteDunkRoomWadV, biteDunkRoomV, biteDunkW, biteRoomV, biteBoxW,
      biteChopW, slotEq hu, slotEq hf]
  -- Code size at an address transports across `EVMStateEquiv` (`accountMapEquiv` preserves code).
  have eCodeW : ∀ {a b : EVM.State} (addr : AccountAddress), EVMStateEquiv a b →
      UInt256.ofNat ((a.lookupAccount addr).option 0 (fun acc => acc.code.size)) =
        UInt256.ofNat ((b.lookupAccount addr).option 0 (fun acc => acc.code.size)) := by
    intro a b addr h
    have hw := accountMapEquiv_code_size_word h.accountMap addr
    simp only [State.lookupAccount]
    cases ha : a.accountMap.find? addr <;> cases hb : b.accountMap.find? addr <;>
      rw [ha, hb] at hw <;> simpa [Option.option, EVM.Word.ofNat] using hw
  -- `storageStore` only changes the account map (to `sstoreAccountMap`).
  have storeFlat : ∀ (ev : EVM.State) (aa : AccountAddress) (k v : UInt256),
      Solm.EVM.storageStore ev aa k v =
        { ev with accountMap := sstoreAccountMap aa ev.accountMap k v } := by
    intro ev aa k v
    simp only [Solm.EVM.storageStore, sstoreAccountMap, State.lookupAccount]
    cases h : ev.accountMap.find? aa with
    | none => simp [Option.option]
    | some acc => simp [Option.option, State.setAccount, Account.updateStorage]
  -- Map a value-`0` call from any `EVMStateEquiv`-coupled state (with matching σ₀/genesis/blocks).
  have mapAnyCall : ∀ {ea eb ea' : EVM.State} {tgt : EVM.Address} {nm : Ident} {ar : List Value}
      {zz pp : Bool} {oo : ByteArray},
      typedCallViaEVM config ea tgt nm 0 ar (zz, ea', oo) pp →
      EVMStateEquiv ea eb → ea.σ₀ = eb.σ₀ → ea.genesisBlockHeader = eb.genesisBlockHeader →
      ea.blocks = eb.blocks → ea.executionEnv.depth ≠ 1024 →
      ∃ (σ' : AccountMap) (AA' : Substate),
        typedCallViaEVM config eb tgt nm 0 ar
          (zz, { eb with accountMap := σ', substate := AA', createdAccounts := ea'.createdAccounts }, oo)
            pp ∧
        EVMStateEquiv ea'
          { eb with accountMap := σ', substate := AA', createdAccounts := ea'.createdAccounts } := by
    intro ea eb ea' tgt nm ar zz pp oo hcall hEq hσ₀ hgen hblk hdepth
    obtain ⟨σ', AA'0, hcallBase, hAcc'⟩ :=
      typedCallViaEVM_accountMapEquiv (evm_solm := { eb with substate := ea.substate })
        hcall (by simpa using hEq.accountMap) (by simpa using hσ₀)
        (by simpa using hEq.createdAccounts.symm) (by simpa using hgen.symm) (by simpa using hblk.symm)
        rfl (by simpa using hEq.executionEnv.symm)
    obtain ⟨AA', hcallSolm⟩ :=
      biteTypedCallZeroSetSubstate hcallBase (by simpa [hEq.executionEnv] using hdepth) eb.substate
    refine ⟨σ', AA', by simpa using hcallSolm, ?_, ?_, ?_⟩
    · exact (typedCallViaEVM_executionEnv_eq hcall).trans hEq.executionEnv
    · rfl
    · simpa using hAcc'
  -- Concretize evmIlk to a record-update of `initState σ_evm`.
  obtain ⟨σI, AI, cAI, hIlkShape⟩ := callShape hIlksCall
  subst evmIlk
  -- Map the ilks STATICCALL.
  obtain ⟨σ_ilk_solm, A_ilk_solm, hIlksCallSolm, hStateIlk⟩ := catBiteMapIlksCall hAccounts hIlksCall
  -- Concretize evmUrn, then map the urns STATICCALL.
  obtain ⟨σU, AU, cAU, hUrnShape⟩ := flatShape hUrnsCall
  subst evmUrn
  obtain ⟨σ_urn_solm, A_urn_solm, hUrnsCallSolm, hStateUrn⟩ := catBiteMapCall hStateIlk hUrnsCall hdepthNe
  -- Concretize evmGrab, then map the grab CALL.
  obtain ⟨σG, AG, cAG, hGrabShape⟩ := flatShape hGrabCall
  subst evmGrab
  obtain ⟨σ_grab_solm, A_grab_solm, hGrabCallSolm, hStateGrab⟩ := catBiteMapCall hStateUrn hGrabCall hdepthNe
  -- Concretize evmFess, then map the fess CALL.
  obtain ⟨σF, AF, cAF, hFessShape⟩ := flatShape hFessCall
  subst evmFess
  obtain ⟨σ_fess_solm, A_fess_solm, hFessCallSolm, hStateFess⟩ := catBiteMapCall hStateGrab hFessCall hdepthNe
  -- Litter `SSTORE`: characterize evmLit as a `storageStore` of evmFess.
  have hWeq := eLitterNew hStateUrn hStateFess iRate art
  have hLitEq := Option.some.inj (hLitStore.symm.trans (storageLocStore_uint256 _ ⟨6⟩ _))
  have hStateLit := hStateFess.storageStore_codeOwner ⟨6⟩ hWeq
  rw [hLitEq] at hKickCall hflipCode
  -- Map the kick CALL (from the litter-`SSTORE` state).
  obtain ⟨σ_kick_solm, A_kick_solm, hKickCallSolm, hStateKick⟩ :=
    mapAnyCall hKickCall hStateLit (by simp [storeFlat, initState]) (by simp [storeFlat, initState])
      (by simp [storeFlat, initState]) (by simpa [storeFlat, initState] using hdepthNe)
  -- Rewrite the σ_solm calls' targets/args from the σ_evm side to the σ_solm side.
  have hInit : EVMStateEquiv (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
      (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) := EVMStateEquiv.initState hAccounts
  rw [eVat hInit] at hIlksCallSolm
  rw [eVat hStateIlk] at hUrnsCallSolm
  rw [eVat hStateUrn, congrArg (fun e => e.codeOwner) hStateUrn.executionEnv, eVow hStateUrn,
    eDink hStateUrn iRate art ink, eDart hStateUrn iRate art] at hGrabCallSolm
  rw [eVow hStateGrab, eDartRate hStateUrn iRate art] at hFessCallSolm
  rw [eFlip hStateUrn, eVow hStateLit, eTab hStateUrn iRate art,
    eDink hStateUrn iRate art ink] at hKickCallSolm
  -- Transfer the side-conditions from the σ_evm states to the σ_solm states.
  rw [eVat hInit, eCodeW _ hInit] at hvatCode0
  rw [eVat hStateIlk, eCodeW _ hStateIlk] at hvatCodeIlk
  rw [slotEq hStateUrn ⟨2⟩] at hlive
  rw [eDunkRoom hStateUrn] at hfitDunkRoomWad
  rw [eDart hStateUrn iRate art] at hfitInkDart
  rw [eDart hStateUrn iRate art] at hfitDartRate
  rw [eDartRate hStateUrn iRate art, eChop hStateUrn] at hfitTabBase
  rw [eLit hStateFess, eTab hStateUrn iRate art] at hfitLitterNew
  rw [eChop hStateUrn] at hmilkChopPos
  rw [eLit hStateUrn, eBox hStateUrn] at hlitLtBox
  rw [eRoom hStateUrn] at hroomGeDust
  rw [eDart hStateUrn iRate art] at hdartPos
  rw [eDink hStateUrn iRate art ink] at hdinkPos
  rw [eDart hStateUrn iRate art] at hdartLim
  rw [eDink hStateUrn iRate art ink] at hdinkLim
  rw [eVat hStateUrn, eCodeW _ hStateUrn] at hvatCodeMid
  rw [eVow hStateGrab, eCodeW _ hStateGrab] at hvowCode
  rw [eFlip hStateUrn, eCodeW _ hStateLit] at hflipCode
  -- Feed the σ_solm scenario to the success leaf.
  exact catBiteSuccessLeaf hcode hret hdispatch hdecode hsz36 hwv hvatCode0 hIlksCallSolm hIlksDec
    hvatCodeIlk hUrnsCallSolm hUrnsDec hlive hfitInkSpot hfitArtRate hfitDunkRoomWad hfitInkDart
    hfitDartRate hfitTabBase hfitLitterNew hspotPos hratePos hartPos hmilkChopPos hunsafe hlitLtBox
    hroomGeDust hdartPos hdinkPos hdartLim hdinkLim hvatCodeMid hGrabCallSolm hGrabDec hvowCode
    hFessCallSolm hFessDec (storageLocStore_uint256 _ ⟨6⟩ _) hflipCode hKickCallSolm hKickDec
    (hcreated.trans hStateKick.createdAccounts)
    (accountMapEquiv.trans hAccountsFinal hStateKick.accountMap)

end Benchmarks.Dss.Cat
