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

end Benchmarks.Dss.Cat
