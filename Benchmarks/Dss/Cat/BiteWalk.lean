import Benchmarks.Dss.Cat.BiteBody
import Benchmarks.Dss.Cat.BiteRevertBranch

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

namespace Benchmarks.Dss.Cat

/-- `urns` returns `(uint256,uint256)`; `< 64` bytes cannot ABI-decode the 2-word tuple. Urns
analogue of `catBiteIlksDecode_none`. -/
theorem catBiteUrnsDecode_none {o : ByteArray} (hoLt : o.size < 64) :
    config.externalABI.decode? "urns" o = none := by
  show ABI.decodeReturnValuesWithMode? DecodeMode.legacySolc05 [abiUInt256, abiUInt256] o = none
  have holen : o.toList.length = o.size := by rw [byteArray_toList_eq, Array.length_toList]; rfl
  have hnone : decodeScalarWordsWithMode? DecodeMode.legacySolc05 [abiUInt256, abiUInt256]
      o.toList 0 = none := by
    cases h : decodeScalarWordsWithMode? DecodeMode.legacySolc05 [abiUInt256, abiUInt256]
        o.toList 0 with
    | none => rfl
    | some vals =>
        exfalso
        have hlen := decodeScalarWordsWithMode?_some_length (by simp) h
        rw [holen] at hlen
        simp only [List.length_cons, List.length_nil] at hlen
        omega
  unfold ABI.decodeReturnValuesWithMode?
  rw [abiTupleHeadSize_scalarWords_eq (types := [abiUInt256, abiUInt256]) (by decide)]
  simp only [bind, Option.bind]
  rw [decodeABIValues_scalarWordsWithMode_eq (mode := DecodeMode.legacySolc05)
    (types := [abiUInt256, abiUInt256]) (bytes := o.toList) (cursor := 0)
    (total := 32 * [abiUInt256, abiUInt256].length) (by decide) (by simp), hnone]

/-- The `urns` post-call scratch mem's free-pointer `MLOAD` (`mem[0x40] = 0x80`) survives the
`< 64`-byte return copy (which lands at `0x80`, entirely above `0x40`). Urns analogue of
`catBiteIlksPostCallMem_mload64_short`. -/
private theorem catBiteUrnsPostCallMem_mload64_short (I : ExecutionEnv) {mem : ByteArray}
    (o : ByteArray) {aw : UInt256} (hmem : 196 ≤ mem.size)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hoLt : o.size < 64) (hout : o.size < UInt256.size)
    (haw : 96 ≤ aw.toNat * 32) (hawsz : aw.toNat * 32 < UInt256.size) :
    (if (⟨64⟩ : UInt256).toNat ≥ (catBiteUrnsPostCallMem I mem o).size ∨ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩
        then ⟨0⟩
     else UInt256.ofNat (fromByteArrayBigEndian
       ((catBiteUrnsPostCallMem I mem o).readWithPadding (⟨64⟩ : UInt256).toNat 32))) = ⟨128⟩ := by
  have hbaseSz : (biteUrnsCalldataMem (biteIlkWord I) (biteUrnWord I) mem).size = mem.size :=
    biteUrnsCalldataMem_size hmem
  have hbaseRead : (biteUrnsCalldataMem (biteIlkWord I) (biteUrnWord I) mem).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := biteUrnsCalldataMem_read64 hmem hread64
  have hlen : (min (⟨64⟩ : UInt256) (UInt256.ofNat o.size)).toNat = o.size :=
    umin_ofNat_right_toNat_of_lt (c := 64) (n := o.size) (by decide) hoLt hout
  have hread : (catBiteUrnsPostCallMem I mem o).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
    unfold catBiteUrnsPostCallMem
    rw [hlen, show (⟨128⟩ : UInt256).toNat = 128 from by native_decide]
    rcases Nat.eq_zero_or_pos o.size with h0 | h0
    · rw [h0, byteArray_write_len_zero]; exact hbaseRead
    · rw [write_read_below_gen_extend o (biteUrnsCalldataMem (biteIlkWord I) (biteUrnWord I) mem)
        128 o.size 64 (by omega) (le_refl _) (by rw [hbaseSz]; omega) (by omega)]
      exact hbaseRead
  have hsz : 64 < (catBiteUrnsPostCallMem I mem o).size := by
    unfold catBiteUrnsPostCallMem
    rw [hlen, show (⟨128⟩ : UInt256).toNat = 128 from by native_decide]
    rcases Nat.eq_zero_or_pos o.size with h0 | h0
    · rw [h0, byteArray_write_len_zero, hbaseSz]; omega
    · rw [write_eq_gen o (biteUrnsCalldataMem (biteIlkWord I) (biteUrnWord I) mem)
          128 o.size (by omega) (le_refl _) (by rw [hbaseSz]; omega),
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
/-- **urns return-decode-short branch (extracted).** `ilks` succeeds and decodes; the `urns`
STATICCALL succeeds but returns `< 64` bytes; reach pc 1420, fire `catBiteUrnsDecodeShortLeaf` +
`catBiteSourceUrnsDecodeRevert`. Urns analogue of `catBiteRevertIlksDecode`. -/
theorem catBiteRevertUrnsDecode {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {σ' σu : AccountMap} {A' Au : Substate}
    {cA' cAu : Batteries.RBSet AccountAddress compare} {o' ou : ByteArray} {ku Cu : ℕ}
    {iDust iSpot iRate : UInt256}
    (hcode : I.code = catBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hdispatch : dispatchMsg contract I.calldata = some biteTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (biteTransition.params.map Param.name)
        (transitionSignature biteTransition).paramTypes I.calldata = some (biteLocals I))
    (hAccounts : accountMapEquiv σ_evm σ_solm) (hdepth : (I.depth : ℕ) < 1024)
    (hvatCode :
      ¬ Reasoning.Theory.uniswapExtCodeSizeWord σ_evm (catBiteVatTargetWord σ_evm I) = ⟨0⟩)
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
                  accountMap := σu, substate := Au, createdAccounts := cAu }, ou) false)
    (hilkslen : 160 ≤ o'.size) (hurnsShort : ou.size < 64)
    (hosz : o'.size < UInt256.size) (hoszu : ou.size < UInt256.size)
    (rd1399 : RD catBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1399⟩
      (⟨1⟩ :: ⟨196⟩ :: ⟨606387804⟩ :: UInt256.land (catSlotWord ⟨3⟩ σ' I) biteAddrMaskWord ::
        ⟨0⟩ :: ⟨0⟩ :: iDust :: iSpot :: iRate :: ⟨0⟩ ::
        UInt256.land biteAddrMaskWord (calldataWord I.calldata 36) :: biteIlkWord I ::
        ⟨419⟩ :: catSelWord I :: [])
      (catBiteUrnsPostCallMem I (catBiteIlksPostCallMem I o') ou) ⟨9⟩ ou (cAu, σu) ku Cu) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hdepthNe : I.depth ≠ 1024 := by omega
  obtain ⟨σs, As, σus, Aus, hIlksSolm, hUrnsSolm, _hAmEq, hvatCodeIlkS⟩ :=
    catBiteMapUrns hAccounts hdepthNe hUrnsVatCode hIlksCall hUrnsCall
  obtain ⟨_, _, rd1420⟩ := RD.catBiteUrnsCallSucceeded rd1399 (by decide) (by simp)
  have hmemI : 196 ≤ (catBiteIlksPostCallMem I o').size := by
    have := catBiteIlksPostCallMem_size I o' hilkslen hosz; omega
  have hread64 : (catBiteIlksPostCallMem I o').readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ :=
    catBiteIlksPostCallMem_read64 I o' hilkslen hosz
  exact catBiteUrnsDecodeShortLeaf hcode hdispatch hdecode rd1420 hurnsShort hoszu
    (catBiteUrnsPostCallMem_mload64_short (mem := catBiteIlksPostCallMem I o')
      (aw := (⟨9⟩ : UInt256)) I ou hmemI hread64
      hurnsShort hoszu (by native_decide) (by native_decide))
    (catBiteMloadCost0 (catBiteAwMInv32 (⟨9⟩ : UInt256) (by native_decide)))
    (catBiteAwMInv32 (⟨9⟩ : UInt256) (by native_decide))
    (by simp only [List.length_cons, List.length_nil]; omega)
    (catBiteSourceUrnsDecodeRevert hwv (catBiteVatCodePos_of_uniswap hAccounts hvatCode)
      hIlksSolm (catBiteIlksDecode_ok hilkslen) hvatCodeIlkS hUrnsSolm
      (catBiteUrnsDecode_none hurnsShort))

/-! # Cat `bite` — the integrator walk (`catBiteBodyImpl`)

Fills the vat-has-code spine of `catBiteBody`, chaining the verified reach spine and branching at
each divergence to the imported business/call leaves, feeding the all-success tail to
`catBiteSuccessBranch`. Built incrementally region-core by region-core. -/

set_option maxHeartbeats 4000000 in
theorem catBiteBodyImpl {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = catBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x45, 0xcf, 0x22, 0x30]⟩) (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I ⟨#[0x45, 0xcf, 0x22, 0x30]⟩ rfl hsel
  by_cases hshort : I.calldata.size < 68
  · exact catBiteShort hcode hsize hwv hsz4 hshort hsel hAccounts
  · rw [not_lt] at hshort
    have hsz68 : 68 ≤ I.calldata.size := hshort
    have hsz36 : 36 ≤ I.calldata.size := by omega
    have hdispatch : dispatchMsg contract I.calldata = some biteTransition := catDispatch_bite hsel
    have hdecode :
        decodeCalldataWithMode config.abiDecodeMode (biteTransition.params.map Param.name)
          (transitionSignature biteTransition).paramTypes I.calldata = some (biteLocals I) :=
      biteDecode_ok hsz68
    by_cases hvatCode :
        Reasoning.Theory.uniswapExtCodeSizeWord σ_evm (catBiteVatTargetWord σ_evm I) = ⟨0⟩
    · exact catBiteBodyIlksNoCode hcode hsize hwv hsel hsz68 hAccounts hdispatch hdecode hvatCode
    · -- vat has code. Spine walk begins at the ilks STATICCALL.
      by_cases hdepth : I.depth.val < 1024
      · obtain ⟨cA', σ', z, o', A', awout, k', C', rd1249, hIlksCall, hosz, haw288, hawout9⟩ :=
          catBiteReachPostIlksAw hcode hwv hsz68 hsize hsz36 hsel hvatCode hdepth
        cases z with
        | false =>
            -- ilks STATICCALL returned success = 0.
            exact catBiteBodyIlksFailCore hcode hwv hdispatch hdecode hAccounts hvatCode
              hIlksCall rd1249 hosz (by simp)
        | true =>
            by_cases hilkslen : 160 ≤ o'.size
            · -- ilks decoded OK; STATICCALL urns.
              have hurn :
                  UInt256.land biteAddrMaskWord
                    (UInt256.land biteAddrMaskWord (calldataWord I.calldata 36)) = biteUrnWord I := by
                have hmask : biteAddrMaskWord = solcAddrMask := by native_decide
                have h2 : (2 : ℕ) ^ 160 ≤ UInt256.size := by
                  rw [show UInt256.size = 2 ^ 256 from rfl]
                  exact Nat.pow_le_pow_right (by norm_num) (by norm_num)
                have hval : (AccountAddress.ofNat (calldataWord I.calldata 36).toNat).val
                    = (calldataWord I.calldata 36).toNat % 2 ^ 160 := by
                  unfold AccountAddress.ofNat
                  simp only [Fin.val_ofNat]
                  rw [show AccountAddress.size = 2 ^ 160 from rfl]
                simp only [biteUrnWord, biteUrnAddr, hmask]
                rw [solcAddrMask_clean_left
                  (by rw [u256_land_comm]; exact solcAddrMask_result_canonical _)]
                apply u256_inj
                rw [u256_land_toNat, nat_land_comm,
                  show solcAddrMask.toNat = 2 ^ 160 - 1 from by decide, nat_land_mask_eq_mod,
                  Nat.mod_eq_of_lt (lt_of_lt_of_le (Nat.mod_lt _ (by positivity)) h2),
                  UInt256.toNat_ofNat_of_lt
                    (by rw [hval]; exact lt_of_lt_of_le (Nat.mod_lt _ (by positivity)) h2), hval]
              by_cases hUrnsVatCode :
                  Reasoning.Theory.uniswapExtCodeSizeWord σ'
                    (UInt256.land (catSlotWord ⟨3⟩ σ' I) biteAddrMaskWord) = ⟨0⟩
              · -- urns vat has no code (unreachable: same vat as ilks) — divergence leaf.
                sorry
              · obtain ⟨cAu, σu, zu, ou, Au, ku, Cu, rd1399, hUrnsCall, hoszu⟩ :=
                  catBiteReachPostUrnsAw rd1249 (by decide) hsz36 haw288
                    (by rw [hawout9]; native_decide)
                    (catBiteIlksPostCallMem_size I o' hilkslen hosz).ge
                    hilkslen hosz
                    (catBiteIlksPostCallMem_read64 I o' hilkslen hosz)
                    (catBiteIlksPostCallMem_read160 I o' hilkslen hosz)
                    (catBiteIlksPostCallMem_read192 I o' hilkslen hosz)
                    (catBiteIlksPostCallMem_read256 I o' hilkslen hosz)
                    hurn hUrnsVatCode hdepth
                cases zu with
                | false =>
                    -- urns STATICCALL returned success = 0 → revert leaf.
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
                      have hva : biteVatAddr eI
                          = AccountAddress.ofUInt256 (catBiteVatTargetWord σs I) := by
                        rw [accountAddress_ofUInt256_eq_ofNat_toNat]
                        simp only [biteVatAddr, catBiteVatTargetWord, catAddressReturnWord,
                          catSlotWord, heIam, heIee]
                      rw [hva]
                      refine codePos eI (catBiteVatTargetWord σs I) ?_
                      rw [heIam, show catBiteVatTargetWord σs I
                            = (catSlotWord ⟨3⟩ σs I).land biteAddrMaskWord from by
                          simp only [catBiteVatTargetWord, catAddressReturnWord, hmask],
                        ← hslot3, ← uniswapExtCodeSizeWord_accountMapEquiv hEqIlk.accountMap]
                      exact hUrnsVatCode
                    refine catBiteUrnsFailLeaf hcode hdispatch hdecode rd1399 hoszu
                      (by simp only [List.length_cons, List.length_nil]; omega) ?_
                    exact catBiteSourceUrnsFailRevert hwv
                      (catBiteVatCodePos_of_uniswap hAccounts hvatCode) hIlksSolm
                      (catBiteIlksDecode_ok hilkslen) hvatCodeIlk hUrnsSolm
                | true =>
                    by_cases hurnslen : 64 ≤ ou.size
                    · by_cases hlive : catSlotWord ⟨2⟩ σu I = ⟨1⟩
                      · -- live: reach pc 1521 (Seg3 urns decode + Seg4 live guard).
                        have hse : accountStorageStateEq σ' σu :=
                          typedCallViaEVM_static_accountStorageStateEq hUrnsCall
                        have hslot3 : catSlotWord ⟨3⟩ σ' I = catSlotWord ⟨3⟩ σu I := by
                          simp only [catSlotWord, solcSlotWord]
                          exact accountStorageStateEq_storage_findD hse I.codeOwner ⟨3⟩ ⟨0⟩
                        rw [hslot3] at rd1399
                        have hmemI : (196 : ℕ) ≤ (catBiteIlksPostCallMem I o').size := by
                          have h := catBiteIlksPostCallMem_size I o' hilkslen hosz; omega
                        have hmemUsz : (224 : ℕ) ≤
                            (catBiteUrnsPostCallMem I (catBiteIlksPostCallMem I o') ou).size := by
                          have hbaseSz : (biteUrnsCalldataMem (biteIlkWord I) (biteUrnWord I)
                              (catBiteIlksPostCallMem I o')).size = 288 := by
                            rw [biteUrnsCalldataMem_size hmemI,
                              catBiteIlksPostCallMem_size I o' hilkslen hosz]
                          have hlen64 : ((⟨64⟩ : UInt256) ⊓ UInt256.ofNat ou.size).toNat = 64 :=
                            umin_ofNat_right_toNat_of_ge (c := 64) (n := ou.size) (by decide)
                              hurnslen hoszu
                          unfold catBiteUrnsPostCallMem
                          rw [hlen64, show (⟨128⟩ : UInt256).toNat = 128 from by native_decide,
                            write_eq_gen ou _ 128 64 (by decide) (by omega)
                              (by rw [hbaseSz]; omega),
                            ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
                            ByteArray.size_extract, ByteArray.size_extract, hbaseSz]
                          omega
                        obtain ⟨_, _, rd1521⟩ :=
                          catBiteReach1399to1521 rd1399 (by decide)
                            (by omega) (by rw [hawout9]; native_decide)
                            (le_trans (by norm_num) hmemUsz)
                            hurnslen hoszu
                            (catBiteUrnsPostCallMem_read64 I ou hmemI
                              (catBiteIlksPostCallMem_read64 I o' hilkslen hosz) hurnslen hoszu)
                            (catBiteUrnsPostCallMem_read128 I ou hmemI hurnslen hoszu)
                            (catBiteUrnsPostCallMem_read160 I ou hmemI hurnslen hoszu)
                            hlive
                        -- Seg5 (1521 → 1620): require(spot > 0 && ink*spot < art*rate).
                        set art := UInt256.ofNat (fromByteArrayBigEndian (ou.extract 32 64)) with hart
                        set ink := UInt256.ofNat (fromByteArrayBigEndian (ou.extract 0 32)) with hink
                        set iSpot := UInt256.ofNat (fromByteArrayBigEndian (o'.extract 64 96)) with hiSpot
                        set iRate := UInt256.ofNat (fromByteArrayBigEndian (o'.extract 32 64)) with hiRate
                        by_cases hfitArtRate : art.toNat * iRate.toNat < UInt256.size
                        · by_cases hfitInkSpot : ink.toNat * iSpot.toNat < UInt256.size
                          · by_cases hspotPos : 0 < iSpot.toNat
                            · by_cases hunsafe : (ink * iSpot).toNat < (art * iRate).toNat
                              · obtain ⟨_, _, rd1620⟩ :=
                                  catBiteTraceSeg5 rd1521 hspotPos hfitArtRate hfitInkSpot hunsafe
                                    (by simp)
                                -- Seg6Aw (1620 → 1708): milk-struct alloc + room = box - litter.
                                rw [hawout9] at rd1620
                                have hmf :
                                    (ou.write 0 (biteUrnsCalldataMem (biteIlkWord I) (biteUrnWord I)
                                      (o'.write 0 (catBiteIlksCalldataMem (biteIlkWord I) solcFreePtrMem)
                                        catBiteIlksOutPtr.toNat
                                        (catBiteIlksOutSize ⊓ UInt256.ofNat o'.size).toNat))
                                      (⟨128⟩ : UInt256).toNat
                                      ((⟨64⟩ : UInt256) ⊓ UInt256.ofNat ou.size).toNat)
                                      = catBiteUrnsPostCallMem I (catBiteIlksPostCallMem I o') ou := rfl
                                rw [hmf] at rd1620
                                have h64 : (⟨64⟩ : UInt256).toNat = 64 := by native_decide
                                have h128 : (⟨128⟩ : UInt256).toNat = 128 := by native_decide
                                by_cases hle :
                                    (solcSlotWord σu I ⟨6⟩).toNat ≤ (solcSlotWord σu I ⟨5⟩).toNat
                                · obtain ⟨_, _, rd1708⟩ := catBiteReachSeg6Aw (fp := ⟨128⟩) rd1620
                                    (by native_decide)
                                    (mloadWordValue_of_readWithPadding (off := ⟨64⟩) (v := ⟨128⟩)
                                      (by rw [h64]; have := hmemUsz; omega) (by native_decide)
                                      (catBiteUrnsPostCallMem_read64 I ou hmemI
                                        (catBiteIlksPostCallMem_read64 I o' hilkslen hosz)
                                        hurnslen hoszu))
                                    (catBiteScratchMem_mload64
                                      (catBiteUrnsPostCallMem I (catBiteIlksPostCallMem I o') ou)
                                      ⟨128⟩ (biteIlkWord I)
                                      (by rw [h128]; have := hmemUsz; omega) (by native_decide)
                                      (by native_decide) (by native_decide) (by native_decide))
                                    (catBiteScratchMem_read0_64
                                      (catBiteUrnsPostCallMem I (catBiteIlksPostCallMem I o') ou)
                                      ⟨128⟩ (biteIlkWord I)
                                      (by rw [h128]; have := hmemUsz; omega) (by native_decide))
                                    (by native_decide) (by native_decide) (by native_decide)
                                    hle (by simp)
                                  -- milk-struct field reads (chop@[32+q], dunk@[64+q]).
                                  have hChop := catBiteMilkMem_mload_chop
                                    (catBiteUrnsPostCallMem I (catBiteIlksPostCallMem I o') ou)
                                    ⟨128⟩ (biteIlkWord I) (⟨96⟩ + ⟨128⟩)
                                    (biteAddrMaskWord.land
                                      (solcSlotWord σu I (solcMappingSlot ⟨1⟩ (biteIlkWord I))))
                                    (solcSlotWord σu I (solcMappingSlot ⟨1⟩ (biteIlkWord I) + ⟨1⟩))
                                    (solcSlotWord σu I (solcMappingSlot ⟨1⟩ (biteIlkWord I) + ⟨2⟩))
                                    (aw := ⟨10⟩)
                                    (by rw [h128]; have := hmemUsz; omega) rfl
                                    (by native_decide) (by native_decide)
                                    (by native_decide) (by native_decide)
                                  have hDunk := catBiteMilkMem_mload_dunk
                                    (catBiteUrnsPostCallMem I (catBiteIlksPostCallMem I o') ou)
                                    ⟨128⟩ (biteIlkWord I) (⟨96⟩ + ⟨128⟩)
                                    (biteAddrMaskWord.land
                                      (solcSlotWord σu I (solcMappingSlot ⟨1⟩ (biteIlkWord I))))
                                    (solcSlotWord σu I (solcMappingSlot ⟨1⟩ (biteIlkWord I) + ⟨1⟩))
                                    (solcSlotWord σu I (solcMappingSlot ⟨1⟩ (biteIlkWord I) + ⟨2⟩))
                                    (aw := ⟨10⟩)
                                    (by rw [h128]; have := hmemUsz; omega) rfl
                                    (by native_decide) (by native_decide)
                                    (by native_decide) (by native_decide)
                                  -- name the DSMath chain so the guards are stateable.
                                  set room := (solcSlotWord σu I ⟨5⟩).sub (solcSlotWord σu I ⟨6⟩)
                                    with hroomDef
                                  set milkDunk :=
                                    solcSlotWord σu I (solcMappingSlot ⟨1⟩ (biteIlkWord I) + ⟨2⟩)
                                    with hmilkDunkDef
                                  set milkChop :=
                                    solcSlotWord σu I (solcMappingSlot ⟨1⟩ (biteIlkWord I) + ⟨1⟩)
                                    with hmilkChopDef
                                  set iDust := UInt256.ofNat (fromByteArrayBigEndian (o'.extract 128 160))
                                    with hiDustDef
                                  set dunkRoom :=
                                    (if UInt256.gt milkDunk room = ⟨0⟩ then milkDunk else room)
                                    with hdunkRoomDef
                                  set dunkRoomWad := UInt256.mul dunkRoom ⟨1000000000000000000⟩
                                    with hdunkRoomWadDef
                                  set dartDenomRate := UInt256.div dunkRoomWad iRate with hdartDenomDef
                                  set dartCandidate := UInt256.div dartDenomRate milkChop
                                    with hdartCandDef
                                  set dart :=
                                    (if UInt256.gt art dartCandidate = ⟨0⟩ then art else dartCandidate)
                                    with hdartDef
                                  set inkDart := UInt256.mul ink dart with hinkDartDef
                                  set dinkCandidate := UInt256.div inkDart art with hdinkCandDef
                                  set dink :=
                                    (if UInt256.gt ink dinkCandidate = ⟨0⟩ then ink else dinkCandidate)
                                    with hdinkDef
                                  -- Take the all-guards-hold success path; defer each fail branch.
                                  by_cases hlitterbox :
                                      (solcSlotWord σu I ⟨6⟩).toNat < (solcSlotWord σu I ⟨5⟩).toNat
                                  swap
                                  · sorry -- box ≤ litter: room = 0 / room-require branch
                                  by_cases hroomdust : iDust.toNat ≤ room.toNat
                                  swap
                                  · sorry -- dust > room: require(room ≥ dust) fails
                                  by_cases hRatePos : iRate ≠ ⟨0⟩
                                  swap
                                  · -- rate = 0 unreachable: hunsafe forces art·rate > 0.
                                    exfalso
                                    have hr0 : iRate = ⟨0⟩ := not_not.mp hRatePos
                                    have hz : (art * iRate).toNat = 0 := by
                                      rw [u256_mul_op_toNat, hr0,
                                        show (⟨0⟩ : UInt256).toNat = 0 from rfl, Nat.mul_zero, Nat.zero_mod]
                                    omega
                                  by_cases hChopPos : milkChop ≠ ⟨0⟩
                                  swap
                                  · -- chop = 0: milkChop div-by-zero INVALID (if dunkRoom*WAD fits) / mul-overflow.
                                    by_cases hFitWad : (⟨1000000000000000000⟩ : UInt256).toNat *
                                      dunkRoom.toNat < UInt256.size
                                    · exact catBiteRevertMilkChopZero hcode hwv hdispatch hdecode hAccounts hsz36 hdepth
                                        hvatCode hUrnsVatCode hIlksCall hUrnsCall hilkslen hurnslen hosz hoszu hurn hlive
                                        hmemI hmemUsz (by native_decide) rd1708 hChop hDunk hlitterbox hroomdust hunsafe
                                        hfitArtRate hfitInkSpot hspotPos hRatePos hFitWad (not_not.mp hChopPos)
                                        hart hink hiSpot hiRate hiDustDef hroomDef hmilkDunkDef hmilkChopDef hdunkRoomDef
                                        hdunkRoomWadDef hdartDenomDef
                                    · exact catBiteRevertDunkRoomWad hcode hwv hdispatch hdecode hAccounts hsz36 hdepth
                                        hvatCode hUrnsVatCode hIlksCall hUrnsCall hilkslen hurnslen hosz hoszu hurn hlive
                                        hmemI hmemUsz (by native_decide) rd1708 hChop hDunk hlitterbox hroomdust hunsafe
                                        hfitArtRate hfitInkSpot hspotPos hRatePos hFitWad hart hink hiSpot hiRate hiDustDef
                                        hroomDef hmilkDunkDef hmilkChopDef hdunkRoomDef
                                  by_cases hFitWad : (⟨1000000000000000000⟩ : UInt256).toNat *
                                    dunkRoom.toNat < UInt256.size
                                  swap
                                  · -- dunkRoom*WAD checkedMul overflow: reach pc 3720, mul-overflow revert.
                                    exact catBiteRevertDunkRoomWad hcode hwv hdispatch hdecode hAccounts hsz36 hdepth
                                      hvatCode hUrnsVatCode hIlksCall hUrnsCall hilkslen hurnslen hosz hoszu hurn hlive
                                      hmemI hmemUsz (by native_decide) rd1708 hChop hDunk hlitterbox hroomdust hunsafe
                                      hfitArtRate hfitInkSpot hspotPos hRatePos hFitWad hart hink hiSpot hiRate hiDustDef
                                      hroomDef hmilkDunkDef hmilkChopDef hdunkRoomDef
                                  by_cases hArtPos : art ≠ ⟨0⟩
                                  swap
                                  · -- art = 0 unreachable: hunsafe forces art·rate > 0.
                                    exfalso
                                    have ha0 : art = ⟨0⟩ := not_not.mp hArtPos
                                    have hz : (art * iRate).toNat = 0 := by
                                      rw [u256_mul_op_toNat, ha0,
                                        show (⟨0⟩ : UInt256).toNat = 0 from rfl, Nat.zero_mul, Nat.zero_mod]
                                    omega
                                  by_cases hFitInkDart : dart.toNat * ink.toNat < UInt256.size
                                  swap
                                  · -- ink*dart checkedMul overflow: reach pc 3720, mul-overflow revert.
                                    exact catBiteRevertInkDart hcode hwv hdispatch hdecode hAccounts hsz36 hdepth
                                      hvatCode hUrnsVatCode hIlksCall hUrnsCall hilkslen hurnslen hosz hoszu hurn hlive
                                      hmemI hmemUsz (by native_decide) rd1708 hChop hDunk hlitterbox hroomdust hunsafe
                                      hfitArtRate hfitInkSpot hspotPos hRatePos hChopPos hFitWad hArtPos hFitInkDart
                                      hart hink hiSpot hiRate hiDustDef hroomDef hmilkDunkDef hmilkChopDef hdunkRoomDef
                                      hdunkRoomWadDef hdartDenomDef hdartCandDef hdartDef
                                  by_cases hDartPos : 0 < dart.toNat
                                  swap
                                  · sorry -- dart = 0: require(dart > 0) fails
                                  by_cases hDinkPos : 0 < dink.toNat
                                  swap
                                  · sorry -- dink = 0: require(dink > 0) fails
                                  by_cases hDartLim :
                                      dart.toNat ≤ (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨255⟩).toNat
                                  swap
                                  · sorry -- dart > 2^255: int256 cast bound fails
                                  by_cases hDinkLim :
                                      dink.toNat ≤ (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨255⟩).toNat
                                  swap
                                  · sorry -- dink > 2^255: int256 cast bound fails
                                  obtain ⟨_, _, rd2073⟩ :=
                                    catBiteReach1708to2073 rd1708 hlitterbox hroomdust hChop hDunk
                                      (by native_decide) (by native_decide) hRatePos hChopPos
                                      hdunkRoomDef.symm hFitWad hdunkRoomWadDef.symm
                                      hdartDenomDef.symm hdartCandDef.symm hdartDef.symm hArtPos
                                      hFitInkDart hinkDartDef.symm hdinkCandDef.symm hdinkDef.symm
                                      hDartPos hDinkPos hDartLim hDinkLim
                                  -- === STEP 1: grab CALL reach (pc 2073 → 2193) ===
                                  set base := catBiteUrnsPostCallMem I (catBiteIlksPostCallMem I o') ou
                                  clear_value base
                                  set flipW := biteAddrMaskWord.land
                                    (solcSlotWord σu I (solcMappingSlot ⟨1⟩ (biteIlkWord I)))
                                    with hflipWDef
                                  clear_value flipW
                                  have hthisCanon :
                                      (UInt256.ofNat I.codeOwner.val).toNat < EVM.addressModulus := by
                                    have h2 : (UInt256.ofNat I.codeOwner.val).toNat
                                        = I.codeOwner.val := by
                                      apply UInt256.toNat_ofNat_of_lt
                                      exact lt_of_lt_of_le I.codeOwner.isLt
                                        (show AccountAddress.size ≤ UInt256.size from by decide)
                                    rw [h2]; change I.codeOwner.val < AccountAddress.size
                                    exact I.codeOwner.isLt
                                  -- free pointer of the milk mem: mem[0x40] = q + 96 (q = 96 + 128).
                                  have hMilkFp := catBiteMilkMem_read64 base ⟨128⟩ (biteIlkWord I)
                                    (⟨96⟩ + ⟨128⟩) flipW milkChop milkDunk (by rw [h128]; omega) rfl
                                    (by native_decide) (by native_decide)
                                  have hMilkSz := catBiteMilkMem_size base ⟨128⟩ (biteIlkWord I)
                                    (⟨96⟩ + ⟨128⟩) flipW milkChop milkDunk (by rw [h128]; omega) rfl
                                    (by native_decide) (by native_decide)
                                  have hpmemMilk :
                                      ((⟨96⟩ + ⟨128⟩) + ⟨96⟩ : UInt256).toNat ≤
                                      (catBiteMilkMem base ⟨128⟩ (biteIlkWord I) (⟨96⟩ + ⟨128⟩) flipW
                                        milkChop milkDunk).size := by
                                    rw [hMilkSz,
                                      show ((⟨96⟩ + ⟨128⟩) + ⟨96⟩ : UInt256).toNat = 320 from by
                                        native_decide,
                                      show ((⟨96⟩ + ⟨128⟩ : UInt256).toNat + 96) = 320 from by
                                        native_decide]
                                    exact le_max_right _ _
                                  by_cases hGrabCode :
                                      Reasoning.Theory.uniswapExtCodeSizeWord σu
                                        (UInt256.land (solcSlotWord σu I ⟨3⟩) biteAddrMaskWord) = ⟨0⟩
                                  · sorry -- grab vat has no code → divergence leaf
                                  · obtain ⟨cAg, σg, zg, og, Ag, kg, Cg, rd2193, hGrabCall, hoszg⟩ :=
                                      catBiteReachGrabAw rd2073 hMilkFp (by native_decide) hpmemMilk
                                        (by native_decide) (by native_decide) (by native_decide)
                                        hthisCanon (hDinkLim.trans_eq (by native_decide))
                                        (hDartLim.trans_eq (by native_decide)) hGrabCode hdepth
                                    cases zg with
                                    | false =>
                                      exact catBiteRevertGrabFail hcode hdispatch hdecode hAccounts hwv hperm hsz36 hdepth hurn
                                        hilkslen hurnslen hlive hvatCode hUrnsVatCode hGrabCode hIlksCall hUrnsCall hGrabCall
                                        (by simpa using rd2193) hoszg (by simp only [List.length_cons, List.length_nil]; omega)
                                        hart hink hiSpot hiRate hiDustDef hroomDef hmilkDunkDef hmilkChopDef hdunkRoomDef
                                        hdunkRoomWadDef hdartDenomDef hdartCandDef hdartDef hinkDartDef hdinkCandDef hdinkDef
                                        hspotPos hfitArtRate hfitInkSpot hunsafe hlitterbox hroomdust hRatePos hChopPos hFitWad
                                        hArtPos hFitInkDart hDartPos hDinkPos hDartLim hDinkLim
                                    | true =>
                                      -- === STEP 2: fess CALL reach (pc 2193 → 2300) ===
                                      by_cases hRateFit :
                                          iRate.toNat * dart.toNat < UInt256.size
                                      swap
                                      · -- iRate·dart overflow unreachable: dart ≤ art ⇒ iRate·dart ≤ art·iRate < size.
                                        have hdart_le : dart.toNat ≤ art.toNat := by
                                          rw [hdartDef]; split
                                          · exact le_refl _
                                          · rename_i h
                                            by_contra hc
                                            exact h (ugt_zero (by omega))
                                        exact absurd
                                          (calc iRate.toNat * dart.toNat
                                                ≤ iRate.toNat * art.toNat :=
                                                  Nat.mul_le_mul (Nat.le_refl _) hdart_le
                                              _ = art.toNat * iRate.toNat := Nat.mul_comm _ _
                                              _ < UInt256.size := hfitArtRate)
                                          hRateFit
                                      -- `with_reducible` freezes `MachineState.M` (reducible in this
                                      -- file, unlike BiteBody's section) so the `catBiteAwStepL_toNat`
                                      -- defeq does not unfold M+`UInt256.size` and blow up heartbeats.
                                      have hawF := by
                                        with_reducible
                                          exact catBiteAwStepL_toNat ⟨10⟩
                                            (⟨96⟩ + ⟨128⟩ + ⟨96⟩ + ⟨164⟩ : UInt256).toNat
                                            (catBiteMltL ⟨10⟩
                                              (⟨96⟩ + ⟨128⟩ + ⟨96⟩ + ⟨164⟩ : UInt256).toNat
                                              (by native_decide))
                                      have hGrabSz := catBiteGrabCalldataMemP_size
                                        (⟨96⟩ + ⟨128⟩ + ⟨96⟩) (biteIlkWord I)
                                        (biteAddrMaskWord.land (calldataWord I.calldata 36))
                                        (UInt256.ofNat I.codeOwner.val) (solcSlotWord σu I ⟨4⟩) dink dart
                                        hpmemMilk (by native_decide)
                                      by_cases hFessCode :
                                          Reasoning.Theory.uniswapExtCodeSizeWord σg
                                            (UInt256.land biteAddrMaskWord (solcSlotWord σg I ⟨4⟩)) = ⟨0⟩
                                      · sorry -- fess vow has no code → divergence leaf
                                      · obtain ⟨cAf, σf, zf, ofb, Af, kf, Cf, rd2300, hFessCall, hoszf⟩ :=
                                          catBiteReachFessAw rd2193 (by decide) hRateFit rfl
                                            (by rw [catBiteGrabCalldataMemP_read64 (⟨96⟩ + ⟨128⟩ + ⟨96⟩)
                                                  _ _ _ _ _ _ (by native_decide) hpmemMilk
                                                  (by native_decide)]
                                                exact hMilkFp)
                                            (by native_decide) (le_trans (by native_decide) hGrabSz)
                                            (by rw [hawF]; native_decide) (by rw [hawF]; native_decide)
                                            (by native_decide) hFessCode hdepth
                                        -- STEP A: fess CALL status split.
                                        by_cases hzf : zf = true
                                        swap
                                        · have hzff : zf = false := by simpa using hzf
                                          exact catBiteRevertFessFail hcode hdispatch hdecode hAccounts hwv hperm hsz36 hdepth hurn
                                            hilkslen hurnslen hlive hvatCode hUrnsVatCode hGrabCode hFessCode hIlksCall hUrnsCall
                                            hGrabCall hFessCall (by simpa [hzff] using rd2300) hoszf
                                            (by simp only [List.length_cons, List.length_nil]; omega) hzff hRateFit
                                            hart hink hiSpot hiRate hiDustDef hroomDef hmilkDunkDef hmilkChopDef hdunkRoomDef
                                            hdunkRoomWadDef hdartDenomDef hdartCandDef hdartDef hinkDartDef hdinkCandDef hdinkDef
                                            hspotPos hfitArtRate hfitInkSpot hunsafe hlitterbox hroomdust hRatePos hChopPos hFitWad
                                            hArtPos hFitInkDart hDartPos hDinkPos hDartLim hDinkLim
                                        subst hzf
                                        -- awF (the 2300 active-words) collapses to ⟨17⟩.
                                        have hinner :
                                            (catBiteAwStepL ⟨10⟩
                                              (⟨96⟩ + ⟨128⟩ + ⟨96⟩ + ⟨164⟩ : UInt256).toNat).toNat = 17 := by
                                          rw [hawF]; native_decide
                                        have hawF17 :
                                            (catBiteAwStepL (catBiteAwStepL ⟨10⟩
                                                (⟨96⟩ + ⟨128⟩ + ⟨96⟩ + ⟨164⟩ : UInt256).toNat)
                                              (⟨4⟩ + (⟨96⟩ + ⟨128⟩ + ⟨96⟩) : UInt256).toNat) = ⟨17⟩ := by
                                          apply u256_inj
                                          with_reducible
                                            rw [catBiteAwStepL_toNat _ _ (catBiteMltL _ _ (by native_decide))]
                                          rw [hinner]; native_decide
                                        rw [hawF17] at rd2300
                                        -- Memory-size facts: the fess overlay never shrinks the grab
                                        -- calldata region, so it keeps the `[0, 484)` window the kick
                                        -- calldata build needs (grab already wrote up to `p+164`).
                                        have hwrite_eq : ∀ (a : ByteArray) (w : UInt256) (off : ℕ),
                                            off ≤ a.size →
                                            ((UInt256.toByteArray w).write 0 a off 32).size
                                              = max a.size (off + 32) := fun a w off hoff =>
                                          toByteArray_write32_size_of_le a w off a.size
                                            (max a.size (off + 32)) rfl hoff rfl
                                        have hfess_ge : ∀ (m : ByteArray) (dr : UInt256),
                                            (⟨96⟩ + ⟨128⟩ + ⟨96⟩ : UInt256).toNat ≤ m.size →
                                            m.size ≤ (catBiteFessCalldataMemP (⟨96⟩ + ⟨128⟩ + ⟨96⟩) dr m).size := by
                                          intro m dr hm
                                          unfold catBiteFessCalldataMemP catBiteFessSelMemP
                                          rw [hwrite_eq _ dr (⟨4⟩ + (⟨96⟩ + ⟨128⟩ + ⟨96⟩) : UInt256).toNat
                                              (by rw [hwrite_eq m _ (⟨96⟩ + ⟨128⟩ + ⟨96⟩ : UInt256).toNat hm]
                                                  exact le_trans (by native_decide) (le_max_right _ _)),
                                            hwrite_eq m _ (⟨96⟩ + ⟨128⟩ + ⟨96⟩ : UInt256).toNat hm]
                                          omega
                                        have hgrab_le :
                                            (⟨96⟩ + ⟨128⟩ + ⟨96⟩ : UInt256).toNat ≤ _ :=
                                          le_trans (show (⟨96⟩ + ⟨128⟩ + ⟨96⟩ : UInt256).toNat
                                            ≤ (⟨96⟩ + ⟨128⟩ + ⟨96⟩ + ⟨164⟩ : UInt256).toNat + 32 from by
                                              native_decide) hGrabSz
                                        have hfess_mono := hfess_ge _ (dart.mul iRate) hgrab_le
                                        have hpmem_kick :
                                            (⟨96⟩ + ⟨128⟩ + ⟨96⟩ : UInt256).toNat + 164 ≤ _ :=
                                          le_trans (le_trans (show (⟨96⟩ + ⟨128⟩ + ⟨96⟩ : UInt256).toNat + 164
                                            ≤ (⟨96⟩ + ⟨128⟩ + ⟨96⟩ + ⟨164⟩ : UInt256).toNat + 32 from by
                                              native_decide) hGrabSz) hfess_mono
                                        -- STEP B: name the DSMath tab chain; split the two overflow guards.
                                        set dartRate := UInt256.mul dart iRate with hdartRateDef
                                        set tabBase := UInt256.mul dartRate milkChop with htabBaseDef
                                        set tab := UInt256.div tabBase ⟨1000000000000000000⟩ with htabDef
                                        set litterNew := solcSlotWord σf I ⟨6⟩ + tab with hlitterNewDef
                                        by_cases hChopFit : milkChop.toNat * dartRate.toNat < UInt256.size
                                        swap
                                        · exact catBiteRevertTabBase hcode hdispatch hdecode hAccounts
                                            hwv hperm hsz36 hdepth hurn hilkslen hurnslen hlive hvatCode
                                            hUrnsVatCode hGrabCode hFessCode hIlksCall hUrnsCall hGrabCall
                                            hFessCall rd2300 (by decide)
                                            (by
                                              rw [if_neg (by
                                                    refine not_or.mpr ⟨?_, ?_⟩
                                                    · have e : (⟨32⟩ + (⟨96⟩ + ⟨128⟩) : UInt256).toNat = 256 :=
                                                        by native_decide
                                                      have e2 : (⟨96⟩ + ⟨128⟩ + ⟨96⟩ : UInt256).toNat = 320 :=
                                                        by native_decide
                                                      have := hpmem_kick; omega
                                                    · native_decide),
                                                catBiteFessCalldataMemP_readBelow (⟨96⟩ + ⟨128⟩ + ⟨96⟩) dartRate
                                                  (⟨32⟩ + (⟨96⟩ + ⟨128⟩) : UInt256).toNat (by native_decide)
                                                  hgrab_le (by native_decide),
                                                catBiteGrabCalldataMemP_readBelow (⟨96⟩ + ⟨128⟩ + ⟨96⟩)
                                                  (biteIlkWord I) (biteAddrMaskWord.land (calldataWord I.calldata 36))
                                                  (UInt256.ofNat I.codeOwner.val) (solcSlotWord σu I ⟨4⟩) dink dart
                                                  (⟨32⟩ + (⟨96⟩ + ⟨128⟩) : UInt256).toNat (by native_decide)
                                                  hpmemMilk (by native_decide)]
                                              rw [if_neg (by
                                                    refine not_or.mpr ⟨?_, ?_⟩
                                                    · have e1 : (⟨32⟩ + (⟨96⟩ + ⟨128⟩) : UInt256).toNat = 256 :=
                                                        by native_decide
                                                      have e2 : (⟨96⟩ + ⟨128⟩ + ⟨96⟩ : UInt256).toNat = 320 :=
                                                        by native_decide
                                                      have := hpmemMilk; omega
                                                    · native_decide)] at hChop
                                              exact hChop)
                                            (by native_decide) (by native_decide) hRateFit
                                            hart hink hiSpot hiRate hiDustDef hroomDef hmilkDunkDef
                                            hmilkChopDef hdunkRoomDef hdunkRoomWadDef hdartDenomDef
                                            hdartCandDef hdartDef hinkDartDef hdinkCandDef hdinkDef
                                            hdartRateDef hspotPos hfitArtRate hfitInkSpot hunsafe
                                            hlitterbox hroomdust hRatePos hChopPos hFitWad hArtPos
                                            hFitInkDart hDartPos hDinkPos hDartLim hDinkLim hChopFit
                                        by_cases hLitFit :
                                            (solcSlotWord σf I ⟨6⟩).toNat + tab.toNat < UInt256.size
                                        swap
                                        · sorry -- litter + tab checkedAdd overflow → divergence
                                        -- 2300 → 2383: fess-success guard + tab arithmetic + litter SSTORE.
                                        obtain ⟨_, _, rd2383⟩ :=
                                          catBiteReach2300to2383 (milkChop := milkChop) rd2300 (by decide)
                                            (by
                                              rw [if_neg (by
                                                    refine not_or.mpr ⟨?_, ?_⟩
                                                    · have e : (⟨32⟩ + (⟨96⟩ + ⟨128⟩) : UInt256).toNat = 256 :=
                                                        by native_decide
                                                      have e2 : (⟨96⟩ + ⟨128⟩ + ⟨96⟩ : UInt256).toNat = 320 :=
                                                        by native_decide
                                                      have := hpmem_kick; omega
                                                    · native_decide),
                                                catBiteFessCalldataMemP_readBelow (⟨96⟩ + ⟨128⟩ + ⟨96⟩) dartRate
                                                  (⟨32⟩ + (⟨96⟩ + ⟨128⟩) : UInt256).toNat (by native_decide)
                                                  hgrab_le (by native_decide),
                                                catBiteGrabCalldataMemP_readBelow (⟨96⟩ + ⟨128⟩ + ⟨96⟩)
                                                  (biteIlkWord I) (biteAddrMaskWord.land (calldataWord I.calldata 36))
                                                  (UInt256.ofNat I.codeOwner.val) (solcSlotWord σu I ⟨4⟩) dink dart
                                                  (⟨32⟩ + (⟨96⟩ + ⟨128⟩) : UInt256).toNat (by native_decide)
                                                  hpmemMilk (by native_decide)]
                                              rw [if_neg (by
                                                    refine not_or.mpr ⟨?_, ?_⟩
                                                    · have e1 : (⟨32⟩ + (⟨96⟩ + ⟨128⟩) : UInt256).toNat = 256 :=
                                                        by native_decide
                                                      have e2 : (⟨96⟩ + ⟨128⟩ + ⟨96⟩ : UInt256).toNat = 320 :=
                                                        by native_decide
                                                      have := hpmemMilk; omega
                                                    · native_decide)] at hChop
                                              exact hChop)
                                            (by native_decide) (by native_decide) hperm hRateFit hChopFit hLitFit
                                            hdartRateDef.symm htabBaseDef.symm htabDef.symm hlitterNewDef.symm
                                        -- STEP C: kick CALL reach (2383 → 2532), all at free ptr `p`.
                                        by_cases hKickCode :
                                            Reasoning.Theory.uniswapExtCodeSizeWord
                                              (sstoreAccountMap I.codeOwner σf ⟨6⟩ litterNew)
                                              (UInt256.land biteAddrMaskWord flipW) = ⟨0⟩
                                        · sorry -- kick flip target has no code → divergence leaf
                                        · -- flip@q and free-ptr@64 reads through the fess/grab overlay.
                                          have hFlipRead :
                                              (catBiteFessCalldataMemP (⟨96⟩ + ⟨128⟩ + ⟨96⟩) dartRate
                                                (catBiteGrabCalldataMemP (⟨96⟩ + ⟨128⟩ + ⟨96⟩) (biteIlkWord I)
                                                  (biteAddrMaskWord.land (calldataWord I.calldata 36))
                                                  (UInt256.ofNat I.codeOwner.val) (solcSlotWord σu I ⟨4⟩) dink dart
                                                  (catBiteMilkMem base ⟨128⟩ (biteIlkWord I) (⟨96⟩ + ⟨128⟩) flipW
                                                    milkChop milkDunk))).readWithPadding
                                                (⟨96⟩ + ⟨128⟩ : UInt256).toNat 32
                                                = (flipW : UInt256).toByteArray := by
                                            rw [catBiteFessCalldataMemP_readBelow (⟨96⟩ + ⟨128⟩ + ⟨96⟩) dartRate
                                                  (⟨96⟩ + ⟨128⟩ : UInt256).toNat (by native_decide) hgrab_le
                                                  (by native_decide),
                                                catBiteGrabCalldataMemP_readBelow (⟨96⟩ + ⟨128⟩ + ⟨96⟩)
                                                  (biteIlkWord I) (biteAddrMaskWord.land (calldataWord I.calldata 36))
                                                  (UInt256.ofNat I.codeOwner.val) (solcSlotWord σu I ⟨4⟩) dink dart
                                                  (⟨96⟩ + ⟨128⟩ : UInt256).toNat (by native_decide) hpmemMilk
                                                  (by native_decide),
                                                catBiteMilkMem_readflip base ⟨128⟩ (biteIlkWord I) (⟨96⟩ + ⟨128⟩)
                                                  flipW milkChop milkDunk (by rw [h128]; have := hmemUsz; omega)
                                                  rfl (by native_decide) (by native_decide)]
                                          have hread64F :
                                              (catBiteFessCalldataMemP (⟨96⟩ + ⟨128⟩ + ⟨96⟩) dartRate
                                                (catBiteGrabCalldataMemP (⟨96⟩ + ⟨128⟩ + ⟨96⟩) (biteIlkWord I)
                                                  (biteAddrMaskWord.land (calldataWord I.calldata 36))
                                                  (UInt256.ofNat I.codeOwner.val) (solcSlotWord σu I ⟨4⟩) dink dart
                                                  (catBiteMilkMem base ⟨128⟩ (biteIlkWord I) (⟨96⟩ + ⟨128⟩) flipW
                                                    milkChop milkDunk))).readWithPadding 64 32
                                                = (⟨96⟩ + ⟨128⟩ + ⟨96⟩ : UInt256).toByteArray := by
                                            rw [catBiteFessCalldataMemP_read64 (⟨96⟩ + ⟨128⟩ + ⟨96⟩) dartRate
                                                  (by native_decide) hgrab_le (by native_decide),
                                                catBiteGrabCalldataMemP_read64 (⟨96⟩ + ⟨128⟩ + ⟨96⟩) (biteIlkWord I)
                                                  (biteAddrMaskWord.land (calldataWord I.calldata 36))
                                                  (UInt256.ofNat I.codeOwner.val) (solcSlotWord σu I ⟨4⟩) dink dart
                                                  (by native_decide) hpmemMilk (by native_decide)]
                                            exact hMilkFp
                                          obtain ⟨cAk, σk, zk, ok, Ak, kk, Ck, rd2532, hKickCall, hoszk,
                                              hRDret⟩ :=
                                            catBiteReachKickC rd2383
                                              (mloadWordValue_of_readWithPadding
                                                (lt_of_lt_of_le (show (⟨96⟩ + ⟨128⟩ : UInt256).toNat
                                                  < (⟨96⟩ + ⟨128⟩ + ⟨96⟩ : UInt256).toNat + 164 from by
                                                    native_decide) hpmem_kick)
                                                (by native_decide) hFlipRead)
                                              (mloadWordValue_of_readWithPadding
                                                (lt_of_lt_of_le (show (⟨64⟩ : UInt256).toNat
                                                  < (⟨96⟩ + ⟨128⟩ + ⟨96⟩ : UInt256).toNat + 164 from by
                                                    native_decide) hpmem_kick)
                                                (by native_decide)
                                                (by rw [show (⟨64⟩ : UInt256).toNat = 64 from by native_decide]
                                                    exact hread64F))
                                              hread64F (by native_decide) (by native_decide) (by native_decide)
                                              (by native_decide) (by native_decide) hpmem_kick (by native_decide)
                                              hperm hRateFit hKickCode hdepth
                                          -- STEP D: take the kick-success / long-enough-return branch.
                                          by_cases hzk : zk = true
                                          swap
                                          · have hzkf : zk = false := by simpa using hzk
                                            exact catBiteRevertKickFail hcode hdispatch hdecode hAccounts hwv hperm hsz36 hdepth hurn
                                              hilkslen hurnslen hlive hvatCode hUrnsVatCode hGrabCode hFessCode hKickCode hIlksCall
                                              hUrnsCall hGrabCall hFessCall hKickCall (by simpa [hzkf] using rd2532) hoszk
                                              (by simp only [List.length_cons, List.length_nil]; omega) hzkf hRateFit hflipWDef hdartRateDef
                                              htabBaseDef htabDef hlitterNewDef hChopFit hLitFit hart hink hiSpot hiRate hiDustDef hroomDef
                                              hmilkDunkDef hmilkChopDef hdunkRoomDef hdunkRoomWadDef hdartDenomDef hdartCandDef hdartDef
                                              hinkDartDef hdinkCandDef hdinkDef hspotPos hfitArtRate hfitInkSpot hunsafe hlitterbox hroomdust
                                              hRatePos hChopPos hFitWad hArtPos hFitInkDart hDartPos hDinkPos hDartLim hDinkLim
                                          by_cases hk32 : 32 ≤ ok.size
                                          swap
                                          · -- kick return decode short (returndatasize < 32): all heavy work (free-ptr
                                            -- MLOAD facts + Solm mapping) is inside `catBiteRevertKickDecodeW` (own budget);
                                            -- the walk supplies rd2532/reads by cheap metavar assignment.
                                            exact catBiteRevertKickDecodeW hcode hdispatch hdecode hAccounts hwv hperm hsz36 hdepth
                                              hurn hilkslen hurnslen hlive hvatCode hUrnsVatCode hGrabCode hFessCode hKickCode
                                              hIlksCall hUrnsCall hGrabCall hFessCall hKickCall rd2532 hpmem_kick hread64F
                                              (by native_decide) (by native_decide) (by native_decide) hoszk
                                              (by simp only [List.length_cons, List.length_nil]; omega) hzk (by rw [hzk]; decide)
                                              (by omega) hRateFit hflipWDef hdartRateDef htabBaseDef htabDef hlitterNewDef hChopFit
                                              hLitFit hart hink hiSpot hiRate hiDustDef hroomDef hmilkDunkDef hmilkChopDef
                                              hdunkRoomDef hdunkRoomWadDef hdartDenomDef hdartCandDef hdartDef hinkDartDef
                                              hdinkCandDef hdinkDef hspotPos hfitArtRate hfitInkSpot hunsafe hlitterbox hroomdust
                                              hRatePos hChopPos hFitWad hArtPos hFitInkDart hDartPos hDinkPos hDartLim hDinkLim
                                          have hret := hRDret hzk hk32
                                          have hdepthNe : I.depth ≠ 1024 := by omega
                                          obtain ⟨AU, hUrnsCall'⟩ :=
                                            biteTypedCallZeroSetSubstate hUrnsCall
                                              (by simpa [initState] using hdepthNe) A'
                                          obtain ⟨AG, hGrabCall'⟩ :=
                                            biteTypedCallZeroSetSubstate hGrabCall
                                              (by simpa [initState] using hdepthNe) AU
                                          obtain ⟨AF, hFessCall'⟩ :=
                                            biteTypedCallZeroSetSubstate hFessCall
                                              (by simpa [initState] using hdepthNe) AG
                                          obtain ⟨AK, hKickCall'⟩ :=
                                            biteTypedCallZeroSetSubstate hKickCall
                                              (by simpa [initState] using hdepthNe) AF
                                          set S := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I
                                            with hS
                                          have hbr : ∀ (o : ByteArray) (k : ℕ), k + 32 ≤ o.size →
                                              ABI.bytesToWord ((o.toList.drop k).take 32) =
                                                UInt256.ofNat (fromByteArrayBigEndian
                                                  (o.extract k (k + 32))) := by
                                            intro o k h
                                            rw [decode_word_at_eq_any o k h, uInt256OfByteArray_eq]
                                            congr 1; unfold fromByteArrayBigEndian; congr 1
                                            rw [byteArray_toList_eq (o.readBytes k 32),
                                              readBytes_at_toList_any o k h,
                                              byteArray_toList_eq (o.extract k (k + 32)),
                                              ByteArray.data_extract, Array.toList_extract,
                                              List.extract_eq_take_drop]
                                            simp
                                          have hmask : biteAddrMaskWord = solcAddrMask := by
                                            native_decide
                                          have uminEq : ∀ a b : UInt256,
                                              (if UInt256.gt a b = ⟨0⟩ then a else b) = umin a b := by
                                            intro a b
                                            unfold umin
                                            by_cases h : a.toNat ≤ b.toNat
                                            · rw [if_pos (ugt_zero h), if_pos h]
                                            · rw [if_neg (by rw [ugt_one (by omega)]; decide), if_neg h]
                                          have hposNe : ∀ w : UInt256, w ≠ ⟨0⟩ → 0 < w.toNat :=
                                            fun w hw => Nat.pos_of_ne_zero
                                              (fun h => hw (uint256_toNat_eq_zero h))
                                          have hwad : wadU = ⟨1000000000000000000⟩ := by native_decide
                                          have hsl : (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨255⟩).toNat = 57896044618658097711785492504343953926634992332820282019728792003956564819968 := by native_decide
                                          set eIlk := { S with accountMap := σ', substate := A', createdAccounts := cA' } with heIlk
                                          set eUrn := { S with accountMap := σu, substate := AU, createdAccounts := cAu } with heUrn
                                          set eGrab := { S with accountMap := σg, substate := AG, createdAccounts := cAg } with heGrab
                                          set eFess := { S with accountMap := σf, substate := AF, createdAccounts := cAf } with heFess
                                          set eKick := { S with accountMap := σk, substate := AK, createdAccounts := cAk } with heKick
                                          have heUam : eUrn.accountMap = σu := rfl
                                          have heUee : eUrn.executionEnv = I := rfl
                                          have heFam : eFess.accountMap = σf := rfl
                                          have heFee : eFess.executionEnv = I := rfl
                                          have hboxB : biteBoxW eUrn = solcSlotWord σu I ⟨5⟩ := by
                                            simp only [biteBoxW, catSlotWord, heUam, heUee]
                                          have hlitB : biteLitW eUrn = solcSlotWord σu I ⟨6⟩ := by
                                            simp only [biteLitW, catSlotWord, heUam, heUee]
                                          have hchopB : biteChopW I eUrn = milkChop := by
                                            rw [hmilkChopDef]
                                            simp only [biteChopW, catSlotWord, heUam, heUee,
                                              biteChopSlot, biteFlipSlot_eq hsz36]
                                          have hdunkB : biteDunkW I eUrn = milkDunk := by
                                            rw [hmilkDunkDef]
                                            simp only [biteDunkW, catSlotWord, heUam, heUee,
                                              biteDunkSlot, biteFlipSlot_eq hsz36]
                                          have hroomB : biteRoomV eUrn = room := by
                                            rw [hroomDef]
                                            simp only [biteRoomV, biteBoxW, biteLitW, catSlotWord,
                                              heUam, heUee]
                                          have hdunkroomB : biteDunkRoomV I eUrn = dunkRoom := by
                                            rw [hdunkRoomDef, uminEq milkDunk room]
                                            simp only [biteDunkRoomV, hdunkB, hroomB]
                                          have hdartvB : biteDartV I eUrn iRate art = dart := by
                                            have hcand : biteDartCandV I eUrn iRate = dartCandidate := by
                                              simp only [biteDartCandV, biteDartDenomV,
                                                biteDunkRoomWadV, hchopB, hdunkroomB, hwad,
                                                hdartCandDef, hdartDenomDef, hdunkRoomWadDef]
                                              rfl
                                            rw [hdartDef, uminEq art dartCandidate]
                                            simp only [biteDartV, hcand]
                                          have hdinkvB : biteDinkV I eUrn iRate art ink = dink := by
                                            have hcand :
                                                biteDinkCandV I eUrn iRate art ink = dinkCandidate := by
                                              simp only [biteDinkCandV, biteInkDartV, hdartvB,
                                                hdinkCandDef, hinkDartDef]
                                              rfl
                                            rw [hdinkDef, uminEq ink dinkCandidate]
                                            simp only [biteDinkV, hcand]
                                          have hdartrateB : biteDartRateV I eUrn iRate art = dartRate := by
                                            rw [hdartRateDef]
                                            simp only [biteDartRateV, hdartvB]; rfl
                                          have htabB : biteTabV I eUrn iRate art = tab := by
                                            rw [htabDef, htabBaseDef]
                                            simp only [biteTabV, biteTabBaseV, hdartrateB, hchopB, hwad]
                                            rfl
                                          have hlitFB : biteLitW eFess = solcSlotWord σf I ⟨6⟩ := by
                                            simp only [biteLitW, catSlotWord, heFam, heFee]
                                          have heIam : eIlk.accountMap = σ' := rfl
                                          have heIee : eIlk.executionEnv = I := rfl
                                          have heGam : eGrab.accountMap = σg := rfl
                                          have heGee : eGrab.executionEnv = I := rfl
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
                                          have hbytes :
                                              biteIlkBytes I = EVM.Word.toBytesBE (biteIlkWord I) := by
                                            have hlen32 : (biteIlkBytes I).length = 32 := by
                                              simp only [biteIlkBytes, List.length_take, List.length_drop]
                                              have htlen : I.calldata.toList.length = I.calldata.size := by
                                                rw [byteArray_toList_eq, Array.length_toList]; rfl
                                              rw [htlen]; omega
                                            have hword : ABI.bytesToWord (biteIlkBytes I) = biteIlkWord I := by
                                              simpa [biteIlkBytes, biteIlkWord] using
                                                (decode_word_at_eq_any I.calldata 4 (by simpa using hsz36))
                                            have hto := toBytesBE_bytesToWord_of_length
                                              (bs := biteIlkBytes I) hlen32
                                            rw [hword] at hto; exact hto.symm
                                          have hAddrRT : ∀ a : AccountAddress,
                                              AccountAddress.ofNat (UInt256.ofNat a.val).toNat = a := by
                                            intro a
                                            have h1 : (UInt256.ofNat a.val).toNat = a.val :=
                                              UInt256.toNat_ofNat_of_lt (lt_of_lt_of_le a.isLt
                                                (show AccountAddress.size ≤ UInt256.size from by decide))
                                            rw [h1]; apply Fin.ext
                                            simp only [AccountAddress.ofNat, Fin.ofNat]
                                            exact Nat.mod_eq_of_lt a.isLt
                                          have hlitternew :
                                              biteLitterNewV I eUrn eFess iRate art = litterNew := by
                                            rw [hlitterNewDef]
                                            simp only [biteLitterNewV, hlitFB, htabB]
                                          have hflipAddr : biteFlipAddrV I eUrn =
                                              AccountAddress.ofUInt256 (biteAddrMaskWord.land flipW) := by
                                            rw [accountAddress_ofUInt256_eq_ofNat_toNat, hflipWDef, hmask]
                                            simp only [biteFlipAddrV, catSlotWord, heUam, heUee,
                                              biteFlipSlot_eq hsz36]
                                            rw [solcAddrMask_clean_left
                                              (by rw [u256_land_comm]; exact solcAddrMask_result_canonical _),
                                              u256_land_comm]
                                          refine catBiteSuccessBranch
                                            (evmIlk := eIlk) (evmUrn := eUrn) (evmGrab := eGrab)
                                            (evmFess := eFess) (evmKick := eKick)
                                            (ilksOut := o') (urnsOut := ou) (grabOut := og)
                                            (fessOut := ofb) (kickOut := ok)
                                            (iRate := iRate) (iSpot := iSpot) (iDust := iDust)
                                            (ink := ink) (art := art)
                                            (id := UInt256.ofNat (fromByteArrayBigEndian (ok.extract 0 32)))
                                            (iArt := UInt256.ofNat (fromByteArrayBigEndian (o'.extract 0 32)))
                                            (iLine := UInt256.ofNat (fromByteArrayBigEndian (o'.extract 96 128)))
                                            (acc := (cAk, σk))
                                            (hcode := hcode) (hdispatch := hdispatch) (hdecode := hdecode)
                                            (hAccounts := hAccounts) (hsz36 := hsz36) (hwv := hwv)
                                            (hret := hret) (hcreated := rfl)
                                            (hAccountsFinal := accountMapEquiv_refl σk)
                                            (hLitStore := storageLocStore_uint256 _ ⟨6⟩ _)
                                            (hIlksDec := by
                                              have h := catBiteIlksDecode_ok hilkslen
                                              rw [hbr o' 0 (by omega), hbr o' 32 (by omega),
                                                hbr o' 64 (by omega), hbr o' 96 (by omega),
                                                hbr o' 128 (by omega)] at h
                                              exact h)
                                            (hUrnsDec := by
                                              have h := catBiteUrnsDecode_ok hurnslen
                                              rw [hbr ou 0 (by omega), hbr ou 32 (by omega)] at h
                                              exact h)
                                            (hKickDec := catBiteKickDecode_ok hk32)
                                            (hGrabDec := by simp [config, externalABI, decodeVoid?])
                                            (hFessDec := by simp [config, externalABI, decodeVoid?])
                                            (hfitInkSpot := hfitInkSpot) (hfitArtRate := hfitArtRate)
                                            (hspotPos := hspotPos) (hunsafe := hunsafe)
                                            (hratePos := hposNe iRate hRatePos)
                                            (hartPos := hposNe art hArtPos)
                                            (hlive := by rw [heUam, heUee]; exact hlive)
                                            (hfitDunkRoomWad := by
                                              rw [hdunkroomB, hwad, Nat.mul_comm]; exact hFitWad)
                                            (hfitInkDart := by
                                              rw [hdartvB, Nat.mul_comm]; exact hFitInkDart)
                                            (hfitDartRate := by
                                              rw [hdartvB, Nat.mul_comm]; exact hRateFit)
                                            (hfitTabBase := by
                                              rw [hdartrateB, hchopB, Nat.mul_comm]; exact hChopFit)
                                            (hfitLitterNew := by rw [hlitFB, htabB]; exact hLitFit)
                                            (hmilkChopPos := by rw [hchopB]; exact hposNe milkChop hChopPos)
                                            (hlitLtBox := by rw [hlitB, hboxB]; exact hlitterbox)
                                            (hroomGeDust := by rw [hroomB]; exact hroomdust)
                                            (hdartPos := by rw [hdartvB]; exact hDartPos)
                                            (hdinkPos := by rw [hdinkvB]; exact hDinkPos)
                                            (hdartLim := by
                                              rw [hdartvB]; simp only [int256Limit]
                                              exact Int.ofNat_le.mpr (hDartLim.trans_eq hsl))
                                            (hdinkLim := by
                                              rw [hdinkvB]; simp only [int256Limit]
                                              exact Int.ofNat_le.mpr (hDinkLim.trans_eq hsl))
                                            (hvatCode0 :=
                                              catBiteVatCodePos_of_uniswap (accountMapEquiv_refl σ_evm) hvatCode)
                                            (hIlksCall := by
                                              rw [catBiteVatEvmAddr_eq_target]; exact hIlksCall)
                                            (hvatCodeIlk := by
                                              have haddr : biteVatAddr eIlk =
                                                  AccountAddress.ofUInt256 (catBiteVatTargetWord σ' I) := by
                                                rw [accountAddress_ofUInt256_eq_ofNat_toNat]
                                                simp only [biteVatAddr, catBiteVatTargetWord,
                                                  catAddressReturnWord, catSlotWord, heIam, heIee]
                                              rw [haddr]
                                              refine codePos eIlk (catBiteVatTargetWord σ' I) ?_
                                              have ht : catBiteVatTargetWord σ' I =
                                                  (catSlotWord ⟨3⟩ σ' I).land biteAddrMaskWord := by
                                                simp only [catBiteVatTargetWord, catAddressReturnWord, hmask]
                                              rw [heIam, ht]; exact hUrnsVatCode)
                                            (hUrnsCall := by
                                              have haddr : EVM.address (biteVatAddr eIlk).val =
                                                  AccountAddress.ofUInt256
                                                    ((catSlotWord ⟨3⟩ σ' I).land biteAddrMaskWord) := by
                                                rw [addrId, accountAddress_ofUInt256_eq_ofNat_toNat]
                                                simp only [biteVatAddr, catSlotWord, heIam, heIee, hmask]
                                              rw [haddr]; exact hUrnsCall')
                                            (hvatCodeMid := by
                                              have haddr : biteVatAddr eUrn =
                                                  AccountAddress.ofUInt256 (catBiteVatTargetWord σu I) := by
                                                rw [accountAddress_ofUInt256_eq_ofNat_toNat]
                                                simp only [biteVatAddr, catBiteVatTargetWord,
                                                  catAddressReturnWord, catSlotWord, heUam, heUee]
                                              rw [haddr]
                                              refine codePos eUrn (catBiteVatTargetWord σu I) ?_
                                              have ht : catBiteVatTargetWord σu I =
                                                  (solcSlotWord σu I ⟨3⟩).land biteAddrMaskWord := by
                                                simp only [catBiteVatTargetWord, catAddressReturnWord,
                                                  catSlotWord, hmask]
                                              rw [heUam, ht]; exact hGrabCode)
                                            (hGrabCall := by
                                              rw [hperm] at hGrabCall'
                                              have ht : EVM.address (biteVatAddr eUrn).val =
                                                  AccountAddress.ofUInt256
                                                    ((solcSlotWord σu I ⟨3⟩).land biteAddrMaskWord) := by
                                                rw [addrId, accountAddress_ofUInt256_eq_ofNat_toNat, hmask]
                                                simp only [biteVatAddr, catSlotWord, heUam, heUee]
                                              have h1 : biteIlkVal I =
                                                  Value.fixedBytes bytes32Width
                                                    (EVM.Word.toBytesBE (biteIlkWord I)) := by
                                                simp only [biteIlkVal, hbytes]
                                              have h2 : biteUrnVal I = Value.address (AccountAddress.ofNat
                                                  (biteAddrMaskWord.land
                                                    (biteAddrMaskWord.land (calldataWord I.calldata 36))).toNat) := by
                                                rw [hurn]
                                                simp only [biteUrnVal, biteUrnWord, biteUrnAddr, hAddrRT]
                                              have h3 : (eUrn.executionEnv.codeOwner : AccountAddress) =
                                                  AccountAddress.ofNat (UInt256.ofNat I.codeOwner.val).toNat := by
                                                rw [heUee]; exact (hAddrRT I.codeOwner).symm
                                              have h4 : biteVowAddrV eUrn = AccountAddress.ofNat
                                                  (biteAddrMaskWord.land (solcSlotWord σu I ⟨4⟩)).toNat := by
                                                simp only [biteVowAddrV, catSlotWord, heUam, heUee, hmask]
                                                rw [u256_land_comm]
                                              rw [ht, h1, h2, h3, h4, hdinkvB, hdartvB]
                                              exact hGrabCall')
                                            (hvowCode := by
                                              have haddr : biteVowAddrV eGrab =
                                                  AccountAddress.ofUInt256
                                                    ((solcSlotWord σg I ⟨4⟩).land solcAddrMask) := by
                                                rw [accountAddress_ofUInt256_eq_ofNat_toNat]
                                                simp only [biteVowAddrV, catSlotWord, heGam, heGee]
                                              rw [haddr]
                                              refine codePos eGrab ((solcSlotWord σg I ⟨4⟩).land solcAddrMask) ?_
                                              rw [heGam, u256_land_comm, ← hmask]; exact hFessCode)
                                            (hFessCall := by
                                              have haddr : EVM.address (biteVowAddrV eGrab).val =
                                                  AccountAddress.ofUInt256
                                                    (biteAddrMaskWord.land (solcSlotWord σg I ⟨4⟩)) := by
                                                rw [addrId, accountAddress_ofUInt256_eq_ofNat_toNat,
                                                  hmask, u256_land_comm]
                                                simp only [biteVowAddrV, catSlotWord, heGam, heGee]
                                              rw [hperm] at hFessCall'
                                              rw [haddr, show bw (biteDartRateV I eUrn iRate art) =
                                                Value.int (Int.ofNat dartRate.toNat) from by rw [hdartrateB]]
                                              exact hFessCall')
                                            (hflipCode := by
                                              rw [hflipAddr]
                                              refine codePos _ (biteAddrMaskWord.land flipW) ?_
                                              simp only [storageStore_accountMap, heFam, heFee]
                                              rw [hlitternew]; exact hKickCode)
                                            (hKickCall := by
                                              rw [hzk, hperm] at hKickCall'
                                              have storeFlat : ∀ (ev : EVM.State) (aa : AccountAddress)
                                                  (k v : UInt256), Solm.EVM.storageStore ev aa k v =
                                                    { ev with accountMap := sstoreAccountMap aa ev.accountMap k v } := by
                                                intro ev aa k v
                                                simp only [Solm.EVM.storageStore, sstoreAccountMap, State.lookupAccount]
                                                cases h : ev.accountMap.find? aa with
                                                | none => simp [Option.option]
                                                | some acc => simp [Option.option, State.setAccount, Account.updateStorage]
                                              have hdiv1 : ∀ y : UInt256, UInt256.div y ⟨1⟩ = y := fun y => by
                                                apply u256_inj
                                                rw [udiv_toNat, show (⟨1⟩ : UInt256).toNat = 1 from by native_decide,
                                                  Nat.div_one]
                                              have hexp : UInt256.exp (⟨256⟩ : UInt256) ⟨0⟩ = ⟨1⟩ := by native_decide
                                              have hvowW : ∀ σx : AccountMap,
                                                  UInt256.land (solcSlotWord σx I ⟨4⟩) solcAddrMask = seg8VowM σx I := by
                                                intro σx
                                                simp only [seg8VowM, hmask, hexp, hdiv1]
                                                rw [solcAddrMask_clean_left
                                                  (by rw [u256_land_comm]; exact solcAddrMask_result_canonical _),
                                                  u256_land_comm]
                                              have hvowArg :
                                                  biteVowAddrV (Solm.EVM.storageStore eFess eFess.executionEnv.codeOwner
                                                      ⟨6⟩ litterNew)
                                                    = AccountAddress.ofNat
                                                      (seg8VowM (sstoreAccountMap I.codeOwner σf ⟨6⟩ litterNew) I).toNat := by
                                                simp only [biteVowAddrV, storageStore_accountMap,
                                                  storageStore_executionEnv, heFam, heFee, catSlotWord]
                                                rw [hvowW]
                                              have h2 : biteUrnVal I = Value.address (AccountAddress.ofNat
                                                  (biteAddrMaskWord.land
                                                    (biteAddrMaskWord.land (calldataWord I.calldata 36))).toNat) := by
                                                rw [hurn]
                                                simp only [biteUrnVal, biteUrnWord, biteUrnAddr, hAddrRT]
                                              rw [hlitternew, hvowArg, storeFlat, addrId, hflipAddr, h2, htabB, hdinkvB]
                                              exact hKickCall')
                                · -- room underflow (box < litter): reach pc 3762 at grown aw=10, empty revert.
                                  exact catBiteRevertRoomSub hcode hwv hdispatch hdecode hAccounts hsz36 hdepth
                                    hvatCode hUrnsVatCode hIlksCall hUrnsCall hilkslen hurnslen hosz hoszu hurn
                                    hlive hmemI hmemUsz rd1620 hle hunsafe hfitArtRate hfitInkSpot hspotPos
                                    hart hink hiSpot hiRate rfl
                              · exact catBiteRevertUnsafe hcode hwv hdispatch hdecode hAccounts hsz36 hdepth
                                  hvatCode hUrnsVatCode hIlksCall hUrnsCall hilkslen hosz hurnslen hoszu hurn hlive
                                  rd1521 haw288 (by rw [hawout9]; native_decide) hspotPos hfitArtRate hfitInkSpot
                                  hart hink hiSpot hiRate rfl hunsafe
                            · exact catBiteRevertSpotZero hcode hwv hdispatch hdecode hAccounts hsz36 hdepth
                                hvatCode hUrnsVatCode hIlksCall hUrnsCall hilkslen hosz hurnslen hoszu hurn hlive
                                rd1521 haw288 (by rw [hawout9]; native_decide)
                                (uint256_toNat_eq_zero (Nat.le_zero.mp (Nat.not_lt.mp hspotPos)))
                                hfitArtRate hfitInkSpot hart hink hiSpot hiRate rfl
                          · exact catBiteRevertInkSpot hcode hwv hdispatch hdecode hAccounts hsz36 hdepth
                              hvatCode hUrnsVatCode hIlksCall hUrnsCall hilkslen hurnslen hurn hlive rd1521
                              hfitArtRate hart hink hiSpot hiRate rfl hfitInkSpot
                        · exact catBiteRevertArtRate hcode hwv hdispatch hdecode hAccounts hsz36 hdepth
                            hvatCode hUrnsVatCode hIlksCall hUrnsCall hilkslen hosz hurnslen hoszu hurn hlive
                            rd1521 haw288 (by rw [hawout9]; native_decide) hart hink hiSpot hiRate rfl hfitArtRate
                      · -- require(live == 1) fails → revert leaf.
                        exact catBiteRevertLive hcode hwv hdispatch hdecode hAccounts hsz36 hdepth
                          hvatCode hUrnsVatCode hIlksCall hUrnsCall hilkslen hosz hurnslen hoszu hurn
                          rd1399 (by decide) haw288 (by rw [hawout9]; native_decide) rfl rfl rfl hlive
                    · -- urns return decode short (`returndatasize < 64`).
                      rw [show (if (true = true) then (⟨1⟩ : UInt256) else ⟨0⟩) = (⟨1⟩ : UInt256)
                        from rfl, hawout9] at rd1399
                      exact catBiteRevertUrnsDecode hcode hwv hdispatch hdecode hAccounts hdepth
                        hvatCode hUrnsVatCode hIlksCall hUrnsCall hilkslen (by omega) hosz hoszu rd1399
            · -- ilks return decode short (`returndatasize < 160`).
              exact catBiteRevertIlksDecode hcode hwv hdispatch hdecode hAccounts hvatCode
                hIlksCall rd1249 (by decide) hosz hawout9 hilkslen
      · -- ilks STATICCALL hits the call-depth limit (depth = 1024): STATICCALL returns 0 without
        -- invoking Θ, so the ilks success-guard reverts (both sides), mapped by `catBiteBodyIlksFailCore`.
        have hdepth1024 : I.depth = 1024 := Fin.ext (by have := I.depth.isLt; omega)
        obtain ⟨k, C, rd1163⟩ :=
          catReachBiteRoutine (g := Sat256.ofUInt256 g) hcode hwv hsz68 hsize hsel
        obtain ⟨_, _, rd1233⟩ := RD.catBiteIlksToStaticcallGuard (hR := by simp) rd1163
        obtain ⟨gasWord, _, _, rd1248⟩ := RD.uniswapExtcodesizeGuardOkGas
          (pc := ⟨1233⟩) (okPc := ⟨1245⟩) rd1233 hvatCode
          (by native_decide) (by native_decide) (by native_decide) (by native_decide)
          (by native_decide) (by native_decide) (by native_decide) (by native_decide)
          (by native_decide) (by native_decide) (by simp)
        obtain ⟨_, _, rd1249⟩ :=
          RD.uniswapStaticcallDepthLimit rd1248 (by native_decide) hdepth1024 (by simp)
        have hbytes : biteIlkBytes I = EVM.Word.toBytesBE (biteIlkWord I) := by
          simpa [biteIlkBytes, biteIlkWord, biteUrnsIlkBytes, biteUrnsIlkWord] using
            biteUrnsIlkBytes_eq_toBytesBE (I := I) hsz36
        have hencode : config.externalABI.encode? "ilks" [biteIlkVal I] =
            some ((catBiteIlksCalldataMem (biteIlkWord I) solcFreePtrMem).readWithPadding
              catBiteIlksOutPtr.toNat catBiteIlksInSize.toNat) := by
          simpa [biteIlkVal] using
            catBiteIlksEncode_eq (biteIlkWord I) (biteIlkBytes I) solcFreePtrMem_size hbytes
        have hIlksFailCall :
            typedCallViaEVM config (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
              (AccountAddress.ofUInt256 (catBiteVatTargetWord σ_evm I)) "ilks" 0 [biteIlkVal I]
              (false, _, ByteArray.empty) false :=
          callNotMade_depthLimit hencode (by simpa [initState] using hdepth1024)
        exact catBiteBodyIlksFailCore hcode hwv hdispatch hdecode hAccounts hvatCode
          hIlksFailCall rd1249 (by decide) (by simp)

end Benchmarks.Dss.Cat
