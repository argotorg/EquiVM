import Benchmarks.Dss.Cat.BiteBody

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

namespace Benchmarks.Dss.Cat

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
                    -- urns STATICCALL returned success = 0.
                    sorry
                | true =>
                    -- urns decoded OK; continue the spine (Core 3).
                    sorry
            · -- ilks return decode short (`returndatasize < 160`).
              sorry
      · -- ilks STATICCALL hits the call-depth limit (depth = 1024).
        sorry

end Benchmarks.Dss.Cat
