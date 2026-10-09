import Benchmarks.Morpho.MorphoBlue.ErrorRoutines
import Benchmarks.Morpho.MorphoBlue.AdminCommon

/-!
# Morpho `setFeeRecipient(address)`

Per-function proof: calldata decode facts, the EVM trace from the dispatcher arm through the
body, the Solm body evaluation, and the `…Body` theorem `Correct.lean` consumes.
Dispatcher arm entry: pc 717; reach lemma `morphoReachSetFeeRecipientBody`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables

namespace Benchmarks.Morpho.MorphoBlue

set_option maxRecDepth 2000000

def setFeeRecipientArgs (cd : ByteArray) : Store :=
  (∅ : Store).insert "newFeeRecipient" (.address (AccountAddress.ofNat (calldataWord cd 4).toNat))

def setFeeRecipientFrame (v : MorphoImmutables) (cd : ByteArray) : Frame :=
  { contract := contract, locals := (setFeeRecipientArgs cd).insert "__calldata" (.bytes cd),
    immutables := immStore v }

theorem morphoSetFeeRecipientBodySplit (v : MorphoImmutables) (evm : EVM.State)
    (hcv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsize : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (hcanon : (calldataWord evm.executionEnv.calldata 4).toNat < EVM.addressModulus)
    (ho : solcSourceWord evm.executionEnv = solcAddressSlotWord ⟨0⟩ evm.accountMap evm.executionEnv)
    (hne : calldataWord evm.executionEnv.calldata 4 ≠
      solcAddressSlotWord ⟨1⟩ evm.accountMap evm.executionEnv) :
    ExecTransitionBody config contract evm (setFeeRecipientArgs evm.executionEnv.calldata)
      setFeeRecipientTransition.body
      (.returned (setFeeRecipientFrame v evm.executionEnv.calldata)
        (Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨1⟩
          (setAddressOffset0Word (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩)
            (calldataWord evm.executionEnv.calldata 4))) none) (immStore v) ∧
    (evm.executionEnv.perm = false →
      ExecTransitionBody config contract evm (setFeeRecipientArgs evm.executionEnv.calldata)
        setFeeRecipientTransition.body .staticViolation (immStore v)) := by
  exact addressAdminBodySplit v evm (setFeeRecipientArgs evm.executionEnv.calldata)
    "feeRecipient" "newFeeRecipient" "SetFeeRecipient" ⟨1⟩ (calldataWord evm.executionEnv.calldata 4)
    (by simp [addressAdminFrame, setFeeRecipientArgs]) (by simp [addressAdminFrame, setFeeRecipientArgs])
    (by simp only [addressAdminFrame, setFeeRecipientArgs,
      store_get_ne (k := "__calldata") (a := "newFeeRecipient") _ _ (by decide), store_get_self]) rfl rfl hcv hsize hcanon ho hne

theorem morphoSetFeeRecipientBodyRejects (v : MorphoImmutables) (evm : EVM.State)
    (hcv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsize : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (hcanon : (calldataWord evm.executionEnv.calldata 4).toNat < EVM.addressModulus)
    (hbad : solcSourceWord evm.executionEnv ≠ solcAddressSlotWord ⟨0⟩ evm.accountMap evm.executionEnv ∨
      calldataWord evm.executionEnv.calldata 4 =
        solcAddressSlotWord ⟨1⟩ evm.accountMap evm.executionEnv) :
    ExecTransitionBody config contract evm (setFeeRecipientArgs evm.executionEnv.calldata)
      setFeeRecipientTransition.body .reverted (immStore v) := by
  exact addressAdminBodyRejects v evm (setFeeRecipientArgs evm.executionEnv.calldata)
    "feeRecipient" "newFeeRecipient" "SetFeeRecipient" ⟨1⟩ (calldataWord evm.executionEnv.calldata 4)
    (by simp [addressAdminFrame, setFeeRecipientArgs]) (by simp [addressAdminFrame, setFeeRecipientArgs])
    (by simp only [addressAdminFrame, setFeeRecipientArgs,
      store_get_ne (k := "__calldata") (a := "newFeeRecipient") _ _ (by decide), store_get_self]) rfl rfl hcv hsize hcanon hbad

set_option maxRecDepth 10000 in
theorem morphoSetFeeRecipientReachDecode {σ σ₀ A I} {g : Sat256} (v : MorphoImmutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (morphoSelBytes 24))
    (hcv : I.weiValue = ⟨0⟩) (hlen : 36 ≤ I.calldata.size)
    (hbound : I.calldata.size < 2 ^ 255 + 4) :
    ∃ k C, RD (deployedRuntime v) I g (initState σ σ₀ g A I) (UInt256.ofNat 11354)
      [UInt256.ofNat 776, UInt256.ofNat 876, ⟨0⟩]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C := by
  obtain ⟨k, C, rd⟩ := morphoReachSetFeeRecipientBody (g := g) (σ := σ) (σ₀ := σ₀)
    (A := A) v hcode (by omega) hsize hsel
  have rdGuard := morphoBlocks.morpho_block_717_fallthrough
    (immWords := wordsOf (immStore v)) (by decide) hcv rd
  have hcond := solcCalldataStaticLenCheckOk (words := 1) hlen hbound hsize
  have rdCall := morphoBlocks.morpho_block_724_fallthrough
    (immWords := wordsOf (immStore v)) (by decide)
    (by simpa only [wordAddNegFour] using hcond) rdGuard
  have rdDecode := morphoBlocks.morpho_block_766
    (immWords := wordsOf (immStore v)) (by decide)
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) rdCall
  exact ⟨_, _, rdDecode⟩

set_option maxRecDepth 1000 in
theorem morphoSetFeeRecipientReachOwnerCheck {σ σ₀ A I} {g : Sat256} (v : MorphoImmutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (morphoSelBytes 24))
    (hcv : I.weiValue = ⟨0⟩) (hlen : 36 ≤ I.calldata.size)
    (hbound : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (calldataWord I.calldata 4).toNat < EVM.addressModulus) :
    ∃ aw k C, RD (deployedRuntime v) I g (initState σ σ₀ g A I) (UInt256.ofNat 12097)
      [UInt256.eq (solcSourceWord I) (solcAddressSlotWord ⟨0⟩ σ I),
       UInt256.ofNat 128, UInt256.ofNat 848, calldataWord I.calldata 4,
       UInt256.ofNat 115792089237316195423570985007226406215939081747436879206741300988257197096960,
       solcAddrMask, UInt256.ofNat 876, ⟨0⟩]
      (morphoNotOwnerMem solcFreePtrMem) aw ByteArray.empty σ k C := by
  obtain ⟨k, C, rd⟩ := morphoSetFeeRecipientReachDecode (g := g) (σ := σ) (σ₀ := σ₀)
    (A := A) v hcode hsize hsel hcv hlen hbound
  obtain ⟨k', C', rdBody⟩ := morphoDecodeAddress4Ok (v := v) (by simp only [List.length_cons, List.length_nil]; decide)
    (by rw [morphoPatchedValidJumps v]; jump_dest) hcanon rd
  obtain ⟨kb, Cb, rdMessage⟩ := morphoBlocks.morpho_block_776
    (immWords := wordsOf (immStore v)) (by simp only [List.length_cons, List.length_nil]; decide)
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) rdBody
  obtain ⟨aw, km, Cm, rdCheck⟩ := morphoNotOwnerMessage (v := v) (by simp only [List.length_cons, List.length_nil]; decide)
    (by rw [morphoPatchedValidJumps v]; jump_dest) (by native_decide) rdMessage
  have rdRequire := morphoBlocks.morpho_block_585
    (immWords := wordsOf (immStore v)) (by simp only [List.length_cons, List.length_nil]; decide)
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) rdCheck
  have hptr : memLoad (UInt256.ofNat 64) solcFreePtrMem = UInt256.ofNat 128 := solcFreePtrMem_mload64
  exact ⟨_, _, _, by simpa only [morphoBlocks.morpho_block_585_stack, hptr] using rdRequire⟩

set_option maxRecDepth 1000 in
theorem morphoSetFeeRecipientReachChangedCheck {σ σ₀ A I} {g : Sat256} (v : MorphoImmutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (morphoSelBytes 24))
    (hcv : I.weiValue = ⟨0⟩) (hlen : 36 ≤ I.calldata.size)
    (hbound : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (calldataWord I.calldata 4).toNat < EVM.addressModulus)
    (ho : solcSourceWord I = solcAddressSlotWord ⟨0⟩ σ I) :
    ∃ aw k C, RD (deployedRuntime v) I g (initState σ σ₀ g A I) (UInt256.ofNat 12097)
      [UInt256.isZero (UInt256.eq (calldataWord I.calldata 4) (solcAddressSlotWord ⟨1⟩ σ I)),
       UInt256.ofNat 192, UInt256.ofNat 876, solcSlotWordAt ⟨1⟩ σ I,
       UInt256.ofNat 115792089237316195423570985007226406215939081747436879206741300988257197096960,
       calldataWord I.calldata 4, calldataWord I.calldata 4, ⟨0⟩]
      (morphoAlreadySetMem (morphoNotOwnerMem solcFreePtrMem)) aw ByteArray.empty σ k C := by
  obtain ⟨aw, k, C, rd⟩ := morphoSetFeeRecipientReachOwnerCheck (g := g) (σ := σ) (σ₀ := σ₀)
    (A := A) v hcode hsize hsel hcv hlen hbound hcanon
  obtain ⟨kt, Ct, rdNext⟩ := morphoRequireTrue (v := v) (by simp only [List.length_cons, List.length_nil]; decide)
    (by rw [morphoPatchedValidJumps v]; jump_dest)
    (by rw [ho, uInt256_eq_self]; decide) rd
  obtain ⟨kr, Cr, rdMessage⟩ := morphoBlocks.morpho_block_848
    (immWords := wordsOf (immStore v)) (by simp only [List.length_cons, List.length_nil]; decide)
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) rdNext
  obtain ⟨aw', km, Cm, rdCheck⟩ := morphoAlreadySetMessage (v := v) (by simp only [List.length_cons, List.length_nil]; decide)
    (by rw [morphoPatchedValidJumps v]; jump_dest) (by native_decide) rdMessage
  have rdRequire := morphoBlocks.morpho_block_865
    (immWords := wordsOf (immStore v)) (by simp only [List.length_cons, List.length_nil]; decide)
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) rdCheck
  change RD _ _ _ _ _
    [UInt256.isZero (UInt256.eq (UInt256.land (calldataWord I.calldata 4) solcAddrMask)
      (solcAddressSlotWord ⟨1⟩ σ I)), _, _, _, _,
      UInt256.land (calldataWord I.calldata 4) solcAddrMask,
      UInt256.land (calldataWord I.calldata 4) solcAddrMask, _] _ _ _ _ _ _ at rdRequire
  rw [solcAddrMask_clean hcanon] at rdRequire
  have hptr : memLoad (UInt256.ofNat 64) (morphoNotOwnerMem solcFreePtrMem) = UInt256.ofNat 192 := by native_decide
  rw [hptr] at rdRequire
  exact ⟨_, _, _, rdRequire⟩

set_option maxRecDepth 1000 in
theorem morphoSetFeeRecipientXRejects {σ σ₀ A I} {g : Sat256} (v : MorphoImmutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (morphoSelBytes 24))
    (hcv : I.weiValue = ⟨0⟩) (hlen : 36 ≤ I.calldata.size)
    (hbound : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (calldataWord I.calldata 4).toNat < EVM.addressModulus)
    (hbad : solcSourceWord I ≠ solcAddressSlotWord ⟨0⟩ σ I ∨
      calldataWord I.calldata 4 = solcAddressSlotWord ⟨1⟩ σ I) :
    RDrev (deployedRuntime v) g (initState σ σ₀ g A I) := by
  by_cases ho : solcSourceWord I = solcAddressSlotWord ⟨0⟩ σ I
  · obtain ⟨aw, k, C, rd⟩ := morphoSetFeeRecipientReachChangedCheck (g := g) (σ := σ) (σ₀ := σ₀)
      (A := A) v hcode hsize hsel hcv hlen hbound hcanon ho
    have heq := hbad.resolve_left (not_not.mpr ho)
    exact morphoRequireFalseShort (v := v) (by simp)
      (by rw [heq, uInt256_eq_self]; decide) (by native_decide) (by native_decide) rd
  · obtain ⟨aw, k, C, rd⟩ := morphoSetFeeRecipientReachOwnerCheck (g := g) (σ := σ) (σ₀ := σ₀)
      (A := A) v hcode hsize hsel hcv hlen hbound hcanon
    exact morphoRequireFalseShort (v := v) (by simp)
      (u256_eq_of_ne ho) (by native_decide) (by native_decide) rd

set_option maxRecDepth 1000 in
theorem morphoSetFeeRecipientReachStore {σ σ₀ A I} {g : Sat256} (v : MorphoImmutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (morphoSelBytes 24))
    (hcv : I.weiValue = ⟨0⟩) (hlen : 36 ≤ I.calldata.size)
    (hbound : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (calldataWord I.calldata 4).toNat < EVM.addressModulus)
    (ho : solcSourceWord I = solcAddressSlotWord ⟨0⟩ σ I)
    (hne : calldataWord I.calldata 4 ≠ solcAddressSlotWord ⟨1⟩ σ I) :
    ∃ aw k C, RD (deployedRuntime v) I g (initState σ σ₀ g A I) (UInt256.ofNat 876)
      [solcSlotWordAt ⟨1⟩ σ I,
       UInt256.ofNat 115792089237316195423570985007226406215939081747436879206741300988257197096960,
       calldataWord I.calldata 4, calldataWord I.calldata 4, ⟨0⟩]
      (morphoAlreadySetMem (morphoNotOwnerMem solcFreePtrMem)) aw ByteArray.empty σ k C := by
  obtain ⟨aw, k, C, rd⟩ := morphoSetFeeRecipientReachChangedCheck (g := g) (σ := σ) (σ₀ := σ₀)
    (A := A) v hcode hsize hsel hcv hlen hbound hcanon ho
  obtain ⟨k', C', rdStore⟩ := morphoRequireTrue (v := v) (by simp)
    (by rw [morphoPatchedValidJumps v]; jump_dest)
    (by rw [u256_eq_of_ne hne]; decide) rd
  exact ⟨_, _, _, rdStore⟩

set_option maxRecDepth 1000 in
theorem morphoSetFeeRecipientXSplit {σ σ₀ A I} {g : Sat256} (v : MorphoImmutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (morphoSelBytes 24))
    (hcv : I.weiValue = ⟨0⟩) (hlen : 36 ≤ I.calldata.size)
    (hbound : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (calldataWord I.calldata 4).toNat < EVM.addressModulus)
    (ho : solcSourceWord I = solcAddressSlotWord ⟨0⟩ σ I)
    (hne : calldataWord I.calldata 4 ≠ solcAddressSlotWord ⟨1⟩ σ I) :
    (I.perm = true ∧ RDret (deployedRuntime v) g (initState σ σ₀ g A I)
      (sstoreAccountMap I.codeOwner σ ⟨1⟩
        (setAddressOffset0Word (solcSlotWordAt ⟨1⟩ σ I) (calldataWord I.calldata 4))) ByteArray.empty) ∨
    (I.perm = false ∧ RDstatic (deployedRuntime v) g (initState σ σ₀ g A I)) := by
  obtain ⟨aw, k, C, rd⟩ := morphoSetFeeRecipientReachStore (g := g) (σ := σ) (σ₀ := σ₀)
    (A := A) v hcode hsize hsel hcv hlen hbound hcanon ho hne
  by_cases hperm : I.perm = true
  · refine .inl ⟨hperm, ?_⟩
    have hmask : UInt256.lnot solcAddrMask =
        UInt256.ofNat 115792089237316195423570985007226406215939081747436879206741300988257197096960 := by native_decide
    rw [setAddressOffset0Word, hmask, solcAddrMask_clean hcanon]
    simpa only [show (⟨0⟩ : UInt256).toNat = 0 from rfl, byteArray_readWithPadding_zero] using
      morphoBlocks.morpho_block_876 (immWords := wordsOf (immStore v)) (by decide) hperm rd
  · have hp : I.perm = false := Bool.eq_false_of_not_eq_true hperm
    refine .inr ⟨hp, ?_⟩
    have r1 := rd.jumpdest (by
      immutable_decode(immutableLayout, morphoBytecode, wordsOf (immStore v),
        (⟨876⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none,
        morphoBlocks.immutableLayout_inBounds, morphoBlocks.immutableTemplate_size64)) (by evm_ov)
    have r2 := r1.and (by
      immutable_decode(immutableLayout, morphoBytecode, wordsOf (immStore v),
        (⟨877⟩ : UInt256), UInt8.ofNat 22, .AND, none,
        morphoBlocks.immutableLayout_inBounds, morphoBlocks.immutableTemplate_size64)) (by evm_ov)
    have r3 := r2.or (by
      immutable_decode(immutableLayout, morphoBytecode, wordsOf (immStore v),
        (⟨878⟩ : UInt256), UInt8.ofNat 23, .OR, none,
        morphoBlocks.immutableLayout_inBounds, morphoBlocks.immutableTemplate_size64)) (by evm_ov)
    have r4 := r3.push1 (UInt256.ofNat 1) (by
      immutable_decode(immutableLayout, morphoBytecode, wordsOf (immStore v),
        (⟨879⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1),
        morphoBlocks.immutableLayout_inBounds, morphoBlocks.immutableTemplate_size64)) (by evm_ov)
    exact r4.sstoreStatic hp (by
      immutable_decode(immutableLayout, morphoBytecode, wordsOf (immStore v),
        (⟨881⟩ : UInt256), UInt8.ofNat 85, .SSTORE, none,
        morphoBlocks.immutableLayout_inBounds, morphoBlocks.immutableTemplate_size64)) (by evm_ov)

set_option maxRecDepth 10000 in
theorem morphoSetFeeRecipientXReverts {σ σ₀ A I} {g : Sat256} (v : MorphoImmutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (morphoSelBytes 24))
    (hbad : I.weiValue ≠ ⟨0⟩ ∨ I.calldata.size < 36 ∨ 2 ^ 255 + 4 ≤ I.calldata.size) :
    RDrev (deployedRuntime v) g (initState σ σ₀ g A I) := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (morphoSelBytes 24) rfl hsel
  obtain ⟨k, C, rd⟩ := morphoReachSetFeeRecipientBody (g := g) (σ := σ) (σ₀ := σ₀)
    (A := A) v hcode hsz hsize hsel
  have hvalid : (D_J (deployedRuntime v) 0).contains (UInt256.ofNat 440) = true := by
    rw [morphoPatchedValidJumps v]
    jump_dest
  by_cases hcv : I.weiValue = ⟨0⟩
  · have hlen := hbad.resolve_left (not_not.mpr hcv)
    have rdGuard := morphoBlocks.morpho_block_717_fallthrough
      (immWords := wordsOf (immStore v)) (by decide) hcv rd
    have hcond : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) (UInt256.ofNat 32) = ⟨1⟩ := by
      rcases hlen with hshort | hbig
      · exact solcCalldataStaticLenCheckShort (words := 1) hsz hshort hsize (by norm_num)
      · exact solcCalldataStaticLenCheckHuge (words := 1) hbig hsize (by norm_num)
    have rdRevert := morphoBlocks.morpho_block_724_taken
      (immWords := wordsOf (immStore v)) (by decide)
      (by rw [wordAddNegFour, hcond]; decide) hvalid rdGuard
    exact morphoBlocks.morpho_block_440 (immWords := wordsOf (immStore v)) (by decide) rdRevert
  · have rdRevert := morphoBlocks.morpho_block_717_taken
      (immWords := wordsOf (immStore v)) (by decide) hcv hvalid rd
    exact morphoBlocks.morpho_block_440 (immWords := wordsOf (immStore v)) (by decide) rdRevert

set_option maxRecDepth 10000 in
theorem morphoSetFeeRecipientXNoncanonical {σ σ₀ A I} {g : Sat256} (v : MorphoImmutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (morphoSelBytes 24)) (hlen : 36 ≤ I.calldata.size)
    (hbound : I.calldata.size < 2 ^ 255 + 4)
    (hnc : ¬ (calldataWord I.calldata 4).toNat < EVM.addressModulus) :
    RDrev (deployedRuntime v) g (initState σ σ₀ g A I) := by
  by_cases hcv : I.weiValue = ⟨0⟩
  · obtain ⟨k, C, rd⟩ := morphoSetFeeRecipientReachDecode (g := g) (σ := σ) (σ₀ := σ₀)
      (A := A) v hcode hsize hsel hcv hlen hbound
    exact morphoDecodeAddress4Revert (by decide) hnc rd
  · exact morphoSetFeeRecipientXReverts v hcode hsize hsel (.inl hcv)

/-- `setFeeRecipient(address)`: the theorem `Correct.lean` routes selector 24 to. -/
theorem morphoSetFeeRecipientBody {σ σ₀ A I} {g : UInt256} (v : MorphoImmutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (morphoSelBytes 24)) :
    runtimeRefinementFor config contract σ σ₀ g A I (immStore v) := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (morphoSelBytes 24) rfl hsel
  have hd : selectorDispatchMsg contract I.calldata = some setFeeRecipientTransition :=
    morphoSelectorDispatch_of_selIs (by decide) hsel
  by_cases hlen : 36 ≤ I.calldata.size
  · by_cases hbound : I.calldata.size < 2 ^ 255 + 4
    · by_cases hcanon : (calldataWord I.calldata 4).toNat < EVM.addressModulus
      · have hdec : decodeCalldataWithMode config.abiDecodeMode
            (setFeeRecipientTransition.params.map Param.name)
            (transitionSignature setFeeRecipientTransition).paramTypes I.calldata =
            some (setFeeRecipientArgs I.calldata) := decodeCalldata_address_ok hlen hbound hcanon
        by_cases hcv : I.weiValue = ⟨0⟩
        · by_cases ho : solcSourceWord I = solcAddressSlotWord ⟨0⟩ σ I
          · by_cases heq : calldataWord I.calldata 4 = solcAddressSlotWord ⟨1⟩ σ I
            · exact reEquivSelectorRevert hcode
                (morphoSetFeeRecipientXRejects v hcode hsize hsel hcv hlen hbound hcanon (.inr heq)) hd hdec
                (morphoSetFeeRecipientBodyRejects v _ hcv hbound hcanon (.inr heq))
            · have hbody := morphoSetFeeRecipientBodySplit v (initState σ σ₀ (.ofUInt256 g) A I)
                hcv hbound hcanon ho heq
              rcases morphoSetFeeRecipientXSplit (g := .ofUInt256 g) (σ₀ := σ₀) (A := A)
                v hcode hsize hsel hcv hlen hbound hcanon ho heq with ⟨hp, hx⟩ | ⟨hp, hx⟩
              · exact reEquivSelectorExecutionGen hcode hx hd hdec hbody.1
                  (by rw [storageStore_accountMap]; rfl) (.fallthrough rfl rfl (by native_decide))
              · exact reEquivSelectorStatic hcode hx hd hdec (hbody.2 hp)
          · exact reEquivSelectorRevert hcode
              (morphoSetFeeRecipientXRejects v hcode hsize hsel hcv hlen hbound hcanon (.inl ho)) hd hdec
              (morphoSetFeeRecipientBodyRejects v _ hcv hbound hcanon (.inl ho))
        · exact reEquivSelectorRevert hcode
            (morphoSetFeeRecipientXReverts v hcode hsize hsel (.inl hcv)) hd hdec
            (bodyReverts_nonPayable hcv)
      · exact reEquivSelectorDecodingFailed hcode
          (morphoSetFeeRecipientXNoncanonical v hcode hsize hsel hlen hbound hcanon) hd
          (decodeCalldata_address_none_noncanon hlen hbound hcanon)
    · exact reEquivSelectorDecodingFailed hcode
        (morphoSetFeeRecipientXReverts v hcode hsize hsel (.inr (.inr (by omega)))) hd
        (decodeCalldata_address_none_huge (by omega))
  · exact reEquivSelectorDecodingFailed hcode
      (morphoSetFeeRecipientXReverts v hcode hsize hsel (.inr (.inl (by omega)))) hd
      (decodeCalldata_address_none_short hsz (by omega))

end Benchmarks.Morpho.MorphoBlue
