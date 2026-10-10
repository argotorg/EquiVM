import Benchmarks.CompoundIII.Comet.GetterSource
import Benchmarks.CompoundIII.Comet.SelectorRefinement
import Benchmarks.CompoundIII.Comet.SourceSelectors
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_011

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables
open cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

-- LIBRARY CANDIDATE: outcome of a nonpayable getter with a signed calldata-size guard.
def GetterResult (code : ByteArray) (ee : ExecutionEnv) (g : Sat256) (s0 : State)
    (σ : AccountMap) (out : ByteArray) : Prop :=
  if ee.weiValue = ⟨0⟩ ∧ ee.calldata.size < 2 ^ 255 + 4 then
    RDret code g s0 σ out
  else RDrev code g s0

theorem guardedGetter_refines {cfg : Config} {C : ContractDecl} {t : TransitionDecl}
    {imms : Store} {σ σ₀ A I} {g : UInt256} {code out : ByteArray}
    {body : List Stmt} {value : Value} {ty : ABIType}
    (hcode : I.code = code) (hsz : 4 ≤ I.calldata.size)
    (hd : selectorDispatchMsg C I.calldata = some t) (hp : t.params = [])
    (hb : t.body = calldataPrologue body) (ht : t.returnType = [ty])
    (henc : encodeReturnValue? ty value = some out)
    (hsource : I.weiValue = ⟨0⟩ → I.calldata.size < 2 ^ 255 + 4 → ∃ frame,
      ExecTransitionBody cfg C (initState σ σ₀ (Sat256.ofUInt256 g) A I) ∅
        (calldataPrologue body)
        (.returned frame (initState σ σ₀ (Sat256.ofUInt256 g) A I) (some [value])) imms)
    (hX : GetterResult code I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) σ out) :
    runtimeRefinementFor cfg C σ σ₀ g A I imms := by
  have hdec : decodeCalldataWithMode cfg.abiDecodeMode (t.params.map Param.name)
      (transitionSignature t).paramTypes I.calldata = some (∅ : Store) := by
    simpa only [transitionSignature, hp, List.map_nil] using
      (decodeCalldataWithMode_empty_ok (mode := cfg.abiDecodeMode) hsz)
  by_cases hvalue : I.weiValue = ⟨0⟩
  · by_cases hhi : I.calldata.size < 2 ^ 255 + 4
    · simp only [GetterResult, hvalue, hhi, and_self, if_true] at hX
      obtain ⟨frame, hbody⟩ := hsource hvalue hhi
      apply selectorReturn_refines hcode hX hd hdec
      · rw [hb]
        exact hbody
      · rw [ht]
        exact returnEquiv_of_encode henc
    · simp only [GetterResult, hvalue, hhi, and_false, if_false] at hX
      apply selectorRevert_refines hcode hX hd hdec
      rw [hb]
      exact calldataPrologue_huge hvalue hhi
  · simp only [GetterResult, hvalue, false_and, if_false] at hX
    apply selectorRevert_refines hcode hX hd hdec
    rw [hb]
    exact calldataPrologue_nonpayable hvalue

theorem immutableGetter_refines {cfg : Config} {C : ContractDecl} {t : TransitionDecl}
    {imms : Store} {σ σ₀ A I} {g : UInt256} {code out : ByteArray}
    {name : Ident} {value : Value} {ty : ABIType}
    (hcode : I.code = code) (hsz : 4 ≤ I.calldata.size)
    (hd : selectorDispatchMsg C I.calldata = some t) (hp : t.params = [])
    (hb : t.body = calldataPrologue [.return [.immutable name]])
    (ht : t.returnType = [ty]) (hget : imms.get? name = some value)
    (henc : encodeReturnValue? ty value = some out)
    (hX : GetterResult code I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) σ out) :
    runtimeRefinementFor cfg C σ σ₀ g A I imms := by
  apply guardedGetter_refines hcode hsz hd hp hb ht henc ?_ hX
  intro hvalue hhi
  exact ⟨_, immutableGetter_returns hvalue hhi hget⟩

theorem getterLength_ok {size : Nat} (hlo : 4 ≤ size)
    (hhi : size < 2 ^ 255 + 4) (hsize : size < UInt256.size) :
    UInt256.slt (UInt256.lnot ⟨3⟩ + UInt256.ofNat size) ⟨0⟩ = ⟨0⟩ := by
  rw [lnot3_add_returnSize hlo hsize]
  apply slt_lit_zero (by decide)
  · exact Nat.zero_le _
  · rw [ulit_toNat' _ (by omega)]
    omega

theorem getterLength_huge {size : Nat} (hhi : 2 ^ 255 + 4 ≤ size)
    (hsize : size < UInt256.size) :
    UInt256.slt (UInt256.lnot ⟨3⟩ + UInt256.ofNat size) ⟨0⟩ ≠ ⟨0⟩ := by
  have hlo : 4 ≤ size := by omega
  rw [lnot3_add_returnSize hlo hsize]
  have hs : UInt256.slt (UInt256.ofNat (size - 4)) ⟨0⟩ = ⟨1⟩ := by
    apply slt_lit_one_high (by decide)
    rw [ulit_toNat' _ (by omega)]
    omega
  rw [hs]
  decide

theorem getterReturnData (w : UInt256) :
    (w.toByteArray.write 0 solcFreePtrMem
      (memLoad ⟨64⟩ solcFreePtrMem).toNat 32).readWithPadding
        (memLoad ⟨64⟩ solcFreePtrMem).toNat 32 = w.toByteArray := by
  have hload : memLoad ⟨64⟩ solcFreePtrMem = ⟨128⟩ := solcFreePtrMem_mload64
  rw [hload]
  exact solcReturnMem_read128 w

-- LIBRARY CANDIDATE: canonical address cleanup and ABI return encoding.
theorem getterAddressClean (a : AccountAddress) :
    UInt256.land (UInt256.sub (UInt256.shiftLeft ⟨1⟩ ⟨160⟩) ⟨1⟩) (EVM.word a.val) =
      EVM.word a.val := by
  change UInt256.land solcAddrMask (EVM.word a.val) = EVM.word a.val
  rw [u256_land_comm, addressWord_val_clean]

theorem getterAddressEncoding (a : AccountAddress) :
    encodeReturnValue? (.elem .address) (.address a) = some (EVM.word a.val).toByteArray := by
  have hnat : (EVM.word a.val).toNat = a.val :=
    UInt256.toNat_ofNat_of_lt (lt_of_lt_of_le a.isLt (by decide))
  simpa only [addressWord_val_clean, hnat, accountAddress_ofNat_val] using
    solcAddressReturnEncoding rfl (EVM.word a.val)

theorem cometRevert1410 {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem rdata : ByteArray} {aw : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256} (hstack : R.length + 2 ≤ 1024)
    (h : RD (deployedRuntime v) ee g s0 ⟨1410⟩ R mem aw rdata σ k C) :
    RDrev (deployedRuntime v) g s0 :=
  cometWithExtendedAssetList_block_1410 (immWords := wordsOf (immStore v)) hstack h

-- LIBRARY CANDIDATE: ABI bool encoding for an arbitrary word's nonzero test.
theorem nonzeroReturnEncoding (w : UInt256) :
    encodeReturnValue? (.elem .bool) (.bool (decide (w.toNat ≠ 0))) =
      some (UInt256.isZero (UInt256.isZero w)).toByteArray := by
  by_cases hz : w = ⟨0⟩
  · subst w
    exact boolFalseReturnEncoding
  · have hn : w.toNat ≠ 0 := fun h ↦ hz (u256_inj h)
    rw [decide_eq_true hn, isZero_eq_zero_of_ne hz]
    exact boolTrueReturnEncoding

end Benchmarks.CompoundIII.Comet
