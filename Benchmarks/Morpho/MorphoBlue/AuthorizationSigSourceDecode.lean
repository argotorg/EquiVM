import Benchmarks.Morpho.MorphoBlue.RawCalldataSource
import Benchmarks.Morpho.MorphoBlue.AuthorizationABI
import Benchmarks.Morpho.MorphoBlue.Fallback

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Morpho.MorphoBlue.Immutables
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

def authorizationSigFrame (cd : ByteArray) (v : MorphoImmutables) : Frame :=
  { contract := contract, locals := fallbackLocals cd, immutables := immStore v }

def authorizationDecodedFrame (cd : ByteArray) (v : MorphoImmutables) : Frame :=
  { authorizationSigFrame cd v with
    locals := (fallbackLocals cd).insert "authorization" (authorizationFromCalldata cd).value }

theorem morphoAuthorizationSigPrelude (evm : EVM.State) (v : MorphoImmutables)
    (hcv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsel : selIs evm.executionEnv (morphoSelBytes 27)) :
    ABlock config evm (authorizationSigFrame evm.executionEnv.calldata v)
      setAuthorizationWithSigTransition.body (authorizationSigFrame evm.executionEnv.calldata v)
      (setAuthorizationWithSigTransition.body.drop 6) := by
  have hs := calldata_size_ge_of_selIs evm.executionEnv (morphoSelBytes 27) rfl hsel
  have he : evm.executionEnv.calldata.extract 0 4 = morphoSelBytes 27 :=
    (byteArray_eq_of_beq hsel).symm
  have hb (i : Nat) (hi : i < 4) :
      evm.executionEnv.calldata[i] = (morphoSelBytes 27)[i]'(by decide +revert) :=
    selectorPrefix_get hi hs he
  have p0 := (ABlock.start (cfg := config) (evm := evm)
    (solm := authorizationSigFrame evm.executionEnv.calldata v)
    (stmts := setAuthorizationWithSigTransition.body)).requireStep (evalCallvalueEq_true hcv)
  have p1 := p0.requireStep (by simpa only [hs, decide_true] using fallbackSize_eval evm v)
  have p2 := p1.requireStep (by
    have h := fallbackByte_eval evm v 0 128 (by omega)
    rw [hb 0 (by decide)] at h
    exact h)
  have p3 := p2.requireStep (by
    have h := fallbackByte_eval evm v 1 105 (by omega)
    rw [hb 1 (by decide)] at h
    exact h)
  have p4 := p3.requireStep (by
    have h := fallbackByte_eval evm v 2 33 (by omega)
    rw [hb 2 (by decide)] at h
    exact h)
  exact p4.requireStep (by
    have h := fallbackByte_eval evm v 3 143 (by omega)
    rw [hb 3 (by decide)] at h
    exact h)

theorem evalAuthorizationDecode (evm : EVM.State) (v : MorphoImmutables)
    (hl : 164 ≤ evm.executionEnv.calldata.size) :
    evalExpr? config (authorizationSigFrame evm.executionEnv.calldata v) evm
      (.abiDecode authorizationABIType (.bytesSlice (.var "__calldata") (.intLit 4) (.intLit 164))) =
      if (authorizationFromCalldata evm.executionEnv.calldata).Canonical then
        .ok (authorizationFromCalldata evm.executionEnv.calldata).value else .revert := by
  have hg : (authorizationSigFrame evm.executionEnv.calldata v).locals.get? "__calldata" =
      some (.bytes evm.executionEnv.calldata) := store_get_self _ _ _
  have hs := evalCalldataSlice (cfg := config) (evm := evm) hg (by decide : 4 ≤ 164) hl
  change evalExpr? config (authorizationSigFrame evm.executionEnv.calldata v) evm
    (.bytesSlice (.var "__calldata") (.intLit 4) (.intLit 164)) = _ at hs
  rw [evalExpr?, hs]
  simp only [bind, EvalResult.bind]
  rw [show config.abiDecodeMode = .modern from rfl, decodeAuthorization _ hl]
  by_cases hc : (authorizationFromCalldata evm.executionEnv.calldata).Canonical <;>
    simp only [hc, ↓reduceIte] <;> rfl

theorem morphoAuthorizationSigBoundsPrelude (evm : EVM.State) (v : MorphoImmutables)
    (hcv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsel : selIs evm.executionEnv (morphoSelBytes 27))
    (hh : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (hl : 164 ≤ evm.executionEnv.calldata.size) :
    ABlock config evm (authorizationSigFrame evm.executionEnv.calldata v)
      setAuthorizationWithSigTransition.body (authorizationSigFrame evm.executionEnv.calldata v)
      (setAuthorizationWithSigTransition.body.drop 8) := by
  have p0 := morphoAuthorizationSigPrelude evm v hcv hsel
  have p1 := p0.requireStep (by
    simpa only [hh, decide_true] using calldataGuard_eval
      (cfg := config) (solm := authorizationSigFrame evm.executionEnv.calldata v)
      (store_get_self _ _ _))
  exact p1.requireStep (by
    simpa only [hl, decide_true] using evalCalldataLengthGe
      (cfg := config) (frame := authorizationSigFrame evm.executionEnv.calldata v) 164
      (store_get_self _ _ _))

theorem morphoAuthorizationSigDecoded (evm : EVM.State) (v : MorphoImmutables)
    (hcv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsel : selIs evm.executionEnv (morphoSelBytes 27))
    (hh : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (hl : 164 ≤ evm.executionEnv.calldata.size)
    (hc : (authorizationFromCalldata evm.executionEnv.calldata).Canonical) :
    ABlock config evm (authorizationSigFrame evm.executionEnv.calldata v)
      setAuthorizationWithSigTransition.body (authorizationDecodedFrame evm.executionEnv.calldata v)
      (setAuthorizationWithSigTransition.body.drop 9) := by
  exact (morphoAuthorizationSigBoundsPrelude evm v hcv hsel hh hl).letStep
    (by simpa only [hc, ↓reduceIte] using evalAuthorizationDecode evm v hl)

def AuthorizationSigBounds (cd : ByteArray) : Prop :=
  260 ≤ cd.size ∧ cd.size < 2 ^ 255 + 4 ∧ (authorizationFromCalldata cd).Canonical

theorem authorizationDecodedFrame_calldata (cd : ByteArray) (v : MorphoImmutables) :
    (authorizationDecodedFrame cd v).locals.get? "__calldata" = some (.bytes cd) := by
  dsimp only [authorizationDecodedFrame]
  rw [store_get_ne _ _ (by decide)]
  exact store_get_self _ _ _

theorem morphoAuthorizationSigSourceDecode (evm : EVM.State) (v : MorphoImmutables)
    (hcv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsel : selIs evm.executionEnv (morphoSelBytes 27))
    (hb : AuthorizationSigBounds evm.executionEnv.calldata) :
    ABlock config evm (authorizationSigFrame evm.executionEnv.calldata v)
      setAuthorizationWithSigTransition.body (authorizationDecodedFrame evm.executionEnv.calldata v)
      (setAuthorizationWithSigTransition.body.drop 10) := by
  exact (morphoAuthorizationSigDecoded evm v hcv hsel hb.2.1 (by have := hb.1; omega)
    hb.2.2).requireStep (by
      simpa only [hb.1, decide_true] using evalCalldataLengthGe
        (cfg := config) (evm := evm) 260
        (authorizationDecodedFrame_calldata evm.executionEnv.calldata v))

theorem morphoAuthorizationSigSourceDecodeRevert (evm : EVM.State) (v : MorphoImmutables)
    (hcv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsel : selIs evm.executionEnv (morphoSelBytes 27))
    (hb : ¬ AuthorizationSigBounds evm.executionEnv.calldata) :
    ExecTransitionBody config contract evm (fallbackLocals evm.executionEnv.calldata)
      setAuthorizationWithSigTransition.body .reverted (immStore v) := by
  apply ExecFuncBody.execBlockRevert
  have p0 := morphoAuthorizationSigPrelude evm v hcv hsel
  have hg := calldataGuard_eval (cfg := config) (evm := evm)
    (solm := authorizationSigFrame evm.executionEnv.calldata v) (store_get_self _ _ _)
  by_cases hh : evm.executionEnv.calldata.size < 2 ^ 255 + 4
  swap
  · exact p0.requireRevert (by simpa only [hh, decide_false] using hg)
  have p1 := p0.requireStep (by simpa only [hh, decide_true] using hg)
  have hl := evalCalldataLengthGe (cfg := config) (evm := evm)
    (frame := authorizationSigFrame evm.executionEnv.calldata v) 164 (store_get_self _ _ _)
  by_cases hs : 164 ≤ evm.executionEnv.calldata.size
  swap
  · exact p1.requireRevert (by simpa only [hs, decide_false] using hl)
  have p2 := p1.requireStep (by simpa only [hs, decide_true] using hl)
  by_cases hc : (authorizationFromCalldata evm.executionEnv.calldata).Canonical
  swap
  · apply p2.run
    exact ExecBlock.consRevert (ExecStmt.letDeclRevert
      (by simpa only [hc, ↓reduceIte] using evalAuthorizationDecode evm v hs))
  have p3 := p2.letStep (by simpa only [hc, ↓reduceIte] using evalAuthorizationDecode evm v hs)
  exact p3.requireRevert (by
    simpa only [show ¬ 260 ≤ evm.executionEnv.calldata.size from fun hx ↦ hb ⟨hx, hh, hc⟩,
      decide_false] using evalCalldataLengthGe (cfg := config) (evm := evm) 260
        (authorizationDecodedFrame_calldata evm.executionEnv.calldata v))

end Benchmarks.Morpho.MorphoBlue
