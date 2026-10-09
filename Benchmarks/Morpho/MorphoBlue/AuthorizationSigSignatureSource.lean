import Benchmarks.Morpho.MorphoBlue.AuthorizationSigDigest
import Benchmarks.Morpho.MorphoBlue.AuthorizationSignatureABI

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

theorem AuthorizationLocals.evalSignature {a cd locals} (hl : AuthorizationLocals a cd locals)
    (imms : Store) (evm : EVM.State) (hs : 260 ≤ cd.size) :
    evalExpr? config { contract := contract, locals := locals, immutables := imms } evm
      (.abiDecode signatureABIType (.bytesSlice (.var "__calldata") (.intLit 164) (.intLit 260))) =
      if (signatureRecoveryWord cd).toNat < 256 then .ok (signatureValue cd) else .revert := by
  have he := evalCalldataSlice (cfg := config) (evm := evm) (frame :=
    { contract := contract, locals := locals, immutables := imms }) hl.calldata (by decide : 164 ≤ 260) hs
  change evalExpr? config { contract := contract, locals := locals, immutables := imms } evm
    (.bytesSlice (.var "__calldata") (.intLit 164) (.intLit 260)) = _ at he
  rw [evalExpr?, he]
  simp only [bind, EvalResult.bind]
  rw [show config.abiDecodeMode = .modern from rfl, decodeSignature cd hs]
  by_cases hv : (signatureRecoveryWord cd).toNat < 256 <;> simp only [hv, ↓reduceIte] <;> rfl

def authorizationSignatureLocals (locals : Store) (cd : ByteArray) : Store :=
  (locals.insert "signature" (signatureValue cd)).insert
    "precompile" (.address (AccountAddress.ofNat 1))

theorem morphoAuthorizationSignatureSource {a cd locals}
    (hl : AuthorizationLocals a cd locals) (imms : Store) (evm : EVM.State)
    (hs : 260 ≤ cd.size) (hv : (signatureRecoveryWord cd).toNat < 256) :
    ABlock config evm { contract := contract, locals := locals, immutables := imms }
      (setAuthorizationWithSigTransition.body.drop 16)
      { contract := contract, locals := authorizationSignatureLocals locals cd, immutables := imms }
      (setAuthorizationWithSigTransition.body.drop 18) := by
  refine (ABlock.start.letStep (by simpa only [hv, ↓reduceIte] using hl.evalSignature imms evm hs)).letStep ?_
  simp only [evalExpr?, bind, EvalResult.bind, pure]
  rfl

theorem morphoAuthorizationSignatureSourceRevert {a cd locals}
    (hl : AuthorizationLocals a cd locals) (imms : Store) (evm : EVM.State)
    (hs : 260 ≤ cd.size) (hv : ¬ (signatureRecoveryWord cd).toNat < 256) :
    ExecBlock config { contract := contract, locals := locals, immutables := imms }
      evm (setAuthorizationWithSigTransition.body.drop 16) .reverted :=
  ExecBlock.consRevert (ExecStmt.letDeclRevert
    (by simpa only [hv, ↓reduceIte] using hl.evalSignature imms evm hs))

end Benchmarks.Morpho.MorphoBlue
