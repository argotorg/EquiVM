import Benchmarks.UniswapV3.Pool.CheckedCastSource
import Benchmarks.UniswapV3.Pool.Routines

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def safeCast160Function : FunctionDecl := contract.functions[50]!

theorem safeCast160Lookup :
    lookupCallable? contract "SafeCast_toUint160" = some safeCast160Function.toCallable := rfl

def safeCast160Locals (y : UInt256) : Store := (∅ : Store).insert "y" (.int (Int.ofNat y.toNat))

def safeCast160Frame (imms : Store) (y : UInt256) : Frame :=
  {contract := contract, locals := safeCast160Locals y, immutables := imms}

def safeCast160ReadyFrame (imms : Store) (y : UInt256) : Frame :=
  checkedCastFrame (safeCast160Frame imms y) "z" (.uint ⟨160, by decide⟩) (Int.ofNat y.toNat)

def safeCast160Valid (y : UInt256) : Prop :=
  normalizeInt (.uint ⟨160, by decide⟩) (Int.ofNat y.toNat) = Int.ofNat y.toNat

theorem safeCast160Bind (y : UInt256) :
    bindParams? safeCast160Function.params [.int (Int.ofNat y.toNat)] =
      some (safeCast160Locals y) := rfl

theorem safeCast160Valid_iff (y : UInt256) : safeCast160Valid y ↔ y.toNat < 2 ^ 160 := by
  rw [safeCast160Valid, normalizeUIntWord_mask ⟨160, by decide⟩ y
    (UInt256.ofNat (2 ^ 160 - 1)) (by decide)]
  constructor
  · intro h
    have hn := Int.ofNat.inj h
    have hb := u256LandMaskToNatLtOfToNat (bits := 160) y (UInt256.ofNat (2 ^ 160 - 1)) (by decide)
    rwa [hn] at hb
  · intro h
    rw [u256LandMaskCleanOfToNat (bits := 160) y (UInt256.ofNat (2 ^ 160 - 1)) (by decide) h]

theorem safeCast160Returns (imms : Store) (evm : EVM.State) (y : UInt256)
    (hy : safeCast160Valid y) :
    ExecFuncBody config (safeCast160Frame imms y) evm safeCast160Function.body
      (.returned (safeCast160ReadyFrame imms y) evm (some [.int (Int.ofNat y.toNat)])) :=
  checkedCastReturns (safeCast160Frame imms y) evm "y" "z" (.uint ⟨160, by decide⟩)
    (Int.ofNat y.toNat) (by decide) Std.HashMap.getElem?_insert_self hy

theorem safeCast160Reverts (imms : Store) (evm : EVM.State) (y : UInt256)
    (hy : ¬safeCast160Valid y) :
    ExecFuncBody config (safeCast160Frame imms y) evm safeCast160Function.body .reverted :=
  checkedCastReverts (safeCast160Frame imms y) evm "y" "z" (.uint ⟨160, by decide⟩)
    (Int.ofNat y.toNat) (by decide) Std.HashMap.getElem?_insert_self hy

end Benchmarks.UniswapV3.Pool
