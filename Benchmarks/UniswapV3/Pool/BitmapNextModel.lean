import Benchmarks.UniswapV3.Pool.BitmapPositionWords
import Benchmarks.UniswapV3.Pool.BitmapStorage
import Benchmarks.UniswapV3.Pool.BitMsbSource
import Benchmarks.UniswapV3.Pool.BitLsbSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def bitmapNextFunction : FunctionDecl := contract.functions[16]!

theorem bitmapNextLookup : lookupCallable? contract "TickBitmap_nextInitializedTickWithinOneWord" =
    some bitmapNextFunction.toCallable := rfl

def bitmapNextLocals (tick spacing : Int) (lte : Bool) : Store :=
  (((∅ : Store).insert "lte" (.bool lte)).insert "tickSpacing" (.int spacing)).insert "tick"
    (.int tick)

def bitmapNextFrame (imms : Store) (tick spacing : Int) (lte : Bool) : Frame :=
  {contract := contract, locals := bitmapNextLocals tick spacing lte, immutables := imms}

theorem bitmapNextBind (tick spacing : Int) (lte : Bool) :
    bindParams? bitmapNextFunction.params [.int tick, .int spacing, .bool lte] =
      some (bitmapNextLocals tick spacing lte) := rfl

def bitmapNextAdjust (tick spacing : Int) : Prop := tick < 0 ∧ tick.tmod spacing ≠ 0

instance (tick spacing : Int) : Decidable (bitmapNextAdjust tick spacing) :=
  inferInstanceAs (Decidable (_ ∧ _))

def bitmapNextCompressed (tick spacing : Int) : Int :=
  if bitmapNextAdjust tick spacing then normalizeInt (.sint ⟨24, by decide⟩) (tick.tdiv spacing - 1)
  else tick.tdiv spacing

def bitmapNextPosition (compressed : Int) (lte : Bool) : Int :=
  if lte then compressed else normalizeInt (.sint ⟨24, by decide⟩) (compressed + 1)

def bitmapNextShift (compressed : Int) (lte : Bool) : UInt256 :=
  UInt256.ofNat (2 ^ (bitmapBitPos (bitmapNextPosition compressed lte)).toNat)

def bitmapNextMask (compressed : Int) (lte : Bool) : UInt256 :=
  if lte then UInt256.sub (bitmapNextShift compressed lte) ⟨1⟩ + bitmapNextShift compressed lte
  else UInt256.lnot (UInt256.sub (bitmapNextShift compressed lte) ⟨1⟩)

def bitmapNextMasked (evm : EVM.State) (compressed : Int) (lte : Bool) : UInt256 :=
  UInt256.land (solcSlotWordAt (bitmapSlot (bitmapWordPos (bitmapNextPosition compressed lte)))
    evm.accountMap evm.executionEnv) (bitmapNextMask compressed lte)

def bitmapNextResult (compressed spacing : Int) (lte : Bool) (masked : UInt256) : Int :=
  let bit := bitmapBitPos (bitmapNextPosition compressed lte)
  let narrow : Int → Int := normalizeInt (.sint ⟨24, by decide⟩)
  let byte : Int → Int := normalizeInt (.uint ⟨8, by decide⟩)
  if lte then
    let distance := if masked = ⟨0⟩ then narrow bit
      else narrow (byte (bit - Int.ofNat (tickLogMsbCount masked)))
    narrow (narrow (compressed - distance) * spacing)
  else
    let distance := if masked = ⟨0⟩ then narrow (byte (255 - bit))
      else narrow (byte (Int.ofNat (bitLsbCount masked) - bit))
    narrow (narrow (narrow (compressed + 1) + distance) * spacing)

end Benchmarks.UniswapV3.Pool
