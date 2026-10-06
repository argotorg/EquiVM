import Examples.TinyImmutable.Bytecode
import Reasoning.Immutables

/-!
The contract keeps typed immutable values in its specification. The generated
summaries take a generic key-to-word function; `immutableWords` is the adapter
between the two, and `immutableLayout` comes from the same reference table used
by the constructor patch relation.
-/

open Solm Ethereum Ethereum.EVM Reasoning.Immutables
open TinyImmutable.Immutables

namespace TinyImmutable

/-- Patch sites in the deployed runtime template. -/
def immutableLayout : Layout :=
  ⟨immutableReferences.flatMap (fun (_, key, sites) =>
    sites.map (fun offset => (offset, 32, key)))⟩

/-- Interpret typed contract immutables as the words consumed by generic summaries. -/
def immutableWords (v : TinyImmutables) : String → UInt256
  | "scale" => EVM.wordOfInt (Int.ofNat v.scale.toNat)
  | "owner" => EVM.Word.ofNat (↑v.owner : Nat)
  | _ => ⟨0⟩

end TinyImmutable
