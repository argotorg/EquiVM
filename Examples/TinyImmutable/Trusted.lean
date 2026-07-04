import Examples.TinyImmutable.Bytecode
import Reasoning.Dispatch

/-!
# TinyImmutable trusted facts

This file contains the TinyImmutable-local trusted selector facts. These are the only explicit
trusted declarations in the example.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory
open TinyImmutable.Immutables

namespace TinyImmutable

abbrev ownerSelBytes : ByteArray := ⟨#[0x8d, 0xa5, 0xcb, 0x5b]⟩
abbrev quoteSelBytes : ByteArray := ⟨#[0xed, 0x1b, 0xd7, 0x6c]⟩
abbrev scaleSelBytes : ByteArray := ⟨#[0xf5, 0x1e, 0x18, 0x1a]⟩

/-- Selector fact: `keccak256("owner()")[0:4]`. -/
axiom ownerSelectorOf (v : TinyImmutables) :
    selectorOf (ownerTransition v) = ownerSelBytes

/-- Selector fact: `keccak256("quote(uint256)")[0:4]`. -/
axiom quoteSelectorOf (v : TinyImmutables) :
    selectorOf (quoteTransition v) = quoteSelBytes

/-- Selector fact: `keccak256("scale()")[0:4]`. -/
axiom scaleSelectorOf (v : TinyImmutables) :
    selectorOf (scaleTransition v) = scaleSelBytes

end TinyImmutable
