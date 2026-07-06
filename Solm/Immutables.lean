import Solm.Value

/-!
# Immutable / library reference patching

solc leaves each immutable reference as 32 zero bytes in the `--bin-runtime` *template*, and the
constructor splices the concrete value in at each offset that solc reports under
`immutableReferences` in its standard-JSON output (trusted per-benchmark data, same trust class as
selector facts).  `patchRuntime` performs exactly that splice.

`spliceBytes?` is width-agnostic on purpose: the same splice serves 20-byte `linkReferences`
(external-library placeholders); only `patchRuntime`'s outer gate fixes the 32-byte immutable width.
-/

namespace Solm

/-- Overwrite `template[offset : offset + value.size]` with `value`; `none` if it would overrun the
    template (loud, never clamped).  Width-agnostic — used for both 32-byte immutables and 20-byte
    library links. -/
def spliceBytes? (template : ByteArray) (offset : Nat) (value : ByteArray) : Option ByteArray :=
  if offset + value.size ≤ template.size then
    some (template.extract 0 offset ++ value ++ template.extract (offset + value.size) template.size)
  else
    none

/-- Splice each 32-byte immutable `value` into `template` at its `offset`.  `none` if any patch is
    not exactly 32 bytes or would overrun the template. -/
def patchRuntime (template : ByteArray) (patches : List (Nat × ByteArray)) : Option ByteArray :=
  patches.foldlM (fun acc p => if p.2.size = 32 then spliceBytes? acc p.1 p.2 else none) template

-- Splice round-trip on a small array (patch the low / high 32-byte word); out-of-bounds and a
-- non-32-byte patch are both `none`.
#guard patchRuntime (ByteArray.mk (Array.replicate 64 0)) [(0, ByteArray.mk (Array.replicate 32 7))]
  = some (ByteArray.mk (Array.replicate 32 7 ++ Array.replicate 32 0))
#guard patchRuntime (ByteArray.mk (Array.replicate 64 0)) [(32, ByteArray.mk (Array.replicate 32 7))]
  = some (ByteArray.mk (Array.replicate 32 0 ++ Array.replicate 32 7))
#guard patchRuntime (ByteArray.mk (Array.replicate 40 0)) [(16, ByteArray.mk (Array.replicate 32 7))] = none
#guard patchRuntime (ByteArray.mk (Array.replicate 64 0)) [(0, ByteArray.mk (Array.replicate 20 7))] = none

end Solm
