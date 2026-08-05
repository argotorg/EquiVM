/-!
# Pure Identity model

This is the functional model used by the Identity precompile in `evm-semantics`: return the input
byte array unchanged.
-/

namespace Identity

def model (input : ByteArray) : ByteArray := input

@[simp] theorem model_eq (input : ByteArray) : model input = input := rfl

end Identity
