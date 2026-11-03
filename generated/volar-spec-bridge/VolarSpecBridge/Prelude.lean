import VolarSpecGarble.Verification.ProofObligations
import VolarSpecNative.Generated

/-!
# Bridge prelude (curated): scalar/list transports

The per-struct transports and per-method commutation theorems are generated
by volar's `printer_lean_bridge` (see `VolarSpecBridge.Generated`). This file
is the curated support they reference.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open volar_spec

/-- Transport: Aeneas `U8` → Lean `UInt8`. Exact (the value is < 256). -/
def u8ToUInt8 (x : Std.U8) : UInt8 := UInt8.ofNatLT x.val (by
  have := x.hBounds
  simp [UScalarTy.U8_numBits_eq] at this
  omega)

theorem u8ToUInt8_val (x : Std.U8) : (u8ToUInt8 x).toNat = x.val := by
  simp [u8ToUInt8]

theorem u8ToUInt8_injective : Function.Injective u8ToUInt8 := by
  intro a b h
  apply UScalar.eq_of_val_eq
  have := congrArg UInt8.toNat h
  simpa [u8ToUInt8_val] using this

/-- `u8ToUInt8` is a xor-homomorphism. -/
theorem u8ToUInt8_xor (x y : Std.U8) :
    u8ToUInt8 (x ^^^ y) = u8ToUInt8 x ^^^ u8ToUInt8 y := by
  apply UInt8.toNat_inj.mp
  simp [u8ToUInt8_val, UScalar.val_xor, UInt8.toNat_xor]

/-- `u8ToUInt8` of the Aeneas `U8` default is `0`. -/
theorem u8ToUInt8_default : u8ToUInt8 (default : Std.U8) = 0 := by
  apply UInt8.toNat_inj.mp
  simp [u8ToUInt8_val, UScalar.default_val]

/-- Transport: extracted shim array → native list. -/
def arrToNative {N : Type} (a : array.Array Std.U8 N) : List UInt8 :=
  (vecL a.data).map u8ToUInt8

/-- The `AsRef` dictionary used by all shim-array digest `update` calls. -/
def arrayAsRef {N : Type} (d : vole.VoleArray N Std.U8) :
    core.convert.AsRef (array.Array Std.U8 N) (Slice Std.U8) :=
  core.Shared0T.Insts.CoreConvertAsRef
    (array.Array.Insts.CoreConvertAsRefSlice Std.U8 d.arrayArraySizeInst)


/-- Transport: fixed-size core array of shim arrays → list of lists. -/
def arrFixedToNative {N : Type} {k : Std.Usize}
    (a : Aeneas.Std.Array (array.Array Std.U8 N) k) : List (List UInt8) :=
  (Aeneas.Std.Array.v a).map arrToNative
