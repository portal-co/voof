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
open RustM ControlFlow Error
open volar_spec
open Aeneas.Std.WP

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

/-- `u8ToUInt8` is an and-homomorphism. -/
theorem u8ToUInt8_and (x y : Std.U8) :
    u8ToUInt8 (x &&& y) = u8ToUInt8 x &&& u8ToUInt8 y := by
  apply UInt8.toNat_inj.mp
  simp [u8ToUInt8_val, UScalar.val_and, UInt8.toNat_and]

/-- `u8ToUInt8 1#u8 = 1`. -/
theorem u8ToUInt8_one : u8ToUInt8 (1#u8 : Std.U8) = 1 := by
  apply UInt8.toNat_inj.mp
  simp [u8ToUInt8_val]

/-- Spec of the shim-array index at 0 (used by the and_via_table bridge). -/
theorem shim_index_zero {N : Type} (d : vole.VoleArray N Std.U8)
    (a : volar_spec.array.Array Std.U8 N) (h0 : 0 < (vecL a.data).length) :
    array.Array.Insts.CoreOpsIndexIndexUsizeT.index d.arrayArraySizeInst a 0#usize =
      ok ((vecL a.data)[0]'h0) := by
  have h0v : 0 < a.data.val.length := h0
  have hz : (0#usize : Std.Usize).val = 0 := by decide
  have h0' : (0#usize : Std.Usize).val < a.data.val.length := by omega
  simp only [array.Array.Insts.CoreOpsIndexIndexUsizeT.index,
    alloc.vec.Vec.Insts.CoreOpsIndexIndex.index,
    core.Slice.Insts.CoreOpsIndexIndex.index,
    alloc.vec.Vec.Insts.CoreOpsDerefDerefSlice.deref, alloc.vec.Vec.as_slice,
    rust_primitives.sequence.seq_to_slice,
    core.Usize.Insts.CoreSliceIndexSliceIndexSliceT.get,
    rust_primitives.slice.slice_length,
    rust_primitives.slice.slice_index, Slice.index_usize,
    UScalar.lt_equiv, Slice.len_val, Slice.length, Slice.getElem?_Usize_eq,
    eq_true h0',
    decide_true, ↓reduceIte, getElem?_pos, spec_ok, bind_tc_ok]
  rfl

/-- The and_via_table index prefix: peel the two bit-test ifs with a
higher-order continuation (Miller pattern in `i2 i5`). -/
theorem table_sel_prefix {α : Type} (x y : Std.U8) (CONT : Std.Usize → Std.Usize → RustM α) :
    (do let i2 ← if x = 1#u8 then ok (1#usize : Std.Usize) else ok 0#usize
        let i5 ← if y = 1#u8 then ok (2#usize : Std.Usize) else ok 0#usize
        CONT i2 i5) =
    CONT (if x = 1#u8 then (1#usize : Std.Usize) else 0#usize)
         (if y = 1#u8 then (2#usize : Std.Usize) else 0#usize) := by
  by_cases h1 : x = 1#u8 <;> by_cases h2 : y = 1#u8 <;>
    simp [h1, h2, Bind.bind, Aeneas.Std.bind]

/-- The extracted and_via_table index value, as a Nat expression. -/
theorem table_sel_index_val (b1 b2 : Std.U8) :
    ((if b1 = 1#u8 then (1#usize : Std.Usize) else 0#usize) |||
     (if b2 = 1#u8 then (2#usize : Std.Usize) else 0#usize)).val =
    (if b1 = 1#u8 then 1 else 0) ||| (if b2 = 1#u8 then 2 else 0) := by
  by_cases h1 : b1 = 1#u8 <;> by_cases h2 : b2 = 1#u8 <;> simp [h1, h2, UScalar.val_or]

/-- The and_via_table index is always in-bounds for the 4-row table. -/
theorem table_sel_index_lt4 (b1 b2 : Std.U8) :
    ((if b1 = 1#u8 then (1#usize : Std.Usize) else 0#usize) |||
     (if b2 = 1#u8 then (2#usize : Std.Usize) else 0#usize)).val < 4 := by
  rw [table_sel_index_val]
  by_cases h1 : b1 = 1#u8 <;> by_cases h2 : b2 = 1#u8 <;> simp [h1, h2]
