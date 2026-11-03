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

/-- `u8ToUInt8` is an or-homomorphism. -/
theorem u8ToUInt8_or (x y : Std.U8) :
    u8ToUInt8 (x ||| y) = u8ToUInt8 x ||| u8ToUInt8 y := by
  apply UInt8.toNat_inj.mp
  simp [u8ToUInt8_val, UScalar.val_or, UInt8.toNat_or]

/-- `map u8ToUInt8` commutes with `List.set`. -/
theorem map_set_u8 (l : List Std.U8) (i : Nat) (x : Std.U8) :
    (l.set i x).map u8ToUInt8 = (l.map u8ToUInt8).set i (u8ToUInt8 x) := by
  induction l generalizing i with
  | nil => rfl
  | cons a l ih =>
    cases i with
    | zero => rfl
    | succ i =>
      show (u8ToUInt8 a :: (l.set i x).map u8ToUInt8) = u8ToUInt8 a :: (l.map u8ToUInt8).set i (u8ToUInt8 x)
      rw [ih]

/-! ## Native-side bit-pack machinery (`to_share`)

The native `to_share` emits an `Id.run` for-in loop over `[0:8]`, which is
definitionally a `List.foldl` over `List.range' 0 8`; `bitPack_transport`
transports the extracted `bitPackBvFrom` (curated in ProofObligations) to it.
-/
/-- the native inner loop is the foldl form. -/
theorem to_share_inner_native (l : List UInt8) (i : Nat) :
    (Id.run do
      let mut v := (0 : UInt8)
      for h : j in [(0):(8)] do
        let bit := (l[((i * (8)) + j)]! &&& ((1) : UInt8))
        v := v ||| (bit <<< (j).toUInt8)
      return v) =
    List.foldl (fun b a => b ||| (((l[i * 8 + a]?.getD default) &&& 1) <<< UInt8.ofNat a))
      0 (List.range' 0 8) := by
  simp

/-- u8ToUInt8 of a BitVec-constructed U8. -/
theorem u8ToUInt8_mk (bv : BitVec 8) :
    u8ToUInt8 (⟨bv⟩ : Std.U8) = UInt8.ofBitVec bv := by
  apply UInt8.toNat_inj.mp
  show ((⟨bv⟩ : Std.U8)).bv.toNat = bv.toNat
  rfl

/-- u8ToUInt8 distributes over BitVec-or of mk's. -/
theorem u8ToUInt8_mk_or (a b : BitVec 8) :
    u8ToUInt8 (⟨a ||| b⟩ : Std.U8) = u8ToUInt8 ⟨a⟩ ||| u8ToUInt8 ⟨b⟩ := by
  apply UInt8.toNat_inj.mp
  show (a ||| b).toNat = (a.toNat ||| b.toNat : Nat)
  exact BitVec.toNat_or a b

/-- u8ToUInt8 distributes over BitVec-shift-left by a small Nat. -/
theorem u8ToUInt8_mk_shl (bv : BitVec 8) (s : Nat) (hs : s < 8) :
    u8ToUInt8 (⟨bv <<< s⟩ : Std.U8) = u8ToUInt8 ⟨bv⟩ <<< UInt8.ofNat s := by
  apply UInt8.toNat_inj.mp
  show (bv <<< s).toNat = (UInt8.ofBitVec bv <<< UInt8.ofNat s).toBitVec.toNat
  rw [BitVec.toNat_shiftLeft]
  show (bv.toNat <<< s) % 256 = (bv <<< ((UInt8.mod (UInt8.ofNat s) 8).toBitVec.toNat)).toNat
  rw [BitVec.toNat_shiftLeft]
  have h8 : (UInt8.mod (UInt8.ofNat s) 8).toBitVec.toNat = s := by
    simp [UInt8.mod, UInt8.ofNat, UInt8.toNat, UInt8.toBitVec]
    sorry
  rw [h8]

/-- map-getD: the mapped in-range-or-default read. -/
theorem map_getD_u8 (l : List Std.U8) (k : Nat) :
    ((l.map u8ToUInt8)[k]?.getD default) = u8ToUInt8 (l[k]!) := by
  cases h : l[k]? with
  | none =>
    simp [h]
    simp [u8ToUInt8_default]
    rfl
  | some x =>
    simp [h]

/-- u8ToUInt8 of a small shift, Std.U8-level form. -/
theorem u8ToUInt8_shl (x : Std.U8) (s : Nat) (hs : s < 8) :
    u8ToUInt8 (⟨x.bv <<< s⟩ : Std.U8) = (u8ToUInt8 x) <<< UInt8.ofNat s :=
  u8ToUInt8_mk_shl x.bv s hs

/-- the foldl bit-pack equals the transported extracted bit-pack. -/
theorem bitPack_transport (ln : List UInt8) (l : List Std.U8) (hl : ln = l.map u8ToUInt8) (i : Nat) :
    ∀ (k s : Nat) (v : Std.U8), 8 - s = k →
    List.foldl (fun b a => b ||| (((ln[i * 8 + a]?.getD default) &&& 1) <<< UInt8.ofNat a))
        (u8ToUInt8 v) (List.range' s k)
    = u8ToUInt8 ⟨bitPackBvFrom l i s v.bv⟩ := by
  intro k
  induction k with
  | zero =>
    intro s v hk
    have hs : ¬ s < 8 := by omega
    have h1 : List.range' s 0 = [] := rfl
    rw [h1]
    show u8ToUInt8 v = u8ToUInt8 ⟨bitPackBvFrom l i s v.bv⟩
    congr 1
    rw [show bitPackBvFrom l i s v.bv = v.bv from by rw [bitPackBvFrom.eq_def]; rw [if_neg hs]]
  | succ k ih =>
    intro s v hk
    have hs : s < 8 := by omega
    have hk' : 8 - (s + 1) = k := by omega
    rw [List.range'_succ]
    rw [List.foldl_cons]
    show (List.foldl (fun b a => b ||| (((ln[i * 8 + a]?.getD default) &&& 1) <<< UInt8.ofNat a))
        (u8ToUInt8 v ||| (((ln[i * 8 + s]?.getD default) &&& 1) <<< UInt8.ofNat s))
        (List.range' (s + 1) k)) = _
    have hbyte : (u8ToUInt8 v) ||| (((ln[i * 8 + s]?.getD default) &&& 1) <<< UInt8.ofNat s)
        = u8ToUInt8 (v ||| ⟨(l[i * 8 + s]! &&& 1#u8).bv <<< s⟩) := by
      rw [hl, map_getD_u8]
      have h1 : (u8ToUInt8 (l[i * 8 + s]!) &&& 1) = u8ToUInt8 (l[i * 8 + s]! &&& 1#u8) := by
        rw [← u8ToUInt8_one, ← u8ToUInt8_and]
      rw [h1]
      rw [← u8ToUInt8_shl _ s hs]
      rw [← u8ToUInt8_or]
    rw [hbyte]
    have hstep : bitPackBvFrom l i s v.bv = bitPackBvFrom l i (s + 1) (v.bv ||| ((l[i * 8 + s]! &&& 1#u8).bv <<< s)) := by
      rw [bitPackBvFrom.eq_def]
      rw [if_pos hs]
    rw [hstep]
    exact ih (s + 1) ⟨v.bv ||| ((l[i * 8 + s]! &&& 1#u8).bv <<< s)⟩ hk'


