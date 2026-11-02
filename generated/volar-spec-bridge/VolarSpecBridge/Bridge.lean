import VolarSpecGarble.Extraction
import VolarSpecGarble.Verification.ProofObligations
import VolarSpecNative.Generated

/-!
# M2 bridge: Aeneas extraction ↔ native emission

Transports between the two representations of the garble spec:

- `Aeneas.Std.U8` ↔ `UInt8` (via `val`/`toNat`)
- extracted shim `array.Array U8 N` ↔ native `List UInt8`
- extracted `garble.Garble N`/`garble.Eval N` ↔ native `Garble n`/`Eval n`

and the commutation theorems for the digest-free fragment
(`share`/`open`): the extracted functions, transported to lists, equal the
native functions applied to the transported inputs.
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

/-- Transport: extracted shim array → native list. -/
def arrToNative {N : Type} (a : array.Array Std.U8 N) : List UInt8 :=
  (vecL a.data).map u8ToUInt8

/-- Transport: extracted garble/eval → native. -/
def garbleToNative {N : Type} (n : Nat) (g : garble.Garble N) : Garble n :=
  { base := arrToNative g.base }

def evalToNative {N : Type} (n : Nat) (e : garble.Eval N) : Eval n :=
  { target := arrToNative e.target }

/-- `u8ToUInt8` is a xor-homomorphism. -/
theorem u8ToUInt8_xor (x y : Std.U8) :
    u8ToUInt8 (x ^^^ y) = u8ToUInt8 x ^^^ u8ToUInt8 y := by
  apply UInt8.toNat_inj.mp
  simp [u8ToUInt8_val, UScalar.val_xor]

open Aeneas.Std.WP
open RustM

/-- **share commutes with the transport**: sharing on the extracted side and
transporting equals sharing on the native side. -/
theorem share_commutes {N : Type} (d : vole.VoleArray N Std.U8)
    (m : Std.Usize)
    (hsize : d.arrayArraySizeInst.typenummarker_traitsUnsignedInst.USIZE = ok m)
    (g : garble.Garble N) (t : array.Array Std.U8 N)
    (hgl : (vecL g.base.data).length = m.val) (htl : (vecL t.data).length = m.val) :
    (do let e ← garble.Garble.share d g t; ok (evalToNative m.val e)) =
    ok (Garble.share (garbleToNative m.val g) (arrToNative t)) := by
  obtain ⟨e0, hshare, hpost⟩ := spec_ok_elim (share_spec d m hsize g t hgl htl)
  simp only [Bind.bind, Aeneas.Std.bind]
  rw [hshare]
  simp only []
  congr 1
  simp only [evalToNative, garbleToNative, Garble.share, arrToNative]
  congr 1
  rw [hpost, List.map_ofFn]
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    rw [List.getElem_ofFn, List.getElem_ofFn]
    have hi : i < m.val := by simpa using h1
    have hb : i < (vecL g.base.data).length := by rw [hgl]; exact hi
    have ht : i < (vecL t.data).length := by rw [htl]; exact hi
    simp only [Function.comp_apply, Fin.val_mk, xorBytes]
    rw [dif_pos ⟨hb, ht⟩]
    rw [List.getElem!_eq_getElem?_getD, List.getElem!_eq_getElem?_getD]
    rw [List.getElem?_map, List.getElem?_map]
    rw [List.getElem?_eq_getElem hb, List.getElem?_eq_getElem ht]
    simp [u8ToUInt8_xor]

/-- **open commutes with the transport.** -/
theorem open_commutes {N : Type} (d : vole.VoleArray N Std.U8)
    (m : Std.Usize)
    (hsize : d.arrayArraySizeInst.typenummarker_traitsUnsignedInst.USIZE = ok m)
    (e : garble.Eval N) (g : garble.Garble N)
    (hel : (vecL e.target.data).length = m.val) (hgl : (vecL g.base.data).length = m.val) :
    (do let a ← garble.Eval.open d e g; ok (arrToNative a)) =
    ok (Eval.open_ (evalToNative m.val e) (garbleToNative m.val g)) := by
  obtain ⟨a0, hopen, hpost⟩ := spec_ok_elim (open_spec d m hsize e g hel hgl)
  simp only [Bind.bind, Aeneas.Std.bind]
  rw [hopen]
  simp only []
  congr 1
  simp only [evalToNative, garbleToNative, Eval.open_, arrToNative]
  rw [hpost, List.map_ofFn]
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    rw [List.getElem_ofFn, List.getElem_ofFn]
    have hi : i < m.val := by simpa using h1
    have he : i < (vecL e.target.data).length := by rw [hel]; exact hi
    have hb : i < (vecL g.base.data).length := by rw [hgl]; exact hi
    simp only [Function.comp_apply, xorBytes]
    rw [dif_pos ⟨he, hb⟩]
    rw [List.getElem!_eq_getElem?_getD, List.getElem!_eq_getElem?_getD]
    rw [List.getElem?_map, List.getElem?_map]
    rw [List.getElem?_eq_getElem he, List.getElem?_eq_getElem hb]
    simp [u8ToUInt8_xor]

/-- **M2 capstone**: the native round-trip, *derived* from the extracted
spec's verified behavior via the bridge — the extracted `open ∘ share`
specification transports to the native `open_ ∘ share` equation. -/
theorem native_roundtrip_via_bridge {N : Type} (d : vole.VoleArray N Std.U8)
    (m : Std.Usize)
    (hsize : d.arrayArraySizeInst.typenummarker_traitsUnsignedInst.USIZE = ok m)
    (g : garble.Garble N) (t : array.Array Std.U8 N)
    (hgl : (vecL g.base.data).length = m.val) (htl : (vecL t.data).length = m.val) :
    Eval.open_ (Garble.share (garbleToNative m.val g) (arrToNative t))
      (garbleToNative m.val g) = arrToNative t := by
  have h := open_share_roundtrip d m hsize g t hgl htl
  obtain ⟨e0, hshare, hpost⟩ := spec_ok_elim (share_spec d m hsize g t hgl htl)
  have hle : (vecL e0.target.data).length = m.val := by rw [hpost]; simp
  -- the extracted round trip: open (share g t) g = ok t; with share = ok e0:
  have hopen0 : garble.Eval.open d e0 g = ok t := by
    rw [show garble.Garble.share d g t = ok e0 from hshare] at h
    simp only [Bind.bind, Aeneas.Std.bind] at h
    exact h
  -- transport both ends through the commutation theorems
  have hs := share_commutes d m hsize g t hgl htl
  rw [hshare] at hs
  simp only [Bind.bind, Aeneas.Std.bind] at hs
  rw [ok.injEq] at hs
  have ho := open_commutes d m hsize e0 g hle hgl
  rw [hopen0] at ho
  simp only [Bind.bind, Aeneas.Std.bind] at ho
  rw [ok.injEq] at ho
  rw [← hs, ho]
