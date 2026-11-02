import VolarSpecNative.Generated

/-!
# Native-spec proofs

First correctness theorem of the native (printer_lean) representation:
sharing a target label through a garble base and opening it again is the
identity. This is the native-side statement; the bridge theorem to the
Aeneas extraction (`VolarSpecGarble`) is M2.

The native model is `List`-based, so the round-trip holds up to the length
invariant the type-level `N` carried in the Rust original.
-/

/-- Round-trip: `open (share g t) g = t`, given `t` has the label length. -/
theorem Eval_open_Garble_share {n : Nat} (g : Garble n) (t : List UInt8)
    (ht : t.length = n) :
    Eval.open_ (Garble.share g t) g = t := by
  unfold Eval.open_ Garble.share
  apply List.ext_getElem
  · simp [List.length_ofFn, ht]
  · intro i h1 h2
    have hi : i < n := ht ▸ h2
    rw [List.getElem_ofFn]
    simp only [List.getElem!_eq_getElem?_getD, List.getElem?_ofFn, ht,
      dif_pos hi, List.getElem?_eq_getElem h2, Option.getD_some]
    rw [UInt8.xor_comm (g.base[i]?.getD default) t[i], UInt8.xor_assoc,
      UInt8.xor_self, UInt8.xor_zero]
