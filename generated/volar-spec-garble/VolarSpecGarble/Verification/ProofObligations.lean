/- Handwritten proofs about the extracted definitions.

hax creates this directory once and never modifies anything under
`Verification/`.

This file: the M2 bridge groundwork — partial-correctness *specs* (Aeneas
`⦃·⦄` idiom) for the shim `array.Array.from_fn` and the garble spec's
`share`/`open`, capped by the Aeneas-side round-trip theorem
`open_share_roundtrip` (the extraction-level counterpart of the native
`Eval_open_Garble_share` in `VolarSpecNative.Verification`).

Conventions used throughout:
- `vecL` extracts the list spine of the extracted shim Array. It is a `def`
  (not an abbrev) so goals stay well-typed at instances transparency —
  the `alloc.vec.Vec → Slice` coercion chain is semireducible and breaks
  `dsimp`/progress checks otherwise.
- Monadic binds are reduced by `simp only [Bind.bind, Aeneas.Std.bind]`
  (the `Bind` instance hides the reducible `Aeneas.Std.bind`; `bind_tc_ok`
  rewriting leaves unreduced redexes behind).
- `rw` steps in loop proofs are fully instantiated (e.g. `hg f i`) so they
  cannot rewrite under the loop's recursive lambda, which must stay
  syntactically identical to the induction hypothesis's. -/
import VolarSpecGarble.Extraction

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM ControlFlow Error
open volar_spec
open Aeneas.Std.WP

/-- List spine of an extracted `array.Array`'s Vec (kept as a `def` so goals
stay well-typed at instances transparency). -/
def vecL {T : Type} (v : alloc.vec.Vec T) : List T := v.val

/-- `spec` is total correctness here: fail/div are excluded. -/
theorem spec_ok_elim {α : Type} {m : RustM α} {p : α → Prop} (h : spec m p) :
    ∃ v, m = ok v ∧ p v := by
  cases hm : m with
  | ok v => exact ⟨v, rfl, by simpa [spec, theta, wp_return, hm] using h⟩
  | fail e => simp [spec, theta, hm] at h
  | div => simp [spec, theta, hm] at h

/-- `x ^^^ y ^^^ y = x` on Aeneas `U8`. -/
theorem u8_xor_cancel (x y : Std.U8) : x ^^^ y ^^^ y = x := by
  show UScalar.xor (UScalar.xor x y) y = x
  unfold UScalar.xor
  cases x; cases y
  congr 1
  dsimp only
  rw [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

/-- The extracted `from_fn_loop` is `loop` over its body (by definition;
kept as a named rewrite so specs can stay in the `loop` form). -/
theorem from_fn_loop_eq_loop {T N T2 : Type}
    (d : array.ArraySize N) (F : core.ops.function.FnMut T2 Std.Usize T)
    (f : T2) (data : alloc.vec.Vec T) (i : Std.Usize) :
    array.Array.from_fn_loop d F f data i =
    loop (fun x => array.Array.from_fn_loop.body d F x.1 x.2.1 x.2.2) (f, data, i) := rfl

theorem u8_xor_comm (x y : Std.U8) : x ^^^ y = y ^^^ x := by
  show UScalar.xor x y = UScalar.xor y x
  unfold UScalar.xor
  cases x; cases y
  congr 1
  dsimp only
  exact BitVec.xor_comm _ _

theorem u8_xor_cancel2 (b t : Std.U8) : (b ^^^ t) ^^^ b = t := by
  rw [u8_xor_comm b t]
  exact u8_xor_cancel t b


/-- Spec of the `split_first` model (hand model in Assumptions): nil case. -/
theorem slice_split_first_nil {T : Type} (s : Slice T) (h : s.val = []) :
    core.slice.Slice.split_first s = ok core.option.Option.None := by
  conv_lhs => rw [core.slice.Slice.split_first]
  split
  · rfl
  · rename_i x' rest' hv
    rw [h] at hv
    nomatch hv

/-- Spec of the `split_first` model: cons case. -/
theorem slice_split_first_cons {T : Type} (s : Slice T) (x : T) (rest : List T)
    (h : s.val = x :: rest) :
    core.slice.Slice.split_first s = ok (core.option.Option.Some (x,
      (⟨rest, by
        have hsp := s.property
        rw [h] at hsp
        simp only [List.length_cons] at hsp
        omega⟩ : Slice T))) := by
  conv_lhs => rw [core.slice.Slice.split_first]
  split
  · rename_i hv
    rw [h] at hv
    nomatch hv
  · rename_i x' rest' hv
    rw [h] at hv
    simp only [List.cons.injEq] at hv
    obtain ⟨rfl, rfl⟩ := hv
    rfl

/-- `core.U8`'s `Default` computes to `default`. -/
theorem core_u8_default :
    core.U8.Insts.CoreDefaultDefault.default = ok (default : Std.U8) := by
  rfl

/-- Spec of the shim's `Default` loop (mirrors `from_fn_loop_spec`). -/
theorem array_default_loop_spec {T N : Type}
    (dd : core.default.Default T) (d : array.ArraySize N)
    (m : Std.Usize) (hsize : d.typenummarker_traitsUnsignedInst.USIZE = ok m)
    (dv : T) (hdv : dd.default = ok dv)
    : ∀ (k : Nat) (data : alloc.vec.Vec T) (i : Std.Usize),
      m.val - i.val = k → i.val ≤ m.val →
      vecL data = List.replicate i.val dv →
      loop (fun x => array.Array.Insts.CoreDefaultDefault.default_loop.body dd d x.1 x.2) (data, i)
        ⦃ data' => vecL data' = List.replicate m.val dv ⦄ := by
  intro k
  induction k with
  | zero =>
    intro data i hk hi hdata
    have him : i.val = m.val := by omega
    rw [loop.eq_1]
    conv in (array.Array.Insts.CoreDefaultDefault.default_loop.body dd d (data, i).1
        (data, i).2) =>
      simp only [array.Array.Insts.CoreDefaultDefault.default_loop.body]
    rw [hsize]
    simp only [Bind.bind, Aeneas.Std.bind]
    have hni : ¬ (i < m) := by simp [UScalar.lt_equiv, him]
    rw [if_neg hni]
    simp only [spec_ok]
    rw [← him]
    exact hdata
  | succ k ih =>
    intro data i hk hi hdata
    have hlt : i < m := by simp [UScalar.lt_equiv]; omega
    rw [loop.eq_1]
    conv in (array.Array.Insts.CoreDefaultDefault.default_loop.body dd d (data, i).1
        (data, i).2) =>
      simp only [array.Array.Insts.CoreDefaultDefault.default_loop.body]
    rw [hsize]
    simp only [Bind.bind, Aeneas.Std.bind]
    rw [if_pos hlt]
    rw [hdv]
    simp only [Bind.bind, Aeneas.Std.bind]
    have hlen : (vecL data).length = i.val := by rw [hdata]; simp [vecL]
    have hlen2 : (data.val ++ [dv]).length ≤ Usize.max := by
      simp only [List.length_append, List.length_cons, List.length_nil,
        show data.val.length = i.val from hlen]
      have h2 : m.val ≤ Usize.max := by scalar_tac
      omega
    have hpush : data.push dv = ok ⟨data.val ++ [dv], hlen2⟩ := by
      simp only [alloc.vec.Vec.push, rust_primitives.sequence.seq_push]
      rw [dif_pos hlen2]
      simp only [Bind.bind, Aeneas.Std.bind]
    have hadd := UScalar.add_equiv i 1#usize
    have h1v : (1#usize : Std.Usize).val = 1 := by
      simp [UScalar.ofNat, UScalar.ofNatCore_val_eq]
    rw [h1v] at hadd
    rw [hpush]
    simp only [Bind.bind, Aeneas.Std.bind]
    cases haddi : i + 1#usize with
    | ok z =>
      rw [haddi] at hadd; obtain ⟨hin, hv, -⟩ := hadd
      simp
      exact ih ⟨data.val ++ [dv], hlen2⟩ z (by omega) (by omega) (by
        show data.val ++ [dv] = _
        rw [hv, List.replicate_succ']
        have hdata' : data.val = List.replicate i.val dv := hdata
        rw [← hdata'])
    | fail e =>
      rw [haddi] at hadd
      obtain ⟨-, hnin⟩ := hadd
      exfalso
      have hlt' : i.val < m.val := (UScalar.lt_equiv i m).mp hlt
      simp only [UScalar.inBounds] at hnin
      have hb := m.hBounds
      omega
    | div => rw [haddi] at hadd; simp at hadd

/-- Spec of the shim's `Default for Array` instance: the result's data is
`replicate N.USIZE default`. -/
theorem array_default_spec {T N : Type}
    (dd : core.default.Default T) (dc : core.clone.Clone T) (d : array.ArraySize N)
    (m : Std.Usize) (hsize : d.typenummarker_traitsUnsignedInst.USIZE = ok m)
    (dv : T) (hdv : dd.default = ok dv) :
    array.Array.Insts.CoreDefaultDefault.default dd dc d
      ⦃ a => vecL a.data = List.replicate m.val dv ⦄ := by
  simp only [array.Array.Insts.CoreDefaultDefault.default, alloc.vec.Vec.new,
    rust_primitives.sequence.seq_empty, Bind.bind, Aeneas.Std.bind]
  rw [show array.Array.Insts.CoreDefaultDefault.default_loop dd d (Slice.new T) 0#usize
      = loop (fun x => array.Array.Insts.CoreDefaultDefault.default_loop.body dd d x.1 x.2)
        (Slice.new T, 0#usize) from rfl]
  have hloop := array_default_loop_spec dd d m hsize dv hdv m.val (Slice.new T) 0#usize
    (by simp [UScalar.ofNat, UScalar.ofNatCore_val_eq]) (by simp)
    (by simp [vecL, Slice.new])
  obtain ⟨v, hv, hpost⟩ := spec_ok_elim hloop
  rw [hv]
  simp only []
  rw [spec_ok]
  exact hpost

/-- Spec of the extracted `from_fn` loop: after the loop, the data is the
prefix extended by the generator's remaining values. The FnMut closure is
required to be *stateless* (returns its input state unchanged) and
total below `m`. -/
theorem from_fn_loop_spec {T N T2 : Type}
    (d : array.ArraySize N) (F : core.ops.function.FnMut T2 Std.Usize T)
    (m : Std.Usize) (hsize : d.typenummarker_traitsUnsignedInst.USIZE = ok m)
    (f : T2)
    (g : Nat → T) (hg : ∀ (i : Std.Usize), i.val < m.val → F.call_mut f i = ok (g i.val, f))
    : ∀ (k : Nat) (data : alloc.vec.Vec T) (i : Std.Usize),
      m.val - i.val = k → i.val ≤ m.val →
      vecL data = List.ofFn (fun j : Fin i.val => g j.val) →
      loop (fun x => array.Array.from_fn_loop.body d F x.1 x.2.1 x.2.2) (f, data, i)
        ⦃ data' => vecL data' = List.ofFn (fun j : Fin m.val => g j.val) ⦄ := by
  intro k
  induction k with
  | zero =>
    intro data i hk hi hdata
    have him : i.val = m.val := by omega
    rw [loop.eq_1]
    conv in (array.Array.from_fn_loop.body d F (f, data, i).1 (f, data, i).2.1
        (f, data, i).2.2) =>
      simp only [array.Array.from_fn_loop.body]
    rw [hsize]
    simp only [Bind.bind, Aeneas.Std.bind]
    have hni : ¬ (i < m) := by simp [UScalar.lt_equiv, him]
    rw [if_neg hni]
    simp only [spec_ok]
    rw [← him]
    exact hdata
  | succ k ih =>
    intro data i hk hi hdata
    have hlt : i < m := by simp [UScalar.lt_equiv]; omega
    rw [loop.eq_1]
    conv in (array.Array.from_fn_loop.body d F (f, data, i).1 (f, data, i).2.1
        (f, data, i).2.2) =>
      simp only [array.Array.from_fn_loop.body]
    rw [hsize]
    simp only [Bind.bind, Aeneas.Std.bind]
    rw [if_pos hlt]
    rw [hg i ((UScalar.lt_equiv i m).mp hlt)]
    simp only [Bind.bind, Aeneas.Std.bind]
    simp
    have hlen : (vecL data).length = i.val := by rw [hdata]; simp [vecL]
    have hlen2 : (data.val ++ [g i.val]).length ≤ Usize.max := by
      simp only [List.length_append, List.length_cons, List.length_nil,
        show data.val.length = i.val from hlen]
      have h2 : m.val ≤ Usize.max := by scalar_tac
      omega
    have hpush : data.push (g i.val) = ok ⟨data.val ++ [g i.val], hlen2⟩ := by
      simp only [alloc.vec.Vec.push, rust_primitives.sequence.seq_push]
      rw [dif_pos hlen2]
      simp only [Bind.bind, Aeneas.Std.bind]
    have hadd := UScalar.add_equiv i 1#usize
    have h1v : (1#usize : Std.Usize).val = 1 := by
      simp [UScalar.ofNat, UScalar.ofNatCore_val_eq]
    rw [h1v] at hadd
    rw [hpush]
    simp only [Bind.bind, Aeneas.Std.bind]
    cases haddi : i + 1#usize with
    | ok z =>
      rw [haddi] at hadd; obtain ⟨hin, hv, -⟩ := hadd
      simp
      exact ih ⟨data.val ++ [g i.val], hlen2⟩ z (by omega) (by omega) (by
        show data.val ++ [g i.val] = _
        rw [hv, List.ofFn_succ_last]
        simp only [Fin.val_last, Fin.val_castSucc]
        have hdata' : data.val = List.ofFn (fun j : Fin i.val => g j.val) := hdata
        rw [← hdata'])
    | fail e =>
      rw [haddi] at hadd
      obtain ⟨-, hnin⟩ := hadd
      exfalso
      have hlt' : i.val < m.val := (UScalar.lt_equiv i m).mp hlt
      simp only [UScalar.inBounds] at hnin
      have hb := m.hBounds
      omega
    | div => rw [haddi] at hadd; simp at hadd

/-- Spec of the extracted `array.Array.from_fn`: the result's data is the
`List.ofFn` image of the generator. -/
theorem from_fn_spec {T N T2 : Type}
    (d : array.ArraySize N) (F : core.ops.function.FnMut T2 Std.Usize T)
    (m : Std.Usize) (hsize : d.typenummarker_traitsUnsignedInst.USIZE = ok m)
    (f : T2)
    (g : Nat → T) (hg : ∀ (i : Std.Usize), i.val < m.val → F.call_mut f i = ok (g i.val, f)) :
    array.Array.from_fn d F f
      ⦃ a => vecL a.data = List.ofFn (fun j : Fin m.val => g j.val) ⦄ := by
  simp only [array.Array.from_fn, alloc.vec.Vec.new, rust_primitives.sequence.seq_empty,
    Bind.bind, Aeneas.Std.bind]
  rw [from_fn_loop_eq_loop]
  have hloop := from_fn_loop_spec d F m hsize f g hg m.val (Slice.new T) 0#usize
    (by simp [UScalar.ofNat, UScalar.ofNatCore_val_eq]) (by simp)
    (by simp [vecL, Slice.new])
  obtain ⟨v, hv, hpost⟩ := spec_ok_elim hloop
  rw [hv]
  simp only []
  rw [spec_ok]
  exact hpost

/-- Pointwise xor of two list spines, as a total Nat-indexed function
(out-of-range indices give 0; proofs only use in-range indices). -/
def xorBytes (a b : List Std.U8) (j : Nat) : Std.U8 :=
  if hj : j < a.length ∧ j < b.length then a[j]'hj.1 ^^^ b[j]'hj.2 else default

/-- The share closure is stateless and pointwise-xor (in range). -/
theorem share_closure_call_mut {N : Type} (d : vole.VoleArray N Std.U8)
    (g : garble.Garble N) (t : array.Array Std.U8 N) (i : Std.Usize)
    (hg : i.val < (vecL g.base.data).length) (ht : i.val < (vecL t.data).length) :
    garble.Garble.share.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU8.call_mut
        d (g, t) i =
      ok (xorBytes (vecL g.base.data) (vecL t.data) i.val, (g, t)) := by
  have hg' : i.val < g.base.data.val.length := hg
  have ht' : i.val < t.data.val.length := ht
  simp only [garble.Garble.share.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU8.call_mut,
    array.Array.Insts.CoreOpsIndexIndexUsizeT.index,
    alloc.vec.Vec.Insts.CoreOpsIndexIndex.index,
    core.Slice.Insts.CoreOpsIndexIndex.index,
    alloc.vec.Vec.Insts.CoreOpsDerefDerefSlice.deref, alloc.vec.Vec.as_slice,
    rust_primitives.sequence.seq_to_slice,
    core.Usize.Insts.CoreSliceIndexSliceIndexSliceT.get,
    rust_primitives.slice.slice_length,
    rust_primitives.slice.slice_index, Slice.index_usize,
    UScalar.lt_equiv, Slice.len_val, Slice.length, Slice.getElem?_Usize_eq,
    eq_true hg', eq_true ht',
    decide_true, ↓reduceIte, getElem?_pos, spec_ok, bind_tc_ok, lift]
  simp [xorBytes, vecL, hg, ht, hg', ht']
  rfl

/-- The open closure is stateless and pointwise-xor (in range). is stateless and pointwise-xor (in range). -/
theorem open_closure_call_mut {N : Type} (d : vole.VoleArray N Std.U8)
    (e : garble.Eval N) (g : garble.Garble N) (i : Std.Usize)
    (he : i.val < (vecL e.target.data).length) (hg : i.val < (vecL g.base.data).length) :
    garble.Eval.open.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU8.call_mut
        d (e, g) i =
      ok (xorBytes (vecL e.target.data) (vecL g.base.data) i.val, (e, g)) := by
  have he' : i.val < e.target.data.val.length := he
  have hg' : i.val < g.base.data.val.length := hg
  simp only [garble.Eval.open.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU8.call_mut,
    array.Array.Insts.CoreOpsIndexIndexUsizeT.index,
    alloc.vec.Vec.Insts.CoreOpsIndexIndex.index,
    core.Slice.Insts.CoreOpsIndexIndex.index,
    alloc.vec.Vec.Insts.CoreOpsDerefDerefSlice.deref, alloc.vec.Vec.as_slice,
    rust_primitives.sequence.seq_to_slice,
    core.Usize.Insts.CoreSliceIndexSliceIndexSliceT.get,
    rust_primitives.slice.slice_length,
    rust_primitives.slice.slice_index, Slice.index_usize,
    UScalar.lt_equiv, Slice.len_val, Slice.length, Slice.getElem?_Usize_eq,
    eq_true he', eq_true hg',
    decide_true, ↓reduceIte, getElem?_pos, spec_ok, bind_tc_ok, lift]
  simp [xorBytes, vecL, he, hg, he', hg']
  rfl

/-- Spec of the extracted `Garble.share`: the shared target is the pointwise
xor of base and target. -/
theorem share_spec {N : Type} (d : vole.VoleArray N Std.U8)
    (m : Std.Usize)
    (hsize : d.arrayArraySizeInst.typenummarker_traitsUnsignedInst.USIZE = ok m)
    (g : garble.Garble N) (t : array.Array Std.U8 N)
    (hgl : (vecL g.base.data).length = m.val) (htl : (vecL t.data).length = m.val) :
    garble.Garble.share d g t
      ⦃ e => vecL e.target.data = List.ofFn (fun j : Fin m.val =>
          xorBytes (vecL g.base.data) (vecL t.data) j.val) ⦄ := by
  simp only [garble.Garble.share]
  apply spec_bind (from_fn_spec d.arrayArraySizeInst
    (garble.Garble.share.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU8 d) m hsize (g, t)
    (fun j => xorBytes (vecL g.base.data) (vecL t.data) j)
    (by
      intro i hi
      exact share_closure_call_mut d g t i (by rw [hgl]; exact hi) (by rw [htl]; exact hi)))
  intro a ha
  rw [spec_ok]
  exact ha

/-- Spec of the extracted `Eval.open`: the opened value is the pointwise xor
of target and base. -/
theorem open_spec {N : Type} (d : vole.VoleArray N Std.U8)
    (m : Std.Usize)
    (hsize : d.arrayArraySizeInst.typenummarker_traitsUnsignedInst.USIZE = ok m)
    (e : garble.Eval N) (g : garble.Garble N)
    (hel : (vecL e.target.data).length = m.val) (hgl : (vecL g.base.data).length = m.val) :
    garble.Eval.open d e g
      ⦃ a => vecL a.data = List.ofFn (fun j : Fin m.val =>
          xorBytes (vecL e.target.data) (vecL g.base.data) j.val) ⦄ := by
  simp only [garble.Eval.open]
  exact from_fn_spec d.arrayArraySizeInst
    (garble.Eval.open.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU8 d) m hsize (e, g)
    (fun j => xorBytes (vecL e.target.data) (vecL g.base.data) j)
    (by
      intro i hi
      exact open_closure_call_mut d e g i (by rw [hel]; exact hi) (by rw [hgl]; exact hi))

/-- **Round-trip on the extracted spec**: `open (share g t) g = ok t`, given
both arrays have the `N.USIZE` length. This is the extraction-level
counterpart of `VolarSpecNative.Eval_open_Garble_share`. -/
theorem open_share_roundtrip {N : Type} (d : vole.VoleArray N Std.U8)
    (m : Std.Usize)
    (hsize : d.arrayArraySizeInst.typenummarker_traitsUnsignedInst.USIZE = ok m)
    (g : garble.Garble N) (t : array.Array Std.U8 N)
    (hgl : (vecL g.base.data).length = m.val) (htl : (vecL t.data).length = m.val) :
    (do let e ← garble.Garble.share d g t; garble.Eval.open d e g) = ok t := by
  obtain ⟨e0, hshare, hpost1⟩ := spec_ok_elim (share_spec d m hsize g t hgl htl)
  have hle : (vecL e0.target.data).length = m.val := by rw [hpost1]; simp
  obtain ⟨a0, hopen, hpost2⟩ := spec_ok_elim (open_spec d m hsize e0 g hle hgl)
  rw [show (do let e ← garble.Garble.share d g t; garble.Eval.open d e g)
        = ok a0 from by
      simp only [Bind.bind, Aeneas.Std.bind]
      rw [hshare]
      simp only [Aeneas.Std.bind]
      rw [hopen]]
  rw [hpost1] at hpost2
  have hfin : List.ofFn (fun j : Fin m.val =>
        xorBytes (List.ofFn (fun j' : Fin m.val =>
          xorBytes (vecL g.base.data) (vecL t.data) j'.val))
          (vecL g.base.data) j.val) = vecL t.data := by
    apply List.ext_getElem
    · simp [htl]
    · intro i h1 h2
      have h1' : i < m.val := by simpa using h1
      have hb : i < (vecL g.base.data).length := by rw [hgl]; exact h1'
      have ht : i < (vecL t.data).length := by rw [htl]; exact h1'
      rw [List.getElem_ofFn]
      simp only [xorBytes]
      rw [dif_pos ⟨by simpa using h1', hb⟩]
      rw [List.getElem_ofFn]
      simp only [xorBytes]
      rw [dif_pos ⟨hb, ht⟩]
      exact u8_xor_cancel2 _ _
  have hval : a0.data.val = t.data.val := hpost2.trans hfin
  congr 1
  cases a0; cases t
  congr 1
  · exact (Slice.eq_iff _ _).mpr (by simpa using hval)
