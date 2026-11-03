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

/-- The Usize Clone instance is the identity. -/
theorem usize_clone (x : Std.Usize) : core.Usize.Insts.CoreCloneClone.clone x = ok x := by
  rfl

/-- The Usize PartialOrd `partial_cmp` computes the comparison. -/
theorem usize_partial_cmp (a b : Std.Usize) :
    core.Usize.Insts.CoreCmpPartialOrdUsize.partial_cmp a b =
      ok (core.option.Option.Some (match compare a.val b.val with
        | .lt => core.cmp.Ordering.Less
        | .eq => core.cmp.Ordering.Equal
        | .gt => core.cmp.Ordering.Greater)) := by
  rfl

/-- The Usize PartialOrd `lt` computes the comparison. -/
theorem usize_partialOrd_lt (a b : Std.Usize) :
    core.Usize.Insts.CoreCmpPartialOrdUsize.lt a b = ok (decide (a.val < b.val)) := by
  simp only [core.Usize.Insts.CoreCmpPartialOrdUsize, CoreModels.core.mkUPartialOrd]
  cases h : compare a.val b.val with
  | lt => have h2 := Nat.compare_eq_lt.mp h; simp [h2]
  | eq => have h2 := Nat.compare_eq_eq.mp h; simp [h2]
  | gt => have h2 := Nat.compare_eq_gt.mp h; simp [show ¬ (a.val < b.val) from by omega]

/-- (curated) next on a Usize range with the CoreModels step instance. -/
theorem usize_range_next_spec (range : core.ops.range.Range Std.Usize) :
    core.iter.range.IteratorRange.next core.Usize.Insts.CoreIterRangeStep range
    ⦃ opt range' =>
      (range.start.val < range.end.val →
        opt = core.option.Option.Some range.start ∧
        range'.start.val = range.start.val + 1 ∧ range'.end = range.end) ∧
      (range.start.val ≥ range.end.val →
        opt = core.option.Option.None ∧ range' = range) ⦄ := by
  unfold core.iter.range.IteratorRange.next
  unfold CoreModels.core.IteratorRange.next
  simp only [core.Usize.Insts.CoreIterRangeStep, usize_partial_cmp, bind_tc_ok]
  cases hcmp : compare range.start.val range.end.val with
  | lt =>
    have hlt : range.start.val < range.end.val := Nat.compare_eq_lt.mp hcmp
    simp only [usize_clone, bind_tc_ok, ↓reduceIte]
    conv in (core.Usize.Insts.CoreIterRangeStep.forward_checked range.start 1#usize) =>
      simp only [core.Usize.Insts.CoreIterRangeStep.forward_checked,
        core.convert.TryFromUTInfallible.Blanket.try_from, core.convert.From.Blanket.from,
        core.num.Usize.checked_add, core.num.Usize.overflowing_add,
        rust_primitives.arithmetic.overflowing_add_usize, bind_tc_ok]
    have hno : BitVec.uaddOverflow range.start.bv (1#usize).bv = false := by
      have hbv : range.start.bv.toNat < 2 ^ UScalarTy.Usize.numBits := range.start.hBounds
      have heb : range.end.val < 2 ^ UScalarTy.Usize.numBits := range.end.hBounds
      have h1 : (1#usize : Std.Usize).bv.toNat = 1 := by
        simp [UScalar.ofNat, UScalar.ofNatCore_val_eq]
      simp only [BitVec.uaddOverflow, decide_eq_false_iff_not, not_le, h1]
      show range.start.bv.toNat + 1 < 2 ^ UScalarTy.Usize.numBits
      have hlink : range.start.val = range.start.bv.toNat := rfl
      omega
    simp only [UScalar.overflowing_add, bind_tc_ok, hno, Bool.false_eq_true, ↓reduceIte, spec_ok]
    refine ⟨?_, ?_⟩
    · intro _
      refine ⟨rfl, ?_, rfl⟩
      have h1 : (1#usize : Std.Usize).bv.toNat = 1 := by
        simp [UScalar.ofNat, UScalar.ofNatCore_val_eq]
      have hb : range.start.bv.toNat < 2 ^ UScalarTy.Usize.numBits := range.start.hBounds
      have he : range.end.val < 2 ^ UScalarTy.Usize.numBits := range.end.hBounds
      show ((⟨range.start.bv + (1#usize : Std.Usize).bv⟩ : Std.Usize)).val = range.start.val + 1
      have hlink : range.start.val = range.start.bv.toNat := rfl
      have hel : range.end.val = range.end.bv.toNat := rfl
      simp only [UScalar.val, BitVec.toNat_add, h1]
      rw [Nat.mod_eq_of_lt]
      omega
    · intro hge
      omega
  | eq =>
    have heq : range.start.val = range.end.val := Nat.compare_eq_eq.mp hcmp
    simp only [usize_clone, bind_tc_ok, Bool.false_eq_true, ↓reduceIte, spec_ok]
    exact ⟨fun h => by omega, fun _ => ⟨rfl, rfl⟩⟩
  | gt =>
    have hgt : range.end.val < range.start.val := Nat.compare_eq_gt.mp hcmp
    simp only [usize_clone, bind_tc_ok, Bool.false_eq_true, ↓reduceIte, spec_ok]
    exact ⟨fun h => by omega, fun _ => ⟨rfl, rfl⟩⟩

/-- The bit-pack accumulated by to_share's inner loop from position `s`
(BitVec-level so it is pure). -/
def bitPackBvFrom (l : List Std.U8) (i s : Nat) (v : BitVec 8) : BitVec 8 :=
  if s < 8 then
    bitPackBvFrom l i (s + 1) (v ||| ((l[i * 8 + s]! &&& 1#u8).bv <<< s))
  else v
termination_by 8 - s

/-- (curated) scalar ops as functions, for rewriting instance calls. -/
theorem usize_mul_eq (a b : Std.Usize) : a * b = UScalar.mul a b := rfl
theorem usize_add_eq (a b : Std.Usize) : a + b = UScalar.add a b := rfl
theorem usize_one_val : (1#usize : Std.Usize).val = 1 := by
  simp [UScalar.ofNat, UScalar.ofNatCore_val_eq]
theorem usize_eight_val : (8#usize : Std.Usize).val = 8 := by
  simp [UScalar.ofNat, UScalar.ofNatCore_val_eq]

/-- (curated) U8 shift-left by a small amount: equation form. -/
theorem u8_shl_eq (x : Std.U8) (j : Std.Usize) (hj : j.val < 8) :
    ∃ z : Std.U8, x <<< j = ok z ∧ z.bv = x.bv <<< j.val := by
  have h := U8.ShiftLeft_spec x j
  cases hshl : x <<< j with
  | ok z =>
    rw [hshl] at h
    exact ⟨z, rfl, h.2.1⟩
  | fail e =>
    rw [hshl] at h
    simp only [partialSpec] at h
    cases e <;> simp_all <;> omega
  | div => rw [hshl] at h; simp [partialSpec] at h

/-- bitPackBvFrom unfolds one step. -/
theorem bitPackBvFrom_step (l : List Std.U8) (i s : Nat) (v : BitVec 8) (hs : s < 8) :
    bitPackBvFrom l i s v =
      bitPackBvFrom l i (s + 1) (v ||| ((l[i * 8 + s]! &&& 1#u8).bv <<< s)) := by
  conv_lhs => rw [bitPackBvFrom.eq_def]
  rw [if_pos hs]

/-- (curated) one step of to_share's inner loop body, as a value-level
equation: at a valid iterator state, the body continues with the packed bit
or'd in. -/
theorem to_share_loop_body_step {N : Type} (d : vole.VoleArray N Std.U8)
    (g : garble.Garble N) (i : Std.Usize)
    (m : Std.Usize) (hg : (vecL g.base.data).length = m.val)
    (hi : i.val * 8 + 7 < m.val)
    (iter : core.ops.range.Range Std.Usize) (v : Std.U8)
    (hlt : iter.start.val < 8) (hend : iter.end = 8#usize) :
    ∃ (it2 : core.ops.range.Range Std.Usize) (z4 : Std.U8),
      garble.Garble.to_share.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU8.call_mut_loop.body
          d g i iter v =
        ok (cont (it2, v ||| z4)) ∧
      it2.start.val = iter.start.val + 1 ∧
      it2.end = iter.end ∧
      z4.bv = ((vecL g.base.data)[i.val * 8 + iter.start.val]! &&& 1#u8).bv <<< iter.start.val := by
  -- next
  obtain ⟨⟨o, it2⟩, hr, hpost⟩ := spec_ok_elim (usize_range_next_spec iter)
  have halias : core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next
      core.Usize.Insts.CoreIterRangeStep iter =
      core.iter.range.IteratorRange.next core.Usize.Insts.CoreIterRangeStep iter := rfl
  obtain ⟨hpost1, -⟩ := hpost
  obtain ⟨hopt, hitstart, hitend⟩ := hpost1 (by
    have he2 : iter.end.val = 8 := by rw [hend]; exact usize_eight_val
    omega)
  -- the body
  simp only [garble.Garble.to_share.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU8.call_mut_loop.body]
  rw [halias, hr]
  simp only [Bind.bind, Aeneas.Std.bind]
  rw [hopt]
  simp
  -- i * 8
  rw [usize_mul_eq]
  cases hmul : UScalar.mul i 8#usize with
  | fail e =>
    have hmule := UScalar.mul_equiv i 8#usize
    rw [hmul] at hmule
    obtain ⟨-, hnin⟩ := hmule
    exfalso
    simp only [UScalar.inBounds, usize_eight_val] at hnin
    have hb : m.val < 2 ^ UScalarTy.Usize.numBits := m.hBounds
    have hmax : UScalar.max UScalarTy.Usize = 2 ^ UScalarTy.Usize.numBits - 1 := by
      simp [UScalar.max_USize_eq, Usize.max, Usize.numBits, UScalarTy.Usize_numBits_eq]
    omega
  | div =>
    have hmule := UScalar.mul_equiv i 8#usize
    rw [hmul] at hmule
    simp at hmule
  | ok z1 =>
    have hmule := UScalar.mul_equiv i 8#usize
    rw [hmul] at hmule
    obtain ⟨hmin, hmv, -⟩ := hmule
    simp only [usize_eight_val] at hmv
    simp only [Bind.bind, Aeneas.Std.bind]
    -- z1 + iter.start
    cases hadd : z1 + iter.start with
    | fail e =>
      have hadde := UScalar.add_equiv z1 iter.start
      rw [hadd] at hadde
      obtain ⟨-, hnin⟩ := hadde
      exfalso
      simp only [UScalar.inBounds, usize_eight_val] at hnin
      have hb : m.val < 2 ^ UScalarTy.Usize.numBits := m.hBounds
      have hmax : UScalar.max UScalarTy.Usize = 2 ^ UScalarTy.Usize.numBits - 1 := by
        simp [UScalar.max_USize_eq, Usize.max, Usize.numBits, UScalarTy.Usize_numBits_eq]
      omega
    | div =>
      have hadde := UScalar.add_equiv z1 iter.start
      rw [hadd] at hadde
      simp at hadde
    | ok z2 =>
      have hadde := UScalar.add_equiv z1 iter.start
      rw [hadd] at hadde
      obtain ⟨hain, hav2, -⟩ := hadde
      simp only [Bind.bind, Aeneas.Std.bind]
      -- index
      have hbnd : z2.val < g.base.data.val.length := by
        have hgl : g.base.data.val.length = m.val := hg
        rw [hav2, hmv]
        omega
      have hidx : array.Array.Insts.CoreOpsIndexIndexUsizeT.index d.arrayArraySizeInst g.base z2
          = ok (g.base.data.val[z2.val]'hbnd) := by
        simp only [array.Array.Insts.CoreOpsIndexIndexUsizeT.index,
          alloc.vec.Vec.Insts.CoreOpsIndexIndex.index,
          core.Slice.Insts.CoreOpsIndexIndex.index,
          alloc.vec.Vec.Insts.CoreOpsDerefDerefSlice.deref, alloc.vec.Vec.as_slice,
          rust_primitives.sequence.seq_to_slice,
          core.Usize.Insts.CoreSliceIndexSliceIndexSliceT.get,
          rust_primitives.slice.slice_length,
          rust_primitives.slice.slice_index, Slice.index_usize,
          UScalar.lt_equiv, Slice.len_val, Slice.length, Slice.getElem?_Usize_eq,
          hbnd, decide_true, ↓reduceIte, getElem?_pos, spec_ok, bind_tc_ok, lift]
      rw [hidx]
      simp only [Bind.bind, Aeneas.Std.bind, lift]
      -- shl
      obtain ⟨z4, hshl, hshlbv⟩ := u8_shl_eq
        (g.base.data.val[z2.val]'hbnd &&& 1#u8) iter.start (by omega)
      rw [hshl]
      simp only [Bind.bind, Aeneas.Std.bind, lift]
      refine ⟨it2, z4, rfl, hitstart, hitend, ?_⟩
      rw [hshlbv]
      congr 1
      congr 1
      congr 1
      -- (↑g.base.data)[↑z2] = (vecL g.base.data)[i*8+start]!
      have hz2 : z2.val = i.val * 8 + iter.start.val := by rw [hav2, hmv]
      rw [← hz2]
      simp [vecL, List.getElem!_eq_getElem?_getD, getElem?_pos, hbnd]

/-- (curated) the to_share inner loop packs the bits (equation form — avoids
the `Post`/`⦃⦄` elaboration friction). -/
theorem to_share_loop_eq {N : Type} (d : vole.VoleArray N Std.U8)
    (g : garble.Garble N) (i : Std.Usize)
    (m : Std.Usize) (hg : (vecL g.base.data).length = m.val)
    (hi : i.val * 8 + 7 < m.val) :
    ∀ (k : Nat) (iter : core.ops.range.Range Std.Usize) (v : Std.U8),
      8 - iter.start.val = k → iter.start.val ≤ 8 → iter.end = 8#usize →
      loop (fun x =>
        garble.Garble.to_share.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU8.call_mut_loop.body
          d g i x.1 x.2) (iter, v) =
        ok (g, ⟨bitPackBvFrom (vecL g.base.data) i.val iter.start.val v.bv⟩) := by
  intro k
  induction k with
  | zero =>
    intro iter v hk hle hend
    have hs : iter.start.val = 8 := by omega
    have hs8 : iter.start.val = 8 := hs
    rw [loop.eq_1]
    conv in (garble.Garble.to_share.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU8.call_mut_loop.body
        d g i (iter, v).1 (iter, v).2) =>
      simp only [garble.Garble.to_share.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU8.call_mut_loop.body]
    obtain ⟨⟨o, it2⟩, hr, hpost⟩ := spec_ok_elim (usize_range_next_spec iter)
    have halias : core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next
        core.Usize.Insts.CoreIterRangeStep iter =
        core.iter.range.IteratorRange.next core.Usize.Insts.CoreIterRangeStep iter := rfl
    rw [halias, hr]
    simp only [Bind.bind, Aeneas.Std.bind]
    have hge : iter.start.val ≥ iter.end.val := by
      have he := usize_eight_val
      have he2 : iter.end.val = 8 := by rw [hend]; exact he
      omega
    obtain ⟨-, hpost2⟩ := hpost
    obtain ⟨hopt, hiter'⟩ := hpost2 hge
    rw [hopt]
    simp
    rw [hs]
    unfold bitPackBvFrom
    simp
  | succ k ih =>
    intro iter v hk hle hend
    have hlt : iter.start.val < 8 := by
      have he2 : iter.end.val = 8 := by rw [hend]; exact usize_eight_val
      omega
    -- one body step
    obtain ⟨it2, z4, hstep⟩ := to_share_loop_body_step d g i m hg hi iter v hlt hend
    rw [loop.eq_1]
    rw [show (iter, v).1 = iter from rfl, show (iter, v).2 = v from rfl]
    rw [hstep.1]
    simp only [Bind.bind, Aeneas.Std.bind]
    -- IH on the successor state
    have hnext : loop (fun x =>
        garble.Garble.to_share.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU8.call_mut_loop.body
          d g i x.1 x.2) (it2, v ||| z4) =
        ok (g, ⟨bitPackBvFrom (vecL g.base.data) i.val it2.start.val (v ||| z4).bv⟩) :=
      ih it2 (v ||| z4) (by omega) (by omega) (by rw [hstep.2.2.1]; exact hend)
    rw [hnext]
    congr 1
    congr 1
    rw [hstep.2.1]
    conv_rhs => rw [bitPackBvFrom_step _ _ _ _ hlt]
    rw [UScalar.bv_or]
    exact congrArg (fun x : BitVec 8 => (⟨x⟩ : Std.U8))
      (congrArg (bitPackBvFrom (vecL g.base.data) i.val (iter.start.val + 1))
        (congrArg (fun x => v.bv ||| x) hstep.2.2.2))


/-- (curated) the to_share closure is the bit-pack. -/
theorem Garble_to_share_closure_spec {N O : Type} (d : vole.VoleArray N Std.U8)
    (dO : vole.VoleArray O Std.U8)
    (divDict : core.ops.arith.Div N
      (typenum.uint.UInt (typenum.uint.UInt (typenum.uint.UInt (typenum.uint.UInt
        typenum.uint.UTerm typenum.bit.B1) typenum.bit.B0) typenum.bit.B0)
      typenum.bit.B0) O)
    (m : Std.Usize)
    (g : garble.Garble N) (i : Std.Usize)
    (hg : (vecL g.base.data).length = m.val)
    (hi : i.val * 8 + 7 < m.val) :
    garble.Garble.to_share.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU8.call_mut
        d dO divDict g i =
      ok (⟨bitPackBvFrom (vecL g.base.data) i.val 0 (0#u8).bv⟩, g) := by
  simp only [garble.Garble.to_share.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU8.call_mut]
  rw [show garble.Garble.to_share.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU8.call_mut_loop
        d { start := 0#usize, «end» := 8#usize } g i 0#u8 =
      loop (fun x =>
        garble.Garble.to_share.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU8.call_mut_loop.body
          d g i x.1 x.2) ({ start := 0#usize, «end» := 8#usize }, 0#u8) from rfl]
  rw [to_share_loop_eq d g i m hg hi 8 { start := 0#usize, «end» := 8#usize } 0#u8
    (by simp [usize_eight_val]) (by simp [usize_eight_val]) rfl]
  simp only [Bind.bind, Aeneas.Std.bind]
  rfl

/-- (curated) the extracted `Garble.to_share` bit-packs each output byte. -/
theorem garble_to_share_spec {N O : Type} (d : vole.VoleArray N Std.U8)
    (dO : vole.VoleArray O Std.U8)
    (divDict : core.ops.arith.Div N
      (typenum.uint.UInt (typenum.uint.UInt (typenum.uint.UInt (typenum.uint.UInt
        typenum.uint.UTerm typenum.bit.B1) typenum.bit.B0) typenum.bit.B0)
      typenum.bit.B0) O)
    (m mo : Std.Usize)
    (hsize : d.arrayArraySizeInst.typenummarker_traitsUnsignedInst.USIZE = ok m)
    (hsizeO : dO.arrayArraySizeInst.typenummarker_traitsUnsignedInst.USIZE = ok mo)
    (hdiv : mo.val * 8 = m.val)
    (g : garble.Garble N)
    (hgl : (vecL g.base.data).length = m.val) :
    garble.Garble.to_share d dO divDict g
      ⦃ r => vecL r.base.data = List.ofFn (fun j : Fin mo.val =>
          ⟨bitPackBvFrom (vecL g.base.data) j.val 0 (0#u8).bv⟩) ⦄ := by
  simp only [garble.Garble.to_share]
  apply spec_bind (from_fn_spec dO.arrayArraySizeInst
    (garble.Garble.to_share.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU8 d dO divDict)
    mo hsizeO g
    (fun j => ⟨bitPackBvFrom (vecL g.base.data) j 0 (0#u8).bv⟩)
    (by
      intro i hi
      exact Garble_to_share_closure_spec d dO divDict m g i hgl (by omega)))
  intro a ha
  rw [spec_ok]
  exact ha

