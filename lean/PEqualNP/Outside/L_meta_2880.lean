import Mathlib.Order.Preorder.Finite
import Mathlib.Data.List.GetD
import Mathlib.Data.Bool.Basic
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2880

open PEqualNP.CircuitLowerBounds

-- Gate-fold monotonicity below is adapted from this repository's L_meta_1082.
def stp (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem eval_eq (C : Circuit) (x : List Bool) :
    C.eval x = (C.gates.foldl stp x).getD C.output false := rfl

theorem getD_snoc (W : List Bool) (v : Bool) (i : ℕ) :
    (W ++ [v]).getD i false = if i = W.length then v else W.getD i false := by
  rcases lt_trichotomy i W.length with h | h | h
  · rw [ite_eq_right (by omega)]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]
  · subst h
    simp [List.getD_eq_getElem?_getD]
  · rw [ite_eq_right (by omega)]
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by omega)]

theorem ev_and (g : Gate) (f : ℕ → Bool) (h : g.op = GateOp.and) :
    (g.op.eval (g.inputs.map f) = true ↔ ∀ i ∈ g.inputs, f i = true) := by
  rw [h]
  simp [GateOp.eval]

theorem ev_or (g : Gate) (f : ℕ → Bool) (h : g.op = GateOp.or) :
    (g.op.eval (g.inputs.map f) = true ↔ ∃ i ∈ g.inputs, f i = true) := by
  rw [h]
  simp [GateOp.eval]

-- AND and OR gates are monotone: a wire true on the smaller run is true on the larger
theorem mono : ∀ (gs : List Gate) (W1 W2 : List Bool), W1.length = W2.length →
    (∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) →
    (∀ i, W1.getD i false = true → W2.getD i false = true) →
    ∀ i, (gs.foldl stp W1).getD i false = true → (gs.foldl stp W2).getD i false = true := by
  intro gs
  induction gs with
  | nil => intro W1 W2 _ _ H; simpa using H
  | cons g gs ih =>
    intro W1 W2 hl hop H
    rw [List.foldl_cons, List.foldl_cons]
    apply ih (stp W1 g) (stp W2 g) (by simp [stp, hl])
      (fun g' hg' => hop g' (List.mem_cons_of_mem _ hg'))
    intro i
    simp only [stp, getD_snoc, hl]
    split_ifs
    · rcases hop g List.mem_cons_self with ha | ho
      · rw [ev_and g _ ha, ev_and g _ ha]
        intro h k hk
        exact H k (h k hk)
      · rw [ev_or g _ ho, ev_or g _ ho]
        rintro ⟨k, hk, h⟩
        exact ⟨k, hk, H k h⟩
    · exact H i

-- The bitwise order on Fin n -> Bool extends to out-of-range reads,
-- which evaluate to false on both sides.
theorem ofFn_le {n : ℕ} {x y : Fin n → Bool} (hxy : x ≤ y) :
    ∀ i : ℕ, (List.ofFn x).getD i false = true →
      (List.ofFn y).getD i false = true := by
  intro i hi
  by_cases h : i < n
  · have hbit := hxy (⟨i, h⟩ : Fin n)
    rw [Bool.le_iff_imp] at hbit
    simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, h, dite_true,
      Option.getD_some] at hi ⊢
    exact hbit hi
  · have hx : (List.ofFn x).length ≤ i := by
      simpa only [List.length_ofFn] using Nat.le_of_not_gt h
    rw [List.getD_eq_default _ _ hx] at hi
    exact Bool.noConfusion hi

theorem monotone_eval {n : ℕ} (C : Circuit) (hC : PEqualNP.MetaComplexity.Monotone2 C)
    {x y : Fin n → Bool} (hxy : x ≤ y) :
    C.eval (List.ofFn x) = true → C.eval (List.ofFn y) = true := by
  have hop (g : Gate) (hg : g ∈ C.gates) : g.op = GateOp.and ∨ g.op = GateOp.or := by
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using (hC g hg).1
  rw [eval_eq, eval_eq]
  exact mono C.gates (List.ofFn x) (List.ofFn y) (by simp) hop (ofFn_le hxy) C.output

end PEqualNP.Outside.L_meta_2880

open PEqualNP.Outside.L_meta_2880 in
theorem PEqualNP.Outside.L_meta_2880 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x2 → ∀ (x4 : (Fin x1 → Bool) → Prop), (∀ (x5 : Fin x1 → Bool), Minimal x4 x5 → x2.eval (List.ofFn x5) = Bool.true) → (∀ (x6 : Fin x1 → Bool), Maximal (fun (x7 : Fin x1 → Bool) => ¬x4 x7) x6 → x2.eval (List.ofFn x6) = Bool.false) → ∀ (x7 : Fin x1 → Bool), x2.eval (List.ofFn x7) = Bool.true ↔ x4 x7 := by
  classical
  intro n C hC P hmin hmax x
  constructor
  · intro hx
    by_contra hP
    obtain ⟨z, hxz, hz⟩ :=
      Finite.exists_le_maximal (p := fun z : Fin n → Bool => ¬ P z) hP
    have hzTrue := monotone_eval C hC hxz hx
    rw [hmax z hz] at hzTrue
    exact Bool.noConfusion hzTrue
  · intro hP
    obtain ⟨y, hyx, hy⟩ := Finite.exists_le_minimal (p := P) hP
    exact monotone_eval C hC hyx (hmin y hy)
