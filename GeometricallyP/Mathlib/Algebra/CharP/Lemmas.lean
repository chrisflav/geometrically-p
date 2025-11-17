import Mathlib.Algebra.CharP.Lemmas

instance Subsingleton.charP (R : Type*) [AddMonoidWithOne R] [Subsingleton R] : CharP R 1 :=
  ⟨fun x ↦ by simpa using eq_zero (x : R)⟩

/-- If `R` has an exponential characteristic, it is nontrivial. -/
lemma Nontrivial.of_expChar (R : Type*) [AddMonoidWithOne R] (q : ℕ) [hq : ExpChar R q] :
    Nontrivial R := by
  cases hq with
  | zero => infer_instance
  | prime hq =>
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    exact hq.ne_one (CharP.eq R ‹_› h.charP)
