/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import GeometricallyP.Algebra.Irreducible

/-!
# Connectedness of prime spectrum

In this file we show some results on connectedness of the prime spectrum of a ring.
-/

universe v u

open TensorProduct Algebra

variable {k : Type u} {R : Type*} [Field k] [CommRing R] [Algebra k R]

/-- The set of idempotent elements of a multiplicative structure. -/
abbrev idempotents (R : Type*) [Mul R] : Set R :=
  { e | IsIdempotentElem e}

/-- If every idempotent is trivial, then `Spec R` is connected. -/
lemma PrimeSpectrum.preconnectedSpace_of_forall_isIdempotentElem
    (H : ∀ e : R, IsIdempotentElem e → e = 0 ∨ e = 1) :
    PreconnectedSpace (PrimeSpectrum R) :=
    by
    wlog nt:  Nontrivial R
    · push_neg at nt
      apply PrimeSpectrum.isEmpty_iff_subsingleton.mpr at nt
      infer_instance
    apply preconnectedSpace_iff_clopen.mpr
    · intro s hs
      apply PrimeSpectrum.isClopen_iff.mp at hs
      obtain ⟨e, he⟩ := hs
      obtain ⟨h1, h2⟩ := he
      apply H at h1
      obtain h0|hf := h1
      · left
        rw [h2, h0]
        simp
      · right
        rw [h2, hf]
        simp

lemma PrimeSpectrum.basicOpen_eq_top_iff (f : R) : basicOpen f = ⊤ ↔ IsUnit f := by
  rw [← TopologicalSpace.Opens.coe_inj, basicOpen_eq_zeroLocus_compl]
  simp only [TopologicalSpace.Opens.coe_top, Set.compl_univ_iff]
  constructor
  · intro h
    apply Ideal.span_singleton_eq_top.mp
    rw [← PrimeSpectrum.zeroLocus_span {f}] at h
    exact PrimeSpectrum.zeroLocus_empty_iff_eq_top.mp h
  · intro x
    rw [← PrimeSpectrum.zeroLocus_span {f}]
    apply PrimeSpectrum.zeroLocus_empty_of_one_mem
    simp only [SetLike.mem_coe]
    have :  Ideal.span {f} = ⊤ := by
      exact Ideal.span_singleton_eq_top.mpr x
    simp [this]

lemma PrimeSpectrum.preconnectedSpace_iff_idempotents_eq :
    PreconnectedSpace (PrimeSpectrum R) ↔ idempotents R = {0, 1} :=
    by
    constructor
    · intro h
      apply preconnectedSpace_iff_clopen.mp at h
      simp_rw [PrimeSpectrum.isClopen_iff] at h
      apply Set.Subset.antisymm
      · intro e he
        have he1: IsIdempotentElem e := by simpa
        specialize h (PrimeSpectrum.basicOpen e) ⟨e, he, rfl⟩
        obtain h1|h2 := h
        · have : e = 0 := by
            rw [← Set.bot_eq_empty] at h1
            have h2 : IsNilpotent e := by
              apply (PrimeSpectrum.basicOpen_eq_bot_iff e).mp
              ext1
              exact h1
            exact IsNilpotent.eq_zero_of_isIdempotentElem he1 h2
          left
          exact this
        · have : e = 1 := by
            rw [← Set.top_eq_univ] at h2
            have h3 : IsUnit e := by
              apply (PrimeSpectrum.basicOpen_eq_top_iff e).mp
              ext1
              exact h2
            exact (IsUnit.mul_eq_left h3).mp he
          right
          exact this
      · intro e
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_setOf_eq]
        intro h
        obtain h1|h2 := h
        · rw [h1]
          exact IsIdempotentElem.zero
        · rw [h2]
          exact IsIdempotentElem.one
    · intro h
      apply PrimeSpectrum.preconnectedSpace_of_forall_isIdempotentElem
      intro e he
      have : e ∈ ({0,1} : Set R) := by
        rwa [← h]
      simpa using this

lemma PrimeSpectrum.connectedSpace_of_forall_connectedSpace_of_isSeparable
    (H : ∀ (K : Type v) [Field K] [Algebra k K] [Module.Finite k K] [Algebra.IsSeparable k K],
      ConnectedSpace (PrimeSpectrum (K ⊗[k] R)))
    (Ω : Type v) [Field Ω] [Algebra k Ω] [Algebra.IsSeparable k Ω] :
    ConnectedSpace (PrimeSpectrum (Ω ⊗[k] R)) :=
  /-
  Use `eq_zero_or_eq_one_of_isIdempotentElem_of_forall_isSeparable`
  -/
  sorry

@[stacks 037R]
lemma PrimeSpectrum.connectedSpace_tensorProduct_of_isSepClosed [IsSepClosed k] {S : Type*}
    [CommRing S] [Algebra k S] (hR : ConnectedSpace (PrimeSpectrum R))
    (hS : ConnectedSpace (PrimeSpectrum S)) : ConnectedSpace (PrimeSpectrum (R ⊗[k] S)) :=
  -- use `PrimeSpectrum.irreducibleSpace_tensorProduct_of_isSepClosed`
  sorry

lemma PrimeSpectrum.connectedSpace_of_faithfullyFlat {S : Type*} [CommRing S] [Algebra R S]
    [Module.FaithfullyFlat R S] [ConnectedSpace (PrimeSpectrum S)] :
    ConnectedSpace (PrimeSpectrum R) :=
  /-
  use `PrimeSpectrum.specComap_surjective_of_faithfullyFlat`
  -/
  sorry

lemma PrimeSpectrum.connectedSpace_of_isScalarTower (K L : Type*) [Field K] [Field L]
    [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [ConnectedSpace (PrimeSpectrum (L ⊗[k] R))] :
    ConnectedSpace (PrimeSpectrum (K ⊗[k] R)) :=
  -- uses `PrimeSpectrum.connectedSpace_of_faithfullyFlat`
  sorry
