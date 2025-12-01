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

lemma subset_idempotents : {0, 1} ⊆ idempotents R := by
  simp [idempotents, Set.subset_def, IsIdempotentElem.zero, IsIdempotentElem.one]

/-- If every idempotent is trivial, then `Spec R` is connected. -/
lemma PrimeSpectrum.preconnectedSpace_of_forall_isIdempotentElem
    (H : ∀ e : R, IsIdempotentElem e → e = 0 ∨ e = 1) :
    PreconnectedSpace (PrimeSpectrum R) := by
  nontriviality R
  rw [preconnectedSpace_iff_clopen]
  intro s hs
  obtain ⟨e, he⟩ := PrimeSpectrum.isClopen_iff.mp hs
  obtain ⟨h, rfl⟩ := he
  cases H _ h <;> simp [*]

lemma PrimeSpectrum.basicOpen_eq_top_iff (f : R) : basicOpen f = ⊤ ↔ IsUnit f := by
  rw [← TopologicalSpace.Opens.coe_inj, basicOpen_eq_zeroLocus_compl,
    TopologicalSpace.Opens.coe_top, Set.compl_univ_iff]
  refine ⟨fun h ↦ ?_, fun x ↦ ?_⟩
  · rw [← Ideal.span_singleton_eq_top, ← PrimeSpectrum.zeroLocus_empty_iff_eq_top]
    rwa [← PrimeSpectrum.zeroLocus_span {f}] at h
  · rw [← PrimeSpectrum.zeroLocus_span {f}]
    simp [PrimeSpectrum.zeroLocus_empty_of_one_mem, Ideal.span_singleton_eq_top.mpr x]

lemma PrimeSpectrum.preconnectedSpace_iff_idempotents_subset :
    PreconnectedSpace (PrimeSpectrum R) ↔ idempotents R ⊆ {0, 1} := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · simp_rw [preconnectedSpace_iff_clopen, PrimeSpectrum.isClopen_iff] at h
    refine fun e he ↦ ?_
    have he1 : IsIdempotentElem e := by simpa
    obtain h1 | h2 := h (PrimeSpectrum.basicOpen e) ⟨e, he, rfl⟩
    · obtain rfl : e = 0 := by
        rw [← Set.bot_eq_empty] at h1
        have h2 : IsNilpotent e := by
          apply (PrimeSpectrum.basicOpen_eq_bot_iff e).mp
          ext1
          exact h1
        exact IsNilpotent.eq_zero_of_isIdempotentElem he1 h2
      simp
    · obtain rfl : e = 1 := by
        rw [← Set.top_eq_univ] at h2
        have h3 : IsUnit e := by
          apply (PrimeSpectrum.basicOpen_eq_top_iff e).mp
          ext1
          exact h2
        exact (IsUnit.mul_eq_left h3).mp he
      simp
  · apply PrimeSpectrum.preconnectedSpace_of_forall_isIdempotentElem
    intro e he
    exact h he

lemma PrimeSpectrum.preconnectedSpace_of_forall_connectedSpace_of_isSeparable
    (H : ∀ (K : Type v) [Field K] [Algebra k K] [Module.Finite k K] [Algebra.IsSeparable k K],
      PreconnectedSpace (PrimeSpectrum (K ⊗[k] R)))
    (Ω : Type v) [Field Ω] [Algebra k Ω] [Algebra.IsSeparable k Ω] :
    PreconnectedSpace (PrimeSpectrum (Ω ⊗[k] R)) := by
  simp_rw [PrimeSpectrum.preconnectedSpace_iff_idempotents_subset] at H ⊢
  exact eq_zero_or_eq_one_of_isIdempotentElem_of_forall_isSeparable H _

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
