/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import GeometricallyP.Algebra.TensorProduct
import GeometricallyP.Mathlib.Topology.Homeomorph.Lemmas
import GeometricallyP.Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Spectrum.Prime.Homeomorph

/-!
# Irreducibility of prime spectrum

In this file we show some results on irreducibility of the prime spectrum of a ring.

-/

universe u

open TensorProduct Algebra

variable {k : Type u} {R : Type*} [Field k] [CommRing R] [Algebra k R]

/-- `Spec R` is preirreducible if and only if `R` has at most one minimal prime. -/
lemma PrimeSpectrum.preirreducibleSpace_iff {R : Type*} [CommSemiring R] :
    PreirreducibleSpace (PrimeSpectrum R) ↔ (minimalPrimes R).Subsingleton := by
  rw [preirreducibleSpace_iff_subsingleton_irreducibleComponents]
  simpa [Set.subsingleton_coe, OrderDual] using
    (minimalPrimes.equivIrreducibleComponents R).symm.subsingleton_congr

/-- `Spec R` is irreducible if and only if `R` has a unique minimal prime. -/
lemma PrimeSpectrum.irreducibleSpace_iff {R : Type*} [CommSemiring R] :
    IrreducibleSpace (PrimeSpectrum R) ↔
      Nontrivial R ∧ (minimalPrimes R).Subsingleton := by
  rw [irreducibleSpace_iff_nonempty_and_subsingleton, PrimeSpectrum.nonempty_iff_nontrivial]
  congr!
  have h1 := (minimalPrimes.equivIrreducibleComponents R).symm.subsingleton_congr
  simp only [OrderDual, Set.subsingleton_coe] at h1
  rw [h1]

lemma Ideal.IsPrime.nontrivial {R : Type*} [Semiring R]
    {I : Ideal R} (hI : I.IsPrime) : Nontrivial R :=
  nontrivial_of_ne 1 0 (fun h ↦ hI.1 <| (eq_top_iff_one I).mpr (h ▸ I.zero_mem))

lemma RingHom.isIntegral_algebraMap_iff {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] :
    (algebraMap R S).IsIntegral ↔ Algebra.IsIntegral R S := by
  simp_rw [Algebra.isIntegral_def, RingHom.IsIntegral, _root_.IsIntegral]

lemma Algebra.TensorProduct.isIntegral_includeRight (R S T : Type*) [CommRing R] [CommRing S]
    [Algebra R S] [CommRing T] [Algebra R T] [Algebra.IsIntegral R T] :
    (Algebra.TensorProduct.includeRight : S →ₐ[R] T ⊗[R] S).IsIntegral :=
  have : (Algebra.TensorProduct.includeRight : S →ₐ[R] T ⊗[R] S) =
      (Algebra.TensorProduct.comm ..).toAlgHom.comp (IsScalarTower.toAlgHom R S _) := rfl
  this ▸ RingHom.IsIntegral.trans _ _
    (RingHom.isIntegral_algebraMap_iff.mpr <| Algebra.IsIntegral.tensorProduct R S T)
    (RingHom.isIntegral_of_surjective _ (AlgEquiv.surjective _))

/-- If `Spec (K ⊗[k] R)` is irreducible for every finite, separable extension `K` of `k`,
the same holds for `Spec (Ω ⊗[k] R)` for every separable extension `Ω` of `k`. -/
lemma PrimeSpectrum.irreducibleSpace_of_isSeparable
    (H : ∀ (K : Type u) [Field K] [Algebra k K] [Module.Finite k K] [Algebra.IsSeparable k K],
      IrreducibleSpace (PrimeSpectrum (K ⊗[k] R))) (Ω : Type u) [Field Ω] [Algebra k Ω]
      [Algebra.IsSeparable k Ω] :
    IrreducibleSpace (PrimeSpectrum (Ω ⊗[k] R)) :=
  have : Nontrivial R := by
    convert (Algebra.TensorProduct.lid k R).symm.toRingHom.domain_nontrivial
    rw [← PrimeSpectrum.nonempty_iff_nontrivial]
    exact (H k).2
  have : PreirreducibleSpace (PrimeSpectrum (Ω ⊗[k] R)) := by
    rw [PrimeSpectrum.preirreducibleSpace_iff]
    simp_rw [PrimeSpectrum.irreducibleSpace_iff] at H
    apply subsingleton_minimalPrimes_of_isSeparable
    intro K _ _ _ _
    exact (H K).2
  ⟨((Algebra.TensorProduct.isIntegral_includeRight k R Ω).specComap_surjective <|
    Algebra.TensorProduct.includeRight_injective (algebraMap k Ω).injective).nonempty⟩

lemma PrimeSpectrum.comap_quotientMk_surjective_of_le_nilradical {R : Type*} [CommRing R]
    (I : Ideal R) (hle : I ≤ nilradical R) :
    Function.Surjective (PrimeSpectrum.comap <| Ideal.Quotient.mk I) := by
  simpa [← Set.range_eq_univ, range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective,
    zeroLocus_eq_univ_iff]

lemma PrimeSpectrum.irreducibleSpace_iff_of_isPurelyInseparable
    (k R : Type*) [CommRing R] [Field k] [Algebra k R]
    (K : Type*) [Field K] [Algebra k K]
    (L : Type*) [Field L] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [IsPurelyInseparable K L] :
    IrreducibleSpace (PrimeSpectrum (K ⊗[k] R)) ↔ IrreducibleSpace (PrimeSpectrum (L ⊗[k] R)) := by
  have e := isHomeomorph_comap_tensorProductMap_of_isPurelyInseparable K k R L
  refine ⟨fun h ↦ (e.homeomorph).symm.isHomeomorph.irreducibleSpace, fun h ↦ e.irreducibleSpace⟩

lemma PrimeSpectrum.irreducibleSpace_iff_of_isAlgClosure_of_isSepClosure
    (k R : Type*) [CommRing R] [Field k] [Algebra k R]
    (K : Type*) [Field K] [Algebra k K] [IsSepClosure k K]
    (L : Type*) [Field L] [Algebra k L] [IsAlgClosure k L] :
    IrreducibleSpace (PrimeSpectrum (K ⊗[k] R)) ↔ IrreducibleSpace (PrimeSpectrum (L ⊗[k] R)) := by
  obtain ⟨inst, _, h⟩ := exists_algebra_isPurelyInseparable_of_isSepClosure_of_isAlgClosure k K L
  rw [PrimeSpectrum.irreducibleSpace_iff_of_isPurelyInseparable k R K L]

@[stacks 00I7 "For domains of finite type over `k`."]
private lemma PrimeSpectrum.irreducibleSpace_tensorProduct_of_isAlgClosed_aux [IsAlgClosed k]
    {S : Type*} [CommRing S] [Algebra k S] [Algebra.FiniteType k S]
    [IsDomain S] [Algebra.FiniteType k R] [IsDomain R]
    (hR : IrreducibleSpace (PrimeSpectrum R))
    (hS : IrreducibleSpace (PrimeSpectrum S)) :
    IrreducibleSpace (PrimeSpectrum (R ⊗[k] S)) :=
  sorry

example {R S A B : Type*} [CommRing R] [CommRing A] [CommRing S] [CommRing B]
    [Algebra R S] [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B] :
    Algebra (A ⊗[R] S) (B ⊗[R] S) :=
  RingHom.toAlgebra <| AlgHom.toRingHom <|
    Algebra.TensorProduct.map (IsScalarTower.toAlgHom R A B) (AlgHom.id R S)

lemma isDomain_iff_isReduced_and_irreducibleSpace {R : Type*} [CommRing R] :
    IsDomain R ↔ IsReduced R ∧ IrreducibleSpace (PrimeSpectrum R) :=
  sorry

@[stacks 00I7 "For algebraically closed fields."]
lemma PrimeSpectrum.irreducibleSpace_tensorProduct_of_isAlgClosed [IsAlgClosed k] {S : Type*}
    [CommRing S] [Algebra k S] (hR : IrreducibleSpace (PrimeSpectrum R))
    (hS : IrreducibleSpace (PrimeSpectrum S)) : IrreducibleSpace (PrimeSpectrum (R ⊗[k] S)) :=
  -- use `PrimeSpectrum.irreducibleSpace_tensorProduct_of_isAlgClosed_aux`
  -- to replace `R` and `S` by their reductions use
  -- `PrimeSpectrum.irreducibleSpace_tensorProduct_of_isAlgClosed_aux`
  -- and `PrimeSpectrum.isClosedEmbedding_comap_of_surjective`
  -- then use `isDomain_iff_isReduced_and_irreducibleSpace`
  -- and `Algebra.IsGeometricallyReduced.isReduced_tensorProduct`
  sorry

@[stacks 00I7]
lemma PrimeSpectrum.irreducibleSpace_tensorProduct_of_isSepClosed [IsSepClosed k] {S : Type*}
    [CommRing S] [Algebra k S] (hR : IrreducibleSpace (PrimeSpectrum R))
    (hS : IrreducibleSpace (PrimeSpectrum S)) : IrreducibleSpace (PrimeSpectrum (R ⊗[k] S)) :=
  -- use `PrimeSpectrum.irreducibleSpace_tensorProduct_of_isAlgClosed`
  -- Bryan
  sorry

lemma PrimeSpectrum.irreducibleSpace_of_faithfullyFlat {S : Type*} [CommRing S] [Algebra R S]
    [Module.FaithfullyFlat R S] [IrreducibleSpace (PrimeSpectrum S)] :
    IrreducibleSpace (PrimeSpectrum R) :=
  /-
  use `PrimeSpectrum.specComap_surjective_of_faithfullyFlat`
  and `Function.Surjective.preirreducibleSpace`
  -/
  -- Timo
  sorry

lemma PrimeSpectrum.irreducibleSpace_of_isScalarTower (K L : Type*) [Field K] [Field L]
    [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [IrreducibleSpace (PrimeSpectrum (L ⊗[k] R))] :
    IrreducibleSpace (PrimeSpectrum (K ⊗[k] R)) :=
  -- uses `PrimeSpectrum.irreducibleSpace_of_faithfullyFlat`
  -- Timo
  sorry
