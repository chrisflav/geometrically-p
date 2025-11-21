/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import GeometricallyP.Algebra.TensorProduct
import GeometricallyP.Mathlib.Topology.Homeomorph.Lemmas
import GeometricallyP.Mathlib.RingTheory.Nilpotent.GeometricallyReduced
import GeometricallyP.Mathlib.FieldTheory.PurelyInseparable.Basic
import GeometricallyP.Mathlib.RingTheory.Spectrum.Prime.RingHom
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Spectrum.Prime.Homeomorph
import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
import GeometricallyP.Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Spectrum.Prime.Jacobson
import Mathlib.RingTheory.Spectrum.Prime.Chevalley
import Mathlib.RingTheory.FiniteStability

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

lemma PrimeSpectrum.irreducibleSpace_iff_of_ringEquiv
    {R S : Type*} [CommSemiring R] [CommSemiring S]
    (e : R ≃+* S) :
    IrreducibleSpace (PrimeSpectrum R) ↔ IrreducibleSpace (PrimeSpectrum S) :=
  ⟨fun _ ↦ (PrimeSpectrum.homeomorphOfRingEquiv e).isHomeomorph.irreducibleSpace,
  fun _ ↦ (PrimeSpectrum.homeomorphOfRingEquiv e.symm).isHomeomorph.irreducibleSpace⟩

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

lemma PrimeSpectrum.irreducibleSpace_iff_of_isAlgClosure_of_isSepClosed
    (k R : Type*) [CommRing R] [Field k] [Algebra k R]
    [IsSepClosed k]
    (L : Type*) [Field L] [Algebra k L] [IsAlgClosure k L] :
    IrreducibleSpace (PrimeSpectrum R) ↔ IrreducibleSpace (PrimeSpectrum (L ⊗[k] R)) :=
  (irreducibleSpace_iff_of_ringEquiv (Algebra.TensorProduct.lid k R).symm.toRingEquiv).trans
    (irreducibleSpace_iff_of_isAlgClosure_of_isSepClosure k R k L)

noncomputable def PrimeSpectrum.algEquiv_residueField_of_isAlgClosed
    [IsAlgClosed k] [Algebra.FiniteType k R]
    (p : PrimeSpectrum R) [hp : p.asIdeal.IsMaximal] :
    k ≃ₐ[k] p.asIdeal.ResidueField :=
  let e₁ :=
    (AlgEquiv.ofBijective _ p.asIdeal.bijective_algebraMap_quotient_residueField).restrictScalars k
  let : Field (R ⧸ p.asIdeal) := Ideal.Quotient.field _
  have : Module.Finite k (R ⧸ p.asIdeal) :=
    finite_of_finite_type_of_isJacobsonRing k (R ⧸ p.asIdeal)
  let e₀ : k ≃ₐ[k] (R ⧸ p.asIdeal) :=
    (AlgEquiv.ofBijective (ofId _ _) IsAlgClosed.algebraMap_bijective_of_isIntegral)
  e₀.trans e₁

open TensorProduct in
@[stacks 00I7 "For algebras of finite type over `k`."]
private lemma PrimeSpectrum.irreducibleSpace_tensorProduct_of_isAlgClosed_aux [IsAlgClosed k]
    {S : Type*} [CommRing S] [Algebra k S]
    [Algebra.FiniteType k R] [Algebra.FiniteType k S]
    (hR : IrreducibleSpace (PrimeSpectrum R))
    (hS : IrreducibleSpace (PrimeSpectrum S)) :
    IrreducibleSpace (PrimeSpectrum (R ⊗[k] S)) where
  isPreirreducible_univ := by
    have : IsJacobsonRing R := isJacobsonRing_of_finiteType (A := k)
    have hc : closure (closedPoints (PrimeSpectrum R)) = Set.univ := closure_closedPoints
    have h := hR.isIrreducible_univ.isPreirreducible.preimage_of_dense_isPreirreducible_fiber
      (X := PrimeSpectrum (R ⊗[k] S))
      (f := comap <| (algebraMap R (R ⊗[k] S)))
    simp only [Set.univ_inter, Set.univ_subset_iff, Set.preimage_univ] at h
    apply h
    · have : FinitePresentation R (R ⊗[k] S) :=
        have : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing k R
        FinitePresentation.of_finiteType.mp (inferInstance)
      apply isOpenMap_comap_of_hasGoingDown_of_finitePresentation
    · rw [← dense_iff_closure_eq] at hc ⊢
      refine hc.mono (fun p hp ↦ ?_)
      rw [mem_closedPoints_iff, isClosed_singleton_iff_isMaximal p] at hp
      have : IrreducibleSpace (PrimeSpectrum ((R ⊗[k] S) ⊗[R] p.asIdeal.ResidueField)) :=
        let e₀ : (p.asIdeal.ResidueField ⊗[R] (R ⊗[k] S)) ≃+* (p.asIdeal.ResidueField ⊗[k] S) :=
          (cancelBaseChange _ _ R _ _).toRingEquiv
        let e₁ : (p.asIdeal.ResidueField ⊗[k] S) ≃+* S :=
          (Algebra.TensorProduct.congr (algEquiv_residueField_of_isAlgClosed p).symm
            AlgEquiv.refl).trans (Algebra.TensorProduct.lid k S)
        (irreducibleSpace_iff_of_ringEquiv <|
          (Algebra.TensorProduct.comm R _ p.asIdeal.ResidueField).toRingEquiv.trans <|
          e₀.trans e₁).mpr hS
      simpa [comap, preimage_eq_range_tensor_residueField R (R ⊗[k] S) p] using
        this.isPreirreducible_univ.image _ <| continuousOn_univ.mpr (comap _).continuous_toFun
  toNonempty :=
    have := (irreducibleSpace_iff.mp hR).1
    have := (irreducibleSpace_iff.mp hS).1
    have := nontrivial_of_algebraMap_injective_of_flat_left k R S (RingHom.injective _)
    inferInstance

lemma minimalPrimes_eq_singleton_nilradical {R : Type*} [CommRing R]
    [IrreducibleSpace (PrimeSpectrum R)] :
    minimalPrimes R = {nilradical R} := by
  have : (minimalPrimes R).Nonempty ∧ (minimalPrimes R).Subsingleton := by
    constructor
    · have : Nontrivial R := by
        exact (PrimeSpectrum.irreducibleSpace_iff.mp inferInstance).1
      have h : (⊥ : Ideal R) ≠ ⊤ := by
        exact bot_ne_top
      rw [← Set.nonempty_coe_sort]
      exact Ideal.nonempty_minimalPrimes h
    · exact (PrimeSpectrum.irreducibleSpace_iff.mp inferInstance).2
  rw [← Set.exists_eq_singleton_iff_nonempty_subsingleton] at this
  obtain ⟨I, hI⟩ := this
  rw [hI, Set.singleton_eq_singleton_iff, nilradical, Submodule.zero_eq_bot,
    ← Ideal.sInf_minimalPrimes, ← minimalPrimes, hI]
  simp

/-- A ring is a domain if and only if it is reduced and its prime spectrum
is irreducible. -/
lemma isDomain_iff_isReduced_and_irreducibleSpace {R : Type*} [CommRing R] :
    IsDomain R ↔ IsReduced R ∧ IrreducibleSpace (PrimeSpectrum R) := by
  constructor
  · intro h
    constructor
    · infer_instance
    exact PrimeSpectrum.irreducibleSpace
  · intro h
    obtain ⟨hred, hirr⟩ := h
    have h1 : (minimalPrimes R) = {(⊥ : Ideal R)} := by
      rw [minimalPrimes_eq_singleton_nilradical]
      simp
    have h_in : (⊥ : Ideal R) ∈ (minimalPrimes R) := by
      rw [h1]
      simp
    have hbp2 :(⊥ : Ideal R).IsPrime := by
      apply Ideal.minimalPrimes_isPrime (h_in)
    exact IsDomain.of_bot_isPrime R

/-- If `Spec R` is irreducible and `S` is an `R`-algebra such that the induced
map `Spec S → Spec R` is open and for a dense set of primes `p` of `R`, the fibre
`Spec (S ⊗[R] κ(p))` is irreducible, then `Spec S` is irreducible. -/
lemma PrimeSpectrum.irreducibleSpace_of_isOpenMap_of_dense
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [IrreducibleSpace (PrimeSpectrum R)]
    (hf : IsOpenMap (PrimeSpectrum.comap <| algebraMap R S))
    {s : Set (PrimeSpectrum R)} (hs : Dense s)
    (H : ∀ p ∈ s,
      IrreducibleSpace (PrimeSpectrum <| S ⊗[R] p.asIdeal.ResidueField)) :
    IrreducibleSpace (PrimeSpectrum S) :=
  -- use ...
  sorry

noncomputable def homeomorph_ofClosedDenseEmbedding {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] (f : X → Y) (hfc : Topology.IsClosedEmbedding f)
    (hfd : DenseRange f) : X ≃ₜ Y := by
  apply IsHomeomorph.homeomorph f
  rw [isHomeomorph_iff_continuous_isClosedMap_bijective]
  refine ⟨hfc.continuous, hfc.isClosedMap, ⟨hfc.injective, ?_⟩⟩
  rwa [DenseRange, dense_iff_closure_eq, IsClosed.closure_eq, Set.range_eq_univ] at hfd
  exact hfc.isClosedMap.isClosed_range

lemma geo_reduced_iff_reduce_alg_closed {k R : Type*} [Field k] [IsAlgClosed k]
  [CommRing R] [Algebra k R] [IsReduced R] : IsGeometricallyReduced k R where
    isReduced_algebraicClosure_tensorProduct := by
      let triv : k ≃ₐ[k] AlgebraicClosure k :=
        AlgEquiv.ofBijective (Algebra.ofId k (AlgebraicClosure k))
        (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := k) (K := (AlgebraicClosure k)))
      let : R ≃ₐ[k] R := AlgEquiv.refl
      have : (AlgebraicClosure k ⊗[k] R) ≃ₐ[k] R :=
        AlgEquiv.trans (Algebra.TensorProduct.congr triv.symm this) (Algebra.TensorProduct.lid k R)
      exact isReduced_of_injective this this.injective

@[stacks 00I7 "For algebraically closed fields."]
lemma PrimeSpectrum.irreducibleSpace_tensorProduct_of_isAlgClosed [IsAlgClosed k] {S : Type*}
    [CommRing S] [Algebra k S] (hR : IrreducibleSpace (PrimeSpectrum R))
    (hS : IrreducibleSpace (PrimeSpectrum S)) : IrreducibleSpace (PrimeSpectrum (R ⊗[k] S)) := by
  letI Rred := R ⧸ nilradical R
  letI Sred := S ⧸ nilradical S
  let : Algebra (R ⊗[k] S) (Rred ⊗[k] Sred) := RingHom.toAlgebra <|
    Algebra.TensorProduct.map (IsScalarTower.toAlgHom k R Rred) (IsScalarTower.toAlgHom k S Sred)
  let : IsReduced Rred := by
    rw [← Ideal.isRadical_iff_quotient_reduced]
    exact Ideal.radical_isRadical ⊥
  let : IsReduced Sred := by
    rw [← Ideal.isRadical_iff_quotient_reduced]
    exact Ideal.radical_isRadical ⊥

  let denseR : DenseRange ⇑(PrimeSpectrum.comap (algebraMap R Rred)) := by
    simp [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical, Rred]
  let denseS : DenseRange ⇑(PrimeSpectrum.comap (algebraMap S Sred)) := by
    simp [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical, Sred]
  let denseRtS : DenseRange ⇑(PrimeSpectrum.comap (algebraMap (R ⊗[k] S) (Rred ⊗[k] Sred))) := by
    rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical, RingHom.algebraMap_toAlgebra,
      RingHom.ker_coe_toRingHom, Algebra.TensorProduct.map_ker]
    · simp [Rred, Sred]
      · apply And.intro
        · rw [← RingHom.ker_coe_toRingHom]
          simpa using Ideal.map_nilradical_le _
        · rw [← RingHom.ker_coe_toRingHom]
          simpa using Ideal.map_nilradical_le _
    · apply Ideal.Quotient.mk_surjective
    · apply Ideal.Quotient.mk_surjective

  let homeoR : PrimeSpectrum Rred ≃ₜ PrimeSpectrum R :=
    (homeomorph_ofClosedDenseEmbedding ⇑(PrimeSpectrum.comap (algebraMap R Rred))
      (PrimeSpectrum.isClosedEmbedding_comap_of_surjective Rred (algebraMap R Rred)
        Ideal.Quotient.mk_surjective)
      denseR)
  let homeoS : PrimeSpectrum Sred ≃ₜ PrimeSpectrum S :=
    (homeomorph_ofClosedDenseEmbedding ⇑(PrimeSpectrum.comap (algebraMap S Sred))
      (PrimeSpectrum.isClosedEmbedding_comap_of_surjective Sred (algebraMap S Sred)
        Ideal.Quotient.mk_surjective)
      denseS)
  let homeoRredtSred : PrimeSpectrum (Rred ⊗[k] Sred) ≃ₜ PrimeSpectrum (R ⊗[k] S) :=
    (homeomorph_ofClosedDenseEmbedding
      ⇑(PrimeSpectrum.comap (algebraMap (R ⊗[k] S) (Rred ⊗[k] Sred)))
      (PrimeSpectrum.isClosedEmbedding_comap_of_surjective (Rred ⊗[k] Sred)
        (algebraMap (R ⊗[k] S) (Rred ⊗[k] Sred)) ?_)
      denseRtS)
  · let : IrreducibleSpace (PrimeSpectrum Rred) := homeoR.symm.isHomeomorph.irreducibleSpace
    let : IrreducibleSpace (PrimeSpectrum Sred) := homeoS.symm.isHomeomorph.irreducibleSpace
    let : IsDomain Rred := by
      rw [isDomain_iff_isReduced_and_irreducibleSpace]
      exact ⟨inferInstance, inferInstance⟩
    let : IsDomain Sred := by
      rw [isDomain_iff_isReduced_and_irreducibleSpace]
      exact ⟨inferInstance, inferInstance⟩
    let domain : IsDomain (Rred ⊗[k] Sred) := isDomain_tensorProduct_of_forall_isDomain_of_FG ?_
    · exact homeoRredtSred.isHomeomorph.irreducibleSpace
    intro S T Sfg Tfg
    have : Algebra.FiniteType k S := by simp [← Subalgebra.fg_iff_finiteType, Sfg]
    have : Algebra.FiniteType k T := by simp [← Subalgebra.fg_iff_finiteType, Tfg]
    rw [isDomain_iff_isReduced_and_irreducibleSpace]
    have : IsGeometricallyReduced k T := geo_reduced_iff_reduce_alg_closed
    have : IsReduced (S ⊗[k] T) := Algebra.IsGeometricallyReduced.isReduced_tensorProduct
    exact ⟨inferInstance,
      PrimeSpectrum.irreducibleSpace_tensorProduct_of_isAlgClosed_aux inferInstance inferInstance⟩
  · rw [RingHom.algebraMap_toAlgebra]
    exact TensorProduct.map_surjective (Ideal.Quotient.mk_surjective) (Ideal.Quotient.mk_surjective)

@[stacks 00I7]
lemma PrimeSpectrum.irreducibleSpace_tensorProduct_of_isSepClosed [IsSepClosed k] {S : Type*}
    [CommRing S] [Algebra k S] (hR : IrreducibleSpace (PrimeSpectrum R))
    (hS : IrreducibleSpace (PrimeSpectrum S)) : IrreducibleSpace (PrimeSpectrum (R ⊗[k] S)) := by
  -- use `PrimeSpectrum.irreducibleSpace_tensorProduct_of_isAlgClosed`
  letI kbar := AlgebraicClosure k
  have hR' : IrreducibleSpace (PrimeSpectrum (kbar ⊗[k] R)) :=
    (irreducibleSpace_iff_of_isAlgClosure_of_isSepClosed k R _).mp hR
  have hS' : IrreducibleSpace (PrimeSpectrum (kbar ⊗[k] S)) :=
    (irreducibleSpace_iff_of_isAlgClosure_of_isSepClosed k S _).mp hS
  have hRS' := irreducibleSpace_tensorProduct_of_isAlgClosed (k := kbar) hR' hS'
  apply (irreducibleSpace_iff_of_isAlgClosure_of_isSepClosed k (R ⊗[k] S) kbar).mpr
  let e := (Algebra.TensorProduct.tensorTensorTensorComm k k kbar kbar kbar R kbar S).trans
    (Algebra.TensorProduct.congr (Algebra.TensorProduct.lid kbar kbar) AlgEquiv.refl)
  exact (PrimeSpectrum.homeomorphOfRingEquiv e.toRingEquiv).isHomeomorph.irreducibleSpace

lemma PrimeSpectrum.irreducibleSpace_of_faithfullyFlat (S : Type*) [CommRing S] [Algebra R S]
    [Module.FaithfullyFlat R S] [IrreducibleSpace (PrimeSpectrum S)] :
    IrreducibleSpace (PrimeSpectrum R) := by
  /-
  use `PrimeSpectrum.specComap_surjective_of_faithfullyFlat`
  and `Function.Surjective.preirreducibleSpace`
  -/
  let f := PrimeSpectrum.comap (algebraMap R S)
  have surj_f : Function.Surjective f := PrimeSpectrum.specComap_surjective_of_faithfullyFlat
  have : PreirreducibleSpace (PrimeSpectrum R) :=
    Function.Surjective.preirreducibleSpace f f.continuous surj_f
  have nonempty : Nonempty (PrimeSpectrum R) := ⟨f (Classical.arbitrary (PrimeSpectrum S))⟩
  constructor
  exact nonempty

lemma Module.FaithfullyFlat.of_isBaseChange {R S M N : Type*} [CommRing R] [CommRing S]
    [Algebra R S] [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module S N] [Module R N] [IsScalarTower R S N]
    {f : M →ₗ[R] N} (hf : IsBaseChange S f) [Module.FaithfullyFlat R M] :
    Module.FaithfullyFlat S N := by
  let e := hf.equiv
  apply Module.FaithfullyFlat.of_linearEquiv _ _ e.symm

attribute [local instance] TensorProduct.rightAlgebra in
lemma PrimeSpectrum.irreducibleSpace_of_isScalarTower (K L : Type*) [Field K] [Field L]
    [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [IrreducibleSpace (PrimeSpectrum (L ⊗[k] R))] :
    IrreducibleSpace (PrimeSpectrum (K ⊗[k] R)) := by
  -- uses `PrimeSpectrum.irreducibleSpace_of_faithfullyFlat`
  let f := Algebra.TensorProduct.map (IsScalarTower.toAlgHom k K L) (AlgHom.id k R)
  let algebra := RingHom.toAlgebra <| AlgHom.toRingHom <| f

  let g : L →ₐ[K] L ⊗[k] R := IsScalarTower.toAlgHom _ _ _
  have h : IsScalarTower K (K ⊗[k] R) (L ⊗[k] R) := IsScalarTower.of_algebraMap_eq (congrFun rfl)
  have : IsBaseChange (K ⊗[k] R) g.toLinearMap := by
    rw [← Algebra.isPushout_iff]
    let e' : L ⊗[K] (K ⊗[k] R) ≃ₐ[L] L ⊗[k] R := by
      apply Algebra.TensorProduct.cancelBaseChange
    have : IsScalarTower k (K ⊗[k] R) (L ⊗[K] (K ⊗[k] R)) := by
      apply IsScalarTower.of_algebraMap_eq
      intro x
      simp [TensorProduct.right_algebraMap_apply]
      rw [IsScalarTower.algebraMap_apply k K L x, TensorProduct.tmul_one_eq_one_tmul]
      simp
    have : (e'.toAlgHom.restrictScalars k).comp
        (IsScalarTower.toAlgHom k (K ⊗[k] R) (L ⊗[K] (K ⊗[k] R))) =
        IsScalarTower.toAlgHom _ _ _ := by
      ext
      · simp [e', RingHom.algebraMap_toAlgebra, f, Algebra.smul_def]
      simp [e', RingHom.algebraMap_toAlgebra, f, Algebra.smul_def]
    let e : L ⊗[K] (K ⊗[k] R) ≃ₐ[K ⊗[k] R] L ⊗[k] R := by
      apply AlgEquiv.ofRingEquiv (f := e'.toRingEquiv)
      intro x
      exact congr($this x)
    apply Algebra.IsPushout.of_equiv e
    ext
    simp [e, e', Algebra.TensorProduct.one_def]
  have : Module.FaithfullyFlat (K ⊗[k] R) (L ⊗[k] R) := by
    apply Module.FaithfullyFlat.of_isBaseChange this
  apply PrimeSpectrum.irreducibleSpace_of_faithfullyFlat (L ⊗[k] R)
