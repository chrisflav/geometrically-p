/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import GeometricallyP.Geometry.Basic
import GeometricallyP.Algebra.GeometricallyIrreducible
import GeometricallyP.Mathlib.Topology.Irreducible
import GeometricallyP.Mathlib.AlgebraicGeometry.Scheme
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen

/-!
# Geometrically irreducible schemes over a field

A scheme `X` over a field `k` is geometrically irreducible if any base change `X_K`
for a field extension `K` of `k` is irreducible.
-/

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

lemma irreducibleSpace_of_isOpenImmersion {U X : Scheme.{u}} (i : U ⟶ X)
[IsOpenImmersion i] [Nonempty U]
    [IrreducibleSpace X] :
    IrreducibleSpace (U) := by
  let V := i.opensRange
  let h_iso_image : U ≅ V := i.isoOpensRange
  let h_nonempty_V : Set.Nonempty (V.1) := by
    let h: Nonempty V.1 := h_iso_image.inv.surjective.nonempty
    simp
    exact (Scheme.Opens.nonempty_iff V).mp h
  let isIrr_X : IsIrreducible (Set.univ : Set X.carrier) := by
    apply IrreducibleSpace.isIrreducible_univ
  let isIrr_V : IsIrreducible V.1 := by
    apply IsPreirreducible.subset_irreducible isIrr_X.isPreirreducible h_nonempty_V V.2 (by rfl)
    simp
  let h_irr_V : IrreducibleSpace (V) :=
    Subtype.irreducibleSpace isIrr_V
  apply h_iso_image.inv.surjective.irreducibleSpace
  exact h_iso_image.inv.continuous


lemma preIrreducibleSpace_of_isOpenImmersion {U X : Scheme.{u}} (i : U ⟶ X) [IsOpenImmersion i]
    [PreirreducibleSpace X] :
    PreirreducibleSpace (U) := by
  let V := i.opensRange
  let h_iso_image : U ≅ V := i.isoOpensRange
  let isPreirr_X : IsPreirreducible (Set.univ : Set X.carrier) :=
    PreirreducibleSpace.isPreirreducible_univ
  let isPreirr_V : IsPreirreducible V.1 :=
    IsPreirreducible.open_subset isPreirr_X V.2 (by simp)
  let h_preirr_V : PreirreducibleSpace (V) :=
    Subtype.preirreducibleSpace isPreirr_V
  apply h_iso_image.inv.surjective.preirreducibleSpace
  exact h_iso_image.inv.continuous

--#find_home

/-- A scheme `X` over a field `k` is geometrically irreducible if any base change `X_K`
is irreducible for a field extension `K` of `k`. -/
abbrev GeometricallyIrreducible {k : Type u} [Field k] {X : Scheme.{u}}
    (s : X ⟶ Spec (.of k)) : Prop :=
  Geometrically (fun X ↦ IrreducibleSpace X) s

instance : ObjectProperty.InheritedFromSource
    (fun (X : Scheme) ↦ IrreducibleSpace X)
    @Surjective := by
  constructor
  intro X Y f hf hX
  exact f.surjective.irreducibleSpace _ f.continuous

instance : ObjectProperty.IsClosedUnderIsomorphisms
      (fun (X : Scheme) ↦ IrreducibleSpace X) :=
  .of_inheritedFromSource _ @Surjective

namespace GeometricallyIrreducible

variable {k : Type u} [Field k] {X : Scheme.{u}} (s : X ⟶ Spec (.of k))

lemma iff_irreducibleSpace_pullback :
    GeometricallyIrreducible s ↔
      ∀ (K : Type u) [Field K] [Algebra k K],
        IrreducibleSpace ↑(pullback s (Spec (.of K) ↘ _)) :=
  Geometrically.iff_of_isClosedUnderIsomorphisms _

/-- The affine scheme `Spec R` is geometrically irreducible over `k` if and only if
the `k`-algebra `R` is geometrically irreducible. -/
-- Note: this is nontrivial, because the definition of `Algebra.GeometricallyIrreducible` is
-- quite different.
lemma iff_spec (R : Type u) [CommRing R] [Algebra k R] :
    GeometricallyIrreducible (Spec (.of R) ↘ Spec (.of k)) ↔
      Algebra.GeometricallyIrreducible k R :=
  -- Timo
  sorry

/-- Every nonempty open subscheme of a geometrically irreducible scheme is geometrically
irreducible. -/
@[stacks 038G "Final statement."]
lemma of_isOpenImmersion (U : Scheme.{u}) (i : U ⟶ X) [IsOpenImmersion i] [Nonempty U]
    [GeometricallyIrreducible s] :
    GeometricallyIrreducible (i ≫ s) := by
  rw [GeometricallyIrreducible, Geometrically.iff_of_isClosedUnderIsomorphisms]
  intro K _ _
  have h_geo_irr : GeometricallyIrreducible s := by assumption
  have h_X_non_empty: Nonempty X := by
    by_contra h_empty
    have : IsEmpty X := not_nonempty_iff.mp h_empty
    haveI : IsEmpty U := Function.isEmpty (f := i.base)
    exact not_nonempty_iff.mpr ‹IsEmpty U› ‹Nonempty U›
  have h_disjoint : ¬ Disjoint (Set.range s.base) (Set.range (Spec (.of K) ↘ Spec (.of k)).base) := by
    rw  [Set.not_disjoint_iff]
    have sing : Subsingleton (Spec (.of k)) := by
      infer_instance
    let x : Spec (.of k) := ⟨⊥, Ideal.bot_prime⟩
    have s_surj : Function.Surjective s.base := by
      apply Function.surjective_to_subsingleton
    use x
    constructor
    · apply s_surj
    dsimp
    apply Function.surjective_to_subsingleton
  have : Nonempty ↑(pullback s (Spec (.of K) ↘ Spec (.of k))) := by
    rw [← not_isEmpty_iff]
    by_contra h_contra
    rw [AlgebraicGeometry.Scheme.isEmpty_pullback_iff] at h_contra
    apply h_disjoint
    exact h_contra
  let i' := pullback.snd i (pullback.fst s (Spec (.of K) ↘ Spec (.of k)))
  have : IrreducibleSpace ↥(pullback s (Spec (CommRingCat.of K) ↘ Spec (CommRingCat.of k))) := by
    rw [(iff_irreducibleSpace_pullback s)] at h_geo_irr
    specialize h_geo_irr K
    exact h_geo_irr
  let UK := pullback i (pullback.fst s (Spec (CommRingCat.of K) ↘ Spec (CommRingCat.of k)))
  let U_times_K := pullback (i ≫ s) (Spec (CommRingCat.of K) ↘ Spec (CommRingCat.of k))
  let Iso : U_times_K ≅ UK := by
    symm
    apply pullbackRightPullbackFstIso
  have h_disjoint_U : ¬ Disjoint (Set.range (i ≫ s).base) (Set.range (Spec (.of K) ↘ Spec (.of k)).base) := by
    rw  [Set.not_disjoint_iff]
    have sing : Subsingleton (Spec (.of k)) := by
      infer_instance
    let x : Spec (.of k) := ⟨⊥, Ideal.bot_prime⟩
    have ios_surj : Function.Surjective (i ≫ s).base := by
      apply Function.surjective_to_subsingleton
    use x
    constructor
    · apply ios_surj
    dsimp
    apply Function.surjective_to_subsingleton
  have h_U_times_K_nonempty : Nonempty U_times_K := by
    rw [← not_isEmpty_iff]
    by_contra h_contra
    rw [AlgebraicGeometry.Scheme.isEmpty_pullback_iff] at h_contra
    apply h_disjoint_U
    exact h_contra
  have : Nonempty UK := by
    obtain ⟨x⟩ := h_U_times_K_nonempty
    exact ⟨Iso.hom x⟩
  let h_UK_Irreducible : IrreducibleSpace UK := by
    apply irreducibleSpace_of_isOpenImmersion i'
  have h_final:IrreducibleSpace U_times_K := by
    have : UK ≅ U_times_K := Iso.symm
    apply IsHomeomorph.irreducibleSpace this.hom
    exact this.hom.homeomorph.isHomeomorph
  exact h_final


/-- If `X` is geometrically irreducible over `k` and `U` is an affine open, `Γ(X, U)` is
geometrically irreducible over `k`. -/
@[stacks 038G "(1) => (2)"]
lemma geometricallyIrreducible_of_isAffineOpen (U : X.Opens) (hU : IsAffineOpen U)
    (hU : U.carrier.Nonempty) :
    letI : Algebra k Γ(X, U) := algebraOfHomSpec s U
    Algebra.GeometricallyIrreducible k Γ(X, U) :=
  -- use `of_isOpenImmersion` to reduce to the affine case
  sorry

/-- If `X` is covered by geometrically irreducible open subschemes with pairwise
non-empty intersections, `X` is geometrically irreducible. -/
@[stacks 038G "(4) => (1)"]
lemma of_openCover (𝒰 : X.OpenCover) [Nonempty 𝒰.I₀]
    (hn : ∀ i j, Nonempty ↑(pullback (𝒰.f i) (𝒰.f j)))
    (h : ∀ i, GeometricallyIrreducible (𝒰.f i ≫ s)) :
    GeometricallyIrreducible s :=
  sorry

/-- Being geometrically irreducible can be checked on finite extensions. -/
lemma of_finite
    (H : ∀ (K : Type u) [Field K] [Algebra k K] [Module.Finite k K] [Algebra.IsSeparable k K],
      IrreducibleSpace ↑(pullback s (Spec (.of K) ↘ Spec (.of k)))) :
    GeometricallyIrreducible s :=
  sorry

/-- Being geometrically irreducible can be checked on a separable closure. -/
lemma of_isSepClosure (K : Type u) [Field K] [Algebra k K] [IsSepClosure k K]
    [IrreducibleSpace ↑(pullback s (Spec (.of K) ↘ Spec (.of k)))] :
    GeometricallyIrreducible s :=
  sorry

/-- `X` is geometrically irreducible over `s` if and only if `X_K` is irreducible
for `K` a separable closure of `k`. -/
theorem iff_irreducibleSpace_separableClosure :
    GeometricallyIrreducible s ↔
      IrreducibleSpace ↑(pullback s (Spec (.of <| SeparableClosure k) ↘ Spec (.of k))) :=
  sorry

/-- If `X` is geometrically irreducible over `k` and `Y` is any `k`-scheme, then
`X ×[k] Y ⟶ Y` induces an order preserving bijection between irreducible components. -/
@[stacks 0364]
def irreducibleComponentsOrderIsoPullback [GeometricallyIrreducible s] {Y : Scheme.{u}}
    (t : Y ⟶ Spec (.of k)) :
    irreducibleComponents Y ≃o irreducibleComponents ↑(pullback s t) :=
  irreducibleComponentsEquivOfIsPreirreducibleFiber _ (pullback.snd s t).continuous
    -- use `AlgebraicGeometry.universallyOpen_Spec_field`
    sorry
    sorry
    sorry

end GeometricallyIrreducible

end AlgebraicGeometry
