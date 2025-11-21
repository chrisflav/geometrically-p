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
      Algebra.GeometricallyIrreducible k R := by
  rw [iff_irreducibleSpace_pullback]
  constructor
  · rw [Algebra.geometricallyIrreducible_iff]
    intro h
    let irred : IrreducibleSpace ↥(pullback
        (Spec.map (CommRingCat.ofHom (algebraMap k R)))
        (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k))))) :=
      h (AlgebraicClosure k)
    have irred_switch_tp : IrreducibleSpace ↥(pullback
        (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k))))
        (Spec.map (CommRingCat.ofHom (algebraMap k R)))) := by
        apply IsHomeomorph.irreducibleSpace _ (pullbackSymmetry _
            (Spec.map (CommRingCat.ofHom (algebraMap k R)))).inv.homeomorph.isHomeomorph
    let equiv := AlgebraicGeometry.pullbackSpecIso k (AlgebraicClosure k) R
    let f := equiv.hom
    let hf : IsHomeomorph f := f.homeomorph.isHomeomorph
    exact IsHomeomorph.irreducibleSpace f hf
  · intro h K _ _
    have irred_pb : IrreducibleSpace ↥(Spec (CommRingCat.of (TensorProduct k K R))) :=
        (Algebra.GeometricallyIrreducible.irreducibleSpace k R) K
    let equiv := AlgebraicGeometry.pullbackSpecIso k K R
    let f := equiv.inv
    let hf : IsHomeomorph f := f.homeomorph.isHomeomorph
    have irred_pb' : IrreducibleSpace ↥(pullback
        (Spec.map (CommRingCat.ofHom (algebraMap k K)))
        (Spec (CommRingCat.of R) ↘ Spec (CommRingCat.of k)))
      := IsHomeomorph.irreducibleSpace f hf
    exact IsHomeomorph.irreducibleSpace _ (pullbackSymmetry _
        (Spec.map (CommRingCat.ofHom (algebraMap k K)))).inv.homeomorph.isHomeomorph

/-- Every nonempty open subscheme of a geometrically irreducible scheme is geometrically
irreducible. -/
@[stacks 038G "Final statement."]
lemma of_isOpenImmersion (U : Scheme.{u}) (i : U ⟶ X) [IsOpenImmersion i] [Nonempty U]
    [GeometricallyIrreducible s] :
    GeometricallyIrreducible (i ≫ s) :=
  -- Alireza
  sorry

/-- If `X` is geometrically irreducible over `k` and `U` is an affine open, `Γ(X, U)` is
geometrically irreducible over `k`. -/
@[stacks 038G "(1) => (2)"]
lemma geometricallyIrreducible_of_isAffineOpen [GeometricallyIrreducible s]
    (U : X.Opens) (hU : IsAffineOpen U) (hU : U.carrier.Nonempty) :
    letI : Algebra k Γ(X, U) := algebraOfHomSpec s U
    Algebra.GeometricallyIrreducible k Γ(X, U) :=
  -- use `of_isOpenImmersion` to reduce to the affine case
  -- Cheni
  sorry

lemma _root_.irreducible_of_openCover {X ι : Type*} [TopologicalSpace X]
    {U : ι → TopologicalSpace.Opens X} (hU : TopologicalSpace.IsOpenCover U)
    (hn : ∀ i j, Nonempty ↑((U i).carrier ∩ (U j).carrier))
    (h : ∀ i, IrreducibleSpace ↥(U i)) :
    IrreducibleSpace X := by
  apply irreducibleComponents_eq_singleton_iff.mp
  #check exists_mem_irreducibleComponents_subset_of_isIrreducible
  sorry


lemma irreducible_of_openCover (𝒰 : X.OpenCover) [Nonempty 𝒰.I₀]
    (hn : ∀ i j, Nonempty ↑(pullback (𝒰.f i) (𝒰.f j)))
    (h : ∀ i, IrreducibleSpace (𝒰.X i)) :
    IrreducibleSpace X := by
  -- irreducibility can be checked on an open cover
  have := 𝒰.isOpenCover_opensRange
  have hn' : ∀ i j,
      Nonempty ↑((𝒰.f i).opensRange.carrier ∩ (𝒰.f j).opensRange.carrier) :=
    -- nonempty pullback implies nonempty intersection of subsets
    sorry
  refine _root_.irreducible_of_openCover this hn' (fun i ↦ ?_)
  apply (Set.rangeFactorization_surjective (f := (𝒰.f i))).irreducibleSpace
  exact continuous_rangeFactorization_iff.mpr (𝒰.f i).continuous

/-- If `X` is covered by geometrically irreducible open subschemes with pairwise
non-empty intersections, `X` is geometrically irreducible. -/
@[stacks 038G "(4) => (1)"]
lemma of_openCover (𝒰 : X.OpenCover) [Nonempty 𝒰.I₀]
    (hn : ∀ i j, Nonempty ↑(pullback (𝒰.f i) (𝒰.f j)))
    (h : ∀ i, GeometricallyIrreducible (𝒰.f i ≫ s)) :
    GeometricallyIrreducible s := by
  refine (Geometrically.iff_of_isClosedUnderIsomorphisms s).mpr (fun K _ _ ↦ ?_)
  let hpo :=
    Scheme.Pullback.openCoverOfLeft 𝒰 s (Spec (CommRingCat.of K) ↘ Spec (CommRingCat.of k))
  have hi (i : hpo.I₀) : IrreducibleSpace (hpo.X i) := by
    simp only [Scheme.Pullback.openCoverOfLeft_X, hpo]
    apply (Geometrically.iff_of_isClosedUnderIsomorphisms (𝒰.f i ≫ s)).mp (h i)
  have : Nonempty hpo.I₀ := by simp only [Scheme.Pullback.openCoverOfLeft_I₀, hpo]; infer_instance
  refine irreducible_of_openCover hpo (fun i j ↦ ?_) hi
  -- pullback cover has pairwise non-empty intersections
  sorry

/-- Being geometrically irreducible can be checked on finite extensions. -/
lemma of_finite
    (H : ∀ (K : Type u) [Field K] [Algebra k K] [Module.Finite k K] [Algebra.IsSeparable k K],
      IrreducibleSpace ↑(pullback s (Spec (.of K) ↘ Spec (.of k)))) :
    GeometricallyIrreducible s :=
  sorry

/-- Being geometrically irreducible can be checked on a separably closed field. -/
lemma of_isSepClosed (Ω : Type u) [Field Ω] [Algebra k Ω] [IsSepClosed Ω]
    [IrreducibleSpace ↑(pullback s (Spec (.of Ω) ↘ Spec (.of k)))] :
    GeometricallyIrreducible s :=
  -- Yannis
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
