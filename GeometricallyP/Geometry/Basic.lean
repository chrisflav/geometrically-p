/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import GeometricallyP.Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
import GeometricallyP.Mathlib.CategoryTheory.ObjectProperty.Stability
import Mathlib.AlgebraicGeometry.Properties

/-!
# Geometrically-`P` schemes over a field

In this file we define the basic interface for properties like geometrically reduced,
geometrically irreducible, geometrically connected etc. In this file
we treat an abstract property of schemes `P` and derive the general properties that are
shared by all of these variants.

A scheme `X` over a field `k` is geometrically `P` if `P` holds for any base change `X_K`
for a field extension `K` of `k`.
-/

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

noncomputable instance (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] :
    (Spec (.of S)).Over (Spec (.of R)) where
  hom := Spec.map (CommRingCat.ofHom <| algebraMap R S)

@[simp]
lemma overHom_spec_self (R : Type u) [CommRing R] :
    Spec (.of R) ↘ Spec (.of R) = 𝟙 _ := Spec.map_id _

/-- If `X` is a scheme over `S` and `f : T ⟶ S` is a morphism, the fibre product
`X ×[S] T` is a scheme over `T`.
This matches the order in `CategoryTheory.Over.pullback`, but not the tensor product convention. -/
noncomputable instance {X S T : Scheme.{u}} (f : T ⟶ S) [X.Over S] :
    (pullback (X ↘ S) f).Over T where
  hom := pullback.snd _ _

/-- A scheme `X` over a field `k` is geometrically `P` if `P` holds for any base change `X_K`
for a field extension `K` of `k`. -/
@[mk_iff]
class Geometrically (P : ObjectProperty Scheme.{u}) {k : Type u} [Field k] {X : Scheme.{u}}
    (s : X ⟶ Spec (.of k)) : Prop where
  prop_of_isPullback (s) (K : Type u) [Field K] [Algebra k K] (Y : Scheme.{u}) (fst : Y ⟶ X)
    (snd : Y ⟶ Spec (.of K)) (h : IsPullback fst snd s (Spec (.of K) ↘ Spec (.of k))) :
    P Y

/-- A scheme `X` over a field `k` is geometrically reduced if any base change `X_K`
is reduced for a field extension `K` of `k`. -/
abbrev GeometricallyIsReduced {k : Type u} [Field k] {X : Scheme.{u}}
    (s : X ⟶ Spec (.of k)) : Prop :=
  Geometrically (fun X ↦ IsReduced X) s

/-- A scheme `X` over a field `k` is geometrically connected if any base change `X_K`
is connected for a field extension `K` of `k`. -/
abbrev GeometricallyConnected {k : Type u} [Field k] {X : Scheme.{u}}
    (s : X ⟶ Spec (.of k)) : Prop :=
  Geometrically (fun X ↦ ConnectedSpace X) s

namespace Geometrically

variable {P : ObjectProperty Scheme.{u}} {k : Type u} [Field k] {X : Scheme.{u}}
  (s : X ⟶ Spec (.of k))

lemma prop_self [Geometrically P s] : P X :=
  prop_of_isPullback s k X (𝟙 X) s <| by simp [IsPullback.of_id_fst]

lemma prop_pullback [Geometrically P s] (K : Type u) [Field K] [Algebra k K] :
    P (pullback s (Spec (.of K) ↘ _)) :=
  prop_of_isPullback s K _ _ _ (.of_hasPullback _ _)

lemma prop_pullback' [Geometrically P s] (K : Type u) [Field K] [Algebra k K] :
    P (pullback (Spec (.of K) ↘ _) s) :=
  prop_of_isPullback s K _ _ _ (.flip <| .of_hasPullback _ _)

lemma iff_of_isClosedUnderIsomorphisms [P.IsClosedUnderIsomorphisms] :
    Geometrically P s ↔
      ∀ (K : Type u) [Field K] [Algebra k K], P (pullback s (Spec (.of K) ↘ _)) := by
  refine ⟨fun h K _ _ ↦ prop_pullback _ _, fun H ↦ ?_⟩
  rw [geometrically_iff]
  intro K _ _ Y fst snd h
  exact P.prop_of_iso h.isoPullback.symm (H _)

lemma iff_of_iso [P.IsClosedUnderIsomorphisms] {Y : Scheme.{u}} (t : Y ⟶ Spec (.of k)) (e : X ≅ Y)
    (w : e.hom ≫ t = s := by cat_disch) : Geometrically P s ↔ Geometrically P t := by
  rw [iff_of_isClosedUnderIsomorphisms, iff_of_isClosedUnderIsomorphisms]
  congr! 3
  apply P.prop_iff_of_iso
  exact (Over.pullback _ ⋙ Over.forget _).mapIso (Over.isoMk e w : Over.mk s ≅ Over.mk t)

/-- If `X ⟶ Spec k` is geometrically `P` and `k'` is a field extension of `k`,
then also `X_k' ⟶ Spec k'` is geometrically `P`. -/
lemma of_isPullback [P.IsClosedUnderIsomorphisms] {k' : Type u} [Field k']
    [Algebra k k'] {Y : Scheme.{u}} {fst : Y ⟶ X} {snd : Y ⟶ Spec (.of k')}
    (h : IsPullback fst snd s (Spec (.of k') ↘ Spec (.of k))) [Geometrically P s] :
    Geometrically P snd :=
  sorry

/--
Suppose the property `P` is preserved by surjective morphisms (i.e., if `X ⟶ Y` is surjective
and `X` satisfies `P`, also `Y` satisfies `P`).
Then `Geometrically P` is invariant under scalar extensions.
-/
-- Note: this is in particular satisfied for `P = IrreducibleSpace` and `P = ConnectedSpace`.
@[stacks 054P]
lemma iff_of_inheritedFromSource_surjective_of_isPullback [P.InheritedFromSource @Surjective]
    {k' : Type u} [Field k'] [Algebra k k'] {Y : Scheme.{u}} {fst : Y ⟶ X} {snd : Y ⟶ Spec (.of k')}
    (h : IsPullback fst snd s (Spec (.of k') ↘ Spec (.of k))) :
    Geometrically P snd ↔ Geometrically P s :=
  have : P.IsClosedUnderIsomorphisms := .of_inheritedFromSource _ @Surjective
  sorry

end Geometrically

end AlgebraicGeometry
