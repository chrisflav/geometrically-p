/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import GeometricallyP.Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
import GeometricallyP.Mathlib.CategoryTheory.ObjectProperty.Stability
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.AlgebraicGeometry.PullbackCarrier

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
open TensorProduct

namespace AlgebraicGeometry

noncomputable instance (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] :
    (Spec (.of S)).Over (Spec (.of R)) where
  hom := Spec.map (CommRingCat.ofHom <| algebraMap R S)

@[simp]
lemma overHom_spec_self (R : Type u) [CommRing R] :
    Spec (.of R) ↘ Spec (.of R) = 𝟙 _ := Spec.map_id _

lemma overHom_Spec_def (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] :
    (Spec (.of S)) ↘ (Spec (.of R)) = Spec.map (CommRingCat.ofHom <| algebraMap R S) :=
  rfl

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
    Geometrically P snd where
  prop_of_isPullback K _ _ Z := by
    intro fst' snd' isPullback
    let : Algebra k K := Algebra.compHom K (algebraMap k k')
    have : IsPullback (fst' ≫ fst) snd' s ( (Spec (.of K) ↘ Spec (.of k)))  := by
     convert IsPullback.paste_horiz isPullback h
     rw [overHom_Spec_def, overHom_Spec_def, overHom_Spec_def]
     rw [← Spec.map_comp]
     rfl
    apply prop_of_isPullback s K Z _ _ this

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
    Geometrically P snd ↔ Geometrically P s := by
  have closed_under_iso : P.IsClosedUnderIsomorphisms := .of_inheritedFromSource _ @Surjective
  repeat rw [geometrically_iff]
  constructor
  · intro h' k'' _ _ X'' fst'' snd'' h''
    -- Construct common field extension of k' and k''
    let tensor_prod := k' ⊗[k] k''
    have : Nontrivial tensor_prod := by apply Module.FaithfullyFlat.lTensor_nontrivial
    obtain ⟨M, hM⟩ := Ideal.exists_maximal tensor_prod
    let k''' := tensor_prod ⧸ M
    let : Field k''' := Ideal.Quotient.field M

    -- Construct maps between the Specs
    let inr : k'' →ₐ tensor_prod := Algebra.TensorProduct.includeRight
    let : Algebra k'' k''' := Algebra.compHom k''' inr.toRingHom
    let specMap''' := Spec (.of k''') ↘ Spec (.of k')
    let specMap'''' := Spec (.of k''') ↘ Spec (.of k'')

    -- Construct the common pullback
    let X''' := pullback snd specMap'''
    let X'''' := pullback snd'' specMap''''
    have PX''' := h' k''' X''' (pullback.fst snd specMap''')
      (pullback.snd snd specMap''') (IsPullback.of_hasPullback _ _)
    have : X''' ≅ X'''' := sorry -- This is pretty tedious to show. I don't know how to do this properly

    -- Use the other pullback square to propagate P to X'' along the surjective morphism
    have PX'''' := closed_under_iso.of_iso this PX'''
    let g := pullback.fst snd'' specMap''''
    have : Surjective g := by
      have is_pb : IsPullback (pullback.snd snd'' specMap'''') g
          (Spec (.of k''') ↘ Spec (.of k'')) snd'' := by
        apply IsPullback.flip
        apply IsPullback.of_hasPullback _ _
      have surj : Surjective (Spec (.of k''') ↘ Spec (.of k'')) := by
        apply (surjective_iff _).mpr
        apply Function.surjective_to_subsingleton
      have : MorphismProperty.IsStableUnderBaseChange @Surjective := by infer_instance
      apply this.of_isPullback is_pb surj
    apply (_ : P.InheritedFromSource @Surjective).of_hom_of_source g this PX''''
    assumption -- this should ideally be moved into the line above
  · intro h' k'' _ _ Y' fst' snd' h''
    let : Algebra k k'' := Algebra.compHom k'' (algebraMap k k')
    refine h' k'' Y' (fst' ≫ fst) snd' ?_
    convert IsPullback.paste_horiz h'' h
    refine .trans ?_ (Spec.map_comp _ _)
    rfl






end Geometrically

end AlgebraicGeometry
