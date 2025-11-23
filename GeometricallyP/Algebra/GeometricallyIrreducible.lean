/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.IsSepClosed
import Mathlib.FieldTheory.LinearDisjoint
import Mathlib.RingTheory.Spectrum.Prime.Topology
import GeometricallyP.Algebra.Irreducible

/-!
# Geometrically irreducible algebras

In this file we develop the theory of geometrically irreducible algebras over a field.

## References

- https://stacks.math.columbia.edu/tag/00I2
-/

universe u

open TensorProduct

namespace Algebra

variable {k : Type u} {R : Type*} [Field k] [CommRing R] [Algebra k R]

/--
A `k`-algebra `R` is geometrically irreducible if `Spec (AlgebraicClosure k ⊗[k] R)` is
irreducible. In this case, `Spec (K ⊗[k] R)` is irreducible for every field extension `K` of `k`
(see `Algebra.GeometricallyIrreducible.irreducibleSpace`).
Note: The stacks project definition is the latter condition, which is equivalent to the former by
the above. The reason for choosing this definition is that it does not quantify over types.
-/
@[stacks 037L, mk_iff]
class GeometricallyIrreducible (k R : Type*) [Field k] [CommRing R] [Algebra k R] : Prop where
  irreducibleSpace_tensorProduct :
    IrreducibleSpace (PrimeSpectrum (AlgebraicClosure k ⊗[k] R))

namespace GeometricallyIrreducible

variable (k : Type u) (R : Type*) [CommRing R] [Field k] [Algebra k R]

@[stacks 037K "(3) <=> (4)"]
lemma iff_irreducibleSpace_separableClosure :
    GeometricallyIrreducible k R ↔
      IrreducibleSpace (PrimeSpectrum (SeparableClosure k ⊗[k] R)) := by
  rw [geometricallyIrreducible_iff]
  exact (PrimeSpectrum.irreducibleSpace_iff_of_isAlgClosure_of_isSepClosure _ _ _ _).symm

/-- If `Spec (K ⊗[k] R)` is irreducible for every finite separable extension `K` of `k`, then
`R` is geometrically irreducible over `k`. -/
@[stacks 037K "(2) => (3) => (4)"]
theorem of_forall_irreducibleSpace_of_isSeparable
    (H : ∀ (K : Type u) [Field K] [Algebra k K] [Module.Finite k K] [Algebra.IsSeparable k K],
      IrreducibleSpace (PrimeSpectrum (K ⊗[k] R))) :
    Algebra.GeometricallyIrreducible k R := by
  rw [iff_irreducibleSpace_separableClosure]
  exact PrimeSpectrum.irreducibleSpace_of_isSeparable H (SeparableClosure k)

/-- If `R` is geometrically irreducible over `k`, for every field extension `K` of `k`, the
prime spectrum `Spec (K ⊗[k] R)` is irreducible. -/
@[stacks 037K "(4) => (1)"]
theorem irreducibleSpace [Algebra.GeometricallyIrreducible k R]
    (K : Type*) [Field K] [Algebra k K] :
    IrreducibleSpace (PrimeSpectrum (K ⊗[k] R)) := by
  let : Algebra (AlgebraicClosure k) (K ⊗[k] AlgebraicClosure k) :=
    Algebra.TensorProduct.rightAlgebra
  let : Algebra K (K ⊗[k] AlgebraicClosure k) :=
    Algebra.TensorProduct.leftAlgebra
  obtain ⟨m, _⟩ := Ideal.exists_maximal (K ⊗[k] AlgebraicClosure k)
  let F :=  (K ⊗[k] AlgebraicClosure k) ⧸ m
  let : Field F := Ideal.Quotient.field m
  let : Algebra (K ⊗[k] R) (F ⊗[k] R) := RingHom.toAlgebra <| AlgHom.toRingHom <|
    Algebra.TensorProduct.map (IsScalarTower.toAlgHom k K F) (AlgHom.id k R)
  let hR : IrreducibleSpace (PrimeSpectrum (AlgebraicClosure k ⊗[k] R)) := by
    rw [← geometricallyIrreducible_iff]
    infer_instance
  let hF : IrreducibleSpace (PrimeSpectrum F) := inferInstance
  let : IrreducibleSpace (PrimeSpectrum (F ⊗[AlgebraicClosure k] (AlgebraicClosure k ⊗[k] R))) :=
      PrimeSpectrum.irreducibleSpace_tensorProduct_of_isAlgClosed (k:=AlgebraicClosure k) hF hR
  let homeo : PrimeSpectrum (F ⊗[AlgebraicClosure k] (AlgebraicClosure k ⊗[k] R)) ≃ₜ
    PrimeSpectrum (F ⊗[k] R) := PrimeSpectrum.homeomorphOfRingEquiv
      (Algebra.TensorProduct.cancelBaseChange k (AlgebraicClosure k) (AlgebraicClosure k) F R)
  have : IrreducibleSpace (PrimeSpectrum (F ⊗[k] R)) := homeo.isHomeomorph.irreducibleSpace
  exact PrimeSpectrum.irreducibleSpace_of_isScalarTower K F

/-- If `R` is geometrically irreducible over `k`, for every field extension `K` of `k`, the
prime spectrum `Spec (K ⊗[k] R)` is irreducible. -/
theorem irreducibleSpace' [Algebra.GeometricallyIrreducible k R]
    (K : Type*) [Field K] [Algebra k K] :
    IrreducibleSpace (PrimeSpectrum (R ⊗[k] K)) := by
  rw [PrimeSpectrum.homeomorphOfRingEquiv (Algebra.TensorProduct.comm _ _ _).toRingEquiv
        |>.isHomeomorph.irreducibleSpace_iff]
  exact irreducibleSpace _ _ _

/-- If `Ω` is a separably closed extension of `k` such that `Spec (Ω ⊗[k] R)` is irreducible,
`R` is geometrically irreducible over `k`. -/
theorem of_irreducibleSpace_of_isSepClosed (Ω : Type*) [Field Ω] [Algebra k Ω] [IsSepClosed Ω]
    (H : IrreducibleSpace (PrimeSpectrum (Ω ⊗[k] R))) :
    Algebra.GeometricallyIrreducible k R := by
  rw [iff_irreducibleSpace_separableClosure]
  let h : Algebra (SeparableClosure k) Ω :=
    (IsSepClosed.lift : (SeparableClosure k →ₐ[k] Ω)).toAlgebra
  apply PrimeSpectrum.irreducibleSpace_of_isScalarTower (SeparableClosure k) Ω

--this should be somewhere right?
lemma IsFieldOfIsoField (K L : Type*) [Field K] [Ring L] (e : K ≃+* L) : IsField L := by
  constructor
  · use e.toFun 0, e.toFun 1
    intro h
    have : (0:K)= (1:K) := by
      rw [← e.left_inv 0, h, e.left_inv 1]
    grind-- a bit overkill right? i could'nt find better
  · intro x y
    rw [← e.right_inv x, ← e.right_inv y, ← e.map_mul', mul_comm, e.map_mul']
  · intro a ha
    use e.toFun ((e.invFun a) ⁻¹)
    slice_lhs 1 1 => rw [← e.right_inv a]
    rw [ ← e.map_mul']
    have : e.invFun a ≠ 0 := by
      suffices e.symm a ≠ 0 by
        exact this
      apply  (RingEquiv.map_ne_zero_iff _).2 ha
    rw [Field.mul_inv_cancel _ this, ← RingEquiv.map_one e]
    rfl

/-- If K/k is a finte separable extension and L a geometrically irreducible field over k
then L ⊗[k] K is a field -/
lemma isField_tensorProduct_of_isSeparable (k K L : Type*) [Field k] [Field K] [Field L]
    [Algebra k K] [Algebra k L] [Module.Finite k K] [Algebra.IsSeparable k K]
    [GeometricallyIrreducible k L] :
    IsField (L ⊗[k] K) := by
  obtain ⟨a, ha⟩ := Field.exists_primitive_element k K
  have h : IsAdjoinRoot (L ⊗[k] K) _ :=
    (IsAdjoinRoot.mkOfPrimitiveElement (IsIntegral.isIntegral a) ha).tensorProduct
  have : IsDomain (L ⊗[k] K) := by
    rw [isDomain_iff_isReduced_and_irreducibleSpace]
    refine ⟨?_, irreducibleSpace' k L K⟩
    exact .of_isAdjoinRoot_of_squareFree _ h
      (Polynomial.Separable.map (IsSeparable.isSeparable' a)).squarefree
  have : IsArtinianRing (L ⊗[k] K) := by
    refine IsAdjoinRoot.isArtinianRing_of_field _ h ?_
    exact (map_ne_zero_iff (Polynomial.mapRingHom (algebraMap k L))
      (Polynomial.map_injective _ <| FaithfulSMul.algebraMap_injective k L)).mpr <|
      minpoly.ne_zero_of_finite k a
  exact IsArtinianRing.isField_of_isDomain (L ⊗[k] K)

/-- If `K` is geometrically irreducible over `k` and `R` is geometrically irreducible over `K`,
then `R` is geometrically irreducible over `k`. -/
@[stacks 0G30]
lemma trans (K : Type*) [Field K] [Algebra k K] [Algebra K R] [IsScalarTower k K R]
    [GeometricallyIrreducible k K] [GeometricallyIrreducible K R] :
    GeometricallyIrreducible k R := by
  refine of_forall_irreducibleSpace_of_isSeparable _ _ fun k' _ _ _ _ ↦ ?_
  let K' := K ⊗[k] k'
  let : Algebra k' K' := TensorProduct.rightAlgebra
  have cb : (K' ⊗[K] R) ≃+* k' ⊗[k] R :=
    (Algebra.TensorProduct.comm K K' R).toRingEquiv.trans <|
      (Algebra.TensorProduct.cancelBaseChange k K K R k').toRingEquiv.trans
      (Algebra.TensorProduct.comm k R k').toRingEquiv
  rw [← ((PrimeSpectrum.homeomorphOfRingEquiv cb)).isHomeomorph.irreducibleSpace_iff]
  let : Field K' := (isField_tensorProduct_of_isSeparable k k' K).toField
  exact irreducibleSpace K R K'

/-- Let `K` over k` be a field extension. Then `K` is geometrically irreducible over `k`
if and only if every `k`-separable, algebraic element `x : K` is contained in `k`. -/
@[stacks 0G33]
theorem iff_of_forall_isSeparable_mem (K : Type*) [Field K] [Algebra k K] :
    GeometricallyIrreducible k K ↔
      ∀ x : K, IsSeparable k x → x ∈ Set.range (algebraMap k K) :=
  sorry

end GeometricallyIrreducible

end Algebra
