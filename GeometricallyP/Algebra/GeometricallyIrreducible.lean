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
  irreducibleSpace_tensorProduct : IrreducibleSpace (PrimeSpectrum (AlgebraicClosure k ⊗[k] R))

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
    Algebra.GeometricallyIrreducible k R :=
  /-
  uses `PrimeSpectrum.irreducibleSpace_of_isSeparable` and `iff_irreducibleSpace_separableClosure`
  -/
  sorry

/-- If `R` is geometrically irreducible over `k`, for every field extension `K` of `k`, the
prime spectrum `Spec (K ⊗[k] R)` is irreducible. -/
@[stacks 037K "(4) => (1)"]
theorem irreducibleSpace [Algebra.GeometricallyIrreducible k R]
    (K : Type*) [Field K] [Algebra k K] :
    IrreducibleSpace (PrimeSpectrum (K ⊗[k] R)) :=
  -- uses `PrimeSpectrum.irreducibleSpace_tensorProduct_of_isAlgClosed`
  sorry

/-- If `Ω` is a separably closed extension of `k` such that `Spec (Ω ⊗[k] R)` is irreducible,
`R` is geometrically irreducible over `k`. -/
theorem of_irreducibleSpace_of_isSepClosed (Ω : Type*) [Field Ω] [Algebra k Ω] [IsSepClosed Ω]
    (H : IrreducibleSpace (PrimeSpectrum (Ω ⊗[k] R))) :
    Algebra.GeometricallyIrreducible k R :=
  /-
  use `iff_irreducibleSpace_separableClosure` and `PrimeSpectrum.irreducibleSpace_of_isScalarTower`
  -/
  sorry

/-- If K/k is a finte separable extension and L a field over k then L ⊗[k] K is a field -/
lemma FinSepExTensorIsField (k K L : Type*) [Field k] [Field K] [Field L] [Algebra k K] [Algebra k L] [Module.Finite k K] [Algebra.IsSeparable k K] : IsField (L ⊗[k] K) := by
  --#check k⟮α⟯
  let a := (Field.exists_primitive_element k K).choose
  let ha  : IntermediateField.adjoin k {a} = ⊤ := (Field.exists_primitive_element k K).choose_spec

  let a2 : (L ⊗[k] K) := (1:L) ⊗ₜ[k] a

  let M := Algebra.adjoin L {a2}

  let : M ≃ₐ (L ⊗[k] K) := by sorry

  --L⊗[k]K= L(a) qui est un corps
  sorry

/-- If `K` is geometrically irreducible over `k` and `R` is geometrically irreducible over `K`,
then `R` is geometrically irreducible over `k`. -/
@[stacks 0G30]
lemma trans (K : Type*) [Field K] [Algebra k K] [Algebra K R] [IsScalarTower k K R]
    [GeometricallyIrreducible k K] [GeometricallyIrreducible K R] :
    GeometricallyIrreducible k R := by
      apply of_forall_irreducibleSpace_of_isSeparable
      intro k' _ _ _ _

      let K' := K ⊗[k] k'

      let : Algebra K K' := TensorProduct.leftAlgebra

      let : Algebra k' K' := TensorProduct.rightAlgebra

      have : IsScalarTower k K K' := isScalarTower_left

      have : IsScalarTower k k' K' := Algebra.TensorProduct.right_isScalarTower

      have cb: (K' ⊗[K] R) ≃+* k' ⊗[k] R := (Algebra.TensorProduct.comm K K' R).toRingEquiv.trans <| (Algebra.TensorProduct.cancelBaseChange k K K R k').toRingEquiv.trans (Algebra.TensorProduct.comm k R k').toRingEquiv

      suffices IrreducibleSpace (PrimeSpectrum ((K' ⊗[K] R))) by
        let homeo := Homeomorph.isHomeomorph ((PrimeSpectrum.homeomorphOfRingEquiv cb))
        exact IsHomeomorph.irreducibleSpace _ homeo

      let : Field K' := by
        apply IsField.toField
        apply FinSepExTensorIsField

      exact  irreducibleSpace K R K'

/-- Let `K` over k` be a field extension. Then `K` is geometrically irreducible over `k`
if and only if every `k`-separable, algebraic element `x : K` is contained in `k`. -/
@[stacks 0G33]
theorem iff_of_forall_isSeparable_mem (K : Type*) [Field K] [Algebra k K] :
    GeometricallyIrreducible k K ↔
      ∀ x : K, IsSeparable k x → x ∈ Set.range (algebraMap k K) :=
  sorry

end GeometricallyIrreducible

end Algebra
