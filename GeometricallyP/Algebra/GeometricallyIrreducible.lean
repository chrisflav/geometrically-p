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

noncomputable def foo {R : Type*} (S:Type*) [CommRing R] [CommRing S]
    [Algebra R S] (p : Polynomial R) :
    AdjoinRoot (p.map (algebraMap R S)) ≃ₐ[S] S ⊗[R] AdjoinRoot p :=
  AlgEquiv.ofAlgHom
    (AdjoinRoot.liftAlgHom _ TensorProduct.includeLeft ( 1 ⊗ₜ AdjoinRoot.root p) (by
    --let motive : Polynomial R → Prop :=
      --fun p => (Polynomial.eval₂ (TensorProduct.includeLeft) (1 ⊗ₜ[R] AdjoinRoot.root p) (Polynomial.map (algebraMap R S) p) = 0)


    --apply Polynomial.induction_on  p




    --rw [Polynomial.eval₂_def]
    --simp


    sorry))
    (Algebra.TensorProduct.lift (AdjoinRoot.ofAlgHom S (Polynomial.map (algebraMap R S) p)) (AdjoinRoot.liftAlgHom p ⟨ by apply algebraMap, by simp ⟩ (AdjoinRoot.root (Polynomial.map (algebraMap R S) p)
      ) (by


      simp
      let motive := fun p => Polynomial.eval₂ (algebraMap R (AdjoinRoot (Polynomial.map (algebraMap R S) p))) (AdjoinRoot.root (Polynomial.map (algebraMap R S) p)) p = 0


      apply @Polynomial.induction_on _ _ motive

      · intro a
        simp [motive]

        sorry
      · intro p q hp hq
        simp [motive]

        sorry
      · sorry))
    (by
      intro _ _
      apply Commute.all))
    (by aesop)
    (by aesop)

/-- If K/k is a finte separable extension and L a field over k then L ⊗[k] K is a field -/
lemma FinSepExTensorIsField (k K L : Type*) [Field k] [Field K] [Field L] [Algebra k K] [Algebra k L] [Module.Finite k K] [Algebra.IsSeparable k K] [GeometricallyIrreducible k L] : IsField (L ⊗[k] K) := by

  --obtain ⟨a,ha⟩ := Field.exists_primitive_element k K

  let pb := Field.powerBasisOfFiniteOfSeparable k K

  let p := minpoly k pb.gen

  -- case dijsonction if (Polynomial.map (algebraMap k L) p)) is unit or not
  rcases (Classical.em <| IsUnit (Polynomial.map (algebraMap k L) p)) with Up | nUp

  -- then deg p = 1 and then k=K and then L ⊗[k] K=L wich is a field
  sorry
  -- otherwise:

  let : AdjoinRoot p ≃ₐ[k] K := by
    apply AdjoinRoot.equiv' p pb
    · simp
      rfl
    · aesop
  let :  L ⊗[k] AdjoinRoot p ≃ₐ[k] L ⊗[k] K := by
    apply Algebra.TensorProduct.congr AlgEquiv.refl this

  let iso : AdjoinRoot (Polynomial.map (algebraMap k L) p) ≃+* L ⊗[k] K := ((foo L p).toRingEquiv).trans <| this

  have : Fact (Irreducible (Polynomial.map (algebraMap k L) p)) := by
    constructor
    by_contra!
    rw [irreducible_iff] at this
    push_neg at this

    obtain ⟨a,b,⟨hp,ha,hb⟩⟩ := this nUp

    --K[X]/(p) = K[X]/(a) × K[X]/(b)
    let e : AdjoinRoot (Polynomial.map (algebraMap k L) p) ≃+* AdjoinRoot a × AdjoinRoot b := by
      --thm chinois and p is separable
      sorry

    let  : K⊗[k]L ≃+*  AdjoinRoot a × AdjoinRoot b := by
      exact (Algebra.TensorProduct.comm k K L).toRingEquiv.trans <| iso.symm.trans <| e

    -- Spec(L⊗[k]K) = Spec (K[X]/(a) × K[X]/(b)) = Spec ( K[X]/(a)) ⨿ Spec ( K[X]/(b))
    #check (PrimeSpectrum.homeomorphOfRingEquiv this).trans PrimeSpectrum.primeSpectrumProdHomeo

    -- this space is irreducible
    let irr: IrreducibleSpace (PrimeSpectrum (K ⊗[k] L)) :=  irreducibleSpace k L K

    --K/k is geometrically irreducible then Spec ( K[X]/(a)) ⨿ Spec ( K[X]/(b)) is irreducible
    have : IrreducibleSpace <| PrimeSpectrum (AdjoinRoot a) ⊕ PrimeSpectrum (AdjoinRoot b) := by
      let homeo := Homeomorph.isHomeomorph <| (PrimeSpectrum.homeomorphOfRingEquiv this).trans PrimeSpectrum.primeSpectrumProdHomeo

      exact IsHomeomorph.irreducibleSpace _ homeo

    let X := PrimeSpectrum (AdjoinRoot a) ⊕ PrimeSpectrum (AdjoinRoot b)
    let U : Set X := (Sum.inl)'' ⊤
    let V : Set X := (Sum.inr)'' ⊤

    have : IsOpen U := by
      apply isOpen_sum_iff.mpr
      constructor
      · unfold U
        simp
      · unfold U
        aesop
    have : IsOpen V := by
      apply isOpen_sum_iff.mpr
      constructor
      · unfold V
        aesop
      · unfold V
        simp
      --PrimeSpectrum (AdjoinRoot a)

    have nU : Nonempty U := by
      --otherwise a is a unit
      sorry

    have nV: Nonempty V := by sorry


    have : (U ∩ V ).Nonempty := nonempty_preirreducible_inter (by assumption) (by assumption) (by sorry ) (by sorry)

    have : (U ∩ V ) = ⊥ := by sorry

    apply?


    sorry

  have : Field <| AdjoinRoot (Polynomial.map (algebraMap k L) p) := by

    apply @AdjoinRoot.instField _ _ (Polynomial.map (algebraMap k L) p)

  apply IsFieldOfIsoField _ _ iso


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

      have cb : (K' ⊗[K] R) ≃+* k' ⊗[k] R := (Algebra.TensorProduct.comm K K' R).toRingEquiv.trans <| (Algebra.TensorProduct.cancelBaseChange k K K R k').toRingEquiv.trans (Algebra.TensorProduct.comm k R k').toRingEquiv

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
