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

/-- If every idempotent is trivial, then `Spec R` is connected. -/
lemma PrimeSpectrum.connectedSpace_of_forall_isIdempotentElem
    (H : ∀ e : R, IsIdempotentElem e → e = 0 ∨ e = 1) :
    ConnectedSpace (PrimeSpectrum R) :=
  -- use `PrimeSpectrum.isIdempotentElemEquivClopens`
  sorry

lemma PrimeSpectrum.connectedSpace_iff_idempotents_eq :
    ConnectedSpace (PrimeSpectrum R) ↔ idempotents R = {0, 1} :=
  sorry

lemma PrimeSpectrum.connectedSpace_of_forall_connectedSpace_of_isSeparable
    (H : ∀ (K : Type v) [Field K] [Algebra k K] [Module.Finite k K] [Algebra.IsSeparable k K],
      ConnectedSpace (PrimeSpectrum (K ⊗[k] R)))
    (Ω : Type v) [Field Ω] [Algebra k Ω] [Algebra.IsSeparable k Ω] :
    ConnectedSpace (PrimeSpectrum (Ω ⊗[k] R)) :=
  /-
  Use `eq_zero_or_eq_one_of_isIdempotentElem_of_forall_isSeparable`
  -/
  sorry

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
