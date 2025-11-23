import Mathlib.AlgebraicGeometry.Scheme

universe u

namespace AlgebraicGeometry

/-- Every morphism `X ⟶ Spec (.of R)` induces an `R`-algebra structure on
`Γ(X, U)` for every `U`. -/
noncomputable def algebraOfHomSpec {R : Type u} [CommRing R] {X : Scheme.{u}}
    (s : X ⟶ Spec (.of R)) (U : X.Opens) : Algebra R Γ(X, U) :=
  ((s.appLE ⊤ U (by simp)).hom.comp
    (Scheme.ΓSpecIso <| .of R).commRingCatIsoToRingEquiv.symm.toRingHom).toAlgebra

end AlgebraicGeometry
