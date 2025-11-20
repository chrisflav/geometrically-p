import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.IsSepClosed
import Mathlib.FieldTheory.SeparableDegree
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.Ideal.GoingDown
import Mathlib.RingTheory.RingHom.Flat
import Mathlib.RingTheory.IsAdjoinRoot

/-!
# Auxiliary results on tensor products
-/

universe v u

variable {k : Type u} {R : Type*} [Field k] [CommRing R] [Algebra k R]

open TensorProduct

lemma Ideal.under_mono {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    {I J : Ideal S} (hIJ : I ≤ J) : I.under R ≤ J.under R :=
  Ideal.comap_mono hIJ

lemma Ideal.under_mem_minimalPrimes (R : Type*) {S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.HasGoingDown R S] (p : Ideal S) (hp : p ∈ minimalPrimes S) :
    p.under R ∈ minimalPrimes R := by
  rw [minimalPrimes_eq_minimals, Set.mem_setOf_eq]
  have : p.IsPrime := hp.1.1
  refine ⟨inferInstance, fun q hq hle ↦ ?_⟩
  obtain ⟨Q, hQle, hQ, ho⟩ := Ideal.exists_ideal_le_liesOver_of_le p hle
  obtain rfl : p = Q := le_antisymm (hp.2 ⟨hQ, bot_le⟩ hQle) hQle
  rw [ho.1]

lemma RingHom.Flat.tensorProductMap_left {R S A B C : Type*}
    [CommRing R] [CommRing S] [Algebra R S] [CommRing A] [Algebra R A] [Algebra S A]
    [IsScalarTower R S A] [CommRing B] [Algebra R B] [CommRing C] [Algebra R C] [Algebra S C]
    [IsScalarTower R S C] (f : A →ₐ[S] C)-- (g : B →ₐ[R] D)
    (hf : f.toRingHom.Flat) : (Algebra.TensorProduct.map f (.id R B)).Flat := by
  algebraize [f.toRingHom, (Algebra.TensorProduct.map f (.id R B)).toRingHom]
  have : IsScalarTower R A C := .of_algHom (f.restrictScalars R)
  let e : C ⊗[R] B ≃ₐ[A] (A ⊗[R] B) ⊗[A] C :=
    ((Algebra.TensorProduct.cancelBaseChange R A A C B).symm).trans
      (Algebra.TensorProduct.comm ..).symm
  have : (Algebra.TensorProduct.map f (AlgHom.id R B)).toRingHom =
      (e.symm : _ →+* _).comp (algebraMap (A ⊗[R] B) ((A ⊗[R] B) ⊗[A] C)) := by
    ext x
    induction x with
    | zero => simp
    | add x y hx hy => simp_all [add_tmul]
    | tmul x y => simp [e, Algebra.smul_def, RingHom.algebraMap_toAlgebra]
  rw [this]
  apply RingHom.Flat.comp
  · rw [RingHom.flat_algebraMap_iff]
    infer_instance
  · apply RingHom.Flat.of_bijective e.symm.bijective

lemma RingHom.Flat.tensorProductMap {R S A B C D : Type*}
    [CommRing R] [CommRing S] [Algebra R S] [CommRing A] [Algebra R A] [Algebra S A]
    [IsScalarTower R S A] [CommRing B] [Algebra R B] [CommRing C] [Algebra R C] [Algebra S C]
    [IsScalarTower R S C] [CommRing D] [Algebra R D] (f : A →ₐ[S] C) (g : B →ₐ[R] D)
    (hf : f.toRingHom.Flat) (hg : g.toRingHom.Flat) :
    (Algebra.TensorProduct.map f g).Flat := by
  have : Algebra.TensorProduct.map f g =
      (Algebra.TensorProduct.map (.id _ _) g).comp (Algebra.TensorProduct.map f (.id _ _)) := by
    ext <;> rfl
  rw [this]
  refine RingHom.Flat.comp (.tensorProductMap_left _ hf) ?_
  change (Algebra.TensorProduct.map (AlgHom.id R C) g).Flat
  have : Algebra.TensorProduct.map (AlgHom.id R C) g =
      AlgHom.comp (Algebra.TensorProduct.comm ..).toAlgHom
        ((Algebra.TensorProduct.map g (AlgHom.id R C)).comp <|
          (Algebra.TensorProduct.comm ..).toAlgHom) := by ext <;> rfl
  rw [this]
  exact (RingHom.Flat.of_bijective (Algebra.TensorProduct.comm R C B).bijective).comp
    (.tensorProductMap_left _ hg) |>.comp <| .of_bijective (AlgEquiv.bijective _)

lemma Algebra.TensorProduct.exists_intermediateField_isSeparable_and_mem_range
    (Ω : Type*) [Field Ω] [Algebra k Ω] [Algebra.IsSeparable k Ω] (x : Ω ⊗[k] R) :
    ∃ (K : IntermediateField k Ω), Algebra.IsSeparable k K ∧ Module.Finite k K ∧
        x ∈ Set.range
          (Algebra.TensorProduct.map (IsScalarTower.toAlgHom k K Ω) (AlgHom.id k R)) := by
  induction x with
  | zero => exact ⟨⊥, inferInstance, inferInstance, 0, by simp⟩
  | add x y hx hy =>
    obtain ⟨K, hK₁, hK₂, ⟨x, rfl⟩⟩ := hx
    obtain ⟨L, hL₁, hL₂, ⟨y, rfl⟩⟩ := hy
    let instK : Algebra ↥K ↥(K ⊔ L) :=
      (IntermediateField.inclusion le_sup_left).toRingHom.toAlgebra
    let _ : Module ↥K ↥(K ⊔ L) := instK.toModule
    let instL : Algebra ↥L ↥(K ⊔ L) :=
      (IntermediateField.inclusion le_sup_right).toRingHom.toAlgebra
    let _ : Module ↥L ↥(K ⊔ L) := instL.toModule
    let gK : K ⊗[k] R →ₐ[k] ↥(K ⊔ L) ⊗[k] R :=
      Algebra.TensorProduct.map (IsScalarTower.toAlgHom k K _) (AlgHom.id k R)
    let gL : L ⊗[k] R →ₐ[k] ↥(K ⊔ L) ⊗[k] R :=
      Algebra.TensorProduct.map (IsScalarTower.toAlgHom k L _) (AlgHom.id k R)
    let f (K : IntermediateField k Ω) : K ⊗[k] R →ₐ[k] Ω ⊗[k] R :=
      Algebra.TensorProduct.map (IsScalarTower.toAlgHom _ _ _) (AlgHom.id k R)
    have hK : (f (K ⊔ L)).comp gK = f K := by ext <;> rfl
    have hL : (f (K ⊔ L)).comp gL = f L := by ext <;> rfl
    refine ⟨K ⊔ L, inferInstance, inferInstance, gK x + gL y, ?_⟩
    trans (f (K ⊔ L)) (gK x) + (f (K ⊔ L)) (gL y)
    · exact (f (K ⊔ L)).map_add (gK x) (gL y)
    · exact congr($(DFunLike.congr_fun hK x) + $(DFunLike.congr_fun hL y))
  | tmul x y =>
    refine ⟨IntermediateField.adjoin k {x}, ?_, ?_,
        ⟨x, IntermediateField.mem_adjoin_simple_self k x⟩ ⊗ₜ y, rfl⟩
    · rw [IntermediateField.isSeparable_adjoin_simple_iff_isSeparable]
      exact Algebra.IsSeparable.isSeparable k x
    · apply IntermediateField.adjoin.finiteDimensional
      exact Algebra.IsIntegral.isIntegral x

lemma Algebra.TensorProduct.exists_field_isSeparable_and_mem_range (Ω : Type v) [Field Ω]
    [Algebra k Ω] [Algebra.IsSeparable k Ω] (x : Ω ⊗[k] R) :
    ∃ (K : Type v) (_ : Field K) (_ : Algebra k K) (_ : Algebra K Ω) (_ : IsScalarTower k K Ω),
      Algebra.IsSeparable k K ∧ Module.Finite k K ∧
        x ∈ Set.range
          (Algebra.TensorProduct.map (IsScalarTower.toAlgHom k K Ω) (AlgHom.id k R)) := by
  obtain ⟨K, _, _, hK⟩ :=
    Algebra.TensorProduct.exists_intermediateField_isSeparable_and_mem_range _ x
  use K, inferInstance, inferInstance, inferInstance, inferInstance

/-- If `K ⊗[k] R` has up to one minimal prime for every finite, separable extension `K` of `k`,
the same holds for `Ω ⊗[k] R` for every separable extension `Ω` of `k`. -/
lemma subsingleton_minimalPrimes_of_isSeparable
    (H : ∀ (K : Type v) [Field K] [Algebra k K] [Module.Finite k K] [Algebra.IsSeparable k K],
      (minimalPrimes (K ⊗[k] R)).Subsingleton) (Ω : Type v) [Field Ω] [Algebra k Ω]
      [Algebra.IsSeparable k Ω] :
    (minimalPrimes (Ω ⊗[k] R)).Subsingleton := by
  refine fun p hp q hq ↦ ?_
  ext x
  obtain ⟨K, _, _, _, _, _, _, ⟨x, hx, rfl⟩⟩ :=
    Algebra.TensorProduct.exists_field_isSeparable_and_mem_range _ x
  let f : K ⊗[k] R →ₐ[k] Ω ⊗[k] R :=
    Algebra.TensorProduct.map (IsScalarTower.toAlgHom _ _ _) (AlgHom.id k R)
  let _ : Algebra (K ⊗[k] R) (Ω ⊗[k] R) := f.toRingHom.toAlgebra
  have : f.toRingHom.Flat := by
    refine .tensorProductMap _ _ ?_ (.of_bijective <| Function.Involutive.bijective (congrFun rfl))
    simp only [AlgHom.toRingHom_eq_coe, IsScalarTower.coe_toAlgHom, RingHom.flat_algebraMap_iff]
    infer_instance
  have : Module.Flat (K ⊗[k] R) (Ω ⊗[k] R) := this
  have : p.under (K ⊗[k] R) = q.under (K ⊗[k] R) :=
    (H K) (p.under_mem_minimalPrimes (K ⊗[k] R) hp) (q.under_mem_minimalPrimes (K ⊗[k] R) hq)
  exact SetLike.ext_iff.mp this x

/-- If `K ⊗[k] R` has no non-trivial idempontents for every finite, separable extension `K` of `k`,
the same holds for `Ω ⊗[k] R` for every separable extension `Ω` of `k`. -/
lemma eq_zero_or_eq_one_of_isIdempotentElem_of_forall_isSeparable
    (H : ∀ (K : Type v) [Field K] [Algebra k K] [Module.Finite k K] [Algebra.IsSeparable k K]
      (e : K ⊗[k] R), IsIdempotentElem e → e = 0 ∨ e = 1) (Ω : Type v) [Field Ω] [Algebra k Ω]
      [Algebra.IsSeparable k Ω] (e : Ω ⊗[k] R) (he : IsIdempotentElem e) :
    e = 0 ∨ e = 1 := by
  -- argue as in `subsingleton_minimalPrimes_of_isSeparable`
  sorry

/-- If for every finitely generated subalgebra `S'` of `S`
and finitely generated subalgebra `T'` of `T`, the tensor product
`S' ⊗[R] T'` is a domain, then also `S ⊗[R] T` is a domain. -/
@[stacks 00I3 "(2) in contrapositive form"]
lemma isDomain_tensorProduct_of_forall_isDomain_of_FG
    {R S T : Type*} [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
    (H : ∀ (S' : Subalgebra R S) (T' : Subalgebra R T),
      S'.FG → T'.FG → IsDomain (S' ⊗[R] T')) :
    IsDomain (S ⊗[R] T) :=
  sorry
