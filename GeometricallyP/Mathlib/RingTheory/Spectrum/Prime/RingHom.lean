import Mathlib.RingTheory.Spectrum.Prime.RingHom

open Algebra TensorProduct

theorem PrimeSpectrum.preimage_eq_range_tensor_residueField (R S : Type*) [CommRing R]
    [CommRing S] [Algebra R S] (p : PrimeSpectrum R) :
    (algebraMap R S).specComap ⁻¹' {p}
    = Set.range (algebraMap S (S ⊗[R] p.asIdeal.ResidueField)).specComap := by
  ext ps
  simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_range]
  let k := p.asIdeal.ResidueField
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · let f : S ⊗[R] k →ₐ[R] ps.asIdeal.ResidueField :=
      lift (IsScalarTower.toAlgHom _ _ _)
        (Ideal.ResidueField.mapₐ _ _ (by simp only [RingHom.specComap] at h; simp [← h]))
        (fun _ _ ↦ Commute.all ..)
    use f.specComap ⊥
    have : RingHom.comp f (algebraMap S (S ⊗[R] k))
      = algebraMap S ps.asIdeal.ResidueField := by ext; simp [f]
    simp only [AlgHom.toRingHom_eq_coe, ← specComap_comp_apply]
    rw [this]
    exact PrimeSpectrum.ext (Ideal.ext fun x ↦ Ideal.algebraMap_residueField_eq_zero)
  · rcases h with ⟨y, rfl⟩
    have : (algebraMap S (S ⊗[R] p.asIdeal.ResidueField)).comp (algebraMap R S)
        = includeRight.toRingHom.comp (algebraMap R k) := by
      simp only [AlgHom.toRingHom_eq_coe, AlgHom.comp_algebraMap_of_tower]; rfl
    simpa [← specComap_comp_apply, this] using
      (Set.range_eq_singleton_iff.mp <| residueField_specComap p) (includeRight.specComap y)
