import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Nilpotent.Lemmas

lemma Ideal.map_nilradical_le {R S F : Type*}
    [CommSemiring R] [CommSemiring S]
    [FunLike F R S]
    [RingHomClass F R S] (f : F) :
    (nilradical R).map f ≤ nilradical S := by
  convert Ideal.map_radical_le f
  simp [nilradical]
