module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0002

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.LFun GlobalTheory.CuspRep GlobalTheory.HeckeGal.Model

namespace GlobalTheory.Published.JacquetShalikaModel

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]


open NumberField IsDedekindDomain in
variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] in
omit [_root_.NumberField.IsTotallyComplex E] in
theorem _root_.GlobalTheory.Published.JacquetShalikaModel.infinite_places : Infinite (HeightOneSpectrum (𝓞 E)) := by
  classical
  by_contra h
  rw [not_infinite_iff_finite] at h
  have hfin : (Set.range fun P : HeightOneSpectrum (𝓞 E) =>
      Ideal.comap (algebraMap ℤ (𝓞 E)) P.asIdeal).Finite := Set.finite_range _
  apply Nat.infinite_setOf_prime
  have hinj : Set.InjOn (fun p : ℕ => Ideal.span {(p : ℤ)}) {p | p.Prime} := by
    intro p _ q _ hpq
    have := Ideal.span_singleton_eq_span_singleton.mp hpq
    rw [Int.associated_iff_natAbs] at this
    simpa using this
  refine Set.Finite.of_finite_image (hfin.subset ?_) hinj
  rintro _ ⟨p, hp, rfl⟩
  haveI hmax : (Ideal.span {(p : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hp).irreducible
  obtain ⟨Q, hQ, hlies⟩ :=
    Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 E) (Ideal.span {(p : ℤ)})
  have hcomap : Ideal.comap (algebraMap ℤ (𝓞 E)) Q = Ideal.span {(p : ℤ)} :=
    (hlies.over).symm
  have hne : Q ≠ ⊥ := by
    rintro rfl
    have hmem : (p : ℤ) ∈ Ideal.comap (algebraMap ℤ (𝓞 E)) (⊥ : Ideal (𝓞 E)) :=
      hcomap ▸ Ideal.subset_span rfl
    rw [Ideal.mem_comap, Ideal.mem_bot, map_natCast, Nat.cast_eq_zero] at hmem
    exact hp.ne_zero hmem
  exact ⟨⟨Q, hQ.isPrime, hne⟩, hcomap⟩

end GlobalTheory.Published.JacquetShalikaModel
