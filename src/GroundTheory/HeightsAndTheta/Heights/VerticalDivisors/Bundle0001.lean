module

public import Mathlib

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PSpecChartQuot
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

noncomputable section

namespace SpecChart

variable {A : Type*} [CommRing A] (W : Ideal A) [W.IsPrime] (P : Ideal A)

theorem isLocalization_quot :
    IsLocalization (W.primeCompl.map (Ideal.Quotient.mk P))
      (Localization.AtPrime W ⧸ P.map (algebraMap A (Localization.AtPrime W))) := by
  rw [_root_.isLocalization_iff]
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨_, s, hs, rfl⟩
    rw [Ideal.Quotient.algebraMap_quotient_map_quotient]
    exact (IsLocalization.map_units (Localization.AtPrime W) (⟨s, hs⟩ : W.primeCompl)).map _
  · intro z
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective W.primeCompl x
    refine ⟨⟨Ideal.Quotient.mk P a, ⟨_, s.1, s.2, rfl⟩⟩, ?_⟩
    simp only [Ideal.Quotient.algebraMap_quotient_map_quotient, ← map_mul, IsLocalization.mk'_spec]
  · intro x y h
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [Ideal.Quotient.algebraMap_quotient_map_quotient, Ideal.Quotient.algebraMap_quotient_map_quotient,
      Ideal.Quotient.eq, ← map_sub, IsLocalization.mem_map_algebraMap_iff W.primeCompl] at h
    obtain ⟨⟨⟨p, hp⟩, ⟨t, ht⟩⟩, h⟩ := h
    simp only at h
    rw [← map_mul, IsLocalization.eq_iff_exists W.primeCompl] at h
    obtain ⟨⟨u, hu⟩, h⟩ := h
    refine ⟨⟨Ideal.Quotient.mk P (u * t), ⟨u * t, W.primeCompl.mul_mem hu ht, rfl⟩⟩, ?_⟩
    simp only
    rw [← map_mul, ← map_mul, Ideal.Quotient.eq, ← mul_sub]
    have h' : u * ((a - b) * t) = u * p := h
    rw [show u * t * (a - b) = u * ((a - b) * t) by ring, h']
    exact P.mul_mem_left _ hp

theorem flat_of_isLocalization_comp {R S T : Type*} [CommRing R] [CommRing S] [CommRing T] [Algebra R S]
    (M : Submonoid R) [IsLocalization M S] (g : S →+* T) (hg : (g.comp (algebraMap R S)).Flat) :
    g.Flat := by
  letI := g.toAlgebra
  letI : Algebra R T := (g.comp (algebraMap R S)).toAlgebra
  haveI : IsScalarTower R S T := IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact (Module.flat_iff_of_isLocalization S M T).mpr hg

end SpecChart

end

end GroundTheory.Heights₂.Heights.Vertical
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.StatementsFibreCompDim
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial IsDedekindDomain

def FibreCompDim.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDedekindDomain O] (F : Type) [Field F] [Algebra O F]
    [IsFractionRing O F] (n : ℕ) (P W : Ideal (MvPolynomial (Fin n) O)) (v : HeightOneSpectrum O),
    P.IsPrime → P.comap (C : O →+* MvPolynomial (Fin n) O) = ⊥ →
      W ∈ (P ⊔ Ideal.map (C : O →+* MvPolynomial (Fin n) O) v.asIdeal).minimalPrimes →
        ringKrullDim (MvPolynomial (Fin n) v.asIdeal.ResidueField ⧸
            W.map (MvPolynomial.map (algebraMap O v.asIdeal.ResidueField))) =
          ringKrullDim (MvPolynomial (Fin n) F ⧸ P.map (MvPolynomial.map (algebraMap O F)))

end GroundTheory.Heights₂.Heights.Vertical
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.StatementsFibreCut
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial IsDedekindDomain

def FibreClosedComponent.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDedekindDomain O] (F : Type) [Field F] [Algebra O F]
    [IsFractionRing O F] (n : ℕ) (P W : Ideal (MvPolynomial (Fin n) O)) (v : HeightOneSpectrum O),
    P.IsPrime → P.comap (C : O →+* MvPolynomial (Fin n) O) = ⊥ →
      W ∈ (P ⊔ Ideal.map (C : O →+* MvPolynomial (Fin n) O) v.asIdeal).minimalPrimes →
        W.IsMaximal →
          ringKrullDim (MvPolynomial (Fin n) F ⧸ P.map (MvPolynomial.map (algebraMap O F))) = 0

def FibreCut.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDedekindDomain O] (n : ℕ) (P W : Ideal (MvPolynomial (Fin n) O))
    (v : HeightOneSpectrum O),
    P.IsPrime → P.comap (C : O →+* MvPolynomial (Fin n) O) = ⊥ →
      W ∈ (P ⊔ Ideal.map (C : O →+* MvPolynomial (Fin n) O) v.asIdeal).minimalPrimes →
        ¬ W.IsMaximal →
          ∃ (P' W' : Ideal (MvPolynomial (Fin n) O)) (f : MvPolynomial (Fin n) O),
            f ∉ P ∧ P' ∈ (P ⊔ Ideal.span {f}).minimalPrimes ∧
            P'.comap (C : O →+* MvPolynomial (Fin n) O) = ⊥ ∧
            W' ∈ (P' ⊔ Ideal.map (C : O →+* MvPolynomial (Fin n) O) v.asIdeal).minimalPrimes ∧
            ringKrullDim (MvPolynomial (Fin n) O ⧸ W') + 1 = ringKrullDim (MvPolynomial (Fin n) O ⧸ W)

def GenericFibreDrop.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsNoetherianRing O] (F : Type) [Field F] [Algebra O F]
    [IsFractionRing O F] (n : ℕ) (P P' : Ideal (MvPolynomial (Fin n) O))
    (f : MvPolynomial (Fin n) O),
    P.IsPrime → P'.comap (C : O →+* MvPolynomial (Fin n) O) = ⊥ → f ∉ P →
      P' ∈ (P ⊔ Ideal.span {f}).minimalPrimes →
        ringKrullDim (MvPolynomial (Fin n) F ⧸ P.map (MvPolynomial.map (algebraMap O F))) =
          ringKrullDim (MvPolynomial (Fin n) F ⧸ P'.map (MvPolynomial.map (algebraMap O F))) + 1

def CodimOnePrimeAvoid.Statement : Prop :=
  ∀ (k B : Type) [Field k] [CommRing B] [IsDomain B] [Algebra k B] [Algebra.FiniteType k B] (h : B),
    h ≠ 0 → 1 ≤ ringKrullDim B →
      ∃ N : Ideal B, N.IsPrime ∧ h ∉ N ∧ ringKrullDim (B ⧸ N) + 1 = ringKrullDim B

end GroundTheory.Heights₂.Heights.Vertical
end

