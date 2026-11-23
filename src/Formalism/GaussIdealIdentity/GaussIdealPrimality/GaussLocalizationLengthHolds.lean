module

public import Formalism.GaussIdealIdentity.StatementLA

@[expose] public section

open MvPolynomial IsLocalRing

noncomputable section

namespace Formalism.DV.GaussP

variable (σ O : Type) [Fintype σ] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

theorem gaussIdeal_isPrime : (gaussIdeal σ O).IsPrime := by
  have h := MvPolynomial.ker_map (σ := σ) (IsLocalRing.residue O)
  rw [IsLocalRing.ker_residue] at h
  unfold gaussIdeal
  rw [← h]
  exact RingHom.ker_isPrime _

variable [(gaussIdeal σ O).IsPrime]

local notation "A" => Localization.AtPrime (gaussIdeal σ O)

theorem maximalIdeal_eq :
    IsLocalRing.maximalIdeal A = Ideal.map (algebraMap O A) (IsLocalRing.maximalIdeal O) := by
  rw [← Localization.AtPrime.map_eq_maximalIdeal, IsScalarTower.algebraMap_eq O (MvPolynomial σ O) A,
    ← Ideal.map_map, MvPolynomial.algebraMap_eq]
  try rfl

theorem algebraMap_injective : Function.Injective (algebraMap O A) := by
  rw [IsScalarTower.algebraMap_eq O (MvPolynomial σ O) A, RingHom.coe_comp, MvPolynomial.algebraMap_eq]
  exact (IsLocalization.injective (S := A) (M := (gaussIdeal σ O).primeCompl)
    (Ideal.primeCompl_le_nonZeroDivisors (gaussIdeal σ O))).comp (MvPolynomial.C_injective σ O)

instance isDomain_A : IsDomain A :=
  IsLocalization.isDomain_localization (Ideal.primeCompl_le_nonZeroDivisors (gaussIdeal σ O))

instance isNoetherianRing_A : IsNoetherianRing A :=
  IsLocalization.isNoetherianRing (gaussIdeal σ O).primeCompl A inferInstance

theorem isDVR : IsDiscreteValuationRing A := by
  obtain ⟨ϖ, hϖ⟩ := Submodule.IsPrincipal.principal (IsLocalRing.maximalIdeal O)
  have hϖ' : IsLocalRing.maximalIdeal O = Ideal.span {ϖ} := hϖ
  have hmA : IsLocalRing.maximalIdeal A = Ideal.span {algebraMap O A ϖ} := by
    rw [maximalIdeal_eq σ O, hϖ', Ideal.map_span, Set.image_singleton]
  have hne : algebraMap O A ϖ ≠ 0 := by
    intro h0
    apply IsDiscreteValuationRing.not_a_field O
    rw [hϖ', Ideal.span_singleton_eq_bot]
    exact algebraMap_injective σ O (h0.trans (map_zero _).symm)
  have hnf : ¬ IsField A := by
    rw [IsLocalRing.isField_iff_maximalIdeal_eq, hmA, Ideal.span_singleton_eq_bot]
    exact hne
  have hp : (IsLocalRing.maximalIdeal A).IsPrincipal := ⟨⟨_, hmA⟩⟩
  exact ((IsDiscreteValuationRing.TFAE A hnf).out 1 5).2 hp

instance isLocalHom_A : IsLocalHom (algebraMap O A) := by
  constructor
  intro a ha
  rw [IsScalarTower.algebraMap_eq O (MvPolynomial σ O) A, RingHom.comp_apply,
    IsLocalization.AtPrime.isUnit_to_map_iff A (gaussIdeal σ O)] at ha
  by_contra hna
  apply ha
  have : a ∈ IsLocalRing.maximalIdeal O := hna
  show MvPolynomial.C a ∈ gaussIdeal σ O
  exact Ideal.mem_map_of_mem _ this

end GaussP

end Formalism.DV
