module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.CycCOfCyclic
public import PositivityTheory.AutomorphicForms.PublishedInputs.CyclicBaseChangeLifts.SplitLift
public import PositivityTheory.AutomorphicForms.PublishedInputs.CyclicBaseChange.SConjSpaceC
public import PositivityTheory.AutomorphicForms.PublishedInputs.CyclicBaseChange.Bundle0001
public import PositivityTheory.AutomorphicForms.PublishedInputs.CyclicBaseChange.P_SSatEx
public import PositivityTheory.AutomorphicForms.PublishedInputs.CyclicBaseChange.PSConjSpaceC
public import PositivityTheory.AutomorphicForms.PublishedInputs.CyclicBaseChange.PSConjSpaceR
public import PositivityTheory.AutomorphicForms.PublishedInputs.CyclicBaseChange.PSConjSatR
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.Bundle0010
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.NormQuad
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.SolvableEquivalenceOfBaseChange
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.Bundle0008
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0055
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0053
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0052
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0056
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.QuadraticInductionGL2Alt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0010
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.SolCOfSolDescent

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.ComplexBaseChangeOfLiterature
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published UpperTheory.CBC

namespace UpperTheory.V.Z.Bc

def CBCc : Prop :=
  ∀ (K M : Type) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M] [IsGalois K M],
    (Module.finrank K M).Prime → IsTotallyComplex K → ∀ n : ℕ, 1 ≤ n →
      (∀ π : Cusp K n, (∃ η : HChar K, IsNormChar M η ∧ (π.twist η).Iso π) ∨
        ∃ P : Cusp M n, WeakBC π.sat P.sat ∧ (∀ τ m, π.inf (τ.comp (algebraMap K M)) m → P.inf τ m) ∧ SplitLift π P) ∧
      (∀ P : Cusp M n, (∀ σ : M ≃ₐ[K] M, P.ConjIso σ.toRingEquiv) →
        ∃ π : Cusp K n, WeakBC π.sat P.sat ∧ (∀ τ m, P.inf τ m → π.inf (τ.comp (algebraMap K M)) m) ∧ SplitLift π P) ∧
      ∀ (π : Cusp K n) (P : Cusp M n), (∀ σ : M ≃ₐ[K] M, P.ConjIso σ.toRingEquiv) → WeakBC π.sat P.sat →
        (∀ η : HChar K, IsNormChar M η → ¬ (π.twist η).Iso π) ∧
        ∀ π₁ : Cusp K n, WeakBC π₁.sat P.sat → ∃ η : HChar K, (η = 1 ∨ IsNormChar M η) ∧ (π.twist η).Iso π₁

def CBCr : Prop :=
  ∀ (K M : Type) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M] [IsGalois K M],
    (Module.finrank K M).Prime → IsTotallyComplex K → ∀ n : ℕ, 1 ≤ n →
      (∀ π : Cusp K n, RegInf n π.inf → (∃ η : HChar K, IsNormChar M η ∧ (π.twist η).Iso π) ∨
        ∃ P : Cusp M n, WeakBC π.sat P.sat ∧ ∀ τ m, π.inf (τ.comp (algebraMap K M)) m → P.inf τ m) ∧
      (∀ P : Cusp M n, RegInf n P.inf → (∀ σ : M ≃ₐ[K] M, P.ConjIso σ.toRingEquiv) →
        ∃ π : Cusp K n, WeakBC π.sat P.sat ∧ ∀ τ m, P.inf τ m → π.inf (τ.comp (algebraMap K M)) m) ∧
      ∀ (π : Cusp K n) (P : Cusp M n), (∀ σ : M ≃ₐ[K] M, P.ConjIso σ.toRingEquiv) → WeakBC π.sat P.sat →
        ∀ π₁ : Cusp K n, WeakBC π₁.sat P.sat → ∃ η : HChar K, (η = 1 ∨ IsNormChar M η) ∧ (π.twist η).Iso π₁

theorem cbcr_of_cbcc (h : CBCc) : CBCr := by
  intro K M _ _ _ _ _ _ hp hK n hn
  obtain ⟨a, b, c⟩ := h K M hp hK n hn
  refine ⟨fun π _ => (a π).imp_right fun ⟨P, h1, h2, _⟩ => ⟨P, h1, h2⟩, fun P _ hP => ?_, fun π P h1 h2 => (c π P h1 h2).2⟩
  obtain ⟨π, h1, h2, _⟩ := b P hP
  exact ⟨π, h1, h2⟩

end UpperTheory.V.Z.Bc
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.GaloisRepRankTwoOfHyps
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published UpperTheory.V.Af.Bc UpperTheory.V.Af.Sol

namespace UpperTheory.V.Z.Bc

def ExRTwo : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime]
    (ι : Qbar l ≃+* ℂ) (π : TR.CuspSub F 2) (χ : HChar F), π.IsRegAlg → π.Polarized χ →
    ∃ r : G F Ω →* GL (Fin 2) (Qbar l), Continuous r ∧ AttR ι r π

theorem galois_rep_rank_two_of_hypotheses (P : HypothesesH) : ExRTwo := fun F Ω _ _ _ _ _ _ l _ ι π χ h1 h2 =>
  let ⟨r, _, _, H, h, _⟩ := exR P F Ω l ι 2 one_le_two π χ h1 h2
  ⟨r, H.cont, h⟩

private theorem cusp_unique {F : Type} [Field F] [NumberField F] {n : ℕ} {sat : HeightOneSpectrum (𝓞 F) → Multiset ℂˣ → Prop}
    {inf : (F →+* ℂ) → Multiset ℂ → Prop} (h : IsCusp n sat inf) : ∀ v B B', sat v B → sat v B' → B = B' := by
  rcases h with ⟨_, π, rfl, -⟩ | ⟨_, π, rfl, -⟩
  · exact fun _ _ _ h h' => h.unique h'
  · exact fun _ _ _ h h' => h.unique h'

private theorem not_both (F : Type) [Field F] [NumberField F] (h : IsTotallyReal F) (h' : IsTotallyComplex F) : False := by
  obtain ⟨v⟩ : Nonempty (InfinitePlace F) := inferInstance
  exact (InfinitePlace.not_isReal_iff_isComplex.2 (h'.isComplex v)) (h.isReal v)

end UpperTheory.V.Z.Bc
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.IndCOfIndComplex
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published UpperTheory.V.Z.Bc

section Places

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

end Places

private theorem infOf_ne {m m' : Fin 2 → ℤ} (h : Function.Injective ![m 0, m 1, m' 0, m' 1]) : infOf m ≠ infOf m' := by
  intro e
  have h1 : (((2 : ℕ) : ℂ) - 1) / 2 + (m 0 : ℂ) ∈ infOf m := Multiset.mem_map.2 ⟨0, Finset.mem_univ_val _, rfl⟩
  rw [e] at h1
  obtain ⟨i, -, hi⟩ := Multiset.mem_map.1 h1
  have h2 : m' i = m 0 := Int.cast_injective (add_left_cancel hi)
  fin_cases i
  · exact absurd (@h 2 0 h2) (by decide)
  · exact absurd (@h 3 0 h2) (by decide)

open UpperTheory.CBC UpperTheory.CBC.SConjSpaceCAux in
private theorem not_conjIso {K M : Type} [Field K] [NumberField K] [Field M] [NumberField M] [_root_.NumberField.IsTotallyComplex M] [Algebra K M]
    [IsGalois K M] (π : CuspSub M 2) (hm : MixWtC K π) : ¬ ∀ σ : M ≃ₐ[K] M, (Cusp.cx π).ConjIso σ.toRingEquiv := by
  intro h
  obtain ⟨φ⟩ : Nonempty (K →+* ℂ) := inferInstance
  obtain ⟨m, m', τ, τ', -, h1, h2, k1, k2, hinj⟩ := hm φ
  obtain ⟨σ, hσ⟩ := ComplexEmbedding.exists_comp_symm_eq_of_comp_eq (k := K) τ τ' (h1.trans h2.symm)
  obtain ⟨s, hs⟩ := SGalAdEx_holds M σ.toRingEquiv
  obtain ⟨P', hsp, hiso⟩ := h σ s hs
  obtain ⟨d, hd, hd'⟩ := exists_GD _ s hs
  cases P' with
  | re π' => exact hiso.elim
  | cx π' =>
    have e : τ.comp (d.σ.symm : M →+* M) = τ' := by
      rw [hd']
      exact hσ
    have k3 : π'.HasInfChar τ (infOf m') := by
      refine ⟨k2.1, fun u x hx => ?_⟩
      have hx' : x.1 ∈ (Cusp.cx π').space := ⟨x, hx, rfl⟩
      rw [hsp] at hx'
      obtain ⟨_, ⟨y, hy, rfl⟩, hxy⟩ := hx'
      obtain rfl : x = pull d 2 y := Subtype.ext (by rw [← hxy, ← hd]; rfl)
      rw [cap_pull, e, k2.2 u y hy, map_smul]
    exact infOf_ne hinj (k1.unique (CuspSub.Iso.hasInfChar hiso k3))
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.SolQ
section
theorem UpperTheory.V.Z.Bc.solQ (h : UpperTheory.V.Z.Bc.SolE) : UpperTheory.V.Z.Bc.SolC := by
  intro F₀ F M Ω _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hsol hplus hF hM l _ ι n hn r μ hr hirr hμ hs ⟨c, P, hc, hP⟩
  exact h F M Ω hsol hF hM l ι n hn r hr hirr ⟨F₀, _, _, _, _, inferInstance, inferInstance, hplus.1, μ, c, P, hμ, hs, hc, hP⟩
end

