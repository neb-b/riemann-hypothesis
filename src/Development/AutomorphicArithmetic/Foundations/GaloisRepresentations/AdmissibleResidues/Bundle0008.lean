module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.Bundle0006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.Bundle0009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.SymmetricCubeUnits.Sym3AutKOf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.SolCOfSolDescent
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.RhoKApply
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.Bundle0010
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.Bundle0007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.WeightChange
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.QuadraticSplitting.QuadSplit
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.QuadraticInductionGL2Alt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.PurityTempered.AlgPowConst
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.CountRankThree
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.CsdSsOfFull
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.Bundle0008
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.QuadraticTwists.ExtReal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.QuadraticTwists.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0033
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0763
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0165
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0212
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0009

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.PolarizedAutomorphicOfAutP
section
noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base

namespace UpperTheory.GalN.V

section
variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}
  {ι : Qbar l ≃+* ℂ} {r r' : G F Ω →* GL (Fin n) (Qbar l)}

theorem Wit.iso' [IsCMField F] (e : RepIso r r') (hU : Wit ι r) : Wit ι r' := by
  intro w hw A hA hfin
  obtain ⟨g, hg⟩ := e
  have hfin' : (r '' (Ine (F := F) A : Set (G F Ω))).Finite := by
    refine (hfin.image (fun x => g⁻¹ * x * g)).subset ?_
    rintro _ ⟨s, hs, rfl⟩
    refine ⟨r' s, ⟨s, hs, rfl⟩, ?_⟩
    simp only [hg s]
    group
  obtain ⟨s, j, hj, hF, h⟩ := hU w hw A hA hfin'
  refine ⟨s, j, hj, hF, fun α β hα hβ k hk => ?_⟩
  rw [hg s, Units.val_mul, Units.val_mul, Matrix.coe_units_inv, Matrix.charpoly_units_conj] at hα hβ
  exact h α β hα hβ k hk

theorem attC_iso [_root_.NumberField.IsTotallyComplex F] {π : CuspSub F n} (h : RepIso r r') (H : AttC ι r π) : AttC ι r' π := by
  refine ⟨?_, H.2.mono fun _ ⟨B, hB, hB'⟩ => ⟨B, hB, hB'.of_iso h⟩⟩
  obtain ⟨g, hg⟩ := h
  let e : (Fin n → Qbar l) ≃ₗ[Qbar l] (Fin n → Qbar l) :=
    Matrix.toLin'OfInv (M := (g : Matrix (Fin n) (Fin n) (Qbar l)))
      (M' := ((g⁻¹ : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)))
      (Units.mul_inv g) (Units.inv_mul g)
  have he (v : Fin n → Qbar l) :
      e v = ((g⁻¹ : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)).mulVec v := rfl
  have intertwine (s : G F Ω) (v : Fin n → Qbar l) :
      e ((r' s : Matrix (Fin n) (Fin n) (Qbar l)).mulVec v) =
        (r s : Matrix (Fin n) (Fin n) (Qbar l)).mulVec (e v) := by
    rw [he, he, hg s, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Units.val_mul, ← Units.val_mul]
    congr 2
    group
  intro W hW
  obtain ⟨W', hW', hc⟩ := H.1 (W.map e.toLinearMap) (by
    rintro s _ ⟨v, hv, rfl⟩
    exact ⟨_, hW s v hv, intertwine s v⟩)
  refine ⟨W'.comap e.toLinearMap, fun s v hv => ?_, ?_⟩
  · show e _ ∈ W'
    rw [intertwine]
    exact hW' s (e v) hv
  · have hcompl : IsCompl ((W.map e.toLinearMap).comap e.toLinearMap) (W'.comap e.toLinearMap) :=
      (Submodule.orderIsoMapComap e).symm.isCompl hc
    rwa [Submodule.comap_map_eq_of_injective e.injective] at hcompl

theorem autCsd_iso {F Ω : Type} [Field F] [NumberField F] [IsCMField F] [Field Ω] [Algebra F Ω] {l : ℕ}
    [Fact l.Prime] {n : ℕ} {ι : Qbar l ≃+* ℂ} {r r' : G F Ω →* GL (Fin n) (Qbar l)} (h : Af.RepIso r r')
    (H : IsAutCsdN ι r) : IsAutCsdN ι r' :=
  ⟨H.1.imp fun _ k => ⟨k.1, k.2.1, attC_iso h k.2.2⟩, fun c => (H.2 (continuous_of_iso c h.symm')).iso' h⟩

end

def NewformAut0 : Prop :=
  ∀ (k : ℕ), 2 ≤ k → ∀ (f : Newform k) (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω]
    (ι : Qbar l ≃+* ℂ) (W : G ℚ Ω →* GL (Fin 2) (Qbar l)) (j : ℤ), f.Att ι (tw W (cycBar ℚ Ω l ^ j)) → IsAutomorphicOverImagQuad ι W

end UpperTheory.GalN.V
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.SeedDefs
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial IsLocalRing
open GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Sd UpperTheory.V.Sd.S2

namespace UpperTheory.GalN.V

def PropEGN : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ) (c : G ℚ Ω), Sd.IsCC c →
    ∀ (N w : ℕ) (φ θ : G ℚ Ω →* (Qbar l)ˣ), SlopeTestRemainingChoices N w θ → SplitAt N w φ → φ ≠ 1 → ∃ k₀ : ℕ, ∀ k ≥ k₀, φ c = (-1) ^ k →
      ∃ ρ, EisRep ι φ θ k ρ ∧ RW ι ρ

section
variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {D : Raw Ω c} (T : Tower D)

def Wts0 (h : Fin 4 → ℤ) (P : PD T.ι (G T.F Ω) (PadicAlgCl l)) : Prop :=
  ∃ U : Subgroup (G T.F Ω), IsOpen (U : Set (G T.F Ω)) ∧ ∀ v i, ∀ s ∈ U ⊓ Ine (F := T.F) (T.pl v),
    P.ψ v i s ^ 2 = ((cycBar T.F Ω l s ^ h i : (PadicAlgCl l)ˣ) : PadicAlgCl l)

variable {T} {h : Fin 4 → ℤ} {P : PD T.ι (G T.F Ω) (PadicAlgCl l)}

theorem mkWts (k : Wts0 T h P) (_ : h 1 + 4 ≤ h 0 → haveI := T.nF; Unlinked P.r.toHomUnits) : T.Wts h P := k
theorem mkWts4 (k : Wts0 T (fun i => 2 * D.wts4 i) P) : T.Wts (fun i => 2 * D.wts4 i) P :=
  mkWts k fun hb => absurd hb (by simp [Raw.wts4]; omega)
end

end UpperTheory.GalN.V
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.WinFreePU
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Th
open scoped Pointwise

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem place_under {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {A : ValuationSubring Ω} {p : ℕ}
    (hp0 : p ≠ 0) (hp : A.valuation (p : Ω) < 1) :
    ∃ w : HeightOneSpectrum (𝓞 F), IsPlaceOver A w ∧ (p : 𝓞 F) ∈ w.asIdeal := by
  have hint : A.valuation.Integers A :=
    { hom_inj := Subtype.coe_injective
      map_le_one := fun a => A.valuation_le_one a
      exists_of_le_one := fun r hr => ⟨⟨r, (A.valuation_le_one_iff r).1 hr⟩, rfl⟩ }
  have hle : ∀ x : 𝓞 F, A.valuation (algebraMap F Ω (x : F)) ≤ 1 := by
    intro x
    have h1 : IsIntegral ℤ (algebraMap F Ω (x : F)) :=
      (RingOfIntegers.isIntegral_coe x).map (IsScalarTower.toAlgHom ℤ F Ω)
    exact hint.mem_of_integral (h1.tower_top (A := A))
  let I : Ideal (𝓞 F) :=
    { carrier := {x | A.valuation (algebraMap F Ω (x : F)) < 1}
      add_mem' := by
        intro a b ha hb
        show A.valuation (algebraMap F Ω ((a : F) + (b : F))) < 1
        rw [map_add (f := _)]
        exact A.valuation.map_add_lt ha hb
      zero_mem' := by
        show A.valuation (algebraMap F Ω (0 : F)) < 1
        rw [map_zero, map_zero]
        exact lt_of_le_of_lt zero_le' hp
      smul_mem' := by
        intro c a ha
        show A.valuation (algebraMap F Ω ((c : F) * (a : F))) < 1
        rw [map_mul, map_mul]
        exact lt_of_le_of_lt (mul_le_of_le_one_left' (hle c)) ha }
  have hI : I.IsPrime := by
    refine Ideal.isPrime_iff.2 ⟨?_, ?_⟩
    · rw [Ideal.ne_top_iff_one]
      show ¬ A.valuation (algebraMap F Ω (1 : F)) < 1
      rw [map_one, map_one]
      exact lt_irrefl _
    · intro a b hab
      show A.valuation (algebraMap F Ω (a : F)) < 1 ∨ A.valuation (algebraMap F Ω (b : F)) < 1
      have hab' : A.valuation (algebraMap F Ω (a : F)) * A.valuation (algebraMap F Ω (b : F)) < 1 := by
        have h0 : A.valuation (algebraMap F Ω ((a : F) * (b : F))) < 1 := hab
        rwa [map_mul, map_mul] at h0
      by_contra hne
      push_neg at hne
      have ha1 := le_antisymm (hle a) hne.1
      have hb1 := le_antisymm (hle b) hne.2
      rw [ha1, hb1, mul_one] at hab'
      exact lt_irrefl _ hab'
  have hpI : ((p : ℕ) : 𝓞 F) ∈ I := by
    show A.valuation (algebraMap F Ω (((p : ℕ) : 𝓞 F) : F)) < 1
    change A.valuation (algebraMap F Ω (algebraMap (𝓞 F) F (p : 𝓞 F))) < 1
    rw [map_natCast, map_natCast]
    exact hp
  have hne : I ≠ ⊥ := by
    intro h0
    rw [h0, Ideal.mem_bot] at hpI
    exact hp0 (by exact_mod_cast hpI)
  exact ⟨⟨I, hI, hne⟩, fun x => Iff.rfl, hpI⟩

private theorem pow_eq_one_of_kills {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω]
    {M : ℕ} (hM : 1 ≤ M) : ∃ k : ℕ, 0 < k ∧ ∀ (C : Type) [Monoid C] (χ : G F Ω →* C), KillsMu M χ → ∀ s, χ s ^ k = 1 := by
  classical
  refine ⟨M.factorial, Nat.factorial_pos M, ?_⟩
  intro C _ χ hχ s
  rw [← map_pow]
  refine hχ _ (fun ζ hζ => ?_)
  have hmem : ∀ z : Ω, z ∈ Polynomial.nthRootsFinset M (1 : Ω) ↔ z ^ M = 1 :=
    fun z => Polynomial.mem_nthRootsFinset hM 1
  have hcard : (Polynomial.nthRootsFinset M (1 : Ω)).card ≤ M :=
    (Multiset.toFinset_card_le _).trans (Polynomial.card_nthRoots _ _)
  let σ : Equiv.Perm (Polynomial.nthRootsFinset M (1 : Ω)) :=
    Equiv.subtypeEquiv s.toEquiv (fun z => by
      show z ∈ Polynomial.nthRootsFinset M (1 : Ω) ↔ s z ∈ Polynomial.nthRootsFinset M (1 : Ω)
      rw [hmem, hmem, ← map_pow, map_eq_one_iff _ s.injective])
  have hpow : σ ^ M.factorial = 1 := by
    have h1 := pow_card_eq_one (x := σ)
    rw [Fintype.card_perm, Fintype.card_coe] at h1
    obtain ⟨c, hc⟩ := Nat.factorial_dvd_factorial hcard
    rw [hc, pow_mul, h1, one_pow]
  have hit : ∀ (m : ℕ) (z : Polynomial.nthRootsFinset M (1 : Ω)),
      (((σ ^ m) z : Polynomial.nthRootsFinset M (1 : Ω)) : Ω) = (s ^ m) (z : Ω) := by
    intro m
    induction m with
    | zero =>
      intro z
      rfl
    | succ m ih =>
      intro z
      rw [pow_succ, Equiv.Perm.mul_apply, ih, pow_succ, AlgEquiv.mul_apply]
      rfl
  have h2 := hit M.factorial ⟨ζ, (hmem ζ).2 hζ⟩
  rw [hpow] at h2
  exact h2.symm

private theorem charpoly_of_flag {H k : Type} [Group H] [CommRing k] {n : ℕ} {r : H →* GL (Fin n) k}
    {κ : Fin n → H →* kˣ} (h : W.HasFlag r κ) (s : H) (b : GL (Fin n) k) :
    ((b * r s * b⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).charpoly = ∏ i, (X - C ((κ i s : kˣ) : k)) := by
  obtain ⟨g, hg⟩ := h
  rw [show b * r s * b⁻¹ = (b * g⁻¹) * (g * r s * g⁻¹) * (b * g⁻¹)⁻¹ by group]
  rw [Units.val_mul, Units.val_mul, Matrix.coe_units_inv, Matrix.charpoly_units_conj,
    Matrix.charpoly_of_upperTriangular _ (fun i j hij => (hg s).1 i j hij)]
  exact Finset.prod_congr rfl (fun i _ => by rw [(hg s).2 i])
end

