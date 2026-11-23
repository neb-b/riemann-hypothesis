module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Classifies
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0738
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.LevelTwistCyclotomicPow
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0028
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0029

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial GlobalTheory.GalOfCusp UpperTheory.V.Af

private theorem not_mem_of_distinct_prime {K : Type} [Field K] [NumberField K] {p l : ℕ} (w : HeightOneSpectrum (𝓞 K)) (hp : p.Prime)
    (hl : l.Prime) (hlp : l ≠ p) (hw : (p : 𝓞 K) ∈ w.asIdeal) : (l : 𝓞 K) ∉ w.asIdeal := by
  intro h
  have hc : IsCoprime (l : 𝓞 K) (p : 𝓞 K) := Nat.Coprime.cast ((Nat.coprime_primes hl hp).2 hlp)
  obtain ⟨a, b, hab⟩ := hc
  exact w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2
    (hab ▸ w.asIdeal.add_mem (w.asIdeal.mul_mem_left a h) (w.asIdeal.mul_mem_left b hw)))

private theorem admissible_twist_cyclotomic {K Ω : Type} [Field K] [NumberField K] [IsCMField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (e N : ℕ) (ρ : G K Ω →* GL (Fin 3) (Qbar l)) (h : Adm3 ι e N ρ) :
    AdmK ι N ![(e : ℤ) - 1, -1, -(e : ℤ) - 1] (tw ρ (cycBar K Ω l)⁻¹) := by
  refine ⟨(UpperTheory.isIrr_twist_and_repIso_of_twist_repIso _ _ 3 _).1 ρ h.irr, h.aut, ?_, by decide⟩
  have h1 := UpperTheory.level_twist_cyclotomic_pow K Ω l 3 N _ ρ (-1) h.level
  rw [zpow_neg_one] at h1
  convert h1 using 1
  funext i
  fin_cases i <;> simp <;> ring
