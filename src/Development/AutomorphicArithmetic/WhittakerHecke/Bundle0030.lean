module

public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.CharacterNorms.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.Bundle0002
public import Development.AutomorphicArithmetic.WhittakerHecke.RatIdeleAbsRealIdeleNatIdeleUnitIdeles
public import Development.AutomorphicArithmetic.WhittakerHecke.Bundle0026
public import Development.AutomorphicArithmetic.WhittakerHecke.Bundle0019
public import Development.AutomorphicArithmetic.WhittakerHecke.Bundle0027

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.WhittakerHecke.HeightOneSpectrumRatCorrespondPrimes
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)
open UpperTheory.V.Af.Smo (EigAt)
open scoped ComplexOrder

private theorem cast_dvd {a b : ℕ} : (a : 𝓞 ℚ) ∣ (b : 𝓞 ℚ) ↔ a ∣ b := by
  refine ⟨fun h => ?_, fun h => Nat.cast_dvd_cast h⟩
  have h1 := map_dvd Rat.ringOfIntegersEquiv h
  rw [map_natCast, map_natCast] at h1
  exact Int.natCast_dvd_natCast.1 h1

private theorem mem_iff_dvd (N : ℕ) (v : HeightOneSpectrum (𝓞 ℚ)) :
    (N : 𝓞 ℚ) ∈ v.asIdeal ↔ normV v ∣ N := by
  rw [← cast_dvd, ← Ideal.mem_span_singleton, ← (UpperTheory.V.Af.Nf.places v).2.1]

theorem UpperTheory.heightOneSpectrum_rat_correspond_primes :
    (∀ v : H.P ℚ, (normV v).Prime) ∧ (∀ p : ℕ, p.Prime → ∃ v : H.P ℚ, normV v = p) ∧ (∀ v v' : H.P ℚ, normV v = normV v' → v = v') ∧
          (∀ (N : ℕ) (v : H.P ℚ), Bad N v ↔ normV v ∣ N) := by
  refine ⟨fun v => (UpperTheory.V.Af.Nf.places v).1, fun p hp => ?_, fun v v' h => ?_, fun N v => mem_iff_dvd N v⟩
  · have hnt : Ideal.span {(p : 𝓞 ℚ)} ≠ ⊤ := by
      rw [Ne, Ideal.span_singleton_eq_top, isUnit_iff_dvd_one, ← Nat.cast_one, cast_dvd, Nat.dvd_one]
      exact hp.ne_one
    obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hnt
    have hpM : (p : 𝓞 ℚ) ∈ M := hle (Ideal.mem_span_singleton_self _)
    have hM0 : M ≠ ⊥ := by
      rintro rfl
      exact hp.ne_zero (Nat.cast_eq_zero.1 (Ideal.mem_bot.1 hpM))
    let w : HeightOneSpectrum (𝓞 ℚ) := ⟨M, hM.isPrime, hM0⟩
    exact ⟨w, (Nat.prime_dvd_prime_iff_eq (UpperTheory.V.Af.Nf.places w).1 hp).1 ((mem_iff_dvd p w).1 hpM)⟩
  · apply HeightOneSpectrum.ext
    rw [(UpperTheory.V.Af.Nf.places v).2.1, (UpperTheory.V.Af.Nf.places v').2.1, h]
end

-- bundled from Development.AutomorphicArithmetic.WhittakerHecke.TwistedZetaIntegralAtCompactEqAtRotation
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)
open UpperTheory.V.Af.Smo (EigAt)
open scoped ComplexOrder

theorem UpperTheory.twisted_zeta_integral_at_compact_eq_at_rotation :
    ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (D : Dat ℚ E) (P : CuspSub E 2) (ω χ : HChar ℚ),
        CenN P ω → Unit1 ω → (∀ a, (χ.1 a * ω.1 a) ^ 2 = 1) → ∀ (L N : ℕ), ChOk χ L → ∀ φ, admitted D ω φ → Gd D P L N φ → ∀ (s : ℂ), ∀ k ∈ KK ℚ, k ∈ SS N → ∀ t : ℝ, re (k 1 0) = Real.sin t → re (k 1 1) = Real.cos t →
        Yt D χ φ s (gl k) = Yt D χ φ s (rot t) := by
  intro E _ _ _ D P ω χ hC hU hχ L N hL φ hA hG s k hk hS t hs hc
  obtain ⟨b, ζ, κ, hζ, hκ, hdec⟩ := UpperTheory.exists_unipotent_diag_rotation_level_decomposition N hG.pos k hk hS t hs hc
  have hab : ab ζ = 1 := UpperTheory.ratIdeleAbs_realIdele_natIdele_unitIdeles.2.2.1 ζ hζ
  have habm : ∀ y : (A ℚ)ˣ, ab (y * ζ ^ 2) = ab y := by
    intro y
    have h1 : IdeleGroup.ideleModule ℚ ζ = 1 := Subtype.ext hab
    show ((IdeleGroup.ideleModule ℚ (y * ζ ^ 2) : {r : ℝ // 0 < r}) : ℝ) = _
    rw [map_mul, map_pow, h1, one_pow, mul_one]
    rfl
  have hχω : ((ω.1 ζ⁻¹ : ℂˣ) : ℂ) ^ 2 = ((χ.1 ζ : ℂˣ) : ℂ) ^ 2 := by
    have h := hχ ζ
    have h2 : (ω.1 ζ⁻¹) ^ 2 = (χ.1 ζ) ^ 2 := by
      rw [map_inv, inv_pow, inv_eq_iff_mul_eq_one, ← mul_pow, mul_comm]
      exact h
    exact_mod_cast congrArg (fun u : ℂˣ => (u : ℂ)) h2
  let Gf : IdeleGroup ℚ → ℂ := fun y => Wo D φ (em E (aE y * rot t)) * ((χ.1 y : ℂˣ) : ℂ) * ((ab y : ℝ) : ℂ) ^ (s - 1)
  have key : ∀ y : IdeleGroup ℚ, Wo D φ (em E (aE y * gl k)) * ((χ.1 y : ℂˣ) : ℂ) * ((ab y : ℝ) : ℂ) ^ (s - 1) = Gf (y * ζ ^ 2) := by
    intro y
    rw [hdec, UpperTheory.whittaker_diagTorus_mul_iwasawa_eq E D ω φ hA N hG.lev y ζ b (rot t) κ hκ, hχω]
    show _ = Wo D φ (em E (aE (y * ζ ^ 2) * rot t)) * ((χ.1 (y * ζ ^ 2) : ℂˣ) : ℂ) * ((ab (y * ζ ^ 2) : ℝ) : ℂ) ^ (s - 1)
    have hχm : χ.1 (y * ζ ^ 2) = χ.1 y * χ.1 ζ ^ 2 := by rw [map_mul, map_pow]
    rw [habm, hχm]
    push_cast
    ring
  unfold Yt
  rw [integral_congr_ae (Filter.Eventually.of_forall key)]
  exact integral_mul_right_eq_self Gf (ζ ^ 2)
end

