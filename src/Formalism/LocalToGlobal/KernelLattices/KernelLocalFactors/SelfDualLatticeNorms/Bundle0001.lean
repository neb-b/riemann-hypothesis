module

public import Formalism.LocalToGlobal.KernelLattices.KerStd
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.BaseEx
public import Formalism.LocalToGlobal.GlobalTheory.GL3.PStdOK
public import Formalism.LocalToGlobal.GlobalTheory.GL3.NormNatCoprime
public import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.PeriodRelations.Bundle0002
public import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.WeierstrassUniqueness.Bundle0001
public import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.NormTwelveCubedEqOneOfFiveLePrime
public import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.Bundle0006
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral

@[expose] public section

-- bundled from Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.SelfDualLatticeNorms.IntCurveOfScale
section
noncomputable section
open scoped BigOperators
open NumberField Formalism.BasicNotions Classical

namespace Formalism.L2.Ker.KS

open Formalism.MainNotions Formalism.L2.Col
open Formalism.L2.Th1.E (IntCurve curveL)

theorem intCurve_of_scale (p : ℕ) [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p]) (L : PeriodPair) (c : ℂ) (hc : c ≠ 0)
    (h : IntCurve (curveL p (Formalism.L2.Th1.F.scalePair L c hc) ι)) (hΔ : ‖ι (L.g₂ ^ 3 - 27 * L.g₃ ^ 2)‖ = 1) :
    IntCurve (curveL p L ι) := by
  have hH := Formalism.L2.Th1.F.homogeneity L c hc
  have h2 : (Formalism.L2.Th1.F.scalePair L c hc).g₂ = (c ^ 4)⁻¹ * L.g₂ := hH.2.2.2.2.2.2.2.2.2.1
  have h3 : (Formalism.L2.Th1.F.scalePair L c hc).g₃ = (c ^ 6)⁻¹ * L.g₃ := hH.2.2.2.2.2.2.2.2.2.2
  obtain ⟨-, -, -, h4, h6, hD⟩ := h
  have hS := fun g2 g3 : ℂ_[p] => (Formalism.L2.Th1.A.shortInv ℂ_[p] g2 g3).2.2.2
  have hιc : ι c ≠ 0 := by simpa using hc
  have hcn : ‖ι c‖ = 1 := by
    unfold curveL at hD
    rw [hS, h2, h3] at hD
    have e : ι ((c ^ 4)⁻¹ * L.g₂) ^ 3 - 27 * ι ((c ^ 6)⁻¹ * L.g₃) ^ 2 = (ι c ^ 12)⁻¹ * ι (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) := by
      simp only [map_mul, map_inv₀, map_pow, map_sub, map_ofNat]
      field_simp
    rw [e, norm_mul, hΔ, mul_one, norm_inv, norm_pow, inv_eq_one] at hD
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by norm_num)).1 hD
  refine ⟨by simp [curveL, Formalism.L2.Th1.A.shortW], by simp [curveL, Formalism.L2.Th1.A.shortW], by simp [curveL, Formalism.L2.Th1.A.shortW], ?_, ?_, ?_⟩
  · have e : (curveL p L ι).a₄ = ι c ^ 4 * (curveL p (Formalism.L2.Th1.F.scalePair L c hc) ι).a₄ := by
      simp only [curveL, Formalism.L2.Th1.A.shortW, h2, map_mul, map_inv₀, map_pow]
      field_simp
    rw [e, norm_mul, norm_pow, hcn, one_pow, one_mul]
    exact h4
  · have e : (curveL p L ι).a₆ = ι c ^ 6 * (curveL p (Formalism.L2.Th1.F.scalePair L c hc) ι).a₆ := by
      simp only [curveL, Formalism.L2.Th1.A.shortW, h3, map_mul, map_inv₀, map_pow]
      field_simp
    rw [e, norm_mul, norm_pow, hcn, one_pow, one_mul]
    exact h6
  · unfold curveL
    rw [hS]
    simpa only [map_sub, map_mul, map_pow, map_ofNat] using hΔ

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ)

theorem disc_one (hcc : TaylorLogMetric.IsCurveIdeal D cc) (hδ : TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) : B.L.g₂ ^ 3 - 27 * B.L.g₃ ^ 2 = 1 := by
  have hL : (B.L.lattice : Set ℂ) = TaylorLogMetric.lamOf D cc δ := by
    rw [← B.lat]; rfl
  obtain ⟨e2, e3⟩ := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.g2_g3_eq_periodPair (TaylorLogMetric.lamOf D cc δ) B.L hL
  have h := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.br_discr_lamOf D cc hcc δ hδ
  rw [← e2, ← e3]
  exact h

theorem intCurve_base (hcc : TaylorLogMetric.IsCurveIdeal D cc) (hδ : TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) (ι : ℂ ≃+* ℂ_[p]) :
    IntCurve (curveL p B.L ι) := by
  have hcm : Formalism.L2.Th1.CM.HasCMBy D.host.d B.L := by
    intro ω hω
    have := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SO.hst B ω hω
    rwa [Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SO.theta_val] at this
  have hd8 : D.host.d % 8 = 7 := dMod8 D
  obtain ⟨c, hc, hI⟩ := Formalism.L2.Th1.Top.good_model_exists_all_primes D.host.d B.L D.host.hyp.2.1.squarefree (by omega) hcm p hp ι
  refine intCurve_of_scale p ι B.L c hc hI ?_
  rw [disc_one B hcc hδ, map_one, norm_one]

theorem chiFac_unit (χ : TaylorLogMetric.IdE D → ℂ) (hχ : TaylorLogMetric.IsChi D χ) (p : ℕ) [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p]) {N N' : ℕ}
    {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)} {L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)}
    (hA : TaylorLogMetric.admitted D N N' L L') (h1 : TaylorLogMetric.EqAt D p (StandardLatticesGL3.stdL D N) L) (h2 : TaylorLogMetric.EqAt D p (StandardLatticesGL3.stdL D N') L') :
    ‖ι (Base.chiFac χ N N' L L')‖ = 1 := by
  obtain ⟨hq, hn⟩ := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.RestC.chiFacUnit χ hχ p ((ι : ℂ →+* ℂ_[p]).comp (algebraMap TaylorLogMetric.Qbar ℂ)) N N' L L' hA h1 h2
  unfold TaylorLogMetric.lamC at hn
  rw [dite_eq_left hq] at hn
  exact hn

end Formalism.L2.Ker.KS
end
end

-- bundled from Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.SelfDualLatticeNorms.KapVal
section
noncomputable section
open NumberField IsDedekindDomain

namespace Formalism.L2.Ker.KS

section Val

variable {K : Type} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime] (f : K →+* ℂ_[p])

theorem normO_le (a : 𝓞 K) : ‖f (a : K)‖ ≤ 1 := by
  obtain ⟨P, hm, hP⟩ := RingOfIntegers.isIntegral_coe a
  let v : Valuation ℂ_[p] NNReal := NormedField.valuation
  have hv := Valuation.integer.integers v
  have h2 : IsIntegral v.integer (f (a : K)) := by
    refine ⟨P.map (Int.castRingHom v.integer), hm.map _, ?_⟩
    rw [Polynomial.eval₂_map]
    have e1 : (algebraMap v.integer ℂ_[p]).comp (Int.castRingHom v.integer) = f.comp (algebraMap ℤ K) :=
      RingHom.ext_int _ _
    rw [e1, ← Polynomial.hom_eval₂]
    have : Polynomial.eval₂ (algebraMap ℤ K) (a : K) P = 0 := hP
    rw [this, map_zero]
  have := (hv.isIntegral_iff_v_le_one).mp h2
  exact_mod_cast this

variable (𝔭 : HeightOneSpectrum (𝓞 K)) (ϖ : 𝓞 K) (h : ℕ) (hgen : 𝔭.asIdeal ^ h = Ideal.span {ϖ}) (hlt : ‖f (ϖ : K)‖ < 1)

include hgen hlt in
theorem norm_lt_of_mem {t : 𝓞 K} (ht : t ∈ 𝔭.asIdeal) : ‖f (t : K)‖ < 1 := by
  have hmem : t ^ h ∈ Ideal.span {ϖ} := hgen ▸ Ideal.pow_mem_pow ht h
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hmem
  have key : ‖f (t : K)‖ ^ h < 1 := by
    have e : ‖f (t : K)‖ ^ h = ‖f (c : K)‖ * ‖f (ϖ : K)‖ := by
      rw [← norm_pow, ← map_pow, ← norm_mul, ← map_mul]
      congr 2
      exact_mod_cast hc.symm
    rw [e]
    calc ‖f (c : K)‖ * ‖f (ϖ : K)‖ ≤ 1 * ‖f (ϖ : K)‖ :=
          mul_le_mul_of_nonneg_right (normO_le f c) (norm_nonneg _)
      _ < 1 := by rw [one_mul]; exact hlt
  have hh : h ≠ 0 := by
    rintro rfl
    simp at key
  exact (pow_lt_one_iff_of_nonneg (norm_nonneg _) hh).mp key

include hgen hlt in
theorem norm_eq_one_of_not_mem {a : 𝓞 K} (ha : a ∉ 𝔭.asIdeal) : ‖f (a : K)‖ = 1 := by
  obtain ⟨b, i, hi, hbi⟩ := 𝔭.isMaximal.exists_inv ha
  have hsmall : ‖f (i : K)‖ < 1 := norm_lt_of_mem f 𝔭 ϖ h hgen hlt hi
  have hba : ‖f (b : K)‖ * ‖f (a : K)‖ = 1 := by
    rw [← norm_mul, ← map_mul]
    have e : ((b : K) * (a : K)) = 1 + -(i : K) := by
      have : ((b * a + i : 𝓞 K) : K) = 1 := by rw [hbi]; rfl
      push_cast at this
      linear_combination this
    rw [e, map_add (f := _), map_neg, map_one]
    rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm] <;> simp [norm_neg] <;> linarith [hsmall]
  refine le_antisymm (normO_le f a) ?_
  calc (1 : ℝ) = ‖f (b : K)‖ * ‖f (a : K)‖ := hba.symm
    _ ≤ 1 * ‖f (a : K)‖ := mul_le_mul_of_nonneg_right (normO_le f b) (norm_nonneg _)
    _ = ‖f (a : K)‖ := one_mul _

include hgen hlt in
theorem norm_pow_int {a : 𝓞 K} (ha : a ≠ 0) :
    ∃ n : ℕ, 𝔭.intValuation a = WithZero.exp (-(n : ℤ)) ∧ ‖f (a : K)‖ ^ h = ‖f (ϖ : K)‖ ^ n := by
  classical
  obtain ⟨n, hva⟩ : ∃ n : ℕ, 𝔭.intValuation a = WithZero.exp (-(n : ℤ)) := ⟨_, 𝔭.intValuation_if_neg ha⟩
  refine ⟨n, hva, ?_⟩
  have hvah : 𝔭.intValuation (a ^ h) = WithZero.exp (-((n * h : ℕ) : ℤ)) := by
    rw [map_pow, hva, ← WithZero.exp_nsmul]
    congr 1
    push_cast
    ring
  have hmem : a ^ h ∈ Ideal.span {ϖ ^ n} := by
    have := (𝔭.intValuation_le_pow_iff_mem (a ^ h) (n * h)).mp hvah.le
    rwa [mul_comm, pow_mul, hgen, Ideal.span_singleton_pow] at this
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hmem
  have hcn : c ∉ 𝔭.asIdeal := by
    intro hcm
    have h1 : a ^ h ∈ 𝔭.asIdeal ^ (n * h + 1) := by
      rw [← hc, pow_succ', mul_comm n h, pow_mul, hgen, Ideal.span_singleton_pow]
      exact Ideal.mul_mem_mul hcm (Ideal.mem_span_singleton_self _)
    have h2 := (𝔭.intValuation_le_pow_iff_mem _ _).mpr h1
    rw [hvah, WithZero.exp_le_exp] at h2
    push_cast at h2
    omega
  have hc1 := norm_eq_one_of_not_mem f 𝔭 ϖ h hgen hlt hcn
  have e : (a : K) ^ h = (c : K) * (ϖ : K) ^ n := by exact_mod_cast hc.symm
  rw [← norm_pow, ← map_pow f, e, map_mul, norm_mul, hc1, one_mul, map_pow, norm_pow]

include hgen hlt in
theorem norm_pow_eq {x : K} (hx : x ≠ 0) :
    ‖f x‖ ^ h = ‖f (ϖ : K)‖ ^ (-WithZero.log (𝔭.valuation K x)) := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 K) x
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have ha0 : a ≠ 0 := by
    rintro rfl
    simp at hx
  obtain ⟨n, hva, hna⟩ := norm_pow_int f 𝔭 ϖ h hgen hlt ha0
  obtain ⟨m, hvb, hnb⟩ := norm_pow_int f 𝔭 ϖ h hgen hlt hb0
  have hϖ : ϖ ≠ 0 := by
    rintro rfl
    rw [Ideal.span_singleton_eq_bot.mpr rfl] at hgen
    exact (pow_ne_zero h 𝔭.ne_bot) hgen
  have hfϖ : ‖f (ϖ : K)‖ ≠ 0 := by simpa using hϖ
  have hva' : 𝔭.valuation K (algebraMap (𝓞 K) K a) = WithZero.exp (-(n : ℤ)) := by
    rw [← hva]
    exact HeightOneSpectrum.valuation_of_algebraMap 𝔭 a
  have hvb' : 𝔭.valuation K (algebraMap (𝓞 K) K b) = WithZero.exp (-(m : ℤ)) := by
    rw [← hvb]
    exact HeightOneSpectrum.valuation_of_algebraMap 𝔭 b
  rw [(𝔭.valuation K).map_div, hva', hvb', ← WithZero.exp_sub, WithZero.log_exp, map_div₀, norm_div,
    div_pow]
  change ‖f (a : K)‖ ^ h / ‖f (b : K)‖ ^ h = _
  rw [hna, hnb, show -(-(n : ℤ) - -(m : ℤ)) = (n : ℤ) - m by ring, zpow_sub₀ hfϖ, zpow_natCast,
    zpow_natCast]

end Val

end Formalism.L2.Ker.KS
end
end

