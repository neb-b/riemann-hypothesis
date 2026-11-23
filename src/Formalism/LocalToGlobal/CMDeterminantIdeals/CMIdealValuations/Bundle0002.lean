module

public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.Bundle0001
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.ProdMulLeDetIdeal
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.ValuationLeOfEqAlgebraMap
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.AbsNormSpanGalois
public import Formalism.LocalToGlobal.CMDeterminantIdeals.HadamardLoc0

@[expose] public section

-- bundled from Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.AbsNormEqRelIndexMul
section
noncomputable section

namespace Formalism.L2.LamCM

open NumberField IsDedekindDomain
open scoped nonZeroDivisors ComplexOrder

namespace Dx

variable {K : Type} [Field K] [NumberField K]

theorem absNorm_eq_relIndex_mul (J J' : FractionalIdeal (𝓞 K)⁰ K) (hJ' : J' ≠ 0) (hle : J' ≤ J) :
    FractionalIdeal.absNorm J' = ((J' : Submodule (𝓞 K) K).toAddSubgroup.relIndex
      (J : Submodule (𝓞 K) K).toAddSubgroup : ℚ) * FractionalIdeal.absNorm J := by
  have hJ : J ≠ 0 := by rintro rfl; exact hJ' (FractionalIdeal.le_zero_iff.1 hle)
  have hX : J' * J⁻¹ ≤ 1 := by
    calc J' * J⁻¹ ≤ J * J⁻¹ := mul_le_mul' hle le_rfl
      _ = 1 := mul_inv_cancel₀ hJ
  obtain ⟨X, hX'⟩ := FractionalIdeal.le_one_iff_exists_coeIdeal.1 hX
  have hdec : J' = J * (X : FractionalIdeal (𝓞 K)⁰ K) := by
    rw [hX', mul_comm J', ← mul_assoc, mul_inv_cancel₀ hJ, one_mul]
  obtain ⟨c, P, hc, hP⟩ := FractionalIdeal.exists_eq_spanSingleton_mul J
  let φ : 𝓞 K →+ K := (AddMonoidHom.mulLeft ((algebraMap (𝓞 K) K c)⁻¹)).comp (algebraMap (𝓞 K) K).toAddMonoidHom
  have hc' : (algebraMap (𝓞 K) K c)⁻¹ ≠ 0 :=
    inv_ne_zero ((map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).2 hc)
  have hφ : Function.Injective φ := by
    intro r s h
    have h' : (algebraMap (𝓞 K) K c)⁻¹ * algebraMap (𝓞 K) K r = (algebraMap (𝓞 K) K c)⁻¹ * algebraMap (𝓞 K) K s := h
    exact IsFractionRing.injective (𝓞 K) K (mul_left_cancel₀ hc' h')
  have hmap : ∀ Q : Ideal (𝓞 K), ((FractionalIdeal.spanSingleton (𝓞 K)⁰ (algebraMap (𝓞 K) K c)⁻¹ *
      (Q : FractionalIdeal (𝓞 K)⁰ K) : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K).toAddSubgroup =
      Q.toAddSubgroup.map φ := by
    intro Q
    ext x
    simp only [Submodule.mem_toAddSubgroup, FractionalIdeal.coe_mul, FractionalIdeal.coe_spanSingleton,
      Submodule.mem_span_singleton_mul, AddSubgroup.mem_map]
    constructor
    · rintro ⟨z, hz, rfl⟩
      obtain ⟨r, hr, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hz
      exact ⟨r, hr, rfl⟩
    · rintro ⟨r, hr, rfl⟩
      exact ⟨algebraMap (𝓞 K) K r, (FractionalIdeal.mem_coeIdeal _).2 ⟨r, hr, rfl⟩, rfl⟩
  have hJ'P : J' = FractionalIdeal.spanSingleton (𝓞 K)⁰ (algebraMap (𝓞 K) K c)⁻¹ *
      ((P * X : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) := by
    rw [hdec, hP, FractionalIdeal.coeIdeal_mul, mul_assoc]
  have hrel : (J' : Submodule (𝓞 K) K).toAddSubgroup.relIndex (J : Submodule (𝓞 K) K).toAddSubgroup =
      (P * X).toAddSubgroup.relIndex P.toAddSubgroup := by
    rw [hJ'P, hmap, hP, hmap, AddSubgroup.relIndex_map_map_of_injective _ _ hφ]
  have hPX : P * X ≤ P := by simpa [mul_comm] using (Ideal.mul_le_right : X * P ≤ P)
  have htow := AddSubgroup.relIndex_mul_relIndex (P * X).toAddSubgroup P.toAddSubgroup ⊤ hPX le_top
  rw [AddSubgroup.relIndex_top_right, AddSubgroup.relIndex_top_right] at htow
  have hn : ∀ Q : Ideal (𝓞 K), Ideal.absNorm Q = Q.toAddSubgroup.index := fun Q => by
    rw [Ideal.absNorm_apply]; rfl
  have hmul : Ideal.absNorm (P * X) = Ideal.absNorm P * Ideal.absNorm X := map_mul _ _ _
  rw [hn, hn, hn] at hmul
  have hP0 : P.toAddSubgroup.index ≠ 0 := by
    rw [← hn]
    intro h
    apply hJ
    rw [hP, Ideal.absNorm_eq_zero_iff.1 h, FractionalIdeal.coeIdeal_bot, mul_zero]
  have hidx : (P * X).toAddSubgroup.relIndex P.toAddSubgroup = Ideal.absNorm X := by
    rw [hn X]
    apply Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hP0)
    rw [htow, hmul, mul_comm]
  rw [hrel, hidx, hdec, map_mul, FractionalIdeal.coeIdeal_absNorm, mul_comm]

end Dx

end Formalism.L2.LamCM
end
end

-- bundled from Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.DetValuationLeOne
section
noncomputable section

namespace Formalism.L2.LamCM

open NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped nonZeroDivisors ComplexOrder

theorem key_formula_link : KeyCoreLink := by
  intro h
  obtain ⟨κ, h1, h2, h3, h4⟩ := h
  refine ⟨κ, h1, h2, ?_, h4.2⟩
  intro R K _ _ _ _ _ _ _ x xK hpb
  obtain ⟨u, hu, -⟩ := h3 R K x xK hpb
  exact ⟨u, hu⟩

section Core

end Core

section Lie

end Lie

section Had

variable {K : Type} [Field K] [NumberField K]

theorem prod_span_le_of_loc {g : ℕ} (abelian₂ : MLine K) (ℓ : Fin g → MLine K) (d : K) (hLam : abelian₂.I ≠ 0)
    (hℓ : ∀ j, (ℓ j).I ≠ 0) (hd : d ≠ 0)
    (hloc : ∀ p : HeightOneSpectrum (𝓞 K), ∃ (cd : K) (cl : Fin g → K), IsLocGen p cd abelian₂.I ∧
      (∀ j, IsLocGen p (cl j) (ℓ j).I) ∧ p.valuation K ((∏ j, cl j) * d) ≤ p.valuation K cd) :
    (∏ j, (ℓ j).I) * FractionalIdeal.spanSingleton (𝓞 K)⁰ d ≤ abelian₂.I := by
  have hP : (∏ j, (ℓ j).I) ≠ 0 := Finset.prod_ne_zero_iff.2 fun j _ => hℓ j
  have hs : FractionalIdeal.spanSingleton (𝓞 K)⁰ d ≠ 0 := spanSingleton_ne_zero' hd
  have hX0 : (∏ j, (ℓ j).I) * FractionalIdeal.spanSingleton (𝓞 K)⁰ d ≠ 0 := mul_ne_zero hP hs
  have h1 : (∏ j, (ℓ j).I) * FractionalIdeal.spanSingleton (𝓞 K)⁰ d * abelian₂.I⁻¹ ≤ 1 := by
    apply le_one_of_count_nonneg (mul_ne_zero hX0 (inv_ne_zero hLam))
    intro p
    obtain ⟨cd, cl, hcd, hcl, hv⟩ := hloc p
    have hgen : IsLocGen p ((∏ j, cl j) * d) ((∏ j, (ℓ j).I) * FractionalIdeal.spanSingleton (𝓞 K)⁰ d) :=
      IsLocGen.mul' (IsLocGen.prod' Finset.univ cl (fun j => (ℓ j).I) hcl hℓ) ⟨hd, rfl⟩ hP hs
    rw [FractionalIdeal.count_mul K p hX0 (inv_ne_zero hLam), FractionalIdeal.count_inv, ← hgen.2, ← hcd.2]
    rw [valuation_eq_exp_count p hgen.1, valuation_eq_exp_count p hcd.1, WithZero.exp_le_exp] at hv
    omega
  calc (∏ j, (ℓ j).I) * FractionalIdeal.spanSingleton (𝓞 K)⁰ d
      = (∏ j, (ℓ j).I) * FractionalIdeal.spanSingleton (𝓞 K)⁰ d * abelian₂.I⁻¹ * abelian₂.I := by
        rw [mul_assoc _ abelian₂.I⁻¹, inv_mul_cancel₀ hLam, mul_one]
    _ ≤ 1 * abelian₂.I := mul_le_mul' h1 le_rfl
    _ = abelian₂.I := one_mul _

theorem hadamard_of_le (g : ℕ) (abelian₂ : MLine K) (ℓ : Fin g → MLine K) (u : Fin g → Fin g → K)
    (H : (K →+* ℂ) → Matrix (Fin g) (Fin g) ℂ) (La : ℝ) (hLam : abelian₂.I ≠ 0) (hℓ : ∀ j, (ℓ j).Good)
    (hdne : (Matrix.of u).det ≠ 0) (hLa : 0 < La) (hH : ∀ σ, (H σ).PosDef)
    (hn : ∀ σ, abelian₂.n σ = Real.sqrt (H σ).det.re)
    (hle : (∏ j, (ℓ j).I) * FractionalIdeal.spanSingleton (𝓞 K)⁰ (Matrix.of u).det ≤ abelian₂.I)
    (hsq : ∀ σ j, ReciprocityTheory.MultiplicativeHeights.hq (H σ) (ReciprocityTheory.MultiplicativeHeights.embVec σ (u j)) ≤ (La * (ℓ j).n σ) ^ 2) :
    ∑ j, (ℓ j).deg - (g : ℝ) * (Module.finrank ℚ K : ℝ) * Real.log La ≤ abelian₂.deg := by
  set d := (Matrix.of u).det with hd
  have hX0 : (∏ j, (ℓ j).I) * FractionalIdeal.spanSingleton (𝓞 K)⁰ d ≠ 0 :=
    mul_ne_zero (Finset.prod_ne_zero_iff.2 fun j _ => (hℓ j).1)
      (by rwa [Ne, FractionalIdeal.spanSingleton_eq_zero_iff])
  have hN := A2.absNorm_anti' hle hX0
  have hposI : ∀ j, (0 : ℝ) < ((FractionalIdeal.absNorm (ℓ j).I : ℚ) : ℝ) := fun j => by
    exact_mod_cast A2.absNorm_pos' (hℓ j).1
  have hposd : ∀ σ : K →+* ℂ, 0 < ‖σ d‖ := fun σ => norm_pos_iff.2 ((map_ne_zero σ).2 hdne)
  have hposD := A2.absNorm_pos' hLam
  have hNX : ((FractionalIdeal.absNorm ((∏ j, (ℓ j).I) * FractionalIdeal.spanSingleton (𝓞 K)⁰ d) : ℚ) : ℝ) =
      (∏ j, ((FractionalIdeal.absNorm (ℓ j).I : ℚ) : ℝ)) * ∏ σ : K →+* ℂ, ‖σ d‖ := by
    rw [map_mul, map_prod, Rat.cast_mul, Rat.cast_prod, A2.absNorm_span_real]
  have hlogN : Real.log ((FractionalIdeal.absNorm abelian₂.I : ℚ) : ℝ) ≤
      ∑ j, Real.log ((FractionalIdeal.absNorm (ℓ j).I : ℚ) : ℝ) + ∑ σ : K →+* ℂ, Real.log ‖σ d‖ := by
    rw [← Real.log_prod (fun j _ => (hposI j).ne'), ← Real.log_prod (fun σ _ => (hposd σ).ne'),
      ← Real.log_mul (Finset.prod_pos fun j _ => hposI j).ne' (Finset.prod_pos fun σ _ => hposd σ).ne', ← hNX]
    exact Real.log_le_log (by exact_mod_cast hposD) (by exact_mod_cast hN)
  have hσ : ∀ σ : K →+* ℂ, Real.log ‖σ d‖ + Real.log (Real.sqrt (H σ).det.re) ≤
      ∑ j, (Real.log La + Real.log ((ℓ j).n σ)) := by
    intro σ
    have hD := A2.det_re_pos (hH σ)
    have hGpd : (ReciprocityTheory.MultiplicativeHeights.gramC (H σ) σ u).PosDef := by
      rw [A2.gramC_eq]
      apply (hH σ).conjTranspose_mul_mul_same
      apply Matrix.mulVec_injective_iff_isUnit.2
      rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_transpose, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
      exact IsUnit.mk0 _ ((map_ne_zero σ).2 hdne)
    have hdiagpos : ∀ j, 0 < (ReciprocityTheory.MultiplicativeHeights.gramC (H σ) σ u j j).re := fun j => by
      simpa using (Complex.lt_def.1 (hGpd.diag_pos (i := j))).1
    have hHd := hadamardInequality g _ hGpd
    rw [A2.gramC_det, Complex.re_ofReal_mul] at hHd
    have hbound : ∏ j, (ReciprocityTheory.MultiplicativeHeights.gramC (H σ) σ u j j).re ≤ ∏ j, (La * (ℓ j).n σ) ^ 2 := by
      apply Finset.prod_le_prod₀
      · intro j _
        exact (hdiagpos j).le
      · intro j _
        exact hsq σ j
    have key : ‖σ d‖ ^ 2 * (H σ).det.re ≤ ∏ j, (La * (ℓ j).n σ) ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq]
      exact hHd.trans hbound
    have hpos' : 0 < ‖σ d‖ ^ 2 * (H σ).det.re := by
      have := hposd σ
      positivity
    have hlog := Real.log_le_log hpos' key
    have hnpos : ∀ j, 0 < (ℓ j).n σ := fun j => (hℓ j).2 σ
    rw [Real.log_mul (by have := hposd σ; positivity) hD.ne', Real.log_pow,
      Real.log_prod (fun j _ => by have := hnpos j; positivity)] at hlog
    have hs : ∑ j, Real.log ((La * (ℓ j).n σ) ^ 2) = 2 * ∑ j, (Real.log La + Real.log ((ℓ j).n σ)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [Real.log_pow, Real.log_mul hLa.ne' (hnpos j).ne']
      push_cast
      ring
    rw [hs] at hlog
    rw [Real.log_sqrt hD.le]
    push_cast at hlog
    linarith
  have hsumσ := Finset.sum_le_sum fun σ (_ : σ ∈ (Finset.univ : Finset (K →+* ℂ))) => hσ σ
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul] at hsumσ
  have hc : ∑ σ : K →+* ℂ, ∑ j, Real.log ((ℓ j).n σ) = ∑ j, ∑ σ : K →+* ℂ, Real.log ((ℓ j).n σ) :=
    Finset.sum_comm
  have hcard : (Fintype.card (K →+* ℂ) : ℝ) = Module.finrank ℚ K := by
    exact_mod_cast NumberField.Embeddings.card K ℂ
  rw [hc, hcard] at hsumσ
  have hLd : abelian₂.deg = -Real.log ((FractionalIdeal.absNorm abelian₂.I : ℚ) : ℝ) -
      ∑ σ, Real.log (Real.sqrt (H σ).det.re) := by
    simp only [MLine.deg, hn]
  rw [hLd]
  simp only [MLine.deg, Finset.sum_sub_distrib, Finset.sum_neg_distrib]
  linarith

end Had

theorem hadamard_local_base : HadamardLoc0 := by
  intro K _ _ g abelian₂ ℓ U H La hLam hℓ hdet hLa hH hn hloc hsq
  have hle := prod_span_le_of_loc abelian₂ ℓ U.det hLam (fun j => (hℓ j).1) hdet hloc
  exact hadamard_of_le g abelian₂ ℓ U H La hLam hℓ hdet hLa hH hn hle hsq

end Formalism.L2.LamCM
end
end

