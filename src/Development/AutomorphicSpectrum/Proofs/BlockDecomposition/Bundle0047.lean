module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.KernelL2RowsColumns
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SchwartzBilinear.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0021
public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.StripEntire
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0041
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.Splits

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RowIntOfKerBasic
section
open MeasureTheory
open scoped ENNReal Pointwise

namespace GlobalTheory.CompanionTheory.KernelRows

open PositivityTheory.Rg.BcB.E1

theorem rowInt_of_kerBasic : KerBasic → RowInt := by
  intro hK X φ hφ
  haveI : MeasurableConstSMul X.Γ X.G := ⟨fun γ => measurable_const_mul (γ : X.G)⟩
  haveI : SMulInvariantMeasure X.Γ X.G X.μ := ⟨fun γ s _ => measure_preimage_mul _ γ.1 s⟩
  have hc : Continuous φ := hφ.1
  have hcs : HasCompactSupport φ := hφ.2
  have hc' : Continuous fun z : X.G => φ z⁻¹ := hc.comp continuous_inv
  have hcs' : HasCompactSupport fun z : X.G => φ z⁻¹ :=
    hcs.comp_homeomorph (Homeomorph.inv X.G)
  have hfin1 : ∫⁻ z, ‖φ z‖ₑ ∂X.μ ≠ ⊤ :=
    (hc.integrable_of_hasCompactSupport (μ := X.μ) hcs).2.ne
  have hfin2 : ∫⁻ z, ‖φ z⁻¹‖ₑ ∂X.μ ≠ ⊤ :=
    (hc'.integrable_of_hasCompactSupport (μ := X.μ) hcs').2.ne
  have hb := (hK X φ hφ).2.2.2.2.2
  have hν : X.ν = X.μ.restrict X.F := rfl
  refine ⟨∫⁻ z, ‖φ z‖ₑ ∂X.μ + ∫⁻ z, ‖φ z⁻¹‖ₑ ∂X.μ, ENNReal.add_ne_top.2 ⟨hfin1, hfin2⟩, ?_, ?_⟩
  · intro x
    calc ∫⁻ y, ‖ker X.Γ φ x y‖ₑ ∂X.ν
        ≤ ∫⁻ y, ∑' γ : X.Γ, ‖φ (x⁻¹ * (γ : X.G) * y)‖ₑ ∂X.ν := lintegral_mono (hb x)
      _ = ∑' γ : X.Γ, ∫⁻ y in X.F, ‖φ (x⁻¹ * (γ • y))‖ₑ ∂X.μ := by
          rw [hν, lintegral_tsum]
          · refine tsum_congr fun γ => lintegral_congr fun y => ?_
            rw [Subgroup.smul_def, smul_eq_mul, mul_assoc]
          · intro γ
            exact (hc.comp (by fun_prop)).enorm.aemeasurable
      _ = ∫⁻ y, ‖φ (x⁻¹ * y)‖ₑ ∂X.μ :=
          (X.fd.lintegral_eq_tsum'' (fun y => ‖φ (x⁻¹ * y)‖ₑ)).symm
      _ = ∫⁻ y, ‖φ y‖ₑ ∂X.μ := lintegral_mul_left_eq_self (fun y => ‖φ y‖ₑ) x⁻¹
      _ ≤ _ := le_self_add
  · intro y
    calc ∫⁻ x, ‖ker X.Γ φ x y‖ₑ ∂X.ν
        ≤ ∫⁻ x, ∑' γ : X.Γ, ‖φ (x⁻¹ * (γ : X.G) * y)‖ₑ ∂X.ν :=
          lintegral_mono fun x => hb x y
      _ = ∑' γ : X.Γ, ∫⁻ x in X.F, ‖φ (x⁻¹ * (γ : X.G) * y)‖ₑ ∂X.μ := by
          rw [hν, lintegral_tsum]
          intro γ
          exact (hc.comp (by fun_prop)).enorm.aemeasurable
      _ = ∑' γ : X.Γ, ∫⁻ x in X.F, ‖φ ((γ • x)⁻¹ * y)‖ₑ ∂X.μ := by
          rw [← (Equiv.inv X.Γ).tsum_eq]
          refine tsum_congr fun γ => lintegral_congr fun x => ?_
          simp [Subgroup.smul_def, smul_eq_mul, mul_inv_rev]
      _ = ∫⁻ x, ‖φ (x⁻¹ * y)‖ₑ ∂X.μ :=
          (X.fd.lintegral_eq_tsum'' (fun x => ‖φ (x⁻¹ * y)‖ₑ)).symm
      _ = ∫⁻ z, ‖φ z⁻¹‖ₑ ∂X.μ := by
          rw [← lintegral_mul_left_eq_self (fun x => ‖φ (x⁻¹ * y)‖ₑ) y]
          refine lintegral_congr fun z => ?_
          simp [mul_inv_rev]
      _ ≤ _ := le_add_self

end GlobalTheory.CompanionTheory.KernelRows
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SchurOpOfSchurL
section
noncomputable section

open MeasureTheory
open scoped ENNReal

namespace GlobalTheory.CompanionTheory.Schur

open PositivityTheory.Rg.BcB.E1

variable {α : Type} [MeasurableSpace α] {ν : Measure α}

theorem eLpNorm_two_sq (f : α → ℂ) : eLpNorm' f 2 ν ^ 2 = ∫⁻ x, ‖f x‖ₑ ^ 2 ∂ν := by
  simpa [ENNReal.rpow_ofNat] using
    (lintegral_rpow_eNorm_eq_rpow_eLpNorm' (f := f) (μ := ν) (q := 2) (by norm_num)).symm

theorem schur_memLp (hS : SchurL) [SFinite ν] (k : α → α → ℂ) (A : ℝ≥0∞)
    (hk : Measurable (Function.uncurry k)) (hA : A ≠ ⊤)
    (hr : ∀ x, ∫⁻ y, ‖k x y‖ₑ ∂ν ≤ A) (hc : ∀ y, ∫⁻ x, ‖k x y‖ₑ ∂ν ≤ A)
    (g : α → ℂ) (hg : MemLp g 2 ν) :
    MemLp (fun x => ∫ y, k x y * g y ∂ν) 2 ν ∧
      eLpNorm (fun x => ∫ y, k x y * g y ∂ν) 2 ν ≤ A * eLpNorm g 2 ν ∧
      ∀ᵐ x ∂ν, Integrable (fun y => k x y * g y) ν := by
  have norm_sq (f : α → ℂ) (hf : AEStronglyMeasurable f ν) :
      eLpNorm f 2 ν ^ 2 = ∫⁻ x, ‖f x‖ₑ ^ 2 ∂ν := by
    simpa [ENNReal.rpow_ofNat] using eLpNorm_nnreal_pow_eq_lintegral (p := 2) (by norm_num) hf
  have hkK : Measurable (Function.uncurry fun x y => ‖k x y‖ₑ) := hk.eNorm
  have hgSm := hg.aestronglyMeasurable
  have hgm : AEMeasurable (fun y => ‖g y‖ₑ) ν := hgSm.eNorm
  have key := hS α ν (fun x y => ‖k x y‖ₑ) A (fun y => ‖g y‖ₑ) hkK hgm hr hc
  have hgfin : eLpNorm g 2 ν ≠ ⊤ := hg.ne
  have hsq : ∫⁻ y, ‖g y‖ₑ ^ 2 ∂ν = eLpNorm g 2 ν ^ 2 := (norm_sq g hgSm).symm
  have hbound : ∫⁻ x, (∫⁻ y, ‖k x y‖ₑ * ‖g y‖ₑ ∂ν) ^ 2 ∂ν ≤ (A * eLpNorm g 2 ν) ^ 2 := by
    rw [mul_pow, ← hsq]; exact key
  have hfin : (A * eLpNorm g 2 ν) ^ 2 ≠ ⊤ := ENNReal.pow_ne_top (ENNReal.mul_ne_top hA hgfin)
  have hprod : AEStronglyMeasurable (fun p : α × α => k p.1 p.2 * g p.2) (ν.prod ν) :=
    hk.stronglyMeasurable.aestronglyMeasurable.mul hgSm.comp_snd
  have hSm : AEStronglyMeasurable (fun x => ∫ y, k x y * g y ∂ν) ν :=
    hprod.integral_prod_right'
  have hhm : AEMeasurable (fun x => ∫⁻ y, ‖k x y‖ₑ * ‖g y‖ₑ ∂ν) ν := by
    have : AEMeasurable (fun p : α × α => ‖k p.1 p.2‖ₑ * ‖g p.2‖ₑ) (ν.prod ν) := by
      simpa [eNorm_mul] using hprod.eNorm
    exact this.lintegral_prod_right'
  have hle : eLpNorm (fun x => ∫ y, k x y * g y ∂ν) 2 ν ≤ A * eLpNorm g 2 ν := by
    refine (ENNReal.pow_right_strictMono two_ne_zero).le_iff_le.1 ?_
    rw [norm_sq _ hSm]
    refine le_trans (lintegral_mono fun x => ?_) hbound
    refine pow_le_pow_left' ?_ 2
    refine (eNorm_integral_le_lintegral_eNorm _).trans ?_
    simp [eNorm_mul]
  refine ⟨hle.trans_lt (ENNReal.mul_ne_top hA hgfin).lt_top, hle, ?_⟩
  have hae : ∀ᵐ x ∂ν, (∫⁻ y, ‖k x y‖ₑ * ‖g y‖ₑ ∂ν) ^ 2 < ⊤ :=
    ae_lt_top' (hhm.pow_const 2) (ne_top_of_le_ne_top hfin hbound)
  filter_upwards [hae] with x hx
  have hxf : ∫⁻ y, ‖k x y‖ₑ * ‖g y‖ₑ ∂ν < ⊤ := by
    refine lt_top_iff_ne_top.2 fun hcon => ?_
    simp [hcon] at hx
  have hkx : Measurable (k x) := hk.of_uncurry_left
  refine ⟨hkx.aestronglyMeasurable.mul hgSm, ?_⟩
  simpa [HasFiniteIntegral, eNorm_mul] using hxf

theorem schurOp_of_schurL (hS : SchurL) : SchurOp := by
  intro α _ ν _ k A hk hA hr hc
  have H := fun f : Lp ℂ 2 ν => schur_memLp hS k A hk hA hr hc (f : α → ℂ) (Lp.memLp f)
  let L : Lp ℂ 2 ν →ₗ[ℂ] Lp ℂ 2 ν :=
    { toFun := fun f => (H f).1.toLp _
      map_add' := by
        intro f g
        apply Lp.ext
        have h1 := (H (f + g)).1.coeFn_toLp
        have h2 := (H f).1.coeFn_toLp
        have h3 := (H g).1.coeFn_toLp
        have h4 := Lp.coeFn_add ((H f).1.toLp _) ((H g).1.toLp _)
        filter_upwards [h1, h2, h3, h4, (H f).2.2, (H g).2.2] with x e1 e2 e3 e4 i1 i2
        rw [e1, e4, Pi.add_apply, e2, e3, ← integral_add i1 i2]
        refine integral_congr_ae ?_
        filter_upwards [Lp.coeFn_add f g] with y hy
        rw [hy, Pi.add_apply, mul_add]
      map_smul' := by
        intro c f
        apply Lp.ext
        have h1 := (H (c • f)).1.coeFn_toLp
        have h2 := (H f).1.coeFn_toLp
        have h4 := Lp.coeFn_smul c ((H f).1.toLp _)
        filter_upwards [h1, h2, h4] with x e1 e2 e4
        rw [e1, RingHom.id_apply, e4, Pi.smul_apply, e2, smul_eq_mul, ← integral_const_mul]
        refine integral_congr_ae ?_
        filter_upwards [Lp.coeFn_smul c f] with y hy
        rw [hy, Pi.smul_apply, smul_eq_mul]
        ring }
  refine ⟨L.mkContinuous A.toReal ?_, fun f => (H f).1.coeFn_toLp⟩
  intro f
  change ‖(H f).1.toLp _‖ ≤ A.toReal * ‖f‖
  rw [Lp.norm_toLp, Lp.norm_def, ← ENNReal.toReal_mul]
  exact ENNReal.toReal_mono (ENNReal.mul_ne_top hA (Lp.memLp f).ne) (H f).2.1

end GlobalTheory.CompanionTheory.Schur

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SchwartzFourierTransformMatrix
section
open scoped Matrix SchwartzMap FourierTransform RealInnerProductSpace
open MeasureTheory

namespace GlobalTheory.CompanionTheory.FourierMatrix

theorem exists_schwartz_bilinear_transform {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V)
    [μ.IsAddHaarMeasure] (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (hB : ∀ u, (∀ v, B u v = 0) → u = 0)
    (φ : 𝓢(V, ℂ)) :
    ∃ ψ : 𝓢(V, ℂ), ⇑ψ = fun u =>
      ∫ v, Complex.exp (2 * Real.pi * Complex.I * ((B u v : ℝ) : ℂ)) * φ v ∂μ :=
  _root_.UpperTheory.Reformulated.B.P6.r12b.GlobalTheory.CompanionTheory.FourierMatrix.exists_schwartz_bilinear_transform μ B hB φ

theorem trace_conjTranspose_mul (m n : ℕ) (u v : Fin m → Fin n → ℂ) :
    Matrix.trace ((Matrix.of u)ᴴ * Matrix.of v) = ∑ j, ∑ i, star (u i j) * v i j := by
  simp [Matrix.trace, Matrix.mul_apply, Matrix.conjTranspose_apply]

noncomputable def traceForm (m n : ℕ) (s : ℂ) :
    (Fin m → Fin n → ℂ) →ₗ[ℝ] (Fin m → Fin n → ℂ) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun u v => (s * Matrix.trace ((Matrix.of u)ᴴ * Matrix.of v)).re)
    (by
      intro a b c
      simp only [trace_conjTranspose_mul, Pi.add_apply, star_add, add_mul,
        Finset.sum_add_distrib, mul_add, Complex.add_re])
    (by
      intro r a b
      have : ∑ j, ∑ i, star ((r • a) i j) * b i j
          = (r : ℂ) * ∑ j, ∑ i, star (a i j) * b i j := by
        simp only [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
        simp [Complex.real_smul, mul_assoc]
      rw [trace_conjTranspose_mul, trace_conjTranspose_mul, this, mul_left_comm,
        Complex.re_ofReal_mul, smul_eq_mul])
    (by
      intro a b c
      simp only [trace_conjTranspose_mul, Pi.add_apply, mul_add,
        Finset.sum_add_distrib, Complex.add_re])
    (by
      intro r a b
      have : ∑ j, ∑ i, star (a i j) * (r • b) i j
          = (r : ℂ) * ∑ j, ∑ i, star (a i j) * b i j := by
        simp only [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
        simp only [Pi.smul_apply, Complex.real_smul]
        ring
      rw [trace_conjTranspose_mul, trace_conjTranspose_mul, this, mul_left_comm,
        Complex.re_ofReal_mul, smul_eq_mul])

theorem traceForm_apply (m n : ℕ) (s : ℂ) (u v : Fin m → Fin n → ℂ) :
    traceForm m n s u v = (s * Matrix.trace ((Matrix.of u)ᴴ * Matrix.of v)).re := rfl

theorem traceForm_nondegenerate (m n : ℕ) (s : ℂ) (hs : s ≠ 0) (u : Fin m → Fin n → ℂ)
    (h : ∀ v, traceForm m n s u v = 0) : u = 0 := by
  have h0 := h (fun i j => star s * u i j)
  rw [traceForm_apply, trace_conjTranspose_mul] at h0
  have h1 : s * ∑ j, ∑ i, star (u i j) * (star s * u i j)
      = ((Complex.normSq s * ∑ j, ∑ i, Complex.normSq (u i j) : ℝ) : ℂ) := by
    push_cast
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_conj_mul_self]
    simp only [Complex.star_def]
    ring
  rw [h1, Complex.ofReal_re] at h0
  have hsn : Complex.normSq s ≠ 0 := by simpa [Complex.normSq_eq_zero] using hs
  have h2 : ∑ j, ∑ i, Complex.normSq (u i j) = 0 := by
    rcases mul_eq_zero.mp h0 with h3 | h3
    · exact absurd h3 hsn
    · exact h3
  funext i j
  have h3 := (Finset.sum_eq_zero_iff_of_nonneg
    (fun j _ => Finset.sum_nonneg fun i _ => Complex.normSq_nonneg (u i j))).mp h2 j
    (Finset.mem_univ j)
  have h4 := (Finset.sum_eq_zero_iff_of_nonneg
    (fun i _ => Complex.normSq_nonneg (u i j))).mp h3 i (Finset.mem_univ i)
  simpa [Complex.normSq_eq_zero] using h4

theorem exists_schwartz_trace_transform :
    ∀ (m n : ℕ) (C s : ℂ), s ≠ 0 → ∀ φ : SchwartzMap (Fin m → Fin n → ℂ) ℂ,
      ∃ ψ : SchwartzMap (Fin m → Fin n → ℂ) ℂ, ⇑ψ = fun u => C * ∫ v : Fin m → Fin n → ℂ,
        Complex.exp (2 * Real.pi * Complex.I *
          ((s * Matrix.trace ((Matrix.of u)ᴴ * Matrix.of v)).re : ℂ)) * φ v := by
  intro m n C s hs φ
  haveI : Measure.IsAddHaarMeasure (volume : Measure (Fin n → ℂ)) :=
    Measure.pi.isAddHaarMeasure _
  haveI : Measure.IsAddHaarMeasure (volume : Measure (Fin m → Fin n → ℂ)) :=
    Measure.pi.isAddHaarMeasure _
  obtain ⟨ψ, hψ⟩ := exists_schwartz_bilinear_transform (volume : Measure (Fin m → Fin n → ℂ))
    (traceForm m n s) (traceForm_nondegenerate m n s hs) φ
  refine ⟨C • ψ, ?_⟩
  funext u
  simp only [SchwartzMap.smul_apply, hψ, smul_eq_mul, traceForm_apply]

end GlobalTheory.CompanionTheory.FourierMatrix
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ScoreTZeroEqLevelCount
section
open Finset GlobalTheory.CompanionTheory.CoefId

namespace GlobalTheory.CompanionTheory.CoefId

theorem score_tZero_level : ∀ {n : ℕ} (lev : Fin n → ℕ), Monotone lev → ∀ a : Fin n,
    score (tZero lev) a = ((univ.filter fun b => lev a < lev b).card : ℤ)
      - ((univ.filter fun b => lev b < lev a).card : ℤ) + ((a : ℕ) : ℤ) := by
  intro n lev hm a
  have hlt : ∀ b, lev a < lev b → a < b := fun b h => by
    by_contra hc
    exact absurd (hm (not_lt.mp hc)) (not_le.mpr h)
  have h1 : ((tZero lev).filter fun p => p.1 = a).card
      = (univ.filter fun b => lev a < lev b).card := by
    symm
    refine Finset.card_bij (fun b _ => (a, b)) ?_ ?_ ?_
    · intro b hb
      have hb' : lev a < lev b := (Finset.mem_filter.mp hb).2
      simp [tZero, prs, hb', hlt b hb']
    · intro b _ c _ h
      exact (Prod.ext_iff.mp h).2
    · rintro ⟨x, b⟩ hp
      simp only [tZero, prs, Finset.mem_filter, Finset.mem_univ, true_and] at hp
      obtain ⟨⟨_, h⟩, rfl⟩ := hp
      exact ⟨b, by simp [h], rfl⟩
  have h2 : (((prs n) \ tZero lev).filter fun p => p.2 = a).card
      = (univ.filter fun b => b < a ∧ lev b = lev a).card := by
    symm
    refine Finset.card_bij (fun b _ => (b, a)) ?_ ?_ ?_
    · intro b hb
      have hb' := (Finset.mem_filter.mp hb).2
      simp [tZero, prs, hb'.1, hb'.2]
    · intro b _ c _ h
      exact (Prod.ext_iff.mp h).1
    · rintro ⟨b, x⟩ hp
      simp only [tZero, prs, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and, not_and,
        not_lt] at hp
      obtain ⟨⟨h, h'⟩, rfl⟩ := hp
      exact ⟨b, by simp [h, le_antisymm (hm h.le) (h' h)], rfl⟩
  have h3 : (univ.filter fun b : Fin n => b < a).card = (a : ℕ) := by
    simpa [Finset.filter_gt_eq_Iio] using Fin.card_Iio a
  have h4 : (univ.filter fun b => lev b < lev a).card
      + (univ.filter fun b => b < a ∧ lev b = lev a).card = (a : ℕ) := by
    rw [← h3, ← Finset.card_filter_add_card_filter_not (s := univ.filter fun b : Fin n => b < a)
      (fun b => lev b < lev a)]
    congr 2
    · ext b
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro h
        refine ⟨?_, h⟩
        by_contra hc
        exact absurd (hm (not_lt.mp hc)) (not_le.mpr h)
      · exact fun h => h.2
    · ext b
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨h, h'⟩
        exact ⟨h, fun hc => absurd h' (ne_of_lt hc)⟩
      · rintro ⟨h, h'⟩
        exact ⟨h, le_antisymm (hm h.le) (not_lt.mp h')⟩
  unfold score
  rw [h1, h2]
  have h4' : ((univ.filter fun b => lev b < lev a).card : ℤ)
      + ((univ.filter fun b => b < a ∧ lev b = lev a).card : ℤ) = ((a : ℕ) : ℤ) := by
    exact_mod_cast h4
  linarith

end GlobalTheory.CompanionTheory.CoefId
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SectionLawHolds
section
noncomputable section

open PositivityTheory.RgEis

namespace GlobalTheory.CompanionTheory.RgEisSec

variable {G : Type} [Group G] [TopologicalSpace G]
  {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W]

theorem isQuotientMap_mul [IsTopologicalGroup G] {K P : Subgroup G} (hK : IsCompact (K : Set G))
    (hP : IsClosed (P : Set G)) (hI : Iwa P K) :
    Topology.IsQuotientMap (fun x : P × K => (x.1 : G) * (x.2 : G)) :=
  _root_.UpperTheory.Reformulated.B.DYhc7.main hK hP hI

theorem sec_mul {Γ K P : Subgroup G} {c : G → ℂ} {ρ : K →* (W →L[ℂ] W)} (hch : IsCh Γ P c)
    {w : W} (hw : w ∈ secSp K P c ρ) {p : G} (hp : p ∈ P) (k : K) :
    sec K P c ρ (p * k) w = c p • ρ k⁻¹ w := by
  have h : ∃ k' : K, (p * (k : G)) * (k' : G)⁻¹ ∈ P := ⟨k, by simpa using hp⟩
  rw [sec, dite_eq_left h]
  obtain ⟨k0, hk0⟩ : ∃ k0 : K, k0 = h.choose := ⟨_, rfl⟩
  have h0 : p * (k : G) * (k0 : G)⁻¹ ∈ P := hk0 ▸ h.choose_spec
  rw [← hk0]
  have hr : ((k0 * k⁻¹ : K) : G) ∈ P := by
    have : ((k0 * k⁻¹ : K) : G) = (p * (k : G) * (k0 : G)⁻¹)⁻¹ * p := by simp [mul_assoc]
    rw [this]
    exact P.mul_mem (P.inv_mem h0) hp
  have hrw : c ((k0 * k⁻¹ : K) : G) • ρ (k0 * k⁻¹) w = w := hw _ hr
  have hcp : c p = c (p * (k : G) * (k0 : G)⁻¹) * c ((k0 * k⁻¹ : K) : G) := by
    rw [← hch.mul _ h0 _ hr]
    congr 1
    simp [mul_assoc]
  have hρ : ρ k⁻¹ = ρ k0⁻¹ * ρ (k0 * k⁻¹) := by
    rw [← map_mul]
    congr 1
    simp
  calc (c (p * (k : G) * (k0 : G)⁻¹) • ρ k0⁻¹) w
      = c (p * (k : G) * (k0 : G)⁻¹) • ρ k0⁻¹ (c ((k0 * k⁻¹ : K) : G) • ρ (k0 * k⁻¹) w) := by
        rw [hrw]; rfl
    _ = c p • ρ k⁻¹ w := by
        rw [hcp, hρ, map_smul, mul_smul]; rfl

theorem sec_continuous [IsTopologicalGroup G] {Γ K P : Subgroup G} {c : G → ℂ}
    {ρ : K →* (W →L[ℂ] W)} (hK : IsCompact (K : Set G)) (hρ : Continuous ρ) (hpar : IsPar Γ K P c)
    {w : W} (hw : w ∈ secSp K P c ρ) : Continuous fun g => sec K P c ρ g w := by
  refine (isQuotientMap_mul hK hpar.closed hpar.iwa).continuous_iff.mpr ?_
  have hc : Continuous fun p : P => c p := continuousOn_iff_continuous_restrict.mp hpar.ch.cont
  have he : ((fun g => sec K P c ρ g w) ∘ fun x : P × K => (x.1 : G) * (x.2 : G))
      = fun x : P × K => c x.1 • ρ x.2⁻¹ w := by
    funext x
    exact sec_mul hpar.ch hw x.1.2 x.2
  rw [he]
  have h2 : Continuous fun k : K => ρ k⁻¹ w :=
    (hρ.comp continuous_inv).clm_apply continuous_const
  exact (hc.comp continuous_fst).smul (h2.comp continuous_snd)

theorem sec_bound {Γ K P : Subgroup G} {c : G → ℂ} {ρ : K →* (W →L[ℂ] W)}
    (hK : IsCompact (K : Set G)) (hρ : Continuous ρ) (hpar : IsPar Γ K P c) :
    ∃ M : ℝ, ∀ g (w : W), ‖sec K P c ρ g w‖ ≤ M * ‖w‖ := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  obtain ⟨M, hM⟩ := (isCompact_range hρ).isBounded.exists_norm_le
  refine ⟨M, fun g w => ?_⟩
  obtain ⟨p, hp, k, hk, rfl⟩ := hpar.iwa g
  have h : ∃ k' : K, (p * k) * (k' : G)⁻¹ ∈ P := ⟨⟨k, hk⟩, by simpa using hp⟩
  rw [sec, dite_eq_left h, ContinuousLinearMap.smul_apply, norm_smul, hpar.ch.norm _ h.choose_spec,
    one_mul]
  exact ((ρ _).le_opNorm w).trans (mul_le_mul_of_nonneg_right (hM _ ⟨_, rfl⟩) (norm_nonneg _))

theorem secLaw : SecLaw := by
  intro G _ _ _ _ _ W _ _ _ K ρ hK hρ Γ P c hpar
  exact ⟨fun w hw p hp k => sec_mul hpar.ch hw hp k,
    fun w hw => sec_continuous hK hρ hpar hw, sec_bound hK hρ hpar⟩

end GlobalTheory.CompanionTheory.RgEisSec
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SectionOverIdempotentProperties
section
open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.R

namespace GlobalTheory.CompanionTheory.SecRules

theorem secOn_zero {S : Type} [CommRing S] (Y : Scheme.{0}) (f : Y ⟶ Spec (CommRingCat.of S)) :
    SecOn f 0 := by
  haveI : Subsingleton (Localization.Away (0 : S)) :=
    IsLocalization.subsingleton (M := Submonoid.powers (0 : S)) (Submonoid.mem_powers 0)
  haveI : IsEmpty (Spec (CommRingCat.of (Localization.Away (0 : S)))) :=
    inferInstanceAs (IsEmpty (PrimeSpectrum (Localization.Away (0 : S))))
  exact ⟨isInitialOfIsEmpty.to Y, isInitialOfIsEmpty.hom_ext _ _⟩

theorem secOn_mul {S : Type} [CommRing S] {Y : Scheme.{0}} {f : Y ⟶ Spec (CommRingCat.of S)}
    (e e' : S) (h : SecOn f e) : SecOn f (e * e') := by
  obtain ⟨s, hs⟩ := h
  refine ⟨Spec.map (CommRingCat.ofHom (IsLocalization.Away.awayToAwayRight
    (S := Localization.Away e) (P := Localization.Away (e * e')) e e')) ≫ s, ?_⟩
  rw [Category.assoc, hs, ← Spec.map_comp]
  congr 1
  ext a
  simp only [CommRingCat.comp_apply, CommRingCat.hom_ofHom]
  exact IsLocalization.Away.awayToAwayRight_eq e e' a

theorem section_of_secOn_one {S : Type} [CommRing S] {Y : Scheme.{0}}
    {f : Y ⟶ Spec (CommRingCat.of S)} (h : SecOn f 1) :
    ∃ s : Spec (CommRingCat.of S) ⟶ Y, s ≫ f = 𝟙 _ := by
  obtain ⟨s, hs⟩ := h
  let eqv := IsLocalization.atUnit S (Localization.Away (1 : S)) 1 isUnit_one
  refine ⟨Spec.map (CommRingCat.ofHom (eqv.symm : Localization.Away (1 : S) →+* S)) ≫ s, ?_⟩
  rw [Category.assoc, hs, ← Spec.map_comp]
  have hid : CommRingCat.ofHom (Algebra.algebraMap S (Localization.Away (1 : S))) ≫
      CommRingCat.ofHom (eqv.symm : Localization.Away (1 : S) →+* S) = 𝟙 _ := by
    ext a
    simp only [CommRingCat.comp_apply, CommRingCat.hom_ofHom, CommRingCat.id_apply]
    exact eqv.symm.commutes a
  rw [hid, Spec.map_id]

theorem main : ∀ {S : Type} [CommRing S] (Y : Scheme.{0}) (f : Y ⟶ Spec (CommRingCat.of S)),
    SecOn f 0 ∧ (∀ e e' : S, SecOn f e → SecOn f (e * e')) ∧
      (SecOn f 1 → ∃ s : Spec (CommRingCat.of S) ⟶ Y, s ≫ f = 𝟙 _) := by
  intro S _ Y f
  exact ⟨secOn_zero Y f, fun e e' h => secOn_mul e e' h, section_of_secOn_one⟩

end GlobalTheory.CompanionTheory.SecRules
end

