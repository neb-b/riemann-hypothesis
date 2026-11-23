module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.OnlyIsotropic
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0287
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0315
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0306
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0300
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsNormEmbId
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobData
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0314
public import GroundTheory.AutomorphicForms.Bundle0023
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryMemGLs
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0310
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CrisZeroSurjective

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocVanishOf
section
noncomputable section

open Matrix MeasureTheory PositivityTheory.Rg.BcB PositivityTheory.Rg.Tf.Loc

namespace GlobalTheory.CompanionTheory.LocVan

variable {n : ℕ}

theorem locVanish_of (hN : NilChange) (hQ : QuotVanish) : LocVanish := by
  intro n _ _ μ _ f u d μd _ W₁ W₂ hf hfc hV hsep hW1 hle h12 h21 hu hub huK huT huN
  have hTw : Continuous fun x : GL (Fin n) ℂ => twConj (thC n) x d :=
    (continuous_inv.mul continuous_const).mul continuous_thC
  refine hQ n μ d μd W₁ W₂ hsep hW1 hle h12 h21 _
    (((hf.comp hTw).measurable).mul hu) (fun t ht x => ?_) (fun x k hk => ?_) ?_
  · show f (twConj (thC n) (t * x) d) * u (t * x) = f (twConj (thC n) x d) * u x
    rw [twConj_mul_left _ _ ht, huT t ht]
  · show f (twConj (thC n) (x * k) d) * u (x * k) = f (twConj (thC n) x d) * u x
    have : twConj (thC n) (x * k) d = twConj (thC n) k (twConj (thC n) x d) := by
      simp only [twConj, map_mul, _root_.mul_inv_rev, mul_assoc]
    rw [this, hV.1 k _ hk, huK x k hk]
  · intro _ _ ν _ q
    obtain ⟨Φ, hΦc, hΦ, hΦν⟩ := hN n d W₁ W₂ hsep hW1 hle h12 h21
    obtain ⟨c, hc⟩ := hΦν ν

    set g : nilrad W₁ W₂ → ℂ := fun Y => f (q⁻¹ * uOf Y * d * thC n q) with hg
    have hgc : Continuous g :=
      hf.comp (((continuous_const.mul continuous_uOf).mul continuous_const).mul continuous_const)
    have e1 : ∀ X : nilrad W₁ W₂,
        f (twConj (thC n) (uOf X * q) d) * u (uOf X * q) = u q * g (Φ X) := fun X => by
      have hm : (uOf X).val - 1 ∈ nilrad W₁ W₂ := by simpa using X.2
      rw [huN _ hm, mul_comm]
      congr 2
      simp only [hg, hΦ, twConj, map_mul, _root_.mul_inv_rev]
      group
    have e2 : ∫ X, g (Φ X) ∂ν = (c : ℝ) • ∫ Y, g Y ∂ν := by
      rw [← integral_map hΦc.measurable.aemeasurable hgc.aestronglyMeasurable, hc,
        integral_smul_measure]
      simp
    simp only [e1]
    rw [integral_const_mul, e2]
    suffices h : ∫ Y, g Y ∂ν = 0 by simp [h]

    letI : MeasurableSpace (nilrad (img q⁻¹ W₁) (img q⁻¹ W₂)) := borel _
    haveI : BorelSpace (nilrad (img q⁻¹ W₁) (img q⁻¹ W₂)) := ⟨rfl⟩
    have hcn := continuous_conjNil q W₁ W₂
    haveI : (ν.map (conjNil q W₁ W₂)).IsAddHaarMeasure :=
      (conjNil q W₁ W₂).isAddHaarMeasure_map ν hcn (continuous_conjNil_symm q W₁ W₂)
    have key := hV.2 (twConj (thC n) q d) (img q⁻¹ W₁) (img q⁻¹ W₂) (img_ne_bot _ hW1)
      (img_le_img _ hle) (by rw [perpD_twConj, h12]) (by rw [perpD_twConj, h21]) uOf
      (fun X => uOf_val X) (ν.map (conjNil q W₁ W₂))
    have hcont : Continuous fun Z : nilrad (img q⁻¹ W₁) (img q⁻¹ W₂) =>
        f (uOf Z * twConj (thC n) q d) := hf.comp (continuous_uOf.mul continuous_const)
    rw [integral_map hcn.measurable.aemeasurable hcont.aestronglyMeasurable] at key
    rw [← key]
    refine integral_congr_ae (Filter.Eventually.of_forall fun Y => ?_)
    show f _ = f _
    rw [uOf_conjNil]
    congr 1
    simp only [twConj]
    group

end GlobalTheory.CompanionTheory.LocVan
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormSqIntegralSmulLe
section
open MeasureTheory GlobalTheory.CompanionTheory.UnitaryFramesMetricPeriods
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.CompanionTheory.Godement

section Unitary

variable {Γ : Type} [Group Γ] [TopologicalSpace Γ] {B : Type} [NormedAddCommGroup B] [InnerProductSpace ℂ B]

theorem inner_map {ρ : Γ → (B →L[ℂ] B)} (hU : IsU ρ) (g : Γ) (x y : B) : ⟪ρ g x, ρ g y⟫_ℂ = ⟪x, y⟫_ℂ := by
  obtain ⟨-, -, hnorm, -⟩ := hU
  exact (LinearIsometry.mk (ρ g : B →ₗ[ℂ] B) (hnorm g)).inner_map_map x y

theorem inner_orbit {ρ : Γ → (B →L[ℂ] B)} (hU : IsU ρ) (v : B) (g h : Γ) :
    ⟪ρ g v, ρ h v⟫_ℂ = ⟪v, ρ (g⁻¹ * h) v⟫_ℂ := by
  rw [← GlobalTheory.CompanionTheory.Godement.inner_map hU g v (ρ (g⁻¹ * h) v)]
  obtain ⟨-, hmul, -, -⟩ := hU
  congr 1
  calc ρ h v = ρ (g * (g⁻¹ * h)) v := by rw [mul_inv_cancel_left]
    _ = ρ g (ρ (g⁻¹ * h) v) := by rw [hmul g (g⁻¹ * h), ContinuousLinearMap.mul_apply]

end Unitary

theorem mul_le_half_add (a b : ℝ≥0∞) : a * b ≤ 2⁻¹ * (a ^ 2 + b ^ 2) := by
  have h := ENNReal.young_inequality a b Real.HolderConjugate.two_two
  rw [ENNReal.rpow_two, ENNReal.rpow_two, ENNReal.ofReal_ofNat] at h
  calc a * b ≤ a ^ 2 / 2 + b ^ 2 / 2 := h
    _ = 2⁻¹ * (a ^ 2 + b ^ 2) := by
      rw [div_eq_mul_inv, div_eq_mul_inv, mul_comm (a ^ 2), mul_comm (b ^ 2), mul_add]

theorem norm_sq_integral_smul_le : ∀ {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [LocallyCompactSpace Γ]
    [SecondCountableTopology Γ] [MeasurableSpace Γ] [BorelSpace Γ] (ν : Measure Γ) [ν.IsHaarMeasure] [ν.IsMulRightInvariant]
    {B : Type} [NormedAddCommGroup B] [InnerProductSpace ℂ B] [CompleteSpace B] (ρ : Γ → (B →L[ℂ] B)), IsU ρ → ∀ v : B, Integrable (fun g => ⟪v, ρ g v⟫_ℂ) ν → ∀ f : Γ → ℂ, Measurable f → Integrable f ν →
    Integrable (fun g => ‖f g‖ ^ 2) ν →
    ‖∫ g, f g • ρ g v ∂ν‖ ^ 2 ≤ (∫ g, ‖f g‖ ^ 2 ∂ν) * ∫ g, ‖⟪v, ρ g v⟫_ℂ‖ ∂ν := by
  intro Γ _ _ _ _ _ _ _ ν _ _ B _ _ _ ρ hU v hφ f hf hfi hf2
  obtain ⟨-, -, -, hcont⟩ := id hU
  have hA : 0 ≤ ∫ g, ‖f g‖ ^ 2 ∂ν := integral_nonneg fun g => sq_nonneg _
  have hB : 0 ≤ ∫ g, ‖⟪v, ρ g v⟫_ℂ‖ ∂ν := integral_nonneg fun g => norm_nonneg _
  by_cases hF : Integrable (fun g => f g • ρ g v) ν
  swap
  · rw [integral_undef hF, norm_zero, zero_pow two_ne_zero]
    exact mul_nonneg hA hB
  have hψc : Continuous fun x : Γ => ‖⟪v, ρ x v⟫_ℂ‖ₑ := (continuous_const.inner (hcont v)).enorm
  have hψ : Measurable fun x : Γ => ‖⟪v, ρ x v⟫_ℂ‖ₑ := hψc.measurable
  have hfe : Measurable fun g : Γ => ‖f g‖ₑ ^ 2 := hf.enorm.pow_const 2
  have hswap : ∀ g h : Γ, ‖⟪v, ρ (h⁻¹ * g) v⟫_ℂ‖ₑ = ‖⟪v, ρ (g⁻¹ * h) v⟫_ℂ‖ₑ := by
    intro g h
    rw [← GlobalTheory.CompanionTheory.Godement.inner_orbit hU v h g, ← GlobalTheory.CompanionTheory.Godement.inner_orbit hU v g h,
      ← inner_conj_symm (ρ h v) (ρ g v), RCLike.enorm_conj]
  have hswapm : AEMeasurable (Function.uncurry fun h g : Γ =>
      2⁻¹ * (‖f g‖ₑ ^ 2 * ‖⟪v, ρ (h⁻¹ * g) v⟫_ℂ‖ₑ)) (ν.prod ν) := by
    apply Measurable.aemeasurable
    exact measurable_const.mul ((hfe.comp measurable_snd).mul
      (hψ.comp (measurable_fst.inv.mul measurable_snd)))
  have hm3 : Measurable fun h => 2⁻¹ * ‖f h‖ₑ ^ 2 * ∫⁻ x, ‖⟪v, ρ x v⟫_ℂ‖ₑ ∂ν :=
    (measurable_const.mul hfe).mul_const _
  have hm4 : Measurable fun h => 2⁻¹ * ‖f h‖ₑ ^ 2 := measurable_const.mul hfe
  have hII : ⟪∫ g, f g • ρ g v ∂ν, ∫ g, f g • ρ g v ∂ν⟫_ℂ =
      ∫ h, f h * starRingEnd ℂ (∫ g, f g * ⟪ρ h v, ρ g v⟫_ℂ ∂ν) ∂ν := by
    rw [← integral_inner hF]
    refine integral_congr_ae ?_
    filter_upwards with h
    rw [inner_smul_right, ← inner_conj_symm, ← integral_inner hF]
    simp only [inner_smul_right]
  have key : ‖⟪∫ g, f g • ρ g v ∂ν, ∫ g, f g • ρ g v ∂ν⟫_ℂ‖ₑ ≤
      (∫⁻ g, ‖f g‖ₑ ^ 2 ∂ν) * ∫⁻ x, ‖⟪v, ρ x v⟫_ℂ‖ₑ ∂ν := by
    rw [hII]
    calc ‖∫ h, f h * starRingEnd ℂ (∫ g, f g * ⟪ρ h v, ρ g v⟫_ℂ ∂ν) ∂ν‖ₑ
        ≤ ∫⁻ h, ‖f h * starRingEnd ℂ (∫ g, f g * ⟪ρ h v, ρ g v⟫_ℂ ∂ν)‖ₑ ∂ν :=
          enorm_integral_le_lintegral_enorm _
      _ ≤ ∫⁻ h, ∫⁻ g, 2⁻¹ * (‖f h‖ₑ ^ 2 + ‖f g‖ₑ ^ 2) * ‖⟪v, ρ (h⁻¹ * g) v⟫_ℂ‖ₑ ∂ν ∂ν := by
          refine lintegral_mono fun h => ?_
          beta_reduce
          rw [enorm_mul, RCLike.enorm_conj]
          calc ‖f h‖ₑ * ‖∫ g, f g * ⟪ρ h v, ρ g v⟫_ℂ ∂ν‖ₑ
              ≤ ‖f h‖ₑ * ∫⁻ g, ‖f g * ⟪ρ h v, ρ g v⟫_ℂ‖ₑ ∂ν := by
                gcongr
                exact enorm_integral_le_lintegral_enorm _
            _ ≤ ∫⁻ g, ‖f h‖ₑ * ‖f g * ⟪ρ h v, ρ g v⟫_ℂ‖ₑ ∂ν := lintegral_const_mul_le _ _
            _ ≤ _ := by
                refine lintegral_mono fun g => ?_
                beta_reduce
                rw [enorm_mul, GlobalTheory.CompanionTheory.Godement.inner_orbit hU, ← mul_assoc]
                gcongr ?_ * _
                exact GlobalTheory.CompanionTheory.Godement.mul_le_half_add _ _
      _ = ∫⁻ h, (2⁻¹ * ‖f h‖ₑ ^ 2 * ∫⁻ x, ‖⟪v, ρ x v⟫_ℂ‖ₑ ∂ν +
            ∫⁻ g, 2⁻¹ * (‖f g‖ₑ ^ 2 * ‖⟪v, ρ (h⁻¹ * g) v⟫_ℂ‖ₑ) ∂ν) ∂ν := by
          refine lintegral_congr fun h => ?_
          have hm : Measurable fun g => ‖⟪v, ρ (h⁻¹ * g) v⟫_ℂ‖ₑ := hψ.comp (measurable_const_mul h⁻¹)
          have hm2 : Measurable fun g => 2⁻¹ * ‖f h‖ₑ ^ 2 * ‖⟪v, ρ (h⁻¹ * g) v⟫_ℂ‖ₑ :=
            measurable_const.mul hm
          calc ∫⁻ g, 2⁻¹ * (‖f h‖ₑ ^ 2 + ‖f g‖ₑ ^ 2) * ‖⟪v, ρ (h⁻¹ * g) v⟫_ℂ‖ₑ ∂ν
              = ∫⁻ g, (2⁻¹ * ‖f h‖ₑ ^ 2 * ‖⟪v, ρ (h⁻¹ * g) v⟫_ℂ‖ₑ +
                  2⁻¹ * (‖f g‖ₑ ^ 2 * ‖⟪v, ρ (h⁻¹ * g) v⟫_ℂ‖ₑ)) ∂ν :=
                lintegral_congr fun g => by ring
            _ = ∫⁻ g, 2⁻¹ * ‖f h‖ₑ ^ 2 * ‖⟪v, ρ (h⁻¹ * g) v⟫_ℂ‖ₑ ∂ν +
                  ∫⁻ g, 2⁻¹ * (‖f g‖ₑ ^ 2 * ‖⟪v, ρ (h⁻¹ * g) v⟫_ℂ‖ₑ) ∂ν :=
                lintegral_add_left hm2 _
            _ = _ := by
                rw [lintegral_const_mul _ hm,
                  lintegral_mul_left_eq_self (fun x => ‖⟪v, ρ x v⟫_ℂ‖ₑ) h⁻¹]
      _ = (∫⁻ h, 2⁻¹ * ‖f h‖ₑ ^ 2 * ∫⁻ x, ‖⟪v, ρ x v⟫_ℂ‖ₑ ∂ν ∂ν) +
            ∫⁻ h, ∫⁻ g, 2⁻¹ * (‖f g‖ₑ ^ 2 * ‖⟪v, ρ (h⁻¹ * g) v⟫_ℂ‖ₑ) ∂ν ∂ν :=
          lintegral_add_left hm3 _
      _ = 2⁻¹ * (∫⁻ g, ‖f g‖ₑ ^ 2 ∂ν) * (∫⁻ x, ‖⟪v, ρ x v⟫_ℂ‖ₑ ∂ν) +
            2⁻¹ * (∫⁻ g, ‖f g‖ₑ ^ 2 ∂ν) * (∫⁻ x, ‖⟪v, ρ x v⟫_ℂ‖ₑ ∂ν) := by
          congr 1
          · rw [lintegral_mul_const _ hm4, lintegral_const_mul _ hfe]
          · rw [lintegral_lintegral_swap hswapm]
            calc ∫⁻ g, ∫⁻ h, 2⁻¹ * (‖f g‖ₑ ^ 2 * ‖⟪v, ρ (h⁻¹ * g) v⟫_ℂ‖ₑ) ∂ν ∂ν
                = ∫⁻ g, 2⁻¹ * ‖f g‖ₑ ^ 2 * ∫⁻ x, ‖⟪v, ρ x v⟫_ℂ‖ₑ ∂ν ∂ν := by
                  refine lintegral_congr fun g => ?_
                  have hm : Measurable fun h => ‖⟪v, ρ (g⁻¹ * h) v⟫_ℂ‖ₑ :=
                    hψ.comp (measurable_const_mul g⁻¹)
                  simp_rw [hswap g]
                  rw [← lintegral_mul_left_eq_self (fun x => ‖⟪v, ρ x v⟫_ℂ‖ₑ) g⁻¹,
                    ← lintegral_const_mul _ hm]
                  exact lintegral_congr fun h => by ring
              _ = _ := by
                  rw [lintegral_mul_const _ hm4, lintegral_const_mul _ hfe]
      _ = (∫⁻ g, ‖f g‖ₑ ^ 2 ∂ν) * ∫⁻ x, ‖⟪v, ρ x v⟫_ℂ‖ₑ ∂ν := by
          rw [← two_mul, ← mul_assoc, ← mul_assoc,
            ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]
  have hX : ENNReal.ofReal (∫ g, ‖f g‖ ^ 2 ∂ν) = ∫⁻ g, ‖f g‖ₑ ^ 2 ∂ν := by
    rw [ofReal_integral_eq_lintegral_ofReal hf2 (Filter.Eventually.of_forall fun g => sq_nonneg _)]
    refine lintegral_congr fun g => ?_
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]
  have hY : ENNReal.ofReal (∫ g, ‖⟪v, ρ g v⟫_ℂ‖ ∂ν) = ∫⁻ x, ‖⟪v, ρ x v⟫_ℂ‖ₑ ∂ν := by
    rw [ofReal_integral_eq_lintegral_ofReal hφ.norm (Filter.Eventually.of_forall fun g => norm_nonneg _)]
    exact lintegral_congr fun g => ofReal_norm_eq_enorm _
  have hL : ‖∫ g, f g • ρ g v ∂ν‖ ^ 2 = ‖⟪∫ g, f g • ρ g v ∂ν, ∫ g, f g • ρ g v ∂ν⟫_ℂ‖ := by
    rw [inner_self_eq_norm_sq_to_K]
    simp
  rw [hL, ← ENNReal.ofReal_le_ofReal_iff (mul_nonneg hA hB), ENNReal.ofReal_mul hA, hX, hY,
    ofReal_norm_eq_enorm]
  exact key

end GlobalTheory.CompanionTheory.Godement
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ParabolicDecompositionUpperHalfSpace
section
open scoped Matrix

namespace GlobalTheory.CompanionTheory.SiegelPoint

open Matrix PositivityTheory.Rg.Sw

variable {n : ℕ}

theorem block_relations (A B D : Matrix (Fin n) (Fin n) ℂ)
    (h : InG (fromBlocks A B 0 D : M2 n)) : Aᴴ * D = 1 ∧ Bᴴ * D = Dᴴ * B := by
  unfold InG JJ at h
  rw [fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_multiply] at h
  obtain ⟨-, h12, -, h22⟩ := fromBlocks_inj.mp h
  simp only [conjTranspose_zero, Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one, Matrix.one_mul,
    Matrix.mul_neg, Matrix.neg_mul, add_zero, zero_add, neg_zero] at h12 h22
  exact ⟨h12, (neg_add_eq_zero.mp h22).symm⟩

theorem levi_inG (a D : Matrix (Fin n) (Fin n) ℂ) (h : aᴴ * D = 1) :
    InG (fromBlocks a 0 0 D : M2 n) := by
  have h' : Dᴴ * a = 1 := by
    have h2 := congrArg conjTranspose h
    rwa [conjTranspose_mul, conjTranspose_conjTranspose, conjTranspose_one] at h2
  unfold InG JJ
  rw [fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_multiply]
  simp only [conjTranspose_zero, Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one, Matrix.one_mul,
    Matrix.mul_neg, Matrix.neg_mul, add_zero, zero_add, h, h', neg_zero]

theorem siegel_point :
    ∀ (n : ℕ) (p : PositivityTheory.Rg.Sw.GR n), (PositivityTheory.Rg.Sw.mR p).toBlocks₂₁ = 0 →
      ∃ (nb ma : PositivityTheory.Rg.Sw.GR n) (b a : Matrix (Fin n) (Fin n) ℂ), bᴴ = b ∧ IsUnit a.det ∧
        PositivityTheory.Rg.Sw.mR nb = PositivityTheory.Rg.Sw.nU b ∧ PositivityTheory.Rg.Sw.mR ma = Matrix.fromBlocks a 0 0 (aᴴ)⁻¹ ∧
        p = nb * ma ∧
        ((PositivityTheory.Rg.Sw.mR p).toBlocks₁₁ * (Complex.I • 1) + (PositivityTheory.Rg.Sw.mR p).toBlocks₁₂) *
            ((PositivityTheory.Rg.Sw.mR p).toBlocks₂₁ * (Complex.I • 1) + (PositivityTheory.Rg.Sw.mR p).toBlocks₂₂)⁻¹ =
          b + Complex.I • (a * aᴴ) := by
  intro n p hp
  set A := (mR p).toBlocks₁₁ with hA
  set B := (mR p).toBlocks₁₂ with hB
  set D := (mR p).toBlocks₂₂ with hD
  have hpm : mR p = fromBlocks A B 0 D := by
    rw [← hp]
    exact (fromBlocks_toBlocks (mR p)).symm
  have hG : InG (mR p) := p.2
  rw [hpm] at hG
  obtain ⟨h1, h2⟩ := block_relations A B D hG
  have hDA : D * Aᴴ = 1 := mul_eq_one_comm.mp h1
  have hADh : A * Dᴴ = 1 := by
    have h3 := congrArg conjTranspose hDA
    rwa [conjTranspose_mul, conjTranspose_conjTranspose, conjTranspose_one] at h3
  have hinv : (Aᴴ)⁻¹ = D := Matrix.inv_eq_right_inv h1
  have hDinv : D⁻¹ = Aᴴ := Matrix.inv_eq_right_inv hDA
  set b := B * Aᴴ with hb
  have hbh : bᴴ = b := by
    rw [hb, conjTranspose_mul, conjTranspose_conjTranspose]
    calc A * Bᴴ = A * Bᴴ * (D * Aᴴ) := by rw [hDA, Matrix.mul_one]
      _ = A * (Bᴴ * D) * Aᴴ := by simp only [Matrix.mul_assoc]
      _ = A * (Dᴴ * B) * Aᴴ := by rw [h2]
      _ = A * Dᴴ * B * Aᴴ := by simp only [Matrix.mul_assoc]
      _ = B * Aᴴ := by rw [hADh, Matrix.one_mul]
  have hnbG : InG (nU b : M2 n) := by
    unfold InG JJ nU
    rw [fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_multiply]
    simp only [conjTranspose_zero, conjTranspose_one, Matrix.mul_zero, Matrix.zero_mul,
      Matrix.mul_one, Matrix.one_mul, Matrix.mul_neg, Matrix.neg_mul, add_zero, zero_add, hbh,
      neg_add_cancel, neg_zero]
  have hdet1 : IsUnit (nU b : M2 n).det := by
    unfold nU
    rw [det_fromBlocks_zero₂₁, det_one, mul_one]
    exact isUnit_one
  have hmaG : InG (fromBlocks A 0 0 D : M2 n) := levi_inG A D h1
  have hM : (fromBlocks A 0 0 D : M2 n) * fromBlocks Dᴴ 0 0 Aᴴ = 1 := by
    rw [fromBlocks_multiply]
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, hADh, hDA, fromBlocks_one]
  have hdet2 : IsUnit (fromBlocks A 0 0 D : M2 n).det := Matrix.isUnit_det_of_right_inverse hM
  refine ⟨⟨Matrix.nonsingInvUnit _ hdet1, hnbG⟩, ⟨Matrix.nonsingInvUnit _ hdet2, hmaG⟩, b, A, hbh,
    Matrix.isUnit_det_of_right_inverse hADh, rfl, ?_, ?_, ?_⟩
  · show (fromBlocks A 0 0 D : M2 n) = fromBlocks A 0 0 (Aᴴ)⁻¹
    rw [hinv]
  · apply Subtype.ext
    apply Units.ext
    show mR p = nU b * fromBlocks A 0 0 D
    rw [hpm]
    unfold nU
    rw [fromBlocks_multiply]
    simp only [Matrix.mul_zero, Matrix.zero_mul, Matrix.one_mul, add_zero, zero_add]
    rw [hb, Matrix.mul_assoc, h1, Matrix.mul_one]
  · rw [hp, Matrix.zero_mul, zero_add, hDinv, Matrix.add_mul, Matrix.mul_smul, Matrix.mul_one,
      Matrix.smul_mul, hb, add_comm]

end GlobalTheory.CompanionTheory.SiegelPoint
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RangeIsotropicIffInvolutionMulZero
section
open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Tf.Loc PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D4 GlobalTheory.CompanionTheory.TorusCh
open scoped Pointwise

namespace GlobalTheory.CompanionTheory.TorusCh

theorem pair_range_eq {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}
    (D p : Matrix (Fin n) (Fin n) E) (a b : Fin n → E) :
    ∑ i, conjE E ((p *ᵥ a) i) * (D *ᵥ (p *ᵥ b)) i =
      (conjE E ∘ a) ⬝ᵥ (((p.map (conjE E))ᵀ * D * p) *ᵥ b) := by
  have h1 : ((p.map (conjE E))ᵀ * D * p) *ᵥ b = (p.map (conjE E))ᵀ *ᵥ (D *ᵥ (p *ᵥ b)) := by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, mul_assoc]
  rw [h1, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [RingHom.map_mulVec]

theorem iso_range_iff_sg_mul (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ)
    (d : GL (Fin n) E) (π : Matrix (Fin n) (Fin n) E) :
    LinearMap.range (Matrix.toLin' π) ≤ perpD (conjE E) d (LinearMap.range (Matrix.toLin' π)) ↔
      sg d π * π = 0 := by
  have hd1 : d.val * (d⁻¹ : GL (Fin n) E).val = 1 := Units.mul_inv d
  have hd2 : (d⁻¹ : GL (Fin n) E).val * d.val = 1 := Units.inv_mul d
  have hsg : sg d π * π = d.val * ((π.map (conjE E))ᵀ * (d⁻¹ : GL (Fin n) E).val * π) := by
    simp only [sg, mul_assoc]
  have hM : sg d π * π = 0 ↔ (π.map (conjE E))ᵀ * (d⁻¹ : GL (Fin n) E).val * π = 0 := by
    rw [hsg]
    constructor
    · intro h
      have h2 := congrArg (fun X => (d⁻¹ : GL (Fin n) E).val * X) h
      simpa [← mul_assoc, hd2] using h2
    · intro h
      rw [h, mul_zero]
  rw [hM]
  constructor
  · intro h
    ext i j
    have hv : π *ᵥ Pi.single j 1 ∈ perpD (conjE E) d (LinearMap.range (Matrix.toLin' π)) :=
      h ⟨Pi.single j 1, by rw [Matrix.toLin'_apply]⟩
    obtain ⟨y, hy, hyv⟩ := hv
    have hy' : ∀ x ∈ LinearMap.range (Matrix.toLin' π), ∑ k, conjE E (x k) * y k = 0 := hy
    have hyd : y = (d⁻¹ : GL (Fin n) E).val *ᵥ (π *ᵥ Pi.single j 1) := by
      rw [← hyv, Matrix.toLin'_apply, Matrix.mulVec_mulVec, hd2, Matrix.one_mulVec]
    have h3 := hy' (π *ᵥ Pi.single i 1) ⟨Pi.single i 1, by rw [Matrix.toLin'_apply]⟩
    rw [hyd, pair_range_eq] at h3
    have hc : (conjE E ∘ (Pi.single i 1 : Fin n → E)) = Pi.single i 1 := by
      funext k
      by_cases hk : k = i
      · subst hk; simp
      · simp [Pi.single_apply, hk]
    rw [hc, single_one_dotProduct, Matrix.mulVec_single_one] at h3
    simpa using h3
  · rintro h _ ⟨b, rfl⟩
    refine ⟨(d⁻¹ : GL (Fin n) E).val *ᵥ (π *ᵥ b), ?_, ?_⟩
    · rintro _ ⟨a, rfl⟩
      simp only [Matrix.toLin'_apply]
      rw [pair_range_eq, h, Matrix.zero_mulVec, dotProduct_zero]
    · rw [Matrix.toLin'_apply, Matrix.toLin'_apply, Matrix.mulVec_mulVec, hd1, Matrix.one_mulVec]

end GlobalTheory.CompanionTheory.TorusCh
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RightDerivativeCalculusHolds
section
noncomputable section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate

namespace GlobalTheory.CompanionTheory.RCalc

open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem rcalc : RCalc := by
  intro n
  refine ⟨?_, ?_, ?_⟩
  · intro V _ _ f hf
    exact ⟨fun X => Rd_contDiffOn X hf, fun X Y g hg => Rd_bracket X Y hf hg, fun s m X g hg => Rd_gel X s m hf hg,
      fun s m x hx g hg => ⟨gel_left s m hx hf hg, gel_right s m hx hf hg⟩⟩
  · intro E f hf s m
    exact gel_mem_CE E hf s m
  · intro _ _ μ _ V _ _ _ f hf hc X
    exact ibp n μ V f hf hc X

end GlobalTheory.CompanionTheory.RCalc
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothModelTensorWittComparison
section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open CategoryTheory AlgebraicGeometry TensorProduct GroundTheory.PAdicHodge GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.Pb

noncomputable section
namespace GlobalTheory.CompanionTheory.BcAcris

theorem pull_comm {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (r : Res l K) (M : Model l K) (j n : ℕ)
    (Q' : ObjectProperty (Thick (nlFun (B.DD true (base l) n) l M.X M.p (Mid.κm r n)))) (a : AW r)
    (y : (Wc.HS l (B.schFn M.p) r.ρ j).M n) :
    (toQ Q' ((base l).cris n)).pull j (idA r a • bWL r M n j y) =
      (base l).cris n a • (toQ Q' ((base l).cris n)).pull j
        ((B.omMor ((nm r M n).mor l) r.w (Mid.wn_mk r n)).pull j y) := by
  have e : bWL r M n j y = (B.omMor ((nm r M n).mor l) r.w (Mid.wn_mk r n)).pull j y :=
    congrArg (fun t => CH.Mor.pull t j y) (bWMorL_eq r M n)
  exact (congrArg (fun v => (toQ Q' ((base l).cris n)).pull j (idA r a • v)) e).trans
    (LinearMap.map_smulₛₗ ((toQ Q' ((base l).cris n)).pull j) (idA r a) _)


set_option maxHeartbeats 12000000 in
theorem bc_tens : ∀ {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (r : Res l K) (M : Model l K), M.Sm → ∀ j n,
    Tens (WittVector l r.k) (N := fun _ : Unit => AW r) (M := fun _ => (Wc.HS l (B.schFn M.p) r.ρ j).M n)
      (M' := Mid.HM r M n j) fun _ a y => idA r a • bWL r M n j y := by
  intro l _ K r M hM j n
  letI := (Mid.wn r n).toAlgebra
  haveI : Module.Flat (Wc.Wm l r.k n) ((base l).Acr n) := GlobalTheory.T.flat_acris_truncated_witt r n
  obtain ⟨U⟩ := cov_of_sm M hM
  let m := nm r M n
  let Q : ObjectProperty (Thick (nlFun (Wc.pd l r.k n) l M.X M.p ((Wc.res l r.k n).comp r.ρ))) := St ⊤ {⊤}
  let Q' : ObjectProperty (Thick (nlFun (B.DD true (base l) n) l M.X M.p (Mid.κm r n))) := St ⊤ {⊤}
  have hQ : ∀ T, Q T := st_all
  have hQ' : ∀ T, Q' T := st_all
  have h : ∀ T, Q' T → Q ((m.mor l).functor.obj T) := fun T _ => hQ _
  have ha : ∀ a, (m.smor Q Q' h).LeC a (oT Q) (oT Q') := fun a => GlobalTheory.CompanionTheory.BcCov.leC_top _ a _ _ (oT_top Q')
  have hb : ∀ a, (m.smor Q Q' h).LeC a (oB Q) (oB Q') := fun a => GlobalTheory.CompanionTheory.BcCov.leC_bot _ a _ _ fun T => oB_bot Q _
  have T := GlobalTheory.T.nilpotent_identity_morphism_compat (Fact.out : l.Prime).ne_zero (l_nil r n) m rfl rfl U Q Q' rfl rfl h ha hb j
  refine tens_change (A := AW r) (Ideal.Quotient.mk _) ((base l).cris n) (cris_surjective n) (fun w => rfl)
    Ideal.Quotient.mk_surjective ((l : WittVector l r.k) ^ n)
    (Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _)) ?_
    ((toQ Q (Ideal.Quotient.mk _)).pull j) (toQ_pull_bijective Q _ hQ j)
    ((toQ Q' ((base l).cris n)).pull j).toAddMonoidHom (toQ_pull_bijective Q' _ hQ' j)
    _ _ ?_ T
  · intro a h0
    obtain ⟨b, hb'⟩ := cris_ker n a h0
    refine ⟨b, hb'.trans ?_⟩
    change _ = r.w _ * b
    rw [map_pow, map_natCast]
  · intro a y
    have key := sqC_toQ m Q Q' h (Ideal.Quotient.mk _) ((base l).cris n) r.w (Mid.wn_mk r n) ((base l).cris n a)
      (ha _) (hb _) j y
    exact (pull_comm r M j n Q' a y).trans key.symm

end GlobalTheory.CompanionTheory.BcAcris
end
end

