module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0277
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.HaarUpqIsMulRightInvariant
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0086
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0082
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0084
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0080
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0083
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0079
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaTaylorCoeffsAlgebraicAtComplexMultiplicatio
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Formalism.PairingDivisors.StatementH

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsInvInvariantOfRight
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU GlobalTheory.IndefiniteRowSideFullHecke.CartanCoshPower Matrix MeasureTheory

noncomputable section
namespace GlobalTheory.CartanInt

variable {p q : ℕ}

theorem isInvInvariant_of_right {G : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G)
    [μ.IsHaarMeasure] [μ.IsMulRightInvariant] : μ.IsInvInvariant := by
  constructor
  let c : ENNReal := Measure.haarScalarFactor μ.inv μ
  have hc : μ.inv = c • μ := Measure.isMulLeftInvariant_eq_smul μ.inv μ
  have h1 : Measure.map Inv.inv (Measure.map Inv.inv μ) = c ^ 2 • μ := by
    rw [← Measure.inv_def μ, hc, Measure.map_smul c continuous_inv.measurable.aemeasurable, ← Measure.inv_def μ, hc, smul_smul, pow_two]
  have μeq : μ = c ^ 2 • μ := by
    rw [Measure.map_map continuous_inv.measurable continuous_inv.measurable] at h1
    simpa only [inv_involutive, Function.Involutive.comp_self, Measure.map_id] using h1
  have K : TopologicalSpace.PositiveCompacts G := Classical.arbitrary _
  have h2 : c ^ 2 * μ K = 1 ^ 2 * μ K := by
    conv_rhs => rw [μeq]
    simp
  have h3 : c ^ 2 = 1 ^ 2 :=
    (ENNReal.mul_left_inj (Measure.measure_pos_of_nonempty_interior _ K.interior_nonempty).ne'
          K.isCompact.measure_lt_top.ne).1 h2
  have h4 : c = 1 := (ENNReal.pow_right_strictMono two_ne_zero).injective h3
  rw [hc, h4, one_smul]

theorem isUnit_mat (g : UpqT p q) : IsUnit (UpqT.mat g) := Units.isUnit _

theorem isCompact_Kc : IsCompact (Kc p q) := by
  have h : Kc p q = ⋂ a, ⋂ b, ⋂ (_ : ¬ sameBlock a b), {x : UpqT p q | UpqT.mat x a b = 0} := by
    ext x
    simp only [Set.mem_iInter, Set.mem_ofPred_eq]
    exact Iff.rfl
  have hcl : IsClosed (Kc p q) := by
    rw [h]
    refine isClosed_iInter fun a => isClosed_iInter fun b => isClosed_iInter fun _ => ?_
    exact isClosed_eq (GlobalTheory.UpqTopology.continuous_mat.matrix_elem a b) continuous_const
  have hc : IsCompact (Set.univ.pi fun _ : Ix p q => Set.univ.pi fun _ : Ix p q => Metric.closedBall (0 : ℂ) 1) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall 0 1
  refine (GlobalTheory.UpqTopology.isClosedEmbedding_mat.isCompact_preimage (K := _) hc).of_isClosed_subset hcl ?_
  intro x hx a _ b _
  simpa using entry_norm_bound_of_unitary (Matrix.mem_unitaryGroup_iff'.2 (star_mul_of_mem_Kc hx)) a b

theorem exists_action (L : Mat p q → (Fin p → Fin q → ℂ)) (hL : ContinuousOn L {g | IsUnit g})
    (hLk : ∀ (k : Mat p q) (B : Fin p → Fin q → ℂ), kᴴ * k = 1 → L (k * NormedSpace.exp (pY B)) = B)
    (g : UpqT p q) : ∃ ψ : (Fin p → Fin q → ℂ) → (Fin p → Fin q → ℂ), Continuous ψ ∧ Function.Bijective ψ ∧
      ∀ B, ∃ κ ∈ Kc p q, eP B * g = κ * eP (ψ B) := by
  obtain ⟨i1, -⟩ := GlobalTheory.UpqTopology.upq_lcsc p q
  let ψ : UpqT p q → (Fin p → Fin q → ℂ) → (Fin p → Fin q → ℂ) := fun g B => L (UpqT.mat (eP B * g))
  have key : ∀ (x κ : UpqT p q) (B' : Fin p → Fin q → ℂ), κ ∈ Kc p q → x = κ * eP B' →
      L (UpqT.mat x) = B' := by
    intro x κ B' hκ hx
    rw [hx, mat_mul, mat_eP]
    exact hLk _ _ (star_mul_of_mem_Kc hκ)
  have dec : ∀ g B, ∃ κ ∈ Kc p q, eP B * g = κ * eP (ψ g B) := by
    intro g B
    obtain ⟨κ, hκ, B', h⟩ := exists_cartan (eP B * g)
    have : ψ g B = B' := key _ κ B' hκ h
    exact ⟨κ, hκ, by rw [this]; exact h⟩
  have inv : ∀ g B, ψ g⁻¹ (ψ g B) = B := by
    intro g B
    obtain ⟨κ, hκ, h⟩ := dec g B
    refine key _ κ⁻¹ B ((Ksg p q).inv_mem hκ) ?_
    rw [eq_inv_mul_iff_mul_eq, ← mul_assoc, ← h, mul_inv_cancel_right]
  refine ⟨ψ g, ?_, ?_, dec g⟩
  · exact hL.comp_continuous
      (GlobalTheory.UpqTopology.continuous_mat.comp (continuous_eP.mul continuous_const)) fun B => isUnit_mat _
  · refine Function.bijective_iff_has_inverse.2 ⟨ψ g⁻¹, inv g, fun B => ?_⟩
    have := inv g⁻¹ B
    rwa [inv_inv] at this

theorem haar_polar : ∀ (p q : ℕ) (m : Measure (UpqT p q)), m.IsHaarMeasure → ∃ (c : ℝ) (mK : Measure (UpqT p q)), 0 < c ∧ IsProbabilityMeasure mK ∧ mK (Kc p q)ᶜ = 0 ∧ (∀ k ∈ Kc p q, Measure.map (fun x => k * x) mK = mK) ∧ ∀ f : UpqT p q → ENNReal, Measurable f → ∫⁻ g, f g ∂m = ENNReal.ofReal c * ∫⁻ B : Fin p → Fin q → ℂ, (∫⁻ k, f (k * eP B) ∂mK) * ENNReal.ofReal (polJ (pY B)) := by
  intro p q m hm
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := GlobalTheory.UpqTopology.upq_lcsc p q
  haveI := GlobalTheory.UpqUnimodular.isMulRightInvariant_of_isHaarMeasure p q m hm
  haveI := isInvInvariant_of_right m
  obtain ⟨mK, hprob, hK0, hleft, hright⟩ :=
    GlobalTheory.exists_biinvariant_probability_on_compact_subgroup (UpqT p q) (Ksg p q) isCompact_Kc
  obtain ⟨L, hLc, hL⟩ := GlobalTheory.PolarLogCont.exists_continuousOn_polar_log p q
  have hpos : ∀ B : Fin p → Fin q → ℂ, 0 < polJ (pY B) := fun B => one_pos.trans_le (one_le_polJ _)
  have hJc : Continuous fun B : Fin p → Fin q → ℂ => polJ (pY B) := (continuous_polJ p q).comp continuous_pY
  have hJm : Measurable fun B : Fin p → Fin q → ℂ => ENNReal.ofReal (polJ (pY B)) :=
    ENNReal.measurable_ofReal.comp hJc.measurable
  have hdet : ∀ B : Fin p → Fin q → ℂ, LinearMap.det (sP (pY B)) = polJ (pY B) :=
    fun B => det_sinhc_eq_polarJacobian p q _ (SinhcPres.sAd_pY p q B)
  have hem : Measurable (eP : (Fin p → Fin q → ℂ) → UpqT p q) := continuous_eP.measurable
  haveI : IsLocallyFiniteMeasure
      ((volume : Measure (Fin p → Fin q → ℂ)).withDensity fun B => ENNReal.ofReal (polJ (pY B))) :=
    IsLocallyFiniteMeasure.withDensity_ofReal hJc
  obtain ⟨c, hc, hf⟩ := GlobalTheory.Twist.lintegral_haar_eq_transversal (UpqT p q) (Fin p → Fin q → ℂ) m mK
    (volume.withDensity fun B => ENNReal.ofReal (polJ (pY B))) (Kc p q) eP hem hK0 hright
    (by
      intro h0
      rw [withDensity_eq_zero_iff hJm.aemeasurable] at h0
      haveI : (volume : Measure (Fin q → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
      haveI : (volume : Measure (Fin p → Fin q → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
      haveI : (ae (volume : Measure (Fin p → Fin q → ℂ))).NeBot :=
        ae_neBot.2 fun h => (isOpen_univ.measure_ne_zero (volume : Measure (Fin p → Fin q → ℂ))
          Set.univ_nonempty) (by rw [h]; rfl)
      obtain ⟨B, hB⟩ := h0.exists
      exact absurd hB (by simpa using hpos B))
    (by
      intro C hC
      have hcomp : IsCompact (L '' (UpqT.mat '' C)) :=
        (hC.image GlobalTheory.UpqTopology.continuous_mat).image_of_continuousOn (hLc.mono (by
          rintro _ ⟨x, -, rfl⟩; exact isUnit_mat x))
      refine lt_of_le_of_lt (measure_mono ?_) hcomp.measure_lt_top
      rintro B ⟨k, hk, hB⟩
      refine ⟨_, ⟨_, hB, rfl⟩, ?_⟩
      rw [mat_mul, mat_eP]
      exact hL _ B (star_mul_of_mem_Kc hk))
    (by
      intro g
      obtain ⟨ψ, hψc, hψb, hψ⟩ := exists_action L hLc hL g
      refine ⟨ψ, hψc.measurable, GlobalTheory.map_withDensity_of_jacobian p q _ ψ hJc hψc hψb ?_, hψ⟩
      have := jacobian_action_p p q (UpqT.mat g) ψ hψc (fun B => by
          obtain ⟨κ, hκ, h⟩ := hψ B
          obtain ⟨U, hU, V, hV, hm⟩ := (mem_Kc_iff κ).1 hκ
          refine ⟨U, hU, V, hV, ?_⟩
          have := congrArg UpqT.mat h
          rwa [mat_mul, mat_mul, mat_eP, mat_eP, hm] at this)
        (fun B => by rw [hdet]; exact hpos B) (SinhcPres.sAd_pY p q)
        (fun B => hasStrictFDerivAt_exp_two_pY p q B (hasDerivAt_exp_two_add_smul p q (pY B)))
      simpa only [hdet] using this)
  refine ⟨c, mK, hc, hprob, hK0, hleft, fun f hfm => ?_⟩
  rw [hf f hfm, lintegral_withDensity_eq_lintegral_mul _ hJm]
  · congr 1
    refine lintegral_congr fun B => ?_
    simp only [Pi.mul_apply, mul_comm]
  · exact Measurable.lintegral_prod_right' (f := fun z : (Fin p → Fin q → ℂ) × UpqT p q => f (z.2 * eP z.1))
      (hfm.comp (measurable_snd.mul (hem.comp measurable_fst)))

end GlobalTheory.CartanInt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.LamBallULe
section
noncomputable section
namespace GlobalTheory.CartanInt.LamBall
open Formalism.BasicNotions Matrix MeasureTheory

theorem pow_self_le_factorial_sq (n : ℕ) : n ^ n ≤ n.factorial ^ 2 := by
  have h1 : ∏ k ∈ Finset.range n, (k + 1) = n.factorial := Finset.prod_range_add_one_eq_factorial n
  have h2 : ∏ k ∈ Finset.range n, (n - k) = n.factorial := by
    calc ∏ k ∈ Finset.range n, (n - k) = ∏ k ∈ Finset.range n, ((n - 1 - k) + 1) :=
          Finset.prod_congr rfl fun k hk => by have := Finset.mem_range.1 hk; omega
      _ = ∏ k ∈ Finset.range n, (k + 1) := Finset.prod_range_reflect (fun k => k + 1) n
      _ = n.factorial := h1
  calc n ^ n = ∏ _k ∈ Finset.range n, n := by rw [Finset.prod_const, Finset.card_range]
    _ ≤ ∏ k ∈ Finset.range n, ((k + 1) * (n - k)) := by
        apply Finset.prod_le_prod'
        intro k hk
        have hk := Finset.mem_range.1 hk
        obtain ⟨m, hm⟩ : ∃ m, n - k = m + 1 := ⟨n - k - 1, by omega⟩
        have hn : n = k + m + 1 := by omega
        rw [hm, hn]
        nlinarith
    _ = n.factorial ^ 2 := by rw [Finset.prod_mul_distrib, h1, h2, sq]

theorem two_mul_pow_le_factorial (N : ℕ) : (2 * N) ^ N ≤ (2 * N).factorial := by
  have h := pow_self_le_factorial_sq (2 * N)
  rw [pow_mul'] at h
  exact (Nat.pow_le_pow_iff_left two_ne_zero).1 h

theorem volume_l1_ball_le {ι : Type} [Fintype ι] (a : ℕ) (ha : Fintype.card ι = a ^ 2) (r : ℝ)
    (hr : 0 < r) : (volume : Measure (ι → ℂ)) {z | ∑ i, ‖z i‖ < 2 * r} ≤
      ENNReal.ofReal ((18 / 5 * r / (a : ℝ)) ^ (a ^ 2)) ^ 2 := by
  classical
  rcases Nat.eq_zero_or_pos a with rfl | ha0
  · have : IsEmpty ι := Fintype.card_eq_zero_iff.1 (by simpa using ha)
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, pow_zero,
      ENNReal.ofReal_one, one_pow]
    rw [MeasureTheory.volume_pi, Measure.pi_of_empty]
    exact prob_le_one
  · have hnpos : (0 : ℝ) < Fintype.card ι := by rw [ha]; push_cast; positivity
    have : Nonempty ι := Fintype.card_pos_iff.1 (by rw [ha]; positivity)
    have hset : {z : ι → ℂ | ∑ i, ‖z i‖ < 2 * r} =
        {z | (∑ i, ‖z i‖ ^ (1 : ℝ)) ^ (1 / (1 : ℝ)) < 2 * r} := by
      simp only [Real.rpow_one, div_one]
    have hG3 : Real.Gamma (2 / 1 + 1) = 2 := by
      have := Real.Gamma_nat_eq_factorial 2
      norm_num at this ⊢
    have hGn : Real.Gamma (2 * (Fintype.card ι : ℝ) / 1 + 1) = ((2 * Fintype.card ι).factorial : ℝ) := by
      rw [div_one, ← Real.Gamma_nat_eq_factorial]
      push_cast
      ring_nf
    rw [hset, Complex.volume_sum_rpow_lt ι le_rfl, hG3, hGn, ← ha,
      ← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_pow (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    set n := Fintype.card ι with hn
    have hfac : ((2 : ℝ) * n) ^ n ≤ ((2 * n).factorial : ℝ) := by
      exact_mod_cast two_mul_pow_le_factorial n
    have han : (a : ℝ) ^ 2 = n := by exact_mod_cast ha.symm
    calc (2 * r) ^ (2 * n) * ((Real.pi * 2) ^ n / ((2 * n).factorial : ℝ))
        = (8 * Real.pi * r ^ 2) ^ n / ((2 * n).factorial : ℝ) := by
          rw [pow_mul, ← mul_div_assoc, ← mul_pow]
          congr 2
          ring
      _ ≤ (8 * Real.pi * r ^ 2) ^ n / ((2 : ℝ) * n) ^ n :=
          div_le_div_of_nonneg_left (by positivity) (pow_pos (by positivity) n) hfac
      _ = (4 * Real.pi * r ^ 2 / n) ^ n := by
          rw [← div_pow]
          congr 1
          field_simp
          ring
      _ ≤ (324 / 25 * r ^ 2 / n) ^ n := by
          apply pow_le_pow_left₀ (by positivity)
          gcongr
          linarith [Real.pi_lt_d2]
      _ = ((18 / 5 * r / a) ^ 2) ^ n := by
          congr 1
          rw [div_pow, han]
          ring
      _ = ((18 / 5 * r / a) ^ n) ^ 2 := by rw [← pow_mul, ← pow_mul, Nat.mul_comm]

theorem lam_ballU_le (p q : ℕ) (lam : Measure (lieU p q)) (h : IsOmegaLeb lam) (r : ℝ) (hr : 0 < r) :
    lam (ballU p q r) ≤ ENNReal.ofReal ((18 / 5 * r / ((p + q : ℕ) : ℝ)) ^ ((p + q) ^ 2)) := by
  classical
  obtain ⟨hHaar, hmap⟩ := h
  have : BorelSpace (lieU p q) := ⟨rfl⟩
  have hcont : Continuous fun X : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ =>
      Xᴴ * Formalism.UG.Jpq p q + Formalism.UG.Jpq p q * X :=
    (continuous_id.matrix_conjTranspose.matrix_mul continuous_const).add
      (continuous_const.matrix_mul continuous_id)
  have hcl : IsClosed (lieU p q : Set (Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ)) :=
    isClosed_eq hcont continuous_const
  have : LocallyCompactSpace (Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) :=
    inferInstanceAs (LocallyCompactSpace (Fin p ⊕ Fin q → Fin p ⊕ Fin q → ℂ))
  have : SecondCountableTopology (Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) :=
    inferInstanceAs (SecondCountableTopology (Fin p ⊕ Fin q → Fin p ⊕ Fin q → ℂ))
  have : LocallyCompactSpace (lieU p q) := hcl.isClosedEmbedding_subtypeVal.locallyCompactSpace
  have : SecondCountableTopology (lieU p q) :=
    hcl.isClosedEmbedding_subtypeVal.isEmbedding.secondCountableTopology
  have : OpensMeasurableSpace (lieU p q × lieU p q) := inferInstance
  have : IsLocallyFiniteMeasure lam := inferInstance
  have : SigmaFinite lam := inferInstance
  have hc : Continuous fun ab : lieU p q × lieU p q =>
      (ab.1 : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) +
        Complex.I • (ab.2 : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) :=
    have h1 : Continuous fun ab : lieU p q × lieU p q =>
        (ab.1 : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) := continuous_subtype_val.comp continuous_fst
    have h2 : Continuous fun ab : lieU p q × lieU p q =>
        (ab.2 : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) := continuous_subtype_val.comp continuous_snd
    h1.add (h2.const_smul Complex.I)
  have hΦ : Measurable fun ab : lieU p q × lieU p q =>
      Formalism.BasicNotions.entries ((ab.1 : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) +
        Complex.I • (ab.2 : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ)) :=
    (continuous_pi fun ij : (Fin p ⊕ Fin q) × (Fin p ⊕ Fin q) => hc.matrix_elem ij.1 ij.2).measurable
  have hS : MeasurableSet {z : (Fin p ⊕ Fin q) × (Fin p ⊕ Fin q) → ℂ | ∑ i, ‖z i‖ < 2 * r} :=
    (isOpen_lt (continuous_finsetSum _ fun i _ => (continuous_apply i).norm)
      continuous_const).measurableSet
  have hsub : ballU p q r ×ˢ ballU p q r ⊆ (fun ab : lieU p q × lieU p q =>
      Formalism.BasicNotions.entries ((ab.1 : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) +
        Complex.I • (ab.2 : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ))) ⁻¹'
      {z | ∑ i, ‖z i‖ < 2 * r} := by
    rintro ⟨X, Y⟩ ⟨hX, hY⟩
    simp only [ballU, Set.mem_ofPred_eq] at hX hY
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, Formalism.BasicNotions.entries, Fintype.sum_prod_type]
    calc ∑ i, ∑ j, ‖((X : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) +
          Complex.I • (Y : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ)) i j‖
        ≤ ∑ i, ∑ j, (‖(X : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) i j‖ +
          ‖(Y : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) i j‖) := by
          refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
          rw [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
          calc _ ≤ _ := norm_add_le _ _
            _ = _ := by rw [norm_mul, Complex.norm_I, one_mul]
      _ = (∑ i, ∑ j, ‖(X : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) i j‖) +
          ∑ i, ∑ j, ‖(Y : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) i j‖ := by
          simp only [Finset.sum_add_distrib]
      _ < r + r := add_lt_add hX hY
      _ = 2 * r := by ring
  have hvol := volume_l1_ball_le (ι := (Fin p ⊕ Fin q) × (Fin p ⊕ Fin q)) (p + q)
    (by simp [Fintype.card_prod, Fintype.card_sum, sq]) r hr
  have key : lam (ballU p q r) ^ 2 ≤
      ENNReal.ofReal ((18 / 5 * r / ((p + q : ℕ) : ℝ)) ^ ((p + q) ^ 2)) ^ 2 := by
    calc lam (ballU p q r) ^ 2 = (lam.prod lam) (ballU p q r ×ˢ ballU p q r) := by
          rw [Measure.prod_prod, sq]
      _ ≤ (lam.prod lam) ((fun ab : lieU p q × lieU p q =>
            Formalism.BasicNotions.entries ((ab.1 : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) +
              Complex.I • (ab.2 : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ))) ⁻¹'
            {z | ∑ i, ‖z i‖ < 2 * r}) := measure_mono hsub
      _ = ((lam.prod lam).map (fun ab : lieU p q × lieU p q =>
            Formalism.BasicNotions.entries ((ab.1 : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) +
              Complex.I • (ab.2 : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ))))
            {z | ∑ i, ‖z i‖ < 2 * r} := (Measure.map_apply hΦ hS).symm
      _ = volume {z : (Fin p ⊕ Fin q) × (Fin p ⊕ Fin q) → ℂ | ∑ i, ‖z i‖ < 2 * r} := by
          rw [hmap]
      _ ≤ _ := hvol
  exact (ENNReal.pow_le_pow_left_iff two_ne_zero).1 key

end GlobalTheory.CartanInt.LamBall
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.MeasurableCoshPow
section
noncomputable section
namespace GlobalTheory.CoshPowMeas
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU GlobalTheory.IndefiniteRowSideFullHecke.CartanCoshPower GlobalTheory.CartanInt Matrix MeasureTheory
open Filter Topology

variable {p q : ℕ}

theorem continuous_cartanB : Continuous (cartanB : UpqT p q → Matrix (Fin p) (Fin q) ℂ) := by
  have h : Continuous fun g : UpqT p q => GlobalTheory.PolarLogCont.halfLog (UpqT.mat g) :=
    GlobalTheory.PolarLogCont.continuousOn_halfLog.comp_continuous GlobalTheory.UpqTopology.continuous_mat
      fun g => Units.isUnit (show Formalism.UG.Upq p q from g).1
  have hc : Continuous fun M : Mat p q => M.toBlocks₁₂ := by
    refine continuous_matrix fun i j => ?_
    exact continuous_id.matrix_elem (Sum.inl i) (Sum.inr j)
  exact hc.comp h

def sPad (B : Matrix (Fin p) (Fin q) ℂ) (j : Fin q) : ℝ := if (j : ℕ) < p then singVal B j else 0

theorem exists_gram (B : Matrix (Fin p) (Fin q) ℂ) : ∃ V : Matrix (Fin q) (Fin q) ℂ, Vᴴ * V = 1 ∧
    Bᴴ * B = V * Matrix.diagonal (fun j => ((sPad B j : ℝ) : ℂ) ^ 2) * Vᴴ := by
  obtain ⟨U, hU, V, hV, hB⟩ := GlobalTheory.RectSVD.exists_svd_singularValues p q B
  have h1 : Uᴴ * U = 1 := Matrix.mem_unitaryGroup_iff'.mp hU
  have h2 : Vᴴ * V = 1 := Matrix.mem_unitaryGroup_iff'.mp hV
  refine ⟨V, h2, ?_⟩
  set D : Matrix (Fin p) (Fin q) ℂ := Matrix.of fun (i : Fin p) (j : Fin q) =>
        if (i : ℕ) = (j : ℕ) then (((Matrix.toEuclideanLin B).singularValues i : ℝ) : ℂ) else 0 with hD
  have hDD : Dᴴ * D = Matrix.diagonal (fun j => ((sPad B j : ℝ) : ℂ) ^ 2) := by
    ext j j'
    rw [Matrix.mul_apply]
    by_cases hj : (j : ℕ) < p
    · rw [Finset.sum_eq_single (⟨j, hj⟩ : Fin p)]
      · by_cases hjj : j = j'
        · subst hjj
          simp [hD, sPad, hj, singVal, sq]
        · have : (j : ℕ) ≠ j' := fun h => hjj (Fin.ext h)
          simp [hD, hjj, this]
      · intro i _ hi
        have : (i : ℕ) ≠ j := fun h => hi (Fin.ext h)
        simp [hD, this]
      · simp
    · rw [Finset.sum_eq_zero]
      · by_cases hjj : j = j'
        · subst hjj
          simp [sPad, hj]
        · simp [hjj]
      · intro i _
        have : (i : ℕ) ≠ j := fun h => hj (h ▸ i.isLt)
        simp [hD, this]
  rw [← hDD]
  conv_lhs => rw [hB]
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc Uᴴ U, h1, Matrix.one_mul]

theorem conj_pow {n : Type} [Fintype n] [DecidableEq n] (V A : Matrix n n ℂ) (h : Vᴴ * V = 1) (k : ℕ) :
    (V * A * Vᴴ) ^ k = V * A ^ k * Vᴴ := by
  induction k with
  | zero => simp [mul_eq_one_comm.1 h]
  | succ k ih =>
    rw [pow_succ, ih, pow_succ]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Vᴴ V, h, Matrix.one_mul]

def coshSum (n : ℕ) (B : Matrix (Fin p) (Fin q) ℂ) : Matrix (Fin q) (Fin q) ℂ :=
  ∑ k ∈ Finset.range n, (((2 * k).factorial : ℕ) : ℂ)⁻¹ • (Bᴴ * B) ^ k

theorem continuous_coshSum (n : ℕ) : Continuous (coshSum n : Matrix (Fin p) (Fin q) ℂ → _) := by
  unfold coshSum
  refine continuous_finsetSum _ fun k _ => ?_
  have h : Continuous fun B : Matrix (Fin p) (Fin q) ℂ => Bᴴ * B :=
    continuous_id.matrix_conjTranspose.matrix_mul continuous_id
  exact (h.pow k).const_smul ((((2 * k).factorial : ℕ) : ℂ)⁻¹)

theorem det_coshSum (n : ℕ) (B : Matrix (Fin p) (Fin q) ℂ) : (coshSum n B).det.re =
    ∏ j : Fin q, ∑ k ∈ Finset.range n, sPad B j ^ (2 * k) / ((2 * k).factorial : ℕ) := by
  obtain ⟨V, hV, h⟩ := exists_gram B
  have e : coshSum n B = V * Matrix.diagonal (fun j => ((∑ k ∈ Finset.range n,
      sPad B j ^ (2 * k) / ((2 * k).factorial : ℕ) : ℝ) : ℂ)) * Vᴴ := by
    have e1 : Matrix.diagonal (fun j => ((∑ k ∈ Finset.range n,
      sPad B j ^ (2 * k) / ((2 * k).factorial : ℕ) : ℝ) : ℂ)) = ∑ k ∈ Finset.range n,
        (((2 * k).factorial : ℕ) : ℂ)⁻¹ • (Matrix.diagonal (fun j => ((sPad B j : ℝ) : ℂ) ^ 2)) ^ k := by
      ext i j
      simp only [Matrix.diagonal_pow, Matrix.sum_apply, Matrix.smul_apply, Matrix.diagonal_apply]
      split_ifs
      · push_cast
        refine Finset.sum_congr rfl fun k _ => ?_
        simp [pow_mul, div_eq_inv_mul]
      · simp
    rw [e1, coshSum, h, Matrix.mul_sum, Matrix.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [conj_pow _ _ hV, Matrix.mul_smul, Matrix.smul_mul]
  rw [e, Matrix.det_mul_comm, ← Matrix.mul_assoc, hV, Matrix.one_mul, Matrix.det_diagonal,
    ← Complex.ofReal_prod, Complex.ofReal_re]

theorem prod_cosh_sPad (B : Matrix (Fin p) (Fin q) ℂ) :
    ∏ j : Fin q, Real.cosh (sPad B j) = ∏ i ∈ Finset.range (min p q), Real.cosh (singVal B i) := by
  unfold sPad
  rw [Fin.prod_univ_eq_prod_range (fun j => Real.cosh (if j < p then singVal B j else 0)) q]
  symm
  refine Finset.prod_subset_one_on_sdiff (Finset.range_subset_range.2 (min_le_right p q)) ?_ ?_
  · intro x hx
    have : ¬ x < p := by
      simp only [Finset.mem_sdiff, Finset.mem_range] at hx; omega
    simp [this]
  · intro x hx
    have : x < p := by
      simp only [Finset.mem_range] at hx; omega
    simp [this]

theorem tendsto_det_coshSum (B : Matrix (Fin p) (Fin q) ℂ) :
    Tendsto (fun n => (coshSum n B).det.re) atTop
      (𝓝 (∏ i ∈ Finset.range (min p q), Real.cosh (singVal B i))) := by
  simp only [det_coshSum, ← prod_cosh_sPad]
  exact tendsto_finsetProd _ fun j _ => (Real.hasSum_cosh (sPad B j)).tendsto_sum_nat

theorem measurable_coshPow : ∀ (p q : ℕ) (c : ℝ), Measurable (coshPow c : UpqT p q → ℝ) := by
  intro p q c
  have : BorelSpace (UpqT p q) := (GlobalTheory.UpqTopology.upq_lcsc p q).2.2.2.2.1
  have h : Measurable fun g : UpqT p q =>
      ∏ i ∈ Finset.range (min p q), Real.cosh (singVal (cartanB g) i) := by
    refine measurable_of_tendsto_metrizable
      (f := fun n (g : UpqT p q) => (coshSum n (cartanB g)).det.re) (fun n => ?_)
      (tendsto_pi_nhds.2 fun g => tendsto_det_coshSum _)
    exact (Complex.continuous_re.comp
      (((continuous_coshSum n).comp continuous_cartanB).matrix_det)).measurable
  have e : (coshPow c : UpqT p q → ℝ) = fun g =>
      (∏ i ∈ Finset.range (min p q), Real.cosh (singVal (cartanB g) i)) ^ (-c) := by
    funext g
    exact Real.finsetProd_rpow _ _ (fun i _ => (Real.cosh_pos _).le) _
  rw [e]
  exact h.pow_const _

end GlobalTheory.CoshPowMeas
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaTaylorCoeffsAlgebraicAtComplexMultiplicatioStatement
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaTaylorCoeffs_algebraic_at_complexMultiplication : ∀ D : D7, useAlg D := by
  first | exact @GlobalTheory.ThetaAlgebraic.taylor_algebraic | exact GlobalTheory.ThetaAlgebraic.taylor_algebraic | (intros; apply GlobalTheory.ThetaAlgebraic.taylor_algebraic <;> assumption)
end

