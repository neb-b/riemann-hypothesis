module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0076
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0075
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.DilationUnipotentWeylMeasure
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0074
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormalFormOrderZeroOfParts

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselNonvanishingFromL2
section
open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal ComplexConjugate

noncomputable section

set_option maxHeartbeats 1600000

namespace Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity

open Formalism.FourierDecayAlt.ThreeDimData

theorem bessel_nonvanishing_from_L2 : Formalism.FourierDecayAlt.ThreeDimData.More.BesselNonvanishingReduction := by
  classical
  intro hSch hNI hGS hGG hDD hBC hInp _ k r ε lam h H _ _ _ σ w0 Wp _ _ _ _ z c u π μW μN μG νq hS W hWc hWeq
    hRe hpos hfin
  by_contra hcon
  push_neg at hcon
  obtain ⟨hlam, hσ, hgap, hGapOK, hw0, hz, hT, hc, hπ, hWh, hNh, hGh, hq⟩ := hS
  have hS' : Side k r ε lam h σ w0 z c u π μW μN μG νq :=
    ⟨hlam, hσ, hgap, hGapOK, hw0, hz, hT, hc, hπ, hWh, hNh, hGh, hq⟩
  have := hWh.1; have := hNh.1; have := hGh.1
  have hsm := DDSmoothness.DD_smooth hInp.2.2.1 hlam hσ hw0
  have memDD : ∀ g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), σ g w0 ∈ DDsp σ w0 :=
    fun g hg => Submodule.subset_span ⟨g, hg, rfl⟩
  have hof : Continuous (fun y : Formalism.QuantumDeterminants.Mt k r => (Matrix.of y : Mx k r)) := continuous_id
  have hGae : ∀ᵐ y ∂μG, Matrix.of y ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := ae_iff.mpr hGh.2.2.1
  have hWae : ∀ᵐ p1 ∂μW, Matrix.of p1 ∈ Formalism.QuantumDeterminants.UWset k r z := ae_iff.mpr hWh.2.2.1
  have hNae : ∀ᵐ p2 ∂μN, Matrix.of p2 ∈ Formalism.QuantumDeterminants.Nset k r := ae_iff.mpr hNh.2.2.1
  have hPae : ∀ᵐ p ∂(μW.prod μN), Matrix.of p.1 ∈ Formalism.QuantumDeterminants.UWset k r z ∧ Matrix.of p.2 ∈ Formalism.QuantumDeterminants.Nset k r :=
    (Measure.quasiMeasurePreserving_fst.ae hWae).and (Measure.quasiMeasurePreserving_snd.ae hNae)
  obtain ⟨hS0, hSc⟩ := DDSmoothness.muSof_facts hWh hNh
  have hνae := DDSmoothness.ae_UH_of_quot hGh.2.2.1 hS0 hSc hq
  have hBC' := hBC hInp k r ε lam h H σ w0 Wp z c u π μW μN μG νq hS'
  have hcs := Formalism.FourierDecayAlt.P.S3dx4.sigma_contOn hσ w0

  have hW0 : ∀ x0 ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), W x0 = 0 := by
    intro x0 hx0
    obtain ⟨hI, hR⟩ := hRe x0 hx0
    rw [← hR]
    unfold PI.BesselPeriodGGP.rconv
    apply ext_inner_left ℂ
    intro η
    rw [inner_zero_right, ← integral_inner hI η]
    obtain ⟨hxi, hxx, hxx'⟩ := uh_inv hx0
    set U : Set (Formalism.QuantumDeterminants.Mt k r) := {g | Matrix.of g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)} with hU
    have hUm : MeasurableSet U := (isClosed_UH.preimage hof).measurableSet
    let Φ : Formalism.QuantumDeterminants.Mt k r → ℂ := fun g =>
      ⟪η, PI.BesselPeriodGGP.eFun μG σ w0 (x0⁻¹ * Matrix.of g) • W (Matrix.of g)⟫_ℂ
    let Φ' : Formalism.QuantumDeterminants.Mt k r → ℂ := U.piecewise Φ (fun _ => 0)
    have hΦc : ContinuousOn Φ U := by
      have hm : ContinuousOn (fun g : Formalism.QuantumDeterminants.Mt k r => x0⁻¹ * (Matrix.of g : Mx k r)) U :=
        (continuous_const.matrix_mul hof).continuousOn
      have hmaps : Set.MapsTo (fun g : Formalism.QuantumDeterminants.Mt k r => x0⁻¹ * (Matrix.of g : Mx k r)) U
          (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) := fun g hg => DDSmoothness.uh_mul hxi hg
      have he : ContinuousOn (fun g : Formalism.QuantumDeterminants.Mt k r =>
          PI.BesselPeriodGGP.eFun μG σ w0 (x0⁻¹ * Matrix.of g)) U := by
        unfold PI.BesselPeriodGGP.eFun
        exact continuousOn_const.mul (continuous_star.comp_continuousOn
          (continuousOn_const.inner (hcs.comp hm hmaps)))
      have hWc' : ContinuousOn (fun g : Formalism.QuantumDeterminants.Mt k r => W (Matrix.of g)) U :=
        hWc.comp hof.continuousOn (fun g hg => hg)
      exact continuousOn_const.inner (he.smul hWc')
    have hΦm : Measurable Φ' := hΦc.measurable_piecewise continuousOn_const hUm
    have hlm : Measurable (Formalism.QuantumDeterminants.lmulM (k := k) (r := r) x0) := by
      have : Continuous (Formalism.QuantumDeterminants.lmulM (k := k) (r := r) x0) := continuous_const.matrix_mul hof
      exact this.measurable
    have htrans : (fun g : Formalism.QuantumDeterminants.Mt k r =>
        ⟪η, PI.BesselPeriodGGP.eFun μG σ w0 (Matrix.of g) • W (x0 * Matrix.of g)⟫_ℂ) =ᵐ[μG]
        Φ' ∘ Formalism.QuantumDeterminants.lmulM x0 := by
      filter_upwards [hGae] with g hg
      have hxg : x0 * Matrix.of g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := DDSmoothness.uh_mul hx0 hg
      have hmem : Formalism.QuantumDeterminants.lmulM x0 g ∈ U := hxg
      simp only [Function.comp, Φ', Set.piecewise, hmem, if_true, Φ]
      show _ = ⟪η, PI.BesselPeriodGGP.eFun μG σ w0 (x0⁻¹ * (x0 * Matrix.of g)) • W (x0 * Matrix.of g)⟫_ℂ
      rw [← Matrix.mul_assoc, hxx', Matrix.one_mul]
    have hmapEq : μG.map (Formalism.QuantumDeterminants.lmulM x0) = μG := hGh.2.2.2 x0 hx0
    have hΦint : Integrable Φ' μG := by
      have h1 : Integrable (fun g : Formalism.QuantumDeterminants.Mt k r =>
          ⟪η, PI.BesselPeriodGGP.eFun μG σ w0 (Matrix.of g) • W (x0 * Matrix.of g)⟫_ℂ) μG :=
        (innerSL ℂ η).integrable_comp hI
      have h2 : Integrable (Φ' ∘ Formalism.QuantumDeterminants.lmulM x0) μG := h1.congr htrans
      rw [← integrable_map_measure hΦm.aestronglyMeasurable hlm.aemeasurable, hmapEq] at h2
      exact h2
    rw [integral_congr_ae htrans]
    show ∫ a, Φ' (Formalism.QuantumDeterminants.lmulM x0 a) ∂μG = 0
    rw [← integral_map hlm.aemeasurable hΦm.aestronglyMeasurable, hmapEq]
    have : SFinite (muSof μW μN) := by unfold muSof; infer_instance
    refine quot_zero hq Φ' hΦm hΦint ?_
    filter_upwards [hνae] with x hx
    have hpm : Measurable (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r =>
        (fun i j => (Matrix.of p.1 * Matrix.of p.2) i j : Formalism.QuantumDeterminants.Mt k r)) := by
      have h1 : Continuous (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r => (Matrix.of p.1 : Mx k r)) := continuous_fst
      have h2 : Continuous (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r => (Matrix.of p.2 : Mx k r)) := continuous_snd
      have h3 : Continuous (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r =>
          (fun i j => (Matrix.of p.1 * Matrix.of p.2) i j : Formalism.QuantumDeterminants.Mt k r)) := h1.matrix_mul h2
      exact h3.measurable
    have hFm : Measurable (fun s : Formalism.QuantumDeterminants.Mt k r => Φ' (mulMt s x)) :=
      hΦm.comp (measurable_mulMt.comp (measurable_id.prodMk measurable_const))
    unfold muSof
    rw [integral_map hpm.aemeasurable hFm.aestronglyMeasurable]
    set u' := σ (Matrix.of x) w0 with hu'
    set v' := σ x0 w0 with hv'
    have hu'DD : u' ∈ DDsp σ w0 := memDD _ hx
    have hv'DD : v' ∈ DDsp σ w0 := memDD _ hx0
    have hI2 : Integrable (beInt z c π σ u' v') (μW.prod μN) := hBC'.1 u' (hsm _ hu'DD) v' (Or.inl hv'DD)
    have hval : ∀ᵐ p ∂(μW.prod μN), Φ' (mulMt (fun i j => (Matrix.of p.1 * Matrix.of p.2) i j) x) =
        ((PI.BesselPeriodGGP.fdegH μG σ w0 : ℝ) : ℂ) * ⟪beInt z c π σ u' v' p η, W (Matrix.of x)⟫_ℂ := by
      filter_upwards [hPae] with p hp
      have hs : Matrix.of p.1 * Matrix.of p.2 ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := DDSmoothness.uh_mul hp.1.1 hp.2.1
      have hsx : Matrix.of p.1 * Matrix.of p.2 * Matrix.of x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) :=
        DDSmoothness.uh_mul hs hx
      have hmem : mulMt (fun i j => (Matrix.of p.1 * Matrix.of p.2) i j) x ∈ U := hsx
      simp only [Φ', Set.piecewise, hmem, if_true, Φ]
      show ⟪η, PI.BesselPeriodGGP.eFun μG σ w0 (x0⁻¹ * (Matrix.of p.1 * Matrix.of p.2 * Matrix.of x)) •
          W (Matrix.of p.1 * Matrix.of p.2 * Matrix.of x)⟫_ℂ = _
      rw [hWeq _ hp.1 _ hp.2 _ hx]
      have hdet : IsUnit x0.det := Matrix.isUnit_det_of_right_inverse hxx
      have eσ : σ (x0⁻¹ * (Matrix.of p.1 * Matrix.of p.2 * Matrix.of x)) w0 =
          σ x0⁻¹ (σ (Matrix.of p.1 * Matrix.of p.2) u') := by
        rw [Formalism.FourierDecayAlt.P.TranslationBesselVanishing.sigma_mul hσ hxi hsx, Formalism.FourierDecayAlt.P.TranslationBesselVanishing.sigma_mul hσ hs hx]; rfl
      have eA : ⟪w0, σ (x0⁻¹ * (Matrix.of p.1 * Matrix.of p.2 * Matrix.of x)) w0⟫_ℂ =
          ⟪v', σ (Matrix.of p.1 * Matrix.of p.2) u'⟫_ℂ := by
        rw [eσ, sigma_inner hσ hxi, Matrix.nonsing_inv_nonsing_inv x0 hdet]
      unfold PI.BesselPeriodGGP.eFun beInt
      rw [eA, inner_smul_right, inner_smul_right, piW_inner hT hπ hp.1, ContinuousLinearMap.smul_apply,
        inner_smul_left]
      simp only [map_mul, Complex.star_def, Complex.conj_conj]
      ring
    rw [integral_congr_ae hval, integral_const_mul]
    have hf : Integrable (fun p => beInt z c π σ u' v' p η) (μW.prod μN) :=
      (ContinuousLinearMap.apply ℂ Wp η).integrable_comp hI2
    have hinner : ∫ p, ⟪beInt z c π σ u' v' p η, W (Matrix.of x)⟫_ℂ ∂(μW.prod μN) =
        ⟪be z c π σ μW μN u' v' η, W (Matrix.of x)⟫_ℂ := by
      have e2 : be z c π σ μW μN u' v' η = ∫ p, beInt z c π σ u' v' p η ∂(μW.prod μN) :=
        ContinuousLinearMap.integral_apply hI2 η
      rw [e2, ← inner_conj_symm, ← integral_inner hf (W (Matrix.of x)), ← integral_conj]
      congr 1
      funext p
      rw [inner_conj_symm]
    rw [hinner, hcon u' hu'DD v' hv'DD]
    simp

  have hl0 : PI.BesselPeriodGGP.l2SG νq W = 0 := by
    unfold PI.BesselPeriodGGP.l2SG
    rw [lintegral_congr_ae (g := fun _ => 0) ?_, lintegral_zero]
    filter_upwards [hνae] with x hx
    rw [hW0 _ hx]; simp
  rw [hl0] at hpos
  exact lt_irrefl _ hpos

theorem bessel_nonzero_l2_reduction : Formalism.FourierDecayAlt.ThreeDimData.More.BesselNonvanishingReduction := bessel_nonvanishing_from_L2

end Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CapAdInv
section
open Matrix Finset
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.JFxE

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity Formalism.FourierDecayAlt.P.JFxB

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem lie_sub {X Y : Mat k r} (hX : inLie k r X) (hY : inLie k r Y) : inLie k r (X - Y) := by
  unfold inLie at *
  rw [Matrix.conjTranspose_sub, Matrix.sub_mul, Matrix.mul_sub, sub_add_sub_comm, hX, hY, sub_zero]

theorem lie_add {X Y : Mat k r} (hX : inLie k r X) (hY : inLie k r Y) : inLie k r (X + Y) := by
  unfold inLie at *
  rw [Matrix.conjTranspose_add, Matrix.add_mul, Matrix.mul_add, add_add_add_comm, hX, hY, add_zero]

theorem EHH {φ F : Mat k r → E} {U : Set (Mat k r)} {g : Mat k r} (hφ : CkOn 2 (GV k r) φ) (hU : IsOpen U)
    (hgU : g ∈ U) (hg : g ∈ GV k r) (hF : ContDiffOn ℝ 2 F U) (hff : ∀ h ∈ U, h ∈ GV k r → φ h = F h)
    (a b c d : Fin (2 * r + k + 1)) :
    Q.EH k r a b (Q.EH k r c d φ) g =
      (fderiv ℝ F g (g * Xa k r a b * Xa k r c d) +
          fderiv ℝ (fderiv ℝ F) g (g * Xa k r a b) (g * Xa k r c d)) +
        Complex.I • (fderiv ℝ F g (g * Xa k r a b * Xb k r c d) +
          fderiv ℝ (fderiv ℝ F) g (g * Xa k r a b) (g * Xb k r c d)) +
      Complex.I • ((fderiv ℝ F g (g * Xb k r a b * Xa k r c d) +
          fderiv ℝ (fderiv ℝ F) g (g * Xb k r a b) (g * Xa k r c d)) +
        Complex.I • (fderiv ℝ F g (g * Xb k r a b * Xb k r c d) +
          fderiv ℝ (fderiv ℝ F) g (g * Xb k r a b) (g * Xb k r c d))) := by
  have hc : ContDiffOn ℝ (((1 + 1 : ℕ) : ℕ∞) : WithTop ℕ∞) F U := by simpa using hF
  have hφ2 : CkOn ((1 : ℕ∞) + 1) (GV k r) φ := by
    have e : ((1 : ℕ∞) + 1) = 2 := by norm_num
    rw [e]; exact hφ
  have hφ1 : ∀ X : Mat k r, inLie k r X → CkOn 1 (GV k r) (Dx (false, X) φ) :=
    fun X hX => CkOn_Dx (x := (false, X)) hX hφ2
  have hop : ∀ X Y : Mat k r, inLie k r X → inLie k r Y →
      Dx (false, X) (Dx (false, Y) φ) g =
        fderiv ℝ (fderiv ℝ F) g (g * X) (g * Y) + fderiv ℝ F g (g * X * Y) :=
    fun X Y hX hY => Formalism.FourierDecayAlt.P.B4.op_op_ext false false hU hc hff hX hY hgU hg
  have hEcd : Q.EH k r c d φ = fun h => Dx (false, Xa k r c d) φ h + Complex.I • Dx (false, Xb k r c d) φ h :=
    EH_eq c d φ
  rw [EH_eq a b, hEcd]
  simp only
  rw [Dx_add (x := (false, Xa k r a b)) (Xa_lie a b) (hφ1 _ (Xa_lie c d)) (CkOn_smul _ (hφ1 _ (Xb_lie c d))) g hg,
    Dx_add (x := (false, Xb k r a b)) (Xb_lie a b) (hφ1 _ (Xa_lie c d)) (CkOn_smul _ (hφ1 _ (Xb_lie c d))) g hg,
    Dx_smul, Dx_smul]
  simp only
  rw [hop _ _ (Xa_lie a b) (Xa_lie c d), hop _ _ (Xa_lie a b) (Xb_lie c d), hop _ _ (Xb_lie a b) (Xa_lie c d),
    hop _ _ (Xb_lie a b) (Xb_lie c d)]
  simp only [smul_add]
  abel

theorem single_comm (a b c d : Fin (2 * r + k + 1)) :
    Matrix.single a b (1 : ℂ) * Matrix.single c d 1 - Matrix.single c d 1 * Matrix.single a b 1 =
      ((if b = c then Matrix.single a d 1 else 0) - (if d = a then Matrix.single c b 1 else 0) : Mat k r) := by
  split_ifs with h1 h2 h2
  all_goals
    first
    | (try subst h1); (try subst h2)
      simp [Matrix.single_mul_single_same, Matrix.single_mul_single_of_ne, *]
    | ext i j
      simp_all [Matrix.mul_apply, Matrix.single_apply, ite_and, mul_ite, ite_mul, Finset.sum_ite_eq,
        Finset.sum_ite_eq']

theorem EH_HGl : HGl (Q.EH (E := E) k r) := by
  intro a b c d φ hφ g hg
  obtain ⟨U, F, hU, hgU, hF, hff⟩ := hφ g hg
  have hF2 : ContDiffOn ℝ 2 F U := by exact_mod_cast hF
  have hF' : HasFDerivAt F (fderiv ℝ F g) g :=
    ((hF2.differentiableOn (by norm_num)).differentiableAt (hU.mem_nhds hgU)).hasFDerivAt
  have hsym : ∀ v w : Mat k r, fderiv ℝ (fderiv ℝ F) g v w = fderiv ℝ (fderiv ℝ F) g w v := by
    have hc : ContDiffOn ℝ (((1 + 1 : ℕ) : ℕ∞) : WithTop ℕ∞) F U := by simpa using hF2
    have := (hc.contDiffAt (hU.mem_nhds hgU)).isSymmSndFDerivAt
      (by rw [minSmoothness_of_isRCLikeNormedField]; norm_cast)
    intro v w; exact this v w
  set A1 := Xa k r a b with hA1
  set A2 := Xb k r a b with hA2
  set C1 := Xa k r c d with hC1
  set C2 := Xb k r c d with hC2
  set D1 := fderiv ℝ F g with hD1
  set D2 := fderiv ℝ (fderiv ℝ F) g with hD2
  have hR : (if b = c then Q.EH k r a d φ g else 0) - (if d = a then Q.EH k r c b φ g else 0) =
      Psi D1 g (Matrix.single a b (1 : ℂ) * Matrix.single c d 1 - Matrix.single c d 1 * Matrix.single a b 1) := by
    rw [single_comm, Psi_sub]
    congr 1
    · split_ifs
      · exact EH_psi hU hgU hg hF' hff a d
      · exact (Psi_zero D1 g).symm
    · split_ifs
      · exact EH_psi hU hgU hg hF' hff c b
      · exact (Psi_zero D1 g).symm
  have e1 : A1 + Complex.I • A2 = Matrix.single a b 1 := hp_decomp _
  have e2 : C1 + Complex.I • C2 = Matrix.single c d 1 := hp_decomp _
  have hbr : Matrix.single a b (1 : ℂ) * Matrix.single c d 1 - Matrix.single c d 1 * Matrix.single a b 1 =
      ((A1 * C1 - C1 * A1) - (A2 * C2 - C2 * A2)) + Complex.I • ((A1 * C2 - C2 * A1) + (A2 * C1 - C1 * A2)) := by
    rw [← e1, ← e2]
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul]
    have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
    linear_combination (norm := module) hI • (A2 * C2 - C2 * A2)
  have hl1 : inLie k r ((A1 * C1 - C1 * A1) - (A2 * C2 - C2 * A2)) :=
    lie_sub (lie_bracket (Xa_lie a b) (Xa_lie c d)) (lie_bracket (Xb_lie a b) (Xb_lie c d))
  have hl2 : inLie k r ((A1 * C2 - C2 * A1) + (A2 * C1 - C1 * A2)) :=
    lie_add (lie_bracket (Xa_lie a b) (Xb_lie c d)) (lie_bracket (Xb_lie a b) (Xa_lie c d))
  have hP : Psi D1 g (((A1 * C1 - C1 * A1) - (A2 * C2 - C2 * A2)) + Complex.I • ((A1 * C2 - C2 * A1) + (A2 * C1 - C1 * A2))) =
      D1 (g * ((A1 * C1 - C1 * A1) - (A2 * C2 - C2 * A2))) + Complex.I • D1 (g * ((A1 * C2 - C2 * A1) + (A2 * C1 - C1 * A2))) := by
    unfold Psi
    rw [(hp_of_parts hl1 hl2).1, (hp_of_parts hl1 hl2).2]
  rw [hR, hbr, hP, EHH hφ hU hgU hg hF2 hff a b c d, EHH hφ hU hgU hg hF2 hff c d a b]
  rw [← hA1, ← hA2, ← hC1, ← hC2, ← hD1, ← hD2]
  rw [hsym (g * C1) (g * A1), hsym (g * C2) (g * A1), hsym (g * C1) (g * A2), hsym (g * C2) (g * A2)]
  simp only [Matrix.mul_sub, Matrix.mul_add, map_sub, map_add (f := _), ← Matrix.mul_assoc]
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  linear_combination (norm := module) hI • (D1 (g * A2 * C2) - D1 (g * C2 * A2))

theorem capAdInv : CapAdInv := by
  intro k r E _ _ y u f hy hf h hh
  have hyu := gv_unit hy
  have hQP : y * y⁻¹ = 1 := Matrix.mul_nonsing_inv _ hyu
  have hm : Q.mdim k r 0 = 2 * r + k + 1 := by simp [Q.mdim]
  set e : Fin (Q.mdim k r 0) ≃ Fin (2 * r + k + 1) := finCongr hm with he
  have hpos : Q.posL k r 0 = ⇑e := by
    funext j; apply Fin.ext; simp [Q.posL, he]
  rw [hpos]
  exact ad_main (Q.EH k r) EH_HC EH_HL EH_HA EH_HS EH_HGl (EHc k r y) (EHc_HL hy) hQP
    (fun c d φ hφ g hg => EHc_change hy c d φ hφ g hg) e u f (by rw [hm]; exact hf) h hh

theorem cVRho : JF.CVRho := cvRho_of capAdInv

end Formalism.FourierDecayAlt.P.JFxE
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTCCurvTrCalc
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

noncomputable section

theorem modA_eq_fun (P : M.Par) (ρ : M.Ty P) :
    modA P ρ = fun w => (M.aC P ρ : ℂ) * star w * (w * star w - (P.TT : ℂ))⁻¹ := by
  funext w
  have h : (w * star w : ℂ) = (Complex.normSq w : ℂ) := Complex.mul_conj w
  rw [h]
  simp only [modA, div_eq_mul_inv]

theorem dZb_modA (P : M.Par) (ρ : M.Ty P) {ζ : ℂ} (hζ : ζ ∈ Ann P) :
    NF.dZb (modA P ρ) ζ = -(((M.aC P ρ * P.TT : ℝ) : ℂ)) / ((Complex.normSq ζ : ℂ) - (P.TT : ℂ)) ^ 2 := by
  have hns : (ζ * star ζ : ℂ) = (Complex.normSq ζ : ℂ) := Complex.mul_conj ζ
  have hlt : P.TT < Complex.normSq ζ := hζ
  have hN0 : ζ * star ζ - (P.TT : ℂ) ≠ 0 := by
    rw [hns, ← Complex.ofReal_sub]
    exact Complex.ofReal_ne_zero.mpr (sub_ne_zero.mpr hlt.ne')
  have hS := (hasFDerivAt_id (𝕜 := ℝ) ζ).star
  have hN := ((hasFDerivAt_id (𝕜 := ℝ) ζ).mul hS).sub_const (P.TT : ℂ)
  have hI := ((hasDerivAt_inv hN0).hasFDerivAt.restrictScalars ℝ).comp ζ hN
  have hF := ((hasFDerivAt_const (𝕜 := ℝ) (M.aC P ρ : ℂ) ζ).mul hS).mul hI
  have hF' : HasFDerivAt (fun w : ℂ => (M.aC P ρ : ℂ) * star w * (w * star w - (P.TT : ℂ))⁻¹) _ ζ := hF
  rw [modA_eq_fun]
  simp only [NF.dZb]
  rw [hF'.fderiv]
  rw [← hns]
  simp [Complex.star_def]
  field_simp
  ring_nf
  simp only [Complex.I_sq]
  ring

theorem re_dZb_modA (P : M.Par) (ρ : M.Ty P) {ζ : ℂ} (hζ : ζ ∈ Ann P) :
    (NF.dZb (modA P ρ) ζ).re = -(M.aC P ρ * P.TT) / (Complex.normSq ζ - P.TT) ^ 2 := by
  rw [dZb_modA P ρ hζ]
  have h : (-(((M.aC P ρ * P.TT : ℝ) : ℂ)) / ((Complex.normSq ζ : ℂ) - (P.TT : ℂ)) ^ 2) =
      ((-(M.aC P ρ * P.TT) / (Complex.normSq ζ - P.TT) ^ 2 : ℝ) : ℂ) := by
    push_cast
    ring
  rw [h, Complex.ofReal_re]

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTCRefAn
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Complex MeasureTheory intervalIntegral

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

noncomputable section

theorem reference_annulus_holds : GTCRefAn := by
  intro TT α c hTT hα hre R hR hR2
  have hpt : ∀ θ : ℝ, TT < Complex.normSq (circleMap 0 R θ) := by
    intro θ
    have h1 : ‖circleMap 0 R θ‖ = R := by rw [norm_circleMap_zero, abs_of_pos hR]
    rw [Complex.normSq_eq_norm_sq, h1]
    exact hR2
  have hcα : Continuous (fun θ : ℝ => α (circleMap 0 R θ)) :=
    hα.continuousOn.comp_continuous (continuous_circleMap 0 R) hpt
  have hd : (fun θ : ℝ => deriv (circleMap 0 R) θ) = fun θ => circleMap 0 R θ * Complex.I := by
    funext θ
    exact deriv_circleMap 0 R θ
  have hF : Continuous (fun θ : ℝ => deriv (circleMap 0 R) θ • α (circleMap 0 R θ)) := by
    have h2 : Continuous (fun θ : ℝ => deriv (circleMap 0 R) θ) := by
      rw [hd]
      exact (continuous_circleMap 0 R).mul continuous_const
    exact h2.smul hcα
  have key : ∀ θ : ℝ, Complex.imCLM (deriv (circleMap 0 R) θ • α (circleMap 0 R θ)) = c := by
    intro θ
    rw [deriv_circleMap, smul_eq_mul, Complex.imCLM_apply]
    rw [← hre (circleMap 0 R θ) (hpt θ)]
    simp only [Complex.mul_im, Complex.mul_re, Complex.I_re, Complex.I_im]
    ring
  unfold circleIntegral
  rw [← Complex.imCLM_apply, ← ContinuousLinearMap.intervalIntegral_comp_comm _ (hF.intervalIntegrable _ _)]
  simp only [key]
  rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero]

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTCTheta
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

noncomputable section

def rhoSum (P : M.Par) (ρ : M.Ty P) : ℝ := ∑ i ∈ Finset.Icc 1 (P.k - 1), M.rho P ρ i

def uSum (P : M.Par) : ℝ := ∑ i ∈ Finset.Icc 1 P.k, (P.u i + P.u' i)

theorem aC_eq (P : M.Par) (ρ : M.Ty P) : M.aC P ρ = uSum P / 2 - rhoSum P ρ := rfl

def ThetaNF (P : M.Par) {𝒜 : Type} [Ring 𝒜] [StarRing 𝒜] [Algebra ℂ 𝒜] (d : Q.NFData P 𝒜) : 𝒜 :=
  d.L.ζ * d.L.nab + d.L.ζb * d.L.nabs + d.κ (fun ρ => ((rhoSum P ρ : ℝ) : ℂ)) +
    algebraMap ℂ 𝒜 d.L.TT * d.L.GGi * d.κ (fun ρ => ((2 * rhoSum P ρ - uSum P : ℝ) : ℂ))

def GTRTopNF : Prop :=
  ∀ (P : M.Par) (𝒜 : Type) [Ring 𝒜] [StarRing 𝒜] [Algebra ℂ 𝒜] (d : Q.NFData P 𝒜),
    P.OK → 2 ≤ P.k → Fr.IsStarLevel d.L → d.Rel → d.L.TT = ((P.TT : ℝ) : ℂ) →
    ∃ c : ℕ → 𝒜, (∀ Y : ℂ, d.QQ Y 0 0 = ∑ j ∈ Finset.range (P.k + 2), Y ^ j • c j) ∧
      ∃ s : ℤ, c P.k = ThetaNF P d + ((s : ℂ)) • (1 : 𝒜)

def GTRTopAct : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ)
    (π : Q.Mx P.k P.r → (Wp →L[ℂ] Wp)) (π' : Q.Mx P.k P.r → (Wq →L[ℂ] Wq)),
    Q.IsPlace P z z' π π' → 2 ≤ P.k → ∀ X : Q.ActualOps P.k P.r z z' π π',
    ∃ c : ℕ → Module.End ℂ (Q.RadSp P.k P.r z z' π π'),
      (∀ Y : ℂ, X.t Y 0 0 = ∑ j ∈ Finset.range (P.k + 2), Y ^ j • c j) ∧
      ∃ s : ℤ, ∀ (Φ : Q.RadSp P.k P.r z z' π π'), ∀ x ∈ Q.DomR P.k P.r z z',
        (c P.k Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2 =
          (∑ a : Fin (Q.mdim P.k P.r (Fin.last P.r)),
            Q.EH P.k P.r (Q.posL P.k P.r (Fin.last P.r) a) (Q.posL P.k P.r (Fin.last P.r) a)
              ((Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) x.1) x.2) +
            ((s : ℂ)) • (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTSSLSliceDZ
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

theorem second_shift_slice_derivative : GTSSLSliceDZ := by
  intro Wp Wq _ _ _ _ _ _ P Bs hpl T hT Φ Φ' c c' hc hc' hEq ζ hζ
  obtain ⟨n, A, -, hTA⟩ := hT
  have hTT : Tz P.k P.r Bs.z * Tz P.k P.r Bs.z' = P.TT := by
    rw [hpl.2.2.2.1, hpl.2.2.2.2.1]; rfl
  have hU : IsOpen (Ann P) := isOpen_lt continuous_const Complex.continuous_normSq
  have hq : ((c, ζ) : (Fin P.r → ℂ) × ℂ) ∈ NF.QR P.k P.r Bs.z Bs.z' := ⟨hc, by rw [hTT]; exact hζ⟩
  have hq' : ((c', ζ) : (Fin P.r → ℂ) × ℂ) ∈ NF.QR P.k P.r Bs.z Bs.z' := ⟨hc', by rw [hTT]; exact hζ⟩
  have hev : (fun ζ' => NF.radR P.k P.r Bs.z Bs.z' Bs.μsec (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) (c, ζ')) =ᶠ[nhds ζ]
      (fun ζ' => NF.radR P.k P.r Bs.z Bs.z' Bs.μsec (Φ' : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) (c', ζ')) := by
    filter_upwards [hU.mem_nhds hζ] with ζ' hζ'
    have m : ((c, ζ') : (Fin P.r → ℂ) × ℂ) ∈ NF.QR P.k P.r Bs.z Bs.z' := ⟨hc, by rw [hTT]; exact hζ'⟩
    have m' : ((c', ζ') : (Fin P.r → ℂ) × ℂ) ∈ NF.QR P.k P.r Bs.z Bs.z' := ⟨hc', by rw [hTT]; exact hζ'⟩
    unfold NF.radR
    rw [Set.indicator_of_mem m, Set.indicator_of_mem m']
    exact hEq ζ' hζ'
  have e1 : NF.radR P.k P.r Bs.z Bs.z' Bs.μsec (T Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) (c, ζ) =
      (T Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c (NF.muZ P.k P.r Bs.μsec ζ) := by
    unfold NF.radR; rw [Set.indicator_of_mem hq]
  have e2 : NF.radR P.k P.r Bs.z Bs.z' Bs.μsec (T Φ' : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) (c', ζ) =
      (T Φ' : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c' (NF.muZ P.k P.r Bs.μsec ζ) := by
    unfold NF.radR; rw [Set.indicator_of_mem hq']
  have h1 := hTA Φ (c, ζ) hq
  have h2 := hTA Φ' (c', ζ) hq'
  dsimp only at h1 h2
  rw [← e1, ← e2, h1, h2]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [(hev.iteratedFDeriv ℝ j).eq_of_nhds]

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
end

