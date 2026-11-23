module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1098
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1110
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1128
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1305
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1117
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0019
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfM
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.FirstMinimumInvariantContinuousPosOnFrames
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1311
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0712
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfK
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0013
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.KaUnfoldPfA
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.KronHolPsiStatementHolds
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0033
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.EnormPowLeInvMeasureMulLintegralBall
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0023
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1306
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0152
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1077
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1277
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0012
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0202

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralMixTopSlotEqZero
section
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

namespace GlobalTheory.GoodTop

set_option autoImplicit false

noncomputable def transConn {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] (ρ : V n → ℝ)
    (G₀ G₁ : V n → Matrix r r ℂ) (j : Fin n) (i a : Fin n) : V n → Matrix r r ℂ :=
  if i < j then fun x => -conn G₁ x (coordVec a)
  else if i = j then fun x => -((ρ x : ℂ) • (conn G₁ x (coordVec a) - conn G₀ x (coordVec a)))
  else fun x => -conn G₀ x (coordVec a)

theorem weighted_bound_cut_sum (x A B w C c : ℝ) (hx0 : 0 ≤ x) (hx : x ≤ C) (hA0 : 0 ≤ A) (hB0 : 0 ≤ B)
    (hw0 : 0 ≤ w) (hw1 : w ≤ 1) (hA : A * w ≤ c) (hB : B ≤ C) : x * (A + B) * w ≤ C * (|c| + C) := by
  have h1 : (A + B) * w ≤ |c| + C := by nlinarith [le_abs_self c]
  have hC : 0 ≤ C := hx0.trans hx
  rw [mul_assoc]
  exact mul_le_mul hx h1 (by positivity) hC

theorem weighted_bound_cut_entry (x X₁ X₀ d Y₁ Y₀ : ℂ) (wa wb C c : ℝ) (hx : ‖x‖ ≤ C) (hd : ‖d‖ ≤ C)
    (hX₁ : ‖X₁‖ * (wa * wb) ≤ c) (hX₀ : ‖X₀‖ ≤ C) (hY₁ : ‖Y₁‖ * wa ≤ c) (hY₀ : ‖Y₀‖ ≤ C)
    (hwa0 : 0 ≤ wa) (hwa1 : wa ≤ 1) (hwb0 : 0 ≤ wb) (hwb1 : wb ≤ 1) :
    ‖x * (X₁ - X₀) - d * (Y₁ - Y₀)‖ * (wa * wb) ≤ 2 * C * (|c| + C) := by
  have hC : 0 ≤ C := (norm_nonneg _).trans hx
  have e1 := weighted_bound_cut_sum ‖x‖ ‖X₁‖ ‖X₀‖ (wa * wb) C c (norm_nonneg _) hx (norm_nonneg _) (norm_nonneg _)
    (by positivity) (by nlinarith) hX₁ hX₀
  have e2 := weighted_bound_cut_sum ‖d‖ ‖Y₁‖ ‖Y₀‖ wa C c (norm_nonneg _) hd (norm_nonneg _) (norm_nonneg _)
    hwa0 hwa1 hY₁ hY₀
  have n1 : ‖x * (X₁ - X₀) - d * (Y₁ - Y₀)‖ ≤ ‖x‖ * (‖X₁‖ + ‖X₀‖) + ‖d‖ * (‖Y₁‖ + ‖Y₀‖) := by
    refine (norm_sub_le _ _).trans (add_le_add ?_ ?_) <;> rw [norm_mul] <;>
      exact mul_le_mul_of_nonneg_left (norm_sub_le _ _) (norm_nonneg _)
  have hww : 0 ≤ wa * wb := by positivity
  have e2' : ‖d‖ * (‖Y₁‖ + ‖Y₀‖) * (wa * wb) ≤ C * (|c| + C) := by
    have h0 : 0 ≤ ‖d‖ * (‖Y₁‖ + ‖Y₀‖) * wa := by positivity
    calc ‖d‖ * (‖Y₁‖ + ‖Y₀‖) * (wa * wb) = (‖d‖ * (‖Y₁‖ + ‖Y₀‖) * wa) * wb := by ring
      _ ≤ (‖d‖ * (‖Y₁‖ + ‖Y₀‖) * wa) * 1 := mul_le_mul_of_nonneg_left hwb1 h0
      _ ≤ C * (|c| + C) := by rw [mul_one]; exact e2
  calc ‖x * (X₁ - X₀) - d * (Y₁ - Y₀)‖ * (wa * wb)
      ≤ (‖x‖ * (‖X₁‖ + ‖X₀‖) + ‖d‖ * (‖Y₁‖ + ‖Y₀‖)) * (wa * wb) := mul_le_mul_of_nonneg_right n1 hww
    _ = ‖x‖ * (‖X₁‖ + ‖X₀‖) * (wa * wb) + ‖d‖ * (‖Y₁‖ + ‖Y₀‖) * (wa * wb) := by ring
    _ ≤ C * (|c| + C) + C * (|c| + C) := add_le_add e1 e2'
    _ = 2 * C * (|c| + C) := by ring

theorem integral_mixTop_position_eq_zero : ∀ {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] (S : Finset (Fin n)) (U K : Set (V n)) (G₀ G₁ : V n → Matrix r r ℂ) (ρ : V n → ℝ) (c : ℝ), IsOpen U → IsCompact K → K ⊆ U → (∀ v ∈ U, ∀ a ∈ S, ‖v a‖ ≤ 1 / 2) → (∀ v ∈ U, MContDiffAt ∞ G₀ v ∧ IsUnit (G₀ v).det) → (∀ v ∈ offHyp S U, MContDiffAt ∞ G₁ v ∧ IsUnit (G₁ v).det) → (∀ v ∈ offHyp S U, ∀ a i j, ‖conn G₁ v (coordVec a) i j‖ * poinWt S v a ≤ c) → (∀ v ∈ offHyp S U, ∀ a b i j, ‖curv G₁ v (coordVec a) (coordVec b) i j‖ * (poinWt S v a * poinWt S v b) ≤ c) → ContDiffOn ℝ ∞ ρ U → (∀ v ∈ U, v ∉ K → ρ v = 0) → ∀ j : Fin n, IntegrableOn (fun v => mixTop (intersection_update_fsHerm_neg_one (curvAt G₁ v) ((ρ v : ℂ) • (curvAt G₁ v - curvAt G₀ v) - cutForm ρ G₀ G₁ v) (curvAt G₀ v) j)) (offHyp S U) ∧ ∫ v in offHyp S U, mixTop (intersection_update_fsHerm_neg_one (curvAt G₁ v) ((ρ v : ℂ) • (curvAt G₁ v - curvAt G₀ v) - cutForm ρ G₀ G₁ v) (curvAt G₀ v) j) = 0 := by
  intro n r _ _ S U K G₀ G₁ ρ c hU hK hKU hsmall hG₀ hG₁ hconn hcurv hρ hρK j
  obtain ⟨C, hC0, hC⟩ := exists_bound_smooth_data U K G₀ ρ hU hK hKU hG₀ hρ
  have h2 : (2 : WithTop ℕ∞) ≤ ∞ := WithTop.coe_le_coe.2 le_top
  have h3 : (2 : WithTop ℕ∞) + 1 ≤ ∞ := WithTop.coe_le_coe.2 le_top
  have hw : ∀ v ∈ U, ∀ a, 0 ≤ poinWt S v a ∧ poinWt S v a ≤ 1 :=
    fun v hv a => (_root_.GlobalTheory.GoodTop.poinWt_mem_Icc_and_pos S v (hsmall v hv)).1 a
  have hρd : ∀ v ∈ U, ContDiffAt ℝ ∞ ρ v := fun v hv => hρ.contDiffAt (hU.mem_nhds hv)
  have hρc : ∀ v ∈ U, ContDiffAt ℝ 2 (fun x => (ρ x : ℂ)) v := fun v hv =>
    Complex.ofRealCLM.contDiff.contDiffAt.comp v ((hρd v hv).of_le h2)
  set θ := transConn ρ G₀ G₁ j with hθ
  have hsm : ∀ i a, ∀ v ∈ offHyp S U, MContDiffAt 2 (θ i a) v := by
    intro i a v hv
    have h1 := (hG₁ v hv).1.conn (j := 2) (hG₁ v hv).2 h3 (coordVec a)
    have h0 := (hG₀ v hv.1).1.conn (j := 2) (hG₀ v hv.1).2 h3 (coordVec a)
    simp only [hθ, transConn]
    split_ifs
    · exact h1.neg
    · exact (MContDiffAt.smul (hρc v hv.1) (h1.sub h0)).neg
    · exact h0.neg
  have heq : ∀ v ∈ offHyp S U, (fun i a b => mdbar (θ i a) v (coordVec b)) =
      intersection_update_fsHerm_neg_one (curvAt G₁ v) ((ρ v : ℂ) • (curvAt G₁ v - curvAt G₀ v) - cutForm ρ G₀ G₁ v) (curvAt G₀ v) j := by
    intro v hv
    funext i a b
    simp only [hθ, transConn, intersection_update_fsHerm_neg_one]
    split_ifs with h h'
    · rw [mdbar_neg]; rfl
    · exact congrFun (congrFun (GlobalTheory.T.antiholomorphicDeriv_cutoff_connection_difference_eq ((hρd v hv.1).differentiableAt (by simp))
        ((hG₀ v hv.1).1.of_le h2) (hG₀ v hv.1).2 ((hG₁ v hv).1.of_le h2) (hG₁ v hv).2) a) b
    · rw [mdbar_neg]; rfl
  have hzero : ∀ a, ∀ v ∈ offHyp S U, v ∉ K → θ j a v = 0 := by
    intro a v hv hvK
    simp [hθ, transConn, hρK v hv.1 hvK]
  have hcC : 0 ≤ C * (|c| + C) := by positivity
  have hbd1 : ∀ v ∈ offHyp S U, v ∈ K → ∀ a p q,
      ‖θ j a v p q‖ * poinWt S v a ≤ |c| + C + 2 * C * (|c| + C) := by
    intro v hv hvK a p q
    obtain ⟨hρv, -, hc0, -⟩ := hC v hvK
    simp only [hθ, transConn, lt_irrefl, if_false, if_true, Matrix.neg_apply, Matrix.smul_apply,
      Matrix.sub_apply, smul_eq_mul, norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have e := weighted_bound_cut_sum |ρ v| ‖conn G₁ v (coordVec a) p q‖ ‖conn G₀ v (coordVec a) p q‖ (poinWt S v a) C c
      (abs_nonneg _) hρv (norm_nonneg _) (norm_nonneg _) (hw v hv.1 a).1 (hw v hv.1 a).2
      (hconn v hv a p q) (hc0 a p q)
    have n1 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
      (norm_sub_le (conn G₁ v (coordVec a) p q) (conn G₀ v (coordVec a) p q)) (abs_nonneg (ρ v)))
      (hw v hv.1 a).1
    have : 0 ≤ |c| := abs_nonneg c
    nlinarith
  have hbd2 : ∀ v ∈ offHyp S U, v ∈ K → ∀ i a b p q,
      ‖mdbar (θ i a) v (coordVec b) p q‖ * (poinWt S v a * poinWt S v b) ≤
        |c| + C + 2 * C * (|c| + C) := by
    intro v hv hvK i a b p q
    obtain ⟨hρv, hdv, hc0, hk0⟩ := hC v hvK
    obtain ⟨hwa0, hwa1⟩ := hw v hv.1 a
    obtain ⟨hwb0, hwb1⟩ := hw v hv.1 b
    have hww : 0 ≤ poinWt S v a * poinWt S v b := by positivity
    have hww1 : poinWt S v a * poinWt S v b ≤ 1 := by nlinarith
    have hca : 0 ≤ |c| := abs_nonneg c
    rw [show mdbar (θ i a) v (coordVec b) = _ from congrFun (congrFun (congrFun (heq v hv) i) a) b]
    simp only [intersection_update_fsHerm_neg_one]
    split_ifs with h h'
    · have := hcurv v hv a b p q
      simp only [curvAt]
      nlinarith [le_abs_self c]
    · simp only [curvAt, cutForm, Pi.sub_apply, Pi.smul_apply, Matrix.sub_apply, Matrix.smul_apply,
        smul_eq_mul]
      have e := weighted_bound_cut_entry (ρ v : ℂ) (curv G₁ v (coordVec a) (coordVec b) p q) (curv G₀ v (coordVec a) (coordVec b) p q)
        (dbar (fun x => (ρ x : ℂ)) v (coordVec b)) (conn G₁ v (coordVec a) p q) (conn G₀ v (coordVec a) p q)
        (poinWt S v a) (poinWt S v b) C c (by rw [Complex.norm_real, Real.norm_eq_abs]; exact hρv) (hdv b)
        (hcurv v hv a b p q) (hk0 a b p q) (hconn v hv a p q) (hc0 a p q) hwa0 hwa1 hwb0 hwb1
      nlinarith
    · simp only [curvAt]
      have := hk0 a b p q
      have := mul_le_mul_of_nonneg_left hww1 (norm_nonneg (curv G₀ v (coordVec a) (coordVec b) p q))
      nlinarith
  obtain ⟨hi, hint⟩ := _root_.GlobalTheory.GoodTop.integral_mixTop_mdbar_eq_zero S U K θ j (|c| + C + 2 * C * (|c| + C)) hU hK hKU hsmall hsm hzero
    hbd1 hbd2
  have hO : MeasurableSet (offHyp S U) := (isOpen_offHyp_of_isOpen S U hU).measurableSet
  refine ⟨hi.congr_fun (fun v hv => congrArg mixTop (heq v hv)) hO, ?_⟩
  rw [← hint]
  exact setIntegral_congr_fun hO fun v hv => congrArg mixTop (heq v hv).symm

end GlobalTheory.GoodTop
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvariantExtensionMeasurableContDiffOnChart
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.PeakWeightSmooth

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem lact_inv_lact (X : Data E r) (γ : GL (Fin r) E) (y : Frame X.Ψ r) : lact γ⁻¹ (lact γ y) = y := by
  rw [KU.lact_lact X, inv_mul_cancel, KU.lact_one X]

theorem lact_lact_inv (X : Data E r) (γ : GL (Fin r) E) (y : Frame X.Ψ r) : lact γ (lact γ⁻¹ y) = y := by
  rw [KU.lact_lact X, mul_inv_cancel, KU.lact_one X]

theorem local_form (X : Data E r) (x : Frame X.Ψ r) (hx : IsOrth X x) (ρ R : ℝ) (η : V (nd X) → ℝ)
    (ψ : Frame X.Ψ r → ℝ) (hρR : ρ < R) (hR : ∀ z : V (nd X), ‖z‖ ≤ R → z ∈ OmF X x)
    (hψ : ∀ γ ∈ X.Γ, ∀ b ∈ Bor X.Ψ r, ∀ z : V (nd X), ‖z‖ ≤ R → ψ (lact γ (rmul (cpt X x z) b)) = η z)
    (h0 : ∀ y, (¬ ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, ∃ z : V (nd X), ‖z‖ ≤ ρ ∧ y = lact γ (rmul (cpt X x z) b)) →
      ψ y = 0)
    (hloc : ∀ y ∈ X.dom, (¬ ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, ∃ z : V (nd X), ‖z‖ ≤ ρ ∧
      y = lact γ (rmul (cpt X x z) b)) → ∀ᶠ y' in 𝓝 y, ¬ ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, ∃ z : V (nd X),
        ‖z‖ ≤ ρ ∧ y' = lact γ (rmul (cpt X x z) b))
    {y : Frame X.Ψ r} (hy : y ∈ X.dom) :
    (∀ᶠ y' in 𝓝 y, ψ y' = 0) ∨
    ∃ (γ : GL (Fin r) E) (zOf : Frame X.Ψ r → V (nd X)) (U : Set (Frame X.Ψ r)),
      IsOpen U ∧ lact γ⁻¹ y ∈ U ∧ DifferentiableOn ℂ zOf U ∧
      ∀ᶠ y' in 𝓝 y, ψ y' = η (zOf (lact γ⁻¹ y')) := by
  by_cases hS : ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, ∃ z : V (nd X), ‖z‖ ≤ ρ ∧ y = lact γ (rmul (cpt X x z) b)
  · right
    obtain ⟨γ, hγ, b, hb, z, hz, rfl⟩ := hS
    obtain ⟨Δ, zOf, bOf, hΔ, -, hzd, -, hsplit, hinv⟩ := lu_holds r X x hx
    have hUo : IsOpen {w | w ∈ X.dom ∧ Δ w ≠ 0} :=
      (IW.isOpen_dom X).inter (isOpen_ne_fun hΔ.continuous continuous_const)
    have hzO : z ∈ OmF X x := hR z (hz.trans hρR.le)
    have hmem : lact γ⁻¹ (lact γ (rmul (cpt X x z) b)) ∈ {w | w ∈ X.dom ∧ Δ w ≠ 0} := by
      rw [lact_inv_lact]
      exact ⟨OntoS.dom_rmul X hzO hb, (hinv z hzO b hb).1⟩
    refine ⟨γ, zOf, _, hUo, hmem, hzd, ?_⟩
    have hcont : ContinuousAt (fun y' => lact γ⁻¹ y') (lact γ (rmul (cpt X x z) b)) :=
      (KU.cont_lact X γ⁻¹).continuousAt
    have hU' : ∀ᶠ y' in 𝓝 (lact γ (rmul (cpt X x z) b)), lact γ⁻¹ y' ∈ {w | w ∈ X.dom ∧ Δ w ≠ 0} :=
      hcont.preimage_mem_nhds (hUo.mem_nhds hmem)
    have hzc : ContinuousAt (fun y' => zOf (lact γ⁻¹ y')) (lact γ (rmul (cpt X x z) b)) :=
      ContinuousAt.comp (f := fun y' => lact γ⁻¹ y')
        ((hzd.differentiableAt (hUo.mem_nhds hmem)).continuousAt) hcont
    have hval : zOf (lact γ⁻¹ (lact γ (rmul (cpt X x z) b))) = z := by
      rw [lact_inv_lact]; exact (hinv z hzO b hb).2.1
    have h2 : ‖zOf (lact γ⁻¹ (lact γ (rmul (cpt X x z) b)))‖ < R := by
      rw [hval]; exact lt_of_le_of_lt hz hρR
    have hnear : ∀ᶠ y' in 𝓝 (lact γ (rmul (cpt X x z) b)), ‖zOf (lact γ⁻¹ y')‖ < R :=
      hzc.norm.eventually_lt continuousAt_const h2
    filter_upwards [hU', hnear] with y' hy'U hy'n
    obtain ⟨hy'd, hy'Δ⟩ := hy'U
    obtain ⟨-, hbO, heq⟩ := hsplit _ hy'd hy'Δ
    have hy' : y' = lact γ (rmul (cpt X x (zOf (lact γ⁻¹ y'))) (bOf (lact γ⁻¹ y'))) := by
      rw [← heq, lact_lact_inv]
    conv_lhs => rw [hy']
    exact hψ γ hγ _ hbO _ hy'n.le
  · left
    filter_upwards [hloc y hy hS] with y' hy'
    exact h0 y' hy'

end GlobalTheory.PeakWeightSmooth

namespace GlobalTheory.PeakWeightSmooth

theorem measurable_and_contDiffOn : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (x : Frame X.Ψ r) (ρ R : ℝ) (η : V (nd X) → ℝ) (ψ : Frame X.Ψ r → ℝ), IsOrth X x → ρ < R → (∀ z : V (nd X), ‖z‖ ≤ R → z ∈ OmF X x) → ContDiff ℝ ∞ η → (∀ γ ∈ X.Γ, ∀ b ∈ Bor X.Ψ r, ∀ z : V (nd X), ‖z‖ ≤ R → ψ (lact γ (rmul (cpt X x z) b)) = η z) → (∀ y, (¬ ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, ∃ z : V (nd X), ‖z‖ ≤ ρ ∧ y = lact γ (rmul (cpt X x z) b)) → ψ y = 0) → (∀ y ∈ X.dom, (¬ ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, ∃ z : V (nd X), ‖z‖ ≤ ρ ∧ y = lact γ (rmul (cpt X x z) b)) → ∀ᶠ y' in 𝓝 y, ¬ ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, ∃ z : V (nd X), ‖z‖ ≤ ρ ∧ y' = lact γ (rmul (cpt X x z) b)) → Measurable ψ ∧ ContDiffOn ℝ ∞ (fun w => ψ (cpt X x w)) (OmF X x) := by
  intro E _ _ _ r X x ρ R η ψ hx hρR hR hη hψ h0 hloc
  classical
  have hS_dom : ∀ y, (∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, ∃ z : V (nd X), ‖z‖ ≤ ρ ∧
      y = lact γ (rmul (cpt X x z) b)) → y ∈ X.dom := by
    rintro y ⟨γ, hγ, b, hb, z, hz, rfl⟩
    exact KU.lact_dom X hγ (OntoS.dom_rmul X (hR z (hz.trans hρR.le)) hb)
  have hcont : ∀ y ∈ X.dom, ContinuousAt ψ y := by
    intro y hy
    rcases local_form X x hx ρ R η ψ hρR hR hψ h0 hloc hy with h | ⟨γ, zOf, U, hUo, hyU, hzd, hev⟩
    · exact (continuousAt_const (y := (0 : ℝ))).congr (h.mono fun _ h => h.symm)
    · have : ContinuousAt (fun y' => η (zOf (lact γ⁻¹ y'))) y :=
        hη.continuous.continuousAt.comp (((hzd.differentiableAt (hUo.mem_nhds hyU)).continuousAt).comp
          (KU.cont_lact X γ⁻¹).continuousAt)
      exact this.congr (hev.mono fun _ h => h.symm)
  have hzero : ∀ y, y ∉ X.dom → ψ y = 0 := fun y hy => h0 y (fun h => hy (hS_dom y h))
  constructor
  · have heq : ψ = X.dom.piecewise ψ (fun _ => 0) := by
      funext y
      by_cases hy : y ∈ X.dom
      · simp [Set.piecewise, hy]
      · simp [Set.piecewise, hy, hzero y hy]
    rw [heq]
    exact ContinuousOn.measurable_piecewise (fun y hy => (hcont y hy).continuousWithinAt)
      continuousOn_const (IW.isOpen_dom X).measurableSet
  · intro w hw
    refine ContDiffAt.contDiffWithinAt ?_
    have hc : ContinuousAt (cpt X x) w := (IW.cpt_diff X x).continuous.continuousAt
    rcases local_form X x hx ρ R η ψ hρR hR hψ h0 hloc (y := cpt X x w) hw with
      h | ⟨γ, zOf, U, hUo, hyU, hzd, hev⟩
    · have h' : ∀ᶠ w' in 𝓝 w, ψ (cpt X x w') = 0 := hc.eventually h
      exact (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq h'
    · have hg : Differentiable ℂ (fun w' => lact γ⁻¹ (cpt X x w')) := by
        have e : (fun w' => lact γ⁻¹ (cpt X x w')) = cpt X (lact γ⁻¹ x) := by
          funext w'; rw [KU.cpt_lact]
        rw [e]; exact IW.cpt_diff X _
      have hN : (fun w' => lact γ⁻¹ (cpt X x w')) ⁻¹' U ∈ 𝓝 w :=
        hg.continuous.continuousAt.preimage_mem_nhds (hUo.mem_nhds hyU)
      have hΦd : DifferentiableOn ℂ (fun w' => zOf (lact γ⁻¹ (cpt X x w')))
          ((fun w' => lact γ⁻¹ (cpt X x w')) ⁻¹' U) :=
        hzd.comp hg.differentiableOn (fun _ h => h)
      have hΦ : ContDiffAt ℂ ∞ (fun w' => zOf (lact γ⁻¹ (cpt X x w'))) w :=
        GlobalTheory.SCV.contDiffAt_of_differentiableOn hΦd hN _
      have hev' : ∀ᶠ w' in 𝓝 w, ψ (cpt X x w') = η (zOf (lact γ⁻¹ (cpt X x w'))) := hc.eventually hev
      exact ((hη.contDiffAt).comp w (hΦ.restrict_scalars ℝ)).congr_of_eventuallyEq hev'

end GlobalTheory.PeakWeightSmooth
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvariantMeasureChartBallOrthonormalLowerBound
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory
open scoped ENNReal

namespace GlobalTheory.BallVol

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem spread_zero (X : Data E r) (hr : 0 < r) (τ : X.Ψ) : X.spread (fun _ _ => 0) τ = 0 := by
  haveI : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
  simp [Data.spread]

theorem nd_le (X : Data E r) : nd X ≤ X.Ψ.card * (r * r) := by
  unfold nd
  rw [Fintype.card_prod, Fintype.card_coe]
  refine Nat.mul_le_mul_left _ ?_
  calc Fintype.card {p : Fin r × Fin r // p.2 < p.1} ≤ Fintype.card (Fin r × Fin r) :=
        Fintype.card_subtype_le _
    _ = r * r := by simp

theorem nat_bound (f r n : ℕ) (hf : 1 ≤ f) (hr : 1 ≤ r) (hn : n ≤ f * (r * r)) :
    2 * n * (200 * r ^ 3 * f) + n * n + 1 ≤ 402 * (f * r) ^ 8 := by
  set a := f * r with ha
  have ha1 : 1 ≤ a := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
  have hra : r ≤ a := by rw [ha]; exact Nat.le_mul_of_pos_left r (by omega)
  have hfa : f ≤ a := by rw [ha]; exact Nat.le_mul_of_pos_right f (by omega)
  have hna : n ≤ a * a := hn.trans (by rw [ha, ← Nat.mul_assoc]; exact Nat.mul_le_mul_left _ hra)
  have h1 : 2 * n * (200 * r ^ 3 * f) ≤ 400 * a ^ 8 := by
    have e : 2 * n * (200 * r ^ 3 * f) ≤ 400 * ((a * a) * (a ^ 3 * a)) := by
      have := Nat.mul_le_mul hna (Nat.mul_le_mul (Nat.pow_le_pow_left hra 3) hfa)
      nlinarith
    refine e.trans (Nat.mul_le_mul_left _ ?_)
    calc a * a * (a ^ 3 * a) = a ^ 6 := by ring
      _ ≤ a ^ 8 := Nat.pow_le_pow_right ha1 (by norm_num)
  have h2 : n * n ≤ a ^ 8 := by
    calc n * n ≤ (a * a) * (a * a) := Nat.mul_le_mul hna hna
      _ = a ^ 4 := by ring
      _ ≤ a ^ 8 := Nat.pow_le_pow_right ha1 (by norm_num)
  have h3 : 1 ≤ a ^ 8 := Nat.one_le_pow _ _ ha1
  omega

theorem real_bound (f r n : ℕ) (hf : 1 ≤ f) (hr : 1 ≤ r) (hn : n ≤ f * (r * r)) :
    Real.exp (-(402 * ((f : ℝ) * r) ^ 8)) ≤ Real.exp (-(1 / 10)) *
      (Real.pi ^ n * (1 / (200 * (r : ℝ) ^ 3 * f)) ^ (2 * n) / n.factorial) := by
  set K : ℝ := 200 * (r : ℝ) ^ 3 * f with hK
  have hf' : (1 : ℝ) ≤ f := by exact_mod_cast hf
  have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hK1 : 1 ≤ K := by
    have : (1 : ℝ) ≤ (r : ℝ) ^ 3 := one_le_pow₀ hr'
    rw [hK]; nlinarith
  have hKpos : 0 < K := by linarith

  have hδ : Real.exp (-K) ≤ 1 / K := by
    rw [Real.exp_neg, one_div]
    exact inv_anti₀ hKpos (by linarith [Real.add_one_le_exp K])
  have hδn : Real.exp (-(2 * n * K)) ≤ (1 / K) ^ (2 * n) := by
    calc Real.exp (-(2 * n * K)) = Real.exp (-K) ^ (2 * n) := by
          rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
      _ ≤ (1 / K) ^ (2 * n) := pow_le_pow_left₀ (Real.exp_pos _).le hδ _
  have hpi : (1 : ℝ) ≤ Real.pi ^ n := one_le_pow₀ (by linarith [Real.pi_gt_three])
  have hfac : (n.factorial : ℝ) ≤ Real.exp ((n : ℝ) * n) := by
    have h1 : (n.factorial : ℝ) ≤ (n : ℝ) ^ n := by exact_mod_cast Nat.factorial_le_pow n
    have h2 : (n : ℝ) ^ n ≤ Real.exp n ^ n :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) (by linarith [Real.add_one_le_exp (n : ℝ)]) _
    rw [← Real.exp_nat_mul] at h2
    exact h1.trans h2
  have hfpos : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  have hN := nat_bound f r n hf hr hn
  have hNR : 2 * (n : ℝ) * K + n * n + 1 ≤ 402 * ((f : ℝ) * r) ^ 8 := by
    rw [hK]; exact_mod_cast hN
  have hmain : Real.exp (-(402 * ((f : ℝ) * r) ^ 8)) ≤
      Real.exp (-(1 / 10)) * (Real.exp (-(2 * n * K)) / Real.exp ((n : ℝ) * n)) := by
    rw [← Real.exp_sub, ← Real.exp_add]
    exact Real.exp_le_exp.2 (by linarith)
  refine hmain.trans (mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le)
  calc Real.exp (-(2 * n * K)) / Real.exp ((n : ℝ) * n)
      ≤ (1 / K) ^ (2 * n) / n.factorial := div_le_div₀ (by positivity) hδn hfpos hfac
    _ ≤ Real.pi ^ n * (1 / K) ^ (2 * n) / n.factorial := by
        gcongr
        exact le_mul_of_one_le_left (by positivity) hpi

theorem ballvol : ∃ C : ℝ, 0 ≤ C ∧ ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ)
    (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r) (x : ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r), 0 < X.p0 → X.p0 < r →
    ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x →
    ENNReal.ofReal (Real.exp (-(C * ((X.Ψ.card : ℝ) * r) ^ 8))) ≤
      ReciprocityTheory.ChartRestriction.G.AR.Up.muF X x (Metric.ball (0 : ReciprocityTheory.L2DbarEstimates.V (ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X))
        (1 / (100 * (r : ℝ) ^ 2)) ∩ ReciprocityTheory.ChartRestriction.G.AR.Up.OmF X x) := by
  refine ⟨402, by norm_num, ?_⟩
  intro E _ _ _ r X x hp0 hpr hx
  have hr : 0 < r := lt_of_le_of_lt (Nat.zero_le _) hpr
  set la : Wt X.Ψ r := fun _ _ => 0 with hla
  set w : ℝ := ∑ τ, X.spread la τ with hw
  have hw0 : w = 0 := Finset.sum_eq_zero fun τ _ => spread_zero X hr τ
  have hcard : ((X.Ψ.card : ℕ) : ℝ) = fdeg E := by
    rw [← Fintype.card_coe, QuadraticCoefficientForms.card_Psi X]
  have hf1 : (1 : ℝ) ≤ (X.Ψ.card : ℝ) := by rw [hcard]; exact one_le_field_half_degree
  have hf1n : 1 ≤ X.Ψ.card := by exact_mod_cast hf1
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  set δ := GlobalTheory.LevGeo.chartRad E r w with hδ
  have hδeq : δ = 1 / (200 * (r : ℝ) ^ 3 * (X.Ψ.card : ℝ)) := by
    rw [hδ, GlobalTheory.LevGeo.chartRad, hw0, zero_add, hcard]
  have hδpos : 0 < δ := by rw [hδeq]; positivity
  have hδle : δ ≤ 1 / (100 * (r : ℝ) ^ 2) := by
    rw [hδeq]
    refine one_div_le_one_div_of_le (by positivity) ?_
    have h3 : (r : ℝ) ^ 2 ≤ (r : ℝ) ^ 3 := pow_le_pow_right₀ hr1 (by norm_num)
    have h4 : (r : ℝ) ^ 3 ≤ (r : ℝ) ^ 3 * (X.Ψ.card : ℝ) := le_mul_of_one_le_right (by positivity) hf1
    nlinarith
  have hnear : ∀ z : V (nd X), ‖z‖ ≤ δ → cpt X x z ∈ X.dom ∧
      Real.exp (-(1 / 20)) ≤ X.nfac la (cpt X x z) ^ 2 ∧ Real.exp (-(1 / 10)) ≤ densF X x z :=
    fun z hz => GlobalTheory.ChartNearOne.chart_near_one E r X la w x hr hx le_rfl z hz
  have hsubO : Metric.ball (0 : V (nd X)) δ ⊆ OmF X x := fun z hz =>
    (hnear z (le_of_lt (mem_ball_zero_iff.1 hz))).1
  have hsub : Metric.ball (0 : V (nd X)) δ ⊆
      Metric.ball 0 (1 / (100 * (r : ℝ) ^ 2)) ∩ OmF X x := fun z hz =>
    ⟨Metric.ball_subset_ball hδle hz, hsubO hz⟩
  refine le_trans ?_ (measure_mono hsub)
  have hm : muF X x (Metric.ball 0 δ) =
      ∫⁻ z in Metric.ball (0 : V (nd X)) δ, ENNReal.ofReal (densF X x z) := by
    rw [muF, withDensity_apply _ measurableSet_ball, Measure.restrict_restrict measurableSet_ball,
      Set.inter_eq_left.2 hsubO]
  rw [hm]
  have hn := nd_le X
  calc ENNReal.ofReal (Real.exp (-(402 * ((X.Ψ.card : ℝ) * r) ^ 8)))
      ≤ ENNReal.ofReal (Real.exp (-(1 / 10))) * volume (Metric.ball (0 : V (nd X)) δ) := by
        rw [GlobalTheory.volume_ball_euclideanSpace_complex 0 hδpos, Fintype.card_fin,
          ← ENNReal.ofReal_mul (Real.exp_pos _).le]
        refine ENNReal.ofReal_le_ofReal ?_
        rw [hδeq]
        exact real_bound X.Ψ.card r (nd X) hf1n hr hn
    _ = ∫⁻ z in Metric.ball (0 : V (nd X)) δ, ENNReal.ofReal (Real.exp (-(1 / 10))) := by
        rw [setLIntegral_const, mul_comm]
    _ ≤ _ := setLIntegral_mono' measurableSet_ball fun z hz =>
        ENNReal.ofReal_le_ofReal (hnear z (le_of_lt (mem_ball_zero_iff.1 hz))).2.2

end

end GlobalTheory.BallVol
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCompactClosureZpowersIffBoundedEntriesStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.UnitLemma GlobalTheory.InertUnitOrb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCompact_closure_zpowers_iff_bounded_entries : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] (w : Pl E) (n : ℕ) (H : Subgroup (GLw n w)), IsClosed (H : Set (GLw n w)) → ∀ s : H, IsCompact (closure (Subgroup.zpowers s : Set H)) ↔ ∃ m : ℤ, ∀ k : ℤ, ∀ i j, Valued.v ((((s ^ k : H) : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j) ≤ WithZero.exp m := by
  first | exact @GlobalTheory.PowersCompact.isCompact_closure_zpowers_iff | exact GlobalTheory.PowersCompact.isCompact_closure_zpowers_iff | (intros; apply GlobalTheory.PowersCompact.isCompact_closure_zpowers_iff <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCosocleComp
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.JHMult

noncomputable section

namespace GlobalTheory.CosocleComp

variable {G H V W : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

def subrepOfComp (ρ : Representation ℂ G V) (s : H →* G) (hs : Function.Surjective s) :
    Subrepresentation (ρ.comp s : Representation ℂ H V) ≃o Subrepresentation ρ where
  toFun S := ⟨S.toSubmodule, fun g v hv => by
    obtain ⟨h, rfl⟩ := hs g
    exact S.apply_mem_toSubmodule h hv⟩
  invFun S := ⟨S.toSubmodule, fun h _ hv => S.apply_mem_toSubmodule (s h) hv⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

theorem isIrreducible_comp {ρ : Representation ℂ G V} {s : H →* G} (hs : Function.Surjective s)
    (h : ρ.IsIrreducible) : Representation.IsIrreducible (ρ.comp s : Representation ℂ H V) :=
  (subrepOfComp ρ s hs).isSimpleOrder_iff.2 h

theorem isCosocle_comp : ∀ (G H V W : Type) [Group G] [Group H] [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] (σ : Representation ℂ G W) (π : Representation ℂ G V) (s : H →* G), Function.Surjective s →
    IsCosocle σ π → IsCosocle (σ.comp s) (π.comp s) := by
  intro G H V W _ _ _ _ _ _ σ π s hs h
  obtain ⟨hi, f, hf, hS⟩ := h
  let f' : Representation.IntertwiningMap (π.comp s : Representation ℂ H V) (σ.comp s : Representation ℂ H W) := ⟨f.toLinearMap, fun g => f.isIntertwining' (s g)⟩
  refine ⟨isIrreducible_comp hs hi, f', hf, fun S hS' => ?_⟩
  have h1 := hS (subrepOfComp π s hs S) ((OrderIso.isCoatom_iff (subrepOfComp π s hs) S).2 hS')
  have h2 := congrArg Subrepresentation.toSubmodule h1
  have inj : Function.Injective (Subrepresentation.toSubmodule (ρ := (π.comp s : Representation ℂ H V))) := by
    rintro ⟨a, _⟩ ⟨b, _⟩ rfl; rfl
  exact inj h2

end GlobalTheory.CosocleComp
end
end

