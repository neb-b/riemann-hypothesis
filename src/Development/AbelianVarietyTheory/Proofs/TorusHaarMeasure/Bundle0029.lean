module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0019
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.FundSetPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OmFConnPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OntoStatementPfC
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfH
public import ReciprocityTheory.L2DbarEstimates.LeviForms.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0028
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0016
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0013
public import ReciprocityTheory.L2DbarEstimates.WeakHolomorphy.Bundle0003

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ChangeDifferentiableOn
section
namespace GlobalTheory.MeasInv

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates
  MeasureTheory Topology ReciprocityTheory.ChartRestriction.G.AR.Up.ExtFPf
open scoped ContDiff ENNReal Matrix

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : Data E r}

theorem differentiable_cpt (x0 : Frame X.Ψ r) : Differentiable ℂ (cpt X x0) :=
  differentiable_pi.2 fun τ => differentiable_pi.2 fun a => differentiable_pi.2 fun b =>
    (IW.cpt_entry_cd X x0 τ a b).differentiable (by simp)

def overlap (x0 : Frame X.Ψ r) {x1 : Frame X.Ψ r} (D1 : LUData X x1) : Set (V (nd X)) :=
  {z | z ∈ OmF X x0 ∧ D1.Δ (cpt X x0 z) ≠ 0}

variable {x0 x1 : Frame X.Ψ r}

theorem isOpen_overlap (D1 : LUData X x1) : IsOpen (overlap x0 D1) :=
  (isOpen_cell D1).preimage (differentiable_cpt x0).continuous

theorem overlap_nonempty (h0 : IsOrth X x0) (D0 : LUData X x0) (D1 : LUData X x1) :
    ∃ z ∈ OmF X x0, D1.Δ (cpt X x0 z) ≠ 0 := by
  have hz0 := IW.zero_mem_OmF X x0 h0
  have hc : cpt X x0 0 ∈ cell D0 := ⟨hz0, (cpt_cell D0 hz0).1⟩
  obtain ⟨ε, hε, hB⟩ := Metric.isOpen_iff.1 (isOpen_cell D0) _ hc
  obtain ⟨y, hy, hy1⟩ := D1.dense _ hz0 ε hε
  obtain ⟨hyd, hy0⟩ := hB hy
  obtain ⟨hz, hb, he⟩ := D0.split y hyd hy0
  exact ⟨_, hz, cell_of_rmul D1 hz hb (he ▸ hy1)⟩

theorem overlap_ae_eq (h0 : IsOrth X x0) (D0 : LUData X x0) (D1 : LUData X x1) :
    overlap x0 D1 =ᵐ[volume] OmF X x0 := by
  have hnull := OntoD.null_zero (g := fun z => D1.Δ (cpt X x0 z)) (ExF.isOpen_OmF X x0)
    (OmFConnStatement_holds r X x0 h0)
    (D1.hΔ.comp (differentiable_cpt x0)).differentiableOn (overlap_nonempty h0 D0 D1)
  rw [ae_eq_set]
  refine ⟨?_, ?_⟩
  · rw [Set.diff_eq_empty.2 (by exact fun z hz => hz.1)]
    exact measure_empty
  · refine measure_mono_null (fun z hz => ?_) hnull
    refine Set.mem_inter hz.1 ?_
    by_contra h
    exact hz.2 ⟨hz.1, h⟩

theorem lintegral_muF_overlap (h0 : IsOrth X x0) (D0 : LUData X x0) (D1 : LUData X x1)
    (g : V (nd X) → ℝ≥0∞) :
    ∫⁻ z, g z ∂muF X x0 = ∫⁻ z in overlap x0 D1, ENNReal.ofReal (densF X x0 z) * g z := by
  unfold muF
  rw [lintegral_withDensity_eq_lintegral_mul_non_measurable _
    (OntoC.measurable_densF X x0) (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top),
    Measure.restrict_congr_set (overlap_ae_eq h0 D0 D1)]
  rfl

theorem change_mem (D0 : LUData X x0) (D1 : LUData X x1) {z : V (nd X)} (hz : z ∈ overlap x0 D1) :
    D1.zOf (cpt X x0 z) ∈ overlap x1 D0 ∧ D0.zOf (cpt X x1 (D1.zOf (cpt X x0 z))) = z := by
  obtain ⟨hw, hb, he⟩ := D1.split _ hz.1 hz.2
  obtain ⟨hΔ, hzz, -⟩ := cpt_cell D0 hz.1
  have h1 : D0.Δ (cpt X x1 (D1.zOf (cpt X x0 z))) ≠ 0 := cell_of_rmul D0 hw hb (he ▸ hΔ)
  refine ⟨⟨hw, h1⟩, ?_⟩
  rw [← (cell_rmul D0 hw h1 hb).2.1, ← he, hzz]

theorem change_image (D0 : LUData X x0) (D1 : LUData X x1) :
    (fun z => D1.zOf (cpt X x0 z)) '' overlap x0 D1 = overlap x1 D0 := by
  ext w
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact (change_mem D0 D1 hz).1
  · intro hw
    exact ⟨_, (change_mem D1 D0 hw).1, (change_mem D1 D0 hw).2⟩

theorem change_injOn (D0 : LUData X x0) (D1 : LUData X x1) :
    Set.InjOn (fun z => D1.zOf (cpt X x0 z)) (overlap x0 D1) := by
  intro z hz z' hz' h
  have h' : D1.zOf (cpt X x0 z) = D1.zOf (cpt X x0 z') := h
  rw [← (change_mem D0 D1 hz).2, h', (change_mem D0 D1 hz').2]

theorem change_differentiableOn (D1 : LUData X x1) :
    DifferentiableOn ℂ (fun z => D1.zOf (cpt X x0 z)) (overlap x0 D1) :=
  D1.hz.comp (differentiable_cpt x0).differentiableOn fun _ hz => hz

theorem densF_mul_nfac_sq (h0 : IsOrth X x0) {z : V (nd X)} (hz : z ∈ OmF X x0) :
    densF X x0 z * X.nfac (kapW X) (cpt X x0 z) ^ 2 = 1 := by
  have hN := FlowCoefficientBounds.nfac_pos X hz (kapW X)
  have hd := OntoB.densF_pos hz
  have h := IW.phla_kapW_cpt X x0 h0 hz
  unfold phla at h
  rw [← Real.exp_log hd, ← h, ← Real.exp_log (pow_pos hN 2), ← Real.exp_add, Real.log_pow]
  simp

theorem densF_change (hN : NfacRmulStatement (E := E)) (h0 : IsOrth X x0) (h1 : IsOrth X x1)
    {z w : V (nd X)} (hz : z ∈ OmF X x0) (hw : w ∈ OmF X x1) {b : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r)
    (he : cpt X x0 z = rmul (cpt X x1 w) b) :
    densF X x0 z = ‖bchar (kapW X) b‖ ^ 2 * densF X x1 w := by
  have e0 := densF_mul_nfac_sq h0 hz
  have e1 := densF_mul_nfac_sq h1 hw
  rw [he, hN r X (kapW X) _ hw b hb] at e0
  have hc : ‖bchar (kapW X) b‖ ≠ 0 := by
    intro h
    rw [h] at e0
    simp at e0
  calc densF X x0 z = densF X x0 z * (densF X x1 w * X.nfac (kapW X) (cpt X x1 w) ^ 2) := by
        rw [e1, mul_one]
    _ = ‖bchar (kapW X) b‖ ^ 2 * densF X x1 w *
        (densF X x0 z * (‖bchar (kapW X) b‖⁻¹ * X.nfac (kapW X) (cpt X x1 w)) ^ 2) := by
        field_simp
    _ = _ := by rw [e0, mul_one]

end

end GlobalTheory.MeasInv

namespace GlobalTheory

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates
  MeasureTheory Topology ReciprocityTheory.ChartRestriction.G.AR.Up.ExtFPf MeasInv
open scoped ContDiff ENNReal Matrix

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem measInv_of_jacobian (hK : KapGGStatement (E := E))
    (hN : NfacRmulStatement (E := E) ∧ NfacLactStatement (E := E) ∧ PnormInvStatement (E := E)) :
    MeasInvStatement (E := E) := by
  intro r X x0 x1 h0 h1 φ hφ hinv
  obtain ⟨D0⟩ := luData_of lu_holds X x0 h0
  obtain ⟨D1⟩ := luData_of lu_holds X x1 h1
  have hmeas : Measurable fun w => ENNReal.ofReal (densF X x1 w) * φ (cpt X x1 w) :=
    (OntoC.measurable_densF X x1).mul (hφ.comp (differentiable_cpt x1).continuous.measurable)
  rw [lintegral_muF_overlap h0 D0 D1, lintegral_muF_overlap h1 D1 D0, ← change_image D0 D1,
    I.cov (nd X) _ _ _ (isOpen_overlap D1) (change_differentiableOn D1) (change_injOn D0 D1) hmeas]
  have hdet := hK r X x0 x1 1 _ _ (fun z => D1.bOf (cpt X x0 z)) (isOpen_overlap D1)
    (change_differentiableOn D1) fun z hz => by
      obtain ⟨-, hb, he⟩ := D1.split _ hz.1 hz.2
      exact ⟨hz.1, hb, by rw [FundSetPf.lact_one]; exact he⟩
  refine setLIntegral_congr_fun (isOpen_overlap D1).measurableSet fun z hz => ?_
  obtain ⟨hw, hb, he⟩ := D1.split _ hz.1 hz.2
  have hd : LinearMap.det (fderiv ℂ (fun z => D1.zOf (cpt X x0 z)) z : V (nd X) →ₗ[ℂ] V (nd X)) =
      bchar (kapW X) (D1.bOf (cpt X x0 z)) := hdet z hz
  have hφe : φ (cpt X x0 z) = φ (cpt X x1 (D1.zOf (cpt X x0 z))) := by
    rw [← hinv _ hw _ hb, ← he]
  beta_reduce
  rw [hd, densF_change hN.1 h0 h1 hz.1 hw hb he, ENNReal.ofReal_mul (by positivity), hφe, mul_assoc]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.CompactModLatticeStabiliserOfLeFirstMinimumStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
theorem _root_.GlobalTheory.T.compact_mod_latticeStabiliser_of_le_firstMinimum : (∀ (r : ℕ) (X : Data E r) (H : Subgroup (X.Ψ → GL (Fin r) ℂ)), (∀ g, g ∈ H ↔ X.IsUnitaryC fun τ => (g τ : Matrix (Fin r) (Fin r) ℂ)) → ∀ x0, IsOrth X x0 → ∀ ε : ℝ, 0 < ε → ∃ K : Set H, IsCompact K ∧ ∀ g : H, ε ≤ X.la1 (X.lmulC (fun τ => (((g : H) : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ)) x0) → ∃ u : H, (∃ γ : GL (Fin r) E, IsUStab X.Gm X.Λ γ ∧ ∀ τ : X.Ψ, ((((u : H) : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) = (γ : Matrix (Fin r) (Fin r) E).map τ.1) ∧ ∃ k ∈ K, g = u * k) := by
  first | exact @GlobalTheory.FiniteCovolume.exists_unitaryStab_mul_compact_of_le_firstMinimum | exact GlobalTheory.FiniteCovolume.exists_unitaryStab_mul_compact_of_le_firstMinimum | (intros; apply GlobalTheory.FiniteCovolume.exists_unitaryStab_mul_compact_of_le_firstMinimum <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.NormLeSqrtWeightNearOrthonormal
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory

theorem norm_le_sqrt_of_lintegral_ball_le (n : ℕ) (z : V n) {R a : ℝ} (hR : 0 < R) (ha : 0 ≤ a)
    (u : V n → ℂ) (hu : DifferentiableOn ℂ u (Metric.ball z R)) {I : ℝ≥0∞} (hI : I < ⊤)
    (h : ∫⁻ w in Metric.ball z R, ENNReal.ofReal (‖u w‖ ^ 2) ≤ ENNReal.ofReal a * I) :
    ‖u z‖ ≤ Real.sqrt (I.toReal / (volume (Metric.ball (0 : V n) R)).toReal) * Real.sqrt a := by
  have hmv := ReciprocityTheory.L2DbarEstimates.C.mv n z R u (fun _ => 1) hu measurable_const
  simp only [mul_one, setLIntegral_const, one_mul] at hmv
  have hint : ∫⁻ w in Metric.ball z R, ENNReal.ofReal (‖u w‖ ^ 2) =
      ∫⁻ w in Metric.ball z R, ‖u w‖ₑ ^ 2 := by
    refine setLIntegral_congr_fun measurableSet_ball fun w _ => ?_
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
  rw [hint] at h
  have hvol : volume (Metric.ball z R) = volume (Metric.ball (0 : V n) R) :=
    Measure.addHaar_ball_center volume z R
  have hpos : 0 < volume (Metric.ball (0 : V n) R) := Metric.measure_ball_pos volume 0 hR
  have hfin : volume (Metric.ball (0 : V n) R) < ⊤ := measure_ball_lt_top
  have hle : ‖u z‖ₑ ^ 2 * volume (Metric.ball (0 : V n) R) ≤ ENNReal.ofReal a * I := by
    rw [← hvol]; exact hmv.trans h
  have hreal : ‖u z‖ ^ 2 * (volume (Metric.ball (0 : V n) R)).toReal ≤ a * I.toReal := by
    have := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hI.ne) hle
    rwa [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_pow, toReal_enorm,
      ENNReal.toReal_ofReal ha] at this
  have hvr : 0 < (volume (Metric.ball (0 : V n) R)).toReal := ENNReal.toReal_pos hpos.ne' hfin.ne
  have hsq : ‖u z‖ ^ 2 ≤ I.toReal / (volume (Metric.ball (0 : V n) R)).toReal * a := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hvr, mul_comm I.toReal]
    exact hreal
  rw [← Real.sqrt_mul (div_nonneg ENNReal.toReal_nonneg hvr.le), ← Real.sqrt_sq (norm_nonneg (u z))]
  exact Real.sqrt_le_sqrt hsq

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem norm_le_sqrt_weight_near_orthonormal :
    (MeasInvStatement (E := E)) → (∀ (r : ℕ) (X : Data E r) (la : Wt X.Ψ r), ∃ ρ c C : ℝ, 0 < ρ ∧ 0 < c ∧ ∀ x, IsOrth X x → ∀ z : V (nd X), ‖z‖ < ρ → cpt X x z ∈ X.dom ∧ c ≤ densF X x z ∧ densF X x z ≤ C ∧ c ≤ X.nfac la (cpt X x z) ∧ X.nfac la (cpt X x z) ≤ C) → (NfacRmulStatement (E := E) ∧ NfacLactStatement (E := E) ∧ PnormInvStatement (E := E)) → (∀ (r : ℕ) (X : Data E r) (x0 : Frame X.Ψ r), IsOrth X x0 → ∀ (la : Wt X.Ψ r) (W : Frame X.Ψ r → ℝ≥0∞) (bb : ℝ) (κ : Frame X.Ψ r → ℝ), (Measurable κ ∧ (∀ x ∈ X.dom, 0 < κ x ∧ κ x ≤ 1) ∧ (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, κ (rmul x b) = κ x) ∧ (∀ z ∈ OmF X x0, κ (cpt X x0 z) = kaF X x0 bb z) ∧ (∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ x ∈ X.dom, ∑' γ : X.Γ, ENNReal.ofReal (Real.sqrt (κ (lact γ.1 x))) ≤ C) ∧ ∃ ρ C : ℝ, 0 < ρ ∧ ∀ x, IsOrth X x → ∀ z : V (nd X), ‖z‖ < ρ → κ (cpt X x z) ≤ C * κ x) → IsMetricW X la W → WLower X la W → ∀ (F : V (nd X) → ℂ) (P : Frame X.Ψ r → ℂ), InAt X x0 W bb F → IsBEq X la P → (∀ z ∈ OmF X x0, P (cpt X x0 z) = F z) → ∃ ρ C : ℝ, 0 < ρ ∧ ∀ x, IsOrth X x → ∀ z : V (nd X), ‖z‖ < ρ → cpt X x z ∈ X.dom ∧ ‖P (cpt X x z)‖ ≤ C * Real.sqrt (κ x)) := by
  intro hMI hU _ r X x0 hx0 la W bb κ hκ hW hWL F P hIn hP hPF
  obtain ⟨hκm, hκpos, hκB, hκF, -, ρ2, C2, hρ2, hκC⟩ := hκ
  obtain ⟨ρ1, c1, C1, hρ1, hc1, hUx⟩ := hU r X la
  obtain ⟨cW, hcW, hWlow⟩ := hWL
  unfold InAt at hIn
  classical

  obtain ⟨φ, hφeq⟩ : ∃ φ : Frame X.Ψ r → ℝ≥0∞,
      φ = ReciprocityTheory.ChartRestriction.G.AR.Up.OntoE.phiF X P fun y => W y / ENNReal.ofReal (κ y) := ⟨_, rfl⟩
  have hφm : Measurable φ := by
    rw [hφeq]
    exact ReciprocityTheory.ChartRestriction.G.AR.Up.OntoE.phiF_meas X hP.1.continuousOn (hW.1.div hκm.ennreal_ofReal)
  have hφdom : ∀ y ∈ X.dom, φ y = ENNReal.ofReal (‖P y‖ ^ 2) * (W y / ENNReal.ofReal (κ y)) := by
    intro y hy
    rw [hφeq]
    exact ReciprocityTheory.ChartRestriction.G.AR.Up.OntoE.phiF_dom X P _ hy
  have hφB : ∀ y ∈ X.dom, ∀ b ∈ Bor X.Ψ r, φ (rmul y b) = φ y := by
    intro y hy b hb
    rw [hφdom _ (ReciprocityTheory.ChartRestriction.G.AR.Up.OntoS.dom_rmul X hy hb), hφdom y hy, hP.2 y hy b hb,
      hW.2.1 y hy b hb, hκB y hy b hb, norm_mul, mul_pow, ENNReal.ofReal_mul (sq_nonneg _)]
    have h0 : ENNReal.ofReal (‖bchar la b‖ ^ 2) ≠ 0 :=
      (ENNReal.ofReal_pos.2 (pow_pos (norm_pos_iff.2
        (ReciprocityTheory.ChartRestriction.G.AR.Up.OntoE.bchar_ne X la hb)) 2)).ne'
    simp only [div_eq_mul_inv]
    rw [show ∀ t a w k : ℝ≥0∞, t * a * (w * t⁻¹ * k⁻¹) = (t * t⁻¹) * (a * (w * k⁻¹)) from
      fun t a w k => by ring, ENNReal.mul_inv_cancel h0 ENNReal.ofReal_ne_top, one_mul]

  have hOm : MeasurableSet (OmF X x0) := by
    have h := ReciprocityTheory.ChartRestriction.G.AR.Up.OntoC.isOpen_nonvanishingLocus X x0 (g1 := fun _ => (1 : ℂ))
      (differentiableOn_const 1)
    have he : ReciprocityTheory.ChartRestriction.G.AR.Up.OntoC.Om1 X x0 (fun _ => (1 : ℂ)) = OmF X x0 := by
      ext z
      simp [ReciprocityTheory.ChartRestriction.G.AR.Up.OntoC.Om1]
    exact (he ▸ h).measurableSet
  have hae : ∀ᵐ z ∂muF X x0, z ∈ OmF X x0 := by
    unfold muF
    exact (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem hOm)
  obtain ⟨I, hIeq⟩ : ∃ I, I = ∫⁻ z, φ (cpt X x0 z) ∂muF X x0 := ⟨_, rfl⟩
  have hI : I < ⊤ := by
    rw [hIeq]
    refine lt_of_eq_of_lt (lintegral_congr_ae ?_) hIn
    filter_upwards [hae] with z hz
    have hka : 0 < kaF X x0 bb z := Real.exp_pos _
    rw [hφdom _ hz, hPF z hz, hκF z hz, ENNReal.ofReal_div_of_pos hka]
    simp only [div_eq_mul_inv]
    ring

  obtain ⟨C2', hC2'eq⟩ : ∃ C2' : ℝ, C2' = max C2 1 := ⟨_, rfl⟩
  have hC2' : 0 < C2' := hC2'eq ▸ lt_of_lt_of_le one_pos (le_max_right _ _)
  obtain ⟨m, hmeq⟩ : ∃ m : ℝ, m = cW * c1 ^ 2 := ⟨_, rfl⟩
  have hm : 0 < m := hmeq ▸ mul_pos hcW (pow_pos hc1 2)
  obtain ⟨A, hAeq⟩ : ∃ A : ℝ, A = C2' / (m * c1) := ⟨_, rfl⟩
  have hA : 0 < A := hAeq ▸ div_pos hC2' (mul_pos hm hc1)
  obtain ⟨ρ, hρeq⟩ : ∃ ρ : ℝ, ρ = min ρ1 ρ2 / 2 := ⟨_, rfl⟩
  have hρ : 0 < ρ := hρeq ▸ half_pos (lt_min hρ1 hρ2)
  have h2ρ : 2 * ρ = min ρ1 ρ2 := by rw [hρeq]; ring
  have hρ1' : 2 * ρ ≤ ρ1 := h2ρ ▸ min_le_left _ _
  have hρ2' : 2 * ρ ≤ ρ2 := h2ρ ▸ min_le_right _ _
  refine ⟨ρ, Real.sqrt (I.toReal / (volume (Metric.ball (0 : V (nd X)) ρ)).toReal) * Real.sqrt A,
    hρ, ?_⟩
  intro x hx z hz
  have hxdom : x ∈ X.dom := ReciprocityTheory.ChartRestriction.G.AR.Up.IW.orth_mem_dom X x hx
  have hκx : 0 < κ x := (hκpos x hxdom).1
  have hsmall : ∀ w : V (nd X), ‖w‖ < 2 * ρ → cpt X x w ∈ X.dom ∧ c1 ≤ densF X x w ∧
      c1 ≤ X.nfac la (cpt X x w) ∧ κ (cpt X x w) ≤ C2' * κ x := by
    intro w hw
    obtain ⟨h1, h2, -, h4, -⟩ := hUx x hx w (by linarith)
    refine ⟨h1, h2, h4, ?_⟩
    exact (hκC x hx w (by linarith)).trans
      (mul_le_mul_of_nonneg_right (hC2'eq ▸ le_max_left _ _) hκx.le)
  refine ⟨(hsmall z (by linarith)).1, ?_⟩
  have hIx : ∫⁻ w, φ (cpt X x w) ∂muF X x = I := by
    rw [hIeq]
    exact (hMI r X x0 x hx0 hx φ hφm hφB).symm
  have hball : ∀ w ∈ Metric.ball z ρ, ‖w‖ < 2 * ρ := by
    intro w hw
    rw [Metric.mem_ball, dist_eq_norm] at hw
    have := norm_sub_norm_le w z
    linarith

  have hcpt : Differentiable ℂ (fun w : V (nd X) => cpt X x w) := by
    refine differentiable_pi.2 fun τ => differentiable_pi.2 fun a => differentiable_pi.2 fun b => ?_
    exact (ReciprocityTheory.ChartRestriction.G.AR.Up.IW.cpt_entry_cd X x τ a b).differentiable (by simp)
  have hu : DifferentiableOn ℂ (fun w => P (cpt X x w)) (Metric.ball z ρ) :=
    hP.1.comp hcpt.differentiableOn fun w hw => (hsmall w (hball w hw)).1

  have hpt : ∀ w ∈ Metric.ball z ρ, ENNReal.ofReal (‖P (cpt X x w)‖ ^ 2) ≤
      ENNReal.ofReal (A * κ x) * (ENNReal.ofReal (densF X x w) * φ (cpt X x w)) := by
    intro w hw
    obtain ⟨hd, hdens, hnf, hκw⟩ := hsmall w (hball w hw)
    have hκw0 : 0 < κ (cpt X x w) := (hκpos _ hd).1
    have hn0 : 0 < X.nfac la (cpt X x w) := lt_of_lt_of_le hc1 hnf
    have hWw : ENNReal.ofReal m ≤ W (cpt X x w) := by
      refine le_trans (ENNReal.ofReal_le_ofReal ?_) (hWlow _ hd)
      have he : -phla X la (cpt X x w) = Real.log (X.nfac la (cpt X x w) ^ 2) := by
        rw [phla, Real.log_pow]
        push_cast
        ring
      rw [he, Real.exp_log (pow_pos hn0 2), hmeq]
      have := hc1.le
      gcongr
    have key : ENNReal.ofReal (A * κ x) *
        (ENNReal.ofReal c1 * (ENNReal.ofReal m / ENNReal.ofReal (C2' * κ x))) = 1 := by
      rw [← ENNReal.ofReal_div_of_pos (mul_pos hC2' hκx), ← ENNReal.ofReal_mul hc1.le,
        ← ENNReal.ofReal_mul (mul_pos hA hκx).le, ← ENNReal.ofReal_one]
      congr 1
      rw [hAeq]
      have := hm.ne'
      have := hc1.ne'
      have := hC2'.ne'
      have := hκx.ne'
      field_simp
    calc ENNReal.ofReal (‖P (cpt X x w)‖ ^ 2)
        = ENNReal.ofReal (A * κ x) *
            (ENNReal.ofReal c1 * (ENNReal.ofReal m / ENNReal.ofReal (C2' * κ x))) *
            ENNReal.ofReal (‖P (cpt X x w)‖ ^ 2) := by rw [key, one_mul]
      _ ≤ ENNReal.ofReal (A * κ x) *
            (ENNReal.ofReal (densF X x w) * (W (cpt X x w) / ENNReal.ofReal (κ (cpt X x w)))) *
            ENNReal.ofReal (‖P (cpt X x w)‖ ^ 2) := by gcongr
      _ = ENNReal.ofReal (A * κ x) * (ENNReal.ofReal (densF X x w) * φ (cpt X x w)) := by
        rw [hφdom _ hd]
        ring
  have hint : ∫⁻ w in Metric.ball z ρ, ENNReal.ofReal (‖P (cpt X x w)‖ ^ 2) ≤
      ENNReal.ofReal (A * κ x) * I := by
    calc ∫⁻ w in Metric.ball z ρ, ENNReal.ofReal (‖P (cpt X x w)‖ ^ 2)
        ≤ ∫⁻ w in Metric.ball z ρ,
            ENNReal.ofReal (A * κ x) * (ENNReal.ofReal (densF X x w) * φ (cpt X x w)) :=
          setLIntegral_mono' measurableSet_ball hpt
      _ = ENNReal.ofReal (A * κ x) *
            ∫⁻ w in Metric.ball z ρ, ENNReal.ofReal (densF X x w) * φ (cpt X x w) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ = ENNReal.ofReal (A * κ x) * ∫⁻ w in Metric.ball z ρ, φ (cpt X x w) ∂muF X x := by
          rw [ReciprocityTheory.ChartRestriction.G.AR.Up.OntoC.setLIntegral_muF X x measurableSet_ball
            (fun w hw => (hsmall w (hball w hw)).1)]
      _ ≤ ENNReal.ofReal (A * κ x) * I := by
          gcongr
          rw [← hIx]
          exact setLIntegral_le_lintegral _ _
  have hfin := norm_le_sqrt_of_lintegral_ball_le (nd X) z hρ (mul_pos hA hκx).le
    (fun w => P (cpt X x w)) hu hI hint
  rw [Real.sqrt_mul hA.le, ← mul_assoc] at hfin
  exact hfin

end GlobalTheory
end

