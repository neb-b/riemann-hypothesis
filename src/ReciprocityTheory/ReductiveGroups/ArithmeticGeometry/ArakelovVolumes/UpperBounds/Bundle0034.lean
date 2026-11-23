module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0032
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfH
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfG
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfM
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0033

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfB
section
namespace ReciprocityTheory.ChartRestriction.G.AR.Up

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def KronHolStatement : Prop :=
  ∀ (r : ℕ) (X : Data E r) (Xa : ArchInM X) (Fl : FlatM X Xa), PropDisc X →
    (∃ bb m : ℝ, 4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 < bb ∧ bb < m ∧
      ∀ x0, IsOrth X x0 → ∀ z ∈ OmF X x0, ∀ ξ : Fin (nd X) → ℂ,
        m * leviRh X x0 z ξ ≤ leviO X x0 (phla X Xa.Fp) z ξ - leviDens X x0 z ξ -
          (nd X : ℝ) * leviO X x0 (phla X Xa.L) z ξ) →
    (∀ x0, IsOrth X x0 → ∀ z ∈ OmF X x0, ∀ ξ : Fin (nd X) → ℂ, 0 ≤ leviO X x0 (phla X Xa.L) z ξ) →
    ∀ j, ∃ (x0 : Frame X.Ψ r) (W : Frame X.Ψ r → ℝ≥0∞) (bb : ℝ) (F : V (nd X) → ℂ)
      (P : Frame X.Ψ r → ℂ) (γ0 : GL (Fin r) E),
      IsOrth X x0 ∧ IsMetricW X Xa.Fp W ∧ WLower X Xa.Fp W ∧ 4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 < bb ∧
      DifferentiableOn ℂ F (OmF X x0) ∧ InAt X x0 W bb F ∧ IsBEq X Xa.Fp P ∧
      (∀ z ∈ OmF X x0, P (cpt X x0 z) = F z) ∧ γ0 ∈ X.Γ ∧ P (lact γ0 (Fl.xs j)) ≠ 0 ∧
      ∀ γ ∈ X.Γ, ∀ j', (γ ≠ γ0 ∨ j' ≠ j) → P (lact γ (Fl.xs j')) = 0

theorem chi_ne_zero {r : ℕ} (X : Data E r) (la : Wt X.Ψ r) {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ) :
    X.χ la γ ≠ 0 := by
  obtain ⟨n, hn, h⟩ := X.χ_fin la
  intro h0
  have h1 := h γ hγ
  rw [h0, zero_pow hn.ne'] at h1
  exact zero_ne_one h1

theorem poin_single {r : ℕ} (X : Data E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (x : Frame X.Ψ r)
    {γ0 : GL (Fin r) E} (h0 : γ0 ∈ X.Γ) (hz : ∀ γ ∈ X.Γ, γ ≠ γ0 → P (lact γ x) = 0) :
    poin X la P x = (X.χ la γ0)⁻¹ * P (lact γ0 x) := by
  unfold poin
  rw [tsum_eq_single ⟨γ0, h0⟩ fun γ hγ => by
    rw [hz γ.1 γ.2 fun h => hγ (Subtype.ext h), mul_zero]]

theorem poin_zero {r : ℕ} (X : Data E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (x : Frame X.Ψ r)
    (hz : ∀ γ ∈ X.Γ, P (lact γ x) = 0) : poin X la P x = 0 := by
  unfold poin
  exact (tsum_congr fun γ => by rw [hz γ.1 γ.2, mul_zero]).trans tsum_zero

theorem leviO_zero {r : ℕ} (X : Data E r) (x0 : Frame X.Ψ r) (z : V (nd X)) (ξ : Fin (nd X) → ℂ) :
    leviO X x0 (fun _ => (0 : ℝ)) z ξ = 0 := by
  have h0 : ∀ k, wdb (nd X) k (fun _ : V (nd X) => (0 : ℂ)) = fun _ => 0 := fun k => by
    funext y
    simp [wdb]
  simp [leviO, leviM, leviV, wd, h0]

theorem kronHol_of_psi (hK : KronHolPsiStatement (E := E)) : KronHolStatement (E := E) := by
  intro r X Xa Fl hPD hm hL j
  obtain ⟨bb, m, hb1, hb2, hb3⟩ := hm

  obtain ⟨η, hη, hpos⟩ := Xa.posF
  have hmarg : ∃ bb m : ℝ, 4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 < bb ∧ bb < m ∧
      ∀ x0, IsOrth X x0 → ∀ z ∈ OmF X x0, ∀ ξ : Fin (nd X) → ℂ,
        m * leviRh X x0 z ξ ≤ leviO X x0 (phla X Xa.Fp) z ξ - leviDens X x0 z ξ -
          (nd X : ℝ) * leviO X x0 (phla X Xa.L) z ξ + leviO X x0 (fun _ => (0 : ℝ)) z ξ :=
    ⟨bb, m, hb1, hb2, fun x0 hx z hz ξ => by
      rw [ReciprocityTheory.ChartRestriction.G.AR.Up.leviO_zero, add_zero]
      exact hb3 x0 hx z hz ξ⟩
  have heta : ∃ η : ℝ, 0 < η ∧ ∀ x0, IsOrth X x0 → ∀ z ∈ OmF X x0, ∀ ξ : Fin (nd X) → ℂ,
      2 * η * leviO X x0 (phla X Xa.L) z ξ ≤ leviO X x0 (phla X Xa.Fp) z ξ - leviDens X x0 z ξ -
        (nd X : ℝ) * leviO X x0 (phla X Xa.L) z ξ + leviO X x0 (fun _ => (0 : ℝ)) z ξ :=
    ⟨η, hη, fun x0 hx z hz ξ => by
      rw [ReciprocityTheory.ChartRestriction.G.AR.Up.leviO_zero, add_zero]
      have h1 := hpos 0 le_rfl (by rw [zero_mul]; positivity) x0
        (ReciprocityTheory.ChartRestriction.G.AR.Up.IW.orth_mem_dom X x0 hx) z hz ξ
      rw [zero_mul, zero_mul, sub_zero, ReciprocityTheory.ChartRestriction.G.AR.Up.IW.leviM_comb X x0 hx hz] at h1
      exact h1⟩
  obtain ⟨x0, W, bb', F, P, γ0, h1, h2, h3, -, h5, h6, h7, h8, h9, h10, h11, h12⟩ :=
    hK r X Xa Fl hPD (fun _ => 0) (fun _ _ _ _ _ _ => rfl) (fun _ _ => contDiffOn_const)
      ⟨0, fun _ _ => le_rfl⟩ hmarg heta hL j
  exact ⟨x0, W, bb', F, P, γ0, h1, h2, h3, h5, h6, h7, h8, h9, h10, h11, h12⟩

theorem interp_of (hP : PoinStatement (E := E)) (hK' : KronHolPsiStatement (E := E)) :
    InterpStatement (E := E) := by
  intro r X Xa Fl hPD hm hL hSS
  have hK := ReciprocityTheory.ChartRestriction.G.AR.Up.kronHol_of_psi hK'
  refine ReciprocityTheory.ChartRestriction.G.AR.Up.interp_of_kron X Xa.Fp Fl.xs fun j => ?_
  obtain ⟨x0, W, bb, F, P, γ0, hO, hW, hWL, hbb, hF, hIn, hBE, hPF, hγ0, hne, hzero⟩ :=
    hK r X Xa Fl hPD hm hL j

  have hIn' : InAt X x0 W bb (fun z => X.χ Xa.Fp γ0 / P (lact γ0 (Fl.xs j)) * F z) := by
    unfold InAt at hIn ⊢
    have h1 : ∀ z, ENNReal.ofReal (‖X.χ Xa.Fp γ0 / P (lact γ0 (Fl.xs j)) * F z‖ ^ 2 / kaF X x0 bb z) *
        W (cpt X x0 z) = ENNReal.ofReal (‖X.χ Xa.Fp γ0 / P (lact γ0 (Fl.xs j))‖ ^ 2) *
          (ENNReal.ofReal (‖F z‖ ^ 2 / kaF X x0 bb z) * W (cpt X x0 z)) := fun z => by
      rw [norm_mul, mul_pow, mul_div_assoc, ENNReal.ofReal_mul (by positivity), mul_assoc]
    simp_rw [h1]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hIn
  have hBE' : IsBEq X Xa.Fp (fun x => X.χ Xa.Fp γ0 / P (lact γ0 (Fl.xs j)) * P x) :=
    ⟨(differentiableOn_const _).mul hBE.1, fun x hx b hb => by dsimp only; rw [hBE.2 x hx b hb]; ring⟩
  obtain ⟨-, hbdd, -⟩ := hP r X x0 hO hPD Xa.Fp W bb hW hWL hbb
    (fun z => X.χ Xa.Fp γ0 / P (lact γ0 (Fl.xs j)) * F z)
    (fun x => X.χ Xa.Fp γ0 / P (lact γ0 (Fl.xs j)) * P x)
    ((differentiableOn_const _).mul hF) hIn' hBE' fun z hz => by simp only [hPF z hz]
  refine ⟨_, ReciprocityTheory.ChartRestriction.G.AR.Up.ss_sub_ssgt0 X Xa.Fp (hSS _ hbdd), fun j' => ?_⟩
  split_ifs with hj
  · subst hj
    rw [ReciprocityTheory.ChartRestriction.G.AR.Up.poin_single X Xa.Fp _ (Fl.xs j') hγ0 fun γ hγ hγ' => by
      simp only [hzero γ hγ j' (Or.inl hγ'), mul_zero]]
    rw [div_mul_cancel₀ _ hne, inv_mul_cancel₀ (ReciprocityTheory.ChartRestriction.G.AR.Up.chi_ne_zero X Xa.Fp hγ0)]
  · exact ReciprocityTheory.ChartRestriction.G.AR.Up.poin_zero X Xa.Fp _ (Fl.xs j') fun γ hγ => by
      simp only [hzero γ hγ j' (Or.inr hj), mul_zero]

end

end ReciprocityTheory.ChartRestriction.G.AR.Up
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfN
section
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.IW

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Filter
  Metric
open scoped ContDiff ENNReal Matrix

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

theorem muF_lintegral (x0 : Frame X.Ψ r) (g : V (nd X) → ℝ≥0∞) :
    ∫⁻ z, g z ∂muF X x0 = ∫⁻ z in OmF X x0, ENNReal.ofReal (densF X x0 z) * g z := by
  unfold muF
  rw [lintegral_withDensity_eq_lintegral_mul_non_measurable _ (densF_meas X x0).ennreal_ofReal
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  rfl

theorem rhoF_split (x0 : Frame X.Ψ r) (Fp : Wt X.Ψ r) (ψ : Frame X.Ψ r → ℝ) (bb : ℝ) {z : V (nd X)}
    (hz : z ∈ OmF X x0) :
    rhoF X x0 Fp ψ bb z = densF X x0 z * (Real.exp (-(phla X Fp (cpt X x0 z) + ψ (cpt X x0 z))) /
      kaF X x0 bb z) := by
  unfold rhoF kaF
  rw [Real.exp_add, Real.exp_add, Real.exp_log (densF_pos X x0 hz), div_eq_mul_inv, ← Real.exp_neg,
    show -(-bb * rhF X x0 z) = bb * rhF X x0 z by ring]
  ring

theorem inAt_of (x0 : Frame X.Ψ r) (Fp : Wt X.Ψ r) (ψ : Frame X.Ψ r → ℝ) (bb : ℝ) (F : V (nd X) → ℂ)
    (hint : ∫⁻ z in OmF X x0, ENNReal.ofReal (‖F z‖ ^ 2 * rhoF X x0 Fp ψ bb z) < ⊤) :
    InAt X x0 (Wpsi X Fp ψ) bb F := by
  have hmeas : MeasurableSet (OmF X x0) := (ExF.isOpen_OmF X x0).measurableSet
  unfold InAt
  rw [muF_lintegral]
  refine lt_of_le_of_lt (lintegral_mono_ae ?_) hint
  filter_upwards [ae_restrict_mem hmeas] with z hz
  have hd := (densF_pos X x0 hz).le
  have hz' : cpt X x0 z ∈ X.dom := hz
  have hW : Wpsi X Fp ψ (cpt X x0 z) =
      ENNReal.ofReal (Real.exp (-(phla X Fp (cpt X x0 z) + ψ (cpt X x0 z)))) := by
    unfold Wpsi; rw [if_pos hz']
  have hk : 0 < kaF X x0 bb z := Real.exp_pos _
  rw [hW, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul hd,
    rhoF_split X x0 Fp ψ bb hz]
  apply le_of_eq
  congr 1
  ring

theorem extF_hyp (x0 : Frame X.Ψ r) (ho : IsOrth X x0) (Fp : Wt X.Ψ r) (ψ : Frame X.Ψ r → ℝ)
    (C0 : ℝ) (hψb : ∀ x ∈ X.dom, ψ x ≤ C0) (bb : ℝ) (hbb : 0 ≤ bb) (F : V (nd X) → ℂ)
    (hint : ∫⁻ z in OmF X x0, ENNReal.ofReal (‖F z‖ ^ 2 * rhoF X x0 Fp ψ bb z) < ⊤) :
    ∀ C : Set (Frame X.Ψ r), IsCompact C → C ⊆ X.dom →
      ∫⁻ z in sat X x0 C, ENNReal.ofReal (‖F z‖ ^ 2 * Real.exp (-phla X Fp (cpt X x0 z))) ∂muF X x0 < ⊤ := by
  intro C _ _
  have hmeas : MeasurableSet (OmF X x0) := (ExF.isOpen_OmF X x0).measurableSet
  refine lt_of_le_of_lt (setLIntegral_le_lintegral _ _) ?_
  rw [muF_lintegral]
  have hfin : ∫⁻ z in OmF X x0, ENNReal.ofReal (Real.exp C0) *
      ENNReal.ofReal (‖F z‖ ^ 2 * rhoF X x0 Fp ψ bb z) < ⊤ := by
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hint
  refine lt_of_le_of_lt (lintegral_mono_ae ?_) hfin
  filter_upwards [ae_restrict_mem hmeas] with z hz
  have hd := (densF_pos X x0 hz).le
  have hψ := hψb _ hz
  have hrh := ExF.rhF_nonneg X x0 ho hz
  rw [← ENNReal.ofReal_mul hd, ← ENNReal.ofReal_mul (Real.exp_pos _).le, rhoF_split X x0 Fp ψ bb hz]
  apply ENNReal.ofReal_le_ofReal
  have key : 1 ≤ Real.exp C0 * (Real.exp (-(phla X Fp (cpt X x0 z) + ψ (cpt X x0 z))) /
      kaF X x0 bb z) * Real.exp (phla X Fp (cpt X x0 z)) := by
    unfold kaF
    rw [div_eq_mul_inv, ← Real.exp_neg, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    apply Real.one_le_exp
    nlinarith [mul_nonneg hbb hrh]
  have he : Real.exp (phla X Fp (cpt X x0 z)) * Real.exp (-phla X Fp (cpt X x0 z)) = 1 := by
    rw [← Real.exp_add]; simp
  have hA : 0 ≤ ‖F z‖ ^ 2 := by positivity
  have hE : 0 ≤ Real.exp (-phla X Fp (cpt X x0 z)) := (Real.exp_pos _).le
  calc densF X x0 z * (‖F z‖ ^ 2 * Real.exp (-phla X Fp (cpt X x0 z)))
      = (densF X x0 z * ‖F z‖ ^ 2 * Real.exp (-phla X Fp (cpt X x0 z))) * 1 := by ring
    _ ≤ (densF X x0 z * ‖F z‖ ^ 2 * Real.exp (-phla X Fp (cpt X x0 z))) *
        (Real.exp C0 * (Real.exp (-(phla X Fp (cpt X x0 z) + ψ (cpt X x0 z))) / kaF X x0 bb z) *
          Real.exp (phla X Fp (cpt X x0 z))) :=
        mul_le_mul_of_nonneg_left key (mul_nonneg (mul_nonneg hd hA) hE)
    _ = Real.exp C0 * (‖F z‖ ^ 2 * (densF X x0 z * (Real.exp (-(phla X Fp (cpt X x0 z) +
          ψ (cpt X x0 z))) / kaF X x0 bb z))) *
          (Real.exp (phla X Fp (cpt X x0 z)) * Real.exp (-phla X Fp (cpt X x0 z))) := by ring
    _ = _ := by rw [he, mul_one]

theorem value_base (hV : VanishAtSStatement (E := E)) (x0 : Frame X.Ψ r) (ho : IsOrth X x0)
    (Xa : ArchInM X) (Fl : FlatM X Xa) (ψ : Frame X.Ψ r → ℝ)
    (hψs : ContDiffOn ℝ ∞ (fun z => ψ (cpt X x0 z)) (OmF X x0)) (bb : ℝ) (ε : ℝ) (hε : 0 < ε)
    (hball : closedBall (0 : V (nd X)) (2 * ε) ⊆ OmF X x0) (F : V (nd X) → ℂ)
    (hFd : DifferentiableOn ℂ F (OmF X x0))
    (hI : ∫⁻ y in OmF X x0, ENNReal.ofReal (‖HE.cut ε hε y - F y‖ ^ 2 *
          Real.exp (-psie X x0 Xa.Fp Xa.L ψ bb y) *
          HE.nsq (fun k z => Fl.s k (cpt X x0 z)) y ^ (-(nd X : ℝ))) < ⊤)
    (P : Frame X.Ψ r → ℂ) (hPF : ∀ z ∈ OmF X x0, P (cpt X x0 z) = F z)
    (hw : Fl.w0 x0 ≠ 0) (hs0 : ∀ k, Fl.s k x0 = 0)
    (hdet : (fderiv ℂ (fun z => sig X Fl.w0 Fl.s (cpt X x0 z)) 0).det ≠ 0) : P x0 = 1 := by
  have hn : 0 < nd X := by have := Xa.n_ge; omega
  have h0 : cpt X x0 0 ∈ X.dom := hball (mem_closedBall_self (by linarith))
  have hx0 : x0 ∈ X.dom := by rwa [cpt_zero] at h0
  have hsub2 : closedBall (0 : V (nd X)) ε ⊆ OmF X x0 :=
    fun z hz => hball (closedBall_subset_closedBall (by linarith) hz)
  have hsub : ball (0 : V (nd X)) ε ⊆ OmF X x0 := fun z hz => hsub2 (ball_subset_closedBall hz)
  have hu : DifferentiableOn ℂ (fun z => (fun x => P x - 1) (cpt X x0 z)) (ball 0 ε) :=
    ((hFd.mono hsub).sub_const 1).congr fun z hz => by
      show P (cpt X x0 z) - 1 = F z - 1
      rw [hPF z (hsub hz)]
  have hsd : ∀ k, DifferentiableOn ℂ (fun z => Fl.s k (cpt X x0 z)) (ball 0 ε) :=
    fun k => (comp_cpt_diffOn X (Fl.s_van k).1.1.1.1 x0).mono hsub
  have hwd : DifferentiableOn ℂ (fun z => Fl.w0 (cpt X x0 z)) (ball 0 ε) :=
    (comp_cpt_diffOn X Fl.weightForm_vanishes.1.1.1.1 x0).mono hsub
  have hcont : ContinuousOn (psie X x0 Xa.Fp Xa.L ψ bb) (closedBall 0 ε) := fun z hz =>
    (psie_cdAt X x0 ho Xa.Fp Xa.L ψ hψs bb (hsub2 hz)).continuousAt.continuousWithinAt
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : V (nd X)) ε).bddAbove_image hcont
  have hmeasB : MeasurableSet (ball (0 : V (nd X)) ε) := measurableSet_ball
  have hint : ∫⁻ z in ball (0 : V (nd X)) ε, ENNReal.ofReal (‖(fun x => P x - 1) (cpt X x0 z)‖ ^ 2 *
      (∑ k, ‖Fl.s k (cpt X x0 z)‖ ^ 2) ^ (-(nd X : ℝ))) < ⊤ := by
    have hfin : ∫⁻ y in OmF X x0, ENNReal.ofReal (Real.exp M) *
        ENNReal.ofReal (‖HE.cut ε hε y - F y‖ ^ 2 * Real.exp (-psie X x0 Xa.Fp Xa.L ψ bb y) *
          HE.nsq (fun k z => Fl.s k (cpt X x0 z)) y ^ (-(nd X : ℝ))) < ⊤ := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hI
    refine lt_of_le_of_lt ?_ hfin
    refine le_trans ?_ (lintegral_mono_set hsub)
    refine lintegral_mono_ae ?_
    filter_upwards [ae_restrict_mem hmeasB] with z hz
    have hzc : z ∈ closedBall (0 : V (nd X)) ε := ball_subset_closedBall hz
    have hcut : HE.cut ε hε z = 1 := by
      unfold HE.cut
      rw [(HE.bumpE ε hε).one_of_mem_closedBall hzc]
      simp
    have hnsq : HE.nsq (fun k z => Fl.s k (cpt X x0 z)) z = ∑ k, ‖Fl.s k (cpt X x0 z)‖ ^ 2 := by
      unfold HE.nsq
      simp [Complex.normSq_eq_norm_sq]
    have hpe : 1 ≤ Real.exp M * Real.exp (-psie X x0 Xa.Fp Xa.L ψ bb z) := by
      rw [← Real.exp_add]
      apply Real.one_le_exp
      have := hM ⟨z, hzc, rfl⟩
      linarith
    beta_reduce
    rw [hcut, hnsq, hPF z (hsub hz), ← ENNReal.ofReal_mul (Real.exp_pos _).le, norm_sub_rev (1 : ℂ) (F z)]
    apply ENNReal.ofReal_le_ofReal
    have hN : 0 ≤ (∑ k, ‖Fl.s k (cpt X x0 z)‖ ^ 2) ^ (-(nd X : ℝ)) :=
      Real.rpow_nonneg (Finset.sum_nonneg fun _ _ => by positivity) _
    have hA : 0 ≤ ‖F z - 1‖ ^ 2 := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hpe (mul_nonneg hA hN)]
  have key := hV r X x0 hn ho hx0 (fun x => P x - 1) Fl.w0 Fl.s ε hε hu hsd hwd hw hs0 hdet hint
  simpa [sub_eq_zero] using key

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.IW
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.PoinStatementPf
section
namespace ReciprocityTheory.ChartRestriction.G.AR.Up

open NumberField

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem poin_of_inputs (hLU : LUStatement (E := E)) (hS : PoinPf.SumBallStatement (E := E))
    (hF : PoinPf.FFStatement (E := E)) : PoinStatement (E := E) :=
  PoinPf.poin_of (PoinPf.loc_of (PoinPf.subMeanLoc_of hLU) hS)
    (PoinPf.ball_of PoinPf.subMean_holds hS) hF

theorem poin_holds : PoinStatement (E := E) :=
  poin_of_inputs lu_holds PoinPf.sumBall_holds PoinPf.ff_holds

end ReciprocityTheory.ChartRestriction.G.AR.Up
end

