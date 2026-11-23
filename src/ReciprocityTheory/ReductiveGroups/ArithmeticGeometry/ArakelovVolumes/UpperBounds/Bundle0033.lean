module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0031
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.PoinStatementPfH

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OntoStatementPf
section
namespace ReciprocityTheory.ChartRestriction.G.AR.Up

open NumberField Complex Matrix Topology Filter MeasureTheory Set ReciprocityTheory.ChartRestriction.G.FD
  ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates ReciprocityTheory.ChartRestriction.G.AR.Up.OntoB ReciprocityTheory.ChartRestriction.G.AR.Up.OntoH
  ReciprocityTheory.ChartRestriction.G.AR.Up.OntoI ReciprocityTheory.ChartRestriction.G.AR.Up.OntoJ
open scoped ComplexConjugate ContDiff ENNReal InnerProductSpace

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem onto_of (hPoin : PoinStatement (E := E)) (hExtF : ExtFStatement (E := E))
    (hGrad : RhGradFStatement (E := E)) (hExG : ExhaustGStatement (E := E))
    (hKa : KaUnfoldStatement (E := E)) (hPair : PairUnfoldStatement (E := E))
    (hBig : BigCellStatement (E := E)) (hConn : OmFConnStatement (E := E)) :
    OntoStatement (E := E) := by
  intro r X x0 hx0 hPD la W Ps g1 bb m hW hWL hbb4 hm hg1 hg1ne hPs hWPs hLev hSS FF hFF hfin
    f hf hfF
  obtain ⟨K, g, hg⟩ := hfin
  have hWm : Measurable W := hW.1
  have hPo := fun (F : V (nd X) → ℂ) (P : Frame X.Ψ r → ℂ)
      (hD : OntoJ.Dt X x0 W bb la F P) =>
    hPoin r X x0 hx0 hPD la W bb hW hWL hbb4 F P hD.1 hD.2.1 hD.2.2.1 hD.2.2.2
  have hae : ∀ᵐ z ∂(OntoI.nuF X x0 W FF), z ∈ FF := by
    have h1 : ∀ᵐ z ∂((muF X x0).restrict FF), z ∈ FF := ae_restrict_mem hFF.1
    first
      | exact (withDensity_absolutelyContinuous _ _).ae_le h1
      | (unfold OntoI.nuF; exact (withDensity_absolutelyContinuous _ _).ae_le h1)
  have hmemP : ∀ (F : V (nd X) → ℂ) (P : Frame X.Ψ r → ℂ), OntoJ.Dt X x0 W bb la F P →
      MemLp (fun z => poin X la P (cpt X x0 z)) 2 (OntoI.nuF X x0 W FF) := fun F P hD =>
    OntoI.memLp_of (r := r) (X := X) (x0 := x0) (W := W) (FF := FF) hWm
      (hPo F P hD).2.1.1.1.continuousOn ((hPo F P hD).2.2.1 FF hFF)
  have hmemf : MemLp (fun z => f (cpt X x0 z)) 2 (OntoI.nuF X x0 W FF) :=
    OntoI.memLp_of (r := r) (X := X) (x0 := x0) (W := W) (FF := FF) hWm
      hf.1.1.1.continuousOn hfF
  have hzero : MemLp (fun z => (0 : Frame X.Ψ r → ℂ) (cpt X x0 z)) 2 (OntoI.nuF X x0 W FF) := by
    refine (hmemP _ _ (OntoJ.Dt_zero X x0)).ae_eq (ae_of_all _ fun z => ?_)
    exact OntoI.poin_zero (r := r) (X := X) la _

  obtain ⟨M, hMmem⟩ : ∃ M : Submodule ℂ (Lp ℂ 2 (OntoI.nuF X x0 W FF)), ∀ v, v ∈ M ↔
      ∃ (F : V (nd X) → ℂ) (P : Frame X.Ψ r → ℂ) (hD : OntoJ.Dt X x0 W bb la F P),
        v = (hmemP F P hD).toLp _ := by
    refine ⟨{ carrier := {v | ∃ (F : V (nd X) → ℂ) (P : Frame X.Ψ r → ℂ)
                (hD : OntoJ.Dt X x0 W bb la F P), v = (hmemP F P hD).toLp _}
              add_mem' := by
                rintro _ _ ⟨F1, P1, hD1, rfl⟩ ⟨F2, P2, hD2, rfl⟩
                refine ⟨_, _, OntoJ.Dt_add (r := r) (X := X) (x0 := x0) hWm hD1 hD2, ?_⟩
                rw [← MemLp.toLp_add (hmemP F1 P1 hD1) (hmemP F2 P2 hD2)]
                refine MemLp.toLp_congr _ _ ?_
                filter_upwards [hae] with z hz
                have hx : cpt X x0 z ∈ X.dom := hFF.2.1 hz
                show poin X la P1 (cpt X x0 z) + poin X la P2 (cpt X x0 z) =
                  poin X la (fun y => P1 y + P2 y) (cpt X x0 z)
                exact (OntoI.poin_add (r := r) (X := X) la ((hPo F1 P1 hD1).1 _ hx)
                  ((hPo F2 P2 hD2).1 _ hx)).symm
              zero_mem' := ⟨fun _ => 0, fun _ => 0, OntoJ.Dt_zero X x0, by
                rw [← MemLp.toLp_zero hzero]
                exact MemLp.toLp_congr _ _
                  (ae_of_all _ fun z => (OntoI.poin_zero (r := r) (X := X) la (cpt X x0 z)).symm)⟩
              smul_mem' := by
                rintro a _ ⟨F, P, hD, rfl⟩
                refine ⟨_, _, OntoJ.Dt_smul (r := r) (X := X) (x0 := x0) a hD, ?_⟩
                rw [← MemLp.toLp_const_smul a (hmemP F P hD)]
                exact MemLp.toLp_congr _ _
                  (ae_of_all _ fun z => (OntoI.poin_smul (r := r) (X := X) la a P (cpt X x0 z)).symm) },
      fun v => Iff.rfl⟩

  obtain ⟨D2, hD2i⟩ : ∃ D2 : Submodule ℂ (Frame X.Ψ r → ℂ), ∀ h, h ∈ D2 ↔
      h ∈ Submodule.span ℂ (Set.range g) ∧
        MemLp (fun z => h (cpt X x0 z)) 2 (OntoI.nuF X x0 W FF) :=
    ⟨{ carrier := {h | h ∈ Submodule.span ℂ (Set.range g) ∧
          MemLp (fun z => h (cpt X x0 z)) 2 (OntoI.nuF X x0 W FF)}
       add_mem' := fun {a b} ha hb => ⟨Submodule.add_mem _ ha.1 hb.1, ha.2.add hb.2⟩
       zero_mem' := ⟨Submodule.zero_mem _, hzero⟩
       smul_mem' := fun c {h} hh => ⟨Submodule.smul_mem _ c hh.1, hh.2.const_smul c⟩ },
      fun h => Iff.rfl⟩
  have hD2m : ∀ h : D2, MemLp (fun z => (h : Frame X.Ψ r → ℂ) (cpt X x0 z)) 2
      (OntoI.nuF X x0 W FF) := fun h => ((hD2i h).1 h.2).2
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : D2 →ₗ[ℂ] Lp ℂ 2 (OntoI.nuF X x0 W FF), ∀ h : D2,
      Φ h = (hD2m h).toLp _ :=
    ⟨{ toFun := fun h => (hD2m h).toLp _
       map_add' := fun a b => MemLp.toLp_add (hD2m a) (hD2m b)
       map_smul' := fun c a => MemLp.toLp_const_smul c (hD2m a) }, fun h => rfl⟩
  have hMle : M ≤ LinearMap.range Φ := by
    intro v hv
    obtain ⟨F, P, hD, rfl⟩ := (hMmem v).1 hv
    obtain ⟨c, hc⟩ := hg _ (hSS _ (hPo F P hD).2.1) ((hPo F P hD).2.2.1 FF hFF)
    obtain ⟨h, hhD, hhx⟩ : ∃ h : Frame X.Ψ r → ℂ, h ∈ Submodule.span ℂ (Set.range g) ∧
        ∀ x, h x = ∑ i, c i * g i x :=
      ⟨∑ i, c i • g i, Submodule.sum_mem _ fun i _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self i)),
        fun x => by simp [Finset.sum_apply]⟩
    have hae2 : (fun z => h (cpt X x0 z)) =ᵐ[OntoI.nuF X x0 W FF]
        fun z => poin X la P (cpt X x0 z) := by
      filter_upwards [hae] with z hz
      rw [hhx, hc _ (hFF.2.1 hz)]
    have hmh : MemLp (fun z => h (cpt X x0 z)) 2 (OntoI.nuF X x0 W FF) :=
      (hmemP F P hD).ae_eq hae2.symm
    refine LinearMap.mem_range.2 ⟨⟨h, (hD2i h).2 ⟨hhD, hmh⟩⟩, ?_⟩
    rw [hΦ]
    exact MemLp.toLp_congr _ _ hae2
  haveI hfS : FiniteDimensional ℂ (Submodule.span ℂ (Set.range g)) := by
    first
      | exact FiniteDimensional.span_of_finite ℂ (Set.finite_range g)
      | exact FiniteDimensional.span_of_finite (Set.finite_range g)
      | exact Module.Finite.iff_fg.mpr (Submodule.fg_span (Set.finite_range g))
      | exact inferInstance
  have hD2le : D2 ≤ Submodule.span ℂ (Set.range g) := by
    intro h hh
    exact ((hD2i h).1 hh).1
  haveI hfD2 : FiniteDimensional ℂ D2 := by
    first
      | exact Submodule.finiteDimensional_of_le hD2le
      | exact Module.Finite.of_injective (Submodule.inclusion hD2le)
          (Submodule.inclusion_injective hD2le)
  haveI hfR : FiniteDimensional ℂ (LinearMap.range Φ) := by
    first
      | exact LinearMap.finiteDimensional_range Φ
      | exact inferInstance
  haveI hfM : FiniteDimensional ℂ M := by
    first
      | exact Submodule.finiteDimensional_of_le hMle
      | exact Module.Finite.of_injective (Submodule.inclusion hMle)
          (Submodule.inclusion_injective hMle)
  haveI : CompleteSpace M := by
    first
      | exact FiniteDimensional.complete ℂ M
      | exact inferInstance

  obtain ⟨y, hyM, w, hw, hvyw⟩ : ∃ y ∈ M, ∃ w ∈ M.orthogonal,
      hmemf.toLp _ = y + w := by
    first
      | exact Submodule.exists_add_mem_mem_orthogonal M _
      | exact Submodule.exists_add_mem_mem_orthogonal _
  obtain ⟨F, P, hD, rfl⟩ := (hMmem y).1 hyM
  have hmemf0 : MemLp (fun z => f (cpt X x0 z) - poin X la P (cpt X x0 z)) 2
      (OntoI.nuF X x0 W FF) := hmemf.sub (hmemP F P hD)
  have hwLp : w = hmemf0.toLp _ := by
    change w = (hmemf.sub (hmemP F P hD)).toLp _
    rw [MemLp.toLp_sub hmemf (hmemP F P hD), hvyw]
    abel
  have horth : ∀ (F' : V (nd X) → ℂ) (P' : Frame X.Ψ r → ℂ), DifferentiableOn ℂ F' (OmF X x0) →
      InAt X x0 W bb F' → IsBEq X la P' → (∀ z ∈ OmF X x0, P' (cpt X x0 z) = F' z) →
      ∫ z in FF, poin X la P' (cpt X x0 z) *
          (starRingEnd ℂ) (f (cpt X x0 z) - poin X la P (cpt X x0 z)) *
          ((W (cpt X x0 z)).toReal : ℂ) ∂muF X x0 = 0 := by
    intro F' P' h1 h2 h3 h4
    have hD' : OntoJ.Dt X x0 W bb la F' P' := ⟨h1, h2, h3, h4⟩
    have hmem' : (hmemP F' P' hD').toLp _ ∈ M :=
      (hMmem _).2 ⟨F', P', hD', rfl⟩
    have h0 : ⟪(hmemP F' P' hD').toLp _, w⟫_ℂ = 0 := by
      first
        | exact Submodule.inner_right_of_mem_orthogonal hmem' hw
        | exact (Submodule.mem_orthogonal M w).1 hw _ hmem'
    have h0' : ⟪w, (hmemP F' P' hD').toLp _⟫_ℂ = 0 := by
      first
        | exact inner_eq_zero_symm.1 h0
        | exact Submodule.inner_left_of_mem_orthogonal hmem' hw
    rw [hwLp,
      OntoI.inner_toLp (r := r) (X := X) (x0 := x0) (W := W) (FF := FF) hWm hmemf0
        (hmemP F' P' hD')] at h0'
    refine (integral_congr_ae ?_).trans h0'
    filter_upwards with z
    ring
  have hf0SS : (fun y => f y - poin X la P y) ∈ X.SS la :=
    hSS _ (OntoI.bdd_sub (r := r) (X := X) hf.1 (hPo F P hD).2.1)
  have hff0 : InFF X x0 W FF (fun y => f y - poin X la P y) := by
    have hcf : ContinuousOn (fun z => f (cpt X x0 z)) (OmF X x0) :=
      hf.1.1.1.continuousOn.comp
        ((OntoB.cd_cpt (r := r) (X := X) (x0 := x0)).continuous.continuousOn)
        (by intro z hz; exact hz)
    have h1 : AEMeasurable (fun z => ENNReal.ofReal (‖f (cpt X x0 z)‖ ^ 2 / (1 : ℝ))) (muF X x0) :=
      OntoH.aem_of (r := r) (X := X) (x0 := x0)
        (ENNReal.continuous_ofReal.comp_continuousOn ((hcf.norm.pow 2).div_const 1))
    have haem : AEMeasurable
        (fun z => ENNReal.ofReal (‖f (cpt X x0 z)‖ ^ 2 / (1 : ℝ)) * W (cpt X x0 z))
        ((muF X x0).restrict FF) :=
      (h1.mul (OntoH.measW (r := r) (X := X) (x0 := x0) hWm).aemeasurable).restrict
    have key := OntoI.lint_add_le (μ := (muF X x0).restrict FF) (a := fun z => f (cpt X x0 z))
      (b := fun z => -poin X la P (cpt X x0 z)) (k := fun _ => (1 : ℝ))
      (om := fun z => W (cpt X x0 z)) (fun _ => one_pos) haem
    simp only [div_one, norm_neg, ← sub_eq_add_neg] at key
    have hPF := (hPo F P hD).2.2.1 FF hFF
    show ∫⁻ z in FF, ENNReal.ofReal (‖f (cpt X x0 z) - poin X la P (cpt X x0 z)‖ ^ 2) *
      W (cpt X x0 z) ∂muF X x0 < ⊤
    refine lt_of_le_of_lt key (ENNReal.add_lt_top.2 ⟨?_, ?_⟩)
    · first
        | exact ENNReal.mul_lt_top (by simp) hfF
        | exact ENNReal.mul_lt_top (by simp) hfF.ne
    · first
        | exact ENNReal.mul_lt_top (by simp) hPF
        | exact ENNReal.mul_lt_top (by simp) hPF.ne
  have hvan := OntoH.vanish (r := r) (X := X) (x0 := x0) hExG hGrad hKa hPair hBig hConn hExtF
    hx0 hPD hW hWL hbb4 hm hg1 hg1ne hPs hWPs hLev hFF hf0SS hff0 horth
  obtain ⟨hD1, hD2, hD3, hD4⟩ := hD
  refine ⟨F, P, hD1, hD2, hD3, hD4, fun x hx => ?_⟩
  have hx0' := hvan x hx
  exact (sub_eq_zero.1 hx0').symm

end

end ReciprocityTheory.ChartRestriction.G.AR.Up
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.PoinStatementPfI
section
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Filter
open scoped ENNReal Matrix ComplexConjugate

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def psiF (X : Data E r) (x0 : Frame X.Ψ r) (bb : ℝ) (P : Frame X.Ψ r → ℂ) (W : Frame X.Ψ r → ℝ≥0∞)
    (y : Frame X.Ψ r) : ℝ≥0∞ :=
  ‖X.dom.indicator P y‖ₑ ^ 2 * W y / ENNReal.ofReal (kaY X x0 bb y)

theorem psiF_meas (X : Data E r) (x0 : Frame X.Ψ r) (bb : ℝ) {la : Wt X.Ψ r} {P : Frame X.Ψ r → ℂ}
    {W : Frame X.Ψ r → ℝ≥0∞} (hP : IsBEq X la P) (hW : IsMetricW X la W) :
    Measurable (psiF X x0 bb P W) := by
  have h1 : Measurable (X.dom.indicator P) :=
    ReciprocityTheory.ChartRestriction.G.AR.Up.PairUnfoldPf.meas_indC (X := X) hP.1.continuousOn
  unfold psiF
  exact ((h1.enorm.pow_const 2).mul hW.1).div (ENNReal.measurable_ofReal.comp (meas_kaY X x0 bb))

theorem psiF_rmul (X : Data E r) {x0 : Frame X.Ψ r} (hx0 : IsOrth X x0) (bb : ℝ) {la : Wt X.Ψ r}
    {P : Frame X.Ψ r → ℂ} {W : Frame X.Ψ r → ℝ≥0∞} (hP : IsBEq X la P) (hW : IsMetricW X la W) :
    ∀ y ∈ X.dom, ∀ b ∈ Bor X.Ψ r, psiF X x0 bb P W (rmul y b) = psiF X x0 bb P W y := by
  intro y hy b hb
  have hm : rmul y b ∈ X.dom := by
    first
      | exact OrthogonalFrameDomain.rmul_mem_dom X hy hb
      | exact ReciprocityTheory.ChartRestriction.G.FD.OrthogonalFrameDomain.rmul_mem_dom X hy hb
  unfold psiF
  rw [Set.indicator_of_mem hm, Set.indicator_of_mem hy, hP.2 y hy b hb, hW.2.1 y hy b hb,
    kaY_rmul X hx0 hy hb bb]
  congr 1
  rw [enorm_mul, mul_pow]
  have hne : ‖bchar la b‖ₑ ^ 2 ≠ 0 := pow_ne_zero _ (enorm_ne_zero.2 (bchar_ne X la hb))
  have htop : ‖bchar la b‖ₑ ^ 2 ≠ ⊤ := ENNReal.pow_ne_top enorm_ne_top
  have hof : ENNReal.ofReal (‖bchar la b‖ ^ 2) = ‖bchar la b‖ₑ ^ 2 := by
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]
  rw [hof, ENNReal.div_eq_inv_mul]
  calc ‖bchar la b‖ₑ ^ 2 * ‖P y‖ₑ ^ 2 * ((‖bchar la b‖ₑ ^ 2)⁻¹ * W y)
      = (‖bchar la b‖ₑ ^ 2 * (‖bchar la b‖ₑ ^ 2)⁻¹) * (‖P y‖ₑ ^ 2 * W y) := by ring
    _ = ‖P y‖ₑ ^ 2 * W y := by rw [ENNReal.mul_inv_cancel hne htop, one_mul]

theorem psiF_mul (X : Data E r) (x0 : Frame X.Ψ r) (bb : ℝ) (P : Frame X.Ψ r → ℂ)
    (W : Frame X.Ψ r → ℝ≥0∞) {y : Frame X.Ψ r} (hy : y ∈ X.dom) :
    psiF X x0 bb P W y * ENNReal.ofReal (kaY X x0 bb y) = ‖P y‖ₑ ^ 2 * W y := by
  unfold psiF
  rw [Set.indicator_of_mem hy, ENNReal.div_mul_cancel (ENNReal.ofReal_pos.2 (kaY_pos X x0 bb y)).ne'
    ENNReal.ofReal_ne_top]

theorem psiF_int (X : Data E r) {x0 : Frame X.Ψ r} (hx0 : IsOrth X x0) (bb : ℝ) {P : Frame X.Ψ r → ℂ}
    {W : Frame X.Ψ r → ℝ≥0∞} {F : V (nd X) → ℂ} (hPF : ∀ z ∈ OmF X x0, P (cpt X x0 z) = F z) :
    ∫⁻ z, psiF X x0 bb P W (cpt X x0 z) ∂muF X x0 =
      ∫⁻ z, ENNReal.ofReal (‖F z‖ ^ 2 / kaF X x0 bb z) * W (cpt X x0 z) ∂muF X x0 := by
  refine lintegral_congr_ae ?_
  filter_upwards [ExtFPf.ae_OmF] with z hz
  have hyd : cpt X x0 z ∈ X.dom := hz
  simp only [psiF, Set.indicator_of_mem hyd, hPF z hz, kaY_cpt X hx0]
  rw [ENNReal.ofReal_div_of_pos (by unfold kaF; exact Real.exp_pos _), ENNReal.ofReal_pow (norm_nonneg _),
    ofReal_norm, ENNReal.mul_div_right_comm]

theorem meas_densF' (X : Data E r) (x' : Frame X.Ψ r) :
    Measurable fun w => ENNReal.ofReal (densF X x' w) := by
  refine ENNReal.measurable_ofReal.comp ?_
  unfold densF
  refine Finset.measurable_prod _ fun τ _ => Finset.measurable_prod _ fun i _ => ?_
  have hc : Measurable fun z : V (nd X) => ‖dmin X.Gm (cpt X x' z) τ i.castSucc‖ ^ 2 :=
    (((cont_dmin X τ _).comp (cont_cpt' X x')).norm.pow 2).measurable
  have e : (fun z : V (nd X) => ‖dmin X.Gm (cpt X x' z) τ i.castSucc‖ ^ (-2 : ℤ)) =
      fun z => (‖dmin X.Gm (cpt X x' z) τ i.castSucc‖ ^ 2)⁻¹ := by
    funext z; rw [zpow_neg, zpow_ofNat]
  rw [e]; exact hc.inv

theorem kaY_half (X : Data E r) (x0 : Frame X.Ψ r) (bb : ℝ) (y : Frame X.Ψ r) :
    ENNReal.ofReal (kaY X x0 bb y) ^ (1 / 2 : ℝ) = ENNReal.ofReal (kaY X x0 (bb / 2) y) := by
  unfold kaY
  rw [ENNReal.ofReal_rpow_of_nonneg (Real.exp_pos _).le (by norm_num), ← Real.exp_mul]
  congr 2
  ring

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Filter
open scoped ENNReal Matrix ComplexConjugate

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem sumBall_holds : SumBallStatement (E := E) := by
  intro r X x0 la W bb F P H
  obtain ⟨hx0, hPD, hW, -, hbb, -, hA, hP, hPF⟩ := H
  classical
  have hbb0 : 0 ≤ bb := by
    have : 0 ≤ 4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 := by positivity
    linarith
  obtain ⟨ρ1, hρ1, hcomp⟩ := ka_comp X hx0 hbb0
  have e2 : ∀ᶠ w in 𝓝 (0 : V (nd X)), ∀ τ, ∀ i : Fin r, ‖lminor (Gw X w τ) i.castSucc‖ < 2 := by
    rw [Filter.eventually_all]; intro τ; rw [Filter.eventually_all]; intro i
    exact (cont_lminor X τ _).norm.continuousAt.eventually_lt continuousAt_const
      (by rw [norm_lminor_zero]; norm_num)
  obtain ⟨R2, hR2, hR2b⟩ := Metric.eventually_nhds_iff_ball.1 e2
  set ρ0 := min (min ρ1 R2) 1 with hρ0
  have hρ0pos : 0 < ρ0 := lt_min (lt_min hρ1 hR2) one_pos
  have hs : 2 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 < bb / 2 := by linarith
  obtain ⟨C2, hC2, hsum⟩ := kaSum X hx0 hPD hs
  set K := Real.exp (bb * (3 * X.Ψ.card * Real.log 2)) with hK
  set cd : ℝ := ∏ _τ : X.Ψ, ∏ _i : Fin r, (1 / 4 : ℝ) with hcd
  have hcd0 : 0 < cd := Finset.prod_pos fun _ _ => Finset.prod_pos fun _ _ => by norm_num
  set Nn := ∫⁻ z, ENNReal.ofReal (‖F z‖ ^ 2 / kaF X x0 bb z) * W (cpt X x0 z) ∂muF X x0 with hNn
  set c0 : ℝ≥0∞ := ENNReal.ofReal K * ENNReal.ofReal (1 / cd) * Nn with hc0
  have hc0t : c0 ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top) hA.ne
  have hψm := psiF_meas X x0 bb hP hW
  have hψB := psiF_rmul X hx0 bb hP hW
  refine ⟨ρ0, hρ0pos, min_le_right _ _, c0 ^ (1 / 2 : ℝ) * C2,
    ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hc0t) hC2, fun x hx hxo => ?_⟩
  have hI : ∀ γ : X.Γ, ∫⁻ w in Bset X x ρ0,
      ‖P (lact γ.1 (cpt X x w))‖ₑ ^ 2 * W (lact γ.1 (cpt X x w)) ≤
        c0 * ENNReal.ofReal (kaY X x0 bb (lact γ.1 x)) := by
    intro γ
    set x' := lact γ.1 x with hx'
    have hx'o : IsOrth X x' := PairUnfoldPf.isOrth_lact X γ.2 hxo
    have hcptl : ∀ w, lact γ.1 (cpt X x w) = cpt X x' w := fun w =>
      (PairUnfoldPf.cpt_lact X γ.1 x w).symm
    simp only [hcptl]
    have hdom : ∀ w ∈ Bset X x ρ0, cpt X x' w ∈ X.dom := fun w hw => by
      rw [← hcptl]; exact (PairUnfoldPf.lact_mem_dom_iff X γ.2 _).2 hw.2
    set A := ENNReal.ofReal K * ENNReal.ofReal (kaY X x0 bb x') * ENNReal.ofReal (1 / cd) with hAdef
    have hpt : ∀ w ∈ Bset X x ρ0, ‖P (cpt X x' w)‖ₑ ^ 2 * W (cpt X x' w) ≤
        A * (ENNReal.ofReal (densF X x' w) * psiF X x0 bb P W (cpt X x' w)) := by
      intro w hw
      have hyd := hdom w hw
      have hw1 : ‖w‖ < ρ1 := lt_of_lt_of_le hw.1 ((min_le_left _ _).trans (min_le_left _ _))
      have hw2 : w ∈ Metric.ball (0 : V (nd X)) R2 :=
        mem_ball_zero_iff.2 (lt_of_lt_of_le hw.1 ((min_le_left _ _).trans (min_le_right _ _)))
      have hka := hcomp x' hx'o w hw1
      have hdens : cd ≤ densF X x' w := by
        unfold densF
        refine Finset.prod_le_prod₀ (fun _ _ => by positivity) fun τ _ =>
          Finset.prod_le_prod₀ (fun _ _ => by norm_num) fun i _ => ?_
        rw [dmin_cpt_orth X hx'o]
        have h0 : 0 < ‖lminor (Gw X w τ) i.castSucc‖ := by
          rw [← dmin_cpt_orth X hx'o]; exact norm_pos_iff.2 (dmin_ne X hyd τ _)
        have h2 := hR2b w hw2 τ i
        rw [zpow_neg, zpow_ofNat, show (1 / 4 : ℝ) = ((2 : ℝ) ^ 2)⁻¹ by norm_num]
        exact inv_anti₀ (by positivity) (pow_le_pow_left₀ h0.le h2.le 2)
      have hden : 1 ≤ ENNReal.ofReal (1 / cd) * ENNReal.ofReal (densF X x' w) := by
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_one]
        refine ENNReal.ofReal_le_ofReal ?_
        rw [one_div_mul_eq_div, le_div_iff₀ hcd0]
        linarith
      have hkk : ENNReal.ofReal (kaY X x0 bb (cpt X x' w)) ≤
          ENNReal.ofReal K * ENNReal.ofReal (kaY X x0 bb x') := by
        rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]; exact ENNReal.ofReal_le_ofReal hka
      rw [← psiF_mul X x0 bb P W hyd]
      calc psiF X x0 bb P W (cpt X x' w) * ENNReal.ofReal (kaY X x0 bb (cpt X x' w))
          ≤ psiF X x0 bb P W (cpt X x' w) * (ENNReal.ofReal K * ENNReal.ofReal (kaY X x0 bb x')) :=
            mul_le_mul_of_nonneg_left hkk zero_le
        _ = psiF X x0 bb P W (cpt X x' w) * (ENNReal.ofReal K * ENNReal.ofReal (kaY X x0 bb x')) * 1 :=
            (mul_one _).symm
        _ ≤ psiF X x0 bb P W (cpt X x' w) * (ENNReal.ofReal K * ENNReal.ofReal (kaY X x0 bb x')) *
              (ENNReal.ofReal (1 / cd) * ENNReal.ofReal (densF X x' w)) :=
            mul_le_mul_of_nonneg_left hden zero_le
        _ = A * (ENNReal.ofReal (densF X x' w) * psiF X x0 bb P W (cpt X x' w)) := by
            rw [hAdef]; ring
    have hsub : Bset X x ρ0 ⊆ OmF X x' := fun w hw => hdom w hw
    have hAt : A ≠ ⊤ := ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      ENNReal.ofReal_ne_top) ENNReal.ofReal_ne_top
    calc ∫⁻ w in Bset X x ρ0, ‖P (cpt X x' w)‖ₑ ^ 2 * W (cpt X x' w)
        ≤ ∫⁻ w in Bset X x ρ0, A * (ENNReal.ofReal (densF X x' w) * psiF X x0 bb P W (cpt X x' w)) :=
          setLIntegral_mono' (isOpen_Bset X x ρ0).measurableSet hpt
      _ = A * ∫⁻ w in Bset X x ρ0, ENNReal.ofReal (densF X x' w) * psiF X x0 bb P W (cpt X x' w) :=
          lintegral_const_mul' _ _ hAt
      _ ≤ A * ∫⁻ w in OmF X x', ENNReal.ofReal (densF X x' w) * psiF X x0 bb P W (cpt X x' w) :=
          mul_le_mul_of_nonneg_left (lintegral_mono_set hsub) zero_le
      _ = A * ∫⁻ w, psiF X x0 bb P W (cpt X x' w) ∂muF X x' := by
          have hm : Measurable fun w => psiF X x0 bb P W (cpt X x' w) :=
            hψm.comp (cont_cpt' X x').measurable
          rw [muF, lintegral_withDensity_eq_lintegral_mul _ (meas_densF' X x') hm]
          rfl
      _ = A * Nn := by
          rw [measInv_holds r X x' x0 hx'o hx0 _ hψm hψB, psiF_int X hx0 bb hPF]
      _ = c0 * ENNReal.ofReal (kaY X x0 bb x') := by rw [hAdef, hc0]; ring
  calc ∑' γ : X.Γ, (∫⁻ w in Bset X x ρ0,
        ‖P (lact γ.1 (cpt X x w))‖ₑ ^ 2 * W (lact γ.1 (cpt X x w))) ^ (1 / 2 : ℝ)
      ≤ ∑' γ : X.Γ, (c0 * ENNReal.ofReal (kaY X x0 bb (lact γ.1 x))) ^ (1 / 2 : ℝ) :=
        ENNReal.tsum_le_tsum fun γ => ENNReal.rpow_le_rpow (hI γ) (by norm_num)
    _ = ∑' γ : X.Γ, c0 ^ (1 / 2 : ℝ) * ENNReal.ofReal (kaY X x0 (bb / 2) (lact γ.1 x)) :=
        tsum_congr fun γ => by rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), kaY_half]
    _ = c0 ^ (1 / 2 : ℝ) * ∑' γ : X.Γ, ENNReal.ofReal (kaY X x0 (bb / 2) (lact γ.1 x)) :=
        ENNReal.tsum_mul_left
    _ ≤ c0 ^ (1 / 2 : ℝ) * C2 := mul_le_mul_of_nonneg_left (hsum x hxo) zero_le

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf
end

