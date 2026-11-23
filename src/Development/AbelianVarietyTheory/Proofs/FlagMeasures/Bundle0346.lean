module

public import Mathlib
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0215
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0267
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0335
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFibreFamilyHermitianLengthInfiniteAdeles
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0147
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.DensInfTR
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0339
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0226
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0225
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0210
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0108
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FrameActionMulEquivFiniteAdelicUnitary
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0340

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SiegelOneVectorMeasurableOfCompactSupport
section
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice GlobalTheory.GaugeEx
open scoped TensorProduct ENNReal

noncomputable section

namespace GlobalTheory.OneVecMeas

theorem sw1b2_of_cc : GlobalTheory.GaussMean.OneVectorCc → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → SW1b2 F E σ M J := by
  intro hOV F E _ _ _ _ _ σ hCM M J hJ hM β hβ d b Φ Φi Φf Φv hΦi hpure hreal hΦ
  have hOV' := hOV F E σ hCM M J hJ
  have H0 := hOV'.2 hM β hβ d b (fun _ => 0) (fun _ => 0) Φf Φv continuous_const HasCompactSupport.zero
    (fun N e _ _ => contDiff_const) hpure (fun X => by simp)
  refine ⟨H0.1, fun ψ hψ => ?_⟩
  have H1 := H0.2 ψ hψ
  refine ⟨H1.1, fun μ hμ => ⟨(H1.2 μ hμ).1, fun 𝓕 h𝓕 => ?_⟩⟩
  have H2 := (H1.2 μ hμ).2 𝓕 h𝓕
  have hfin : μ 𝓕 < ⊤ := (hOV'.1.2 μ hμ).2 𝓕 h𝓕
  refine ⟨H2.1, H2.2.1, H2.2.2.1, H2.2.2.2.1, ?_⟩
  intro μi νi μv νv hμi hνi hμv hνv
  have hCc := fun (Φ' : (Fin 1 → Fin M → AF F ⊗[F] E) → ℂ) (Φi' : (Fin 1 → Fin M → Ainf F ⊗[F] E) → ℂ) h1 h2 h3 h5 =>
    ((((hOV'.2 hM β hβ d b Φ' Φi' Φf Φv h1 h2 h3 hpure h5).2 ψ hψ).2 μ hμ).2 𝓕 h𝓕).2.2.2.2 μi νi μv νv hμi hνi hμv hνv
  refine ⟨?_, ?_, ?_⟩
  · exact _root_.GlobalTheory.GaugeEx.FibExist.exists_fibreFamily_ainf F E σ hCM M J μi νi (by omega) hJ hμi.1 hνi.1
  · exact ⟨fun v => Classical.choose (_root_.GlobalTheory.HermFibreLocal.exists_isFibreFamily F E σ hCM M J hJ (by omega) v (μv v) (νv v) (hμv v).1 (hνv v).1),
      fun v => Classical.choose_spec (_root_.GlobalTheory.HermFibreLocal.exists_isFibreFamily F E σ hCM M J hJ (by omega) v (μv v) (νv v) (hμv v).1 (hνv v).1)⟩
  intro fi fv hfi hfv

  have : IsTotallyReal F := hCM.1
  have : Countable E := (Module.finBasis ℚ E).equivFun.toEquiv.injective.countable
  set βi : Ainf F := algebraMap F (Ainf F) β with hβi
  have hβiB : βi ∈ {c : Ainf F | ∀ w, c w ≠ 0} :=
    (FibExist.isUnit_ainf_iff βi).1 ((Ne.isUnit hβ).map (algebraMap F (Ainf F)))
  have hβv : ∀ v, algebraMap F (Fv F v) β ≠ 0 := fun v => (map_ne_zero _).2 hβ
  have hBi : {c : Ainf F | IsUnit c} = {c : Ainf F | ∀ w, c w ≠ 0} :=
    Set.ext fun c => FibExist.isUnit_ainf_iff c
  have hBio : IsOpen {c : Ainf F | ∀ w, c w ≠ 0} := by
    have : {c : Ainf F | ∀ w, c w ≠ 0} = ⋂ w, {c : Ainf F | c w ≠ 0} := by ext; simp
    rw [this]
    exact isOpen_iInter_of_finite fun w => isOpen_ne.preimage (continuous_apply w)
  have hΦvR : ∀ v, Φv v = fun X => (((Φv v X).re : ℝ) : ℂ) := fun v => funext fun X =>
    Complex.ext (by simp) (by simp [(hreal v X).2])
  have hΦfR : ∀ Y, Φf Y = (((Φf Y).re : ℝ) : ℂ) ∧ 0 ≤ (Φf Y).re := by
    intro Y
    have e1 : Φf Y = ((∏ᶠ v, (Φv v (projV v Y)).re : ℝ) : ℂ) := by
      have h1 := Complex.ofRealHom.toMonoidHom.map_finprod_of_injective Complex.ofReal_injective
        (fun v => (Φv v (projV v Y)).re)
      rw [hpure.2.2 Y]
      exact (finprod_congr fun v => congrFun (hΦvR v) _).trans h1.symm
    rw [e1]
    exact ⟨by simp, by simpa using finprod_nonneg fun v => (hreal v _).1⟩

  have hdensV : ∀ (Fl : ∀ v, Fv F v → ℂ),
      (∀ v, IsContDensityOn (μv v) (fun X => qR (Fv F v) σ J (X 0)) id (νv v) {c | c ≠ 0} (Φv v) (Fl v)) →
      ∀ v, Fl v (algebraMap F (Fv F v) β) =
          ((∫ X, (Φv v X).re ∂(fv v (algebraMap F (Fv F v) β)) : ℝ) : ℂ) ∧
        ∫⁻ X, ENNReal.ofReal (Φv v X).re ∂(fv v (algebraMap F (Fv F v) β)) =
          ENNReal.ofReal (Fl v (algebraMap F (Fv F v) β)).re := by
    intro Fl hFl v
    have := (hνv v).1
    have h' : IsContDensityOn (μv v) (fun X => qR (Fv F v) σ J (X 0)) id (νv v) {c | c ≠ 0}
        (fun X => (((Φv v X).re : ℝ) : ℂ)) (Fl v) := by
      rw [← hΦvR v]; exact hFl v
    exact _root_.GlobalTheory.FibreDensity.contDensityOn_eq_fibre_integral _ _ (μv v) _ (νv v) _ (fv v) (fun X => (Φv v X).re) (Fl v)
      (FibExist.continuous_qR (Fv F v) σ J) isOpen_ne (hfv v)
      (Complex.continuous_re.comp (hpure.1 v).1.continuous) ((hpure.1 v).2.comp_left Complex.zero_re)
      (fun X => (hreal v X).1) h' _ (hβv v)

  obtain ⟨Fi0, Fl0, -, hFl0, hmul0, -⟩ := hCc (fun _ => 0) (fun _ => 0) continuous_const HasCompactSupport.zero
    (fun N e _ _ => contDiff_const) (fun X => by simp)
  have hFlR : ∀ (Fl : ∀ v, Fv F v → ℂ),
      (∀ v, IsContDensityOn (μv v) (fun X => qR (Fv F v) σ J (X 0)) id (νv v) {c | c ≠ 0} (Φv v) (Fl v)) →
      Multipliable (fun v => Fl v (algebraMap F (Fv F v) β)) →
      Multipliable (fun v => ∫⁻ X, ENNReal.ofReal (Φv v X).re ∂(fv v (algebraMap F (Fv F v) β))) ∧
      ∏' v, ∫⁻ X, ENNReal.ofReal (Φv v X).re ∂(fv v (algebraMap F (Fv F v) β)) =
        ENNReal.ofReal (∏' v, Fl v (algebraMap F (Fv F v) β)).re := by
    intro Fl hFl hm
    have e : (fun v => ∫⁻ X, ENNReal.ofReal (Φv v X).re ∂(fv v (algebraMap F (Fv F v) β))) =
        fun v => ENNReal.ofReal (Fl v (algebraMap F (Fv F v) β)).re := funext fun v => (hdensV Fl hFl v).2
    rw [e]
    exact GlobalTheory.T.multipliable_ofReal_re_of_nonneg_real _ _ hm fun v => by
      rw [(hdensV Fl hFl v).1]
      exact ⟨by simp, by simpa using integral_nonneg fun X => (hreal v X).1⟩
  refine ⟨(hFlR Fl0 hFl0 hmul0).1, ?_⟩
  set C := ∏' v, ∫⁻ X, ENNReal.ofReal (Φv v X).re ∂(fv v (algebraMap F (Fv F v) β)) with hC
  have hCtop : C < ⊤ := by rw [(hFlR Fl0 hFl0 hmul0).2]; exact ENNReal.ofReal_lt_top

  obtain ⟨k, eK, hK⟩ := PI.VolStabS.exists_coord_tens F E
  obtain ⟨k1, e1, h1⟩ := PI.VolStabS.exists_coord_pi eK hK (Fin M)
  obtain ⟨N, eV, hV⟩ := PI.VolStabS.exists_coord_pi e1 h1 (Fin 1)
  let eA : (Fin 1 → Fin M → Ainf F ⊗[F] E) ≃+ (Fin N → ℝ) := { eV.toEquiv with map_add' := hV }
  have hsmooth : ∀ φ : (Fin N → ℝ) → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ →
      ∀ (N' : ℕ) (e' : (Fin 1 → Fin M → Ainf F ⊗[F] E) ≃+ (Fin N' → ℝ)), Continuous e' → Continuous e'.symm →
        ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ((fun X => ((φ (eV X) : ℝ) : ℂ)) ∘ e'.symm) := by
    intro φ hφ N' e' _ he'
    let L := ((eA : (Fin 1 → Fin M → Ainf F ⊗[F] E) →+ (Fin N → ℝ)).comp
      (e'.symm : (Fin N' → ℝ) →+ (Fin 1 → Fin M → Ainf F ⊗[F] E))).toRealLinearMap
      (eV.continuous.comp he')
    have : ((fun X => ((φ (eV X) : ℝ) : ℂ)) ∘ e'.symm) = Complex.ofRealCLM ∘ φ ∘ L := rfl
    rw [this]
    exact Complex.ofRealCLM.contDiff.comp (hφ.comp L.contDiff)

  let act : (Fin 1 → Fin M → E) → HA (AF F) σ J → (Fin 1 → Fin M → AF F ⊗[F] E) :=
    fun x h => h⁻¹ • ratTup (F := F) (AF F) x
  have hact : ∀ x, Continuous (act x) := fun x => continuous_inv.smul continuous_const
  have hpF : Continuous (projFin (F := F) (E := E) (M := M) (n := 1)) :=
    continuous_pi fun a => continuous_pi fun i =>
      (GlobalTheory.GaugeGlue.continuous_map b (sndA F) GlobalTheory.GaugeGlue.continuous_sndA).comp
        ((continuous_apply i).comp (continuous_apply a))
  have hpI : Continuous (projInf (F := F) (E := E) (M := M) (n := 1)) := GlobalTheory.GaugeGlue.continuous_projInf b
  have hΦfc := _root_.GlobalTheory.isPureFin_continuous_hasCompactSupport F E d M 1 b Φf Φv hpure
  let T : Set (Fin 1 → Fin M → E) := {x | hE σ J (x 0) (x 0) = algebraMap F E β}
  have hS : {x : Fin 1 → Fin M → E | x 0 ≠ 0 ∧ hE σ J (x 0) (x 0) = algebraMap F E β} = T := by
    ext x
    refine ⟨fun h => h.2, fun h => ⟨fun h0 => ?_, h⟩⟩
    have : hE σ J (x 0) (x 0) = 0 := by rw [h0]; simp [hE, Formalism.UG.hform]
    exact (map_ne_zero (algebraMap F E)).2 hβ (h.symm.trans this)
  let a : T → HA (AF F) σ J → (Fin N → ℝ) := fun x h => eV (projInf (act x h))
  let w : T → HA (AF F) σ J → ℝ≥0∞ := fun x h => ENNReal.ofReal (Φf (projFin (act x h))).re
  have ha : ∀ x, Continuous (a x) := fun x => eV.continuous.comp (hpI.comp (hact x))
  have hwr : ∀ x, Continuous fun h => (Φf (projFin (act x h))).re :=
    fun x => Complex.continuous_re.comp (hΦfc.1.comp (hpF.comp (hact x)))
  have hw : ∀ x, Continuous (w x) := fun x => ENNReal.continuous_ofReal.comp (hwr x)
  let m₁ : Measure (Fin N → ℝ) := (μ 𝓕)⁻¹ • Measure.sum fun x : T => ((μ.restrict 𝓕).withDensity (w x)).map (a x)
  have hm₁ : ∀ g : (Fin N → ℝ) → ℝ≥0∞, Measurable g →
      ∫⁻ y, g y ∂m₁ = (μ 𝓕)⁻¹ * ∫⁻ h in 𝓕, ∑' x : T, g (a x h) * w x h ∂μ := by
    intro g hg
    have hts := lintegral_tsum (μ := μ.restrict 𝓕) (f := fun (x : T) h => g (a x h) * w x h)
      fun x => ((hg.comp (ha x).measurable).mul (hw x).measurable).aemeasurable
    beta_reduce at hts
    rw [lintegral_smul_measure, lintegral_sum_measure, smul_eq_mul, hts]
    congr 1
    refine tsum_congr fun x => ?_
    rw [lintegral_map hg (ha x).measurable]
    have hwd := lintegral_withDensity_eq_lintegral_mul (μ.restrict 𝓕) (hw x).measurable (hg.comp (ha x).measurable)
    simp only [Function.comp_def] at hwd
    rw [hwd]
    refine lintegral_congr fun h => ?_
    simp only [Pi.mul_apply]
    ring
  let m₂ : Measure (Fin N → ℝ) := C • (fi βi).map eV
  have hm₂ : ∀ g : (Fin N → ℝ) → ℝ≥0∞, Measurable g →
      ∫⁻ y, g y ∂m₂ = C * ∫⁻ X, g (eV X) ∂(fi βi) := by
    intro g hg
    rw [lintegral_smul_measure, lintegral_map hg eV.continuous.measurable, smul_eq_mul]

  have hfoc : IsFiniteMeasureOnCompacts m₂ := by
    refine ⟨fun K hK => ?_⟩
    obtain ⟨f, hf1, -, hfcs, -⟩ := exists_continuous_one_zero_of_isCompact hK isClosed_empty (Set.disjoint_empty K)
    have hint := (hfi.2.2 (fun X => f (eV X)) (f.continuous.comp eV.continuous) (hfcs.comp_homeomorph eV)
      (Set.subset_univ _)).1 βi hβiB
    have hle : (fi βi) (eV ⁻¹' K) ≤ ∫⁻ X, ‖f (eV X)‖ₑ ∂(fi βi) := by
      rw [← lintegral_indicator_one (hK.isClosed.measurableSet.preimage eV.continuous.measurable)]
      refine lintegral_mono fun X => ?_
      by_cases hX : X ∈ eV ⁻¹' K
      · rw [Set.indicator_of_mem hX, Pi.one_apply, hf1 hX, Pi.one_apply]; simp
      · rw [Set.indicator_of_notMem hX]; exact bot_le
    show (C • (fi βi).map eV) K < ⊤
    rw [Measure.smul_apply, Measure.map_apply eV.continuous.measurable hK.isClosed.measurableSet, smul_eq_mul]
    exact ENNReal.mul_lt_top hCtop (hle.trans_lt hint.2)

  have htest : ∀ φ : (Fin N → ℝ) → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ → HasCompactSupport φ →
      (∀ y, 0 ≤ φ y) → ∫⁻ y, ENNReal.ofReal (φ y) ∂m₁ = ∫⁻ y, ENNReal.ofReal (φ y) ∂m₂ := by
    intro φ hφ hφcs hφ0
    have hφc : Continuous φ := hφ.continuous
    let Φi' : (Fin 1 → Fin M → Ainf F ⊗[F] E) → ℂ := fun X => ((φ (eV X) : ℝ) : ℂ)
    let Φ' : (Fin 1 → Fin M → AF F ⊗[F] E) → ℂ := fun X => Φi' (projInf X) * Φf (projFin X)
    have hΦi'c : Continuous Φi' := Complex.continuous_ofReal.comp (hφc.comp eV.continuous)
    have hΦi'cs : HasCompactSupport Φi' := (hφcs.comp_homeomorph eV).comp_left Complex.ofReal_zero
    have hΦ'c := _root_.GlobalTheory.prod_continuous_hasCompactSupport F E M 1 Φ' Φi' Φf hΦi'c hΦi'cs hΦfc.1 hΦfc.2 (fun X => rfl)
    obtain ⟨Fi', Fl', hdi, hdv, hmul', hmean'⟩ := hCc Φ' Φi' hΦi'c hΦi'cs (hsmooth φ hφ) (fun X => rfl)
    rw [hBi] at hdi
    have := hνi.1
    have hFi := _root_.GlobalTheory.FibreDensity.contDensityOn_eq_fibre_integral _ _ μi _ νi _ fi (fun X => φ (eV X)) Fi' (FibExist.continuous_qR (Ainf F) σ J)
      hBio hfi (hφc.comp eV.continuous) (hφcs.comp_homeomorph eV) (fun X => hφ0 _) hdi βi hβiB
    have hP := hFlR Fl' hdv hmul'
    let f : T → HA (AF F) σ J → ℝ := fun x h => φ (a x h) * (Φf (projFin (act x h))).re
    have hf0 : ∀ x h, 0 ≤ f x h := fun x h => mul_nonneg (hφ0 _) (hΦfR _).2
    have hfm : ∀ x, Measurable (f x) := fun x => ((hφc.comp (ha x)).mul (hwr x)).measurable
    have hΦ'f : ∀ (x : T) h, Φ' (act x h) = ((f x h : ℝ) : ℂ) := by
      intro x h
      show ((φ (eV (projInf (act x h))) : ℝ) : ℂ) * Φf (projFin (act x h)) =
        ((φ (eV (projInf (act x h))) * (Φf (projFin (act x h))).re : ℝ) : ℂ)
      conv_lhs => rw [(hΦfR (projFin (act x h))).1]
      push_cast; ring
    have hint := GlobalTheory.T.lintegral_hermitian_orbit_sum_fixed_length_lt_top F E σ hCM M J hJ β hβ Φ' hΦ'c.1 hΦ'c.2 μ 𝓕 hμ h𝓕
    have hint' : ∫⁻ h in 𝓕, ∑' x : T, ‖((f x h : ℝ) : ℂ)‖ₑ ∂μ < ⊤ := by
      refine lt_of_eq_of_lt ?_ hint
      refine lintegral_congr fun h => tsum_congr fun x => ?_
      rw [← hΦ'f]
    have hL := GlobalTheory.T.meanL_tsum_ofReal_eq_ofReal_re_meanC (HA (AF F) σ J) μ 𝓕 T f hfm hf0 hfin hint'
    rw [hm₁ (fun y => ENNReal.ofReal (φ y)) (ENNReal.measurable_ofReal.comp hφc.measurable),
      hm₂ (fun y => ENNReal.ofReal (φ y)) (ENNReal.measurable_ofReal.comp hφc.measurable)]
    have e1 : (μ 𝓕)⁻¹ * ∫⁻ h in 𝓕, ∑' x : T, ENNReal.ofReal (φ (a x h)) * w x h ∂μ =
        meanL μ 𝓕 (fun h => ∑' x : T, ENNReal.ofReal (f x h)) := by
      unfold meanL; congr 1; refine lintegral_congr fun h => tsum_congr fun x => ?_
      simp only [f, w]; rw [ENNReal.ofReal_mul (hφ0 _)]
    rw [e1, hL]
    have e2 : meanC μ 𝓕 (fun h => ∑' x : T, ((f x h : ℝ) : ℂ)) =
        Fi' βi * ∏' v, Fl' v (algebraMap F (Fv F v) β) := by
      rw [← hmean']; unfold thSum; congr 1; funext h; exact tsum_congr fun x => (hΦ'f x h).symm
    rw [e2, hP.2, hFi.2, hFi.1]
    have hr : 0 ≤ ∫ X, φ (eV X) ∂(fi βi) := integral_nonneg fun X => hφ0 _
    simp only [Complex.re_ofReal_mul, Complex.ofReal_re]
    rw [ENNReal.ofReal_mul hr, mul_comm]
  have := hfoc
  have hm : m₁ = m₂ := _root_.GlobalTheory.measure_eq_of_lintegral_smooth_eq N m₁ m₂ htest
  rw [hS]
  calc meanL μ 𝓕 (fun h => ∑' x : T, Φ (h⁻¹ • ratTup (F := F) (AF F) (x : Fin 1 → Fin M → E)))
      = ∫⁻ y, Φi (eV.symm y) ∂m₁ := by
        rw [hm₁ (fun y => Φi (eV.symm y)) (hΦi.comp eV.symm.continuous.measurable)]
        unfold meanL; congr 1; refine lintegral_congr fun h => tsum_congr fun x => ?_
        simp only [a, w, act, hΦ, Homeomorph.symm_apply_apply]
    _ = ∫⁻ y, Φi (eV.symm y) ∂m₂ := by rw [hm]
    _ = (∫⁻ X, Φi X ∂(fi βi)) * C := by
        rw [hm₂ (fun y => Φi (eV.symm y)) (hΦi.comp eV.symm.continuous.measurable), mul_comm]
        simp only [Homeomorph.symm_apply_apply]

end GlobalTheory.OneVecMeas
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SobolevValueAtOneFixedCompactDiagSignUnitary
section
open MeasureTheory Matrix Formalism.MainNotions.S
open scoped ENNReal

namespace GlobalTheory.SobolevHaar

theorem ofReal_list_sum_le {α : Type} (S : List α) (f : α → ℝ) :
    ENNReal.ofReal (S.map f).sum ≤ (S.map fun a => ENNReal.ofReal (f a)).sum := by
  induction S with
  | nil => simp
  | cons a S ih =>
    simp only [List.map_cons, List.sum_cons]
    exact ENNReal.ofReal_add_le.trans (add_le_add le_rfl ih)

private theorem ofReal_integral_le_lintegral_ofReal {X : Type} [MeasurableSpace X] (μ : Measure X) (f : X → ℝ)
    (hf : ∀ x, 0 ≤ f x) : ENNReal.ofReal (∫ x, f x ∂μ) ≤ ∫⁻ x, ENNReal.ofReal (f x) ∂μ := by
  by_cases hi : Integrable f μ
  · exact (ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall hf)).le
  · rw [integral_undef hi]
    simp

theorem sobolev_at_one_compact : ∀ (n : ℕ) (ε : Fin n → Bool), ∃ (S : List (List (Matrix (Fin n) (Fin n) ℂ))) (C : ℝ) (Q : Set (Formalism.REAL.UJ ε)), IsCompact Q ∧ (∀ l ∈ S, ∀ X ∈ l, Formalism.REAL.inG ε X) ∧ 0 ≤ C ∧ ∀ F : List (Matrix (Fin n) (Fin n) ℂ) → Matrix (Fin n) (Fin n) ℂ → ℂ, (∀ l : List (Matrix (Fin n) (Fin n) ℂ), (∀ Y ∈ l, Formalism.REAL.inG ε Y) → ContinuousOn (F l) (UJset ε)) → (∀ l : List (Matrix (Fin n) (Fin n) ℂ), (∀ Y ∈ l, Formalism.REAL.inG ε Y) → ∀ X, Formalism.REAL.inG ε X → ∀ g ∈ UJset ε, HasDerivAt (fun t : ℝ => F l (g * NormedSpace.exp ((t : ℂ) • X))) (F (X :: l) g) 0) → ENNReal.ofReal (‖F [] 1‖ ^ 2) ≤ ENNReal.ofReal C * (S.map fun l => ∫⁻ y in Q, ENNReal.ofReal (‖F l (umat y)‖ ^ 2) ∂(Formalism.REAL.muG ε)).sum := by
  intro n ε

  obtain ⟨E, hE, hON, -⟩ := GlobalTheory.LieONB.exists_orthonormal_basis n ε
  obtain ⟨s, hs, hsmall⟩ := exists_small n
  obtain ⟨c, -, hc, -⟩ := GlobalTheory.GaugeConst.exists_unique_isGauge n ε
  have hEl : ∀ i, E i ∈ GlobalTheory.GaugeConst.lieJ ε := fun i => GlobalTheory.GaugeConst.mem_lieJ.2 (hE i).1
  have hsm : ∀ (t : ℝ) (X : Matrix (Fin n) (Fin n) ℂ), (t : ℂ) • X = t • X := by
    intro t X
    ext a b
    simp [Complex.real_smul]

  obtain ⟨cu, hcuM, hcuc⟩ : ∃ cu : Fin (n ^ 2) → ℝ → Formalism.REAL.UJ ε,
      (∀ i t, umat (cu i t) = NormedSpace.exp ((t : ℂ) • E i)) ∧ ∀ i, Continuous (cu i) := by
    refine ⟨fun i t => GlobalTheory.GaugeConst.expJ ε (t • ⟨E i, hEl i⟩), fun i t => ?_, fun i => ?_⟩
    · rw [hsm]
      exact GlobalTheory.GaugeConst.uMat_expJ ε (t • ⟨E i, hEl i⟩)
    · exact (GlobalTheory.GaugeConst.continuous_expJ ε).comp (continuous_id.smul continuous_const)
  have hu1 : umat (1 : Formalism.REAL.UJ ε) = 1 := rfl
  have humul : ∀ x y : Formalism.REAL.UJ ε, umat (x * y) = umat x * umat y := fun _ _ => rfl
  have hinj : Function.Injective (fun x : Formalism.REAL.UJ ε => umat x) :=
    GlobalTheory.GaugeConst.uMat_injective ε
  have hcu0 : ∀ i, cu i 0 = 1 := by
    intro i
    apply hinj
    show umat (cu i 0) = umat 1
    rw [hcuM, hu1]
    simp
  have hcuadd : ∀ i a b, cu i (a + b) = cu i a * cu i b := by
    intro i a b
    apply hinj
    show umat (cu i (a + b)) = umat (cu i a * cu i b)
    rw [humul, hcuM, hcuM, hcuM, Complex.ofReal_add, add_smul]
    exact Matrix.exp_add_of_commute _ _ (((Commute.refl (E i)).smul_left _).smul_right _)

  have hlist : ∀ l : List (Formalism.REAL.UJ ε), umat l.prod = (l.map fun x => umat x).prod := by
    intro l
    induction l with
    | nil => rfl
    | cons a l ih => rw [List.prod_cons, humul, ih, List.map_cons, List.prod_cons]
  have hΘ : ∀ t : Fin (n ^ 2) → ℝ, umat ((List.ofFn fun i => cu i (t i)).prod) =
      (List.ofFn fun i => NormedSpace.exp ((t i : ℂ) • E i)).prod := by
    intro t
    rw [hlist, List.map_ofFn]
    simp only [Function.comp_def, hcuM]
  have hΘc : Continuous fun t : Fin (n ^ 2) → ℝ => (List.ofFn fun i => cu i (t i)).prod :=
    GlobalTheory.continuous_prod_ofFn_curves (n ^ 2) cu hcuc
  obtain ⟨K, hchart⟩ : ∃ K : ℝ, ∀ Φ : Formalism.REAL.UJ ε → ENNReal, Measurable Φ →
      ∫⁻ t in Set.pi Set.univ (fun _ : Fin (n ^ 2) => Set.Icc (0 : ℝ) s),
          Φ ((List.ofFn fun i => cu i (t i)).prod) ≤
        ENNReal.ofReal K * ∫⁻ y in (fun t : Fin (n ^ 2) → ℝ => (List.ofFn fun i => cu i (t i)).prod) ''
          Set.pi Set.univ (fun _ : Fin (n ^ 2) => Set.Icc (0 : ℝ) s), Φ y ∂(Formalism.REAL.muG ε) :=
    ⟨_, GlobalTheory.ProductChart.lintegral_chart_le n ε c s E
      (fun t => (List.ofFn fun i => cu i (t i)).prod) hc (fun i => (hE i).1) hON hs hsmall hΘ⟩

  have hD : ∀ i, ∀ v ∈ {l : List (Matrix (Fin n) (Fin n) ℂ) | ∀ Y ∈ l, Formalism.REAL.inG ε Y},
      E i :: v ∈ {l : List (Matrix (Fin n) (Fin n) ℂ) | ∀ Y ∈ l, Formalism.REAL.inG ε Y} := by
    intro i v hv
    simp only [Set.mem_ofPred_eq] at hv ⊢
    intro Y hY
    rcases List.mem_cons.1 hY with rfl | hY
    · exact (hE i).1
    · exact hv Y hY
  obtain ⟨S, C0, hSA, hC0, hbound⟩ :=
    cube_sum {l : List (Matrix (Fin n) (Fin n) ℂ) | ∀ Y ∈ l, Formalism.REAL.inG ε Y} [] (by simp) s hs
      (n ^ 2) cu (fun i v => E i :: v) (fun i => ⟨hcuc i, hcu0 i, hcuadd i⟩) hD
  refine ⟨S, C0 * max K 0,
    (fun t : Fin (n ^ 2) → ℝ => (List.ofFn fun i => cu i (t i)).prod) ''
      Set.pi Set.univ (fun _ : Fin (n ^ 2) => Set.Icc (0 : ℝ) s),
    (isCompact_univ_pi fun _ => isCompact_Icc).image hΘc,
    fun l hl => (hSA l hl : ∀ Y ∈ l, Formalism.REAL.inG ε Y),
    mul_nonneg hC0 (le_max_right _ _), ?_⟩
  intro F hFc hFd
  have hmem : ∀ x : Formalism.REAL.UJ ε, umat x ∈ UJset ε := fun x => x.2
  have hFrc : ∀ v : List (Matrix (Fin n) (Fin n) ℂ), (∀ Y ∈ v, Formalism.REAL.inG ε Y) →
      Continuous fun x : Formalism.REAL.UJ ε => F v (umat x) := fun v hv =>
    (hFc v hv).comp_continuous (GlobalTheory.GaugeConst.continuous_uMat ε) hmem
  have hFrd : ∀ v : List (Matrix (Fin n) (Fin n) ℂ), (∀ Y ∈ v, Formalism.REAL.inG ε Y) →
      ∀ (i : Fin (n ^ 2)) (x : Formalism.REAL.UJ ε),
        HasDerivAt (fun t => F v (umat (x * cu i t))) (F (E i :: v) (umat x)) 0 := by
    intro v hv i x
    have h := hFd v hv (E i) (hE i).1 (umat x) (hmem x)
    have he : (fun t : ℝ => F v (umat (x * cu i t))) =
        fun t : ℝ => F v (umat x * NormedSpace.exp ((t : ℂ) • E i)) := by
      funext t
      rw [humul, hcuM]
    rw [he]
    exact h
  have hb : ‖F [] 1‖ ^ 2 ≤ C0 * (S.map fun v =>
      ∫ t in Set.pi Set.univ (fun _ : Fin (n ^ 2) => Set.Icc (0 : ℝ) s),
        ‖F v (umat ((List.ofFn fun i => cu i (t i)).prod))‖ ^ 2).sum :=
    hbound (fun v x => F v (umat x)) hFrc hFrd
  have hpt : ∀ v ∈ S,
      ENNReal.ofReal (∫ t in Set.pi Set.univ (fun _ : Fin (n ^ 2) => Set.Icc (0 : ℝ) s),
        ‖F v (umat ((List.ofFn fun i => cu i (t i)).prod))‖ ^ 2) ≤
      ENNReal.ofReal K * ∫⁻ y in (fun t : Fin (n ^ 2) → ℝ => (List.ofFn fun i => cu i (t i)).prod) ''
          Set.pi Set.univ (fun _ : Fin (n ^ 2) => Set.Icc (0 : ℝ) s),
        ENNReal.ofReal (‖F v (umat y)‖ ^ 2) ∂(Formalism.REAL.muG ε) := by
    intro v hv
    have hcont := hFrc v (hSA v hv)
    have hmeas : Measurable fun y : Formalism.REAL.UJ ε => ENNReal.ofReal (‖F v (umat y)‖ ^ 2) :=
      (ENNReal.continuous_ofReal.comp (hcont.norm.pow 2)).measurable
    have h1 := ofReal_integral_le_lintegral_ofReal
      (volume.restrict (Set.pi Set.univ (fun _ : Fin (n ^ 2) => Set.Icc (0 : ℝ) s)))
      (fun t => ‖F v (umat ((List.ofFn fun i => cu i (t i)).prod))‖ ^ 2) (fun t => sq_nonneg _)
    have h2 := hchart (fun y => ENNReal.ofReal (‖F v (umat y)‖ ^ 2)) hmeas
    exact h1.trans h2
  calc ENNReal.ofReal (‖F [] 1‖ ^ 2)
      ≤ ENNReal.ofReal (C0 * (S.map fun v =>
          ∫ t in Set.pi Set.univ (fun _ : Fin (n ^ 2) => Set.Icc (0 : ℝ) s),
            ‖F v (umat ((List.ofFn fun i => cu i (t i)).prod))‖ ^ 2).sum) :=
        ENNReal.ofReal_le_ofReal hb
    _ = ENNReal.ofReal C0 * ENNReal.ofReal (S.map fun v =>
          ∫ t in Set.pi Set.univ (fun _ : Fin (n ^ 2) => Set.Icc (0 : ℝ) s),
            ‖F v (umat ((List.ofFn fun i => cu i (t i)).prod))‖ ^ 2).sum :=
        ENNReal.ofReal_mul hC0
    _ ≤ ENNReal.ofReal C0 * (S.map fun v => ENNReal.ofReal K *
          ∫⁻ y in (fun t : Fin (n ^ 2) → ℝ => (List.ofFn fun i => cu i (t i)).prod) ''
            Set.pi Set.univ (fun _ : Fin (n ^ 2) => Set.Icc (0 : ℝ) s),
          ENNReal.ofReal (‖F v (umat y)‖ ^ 2) ∂(Formalism.REAL.muG ε)).sum := by
        gcongr
        exact (ofReal_list_sum_le _ _).trans (List.sum_le_sum hpt)
    _ = ENNReal.ofReal C0 * ENNReal.ofReal K * (S.map fun v =>
          ∫⁻ y in (fun t : Fin (n ^ 2) → ℝ => (List.ofFn fun i => cu i (t i)).prod) ''
            Set.pi Set.univ (fun _ : Fin (n ^ 2) => Set.Icc (0 : ℝ) s),
          ENNReal.ofReal (‖F v (umat y)‖ ^ 2) ∂(Formalism.REAL.muG ε)).sum := by
        rw [List.sum_map_mul_left, mul_assoc]
    _ ≤ ENNReal.ofReal (C0 * max K 0) * (S.map fun v =>
          ∫⁻ y in (fun t : Fin (n ^ 2) → ℝ => (List.ofFn fun i => cu i (t i)).prod) ''
            Set.pi Set.univ (fun _ : Fin (n ^ 2) => Set.Icc (0 : ℝ) s),
          ENNReal.ofReal (‖F v (umat y)‖ ^ 2) ∂(Formalism.REAL.muG ε)).sum := by
        rw [ENNReal.ofReal_mul hC0]
        gcongr
        exact le_max_left _ _

end GlobalTheory.SobolevHaar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TransportRepresentsClassesWeightOne
section
open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ColClass

theorem classes_and_weight : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (F : Formalism.L2.Forms.Forms0 D u) (Tr : Transport X u F) (hK : X.LevelSubgroupCharacter), (∀ a, Tr.ιA (sigA X.B.I a) = Formalism.UG.sigR (Formalism.L2.Forms.sigD D) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (Tr.ιA a)) → LevelMatch X Tr hK → ClsMatch X Tr hK ∧ (Formalism.L2.SG.ColsDim.StabTriv (iotaF X u) (Ku X u hK) → ∀ c, (D.mem u).C.wt 0 c = 1) := by
  intro D X u F Tr hK hsig hLM
  have hW : WittX X u Tr.wt := ⟨Tr.wt_isom, Tr.wt_e, Tr.wt_f, Tr.weight_z⟩
  have hA : IsAdeleIso X Tr.ιA := ⟨Tr.ιA_rat, Tr.ιA_int⟩
  obtain ⟨Φ, hΦ⟩ := _root_.GlobalTheory.frame_action_mulEquiv D X u Tr.wt Tr.ιA hW hA hsig
  obtain ⟨h1, h2, -⟩ := GlobalTheory.T.transport_rational_points_stabiliser_frame D X u Tr.wt Tr.ιA hW hA Φ hΦ
  have hc : ∀ c, Tr.hc c = Φ.symm (F.cls0.y c * Tr.h0⁻¹) := fun c => by
    rw [MulEquiv.eq_symm_apply]
    exact (hΦ _ _).1 (Tr.hc_rep c)
  have hKu : ∀ h : Hfin X u, h ∈ Ku X u hK ↔
      (((Tr.h0⁻¹ * Φ h * Tr.h0 : Formalism.UG.UPts (Formalism.L2.Forms.sigD D) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _))
        (FiniteAdeleRing (𝓞 D.host.F) D.host.F))) : GL _ _) ∈ F.cls0.lev.U :=
    fun h => (hLM.2 h (Φ h) ((hΦ h (Φ h)).2 rfl)).1
  have key := GlobalTheory.ClassDict.classReps_dictionary D.host.F D.host.E (Formalism.L2.Forms.sigD D) (D.R.N 0)
    (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) _ _ _ F.cls0.lev (Gam X u) (Hfin X u) (iotaF X u) (Ku X u hK)
    Φ Tr.h0 hKu h1 h2 ((D.mem u).C.cls 0) F.cls0.y F.cls0.y_bij
  refine ⟨fun h => ?_, fun hst c => ?_⟩
  · obtain ⟨c, hc1, hc2⟩ := key.1 h
    refine ⟨c, ?_, fun c' hc' => hc2 c' ?_⟩
    · obtain ⟨γ, κ, e⟩ := hc1
      exact ⟨γ, κ, by rw [hc]; exact e⟩
    · obtain ⟨γ, κ, e⟩ := hc'
      exact ⟨γ, κ, by rw [← hc]; exact e⟩
  · have hsub : Subsingleton ((D.mem u).C.stab 0 c) := by
      refine ⟨fun s t => ?_⟩
      have h1' : ∀ s : (D.mem u).C.stab 0 c, s = 1 := by
        intro s
        apply F.cls0.stabI_inj c
        rw [map_one]
        apply Subtype.ext
        have hr := (F.cls0.stabI_range c (F.cls0.stabI c s)).1 ⟨s, rfl⟩
        exact key.2 hst c _ (F.cls0.stabI c s).2 hr
      rw [h1' s, h1' t]
    have : Nat.card ((D.mem u).C.stab 0 c) = 1 := by
      haveI : Unique ((D.mem u).C.stab 0 c) := uniqueOfSubsingleton 1
      exact Nat.card_unique
    simp [Formalism.BasicNotions.ColumnChain.wt, this]

end GlobalTheory.ColClass
end

