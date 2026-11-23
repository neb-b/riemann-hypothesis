module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.Bundle0012
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.Bundle0001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.OrbRing
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicUnitaryOrbits.StLamOf
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicUnitaryOrbits.Bundle0002
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HermitianDiagonalization.ExistsOrthogonalFamily

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.PolarLocalOfAction
section
noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Topology Filter Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub
  Formalism.L2.SG.TypedSets Formalism.L2.SG.Pf.NcReal
open scoped TensorProduct

def ActMeas : Prop := ∀ {D : D7} (X : HidaSetting D) (Z : TupI X),
    Measurable (fun g : HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J => g • Z)

def FibOrbAt : Prop := ∀ {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ) hT μinf νinf fibInf,
    PushHyp X u' ψ hT μinf νinf fibInf → ∀ Ω a, IsChart X u' hT Ω a →
    ∃ Ω₁ ⊆ Ω, Ω₁ ∈ 𝓝 (TI X u' hT) ∧ ∀ T ∈ Ω₁, ∃ k : ENNReal,
      fibInf T = k • X.measG.μGinf.map (fun g => g • rmulT X (a T) (Y0 X u'))

def OrbCont : Prop := ∀ {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ) hT μinf νinf fibInf,
    PushHyp X u' ψ hT μinf νinf fibInf → ∀ Ω a, IsChart X u' hT Ω a →
    ∃ Ω₁ ⊆ Ω, Ω₁ ∈ 𝓝 (TI X u' hT) ∧ ∃ c : HmI X → ENNReal, ContinuousAt c (TI X u' hT) ∧
      PolId X u' μinf νinf a Ω₁ c

def JacOneC : Prop := ∀ {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ) hT μinf νinf fibInf,
    PushHyp X u' ψ hT μinf νinf fibInf → ∀ Ω a, IsChart X u' hT Ω a →
    ∀ Ω₂ ⊆ Ω, Ω₂ ∈ 𝓝 (TI X u' hT) → ∀ c : HmI X → ENNReal, ContinuousAt c (TI X u' hT) →
      PolId X u' μinf νinf a Ω₂ c → c (TI X u' hT) = (ENNReal.ofReal (KVal X u'))⁻¹

theorem isOpen_ne_zero_top : IsOpen (({0}ᶜ ∩ {⊤}ᶜ : Set ENNReal)) :=
  isOpen_compl_singleton.inter isOpen_compl_singleton

theorem polar_local_of_orbit (hK : KPos) (h2 : OrbCont) (h4 : JacOneC) : PolarLoc := by
  intro D X u' ψ hT μinf νinf fibInf hP
  obtain ⟨Ω, a, hC⟩ := sqChart_holds X u' ψ hT μinf νinf fibInf hP
  obtain ⟨Ω₁, hΩ₁, hΩ₁n, c, hcc, hc⟩ := h2 X u' ψ hT μinf νinf fibInf hP Ω a hC
  have hK0 : 0 < KVal X u' := hK X u' ψ hT μinf νinf fibInf hP
  have hc0 : c (TI X u' hT) = (ENNReal.ofReal (KVal X u'))⁻¹ :=
    h4 X u' ψ hT μinf νinf fibInf hP Ω a hC Ω₁ hΩ₁ hΩ₁n c hcc hc
  have hne0 : c (TI X u' hT) ≠ 0 := by rw [hc0]; exact ENNReal.inv_ne_zero.2 ENNReal.ofReal_ne_top
  have hneT : c (TI X u' hT) ≠ ⊤ := by rw [hc0]; exact ENNReal.inv_ne_top.2 (ENNReal.ofReal_pos.2 hK0).ne'
  have hN : c ⁻¹' ({0}ᶜ ∩ {⊤}ᶜ) ∈ 𝓝 (TI X u' hT) :=
    hcc (isOpen_ne_zero_top.mem_nhds ⟨Set.mem_compl_singleton_iff.2 hne0, Set.mem_compl_singleton_iff.2 hneT⟩)
  refine ⟨Ω₁ ∩ c ⁻¹' ({0}ᶜ ∩ {⊤}ᶜ), a, fun T => ((c T)⁻¹).toReal, inter_mem hΩ₁n hN, hC.2.1, hC.2.2.1,
    ?_, ?_, ?_⟩
  · show ((c (TI X u' hT))⁻¹).toReal = KVal X u'
    rw [hc0, inv_inv, ENNReal.toReal_ofReal hK0.le]
  · have ht : (c (TI X u' hT))⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.2 hne0
    have hinv : ContinuousAt (fun T => (c T)⁻¹) (TI X u' hT) := tendsto_inv_iff.2 hcc
    exact ContinuousAt.comp (g := ENNReal.toReal) (f := fun T => (c T)⁻¹) (ENNReal.continuousAt_toReal ht) hinv
  · intro φ hφ S hS hSm
    rw [hc φ hφ S (hS.trans Set.inter_subset_left) hSm]
    refine setLIntegral_congr_fun hSm ?_
    intro T hTS
    have hT2 := (hS hTS).2
    have h0 : c T ≠ 0 := Set.mem_compl_singleton_iff.1 hT2.1
    show c T * _ = (ENNReal.ofReal ((c T)⁻¹).toReal)⁻¹ * _
    rw [ENNReal.ofReal_toReal (ENNReal.inv_ne_top.2 h0), inv_inv]

theorem orbCont_of (hG : GramMeas) (hA : ActMeas) (h1 : FibOrbAt) (h2 : PushCont) : OrbCont := by
  intro D X u' ψ hT μinf νinf fibInf hP Ω a hC
  obtain ⟨Ω₁, hΩ₁, hΩ₁n, hk⟩ := h1 X u' ψ hT μinf νinf fibInf hP Ω a hC
  obtain ⟨φ, hφc, hφm, hφs, hφU, hφ0, hIpos, hIfin, hIc⟩ := h2 X u' ψ hT μinf νinf fibInf hP a hC.2.1 hC.2.2.1
  have hfib := hP.2.2.2.2.2.2
  have hΦm : Measurable fun y => ENNReal.ofReal (φ y) := ENNReal.measurable_ofReal.comp hφm
  set I : HmI X → ENNReal := fun T =>
    ∫⁻ g, ENNReal.ofReal (φ (g • rmulT X (a T) (Y0 X u'))) ∂X.measG.μGinf with hIdef
  set Nf : HmI X → ENNReal := fun T => ∫⁻ y, ENNReal.ofReal (φ y) ∂(fibInf T) with hNdef
  have hI1 : I (TI X u' hT) = ∫⁻ g, ENNReal.ofReal (φ (g • Y0 X u')) ∂X.measG.μGinf := by
    simp only [hIdef]; rw [hC.2.1, rmulT_one]
  have hI0 : I (TI X u' hT) ≠ 0 := by rw [hI1]; exact hIpos.ne'
  have hIT : I (TI X u' hT) ≠ ⊤ := by rw [hI1]; exact hIfin.ne
  have hIN : I ⁻¹' ({0}ᶜ ∩ {⊤}ᶜ) ∈ 𝓝 (TI X u' hT) :=
    hIc (isOpen_ne_zero_top.mem_nhds ⟨Set.mem_compl_singleton_iff.2 hI0, Set.mem_compl_singleton_iff.2 hIT⟩)

  have c3 := hfib.2.2 φ hφc hφs hφU
  have hNeq : Nf = fun T => ENNReal.ofReal (∫ v, φ v ∂(fibInf T)) := by
    funext T
    exact (ofReal_integral_eq_lintegral_ofReal (c3.1 T (Set.mem_univ _))
      (Eventually.of_forall fun y => hφ0 y)).symm
  have hNc : ContinuousAt Nf (TI X u' hT) := by
    rw [hNeq]
    exact (ENNReal.continuous_ofReal.comp (continuousOn_univ.1 c3.2)).continuousAt
  refine ⟨Ω₁ ∩ I ⁻¹' ({0}ᶜ ∩ {⊤}ᶜ), Set.inter_subset_left.trans hΩ₁, inter_mem hΩ₁n hIN,
    fun T => Nf T / I T, ENNReal.Tendsto.div hNc (Or.inr hI0) hIc (Or.inl hIT), ?_⟩
  intro φ' hφ' S hS hSm
  have hGS := hG X S hSm
  have c2 := hfib.2.1 ((gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J ⁻¹' (Subtype.val '' S)).indicator φ')
    (hφ'.indicator hGS)
  rw [lintegral_indicator hGS, Measure.restrict_restrict hGS] at c2
  rw [c2]
  have inner : ∀ b, ∫⁻ v, (gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J ⁻¹' (Subtype.val '' S)).indicator φ' v
      ∂(fibInf b) = S.indicator (fun T => ∫⁻ v, φ' v ∂(fibInf T)) b := by
    intro b
    have hae : ∀ᵐ y ∂(fibInf b), y ∈ gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J ⁻¹' {Subtype.val b} ∩ IndI X :=
      ae_iff.2 (hfib.1 b)
    by_cases hb : b ∈ S
    · rw [Set.indicator_of_mem hb]
      apply lintegral_congr_ae
      filter_upwards [hae] with y hy
      have hy1 := Set.mem_singleton_iff.1 (Set.mem_preimage.1 hy.1)
      exact Set.indicator_of_mem (Set.mem_preimage.2 (show gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J y ∈
        Subtype.val '' S from ⟨b, hb, hy1.symm⟩)) _
    · rw [Set.indicator_of_notMem hb]
      calc _ = ∫⁻ _, (0 : ENNReal) ∂(fibInf b) := by
              apply lintegral_congr_ae
              filter_upwards [hae] with y hy
              have hy1 := Set.mem_singleton_iff.1 (Set.mem_preimage.1 hy.1)
              refine Set.indicator_of_notMem ?_ _
              rintro ⟨c, hc, hcy⟩
              have hcb : c = b := Subtype.val_injective (hcy.trans hy1)
              exact hb (hcb ▸ hc)
        _ = 0 := lintegral_zero
  simp_rw [inner]
  rw [lintegral_indicator hSm]
  refine setLIntegral_congr_fun hSm ?_
  intro T hTS
  obtain ⟨k, hkT⟩ := hk T (hS hTS).1
  have hIT2 := (hS hTS).2
  have h0 : I T ≠ 0 := Set.mem_compl_singleton_iff.1 hIT2.1
  have hTop : I T ≠ ⊤ := Set.mem_compl_singleton_iff.1 hIT2.2
  have hm := hA X (rmulT X (a T) (Y0 X u'))
  have e1 : ∀ ψ' : TupI X → ENNReal, Measurable ψ' →
      ∫⁻ v, ψ' v ∂(fibInf T) = k * ∫⁻ g, ψ' (g • rmulT X (a T) (Y0 X u')) ∂X.measG.μGinf := by
    intro ψ' hψ'
    rw [hkT, lintegral_smul_measure, lintegral_map hψ' hm, smul_eq_mul]
  have hNk : Nf T = k * I T := e1 _ hΦm
  show ∫⁻ v, φ' v ∂(fibInf T) = Nf T / I T * ∫⁻ g, φ' (g • rmulT X (a T) (Y0 X u')) ∂X.measG.μGinf
  rw [hNk, ENNReal.mul_div_cancel_right h0 hTop, e1 φ' hφ']

theorem polar_local_of_action (hK : KPos) (hG : GramMeas) (hA : ActMeas) (h1 : FibOrbAt) (h2 : PushCont) (h4 : JacOneC) :
    PolarLoc :=
  polar_local_of_orbit hK (orbCont_of hG hA h1 h2) h4

end PI.AprimeInfW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.SquareChartC1Local
section
noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Topology Filter NumberField Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
  Formalism.L2.SG.Sub Formalism.L2.SG.TypedSets Formalism.L2.SG.Pf.NcReal
open scoped TensorProduct Matrix

theorem square_chart_c1_local {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    [FiniteDimensional F E] (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) {M m : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (Y : Fin m → Fin M → E) (hT : ∀ i j, σ (gramE σ J Y j i) = gramE σ J Y i j) (hdet : (gramE σ J Y).det ≠ 0)
    {N : ℕ} (e : Matrix (Fin m) (Fin m) (Ainf F ⊗[F] E) ≃ₜ (Fin N → ℝ)) (he : ∀ x y, e (x + y) = e x + e y) :
    ∃ (Ω : Set (HermR (Ainf F) σ m)) (a : HermR (Ainf F) σ m → Matrix (Fin m) (Fin m) (Ainf F ⊗[F] E)),
      Ω ∈ 𝓝 (hermOf (Ainf F) σ (gramE σ J Y) hT) ∧ a (hermOf (Ainf F) σ (gramE σ J Y) hT) = 1 ∧
      ContinuousAt a (hermOf (Ainf F) σ (gramE σ J Y) hT) ∧
      (∀ T ∈ Ω, gramR (Ainf F) σ J (fun b i => ∑ c, a T c b * ratTup (Ainf F) Y c i) = (T : Matrix _ _ _)) ∧
      ∀ {η μ' : Type} [Fintype η] [Fintype μ'] (eH : HermR (Ainf F) σ m ≃ₜ EuclideanSpace ℝ η)
        (eM : Matrix (Fin m) (Fin m) (Ainf F ⊗[F] E) ≃ₜ EuclideanSpace ℝ μ'),
        (∀ x y, eH (x + y) = eH x + eH y) → (∀ x y, eM (x + y) = eM x + eM y) →
        ContDiffAt ℝ 1 (fun z => eM (a (eH.symm z))) (eH (hermOf (Ainf F) σ (gramE σ J Y) hT)) ∧
        ∀ v, fderiv ℝ (fun z => eM (a (eH.symm z))) (eH (hermOf (Ainf F) σ (gramE σ J Y) hT)) v =
          (1 / 2 : ℝ) • eM ((gramE σ J Y)⁻¹.map (inclR (Ainf F)) *
            ((eH.symm v : HermR (Ainf F) σ m) : Matrix (Fin m) (Fin m) (Ainf F ⊗[F] E))) := by
  classical
  set G := gramE σ J Y with hG
  have hu : IsUnit G.det := isUnit_iff_ne_zero.2 hdet
  set Tm : Matrix (Fin m) (Fin m) (Ainf F ⊗[F] E) := G.map (inclR (Ainf F)) with hTm
  set Ti : Matrix (Fin m) (Fin m) (Ainf F ⊗[F] E) := G⁻¹.map (inclR (Ainf F)) with hTi
  have hTTi : Tm * Ti = 1 := by
    rw [hTm, hTi, ← Matrix.map_mul, Matrix.mul_nonsing_inv G hu, Matrix.map_one _ (map_zero _) (map_one _)]
  have hTiT : Ti * Tm = 1 := by
    rw [hTm, hTi, ← Matrix.map_mul, Matrix.nonsing_inv_mul G hu, Matrix.map_one _ (map_zero _) (map_one _)]
  set c : Matrix (Fin m) (Fin m) (Ainf F ⊗[F] E) → Matrix (Fin m) (Fin m) (Ainf F ⊗[F] E) :=
    Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Ainf F) σ) with hc
  have hsig := sq_sig_inv (Ainf F) σ hσ
  have hcc : ∀ P, c (c P) = P := by intro P; ext i j; simp [hc, Formalism.UG.cT, hsig]
  have hcadd : ∀ P Q, c (P + Q) = c P + c Q := by intro P Q; ext i j; simp [hc, Formalism.UG.cT]
  have hcsub : ∀ P Q, c (P - Q) = c P - c Q := by intro P Q; ext i j; simp [hc, Formalism.UG.cT]
  have hcmul : ∀ P Q, c (P * Q) = c Q * c P := fun P Q => Formalism.UG.cT_mul _ P Q
  have hc1 : c 1 = 1 := Formalism.UG.cT_one _
  have hcT : c Tm = Tm := by
    ext i j
    simp only [hc, Formalism.UG.cT, hTm, Matrix.transpose_apply, Matrix.map_apply]
    rw [← hT i j]
    simp [Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR, inclR]
  have hcTi : c Ti * Tm = 1 := by
    calc c Ti * Tm = c Ti * c Tm := by rw [hcT]
      _ = c (Tm * Ti) := (hcmul Tm Ti).symm
      _ = 1 := by rw [hTTi, hc1]
  have hcont_c : Continuous c := by
    show Continuous fun P : Matrix (Fin m) (Fin m) (Ainf F ⊗[F] E) => (P.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Ainf F) σ))ᵀ
    exact (continuous_id.matrix_map (continuous_sigRP (Ainf F) σ)).matrix_transpose
  set Bq : Matrix (Fin m) (Fin m) (Ainf F ⊗[F] E) → Matrix (Fin m) (Fin m) (Ainf F ⊗[F] E) →
      Matrix (Fin m) (Fin m) (Ainf F ⊗[F] E) := fun h k => c (Ti * h) * Tm * (Ti * k) with hBq
  set Lq : Matrix (Fin m) (Fin m) (Ainf F ⊗[F] E) → Matrix (Fin m) (Fin m) (Ainf F ⊗[F] E) :=
    fun h => h - c h with hLq
  have hD : ∀ u, Bq Tm u + Bq u Tm + Lq u = u + u := by
    intro u
    simp only [hBq, hLq]
    rw [hTiT, hc1, Matrix.one_mul, Matrix.mul_one, ← Matrix.mul_assoc Tm Ti u, hTTi, Matrix.one_mul, hcmul Ti u,
      Matrix.mul_assoc (c u) (c Ti) Tm, hcTi, Matrix.mul_one]
    abel
  obtain ⟨g, hgc, hg0, hgev, hgcd, hgd⟩ := exists_local_solution_contDiffAt e he Bq
    (by intro x x' y; simp only [hBq, Matrix.mul_add, hcadd, Matrix.add_mul])
    (by intro x y y'; simp only [hBq, Matrix.mul_add])
    (((hcont_c.comp (continuous_const.matrix_mul continuous_fst)).matrix_mul continuous_const).matrix_mul
      (continuous_const.matrix_mul continuous_snd))
    Lq (by intro x y; simp only [hLq, hcadd]; abel) (continuous_id.sub hcont_c) Tm hD
  have hy0 : Bq Tm Tm + Lq Tm = Tm := by
    simp only [hBq, hLq]
    rw [hTiT, hc1, Matrix.one_mul, Matrix.mul_one, hcT, sub_self, add_zero]
  rw [hy0] at hgc hg0 hgev hgcd hgd
  refine ⟨Subtype.val ⁻¹' {y | Bq (g y) (g y) + Lq (g y) = y}, fun T => Ti * g T.val, ?_, ?_, ?_, ?_, ?_⟩
  · exact continuous_subtype_val.continuousAt.preimage_mem_nhds hgev
  · show Ti * g Tm = 1
    rw [hg0, hTiT]
  · exact (continuous_const.matrix_mul continuous_id).continuousAt.comp
      (ContinuousAt.comp_of_eq hgc continuous_subtype_val.continuousAt rfl)
  · intro T hT'
    have hT'' : Bq (g T.val) (g T.val) + Lq (g T.val) = T.val := hT'
    show gramR (Ainf F) σ J (fun b i => ∑ c, (Ti * g T.val) c b * ratTup (Ainf F) Y c i) = T.val
    rw [sq_gramR_rmul (Ainf F) σ J (Ti * g T.val) (ratTup (Ainf F) Y), gramR_ratTup]
    set h := g T.val
    have hP : c (Bq h h) = Bq h h := by
      simp only [hBq]
      rw [hcmul (c (Ti * h) * Tm) (Ti * h), hcmul (c (Ti * h)) Tm, hcc, hcT, Matrix.mul_assoc]
    have hTh : c T.val = T.val := by
      ext i j
      exact T.2 i j
    have hLL : c (Lq h) = -(Lq h) := by
      simp only [hLq]
      rw [hcsub, hcc]
      abel
    have h2 : Lq h + Lq h = 0 := by
      have e1 := congrArg c hT''
      rw [hcadd, hP, hLL, hTh] at e1
      have e2 := add_left_cancel (hT''.trans e1.symm)
      exact eq_neg_iff_add_eq_zero.mp e2
    have h0 : Lq h = 0 := by
      calc Lq h = ((1 / 2 : F) * 2) • Lq h := by norm_num
        _ = (1 / 2 : F) • (Lq h + Lq h) := by rw [mul_smul, two_smul]
        _ = 0 := by rw [h2, smul_zero]
    rw [h0, add_zero] at hT''
    exact hT''
  · intro η μ' _ _ eH eM heH heM
    have hHs : ∀ x y, eH.symm (x + y) = eH.symm x + eH.symm y := by
      intro x y; apply eH.injective; rw [heH]; simp
    have hes : ∀ x y, e.symm (x + y) = e.symm x + e.symm y := by
      intro x y; apply e.injective; rw [he]; simp
    let L₁ : EuclideanSpace ℝ η →L[ℝ] (Fin N → ℝ) :=
      (AddMonoidHom.mk' (fun z => e ((eH.symm z : HermR (Ainf F) σ m) : Matrix (Fin m) (Fin m) (Ainf F ⊗[F] E)))
        (by intro x y; simp only [hHs, AddSubgroup.coe_add, he])).toRealLinearMap
        (e.continuous.comp (continuous_subtype_val.comp eH.symm.continuous))
    let L₂ : (Fin N → ℝ) →L[ℝ] EuclideanSpace ℝ μ' :=
      (AddMonoidHom.mk' (fun y => eM (Ti * e.symm y)) (by intro x y; simp only [hes, Matrix.mul_add, heM])).toRealLinearMap
        (eM.continuous.comp ((continuous_const.matrix_mul continuous_id).comp e.symm.continuous))
    have hL₁ : ∀ z, L₁ z = e ((eH.symm z : HermR (Ainf F) σ m) : Matrix (Fin m) (Fin m) (Ainf F ⊗[F] E)) := fun z => rfl
    have hL₂ : ∀ y, L₂ y = eM (Ti * e.symm y) := fun y => rfl
    have hfun : (fun z => eM (Ti * g ((eH.symm z : HermR (Ainf F) σ m) : Matrix (Fin m) (Fin m) (Ainf F ⊗[F] E)))) =
        fun z => L₂ ((fun y => e (g (e.symm y))) (L₁ z)) := by
      funext z
      rw [hL₁, hL₂]
      simp only [Homeomorph.symm_apply_apply]
    have hpt : L₁ (eH (hermOf (Ainf F) σ (gramE σ J Y) hT)) = e Tm := by
      rw [hL₁, Homeomorph.symm_apply_apply]; rfl
    have hgcd' : ContDiffAt ℝ 1 (fun y => e (g (e.symm y))) (L₁ (eH (hermOf (Ainf F) σ (gramE σ J Y) hT))) := by
      rw [hpt]; exact hgcd
    have hgd' : HasFDerivAt (fun y => e (g (e.symm y))) ((1 / 2 : ℝ) • ContinuousLinearMap.id ℝ (Fin N → ℝ))
        (L₁ (eH (hermOf (Ainf F) σ (gramE σ J Y) hT))) := by
      rw [hpt]; exact hgd
    have hD := L₂.hasFDerivAt.comp (eH (hermOf (Ainf F) σ (gramE σ J Y) hT)) (hgd'.comp _ L₁.hasFDerivAt)
    refine ⟨?_, ?_⟩
    · show ContDiffAt ℝ 1 (fun z => eM (Ti * g ((eH.symm z : HermR (Ainf F) σ m) : Matrix (Fin m) (Fin m) (Ainf F ⊗[F] E))))
        (eH (hermOf (Ainf F) σ (gramE σ J Y) hT))
      rw [hfun]
      exact L₂.contDiff.contDiffAt.comp _ (hgcd'.comp _ L₁.contDiff.contDiffAt)
    · intro v
      show fderiv ℝ (fun z => eM (Ti * g ((eH.symm z : HermR (Ainf F) σ m) : Matrix (Fin m) (Fin m) (Ainf F ⊗[F] E))))
        (eH (hermOf (Ainf F) σ (gramE σ J Y) hT)) v = _
      have hD' : HasFDerivAt (fun z => L₂ ((fun y => e (g (e.symm y))) (L₁ z))) _
          (eH (hermOf (Ainf F) σ (gramE σ J Y) hT)) := hD
      rw [hfun, hD'.fderiv]
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply,
        map_smul]
      rw [hL₂, hL₁, Homeomorph.symm_apply_apply]

def TinvI {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) : MfI X :=
  (gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u')))⁻¹.map (inclR (Ainf X.B.I.F))

def SquareChartC1 : Prop := ∀ {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ) hT μinf νinf fibInf,
    PushHyp X u' ψ hT μinf νinf fibInf → ∃ Ω a, IsChart X u' hT Ω a ∧
      ∀ {η μ' : Type} [Fintype η] [Fintype μ'] (eH : HmI X ≃ₜ EuclideanSpace ℝ η)
        (eM : MfI X ≃ₜ EuclideanSpace ℝ μ'),
        (∀ x y, eH (x + y) = eH x + eH y) → (∀ x y, eM (x + y) = eM x + eM y) →
        ContDiffAt ℝ 1 (fun z => eM (a (eH.symm z))) (eH (TI X u' hT)) ∧
        ∀ v, fderiv ℝ (fun z => eM (a (eH.symm z))) (eH (TI X u' hT)) v =
          (1 / 2 : ℝ) • eM (TinvI X u' * ((eH.symm v : HmI X) : Matrix _ _ _))

theorem square_chart_c1 : SquareChartC1 := by
  intro D X u' ψ hT μinf νinf fibInf hP
  haveI : IsTotallyReal X.B.I.F := X.B.I.cm.totReal
  haveI : FiniteDimensional X.B.I.F X.B.I.E :=
    Module.finite_of_finrank_pos (by rw [X.B.I.cm.deg2]; norm_num)
  have hσ : ∀ x, X.B.I.cm.sig (X.B.I.cm.sig x) = x := fun x => star_star x
  have hdet := detNZ_holds X u' ψ hT μinf νinf fibInf hP
  obtain ⟨k, eK, hK⟩ := sq_coord_tens X.B.I.F X.B.I.E
  obtain ⟨k1, e1, h1⟩ := sq_coord_pi eK hK (Fin (D.R.rS + 1 + D.R.rS))
  obtain ⟨N, eM, hM⟩ := sq_coord_pi e1 h1 (Fin (D.R.rS + 1 + D.R.rS))
  obtain ⟨Ω, a, h1', h2', h3', h4', h5'⟩ :=
    square_chart_c1_local X.B.I.cm.sig hσ X.B.I.J (tupH (frameOf X u')) hT hdet eM hM
  exact ⟨Ω, a, ⟨h1', h2', h3', fun T hT' => h4' T hT'⟩, fun eH eM' heH heM => h5' eH eM' heH heM⟩

end PI.AprimeInfW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.WittInfHolds
section
noncomputable section

namespace PI.AprimeInfWitt

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField Matrix Formalism.UG PI.VolStabSW.OrbR
open scoped TensorProduct

theorem witt_R {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (h2 : Module.finrank F E = 2) (hfix : ∀ a : E, σ a = a ↔ a ∈ (algebraMap F E).range)
    (hinv : ∀ x, σ (σ x) = x) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J) {a : ℕ}
    (X0 : Fin a → Fin M → E) (hT : ∀ i j, σ (gramE σ J X0 j i) = gramE σ J X0 i j)
    (hdet : (gramE σ J X0).det ≠ 0) (R : Type) [CommRing R] [Algebra F R]
    (hU : PIW.AdelicOrbitU.UnitChoice R) (y : Fin a → Fin M → R ⊗[F] E)
    (hy : gramR R σ J y = (gramE σ J X0).map (inclR R)) :
    ∃ g : HA R σ J, g • ratTup (F := F) R X0 = y := by
  set T := gramE σ J X0 with hTdef
  let sE : E →+* E := σ
  have hTH : IsHerm sE T := by
    ext i j; exact hT i j
  have hh : PI.UnitaryGroupMassFormula.HermConj.IsHermForm sE (Formalism.UG.hform sE T) :=
    { add := fun x y z => by
        rw [PIW.AdelicOrbitU.hform_eq_dot, PIW.AdelicOrbitU.hform_eq_dot,
          PIW.AdelicOrbitU.hform_eq_dot, mulVec_add, dotProduct_add]
      smul := fun x c y => PIW.AdelicOrbitU.hform_smul_right sE T c x y
      herm := fun x y => (PIW.AdelicOrbitU.hform_conj sE T hinv hTH x y).symm }
  obtain ⟨v, hvli, hvo⟩ := PI.UnitaryGroupMassFormula.HermConj.exists_orthogonal_family sE a (Fin a → E)
    (by simp) (Formalism.UG.hform sE T) hh
  set P : Matrix (Fin a) (Fin a) E := tM v with hP
  have hPu : IsUnit P.det := by
    have h1 : IsUnit (Matrix.of v) := Matrix.linearIndependent_rows_iff_isUnit.mp hvli
    have h2 : P = (Matrix.of v)ᵀ := rfl
    rw [h2, det_transpose]
    exact (Matrix.isUnit_iff_isUnit_det _).mp h1
  set D := Formalism.UG.cT sE P * T * P with hD
  have hDv : ∀ j k, Formalism.UG.hform sE T (v j) (v k) = D j k := fun j k => gram_tM sE T v j k
  have hDoff : ∀ j k, j ≠ k → D j k = 0 := fun j k hjk => by rw [← hDv]; exact hvo j k hjk
  have hDdiag : D = Matrix.diagonal fun j => D j j := by
    ext j k
    by_cases hjk : j = k
    · subst hjk; simp
    · rw [hDoff j k hjk, Matrix.diagonal_apply_ne _ hjk]
  have hDdet : D.det ≠ 0 := by
    have hc : (Formalism.UG.cT sE P).det = sE P.det := by
      rw [Formalism.UG.cT, det_transpose, RingHom.map_det]; rfl
    rw [hD, det_mul, det_mul, hc]
    refine mul_ne_zero (mul_ne_zero ?_ hdet) hPu.ne_zero
    exact (map_ne_zero sE).mpr hPu.ne_zero
  have hDne : ∀ j, D j j ≠ 0 := by
    intro j
    rw [hDdiag, det_diagonal] at hDdet
    exact Finset.prod_ne_zero_iff.mp hDdet j (Finset.mem_univ j)
  have hDfix : ∀ j, σ (D j j) = D j j := fun j => by
    rw [← hDv]; exact PIW.AdelicOrbitU.hform_conj sE T hinv hTH _ _

  let sS := Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR R σ
  let JS := JR (F := F) R J
  have hsS : ∀ z, sS (sS z) = z := (PIW.AdelicOrbitU.stFix F E σ h2 hfix R).1
  have hJS : IsHerm sS JS := PIW.AdelicOrbitU.isHerm_JR R σ J hJ.1
  have hJSd : IsUnit JS.det := PIW.AdelicOrbitU.isUnit_det_JR (F := F) R J hJ.2
  have hcTmap : ∀ {p q : ℕ} (N : Matrix (Fin p) (Fin q) E),
      Formalism.UG.cT sS (N.map (inclR (F := F) R)) = (Formalism.UG.cT sE N).map (inclR (F := F) R) := by
    intro p q N; ext i j
    simp only [Formalism.UG.cT, Matrix.map_apply, Matrix.transpose_apply]
    exact PIW.AdelicOrbitU.sigR_inclR (F := F) R σ _
  set Xm : Matrix (Fin M) (Fin a) (R ⊗[F] E) := (tM X0).map (inclR (F := F) R) with hXm
  set Pm : Matrix (Fin a) (Fin a) (R ⊗[F] E) := P.map (inclR (F := F) R) with hPm
  have hTg : Formalism.UG.cT sE (tM X0) * J * tM X0 = T := by
    ext i j; rw [← gram_tM]; rfl
  have hyg : Formalism.UG.cT sS (tM y) * JS * tM y = T.map (inclR (F := F) R) := by
    ext i j; rw [← gram_tM]; exact congrFun (congrFun hy i) j
  let x' : Fin a → Fin M → R ⊗[F] E := fun j r => (Xm * Pm) r j
  let y' : Fin a → Fin M → R ⊗[F] E := fun j r => (tM y * Pm) r j
  have hGx : ∀ j k, Formalism.UG.hform sS JS (x' j) (x' k) = inclR (F := F) R (D j k) := by
    intro j k
    rw [gram_tM]
    have e : tM x' = Xm * Pm := rfl
    rw [e, gram_mul, hXm, hPm, hcTmap, hcTmap]
    show ((Formalism.UG.cT sE P).map (inclR (F := F) R) * ((Formalism.UG.cT sE (tM X0)).map (inclR (F := F) R) * J.map (inclR (F := F) R) *
      (tM X0).map (inclR (F := F) R)) * P.map (inclR (F := F) R)) j k = _
    rw [← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.map_mul, hTg]
    rfl
  have hGy : ∀ j k, Formalism.UG.hform sS JS (y' j) (y' k) = inclR (F := F) R (D j k) := by
    intro j k
    rw [gram_tM]
    have e : tM y' = tM y * Pm := rfl
    rw [e, gram_mul, hyg, hPm, hcTmap, ← Matrix.map_mul, ← Matrix.map_mul]
    rfl
  obtain ⟨g, hgU, hgx⟩ := orb_orth sS JS hsS hJS hJSd a x' y'
    (fun j k hjk => by rw [hGx, hDoff j k hjk, map_zero])
    (fun j k => by rw [hGx, hGy])
    (fun j => by rw [hGx]; exact (isUnit_iff_ne_zero.mpr (hDne j)).map _)
    (fun j t => by
      obtain ⟨β, hβ⟩ := (hfix _).mp (hDfix j)
      have hβ0 : β ≠ 0 := by
        rintro rfl; exact hDne j (by rw [← hβ, map_zero])
      obtain ⟨lam, hlam, hu⟩ := PIW.AdelicOrbitU.stLam F E σ h2 hfix R hU t β hβ0
      refine ⟨lam, hlam, ?_⟩
      rw [hGx, ← hβ, PIW.AdelicOrbitU.inclR_algebraMap]
      exact hu)
  have hmat : (g : Matrix (Fin M) (Fin M) (R ⊗[F] E)) * Xm * Pm = tM y * Pm := by
    ext r j
    rw [Matrix.mul_assoc]
    have := congrFun (hgx j) r
    simpa [x', y', Matrix.mul_apply, mulVec, dotProduct] using this
  have hPmu : IsUnit Pm.det := by
    show IsUnit ((inclR (F := F) R).mapMatrix P).det
    rw [← RingHom.map_det]; exact hPu.map _
  have hmat2 : (g : Matrix (Fin M) (Fin M) (R ⊗[F] E)) * Xm = tM y := by
    have := congrArg (fun N => N * Pm⁻¹) hmat
    simpa only [Matrix.mul_nonsing_inv_cancel_right _ _ hPmu] using this
  refine ⟨(⟨g, hgU⟩ : HR R σ J), ?_⟩
  funext i
  funext r
  show ((g : Matrix (Fin M) (Fin M) (R ⊗[F] E)) *ᵥ ratTup (F := F) R X0 i) r = y i r
  have := congrFun (congrFun hmat2 r) i
  simpa [Xm, tM, ratTup, Matrix.mul_apply, mulVec, dotProduct] using this

end PI.AprimeInfWitt

namespace PI.AprimeInfW

open MeasureTheory Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub
  Formalism.L2.SG.TypedSets Formalism.L2.SG.Pf.NcReal
open scoped TensorProduct

theorem wittInf_holds : WittInf := by
  intro D X u' ψ hT μinf νinf fibInf hP y hy
  have h2 : Module.finrank X.B.I.F X.B.I.E = 2 := X.B.I.cm.deg2
  have hfix : ∀ a : X.B.I.E, X.B.I.cm.sig a = a ↔ a ∈ (algebraMap X.B.I.F X.B.I.E).range :=
    fun a => X.B.I.cm.fixed a
  have hinv : ∀ x, X.B.I.cm.sig (X.B.I.cm.sig x) = x := fun x => star_star x
  have hJ : IsHermND X.B.I.cm.sig X.B.I.J := by
    refine ⟨fun i j => ?_, X.B.I.J_det⟩
    have := congrFun (congrFun X.B.I.J_herm i) j
    simp only [Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply] at this
    exact this
  have hdet := detNZ_holds X u' ψ hT μinf νinf fibInf hP
  have hU : PIW.AdelicOrbitU.UnitChoice (Ainf X.B.I.F) :=
    PIW.AdelicOrbitU.uc_pi (fun v : NumberField.InfinitePlace X.B.I.F => v.Completion)
  have hyG : gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J y =
      (gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u'))).map (inclR (Ainf X.B.I.F)) :=
    Set.mem_singleton_iff.1 (Set.mem_preimage.1 hy.1)
  obtain ⟨g, hg⟩ := PI.AprimeInfWitt.witt_R X.B.I.cm.sig h2 hfix hinv X.B.I.J hJ (tupH (frameOf X u')) hT hdet
    (Ainf X.B.I.F) hU y hyG
  exact ⟨g, hg⟩

end PI.AprimeInfW
end
end

