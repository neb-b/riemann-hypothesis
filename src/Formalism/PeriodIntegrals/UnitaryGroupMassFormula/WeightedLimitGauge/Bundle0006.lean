module

public import Mathlib
public import Formalism.PeriodIntegrals.Bundle0006
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.VolumeLieE
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.HaarUniq
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.RhsHaar
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.Bundle0004
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.Bundle0005
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.MBaseMem
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.Bundle0002

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.RhsWInvDA
section
set_option linter.unusedVariables false

noncomputable section

open MeasureTheory Filter Topology Matrix Set
open scoped ENNReal

namespace PI.RhsWLim.W.RI

theorem polish_of_lcsc (Y : Type) [TopologicalSpace Y] [LocallyCompactSpace Y] [T2Space Y]
    [SecondCountableTopology Y] : PolishSpace Y := by
  let _ := TopologicalSpace.metrizableSpaceMetric Y
  have hemb : IsEmbedding ((↑) : Y → UniformSpace.Completion Y) :=
    (UniformSpace.Completion.isUniformEmbedding_coe Y).isEmbedding
  have hdense : DenseRange ((↑) : Y → UniformSpace.Completion Y) :=
    UniformSpace.Completion.denseRange_coe
  have hopen : IsOpen (range ((↑) : Y → UniformSpace.Completion Y)) := by
    rw [isOpen_iff_forall_mem_open]
    rintro _ ⟨y, rfl⟩
    obtain ⟨K, hK, hKy⟩ := exists_compact_mem_nhds y
    obtain ⟨V, hVK, hVo, hyV⟩ := mem_nhds_iff.1 hKy
    obtain ⟨U, hUo, hUV⟩ := hemb.isInducing.isOpen_iff.1 hVo
    refine ⟨U, ?_, hUo, ?_⟩
    · have hcl : IsClosed (((↑) : Y → UniformSpace.Completion Y) '' K) :=
        (hK.image hemb.continuous).isClosed
      calc U ⊆ closure (U ∩ range ((↑) : Y → UniformSpace.Completion Y)) :=
            hdense.open_subset_closure_inter hUo
        _ ⊆ closure (((↑) : Y → UniformSpace.Completion Y) '' K) := by
            apply closure_mono
            rintro _ ⟨hz, ⟨z, rfl⟩⟩
            refine ⟨z, hVK ?_, rfl⟩
            rw [← hUV]
            exact hz
        _ = ((↑) : Y → UniformSpace.Completion Y) '' K := hcl.closure_eq
        _ ⊆ range ((↑) : Y → UniformSpace.Completion Y) := image_subset_range _ _
    · show y ∈ ((↑) : Y → UniformSpace.Completion Y) ⁻¹' U
      rw [hUV]
      exact hyV
  have : PolishSpace (range ((↑) : Y → UniformSpace.Completion Y)) := hopen.polishSpace
  exact hemb.toHomeomorph.isClosedEmbedding.polishSpace

section Abstract

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

theorem meas_avg (H : Subgroup G) (ν : Measure H) [SFinite ν] {f : G → ℝ≥0∞} (hf : Measurable f) :
    Measurable (fun g : G => ∫⁻ h, f (g * (h : G)) ∂ν) := by
  have hc : Continuous (fun p : G × H => p.1 * (p.2 : G)) :=
    continuous_fst.mul (continuous_subtype_val.comp continuous_snd)
  exact (hf.comp hc.measurable).lintegral_prod_right'

theorem avg_mul_mem (H : Subgroup G) (ν : Measure H) [ν.IsMulLeftInvariant] (f : G → ℝ≥0∞)
    (g : G) (k : H) : ∫⁻ h, f (g * k * (h : G)) ∂ν = ∫⁻ h, f (g * (h : G)) ∂ν := by
  have := lintegral_mul_left_eq_self (μ := ν) (fun h : H => f (g * (h : G))) k
  simpa [mul_assoc] using this

theorem avg_out (H : Subgroup G) (ν : Measure H) [ν.IsMulLeftInvariant] (f : G → ℝ≥0∞) (g : G) :
    ∫⁻ h, f ((g : G ⧸ H).out * (h : G)) ∂ν = ∫⁻ h, f (g * (h : G)) ∂ν := by
  obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul H g
  rw [hk]
  exact avg_mul_mem H ν f g k

theorem meas_avg_q (H : Subgroup G) (ν : Measure H) [SFinite ν] [ν.IsMulLeftInvariant]
    {f : G → ℝ≥0∞} (hf : Measurable f) :
    Measurable (fun q : G ⧸ H => ∫⁻ h, f (q.out * (h : G)) ∂ν) := by
  apply measurable_from_quotient.2
  have : ((fun q : G ⧸ H => ∫⁻ h, f (q.out * (h : G)) ∂ν) ∘ Quotient.mk'') =
      fun g => ∫⁻ h, f (g * (h : G)) ∂ν := by
    funext g
    exact avg_out H ν f g
  rw [this]
  exact meas_avg H ν hf

theorem lint_eq (H : Subgroup G) (ν : Measure H) [ν.IsMulLeftInvariant] [IsFiniteMeasure ν]
    (μ : Measure G) [SFinite μ] (hr : ∀ k : H, μ.map (· * (k : G)) = μ) (f : G → ℝ≥0∞) (hf : Measurable f) :
    ν univ * ∫⁻ g, f g ∂μ =
      ∫⁻ q, (∫⁻ h, f (q.out * (h : G)) ∂ν) ∂(μ.map (QuotientGroup.mk : G → G ⧸ H)) := by
  rw [lintegral_map (meas_avg_q H ν hf) measurable_quotient_mk'']
  have e1 : ∀ g : G, ∫⁻ h, f ((g : G ⧸ H).out * (h : G)) ∂ν = ∫⁻ h, f (g * (h : G)) ∂ν := avg_out H ν f
  rw [lintegral_congr e1]
  have hmeas2 : AEMeasurable (Function.uncurry fun (g : G) (h : H) => f (g * (h : G))) (μ.prod ν) := by
    have hc2 : Continuous (fun p : G × H => p.1 * (p.2 : G)) :=
      continuous_fst.mul (continuous_subtype_val.comp continuous_snd)
    exact (hf.comp hc2.measurable).aemeasurable
  rw [lintegral_lintegral_swap hmeas2]
  have : ∀ h : H, ∫⁻ g, f (g * (h : G)) ∂μ = ∫⁻ g, f g ∂μ := fun h => by
    rw [← lintegral_map hf (measurable_mul_const (h : G)), hr h]
  rw [lintegral_congr this, lintegral_const, mul_comm]

variable {X : Type} [TopologicalSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X]

def iotaQ (H : Subgroup G) (p : G → X) (q : G ⧸ H) : X := p q.out

theorem desc_uniq (H : Subgroup G) (hH : IsClosed (H : Set G)) (ν : Measure H) [ν.IsMulLeftInvariant]
    (h0 : ν univ ≠ 0) (hfin : ν univ ≠ ∞) (p : G → X) (hp : Continuous p)
    (hpH : ∀ g g' : G, p g = p g' ↔ g⁻¹ * g' ∈ H) (μ₁ μ₂ : Measure G) [SFinite μ₁] [SFinite μ₂]
    (h₁ : ∀ k : H, μ₁.map (· * (k : G)) = μ₁) (h₂ : ∀ k : H, μ₂.map (· * (k : G)) = μ₂)
    (hm : μ₁.map p = μ₂.map p) : μ₁ = μ₂ := by
  classical
  haveI : IsFiniteMeasure ν := ⟨lt_top_iff_ne_top.2 hfin⟩
  haveI : IsClosed (H : Set G) := hH
  haveI : PolishSpace G := polish_of_lcsc G
  haveI : PolishSpace (G ⧸ H) := polish_of_lcsc _
  haveI : BorelSpace (G ⧸ H) := CosetSpace.borelSpace
  have hmk : ∀ g : G, iotaQ H p (g : G ⧸ H) = p g := by
    intro g
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul H g
    show p (g : G ⧸ H).out = p g
    rw [hk]
    refine ((hpH g (g * k)).2 ?_).symm
    rw [inv_mul_cancel_left]
    exact k.2
  have hcomp : (iotaQ H p ∘ (QuotientGroup.mk : G → G ⧸ H)) = p := funext hmk
  have hιc : Continuous (iotaQ H p) := by
    rw [(QuotientGroup.isQuotientMap_mk H).continuous_iff, hcomp]
    exact hp
  have hinj : Function.Injective (iotaQ H p) := by
    intro q q' h
    rw [← QuotientGroup.out_eq' q, ← QuotientGroup.out_eq' q', QuotientGroup.eq]
    exact (hpH _ _).1 h
  have hemb : MeasurableEmbedding (iotaQ H p) := hιc.measurableEmbedding hinj
  have hπ : Measurable (QuotientGroup.mk : G → G ⧸ H) := measurable_quotient_mk''
  have hq : μ₁.map (QuotientGroup.mk : G → G ⧸ H) = μ₂.map (QuotientGroup.mk : G → G ⧸ H) := by
    calc μ₁.map (QuotientGroup.mk : G → G ⧸ H)
        = ((μ₁.map (QuotientGroup.mk : G → G ⧸ H)).map (iotaQ H p)).comap (iotaQ H p) :=
          (hemb.comap_map _).symm
      _ = (μ₁.map p).comap (iotaQ H p) := by rw [Measure.map_map hemb.measurable hπ, hcomp]
      _ = (μ₂.map p).comap (iotaQ H p) := by rw [hm]
      _ = ((μ₂.map (QuotientGroup.mk : G → G ⧸ H)).map (iotaQ H p)).comap (iotaQ H p) := by
          rw [Measure.map_map hemb.measurable hπ, hcomp]
      _ = μ₂.map (QuotientGroup.mk : G → G ⧸ H) := hemb.comap_map _
  ext S hS
  have hf : Measurable (S.indicator (1 : G → ℝ≥0∞)) := measurable_one.indicator hS
  have e1 := lint_eq H ν μ₁ h₁ _ hf
  have e2 := lint_eq H ν μ₂ h₂ _ hf
  rw [hq, ← e2, lintegral_indicator_one hS, lintegral_indicator_one hS] at e1
  exact (ENNReal.mul_right_inj h0 hfin).1 e1

end Abstract

end PI.RhsWLim.W.RI
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.RhsWInvO
section
set_option linter.unusedVariables false

noncomputable section

open MeasureTheory Filter Topology Matrix Set
open scoped ENNReal

namespace PI.RhsWLim.W.RI

open PI.RhsWLim PI.RhsWLim.W PI.RhsWLim.W.ZetaZeros

def UnimodK : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (μ : Measure (Mt k r)), IsHaarOn (UWset k r z) μ → μ Set.univ ≠ ⊤ →
    ∀ b ∈ UWset k r z, μ.map (rmulM b) = μ

def FibTrans : Prop :=
  ∀ (k r : ℕ) (z v v' : Fin (2 * r + k + 1) → ℂ), inWb k r z → inWb k r v → inWb k r v' → 0 < Tz k r z →
    herm (Hpk k r) v v = herm (Hpk k r) v' v' → herm (Hpk k r) v z = herm (Hpk k r) v' z →
      ∃ u ∈ UWset k r z, u *ᵥ v = v'

def HypQ : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ), 1 ≤ k → inWb k r z → inWb k r z' → 0 < Tz k r z → 0 < Tz k r z' →
    ∃ Q : Measure (Fin (2 * r + k + 1) → ℂ), SigmaFinite Q ∧ (∀ s ∈ UWb k r, Q.map (fun v => s *ᵥ v) = Q) ∧
      Q {v | ¬ (inWb k r v ∧ herm (Hpk k r) v v = herm (Hpk k r) z' z')} = 0 ∧
      ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧ ∀ g : ℂ → ℝ≥0∞, Measurable g →
        ∫⁻ v, g (herm (Hpk k r) v z) ∂Q = c * ∫⁻ ζ, ENNReal.ofReal (zWeight k (Tz k r z) (Tz k r z') ζ) * g ζ

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {μW μW' : Measure (Mt k r)} {a a' : ℝ}
  {μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ}

def Gf (μW : Measure (Mt k r)) (F : (Fin (2 * r + k + 1) → ℂ) → ℝ≥0∞) (v : Fin (2 * r + k + 1) → ℂ) : ℝ≥0∞ :=
  ∫⁻ h, F (Matrix.of h *ᵥ v) ∂μW

theorem cont_act : Continuous (fun p : (Fin (2 * r + k + 1) → ℂ) × Mt k r => (Matrix.of p.2 : Mat k r) *ᵥ p.1) :=
  Continuous.matrix_mulVec (continuous_snd (X := Fin (2 * r + k + 1) → ℂ) (Y := Mat k r)) continuous_fst

theorem meas_Gf [SFinite μW] {F : (Fin (2 * r + k + 1) → ℂ) → ℝ≥0∞} (hF : Measurable F) : Measurable (Gf μW F) :=
  (hF.comp cont_act.measurable).lintegral_prod_right'

theorem cont_herm (w : Fin (2 * r + k + 1) → ℂ) : Continuous (fun v => herm (Hpk k r) v w) :=
  continuous_const.dotProduct (continuous_const.matrix_mulVec continuous_id)

theorem herm_both {n : ℕ} (H g : Matrix (Fin n) (Fin n) ℂ) (hg : gᴴ * H * g = H) (v w : Fin n → ℂ) :
    herm H (g *ᵥ v) (g *ᵥ w) = herm H v w := by
  unfold herm
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hg]

theorem inWb_Em (u : Fin (k + 1) → ℂ) : inWb k r (MB.Em k r *ᵥ u) := by
  intro i hi
  simp only [Matrix.mulVec, dotProduct, MB.Em]
  refine Finset.sum_eq_zero fun m _ => ?_
  rw [if_neg, zero_mul]
  intro h
  rw [h] at hi
  have := m.isLt
  simp only [wI] at hi
  omega

theorem inWb_emb (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (hz' : inWb k r z') : inWb k r (embWb k r μ *ᵥ z') := by
  rw [← inWb_eq hz', Matrix.mulVec_mulVec, emb_mul_Em, ← Matrix.mulVec_mulVec]
  exact inWb_Em _

theorem rhs_orb (hd : WbData k r z z' μW μW' a a' μsec) (F : (Fin (2 * r + k + 1) → ℂ) → ℝ≥0∞) :
    rhsW k r z z' μW μW' μsec (fun x => F (orbV k r z' x)) = ENNReal.ofReal a' *
      ∫⁻ ζ, ENNReal.ofReal (zWeight k (Tz k r z) (Tz k r z') ζ) * Gf μW F (embWb k r (μsec ζ) *ᵥ z') := by
  unfold rhsW
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_congr fun ζ => ?_
  have inner : ∀ h : Mt k r, ∫⁻ h', F (orbV k r z'
      (fun i j => (Matrix.of h * embWb k r (μsec ζ) * (Matrix.of h')⁻¹) i j)) ∂μW' =
        ENNReal.ofReal a' * F (Matrix.of h *ᵥ (embWb k r (μsec ζ) *ᵥ z')) := by
    intro h
    have hae : ∀ᵐ h' ∂μW', Matrix.of h' ∈ UWset k r z' := by
      rw [ae_iff]
      exact hd.haarW'.2.2.1
    calc ∫⁻ h', F (orbV k r z' (fun i j => (Matrix.of h * embWb k r (μsec ζ) * (Matrix.of h')⁻¹) i j)) ∂μW'
        = ∫⁻ h', F (Matrix.of h *ᵥ (embWb k r (μsec ζ) *ᵥ z')) ∂μW' := by
          refine lintegral_congr_ae ?_
          filter_upwards [hae] with h' hh'
          show F ((Matrix.of h * embWb k r (μsec ζ) * (Matrix.of h')⁻¹) *ᵥ z') =
            F (Matrix.of h *ᵥ (embWb k r (μsec ζ) *ᵥ z'))
          rw [← Matrix.mulVec_mulVec, inv_fix (HU.isUnit_of_uh hh'.1) hh'.2.2, ← Matrix.mulVec_mulVec]
      _ = F (Matrix.of h *ᵥ (embWb k r (μsec ζ) *ᵥ z')) * μW' Set.univ := lintegral_const _
      _ = ENNReal.ofReal a' * F (Matrix.of h *ᵥ (embWb k r (μsec ζ) *ᵥ z')) := by rw [hd.massW', mul_comm]
  simp_rw [inner]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  unfold Gf
  ring

theorem avg_Q (Q : Measure (Fin (2 * r + k + 1) → ℂ)) [SigmaFinite Q] (hQ : ∀ s ∈ UWb k r, Q.map (fun v => s *ᵥ v) = Q)
    (hW : IsHaarOn (UWset k r z) μW) {F : (Fin (2 * r + k + 1) → ℂ) → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ v, Gf μW F v ∂Q = μW Set.univ * ∫⁻ v, F v ∂Q := by
  have := hW.1
  unfold Gf
  rw [lintegral_lintegral_swap (μ := Q) (ν := μW) (f := fun v (h : Mt k r) => F (Matrix.of h *ᵥ v))
    (hF.comp cont_act.measurable).aemeasurable]
  have hae : ∀ᵐ h ∂μW, Matrix.of h ∈ UWset k r z := by
    rw [ae_iff]
    exact hW.2.2.1
  have e : ∀ᵐ h ∂μW, ∫⁻ v, F (Matrix.of h *ᵥ v) ∂Q = ∫⁻ v, F v ∂Q := by
    filter_upwards [hae] with h hh
    have hmv : Measurable (fun v : Fin (2 * r + k + 1) → ℂ => (Matrix.of h : Mat k r) *ᵥ v) :=
      (continuous_const.matrix_mulVec continuous_id).measurable
    rw [← lintegral_map hF hmv, hQ _ ⟨hh.1, hh.2.1⟩]
  rw [lintegral_congr_ae e, lintegral_const, mul_comm]

theorem Gf_fib (hU : UnimodK) (hT : FibTrans) (hW : IsHaarOn (UWset k r z) μW) (hfin : μW Set.univ ≠ ⊤)
    (hz : inWb k r z) (hTz : 0 < Tz k r z) {F : (Fin (2 * r + k + 1) → ℂ) → ℝ≥0∞} (hF : Measurable F)
    {v v' : Fin (2 * r + k + 1) → ℂ} (hv : inWb k r v) (hv' : inWb k r v')
    (h1 : herm (Hpk k r) v v = herm (Hpk k r) v' v') (h2 : herm (Hpk k r) v z = herm (Hpk k r) v' z) :
    Gf μW F v = Gf μW F v' := by
  obtain ⟨u, hu, huv⟩ := hT k r z v' v hz hv' hv hTz h1.symm h2.symm
  have hm : Measurable (fun y : Mt k r => F (Matrix.of y *ᵥ v')) :=
    hF.comp ((cont_act (k := k) (r := r)).comp (Continuous.prodMk continuous_const continuous_id)).measurable
  unfold Gf
  calc ∫⁻ h, F (Matrix.of h *ᵥ v) ∂μW = ∫⁻ h, (fun y : Mt k r => F (Matrix.of y *ᵥ v')) (rmulM u h) ∂μW := by
        refine lintegral_congr fun h => ?_
        show F (Matrix.of h *ᵥ v) = F ((Matrix.of h * u) *ᵥ v')
        rw [← Matrix.mulVec_mulVec, huv]
    _ = ∫⁻ y, F (Matrix.of y *ᵥ v') ∂(μW.map (rmulM u)) := (lintegral_map hm (rmulM_cont u).measurable).symm
    _ = ∫⁻ h, F (Matrix.of h *ᵥ v') ∂μW := by rw [hU k r z μW hW hfin u hu]

end PI.RhsWLim.W.RI
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.TransW
section
set_option linter.unusedVariables false

noncomputable section

open MeasureTheory Filter Topology Matrix ComplexConjugate
open scoped ENNReal

namespace PI.RhsWLim.W

open PI.RhsWLim

variable {k r : ℕ}

def boost (y : Fin k → ℂ) (c : ℂ) : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ := fun i j =>
  Fin.lastCases (Fin.lastCases c (fun j' => ((‖c‖ : ℂ) / conj c) * conj (y j')) j)
    (fun i' => Fin.lastCases (y i')
      (fun j' => (if i' = j' then 1 else 0) + y i' * conj (y j') / (1 + (‖c‖ : ℂ))) j) i

theorem form_apply (A : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (i j : Fin (k + 1)) :
    (Aᴴ * Hb k * A) i j = ∑ l : Fin k, conj (A l.castSucc i) * A l.castSucc j -
      conj (A (Fin.last k) i) * A (Fin.last k) j := by
  rw [Hb, Matrix.mul_apply, Fin.sum_univ_castSucc]
  simp only [Matrix.mul_diagonal, Matrix.conjTranspose_apply, Complex.star_def, Fin.castSucc_ne_last, if_false,
    if_true, mul_one]
  ring

theorem boost_mem (y : Fin k → ℂ) (c : ℂ)
    (hS : ∑ l, conj (y l) * y l = ((‖c‖ : ℝ) : ℂ) ^ 2 - 1) (hc0 : c ≠ 0) :
    (boost y c)ᴴ * Hb k * boost y c = Hb k := by
  have hc : conj c * c = ((‖c‖ : ℝ) : ℂ) ^ 2 := by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring
  have hD : (1 + ((‖c‖ : ℝ) : ℂ)) ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith [norm_nonneg c]
  have hcc : conj c ≠ 0 := by rwa [map_ne_zero]
  have hn0 : ((‖c‖ : ℝ) : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]; exact norm_ne_zero_iff.2 hc0
  have hcb : conj c = ((‖c‖ : ℝ) : ℂ) ^ 2 / c := by
    rw [eq_div_iff hc0]; exact hc
  ext i j
  rw [form_apply]
  induction i using Fin.lastCases with
  | last =>
    induction j using Fin.lastCases with
    | last =>
      simp only [boost, Fin.lastCases_last, Fin.lastCases_castSucc, Hb, Matrix.diagonal_apply_eq, if_true]
      rw [hS, hc]; ring
    | cast j =>
      simp only [boost, Fin.lastCases_last, Fin.lastCases_castSucc, Hb, Matrix.diagonal_apply_ne _ (Fin.castSucc_ne_last j).symm]
      have h1 : ∀ l : Fin k, conj (y l) * ((if l = j then 1 else 0) + y l * conj (y j) / (1 + (‖c‖ : ℂ))) =
          (if l = j then conj (y l) else 0) + (conj (y j) / (1 + (‖c‖ : ℂ))) * (conj (y l) * y l) := by
        intro l; split_ifs <;> ring
      rw [Finset.sum_congr rfl (fun l _ => h1 l), Finset.sum_add_distrib, Finset.sum_ite_eq', ← Finset.mul_sum, hS]
      simp only [Finset.mem_univ, if_true, map_mul, map_div₀, Complex.conj_ofReal, Complex.conj_conj]
      try simp only [hcb]
      field_simp
      ring
  | cast i =>
    induction j using Fin.lastCases with
    | last =>
      simp only [boost, Fin.lastCases_last, Fin.lastCases_castSucc, Hb, Matrix.diagonal_apply_ne _ (Fin.castSucc_ne_last i)]
      have h1 : ∀ l : Fin k, conj ((if l = i then 1 else 0) + y l * conj (y i) / (1 + (‖c‖ : ℂ))) * y l =
          (if l = i then y l else 0) + (y i / (1 + (‖c‖ : ℂ))) * (conj (y l) * y l) := by
        intro l
        simp only [map_add (f := _), map_mul, map_div₀, map_one, Complex.conj_ofReal, Complex.conj_conj]
        split_ifs <;> simp <;> ring
      rw [Finset.sum_congr rfl (fun l _ => h1 l), Finset.sum_add_distrib, Finset.sum_ite_eq', ← Finset.mul_sum, hS]
      simp only [Finset.mem_univ, if_true, map_mul, map_div₀, Complex.conj_ofReal, Complex.conj_conj]
      try simp only [hcb]
      field_simp
      ring
    | cast j =>
      simp only [boost, Fin.lastCases_last, Fin.lastCases_castSucc, Hb, Matrix.diagonal_apply, Fin.castSucc_inj,
        Fin.castSucc_ne_last, if_false]
      have h1 : ∀ l : Fin k, conj ((if l = i then 1 else 0) + y l * conj (y i) / (1 + (‖c‖ : ℂ))) *
          ((if l = j then 1 else 0) + y l * conj (y j) / (1 + (‖c‖ : ℂ))) =
          (if l = i then (if i = j then 1 else 0) else 0) + (if l = i then y i * conj (y j) / (1 + (‖c‖ : ℂ)) else 0) +
            (if l = j then conj (y l) * y i / (1 + (‖c‖ : ℂ)) else 0) +
            (y i * conj (y j) / (1 + (‖c‖ : ℂ)) ^ 2) * (conj (y l) * y l) := by
        intro l
        simp only [map_add (f := _), map_mul, map_div₀, map_one, Complex.conj_ofReal, Complex.conj_conj]
        by_cases hi : l = i <;> by_cases hj : l = j
        · subst hi; subst hj; simp <;> field_simp <;> ring
        · subst hi; simp [hj] <;> field_simp <;> ring
        · subst hj; simp [hi] <;> field_simp <;> ring
        · simp [hi, hj] <;> field_simp <;> ring
      rw [Finset.sum_congr rfl (fun l _ => h1 l), Finset.sum_add_distrib, Finset.sum_add_distrib,
        Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq', Finset.sum_ite_eq', ← Finset.mul_sum, hS]
      simp only [Finset.mem_univ, if_true, map_mul, map_div₀, Complex.conj_ofReal, Complex.conj_conj]
      split_ifs with hij
      · subst hij; try simp only [hcb]; field_simp; ring
      · try simp only [hcb]; field_simp; ring

theorem hermHb_self (v : Fin (k + 1) → ℂ) :
    herm (Hb k) v v = ((∑ l : Fin k, Complex.normSq (v l.castSucc) - Complex.normSq (v (Fin.last k)) : ℝ) : ℂ) := by
  unfold herm
  rw [dotProduct, Fin.sum_univ_castSucc]
  simp only [Hb, Matrix.mulVec_diagonal, Fin.castSucc_ne_last, if_false, if_true, Pi.star_apply, Complex.star_def]
  push_cast [Complex.normSq_eq_conj_mul_self]
  ring

theorem emb_mulVec_out (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (v : Fin (2 * r + k + 1) → ℂ)
    (i : Fin (2 * r + k + 1)) (hi : i.val < r ∨ r + k < i.val) : (embWb k r μ *ᵥ v) i = v i := by
  rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single i]
  · unfold embWb
    rw [dite_eq_right (by omega), if_pos ⟨rfl, by omega⟩, one_mul]
  · intro l _ hl
    unfold embWb
    rw [dite_eq_right (by omega), if_neg (fun h => hl h.1.symm), zero_mul]
  · simp

theorem wLast_inWb (s : ℂ) : inWb k r (s • wLast k r) := by
  intro i hi
  have : i ≠ wI k r (Fin.last k) := by
    intro h; have := congrArg Fin.val h; simp only [wI, Fin.val_last] at this; omega
  simp [wLast, bvec, Pi.single_apply, this]

theorem wbPart_wLast (s : ℂ) (m : Fin (k + 1)) :
    wbPart k r (s • wLast k r) m = if m = Fin.last k then s else 0 := by
  simp only [wbPart, wLast, bvec, Pi.smul_apply, Pi.single_apply, smul_eq_mul]
  by_cases h : m = Fin.last k
  · subst h; simp
  · rw [if_neg (fun h' => h (wI_injective h')), if_neg h, mul_zero]

theorem transW : TransW := by
  intro k r z hz hT
  set T := Tz k r z with hTdef
  set s : ℝ := Real.sqrt T with hsdef
  have hs : 0 < s := Real.sqrt_pos.2 hT
  have hss : s * s = T := Real.mul_self_sqrt hT.le
  have hs0 : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hs.ne'
  set u : Fin (k + 1) → ℂ := fun j => z (wI k r j) / s with hu
  set y : Fin k → ℂ := fun l => u l.castSucc with hy
  set c : ℂ := u (Fin.last k) with hcdef

  have hTform : T = Complex.normSq (z (wI k r (Fin.last k))) - ∑ l : Fin k, Complex.normSq (z (wI k r l.castSucc)) := by
    rw [hTdef, Tz, herm_wb _ _ hz, hermHb_self, Complex.ofReal_re]
    simp only [wbPart]; ring
  have hnq : ∀ a : ℂ, Complex.normSq (a / s) = Complex.normSq a / T := by
    intro a; rw [Complex.normSq_div, Complex.normSq_ofReal, hss]
  have hBA : Complex.normSq c - ∑ l : Fin k, Complex.normSq (y l) = 1 := by
    simp only [hcdef, hy, hu, hnq]
    rw [← Finset.sum_div, ← sub_div, ← hTform, div_self hT.ne']
  have hA0 : 0 ≤ ∑ l : Fin k, Complex.normSq (y l) := Finset.sum_nonneg fun l _ => Complex.normSq_nonneg _
  have hc0 : c ≠ 0 := by
    intro h; rw [h, map_zero] at hBA; linarith
  have hS : ∑ l, conj (y l) * y l = ((‖c‖ : ℝ) : ℂ) ^ 2 - 1 := by
    have e1 : ∑ l, conj (y l) * y l = ((∑ l : Fin k, Complex.normSq (y l) : ℝ) : ℂ) := by
      push_cast [Complex.normSq_eq_conj_mul_self]; rfl
    have e2 : (‖c‖ : ℝ) ^ 2 = Complex.normSq c := (Complex.normSq_eq_norm_sq c).symm
    have hA : ∑ l : Fin k, Complex.normSq (y l) = Complex.normSq c - 1 := by linarith
    rw [e1, ← Complex.ofReal_pow, e2, hA]
    push_cast; ring
  refine ⟨embWb k r (boost y c), MB.emb_mem_UWb (boost_mem y c hS hc0), ?_⟩
  funext i
  by_cases hi : i.val < r ∨ r + k < i.val
  · rw [emb_mulVec_out _ _ i hi, wLast_inWb _ i hi, hz i hi]
  · push Not at hi
    obtain ⟨j, rfl⟩ : ∃ j : Fin (k + 1), wI k r j = i :=
      ⟨⟨i.val - r, by omega⟩, by apply Fin.ext; simp only [wI]; omega⟩
    have e := congrFun (wbPart_emb (boost y c) _ (wLast_inWb (k := k) (r := r) (s : ℂ))) j
    simp only [wbPart] at e
    rw [e, Matrix.mulVec, dotProduct, Finset.sum_eq_single (Fin.last k)]
    · have hb : boost y c j (Fin.last k) = u j := by
        induction j using Fin.lastCases with
        | last => simp [boost, hcdef]
        | cast j' => simp [boost, hy]
      have hw := wbPart_wLast (k := k) (r := r) (s : ℂ) (Fin.last k)
      rw [hb, hw, if_pos rfl]
      simp only [hu]
      field_simp
    · intro m _ hm
      have hw := wbPart_wLast (k := k) (r := r) (s : ℂ) m
      rw [hw, if_neg hm, mul_zero]
    · simp

end PI.RhsWLim.W
end
end

