module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.Bundle0006
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.Bundle0004
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.Bundle0005
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.PolarHyp
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.Bundle0001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.Bundle0003
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.Bundle0008
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.OrbitPushM
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.OrbitPushI
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.Bundle0007
public import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsPrincipalIdealRingOfHenselian
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0043
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermExponentsNonnegAndDefectGroupBound
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LatticeCountBoundFrames
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0090
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0087
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RmulMul
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0079
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0088

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HyperboloidInvariantMeasurePolarForm
section
noncomputable section

open MeasureTheory Matrix
open scoped ENNReal

namespace GlobalTheory.HyperboloidPolar

open PI.RhsWLim PI.RhsWLim.W

variable {k r : ℕ}

theorem opVec_inWb (p : (Fin k → ℂ) × ℂ) : inWb k r (opVec k r p) := by
  intro i hi
  unfold opVec
  rw [dif_neg (by omega), if_neg (by omega)]

theorem wbPart_opVec (p : (Fin k → ℂ) × ℂ) : wbPart k r (opVec k r p) = toW k p := by
  funext m
  have := m.isLt
  unfold wbPart opVec toW wI
  by_cases h : m.val < k
  · rw [dif_pos (by simp only; omega), dif_pos h]
    exact congrArg p.1 (Fin.ext (by simp))
  · rw [dif_neg (by simp only; omega), dif_neg h, if_pos (by simp only; omega)]

theorem opCo_eq (v : Fin (2 * r + k + 1) → ℂ) : opCo k r v = ofW k (wbPart k r v) := rfl

theorem opCo_opVec (p : (Fin k → ℂ) × ℂ) : opCo k r (opVec k r p) = p := by
  rw [opCo_eq, wbPart_opVec, ofW_toW]

theorem eq_of_wbPart {v w : Fin (2 * r + k + 1) → ℂ} (hv : inWb k r v) (hw : inWb k r w)
    (h : wbPart k r v = wbPart k r w) : v = w := by
  funext i
  by_cases hi : i.val < r ∨ r + k < i.val
  · rw [hv i hi, hw i hi]
  · have hm : MB.mid k r i := by constructor <;> omega
    have := congrFun h (MB.midx hm)
    simpa only [wbPart, MB.wI_midx] using this

theorem opVec_opCo {v : Fin (2 * r + k + 1) → ℂ} (hv : inWb k r v) : opVec k r (opCo k r v) = v :=
  eq_of_wbPart (opVec_inWb _) hv (by rw [wbPart_opVec, opCo_eq, toW_ofW])

theorem inWb_uwb {s : Mat k r} (hs : s ∈ UWb k r) {v : Fin (2 * r + k + 1) → ℂ} (hv : inWb k r v) :
    inWb k r (s *ᵥ v) := by
  rw [op_uwb_eq_emb hs]
  exact RI.inWb_emb _ hv

theorem continuous_opVec : Continuous (opVec k r) := by
  refine continuous_pi fun i => ?_
  unfold opVec
  by_cases h : r ≤ i.val ∧ i.val < r + k
  · simp only [dif_pos h]
    exact (continuous_apply _).comp continuous_fst
  · simp only [dif_neg h]
    by_cases h' : i.val = r + k
    · simp only [if_pos h']
      exact continuous_snd
    · simp only [if_neg h']
      exact continuous_const

theorem continuous_opCo : Continuous (opCo k r) :=
  (continuous_pi fun i => continuous_apply (wI k r (Fin.castSucc i))).prodMk
    (continuous_apply (wI k r (Fin.last k)))

theorem herm_opVec (p : (Fin k → ℂ) × ℂ) :
    herm (Hpk k r) (opVec k r p) (opVec k r p) = (qf k p : ℂ) := by
  rw [herm_wb _ _ (opVec_inWb p), wbPart_opVec, qf_eq]
  rfl

theorem herm_self_eq {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) :
    herm (Hpk k r) z z = ((-Tz k r z : ℝ) : ℂ) := by
  unfold Tz
  rw [neg_neg, herm_wb _ _ hz, hermHb_self, Complex.ofReal_re]

def hypAmb (k r : ℕ) (T' : ℝ) : Measure (Fin (2 * r + k + 1) → ℂ) := (hypM k T').map (opVec k r)

theorem hypAmb_sigmaFinite {T' : ℝ} (hT' : 0 < T') : SigmaFinite (hypAmb k r T') := by
  have : IsFiniteMeasureOnCompacts (hypAmb k r T') := by
    refine ⟨fun C hC => ?_⟩
    rw [hypAmb, Measure.map_apply continuous_opVec.measurable hC.measurableSet]
    refine lt_of_le_of_lt (measure_mono ?_) ((hypLF k T' hT').2 _ (hC.image continuous_opCo))
    intro p hp
    exact ⟨_, hp, opCo_opVec p⟩
  infer_instance

theorem hypAmb_inv (hk : 1 ≤ k) {T' : ℝ} (hT' : 0 < T') {s : Mat k r} (hs : s ∈ UWb k r) :
    (hypAmb k r T').map (fun v => s *ᵥ v) = hypAmb k r T' := by
  have hI := hypInv_of lebInvB (coneForm_of hypTh coneVol) k r T' hk hT' s hs
  have hm : Continuous (fun v : Fin (2 * r + k + 1) → ℂ => s *ᵥ v) :=
    continuous_const.matrix_mulVec continuous_id
  have hA : Continuous (opAct k r s) := continuous_opCo.comp (hm.comp continuous_opVec)
  have e : (fun v => s *ᵥ v) ∘ opVec k r = opVec k r ∘ opAct k r s := by
    funext p
    exact (opVec_opCo (inWb_uwb hs (opVec_inWb p))).symm
  rw [hypAmb, Measure.map_map hm.measurable continuous_opVec.measurable, e,
    ← Measure.map_map continuous_opVec.measurable hA.measurable, hI]

theorem hypAmb_conc {z' : Fin (2 * r + k + 1) → ℂ} (hz' : inWb k r z') (hT' : 0 < Tz k r z') :
    hypAmb k r (Tz k r z') {v | ¬ (inWb k r v ∧ herm (Hpk k r) v v = herm (Hpk k r) z' z')} = 0 := by
  have hc : IsClosed {v : Fin (2 * r + k + 1) → ℂ |
      inWb k r v ∧ herm (Hpk k r) v v = herm (Hpk k r) z' z'} := by
    change IsClosed ({v : Fin (2 * r + k + 1) → ℂ | inWb k r v} ∩
      {v : Fin (2 * r + k + 1) → ℂ | herm (Hpk k r) v v = herm (Hpk k r) z' z'})
    apply IsClosed.inter
    · have : {v : Fin (2 * r + k + 1) → ℂ | inWb k r v} =
          ⋂ i : Fin (2 * r + k + 1), ⋂ _ : (i.val < r ∨ r + k < i.val), {v | v i = 0} := by
        ext v
        simp only [inWb, Set.mem_iInter]
        rfl
      show IsClosed {v : Fin (2 * r + k + 1) → ℂ | inWb k r v}
      rw [this]
      exact isClosed_iInter fun i => isClosed_iInter fun _ => isClosed_eq (continuous_apply i) continuous_const
    · apply isClosed_eq
      · unfold herm
        exact continuous_id.star.dotProduct (continuous_const.matrix_mulVec continuous_id)
      · exact continuous_const
  have hm : MeasurableSet {v : Fin (2 * r + k + 1) → ℂ |
      ¬ (inWb k r v ∧ herm (Hpk k r) v v = herm (Hpk k r) z' z')} := hc.measurableSet.compl
  rw [hypAmb, Measure.map_apply continuous_opVec.measurable hm]
  refine measure_mono_null ?_ (hypLF k _ hT').1
  intro p hp hS
  apply hp
  refine ⟨opVec_inWb p, ?_⟩
  rw [herm_opVec, herm_self_eq hz', (hypS_iff _ p).1 hS]

theorem hypAmb_polar (hk : 1 ≤ k) {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hT : 0 < Tz k r z)
    {T' : ℝ} (hT' : 0 < T') (g : ℂ → ℝ≥0∞) (hg : Measurable g) :
    ∫⁻ v, g (herm (Hpk k r) v z) ∂hypAmb k r T' =
      ENNReal.ofReal (2 * Real.pi ^ k / (k - 1).factorial / (2 * Tz k r z ^ k)) *
        ∫⁻ ζ, ENNReal.ofReal (zWeight k (Tz k r z) T' ζ) * g ζ := by
  obtain ⟨p, hp, hpz⟩ := transW k r z hz hT
  set s := Real.sqrt (Tz k r z) with hs
  have hs0 : (s : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]; exact (Real.sqrt_pos.2 hT).ne'
  set zs := ((s : ℂ) • wLast k r) with hzs
  have hgm : Measurable fun v => g (herm (Hpk k r) v zs) := hg.comp (RI.cont_herm zs).measurable
  have hm : Measurable (fun v : Fin (2 * r + k + 1) → ℂ => p⁻¹ *ᵥ v) :=
    (continuous_const.matrix_mulVec continuous_id).measurable
  have step1 : ∫⁻ v, g (herm (Hpk k r) v z) ∂hypAmb k r T' = ∫⁻ v, g (herm (Hpk k r) v zs) ∂hypAmb k r T' := by
    calc ∫⁻ v, g (herm (Hpk k r) v z) ∂hypAmb k r T'
        = ∫⁻ v, (fun y => g (herm (Hpk k r) y zs)) (p⁻¹ *ᵥ v) ∂hypAmb k r T' := by
          refine lintegral_congr fun v => ?_
          rw [← hpz, herm_mulVec_right hp.1]
      _ = ∫⁻ y, g (herm (Hpk k r) y zs) ∂((hypAmb k r T').map (fun v => p⁻¹ *ᵥ v)) :=
          (lintegral_map hgm hm).symm
      _ = _ := by rw [hypAmb_inv hk hT' (HU.uwb_inv hp)]
  set f : (Fin k → ℂ) × ℂ → ℝ≥0∞ := fun v => g (-((s : ℂ) * v.2)) with hf
  have hfm : Measurable f := hg.comp (continuous_const.mul continuous_snd).neg.measurable
  have step2 : ∫⁻ v, g (herm (Hpk k r) v zs) ∂hypAmb k r T' = hypMeas k T' f := by
    rw [hypMeas_eq k T' hfm, hypAmb, lintegral_map hgm continuous_opVec.measurable]
    refine lintegral_congr fun q => ?_
    have e : opVec k r q (wI k r (Fin.last k)) = q.2 := congrArg Prod.snd (opCo_opVec (r := r) q)
    rw [hzs, herm_wLast, e]
  set G : ℝ → ℂ → ℝ≥0∞ := fun _ c => g (-((s : ℂ) * c)) with hGdef
  have hGm : Measurable (Function.uncurry G) :=
    hg.comp (continuous_const.mul continuous_snd).neg.measurable
  have step3 := polarHyp k (Tz k r z) T' hk hT hT' G hGm
  rw [← hs] at step3
  have hcancel : ∀ ζ : ℂ, -((s : ℂ) * -(ζ / (s : ℂ))) = ζ := by
    intro ζ; field_simp
  have e3 : hypMeas k T' f =
      hypMeas k T' (fun v => G ‖(WithLp.equiv 2 (Fin k → ℂ)).symm v.1‖ v.2) := rfl
  rw [step1, step2, e3, step3]
  simp only [hGdef, hcancel]

theorem hypQ : RI.HypQ := by
  intro k r z z' hk hz hz' hT hT'
  refine ⟨hypAmb k r (Tz k r z'), hypAmb_sigmaFinite hT', fun s hs => hypAmb_inv hk hT' hs,
    hypAmb_conc hz' hT', ENNReal.ofReal (2 * Real.pi ^ k / (k - 1).factorial / (2 * Tz k r z ^ k)),
    ?_, ENNReal.ofReal_ne_top, fun g hg => hypAmb_polar hk hz hT hT' g hg⟩
  have := Real.pi_pos
  exact (ENNReal.ofReal_pos.2 (by positivity)).ne'

end GlobalTheory.HyperboloidPolar
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TotalLeGeneric
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.GenMass

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ}


omit [IsNonarchimedeanLocalField F] [CharZero F] in
theorem pair_mem_cls (S : Frames L r k) (g g' : Fin (r + 1) → S.V) : (g, g') ∈ S.frameCls g g' := by
  have h1 : IsIntM L (1 : Matrix (Fin (r + 1)) (Fin (r + 1)) E) := fun i j => by
    rw [Matrix.one_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  refine ⟨1, 1, h1, h1, fun i j h => ?_, fun i => by simp, fun i j => ⟨0, zero_mem _, by simp⟩,
    fun j => ?_, fun j => ?_⟩
  · simp [Matrix.one_apply_ne h.ne']
  · simp [Matrix.one_apply]
  · simp [Matrix.one_apply]


omit [IsNonarchimedeanLocalField F] [CharZero F] in
theorem sumCls_le (S : Frames L r k) (φ : Set S.FrP → ℝ≥0∞) (c : ℝ≥0∞) (h : ∀ C, S.IsCls C → φ C ≤ c) :
    S.sumCls φ ≤ (S.sumCls fun _ => 1) * c := by
  unfold Frames.sumCls
  rw [← ENNReal.tsum_mul_right]
  refine ENNReal.tsum_le_tsum fun o => ?_
  split_ifs with ho
  · rw [mul_one]
    gcongr
    exact h _ ho.1
  · simp

theorem q_pow_le (S : Frames L r k) (e : ℤ) (he0 : 0 ≤ e) (he : e ≤ S.vth + S.a + S.vD) (m : ℕ) :
    (S.q : ℝ≥0∞) ^ (m * e.toNat) ≤ ENNReal.ofReal (S.Hp ^ m) := by
  have hq : 2 ≤ S.q := (GlobalTheory.UnramOrder.order_facts L S.ϖ S.ϖ_irr).2.2.2.2.2.2.1
  have hq1 : (1 : ℝ) ≤ S.q := by exact_mod_cast (by omega : 1 ≤ S.q)
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_pow (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [mul_comm, pow_mul]
  refine pow_le_pow_left₀ (by positivity) ?_ _
  rw [← zpow_natCast, Int.toNat_of_nonneg he0]
  exact zpow_le_zpow_right₀ hq1 he

omit [IsNonarchimedeanLocalField F] [CharZero F] in
theorem vth_nonneg (S : Frames L r k) : 0 ≤ S.vth := by
  unfold Frames.vth
  split_ifs <;> norm_num

theorem total_weight_le (S : Frames L r k) (ha : 0 ≤ S.a) (hD : 0 ≤ S.vD) :
    (S.sumCls fun _ => 1) ≤ ENNReal.ofReal (S.Hp ^ (r * (r + 1))) := by
  have hv := vth_nonneg S
  exact ((GlobalTheory.HL.ClassCount.sumCls_le_encard L r k S).trans (GlobalTheory.IntClsCount.main L r k S hD)).trans
    (q_pow_le S _ (by omega) (by omega) _)

theorem sumCls_eq_single (S : Frames L r k) (h1 : (S.sumCls fun _ => 1) ≤ 1) (φ : Set S.FrP → ℝ≥0∞)
    (hφ : ∀ h ∈ S.St, ∀ C, φ (h • C) = φ C) (C : Set S.FrP) (hC : S.IsIntCls C) :
    S.sumCls φ = ENNReal.ofReal (S.wC C) * φ C := by
  let o' : MulAction.orbitRel.Quotient S.St (Set S.FrP) := Quotient.mk _ C
  obtain ⟨h, hh⟩ : o'.out ∈ MulAction.orbit S.St C :=
    MulAction.orbitRel_apply.1 (Quotient.mk_out (s := MulAction.orbitRel S.St (Set S.FrP)) _)
  have hh' : h.1 • C = o'.out := hh
  have ho' : S.IsIntCls o'.out := hh' ▸ GlobalTheory.HL.ClassCount.isIntCls_smul S h.2 hC
  unfold Frames.sumCls at h1 ⊢
  rw [tsum_eq_single o', if_pos ho', ← hh', hφ _ h.2, ((GlobalTheory.HL.volSt L r k S).2 C hC.1).2.2.2 _ h.2]
  intro o hne
  refine if_neg fun ho => ?_
  have h2 := (ENNReal.sum_le_tsum {o, o'}).trans h1
  rw [Finset.sum_pair hne, if_pos ho, if_pos ho', mul_one, mul_one] at h2
  have h3 := ENNReal.one_le_ofReal.2 ((GlobalTheory.HL.volSt L r k S).2 _ ho.1).2.2.1
  have h4 := ENNReal.one_le_ofReal.2 ((GlobalTheory.HL.volSt L r k S).2 _ ho'.1).2.2.1
  have h5 := (add_le_add h3 h4).trans h2
  norm_num at h5

end GlobalTheory.HL.GenMass


open GlobalTheory.HL.GenMass in
theorem GlobalTheory.HL.GenMass.total_le_generic : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), 4 * r + 7 ≤ k → ∀ d₁ Λ₁, S.IsTerm d₁ Λ₁ → ∀ g : ℝ≥0∞, g = ENNReal.ofReal (S.wC (S.Fr d₁ Λ₁)) * (S.sumData fun d => S.nT d (S.Fr d₁ Λ₁) fun Λ => S.BBzero d Λ) → 0 < g ∧ g < ⊤ ∧ S.nn ≤ ENNReal.ofReal (8 * S.Hp ^ (9 * (r + 1) ^ 2 + 2 * (2 * r + 2))) * g ∧ (S.Hp = 1 → S.nn = g) := by
  intro F _ _ _ _ _ E _ _ _ L r k S hk d₁ Λ₁ hT g hg
  obtain ⟨hSD, -, hMs, -, -, -, hI, -⟩ := GlobalTheory.HL.TermBasic.term_basic L r k S d₁ Λ₁ hT
  obtain ⟨ha, hD, -, -, hH, -⟩ := GlobalTheory.HL.Defect.exponents_and_defect L r k S d₁ Λ₁ hT
  obtain ⟨κ, hκ, hU⟩ := _root_.GlobalTheory.HL.FrameMass.mass_trace L r k S (by omega) ⟨Λ₁, hSD⟩
  have hv := vth_nonneg S
  have hp : (S.fr d₁ Λ₁, S.fr' d₁ Λ₁) ∈ S.Fr d₁ Λ₁ := pair_mem_cls S _ _
  have hsw := _root_.GlobalTheory.HL.sumData_mass_eq_sumCls L r k S (fun _ _ => True) (fun _ _ _ _ _ _ => trivial)
  have hnn : S.nn = S.sumCls fun C => S.sumData fun d => S.nT d C fun _ => True := hsw.1
  have hM := hU _ hI.1 _ hp (S.M d₁ Λ₁) le_rfl (fun x hx => (hMs hx).2)
    (fun x hx y hy => (hSD.2 y).2 (hMs hy).1 x (hMs hx).1)
  have hM' : ENNReal.ofReal (κ / 2) ≤ S.massSig (S.M d₁ Λ₁) ∧
      S.massSig (S.M d₁ Λ₁) ≤ ENNReal.ofReal (2 * κ) := by
    simpa [Frames.M] using hM
  have hg' : g = ENNReal.ofReal (S.wC (S.Fr d₁ Λ₁)) * S.massSig (S.M d₁ Λ₁) := by
    rw [hg, (_root_.GlobalTheory.HL.ClassMass.class_mass L r k S _ hI.1 _ hp).2]
    rfl
  have hw := ENNReal.one_le_ofReal.2 ((GlobalTheory.HL.volSt L r k S).2 _ hI.1).2.2.1
  have hlow : ENNReal.ofReal (κ / 2) ≤ g := by
    rw [hg', ← one_mul (ENNReal.ofReal (κ / 2))]
    exact mul_le_mul' hw hM'.1
  refine ⟨(ENNReal.ofReal_pos.2 (by positivity)).trans_le hlow, ?_, ?_, fun h1 => ?_⟩
  · rw [hg']
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hM'.2.trans_lt ENNReal.ofReal_lt_top)
  · have hφ : ∀ C, S.IsCls C → (S.sumData fun d => S.nT d C fun _ => True) ≤
        ENNReal.ofReal (S.Hp ^ (2 * (2 * r + 2))) * ENNReal.ofReal (2 * κ) := by
      intro C hC
      obtain ⟨p, hpC⟩ : ∃ p, p ∈ C := by
        obtain ⟨n, -, n', -, rfl⟩ := hC
        exact ⟨_, pair_mem_cls S _ _⟩
      refine ((_root_.GlobalTheory.HL.ClassMass.class_mass L r k S C hC p hpC).1 fun _ => True).trans ?_
      refine (ENNReal.tsum_le_tsum (g := fun _ => ENNReal.ofReal (2 * κ)) fun Mh => ?_).trans ?_
      · refine (hU C hC p hpC Mh.1 Mh.2.1 Mh.2.2.1 Mh.2.2.2.1).2.trans (ENNReal.ofReal_le_ofReal ?_)
        refine mul_le_of_le_one_right (by positivity) ?_
        rw [← Nat.cast_pow]
        exact Nat.cast_inv_le_one _
      · have hc := GlobalTheory.FrameOver.encard_overlattices_le L r k S C hC p hpC ha
        have he : 2 * S.a.toNat * (2 * r + 2) = 2 * (2 * r + 2) * S.a.toNat := by ring
        rw [he] at hc
        have hc' := hc.trans (q_pow_le S _ ha (by omega) _)
        rw [ENNReal.tsum_const]
        refine mul_le_mul_left (le_trans (le_of_eq ?_) hc') _
        simp only [and_true]
        rfl
    rw [hnn]
    refine (sumCls_le S _ _ hφ).trans ?_
    refine (mul_le_mul_left (total_weight_le S ha hD) _).trans ?_
    refine le_trans ?_ (mul_le_mul_right hlow _)
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have h2 : S.Hp ^ (r * (r + 1)) * S.Hp ^ (2 * (2 * r + 2)) ≤
        S.Hp ^ (9 * (r + 1) ^ 2 + 2 * (2 * r + 2)) := by
      rw [← pow_add]
      exact pow_le_pow_right₀ hH (by nlinarith)
    have h3 : 0 ≤ S.Hp ^ (9 * (r + 1) ^ 2 + 2 * (2 * r + 2)) := by positivity
    nlinarith [mul_le_mul_of_nonneg_right h2 hκ.le, mul_nonneg h3 hκ.le]
  · have hq : 2 ≤ S.q := (GlobalTheory.UnramOrder.order_facts L S.ϖ S.ϖ_irr).2.2.2.2.2.2.1
    have hB : ∀ d Λ, S.IsTerm d Λ → S.BBzero d Λ := fun d Λ h => by
      by_contra hc
      have h2 := (GlobalTheory.HL.Defect.exponents_and_defect L r k S d Λ h).2.2.2.2.2.2.2.1 hc
      rw [h1] at h2
      have : S.q ≤ 1 := by exact_mod_cast h2
      omega
    have htw := total_weight_le S ha hD
    rw [h1, one_pow, ENNReal.ofReal_one] at htw
    rw [hnn, sumCls_eq_single S htw _ (fun h hh C => by simp only [hsw.2 h hh]) _ hI, hg]
    congr 2
    funext d
    unfold Frames.nT
    congr 2
    ext Λ
    exact ⟨fun h => ⟨h.1, hB _ _ h.1, h.2.2⟩, fun h => ⟨h.1, trivial, h.2.2⟩⟩
end

