module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0010
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NormStepsLeviElt
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NormStepsSIdem
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NormStepsLeviFrame
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.DualCoords
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ScalarFramePfD

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacConstBHModel
section
noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace Formalism.L2.SG.Pf.BH.Model

def sqs {n : ℕ} (w : Fin n → ℝ) : ℝ := ∑ i, (w i) ^ 2

theorem norm_sq_euclid {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) : ‖x‖ ^ 2 = ∑ i, (WithLp.ofLp x i) ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Real.norm_eq_abs, sq_abs]

theorem euclid_prod (a b : ℕ) (F : ℝ → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ x : EuclideanSpace ℝ (Fin a), ∫⁻ y : EuclideanSpace ℝ (Fin b), F (‖x‖ ^ 2 + ‖y‖ ^ 2) =
      ∫⁻ z : EuclideanSpace ℝ (Fin (a + b)), F (‖z‖ ^ 2) := by

  have hA := PiLp.volume_preserving_ofLp (Fin a)
  have hB := PiLp.volume_preserving_ofLp (Fin b)
  have hC := PiLp.volume_preserving_ofLp (Fin (a + b))
  have hEa : MeasurableEmbedding (@WithLp.ofLp 2 (Fin a → ℝ)) := (MeasurableEquiv.toLp 2 (Fin a → ℝ)).symm.measurableEmbedding
  have hEb : MeasurableEmbedding (@WithLp.ofLp 2 (Fin b → ℝ)) := (MeasurableEquiv.toLp 2 (Fin b → ℝ)).symm.measurableEmbedding
  have hEc : MeasurableEmbedding (@WithLp.ofLp 2 (Fin (a + b) → ℝ)) :=
    (MeasurableEquiv.toLp 2 (Fin (a + b) → ℝ)).symm.measurableEmbedding
  have e1 : ∀ x : EuclideanSpace ℝ (Fin a), ‖x‖ ^ 2 = sqs (WithLp.ofLp x) := norm_sq_euclid
  have e2 : ∀ y : EuclideanSpace ℝ (Fin b), ‖y‖ ^ 2 = sqs (WithLp.ofLp y) := norm_sq_euclid
  have e3 : ∀ z : EuclideanSpace ℝ (Fin (a + b)), ‖z‖ ^ 2 = sqs (WithLp.ofLp z) := norm_sq_euclid
  simp_rw [e1, e2, e3]
  rw [hC.lintegral_comp_emb hEc (fun w => F (sqs w))]
  have inner : ∀ x : EuclideanSpace ℝ (Fin a), ∫⁻ y : EuclideanSpace ℝ (Fin b), F (sqs (WithLp.ofLp x) + sqs (WithLp.ofLp y)) =
      ∫⁻ q : Fin b → ℝ, F (sqs (WithLp.ofLp x) + sqs q) :=
    fun x => hB.lintegral_comp_emb hEb (fun q => F (sqs (WithLp.ofLp x) + sqs q))
  simp_rw [inner]
  rw [hA.lintegral_comp_emb hEa (fun p => ∫⁻ q : Fin b → ℝ, F (sqs p + sqs q))]

  have hS : Measurable fun w : Fin (a + b) → ℝ => sqs w := by unfold sqs; fun_prop
  have hsum := volume_measurePreserving_sumPiEquivProdPi (fun _ : Fin a ⊕ Fin b => ℝ)
  have hcong := volume_measurePreserving_piCongrLeft (fun _ : Fin (a + b) => ℝ) finSumFinEquiv
  rw [← hcong.lintegral_comp_emb (MeasurableEquiv.piCongrLeft _ finSumFinEquiv).measurableEmbedding]
  rw [← hsum.symm.lintegral_comp_emb (MeasurableEquiv.sumPiEquivProdPi _).symm.measurableEmbedding]
  rw [Measure.volume_eq_prod, lintegral_prod _ ?meas]
  · refine lintegral_congr fun p => lintegral_congr fun q => ?_
    congr 1
    symm
    unfold sqs
    rw [← Equiv.sum_comp finSumFinEquiv, Fintype.sum_sum_type]
    have h1 : ∀ (g : Fin a ⊕ Fin b → ℝ) (i : Fin a),
        (Equiv.piCongrLeft (fun _ => ℝ) finSumFinEquiv) g (Fin.castAdd b i) = g (Sum.inl i) := fun g i => by
      rw [← finSumFinEquiv_apply_left, Equiv.piCongrLeft_apply_apply]
    have h2 : ∀ (g : Fin a ⊕ Fin b → ℝ) (i : Fin b),
        (Equiv.piCongrLeft (fun _ => ℝ) finSumFinEquiv) g (Fin.natAdd a i) = g (Sum.inr i) := fun g i => by
      rw [← finSumFinEquiv_apply_right, Equiv.piCongrLeft_apply_apply]
    simp [MeasurableEquiv.piCongrLeft, MeasurableEquiv.sumPiEquivProdPi, h1, h2, Equiv.sumPiEquivProdPi]
  · exact ((hF.comp hS).comp (MeasurableEquiv.piCongrLeft _ finSumFinEquiv).measurable).comp
      (MeasurableEquiv.sumPiEquivProdPi _).symm.measurable |>.aemeasurable

end Formalism.L2.SG.Pf.BH.Model

namespace Formalism.L2.SG.Pf.BH.Model

theorem euclid_cast (a b : ℕ) (h : a = b) (F : ℝ → ℝ≥0∞) :
    ∫⁻ z : EuclideanSpace ℝ (Fin a), F (‖z‖ ^ 2) = ∫⁻ z : EuclideanSpace ℝ (Fin b), F (‖z‖ ^ 2) := by
  subst h; rfl

theorem ip_to_euclid (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (F : ℝ → ℝ≥0∞) :
    ∫⁻ y : E, F (‖y‖ ^ 2) = ∫⁻ x : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)), F (‖x‖ ^ 2) := by
  let φ := (stdOrthonormalBasis ℝ E).repr
  have hφ : MeasurePreserving φ := φ.measurePreserving
  have he : MeasurableEmbedding φ := φ.toHomeomorph.measurableEmbedding
  rw [← hφ.lintegral_comp_emb he (fun x => F (‖x‖ ^ 2))]
  refine lintegral_congr fun y => ?_
  rw [LinearIsometryEquiv.norm_map]

theorem cplx_step (m : ℕ) (F : ℝ → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ w : ℂ, ∫⁻ x : EuclideanSpace ℝ (Fin m), F (2 * ‖w‖ ^ 2 + ‖x‖ ^ 2) =
      2⁻¹ * ∫⁻ z : EuclideanSpace ℝ (Fin (2 + m)), F (‖z‖ ^ 2) := by
  set G : ℝ → ℝ≥0∞ := fun t => ∫⁻ x : EuclideanSpace ℝ (Fin m), F (t + ‖x‖ ^ 2) with hG
  have hGm : Measurable G := by
    have : Measurable fun p : ℝ × EuclideanSpace ℝ (Fin m) => F (p.1 + ‖p.2‖ ^ 2) := hF.comp (by fun_prop)
    exact this.lintegral_prod_right'

  have hs : (Real.sqrt 2) ≠ 0 := by positivity
  have hmap := Measure.map_addHaar_smul (volume : Measure ℂ) hs
  have e1 : ∀ w : ℂ, 2 * ‖w‖ ^ 2 = ‖(Real.sqrt 2) • w‖ ^ 2 := by
    intro w; rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, Real.sq_sqrt (by norm_num)]
  have step1 : ∫⁻ w : ℂ, G (2 * ‖w‖ ^ 2) = 2⁻¹ * ∫⁻ w : ℂ, G (‖w‖ ^ 2) := by
    simp_rw [e1]
    have hmeas : Measurable fun w : ℂ => G (‖w‖ ^ 2) := hGm.comp (by fun_prop)
    rw [← lintegral_map hmeas (by fun_prop : Measurable fun w : ℂ => (Real.sqrt 2) • w), hmap,
      lintegral_smul_measure, Complex.finrank_real_complex]
    congr 1
    rw [show Real.sqrt 2 ^ 2 = 2 by rw [Real.sq_sqrt (by norm_num)]]
    rw [abs_of_pos (by norm_num : (0 : ℝ) < 2⁻¹), ENNReal.ofReal_inv_of_pos (by norm_num)]
    simp

  have step2 : ∫⁻ w : ℂ, G (‖w‖ ^ 2) = ∫⁻ y : EuclideanSpace ℝ (Fin 2), G (‖y‖ ^ 2) := by
    have h1 := Complex.volume_preserving_equiv_pi
    have h2 := PiLp.volume_preserving_ofLp (Fin 2)
    have he2 : MeasurableEmbedding (@WithLp.ofLp 2 (Fin 2 → ℝ)) :=
      (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).symm.measurableEmbedding
    calc ∫⁻ w : ℂ, G (‖w‖ ^ 2) = ∫⁻ w : ℂ, G (sqs (Complex.measurableEquivPi w)) := by
          refine lintegral_congr fun w => ?_
          congr 1
          rw [Complex.measurableEquivPi_apply, sqs, Fin.sum_univ_two, Complex.sq_norm, Complex.normSq_apply]
          simp; ring
      _ = ∫⁻ p : Fin 2 → ℝ, G (sqs p) :=
          h1.lintegral_comp_emb Complex.measurableEquivPi.measurableEmbedding (fun p => G (sqs p))
      _ = ∫⁻ y : EuclideanSpace ℝ (Fin 2), G (sqs (WithLp.ofLp y)) :=
          (h2.lintegral_comp_emb he2 (fun p => G (sqs p))).symm
      _ = ∫⁻ y : EuclideanSpace ℝ (Fin 2), G (‖y‖ ^ 2) := by
          refine lintegral_congr fun y => ?_
          rw [norm_sq_euclid]; rfl
  have hmain : ∫⁻ w : ℂ, ∫⁻ x : EuclideanSpace ℝ (Fin m), F (2 * ‖w‖ ^ 2 + ‖x‖ ^ 2) = ∫⁻ w : ℂ, G (2 * ‖w‖ ^ 2) := rfl
  rw [hmain, step1, step2]
  congr 1
  exact euclid_prod 2 m F hF

end Formalism.L2.SG.Pf.BH.Model

namespace Formalism.L2.SG.Pf.BH.Model

theorem cpow_step (r : ℕ) : ∀ (m : ℕ) (F : ℝ → ℝ≥0∞), Measurable F →
    ∫⁻ u : Fin r → ℂ, ∫⁻ x : EuclideanSpace ℝ (Fin m), F (2 * ∑ a, ‖u a‖ ^ 2 + ‖x‖ ^ 2) =
      (2 ^ r)⁻¹ * ∫⁻ z : EuclideanSpace ℝ (Fin (2 * r + m)), F (‖z‖ ^ 2) := by
  induction r with
  | zero =>
    intro m F hF
    rw [MeasureTheory.volume_pi, Measure.pi_of_empty, lintegral_dirac]
    simp only [Finset.univ_eq_empty, Finset.sum_empty, mul_zero, zero_add, pow_zero, inv_one, one_mul]
    exact euclid_cast m (2 * 0 + m) (by ring) F
  | succ r ih =>
    intro m F hF
    have hp := measurePreserving_piFinSuccAbove (fun _ : Fin (r + 1) => (volume : Measure ℂ)) 0
    have hmeasH : Measurable fun u : Fin (r + 1) → ℂ =>
        ∫⁻ x : EuclideanSpace ℝ (Fin m), F (2 * ∑ a, ‖u a‖ ^ 2 + ‖x‖ ^ 2) := by
      have : Measurable fun p : (Fin (r + 1) → ℂ) × EuclideanSpace ℝ (Fin m) =>
          F (2 * ∑ a, ‖p.1 a‖ ^ 2 + ‖p.2‖ ^ 2) := hF.comp (by fun_prop)
      exact this.lintegral_prod_right'
    rw [MeasureTheory.volume_pi, ← hp.symm.lintegral_comp_emb
      (MeasurableEquiv.piFinSuccAbove (fun _ => ℂ) 0).symm.measurableEmbedding]
    have hsplit : ∀ p : ℂ × (Fin r → ℂ), ∑ a, ‖(MeasurableEquiv.piFinSuccAbove (fun _ => ℂ) 0).symm p a‖ ^ 2 =
        ‖p.1‖ ^ 2 + ∑ a, ‖p.2 a‖ ^ 2 := by
      intro p
      rw [Fin.sum_univ_succ]
      simp [MeasurableEquiv.piFinSuccAbove, Fin.insertNth_zero']
    simp_rw [hsplit]
    rw [lintegral_prod _ ?meas]
    · have inner : ∀ w : ℂ, ∫⁻ u' : Fin r → ℂ, ∫⁻ x : EuclideanSpace ℝ (Fin m),
          F (2 * (‖w‖ ^ 2 + ∑ a, ‖u' a‖ ^ 2) + ‖x‖ ^ 2) ∂volume ∂(Measure.pi fun _ => volume) =
          (2 ^ r)⁻¹ * ∫⁻ z : EuclideanSpace ℝ (Fin (2 * r + m)), F (2 * ‖w‖ ^ 2 + ‖z‖ ^ 2) := by
        intro w
        have := ih m (fun t => F (2 * ‖w‖ ^ 2 + t)) (hF.comp (by fun_prop))
        rw [← MeasureTheory.volume_pi]
        rw [← this]
        refine lintegral_congr fun u' => lintegral_congr fun x => ?_
        congr 1; ring
      simp_rw [inner]
      rw [lintegral_const_mul' _ _ (by simp), cplx_step (2 * r + m) F hF,
        euclid_cast (2 + (2 * r + m)) (2 * (r + 1) + m) (by ring) F, ← mul_assoc, pow_succ,
        ENNReal.mul_inv (by simp) (by simp)]
    · have : Measurable fun q : (ℂ × (Fin r → ℂ)) × EuclideanSpace ℝ (Fin m) =>
          F (2 * (‖q.1.1‖ ^ 2 + ∑ a, ‖q.1.2 a‖ ^ 2) + ‖q.2‖ ^ 2) := hF.comp (by fun_prop)
      exact this.lintegral_prod_right'.aemeasurable

end Formalism.L2.SG.Pf.BH.Model

namespace Formalism.L2.SG.Pf.BH.Model

theorem enn_sq {E : Type*} [NormedAddCommGroup E] (y : E) : ((‖y‖₊ : ℝ≥0∞)) ^ 2 = ENNReal.ofReal (‖y‖ ^ 2) := by
  rw [ENNReal.ofReal_pow (norm_nonneg y), ENNReal.ofReal, norm_toNNReal]

theorem modelVol : Formalism.L2.SG.Pf.BH.ModelVol := by
  intro E1 E2 _ _ _ _ _ _ _ _ _ _ r s hs
  set G : ℝ → ℝ≥0∞ := fun t => if t < s ^ 2 then 1 else 0 with hG
  have hGm : Measurable G := Measurable.ite measurableSet_Iio measurable_const measurable_const
  have hs2 : 0 < s ^ 2 := by positivity

  have hint : ∀ (c : Fin r → ℂ) (y1 : E1) (y2 : E2) (y3 : E1),
      (if (‖y1‖₊ : ℝ≥0∞) ^ 2 + ENNReal.ofReal (2 * ∑ a, ‖c a - 1‖ ^ 2) + (‖y2‖₊ : ℝ≥0∞) ^ 2 + (‖y3‖₊ : ℝ≥0∞) ^ 2 <
          ENNReal.ofReal (s ^ 2) then (1 : ℝ≥0∞) else 0) =
        G (2 * ∑ a, ‖c a - 1‖ ^ 2 + (‖y1‖ ^ 2 + (‖y2‖ ^ 2 + ‖y3‖ ^ 2))) := by
    intro c y1 y2 y3
    have hB : 0 ≤ 2 * ∑ a, ‖c a - 1‖ ^ 2 := by positivity
    rw [enn_sq, enn_sq, enn_sq, ← ENNReal.ofReal_add (by positivity) hB, ← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    simp only [ENNReal.ofReal_lt_ofReal_iff hs2, hG]
    split_ifs with h1 h2 h2 <;> first | rfl | (exfalso; linarith)
  simp_rw [hint]

  have step : ∀ B : ℝ, ∫⁻ y1 : E1, ∫⁻ y2 : E2, ∫⁻ y3 : E1, G (B + (‖y1‖ ^ 2 + (‖y2‖ ^ 2 + ‖y3‖ ^ 2))) =
      ∫⁻ w : EuclideanSpace ℝ (Fin (Module.finrank ℝ E1 + (Module.finrank ℝ E2 + Module.finrank ℝ E1))),
        G (B + ‖w‖ ^ 2) := by
    intro B
    have s3 : ∀ t : ℝ, ∫⁻ y2 : E2, ∫⁻ y3 : E1, G (B + (t + (‖y2‖ ^ 2 + ‖y3‖ ^ 2))) =
        ∫⁻ z : EuclideanSpace ℝ (Fin (Module.finrank ℝ E2 + Module.finrank ℝ E1)), G (B + (t + ‖z‖ ^ 2)) := by
      intro t
      have a1 : ∀ y2 : E2, ∫⁻ y3 : E1, G (B + (t + (‖y2‖ ^ 2 + ‖y3‖ ^ 2))) =
          ∫⁻ x3 : EuclideanSpace ℝ (Fin (Module.finrank ℝ E1)), G (B + (t + (‖y2‖ ^ 2 + ‖x3‖ ^ 2))) :=
        fun y2 => ip_to_euclid E1 (fun u => G (B + (t + (‖y2‖ ^ 2 + u))))
      simp_rw [a1]
      rw [ip_to_euclid E2 (fun u => ∫⁻ x3 : EuclideanSpace ℝ (Fin (Module.finrank ℝ E1)), G (B + (t + (u + ‖x3‖ ^ 2))))]
      exact euclid_prod _ _ (fun u => G (B + (t + u))) (hGm.comp (by fun_prop))
    simp_rw [s3]
    rw [ip_to_euclid E1 (fun u => ∫⁻ z : EuclideanSpace ℝ (Fin (Module.finrank ℝ E2 + Module.finrank ℝ E1)),
      G (B + (u + ‖z‖ ^ 2)))]
    exact euclid_prod _ _ (fun u => G (B + u)) (hGm.comp (by fun_prop))
  simp_rw [step]

  have htr := lintegral_add_left_eq_self (μ := (volume : Measure (Fin r → ℂ)))
    (fun c : Fin r → ℂ => ∫⁻ w : EuclideanSpace ℝ (Fin (Module.finrank ℝ E1 + (Module.finrank ℝ E2 + Module.finrank ℝ E1))),
      G (2 * ∑ a, ‖c a - 1‖ ^ 2 + ‖w‖ ^ 2)) 1
  rw [← htr]
  simp only [Pi.add_apply, Pi.one_apply, add_sub_cancel_left]
  rw [cpow_step r _ G hGm]

  have hball : ∀ (n : ℕ), ∫⁻ z : EuclideanSpace ℝ (Fin n), G (‖z‖ ^ 2) = volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) s) := by
    intro n
    rw [← lintegral_indicator_one measurableSet_ball]
    refine lintegral_congr fun z => ?_
    simp only [hG, Set.indicator, Metric.mem_ball, dist_zero_right, Pi.one_apply]
    congr 1
    apply propext
    constructor
    · intro h; exact lt_of_pow_lt_pow_left₀ 2 hs.le h
    · intro h; exact pow_lt_pow_left₀ h (norm_nonneg _) two_ne_zero
  rw [euclid_cast _ (2 * Module.finrank ℝ E1 + 2 * r + Module.finrank ℝ E2) (by ring) G, hball,
    ENNReal.ofReal_inv_of_pos (by positivity), ENNReal.ofReal_pow (by norm_num)]
  simp

end Formalism.L2.SG.Pf.BH.Model
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NormStepsLeviOntoSEnd
section
noncomputable section

open scoped Classical TensorProduct
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.PoincareInHH.PoincareSetting

namespace Formalism.L2.SG.Pf.NormSteps

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} (TR : TypedRed X) {u : D.what₂.Word}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)} (cs : ColSys X u what₂)

theorem leviOntoS_of_frame (hF : LeviOntoSPf.FrameOfS X u) : LeviOntoS TR cs :=
  LeviOntoSPf.leviOntoS_of_steps TR u cs (LeviOntoSPf.SIdemPf.idempotent_places_exists X) hF
    (LeviOntoSPf.LeviEltPf.levi_element_exists TR u) (LeviOntoSPf.MatLiftPf.integral_matrix_lift_exists TR)

theorem levi_onto_reduction : LeviOntoS TR cs :=
  leviOntoS_of_frame TR cs (LeviOntoSPf.exact_dual_frame_exists X u)

end Formalism.L2.SG.Pf.NormSteps
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ParCols
section
noncomputable section

open scoped Classical ComplexConjugate TensorProduct
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Matrix Formalism.L2.SG.TermOp Formalism.L2.SG.HidaSetting
  Formalism.L2.SG.Pf.unitaryCongruence

namespace Formalism.L2.SG.NormCut

section Par

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

theorem hform_mulVec' {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] (σ : A →+* A)
    (J M : Matrix n n A) (hM : Formalism.UG.cT σ M * J * M = J) (x y : n → A) :
    Formalism.UG.hform σ J (M *ᵥ x) (M *ᵥ y) = Formalism.UG.hform σ J x y := by
  have key : ∀ a b : n → A, Formalism.UG.hform σ J a b = ((fun i => σ (a i)) ᵥ* J) ⬝ᵥ b := by
    intro a b
    simp only [Formalism.UG.hform, dotProduct, Matrix.vecMul, Finset.sum_mul]
    rw [Finset.sum_comm]
  have hσ : (fun i => σ ((M *ᵥ x) i)) = (fun i => σ (x i)) ᵥ* (Formalism.UG.cT σ M) := by
    funext i
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.mulVec, Matrix.vecMul, dotProduct, Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply,
      map_sum, map_mul]
    exact Finset.sum_congr rfl (fun k _ => mul_comm _ _)
  rw [key, key, Matrix.dotProduct_mulVec, hσ, Matrix.vecMul_vecMul, Matrix.vecMul_vecMul, ← Matrix.mul_assoc, hM]

theorem hA_unit (g : X.B.I.Gf) (x y : VA X.B.I) :
    hA X.B.I (X.B.I.fmat g *ᵥ x) (X.B.I.fmat g *ᵥ y) = hA X.B.I x y := by
  unfold hA
  refine hform_mulVec' _ _ (X.B.I.fmat g) ?_ x y
  exact g.2

theorem hA_adj (g : X.B.I.Gf) (x y : VA X.B.I) :
    hA X.B.I x (X.B.I.fmat g *ᵥ y) = hA X.B.I (X.B.I.fmat g⁻¹ *ᵥ x) y := by
  have e : X.B.I.fmat g *ᵥ (X.B.I.fmat g⁻¹ *ᵥ x) = x := by
    rw [Matrix.mulVec_mulVec]
    have h1 : X.B.I.fmat g * X.B.I.fmat g⁻¹ = 1 := by
      change X.B.I.fmat (g * g⁻¹) = 1
      rw [mul_inv_cancel]
      rfl
    rw [h1, Matrix.one_mulVec]
  calc hA X.B.I x (X.B.I.fmat g *ᵥ y) = hA X.B.I (X.B.I.fmat g *ᵥ (X.B.I.fmat g⁻¹ *ᵥ x)) (X.B.I.fmat g *ᵥ y) := by
        rw [e]
    _ = hA X.B.I (X.B.I.fmat g⁻¹ *ᵥ x) y := hA_unit X g _ y

theorem mem_mL_of_InAt {d : VA X.B.I} (hd : d ∈ X.B.I.Lf) (h : InAt X.B.I X.B.g X.B.g d) :
    d ∈ mL X.B.I X.B.g := by
  obtain ⟨c, hc, hcd⟩ := h
  have hb : ((c : ℤ) * Nat.gcdA c X.B.g + (X.B.g : ℤ) * Nat.gcdB c X.B.g) = 1 := by
    rw [← Nat.gcd_eq_gcd_ab, hc.gcd_eq_one]; rfl
  have e : d = ((Nat.gcdA c X.B.g : ℤ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • ((c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • d) +
      ((Nat.gcdB c X.B.g : ℤ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • ((X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • d) := by
    rw [smul_smul, smul_smul, ← add_smul]
    have : ((Nat.gcdA c X.B.g : ℤ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) +
        ((Nat.gcdB c X.B.g : ℤ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * (X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) = 1 := by
      have := congrArg (fun z : ℤ => (z : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F)) hb
      push_cast at this
      linear_combination this
    rw [this, one_smul]
  rw [e]
  have hint : ∀ z : ℤ, ((z : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F)) ∈ IntAf X.B.I.F X.B.I.E := fun z => intCast_mem _ z
  have sm : ∀ (z : ℤ) (w : VA X.B.I), w ∈ mL X.B.I X.B.g →
      ((z : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F)) • w ∈ mL X.B.I X.B.g := fun z w hw => by
    have : ((z : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F)) • w = (⟨_, hint z⟩ : IntAf X.B.I.F X.B.I.E) • w := rfl
    rw [this]; exact Submodule.smul_mem _ _ hw
  exact add_mem (sm _ _ hcd) (sm _ _ (smul_mem_mL X.B.I hd))

theorem mem_Mo_eb {v : VA X.B.I} (hv : v ∈ X.B.I.Lf) (he : ∀ a, ZMod' X.B.I X.B.g (hA X.B.I (X.e0 a) v))
    (hz : ZMod' X.B.I X.B.g (hA X.B.I X.z0 v)) (hb : ∀ l, ZMod' X.B.I X.B.g (hA X.B.I (X.bw l) v)) :
    v ∈ Mo X.B.I X.B.g (Set.range X.e0 ∪ Set.range X.bw) := by
  obtain ⟨hE, hF, hZ, hB, hBd⟩ := frame_Lf X
  have hd := dual_coords X hv
  have e : v = (v - repr0 X v) + repr0 X v := by abel
  rw [e]
  refine add_mem (mL_Mo X.B.I hd) ?_
  have spn : ∀ (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) (w : VA X.B.I), c ∈ IntAf X.B.I.F X.B.I.E →
      w ∈ Set.range X.e0 ∪ Set.range X.bw → c • w ∈ Mo X.B.I X.B.g (Set.range X.e0 ∪ Set.range X.bw) :=
    fun c w hc hw => by
      have : c • w = (⟨c, hc⟩ : IntAf X.B.I.F X.B.I.E) • w := rfl
      rw [this]; exact Submodule.smul_mem _ _ (sub_Mo X.B.I hw)
  unfold repr0
  refine add_mem (add_mem (sub_mem (add_mem ?_ ?_) ?_) ?_) ?_
  · exact sum_mem fun a _ => spn _ _ (hA_int X.B.I (hF a) hv) (Or.inl ⟨a, rfl⟩)
  · exact sum_mem fun a _ => mL_Mo X.B.I (Z_smul_mL X (he a) (hF a))
  · exact mL_Mo X.B.I (Z_smul_mL X hz hZ)
  · exact sum_mem fun l _ => spn _ _ (hA_int X.B.I (hBd l) hv) (Or.inr ⟨l, rfl⟩)
  · exact sum_mem fun l _ => mL_Mo X.B.I (Z_smul_mL X (hb l) (hBd l))

def Par (x : X.B.I.Gf) : Prop :=
  x ∈ X.B.I.Kset ∧ (∀ a, X.B.I.fmat x *ᵥ X.e0 a ∈ Mo X.B.I X.B.g (Set.range X.e0)) ∧
    ∀ j, X.B.I.fmat x *ᵥ X.bw j ∈ Mo X.B.I X.B.g (Set.range X.e0 ∪ Set.range X.bw)

def Good (x : X.B.I.Gf) : Prop := Par X x ∧ Par X x⁻¹

theorem par_one : Par X 1 := by
  unfold Par Mo
  refine ⟨?_, fun a => ?_, fun j => ?_⟩
  · first
    | exact (Formalism.UG.stabGL X.B.I.Lf).one_mem
    | exact one_mem (Formalism.UG.stabGL X.B.I.Lf)
    | (show ((1 : X.B.I.Gf) : GL (Fin X.B.I.n) (X.B.I.E ⊗[X.B.I.F] Af X.B.I.F)) ∈ Formalism.UG.stabGL X.B.I.Lf
       exact one_mem _)
  · rw [show X.B.I.fmat 1 = 1 from rfl, Matrix.one_mulVec]
    exact Submodule.mem_sup_left (Submodule.subset_span ⟨a, rfl⟩)
  · rw [show X.B.I.fmat 1 = 1 from rfl, Matrix.one_mulVec]
    exact Submodule.mem_sup_left (Submodule.subset_span (Or.inr ⟨j, rfl⟩))

theorem par_mul {x y : X.B.I.Gf} (hx : Par X x) (hy : Par X y) : Par X (x * y) := by
  refine ⟨K_mul X.B.I hx.1 hy.1, fun a => ?_, fun j => ?_⟩
  · rw [fmat_mul, ← Matrix.mulVec_mulVec]
    refine pres X.B.I hx.1 X.B.g (Set.range X.e0) _ (sub_Mo X.B.I) ?_ (mL_Mo X.B.I) _ (hy.2.1 a)
    rintro _ ⟨b, rfl⟩
    rw [Matrix.sub_mulVec, Matrix.one_mulVec]
    exact sub_mem (hx.2.1 b) (sub_Mo X.B.I ⟨b, rfl⟩)
  · rw [fmat_mul, ← Matrix.mulVec_mulVec]
    refine pres X.B.I hx.1 X.B.g (Set.range X.e0 ∪ Set.range X.bw) _ (sub_Mo X.B.I) ?_ (mL_Mo X.B.I) _ (hy.2.2 j)
    rintro s (⟨b, rfl⟩ | ⟨l, rfl⟩)
    · rw [Matrix.sub_mulVec, Matrix.one_mulVec]
      exact sub_mem (Mo_mono X.B.I Set.subset_union_left (hx.2.1 b)) (sub_Mo X.B.I (Or.inl ⟨b, rfl⟩))
    · rw [Matrix.sub_mulVec, Matrix.one_mulVec]
      exact sub_mem (hx.2.2 l) (sub_Mo X.B.I (Or.inr ⟨l, rfl⟩))

theorem good_one : Good X 1 := by
  exact ⟨par_one X, by rw [inv_one]; exact par_one X⟩

theorem good_mul {x y : X.B.I.Gf} (hx : Good X x) (hy : Good X y) : Good X (x * y) := by
  exact ⟨par_mul X hx.1 hy.1, by rw [_root_.mul_inv_rev]; exact par_mul X hy.2 hx.2⟩

theorem good_inv {x : X.B.I.Gf} (hx : Good X x) : Good X x⁻¹ := by
  exact ⟨hx.2, by rw [inv_inv]; exact hx.1⟩

variable {X} (TR : TypedRed X)

theorem leviM_mul_par {x y : X.B.I.Gf} (hx : Par X x) (hy : Par X y) (v : TR.Pl) :
    leviM TR (x * y) v = leviM TR x v * leviM TR y v :=
  leviM_mul TR hx.1 hy.1 hy.2.2 hx.2.1 v

theorem leviM_one (v : TR.Pl) : leviM TR 1 v = 1 := by
  ext i j
  have hbw : ∀ j, X.bw j ∈ X.B.I.Lf := fun j => (X.vectorsInLattice.2.2 j).1
  have hbwd : ∀ j, X.bwd j ∈ X.B.I.Lf := fun j => (X.vectorsInLattice.2.2 j).2
  simp only [leviM, show X.B.I.fmat 1 = 1 from rfl, Matrix.one_mulVec]
  have hI := hA_int X.B.I (hbwd i) (hbw j)
  rw [resT_of_mem TR v hI]
  have hZ := X.bw_dual i j
  have hIt : (if i = j then X.ew else 0) ∈ IntAf X.B.I.F X.B.I.E := by
    split_ifs
    · exact X.ew_int
    · exact zero_mem _
  have e : (⟨_, hI⟩ : IntAf X.B.I.F X.B.I.E) = ⟨_, sub_mem hI hIt⟩ + ⟨_, hIt⟩ := by
    apply Subtype.ext; simp
  rw [e, map_add (f := _), res_eq_zero_of_Z TR v _ hZ, zero_add]
  by_cases h : i = j
  · subst h
    simp only [if_true, Matrix.one_apply_eq]
    have e2 : (⟨X.ew, X.ew_int⟩ : IntAf X.B.I.F X.B.I.E) = ⟨X.ew * (1 : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F),
        (IntAf X.B.I.F X.B.I.E).mul_mem X.ew_int (one_mem _)⟩ := by apply Subtype.ext; simp
    have := TR.res_ew v 1
    simp only [OneMemClass.coe_one] at this
    convert this using 2
    exact (map_one (TR.res v)).symm
  · simp only [h, if_false, Matrix.one_apply_ne h]
    exact map_zero (TR.res v) |>.symm ▸ (by congr 1)

end Par

end Formalism.L2.SG.NormCut
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ScalarFramePfE
section
noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.ScalarFramePf

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc ValuativeRel

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Generic

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : Loc.HermSp M V)

def IotaG (q : E) (abelian₂ : Submodule M.L.O V) {r : ℕ} (f₀ f₁ f₂ : Fin (r + 1) → V) (e : V ≃ₗ[E] V) : Prop :=
  (∀ x x' : V, x ∈ abelian₂ → x' ∈ abelian₂ → x ∈ H.perp (H.X f₀) → x' ∈ H.perp (H.X f₁) → x - x' ∈ H.smulLat q abelian₂ →
    ∃ y y'' : V, y ∈ abelian₂ ∧ y'' ∈ abelian₂ ∧ y ∈ H.perp (H.X f₀) ∧ y'' ∈ H.perp (H.X f₂) ∧ x - y ∈ H.X f₀ ∧
      e x' - y'' ∈ H.X f₂ ∧ y - y'' ∈ H.smulLat q abelian₂) ∧
  (∀ x x'' : V, x ∈ abelian₂ → x'' ∈ abelian₂ → x ∈ H.perp (H.X f₀) → x'' ∈ H.perp (H.X f₂) →
    x - x'' ∈ H.smulLat q abelian₂ →
    ∃ y y' : V, y ∈ abelian₂ ∧ y' ∈ abelian₂ ∧ y ∈ H.perp (H.X f₀) ∧ y' ∈ H.perp (H.X f₁) ∧ x - y ∈ H.X f₀ ∧
      e.symm x'' - y' ∈ H.X f₁ ∧ y - y' ∈ H.smulLat q abelian₂)

end Generic

end Formalism.L2.SG.Pf.ScalarFramePf
end
end

