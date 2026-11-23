module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0002
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.OneSTr
public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.StripEntire

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QuadraticBoxVolumeBound
section
open MeasureTheory Topology GlobalTheory.CompanionTheory.WeilSiegel.Inf0
open scoped ENNReal NNReal Matrix

noncomputable section
namespace GlobalTheory.CompanionTheory.WeilSiegel.Inf0.RealBox

theorem pi_smul_const_family {P : Type} [Fintype P] {X : P → Type} [∀ i, MeasurableSpace (X i)]
    (μ : ∀ i, Measure (X i)) [∀ i, SigmaFinite (μ i)] (c : P → ℝ≥0) :
    Measure.pi (fun i => c i • μ i) = (∏ i, c i) • Measure.pi μ := by
  haveI : ∀ i, SigmaFinite (c i • μ i) := fun i => inferInstance
  refine Measure.pi_eq fun s _ => ?_
  simp only [Measure.smul_apply, Measure.pi_pi, ENNReal.smul_def, smul_eq_mul,
    Finset.prod_mul_distrib, ENNReal.ofNNReal_finsetProd]

theorem map_pi_smul {P : Type} [Fintype P] (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasureSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    [(volume : Measure E).IsAddHaarMeasure] (r : P → ℝ) (hr : ∀ w, 0 < r w) :
    (volume : Measure (P → E)).map (fun x w => r w • x w) =
      ENNReal.ofReal (∏ w, (r w ^ Module.finrank ℝ E)⁻¹) • (volume : Measure (P → E)) := by
  have hc : ∀ w, (volume : Measure E).map (fun y => r w • y) =
      Real.toNNReal ((r w ^ Module.finrank ℝ E)⁻¹) • (volume : Measure E) := fun w => by
    rw [Measure.map_addHaar_smul _ (hr w).ne', abs_of_pos (inv_pos.mpr (pow_pos (hr w) _))]
    ext s _
    rw [Measure.smul_apply, Measure.smul_apply, ENNReal.smul_def, ENNReal.ofReal]
  haveI : ∀ w, SigmaFinite ((volume : Measure E).map (fun y => r w • y)) := fun w => by
    rw [hc w]; infer_instance
  have hmap := Measure.pi_map_pi (μ := fun _ : P => (volume : Measure E))
    (f := fun w (y : E) => r w • y)
    (fun w => (continuous_id.const_smul (r w)).measurable.aemeasurable)
  beta_reduce at hmap
  rw [volume_pi, hmap]
  simp only [hc]
  rw [GlobalTheory.CompanionTheory.WeilSiegel.Inf0.RealBox.pi_smul_const_family, ← Real.toNNReal_prod_of_nonneg
    (fun w _ => (inv_pos.mpr (pow_pos (hr w) (Module.finrank ℝ E))).le)]
  ext s _
  rw [Measure.smul_apply, Measure.smul_apply, ENNReal.smul_def, ENNReal.ofReal]

variable {P ι : Type}

theorem continuous_qR0 [Fintype ι] (A : P → Matrix ι ι ℝ) : Continuous (qR0 A) := by
  unfold GlobalTheory.CompanionTheory.WeilSiegel.Inf0.qR0
  exact continuous_pi fun w => continuous_const.mul
    ((continuous_apply w).dotProduct (continuous_const.matrix_mulVec (continuous_apply w)))

theorem continuous_gaussR [Fintype P] [Fintype ι] (Pm : P → Matrix ι ι ℝ) :
    Continuous (gaussR Pm) := by
  unfold gaussR
  exact Real.continuous_exp.comp (continuous_const.mul (continuous_finsetSum _ fun w _ =>
    Continuous.dotProduct (continuous_apply w)
      (Continuous.matrix_mulVec continuous_const (continuous_apply w))))

theorem boxR_one_eq [Fintype P] [Fintype ι] :
    boxR (fun _ : P => (1 : ℝ)) = Metric.closedBall (0 : P → ι → ℝ) 1 := by
  ext x
  simp only [boxR, Set.mem_setOf_eq, mem_closedBall_zero_iff]
  exact (pi_norm_le_iff_of_nonneg zero_le_one).symm

theorem unit_box_bound [Fintype P] [Fintype ι] (A Pm : P → Matrix ι ι ℝ) (Di : (P → ℝ) → ℝ)
    (hDi : Continuous Di)
    (hD : ∀ U : Set (P → ℝ), MeasurableSet U →
      ∫⁻ x in qR0 A ⁻¹' U, ENNReal.ofReal (gaussR Pm x) = ∫⁻ y in U, ENNReal.ofReal (Di y)) :
    ∃ C : ℝ≥0, ∀ U : Set (P → ℝ), MeasurableSet U →
      (volume : Measure (P → ι → ℝ)) (qR0 A ⁻¹' U ∩ boxR (fun _ => (1 : ℝ))) ≤
        (C : ℝ≥0∞) * volume U := by
  have hBc : IsCompact (GlobalTheory.CompanionTheory.WeilSiegel.Inf0.boxR (fun _ : P => (1 : ℝ)) : Set (P → ι → ℝ)) := by
    rw [GlobalTheory.CompanionTheory.WeilSiegel.Inf0.RealBox.boxR_one_eq]; exact isCompact_closedBall _ _
  have hBm : MeasurableSet (GlobalTheory.CompanionTheory.WeilSiegel.Inf0.boxR (fun _ : P => (1 : ℝ)) : Set (P → ι → ℝ)) :=
    hBc.isClosed.measurableSet
  have hBne : (GlobalTheory.CompanionTheory.WeilSiegel.Inf0.boxR (fun _ : P => (1 : ℝ)) : Set (P → ι → ℝ)).Nonempty := by
    rw [GlobalTheory.CompanionTheory.WeilSiegel.Inf0.RealBox.boxR_one_eq]; exact ⟨0, Metric.mem_closedBall_self zero_le_one⟩
  have hQc : Continuous (GlobalTheory.CompanionTheory.WeilSiegel.Inf0.qR0 (P := P) A) := GlobalTheory.CompanionTheory.WeilSiegel.Inf0.RealBox.continuous_qR0 A
  have hKc : IsCompact (GlobalTheory.CompanionTheory.WeilSiegel.Inf0.qR0 A '' (GlobalTheory.CompanionTheory.WeilSiegel.Inf0.boxR (fun _ : P => (1 : ℝ)) : Set (P → ι → ℝ))) :=
    hBc.image hQc
  obtain ⟨x₀, -, hx₀⟩ := hBc.exists_isMinOn hBne (GlobalTheory.CompanionTheory.WeilSiegel.Inf0.RealBox.continuous_gaussR Pm).continuousOn
  obtain ⟨D, hD'⟩ := hKc.exists_bound_of_continuousOn hDi.continuousOn
  have hm : 0 < GlobalTheory.CompanionTheory.WeilSiegel.Inf0.gaussR Pm x₀ := Real.exp_pos _
  refine ⟨Real.toNNReal ((GlobalTheory.CompanionTheory.WeilSiegel.Inf0.gaussR Pm x₀)⁻¹ * D), fun U hU => ?_⟩
  change _ ≤ ENNReal.ofReal ((GlobalTheory.CompanionTheory.WeilSiegel.Inf0.gaussR Pm x₀)⁻¹ * D) * _
  have hS : MeasurableSet (GlobalTheory.CompanionTheory.WeilSiegel.Inf0.qR0 A ⁻¹' U ∩
      (GlobalTheory.CompanionTheory.WeilSiegel.Inf0.boxR (fun _ : P => (1 : ℝ)) : Set (P → ι → ℝ))) := (hQc.measurable hU).inter hBm
  have hK : MeasurableSet (U ∩ GlobalTheory.CompanionTheory.WeilSiegel.Inf0.qR0 A ''
      (GlobalTheory.CompanionTheory.WeilSiegel.Inf0.boxR (fun _ : P => (1 : ℝ)) : Set (P → ι → ℝ))) := hU.inter hKc.isClosed.measurableSet
  have h1 : ENNReal.ofReal (GlobalTheory.CompanionTheory.WeilSiegel.Inf0.gaussR Pm x₀) * (volume : Measure (P → ι → ℝ))
      (GlobalTheory.CompanionTheory.WeilSiegel.Inf0.qR0 A ⁻¹' U ∩ GlobalTheory.CompanionTheory.WeilSiegel.Inf0.boxR (fun _ => (1 : ℝ))) ≤
      ENNReal.ofReal D * volume U := by
    calc ENNReal.ofReal (GlobalTheory.CompanionTheory.WeilSiegel.Inf0.gaussR Pm x₀) * (volume : Measure (P → ι → ℝ))
          (GlobalTheory.CompanionTheory.WeilSiegel.Inf0.qR0 A ⁻¹' U ∩ GlobalTheory.CompanionTheory.WeilSiegel.Inf0.boxR (fun _ => (1 : ℝ)))
        = ∫⁻ _ in GlobalTheory.CompanionTheory.WeilSiegel.Inf0.qR0 A ⁻¹' U ∩ GlobalTheory.CompanionTheory.WeilSiegel.Inf0.boxR (fun _ => (1 : ℝ)),
            ENNReal.ofReal (GlobalTheory.CompanionTheory.WeilSiegel.Inf0.gaussR Pm x₀) := (setLIntegral_const _ _).symm
      _ ≤ ∫⁻ x in GlobalTheory.CompanionTheory.WeilSiegel.Inf0.qR0 A ⁻¹' U ∩ GlobalTheory.CompanionTheory.WeilSiegel.Inf0.boxR (fun _ => (1 : ℝ)),
            ENNReal.ofReal (GlobalTheory.CompanionTheory.WeilSiegel.Inf0.gaussR Pm x) :=
          setLIntegral_mono' hS fun x hx => ENNReal.ofReal_le_ofReal (isMinOn_iff.mp hx₀ x hx.2)
      _ ≤ ∫⁻ x in GlobalTheory.CompanionTheory.WeilSiegel.Inf0.qR0 A ⁻¹' (U ∩ GlobalTheory.CompanionTheory.WeilSiegel.Inf0.qR0 A ''
            (GlobalTheory.CompanionTheory.WeilSiegel.Inf0.boxR (fun _ : P => (1 : ℝ)) : Set (P → ι → ℝ))),
            ENNReal.ofReal (GlobalTheory.CompanionTheory.WeilSiegel.Inf0.gaussR Pm x) :=
          lintegral_mono_set fun x hx => ⟨hx.1, x, hx.2, rfl⟩
      _ = ∫⁻ y in U ∩ GlobalTheory.CompanionTheory.WeilSiegel.Inf0.qR0 A ''
            (GlobalTheory.CompanionTheory.WeilSiegel.Inf0.boxR (fun _ : P => (1 : ℝ)) : Set (P → ι → ℝ)), ENNReal.ofReal (Di y) := hD _ hK
      _ ≤ ∫⁻ _ in U ∩ GlobalTheory.CompanionTheory.WeilSiegel.Inf0.qR0 A ''
            (GlobalTheory.CompanionTheory.WeilSiegel.Inf0.boxR (fun _ : P => (1 : ℝ)) : Set (P → ι → ℝ)), ENNReal.ofReal D :=
          setLIntegral_mono' hK fun y hy =>
            ENNReal.ofReal_le_ofReal ((Real.le_norm_self _).trans (hD' y hy.2))
      _ = ENNReal.ofReal D * volume (U ∩ GlobalTheory.CompanionTheory.WeilSiegel.Inf0.qR0 A ''
            (GlobalTheory.CompanionTheory.WeilSiegel.Inf0.boxR (fun _ : P => (1 : ℝ)) : Set (P → ι → ℝ))) := setLIntegral_const _ _
      _ ≤ ENNReal.ofReal D * volume U := mul_le_mul_right (measure_mono Set.inter_subset_left) _
  calc (volume : Measure (P → ι → ℝ)) (GlobalTheory.CompanionTheory.WeilSiegel.Inf0.qR0 A ⁻¹' U ∩ GlobalTheory.CompanionTheory.WeilSiegel.Inf0.boxR (fun _ => (1 : ℝ)))
      = ENNReal.ofReal ((GlobalTheory.CompanionTheory.WeilSiegel.Inf0.gaussR Pm x₀)⁻¹ * GlobalTheory.CompanionTheory.WeilSiegel.Inf0.gaussR Pm x₀) *
          (volume : Measure (P → ι → ℝ)) (GlobalTheory.CompanionTheory.WeilSiegel.Inf0.qR0 A ⁻¹' U ∩ GlobalTheory.CompanionTheory.WeilSiegel.Inf0.boxR (fun _ => (1 : ℝ))) := by
        rw [inv_mul_cancel₀ hm.ne', ENNReal.ofReal_one, one_mul]
    _ = ENNReal.ofReal (GlobalTheory.CompanionTheory.WeilSiegel.Inf0.gaussR Pm x₀)⁻¹ * (ENNReal.ofReal (GlobalTheory.CompanionTheory.WeilSiegel.Inf0.gaussR Pm x₀) *
          (volume : Measure (P → ι → ℝ)) (GlobalTheory.CompanionTheory.WeilSiegel.Inf0.qR0 A ⁻¹' U ∩ GlobalTheory.CompanionTheory.WeilSiegel.Inf0.boxR (fun _ => (1 : ℝ)))) := by
        rw [ENNReal.ofReal_mul (inv_nonneg.mpr hm.le), mul_assoc]
    _ ≤ ENNReal.ofReal (GlobalTheory.CompanionTheory.WeilSiegel.Inf0.gaussR Pm x₀)⁻¹ * (ENNReal.ofReal D * volume U) :=
        mul_le_mul_right h1 _
    _ = ENNReal.ofReal ((GlobalTheory.CompanionTheory.WeilSiegel.Inf0.gaussR Pm x₀)⁻¹ * D) * volume U := by
        rw [ENNReal.ofReal_mul (inv_nonneg.mpr hm.le), mul_assoc]

theorem qR0_scale [Fintype ι] (A : P → Matrix ι ι ℝ) (t : P → ℝ) (x : P → ι → ℝ) :
    qR0 A (fun w => t w • x w) = fun w => (t w ^ 2) • qR0 A x w := by
  funext w
  simp only [qR0, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul]
  ring

theorem image_box_bound : ∀ (P ι : Type) [Fintype P] [Fintype ι] (A Pm : P → Matrix ι ι ℝ) (Di : (P → ℝ) → ℝ), 2 ≤ Fintype.card ι → Continuous Di → (∀ U : Set (P → ℝ), MeasurableSet U → ∫⁻ x in qR0 A ⁻¹' U, ENNReal.ofReal (gaussR Pm x) = ∫⁻ y in U, ENNReal.ofReal (Di y)) → ∃ C : ℝ≥0, ∀ t : P → ℝ, (∀ w, 0 < t w) → ∀ U : Set (P → ℝ), MeasurableSet U → (volume : Measure (P → ι → ℝ)) (qR0 A ⁻¹' U ∩ boxR t) ≤ (C : ℝ≥0∞) * ENNReal.ofReal (∏ w, t w ^ (Fintype.card ι - 2)) * volume U := by
  intro P ι _ _ A Pm Di hcard hDi hD
  obtain ⟨C, hC⟩ := GlobalTheory.CompanionTheory.WeilSiegel.Inf0.RealBox.unit_box_bound A Pm Di hDi hD
  refine ⟨C, fun t ht U hU => ?_⟩
  have hQc : Continuous (GlobalTheory.CompanionTheory.WeilSiegel.Inf0.qR0 (P := P) A) := GlobalTheory.CompanionTheory.WeilSiegel.Inf0.RealBox.continuous_qR0 A
  have hφm : Measurable (fun (x : P → ι → ℝ) (w : P) => t w • x w) :=
    (continuous_pi fun w => (continuous_apply w).const_smul (t w)).measurable
  have hψm : Measurable (fun (z : P → ℝ) (w : P) => t w ^ 2 • z w) :=
    (continuous_pi fun w => (continuous_apply w).const_smul (t w ^ 2)).measurable
  have hBox : IsClosed (GlobalTheory.CompanionTheory.WeilSiegel.Inf0.boxR t : Set (P → ι → ℝ)) := by
    show IsClosed {x : P → ι → ℝ | ∀ w, ‖x w‖ ≤ t w}
    rw [Set.setOf_forall]
    exact isClosed_iInter fun w => isClosed_le (continuous_apply w).norm continuous_const
  have hSm : MeasurableSet (GlobalTheory.CompanionTheory.WeilSiegel.Inf0.qR0 A ⁻¹' U ∩ (GlobalTheory.CompanionTheory.WeilSiegel.Inf0.boxR t : Set (P → ι → ℝ))) :=
    (hQc.measurable hU).inter hBox.measurableSet
  have hpre : (fun (x : P → ι → ℝ) (w : P) => t w • x w) ⁻¹'
      (GlobalTheory.CompanionTheory.WeilSiegel.Inf0.qR0 A ⁻¹' U ∩ GlobalTheory.CompanionTheory.WeilSiegel.Inf0.boxR t) =
      GlobalTheory.CompanionTheory.WeilSiegel.Inf0.qR0 A ⁻¹' ((fun (z : P → ℝ) (w : P) => t w ^ 2 • z w) ⁻¹' U) ∩
        GlobalTheory.CompanionTheory.WeilSiegel.Inf0.boxR (fun _ => (1 : ℝ)) := by
    ext y
    simp only [Set.mem_preimage, Set.mem_inter_iff, GlobalTheory.CompanionTheory.WeilSiegel.Inf0.RealBox.qR0_scale]
    refine and_congr_right fun _ => ?_
    simp only [GlobalTheory.CompanionTheory.WeilSiegel.Inf0.boxR, Set.mem_setOf_eq]
    exact forall_congr' fun w => by
      rw [norm_smul, Real.norm_of_nonneg (ht w).le, mul_le_iff_le_one_right (ht w)]
  have hφ := GlobalTheory.CompanionTheory.WeilSiegel.Inf0.RealBox.map_pi_smul (P := P) (ι → ℝ) t ht
  have hψ := GlobalTheory.CompanionTheory.WeilSiegel.Inf0.RealBox.map_pi_smul (P := P) ℝ (fun w => t w ^ 2) (fun w => pow_pos (ht w) 2)
  rw [Module.finrank_fintype_fun_eq_card] at hφ
  rw [Module.finrank_self] at hψ
  have e1 : ENNReal.ofReal (∏ w, (t w ^ Fintype.card ι)⁻¹) *
      (volume : Measure (P → ι → ℝ)) (GlobalTheory.CompanionTheory.WeilSiegel.Inf0.qR0 A ⁻¹' U ∩ GlobalTheory.CompanionTheory.WeilSiegel.Inf0.boxR t) =
      volume (GlobalTheory.CompanionTheory.WeilSiegel.Inf0.qR0 A ⁻¹' ((fun (z : P → ℝ) (w : P) => t w ^ 2 • z w) ⁻¹' U) ∩
        GlobalTheory.CompanionTheory.WeilSiegel.Inf0.boxR (fun _ => (1 : ℝ))) := by
    rw [← hpre, ← Measure.map_apply hφm hSm, hφ, Measure.smul_apply, smul_eq_mul]
  have e2 : ENNReal.ofReal (∏ w, ((t w ^ 2) ^ 1)⁻¹) * (volume : Measure (P → ℝ)) U =
      volume ((fun (z : P → ℝ) (w : P) => t w ^ 2 • z w) ⁻¹' U) := by
    rw [← Measure.map_apply hψm hU, hψ, Measure.smul_apply, smul_eq_mul]
  have hprod : ENNReal.ofReal (∏ w, t w ^ Fintype.card ι) *
      ENNReal.ofReal (∏ w, (t w ^ Fintype.card ι)⁻¹) = 1 := by
    rw [← ENNReal.ofReal_mul (Finset.prod_nonneg fun w _ => (pow_pos (ht w) _).le),
      ← Finset.prod_mul_distrib,
      Finset.prod_eq_one fun w _ => mul_inv_cancel₀ (pow_ne_zero _ (ht w).ne'), ENNReal.ofReal_one]
  have hreal : (∏ w, t w ^ Fintype.card ι) * ∏ w, ((t w ^ 2) ^ 1)⁻¹ =
      ∏ w, t w ^ (Fintype.card ι - 2) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun w _ => ?_
    rw [pow_one, show t w ^ Fintype.card ι = t w ^ (Fintype.card ι - 2) * t w ^ 2 by
        rw [← pow_add, Nat.sub_add_cancel hcard],
      mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ (ht w).ne'), mul_one]
  calc (volume : Measure (P → ι → ℝ)) (GlobalTheory.CompanionTheory.WeilSiegel.Inf0.qR0 A ⁻¹' U ∩ GlobalTheory.CompanionTheory.WeilSiegel.Inf0.boxR t)
      = ENNReal.ofReal (∏ w, t w ^ Fintype.card ι) * (ENNReal.ofReal (∏ w, (t w ^ Fintype.card ι)⁻¹) *
          (volume : Measure (P → ι → ℝ)) (GlobalTheory.CompanionTheory.WeilSiegel.Inf0.qR0 A ⁻¹' U ∩ GlobalTheory.CompanionTheory.WeilSiegel.Inf0.boxR t)) := by
        rw [← mul_assoc, hprod, one_mul]
    _ = ENNReal.ofReal (∏ w, t w ^ Fintype.card ι) *
          volume (GlobalTheory.CompanionTheory.WeilSiegel.Inf0.qR0 A ⁻¹' ((fun (z : P → ℝ) (w : P) => t w ^ 2 • z w) ⁻¹' U) ∩
            GlobalTheory.CompanionTheory.WeilSiegel.Inf0.boxR (fun _ => (1 : ℝ))) := by rw [e1]
    _ ≤ ENNReal.ofReal (∏ w, t w ^ Fintype.card ι) *
          ((C : ℝ≥0∞) * volume ((fun (z : P → ℝ) (w : P) => t w ^ 2 • z w) ⁻¹' U)) :=
        mul_le_mul_right (hC _ (hψm hU)) _
    _ = ENNReal.ofReal (∏ w, t w ^ Fintype.card ι) *
          ((C : ℝ≥0∞) * (ENNReal.ofReal (∏ w, ((t w ^ 2) ^ 1)⁻¹) * volume U)) := by rw [e2]
    _ = (C : ℝ≥0∞) * (ENNReal.ofReal (∏ w, t w ^ Fintype.card ι) *
          ENNReal.ofReal (∏ w, ((t w ^ 2) ^ 1)⁻¹)) * volume U := by ring
    _ = (C : ℝ≥0∞) * ENNReal.ofReal (∏ w, t w ^ (Fintype.card ι - 2)) * volume U := by
        rw [← ENNReal.ofReal_mul (Finset.prod_nonneg fun w _ => (pow_pos (ht w) _).le), hreal]

end GlobalTheory.CompanionTheory.WeilSiegel.Inf0.RealBox
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RealizationAdd
section
open CrystallineSemistableComparison.Pb.Kap

namespace GlobalTheory.CompanionTheory.KapRho

theorem rho_add {Λ A B K : Type} [CommRing Λ] [CommRing A] [CommRing B] [Field K]
    (C : Chain.{1} Λ A B K) {j : ℕ} (x y : ∀ n, C.S n j) (f g : Module.Dual K (C.V j) →+ B) :
    C.Rho x f → C.Rho y g → C.Rho (x + y) (f + g) := by
  rintro ⟨hf, e₁, z₁, hz₁, hb₁⟩ ⟨hg, e₂, z₂, hz₂, hb₂⟩
  refine ⟨fun k φ => by simp only [AddMonoidHom.add_apply, hf, hg, mul_add], e₁ + e₂,
    ((C.ℓ : A) ^ e₂) • z₁ + ((C.ℓ : A) ^ e₁) • z₂, fun n => ?_, fun {m} bs => ?_⟩
  · simp only [map_add (f := _), map_smul, hz₁, hz₂, Pi.add_apply]
    rw [pow_add]
    module
  · simp only [AddMonoidHom.add_apply, add_smul, Finset.sum_add_distrib, map_add (f := _),
      LinearMap.map_smulₛₗ, map_pow, map_natCast, ← hb₁ bs, ← hb₂ bs]
    rw [pow_add]
    module

end GlobalTheory.CompanionTheory.KapRho
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RealizationCupProduct
section
set_option backward.isDefEq.respectTransparency false

open CrystallineSemistableComparison.Pb.Kap

namespace GlobalTheory.CompanionTheory.KapRho

theorem semilinear_eq_sum_coord {K B : Type*} {V : Type*} [Field K] [CommRing B] [AddCommGroup V]
    [Module K V] (o : K →+* B) (f : Module.Dual K V →+ B)
    (hf : ∀ (k : K) φ, f (k • φ) = o k * f φ) {m : ℕ} (bs : Module.Basis (Fin m) K V)
    (φ : Module.Dual K V) : f φ = ∑ s, f (bs.coord s) * o (φ (bs s)) := by
  have hφ : φ = ∑ s, φ (bs s) • bs.coord s := by
    refine bs.ext fun t => ?_
    simp [LinearMap.sum_apply, Finsupp.single_apply]
  conv_lhs => rw [hφ]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [hf, mul_comm]

theorem rho_cup :
    ∀ {Λ A B K : Type} [CommRing Λ] [CommRing A] [CommRing B] [Field K] (C : Chain.{1} Λ A B K)
      (hC : C.Good) (P : Cup C), P.Good → ∀ {i j : ℕ} (x : ∀ n, C.S n i) (y : ∀ n, C.S n j)
      (f : Module.Dual K (C.V i) →+ B) (g : Module.Dual K (C.V j) →+ B)
      (h : Module.Dual K (C.V (i + j)) →+ B), C.Rho x f → C.Rho y g →
      C.Rho (fun n => P.cS n i j (x n) (y n)) h →
      ∀ {m m' : ℕ} (bs : Module.Basis (Fin m) K (C.V i)) (bs' : Module.Basis (Fin m') K (C.V j))
        (φ : Module.Dual K (C.V (i + j))),
        h φ = ∑ s, ∑ s', f (bs.coord s) * g (bs'.coord s') *
          C.o (φ (P.cV i j (bs s) (bs' s'))) := by
  intro Λ A B K _ _ _ _ C hC P hP i j x y f g h hf hg hh m m' bs bs' φ
  obtain ⟨-, e, z, hzr, hzb⟩ := hf
  obtain ⟨-, e', w, hwr, hwb⟩ := hg
  obtain ⟨hh1, e'', u, hur, hub⟩ := hh
  haveI := hC.fin (i + j)
  let b := Module.finBasis K (C.V (i + j))
  have hv : ∀ n, C.red n (i + j) (P.cZ i j z w) =
      ((C.ℓ : A) ^ (e + e')) • C.r n (i + j) (P.cS n i j (x n) (y n)) := by
    intro n
    rw [hP.red, hzr, hwr, hP.r, map_smul, LinearMap.map_smul₂, smul_smul, pow_add, mul_comm]
  have hd : C.b (i + j) (((C.ℓ : A) ^ (e + e')) • u - ((C.ℓ : A) ^ e'') • P.cZ i j z w) = 0 := by
    refine hC.sep _ _ fun n => ?_
    have hu := hur n
    simp only at hu
    rw [map_sub, map_smul, map_smul, hu, hv n, smul_smul, smul_smul, mul_comm, sub_self]
  have key : ((C.ℓ : B) ^ (e + e')) • C.b (i + j) u =
      ((C.ℓ : B) ^ e'') • C.b (i + j) (P.cZ i j z w) := by
    rw [map_sub, LinearMap.map_smulₛₗ, LinearMap.map_smulₛₗ, sub_eq_zero] at hd
    simpa only [map_pow, map_natCast] using hd
  let c : Fin (Module.finrank K (C.V (i + j))) → B := fun t =>
    ∑ s, ∑ s', f (bs.coord s) * g (bs'.coord s') *
      C.o (b.coord t (P.cV i j (bs s) (bs' s')))
  have hμ : ∀ s s', P.cW i j (C.μ i (bs s)) (C.μ j (bs' s')) =
      ∑ t, C.o (b.coord t (P.cV i j (bs s) (bs' s'))) • C.μ (i + j) (b t) := by
    intro s s'
    rw [← hP.μ]
    conv_lhs => rw [← b.sum_repr (P.cV i j (bs s) (bs' s'))]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [LinearMap.map_smulₛₗ, Module.Basis.coord_apply]
  have hcup : P.cW i j (∑ s, f (bs.coord s) • C.μ i (bs s))
      (∑ s', g (bs'.coord s') • C.μ j (bs' s')) = ∑ t, c t • C.μ (i + j) (b t) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, hμ, c,
      Finset.sum_smul, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    symm
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun s' _ => Finset.sum_congr rfl fun t _ => ?_
    congr 1
    ring
  have hcoef : ∑ t, h (b.coord t) • C.μ (i + j) (b t) = ∑ t, c t • C.μ (i + j) (b t) := by
    have hu : IsUnit ((C.ℓ : B) ^ (e + e') * (C.ℓ : B) ^ e'') :=
      (hC.unit.pow _).mul (hC.unit.pow _)
    refine (hu.smul_left_cancel).1 ?_
    rw [hP.b, ← hub b, ← hzb bs, ← hwb bs', map_smul, LinearMap.map_smul₂, hcup, smul_smul,
      smul_smul, smul_smul] at key
    have hl : (C.ℓ : B) ^ e'' * (C.ℓ : B) ^ e' * (C.ℓ : B) ^ e =
        (C.ℓ : B) ^ (e + e') * (C.ℓ : B) ^ e'' := by ring
    rwa [hl] at key
  have hc : ∀ t, h (b.coord t) = c t := by
    obtain ⟨g₀, -, hg₀⟩ := hC.basis (i + j) b (∑ t, c t • C.μ (i + j) (b t))
    have h1 := hg₀ c rfl
    have h2 := hg₀ (fun t => h (b.coord t)) hcoef.symm
    exact fun t => congrFun (h2.trans h1.symm) t
  have hφ : ∀ s s', C.o (φ (P.cV i j (bs s) (bs' s'))) =
      ∑ t, C.o (b.coord t (P.cV i j (bs s) (bs' s'))) * C.o (φ (b t)) := by
    intro s s'
    conv_lhs => rw [← b.sum_repr (P.cV i j (bs s) (bs' s'))]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, smul_eq_mul, map_mul, Module.Basis.coord_apply]
  refine (semilinear_eq_sum_coord C.o h hh1 b φ).trans ?_
  simp only [hc, c, hφ, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun s' _ => Finset.sum_congr rfl fun t _ => ?_
  rw [mul_assoc]

end GlobalTheory.CompanionTheory.KapRho
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RealizationFunctorial
section
open CrystallineSemistableComparison.Pb.Kap

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false

namespace GlobalTheory.CompanionTheory.KapRhoHom

private theorem dual_expand {K B : Type} {V : Type*} [Field K] [CommRing B] [AddCommGroup V] [Module K V]
    (o : K →+* B) (f : Module.Dual K V →+ B) (hf : ∀ (k : K) φ, f (k • φ) = o k * f φ)
    {m : ℕ} (bs : Module.Basis (Fin m) K V) (φ : Module.Dual K V) :
    f φ = ∑ s, f (bs.coord s) * o (φ (bs s)) := by
  have hφ : φ = ∑ s, φ (bs s) • bs.coord s := by
    refine bs.ext fun t => ?_
    simp [LinearMap.sum_apply, Finsupp.single_apply]
  conv_lhs => rw [hφ]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [hf, mul_comm]

theorem rho_hom :
    ∀ {Λ A B K Λ' A' B' : Type} [CommRing Λ] [CommRing A] [CommRing B] [Field K] [CommRing Λ']
      [CommRing A'] [CommRing B'] (C : Chain.{1} Λ A B K) (C' : Chain.{1} Λ' A' B' K)
      (h : Hom C C'), C.Good → C'.Good → h.Good → ∀ {j : ℕ} (x : ∀ n, C.S n j)
      (f : Module.Dual K (C.V j) →+ B), C.Rho x f →
        C'.Rho (fun n => h.fS n j (x n)) (h.tr j f) := by
  intro Λ A B K Λ' A' B' _ _ _ _ _ _ _ C C' h hC hC' hh j x f hR
  obtain ⟨hs, e, z, hz, hW⟩ := hR
  have htr : ∀ φ : Module.Dual K (C'.V j),
      h.tr j f φ = h.sB (f (Module.Dual.transpose (R := K) (h.fV j) φ)) := fun φ => rfl
  refine ⟨fun k φ => ?_, e, h.fZ j z, fun n => ?_, ?_⟩
  · rw [htr, htr, map_smul, hs, map_mul, hh.o]
  · rw [← hh.red, hz, map_smulₛₗ, hh.r, map_pow, map_natCast, hh.ℓ]
  · intro m bs'
    haveI := hC.fin j
    have bs := Module.finBasis K (C.V j)
    have hE := congrArg (h.fW j) (hW bs)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hh.b, map_smulₛₗ, map_sum, map_pow, map_natCast] at hE
    rw [← hE, hh.ℓ]
    congr 1
    have hexp : ∀ t, h.tr j f (bs'.coord t) =
        ∑ s, h.sB (f (bs.coord s)) * C'.o (bs'.coord t (h.fV j (bs s))) := by
      intro t
      set_option synthInstance.maxHeartbeats 100000 in
        rw [htr, dual_expand C.o f hs bs, map_sum]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [map_mul, hh.o]
      rfl
    have hμ : ∀ s, C'.μ j (h.fV j (bs s)) =
        ∑ t, C'.o (bs'.coord t (h.fV j (bs s))) • C'.μ j (bs' t) := by
      intro s
      conv_lhs => rw [← bs'.sum_repr (h.fV j (bs s))]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [map_smulₛₗ]
      rfl
    calc ∑ t, h.tr j f (bs'.coord t) • C'.μ j (bs' t)
        = ∑ t, ∑ s, (h.sB (f (bs.coord s)) * C'.o (bs'.coord t (h.fV j (bs s)))) • C'.μ j (bs' t) := by
          refine Finset.sum_congr rfl fun t _ => ?_
          rw [hexp, Finset.sum_smul]
      _ = ∑ s, ∑ t, (h.sB (f (bs.coord s)) * C'.o (bs'.coord t (h.fV j (bs s)))) • C'.μ j (bs' t) :=
          Finset.sum_comm
      _ = ∑ s, h.fW j (f (bs.coord s) • C.μ j (bs s)) := by
          refine Finset.sum_congr rfl fun s _ => ?_
          rw [map_smulₛₗ, hh.μ, hμ, Finset.smul_sum]
          refine Finset.sum_congr rfl fun t _ => ?_
          rw [mul_smul]

end GlobalTheory.CompanionTheory.KapRhoHom
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RealizationSmul
section
open CrystallineSemistableComparison.Pb.Kap

namespace GlobalTheory.CompanionTheory.KapChain

theorem rho_smul : ∀ {Λ A B K : Type} [CommRing Λ] [CommRing A] [CommRing B] [Field K] (C : Chain.{1} Λ A B K) {j : ℕ}
    (c : Λ) (x : ∀ n, C.S n j) (f : Module.Dual K (C.V j) →+ B), C.Rho x f →
    C.Rho (c • x) ((AddMonoidHom.mulLeft (C.ι (C.lam c))).comp f) := by
  intro Λ A B K _ _ _ _ C j c x f hf
  obtain ⟨h1, e, z, h2, h3⟩ := hf
  refine ⟨?_, e, C.lam c • z, ?_, ?_⟩
  · intro k φ
    simp only [AddMonoidHom.comp_apply, AddMonoidHom.coe_mulLeft, h1]
    ring
  · intro n
    rw [map_smul, h2 n, Pi.smul_apply, LinearMap.map_smulₛₗ, smul_comm]
  · intro m bs
    rw [LinearMap.map_smulₛₗ, ← h3 bs]
    simp only [AddMonoidHom.comp_apply, AddMonoidHom.coe_mulLeft, mul_smul]
    rw [← Finset.smul_sum, smul_comm]

end GlobalTheory.CompanionTheory.KapChain
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SectionInvarianceCosetSum
section
open Filter Topology

namespace GlobalTheory.CompanionTheory.RgEisCross


open PositivityTheory.RgEis in
theorem stage_eis : PositivityTheory.RgEis.PiLocalization₂ → ∀ (G : Type) [Group G] (W : Type) [NormedAddCommGroup W] [NormedSpace ℂ W] [CompleteSpace W]
    (Γ K Q P : Subgroup G) (c : G → ℂ) (ρ : K →* (W →L[ℂ] W)) (ξ lam : G → ℝ) (Λ : G → ℂ) (s : ℂ) (w : W) (Ms : ℝ),
    P ≤ Q → (∀ γ ∈ Γ, γ ∈ Q → ∀ x, ξ (γ * x) = ξ x) → (∀ γ ∈ Γ, γ ∈ P → ∀ x, Λ (γ * x) = Λ x) →
    (∀ γ ∈ Γ, γ ∈ P → ∀ x, PositivityTheory.RgEis.sec K P c ρ (γ * x) w = PositivityTheory.RgEis.sec K P c ρ x w) →
    (∀ x, ‖PositivityTheory.RgEis.sec K P c ρ x w‖ ≤ Ms) → PositivityTheory.RgEis.Conv Γ P lam →
    (∀ x, (Λ x + s * ξ x).re = lam x) → ∀ g : G,
    ∑' r : PositivityTheory.RgEis.Cos (Γ ⊓ Q) Γ, Complex.exp (s * ξ (PositivityTheory.RgEis.rep r * g)) •
        PositivityTheory.RgEis.eis (Γ ⊓ Q) K P c ρ Λ (PositivityTheory.RgEis.rep r * g) w =
      PositivityTheory.RgEis.eis Γ K P c ρ (fun x => Λ x + s * ξ x) g w := by
  intro hSt G _ W _ _ _ Γ K Q P c ρ ξ lam Λ s w Ms hPQ hξ hΛ hsec hMs hconv hre g
  set f : G → W := fun x => Complex.exp (Λ x + s * ξ x) • sec K P c ρ x w with hf
  have hfinv : ∀ γ ∈ Γ, γ ∈ P → ∀ x, f (γ * x) = f x := by
    intro γ hγ hP x
    simp only [hf]
    rw [hΛ γ hγ hP x, hξ γ hγ (hPQ hP) x, hsec γ hγ hP x]
  have hnorm : ∀ x, ‖f x‖ ≤ Ms * Real.exp (lam x) := by
    intro x
    simp only [hf]
    rw [norm_smul, Complex.norm_exp, hre x, mul_comm (Real.exp _)]
    exact mul_le_mul_of_nonneg_right (hMs x) (Real.exp_pos _).le
  have hsum : Summable fun q : Cos P Γ => ‖f (rep q * g)‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun q => hnorm _) ((hconv g).mul_left Ms)
  obtain ⟨-, -, hstage⟩ := hSt G W P (Γ ⊓ Q) Γ f inf_le_left (fun γ hγ hP => ⟨hγ, hPQ hP⟩) hfinv g hsum
  have hR : eis Γ K P c ρ (fun x => Λ x + s * ξ x) g w = ∑' q : Cos P Γ, f (rep q * g) := rfl
  rw [hR, hstage]
  unfold eis
  refine tsum_congr fun r => ?_
  rw [← tsum_const_smul'']
  refine tsum_congr fun q => ?_
  have hq : rep q ∈ Γ ⊓ Q := (Quotient.out q).2
  simp only [hf]
  rw [hξ _ (Subgroup.mem_inf.mp hq).1 (Subgroup.mem_inf.mp hq).2, Complex.exp_add, smul_smul, mul_comm]

end GlobalTheory.CompanionTheory.RgEisCross
end

