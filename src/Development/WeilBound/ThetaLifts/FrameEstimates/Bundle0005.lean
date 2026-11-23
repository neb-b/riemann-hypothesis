module

public import Mathlib
public import Development.WeilBound.ThetaLifts.FrameEstimates.SquareIntegrableWeilRange

@[expose] public section

-- bundled from Development.WeilBound.ThetaLifts.FrameEstimates.LatMeas
section
noncomputable section

namespace PositivityTheory.ThKEst

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace LatticeQuotientMeasure

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}


variable (F) in
def e0 : AF F := ((0 : Ainf F), (1 : Af F))

theorem at_iff {M : Type} [AddCommGroup M] [Module (AF F) M] (z : M) : At (evI F) z ↔ e0 F • z = 0 := by
  constructor
  · intro h
    apply h
    show (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace F) (0 : Ainf F) = 0
    exact map_zero _
  · intro h u hu
    have hu1 : u.1 = 0 := by
      have hu' : (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace F) u.1 = 0 := hu
      exact (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace F).injective (hu'.trans (map_zero _).symm)
    have hue : u = u * e0 F := by
      refine Prod.ext ?_ ?_
      · show u.1 = u.1 * (0 : Ainf F)
        rw [hu1, zero_mul]
      · show u.2 = u.2 * (1 : Af F)
        rw [mul_one]
    rw [hue, mul_smul, h, smul_zero]

variable (F) in
theorem t2Space_adeleRing_of_numberField : T2Space (AF F) := by
  haveI : T2Space (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F) :=
    T2Space.of_injective_continuous DFunLike.coe_injective RestrictedProduct.continuous_coe
  haveI : T2Space (NumberField.InfiniteAdeleRing F) :=
    show T2Space ((v : InfinitePlace F) → v.Completion) from inferInstance
  show T2Space (NumberField.InfiniteAdeleRing F × IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)
  infer_instance

variable (F E) in
theorem t2Space_cm_host_adeles : T2Space (AE F E) := by
  haveI := t2Space_adeleRing_of_numberField F
  let b := Algebra.TensorProduct.basis (AF F) (Module.finBasis F E)
  exact T2Space.of_injective_continuous (X := AE F E) b.equivFun.injective
    (IsModuleTopology.continuous_of_linearMap (A := AE F E) b.equivFun.toLinearMap)

variable (F E) in
theorem ring_AE : IsTopologicalRing (AE F E) := by
  exact IsModuleTopology.isTopologicalRing (AF F) (AE F E)

omit [NumberField E] in
theorem continuous_piInf {w : InfinitePlace F} (τ : EmbOver E w) : Continuous (piInf τ) := by
  let φ : AF F →+* ℂ := (NumberField.InfinitePlace.Completion.extensionEmbedding w).comp
    (GlobalTheory.AdelicU.evInf F w).toRingHom
  have hφ : Continuous φ :=
    (NumberField.InfinitePlace.Completion.isometry_extensionEmbedding w).continuous.comp
      ((continuous_apply w).comp continuous_fst)
  letI : Module (AF F) ℂ := Module.compHom ℂ φ
  haveI : ContinuousSMul (AF F) ℂ := ⟨(hφ.comp continuous_fst).mul continuous_snd⟩
  have hpt : ∀ (b : AF F) (e : E), piInf τ (b ⊗ₜ[F] e) = φ b * (τ.1 e) := fun b e => rfl
  let Lm : AE F E →ₗ[AF F] ℂ :=
    { toFun := piInf τ
      map_add' := map_add _
      map_smul' := by
        intro a x
        induction x using TensorProduct.induction_on with
        | zero => simp
        | tmul b e =>
          rw [TensorProduct.smul_tmul', hpt, hpt, smul_eq_mul, map_mul]
          show φ a * φ b * τ.1 e = φ a * (φ b * τ.1 e)
          ring
        | add x y hx hy =>
          rw [smul_add, map_add (f := _), hx, hy, map_add (f := _), smul_add] }
  exact IsModuleTopology.continuous_of_linearMap Lm

variable {n d : ℕ}

theorem continuous_sz (τ : ∀ w : InfinitePlace F, EmbOver E w) : Continuous (sz τ : Ten F E n d → ℝ) := by
  exact continuous_finsetSum _ fun w _ => continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
    ((continuous_piInf (τ w)).comp (continuous_id.matrix_elem i j)).norm

theorem isClosed_supp {C : Set (Ten F E n d)} (hC : IsCompact C) :
    IsClosed {z : Ten F E n d | ∃ c ∈ C, At (evI F) (z - c)} := by
  haveI := t2Space_cm_host_adeles F E
  have hset : {z : Ten F E n d | ∃ c ∈ C, At (evI F) (z - c)} =
      (fun z : Ten F E n d => e0 F • z) ⁻¹' ((fun c : Ten F E n d => e0 F • c) '' C) := by
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_image, at_iff, smul_sub, sub_eq_zero]
    constructor
    · rintro ⟨c, hc, hzc⟩
      exact ⟨c, hc, hzc.symm⟩
    · rintro ⟨c, hc, hzc⟩
      exact ⟨c, hc, hzc.symm⟩
  rw [hset]
  exact (hC.image (continuous_const_smul (e0 F))).isClosed.preimage (continuous_const_smul (e0 F))

theorem measurable_maj {G : Type} [TopologicalSpace G] [MeasurableSpace G] [BorelSpace G]
    (τ : ∀ w : InfinitePlace F, EmbOver E w) {C : Set (Ten F E n d)} (hC : IsCompact C) (N : ℕ)
    {f : G → Ten F E n d} (hf : Continuous f) : Measurable fun g => maj τ C N (f g) := by
  have hcl := isClosed_supp (F := F) (E := E) (n := n) (d := d) hC
  delta maj
  refine Measurable.ite (hcl.preimage hf).measurableSet ?_ measurable_const
  exact ((continuous_const.add ((continuous_sz τ).comp hf)).measurable.pow_const N).inv

omit [NumberField E] in
theorem continuous_mat_inv {J : Matrix (Fin n) (Fin n) E} : Continuous fun g : UA σ J => mat g⁻¹ := by
  exact Units.continuous_coe_inv.comp continuous_subtype_val

end LatticeQuotientMeasure


open LatticeQuotientMeasure in
theorem latMeas : LatMeas := by
  intro F E _ _ _ _ _ σ _ τ n d J J' _ _ C N S hC h
  haveI := ring_AE F E
  haveI := t2Space_cm_host_adeles F E
  haveI : Countable E := Countable.of_equiv _ (Module.finBasis ℚ E).equivFun.toEquiv.symm
  haveI : Countable (Matrix (Fin n) (Fin d) E) := show Countable (Fin n → Fin d → E) from inferInstance
  haveI : BorelSpace (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ J) := ⟨rfl⟩
  delta latSum
  refine Measurable.tsum fun x => ENNReal.measurable_ofReal.comp ?_
  exact measurable_maj τ hC N ((continuous_mat_inv.matrix_mul continuous_const).matrix_mul continuous_const)

end PositivityTheory.ThKEst

end
end

-- bundled from Development.WeilBound.ThetaLifts.FrameEstimates.OneVar
section
noncomputable section

namespace PositivityTheory.ThKEst

open scoped NNReal ENNReal
open MeasureTheory Metric

section

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

omit [NormedSpace ℝ V] [FiniteDimensional ℝ V] in
theorem oneVar_sep (Λ : Submodule ℤ V) [DiscreteTopology Λ] :
    ∃ ε : ℝ, 0 < ε ∧ Pairwise (Function.onFun Disjoint fun x : Λ => ball (x : V) ε) := by
  obtain ⟨δ, hδ, h⟩ := Metric.isOpen_iff.1 (isOpen_discrete ({0} : Set Λ)) 0 rfl
  refine ⟨δ / 2, by positivity, fun x y hxy => ?_⟩
  apply Metric.ball_disjoint_ball
  by_contra hlt
  push Not at hlt
  apply hxy
  have hm : x - y ∈ ball (0 : Λ) δ := by
    rw [mem_ball_zero_iff]
    have : ‖x - y‖ = dist (x : V) (y : V) := by
      rw [dist_eq_norm]; rfl
    linarith
  exact sub_eq_zero.1 (h hm)

omit [NormedSpace ℝ V] [FiniteDimensional ℝ V] in
theorem oneVar_pt {c ε : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) (hε : 0 < ε) (N : ℕ) {x y : V} (hy : y ∈ ball x ε) :
    ((1 + c * ‖x‖) ^ N)⁻¹ ≤ (1 + ε) ^ N * ((1 + ‖c • (1 : ℝ)‖ * ‖y‖) ^ N)⁻¹ := by
  have hcn : ‖c • (1 : ℝ)‖ = c := by simp [abs_of_pos hc]
  rw [hcn]
  have h1 : ‖y‖ ≤ ‖x‖ + ε := by
    have := mem_ball_iff_norm.1 hy
    have h2 := norm_le_norm_add_norm_sub' y x
    linarith
  have hx := norm_nonneg x
  have hy0 := norm_nonneg y
  have h2 : 1 + c * ‖y‖ ≤ (1 + ε) * (1 + c * ‖x‖) := by
    have : c * ‖y‖ ≤ c * (‖x‖ + ε) := mul_le_mul_of_nonneg_left h1 hc.le
    have h3 : c * ε ≤ ε := by nlinarith
    have h4 : 0 ≤ ε * (c * ‖x‖) := by positivity
    nlinarith
  rw [← div_eq_mul_inv, le_div_iff₀ (by positivity), inv_mul_eq_div, div_le_iff₀ (by positivity), ← mul_pow]
  exact pow_le_pow_left₀ (by positivity) h2 N

theorem oneVar_core (Λ : Submodule ℤ V) [DiscreteTopology Λ] (N : ℕ) (hN : Module.finrank ℝ V < N) :
    ∃ K : ℝ≥0, ∀ c : ℝ, 0 < c → c ≤ 1 →
      ∑' x : Λ, ENNReal.ofReal (((1 + c * ‖(x : V)‖) ^ N)⁻¹) ≤ K * ENNReal.ofReal ((c ^ Module.finrank ℝ V)⁻¹) := by
  borelize V
  haveI : ProperSpace V := FiniteDimensional.proper_real V
  haveI : Countable Λ := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  set μ : Measure V := Measure.addHaar with hμ
  obtain ⟨ε, hε, hd⟩ := oneVar_sep Λ
  set f : V → ℝ≥0∞ := fun y => ENNReal.ofReal (((1 + ‖y‖) ^ N)⁻¹) with hf
  have hfm : Measurable f := by
    rw [hf]; fun_prop
  have hI : ∫⁻ y, f y ∂μ < ⊤ := by
    have := finite_integral_one_add_norm (E := V) (μ := μ) (r := (N : ℝ)) (by exact_mod_cast hN)
    refine lt_of_eq_of_lt (lintegral_congr fun y => ?_) this
    rw [hf, Real.rpow_neg (by positivity), Real.rpow_natCast]
  set b : ℝ≥0∞ := μ (ball (0 : V) ε) with hb
  have hb0 : b ≠ 0 := (measure_ball_pos μ _ hε).ne'
  have hbt : b ≠ ⊤ := measure_ball_lt_top.ne
  set A : ℝ≥0∞ := ENNReal.ofReal ((1 + ε) ^ N) with hA
  have hK : b⁻¹ * A * ∫⁻ y, f y ∂μ ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.inv_ne_top.2 hb0) ENNReal.ofReal_ne_top) hI.ne
  refine ⟨(b⁻¹ * A * ∫⁻ y, f y ∂μ).toNNReal, fun c hc hc1 => ?_⟩
  rw [ENNReal.coe_toNNReal hK]
  have hsc : ∫⁻ y, f (c • y) ∂μ = ENNReal.ofReal ((c ^ Module.finrank ℝ V)⁻¹) * ∫⁻ y, f y ∂μ := by
    rw [← lintegral_map hfm (measurable_const_smul c), Measure.map_addHaar_smul μ hc.ne', lintegral_smul_measure,
      abs_of_pos (by positivity), smul_eq_mul]
  have hpt : ∀ x : Λ, b * ENNReal.ofReal (((1 + c * ‖(x : V)‖) ^ N)⁻¹) ≤ A * ∫⁻ y in ball (x : V) ε, f (c • y) ∂μ := by
    intro x
    have e1 : b = μ (ball (x : V) ε) := (Measure.addHaar_ball_center μ _ _).symm
    rw [e1, mul_comm, ← setLIntegral_const, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine setLIntegral_mono' measurableSet_ball fun y hy => ?_
    simp only [hf]
    rw [← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have := oneVar_pt hc hc1 hε N hy
    simpa [norm_smul] using this
  have hsum : b * ∑' x : Λ, ENNReal.ofReal (((1 + c * ‖(x : V)‖) ^ N)⁻¹) ≤ A * ∫⁻ y, f (c • y) ∂μ := by
    rw [← ENNReal.tsum_mul_left]
    refine (ENNReal.tsum_le_tsum hpt).trans ?_
    rw [ENNReal.tsum_mul_left, ← lintegral_iUnion (fun _ => measurableSet_ball) hd]
    gcongr
    exact Measure.restrict_le_self
  calc ∑' x : Λ, ENNReal.ofReal (((1 + c * ‖(x : V)‖) ^ N)⁻¹)
      = b⁻¹ * (b * ∑' x : Λ, ENNReal.ofReal (((1 + c * ‖(x : V)‖) ^ N)⁻¹)) := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel hb0 hbt, one_mul]
    _ ≤ b⁻¹ * (A * ∫⁻ y, f (c • y) ∂μ) := by gcongr
    _ = _ := by rw [hsc]; ring

end

theorem oneVar_of : OneVar := by
  intro V _ _ _ Λ _ N hN
  obtain ⟨K, hK⟩ := oneVar_core Λ N hN
  refine ⟨K, fun l => ?_⟩
  have h := hK (Real.exp (-max 0 l)) (Real.exp_pos _) (Real.exp_le_one_iff.2 (by simp))
  rw [← Real.exp_nat_mul, ← Real.exp_neg, mul_neg, neg_neg] at h
  refine le_trans (ENNReal.tsum_le_tsum fun x => ENNReal.ofReal_le_ofReal ?_) h
  have : Real.exp (-max 0 l) ≤ Real.exp (-l) := Real.exp_le_exp.2 (neg_le_neg (le_max_right _ _))
  gcongr

end PositivityTheory.ThKEst

end
end

-- bundled from Development.WeilBound.ThetaLifts.FrameEstimates.Parity
section
noncomputable section

namespace PositivityTheory.ThKEst

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace ParityOfCoefficients

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

theorem neg_mem_schA {Φ : (κ → AF F) → ℂ} (h : Φ ∈ schA F κ) : (fun x => Φ (-x)) ∈ schA F κ := by
  classical
  induction h using Submodule.span_induction with
  | mem Φ hΦ =>
    obtain ⟨f, g, hg, rfl⟩ := hΦ
    refine Submodule.subset_span ⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (ContinuousLinearEquiv.neg ℝ) f,
      fun y => g (-y), ⟨hg.1.comp_continuous continuous_neg, hg.2.comp_homeomorph (Homeomorph.neg _)⟩, ?_⟩
    funext x
    simp only [pureA, SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply,
      ContinuousLinearEquiv.neg_apply]
    congr 2
    funext i
    exact map_neg (InfiniteAdeleRing.ringEquiv_mixedSpace F) (x i).1
  | zero => exact Submodule.zero_mem _
  | add a b _ _ ha hb => exact Submodule.add_mem _ ha hb
  | smul c a _ ha => exact Submodule.smul_mem _ c ha

theorem exists_haar : ∃ μ : Measure (κ → AF F), μ.IsAddHaarMeasure ∧
    ∀ f : (κ → AF F) → ℂ, ∫ x, f (-x) ∂μ = ∫ x, f x ∂μ := by
  haveI : BorelSpace (κ → AF F) := ⟨rfl⟩
  obtain ⟨K⟩ : Nonempty (TopologicalSpace.PositiveCompacts (κ → AF F)) := inferInstance
  exact ⟨Measure.addHaarMeasure K, inferInstance, fun f => integral_neg_eq_self f _⟩

theorem coef_neg (ψ : AddChar (AF F) ℂ) (μ : Measure (κ → AF F))
    (hμ : ∀ f : (κ → AF F) → ℂ, ∫ x, f (-x) ∂μ = ∫ x, f x ∂μ) (Φ₁ Φ₂ : (κ → AF F) → ℂ)
    (w : (κ → AF F) × (κ → AF F)) :
    coef F ψ μ Φ₁ Φ₂ (-w) = coef F ψ μ (fun x => Φ₁ (-x)) (fun x => Φ₂ (-x)) w := by
  unfold coef
  rw [← hμ]
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  simp only [schr, Prod.fst_neg, Prod.snd_neg, neg_dotProduct_neg, neg_add]

variable {E : Type} [Field E] [NumberField E] [Algebra F E]

def negOne (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) : UA σ J :=
  ⟨-1, by
    change ((-1 : GL (Fin n) (AE F E)) : Matrix (Fin n) (Fin n) (AE F E))ᵀ * incM F J *
      ((-1 : GL (Fin n) (AE F E)) : Matrix (Fin n) (Fin n) (AE F E)).map (cA σ) = incM F J
    rw [Units.val_neg, Units.val_one, Matrix.map_neg _ (map_neg (cA σ)),
      Matrix.map_one _ (map_zero (cA σ)) (map_one (cA σ))]
    simp⟩

theorem mat_negOne_inv (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) : mat (negOne σ J)⁻¹ = -1 := rfl

theorem mat_one_inv (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) : mat (1 : UA σ J)⁻¹ = 1 := rfl

end ParityOfCoefficients


open ParityOfCoefficients in
theorem parity_of (hC : CoefEq) (hF : FourierInj) : Parity := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hp
  obtain ⟨μ, hμ, hneg⟩ := exists_haar (F := F) (κ := Fin n × Fin d)
  have pres : ∀ Φ ∈ schA F (Fin n × Fin d), om (negOne σ X.J, 1) Φ ∈ schA F (Fin n × Fin d) :=
    fun Φ hΦ => (IsUWeilPair.isUSplitting hp.weil).pres _ Φ hΦ
  have key : ∀ Φ₁ ∈ schA F (Fin n × Fin d), ∀ Φ₂ ∈ schA F (Fin n × Fin d), ∀ x u,
      om (negOne σ X.J, 1) Φ₁ x * (starRingEnd ℂ) (om (negOne σ X.J, 1) Φ₂ u) =
        Φ₁ (-x) * (starRingEnd ℂ) (Φ₂ (-u)) := by
    intro Φ₁ h₁ Φ₂ h₂
    refine hF F _ B.ψ hp.base.std μ hμ _ (pres _ h₁) _ (pres _ h₂) _ (neg_mem_schA h₁) _ (neg_mem_schA h₂) ?_
    funext w
    obtain ⟨z, rfl⟩ := M.co.e.surjective w
    rw [hC F E σ B n d X W M χX χW om r s r' s' hp μ hμ Φ₁ h₁ Φ₂ h₂, ← coef_neg B.ψ μ hneg, mat_negOne_inv,
      mat_one_inv, Matrix.transpose_one, Matrix.mul_one, Matrix.neg_mul, Matrix.one_mul, map_neg]
  by_cases h0 : ∃ Φ₀ ∈ schA F (Fin n × Fin d), ∃ u, Φ₀ (-u) ≠ 0
  · obtain ⟨Φ₀, hΦ₀, u, hu⟩ := h0
    have h1 := congrArg norm (key Φ₀ hΦ₀ Φ₀ hΦ₀ u u)
    simp only [norm_mul, Complex.norm_conj] at h1
    have h2 : ‖om (negOne σ X.J, 1) Φ₀ u‖ = ‖Φ₀ (-u)‖ :=
      (mul_self_inj_of_nonneg (norm_nonneg _) (norm_nonneg _)).mp h1
    have h3 : ‖Φ₀ (-u)‖ ≠ 0 := norm_ne_zero_iff.mpr hu
    have h4 : (starRingEnd ℂ) (om (negOne σ X.J, 1) Φ₀ u) ≠ 0 := by
      rw [← norm_ne_zero_iff, Complex.norm_conj, h2]; exact h3
    refine ⟨negOne σ X.J, (starRingEnd ℂ) (Φ₀ (-u)) / (starRingEnd ℂ) (om (negOne σ X.J, 1) Φ₀ u), rfl, ?_,
      fun Φ hΦ => funext fun x => ?_⟩
    · rw [norm_div, Complex.norm_conj, Complex.norm_conj, h2, div_self h3]
    · rw [Pi.smul_apply, smul_eq_mul, div_mul_eq_mul_div, eq_div_iff h4, key Φ hΦ Φ₀ hΦ₀, mul_comm]
  · refine ⟨negOne σ X.J, 1, rfl, norm_one, fun Φ hΦ => ?_⟩
    have z : ∀ Ψ ∈ schA F (Fin n × Fin d), Ψ = 0 := fun Ψ hΨ => funext fun x => by
      by_contra hx
      exact h0 ⟨Ψ, hΨ, -x, by rwa [neg_neg]⟩
    rw [z _ (pres Φ hΦ), one_smul, z _ (neg_mem_schA hΦ)]

end PositivityTheory.ThKEst

end
end

