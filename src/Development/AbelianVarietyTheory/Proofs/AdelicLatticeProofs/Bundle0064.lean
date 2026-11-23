module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0057
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0061
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HasDerivAtZeroAndIsTheta
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsOpenNsmulAdelicCompletionOfVectorSet
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0062

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.DifferentiableOfChar
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FockTranslate

open GlobalTheory.SplitScalar GlobalTheory.LatVac

theorem differentiable_of_char (χ : ℝ → ℂ) (hc : Continuous χ) (h0 : χ 0 = 1)
    (hm : ∀ s t, χ (s + t) = χ s * χ t) : Differentiable ℝ χ := by
  first
  | exact @_root_.GlobalTheory.ContinuousHomDifferentiable.continuous_hom_differentiable
  | exact _root_.GlobalTheory.ContinuousHomDifferentiable.continuous_hom_differentiable
  | (apply _root_.GlobalTheory.ContinuousHomDifferentiable.continuous_hom_differentiable <;> assumption)
  | (intros; apply _root_.GlobalTheory.ContinuousHomDifferentiable.continuous_hom_differentiable <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ContinuousHomDifferentiable.continuous_hom_differentiable <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ContinuousHomDifferentiable.continuous_hom_differentiable ..)

variable {D : D7}

theorem differentiable_heisO {ψ : AddChar (AF D.host.F) ℂ} (hψ : Continuous ψ) {S T : HSp D} {f : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) (L : ℝ →+ WO S T) (hL : Continuous L) (hfin : ∀ t, (L t).map (finPart D) = 0)
    (w : WO S T) : Differentiable ℝ fun t : ℝ => heisO ψ S T (L t) f w := by
  have h1 : Differentiable ℝ fun t : ℝ => ψ (symplOH S T w (L t)) := by
    refine differentiable_of_char _ (hψ.comp (continuous_const.mul (continuous_symplO S T continuous_const hL))) ?_ ?_
    · rw [map_zero, symplOH, symplO_zero_right, mul_zero, AddChar.map_zero_eq_one]
    · intro s t
      rw [map_add (f := _), symplOH_add_right, AddChar.map_add_eq_mul]
  have h2 := hf.smooth 1 (L.comp (Pi.evalAddMonoidHom (fun _ : Fin 1 => ℝ) 0)) (hL.comp (continuous_apply 0))
    (fun t => hfin _) w
  have h3 : Differentiable ℝ fun t : ℝ => f (w + L t) :=
    (h2.differentiable (by simp)).comp (differentiable_pi.2 fun _ : Fin 1 => differentiable_id)
  exact h1.mul h3

theorem dRho_sum {ψ : AddChar (AF D.host.F) ℂ} (hψ : Continuous ψ) {θ : InfFam D} (hθ : IsInfFam θ) {S T : HSp D}
    {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ)
    {ι : Type} (s : Finset ι) (a : ι → WO S T) (c : ι → ℂ) (ha : ∀ i ∈ s, (a i).map (infPart D) = 0) :
    dRho (heisO ψ S T) θ τ z (∑ i ∈ s, c i • heisO ψ S T (a i) f) =
      ∑ i ∈ s, c i • heisO ψ S T (a i) (dRho (heisO ψ S T) θ τ z f) := by
  have hL : IsLineAt θ τ z (lineAt θ τ z) :=
    Classical.epsilon_spec (GlobalTheory.RealLineAt.lineAt_exists D θ hθ _ _ τ z)
  funext x
  have e : (fun t : ℝ => heisO ψ S T (lineAt θ τ z t) (∑ i ∈ s, c i • heisO ψ S T (a i) f) x) =
      fun t : ℝ => ∑ i ∈ s, (c i * ψ (symplOH S T x (a i))) * heisO ψ S T (lineAt θ τ z t) f (x + a i) := by
    funext t
    rw [heisO_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [heisO_smul, heisO_comm, symplO_real_fin S T (hL.2.1 t) (ha i hi), AddChar.map_zero_eq_one, one_smul,
      mul_assoc]
    rfl
  show deriv (fun t : ℝ => heisO ψ S T (lineAt θ τ z t) (∑ i ∈ s, c i • heisO ψ S T (a i) f) x) 0 = _
  rw [e, deriv_fun_sum fun i _ => ((differentiable_heisO hψ hf _ hL.1 hL.2.1 (x + a i)).const_mul _) 0,
    Finset.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [deriv_const_mul_field, mul_assoc]
  rfl

theorem isFockVacAt_sum : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D), IsCharAF D.host.F ψ → IsInfFam θ → ∀ f : WO S T → ℂ, IsThetaFunO ψ S T f → ∀ (τ : D.what₂.Tau) (J : Matrix (Fin T.rank) (Fin S.rank) ℂ → Matrix (Fin T.rank) (Fin S.rank) ℂ), IsFockVacAt (heisO ψ S T) θ τ J f → ∀ (ι : Type) (s : Finset ι) (a : ι → WO S T) (c : ι → ℂ), (∀ i ∈ s, (a i).map (infPart D) = 0) → IsFockVacAt (heisO ψ S T) θ τ J (∑ i ∈ s, c i • heisO ψ S T (a i) f) := by
  intro D ψ θ S T hψ hθ f hf τ J hv ι s a c ha z
  have hc : Continuous ψ := hψ.1
  have h0 : dRho (heisO ψ S T) θ τ z f + Complex.I • dRho (heisO ψ S T) θ τ (J z) f = 0 := hv z
  rw [annih, dRho_sum hc hθ hf τ z s a c ha, dRho_sum hc hθ hf τ (J z) s a c ha, Finset.smul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [smul_comm, ← smul_add, ← heisO_smul, ← heisL_apply, ← heisL_apply, ← map_add (f := _), h0, map_zero, smul_zero]

end GlobalTheory.FockTranslate

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EqZeroOfAeFundamentalDomain
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ContDiff Topology ENNReal

namespace GlobalTheory.WeilVacMove

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Filter

section Abstract

theorem ae_zero_of_lintegral_eq {X : Type} [MeasurableSpace X] (ν : Measure X) [IsFiniteMeasure ν]
    (a b : ℕ → X → ℂ) (c : X → ℂ) (C : ℝ) (ha : ∀ n, Measurable (a n)) (hb : ∀ n, Measurable (b n))
    (hc : Measurable c) (hC : ∀ n x, ‖a n x‖ ≤ C) (ha0 : ∀ x, Tendsto (fun n => a n x) atTop (𝓝 0))
    (hbc : ∀ x, Tendsto (fun n => b n x) atTop (𝓝 (c x)))
    (he : ∀ n, ∫⁻ x, ‖b n x‖ₑ ^ 2 ∂ν = ∫⁻ x, ‖a n x‖ₑ ^ 2 ∂ν) : ∀ᵐ x ∂ν, c x = 0 := by
  have hq : Continuous fun z : ℂ => ‖z‖ₑ ^ 2 := (ENNReal.continuous_pow 2).comp continuous_enorm
  have h1 : Tendsto (fun n => ∫⁻ x, ‖a n x‖ₑ ^ 2 ∂ν) atTop (𝓝 (∫⁻ _, 0 ∂ν)) := by
    refine tendsto_lintegral_of_dominated_convergence (fun _ => ENNReal.ofReal C ^ 2)
      (fun n => hq.measurable.comp (ha n)) (fun n => Eventually.of_forall fun x => ?_) ?_
      (Eventually.of_forall fun x => ?_)
    · refine pow_le_pow_left' ?_ 2
      rw [← ofReal_norm_eq_enorm]
      exact ENNReal.ofReal_le_ofReal (hC n x)
    · rw [lintegral_const]
      exact ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top) (measure_ne_top _ _)
    · simpa [Function.comp_def] using (hq.tendsto 0).comp (ha0 x)
  rw [lintegral_zero] at h1
  have h2 : ∫⁻ x, ‖c x‖ₑ ^ 2 ∂ν ≤ 0 := by
    have e : ∀ x, ‖c x‖ₑ ^ 2 = liminf (fun n => ‖b n x‖ₑ ^ 2) atTop := fun x =>
      ((hq.tendsto _).comp (hbc x)).liminf_eq.symm
    simp_rw [e]
    refine (lintegral_liminf_le fun n => hq.measurable.comp (hb n)).trans ?_
    have e2 : (fun n => ∫⁻ x, ((fun z : ℂ => ‖z‖ₑ ^ 2) ∘ b n) x ∂ν) = fun n => ∫⁻ x, ‖a n x‖ₑ ^ 2 ∂ν := funext he
    rw [e2]
    exact h1.liminf_eq.le
  have h3 := (lintegral_eq_zero_iff (hq.measurable.comp hc)).1 (le_antisymm h2 zero_le')
  filter_upwards [h3] with x hx
  simpa using hx

theorem eq_zero_of_ae_fundamentalDomain {G : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (Γ : AddSubgroup G) [DiscreteTopology Γ]
    (μ : Measure G) [μ.IsAddHaarMeasure] (𝓕 : Set G) (h𝓕 : IsAddFundamentalDomain Γ 𝓕 μ) (c : G → ℂ)
    (hc : Continuous c) (hp : ∀ γ ∈ Γ, ∀ w, ‖c (γ + w)‖ = ‖c w‖) (h0 : ∀ᵐ x ∂μ.restrict 𝓕, c x = 0) : c = 0 := by
  have : Countable Γ := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  have ho : IsOpen {x | c x ≠ 0} := isOpen_ne_fun hc continuous_const
  have h1 : μ {x | c x ≠ 0} = 0 := by
    refine h𝓕.measure_zero_of_invariant _ (fun g => ?_) ?_
    · ext x
      rw [Set.mem_vadd_set_iff_neg_vadd_mem]
      show c (((-g : Γ) : G) + x) ≠ 0 ↔ c x ≠ 0
      rw [← norm_ne_zero_iff, hp _ (-g).2, norm_ne_zero_iff]
    · rw [← Measure.restrict_apply ho.measurableSet]
      exact h0
  funext x
  by_contra hx
  exact (ho.measure_pos μ ⟨x, hx⟩).ne' h1

theorem tendsto_diffQuot {F : ℝ → ℂ} {d : ℂ} (h : HasDerivAt F d 0) :
    Tendsto (fun n : ℕ => ((1 / ((n : ℝ) + 1) : ℝ) : ℂ)⁻¹ * (F (1 / ((n : ℝ) + 1)) - F 0)) atTop (𝓝 d) := by
  have h1 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝[≠] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨tendsto_one_div_add_atTop_nhds_zero_nat, Eventually.of_forall fun n =>
      (Nat.one_div_pos_of_nat (n := n)).ne'⟩
  refine (h.tendsto_slope_zero.comp h1).congr fun n => ?_
  simp only [Function.comp_apply, zero_add, Complex.real_smul, Complex.ofReal_inv]

theorem norm_diffQuot_le {F F' : ℝ → ℂ} {C : ℝ} (h : ∀ s, HasDerivAt F (F' s) s) (hC : ∀ s, ‖F' s‖ ≤ C) (t : ℝ)
    (ht : t ≠ 0) : ‖(t : ℂ)⁻¹ * (F t - F 0)‖ ≤ C := by
  have h1 := convex_univ.norm_image_sub_le_of_norm_hasDerivWithin_le (f := F) (f' := F') (C := C)
    (fun s _ => (h s).hasDerivWithinAt) (fun s _ => hC s) (Set.mem_univ 0) (Set.mem_univ t)
  rw [sub_zero] at h1
  rw [norm_mul, norm_inv, Complex.norm_real, inv_mul_le_iff₀ (norm_pos_iff.2 ht), mul_comm]
  exact h1

end Abstract

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D}

theorem norm_periodic (hψ : IsStdChar D ψ (-1)) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    ∀ γ ∈ ratL T S, ∀ w, ‖f (γ + w)‖ = ‖f w‖ := by
  rintro _ ⟨γ, rfl⟩ w
  have := hf.quasi γ w
  exact (congrArg norm this).trans (by rw [norm_mul, hψ.1.2.1, one_mul])

theorem exists_bound (hψ : IsStdChar D ψ (-1)) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    ∃ C : ℝ, ∀ w, ‖f w‖ ≤ C := by
  obtain ⟨-, -, -, -, -, K, hK, hKc⟩ := GlobalTheory.AdelicMatrixLattice.lattice D T S
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hf.cont.continuousOn
  refine ⟨C, fun w => ?_⟩
  obtain ⟨γ, hγ, h⟩ := hKc w
  rw [← norm_periodic hψ hf γ hγ w]
  exact hC _ h

variable {χS χT : (AE D)ˣ →* Circle} {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}

theorem om_dLine (hW : IsWeilDatumO ψ S T χS χT om) (g : GA D S) (h : GA D T) {L L' : ℝ →+ WO S T}
    (hL : Continuous L) (hL0 : ∀ t, (L t).map (finPart D) = 0) (hL' : Continuous L')
    (hL0' : ∀ t, (L' t).map (finPart D) = 0) (e : ∀ t, L' t = actO S T g h (L t)) {f : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) : om (g, h) (dLine ψ S T L f) = dLine ψ S T L' (om (g, h) f) := by
  have hψ := hW.std
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hKc⟩ := GlobalTheory.AdelicMatrixLattice.lattice D T S
  have i6 : BorelSpace (WO S T) := ⟨rfl⟩
  obtain ⟨μ, 𝓕, hμ, h𝓕, h1⟩ := (GlobalTheory.meanSquare_addFundamentalDomain_of_cocompact (WO S T) (ratL T S) K hK hKc).1
  have : IsFiniteMeasure (μ.restrict 𝓕) := ⟨by rw [Measure.restrict_apply_univ, h1]; exact ENNReal.one_lt_top⟩
  have hF := hW.om_pres (g, h) f hf
  obtain ⟨hd, hdt⟩ := hasDerivAt_zero_and_isTheta hψ hL hL0 hf
  obtain ⟨hd', hdt'⟩ := hasDerivAt_zero_and_isTheta hψ hL' hL0' hF
  obtain ⟨C, hC⟩ := exists_bound hψ hdt
  let a : ℕ → WO S T → ℂ := fun n => ((1 / ((n : ℝ) + 1) : ℝ) : ℂ)⁻¹ •
    (heisO ψ S T (L (1 / ((n : ℝ) + 1))) f - f) - dLine ψ S T L f
  have hat : ∀ n, IsThetaFunO ψ S T (a n) := fun n =>
    isTheta_sub (isTheta_smul _ (isTheta_sub (isTheta_heisO_real hψ (hL0 _) hf) hf)) hdt
  have hct : IsThetaFunO ψ S T (dLine ψ S T L' (om (g, h) f) - om (g, h) (dLine ψ S T L f)) :=
    isTheta_sub hdt' (hW.om_pres _ _ hdt)
  have ha : ∀ n x, a n x = ((1 / ((n : ℝ) + 1) : ℝ) : ℂ)⁻¹ *
      (heisO ψ S T (L (1 / ((n : ℝ) + 1))) f x - heisO ψ S T (L 0) f x) - dLine ψ S T L f x := by
    intro n x
    rw [map_zero L, heisO_zero]
    rfl
  have hb : ∀ n x, om (g, h) (a n) x = ((1 / ((n : ℝ) + 1) : ℝ) : ℂ)⁻¹ *
      (heisO ψ S T (L' (1 / ((n : ℝ) + 1))) (om (g, h) f) x - heisO ψ S T (L' 0) (om (g, h) f) x) -
        om (g, h) (dLine ψ S T L f) x := by
    intro n x
    rw [map_zero L', heisO_zero, e, ← hW.om_heis g h _ f hf, map_sub, map_smul, map_sub]
    rfl
  have key := ae_zero_of_lintegral_eq (μ.restrict 𝓕) a (fun n => om (g, h) (a n)) _ (C + C)
    (fun n => (hat n).cont.measurable) (fun n => (hW.om_pres _ _ (hat n)).cont.measurable) hct.cont.measurable
    (fun n x => by
      rw [ha]
      refine (norm_sub_le _ _).trans (add_le_add ?_ (hC x))
      refine norm_diffQuot_le (hasDerivAt_line hψ hL hL0 hf x) (fun s => ?_) _ (Nat.one_div_pos_of_nat (n := n)).ne'
      rw [heisO, norm_mul, hψ.1.2.1, one_mul]
      exact hC _)
    (fun x => by
      have := (tendsto_diffQuot (hd x)).sub_const (dLine ψ S T L f x)
      rw [sub_self] at this
      exact this.congr fun n => (ha n x).symm)
    (fun x => ((tendsto_diffQuot (hd' x)).sub_const (om (g, h) (dLine ψ S T L f) x)).congr fun n => (hb n x).symm)
    (fun n => hW.om_unit μ 𝓕 hμ h𝓕 _ _ (hat n))
  exact (sub_eq_zero.1 (eq_zero_of_ae_fundamentalDomain (ratL T S) μ 𝓕 h𝓕 _ hct.cont (norm_periodic hψ hct) key)).symm

variable {θ : InfFam D}

theorem compAt_mul (θ : InfFam D) (τ : D.what₂.Tau) {k m n : ℕ} (x : Mx D k m) (y : Mx D m n) :
    compAt θ τ (HMul.hMul x y : Mx D k n) = compAt θ τ x * compAt θ τ y :=
  Matrix.map_mul (f := (θ τ).comp (infPart D))

theorem compAt_one (θ : InfFam D) (τ : D.what₂.Tau) {k : ℕ} : compAt θ τ (1 : Mx D k k) = 1 :=
  Matrix.map_one _ (map_zero ((θ τ).comp (infPart D))) (map_one ((θ τ).comp (infPart D)))

theorem mt_mul (V : HSp D) (g g' : GA D V) : mt V (g * g') = mt V g * mt V g' := by simp [Formalism.L2.Theta.mt]

theorem mt_one (V : HSp D) : mt V 1 = 1 := by simp [Formalism.L2.Theta.mt]

theorem compAt_mt_mul_inv (θ : InfFam D) (τ : D.what₂.Tau) (V : HSp D) (g : GA D V) :
    compAt θ τ (mt V g) * compAt θ τ (mt V g⁻¹) = 1 := by
  rw [← compAt_mul, ← mt_mul, mul_inv_cancel, mt_one, compAt_one]

theorem compAt_mt_inv_mul (θ : InfFam D) (τ : D.what₂.Tau) (V : HSp D) (g : GA D V) :
    compAt θ τ (mt V g⁻¹) * compAt θ τ (mt V g) = 1 := by
  rw [← compAt_mul, ← mt_mul, inv_mul_cancel, mt_one, compAt_one]

theorem compAt_actO (θ : InfFam D) (τ : D.what₂.Tau) (g : GA D S) (h : GA D T) (x : WO S T) :
    compAt θ τ (actO S T g h x) = compAt θ τ (mt T h) * compAt θ τ x * compAt θ τ (mt S g⁻¹) := by
  unfold actO
  rw [compAt_mul, compAt_mul]

theorem actO_add (g : GA D S) (h : GA D T) (x y : WO S T) :
    actO S T g h (x + y) = actO S T g h x + actO S T g h y := by
  unfold actO
  rw [Matrix.mul_add, Matrix.add_mul]

theorem lineAt_actO (hθ : IsInfFam θ) (τ : D.what₂.Tau) (g : GA D S) (h : GA D T)
    (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) (t : ℝ) :
    lineAt θ τ (compAt θ τ (mt T h) * z * compAt θ τ (mt S g⁻¹)) t = actO S T g h (lineAt θ τ z t) := by
  obtain ⟨h1, h2, h3⟩ := isLineAt_lineAt hθ τ z
  let M : ℝ →+ WO S T := AddMonoidHom.mk' (fun t => actO S T g h (lineAt θ τ z t)) fun s t => by
    rw [map_add (f := _), actO_add]
  have hM : IsLineAt θ τ (compAt θ τ (mt T h) * z * compAt θ τ (mt S g⁻¹)) M := by
    refine ⟨(continuous_const.matrix_mul h1).matrix_mul continuous_const, fun t => ?_, fun t τ' => ?_⟩
    · show (actO S T g h (lineAt θ τ z t)).map (finPart D) = 0
      unfold actO
      rw [Matrix.map_mul, Matrix.map_mul, h2, Matrix.mul_zero, Matrix.zero_mul]
    · show compAt θ τ' (actO S T g h (lineAt θ τ z t)) = _
      rw [compAt_actO, h3]
      split_ifs with hτ
      · rw [hτ, Matrix.mul_smul, Matrix.smul_mul]
      · rw [Matrix.mul_zero, Matrix.zero_mul]
  rw [GlobalTheory.RealLineAt.lineAt_unique D θ hθ _ _ τ _ _ _ (isLineAt_lineAt hθ τ _) hM]
  rfl

theorem om_dRho (hW : IsWeilDatumO ψ S T χS χT om) (hθ : IsInfFam θ) (g : GA D S) (h : GA D T) (τ : D.what₂.Tau)
    (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    om (g, h) (Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z f) =
      Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ (compAt θ τ (mt T h) * z * compAt θ τ (mt S g⁻¹)) (om (g, h) f) :=
  om_dLine hW g h (isLineAt_lineAt hθ τ z).1 (isLineAt_lineAt hθ τ z).2.1 (isLineAt_lineAt hθ τ _).1
    (isLineAt_lineAt hθ τ _).2.1 (lineAt_actO hθ τ g h z) hf

theorem cplxO_move (θ : InfFam D) (τ : D.what₂.Tau) (g : GA D S) (h : GA D T)
    {sS sS' : Matrix (Fin S.rank) (Fin S.rank) ℂ} {sT sT' : Matrix (Fin T.rank) (Fin T.rank) ℂ}
    (hS : sS' * compAt θ τ (mt S g) = compAt θ τ (mt S g) * sS)
    (hT : sT' * compAt θ τ (mt T h) = compAt θ τ (mt T h) * sT) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) :
    cplxO sS' sT' (compAt θ τ (mt T h) * z * compAt θ τ (mt S g⁻¹)) =
      compAt θ τ (mt T h) * cplxO sS sT z * compAt θ τ (mt S g⁻¹) := by
  have h1 : compAt θ τ (mt S g⁻¹) * sS' = sS * compAt θ τ (mt S g⁻¹) := by
    calc _ = compAt θ τ (mt S g⁻¹) * (sS' * compAt θ τ (mt S g)) * compAt θ τ (mt S g⁻¹) := by
          rw [Matrix.mul_assoc, Matrix.mul_assoc, compAt_mt_mul_inv, Matrix.mul_one]
      _ = _ := by rw [hS, ← Matrix.mul_assoc, compAt_mt_inv_mul, Matrix.one_mul]
  unfold cplxO
  rw [Matrix.mul_smul, Matrix.smul_mul]
  congr 1
  calc _ = (sT' * compAt θ τ (mt T h)) * z * (compAt θ τ (mt S g⁻¹) * sS') := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hT, h1]; simp only [Matrix.mul_assoc]

end GlobalTheory.WeilVacMove

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EventuallyFinEqOne
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinTranslate

open GlobalTheory.WeilVacMove

theorem eq_one_of_pow_near {z : ℂ} (hz : ‖z‖ = 1) (h : ∀ k : ℕ, ‖z ^ k - 1‖ < 1) : z = 1 := by
  by_contra hne
  have hb : ∀ n : ℕ, (n : ℝ) / 2 ≤ (∑ k ∈ Finset.range n, z ^ k).re := by
    intro n
    rw [Complex.re_sum]
    have hk : ∀ k ∈ Finset.range n, (1 / 2 : ℝ) ≤ (z ^ k).re := by
      intro k _
      have h1 : ‖z ^ k‖ ^ 2 = 1 := by rw [norm_pow, hz, one_pow, one_pow]
      have h2 : ‖z ^ k - 1‖ ^ 2 < 1 := by nlinarith [h k, norm_nonneg (z ^ k - 1)]
      rw [Complex.sq_norm, Complex.normSq_apply] at h1 h2
      simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im, sub_zero] at h2
      nlinarith
    have := Finset.card_nsmul_le_sum _ _ _ hk
    rw [Finset.card_range, nsmul_eq_mul] at this
    linarith
  have hp : 0 < ‖z - 1‖ := norm_pos_iff.2 (sub_ne_zero.2 hne)
  obtain ⟨n, hn⟩ := exists_nat_gt (2 / ‖z - 1‖)
  have h3 : (∑ k ∈ Finset.range n, z ^ k).re ≤ 1 / ‖z - 1‖ := by
    refine (Complex.re_le_norm _).trans ?_
    rw [geom_sum_eq hne, norm_div]
    exact div_le_div_of_nonneg_right (h n).le hp.le
  have h4 := hb n
  have h5 : 2 / ‖z - 1‖ = 2 * (1 / ‖z - 1‖) := by ring
  linarith

theorem eventually_fin_eq_one {F : Type} [Field F] [NumberField F] {ψ : AddChar (AF F) ℂ} (hψ : IsCharAF F ψ) :
    ∀ᶠ c : Af F in 𝓝 0, ψ (pairA F 0 c) = 1 := by
  have hp : Continuous fun α : Af F => pairA F 0 α := continuous_const.prodMk continuous_id
  have hc : Continuous fun α : Af F => ‖ψ (pairA F 0 α) - 1‖ := ((hψ.1.comp hp).sub continuous_const).norm
  have h0 : ‖ψ (pairA F 0 0) - 1‖ < 1 := by
    have : pairA F 0 0 = 0 := rfl
    rw [this, AddChar.map_zero_eq_one, sub_self, norm_zero]
    exact one_pos
  obtain ⟨N, hN, h⟩ := GlobalTheory.AdLat.OpenLat.exists_nsmul_adele F {α | ‖ψ (pairA F 0 α) - 1‖ < 1}
    ((isOpen_lt hc continuous_const).mem_nhds h0)
  refine Filter.mem_of_superset (GlobalTheory.AdLat.OpenLat.nsmul_integral_mem_nhds F N hN) ?_
  rintro _ ⟨a, ha, rfl⟩
  refine eq_one_of_pow_near (hψ.2.1 _) fun k => ?_
  have e : pairA F 0 (N • k • a) = k • pairA F 0 (N • a) :=
    Prod.ext (smul_zero k).symm (smul_comm N k a)
  have h1 : ‖ψ (pairA F 0 (N • k • a)) - 1‖ < 1 := h (k • a) fun v => nsmul_mem (ha v) k
  rwa [e, AddChar.map_nsmul_eq_pow] at h1

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D}

def annSub (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (a : WO S T) : AddSubgroup (WO S T) where
  carrier := {u | ψ (symplOH S T u a) = 1 ∧ ψ (symplOH S T a u) = 1}
  zero_mem' := ⟨by rw [symplOH_zero_left, AddChar.map_zero_eq_one],
    by rw [symplOH_zero_right, AddChar.map_zero_eq_one]⟩
  add_mem' hx hy := ⟨by rw [symplOH_add_left, AddChar.map_add_eq_mul, hx.1, hy.1, one_mul],
    by rw [symplOH_add_right, AddChar.map_add_eq_mul, hx.2, hy.2, one_mul]⟩
  neg_mem' {x} hx := by
    constructor
    · have : ψ (symplOH S T (-x + x) a) = 1 := by rw [neg_add_cancel, symplOH_zero_left, AddChar.map_zero_eq_one]
      rwa [symplOH_add_left, AddChar.map_add_eq_mul, hx.1, mul_one] at this
    · have : ψ (symplOH S T a (-x + x)) = 1 := by rw [neg_add_cancel, symplOH_zero_right, AddChar.map_zero_eq_one]
      rwa [symplOH_add_right, AddChar.map_add_eq_mul, hx.2, mul_one] at this

theorem isOpen_annSub (hψ : IsCharAF D.host.F ψ) {a : WO S T} (ha : a.map (infPart D) = 0) :
    IsOpen (annSub ψ S T a : Set (WO S T)) := by
  haveI : IsTopologicalAddGroup (AE D) := IsTopologicalRing.to_topologicalAddGroup
  haveI : IsTopologicalAddGroup (WO S T) := Pi.topologicalAddGroup
  refine (annSub ψ S T a).isOpen_of_mem_nhds (g := 0) ?_
  have key : ∀ φ : WO S T → AF D.host.F, Continuous φ → φ 0 = 0 → (∀ u, fstA D.host.F (φ u) = 0) →
      ∀ᶠ u in 𝓝 (0 : WO S T), ψ (φ u) = 1 := by
    intro φ hφ h0 h1
    have hc : Continuous fun u => sndA D.host.F (φ u) := continuous_snd.comp hφ
    have ht : Filter.Tendsto (fun u => sndA D.host.F (φ u)) (𝓝 0) (𝓝 0) :=
      hc.tendsto' 0 0 (by rw [h0, map_zero])
    refine (ht.eventually (eventually_fin_eq_one hψ)).mono fun u hu => ?_
    have e : pairA D.host.F 0 (sndA D.host.F (φ u)) = φ u := Prod.ext (h1 u).symm rfl
    rwa [e] at hu
  exact (key (fun u => symplOH S T u a) (continuous_symplOH S T continuous_id continuous_const)
      (symplOH_zero_left S T a) fun u => fst_symplOH S T u a (Or.inr ha)).and
    (key (fun u => symplOH S T a u) (continuous_symplOH S T continuous_const continuous_id)
      (symplOH_zero_right S T a) fun u => fst_symplOH S T a u (Or.inl ha))

theorem isTheta_heisO_fin (hψ : IsCharAF D.host.F ψ) {a : WO S T} (ha : a.map (infPart D) = 0) {f : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) : IsThetaFunO ψ S T (heisO ψ S T a f) := {
  quasi := heisO_quasi ψ S T a f hf.quasi
  level := by
    obtain ⟨U, hU, h1⟩ := hf.level
    refine ⟨U ⊓ annSub ψ S T a, hU.inter (isOpen_annSub hψ ha), fun u hu h0 => ?_⟩
    have h2 : ψ (symplOH S T u a) = 1 ∧ ψ (symplOH S T a u) = 1 := hu.2
    conv_rhs => rw [← h1 u hu.1 h0]
    rw [heisO_heisO, heisO_heisO, h2.1, h2.2, add_comm]
  cont := by
    haveI : IsTopologicalAddGroup (AE D) := IsTopologicalRing.to_topologicalAddGroup
    haveI : IsTopologicalAddGroup (WO S T) := Pi.topologicalAddGroup
    exact (hψ.1.comp (continuous_symplOH S T continuous_id continuous_const)).mul
      (hf.cont.comp (continuous_id.add continuous_const))
  smooth k L h1 h2 w := by
    have e : (fun t => heisO ψ S T a f (w + L t)) = fun t => ψ (symplOH S T w a) * f (w + a + L t) := by
      funext t
      rw [heisO, symplOH_add_left, (symplOH_fin_real S T a (L t) ha (h2 t)).2, add_zero, add_right_comm]
    rw [e]
    exact contDiff_const.mul (hf.smooth k L h1 h2 (w + a)) }

theorem isTheta_sum_heisO_fin : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D), IsCharAF D.host.F ψ → ∀ f : WO S T → ℂ, IsThetaFunO ψ S T f → ∀ (ι : Type) (s : Finset ι) (a : ι → WO S T) (c : ι → ℂ), (∀ i ∈ s, (a i).map (infPart D) = 0) → IsThetaFunO ψ S T (∑ i ∈ s, c i • heisO ψ S T (a i) f) := by
  intro D ψ S T hψ f hf ι s a c ha
  exact Finset.sum_induction _ (IsThetaFunO ψ S T) (fun _ _ => isTheta_add) isTheta_zero
    fun i hi => isTheta_smul _ (isTheta_heisO_fin hψ (ha i hi) hf)

end GlobalTheory.FinTranslate

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ScaledMatrixMemRationalLatticeStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.LatVac
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.scaled_matrix_mem_rational_lattice : ∀ (D : D7) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), Submodule.IsFullLattice D.host.E ΛS → Submodule.IsFullLattice D.host.E ΛT → ∀ M : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ∃ N : ℕ, 0 < N ∧ N • M ∈ latRat S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) := by
  intro D S T ΛS ΛT hS hT M
  first
  | exact GlobalTheory.LatVacFull.latRat_full D S T ΛS ΛT hS hT M
  | exact GlobalTheory.LatVacFull.latRat_full D S T ΛS ΛT hS.toIsLattice hT.toIsLattice M
end

