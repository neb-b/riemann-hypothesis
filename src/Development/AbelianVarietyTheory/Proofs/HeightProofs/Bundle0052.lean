module

public import Mathlib
public import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.Bundle0005
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0003
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0002
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasTypeAllAddOfEquiv
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0209
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0171
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoefBoundOfCasselmanWallach
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0208
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0048
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0047
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0051
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0046
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.FiniteDimensionalPolyV
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0050
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0049

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.CompactAverageContinuousOnUniformModerateGrowth
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
open MeasureTheory Filter Topology

namespace GlobalTheory.KAvgGrowth

theorem continuousOn_and_umg_kAvg : ∀ (n : ℕ) (ε : Fin n → Bool) (f : GlobalTheory.TypeSum.Mx n → ℂ), ContinuousOn f (UJset ε) → GlobalTheory.TypeSum.UMG ε f →
    ∀ e : ↥(Formalism.REAL.KG ε) → ℂ, Continuous e →
    ContinuousOn (fun y => ∫ k, e k * f (y * Formalism.REAL.toMK k) ∂(Formalism.REAL.muK ε)) (UJset ε) ∧
    GlobalTheory.TypeSum.UMG ε (fun y => ∫ k, e k * f (y * Formalism.REAL.toMK k) ∂(Formalism.REAL.muK ε)) := by
  classical
  intro n ε f hf hU e he
  obtain ⟨N, F, hF0, hFd, hFg⟩ := hU
  refine ⟨_root_.GlobalTheory.AvgCont.continuousOn_avg_right_translates n ε f hf e he, ?_⟩
  let B := Module.finBasis ℝ (GlobalTheory.LowTypeDetermined.lie (Jm ε))
  let b : Fin (Module.finrank ℝ (GlobalTheory.LowTypeDetermined.lie (Jm ε))) → Mx n := fun i => (B i : Mx n)
  have hb : ∀ i, b i ∈ lieSet ε := fun i => by rw [lieSet_eq_lie]; exact (B i).2
  let c : Fin (Module.finrank ℝ (GlobalTheory.LowTypeDetermined.lie (Jm ε))) → Mx n → ℝ := fun i Z =>
    if h : Z ∈ lieSet ε then B.repr ⟨Z, by rwa [lieSet_eq_lie] at h⟩ i else 0
  have hsum : ∀ Z ∈ lieSet ε, Z = ∑ i, c i Z • b i := by
    intro Z hZ
    have hZ' : Z ∈ GlobalTheory.LowTypeDetermined.lie (Jm ε) := by rwa [lieSet_eq_lie] at hZ
    have := congrArg Subtype.val (B.sum_repr ⟨Z, hZ'⟩)
    rw [Submodule.coe_sum] at this
    simp only [Submodule.coe_smul] at this
    simp only [c, dif_pos hZ]
    exact this.symm
  have hli : LinearIndependent ℝ b :=
    B.linearIndependent.map' (GlobalTheory.LowTypeDetermined.lie (Jm ε)).subtype (Submodule.ker_subtype _)
  have hC : ∀ l : List (Mx n), (∀ Y ∈ l, Y ∈ lieSet ε) → ∀ Z ∈ lieSet ε, ∀ g ∈ UJset ε,
      F (Z :: l) g = ∑ i, (c i Z : ℂ) * F (b i :: l) g := by
    intro l hl Z hZ g hg
    obtain ⟨τ, hτ0, hτ, hev⟩ := _root_.GlobalTheory.SecondKindChart.exp_eq_expProd_near_zero n ε _ b hb hli (fun Z hZ => ⟨fun i => c i Z, hsum Z hZ⟩) (fun i => c i Z)
    have h2 := _root_.GlobalTheory.TypeSum.hasFDerivAt_derFam_prodExp n ε N F hFd hFg l hl _ b hb g hg
    rw [← hτ0] at h2
    have h3 := h2.comp_hasDerivAt (0 : ℝ) hτ
    have h4 : HasDerivAt (fun t : ℝ => F l (g * NormedSpace.exp (t • Z))) (F (Z :: l) g) 0 := hFd l hl Z hZ g hg
    have h5 : (fun t : ℝ => F l (g * NormedSpace.exp (t • Z))) =ᶠ[nhds 0]
        ((fun t : Fin _ → ℝ => F l (g * (List.ofFn fun i => NormedSpace.exp (t i • b i)).prod)) ∘ τ) := by
      filter_upwards [hev] with t ht
      rw [← hsum Z hZ] at ht
      simp only [Function.comp_apply, ht]
    have h6 := h4.unique (h3.congr_of_eventuallyEq h5)
    rw [h6]
    simp only [ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.smulRight_apply,
      ContinuousLinearMap.proj_apply, Complex.real_smul]
  have hD := _root_.GlobalTheory.TypeSum.derFam_expand_words n ε F hFd _ b c hb hC
  have hK : ∀ k : ↥(KG ε), toMK k ∈ UJset ε := fun k => K_le_UJ (toMK_mem_K k)
  have had : ∀ (k : ↥(KG ε)) (X : Mx n), X ∈ lieSet ε → (toMK k)⁻¹ * X * toMK k ∈ lieSet ε := by
    intro k X hX
    rw [lieSet_eq_lie] at hX ⊢
    exact GlobalTheory.LowTypeDetermined.conj_mem_lie (isUnit_Jm ε) (hK k) hX
  have hinvc : Continuous fun k : ↥(KG ε) => (toMK k)⁻¹ := by
    have e1 : (fun k : ↥(KG ε) => (toMK k)⁻¹) = fun k => toMK k⁻¹ := by
      funext k
      exact (Matrix.coe_units_inv _).symm
    rw [e1]
    exact (continuous_toMK ε).comp continuous_inv
  have hcc : ∀ i (X : Mx n), X ∈ lieSet ε → Continuous fun k : ↥(KG ε) => c i ((toMK k)⁻¹ * X * toMK k) := by
    intro i X hX
    have hX' : ∀ k : ↥(KG ε), (toMK k)⁻¹ * X * toMK k ∈ GlobalTheory.LowTypeDetermined.lie (Jm ε) := fun k => by
      have := had k X hX; rwa [lieSet_eq_lie] at this
    have e1 : (fun k : ↥(KG ε) => c i ((toMK k)⁻¹ * X * toMK k)) =
        fun k => B.repr ⟨(toMK k)⁻¹ * X * toMK k, hX' k⟩ i := by
      funext k
      simp only [c, dif_pos (had k X hX)]
    rw [e1]
    have hm : Continuous fun k : ↥(KG ε) => (⟨(toMK k)⁻¹ * X * toMK k, hX' k⟩ : GlobalTheory.LowTypeDetermined.lie (Jm ε)) :=
      ((hinvc.matrix_mul continuous_const).matrix_mul (continuous_toMK ε)).subtype_mk _
    exact ((B.coord i).continuous_of_finiteDimensional).comp hm
  have e1 : ∀ (l : List (Mx n)) (k : ↥(KG ε)), (l.map fun X => (toMK k)⁻¹ * X * toMK k) =
      List.ofFn fun j => (toMK k)⁻¹ * l.get j * toMK k := by
    intro l k
    conv_lhs => rw [← List.ofFn_get l]
    rw [List.map_ofFn]; rfl
  have hbw : ∀ {m : ℕ} (J : Fin m → Fin (Module.finrank ℝ (GlobalTheory.LowTypeDetermined.lie (Jm ε)))),
      ∀ Y ∈ List.ofFn (fun j => b (J j)), Y ∈ lieSet ε := by
    intro m J Y hY
    obtain ⟨j, rfl⟩ := (List.mem_ofFn' _ _).1 hY
    exact hb _
  have hUb : ∀ l : List (Mx n), (∀ Y ∈ l, Y ∈ lieSet ε) → ∃ C : ℝ, ∀ k : ↥(KG ε), ∀ g ∈ UJset ε,
      ‖F (l.map fun X => (toMK k)⁻¹ * X * toMK k) g‖ ≤ C * (1 + hs g) ^ N := by
    intro l hl
    have hcb : ∀ i (j : Fin l.length), ∃ M : ℝ, ∀ k : ↥(KG ε), |c i ((toMK k)⁻¹ * l.get j * toMK k)| ≤ M := by
      intro i j
      obtain ⟨M, hM⟩ := (isCompact_univ.image (hcc i _ (hl _ (List.get_mem l j)))).isBounded.exists_norm_le
      exact ⟨M, fun k => by simpa [Real.norm_eq_abs] using hM _ ⟨k, Set.mem_univ _, rfl⟩⟩
    choose M hM using hcb
    have hCJ : ∀ J : Fin l.length → Fin (Module.finrank ℝ (GlobalTheory.LowTypeDetermined.lie (Jm ε))), ∃ C : ℝ,
        ∀ g ∈ UJset ε, ‖F (List.ofFn fun j => b (J j)) g‖ ≤ C * (1 + hs g) ^ N := fun J => hFg _ (hbw J)
    choose CJ hCJ using hCJ
    refine ⟨∑ J : Fin l.length → Fin (Module.finrank ℝ (GlobalTheory.LowTypeDetermined.lie (Jm ε))),
      (∏ j, |M (J j) j|) * |CJ J|, fun k g hg => ?_⟩
    rw [e1, hD _ _ (fun j => had k _ (hl _ (List.get_mem l j))) g hg, Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun J _ => ?_)
    rw [norm_mul, norm_prod, mul_assoc]
    have hw : 0 ≤ (1 + hs g) ^ N := pow_nonneg (by linarith [hs_nonneg g]) _
    refine mul_le_mul (Finset.prod_le_prod₀ (fun j _ => norm_nonneg _) fun j _ => ?_) ?_ (norm_nonneg _)
      (Finset.prod_nonneg fun j _ => abs_nonneg _)
    · rw [Complex.norm_real, Real.norm_eq_abs]
      exact (hM _ _ k).trans (le_abs_self _)
    · exact (hCJ J g hg).trans (mul_le_mul_of_nonneg_right (le_abs_self _) hw)
  have hF0c : ContinuousOn (F []) (UJset ε) := hf.congr fun g hg => hF0 g hg
  have hMs : ∀ l : List (Mx n), (∀ Y ∈ l, Y ∈ lieSet ε) → ∀ z ∈ UJset ε,
      AEStronglyMeasurable (fun k : ↥(KG ε) =>
        F (l.map fun X => (toMK k)⁻¹ * X * toMK k) (z * toMK k)) (muK ε) := by
    intro l hl z hz
    refine Measurable.aestronglyMeasurable ?_
    have e2 : (fun k : ↥(KG ε) => F (l.map fun X => (toMK k)⁻¹ * X * toMK k) (z * toMK k)) =
        fun k => ∑ J : Fin l.length → Fin (Module.finrank ℝ (GlobalTheory.LowTypeDetermined.lie (Jm ε))),
          (∏ j, (c (J j) ((toMK k)⁻¹ * l.get j * toMK k) : ℂ)) * F (List.ofFn fun j => b (J j)) (z * toMK k) := by
      funext k
      rw [e1, hD _ _ (fun j => had k _ (hl _ (List.get_mem l j))) _ (mul_mem_UJ hz (hK k))]
    rw [e2]
    refine Finset.measurable_sum _ fun J _ => Measurable.mul ?_ ?_
    · exact Finset.measurable_prod _ fun j _ =>
        Complex.measurable_ofReal.comp (hcc _ _ (hl _ (List.get_mem l j))).measurable
    · exact GlobalTheory.T.measurable_derFam_comp_continuous_of_mem_UJset n ε F hFd hF0c _ (hbw J) (↥(KG ε)) (fun k => z * toMK k)
        (continuous_const.matrix_mul (continuous_toMK ε)) fun k => mul_mem_UJ hz (hK k)
  obtain ⟨hA, hB⟩ := _root_.GlobalTheory.KAvgDeriv.avg_derFam_growth n ε N F hFd hUb hMs e he
  refine ⟨N, _, fun y hy => ?_, hA, hB⟩
  simp only [List.map_nil]
  refine integral_congr_ae (Eventually.of_forall fun k => ?_)
  simp only
  rw [hF0 _ (mul_mem_UJ hy (hK k))]

end GlobalTheory.KAvgGrowth
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.CompactUnitaryCasimirPowPairingModerateGrowthBou
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KFourier MeasureTheory

noncomputable section

namespace GlobalTheory.KFourier.CasimirMove

variable {n : ℕ}

theorem expK_add {ε : Fin n → Bool} {X : Mx n} (hX : inK ε X) (s t : ℝ) :
    expK ε X (s + t) = expK ε X s * expK ε X t := by
  have hEG := group_exponential_facts n ε X hX.1
  have hEK := hEG.2.2.2 hX
  apply Subtype.ext
  show ((expK ε X (s + t) : KG ε) : UJ ε) = (expK ε X s : UJ ε) * (expK ε X t : UJ ε)
  rw [hEK.1, hEK.1, hEK.1]
  exact hEG.2.1 s t

theorem expK_zero {ε : Fin n → Bool} {X : Mx n} (hX : inK ε X) : expK ε X 0 = 1 := by
  have hEG := group_exponential_facts n ε X hX.1
  have hEK := hEG.2.2.2 hX
  apply Subtype.ext
  show ((expK ε X 0 : KG ε) : UJ ε) = 1
  rw [hEK.1]; exact hEG.1

theorem integral_deriv_eq_zero {ε : Fin n → Bool} {X : Mx n} (hX : inK ε X) {G D : KG ε → ℂ}
    (hG : Measurable G) (hD : Measurable D) (hGi : Integrable G (muK ε)) {C : ℝ} (hC : ∀ k, ‖D k‖ ≤ C)
    (hder : ∀ k, HasDerivAt (fun t : ℝ => G (k * expK ε X t)) (D k) 0) : ∫ k, D k ∂(muK ε) = 0 := by
  have hder' : ∀ k s, HasDerivAt (fun t => G (k * expK ε X t)) (D (k * expK ε X s)) s := by
    intro k s
    have h1 := hder (k * expK ε X s)
    have h2 : HasDerivAt (fun t => G (k * expK ε X s * expK ε X (t - s))) (D (k * expK ε X s)) s :=
      HasDerivAt.comp_sub_const (f := fun t => G (k * expK ε X s * expK ε X t)) s s (by rw [sub_self]; exact h1)
    have hfun : (fun t => G (k * expK ε X s * expK ε X (t - s))) = fun t => G (k * expK ε X t) := by
      funext t
      rw [mul_assoc, ← expK_add hX, add_sub_cancel]
    rw [hfun] at h2
    exact h2
  have h := (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := muK ε) (𝕜 := ℝ)
    (F := fun t k => G (k * expK ε X t)) (F' := fun t k => D (k * expK ε X t)) (x₀ := 0) (bound := fun _ => C)
    (s := Set.univ) Filter.univ_mem
    (Filter.Eventually.of_forall fun t => (hG.comp (measurable_mul_const _)).aestronglyMeasurable)
    (by simpa only [expK_zero hX, mul_one] using hGi)
    (hD.comp (measurable_mul_const _)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun k t _ => hC _) (integrable_const C)
    (Filter.Eventually.of_forall fun k t _ => hder' k t)).2
  simp only [integral_mul_right_eq_self (μ := muK ε) G, expK_zero hX, mul_one] at h
  exact h.unique (hasDerivAt_const _ _)

theorem measurable_of_deriv {ε : Fin n → Bool} {X : Mx n} (hX : inK ε X) {G D : KG ε → ℂ}
    (hG : Measurable G) (hder : ∀ k, HasDerivAt (fun t : ℝ => G (k * expK ε X t)) (D k) 0) : Measurable D := by
  have hlim : Filter.Tendsto (fun m : ℕ => 1 / ((m : ℝ) + 1)) Filter.atTop (nhdsWithin 0 {0}ᶜ) := by
    refine tendsto_nhdsWithin_iff.2 ⟨tendsto_one_div_add_atTop_nhds_zero_nat, Filter.Eventually.of_forall fun m => ?_⟩
    have : (0 : ℝ) < 1 / ((m : ℝ) + 1) := Nat.one_div_pos_of_nat
    exact this.ne'
  refine measurable_of_tendsto_metrizable
    (f := fun (m : ℕ) k => slope (fun t : ℝ => G (k * expK ε X t)) 0 (1 / ((m : ℝ) + 1))) (fun m => ?_) ?_
  · simp only [slope_def_module, expK_zero hX, mul_one]
    exact ((hG.comp (measurable_mul_const _)).sub hG).const_smul _
  · exact tendsto_pi_nhds.2 fun k => (hasDerivAt_iff_tendsto_slope.1 (hder k)).comp hlim

theorem hasDerivAt_fam {ε : Fin n → Bool} {F : List (Mx n) → Mx n → ℂ} (hF : IsDerFam ε F) {w : List (Mx n)}
    (hw : ∀ Y ∈ w, inK ε Y) {X : Mx n} (hX : inK ε X) {y : Mx n} (hy : y ∈ UJset ε) (k : KG ε) :
    HasDerivAt (fun t : ℝ => F w (y * toMK (k * expK ε X t))) (F (X :: w) (y * toMK k)) 0 := by
  have h := hF w (fun Y hY => (hw Y hY).1) X hX.1 (y * toMK k) (mul_mem_UJ hy (K_le_UJ (toMK_mem_K k)))
  simpa only [toMK_mul, toMK_expK hX, Complex.coe_smul, Matrix.mul_assoc] using h

theorem measurable_fam {ε : Fin n → Bool} {F : List (Mx n) → Mx n → ℂ} (hF : IsDerFam ε F)
    (hc : ContinuousOn (F []) (UJset ε)) {y : Mx n} (hy : y ∈ UJset ε) {w : List (Mx n)} (hw : ∀ Y ∈ w, inK ε Y) :
    Measurable fun k : KG ε => F w (y * toMK k) := by
  induction w with
  | nil =>
    exact (hc.comp_continuous (continuous_const.mul (continuous_toMK ε))
      fun k => mul_mem_UJ hy (K_le_UJ (toMK_mem_K k))).measurable
  | cons X w ih =>
    have hw' := fun Y hY => hw Y (List.mem_cons_of_mem _ hY)
    have hX := hw X List.mem_cons_self
    exact measurable_of_deriv hX (ih hw') (hasDerivAt_fam hF hw' hX hy)

theorem bound_fam {ε : Fin n → Bool} {N : ℕ} {F : List (Mx n) → Mx n → ℂ} (hg : FamGrowth ε N F)
    {w : List (Mx n)} (hw : ∀ Y ∈ w, inK ε Y) :
    ∃ C : ℝ, ∀ y ∈ UJset ε, ∀ k : KG ε, ‖F w (y * toMK k)‖ ≤ C * (1 + hs y) ^ N := by
  obtain ⟨C, hC⟩ := hg w fun Y hY => (hw Y hY).1
  refine ⟨C, fun y hy k => ?_⟩
  have h := hC _ (mul_mem_UJ hy (K_le_UJ (toMK_mem_K k)))
  rwa [((hermitian_small_ball n ε).2 _ _ (toMK_mem_K k)).1] at h

theorem integrable_mul_fam {ε : Fin n → Bool} {N : ℕ} {F : List (Mx n) → Mx n → ℂ} (hF : IsDerFam ε F)
    (hg : FamGrowth ε N F) (hc : ContinuousOn (F []) (UJset ε)) {y : Mx n} (hy : y ∈ UJset ε) {w : List (Mx n)}
    (hw : ∀ Y ∈ w, inK ε Y) {p : KG ε → ℂ} (hp : Continuous p) :
    Integrable (fun k => p k * F w (y * toMK k)) (muK ε) := by
  obtain ⟨C, hC⟩ := bound_fam hg hw
  exact (integrable_of_continuousK hp).mul_bdd (measurable_fam hF hc hy hw).aestronglyMeasurable
    (Filter.Eventually.of_forall (hC y hy))

theorem by_parts {ε : Fin n → Bool} {N : ℕ} {F : List (Mx n) → Mx n → ℂ} (hF : IsDerFam ε F)
    (hg : FamGrowth ε N F) (hc : ContinuousOn (F []) (UJset ε)) {y : Mx n} (hy : y ∈ UJset ε) {w : List (Mx n)}
    (hw : ∀ Y ∈ w, inK ε Y) {X : Mx n} (hX : inK ε X) {d : ℕ} {p : KG ε → ℂ} (hp : p ∈ polyV ε d) :
    ∫ k, rder ε [X] p k * F w (y * toMK k) ∂(muK ε) = -∫ k, p k * F (X :: w) (y * toMK k) ∂(muK ε) := by
  have hw' : ∀ Y ∈ X :: w, inK ε Y := fun Y hY => (List.mem_cons.1 hY).elim (fun e => e ▸ hX) (hw Y)
  obtain ⟨hq, hd⟩ := rder_mem_and_hasDerivAt ε d p hp X hX
  have cp := continuous_of_mem hp
  have cq := continuous_of_mem hq
  obtain ⟨C₁, h₁⟩ := bound_fam hg hw
  obtain ⟨C₂, h₂⟩ := bound_fam hg hw'
  obtain ⟨B₁, b₁⟩ := isCompact_univ.exists_bound_of_continuousOn cq.continuousOn
  obtain ⟨B₂, b₂⟩ := isCompact_univ.exists_bound_of_continuousOn cp.continuousOn
  have key := integral_deriv_eq_zero hX (G := fun k => p k * F w (y * toMK k))
    (D := fun k => rder ε [X] p k * F w (y * toMK k) + p k * F (X :: w) (y * toMK k))
    (cp.measurable.mul (measurable_fam hF hc hy hw))
    ((cq.measurable.mul (measurable_fam hF hc hy hw)).add (cp.measurable.mul (measurable_fam hF hc hy hw')))
    (integrable_mul_fam hF hg hc hy hw cp) (C := B₁ * (C₁ * (1 + hs y) ^ N) + B₂ * (C₂ * (1 + hs y) ^ N))
    (fun k => (norm_add_le _ _).trans (add_le_add
      (norm_mul_le_of_le (b₁ k trivial) (h₁ y hy k)) (norm_mul_le_of_le (b₂ k trivial) (h₂ y hy k))))
    (fun k => by
      have h := (hd k).fun_mul (hasDerivAt_fam hF hw hX hy k)
      simpa only [expK_zero hX, mul_one] using h)
  rw [integral_add (integrable_mul_fam hF hg hc hy hw cq) (integrable_mul_fam hF hg hc hy hw' cp)] at key
  exact eq_neg_of_add_eq_zero_left key

theorem integral_norm_le_sqrt {ε : Fin n → Bool} {p : KG ε → ℂ} (hp : Continuous p) :
    ∫ k, ‖p k‖ ∂(muK ε) ≤ Real.sqrt (∫ k, ‖p k‖ ^ 2 ∂(muK ε)) := by
  have i1 : Integrable (fun k => ‖p k‖) (muK ε) := (integrable_of_continuousK hp).norm
  have i2 : Integrable (fun k => ‖p k‖ ^ 2) (muK ε) :=
    (hp.norm.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  set a := ∫ k, ‖p k‖ ∂(muK ε) with ha
  have h0 : 0 ≤ ∫ k, (‖p k‖ ^ 2 - 2 * a * ‖p k‖ + a ^ 2) ∂(muK ε) :=
    integral_nonneg fun k => by
      have := sq_nonneg (‖p k‖ - a)
      simp only [Pi.zero_apply]
      nlinarith
  rw [integral_add (f := fun k => ‖p k‖ ^ 2 - 2 * a * ‖p k‖) (i2.sub (i1.const_mul _)) (integrable_const _), integral_sub i2 (i1.const_mul _),
    integral_const_mul, integral_const, ← ha] at h0
  simp only [probReal_univ, smul_eq_mul, one_mul] at h0
  exact Real.le_sqrt_of_sq_le (by nlinarith)

theorem casimir_mem {ε : Fin n → Bool} {r : ℕ} {X : Fin r → Mx n} (hX : ∀ j, inK ε (X j)) {d : ℕ}
    {p : KG ε → ℂ} (hp : p ∈ polyV ε d) : (∑ j, rder ε [X j, X j] p) ∈ polyV ε d :=
  Submodule.sum_mem _ fun j _ =>
    (rder_mem_and_hasDerivAt ε d _ (rder_mem_and_hasDerivAt ε d p hp _ (hX j)).1 _ (hX j)).1

theorem casimir_pow_bound : ∀ {n : ℕ} (ε : Fin n → Bool) (N : ℕ) (F : List (Mx n) → Mx n → ℂ), IsDerFam ε F → FamGrowth ε N F → ContinuousOn (F []) (UJset ε) → ∀ {r : ℕ} (X : Fin r → Mx n), (∀ j, inK ε (X j)) → ∀ (M : ℕ) (u : List (Mx n)), (∀ Y ∈ u, inK ε Y) → ∃ C : ℝ, ∀ (d : ℕ) (p : KG ε → ℂ), p ∈ polyV ε d → ∀ y ∈ UJset ε, ‖∫ k, ((fun φ : KG ε → ℂ => ∑ j, rder ε [X j, X j] φ)^[M] p) k * F u (y * toMK k) ∂(muK ε)‖ ≤ C * (1 + hs y) ^ N * Real.sqrt (∫ k, ‖p k‖ ^ 2 ∂(muK ε)) := by
  intro n ε N F hF hg hc r X hX M
  induction M with
  | zero =>
    intro u hu
    obtain ⟨C, hC⟩ := bound_fam hg hu
    refine ⟨C, fun d p hp y hy => ?_⟩
    have cp := continuous_of_mem hp
    have h0 : 0 ≤ C * (1 + hs y) ^ N := (norm_nonneg _).trans (hC y hy 1)
    calc _ ≤ ∫ k, C * (1 + hs y) ^ N * ‖p k‖ ∂(muK ε) :=
          norm_integral_le_of_norm_le ((integrable_of_continuousK cp).norm.const_mul _)
            (Filter.Eventually.of_forall fun k => by
              rw [mul_comm (C * _)]
              exact norm_mul_le_of_le le_rfl (hC y hy k))
      _ ≤ _ := by
          rw [integral_const_mul]
          exact mul_le_mul_of_nonneg_left (integral_norm_le_sqrt cp) h0
  | succ M ih =>
    intro u hu
    have h1 : ∀ j, ∀ Y ∈ X j :: u, inK ε Y := fun j Y hY => (List.mem_cons.1 hY).elim (fun e => e ▸ hX j) (hu Y)
    have h2 : ∀ j, ∀ Y ∈ X j :: X j :: u, inK ε Y := fun j Y hY =>
      (List.mem_cons.1 hY).elim (fun e => e ▸ hX j) (h1 j Y)
    choose C hC using fun j => ih _ (h2 j)
    refine ⟨∑ j, C j, fun d p hp y hy => ?_⟩
    have hq : (fun φ : KG ε → ℂ => ∑ j, rder ε [X j, X j] φ)^[M] p ∈ polyV ε d :=
      Function.Iterate.rec (fun φ => φ ∈ polyV ε d) hp (fun _ h => casimir_mem hX h) M
    rw [Function.iterate_succ_apply']
    set q := (fun φ : KG ε → ℂ => ∑ j, rder ε [X j, X j] φ)^[M] p with hqd
    have hr : ∀ j, rder ε [X j] q ∈ polyV ε d := fun j => (rder_mem_and_hasDerivAt ε d q hq _ (hX j)).1
    have hrr : ∀ j, rder ε [X j, X j] q ∈ polyV ε d := fun j => (rder_mem_and_hasDerivAt ε d _ (hr j) _ (hX j)).1
    have e : ∀ j, ∫ k, rder ε [X j, X j] q k * F u (y * toMK k) ∂(muK ε) =
        ∫ k, q k * F (X j :: X j :: u) (y * toMK k) ∂(muK ε) := fun j => by
      have a := by_parts hF hg hc hy hu (hX j) (hr j)
      rw [by_parts hF hg hc hy (h1 j) (hX j) hq, neg_neg] at a
      exact a
    simp only [Finset.sum_apply, Finset.sum_mul]
    rw [integral_finsetSum _ fun j _ => integrable_mul_fam hF hg hc hy hu (continuous_of_mem (hrr j))]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [e j]
    exact hC j d p hp y hy

end GlobalTheory.KFourier.CasimirMove

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.CompactUnitaryIntegralConjInvariantStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_compactUnitary_fourierKernel : ∀ {n : ℕ} (ε : Fin n → Bool) (i : ℕ), ∃ e, GlobalTheory.KFourier.IsKer ε i e := by
  first | exact @GlobalTheory.KFourier.exists_isKer | exact GlobalTheory.KFourier.exists_isKer | (intros; apply GlobalTheory.KFourier.exists_isKer <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.CompactUnitaryRightDerivConjInvariantAverageEqStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compactUnitaryRightDeriv_conjInvariantAverage_eq : ∀ {n : ℕ} (ε : Fin n → Bool) (N : ℕ) (F : List (Mx n) → Mx n → ℂ), IsDerFam ε F → FamGrowth ε N F → ∀ f : Mx n → ℂ, ContinuousOn f (UJset ε) → (∀ g ∈ UJset ε, F [] g = f g) → ∀ e : KG ε → ℂ, Continuous e → (∀ a k : KG ε, e (a * k * a⁻¹) = e k) → ∀ u : List (Mx n), (∀ X ∈ u, inK ε X) → ∀ y ∈ UJset ε, GlobalTheory.KFourier.rder ε u (GlobalTheory.KFourier.avgK ε e f y) 1 = ∫ k, e k * F u (y * toMK k) ∂(muK ε) := by
  first | exact @GlobalTheory.KAvgDeriv.rder_avgK_one | exact GlobalTheory.KAvgDeriv.rder_avgK_one | (intros; apply GlobalTheory.KAvgDeriv.rder_avgK_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.ContDiffMatrixRightInvariantDerivativeStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.contDiff_matrixRightInvariantDerivative : ∀ {n : ℕ} (ε : Fin n → Bool) (d : ℕ) (φ : KG ε → ℂ), φ ∈ GlobalTheory.KFourier.polyV ε d → ∀ X : Mx n, inK ε X → GlobalTheory.KFourier.rder ε [X] φ ∈ GlobalTheory.KFourier.polyV ε d ∧ ∀ k : KG ε, HasDerivAt (fun t : ℝ => φ (k * expK ε X t)) (GlobalTheory.KFourier.rder ε [X] φ k) 0 := by
  first | exact @GlobalTheory.KFourier.rder_mem_and_hasDerivAt | exact GlobalTheory.KFourier.rder_mem_and_hasDerivAt | (intros; apply GlobalTheory.KFourier.rder_mem_and_hasDerivAt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsOrthogonalProjectionPolynomialCompactUnita
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open MeasureTheory GlobalTheory.KFourier

noncomputable section

namespace GlobalTheory.KFourier

open MeasureTheory

theorem exists_orthProj_polyV {n : ℕ} (ε : Fin n → Bool) (d : ℕ) (p : KG ε → ℂ) (hp : Continuous p) :
    ∃ p' ∈ GlobalTheory.KFourier.polyV ε d, ∀ q ∈ GlobalTheory.KFourier.polyV ε d,
      ∫ k, star (q k) * (p k - p' k) ∂(muK ε) = 0 := by
  first
  | exact @_root_.GlobalTheory.OrthogonalProjectionPoly.exists_proj_polyV
  | exact _root_.GlobalTheory.OrthogonalProjectionPoly.exists_proj_polyV
  | (apply _root_.GlobalTheory.OrthogonalProjectionPoly.exists_proj_polyV <;> assumption)
  | (intros; apply _root_.GlobalTheory.OrthogonalProjectionPoly.exists_proj_polyV <;> assumption)
  | (intros; apply @_root_.GlobalTheory.OrthogonalProjectionPoly.exists_proj_polyV <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.OrthogonalProjectionPoly.exists_proj_polyV ..)

end GlobalTheory.KFourier

end
end

