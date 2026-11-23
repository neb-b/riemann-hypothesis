module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0002
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0165
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0121
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemSmoothFunctionsOfClosedRightDerivatives
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0165
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0161
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0220
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsAutFunSmStar
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.L2UnitaryRepresentationData
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0194
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0198
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0198

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TendstoModerateGrowthSizeDifferenceQuotient
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Grow GlobalTheory.Size GlobalTheory.Mem.AutSpace Filter
open scoped ENNReal NNReal Topology

namespace GlobalTheory.Size.DiffQuot

theorem norm_taylor_le {f f₁ f₂ : ℝ → ℂ} (d1 : ∀ s, HasDerivAt f (f₁ s) s) (d2 : ∀ s, HasDerivAt f₁ (f₂ s) s)
    {B t : ℝ} (hB0 : 0 ≤ B) (hB : ∀ s ∈ Set.Icc (-|t|) |t|, ‖f₂ s‖ ≤ B) :
    ‖f t - f 0 - (t : ℂ) * f₁ 0‖ ≤ B * |t| * |t| := by
  have hI : Convex ℝ (Set.Icc (-|t|) |t|) := convex_Icc _ _
  have h0 : (0 : ℝ) ∈ Set.Icc (-|t|) |t| := ⟨neg_nonpos.mpr (abs_nonneg t), abs_nonneg t⟩
  have ht : t ∈ Set.Icc (-|t|) |t| := ⟨neg_abs_le t, le_abs_self t⟩

  have h1 : ∀ s ∈ Set.Icc (-|t|) |t|, ‖f₁ s - f₁ 0‖ ≤ B * |t| := by
    intro s hs
    have hmv := hI.norm_image_sub_le_of_norm_hasDerivWithin_le (f := f₁) (f' := f₂)
      (fun x _ => (d2 x).hasDerivWithinAt) hB h0 hs
    refine hmv.trans ?_
    rw [sub_zero, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (abs_le.2 ⟨hs.1, hs.2⟩) hB0

  have hg : ∀ s ∈ Set.Icc (-|t|) |t|, HasDerivWithinAt (fun u : ℝ => f u - (u : ℂ) * f₁ 0) (f₁ s - f₁ 0)
      (Set.Icc (-|t|) |t|) s := by
    intro s _
    have hc : HasDerivAt (fun u : ℝ => (u : ℂ) * f₁ 0) (f₁ 0) s := by
      simpa using ((hasDerivAt_id s).ofReal_comp).mul_const (f₁ 0)
    exact ((d1 s).sub hc).hasDerivWithinAt
  have hmv := hI.norm_image_sub_le_of_norm_hasDerivWithin_le hg h1 h0 ht
  have e : f t - f 0 - (t : ℂ) * f₁ 0 = (f t - (t : ℂ) * f₁ 0) - (f 0 - ((0 : ℝ) : ℂ) * f₁ 0) := by
    push_cast; ring
  rw [e]
  refine hmv.trans (le_of_eq ?_)
  rw [sub_zero, Real.norm_eq_abs]

theorem tendsto_growthSize_diffQuot : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (τ : D.what₂.Tau) (N : ℕ), ∀ X ∈ lieAt V τ, ∀ φ ∈ GlobalTheory.Mem.AutSpace.SmFun θ V, GlobalTheory.Size.growthSob θ V 2 N φ ≠ ⊤ → Filter.Tendsto (fun t : ℝ => GlobalTheory.Size.growthSize V N (((t : ℂ)⁻¹) • (rTr V (oneP θ V τ X t) φ - φ) - Rder θ V τ X φ)) (nhdsWithin 0 {0}ᶜ) (nhds 0) := by
  intro D θ hθ V τ N X hX φ hφ hS
  have hφ1 : Rder θ V τ X φ ∈ SmFun θ V := Rder_mem hφ hX

  have hw : growthSize V N (Rder θ V τ X (Rder θ V τ X φ)) ≠ ⊤ := by
    have hl : IsLieWord V [(τ, X), (τ, X)] := by
      intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl <;> exact hX
    have h2 := growthSize_rWord_ne_top_of_le hθ hφ hS hl (by simp)
    simpa only [rWord, wordAct_cons, wordAct_nil] using h2
  obtain ⟨C, hC⟩ := modGrowthExp_iff.2 hw
  have hC0 : 0 ≤ C := nonneg_of_growth hC

  obtain ⟨K, hK⟩ := exists_height_le_of_isCompact V
    (isCompact_Icc.image (GlobalTheory.Mem.Lift.continuous_oneP hθ hX) :
      IsCompact (oneP θ V τ X '' Set.Icc (-1 : ℝ) 1))
  have hK1 : 1 ≤ K := (one_le_height V _).trans (hK _ ⟨0, ⟨by norm_num, by norm_num⟩, rfl⟩)
  have hK0 : 0 ≤ K := by linarith

  have key : ∀ t : ℝ, |t| ≤ 1 → t ≠ 0 → ∀ g,
      ‖(((t : ℂ)⁻¹) • (rTr V (oneP θ V τ X t) φ - φ) - Rder θ V τ X φ) g‖ ≤
        C * K ^ N * |t| * height V g ^ N := by
    intro t ht1 ht0 g
    have d1 : ∀ s, HasDerivAt (fun s => φ (g * oneP θ V τ X s)) (Rder θ V τ X φ (g * oneP θ V τ X s)) s :=
      fun s => GlobalTheory.Mem.Lift.hasDerivAt_oneP hθ hX (fun g' => GlobalTheory.Mem.Lift.hasDerivAt_Rder hφ hX g') g s
    have d2 : ∀ s, HasDerivAt (fun s => Rder θ V τ X φ (g * oneP θ V τ X s))
        (Rder θ V τ X (Rder θ V τ X φ) (g * oneP θ V τ X s)) s :=
      fun s => GlobalTheory.Mem.Lift.hasDerivAt_oneP hθ hX (fun g' => GlobalTheory.Mem.Lift.hasDerivAt_Rder hφ1 hX g') g s
    have hg0 : 0 ≤ height V g := (height_pos V g).le
    have hB0 : 0 ≤ C * (height V g * K) ^ N := mul_nonneg hC0 (pow_nonneg (mul_nonneg hg0 hK0) N)
    have hB : ∀ s ∈ Set.Icc (-|t|) |t|,
        ‖Rder θ V τ X (Rder θ V τ X φ) (g * oneP θ V τ X s)‖ ≤ C * (height V g * K) ^ N := by
      intro s hs
      have hs1 : s ∈ Set.Icc (-1 : ℝ) 1 := ⟨by linarith [hs.1], by linarith [hs.2]⟩
      refine (hC _).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (height_pos V _).le ?_ N) hC0)
      exact (height_mul_le V _ _).trans (mul_le_mul_of_nonneg_left (hK _ ⟨s, hs1, rfl⟩) hg0)
    have hT := norm_taylor_le d1 d2 hB0 hB
    have e0 : oneP θ V τ X 0 = 1 := GlobalTheory.Mem.Lift.oneP_zero (V := V) (τ := τ) (X := X) hθ
    have htc : (t : ℂ) ≠ 0 := by exact_mod_cast ht0
    have hval : (((t : ℂ)⁻¹) • (rTr V (oneP θ V τ X t) φ - φ) - Rder θ V τ X φ) g =
        (t : ℂ)⁻¹ * (φ (g * oneP θ V τ X t) - φ (g * oneP θ V τ X 0) -
          (t : ℂ) * Rder θ V τ X φ (g * oneP θ V τ X 0)) := by
      simp only [e0, mul_one, rTr, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      field_simp
    have hta : 0 < |t| := abs_pos.mpr ht0
    rw [hval, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs]
    calc |t|⁻¹ * ‖φ (g * oneP θ V τ X t) - φ (g * oneP θ V τ X 0) -
          (t : ℂ) * Rder θ V τ X φ (g * oneP θ V τ X 0)‖
        ≤ |t|⁻¹ * (C * (height V g * K) ^ N * |t| * |t|) :=
          mul_le_mul_of_nonneg_left hT (inv_nonneg.mpr hta.le)
      _ = C * K ^ N * |t| * height V g ^ N := by
          field_simp
          ring

  have hev : ∀ᶠ t : ℝ in nhdsWithin (0 : ℝ) {0}ᶜ, |t| ≤ 1 ∧ t ∈ ({0}ᶜ : Set ℝ) := by
    refine (eventually_nhdsWithin_of_eventually_nhds ?_).and eventually_mem_nhdsWithin
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) one_pos] with t ht
    rw [Metric.mem_ball, Real.dist_eq, sub_zero] at ht
    exact ht.le
  have hle : ∀ᶠ t : ℝ in nhdsWithin (0 : ℝ) {0}ᶜ,
      GlobalTheory.Size.growthSize V N (((t : ℂ)⁻¹) • (rTr V (oneP θ V τ X t) φ - φ) - Rder θ V τ X φ) ≤
        ENNReal.ofReal (C * K ^ N * |t|) := by
    filter_upwards [hev] with t ht
    have ht0 : t ≠ 0 := by simpa using ht.2
    exact (growthSize_le_iff (mul_nonneg (mul_nonneg hC0 (pow_nonneg hK0 N)) (abs_nonneg t))).2
      (key t ht.1 ht0)
  have hlim : Filter.Tendsto (fun t : ℝ => ENNReal.ofReal (C * K ^ N * |t|)) (nhdsWithin 0 {0}ᶜ) (nhds 0) := by
    have h0 : Filter.Tendsto (fun t : ℝ => C * K ^ N * |t|) (nhds 0) (nhds 0) := by
      simpa using (continuous_abs.tendsto (0 : ℝ)).const_mul (C * K ^ N)
    simpa using (ENNReal.tendsto_ofReal h0).mono_left nhdsWithin_le_nhds
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Filter.Eventually.of_forall fun _ => zero_le) hle

end GlobalTheory.Size.DiffQuot

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TendstoModerateGrowthSizeTranslateNearOne
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Grow GlobalTheory.Size GlobalTheory.Mem.AutSpace Filter
open scoped ENNReal NNReal Topology

namespace GlobalTheory.Size.NearOne

variable {D : D7} {θ : InfFam D} {V : HSp D}

theorem exists_log (V : HSp D) (τ : D.what₂.Tau) :
    ∃ Λ : Matrix (Fin V.rank) (Fin V.rank) ℂ → Matrix (Fin V.rank) (Fin V.rank) ℂ, (∀ u, Λ u ∈ lieAt V τ) ∧
      Tendsto Λ (𝓝 1) (𝓝 0) ∧
      ∀ᶠ u in 𝓝[Formalism.QuantumDeterminants.UH (gramAt D V τ)] 1, NormedSpace.exp (Λ u) = u := by
  obtain ⟨L, hL, hexp, hlog⟩ := GlobalTheory.ConjMult.hasLogAt (V := V) τ
  have hJ := GlobalTheory.SmoothAutCheck.gramAt_unit V τ
  have h0 : L 1 = 0 := by
    have h := hlog.self_of_nhds
    simpa using h
  refine ⟨fun u => (L u).1, fun u => (L u).2, ?_, ?_⟩
  · have hc : Filter.Tendsto L (𝓝 1) (𝓝 0) := h0 ▸ hL.continuousAt.tendsto
    exact (continuous_subtype_val.tendsto _).comp hc
  · filter_upwards [nhdsWithin_le_nhds hexp, self_mem_nhdsWithin] with u hu hmem
    exact hu ((GlobalTheory.ConjMult.unit_iffM hJ u).2 hmem)

private theorem continuous_matrix_exp' (n : ℕ) : Continuous (fun M : Matrix (Fin n) (Fin n) ℂ => NormedSpace.exp M) := by
  let _ : NormedRing (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedRing
  let _ : NormedAlgebra ℂ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedAlgebra
  let _ : NormedAlgebra ℚ (Matrix (Fin n) (Fin n) ℂ) := .restrictScalars ℚ ℂ _
  have _ : CompleteSpace (Matrix (Fin n) (Fin n) ℂ) := FiniteDimensional.complete ℂ _
  exact NormedSpace.exp_continuous


attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in
theorem exists_height_le (hθ : IsInfFam θ) (V : HSp D) (τ : D.what₂.Tau) :
    ∀ᶠ X in 𝓝 (0 : Matrix (Fin V.rank) (Fin V.rank) ℂ), X ∈ lieAt V τ →
      ∀ t ∈ Set.Icc (0 : ℝ) 1, height V (oneP θ V τ X t) ≤ 2 := by
  have hl := height_laws (V := V)
  have hexp : Continuous (fun M : Matrix (Fin V.rank) (Fin V.rank) ℂ => NormedSpace.exp M) := continuous_matrix_exp' V.rank
  let F : {X : Matrix (Fin V.rank) (Fin V.rank) ℂ // X ∈ lieAt V τ} × ℝ → ℝ :=
    fun p => height V (atTau θ V τ (NormedSpace.exp (p.2 • p.1.1)))
  have hF : Continuous F := by
    have hin : Continuous fun p : {X : Matrix (Fin V.rank) (Fin V.rank) ℂ // X ∈ lieAt V τ} × ℝ =>
        NormedSpace.exp (p.2 • p.1.1) :=
      hexp.comp (continuous_snd.smul (continuous_subtype_val.comp continuous_fst))
    exact hl.2.2.2.2.comp ((GlobalTheory.PointAtPlaceHom.continuousOn_atTau hθ V τ).comp_continuous hin
      fun p => GlobalTheory.Mem.Lift.exp_mem p.1.2 p.2)
  have h0mem : (0 : Matrix (Fin V.rank) (Fin V.rank) ℂ) ∈ lieAt V τ := by
    show (0 : Matrix (Fin V.rank) (Fin V.rank) ℂ)ᴴ * gramAt D V τ + gramAt D V τ * 0 = 0
    simp
  have hF0 : ∀ t : ℝ, F (⟨0, h0mem⟩, t) = 1 := by
    intro t
    show height V (atTau θ V τ (NormedSpace.exp (t • (0 : Matrix (Fin V.rank) (Fin V.rank) ℂ)))) = 1
    rw [smul_zero, NormedSpace.exp_zero, (GlobalTheory.PointAtPlaceHom.atTau_laws D θ hθ V τ).2.1, hl.2.1]
  have hev : ∀ᶠ x in 𝓝 (⟨0, h0mem⟩ : {X : Matrix (Fin V.rank) (Fin V.rank) ℂ // X ∈ lieAt V τ}),
      ∀ t ∈ Set.Icc (0 : ℝ) 1, F (x, t) ≤ 2 := by
    refine isCompact_Icc.eventually_forall_of_forall_eventually fun t _ => ?_
    have hlt : F (⟨0, h0mem⟩, t) < 2 := by rw [hF0]; norm_num
    exact (hF.continuousAt.eventually (gt_mem_nhds hlt)).mono fun z hz => hz.le
  rw [nhds_subtype, Filter.eventually_comap] at hev
  filter_upwards [hev] with X hX hXl t ht
  exact hX ⟨X, hXl⟩ rfl t ht

theorem growthSize_sub_le (hθ : IsInfFam θ) {τ : D.what₂.Tau} {N : ℕ} {φ : GA D V → ℂ} (hs : φ ∈ SmFun θ V)
    (hf : growthSob θ V 1 N φ ≠ ⊤) {X : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hX : X ∈ lieAt V τ)
    (hh : ∀ t ∈ Set.Icc (0 : ℝ) 1, height V (oneP θ V τ X t) ≤ 2) :
    growthSize V N (rTr V (oneP θ V τ X 1) φ - φ) ≤
      ENNReal.ofReal ((∑ a : Fin V.rank × Fin V.rank, ‖X a.1 a.2‖) * (growthSob θ V 1 N φ).toReal * 2 ^ N) := by
  set S := (growthSob θ V 1 N φ).toReal with hS
  have hS0 : 0 ≤ S := ENNReal.toReal_nonneg
  set s := ∑ a : Fin V.rank × Fin V.rank, ‖X a.1 a.2‖ with hs_def
  have hs0 : 0 ≤ s := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hglob : ∀ a : Fin V.rank × Fin V.rank, ∀ h, ‖glDer θ V (τ, a) φ h‖ ≤ S * height V h ^ N := by
    intro a
    have h1 : growthSize V N (glDer θ V (τ, a) φ) ≤ growthSob θ V 1 N φ := by
      have h0 := le_wordSum (A := glDer θ V) (p := growthSize V N) (d := 1) (l := [(τ, a)]) (by simp) φ
      simpa [wordAct, growthSob] using h0
    have h2 : growthSize V N (glDer θ V (τ, a) φ) ≤ ENNReal.ofReal S := by
      rw [hS, ENNReal.ofReal_toReal hf]
      exact h1
    exact (growthSize_le_iff hS0).1 h2
  have hder : ∀ h, ‖Rder θ V τ X φ h‖ ≤ s * S * height V h ^ N := by
    intro h
    rw [Rder_eq_sum_glDer hθ hs hX, Finset.sum_apply]
    calc ‖∑ a : Fin V.rank × Fin V.rank, (X a.1 a.2 • glDer θ V (τ, a) φ) h‖
        ≤ ∑ a : Fin V.rank × Fin V.rank, ‖(X a.1 a.2 • glDer θ V (τ, a) φ) h‖ := norm_sum_le _ _
      _ ≤ ∑ a : Fin V.rank × Fin V.rank, ‖X a.1 a.2‖ * (S * height V h ^ N) := by
          refine Finset.sum_le_sum fun a _ => ?_
          rw [Pi.smul_apply, norm_smul]
          exact mul_le_mul_of_nonneg_left (hglob a h) (norm_nonneg _)
      _ = s * S * height V h ^ N := by rw [← Finset.sum_mul, mul_assoc]
  have hC : 0 ≤ s * S * 2 ^ N := by positivity
  rw [growthSize_le_iff hC]
  intro g
  have hl := height_laws (V := V)
  have hφd : ∀ t, HasDerivAt (fun r : ℝ => φ (g * oneP θ V τ X r)) (Rder θ V τ X φ (g * oneP θ V τ X t)) t :=
    fun t => GlobalTheory.Mem.Lift.hasDerivAt_oneP hθ hX (fun g' => GlobalTheory.Mem.Lift.hasDerivAt_Rder hs hX g') g t
  have hb : ∀ t ∈ Set.Ico (0 : ℝ) 1, ‖Rder θ V τ X φ (g * oneP θ V τ X t)‖ ≤ s * S * 2 ^ N * height V g ^ N := by
    intro t ht
    have hk : height V (oneP θ V τ X t) ≤ 2 := hh t (Set.Ico_subset_Icc_self ht)
    have hgk : height V (g * oneP θ V τ X t) ≤ height V g * 2 :=
      (hl.2.2.2.1 g _).trans (mul_le_mul_of_nonneg_left hk (zero_le_one.trans (hl.1 g)))
    have hpow : height V (g * oneP θ V τ X t) ^ N ≤ (height V g * 2) ^ N :=
      pow_le_pow_left₀ (zero_le_one.trans (hl.1 _)) hgk N
    calc ‖Rder θ V τ X φ (g * oneP θ V τ X t)‖ ≤ s * S * height V (g * oneP θ V τ X t) ^ N := hder _
      _ ≤ s * S * (height V g * 2) ^ N := mul_le_mul_of_nonneg_left hpow (mul_nonneg hs0 hS0)
      _ = s * S * 2 ^ N * height V g ^ N := by rw [mul_pow]; ring
  have key := norm_image_sub_le_of_norm_deriv_le_segment' (f := fun r : ℝ => φ (g * oneP θ V τ X r))
    (a := 0) (b := 1) (fun t _ => (hφd t).hasDerivWithinAt) hb 1 (by simp)
  simp only [sub_zero, mul_one] at key
  rw [GlobalTheory.Mem.Lift.oneP_zero hθ, mul_one] at key
  exact key

theorem tendsto_growthSize_translate : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (τ : D.what₂.Tau) (N : ℕ), ∀ φ ∈ GlobalTheory.Mem.AutSpace.SmFun θ V, GlobalTheory.Size.growthSob θ V 1 N φ ≠ ⊤ → Filter.Tendsto (fun u : Matrix (Fin V.rank) (Fin V.rank) ℂ => GlobalTheory.Size.growthSize V N (rTr V (atTau θ V τ u) φ - φ)) (nhdsWithin 1 (Formalism.QuantumDeterminants.UH (gramAt D V τ))) (nhds 0) := by
  intro D θ hθ V τ N φ hs hf
  obtain ⟨Λ, hΛmem, hΛ0, hΛexp⟩ := exists_log V τ
  have hH := exists_height_le hθ V τ
  have h1 : Filter.Tendsto Λ (nhdsWithin 1 (Formalism.QuantumDeterminants.UH (gramAt D V τ))) (𝓝 0) := hΛ0.mono_left nhdsWithin_le_nhds
  have h2 : Filter.Tendsto (fun u => ∑ a : Fin V.rank × Fin V.rank, ‖Λ u a.1 a.2‖)
      (nhdsWithin 1 (Formalism.QuantumDeterminants.UH (gramAt D V τ))) (𝓝 0) := by
    have h3 : ∀ a : Fin V.rank × Fin V.rank, Filter.Tendsto (fun u => ‖Λ u a.1 a.2‖)
        (nhdsWithin 1 (Formalism.QuantumDeterminants.UH (gramAt D V τ))) (𝓝 0) := by
      intro a
      have hce : Continuous fun M : Matrix (Fin V.rank) (Fin V.rank) ℂ => M a.1 a.2 := by
        fun_prop
      have h5 : Filter.Tendsto (fun u => Λ u a.1 a.2) (nhdsWithin 1 (Formalism.QuantumDeterminants.UH (gramAt D V τ)))
          (𝓝 ((0 : Matrix (Fin V.rank) (Fin V.rank) ℂ) a.1 a.2)) :=
        (hce.tendsto _).comp h1
      simpa using h5.norm
    have h4 := tendsto_finsetSum (Finset.univ : Finset (Fin V.rank × Fin V.rank)) fun a _ => h3 a
    simpa using h4
  have hc : Filter.Tendsto (fun u => ENNReal.ofReal ((∑ a : Fin V.rank × Fin V.rank, ‖Λ u a.1 a.2‖) *
      (growthSob θ V 1 N φ).toReal * 2 ^ N)) (nhdsWithin 1 (Formalism.QuantumDeterminants.UH (gramAt D V τ))) (𝓝 0) := by
    have h4 := ENNReal.tendsto_ofReal ((h2.mul_const ((growthSob θ V 1 N φ).toReal)).mul_const ((2 : ℝ) ^ N))
    simpa using h4
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hc
    (Filter.Eventually.of_forall fun _ => zero_le) ?_
  filter_upwards [hΛexp, h1.eventually hH] with u hu hhu
  have hk : atTau θ V τ u = oneP θ V τ (Λ u) 1 := by
    show atTau θ V τ u = atTau θ V τ (NormedSpace.exp ((1 : ℝ) • Λ u))
    rw [one_smul, hu]
  rw [hk]
  exact growthSize_sub_le hθ hs hf (hΛmem u) (hhu (hΛmem u))

end GlobalTheory.Size.NearOne

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaCorrespondenceTensorLawBothOrdersOfCovers
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum
open Formalism.IndefR.Mult (DSModel dualPar parA parB)
open Formalism.MainNotions.SchurIrreducible (AdmGK ARi ARiiiUp ARiiiDown ARiiiLine DiscreteSeriesBlattner admQ5)
open GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction hiding Mat
open GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix (SignCompat plainMat barMat)
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (fockIp)
open GlobalTheory.Chain (signed)
open GlobalTheory.Chain.RealIt (LPol locS locT IsPolyIso)
open MeasureTheory Matrix
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ArchRec

namespace GlobalTheory.ArchRec.TensLawOf

section

variable {p q r s : ℕ}

theorem cJoint_swap {σ : Type} (a₁ : Mat p q →ₗ[ℂ] Module.End ℂ (MvPolynomial σ ℂ))
    (a₂ : Mat r s →ₗ[ℂ] Module.End ℂ (MvPolynomial σ ℂ)) (Λ₁ : Ix p q → ℚ) (Λ₂ : Ix r s → ℚ)
    (Φ : MvPolynomial σ ℂ) (h : CJoint a₁ a₂ Λ₁ Λ₂ Φ) : CJoint a₂ a₁ Λ₂ Λ₁ Φ := by
  obtain ⟨⟨d, h0, h1, h2⟩, h3, h4⟩ := h
  exact ⟨⟨d, h0, h2, h1⟩, h4, h3⟩

theorem tIntw_swap {W : Type} [AddCommGroup W] [Module ℂ W] (a₁ : Mat p q →ₗ[ℂ] Module.End ℂ W)
    (a₂ : Mat r s →ₗ[ℂ] Module.End ℂ W) (M₁ : GKMod p q) (M₂ : GKMod r s) (f : W →ₗ[ℂ] M₁.V ⊗[ℂ] M₂.V)
    (h : TIntw a₁ a₂ M₁ M₂ f) :
    TIntw a₂ a₁ M₂ M₁ ((TensorProduct.comm ℂ M₁.V M₂.V).toLinearMap ∘ₗ f) := by
  constructor
  · intro Y
    rw [LinearMap.comp_assoc, h.2 Y, ← LinearMap.comp_assoc, ← LinearMap.comp_assoc]
    congr 1
    ext x y
    simp
  · intro Y
    rw [LinearMap.comp_assoc, h.1 Y, ← LinearMap.comp_assoc, ← LinearMap.comp_assoc]
    congr 1
    ext x y
    simp

theorem comm_comp_inj {W A B : Type} [AddCommGroup W] [Module ℂ W] [AddCommGroup A] [Module ℂ A]
    [AddCommGroup B] [Module ℂ B] {f g : W →ₗ[ℂ] A ⊗[ℂ] B}
    (h : (TensorProduct.comm ℂ A B).toLinearMap ∘ₗ f = (TensorProduct.comm ℂ A B).toLinearMap ∘ₗ g) : f = g := by
  refine LinearMap.ext fun x => ?_
  exact (TensorProduct.comm ℂ A B).injective (LinearMap.congr_fun h x)

theorem range_swap {W A B C : Type} [AddCommGroup W] [Module ℂ W] [AddCommGroup A] [Module ℂ A]
    [AddCommGroup B] [Module ℂ B] [AddCommGroup C] [Module ℂ C] (f : W →ₗ[ℂ] A ⊗[ℂ] B) (j : C →ₗ[ℂ] B)
    (h : LinearMap.range ((TensorProduct.comm ℂ A B).toLinearMap ∘ₗ f) =
      LinearMap.range (TensorProduct.map j (LinearMap.id : A →ₗ[ℂ] A))) :
    LinearMap.range f = LinearMap.range (TensorProduct.map (LinearMap.id : A →ₗ[ℂ] A) j) := by
  have e : (TensorProduct.comm ℂ A B).toLinearMap ∘ₗ TensorProduct.map (LinearMap.id : A →ₗ[ℂ] A) j =
      TensorProduct.map j (LinearMap.id : A →ₗ[ℂ] A) ∘ₗ (TensorProduct.comm ℂ A C).toLinearMap := by
    ext x y
    simp
  apply Submodule.map_injective_of_injective (f := (TensorProduct.comm ℂ A B).toLinearMap)
    (TensorProduct.comm ℂ A B).injective
  rw [← LinearMap.range_comp, ← LinearMap.range_comp, h, e,
    LinearMap.range_comp_of_range_eq_top _ (LinearEquiv.range _)]

end

theorem tensLaw_of : ∀ (X : ProvA) (p q r s : ℕ) (lam : Ix p q → ℚ) (lam' : Ix r s → ℚ), ARi X lam lam' → ARiiiUp X lam lam' → ARiiiDown X lam lam' → ARiiiLine X lam lam' → TensLaw (fockAct1 p q r s) (fockAct2 p q r s) (X.ds p q lam) (X.ds r s lam') (blattner lam) (blattner lam') ∧ TensLaw (fockAct2 p q r s) (fockAct1 p q r s) (X.ds r s lam') (X.ds p q lam) (blattner lam') (blattner lam) := by
  intro X p q r s lam lam' h1 hU hD hL
  obtain ⟨hiff, hnorm, huniq⟩ := _root_.GlobalTheory.ArchRec.Joint.joint_harmonics X p q r s (blattner lam) (blattner lam')
  obtain ⟨Φ₀, hΦ₀⟩ := h1.1
  have hex : CJoint (fockAct1 p q r s) (fockAct2 p q r s) (blattner lam) (blattner lam') Φ₀ :=
    (hiff Φ₀).2 ⟨hΦ₀.1, hΦ₀.2.1, hΦ₀.2.2.1⟩
  refine ⟨⟨⟨Φ₀, hex⟩, huniq, ?_, hL⟩, ⟨⟨Φ₀, cJoint_swap _ _ _ _ _ hex⟩,
    fun Φ Φ' h h' => huniq Φ Φ' (cJoint_swap _ _ _ _ _ h) (cJoint_swap _ _ _ _ _ h'), ?_, ?_⟩⟩
  · intro MM f hf hf0
    obtain ⟨⟨N, -, e, he⟩, hΦ⟩ := hU MM f hf hf0
    refine ⟨⟨N, e, he⟩, fun Φ hJ => ?_⟩
    obtain ⟨c, -, hc⟩ := hnorm Φ hJ
    obtain ⟨g1, g2⟩ := hΦ _ hc
    refine ⟨fun h0 => g1 (by rw [map_smul, h0, smul_zero]), fun f' hf' h => g2 f' hf' ?_⟩
    rw [map_smul, map_smul, h]
  · intro MM f hf hf0
    have hf1 := tIntw_swap _ _ _ _ f hf
    obtain ⟨⟨N, -, e, he, hr⟩, hΦ⟩ := hD MM _ hf1
      (fun h => hf0 (comm_comp_inj (by rw [h, LinearMap.comp_zero])))
    refine ⟨⟨N, e, he, range_swap f _ hr⟩, fun Φ hJ => ?_⟩
    obtain ⟨c, -, hc⟩ := hnorm Φ (cJoint_swap _ _ _ _ _ hJ)
    obtain ⟨g1, g2⟩ := hΦ _ hc
    refine ⟨fun h0 => g1 (by rw [map_smul, LinearMap.comp_apply, h0, map_zero, smul_zero]), fun f' hf' h =>
      comm_comp_inj (g2 _ (tIntw_swap _ _ _ _ f' hf') ?_)⟩
    rw [map_smul, map_smul, LinearMap.comp_apply, LinearMap.comp_apply, h]
  · obtain ⟨f₀, hf₀, hne, hall⟩ := hL
    refine ⟨_, tIntw_swap _ _ _ _ f₀ hf₀,
      fun h => hne (comm_comp_inj (by rw [h, LinearMap.comp_zero])), fun f hf => ?_⟩
    obtain ⟨c, hc⟩ := hall _ (tIntw_swap _ _ _ _ f hf)
    refine ⟨c, comm_comp_inj ?_⟩
    rw [hc]
    refine LinearMap.ext fun x => ?_
    simp

end GlobalTheory.ArchRec.TensLawOf

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLiftNsmulMemCompletedHomLattice
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LiftLevel

theorem isLattice_stdL (E : Type) [Field E] [NumberField E] (n : ℕ) :
    Submodule.IsLattice E (stdL E n) := by
  refine ⟨Submodule.fg_span (Set.finite_range _), ?_⟩
  intro s hs hli
  exact (LinearIndependent.iff_fractionRing _ _).mp hli
theorem isFullLattice_stdL (E : Type) [Field E] [NumberField E] (n : ℕ) :
    Submodule.IsFullLattice E (stdL E n) := by
  letI := isLattice_stdL E n
  refine ⟨?_⟩
  rw [stdL, Submodule.span_span_of_tower, ← (Pi.basisFun E (Fin n)).span_eq]
  congr 2
  funext i
  exact (Pi.basisFun_apply E (Fin n) i).symm

theorem liftL_nsmul_mem_latO : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (hn : T.rank ≤ S.rank) (ΛT : Lt D.host.E T.rank), IsSelfDualC T ΛT → IsAA C.X.Λ ΛT → ∀ (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)), Formalism.L2.DIV.IsFrame βS (stdL D.host.E S.rank) → Formalism.L2.DIV.IsFrame βT ΛT → ∀ (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ), Pg.Nonempty → (∀ PP, PP ∈ Pg ∨ PP ∈ Q → (2 : 𝓞 D.host.E) ∉ PP.asIdeal) → ∀ e : AE D, IsIdemSum e (Pg ∪ Q) → ∃ m : ℕ, 0 < m ∧ ∀ x ∈ GlobalTheory.LiftLevel.liftL S T βS βT Pg Q e, m • x ∈ latO S T (stdL D.host.E S.rank : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True := by
  intro D S T C hn ΛT hΛT hAA βS βT hβS hβT Pg Q ξ hPg h2 e he
  obtain ⟨k₂, hk₂, h₂⟩ := GlobalTheory.PlaceVec.frMapAdj_down S T βS βT
  obtain ⟨k₄, hk₄, h₄⟩ := GlobalTheory.PlaceVec.exists_nsmul_int_mem_latO (S := S) (T := T)
    (ΛS := stdL D.host.E S.rank) (ΛT := ΛT) (isFullLattice_stdL D.host.E S.rank) (GlobalTheory.PlaceVec.selfDual_isFullLattice T ΛT hΛT)
  have hinf : infPart D (cA D e) = 0 := GlobalTheory.PlaceVec.infPart_cA (GlobalTheory.PlaceVec.idemSum_infPart he)
  refine ⟨k₄ * k₂, Nat.mul_pos hk₄ hk₂, fun x hx => ?_⟩
  obtain ⟨hhalf, hint, -⟩ := hx
  have hx0 : (k₂ • x).map (infPart D) = 0 := by
    ext i j
    show infPart D ((k₂ • x) i j) = 0
    rw [Matrix.smul_apply, ← hhalf i j, nsmul_eq_mul, RingHom.map_mul, RingHom.map_mul, hinf, zero_mul, mul_zero]
  rw [mul_smul]
  exact h₄ (k₂ • x) hx0 (by rw [GlobalTheory.PlaceVec.map_toEAf_nsmul]; exact h₂ x hint)

end GlobalTheory.LiftLevel
end
end

