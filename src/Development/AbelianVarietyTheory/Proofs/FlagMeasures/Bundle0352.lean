module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0161
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SobolevInequalityAtIdentityBesselModelUnitaryGro
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TendstoAverageL2Compact
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0175
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0251
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0186
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0179
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0193
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CardIntegralFramesFixedLiftLe
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0348
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0351
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FamDefs
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0025
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.StepAnalyticConstantsP
public import Formalism.LocalToGlobal.Divisibility.Bundle0004
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0028
public import Formalism.LocalToGlobal.GroupLattices.JointServices.LevelOperatorFixesImage
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0229

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BoundedEquivariantMapSmoothContinuousSeminormBou
section
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

namespace GlobalTheory.SgInf

theorem sq_nnnorm_sub_le {W : Type} [NormedAddCommGroup W] (a b c : W) :
    (‖a - b‖₊ : ENNReal) ^ 2 ≤ 2 * (‖a - c‖₊ : ENNReal) ^ 2 + 2 * (‖b - c‖₊ : ENNReal) ^ 2 := by
  have h : ‖a - b‖ ≤ ‖a - c‖ + ‖b - c‖ := by
    simpa [norm_sub_rev] using norm_sub_le_norm_sub_add_norm_sub a c b
  have h2 : (‖a - b‖₊ : NNReal) ^ 2 ≤ 2 * (‖a - c‖₊ : NNReal) ^ 2 + 2 * (‖b - c‖₊ : NNReal) ^ 2 := by
    rw [← NNReal.coe_le_coe]
    push_cast
    nlinarith [sq_nonneg (‖a - c‖ - ‖b - c‖), norm_nonneg (a - b), norm_nonneg (a - c),
      norm_nonneg (b - c)]
  exact_mod_cast h2

theorem list_sq_le {ι : Type} (c : ℝ) (hc : 0 ≤ c) (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (l : List ι) :
    (l.map fun w => 2 * ENNReal.ofReal (c * a w ^ 2)).sum ≤
      ENNReal.ofReal (2 * c * (l.map a).sum ^ 2) := by
  induction l with
  | nil => simp
  | cons w l ih =>
    have hS : 0 ≤ (l.map a).sum := List.sum_nonneg (by
      intro x hx
      obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
      exact ha i)
    simp only [List.map_cons, List.sum_cons]
    have e : 2 * ENNReal.ofReal (c * a w ^ 2) = ENNReal.ofReal (2 * (c * a w ^ 2)) := by
      rw [ENNReal.ofReal_mul (p := 2) (q := c * a w ^ 2) (by norm_num)]; simp
    rw [e]
    refine (add_le_add le_rfl ih).trans ?_
    rw [← ENNReal.ofReal_add (by have := ha w; positivity) (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have := ha w
    nlinarith [mul_nonneg hc (mul_nonneg this hS)]

theorem list_sum_le_two {ι : Type} (l : List ι) (A a b : ι → ENNReal)
    (h : ∀ i ∈ l, A i ≤ 2 * a i + 2 * b i) :
    (l.map A).sum ≤ 2 * (l.map a).sum + 2 * (l.map b).sum := by
  induction l with
  | nil => simp
  | cons w l ih =>
    simp only [List.map_cons, List.sum_cons, mul_add]
    have h1 := h w List.mem_cons_self
    have h2 := ih fun i hi => h i (List.mem_cons_of_mem _ hi)
    calc A w + (l.map A).sum ≤ (2 * a w + 2 * b w) + (2 * (l.map a).sum + 2 * (l.map b).sum) :=
          add_le_add h1 h2
      _ = 2 * a w + 2 * (l.map a).sum + (2 * b w + 2 * (l.map b).sum) := by
          rw [add_add_add_comm]

theorem reg_main : ∀ (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] (σ : Mat k r → (H →L[ℂ] H)) (μG : Measure (Mt k r)) (T : H → Mat k r → Wp), IsURepOn (GG k r) σ → IsHaarOn (GG k r) μG → (∀ u u' : H, (fun x : Mt k r => T (u + u') (Matrix.of x)) =ᵐ[μG] fun x => T u (Matrix.of x) + T u' (Matrix.of x)) → (∀ (b : ℂ) (u : H), (fun x : Mt k r => T (b • u) (Matrix.of x)) =ᵐ[μG] fun x => b • T u (Matrix.of x)) → (∀ K : Set (Mt k r), IsCompact K → ∃ C : ℝ, ∀ u : H, AEStronglyMeasurable (fun x : Mt k r => T u (Matrix.of x)) (μG.restrict K) ∧ ∫⁻ x in K, (‖T u (Matrix.of x)‖₊ : ENNReal) ^ 2 ∂μG ≤ ENNReal.ofReal (C * ‖u‖ ^ 2)) → (∀ y ∈ GG k r, ∀ u : H, (fun x : Mt k r => T (σ y u) (Matrix.of x)) =ᵐ[μG] fun x => T u (Matrix.of x * y)) → ∃ (C : ℝ) (Ws : List (List (Mat k r))), (∀ ws ∈ Ws, ∀ X ∈ ws, InLieHpk k r X) ∧ ∀ u : H, IsSmoothVec σ u → ∃ f : Mat k r → Wp, ContinuousOn f (GG k r) ∧ (fun x : Mt k r => f (Matrix.of x)) =ᵐ[μG] (fun x => T u (Matrix.of x)) ∧ ‖f 1‖ ≤ C * (Ws.map fun ws => ‖dsigW σ ws u‖).sum := by
  intro k r H _ _ _ Wp _ _ _ σ μ T hσ hμ hadd hsm hbd heq
  haveI : CompleteSpace Wp := FiniteDimensional.complete ℂ Wp
  have hGae : ∀ᵐ y ∂μ, (Matrix.of y : Mat k r) ∈ GG k r := by
    rw [ae_iff]; exact hμ.2.2.1
  have hGm : MeasurableSet {x : Mt k r | (Matrix.of x : Mat k r) ∈ GG k r} :=
    IsClosed.measurableSet (α := Mt k r) (gg_closedSub k r).2.1
  have hrest : μ.restrict {x : Mt k r | (Matrix.of x : Mat k r) ∈ GG k r} = μ :=
    Measure.restrict_eq_self_of_ae_mem hGae
  have hcm : ∀ (Λ' : H →L[ℂ] Wp) (v : H),
      AEStronglyMeasurable (fun y : Mt k r => Λ' (σ (Matrix.of y) v)) μ := by
    intro Λ' v
    have hc : ContinuousOn (fun y : Mt k r => Λ' (σ (Matrix.of y) v))
        {x : Mt k r | (Matrix.of x : Mat k r) ∈ GG k r} :=
      Λ'.continuous.comp_continuousOn (hσ.2.2 v)
    have := hc.aestronglyMeasurable (μ := μ) hGm
    rwa [hrest] at this
  obtain ⟨C₀, Ws, K₀, hK₀, hWs, hsob⟩ := _root_.GlobalTheory.SobAtOne.sobolev_at_one_G k r μ hμ
  have hsu := _root_.GlobalTheory.SgInf.SobTranslate.sobolev_translate k r μ C₀ Ws K₀ hμ hK₀ hsob
  have hclm : ∀ Q : Set (Mt k r), IsCompact Q → ∃ K₂ : Set (Mt k r), IsCompact K₂ ∧
      ∀ (Λ' : H →L[ℂ] Wp) (u : H), IsSmoothVec (k := k) (r := r) σ u → ∀ x ∈ Q,
      (Matrix.of x : Mat k r) ∈ GG k r →
      ENNReal.ofReal (‖Λ' (σ (Matrix.of x) u)‖ ^ 2) ≤ ENNReal.ofReal |C₀| *
        (Ws.map fun ws => ∫⁻ y in K₂, (‖Λ' (σ (Matrix.of y) (dsigW σ ws u))‖₊ : ENNReal) ^ 2 ∂μ).sum := by
    intro Q hQ
    obtain ⟨K₂, hK₂, h⟩ := hsu Q hQ
    refine ⟨K₂, hK₂, fun Λ' u hu x hx hxG => ?_⟩
    obtain ⟨hs, hd⟩ := GlobalTheory.T.smooth_functional_orbit_smoothVector k r σ Λ' hσ u hu
    have hcont : ∀ ws ∈ Ws, ContinuousOn (rdWord ws fun g : Mat k r => Λ' (σ g u)) (GG k r) := by
      intro ws hws
      have h1 : ContinuousOn (fun g : Mat k r => Λ' (σ g (dsigW σ ws u))) (GG k r) :=
        Λ'.continuous.comp_continuousOn (hσ.2.2 _)
      exact h1.congr (fun x hx => hd ws (hWs ws hws) x hx)
    refine (h Wp _ hs hcont x hx hxG).trans (le_of_eq ?_)
    congr 2
    refine List.map_congr_left fun ws hws => ?_
    refine lintegral_congr_ae (ae_restrict_of_ae ?_)
    filter_upwards [hGae] with y hy
    rw [hd ws (hWs ws hws) _ hy]
  obtain ⟨K₁, hK₁, hone⟩ := hclm {oneM k r} isCompact_singleton
  obtain ⟨c₁, hc₁⟩ := hbd K₁ hK₁
  choose Λ hΛ using _root_.GlobalTheory.SgInf.ballMean_clm k r σ μ T hμ hadd hsm hbd heq
  refine ⟨Real.sqrt (|C₀| * (2 * |c₁|)), Ws, hWs, fun u hu => ?_⟩
  have hloc : ∀ (v : H) (K : Set (Mt k r)), IsCompact K →
      AEStronglyMeasurable (fun z : Mt k r => T v (Matrix.of z)) (μ.restrict K) ∧
      ∫⁻ x in K, (‖T v (Matrix.of x)‖₊ : ENNReal) ^ 2 ∂μ < ⊤ := by
    intro v K hK
    obtain ⟨C, hC⟩ := hbd K hK
    exact ⟨(hC v).1, (hC v).2.trans_lt ENNReal.ofReal_lt_top⟩
  have hconv : ∀ (v : H) (K : Set (Mt k r)), IsCompact K → Filter.Tendsto (fun j : ℕ =>
      ∫⁻ x in K, (‖avgR μ j (fun z : Mt k r => T v (Matrix.of z)) x - T v (Matrix.of x)‖₊ : ENNReal) ^ 2 ∂μ)
      Filter.atTop (nhds 0) :=
    fun v K hK => _root_.GlobalTheory.SgInf.tendsto_average_L2 k r μ hμ _ (hloc v) K hK

  have hAm : ∀ (j : ℕ) (v : H) (K : Set (Mt k r)), IsCompact K → AEMeasurable (fun y : Mt k r =>
      (‖avgR μ j (fun z : Mt k r => T v (Matrix.of z)) y - T v (Matrix.of y)‖₊ : ENNReal) ^ 2) (μ.restrict K) := by
    intro j v K hK
    have h1 : AEStronglyMeasurable (fun y : Mt k r => avgR μ j (fun z : Mt k r => T v (Matrix.of z)) y) μ := by
      refine (hcm (Λ j) v).congr ?_
      filter_upwards [hGae] with x hx
      exact hΛ j v x hx
    exact ((h1.restrict.sub (hloc v K hK).1).nnnorm.aemeasurable.coe_nnreal_ennreal).pow_const 2

  have hsp : ∀ (j l : ℕ) (v : H) (K : Set (Mt k r)), IsCompact K →
      ∫⁻ y in K, (‖(Λ j - Λ l) (σ (Matrix.of y) v)‖₊ : ENNReal) ^ 2 ∂μ ≤
      2 * ∫⁻ x in K, (‖avgR μ j (fun z : Mt k r => T v (Matrix.of z)) x - T v (Matrix.of x)‖₊ : ENNReal) ^ 2 ∂μ +
      2 * ∫⁻ x in K, (‖avgR μ l (fun z : Mt k r => T v (Matrix.of z)) x - T v (Matrix.of x)‖₊ : ENNReal) ^ 2 ∂μ := by
    intro j l v K hK
    rw [← lintegral_const_mul' 2 _ (by simp), ← lintegral_const_mul' 2 _ (by simp),
      ← lintegral_add_left' ((hAm j v K hK).const_mul 2)]
    refine lintegral_mono_ae (ae_restrict_of_ae ?_)
    filter_upwards [hGae] with y hy
    rw [ContinuousLinearMap.sub_apply, hΛ j v y hy, hΛ l v y hy]
    exact sq_nnnorm_sub_le _ _ _
  have hsp1 : ∀ (j : ℕ) (v : H) (K : Set (Mt k r)), IsCompact K →
      ∫⁻ y in K, (‖Λ j (σ (Matrix.of y) v)‖₊ : ENNReal) ^ 2 ∂μ ≤
      2 * ∫⁻ x in K, (‖avgR μ j (fun z : Mt k r => T v (Matrix.of z)) x - T v (Matrix.of x)‖₊ : ENNReal) ^ 2 ∂μ +
      2 * ∫⁻ x in K, (‖T v (Matrix.of x)‖₊ : ENNReal) ^ 2 ∂μ := by
    intro j v K hK
    rw [← lintegral_const_mul' 2 _ (by simp), ← lintegral_const_mul' 2 _ (by simp),
      ← lintegral_add_left' ((hAm j v K hK).const_mul 2)]
    refine lintegral_mono_ae (ae_restrict_of_ae ?_)
    filter_upwards [hGae] with y hy
    rw [hΛ j v y hy]
    simpa using sq_nnnorm_sub_le (avgR μ j (fun z : Mt k r => T v (Matrix.of z)) y) 0 (T v (Matrix.of y))
  have hEt : ∀ K : Set (Mt k r), IsCompact K → Filter.Tendsto (fun j : ℕ =>
      (Ws.map fun ws => ∫⁻ x in K, (‖avgR μ j (fun z : Mt k r => T (dsigW σ ws u) (Matrix.of z)) x -
        T (dsigW σ ws u) (Matrix.of x)‖₊ : ENNReal) ^ 2 ∂μ).sum) Filter.atTop (nhds 0) := by
    intro K hK
    have h := tendsto_list_sum (f := fun (ws : List (Mat k r)) (j : ℕ) =>
      ∫⁻ x in K, (‖avgR μ j (fun z : Mt k r => T (dsigW σ ws u) (Matrix.of z)) x -
        T (dsigW σ ws u) (Matrix.of x)‖₊ : ENNReal) ^ 2 ∂μ) (a := fun _ => 0) Ws
      (fun ws _ => hconv _ K hK)
    have e0 : (Ws.map fun _ => (0 : ENNReal)).sum = 0 := by simp
    rwa [e0] at h
  have hCau : ∀ Q : Set (Mt k r), IsCompact Q → ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ j ≥ N, ∀ l ≥ N, ∀ x ∈ Q,
      (Matrix.of x : Mat k r) ∈ GG k r →
      ‖Λ j (σ (Matrix.of x) u) - Λ l (σ (Matrix.of x) u)‖ ≤ ε := by
    intro Q hQ ε hε
    obtain ⟨K₂, hK₂, h⟩ := hclm Q hQ
    have hG : Filter.Tendsto (fun j : ℕ => ENNReal.ofReal |C₀| * (2 *
        (Ws.map fun ws => ∫⁻ x in K₂, (‖avgR μ j (fun z : Mt k r => T (dsigW σ ws u) (Matrix.of z)) x -
          T (dsigW σ ws u) (Matrix.of x)‖₊ : ENNReal) ^ 2 ∂μ).sum)) Filter.atTop (nhds 0) := by
      have h1 := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal |C₀|)
        (ENNReal.Tendsto.const_mul (a := 2) (hEt K₂ hK₂) (Or.inr (by simp)))
        (Or.inr ENNReal.ofReal_ne_top)
      simpa using h1
    have hη : (0 : ENNReal) < ENNReal.ofReal (ε ^ 2 / 2) := ENNReal.ofReal_pos.2 (by positivity)
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (hG.eventually_lt_const hη)
    refine ⟨N, fun j hj l hl x hx hxG => ?_⟩
    have hb := h (Λ j - Λ l) u hu x hx hxG
    have hs := list_sum_le_two Ws _ _ _ (fun ws _ => hsp j l (dsigW σ ws u) K₂ hK₂)
    have h3 : ENNReal.ofReal (‖(Λ j - Λ l) (σ (Matrix.of x) u)‖ ^ 2) ≤
        ENNReal.ofReal (ε ^ 2 / 2) + ENNReal.ofReal (ε ^ 2 / 2) := by
      refine hb.trans ((mul_le_mul' le_rfl hs).trans ?_)
      rw [mul_add]
      exact add_le_add (hN j hj).le (hN l hl).le
    rw [← ENNReal.ofReal_add (by positivity) (by positivity),
      ENNReal.ofReal_le_ofReal_iff (by positivity)] at h3
    have h4 : ‖(Λ j - Λ l) (σ (Matrix.of x) u)‖ ^ 2 ≤ ε ^ 2 := by linarith
    have h5 := (pow_le_pow_iff_left₀ (norm_nonneg _) hε.le (by norm_num)).1 h4
    simpa using h5
  obtain ⟨F, hFc, hFae, hFl⟩ := _root_.GlobalTheory.SgInf.RegLimit.exists_continuous_limit k r μ hμ (fun j g => Λ j (σ g u))
    (fun z : Mt k r => T u (Matrix.of z)) (fun j => (Λ j).continuous.comp_continuousOn (hσ.2.2 u))
    (fun Q hQ => (hloc u Q hQ).1) hCau (fun Q hQ => by
      refine (hconv u Q hQ).congr fun j => ?_
      refine lintegral_congr_ae (ae_restrict_of_ae ?_)
      filter_upwards [hGae] with x hx
      rw [hΛ j u x hx])
  refine ⟨F, hFc, hFae, ?_⟩
  have h1G : (1 : Mat k r) ∈ GG k r := (gg_closedSub k r).2.2.1
  have hlim := hFl 1 h1G
  have hb : ∀ j : ℕ, ENNReal.ofReal (‖Λ j (σ 1 u)‖ ^ 2) ≤ ENNReal.ofReal |C₀| * (2 *
      (Ws.map fun ws => ∫⁻ x in K₁, (‖avgR μ j (fun z : Mt k r => T (dsigW σ ws u) (Matrix.of z)) x -
          T (dsigW σ ws u) (Matrix.of x)‖₊ : ENNReal) ^ 2 ∂μ).sum +
      2 * (Ws.map fun ws => ENNReal.ofReal (|c₁| * ‖dsigW σ ws u‖ ^ 2)).sum) := by
    intro j
    have h0 := hone (Λ j) u hu (oneM k r) rfl h1G
    refine h0.trans (mul_le_mul' le_rfl (list_sum_le_two Ws _ _ _ fun ws _ => ?_))
    refine (hsp1 j (dsigW σ ws u) K₁ hK₁).trans ?_
    gcongr
    refine (hc₁ _).2.trans (ENNReal.ofReal_le_ofReal ?_)
    have := le_abs_self c₁
    have h2 := sq_nonneg ‖dsigW σ ws u‖
    nlinarith
  have hlimL : Filter.Tendsto (fun j : ℕ => ENNReal.ofReal (‖Λ j (σ 1 u)‖ ^ 2)) Filter.atTop
      (nhds (ENNReal.ofReal (‖F 1‖ ^ 2))) :=
    (ENNReal.continuous_ofReal.tendsto _).comp (hlim.norm.pow 2)
  have hlimR := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal |C₀|)
    ((ENNReal.Tendsto.const_mul (a := 2) (hEt K₁ hK₁) (Or.inr (by simp))).add
      (tendsto_const_nhds (x := 2 * (Ws.map fun ws => ENNReal.ofReal (|c₁| * ‖dsigW σ ws u‖ ^ 2)).sum)))
    (Or.inr ENNReal.ofReal_ne_top)
  have hfin := le_of_tendsto_of_tendsto' hlimL hlimR hb
  rw [mul_zero, zero_add, ← List.sum_map_mul_left] at hfin
  have hS := list_sq_le |c₁| (abs_nonneg _) (fun ws : List (Mat k r) => ‖dsigW σ ws u‖)
    (fun _ => norm_nonneg _) Ws
  have hSn : 0 ≤ (Ws.map fun ws => ‖dsigW σ ws u‖).sum := List.sum_nonneg (by
    intro x hx
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
    exact norm_nonneg _)
  have h3 := hfin.trans (mul_le_mul' le_rfl hS)
  rw [← ENNReal.ofReal_mul (abs_nonneg _),
    ENNReal.ofReal_le_ofReal_iff (by positivity)] at h3
  have h4 := Real.abs_le_sqrt (h := h3)
  rw [abs_norm] at h4
  have e : |C₀| * (2 * |c₁| * (Ws.map fun ws => ‖dsigW σ ws u‖).sum ^ 2) =
      (|C₀| * (2 * |c₁|)) * (Ws.map fun ws => ‖dsigW σ ws u‖).sum ^ 2 := by ring
  rw [e, Real.sqrt_mul (by positivity), Real.sqrt_sq hSn] at h4
  exact h4

end GlobalTheory.SgInf
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CardExactGramIntegralFrameClassesLe
section
noncomputable section

open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC GlobalTheory.LoopC.FrEqv
open scoped ENNReal Classical

namespace GlobalTheory.LoopC.FrEx

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T T' : E}

theorem hT_swap {x y : S.V} (h : S.hT x y = 0) : S.hT y x = 0 := by
  have := S.herm.eq x y
  rw [h, map_zero] at this
  exact this.symm

theorem mem_orth {U : Submodule E S.V} {y : S.V} : y ∈ orth S U ↔ ∀ x ∈ U, S.hT x y = 0 := by
  simp only [orth, Submodule.mem_iInf, LinearMap.mem_ker]

def moveFl (n : S.V ≃ₗ[E] S.V) (hn : n ∈ Formalism.HermitianLatticesTheory.isom S.hT) (F : LFlag S r T) : LFlag S r T :=
  ⟨⟨fun a => n (F.fl.e a), n F.fl.z,
    F.fl.e_indep.map' (n : S.V →ₗ[E] S.V) n.ker,
    fun a b => (hn _ _).trans (F.fl.e_iso a b), fun a => (hn _ _).trans (F.fl.z_orth a),
    (hn _ _).trans F.fl.z_norm⟩, n F.fl.z⟩

theorem frame_moveFl (n : S.V ≃ₗ[E] S.V) (hn : n ∈ Formalism.HermitianLatticesTheory.isom S.hT) (F : LFlag S r T) (b : Fin (r + 1)) :
    frame (moveFl n hn F) b = n (frame F b) := by
  refine Fin.lastCases ?_ (fun a => ?_) b <;> simp [frame, FlagG.fvec, moveFl]

theorem eq_zero_of_orth_frame (F : LFlag S r T) (F' : LFlag S r T') (b₀ : Fin (r + 1))
    (hd : (((ZhatL F F').submatrix Fin.castSucc id).submatrix id b₀.succAbove).det ≠ 0)
    {x : S.V} (hx : x ∈ Xsp F) (h : ∀ b, S.hT x (frame F' b) = 0) : x = 0 := by
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun E).1 hx
  have h0 : (fun a => star (c a)) = 0 := by
    refine Matrix.eq_zero_of_vecMul_eq_zero hd ?_
    funext b
    have := h (b₀.succAbove b)
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, LinearMap.map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
      starRingEnd_apply] at this
    simpa [Matrix.vecMul, dotProduct, Zhat, brS, FlagG.fvec] using this
  have : ∀ a, c a = 0 := fun a => by simpa using congrFun h0 a
  simp [this]

theorem orth_frame_of_mem_Thp {Λ : Submodule (𝓞 E) S.V} {F : LFlag S r T} {F' : LFlag S r T'}
    (hl : IsLift Λ F') (he : ∀ a, F'.fl.e a ∈ Λ) {θ : S.V} (hθ : θ ∈ Thp Λ F F') (b : Fin (r + 1)) :
    S.hT θ (frame F' b) = 0 := by
  refine hT_swap (mem_orth.1 hθ.2 _ (Submodule.subset_span ?_))
  refine Fin.lastCases ?_ (fun a => ?_) b
  · have : frame F' (Fin.last r) = F'.zt := by simp [frame, FlagG.fvec, hl.2]
    rw [this]
    exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
  · have : frame F' a.castSucc = F'.fl.e a := by simp [frame, FlagG.fvec]
    rw [this]
    exact Submodule.mem_sup_left (Submodule.mem_sup_right ⟨he a, Submodule.subset_span ⟨a, rfl⟩⟩)

end Gen

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable (D : D7)

theorem eq_zero_of_span_E {x : (hS D).V} (hx : x ∈ Submodule.span D.host.E (Set.range D.sp.hypE))
    (h : ∀ a, (hS D).hT x (D.sp.hypF a) = 0) : x = 0 := by
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun D.host.E).1 hx
  have : ∀ a, c a = 0 := fun a => by
    have := h a
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, LinearMap.map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
      D.sp.hyp_ef] at this
    simpa using this
  simp [this]

theorem eq_zero_of_span_F {x : (hS D).V} (hx : x ∈ Submodule.span D.host.E (Set.range D.sp.hypF))
    (h : ∀ a, (hS D).hT (D.sp.hypE a) x = 0) : x = 0 := by
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun D.host.E).1 hx
  have : ∀ a, c a = 0 := fun a => by
    have := h a
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, smul_eq_mul, D.sp.hyp_ef] at this
    simpa using this
  simp [this]

theorem YS_le {y : (hS D).V} (hy : y ∈ YS D) : y ∈ Submodule.span D.host.E (Set.range D.sp.hypF) := by
  have : YS D ≤ toO (hS D) (Submodule.span D.host.E (Set.range D.sp.hypF)) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨a, x, _, rfl⟩
    exact Submodule.smul_mem (Submodule.span D.host.E (Set.range D.sp.hypF)) x (Submodule.subset_span ⟨a, rfl⟩)
  exact this hy

theorem XS_le {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) {y : (hS D).V} (hy : y ∈ XS D F0) : y ∈ F0.X := by
  have : XS D F0 ≤ toO (hS D) F0.X := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨a, x, _, rfl⟩
    exact Submodule.smul_mem F0.X x (Submodule.subset_span ⟨a, rfl⟩)
  exact this hy

theorem iXY_mem_of_split {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (he : F0.e = D.sp.hypE) {Λ : LatV D}
    (hs : IsSplit D F0 Λ) (p : (D.sp.X 0).V) {θ : (hS D).V} (hθ : θ ∈ Λ) (hx : θ - D.sp.iXY 0 p ∈ F0.X) :
    D.sp.iXY 0 p ∈ Λ := by
  have hθ' := hθ
  rw [hs] at hθ'
  obtain ⟨_, h1, y, hy, rfl⟩ := Submodule.mem_sup.1 hθ'
  obtain ⟨a, ha, w, hw, rfl⟩ := Submodule.mem_sup.1 h1
  have haX := XS_le D F0 ha
  have hX : ∀ x ∈ F0.X, ∀ i, (hS D).hT (D.sp.hypE i) x = 0 := fun x hx i =>
    mem_orth.1 (X_le_orth (F := lf D F0) hx) _ (Submodule.subset_span ⟨i, by rw [← he]⟩)
  have hwE : ∀ i, (hS D).hT (D.sp.hypE i) w = 0 := fun i =>
    mem_orth.1 hw.2 _ (Submodule.subset_span (Or.inl ⟨i, rfl⟩))
  have hwF : ∀ i, (hS D).hT (D.sp.hypF i) w = 0 := fun i =>
    mem_orth.1 hw.2 _ (Submodule.subset_span (Or.inr ⟨i, rfl⟩))
  have hy0 : y = 0 := by
    refine eq_zero_of_span_F D (YS_le D hy) fun i => ?_
    have h1 := hX _ hx i
    have h2 : (hS D).hT (D.sp.hypE i) (D.sp.iXY 0 p) = 0 := hT_swap (D.sp.hyp_orthX i p).1
    rw [map_sub, map_add (f := _), map_add (f := _), h2, hX a haX i, hwE i] at h1
    simpa using h1
  subst hy0
  have h3 : w - D.sp.iXY 0 p ∈ F0.X := by
    have := F0.X.sub_mem hx haX
    convert this using 1
    abel
  have h4 : w - D.sp.iXY 0 p = 0 := by
    refine eq_zero_of_span_E D (by rw [← he]; exact h3) fun i => ?_
    rw [map_sub, LinearMap.sub_apply, hT_swap (hwF i)]
    have := (D.sp.hyp_orthX i p).2
    simpa using this
  rw [← sub_eq_zero.1 h4]
  exact hw.1

theorem exists_lift {T T' : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (he : F0.e = D.sp.hypE) {Λ : LatV D}
    (hs : IsSplit D F0 Λ) (P : LatW D) (Z : GramM D) (b₀ : Fin (D.R.rS + 1)) (hb : rowMinor D Z b₀ ≠ 0)
    {F' : Fg D T'} (hF : F' ∈ ExSet D Λ (lf D F0) T' Z P) :
    ∃ φ : P →ₗ[𝓞 D.host.E] (hS D).V, (∀ p, φ p ∈ XLam Λ (lf D F0)) ∧
      ∀ (p : P) b, (hS D).hT (D.sp.iXY 0 (p : (D.sp.X 0).V) + φ p) (frame F' b) = 0 := by
  obtain ⟨hl, hE, hZ, hP⟩ := hF
  have ex : ∀ p : P, ∃ x, x ∈ XLam Λ (lf D F0) ∧
      ∀ b, (hS D).hT (D.sp.iXY 0 (p : (D.sp.X 0).V) + x) (frame F' b) = 0 := by
    intro p
    obtain ⟨θ, hθ, x, hx, e⟩ := Submodule.mem_sup.1 (hP p.2)
    have e' : θ + x = D.sp.iXY 0 (p : (D.sp.X 0).V) := e
    have hx' : x ∈ F0.X := hx
    have h1 : θ - D.sp.iXY 0 (p : (D.sp.X 0).V) ∈ F0.X := by
      rw [← e']; simpa using hx'
    refine ⟨θ - D.sp.iXY 0 (p : (D.sp.X 0).V),
      ⟨Λ.sub_mem hθ.1 (iXY_mem_of_split D F0 he hs _ hθ.1 h1), h1⟩, fun b => ?_⟩
    rw [add_sub_cancel]
    exact orth_frame_of_mem_Thp hl hE hθ b
  choose f hf1 hf2 using ex
  have uniq : ∀ x ∈ F0.X, (∀ b, (hS D).hT x (frame F' b) = 0) → x = 0 := fun x hx h =>
    eq_zero_of_orth_frame (lf D F0) F' b₀ (by rw [hZ]; exact hb) hx h
  have hfX : ∀ p, f p ∈ F0.X := fun p => (hf1 p).2
  refine ⟨⟨⟨f, fun p q => ?_⟩, fun c p => ?_⟩, hf1, hf2⟩
  · rw [← sub_eq_zero]
    refine uniq _ (F0.X.sub_mem (hfX _) (F0.X.add_mem (hfX _) (hfX _))) fun b => ?_
    have h1 := hf2 (p + q) b
    have h2 := hf2 p b
    have h3 := hf2 q b
    simp only [Submodule.coe_add, map_add (f := _), map_sub, LinearMap.add_apply, LinearMap.sub_apply] at h1 h2 h3 ⊢
    linear_combination h1 - h2 - h3
  · show f (c • p) = c • f p
    have e1 : c • f p = algebraMap _ D.host.E c • f p := (algebraMap_smul D.host.E c (f p)).symm
    have e2 : ((c • p : P) : (D.sp.X 0).V) = algebraMap _ D.host.E c • (p : (D.sp.X 0).V) :=
      (algebraMap_smul D.host.E c (p : (D.sp.X 0).V)).symm
    rw [e1, ← sub_eq_zero]
    refine uniq _ (F0.X.sub_mem (hfX _) (F0.X.smul_mem _ (hfX _))) fun b => ?_
    have h1 := hf2 (c • p) b
    have h2 := hf2 p b
    rw [e2] at h1
    simp only [map_add (f := _), map_sub, map_smul, LinearMap.map_smulₛₗ, LinearMap.add_apply, LinearMap.sub_apply,
      LinearMap.smul_apply, smul_eq_mul] at h1 h2 ⊢
    linear_combination h1 - (starRingEnd D.host.E) (algebraMap _ D.host.E c) * h2

theorem cntCl_ExSet_le : ∀ (D : D7) (u u' : D.what₂.Word) (F0 : Fb D u) (Λ : LatV D), Stand D u u' → IsBase D u F0 → IsRowLat D F0 Λ → IsSplit D F0 Λ → ∀ (P : LatW D) (Z : GramM D) (s : ℕ) (De Q : ℝ), 1 ≤ s → s ≤ D.R.k → SubOK D (L0X D Λ (lf D F0)) P s De → QOK D u u' Z Q → (cntCl (ExSet D Λ (lf D F0) ((Tu D u' : ℕ) : D.host.E) Z P) (TEqv D Λ (lf D F0)) : ℝ≥0∞) ≤ ENNReal.ofReal (frB D s (NT D u) De Q) := by
  intro D u u' F0 Λ hst hb hrow hsp P Z s De Q hs1 hsk hsub hQ
  obtain ⟨reps, hcard, hreps, hall⟩ := GlobalTheory.T.exists_sublattice_lifts_modulo_fixing_unipotent D u u' F0 Λ hst hb hrow hsp P s De hsub
  obtain ⟨b₀, hb₀, -⟩ := hQ.2.2.1
  have h1 := cntCl_le_sum (TEqv_equivalence D Λ (lf D F0) (T' := ((Tu D u' : ℕ) : D.host.E))) reps
    (ExSet D Λ (lf D F0) ((Tu D u' : ℕ) : D.host.E) Z P)
    (fun φ => FixSet D Λ (lf D F0) ((Tu D u' : ℕ) : D.host.E) Z P φ) (by
      intro F' hF'
      obtain ⟨φ, hφ, hφ'⟩ := exists_lift D F0 hb.1 hsp P Z b₀ hb₀ hF'
      obtain ⟨φ₀, h₀, n, ⟨hn, hnf⟩, hnp⟩ := hall φ hφ
      obtain ⟨hl, hE, hZ, -⟩ := hF'
      refine ⟨φ₀, h₀, moveFl n hn.1.1 F', ⟨⟨(aut_mem_iff hn.1 _).2 hl.1, rfl⟩,
        fun a => (aut_mem_iff hn.1 _).2 (hE a), ?_, fun p b => ?_⟩, n, hn, 1,
        fun a b h => Matrix.one_apply_ne h.ne', fun a => by simp, ?_⟩
      · rw [← hZ]
        funext a b
        change (hS D).hT (frame (lf D F0) a) (frame (moveFl n hn.1.1 F') b) =
          (hS D).hT (frame (lf D F0) a) (frame F' b)
        rw [frame_moveFl, ← hn.1.1 (frame (lf D F0) a) (frame F' b), hnf]
      · rw [frame_moveFl, ← hnp, hn.1.1]
        exact hφ' p b
      · rw [frameAct_one]
        funext b
        exact frame_moveFl _ _ _ b)
  have h2 : (cntCl (ExSet D Λ (lf D F0) ((Tu D u' : ℕ) : D.host.E) Z P) (TEqv D Λ (lf D F0)) : ℝ≥0∞) ≤
      ∑ φ ∈ reps, (cntCl (FixSet D Λ (lf D F0) ((Tu D u' : ℕ) : D.host.E) Z P φ) (TEqv D Λ (lf D F0)) : ℝ≥0∞) := by
    have := ENat.toENNReal_le.2 h1
    refine this.trans (le_of_eq ?_)
    exact map_sum ENat.toENNRealRingHom _ _
  refine h2.trans ((Finset.sum_le_card_nsmul _ _ _ fun φ hφ =>
    _root_.GlobalTheory.LoopC.FixedLift.card_frames_le D u u' F0 Λ hst hb hrow hsp P φ Z s De Q hs1 hsk (hreps φ hφ) hsub hQ).trans ?_)
  have hnn : 0 ≤ NT D u ^ (2 * D.R.rS) * De ^ D.R.rS := le_trans (Nat.cast_nonneg _) hcard
  rw [frB, ENNReal.ofReal_mul hnn, nsmul_eq_mul]
  gcongr
  rw [← ENNReal.ofReal_natCast]
  exact ENNReal.ofReal_le_ofReal hcard

end GlobalTheory.LoopC.FrEx

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.NonGenericCorankOnePairsBoundOfSplitFiniteRealRoStatement
section
open Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic GlobalTheory.NGRow
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonGenericCorankOnePairsBound_of_splitFiniteRealRow : NGCut2P → RowNGP := by
  first | exact @GlobalTheory.NGRow.rowNG_of_cut2P | exact GlobalTheory.NGRow.rowNG_of_cut2P | (intros; apply GlobalTheory.NGRow.rowNG_of_cut2P <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowMapSurjectiveOfPrimitiveRows
section
open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR.Links Formalism.IndefR.Cx NumberField

namespace GlobalTheory

theorem rowMap_surjective_of_primitiveRows_alt : ∀ (D : D7) [_root_.NumberField.IsTotallyComplex D.what₂.LL] (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (P0 : Subgroup G) (ψ0 : P0 →* D.what₂.LLˣ) (Ps : Subgroup G) (ψs : Ps →* D.what₂.LLˣ) (Zs : DefSub A3.fam3.amb3) (S0 : IndefData (A3.side3 P0 ψ0 Zs)) (S1 : IndefData (A3.side3 Ps ψs Zs)) (X0 : BaseLevelRowSide D) (Dc : DefCols (A3.side3 Ps ψs Zs)) (Sp : SPer Dc) (C : ColData Dc Sp S1) (NuC : ∀ u, Submodule (𝓞 D.what₂.LL) (Fin (Dc.a u) → D.what₂.LL)) (I : DivisionCompatibilityDataThreeSided D A3 P0 ψ0 Ps ψs Zs S0 S1 X0 Dc) (Dcf : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 Ps ψs Zs)) (Spf : ∀ Zs : DefSub A3.fam3.amb3, SPer (Dcf Zs)) (Zscf : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3) (s : ℕ), DivDef3 D A3 P0 ψ0 Ps ψs Zs S0 S1 X0 C NuC I → A3.fam3.Ok3 s → A3.fam3.TypesSep3 → R.WeakCharacterisation (⟨P0, ψ0, Ps, ψs, Dcf, Spf, Zscf⟩ : Face3 D A3) → PrimRows3 R (⟨P0, ψ0, Ps, ψs, Dcf, Spf, Zscf⟩ : Face3 D A3) → (R.toCx3 (⟨P0, ψ0, Ps, ψs, Dcf, Spf, Zscf⟩ : Face3 D A3)).zs = Zs → HEq ((R.toCx3 (⟨P0, ψ0, Ps, ψs, Dcf, Spf, Zscf⟩ : Face3 D A3)).data (⟨P0, ψ0, Ps, ψs, Dcf, Spf, Zscf⟩ : Face3 D A3).cr true) S1 → (D.what₂.V0 D.what₂.mu0).map (D.what₂.iota D.what₂.mu0) = ⊤ := by
  intro D _ G _ _ Pl0 I0 T A3 Ks _ _ _ R P0 ψ0 Ps ψs Zs S0 S1 X0 Dc Sp C NuC I Dcf Spf Zscf s hD hOk hSep hW hP hzs hS1
  obtain ⟨h1, h2⟩ := _root_.GlobalTheory.prim_rows_surjective D G Pl0 I0 T A3 Ks R ⟨P0, ψ0, Ps, ψs, Dcf, Spf, Zscf⟩ s hOk hSep hW hP Zs S1 hzs hS1
  exact _root_.GlobalTheory.V0_map_iota_eq_top_of_definite D G Pl0 I0 (List ℕ) T D.R.m A3 P0 ψ0 Ps ψs Zs S0 S1 X0 Dc Sp C NuC I hD ⟨s, hOk.ok2⟩ h1 h2

end GlobalTheory
end

