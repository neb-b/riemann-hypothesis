module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0057
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0021
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0018
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0007
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0055
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0004
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0004
public import ReciprocityTheory.AnalyticForms.AnalyticCharts.Bundle0001
public import ReciprocityTheory.AnalyticForms.AnalyticCharts.Osgood
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0046
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0058

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PPrimitiveFormMinimalFactorPoints
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

namespace PrimitiveFormMinimalFactorPoints

open Topology Filter Polynomial

def anSub {d : ℕ} (y₀ : Fin d → ℂ) : Subring ((Fin d → ℂ) → ℂ) where
  carrier := {f | AnalyticAt ℂ f y₀}
  mul_mem' ha hb := AnalyticAt.mul ha hb
  one_mem' := analyticAt_const
  add_mem' ha hb := AnalyticAt.add ha hb
  zero_mem' := analyticAt_const
  neg_mem' ha := AnalyticAt.neg ha

theorem coeff_analyticAt {d : ℕ} {y₀ : Fin d → ℂ} {E : Polynomial ((Fin d → ℂ) → ℂ)}
    (h : E ∈ liftsRing (anSub y₀).subtype) (k : ℕ) : AnalyticAt ℂ (E.coeff k) y₀ := by
  rw [← lifts_iff_liftsRing, lifts_iff_coeff_lifts] at h
  obtain ⟨f, hf⟩ := h k
  rw [← hf]
  exact f.2

theorem C_mem {d : ℕ} {y₀ : Fin d → ℂ} {f : (Fin d → ℂ) → ℂ} (hf : AnalyticAt ℂ f y₀) :
    C f ∈ liftsRing (anSub y₀).subtype := by
  rw [← lifts_iff_liftsRing]
  exact C_mem_lifts (anSub y₀).subtype ⟨f, hf⟩

theorem X_mem {d : ℕ} (y₀ : Fin d → ℂ) : (X : Polynomial ((Fin d → ℂ) → ℂ)) ∈ liftsRing (anSub y₀).subtype := by
  rw [← lifts_iff_liftsRing]
  exact X_mem_lifts _

theorem eval₂_eq_zero_of_dvd {d n : ℕ} {b : Fin n → (Fin d → ℂ) → ℂ} {y : Fin d → ℂ}
    {E : Polynomial ((Fin d → ℂ) → ℂ)}
    (hd : (X ^ n + ∑ j, C (b j y) * X ^ (j : ℕ) : Polynomial ℂ) ∣ E.map (Pi.evalRingHom (fun _ : Fin d → ℂ => ℂ) y))
    {τ : ℂ} (hτ : τ ^ n + ∑ j, b j y * τ ^ (j : ℕ) = 0) :
    E.eval₂ (Pi.evalRingHom (fun _ : Fin d → ℂ => ℂ) y) τ = 0 := by
  obtain ⟨G, hG⟩ := hd
  rw [← eval_map, hG, eval_mul]
  simp [eval_finsetSum, hτ]

theorem cleared_eq {n : ℕ} (c : Fin n → ℂ) (D x : ℂ) :
    (D * x) ^ n + ∑ j : Fin n, c j * D ^ (n - j) * (D * x) ^ (j : ℕ) =
      D ^ n * (x ^ n + ∑ j : Fin n, c j * x ^ (j : ℕ)) := by
  rw [mul_add, Finset.mul_sum, mul_pow]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_pow, ← pow_sub_mul_pow D j.2.le]
  ring

theorem linear_apply_eq_sum {σ : Type} [Fintype σ] [DecidableEq σ] {F : Type} [AddCommGroup F] [Module ℂ F]
    [TopologicalSpace F] (L : (σ → ℂ) →L[ℂ] F) (v : σ → ℂ) :
    L v = ∑ i, v i • L (fun j => if i = j then 1 else 0) :=
  LinearMap.pi_apply_eq_sum_univ (L : (σ → ℂ) →ₗ[ℂ] F) v

theorem roots_near_centred {E : Type*} [TopologicalSpace E] {n : ℕ} (b : Fin n → E → ℂ) (y₀ : E) (u : ℂ)
    (hb : ∀ j, ContinuousAt (b j) y₀) (h0 : ∀ T : ℂ, T ^ n + ∑ j, b j y₀ * T ^ (j : ℕ) = (T - u) ^ n)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ y in 𝓝 y₀, ∀ x : ℂ, x ^ n + ∑ j, b j y * x ^ (j : ℕ) = 0 → ‖x - u‖ < ε := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    exact Eventually.of_forall fun y x hx => by simp at hx
  set S : E → ℝ := fun y => ∑ j, ‖b j y‖ with hS
  set B : ℝ := max 1 (S y₀ + 1) with hB
  have hB1 : 1 ≤ B := le_max_left _ _
  have hSt : Tendsto S (𝓝 y₀) (𝓝 (S y₀)) :=
    tendsto_finsetSum _ fun j _ => (hb j).tendsto.norm
  have hDt : Tendsto (fun y => ∑ j, ‖b j y₀ - b j y‖ * B ^ (j : ℕ)) (𝓝 y₀) (𝓝 0) := by
    have : Tendsto (fun y => ∑ j, ‖b j y₀ - b j y‖ * B ^ (j : ℕ)) (𝓝 y₀)
        (𝓝 (∑ j : Fin n, ‖b j y₀ - b j y₀‖ * B ^ (j : ℕ))) :=
      tendsto_finsetSum _ fun j _ => ((tendsto_const_nhds.sub (hb j).tendsto).norm).mul_const _
    simpa using this
  have hεn : (0 : ℝ) < ε ^ n := pow_pos hε n
  filter_upwards [hSt.eventually (gt_mem_nhds (lt_add_one (S y₀))), hDt.eventually (gt_mem_nhds hεn)]
    with y hSy hDy x hx
  have hxB : ‖x‖ ≤ B := by
    by_cases hx1 : ‖x‖ ≤ 1
    · exact hx1.trans hB1
    replace hx1 := lt_of_not_ge hx1
    have hxn : x ^ n = -∑ j, b j y * x ^ (j : ℕ) := eq_neg_of_add_eq_zero_left hx
    have hle : ‖x‖ ^ n ≤ S y * ‖x‖ ^ (n - 1) := by
      calc ‖x‖ ^ n = ‖∑ j, b j y * x ^ (j : ℕ)‖ := by rw [← norm_pow, hxn, norm_neg]
        _ ≤ ∑ j, ‖b j y * x ^ (j : ℕ)‖ := norm_sum_le _ _
        _ ≤ ∑ j : Fin n, ‖b j y‖ * ‖x‖ ^ (n - 1) := by
          refine Finset.sum_le_sum fun j _ => ?_
          rw [norm_mul, norm_pow]
          exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hx1.le (by omega)) (norm_nonneg _)
        _ = S y * ‖x‖ ^ (n - 1) := by rw [hS, Finset.sum_mul]
    have hpos : 0 < ‖x‖ ^ (n - 1) := pow_pos (zero_lt_one.trans hx1) _
    have : ‖x‖ * ‖x‖ ^ (n - 1) ≤ S y * ‖x‖ ^ (n - 1) := by
      rw [← pow_succ', Nat.sub_add_cancel hn]; exact hle
    have hxS : ‖x‖ ≤ S y := le_of_mul_le_mul_right this hpos
    exact hxS.trans (hSy.le.trans (le_max_right _ _))
  have hid : (x - u) ^ n = ∑ j, (b j y₀ - b j y) * x ^ (j : ℕ) := by
    rw [← h0 x]
    have : x ^ n = -∑ j, b j y * x ^ (j : ℕ) := eq_neg_of_add_eq_zero_left hx
    rw [this]
    simp only [sub_mul, Finset.sum_sub_distrib]
    ring
  have hle : ‖x - u‖ ^ n ≤ ∑ j, ‖b j y₀ - b j y‖ * B ^ (j : ℕ) := by
    calc ‖x - u‖ ^ n = ‖∑ j, (b j y₀ - b j y) * x ^ (j : ℕ)‖ := by rw [← norm_pow, hid]
      _ ≤ ∑ j, ‖(b j y₀ - b j y) * x ^ (j : ℕ)‖ := norm_sum_le _ _
      _ ≤ ∑ j : Fin n, ‖b j y₀ - b j y‖ * B ^ (j : ℕ) := by
        refine Finset.sum_le_sum fun j _ => ?_
        rw [norm_mul, norm_pow]
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hxB _) (norm_nonneg _)
  have : ‖x - u‖ ^ n < ε ^ n := hle.trans_lt hDy
  exact lt_of_pow_lt_pow_left₀ n hε.le this

theorem proof (hMin : GermMinimalPolynomialDivides.Statement) (hCen : FiniteFibreCentredEquation.Statement)
    (hRem : PrimitiveFormRemainder.Statement) : PrimitiveFormMinimalFactorPoints.Statement := by
  classical
  intro σ _ Y w d A hX hirr hiso hinj ℓ N a δ q ha hδ hq hδne hp hsep hrel
  obtain ⟨n, b, hb, hmX, hdiv⟩ := hMin σ Y w d A hX hirr hiso hinj ℓ (ℓ.analyticAt w)
  choose nW cW hcW hcW0 hWX using fun i : σ =>
    hCen σ Y w d A hX hiso (fun z => z i) ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : σ => ℂ) i).analyticAt w)
  obtain ⟨V, K, f, hVo, hwV, hf, hXV⟩ := hX
  choose M R hR hRz using fun k : Fin K => hRem σ w d A ℓ N δ q nW cW (f k) hδ hq hcW hcW0 (hf k w hwV)
  set ev : (Fin d → ℂ) → ((Fin d → ℂ) → ℂ) →+* ℂ := fun y => Pi.evalRingHom (fun _ : Fin d → ℂ => ℂ) y with hev
  have hevC : ∀ y (g : (Fin d → ℂ) → ℂ), ev y g = g y := fun _ _ => rfl
  set e : σ → σ → ℂ := fun i j => if i = j then 1 else 0 with he

  set Q : σ → Polynomial ((Fin d → ℂ) → ℂ) := fun i => ∑ j, C (q i j) * X ^ (j : ℕ) with hQdef
  have hQ : ∀ i, Q i ∈ liftsRing (anSub (A w)).subtype := fun i =>
    Subring.sum_mem _ fun j _ => Subring.mul_mem _ (C_mem (hq i j)) (Subring.pow_mem _ (X_mem _) _)
  have hQe : ∀ i y t, (Q i).eval₂ (ev y) t = ∑ j, q i j y * t ^ (j : ℕ) := by
    intro i y t; simp [hQdef, eval₂_finsetSum, hevC]
  have hproj : ∀ r : Fin d, AnalyticAt ℂ (fun y : Fin d → ℂ => y r) (A w) := fun r =>
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin d => ℂ) r).analyticAt _
  set Ep : Polynomial ((Fin d → ℂ) → ℂ) := X ^ N + ∑ j, C (a j) * X ^ (j : ℕ) with hEp
  set EA : Fin d → Polynomial ((Fin d → ℂ) → ℂ) := fun r =>
    ∑ i, C (fun _ => A (e i) r) * Q i - C (fun y => δ y * y r) with hEA
  set El : Polynomial ((Fin d → ℂ) → ℂ) := ∑ i, C (fun _ => ℓ (e i)) * Q i - C δ * X with hEl
  set EW : σ → Polynomial ((Fin d → ℂ) → ℂ) := fun i =>
    Q i ^ nW i + ∑ j, C (fun y => cW i j y * δ y ^ (nW i - j)) * Q i ^ (j : ℕ) with hEW
  have hEpc : Ep ∈ liftsRing (anSub (A w)).subtype :=
    Subring.add_mem _ (Subring.pow_mem _ (X_mem _) _)
      (Subring.sum_mem _ fun j _ => Subring.mul_mem _ (C_mem (ha j)) (Subring.pow_mem _ (X_mem _) _))
  have hEAc : ∀ r, EA r ∈ liftsRing (anSub (A w)).subtype := fun r =>
    Subring.sub_mem _ (Subring.sum_mem _ fun i _ => Subring.mul_mem _ (C_mem analyticAt_const) (hQ i))
      (C_mem (hδ.mul (hproj r)))
  have hElc : El ∈ liftsRing (anSub (A w)).subtype :=
    Subring.sub_mem _ (Subring.sum_mem _ fun i _ => Subring.mul_mem _ (C_mem analyticAt_const) (hQ i))
      (Subring.mul_mem _ (C_mem hδ) (X_mem _))
  have hEWc : ∀ i, EW i ∈ liftsRing (anSub (A w)).subtype := fun i =>
    Subring.add_mem _ (Subring.pow_mem _ (hQ i) _) (Subring.sum_mem _ fun j _ =>
      Subring.mul_mem _ (C_mem ((hcW i j).mul (hδ.pow _))) (Subring.pow_mem _ (hQ i) _))

  have hEpe : ∀ y t, Ep.eval₂ (ev y) t = t ^ N + ∑ j, a j y * t ^ (j : ℕ) := by
    intro y t; simp [hEp, eval₂_finsetSum, hevC]
  have hEAe : ∀ r y t, (EA r).eval₂ (ev y) t = ∑ i, A (e i) r * ∑ j, q i j y * t ^ (j : ℕ) - δ y * y r := by
    intro r y t; simp [hEA, eval₂_finsetSum, hevC, hQe]
  have hEle : ∀ y t, El.eval₂ (ev y) t = ∑ i, ℓ (e i) * ∑ j, q i j y * t ^ (j : ℕ) - δ y * t := by
    intro y t; simp [hEl, eval₂_finsetSum, hevC, hQe]
  have hEWe : ∀ i y t, (EW i).eval₂ (ev y) t = (∑ j, q i j y * t ^ (j : ℕ)) ^ nW i +
      ∑ j : Fin (nW i), cW i j y * δ y ^ (nW i - j) * (∑ j, q i j y * t ^ (j : ℕ)) ^ (j : ℕ) := by
    intro i y t; simp [hEW, eval₂_finsetSum, hevC, hQe, eval₂_pow]
  have hAsum : ∀ (v : σ → ℂ) r, A v r = ∑ i, v i * A (e i) r := by
    intro v r; rw [linear_apply_eq_sum A v]; simp [Finset.sum_apply, he]
  have hlsum : ∀ v : σ → ℂ, ℓ v = ∑ i, v i * ℓ (e i) := by
    intro v; rw [linear_apply_eq_sum ℓ v]; simp [he]

  have hrelA : ∀ᶠ z in 𝓝 w, z ∈ Y → ∀ i, δ (A z) * z i = ∑ j, q i j (A z) * ℓ z ^ (j : ℕ) := by
    filter_upwards [eventually_all.2 hrel] with z hz hzX i using hz i hzX
  have hWA : ∀ᶠ z in 𝓝 w, z ∈ Y → ∀ i, z i ^ nW i + ∑ j, cW i j (A z) * z i ^ (j : ℕ) = 0 := by
    filter_upwards [eventually_all.2 hWX] with z hz hzX i using hz i hzX
  have dEp := hdiv Ep (coeff_analyticAt hEpc) (by
    filter_upwards [hp] with z hz hzX; rw [hEpe]; exact hz hzX)
  have dEA := fun r => hdiv (EA r) (coeff_analyticAt (hEAc r)) (by
    filter_upwards [hrelA] with z hz hzX
    rw [hEAe, Finset.sum_congr rfl fun i _ => by rw [← hz hzX i], hAsum z r, Finset.mul_sum,
      ← Finset.sum_sub_distrib]
    exact Finset.sum_eq_zero fun i _ => by ring)
  have dEl := hdiv El (coeff_analyticAt hElc) (by
    filter_upwards [hrelA] with z hz hzX
    rw [hEle, Finset.sum_congr rfl fun i _ => by rw [← hz hzX i]]
    rw [hlsum z, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_eq_zero fun i _ => by ring)
  have dEW := fun i => hdiv (EW i) (coeff_analyticAt (hEWc i)) (by
    filter_upwards [hrelA, hWA] with z hz hzW hzX
    rw [hEWe, ← hz hzX i, cleared_eq, hzW hzX i, mul_zero])
  have dR := fun k => hdiv (R k) (hR k) (by
    filter_upwards [hRz k, hrelA, hWA, hVo.mem_nhds hwV] with z h1 hz hzW hzV hzX
    have hz0 : z ∈ {z | z ∈ V ∧ ∀ i, f i z = 0} := by rw [← hXV]; exact ⟨hzX, hzV⟩
    rw [← h1 (hzW hzX) (hz hzX), hz0.2 k, mul_zero])
  refine ⟨n, b, hb, hmX, ?_, ?_⟩
  · filter_upwards [hsep, dEp] with y hs hd hδy
    refine (hs hδy).of_dvd ?_
    set_option synthInstance.maxHeartbeats 100000 in
      simpa [hEp, Polynomial.map_add (f := _), Polynomial.map_sum, hevC] using hd
  intro U hU
  have hO : ∀ᶠ z in 𝓝 w, z ∈ U ∧ z ∈ V ∧ ∀ k, (∀ i, z i ^ nW i + ∑ j, cW i j (A z) * z i ^ (j : ℕ) = 0) →
      (∀ i, δ (A z) * z i = ∑ j, q i j (A z) * ℓ z ^ (j : ℕ)) →
      δ (A z) ^ M k * f k z = (R k).eval₂ (Pi.evalRingHom (fun _ : Fin d → ℂ => ℂ) (A z)) (ℓ z) :=
    by filter_upwards [hU, hVo.mem_nhds hwV, eventually_all.2 hRz] with z h1 h2 h3 using ⟨h1, h2, h3⟩
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hO
  have hnear := fun i => roots_near_centred (cW i) (A w) (w i) (fun j => (hcW i j).continuousAt) (hcW0 i) hε
  filter_upwards [eventually_all.2 hnear, eventually_all.2 dEA, dEl, eventually_all.2 dEW,
    eventually_all.2 dR] with y hny hAy hly hWy hRy hδy τ hτ
  set φ : σ → ℂ := fun i => (∑ j, q i j y * τ ^ (j : ℕ)) / δ y with hφ
  have hQφ : ∀ i, ∑ j, q i j y * τ ^ (j : ℕ) = δ y * φ i := fun i => by
    rw [hφ]; field_simp
  have hAφ : A φ = y := by
    funext r
    have h0 := eval₂_eq_zero_of_dvd (hAy r) hτ
    rw [hEAe, sub_eq_zero] at h0
    rw [hAsum φ r]
    apply mul_left_cancel₀ hδy
    rw [← h0, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [hQφ i]; ring
  have hlφ : ℓ φ = τ := by
    have h0 := eval₂_eq_zero_of_dvd hly hτ
    rw [hEle, sub_eq_zero] at h0
    rw [hlsum φ]
    apply mul_left_cancel₀ hδy
    rw [← h0, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [hQφ i]; ring
  have hWφ : ∀ i, φ i ^ nW i + ∑ j, cW i j y * φ i ^ (j : ℕ) = 0 := by
    intro i
    have h0 := eval₂_eq_zero_of_dvd (hWy i) hτ
    rw [hEWe, hQφ i, cleared_eq] at h0
    exact (mul_eq_zero.1 h0).resolve_left (pow_ne_zero _ hδy)
  have hdist : dist φ w < ε := by
    rw [dist_pi_lt_iff hε]
    intro i
    rw [dist_eq_norm]
    exact hny i (φ i) (hWφ i)
  obtain ⟨hφU, hφV, hφR⟩ := hball hdist
  have hfk : ∀ k, f k φ = 0 := by
    intro k
    have h1 := hφR k (by rw [hAφ]; exact hWφ) (by intro i; rw [hAφ, hlφ, hQφ i])
    rw [hAφ, hlφ, eval₂_eq_zero_of_dvd (hRy k) hτ] at h1
    exact (mul_eq_zero.1 h1).resolve_left (pow_ne_zero _ hδy)
  have hφX : φ ∈ Y ∩ V := by rw [hXV]; exact ⟨hφV, hfk⟩
  exact ⟨⟨hφX.1, hφU⟩, hAφ, hlφ⟩

end PrimitiveFormMinimalFactorPoints

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSheetOnlyNull
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets

noncomputable section

namespace SheetOnlyNull

variable {n d : ℕ}

theorem injective_iff_det_ne_zero (L : (Fin d → ℂ) →L[ℂ] (Fin d → ℂ)) :
    Function.Injective L ↔ LinearMap.det (L : (Fin d → ℂ) →ₗ[ℂ] (Fin d → ℂ)) ≠ 0 := by
  rw [← isUnit_iff_ne_zero, ← LinearMap.isUnit_iff_isUnit_det, LinearMap.isUnit_iff_ker_eq_bot,
    LinearMap.ker_eq_bot]
  rfl

theorem finrank_real_fin_complex (d : ℕ) : Module.finrank ℝ (Fin d → ℂ) = 2 * d := by
  rw [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    Complex.finrank_real_complex, smul_eq_mul, mul_comm]

theorem differentiableOn_mulVec {m : ℕ} (B : Matrix (Fin m) (Fin n) ℂ) {U : Set (Fin d → ℂ)}
    {s : (Fin d → ℂ) → Fin n → ℂ} (hs : DifferentiableOn ℂ s U) :
    DifferentiableOn ℂ (fun w => B *ᵥ s w) U :=
  (LinearMap.toContinuousLinearMap B.mulVecLin).differentiable.comp_differentiableOn hs

theorem analyticOnNhd_of_differentiableOn {m : ℕ} {U : Set (Fin d → ℂ)}
    {F : (Fin d → ℂ) → Fin m → ℂ} (hU : IsOpen U) (hF : DifferentiableOn ℂ F U) :
    AnalyticOnNhd ℂ F U := fun w hw =>
  AnalyticAt.pi fun i => ReciprocityTheory.AnForm.Osgood.osgood d U (fun z => F z i) hU
    (differentiableOn_pi.1 hF i) w hw

theorem analyticOnNhd_det_jacC {U : Set (Fin d → ℂ)} {F : (Fin d → ℂ) → Fin d → ℂ}
    (hU : IsOpen U) (hF : DifferentiableOn ℂ F U) :
    AnalyticOnNhd ℂ (fun w => (ReciprocityTheory.AnForm.A.jacC F w).det) U := by
  intro w hw
  have hF' := (analyticOnNhd_of_differentiableOn hU hF).fderiv w hw
  have hent : ∀ a k, AnalyticAt ℂ (fun z => ReciprocityTheory.AnForm.A.jacC F z a k) w := fun a k => by
    show AnalyticAt ℂ (fun z => fderiv ℂ F z (Pi.single k 1) a) w
    exact (((ContinuousLinearMap.proj a).comp
      (ContinuousLinearMap.apply ℂ (Fin d → ℂ) (Pi.single k (1 : ℂ)))).analyticAt _).comp hF'
  simp only [Matrix.det_apply']
  exact Finset.analyticAt_fun_sum _ fun σ _ => analyticAt_const.mul
    (Finset.analyticAt_fun_prod _ fun i _ => hent _ _)

theorem exists_sheet_nhds {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin d) (Fin n) ℂ}
    (x : Fin n → ℂ) :
    ∃ (s : (Fin d → ℂ) → Fin n → ℂ) (U : Set (Fin d → ℂ)) (W : Set (Fin n → ℂ)),
      IsOpen U ∧ IsOpen W ∧ DifferentiableOn ℂ s U ∧
      (∀ x' ∈ zeroSet J ∩ W, A *ᵥ x' ∈ U ∧ IsSheetAt J A x' s) ∧
      ((∃ s, IsSheetAt J A x s) → x ∈ W) := by
  by_cases hx : ∃ s, IsSheetAt J A x s
  · obtain ⟨s, U, hU, hxU, hsd, hsx, hsec, V, hV, hVs⟩ := hx
    have hAc : Continuous fun z : Fin n → ℂ => A *ᵥ z := by fun_prop
    refine ⟨s, U, interior V ∩ (fun z => A *ᵥ z) ⁻¹' U, hU,
      isOpen_interior.inter (hU.preimage hAc), hsd, ?_, fun _ =>
        ⟨mem_interior_iff_mem_nhds.2 hV, hxU⟩⟩
    rintro x' ⟨hx'Z, hx'V, hx'U⟩
    have hx's : s (A *ᵥ x') = x' := (hVs x' ⟨hx'Z, interior_subset hx'V⟩ hx'U).symm
    exact ⟨hx'U, U, hU, hx'U, hsd, hx's, hsec, interior V, isOpen_interior.mem_nhds hx'V,
      fun x'' hx'' hAx'' => hVs x'' ⟨hx''.1, interior_subset hx''.2⟩ hAx''⟩
  · exact ⟨fun _ => x, ∅, ∅, isOpen_empty, isOpen_empty, differentiableOn_empty,
      by simp, fun h => absurd h hx⟩

theorem exists_sheet_of_det_ne_zero {J : Ideal (MvPolynomial (Fin n) ℂ)}
    {A A' : Matrix (Fin d) (Fin n) ℂ} {x : Fin n → ℂ} {s : (Fin d → ℂ) → Fin n → ℂ}
    (hs : IsSheetAt J A x s)
    (hdet : (ReciprocityTheory.AnForm.A.jacC (fun w => A' *ᵥ s w) (A *ᵥ x)).det ≠ 0) :
    ∃ s', IsSheetAt J A' x s' := by
  obtain ⟨U, hU, hyU, hsd, hsx, hsec, V, hV, hVs⟩ := hs
  set F : (Fin d → ℂ) → Fin d → ℂ := fun w => A' *ᵥ s w with hFdef
  have hFa := analyticOnNhd_of_differentiableOn hU (differentiableOn_mulVec A' hsd)
  set G : Set (Fin d → ℂ) := U ∩ (fun w => (ReciprocityTheory.AnForm.A.jacC F w).det) ⁻¹' {0}ᶜ with hGdef
  have hG : IsOpen G := (analyticOnNhd_det_jacC hU (differentiableOn_mulVec A' hsd)).continuousOn
    |>.isOpen_inter_preimage hU isOpen_compl_singleton
  have hinj : ∀ w, (ReciprocityTheory.AnForm.A.jacC F w).det ≠ 0 → Function.Injective (fderiv ℂ F w) :=
    fun w hw => (injective_iff_det_ne_zero _).2 (by rwa [← ReciprocityTheory.AnForm.A.det_jacC])
  have hequiv : ∀ w ∈ G, ∃ e : (Fin d → ℂ) ≃L[ℂ] (Fin d → ℂ),
      HasStrictFDerivAt F (e : (Fin d → ℂ) →L[ℂ] (Fin d → ℂ)) w := by
    intro w hw
    refine ⟨(LinearEquiv.ofInjectiveEndo _ (hinj w hw.2)).toContinuousLinearEquiv, ?_⟩
    exact (hFa w hw.1).hasStrictFDerivAt.congr_fderiv (ContinuousLinearMap.ext fun v => rfl)
  obtain ⟨e, he⟩ := hequiv _ ⟨hyU, hdet⟩
  set φ := he.toOpenPartialHomeomorph F with hφdef
  have hφ : ∀ w, φ w = F w := fun w => by rw [hφdef, HasStrictFDerivAt.toOpenPartialHomeomorph_coe]
  have hysrc : A *ᵥ x ∈ φ.source := he.mem_toOpenPartialHomeomorph_source
  have hFx : F (A *ᵥ x) = A' *ᵥ x := by simp only [hFdef, hsx]
  have hsym : φ.symm (A' *ᵥ x) = A *ᵥ x := by rw [← hFx, ← hφ, φ.left_inv hysrc]
  refine ⟨s ∘ φ.symm, φ.target ∩ φ.symm ⁻¹' G, φ.isOpen_inter_preimage_symm hG,
    ⟨by rw [← hFx, ← hφ]; exact φ.map_source hysrc, by rw [Set.mem_preimage, hsym]; exact ⟨hyU, hdet⟩⟩,
    ?_, by simp only [Function.comp_apply, hsym, hsx], fun z hz => ⟨?_, (hsec _ hz.2.1).2⟩, ?_⟩
  · intro z ⟨hzT, hzG⟩
    obtain ⟨e', he'⟩ := hequiv _ hzG
    have hsymd : HasFDerivAt φ.symm _ z :=
      φ.hasFDerivAt_symm hzT (f' := e') (by
        have : (φ : (Fin d → ℂ) → Fin d → ℂ) = F := funext hφ
        rw [this]; exact he'.hasFDerivAt)
    exact ((hsd.differentiableAt (hU.mem_nhds hzG.1)).comp z
      hsymd.differentiableAt).differentiableWithinAt
  · show F (φ.symm z) = z
    rw [← hφ, φ.right_inv hz.1]
  · refine ⟨V ∩ (fun z => A *ᵥ z) ⁻¹' (φ.source ∩ U), inter_mem hV
      (((φ.open_source.inter hU).preimage (by fun_prop)).mem_nhds ⟨hysrc, hyU⟩), ?_⟩
    rintro x'' ⟨hx''Z, hx''V, hx''src, hx''U⟩ -
    have hx'' : x'' = s (A *ᵥ x'') := hVs x'' ⟨hx''Z, hx''V⟩ hx''U
    have hA' : A' *ᵥ x'' = φ (A *ᵥ x'') := by rw [hφ, hFdef]; exact congrArg _ hx''
    rw [Function.comp_apply, hA', φ.left_inv hx''src]
    exact hx''

theorem exists_det_ne_zero (h₁ : IndefiniteRowSideFullHecke.ComplexSets.FiniteMapOpen.Statement)
    (h₂ : IndefiniteRowSideFullHecke.ComplexSets.CriticalImageNull.Statement) {J : Ideal (MvPolynomial (Fin n) ℂ)}
    {A A' : Matrix (Fin d) (Fin n) ℂ} (hJ : J.IsPrime) (hA' : IsFiniteProjection J A')
    {x : Fin n → ℂ} {s : (Fin d → ℂ) → Fin n → ℂ} (hs : IsSheetAt J A x s)
    {W₀ : Set (Fin d → ℂ)} (hW₀ : IsOpen W₀) (hxW₀ : A *ᵥ x ∈ W₀) :
    ∃ w ∈ W₀, (ReciprocityTheory.AnForm.A.jacC (fun w => A' *ᵥ s w) w).det ≠ 0 := by
  obtain ⟨U, hU, hyU, hsd, hsx, hsec, V, hV, hVs⟩ := hs
  set F : (Fin d → ℂ) → Fin d → ℂ := fun w => A' *ᵥ s w with hFdef
  by_contra hall
  push Not at hall
  have hcrit : F '' (W₀ ∩ U) ⊆ F '' {w | w ∈ U ∧ ¬ Function.Injective (fderiv ℂ F w)} :=
    Set.image_mono fun w hw => ⟨hw.2, fun hinj => (injective_iff_det_ne_zero _).1 hinj
      (by rw [← ReciprocityTheory.AnForm.A.det_jacC]; exact hall w hw.1)⟩
  have hnull := measure_mono_null hcrit (h₂ d d U F hU (differentiableOn_mulVec A' hsd))
  have hxZ : x ∈ zeroSet J := hsx ▸ (hsec _ hyU).2
  have hAc : Continuous fun z : Fin n → ℂ => A *ᵥ z := by fun_prop
  have hnhds := h₁ n d J (linPoly A') hJ hA'.injective hA'.finite x hxZ
    (V ∩ (fun z => A *ᵥ z) ⁻¹' (W₀ ∩ U))
    (inter_mem hV (((hW₀.inter hU).preimage hAc).mem_nhds ⟨hxW₀, hyU⟩))
  have hev : ∀ z : Fin n → ℂ, (fun i => eval z (linPoly A' i)) = A' *ᵥ z := fun z => by
    ext i
    simp [linPoly, Matrix.mulVec, dotProduct]
  simp only [hev] at hnhds
  have hsub : (fun z => A' *ᵥ z) '' (IndefiniteRowSideFullHecke.ComplexSets.zeroLocus J ∩
      (V ∩ (fun z => A *ᵥ z) ⁻¹' (W₀ ∩ U))) ⊆ F '' (W₀ ∩ U) := by
    rintro _ ⟨z, ⟨hzZ, hzV, hzW⟩, rfl⟩
    refine ⟨A *ᵥ z, hzW, ?_⟩
    simp only [hFdef]
    rw [← hVs z ⟨hzZ, hzV⟩ hzW.2]
  have hpos := Measure.measure_pos_of_mem_nhds (μ := μH[(Module.finrank ℝ (Fin d → ℂ) : ℝ)])
    (Filter.mem_of_superset hnhds hsub)
  rw [finrank_real_fin_complex] at hpos
  exact hpos.ne' hnull

end SheetOnlyNull

theorem SheetOnlyNull.proof (h₁ : IndefiniteRowSideFullHecke.ComplexSets.FiniteMapOpen.Statement)
    (h₂ : IndefiniteRowSideFullHecke.ComplexSets.CriticalImageNull.Statement) : SheetOnlyNull.Statement := by
  intro n d J A A' hJ _ _ hA'
  set B := {x | x ∈ zeroSet J ∧ (∃ s, IsSheetAt J A x s) ∧ ¬ ∃ s', IsSheetAt J A' x s'} with hBdef
  choose σ U W hU hW hσd hWsh hxW using
    fun x : Fin n → ℂ => SheetOnlyNull.exists_sheet_nhds (J := J) (A := A) x
  obtain ⟨T, hTc, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable W hW
  have hpiece : ∀ i, volume ((fun x => A *ᵥ x) '' (B ∩ W i)) = 0 := by
    intro i
    apply ReciprocityTheory.AnForm.volume_eq_zero_of_locally_in_analytic_zero_set
    rintro _ ⟨x, ⟨hxB, hxWi⟩, rfl⟩
    obtain ⟨hAx, hsh⟩ := hWsh i x ⟨hxB.1, hxWi⟩
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp (hU i) _ hAx
    refine ⟨Metric.ball (A *ᵥ x) r, Metric.isOpen_ball, Metric.mem_ball_self hr,
      (convex_ball _ r).isPreconnected,
      fun w => (ReciprocityTheory.AnForm.A.jacC (fun v => A' *ᵥ σ i v) w).det,
      (SheetOnlyNull.analyticOnNhd_det_jacC (hU i)
        (SheetOnlyNull.differentiableOn_mulVec A' (hσd i))).mono hball,
      SheetOnlyNull.exists_det_ne_zero h₁ h₂ hJ hA' hsh Metric.isOpen_ball (Metric.mem_ball_self hr),
      ?_⟩
    rintro _ ⟨⟨x'', ⟨hx''B, hx''W⟩, rfl⟩, -⟩
    by_contra hne
    exact hx''B.2.2 (SheetOnlyNull.exists_sheet_of_det_ne_zero (hWsh i x'' ⟨hx''B.1, hx''W⟩).2 hne)
  refine measure_mono_null ?_ ((measure_biUnion_null_iff hTc).2 fun i _ => hpiece i)
  rintro _ ⟨x, hxB, rfl⟩
  have hx : x ∈ ⋃ i ∈ T, W i := hTU ▸ Set.mem_iUnion.2 ⟨x, hxW x hxB.2.1⟩
  obtain ⟨i, hiT, hxi⟩ := Set.mem_iUnion₂.1 hx
  exact Set.mem_biUnion hiT ⟨x, ⟨hxB, hxi⟩, rfl⟩

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PStokesOnVariety
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff

theorem StokesOnVariety.proof (hD : ComplexSets.DiscriminantCover.Statement)
    (hS : StokesOffDiscriminant.Statement) (hL : CutOffLimit.Statement) :
    StokesOnVariety.Statement := by
  have key : ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (f g : (Fin n → ℂ) → ℝ)
      (φ : Fin d → (Fin n → ℂ) → ℝ), J.IsPrime →
      ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d + 1 : ℕ) →
      SmoothNear (zeroSet J) f → SmoothNear (zeroSet J) g → (∀ i, SmoothNear (zeroSet J) (φ i)) →
      HasCompactSupport f → varInt J (d + 1) f (vecCons g φ) = varInt J (d + 1) g (vecCons f φ) := by
    intro n d J f g φ hJ hdim hf hg hφ hc
    unfold varInt
    split_ifs with hA
    · have hAf := hA.choose_spec
      generalize hA.choose = A at hAf ⊢
      obtain ⟨P, hP0, hPcov⟩ := hD n (d + 1) J A hJ hdim hAf

      have hsheet : ∀ x ∈ zeroSet J, eval (A *ᵥ x) P ≠ 0 → ∃ s, IsSheetAt J A x s := by
        intro x hx hPx
        obtain ⟨-, -, hloc⟩ := hPcov (A *ᵥ x) hPx
        obtain ⟨U, V, s, hU, hyU, hV, hxV, hs, hsy, hAs, hZV⟩ := hloc x ⟨hx, rfl⟩
        refine ⟨s, U, hU, hyU, hs, hsy, fun w hw => ⟨hAs w hw, ?_⟩, V, hV.mem_nhds hxV, ?_⟩
        · have hw' : s w ∈ zeroSet J ∩ V := hZV ▸ Set.mem_image_of_mem s hw
          exact hw'.1
        · rintro x' hx' -
          rw [hZV] at hx'
          obtain ⟨w, hw, rfl⟩ := hx'
          rw [hAs w hw]
      obtain ⟨χ, hχs, hχU, hlim⟩ := hL n d J A P hJ hdim hAf hP0
      obtain ⟨h1, h2⟩ := hlim f g φ hf hg hφ hc
      refine tendsto_nhds_unique h1 (Tendsto.congr (fun k => ?_) h2)
      obtain ⟨U, hU, hDU, hχ0⟩ := hχU k
      obtain ⟨V, hV, hZV, hfV⟩ := hf
      have hcχ : HasCompactSupport (fun x => χ k x * f x) := hc.mul_left (f := χ k)
      refine (hS n d J A P hJ hdim hAf hP0 hsheet (fun x => χ k x * f x) g φ
        ⟨V, hV, hZV, (hχs k).contDiffOn.mul hfV⟩ hg hφ hcχ ⟨U, hU, hDU, fun x hx => ?_⟩).symm
      rw [hχ0 x hx, zero_mul]
    · rfl
  intro n d J f g φ hJ hdim hf hg hφ hc
  rcases hc with hc | hc
  · exact key n d J f g φ hJ hdim hf hg hφ hc
  · exact (key n d J g f φ hJ hdim hg hf hφ hc).symm

end GroundTheory.Heights₂.Heights
end

