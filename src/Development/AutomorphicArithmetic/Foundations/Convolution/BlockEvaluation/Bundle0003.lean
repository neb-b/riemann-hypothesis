module

public import Development.AutomorphicArithmetic.Foundations.Convolution.BlockEvaluation.TruncSpec
public import Development.AutomorphicArithmetic.Foundations.Convolution.PolynomialCoefficientBounds.GenPiecesK
public import Development.AutomorphicArithmetic.Foundations.Convolution.PolynomialCoefficientBounds.Bundle0003
public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.Convolution.PolynomialCoefficientBounds.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.Convolution.PolynomialCoefficientBounds.Bundle0005

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.BlockEvaluation.SideEst
section
open MeasureTheory NumberField IsDedekindDomain MvPolynomial Filter Topology GroundTheory.Automorphic GroundTheory.Automorphic.Reduction UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Ci PositivityTheory.Rg.Fx PositivityTheory.Rg.Tf.Core

private theorem msOf_ex {K : Type} [Field K] [NumberField K] {n : ℕ} (Λ : (K →+* ℂ) → Multiset ℂ) (h : ∀ τ, (Λ τ).card = n) :
    ∃ L : Ix K n → ℂ, msOf L = Λ := by
  have : ∀ τ, ∃ f : Fin n → ℂ, Finset.univ.val.map f = Λ τ := by
    intro τ
    have h1 := h τ
    induction hm : Λ τ using Quotient.inductionOn with
    | _ a =>
      rw [hm] at h1
      have h2 : a.length = n := by simpa using h1
      subst h2
      exact ⟨a.get, by rw [Fin.univ_val_map, List.ofFn_get]; rfl⟩
  choose f hf using this
  exact ⟨fun x => f x.1 x.2, funext hf⟩

private theorem val_congr {K : Type} [Field K] [NumberField K] {n : ℕ} (S : Set (Pl K)) (x : ℝ) (Λ : (K →+* ℂ) → Multiset ℂ)
    (t t' : Pl K → Multiset ℂ) (h : ∀ w ∉ S, t w = t' w) (P : PR K n) (hP : ∀ y ∈ P.vars, y.1 ∉ S) :
    val x Λ t P = val x Λ t' P :=
  eval₂Hom_congr' rfl (fun i hi _ => by unfold hval; rw [h _ (hP i hi)]) rfl

private theorem arith (C w zN zi q r kM e B E1 E2 kk f g1 g2 : ℝ) (hw : 0 ≤ w) (hzN : 0 ≤ zN) (hzi : 0 ≤ zi) (hq : 0 ≤ q)
    (hr : 0 ≤ r) (hkM : 0 ≤ kM) (he : 0 ≤ e) (hB : 0 ≤ B) (hE1 : 0 ≤ E1) (hE2 : 0 ≤ E2) (hkk : 0 ≤ kk) (hf : 0 < f)
    (hg1 : 1 ≤ g1) (hg2 : 1 ≤ g2) (h1 : w * zN ≤ E1 * g1) (h2 : w * zi ≤ E2) (h3 : q ≤ B * e) (h4 : r ≤ B * e / f)
    (h5 : kM ≤ kk * g2) :
    C * w * (zN * (q + kM * r) + kM * zi * q) ≤ |C| * e * g1 * g2 * B * (E1 * (1 + kk / f) + kk * E2) := by
  have g1' : 0 ≤ g1 := zero_le_one.trans hg1
  have g2' : 0 ≤ g2 := zero_le_one.trans hg2
  have h2' : w * zi ≤ g1 * E2 := h2.trans (le_mul_of_one_le_left hE2 hg1)
  have h3' : q ≤ g2 * (B * e) := h3.trans (le_mul_of_one_le_left (by positivity) hg2)
  have hC := le_abs_self C
  calc _ = C * (w * zN * (q + kM * r) + kM * (w * zi) * q) := by ring
    _ ≤ |C| * (w * zN * (q + kM * r) + kM * (w * zi) * q) := mul_le_mul_of_nonneg_right hC (by positivity)
    _ ≤ |C| * (E1 * g1 * (g2 * (B * e) + kk * g2 * (B * e / f)) + kk * g2 * (g1 * E2) * (B * e)) := by gcongr
    _ = _ := by ring

set_option maxHeartbeats 1600000 in
theorem UpperTheory.ConvolutionTheory.Ci.sideEst :
    OneSide → EvVal → TruncSpec → ∀ (K : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] (n l : ℕ), 0 < n →
      ∀ (μ : Measure (normOneGL (K := K) (n := n))) [μ.IsHaarMeasure] (θ : Twist μ) (𝔰 : Side θ l) (ev : PR K n →+* (LL μ →L[ℂ] LL μ)),
      𝔰.toAmp.IsEv ev → (∀ P, Inner μ (ev P)) → ∀ C₀ : ℝ, ∃ c₁ : ℝ, ∀ η : ℝ, 0 < η → η ≤ 1 →
      ∀ χ : ℝ → ℝ, Continuous χ → (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) → (∀ x ≥ η, χ x = 1) →
      ∃ s : Finset (ℝ × Submodule ℂ (LL μ)),
        (∀ y, y ∈ s ↔ η < y.1 ∧ IsSummand μ y.2 ∧ y.2.map (θ.U : LL μ →ₗ[ℂ] LL μ) = y.2 ∧ eigIn y.2 𝔰.toAmp.A y.1 ≠ ⊥) ∧
        (∀ y ∈ s, FiniteDimensional ℂ (eigIn y.2 𝔰.toAmp.A y.1)) ∧
        ∀ Φ G, admitted 𝔰.S Φ → IsGen Φ G →
          (∃ C : ℝ, ∀ d : ℕ, ‖ev (trunc d G) ∘L fcalc χ 𝔰.toAmp.A ∘L (1 - Pc μ)‖ ≤ C ^ (d + 1) / d.factorial) →
          ∀ P : PR K n, (∀ y ∈ P.vars, y.1 ∉ 𝔰.S) → ∃ u : ℝ × Submodule ℂ (LL μ) → ℕ → ℂ,
            (∀ y ∈ s, ∀ (L : Ix K n → ℂ) t, At μ 𝔰.S y.2 (msOf L) t →
              Tendsto (u y) atTop (𝓝 (y.1 * val y.1 (msOf L) t P * evK L (hval t) Φ))) ∧
            ∀ (p : ℕ) (N : ℝ) (s₀ : ℕ), ∃ M : ℝ, 0 ≤ M ∧ ∀ (j d : ℕ), ∀ m ≤ s₀, ∀ m' ≤ s₀, ∀ f : TG K n,
              𝔰.Rep (ev (chebP η (j / p + m) * (trunc d G * P))) (j + m') (Real.exp (C₀ * ((j + m' : ℕ) : ℝ))) f →
              ‖twInt θ f - ∑ y ∈ s, u y d * (y.1 : ℂ) ^ d * (cheb η (j / p + m) y.1 : ℂ) *
                  trOn (eigIn y.2 𝔰.toAmp.A y.1) ((𝔰.Uq 0 ^ (j + m')) ∘L Rop μ 𝔰.g ∘L θ.U)‖ ≤
                M ^ (d + 1) * (Real.exp (c₁ * j) * (1 + (4 / η) ^ (j / p) / d.factorial) + (4 / η) ^ (j / p) * Real.exp (-N * j)) := by
  intro hOS hEV hTS K _ _ _ n l hn μ _ θ 𝔰 ev hev hin C₀
  classical
  obtain ⟨N, hN⟩ := hOS K n l hn μ θ 𝔰 ev hev hin
  obtain ⟨C, hC0, hC1⟩ : ∃ C : ℝ, C₀ ≤ C ∧ 1 ≤ C := ⟨max C₀ 1, le_max_left _ _, le_max_right _ _⟩
  obtain ⟨lu, hlu0, hlu⟩ : ∃ lu : ℝ, 0 ≤ lu ∧ ‖𝔰.Uq 0‖ ≤ Real.exp lu :=
    ⟨‖𝔰.Uq 0‖, norm_nonneg _, by linarith [Real.add_one_le_exp ‖𝔰.Uq 0‖]⟩
  refine ⟨N * C + lu, fun η hη hη1 χ hχ hχ1 hχ2 => ?_⟩
  obtain ⟨s, hs1, hs2, hs3⟩ := hN η hη hη1 χ hχ hχ1 hχ2
  refine ⟨s, hs1, hs2, fun Φ G hΦ hG hb P hP => ?_⟩
  obtain ⟨Cb, hCb⟩ := hb
  obtain ⟨⟨κ, D, hκ, hBd⟩, hu, hM⟩ := (hTS K n 𝔰.S Φ hΦ).2 G hG
  obtain ⟨Mt, hMt⟩ := hM _ ev hev.const
  have hE := fun y (hy : y ∈ s) => hEV K n hn μ 𝔰.toAmp y.2 y.1 (hη.trans ((hs1 y).1 hy).1) ((hs1 y).1 hy).2.1
  have hex : ∀ y : ℝ × Submodule ℂ (LL μ), ∃ (L : Ix K n → ℂ) (t : Pl K → Multiset ℂ), y ∈ s → At μ 𝔰.S y.2 (msOf L) t := by
    intro y
    by_cases hy : y ∈ s
    · obtain ⟨Λ, t, h⟩ := (hE y hy).1 ((hs1 y).1 hy).2.2.2
      obtain ⟨L, rfl⟩ := msOf_ex Λ fun τ => (h.1 τ).1
      exact ⟨L, t, fun _ => h⟩
    · exact ⟨0, 0, fun h => absurd h hy⟩
  choose L t hLt using hex
  choose u hu1 hu2 using hu
  have hT : ∀ d, ∀ y ∈ (trunc d G).vars, y.1 ∉ 𝔰.S := fun d y hy => hκ _ ((hBd d).1 y hy)
  refine ⟨fun y d => y.1 * val y.1 (msOf (L y)) (t y) P * u (L y) (t y) d, fun y hy L' t' h' => ?_, fun p N₁ s₀ => ?_⟩
  · obtain ⟨e1, e2⟩ := (hE y hy).2.1 _ _ _ _ (hLt y hy) h'
    have hy0 : (y.1 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (hη.trans ((hs1 y).1 hy).1).ne'
    have e3 : u (L y) (t y) = u L' t' := by
      funext d
      refine mul_left_cancel₀ (pow_ne_zero d hy0) ?_
      rw [← hu2, ← hu2, e1]
      exact val_congr 𝔰.S _ _ _ _ e2 _ (hT d)
    beta_reduce
    rw [e3, e1, val_congr 𝔰.S _ _ _ _ e2 P hP]
    exact (hu1 L' t').const_mul _
  obtain ⟨N', hN'⟩ := exists_nat_ge (max N₁ 0 + lu)
  obtain ⟨C₁, hC₁⟩ := hs3 N'
  have hk : 1 ≤ 4 / η := by rw [le_div_iff₀ hη]; linarith
  have hc₁ : 0 ≤ N * C + lu := by positivity
  obtain ⟨B, hB1, hB2, hB3⟩ : ∃ B : ℝ, 1 ≤ B ∧ |Mt| ≤ B ∧ |Cb| ≤ B :=
    ⟨max 1 (max |Mt| |Cb|), le_max_left _ _, (le_max_left _ _).trans (le_max_right _ _), (le_max_right _ _).trans (le_max_right _ _)⟩
  have hB0 : 0 ≤ B := zero_le_one.trans hB1
  obtain ⟨K0, hK0, hK1⟩ : ∃ K0 : ℝ, |C₁| * ‖ev P‖ * Real.exp ((N * C + lu) * s₀) * (4 / η) ^ s₀ ≤ K0 ∧ 1 ≤ K0 :=
    ⟨max _ 1, le_max_left _ _, le_max_right _ _⟩
  refine ⟨K0 * B, by positivity, fun j d m hm m' hm' f hf => ?_⟩
  have hJ0 : (0 : ℝ) ≤ ((j + m' : ℕ) : ℝ) := Nat.cast_nonneg _
  have hJ1 : (j : ℝ) ≤ ((j + m' : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_right j m'
  have hJ2 : ((j + m' : ℕ) : ℝ) ≤ j + s₀ := by exact_mod_cast Nat.add_le_add_left hm' j
  have hQv : ∀ y ∈ (trunc d G * P).vars, y.1 ∉ 𝔰.S := fun y hy => by
    rcases Finset.mem_union.1 (vars_mul _ _ hy) with h | h
    · exact hT d y h
    · exact hP y h
  have key := hC₁ (trunc d G * P) (fun y => val y.1 (msOf (L y)) (t y) (trunc d G * P))
    (fun y hy v hv => (hE y hy).2.2 ev hev _ _ (hLt y hy) _ hQv v hv) (j / p + m) (j + m')
    (Real.exp (C * ((j + m' : ℕ) : ℝ))) f (Real.one_le_exp (by positivity))
    ⟨hf.1, fun x hx => hf.2 x (lt_of_le_of_lt (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right hC0 hJ0)) hx)⟩
  have es : ∑ y ∈ s, y.1 * val y.1 (msOf (L y)) (t y) P * u (L y) (t y) d * (y.1 : ℂ) ^ d * (cheb η (j / p + m) y.1 : ℂ) *
        trOn (eigIn y.2 𝔰.toAmp.A y.1) ((𝔰.Uq 0 ^ (j + m')) ∘L Rop μ 𝔰.g ∘L θ.U) =
      ∑ y ∈ s, (cheb η (j / p + m) y.1 : ℂ) * (y.1 * val y.1 (msOf (L y)) (t y) (trunc d G * P) *
        trOn (eigIn y.2 𝔰.toAmp.A y.1) ((𝔰.Uq 0 ^ (j + m')) ∘L Rop μ 𝔰.g ∘L θ.U)) := by
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [map_mul, hu2]
    ring
  beta_reduce
  rw [es]
  refine key.trans ?_
  have hw : ‖𝔰.Uq 0‖ ^ (j + m') ≤ Real.exp (lu * ((j + m' : ℕ) : ℝ)) := by
    rw [mul_comm, Real.exp_nat_mul]
    exact pow_le_pow_left₀ (norm_nonneg _) hlu _
  have hdf : (0 : ℝ) < d.factorial := by exact_mod_cast d.factorial_pos
  have a1 : ‖𝔰.Uq 0‖ ^ (j + m') * Real.exp (C * ((j + m' : ℕ) : ℝ)) ^ N ≤
      Real.exp ((N * C + lu) * j) * Real.exp ((N * C + lu) * s₀) := by
    refine (mul_le_mul_of_nonneg_right hw (by positivity)).trans ?_
    rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    have := mul_le_mul_of_nonneg_left hJ2 hc₁
    linarith
  have a2 : ‖𝔰.Uq 0‖ ^ (j + m') * (Real.exp (C * ((j + m' : ℕ) : ℝ)) ^ N')⁻¹ ≤ Real.exp (-N₁ * j) := by
    refine (mul_le_mul_of_nonneg_right hw (by positivity)).trans ?_
    rw [← Real.exp_nat_mul, ← Real.exp_neg, ← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    have b1 : (N' : ℝ) * ((j + m' : ℕ) : ℝ) ≤ N' * (C * ((j + m' : ℕ) : ℝ)) :=
      mul_le_mul_of_nonneg_left (le_mul_of_one_le_left hJ0 hC1) (Nat.cast_nonneg _)
    have b2 := mul_le_mul_of_nonneg_right hN' hJ0
    have b3 := mul_le_mul_of_nonneg_left hJ1 (le_max_right N₁ 0)
    have b4 := mul_le_mul_of_nonneg_right (le_max_left N₁ 0) (Nat.cast_nonneg j : (0 : ℝ) ≤ j)
    linarith
  have pw : ∀ x : ℝ, |x| ≤ B → x ^ (d + 1) ≤ B ^ (d + 1) := fun x hx =>
    (le_abs_self _).trans (by rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) hx _)
  have a3 : ‖ev (trunc d G * P)‖ ≤ B ^ (d + 1) * ‖ev P‖ := by
    rw [map_mul]
    exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right ((hMt d).trans (pw _ hB2)) (norm_nonneg _))
  have a4 : ‖ev (trunc d G * P) ∘L fcalc χ 𝔰.toAmp.A ∘L (1 - Pc μ)‖ ≤ B ^ (d + 1) * ‖ev P‖ / d.factorial := by
    have e : ev (trunc d G * P) ∘L fcalc χ 𝔰.toAmp.A ∘L (1 - Pc μ) =
        ev P ∘L (ev (trunc d G) ∘L fcalc χ 𝔰.toAmp.A ∘L (1 - Pc μ)) := by
      rw [mul_comm, map_mul]
      rfl
    rw [e, mul_comm (B ^ (d + 1)), mul_div_assoc]
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_mul_of_nonneg_left ((hCb d).trans ?_) (norm_nonneg _))
    exact div_le_div_of_nonneg_right (pw _ hB3) hdf.le
  have a5 : (4 / η) ^ (j / p + m) ≤ (4 / η) ^ (j / p) * (4 / η) ^ s₀ := by
    rw [pow_add]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hk hm) (by positivity)
  refine (arith C₁ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (by positivity) (by positivity) (by positivity) (norm_nonneg _) (norm_nonneg _)
    (by positivity) (norm_nonneg _) (by positivity) (by positivity) (by positivity) (by positivity) hdf
    (Real.one_le_exp (by positivity)) (one_le_pow₀ hk) a1 a2 a3 a4 a5).trans ?_
  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
  rw [mul_pow]
  exact mul_le_mul_of_nonneg_right (hK0.trans (le_self_pow₀ hK1 (by omega))) (by positivity)
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.BlockEvaluation.TotalDegreeAevalLe
section
open Classical

open MeasureTheory NumberField IsDedekindDomain MvPolynomial Filter Topology GroundTheory.Automorphic GroundTheory.Automorphic.Reduction UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Ci PositivityTheory.Rg.Fx PositivityTheory.Rg.Tf.Core

private theorem totalDegree_aeval_le {σ : Type*} (q : MvPolynomial σ ℂ) (hq : q.totalDegree ≤ 1) (p : Polynomial ℂ) :
    (Polynomial.aeval q p).totalDegree ≤ p.natDegree := by
  rw [Polynomial.aeval_eq_sum_range]
  refine totalDegree_finsetSum_le fun i hi => ?_
  have hi' : i ≤ p.natDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  refine (totalDegree_smul_le _ _).trans ((totalDegree_pow _ _).trans ?_)
  calc
    i * q.totalDegree ≤ i * 1 := Nat.mul_le_mul_left _ hq
    _ ≤ p.natDegree := by simpa using hi'

private theorem exists_fin_map (n : ℕ) (s : Multiset ℂ) (hs : s.card = n) :
    ∃ f : Fin n → ℂ, (Finset.univ : Finset (Fin n)).val.map f = s := by
  subst hs
  induction s using Quotient.inductionOn with
  | h l =>
    refine ⟨fun i => l.get (Fin.cast (by simp) i), ?_⟩
    rw [Fin.univ_val_map]
    refine congrArg _ ?_
    apply List.ext_get <;> simp

theorem UpperTheory.ConvolutionTheory.Ci.bdLem :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (κ κ' : Finset (Pl K)) (D D' d d' : ℕ) (R R' : PR K n),
      (Bd κ D d R → Bd κ' D' d' R' → Bd (κ ∪ κ') (D + D') (d + d') (R * R')) ∧ (∀ η m, Bd κ 0 m (chebP η m : PR K n)) ∧
      (κ ⊆ κ' → D ≤ D' → d ≤ d' → Bd κ D d R → Bd κ' D' d' R) ∧
      ∀ Λ : (K →+* ℂ) → Multiset ℂ, (∀ τ, (Λ τ).card = n) → ∃ L : Ix K n → ℂ, msOf L = Λ := by
  intro K _ _ n κ κ' D D' d d' R R'
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro ⟨h1, h2, h3⟩ ⟨h1', h2', h3'⟩
    refine ⟨?_, (totalDegree_mul _ _).trans (Nat.add_le_add h2 h2'), ?_⟩
    · intro x hx
      rcases Finset.mem_union.mp (vars_mul R R' hx) with h | h
      · exact Finset.mem_union_left _ (h1 x h)
      · exact Finset.mem_union_right _ (h1' x h)
    · intro β
      rw [coeff_mul]
      exact totalDegree_finsetSum_le fun _ _ =>
        (totalDegree_mul _ _).trans (Nat.add_le_add (h3 _) (h3' _))
  · intro η m
    have hq : (C ((2 / η : ℝ) : ℂ) * X none - 1 : MvPolynomial (Option (Ix K n)) ℂ).totalDegree ≤ 1 := by
      refine (totalDegree_sub _ _).trans (max_le ?_ (by simp))
      refine (totalDegree_mul _ _).trans ?_
      simp [totalDegree_X]
    refine ⟨?_, ?_, ?_⟩
    · intro x hx
      simp [chebP, vars_C] at hx
    · simp [chebP]
    · intro β
      unfold chebP
      rw [coeff_C]
      split_ifs
      · refine (totalDegree_aeval_le _ hq _).trans ?_
        simp [Polynomial.Chebyshev.natDegree_T]
      · simp
  · rintro hκ hD hd ⟨h1, h2, h3⟩
    exact ⟨fun x hx => hκ (h1 x hx), h2.trans hD, fun β => (h3 β).trans hd⟩
  · intro Λ hΛ
    choose f hf using fun τ => exists_fin_map n (Λ τ) (hΛ τ)
    refine ⟨fun y => f y.1 y.2, ?_⟩
    funext τ
    exact hf τ
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.BlockEvaluation.TruncSpecAlt
section
open MeasureTheory NumberField IsDedekindDomain MvPolynomial Filter Topology UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Ci
open PositivityTheory.Rg.Fx

private theorem homog_eq {ι : Type} (d : ℕ) (p : MvPolynomial ι ℂ) :
    homog d p = ∑ α ∈ p.support,
      monomial (Finsupp.single none (d - α.degree) + α.mapDomain some) (p.coeff α) := by
  unfold homog
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [rename_monomial, X_pow_eq_monomial, monomial_mul, one_mul]

private theorem deg_le {ι : Type} {d : ℕ} {p : MvPolynomial ι ℂ} (h : p.totalDegree ≤ d) {α : ι →₀ ℕ}
    (hα : α ∈ p.support) : α.degree ≤ d := by
  have := (le_totalDegree hα).trans h
  simpa [Finsupp.degree_apply, Finsupp.sum] using this

private theorem deg_exp {ι : Type} {d : ℕ} {α : ι →₀ ℕ} (h : α.degree ≤ d) :
    (Finsupp.single none (d - α.degree) + α.mapDomain some : Option ι →₀ ℕ).degree = d := by
  rw [map_add (f := _), Finsupp.degree_single, Finsupp.degree_mapDomain]
  omega

private theorem homog_deg {ι : Type} {d : ℕ} {p : MvPolynomial ι ℂ} (h : p.totalDegree ≤ d) :
    (homog d p).totalDegree ≤ d := by
  rw [homog_eq]
  refine totalDegree_finsetSum_le fun α hα => (totalDegree_monomial_le _ _).trans (le_of_eq ?_)
  have := deg_exp (deg_le h hα)
  rw [Finsupp.degree_apply] at this
  exact this

private theorem homog_eval {ι : Type} {d : ℕ} {p : MvPolynomial ι ℂ} (h : p.totalDegree ≤ d) (x : ℂ) (g : ι → ℂ) :
    eval (fun o : Option ι => o.elim x fun y => x * g y) (homog d p) = x ^ d * eval g p := by
  unfold homog
  conv_rhs => rw [p.as_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun α hα => ?_
  have hd := deg_le h hα
  rw [map_mul, map_pow, eval_X, eval_rename, eval_monomial, eval_monomial]
  have e : (α.prod fun n e => ((fun o : Option ι => o.elim x fun y => x * g y) ∘ some) n ^ e)
      = x ^ α.degree * α.prod fun n e => g n ^ e := by
    simp only [Function.comp, Option.elim, mul_pow, Finsupp.prod, Finset.prod_mul_distrib,
      Finset.prod_pow_eq_pow_sum, Finsupp.degree_apply]
  rw [e]
  have : x ^ d = x ^ (d - α.degree) * x ^ α.degree := by rw [← pow_add]; congr 1; omega
  rw [this]
  simp only [Option.elim]
  ring

private theorem mon_norm {σ : Type} [Fintype σ] {H : Type} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (ψ : MvPolynomial σ ℂ →+* (H →L[ℂ] H)) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ m : σ →₀ ℕ, ‖ψ (monomial m 1)‖ ≤ D ^ m.degree := by
  have h0 : 0 ≤ ∑ i, ‖ψ (X i)‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  refine ⟨1 + ∑ i, ‖ψ (X i)‖, by linarith, fun m => ?_⟩
  have h1 : ‖(1 : H →L[ℂ] H)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
  induction m using Finsupp.induction_linear with
  | zero => simpa using h1
  | add a b ha hb =>
    have : (monomial (a + b) 1 : MvPolynomial σ ℂ) = monomial a 1 * monomial b 1 := by
      rw [monomial_mul, one_mul]
    rw [this, map_mul, map_add (f := _), pow_add]
    exact (norm_mul_le _ _).trans (mul_le_mul ha hb (norm_nonneg _) (by positivity))
  | single i e =>
    rw [← X_pow_eq_monomial, map_pow, Finsupp.degree_single]
    have hi : ‖ψ (X i)‖ ≤ 1 + ∑ i, ‖ψ (X i)‖ := by
      have := Finset.single_le_sum (f := fun i => ‖ψ (X i)‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ i)
      linarith
    induction e with
    | zero => simpa using h1
    | succ e ih =>
      rw [pow_succ, pow_succ]
      exact (norm_mul_le _ _).trans (mul_le_mul ih hi (norm_nonneg _) (by positivity))

private theorem homog_norm {ι : Type} [Fintype ι] {H : Type} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (ψ : MvPolynomial (Option ι) ℂ →+* (H →L[ℂ] H)) (hψ : ∀ c : ℂ, ψ (C c) = c • 1) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ (d : ℕ) (p : MvPolynomial ι ℂ), p.totalDegree ≤ d → ‖ψ (homog d p)‖ ≤ l1 p * D ^ d := by
  obtain ⟨D, hD, h⟩ := mon_norm ψ
  refine ⟨D, hD, fun d p hp => ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [homog_eq, map_sum, l1, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun α hα => ?_)
  rw [← mul_one (p.coeff α), ← C_mul_monomial, map_mul, hψ, smul_mul_assoc, one_mul, norm_smul, mul_one]
  refine mul_le_mul_of_nonneg_left ((h _).trans (le_of_eq ?_)) (norm_nonneg _)
  rw [deg_exp (deg_le hp hα)]

private theorem trunc_eq {K : Type} [Field K] [NumberField K] {n : ℕ} (d : ℕ)
    (G : ℕ → MvPolynomial (Pl K × Fin n) (MvPolynomial (Ix K n) ℂ)) (s : Finset ((Pl K × Fin n) →₀ ℕ))
    (h : ∀ k, (G k).support ⊆ s) :
    trunc d G = ∑ β ∈ s, monomial β (∑ k ∈ Finset.range (d + 1), homog d ((G k).coeff β)) := by
  unfold trunc
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_subset (h k) fun β _ hβ => ?_
  rw [notMem_support_iff.mp hβ]
  simp [homog]

private theorem eval_blockE {K : Type} [Field K] [NumberField K] {n : ℕ} (L : Ix K n → ℂ)
    (p : MvPolynomial (Ix K n) ℂ) :
    eval L (aeval blockE p) = eval (fun y : Ix K n => (msOf L y.1).esymm (y.2 + 1)) p := by
  have e : ∀ y : Ix K n, eval L (blockE y) = (msOf L y.1).esymm (y.2 + 1) := by
    intro y
    rw [blockE, eval_rename, ← coe_aeval_eq_eval]
    exact aeval_esymm_eq_multiset_esymm (Fin n) ℂ _ _
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p i hp => simp only [map_mul, hp, aeval_X, eval_X, e]

theorem UpperTheory.ConvolutionTheory.Ci.truncSpec :
    TruncSpec := by
  intro K _ _ n S Φ hΦ
  classical
  obtain ⟨K₀, G₀, hG₀⟩ := UpperTheory.ConvolutionTheory.FX.gen_piecesK (K →+* ℂ) (Pl K × Fin n) n Φ (by
    intro w
    convert hΦ.1 w)
  refine ⟨⟨G₀, fun k => (hG₀ k).1⟩, fun G hG => ?_⟩
  have hGG : G = G₀ := by
    funext k
    refine map_injective _ (UpperTheory.ConvolutionTheory.FX.blockE_inj (K →+* ℂ) n) ?_
    exact (hG k).trans (hG₀ k).1.symm
  subst hGG
  have hs : ∀ k, (G k).support ⊆ Φ.support := fun k => (hG₀ k).2.1
  have hdeg : ∀ d β, ∀ k ∈ Finset.range (d + 1), ((G k).coeff β).totalDegree ≤ d := fun d β k hk =>
    ((hG₀ k).2.2 β).1.trans (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))
  have hT := fun d => trunc_eq d G Φ.support hs
  refine ⟨⟨Φ.vars.image Prod.fst, Φ.totalDegree, ?_, fun d => ?_⟩, fun L t => ?_, fun H _ _ _ ev hev => ?_⟩
  · intro w hw
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hw
    exact hΦ.2 x hx
  · have hsup : (trunc d G).support ⊆ Φ.support := by
      rw [hT]
      refine support_sum.trans (Finset.biUnion_subset.mpr fun β hβ => support_monomial_subset.trans ?_)
      simpa using hβ
    refine ⟨fun x hx => ?_, Finset.sup_mono hsup, fun β => ?_⟩
    · obtain ⟨m, hm, hx⟩ := (mem_vars_iff_mem_support x).mp hx
      exact Finset.mem_image_of_mem _ ((mem_vars_iff_mem_support x).mpr ⟨m, hsup hm, hx⟩)
    · rw [hT, coeff_sum]
      refine totalDegree_finsetSum_le fun γ _ => ?_
      rw [coeff_monomial]
      split_ifs
      · exact totalDegree_finsetSum_le fun k hk => homog_deg (hdeg d γ k hk)
      · simp
  · have hc : ∀ k, ∀ β ∈ Φ.support, eval (fun y : Ix K n => (msOf L y.1).esymm (y.2 + 1)) ((G k).coeff β)
        = eval L (piece k (Φ.coeff β)) := by
      intro k β hβ
      rw [← eval_blockE]
      congr 1
      have := congrArg (AddMonoidAlgebra.coeff · β) (hG k)
      rw [coeff_map, pieceK, coeff_sum] at this
      simp only [coeff_monomial, Finset.sum_ite_eq', if_pos hβ] at this
      exact this
    refine ⟨fun d => ∑ β ∈ Φ.support, (∑ k ∈ Finset.range (d + 1), eval L (piece k (Φ.coeff β))) *
      β.prod fun i e => hval t i ^ e, ?_, fun x d => ?_⟩
    · have : evK L (hval t) Φ = ∑ β ∈ Φ.support, PositivityTheory.Rg.Fx.ev L (Φ.coeff β) * β.prod fun i e => hval t i ^ e := by
        conv_lhs => rw [Φ.as_sum]
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sum]
        refine Finset.sum_congr rfl fun β _ => ?_
        rw [evK, eval₂Hom_monomial]
      rw [this]
      refine tendsto_finsetSum _ fun β _ => Tendsto.mul_const _ ?_
      exact (UpperTheory.ConvolutionTheory.FX.piece_sum _ (Φ.coeff β) L).tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
    · set_option synthInstance.maxHeartbeats 100000 in
        rw [hT, map_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun β hβ => ?_
      set_option synthInstance.maxHeartbeats 100000 in
        rw [val, eval₂Hom_monomial, map_sum, ← mul_assoc, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun k hk => ?_
      rw [← hc k β hβ]
      exact homog_eval (hdeg d β k hk) _ _
  · obtain ⟨D, hD, hb⟩ := homog_norm (ev.comp C) hev
    set A : ℝ := ∑ β ∈ Φ.support, ‖ev (monomial β 1)‖ with hA
    have hA0 : 0 ≤ A := Finset.sum_nonneg fun _ _ => norm_nonneg _
    set E : ℝ := |K₀| + 1 with hE
    have hE1 : 1 ≤ E := by have := abs_nonneg K₀; linarith
    refine ⟨(A + 1) * 2 * E * D, fun d => ?_⟩
    have h1 : ∀ β, ‖ev (C (∑ k ∈ Finset.range (d + 1), homog d ((G k).coeff β)))‖
        ≤ 2 ^ (d + 1) * E ^ (d + 1) * D ^ (d + 1) := by
      intro β
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, map_sum]
      refine (norm_sum_le _ _).trans ?_
      have h2 : ∀ k ∈ Finset.range (d + 1), ‖ev (C (homog d ((G k).coeff β)))‖ ≤ E ^ (d + 1) * D ^ (d + 1) := by
        intro k hk
        refine (hb d _ (hdeg d β k hk)).trans (mul_le_mul ?_ (pow_le_pow_right₀ hD (Nat.le_succ d))
          (by positivity) (by positivity))
        refine ((hG₀ k).2.2 β).2.trans ?_
        have h3 : K₀ ^ (k + 1) ≤ E ^ (k + 1) :=
          (le_abs_self _).trans (by rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (by linarith) _)
        have h4 : E ^ (k + 1) ≤ E ^ (d + 1) :=
          pow_le_pow_right₀ hE1 (by have := Finset.mem_range.mp hk; omega)
        have h5 : (1 : ℝ) ≤ k.factorial := by exact_mod_cast Nat.factorial_pos k
        calc K₀ ^ (k + 1) / k.factorial ≤ E ^ (d + 1) / k.factorial := by gcongr; linarith
          _ ≤ E ^ (d + 1) := div_le_self (by positivity) h5
      refine (Finset.sum_le_card_nsmul _ _ _ h2).trans ?_
      rw [Finset.card_range, nsmul_eq_mul, mul_assoc]
      refine mul_le_mul_of_nonneg_right ?_ (by positivity)
      exact_mod_cast (Nat.lt_two_pow_self (n := d + 1)).le
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hT, map_sum]
    refine (norm_sum_le _ _).trans ?_
    have h6 : ∀ β ∈ Φ.support, ‖ev (monomial β (∑ k ∈ Finset.range (d + 1), homog d ((G k).coeff β)))‖
        ≤ 2 ^ (d + 1) * E ^ (d + 1) * D ^ (d + 1) * ‖ev (monomial β 1)‖ := by
      intro β _
      rw [← mul_one (∑ k ∈ Finset.range (d + 1), homog d ((G k).coeff β)), ← C_mul_monomial, map_mul]
      exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (h1 β) (norm_nonneg _))
    refine (Finset.sum_le_sum h6).trans ?_
    rw [← Finset.mul_sum, ← hA, mul_pow, mul_pow, mul_pow]
    have h7 : A ≤ (A + 1) ^ (d + 1) :=
      (by linarith : A ≤ A + 1).trans (le_self_pow₀ (by linarith) (Nat.succ_ne_zero d))
    calc 2 ^ (d + 1) * E ^ (d + 1) * D ^ (d + 1) * A ≤ 2 ^ (d + 1) * E ^ (d + 1) * D ^ (d + 1) * (A + 1) ^ (d + 1) := by
          gcongr
      _ = _ := by ring
end

