module

public import Mathlib
public import Formalism.LocalToGlobal.CharacterGerms.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0046
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0043
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0008
public import Formalism.HermitianCurvature.Bundle0008
public import Formalism.RealPlaceAnalysis.Bundle0004
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0041
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0059
public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0027
public import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
public import Formalism.PeriodIntegrals.Bundle0011
public import Formalism.PeriodIntegrals.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0049
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0055
public import Formalism.RealPlaceAnalysis.Bundle0003
public import Formalism.RealPlaceAnalysis.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0057

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsGoodIntegerPlanLowLevelsBound
section
open scoped BigOperators
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.UnitaryBoundIntegral

namespace GlobalTheory.GoodPlan

theorem blockBd_le {l n m i y I S : ℕ} {x : ℝ} (hl : 5 ≤ l) (hn : 1 ≤ n)
    (hi : x ≠ 0 → i < I) (h1 : (n : ℝ) * y ≤ x) (h2 : x - n * y ≤ n * S) :
    blockBd l n m i y ≤ n * gam l * ((l : ℝ) ^ i * y) + n * gam l * y - x +
      (if x ≠ 0 then (n : ℝ) * ((S : ℝ) + Real.logb l n + 1) else 0) +
      2 * (I : ℝ) * m / ((l : ℝ) - 1) * ((l : ℝ) ^ i * y) := by
  have hL := GlobalTheory.OrbitPlan.logTerm_nonneg hl hn
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hl' : (5 : ℝ) ≤ l := by exact_mod_cast hl
  have hy0 : (0 : ℝ) ≤ y := Nat.cast_nonneg _
  by_cases hx : x = 0
  · have : (y : ℝ) = 0 := by nlinarith
    have hy : y = 0 := by exact_mod_cast this
    simp [blockBd, hy, hx]
  rw [if_pos hx]
  by_cases hy : y = 0
  · subst hy
    simp only [blockBd, if_true, Nat.cast_zero, mul_zero, sub_zero] at h2 ⊢
    linarith
  have hiI : (i : ℝ) + 1 ≤ I := by exact_mod_cast hi hx
  have hp : (1 : ℝ) ≤ (l : ℝ) ^ i := one_le_pow₀ (by linarith)
  have e : ((i : ℝ) + 1) * m * ((l : ℝ) ^ i + 1) * y / ((l : ℝ) - 1) ≤
      2 * (I : ℝ) * m / ((l : ℝ) - 1) * ((l : ℝ) ^ i * y) := by
    rw [div_mul_eq_mul_div]
    refine div_le_div_of_nonneg_right ?_ (by linarith)
    have : ((i : ℝ) + 1) * ((l : ℝ) ^ i + 1) ≤ I * (2 * (l : ℝ) ^ i) :=
      mul_le_mul hiI (by linarith) (by positivity) (by positivity)
    have hmy : (0 : ℝ) ≤ m * y := by positivity
    nlinarith [mul_le_mul_of_nonneg_right this hmy]
  simp only [blockBd, bdP, hy, if_false]
  linarith

theorem exists_plan : ∀ (l d : ℕ) [NeZero d], 5 ≤ l → ∀ (n m k S : ℕ), 1 ≤ n → 1 ≤ k → ∀ (W : ZMod d → ℕ) (Ws : ZMod d → ℝ) (Good : ZMod d → ℕ → Set ℕ),
  (∀ a, 0 ≤ Ws a ∧ Ws a ≤ W a) → (∀ a, ∀ i ∈ oddLevels d, i < i0 k l → Windows S (Good a i)) →
  ∃ p : Plan l d W, (∀ a i, i0 k l ≤ i → p.y a i = 0) ∧ (∀ a i, p.y a i ≠ 0 → p.y a i ∈ Good a i) ∧
    p.bound n m ≤ Fnum l d (fun a => (n : ℝ) * Ws a) + thl k l * n * (∑ a, Ws a) + n * gam l * (∑ a, ((W a : ℝ) - Ws a)) +
      m * (∑ a, (W a : ℝ)) / ((l : ℝ) - 1) + 2 * (i0 k l : ℝ) * m * (∑ a, Ws a) / ((l : ℝ) - 1) + d * (i0 k l : ℝ) * (n * ((S : ℝ) + Real.logb l n + 1)) := by
  intro l d _ hl n m k S hn hk W Ws Good hW hG
  classical
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hl' : (5 : ℝ) ≤ l := by exact_mod_cast hl
  have hW0 : (0 : ZMod d → ℝ) ≤ fun a => (n : ℝ) * Ws a := fun a => mul_nonneg hn0.le (hW a).1
  obtain ⟨ys, hflow, hsupp, hcard, hval⟩ :=
    GlobalTheory.BasicFlow.dropLevelsBasic l d (by omega) (fun a => (n : ℝ) * Ws a) hW0 (i0 k l)
  obtain ⟨-, h3, -, hthl⟩ := GlobalTheory.LevelsOrbits.thlEq k l hk (by omega)
  have hex : ∀ a i, ∃ y : ℕ, (y ≠ 0 → y ∈ Good a i) ∧ (n : ℝ) * y ≤ ys a i ∧
      ys a i - n * y ≤ n * (S : ℝ) := by
    intro a i
    by_cases hc : i ∈ oddLevels d ∧ i < i0 k l
    · obtain ⟨y, hy, h1, h2⟩ := GlobalTheory.OrbitPlan.exists_good (hG a i hc.1 hc.2)
        (div_nonneg (hflow.1 a i) hn0.le)
      rw [le_div_iff₀ hn0] at h1
      rw [sub_le_iff_le_add, div_le_iff₀ hn0] at h2
      exact ⟨y, fun _ => hy, by linarith, by linarith⟩
    · have : ys a i = 0 := hsupp a i (by
        by_cases h : i ∈ oddLevels d
        · left; by_contra h'; exact hc ⟨h, by omega⟩
        · right; exact h)
      refine ⟨0, fun h => absurd rfl h, by simp [this], ?_⟩
      simp only [this, Nat.cast_zero, mul_zero, sub_zero]; positivity
  choose y hyG hyle hyge using hex
  have hy0 : ∀ a i, ys a i = 0 → y a i = 0 := by
    intro a i h
    have h1 := hyle a i
    rw [h] at h1
    have h2 : (0 : ℝ) ≤ y a i := Nat.cast_nonneg _
    have : (y a i : ℝ) = 0 := by nlinarith
    exact_mod_cast this
  have hleR : ∀ a, (∑ i ∈ oddLevels d, (l : ℝ) ^ i * y a i) +
      (∑ i ∈ oddLevels d, (y (a - (i : ZMod d)) i : ℝ)) ≤ Ws a := by
    intro a
    refine le_of_mul_le_mul_left (le_trans ?_ (hflow.2 a)) hn0
    rw [mul_add, Finset.mul_sum, Finset.mul_sum]
    refine add_le_add (Finset.sum_le_sum fun i _ => ?_) (Finset.sum_le_sum fun i _ => hyle _ i)
    rw [mul_left_comm]
    exact mul_le_mul_of_nonneg_left (hyle a i) (by positivity)
  have hle : ∀ a, (∑ i ∈ oddLevels d, l ^ i * y a i) +
      (∑ i ∈ oddLevels d, y (a - (i : ZMod d)) i) ≤ W a := by
    intro a
    exact_mod_cast (hleR a).trans (hW a).2
  let p : Plan l d W :=
    { y := y
      u := fun a => W a - ((∑ i ∈ oddLevels d, l ^ i * y a i) +
        (∑ i ∈ oddLevels d, y (a - (i : ZMod d)) i))
      supp := fun a i hi => hy0 a i (hsupp a i (Or.inr hi))
      bal := fun a => by have := hle a; omega }
  refine ⟨p, fun a i hi => hy0 a i (hsupp a i (Or.inl hi)), hyG, ?_⟩
  have hbal : ∀ a, (W a : ℝ) = (∑ i ∈ oddLevels d, (l : ℝ) ^ i * y a i) +
      (∑ i ∈ oddLevels d, (y (a - (i : ZMod d)) i : ℝ)) + (p.u a : ℝ) := by
    intro a
    have := p.bal a
    exact_mod_cast this
  set L : ℝ := (n : ℝ) * ((S : ℝ) + Real.logb l n + 1) with hL
  have hL0 : 0 ≤ L := by
    have := GlobalTheory.OrbitPlan.logTerm_nonneg hl hn
    have : (0 : ℝ) ≤ n * S := by positivity
    rw [hL]; linarith
  have hshift : (∑ a, ∑ i ∈ oddLevels d, (y (a - (i : ZMod d)) i : ℝ)) =
      ∑ a, ∑ i ∈ oddLevels d, (y a i : ℝ) := by
    rw [Finset.sum_comm, Finset.sum_comm (f := fun a i => (y a i : ℝ))]
    exact Finset.sum_congr rfl fun i _ =>
      Equiv.sum_comp (Equiv.subRight (i : ZMod d)) (fun a => (y a i : ℝ))
  set A : ℝ := ∑ a, ∑ i ∈ oddLevels d, (l : ℝ) ^ i * y a i with hA
  set B : ℝ := ∑ a, ∑ i ∈ oddLevels d, (y a i : ℝ) with hB
  set U : ℝ := ∑ a, (p.u a : ℝ) with hU
  have hA0 : 0 ≤ A := by positivity
  have hB0 : 0 ≤ B := by positivity
  have hsum : (∑ a, (W a : ℝ)) = A + B + U := by
    rw [Finset.sum_congr rfl fun a _ => hbal a, Finset.sum_add_distrib, Finset.sum_add_distrib,
      hshift]
  have hAB : A + B ≤ ∑ a, Ws a := by
    have := Finset.sum_le_sum (s := Finset.univ) fun a _ => hleR a
    rwa [Finset.sum_add_distrib, hshift] at this
  have e1 : (∑ a, ∑ i ∈ oddLevels d, (if ys a i ≠ 0 then L else 0)) ≤ d * (i0 k l : ℝ) * L := by
    rw [← Finset.sum_product' (f := fun a i => if ys a i ≠ 0 then L else 0), ← Finset.sum_filter,
      Finset.sum_const, nsmul_eq_mul]
    refine mul_le_mul_of_nonneg_right ?_ hL0
    exact_mod_cast hcard.trans (Nat.le_mul_of_pos_right _ (by omega))
  set c : ℝ := 2 * (i0 k l : ℝ) * m / ((l : ℝ) - 1) with hc
  have hl1 : (0 : ℝ) < (l : ℝ) - 1 := by linarith
  have hc0 : 0 ≤ c := by positivity
  have e2 : (∑ a, ∑ i ∈ oddLevels d, blockBd l n m i (y a i)) ≤
      n * gam l * A + n * gam l * B - flowVal d ys +
        (∑ a, ∑ i ∈ oddLevels d, (if ys a i ≠ 0 then L else 0)) + c * A := by
    refine le_trans (Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun i _ =>
      blockBd_le (I := i0 k l) (m := m) hl hn
        (fun h => by by_contra h'; exact h (hsupp a i (Or.inl (by omega))))
        (hyle a i) (hyge a i)) (le_of_eq ?_)
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, flowVal]
    rfl
  have e3 : (∑ a, chBd l n m (p.u a)) = n * gam l * U + m / ((l : ℝ) - 1) * U := by
    simp only [chBd, ← Finset.sum_mul]; ring
  have e4 : m / ((l : ℝ) - 1) * U ≤ m * (∑ a, (W a : ℝ)) / ((l : ℝ) - 1) := by
    rw [mul_div_right_comm]
    exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have e5 : c * A ≤ 2 * (i0 k l : ℝ) * m * (∑ a, Ws a) / ((l : ℝ) - 1) := by
    rw [mul_div_right_comm]
    exact mul_le_mul_of_nonneg_left (by linarith) hc0
  rw [← Finset.mul_sum, ← inv_mul_eq_div, ← hthl] at hval
  unfold Plan.bound Fnum
  rw [e3, Finset.sum_sub_distrib, ← Finset.mul_sum]
  change (∑ a, ∑ i ∈ oddLevels d, blockBd l n m i (y a i)) + _ ≤ _
  rw [hsum] at e4 ⊢
  nlinarith

end GlobalTheory.GoodPlan
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsLinearEquivOfIrreducibleCapelli
section
open Formalism.REAL Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr

namespace GlobalTheory

theorem exists_linearEquiv_of_irreducible_capelli :
    ∀ (V₁ : Type) [AddCommGroup V₁] [Module ℂ V₁] [FiniteDimensional ℂ V₁] (V₂ : Type) [AddCommGroup V₂]
      [Module ℂ V₂] [FiniteDimensional ℂ V₂] (n : ℕ) (E₁ : Fin n → Fin n → Module.End ℂ V₁)
      (E₂ : Fin n → Fin n → Module.End ℂ V₂) (m : Fin n → ℂ), GlRel E₁ → GlRel E₂ → Irr E₁ → Irr E₂ →
      (∀ w v, qdet E₁ w v = cpol m w • v) → (∀ w v, qdet E₂ w v = cpol m w • v) →
      ∃ T : V₁ ≃ₗ[ℂ] V₂, ∀ a b x, T (E₁ a b x) = E₂ a b (T x) := by
  intro V₁ _ _ _ V₂ _ _ _ n E₁ E₂ m g₁ g₂ i₁ i₂ c₁ c₂
  haveI := i₁.1
  haveI := i₂.1
  obtain ⟨ν₁, v₁, -, hv₁, hw₁, -⟩ := Formalism.FourierDecayAlt.P.exists_singular_maximal_vector V₁ n E₁ g₁ ⊤
    (fun _ _ _ _ => Submodule.mem_top) top_ne_bot
  obtain ⟨ν₂, v₂, -, hv₂, hw₂, -⟩ := Formalism.FourierDecayAlt.P.exists_singular_maximal_vector V₂ n E₂ g₂ ⊤
    (fun _ _ _ _ => Submodule.mem_top) top_ne_bot
  have p₁ := Formalism.FourierDecayAlt.P.HighestWeightPolynomials.hw_cpol (m := m) g₁ (mem_CapSp.2 fun w => c₁ w v₁) hv₁ hw₁
  have p₂ := Formalism.FourierDecayAlt.P.HighestWeightPolynomials.hw_cpol (m := m) g₂ (mem_CapSp.2 fun w => c₂ w v₂) hv₂ hw₂
  have s₁ := Formalism.FourierDecayAlt.P.HighestWeightPolynomials.sdec_shift (Formalism.FourierDecayAlt.P.singular_dominant V₁ n E₁ ν₁ v₁ g₁ hw₁ hv₁)
  have s₂ := Formalism.FourierDecayAlt.P.HighestWeightPolynomials.sdec_shift (Formalism.FourierDecayAlt.P.singular_dominant V₂ n E₂ ν₂ v₂ g₂ hw₂ hv₂)
  have h := (Formalism.FourierDecayAlt.P.separating_polynomials n _ _ (fun w => (p₁ w).symm.trans (p₂ w)) s₂).2 s₁
  have hν : ν₁ = ν₂ := by
    funext j
    exact sub_left_injective (congrFun h j)
  subst hν
  exact exists_linearEquiv_of_irreducible_isHW V₁ V₂ n E₁ E₂ ν₁ v₁ v₂ g₁ g₂ i₁.2 i₂.2 hw₁ hw₂ hv₁ hv₂

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsQuotientMeasureWeil
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.QuotWeil

theorem measurable_mulM {m : ℕ} {α : Type} [MeasurableSpace α] {a b : α → PI.MtM m}
    (ha : Measurable a) (hb : Measurable b) :
    Measurable (fun t => (fun i j => (Matrix.of (a t) * Matrix.of (b t)) i j : PI.MtM m)) := by
  refine Measurable.of_eval fun i => Measurable.of_eval fun j => ?_
  simp only [Matrix.mul_apply, Matrix.of_apply]
  refine Finset.measurable_sum _ fun k _ => Measurable.mul ?_ ?_
  · exact (measurable_pi_apply k).comp ((measurable_pi_apply i).comp ha)
  · exact (measurable_pi_apply j).comp ((measurable_pi_apply k).comp hb)

theorem measurable_invM {m : ℕ} :
    Measurable (fun s : PI.MtM m => (fun i j => (Matrix.of s)⁻¹ i j : PI.MtM m)) := by
  refine Measurable.of_eval fun i => Measurable.of_eval fun j => ?_
  have hc : Continuous (fun s : PI.MtM m => (Matrix.of s : Matrix (Fin m) (Fin m) ℂ)) := continuous_id
  simp only [Matrix.inv_def, Matrix.smul_apply, Ring.inverse_eq_inv', smul_eq_mul]
  refine Measurable.mul (Measurable.inv hc.matrix_det.measurable) ?_
  exact (hc.matrix_adjugate.matrix_elem i j).measurable

theorem unfold_abstract {X : Type} [MeasurableSpace X] (mu : X → X → X) (iv : X → X)
    (hmu : Measurable (fun p : X × X => mu p.1 p.2)) (hiv : Measurable iv)
    (μG μS : Measure X) [SFinite μG] [SFinite μS]
    (hleft : ∀ᵐ s ∂μS, μG.map (mu s) = μG ∧ ∀ x, mu (iv s) (mu s x) = x)
    (hinv : ∀ f : X → ℝ≥0∞, Measurable f → ∫⁻ s, f (iv s) ∂μS = ∫⁻ s, f s ∂μS)
    (φ : X → ℝ≥0∞) (hφ : Measurable φ) (hφ1 : ∀ᵐ x ∂μG, ∫⁻ s, φ (mu s x) ∂μS = 1)
    (f : X → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ x, f x ∂μG = ∫⁻ x, (∫⁻ s, f (mu s x) ∂μS) ∂(μG.withDensity φ) := by
  have hl : ∀ s, Measurable (mu s) := fun s => hmu.comp (measurable_const.prodMk measurable_id)
  have hr : ∀ x, Measurable (fun s => mu s x) := fun x =>
    hmu.comp (measurable_id.prodMk measurable_const)
  have h1 : Measurable (fun p : X × X => f (mu p.2 p.1)) := hf.comp (hmu.comp measurable_swap)
  have h2 : Measurable (fun p : X × X => φ (mu (iv p.1) p.2) * f p.2) :=
    (hφ.comp (hmu.comp ((hiv.comp measurable_fst).prodMk measurable_snd))).mul
      (hf.comp measurable_snd)
  have hF : Measurable (fun x : X => ∫⁻ s, f (mu s x) ∂μS) := h1.lintegral_prod_right'
  rw [lintegral_withDensity_eq_lintegral_mul _ hφ hF]
  symm
  calc ∫⁻ x, (φ * fun x : X => ∫⁻ s, f (mu s x) ∂μS) x ∂μG
      = ∫⁻ x, ∫⁻ s, φ x * f (mu s x) ∂μS ∂μG := by
        refine lintegral_congr fun x => ?_
        rw [Pi.mul_apply, lintegral_const_mul]
        exact hf.comp (hr x)
    _ = ∫⁻ s, ∫⁻ x, φ x * f (mu s x) ∂μG ∂μS :=
        lintegral_lintegral_swap ((hφ.comp measurable_fst).mul h1).aemeasurable
    _ = ∫⁻ s, ∫⁻ y, φ (mu (iv s) y) * f y ∂μG ∂μS := by
        refine lintegral_congr_ae (hleft.mono fun s hs => ?_)
        have hm : Measurable (fun y : X => φ (mu (iv s) y) * f y) :=
          (hφ.comp (hl _)).mul hf
        beta_reduce
        conv_rhs => rw [← hs.1, lintegral_map hm (hl s)]
        refine lintegral_congr fun x => ?_
        rw [hs.2]
    _ = ∫⁻ y, ∫⁻ s, φ (mu (iv s) y) * f y ∂μS ∂μG := lintegral_lintegral_swap h2.aemeasurable
    _ = ∫⁻ y, f y ∂μG := by
        refine lintegral_congr_ae (hφ1.mono fun y hy => ?_)
        have hm : Measurable (fun s : X => φ (mu s y)) := hφ.comp (hr y)
        have hm' : Measurable (fun s : X => φ (mu (iv s) y)) := hm.comp hiv
        have := hinv _ hm
        beta_reduce at this ⊢
        rw [lintegral_mul_const _ hm', this, hy, one_mul]

theorem exists_isQuotM : ∀ (m : ℕ) (G S : Set (Matrix (Fin m) (Fin m) ℂ)) (μG μS : Measure (PI.MtM m)),
    PI.IsMatGroup G → PI.IsMatGroup S → S ⊆ G → PI.IsHaarOnM G μG → PI.IsHaarOnM S μS →
    PI.IsRightInvM S μS → ∃ ν, PI.IsQuotM μG μS ν := by
  intro m G S μG μS hG hS hSG hμG hμS hR
  obtain ⟨φ, hφ, hφ1⟩ := _root_.GlobalTheory.exists_normalised_cutoff m G S μS hG hS hSG hμS hR
  have hinv := _root_.GlobalTheory.HaarInversion.lintegral_inv_eq m S μS hS hμS hR
  haveI := hμG.1
  haveI := hμS.1
  have haeS : ∀ᵐ s ∂μS, Matrix.of s ∈ S := by rw [ae_iff]; exact hμS.2.2.1
  have haeG : ∀ᵐ s ∂μG, Matrix.of s ∈ G := by rw [ae_iff]; exact hμG.2.2.1
  refine ⟨μG.withDensity φ, fun f hf => ?_⟩
  refine unfold_abstract (fun s x : PI.MtM m => fun i j => (Matrix.of s * Matrix.of x) i j)
    (fun s i j => (Matrix.of s)⁻¹ i j) (measurable_mulM measurable_fst measurable_snd)
    measurable_invM μG μS (haeS.mono fun s hs => ⟨hμG.2.2.2 _ (hSG hs), fun x => ?_⟩) hinv φ hφ
    (haeG.mono fun x hx => hφ1 x hx) f hf
  have hs1 : (Matrix.of s)⁻¹ * Matrix.of s = 1 := mul_eq_one_comm.1 (hS.2.2.2 _ hs).2
  change (Matrix.of s)⁻¹ * (Matrix.of s * Matrix.of x) = Matrix.of x
  rw [← Matrix.mul_assoc, hs1, Matrix.one_mul]

end GlobalTheory.QuotWeil
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.GlRelationRowStepsFunctionalEigen
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.RowChain

theorem quantumMinor_row_removal_chain (M Wp : Type) [AddCommGroup M] [Module ℂ M] [AddCommGroup Wp] [Module ℂ Wp]
    (k r : ℕ) (E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ M) (l : M →ₗ[ℂ] Wp)
    (p : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → ℂ) (τ : ℝ) (hE : Formalism.REAL.GlRel E)
    (h : ∀ a b : Fin (2 * r + k + 1), a < b → ¬ (r ≤ a.val ∧ b.val ≤ r + k) →
      (∀ v, l (E a b v) = p a b • l v) ∧
      ‖p a b‖ = (if b.val = a.val + 1 ∧ (b.val < r ∨ r + k < a.val) then (1 : ℝ)
        else if (a.val + 1 = r ∧ b.val = r + k) ∨ (a.val = r + k ∧ b.val = r + k + 1) then τ
        else 0)) (d : ℕ) :
    ∀ (i t : ℕ) (a b : Fin (t + 1) → Fin (2 * r + k + 1)), i + d + 1 = r → t + 1 + i = 2 * r + k →
      (∀ j, (a j).val = i + j.val) → (∀ j, (b j).val = i + 1 + j.val) →
      ∃ c : ℂ, ‖c‖ = τ ∧ ∀ u v, l (Formalism.REAL.qminor E a b u v) =
        c • l (Formalism.REAL.qminor E
          (fun j : Fin (r + k) => (⟨r + j.val, by omega⟩ : Fin (2 * r + k + 1)))
          (fun j : Fin (r + k) => (⟨if j.val < k then r + j.val else r + j.val + 1,
            by split_ifs <;> omega⟩ : Fin (2 * r + k + 1))) u v) := by
  induction d with
  | zero =>
    intro i t a b hi ht ha hb
    obtain rfl : t = r + k := by omega
    have hai : Function.Injective a := fun x y hxy => by
      have h1 := ha x; have h2 := ha y; rw [hxy] at h1; exact Fin.ext (by omega)
    have hbi : Function.Injective b := fun x y hxy => by
      have h1 := hb x; have h2 := hb y; rw [hxy] at h1; exact Fin.ext (by omega)
    obtain ⟨e, he, hl⟩ := _root_.GlobalTheory.qminor_row_step_under_functional M Wp _ _ E l a b
      (fun j : Fin (r + k) => (⟨r + j.val, by omega⟩ : Fin (2 * r + k + 1)))
      (fun j : Fin (r + k) => (⟨if j.val < k then r + j.val else r + j.val + 1,
            by split_ifs <;> omega⟩ : Fin (2 * r + k + 1)))
      ⟨i, by omega⟩ ⟨r + k, by omega⟩ (p ⟨i, by omega⟩ ⟨r + k, by omega⟩) hE hai hbi
      (fun x y hxy => by
        simp only [Fin.mk.injEq] at hxy; exact Fin.ext (by omega))
      (fun x y hxy => by
        simp only [Fin.mk.injEq] at hxy; exact Fin.ext (by split_ifs at hxy <;> omega))
      (by
        ext x
        simp only [Set.mem_range, Set.mem_insert_iff, Fin.ext_iff, ha]
        constructor
        · rintro ⟨j, hj⟩
          by_cases h0 : j.val = 0
          · left; omega
          · right; exact ⟨⟨j.val - 1, by omega⟩, by simp only; omega⟩
        · rintro (hx | ⟨j, hj⟩)
          · exact ⟨⟨0, by omega⟩, by simp only; omega⟩
          · exact ⟨⟨j.val + 1, by omega⟩, by simp only; omega⟩)
      (by
        simp only [Set.mem_range, Fin.ext_iff]
        rintro ⟨j, hj⟩; omega)
      (by
        ext x
        simp only [Set.mem_range, Set.mem_insert_iff, Fin.ext_iff, hb]
        constructor
        · rintro ⟨j, hj⟩
          rcases lt_trichotomy j.val k with h0 | h0 | h0
          · right; exact ⟨⟨j.val, by omega⟩, by simp only; split_ifs <;> omega⟩
          · left; omega
          · right; exact ⟨⟨j.val - 1, by omega⟩, by simp only; split_ifs <;> omega⟩
        · rintro (hx | ⟨j, hj⟩)
          · exact ⟨⟨k, by omega⟩, by simp only; omega⟩
          · split_ifs at hj
            · exact ⟨⟨j.val, by omega⟩, by simp only; omega⟩
            · exact ⟨⟨j.val + 1, by omega⟩, by simp only; omega⟩)
      (by
        simp only [Set.mem_range, Fin.ext_iff]
        rintro ⟨j, hj⟩; split_ifs at hj <;> omega)
      (by
        simp only [Set.mem_range, Fin.ext_iff, hb]
        rintro ⟨j, hj⟩; omega)
      (by
        intro j v
        have hj := hb j
        obtain ⟨h1, h2⟩ := h ⟨i, by omega⟩ (b j) (by rw [Fin.lt_def]; simp only; omega)
          (by simp only; omega)
        rw [h1]
        by_cases hc : b j = ⟨r + k, by omega⟩
        · rw [if_pos hc, hc]
        · rw [if_neg hc]
          have hc' : (b j).val ≠ r + k := fun h' => hc (Fin.ext h')
          rw [if_neg (by simp only; omega), if_neg (by simp only; omega)] at h2
          rw [norm_eq_zero.mp h2])
    refine ⟨_, ?_, hl⟩
    obtain ⟨-, h2⟩ := h ⟨i, by omega⟩ ⟨r + k, by omega⟩ (by rw [Fin.lt_def]; simp only; omega)
          (by simp only; omega)
    rw [if_neg (by simp only; omega), if_pos (Or.inl ⟨by simp only; omega, rfl⟩)] at h2
    rw [norm_mul, he, h2, one_mul]
  | succ d ih =>
    intro i t a b hi ht ha hb
    obtain ⟨t, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
    have hai : Function.Injective a := fun x y hxy => by
      have h1 := ha x; have h2 := ha y; rw [hxy] at h1; exact Fin.ext (by omega)
    have hbi : Function.Injective b := fun x y hxy => by
      have h1 := hb x; have h2 := hb y; rw [hxy] at h1; exact Fin.ext (by omega)
    obtain ⟨c, hc, hcl⟩ := ih (i + 1) t
      (fun j : Fin (t + 1) => (⟨i + 1 + j.val, by omega⟩ : Fin (2 * r + k + 1)))
      (fun j : Fin (t + 1) => (⟨i + 1 + 1 + j.val, by omega⟩ : Fin (2 * r + k + 1)))
      (by omega) (by omega) (fun _ => rfl) (fun _ => rfl)
    obtain ⟨e, he, hl⟩ := _root_.GlobalTheory.qminor_row_step_under_functional M Wp _ _ E l a b
      (fun j : Fin (t + 1) => (⟨i + 1 + j.val, by omega⟩ : Fin (2 * r + k + 1)))
      (fun j : Fin (t + 1) => (⟨i + 1 + 1 + j.val, by omega⟩ : Fin (2 * r + k + 1)))
      ⟨i, by omega⟩ ⟨i + 1, by omega⟩ (p ⟨i, by omega⟩ ⟨i + 1, by omega⟩) hE hai hbi
      (fun x y hxy => by
        simp only [Fin.mk.injEq] at hxy; exact Fin.ext (by omega))
      (fun x y hxy => by
        simp only [Fin.mk.injEq] at hxy; exact Fin.ext (by omega))
      (by
        ext x
        simp only [Set.mem_range, Set.mem_insert_iff, Fin.ext_iff, ha]
        constructor
        · rintro ⟨j, hj⟩
          by_cases h0 : j.val = 0
          · left; omega
          · right; exact ⟨⟨j.val - 1, by omega⟩, by simp only; omega⟩
        · rintro (hx | ⟨j, hj⟩)
          · exact ⟨⟨0, by omega⟩, by simp only; omega⟩
          · exact ⟨⟨j.val + 1, by omega⟩, by simp only; omega⟩)
      (by
        simp only [Set.mem_range, Fin.ext_iff]
        rintro ⟨j, hj⟩; omega)
      (by
        ext x
        simp only [Set.mem_range, Set.mem_insert_iff, Fin.ext_iff, hb]
        constructor
        · rintro ⟨j, hj⟩
          by_cases h0 : j.val = 0
          · left; omega
          · right; exact ⟨⟨j.val - 1, by omega⟩, by simp only; omega⟩
        · rintro (hx | ⟨j, hj⟩)
          · exact ⟨⟨0, by omega⟩, by simp only; omega⟩
          · exact ⟨⟨j.val + 1, by omega⟩, by simp only; omega⟩)
      (by
        simp only [Set.mem_range, Fin.ext_iff]
        rintro ⟨j, hj⟩; omega)
      (by
        simp only [Set.mem_range, Fin.ext_iff, hb]
        rintro ⟨j, hj⟩; omega)
      (by
        intro j v
        have hj := hb j
        obtain ⟨h1, h2⟩ := h ⟨i, by omega⟩ (b j) (by rw [Fin.lt_def]; simp only; omega)
          (by simp only; omega)
        rw [h1]
        by_cases hc : b j = ⟨i + 1, by omega⟩
        · rw [if_pos hc, hc]
        · rw [if_neg hc]
          have hc' : (b j).val ≠ i + 1 := fun h' => hc (Fin.ext h')
          rw [if_neg (by simp only; omega), if_neg (by simp only; omega)] at h2
          rw [norm_eq_zero.mp h2])
    obtain ⟨-, h2⟩ := h ⟨i, by omega⟩ ⟨i + 1, by omega⟩ (by rw [Fin.lt_def]; simp only; omega)
          (by simp only; omega)
    rw [if_pos (by simp only; exact ⟨trivial, by omega⟩)] at h2
    refine ⟨e * p ⟨i, by omega⟩ ⟨i + 1, by omega⟩ * c, ?_, fun u v => ?_⟩
    · rw [norm_mul, norm_mul, he, h2, hc, one_mul, one_mul]
    · rw [hl, hcl, smul_smul]

theorem chain_rows : ∀ (M Wp : Type) [AddCommGroup M] [Module ℂ M] [AddCommGroup Wp] [Module ℂ Wp] (k r : ℕ) (E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ M) (l : M →ₗ[ℂ] Wp) (p : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → ℂ) (τ : ℝ), 1 ≤ k → Formalism.REAL.GlRel E → (∀ a b : Fin (2 * r + k + 1), a < b → ¬ (r ≤ a.val ∧ b.val ≤ r + k) → (∀ v, l (E a b v) = p a b • l v) ∧ ‖p a b‖ = (if b.val = a.val + 1 ∧ (b.val < r ∨ r + k < a.val) then (1 : ℝ) else if (a.val + 1 = r ∧ b.val = r + k) ∨ (a.val = r + k ∧ b.val = r + k + 1) then τ else 0)) → 1 ≤ r → ∃ c : ℂ, ‖c‖ = τ ∧ ∀ u v, l (Formalism.REAL.qminor E (Fin.succAbove (Fin.last (2 * r + k))) (Fin.succAbove 0) u v) = c • l (Formalism.REAL.qminor E (fun j : Fin (r + k) => (⟨r + j.val, by omega⟩ : Fin (2 * r + k + 1))) (fun j : Fin (r + k) => (⟨if j.val < k then r + j.val else r + j.val + 1, by split_ifs <;> omega⟩ : Fin (2 * r + k + 1))) u v) := by
  intro M Wp _ _ _ _ k r E l p τ _ hE h hr
  have gen : ∀ (n : ℕ) (a b : Fin n → Fin (2 * r + k + 1)), n = 2 * r + k →
      (∀ j, (a j).val = 0 + j.val) → (∀ j, (b j).val = 0 + 1 + j.val) →
      ∃ c : ℂ, ‖c‖ = τ ∧ ∀ u v, l (Formalism.REAL.qminor E a b u v) =
        c • l (Formalism.REAL.qminor E
          (fun j : Fin (r + k) => (⟨r + j.val, by omega⟩ : Fin (2 * r + k + 1)))
          (fun j : Fin (r + k) => (⟨if j.val < k then r + j.val else r + j.val + 1,
            by split_ifs <;> omega⟩ : Fin (2 * r + k + 1))) u v) := by
    intro n a b hn ha hb
    cases n with
    | zero => omega
    | succ t =>
      exact quantumMinor_row_removal_chain M Wp k r E l p τ hE h (r - 1) 0 t a b (by omega) (by omega) ha hb
  exact gen _ _ _ rfl (fun j => by simp) (fun j => by simp; omega)

end GlobalTheory.RowChain
end

