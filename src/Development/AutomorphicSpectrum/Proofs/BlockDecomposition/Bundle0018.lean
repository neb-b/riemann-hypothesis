module

public import Mathlib

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormPowLeOfEigenvaluesLt
section
open Filter Topology
open scoped NNReal ENNReal

namespace GlobalTheory.CompanionTheory.SpecBound

theorem norm_pow_le_of_eigenvalues_lt (W : Type) [NormedAddCommGroup W] [NormedSpace ℂ W]
    [FiniteDimensional ℂ W] (T : W →L[ℂ] W) (ρ : ℝ)
    (h : ∀ μ : ℂ, Module.End.HasEigenvalue (T : Module.End ℂ W) μ → ‖μ‖ < ρ) :
    ∃ C : ℝ, ∀ j : ℕ, ‖T ^ j‖ ≤ C * ρ ^ j := by
  rcases subsingleton_or_nontrivial W with hW | hW
  · refine ⟨0, fun j => ?_⟩
    have h0 : T ^ j = 0 := by
      ext x
      exact Subsingleton.elim _ _
    simp [h0]
  have : CompleteSpace W := FiniteDimensional.complete ℂ W
  have : Nontrivial (W →L[ℂ] W) :=
    (Module.End.toContinuousLinearMap (𝕜 := ℂ) W).injective.nontrivial
  obtain ⟨z, hz, hzr⟩ := spectrum.exists_nnnorm_eq_spectralRadius T
  have hzE : Module.End.HasEigenvalue (T : Module.End ℂ W) z := by
    rw [Module.End.hasEigenvalue_iff_mem_spectrum]
    have hT : (Module.End.toContinuousLinearMap (𝕜 := ℂ) W) (T : Module.End ℂ W) = T := by
      ext x
      rfl
    rw [← AlgEquiv.spectrum_eq (Module.End.toContinuousLinearMap (𝕜 := ℂ) W), hT]
    exact hz
  have hlt : ‖z‖ < ρ := h z hzE
  have hρ : 0 < ρ := (norm_nonneg z).trans_lt hlt
  let ρ' : ℝ≥0 := ⟨ρ, hρ.le⟩
  have hr : spectralRadius ℂ T < (ρ' : ℝ≥0∞) := by
    rw [← hzr]
    have : ‖z‖₊ < ρ' := by
      rw [← NNReal.coe_lt_coe]
      exact hlt
    exact_mod_cast this
  have hev := (spectrum.pow_nnnorm_pow_one_div_tendsto_nhds_spectralRadius T).eventually_lt_const hr
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hev.and (eventually_gt_atTop 0))
  have key : ∀ n, N ≤ n → ‖T ^ n‖ ≤ ρ ^ n := by
    intro n hn
    obtain ⟨h1, h0⟩ := hN n hn
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast h0.ne'
    have h2 : (‖T ^ n‖₊ : ℝ≥0∞) ≤ (ρ' : ℝ≥0∞) ^ n := by
      have h3 := ENNReal.rpow_le_rpow h1.le (Nat.cast_nonneg n : (0 : ℝ) ≤ (n : ℝ))
      rw [← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hn0, ENNReal.rpow_one,
        ENNReal.rpow_natCast] at h3
      exact h3
    have h4 : ‖T ^ n‖₊ ≤ ρ' ^ n := by exact_mod_cast h2
    have h5 : ((‖T ^ n‖₊ : ℝ≥0) : ℝ) ≤ ((ρ' ^ n : ℝ≥0) : ℝ) := NNReal.coe_le_coe.2 h4
    rw [NNReal.coe_pow, coe_nnnorm] at h5
    exact h5
  refine ⟨1 + ∑ i ∈ Finset.range N, ‖T ^ i‖ / ρ ^ i, fun j => ?_⟩
  have hpow : 0 < ρ ^ j := pow_pos hρ j
  have hsum : 0 ≤ ∑ i ∈ Finset.range N, ‖T ^ i‖ / ρ ^ i :=
    Finset.sum_nonneg fun i _ => div_nonneg (norm_nonneg _) (pow_pos hρ i).le
  by_cases hj : j < N
  · have h6 : ‖T ^ j‖ / ρ ^ j ≤ ∑ i ∈ Finset.range N, ‖T ^ i‖ / ρ ^ i :=
      Finset.single_le_sum (f := fun i => ‖T ^ i‖ / ρ ^ i)
        (fun i _ => div_nonneg (norm_nonneg _) (pow_pos hρ i).le) (Finset.mem_range.2 hj)
    have h7 : ‖T ^ j‖ / ρ ^ j ≤ 1 + ∑ i ∈ Finset.range N, ‖T ^ i‖ / ρ ^ i := by linarith
    exact (div_le_iff₀ hpow).1 h7
  · have h8 := key j (not_lt.1 hj)
    nlinarith [mul_nonneg hsum hpow.le]

end GlobalTheory.CompanionTheory.SpecBound
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NotMemLpOfGrowth
section
open MeasureTheory

namespace GlobalTheory.CompanionTheory.Casselman

theorem mul_rpow_lt_one_of_memLp_geometric {X : Type} [MeasurableSpace X]
    (μ : MeasureTheory.Measure X) (f : X → ℝ) (p : ℝ) (hp : 0 < p)
    (hf : MeasureTheory.MemLp f (ENNReal.ofReal p) μ) (E : ℕ → Set X)
    (hE : ∀ j, MeasurableSet (E j)) (hdisj : Pairwise (Function.onFun Disjoint E))
    (c D B r : ℝ) (hc : 0 < c) (hB : 0 < B) (hr : 0 ≤ r)
    (hμ : ∀ j : ℕ, ENNReal.ofReal (c * D ^ j) ≤ μ (E j))
    (hlow : ∀ j : ℕ, ∀ x ∈ E j, B * r ^ j ≤ |f x|) : D * r ^ p < 1 := by
  by_contra hcon
  have hq : 1 ≤ D * r ^ p := not_lt.1 hcon
  have hrp : 0 ≤ r ^ p := Real.rpow_nonneg hr p
  have hD : 0 ≤ D := by
    by_contra hD
    have : D * r ^ p ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (not_le.1 hD).le hrp
    linarith
  have hp0 : ENNReal.ofReal p ≠ 0 := by simpa using hp
  have hI := (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top hp0 ENNReal.ofReal_ne_top hf.aestronglyMeasurable).1
    hf.eLpNorm_lt_top
  rw [ENNReal.toReal_ofReal hp.le] at hI
  have ha : 0 < c * B ^ p := mul_pos hc (Real.rpow_pos_of_pos hB p)
  have hterm : ∀ j : ℕ, ENNReal.ofReal (c * B ^ p) ≤ ∫⁻ x in E j, ‖f x‖ₑ ^ p ∂μ := by
    intro j
    have hBr : 0 ≤ B * r ^ j := mul_nonneg hB.le (pow_nonneg hr j)
    have h1 : ∫⁻ _ in E j, ENNReal.ofReal ((B * r ^ j) ^ p) ∂μ ≤ ∫⁻ x in E j, ‖f x‖ₑ ^ p ∂μ := by
      refine setLIntegral_mono' (hE j) fun x hx => ?_
      rw [← ENNReal.ofReal_rpow_of_nonneg hBr hp.le, Real.enorm_eq_ofReal_abs]
      exact ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal (hlow j x hx)) hp.le
    rw [setLIntegral_const] at h1
    refine le_trans ?_ h1
    refine le_trans ?_ (mul_le_mul_right (hμ j) _)
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hBr p)]
    refine ENNReal.ofReal_le_ofReal ?_
    have e : (B * r ^ j) ^ p * (c * D ^ j) = c * B ^ p * (D * r ^ p) ^ j := by
      rw [Real.mul_rpow hB.le (pow_nonneg hr j), mul_pow, ← Real.rpow_natCast r j,
        ← Real.rpow_natCast (r ^ p) j, ← Real.rpow_mul hr, ← Real.rpow_mul hr, mul_comm (j : ℝ) p]
      ring
    rw [e]
    exact le_mul_of_one_le_right ha.le (one_le_pow₀ hq)
  have htop : ∑' j : ℕ, ∫⁻ x in E j, ‖f x‖ₑ ^ p ∂μ = ⊤ := by
    refine top_le_iff.1 ?_
    rw [← ENNReal.tsum_const_eq_top_of_ne_zero (α := ℕ)
      (ENNReal.ofReal_pos.2 ha).ne']
    exact ENNReal.tsum_le_tsum hterm
  have hle : ∑' j : ℕ, ∫⁻ x in E j, ‖f x‖ₑ ^ p ∂μ ≤ ∫⁻ x, ‖f x‖ₑ ^ p ∂μ := by
    rw [← lintegral_iUnion hE hdisj]
    exact setLIntegral_le_lintegral _ _
  rw [htop] at hle
  exact absurd (lt_of_le_of_lt hle hI) (lt_irrefl _)

end GlobalTheory.CompanionTheory.Casselman
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProdEntrywiseLe
section
open Finset

namespace GlobalTheory.CompanionTheory.EntrywiseCount

theorem card_lt (n r : ℕ) (hr : r ≤ n) :
    (univ.filter (fun i : Fin n => (i : ℕ) < r)).card = r := by
  have h : (univ.filter (fun i : Fin n => (i : ℕ) < r)).card
      = ((range n).filter (fun i => i < r)).card := by
    rw [Finset.card_filter, Finset.card_filter]
    exact Fin.sum_univ_eq_sum_range (fun i => if i < r then 1 else 0) n
  rw [h]
  have : (range n).filter (fun i => i < r) = range r := by
    ext x
    simp only [mem_filter, mem_range]
    omega
  rw [this, card_range]

theorem card_ge (n r : ℕ) (hr : r ≤ n) :
    (univ.filter (fun j : Fin n => r ≤ (j : ℕ))).card = n - r := by
  have h := Finset.card_filter_add_card_filter_not (s := (univ : Finset (Fin n)))
    (fun i : Fin n => (i : ℕ) < r)
  rw [card_lt n r hr, Finset.card_univ, Fintype.card_fin] at h
  simp only [not_lt] at h
  omega

theorem prod_indicator (n r : ℕ) (hr : r ≤ n) (E : ℝ) :
    ∏ i : Fin n, ∏ j : Fin n, (if (i : ℕ) < r ∧ r ≤ (j : ℕ) then E else 1)
      = E ^ (r * (n - r)) := by
  have inner : ∀ i : Fin n, ∏ j : Fin n, (if (i : ℕ) < r ∧ r ≤ (j : ℕ) then E else 1)
      = if (i : ℕ) < r then E ^ (n - r) else 1 := by
    intro i
    by_cases hi : (i : ℕ) < r
    · simp only [hi, true_and, if_true]
      rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one, card_ge n r hr]
    · simp [hi]
  simp only [inner]
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one, card_lt n r hr,
    ← pow_mul, mul_comm]

theorem factor_le (d : ℕ) (C β t : ℝ) (p : Prop) [Decidable p]
    (hC : 0 ≤ C) (hβ : 0 ≤ β) (ht : 0 ≤ t) :
    C * (1 + β * (if p then Real.exp t else 1)) ^ d
      ≤ (C * (1 + β) ^ d) * (if p then Real.exp ((d : ℝ) * t) else 1) := by
  have hE : 1 ≤ Real.exp t := Real.one_le_exp ht
  have hbase : 1 + β * (if p then Real.exp t else 1)
      ≤ (1 + β) * (if p then Real.exp t else 1) := by
    split_ifs
    · nlinarith
    · linarith
  have hnn : 0 ≤ 1 + β * (if p then Real.exp t else 1) := by
    split_ifs <;> positivity
  have hpow := pow_le_pow_left₀ hnn hbase d
  rw [mul_pow] at hpow
  have hE' : (if p then Real.exp t else 1) ^ d = (if p then Real.exp ((d : ℝ) * t) else 1) := by
    split_ifs
    · rw [← Real.exp_nat_mul]
    · simp
  rw [hE'] at hpow
  calc C * (1 + β * (if p then Real.exp t else 1)) ^ d
      ≤ C * ((1 + β) ^ d * (if p then Real.exp ((d : ℝ) * t) else 1)) :=
        mul_le_mul_of_nonneg_left hpow hC
    _ = _ := by ring

theorem prod_entrywise_le : ∀ (n r d : ℕ), r ≤ n → ∀ (C β t : ℝ), 0 ≤ C → 0 ≤ β → 0 ≤ t →
    ∏ i : Fin n, ∏ j : Fin n,
        C * (1 + β * (if (i : ℕ) < r ∧ r ≤ (j : ℕ) then Real.exp t else 1)) ^ d
      ≤ C ^ (n * n) * (1 + β) ^ (d * (n * n))
        * Real.exp ((d : ℝ) * ((r : ℝ) * ((n : ℝ) - r)) * t) := by
  intro n r d hr C β t hC hβ ht
  have hnn : ∀ (i j : Fin n), 0 ≤
      C * (1 + β * (if (i : ℕ) < r ∧ r ≤ (j : ℕ) then Real.exp t else 1)) ^ d := by
    intro i j
    have : 0 ≤ (if (i : ℕ) < r ∧ r ≤ (j : ℕ) then Real.exp t else 1) := by
      split_ifs <;> positivity
    positivity
  have step : ∏ i : Fin n, ∏ j : Fin n,
        C * (1 + β * (if (i : ℕ) < r ∧ r ≤ (j : ℕ) then Real.exp t else 1)) ^ d
      ≤ ∏ i : Fin n, ∏ j : Fin n, ((C * (1 + β) ^ d) *
          (if (i : ℕ) < r ∧ r ≤ (j : ℕ) then Real.exp ((d : ℝ) * t) else 1)) := by
    apply Finset.prod_le_prod₀
    · intro i _
      exact Finset.prod_nonneg (fun j _ => hnn i j)
    · intro i _
      apply Finset.prod_le_prod₀
      · intro j _
        exact hnn i j
      · intro j _
        exact factor_le d C β t _ hC hβ ht
  refine step.trans (le_of_eq ?_)
  simp only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [prod_indicator n r hr, ← Real.exp_nat_mul, ← pow_mul]
  have hp : (((1 + β) ^ d) ^ n) ^ n = (1 + β) ^ (d * (n * n)) := by
    rw [← pow_mul, ← pow_mul]
  have : (((r * (n - r) : ℕ) : ℝ)) * ((d : ℝ) * t) = (d : ℝ) * ((r : ℝ) * ((n : ℝ) - r)) * t := by
    rw [Nat.cast_mul, Nat.cast_sub hr]
    ring
  rw [this]
  rw [hp]

end GlobalTheory.CompanionTheory.EntrywiseCount
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProdRelIndexNeZero
section
namespace GlobalTheory.CompanionTheory.GroupIndex.RelProd

theorem relIndex_prod_eq_mul {G₁ G₂ : Type} [Group G₁] [Group G₂]
    (I₁ K₁ : Subgroup G₁) (I₂ K₂ : Subgroup G₂) :
    (I₁.prod I₂).relIndex (K₁.prod K₂) = I₁.relIndex K₁ * I₂.relIndex K₂ := by
  have hmap : ((I₁.prod I₂).subgroupOf (K₁.prod K₂)) =
      ((I₁.subgroupOf K₁).prod (I₂.subgroupOf K₂)).comap
        (Subgroup.prodEquiv K₁ K₂).toMonoidHom := by
    ext x
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_prod, Subgroup.mem_comap]
    exact Iff.rfl
  unfold Subgroup.relIndex
  rw [hmap, Subgroup.index_comap_of_surjective _ (Subgroup.prodEquiv K₁ K₂).surjective,
    Subgroup.index_prod]

theorem relIndex_prod_ne_zero_of_ne_zero :
    ∀ (G₁ G₂ : Type) [Group G₁] [Group G₂] (I₁ K₁ : Subgroup G₁) (I₂ K₂ : Subgroup G₂),
      I₁.relIndex K₁ ≠ 0 → I₂.relIndex K₂ ≠ 0 → (I₁.prod I₂).relIndex (K₁.prod K₂) ≠ 0 := by
  intro G₁ G₂ _ _ I₁ K₁ I₂ K₂ h₁ h₂
  rw [relIndex_prod_eq_mul]
  exact mul_ne_zero h₁ h₂

end GlobalTheory.CompanionTheory.GroupIndex.RelProd
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductNeighbourhoodsShrinkCompactOpen
section
open MeasureTheory

namespace GlobalTheory.CompanionTheory.BigCell

theorem preimage_box_shrinking : ∀ (G A ι : Type) [AddCommGroup G] [TopologicalSpace G] [AddCommGroup A] [TopologicalSpace A] [Finite ι] (e : G ≃ₜ+ (ι → A)) (U : ℕ → Set A), (∀ k, IsCompact (U k) ∧ IsOpen (U k) ∧ (0 : A) ∈ U k) → Filter.Tendsto U Filter.atTop (nhds (0 : A)).smallSets → (∀ k, IsCompact (e ⁻¹' Set.pi Set.univ (fun _ => U k)) ∧ IsOpen (e ⁻¹' Set.pi Set.univ (fun _ => U k)) ∧ (0 : G) ∈ e ⁻¹' Set.pi Set.univ (fun _ => U k)) ∧ Filter.Tendsto (fun k => e ⁻¹' Set.pi Set.univ (fun _ => U k)) Filter.atTop (nhds (0 : G)).smallSets := by
  intro G A ι _ _ _ _ _ e U hU hlim
  refine ⟨fun k => ⟨?_, ?_, ?_⟩, ?_⟩
  · exact e.toHomeomorph.isCompact_preimage.2 (isCompact_univ_pi fun _ => (hU k).1)
  · exact (isOpen_set_pi Set.finite_univ fun _ _ => (hU k).2.1).preimage e.continuous
  · show e 0 ∈ Set.pi Set.univ (fun _ => U k)
    rw [map_zero]
    exact Set.mem_univ_pi.2 fun _ => (hU k).2.2
  · rw [Filter.tendsto_smallSets_iff] at hlim ⊢
    intro t ht
    have hc : Filter.Tendsto e.symm (nhds 0) (nhds 0) := by
      have h0 : Filter.Tendsto e.symm (nhds 0) (nhds (e.symm 0)) := e.symm.continuous.tendsto 0
      rw [map_zero] at h0
      exact h0
    have h1 : e.symm ⁻¹' t ∈ nhds (0 : ι → A) := hc ht
    rw [nhds_pi, Filter.mem_pi'] at h1
    obtain ⟨I, s, hs, hsub⟩ := h1
    have hW : (⋂ i, s i) ∈ nhds (0 : A) := Filter.iInter_mem.2 hs
    filter_upwards [hlim _ hW] with k hk
    intro x hx
    have h2 : e x ∈ Set.pi (I : Set ι) s := fun i _ =>
      Set.mem_iInter.1 (hk (hx i (Set.mem_univ i))) i
    simpa using hsub h2

end GlobalTheory.CompanionTheory.BigCell
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QuotientMeasureByInvariantSubgroup
section
open MeasureTheory Topology
open scoped ENNReal NNReal

namespace GlobalTheory.CompanionTheory.Shear

theorem lintegral_shear_eq : ∀ (V A : Type) [AddCommGroup V] [AddCommGroup A] [MeasurableSpace V]
    [MeasurableSpace A] [MeasurableAdd₂ V] [MeasurableAdd₂ A] [MeasurableNeg A] [MeasurableNeg V]
    (μ : Measure V) (lam : Measure A) [SFinite μ] [SFinite lam] [μ.IsAddRightInvariant]
    [lam.IsAddRightInvariant] (j : A →+ V), Measurable j → ∀ f : V → A, Measurable f →
    (∀ v a, f (v + j a) = f v) → ∀ K : Set A, MeasurableSet K → lam K ≠ 0 → lam K ≠ ⊤ →
    ∀ ψ : V → ℝ≥0∞, Measurable ψ → ∫⁻ v, ψ (v + j (f v)) ∂μ = ∫⁻ v, ψ v ∂μ := by
  intro V A _ _ _ _ _ _ _ _ μ lam _ _ _ _ j hj f hf hfinv K hK hK0 hKtop ψ hψ
  classical
  have hind : Measurable (K.indicator (1 : A → ℝ≥0∞)) := measurable_one.indicator hK
  have hind_ne : ∀ a, K.indicator (1 : A → ℝ≥0∞) a ≠ ⊤ := fun a => by
    rw [Set.indicator_apply]
    split_ifs <;> simp
  have hfneg : ∀ v a, f (v + -j a) = f v := fun v a => by
    rw [← map_neg]
    exact hfinv v (-a)
  have sA : ∀ a, ∫⁻ v, ψ (v + j a + j (f v)) ∂μ = ∫⁻ v, ψ (v + j (f v)) ∂μ := fun a =>
    (lintegral_add_right_eq_self (μ := μ) (fun v => ψ (v + j a + j (f v))) (-(j a))).symm.trans
      (lintegral_congr fun v => by simp only [neg_add_cancel_right, hfneg])
  have sB : ∀ v, ∫⁻ a, K.indicator (1 : A → ℝ≥0∞) a * ψ (v + j a + j (f v)) ∂lam =
      ∫⁻ a, K.indicator (1 : A → ℝ≥0∞) (a + -f v) * ψ (v + j a) ∂lam := fun v =>
    (lintegral_add_right_eq_self (μ := lam) (fun a => K.indicator (1 : A → ℝ≥0∞) a * ψ (v + j a + j (f v))) (-(f v))).symm.trans
      (lintegral_congr fun a => by simp only [map_add (f := _), map_neg, add_assoc, neg_add_cancel, add_zero])
  have sC : ∀ a, ∫⁻ v, K.indicator (1 : A → ℝ≥0∞) (a + -f v) * ψ (v + j a) ∂μ = ∫⁻ v, K.indicator (1 : A → ℝ≥0∞) (a + -f v) * ψ v ∂μ :=
    fun a => (lintegral_add_right_eq_self (μ := μ) (fun v => K.indicator (1 : A → ℝ≥0∞) (a + -f v) * ψ (v + j a)) (-(j a))).symm.trans
      (lintegral_congr fun v => by simp only [neg_add_cancel_right, hfneg])
  have sD : ∀ v, ∫⁻ a, K.indicator (1 : A → ℝ≥0∞) (a + -f v) * ψ v ∂lam = lam K * ψ v := fun v => by
    have hm : Measurable fun a => K.indicator (1 : A → ℝ≥0∞) (a + -f v) := hind.comp (measurable_add_const (-f v))
    rw [lintegral_mul_const _ hm, lintegral_add_right_eq_self (μ := lam) (K.indicator (1 : A → ℝ≥0∞)) (-f v),
      lintegral_indicator_one hK]
  have hm1 : Measurable fun p : A × V => K.indicator (1 : A → ℝ≥0∞) p.1 * ψ (p.2 + j p.1 + j (f p.2)) :=
    (hind.comp measurable_fst).mul
      (hψ.comp ((measurable_snd.add (hj.comp measurable_fst)).add (hj.comp (hf.comp measurable_snd))))
  have hm2 : Measurable fun p : V × A => K.indicator (1 : A → ℝ≥0∞) (p.2 + -f p.1) * ψ (p.1 + j p.2) :=
    (hind.comp (measurable_snd.add (hf.comp measurable_fst).neg)).mul
      (hψ.comp (measurable_fst.add (hj.comp measurable_snd)))
  have hm3 : Measurable fun p : A × V => K.indicator (1 : A → ℝ≥0∞) (p.1 + -f p.2) * ψ p.2 :=
    (hind.comp (measurable_fst.add (hf.comp measurable_snd).neg)).mul (hψ.comp measurable_snd)
  have key : lam K * ∫⁻ v, ψ (v + j (f v)) ∂μ = lam K * ∫⁻ v, ψ v ∂μ := by
    calc lam K * ∫⁻ v, ψ (v + j (f v)) ∂μ
        = ∫⁻ a, K.indicator (1 : A → ℝ≥0∞) a * ∫⁻ v, ψ (v + j a + j (f v)) ∂μ ∂lam := by
          simp_rw [sA]
          rw [lintegral_mul_const _ hind, lintegral_indicator_one hK]
      _ = ∫⁻ a, ∫⁻ v, K.indicator (1 : A → ℝ≥0∞) a * ψ (v + j a + j (f v)) ∂μ ∂lam := by
          refine lintegral_congr fun a => ?_
          rw [lintegral_const_mul' _ _ (hind_ne a)]
      _ = ∫⁻ v, ∫⁻ a, K.indicator (1 : A → ℝ≥0∞) a * ψ (v + j a + j (f v)) ∂lam ∂μ :=
          lintegral_lintegral_swap hm1.aemeasurable
      _ = ∫⁻ v, ∫⁻ a, K.indicator (1 : A → ℝ≥0∞) (a + -f v) * ψ (v + j a) ∂lam ∂μ := lintegral_congr fun v => sB v
      _ = ∫⁻ a, ∫⁻ v, K.indicator (1 : A → ℝ≥0∞) (a + -f v) * ψ (v + j a) ∂μ ∂lam :=
          lintegral_lintegral_swap hm2.aemeasurable
      _ = ∫⁻ a, ∫⁻ v, K.indicator (1 : A → ℝ≥0∞) (a + -f v) * ψ v ∂μ ∂lam := lintegral_congr fun a => sC a
      _ = ∫⁻ v, ∫⁻ a, K.indicator (1 : A → ℝ≥0∞) (a + -f v) * ψ v ∂lam ∂μ :=
          lintegral_lintegral_swap hm3.aemeasurable
      _ = ∫⁻ v, lam K * ψ v ∂μ := lintegral_congr fun v => sD v
      _ = lam K * ∫⁻ v, ψ v ∂μ := lintegral_const_mul' _ _ hKtop
  exact (ENNReal.mul_right_inj hK0 hKtop).mp key

end GlobalTheory.CompanionTheory.Shear
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RangeVecMulLinearEq
section
namespace GlobalTheory.CompanionTheory.MatrixRowSpace

variable {K : Type} [Field K]

theorem row_mul {m n r : ℕ} (x : Matrix (Fin m) (Fin r) K) (c : Matrix (Fin r) (Fin n) K)
    (i : Fin m) : (x * c) i = c.vecMulLinear (x i) := by
  ext j
  simp [Matrix.mul_apply, Matrix.vecMul, dotProduct]

theorem range_vecMulLinear_eq {n r : ℕ} (c : Matrix (Fin r) (Fin n) K) :
    LinearMap.range c.vecMulLinear = Submodule.span K (Set.range c) := by
  apply le_antisymm
  · rintro _ ⟨v, rfl⟩
    rw [Matrix.vecMulLinear_apply, Matrix.vecMul_eq_sum]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    refine ⟨Pi.single i 1, ?_⟩
    ext j
    simp [Matrix.vecMul, dotProduct, Pi.single_apply]

theorem span_rows_mul {m n r : ℕ} (x : Matrix (Fin m) (Fin r) K) (c : Matrix (Fin r) (Fin n) K) :
    Submodule.span K (Set.range (x * c)) =
      (Submodule.span K (Set.range x)).map c.vecMulLinear := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    rw [row_mul]
    exact Submodule.mem_map_of_mem (Submodule.subset_span ⟨i, rfl⟩)
  · rw [Submodule.map_le_iff_le_comap, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_comap, ← row_mul]
    exact Submodule.subset_span ⟨i, rfl⟩

theorem span_rows_eq_top_iff {m r : ℕ} (x : Matrix (Fin m) (Fin r) K) :
    x.rank = r ↔ Submodule.span K (Set.range x) = ⊤ := by
  rw [Matrix.rank_eq_finrank_span_row]
  constructor
  · intro h
    exact Submodule.eq_top_of_finrank_eq (h.trans (by simp))
  · intro h
    have h' : Submodule.span K (Set.range x.row) = ⊤ := h
    rw [h', finrank_top]
    simp

theorem span_rows_mul_of_rank {m n r : ℕ} (x : Matrix (Fin m) (Fin r) K)
    (c : Matrix (Fin r) (Fin n) K) (hx : x.rank = r) :
    Submodule.span K (Set.range (x * c)) = Submodule.span K (Set.range c) := by
  rw [span_rows_mul, (span_rows_eq_top_iff x).mp hx, Submodule.map_top, range_vecMulLinear_eq]

end GlobalTheory.CompanionTheory.MatrixRowSpace
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RetractBaseChangeKernelCompatible
section
open TensorProduct

namespace GlobalTheory.CompanionTheory.Retract

theorem constants_of_retract :
    ∀ (R R' M A₀ A₁ B₀ B₁ : Type) [CommRing R] [CommRing R'] [Algebra R R'] [AddCommGroup M] [Module R M] [AddCommGroup A₀] [Module R A₀] [AddCommGroup A₁] [Module R A₁] [AddCommGroup B₀] [Module R' B₀] [AddCommGroup B₁] [Module R' B₁] (i : M →ₗ[R] R') (j : R' →ₗ[R] M) (d₀ : A₀ →ₗ[R] A₁) (d' : B₀ →ₗ[R'] B₁) (E₀ : R' ⊗[R] A₀ ≃ₗ[R'] B₀) (E₁ : R' ⊗[R] A₁ ≃ₗ[R'] B₁) (e : A₀), j ∘ₗ i = LinearMap.id → (∀ x, E₁ (d₀.baseChange R' x) = d' (E₀ x)) → (∀ r : R', r • E₀ (1 ⊗ₜ e) = 0 → r = 0) → (∀ z, d' z = 0 → ∃ r : R', r • E₀ (1 ⊗ₜ e) = z) → Function.Injective (fun m : M ↦ m ⊗ₜ[R] e) ∧ ∀ x : M ⊗[R] A₀, d₀.lTensor M x = 0 → ∃ m : M, m ⊗ₜ[R] e = x := by
  intro R R' M A₀ A₁ B₀ B₁ _ _ _ _ _ _ _ _ _ _ _ _ _ i j d₀ d' E₀ E₁ e hji hcomm hfree hker
  have htm : ∀ r : R', r • E₀ (1 ⊗ₜ e) = E₀ (r ⊗ₜ[R] e) := by
    intro r
    rw [← map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  have hinjR : ∀ r : R', r ⊗ₜ[R] e = 0 → r = 0 := by
    intro r hr
    apply hfree
    rw [htm, hr, map_zero]
  have hkerR : ∀ y : R' ⊗[R] A₀, d₀.baseChange R' y = 0 → ∃ r : R', r ⊗ₜ[R] e = y := by
    intro y hy
    obtain ⟨r, hr⟩ := hker (E₀ y) (by rw [← hcomm, hy, map_zero])
    exact ⟨r, E₀.injective (by rw [← htm, hr])⟩
  have hji' : ∀ m : M, j (i m) = m := fun m => by
    rw [← LinearMap.comp_apply, hji, LinearMap.id_apply]
  have hret : ∀ x : M ⊗[R] A₀, j.rTensor A₀ (i.rTensor A₀ x) = x := by
    intro x
    rw [← LinearMap.rTensor_comp_apply, hji, LinearMap.rTensor_id_apply]
  have hnat : ∀ x : M ⊗[R] A₀,
      d₀.baseChange R' (i.rTensor A₀ x) = i.rTensor A₁ (d₀.lTensor M x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul m a => simp [LinearMap.baseChange_tmul]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  refine ⟨?_, ?_⟩
  · intro m m' h
    have h0 : m ⊗ₜ[R] e = m' ⊗ₜ[R] e := h
    have h1 : (i m - i m') ⊗ₜ[R] e = 0 := by
      have h2 := congrArg (i.rTensor A₀) h0
      simp only [LinearMap.rTensor_tmul] at h2
      rw [TensorProduct.sub_tmul, h2, sub_self]
    have h3 : i m = i m' := sub_eq_zero.mp (hinjR _ h1)
    rw [← hji' m, ← hji' m', h3]
  · intro x hx
    obtain ⟨r, hr⟩ := hkerR (i.rTensor A₀ x) (by rw [hnat, hx, map_zero])
    refine ⟨j r, ?_⟩
    rw [← hret x, ← hr, LinearMap.rTensor_tmul]

end GlobalTheory.CompanionTheory.Retract
end

