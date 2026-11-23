module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArith
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0019
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0011
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0022
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0025
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0024
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0023
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0026

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.WhittakerFunctional
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 Filter Topology

noncomputable section

set_option linter.unusedSectionVars false

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem G5.fderiv_fderiv_eq_of_add_const {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {f g : E → ℝ} {y : E}
    (b : ℝ) (h : ∀ᶠ y' in 𝓝 y, f y' = g y' + b) : fderiv ℝ (fderiv ℝ f) y = fderiv ℝ (fderiv ℝ g) y := by
  apply Filter.EventuallyEq.fderiv_eq
  filter_upwards [h.eventually_nhds] with y' hy'
  have hfg : f =ᶠ[𝓝 y'] fun x => g x + b := hy'
  rw [hfg.fderiv_eq, fderiv_add_const]

theorem G5.ptsIntegral_eq_of_add_const {e : ℕ} (P : Ideal (MRing ι)) (φ ψ : Fin e → ((Σ k, ι k) → ℂ) → ℝ)
    (h : ∀ j, ∃ b : ℝ, ∀ z ∈ mcPts P, φ j z = ψ j z + b) (g : ((Σ k, ι k) → ℂ) → ℝ) :
    ptsIntegral P φ g = ptsIntegral P ψ g := by
  have hs : ∀ Ψ y w, sheetDensity P Ψ φ g y w = sheetDensity P Ψ ψ g y w := by
    intro Ψ y w
    unfold sheetDensity
    split_ifs with hγ
    · congr 1
      have hH : ∀ j, cxHessian (fun y' => φ j (hγ.choose y')) y = cxHessian (fun y' => ψ j (hγ.choose y')) y := by
        intro j
        obtain ⟨b, hb⟩ := h j
        have hev : ∀ᶠ y' in 𝓝 y, φ j (hγ.choose y') = ψ j (hγ.choose y') + b :=
          hγ.choose_spec.2.mono fun y' hy' => hb _ hy'.2.1
        unfold cxHessian
        rw [G5.fderiv_fderiv_eq_of_add_const b hev]
      simp only [maDensity, hH]
    · rfl
  unfold ptsIntegral ptsIntegralAt
  simp only [hs]

theorem G5.ptsIntegral_const {e : ℕ} (P : Ideal (MRing ι)) (φ : Fin e → ((Σ k, ι k) → ℂ) → ℝ) (c : ℝ) :
    ptsIntegral P φ (fun _ => c) = c * ptsIntegral P φ (fun _ => 1) := by
  unfold ptsIntegral
  split_ifs with hΨ
  · unfold ptsIntegralAt
    rw [← MeasureTheory.integral_const_mul]
    congr 1
    funext y
    rw [mul_finsum_mem]
    refine finsum_mem_congr rfl fun w _ => ?_
    unfold sheetDensity
    split_ifs <;> ring
  · simp

theorem G5.isSmoothHerm_constLine (c : ℝ) : IsSmoothHerm (constLine (ι := ι) c) := by
  show ContDiffOn ℝ _ (fun _ => Real.exp (-c)) _
  exact contDiffOn_const

theorem G5.log_tensor_constLine (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (c : ℝ) (z : (Σ k, ι k) → ℂ) (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) :
    Real.log ((A.tensor (constLine c)).h z) = Real.log (A.h z) + -c := by
  show Real.log (A.h z * Real.exp (-c)) = _
  rw [Real.log_mul (A.pos z hz).ne' (Real.exp_pos _).ne', Real.log_exp]

theorem G5.top_tensor_constLine (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) → ℝ)
    (hI : IsIntersectionFamily I) (P : Ideal (MRing ι)) (D : ℕ) (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (c : ℝ)
    (hP : IsArithVar P (D + 1)) (hA : IsSmoothHerm A) :
    I P (D + 1) (fun _ => A.tensor (constLine c)) =
      I P (D + 1) (fun _ => A) - ((D + 1 : ℕ) : ℝ) * c * geomDeg P A D := by
  set A' := A.tensor (constLine (ι := ι) c) with hA'def
  have hA' : IsSmoothHerm A' := hA.mul (G5.isSmoothHerm_constLine c)
  let L : ℕ → Fin (D + 1) → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι := fun k j => if (j : ℕ) < k then A' else A
  have hL2 : ∀ k j, L k j = A ∨ L k j = A' := fun k j => by
    by_cases h : (j : ℕ) < k
    · exact Or.inr (if_pos h)
    · exact Or.inl (if_neg h)
  have hLs : ∀ k j, IsSmoothHerm (L k j) := fun k j => (hL2 k j).elim (fun h => h ▸ hA) (fun h => h ▸ hA')

  have hint : ∀ M : Fin D → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι, (∀ j, M j = A ∨ M j = A') →
      ptsIntegral P (pot M) (fun _ => c) = c * geomDeg P A D := by
    intro M hM
    rw [G5.ptsIntegral_const]
    congr 1
    refine G5.ptsIntegral_eq_of_add_const P _ _ (fun j => ?_) _
    rcases hM j with h | h
    · exact ⟨0, fun z _ => by simp [pot, h]⟩
    · exact ⟨-c, fun z hz => by simp only [pot, h]; exact G5.log_tensor_constLine A c z hz.1⟩
  have step : ∀ k, k ≤ D + 1 → I P (D + 1) (L k) = I P (D + 1) (fun _ => A) - (k : ℝ) * c * geomDeg P A D := by
    intro k
    induction k with
    | zero =>
      intro _
      have : L 0 = fun _ => A := by funext j; simp [L]
      rw [this]; simp
    | succ k ih =>
      intro hk
      have hkD : k < D + 1 := by omega
      set i : Fin (D + 1) := ⟨k, hkD⟩
      set σ := Equiv.swap i (Fin.last D)
      set M : Fin D → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι := fun j => L (k + 1) (σ (Fin.castSucc j))
      have hne : ∀ j : Fin D, σ (Fin.castSucc j) ≠ i := by
        intro j hj
        rw [Equiv.swap_apply_eq_iff, Equiv.swap_apply_left] at hj
        exact (Fin.castSucc_lt_last j).ne hj
      have hMk : ∀ j : Fin D, L k (σ (Fin.castSucc j)) = M j := by
        intro j
        have h1 : ((σ (Fin.castSucc j) : Fin (D + 1)) : ℕ) ≠ k := fun h => hne j (Fin.ext h)
        simp only [M, L]
        by_cases h2 : ((σ (Fin.castSucc j) : Fin (D + 1)) : ℕ) < k
        · rw [if_pos h2, if_pos (by omega)]
        · rw [if_neg h2, if_neg (by omega)]
      have hσi : σ (Fin.last D) = i := Equiv.swap_apply_right _ _
      have e1 : L (k + 1) ∘ σ = Fin.snoc M A' := by
        funext x
        refine Fin.lastCases ?_ (fun j => ?_) x
        · simp only [Function.comp_apply, Fin.snoc_last, hσi, L, i]
          exact if_pos (Nat.lt_succ_self k)
        · simp only [Function.comp_apply, Fin.snoc_castSucc, M]
      have e0 : L k ∘ σ = Fin.snoc M A := by
        funext x
        refine Fin.lastCases ?_ (fun j => ?_) x
        · simp only [Function.comp_apply, Fin.snoc_last, hσi, L, i]
          exact if_neg (lt_irrefl k)
        · simp only [Function.comp_apply, Fin.snoc_castSucc]
          exact hMk j
      have hM : ∀ j, M j = A ∨ M j = A' := fun j => hL2 _ _
      have hMs : ∀ j, IsSmoothHerm (M j) := fun j => hLs _ _
      have hmc := metricChange K ι I hI P D M A (fun _ => c) (fun _ _ _ => rfl) hP hMs hA contDiffOn_const
      have s1 := hI.1 P (D + 1) (L (k + 1)) σ hP (hLs _)
      have s0 := hI.1 P (D + 1) (L k) σ hP (hLs _)
      rw [e1] at s1
      rw [e0] at s0
      have hsnoc : I P (D + 1) (Fin.snoc M A') =
          I P (D + 1) (Fin.snoc M A) - ptsIntegral P (pot M) (fun _ => c) := hmc
      rw [← s1, hsnoc, s0, ih (by omega), hint M hM]
      push_cast
      ring
  have hall : L (D + 1) = fun _ => A' := by
    funext j
    exact if_pos j.isLt
  have := step (D + 1) le_rfl
  rw [hall] at this
  rw [this]

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ZcombIsConjInvariantH
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

set_option linter.unusedSectionVars false

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem HermLine.zcomb_isConjInvariantH {A B : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι} (hA : ReciprocityTheory.ChartRestriction.G.Geo.IsConjInvariantH A) (hB : ReciprocityTheory.ChartRestriction.G.Geo.IsConjInvariantH B)
    (p q : ℤ) : ReciprocityTheory.ChartRestriction.G.Geo.IsConjInvariantH (HermLine.zcomb A B p q) := fun z => by
  show A.h _ ^ p * B.h _ ^ q = A.h z ^ p * B.h z ^ q
  rw [hA z, hB z]

theorem fsH_isConjInvariantH (ι : K → Type) [∀ k, Fintype (ι k)] : ReciprocityTheory.ChartRestriction.G.Geo.IsConjInvariantH (fsH ι) := fun z => by
  show ∏ k, (fsMetric (ι := ι k)).ρ (fun i => (starRingEnd ℂ) (z ⟨k, i⟩)) ^ (1 : K → ℤ) k =
    ∏ k, (fsMetric (ι := ι k)).ρ (fun i => z ⟨k, i⟩) ^ (1 : K → ℤ) k
  exact Finset.prod_congr rfl fun k _ => by rw [ProjLine.isConjInvariant_fs (fun i => z ⟨k, i⟩)]

theorem zcomb_metric_identity {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (q k p n : ℕ) :
    a ^ (q * n) = (a ^ ((q : ℤ) - k * p) * b ^ (p : ℤ)) ^ n * (a ^ (k : ℤ) * b ^ (-1 : ℤ)) ^ (p * n) := by
  rw [← zpow_natCast a, ← zpow_natCast (_ * _) n, ← zpow_natCast (_ * _) (p * n), mul_zpow, mul_zpow,
    ← zpow_mul, ← zpow_mul, ← zpow_mul, ← zpow_mul, mul_mul_mul_comm, ← zpow_add₀ ha, ← zpow_add₀ hb]
  have e1 : ((q : ℤ) - k * p) * (n : ℤ) + (k : ℤ) * ((p * n : ℕ) : ℤ) = ((q * n : ℕ) : ℤ) := by push_cast; ring
  have e2 : (p : ℤ) * (n : ℤ) + (-1 : ℤ) * ((p * n : ℕ) : ℤ) = 0 := by push_cast; ring
  rw [e1, e2, zpow_zero, mul_one]

theorem G2.proof (hK : KodairaSection.Statement) (hS : SectionProduct.Statement)
    (hP : PerturbSemipos.Statement) (hG : NefAmpleGeneric.Statement) (hF : NefAmpleFibre.Statement)
    (hL : ZCombLimit.Statement) : G2.Statement := by
  intro K _ _ ι _ _ Ω _ _ y D M P0 II hD hII har hb hM
  obtain ⟨k, e, C, hk, hC, he0, he, heb⟩ := hK K ι Ω y D M P0 hD har hb hM
  have hHs : IsSmoothHerm (fsH ι) := by
    have h := (hP K ι P0 (mCoordIdeal y) M 0 1 hM.semipos le_rfl zero_le_one).1
    have h' : (HermLine.zcomb M (fsH ι) 0 1).h = (fsH ι).h := by
      funext z
      simp [HermLine.zcomb]
    unfold IsSmoothHerm at h ⊢
    rwa [h'] at h
  refine ⟨k, e, C, hk, hC, he0, he, heb, fun p q hp hpq => ?_,
    hL K ι Ω y D M (fsH ι) II k hII har hM.semipos.1 hHs⟩
  have hkq : k * p ≤ q := hpq.le
  have ha : (HermLine.zcomb M (fsH ι) ((q : ℤ) - k * p) p).a =
      ((q - k * p : ℕ) : ℤ) • M.a + fun _ => ((p : ℕ) : ℤ) := by
    funext i
    simp [HermLine.zcomb, fsH, HermLine.ofMetrics, Nat.cast_sub hkq]
  have hb0 : (0 : ℤ) ≤ (q : ℤ) - k * p := by
    have : ((k * p : ℕ) : ℤ) ≤ q := by exact_mod_cast hkq
    push_cast at this
    linarith
  refine ⟨hP K ι P0 (mCoordIdeal y) M _ _ hM.semipos hb0 (Nat.cast_nonneg p),
    HermLine.zcomb_isConjInvariantH hM.conjInv (fsH_isConjInvariantH ι) _ _, ?_, fun ℓ hℓ => ?_, ?_⟩
  · rw [ha]
    exact hG K ι Ω y D M P0 (q - k * p) p har hM.normalForm_baseLattice_le_dualSpan_sup_line hM.semipos (by omega) hp
  · rw [ha]
    exact hF K ι Ω y D M.a (q - k * p) p ℓ har hM.nef (by omega) hp hℓ
  intro n s hs
  have hB : e ∈ chartLat y (HermLine.zcomb M (fsH ι) k (-1)).a 1 := by
    have h' : (HermLine.zcomb M (fsH ι) k (-1)).a = (k : ℤ) • M.a - 1 := by
      funext i
      simp [HermLine.zcomb, fsH, HermLine.ofMetrics]
      ring
    rw [h']
    exact he
  have hdeg : ((q * n : ℕ) : ℤ) • M.a = (n : ℤ) • (HermLine.zcomb M (fsH ι) ((q : ℤ) - k * p) p).a +
      ((p * n : ℕ) : ℤ) • (HermLine.zcomb M (fsH ι) k (-1)).a := by
    funext i
    simp [HermLine.zcomb, fsH, HermLine.ofMetrics]
    ring
  have hmet : ∀ z ∈ mcPts (mCoordIdeal y), M.h z ^ (q * n) =
      (HermLine.zcomb M (fsH ι) ((q : ℤ) - k * p) p).h z ^ n *
        (HermLine.zcomb M (fsH ι) k (-1)).h z ^ (p * n) := fun z hz =>
    zcomb_metric_identity (M.pos z hz.1).ne' ((fsH ι).pos z hz.1).ne' q k p n
  obtain ⟨hmem, hbd⟩ := hS K ι Ω y (HermLine.zcomb M (fsH ι) ((q : ℤ) - k * p) p)
    (HermLine.zcomb M (fsH ι) k (-1)) M n (p * n) (q * n) s e hdeg hmet hs hB
  refine ⟨hmem, fun c hc => ?_⟩
  have h := hbd c (Real.exp C) hc heb
  rwa [← Real.exp_nat_mul] at h

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

