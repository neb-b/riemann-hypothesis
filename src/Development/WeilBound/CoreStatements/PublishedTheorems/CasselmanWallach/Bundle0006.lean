module

public import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.FunctionalCalculusLaws
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirAlgebra.Bundle0001
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0063
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0049

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.MaximumPrincipleOfFacts
section
noncomputable section

open Matrix Finset ReciprocityTheory.ChartRestriction.DS

namespace PositivityTheory.CW

namespace MaximumPrincipleOneFunction

variable {n : ℕ}

theorem step (hB3 : B3) (hB3g : UnitaryGroupFacts) (ε : Fin n → Bool) (r : ℕ) (u : Matrix (Fin n) (Fin n) ℂ → ℝ) (A η : ℝ)
    (g0 : Matrix (Fin n) (Fin n) ℂ)
    (hmax : ∀ g ∈ UJset ε, u g - A * (1 + hs2 g) ^ r - η * (1 + hs2 g) ^ (r + 1) ≤
      u g0 - A * (1 + hs2 g0) ^ r - η * (1 + hs2 g0) ^ (r + 1))
    (hg0 : g0 ∈ UJset ε) (p : Fin n × Fin n) (hp : p ∈ nc ε)
    (u' : ℝ → ℝ) (d : ℝ)
    (hu' : ∀ t, HasDerivAt (fun t : ℝ => u (g0 * NormedSpace.exp (t • Xp p.1 p.2))) (u' t) t)
    (hd : HasDerivAt u' d 0)
    (v' : ℝ → ℝ) (v'' : ℝ)
    (hv' : ∀ t, HasDerivAt (fun t : ℝ => (1 + hs2 (g0 * NormedSpace.exp (t • Xp p.1 p.2))) ^ r) (v' t) t)
    (hv'' : HasDerivAt v' v'' 0)
    (w' : ℝ → ℝ) (w'' : ℝ)
    (hw' : ∀ t, HasDerivAt (fun t : ℝ => (1 + hs2 (g0 * NormedSpace.exp (t • Xp p.1 p.2))) ^ (r + 1)) (w' t) t)
    (hw'' : HasDerivAt w' w'' 0) :
    d - A * v'' - η * w'' ≤ 0 := by
  obtain ⟨-, -, hmem, -, -, hX⟩ := hB3g n ε
  have hXp := hX p hp
  refine hB3 (fun t => u (g0 * NormedSpace.exp (t • Xp p.1 p.2)) -
      A * (1 + hs2 (g0 * NormedSpace.exp (t • Xp p.1 p.2))) ^ r -
      η * (1 + hs2 (g0 * NormedSpace.exp (t • Xp p.1 p.2))) ^ (r + 1))
    (fun t => u' t - A * v' t - η * w' t) _ ?_ ?_ ?_
  · refine Filter.Eventually.of_forall fun t => ?_
    have h0 : g0 * NormedSpace.exp ((0 : ℝ) • Xp p.1 p.2) = g0 := by simp
    show _ ≤ u (g0 * NormedSpace.exp ((0 : ℝ) • Xp p.1 p.2)) -
      A * (1 + hs2 (g0 * NormedSpace.exp ((0 : ℝ) • Xp p.1 p.2))) ^ r -
      η * (1 + hs2 (g0 * NormedSpace.exp ((0 : ℝ) • Xp p.1 p.2))) ^ (r + 1)
    rw [h0]
    exact hmax _ (hmem g0 hg0 _ hXp t)
  · intro t
    exact ((hu' t).sub ((hv' t).const_mul A)).sub ((hw' t).const_mul η)
  · exact (hd.sub (hv''.const_mul A)).sub (hw''.const_mul η)

theorem hilbert_schmidt_nonneg_alt (g : Matrix (Fin n) (Fin n) ℂ) : 0 ≤ hs2 g :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity

end MaximumPrincipleOneFunction

open MaximumPrincipleOneFunction in
theorem maximum_principle_of_facts : B2 → B3 → UnitaryGroupFacts → MaximumPrincipleVar := by
  intro hB2 hB3 hB3g n ε r
  choose cf hcf0 hcf using hB2
  have hcr0 : 0 ≤ ∑ p ∈ nc ε, cf n (Xp p.1 p.2) r := Finset.sum_nonneg fun p _ => hcf0 _ _ _
  have hcr10 : 0 ≤ ∑ p ∈ nc ε, cf n (Xp p.1 p.2) (r + 1) := Finset.sum_nonneg fun p _ => hcf0 _ _ _
  refine ⟨(∑ p ∈ nc ε, cf n (Xp p.1 p.2) r) + (∑ p ∈ nc ε, cf n (Xp p.1 p.2) (r + 1)) + 1, by linarith, ?_⟩
  intro u A hA hcont hgrowth hsub
  obtain ⟨C, hC⟩ := hgrowth
  obtain ⟨hcpt, h1, hmem, -, hhs, hX⟩ := hB3g n ε
  have key : ∀ η : ℝ, 0 < η → u 1 ≤ A * (1 + hs2 (1 : Matrix (Fin n) (Fin n) ℂ)) ^ r +
      η * (1 + hs2 (1 : Matrix (Fin n) (Fin n) ℂ)) ^ (r + 1) := by
    intro η hη
    by_contra hneg
    push Not at hneg
    have hW : Continuous fun g : Matrix (Fin n) (Fin n) ℂ => 1 + hs2 g := continuous_const.add hhs
    have hK := hcpt (|C| / η + hs2 (1 : Matrix (Fin n) (Fin n) ℂ))
    have hKne : ({g | g ∈ UJset ε ∧ hs2 g ≤ |C| / η + hs2 (1 : Matrix (Fin n) (Fin n) ℂ)} : Set _).Nonempty :=
      ⟨1, h1, by have := div_nonneg (abs_nonneg C) hη.le; linarith⟩
    have hψc : ContinuousOn (fun g => u g - A * (1 + hs2 g) ^ r - η * (1 + hs2 g) ^ (r + 1))
        {g | g ∈ UJset ε ∧ hs2 g ≤ |C| / η + hs2 (1 : Matrix (Fin n) (Fin n) ℂ)} := by
      have hu : ContinuousOn u {g | g ∈ UJset ε ∧ hs2 g ≤ |C| / η + hs2 (1 : Matrix (Fin n) (Fin n) ℂ)} :=
        hcont.mono fun g hg => hg.1
      exact (hu.sub (continuous_const.mul (hW.pow r)).continuousOn).sub
        (continuous_const.mul (hW.pow (r + 1))).continuousOn
    obtain ⟨g0, hg0K, hg0max⟩ := hK.exists_isMaxOn hKne hψc
    have hψ1 : u 1 - A * (1 + hs2 (1 : Matrix (Fin n) (Fin n) ℂ)) ^ r -
        η * (1 + hs2 (1 : Matrix (Fin n) (Fin n) ℂ)) ^ (r + 1) ≤
        u g0 - A * (1 + hs2 g0) ^ r - η * (1 + hs2 g0) ^ (r + 1) :=
      hg0max ⟨h1, by have := div_nonneg (abs_nonneg C) hη.le; linarith⟩
    have hglob : ∀ g ∈ UJset ε, u g - A * (1 + hs2 g) ^ r - η * (1 + hs2 g) ^ (r + 1) ≤
        u g0 - A * (1 + hs2 g0) ^ r - η * (1 + hs2 g0) ^ (r + 1) := by
      intro g hg
      by_cases hgρ : hs2 g ≤ |C| / η + hs2 (1 : Matrix (Fin n) (Fin n) ℂ)
      · exact hg0max ⟨hg, hgρ⟩
      · push Not at hgρ
        have hs1 := hilbert_schmidt_nonneg_alt (1 : Matrix (Fin n) (Fin n) ℂ)
        have hsg := hilbert_schmidt_nonneg_alt g
        have hlt : |C| / η < 1 + hs2 g := by linarith
        have hCl : C < η * (1 + hs2 g) := by
          have := (div_lt_iff₀ hη).mp hlt
          have := le_abs_self C
          linarith
        have hWr : 0 < (1 + hs2 g) ^ r := pow_pos (by linarith) r
        have hAW : 0 ≤ A * (1 + hs2 g) ^ r := mul_nonneg hA hWr.le
        have hug := hC g hg
        have hprod := mul_pos hWr (sub_pos.mpr hCl)
        rw [pow_succ]
        nlinarith
    have hg0 : g0 ∈ UJset ε := hg0K.1
    obtain ⟨d, hd, hdsum⟩ := hsub g0 hg0
    have hW0 := hilbert_schmidt_nonneg_alt g0
    have hWr : 0 < (1 + hs2 g0) ^ r := pow_pos (by linarith) r
    have hWr1 : 0 < (1 + hs2 g0) ^ (r + 1) := pow_pos (by linarith) (r + 1)
    have hp : ∀ p ∈ nc ε, d p ≤ A * cf n (Xp p.1 p.2) r * (1 + hs2 g0) ^ r +
        η * cf n (Xp p.1 p.2) (r + 1) * (1 + hs2 g0) ^ (r + 1) := by
      intro p hp
      obtain ⟨u', hu', hdp⟩ := hd p hp
      obtain ⟨v', v'', hv', hv'', hvb⟩ := hcf n (Xp p.1 p.2) r g0
      obtain ⟨w', w'', hw', hw'', hwb⟩ := hcf n (Xp p.1 p.2) (r + 1) g0
      have hst := step hB3 hB3g ε r u A η g0 hglob hg0 p hp u' (d p) hu' hdp v' v'' hv' hv'' w' w'' hw' hw''
      have h1 := mul_le_mul_of_nonneg_left hvb hA
      have h2 := mul_le_mul_of_nonneg_left hwb hη.le
      nlinarith
    have hsum : ∑ p ∈ nc ε, d p ≤ A * (∑ p ∈ nc ε, cf n (Xp p.1 p.2) r) * (1 + hs2 g0) ^ r +
        η * (∑ p ∈ nc ε, cf n (Xp p.1 p.2) (r + 1)) * (1 + hs2 g0) ^ (r + 1) := by
      refine (Finset.sum_le_sum hp).trans (le_of_eq ?_)
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul, ← Finset.mul_sum, ← Finset.mul_sum]
    have hpos : 0 < (∑ p ∈ nc ε, cf n (Xp p.1 p.2) r) + (∑ p ∈ nc ε, cf n (Xp p.1 p.2) (r + 1)) + 1 := by
      linarith
    have hug0 : A * (1 + hs2 g0) ^ r + η * (1 + hs2 g0) ^ (r + 1) < u g0 := by linarith
    have hm := mul_lt_mul_of_pos_left hug0 hpos
    have e1 := mul_nonneg hcr10 (mul_nonneg hA hWr.le)
    have e2 := mul_pos (by linarith : (0:ℝ) < (∑ p ∈ nc ε, cf n (Xp p.1 p.2) r) + 1) (mul_pos hη hWr1)
    nlinarith
  have hW1 : 0 < (1 + hs2 (1 : Matrix (Fin n) (Fin n) ℂ)) ^ (r + 1) :=
    pow_pos (by linarith [hilbert_schmidt_nonneg_alt (1 : Matrix (Fin n) (Fin n) ℂ)]) (r + 1)
  refine le_of_forall_pos_le_add fun δ hδ => ?_
  have := key (δ / (1 + hs2 (1 : Matrix (Fin n) (Fin n) ℂ)) ^ (r + 1)) (div_pos hδ hW1)
  rwa [div_mul_cancel₀ _ hW1.ne'] at this

end PositivityTheory.CW

end
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.OrthonormalEigenbasisOfBasic
section
noncomputable section

open Matrix Finset ReciprocityTheory.ChartRestriction.DS

namespace PositivityTheory.CW

namespace EigenvectorBasisSetup

variable {n : ℕ} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

theorem casK_apply (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) (v : V) :
    casimirK ε E v = ∑ a, ∑ b, if ε b = ε a then E a b (E b a v) else 0 := by
  unfold casimirK
  simp only [Finset.sum_filter, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  split_ifs <;> simp

theorem cas_apply (E : Fin n → Fin n → Module.End ℂ V) (v : V) :
    casimir E v = ∑ a, ∑ b, E a b (E b a v) := by
  unfold casimir
  simp [LinearMap.sum_apply]

theorem nc_sum {M : Type*} [AddCommMonoid M] (ε : Fin n → Bool) (f : Fin n × Fin n → M) :
    ∑ p ∈ nc ε, f p = ∑ a, ∑ b, if ε b = ε a then 0 else f (a, b) := by
  unfold nc
  rw [Finset.sum_filter, ← Finset.univ_product_univ, Finset.sum_product]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  by_cases h : ε b = ε a
  · simp [h]
  · have : ε a ≠ ε b := fun h' => h h'.symm
    simp [h, this]

theorem swap_sum {M : Type*} [AddCommMonoid M] (ε : Fin n → Bool) (f g : Fin n → Fin n → M) :
    (∑ a, ∑ b, if ε b = ε a then f a b else g a b) =
      ∑ a, ∑ b, if ε b = ε a then f b a else g b a := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  by_cases h : ε b = ε a
  · simp [h]
  · have : ε a ≠ ε b := fun h' => h h'.symm
    simp [h, this]

theorem sq_re (u : V) : ‖u‖ ^ 2 = (inner ℂ u u).re := by
  simpa using (inner_self_eq_norm_sq (𝕜 := ℂ) u).symm

theorem sm_re (r : ℝ) (u : V) : (inner ℂ u ((r : ℂ) • u)).re = r * ‖u‖ ^ 2 := by
  rw [inner_smul_right, Complex.re_ofReal_mul, ← sq_re]

end EigenvectorBasisSetup

open EigenvectorBasisSetup in
theorem orthonormal_eigenbasis_of_basic : A0 := by
  intro n ε V _ _ E hM
  have hU := hM.uni
  have hc : ∀ a b, ε b = ε a → ∀ x y, inner ℂ (E a b x) y = inner ℂ x (E b a y) := by
    intro a b h x y
    rw [hU a b x y]
    simp [adjSign, h.symm]
  have hK : ∀ x y, inner ℂ x (casimirK ε E y) =
      ∑ a, ∑ b, if ε b = ε a then inner ℂ (E b a x) (E b a y) else 0 := by
    intro x y
    rw [casK_apply, inner_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [inner_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    split_ifs with h
    · rw [hc b a h.symm]
    · simp
  have hKre : ∀ w, (inner ℂ w (casimirK ε E w)).re =
      ∑ a, ∑ b, if ε b = ε a then ‖E b a w‖ ^ 2 else 0 := by
    intro w
    rw [hK, Complex.re_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    split_ifs
    · rw [sq_re]
    · simp
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x y
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← inner_conj_symm, hK, hK, map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    split_ifs <;> simp
  · intro μ v hv h0
    have h1 := hKre v
    rw [hv, sm_re] at h1
    have h2 : 0 ≤ μ * ‖v‖ ^ 2 := by
      rw [h1]
      refine Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => ?_
      split_ifs <;> positivity
    have h3 : 0 < ‖v‖ ^ 2 := by positivity
    exact nonneg_of_mul_nonneg_left h2 h3
  · intro a b h
    unfold Z
    exact sub_eq_zero.mpr (casimirK_comm ε hM.gl a b h)
  · intro κ hκ w
    have h3 : ∑ p ∈ nc ε, E p.1 p.2 (E p.2 p.1 w) = (κ : ℂ) • w - casimirK ε E w := by
      rw [← hκ w, cas_apply, casK_apply, nc_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun b _ => ?_
      split_ifs <;> simp
    have hnorm : ∀ a b, ‖E a b w‖ ^ 2 = (adjSign ε a b * inner ℂ w (E b a (E a b w))).re := by
      intro a b
      rw [sq_re, hU]
    have h2 : ∑ p ∈ nc ε, ‖E p.1 p.2 w‖ ^ 2 = (inner ℂ w (casimirK ε E w)).re - κ * ‖w‖ ^ 2 := by
      have e1 : ∑ p ∈ nc ε, ‖E p.1 p.2 w‖ ^ 2 =
          ∑ a, ∑ b, if ε b = ε a then 0 else -(inner ℂ w (E b a (E a b w))).re := by
        rw [nc_sum]
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
        by_cases h : ε b = ε a
        · simp [h]
        · have : ε a ≠ ε b := fun h' => h h'.symm
          simp [h, hnorm, adjSign, this]
      have e2 : (∑ a, ∑ b, if ε b = ε a then (0 : ℝ) else -(inner ℂ w (E b a (E a b w))).re) =
          -(inner ℂ w (∑ p ∈ nc ε, E p.1 p.2 (E p.2 p.1 w))).re := by
        rw [swap_sum, nc_sum, inner_sum, Complex.re_sum, ← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [inner_sum, Complex.re_sum, ← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun b _ => ?_
        split_ifs <;> simp
      rw [e1, e2, h3, inner_sub_right, Complex.sub_re, sm_re]
      ring
    have h1 : ∑ a, ∑ b, ‖E a b w‖ ^ 2 = 2 * (inner ℂ w (casimirK ε E w)).re - κ * ‖w‖ ^ 2 := by
      have e1 : ∑ a, ∑ b, ‖E a b w‖ ^ 2 =
          (∑ a, ∑ b, if ε b = ε a then ‖E a b w‖ ^ 2 else 0) +
            ∑ a, ∑ b, if ε b = ε a then 0 else ‖E a b w‖ ^ 2 := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun b _ => ?_
        split_ifs <;> simp
      have e2 : (∑ a, ∑ b, if ε b = ε a then ‖E a b w‖ ^ 2 else (0 : ℝ)) =
          (inner ℂ w (casimirK ε E w)).re := by
        rw [hKre, swap_sum]
      have e3 : (∑ a, ∑ b, if ε b = ε a then (0 : ℝ) else ‖E a b w‖ ^ 2) =
          ∑ p ∈ nc ε, ‖E p.1 p.2 w‖ ^ 2 := by
        rw [nc_sum]
      rw [e1, e2, e3, h2]
      ring
    exact ⟨h1, h2, h3⟩

end PositivityTheory.CW

end
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.PMaxPr
section
noncomputable section

open Matrix Finset ReciprocityTheory.ChartRestriction.DS

namespace PositivityTheory.CW

namespace PMaxPr

theorem hilbert_schmidt_nonneg_alt {n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) : 0 ≤ hs2 g :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

def evalAt {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (g : Matrix (Fin n) (Fin n) ℂ)
    (F : V →ₗ[ℂ] (Matrix (Fin n) (Fin n) ℂ → ℂ)) : V →ₗ[ℂ] ℂ :=
  (LinearMap.proj (R := ℂ) (φ := fun _ : Matrix (Fin n) (Fin n) ℂ => ℂ) g).comp F

@[simp] theorem evalAt_apply {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (g : Matrix (Fin n) (Fin n) ℂ)
    (F : V →ₗ[ℂ] (Matrix (Fin n) (Fin n) ℂ → ℂ)) (v : V) : evalAt g F v = F v g := rfl

theorem sq_bound (x C w : ℝ) (N : ℕ) (h : x ≤ C * w ^ N) (hx : 0 ≤ x) : x ^ 2 ≤ C ^ 2 * w ^ (2 * N) := by
  calc x ^ 2 ≤ (C * w ^ N) ^ 2 := pow_le_pow_left₀ hx h 2
    _ = C ^ 2 * w ^ (2 * N) := by rw [mul_pow, ← pow_mul, mul_comm N 2]

end PMaxPr

open PMaxPr in
theorem maxPr_of : CasimirIsRealScalar → EigenbasisExists → A13 → UnitaryGroupFacts → MaximumPrincipleVar → SumSquaresSecondDerivative → B5 → MaxPr := by
  intro hA3c hA11a hA13 _ hB4a hB4b hB5 n ε V _ _ E hM N
  classical
  obtain ⟨κ, hκ⟩ := hA3c n ε V E hM
  obtain ⟨ι, b, μ, hb⟩ := hA11a n ε V E hM
  obtain ⟨c, hc0, hc⟩ := hB4a n ε (2 * N)
  obtain ⟨s, x₀, C₁, hs, hC₁, h13⟩ := hA13 n ε V E hM ι b μ hb κ hκ (c / 2) (div_nonneg hc0 (by norm_num))
  have hTfin : {i | μ i < x₀}.Finite := (hb.fin x₀).subset fun i (hi : μ i < x₀) => show μ i ≤ x₀ from le_of_lt hi
  have hT : ∀ i, i ∈ hTfin.toFinset ↔ μ i < x₀ := fun i => by simp
  have hW1 : 0 ≤ (1 + hs2 (1 : Matrix (Fin n) (Fin n) ℂ)) ^ (2 * N) :=
    pow_nonneg (by linarith [hilbert_schmidt_nonneg_alt (1 : Matrix (Fin n) (Fin n) ℂ)]) _
  have hKK : 0 ≤ 2 * C₁ * (hTfin.toFinset.card : ℝ) * (1 + hs2 (1 : Matrix (Fin n) (Fin n) ℂ)) ^ (2 * N) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hC₁) (Nat.cast_nonneg _)) hW1
  refine ⟨s, Real.sqrt (2 * C₁ * hTfin.toFinset.card * (1 + hs2 (1 : Matrix (Fin n) (Fin n) ℂ)) ^ (2 * N)),
    hTfin.toFinset.image b, Real.sqrt_nonneg _, ?_⟩
  intro F hcont hder hgrow B hB hI v
  have hA0 : 0 ≤ 2 * C₁ * (hTfin.toFinset.card : ℝ) * B ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hC₁) (Nat.cast_nonneg _)) (sq_nonneg B)
  choose Cf hCf using hgrow
  have key : ∀ (R : ℝ) (S : Finset ι), (∀ i, i ∈ S ↔ μ i < R) →
      ∑ i ∈ S, phiR s R (μ i) * ‖F (b i) 1‖ ^ 2 ≤
        (Real.sqrt (2 * C₁ * hTfin.toFinset.card * (1 + hs2 (1 : Matrix (Fin n) (Fin n) ℂ)) ^ (2 * N)) * B) ^ 2 := by
    intro R S hS
    have hcu : ContinuousOn (fun g => ∑ i ∈ S, phiR s R (μ i) * ‖F (b i) g‖ ^ 2) (UJset ε) :=
      continuousOn_finsetSum _ fun i _ => continuousOn_const.mul ((hcont (b i)).norm.pow 2)
    have hgu : ∃ C : ℝ, ∀ g ∈ UJset ε,
        (∑ i ∈ S, phiR s R (μ i) * ‖F (b i) g‖ ^ 2) ≤ C * (1 + hs2 g) ^ (2 * N) := by
      refine ⟨∑ i ∈ S, phiR s R (μ i) * Cf (b i) ^ 2, fun g hg => ?_⟩
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum fun i _ => ?_
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (sq_bound _ _ _ _ (hCf (b i) g hg) (norm_nonneg _)) (le_max_right _ _)
    have hdu : ∀ g ∈ UJset ε, ∃ d : Fin n × Fin n → ℝ,
        (∀ p ∈ nc ε, ∃ u' : ℝ → ℝ, (∀ t, HasDerivAt (fun t : ℝ =>
          ∑ i ∈ S, phiR s R (μ i) * ‖F (b i) (g * NormedSpace.exp (t • Xp p.1 p.2))‖ ^ 2) (u' t) t) ∧
          HasDerivAt u' (d p) 0) ∧
        c * (∑ i ∈ S, phiR s R (μ i) * ‖F (b i) g‖ ^ 2) -
          2 * C₁ * (hTfin.toFinset.card : ℝ) * B ^ 2 * (1 + hs2 g) ^ (2 * N) ≤ ∑ p ∈ nc ε, d p := by
      intro g hg
      obtain ⟨d, hd, hsum⟩ := hB4b n ε V E hM ι b μ hb κ hκ F hder S (fun i => phiR s R (μ i)) g hg
      refine ⟨d, hd, ?_⟩
      rw [hsum]
      have h13g := h13 R (evalAt g F) S hTfin.toFinset hS hT
      simp only [evalAt_apply] at h13g
      have hTb : ∑ i ∈ hTfin.toFinset, ‖F (b i) g‖ ^ 2 ≤
          hTfin.toFinset.card • (B ^ 2 * (1 + hs2 g) ^ (2 * N)) :=
        Finset.sum_le_card_nsmul _ _ _ fun i hi =>
          sq_bound _ _ _ _ (hI (b i) (Finset.mem_image_of_mem b hi) g hg) (norm_nonneg _)
      rw [nsmul_eq_mul] at hTb
      have h2 := mul_le_mul_of_nonneg_left hTb hC₁
      nlinarith [h2, h13g]
    have h1 := hc (fun g => ∑ i ∈ S, phiR s R (μ i) * ‖F (b i) g‖ ^ 2) _ hA0 hcu hgu hdu
    calc _ ≤ _ := h1
      _ = _ := by rw [mul_pow, Real.sq_sqrt hKK]; ring
  have h5 := hB5 n ε V E hM ι b μ hb (evalAt 1 F) s _
    (mul_nonneg (Real.sqrt_nonneg _) hB) (fun R S hS => by simpa only [evalAt_apply] using key R S hS) hs v
  simpa only [evalAt_apply] using h5

end PositivityTheory.CW

end
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.SymmetricPowerHolds
section
noncomputable section

open Matrix Finset ReciprocityTheory.ChartRestriction.DS

namespace PositivityTheory.CW

namespace identity_filtration_of_scalar

theorem symm_pow {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] (P : Module.End ℂ W)
    (hP : ∀ x y, inner ℂ (P x) y = inner ℂ x (P y)) :
    ∀ k : ℕ, ∀ x y, inner ℂ ((P ^ k) x) y = inner ℂ x ((P ^ k) y) := by
  intro k
  induction k with
  | zero => intro x y; simp
  | succ k ih =>
    intro x y
    rw [pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih, hP]
    congr 1
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, (Commute.self_pow P k).eq]

end identity_filtration_of_scalar

theorem symmetric_power_holds : A7 := by
  intro W _ _ P hP x hx h0 j
  induction j with
  | zero => simp
  | succ j ih =>
    have hsym := identity_filtration_of_scalar.symm_pow P hP (2 ^ j)

    have key : (inner ℂ x ((P ^ (2 ^ (j + 1))) x)).re = ‖(P ^ (2 ^ j)) x‖ ^ 2 := by
      rw [pow_succ, pow_mul, sq, Module.End.mul_apply, ← hsym]
      exact inner_self_eq_norm_sq (𝕜 := ℂ) ((P ^ (2 ^ j)) x)

    have cs : |(inner ℂ x ((P ^ (2 ^ j)) x)).re| ≤ ‖(P ^ (2 ^ j)) x‖ := by
      calc _ ≤ ‖inner ℂ x ((P ^ (2 ^ j)) x)‖ := Complex.abs_re_le_norm _
        _ ≤ ‖x‖ * ‖(P ^ (2 ^ j)) x‖ := norm_inner_le_norm _ _
        _ = _ := by rw [hx, one_mul]
    have hpos : 0 ≤ (inner ℂ x (P x)).re ^ (2 ^ j) := pow_nonneg h0 _
    calc (inner ℂ x (P x)).re ^ (2 ^ (j + 1)) = ((inner ℂ x (P x)).re ^ (2 ^ j)) ^ 2 := by
          rw [pow_succ, pow_mul]
      _ ≤ ((inner ℂ x ((P ^ (2 ^ j)) x)).re) ^ 2 := pow_le_pow_left₀ hpos ih 2
      _ = |(inner ℂ x ((P ^ (2 ^ j)) x)).re| ^ 2 := (sq_abs _).symm
      _ ≤ ‖(P ^ (2 ^ j)) x‖ ^ 2 := pow_le_pow_left₀ (abs_nonneg _) cs 2
      _ = _ := key.symm

end PositivityTheory.CW

end
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.U0Commute
section
noncomputable section

open Matrix Finset ReciprocityTheory.ChartRestriction.DS

namespace PositivityTheory.CWB

open PositivityTheory.CW

namespace WordFiltrationCommute

variable {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (E : Fin n → Fin n → Module.End ℂ V)

theorem U_mono {j k : ℕ} (h : j ≤ k) : U E j ≤ U E k :=
  Submodule.span_mono fun _ ⟨l, hl, hx⟩ => ⟨l, hl.trans h, hx⟩

theorem one_mem : (1 : Module.End ℂ V) ∈ U E 0 :=
  Submodule.subset_span ⟨[], by simp, by simp⟩

theorem gen_mem (a b : Fin n) : E a b ∈ U E 1 :=
  Submodule.subset_span ⟨[(a, b)], by simp, by simp⟩

theorem mul_mem {j k : ℕ} {x y : Module.End ℂ V} (hx : x ∈ U E j) (hy : y ∈ U E k) :
    x * y ∈ U E (j + k) :=
  by apply _root_.UpperTheory.Reformulated.B.EndomorphismFiltrationMulMem.main <;> assumption

theorem bracket_mem (hE : IsGlRep E) {j k : ℕ} {x y : Module.End ℂ V} (hx : x ∈ U E j) (hy : y ∈ U E k) :
    x * y - y * x ∈ U E (j + k - 1) :=
  by apply _root_.UpperTheory.Reformulated.B.ParabolicUnipotentGL.main <;> assumption

end WordFiltrationCommute

theorem word_filtration_of_length : A1 := by
  intro n ε V _ _ E hM
  have hE : IsGlRep E := hM.gl
  have hC : casimirK ε E ∈ U E 2 := by
    unfold casimirK
    refine Submodule.sum_mem _ fun a _ => Submodule.sum_mem _ fun b _ => ?_
    exact WordFiltrationCommute.U_mono E (by norm_num : 1 + 1 ≤ 2) (WordFiltrationCommute.mul_mem E (WordFiltrationCommute.gen_mem E a b) (WordFiltrationCommute.gen_mem E b a))
  refine ⟨fun j k h => WordFiltrationCommute.U_mono E h, WordFiltrationCommute.one_mem E, WordFiltrationCommute.gen_mem E,
    fun j k x hx y hy => WordFiltrationCommute.mul_mem E hx hy, fun j k x hx y hy => WordFiltrationCommute.bracket_mem E hE hx hy, hC,
    fun a b => ?_⟩
  have hZ := WordFiltrationCommute.bracket_mem E hE hC (WordFiltrationCommute.gen_mem E a b)
  unfold Z
  exact WordFiltrationCommute.U_mono E (by norm_num : 2 + 1 - 1 ≤ 2) hZ

end PositivityTheory.CWB

end
end

