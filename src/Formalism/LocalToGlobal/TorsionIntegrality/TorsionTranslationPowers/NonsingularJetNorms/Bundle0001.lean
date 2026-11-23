module

public import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.StatementT

@[expose] public section

-- bundled from Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.NonsingularJetNorms.ScaledXEqOffOrigin
section
open PowerSeries

noncomputable section

namespace Formalism.L2.Th1.E

namespace Power

section Alg

variable {R : Type} [CommRing R] [IsDomain R]

theorem tri_succ (φ : ℕ → R) (m : ℕ) :
    ∏ j ∈ Finset.range (m + 1), φ (j + 1) ^ (m + 1 - j) =
      (∏ j ∈ Finset.range m, φ (j + 1) ^ (m - j)) * ∏ j ∈ Finset.range (m + 1), φ (j + 1) := by
  have h1 : ∏ j ∈ Finset.range m, φ (j + 1) ^ (m - j) =
      ∏ j ∈ Finset.range (m + 1), φ (j + 1) ^ (m - j) := by
    rw [Finset.prod_range_succ]; simp
  rw [h1, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun j hj => ?_
  have hj' : j ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  rw [← pow_succ]
  congr 1
  omega

theorem ratio (g φ : ℕ → R) (k : ℕ) (hne : ∀ j, j ≤ k → g j ≠ 0)
    (hrec : ∀ j, j + 1 ≤ k → g (j + 2) * g j = φ (j + 1) * g (j + 1) ^ 2) :
    ∀ m, m ≤ k → g (m + 1) * g 0 = (∏ j ∈ Finset.range m, φ (j + 1)) * g 1 * g m := by
  intro m
  induction m with
  | zero => intro _; simp
  | succ m ih =>
    intro hm
    have h1 := ih (by omega)
    have h2 := hrec m hm
    have h3 := hne m (by omega)
    apply mul_right_cancel₀ h3
    rw [Finset.prod_range_succ]
    calc g (m + 1 + 1) * g 0 * g m = (g (m + 2) * g m) * g 0 := by ring
      _ = φ (m + 1) * g (m + 1) * (g (m + 1) * g 0) := by rw [h2]; ring
      _ = _ := by rw [h1]; ring

theorem closed (g φ : ℕ → R) (e x : R) (k : ℕ) (h0 : g 0 = e * x) (hne : ∀ j, j ≤ k → g j ≠ 0)
    (hrec : ∀ j, j + 1 ≤ k → g (j + 2) * g j = φ (j + 1) * g (j + 1) ^ 2) :
    ∀ m, m ≤ k → e ^ m * g (m + 1) * x ^ m =
      g 1 ^ (m + 1) * ∏ j ∈ Finset.range m, φ (j + 1) ^ (m - j) := by
  intro m
  induction m with
  | zero => intro _; simp
  | succ m ih =>
    intro hm
    have h1 := ih (by omega)
    have h2 := ratio g φ k hne hrec (m + 1) hm
    rw [tri_succ]
    calc e ^ (m + 1) * g (m + 1 + 1) * x ^ (m + 1)
        = e ^ m * x ^ m * (g (m + 1 + 1) * (e * x)) := by ring
      _ = (e ^ m * g (m + 1) * x ^ m) * ((∏ j ∈ Finset.range (m + 1), φ (j + 1)) * g 1) := by
          rw [← h0, h2]; ring
      _ = _ := by rw [h1]; ring

end Alg

theorem scaled_x_eq_off_origin {K : Type} [Field K] (W : WeierstrassCurve K) (P : W.toAffine.Point) (hP : P ≠ 0) :
    x2 W P = X ^ 2 * xT W P := by
  cases P with
  | zero => exact absurd rfl hP
  | some x y h => rfl

theorem sum_add {A : Type} [AddCommGroup A] [Fintype A] (M : A → ℝ) (Q : A) :
    ∑ P, M (P + Q) = ∑ P, M P :=
  Equiv.sum_comp (Equiv.addRight Q) M

theorem sum_sub {A : Type} [AddCommGroup A] [Fintype A] (M : A → ℝ) (Q : A) :
    ∑ P, M (P - Q) = ∑ P, M P :=
  Equiv.sum_comp (Equiv.subRight Q) M

theorem sum_zero {A : Type} [AddCommGroup A] [Finite A] (M₀ : A → ℝ) (Q : A) (c : ℝ)
    (h : ∀ P : A, M₀ (P + Q) + M₀ (P - Q) - 2 * M₀ P = 2 * c) : c = 0 := by
  have := Fintype.ofFinite A
  have hs : ∑ P : A, (M₀ (P + Q) + M₀ (P - Q) - 2 * M₀ P) = ∑ _P : A, 2 * c :=
    Finset.sum_congr rfl fun P _ => h P
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, sum_add, sum_sub, ← Finset.mul_sum,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hs
  have hc : (Fintype.card A : ℝ) ≠ 0 := by
    have : 0 < Fintype.card A := Fintype.card_pos
    exact_mod_cast this.ne'
  have : (Fintype.card A : ℝ) * (2 * c) = 0 := by rw [← hs]; ring
  rcases mul_eq_zero.mp this with h' | h'
  · exact absurd h' hc
  · linarith

end Power

theorem translate_power : TransPower := by
  intro K _ _ W T _ π G hG ε h0 t k hk
  obtain ⟨hG1, hG2, hG3⟩ := hG
  have hε : ε ≠ 0 := by
    obtain ⟨ε', hn, he⟩ := hG1 0 (map_zero π)
    have h1 : coeff 1 (C ε * X : K⟦X⟧) = coeff 1 (C ε' * X : K⟦X⟧) := by rw [← h0, ← he]
    simp only [coeff_C_mul, coeff_one_X, mul_one] at h1
    intro h
    rw [← h1, h, norm_zero] at hn
    exact zero_ne_one hn
  have hX : (X : K⟦X⟧) ≠ 0 := X_ne_zero
  have hne : ∀ j, j ≤ k → G (j • t) ≠ 0 := by
    intro j hj
    rcases Nat.eq_zero_or_pos j with rfl | hpos
    · rw [zero_smul, h0]
      exact mul_ne_zero (by simpa using hε) hX
    · intro h
      apply hG2 (j • t) (hk j hpos hj)
      rw [h, map_zero]
  have hrec : ∀ j, j + 1 ≤ k → G ((j + 2) • t) * G (j • t) =
      (C (constantCoeff (G t) ^ 2) * (C (px W (π t)) - xT W (π ((j + 1) • t)))) *
        G ((j + 1) • t) ^ 2 := by
    intro j hj
    have ht : π t ≠ 0 := by
      have := hk 1 le_rfl (by omega)
      rwa [one_smul] at this
    have h := hG3 ((j + 1) • t) t ht
    rw [Power.scaled_x_eq_off_origin W _ (hk (j + 1) (by omega) hj)] at h
    have e1 : (j + 1) • t + t = (j + 2) • t := by rw [← succ_nsmul]
    have e2 : (j + 1) • t - t = j • t := by rw [succ_nsmul]; abel
    rw [e1, e2] at h
    apply mul_left_cancel₀ (pow_ne_zero 2 hX)
    rw [h]; ring
  have h := Power.closed (fun j => G (j • t))
    (fun j => C (constantCoeff (G t) ^ 2) * (C (px W (π t)) - xT W (π (j • t)))) (C ε) X k
    (by simpa using h0) hne hrec k le_rfl
  simpa using h

theorem parallelogram_sum_two : ParSumTwo := by
  intro A _ _ M₀ m h
  have hm : ∀ Q : A, Q ≠ 0 → m Q = 0 := fun Q hQ => Power.sum_zero M₀ Q (m Q) fun P => h P Q hQ
  refine ⟨hm, ?_⟩
  have hpar : ∀ P Q : A, M₀ (P + Q) + M₀ (P - Q) = 2 * M₀ P := by
    intro P Q
    by_cases hQ : Q = 0
    · subst hQ; simp; ring
    · have := h P Q hQ
      rw [hm Q hQ] at this
      linarith
  have := Fintype.ofFinite A
  obtain ⟨P₀, -, hmax⟩ := Finset.exists_max_image (Finset.univ : Finset A) M₀ ⟨0, Finset.mem_univ 0⟩
  have hconst : ∀ R : A, M₀ R = M₀ P₀ := by
    intro R
    have h1 := hpar P₀ (R - P₀)
    have h2 := hmax (P₀ + (R - P₀)) (Finset.mem_univ _)
    have h3 := hmax (P₀ - (R - P₀)) (Finset.mem_univ _)
    have e : P₀ + (R - P₀) = R := by abel
    rw [e] at h1 h2
    linarith
  intro P
  rw [hconst P, hconst 0]

end Formalism.L2.Th1.E
end
end

-- bundled from Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.NonsingularJetNorms.ScaledXOffOrigin
section
open PowerSeries

noncomputable section

namespace Formalism.L2.Th1.E

namespace Main

section Tools

variable {K : Type} [NormedField K]

theorem oneUnit_one : OneUnit (1 : K⟦X⟧) := by
  refine ⟨by simp, fun n => ?_⟩
  rw [coeff_one]
  split_ifs <;> simp

theorem unitAt_one : UnitAt 0 (1 : K⟦X⟧) := ⟨1, 1, norm_one, oneUnit_one, by simp⟩

theorem unitAt_C_mul_X {a : K} (ha : ‖a‖ = 1) : UnitAt 1 (C a * X : K⟦X⟧) :=
  ⟨a, 1, ha, oneUnit_one, by simp⟩

theorem unitAt_of_oneUnit {a : K} {V : K⟦X⟧} (ha : ‖a‖ = 1) (hV : OneUnit V) : UnitAt 0 (C a * V) :=
  ⟨a, V, ha, hV, by simp⟩

theorem norm_natCast_of_dvd [IsUltrametricDist K] {n N : ℕ} (h : n ∣ N) (hN : ‖(N : K)‖ = 1) :
    ‖(n : K)‖ = 1 := by
  obtain ⟨d, rfl⟩ := h
  rw [Nat.cast_mul, norm_mul] at hN
  have h1 : ‖(n : K)‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one K n
  have h2 : ‖(d : K)‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one K d
  refine le_antisymm h1 ?_
  calc (1 : ℝ) = ‖(n : K)‖ * ‖(d : K)‖ := hN.symm
    _ ≤ ‖(n : K)‖ * 1 := mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
    _ = ‖(n : K)‖ := mul_one _

end Tools

theorem fac_exists (hF : FacShape) {K : Type} [NormedField K] [IsUltrametricDist K] [DecidableEq K]
    (W : WeierstrassCurve K) (hW : IntCurve W) {T : Type} [AddCommGroup T]
    (π : T →+ W.toAffine.Point) (hI : IntPts W π) (P Q : T) (hP : π P ≠ 0) (hQ : π Q ≠ 0) :
    ∃ e, UnitAt e (C (px W (π Q)) - xT W (π P)) := by
  obtain ⟨h0, h1, h2⟩ := hF K W hW (π P) (π Q) hP hQ (hI P hP).1 (hI P hP).2 (hI Q hQ).1
    (hI Q hQ).2
    (fun h => by rw [← map_add (f := _)] at h ⊢; exact (hI _ h).1)
    (fun h => by rw [← map_sub] at h ⊢; exact (hI _ h).1)
  by_cases ha : π P + π Q = 0
  · by_cases hq : π Q + π Q = 0
    · refine ⟨2, h2 ?_ hq⟩
      have : π P - π Q = (π P + π Q) - (π Q + π Q) := by abel
      rw [this, ha, hq, sub_zero]
    · exact ⟨1, h1 (Or.inl ha) hq⟩
  · by_cases hs : π P - π Q = 0
    · by_cases hq : π Q + π Q = 0
      · exact ⟨2, h2 hs hq⟩
      · exact ⟨1, h1 (Or.inr hs) hq⟩
    · exact ⟨0, h0 ha hs⟩

end Main

open Main

theorem TransUnit_of (hR : IntRules) (hA : UnitAtRules) (hN : RootInt) (hF : FacShape)
    (hP : TransPower) : TransUnit := by
  intro K _ _ _ W hW T _ π G hI hG t N hNn hNt ht
  obtain ⟨-, -, -, -, -, -, -, -, oInv, -⟩ := hR K
  obtain ⟨uMul, uPow, -, -, -⟩ := hA K
  have hN0 : N ≠ 0 := by
    rintro rfl
    simp at hNn
  have hdvd : addOrderOf (π t) ∣ N := addOrderOf_dvd_of_nsmul_eq_zero hNt
  have hn0 : addOrderOf (π t) ≠ 0 := fun h => hN0 (by rw [h] at hdvd; exact Nat.eq_zero_of_zero_dvd hdvd)
  obtain ⟨k, hk⟩ : ∃ k, addOrderOf (π t) = k + 1 := Nat.exists_eq_succ_of_ne_zero hn0
  have hnn : ‖((k + 1 : ℕ) : K)‖ = 1 := hk ▸ norm_natCast_of_dvd hdvd hNn
  have hjk : ∀ j : ℕ, 1 ≤ j → j ≤ k → π (j • t) ≠ 0 := by
    intro j h1 h2 h
    rw [map_nsmul] at h
    have := Nat.le_of_dvd (by omega) (addOrderOf_dvd_of_nsmul_eq_zero h)
    omega
  have hkt : π ((k + 1) • t) = 0 := by
    rw [map_nsmul, ← hk, addOrderOf_nsmul_eq_zero]
  obtain ⟨ε, hε, hG0⟩ := hG.1 0 (map_zero π)
  obtain ⟨ε', hε', hGn⟩ := hG.1 _ hkt
  have key := hP K W T π G hG ε hG0 t k hjk
  have hc0 : constantCoeff (G t) ≠ 0 := hG.2.1 t ht
  generalize hc : constantCoeff (G t) = c at key hc0 ⊢
  have hprod : ∃ (r m : ℕ) (g : K⟦X⟧), UnitAt m g ∧
      ∏ j ∈ Finset.range k, (C (c ^ 2) * (C (px W (π t)) - xT W (π ((j + 1) • t)))) ^ (k - j) =
        C (c ^ r) * g := by
    apply Finset.prod_induction _
      (fun f => ∃ (r m : ℕ) (g : K⟦X⟧), UnitAt m g ∧ f = C (c ^ r) * g)
    · rintro _ _ ⟨r1, m1, g1, h1, rfl⟩ ⟨r2, m2, g2, h2, rfl⟩
      exact ⟨r1 + r2, m1 + m2, g1 * g2, uMul _ _ _ _ h1 h2, by rw [pow_add, map_mul]; ring⟩
    · exact ⟨0, 0, 1, unitAt_one, by simp⟩
    · intro j hj
      have hj' := Finset.mem_range.mp hj
      obtain ⟨e, he⟩ := fac_exists hF W hW π hI ((j + 1) • t) t (hjk (j + 1) (by omega) (by omega)) ht
      exact ⟨2 * (k - j), e * (k - j), _, uPow _ _ _ he, by rw [mul_pow, ← map_pow, ← pow_mul]⟩
  obtain ⟨r, m, g, ⟨a, V, ha, hV, rfl⟩, hpr⟩ := hprod
  rw [hpr, hGn] at key
  have ha0 : a ≠ 0 := by
    rintro rfl
    simp at ha
  have e1 : C (ε ^ k) * (C ε' * X) * X ^ k = C (ε ^ k * ε') * X ^ (k + 1) := by
    rw [map_mul]; ring
  have e2 : G t ^ (k + 1) * (C (c ^ r) * (C a * X ^ m * V)) =
      (G t ^ (k + 1) * C (c ^ r * a) * V) * X ^ m := by
    rw [map_mul]; ring
  rw [e1, e2] at key
  have hcm := congrArg (coeff m) key
  rw [coeff_C_mul, coeff_X_pow, coeff_mul_X_pow', if_pos le_rfl, Nat.sub_self,
    coeff_zero_eq_constantCoeff_apply, map_mul, map_mul, map_pow, hc, constantCoeff_C, hV.1,
    mul_one] at hcm
  have hne : c ^ (k + 1) * (c ^ r * a) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ hc0) (mul_ne_zero (pow_ne_zero _ hc0) ha0)
  have hm : m = k + 1 := by
    by_contra hm
    rw [if_neg hm, mul_zero] at hcm
    exact hne hcm.symm
  subst hm
  rw [if_pos rfl, mul_one] at hcm
  have hcn : ‖c‖ = 1 := by
    have h1 := congrArg norm hcm
    rw [norm_mul, norm_mul, norm_mul, norm_pow, norm_pow, norm_pow, hε, hε', ha, one_pow, mul_one,
      mul_one, ← pow_add] at h1
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg c) (by omega)).mp h1.symm
  have key2 : C (ε ^ k * ε') = G t ^ (k + 1) * C (c ^ r * a) * V :=
    mul_right_cancel₀ (pow_ne_zero (k + 1) X_ne_zero) key
  have hinv : V * (C c⁻¹ * G t) ^ (k + 1) = 1 := by
    have hca : (C (c ^ r * a) : K⟦X⟧) ≠ 0 := by
      rw [Ne, map_eq_zero_iff _ C_injective]
      exact mul_ne_zero (pow_ne_zero _ hc0) ha0
    apply mul_left_cancel₀ hca
    calc C (c ^ r * a) * (V * (C c⁻¹ * G t) ^ (k + 1))
        = C (c⁻¹ ^ (k + 1)) * (G t ^ (k + 1) * C (c ^ r * a) * V) := by
          rw [mul_pow, map_pow]; ring
      _ = C (c⁻¹ ^ (k + 1) * (c ^ (k + 1) * (c ^ r * a))) := by
          rw [← key2, hcm, ← map_mul]
      _ = C (c ^ r * a) * 1 := by
          rw [mul_one, ← mul_assoc, ← mul_pow, inv_mul_cancel₀ hc0, one_pow, one_mul]
  have hone : constantCoeff (C c⁻¹ * G t) = 1 := by
    rw [map_mul, constantCoeff_C, hc, inv_mul_cancel₀ hc0]
  exact ⟨hcn, hone, hN K (k + 1) _ hnn hone (oInv _ _ hV hinv).2⟩

set_option linter.unusedVariables false in
theorem TransGauss_of (hR : IntRules) (hA : UnitAtRules) (hU : TransUnit) : TransGauss := by
  intro K _ _ _ W hW T _ π G hI hG t N hNn hNt
  obtain ⟨-, -, -, uG, -⟩ := hA K
  by_cases ht : π t = 0
  · obtain ⟨ε, hε, h⟩ := hG.1 t ht
    rw [h]
    exact uG 1 _ (unitAt_C_mul_X hε)
  · obtain ⟨h1, h2⟩ := hU K W hW T π G hI hG t N hNn hNt ht
    have h0 : constantCoeff (G t) ≠ 0 := hG.2.1 t ht
    have := uG 0 _ (unitAt_of_oneUnit h1 h2)
    rwa [← mul_assoc, ← map_mul, mul_inv_cancel₀ h0, map_one, one_mul] at this

end Formalism.L2.Th1.E
end
end

