module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemSymplecticLieAlgebraOfExpSmulMemSymplecticGro
section
open scoped Matrix

namespace GlobalTheory.RealWeil

theorem mem_sp_of_exp_mem_symplecticGroup (l : Type) [Fintype l] [DecidableEq l]
    (X : Matrix (l ⊕ l) (l ⊕ l) ℝ)
    (h : ∀ t : ℝ, NormedSpace.exp (t • X) ∈ Matrix.symplecticGroup l ℝ) :
    X ∈ LieAlgebra.Symplectic.sp l ℝ := by
  letI : NormedRing (Matrix (l ⊕ l) (l ⊕ l) ℝ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℝ (Matrix (l ⊕ l) (l ⊕ l) ℝ) := Matrix.linftyOpNormedAlgebra
  have h1 : HasDerivAt (fun t : ℝ => NormedSpace.exp (t • X)) (NormedSpace.exp ((0:ℝ) • X) * X) 0 :=
    hasDerivAt_exp_smul_const (𝕂 := ℝ) X 0
  have h2 : HasDerivAt (fun t : ℝ => NormedSpace.exp (t • Xᵀ)) (NormedSpace.exp ((0:ℝ) • Xᵀ) * Xᵀ) 0 :=
    hasDerivAt_exp_smul_const (𝕂 := ℝ) Xᵀ 0
  have h3 := (h1.mul_const (Matrix.J l ℝ)).mul h2
  have h4 : ((fun t : ℝ => NormedSpace.exp (t • X) * Matrix.J l ℝ) * fun t : ℝ => NormedSpace.exp (t • Xᵀ)) = fun _ => Matrix.J l ℝ := by
    funext t
    have := SymplecticGroup.mem_iff.1 (h t)
    rw [← Matrix.exp_transpose, Matrix.transpose_smul] at this
    exact this
  rw [h4] at h3
  have h5 := h3.unique (hasDerivAt_const (0:ℝ) (Matrix.J l ℝ))
  simp only [zero_smul, NormedSpace.exp_zero, one_mul, mul_one] at h5
  have hJ := Matrix.J_squared l ℝ
  have h6 : Xᵀ * Matrix.J l ℝ = Matrix.J l ℝ * (-X) := by
    have h7 : Matrix.J l ℝ * (X * Matrix.J l ℝ + Matrix.J l ℝ * Xᵀ) * Matrix.J l ℝ = 0 := by
      rw [h5]; simp
    have h8 : Matrix.J l ℝ * (X * Matrix.J l ℝ + Matrix.J l ℝ * Xᵀ) * Matrix.J l ℝ
        = Matrix.J l ℝ * X * (Matrix.J l ℝ * Matrix.J l ℝ) + (Matrix.J l ℝ * Matrix.J l ℝ) * Xᵀ * Matrix.J l ℝ := by
      noncomm_ring
    rw [h8, hJ] at h7
    simp only [mul_neg, mul_one, neg_mul, one_mul] at h7 ⊢
    rw [← neg_add, neg_eq_zero] at h7
    exact eq_neg_of_add_eq_zero_right h7
  rw [LieAlgebra.Symplectic.sp, mem_skewAdjointMatricesLieSubalgebra, mem_skewAdjointMatricesSubmodule]
  exact h6

end GlobalTheory.RealWeil
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MultiplicativeHasDerivAtZero
section
namespace GlobalTheory

theorem multiplicative_hasDerivAt_zero : ∀ (lam : ℝ → ℂ), lam 0 = 1 →
    (∀ s t, lam (s + t) = lam s * lam t) → ContinuousAt lam 0 → ∃ c : ℂ, HasDerivAt lam c 0 := by
  intro lam h0 hmul hc
  have hcont : Continuous lam := by
    rw [continuous_iff_continuousAt]
    intro t
    have h1 : ContinuousAt (fun x => lam (x - t)) t := by
      apply ContinuousAt.comp (g := lam) (f := fun x => x - t)
      · simpa using hc
      · exact (continuous_id.sub continuous_const).continuousAt
    have h2 : (fun x => lam t * lam (x - t)) = lam := by
      funext x; rw [← hmul]; congr 1; ring
    rw [← h2]; exact continuousAt_const.mul h1
  set F : ℝ → ℂ := fun u => ∫ x in (0:ℝ)..u, lam x with hF
  have hFd : ∀ b, HasDerivAt F (lam b) b := fun b =>
    (hcont.integral_hasStrictDerivAt 0 b).hasDerivAt
  obtain ⟨δ, hδ⟩ : ∃ δ, F δ ≠ 0 := by
    have := (hFd 0).eventually_ne (c := 0) (by rw [h0]; exact one_ne_zero)
    exact this.exists
  have hi : ∀ a b : ℝ, IntervalIntegrable lam MeasureTheory.volume a b :=
    fun a b => hcont.intervalIntegrable a b
  have key : ∀ t, lam t * F δ = F (t + δ) - F t := by
    intro t
    calc lam t * F δ = ∫ s in (0:ℝ)..δ, lam (t + s) := by
          simp only [hF, hmul]; rw [intervalIntegral.integral_const_mul]
      _ = ∫ s in (t + 0)..(t + δ), lam s := intervalIntegral.integral_comp_add_left lam t
      _ = F (t + δ) - F t := by
          simp only [add_zero, hF]
          exact (intervalIntegral.integral_interval_sub_left (hi 0 (t + δ)) (hi 0 t)).symm
  have hd : HasDerivAt (fun t => (F (t + δ) - F t) * (F δ)⁻¹)
      ((lam (0 + δ) - lam 0) * (F δ)⁻¹) 0 := by
    have h1 : HasDerivAt (fun t => F (t + δ)) (lam (0 + δ)) 0 :=
      HasDerivAt.comp_add_const 0 δ (hFd (0 + δ))
    exact (h1.sub (hFd 0)).mul_const _
  refine ⟨_, hd.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)⟩
  simp only
  rw [← key t, mul_assoc, mul_inv_cancel₀ hδ, mul_one]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NewtonRecursionPolyUnique
section
open Finset Polynomial

namespace GlobalTheory

lemma shiftDiffPoly_coeff_comp (f : ℂ[X]) (n : ℕ) :
    (f.comp (X + 1)).coeff n = ∑ i ∈ range (f.natDegree + 1), f.coeff i * (i.choose n : ℂ) := by
  rw [comp, eval₂_eq_sum_range]
  simp [Polynomial.finsetSum_coeff, coeff_C_mul, coeff_X_add_one_pow]

lemma shiftDiffPoly_coeff_top (f : ℂ[X]) (n : ℕ) (hn : f.natDegree ≤ n) :
    (f.comp (X + 1) - f).coeff n = 0 := by
  rw [coeff_sub, shiftDiffPoly_coeff_comp, Finset.sum_eq_single n]
  · simp
  · intro b hb hbn
    have : b < n := by simp at hb; omega
    simp [Nat.choose_eq_zero_of_lt this]
  · intro hn'
    have : f.coeff n = 0 := coeff_eq_zero_of_natDegree_lt (by simp at hn'; omega)
    simp [this]

lemma shiftDiffPoly_coeff_sub (f : ℂ[X]) (e : ℕ) (he : f.natDegree = e + 1) :
    (f.comp (X + 1) - f).coeff e = ((e : ℂ) + 1) * f.coeff (e + 1) := by
  rw [coeff_sub, shiftDiffPoly_coeff_comp, he, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_eq_zero]
  · simp [Nat.choose_succ_self_right]; ring
  · intro i hi
    simp at hi
    simp [Nat.choose_eq_zero_of_lt hi]

theorem newton_recursion_poly_unique : ∀ (m N : ℕ) (p : ℕ → ℂ) (f r : ℂ[X]), m < N → p 0 = (m : ℂ) + 1 → f.natDegree ≤ m → r.natDegree ≤ m → (∀ u : ℂ, (u - m) ^ (N + 1) * (f.eval (u + 1) - f.eval u) - f.eval u * ∑ k ∈ range (N + 1), (-1) ^ k * (u - m) ^ (N - k) * p k = r.eval u) → f = 0 := by
  intro m N p f r hmN hp0 hf hr hid
  have hlead : ∀ k : ℕ, ((X - C (m:ℂ)) ^ k).coeff k = 1 := fun k => by
    have h := ((monic_X_sub_C (m:ℂ)).pow k).coeff_natDegree
    rwa [natDegree_pow, natDegree_X_sub_C, mul_one] at h
  set Pi : ℂ[X] := ∑ k ∈ range (N + 1), C ((-1) ^ k * p k) * (X - C (m:ℂ)) ^ (N - k) with hPi
  set g : ℂ[X] := f.comp (X + 1) - f with hg
  have hpoly : (X - C (m:ℂ)) ^ (N + 1) * g - f * Pi = r := by
    apply Polynomial.funext
    intro u
    simp only [hg, hPi, eval_sub, eval_mul, eval_pow, eval_X, eval_C, eval_comp, eval_add,
      eval_one, Polynomial.eval_finsetSum]
    rw [← hid u]
    congr 2
    apply Finset.sum_congr rfl
    intro k _
    ring
  have hPiN : Pi.coeff N = (m : ℂ) + 1 := by
    rw [hPi, Polynomial.finsetSum_coeff, Finset.sum_range_succ', Finset.sum_eq_zero]
    · simp only [pow_zero, one_mul, Nat.sub_zero, coeff_C_mul, hlead, hp0, mul_one, zero_add]
    · intro k hk
      rw [coeff_C_mul, coeff_eq_zero_of_natDegree_lt, mul_zero]
      rw [natDegree_pow, natDegree_X_sub_C]
      simp at hk
      omega
  have hPideg : Pi.natDegree ≤ N := by
    rw [hPi]
    apply natDegree_sum_le_of_forall_le
    intro k _
    refine (natDegree_C_mul_le _ _).trans ?_
    rw [natDegree_pow, natDegree_X_sub_C]
    omega
  set d := f.natDegree with hd
  have hcoef : ((X - C (m:ℂ)) ^ (N + 1) * g - f * Pi).coeff (d + N) = r.coeff (d + N) := by rw [hpoly]
  rw [coeff_sub] at hcoef
  have hr0 : r.coeff (d + N) = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
  have h2 : (f * Pi).coeff (d + N) = f.coeff d * Pi.coeff N :=
    coeff_mul_add_eq_of_natDegree_le le_rfl hPideg
  have h1 : ((X - C (m:ℂ)) ^ (N + 1) * g).coeff (d + N) = d * f.coeff d := by
    rcases Nat.eq_zero_or_pos d with h0 | hpos
    · have hg0 : g = 0 := by
        ext n
        rw [coeff_zero]
        exact shiftDiffPoly_coeff_top f n (by omega)
      rw [hg0, mul_zero, coeff_zero, h0]
      simp
    · obtain ⟨e, he⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
      have hgdeg : g.natDegree ≤ e := by
        rw [natDegree_le_iff_coeff_eq_zero]
        intro n hn
        exact shiftDiffPoly_coeff_top f n (by omega)
      have hidx : d + N = (N + 1) + e := by omega
      rw [hidx, coeff_mul_add_eq_of_natDegree_le (by rw [natDegree_pow, natDegree_X_sub_C, mul_one]) hgdeg,
        hlead, one_mul, shiftDiffPoly_coeff_sub f e he, he]
      push_cast
      ring
  rw [h1, h2, hPiN, hr0] at hcoef
  have hne : (d : ℂ) - ((m : ℂ) + 1) ≠ 0 := by
    intro h
    have h' : (d : ℂ) = ((m + 1 : ℕ) : ℂ) := by push_cast; linear_combination h
    have := Nat.cast_injective h'
    omega
  have hc : f.coeff d = 0 := by
    have : f.coeff d * ((d : ℂ) - ((m : ℂ) + 1)) = 0 := by linear_combination hcoef
    rcases mul_eq_zero.mp this with h | h
    · exact h
    · exact absurd h hne
  exact leadingCoeff_eq_zero.mp hc

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormCreationAnnihilationWordLeNumberOperatorPow
section
open scoped InnerProductSpace

namespace GlobalTheory

theorem norm_word_le_number_pow : ∀ (T H κ : Type) [AddCommGroup T] [Module ℂ T] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [Fintype κ] (Φ : T →ₗ[ℂ] H) (a c : κ → Module.End ℂ T) (M : Module.End ℂ T) (r r' : ℝ), 1 ≤ r → r' ≤ r → (∀ j x y, inner ℂ (Φ (c j x)) (Φ y) = inner ℂ (Φ x) (Φ (a j y))) → (∀ j, a j * c j - c j * a j = (r' : ℂ) • 1) → M = ∑ j, c j * a j + (r : ℂ) • 1 → (∀ j, M * a j = a j * (M - (r : ℂ) • 1)) → (∀ j, M * c j = c j * (M + (r : ℂ) • 1)) → ∀ (l : List (Module.End ℂ T)) (d : ℕ), (∀ X ∈ l, X ∈ Submodule.span ℂ (Set.range a ∪ Set.range c)) → l.length ≤ d → ∃ C : ℝ, ∀ x, ‖Φ (l.prod x)‖ ≤ C * ‖Φ ((M ^ d) x)‖ := by
  intro T H κ _ _ _ _ _ Φ a c M r r' hr hr' hadj hcomm hM hMa hMc l d hl hld

  have hreal : ∀ (s : ℝ) (x : T), RCLike.re (inner ℂ (Φ x) (Φ ((s : ℂ) • x))) = s * ‖Φ x‖ ^ 2 := by
    intro s x
    rw [map_smul, inner_smul_right, inner_self_eq_norm_sq_to_K]
    simp [Complex.mul_re]
    left; rw [← Complex.ofReal_pow, Complex.ofReal_re]
  have hca : ∀ j x, RCLike.re (inner ℂ (Φ x) (Φ (c j (a j x)))) = ‖Φ (a j x)‖ ^ 2 := by
    intro j x
    rw [← inner_conj_symm, hadj, RCLike.conj_re, inner_self_eq_norm_sq]
  have hMx : ∀ x, M x = ∑ j, c j (a j x) + (r : ℂ) • x := by
    intro x; subst hM; simp [Module.End.mul_apply]
  have hQeq : ∀ x, RCLike.re (inner ℂ (Φ x) (Φ (M x))) = ∑ j, ‖Φ (a j x)‖ ^ 2 + r * ‖Φ x‖ ^ 2 := by
    intro x
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hMx, map_add (f := _), inner_add_right, map_add (f := _), ← hreal, map_sum, inner_sum, map_sum]
    simp only [hca]
  have hQ : ∀ x, ∑ j, ‖Φ (a j x)‖ ^ 2 + r * ‖Φ x‖ ^ 2 ≤ ‖Φ x‖ * ‖Φ (M x)‖ := by
    intro x; rw [← hQeq]; exact (RCLike.re_le_norm _).trans (norm_inner_le_norm _ _)
  have hsum : ∀ x, 0 ≤ ∑ j, ‖Φ (a j x)‖ ^ 2 := fun x => Finset.sum_nonneg (fun j _ => sq_nonneg _)
  have hrx : ∀ x, r * ‖Φ x‖ ≤ ‖Φ (M x)‖ := by
    intro x
    rcases (norm_nonneg (Φ x)).eq_or_lt with h0 | hpos
    · rw [← h0, mul_zero]; exact norm_nonneg _
    · refine le_of_mul_le_mul_left ?_ hpos
      nlinarith [hQ x, hsum x]
  have hx : ∀ x, ‖Φ x‖ ≤ ‖Φ (M x)‖ := by
    intro x; nlinarith [hrx x, norm_nonneg (Φ x)]
  have hsq : ∀ x u, 0 ≤ u → u ^ 2 ≤ ∑ j, ‖Φ (a j x)‖ ^ 2 + r * ‖Φ x‖ ^ 2 → u ≤ ‖Φ (M x)‖ := by
    intro x u hu h
    have h1 := hQ x
    have h2 := mul_le_mul_of_nonneg_right (hx x) (norm_nonneg (Φ (M x)))
    have h3 : u ^ 2 ≤ ‖Φ (M x)‖ ^ 2 := by nlinarith
    exact (pow_le_pow_iff_left₀ hu (norm_nonneg _) two_ne_zero).1 h3
  have ha : ∀ j x, ‖Φ (a j x)‖ ≤ ‖Φ (M x)‖ := by
    intro j x
    refine hsq x _ (norm_nonneg _) ?_
    have := Finset.single_le_sum (f := fun i => ‖Φ (a i x)‖ ^ 2) (fun i _ => sq_nonneg _) (Finset.mem_univ j)
    have : 0 ≤ r * ‖Φ x‖ ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
    linarith
  have hac : ∀ j, a j * c j = c j * a j + (r' : ℂ) • 1 := fun j => sub_eq_iff_eq_add'.1 (hcomm j)
  have hc : ∀ j x, ‖Φ (c j x)‖ ≤ ‖Φ (M x)‖ := by
    intro j x
    refine hsq x _ (norm_nonneg _) ?_
    have e : ‖Φ (c j x)‖ ^ 2 = ‖Φ (a j x)‖ ^ 2 + r' * ‖Φ x‖ ^ 2 := by
      rw [← inner_self_eq_norm_sq (𝕜 := ℂ), hadj, ← Module.End.mul_apply, hac, LinearMap.add_apply,
        LinearMap.smul_apply, Module.End.one_apply, Module.End.mul_apply, map_add, inner_add_right, map_add, hca, hreal]
    have := Finset.single_le_sum (f := fun i => ‖Φ (a i x)‖ ^ 2) (fun i _ => sq_nonneg _) (Finset.mem_univ j)
    have : r' * ‖Φ x‖ ^ 2 ≤ r * ‖Φ x‖ ^ 2 := mul_le_mul_of_nonneg_right hr' (sq_nonneg _)
    linarith
  have hC : ∀ s : ℝ, Commute M (M + (s : ℂ) • 1) := fun s =>
    (Commute.refl M).add_right ((Commute.one_right M).smul_right _)
  have hshift : ∀ (s : ℝ), |s| ≤ r → ∀ y, ‖Φ ((M + (s : ℂ) • 1) y)‖ ≤ 2 * ‖Φ (M y)‖ := by
    intro s hs y
    rw [LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply, map_add (f := _), map_smul]
    calc ‖Φ (M y) + (s : ℂ) • Φ y‖ ≤ ‖Φ (M y)‖ + ‖(s : ℂ) • Φ y‖ := norm_add_le _ _
      _ = ‖Φ (M y)‖ + |s| * ‖Φ y‖ := by rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
      _ ≤ ‖Φ (M y)‖ + r * ‖Φ y‖ := by gcongr
      _ ≤ 2 * ‖Φ (M y)‖ := by linarith [hrx y]
  have hpow : ∀ (s : ℝ), |s| ≤ r → ∀ k y, ‖Φ (((M + (s : ℂ) • 1) ^ k) y)‖ ≤ 2 ^ k * ‖Φ ((M ^ k) y)‖ := by
    intro s hs k
    induction k with
    | zero => intro y; simp
    | succ k ih =>
      intro y
      have e := LinearMap.congr_fun ((hC s).pow_left k).eq y
      rw [Module.End.mul_apply, Module.End.mul_apply] at e
      rw [pow_succ (M + (s : ℂ) • 1) k, Module.End.mul_apply, pow_succ' M k, Module.End.mul_apply]
      calc ‖Φ (((M + (s : ℂ) • 1) ^ k) ((M + (s : ℂ) • 1) y))‖
          ≤ 2 ^ k * ‖Φ ((M ^ k) ((M + (s : ℂ) • 1) y))‖ := ih _
        _ = 2 ^ k * ‖Φ ((M + (s : ℂ) • 1) ((M ^ k) y))‖ := by rw [e]
        _ ≤ 2 ^ k * (2 * ‖Φ (M ((M ^ k) y))‖) := by gcongr; exact hshift s hs _
        _ = 2 ^ (k + 1) * ‖Φ (M ((M ^ k) y))‖ := by ring
  have hcommx : ∀ (s : ℝ) (k : ℕ) x, M (((M + (s : ℂ) • 1) ^ k) x) = ((M + (s : ℂ) • 1) ^ k) (M x) := by
    intro s k x
    have e := LinearMap.congr_fun ((hC s).pow_right k).eq x
    rw [Module.End.mul_apply, Module.End.mul_apply] at e
    exact e
  have hMka : ∀ j (k : ℕ) x, (M ^ k) (a j x) = a j (((M + ((-r : ℝ) : ℂ) • 1) ^ k) x) := by
    intro j k x
    have hs : SemiconjBy (a j) (M + ((-r : ℝ) : ℂ) • 1) M := by
      unfold SemiconjBy; rw [hMa j]; push_cast; rw [neg_smul, ← sub_eq_add_neg]
    have e := LinearMap.congr_fun (hs.pow_right k).eq x
    rw [Module.End.mul_apply, Module.End.mul_apply] at e
    exact e.symm
  have hMkc : ∀ j (k : ℕ) x, (M ^ k) (c j x) = c j (((M + (r : ℂ) • 1) ^ k) x) := by
    intro j k x
    have hs : SemiconjBy (c j) (M + (r : ℂ) • 1) M := by
      unfold SemiconjBy; rw [hMc j]
    have e := LinearMap.congr_fun (hs.pow_right k).eq x
    rw [Module.End.mul_apply, Module.End.mul_apply] at e
    exact e.symm
  have hra : |(-r)| ≤ r := by rw [abs_neg, abs_of_nonneg (by linarith)]
  have hrc : |r| ≤ r := by rw [abs_of_nonneg (by linarith)]
  have hPa : ∀ j (k : ℕ), ∃ C : ℝ, ∀ x, ‖Φ ((M ^ k) (a j x))‖ ≤ C * ‖Φ ((M ^ (k + 1)) x)‖ := by
    intro j k; refine ⟨2 ^ k, fun x => ?_⟩
    rw [hMka]
    calc _ ≤ ‖Φ (M (((M + ((-r : ℝ) : ℂ) • 1) ^ k) x))‖ := ha j _
      _ = ‖Φ (((M + ((-r : ℝ) : ℂ) • 1) ^ k) (M x))‖ := by rw [hcommx]
      _ ≤ 2 ^ k * ‖Φ ((M ^ k) (M x))‖ := hpow _ hra k _
      _ = 2 ^ k * ‖Φ ((M ^ (k + 1)) x)‖ := by rw [pow_succ M k, Module.End.mul_apply]
  have hPc : ∀ j (k : ℕ), ∃ C : ℝ, ∀ x, ‖Φ ((M ^ k) (c j x))‖ ≤ C * ‖Φ ((M ^ (k + 1)) x)‖ := by
    intro j k; refine ⟨2 ^ k, fun x => ?_⟩
    rw [hMkc]
    calc _ ≤ ‖Φ (M (((M + (r : ℂ) • 1) ^ k) x))‖ := hc j _
      _ = ‖Φ (((M + (r : ℂ) • 1) ^ k) (M x))‖ := by rw [hcommx]
      _ ≤ 2 ^ k * ‖Φ ((M ^ k) (M x))‖ := hpow _ hrc k _
      _ = 2 ^ k * ‖Φ ((M ^ (k + 1)) x)‖ := by rw [pow_succ M k, Module.End.mul_apply]
  have hP : ∀ X ∈ Submodule.span ℂ (Set.range a ∪ Set.range c), ∀ k : ℕ, ∃ C : ℝ,
      ∀ x, ‖Φ ((M ^ k) (X x))‖ ≤ C * ‖Φ ((M ^ (k + 1)) x)‖ := by
    intro X hX
    induction hX using Submodule.span_induction with
    | mem X h =>
      rcases h with ⟨j, rfl⟩ | ⟨j, rfl⟩
      · exact hPa j
      · exact hPc j
    | zero => intro k; exact ⟨0, fun x => by simp⟩
    | add X Y _ _ hX hY =>
      intro k
      obtain ⟨C1, h1⟩ := hX k
      obtain ⟨C2, h2⟩ := hY k
      refine ⟨C1 + C2, fun x => ?_⟩
      rw [LinearMap.add_apply, map_add (f := _), map_add (f := _)]
      calc _ ≤ _ := norm_add_le _ _
        _ ≤ C1 * _ + C2 * _ := add_le_add (h1 x) (h2 x)
        _ = _ := by ring
    | smul s X _ hX =>
      intro k
      obtain ⟨C1, h1⟩ := hX k
      refine ⟨‖s‖ * C1, fun x => ?_⟩
      rw [LinearMap.smul_apply, map_smul, map_smul, norm_smul, mul_assoc]
      exact mul_le_mul_of_nonneg_left (h1 x) (norm_nonneg _)
  have hlist : ∀ l : List (Module.End ℂ T), (∀ X ∈ l, X ∈ Submodule.span ℂ (Set.range a ∪ Set.range c)) →
      ∀ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖Φ ((M ^ k) (l.prod x))‖ ≤ C * ‖Φ ((M ^ (k + l.length)) x)‖ := by
    intro l
    induction l with
    | nil => intro _ k; exact ⟨1, zero_le_one, fun x => by simp⟩
    | cons X l ih =>
      intro hXl k
      obtain ⟨C1, h1⟩ := hP X (hXl X (by simp)) k
      obtain ⟨C2, hC2, h2⟩ := ih (fun Y hY => hXl Y (List.mem_cons_of_mem _ hY)) (k + 1)
      refine ⟨max C1 0 * C2, mul_nonneg (le_max_right _ _) hC2, fun x => ?_⟩
      rw [List.prod_cons, Module.End.mul_apply, List.length_cons]
      calc _ ≤ C1 * ‖Φ ((M ^ (k + 1)) (l.prod x))‖ := h1 _
        _ ≤ max C1 0 * ‖Φ ((M ^ (k + 1)) (l.prod x))‖ :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
        _ ≤ max C1 0 * (C2 * ‖Φ ((M ^ (k + 1 + l.length)) x)‖) :=
            mul_le_mul_of_nonneg_left (h2 x) (le_max_right _ _)
        _ = max C1 0 * C2 * ‖Φ ((M ^ (k + (l.length + 1))) x)‖ := by
            rw [mul_assoc, show k + (l.length + 1) = k + 1 + l.length by omega]
  have hmono : ∀ x n i, ‖Φ ((M ^ n) x)‖ ≤ ‖Φ ((M ^ (n + i)) x)‖ := by
    intro x n i
    induction i with
    | zero => simp
    | succ i ih => rw [← add_assoc, pow_succ', Module.End.mul_apply]; exact ih.trans (hx _)
  obtain ⟨C, hC0, h⟩ := hlist l hl 0
  refine ⟨C, fun x => ?_⟩
  have h' := h x
  rw [pow_zero, Module.End.one_apply, zero_add] at h'
  obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le hld
  exact h'.trans (mul_le_mul_of_nonneg_left (hmono x _ i) hC0)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormLeOfCompleteHomogeneousLe
section
open PowerSeries Finset

namespace GlobalTheory.CompleteHomogeneousBound

def WeightedSummable (r : ℝ) (f : ℂ⟦X⟧) : Prop :=
  Summable fun m : ℕ => ‖coeff m f * (r : ℂ) ^ m‖

theorem WeightedSummable.mul {r : ℝ} {f g : ℂ⟦X⟧} (hf : WeightedSummable r f)
    (hg : WeightedSummable r g) : WeightedSummable r (f * g) := by
  have h := summable_norm_sum_mul_antidiagonal_of_summable_norm hf hg
  refine h.congr fun m => ?_
  rw [coeff_mul, Finset.sum_mul]
  congr 1
  refine Finset.sum_congr rfl fun p hp => ?_
  have hpm : p.1 + p.2 = m := by simpa using hp
  rw [← hpm, pow_add]
  ring

theorem weightedSummable_one (r : ℝ) : WeightedSummable r 1 := by
  refine summable_of_ne_finset_zero (s := {0}) fun m hm => ?_
  have : m ≠ 0 := by simpa using hm
  simp [coeff_one, this]

theorem weightedSummable_linear (r : ℝ) (b : ℂ) : WeightedSummable r (1 - C b * X) := by
  refine summable_of_ne_finset_zero (s := {0, 1}) fun m hm => ?_
  have h0 : m ≠ 0 := fun h => hm (by simp [h])
  have h1 : m ≠ 1 := fun h => hm (by simp [h])
  simp [coeff_one, coeff_X, h0, h1]

theorem weightedSummable_prod {ι : Type*} (r : ℝ) (s : Finset ι) (f : ι → ℂ⟦X⟧)
    (h : ∀ i ∈ s, WeightedSummable r (f i)) : WeightedSummable r (∏ i ∈ s, f i) :=
  Finset.prod_induction f (WeightedSummable r) (fun _ _ ha hb => ha.mul hb)
    (weightedSummable_one r) h

theorem weightedSummable_geom_iff (r : ℝ) (b : ℂ) :
    WeightedSummable r (mk fun m => b ^ m) ↔ ‖b * r‖ < 1 := by
  unfold WeightedSummable
  simp only [coeff_mk, ← mul_pow, norm_pow]
  rw [summable_geometric_iff_norm_lt_one, norm_norm]

theorem geom_mul_linear (b : ℂ) : (mk fun m => b ^ m : ℂ⟦X⟧) * (1 - C b * X) = 1 := by
  ext m
  rw [mul_sub, mul_one, ← mul_assoc, map_sub]
  cases m with
  | zero => simp
  | succ m => simp [coeff_succ_mul_X, coeff_one, pow_succ]

theorem coeff_prod_geom {n : ℕ} (β : Fin n → ℂ) (m : ℕ) :
    coeff m (∏ i, (mk fun k => β i ^ k : ℂ⟦X⟧)) =
      ∑ a ∈ Finset.piAntidiag Finset.univ m, ∏ i, β i ^ a i := by
  rw [coeff_prod]
  simp only [coeff_mk]
  refine Finset.sum_bij' (fun l _ => (l : Fin n → ℕ))
    (fun a _ => Finsupp.equivFunOnFinite.symm a) ?_ ?_ ?_ ?_ ?_
  · intro l hl
    simpa [Finset.mem_piAntidiag, Finset.mem_finsuppAntidiag] using hl
  · intro a ha
    simpa [Finset.mem_piAntidiag, Finset.mem_finsuppAntidiag] using ha
  · intro l _
    simp
  · intro a _
    simp
  · intro l _
    rfl

theorem norm_le_of_completeHomogeneous_le (n : ℕ) (β : Fin n → ℂ) (c : Fin n → ℝ) (Q : ℝ)
    (hc0 : ∀ i, 0 ≤ c i) (hcQ : ∀ i, c i ≤ Q)
    (h : ∀ m : ℕ, ‖∑ a ∈ Finset.piAntidiag Finset.univ m, ∏ i, β i ^ a i‖ ≤
      ∑ a ∈ Finset.piAntidiag Finset.univ m, ∏ i, c i ^ a i) (i : Fin n) : ‖β i‖ ≤ Q := by
  by_contra hlt
  rw [not_le] at hlt
  have hpos : 0 < ‖β i‖ := lt_of_le_of_lt ((hc0 i).trans (hcQ i)) hlt
  set r : ℝ := ‖β i‖⁻¹ with hr
  have hr0 : 0 < r := inv_pos.mpr hpos
  have hc : WeightedSummable r (∏ j, (mk fun k => ((c j : ℝ) : ℂ) ^ k : ℂ⟦X⟧)) := by
    refine weightedSummable_prod r _ _ fun j _ => ?_
    rw [weightedSummable_geom_iff, norm_mul, Complex.norm_real, Complex.norm_real,
      Real.norm_of_nonneg (hc0 j), Real.norm_of_nonneg hr0.le, hr, ← div_eq_mul_inv,
      div_lt_one hpos]
    exact (hcQ j).trans_lt hlt
  have hβ : WeightedSummable r (∏ j, (mk fun k => β j ^ k : ℂ⟦X⟧)) := by
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun m => ?_) hc
    rw [norm_mul, norm_mul, coeff_prod_geom, coeff_prod_geom]
    refine mul_le_mul_of_nonneg_right ((h m).trans ?_) (norm_nonneg _)
    have : (∑ a ∈ Finset.piAntidiag Finset.univ m, ∏ j, ((c j : ℝ) : ℂ) ^ a j) =
        ((∑ a ∈ Finset.piAntidiag Finset.univ m, ∏ j, c j ^ a j : ℝ) : ℂ) := by
      push_cast; rfl
    rw [this, Complex.norm_real]
    exact le_abs_self _
  have hlin : WeightedSummable r (∏ j ∈ Finset.univ.erase i, (1 - C (β j) * X)) :=
    weightedSummable_prod r _ _ fun j _ => weightedSummable_linear r _
  have hm := hβ.mul hlin
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i), mul_assoc, ← Finset.prod_mul_distrib,
    Finset.prod_eq_one (fun j _ => geom_mul_linear (β j)), mul_one, weightedSummable_geom_iff,
    norm_mul, Complex.norm_real, Real.norm_of_nonneg hr0.le, hr, mul_inv_cancel₀ hpos.ne'] at hm
  exact lt_irrefl _ hm

end GlobalTheory.CompleteHomogeneousBound
end

