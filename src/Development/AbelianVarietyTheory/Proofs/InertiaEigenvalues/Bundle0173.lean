module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0006
public import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle0001
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PeriodDiscExtensionTateElement
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsAlgebraMapEqRoot
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0034

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUniqueMaxTermUntiltFrobeniusSeries
section
open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per

namespace GlobalTheory.PSer.Uniq

theorem exists_strict_max (f d : ℤ → ℝ) (hd : ∀ n, f (n + 1) = f n + d n) (hanti : StrictAnti d)
    (hne : ∀ n, d n ≠ 0) (hpos : ∃ m, 0 < d m) (hneg : ∃ m, d m < 0) :
    ∃ n₀ : ℤ, ∀ n : ℤ, n ≠ n₀ → f n < f n₀ := by
  obtain ⟨m, hm⟩ := hpos
  have hbdd : ∃ b : ℤ, ∀ z : ℤ, d z < 0 → b ≤ z := ⟨m, fun z hz => by
    by_contra hc
    push_neg at hc
    have := hanti hc
    linarith⟩
  obtain ⟨n₀, hn₀, hmin⟩ := Int.exists_least_of_bdd hbdd hneg
  have hafter : ∀ k, n₀ ≤ k → d k < 0 := fun k hk => by
    rcases hk.lt_or_eq with h | h
    · exact (hanti h).trans hn₀
    · rw [← h]; exact hn₀
  have hbefore : ∀ k, k < n₀ → 0 < d k := fun k hk => by
    rcases lt_or_gt_of_ne (hne k) with h | h
    · exact absurd (hmin k h) (not_le.2 hk)
    · exact h
  have hfwd : ∀ k : ℕ, f (n₀ + k + 1) < f n₀ := by
    intro k
    induction k with
    | zero =>
      have := hd n₀
      have := hafter n₀ le_rfl
      simp only [Nat.cast_zero, add_zero]
      linarith
    | succ k ih =>
      rw [show n₀ + ((k + 1 : ℕ) : ℤ) + 1 = n₀ + k + 1 + 1 by push_cast; ring]
      have := hd (n₀ + k + 1)
      have := hafter (n₀ + k + 1) (by omega)
      linarith
  have hbwd : ∀ k : ℕ, f (n₀ - k - 1) < f n₀ := by
    intro k
    induction k with
    | zero =>
      have := hd (n₀ - 1)
      have := hbefore (n₀ - 1) (by omega)
      simp only [Nat.cast_zero, sub_zero]
      rw [sub_add_cancel] at *
      linarith
    | succ k ih =>
      have := hd (n₀ - ((k + 1 : ℕ) : ℤ) - 1)
      have := hbefore (n₀ - ((k + 1 : ℕ) : ℤ) - 1) (by omega)
      rw [show n₀ - ((k + 1 : ℕ) : ℤ) - 1 + 1 = n₀ - k - 1 by push_cast; ring] at *
      linarith
  refine ⟨n₀, fun n hn => ?_⟩
  rcases lt_or_gt_of_ne hn with h | h
  · have := hbwd (n₀ - n - 1).toNat
    rwa [show n₀ - ((n₀ - n - 1).toNat : ℤ) - 1 = n by omega] at this
  · have := hfwd (n - n₀ - 1).toNat
    rwa [show n₀ + ((n - n₀ - 1).toNat : ℤ) + 1 = n by omega] at this

end GlobalTheory.PSer.Uniq

namespace GlobalTheory.PSer.Uniq

theorem exists_unique_max_term : ∀ (l : ℕ) [Fact l.Prime] (h : ℕ) (s : ℝ), 2 ≤ h → 0 < s → s < 1 →
    ∃ j : ℕ, j < 2 ∧ ∃ n₀ : ℤ, ∀ n : ℤ, n ≠ n₀ →
      ‖(l : ℂ_[l])‖ ^ (-n) * s ^ ((l : ℝ) ^ (n * h + j : ℤ)) <
        ‖(l : ℂ_[l])‖ ^ (-n₀) * s ^ ((l : ℝ) ^ (n₀ * h + j : ℤ)) := by
  intro l _ h s hh hs0 hs1
  have hlp : l.Prime := Fact.out
  have hν1 : ‖(l : ℂ_[l])‖ < 1 := GlobalTheory.RingBasics.norm_p_lt
  have hν0 : 0 < ‖(l : ℂ_[l])‖ := norm_pos_iff.2 (Nat.cast_ne_zero.2 hlp.ne_zero)
  set ν := ‖(l : ℂ_[l])‖ with hν
  have hL : (1 : ℝ) < l := by exact_mod_cast hlp.one_lt
  have hL0 : (0 : ℝ) < l := by linarith
  have hls : Real.log s < 0 := Real.log_neg hs0 hs1
  have hlν : Real.log ν < 0 := Real.log_neg hν0 hν1
  have hq : (1 : ℝ) < (l : ℝ) ^ h := one_lt_pow₀ hL (by omega)
  set c : ℝ := ((l : ℝ) ^ h - 1) * Real.log s with hc_def
  have hc : c < 0 := mul_neg_of_pos_of_neg (by linarith) hls
  let u : ℕ → ℤ → ℝ := fun j n => (l : ℝ) ^ (n * h + j : ℤ)
  let f : ℕ → ℤ → ℝ := fun j n => -(n : ℝ) * Real.log ν + u j n * Real.log s
  let d : ℕ → ℤ → ℝ := fun j n => -Real.log ν + u j n * c
  have hu_succ : ∀ j n, u j (n + 1) = u j n * (l : ℝ) ^ h := fun j n => by
    simp only [u]
    rw [show ((n + 1) * (h : ℤ) + (j : ℤ)) = (n * h + j) + ((h : ℕ) : ℤ) by ring,
      zpow_add₀ hL0.ne', zpow_natCast]
  have hd : ∀ j n, f j (n + 1) = f j n + d j n := by
    intro j n
    simp only [f, d, hc_def]
    rw [hu_succ]
    push_cast
    ring
  have hmono : ∀ j, StrictMono (u j) := fun j a b hab => by
    simp only [u]
    apply zpow_lt_zpow_right₀ hL
    have : (0 : ℤ) < (b - a) * h := mul_pos (by omega) (by omega)
    linarith
  have hanti : ∀ j, StrictAnti (d j) := fun j a b hab => by
    simp only [d]
    have := mul_lt_mul_of_neg_right (hmono j hab) hc
    linarith
  set B : ℝ := Real.log ν / c with hB_def
  have hB : 0 < B := div_pos_of_neg_of_neg hlν hc
  have hBc : B * c = Real.log ν := div_mul_cancel₀ _ hc.ne
  have hpos : ∀ j, ∃ m, 0 < d j m := fun j => by
    obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hB (inv_lt_one_of_one_lt₀ hL)
    refine ⟨-((k : ℤ) + j), ?_⟩
    have h1 : u j (-((k : ℤ) + j)) ≤ (l : ℝ) ^ (-(k : ℤ)) := by
      simp only [u]
      apply zpow_le_zpow_right₀ hL.le
      have : (0 : ℤ) ≤ ((k : ℤ) + j) * ((h : ℤ) - 1) := mul_nonneg (by omega) (by omega)
      nlinarith
    have h2 : (l : ℝ) ^ (-(k : ℤ)) = ((l : ℝ)⁻¹) ^ k := by rw [zpow_neg, zpow_natCast, inv_pow]
    have h3 : u j (-((k : ℤ) + j)) < B := by rw [h2] at h1; exact h1.trans_lt hk
    have := mul_lt_mul_of_neg_right h3 hc
    simp only [d]
    linarith
  have hneg : ∀ j, ∃ m, d j m < 0 := fun j => by
    obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt B hL
    refine ⟨k, ?_⟩
    have h1 : (l : ℝ) ^ ((k : ℤ)) ≤ u j k := by
      simp only [u]
      apply zpow_le_zpow_right₀ hL.le
      have : (0 : ℤ) ≤ (k : ℤ) * ((h : ℤ) - 1) := mul_nonneg (by omega) (by omega)
      nlinarith
    rw [zpow_natCast] at h1
    have := mul_lt_mul_of_neg_right (hk.trans_le h1) hc
    simp only [d]
    linarith
  have htie : ∀ n n', d 0 n = 0 → d 1 n' = 0 → False := by
    intro n n' h0 h1
    have e1 : u 0 n * c = u 1 n' * c := by simp only [d] at h0 h1; linarith
    have e2 := (zpow_right_strictMono₀ hL).injective (mul_right_cancel₀ hc.ne e1)
    push_cast at e2
    have hdvd : (h : ℤ) ∣ 1 := ⟨n - n', by linear_combination -e2⟩
    have := Int.eq_one_of_dvd_one (by positivity) hdvd
    omega
  have hfin : ∀ j, (∀ n, d j n ≠ 0) → ∃ n₀ : ℤ, ∀ n, n ≠ n₀ →
      ν ^ (-n) * s ^ (u j n) < ν ^ (-n₀) * s ^ (u j n₀) := by
    intro j hne
    obtain ⟨n₀, hn₀⟩ := exists_strict_max (f j) (d j) (hd j) (hanti j) hne (hpos j) (hneg j)
    refine ⟨n₀, fun n hn => ?_⟩
    have hT : ∀ m, Real.log (ν ^ (-m) * s ^ (u j m)) = f j m := fun m => by
      rw [Real.log_mul (zpow_pos hν0 _).ne' (Real.rpow_pos_of_pos hs0 _).ne', Real.log_zpow,
        Real.log_rpow hs0]
      simp only [f]
      push_cast
      ring
    rw [← Real.log_lt_log_iff (mul_pos (zpow_pos hν0 _) (Real.rpow_pos_of_pos hs0 _))
      (mul_pos (zpow_pos hν0 _) (Real.rpow_pos_of_pos hs0 _)), hT, hT]
    exact hn₀ n hn
  by_cases H : ∀ n, d 0 n ≠ 0
  · exact ⟨0, by norm_num, hfin 0 H⟩
  · push_neg at H
    obtain ⟨n, hn⟩ := H
    exact ⟨1, by norm_num, hfin 1 fun n' hn' => htie n n' hn hn'⟩

end GlobalTheory.PSer.Uniq
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsWachLatticeMatricesGammaPhi
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL GlobalTheory.HWL.Cmp

noncomputable section

namespace GlobalTheory.HWL.Mat

section Abstract

variable {A M : Type} [CommRing A] [AddCommGroup M] [Module A M] {N : Submodule A M} {r : ℕ}

theorem coeff_ext (nb : Module.Basis (Fin r) A ↥N) {a b : Fin r → A}
    (h : ∑ i, a i • (nb i : M) = ∑ i, b i • (nb i : M)) (i : Fin r) : a i = b i := by
  have hli : LinearIndependent A (fun i => (nb i : M)) :=
    nb.linearIndependent.map' N.subtype (Submodule.ker_subtype N)
  exact Fintype.linearIndependent_iffₛ.1 hli a b h i

theorem eq_sum (nb : Module.Basis (Fin r) A ↥N) {x : M} (hx : x ∈ N) :
    x = ∑ i, nb.repr ⟨x, hx⟩ i • (nb i : M) := by
  have h := congrArg N.subtype (nb.sum_repr ⟨x, hx⟩)
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum] at h
  simpa using h.symm

theorem semi_sum {f : M →+ M} {σ : A → A} (hf : ∀ a x, f (a • x) = σ a • f x) (a : Fin r → A)
    (x : Fin r → M) : f (∑ i, a i • x i) = ∑ i, σ (a i) • f (x i) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]; exact Finset.sum_congr rfl fun i _ => hf _ _

theorem sum_sum (P C : Matrix (Fin r) (Fin r) A) (e : Fin r → M) (j : Fin r) :
    ∑ k, C k j • ∑ i, P i k • e i = ∑ i, (P * C) i j • e i := by
  simp only [Finset.smul_sum, Matrix.mul_apply, Finset.sum_smul, smul_smul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by rw [mul_comm]

theorem common_exp (S : Submodule A M) (Q : A) (x : Fin r → M) (h : ∀ j, ∃ k : ℕ, Q ^ k • x j ∈ S) :
    ∃ m : ℕ, ∀ j, Q ^ m • x j ∈ S := by
  choose k hk using h
  refine ⟨∑ j, k j, fun j => ?_⟩
  obtain ⟨c, hc⟩ := Nat.exists_eq_add_of_le
    (Finset.single_le_sum (f := k) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j))
  rw [hc, add_comm, pow_add, mul_smul]
  exact S.smul_mem _ (hk j)

theorem exists_matrices {Γ : Type} [Mul Γ] (nb : Module.Basis (Fin r) A ↥N) (Q π : A)
    (φ : M →+ M) (σ : A → A) (hφ : ∀ a x, φ (a • x) = σ a • φ x)
    (γ : Γ → M →+ M) (τ : Γ → A →+* A) (hγ : ∀ g a x, γ g (a • x) = τ g a • γ g x)
    (hmul : ∀ g h x, γ (g * h) x = γ g (γ h x)) (hcomm : ∀ g x, φ (γ g x) = γ g (φ x))
    (hNφ : ∀ x ∈ N, ∃ k : ℕ, Q ^ k • φ x ∈ N)
    (hNinv : ∀ y ∈ N, ∃ k : ℕ, Q ^ k • y ∈ Submodule.span A (φ '' (N : Set M)))
    (hNΓ : ∀ g, ∀ x ∈ N, γ g x ∈ N) (hNπ : ∀ g, ∀ x ∈ N, ∃ y ∈ N, γ g x - x = π • y) :
    ∃ (m m' : ℕ) (Gm : Γ → Matrix (Fin r) (Fin r) A) (Pm Pm' : Matrix (Fin r) (Fin r) A),
      (∀ g h, Gm (g * h) = Gm g * (Gm h).map (τ g)) ∧
      (∀ g i j, ∃ c, Gm g i j = (if i = j then 1 else 0) + π * c) ∧
      Pm * Pm' = (Q ^ m') • (1 : Matrix (Fin r) (Fin r) A) ∧
      (∀ g, (τ g Q ^ m) • (Pm * (Gm g).map σ) = (Q ^ m) • (Gm g * Pm.map (τ g))) ∧
      (∀ g j, γ g (nb j : M) = ∑ i, Gm g i j • (nb i : M)) ∧
      ∀ j, Q ^ m • φ (nb j : M) = ∑ i, Pm i j • (nb i : M) := by
  classical
  obtain ⟨m, hm⟩ := common_exp N Q (fun j => φ (nb j : M)) fun j => hNφ _ (nb j).2
  obtain ⟨k, hk⟩ := common_exp _ Q (fun j => (nb j : M)) fun j => hNinv _ (nb j).2
  have hspan : Submodule.span A (φ '' (N : Set M)) ≤
      Submodule.span A (Set.range fun i => φ (nb i : M)) := by
    rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    rw [eq_sum nb hx, semi_sum hφ]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  choose c hc using fun j => (Submodule.mem_span_range_iff_exists_fun A).1 (hspan (hk j))
  obtain ⟨Gm, hG⟩ : ∃ Gm : Γ → Matrix (Fin r) (Fin r) A,
      ∀ g j, γ g (nb j : M) = ∑ i, Gm g i j • (nb i : M) :=
    ⟨fun g i j => nb.repr ⟨_, hNΓ g _ (nb j).2⟩ i, fun g j => eq_sum nb _⟩
  obtain ⟨Pm, hP⟩ : ∃ Pm : Matrix (Fin r) (Fin r) A,
      ∀ j, Q ^ m • φ (nb j : M) = ∑ i, Pm i j • (nb i : M) :=
    ⟨fun i j => nb.repr ⟨_, hm j⟩ i, fun j => eq_sum nb _⟩
  have hone : ∀ (a : A) (j : Fin r),
      ∑ i, (a * if i = j then 1 else 0) • (nb i : M) = a • (nb j : M) := by
    intro a j
    rw [Finset.sum_eq_single j] <;> simp +contextual
  refine ⟨m, m + k, Gm, Pm, Matrix.of fun i j => c j i, ?_, ?_, ?_, ?_, hG, hP⟩
  · intro g h
    ext i j
    refine coeff_ext nb (a := fun i => Gm (g * h) i j)
      (b := fun i => (Gm g * (Gm h).map (τ g)) i j) ?_ i
    rw [← hG, hmul, hG h, semi_sum (hγ g), ← sum_sum]
    simp only [hG, Matrix.map_apply]
  · intro g i j
    obtain ⟨y, hy, e⟩ := hNπ g _ (nb j).2
    refine ⟨nb.repr ⟨y, hy⟩ i, ?_⟩
    refine coeff_ext nb (a := fun i => Gm g i j)
      (b := fun i => (if i = j then 1 else 0) + π * nb.repr ⟨y, hy⟩ i) ?_ i
    have h1 := hone 1 j
    simp only [one_mul, one_smul] at h1
    simp only [add_smul, Finset.sum_add_distrib, mul_smul]
    rw [← hG, h1, ← Finset.smul_sum, ← eq_sum nb hy, ← e]
    abel
  · ext i j
    refine coeff_ext nb (a := fun i => (Pm * Matrix.of fun i j => c j i) i j)
      (b := fun i => ((Q ^ (m + k)) • (1 : Matrix (Fin r) (Fin r) A)) i j) ?_ i
    rw [← sum_sum]
    simp only [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, hone, ← hP, Matrix.of_apply]
    rw [pow_add, mul_smul, ← hc j, Finset.smul_sum]
    exact Finset.sum_congr rfl fun l _ => smul_comm _ _ _
  · intro g
    ext i j
    refine coeff_ext nb (a := fun i => ((τ g Q ^ m) • (Pm * (Gm g).map σ)) i j)
      (b := fun i => ((Q ^ m) • (Gm g * Pm.map (τ g))) i j) ?_ i
    simp only [Matrix.smul_apply, smul_eq_mul, mul_smul, ← Finset.smul_sum]
    rw [← sum_sum, ← sum_sum]
    have h1 : ∑ k, (Gm g).map σ k j • ∑ i, Pm i k • (nb i : M) = Q ^ m • γ g (φ (nb j : M)) := by
      rw [← hcomm, hG, semi_sum hφ, Finset.smul_sum]
      exact Finset.sum_congr rfl fun l _ => by rw [← hP, smul_comm, Matrix.map_apply]
    have h2 : ∑ k, Pm.map (τ g) k j • ∑ i, Gm g i k • (nb i : M) =
        τ g Q ^ m • γ g (φ (nb j : M)) := by
      rw [← map_pow, ← hγ, hP, semi_sum (hγ g)]
      exact Finset.sum_congr rfl fun l _ => by rw [← hG, Matrix.map_apply]
    rw [h1, h2, smul_comm]

end Abstract

theorem wach_matrices : ∀ {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K] [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K] {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B] [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR] [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n s : ℕ} {Γ : WGam PD LL O v n s} {R : WSer Γ} {Zl Ai : Type} [CommRing Zl] [CommRing Ai] [Algebra Zl O] [Algebra Zl Ai] {RW : Type} [CommRing RW] [Algebra O RW] {inclR : (O ⊗[Zl] Ai) →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : O ⊗[Zl] Ai} {I : WIo R (O ⊗[Zl] Ai) RW inclR φR gR πA} {E : WEt I} {zl : PowerSeries Zl →+* LetA O n} (Mo : WN E zl) (T : LocLat G Qp LL O) (r : ℕ) (nb : Module.Basis (Fin r) (LetA O n) ↥(Mo.N T)), ∃ (m m' : ℕ) (Gm : Γ.Gam → Matrix (Fin r) (Fin r) (LetA O n)) (Pm Pm' : Matrix (Fin r) (Fin r) (LetA O n)), (∀ g h, Gm (g * h) = Gm g * (Gm h).map (letγ (R.γ₀ g))) ∧ (∀ g i j k, PowerSeries.constantCoeff (Gm g i j k) = if i = j then 1 else 0) ∧ Pm * Pm' = (R.Q ^ m') • (1 : Matrix (Fin r) (Fin r) (LetA O n)) ∧ (∀ g, (letγ (R.γ₀ g) R.Q ^ m) • (Pm * (Gm g).map (letφ R.φ₀)) = (R.Q ^ m) • (Gm g * Pm.map (letγ (R.γ₀ g)))) ∧ (∀ g j, E.γD T g (nb j : E.DD T) = ∑ i, Gm g i j • (nb i : E.DD T)) ∧ ∀ j, R.Q ^ m • E.φD T (nb j : E.DD T) = ∑ i, Pm i j • (nb i : E.DD T) := by
  intro G _ _ Qp K₀ K _ _ _ _ _ _ _ B BdR _ _ _ _ _ _ _ _ _ _ _ PD LL O _ _ _ _ _ v n s Γ R Zl Ai _ _ _ _
    RW _ _ inclR φR gR πA I E zl Mo T r nb
  have hφ : ∀ (a : LetA O n) (x : E.DD T), E.φD T (a • x) = letφ R.φ₀ a • E.φD T x := by
    intro a x
    rw [← algebraMap_smul R.EE a x, E.φD_smul, R.φE_ext, algebraMap_smul]
  have hγ : ∀ g (a : LetA O n) (x : E.DD T),
      E.γD T g (a • x) = letγ (R.γ₀ g) a • E.γD T g x := by
    intro g a x
    rw [← algebraMap_smul R.EE a x, E.γD_smul, R.γE_ext, algebraMap_smul]
  obtain ⟨m, m', Gm, Pm, Pm', h1, h2, h3, h4, h5, h6⟩ :=
    exists_matrices nb R.Q letπ (E.φD T).toAddMonoidHom (letφ R.φ₀) hφ
      (fun g => (E.γD T g).toAddMonoidHom) (fun g => (letγ (n := n) (R.γ₀ g)).toRingHom) hγ
      (E.γD_mul T) (E.φγ_comm T) (Mo.N_φ T) (Mo.N_φinv T) (Mo.N_Γ T) (Mo.N_π T)
  refine ⟨m, m', Gm, Pm, Pm', h1, ?_, h3, h4, h5, h6⟩
  intro g i j k
  obtain ⟨c, hc⟩ := h2 g i j
  rw [hc]
  split_ifs <;> simp [letπ]

end GlobalTheory.HWL.Mat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusMemRigidFunctionsOfMemInvertEisenstein
section
open PowerSeries GlobalTheory.BK Filter Topology

namespace GlobalTheory.BK

theorem exists_mul_frob_E_eq_one_of_lt (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
    [IsUnitBall O K] (l e : ℕ) [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] (k : ℝ)
    (hk : 1 / ((e : ℝ) * l) < k) :
    ∃ g ∈ R O K l k, g * frob K l (E K l e) = 1 := by
  have hl := (Fact.out : l.Prime).pos
  have hl1 : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have : NeZero (e * l) := ⟨(Nat.mul_pos (NeZero.pos e) hl).ne'⟩
  have hl0 := l_ne_zero (K := K) l
  have hel : (0 : ℝ) < (e : ℝ) * l := by
    have := NeZero.pos e
    positivity
  have hk0 : 0 < k := lt_trans (by positivity) hk
  let c : K⟦X⟧ := expand (e * l) (NeZero.ne _) (rescale (-(l : K)⁻¹) (PowerSeries.mk 1))
  set r : ℝ := (l : ℝ) * rad l k ^ (e * l) with hr
  have hr0 : 0 ≤ r := mul_nonneg (by positivity) (pow_nonneg (rad_nonneg l k) _)
  have hr1 : r < 1 := by
    have h1 : rad l k ^ (e * l) = (l : ℝ) ^ (-(k * ((e : ℝ) * l))) := by
      rw [rad, ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg l)]
      push_cast
      ring_nf
    have h2 : (l : ℝ) ^ (-(k * ((e : ℝ) * l))) < (l : ℝ) ^ (-1 : ℝ) := by
      apply Real.rpow_lt_rpow_of_exponent_lt hl1
      have : 1 < k * ((e : ℝ) * l) := by
        rw [div_lt_iff₀ hel] at hk
        linarith
      linarith
    rw [Real.rpow_neg_one] at h2
    rw [hr, h1]
    calc (l : ℝ) * (l : ℝ) ^ (-(k * ((e : ℝ) * l))) < (l : ℝ) * (l : ℝ)⁻¹ :=
          mul_lt_mul_of_pos_left h2 (by positivity)
      _ = 1 := mul_inv_cancel₀ (by positivity)
  have hc (n : ℕ) : ‖coeff n c‖ * rad l k ^ n ≤ r ^ (n / (e * l)) := by
    simp only [c]
    rw [coeff_expand]
    split_ifs with h
    · obtain ⟨j, rfl⟩ := h
      rw [Nat.mul_div_cancel_left _ (NeZero.pos (e * l)), coeff_rescale, coeff_mk, Pi.one_apply,
        mul_one, norm_pow, norm_neg, norm_inv, norm_l, inv_inv, hr, mul_pow, pow_mul]
    · simpa using pow_nonneg hr0 _
  have hcR : c ∈ R O K l k := mem_R.2 <| squeeze_zero
    (fun n => mul_nonneg (norm_nonneg _) (pow_nonneg (rad_nonneg l k) n)) hc
    ((tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1).comp
      (Nat.tendsto_div_const_atTop (NeZero.ne _)))
  refine ⟨C (l : K)⁻¹ * c, mul_mem (HasK.C_mem _) hcR, ?_⟩
  have h := congrArg (fun f => expand (e * l) (NeZero.ne _) (rescale (-(l : K)⁻¹) f))
    (mk_one_mul_one_sub_eq_one K)
  simp only [map_mul, map_sub, map_one, rescale_X, expand_X, expand_C, map_neg] at h
  have h2 : (C (l : K)⁻¹ : K⟦X⟧) * l = 1 := by
    rw [← map_natCast (C : K →+* K⟦X⟧), ← map_mul, inv_mul_cancel₀ hl0, map_one]
  rw [E, map_add (f := _), map_pow, frob_X, map_natCast, ← pow_mul, mul_comm l e]
  change c * _ = 1 at h
  linear_combination h + c * h2
end GlobalTheory.BK

namespace GlobalTheory.BK

theorem frob_mem_R_of_mem_invE_A : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] (l e : ℕ) [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] (k : ℝ), 1 / ((e : ℝ) * l) < k → ∀ f ∈ invE l e (A O K), frob K l f ∈ R O K l k := by
  intro O K _ _ _ _ _ l e _ _ _ k hk f hf
  have hk0 : 0 < k := lt_trans (by
    have := NeZero.pos e
    have := (Fact.out : l.Prime).pos
    positivity) hk
  obtain ⟨g, hg, hgE⟩ := exists_mul_frob_E_eq_one_of_lt O K l e k hk
  obtain ⟨n, hn⟩ := mem_away.1 hf
  rw [coe_EIn] at hn
  have h1 : frob K l (E K l e ^ n * f) ∈ R O K l k := A_le_R l hk0 (frob_mem_A l hn)
  have h2 : frob K l f = g ^ n * frob K l (E K l e ^ n * f) := by
    rw [map_mul, map_pow, ← mul_assoc, ← mul_pow, hgE, one_pow, one_mul]
  rw [h2]
  exact mul_mem (pow_mem hg n) h1

end GlobalTheory.BK
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InjectiveOfPhiModuleExactTriple
section
open PowerSeries GlobalTheory.BK

open Matrix

namespace GlobalTheory.BK

theorem mulVec_eq_zero_of_subalgebra {O S : Type} [CommRing O] [CommRing S] [IsDomain S] [Algebra O S]
    (B : Subalgebra O S) {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (M : Matrix κ ι S) (hM : ∀ i j, M i j ∈ B)
    (hinj : ∀ v : ι → S, (∀ j, v j ∈ B) → M *ᵥ v = 0 → v = 0) (w : ι → S) (hw : M *ᵥ w = 0) :
    w = 0 := by
  first
  | (rename_i h_2 h_3 h_4 h_5 h_9 h_10 h_11 h_12; revert O S h_2 h_3 h_4 h_5 B ι κ h_9 h_10 h_11 h_12 M hM hinj w hw; exact @_root_.GlobalTheory.SubalgebraMulVecZero.mulVec_eq_zero_of_subalgebra)
  | exact @_root_.GlobalTheory.SubalgebraMulVecZero.mulVec_eq_zero_of_subalgebra
  | exact _root_.GlobalTheory.SubalgebraMulVecZero.mulVec_eq_zero_of_subalgebra
  | (apply _root_.GlobalTheory.SubalgebraMulVecZero.mulVec_eq_zero_of_subalgebra <;> assumption)
  | (intros; apply _root_.GlobalTheory.SubalgebraMulVecZero.mulVec_eq_zero_of_subalgebra <;> assumption)
  | (intros; apply @_root_.GlobalTheory.SubalgebraMulVecZero.mulVec_eq_zero_of_subalgebra <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.SubalgebraMulVecZero.mulVec_eq_zero_of_subalgebra ..)

end GlobalTheory.BK

theorem GlobalTheory.BK.IsExactTriple.injective_app : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) [Fact l.Prime] (ι κ μ : Type) [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype μ] [DecidableEq μ] (P : PhiMod O K l e a ι) (Q : PhiMod O K l e a κ) (T : PhiMod O K l e a μ) (F : Hom P Q) (G : Hom Q T), IsExactTriple F G → Function.Injective F.app := by
  intro O K _ _ _ _ _ l e a _ ι κ μ _ _ _ _ _ _ P Q T F G hex
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro w hw
  funext τ
  refine mulVec_eq_zero_of_subalgebra (A O K) (F.mat τ) (F.mem τ) ?_ (w τ) ?_
  · intro v hv hMv
    have hu : Pi.single τ v ∈ P.M := mem_tot.2 fun τ' => by
      by_cases h : τ' = τ
      · subst h; simpa using (mem_vecs.2 hv)
      · rw [Pi.single_eq_of_ne h]; exact zero_mem _
    have h0 : F.app (Pi.single τ v) = 0 := by
      funext τ'
      rw [Hom.app_apply]
      by_cases h : τ' = τ
      · subst h; simpa using hMv
      · rw [Pi.single_eq_of_ne h, Matrix.mulVec_zero]; rfl
    have := congrFun (hex.inj _ hu h0) τ
    simpa using this
  · have := congrFun hw τ
    rwa [Hom.app_apply] at this
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemRigidFunctionsClosedDiscOfAdicLimit
section
open PowerSeries GlobalTheory.BK Filter Topology

namespace GlobalTheory

theorem mem_R_of_adic_limit (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K]
    [Algebra O K] [IsUnitBall O K] (l : ℕ) (k : ℝ) (f : K⟦X⟧) (s : ℕ → K⟦X⟧)
    (hs : ∀ n, s n ∈ R O K l k) (hf : ∀ n, (X : K⟦X⟧) ^ (n + 1) ∣ f - s n)
    (ht : Tendsto (fun n => normR l k (s (n + 1) - s n)) atTop (𝓝 0)) : f ∈ R O K l k := by
  rw [mem_R]
  have hr : ∀ m : ℕ, 0 ≤ rad l k ^ m := fun m => pow_nonneg (rad_nonneg l k) m
  have hc : ∀ m, coeff m f = coeff m (s m) := fun m => by
    have := X_pow_dvd_iff.1 (hf m) m (Nat.lt_succ_self m)
    rwa [map_sub, sub_eq_zero] at this
  rw [Metric.tendsto_atTop] at ht ⊢
  intro ε hε
  obtain ⟨j, hj⟩ := ht ε hε
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 (mem_R.1 (hs j)) ε hε
  refine ⟨max j N, fun m hm => ?_⟩
  have key : ∀ t, j ≤ t → ‖coeff m (s t)‖ * rad l k ^ m < ε := by
    intro t h
    induction t, h using Nat.le_induction with
    | base =>
      have := hN m (le_of_max_le_right hm)
      rw [Real.dist_eq, sub_zero] at this
      exact (le_abs_self _).trans_lt this
    | succ t h ih =>
      have h1 := hj t h
      rw [Real.dist_eq, sub_zero] at h1
      have h2 : ‖coeff m (s (t + 1) - s t)‖ * rad l k ^ m < ε :=
        (le_normR (O := O) (sub_mem (hs (t + 1)) (hs t)) m).trans_lt ((le_abs_self _).trans_lt h1)
      have h3 : coeff m (s (t + 1)) = coeff m (s t) + coeff m (s (t + 1) - s t) := by
        rw [map_sub]; ring
      rw [h3]
      refine (mul_le_mul_of_nonneg_right (IsUltrametricDist.norm_add_le_max _ _) (hr m)).trans_lt ?_
      rw [max_mul_of_nonneg _ _ (hr m)]
      exact max_lt ih h2
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (mul_nonneg (norm_nonneg _) (hr m)), hc]
  exact key m (le_of_max_le_left hm)

end GlobalTheory
end

