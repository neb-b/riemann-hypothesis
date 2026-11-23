module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
public import GroundTheory.AutomorphicForms.CuspidalDiscreteness.CuspFormsHeight
public import GroundTheory.AutomorphicForms.CuspidalDiscreteness.DecayUniform
public import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.GKStable
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0422
public import Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.WhittakerVanishingImpliesZero
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0425
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.FormUniq
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.NLeA
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ChartGrConst
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HodgeXD
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0415
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0301
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.EulerFinOf

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RapidDecayOfOneParabolicBounds
section
open NumberField GlobalTheory.CuspRep GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction
open scoped NumberField.AdeleRing

namespace GlobalTheory.CompanionTheory.SiegelDecay

theorem ratio_le_of_le {n : ℕ} {t : ℝ} (ht : 0 < t) {ρ : Fin n → ℝ} (hρ : ∀ i, 0 < ρ i)
    (hs : ∀ i j : Fin n, (j : ℕ) = i + 1 → t * ρ j ≤ ρ i) (i j : Fin n) (hij : i ≤ j) :
    ρ j / ρ i ≤ max 1 t⁻¹ ^ n := by
  set S := max 1 t⁻¹
  have hS1 : 1 ≤ S := le_max_left _ _
  have hstep : ∀ l : ℕ, ∀ (hl : l + 1 < n), ρ ⟨l + 1, hl⟩ ≤ S * ρ ⟨l, by omega⟩ := by
    intro l hl
    have h := hs ⟨l, by omega⟩ ⟨l + 1, hl⟩ rfl
    have h2 : ρ ⟨l + 1, hl⟩ ≤ t⁻¹ * ρ ⟨l, by omega⟩ := by
      rw [inv_mul_eq_div, le_div_iff₀ ht]; linarith
    exact h2.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (hρ _).le)
  have hchain : ∀ d : ℕ, ∀ (a : ℕ) (ha : a + d < n),
      ρ ⟨a + d, ha⟩ ≤ S ^ d * ρ ⟨a, by omega⟩ := by
    intro d
    induction d with
    | zero => intro a ha; simp
    | succ d ih =>
      intro a ha
      calc ρ ⟨a + (d + 1), ha⟩ ≤ S * ρ ⟨a + d, by omega⟩ := hstep (a + d) ha
        _ ≤ S * (S ^ d * ρ ⟨a, by omega⟩) :=
            mul_le_mul_of_nonneg_left (ih a (by omega)) (by linarith)
        _ = S ^ (d + 1) * ρ ⟨a, by omega⟩ := by ring
  have hij' : (i : ℕ) ≤ j := hij
  have h1 := hchain (j - i) i (by omega)
  have hj : (⟨(i : ℕ) + (j - i), by omega⟩ : Fin n) = j := Fin.ext (by simp; omega)
  rw [hj] at h1
  rw [div_le_iff₀ (hρ _)]
  calc ρ j ≤ S ^ ((j : ℕ) - i) * ρ i := h1
    _ ≤ S ^ n * ρ i :=
        mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hS1 (by omega)) (hρ _).le

theorem ratio_le_all {n : ℕ} {t : ℝ} (ht : 0 < t) {ρ : Fin n → ℝ} (hρ : ∀ i, 0 < ρ i)
    (hs : ∀ i j : Fin n, (j : ℕ) = i + 1 → t * ρ j ≤ ρ i) {A : ℝ} (hA1 : 1 ≤ A)
    (hA : ∀ i j : Fin n, i < j → ρ i / ρ j ≤ A ^ n) (i j : Fin n) :
    ρ i / ρ j ≤ max 1 t⁻¹ ^ n * A ^ n := by
  have hT : 1 ≤ max 1 t⁻¹ ^ n := one_le_pow₀ (le_max_left _ _)
  have hAn : 1 ≤ A ^ n := one_le_pow₀ hA1
  rcases lt_or_ge i j with h | h
  · exact (hA i j h).trans (le_mul_of_one_le_left (by linarith) hT)
  · exact (ratio_le_of_le ht hρ hs j i h).trans (le_mul_of_one_le_right (by linarith) hAn)

theorem le_of_ratio_le {n : ℕ} {ρ : Fin n → ℝ} (hρ : ∀ i, 0 < ρ i) (hprod : ∏ i, ρ i = 1)
    {R : ℝ} (hR : 1 ≤ R) (h : ∀ i j, ρ i / ρ j ≤ R) (i : Fin n) : ρ i ≤ R := by
  have hn : n ≠ 0 := by
    rintro rfl
    exact i.elim0
  have h1 : ρ i ^ n = ∏ j, ρ i / ρ j := by
    rw [Finset.prod_div_distrib, hprod, div_one]
    simp
  have h2 : ρ i ^ n ≤ R ^ n := by
    rw [h1]
    calc ∏ j, ρ i / ρ j ≤ ∏ _j : Fin n, R :=
          Finset.prod_le_prod₀ (fun j _ => (div_pos (hρ i) (hρ j)).le) (fun j _ => h i j)
      _ = R ^ n := by simp
  exact (pow_le_pow_iff_left₀ (hρ i).le (by linarith) hn).1 h2

theorem inv_le_of_ratio_le {n : ℕ} {ρ : Fin n → ℝ} (hρ : ∀ i, 0 < ρ i) (hprod : ∏ i, ρ i = 1)
    {R : ℝ} (hR : 1 ≤ R) (h : ∀ i j, ρ i / ρ j ≤ R) (i : Fin n) : R⁻¹ ≤ ρ i := by
  have h1 : (ρ i)⁻¹ ≤ R := by
    refine le_of_ratio_le (ρ := fun i => (ρ i)⁻¹) (fun i => inv_pos.2 (hρ i)) ?_ hR ?_ i
    · rw [Finset.prod_inv_distrib, hprod, inv_one]
    · intro i j
      have := h j i
      rwa [inv_div_inv]
  exact inv_le_of_inv_le₀ (hρ i) h1

theorem one_le_rpow_mul_prod {n : ℕ} {ρ : Fin n → ℝ} (hρ : ∀ i, 0 < ρ i) {R : ℝ} (hR : 1 ≤ R)
    (hb : ∀ i, ρ i ≤ R) (hb' : ∀ i, R⁻¹ ≤ ρ i) (lam : Fin n → ℝ) :
    1 ≤ R ^ (∑ i, |lam i|) * ∏ i, ρ i ^ lam i := by
  have hR0 : 0 < R := by linarith
  rw [Real.rpow_sum_of_pos hR0, ← Finset.prod_mul_distrib]
  calc (1 : ℝ) = ∏ _i : Fin n, (1 : ℝ) := by simp
    _ ≤ _ := Finset.prod_le_prod₀ (fun _ _ => zero_le_one) (fun i _ => ?_)
  rcases le_total 0 (lam i) with hl | hl
  · rw [abs_of_nonneg hl, ← Real.mul_rpow hR0.le (hρ i).le]
    refine Real.one_le_rpow ?_ hl
    have := mul_le_mul_of_nonneg_left (hb' i) hR0.le
    rwa [mul_inv_cancel₀ hR0.ne'] at this
  · have hρ' : ρ i ^ lam i = ((ρ i)⁻¹) ^ (-lam i) := by
      rw [Real.inv_rpow (hρ i).le, Real.rpow_neg (hρ i).le, inv_inv]
    rw [abs_of_nonpos hl, hρ', ← Real.mul_rpow hR0.le (inv_pos.2 (hρ i)).le]
    refine Real.one_le_rpow ?_ (by linarith)
    rw [← div_eq_mul_inv, one_le_div (hρ i)]
    exact hb i

theorem one_le_weight {n : ℕ} {t : ℝ} (ht : 0 < t) {ρ : Fin n → ℝ} (hρ : ∀ i, 0 < ρ i)
    (hs : ∀ i j : Fin n, (j : ℕ) = i + 1 → t * ρ j ≤ ρ i) (hprod : ∏ i, ρ i = 1)
    {A : ℝ} (hA1 : 1 ≤ A) (hA : ∀ i j : Fin n, i < j → ρ i / ρ j ≤ A ^ n)
    (lam : Fin n → ℝ) (M : ℕ) (hM : (n : ℝ) * ∑ i, |lam i| ≤ M) :
    1 ≤ (max 1 t⁻¹ ^ n) ^ (∑ i, |lam i|) * A ^ M * ∏ i, ρ i ^ lam i := by
  have hT : 1 ≤ max 1 t⁻¹ ^ n := one_le_pow₀ (le_max_left _ _)
  have hAn : 1 ≤ A ^ n := one_le_pow₀ hA1
  have hA0 : 0 < A := by linarith
  have hR : 1 ≤ max 1 t⁻¹ ^ n * A ^ n := one_le_mul_of_one_le_of_one_le hT hAn
  have hrat := ratio_le_all ht hρ hs hA1 hA
  have h := one_le_rpow_mul_prod hρ hR (le_of_ratio_le hρ hprod hR hrat)
    (inv_le_of_ratio_le hρ hprod hR hrat) lam
  have hP : 0 ≤ ∏ i, ρ i ^ lam i :=
    Finset.prod_nonneg fun i _ => Real.rpow_nonneg (hρ i).le _
  have hpow : (A ^ n) ^ (∑ i, |lam i|) ≤ A ^ M := by
    rw [← Real.rpow_natCast A n, ← Real.rpow_mul hA0.le, ← Real.rpow_natCast A M]
    exact Real.rpow_le_rpow_of_exponent_le hA1 hM
  rw [Real.mul_rpow (by linarith) (by linarith)] at h
  refine h.trans (mul_le_mul_of_nonneg_right ?_ hP)
  exact mul_le_mul_of_nonneg_left hpow (Real.rpow_nonneg (by linarith) _)

theorem rapid_decay_of_one_parabolic_bounds : ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (φ : AdelicGLn.AdelicGL K n → ℂ), Continuous φ → (∀ ω : Set (AdelicGLn.AdelicGL K n), IsCompact ω → ω ⊆ (adelicBorel (K := K) (n := n) : Set (AdelicGLn.AdelicGL K n)) →
    (∀ b ∈ ω, (IdeleGroup.ideleModule K (Matrix.GeneralLinearGroup.det b) : ℝ) = 1) → ∀ t : ℝ, 0 < t → ∀ (r : ℕ) (hr0 : 0 < r) (hrn : r < n), ∃ N : ℕ, ∀ k : ℕ, ∃ C : ℝ,
      ∀ b ∈ ω, ∀ (ρ : Fin n → ℝ) (hρ : ∀ i, 0 < ρ i), (∀ i j : Fin n, (j : ℕ) = i + 1 → t * ρ j ≤ ρ i) →
        ∏ i, ρ i = 1 → ∀ kk ∈ maxCompact (K := K) (n := n), ∀ R : ℝ, 1 ≤ R → (∀ i j : Fin n, ρ i / ρ j ≤ R) →
          ‖φ (b * diagUnits n (fun i => posIdele (K := K) (ρ i) (hρ i)) * kk)‖ ≤
            C * (ρ ⟨r, hrn⟩ / ρ ⟨r - 1, lt_of_le_of_lt (Nat.sub_le r 1) hrn⟩) ^ k * R ^ N) → (∀ ω : Set (AdelicGLn.AdelicGL K n), IsCompact ω → ω ⊆ (adelicBorel (K := K) (n := n) : Set (AdelicGLn.AdelicGL K n)) →
    (∀ b ∈ ω, (IdeleGroup.ideleModule K (Matrix.GeneralLinearGroup.det b) : ℝ) = 1) → ∀ t : ℝ, 0 < t → ∀ lam : Fin n → ℝ, ∃ C : ℝ,
      ∀ b ∈ ω, ∀ (r : Fin n → ℝ) (hr : ∀ i, 0 < r i), (∀ i j : Fin n, (j : ℕ) = i + 1 → t * r j ≤ r i) →
        ∏ i, r i = 1 → ∀ k ∈ maxCompact (K := K) (n := n),
          ‖φ (b * diagUnits n (fun i => posIdele (K := K) (r i) (hr i)) * k)‖ ≤ C * ∏ i, r i ^ lam i) := by
  intro K _ _ n φ hφ hyp ω hω hωB hdet t ht lam
  rcases Nat.lt_or_ge n 2 with hn | hn
  · obtain ⟨C, hC⟩ := (hω.mul (isCompact_maxCompact (K := K) (n := n))).exists_bound_of_continuousOn
      hφ.continuousOn
    refine ⟨C, fun b hb r hr hs hprod k hk => ?_⟩
    have hr1 : ∀ i, r i = 1 := by
      intro i
      have h1 : n = 1 := by
        have := i.pos
        omega
      subst h1
      have hi : i = 0 := Subsingleton.elim _ _
      simpa [hi] using hprod
    have hd : diagUnits n (fun i => posIdele (K := K) (r i) (hr i)) = 1 := by
      have h1 : (fun i => posIdele (K := K) (r i) (hr i)) = 1 := by
        funext i
        have h2 : (⟨r i, hr i⟩ : {x : ℝ // 0 < x}) = 1 := Subtype.ext (hr1 i)
        change posIdeleHom (K := K) ⟨r i, hr i⟩ = 1
        rw [h2, map_one]
      rw [h1, map_one]
    have hP : ∏ i, r i ^ lam i = 1 :=
      Finset.prod_eq_one fun i _ => by rw [hr1 i, Real.one_rpow]
    rw [hd, hP, mul_one, mul_one]
    exact hC _ (Set.mul_mem_mul hb hk)
  · set T : ℝ := max 1 t⁻¹ ^ n with hTdef
    have hT1 : 1 ≤ T := one_le_pow₀ (le_max_left _ _)
    have hT0 : 0 < T := by linarith
    set L : ℝ := ∑ i, |lam i| with hL
    obtain ⟨M, hM⟩ := exists_nat_ge ((n : ℝ) * L)
    have key : ∀ (r : ℕ) (hr : 0 < r) (hrn : r < n), ∃ D : ℝ, ∀ b ∈ ω, ∀ (ρ : Fin n → ℝ)
        (hρ : ∀ i, 0 < ρ i), (∀ i j : Fin n, (j : ℕ) = i + 1 → t * ρ j ≤ ρ i) → ∏ i, ρ i = 1 →
        ∀ kk ∈ maxCompact (K := K) (n := n),
        (∀ i j : Fin n, i < j → ρ i / ρ j ≤ max 1 (ρ ⟨r - 1, by omega⟩ / ρ ⟨r, hrn⟩) ^ n) →
        ‖φ (b * diagUnits n (fun i => posIdele (K := K) (ρ i) (hρ i)) * kk)‖ ≤
          max D 0 * ∏ i, ρ i ^ lam i := by
      intro r hr hrn
      obtain ⟨N, hN⟩ := hyp ω hω hωB hdet t ht r hr hrn
      obtain ⟨C0, hC0⟩ := hN 0
      obtain ⟨C1, hC1⟩ := hN (n * N + M)
      set E : ℝ := max C0 0 + max C1 0 with hE
      have hE0 : 0 ≤ E := add_nonneg (le_max_right _ _) (le_max_right _ _)
      have hC0E : C0 ≤ E := (le_max_left _ _).trans (le_add_of_nonneg_right (le_max_right _ _))
      have hC1E : C1 ≤ E := (le_max_left _ _).trans (le_add_of_nonneg_left (le_max_right _ _))
      have hTL : 0 < T ^ L := Real.rpow_pos_of_pos hT0 _
      have hD0 : 0 ≤ E * T ^ N * T ^ L := by positivity
      refine ⟨E * T ^ N * T ^ L, ?_⟩
      rw [max_eq_left hD0]
      intro b hb ρ hρ hs hprod kk hkk hmax
      have hgain : ρ ⟨r, hrn⟩ / ρ ⟨r - 1, lt_of_le_of_lt (Nat.sub_le r 1) hrn⟩ =
          (ρ ⟨r - 1, by omega⟩ / ρ ⟨r, hrn⟩)⁻¹ := by rw [inv_div]
      obtain ⟨α, hα⟩ : ∃ α, α = ρ ⟨r - 1, by omega⟩ / ρ ⟨r, hrn⟩ := ⟨_, rfl⟩
      rw [← hα] at hmax hgain
      have hα0 : 0 < α := by rw [hα]; exact div_pos (hρ _) (hρ _)
      set P : ℝ := ∏ i, ρ i ^ lam i with hPdef
      have hP : 0 ≤ P := Finset.prod_nonneg fun i _ => Real.rpow_nonneg (hρ i).le _
      rcases le_or_gt α 1 with hα1 | hα1
      · rw [max_eq_left hα1] at hmax
        have hone := one_le_weight ht hρ hs hprod le_rfl hmax lam M hM
        rw [one_pow, mul_one] at hone
        have h := hC0 b hb ρ hρ hs hprod kk hkk T hT1 fun i j => by
          simpa using ratio_le_all ht hρ hs le_rfl hmax i j
        rw [pow_zero, mul_one] at h
        calc _ ≤ C0 * T ^ N := h
          _ ≤ E * T ^ N := mul_le_mul_of_nonneg_right hC0E (by positivity)
          _ ≤ E * T ^ N * (T ^ L * P) := le_mul_of_one_le_right (by positivity) hone
          _ = E * T ^ N * T ^ L * P := by ring
      · rw [max_eq_right hα1.le] at hmax
        have hone := one_le_weight ht hρ hs hprod hα1.le hmax lam M hM
        have hαn : 1 ≤ α ^ n := one_le_pow₀ hα1.le
        have h := hC1 b hb ρ hρ hs hprod kk hkk (T * α ^ n)
          (one_le_mul_of_one_le_of_one_le hT1 hαn) (ratio_le_all ht hρ hs hα1.le hmax)
        rw [hgain] at h
        have hpow : (α⁻¹) ^ (n * N + M) * (T * α ^ n) ^ N = T ^ N * (α ^ M)⁻¹ := by
          have ha : α ^ (n * N) ≠ 0 := (pow_pos hα0 _).ne'
          rw [mul_pow, ← pow_mul α n N, inv_pow, pow_add, mul_inv]
          calc (α ^ (n * N))⁻¹ * (α ^ M)⁻¹ * (T ^ N * α ^ (n * N))
              = ((α ^ (n * N))⁻¹ * α ^ (n * N)) * (T ^ N * (α ^ M)⁻¹) := by ring
            _ = T ^ N * (α ^ M)⁻¹ := by rw [inv_mul_cancel₀ ha, one_mul]
        have hX : 0 ≤ T ^ N * (α ^ M)⁻¹ := by positivity
        calc _ ≤ C1 * (α⁻¹) ^ (n * N + M) * (T * α ^ n) ^ N := h
          _ = C1 * (T ^ N * (α ^ M)⁻¹) := by rw [mul_assoc, hpow]
          _ ≤ E * (T ^ N * (α ^ M)⁻¹) := mul_le_mul_of_nonneg_right hC1E hX
          _ ≤ E * (T ^ N * (α ^ M)⁻¹) * (T ^ L * α ^ M * P) :=
              le_mul_of_one_le_right (mul_nonneg hE0 hX) hone
          _ = E * T ^ N * T ^ L * P := by
              have : α ^ M ≠ 0 := (pow_pos hα0 _).ne'
              field_simp
    choose D hD using key
    refine ⟨∑ r : Fin n, if h : 0 < (r : ℕ) then max (D r h r.2) 0 else 0, ?_⟩
    intro b hb ρ hρ hs hprod k hk
    obtain ⟨r, hr, hrn, hratio⟩ := GroundTheory.Automorphic.CuspidalSpectrum.exists_le_max_pow hn ρ hρ
    have hP : 0 ≤ ∏ i, ρ i ^ lam i :=
      Finset.prod_nonneg fun i _ => Real.rpow_nonneg (hρ i).le _
    refine (hD r hr hrn b hb ρ hρ hs hprod k hk hratio).trans
      (mul_le_mul_of_nonneg_right ?_ hP)
    have h1 := Finset.single_le_sum (f := fun r : Fin n =>
      if h : 0 < (r : ℕ) then max (D r h r.2) 0 else 0)
      (fun r _ => by split_ifs <;> simp) (Finset.mem_univ ⟨r, hrn⟩)
    simpa only [hr, dif_pos] using h1

end GlobalTheory.CompanionTheory.SiegelDecay
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RightDerivativeRealLieHom
section
noncomputable section

open Matrix Finset MeasureTheory
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
open PositivityTheory.RgTw (Mat)
open GlobalTheory.CompanionTheory.GLK (e1 e2 f1)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.ModelS.LieAct

variable {n : ℕ}

theorem SmF_ext {a b : SmF n} (h : ∀ g ∈ GLs n, a.1 g = b.1 g) : a = b := by
  apply Subtype.ext
  funext g
  by_cases hg : g ∈ GLs n
  · exact h g hg
  · rw [a.2.2 g hg, b.2.2 g hg]

theorem Rd_DR (X Y : Mat n) (h : SmF n) {g : Mat n} (hg : g ∈ GLs n) :
    Rd X (DR Y h).1 g = Rd X (Rd Y h.1) g := by
  have hev : (DR Y h).1 =ᶠ[nhds g] Rd Y h.1 := by
    filter_upwards [GlobalTheory.CompanionTheory.RCalc.isOpen_GLs.mem_nhds hg] with y hy
    exact DR_apply Y h hy
  change fderiv ℝ (DR Y h).1 g (g * X) = fderiv ℝ (Rd Y h.1) g (g * X)
  rw [hev.fderiv_eq]

theorem DR_add (X Y : Mat n) : DR (X + Y) = DR X + DR Y := by
  refine LinearMap.ext fun h => SmF_ext fun g hg => ?_
  simpa only [LinearMap.add_apply, Submodule.coe_add, Pi.add_apply, DR_apply _ _ hg] using
    congrFun (GlobalTheory.CompanionTheory.RCalc.Rd_add_left X Y h.1) g

theorem DR_smul (r : ℝ) (X : Mat n) : DR ((r : ℂ) • X) = (r : ℂ) • DR X := by
  refine LinearMap.ext fun h => SmF_ext fun g hg => ?_
  have e : (r : ℂ) • X = r • X := by
    ext a b
    simp only [Matrix.smul_apply, Complex.real_smul, smul_eq_mul]
  simpa only [LinearMap.smul_apply, Submodule.coe_smul, Pi.smul_apply, DR_apply _ _ hg, e,
    Complex.real_smul, smul_eq_mul] using
    congrFun (GlobalTheory.CompanionTheory.RCalc.Rd_smul_left r X h.1) g

theorem DR_bracket (X Y : Mat n) : DR (X * Y - Y * X) = DR X * DR Y - DR Y * DR X := by
  refine LinearMap.ext fun h => SmF_ext fun g hg => ?_
  simp only [LinearMap.sub_apply, mul_apply_eq_comp, Submodule.coe_sub, Pi.sub_apply, DR_apply _ _ hg, Rd_DR _ _ _ hg]
  exact (GlobalTheory.CompanionTheory.RCalc.Rd_bracket X Y h.2.1 hg).symm

theorem DR_lie (n : ℕ) : (∀ X Y : Mat n, DR (X + Y) = DR X + DR Y) ∧
    (∀ (r : ℝ) (X : Mat n), DR ((r : ℂ) • X) = (r : ℂ) • DR X) ∧
    (∀ X Y : Mat n, DR (X * Y - Y * X) = DR X * DR Y - DR Y * DR X) :=
  ⟨DR_add, DR_smul, DR_bracket⟩

end GlobalTheory.CompanionTheory.ModelS.LieAct
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RtMulApply
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter BoundedContinuousFunction
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.AutomorphicL2Unitary GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.LFun Formalism.UG Formalism.L2.Host
open PositivityTheory.jumpWindows

namespace GlobalTheory.CompanionTheory.SmoReg

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

theorem Rt_mul_apply (g h : GA E a) (φ : XB E a) : Rt E a (g * h) φ = Rt E a g (Rt E a h φ) := by
  rw [map_mul]; rfl

theorem polyBd_repI [_root_.NumberField.IsTotallyComplex E] : PolyBd (repI E a) :=
  ⟨1, 0, zero_le_one, fun g x => by
    have : ‖repI E a g x‖ = ‖x‖ := norm_Rt _ _
    simp [this]⟩

theorem conj_stab {G H X : Type} [Group G] [Group H] [TopologicalSpace H] [ContinuousMul H]
    (f : H →* G) (c : G →* H) (R : G → X → X) (hR : ∀ g h x, R (g * h) x = R g (R h x))
    (hf : ∀ u, c (f u) = u) (hcomm : ∀ g, c g = 1 → ∀ u, g * f u = f u * g)
    (g : G) (x : X) (hx : {u : H | R (f u) x = x} ∈ 𝓝 (1 : H)) :
    {u : H | R (f u) (R g x) = R g x} ∈ 𝓝 (1 : H) := by
  obtain ⟨k, hk⟩ : ∃ k, k = c g := ⟨_, rfl⟩
  have hg1 : c ((f k)⁻¹ * g) = 1 := by rw [map_mul, map_inv, hf, ← hk, inv_mul_cancel]
  have hcont : Continuous fun u : H => k⁻¹ * u * k :=
    (continuous_const.mul continuous_id).mul continuous_const
  have hat : Tendsto (fun u : H => k⁻¹ * u * k) (𝓝 1) (𝓝 1) := by
    have := hcont.tendsto 1
    simpa using this
  filter_upwards [hat hx] with u hu
  have key : f u * g = g * f (k⁻¹ * u * k) := by
    have h := hcomm _ hg1 (k⁻¹ * u * k)
    have e : f (k⁻¹ * u * k) = (f k)⁻¹ * f u * f k := by simp only [map_mul, map_inv]
    rw [e] at h ⊢
    have h2 := congrArg (f k * ·) h
    simpa only [mul_assoc, mul_inv_cancel_left] using h2.symm
  have hu' : R (f (k⁻¹ * u * k)) x = x := hu
  change R (f u) (R g x) = R g x
  rw [← hR, key, hR, hu']

theorem lev_Rt [_root_.NumberField.IsTotallyComplex E] (hfl : ∀ (w : Pl E) (u : GL (Fin a) (w.adicCompletion E)),
      cLoc w (fl a w u : GA E a) = u)
    (hcomm : ∀ (w : Pl E) (g : GA E a), cLoc w g = 1 → ∀ u, g * fl a w u = fl a w u * g)
    (S : Finset (Pl E)) (g : GA E a) (φ : XB E a) (hφ : Lev S φ) : Lev S (Rt E a g φ) := by
  intro w hw
  have hx := hφ w hw
  simp only [repW_apply] at hx ⊢
  exact conj_stab (fl a w) (cLoc w) (fun g x => Rt E a g x) Rt_mul_apply (hfl w) (hcomm w) g φ hx

theorem g5b : S2 → G0 → G5b := by
  intro hS2 hG0 E _ _ _ a S
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, -⟩ := hG0 E a
  obtain ⟨-, -, -, hgrp, hT, -⟩ := hS2 _ a (XB E a) (repI E a) polyBd_repI
  refine ⟨?_, fun g φ hφ => lev_Rt h4 h8 S g φ hφ, ?_, ?_, ?_⟩
  · intro g φ hφ
    set y := cInf g with hy
    set gf : GA E a := (infGL E a y)⁻¹ * g with hgf
    have hgf1 : cInf gf = 1 := by
      rw [hgf, map_mul, map_inv, h1, ← hy, inv_mul_cancel]
    have hg : g = infGL E a y * gf := by rw [hgf, mul_inv_cancel_left]
    have hc : ∀ (z : GL (Fin a) (Cinf E)) (x : XB E a),
        Rt E a gf (repI E a z x) = repI E a z (Rt E a gf x) := by
      intro z x
      change Rt E a gf (Rt E a (infGL E a z) x) = Rt E a (infGL E a z) (Rt E a gf x)
      rw [← Rt_mul_apply, ← Rt_mul_apply, h7 gf hgf1 z]
    have := hgrp y _ (hT (Rt E a gf) hc φ hφ)
    have e : Rt E a g φ = repI E a y (Rt E a gf φ) := by
      change Rt E a g φ = Rt E a (infGL E a y) (Rt E a gf φ)
      rw [← Rt_mul_apply, ← hg]
    rw [e]
    exact this
  · intro c φ hφ w hw
    filter_upwards [hφ w hw] with u hu
    have hu' : repW a w u φ = φ := hu
    change repW a w u (c • φ) = c • φ
    rw [map_smul, hu']
  · intro φ φ' hφ hφ' w hw
    filter_upwards [hφ w hw, hφ' w hw] with u hu hu'
    have e : repW a w u φ = φ := hu
    have e' : repW a w u φ' = φ' := hu'
    change repW a w u (φ + φ') = φ + φ'
    rw [map_add (f := _), e, e']
  · intro w hw
    filter_upwards with u
    change repW a w u 0 = 0
    rw [map_zero]

end GlobalTheory.CompanionTheory.SmoReg

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ShearGLMulVecAndNabsDet
section
open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZSeg GlobalTheory.BZMir GlobalTheory.SplitWeil GlobalTheory.CompanionTheory.MirFourier GlobalTheory.CompanionTheory.BZOnto.PerpSmall ValuativeRel Zc
open scoped Topology
open GlobalTheory.CompanionTheory.MirPair

namespace GlobalTheory.CompanionTheory.MirPair

theorem det_one_add_eLast {k : Type} [Field k] {n : ℕ} (b : Fin (n + 1) → k) :
    (1 + vecMulVec (eLast k n) b).det = 1 + b (Fin.last n) := by
  rw [Matrix.vecMulVec_eq Unit, Matrix.det_one_add_replicateCol_mul_replicateRow,
    GlobalTheory.BZMir.eLast, dotProduct_single, mul_one]

theorem shearGL_mulVec_and_nabs_det : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ} (b : Fin (n + 1) → k), valuation k (b (Fin.last n)) < 1 → (∀ x : Fin (n + 1) → k, ((shearGL n b : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ x = x + (b ⬝ᵥ x) • eLast k n) ∧ nabs k (Matrix.GeneralLinearGroup.det (shearGL n b)) = 1 := by
  intro k _ _ _ _ n b hb
  have hv : valuation k (1 + b (Fin.last n)) = 1 := Valuation.map_one_add_of_lt _ hb
  have hdet := GlobalTheory.CompanionTheory.MirPair.det_one_add_eLast b
  have hunit : IsUnit (1 + vecMulVec (GlobalTheory.BZMir.eLast k n) b) := by
    rw [Matrix.isUnit_iff_isUnit_det, hdet, isUnit_iff_ne_zero]
    intro h
    rw [h, map_zero] at hv
    exact zero_ne_one hv
  have hcoe : ((GlobalTheory.CompanionTheory.MirPair.shearGL n b : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) =
      1 + vecMulVec (GlobalTheory.BZMir.eLast k n) b := by
    simp only [GlobalTheory.CompanionTheory.MirPair.shearGL, dif_pos hunit, IsUnit.unit_spec]
  refine ⟨fun x => ?_, ?_⟩
  · rw [hcoe, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.vecMulVec_mulVec, op_smul_eq_smul]
  · apply GlobalTheory.SplitWeil.nabs_eq_one_of_valuation_eq_one
    rw [Matrix.GeneralLinearGroup.val_det_apply, hcoe, hdet, hv]

end GlobalTheory.CompanionTheory.MirPair
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SlantOf
section
open CrystallineSemistableComparison CrystallineSemistableComparison.Onto

namespace GlobalTheory.CompanionTheory.KunGlue

theorem slantOf : CrystallineSemistableComparison.Onto.TopRes → CrystallineSemistableComparison.Onto.SlantOf :=
  fun hT hS hM hC hZ hA hK => _root_.GlobalTheory.CompanionTheory.KunGlue.slant_of_kun hT hS (fun K _ _ X X' P q q' _ _ _ _ p₁ p₂ hP h₁ h₂ =>
    _root_.GlobalTheory.CompanionTheory.KunGlue.kun_left hS hM hC hZ hA hK K X X' P q q' p₁ p₂ hP h₁ h₂)

end GlobalTheory.CompanionTheory.KunGlue
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SwapTwistedCentralizerDiagonal
section
open GlobalTheory.BCT PositivityTheory.Rg.BcB.G8.Fin
open scoped Classical

namespace GlobalTheory.CompanionTheory.SwapCent

theorem twCent_swap : ∀ (H : Type) [Group H] (N : H),
    twCent ((MulEquiv.prodComm : H × H ≃* H × H).toMonoidHom) (N, (1 : H)) =
      (twCent (MonoidHom.id H) N).map ((MonoidHom.id H).prod (MonoidHom.id H)) := by
  intro H _ N
  ext ⟨a, b⟩
  constructor
  · intro h
    have h' : (a, b) * (N, (1 : H)) = (N, (1 : H)) * (b, a) := h
    have h1 : a * N = N * b := congrArg Prod.fst h'
    have h2 : b = a := by simpa using congrArg Prod.snd h'
    subst h2
    exact ⟨b, h1, rfl⟩
  · rintro ⟨x, hx, hxe⟩
    have hx' : x * N = N * x := hx
    have e1 : x = a := congrArg Prod.fst hxe
    have e2 : x = b := congrArg Prod.snd hxe
    subst e1
    subst e2
    change (x, x) * (N, (1 : H)) = (N, (1 : H)) * (x, x)
    simp [hx']

end GlobalTheory.CompanionTheory.SwapCent
end

