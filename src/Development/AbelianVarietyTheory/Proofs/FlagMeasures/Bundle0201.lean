module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SigmaFiniteOfRealSmul
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0185

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagStabilizerMulInvLeviComponentMemUnipotent
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.LeviIso
open Formalism.REAL (Jm UJ Jm_mul_self Jm_conjTranspose)

namespace GlobalTheory.LeviUnip

variable {n n₀ a : ℕ} {j : Fin a → ℕ}

theorem umul {ε : Fin n → Bool} (g h : UJ ε) : uMat (g * h) = uMat g * uMat h := rfl

theorem uone {ε : Fin n → Bool} : uMat (1 : UJ ε) = 1 := rfl

theorem umul_inv {ε : Fin n → Bool} (g : UJ ε) : uMat g * uMat g⁻¹ = 1 := by rw [← umul, mul_inv_cancel, uone]

theorem uinv_mul {ε : Fin n → Bool} (g : UJ ε) : uMat g⁻¹ * uMat g = 1 := by rw [← umul, inv_mul_cancel, uone]

theorem col_mem {B : ∀ i, Matrix (Fin n) (Fin (j i)) ℂ} {W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)}
    (hB : SpansFlag B W) {k : Fin (a + 1)} {i : Fin a} (hi : i.castSucc < k) (u : Fin (j i) → ℂ) :
    B i *ᵥ u ∈ W k := by
  classical
  refine (hB k _).2 ⟨Pi.single i u, fun i' hi' => ?_, ?_⟩
  · have hne : i' ≠ i := by rintro rfl; exact hi' hi
    exact Pi.single_eq_of_ne hne _
  · rw [Finset.sum_eq_single i (fun b _ hb => by rw [Pi.single_eq_of_ne hb, Matrix.mulVec_zero])
      (fun h => absurd (Finset.mem_univ i) h), Pi.single_eq_same]

theorem map_mem {B : ∀ i, Matrix (Fin n) (Fin (j i)) ℂ} {W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)}
    (hB : SpansFlag B W) {k : Fin (a + 1)} (F : Matrix (Fin n) (Fin n) ℂ) (U : Submodule ℂ (Fin n → ℂ))
    (h : ∀ i : Fin a, i.castSucc < k → ∀ u, (F * B i) *ᵥ u ∈ U) {y : Fin n → ℂ} (hy : y ∈ W k) :
    F *ᵥ y ∈ U := by
  obtain ⟨u, hu, rfl⟩ := (hB k y).1 hy
  rw [Matrix.mulVec_sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  by_cases hi : i.castSucc < k
  · rw [Matrix.mulVec_mulVec]
    exact h i hi (u i)
  · rw [hu i hi, Matrix.mulVec_zero, Matrix.mulVec_zero]
    exact U.zero_mem

theorem sum_col_mem {B : ∀ i, Matrix (Fin n) (Fin (j i)) ℂ} {W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)}
    (hB : SpansFlag B W) {k : Fin (a + 1)} {r : ℕ} (q : ∀ i, Matrix (Fin (j i)) (Fin r) ℂ)
    (hq : ∀ i : Fin a, ¬ i.castSucc < k → q i = 0) (u : Fin r → ℂ) : (∑ i, B i * q i) *ᵥ u ∈ W k := by
  rw [Matrix.sum_mulVec]
  refine (hB k _).2 ⟨fun i => q i *ᵥ u, fun i hi => by
    show q i *ᵥ u = 0
    rw [hq i hi, Matrix.zero_mulVec], ?_⟩
  exact Finset.sum_congr rfl fun i _ => (Matrix.mulVec_mulVec _ _ _).symm

theorem mul_inv_mem_flagN (n n₀ a : ℕ) (j : Fin a → ℕ) (ε : Fin n → Bool) (ε₀ : Fin n₀ → Bool)
    (B : ∀ i, Matrix (Fin n) (Fin (j i)) ℂ) (B₀ : Matrix (Fin n) (Fin n₀) ℂ) (hF : IsFrame ε ε₀ B B₀)
    (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)) (A : ∀ i, Matrix (Fin n) (Fin (j i)) ℂ)
    (A₀ : Matrix (Fin n) (Fin n₀) ℂ) (p : ∀ k i, Matrix (Fin (j k)) (Fin (j i)) ℂ)
    (d : ∀ k, Matrix (Fin (j k)) (Fin n₀) ℂ) (s h : Formalism.REAL.UJ ε₀)
    (y : ∀ i, Matrix (Fin (j i)) (Fin (j i)) ℂ) (g m : Formalism.REAL.UJ ε)
    (hA : SpansFlag A W) (hB : SpansFlag B W) (hp : ∀ k i, i < k → p k i = 0) (hpd : ∀ i, (p i i).det ≠ 0)
    (hAB : ∀ i, A i = ∑ k, B k * p k i) (hA₀ : A₀ = B₀ * uMat s + ∑ k, B k * d k)
    (hy : ∀ i, (y i).det ≠ 0) (hg : ∀ i, uMat g * A i = A i * y i) (hg₀ : uMat g * A₀ = A₀ * uMat h)
    (hm : uMat m = lev ε B B₀ (fun i => p i i * y i * (p i i)⁻¹) (uMat (s * h * s⁻¹))) :
    g * m⁻¹ ∈ flagN ε W := by
  classical
  have hpu : ∀ i, IsUnit (p i i).det := fun i => isUnit_iff_ne_zero.2 (hpd i)
  have hyu : ∀ i, IsUnit (y i).det := fun i => isUnit_iff_ne_zero.2 (hy i)
  set x : ∀ i, Matrix (Fin (j i)) (Fin (j i)) ℂ := fun i => p i i * y i * (p i i)⁻¹ with hx
  have hxu : ∀ i, IsUnit (x i).det := by
    intro i
    rw [isUnit_iff_ne_zero]
    simp [hx, Matrix.det_mul, Matrix.det_nonsing_inv, hpd i, hy i]

  have hMB : ∀ i, uMat m⁻¹ * B i = B i * (x i)⁻¹ := by
    intro i
    have h1 : uMat m * B i = B i * x i := by
      rw [hm]
      exact GlobalTheory.LeviIso.IsFrame.lev_mul_B _ _ hF i
    calc uMat m⁻¹ * B i = uMat m⁻¹ * (B i * (x i * (x i)⁻¹)) := by
          rw [Matrix.mul_nonsing_inv _ (hxu i), Matrix.mul_one]
      _ = (uMat m⁻¹ * uMat m) * B i * (x i)⁻¹ := by
          rw [← Matrix.mul_assoc (B i), ← h1]
          simp only [Matrix.mul_assoc]
      _ = B i * (x i)⁻¹ := by rw [uinv_mul, Matrix.one_mul]

  have hG : ∀ k (v : Fin n → ℂ), v ∈ W k → uMat g *ᵥ v ∈ W k := fun k v hv =>
    map_mem hA (uMat g) (W k) (fun i hi u => by
      rw [hg i, ← Matrix.mulVec_mulVec]
      exact col_mem hA hi _) hv
  have hsub : ∀ v : Fin n → ℂ, uMat (g * m⁻¹) *ᵥ v - v = (uMat g * uMat m⁻¹ - 1) *ᵥ v := by
    intro v
    rw [umul, Matrix.sub_mulVec, Matrix.one_mulVec]

  have hNA : ∀ l, (uMat g * uMat m⁻¹ - 1) * A l =
      uMat g * ∑ k, B k * ((x k)⁻¹ * p k l - p k l * (y l)⁻¹) := by
    intro l
    have e1 : uMat m⁻¹ * A l = ∑ k, B k * ((x k)⁻¹ * p k l) := by
      rw [hAB l, Matrix.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [← Matrix.mul_assoc, hMB k, Matrix.mul_assoc]
    have e2 : uMat g * A l * (y l)⁻¹ = A l := by
      rw [hg l, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (hyu l), Matrix.mul_one]
    calc (uMat g * uMat m⁻¹ - 1) * A l = uMat g * (uMat m⁻¹ * A l) - A l := by
          rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc]
      _ = uMat g * ∑ k, B k * ((x k)⁻¹ * p k l) - uMat g * A l * (y l)⁻¹ := by rw [e1, e2]
      _ = _ := by
          rw [hAB l]
          simp only [Matrix.mul_sub, Finset.sum_sub_distrib, Matrix.mul_sum, Matrix.sum_mul,
            Matrix.mul_assoc]

  have hq0 : ∀ l k, l ≤ k → (x k)⁻¹ * p k l - p k l * (y l)⁻¹ = 0 := by
    intro l k hlk
    rcases hlk.lt_or_eq with h | rfl
    · rw [hp k l h, Matrix.mul_zero, Matrix.zero_mul, sub_zero]
    · have : (x l)⁻¹ * p l l = p l l * (y l)⁻¹ := by
        rw [hx, Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ (hpu l),
          Matrix.mul_assoc, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (hpu l), Matrix.mul_one]
      rw [this, sub_self]

  have hNB₀ : (uMat g * uMat m⁻¹ - 1) * B₀ =
      (∑ k, B k * d k) * uMat s⁻¹ - uMat g * (∑ k, B k * d k) * (uMat h⁻¹ * uMat s⁻¹) := by
    have hinv : (s * h * s⁻¹)⁻¹ = s * h⁻¹ * s⁻¹ := by group
    have e1 : uMat m⁻¹ * B₀ = B₀ * (uMat s * uMat h⁻¹ * uMat s⁻¹) := by
      have h1 : uMat m * B₀ = B₀ * uMat (s * h * s⁻¹) := by
        rw [hm]
        exact GlobalTheory.LeviIso.IsFrame.lev_mul_B₀ _ _ hF
      calc uMat m⁻¹ * B₀ = uMat m⁻¹ * (B₀ * (uMat (s * h * s⁻¹) * uMat (s * h * s⁻¹)⁻¹)) := by
            rw [umul_inv, Matrix.mul_one]
        _ = (uMat m⁻¹ * uMat m) * B₀ * uMat (s * h * s⁻¹)⁻¹ := by
            rw [← Matrix.mul_assoc B₀, ← h1]
            simp only [Matrix.mul_assoc]
        _ = _ := by rw [uinv_mul, Matrix.one_mul, hinv, umul, umul]
    have e2 : B₀ * uMat s = A₀ - ∑ k, B k * d k := by
      rw [hA₀]
      abel
    calc (uMat g * uMat m⁻¹ - 1) * B₀ = uMat g * (uMat m⁻¹ * B₀) - B₀ := by
          rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc]
      _ = uMat g * (B₀ * uMat s) * (uMat h⁻¹ * uMat s⁻¹) - B₀ := by
          rw [e1]
          simp only [Matrix.mul_assoc]
      _ = (A₀ * uMat h - uMat g * ∑ k, B k * d k) * (uMat h⁻¹ * uMat s⁻¹) - B₀ := by
          rw [e2, Matrix.mul_sub, hg₀]
      _ = A₀ * uMat s⁻¹ - uMat g * (∑ k, B k * d k) * (uMat h⁻¹ * uMat s⁻¹) - B₀ := by
          rw [Matrix.sub_mul, Matrix.mul_assoc A₀, ← Matrix.mul_assoc (uMat h), umul_inv h,
            Matrix.one_mul]
      _ = (B₀ * uMat s + ∑ k, B k * d k) * uMat s⁻¹
            - uMat g * (∑ k, B k * d k) * (uMat h⁻¹ * uMat s⁻¹) - B₀ := by rw [← hA₀]
      _ = _ := by
          rw [Matrix.add_mul, Matrix.mul_assoc B₀, umul_inv s, Matrix.mul_one]
          abel
  have hlast : ∀ i : Fin a, i.castSucc < Fin.last a := fun i => Fin.castSucc_lt_last i
  have hD : ∀ z, (∑ k, B k * d k) *ᵥ z ∈ W (Fin.last a) := fun z =>
    sum_col_mem hB d (fun i hi => absurd (hlast i) hi) z
  simp only [flagN, Set.mem_ofPred_eq]
  refine ⟨fun i v hv => ?_, fun v hv => ?_⟩
  · rw [hsub]
    refine map_mem hA _ (W i.castSucc) (fun l hl u => ?_) hv
    rw [hNA l, ← Matrix.mulVec_mulVec]
    refine hG _ _ (sum_col_mem hB (fun k => (x k)⁻¹ * p k l - p k l * (y l)⁻¹) (fun k hk => hq0 l k ?_) u)
    rw [Fin.castSucc_lt_castSucc_iff, not_lt] at hk
    rw [Fin.castSucc_lt_succ_iff] at hl
    exact hl.trans hk
  · rw [hsub]

    have hBJ : ∀ i, (B i)ᴴ *ᵥ (Jm ε *ᵥ v) = 0 := by
      intro i
      funext c
      have hc := hv _ (col_mem hB (hlast i) (Pi.single c 1))
      rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec] at hc
      simpa using hc
    have hdec : v = (∑ i, B i *ᵥ ((B i)ᴴ *ᵥ v)) + B₀ *ᵥ (B₀ᴴ *ᵥ v) := by
      have hF' := hF
      unfold IsFrame at hF'
      obtain ⟨-, -, -, -, -, -, hsum⟩ := hF'
      have := congrArg (· *ᵥ v) hsum
      simp only [Matrix.one_mulVec, Matrix.add_mulVec, Matrix.sum_mulVec, ← Matrix.mulVec_mulVec, hBJ,
        Matrix.mulVec_zero, Finset.sum_const_zero, add_zero] at this
      exact this.symm
    rw [hdec, Matrix.mulVec_add]
    refine add_mem ?_ ?_
    · refine map_mem hB _ (W (Fin.last a)) (fun i _ u => ?_)
        ((hB _ _).2 ⟨_, fun i hi => absurd (hlast i) hi, rfl⟩)
      rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, hMB i, Matrix.sub_mulVec]
      refine sub_mem ?_ (col_mem hB (hlast i) u)
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
      exact hG _ _ (col_mem hB (hlast i) _)
    · rw [Matrix.mulVec_mulVec, hNB₀, Matrix.sub_mulVec]
      refine sub_mem ?_ ?_
      · rw [← Matrix.mulVec_mulVec]
        exact hD _
      · rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
        exact hG _ _ (hD _)

end GlobalTheory.LeviUnip
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HasEuclideanBallVolumeHaarComplexGLInverse
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.LeviIso
open Formalism.REAL (hs)

noncomputable section

namespace GlobalTheory.LeviIso.RadLoc

section
open scoped Matrix.Norms.Frobenius

theorem hs_eq_norm_sq {j : ℕ} (M : Matrix (Fin j) (Fin j) ℂ) : hs M = ‖M‖ ^ 2 := by
  rw [Matrix.frobenius_norm_def, ← Real.sqrt_eq_rpow, Real.sq_sqrt (by positivity)]
  simp [hs]

theorem hs_inv_compare {j : ℕ} (x : Matrix (Fin j) (Fin j) ℂ) (hx : x.det ≠ 0) {a : ℝ} (ha : 0 < a)
    (ha1 : a < 1) (h : hs (x⁻¹ - 1) ≤ (1 - a) ^ 2) :
    a ^ 2 * hs (x - 1) ≤ hs (x⁻¹ - 1) ∧ a ^ 2 * hs (x⁻¹ - 1) ≤ hs (x - 1) := by
  simp only [hs_eq_norm_sq] at *
  have e : (x⁻¹ - 1) + (x - 1) = -((x⁻¹ - 1) * (x - 1)) := by
    rw [sub_mul, mul_sub, Matrix.nonsing_inv_mul _ (Ne.isUnit hx)]
    simp
    abel
  have h1 : ‖(x⁻¹ - 1) + (x - 1)‖ ≤ ‖x⁻¹ - 1‖ * ‖x - 1‖ := by
    rw [e, norm_neg]; exact norm_mul_le _ _
  have h2 : ‖x⁻¹ - 1‖ ≤ ‖(x⁻¹ - 1) + (x - 1)‖ + ‖x - 1‖ := by
    simpa using norm_sub_le ((x⁻¹ - 1) + (x - 1)) (x - 1)
  have h3 : ‖x - 1‖ ≤ ‖(x⁻¹ - 1) + (x - 1)‖ + ‖x⁻¹ - 1‖ := by
    simpa using norm_sub_le ((x⁻¹ - 1) + (x - 1)) (x⁻¹ - 1)
  have hA := norm_nonneg (x - 1)
  have hB := norm_nonneg (x⁻¹ - 1)
  generalize ‖x - 1‖ = A at *
  generalize ‖x⁻¹ - 1‖ = B at *
  have h4 : B ≤ 1 - a := (sq_le_sq₀ hB (by linarith)).1 h
  have h5 : B * A ≤ (1 - a) * A := mul_le_mul_of_nonneg_right h4 hA
  rw [← mul_pow, ← mul_pow, sq_le_sq₀ (by positivity) hB, sq_le_sq₀ (by positivity) hA]
  constructor
  · linarith
  · have h6 : a * B ≤ a * ((2 - a) * A) := mul_le_mul_of_nonneg_left (by linarith) ha.le
    nlinarith [mul_nonneg (sq_nonneg (1 - a)) hA]

end

theorem hs_nonneg {j : ℕ} (M : Matrix (Fin j) (Fin j) ℂ) : 0 ≤ hs M := by
  unfold hs; positivity

theorem continuous_hs {j : ℕ} : Continuous (hs : Matrix (Fin j) (Fin j) ℂ → ℝ) := by
  unfold hs; fun_prop

def unitBallAt (j : ℕ) (s : ℝ) : Set (Fin j → Fin j → ℂ) := {x | hs (Matrix.of x - 1) ≤ s ^ 2}

theorem measurableSet_unitBallAt (j : ℕ) (s : ℝ) : MeasurableSet (unitBallAt j s) := by
  refine (isClosed_le (continuous_hs.comp ?_) continuous_const).measurableSet
  exact (continuous_id (X := Matrix (Fin j) (Fin j) ℂ)).sub continuous_const

theorem volume_unitBallAt (j : ℕ) {s : ℝ} (hs0 : 0 < s) :
    volume (unitBallAt j s) = ENNReal.ofReal (s ^ (2 * j ^ 2)) *
      volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (2 * j ^ 2))) 1) := by
  have hd : Module.finrank ℝ (EuclideanSpace ℂ (Fin j × Fin j)) = 2 * j ^ 2 := by
    rw [(WithLp.linearEquiv 2 ℝ (Fin j × Fin j → ℂ)).finrank_eq, Module.finrank_pi_fintype]
    simp [Complex.finrank_real_complex]
    ring
  set e := PoissonV.coords (Fin j) (Fin j) with he
  rw [← (PoissonV.measurePreserving_coords (Fin j) (Fin j)).measure_preimage
    (measurableSet_unitBallAt j s).nullMeasurableSet, ← he]
  have h1 : e ⁻¹' unitBallAt j s =
      Metric.closedBall (e.symm (Matrix.of.symm (1 : Matrix (Fin j) (Fin j) ℂ))) s := by
    ext z
    rw [mem_closedBall_iff_norm, ← sq_le_sq₀ (norm_nonneg _) hs0.le, ← PoissonV.norm_sq_coords, ← he,
      map_sub, e.apply_symm_apply]
    rfl
  rw [h1, Measure.addHaar_closedBall _ _ hs0.le, hd]
  congr 1
  rw [← hd]
  have h := (stdOrthonormalBasis ℝ (EuclideanSpace ℂ (Fin j × Fin j))).measurePreserving_repr
  rw [← h.measure_preimage measurableSet_ball.nullMeasurableSet]
  congr 1
  ext x
  simp

theorem exists_subset {j : ℕ} {P : (Fin j → Fin j → ℂ) → Prop}
    (h : ∀ᶠ x in nhds (Matrix.of.symm (1 : Matrix (Fin j) (Fin j) ℂ)), P x) :
    ∃ δ > 0, ∀ s, 0 ≤ s → s < δ → ∀ x ∈ unitBallAt j s, P x := by
  obtain ⟨δ, hδ, H⟩ := Metric.eventually_nhds_iff.1 h
  refine ⟨δ, hδ, fun s hs0 hsδ x hx => H (lt_of_le_of_lt ?_ hsδ)⟩
  rw [dist_eq_norm, pi_norm_le_iff_of_nonneg hs0]
  intro r
  rw [pi_norm_le_iff_of_nonneg hs0]
  intro c
  rw [← sq_le_sq₀ (norm_nonneg _) hs0]
  refine le_trans ?_ hx
  unfold hs
  refine le_trans ?_ (Finset.single_le_sum (fun i _ => by positivity) (Finset.mem_univ r))
  exact Finset.single_le_sum (f := fun c => ‖(Matrix.of x - 1) r c‖ ^ 2) (fun i _ => by positivity)
    (Finset.mem_univ c)

theorem eventually_good (j : ℕ) {a : ℝ} (ha : 0 < a) (ha1 : a < 1) :
    ∀ᶠ x : Fin j → Fin j → ℂ in nhds (Matrix.of.symm (1 : Matrix (Fin j) (Fin j) ℂ)),
      (a ≤ (‖(Matrix.of x).det‖ ^ 2)⁻¹ ^ j ∧ (‖(Matrix.of x).det‖ ^ 2)⁻¹ ^ j ≤ a⁻¹) ∧
      a ^ 2 * hs (Matrix.of x - 1) ≤ hs ((Matrix.of x)⁻¹ - 1) ∧
      a ^ 2 * hs ((Matrix.of x)⁻¹ - 1) ≤ hs (Matrix.of x - 1) := by
  show ∀ᶠ x : Matrix (Fin j) (Fin j) ℂ in nhds 1,
      (a ≤ (‖x.det‖ ^ 2)⁻¹ ^ j ∧ (‖x.det‖ ^ 2)⁻¹ ^ j ≤ a⁻¹) ∧
      a ^ 2 * hs (x - 1) ≤ hs (x⁻¹ - 1) ∧ a ^ 2 * hs (x⁻¹ - 1) ≤ hs (x - 1)
  have hdet : Continuous fun x : Matrix (Fin j) (Fin j) ℂ => x.det := continuous_id.matrix_det
  have h1 : ContinuousAt (fun x : Matrix (Fin j) (Fin j) ℂ => (‖x.det‖ ^ 2)⁻¹ ^ j) 1 :=
    (((hdet.norm.pow 2).continuousAt).inv₀ (by simp)).pow j
  have h2 : ContinuousAt (fun x : Matrix (Fin j) (Fin j) ℂ => hs (x⁻¹ - 1)) 1 := by
    refine continuous_hs.continuousAt.comp (ContinuousAt.sub (continuousAt_matrix_inv _ ?_) continuousAt_const)
    rw [Ring.inverse_eq_inv']
    exact continuousAt_inv₀ (by simp)
  have h3 := h1.eventually (lt_mem_nhds (a := a) (by simpa using ha1))
  have h4 := h1.eventually (gt_mem_nhds (a := a⁻¹) (by simpa using (one_lt_inv₀ ha).2 ha1))
  have h5 := h2.eventually (gt_mem_nhds (a := (1 - a) ^ 2) (by
    have : 0 < 1 - a := by linarith
    simpa [hs] using pow_pos this 2))
  have h6 := (hdet.continuousAt (x := 1)).eventually_ne (y := 0) (by simp)
  filter_upwards [h3, h4, h5, h6] with x x3 x4 x5 x6
  exact ⟨⟨x3.le, x4.le⟩, hs_inv_compare x x6 ha ha1 x5.le⟩

theorem sandwich (j : ℕ) {a : ℝ} (ha : 0 < a) (ha1 : a < 1) :
    ∀ᶠ r : ℝ in nhdsWithin 0 (Set.Ioi 0),
      ENNReal.ofReal (a ^ (2 * j ^ 2 + 1)) * volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (2 * j ^ 2))) 1) ≤
        (ENNReal.ofReal (2 ^ (j ^ 2)) • haarLoc j)
          {x | Real.sqrt (hs (Matrix.of x - 1) + hs ((Matrix.of x)⁻¹ - 1)) ≤ r} /
          ENNReal.ofReal (r ^ (2 * j ^ 2)) ∧
      (ENNReal.ofReal (2 ^ (j ^ 2)) • haarLoc j)
          {x | Real.sqrt (hs (Matrix.of x - 1) + hs ((Matrix.of x)⁻¹ - 1)) ≤ r} /
          ENNReal.ofReal (r ^ (2 * j ^ 2)) ≤
      ENNReal.ofReal (a⁻¹ ^ (2 * j ^ 2 + 1)) *
        volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (2 * j ^ 2))) 1) := by
  obtain ⟨δ, hδ, H⟩ := exists_subset (eventually_good j ha ha1)
  filter_upwards [Ioo_mem_nhdsGT (mul_pos ha hδ)] with r ⟨hr, hrδ⟩
  have h2 : (0 : ℝ) < √2 := by positivity
  have h21 : (1 : ℝ) ≤ √2 := Real.one_le_sqrt.2 (by norm_num)
  have h22 : (√2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hr1 : r < δ := by nlinarith
  have hr2 : a * r / √2 < δ := by
    refine lt_of_le_of_lt (div_le_self (by positivity) h21) (by nlinarith)
  have hr3 : a⁻¹ * r / √2 < δ := by
    refine lt_of_le_of_lt (div_le_self (by positivity) h21) ?_
    rwa [inv_mul_lt_iff₀ ha]
  have hrd : ENNReal.ofReal (r ^ (2 * j ^ 2)) ≠ 0 := by
    simpa using pow_pos hr _
  have hvol : ∀ b : ℝ, 0 < b → ENNReal.ofReal (2 ^ (j ^ 2)) * (ENNReal.ofReal b *
      volume (unitBallAt j (b * r / √2))) = ENNReal.ofReal (b ^ (2 * j ^ 2 + 1)) *
        volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (2 * j ^ 2))) 1) * ENNReal.ofReal (r ^ (2 * j ^ 2)) := by
    intro b hb
    rw [volume_unitBallAt j (by positivity), mul_right_comm, ← mul_assoc, ← mul_assoc,
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (by positivity)]
    congr 2
    rw [div_pow, pow_mul √2, h22, mul_pow]
    field_simp
    ring
  constructor
  · rw [ENNReal.le_div_iff_mul_le (Or.inl hrd) (Or.inl ENNReal.ofReal_ne_top), ← hvol a ha,
      Measure.smul_apply, smul_eq_mul]
    gcongr
    refine le_trans ?_ (measure_mono (s := unitBallAt j (a * r / √2)) fun x hx => ?_)
    · rw [haarLoc, withDensity_apply _ (measurableSet_unitBallAt j _), ← setLIntegral_const]
      exact setLIntegral_mono' (measurableSet_unitBallAt j _) fun x hx =>
        ENNReal.ofReal_le_ofReal (H _ (by positivity) hr2 x hx).1.1
    · have h3 := (H _ (by positivity) hr2 x hx).2.2
      have h4 : hs (Matrix.of x - 1) ≤ a ^ 2 * r ^ 2 / 2 := by
        have : hs (Matrix.of x - 1) ≤ (a * r / √2) ^ 2 := hx
        rwa [div_pow, h22, mul_pow] at this
      have h5 : hs ((Matrix.of x)⁻¹ - 1) ≤ r ^ 2 / 2 :=
        le_of_mul_le_mul_left (a := a ^ 2) (by linarith) (by positivity)
      have h6 : a ^ 2 * r ^ 2 ≤ r ^ 2 := mul_le_of_le_one_left (by positivity) (by nlinarith)
      refine Real.sqrt_le_iff.2 ⟨hr.le, by linarith⟩
  · rw [ENNReal.div_le_iff hrd ENNReal.ofReal_ne_top, ← hvol a⁻¹ (by positivity),
      Measure.smul_apply, smul_eq_mul]
    gcongr
    refine le_trans (measure_mono (t := unitBallAt j (a⁻¹ * r / √2)) fun x hx => ?_) ?_
    · have h1 := (Real.sqrt_le_iff.1 hx).2
      have h0 := hs_nonneg ((Matrix.of x)⁻¹ - 1)
      have h0' := hs_nonneg (Matrix.of x - 1)
      have h3 := (H r hr.le hr1 x (show hs (Matrix.of x - 1) ≤ r ^ 2 by linarith)).2.1
      have h6 : a ^ 2 * hs (Matrix.of x - 1) ≤ hs (Matrix.of x - 1) :=
        mul_le_of_le_one_left h0' (by nlinarith)
      show hs (Matrix.of x - 1) ≤ (a⁻¹ * r / √2) ^ 2
      rw [div_pow, h22, mul_pow, inv_pow, le_div_iff₀ (by norm_num), le_inv_mul_iff₀ (by positivity)]
      linarith
    · rw [haarLoc, withDensity_apply _ (measurableSet_unitBallAt j _), ← setLIntegral_const]
      exact setLIntegral_mono' (measurableSet_unitBallAt j _) fun x hx =>
        ENNReal.ofReal_le_ofReal (H _ (by positivity) hr3 x hx).1.2

end GlobalTheory.LeviIso.RadLoc

namespace GlobalTheory.LeviIso

open RadLoc

theorem isRadial_haarLoc (j : ℕ) : IsRadial (ENNReal.ofReal (2 ^ (j ^ 2)) • haarLoc j)
    (fun x => Formalism.REAL.hs (Matrix.of x - 1) + Formalism.REAL.hs ((Matrix.of x)⁻¹ - 1)) (2 * j ^ 2) := by
  unfold IsRadial
  set ω := volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (2 * j ^ 2))) 1) with hω
  have hωt : ω ≠ ⊤ := measure_ball_lt_top.ne
  have hc : Filter.Tendsto (fun a : ℝ => ENNReal.ofReal (a ^ (2 * j ^ 2 + 1)) * ω) (nhds 1) (nhds ω) := by
    have : Filter.Tendsto (fun a : ℝ => ENNReal.ofReal (a ^ (2 * j ^ 2 + 1))) (nhds 1) (nhds 1) := by
      simpa using ENNReal.tendsto_ofReal ((continuous_pow (2 * j ^ 2 + 1)).tendsto (1 : ℝ))
    simpa using ENNReal.Tendsto.mul_const this (Or.inl one_ne_zero)
  have hi : Filter.Tendsto (fun a : ℝ => a⁻¹) (nhds 1) (nhds 1) := by
    simpa using Filter.Tendsto.inv₀ (Filter.tendsto_id (x := nhds (1 : ℝ))) one_ne_zero
  refine tendsto_order.2 ⟨fun b hb => ?_, fun b hb => ?_⟩
  · obtain ⟨a, h1, h2, h3⟩ := (((hc.eventually (lt_mem_nhds hb)).filter_mono nhdsWithin_le_nhds).and
      (Ioo_mem_nhdsLT (zero_lt_one' ℝ))).exists
    filter_upwards [sandwich j h2 h3] with r hr
    exact lt_of_lt_of_le h1 hr.1
  · obtain ⟨a, h1, h2, h3⟩ := ((((hc.comp hi).eventually (gt_mem_nhds hb)).filter_mono nhdsWithin_le_nhds).and
      (Ioo_mem_nhdsLT (zero_lt_one' ℝ))).exists
    filter_upwards [sandwich j h2 h3] with r hr
    exact lt_of_le_of_lt hr.2 h1

end GlobalTheory.LeviIso
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HilbertSchmidtEqReTrace
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.LeviIso
open Formalism.REAL (Jm hs Jm_mul_self Jm_conjTranspose)

namespace GlobalTheory.LeviIso

theorem trace_compress {n m : ℕ} (D : Matrix (Fin n) (Fin n) ℂ) (C : Matrix (Fin n) (Fin m) ℂ)
    (y : Matrix (Fin m) (Fin m) ℂ) (hC : Cᴴ * C = 1) (hD : D * C = C * y) :
    (Dᴴ * D * (C * Cᴴ)).trace = (yᴴ * y).trace := by
  have hcore : Cᴴ * (Dᴴ * D * C) = yᴴ * y :=
    calc Cᴴ * (Dᴴ * D * C) = (D * C)ᴴ * (D * C) := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = (C * y)ᴴ * (C * y) := by rw [hD]
      _ = yᴴ * (Cᴴ * C) * y := by simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = yᴴ * y := by rw [hC, Matrix.mul_one]
  rw [← Matrix.mul_assoc, Matrix.trace_mul_comm, hcore]

private theorem hs_eq_re_trace_conjTranspose_mul {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) : hs X = (trace (Xᴴ * X)).re := by
  unfold hs
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.re_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp [Complex.mul_re]

theorem hs_lev_sub_one : ∀ (n n₀ a : ℕ) (j : Fin a → ℕ) (ε : Fin n → Bool) (ε₀ : Fin n₀ → Bool)
    (B : ∀ i, Matrix (Fin n) (Fin (j i)) ℂ) (B₀ : Matrix (Fin n) (Fin n₀) ℂ), IsFrame ε ε₀ B B₀ →
    ∀ (x : ∀ i, Matrix (Fin (j i)) (Fin (j i)) ℂ) (g : Matrix (Fin n₀) (Fin n₀) ℂ),
    Formalism.REAL.hs (lev ε B B₀ x g - 1) =
      ∑ i, (Formalism.REAL.hs (x i - 1) + Formalism.REAL.hs ((x i)⁻¹ - 1)) + Formalism.REAL.hs (g - 1) := by
  intro n n₀ a j ε ε₀ B B₀ h x g
  have hJ : ∀ i, (Jm ε * B i)ᴴ * (Jm ε * B i) = 1 := fun i => by
    rw [Matrix.conjTranspose_mul, Jm_conjTranspose, Matrix.mul_assoc, ← Matrix.mul_assoc (Jm ε),
      Jm_mul_self, Matrix.one_mul, h.1 i]
  have hsplit : (1 : Matrix (Fin n) (Fin n) ℂ) =
      ∑ i, B i * (B i)ᴴ + ∑ i, (Jm ε * B i) * (Jm ε * B i)ᴴ + B₀ * B₀ᴴ := by
    rw [← h.2.2.2.2.2.2]
    congr 2
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.conjTranspose_mul, Jm_conjTranspose]
    simp only [Matrix.mul_assoc]
  have hsub : ∀ {m : ℕ} (C : Matrix (Fin n) (Fin m) ℂ) (y : Matrix (Fin m) (Fin m) ℂ),
      lev ε B B₀ x g * C = C * y → (lev ε B B₀ x g - 1) * C = C * (y - 1) := by
    intro m C y hy
    rw [Matrix.sub_mul, hy, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one]
  have hconj : ∀ {m : ℕ} (Y : Matrix (Fin m) (Fin m) ℂ), hs Yᴴ = hs Y := by
    intro m Y
    rw [hs_eq_re_trace_conjTranspose_mul, hs_eq_re_trace_conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.trace_mul_comm]
  set M := lev ε B B₀ x g - 1 with hM
  have eB : ∀ i, (Mᴴ * M * (B i * (B i)ᴴ)).trace = ((x i - 1)ᴴ * (x i - 1)).trace := fun i =>
    trace_compress M (B i) _ (h.1 i) (hsub _ _ (h.lev_mul_B x g i))
  have eJ : ∀ i, (Mᴴ * M * ((Jm ε * B i) * (Jm ε * B i)ᴴ)).trace =
      (((x i)⁻¹ᴴ - 1)ᴴ * ((x i)⁻¹ᴴ - 1)).trace := fun i =>
    trace_compress M (Jm ε * B i) _ (hJ i) (hsub _ _ (h.lev_mul_JB x g i))
  have e0 : (Mᴴ * M * (B₀ * B₀ᴴ)).trace = ((g - 1)ᴴ * (g - 1)).trace :=
    trace_compress M B₀ _ h.2.2.2.2.1 (hsub _ _ (h.lev_mul_B₀ x g))
  rw [hs_eq_re_trace_conjTranspose_mul, ← Matrix.mul_one (Mᴴ * M), hsplit]
  simp only [Matrix.mul_add, Matrix.mul_sum, Matrix.trace_add, Matrix.trace_sum, Complex.add_re,
    Complex.re_sum, eB, eJ, e0, Finset.sum_add_distrib]
  have hinv : ∀ i, (x i)⁻¹ᴴ - 1 = ((x i)⁻¹ - 1)ᴴ := fun i => by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one]
  simp only [hinv, ← hs_eq_re_trace_conjTranspose_mul, hconj]

end GlobalTheory.LeviIso
end

