module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.SymZeroCommFrame
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0188
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.FriedrichsKernels.Friedrichs
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0189
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.WaveSt

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothCholeskyFactor
section
open MeasureTheory Matrix Topology Filter
open scoped ContDiff ENNReal ComplexOrder Pointwise
open PositivityTheory.RgTw (Mat G hb)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.ConeHaar
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable section

namespace GlobalTheory.CompanionTheory.ConeHaar.Chol

variable {n m k : ℕ}

def invRoot (P : Mat (n + 1)) : ℝ := (Real.sqrt (P 0 0).re)⁻¹

def col (P : Mat (n + 1)) (i : Fin n) : ℂ := P i.succ 0 * (invRoot P : ℂ)

def schur (P : Mat (n + 1)) : Mat n :=
  Matrix.of fun i j => P i.succ j.succ - col P i * star (col P j)

def step (σ : Mat n → Mat n) (P : Mat (n + 1)) : Mat (n + 1) :=
  Matrix.of fun i j =>
    Fin.cases (motive := fun _ => ℂ)
      (Fin.cases (motive := fun _ => ℂ) ((Real.sqrt (P 0 0).re : ℝ) : ℂ) (fun _ => 0) j)
      (fun i' => Fin.cases (motive := fun _ => ℂ) (col P i') (fun j' => σ (schur P) i' j') j) i

lemma step_zero_zero (σ : Mat n → Mat n) (P : Mat (n + 1)) :
    step σ P 0 0 = ((Real.sqrt (P 0 0).re : ℝ) : ℂ) := rfl

lemma step_zero_succ (σ : Mat n → Mat n) (P : Mat (n + 1)) (j : Fin n) :
    step σ P 0 j.succ = 0 := rfl

lemma step_succ_zero (σ : Mat n → Mat n) (P : Mat (n + 1)) (i : Fin n) :
    step σ P i.succ 0 = col P i := rfl

lemma step_succ_succ (σ : Mat n → Mat n) (P : Mat (n + 1)) (i j : Fin n) :
    step σ P i.succ j.succ = σ (schur P) i j := rfl

lemma lead_pos {P : Mat (n + 1)} (hP : P.PosDef) : 0 < (P 0 0).re :=
  (Complex.pos_iff.1 (hP.diag_pos (i := 0))).1

lemma lead_eq {P : Mat (n + 1)} (hP : P.PosDef) : (((P 0 0).re : ℝ) : ℂ) = P 0 0 := by
  apply Complex.ext
  · simp
  · simpa using (Complex.pos_iff.1 (hP.diag_pos (i := 0))).2

lemma root_mul_invRoot {P : Mat (n + 1)} (hP : P.PosDef) :
    Real.sqrt (P 0 0).re * invRoot P = 1 :=
  mul_inv_cancel₀ (Real.sqrt_pos.2 (lead_pos hP)).ne'

lemma lead_mul_invRoot {P : Mat (n + 1)} (hP : P.PosDef) :
    P 0 0 * ((invRoot P : ℂ) * (invRoot P : ℂ)) = 1 := by
  have h : (P 0 0).re * (invRoot P * invRoot P) = 1 := by
    have h1 := root_mul_invRoot hP
    have h2 := Real.mul_self_sqrt (lead_pos hP).le
    calc (P 0 0).re * (invRoot P * invRoot P)
        = (Real.sqrt (P 0 0).re * Real.sqrt (P 0 0).re) * (invRoot P * invRoot P) := by rw [h2]
      _ = (Real.sqrt (P 0 0).re * invRoot P) * (Real.sqrt (P 0 0).re * invRoot P) := by ring
      _ = 1 := by rw [h1]; ring
  rw [← lead_eq hP]
  exact_mod_cast h

lemma schur_posDef {P : Mat (n + 1)} (hP : P.PosDef) : (schur P).PosDef := by
  have hH : ∀ i j, star (P j i) = P i j := fun i j => hP.isHermitian.apply i j
  have hcs : star ((invRoot P : ℝ) : ℂ) = (invRoot P : ℂ) := by simp
  refine PosDef.of_dotProduct_mulVec_pos ?_ ?_
  · ext i j
    simp only [conjTranspose_apply, schur, of_apply, star_sub, star_mul', star_star, hH]
    ring
  · intro x hx
    set c : ℂ := (invRoot P : ℂ) with hc
    set w : ℂ := ∑ j, P 0 j.succ * x j with hw
    set u : ℂ := ∑ i, star (x i) * P i.succ 0 with hu
    set q : ℂ := ∑ i, star (x i) * ∑ j, P i.succ j.succ * x j with hq
    set t : ℂ := -(w * (c * c)) with ht
    let y : Fin (n + 1) → ℂ := Fin.cons t x
    have y0 : y 0 = t := rfl
    have ys : ∀ i : Fin n, y i.succ = x i := fun i => rfl
    have hy : y ≠ 0 := fun h => hx (funext fun i => by simpa [ys] using congrFun h i.succ)
    have hpos := hP.dotProduct_mulVec_pos hy
    have hW : ∑ j, star (col P j) * x j = w * c := by
      rw [hw, Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [col, star_mul', hH, hcs, ← hc]
      ring
    have hrow : ∀ i, (schur P *ᵥ x) i = (∑ j, P i.succ j.succ * x j) - col P i * (w * c) := by
      intro i
      rw [← hW]
      simp only [mulVec, dotProduct, schur, of_apply, sub_mul, Finset.sum_sub_distrib,
        Finset.mul_sum, mul_assoc]
    have hU : ∑ i, star (x i) * col P i = u * c := by
      rw [hu, Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [col, ← hc]
      ring
    have hL : star x ⬝ᵥ (schur P *ᵥ x) = q - (u * c) * (w * c) := by
      simp only [dotProduct, hrow, Pi.star_apply, mul_sub, Finset.sum_sub_distrib]
      congr 1
      generalize w * c = v
      rw [← hU, Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    have h0 : (P *ᵥ y) 0 = P 0 0 * t + w := by
      simp only [mulVec, dotProduct, Fin.sum_univ_succ, y0, ys, hw]
    have hs : ∀ i : Fin n, (P *ᵥ y) i.succ = P i.succ 0 * t + ∑ j, P i.succ j.succ * x j := by
      intro i
      simp only [mulVec, dotProduct, Fin.sum_univ_succ, y0, ys]
    have hz : P 0 0 * t + w = 0 := by
      have := lead_mul_invRoot hP
      rw [← hc] at this
      rw [ht]
      linear_combination (-w) * this
    have hR : star y ⬝ᵥ (P *ᵥ y) = u * t + q := by
      rw [dotProduct, Fin.sum_univ_succ]
      simp only [Pi.star_apply, h0, hs, y0, ys, hz, mul_zero, zero_add, mul_add,
        Finset.sum_add_distrib]
      congr 1
      rw [hu, Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    have hk : star x ⬝ᵥ (schur P *ᵥ x) = star y ⬝ᵥ (P *ᵥ y) := by
      rw [hL, hR, ht]
      ring
    rw [hk]
    exact hpos

lemma step_mul {σ : Mat n → Mat n} {P : Mat (n + 1)} (hP : P.PosDef)
    (hσ : σ (schur P) * (σ (schur P))ᴴ = schur P) : step σ P * (step σ P)ᴴ = P := by
  have hH : ∀ i j, star (P j i) = P i j := fun i j => hP.isHermitian.apply i j
  have hr : ((Real.sqrt (P 0 0).re : ℝ) : ℂ) * (invRoot P : ℂ) = 1 := by
    exact_mod_cast root_mul_invRoot hP
  have hrr : ((Real.sqrt (P 0 0).re : ℝ) : ℂ) * ((Real.sqrt (P 0 0).re : ℝ) : ℂ) = P 0 0 := by
    rw [← lead_eq hP]
    exact_mod_cast Real.mul_self_sqrt (lead_pos hP).le
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
  · simp only [Matrix.mul_apply, conjTranspose_apply, Fin.sum_univ_succ, step_zero_zero, step_zero_succ]
    simp [hrr]
  · simp only [Matrix.mul_apply, conjTranspose_apply, Fin.sum_univ_succ, step_zero_zero, step_zero_succ,
      step_succ_zero]
    simp only [col, star_mul', hH]
    simp
    linear_combination (P 0 j.succ) * hr
  · simp only [Matrix.mul_apply, conjTranspose_apply, Fin.sum_univ_succ, step_zero_zero, step_zero_succ,
      step_succ_zero, step_succ_succ]
    simp [col]
    linear_combination (P i.succ 0) * hr
  · have h := congrFun (congrFun hσ i) j
    simp only [Matrix.mul_apply, conjTranspose_apply] at h
    simp only [Matrix.mul_apply, conjTranspose_apply, Fin.sum_univ_succ, step_succ_zero, step_succ_succ, h]
    simp [schur]

lemma contDiff_entry (i j : Fin m) : ContDiff ℝ ∞ (fun P : Mat m => P i j) :=
  contDiff_apply_apply ℝ i j

lemma contDiffOn_mat {s : Set (Mat k)} {f : Mat k → Mat m}
    (h : ∀ i j, ContDiffOn ℝ ∞ (fun P => f P i j) s) : ContDiffOn ℝ ∞ f s :=
  contDiffOn_pi.2 fun i => contDiffOn_pi.2 fun j => h i j

lemma contDiffOn_entry {s : Set (Mat k)} {f : Mat k → Mat m} (h : ContDiffOn ℝ ∞ f s)
    (i j : Fin m) : ContDiffOn ℝ ∞ (fun P => f P i j) s :=
  (contDiff_entry i j).comp_contDiffOn h

lemma contDiffOn_root :
    ContDiffOn ℝ ∞ (fun P : Mat (n + 1) => Real.sqrt (P 0 0).re) {P | P.PosDef} :=
  ContDiffOn.sqrt (Complex.reCLM.contDiff.comp (contDiff_entry 0 0)).contDiffOn
    fun _ hP => (lead_pos hP).ne'

lemma contDiffOn_invRoot :
    ContDiffOn ℝ ∞ (fun P : Mat (n + 1) => ((invRoot P : ℝ) : ℂ)) {P | P.PosDef} :=
  Complex.ofRealCLM.contDiff.comp_contDiffOn
    (contDiffOn_root.inv fun _ hP => (Real.sqrt_pos.2 (lead_pos hP)).ne')

lemma contDiffOn_col (i : Fin n) :
    ContDiffOn ℝ ∞ (fun P : Mat (n + 1) => col P i) {P | P.PosDef} :=
  (contDiff_entry i.succ 0).contDiffOn.mul contDiffOn_invRoot

lemma contDiffOn_star_col (i : Fin n) :
    ContDiffOn ℝ ∞ (fun P : Mat (n + 1) => star (col P i)) {P | P.PosDef} :=
  Complex.conjCLE.contDiff.comp_contDiffOn (contDiffOn_col i)

lemma contDiffOn_schur : ContDiffOn ℝ ∞ (schur (n := n)) {P | P.PosDef} :=
  contDiffOn_mat fun i j =>
    (contDiff_entry i.succ j.succ).contDiffOn.sub ((contDiffOn_col i).mul (contDiffOn_star_col j))

lemma contDiffOn_step {σ : Mat n → Mat n} (hσ : ContDiffOn ℝ ∞ σ {P | P.PosDef}) :
    ContDiffOn ℝ ∞ (step σ) {P | P.PosDef} := by
  refine contDiffOn_mat fun i j => ?_
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
  · exact Complex.ofRealCLM.contDiff.comp_contDiffOn contDiffOn_root
  · exact contDiffOn_const
  · exact contDiffOn_col i
  · exact contDiffOn_entry (hσ.comp contDiffOn_schur fun _ hP => schur_posDef hP) i j

theorem exists_smooth_section :
    ∀ n : ℕ, ∃ σ₀ : Mat n → Mat n, ContDiffOn ℝ ∞ σ₀ {P | P.PosDef} ∧
      ∀ P : Mat n, P.PosDef → σ₀ P * (σ₀ P)ᴴ = P := by
  intro n
  induction n with
  | zero => exact ⟨id, contDiffOn_id, fun P _ => Subsingleton.elim _ _⟩
  | succ n ih =>
    obtain ⟨σ, hσ, hf⟩ := ih
    exact ⟨step σ, contDiffOn_step hσ, fun P hP => step_mul hP (hf _ (schur_posDef hP))⟩

end GlobalTheory.CompanionTheory.ConeHaar.Chol
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SobolevIntegrationByParts
section
noncomputable section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty

namespace GlobalTheory.CompanionTheory.FcCalc.Ibp

open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc
open GlobalTheory.CompanionTheory.WeightIbp (isOpen_invertible val_mem_invertible weight_ibp)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

def psi (t : ℝ) : ℝ := Real.smoothTransition (2 - t)

theorem psi_contDiff : ContDiff ℝ ∞ psi :=
  Real.smoothTransition.contDiff.comp (contDiff_const.sub contDiff_id)

theorem psi_eq_one {t : ℝ} (h : t ≤ 1) : psi t = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

theorem psi_eq_zero {t : ℝ} (h : 2 ≤ t) : psi t = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

theorem exists_deriv_bound : ∃ D : ℝ, ∀ t, ‖deriv psi t‖ ≤ D := by
  have hc : Continuous (deriv psi) := psi_contDiff.continuous_deriv (by simp)
  refine HasCompactSupport.exists_bound_of_continuous
    (HasCompactSupport.intro (isCompact_Icc (a := (1 : ℝ)) (b := 2)) fun t ht => ?_) hc
  rcases lt_or_ge t 1 with h | h
  · have e : psi =ᶠ[𝓝 t] fun _ => (1 : ℝ) := by
      filter_upwards [Iio_mem_nhds h] with s hs using psi_eq_one (le_of_lt hs)
    rw [e.deriv_eq]; simp
  · have h2 : 2 < t := by
      by_contra hn
      exact ht ⟨h, not_lt.1 hn⟩
    have e : psi =ᶠ[𝓝 t] fun _ => (0 : ℝ) := by
      filter_upwards [Ioi_mem_nhds h2] with s hs using psi_eq_zero (le_of_lt hs)
    rw [e.deriv_eq]; simp

def chi (R : ℝ) (y : Mat n) : ℝ := psi (R⁻¹ * lg y)

theorem chi_smooth (hL : LgFacts) (R : ℝ) : ContDiffOn ℝ ∞ (chi R : Mat n → ℝ) (GLs n) :=
  psi_contDiff.comp_contDiffOn (contDiffOn_const.mul (hL n).2.2.2.1)

theorem chi_cpt {R : ℝ} (hR : 0 < R) : Cpt (chi R : Mat n → ℝ) := by
  refine ⟨2 * R, fun y _ h => psi_eq_zero ?_⟩
  rw [inv_mul_eq_div, le_div_iff₀ hR]
  exact h.le

theorem chi_eq_one {R : ℝ} (hR : 0 < R) {y : Mat n} (h : lg y ≤ R) : chi R y = 1 := by
  refine psi_eq_one ?_
  rw [inv_mul_eq_div, div_le_iff₀ hR]
  linarith

theorem chi_abs_le (R : ℝ) (y : Mat n) : ‖((chi R y : ℝ) : ℂ)‖ ≤ 1 := by
  have h0 := Real.smoothTransition.nonneg (2 - R⁻¹ * lg y)
  have h1 := Real.smoothTransition.le_one (2 - R⁻¹ * lg y)
  have e : chi R y = Real.smoothTransition (2 - R⁻¹ * lg y) := rfl
  rw [Complex.norm_real, e, Real.norm_of_nonneg h0]
  exact h1

theorem chi_fderiv_le (hL : LgFacts) {D : ℝ} (hD : ∀ t, ‖deriv psi t‖ ≤ D) {R : ℝ} (hR : 0 < R) {x : Mat n}
    (hx : x ∈ GLs n) (v : Mat n) : |fderiv ℝ (chi R) x v| ≤ D * (R⁻¹ * |fderiv ℝ lg x v|) := by
  have hlg : HasFDerivAt (lg : Mat n → ℝ) (fderiv ℝ lg x) x :=
    (((hL n).2.2.2.1.contDiffAt (isOpen_invertible.mem_nhds hx)).differentiableAt (by simp)).hasFDerivAt
  have hp : HasDerivAt psi (deriv psi (R⁻¹ * lg x)) (R⁻¹ * lg x) :=
    ((psi_contDiff.differentiable (by simp)) _).hasDerivAt
  have h := (hp.comp_hasFDerivAt x (hlg.const_mul R⁻¹)).fderiv
  have e : fderiv ℝ (chi R) x v = deriv psi (R⁻¹ * lg x) * (R⁻¹ * fderiv ℝ lg x v) := by
    have e' : chi R = psi ∘ fun y : Mat n => R⁻¹ * lg y := rfl
    rw [e']
    exact (DFunLike.congr_fun h v).trans rfl
  rw [e, abs_mul, abs_mul, abs_of_pos (inv_pos.2 hR)]
  exact mul_le_mul_of_nonneg_right (hD _) (by positivity)

theorem chi_continuous (hL : LgFacts) (R : ℝ) : Continuous fun y : G n => ((chi R y.val : ℝ) : ℂ) :=
  Complex.continuous_ofReal.comp
    ((chi_smooth hL R).continuousOn.comp_continuous Units.continuous_val val_mem_invertible)

section Lim

variable [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n))

theorem tendsto_chi (hL : LgFacts) {h : G n → ℂ} (hh : Integrable h μ) :
    Tendsto (fun k : ℕ => ∫ y : G n, ((chi ((k : ℝ) + 1) y.val : ℝ) : ℂ) * h y ∂μ) atTop (𝓝 (∫ y, h y ∂μ)) := by
  refine tendsto_integral_of_dominated_convergence (fun y => ‖h y‖) (fun k => ?_) hh.norm (fun k => ?_) ?_
  · exact (chi_continuous hL _).aestronglyMeasurable.mul hh.1
  · refine Eventually.of_forall fun y => ?_
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (chi_abs_le _ _)
  · refine Eventually.of_forall fun y => ?_
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop ⌈lg y.val⌉₊] with k hk
    have h1 : lg y.val ≤ (k : ℝ) + 1 := by
      have := (Nat.le_ceil (lg y.val)).trans (Nat.cast_le.2 hk)
      linarith
    rw [chi_eq_one (by positivity) h1]
    simp

theorem tendsto_chi_deriv (hL : LgFacts) {X : Mat n} {C : ℝ} (hC : ∀ x ∈ GLs n, |fderiv ℝ lg x (x * X)| ≤ C)
    {h : G n → ℂ} (hh : Integrable h μ) :
    Tendsto (fun k : ℕ => ∫ y : G n, ((fderiv ℝ (chi ((k : ℝ) + 1)) y.val (y.val * X) : ℝ) : ℂ) * h y ∂μ) atTop (𝓝 0) := by
  obtain ⟨D, hD⟩ := exists_deriv_bound
  have hD0 : 0 ≤ D := (norm_nonneg _).trans (hD 0)
  have hC0 : ∀ x ∈ GLs n, 0 ≤ C := fun x hx => (abs_nonneg _).trans (hC x hx)
  have hC1 : 0 ≤ C := hC0 _ (val_mem_invertible (1 : G n))
  have hb : ∀ k : ℕ, ‖∫ y : G n, ((fderiv ℝ (chi ((k : ℝ) + 1)) y.val (y.val * X) : ℝ) : ℂ) * h y ∂μ‖ ≤
      (D * C * ∫ y, ‖h y‖ ∂μ) * ((k : ℝ) + 1)⁻¹ := by
    intro k
    have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    have := norm_integral_le_of_norm_le (μ := μ)
      (f := fun y : G n => ((fderiv ℝ (chi ((k : ℝ) + 1)) y.val (y.val * X) : ℝ) : ℂ) * h y)
      (hh.norm.const_mul (D * (((k : ℝ) + 1)⁻¹ * C)))
      (Eventually.of_forall fun y => by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
        refine (chi_fderiv_le hL hD hk (val_mem_invertible y) _).trans ?_
        gcongr
        exact hC _ (val_mem_invertible y))
    refine this.trans (le_of_eq ?_)
    rw [integral_const_mul]
    ring
  refine squeeze_zero_norm hb ?_
  have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (D * C * ∫ y, ‖h y‖ ∂μ)
  simpa [one_div] using this

end Lim

section Pair

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

theorem exists_coeff (X : Mat n) : ∃ c : Bool × Fin n × Fin n → ℝ, X = ∑ p, c p • bs p := by
  refine ⟨fun p => if p.1 then (X p.2.1 p.2.2).re else (X p.2.1 p.2.2).im, ?_⟩
  ext i j
  simp only [Matrix.sum_apply, Matrix.smul_apply, Fintype.sum_prod_type, Fintype.sum_bool, bs, Matrix.single_apply]
  simp [Finset.sum_add_distrib, Finset.sum_ite_eq, ite_and]

theorem Rd_expand (f : Mat n → V) {X : Mat n} {c : Bool × Fin n × Fin n → ℝ} (h : X = ∑ p, c p • bs p) (g : Mat n) :
    Rd X f g = ∑ p, c p • Rd (bs p) f g := by
  simp only [Rd]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [h, Matrix.mul_sum, map_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Matrix.mul_smul, map_smul]

theorem lg_bound (hL : LgFacts) (X : Mat n) : ∃ C : ℝ, ∀ x ∈ GLs n, |fderiv ℝ lg x (x * X)| ≤ C := by
  obtain ⟨c, hc⟩ := exists_coeff X
  obtain ⟨C, hC⟩ := (hL n).2.2.2.2.2.2
  refine ⟨∑ p, |c p| * C, fun x hx => ?_⟩
  have e : fderiv ℝ lg x (x * X) = ∑ p, c p * fderiv ℝ lg x (x * bs p) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hc, Matrix.mul_sum, map_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Matrix.mul_smul, map_smul, smul_eq_mul]
  rw [e]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun p _ => ?_)
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (hC x hx p) (abs_nonneg _)

variable [MeasurableSpace (G n)] [BorelSpace (G n)] {μ : Measure (G n)}

theorem memLp_Rd {f : Mat n → V} (hf : Sob μ f) (X : Mat n) : MemLp (fun y : G n => Rd X f y.val) 2 μ := by
  obtain ⟨c, hc⟩ := exists_coeff X
  have e : (fun y : G n => Rd X f y.val) = fun y : G n => ∑ p, c p • Rd (bs p) f y.val :=
    funext fun y => Rd_expand f hc y.val
  rw [e]
  exact MeasureTheory.memLp_finsetSum _ fun p _ => (hf.2 [p]).const_smul (c p)

theorem memLp_self {f : Mat n → V} (hf : Sob μ f) : MemLp (fun y : G n => f y.val) 2 μ := hf.2 []

theorem integrable_pair {a b : G n → V} (ha : MemLp a 2 μ) (hb : MemLp b 2 μ) :
    Integrable (fun y => ⟪a y, b y⟫_ℂ) μ := by
  refine (L2.integrable_inner (𝕜 := ℂ) (ha.toLp a) (hb.toLp b)).congr ?_
  filter_upwards [ha.coeFn_toLp, hb.coeFn_toLp] with y h1 h2
  rw [h1, h2]

theorem inner_cls {a b : Mat n → V} (ha : MemLp (fun y : G n => a y.val) 2 μ)
    (hb : MemLp (fun y : G n => b y.val) 2 μ) :
    ⟪cls μ a, cls μ b⟫_ℂ = ∫ y : G n, ⟪a y.val, b y.val⟫_ℂ ∂μ := by
  simp only [cls, dif_pos ha, dif_pos hb]
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [ha.coeFn_toLp, hb.coeFn_toLp] with y h1 h2
  rw [h1, h2]

end Pair

theorem ibpSob : IbpSob := by
  intro n _ _ μ _ V _ _ hL _ hR f f' hf hf' X
  obtain ⟨C, hC⟩ := lg_bound hL X
  have m0 := memLp_self hf
  have m0' := memLp_self hf'
  have m1 := memLp_Rd hf X
  have m1' := memLp_Rd hf' X
  rw [inner_cls m1 m0', inner_cls m0 m1']
  have iA := integrable_pair m0 m1'
  have iB := integrable_pair m1 m0'
  have iC := integrable_pair m0 m0'
  have tA := tendsto_chi μ hL iA
  have tB := tendsto_chi μ hL iB
  have tC := tendsto_chi_deriv μ hL hC iC
  have key : ∀ k : ℕ, ∫ y : G n, ((chi ((k : ℝ) + 1) y.val : ℝ) : ℂ) * ⟪f y.val, Rd X f' y.val⟫_ℂ ∂μ =
      -(∫ y : G n, ((chi ((k : ℝ) + 1) y.val : ℝ) : ℂ) * ⟪Rd X f y.val, f' y.val⟫_ℂ ∂μ) -
        ∫ y : G n, ((fderiv ℝ (chi ((k : ℝ) + 1)) y.val (y.val * X) : ℝ) : ℂ) * ⟪f y.val, f' y.val⟫_ℂ ∂μ :=
    fun k => weight_ibp hR hL μ f' f (chi ((k : ℝ) + 1)) hf'.1 hf.1 (chi_smooth hL _) (chi_cpt (by positivity)) X
  have tA' := (tB.neg.sub tC).congr fun k => (key k).symm
  have e := tendsto_nhds_unique tA tA'
  rw [e, sub_zero, neg_neg]

end GlobalTheory.CompanionTheory.FcCalc.Ibp
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WaveCptBoundedTime
section
noncomputable section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace

open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.WaveMult

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.WaveMult

theorem lg_le_lg_mul_add (hL : LgFacts) {n : ℕ} {x y : Mat n} (hx : x ∈ GLs n) (hy : y ∈ GLs n) :
    lg x ≤ lg (x * y) + lg y := by
  have hdx : x.det ≠ 0 := hx
  have hdy : y.det ≠ 0 := hy
  have hxy : x * y ∈ GLs n := by
    change (x * y).det ≠ 0
    rw [Matrix.det_mul]
    exact mul_ne_zero hdx hdy
  have hu : IsUnit y.det := isUnit_iff_ne_zero.mpr hdy
  have h1 := (hL n).1 (x * y) hxy y⁻¹ (inv_mem_GLs hy)
  have h2 := (hL n).2.1 y hy
  rw [Matrix.mul_nonsing_inv_cancel_right _ _ hu, h2] at h1
  exact h1

theorem wave_cpt_bounded_time : LgFacts → WaveSpeed → ∀ (n : ℕ) (E : KMod n) (u : ℝ → Mat n → E.V),
    IsWave E u → Cpt (u 0) → ∀ T : ℝ, ∃ R : ℝ, ∀ t, |t| ≤ T → ∀ y ∈ GLs n, R < lg y → u t y = 0 := by
  intro hL hS n E u hu hc T
  obtain ⟨c, hc'⟩ := hS n
  obtain ⟨R₀, hR₀⟩ := hc
  refine ⟨R₀ + |c| * (1 + |T|), fun t ht x hx hlg => hc' E u hu t x hx fun y hy hly => ?_⟩
  have hxy : x * y ∈ GLs n := by
    change (x * y).det ≠ 0
    rw [Matrix.det_mul]
    exact mul_ne_zero hx hy
  refine hR₀ (x * y) hxy ?_
  have h1 := lg_le_lg_mul_add hL hx hy
  have h2 : |t| ≤ |T| := ht.trans (le_abs_self T)
  have h3 : c * (1 + |t|) ≤ |c| * (1 + |T|) :=
    calc c * (1 + |t|) ≤ |c| * (1 + |t|) :=
          mul_le_mul_of_nonneg_right (le_abs_self c) (by positivity)
      _ ≤ |c| * (1 + |T|) := mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg c)
  linarith

end GlobalTheory.CompanionTheory.WaveMult
end
end

