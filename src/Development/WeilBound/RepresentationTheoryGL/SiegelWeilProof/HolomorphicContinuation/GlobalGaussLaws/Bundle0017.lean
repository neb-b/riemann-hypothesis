module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle0015
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SchwartzBilinear.Bundle0002
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle0016

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.AwayInC
section
noncomputable section

open scoped Matrix ComplexConjugate SchwartzMap ComplexOrder
open Matrix

namespace PositivityTheory.Rg.Sw.Glob.AwayPf

theorem diag_eq {m n : ℕ} (A : Matrix (Fin m) (Fin m) ℂ) (M : Matrix (Fin m) (Fin n) ℂ) (j : Fin n) :
    (Mᴴ * A * M) j j = star (fun a => M a j) ⬝ᵥ (A *ᵥ fun a => M a j) := by
  simp only [Matrix.mul_apply, dotProduct, mulVec, Matrix.conjTranspose_apply, Pi.star_apply, Finset.mul_sum,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
  ring

theorem tr_re_nonneg {m n : ℕ} {A : Matrix (Fin m) (Fin m) ℂ} (hA : A.PosDef) (M : Matrix (Fin m) (Fin n) ℂ) :
    0 ≤ (trace (Mᴴ * A * M)).re ∧ (M ≠ 0 → 0 < (trace (Mᴴ * A * M)).re) := by
  have hsum : (trace (Mᴴ * A * M)).re = ∑ j, (star (fun a => M a j) ⬝ᵥ (A *ᵥ fun a => M a j)).re := by
    rw [Matrix.trace, Complex.re_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Matrix.diag_apply, diag_eq]
  have hnn : ∀ j, 0 ≤ (star (fun a => M a j) ⬝ᵥ (A *ᵥ fun a => M a j)).re := by
    intro j
    by_cases hv : (fun a => M a j) = 0
    · rw [hv]
      simp
    · exact (hA.re_dotProduct_pos hv).le
  refine ⟨hsum ▸ Finset.sum_nonneg (fun j _ => hnn j), fun hM => ?_⟩
  obtain ⟨j, hj⟩ : ∃ j, (fun a => M a j) ≠ 0 := by
    by_contra hc
    push_neg at hc
    apply hM
    ext a j
    exact congrFun (hc j) a
  rw [hsum]
  exact Finset.sum_pos' (fun j _ => hnn j) ⟨j, Finset.mem_univ _, hA.re_dotProduct_pos hj⟩

theorem tr_re_symm {m n : ℕ} {A : Matrix (Fin m) (Fin m) ℂ} (hA : A.IsHermitian) (M N : Matrix (Fin m) (Fin n) ℂ) :
    (trace (Mᴴ * A * N)).re = (trace (Nᴴ * A * M)).re := by
  have h : (Mᴴ * A * N)ᴴ = Nᴴ * A * M := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hA.eq,
      Matrix.mul_assoc]
  rw [← h, Matrix.trace_conjTranspose]
  simp

theorem tr_im_zero {m n : ℕ} {A : Matrix (Fin m) (Fin m) ℂ} (hA : A.IsHermitian) (M : Matrix (Fin m) (Fin n) ℂ) :
    trace (Mᴴ * A * M) = ((trace (Mᴴ * A * M)).re : ℂ) := by
  have h : star (trace (Mᴴ * A * M)) = trace (Mᴴ * A * M) := by
    rw [← Matrix.trace_conjTranspose]
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hA.eq, Matrix.mul_assoc]
  have him : (trace (Mᴴ * A * M)).im = 0 := by
    have := congrArg Complex.im h
    simp at this
    linarith
  apply Complex.ext <;> simp [him]

section
variable {T : Type} [Fintype T] [DecidableEq T] {m n : ℕ} (τ : T)

def qf (A : T → Matrix (Fin m) (Fin m) ℂ) (w : T → ℝ) (b b' : Bsp τ m n) : ℝ :=
  ∑ t : {τ' : T // τ' ≠ τ}, w t.1 * (trace ((of (b t))ᴴ * A t.1 * of (b' t))).re

def Qf (A : T → Matrix (Fin m) (Fin m) ℂ) (w : T → ℝ) : LinearMap.BilinForm ℝ (Bsp τ m n) :=
  LinearMap.mk₂ ℝ (fun b b' => 2 * qf τ A w b b')
    (fun b₁ b₂ b' => by
      simp only [qf, ← mul_add, ← Finset.sum_add_distrib]
      congr 1
      refine Finset.sum_congr rfl (fun t _ => ?_)
      congr 1
      rw [← Complex.add_re, ← Matrix.trace_add, ← Matrix.add_mul, ← Matrix.add_mul, ← Matrix.conjTranspose_add]
      rfl)
    (fun r b b' => by
      simp only [qf, Finset.mul_sum, smul_eq_mul]
      refine Finset.sum_congr rfl (fun t _ => ?_)
      have : (of ((r • b) t))ᴴ = (r : ℂ) • (of (b t))ᴴ := by
        rw [show of ((r • b) t) = (r : ℂ) • of (b t) from by ext i j; simp [Complex.real_smul]]
        rw [Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal]
      rw [this, Matrix.smul_mul, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, Complex.re_ofReal_mul]
      ring)
    (fun b b₁ b₂ => by
      simp only [qf, ← mul_add, ← Finset.sum_add_distrib]
      congr 1
      refine Finset.sum_congr rfl (fun t _ => ?_)
      congr 1
      rw [← Complex.add_re, ← Matrix.trace_add, ← Matrix.mul_add]
      rfl)
    (fun r b b' => by
      simp only [qf, Finset.mul_sum, smul_eq_mul]
      refine Finset.sum_congr rfl (fun t _ => ?_)
      have : of ((r • b') t) = (r : ℂ) • of (b' t) := by ext i j; simp [Complex.real_smul]
      rw [this, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, Complex.re_ofReal_mul]
      ring)

theorem Qf_apply (A : T → Matrix (Fin m) (Fin m) ℂ) (w : T → ℝ) (b b' : Bsp τ m n) :
    Qf τ A w b b' = 2 * qf τ A w b b' := rfl

theorem Qf_symm (A : T → Matrix (Fin m) (Fin m) ℂ) (hA : ∀ t, t ≠ τ → (A t).IsHermitian) (w : T → ℝ)
    (b b' : Bsp τ m n) : Qf τ A w b b' = Qf τ A w b' b := by
  rw [Qf_apply, Qf_apply]
  congr 1
  unfold qf
  refine Finset.sum_congr rfl (fun t _ => ?_)
  rw [tr_re_symm (hA t.1 t.2)]

theorem Qf_pos (A : T → Matrix (Fin m) (Fin m) ℂ) (hA : ∀ t, t ≠ τ → (A t).PosDef) (w : T → ℝ)
    (hw : ∀ t, t ≠ τ → 0 < w t) (b : Bsp τ m n) (hb : b ≠ 0) : 0 < Qf τ A w b b := by
  rw [Qf_apply]
  have hnn : ∀ t : {τ' : T // τ' ≠ τ}, 0 ≤ w t.1 * (trace ((of (b t))ᴴ * A t.1 * of (b t))).re :=
    fun t => mul_nonneg (hw t.1 t.2).le (tr_re_nonneg (hA t.1 t.2) _).1
  obtain ⟨t, ht⟩ : ∃ t, b t ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hb (funext hc)
  have hof : of (b t) ≠ 0 := by
    intro h0
    apply ht
    funext i j
    exact congrFun (congrFun h0 i) j
  have hpos : 0 < qf τ A w b b :=
    Finset.sum_pos' (fun t _ => hnn t)
      ⟨t, Finset.mem_univ _, mul_pos (hw t.1 t.2) ((tr_re_nonneg (hA t.1 t.2) _).2 hof)⟩
  linarith

theorem exists_gauss (A : T → Matrix (Fin m) (Fin m) ℂ) (hA : ∀ t, t ≠ τ → (A t).PosDef) (w : T → ℝ)
    (hw : ∀ t, t ≠ τ → 0 < w t) :
    ∃ G : 𝓢(Bsp τ m n, ℂ), ∀ b, G b = Complex.exp (-(Real.pi : ℂ) * ((2 * qf τ A w b b : ℝ) : ℂ)) := by
  obtain ⟨G, hG⟩ := GlobalTheory.ThK.EvAt0.GaussForm.exists_schwartz_gauss_form (Qf τ A w)
    (Qf_symm τ A (fun t ht => (hA t ht).isHermitian) w) (fun b hb => Qf_pos τ A hA w hw b hb)
  refine ⟨G, fun b => ?_⟩
  rw [(hG b).1, Qf_apply]

end

end PositivityTheory.Rg.Sw.Glob.AwayPf
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.DBoundA
section
noncomputable section

open Matrix Topology Filter
open scoped ComplexOrder

namespace PositivityTheory.Rg.Sw.Glob

namespace DBoundAH

variable {n : ℕ}

def rowC {m : ℕ} (u : Fin m → Fin n → ℂ) (a : Fin m) : Fin n → ℂ := fun j => star (u a j)

theorem trace_gramB {m : ℕ} (Z : Matrix (Fin n) (Fin n) ℂ) (ε : Fin m → Bool) (b : Bool) (u : Fin m → Fin n → ℂ) :
    (Z * gramB ε b u).trace = ∑ a ∈ Finset.univ.filter (fun a => ε a = b),
      star (rowC u a) ⬝ᵥ (Z *ᵥ rowC u a) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, gramB, evX, Qb, map_sum, map_mul, MvPolynomial.eval_X,
    dotProduct, Matrix.mulVec, rowC, Pi.star_apply, star_star, Finset.mul_sum, Finset.sum_mul]
  simp only [Bool.true_eq_false, if_true, if_false]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun a _ => ?_))
  simp only [Bool.false_eq_true, if_false]
  ring

theorem star_dot_conjTranspose (Z : Matrix (Fin n) (Fin n) ℂ) (w : Fin n → ℂ) :
    star w ⬝ᵥ (Zᴴ *ᵥ w) = star (star w ⬝ᵥ (Z *ᵥ w)) := by
  simp only [dotProduct, mulVec, conjTranspose_apply, Pi.star_apply, star_sum, star_mul', star_star, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem im_eq_re (Z : Matrix (Fin n) (Fin n) ℂ) (w : Fin n → ℂ) :
    (star w ⬝ᵥ (Z *ᵥ w)).im = (star w ⬝ᵥ (((-(Complex.I / 2)) • (Z - Zᴴ)) *ᵥ w)).re := by
  rw [Matrix.smul_mulVec, Matrix.sub_mulVec, dotProduct_smul, dotProduct_sub, star_dot_conjTranspose]
  simp only [smul_eq_mul, Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.div_ofNat_re,
    Complex.div_ofNat_im, Complex.I_re, Complex.I_im, Complex.sub_re, Complex.sub_im, Complex.star_def,
    Complex.conj_re, Complex.conj_im]
  ring

private theorem norm_star_dotProduct_mulVec_le_sum_norm_mul (M : Matrix (Fin n) (Fin n) ℂ) (w : Fin n → ℂ) :
    ‖star w ⬝ᵥ (M *ᵥ w)‖ ≤ (∑ i, ∑ j, ‖M i j‖) * ∑ j, ‖w j‖ ^ 2 := by
  have hS : ∀ i j, ‖w i‖ * ‖w j‖ ≤ ∑ k, ‖w k‖ ^ 2 := by
    intro i j
    have hi : ‖w i‖ ^ 2 ≤ ∑ k, ‖w k‖ ^ 2 :=
      Finset.single_le_sum (f := fun k => ‖w k‖ ^ 2) (fun k _ => by positivity) (Finset.mem_univ i)
    have hj : ‖w j‖ ^ 2 ≤ ∑ k, ‖w k‖ ^ 2 :=
      Finset.single_le_sum (f := fun k => ‖w k‖ ^ 2) (fun k _ => by positivity) (Finset.mem_univ j)
    nlinarith [sq_nonneg (‖w i‖ - ‖w j‖), norm_nonneg (w i), norm_nonneg (w j)]
  calc ‖star w ⬝ᵥ (M *ᵥ w)‖ = ‖∑ i, ∑ j, star (w i) * (M i j * w j)‖ := by
        simp [dotProduct, Matrix.mulVec, Finset.mul_sum]
    _ ≤ ∑ i, ∑ j, ‖star (w i) * (M i j * w j)‖ :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => norm_sum_le _ _)
    _ = ∑ i, ∑ j, ‖M i j‖ * (‖w i‖ * ‖w j‖) :=
        Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
          rw [norm_mul, norm_mul, norm_star]
          ring
    _ ≤ ∑ i, ∑ j, ‖M i j‖ * ∑ k, ‖w k‖ ^ 2 :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
          mul_le_mul_of_nonneg_left (hS i j) (norm_nonneg _)
    _ = (∑ i, ∑ j, ‖M i j‖) * ∑ k, ‖w k‖ ^ 2 := by simp [Finset.sum_mul]

private theorem exists_pos_mul_sum_sq_le_re_of_posDef (H0 : Matrix (Fin n) (Fin n) ℂ) (h0 : H0.PosDef) :
    ∃ c > 0, ∀ w : Fin n → ℂ, c * ∑ j, ‖w j‖ ^ 2 ≤ (star w ⬝ᵥ (H0 *ᵥ w)).re := by
  classical
  have hA := h0.1
  have hspec : H0 = (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) *
      Matrix.diagonal (fun i => ((hA.eigenvalues i : ℝ) : ℂ)) * star (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) := by
    have := hA.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at this
    exact this
  obtain ⟨c, hc, hcle⟩ : ∃ c > 0, ∀ i, c ≤ hA.eigenvalues i := by
    rcases isEmpty_or_nonempty (Fin n) with hn | hn
    · exact ⟨1, one_pos, fun i => (IsEmpty.false i).elim⟩
    · obtain ⟨i0, _, hi0⟩ := Finset.exists_min_image Finset.univ hA.eigenvalues Finset.univ_nonempty
      exact ⟨hA.eigenvalues i0, h0.eigenvalues_pos i0, fun i => hi0 i (Finset.mem_univ i)⟩
  refine ⟨c, hc, fun w => ?_⟩
  have hsv : star w ᵥ* (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) =
      star (star (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) *ᵥ w) := by
    rw [Matrix.star_mulVec, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose]
  have h1 : star w ⬝ᵥ (H0 *ᵥ w) = ∑ i, ((hA.eigenvalues i : ℝ) : ℂ) *
      (star ((star (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) *ᵥ w) i) *
        ((star (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) *ᵥ w) i)) := by
    conv_lhs => rw [hspec]
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, hsv]
    simp only [dotProduct, Matrix.mulVec_diagonal, Pi.star_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have h2 : star (star (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) *ᵥ w) ⬝ᵥ
      (star (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) *ᵥ w) = star w ⬝ᵥ w := by
    rw [← hsv, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Unitary.mul_star_self_of_mem (hA.eigenvectorUnitary).2, Matrix.one_mulVec]
  have hre : ∀ z : ℂ, (star z * z).re = ‖z‖ ^ 2 := by
    intro z
    rw [Complex.star_def, Complex.conj_mul']
    norm_cast
  have h2' : ∑ i, ‖(star (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) *ᵥ w) i‖ ^ 2 = ∑ j, ‖w j‖ ^ 2 := by
    have := congrArg Complex.re h2
    simp only [dotProduct, Pi.star_apply, Complex.re_sum, hre] at this
    exact this
  rw [h1, Complex.re_sum, ← h2', Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [Complex.re_ofReal_mul, hre]
  exact mul_le_mul_of_nonneg_right (hcle i) (by positivity)

theorem posDef_unif {P : Type} [TopologicalSpace P] {p₀ : P} (H : P → Matrix (Fin n) (Fin n) ℂ)
    (hH : ∀ i j, ContinuousAt (fun p => H p i j) p₀) (h0 : (H p₀).PosDef) :
    ∃ δ > 0, ∀ᶠ p in 𝓝 p₀, ∀ w : Fin n → ℂ, δ * ∑ j, ‖w j‖ ^ 2 ≤ (star w ⬝ᵥ (H p *ᵥ w)).re := by
  obtain ⟨c, hc, hcoer⟩ := exists_pos_mul_sum_sq_le_re_of_posDef (H p₀) h0
  have hf : Tendsto (fun p => ∑ i, ∑ j, ‖H p i j - H p₀ i j‖) (𝓝 p₀) (𝓝 0) := by
    have h00 : (0 : ℝ) = ∑ i : Fin n, ∑ j : Fin n, ‖H p₀ i j - H p₀ i j‖ := by simp
    rw [h00]
    exact tendsto_finsetSum _ fun i _ => tendsto_finsetSum _ fun j _ =>
      ((hH i j).tendsto.sub tendsto_const_nhds).norm
  have hev := (tendsto_order.1 hf).2 (c / 2) (by positivity)
  refine ⟨c / 2, by positivity, hev.mono fun p hp w => ?_⟩
  have hb := norm_star_dotProduct_mulVec_le_sum_norm_mul (H p - H p₀) w
  have hsplit : (star w ⬝ᵥ (H p *ᵥ w)).re =
      (star w ⬝ᵥ (H p₀ *ᵥ w)).re + (star w ⬝ᵥ ((H p - H p₀) *ᵥ w)).re := by
    rw [Matrix.sub_mulVec, dotProduct_sub]
    simp
  have hlow : -‖star w ⬝ᵥ ((H p - H p₀) *ᵥ w)‖ ≤ (star w ⬝ᵥ ((H p - H p₀) *ᵥ w)).re :=
    (abs_le.mp (Complex.abs_re_le_norm _)).1
  have hS : 0 ≤ ∑ j, ‖w j‖ ^ 2 := Finset.sum_nonneg fun j _ => by positivity
  have hcw := hcoer w
  have hp' : ∑ i, ∑ j, ‖(H p - H p₀) i j‖ < c / 2 := by simpa [Matrix.sub_apply] using hp
  have hK := mul_le_mul_of_nonneg_right hp'.le hS
  linarith

end DBoundAH

end PositivityTheory.Rg.Sw.Glob
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.DCalcD
section
noncomputable section

open MeasureTheory Filter Topology MvPolynomial

namespace PositivityTheory.Rg.Sw.Glob

namespace DCalcDH

open DCalcH DCalcBH

variable {m n : ℕ}

def sqN (v : Fin m → Fin n → ℂ) : ℝ := ∑ a, ∑ j, ‖v a j‖ ^ 2

theorem sqN_nonneg (v : Fin m → Fin n → ℂ) : 0 ≤ sqN v := by
  unfold sqN; positivity

theorem norm_le_one_add_sq (v : Fin m → Fin n → ℂ) (a : Fin m) (j : Fin n) : ‖v a j‖ ≤ 1 + sqN v := by
  have h1 : ‖v a j‖ ^ 2 ≤ sqN v := by
    unfold sqN
    have ha : ‖v a j‖ ^ 2 ≤ ∑ j', ‖v a j'‖ ^ 2 :=
      Finset.single_le_sum (f := fun j' => ‖v a j'‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ j)
    exact ha.trans (Finset.single_le_sum (f := fun a' => ∑ j', ‖v a' j'‖ ^ 2) (fun _ _ => by positivity)
      (Finset.mem_univ a))
  nlinarith [norm_nonneg (v a j), sq_nonneg (‖v a j‖ - 1)]

theorem norm_crd (v : Fin m → Fin n → ℂ) (k : Fin m × Fin n × Bool) : ‖crd v k‖ = ‖v k.1 k.2.1‖ := by
  unfold crd; split_ifs <;> simp

theorem evX_growth (Q : PX m n) : ∃ C N, 0 ≤ C ∧ ∀ v, ‖evX Q v‖ ≤ C * (1 + sqN v) ^ N := by
  induction Q using MvPolynomial.induction_on with
  | C a => exact ⟨‖a‖, 0, norm_nonneg _, fun v => by simp [evX_eq]⟩
  | add p q hp hq =>
    obtain ⟨C1, N1, hC1, h1⟩ := hp
    obtain ⟨C2, N2, hC2, h2⟩ := hq
    refine ⟨C1 + C2, max N1 N2, by positivity, fun v => ?_⟩
    have hs : 1 ≤ 1 + sqN v := by linarith [sqN_nonneg v]
    have e1 := pow_le_pow_right₀ hs (le_max_left N1 N2)
    have e2 := pow_le_pow_right₀ hs (le_max_right N1 N2)
    calc ‖evX (p + q) v‖ ≤ ‖evX p v‖ + ‖evX q v‖ := by rw [evX_eq, map_add (f := _)]; exact norm_add_le _ _
      _ ≤ C1 * (1 + sqN v) ^ N1 + C2 * (1 + sqN v) ^ N2 := add_le_add (h1 v) (h2 v)
      _ ≤ C1 * (1 + sqN v) ^ max N1 N2 + C2 * (1 + sqN v) ^ max N1 N2 :=
          add_le_add (mul_le_mul_of_nonneg_left e1 hC1) (mul_le_mul_of_nonneg_left e2 hC2)
      _ = (C1 + C2) * (1 + sqN v) ^ max N1 N2 := by ring
  | mul_X p k hp =>
    obtain ⟨C, N, hC, h⟩ := hp
    refine ⟨C, N + 1, hC, fun v => ?_⟩
    have hk : ‖crd v k‖ ≤ 1 + sqN v := by rw [norm_crd]; exact norm_le_one_add_sq v _ _
    calc ‖evX (p * X k) v‖ = ‖evX p v‖ * ‖crd v k‖ := by rw [evX_eq, map_mul, eval_X, norm_mul]; rfl
      _ ≤ C * (1 + sqN v) ^ N * (1 + sqN v) :=
          mul_le_mul (h v) hk (norm_nonneg _) (mul_nonneg hC (pow_nonneg (by linarith [sqN_nonneg v]) _))
      _ = C * (1 + sqN v) ^ (N + 1) := by ring

theorem poly_exp (N : ℕ) (a : ℝ) (ha : 0 < a) :
    ∃ C, 0 ≤ C ∧ ∀ x : ℝ, 0 ≤ x → (1 + x) ^ N * Real.exp (-(a * x)) ≤ C * Real.exp (-(a / 2 * x)) :=
  _root_.UpperTheory.Reformulated.B.P6.r23b.PositivityTheory.Rg.Sw.Glob.DCalcDH.poly_exp N a ha

theorem integrable_gauss_C (a : ℝ) (ha : 0 < a) : Integrable (fun z : ℂ => Real.exp (-(a * ‖z‖ ^ 2))) := by
  have h := GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := ℂ) (b := (a : ℂ)) (by simpa using ha) 0 0
  refine h.norm.congr (Eventually.of_forall fun z => ?_)
  simp only [zero_mul, add_zero, Complex.norm_exp]
  congr 1
  simp [Complex.mul_re, ← Complex.ofReal_pow]

theorem integrable_gauss (a : ℝ) (ha : 0 < a) : Integrable (fun u : Fin m → Fin n → ℂ => Real.exp (-(a * sqN u))) := by
  have hinner : Integrable (fun w : Fin n → ℂ => ∏ j, Real.exp (-(a * ‖w j‖ ^ 2))) :=
    Integrable.fintype_prod (ι := Fin n) (E := ℂ) (μ := fun _ => (volume : Measure ℂ))
      (f := fun _ z => Real.exp (-(a * ‖z‖ ^ 2))) fun _ => integrable_gauss_C a ha
  have houter : Integrable (fun u : Fin m → Fin n → ℂ => ∏ i, ∏ j, Real.exp (-(a * ‖u i j‖ ^ 2))) :=
    Integrable.fintype_prod (ι := Fin m) (E := Fin n → ℂ) (μ := fun _ => (volume : Measure (Fin n → ℂ)))
      (f := fun _ w => ∏ j, Real.exp (-(a * ‖w j‖ ^ 2))) fun _ => hinner
  refine houter.congr (Eventually.of_forall fun u => ?_)
  simp only [sqN]
  rw [Finset.mul_sum, ← Finset.sum_neg_distrib, Real.exp_sum]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Finset.mul_sum, ← Finset.sum_neg_distrib, Real.exp_sum]

end DCalcDH

end PositivityTheory.Rg.Sw.Glob
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.GCSch
section
noncomputable section

open scoped Matrix ComplexOrder
open Matrix

namespace PositivityTheory.Rg.Sw.Glob

open GCSchH

theorem gCSch : GCSch := by
  intro m n ε t c hc htc Z Z' hZ hZ'
  set S := Finset.univ.filter (fun a => epsT t ε a = true) with hS
  set S' := Finset.univ.filter (fun a => epsT t ε a = false) with hS'
  set B := qB S S' c Z Z' with hB
  have hgC : gC ε t c Z Z' = fun u => Complex.exp (-(B u u)) := by
    funext u
    simp only [gC, hB, qB_apply, qF, neg_neg, trace_gramB]
    rfl
  have hP1 : ((-(Complex.I / 2)) • (Zᵀ - Zᵀᴴ)).PosDef := by
    have h := hZ.transpose
    rwa [Matrix.transpose_smul, Matrix.transpose_sub, Matrix.conjTranspose_transpose] at h
  have hP2 : ((-(Complex.I / 2)) • (-Z'ᵀ - (-Z'ᵀ)ᴴ)).PosDef := by
    have h := hZ'.transpose
    unfold IsSiegel at h
    rw [Matrix.conjTranspose_conjTranspose, Matrix.transpose_smul, Matrix.transpose_sub,
      Matrix.conjTranspose_transpose] at h
    rwa [Matrix.conjTranspose_neg, sub_neg_eq_add, neg_add_eq_sub]
  have hre : ∀ u : Fin m → Fin n → ℂ, (B u u).re = c * (∑ a ∈ S, (star (u a) ⬝ᵥ
      (((-(Complex.I / 2)) • (Zᵀ - Zᵀᴴ)) *ᵥ u a)).re + ∑ a ∈ S', (star (u a) ⬝ᵥ
      (((-(Complex.I / 2)) • (-Z'ᵀ - (-Z'ᵀ)ᴴ)) *ᵥ u a)).re) := by
    intro u
    rw [hB, qB_apply, qF, Complex.neg_re, Complex.sub_re, re_I_mul, re_I_mul, Complex.im_sum, Complex.im_sum]
    have e2 : ∀ a, (star (u a) ⬝ᵥ (Z'ᵀ *ᵥ u a)).im = -(star (u a) ⬝ᵥ ((-Z'ᵀ) *ᵥ u a)).im := by
      intro a; rw [Matrix.neg_mulVec, dotProduct_neg, Complex.neg_im, neg_neg]
    simp only [e2, Finset.sum_neg_distrib, im_quad]
    ring
  have hpos : ∀ u : Fin m → Fin n → ℂ, u ≠ 0 → 0 < (B u u).re := by
    intro u hu
    obtain ⟨a, ha⟩ := Function.ne_iff.1 hu
    rw [hre]
    apply mul_pos hc
    have n1 : 0 ≤ ∑ a ∈ S, (star (u a) ⬝ᵥ (((-(Complex.I / 2)) • (Zᵀ - Zᵀᴴ)) *ᵥ u a)).re :=
      Finset.sum_nonneg fun a _ => quad_nonneg hP1 _
    have n2 : 0 ≤ ∑ a ∈ S', (star (u a) ⬝ᵥ (((-(Complex.I / 2)) • (-Z'ᵀ - (-Z'ᵀ)ᴴ)) *ᵥ u a)).re :=
      Finset.sum_nonneg fun a _ => quad_nonneg hP2 _
    cases hb : epsT t ε a
    · have haS : a ∈ S' := by simp [hS', hb]
      have p2 := Finset.sum_pos' (fun a _ => quad_nonneg hP2 (u a)) ⟨a, haS, quad_pos hP2 ha⟩
      linarith
    · have haS : a ∈ S := by simp [hS, hb]
      have p1 := Finset.sum_pos' (fun a _ => quad_nonneg hP1 (u a)) ⟨a, haS, quad_pos hP1 ha⟩
      linarith
  obtain ⟨κ, hκ, hco⟩ := coercive_of_pos B hpos
  obtain ⟨g, hg, -⟩ := GlobalTheory.GaussComplexForm.exists_schwartz_cexp_neg_form _ B κ hκ hco
  refine ⟨g, ?_⟩
  rw [hgC]
  funext u
  exact hg u

theorem gZSch : GZSch := by
  intro m n ε t c hc htc Z hZ
  show IsSch (gC ε t c Z Zᴴ)
  exact gCSch m n ε t c hc htc Z Zᴴ hZ (by rw [Matrix.conjTranspose_conjTranspose]; exact hZ)

end PositivityTheory.Rg.Sw.Glob
end
end

