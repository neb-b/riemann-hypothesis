module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0018
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.M3bNormHolds
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0014
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0017
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.ContinuousRl
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0008
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0019

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FlowCoefficientBounds
section
namespace ReciprocityTheory.ChartRestriction.G.FD.FlowCoefficientBounds

open NumberField Complex MeasureTheory ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

theorem dmin_ne {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) (i : Fin (r + 1)) :
    dmin X.Gm x τ i ≠ 0 := by
  intro h
  have h1 := (hx τ).2 i
  rw [h] at h1
  simp at h1

theorem nfac_pos {x : Frame X.Ψ r} (hx : x ∈ X.dom) (la : Wt X.Ψ r) : 0 < X.nfac la x := by
  unfold Data.nfac
  refine Finset.prod_pos fun τ _ => Finset.prod_pos fun i _ => ?_
  apply Real.rpow_pos_of_pos
  rw [norm_pos_iff]
  exact div_ne_zero (dmin_ne X hx τ _) (dmin_ne X hx τ _)

theorem norm_cexp_I (z : ℂ) (hz : z.im = 0) : ‖cexp (-(4 * (Real.pi : ℂ) * I) * z)‖ = 1 := by
  rw [Complex.norm_exp, Real.exp_eq_one_iff]
  simp [Complex.mul_re, Complex.mul_im, hz]

private lemma sum_sum_sub_isotropic_shift_eq_of_conj_eq_neg {r : ℕ} (g : Fin r → Fin r → ℂ) (hg : ∀ a b, conj (g a b) = g b a)
    (z v w : Fin r → ℂ) (α : ℂ) (hα : conj α = -α)
    (hz : ∑ a, ∑ b, z a * g a b * conj (z b) = 0) :
    ∑ a, ∑ b, (v a - α * (∑ p, ∑ q, v p * g p q * conj (z q)) * z a) * g a b *
        conj (w b - α * (∑ p, ∑ q, w p * g p q * conj (z q)) * z b) =
      ∑ a, ∑ b, v a * g a b * conj (w b) := by
  set A := ∑ p, ∑ q, v p * g p q * conj (z q) with hA
  set B := ∑ p, ∑ q, w p * g p q * conj (z q) with hB
  have hB' : conj B = ∑ a, ∑ b, z a * g a b * conj (w b) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hB, map_sum]
    set_option synthInstance.maxHeartbeats 100000 in
      simp_rw [map_sum, map_mul, Complex.conj_conj, hg]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
  have expand : ∀ a b, (v a - α * A * z a) * g a b * conj (w b - α * B * z b) =
      v a * g a b * conj (w b) + α * (conj B * (v a * g a b * conj (z b))) -
        α * A * (z a * g a b * conj (w b)) - α * α * A * conj B * (z a * g a b * conj (z b)) := by
    intro a b
    simp only [map_sub, map_mul, hα]
    ring
  simp_rw [expand, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [← hA, ← hB', hz]
  ring

theorem flow_real {ξ : Fin r → E} (hξ : X.IsIso ξ) {x : Frame X.Ψ r} (hx : x ∈ X.dom)
    (s : X.Ψ → ℝ) (la : Wt X.Ψ r) :
    X.flow ξ (fun τ => (s τ : ℂ)) x ∈ X.dom ∧
      X.nfac la (X.flow ξ (fun τ => (s τ : ℂ)) x) = X.nfac la x := by
  have hflow : ∀ τ : X.Ψ, gram τ.1 X.Gm (mat (X.flow ξ (fun τ => (s τ : ℂ)) x) τ) =
      gram τ.1 X.Gm (mat x τ) ∧ (X.flowMat ξ τ (s τ)).det = 1 := by
    intro τ
    have hg : ∀ p q, conj (τ.1 (X.Gm p q)) = τ.1 (X.Gm q p) := fun p q => by
      rw [← X.Gm_herm p q, cc, IsCMField.complexEmbedding_complexConj]
    have hz : ∑ a, ∑ b, τ.1 (ξ a) * τ.1 (X.Gm a b) * conj (τ.1 (ξ b)) = 0 := by
      have h0 := congrArg τ.1 hξ.2.1
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [herm, map_sum, map_mul, map_zero, cc, IsCMField.complexEmbedding_complexConj] at h0
      exact h0
    have hα : conj (I * (X.c τ : ℂ) * (s τ : ℂ)) = -(I * (X.c τ : ℂ) * (s τ : ℂ)) := by
      rw [map_mul, map_mul, Complex.conj_I, Complex.conj_ofReal, Complex.conj_ofReal]
      ring
    constructor
    · ext a b
      show hermC τ.1 X.Gm (col (X.flowMat ξ τ (s τ) * mat x τ) a) (col (X.flowMat ξ τ (s τ) * mat x τ) b) =
        hermC τ.1 X.Gm (col (mat x τ) a) (col (mat x τ) b)
      have hcol : ∀ c : Fin r, col (X.flowMat ξ τ (s τ) * mat x τ) c = fun p => col (mat x τ) c p -
          (I * (X.c τ : ℂ) * (s τ : ℂ)) * (∑ p', ∑ q, col (mat x τ) c p' * τ.1 (X.Gm p' q) * conj (τ.1 (ξ q))) * τ.1 (ξ p) := by
        intro c
        funext p
        simp only [col, Data.flowMat, Matrix.mul_apply, Matrix.of_apply, sub_mul, Finset.sum_sub_distrib,
          ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, reduceIte]
        congr 1
        simp only [Finset.mul_sum, Finset.sum_mul]
        exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => by ring
      unfold hermC
      rw [hcol a, hcol b]
      exact sum_sum_sub_isotropic_shift_eq_of_conj_eq_neg (fun p q => τ.1 (X.Gm p q)) hg (fun q => τ.1 (ξ q)) (col (mat x τ) a)
        (col (mat x τ) b) (I * (X.c τ : ℂ) * (s τ : ℂ)) hα hz
    · have hT : X.flowMat ξ τ (s τ) = 1 + Matrix.replicateCol (Fin 1) (fun a => -((I * (X.c τ : ℂ) * (s τ : ℂ)) * τ.1 (ξ a))) *
          Matrix.replicateRow (Fin 1) (fun b => ∑ k, τ.1 (X.Gm b k) * conj (τ.1 (ξ k))) := by
        ext a b
        simp [Data.flowMat, Matrix.mul_apply, Matrix.one_apply] <;> ring
      have h5 : ∑ b, (∑ k, τ.1 (X.Gm b k) * conj (τ.1 (ξ k))) * -((I * (X.c τ : ℂ) * (s τ : ℂ)) * τ.1 (ξ b)) = 0 := by
        have h6 : ∑ b, (∑ k, τ.1 (X.Gm b k) * conj (τ.1 (ξ k))) * -((I * (X.c τ : ℂ) * (s τ : ℂ)) * τ.1 (ξ b)) =
            -(I * (X.c τ : ℂ) * (s τ : ℂ)) * ∑ b, ∑ k, τ.1 (ξ b) * τ.1 (X.Gm b k) * conj (τ.1 (ξ k)) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun b _ => ?_
          rw [Finset.sum_mul, Finset.mul_sum]
          exact Finset.sum_congr rfl fun k _ => by ring
        rw [h6, hz, mul_zero]
      rw [hT]
      refine (Matrix.det_one_add_replicateCol_mul_replicateRow _ _).trans ?_
      simp only [dotProduct]
      rw [h5, add_zero]
  have hdmin : ∀ τ i, dmin X.Gm (X.flow ξ (fun τ => (s τ : ℂ)) x) τ i = dmin X.Gm x τ i := by
    intro τ i
    unfold dmin
    rw [(hflow τ).1]
  refine ⟨?_, ?_⟩
  · show ∀ τ : X.Ψ, (mat (X.flow ξ (fun τ => (s τ : ℂ)) x) τ).det ≠ 0 ∧
      ∀ i : Fin (r + 1), 0 < psgn X.p0 i * (dmin X.Gm (X.flow ξ (fun τ => (s τ : ℂ)) x) τ i).re
    intro τ
    refine ⟨?_, fun i => ?_⟩
    · show (X.flowMat ξ τ (s τ) * mat x τ).det ≠ 0
      rw [Matrix.det_mul, (hflow τ).2, one_mul]
      exact (hx τ).1
    · rw [hdmin]
      exact (hx τ).2 i
  · unfold Data.nfac
    simp only [hdmin]

theorem fj_bound (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (C : ℝ)
    (hP : ∀ y ∈ X.dom, X.pnorm la P y ≤ C) {ξ : Fin r → E} (hξ : X.IsIso ξ) (ν : X.Ψ → ℝ)
    {x : Frame X.Ψ r} (hx : x ∈ X.dom) : X.pnorm la (X.fj la ξ ν P) x ≤ C := by
  have hpos := nfac_pos X hx la
  change ‖X.fj la ξ ν P x‖ * X.nfac la x ≤ C
  have hC : 0 ≤ C := le_trans (by unfold Data.pnorm; positivity) (hP x hx)
  unfold Data.fj
  split_ifs with h1 h2
  · obtain ⟨-, -, hD0, hDt⟩ := h2.choose_spec
    rw [← le_div_iff₀ hpos, norm_mul]
    have hpt : ∀ s : X.Ψ → ℝ, ‖P (X.flow ξ (fun τ => (s τ : ℂ)) x) *
        cexp (-(4 * Real.pi * I) * ∑ τ, (ν τ : ℂ) * s τ)‖ ≤ C / X.nfac la x := by
      intro s
      obtain ⟨hd, hn⟩ := flow_real X hξ hx s la
      rw [norm_mul, norm_cexp_I _ (by rw [Complex.im_sum]; simp), mul_one, le_div_iff₀ hpos, ← hn]
      exact hP _ hd
    haveI : IsFiniteMeasure (volume.restrict h2.choose) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact hDt⟩
    have hI := norm_integral_le_of_norm_le_const (μ := volume.restrict h2.choose) (ae_of_all _ hpt)
    rw [measureReal_def, Measure.restrict_apply_univ] at hI
    have hv : 0 < (volume h2.choose).toReal := ENNReal.toReal_pos hD0.ne' hDt.ne
    simp only [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hv]
    refine (mul_le_mul_of_nonneg_left hI (inv_nonneg.2 hv.le)).trans (le_of_eq ?_)
    rw [mul_comm (C / X.nfac la x) _, ← mul_assoc, inv_mul_cancel₀ hv.ne', one_mul]
  · simp [hC]
  · simp [hC]

theorem herm_of_LZ {g : ℕ} {b : X.Ψ → Fin 2 → Fin 2 → ℂ} (hb : b ∈ X.LZ g) : IsHermFam b := by
  obtain ⟨β, hβ, -, he⟩ := hb
  intro τ i k
  rw [he]
  simp only [Data.embH]
  rw [← hβ i k, cc, IsCMField.complexEmbedding_complexConj]

theorem herm_sum {n : ℕ} (ω : Fin n → X.Ψ → Fin 2 → Fin 2 → ℂ) (hω : ∀ j, IsHermFam (ω j))
    (t : Fin n → ℝ) : IsHermFam (∑ j, (t j : ℂ) • ω j) := by
  intro τ i k
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul, Complex.conj_ofReal]
  exact Finset.sum_congr rfl fun j _ => by rw [hω j τ i k]

theorem fz_bound (u : Fin 2 → Fin r → E) (g : ℕ) (χ : X.Ψ → Fin 2 → Fin 2 → ℂ)
    (G : Frame X.Ψ r → ℂ) (la : Wt X.Ψ r) {y : Frame X.Ψ r} (hy : y ∈ X.dom) (M : ℝ) (hM : 0 ≤ M)
    (hb : ∀ b, IsHermFam b → ‖G (X.Zb u b y)‖ * X.nfac la y ≤ M) :
    X.pnorm la (X.fz u g χ G) y ≤ M := by
  have hpos := nfac_pos X hy la
  change ‖X.fz u g χ G y‖ * X.nfac la y ≤ M
  unfold Data.fz
  split_ifs with h1 h2
  · rw [← le_div_iff₀ hpos]
    have hpt : ∀ t : Fin (4 * Fintype.card X.Ψ) → ℝ, ‖G (X.Zb u (∑ j, (t j : ℂ) • h2.choose j) y) *
        cexp (-(4 * Real.pi * I) * X.pairR χ (∑ j, (t j : ℂ) • h2.choose j))‖ ≤ M / X.nfac la y := by
      intro t
      have hherm : IsHermFam (∑ j, (t j : ℂ) • h2.choose j) :=
        herm_sum X _ (fun j => herm_of_LZ X (h2.choose_spec.1 j)) t
      rw [norm_mul, norm_cexp_I _ (Complex.ofReal_im _), mul_one, le_div_iff₀ hpos]
      exact hb _ hherm
    have hvol : volume (Set.pi Set.univ fun _ : Fin (4 * Fintype.card X.Ψ) => Set.Icc (0 : ℝ) 1) = 1 := by
      rw [volume_pi_pi]
      simp [Real.volume_Icc]
    haveI : IsFiniteMeasure (volume.restrict
        (Set.pi Set.univ fun _ : Fin (4 * Fintype.card X.Ψ) => Set.Icc (0 : ℝ) 1)) :=
      ⟨by rw [Measure.restrict_apply_univ, hvol]; exact ENNReal.one_lt_top⟩
    refine (norm_integral_le_of_norm_le_const (ae_of_all _ hpt)).trans ?_
    rw [measureReal_def, Measure.restrict_apply_univ, hvol]
    simp
  · simp [hM]
  · simp [hM]

end ReciprocityTheory.ChartRestriction.G.FD.FlowCoefficientBounds
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FourierCubeVolume
section
namespace ReciprocityTheory.ChartRestriction.G.FD.FourierCubeVolume

open NumberField Complex ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.FourierCoefficientMatrices MeasureTheory Set Filter
open scoped ComplexConjugate

noncomputable section

section Gen

variable {ι : Type} [Fintype ι] {N : ℕ} (ω : Fin N → ι → Fin 2 → Fin 2 → ℂ)

def Bv (t : Fin N → ℝ) : ι → Fin 2 → Fin 2 → ℂ := ∑ j, (t j : ℂ) • ω j

lemma Bv_add (t s : Fin N → ℝ) : Bv ω (t + s) = Bv ω t + Bv ω s := by
  simp only [Bv, Pi.add_apply, Complex.ofReal_add, add_smul, Finset.sum_add_distrib]

lemma Bv_zero : Bv ω 0 = 0 := by
  simp [Bv]

lemma Bv_herm (hωh : ∀ j, IsHermFam (ω j)) (t : Fin N → ℝ) : IsHermFam (Bv ω t) := by
  intro τ i k
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Bv, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul, Complex.conj_ofReal]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [hωh j τ i k]

lemma Bv_cont : Continuous (Bv ω) := continuous_finsetSum _ (fun j _ => (Complex.continuous_ofReal.comp (continuous_apply j)).smul continuous_const)

lemma pair_Bv (χ : ι → Fin 2 → Fin 2 → ℂ) (t : Fin N → ℝ) :
    pr χ (Bv ω t) = ∑ j, t j * pr χ (ω j) := by
  have hadd : ∀ b b' : ι → Fin 2 → Fin 2 → ℂ, pr χ (b + b') = pr χ b + pr χ b' := by
    intro b b'
    simp only [pr, Pi.add_apply, mul_add, Finset.sum_add_distrib, Complex.add_re]
  have hsm : ∀ (c : ℝ) (b : ι → Fin 2 → Fin 2 → ℂ), pr χ ((c : ℂ) • b) = c * pr χ b := by
    intro c b
    simp only [pr, Pi.smul_apply, smul_eq_mul]
    rw [← Complex.re_ofReal_mul]
    congr 1
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun τ _ => Finset.sum_congr rfl (fun i _ =>
      Finset.sum_congr rfl (fun k _ => by ring)))
  let P : (ι → Fin 2 → Fin 2 → ℂ) →+ ℝ := AddMonoidHom.mk' (pr χ) hadd
  have h1 : pr χ (Bv ω t) = P (Bv ω t) := rfl
  set_option synthInstance.maxHeartbeats 100000 in
    rw [h1, Bv, map_sum]
  exact Finset.sum_congr rfl (fun j _ => hsm _ _)

def ech (χ : ι → Fin 2 → Fin 2 → ℂ) (t : Fin N → ℝ) : ℂ :=
  cexp (-(4 * Real.pi * I) * (pr χ (Bv ω t) : ℂ))

lemma ech_cont (χ : ι → Fin 2 → Fin 2 → ℂ) : Continuous (ech ω χ) := by
  have h : ech ω χ = fun t => cexp (-(4 * Real.pi * I) * ((∑ j, t j * pr χ (ω j) : ℝ) : ℂ)) := by
    funext t
    simp only [ech, pair_Bv]
  rw [h]
  fun_prop

lemma ech_add (χ : ι → Fin 2 → Fin 2 → ℂ) (t s : Fin N → ℝ) :
    ech ω χ (t + s) = ech ω χ t * ech ω χ s := by
  simp only [ech, pair_Bv, Pi.add_apply, add_mul, Finset.sum_add_distrib, Complex.ofReal_add, mul_add,
    Complex.exp_add]

lemma ech_int (χ : ι → Fin 2 → Fin 2 → ℂ) {k : Fin N → ℤ} (hk : ∀ j, 2 * pr χ (ω j) = k j)
    (n : Fin N → ℤ) : ech ω χ (fun i => (n i : ℝ)) = 1 := by
  have hk' : ∀ j, pr χ (ω j) = (k j : ℝ) / 2 := fun j => by linarith [hk j]
  rw [ech, pair_Bv, Complex.exp_eq_one_iff]
  refine ⟨-∑ j, n j * k j, ?_⟩
  simp only [hk']
  push_cast
  rw [Finset.mul_sum, neg_mul (∑ x, ((n x : ℂ) * (k x : ℂ))), Finset.sum_mul, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  ring

end Gen

def cube (N : ℕ) : Set (Fin N → ℝ) := Set.pi Set.univ fun _ => Set.Icc (0 : ℝ) 1

lemma cube_compact (N : ℕ) : IsCompact (cube N) := isCompact_univ_pi (fun _ => isCompact_Icc)

lemma cube_meas (N : ℕ) : MeasurableSet (cube N) := MeasurableSet.univ_pi (fun _ => measurableSet_Icc)

lemma ubox_ae (N : ℕ) : (I2.DimB.ubox N) =ᵐ[volume] cube N := by
  have h1 : I2.DimB.ubox N = Set.pi Set.univ (fun i => Ioc ((0 : Fin N → ℝ) i) ((1 : Fin N → ℝ) i)) := by
    ext x
    simp [I2.DimB.ubox]
  have h2 : cube N = Set.Icc (0 : Fin N → ℝ) 1 := by
    rw [cube, ← Set.pi_univ_Icc]
    rfl
  rw [h1, h2]
  exact Measure.univ_pi_Ioc_ae_eq_Icc

section Mean

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
  (u : Fin 2 → Fin r → E) (g : ℕ) (ω : Fin (4 * Fintype.card X.Ψ) → X.Ψ → Fin 2 → Fin 2 → ℂ)
  (G : Frame X.Ψ r → ℂ)

def Ich (χ : X.Ψ → Fin 2 → Fin 2 → ℂ) (x : Frame X.Ψ r) : ℂ :=
  ∫ t in cube (4 * Fintype.card X.Ψ), G (X.Zb u (Bv ω t) x) * ech ω χ t

variable {X u g ω G}
variable (hω : X.IsLZBasis g ω)
  (hadd : ∀ b b' x, X.Zb u b (X.Zb u b' x) = X.Zb u (b + b') x)
  (hdomH : ∀ b, IsHermFam b → ∀ x ∈ X.dom, X.Zb u b x ∈ X.dom)

include hω in
lemma herm_ω (j : Fin (4 * Fintype.card X.Ψ)) : IsHermFam (ω j) := ReciprocityTheory.ChartRestriction.G.FD.FourierCoefficientLattice.herm_of_LZ X g (hω.1 j)

include hω in
lemma Bv_LZ (n : Fin (4 * Fintype.card X.Ψ) → ℤ) : Bv ω (fun i => (n i : ℝ)) ∈ X.LZ g := by
  exact ReciprocityTheory.ChartRestriction.G.FD.FourierCoefficientLattice.LZ_sum X g hω.1 n

include hω hdomH in
lemma Zb_dom (t : Fin (4 * Fintype.card X.Ψ) → ℝ) {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    X.Zb u (Bv ω t) x ∈ X.dom := hdomH _ (Bv_herm ω (fun j => herm_ω hω j) t) x hx

include hω hdomH in
lemma psi_cont (hG : DifferentiableOn ℂ G X.dom) {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    Continuous fun t => G (X.Zb u (Bv ω t) x) := by
  have hB : Continuous (Bv ω) := Bv_cont ω
  have hc : Continuous fun t => X.Zb u (Bv ω t) x := by
    unfold Data.Zb Data.zmat
    fun_prop
  exact hG.continuousOn.comp_continuous hc (fun t => Zb_dom hω hdomH t hx)

include hω hadd hdomH in
lemma psi_per (hper : ∀ b ∈ X.LZ g, ∀ x ∈ X.dom, G (X.Zb u b x) = G x) {x : Frame X.Ψ r}
    (hx : x ∈ X.dom) (n : Fin (4 * Fintype.card X.Ψ) → ℤ) (t : Fin (4 * Fintype.card X.Ψ) → ℝ) :
    G (X.Zb u (Bv ω (t + fun i => (n i : ℝ))) x) = G (X.Zb u (Bv ω t) x) := by
  have hx' := Zb_dom hω hdomH t hx
  rw [Bv_add, add_comm, ← hadd]
  exact hper _ (Bv_LZ hω n) _ hx'

include hω hdomH in
lemma Ich_diff (hG : DifferentiableOn ℂ G X.dom) (χ : X.Ψ → Fin 2 → Fin 2 → ℂ) :
    DifferentiableOn ℂ (Ich X u ω G χ) X.dom := by
  have := FourierCoefficientDomain.diffOn_param (cube_compact _) (cube_meas _)
    (fun t => FourierCoefficientDomain.ZbL X u (Bv ω t)) (FourierCoefficientDomain.cont_ZbL X u (Bv_cont ω))
    (FourierCoefficientDomain.isOpen_dom X) (fun t _ x hx => Zb_dom hω hdomH t hx) G hG (ech ω χ) (ech_cont ω χ)
  exact this

lemma Ich_rmul (la : Wt X.Ψ r) (hB : ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, G (rmul x b) = bchar la b * G x)
    (hω : X.IsLZBasis g ω) (hdomH : ∀ b, IsHermFam b → ∀ x ∈ X.dom, X.Zb u b x ∈ X.dom)
    (χ : X.Ψ → Fin 2 → Fin 2 → ℂ) {x : Frame X.Ψ r} (hx : x ∈ X.dom) {b : Frame X.Ψ r}
    (hb : b ∈ Bor X.Ψ r) : Ich X u ω G χ (rmul x b) = bchar la b * Ich X u ω G χ x := by
  have hcomm : ∀ t, X.Zb u (Bv ω t) (rmul x b) = rmul (X.Zb u (Bv ω t) x) b := by
    intro t
    funext τ
    show X.zmat u (Bv ω t) τ * mat (rmul x b) τ = mat (X.Zb u (Bv ω t) x) τ * mat b τ
    change X.zmat u (Bv ω t) τ * (mat x τ * mat b τ) = _
    rw [mat_Zb, Matrix.mul_assoc]
  unfold Ich
  simp_rw [hcomm]
  have h2 : ∀ t, G (rmul (X.Zb u (Bv ω t) x) b) * ech ω χ t = bchar la b * (G (X.Zb u (Bv ω t) x) * ech ω χ t) := by
    intro t
    rw [hB _ (Zb_dom hω hdomH t hx) b hb, mul_assoc]
  simp_rw [h2]
  exact integral_const_mul _ _

end Mean

end

end ReciprocityTheory.ChartRestriction.G.FD.FourierCubeVolume
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.PosCoordNe
section
namespace ReciprocityTheory.ChartRestriction.G.FD.OrthonormalPerpBasis

open NumberField Complex Matrix
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]

variable {r : ℕ} (X : Data E r)

theorem ortho_h {x : Frame X.Ψ r} (ho : X.IsOrtho x) (τ : X.Ψ) (a b : Fin r) :
    hermC τ.1 X.Gm (col (mat x τ) a) (col (mat x τ) b) =
      if a = b then ((sgn X.p0 (a : ℕ) : ℝ) : ℂ) else 0 := by
  have h := congrFun (congrFun (ho τ) a) b
  rw [Matrix.diagonal_apply] at h
  exact h

theorem span_cols {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) (w : Fin r → ℂ) :
    ∃ c : Fin r → ℂ, w = ∑ a, c a • col (mat x τ) a := by
  have hdet : IsUnit (mat x τ).det := isUnit_iff_ne_zero.mpr (hx τ).1
  refine ⟨(mat x τ)⁻¹ *ᵥ w, ?_⟩
  have hBB : mat x τ *ᵥ ((mat x τ)⁻¹ *ᵥ w) = w := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]
  calc w = mat x τ *ᵥ ((mat x τ)⁻¹ *ᵥ w) := hBB.symm
    _ = _ := by
      funext k
      simp only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, col]
      exact Finset.sum_congr rfl fun j _ => mul_comm _ _

theorem sgn_mul_self (a : ℕ) : ((sgn X.p0 a : ℝ) : ℂ) * ((sgn X.p0 a : ℝ) : ℂ) = 1 := by
  unfold sgn
  split_ifs <;> simp

private theorem hermC_sum_smul_left' {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (c : Fin r → ℂ)
    (w : Fin r → Fin r → ℂ) (u : Fin r → ℂ) :
    hermC τ G (∑ i, c i • w i) u = ∑ i, c i * hermC τ G (w i) u := by
  unfold hermC
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun b _ => by ring

theorem expand {x : Frame X.Ψ r} (hx : x ∈ X.dom) (ho : X.IsOrtho x) (τ : X.Ψ) (v : Fin r → ℂ) :
    v = ∑ a : Fin r, (((sgn X.p0 (a : ℕ) : ℝ) : ℂ) * hermC τ.1 X.Gm v (col (mat x τ) a)) • col (mat x τ) a := by
  obtain ⟨c, hc⟩ := span_cols X hx τ v
  have hcoef : ∀ a, hermC τ.1 X.Gm v (col (mat x τ) a) = c a * ((sgn X.p0 (a : ℕ) : ℝ) : ℂ) := by
    intro a
    conv_lhs => rw [hc]
    rw [hermC_sum_smul_left']
    simp only [ortho_h X ho τ, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  conv_lhs => rw [hc]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [hcoef, ← mul_assoc, mul_comm _ (c a), mul_assoc, sgn_mul_self, mul_one]

theorem ppos_ortho {x : Frame X.Ψ r} (hx : x ∈ X.dom) (ho : X.IsOrtho x) (τ : X.Ψ) (v : Fin r → ℂ) :
    X.ppos x τ v = ∑ a : Fin X.p0, hermC τ.1 X.Gm v (col (mat x τ) (Fin.castLE X.p0_le a)) •
      col (mat x τ) (Fin.castLE X.p0_le a) := by
  have hg : X.gramPos x τ = 1 := by
    ext a b
    simp only [Data.gramPos, Matrix.submatrix_apply, ho τ, Matrix.diagonal_apply, Fin.castLE_inj,
      Matrix.one_apply]
    split_ifs with h
    · simp [sgn, Fin.coe_castLE, a.isLt]
    · rfl
  unfold Data.ppos
  rw [hg, Matrix.inv_eq_left_inv (mul_one (1 : Matrix (Fin X.p0) (Fin X.p0) ℂ))]
  refine Finset.sum_congr rfl fun a _ => ?_
  congr 1
  simp [Matrix.one_apply]

end ReciprocityTheory.ChartRestriction.G.FD.OrthonormalPerpBasis
end

