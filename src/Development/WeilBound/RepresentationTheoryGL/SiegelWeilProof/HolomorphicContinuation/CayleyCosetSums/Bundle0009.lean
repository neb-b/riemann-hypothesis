module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.DetSecondCayleyBlockNe
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.Bundle0003
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.Bundle0006
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.CayleyInverseConjTransposeMulApply
public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.Bundle0007

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.InverseSecondBlockEqNegConjTranspose
section
noncomputable section

open Matrix

namespace PositivityTheory.Rg.Sw.HSt.CompactCayleyBlocks

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.HSt PositivityTheory.Rg.Sw.HSt.LoweringDerivative PositivityTheory.Rg.Sw.AbsSt

variable {n : ℕ}

private theorem mul_toBlocks₂₁_eq (g h : M2 n) :
    (g * h).toBlocks₂₁ = g.toBlocks₂₁ * h.toBlocks₁₁ + g.toBlocks₂₂ * h.toBlocks₂₁ := by
  ext i j
  simp [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.toBlocks₂₁, Matrix.toBlocks₁₁, Matrix.toBlocks₂₂]

private theorem mul_toBlocks₂₂_eq (g h : M2 n) :
    (g * h).toBlocks₂₂ = g.toBlocks₂₁ * h.toBlocks₁₂ + g.toBlocks₂₂ * h.toBlocks₂₂ := by
  ext i j
  simp [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.toBlocks₂₁, Matrix.toBlocks₁₂, Matrix.toBlocks₂₂]

private theorem mul_toBlocks₁₁' (g h : M2 n) :
    (g * h).toBlocks₁₁ = g.toBlocks₁₁ * h.toBlocks₁₁ + g.toBlocks₁₂ * h.toBlocks₂₁ := by
  ext i j
  simp [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.toBlocks₂₁, Matrix.toBlocks₁₁, Matrix.toBlocks₁₂]

private theorem mul_toBlocks₁₂ (g h : M2 n) :
    (g * h).toBlocks₁₂ = g.toBlocks₁₁ * h.toBlocks₁₂ + g.toBlocks₁₂ * h.toBlocks₂₂ := by
  ext i j
  simp [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.toBlocks₁₂, Matrix.toBlocks₁₁, Matrix.toBlocks₂₂]

private theorem conjTranspose_toBlocks (g : M2 n) :
    (gᴴ).toBlocks₁₁ = (g.toBlocks₁₁)ᴴ ∧ (gᴴ).toBlocks₁₂ = (g.toBlocks₂₁)ᴴ ∧
      (gᴴ).toBlocks₂₁ = (g.toBlocks₁₂)ᴴ ∧ (gᴴ).toBlocks₂₂ = (g.toBlocks₂₂)ᴴ := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> ext i j <;>
    simp [Matrix.toBlocks₁₁, Matrix.toBlocks₁₂, Matrix.toBlocks₂₁, Matrix.toBlocks₂₂,
      Matrix.conjTranspose_apply]

private theorem JJ_toBlocks :
    (JJ n).toBlocks₁₁ = 0 ∧ (JJ n).toBlocks₁₂ = 1 ∧ (JJ n).toBlocks₂₁ = -1 ∧ (JJ n).toBlocks₂₂ = 0 := by
  simp [JJ]

private theorem inK_toBlocks₂_eq {k : M2 n} (hk : InK k) :
    k.toBlocks₂₁ = -k.toBlocks₁₂ ∧ k.toBlocks₂₂ = k.toBlocks₁₁ := by
  have hG : kᴴ * JJ n * k = JJ n := hk.1
  have h2 : k * kᴴ = 1 := mul_eq_one_comm.mp hk.2
  have h3 : JJ n * k = k * JJ n := by
    calc JJ n * k = (k * kᴴ) * JJ n * k := by rw [h2, Matrix.one_mul]
      _ = k * (kᴴ * JJ n * k) := by simp only [Matrix.mul_assoc]
      _ = k * JJ n := by rw [hG]
  obtain ⟨j11, j12, j21, j22⟩ := (JJ_toBlocks (n := n))
  have e1 := congrArg Matrix.toBlocks₁₁ h3
  have e2 := congrArg Matrix.toBlocks₁₂ h3
  rw [mul_toBlocks₁₁', mul_toBlocks₁₁', j11, j12, j21] at e1
  rw [mul_toBlocks₁₂, mul_toBlocks₁₂, j11, j12, j22] at e2
  simp at e1 e2
  exact ⟨e1, e2⟩

private theorem neg_toBlocks₁₁_toBlocks₂₁ (g : M2 n) :
    (-g).toBlocks₁₁ = -g.toBlocks₁₁ ∧ (-g).toBlocks₂₁ = -g.toBlocks₂₁ := by
  refine ⟨?_, ?_⟩ <;> ext i j <;> simp [Matrix.toBlocks₁₁, Matrix.toBlocks₂₁]

private theorem one_toBlocks₁₁_toBlocks₁₂ :
    (1 : M2 n).toBlocks₁₁ = 1 ∧ (1 : M2 n).toBlocks₁₂ = 0 := by
  refine ⟨?_, ?_⟩ <;> ext i j <;> simp [Matrix.toBlocks₁₁, Matrix.toBlocks₁₂, Matrix.one_apply]

private theorem inK_toBlocks₁_unitary_relations {k : M2 n} (hk : InK k) :
    (k.toBlocks₁₁)ᴴ * k.toBlocks₁₁ + (k.toBlocks₁₂)ᴴ * k.toBlocks₁₂ = 1 ∧
      (k.toBlocks₁₁)ᴴ * k.toBlocks₁₂ = (k.toBlocks₁₂)ᴴ * k.toBlocks₁₁ := by
  obtain ⟨hc, hd⟩ := inK_toBlocks₂_eq hk
  have hU : kᴴ * k = 1 := hk.2
  obtain ⟨c11, c12, c21, c22⟩ := conjTranspose_toBlocks k
  obtain ⟨o11, o12⟩ := (one_toBlocks₁₁_toBlocks₁₂ (n := n))
  have e1 := congrArg Matrix.toBlocks₁₁ hU
  have e2 := congrArg Matrix.toBlocks₁₂ hU
  rw [mul_toBlocks₁₁', c11, c12, hc, o11] at e1
  rw [mul_toBlocks₁₂, c11, c12, hc, hd, o12] at e2
  simp only [Matrix.conjTranspose_neg, neg_mul, mul_neg, neg_neg] at e1 e2
  refine ⟨e1, ?_⟩
  rw [← sub_eq_zero]
  simpa [sub_eq_add_neg] using e2

theorem first_cayley_block_mul_compact (g : M2 n) {k : M2 n} (hk : InK k) : u1 (g * k) = u1 g * u1 k := by
  obtain ⟨hc, hd⟩ := inK_toBlocks₂_eq hk
  simp only [u1, mul_toBlocks₂₁_eq, mul_toBlocks₂₂_eq, hc, hd, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul,
    Matrix.mul_smul, Matrix.mul_neg, Matrix.neg_mul, smul_add, smul_neg, smul_smul, Complex.I_mul_I]
  module

theorem second_cayley_block_mul_compact (g : M2 n) {k : M2 n} (hk : InK k) : u2 (g * k) = u2 g * u2 k := by
  obtain ⟨hc, hd⟩ := inK_toBlocks₂_eq hk
  simp only [u2, mul_toBlocks₂₁_eq, mul_toBlocks₂₂_eq, hc, hd, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul,
    Matrix.mul_smul, Matrix.mul_neg, Matrix.neg_mul, smul_add, smul_neg, smul_smul, Complex.I_mul_I]
  module

theorem first_cayley_block_compact_unitary {k : M2 n} (hk : InK k) : (u1 k)ᴴ * u1 k = 1 := by
  obtain ⟨hc, hd⟩ := inK_toBlocks₂_eq hk
  obtain ⟨h1, h2⟩ := inK_toBlocks₁_unitary_relations hk
  have e : (u1 k)ᴴ * u1 k = ((k.toBlocks₁₁)ᴴ * k.toBlocks₁₁ + (k.toBlocks₁₂)ᴴ * k.toBlocks₁₂) +
      Complex.I • ((k.toBlocks₁₂)ᴴ * k.toBlocks₁₁ - (k.toBlocks₁₁)ᴴ * k.toBlocks₁₂) := by
    simp only [u1, hc, hd, Matrix.conjTranspose_add, Matrix.conjTranspose_smul, Matrix.conjTranspose_neg,
      Complex.star_def, Complex.conj_I, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.mul_neg, Matrix.neg_mul, smul_add, smul_neg, smul_smul, neg_smul, Complex.I_mul_I, neg_mul]
    module
  rw [e, h1, h2, sub_self, smul_zero, add_zero]

def eps (n : ℕ) : M2 n := fromBlocks 1 0 0 (-1)

theorem eps_sq : eps n * eps n = 1 := by
  simp [eps, Matrix.fromBlocks_multiply, Matrix.fromBlocks_one]

theorem eps_JJ : eps n * JJ n * eps n = -JJ n := by
  simp [eps, JJ, Matrix.fromBlocks_multiply, Matrix.fromBlocks_neg]

theorem eps_conj : (eps n)ᴴ = eps n := by simp [eps, fromBlocks_conjTranspose]

theorem inK_eps {k : M2 n} (hk : InK k) : InK (eps n * k * eps n) := by
  have hG : kᴴ * JJ n * k = JJ n := hk.1
  have hU : kᴴ * k = 1 := hk.2
  have e : eps n * JJ n * eps n = -JJ n := eps_JJ
  refine ⟨?_, ?_⟩
  · show (eps n * k * eps n)ᴴ * JJ n * (eps n * k * eps n) = JJ n
    calc (eps n * k * eps n)ᴴ * JJ n * (eps n * k * eps n)
        = eps n * (kᴴ * (eps n * JJ n * eps n) * k) * eps n := by
          rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, eps_conj]
          simp only [Matrix.mul_assoc]
      _ = -(eps n * (kᴴ * JJ n * k) * eps n) := by
          rw [e]
          simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]
      _ = JJ n := by rw [hG, e, neg_neg]
  · show (eps n * k * eps n)ᴴ * (eps n * k * eps n) = 1
    calc (eps n * k * eps n)ᴴ * (eps n * k * eps n)
        = eps n * (kᴴ * (eps n * eps n) * k) * eps n := by
          rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, eps_conj]
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [eps_sq, Matrix.mul_one, hU, Matrix.mul_one, eps_sq]

theorem first_cayley_block_swap_conj (k : M2 n) : u1 (eps n * k * eps n) = u2 k := by
  simp [u1, u2, mul_toBlocks₂₁_eq, mul_toBlocks₂₂_eq, eps]

theorem second_cayley_block_compact_unitary {k : M2 n} (hk : InK k) : (u2 k)ᴴ * u2 k = 1 := by
  rw [← first_cayley_block_swap_conj]
  exact first_cayley_block_compact_unitary (inK_eps hk)

theorem second_cayley_block_inv_eq_conjTranspose {k : M2 n} (hk : InK k) : (u2 k)⁻¹ = (u2 k)ᴴ := Matrix.inv_eq_left_inv (second_cayley_block_compact_unitary hk)

theorem inverse_second_block_eq_neg_conjTranspose {x : M2 n} (hx : InG x) : ub2 x = -(u2 x)ᴴ := by
  obtain ⟨c11, c12, c21, c22⟩ := conjTranspose_toBlocks x
  obtain ⟨j11, j12, j21, j22⟩ := (JJ_toBlocks (n := n))
  obtain ⟨n11, n21⟩ := neg_toBlocks₁₁_toBlocks₂₁ (JJ n * xᴴ * JJ n)
  simp only [ub2, u2, inv_of_inG hx, n11, n21, mul_toBlocks₁₁', mul_toBlocks₂₁_eq, mul_toBlocks₂₂_eq, mul_toBlocks₁₂,
    c11, c12, c21, c22,
    j11, j12, j21, j22, Matrix.conjTranspose_add, Matrix.conjTranspose_neg, Matrix.conjTranspose_smul,
    Complex.star_def, Complex.conj_I, Matrix.mul_one, Matrix.mul_zero, Matrix.zero_mul, Matrix.one_mul,
    Matrix.mul_neg, Matrix.neg_mul, add_zero, zero_add, neg_neg, neg_smul, smul_neg]
  module

theorem Om_K {k : M2 n} (hk : InK k) : Om k = -((u2 k)⁻¹ * u1 k) := by
  unfold Om
  rw [inverse_second_block_eq_neg_conjTranspose hk.1, inverse_first_block_eq_conjTranspose hk.1, Matrix.inv_eq_left_inv (mul_eq_one_comm.mp (first_cayley_block_compact_unitary hk)),
    ← second_cayley_block_inv_eq_conjTranspose hk, Matrix.neg_mul]

theorem normSq_det_u1K {k : M2 n} (hk : InK k) : Complex.normSq (u1 k).det = 1 := by
  have h := congrArg Matrix.det (first_cayley_block_compact_unitary hk)
  rw [det_mul, det_conjTranspose, det_one] at h
  have h' : (Complex.normSq (u1 k).det : ℂ) = 1 := by rw [Complex.normSq_eq_conj_mul_self]; exact h
  exact_mod_cast h'

theorem fz_K (m : ℕ) (e : ℤ) (z : ℂ) {k : M2 n} (hk : InK k) : fz m e z k = fz m e 0 k := by
  have hd : (u1 k).det * (ub1 k).det = 1 := by
    rw [inverse_first_block_eq_conjTranspose hk.1, Matrix.det_conjTranspose, Complex.star_def, mul_comm,
      ← Complex.normSq_eq_conj_mul_self, normSq_det_u1K hk, Complex.ofReal_one]
  simp only [fz, hd, Complex.one_cpow, neg_zero, Complex.cpow_zero]

theorem first_cayley_block_upper_triangular_mul {p : M2 n} (hp : p.toBlocks₂₁ = 0) (y : M2 n) : u1 (p * y) = p.toBlocks₂₂ * u1 y := by
  simp only [u1, mul_toBlocks₂₁_eq, mul_toBlocks₂₂_eq, hp, Matrix.zero_mul, zero_add, Matrix.mul_add, Matrix.mul_smul]

theorem second_cayley_block_upper_triangular_mul {p : M2 n} (hp : p.toBlocks₂₁ = 0) (y : M2 n) : u2 (p * y) = p.toBlocks₂₂ * u2 y := by
  simp only [u2, mul_toBlocks₂₁_eq, mul_toBlocks₂₂_eq, hp, Matrix.zero_mul, zero_add, Matrix.mul_add, Matrix.mul_smul,
    Matrix.mul_neg]

theorem inG_mul {x y : M2 n} (hx : InG x) (hy : InG y) : InG (x * y) := by
  have hx' : xᴴ * JJ n * x = JJ n := hx
  have hy' : yᴴ * JJ n * y = JJ n := hy
  show (x * y)ᴴ * JJ n * (x * y) = JJ n
  calc (x * y)ᴴ * JJ n * (x * y) = yᴴ * (xᴴ * JJ n * x) * y := by
        rw [Matrix.conjTranspose_mul]
        simp only [Matrix.mul_assoc]
    _ = JJ n := by rw [hx', hy']

theorem Om_up {p y : M2 n} (hp : InG p) (hp21 : p.toBlocks₂₁ = 0) (hy : InG y) : Om (p * y) = Om y := by
  have hp' : pᴴ * JJ n * p = JJ n := hp
  obtain ⟨c11, c12, c21, c22⟩ := conjTranspose_toBlocks p
  obtain ⟨j11, j12, j21, j22⟩ := (JJ_toBlocks (n := n))
  have e := congrArg Matrix.toBlocks₁₂ hp'
  rw [mul_toBlocks₁₂, mul_toBlocks₁₁', mul_toBlocks₁₂, c11, c12, j11, j12, j21, j22, hp21] at e
  simp only [Matrix.conjTranspose_zero, Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one,
    zero_add, add_zero, Matrix.mul_neg, neg_zero] at e
  have hq : (p.toBlocks₂₂)ᴴ * p.toBlocks₁₁ = 1 := by
    have := congrArg Matrix.conjTranspose e
    simpa [Matrix.conjTranspose_mul] using this
  unfold Om
  rw [inverse_second_block_eq_neg_conjTranspose (inG_mul hp hy), inverse_first_block_eq_conjTranspose (inG_mul hp hy), inverse_second_block_eq_neg_conjTranspose hy, inverse_first_block_eq_conjTranspose hy, second_cayley_block_upper_triangular_mul hp21, first_cayley_block_upper_triangular_mul hp21,
    Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.mul_inv_rev, Matrix.inv_eq_right_inv hq,
    Matrix.neg_mul, Matrix.neg_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (p.toBlocks₂₂)ᴴ, hq, Matrix.one_mul]

def lam (m : ℕ) (e : ℤ) (z : ℂ) (p : M2 n) : ℂ :=
  p.det ^ e * (p.toBlocks₂₂).det ^ (-(m : ℤ)) * ((Complex.normSq (p.toBlocks₂₂).det : ℝ) : ℂ) ^ (-z)

theorem fz_up {p y : M2 n} (hp : InG p) (hp21 : p.toBlocks₂₁ = 0) (hy : InG y) (m : ℕ) (e : ℤ) (z : ℂ) :
    fz m e z (p * y) = lam m e z p * fz m e z y := by
  have h1 : (u1 (p * y)).det = (p.toBlocks₂₂).det * (u1 y).det := by rw [first_cayley_block_upper_triangular_mul hp21, Matrix.det_mul]
  have h2 : (u1 (p * y)).det * (ub1 (p * y)).det =
      ((Complex.normSq (p.toBlocks₂₂).det : ℝ) : ℂ) * ((Complex.normSq (u1 y).det : ℝ) : ℂ) := by
    rw [inverse_first_block_eq_conjTranspose (inG_mul hp hy), Matrix.det_conjTranspose, h1, star_mul', Complex.star_def,
      Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_conj_mul_self]
    ring
  have h3 : (u1 y).det * (ub1 y).det = ((Complex.normSq (u1 y).det : ℝ) : ℂ) := by
    rw [inverse_first_block_eq_conjTranspose hy, Matrix.det_conjTranspose, Complex.star_def, Complex.normSq_eq_conj_mul_self]
    ring
  simp only [fz, lam]
  rw [h2, h3, h1, Matrix.det_mul, mul_zpow, mul_zpow,
    Complex.mul_cpow_ofReal_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _)]
  ring

end PositivityTheory.Rg.Sw.HSt.CompactCayleyBlocks
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.Nonzero
section
noncomputable section

open MeasureTheory Matrix Set Filter Topology
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.HSt.Conv

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.AbsSt PositivityTheory.Rg.Sw.HSt.GRH

variable {n : ℕ}

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def psi (m : ℕ) (e : ℤ) (μK : Measure (KR n)) (u : GR n) : ℂ :=
  ∫ k : KR n, (F0 m 0 e (k : GR n))⁻¹ * F0 m 0 e ((k : GR n) * u) ∂μK

theorem psi_continuous (m : ℕ) (e : ℤ) (μK : Measure (KR n)) [IsFiniteMeasure μK] : Continuous (psi m e μK) := by
  have hF : Continuous (Function.uncurry fun (u : GR n) (k : KR n) =>
      (F0 m 0 e (k : GR n))⁻¹ * F0 m 0 e ((k : GR n) * u)) := by
    show Continuous fun p : GR n × KR n => (F0 m 0 e (p.2 : GR n))⁻¹ * F0 m 0 e ((p.2 : GR n) * p.1)
    refine Continuous.mul ?_ ?_
    · exact ((Vac.continuous_weight_factor detU1 m 0 e).comp (continuous_subtype_val.comp continuous_snd)).inv₀
        fun p => Vac.spherical_section_ne_zero detU1 m 0 e _
    · exact (Vac.continuous_weight_factor detU1 m 0 e).comp ((continuous_subtype_val.comp continuous_snd).mul continuous_fst)
  have := continuous_parametric_integral_of_continuous (μ := μK) hF isCompact_univ
  have e : psi m e μK = fun u => ∫ k : KR n, (F0 m 0 e (k : GR n))⁻¹ * F0 m 0 e ((k : GR n) * u) ∂μK := rfl
  rw [e]
  simpa [Measure.restrict_univ] using this

theorem psi_one (m : ℕ) (e : ℤ) (μK : Measure (KR n)) : psi m e μK 1 = (μK Set.univ).toReal := by
  unfold psi
  simp only [mul_one]
  have h : ∀ k : KR n, (F0 m 0 e (k : GR n))⁻¹ * F0 m 0 e (k : GR n) = 1 := fun k =>
    inv_mul_cancel₀ (Vac.spherical_section_ne_zero detU1 _ _ _ _)
  simp only [h]
  rw [integral_const]
  simp [Measure.real]

private theorem mR_conjTranspose_eq_mR_inv_of_KR (k : KR n) : (mR (k : GR n))ᴴ = mR ((k : GR n)⁻¹) := by
  have hk : (mR (k : GR n))ᴴ * mR (k : GR n) = 1 := (show InK (mR (k : GR n)) from k.2).2
  have h1 : mR (k : GR n) * mR ((k : GR n)⁻¹) = 1 := by
    rw [← mR_mul, mul_inv_cancel]
    simp [mR]
  calc (mR (k : GR n))ᴴ = (mR (k : GR n))ᴴ * (mR (k : GR n) * mR ((k : GR n)⁻¹)) := by
        rw [h1, Matrix.mul_one]
    _ = mR ((k : GR n)⁻¹) := by rw [← Matrix.mul_assoc, hk, Matrix.one_mul]

theorem cw_zero (m : ℕ) (e : ℤ) (ν : Measure (GR n)) [ν.IsHaarMeasure] (μK : Measure (KR n)) [μK.IsHaarMeasure]
    {β : M2 n → ℝ} (hβc : Continuous β) (hβs : HasCompactSupport β) :
    cw m e ν μK β 0 = ∫ u : GR n, (β (mR u) : ℂ) * psi m e μK u ∂ν := by
  have hF := Vac.continuous_weight_factor (n := n) detU1 m 0 e
  have hFne : ∀ g, F0 (n := n) m 0 e g ≠ 0 := fun g => Vac.spherical_section_ne_zero detU1 m 0 e g
  have hCc : IsCompact (mR ⁻¹' (tsupport β)) := isCompact_preimage_mR hβs.isCompact
  have hk : Continuous (fun p : GR n × KR n => ((p.2 : GR n))) :=
    continuous_subtype_val.comp continuous_snd
  let A : GR n × KR n → ℂ := fun p =>
    F0 m 0 e p.1 * ((F0 m 0 e (p.2 : GR n))⁻¹ * (β (mR ((p.2 : GR n)⁻¹ * p.1)) : ℂ))
  let B : GR n × KR n → ℂ := fun p =>
    (β (mR p.1) : ℂ) * ((F0 m 0 e (p.2 : GR n))⁻¹ * F0 m 0 e ((p.2 : GR n) * p.1))
  have hAc : Continuous A := by
    refine (hF.comp continuous_fst).mul (((hF.comp hk).inv₀ fun p => hFne _).mul ?_)
    exact Complex.continuous_ofReal.comp
      (hβc.comp (PositivityTheory.Rg.Sw.HSt.GRH.continuous_mR.comp (hk.inv.mul continuous_fst)))
  have hBc : Continuous B := by
    refine (Complex.continuous_ofReal.comp (hβc.comp (PositivityTheory.Rg.Sw.HSt.GRH.continuous_mR.comp continuous_fst))).mul
      (((hF.comp hk).inv₀ fun p => hFne _).mul (hF.comp (hk.mul continuous_fst)))
  have hAs : HasCompactSupport A := by
    refine HasCompactSupport.intro
      ((((isCompact_univ (X := KR n)).prod hCc).image
        ((continuous_subtype_val.comp continuous_fst).mul continuous_snd)).prod
        (isCompact_univ (X := KR n))) ?_
    intro p hp
    have hz : β (mR ((p.2 : GR n)⁻¹ * p.1)) = 0 := by
      by_contra hne
      apply hp
      refine ⟨⟨⟨p.2, (p.2 : GR n)⁻¹ * p.1⟩, ⟨Set.mem_univ _, subset_tsupport _ hne⟩, ?_⟩, Set.mem_univ _⟩
      simp
    simp [A, hz]
  have hBs : HasCompactSupport B := by
    refine HasCompactSupport.intro (hCc.prod (isCompact_univ (X := KR n))) ?_
    intro p hp
    have hz : β (mR p.1) = 0 := by
      by_contra hne
      exact hp ⟨subset_tsupport _ hne, Set.mem_univ _⟩
    simp [B, hz]
  have hAi : Integrable A (ν.prod μK) := hAc.integrable_of_hasCompactSupport hAs
  have hBi : Integrable B (ν.prod μK) := hBc.integrable_of_hasCompactSupport hBs
  calc cw m e ν μK β 0 = ∫ u, ∫ k, A (u, k) ∂μK ∂ν := by
        unfold cw
        congr 1
        ext u
        unfold phi tw
        rw [Complex.cpow_zero, mul_one, ← integral_const_mul]
        congr 1
        ext k
        simp only [A]
        rw [mR_conjTranspose_eq_mR_inv_of_KR, ← mR_mul]
    _ = ∫ k, ∫ u, A (u, k) ∂ν ∂μK := integral_integral_swap hAi
    _ = ∫ k, ∫ v, A ((k : GR n) * v, k) ∂ν ∂μK := by
        congr 1
        ext k
        exact (integral_mul_left_eq_self (fun u => A (u, k)) (k : GR n)).symm
    _ = ∫ k, ∫ v, B (v, k) ∂ν ∂μK := by
        congr 1
        ext k
        congr 1
        ext v
        simp only [A, B]
        rw [inv_mul_cancel_left]
        ring
    _ = ∫ v, ∫ k, B (v, k) ∂μK ∂ν := (integral_integral_swap hBi).symm
    _ = ∫ u : GR n, (β (mR u) : ℂ) * psi m e μK u ∂ν := by
        congr 1
        ext v
        simp only [B, psi]
        rw [integral_const_mul]

theorem exists_bump (m : ℕ) (e : ℤ) (ν : Measure (GR n)) [ν.IsHaarMeasure] (μK : Measure (KR n)) [μK.IsHaarMeasure] :
    ∃ β : M2 n → ℝ, ContDiff ℝ ∞ β ∧ HasCompactSupport β ∧ cw m e ν μK β 0 ≠ 0 := by
  have hpc : Continuous (psi m e μK) := psi_continuous m e μK
  have h1 : mR (1 : GR n) = 1 := by simp [mR]
  have hp1 : 0 < (psi m e μK 1).re := by
    rw [psi_one, Complex.ofReal_re]
    exact ENNReal.toReal_pos (isOpen_univ.measure_ne_zero μK Set.univ_nonempty) (measure_ne_top _ _)
  have hO : IsOpen {u : GR n | 0 < (psi m e μK u).re} :=
    isOpen_lt continuous_const (Complex.continuous_re.comp hpc)
  obtain ⟨O, hOo, hOeq⟩ := isClosedEmbedding_mR.isInducing.isOpen_iff.mp hO
  have h1O : (1 : M2 n) ∈ O := by
    have h : (1 : GR n) ∈ mR ⁻¹' O := by
      rw [hOeq]
      exact hp1
    simpa [h1] using h
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hOo 1 h1O
  let b : ContDiffBump (1 : M2 n) := ⟨r / 2, r, by positivity, by linarith⟩
  refine ⟨⇑b, b.contDiff, b.hasCompactSupport, ?_⟩
  rw [cw_zero m e ν μK b.continuous b.hasCompactSupport]
  set g : GR n → ℂ := fun u => (b (mR u) : ℂ) * psi m e μK u with hg
  have hgs : HasCompactSupport g := by
    have h := (b.hasCompactSupport.comp_isClosedEmbedding isClosedEmbedding_mR).comp_left
      (g := Complex.ofReal) Complex.ofReal_zero
    exact h.mul_right
  have hgc : Continuous g :=
    (Complex.continuous_ofReal.comp (b.continuous.comp PositivityTheory.Rg.Sw.HSt.GRH.continuous_mR)).mul hpc
  have hre : ∀ u, (g u).re = b (mR u) * (psi m e μK u).re := fun u => Complex.re_ofReal_mul _ _
  have hpos : 0 < ∫ u, (g u).re ∂ν := by
    refine Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := 1)
      (Complex.continuous_re.comp hgc) (hgs.comp_left Complex.zero_re) ?_ ?_
    · intro u
      show 0 ≤ (g u).re
      rw [hre]
      by_cases hu : b (mR u) = 0
      · simp [hu]
      · have hmem : mR u ∈ Metric.ball (1 : M2 n) r := by
          have hs : mR u ∈ Function.support b := hu
          rwa [b.support_eq] at hs
        have hu' : u ∈ mR ⁻¹' O := hball hmem
        rw [hOeq] at hu'
        exact mul_nonneg b.nonneg (le_of_lt hu')
    · show (g 1).re ≠ 0
      rw [hre, h1, b.one_of_mem_closedBall (Metric.mem_closedBall_self (by positivity)), one_mul]
      exact ne_of_gt hp1
  intro h
  have hz : (∫ u, g u ∂ν).re = 0 := by
    rw [h]
    simp
  have hgi : Integrable g ν := hgc.integrable_of_hasCompactSupport hgs
  have hint := integral_re hgi
  simp only [RCLike.re_to_complex] at hint
  linarith

end PositivityTheory.Rg.Sw.HSt.Conv
end
end

