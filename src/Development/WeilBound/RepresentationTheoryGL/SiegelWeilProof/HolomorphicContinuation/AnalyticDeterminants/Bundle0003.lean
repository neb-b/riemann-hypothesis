module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.Bundle0006

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.CayleyA
section
noncomputable section

open Matrix

namespace PositivityTheory.Rg.Sw.LVs

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def Equivar : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (F : Matrix ι ι ℂ → ℂ) (A : Matrix ι ι ℂ), AnalyticAt ℂ F 0 →
    detD (fun T => F (A * T)) = A.det * detD F

def Reindex : Prop :=
  ∀ (ι κ : Type) [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (e : ι ≃ κ) (F : Matrix κ κ ℂ → ℂ),
    AnalyticAt ℂ F 0 → detD (fun T : Matrix ι ι ℂ => F (T.reindex e e)) = detD F

def KappaFin : Prop :=
  ∀ (N : ℕ) (t : ℤ), detD (fun T : Matrix (Fin N) (Fin N) ℂ => (1 + T).det ^ t) =
    ∏ i ∈ Finset.range N, ((t : ℂ) + i)

end PositivityTheory.Rg.Sw.LVs
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.HermRealSmul
section
noncomputable section

open Filter Topology Set Metric Matrix
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.LVs.HolB

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs

variable {n : ℕ}

theorem JJ_sq : JJ n * JJ n = -1 := by
  simp [JJ, fromBlocks_multiply, ← fromBlocks_one, fromBlocks_neg]

theorem inG_mul {a b : M2 n} (ha : InG a) (hb : InG b) : InG (a * b) := by
  unfold InG at *
  rw [conjTranspose_mul]
  calc bᴴ * aᴴ * JJ n * (a * b) = bᴴ * (aᴴ * JJ n * a) * b := by simp only [Matrix.mul_assoc]
    _ = JJ n := by rw [ha, hb]

theorem inG_upper {b : Matrix (Fin n) (Fin n) ℂ} (hb : bᴴ = b) : InG (fromBlocks 1 b 0 1 : M2 n) := by
  unfold InG JJ
  simp [fromBlocks_conjTranspose, fromBlocks_multiply, hb]

theorem inG_lower {c : Matrix (Fin n) (Fin n) ℂ} (hc : cᴴ = c) : InG (fromBlocks 1 0 c 1 : M2 n) := by
  unfold InG JJ
  simp [fromBlocks_conjTranspose, fromBlocks_multiply, hc]

theorem inG_scalar {c : ℂ} (hc : star c * c = 1) : InG (c • (1 : M2 n)) := by
  show (c • (1 : M2 n))ᴴ * JJ n * (c • (1 : M2 n)) = JJ n
  rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_one, Matrix.smul_mul, Matrix.one_mul,
    Matrix.mul_smul, Matrix.mul_one, smul_smul, mul_comm, hc, one_smul]

theorem upper_line (y : M2 n) (b : Matrix (Fin n) (Fin n) ℂ) (t : ℂ) :
    y + t • (y * fromBlocks 0 b 0 0) = y * fromBlocks 1 (t • b) 0 1 := by
  have e : (fromBlocks 1 (t • b) 0 1 : M2 n) = 1 + t • fromBlocks 0 b 0 0 := by
    rw [← Matrix.fromBlocks_one, Matrix.fromBlocks_smul, Matrix.fromBlocks_add]
    simp
  rw [e, mul_add, mul_one, mul_smul_comm]

theorem lower_line (y : M2 n) (c : Matrix (Fin n) (Fin n) ℂ) (t : ℂ) :
    y + t • (y * fromBlocks 0 0 c 0) = y * fromBlocks 1 0 (t • c) 1 := by
  have e : (fromBlocks 1 0 (t • c) 1 : M2 n) = 1 + t • fromBlocks 0 0 c 0 := by
    rw [← Matrix.fromBlocks_one, Matrix.fromBlocks_smul, Matrix.fromBlocks_add]
    simp
  rw [e, mul_add, mul_one, mul_smul_comm]

theorem herm_real_smul {b : Matrix (Fin n) (Fin n) ℂ} (hb : bᴴ = b) (t : ℝ) : ((t : ℂ) • b)ᴴ = (t : ℂ) • b := by
  rw [conjTranspose_smul, hb]
  simp

private theorem fderiv_apply_eq_zero_of_const_on_real_line {E W : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup W] [NormedSpace ℂ W] {f : E → W} {y v : E}
    (hf : DifferentiableAt ℂ f y) (h : ∀ t : ℝ, f (y + (t : ℂ) • v) = f y) : fderiv ℂ f y v = 0 := by
  have hl : HasDerivAt (fun t : ℝ => y + (t : ℂ) • v) v 0 := by
    have h0 := ((Complex.ofRealCLM.hasDerivAt (x := (0 : ℝ))).smul_const v).const_add y
    convert h0 using 1
    · rfl
    · rw [Complex.ofRealCLM_apply, Complex.ofReal_one, one_smul]
  have h1 : HasFDerivAt f ((fderiv ℂ f y).restrictScalars ℝ) (y + ((0 : ℝ) : ℂ) • v) := by
    simpa using hf.hasFDerivAt.restrictScalars ℝ
  have hc := h1.comp_hasDerivAt (0 : ℝ) hl
  have hk : (f ∘ fun t : ℝ => y + (t : ℂ) • v) = fun _ => f y := funext h
  rw [hk] at hc
  exact ((hasDerivAt_const (0 : ℝ) (f y)).unique hc).symm

theorem fderiv_line {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W] {f : M2 n → W} {y v : M2 n}
    (hf : DifferentiableAt ℂ f y) (h : ∀ t : ℝ, f (y + (t : ℂ) • v) = f y) : fderiv ℂ f y v = 0 := by
  exact fderiv_apply_eq_zero_of_const_on_real_line hf h

end PositivityTheory.Rg.Sw.LVs.HolB
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.InfInvA
section
noncomputable section

open MeasureTheory Matrix
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.LVs.II

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

def reK (e : M2 n) : M2 n := (1 / 2 : ℂ) • (e - eᴴ)

def imK (e : M2 n) : M2 n := (-Complex.I / 2) • (e + eᴴ)

def dK (F : M2 n → ℂ) (x e : M2 n) : ℂ := fderiv ℝ F x (reK e * x) + Complex.I * fderiv ℝ F x (imK e * x)

def KSet (n : ℕ) : Set (M2 n) := {g | InK g}

def LeftDeriv : Prop :=
  ∀ (n : ℕ) (Kg : Type) [Group Kg] [TopologicalSpace Kg] [IsTopologicalGroup Kg] [CompactSpace Kg] [MeasurableSpace Kg]
    [BorelSpace Kg] (μ : Measure Kg) [μ.IsHaarMeasure] (ι : Kg →* M2 n), Continuous ι → (∀ g, InK g ↔ ∃ k, ι k = g) →
    ∀ (F : M2 n → ℂ) (U : Set (M2 n)), IsOpen U → KSet n ⊆ U → ContDiffOn ℝ 1 F U →
    ∀ e : M2 n, e * JJ n = JJ n * e →
      Integrable (fun k => dK F (ι k) e) μ ∧ ∫ k, dK F (ι k) e ∂μ = 0

def LawDeriv : Prop :=
  ∀ (n : ℕ) (Θ : M2 n → ℂ) (Ω : Set (M2 n)), IsOpen Ω → {g | InG g} ⊆ Ω → DifferentiableOn ℂ Θ Ω →
    (∀ p x, InG p → p.toBlocks₂₁ = 0 → InG x → Θ (p * x) = ((‖(p.toBlocks₂₂).det‖ ^ (-(2 * (n : ℤ))) : ℝ) : ℂ) * Θ x) →
    ∀ x, InG x → ∀ Y : M2 n, Y.toBlocks₂₁ = 0 →
      fderiv ℂ Θ x (Y * x) = (n : ℂ) * (Y.toBlocks₁₁.trace - Y.toBlocks₂₂.trace) * Θ x

def eA (a b : Fin n) : M2 n := fromBlocks (Matrix.single a b 1) 0 0 (Matrix.single a b 1)

def eB (a b : Fin n) : M2 n := fromBlocks 0 (Matrix.single a b 1) (-Matrix.single a b 1) 0

def cA (Z : M2 n) (a b : Fin n) (x : M2 n) : ℂ := (x * Z * xᴴ).toBlocks₂₂ a b

def cB (Z : M2 n) (a b : Fin n) (x : M2 n) : ℂ := -(x * Z * xᴴ).toBlocks₂₁ a b

def PtId : Prop :=
  ∀ (n : ℕ) (Θ : M2 n → ℂ) (x Z : M2 n), InK x → ContDiffAt ℂ 1 Θ x →
    (∀ Y : M2 n, Y.toBlocks₂₁ = 0 → fderiv ℂ Θ x (Y * x) = (n : ℂ) * (Y.toBlocks₁₁.trace - Y.toBlocks₂₂.trace) * Θ x) →
    fderiv ℂ Θ x (x * Z) =
      ∑ a, ∑ b, (dK (fun y => cA Z a b y * Θ y) x (eA a b) + dK (fun y => cB Z a b y * Θ y) x (eB a b))

def CDiff : Prop := ∀ (n : ℕ) (Z : M2 n) (a b : Fin n), ContDiff ℝ ∞ (cA Z a b) ∧ ContDiff ℝ ∞ (cB Z a b)

end PositivityTheory.Rg.Sw.LVs.II
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.ScalarDir
section
noncomputable section

open Filter Topology Set
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.LVs.HolD

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem line2 {H : E → V} {y w : E} {m : E →L[ℂ] E} (hfd : DifferentiableAt ℂ (fderiv ℂ H) y)
    (hz : ∀ t : ℝ, fderiv ℂ H (y + (t : ℂ) • w) (m (y + (t : ℂ) • w)) = 0) :
    fderiv ℂ (fderiv ℂ H) y w (m y) + fderiv ℂ H y (m w) = 0 := by
  have hψ : HasFDerivAt (fun z => fderiv ℂ H z (m z))
      ((fderiv ℂ H y).comp m + (fderiv ℂ (fderiv ℂ H) y).flip (m y)) y :=
    hfd.hasFDerivAt.clm_apply m.hasFDerivAt
  have h := GlobalTheory.SCV.fderiv_apply_eq_zero_of_frequently hψ.differentiableAt (s := w)
    (GlobalTheory.SCV.frequently_nhdsNE_of_eventually_ofReal
      (p := fun t : ℂ => fderiv ℂ H (y + t • w) (m (y + t • w)) = fderiv ℂ H y (m y))
      (Eventually.of_forall fun t => by
        have h0 := hz 0
        simp only [Complex.ofReal_zero, zero_smul, add_zero] at h0
        rw [hz t, h0]))
  rw [hψ.fderiv] at h
  simpa [add_comm] using h

theorem scalar_dir {H : E → V} {y : E} (hd : DifferentiableAt ℂ H y)
    (h : ∀ t : ℝ, H (Complex.exp ((t : ℂ) * Complex.I) • y) = 0) : fderiv ℂ H y y = 0 := by
  have hγ := (((hasDerivAt_id (0 : ℝ)).ofReal_comp.mul_const Complex.I).cexp).smul_const y
  have hc := HasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) (hd.hasFDerivAt.restrictScalars ℝ) hγ (by simp)
  have hc0 := hc.congr_of_eventuallyEq (f₁ := fun _ : ℝ => (0 : V)) (Eventually.of_forall fun t => (h t).symm)
  have := hc0.unique (hasDerivAt_const (0 : ℝ) (0 : V))
  simp only [ContinuousLinearMap.coe_restrictScalars', id, Complex.ofReal_zero, zero_mul, Complex.exp_zero,
    one_mul, map_smul, Complex.ofReal_one] at this
  exact (smul_eq_zero.mp this).resolve_left Complex.I_ne_zero

end PositivityTheory.Rg.Sw.LVs.HolD
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.SecondCayleyBlockMulConjTransposeEq
section
noncomputable section

set_option linter.unusedSimpArgs false

open Matrix
open scoped ComplexOrder

namespace PositivityTheory.Rg.Sw.LVs

open PositivityTheory.Rg.Sw

variable {n : ℕ}

theorem JJ_mul_JJ : JJ n * JJ n = -1 := by
  simp [JJ, fromBlocks_multiply, ← fromBlocks_one, fromBlocks_neg]

theorem isUnit_det_of_inG' {g : M2 n} (hg : InG g) : IsUnit g.det := by
  have h := congrArg Matrix.det hg
  rw [det_mul, det_mul, det_conjTranspose] at h
  have hJ : (JJ n).det ≠ 0 := by
    intro h0
    have := congrArg Matrix.det (JJ_mul_JJ (n := n))
    rw [det_mul, h0, zero_mul, det_neg, det_one] at this
    simp at this
  refine isUnit_iff_ne_zero.2 fun h0 => hJ ?_
  rw [h0, mul_zero] at h
  exact h.symm

theorem mul_JJ_conjTranspose {g : M2 n} (hg : InG g) : g * JJ n * gᴴ = JJ n := by
  have h1 : (-(JJ n) * gᴴ * JJ n) * g = 1 := by
    have : -(JJ n) * gᴴ * JJ n * g = -(JJ n) * (gᴴ * JJ n * g) := by simp only [Matrix.mul_assoc]
    rw [this, hg, Matrix.neg_mul, JJ_mul_JJ, neg_neg]
  have h2 : g * (-(JJ n) * gᴴ * JJ n) = 1 := mul_eq_one_comm.1 h1
  have h3 : g * (-(JJ n) * gᴴ * JJ n) * JJ n = JJ n := by rw [h2, Matrix.one_mul]
  have h4 : g * (-(JJ n) * gᴴ * JJ n) * JJ n = g * JJ n * gᴴ := by
    simp only [Matrix.mul_assoc, JJ_mul_JJ, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_one, neg_neg]
  rw [← h4, h3]

theorem lower_rel {g : M2 n} (hg : InG g) : g.toBlocks₂₁ * g.toBlocks₂₂ᴴ = g.toBlocks₂₂ * g.toBlocks₂₁ᴴ := by
  have h := congrArg Matrix.toBlocks₂₂ (mul_JJ_conjTranspose hg)
  rw [← fromBlocks_toBlocks g] at h
  simp only [JJ, fromBlocks_conjTranspose, fromBlocks_multiply, toBlocks_fromBlocks₂₂] at h
  simp only [Matrix.mul_zero, zero_add, Matrix.mul_neg, Matrix.mul_one, add_zero] at h
  have : -(g.toBlocks₂₂ * g.toBlocks₂₁ᴴ) + g.toBlocks₂₁ * g.toBlocks₂₂ᴴ = 0 := by
    rw [← h]; simp
  rw [neg_add_eq_zero] at this
  exact this.symm

theorem first_cayley_block_mul_conjTranspose_eq {g : M2 n} (hg : InG g) :
    u1 g * (u1 g)ᴴ = g.toBlocks₂₁ * g.toBlocks₂₁ᴴ + g.toBlocks₂₂ * g.toBlocks₂₂ᴴ := by
  have h := lower_rel hg
  simp only [u1, conjTranspose_add, conjTranspose_smul, Complex.star_def, Complex.conj_I, Matrix.add_mul,
    Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [h]
  match_scalars <;> simp [Complex.I_mul_I] <;> ring_nf <;> simp [Complex.I_sq]

theorem second_cayley_block_mul_conjTranspose_eq {g : M2 n} (hg : InG g) :
    u2 g * (u2 g)ᴴ = g.toBlocks₂₁ * g.toBlocks₂₁ᴴ + g.toBlocks₂₂ * g.toBlocks₂₂ᴴ := by
  have h := lower_rel hg
  simp only [u2, conjTranspose_add, conjTranspose_neg, conjTranspose_smul, Complex.star_def, Complex.conj_I,
    Matrix.add_mul, Matrix.mul_add, Matrix.neg_mul, Matrix.mul_neg, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [h]
  match_scalars <;> simp [Complex.I_mul_I] <;> ring_nf <;> simp [Complex.I_sq]

theorem inv_eq_of_inG {g : M2 n} (hg : InG g) : g⁻¹ = -(JJ n) * gᴴ * JJ n := by
  have h1 : (-(JJ n) * gᴴ * JJ n) * g = 1 := by
    have : -(JJ n) * gᴴ * JJ n * g = -(JJ n) * (gᴴ * JJ n * g) := by simp only [Matrix.mul_assoc]
    rw [this, hg, Matrix.neg_mul, JJ_mul_JJ, neg_neg]
  exact Matrix.inv_eq_left_inv h1

theorem inverse_first_block_eq_of_group {g : M2 n} (hg : InG g) : ub1 g = (u1 g)ᴴ := by
  rw [ub1, inv_eq_of_inG hg, u1]
  conv_lhs => rw [← fromBlocks_toBlocks g]
  simp only [JJ, fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_neg, toBlocks_fromBlocks₁₁,
    toBlocks_fromBlocks₂₁, conjTranspose_add, conjTranspose_smul, Complex.star_def, Complex.conj_I]
  simp only [Matrix.zero_mul, Matrix.one_mul, Matrix.neg_mul, Matrix.mul_zero, Matrix.mul_one, Matrix.mul_neg,
    zero_add, add_zero, neg_zero, neg_neg]
  module

theorem posDef_lower {g : M2 n} (hg : InG g) :
    (g.toBlocks₂₁ * g.toBlocks₂₁ᴴ + g.toBlocks₂₂ * g.toBlocks₂₂ᴴ).PosDef := by
  have hu : IsUnit gᴴ := by
    rw [Matrix.isUnit_iff_isUnit_det, det_conjTranspose]
    exact (isUnit_det_of_inG' hg).star
  have hP : (gᴴᴴ * gᴴ).PosDef := Matrix.PosDef.conjTranspose_mul_self _ (Matrix.mulVec_injective_iff_isUnit.2 hu)
  rw [conjTranspose_conjTranspose] at hP
  have h2 := hP.submatrix (e := (Sum.inr : Fin n → Fin n ⊕ Fin n)) Sum.inr_injective
  convert h2 using 1
  conv_rhs => rw [← fromBlocks_toBlocks g]
  ext i j
  simp [fromBlocks_conjTranspose, fromBlocks_multiply, Matrix.submatrix]

theorem det_first_cayley_block_ne_zero {g : M2 n} (hg : InG g) : (u1 g).det ≠ 0 := by
  intro h
  have h1 := congrArg Matrix.det (first_cayley_block_mul_conjTranspose_eq hg)
  rw [det_mul, h, zero_mul] at h1
  exact (posDef_lower hg).det_pos.ne' h1.symm

theorem det_second_cayley_block_ne_zero {g : M2 n} (hg : InG g) : (u2 g).det ≠ 0 := by
  intro h
  have h1 := congrArg Matrix.det (second_cayley_block_mul_conjTranspose_eq hg)
  rw [det_mul, h, zero_mul] at h1
  exact (posDef_lower hg).det_pos.ne' h1.symm

theorem automorphy_first_mul_parabolic {P : M2 n} (x : M2 n) (hP : P.toBlocks₂₁ = 0) : u1 (P * x) = P.toBlocks₂₂ * u1 x := by
  conv_lhs => rw [← fromBlocks_toBlocks P, ← fromBlocks_toBlocks x, hP]
  simp only [u1, fromBlocks_multiply, toBlocks_fromBlocks₂₁, toBlocks_fromBlocks₂₂, Matrix.zero_mul, zero_add,
    Matrix.mul_add, Matrix.mul_smul]

theorem automorphy_second_mul_parabolic {P : M2 n} (x : M2 n) (hP : P.toBlocks₂₁ = 0) : u2 (P * x) = P.toBlocks₂₂ * u2 x := by
  conv_lhs => rw [← fromBlocks_toBlocks P, ← fromBlocks_toBlocks x, hP]
  simp only [u2, fromBlocks_multiply, toBlocks_fromBlocks₂₁, toBlocks_fromBlocks₂₂, Matrix.zero_mul, zero_add,
    Matrix.mul_add, Matrix.mul_smul, Matrix.mul_neg]

theorem det_par {P : M2 n} (hP : P.toBlocks₂₁ = 0) : P.det = P.toBlocks₁₁.det * P.toBlocks₂₂.det := by
  conv_lhs => rw [← fromBlocks_toBlocks P, hP]
  exact det_fromBlocks_zero₂₁ _ _ _

theorem par_rel {P : M2 n} (hG : InG P) (hP : P.toBlocks₂₁ = 0) : P.toBlocks₁₁ᴴ * P.toBlocks₂₂ = 1 := by
  have h := congrArg Matrix.toBlocks₁₂ hG
  rw [← fromBlocks_toBlocks P, hP] at h
  simpa [JJ, fromBlocks_conjTranspose, fromBlocks_multiply] using h

theorem inverse_first_block_mul_parabolic {P x : M2 n} (hP : P.toBlocks₂₁ = 0) (hPu : IsUnit P.det) :
    ub1 (P * x) = ub1 x * (P.toBlocks₁₁)⁻¹ := by
  have hA : IsUnit P.toBlocks₁₁.det := by
    rw [det_par hP] at hPu; exact isUnit_of_mul_isUnit_left hPu
  have hD : IsUnit P.toBlocks₂₂.det := by
    rw [det_par hP] at hPu; exact isUnit_of_mul_isUnit_right hPu
  have hinv : P⁻¹ = fromBlocks (P.toBlocks₁₁)⁻¹ (-((P.toBlocks₁₁)⁻¹ * P.toBlocks₁₂ * (P.toBlocks₂₂)⁻¹)) 0
      (P.toBlocks₂₂)⁻¹ := by
    conv_lhs => rw [← fromBlocks_toBlocks P, hP]
    refine Matrix.inv_eq_right_inv ?_
    rw [fromBlocks_multiply]
    simp only [Matrix.mul_zero, add_zero, Matrix.zero_mul, zero_add, Matrix.mul_neg,
      Matrix.mul_nonsing_inv _ hA, Matrix.mul_nonsing_inv _ hD]
    rw [← fromBlocks_one]
    congr 1 <;> simp [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hA, Matrix.mul_nonsing_inv _ hD]
  rw [ub1, ub1, Matrix.mul_inv_rev, hinv]
  conv_lhs => rw [← fromBlocks_toBlocks x⁻¹]
  simp only [fromBlocks_multiply, toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₂₁, Matrix.mul_zero, add_zero,
    Matrix.add_mul, Matrix.smul_mul]

theorem lower_mul_conjTranspose (g : M2 n) :
    (g * gᴴ).toBlocks₂₂ = g.toBlocks₂₁ * g.toBlocks₂₁ᴴ + g.toBlocks₂₂ * g.toBlocks₂₂ᴴ := by
  conv_lhs => rw [← fromBlocks_toBlocks g]
  simp [fromBlocks_conjTranspose, fromBlocks_multiply]

theorem first_cayley_block_unitary {k : M2 n} (hk : InG k ∧ kᴴ * k = 1) : u1 k * (u1 k)ᴴ = 1 := by
  rw [first_cayley_block_mul_conjTranspose_eq hk.1, ← lower_mul_conjTranspose, mul_eq_one_comm.1 hk.2]
  simp [← fromBlocks_one]

theorem second_cayley_block_unitary {k : M2 n} (hk : InG k ∧ kᴴ * k = 1) : u2 k * (u2 k)ᴴ = 1 := by
  rw [second_cayley_block_mul_conjTranspose_eq hk.1, ← lower_mul_conjTranspose, mul_eq_one_comm.1 hk.2]
  simp [← fromBlocks_one]

end PositivityTheory.Rg.Sw.LVs
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.SingToDiffA
section
noncomputable section

open MeasureTheory Matrix Filter Topology
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.LVs

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

open PositivityTheory.Rg.Sw

namespace STD

variable {n : ℕ}

abbrev Vr (n : ℕ) := Fin n → Fin n → ℝ

def hermLin (n : ℕ) : Vr n →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ where
  toFun := herm
  map_add' x y := by
    ext i j
    simp only [herm, Pi.add_apply, Matrix.add_apply]
    push_cast
    ring
  map_smul' c x := by
    ext i j
    simp only [herm, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Matrix.smul_apply, Complex.real_smul]
    push_cast
    ring

def hermL (n : ℕ) : Vr n →L[ℝ] Matrix (Fin n) (Fin n) ℂ := LinearMap.toContinuousLinearMap (hermLin n)

theorem hermL_apply (x : Vr n) : hermL n x = herm x := rfl

theorem herm_zero : herm (0 : Vr n) = 0 := by
  ext i j; simp [herm]

def v1 (r c : Fin n) : Vr n := fun i j =>
  ((if i = r ∧ j = c then 1 else 0) + (if i = c ∧ j = r then 1 else 0)) / 2

def v2 (r c : Fin n) : Vr n := fun i j =>
  ((if i = c ∧ j = r then 1 else 0) - (if i = r ∧ j = c then 1 else 0)) / 2

theorem herm_v (r c : Fin n) : herm (v1 r c) + Complex.I • herm (v2 r c) = Matrix.single r c 1 := by
  ext i j
  have e1 : (if j = r ∧ i = c then (1:ℝ) else 0) = if i = c ∧ j = r then 1 else 0 := by
    simp only [and_comm]
  have e2 : (if j = c ∧ i = r then (1:ℝ) else 0) = if i = r ∧ j = c then 1 else 0 := by
    simp only [and_comm]
  have e3 : (Matrix.single r c (1:ℂ)) i j = (((if i = r ∧ j = c then (1:ℝ) else 0 : ℝ)) : ℂ) := by
    rw [Matrix.single_apply]
    by_cases h : i = r ∧ j = c
    · obtain ⟨rfl, rfl⟩ := h; simp
    · rw [if_neg h, if_neg (fun h' => h ⟨h'.1.symm, h'.2.symm⟩)]; simp
  rw [e3]
  simp only [herm, v1, v2, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, e1, e2]
  generalize (if i = r ∧ j = c then (1:ℝ) else 0) = a
  generalize (if i = c ∧ j = r then (1:ℝ) else 0) = b
  push_cast
  linear_combination ((b:ℂ) - a) / 2 * Complex.I_sq

def dc (a : Fin n × Fin n) (f : Vr n → ℂ) : Vr n → ℂ :=
  fun x => fderiv ℝ f x (v1 a.1 a.2) + Complex.I * fderiv ℝ f x (v2 a.1 a.2)

def dList : List (Fin n × Fin n) → (Vr n → ℂ) → Vr n → ℂ
  | [], f => f
  | a :: l, f => dc a (dList l f)

end STD

end PositivityTheory.Rg.Sw.LVs
end
end

