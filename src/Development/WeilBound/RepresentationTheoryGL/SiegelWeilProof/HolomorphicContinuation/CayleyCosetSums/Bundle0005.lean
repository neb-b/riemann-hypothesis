module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.Bundle0004
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.Bundle0005
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.Bundle0008
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.Bundle0006
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.InnerGen
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.Bundle0006

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.CapelliDeterminantRisingFactorial
section
noncomputable section

open Matrix Filter Topology
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.HSt.CKC

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

open PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.LVs.CK

theorem iterated_derivative_column_case (t : ℂ) (M : ℕ) (e : Equiv.Perm (Fin (M + 1))) (c : Fin (M + 1)) :
    iteratedFDeriv ℂ (M + 1) (fun y => fderiv ℂ (Hc (M + 1 + 1) t) y (Matrix.single 0 c.succ 1)) 0
        (fun k => Matrix.single k.succ (Equiv.Perm.decomposeFin.symm (c.succ, e) k.succ) 1) =
      -iteratedFDeriv ℂ (M + 1) (Hc (M + 1) t) 0 (fun k => Matrix.single k (e k) 1) := by
  set σ := Equiv.Perm.decomposeFin.symm (c.succ, e) with hσ
  set k0 : Fin (M + 1) := e.symm c with hk0
  have hek0 : e k0 = c := by rw [hk0, Equiv.apply_symm_apply]
  have hσk0 : σ k0.succ = 0 := by
    rw [hσ, Equiv.Perm.decomposeFin_symm_apply_succ, hek0, Equiv.swap_apply_right]
  have hσo : ∀ j : Fin M, σ (k0.succAbove j).succ = (e (k0.succAbove j)).succ := by
    intro j
    rw [hσ, Equiv.Perm.decomposeFin_symm_apply_succ]
    apply Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero _)
    intro h
    have h' := Fin.succ_injective _ h
    rw [← hek0] at h'
    exact Fin.succAbove_ne k0 j (e.injective h')
  have hslit0 : (1 + piF (0 : Matrix (Fin (M + 1)) (Fin (M + 1 + 1)) ℂ)).det ∈ Complex.slitPlane := by
    simp [piF_zero]
  have hA := icompL (fun y => fderiv ℂ (Hc (M + 1 + 1) t) y (Matrix.single 0 c.succ 1)) phiF
    phiF_add phiF_smul 0 0 phiF_zero
    (analyticAt_fderiv_apply _ _ _ (analyticAt_determinant_power_zero _ t)) (M + 1)
    (fun k => Matrix.single k (σ k.succ) 1)
    (fun k => Matrix.single k.succ (σ k.succ) 1) (fun k => phiF_single _ _)
  rw [← hA]
  have hB : (fun y => fderiv ℂ (Hc (M + 1 + 1) t) y (Matrix.single 0 c.succ 1)) ∘ phiF
      =ᶠ[𝓝 0] fsumc t c := by
    filter_upwards [ev_piFc (M + 1)] with X hX
    exact fderiv_determinant_power_column t X hX c
  rw [(hB.iteratedFDeriv ℂ (M + 1)).eq_of_nhds]
  rw [ipeel (fsumc t c) 0 (analyticAt_fsumc t c 0 hslit0) M _ k0]
  have hD : (fun y => fderiv ℂ (fsumc t c) y (Matrix.single k0 (σ k0.succ) 1)) =ᶠ[𝓝 0]
      fun y => (-1 : ℂ) *
        ((fun z => fderiv ℂ (Hc (M + 1) t) z (Matrix.single k0 c 1)) ∘ piF) y := by
    filter_upwards [ev_piFc (M + 1)] with X hX
    have h := fderiv_fsumc t c k0 X hX
    simp only [Function.comp_apply]
    rw [hσk0]
    erw [h]
    ring
  refine (congrFun (congrArg DFunLike.coe (hD.iteratedFDeriv ℂ M).eq_of_nhds) _).trans ?_
  have hG0 : AnalyticAt ℂ (fun z => fderiv ℂ (Hc (M + 1) t) z (Matrix.single k0 c 1)) 0 :=
    analyticAt_fderiv_apply _ _ _ (analyticAt_determinant_power_zero _ t)
  have hGc : AnalyticAt ℂ
      ((fun z => fderiv ℂ (Hc (M + 1) t) z (Matrix.single k0 c 1)) ∘ piF) 0 := by
    have hcomp : ((fun z => fderiv ℂ (Hc (M + 1) t) z (Matrix.single k0 c 1)) ∘ piF) =
        (fun z => fderiv ℂ (Hc (M + 1) t) z (Matrix.single k0 c 1)) ∘ (piL (M + 1)) := by
      funext X
      simp only [Function.comp_apply, piL_apply]
    rw [hcomp]
    refine AnalyticAt.comp ?_ ((piL (M + 1)).analyticAt 0)
    rw [piL_apply, piF_zero]
    exact hG0
  refine (iconst_mul _ 0 (-1) hGc M _).trans ?_
  rw [icompL (fun z => fderiv ℂ (Hc (M + 1) t) z (Matrix.single k0 c 1)) piF
    piF_add piF_smul 0 0 piF_zero hG0 M _
    (fun k => Matrix.single (k0.succAbove k) (e (k0.succAbove k)) 1)
    (fun k => by simp only [hσo, piF_single_succ])]
  rw [neg_one_mul, ipeel (Hc (M + 1) t) 0 (analyticAt_determinant_power_zero _ t) M _ k0, hek0]
  rfl

theorem term_pc (t : ℂ) (N : ℕ) (p : Fin (N + 1)) (e : Equiv.Perm (Fin N)) :
    iteratedFDeriv ℂ (N + 1) (Hc (N + 1) t) 0
        (fun k => Matrix.single k (Equiv.Perm.decomposeFin.symm (p, e) k) 1) =
      iteratedFDeriv ℂ N (fun y => fderiv ℂ (Hc (N + 1) t) y (Matrix.single 0 p 1)) 0
        (fun k => Matrix.single k.succ (Equiv.Perm.decomposeFin.symm (p, e) k.succ) 1) := by
  rw [ipeel0 (Hc (N + 1) t) 0 (analyticAt_determinant_power_zero (N + 1) t) N]
  simp only [Equiv.Perm.decomposeFin_symm_apply_zero]
  rfl

theorem rec_stepc (t : ℂ) (N : ℕ) : detD (Hc (N + 1) t) = (t + N) * detD (Hc N t) := by
  have h0 : ∀ e : Equiv.Perm (Fin N),
      iteratedFDeriv ℂ (N + 1) (Hc (N + 1) t) 0
        (fun k => Matrix.single k (Equiv.Perm.decomposeFin.symm (0, e) k) 1) =
      t * iteratedFDeriv ℂ N (Hc N t) 0 (fun k => Matrix.single k (e k) 1) := by
    intro e
    rw [term_pc]
    simp only [Equiv.Perm.decomposeFin_symm_apply_succ, Equiv.swap_self, Equiv.refl_apply]
    exact iterated_derivative_corner_case t e
  have h1 : ∀ (c : Fin N) (e : Equiv.Perm (Fin N)),
      iteratedFDeriv ℂ (N + 1) (Hc (N + 1) t) 0
        (fun k => Matrix.single k (Equiv.Perm.decomposeFin.symm (c.succ, e) k) 1) =
      -iteratedFDeriv ℂ N (Hc N t) 0 (fun k => Matrix.single k (e k) 1) := by
    intro c e
    cases N with
    | zero => exact c.elim0
    | succ M =>
      rw [term_pc]
      exact iterated_derivative_column_case t M e c
  rw [detD_fin (N + 1) _ (analyticAt_determinant_power_zero (N + 1) t), detD_fin N _ (analyticAt_determinant_power_zero N t),
    ← Equiv.sum_comp Equiv.Perm.decomposeFin.symm, Fintype.sum_prod_type, Fin.sum_univ_succ]
  simp only [Equiv.Perm.decomposeFin.symm_sign, h0, h1, Fin.succ_ne_zero, if_true, if_false,
    Units.val_mul, Units.val_neg, Units.val_one, Int.cast_mul, Int.cast_neg, Int.cast_one,
    one_mul, neg_one_mul, mul_neg, neg_neg, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  rw [add_mul, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun e _ => by ring

theorem capelli_determinant_rising_factorial (t : ℂ) : ∀ N : ℕ, detD (Hc N t) = ∏ i ∈ Finset.range N, (t + i)
  | 0 => by
    rw [detD_fin 0 _ (analyticAt_determinant_power_zero 0 t)]
    simp [Hc, iteratedFDeriv_zero_apply]
  | N + 1 => by
    rw [rec_stepc, capelli_determinant_rising_factorial t N, Finset.prod_range_succ]
    ring

end PositivityTheory.Rg.Sw.HSt.CKC

namespace PositivityTheory.Rg.Sw.HSt

open PositivityTheory.Rg.Sw.LVs

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem kappaC : KappaC := fun N t => CKC.capelli_determinant_rising_factorial t N

theorem analyticAt_det_one_add_cpow {ι : Type} [Fintype ι] [DecidableEq ι] (t : ℂ) :
    AnalyticAt ℂ (fun T : Matrix ι ι ℂ => (1 + T).det ^ t) 0 := by
  have h1 : AnalyticAt ℂ (fun T : Matrix ι ι ℂ => (1 + T).det) 0 :=
    (LVs.analyticAt_det (1 + 0)).comp (analyticAt_const.add analyticAt_id)
  exact h1.cpow analyticAt_const (by simpa using Complex.one_mem_slitPlane)

end PositivityTheory.Rg.Sw.HSt
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.ContDiffOnInverseFirstBlock
section
noncomputable section

open Matrix Filter Topology
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.HSt.LoweringDerivative

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.HSt

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

private theorem deriv_comp_mul_exp_smul_eq_fderiv (F : M2 n → ℂ) (x W : M2 n) (hF : DifferentiableAt ℂ F x) :
    deriv (fun t : ℝ => F (x * NormedSpace.exp ((t : ℂ) • W))) 0 = fderiv ℂ F x (x * W) := by
  have hL : HasDerivAt (fun t : ℝ => x * II.cE W t) (x * W) 0 := by
    let L : M2 n →L[ℝ] M2 n := LinearMap.toContinuousLinearMap (LinearMap.mulLeft ℝ x)
    exact L.hasFDerivAt.comp_hasDerivAt (0 : ℝ) (II.cE_hasDerivAt0 W)
  have h := (hF.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt_of_eq (0 : ℝ) hL (by simp [II.cE])
  have he : (fun t : ℝ => F (x * NormedSpace.exp ((t : ℂ) • W))) = fun t => F (x * II.cE W t) := by
    funext t
    simp only [II.cE, Complex.coe_smul]
  rw [he]
  exact h.deriv

theorem rC_eq (F : M2 n → ℂ) (x Z : M2 n) (hF : DifferentiableAt ℂ F x) : rC Z F x = fderiv ℂ F x (x * Z) := by
  unfold rC
  rw [deriv_comp_mul_exp_smul_eq_fderiv F x _ hF, deriv_comp_mul_exp_smul_eq_fderiv F x _ hF, ← smul_eq_mul Complex.I, ← map_smul, ← map_add (f := _),
    ← Matrix.mul_smul, ← Matrix.mul_add, smul_smul]
  have hI : Complex.I * (1 / (2 * Complex.I)) = 1 / 2 := by
    field_simp
  rw [hI, ← smul_add, add_add_sub_cancel, ← two_smul ℂ Z, smul_smul]
  norm_num

theorem contDiffOn_inverse_first_block : ∀ i j, ContDiffOn ℂ ∞ (fun x : M2 n => ub1 x i j) {x | x.det ≠ 0} := by
  intro i j
  exact LVs.contDiffOn_inverse_first_block _ (fun x hx => isUnit_iff_ne_zero.2 hx) i j

theorem isOpen_det_ne : IsOpen {x : M2 n | x.det ≠ 0} :=
  isOpen_ne_fun (continuous_id.matrix_det) continuous_const

end PositivityTheory.Rg.Sw.HSt.LoweringDerivative
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.DetUnitOfInK
section
noncomputable section

open MeasureTheory Matrix

namespace PositivityTheory.Rg.Sw.HSt

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs

variable {n : ℕ}

theorem det_nU (H : Matrix (Fin n) (Fin n) ℂ) : (nU H).det = 1 := by
  simp [nU, Matrix.det_fromBlocks_zero₂₁]

theorem fz_twist (m : ℕ) (e : ℤ) (z : ℂ) (y : M2 n) : fz m e z y = y.det ^ e * fz m 0 z y := by
  simp [fz, mul_assoc]

theorem det_unit_of_inK {k : M2 n} (hk : InK k) : star k.det * k.det = 1 := by
  have h := congrArg Matrix.det hk.2
  rw [Matrix.det_mul, Matrix.det_conjTranspose, Matrix.det_one] at h
  exact h

theorem rhoP_twist {Kg : Type} (ι : Kg → M2 n) (hK : ∀ k, InK (ι k)) (m : ℕ) (e : ℤ) (Y : Matrix (Fin n) (Fin n) ℂ)
    (k : Kg) : rhoP ι m e Y k * (ι k).det ^ e = rhoP ι m 0 Y k := by
  unfold rhoP
  rw [fz_twist m e 0 (ι k)]
  simp only [star_mul, star_zpow₀]
  have hu : star (ι k).det * (ι k).det = 1 := det_unit_of_inK (hK k)
  have h1 : star (ι k).det ^ e * (ι k).det ^ e = 1 := by
    rw [← mul_zpow, hu, _root_.one_zpow]
  linear_combination (star ((u2 (ι k))⁻¹ * Y * u1 (ι k)).trace * star (fz m 0 0 (ι k))) * h1

theorem tOp_twist {Kg : Type} [MeasurableSpace Kg] (μ : Measure Kg) (ι : Kg → M2 n) (hK : ∀ k, InK (ι k)) (m : ℕ)
    (e : ℤ) (Y : Matrix (Fin n) (Fin n) ℂ) (ψ : (Fin n → Fin n → ℝ) → ℂ) (a b x : M2 n) (z : ℂ) :
    tOp μ ι (rhoP ι m e Y) ψ a b (fz m e z) x =
      (x.det ^ e * a.det ^ e * b.det ^ e) * tOp μ ι (rhoP ι m 0 Y) ψ a b (fz m 0 z) x := by
  unfold tOp
  rw [← integral_const_mul]
  congr 1
  funext k
  have hin : (∫ (t : Fin n → Fin n → ℝ), fz m e z (x * ι k * a * nU (herm t) * b) * ψ t)
      = (x.det ^ e * (ι k).det ^ e * a.det ^ e * b.det ^ e) *
        ∫ (t : Fin n → Fin n → ℝ), fz m 0 z (x * ι k * a * nU (herm t) * b) * ψ t := by
    rw [← integral_const_mul]
    congr 1
    funext t
    rw [fz_twist m e z, Matrix.det_mul, Matrix.det_mul, Matrix.det_mul, Matrix.det_mul, det_nU, mul_one,
      mul_zpow, mul_zpow, mul_zpow]
    ring
  rw [hin, ← rhoP_twist ι hK m e Y k]
  ring

theorem eRed : ERed := by
  intro h n m e hmn Kg _ _ _ _ _ _ μ _ ι hι hK
  obtain ⟨P, ψ, a, b, x, h1, h2, h3, h4, h5⟩ := h n m hmn Kg μ ι hι hK
  refine ⟨P, ψ, a, b, x, h1, h2, h3, h4, ?_⟩
  have hKk : ∀ k, InK (ι k) := fun k => (hK (ι k)).2 ⟨k, rfl⟩
  have hfun : (fun z : ℂ => tOp μ (⇑ι) (rhoP (⇑ι) m e P) ψ a b (fz m e z) x)
      = fun z : ℂ => (x.det ^ e * a.det ^ e * b.det ^ e) * tOp μ (⇑ι) (rhoP (⇑ι) m 0 P) ψ a b (fz m 0 z) x := by
    funext z
    exact tOp_twist μ ι hKk m e P ψ a b x z
  rw [hfun, deriv_const_mul_field']
  refine mul_ne_zero ?_ h5
  refine mul_ne_zero (mul_ne_zero ?_ ?_) ?_
  · exact zpow_ne_zero _ (isUnit_det_of_InG h4).ne_zero
  · exact zpow_ne_zero _ (isUnit_det_of_InG h2).ne_zero
  · exact zpow_ne_zero _ (isUnit_det_of_InG h3).ne_zero

end PositivityTheory.Rg.Sw.HSt
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.SecondCoordMulInner
section
noncomputable section

open MeasureTheory Matrix

namespace PositivityTheory.Rg.Sw.HSt.L3

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs

variable {m n : ℕ}

def v1 (b : M2 n) : Matrix (Fin n) (Fin n) ℂ := Complex.I • b.toBlocks₁₁ + b.toBlocks₁₂

theorem fz_zero (e : ℤ) (x : M2 n) : fz m e 0 x = x.det ^ e * (u1 x).det ^ (-(m : ℤ)) := by
  simp [fz]

theorem blocks_mul (g b : M2 n) : (g * b).toBlocks₂₁ = g.toBlocks₂₁ * b.toBlocks₁₁ + g.toBlocks₂₂ * b.toBlocks₂₁ ∧
    (g * b).toBlocks₂₂ = g.toBlocks₂₁ * b.toBlocks₁₂ + g.toBlocks₂₂ * b.toBlocks₂₂ := by
  constructor <;> ext i j <;>
    simp [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.toBlocks₂₁, Matrix.toBlocks₁₁,
      Matrix.toBlocks₁₂, Matrix.toBlocks₂₂, Matrix.add_apply]

theorem second_coord_mul_inner (g b : M2 n) : u1 (g * b) = g.toBlocks₂₁ * v1 b + g.toBlocks₂₂ * u1 b := by
  obtain ⟨h1, h2⟩ := blocks_mul g b
  simp only [u1, v1, h1, h2, Matrix.mul_add, Matrix.mul_smul, smul_add]
  abel

theorem nU_blocks (y : M2 n) (S : Matrix (Fin n) (Fin n) ℂ) :
    (y * nU S).toBlocks₂₁ = y.toBlocks₂₁ ∧ (y * nU S).toBlocks₂₂ = y.toBlocks₂₁ * S + y.toBlocks₂₂ := by
  obtain ⟨h1, h2⟩ := blocks_mul y (nU S)
  simp only [nU, Matrix.toBlocks_fromBlocks₁₁, Matrix.toBlocks_fromBlocks₁₂,
    Matrix.toBlocks_fromBlocks₂₁, Matrix.toBlocks_fromBlocks₂₂, Matrix.mul_one, Matrix.mul_zero,
    add_zero] at h1 h2
  exact ⟨h1, h2⟩

theorem det_nU (S : Matrix (Fin n) (Fin n) ℂ) : (nU S).det = 1 := by
  simp [nU]

private theorem mul_JJ_mul_conjTranspose_eq_of_inG (y : M2 n) (hy : InG y) : y * JJ n * yᴴ = JJ n := by
  have hJ : JJ n * JJ n = -1 := by
    ext (i|i) (j|j) <;> simp [JJ, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]
  have hy' : yᴴ * JJ n * y = JJ n := hy
  have h1 : (-(JJ n * yᴴ * JJ n)) * y = 1 := by
    calc (-(JJ n * yᴴ * JJ n)) * y = -(JJ n * (yᴴ * JJ n * y)) := by
          simp only [Matrix.neg_mul, Matrix.mul_assoc]
      _ = 1 := by rw [hy', hJ, neg_neg]
  have h2 : y * (-(JJ n * yᴴ * JJ n)) = 1 := mul_eq_one_comm.mp h1
  calc y * JJ n * yᴴ = y * JJ n * yᴴ * (-(JJ n * JJ n)) := by rw [hJ, neg_neg, Matrix.mul_one]
    _ = (y * (-(JJ n * yᴴ * JJ n))) * JJ n := by
      simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]
    _ = JJ n := by rw [h2, Matrix.one_mul]

theorem hermit_cd (y : M2 n) (hy : InG y) (hc : IsUnit y.toBlocks₂₁.det) :
    (y.toBlocks₂₁⁻¹ * y.toBlocks₂₂).IsHermitian := by
  have h := congrArg Matrix.toBlocks₂₂ (mul_JJ_mul_conjTranspose_eq_of_inG y hy)
  rw [← Matrix.fromBlocks_toBlocks y] at h
  simp [JJ, Matrix.fromBlocks_multiply, Matrix.fromBlocks_conjTranspose] at h
  rw [neg_add_eq_zero] at h
  have hcH : IsUnit (y.toBlocks₂₁)ᴴ.det := by
    rw [Matrix.det_conjTranspose]
    exact isUnit_star.mpr hc
  rw [Matrix.IsHermitian, Matrix.conjTranspose_mul, Matrix.conjTranspose_nonsing_inv]
  calc (y.toBlocks₂₂)ᴴ * (y.toBlocks₂₁)ᴴ⁻¹
      = (y.toBlocks₂₁)⁻¹ * (y.toBlocks₂₁ * (y.toBlocks₂₂)ᴴ) * (y.toBlocks₂₁)ᴴ⁻¹ := by
        rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hc, Matrix.one_mul]
    _ = (y.toBlocks₂₁)⁻¹ * (y.toBlocks₂₂ * (y.toBlocks₂₁)ᴴ) * (y.toBlocks₂₁)ᴴ⁻¹ := by rw [← h]
    _ = (y.toBlocks₂₁)⁻¹ * y.toBlocks₂₂ := by
        rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hcH, Matrix.mul_one]

theorem v_rel (b : M2 n) (hb : InG b) : (u1 b)ᴴ * v1 b - (v1 b)ᴴ * u1 b = (2 * Complex.I) • (1 : Matrix (Fin n) (Fin n) ℂ) := by
  have e := hb
  unfold InG at e
  rw [← Matrix.fromBlocks_toBlocks b] at e
  simp [JJ, Matrix.fromBlocks_multiply, Matrix.fromBlocks_conjTranspose] at e
  obtain ⟨e1, e2, e3, e4⟩ := e
  have key : (u1 b)ᴴ * v1 b - (v1 b)ᴴ * u1 b =
      -(-((b.toBlocks₂₁)ᴴ * b.toBlocks₁₁) + (b.toBlocks₁₁)ᴴ * b.toBlocks₂₁)
      - (-((b.toBlocks₂₂)ᴴ * b.toBlocks₁₂) + (b.toBlocks₁₂)ᴴ * b.toBlocks₂₂)
      + Complex.I • ((-((b.toBlocks₂₁)ᴴ * b.toBlocks₁₂) + (b.toBlocks₁₁)ᴴ * b.toBlocks₂₂)
        - (-((b.toBlocks₂₂)ᴴ * b.toBlocks₁₁) + (b.toBlocks₁₂)ᴴ * b.toBlocks₂₁)) := by
    simp only [u1, v1, Matrix.conjTranspose_add, Matrix.conjTranspose_smul, Matrix.add_mul,
      Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, Complex.star_def, Complex.conj_I]
    match_scalars <;>
      first | ring1 | linear_combination Complex.I_sq | linear_combination -Complex.I_sq
  rw [key, e1, e2, e3, e4]
  module

end PositivityTheory.Rg.Sw.HSt.L3
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.StepD
section
noncomputable section

open MeasureTheory Matrix
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.HSt.Cx3

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.HSt

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem stepD (j : ℕ) (p q : ℤ) {Kg : Type} [TopologicalSpace Kg] [CompactSpace Kg] [MeasurableSpace Kg]
    [BorelSpace Kg] (μ : Measure Kg) [IsFiniteMeasure μ] [IsFiniteMeasureOnCompacts μ]
    (ι : Kg → M2 n) (hι : Continuous ι) (hιG : ∀ k, InG (ι k)) (ρ : Kg → ℂ) (hρ : Continuous ρ)
    (hC : ∀ g, InG g → ∫ k, hF j p q (ι k * g) * ρ k ∂μ = 0) :
    ∀ (N : ℕ) (W : Fin N → M2 n) (g : M2 n), InG g →
      ∫ k, iteratedFDeriv ℂ N (hF j p q) (ι k * g) (fun i => ι k * g * W i) * ρ k ∂μ = 0 := by
  intro N W g hg
  set Ω : Set (M2 n) := {x | ∀ k, ι k * x ∈ Dom n} with hΩ
  have hΩo : IsOpen Ω := isOpen_domK Kg ι hι
  have hGΩ : GSet n ⊆ Ω := fun x hx k => gset_sub_dom (inG_mul (hιG k) hx)
  have hF0 : ContDiffOn ℂ ∞ (hF (n := n) j p q) (Dom n) := contDiffOn_hF j p q
  have hsm : ∀ k, ContDiffOn ℂ ∞ (fun x => hF j p q (ι k * x) * ρ k) Ω := fun k =>
    (hF0.comp (contDiff_mulLeft (ι k)).contDiffOn (fun x (hx : x ∈ Ω) => hx k)).mul contDiffOn_const
  have hH := holInt n Kg μ Ω (fun k x => hF j p q (ι k * x) * ρ k) hΩo
    (fun N => continuousOn_iteratedFDeriv_translate (hF j p q) (Dom n) isOpen_dom hF0 Kg ι hι ρ hρ N) hsm
  have hz := holZero n Ω (fun x => ∫ k, hF j p q (ι k * x) * ρ k ∂μ) hΩo hGΩ hH.1
    (fun g hg => hC g hg) N g hg
  have key := hH.2 N g (fun i => g * W i) (hGΩ hg)
  rw [hz] at key
  simp only [_root_.zero_apply] at key
  rw [key]
  refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
  have hk : ι k * g ∈ Dom n := hGΩ hg k
  show iteratedFDeriv ℂ N (hF j p q) (ι k * g) (fun i => ι k * g * W i) * ρ k =
    iteratedFDeriv ℂ N (fun x => hF j p q (ι k * x) * ρ k) g (fun i => g * W i)
  rw [iteratedFDeriv_mul_const_of (fun x => hF j p q (ι k * x)) Ω hΩo
    (hF0.comp (contDiff_mulLeft (ι k)).contDiffOn (fun x (hx : x ∈ Ω) => hx k)) (ρ k) g (hGΩ hg) N,
    iteratedFDeriv_left_mul (hF j p q) (Dom n) isOpen_dom hF0 (ι k) g hk N]
  simp only [mul_assoc]

theorem stepC (hFd : FdProps) (hDj : DjFd) (hSph : SphU) (hFz : FzHol) (m j : ℕ) (hj1 : 1 ≤ j) (hjn : j ≤ n)
    (ha1 : deriv (fun z : ℂ => (∏ i ∈ Finset.range j, ((i : ℂ) - z)) *
      (∏ i ∈ Finset.range (n - j), ((i : ℂ) - m - z))) 0 ≠ 0)
    {Kg : Type} [TopologicalSpace Kg] [CompactSpace Kg] [MeasurableSpace Kg]
    [BorelSpace Kg] (μ : Measure Kg) [IsFiniteMeasure μ] [IsFiniteMeasureOnCompacts μ]
    (ι : Kg → M2 n) (hι : Continuous ι) (hιG : ∀ k, InG (ι k)) (ρ : Kg → ℂ) (hρ : Continuous ρ)
    (hB : ∀ g, InG g → detD (fun T : Matrix (blkA (n := n) j) (blkA j) ℂ => detD (fun S : Matrix (blkB (n := n) j) (blkB j) ℂ =>
      ∫ k, Fd m (ι k * (g * mX 1 (embOn (blkA j) T) (embOn (blkB j) S) 1)) * ρ k ∂μ)) = 0) :
    ∀ g, InG g → ∫ k, hF j (m : ℤ) 0 (ι k * g) * ρ k ∂μ = 0 := by
  intro g hg
  have hGZ : GSet n ⊆ DomZ n := (hFz n m 0).2.1
  have hkg : ∀ k, ι k * g ∈ DomZ n := fun k => hGZ (inG_mul (hιG k) hg)
  have hFdc : ContDiffOn ℂ ⊤ (Fd (n := n) m) (DomZ n) := (hFd n m).1
  have hS := hSph n (Fd m) (DomZ n) (hFz n m 0).1 hFdc μ ι hι ρ hρ (LQ (blkA j)) (LR (blkB j))
    (fun M x T => by rw [LQ_apply, LQ_apply, mul_assoc]) (fun M x S => by rw [LR_apply, LR_apply, mul_assoc]) g hkg
  have e1 : (fun T : Matrix (blkA (n := n) j) (blkA j) ℂ => detD (fun S : Matrix (blkB (n := n) j) (blkB j) ℂ =>
      ∫ k, Fd m (ι k * (g * mX 1 (embOn (blkA j) T) (embOn (blkB j) S) 1)) * ρ k ∂μ)) =
      fun T => detD (fun S => ∫ k, Fd m (ι k * (g + LQ (blkA j) g T + LR (blkB j) g S)) * ρ k ∂μ) := by
    funext T; congr 1; funext S
    rw [mul_mX, LQ_apply, LR_apply]
  have e2 : ∀ k, detD (fun T : Matrix (blkA (n := n) j) (blkA j) ℂ => detD (fun S : Matrix (blkB (n := n) j) (blkB j) ℂ =>
      Fd m (ι k * g + LQ (blkA j) (ι k * g) T + LR (blkB j) (ι k * g) S))) * ρ k =
      deriv (fun z : ℂ => (∏ i ∈ Finset.range j, ((i : ℂ) - z)) *
        (∏ i ∈ Finset.range (n - j), ((i : ℂ) - m - z))) 0 * (hF j (m : ℤ) 0 (ι k * g) * ρ k) := by
    intro k
    have r : (fun T : Matrix (blkA (n := n) j) (blkA j) ℂ => detD (fun S : Matrix (blkB (n := n) j) (blkB j) ℂ =>
        Fd m (ι k * g + LQ (blkA j) (ι k * g) T + LR (blkB j) (ι k * g) S))) =
        fun T => detD (fun S => Fd m ((ι k * g) * mX 1 (embOn (blkA j) T) (embOn (blkB j) S) 1)) := by
      funext T; congr 1; funext S
      rw [mul_mX, LQ_apply, LR_apply]
    rw [r, hDj n m j (ι k * g) hj1 hjn (hkg k)]
    ring
  have h := hB g hg
  rw [e1, hS, integral_congr_ae (Filter.Eventually.of_forall e2), integral_const_mul] at h
  exact (mul_eq_zero.1 h).resolve_left ha1

end PositivityTheory.Rg.Sw.HSt.Cx3
end
end

