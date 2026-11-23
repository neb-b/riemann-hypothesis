module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.Bundle0006
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IntegralConjInnerMulInnerOfIsEmptyEquiv
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.DerivProdRangeSubMulProdNeZero
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.Bundle0001
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.ConvPhi
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.MapsToUpToSign

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.AbsArgLtPi
section
noncomputable section

open Matrix Filter Topology Set

namespace PositivityTheory.Rg.Sw.HSt

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs

variable {n : ℕ}

theorem abs_arg_lt_pi {P : ℂ} (hP : P ∈ Complex.slitPlane) : |P.arg| < Real.pi := by
  rw [abs_lt]
  exact ⟨Complex.neg_pi_lt_arg P, lt_of_le_of_ne (Complex.arg_le_pi P) (Complex.slitPlane_arg_ne_pi hP)⟩

theorem cpow_split {P a b : ℂ} (hP : P ∈ Complex.slitPlane) (ha : a ≠ 0) (hb : b ≠ 0)
    (ha' : |a.arg| < (Real.pi - |P.arg|) / 2) (hb' : |b.arg| < (Real.pi - |P.arg|) / 2) (w : ℂ) :
    (P * a * b) ^ w = P ^ w * a ^ w * b ^ w := by
  have hP0 : P ≠ 0 := Complex.slitPlane_ne_zero hP
  have hPpi := abs_arg_lt_pi hP
  have hpos : 0 ≤ Real.pi - |P.arg| := by linarith
  have h1 : P.arg + a.arg ∈ Ioc (-Real.pi) Real.pi := by
    have := abs_add_le P.arg a.arg
    constructor
    · linarith [neg_abs_le (P.arg + a.arg)]
    · linarith [le_abs_self (P.arg + a.arg)]
  have hPa : P * a ≠ 0 := mul_ne_zero hP0 ha
  have harg : (P * a).arg = P.arg + a.arg := by
    have := congrArg Complex.im (Complex.log_mul hP0 ha h1)
    simpa [Complex.log_im] using this
  have h2 : (P * a).arg + b.arg ∈ Ioc (-Real.pi) Real.pi := by
    rw [harg]
    have := abs_add_le (P.arg + a.arg) b.arg
    have := abs_add_le P.arg a.arg
    constructor
    · linarith [neg_abs_le (P.arg + a.arg + b.arg)]
    · linarith [le_abs_self (P.arg + a.arg + b.arg)]
  rw [Complex.cpow_def_of_ne_zero (mul_ne_zero hPa hb), Complex.log_mul hPa hb h2, Complex.log_mul hP0 ha h1,
    Complex.cpow_def_of_ne_zero hP0, Complex.cpow_def_of_ne_zero ha, Complex.cpow_def_of_ne_zero hb,
    ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  ring

theorem detD_congr {ι : Type} [Fintype ι] [DecidableEq ι] {F G : Matrix ι ι ℂ → ℂ} (h : F =ᶠ[𝓝 0] G) :
    detD F = detD G := by
  unfold detD
  rw [(h.iteratedFDeriv ℂ (Fintype.card ι)).eq_of_nhds]

theorem ev_small {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {c : E → ℂ} (hc : ContinuousAt c 0) (h0 : c 0 = 1)
    {δ : ℝ} (hδ : 0 < δ) : ∀ᶠ T in 𝓝 (0 : E), c T ≠ 0 ∧ |(c T).arg| < δ := by
  have hne : ∀ᶠ T in 𝓝 (0 : E), c T ≠ 0 := hc.eventually_ne (by rw [h0]; exact one_ne_zero)
  have hcont : ContinuousAt (fun T => (c T).arg) 0 :=
    ContinuousAt.comp (f := c) (g := Complex.arg) (Complex.continuousAt_arg (by rw [h0]; exact Complex.one_mem_slitPlane)) hc
  have ht : Tendsto (fun T => (c T).arg) (𝓝 0) (𝓝 0) := by
    have := hcont.tendsto
    simpa [h0, Complex.arg_one] using this
  filter_upwards [hne, ht (Metric.ball_mem_nhds 0 hδ)] with T h1 h2
  refine ⟨h1, ?_⟩
  simpa [Metric.mem_ball, Real.dist_eq] using h2

private theorem mul_toBlocks₂₁' (A B : M2 n) :
    (A * B).toBlocks₂₁ = A.toBlocks₂₁ * B.toBlocks₁₁ + A.toBlocks₂₂ * B.toBlocks₂₁ := by
  ext i j
  simp [Matrix.toBlocks₂₁, Matrix.toBlocks₁₁, Matrix.toBlocks₂₂, Matrix.mul_apply, Fintype.sum_sum_type]

private theorem mul_toBlocks₂₂ (A B : M2 n) :
    (A * B).toBlocks₂₂ = A.toBlocks₂₁ * B.toBlocks₁₂ + A.toBlocks₂₂ * B.toBlocks₂₂ := by
  ext i j
  simp [Matrix.toBlocks₂₁, Matrix.toBlocks₁₂, Matrix.toBlocks₂₂, Matrix.mul_apply, Fintype.sum_sum_type]

private theorem u1_mul_mX_one_eq_add (x : M2 n) (Q R : Matrix (Fin n) (Fin n) ℂ) :
    u1 (x * mX 1 Q R 1) = u1 x + u2 x * R := by
  have hinv : (Cm n)⁻¹ = Cmi n := Matrix.inv_eq_left_inv cmi_mul_cm
  have hxc21 : (x * Cm n).toBlocks₂₁ = u1 x := by
    rw [mul_toBlocks₂₁', Cm, toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₂₁, u1]
    simp [Matrix.mul_smul]
  have hxc22 : (x * Cm n).toBlocks₂₂ = u2 x := by
    rw [mul_toBlocks₂₂, Cm, toBlocks_fromBlocks₁₂, toBlocks_fromBlocks₂₂, u2]
    simp [Matrix.mul_smul]
  rw [mX, hinv, show x * (Cm n * fromBlocks 1 Q R 1 * Cmi n) = (x * Cm n * fromBlocks 1 Q R 1) * Cmi n by
    simp only [Matrix.mul_assoc], first_cayley_block_mul_inverse_cayley, mul_toBlocks₂₁', toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₂₁,
    Matrix.mul_one, hxc21, hxc22]

theorem fz_mX {m : ℕ} {e : ℤ} {z : ℂ} {j : ℕ} {x : M2 n} (hx : x ∈ DomZ n)
    (T : Matrix (blkA (n := n) j) (blkA j) ℂ) (S : Matrix (blkB (n := n) j) (blkB j) ℂ)
    (h1 : (1 + subOn (blkB j) (wM x)⁻¹ * S).det ≠ 0) (h2 : (1 + subOn (blkA j) (wM x) * T).det ≠ 0)
    (h1' : |((1 + subOn (blkB j) (wM x)⁻¹ * S).det).arg| < (Real.pi - |((u1 x).det * (ub1 x).det).arg|) / 2)
    (h2' : |((1 + subOn (blkA j) (wM x) * T).det).arg| < (Real.pi - |((u1 x).det * (ub1 x).det).arg|) / 2) :
    fz m e z (x * mX 1 (embOn (blkA j) T) (embOn (blkB j) S) 1) =
      (fz m e z x * (1 + subOn (blkA j) (wM x) * T).det ^ (-z)) *
        (1 + subOn (blkB j) (wM x)⁻¹ * S).det ^ ((-(m : ℂ)) - z) := by
  obtain ⟨hD, hP⟩ := hx
  have hD' := hD
  obtain ⟨hdet, hu1, hu2, -⟩ := hD'
  obtain ⟨hQR, hRQ⟩ := embOn_mul_embOn_compl j T S
  have hdetM : (x * mX 1 (embOn (blkA j) T) (embOn (blkB j) S) 1).det = x.det := by
    rw [Matrix.det_mul, det_mX_one _ _ hRQ, mul_one]
  have hub : (ub1 (x * mX 1 (embOn (blkA j) T) (embOn (blkB j) S) 1)).det =
      (1 + subOn (blkA j) (wM x) * T).det * (ub1 x).det := by
    rw [inverse_first_block_mul_unipotent_domain x hD _ _ hQR hRQ, Matrix.det_mul, det_one_add_mul_comm, det_one_add_mul_embOn]
  have hw : (wM x)⁻¹ = (u1 x)⁻¹ * u2 x := by
    rw [wM, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ (isUnit_iff_ne_zero.mpr hu2)]
  have hu : (u1 (x * mX 1 (embOn (blkA j) T) (embOn (blkB j) S) 1)).det =
      (u1 x).det * (1 + subOn (blkB j) (wM x)⁻¹ * S).det := by
    rw [u1_mul_mX_one_eq_add, ← det_one_add_mul_embOn, ← Matrix.det_mul]
    congr 1
    rw [hw, Matrix.mul_add, Matrix.mul_one, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hu1), Matrix.one_mul]
  unfold fz
  rw [hdetM, hu, hub,
    show (u1 x).det * (1 + subOn (blkB j) (wM x)⁻¹ * S).det * ((1 + subOn (blkA j) (wM x) * T).det * (ub1 x).det) =
      (u1 x).det * (ub1 x).det * (1 + subOn (blkA j) (wM x) * T).det * (1 + subOn (blkB j) (wM x)⁻¹ * S).det by ring,
    cpow_split hP h2 h1 h2' h1' (-z), mul_zpow, sub_eq_add_neg, Complex.cpow_add _ _ h1,
    show (-(m : ℂ)) = ((-(m : ℤ) : ℤ) : ℂ) by push_cast; ring, Complex.cpow_intCast]
  ring

private theorem detD_det_one_add_mul_rpow_eq {ι : Type} [Fintype ι] [DecidableEq ι] (W : Matrix ι ι ℂ) (t : ℂ) :
    (detD fun S : Matrix ι ι ℂ => (1 + W * S).det ^ t) =
      W.det * ∏ i ∈ Finset.range (Fintype.card ι), (t + (i : ℂ)) := by
  have hF : AnalyticAt ℂ (fun S : Matrix ι ι ℂ => (1 + S).det ^ t) 0 := analyticAt_det_one_add_cpow t
  have h := CEq.equivar_thm ι (fun S : Matrix ι ι ℂ => (1 + S).det ^ t) W hF
  beta_reduce at h
  rw [h]
  congr 1
  have hG : AnalyticAt ℂ (fun S : Matrix (Fin (Fintype.card ι)) (Fin (Fintype.card ι)) ℂ => (1 + S).det ^ t) 0 :=
    analyticAt_det_one_add_cpow t
  have hr := CEq.reindex_thm ι (Fin (Fintype.card ι)) (Fintype.equivFin ι) _ hG
  beta_reduce at hr
  rw [← kappaC (Fintype.card ι) t, ← hr]
  congr 1
  funext S
  have hS : (1 : Matrix (Fin (Fintype.card ι)) (Fin (Fintype.card ι)) ℂ) +
      Matrix.reindex (Fintype.equivFin ι) (Fintype.equivFin ι) S =
      Matrix.reindex (Fintype.equivFin ι) (Fintype.equivFin ι) (1 + S) := by
    ext a b
    simp [Matrix.reindex_apply, Matrix.one_apply]
  rw [hS, Matrix.det_reindex_self]

theorem djZ : DjZ := by
  intro n m e j z x hj hx
  have hx' := hx
  obtain ⟨hD, hP⟩ := hx'
  have hδ : 0 < (Real.pi - |((u1 x).det * (ub1 x).det).arg|) / 2 := by
    have := abs_arg_lt_pi hP
    linarith
  have hcA : ∀ᶠ T in 𝓝 (0 : Matrix (blkA (n := n) j) (blkA j) ℂ),
      (1 + subOn (blkA j) (wM x) * T).det ≠ 0 ∧
        |((1 + subOn (blkA j) (wM x) * T).det).arg| < (Real.pi - |((u1 x).det * (ub1 x).det).arg|) / 2 :=
    ev_small (c := fun T => (1 + subOn (blkA j) (wM x) * T).det)
      ((continuous_const.add (continuous_const.matrix_mul continuous_id)).matrix_det.continuousAt)
      (by simp) hδ
  have hcB : ∀ᶠ S in 𝓝 (0 : Matrix (blkB (n := n) j) (blkB j) ℂ),
      (1 + subOn (blkB j) (wM x)⁻¹ * S).det ≠ 0 ∧
        |((1 + subOn (blkB j) (wM x)⁻¹ * S).det).arg| < (Real.pi - |((u1 x).det * (ub1 x).det).arg|) / 2 :=
    ev_small (c := fun S => (1 + subOn (blkB j) (wM x)⁻¹ * S).det)
      ((continuous_const.add (continuous_const.matrix_mul continuous_id)).matrix_det.continuousAt)
      (by simp) hδ
  have hinner : ∀ T : Matrix (blkA (n := n) j) (blkA j) ℂ,
      ((1 + subOn (blkA j) (wM x) * T).det ≠ 0 ∧
        |((1 + subOn (blkA j) (wM x) * T).det).arg| < (Real.pi - |((u1 x).det * (ub1 x).det).arg|) / 2) →
      (detD fun S : Matrix (blkB (n := n) j) (blkB j) ℂ =>
          fz m e z (x * mX 1 (embOn (blkA j) T) (embOn (blkB j) S) 1)) =
        (fz m e z x * (1 + subOn (blkA j) (wM x) * T).det ^ (-z)) *
          ((subOn (blkB j) (wM x)⁻¹).det *
            ∏ i ∈ Finset.range (Fintype.card (blkB (n := n) j)), ((-(m : ℂ)) - z + (i : ℂ))) := by
    intro T hT
    rw [PositivityTheory.Rg.Sw.HSt.detD_congr (G := fun S : Matrix (blkB (n := n) j) (blkB j) ℂ =>
        (fz m e z x * (1 + subOn (blkA j) (wM x) * T).det ^ (-z)) *
          (1 + subOn (blkB j) (wM x)⁻¹ * S).det ^ ((-(m : ℂ)) - z)) ?_,
      detD_const_mul, detD_det_one_add_mul_rpow_eq]
    filter_upwards [hcB] with S hS
    exact fz_mX hx T S hS.1 hT.1 hS.2 hT.2
  rw [PositivityTheory.Rg.Sw.HSt.detD_congr (G := fun T : Matrix (blkA (n := n) j) (blkA j) ℂ =>
      (fz m e z x * ((subOn (blkB j) (wM x)⁻¹).det *
        ∏ i ∈ Finset.range (Fintype.card (blkB (n := n) j)), ((-(m : ℂ)) - z + (i : ℂ)))) *
        (1 + subOn (blkA j) (wM x) * T).det ^ (-z)) ?_]
  · rw [detD_const_mul, detD_det_one_add_mul_rpow_eq, card_blkA hj, card_blkB hj, minorOn_eq, minorOn_eq]
    have e1 : ∏ i ∈ Finset.range j, (-z + (i : ℂ)) = ∏ i ∈ Finset.range j, ((i : ℂ) - z) :=
      Finset.prod_congr rfl (fun i _ => by ring)
    have e2 : ∏ i ∈ Finset.range (n - j), ((-(m : ℂ)) - z + (i : ℂ)) =
        ∏ i ∈ Finset.range (n - j), ((i : ℂ) - m - z) :=
      Finset.prod_congr rfl (fun i _ => by ring)
    rw [e1, e2]
    ring
  · filter_upwards [hcA] with T hT
    rw [hinner T hT]
    ring

end PositivityTheory.Rg.Sw.HSt
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.CanonicalPsiNeZeroOfPathBasis
section
noncomputable section

open MeasureTheory Matrix
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.HSt

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem isOpen_setK {U : Set (M2 n)} (hU : IsOpen U) (Kg : Type) [TopologicalSpace Kg] [CompactSpace Kg]
    (ι : Kg → M2 n) (hι : Continuous ι) : IsOpen {x : M2 n | ∀ k, ι k * x ∈ U} := by
  have hc : Continuous fun p : Kg × M2 n => ι p.1 * p.2 :=
    (hι.comp continuous_fst).mul continuous_snd
  have hcl : IsClosed {p : Kg × M2 n | ι p.1 * p.2 ∉ U} := (hU.preimage hc).isClosed_compl
  have himg := isClosedMap_snd_of_compactSpace (X := Kg) (Y := M2 n) _ hcl
  have heq : {x : M2 n | ∀ k, ι k * x ∈ U} = (Prod.snd '' {p : Kg × M2 n | ι p.1 * p.2 ∉ U})ᶜ := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_compl_iff, Set.mem_image, Prod.exists, exists_eq_right, not_exists, not_not]
  rw [heq]
  exact himg.isOpen_compl

private theorem u1_eq_toBlocks₂₁_mul_Cm (y : M2 n) : u1 y = toBlocks₂₁ (y * Cm n) := by
  rw [← fromBlocks_toBlocks y]
  ext i j
  simp [Cm, fromBlocks_multiply, u1, toBlocks₂₁, toBlocks₂₂]

private theorem ub1_eq_toBlocks₁₁_fromBlocks_mul_inv (y : M2 n) :
    ub1 y = toBlocks₁₁ (fromBlocks 1 (Complex.I • 1) 0 0 * y⁻¹) := by
  rw [ub1]
  conv_rhs => rw [← fromBlocks_toBlocks y⁻¹]
  simp [fromBlocks_multiply]

private theorem fromBlocks_I_mul_Cm_mul_fromBlocks_diag (A B : Matrix (Fin n) (Fin n) ℂ) :
    fromBlocks (1 : Matrix (Fin n) (Fin n) ℂ) (Complex.I • 1) 0 0 * Cm n * fromBlocks A 0 0 B =
      fromBlocks A 0 0 1 * (fromBlocks (1 : Matrix (Fin n) (Fin n) ℂ) (Complex.I • 1) 0 0 * Cm n) := by
  have h : fromBlocks (1 : Matrix (Fin n) (Fin n) ℂ) (Complex.I • 1) 0 0 * Cm n =
      fromBlocks ((2 * Complex.I) • 1) 0 0 0 := by
    simp only [Cm, fromBlocks_multiply]
    congr 1 <;> ext i j <;> simp [Matrix.one_apply] <;> split_ifs <;> ring_nf <;> simp
  rw [h, fromBlocks_multiply, fromBlocks_multiply]
  simp

private theorem det_one_add_of_support_blkA_blkB (j : ℕ) (P' : Matrix (Fin n) (Fin n) ℂ)
    (hP : ∀ a b, P' a b ≠ 0 → a ∈ blkA j ∧ b ∈ blkB j) : det (1 + P') = 1 := by
  have hd : ∀ a, P' a a = 0 := by
    intro a
    by_contra h
    obtain ⟨h1, h2⟩ := hP a a h
    simp [blkB] at h2
    exact h2 h1
  rw [Matrix.det_of_upperTriangular]
  · simp [hd]
  · intro a b hab
    have hab' : (b : ℕ) < a := hab
    have hne : a ≠ b := fun h => by subst h; omega
    simp only [Matrix.add_apply, Matrix.one_apply, hne, if_false, zero_add]
    by_contra h
    obtain ⟨h1, h2⟩ := hP a b h
    simp [blkA, blkB] at h1 h2
    omega

private theorem det_one_add_of_support_blkB_blkA (j : ℕ) (S' : Matrix (Fin n) (Fin n) ℂ)
    (hS : ∀ a b, S' a b ≠ 0 → a ∈ blkB j ∧ b ∈ blkA j) : det (1 + S') = 1 := by
  have hd : ∀ a, S' a a = 0 := by
    intro a
    by_contra h
    obtain ⟨h1, h2⟩ := hS a a h
    simp [blkB] at h1
    exact h1 h2
  rw [Matrix.det_of_lowerTriangular]
  · simp [hd]
  · intro a b hab
    have hab' : (a : ℕ) < b := hab
    have hne : a ≠ b := fun h => by subst h; omega
    simp only [Matrix.add_apply, Matrix.one_apply, hne, if_false, zero_add]
    by_contra h
    obtain ⟨h1, h2⟩ := hS a b h
    simp [blkA, blkB] at h1 h2
    omega

theorem Fd_kpart (m j : ℕ) (x : M2 n) (hx : x ∈ Dom n)
    (P' S' : Matrix (Fin n) (Fin n) ℂ) (hP : ∀ a b, P' a b ≠ 0 → a ∈ blkA j ∧ b ∈ blkB j)
    (hS : ∀ a b, S' a b ≠ 0 → a ∈ blkB j ∧ b ∈ blkA j) : Fd m (x * mX (1 + P') 0 0 (1 + S')) = Fd m x := by
  have hPd : det (1 + P') = 1 := det_one_add_of_support_blkA_blkB j P' hP
  have hSd : det (1 + S') = 1 := det_one_add_of_support_blkB_blkA j S' hS
  have hPu : IsUnit (det (1 + P')) := by rw [hPd]; exact isUnit_one
  have hSu : IsUnit (det (1 + S')) := by rw [hSd]; exact isUnit_one
  have hCi : (Cm n)⁻¹ = Cmi n := Matrix.inv_eq_left_inv cmi_mul_cm
  have hCii : (Cmi n)⁻¹ = Cm n := Matrix.inv_eq_right_inv cmi_mul_cm
  have hCC : Cm n * Cmi n = 1 := mul_eq_one_comm.mp cmi_mul_cm
  have hg : mX (1 + P') 0 0 (1 + S') = Cm n * fromBlocks (1 + P') 0 0 (1 + S') * Cmi n := by
    rw [mX, hCi]
  have hDinv : (fromBlocks (1 + P') 0 0 (1 + S'))⁻¹ = fromBlocks (1 + P')⁻¹ 0 0 (1 + S')⁻¹ := by
    apply Matrix.inv_eq_left_inv
    rw [fromBlocks_multiply]
    simp [Matrix.nonsing_inv_mul _ hPu, Matrix.nonsing_inv_mul _ hSu]
  have hu : u1 (x * mX (1 + P') 0 0 (1 + S')) = u1 x * (1 + P') := by
    rw [u1_eq_toBlocks₂₁_mul_Cm, u1_eq_toBlocks₂₁_mul_Cm x, hg]
    have h : x * (Cm n * fromBlocks (1 + P') 0 0 (1 + S') * Cmi n) * Cm n =
        (x * Cm n) * fromBlocks (1 + P') 0 0 (1 + S') := by
      simp only [Matrix.mul_assoc, cmi_mul_cm, Matrix.mul_one]
    rw [h]
    conv_lhs => rw [← fromBlocks_toBlocks (x * Cm n)]
    rw [fromBlocks_multiply]
    simp
  have hub : ub1 (x * mX (1 + P') 0 0 (1 + S')) = (1 + P')⁻¹ * ub1 x := by
    rw [ub1_eq_toBlocks₁₁_fromBlocks_mul_inv, ub1_eq_toBlocks₁₁_fromBlocks_mul_inv x, hg, Matrix.mul_inv_rev, Matrix.mul_inv_rev,
      Matrix.mul_inv_rev, hCii, hDinv, hCi]
    have h : fromBlocks (1 : Matrix (Fin n) (Fin n) ℂ) (Complex.I • 1) 0 0 *
        (Cm n * (fromBlocks (1 + P')⁻¹ 0 0 (1 + S')⁻¹ * Cmi n) * x⁻¹) =
        fromBlocks (1 + P')⁻¹ 0 0 1 * (fromBlocks (1 : Matrix (Fin n) (Fin n) ℂ) (Complex.I • 1) 0 0 * x⁻¹) := by
      have h3 := fromBlocks_I_mul_Cm_mul_fromBlocks_diag (n := n) (1 + P')⁻¹ (1 + S')⁻¹
      calc _ = (fromBlocks (1 : Matrix (Fin n) (Fin n) ℂ) (Complex.I • 1) 0 0 * Cm n *
              fromBlocks (1 + P')⁻¹ 0 0 (1 + S')⁻¹) * Cmi n * x⁻¹ := by
            simp only [Matrix.mul_assoc]
        _ = _ := by
            rw [h3]
            simp only [Matrix.mul_assoc, hCC, Matrix.one_mul]
    rw [h]
    conv_lhs => rw [← fromBlocks_toBlocks (fromBlocks (1 : Matrix (Fin n) (Fin n) ℂ) (Complex.I • 1) 0 0 * x⁻¹)]
    rw [fromBlocks_multiply]
    simp
  unfold Fd
  congr 1
  funext z
  unfold fz
  rw [hu, hub, det_mul, det_mul, det_mul, hPd, Matrix.det_nonsing_inv, hPd]
  simp

private theorem u2_eq_toBlocks₂₂_mul_Cm (y : M2 n) : u2 y = toBlocks₂₂ (y * Cm n) := by
  rw [← fromBlocks_toBlocks y]
  ext i j
  simp [Cm, fromBlocks_multiply, u2, toBlocks₂₁, toBlocks₂₂]

theorem fderiv_fV_R (m : ℕ) (x : M2 n) (hx : x ∈ Dom n) (a0 b0 : Fin n) :
    fderiv ℂ (fV (n := n) (m : ℤ) 0) x (x * WD 0 (Matrix.single a0 b0 1)) =
      ((m : ℂ) - n) * ((u1 x)⁻¹ * u2 x) b0 a0 * fV (m : ℤ) 0 x := by
  set E : Matrix (Fin n) (Fin n) ℂ := Matrix.single a0 b0 1 with hE
  obtain ⟨hdx, hd1, hd2, hdb⟩ := hx
  have hCi : (Cm n)⁻¹ = Cmi n := Matrix.inv_eq_left_inv cmi_mul_cm
  have hCC : Cm n * Cmi n = 1 := mul_eq_one_comm.mp cmi_mul_cm
  have hline : ∀ t : ℂ, x + t • (x * WD 0 E) = x * mX 1 0 (t • E) 1 := by
    intro t
    have h : mX 1 0 (t • E) 1 = 1 + t • WD 0 E := by
      simp only [mX, WD, hCi]
      have h' : (fromBlocks (1 : Matrix (Fin n) (Fin n) ℂ) 0 (t • E) 1 : M2 n) =
          1 + t • (fromBlocks 0 0 E 0 : M2 n) := by
        rw [← fromBlocks_one, fromBlocks_smul, fromBlocks_add]
        simp
      rw [h', Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hCC, Matrix.mul_smul, Matrix.smul_mul]
    rw [h, Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul]
  have hu1 : ∀ t : ℂ, u1 (x * mX 1 0 (t • E) 1) = u1 x + t • (u2 x * E) := by
    intro t
    rw [u1_eq_toBlocks₂₁_mul_Cm, u1_eq_toBlocks₂₁_mul_Cm x, u2_eq_toBlocks₂₂_mul_Cm x, mX, hCi]
    have h : x * (Cm n * fromBlocks 1 0 (t • E) 1 * Cmi n) * Cm n =
        (x * Cm n) * fromBlocks 1 0 (t • E) 1 := by
      simp only [Matrix.mul_assoc, cmi_mul_cm, Matrix.mul_one]
    rw [h]
    conv_lhs => rw [← fromBlocks_toBlocks (x * Cm n)]
    rw [fromBlocks_multiply]
    simp [Matrix.mul_smul]
  have hub : ∀ t : ℂ, ub1 (x * mX 1 0 (t • E) 1) = ub1 x := by
    intro t
    rw [inverse_first_block_mul_unipotent_domain x ⟨hdx, hd1, hd2, hdb⟩ 0 (t • E) (by simp) (by simp)]
    simp
  have hg : (fun t : ℂ => fV (n := n) (m : ℤ) 0 (x + t • (x * WD 0 E))) =
      fun t : ℂ => (u1 x + t • (u2 x * E)).det ^ ((m : ℤ) - n) * (ub1 x).det ^ (-(n : ℤ)) := by
    funext t
    rw [hline, fV, hu1, hub]
    simp
  have hdiff : DifferentiableAt ℂ (fV (n := n) (m : ℤ) 0) x :=
    ((contDiffOn_fV (m : ℤ) 0).contDiffAt (isOpen_dom.mem_nhds ⟨hdx, hd1, hd2, hdb⟩)).differentiableAt
      (by simp)
  have hL := ((hasDerivAt_id (0 : ℂ)).smul_const (x * WD 0 E)).const_add x
  simp only [id, one_smul] at hL
  have h1 := hdiff.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℂ) hL (by simp)
  have hdet := hasDerivAt_det_add (u1 x) (u2 x * E) (isUnit_iff_ne_zero.mpr hd1)
  have h2 := ((hasDerivAt_zpow ((m : ℤ) - n) ((u1 x + (0 : ℂ) • (u2 x * E)).det)
    (Or.inl (by simpa using hd1))).comp (0 : ℂ) hdet).mul_const ((ub1 x).det ^ (-(n : ℤ)))
  have h1' : HasDerivAt (fun t : ℂ => fV (n := n) (m : ℤ) 0 (x + t • (x * WD 0 E)))
      (fderiv ℂ (fV (n := n) (m : ℤ) 0) x (x * WD 0 E)) 0 := h1
  rw [hg] at h1'
  rw [h1'.unique h2]
  simp only [zero_smul, add_zero]
  rw [← Matrix.mul_assoc, hE, trace_mul_single, fV, zpow_sub_one₀ hd1]
  simp only [zpow_zero, mul_one, MulOpposite.op_one, one_smul, Int.cast_sub, Int.cast_natCast]
  field_simp

end PositivityTheory.Rg.Sw.HSt
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.IsCompactKSet
section
noncomputable section

open MeasureTheory Matrix Set Filter Topology

namespace PositivityTheory.Rg.Sw.HSt.Conv

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.AbsSt PositivityTheory.Rg.Sw.HSt.GRH

variable {n : ℕ}

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem continuous_kR : Continuous (fun k : KR n => mR (k : GR n)) := PositivityTheory.Rg.Sw.HSt.GRH.continuous_mR.comp continuous_subtype_val

def kSet (S : Set (M2 n)) : Set (M2 n) := (fun p : KR n × M2 n => mR (p.1 : GR n) * p.2) '' (univ ×ˢ S)

theorem isCompact_kSet {S : Set (M2 n)} (hS : IsCompact S) : IsCompact (kSet S) :=
  (isCompact_univ.prod hS).image ((continuous_kR.comp continuous_fst).mul continuous_snd)

theorem tw_eq_zero (m : ℕ) (e : ℤ) (μK : Measure (KR n)) (β : M2 n → ℝ) {X : M2 n} (hX : X ∉ kSet (tsupport β)) :
    tw m e μK β X = 0 := by
  unfold tw
  have hz : ∀ k : KR n, β ((mR (k : GR n))ᴴ * X) = 0 := by
    intro k
    by_contra h
    apply hX
    have hk : InK (mR (k : GR n)) := k.2
    have hkk : mR (k : GR n) * (mR (k : GR n))ᴴ = 1 := mul_eq_one_comm.mp hk.2
    refine ⟨(k, (mR (k : GR n))ᴴ * X), ⟨mem_univ _, subset_tsupport _ h⟩, ?_⟩
    simp only
    rw [← Matrix.mul_assoc, hkk, Matrix.one_mul]
  simp [hz]

theorem tw_support (m : ℕ) (e : ℤ) (μK : Measure (KR n)) {β : M2 n → ℝ} (hβ : HasCompactSupport β) :
    HasCompactSupport (tw m e μK β) := by
  refine HasCompactSupport.intro (isCompact_kSet hβ) fun X hX => tw_eq_zero m e μK β hX

end PositivityTheory.Rg.Sw.HSt.Conv
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.VanishInv
section
noncomputable section

open MeasureTheory Matrix

namespace PositivityTheory.Rg.Sw.HSt.L3

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs

variable {m n : ℕ}

theorem vanish_inv (hmn : m < n) (e : ℤ) (y b : M2 n) (hy : InG y) (hb : InG b) (hc : IsUnit y.toBlocks₂₁.det)
    (ψ : (Fin n → Fin n → ℝ) → ℂ) (hψ : IsSingTest ψ) :
    ∫ s, fz m e 0 (y * nU (herm s) * b) * ψ s = 0 := by
  obtain ⟨R, H0, κ, hR, hH0, hκ, hf⟩ := factor y b hy hb hc
  have key : ∀ s, fz m e 0 (y * nU (herm s) * b) * ψ s =
      ((y.det * b.det) ^ e * κ ^ (-(m : ℤ))) *
        (ψ s * (R * Rᴴ - Complex.I • (H0 + herm s)).det⁻¹ ^ m) := by
    intro s
    rw [fz_zero, hf, Matrix.det_mul, Matrix.det_mul, det_nU, mul_one]
    simp only [mul_zpow, _root_.zpow_neg, zpow_natCast, inv_pow]
    ring
  simp_rw [key]
  rw [MeasureTheory.integral_const_mul, core2 hmn R hR H0 hH0 ψ hψ, mul_zero]

end PositivityTheory.Rg.Sw.HSt.L3
end
end

