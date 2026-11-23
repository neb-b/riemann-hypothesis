module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0009
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0015

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.BasePsiLeviLowerBound
section
namespace ReciprocityTheory.ChartRestriction.G.AR.Up

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def IsInvFn (X : Data E r) (ph : Frame X.Ψ r → ℝ) : Prop :=
  ∀ γ ∈ X.Γ, ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, ph (lact γ (rmul x b)) = ph x

def leviM (X : Data E r) (g : Frame X.Ψ r → ℝ) (x0 : Frame X.Ψ r) (z : V (nd X))
    (ξ : Fin (nd X) → ℂ) : ℝ :=
  (leviV (nd X) (fun w => ((g (cpt X x0 w) : ℝ) : ℂ)) z ξ).re

def cfwM (X : Data E r) (ps : Frame X.Ψ r → ℝ) (a : ℝ) : Prop :=
  (∃ C A' : ℝ, ∀ x ∈ X.dom, ps x ≤ C + A' * Real.log (1 + 1 / X.la1 x)) ∧
  ∀ η : ℝ, 0 < η → η < 1 / 2 → ∃ C A' : ℝ, ∀ x ∈ X.dom, ∀ ξ : Fin r → E, X.IsIso ξ →
    (∀ τ, 1 ≤ X.tt ξ x τ) →
    ps x ≤ C + A' * Real.log (1 + 1 / X.la1 x) - 8 * Real.pi * (1 - 2 * η) * a * ⨅ τ, X.tt ξ x τ

structure ArchInM (X : Data E r) where
  L : Wt X.Ψ r
  de : Wt X.Ψ r
  Fp : Wt X.Ψ r
  T : ℕ
  i : ℕ
  g0 : ℕ
  N : ℕ
  c : ℝ
  c1 : ℝ
  a1 : ℝ
  rr : ℝ
  n_ge : 2 ≤ nd X
  T_ge : 11 * nd X ^ 2 ≤ T
  i_pos : 1 ≤ i
  genus_pos : 1 ≤ g0
  c_pos : 0 < c
  frame_theta_const_pos : 0 < c1
  frame_theta_weight_pos : 0 < a1
  rr_nonneg : 0 ≤ rr
  Tcg0 : (T : ℝ) * c * g0 ≤ 1
  rr_le : rr * (1 + c1 / a1) ≤ 2 * T
  w : Fin N → Frame X.Ψ r → ℂ
  w_van : ∀ k, w k ∈ X.SSgt L 0
  w_nz : ∀ x ∈ X.dom, ∃ k, w k x ≠ 0
  ph : Frame X.Ψ r → ℝ
  ph_inv : IsInvFn X ph
  ph_nonneg : ∀ x ∈ X.dom, 0 ≤ ph x
  p1 : ∃ ca ε0 : ℝ, 0 < ca ∧ 0 < ε0 ∧ ∀ x ∈ X.dom, X.la1 x < ε0 → ca / X.la1 x ^ 2 ≤ ph x
  p2 : ∀ x ∈ X.dom, (T : ℝ) * c * ph x ≤ c1 / X.la1 x ^ 2
  p3 : ∃ K : ℝ, ∀ x ∈ X.dom, Real.exp (-(2 * c * ph x)) ≤ K * ∑ k, X.pnorm L (w k) x ^ 2
  et : Frame X.Ψ r → ℂ
  genus_even : Even g0
  et_sec : X.IsSec ((i * (g0 / 2)) • de) et
  et_ne : ∃ x ∈ X.dom, et x ≠ 0
  p4 : ∃ K : ℝ, ∀ x ∈ X.dom, X.pnorm ((i * (g0 / 2)) • de) et x ^ 2 ≤ K * Real.exp (-(2 * i * ph x))
  th1 : Frame X.Ψ r → ℂ
  firstTheta_vanishes : th1 ∈ X.SSgt (2 • L - de) 0
  firstTheta_ne_zero : ∃ x ∈ X.dom, th1 x ≠ 0
  th2 : Frame X.Ψ r → ℂ
  secondTheta_vanishes : th2 ∈ X.SSgt ((nd X + 4) • L - Fp) 0
  secondTheta_ne_zero : ∃ x ∈ X.dom, th2 x ≠ 0
  thp : Frame X.Ψ r → ℂ
  thp_van : thp ∈ X.SSgt Fp 0
  thp_ne : ∃ x ∈ X.dom, thp x ≠ 0
  ps0 : Frame X.Ψ r → ℝ
  potential_invariant : IsInvFn X ps0
  potential_smooth : ∀ x0 ∈ X.dom, ContDiffOn ℝ ∞ (fun z => ps0 (cpt X x0 z)) {z | cpt X x0 z ∈ X.dom}
  base_psi_levi_lower_bound : ∀ x0 ∈ X.dom, ∀ z, cpt X x0 z ∈ X.dom → ∀ ξ : Fin (nd X) → ℂ,
    -(rr / 2 * leviM X (phla X de) x0 z ξ) ≤ leviM X ps0 x0 z ξ
  base_psi_weighted_cf : cfwM X ps0 a1
  posL : ∀ x0 ∈ X.dom, ∀ z, cpt X x0 z ∈ X.dom → ∀ ξ : Fin (nd X) → ℂ, ξ ≠ 0 →
    0 < leviM X (phla X L) x0 z ξ
  posLde : ∀ x0 ∈ X.dom, ∀ z, cpt X x0 z ∈ X.dom → ∀ ξ : Fin (nd X) → ℂ, ξ ≠ 0 →
    0 < leviM X (phla X (2 • L - de)) x0 z ξ
  posF : ∃ η : ℝ, 0 < η ∧ ∀ t : ℝ, 0 ≤ t → t * rr ≤ 2 * T →
    ∀ x0 ∈ X.dom, ∀ z, cpt X x0 z ∈ X.dom → ∀ ξ : Fin (nd X) → ℂ,
      2 * η * leviM X (phla X L) x0 z ξ ≤
        leviM X (phla X (Fp - kapW X - nd X • L)) x0 z ξ - t * (rr / 2) * leviM X (phla X de) x0 z ξ

structure FlatM (X : Data E r) (Xa : ArchInM X) where
  w0 : Frame X.Ψ r → ℂ
  s : Fin (nd X) → Frame X.Ψ r → ℂ
  weightForm_vanishes : w0 ∈ X.SSgt Xa.L 0
  s_van : ∀ k, s k ∈ X.SSgt Xa.L 0
  δ : ℕ
  xs : Fin δ → Frame X.Ψ r
  xs_mem : ∀ j, xs j ∈ X.dom
  S_eq : ∀ x ∈ X.dom, (∀ k, s k x = 0) ↔
    ∃ j, ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, x = lact γ (rmul (xs j) b)
  xs_inj : ∀ j j', ∀ γ ∈ X.Γ, ∀ b ∈ Bor X.Ψ r, xs j' = lact γ (rmul (xs j) b) → j = j'
  w0_ne : ∀ j, w0 (xs j) ≠ 0
  coord : ∀ j, (fderiv ℂ (fun z : V (nd X) => (WithLp.toLp 2 fun k =>
    s k (cpt X (xs j) z) / w0 (cpt X (xs j) z) : V (nd X))) 0).det ≠ 0
  w_le : ∃ K : ℝ, ∀ x ∈ X.dom, ∑ k, X.pnorm Xa.L (Xa.w k) x ^ 2 ≤
    K * (X.pnorm Xa.L w0 x ^ 2 + ∑ k, X.pnorm Xa.L (s k) x ^ 2)

  denom_le_family : ∃ K : ℝ, ∀ x ∈ X.dom, X.pnorm Xa.L w0 x ^ 2 ≤ K * ∑ k, X.pnorm Xa.L (Xa.w k) x ^ 2
  s_le_w : ∃ K : ℝ, ∀ x ∈ X.dom, ∑ k, X.pnorm Xa.L (s k) x ^ 2 ≤ K * ∑ k, X.pnorm Xa.L (Xa.w k) x ^ 2

  family_le_coords : ∀ U : Set (Frame X.Ψ r), IsOpen U → (∀ j, xs j ∈ U) →
    (∀ x ∈ U, ∀ γ ∈ X.Γ, ∀ b ∈ Bor X.Ψ r, lact γ (rmul x b) ∈ U) →
    ∃ K : ℝ, ∀ x ∈ X.dom, x ∉ U → ∑ k, X.pnorm Xa.L (Xa.w k) x ^ 2 ≤ K * ∑ k, X.pnorm Xa.L (s k) x ^ 2

def monoM {n : ℕ} (X : Data E r) (s : Fin n → Frame X.Ψ r → ℂ) (α : Fin n → ℕ) (x : Frame X.Ψ r) : ℂ :=
  ∏ k, s k x ^ α k

def leadM {n δ : ℕ} (X : Data E r) (s : Fin n → Frame X.Ψ r → ℂ) (w0 : Frame X.Ψ r → ℂ)
    (t : Fin δ → Frame X.Ψ r → ℂ) (T a0 : ℕ) (cc : (Fin n → ℕ) → Fin δ → ℂ) (x : Frame X.Ψ r) : ℂ :=
  ∑ α ∈ ReciprocityTheory.ChartRestriction.G.AR.multiLt n a0, ∑ k, cc α k * monoM X s α x * w0 x ^ (T - ∑ q, α q) * t k x

end

end ReciprocityTheory.ChartRestriction.G.AR.Up
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.LUStatementPfA
section
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.LUPf

open Matrix ReciprocityTheory.ChartRestriction.G.FD

noncomputable section

variable {n : ℕ}

abbrev lb (M : Matrix (Fin n) (Fin n) ℂ) (i : Fin n) : Matrix (Fin i) (Fin i) ℂ :=
  M.submatrix (Fin.castLE i.isLt.le) (Fin.castLE i.isLt.le)

theorem det_lb (M : Matrix (Fin n) (Fin n) ℂ) (i : Fin n) :
    (lb M i).det = lminor M (Fin.castSucc i) := rfl

def wv (M : Matrix (Fin n) (Fin n) ℂ) (i : Fin n) : Fin i → ℂ :=
  vecMul (fun j : Fin i => M i (Fin.castLE i.isLt.le j)) (lb M i)⁻¹

def Lm (M : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun i k => if h : (k : ℕ) < i then -wv M i ⟨k, h⟩ else if k = i then 1 else 0

theorem row_expand (N M : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n)
    (hup : ∀ k : Fin n, i < k → N i k = 0) (hd : N i i = 1) :
    (N * M) i j = (∑ k : Fin i, N i (Fin.castLE i.isLt.le k) * M (Fin.castLE i.isLt.le k) j) + M i j := by
  classical
  rw [Matrix.mul_apply]
  have h1 : ∑ k : Fin n, N i k * M k j = ∑ k ∈ Finset.univ.filter (fun k => k ≤ i), N i k * M k j := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun k _ => ?_
    split_ifs with hk
    · rfl
    · rw [hup k (lt_of_not_ge hk), zero_mul]
  have h2 : Finset.univ.filter (fun k : Fin n => k ≤ i) = insert i (Finset.univ.filter (fun k => k < i)) := by
    ext k
    simp [le_iff_lt_or_eq, or_comm]
  have h3 : ∑ k ∈ Finset.univ.filter (fun k : Fin n => k < i), N i k * M k j =
      ∑ k : Fin i, N i (Fin.castLE i.isLt.le k) * M (Fin.castLE i.isLt.le k) j := by
    refine Finset.sum_bij' (fun k hk => (⟨k, (Finset.mem_filter.mp hk).2⟩ : Fin i))
      (fun k _ => Fin.castLE i.isLt.le k) (fun _ _ => Finset.mem_univ _) (fun k _ => ?_)
      (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact k.isLt
  rw [h1, h2, Finset.sum_insert (by simp), h3, hd, one_mul, add_comm]

theorem Lm_up (M : Matrix (Fin n) (Fin n) ℂ) (i k : Fin n) (h : i < k) : Lm M i k = 0 := by
  simp only [Lm, Matrix.of_apply]
  have h' : ¬ ((k : ℕ) < i) := by rw [Fin.lt_iff_val_lt_val] at h; omega
  rw [dite_eq_right h', if_neg (ne_of_gt h)]

theorem Lm_diag (M : Matrix (Fin n) (Fin n) ℂ) (i : Fin n) : Lm M i i = 1 := by
  simp [Lm]

theorem Lm_det (M : Matrix (Fin n) (Fin n) ℂ) : (Lm M).det = 1 := by
  rw [Matrix.det_of_lowerTriangular _ (fun i k h => Lm_up M i k (OrderDual.toDual_lt_toDual.mp h))]
  simp [Lm_diag]

theorem row_sys (N M : Matrix (Fin n) (Fin n) ℂ) (i : Fin n)
    (hup : ∀ k : Fin n, i < k → N i k = 0) (hd : N i i = 1)
    (hz : ∀ j : Fin n, j < i → (N * M) i j = 0) :
    vecMul (fun k : Fin i => N i (Fin.castLE i.isLt.le k)) (lb M i) =
      -fun j : Fin i => M i (Fin.castLE i.isLt.le j) := by
  funext j'
  have hrow := row_expand N M i (Fin.castLE i.isLt.le j') hup hd
  rw [hz _ (by simp [Fin.lt_iff_val_lt_val])] at hrow
  simp only [vecMul, dotProduct, lb, submatrix_apply, Pi.neg_apply]
  linear_combination (-1 : ℂ) * hrow

theorem Lm_mul_up (M : Matrix (Fin n) (Fin n) ℂ) (hM : ∀ k : Fin (n + 1), lminor M k ≠ 0)
    (i j : Fin n) (h : j < i) : (Lm M * M) i j = 0 := by
  have hdet : IsUnit (lb M i).det := by rw [det_lb]; exact isUnit_iff_ne_zero.mpr (hM _)
  rw [row_expand (Lm M) M i j (fun k hk => Lm_up M i k hk) (Lm_diag M i)]
  have hL : ∀ k : Fin i, Lm M i (Fin.castLE i.isLt.le k) = -wv M i k := by
    intro k
    simp only [Lm, Matrix.of_apply]
    rw [dite_eq_left (by simp)]
    rfl
  simp_rw [hL]
  have key : vecMul (wv M i) (lb M i) = fun j : Fin i => M i (Fin.castLE i.isLt.le j) := by
    rw [wv, vecMul_vecMul, Matrix.nonsing_inv_mul _ hdet, vecMul_one]
  have hk := congrFun key ⟨j, h⟩
  simp only [vecMul, dotProduct, lb, submatrix_apply] at hk
  have hk' : ∑ k : Fin i, wv M i k * M (Fin.castLE i.isLt.le k) j = M i j := hk
  simp only [neg_mul, Finset.sum_neg_distrib, hk', neg_add_cancel]

theorem Lm_unique (N M : Matrix (Fin n) (Fin n) ℂ) (hM : ∀ k : Fin (n + 1), lminor M k ≠ 0)
    (hup : ∀ i k : Fin n, i < k → N i k = 0) (hd : ∀ i, N i i = 1)
    (hz : ∀ i j : Fin n, j < i → (N * M) i j = 0) : N = Lm M := by
  ext i k
  have hdet : IsUnit (lb M i).det := by rw [det_lb]; exact isUnit_iff_ne_zero.mpr (hM _)
  have h1 := row_sys N M i (hup i) (hd i) (hz i)
  have h2 := row_sys (Lm M) M i (fun k hk => Lm_up M i k hk) (Lm_diag M i)
    (fun j hj => Lm_mul_up M hM i j hj)
  have heq : (fun k : Fin i => N i (Fin.castLE i.isLt.le k)) = fun k => Lm M i (Fin.castLE i.isLt.le k) := by
    have h3 := congrArg (fun v => vecMul v (lb M i)⁻¹) (h1.trans h2.symm)
    simpa only [vecMul_vecMul, Matrix.mul_nonsing_inv _ hdet, vecMul_one] using h3
  rcases lt_trichotomy k i with hk | rfl | hk
  · exact congrFun heq ⟨k, hk⟩
  · rw [hd, Lm_diag]
  · rw [hup i k hk, Lm_up M i k hk]

theorem lminor_nb (N B : Matrix (Fin n) (Fin n) ℂ) (hup : ∀ i k : Fin n, i < k → N i k = 0)
    (hd : ∀ i, N i i = 1) (hB : B.BlockTriangular id) (k : Fin (n + 1)) :
    lminor (N * B) k = ∏ j : Fin k, B (Fin.castLE (Nat.le_of_lt_succ k.isLt) j)
      (Fin.castLE (Nat.le_of_lt_succ k.isLt) j) := by
  set e : Fin k → Fin n := Fin.castLE (Nat.le_of_lt_succ k.isLt) with he
  have hmono : ∀ a b : Fin k, a < b → e a < e b := fun a b h => h
  have hsub : (N * B).submatrix e e = N.submatrix e e * B.submatrix e e := by
    ext a b
    simp only [submatrix_apply, Matrix.mul_apply]
    symm
    refine Fintype.sum_of_injective e (Fin.castLE_injective _) _ _ (fun c hc => ?_) (fun _ => rfl)
    have hc' : (k : ℕ) ≤ c := by
      by_contra hlt
      exact hc ⟨⟨c, by omega⟩, Fin.ext rfl⟩
    have hac : e a < c := by
      rw [Fin.lt_iff_val_lt_val]
      show (a : ℕ) < c
      omega
    rw [hup _ _ hac, zero_mul]
  have hNt : (N.submatrix e e).BlockTriangular OrderDual.toDual :=
    fun a b h => hup _ _ (hmono _ _ (OrderDual.toDual_lt_toDual.mp h))
  have hBt : (B.submatrix e e).BlockTriangular id := fun a b h => hB (hmono _ _ h)
  rw [lminor, ← he, hsub, det_mul, Matrix.det_of_lowerTriangular _ hNt,
    Matrix.det_of_upperTriangular hBt]
  simp [hd]

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.LUPf
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.MeasInvStatementPfC
section
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.MI

open Matrix MeasureTheory ReciprocityTheory.ChartRestriction.G.FD

noncomputable section

theorem volume_null_of_slice {I : Type*} [Fintype I] [DecidableEq I] (i0 : I) {S : Set (I → ℂ)}
    (hS : MeasurableSet S) (huniq : ∀ v ∈ S, ∀ v' ∈ S, (∀ j, j ≠ i0 → v j = v' j) → v = v') :
    volume S = 0 := by
  classical
  let e := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : I => ℂ) (fun j => j ≠ i0)
  have hmp : MeasurePreserving e (volume : Measure (I → ℂ))
      ((Measure.pi fun _ : {j // j ≠ i0} => (volume : Measure ℂ)).prod
        (Measure.pi fun _ : {j // ¬ j ≠ i0} => (volume : Measure ℂ))) :=
    measurePreserving_piEquivPiSubtypeProd (fun _ : I => (volume : Measure ℂ)) (fun j => j ≠ i0)
  have hS' : MeasurableSet (e.symm ⁻¹' S) := e.symm.measurable hS
  rw [← hmp.symm.measure_preimage_equiv S, Measure.measure_prod_null hS']
  refine Filter.Eventually.of_forall fun x => ?_
  haveI : Nonempty {j // ¬ j ≠ i0} := ⟨⟨i0, not_not.2 rfl⟩⟩
  show (Measure.pi fun _ : {j // ¬ j ≠ i0} => (volume : Measure ℂ)) _ = 0
  refine Set.Subsingleton.measure_zero ?_ _
  intro y hy y' hy'
  have hxy : e.symm (x, y) = e.symm (x, y') := by
    refine huniq _ hy _ hy' fun j hj => ?_
    simp [e, MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd, hj]
  have := e.symm.injective hxy
  exact (Prod.ext_iff.1 this).2

lemma det_diff_last {k : ℕ} (B B' : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)
    (h : ∀ a b, ¬ (a = Fin.last k ∧ b = Fin.last k) → B a b = B' a b) :
    B.det - B'.det = (B (Fin.last k) (Fin.last k) - B' (Fin.last k) (Fin.last k)) *
      (B.submatrix Fin.castSucc Fin.castSucc).det := by
  have hrows : ∀ j : Fin (k + 1), B.submatrix (Fin.last k).succAbove j.succAbove =
      B'.submatrix (Fin.last k).succAbove j.succAbove := by
    intro j
    ext a b
    refine h _ _ fun hab => ?_
    have := hab.1
    rw [Fin.succAbove_last] at this
    exact Fin.castSucc_ne_last a this
  rw [Matrix.det_succ_row B (Fin.last k), Matrix.det_succ_row B' (Fin.last k),
    ← Finset.sum_sub_distrib, Finset.sum_eq_single (Fin.last k)]
  · rw [hrows (Fin.last k)]
    have hs : (-1 : ℂ) ^ ((Fin.last k : ℕ) + (Fin.last k : ℕ)) = 1 := by
      rw [Fin.val_last, ← two_mul, pow_mul]; simp
    have hc : B.submatrix Fin.castSucc Fin.castSucc = B'.submatrix Fin.castSucc Fin.castSucc := by
      simpa [Fin.succAbove_last] using hrows (Fin.last k)
    rw [hs, Fin.succAbove_last, hc]
    ring
  · intro j _ hj
    have hrow : B (Fin.last k) j = B' (Fin.last k) j := h _ _ fun hab => hj hab.2
    rw [hrow, hrows j]
    ring
  · intro hmem
    exact absurd (Finset.mem_univ _) hmem

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ}

lemma continuous_lminor (τ : ι) (i : Fin (r + 1)) : Continuous fun v : Ix ι r → ℂ => lminor (Mt v τ) i := by
  unfold Mt lminor
  refine Continuous.matrix_det ?_
  refine continuous_pi fun a => continuous_pi fun b => ?_
  exact continuous_apply _

theorem volume_lminor_zero (τ : ι) :
    ∀ k (h : k < r + 1), volume {v : Ix ι r → ℂ | lminor (Mt v τ) ⟨k, h⟩ = 0} = 0 := by
  intro k
  induction k with
  | zero =>
    intro h
    have hempty : {v : Ix ι r → ℂ | lminor (Mt v τ) ⟨0, h⟩ = 0} = ∅ := by
      ext v
      simp [lminor]
    rw [hempty, measure_empty]
  | succ k ih =>
    intro h
    have hk : k < r + 1 := by omega
    have hkr : k < r := by omega
    have hl : (Fin.castLE (Nat.le_of_lt_succ h) (Fin.last k) : Fin r) = ⟨k, hkr⟩ :=
      Fin.ext (by simp)
    have key : ∀ w : Ix ι r → ℂ, lminor (Mt w τ) ⟨k, hk⟩ =
        (((Mt w τ).submatrix (Fin.castLE (Nat.le_of_lt_succ h)) (Fin.castLE (Nat.le_of_lt_succ h))).submatrix
          Fin.castSucc Fin.castSucc).det := fun w => rfl
    have hmeas : MeasurableSet {v : Ix ι r → ℂ |
        lminor (Mt v τ) ⟨k + 1, h⟩ = 0 ∧ lminor (Mt v τ) ⟨k, hk⟩ ≠ 0} :=
      (isClosed_eq (continuous_lminor τ _) continuous_const).measurableSet.inter
        (isClosed_eq (continuous_lminor τ _) continuous_const).isOpen_compl.measurableSet
    refine measure_mono_null (t := {v : Ix ι r → ℂ | lminor (Mt v τ) ⟨k, hk⟩ = 0} ∪
      {v : Ix ι r → ℂ | lminor (Mt v τ) ⟨k + 1, h⟩ = 0 ∧ lminor (Mt v τ) ⟨k, hk⟩ ≠ 0}) ?_ ?_
    · intro v hv
      by_cases h0 : lminor (Mt v τ) ⟨k, hk⟩ = 0
      · exact Or.inl h0
      · exact Or.inr ⟨hv, h0⟩
    refine measure_union_null (ih hk) ?_
    refine volume_null_of_slice (τ, ⟨k, hkr⟩, ⟨k, hkr⟩) hmeas ?_
    intro v hv v' hv' hagree
    have dd := det_diff_last
      ((Mt v τ).submatrix (Fin.castLE (Nat.le_of_lt_succ h)) (Fin.castLE (Nat.le_of_lt_succ h)))
      ((Mt v' τ).submatrix (Fin.castLE (Nat.le_of_lt_succ h)) (Fin.castLE (Nat.le_of_lt_succ h)))
      (by
        intro a b hab
        refine hagree _ fun heq => hab ?_
        simp only [Prod.mk.injEq, Fin.ext_iff, Fin.coe_castLE] at heq
        exact ⟨Fin.ext (by simp [heq.2.1]), Fin.ext (by simp [heq.2.2])⟩)
    have h1 : lminor (Mt v τ) ⟨k + 1, h⟩ = 0 := hv.1
    have h2 : lminor (Mt v' τ) ⟨k + 1, h⟩ = 0 := hv'.1
    have hm : lminor (Mt v τ) ⟨k, hk⟩ ≠ 0 := hv.2
    rw [key v] at hm
    simp only [lminor] at h1 h2
    rw [h1, h2, sub_zero] at dd
    simp only [Matrix.submatrix_apply, hl] at dd
    have hz : v (τ, ⟨k, hkr⟩, ⟨k, hkr⟩) - v' (τ, ⟨k, hkr⟩, ⟨k, hkr⟩) = 0 := by
      rcases mul_eq_zero.1 dd.symm with hz | hz
      · exact hz
      · exact absurd hz hm
    funext j
    by_cases hj : j = (τ, ⟨k, hkr⟩, ⟨k, hkr⟩)
    · subst hj; exact sub_eq_zero.1 hz
    · exact hagree j hj

theorem volume_BC_compl : volume (BC ι r)ᶜ = 0 := by
  have hU : (BC ι r)ᶜ = ⋃ τ : ι, ⋃ i : Fin (r + 1), {v : Ix ι r → ℂ | lminor (Mt v τ) i = 0} := by
    ext v
    simp [BC]
  rw [hU]
  refine measure_iUnion_null fun τ => measure_iUnion_null fun i => ?_
  exact volume_lminor_zero τ i.1 i.2

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.MI
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OrthoStatementPf
section
namespace ReciprocityTheory.ChartRestriction.G.AR.Up

open NumberField Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem ortho_holds : OrthoStatement (E := E) := by
  intro r X x hx

  have hBor := ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.bOf_mem (X := X) hx
  refine ⟨ReciprocityTheory.ChartRestriction.G.FD.rmul x (ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.bOf X x),
    ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.ortho_bOf (X := X) hx,
    fun τ => ((ReciprocityTheory.ChartRestriction.G.FD.mat (ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.bOf X x) τ)⁻¹ :
      Matrix (Fin r) (Fin r) ℂ), ?_, ?_⟩
  · intro τ
    have hdet : IsUnit (ReciprocityTheory.ChartRestriction.G.FD.mat (ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.bOf X x) τ).det :=
      isUnit_iff_ne_zero.mpr (hBor τ).1
    haveI : Invertible (ReciprocityTheory.ChartRestriction.G.FD.mat (ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.bOf X x) τ) :=
      Matrix.invertibleOfIsUnitDet _ hdet
    have hM : (ReciprocityTheory.ChartRestriction.G.FD.mat (ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.bOf X x) τ).BlockTriangular id :=
      fun i j hij => (hBor τ).2 i j hij
    have hMi := Matrix.blockTriangular_inv_of_blockTriangular hM
    refine ⟨?_, fun a c hca => hMi hca⟩
    show ((ReciprocityTheory.ChartRestriction.G.FD.mat (ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.bOf X x) τ)⁻¹).det ≠ 0
    exact (Matrix.isUnit_nonsing_inv_det _ hdet).ne_zero
  · funext τ
    have hdet : IsUnit (ReciprocityTheory.ChartRestriction.G.FD.mat (ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.bOf X x) τ).det :=
      isUnit_iff_ne_zero.mpr (hBor τ).1
    show ReciprocityTheory.ChartRestriction.G.FD.mat x τ = ReciprocityTheory.ChartRestriction.G.FD.mat x τ *
      ReciprocityTheory.ChartRestriction.G.FD.mat (ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.bOf X x) τ *
      (ReciprocityTheory.ChartRestriction.G.FD.mat (ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.bOf X x) τ)⁻¹
    rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hdet, Matrix.mul_one]

end

end ReciprocityTheory.ChartRestriction.G.AR.Up
end

