module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.IsClosedKset
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.Bundle0002
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.Bundle0007
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.Bundle0004
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.Bundle0008
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.Bundle0003
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.KFacts
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.Bundle0003

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.DecMoments
section
noncomputable section

open Finset MeasureTheory Matrix
open scoped ComplexOrder ContDiff ENNReal

namespace ReciprocityTheory.ChartRestriction.DS.S7

open ReciprocityTheory.ChartRestriction.DS

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

lemma dm_rank_add (A B : Matrix (Fin n) (Fin n) ℂ) : (A + B).rank ≤ A.rank + B.rank := by
  unfold Matrix.rank
  rw [Matrix.mulVecLin_add]
  calc Module.finrank ℂ (LinearMap.range (A.mulVecLin + B.mulVecLin))
      ≤ Module.finrank ℂ ↥(LinearMap.range A.mulVecLin ⊔ LinearMap.range B.mulVecLin) := by
        apply Submodule.finrank_mono
        rintro _ ⟨v, rfl⟩
        exact Submodule.add_mem_sup ⟨v, rfl⟩ ⟨v, rfl⟩
    _ ≤ _ := Submodule.finrank_add_le_finrank_add_finrank _ _

lemma dm_zero_of_eq {ε : Fin n → Bool} {Y : Matrix (Fin n) (Fin n) ℂ} (hYp : inP ε Y) (a b : Fin n)
    (hab : ε a = ε b) : Y a b = 0 := by
  have h := congrFun (congrFun hYp.2 a) b
  simp only [Jm, Matrix.mul_diagonal, Matrix.neg_apply, Matrix.diagonal_mul, hab] at h
  split_ifs at h
  · linear_combination (1 / 2 : ℂ) * h
  · linear_combination (-1 / 2 : ℂ) * h

lemma dm_rank_le {ε : Fin n → Bool} {Y : Matrix (Fin n) (Fin n) ℂ} (hYp : inP ε Y) :
    Y.rank ≤ 2 * q0 ε := by
  classical
  set P : Matrix (Fin n) (Fin n) ℂ := Matrix.diagonal fun a => if ε a then 1 else 0 with hPd
  set Q : Matrix (Fin n) (Fin n) ℂ := Matrix.diagonal fun a => if ε a then 0 else 1 with hQd
  have hY : Y = P * Y * Q + Q * Y * P := by
    ext a b
    simp only [hPd, hQd, Matrix.add_apply, Matrix.mul_diagonal, Matrix.diagonal_mul]
    by_cases ha : ε a <;> by_cases hb : ε b <;> simp [ha, hb] <;>
      exact dm_zero_of_eq hYp a b (by simp [ha, hb])
  have hP : P.rank = pOf ε := by
    rw [hPd, Matrix.rank_diagonal, Fintype.card_subtype]
    unfold pOf
    congr 1; ext a; by_cases h : ε a <;> simp [h]
  have hQ : Q.rank = qOf ε := by
    rw [hQd, Matrix.rank_diagonal, Fintype.card_subtype]
    unfold qOf
    congr 1; ext a; by_cases h : ε a <;> simp [h]
  have h1 : (P * Y * Q).rank ≤ q0 ε :=
    le_min ((Matrix.rank_mul_le_left _ _).trans ((Matrix.rank_mul_le_left _ _).trans hP.le))
      ((Matrix.rank_mul_le_right _ _).trans hQ.le)
  have h2 : (Q * Y * P).rank ≤ q0 ε :=
    le_min ((Matrix.rank_mul_le_right _ _).trans hP.le)
      ((Matrix.rank_mul_le_left _ _).trans ((Matrix.rank_mul_le_left _ _).trans hQ.le))
  calc Y.rank = (P * Y * Q + Q * Y * P).rank := congrArg Matrix.rank hY
    _ ≤ (P * Y * Q).rank + (Q * Y * P).rank := dm_rank_add _ _
    _ ≤ q0 ε + q0 ε := add_le_add h1 h2
    _ = 2 * q0 ε := by ring

lemma dm_card_le {ε : Fin n → Bool} {Y U : Matrix (Fin n) (Fin n) ℂ} {y : Fin n → ℝ}
    (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) (hY : Y = U * Matrix.diagonal (fun j => (y j : ℂ)) * Uᴴ)
    (hYp : inP ε Y) : (univ.filter fun j => y j ≠ 0).card ≤ 2 * q0 ε := by
  have hdet : IsUnit U.det := Matrix.isUnit_det_of_left_inverse (Matrix.mem_unitaryGroup_iff'.1 hU)
  have hdet' : IsUnit Uᴴ.det := Matrix.isUnit_det_of_right_inverse (Matrix.mem_unitaryGroup_iff'.1 hU)
  have h1 : Y.rank = (univ.filter fun j => y j ≠ 0).card := by
    rw [hY, Matrix.rank_mul_eq_left_of_isUnit_det _ _ hdet',
      Matrix.rank_mul_eq_right_of_isUnit_det _ _ hdet, Matrix.rank_diagonal, Fintype.card_subtype]
    simp [Complex.ofReal_eq_zero]
  rw [← h1]
  exact dm_rank_le hYp

lemma dm_range {ε : Fin n → Bool} {Y U : Matrix (Fin n) (Fin n) ℂ} {y : Fin n → ℝ}
    (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) (hY : Y = U * Matrix.diagonal (fun j => (y j : ℂ)) * Uᴴ)
    (hYp : inP ε Y) (J : Finset (Fin n)) :
    |∑ j ∈ J, y j| ≤ Real.sqrt (2 * q0 ε) * Real.sqrt (hs Y) := by
  unfold hs
  have key : ∀ M : Matrix (Fin n) (Fin n) ℂ, (((∑ i, ∑ j, ‖M i j‖ ^ 2 : ℝ)) : ℂ) = (M * Mᴴ).trace := by
    intro M
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Complex.ofReal_sum, Complex.ofReal_pow]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    first
      | (rw [Complex.star_def, Complex.mul_conj'])
      | (rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring)
      | simp [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hUU : Uᴴ * U = 1 := Matrix.mem_unitaryGroup_iff'.1 hU
  have h2 : ∀ M : Matrix (Fin n) (Fin n) ℂ, Uᴴ * (U * M) = M := fun M => by
    rw [← Matrix.mul_assoc, hUU, Matrix.one_mul]
  have htr : (Y * Yᴴ).trace = (((∑ j, y j ^ 2 : ℝ)) : ℂ) := by
    rw [hY]
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc, h2]
    rw [Matrix.trace_mul_comm, Matrix.mul_assoc, Matrix.mul_assoc, hUU, Matrix.mul_one,
      Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal]
    push_cast
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [Complex.conj_ofReal, sq]
  have hsum : ∑ i, ∑ j, ‖Y i j‖ ^ 2 = ∑ j, y j ^ 2 := by
    have h := key Y
    rw [htr] at h
    exact_mod_cast h
  have hT : ∑ j ∈ J, y j = ∑ j ∈ J.filter (fun j => y j ≠ 0), y j :=
    (Finset.sum_filter_ne_zero _).symm
  have hcard : (J.filter fun j => y j ≠ 0).card ≤ 2 * q0 ε :=
    (Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_univ J))).trans
      (dm_card_le hU hY hYp)
  have hcs : (∑ j ∈ J.filter (fun j => y j ≠ 0), y j) ^ 2 ≤
      ((J.filter fun j => y j ≠ 0).card : ℝ) * ∑ j, y j ^ 2 := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq (J.filter fun j => y j ≠ 0) (fun _ => (1 : ℝ)) y
    simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at h
    refine h.trans (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _))
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun j _ _ => sq_nonneg _)
  rw [hsum, ← Real.sqrt_mul (by positivity), hT]
  apply Real.abs_le_sqrt
  refine hcs.trans (mul_le_mul_of_nonneg_right ?_ (Finset.sum_nonneg fun j _ => sq_nonneg _))
  exact_mod_cast hcard

theorem dec_moments {ε : Fin n → Bool} {Y U : Matrix (Fin n) (Fin n) ℂ} {y : Fin n → ℝ}
    (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) (hY : Y = U * Matrix.diagonal (fun j => (y j : ℂ)) * Uᴴ)
    (hYp : inP ε Y) (i : ℕ) (hi : i ≤ n) :
    (∑ J : {J : Finset (Fin n) // J.card = i},
        ‖(U.submatrix (Fin.castLE hi) (J.1.orderEmbOfFin J.2)).det‖ ^ 2 = 1) ∧
    (∑ J : {J : Finset (Fin n) // J.card = i},
        ‖(U.submatrix (Fin.castLE hi) (J.1.orderEmbOfFin J.2)).det‖ ^ 2 * (∑ j ∈ J.1, y j) = 0) ∧
    (∑ J : {J : Finset (Fin n) // J.card = i},
        ‖(U.submatrix (Fin.castLE hi) (J.1.orderEmbOfFin J.2)).det‖ ^ 2 * (∑ j ∈ J.1, y j) ^ 2 =
      ∑ a : Fin n, ∑ b : Fin n, if (b : ℕ) < i ∧ i ≤ (a : ℕ) then ‖Y a b‖ ^ 2 else 0) ∧
    (∀ J : {J : Finset (Fin n) // J.card = i},
        |∑ j ∈ J.1, y j| ≤ Real.sqrt (2 * q0 ε) * Real.sqrt (hs Y)) := by
  have hd : ∀ a, Y a a = 0 := fun a => dm_zero_of_eq hYp a a rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h := dm_mass hU hi
    have h2 : ∑ J : {J : Finset (Fin n) // J.card = i}, dmW U hi J = 1 := by exact_mod_cast h
    exact h2
  · have h := dm_mean hU hY hd hi
    have h2 : ∑ J : {J : Finset (Fin n) // J.card = i}, dmW U hi J * (∑ j ∈ J.1, y j) = 0 := by
      exact_mod_cast h
    exact h2
  · have h := (dm_var hU hY hd hi).trans (dm_rhs hY i)
    have h2 : ∑ J : {J : Finset (Fin n) // J.card = i}, dmW U hi J * (∑ j ∈ J.1, y j) ^ 2 =
        ∑ a : Fin n, ∑ b : Fin n, if (b : ℕ) < i ∧ i ≤ (a : ℕ) then ‖Y a b‖ ^ 2 else 0 := by
      exact_mod_cast h
    exact h2
  · intro J
    exact dm_range hU hY hYp J.1

end ReciprocityTheory.ChartRestriction.DS.S7
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.GelfandPhiA
section
noncomputable section

open Finset Matrix
open scoped ContDiff

namespace ReciprocityTheory.ChartRestriction.DS.S7

open ReciprocityTheory.ChartRestriction.DS

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

def smoothS (n : ℕ) : Submodule ℂ (Matrix (Fin n) (Fin n) ℂ → ℂ) where
  carrier := {F | ContDiffOn ℂ ∞ F (OmegaSet n)}
  add_mem' hF hG := hF.add hG
  zero_mem' := contDiffOn_const
  smul_mem' c _ hF := hF.const_smul c

private theorem isOpen_OmegaSet' : IsOpen (OmegaSet n) := by
  show IsOpen {z : Matrix (Fin n) (Fin n) ℂ | ∀ i : Fin n, lead ((i : ℕ) + 1) z ≠ 0}
  rw [Set.setOf_forall]
  refine isOpen_iInter_of_finite fun i => isOpen_ne_fun ?_ continuous_const
  show Continuous fun z : Matrix (Fin n) (Fin n) ℂ => lead ((i : ℕ) + 1) z
  by_cases h : (i : ℕ) + 1 ≤ n
  · have e : (fun z : Matrix (Fin n) (Fin n) ℂ => lead ((i : ℕ) + 1) z) =
        fun z => (z.submatrix (Fin.castLE h) (Fin.castLE h)).det := funext fun z => dif_pos h
    rw [e]
    exact (continuous_id.matrix_submatrix _ _).matrix_det
  · have e : (fun z : Matrix (Fin n) (Fin n) ℂ => lead ((i : ℕ) + 1) z) = fun _ => 0 :=
      funext fun z => dif_neg h
    rw [e]
    exact continuous_const

theorem lhol_congr {X : Matrix (Fin n) (Fin n) ℂ} {G H : Matrix (Fin n) (Fin n) ℂ → ℂ}
    (h : Set.EqOn G H (OmegaSet n)) {z : Matrix (Fin n) (Fin n) ℂ} (hz : z ∈ OmegaSet n) :
    Lhol X G z = Lhol X H z := by
  show fderiv ℂ G z (X * z) = fderiv ℂ H z (X * z)
  rw [Filter.EventuallyEq.fderiv_eq (Filter.eventually_of_mem (isOpen_OmegaSet'.mem_nhds hz) h)]

theorem lhol_mem {X : Matrix (Fin n) (Fin n) ℂ} {F : Matrix (Fin n) (Fin n) ℂ → ℂ}
    (hF : ContDiffOn ℂ ∞ F (OmegaSet n)) : ContDiffOn ℂ ∞ (Lhol X F) (OmegaSet n) := by
  have h1 :=
    ((contDiffOn_infty_iff_fderiv_of_isOpen isOpen_OmegaSet').1 hF).2
  have h2 : ContDiff ℂ ∞ (fun z : Matrix (Fin n) (Fin n) ℂ => X * z) := by
    refine contDiff_pi.2 fun a => contDiff_pi.2 fun b => ?_
    simp only [Matrix.mul_apply]
    exact ContDiff.sum fun c _ => contDiff_const.mul (contDiff_pi.1 (contDiff_pi.1 contDiff_id c) b)
  exact h1.clm_apply h2.contDiffOn

def ltOp (X : Matrix (Fin n) (Fin n) ℂ) (F : Matrix (Fin n) (Fin n) ℂ → ℂ) :
    Matrix (Fin n) (Fin n) ℂ → ℂ :=
  (OmegaSet n).indicator (Lhol X F)

theorem ltOp_of_mem {X : Matrix (Fin n) (Fin n) ℂ} (F : Matrix (Fin n) (Fin n) ℂ → ℂ)
    {z : Matrix (Fin n) (Fin n) ℂ} (hz : z ∈ OmegaSet n) : ltOp X F z = Lhol X F z := by
  exact Set.indicator_of_mem hz _

theorem ltOp_of_not_mem {X : Matrix (Fin n) (Fin n) ℂ} (F : Matrix (Fin n) (Fin n) ℂ → ℂ)
    {z : Matrix (Fin n) (Fin n) ℂ} (hz : z ∉ OmegaSet n) : ltOp X F z = 0 := by
  simp [ltOp, hz]

theorem ltOp_mem {X : Matrix (Fin n) (Fin n) ℂ} {F : Matrix (Fin n) (Fin n) ℂ → ℂ}
    (hF : ContDiffOn ℂ ∞ F (OmegaSet n)) : ContDiffOn ℂ ∞ (ltOp X F) (OmegaSet n) := by
  exact (lhol_mem hF).congr fun z hz => ltOp_of_mem F hz

theorem differentiableAt_of_mem {F : Matrix (Fin n) (Fin n) ℂ → ℂ}
    (hF : ContDiffOn ℂ ∞ F (OmegaSet n)) {z : Matrix (Fin n) (Fin n) ℂ} (hz : z ∈ OmegaSet n) :
    DifferentiableAt ℂ F z := by
  exact ((hF.differentiableOn (by simp <;> exact_mod_cast (le_top : (1 : ℕ∞) ≤ ⊤))) z hz).differentiableAt (isOpen_OmegaSet'.mem_nhds hz)

def eOp (X : Matrix (Fin n) (Fin n) ℂ) : Module.End ℂ (smoothS n) where
  toFun F := ⟨ltOp X F, ltOp_mem F.2⟩
  map_add' F G := by
    apply Subtype.ext
    funext z
    by_cases hz : z ∈ OmegaSet n
    · simp only [Submodule.coe_add, Pi.add_apply, ltOp_of_mem _ hz]
      show fderiv ℂ (F.1 + G.1) z (X * z) = fderiv ℂ F.1 z (X * z) + fderiv ℂ G.1 z (X * z)
      erw [((differentiableAt_of_mem F.2 hz).hasFDerivAt.add (differentiableAt_of_mem G.2 hz).hasFDerivAt).fderiv]
      rfl
    · simp only [Submodule.coe_add, Pi.add_apply, ltOp_of_not_mem _ hz, add_zero]
  map_smul' c F := by
    apply Subtype.ext
    funext z
    by_cases hz : z ∈ OmegaSet n
    · simp only [SetLike.val_smul, Pi.smul_apply, RingHom.id_apply, ltOp_of_mem _ hz]
      show fderiv ℂ (c • F.1) z (X * z) = c • fderiv ℂ F.1 z (X * z)
      erw [fderiv_const_smul (differentiableAt_of_mem F.2 hz)]
      rfl
    · simp only [SetLike.val_smul, Pi.smul_apply, RingHom.id_apply, ltOp_of_not_mem _ hz, smul_zero]

theorem eOp_apply (X : Matrix (Fin n) (Fin n) ℂ) (F : smoothS n) :
    ((eOp X F : smoothS n) : Matrix (Fin n) (Fin n) ℂ → ℂ) = ltOp X F := rfl

theorem eOp_sub (X Y : Matrix (Fin n) (Fin n) ℂ) : eOp (X - Y) = eOp X - eOp Y := by
  apply LinearMap.ext
  intro F
  apply Subtype.ext
  funext z
  show ltOp (X - Y) F.1 z = ltOp X F.1 z - ltOp Y F.1 z
  by_cases hz : z ∈ OmegaSet n
  · rw [ltOp_of_mem _ hz, ltOp_of_mem _ hz, ltOp_of_mem _ hz]
    show fderiv ℂ F.1 z ((X - Y) * z) = fderiv ℂ F.1 z (X * z) - fderiv ℂ F.1 z (Y * z)
    rw [Matrix.sub_mul, map_sub]
  · rw [ltOp_of_not_mem _ hz, ltOp_of_not_mem _ hz, ltOp_of_not_mem _ hz, sub_zero]

theorem eOp_zero : eOp (0 : Matrix (Fin n) (Fin n) ℂ) = 0 := by
  apply LinearMap.ext; intro F
  apply Subtype.ext; funext z
  show ltOp 0 F z = 0
  by_cases hz : z ∈ OmegaSet n
  · rw [ltOp_of_mem _ hz]
    show fderiv ℂ F.1 z (0 * z) = 0
    rw [Matrix.zero_mul, map_zero]
  · rw [ltOp_of_not_mem _ hz]

private theorem Lhol_commutator_on_OmegaSet {F : Matrix (Fin n) (Fin n) ℂ → ℂ} (hF : ContDiffOn ℂ ∞ F (OmegaSet n))
    (X Y : Matrix (Fin n) (Fin n) ℂ) {z : Matrix (Fin n) (Fin n) ℂ} (hz : z ∈ OmegaSet n) :
    Lhol X (Lhol Y F) z - Lhol Y (Lhol X F) z = Lhol (Y * X - X * Y) F z := by
  have hc := hF.contDiffAt (isOpen_OmegaSet'.mem_nhds hz)
  have h1 := ((contDiffOn_infty_iff_fderiv_of_isOpen isOpen_OmegaSet').1 hF).2
  have hd := ((h1.differentiableOn (by simp <;> exact_mod_cast (le_top : (1 : ℕ∞) ≤ ⊤))) z hz).differentiableAt
    (isOpen_OmegaSet'.mem_nhds hz) |>.hasFDerivAt
  have hs := hc.isSymmSndFDerivAt (by first | exact le_top | (simp; done) | (simp <;> exact (WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ ⊤) : ((2 : ℕ∞) : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω))) | (simp <;> decide))
  let LX : Matrix (Fin n) (Fin n) ℂ →L[ℂ] Matrix (Fin n) (Fin n) ℂ := LinearMap.toContinuousLinearMap
    { toFun := fun w => X * w
      map_add' := fun a b => Matrix.mul_add X a b
      map_smul' := fun c a => Matrix.mul_smul X c a }
  let LY : Matrix (Fin n) (Fin n) ℂ →L[ℂ] Matrix (Fin n) (Fin n) ℂ := LinearMap.toContinuousLinearMap
    { toFun := fun w => Y * w
      map_add' := fun a b => Matrix.mul_add Y a b
      map_smul' := fun c a => Matrix.mul_smul Y c a }
  show fderiv ℂ (fun w => fderiv ℂ F w (LY w)) z (X * z) -
      fderiv ℂ (fun w => fderiv ℂ F w (LX w)) z (Y * z) = fderiv ℂ F z ((Y * X - X * Y) * z)
  erw [(hd.clm_apply LY.hasFDerivAt).fderiv, (hd.clm_apply LX.hasFDerivAt).fderiv]
  show fderiv ℂ F z (Y * (X * z)) + fderiv ℂ (fderiv ℂ F) z (X * z) (Y * z) -
      (fderiv ℂ F z (X * (Y * z)) + fderiv ℂ (fderiv ℂ F) z (Y * z) (X * z)) = _
  rw [show fderiv ℂ (fderiv ℂ F) z (X * z) (Y * z) = fderiv ℂ (fderiv ℂ F) z (Y * z) (X * z) from
    hs (X * z) (Y * z)]
  rw [Matrix.sub_mul, map_sub, Matrix.mul_assoc, Matrix.mul_assoc]
  abel

theorem eOp_comm (X Y : Matrix (Fin n) (Fin n) ℂ) :
    eOp X * eOp Y - eOp Y * eOp X = eOp (Y * X - X * Y) := by
  apply LinearMap.ext; intro F
  apply Subtype.ext; funext z
  show ltOp X (ltOp Y F) z - ltOp Y (ltOp X F) z = ltOp (Y * X - X * Y) F z
  by_cases hz : z ∈ OmegaSet n
  · rw [ltOp_of_mem _ hz, ltOp_of_mem _ hz, ltOp_of_mem _ hz,
      lhol_congr (fun w hw => ltOp_of_mem F hw) hz, lhol_congr (fun w hw => ltOp_of_mem F hw) hz]
    exact Lhol_commutator_on_OmegaSet F.2 X Y hz
  · rw [ltOp_of_not_mem _ hz, ltOp_of_not_mem _ hz, ltOp_of_not_mem _ hz, sub_zero]

theorem isGlRep_eOp (X : Fin n → Fin n → Matrix (Fin n) (Fin n) ℂ)
    (hX : ∀ a b c d, X c d * X a b - X a b * X c d =
      (if b = c then X a d else 0) - (if d = a then X c b else 0)) :
    IsGlRep (fun a b => eOp (X a b)) := by
  intro a b c d
  rw [eOp_comm, hX a b c d, eOp_sub]
  split_ifs <;> simp [eOp_zero]

theorem opPow_eqOn (X Y : Fin n → Fin n → Matrix (Fin n) (Fin n) ℂ) (σ : Equiv.Perm (Fin n)) (c : ℂ)
    (hY : ∀ a b, Y a b = c • X (σ a) (σ b)) (F : Matrix (Fin n) (Fin n) ℂ → ℂ) (G : smoothS n)
    (hFG : Set.EqOn F G (OmegaSet n)) (k : ℕ) (a b : Fin n) :
    Set.EqOn (opPow (fun a b => Lhol (Y a b)) k a b F)
      (fun z => c ^ k * ((ePow (fun a b => eOp (X a b)) k (σ a) (σ b) G : smoothS n) :
        Matrix (Fin n) (Fin n) ℂ → ℂ) z) (OmegaSet n) := by
  unfold ePow
  simp only [Bl.ThirdBlockLemmaA.goal1]
  induction k generalizing a b with
  | zero =>
    intro z hz
    by_cases hab : a = b
    · subst hab
      simp [opPow, Matrix.one_apply, hFG hz]
    · have hs : σ a ≠ σ b := fun h => hab (σ.injective h)
      simp [opPow, Matrix.one_apply, hab, hs]
  | succ k ih =>
    intro z hz
    have hterm : ∀ d, Lhol (Y a d) (opPow (fun a b => Lhol (Y a b)) k d b F) z =
        c ^ (k + 1) * ((eOp (X (σ a) (σ d)) ((((Matrix.of fun a b => eOp (X a b)) ^ k) (σ d) (σ b)) G) :
          smoothS n) : Matrix (Fin n) (Fin n) ℂ → ℂ) z := by
      intro d
      set g : smoothS n := (((Matrix.of fun a b => eOp (X a b)) ^ k) (σ d) (σ b)) G with hg
      rw [lhol_congr (ih d b) hz, eOp_apply, ltOp_of_mem _ hz]
      show fderiv ℂ (fun w => c ^ k * (g : Matrix (Fin n) (Fin n) ℂ → ℂ) w) z (Y a d * z) =
        c ^ (k + 1) * fderiv ℂ (g : Matrix (Fin n) (Fin n) ℂ → ℂ) z (X (σ a) (σ d) * z)
      erw [fderiv_const_mul (differentiableAt_of_mem g.2 hz) (c ^ k)]
      rw [hY a d, Matrix.smul_mul]
      show c ^ k * fderiv ℂ (g : Matrix (Fin n) (Fin n) ℂ → ℂ) z (c • (X (σ a) (σ d) * z)) = _
      rw [map_smul, smul_eq_mul]
      ring
    simp only [opPow, Finset.sum_apply]
    rw [Finset.sum_congr rfl fun d _ => hterm d, pow_succ' (Matrix.of fun a b => eOp (X a b)) k,
      Matrix.mul_apply]
    simp only [LinearMap.sum_apply, Submodule.coe_sum, Finset.sum_apply, Module.End.mul_apply,
      Matrix.of_apply, Finset.mul_sum]
    exact Fintype.sum_equiv σ _ _ (fun d => rfl)

theorem opGelfand_eq (X Y : Fin n → Fin n → Matrix (Fin n) (Fin n) ℂ) (σ : Equiv.Perm (Fin n)) (c : ℂ)
    (hY : ∀ a b, Y a b = c • X (σ a) (σ b)) (F : Matrix (Fin n) (Fin n) ℂ → ℂ) (G : smoothS n)
    (hFG : Set.EqOn F G (OmegaSet n)) (k : ℕ) {z : Matrix (Fin n) (Fin n) ℂ} (hz : z ∈ OmegaSet n) :
    opGelfand (fun a b => Lhol (Y a b)) k F z =
      c ^ k * ((gelfand (fun a b => eOp (X a b)) k G : smoothS n) : Matrix (Fin n) (Fin n) ℂ → ℂ) z := by
  simp only [opGelfand, gelfand, Finset.sum_apply, LinearMap.sum_apply, Submodule.coe_sum,
    Finset.mul_sum]
  exact Fintype.sum_equiv σ (fun a => opPow (fun a b => Lhol (Y a b)) k a a F z)
    (fun a => c ^ k * ((ePow (fun a b => eOp (X a b)) k a a G : smoothS n) :
      Matrix (Fin n) (Fin n) ℂ → ℂ) z)
    fun a => opPow_eqOn X Y σ c hY F G hFG k a a hz

end ReciprocityTheory.ChartRestriction.DS.S7
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.LocalB
section
noncomputable section

open Matrix Filter Topology Set

namespace ReciprocityTheory.ChartRestriction.DS.S7

open ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ} {ε : Fin n → Bool} {Λ : Fin n → ℝ}

section PathL
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

lemma lcB_path (z Y : Matrix (Fin n) (Fin n) ℂ) :
    HasDerivAt (fun s : ℝ => z * NormedSpace.exp ((s : ℂ) • Y)) (z * Y) 0 := by
  have h1 := hasDerivAt_exp_smul_const Y ((0 : ℝ) : ℂ)
  have hof : HasDerivAt (fun y : ℝ => (y : ℂ)) 1 (0 : ℝ) := Complex.ofRealCLM.hasDerivAt
  have h2 := HasDerivAt.scomp (h := fun y : ℝ => (y : ℂ)) (0 : ℝ) h1 hof
  have h3 := h2.const_mul z
  exact h3.congr_deriv (by simp)

end PathL

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

lemma lcB_hasDerivAt (T : KType ε Λ) (μ : Fin n → ℤ) {U : Set (Matrix (Fin n) (Fin n) ℂ)} (hUo : IsOpen U)
    (hdiff : DifferentiableOn ℂ (psM T μ) U) {Y : Matrix (Fin n) (Fin n) ℂ}
    (hid : ∀ z ∈ U, fderiv ℂ (psM T μ) z (z * Y) = -(T.dτ Y * psM T μ z))
    (hY : inK ε Y) (γ : ℝ → KG ε)
    (hγ : ∀ t : ℝ, toMK (γ t) = NormedSpace.exp ((t : ℂ) • Y)) (hmul : ∀ s t, γ (s + t) = γ s * γ t)
    (A : Matrix (Fin n) (Fin n) ℂ) {t : ℝ} (ht : A * NormedSpace.exp ((t : ℂ) • Y) ∈ U) :
    HasDerivAt (fun s : ℝ => T.op (γ s) * psM T μ (A * NormedSpace.exp ((s : ℂ) • Y))) 0 t := by
  set z := A * NormedSpace.exp ((t : ℂ) • Y) with hz
  have hcomm : ∀ s : ℝ, A * NormedSpace.exp ((s : ℂ) • Y) =
      z * NormedSpace.exp (((s - t : ℝ) : ℂ) • Y) := by
    intro s
    rw [hz, mul_assoc, ← Matrix.exp_add_of_commute _ _
      (((Commute.refl Y).smul_left _).smul_right _), ← add_smul]
    rw [show ((t : ℂ) + ((s - t : ℝ) : ℂ)) = (s : ℂ) by push_cast; ring]
  have h1 := lcB_path z Y
  have h2 := hasDerivAt_iff_tendsto_slope.1 h1
  have h3 : HasDerivAt (fun s : ℝ => z * NormedSpace.exp ((s : ℂ) • Y)) (z * Y) 0 :=
    hasDerivAt_iff_tendsto_slope.2 h2
  have h4 := HasDerivAt.comp_sub_const t t (by rw [sub_self]; exact h3)
  have hp : HasDerivAt (fun s : ℝ => A * NormedSpace.exp ((s : ℂ) • Y)) (z * Y) t := by
    rw [show (fun s : ℝ => A * NormedSpace.exp ((s : ℂ) • Y)) =
      fun s => z * NormedSpace.exp (((s - t : ℝ) : ℂ) • Y) from funext hcomm]
    exact h4
  have hF : HasFDerivAt (psM T μ) (fderiv ℂ (psM T μ) z) z :=
    (hdiff.differentiableAt (hUo.mem_nhds ht)).hasFDerivAt
  have hF' : HasFDerivAt (psM T μ) ((fderiv ℂ (psM T μ) z).restrictScalars ℝ) z :=
    hF.restrictScalars ℝ
  have hq0 := hF'.comp_hasDerivAt t hp
  have e : ((fderiv ℂ (psM T μ) z).restrictScalars ℝ) (z * Y) = -(T.dτ Y * psM T μ z) := hid z ht
  have hq : HasDerivAt (fun s : ℝ => psM T μ (A * NormedSpace.exp ((s : ℂ) • Y)))
      (-(T.dτ Y * psM T μ z)) t := hq0.congr_deriv e
  have ho1 : HasDerivAt (fun s : ℝ => T.op (γ s)) (T.op (γ t) * T.dτ Y) t := by
    have h5 := (T.hasDeriv Y hY γ hγ).const_mul (T.op (γ t))
    have h6 := HasDerivAt.comp_sub_const t t (by rw [sub_self]; exact h5)
    have he : (fun s : ℝ => T.op (γ s)) =
        fun s => T.op (γ t) * ((T.τ (γ (s - t)) : unitary (T.V →L[ℂ] T.V)) : T.V →L[ℂ] T.V) := by
      funext s
      have hs := hmul t (s - t)
      rw [show t + (s - t) = s by ring] at hs
      simp only [KType.op]
      rw [hs, map_mul]
      rfl
    rw [he]
    exact h6
  have hprod := ho1.mul hq
  have hzero : T.op (γ t) * T.dτ Y * psM T μ (A * NormedSpace.exp ((t : ℂ) • Y)) +
      T.op (γ t) * -(T.dτ Y * psM T μ z) = 0 := by
    rw [mul_neg, mul_assoc]
    exact add_neg_cancel _
  exact hzero ▸ hprod

theorem lcB_const (T : KType ε Λ) (μ : Fin n → ℤ) {U : Set (Matrix (Fin n) (Fin n) ℂ)} (hUo : IsOpen U)
    (hdiff : DifferentiableOn ℂ (psM T μ) U) {Y : Matrix (Fin n) (Fin n) ℂ}
    (hid : ∀ z ∈ U, fderiv ℂ (psM T μ) z (z * Y) = -(T.dτ Y * psM T μ z))
    (hY : inK ε Y) (γ : ℝ → KG ε)
    (hγ : ∀ t : ℝ, toMK (γ t) = NormedSpace.exp ((t : ℂ) • Y)) (hmul : ∀ s t, γ (s + t) = γ s * γ t)
    (A : Matrix (Fin n) (Fin n) ℂ) (hpath : ∀ t ∈ Icc (0 : ℝ) 1, A * NormedSpace.exp ((t : ℂ) • Y) ∈ U) :
    T.op (γ 1) * psM T μ (A * NormedSpace.exp Y) = psM T μ A := by
  have h0 : γ 0 = 1 := by simpa using hmul 0 0
  let g : ℝ → T.V →L[ℂ] T.V := fun t => T.op (γ t) * psM T μ (A * NormedSpace.exp ((t : ℂ) • Y))
  have hd : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt g 0 t := fun t ht =>
    lcB_hasDerivAt T μ hUo hdiff hid hY γ hγ hmul A (hpath t ht)
  have hcont : ContinuousOn g (Icc 0 1) := fun t ht => (hd t ht).continuousAt.continuousWithinAt
  have hc := constant_of_has_deriv_right_zero hcont
    (fun t ht => (hd t (Ico_subset_Icc_self ht)).hasDerivWithinAt) 1 ⟨zero_le_one, le_rfl⟩
  simpa [g, h0, KType.op] using hc

end ReciprocityTheory.ChartRestriction.DS.S7
end
end

