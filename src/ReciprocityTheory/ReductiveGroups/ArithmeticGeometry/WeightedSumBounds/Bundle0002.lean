module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.TangentEqLcZero
public import ReciprocityTheory.DualLattices.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.PtOrderProdSub
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.PtCoeffSingleSubst

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.EqZeroOfVecMulTmat
section
namespace ReciprocityTheory.ChartRestriction.G.Sh.PTb

open MvPowerSeries ReciprocityTheory.PGsh

noncomputable section

variable {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)} {d : ℕ}

def tmat (γ : Fin d → Fin d → PowerSeries C) : Matrix (Fin d) (Fin d) C :=
  Matrix.of fun a b => tangent (γ a) b

theorem sum_smul_tangent (γ : Fin d → Fin d → PowerSeries C) (x : Fin d → C) :
    ∑ b, x b • tangent (γ b) = Matrix.vecMul x (tmat γ) := by
  funext c
  simp [Matrix.vecMul, dotProduct, tmat, Finset.sum_apply]

theorem tmat_det_ne_zero {γ : Fin d → Fin d → PowerSeries C} (hdet : v (tmat γ).det = 0) :
    (tmat γ).det ≠ 0 := by
  intro h
  rw [h] at hdet
  simp at hdet

theorem tmat_isUnit_det {γ : Fin d → Fin d → PowerSeries C} (hdet : v (tmat γ).det = 0) :
    IsUnit (tmat γ).det := isUnit_iff_ne_zero.mpr (tmat_det_ne_zero hdet)

theorem isIntV_tmat_inv {γ : Fin d → Fin d → PowerSeries C} (hγ : ∀ a, IsCurve v (γ a))
    (hdet : v (tmat γ).det = 0) (i j : Fin d) : IsIntV v ((tmat γ)⁻¹ i j) := by
  let S : Subring C :=
    { carrier := {x | 0 ≤ v x}
      mul_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq, AddValuation.map_mul] at *
        exact add_nonneg ha hb
      one_mem' := by simp
      add_mem' := fun {a b} ha hb => le_trans (le_min ha hb) (AddValuation.map_add v a b)
      zero_mem' := by simp
      neg_mem' := fun {a} ha => by simpa [AddValuation.map_neg] using ha }
  have hent : ∀ a b, tmat γ a b ∈ S := fun a b => by
    show 0 ≤ v (tmat γ a b)
    exact (hγ a b).2 1
  let M' : Matrix (Fin d) (Fin d) S := fun a b => ⟨tmat γ a b, hent a b⟩
  have hM : tmat γ = S.subtype.mapMatrix M' := by
    ext a b
    rfl
  have hadj : ∀ i j, (tmat γ).adjugate i j ∈ S := by
    intro i j
    rw [hM, ← RingHom.map_adjugate]
    first
    | exact (M'.adjugate i j).2
    | simp
  have hdet_inv : v ((tmat γ).det⁻¹) = 0 := by
    have h1 : v ((tmat γ).det⁻¹ * (tmat γ).det) = 0 := by
      rw [inv_mul_cancel₀ (tmat_det_ne_zero hdet), AddValuation.map_one]
    rwa [AddValuation.map_mul, hdet, add_zero] at h1
  show 0 ≤ v ((tmat γ)⁻¹ i j)
  rw [Matrix.inv_def, Ring.inverse_eq_inv, Matrix.smul_apply, smul_eq_mul, AddValuation.map_mul,
    hdet_inv, zero_add]
  exact hadj i j

theorem vecMul_inv_tmat {γ : Fin d → Fin d → PowerSeries C} (hdet : v (tmat γ).det = 0)
    (w : Fin d → C) : Matrix.vecMul (Matrix.vecMul w (tmat γ)⁻¹) (tmat γ) = w := by
  rw [Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ (tmat_isUnit_det hdet), Matrix.vecMul_one]

theorem eq_zero_of_vecMul_tmat {γ : Fin d → Fin d → PowerSeries C} (hdet : v (tmat γ).det = 0)
    {x : Fin d → C} (h : Matrix.vecMul x (tmat γ) = 0) : x = 0 := by
  have h2 := congrArg (fun w => Matrix.vecMul w (tmat γ)⁻¹) h
  simp only [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ (tmat_isUnit_det hdet),
    Matrix.vecMul_one, Matrix.zero_vecMul] at h2
  exact h2

theorem isIntV_vecMul_inv {γ : Fin d → Fin d → PowerSeries C} (hγ : ∀ a, IsCurve v (γ a))
    (hdet : v (tmat γ).det = 0) {w : Fin d → C} (hw : ∀ c, IsIntV v (w c)) (b : Fin d) :
    IsIntV v (Matrix.vecMul w (tmat γ)⁻¹ b) := by
  let S : Subring C :=
    { carrier := {x | 0 ≤ v x}
      mul_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq, AddValuation.map_mul] at *
        exact add_nonneg ha hb
      one_mem' := by simp
      add_mem' := fun {a b} ha hb => le_trans (le_min ha hb) (AddValuation.map_add v a b)
      zero_mem' := by simp
      neg_mem' := fun {a} ha => by simpa [AddValuation.map_neg] using ha }
  have hmem : Matrix.vecMul w (tmat γ)⁻¹ b ∈ S := by
    simp only [Matrix.vecMul, dotProduct]
    exact S.sum_mem fun c _ => S.mul_mem (hw c) (isIntV_tmat_inv hγ hdet c b)
  exact hmem

theorem vecMul_tmat_support {h : ℕ} (ty : Fin d → ZMod h) {γ : Fin d → Fin d → PowerSeries C}
    (hdet : v (tmat γ).det = 0) (ht : ∀ b c, ty c ≠ ty b → tangent (γ b) c = 0)
    (x : Fin d → C) (τ : ZMod h) (hw : ∀ c, ty c ≠ τ → Matrix.vecMul x (tmat γ) c = 0) :
    ∀ b, ty b ≠ τ → x b = 0 := by
  intro b hb
  set x' : Fin d → C := fun b => if ty b ≠ τ then x b else 0 with hx'
  have hz : Matrix.vecMul x' (tmat γ) = 0 := by
    funext c
    simp only [Matrix.vecMul, dotProduct, Pi.zero_apply]
    by_cases hc : ty c = τ
    · apply Finset.sum_eq_zero
      intro b' _
      by_cases hb' : ty b' ≠ τ
      · have h0 : tangent (γ b') c = 0 := ht b' c (by rw [hc]; exact fun h => hb' h.symm)
        simp [hx', hb', tmat, h0]
      · simp [hx', hb']
    · have h0 := hw c hc
      simp only [Matrix.vecMul, dotProduct] at h0
      rw [← h0]
      apply Finset.sum_congr rfl
      intro b' _
      by_cases hb' : ty b' ≠ τ
      · simp [hx', hb']
      · have hb2 : ty b' = τ := not_not.mp hb'
        have h1 : tangent (γ b') c = 0 := ht b' c (by rw [hb2]; exact hc)
        simp [hx', hb', tmat, h1]
  have h3 := congrFun (eq_zero_of_vecMul_tmat hdet hz) b
  simpa [hx', hb] using h3

end

end ReciprocityTheory.ChartRestriction.G.Sh.PTb
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.OmBStatement
section
namespace ReciprocityTheory.ChartRestriction.G.Sh

open ReciprocityTheory.PGsh

noncomputable section

private theorem key {C : Type} [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ))
    (lg P : PowerSeries C) (Ω b : C) (M : ℕ) (hM : 2 ≤ M) (β φ r : ℝ) (hβ : 0 < β)
    (hb : v b = β) (hfac : v (M.factorial : C) = φ) (hr : v Ω = r) (hrβ : r < β)
    (hl0 : PowerSeries.coeff 0 lg = 0) (hl1 : PowerSeries.coeff 1 lg = 1)
    (hlg : ∀ j, 2 ≤ j → j < M → PowerSeries.coeff j lg = 0)
    (hsub : PowerSeries.subst P lg = b • lg) (hP0 : PowerSeries.coeff 0 P = 0)
    (hP1 : PowerSeries.coeff 1 P = b) (hPg : ∀ j, 2 ≤ j → j < M → PowerSeries.coeff j P = 0)
    (hu : v (PowerSeries.coeff M P) = 0) (hint : PsIsInt v (expComp Ω lg)) :
    r - β = M * r - φ := by
  have hc := PowerSeriesCoeffGaps.coeff_subst_gap lg P M hM b hl0 hl1 hlg hP0 hP1 hPg
  rw [hsub, PowerSeries.coeff_smul, smul_eq_mul] at hc
  have hu' : PowerSeries.coeff M P = PowerSeries.coeff M lg * (b + -b ^ M) := by
    linear_combination -hc
  have hMr : (2 : ℝ) ≤ M := by exact_mod_cast hM
  have hvb : v (-b ^ M) = ((M * β : ℝ) : WithTop ℝ) := by
    rw [v.map_neg, v.map_pow, hb, ← WithTop.coe_nsmul, nsmul_eq_mul]
  have hd : v (b + -b ^ M) = β := PowerSeriesCoeffGaps.add_eq_of_lt v hb hvb (by nlinarith)
  have hk0 : PowerSeries.coeff M lg ≠ 0 := by
    intro h0
    rw [hu', h0, zero_mul, v.map_zero] at hu
    exact WithTop.top_ne_zero hu
  obtain ⟨s, hs⟩ := PowerSeriesCoeffGaps.exists_real v hk0
  have hs' : s = -β := by
    rw [hu', v.map_mul, hs, hd, ← WithTop.coe_add] at hu
    have := WithTop.coe_eq_zero.mp hu
    linarith
  have hI := hint M
  unfold IsIntV at hI
  rw [PowerSeriesCoeffGaps.coeff_expComp_gap Ω lg M hM hl0 hl1 hlg] at hI
  have hx : v (Ω * PowerSeries.coeff M lg) = ((r + -β : ℝ) : WithTop ℝ) := by
    rw [v.map_mul, hr, hs, hs', WithTop.coe_add]
  have hy : v (Ω ^ M / (M.factorial : C)) = ((M * r - φ : ℝ) : WithTop ℝ) :=
    PowerSeriesCoeffGaps.div_eq_coe v (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero M))
      (by rw [v.map_pow, hr, ← WithTop.coe_nsmul, nsmul_eq_mul]) hfac
  have := PowerSeriesCoeffGaps.eq_of_nonneg_add v (by linarith) hx hy hI
  linarith

end

end ReciprocityTheory.ChartRestriction.G.Sh
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.PtSolveMapFixedIff
section
namespace ReciprocityTheory.ChartRestriction.G.Sh

open MvPowerSeries ReciprocityTheory.PGsh

open Classical

noncomputable section

variable {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)}

def PTGood (v : AddValuation C (WithTop ℝ)) {ι τ : Type*} (x : ι → MvPowerSeries τ C) : Prop :=
  ∀ i, constantCoeff (x i) = 0 ∧ x i ∈ ptIntSer v τ

theorem ptGood_zero {ι τ : Type*} : PTGood v (0 : ι → MvPowerSeries τ C) := fun _ => ⟨map_zero _, zero_mem _⟩

theorem ptGood_lim {ι τ : Type*} {T : (ι → MvPowerSeries τ C) → (ι → MvPowerSeries τ C)}
    (hP : ∀ n, PTGood v (T^[n] 0)) (x : ι → MvPowerSeries τ C)
    (hx : ∀ n, PTAgree n x (T^[n] 0)) : PTGood v x := by
  intro i
  have hc : ∀ e, coeff e (x i) = coeff e ((T^[e.degree + 1] 0) i) :=
    fun e => hx (e.degree + 1) i e (Nat.lt_succ_self _)
  refine ⟨?_, ?_⟩
  · rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hc,
      MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact (hP _ i).1
  · show ∀ α, coeff α (x i) ∈ ptIntSub v
    intro α
    have h : ∀ β, coeff β ((T^[α.degree + 1] 0) i) ∈ ptIntSub v := (hP _ i).2
    rw [hc]
    exact h α

theorem pt_subst_lin_split {σ τ : Type*} [Fintype σ] {x : σ → MvPowerSeries τ C}
    (hx : HasSubst x) (Φ : MvPowerSeries σ C) (m : σ → C) :
    subst x Φ = ∑ a, m a • x a + subst x (Φ - ∑ a, m a • X a) := by
  have hs : subst x (∑ a, m a • X a : MvPowerSeries σ C) = ∑ a, m a • x a := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← MvPowerSeries.coe_substAlgHom hx, map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [MvPowerSeries.coe_substAlgHom hx, MvPowerSeries.subst_smul hx, MvPowerSeries.subst_X hx]
  rw [MvPowerSeries.subst_sub hx, hs]
  abel

theorem pt_low_of_lin {σ : Type*} [Fintype σ] {Φ : MvPowerSeries σ C}
    (h0 : constantCoeff Φ = 0) (m : σ → C)
    (hm : ∀ s, coeff (Finsupp.single s 1) Φ = m s) :
    ∀ α : σ →₀ ℕ, α.degree ≤ 1 → coeff α (Φ - ∑ a, m a • X a) = 0 := by
  intro α hα
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sub, map_sum]
  simp only [map_smul, smul_eq_mul]
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hα with h | h
  · obtain rfl := (Finsupp.degree_eq_zero_iff α).mp h
    simp [MvPowerSeries.coeff_X, MvPowerSeries.coeff_zero_eq_constantCoeff_apply, h0]
    refine Finset.sum_eq_zero fun a _ => if_neg ?_
    exact fun e => (Finsupp.single_ne_zero.mpr one_ne_zero) e.symm
  · have hne : α ≠ 0 := by
      rintro rfl
      simp at h
    obtain ⟨s, hs⟩ := Finsupp.ne_iff.mp hne
    simp only [Finsupp.coe_zero, Pi.zero_apply] at hs
    have hle : Finsupp.single s 1 ≤ α := by
      rw [Finsupp.le_def]
      intro i
      by_cases hi : i = s
      · subst hi
        simp only [Finsupp.single_eq_same]
        omega
      · simp [Finsupp.single_apply, Ne.symm hi]
    have hadd := add_tsub_cancel_of_le hle
    have hd := congrArg Finsupp.degree hadd
    rw [map_add (f := _), Finsupp.degree_single, h] at hd
    have h0' : α - Finsupp.single s 1 = 0 := (Finsupp.degree_eq_zero_iff _).mp (by omega)
    rw [← hadd, h0', add_zero]
    simp [MvPowerSeries.coeff_X, hm, Finsupp.single_left_inj one_ne_zero]

section Solve

variable {d : ℕ} {σ τ : Type*} [Finite σ]
  (A : (Fin d → MvPowerSeries τ C) → σ → MvPowerSeries τ C)
  (K : Fin d → MvPowerSeries σ C) (M N : Matrix (Fin d) (Fin d) C)
  (f : Fin d → MvPowerSeries τ C)

def ptSolveMap (x : Fin d → MvPowerSeries τ C) : Fin d → MvPowerSeries τ C :=
  fun c => ∑ b, N b c • (f b - subst (A x) (K b))

private lemma sum_smul_sum_smul_eq_of_mul_eq_one (P Q : Matrix (Fin d) (Fin d) C) (hPQ : P * Q = 1)
    (z : Fin d → MvPowerSeries τ C) (c : Fin d) : ∑ b, Q b c • ∑ a, P a b • z a = z c := by
  simp_rw [Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_smul]
  have e : ∀ a, ∑ b, Q b c * P a b = (P * Q) a c := fun a => by
    rw [Matrix.mul_apply]
    exact Finset.sum_congr rfl fun b _ => mul_comm _ _
  simp_rw [e, hPQ, Matrix.one_apply, ite_smul, one_smul, zero_smul]
  simp

theorem ptSolveMap_fixed_iff (hNM : N * M = 1) (hMN : M * N = 1)
    (x : Fin d → MvPowerSeries τ C) :
    ptSolveMap A K N f x = x ↔ ∀ b, ∑ a, M a b • x a + subst (A x) (K b) = f b := by
  constructor
  · intro hx b
    have e := sum_smul_sum_smul_eq_of_mul_eq_one N M hNM (fun c => f c - subst (A x) (K c)) b
    have hx' : ∀ a, ∑ c, N c a • (f c - subst (A x) (K c)) = x a := fun a => congrFun hx a
    simp_rw [hx'] at e
    rw [e]
    abel
  · intro h
    funext c
    have hy : ∀ b, f b - subst (A x) (K b) = ∑ a, M a b • x a := fun b => by
      rw [← h b]
      abel
    simp only [ptSolveMap]
    simp_rw [hy]
    exact sum_smul_sum_smul_eq_of_mul_eq_one M N hMN x c

variable {A K}

theorem ptSolveMap_agree
    (hA0 : ∀ x, PTGood v x → ∀ s, constantCoeff (A x s) = 0)
    (hAag : ∀ k x y, PTGood v x → PTGood v y → PTAgree k x y →
      ∀ s (e : τ →₀ ℕ), e.degree < k → coeff e (A x s) = coeff e (A y s))
    (hK : ∀ b α, coeff α (K b) ≠ 0 → 2 ≤ α.degree ∨
      ∀ x y, PTGood v x → PTGood v y → ∀ s ∈ α.support, A x s = A y s)
    (k : ℕ) (x y : Fin d → MvPowerSeries τ C) (hx : PTGood v x) (hy : PTGood v y)
    (hxy : PTAgree k x y) :
    PTAgree (k + 1) (ptSolveMap A K N f x) (ptSolveMap A K N f y) := by
  intro c e he
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [ptSolveMap, map_sum, coeff_smul, map_sub]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [pt_subst_agree (hasSubst_of_constantCoeff_zero (hA0 x hx))
    (hasSubst_of_constantCoeff_zero (hA0 y hy)) (hA0 x hx) (hA0 y hy) (K b) k
    (hAag k x y hx hy hxy) (fun α hα => (hK b α hα).imp id (fun h => h x y hx hy)) e he]

theorem ptSolveMap_good (hN : ∀ i j, N i j ∈ ptIntSub v) (hf : PTGood v f)
    (hA0 : ∀ x, PTGood v x → ∀ s, constantCoeff (A x s) = 0)
    (hAi : ∀ x, PTGood v x → ∀ s, A x s ∈ ptIntSer v τ)
    (hKi : ∀ b, K b ∈ ptIntSer v σ) (hK0 : ∀ b, constantCoeff (K b) = 0)
    (x : Fin d → MvPowerSeries τ C) (hx : PTGood v x) :
    PTGood v (ptSolveMap A K N f x) := by
  intro c
  have hs := hasSubst_of_constantCoeff_zero (hA0 x hx)
  refine ⟨?_, ?_⟩
  · rw [← coeff_zero_eq_constantCoeff_apply]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [ptSolveMap, map_sum, coeff_smul, map_sub, coeff_zero_eq_constantCoeff_apply,
      (hf _).1, constantCoeff_subst_eq_zero hs (hA0 x hx) (hK0 _), sub_zero, mul_zero,
      Finset.sum_const_zero]
  · exact Subring.sum_mem _ fun b _ => ptIntSer_smul (hN b c)
      (Subring.sub_mem _ (hf b).2 (ptIntSer_subst hs (hAi x hx) (hKi b)))

theorem pt_solve (hNM : N * M = 1) (hMN : M * N = 1) (hN : ∀ i j, N i j ∈ ptIntSub v)
    (hf : PTGood v f)
    (hA0 : ∀ x, PTGood v x → ∀ s, constantCoeff (A x s) = 0)
    (hAi : ∀ x, PTGood v x → ∀ s, A x s ∈ ptIntSer v τ)
    (hAag : ∀ k x y, PTGood v x → PTGood v y → PTAgree k x y →
      ∀ s (e : τ →₀ ℕ), e.degree < k → coeff e (A x s) = coeff e (A y s))
    (hK : ∀ b α, coeff α (K b) ≠ 0 → 2 ≤ α.degree ∨
      ∀ x y, PTGood v x → PTGood v y → ∀ s ∈ α.support, A x s = A y s)
    (hKi : ∀ b, K b ∈ ptIntSer v σ) (hK0 : ∀ b, constantCoeff (K b) = 0) :
    ∃! x : Fin d → MvPowerSeries τ C,
      PTGood v x ∧ ∀ b, ∑ a, M a b • x a + subst (A x) (K b) = f b := by
  have hag : ∀ k (x y : Fin d → MvPowerSeries τ C), PTGood v x → PTGood v y → PTAgree k x y →
      PTAgree (k + 1) (ptSolveMap A K N f x) (ptSolveMap A K N f y) :=
    fun k x y hx hy hxy => ptSolveMap_agree (N := N) (f := f) hA0 hAag hK k x y hx hy hxy
  have hgood : ∀ x, PTGood v x → PTGood v (ptSolveMap A K N f x) :=
    fun x hx => ptSolveMap_good (N := N) (f := f) hN hf hA0 hAi hKi hK0 x hx
  have hzero : ∀ x y : Fin d → MvPowerSeries τ C, PTAgree 0 x y :=
    fun x y i e he => absurd he (Nat.not_lt_zero _)
  have hmono : ∀ k l (x y : Fin d → MvPowerSeries τ C), l ≤ k → PTAgree k x y → PTAgree l x y :=
    fun k l x y hlk h i e he => h i e (lt_of_lt_of_le he hlk)
  have htrans : ∀ k (x y z : Fin d → MvPowerSeries τ C), PTAgree k x y → PTAgree k y z →
      PTAgree k x z :=
    fun k x y z h1 h2 i e he => (h1 i e he).trans (h2 i e he)
  have hit : ∀ n, PTGood v ((ptSolveMap A K N f)^[n] 0) := by
    intro n
    induction n with
    | zero => exact ptGood_zero
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact hgood _ ih
  have hstep : ∀ k, PTAgree k ((ptSolveMap A K N f)^[k] 0) ((ptSolveMap A K N f)^[k + 1] 0) := by
    intro k
    induction k with
    | zero => exact hzero _ _
    | succ k ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply' _ (k + 1)]
      exact hag k _ _ (hit k) (hit (k + 1)) ih
  have hchain : ∀ k m, PTAgree k ((ptSolveMap A K N f)^[k] 0) ((ptSolveMap A K N f)^[k + m] 0) := by
    intro k m
    induction m with
    | zero => exact fun i e he => rfl
    | succ m ih =>
      exact htrans k _ _ _ ih (hmono (k + m) k _ _ (Nat.le_add_right k m) (hstep (k + m)))
  let x : Fin d → MvPowerSeries τ C :=
    fun i e => coeff e ((ptSolveMap A K N f)^[e.degree + 1] 0 i)
  have hx : ∀ n, PTAgree n x ((ptSolveMap A K N f)^[n] 0) := by
    intro n i e he
    show coeff e ((ptSolveMap A K N f)^[e.degree + 1] 0 i) = _
    have hle : e.degree + 1 ≤ n := he
    have h1 := hchain (e.degree + 1) (n - (e.degree + 1))
    rw [Nat.add_sub_cancel' hle] at h1
    exact h1 i e (Nat.lt_succ_self _)
  have hxg : PTGood v x := ptGood_lim hit x hx
  have hfix : ptSolveMap A K N f x = x := by
    apply PTAgree.eq
    intro k
    cases k with
    | zero => exact hzero _ _
    | succ k =>
      have h1 : PTAgree (k + 1) (ptSolveMap A K N f x) ((ptSolveMap A K N f)^[k + 1] 0) := by
        rw [Function.iterate_succ_apply']
        exact hag k _ _ hxg (hit k) (hx k)
      exact htrans _ _ _ _ h1 (fun i e he => ((hx (k + 1)) i e he).symm)
  refine ⟨x, ⟨hxg, (ptSolveMap_fixed_iff (A := A) (K := K) (M := M) (N := N) (f := f)
    hNM hMN x).mp hfix⟩, ?_⟩
  rintro y ⟨hyg, hy⟩
  have hyfix := (ptSolveMap_fixed_iff (A := A) (K := K) (M := M) (N := N) (f := f)
    hNM hMN y).mpr hy
  apply PTAgree.eq
  intro k
  induction k with
  | zero => exact hzero _ _
  | succ k ih =>
    have h2 := hag k y x hyg hxg ih
    rwa [hyfix, hfix] at h2

end Solve

end

end ReciprocityTheory.ChartRestriction.G.Sh
end

