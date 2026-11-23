module

public import Mathlib

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericLuDecompositionUnique
section
open Matrix

namespace GlobalTheory.CompanionTheory.GenericLU

theorem affine_form_ne_zero {K L : Type} [Field K] [Field L] [Algebra K L] {n : ℕ}
    (a : K) (b : Fin n → K) (x : Fin n → L) (hx : AlgebraicIndependent K x)
    (hab : a ≠ 0 ∨ ∃ j, b j ≠ 0) :
    algebraMap K L a + ∑ j, algebraMap K L (b j) * x j ≠ 0 := by
  classical
  intro h
  let P : MvPolynomial (Fin n) K :=
    MvPolynomial.C a + ∑ j, MvPolynomial.C (b j) * MvPolynomial.X j
  have hP : MvPolynomial.aeval x P = 0 := by
    set_option synthInstance.maxHeartbeats 100000 in
      simpa [P, map_add (f := _), map_sum, map_mul, MvPolynomial.aeval_C, MvPolynomial.aeval_X] using h
  have hP0 : P = 0 := by
    have := (injective_iff_map_eq_zero (MvPolynomial.aeval x : MvPolynomial (Fin n) K →ₐ[K] L)).mp hx
    exact this P hP
  rcases hab with ha | ⟨j, hj⟩
  · apply ha
    have := congrArg (AddMonoidAlgebra.coeff · 0) hP0
    simpa [P, MvPolynomial.coeff_add, MvPolynomial.coeff_sum, MvPolynomial.coeff_C_mul,
      MvPolynomial.coeff_C, MvPolynomial.coeff_X'] using this
  · apply hj
    have := congrArg (AddMonoidAlgebra.coeff · (Finsupp.single j 1)) hP0
    have hne : (0 : Fin n →₀ ℕ) ≠ Finsupp.single j 1 :=
      (Finsupp.single_ne_zero.mpr one_ne_zero).symm
    simpa [P, hne, MvPolynomial.coeff_add, MvPolynomial.coeff_sum, MvPolynomial.coeff_C_mul,
      MvPolynomial.coeff_C, MvPolynomial.coeff_X', Finsupp.single_left_inj, Finsupp.single_eq_single_iff] using this

theorem schur_det_ne_zero {F : Type} [Field F] {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) F)
    (x : Fin n → F) (hA : A.det ≠ 0) (q : Fin (n + 1) → F)
    (hq : ∀ i, q i = A i 0 + ∑ k, A i k.succ * x k) (h0 : q 0 ≠ 0) :
    (Matrix.of fun i j : Fin n => A i.succ j.succ - q i.succ / q 0 * A 0 j.succ).det ≠ 0 := by
  intro hdet
  obtain ⟨y, hy, hSy⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  set t : F := -(∑ j, A 0 j.succ * y j) / q 0 with ht
  apply hA
  refine Matrix.exists_mulVec_eq_zero_iff.mp
    ⟨Fin.cons t (fun k => y k + t * x k), ?_, ?_⟩
  · intro hz
    have h1 : t = 0 := by simpa using congrFun hz 0
    apply hy
    funext k
    have := congrFun hz k.succ
    simpa [h1] using this
  · have key : ∀ i, (A *ᵥ (Fin.cons t (fun k => y k + t * x k) : Fin (n + 1) → F)) i
        = t * q i + ∑ k, A i k.succ * y k := by
      intro i
      simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, hq,
        mul_add, Finset.sum_add_distrib, Finset.mul_sum]
      have : ∀ k, A i k.succ * (t * x k) = t * (A i k.succ * x k) := fun k => by ring
      simp only [this]
      ring
    funext i
    rw [key]
    refine Fin.cases ?_ (fun i => ?_) i
    · simp only [ht, Pi.zero_apply]
      field_simp
      ring
    · have h := congrFun hSy i
      simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.zero_apply, sub_mul,
        Finset.sum_sub_distrib, mul_assoc, ← Finset.mul_sum] at h
      simp only [ht, Pi.zero_apply]
      field_simp at h ⊢
      linear_combination h

theorem lu_step {L : Type} [Field L] {n : ℕ} (M : Matrix (Fin (n + 1)) (Fin (n + 1)) L)
    (hM : M 0 0 ≠ 0) (v' w' : Matrix (Fin n) (Fin n) L)
    (hsch : ∀ i j, M i.succ j.succ - M i.succ 0 / M 0 0 * M 0 j.succ = (v' * w') i j)
    (h1 : ∀ k, v' k k = 1) (h2 : ∀ l k, l < k → v' l k = 0)
    (h3 : ∀ l k, k < l → w' l k = 0) (h4 : ∀ k, w' k k ≠ 0) :
    ∃ v w : Matrix (Fin (n + 1)) (Fin (n + 1)) L, M = v * w ∧ (∀ k, v k k = 1) ∧
      (∀ l k, l < k → v l k = 0) ∧ (∀ l k, k < l → w l k = 0) ∧ ∀ k, w k k ≠ 0 := by
  let v : Matrix (Fin (n + 1)) (Fin (n + 1)) L := fun i j =>
    Fin.cases (Fin.cases 1 (fun _ => 0) j)
      (fun i' => Fin.cases (M i'.succ 0 / M 0 0) (fun j' => v' i' j') j) i
  let w : Matrix (Fin (n + 1)) (Fin (n + 1)) L := fun i j =>
    Fin.cases (Fin.cases (M 0 0) (fun j' => M 0 j'.succ) j)
      (fun i' => Fin.cases 0 (fun j' => w' i' j') j) i
  have v00 : v 0 0 = 1 := rfl
  have v0s : ∀ j, v 0 (Fin.succ j) = 0 := fun _ => rfl
  have vs0 : ∀ i, v (Fin.succ i) 0 = M i.succ 0 / M 0 0 := fun _ => rfl
  have vss : ∀ i j, v (Fin.succ i) (Fin.succ j) = v' i j := fun _ _ => rfl
  have w00 : w 0 0 = M 0 0 := rfl
  have w0s : ∀ j, w 0 (Fin.succ j) = M 0 j.succ := fun _ => rfl
  have ws0 : ∀ i, w (Fin.succ i) 0 = 0 := fun _ => rfl
  have wss : ∀ i j, w (Fin.succ i) (Fin.succ j) = w' i j := fun _ _ => rfl
  refine ⟨v, w, ?_, ?_, ?_, ?_, ?_⟩
  · ext i j
    rw [Matrix.mul_apply, Fin.sum_univ_succ]
    refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
    · simp [v00, v0s, w00]
    · simp [v00, v0s, w0s]
    · simp [vs0, vss, w00, ws0]
      field_simp
    · have := hsch i j
      rw [Matrix.mul_apply] at this
      simp only [vs0, vss, w0s, wss]
      rw [← this]
      ring
  · intro k
    refine Fin.cases ?_ (fun k => ?_) k
    · exact v00
    · rw [vss]; exact h1 k
  · intro l k
    refine Fin.cases ?_ (fun l => ?_) l <;> refine Fin.cases ?_ (fun k => ?_) k
    · intro h; exact absurd h (lt_irrefl _)
    · intro _; exact v0s k
    · intro h; exact absurd h (Fin.not_lt_zero _)
    · intro h; rw [vss]; exact h2 l k (Fin.succ_lt_succ_iff.mp h)
  · intro l k
    refine Fin.cases ?_ (fun l => ?_) l <;> refine Fin.cases ?_ (fun k => ?_) k
    · intro h; exact absurd h (lt_irrefl _)
    · intro h; exact absurd h (Fin.not_lt_zero _)
    · intro _; exact ws0 l
    · intro h; rw [wss]; exact h3 l k (Fin.succ_lt_succ_iff.mp h)
  · intro k
    refine Fin.cases ?_ (fun k => ?_) k
    · rw [w00]; exact hM
    · rw [wss]; exact h4 k

theorem generic_lu_decomposition_exists (n : ℕ) : ∀ (K L : Type) [Field K] [Field L] [Algebra K L]
    (A : Matrix (Fin n) (Fin n) K) (u : Matrix (Fin n) (Fin n) L), A.det ≠ 0 →
    (∀ k, u k k = 1) → (∀ l k, l < k → u l k = 0) →
    AlgebraicIndependent K (fun q : {lk : Fin n × Fin n // lk.2 < lk.1} => u q.1.1 q.1.2) →
    ∃ v w : Matrix (Fin n) (Fin n) L, A.map (algebraMap K L) * u = v * w ∧ (∀ k, v k k = 1) ∧
      (∀ l k, l < k → v l k = 0) ∧ (∀ l k, k < l → w l k = 0) ∧ ∀ k, w k k ≠ 0 := by
  induction n with
  | zero =>
    intro K L _ _ _ A u _ _ _ _
    exact ⟨0, 0, Subsingleton.elim _ _, fun k => k.elim0, fun l => l.elim0, fun l => l.elim0,
      fun k => k.elim0⟩
  | succ n ih =>
    intro K L _ _ _ A u hA hdiag hup hind
    let x : Fin n → L := fun i => u i.succ 0
    let u' : Matrix (Fin n) (Fin n) L := fun i j => u i.succ j.succ
    let y : {lk : Fin n × Fin n // lk.2 < lk.1} → L := fun q => u' q.1.1 q.1.2
    let idx : {lk : Fin n × Fin n // lk.2 < lk.1} ⊕ Fin n →
        {lk : Fin (n + 1) × Fin (n + 1) // lk.2 < lk.1} :=
      Sum.elim (fun q => ⟨(q.1.1.succ, q.1.2.succ), Fin.succ_lt_succ_iff.mpr q.2⟩)
        (fun i => ⟨(i.succ, 0), Fin.succ_pos i⟩)
    have hidx : Function.Injective idx := by
      rintro (s | i) (s' | i') hh
      · have e : (s.1.1.succ, s.1.2.succ) = (s'.1.1.succ, s'.1.2.succ) :=
          congrArg Subtype.val hh
        exact congrArg Sum.inl (Subtype.ext (Prod.ext
          (Fin.succ_injective _ (congrArg Prod.fst e))
          (Fin.succ_injective _ (congrArg Prod.snd e))))
      · have e : (s.1.1.succ, s.1.2.succ) = (i'.succ, (0 : Fin (n + 1))) :=
          congrArg Subtype.val hh
        exact absurd (congrArg Prod.snd e) (Fin.succ_ne_zero _)
      · have e : (i.succ, (0 : Fin (n + 1))) = (s'.1.1.succ, s'.1.2.succ) :=
          congrArg Subtype.val hh
        exact absurd (congrArg Prod.snd e).symm (Fin.succ_ne_zero _)
      · have e : (i.succ, (0 : Fin (n + 1))) = (i'.succ, (0 : Fin (n + 1))) :=
          congrArg Subtype.val hh
        exact congrArg Sum.inr (Fin.succ_injective _ (congrArg Prod.fst e))
    have hsum : AlgebraicIndependent K (Sum.elim y x) := by
      have := hind.comp idx hidx
      convert this using 1
      funext s
      rcases s with q | i <;> rfl
    obtain ⟨hx, hy⟩ := AlgebraicIndependent.sumElim_iff.mp hsum
    have hy' : AlgebraicIndependent (IntermediateField.adjoin K (Set.range x)) y :=
      IntermediateField.algebraicIndependent_adjoin_iff.mpr hy
    let K₁ := IntermediateField.adjoin K (Set.range x)
    let xs : Fin n → K₁ := fun i => ⟨x i, IntermediateField.subset_adjoin K _ ⟨i, rfl⟩⟩
    let A₁ : Matrix (Fin (n + 1)) (Fin (n + 1)) K₁ := A.map (algebraMap K K₁)
    let q : Fin (n + 1) → K₁ := fun i => A₁ i 0 + ∑ k, A₁ i k.succ * xs k
    have hA₁ : A₁.det ≠ 0 := by
      have : A₁.det = algebraMap K K₁ A.det := by
        simpa [A₁] using (RingHom.map_det (algebraMap K K₁) A).symm
      rw [this]
      exact (map_ne_zero _).mpr hA
    let M : Matrix (Fin (n + 1)) (Fin (n + 1)) L := A.map (algebraMap K L) * u
    have hcoe : ∀ i j, algebraMap K₁ L (A₁ i j) = algebraMap K L (A i j) := fun i j =>
      (IsScalarTower.algebraMap_apply K K₁ L (A i j)).symm
    have hxs : ∀ k, algebraMap K₁ L (xs k) = x k := fun _ => rfl
    have hM0 : ∀ i, M i 0 = algebraMap K₁ L (q i) := by
      intro i
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [M, q, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.map_apply, hdiag, map_add (f := _),
        map_sum, map_mul, hcoe, hxs, mul_one]
      rfl
    have hMs : ∀ i j, M i j.succ = ∑ k, algebraMap K L (A i k.succ) * u' k j := by
      intro i j
      simp only [M, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.map_apply]
      rw [hup 0 j.succ (Fin.succ_pos j)]
      simp [u']
    have hp : M 0 0 ≠ 0 := by
      have hne : A 0 0 ≠ 0 ∨ ∃ j, A 0 (Fin.succ j) ≠ 0 := by
        by_contra hcon
        push_neg at hcon
        apply hA
        apply Matrix.det_eq_zero_of_row_eq_zero 0
        intro j
        refine Fin.cases hcon.1 hcon.2 j
      have := affine_form_ne_zero (A 0 0) (fun j => A 0 j.succ) x hx hne
      have h2 : M 0 0 = algebraMap K L (A 0 0) + ∑ j, algebraMap K L (A 0 j.succ) * x j := by
        simp only [M, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.map_apply, hdiag, mul_one]
        rfl
      rwa [h2]
    have hq0 : q 0 ≠ 0 := by
      intro h
      apply hp
      rw [hM0, h, map_zero]
    let S : Matrix (Fin n) (Fin n) K₁ :=
      Matrix.of fun i j : Fin n => A₁ i.succ j.succ - q i.succ / q 0 * A₁ 0 j.succ
    have hS : S.det ≠ 0 := schur_det_ne_zero A₁ xs hA₁ q (fun _ => rfl) hq0
    obtain ⟨v', w', hvw, h1, h2, h3, h4⟩ := ih K₁ L S u' hS (fun k => hdiag k.succ)
      (fun l k h => hup l.succ k.succ (Fin.succ_lt_succ_iff.mpr h)) hy'
    refine lu_step M hp v' w' ?_ h1 h2 h3 h4
    intro i j
    rw [← hvw, Matrix.mul_apply, hMs, hMs, hM0, hM0, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [S, Matrix.map_apply, Matrix.of_apply, map_sub, map_mul, map_div₀, hcoe]
    ring

theorem generic_lu : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] (n : ℕ)
    (A : Matrix (Fin n) (Fin n) K) (u : Matrix (Fin n) (Fin n) L), A.det ≠ 0 →
    (∀ k, u k k = 1) → (∀ l k, l < k → u l k = 0) →
    AlgebraicIndependent K (fun q : {lk : Fin n × Fin n // lk.2 < lk.1} => u q.1.1 q.1.2) →
    ∃ v w : Matrix (Fin n) (Fin n) L, A.map (algebraMap K L) * u = v * w ∧ (∀ k, v k k = 1) ∧
      (∀ l k, l < k → v l k = 0) ∧ (∀ l k, k < l → w l k = 0) ∧ ∀ k, w k k ≠ 0 := by
  intro K L _ _ _ n
  exact generic_lu_decomposition_exists n K L

end GlobalTheory.CompanionTheory.GenericLU
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HBBound
section
open NumberField IsDedekindDomain

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem hB_bound : ∀ (N j B : ℕ) (S : Finset ℕ) (d v : ℕ → ℝ) (lrd Lv hrec hB : ℝ), j ≤ N → 3 ≤ B → 0 ≤ lrd → |hrec| ≤ N * (3 / 2 * lrd + |Lv| / 2) → hB = hrec + ∑ p ∈ S, d p → (∀ p ∈ S, p.Prime) → (∀ p ∈ S, 0 ≤ v p) → (∀ p ∈ S, |d p| ≤ (N / ((p : ℝ) - 1) + j * v p + ((N : ℝ) - j) * v p) * Real.log p) → ∑ p ∈ S, v p * Real.log p ≤ lrd → ∑ p ∈ S, Real.log p / ((p : ℝ) - 1) ≤ 3 * Real.log B + 1 → |hB| ≤ 4 * N * (Real.log B + lrd + |Lv|) := by
  intro N j B S d v lrd Lv hrec hB hj hB3 hl hrecb hBeq hprime hv hd hsv hsl
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have hlogB : 1 ≤ Real.log B := by
    have h3 : (3 : ℝ) ≤ B := by exact_mod_cast hB3
    have hexp : Real.exp 1 ≤ B := by
      have := Real.exp_one_lt_d9
      linarith
    have := Real.log_le_log (Real.exp_pos 1) hexp
    rwa [Real.log_exp] at this
  have hsum : |∑ p ∈ S, d p| ≤ N * (3 * Real.log B + 1) + N * lrd := by
    calc |∑ p ∈ S, d p| ≤ ∑ p ∈ S, |d p| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ p ∈ S, ((N : ℝ) * (Real.log p / ((p : ℝ) - 1)) + N * (v p * Real.log p)) := by
        apply Finset.sum_le_sum
        intro p hp
        have hdp := hd p hp
        have e : ((N : ℝ) / ((p : ℝ) - 1) + j * v p + ((N : ℝ) - j) * v p) * Real.log p =
            (N : ℝ) * (Real.log p / ((p : ℝ) - 1)) + N * (v p * Real.log p) := by ring
        linarith
      _ = (N : ℝ) * ∑ p ∈ S, Real.log p / ((p : ℝ) - 1) + N * ∑ p ∈ S, v p * Real.log p := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
      _ ≤ N * (3 * Real.log B + 1) + N * lrd := by gcongr
  have htot : |hB| ≤ |hrec| + |∑ p ∈ S, d p| := by
    rw [hBeq]; exact abs_add_le _ _
  nlinarith [mul_nonneg hN (sub_nonneg.mpr hlogB), mul_nonneg hN hl, mul_nonneg hN (abs_nonneg Lv)]

end GlobalTheory.CompanionTheory.Ar.Flat
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ImplicitRootAnalytic
section
open Filter Topology

namespace GlobalTheory.CompanionTheory.SimpleRoot

theorem exists_analytic_simple_root
    (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] (n : ℕ)
    (c : ℕ → E → ℂ) (w₀ : E) (τ₀ : ℂ) (hc : ∀ j, AnalyticAt ℂ (c j) w₀)
    (h0 : ∑ j ∈ Finset.range (n + 1), c j w₀ * τ₀ ^ j = 0)
    (h1 : ∑ j ∈ Finset.range (n + 1), (j : ℂ) * c j w₀ * τ₀ ^ (j - 1) ≠ 0) :
    ∃ (V : Set E) (W : Set ℂ) (g : E → ℂ), IsOpen V ∧ w₀ ∈ V ∧ IsOpen W ∧ τ₀ ∈ W ∧
      AnalyticOnNhd ℂ g V ∧ ∀ w ∈ V, ∀ τ ∈ W,
        ∑ j ∈ Finset.range (n + 1), c j w * τ ^ j = 0 → τ = g w := by
  set F : E × ℂ → ℂ := fun p => ∑ j ∈ Finset.range (n + 1), c j p.1 * p.2 ^ j with hFdef
  have hFa : AnalyticAt ℂ F (w₀, τ₀) := by
    refine Finset.analyticAt_fun_sum _ fun j _ => ?_
    exact ((hc j).comp analyticAt_fst).mul (analyticAt_snd.pow j)
  have cdf : ContDiffAt ℂ (⊤ : WithTop ℕ∞) F (w₀, τ₀) := hFa.contDiffAt
  have pn : (⊤ : WithTop ℕ∞) ≠ 0 := by simp
  set d : ℂ := ∑ j ∈ Finset.range (n + 1), (j : ℂ) * c j w₀ * τ₀ ^ (j - 1) with hd_def
  have hd : HasDerivAt (fun τ => F (w₀, τ)) d τ₀ :=
    HasDerivAt.fun_sum (u := Finset.range (n + 1)) (A := fun j τ => c j w₀ * τ ^ j)
      (A' := fun j => (j : ℂ) * c j w₀ * τ₀ ^ (j - 1)) fun j _ => by
        rw [show (j : ℂ) * c j w₀ * τ₀ ^ (j - 1) = c j w₀ * ((j : ℂ) * τ₀ ^ (j - 1)) by ring]
        exact (hasDerivAt_pow j τ₀).const_mul (c j w₀)
  have hfd : HasFDerivAt (fun τ => F (w₀, τ))
      ((fderiv ℂ F (w₀, τ₀)).comp (ContinuousLinearMap.inr ℂ E ℂ)) τ₀ :=
    hFa.differentiableAt.hasFDerivAt.comp τ₀ (hasFDerivAt_prodMk_right w₀ τ₀)
  have heq : (fderiv ℂ F (w₀, τ₀)).comp (ContinuousLinearMap.inr ℂ E ℂ) =
      ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) d :=
    hfd.unique hd.hasFDerivAt
  have if₂ : ((fderiv ℂ F (w₀, τ₀)).comp (ContinuousLinearMap.inr ℂ E ℂ)).IsInvertible := by
    rw [heq]
    refine ⟨ContinuousLinearEquiv.unitsEquivAut ℂ (Units.mk0 d h1), ?_⟩
    ext
    simp
  set g := cdf.implicitFunction pn if₂ with hg_def
  have hg : AnalyticAt ℂ g w₀ := (cdf.contDiffAt_implicitFunction pn if₂).analyticAt
  obtain ⟨V₂, W, hV₂o, hw₀V₂, hWo, hτ₀W, hsub⟩ :=
    mem_nhds_prod_iff'.1 (cdf.eventually_apply_eq_iff_implicitFunction pn if₂)
  refine ⟨{w | AnalyticAt ℂ g w} ∩ V₂, W, g, (isOpen_analyticAt ℂ g).inter hV₂o, ⟨hg, hw₀V₂⟩, hWo, hτ₀W,
    fun w hw => hw.1, ?_⟩
  intro w hw τ hτ hroot
  have hmem := hsub (Set.mk_mem_prod hw.2 hτ)
  simp only [Set.mem_ofPred_eq] at hmem
  have h' : F (w, τ) = F (w₀, τ₀) := by
    change (∑ j ∈ Finset.range (n + 1), c j w * τ ^ j) = ∑ j ∈ Finset.range (n + 1), c j w₀ * τ₀ ^ j
    rw [hroot, h0]
  exact (hmem.1 h').symm

end GlobalTheory.CompanionTheory.SimpleRoot
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IntegralOverLocalizationScaled
section
namespace GlobalTheory.CompanionTheory.Ggeo.ClearDenominators

open Polynomial

theorem exists_common_denominator {o K : Type} [CommRing o] [Field K] [Algebra o K]
    (A : Subalgebra o K) (R : Subring K)
    (hfrac : ∀ r ∈ R, ∃ u ∈ A, ∃ v ∈ A, v ≠ 0 ∧ v⁻¹ ∈ R ∧ r = u / v)
    (s : Finset K) (hs : ∀ x ∈ s, x ∈ R) :
    ∃ w ∈ A, w ≠ 0 ∧ w⁻¹ ∈ R ∧ ∀ x ∈ s, w * x ∈ A := by
  classical
  revert hs
  refine Finset.induction_on s ?_ ?_
  · intro _
    refine ⟨1, one_mem A, one_ne_zero, ?_, ?_⟩
    · rw [inv_one]
      exact one_mem R
    · intro x hx
      simp at hx
  · intro a t _ ih hs
    obtain ⟨w, hwA, hw0, hwR, hw⟩ :=
      ih (fun x hx => hs x (Finset.mem_insert_of_mem hx))
    obtain ⟨u, huA, v, hvA, hv0, hvR, hav⟩ := hfrac a (hs a (Finset.mem_insert_self a t))
    refine ⟨w * v, mul_mem hwA hvA, mul_ne_zero hw0 hv0, ?_, ?_⟩
    · rw [mul_inv]
      exact mul_mem hwR hvR
    · intro x hx
      rcases Finset.mem_insert.mp hx with hxa | hxt
      · have key : w * v * x = w * u := by
          rw [hxa, hav, div_eq_mul_inv]
          calc w * v * (u * v⁻¹) = w * u * (v * v⁻¹) := by ring
            _ = w * u := by rw [mul_inv_cancel₀ hv0, mul_one]
        rw [key]
        exact mul_mem hwA huA
      · have key : w * v * x = v * (w * x) := by ring
        rw [key]
        exact mul_mem hvA (hw x hxt)

theorem exists_mul_isIntegral :
    ∀ {o K : Type} [CommRing o] [Field K] [Algebra o K] (A : Subalgebra o K) (R : Subring K),
      (∀ a ∈ A, a ∈ R) → (∀ r ∈ R, ∃ u ∈ A, ∃ v ∈ A, v ≠ 0 ∧ v⁻¹ ∈ R ∧ r = u / v) →
      ∀ (t : K), IsIntegral R t → ∃ v ∈ A, v ≠ 0 ∧ v⁻¹ ∈ R ∧ IsIntegral A (v * t) := by
  intro o K _ _ _ A R _ hfrac t ht
  classical
  obtain ⟨p, hpm, hp⟩ := ht
  have hPm : (p.map (algebraMap R K)).Monic := hpm.map (algebraMap R K)
  have hP : (p.map (algebraMap R K)).eval₂ (RingHom.id K) t = 0 := by
    rw [Polynomial.eval₂_map, RingHom.id_comp]
    exact hp
  have hPR : ∀ i, (p.map (algebraMap R K)).coeff i ∈ R := by
    intro i
    rw [Polynomial.coeff_map]
    exact (p.coeff i).2
  generalize p.map (algebraMap R K) = P at hPm hP hPR
  obtain ⟨w, hwA, hw0, hwR, hw⟩ := exists_common_denominator A R hfrac
    ((Finset.range (P.natDegree + 1)).image P.coeff) (by
      intro x hx
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
      exact hPR i)
  refine ⟨w, hwA, hw0, hwR, ?_⟩
  have hcoef : ∀ i, P.coeff i * w ^ (P.natDegree - i) ∈ A := by
    intro i
    rcases lt_trichotomy i P.natDegree with hi | hi | hi
    · obtain ⟨k, hk⟩ : ∃ k, P.natDegree - i = k + 1 := ⟨P.natDegree - i - 1, by omega⟩
      have h1 : P.coeff i * w ^ (P.natDegree - i) = w ^ k * (w * P.coeff i) := by
        rw [hk]
        ring
      rw [h1]
      exact mul_mem (pow_mem hwA k)
        (hw _ (Finset.mem_image_of_mem _ (Finset.mem_range.mpr (by omega))))
    · rw [hi, Nat.sub_self, pow_zero, mul_one, hPm.coeff_natDegree]
      exact one_mem A
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt hi, zero_mul]
      exact zero_mem A
  have hQm : (P.scaleRoots w).Monic := by
    rw [Polynomial.Monic, Polynomial.leadingCoeff, Polynomial.natDegree_scaleRoots,
      Polynomial.coeff_scaleRoots_natDegree]
    exact hPm
  have hlift : P.scaleRoots w ∈ Polynomial.lifts (algebraMap A K) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro i
    rw [Polynomial.coeff_scaleRoots]
    exact ⟨⟨_, hcoef i⟩, rfl⟩
  obtain ⟨q, hqmap, -, hqm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hlift hQm
  refine ⟨q, hqm, ?_⟩
  rw [Polynomial.eval₂_eq_eval_map, hqmap]
  exact Polynomial.scaleRoots_eval₂_eq_zero (RingHom.id K) hP

end GlobalTheory.CompanionTheory.Ggeo.ClearDenominators
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IotaMultiChangeOfBasisDet
section
namespace GlobalTheory.CompanionTheory.Ar.Lat

theorem wedge_matrix_mul_family (Ω V : Type) [Field Ω] [AddCommGroup V] [Module Ω V] (n : ℕ)
    (e : Fin n → V) (P : Matrix (Fin n) (Fin n) Ω) :
    exteriorPower.ιMulti Ω n (fun i => ∑ j, P i j • e j) = P.det • exteriorPower.ιMulti Ω n e := by
  let L : (Fin n → Ω) →ₗ[Ω] V := (Pi.basisFun Ω (Fin n)).constr Ω e
  have hL : ∀ c : Fin n → Ω, L c = ∑ j, c j • e j := fun c => by
    simp [L, Module.Basis.constr_apply_fintype]
  have hLe : (fun i => L (Pi.basisFun Ω (Fin n) i)) = e := funext fun i => by simp [L]
  rw [← sub_eq_zero]
  refine (Module.forall_dual_apply_eq_zero_iff Ω _).1 fun f => ?_
  let A : (Fin n → Ω) [⋀^Fin n]→ₗ[Ω] Ω :=
    (f.compAlternatingMap (exteriorPower.ιMulti Ω n (M := V))).compLinearMap L
  have h := congrArg (fun g => g (fun i => P i))
    (AlternatingMap.eq_smul_basis_det (Pi.basisFun Ω (Fin n)) A)
  simp only [AlternatingMap.smul_apply, Pi.basisFun_det_apply, smul_eq_mul] at h
  have h1 : A (fun i => P i) = f (exteriorPower.ιMulti Ω n (fun i => ∑ j, P i j • e j)) := by
    simp only [A, AlternatingMap.compLinearMap_apply, LinearMap.compAlternatingMap_apply]
    congr 2
    funext i
    exact hL _
  have h2 : A (Pi.basisFun Ω (Fin n)) = f (exteriorPower.ιMulti Ω n e) := by
    simp only [A, AlternatingMap.compLinearMap_apply, LinearMap.compAlternatingMap_apply]
    congr 2
  have h3 : (Matrix.of fun i => P i) = P := rfl
  rw [h1, h2, h3] at h
  rw [map_sub, map_smul, h, smul_eq_mul, mul_comm, sub_self]

end GlobalTheory.CompanionTheory.Ar.Lat
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IotaMultiNeZeroOfLinIndep
section
namespace GlobalTheory.CompanionTheory.Exterior

theorem ιMulti_ne_zero_of_linearIndependent :
    ∀ (Ω V : Type) [Field Ω] [AddCommGroup V] [Module Ω V] (n : ℕ) (e : Fin n → V),
      LinearIndependent Ω e → exteriorPower.ιMulti Ω n e ≠ 0 := by
  intro Ω V _ _ _ n e he h
  let f : (Fin n → Ω) →ₗ[Ω] V := Fintype.linearCombination Ω e
  have hf : LinearMap.ker f = ⊥ :=
    LinearMap.ker_eq_bot.2 he.fintypeLinearCombination_injective
  obtain ⟨π, hπ⟩ := f.exists_leftInverse_of_injective hf
  have hπe : ∀ j, π (e j) = Pi.single j 1 := by
    intro j
    have h2 := LinearMap.congr_fun hπ (Pi.single j 1)
    simpa [f, Fintype.linearCombination_apply_single] using h2
  let D : V [⋀^Fin n]→ₗ[Ω] Ω :=
    (Matrix.detRowAlternating (n := Fin n) (R := Ω)).compLinearMap π
  have h1 := exteriorPower.alternatingMapLinearEquiv_apply_ιMulti D e
  rw [h, map_zero] at h1
  have h3 : D e = 1 := by
    have h4 : (fun i => π (e i)) = (1 : Matrix (Fin n) (Fin n) Ω) := by
      ext i j
      simp [hπe, Matrix.one_apply, Pi.single_apply, eq_comm]
    change Matrix.det (fun i => π (e i)) = 1
    rw [h4, Matrix.det_one]
  rw [h3] at h1
  exact zero_ne_one h1

end GlobalTheory.CompanionTheory.Exterior
end

