module

public import Mathlib

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ModerateGrowthAddSmul
section
theorem UpperTheory.moderate_growth_add_smul :
    ∀ {Y : Type} (h : Y → ℝ) (f g : Y → ℂ) (z : ℂ), (∀ y, 1 ≤ h y) →
        (∃ (C : ℝ) (N : ℕ), ∀ y, ‖f y‖ ≤ C * h y ^ N) → (∃ (C : ℝ) (N : ℕ), ∀ y, ‖g y‖ ≤ C * h y ^ N) →
        ∃ (C : ℝ) (N : ℕ), ∀ y, ‖f y + z * g y‖ ≤ C * h y ^ N := by
  intro Y h f g z hh ⟨C, N, hf⟩ ⟨D, M, hg⟩
  refine ⟨|C| + ‖z‖ * |D|, N + M, fun y => ?_⟩
  have h0 : 0 ≤ h y := zero_le_one.trans (hh y)
  have h1 : ‖f y‖ ≤ |C| * h y ^ (N + M) :=
    (hf y).trans (mul_le_mul (le_abs_self C)
      (pow_le_pow_right₀ (hh y) (Nat.le_add_right N M)) (pow_nonneg h0 _) (abs_nonneg C))
  have h2 : ‖g y‖ ≤ |D| * h y ^ (N + M) :=
    (hg y).trans (mul_le_mul (le_abs_self D)
      (pow_le_pow_right₀ (hh y) (Nat.le_add_left M N)) (pow_nonneg h0 _) (abs_nonneg D))
  calc ‖f y + z * g y‖ ≤ ‖f y‖ + ‖z * g y‖ := norm_add_le _ _
    _ = ‖f y‖ + ‖z‖ * ‖g y‖ := by rw [norm_mul]
    _ ≤ |C| * h y ^ (N + M) + ‖z‖ * (|D| * h y ^ (N + M)) :=
        add_le_add h1 (mul_le_mul_of_nonneg_left h2 (norm_nonneg z))
    _ = (|C| + ‖z‖ * |D|) * h y ^ (N + M) := by ring
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.MovedPointDeterminant
section
private theorem UpperTheory.Reformulated.B.MovedPointDeterminant.exists_moved_ne {a : ℕ} {σ : Equiv.Perm (Fin a)} (hσ : σ ≠ 1)
    (i : Fin a) : ∃ j, j ≠ i ∧ σ j ≠ j := by
  by_contra h
  push Not at h
  apply hσ
  ext1 j
  by_cases hj : j = i
  · subst hj
    by_contra hne
    exact hne (σ.injective (h _ hne))
  · exact h j hj

theorem UpperTheory.Reformulated.B.MovedPointDeterminant.cv_det :
    ∀ {a : ℕ} {m : ℝ → Matrix (Fin a) (Fin a) ℂ}
    {Y : Matrix (Fin a) (Fin a) ℂ},
    m (0 : ℝ) = (1 : Matrix (Fin a) (Fin a) ℂ) →
      (∀ (i j : Fin a), HasDerivAt (fun (s : ℝ) ↦ m s i j) (Y i j) (0 : ℝ)) →
        HasDerivAt (fun (s : ℝ) ↦ (m s).det) (∑ i : Fin a, Y i i) (0 : ℝ) := by
  intro a m Y h0 hd
  have key : HasDerivAt
      (fun s : ℝ ↦ ∑ σ : Equiv.Perm (Fin a), ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, m s (σ i) i)
      (∑ σ : Equiv.Perm (Fin a), ((Equiv.Perm.sign σ : ℤ) : ℂ) *
        ∑ i, (∏ j ∈ Finset.univ.erase i, m 0 (σ j) j) • Y (σ i) i) 0 :=
    HasDerivAt.fun_sum fun σ _ ↦
      (HasDerivAt.fun_finsetProd (f := fun i s ↦ m s (σ i) i)
        (fun i _ ↦ hd (σ i) i)).const_mul _
  have hval : (∑ σ : Equiv.Perm (Fin a), ((Equiv.Perm.sign σ : ℤ) : ℂ) *
        ∑ i, (∏ j ∈ Finset.univ.erase i, m 0 (σ j) j) • Y (σ i) i) = ∑ i, Y i i := by
    rw [Finset.sum_eq_single (1 : Equiv.Perm (Fin a))]
    · simp [h0]
    · intro σ _ hσ
      refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun i _ ↦ ?_)
      obtain ⟨j, hj, hm⟩ := UpperTheory.Reformulated.B.MovedPointDeterminant.exists_moved_ne hσ i
      rw [Finset.prod_eq_zero (i := j) (by simp [hj]) (by rw [h0, Matrix.one_apply_ne hm]),
        zero_smul]
    · simp
  rw [hval] at key
  simpa only [Matrix.det_apply'] using key
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.MsMul
section
@[reducible] noncomputable def UpperTheory.Reformulated.B.Qj21.XZ :
    Type → ℕ → ℕ → Type :=
    fun (Lt : Type) (N0 N1 : ℕ) ↦ Lt × ℕ × Fin N0 ⊕ Lt × Fin N0 × Fin N1

@[reducible] noncomputable def UpperTheory.Reformulated.B.Qj21.PolyXZ :
    Type → ℕ → ℕ → Type :=
    fun (H : Type) (N0 N1 : ℕ) ↦ MvPolynomial (UpperTheory.Reformulated.B.Qj21.XZ (Bool × H) N0 N1) ℤ

noncomputable def UpperTheory.Reformulated.B.Qj21.lfo :
    {H : Type} → {N0 N1 : ℕ} → H → ℕ × Fin N1 → UpperTheory.Reformulated.B.Qj21.PolyXZ H N0 N1 :=
    fun {H : Type} {N0 N1 : ℕ} (t : H) (c : ℕ × Fin N1) ↦
      ∑ a : Fin N0, MvPolynomial.X (Sum.inl ((Bool.false, t), c.1, a)) * MvPolynomial.X (Sum.inr ((Bool.false, t), a, c.2))

noncomputable def UpperTheory.Reformulated.B.Qj21.tmL :
    {H : Type} → {N0 N1 : ℕ} → H → List (ℕ × Fin N1) → UpperTheory.Reformulated.B.Qj21.PolyXZ H N0 N1 → UpperTheory.Reformulated.B.Qj21.PolyXZ H N0 N1 :=
    fun {H : Type} {N0 N1 : ℕ} (t : H) (L : List (ℕ × Fin N1)) (h : UpperTheory.Reformulated.B.Qj21.PolyXZ H N0 N1) ↦
      (List.map (UpperTheory.Reformulated.B.Qj21.lfo t) L).prod * h

noncomputable def UpperTheory.Reformulated.B.Qj21.nzc :
    {N1 : ℕ} → List (ℕ × Fin N1) → ℕ :=
    fun {N1 : ℕ} (L : List (ℕ × Fin N1)) ↦
      (List.map (fun (c : ℕ × Fin N1) ↦ if c.1 = (0 : ℕ) then (0 : ℕ) else (1 : ℕ)) L).sum

noncomputable def UpperTheory.Reformulated.B.Qj21.z0c :
    {N1 : ℕ} → List (ℕ × Fin N1) → ℕ :=
    fun {N1 : ℕ} (L : List (ℕ × Fin N1)) ↦
      (List.map (fun (c : ℕ × Fin N1) ↦ if c.1 = (0 : ℕ) then (1 : ℕ) else (0 : ℕ)) L).sum

noncomputable def UpperTheory.Reformulated.B.Qj21.MS :
    {H : Type} → {N0 N1 : ℕ} → H → ℕ → ℕ → Submodule ℤ (UpperTheory.Reformulated.B.Qj21.PolyXZ H N0 N1) :=
    fun {H : Type} {N0 N1 : ℕ} (t : H) (a b : ℕ) ↦
      Submodule.span ℤ
        {Q : UpperTheory.Reformulated.B.Qj21.PolyXZ H N0 N1 |
          ∃ (L : List (ℕ × Fin N1)),
            Q = UpperTheory.Reformulated.B.Qj21.tmL t L (1 : UpperTheory.Reformulated.B.Qj21.PolyXZ H N0 N1) ∧
              UpperTheory.Reformulated.B.Qj21.nzc L = a ∧ UpperTheory.Reformulated.B.Qj21.z0c L = b}

theorem UpperTheory.Reformulated.B.Qj21.ms_mul :
    ∀ {H : Type} {N0 N1 : ℕ} (t : H) {a b a' b' : ℕ} {P Q : UpperTheory.Reformulated.B.Qj21.PolyXZ H N0 N1},
      P ∈ UpperTheory.Reformulated.B.Qj21.MS t a b → Q ∈ UpperTheory.Reformulated.B.Qj21.MS t a' b' → P * Q ∈ UpperTheory.Reformulated.B.Qj21.MS t (a + a') (b + b') := by
  intro H N0 N1 t a b a' b' P Q hP hQ
  have key : UpperTheory.Reformulated.B.Qj21.MS (N0 := N0) (N1 := N1) t a b * UpperTheory.Reformulated.B.Qj21.MS t a' b'
      ≤ UpperTheory.Reformulated.B.Qj21.MS t (a + a') (b + b') := by
    unfold UpperTheory.Reformulated.B.Qj21.MS
    rw [Submodule.span_mul_span]
    apply Submodule.span_mono
    rintro _ ⟨x, ⟨L, rfl, h1, h2⟩, y, ⟨L', rfl, h3, h4⟩, rfl⟩
    refine ⟨L ++ L', ?_, ?_, ?_⟩
    · simp only [UpperTheory.Reformulated.B.Qj21.tmL, List.map_append, List.prod_append, mul_one]
    · rw [← h1, ← h3]
      simp only [UpperTheory.Reformulated.B.Qj21.nzc, List.map_append, List.sum_append]
    · rw [← h2, ← h4]
      simp only [UpperTheory.Reformulated.B.Qj21.z0c, List.map_append, List.sum_append]
  exact key (Submodule.mul_mem_mul hP hQ)
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.MulIntegralStatement
section
namespace OneParameterGroupMulIntegral
open intervalIntegral

private lemma mul_integral {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
    (c : A) (f : ℝ → A) (a b : ℝ) (hf : IntervalIntegrable f MeasureTheory.volume a b) :
    c * (∫ s in a..b, f s) = ∫ s in a..b, c * f s := by
  have := (ContinuousLinearMap.mul ℝ A c).intervalIntegral_comp_comm (μ := MeasureTheory.volume)
    (a := a) (b := b) (f := f)
  simpa using (this hf).symm

end OneParameterGroupMulIntegral

open OneParameterGroupMulIntegral in
theorem UpperTheory.Reformulated.B.OneParameterGroupDifferentiableAtZero.main.{u_1} :
    ∀ {W : Type u_1} [inst : NormedAddCommGroup W]
    [inst_1 : NormedSpace ℂ W] [CompleteSpace W] (φ : ℝ → W →L[ℂ] W),
    Continuous φ → φ (0 : ℝ) = (1 : W →L[ℂ] W) → (∀ (s t : ℝ), φ (s + t) = φ s * φ t) → DifferentiableAt ℝ φ (0 : ℝ) := by
  intro W _ _ _ φ hc h0 hmul

  obtain ⟨ε, εpos, hε⟩ := Metric.continuous_iff.mp hc 0 (1/2) (by norm_num)
  set δ : ℝ := ε / 2 with hδ
  have δpos : 0 < δ := by positivity
  set A : W →L[ℂ] W := ∫ s in (0:ℝ)..δ, φ s with hA
  have hint : ∀ a b : ℝ, IntervalIntegrable φ MeasureTheory.volume a b :=
    fun a b => hc.intervalIntegrable a b
  have hest : ‖A - δ • (1 : W →L[ℂ] W)‖ ≤ 1/2 * δ := by
    have e1 : A - δ • (1 : W →L[ℂ] W) = ∫ s in (0:ℝ)..δ, (φ s - 1) := by
      rw [intervalIntegral.integral_sub (hint 0 δ) intervalIntegrable_const,
        intervalIntegral.integral_const]
      simp <;> rfl
    rw [e1]
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := δ) (C := 1/2)
      (f := fun s => φ s - 1) (by
        intro x hx
        rw [Set.uIoc_of_le δpos.le] at hx
        have hxd : dist x 0 < ε := by
          rw [Real.dist_eq, sub_zero, abs_of_pos hx.1]; linarith [hx.2]
        have := hε x hxd
        rw [dist_eq_norm, h0] at this
        exact this.le)
    simpa [abs_of_pos δpos] using this
  have hsmall : ‖1 - δ⁻¹ • A‖ < 1 := by
    have : 1 - δ⁻¹ • A = -(δ⁻¹ • (A - δ • (1 : W →L[ℂ] W))) := by
      rw [smul_sub, smul_smul, inv_mul_cancel₀ δpos.ne']; simp
    rw [this, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr δpos)]
    calc δ⁻¹ * ‖A - δ • (1 : W →L[ℂ] W)‖ ≤ δ⁻¹ * (1/2 * δ) :=
          mul_le_mul_of_nonneg_left hest (inv_pos.mpr δpos).le
      _ = 1/2 := by field_simp
      _ < 1 := by norm_num
  set u := Units.oneSub (1 - δ⁻¹ • A) hsmall
  have hu : (u : W →L[ℂ] W) = δ⁻¹ • A := by simp [u, Units.val_oneSub]
  set B : W →L[ℂ] W := δ⁻¹ • ((u⁻¹ : (W →L[ℂ] W)ˣ) : W →L[ℂ] W)
  have hAB : A * B = 1 := by
    simp only [B, mul_smul_comm, ← smul_mul_assoc, ← hu]
    exact u.mul_inv
  set F : ℝ → W →L[ℂ] W := fun u => ∫ s in (0:ℝ)..u, φ s
  have key : ∀ t, φ t = (F (t + δ) - F t) * B := by
    intro t
    have h1 : φ t * A = F (t + δ) - F t := by
      rw [hA, mul_integral _ _ _ _ (hint 0 δ)]
      have : (fun s => φ t * φ s) = fun s => φ (t + s) := by
        funext s; rw [hmul]
      rw [this, intervalIntegral.integral_comp_add_left (fun s => φ s) t]
      simp only [add_zero, F]
      rw [intervalIntegral.integral_interval_sub_left (hint 0 (t + δ)) (hint 0 t)]
    calc φ t = φ t * A * B := by rw [mul_assoc, hAB, mul_one]
      _ = _ := by rw [h1]
  have hF : ∀ x, HasDerivAt F (φ x) x := fun x => (hc.integral_hasStrictDerivAt 0 x).hasDerivAt
  have hd : HasDerivAt (fun t => (F (t + δ) - F t) * B) ((φ (0 + δ) - φ 0) * B) 0 := by
    apply HasDerivAt.mul_const
    apply HasDerivAt.sub
    · exact (hF (0 + δ)).comp_add_const 0 δ
    · exact hF 0
  have : φ = fun t => (F (t + δ) - F t) * B := funext key
  rw [this]
  exact hd.differentiableAt
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.MulLeftCancelOfDetNeZero
section
theorem UpperTheory.Reformulated.B.Yoa2.mul_left_cancel_of_det_ne_zero.{u_1} :
    ∀ {R : Type u_1} [inst : CommRing R] [IsDomain R] {n : ℕ} {A X Y : Matrix (Fin n) (Fin n) R},
      A.det ≠ (0 : R) → A * X = A * Y → X = Y := by
  intro R _ _ n A X Y hA h
  have h2 : A.det • X = A.det • Y := by
    have h3 : A.adjugate * (A * X) = A.adjugate * (A * Y) := by rw [h]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.adjugate_mul, Matrix.smul_mul,
      Matrix.smul_mul, Matrix.one_mul, Matrix.one_mul] at h3
    exact h3
  ext i j
  have h4 : A.det * X i j = A.det * Y i j := congrFun (congrFun h2 i) j
  exact mul_left_cancel₀ hA h4
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.MulVecFixOfSupp
section
theorem UpperTheory.Reformulated.B.Qi20.mulVec_fix_of_supp :
    ∀ {m : ℕ} (y : Matrix (Fin m) (Fin m) ℂ) (v : Fin m → ℂ),
    (∀ (j : Fin m), v j ≠ (0 : ℂ) → ∀ (i : Fin m), y i j = if i = j then (1 : ℂ) else (0 : ℂ)) → y.mulVec v = v := by
  intro m y v h
  have key : y.mulVec v = (1 : Matrix (Fin m) (Fin m) ℂ).mulVec v := by
    funext i
    simp only [Matrix.mulVec, dotProduct]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hj : v j = 0
    · rw [hj, mul_zero, mul_zero]
    · rw [h j hj i, Matrix.one_apply]
  rw [key, Matrix.one_mulVec]
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.MultiDimensional
section
theorem UpperTheory.Reformulated.B.MultiDimensional.multi_dim :
    ∀ {P : Type} [inst : Fintype P] (g : P → ℤ → ENNReal), ∑' (x : P → ℤ), ∏ p : P, g p (x p) ≤ ∏ p : P, ∑' (n : ℤ), g p n := by
  intro P _ g
  classical
  rw [ENNReal.tsum_eq_iSup_sum]
  refine iSup_le fun s => ?_
  calc ∑ x ∈ s, ∏ p : P, g p (x p)
      ≤ ∑ x ∈ Fintype.piFinset (fun p => s.image (fun y : P → ℤ => y p)), ∏ p : P, g p (x p) := by
        refine Finset.sum_le_sum_of_subset fun x hx => ?_
        exact Fintype.mem_piFinset.2 fun p => Finset.mem_image_of_mem _ hx
    _ = ∏ p : P, ∑ n ∈ s.image (fun y : P → ℤ => y p), g p n :=
        (Finset.prod_univ_sum _ _).symm
    _ ≤ ∏ p : P, ∑' (n : ℤ), g p n :=
        Finset.prod_le_prod' fun p _ => ENNReal.sum_le_tsum _
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.MultilinearVanishLattice
section
theorem UpperTheory.multilinear_vanish_lattice :
    ∀ {ι : Type} [Finite ι] [DecidableEq ι] {M : ι → Type} {N : Type} [∀ i, AddCommGroup (M i)] [∀ i, Module ℂ (M i)]
        [AddCommGroup N] [Module ℂ N] (T : MultilinearMap (RingHom.id ℂ) M N) (L G : ∀ i, Set (M i)),
        (∀ v : ∀ i, M i, (∀ i, v i ∈ L i) → T v = 0) →
        (∀ i, ∀ w ∈ G i, ∃ w0 ∈ L i, ∀ v : ∀ i, M i, T (Function.update v i w0) = 0 → T (Function.update v i w) = 0) →
        ∀ v : ∀ i, M i, (∀ i, v i ∈ Submodule.span ℂ (G i)) → T v = 0 := by
  intro ι _ _ M N _ _ _ _ T L G hL hG
  have key : ∀ s : Finset ι, ∀ v : ∀ i, M i, (∀ i ∈ s, v i ∈ Submodule.span ℂ (G i)) →
      (∀ i, i ∉ s → v i ∈ L i) → T v = 0 := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact fun v _ h => hL v fun i => h i (Finset.notMem_empty i)
    | insert a s ha ih =>
      intro v hs hn
      have hker : Submodule.span ℂ (G a) ≤ LinearMap.ker (T.toLinearMap v a) := by
        rw [Submodule.span_le]
        intro w hw
        obtain ⟨w0, hw0, h⟩ := hG a w hw
        have h0 : T (Function.update v a w0) = 0 := by
          apply ih
          · intro i hi
            have hia : i ≠ a := fun e => ha (e ▸ hi)
            rw [Function.update_of_ne hia]
            exact hs i (Finset.mem_insert_of_mem hi)
          · intro i hi
            by_cases hia : i = a
            · subst hia
              rw [Function.update_self]
              exact hw0
            · rw [Function.update_of_ne hia]
              exact hn i (by simp [hia, hi])
        exact h v h0
      have hv : T (Function.update v a (v a)) = 0 := hker (hs a (Finset.mem_insert_self a s))
      rwa [Function.update_eq_self] at hv
  intro v hv
  haveI := Fintype.ofFinite ι
  exact key Finset.univ v (fun i _ => hv i) (fun i hi => absurd (Finset.mem_univ i) hi)
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.MultiplicationNormBound
section
open MeasureTheory

theorem UpperTheory.Reformulated.B.MultiplicationNormBound.norm_mul_le {X : Type*} (c : X → ℝ) (hb : ∀ x, |c x| ≤ 1)
    (x : X) (z : ℂ) : ‖(c x : ℂ) * z‖ ≤ ‖z‖ := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_of_le_one_left (norm_nonneg _) (hb x)

theorem UpperTheory.Reformulated.B.MultiplicationNormBound.memLp_mul {X : Type*} [MeasurableSpace X] {ν : Measure X}
    (c : X → ℝ) (hc : Measurable c) (hb : ∀ x, |c x| ≤ 1) (f : Lp ℂ 2 ν) :
    MemLp (fun x => (c x : ℂ) * f x) 2 ν :=
  (Lp.memLp f).of_le
    ((Complex.measurable_ofReal.comp hc).aestronglyMeasurable.mul (Lp.aestronglyMeasurable f))
    (Filter.Eventually.of_forall fun x => UpperTheory.Reformulated.B.MultiplicationNormBound.norm_mul_le c hb x (f x))

noncomputable def UpperTheory.Reformulated.B.MultiplicationNormBound.mulL.{u_1} :
    {X : Type u_1} →
      [inst : MeasurableSpace X] →
        {ν : MeasureTheory.Measure X} →
          (c : X → ℝ) →
            Measurable c →
              (∀ (x : X), |c x| ≤ (1 : ℝ)) →
                ↥(MeasureTheory.Lp ℂ (2 : ENNReal) ν) →L[ℂ] ↥(MeasureTheory.Lp ℂ (2 : ENNReal) ν) :=
  fun {X} _ {ν} c hc hb =>
    LinearMap.mkContinuous
      { toFun := fun f => (UpperTheory.Reformulated.B.MultiplicationNormBound.memLp_mul c hc hb f).toLp (fun x => (c x : ℂ) * f x)
        map_add' := fun f g => by
          apply Lp.ext
          filter_upwards [(UpperTheory.Reformulated.B.MultiplicationNormBound.memLp_mul c hc hb (f + g)).coeFn_toLp,
            (UpperTheory.Reformulated.B.MultiplicationNormBound.memLp_mul c hc hb f).coeFn_toLp,
            (UpperTheory.Reformulated.B.MultiplicationNormBound.memLp_mul c hc hb g).coeFn_toLp, Lp.coeFn_add f g,
            Lp.coeFn_add ((UpperTheory.Reformulated.B.MultiplicationNormBound.memLp_mul c hc hb f).toLp _)
              ((UpperTheory.Reformulated.B.MultiplicationNormBound.memLp_mul c hc hb g).toLp _)] with x h1 h2 h3 h4 h5
          rw [h1, h5, h4, Pi.add_apply, Pi.add_apply, h2, h3, mul_add]
        map_smul' := fun a f => by
          apply Lp.ext
          filter_upwards [(UpperTheory.Reformulated.B.MultiplicationNormBound.memLp_mul c hc hb (a • f)).coeFn_toLp,
            (UpperTheory.Reformulated.B.MultiplicationNormBound.memLp_mul c hc hb f).coeFn_toLp, Lp.coeFn_smul a f,
            Lp.coeFn_smul a ((UpperTheory.Reformulated.B.MultiplicationNormBound.memLp_mul c hc hb f).toLp _)] with x h1 h2 h3 h4
          rw [RingHom.id_apply, h1, h4, h3, Pi.smul_apply, Pi.smul_apply, h2, smul_eq_mul,
            smul_eq_mul, mul_left_comm] }
      1
      (fun f => by
        rw [one_mul]
        apply Lp.norm_le_norm_of_ae_le
        filter_upwards [(UpperTheory.Reformulated.B.MultiplicationNormBound.memLp_mul c hc hb f).coeFn_toLp] with x h
        exact h ▸ UpperTheory.Reformulated.B.MultiplicationNormBound.norm_mul_le c hb x (f x))
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.MultiplicationPackage
section
noncomputable def UpperTheory.Reformulated.B.MatrixHomeomorphOfGeneralLinearPair.mulH_pk :
    {K : Type} →
      [inst : Field K] →
        [inst_1 : TopologicalSpace K] →
          [IsTopologicalRing K] →
            {n d : ℕ} → GL (Fin n) K → GL (Fin d) K → Matrix (Fin n) (Fin d) K ≃ₜ Matrix (Fin n) (Fin d) K :=
  fun {K} _ _ _ {n d} a c =>
    { toFun := fun y => (a : Matrix (Fin n) (Fin n) K) * y * (c : Matrix (Fin d) (Fin d) K)
      invFun := fun y =>
        ((a⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * y *
          ((c⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)
      left_inv := fun y => by
        beta_reduce
        rw [Matrix.mul_assoc, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one, ← Matrix.mul_assoc,
          Units.inv_mul, Matrix.one_mul]
      right_inv := fun y => by
        beta_reduce
        rw [Matrix.mul_assoc, Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one, ← Matrix.mul_assoc,
          Units.mul_inv, Matrix.one_mul]
      continuous_toFun := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
      continuous_invFun := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const }
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.MultisetSeparation
section
open Polynomial in
private lemma eval_prod_add (m : Multiset ℂ) (u : ℂ) :
    (((m.map (fun x : ℂ ↦ -x)).map (fun x : ℂ ↦ X - C x)).prod).eval u
      = (m.map (fun x : ℂ ↦ u + x)).prod := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons, eval_mul, ih, eval_sub, eval_X, eval_C]
    ring

theorem UpperTheory.Reformulated.B.MultisetSeparation.msetSep :
    ∀ (m m' : Multiset ℂ),
    (∀ (u : ℂ), (Multiset.map (fun (x : ℂ) ↦ u + x) m).prod = (Multiset.map (fun (x : ℂ) ↦ u + x) m').prod) → m = m' := by
  intro m m' h
  have hp : ((m.map (fun x : ℂ ↦ -x)).map (fun x : ℂ ↦ Polynomial.X - Polynomial.C x)).prod
      = ((m'.map (fun x : ℂ ↦ -x)).map (fun x : ℂ ↦ Polynomial.X - Polynomial.C x)).prod := by
    apply Polynomial.funext
    intro u
    rw [eval_prod_add, eval_prod_add, h u]
  have hr := congrArg Polynomial.roots hp
  rw [Polynomial.roots_multiset_prod_X_sub_C, Polynomial.roots_multiset_prod_X_sub_C] at hr
  exact Multiset.map_injective neg_injective hr
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.NearOfAdjoin
section
theorem UpperTheory.Reformulated.B.Qg2.near_of_adjoin :
    ∀ {P L : Type} [inst : CommRing P] [inst_1 : CommRing L]
    [inst_2 : Algebra P L] (G : Set L),
    (∀ g ∈ G, IsNilpotent g) →
      ∀ x ∈ Algebra.adjoin P G, ∃ (p : P), IsNilpotent (x - (Algebra.algebraMap P L : P → L) p) := by
  intro P L _ _ _ G hG x hx
  induction hx using Algebra.adjoin_induction with
  | mem y hy => exact ⟨0, by simpa using hG y hy⟩
  | algebraMap r => exact ⟨r, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨p, hp⟩ := hy
    obtain ⟨q, hq⟩ := hz
    refine ⟨p + q, ?_⟩
    have h := (Commute.all _ _).isNilpotent_add hp hq
    convert h using 1
    rw [map_add (f := _)]
    ring
  | mul y z _ _ hy hz =>
    obtain ⟨p, hp⟩ := hy
    obtain ⟨q, hq⟩ := hz
    refine ⟨p * q, ?_⟩
    rw [← mem_nilradical] at hp hq ⊢
    have h := (nilradical L).add_mem ((nilradical L).mul_mem_right z hp)
      ((nilradical L).mul_mem_left ((Algebra.algebraMap P L : P → L) p) hq)
    convert h using 1
    rw [map_mul]
    ring
end

