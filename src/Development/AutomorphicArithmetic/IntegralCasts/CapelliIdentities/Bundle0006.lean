module

public import Mathlib

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CharpolyCoeffValuation
section
private theorem UpperTheory.valuation_perm_term {K Γ ι : Type} [Field K] [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation K Γ) [Fintype ι] [DecidableEq ι] (M : Matrix ι ι K) (σ : Equiv.Perm ι) :
    v (Equiv.Perm.sign σ • ∏ i, M (σ i) i) = ∏ i, v (M (σ i) i) := by
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h, map_prod]

private theorem UpperTheory.valuation_det_le_one_of_entries_le_one' {K Γ ι : Type} [Field K] [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation K Γ) [Fintype ι] [DecidableEq ι] (M : Matrix ι ι K)
    (h1 : ∀ i j, v (M i j) ≤ 1) : v M.det ≤ 1 := by
  rw [Matrix.det_apply]
  refine v.map_sum_le fun σ _ => ?_
  rw [UpperTheory.valuation_perm_term]
  exact Finset.prod_le_one' fun i _ => h1 _ _

private theorem UpperTheory.val_det_eq_one_iff {K Γ ι : Type} [Field K] [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation K Γ) [Fintype ι] [DecidableEq ι] [LinearOrder ι] (M : Matrix ι ι K)
    (h1 : ∀ i j, v (M i j) ≤ 1) (h2 : ∀ i j, j < i → v (M i j) < 1) :
    v M.det = 1 ↔ ∀ i, v (M i i) = 1 := by
  have hlt : ∀ (σ : Equiv.Perm ι) (j : ι), v (M (σ j) j) < 1 →
      v (Equiv.Perm.sign σ • ∏ i, M (σ i) i) < 1 := by
    intro σ j hj
    rw [UpperTheory.valuation_perm_term, ← Finset.mul_prod_erase _ _ (Finset.mem_univ j)]
    exact lt_of_le_of_lt (mul_le_of_le_one_right' (Finset.prod_le_one' fun i _ => h1 _ _)) hj
  have hσ : ∀ σ : Equiv.Perm ι, σ ≠ 1 → v (Equiv.Perm.sign σ • ∏ i, M (σ i) i) < 1 := by
    intro σ hσ
    have : ∃ j, j < σ j := by
      by_contra hcon
      push Not at hcon
      apply hσ
      ext i
      induction i using WellFoundedLT.induction with
      | _ i ih =>
        rcases (hcon i).lt_or_eq with h | h
        · exact σ.injective (ih _ h)
        · exact h
    obtain ⟨j, hj⟩ := this
    exact hlt σ j (h2 _ _ hj)
  constructor
  · intro h i
    by_contra hne
    have hi : v (M i i) < 1 := lt_of_le_of_ne (h1 _ _) hne
    refine absurd h (ne_of_lt ?_)
    rw [Matrix.det_apply]
    refine v.map_sum_lt one_ne_zero fun σ _ => ?_
    by_cases h' : σ = 1
    · exact hlt σ i (by simpa [h'] using hi)
    · exact hσ σ h'
  · intro h
    have h0 : v (Equiv.Perm.sign (1 : Equiv.Perm ι) • ∏ i, M ((1 : Equiv.Perm ι) i) i) = 1 := by
      rw [UpperTheory.valuation_perm_term]
      exact Finset.prod_eq_one fun i _ => h i
    rw [Matrix.det_apply, v.map_sum_eq_of_lt (Finset.mem_univ 1), h0]
    intro σ hσ'
    rw [h0]
    exact hσ σ (by simpa using hσ')

private theorem UpperTheory.prod_lt_of_strictMono {Γ ι : Type} [LinearOrderedCommGroupWithZero Γ]
    [LinearOrder ι] (f : ι → Γ) (hf : StrictMono f) (h0 : ∀ i, 0 < f i) (S T : Finset ι)
    (hc : S.card = T.card) (hne : S ≠ T) (hT : ∀ i j, i ∉ T → j ∈ T → i < j) :
    ∏ i ∈ S, f i < ∏ i ∈ T, f i := by
  have hc' : (S \ T).card = (T \ S).card := Finset.card_sdiff_comm hc
  have hS : (S \ T).Nonempty := by
    rw [Finset.sdiff_nonempty]
    intro hsub
    exact hne (Finset.eq_of_subset_of_card_le hsub hc.ge)
  have hT' : (T \ S).Nonempty := by
    rw [← Finset.card_pos, ← hc', Finset.card_pos]
    exact hS
  obtain ⟨c, hcm, hcmax⟩ := Finset.exists_max_image (S \ T) id hS
  have key : ∏ i ∈ S \ T, f i < ∏ i ∈ T \ S, f i := by
    calc ∏ i ∈ S \ T, f i ≤ ∏ _i ∈ S \ T, f c :=
          Finset.prod_le_prod' fun i hi => hf.monotone (hcmax i hi)
      _ = ∏ _i ∈ T \ S, f c := by simp [hc']
      _ < _ := Finset.prod_lt_prod_of_nonempty₀ (fun _ _ => h0 c)
          (fun i hi => hf (hT _ _ (Finset.mem_sdiff.1 hcm).2 (Finset.mem_sdiff.1 hi).1)) hT'
  rw [← Finset.prod_inter_mul_prod_diff S T, ← Finset.prod_inter_mul_prod_diff T S,
    Finset.inter_comm T S]
  exact mul_lt_mul_of_pos_left key (Finset.prod_pos fun i _ => h0 i)

theorem UpperTheory.charpoly_coeff_valuation :
    ∀ {K Γ : Type} [Field K] [LinearOrderedCommGroupWithZero Γ] (v : Valuation K Γ) (n : ℕ)
        (M : Matrix (Fin n) (Fin n) K) (d : Fin n → K),
        (∀ i j, v (M i j) ≤ 1) → (∀ i j, j < i → v (M i j) < 1) → v M.det = 1 →
        StrictMono (fun i => v (d i)) → (∀ i, d i ≠ 0) →
        ∀ k ≤ n, v ((Matrix.diagonal d * M).charpoly.coeff k) =
          ∏ i ∈ Finset.univ.filter (fun i : Fin n => k ≤ i.val), v (d i) := by
  intro K Γ _ _ v n M d h1 h2 hdet hmono hd k hk
  have hdiag := (UpperTheory.val_det_eq_one_iff v M h1 h2).1 hdet
  have hminor : ∀ S : Finset (Fin n),
      v ((Matrix.diagonal d * M).submatrix (Subtype.val : S → Fin n) (Subtype.val : S → Fin n)).det
        = (∏ i ∈ S, v (d i)) *
          v (M.submatrix (Subtype.val : S → Fin n) (Subtype.val : S → Fin n)).det := by
    intro S
    have : (Matrix.diagonal d * M).submatrix (Subtype.val : S → Fin n) (Subtype.val : S → Fin n)
        = Matrix.of fun i j : S => d i *
          (M.submatrix (Subtype.val : S → Fin n) (Subtype.val : S → Fin n)) i j := by
      ext i j
      simp
    rw [this, Matrix.det_mul_column, map_mul, map_prod, Finset.prod_coe_sort S fun i => v (d i)]
  set T := Finset.univ.filter (fun i : Fin n => k ≤ i.val) with hT
  have hcard : T.card = n - k := by
    have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n)))
      (fun i : Fin n => k ≤ i.val)
    have h' : (Finset.univ.filter fun i : Fin n => ¬ k ≤ i.val).card = k := by
      simp only [not_le]
      rw [Fin.card_filter_val_lt, min_eq_right hk]
    rw [h', Finset.card_univ, Fintype.card_fin, ← hT] at h
    omega
  have hTval : v ((Matrix.diagonal d * M).submatrix (Subtype.val : T → Fin n)
      (Subtype.val : T → Fin n)).det = ∏ i ∈ T, v (d i) := by
    rw [hminor, (UpperTheory.val_det_eq_one_iff v
      (M.submatrix (Subtype.val : T → Fin n) (Subtype.val : T → Fin n)) (fun i j => h1 _ _)
      (fun i j h => h2 _ _ h)).2 fun i => hdiag _, mul_one]
  have hc := Matrix.charpoly_coeff_eq_sum_minors (Matrix.diagonal d * M) (n - k) (by simp)
  rw [Fintype.card_fin, Nat.sub_sub_self hk] at hc
  have hmem : T ∈ Finset.powersetCard (n - k) (Finset.univ : Finset (Fin n)) := by
    simp [hcard]
  rw [hc, map_mul, map_pow, v.map_neg, map_one, one_pow, one_mul, v.map_sum_eq_of_lt hmem, hTval]
  intro S hS
  rw [hTval, hminor]
  simp only [Finset.mem_sdiff, Finset.mem_powersetCard, Finset.mem_singleton] at hS
  refine lt_of_le_of_lt
    (mul_le_of_le_one_right' (UpperTheory.valuation_det_le_one_of_entries_le_one' v _ fun i j => h1 _ _)) ?_
  refine UpperTheory.prod_lt_of_strictMono (fun i => v (d i)) hmono
    (fun i => zero_lt_iff.2 ((v.ne_zero_iff).2 (hd i))) S T (hS.1.2.trans hcard.symm) hS.2 ?_
  intro i j hi hj
  simp only [hT, Finset.mem_filter, Finset.mem_univ, true_and, not_le] at hi hj
  exact Fin.lt_def.2 (lt_of_lt_of_le hi hj)
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CharpolyPowersRatios
section
noncomputable def UpperTheory.Reformulated.B.CharpolyPowersRatios.FreeRatios :
    {κ ι : Type} → [inst : Field κ] → (ι → κˣ) → Prop :=
    fun {κ ι : Type} [Field κ] (α : ι → κˣ) ↦ ∀ (i j : ι), i ≠ j → ∀ (m : ℕ), (0 : ℕ) < m → α i ^ m ≠ α j ^ m

theorem UpperTheory.Reformulated.B.CharpolyPowersRatios.charpoly_pow :
    ∀ {K : Type} [inst : Field K] {n : ℕ} (M : Matrix (Fin n) (Fin n) K) (a : Fin n → Kˣ),
      M.charpoly = ∏ i : Fin n, (Polynomial.X - (Polynomial.C : K → Polynomial K) (↑(a i) : K)) →
        UpperTheory.Reformulated.B.CharpolyPowersRatios.FreeRatios a →
          ∀ (d : ℕ),
            (0 : ℕ) < d →
              (M ^ d).charpoly = ∏ i : Fin n, (Polynomial.X - (Polynomial.C : K → Polynomial K) ((↑(a i) : K) ^ d)) := by
  intro K _ n M a hM hfree d _
  have hinj : Function.Injective (fun i => (a i : K)) := by
    intro i j hij
    by_contra hne
    exact hfree i j hne 1 one_pos (by simpa using Units.ext hij)
  have hev : ∀ i, Module.End.HasEigenvalue (Matrix.toLin' M) (a i : K) := by
    intro i
    rw [Module.End.hasEigenvalue_iff_isRoot_charpoly, Matrix.charpoly_toLin', hM,
      Polynomial.IsRoot.def, Polynomial.eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)
  choose v hv using fun i => (hev i).exists_hasEigenvector
  have hli : LinearIndependent K v :=
    Module.End.eigenvectors_linearIndependent' _ (fun i => (a i : K)) hinj v hv
  let b : Module.Basis (Fin n) K (Fin n → K) :=
    basisOfLinearIndependentOfCardEqFinrank' v hli (by simp)
  have hb : ⇑b = v := coe_basisOfLinearIndependentOfCardEqFinrank' v hli _
  have hpow : ∀ j, Matrix.toLin' (M ^ d) (v j) = ((a j : K) ^ d) • v j := by
    intro j
    rw [Matrix.toLin'_pow]
    exact (hv j).pow_apply d
  have hmat : LinearMap.toMatrix b b (Matrix.toLin' (M ^ d)) =
      Matrix.diagonal (fun i => (a i : K) ^ d) := by
    ext i j
    rw [LinearMap.toMatrix_apply, hb, hpow, map_smul, ← hb]
    simp only [Module.Basis.repr_self, Matrix.diagonal_apply, Finsupp.smul_single, Finsupp.single_apply, smul_eq_mul, mul_one]
    by_cases h : i = j
    · subst h; simp
    · simp [h, Ne.symm h]
  rw [← Matrix.charpoly_toLin', ← LinearMap.charpoly_toMatrix _ b, hmat, Matrix.charpoly_diagonal]
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CharpolySmul
section
theorem UpperTheory.Reformulated.B.Qh50.charpoly_smul_alt.{u_1, u_2} :
    ∀ {k : Type u_1} {ι : Type u_2} [inst : Field k] [inst_1 : Fintype ι] [inst_2 : DecidableEq ι]
    (M : Matrix ι ι k) {c : k},
    c ≠ (0 : k) →
      (c • M).charpoly =
        (Polynomial.C : k → Polynomial k) (c ^ Fintype.card ι) *
          M.charpoly.comp ((Polynomial.C : k → Polynomial k) c⁻¹ * Polynomial.X) := by
  intro k ι _ _ _ M c hc
  have h1 : M.charpoly.comp (Polynomial.C c⁻¹ * Polynomial.X) =
      ((Polynomial.compRingHom (Polynomial.C c⁻¹ * Polynomial.X)).mapMatrix M.charmatrix).det := by
    rw [← RingHom.map_det]
    rfl
  have h2 : (Polynomial.C c : Polynomial k) * Polynomial.C c⁻¹ = 1 := by
    rw [← Polynomial.C_mul, mul_inv_cancel₀ hc, Polynomial.C_1]
  rw [h1, Polynomial.C_pow, ← Matrix.det_smul, Matrix.charpoly]
  congr 1
  refine Matrix.ext fun i j => ?_
  by_cases hij : i = j
  · subst hij
    simp only [Matrix.smul_apply, RingHom.mapMatrix_apply, Matrix.map_apply,
      Matrix.charmatrix_apply_eq, smul_eq_mul, Polynomial.coe_compRingHom_apply,
      Polynomial.sub_comp, Polynomial.X_comp, Polynomial.C_comp, Polynomial.C_mul]
    rw [mul_sub, ← mul_assoc, h2, one_mul]
  · simp only [Matrix.smul_apply, RingHom.mapMatrix_apply, Matrix.map_apply,
      Matrix.charmatrix_apply_ne _ _ _ hij, smul_eq_mul, Polynomial.coe_compRingHom_apply,
      Polynomial.neg_comp, Polynomial.C_comp, Polynomial.C_mul, mul_neg]
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ChoiceFunction
section
theorem UpperTheory.Reformulated.B.InterpolationPointsOfFinrankBound.pick :
    ∀ {k D : Type} [inst : Field k] (P : Set D) {p0 : D},
    p0 ∈ P →
      ∀ (W : Submodule k (D → k)),
        (∀ (f : D → k), f ∈ W ↔ ∀ p ∈ P, f p = (0 : k)) →
          ∀ (n : ℕ) (Y : Submodule k (D → k)) [FiniteDimensional k ↥Y],
            Module.finrank k ↥Y ≤ n + Module.finrank k ↥(Y ⊓ W) →
              ∃ (u : Fin n → D), (∀ (a : Fin n), u a ∈ P) ∧ ∀ f ∈ Y, (∀ (a : Fin n), f (u a) = (0 : k)) → f ∈ W := by
  intro k D _ P p0 hp0 W hW n
  induction n with
  | zero =>
    intro Y _ h
    refine ⟨fun _ => p0, fun _ => hp0, fun f hf _ => ?_⟩
    have heq : Y ⊓ W = Y :=
      Submodule.eq_of_le_of_finrank_le inf_le_left (by simpa using h)
    rw [← heq] at hf
    exact hf.2
  | succ n ih =>
    intro Y _ h
    by_cases hYW : Y ≤ W
    · exact ⟨fun _ => p0, fun _ => hp0, fun f hf _ => hYW hf⟩
    · obtain ⟨g, hgY, hgW⟩ := SetLike.not_le_iff_exists.mp hYW
      rw [hW] at hgW
      simp only [not_forall] at hgW
      obtain ⟨p, hp, hgp⟩ := hgW
      let K : Submodule k (D → k) := LinearMap.ker (LinearMap.proj p : (D → k) →ₗ[k] k)
      have hK : ∀ f : D → k, f ∈ K ↔ f p = 0 := fun f => LinearMap.mem_ker
      have hWK : W ≤ K := fun f hf => (hK f).2 ((hW f).1 hf p hp)
      haveI : FiniteDimensional k ↥(Y ⊓ K) := Submodule.finiteDimensional_of_le inf_le_left
      have hlt : Y ⊓ K < Y := by
        refine lt_of_le_of_ne inf_le_left fun he => hgp ?_
        rw [← he] at hgY
        exact (hK g).1 hgY.2
      have hrank := Submodule.finrank_lt_finrank_of_lt hlt
      have hinf : (Y ⊓ K) ⊓ W = Y ⊓ W := by
        rw [inf_assoc, inf_eq_right.2 hWK]
      obtain ⟨u, hu, hu'⟩ := ih (Y ⊓ K) (by rw [hinf]; omega)
      refine ⟨Fin.cons p u, fun a => ?_, fun f hf hz => ?_⟩
      · refine Fin.cases ?_ (fun i => ?_) a
        · simpa using hp
        · simpa using hu i
      · refine hu' f ⟨hf, (hK f).2 ?_⟩ fun a => ?_
        · simpa using hz 0
        · simpa using hz a.succ
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ChoiceOfModulusAndDiscriminant
section
open scoped IntermediateField TensorProduct Matrix Pointwise NumberField Topology ContDiff NNReal ENNReal Polynomial DirectSum BigOperators InnerProductSpace Manifold

noncomputable def UpperTheory.Reformulated.B.ChoiceOfModulusAndDiscriminant.CmOK :
    ℕ → ℤ → ℤ → ℕ → Prop :=
    fun (a : ℕ) (b c : ℤ) (d : ℕ) ↦
      (4 : ℤ) * (↑a : ℤ) * c = b ^ (2 : ℕ) + (↑d : ℤ) ∧ Odd a ∧ d % (8 : ℕ) = (7 : ℕ) ∧ Nat.Prime d

noncomputable def UpperTheory.Reformulated.B.ChoiceOfModulusAndDiscriminant.cmTheta :
    ℤ → ℕ → ℂ :=
    fun (b : ℤ) (d : ℕ) ↦ ((↑b : ℂ) + Complex.I * (↑√(↑d : ℝ) : ℂ)) / (2 : ℂ)

@[reducible] noncomputable def UpperTheory.Reformulated.B.ChoiceOfModulusAndDiscriminant.KF :
    ℤ → ℕ → IntermediateField ℚ ℂ :=
    fun (b : ℤ) (d : ℕ) ↦ ℚ⟮UpperTheory.Reformulated.B.ChoiceOfModulusAndDiscriminant.cmTheta b d⟯

private theorem UpperTheory.Reformulated.B.ChoiceOfModulusAndDiscriminant.theta_sq (b : ℤ) (d : ℕ) :
    UpperTheory.Reformulated.B.ChoiceOfModulusAndDiscriminant.cmTheta b d * UpperTheory.Reformulated.B.ChoiceOfModulusAndDiscriminant.cmTheta b d =
      (b : ℂ) * UpperTheory.Reformulated.B.ChoiceOfModulusAndDiscriminant.cmTheta b d - ((b : ℂ) ^ 2 + (d : ℂ)) / 4 := by
  have h : ((√(d : ℝ) : ℝ) : ℂ) * ((√(d : ℝ) : ℝ) : ℂ) = (d : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg d)]
    simp
  unfold UpperTheory.Reformulated.B.ChoiceOfModulusAndDiscriminant.cmTheta
  linear_combination (((√(d : ℝ) : ℝ) : ℂ) * ((√(d : ℝ) : ℝ) : ℂ) / 4) * Complex.I_mul_I - (1 / 4 : ℂ) * h

private theorem UpperTheory.Reformulated.B.ChoiceOfModulusAndDiscriminant.theta_integral (b : ℤ) (d : ℕ) :
    IsIntegral ℚ (UpperTheory.Reformulated.B.ChoiceOfModulusAndDiscriminant.cmTheta b d) := by
  refine ⟨Polynomial.X ^ 2 - Polynomial.C (b : ℚ) * Polynomial.X
    + Polynomial.C (((b : ℚ) ^ 2 + (d : ℚ)) / 4), ?_, ?_⟩
  · monicity!
  · have h := UpperTheory.Reformulated.B.ChoiceOfModulusAndDiscriminant.theta_sq b d
    simp only [Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul,
      Polynomial.eval₂_X_pow, Polynomial.eval₂_X, Polynomial.eval₂_C, eq_ratCast]
    push_cast
    linear_combination h

theorem UpperTheory.Reformulated.B.ChoiceOfModulusAndDiscriminant.kap_repr :
    ∀ {a : ℕ} {b c : ℤ} {d : ℕ},
      UpperTheory.Reformulated.B.ChoiceOfModulusAndDiscriminant.CmOK a b c d →
        ∀ {x : ℂ}, x ∈ UpperTheory.Reformulated.B.ChoiceOfModulusAndDiscriminant.KF b d → ∃ (u : ℚ) (v : ℚ), x = (↑u : ℂ) + (↑v : ℂ) * UpperTheory.Reformulated.B.ChoiceOfModulusAndDiscriminant.cmTheta b d := by
  intro a b c d _ x hx
  have hx' : x ∈ Algebra.adjoin ℚ {UpperTheory.Reformulated.B.ChoiceOfModulusAndDiscriminant.cmTheta b d} := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
      (UpperTheory.Reformulated.B.ChoiceOfModulusAndDiscriminant.theta_integral b d).isAlgebraic]
    exact hx
  clear hx
  induction hx' using Algebra.adjoin_induction with
  | mem y hy =>
    rw [Set.mem_singleton_iff] at hy
    exact ⟨0, 1, by simp [hy]⟩
  | algebraMap r => exact ⟨r, 0, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨u, v, rfl⟩ := hy
    obtain ⟨u', v', rfl⟩ := hz
    exact ⟨u + u', v + v', by push_cast; ring⟩
  | mul y z _ _ hy hz =>
    obtain ⟨u, v, rfl⟩ := hy
    obtain ⟨u', v', rfl⟩ := hz
    refine ⟨u * u' - v * v' * (((b : ℚ) ^ 2 + (d : ℚ)) / 4), u * v' + v * u' + v * v' * b, ?_⟩
    push_cast
    linear_combination ((v : ℂ) * (v' : ℂ)) * UpperTheory.Reformulated.B.ChoiceOfModulusAndDiscriminant.theta_sq b d
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ClearDenominatorsLattice
section
theorem UpperTheory.Reformulated.B.ClearDenominatorsLattice.exists_integer_smul_mem_of_span_top :
    ∀ {K V : Type} [inst : Field K] [NumberField K] [inst_2 : AddCommGroup V]
    [inst_3 : _root_.Module K V] [inst_4 : _root_.Module (NumberField.RingOfIntegers K) V]
    [IsScalarTower (NumberField.RingOfIntegers K) K V] (L : Submodule (NumberField.RingOfIntegers K) V),
    Submodule.span K (↑L : Set V) = ⊤ →
      ∀ (x : V), ∃ (r : NumberField.RingOfIntegers K), r ≠ (0 : NumberField.RingOfIntegers K) ∧ r • x ∈ L := by
  intro K V _ _ _ _ _ _ L hL x
  have hx : x ∈ Submodule.span K (↑L : Set V) := hL ▸ Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, one_ne_zero, by rwa [one_smul]⟩
  | zero => exact ⟨1, one_ne_zero, by rw [smul_zero]; exact L.zero_mem⟩
  | add y z _ _ hy hz =>
    obtain ⟨r, hr, hry⟩ := hy
    obtain ⟨s, hs, hsz⟩ := hz
    refine ⟨r * s, mul_ne_zero hr hs, ?_⟩
    rw [smul_add]
    refine L.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]
      exact L.smul_mem _ hry
    · rw [mul_smul]
      exact L.smul_mem _ hsz
  | smul a y _ hy =>
    obtain ⟨r, hr, hry⟩ := hy
    obtain ⟨⟨n, d⟩, hnd⟩ :=
      IsLocalization.surj (nonZeroDivisors (NumberField.RingOfIntegers K)) a
    refine ⟨r * d, mul_ne_zero hr (nonZeroDivisors.ne_zero d.2), ?_⟩
    have h1 : (d : NumberField.RingOfIntegers K) • (a • y) = n • y := by
      rw [← algebraMap_smul K (d : NumberField.RingOfIntegers K) (a • y), ← mul_smul, mul_comm,
        hnd, algebraMap_smul]
    rw [mul_smul, h1, ← mul_smul, mul_comm, mul_smul]
    exact L.smul_mem _ hry
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ClosureSpanCoefficients
section
theorem UpperTheory.closure_span_coefficients :
    ∀ {R M L : Type} [Ring R] [AddCommGroup M] [Module R M] [AddCommGroup L] (O : AddSubgroup R) (f : L →+ M) {m : ℕ} (x : Fin m → L),
        Submodule.span ℤ (Set.range x) = ⊤ → ∀ z : M,
          z ∈ AddSubgroup.closure {z : M | ∃ a ∈ O, ∃ l : L, z = a • f l} ↔
            ∃ a : Fin m → R, (∀ i, a i ∈ O) ∧ ∑ i, a i • f (x i) = z := by
  intro R M L _ _ _ _ O f m x hx z
  constructor
  · intro hz
    induction hz using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨a, ha, l, rfl⟩ := hz
      have hl : l ∈ Submodule.span ℤ (Set.range x) := hx ▸ Submodule.mem_top
      obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 hl
      refine ⟨fun i => c i • a, fun i => O.zsmul_mem ha _, ?_⟩
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_zsmul, smul_assoc, smul_comm]
    | zero => exact ⟨0, fun _ => O.zero_mem, by simp⟩
    | add u v _ _ hu hv =>
      obtain ⟨a, ha, rfl⟩ := hu
      obtain ⟨b, hb, rfl⟩ := hv
      exact ⟨a + b, fun i => O.add_mem (ha i) (hb i), by
        simp [add_smul, Finset.sum_add_distrib]⟩
    | neg u _ hu =>
      obtain ⟨a, ha, rfl⟩ := hu
      exact ⟨-a, fun i => O.neg_mem (ha i), by simp⟩
  · rintro ⟨a, ha, rfl⟩
    exact sum_mem fun i _ => AddSubgroup.subset_closure ⟨a i, ha i, x i, rfl⟩
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ClosureUpperUni
section
noncomputable def UpperTheory.Reformulated.B.Qe27.upperUni :
    (k : ℕ) → (A : Type) → [inst : CommRing A] → Set (GL (Fin k) A) :=
    fun (k : ℕ) (A : Type) [CommRing A] ↦
      {x : GL (Fin k) A |
        ∀ (i j : Fin k),
          (j < i → (↑x : Matrix (Fin k) (Fin k) A) i j = (0 : A)) ∧ (↑x : Matrix (Fin k) (Fin k) A) i i = (1 : A)}

private theorem UpperTheory.Reformulated.B.Qe27.diag_mul {k : ℕ} {A : Type} [CommRing A]
    (M N : Matrix (Fin k) (Fin k) A) (hM : M.BlockTriangular id) (hN : N.BlockTriangular id)
    (i : Fin k) : (M * N) i i = M i i * N i i := by
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_single i (fun j _ hj => ?_) (fun h => absurd (Finset.mem_univ i) h)
  rcases lt_or_gt_of_ne hj with h | h
  · rw [hM (show id j < id i from h), zero_mul]
  · rw [hN (show id i < id j from h), mul_zero]

private theorem UpperTheory.Reformulated.B.Qe27.mem_iff {k : ℕ} {A : Type} [CommRing A] (x : GL (Fin k) A) :
    x ∈ UpperTheory.Reformulated.B.Qe27.upperUni k A ↔
      (x : Matrix (Fin k) (Fin k) A).BlockTriangular id ∧
        ∀ i, (x : Matrix (Fin k) (Fin k) A) i i = 1 :=
  ⟨fun h => ⟨fun i j hij => (h i j).1 hij, fun i => (h i i).2⟩,
    fun h i _ => ⟨fun hij => h.1 hij, h.2 i⟩⟩

theorem UpperTheory.Reformulated.B.Qe27.closure_upperUni :
    ∀ {k : ℕ} (A : Type) [inst : CommRing A],
      ∀ x ∈ Subgroup.closure (UpperTheory.Reformulated.B.Qe27.upperUni k A), x ∈ UpperTheory.Reformulated.B.Qe27.upperUni k A := by
  intro k A _ x hx
  induction hx using Subgroup.closure_induction with
  | mem y hy => exact hy
  | one =>
    rw [UpperTheory.Reformulated.B.Qe27.mem_iff]
    exact ⟨Matrix.blockTriangular_one, fun i => Matrix.one_apply_eq i⟩
  | mul y z _ _ hy hz =>
    rw [UpperTheory.Reformulated.B.Qe27.mem_iff] at hy hz ⊢
    rw [Units.val_mul]
    refine ⟨hy.1.mul hz.1, fun i => ?_⟩
    rw [UpperTheory.Reformulated.B.Qe27.diag_mul _ _ hy.1 hz.1, hy.2, hz.2, one_mul]
  | inv y _ hy =>
    rw [UpperTheory.Reformulated.B.Qe27.mem_iff] at hy ⊢
    have hinv : ((y⁻¹ : GL (Fin k) A) : Matrix (Fin k) (Fin k) A).BlockTriangular id := by
      letI : Invertible (y : Matrix (Fin k) (Fin k) A) := y.invertible
      rw [Matrix.coe_units_inv]
      exact Matrix.blockTriangular_inv_of_blockTriangular hy.1
    refine ⟨hinv, fun i => ?_⟩
    have h := UpperTheory.Reformulated.B.Qe27.diag_mul _ _ hy.1 hinv i
    rw [Units.mul_inv, Matrix.one_apply_eq, hy.2, one_mul] at h
    exact h.symm
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CoeffProdOneAdd
section
namespace UpperTheory.Reformulated.B.Qk43

private lemma esymm_zero_deg (s : Multiset ℂ) : s.esymm 0 = 1 := by
  simp [Multiset.esymm]

private lemma esymm_cons_succ (a : ℂ) (s : Multiset ℂ) (k : ℕ) :
    (a ::ₘ s).esymm (k + 1) = s.esymm (k + 1) + a * s.esymm k := by
  simp [Multiset.esymm, Multiset.powersetCard_cons, Multiset.sum_map_mul_left]

open Polynomial in
private lemma coeff_prod_one_add (s : Multiset ℂ) (k : ℕ) :
    (s.map fun r => (1 + C r * X : ℂ[X])).prod.coeff k = s.esymm k := by
  induction s using Multiset.induction_on generalizing k with
  | empty => cases k <;> simp [Multiset.esymm, coeff_one, Multiset.powersetCard_zero_right]
  | cons a s ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, add_mul, one_mul, mul_assoc, coeff_add,
      coeff_C_mul]
    cases k with
    | zero => rw [coeff_X_mul_zero, ih, esymm_zero_deg, esymm_zero_deg, mul_zero, add_zero]
    | succ k => rw [coeff_X_mul, ih, ih, esymm_cons_succ]

theorem esymm_add (s t : Multiset ℂ) (j : ℕ) :
    (s + t).esymm j = ∑ a ∈ Finset.range (j + 1), s.esymm a * t.esymm (j - a) := by
  rw [← coeff_prod_one_add, Multiset.map_add (f := _), Multiset.prod_add, Polynomial.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [coeff_prod_one_add]

end UpperTheory.Reformulated.B.Qk43
end

