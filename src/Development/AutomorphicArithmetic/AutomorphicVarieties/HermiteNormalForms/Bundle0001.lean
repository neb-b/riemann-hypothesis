module

public import Mathlib

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.Blockdet
section
open Matrix
open scoped ComplexOrder

theorem UpperTheory.V.KT.blockdet :
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (N : ℕ) (E : Matrix ι ι ℂ) (A : ι → Matrix (Fin N) (Fin N) ℂ),
    (Matrix.of fun s t : Fin N × ι => ∑ φ, star (E φ s.2) * A φ s.1 t.1 * E φ t.2).det =
      (star E.det * E.det) ^ N * ∏ φ, (A φ).det := by
  intro ι _ _ N E A
  have key : (Matrix.of fun s t : Fin N × ι => ∑ φ, star (E φ s.2) * A φ s.1 t.1 * E φ t.2) =
      (Matrix.kronecker (1 : Matrix (Fin N) (Fin N) ℂ) E)ᴴ * Matrix.blockDiagonal A *
        Matrix.kronecker (1 : Matrix (Fin N) (Fin N) ℂ) E := by
    ext ⟨i, a⟩ ⟨j, b⟩
    simp [Matrix.mul_apply, Fintype.sum_prod_type, Matrix.one_apply, Matrix.blockDiagonal_apply,
      Matrix.kronecker, Matrix.kroneckerMap_apply, ite_mul, mul_ite, Finset.sum_ite_eq,
      Finset.sum_ite_eq', Matrix.conjTranspose_apply]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.sum_eq_single i]
    · simp
    · intro k _ hk
      simp [hk]
    · simp
  rw [key, Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose, Matrix.kronecker,
    Matrix.det_kronecker, Matrix.det_blockDiagonal]
  simp [star_pow, mul_pow]
  ring
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.Cardsep
section
open Matrix
open scoped ComplexOrder

theorem UpperTheory.V.KT.cardsep :
    ∀ (M : Type) [AddCommGroup M] [Module.Free ℤ M] [Module.Finite ℤ M] (q : ℕ), q ≠ 0 → ∀ S : Set M,
    (∀ a ∈ S, ∀ b ∈ S, ∀ x : M, a - b = q • x → a = b) → S.Finite ∧ S.ncard ≤ q ^ Module.finrank ℤ M := by
  intro M _ _ _ q hq S hS
  haveI : NeZero q := ⟨hq⟩
  set r := Module.finrank ℤ M
  let bs := Module.finBasis ℤ M
  let f : M → (Fin r → ZMod q) := fun m i => ((bs.equivFun m i : ℤ) : ZMod q)
  have hinj : Set.InjOn f S := by
    intro a ha c hc hac
    have hdvd : ∀ i, (q : ℤ) ∣ bs.equivFun (a - c) i := by
      intro i
      have h := congrFun hac i
      simp only [f] at h
      rw [map_sub, Pi.sub_apply]
      have := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp h.symm
      simpa using this
    refine hS a ha c hc (bs.equivFun.symm fun i => bs.equivFun (a - c) i / q) ?_
    apply bs.equivFun.injective
    rw [map_nsmul, LinearEquiv.apply_symm_apply]
    funext i
    simp only [Pi.smul_apply, nsmul_eq_mul]
    exact (Int.mul_ediv_cancel' (hdvd i)).symm
  have himg : (f '' S).Finite := Set.toFinite _
  have hfin : S.Finite := Set.Finite.of_finite_image himg hinj
  refine ⟨hfin, ?_⟩
  rw [← hinj.ncard_image]
  calc (f '' S).ncard ≤ (Set.univ : Set (Fin r → ZMod q)).ncard :=
        Set.ncard_le_ncard (Set.subset_univ _) (Set.toFinite _)
    _ = q ^ r := by
      rw [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card, Fintype.card_fin]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.Cardsub
section
open Matrix
open scoped ComplexOrder

theorem UpperTheory.V.KT.cardsub :
    ∀ (α : Type) (S : Set α) (k : ℕ), S.Finite →
    {M : Finset α | (↑M : Set α) ⊆ S ∧ M.card ≤ k}.Finite ∧
      {M : Finset α | (↑M : Set α) ⊆ S ∧ M.card ≤ k}.ncard ≤ (S.ncard + 1) ^ k := by
  intro α S k hS
  classical
  set T := hS.toFinset with hT
  let F : Finset (Finset α) := (Finset.range (k + 1)).biUnion fun j => T.powersetCard j
  have hsub : {M : Finset α | (↑M : Set α) ⊆ S ∧ M.card ≤ k} ⊆ (↑F : Set (Finset α)) := by
    rintro M ⟨hM, hk⟩
    rw [Finset.mem_coe, Finset.mem_biUnion]
    refine ⟨M.card, Finset.mem_range.2 (by omega), Finset.mem_powersetCard.2 ⟨?_, rfl⟩⟩
    intro x hx
    simpa [T] using hM hx
  have hfin := F.finite_toSet.subset hsub
  refine ⟨hfin, ?_⟩
  calc _ ≤ (↑F : Set (Finset α)).ncard := Set.ncard_le_ncard hsub F.finite_toSet
    _ = F.card := Set.ncard_coe_finset F
    _ ≤ ∑ j ∈ Finset.range (k + 1), (T.powersetCard j).card := Finset.card_biUnion_le
    _ = ∑ j ∈ Finset.range (k + 1), T.card.choose j := by simp [Finset.card_powersetCard]
    _ ≤ ∑ j ∈ Finset.range (k + 1), T.card ^ j * 1 ^ (k - j) * k.choose j := by
      apply Finset.sum_le_sum
      intro j hj
      have h1 : T.card.choose j ≤ T.card ^ j := Nat.choose_le_pow _ _
      have h2 : 1 ≤ k.choose j := Nat.choose_pos (by simp at hj; omega)
      rw [one_pow, mul_one]
      calc T.card.choose j ≤ T.card ^ j := h1
        _ = T.card ^ j * 1 := (mul_one _).symm
        _ ≤ T.card ^ j * k.choose j := Nat.mul_le_mul_left _ h2
    _ = (T.card + 1) ^ k := (add_pow _ _ _).symm
    _ = (S.ncard + 1) ^ k := by rw [Set.ncard_eq_toFinset_card S hS]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.Cramer
section
open Matrix
open scoped ComplexOrder

private lemma cs_vec {N : ℕ} (x y : Fin N → ℂ) (hx : (star x ⬝ᵥ x).re ≤ 1)
    (hy : (star y ⬝ᵥ y).re ≤ 1) : ‖star x ⬝ᵥ y‖ ≤ 1 := by
  have key : ∀ u v : Fin N → ℂ, star u ⬝ᵥ v =
      inner ℂ (WithLp.toLp 2 u : EuclideanSpace ℂ (Fin N)) (WithLp.toLp 2 v) := by
    intro u v
    rw [EuclideanSpace.inner_toLp_toLp, dotProduct_comm]
  have nb : ∀ u : Fin N → ℂ, (star u ⬝ᵥ u).re ≤ 1 →
      ‖(WithLp.toLp 2 u : EuclideanSpace ℂ (Fin N))‖ ≤ 1 := by
    intro u hu
    rw [key] at hu
    have h := inner_self_eq_norm_sq (𝕜 := ℂ) (WithLp.toLp 2 u : EuclideanSpace ℂ (Fin N))
    have h2 : ‖(WithLp.toLp 2 u : EuclideanSpace ℂ (Fin N))‖ ^ 2 ≤ 1 := by
      rw [← h]; exact hu
    nlinarith [norm_nonneg (WithLp.toLp 2 u : EuclideanSpace ℂ (Fin N))]
  rw [key]
  refine (norm_inner_le_norm _ _).trans ?_
  exact mul_le_one₀ (nb x hx) (norm_nonneg _) (nb y hy)

private lemma cs_form {N : ℕ} (G : Matrix (Fin N) (Fin N) ℂ) (hG : G.PosSemidef)
    (x y : Fin N → ℂ) (hx : (star x ⬝ᵥ (G *ᵥ x)).re ≤ 1)
    (hy : (star y ⬝ᵥ (G *ᵥ y)).re ≤ 1) : ‖star x ⬝ᵥ (G *ᵥ y)‖ ≤ 1 := by
  open scoped MatrixOrder in
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hG.nonneg
  have key : ∀ u v : Fin N → ℂ, star u ⬝ᵥ (G *ᵥ v) = star (B *ᵥ u) ⬝ᵥ (B *ᵥ v) := by
    intro u v
    rw [hB, star_mulVec, ← mulVec_mulVec, dotProduct_mulVec, star_eq_conjTranspose]
  rw [key] at hx hy ⊢
  exact cs_vec _ _ hx hy

theorem UpperTheory.V.KT.cramer :
    ∀ (N : ℕ) (G : Matrix (Fin N) (Fin N) ℂ) (c : Fin N → ℂ), G.PosSemidef → (∀ a, (G a a).re ≤ 1) →
    (star c ⬝ᵥ (G *ᵥ c)).re ≤ 1 → ∀ a, ‖G.det‖ * ‖c a‖ ≤ (N : ℝ) ^ N := by
  intro N G c hG hd hc a
  have hs : ∀ (i : Fin N) (v : Fin N → ℂ), star (Pi.single i (1 : ℂ) : Fin N → ℂ) ⬝ᵥ v = v i := by
    intro i v
    simp [← Pi.single_star]
  have he : ∀ i j : Fin N, star (Pi.single i (1 : ℂ) : Fin N → ℂ) ⬝ᵥ
      (G *ᵥ (Pi.single j (1 : ℂ) : Fin N → ℂ)) = G i j := by
    intro i j
    rw [hs]; simp
  have h1 : ∀ i j, ‖G i j‖ ≤ 1 := by
    intro i j
    rw [← he]
    exact cs_form G hG _ _ (by rw [he]; exact hd i) (by rw [he]; exact hd j)
  have h2 : ∀ i, ‖(G *ᵥ c) i‖ ≤ 1 := by
    intro i
    rw [← hs i (G *ᵥ c)]
    exact cs_form G hG _ _ (by rw [he]; exact hd i) hc
  have h3 : G.det * c a = (G.updateCol a (G *ᵥ c)).det := by
    rw [← Matrix.cramer_apply, Matrix.cramer_eq_adjugate_mulVec, mulVec_mulVec, adjugate_mul]
    simp [smul_mulVec]
  rw [← norm_mul, h3]
  have h4 := Matrix.det_le (A := G.updateCol a (G *ᵥ c)) (abv := NormedField.toAbsoluteValue ℂ)
    (x := 1) (by
      intro i j
      change ‖G.updateCol a (G *ᵥ c) i j‖ ≤ 1
      rw [updateCol_apply]
      split_ifs
      · exact h2 i
      · exact h1 i j)
  refine le_trans h4 ?_
  simp only [Fintype.card_fin, one_pow, nsmul_eq_mul, mul_one]
  exact_mod_cast Nat.factorial_le_pow N
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.Grampsd
section
open Matrix
open scoped ComplexOrder

theorem UpperTheory.V.KT.grampsd :
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (G : Matrix ι ι ℝ), G.IsHermitian →
    (∀ c : ι → ℤ, 0 ≤ (fun i => (c i : ℝ)) ⬝ᵥ (G *ᵥ fun i => (c i : ℝ))) → G.PosSemidef := by
  intro ι _ _ G hG hc
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  refine ⟨hG, fun x => ?_⟩
  simp only [star_trivial]
  let Q : (ι → ℝ) → ℝ := fun v => v ⬝ᵥ (G *ᵥ v)
  have hQ : Continuous Q := by
    simp only [Q, dotProduct, mulVec]
    fun_prop
  let u : ℕ → ι → ℝ := fun n i => (⌊(n : ℝ) * x i⌋ : ℝ) / n
  have hu : Filter.Tendsto u Filter.atTop (nhds x) := by
    rw [tendsto_pi_nhds]
    intro i
    have h1 : Filter.Tendsto (fun n : ℕ => x i - 1 / (n : ℝ)) Filter.atTop (nhds (x i)) := by
      have h2 := (tendsto_const_nhds (x := x i)).sub (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ))
      simpa using h2
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' h1 tendsto_const_nhds ?_ ?_
    · filter_upwards [Filter.eventually_gt_atTop 0] with n hn
      have hn' : (0 : ℝ) < n := by exact_mod_cast hn
      simp only [u]
      rw [le_div_iff₀ hn']
      have := Int.sub_one_lt_floor ((n : ℝ) * x i)
      have e : (x i - 1 / n) * n = n * x i - 1 := by field_simp
      rw [e]
      linarith
    · filter_upwards [Filter.eventually_gt_atTop 0] with n hn
      have hn' : (0 : ℝ) < n := by exact_mod_cast hn
      simp only [u]
      rw [div_le_iff₀ hn']
      have := Int.floor_le ((n : ℝ) * x i)
      linarith
  have hnn : ∀ n, 0 ≤ Q (u n) := by
    intro n
    have h := hc (fun i => ⌊(n : ℝ) * x i⌋)
    have e : u n = (1 / (n : ℝ)) • (fun i => ((⌊(n : ℝ) * x i⌋ : ℤ) : ℝ)) := by
      funext i
      simp [u, div_eq_inv_mul]
    have h0 : 0 ≤ 1 / (n : ℝ) := by positivity
    simp only [Q, e, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul]
    exact mul_nonneg h0 (mul_nonneg h0 h)
  exact ge_of_tendsto' ((hQ.tendsto x).comp hu) hnn
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.Hadam
section
open Matrix
open scoped ComplexOrder

theorem UpperTheory.V.KT.hadam :
    ∀ (N : ℕ) (G : Matrix (Fin N) (Fin N) ℂ), G.PosSemidef → (∀ a, (G a a).re ≤ 1) →
    0 ≤ G.det.re ∧ G.det.re ≤ 1 ∧ ‖G.det‖ = G.det.re := by
  intro N G hG hdiag
  have hH : G.IsHermitian := hG.1
  have hnn : ∀ i, 0 ≤ hH.eigenvalues i := fun i => hG.eigenvalues_nonneg i
  have hdet : G.det = ((∏ i, hH.eigenvalues i : ℝ) : ℂ) := by
    rw [hH.det_eq_prod_eigenvalues]
    push_cast
    rfl
  have htr : ∑ i, hH.eigenvalues i ≤ N := by
    have h2 : (G.trace).re = ∑ i, hH.eigenvalues i := by
      rw [hH.trace_eq_sum_eigenvalues, Complex.re_sum]
      simp
    have h3 : (G.trace).re ≤ N := by
      rw [Matrix.trace, Complex.re_sum]
      calc ∑ a, (G a a).re ≤ ∑ _a : Fin N, (1 : ℝ) := Finset.sum_le_sum fun a _ => hdiag a
        _ = N := by simp
    linarith
  have hp0 : 0 ≤ ∏ i, hH.eigenvalues i := Finset.prod_nonneg fun i _ => hnn i
  have hp1 : ∏ i, hH.eigenvalues i ≤ 1 := by
    calc ∏ i, hH.eigenvalues i ≤ ∏ i, Real.exp (hH.eigenvalues i - 1) :=
          Finset.prod_le_prod₀ (fun i _ => hnn i) fun i _ => by
            linarith [Real.add_one_le_exp (hH.eigenvalues i - 1)]
      _ = Real.exp (∑ i, (hH.eigenvalues i - 1)) := (Real.exp_sum _ _).symm
      _ ≤ 1 := by
        rw [Real.exp_le_one_iff, Finset.sum_sub_distrib]
        simp
        linarith
  rw [hdet]
  simp only [Complex.ofReal_re, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hp0]
  exact ⟨hp0, hp1, trivial⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.Hnfeq
section
open Matrix
open scoped ComplexOrder

theorem UpperTheory.V.KT.hnfeq :
    ∀ (R : Type) [CommRing R] [IsDomain R] (N : ℕ) (r : R), r ≠ 0 → ∀ A A' B B' X : Matrix (Fin N) (Fin N) R,
    A * B = r • (1 : Matrix (Fin N) (Fin N) R) → B * A = r • (1 : Matrix (Fin N) (Fin N) R) →
    A' * B' = r • (1 : Matrix (Fin N) (Fin N) R) → B' * A' = r • (1 : Matrix (Fin N) (Fin N) R) →
    B - B' = r • X → ∃ g : GL (Fin N) R, (g : Matrix (Fin N) (Fin N) R) * A = A' := by
  intro R _ _ N r hr A A' B B' X hAB hBA hAB' hBA' hX
  have canc : ∀ P Q : Matrix (Fin N) (Fin N) R, r • P = r • Q → P = Q := by
    intro P Q h
    ext i j
    have := congrFun (congrFun h i) j
    simp only [Matrix.smul_apply, smul_eq_mul] at this
    exact mul_left_cancel₀ hr this
  have hg : r • (1 + A' * X) = A' * B := by
    rw [smul_add, ← Matrix.mul_smul, ← hX, Matrix.mul_sub, hAB']; abel
  have hh : r • (1 - A * X) = A * B' := by
    rw [smul_sub, ← Matrix.mul_smul, ← hX, Matrix.mul_sub, hAB]; abel
  have h1 : (1 + A' * X) * (1 - A * X) = 1 := by
    apply canc
    apply canc
    calc r • r • ((1 + A' * X) * (1 - A * X)) = (r • (1 + A' * X)) * (r • (1 - A * X)) := by
          rw [Matrix.smul_mul, Matrix.mul_smul]
      _ = A' * (B * A) * B' := by rw [hg, hh]; simp only [Matrix.mul_assoc]
      _ = r • r • (1 : Matrix (Fin N) (Fin N) R) := by
          rw [hBA, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hAB']
  have h2 : (1 - A * X) * (1 + A' * X) = 1 := by
    apply canc
    apply canc
    calc r • r • ((1 - A * X) * (1 + A' * X)) = (r • (1 - A * X)) * (r • (1 + A' * X)) := by
          rw [Matrix.smul_mul, Matrix.mul_smul]
      _ = A * (B' * A') * B := by rw [hg, hh]; simp only [Matrix.mul_assoc]
      _ = r • r • (1 : Matrix (Fin N) (Fin N) R) := by
          rw [hBA', Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hAB]
  refine ⟨⟨1 + A' * X, 1 - A * X, h1, h2⟩, ?_⟩
  apply canc
  change r • ((1 + A' * X) * A) = r • A'
  rw [← Matrix.smul_mul, hg, Matrix.mul_assoc, hBA, Matrix.mul_smul, Matrix.mul_one]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.Torsfree
section
open Matrix
open scoped ComplexOrder

private theorem UpperTheory.V.KT.torsfree_sep {R : Type} [Ring R] [Module.Free ℤ R]
    (z w : R) (h : z = (3 : ℤ) • (z * w)) : z = 0 := by
  have hn : ∀ n : ℕ, z = (3 : ℤ) ^ n • (z * w ^ n) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      calc z = (3 : ℤ) • (z * w) := h
        _ = (3 : ℤ) • (((3 : ℤ) ^ n • (z * w ^ n)) * w) := by rw [← ih]
        _ = (3 : ℤ) ^ (n + 1) • (z * w ^ (n + 1)) := by
          rw [smul_mul_assoc, smul_smul, pow_succ', pow_succ, mul_assoc]
  let b := Module.Free.chooseBasis ℤ R
  apply b.repr.injective
  ext i
  have hd : ∀ n : ℕ, (3 : ℤ) ^ n ∣ b.repr z i := by
    intro n
    refine ⟨b.repr (z * w ^ n) i, ?_⟩
    conv_lhs => rw [hn n]
    rw [map_zsmul]
    simp
  simp only [map_zero, Finsupp.coe_zero, Pi.zero_apply]
  by_contra hne
  have h1 := Int.natAbs_le_of_dvd_ne_zero (hd (b.repr z i).natAbs) hne
  rw [Int.natAbs_pow] at h1
  have h2 : (b.repr z i).natAbs < 3 ^ (b.repr z i).natAbs := Nat.lt_pow_self (by norm_num)
  have h3 : (3 : ℤ).natAbs = 3 := rfl
  rw [h3] at h1
  omega

private theorem UpperTheory.V.KT.torsfree_binom {R : Type} [Ring R] (z : R) (k : ℕ) :
    ∃ w : R, (1 + z) ^ k = 1 + (k : ℤ) • z + z * z * w := by
  induction k with
  | zero => exact ⟨0, by simp⟩
  | succ k ih =>
    obtain ⟨w, hw⟩ := ih
    refine ⟨(k : ℤ) • 1 + w * (1 + z), ?_⟩
    rw [pow_succ, hw]
    push_cast
    simp only [add_smul, one_smul, mul_add, add_mul, mul_one, one_mul, smul_mul_assoc,
      mul_smul_comm, mul_assoc]
    abel

theorem UpperTheory.V.KT.torsfree :
    ∀ (R : Type) [Ring R] [Module.Free ℤ R] [Module.Finite ℤ R] (u x : R) (k : ℕ), 0 < k →
    u = 1 + 3 * x → u ^ k = 1 → u = 1 := by
  intro R _ _ _ u x k
  have h3 : ∀ y : R, 3 * y = (3 : ℤ) • y := by
    intro y
    rw [zsmul_eq_mul]; norm_num
  induction k using Nat.strong_induction_on generalizing u x with
  | _ k ih =>
    intro hk hu hpow
    rw [h3] at hu
    by_cases hdiv : 3 ∣ k
    · obtain ⟨m, rfl⟩ := hdiv
      have hm : 0 < m := by omega
      obtain ⟨w, hw⟩ := UpperTheory.V.KT.torsfree_binom ((3 : ℤ) • x) m
      rw [← hu] at hw
      set y : R := (m : ℤ) • x + x * ((3 : ℤ) • x) * w with hy
      have hv : u ^ m = 1 + (3 : ℤ) • y := by
        rw [hw, hy, smul_add, smul_comm (3 : ℤ) (m : ℤ), add_assoc, smul_mul_assoc (3 : ℤ) x,
          smul_mul_assoc (3 : ℤ)]
      have hv3 : (1 + (3 : ℤ) • y) ^ 3 = 1 := by
        rw [← hv, ← pow_mul, mul_comm, hpow]
      have hz : (3 : ℤ) • y = 0 := by
        apply UpperTheory.V.KT.torsfree_sep _ (-y - y * y)
        have hinj : Function.Injective (fun t : R => (3 : ℤ) • t) :=
          smul_right_injective R (by norm_num)
        apply hinj
        have e : (3 : ℤ) • ((3 : ℤ) • y) - (3 : ℤ) • ((3 : ℤ) • (((3 : ℤ) • y) * (-y - y * y)))
            = (1 + (3 : ℤ) • y) ^ 3 - 1 := by
          simp only [pow_succ, pow_zero, mul_add, add_mul, mul_sub, mul_neg, mul_one, one_mul,
            smul_mul_assoc, mul_smul_comm, mul_assoc]
          module
        rw [hv3, sub_self, sub_eq_zero] at e
        exact e
      rw [hz, add_zero] at hv
      exact ih m (by omega) u x hm (by rw [h3]; exact hu) hv
    · obtain ⟨w, hw⟩ := UpperTheory.V.KT.torsfree_binom ((3 : ℤ) • x) k
      rw [← hu, hpow, add_assoc, left_eq_add] at hw
      obtain ⟨a, b, hab⟩ : ∃ a b : ℤ, a * k + 3 * b = 1 := by
        have : (k : ℤ) % 3 = 1 ∨ (k : ℤ) % 3 = 2 := by omega
        rcases this with h | h
        · exact ⟨1, -((k : ℤ) / 3), by omega⟩
        · exact ⟨-1, (k : ℤ) / 3 + 1, by omega⟩
      have hz : (3 : ℤ) • x = 0 := by
        apply UpperTheory.V.KT.torsfree_sep _ (b • 1 - a • (x * w))
        have e : (3 : ℤ) • (((3 : ℤ) • x) * (b • 1 - a • (x * w)))
            = (a * k + 3 * b) • ((3 : ℤ) • x)
              - a • ((k : ℤ) • ((3 : ℤ) • x) + (3 : ℤ) • x * (3 : ℤ) • x * w) := by
          simp only [mul_sub, mul_one, smul_mul_assoc, mul_smul_comm, mul_assoc]
          module
        rw [e, hw, hab, smul_zero, sub_zero, one_smul]
      rw [hu, hz, add_zero]
end

