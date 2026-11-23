module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.StLocB
public import GroundTheory.AutomorphicForms.Bundle0024

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.RepsEx
section
open MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.Spherical UpperTheory.Gal.Gen

theorem UpperTheory.Gal.Gen.repsEx_pf :
    UpperTheory.Gal.Gen.RepsEx := by
  intro F _ _ _ _ n _ _ μ _ h
  classical
  have hKc := GLnLocal.isCompact_integralGL F n
  have hKo : IsOpen ((GLnLocal.integralGL F n : Subgroup (GL (Fin n) F)) : Set (GL (Fin n) F)) :=
    (integralOpen F n).isOpen
  have hbi := HeckeAlgebra.HeckeAlgebraLevel.val_mem hKc hKo h
  have hsupp : HasCompactSupport ⇑(HeckeAlgebra.HeckeAlgebraLevel.val hKc hKo h) := (HeckeAlgebra.mem _).2
  set φ : GL (Fin n) F → ℂ := ⇑(HeckeAlgebra.HeckeAlgebraLevel.val hKc hKo h) with hφ
  have hright : ∀ g k, k ∈ GLnLocal.integralGL F n → φ (g * k) = φ g := fun g k hk => (hbi k hk g).2
  set S := (finite_image_mk_tsupport (integralOpen F n) hsupp).toFinset with hS
  refine ⟨S.image Quotient.out, ?_, ?_⟩
  · intro g hg g' hg' hgg
    simp only [Finset.mem_image] at hg hg'
    obtain ⟨x, -, rfl⟩ := hg
    obtain ⟨y, -, rfl⟩ := hg'
    have hxy : x = y := by
      rw [← QuotientGroup.out_eq' x, ← QuotientGroup.out_eq' y]
      exact QuotientGroup.eq.2 hgg
    rw [hxy]
  · intro f hf
    have hint := integral_eq_smul_finsum_coset μ (integralOpen F n) hKc (f := fun x => φ x * f x)
      hsupp.mul_right (fun g k hk => by simp only [hright g k hk, hf g k hk])
    rw [hint, Complex.real_smul]
    congr 1
    rw [finsum_eq_sum_of_support_subset (s := S) _ ?_, Finset.sum_image]
    · rfl
    · intro x _ y _ hxy
      exact Quotient.out_injective hxy
    · intro x hx
      have hne : φ (Quotient.out x) ≠ 0 := left_ne_zero_of_mul hx
      rw [hS, Set.Finite.coe_toFinset]
      exact ⟨Quotient.out x, subset_tsupport _ hne, QuotientGroup.out_eq' x⟩
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.SmallPf
section
open MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.Spherical UpperTheory.Gal.Gen

theorem UpperTheory.Gal.Gen.small_pf :
    UpperTheory.Gal.Gen.SymEx → UpperTheory.Gal.Gen.StarEx → UpperTheory.Gal.Gen.NullZero → UpperTheory.Gal.Gen.DensCont → UpperTheory.Gal.Gen.Small := by
  intro hSym hStar hNull hDens n Φ hΦ δ hδ
  obtain ⟨P, hPmem, hPprod, hPpoly⟩ := hSym n Φ
  obtain ⟨Ψ, hΨ, hPΨ⟩ := hPpoly hΦ
  obtain ⟨Q, hQmem, hQ⟩ := hStar n P hPmem
  obtain ⟨-, -, hcont, hnorm⟩ := hDens n 0 le_rfl one_pos
  obtain ⟨M, hM⟩ := (isCompact_univ : IsCompact (Set.univ : Set (Fin n → UnitAddCircle))).exists_bound_of_continuousOn
    (hcont P).continuousOn
  set c : ℝ := 1 / (M ^ 2 + 1) with hc
  have hc0 : 0 < c := by positivity
  let g : (Fin n → UnitAddCircle) → ℝ := fun θ => 1 - c * ‖evalAt (pt θ) P‖ ^ 2
  have hg0 : ∀ θ, 0 ≤ g θ := by
    intro θ
    have h1 : ‖evalAt (pt θ) P‖ ≤ M := hM θ (Set.mem_univ _)
    have h2 : ‖evalAt (pt θ) P‖ ^ 2 ≤ M ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) h1 2
    have h3 : c * ‖evalAt (pt θ) P‖ ^ 2 ≤ 1 := by
      rw [hc, div_mul_eq_mul_div, one_mul, div_le_one (by positivity)]
      linarith
    simp only [g]
    linarith
  have hg1 : ∀ θ, g θ ≤ 1 := by
    intro θ
    simp only [g]
    have : 0 ≤ c * ‖evalAt (pt θ) P‖ ^ 2 := by positivity
    linarith
  let pk : ℕ → LaurentRing n := fun k => (1 - (c : ℂ) • (P * Q)) ^ k
  have hpk_mem : ∀ k, pk k ∈ symmetricLaurent (n := n) := by
    intro k
    exact Subalgebra.pow_mem _ (Subalgebra.sub_mem _ (Subalgebra.one_mem _)
      (Subalgebra.smul_mem _ (Subalgebra.mul_mem _ hPmem hQmem) _)) k
  have hpk_eval : ∀ k θ, evalAt (pt θ) (pk k) = ((g θ : ℝ) : ℂ) ^ k := by
    intro k θ
    simp only [pk, g, map_pow, map_sub, map_one, map_smul, map_mul, smul_eq_mul]
    rw [hQ (pt θ) (hnorm θ), Complex.mul_conj']
    push_cast
    ring
  have hF : ∀ k θ, ‖evalAt (pt θ) (pk k)‖ ^ 2 = (g θ ^ k) ^ 2 := by
    intro k θ
    rw [hpk_eval, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hg0 θ)]
  have hlim : Filter.Tendsto (fun k => ∫ θ, ‖evalAt (pt θ) (pk k)‖ ^ 2) Filter.atTop
      (nhds (∫ _θ : Fin n → UnitAddCircle, (0 : ℝ))) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ)) (fun k => ?_) (integrable_const _)
      (fun k => Filter.Eventually.of_forall (fun θ => ?_)) ?_
    · exact ((hcont (pk k)).norm.pow 2).aestronglyMeasurable
    · rw [hF, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact pow_le_one₀ (pow_nonneg (hg0 θ) _) (pow_le_one₀ (hg0 θ) (hg1 θ))
    · filter_upwards [hNull n Ψ hΨ] with θ hθ
      have hP0 : evalAt (pt θ) P ≠ 0 := by rw [hPΨ]; exact hθ
      have hlt : g θ < 1 := by
        simp only [g]
        have : 0 < c * ‖evalAt (pt θ) P‖ ^ 2 := by
          have := norm_pos_iff.mpr hP0
          positivity
        linarith
      simp only [hF]
      have h := (tendsto_pow_atTop_nhds_zero_of_lt_one (hg0 θ) hlt).pow 2
      simpa using h
  rw [MeasureTheory.integral_zero] at hlim
  obtain ⟨k, hk⟩ := ((tendsto_order.1 hlim).2 δ hδ).exists
  refine ⟨pk k, hpk_mem k, fun z hz => ?_, hk.le⟩
  have hP0 : evalAt z P = 0 := by
    rw [hPprod]
    exact Finset.prod_eq_zero (Finset.mem_univ 1) (by simpa using hz)
  simp only [pk, map_pow, map_sub, map_one, map_smul, map_mul, hP0, zero_mul, smul_zero, sub_zero, one_pow]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.StarEx
section
open MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.Spherical UpperTheory.Gal.Gen

namespace UpperTheory.Gal.Gen

private noncomputable def refl {n : ℕ} (z : Fin n → ℂˣ) : Fin n → ℂˣ :=
  fun i => (Units.map (starRingEnd ℂ).toMonoidHom (z i))⁻¹

private noncomputable def star' {n : ℕ} (p : LaurentRing n) : LaurentRing n :=
  p.coeff.sum fun l c => AddMonoidAlgebra.single (-l) ((starRingEnd ℂ) c)

private theorem refl_val {n : ℕ} (z : Fin n → ℂˣ) (i : Fin n) :
    ((refl z i : ℂˣ) : ℂ) = ((starRingEnd ℂ) (z i : ℂ))⁻¹ := by
  simp [refl]

private theorem evalAt_star' {n : ℕ} (p : LaurentRing n) (z : Fin n → ℂˣ) :
    evalAt z (star' p) = (starRingEnd ℂ) (evalAt (refl z) p) := by
  rw [star', map_finsuppSum, evalAt_apply, map_finsuppSum]
  refine Finsupp.sum_congr ?_
  intro l _
  rw [evalAt_single, map_mul, monomialChar_apply, monomialChar_apply, map_prod]
  congr 1
  refine Finset.prod_congr rfl ?_
  intro i _
  simp [refl_val, Units.val_zpow_eq_zpow_val, zpow_neg, map_zpow₀, map_inv₀]

private theorem refl_comp {n : ℕ} (z : Fin n → ℂˣ) (σ : Equiv.Perm (Fin n)) :
    refl (z ∘ σ) = refl z ∘ σ := rfl

private theorem refl_eq {n : ℕ} (z : Fin n → ℂˣ) (hz : ∀ i, ‖(z i : ℂ)‖ = 1) : refl z = z := by
  funext i
  apply Units.ext
  rw [refl_val, Complex.inv_def, Complex.conj_conj, Complex.normSq_conj, Complex.normSq_eq_norm_sq, hz i]
  simp

end UpperTheory.Gal.Gen

theorem UpperTheory.Gal.Gen.starEx_pf :
    UpperTheory.Gal.Gen.StarEx := by
  intro n p hp
  refine ⟨star' p, ?_, fun z hz => ?_⟩
  · intro σ
    refine eq_of_forall_evalAt fun z => ?_
    rw [evalAt_permAct, evalAt_star', evalAt_star', refl_comp, ← evalAt_permAct, hp σ]
  · rw [evalAt_star', refl_eq z hz]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.SymExPf
section
open MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.Spherical UpperTheory.Gal.Gen

theorem UpperTheory.Gal.Gen.symEx_pf :
    UpperTheory.Gal.Gen.SymEx := by
  intro n Φ
  refine ⟨polyEmb (n := n) (∏ σ : Equiv.Perm (Fin n), MvPolynomial.rename σ Φ), ?_, ?_, ?_⟩
  · show ∀ τ : Equiv.Perm (Fin n), permAct τ _ = _
    intro τ
    rw [← polyEmb_rename]
    congr 1
    rw [map_prod]
    simp_rw [MvPolynomial.rename_rename]
    exact Fintype.prod_equiv (Equiv.mulLeft τ) _ _ (fun σ => rfl)
  · intro z
    rw [evalAt_polyEmb, map_prod]
    refine Finset.prod_congr rfl (fun σ _ => ?_)
    rw [MvPolynomial.aeval_rename]
    rfl
  · intro hΦ
    refine ⟨∏ σ : Equiv.Perm (Fin n), MvPolynomial.rename σ Φ, ?_, fun z => ?_⟩
    · rw [Finset.prod_ne_zero_iff]
      intro σ _ h
      apply hΦ
      exact MvPolynomial.rename_injective _ σ.injective (by rw [h, map_zero])
    · rw [evalAt_polyEmb]
      rfl
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.WtPosTermPos
section
open MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.Spherical UpperTheory.Gal.Gen

private lemma wtPos_expand (n : ℕ) (l : Fin n → ℤ) :
    ∑ i : Fin n, ∑ j : Fin n, (((i : ℕ) : ℤ) - ((j : ℕ) : ℤ)) * (l j - l i) =
      2 * (∑ i : Fin n, ((i : ℕ) : ℤ)) * (∑ i, l i) - 2 * n * ∑ i : Fin n, l i * ((i : ℕ) : ℤ) := by
  have h : ∀ i : Fin n, ∑ j : Fin n, (((i : ℕ) : ℤ) - ((j : ℕ) : ℤ)) * (l j - l i) =
      ((i : ℕ) : ℤ) * (∑ j, l j) - n * (l i * ((i : ℕ) : ℤ)) - (∑ j : Fin n, l j * ((j : ℕ) : ℤ))
        + (∑ j : Fin n, ((j : ℕ) : ℤ)) * l i := by
    intro i
    have e : ∀ j : Fin n, (((i : ℕ) : ℤ) - ((j : ℕ) : ℤ)) * (l j - l i) =
        ((i : ℕ) : ℤ) * l j - l i * ((i : ℕ) : ℤ) - l j * ((j : ℕ) : ℤ) + ((j : ℕ) : ℤ) * l i := by
      intro j; ring
    simp only [e, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_mul,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  simp only [h, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_mul,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

private lemma wtPos_term {n : ℕ} {l : Fin n → ℤ} (hl : Antitone l) (i j : Fin n) :
    0 ≤ (((i : ℕ) : ℤ) - ((j : ℕ) : ℤ)) * (l j - l i) := by
  rcases le_total i j with h | h
  · have h1 : ((i : ℕ) : ℤ) ≤ ((j : ℕ) : ℤ) := by exact_mod_cast h
    have h2 := hl h
    exact mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)
  · have h1 : ((j : ℕ) : ℤ) ≤ ((i : ℕ) : ℤ) := by exact_mod_cast h
    have h2 := hl h
    exact mul_nonneg (by linarith) (by linarith)

private lemma wtPos_term_pos {n : ℕ} {l : Fin n → ℤ} (hl : Antitone l) {i j : Fin n} (hij : l i ≠ l j) :
    0 < (((i : ℕ) : ℤ) - ((j : ℕ) : ℤ)) * (l j - l i) := by
  have hne : i ≠ j := fun h => hij (by rw [h])
  rcases lt_or_gt_of_ne hne with h | h
  · have h1 : ((i : ℕ) : ℤ) < ((j : ℕ) : ℤ) := by exact_mod_cast h
    have h2 : l j < l i := lt_of_le_of_ne (hl h.le) (Ne.symm hij)
    exact mul_pos_of_neg_of_neg (by linarith) (by linarith)
  · have h1 : ((j : ℕ) : ℤ) < ((i : ℕ) : ℤ) := by exact_mod_cast h
    have h2 : l i < l j := lt_of_le_of_ne (hl h.le) hij
    exact mul_pos (by linarith) (by linarith)

private lemma wtPos_sum (n : ℕ) (l : Fin n → ℤ) (c : ℤ) :
    ∑ i, l i * (c - ((i : ℕ) : ℤ)) = c * (∑ i, l i) - ∑ i : Fin n, l i * ((i : ℕ) : ℤ) := by
  simp only [mul_sub, Finset.sum_sub_distrib, Finset.mul_sum, mul_comm]

theorem UpperTheory.Gal.Gen.wtPos_pf :
    UpperTheory.Gal.Gen.WtPos := by
  intro n l hl hl0
  set S : ℤ := ∑ i, l i with hS
  set T : ℤ := ∑ i : Fin n, l i * ((i : ℕ) : ℤ) with hT
  rcases lt_trichotomy S 0 with h | h | h
  · refine ⟨-(|T| + 1), ?_⟩
    rw [wtPos_sum, ← hS, ← hT]
    have h1 : T ≤ |T| := le_abs_self T
    have h2 : 0 ≤ |T| := abs_nonneg T
    nlinarith
  ·
    obtain ⟨a, ha⟩ : ∃ a, l a ≠ 0 := by
      by_contra hc
      push_neg at hc
      exact hl0 (funext hc)
    obtain ⟨b, hb⟩ : ∃ b, l a ≠ l b := by
      by_contra hc
      push_neg at hc
      have hs : S = n * l a := by
        rw [hS, Finset.sum_congr rfl (fun i _ => (hc i).symm)]
        simp
      rw [h] at hs
      have hn : (n : ℤ) ≠ 0 := by
        have : 0 < n := Fin.pos a
        exact_mod_cast this.ne'
      exact ha ((mul_eq_zero.mp hs.symm).resolve_left hn)
    have hpos : 0 < ∑ i : Fin n, ∑ j : Fin n, (((i : ℕ) : ℤ) - ((j : ℕ) : ℤ)) * (l j - l i) := by
      refine Finset.sum_pos' (fun i _ => Finset.sum_nonneg fun j _ => wtPos_term hl i j) ⟨a, Finset.mem_univ a, ?_⟩
      exact Finset.sum_pos' (fun j _ => wtPos_term hl a j) ⟨b, Finset.mem_univ b, wtPos_term_pos hl hb⟩
    rw [wtPos_expand, ← hS, ← hT, h] at hpos
    have hn : (0 : ℤ) ≤ n := Int.natCast_nonneg n
    have hT0 : T < 0 := by
      by_contra hc
      push_neg at hc
      nlinarith [mul_nonneg hn hc]
    refine ⟨0, ?_⟩
    rw [wtPos_sum, ← hS, ← hT]
    linarith
  · refine ⟨|T| + 1, ?_⟩
    rw [wtPos_sum, ← hS, ← hT]
    have h1 : T ≤ |T| := le_abs_self T
    have h2 : 0 ≤ |T| := abs_nonneg T
    nlinarith
end

