module

public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.SelmerRankBounds.EllipticityFromProductFormula
public import GroundTheory.GlobalFields.IdeleGroups.GaloisOnAdeles.Action
public import GroundTheory.GlobalFields.IdeleGroups.GaloisOnAdeles.Places
public import GroundTheory.GlobalFields.IdeleGroups.SIdeleGroups.Galois
public import GroundTheory.AutomorphicForms.CuspidalDiscreteness.CuspFormsHeight
public import GroundTheory.AutomorphicForms.CuspidalDiscreteness.SiegelConj
public import GroundTheory.AutomorphicForms.Bundle0018

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AdelicQuotients.NormGaloisSmulAdeleComponentAtSmulPlace
section
open NumberField IsDedekindDomain Polynomial
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Global GroundTheory.Global.SemiLocal GroundTheory.Global.AdeleBaseChange
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Loc PositivityTheory.Rg.Tf.Geo
open scoped NumberField.AdeleRing TensorProduct

section
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

private theorem galAd_apply (σ : E ≃ₐ[F] E) (y : 𝔸[E]) : galAd σ y = σ • y := by
  have h : galAd σ = MulSemiringAction.toRingHom (E ≃ₐ[F] E) 𝔸[E] σ := by
    refine adeleRingHom_ext (K := F) (fun l => ?_) (fun a => ?_)
    · change adeleTensorEquiv F E (Algebra.TensorProduct.map (σ : E →ₐ[F] E) (AlgHom.id F 𝔸[F])
        ((adeleTensorEquiv F E).symm (algebraMap E 𝔸[E] l))) = σ • algebraMap E 𝔸[E] l
      rw [adeleTensorEquiv_symm_algebraMap, Algebra.TensorProduct.map_tmul, adeleTensorEquiv_tmul,
        AdeleBaseChange.smul_algebraMap, map_one, map_one, mul_one]
      rfl
    · change adeleTensorEquiv F E (Algebra.TensorProduct.map (σ : E →ₐ[F] E) (AlgHom.id F 𝔸[F])
        ((adeleTensorEquiv F E).symm (adeleMap F E a))) = σ • adeleMap F E a
      rw [adeleTensorEquiv_symm_adeleMap, Algebra.TensorProduct.map_tmul, adeleTensorEquiv_tmul,
        smul_adeleMap, map_one, map_one, one_mul]
      rfl
  rw [h]
  rfl

private theorem continuous_infMap {M M' : Type} [Field M] [NumberField M] [Field M']
    [NumberField M'] (τ : M ≃+* M') (w' : InfinitePlace M') :
    Continuous (infiniteCompletionMap τ w') := by
  open scoped NumberField.LiesOver in
  let _ : Algebra M M' := (τ : M →+* M').toAlgebra
  change Continuous (algebraMap (w'.comap (algebraMap M M')).Completion w'.Completion)
  rw [AbsoluteValue.Completion.algebraMap_eq_of_liesOver]
  exact AbsoluteValue.Completion.continuous_map _ _

private theorem norm_algebraMap_of_smul_eq (σ : E ≃ₐ[F] E) (u w : HeightOneSpectrum (𝓞 E))
    (h : σ • u = w) (l : E) :
    ‖algebraMap E (w.adicCompletion E) (σ l)‖ = ‖algebraMap E (u.adicCompletion E) l‖ := by
  subst h
  exact norm_algebraMap_smul σ u l

private theorem norm_finMap (σ : E ≃ₐ[F] E) (w : HeightOneSpectrum (𝓞 E))
    (y : (comapPrime (σ : E ≃+* E) w).adicCompletion E) :
    ‖finiteCompletionMap (σ : E ≃+* E) w y‖ = ‖y‖ := by
  refine (HeightOneSpectrum.denseRange_algebraMap E (comapPrime (σ : E ≃+* E) w)).induction_on
    (p := fun y => ‖finiteCompletionMap (σ : E ≃+* E) w y‖ = ‖y‖) y
    (isClosed_eq (continuous_norm.comp (continuous_finiteCompletionMap _ w)) continuous_norm)
    fun l => ?_
  rw [finiteCompletionMap_algebraMap]
  exact norm_algebraMap_of_smul_eq σ _ w (by rw [comapPrime_eq_inv_smul, smul_inv_smul]) l

private theorem norm_algebraMap_completion (w : InfinitePlace E) (x : E) :
    ‖algebraMap E w.Completion x‖ = w x :=
  by
    rw [AbsoluteValue.Completion.algebraMap_def, WithAbs.algebraMap_right_apply]
    simpa using InfinitePlace.Completion.norm_coe w (WithAbs.toAbs _ x)

private theorem norm_infMap (σ : E ≃ₐ[F] E) (w : InfinitePlace E)
    (y : (w.comap ((σ : E ≃+* E) : E →+* E)).Completion) :
    ‖infiniteCompletionMap (σ : E ≃+* E) w y‖ = ‖y‖ := by
  refine InfinitePlace.Completion.induction_on _ y
    (isClosed_eq (continuous_norm.comp (continuous_infMap _ w)) continuous_norm) fun a => ?_
  have ha : algebraMap E (w.comap ((σ : E ≃+* E) : E →+* E)).Completion a.ofAbs = (a : (w.comap ((σ : E ≃+* E) : E →+* E)).Completion) := by
    rw [AbsoluteValue.Completion.algebraMap_def, WithAbs.algebraMap_right_apply, Algebra.algebraMap_self_apply]
  rw [← ha]
  change ‖infiniteCompletionMap (σ : E ≃+* E) w (algebraMap E _ a.ofAbs)‖ =
    ‖algebraMap E (w.comap ((σ : E ≃+* E) : E →+* E)).Completion a.ofAbs‖
  rw [infiniteCompletionMap_algebraMap, norm_algebraMap_completion, norm_algebraMap_completion,
    InfinitePlace.comap_apply]
  rfl

private theorem norm_snd_congr (a : 𝔸[E]) {w₁ w₂ : HeightOneSpectrum (𝓞 E)} (h : w₁ = w₂) :
    ‖a.2 w₁‖ = ‖a.2 w₂‖ := by
  subst h
  rfl

private theorem norm_fst_congr (a : 𝔸[E]) {w₁ w₂ : InfinitePlace E} (h : w₁ = w₂) :
    ‖a.1 w₁‖ = ‖a.1 w₂‖ := by
  subst h
  rfl

end

theorem UpperTheory.norm_galois_smul_adele_component_at_smul_place :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E ≃ₐ[F] E) (a : 𝔸[E]),
        (∀ w : HeightOneSpectrum (𝓞 E), ‖(galAd σ a).2 (σ • w)‖ = ‖a.2 w‖) ∧
        ∀ w : InfinitePlace E, ‖(galAd σ a).1 (σ • w)‖ = ‖a.1 w‖ := by
  intro F E _ _ _ _ _ σ a
  rw [galAd_apply]
  constructor
  · intro w
    rw [smul_snd, norm_finMap]
    exact norm_snd_congr a (by rw [comapPrime_eq_inv_smul, inv_smul_smul])
  · intro w
    rw [smul_fst, norm_infMap]
    exact norm_fst_congr a (by rw [comap_eq_inv_smul, inv_smul_smul])
end

-- bundled from Development.AutomorphicArithmetic.AdelicQuotients.OneLeEntryBoundOfBorelDiagonalDecomp
section
open NumberField IsDedekindDomain Polynomial
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Global GroundTheory.Global.AdeleBaseChange
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Loc PositivityTheory.Rg.Tf.Geo
open scoped NumberField.AdeleRing

private theorem entry_le {E : Type*} [NormedField E] {n : ℕ} (b m b' : GL (Fin n) E)
    (d : Fin n → Eˣ) (ρ : Fin n → ℝ) (hd : ∀ i, ‖((d i : Eˣ) : E)‖ = ρ i) (hρ : ∀ i, 0 < ρ i)
    (hb : ∀ p q : Fin n, q < p → (b : Matrix (Fin n) (Fin n) E) p q = 0)
    (hb' : ∀ p q : Fin n, q < p → (b' : Matrix (Fin n) (Fin n) E) p q = 0)
    (r : ℕ) (ε : ℝ) (hε : 0 < ε) (hr : ∀ i j : Fin n, (i : ℕ) < r → r ≤ (j : ℕ) → ρ j / ρ i ≤ ε)
    (i j : Fin n) (hi : (i : ℕ) < r) (hj : r ≤ (j : ℕ)) :
    ‖((b * diagUnits n d * m * (diagUnits n d)⁻¹ * b' : GL (Fin n) E) :
        Matrix (Fin n) (Fin n) E) j i‖ ≤
      (n : ℝ) ^ 2 * ε * (AutomorphicForm.locHeight b * AutomorphicForm.locHeight m *
        AutomorphicForm.locHeight b') := by
  have hinv : (((diagUnits n d)⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) =
      Matrix.diagonal fun i => (((d i)⁻¹ : Eˣ) : E) := by
    rw [← map_inv, coe_diagUnits]; rfl
  have e : ((b * diagUnits n d * m * (diagUnits n d)⁻¹ * b' : GL (Fin n) E) :
        Matrix (Fin n) (Fin n) E) j i =
      ∑ q, ∑ p, (b : Matrix (Fin n) (Fin n) E) j p * ((d p : Eˣ) : E) *
        (m : Matrix (Fin n) (Fin n) E) p q * (((d q)⁻¹ : Eˣ) : E) *
        (b' : Matrix (Fin n) (Fin n) E) q i := by
    rw [Units.val_mul, Units.val_mul, Units.val_mul, Units.val_mul, hinv, coe_diagUnits,
      Matrix.mul_apply]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [Matrix.mul_diagonal, Matrix.mul_apply, Finset.sum_mul, Finset.sum_mul]
    exact Finset.sum_congr rfl fun p _ => by rw [Matrix.mul_diagonal]
  have hL : 0 ≤ AutomorphicForm.locHeight b * AutomorphicForm.locHeight m *
      AutomorphicForm.locHeight b' := by
    have h1 := AutomorphicForm.locHeight_pos b
    have h2 := AutomorphicForm.locHeight_pos m
    have h3 := AutomorphicForm.locHeight_pos b'
    positivity
  have term : ∀ p q : Fin n, ‖(b : Matrix (Fin n) (Fin n) E) j p * ((d p : Eˣ) : E) *
        (m : Matrix (Fin n) (Fin n) E) p q * (((d q)⁻¹ : Eˣ) : E) *
        (b' : Matrix (Fin n) (Fin n) E) q i‖ ≤
      ε * (AutomorphicForm.locHeight b * AutomorphicForm.locHeight m *
        AutomorphicForm.locHeight b') := by
    intro p q
    by_cases h1 : p < j
    · rw [hb j p h1]; simpa using mul_nonneg hε.le hL
    by_cases h2 : i < q
    · rw [hb' q i h2]; simpa using mul_nonneg hε.le hL
    have hp : r ≤ (p : ℕ) := hj.trans (Fin.not_lt.1 h1)
    have hq : (q : ℕ) < r := lt_of_le_of_lt (Fin.not_lt.1 h2) hi
    have hratio := hr q p hq hp
    have hq0 := hρ q
    have e2 : ‖(b : Matrix (Fin n) (Fin n) E) j p * ((d p : Eˣ) : E) *
        (m : Matrix (Fin n) (Fin n) E) p q * (((d q)⁻¹ : Eˣ) : E) *
        (b' : Matrix (Fin n) (Fin n) E) q i‖ =
        ρ p / ρ q * (‖(b : Matrix (Fin n) (Fin n) E) j p‖ * ‖(m : Matrix (Fin n) (Fin n) E) p q‖ *
          ‖(b' : Matrix (Fin n) (Fin n) E) q i‖) := by
      rw [norm_mul, norm_mul, norm_mul, norm_mul, Units.val_inv_eq_inv_val, norm_inv, hd, hd]
      field_simp
    rw [e2]
    refine mul_le_mul hratio ?_ (by positivity) hε.le
    exact mul_le_mul (mul_le_mul (AutomorphicForm.norm_apply_le_locHeight b j p)
      (AutomorphicForm.norm_apply_le_locHeight m p q) (norm_nonneg _)
      (AutomorphicForm.locHeight_pos b).le) (AutomorphicForm.norm_apply_le_locHeight b' q i)
      (norm_nonneg _) (mul_nonneg (AutomorphicForm.locHeight_pos b).le
        (AutomorphicForm.locHeight_pos m).le)
  rw [e]
  calc _ ≤ ∑ _q : Fin n, ∑ _p : Fin n, ε * (AutomorphicForm.locHeight b *
        AutomorphicForm.locHeight m * AutomorphicForm.locHeight b') :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun q _ =>
          (norm_sum_le _ _).trans (Finset.sum_le_sum fun p _ => term p q))
    _ = _ := by simp; ring

theorem UpperTheory.one_le_entry_bound_of_borel_diagonal_decomp :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (δ : GL (Fin n) K) (b b' m : AdelicGLn.AdelicGL K n),
          b ∈ (adelicBorel : Subgroup (AdelicGLn.AdelicGL K n)) → b' ∈ (adelicBorel : Subgroup (AdelicGLn.AdelicGL K n)) →
          ∀ (ρ : Fin n → ℝ) (hρ : ∀ i, 0 < ρ i) (r : ℕ) (ε : ℝ), 0 < ε →
          (∀ i j : Fin n, (i : ℕ) < r → r ≤ (j : ℕ) → ρ j / ρ i ≤ ε) →
          AdelicGLn.diagonal K n δ = b * diagUnits n (fun i => posIdele (K := K) (ρ i) (hρ i)) * m *
            (diagUnits n (fun i => posIdele (K := K) (ρ i) (hρ i)))⁻¹ * b' →
          ∀ i j : Fin n, (i : ℕ) < r → r ≤ (j : ℕ) → (δ : Matrix (Fin n) (Fin n) K) j i ≠ 0 →
          1 ≤ ((n : ℝ) ^ 2 * ε) ^ Module.finrank ℚ K * (AutomorphicForm.heightConst K n *
            (AutomorphicForm.height b * AutomorphicForm.height m * AutomorphicForm.height b')) ^ 2 := by
  intro K _ _ n δ b b' m hb hb' ρ hρ r ε hε hr hδ i j hi hj hc
  have hfin : ∀ v : HeightOneSpectrum (𝓞 K),
      finAt v (diagUnits n (fun i => posIdele (K := K) (ρ i) (hρ i))) = 1 := by
    intro v
    refine Units.ext (Matrix.ext fun p q => ?_)
    rw [finAt_apply, coe_diagUnits, Matrix.diagonal_apply, Units.val_one, Matrix.one_apply]
    split_ifs with h
    · subst h
      exact posIdele_finite (K := K) (ρ p) (hρ p) v
    · rfl
  have hv : ∀ v : HeightOneSpectrum (𝓞 K),
      ‖(((δ : Matrix (Fin n) (Fin n) K) j i : K) : v.adicCompletion K)‖ ≤
        AutomorphicForm.locHeight (finAt v (b * m * b')) := by
    intro v
    have h1 : finAt v (AdelicGLn.diagonal K n δ) = finAt v (b * m * b') := by
      rw [hδ]
      simp only [finAt_mul, finAt_inv, hfin, mul_one, inv_one]
    have h2 := AutomorphicForm.norm_apply_le_locHeight (finAt v (b * m * b')) j i
    rw [← h1, finAt_apply, AdelicGLn.diagonal_apply] at h2
    rw [h1] at h2
    exact h2
  have hw : ∀ w : InfinitePlace K,
      ‖(((δ : Matrix (Fin n) (Fin n) K) j i : K) : w.Completion)‖ ≤
        (n : ℝ) ^ 2 * ε * (AutomorphicForm.locHeight (infAt w b) *
          AutomorphicForm.locHeight (infAt w m) * AutomorphicForm.locHeight (infAt w b')) := by
    intro w
    have h1 : infAt w (AdelicGLn.diagonal K n δ) =
        infAt w b * diagUnits n (fun i => posRealToUnits w ⟨ρ i ^ w.mult, pow_pos (hρ i) _⟩) *
          infAt w m * (diagUnits n (fun i => posRealToUnits w ⟨ρ i ^ w.mult, pow_pos (hρ i) _⟩))⁻¹ *
          infAt w b' := by
      rw [hδ]
      simp only [infAt_mul, infAt_inv, infAt_diagUnits_posIdele]
    have h2 := entry_le (infAt w b) (infAt w m) (infAt w b')
      (fun i => posRealToUnits w ⟨ρ i ^ w.mult, pow_pos (hρ i) _⟩) ρ
      (fun i => norm_posRealToUnits w (hρ i)) hρ
      (fun p q h => by rw [infAt_apply, mem_adelicBorel.1 hb h]; rfl)
      (fun p q h => by rw [infAt_apply, mem_adelicBorel.1 hb' h]; rfl)
      r ε hε hr i j hi hj
    rw [← h1, infAt_apply, AdelicGLn.diagonal_apply] at h2
    rw [AdeleRing.algebraMap_fst_apply] at h2
    exact h2
  have hN : 0 ≤ (n : ℝ) ^ 2 * ε := by positivity
  have pb := AutomorphicForm.height_pos b
  have pm := AutomorphicForm.height_pos m
  have pb' := AutomorphicForm.height_pos b'
  have hC := AutomorphicForm.one_le_heightConst (K := K) (n := n)
  have inf_le : ∀ g : AdelicGLn.AdelicGL K n,
      ∏ w : InfinitePlace K, AutomorphicForm.locHeight (infAt w g) ^ w.mult ≤
        AutomorphicForm.height g := fun g =>
    le_mul_of_one_le_right (zero_le_one.trans (AutomorphicForm.one_le_prod_locHeight g))
      (AutomorphicForm.one_le_finprod_locHeight g)
  have hI : ∏ w : InfinitePlace K, ‖(((δ : Matrix (Fin n) (Fin n) K) j i : K) : w.Completion)‖ ^ w.mult ≤
      ((n : ℝ) ^ 2 * ε) ^ Module.finrank ℚ K *
        (AutomorphicForm.height b * AutomorphicForm.height m * AutomorphicForm.height b') := by
    calc _ ≤ ∏ w : InfinitePlace K, ((n : ℝ) ^ 2 * ε * (AutomorphicForm.locHeight (infAt w b) *
          AutomorphicForm.locHeight (infAt w m) * AutomorphicForm.locHeight (infAt w b'))) ^ w.mult :=
          Finset.prod_le_prod₀ (fun _ _ => pow_nonneg (norm_nonneg _) _)
            fun w _ => pow_le_pow_left₀ (norm_nonneg _) (hw w) _
      _ = ((n : ℝ) ^ 2 * ε) ^ Module.finrank ℚ K *
          ((∏ w : InfinitePlace K, AutomorphicForm.locHeight (infAt w b) ^ w.mult) *
           (∏ w : InfinitePlace K, AutomorphicForm.locHeight (infAt w m) ^ w.mult) *
           (∏ w : InfinitePlace K, AutomorphicForm.locHeight (infAt w b') ^ w.mult)) := by
          rw [← InfinitePlace.sum_mult_eq (K := K), ← Finset.prod_pow_eq_pow_sum]
          simp only [mul_pow, Finset.prod_mul_distrib]
      _ ≤ _ := by
          refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hN _)
          have q1 := zero_le_one.trans (AutomorphicForm.one_le_prod_locHeight b)
          have q2 := zero_le_one.trans (AutomorphicForm.one_le_prod_locHeight m)
          have q3 := zero_le_one.trans (AutomorphicForm.one_le_prod_locHeight b')
          exact mul_le_mul (mul_le_mul (inf_le b) (inf_le m) q2 pb.le) (inf_le b') q3 (by positivity)
  have hF : ∏ᶠ v : HeightOneSpectrum (𝓞 K), ‖(((δ : Matrix (Fin n) (Fin n) K) j i : K) : v.adicCompletion K)‖ ≤
      AutomorphicForm.heightConst K n ^ 2 *
        (AutomorphicForm.height b * AutomorphicForm.height m * AutomorphicForm.height b') := by
    calc _ ≤ ∏ᶠ v : HeightOneSpectrum (𝓞 K), AutomorphicForm.locHeight (finAt v (b * m * b')) :=
          finprod_le_finprod₀ (Filter.eventually_cofinite.1 (eventually_norm_eq_one hc))
            (fun _ => norm_nonneg _) (AutomorphicForm.finite_mulSupport_locHeight_finAt _) hv
      _ ≤ AutomorphicForm.height (b * m * b') :=
          le_mul_of_one_le_left (zero_le_one.trans (AutomorphicForm.one_le_finprod_locHeight _))
            (AutomorphicForm.one_le_prod_locHeight _)
      _ ≤ AutomorphicForm.heightConst K n * AutomorphicForm.height (b * m) * AutomorphicForm.height b' :=
          AutomorphicForm.height_mul_le _ _
      _ ≤ AutomorphicForm.heightConst K n * (AutomorphicForm.heightConst K n *
            AutomorphicForm.height b * AutomorphicForm.height m) * AutomorphicForm.height b' := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
            (AutomorphicForm.height_mul_le _ _) (zero_le_one.trans hC)) pb'.le
      _ = _ := by ring
  have hC0 : 0 < AutomorphicForm.heightConst K n := zero_lt_one.trans_le hC
  calc (1 : ℝ) = _ := (prod_norm_mul_finprod_norm hc).symm
    _ ≤ (((n : ℝ) ^ 2 * ε) ^ Module.finrank ℚ K *
          (AutomorphicForm.height b * AutomorphicForm.height m * AutomorphicForm.height b')) *
        (AutomorphicForm.heightConst K n ^ 2 *
          (AutomorphicForm.height b * AutomorphicForm.height m * AutomorphicForm.height b')) :=
        mul_le_mul hI hF (finprod_nonneg fun _ => norm_nonneg _) (by positivity)
    _ = _ := by ring
end

-- bundled from Development.AutomorphicArithmetic.AdelicQuotients.OneLeHeightOffAndSubmultiplicative
section
open NumberField IsDedekindDomain Polynomial
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Global GroundTheory.Global.SemiLocal GroundTheory.Global.AdeleBaseChange
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Loc PositivityTheory.Rg.Tf.Geo
open scoped NumberField.AdeleRing

theorem UpperTheory.one_le_heightOff_and_submultiplicative :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) (q : HeightOneSpectrum (𝓞 F)),
        (∀ g : AdelicGLn.AdelicGL E n, 1 ≤ heightOff q g) ∧ heightOff q (1 : AdelicGLn.AdelicGL E n) = 1 ∧
        ∀ g h : AdelicGLn.AdelicGL E n, heightOff q (g * h) ≤ AutomorphicForm.heightConst E n * heightOff q g * heightOff q h := by
  classical
  intro F E _ _ _ _ _ n q
  let f : AdelicGLn.AdelicGL E n → HeightOneSpectrum (𝓞 E) → ℝ := fun x w =>
    if below F w ≠ q then AutomorphicForm.locHeight (finAt w x) else 1
  have hoff : ∀ x : AdelicGLn.AdelicGL E n, heightOff q x =
      (∏ w : InfinitePlace E, AutomorphicForm.locHeight (infAt w x) ^ w.mult) * ∏ᶠ w, f x w := by
    intro x
    unfold heightOff
    congr 1
    exact finprod_congr fun w => finprod_eq_if
  have hone : ∀ x w, 1 ≤ f x w := by
    intro x w
    simp only [f]
    split_ifs
    · exact AutomorphicForm.one_le_locHeight _
    · exact le_rfl
  have hsupp : ∀ x, (Function.mulSupport (f x)).Finite := by
    intro x
    refine (AutomorphicForm.finite_mulSupport_locHeight_finAt x).subset ?_
    intro w hw
    simp only [Function.mem_mulSupport, f] at hw ⊢
    intro h
    apply hw
    rw [h]
    simp
  have hfi1 : ∀ x, 1 ≤ ∏ᶠ w, f x w := fun x =>
    finprod_induction (fun y : ℝ => 1 ≤ y) le_rfl
      (fun _ _ hx hy => one_le_mul_of_one_le_of_one_le hx hy) (hone x)
  refine ⟨fun g => ?_, ?_, fun g h => ?_⟩
  · rw [hoff]
    exact one_le_mul_of_one_le_of_one_le (AutomorphicForm.one_le_prod_locHeight g) (hfi1 g)
  · have h1 : ∀ w, f 1 w = 1 := by
      intro w
      simp [f, AutomorphicForm.locHeight_one]
    rw [hoff, finprod_eq_one_of_forall_eq_one h1]
    simp [AutomorphicForm.locHeight_one]
  · set s := ((hsupp g).union (hsupp h)).union (hsupp (g * h))
    have hfin : ∀ x : AdelicGLn.AdelicGL E n, x = g ∨ x = h ∨ x = g * h →
        ∏ᶠ w, f x w = ∏ w ∈ s.toFinset, f x w := by
      intro x hx
      refine finprod_eq_prod_of_mulSupport_subset _ ?_
      intro v hv
      simp only [Set.Finite.coe_toFinset, Set.mem_union]
      rcases hx with rfl | rfl | rfl
      · exact Or.inl (Or.inl hv)
      · exact Or.inl (Or.inr hv)
      · exact Or.inr hv
    have hf : ∏ᶠ w, f (g * h) w ≤ (∏ᶠ w, f g w) * ∏ᶠ w, f h w := by
      rw [hfin _ (Or.inr (Or.inr rfl)), hfin _ (Or.inl rfl), hfin _ (Or.inr (Or.inl rfl)),
        ← Finset.prod_mul_distrib]
      refine Finset.prod_le_prod₀ (fun v _ => le_trans zero_le_one (hone _ v)) fun v _ => ?_
      simp only [f]
      split_ifs
      · rw [finAt_mul]
        exact AutomorphicForm.locHeight_mul_le_of_ultrametric _ _
      · simp
    have hi : (∏ w : InfinitePlace E, AutomorphicForm.locHeight (infAt w (g * h)) ^ w.mult) ≤
        AutomorphicForm.heightConst E n *
          (∏ w : InfinitePlace E, AutomorphicForm.locHeight (infAt w g) ^ w.mult) *
          ∏ w : InfinitePlace E, AutomorphicForm.locHeight (infAt w h) ^ w.mult := by
      rw [AutomorphicForm.heightConst, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
      refine Finset.prod_le_prod₀
        (fun w _ => by have := AutomorphicForm.locHeight_pos (infAt w (g * h)); positivity)
        fun w _ => ?_
      rw [← mul_pow, ← mul_pow, infAt_mul]
      exact pow_le_pow_left₀ (AutomorphicForm.locHeight_pos _).le
        (AutomorphicForm.locHeight_mul_le _ _) _
    rw [hoff, hoff, hoff]
    calc (∏ w : InfinitePlace E, AutomorphicForm.locHeight (infAt w (g * h)) ^ w.mult) *
          ∏ᶠ w, f (g * h) w
        ≤ (AutomorphicForm.heightConst E n *
            (∏ w : InfinitePlace E, AutomorphicForm.locHeight (infAt w g) ^ w.mult) *
            ∏ w : InfinitePlace E, AutomorphicForm.locHeight (infAt w h) ^ w.mult) *
          ((∏ᶠ w, f g w) * ∏ᶠ w, f h w) :=
          mul_le_mul hi hf (le_trans zero_le_one (hfi1 _))
            (mul_nonneg (mul_nonneg (le_trans zero_le_one AutomorphicForm.one_le_heightConst)
              (le_trans zero_le_one (AutomorphicForm.one_le_prod_locHeight g)))
              (le_trans zero_le_one (AutomorphicForm.one_le_prod_locHeight h)))
      _ = _ := by ring
end

-- bundled from Development.AutomorphicArithmetic.AdelicQuotients.OneLeMulHeightConstHeightOffPowOfSmallAtPlace
section
open NumberField IsDedekindDomain Polynomial
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Global GroundTheory.Global.SemiLocal GroundTheory.Global.AdeleBaseChange
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Loc PositivityTheory.Rg.Tf.Geo
open scoped NumberField.AdeleRing

private theorem finprod_le_mul_finprod_pow {ι : Type*} {N b : ι → ℝ} (hN : (Function.mulSupport N).Finite)
    (hb : (Function.mulSupport b).Finite) (i₀ : ι) (ε : ℝ) (m : ℕ) (N0 : ∀ i, 0 ≤ N i)
    (hi₀ : b i₀ = 1) (h0 : N i₀ ≤ ε) (h : ∀ i, i ≠ i₀ → N i ≤ b i ^ m) :
    ∏ᶠ i, N i ≤ ε * (∏ᶠ i, b i) ^ m := by
  classical
  set s : Finset ι := (hN.toFinset ∪ hb.toFinset) ∪ {i₀} with hs
  have hi : i₀ ∈ s := by simp [hs]
  rw [finprod_eq_prod_of_mulSupport_subset N (s := s)
      (fun v hv => by simp only [hs, Finset.coe_union, Set.Finite.coe_toFinset]; exact Or.inl (Or.inl hv)),
    finprod_eq_prod_of_mulSupport_subset b (s := s)
      (fun v hv => by simp only [hs, Finset.coe_union, Set.Finite.coe_toFinset]; exact Or.inl (Or.inr hv)),
    ← Finset.mul_prod_erase s N hi, ← Finset.mul_prod_erase s b hi, hi₀, one_mul, ← Finset.prod_pow]
  exact mul_le_mul h0 (Finset.prod_le_prod₀ (fun i _ => N0 i) fun i hi' => h i (Finset.ne_of_mem_erase hi'))
    (Finset.prod_nonneg fun i _ => N0 i) ((N0 _).trans h0)

theorem UpperTheory.one_le_mul_heightConst_heightOff_pow_of_small_at_place :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) (q : HeightOneSpectrum (𝓞 F)) (w₀ : PlacesOver E q) (g : AdelicGLn.AdelicGL E n) (a : E) (ε : ℝ), a ≠ 0 →
        (∀ w : InfinitePlace E, ‖algebraMap E w.Completion a‖ ≤ (max 1 (n : ℝ) * AutomorphicForm.locHeight (infAt w g)) ^ n) →
        (∀ w : HeightOneSpectrum (𝓞 E), ‖algebraMap E (w.adicCompletion E) a‖ ≤ AutomorphicForm.locHeight (finAt w g) ^ n) →
        (∀ w : PlacesOver E q, ‖algebraMap E (w.1.adicCompletion E) a‖ ≤ 1) →
        ‖algebraMap E (w₀.1.adicCompletion E) a‖ ≤ ε →
        1 ≤ ε * (AutomorphicForm.heightConst E n * heightOff q g) ^ n := by
  intro F E _ _ _ _ _ n q w₀ g a ε ha hinf hfin hq h0
  classical
  have hprod : (∏ w : InfinitePlace E, ‖algebraMap E w.Completion a‖ ^ w.mult) *
      ∏ᶠ v : HeightOneSpectrum (𝓞 E), ‖algebraMap E (v.adicCompletion E) a‖ = 1 :=
    by
      simpa only [InfinitePlace.Completion.algebraMap_apply,
        HeightOneSpectrum.algebraMap_adicCompletion, Function.comp_apply,
        Algebra.algebraMap_self_apply] using prod_norm_mul_finprod_norm ha
  have hNfin : (Function.mulSupport fun v : HeightOneSpectrum (𝓞 E) =>
      ‖algebraMap E (v.adicCompletion E) a‖).Finite :=
    Filter.eventually_cofinite.1 (eventually_norm_eq_one ha)
  set b : HeightOneSpectrum (𝓞 E) → ℝ := fun v =>
    if below F v ≠ q then AutomorphicForm.locHeight (finAt v g) else 1 with hb
  have hbfin : (Function.mulSupport b).Finite := by
    refine (AutomorphicForm.finite_mulSupport_locHeight_finAt g).subset fun v hv => ?_
    simp only [Function.mem_mulSupport, hb] at hv ⊢
    intro h1
    exact hv (by simp [h1])
  have hw₀ : below F w₀.1 = q := by
    have := w₀.2.over
    exact HeightOneSpectrum.ext this.symm
  have hF : ∏ᶠ v : HeightOneSpectrum (𝓞 E), ‖algebraMap E (v.adicCompletion E) a‖ ≤
      ε * (∏ᶠ v, b v) ^ n := by
    refine finprod_le_mul_finprod_pow hNfin hbfin w₀.1 ε n (fun _ => norm_nonneg _) (by simp [hb, hw₀]) h0 fun v _ => ?_
    by_cases hv : below F v = q
    · have hl : v.asIdeal.LiesOver q.asIdeal := ⟨(congrArg HeightOneSpectrum.asIdeal hv).symm⟩
      have := hq ⟨v, hl⟩
      simpa [hb, hv] using this
    · simpa [hb, hv] using hfin v
  set A : ℝ := ∏ w : InfinitePlace E, AutomorphicForm.locHeight (infAt w g) ^ w.mult with hA
  have hI : (∏ w : InfinitePlace E, ‖algebraMap E w.Completion a‖ ^ w.mult) ≤
      (AutomorphicForm.heightConst E n * A) ^ n := by
    have e : (AutomorphicForm.heightConst E n * A) ^ n =
        ∏ w : InfinitePlace E, ((max 1 (n : ℝ) * AutomorphicForm.locHeight (infAt w g)) ^ n) ^ w.mult := by
      rw [AutomorphicForm.heightConst, hA, ← Finset.prod_mul_distrib, ← Finset.prod_pow]
      refine Finset.prod_congr rfl fun w _ => ?_
      rw [← mul_pow, ← pow_mul, ← pow_mul, mul_comm n]
    rw [e]
    exact Finset.prod_le_prod₀ (fun _ _ => pow_nonneg (norm_nonneg _) _) fun w _ =>
      pow_le_pow_left₀ (norm_nonneg _) (hinf w) _
  have hoff : heightOff q g = A * ∏ᶠ v, b v := by
    simp only [heightOff, hA, hb, finprod_eq_if]
  have hC : 0 ≤ (AutomorphicForm.heightConst E n * A) ^ n := by
    refine pow_nonneg (mul_nonneg (zero_le_one.trans AutomorphicForm.one_le_heightConst) ?_) _
    exact Finset.prod_nonneg fun _ _ => pow_nonneg (AutomorphicForm.locHeight_pos _).le _
  calc (1 : ℝ) = _ := hprod.symm
    _ ≤ (AutomorphicForm.heightConst E n * A) ^ n * (ε * (∏ᶠ v, b v) ^ n) :=
        mul_le_mul hI hF (finprod_nonneg fun _ => norm_nonneg _) hC
    _ = ε * (AutomorphicForm.heightConst E n * heightOff q g) ^ n := by
        rw [hoff]; simp only [mul_pow]; ring
end

-- bundled from Development.AutomorphicArithmetic.AdelicQuotients.UnimodularFiniteQuotientMeasureOfCocompact
section
open MeasureTheory NumberField IsDedekindDomain Polynomial
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Global GroundTheory.Global.SemiLocal
open GroundTheory.Global.AdeleBaseChange
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Loc PositivityTheory.Rg.Tf.Geo
open scoped ENNReal NumberField.AdeleRing TensorProduct

theorem UpperTheory.unimodular_finite_quotientMeasure_of_cocompact :
    ∀ (T : Type) [Group T] [TopologicalSpace T] [IsTopologicalGroup T] [LocallyCompactSpace T] [T2Space T] [SecondCountableTopology T] [MeasurableSpace T] [BorelSpace T] (Λ : Subgroup T) [DiscreteTopology Λ] (ν : Measure T) [ν.IsHaarMeasure],
        (∃ C : Set T, IsCompact C ∧ ∀ t : T, ∃ g ∈ Λ, ∃ y ∈ C, t = g * y) →
        ν.IsMulRightInvariant ∧ ν.IsInvInvariant ∧ quotientMeasure Λ ν Set.univ < ⊤ := by
  intro T _ _ _ _ _ _ _ _ Λ _ ν _ hC
  obtain ⟨C, hC, h⟩ := hC
  haveI : CompactSpace (RightCosetSpace Λ) := by
    refine ⟨(hC.image (RightCosetSpace.continuous_mk Λ)).of_isClosed_subset isClosed_univ ?_⟩
    intro x _
    obtain ⟨t, rfl⟩ := RightCosetSpace.mk_surjective Λ x
    obtain ⟨g, hg, y, hy, rfl⟩ := h t
    exact ⟨y, hy, (RightCosetSpace.mk_mul_of_mem hg y).symm⟩
  haveI hr : ν.IsMulRightInvariant := RightCosetSpace.isMulRightInvariant_of_compactSpace Λ ν
  haveI := RightCosetSpace.isFiniteMeasure (Γ := Λ) ν
  exact ⟨hr, ⟨RightCosetSpace.inv_eq_self_of_isMulRightInvariant ν⟩, measure_lt_top _ _⟩
end

