module

public import Mathlib

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.BlockEmb
section
noncomputable section

namespace PI.AprimeInfG

open scoped Matrix

variable {n k : ℕ} {S : Finset (Fin n)}

def emb0 (e : Fin k ≃ S) (X : Matrix (Fin k) (Fin k) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  fun i j => if h : i ∈ S ∧ j ∈ S then X (e.symm ⟨i, h.1⟩) (e.symm ⟨j, h.2⟩) else 0

def blockEmbeddingAddHom (e : Fin k ≃ S) : Matrix (Fin k) (Fin k) ℂ →+ Matrix (Fin n) (Fin n) ℂ where
  toFun := emb0 e
  map_zero' := by
    funext i j
    simp [emb0]
  map_add' X Y := by
    funext i j
    simp only [emb0, Matrix.add_apply]
    split_ifs <;> simp

private theorem emb0_apply_coe_coe (e : Fin k ≃ S) (X : Matrix (Fin k) (Fin k) ℂ) (a b : Fin k) :
    emb0 e X (e a) (e b) = X a b := by
  simp [emb0]

private theorem emb0_apply_of_left_not_mem (e : Fin k ≃ S) (X : Matrix (Fin k) (Fin k) ℂ) {i j : Fin n}
    (hi : i ∉ S) : emb0 e X i j = 0 := by
  simp [emb0, hi]

private theorem emb0_apply_of_right_not_mem (e : Fin k ≃ S) (X : Matrix (Fin k) (Fin k) ℂ) {i j : Fin n}
    (hj : j ∉ S) : emb0 e X i j = 0 := by
  simp [emb0, hj]

private theorem exists_equiv_coe_eq_of_mem (e : Fin k ≃ S) {i : Fin n} (hi : i ∈ S) :
    ∃ a, (e a : Fin n) = i :=
  ⟨e.symm ⟨i, hi⟩, by simp⟩

private theorem sum_eq_sum_equiv_of_eq_zero_of_not_mem {M : Type*} [AddCommMonoid M] (e : Fin k ≃ S) (F : Fin n → M)
    (hF : ∀ l, l ∉ S → F l = 0) : ∑ l, F l = ∑ c, F (e c) := by
  rw [← Finset.sum_subset (Finset.subset_univ S) (fun l _ hl => hF l hl), ← Finset.sum_coe_sort S]
  exact (Equiv.sum_comp e (fun x : S => F x)).symm

theorem embed_mul (e : Fin k ≃ S) (X Y : Matrix (Fin k) (Fin k) ℂ) :
    emb0 e (X * Y) = emb0 e X * emb0 e Y := by
  ext i j
  rw [Matrix.mul_apply]
  by_cases hi : i ∈ S
  · by_cases hj : j ∈ S
    · obtain ⟨a, rfl⟩ := exists_equiv_coe_eq_of_mem e hi
      obtain ⟨b, rfl⟩ := exists_equiv_coe_eq_of_mem e hj
      rw [emb0_apply_coe_coe, Matrix.mul_apply, sum_eq_sum_equiv_of_eq_zero_of_not_mem e]
      · simp only [emb0_apply_coe_coe]
      · intro l hl
        simp [emb0_apply_of_right_not_mem e X hl]
    · rw [emb0_apply_of_right_not_mem e _ hj]
      symm
      exact Finset.sum_eq_zero (fun l _ => by rw [emb0_apply_of_right_not_mem e Y hj, mul_zero])
  · rw [emb0_apply_of_left_not_mem e _ hi]
    symm
    exact Finset.sum_eq_zero (fun l _ => by rw [emb0_apply_of_left_not_mem e X hi, zero_mul])

theorem embed_pow_succ (e : Fin k ≃ S) (X : Matrix (Fin k) (Fin k) ℂ) (m : ℕ) :
    emb0 e (X ^ (m + 1)) = emb0 e X ^ (m + 1) := by
  induction m with
  | zero => simp only [zero_add, pow_one]
  | succ m ih => rw [pow_succ, embed_mul, ih, ← pow_succ]

private theorem emb0Add_apply (e : Fin k ≃ S) (X : Matrix (Fin k) (Fin k) ℂ) :
    blockEmbeddingAddHom e X = emb0 e X :=
  rfl

private theorem emb0_smul (e : Fin k ≃ S) (c : ℂ) (X : Matrix (Fin k) (Fin k) ℂ) :
    emb0 e (c • X) = c • emb0 e X := by
  ext i j
  rw [Matrix.smul_apply]
  by_cases hi : i ∈ S
  · by_cases hj : j ∈ S
    · obtain ⟨a, rfl⟩ := exists_equiv_coe_eq_of_mem e hi
      obtain ⟨b, rfl⟩ := exists_equiv_coe_eq_of_mem e hj
      rw [emb0_apply_coe_coe, emb0_apply_coe_coe, Matrix.smul_apply]
    · rw [emb0_apply_of_right_not_mem e _ hj, emb0_apply_of_right_not_mem e _ hj, smul_zero]
  · rw [emb0_apply_of_left_not_mem e _ hi, emb0_apply_of_left_not_mem e _ hi, smul_zero]

theorem continuous_embed (e : Fin k ≃ S) : Continuous (emb0 e) := by
  refine continuous_matrix fun i j => ?_
  by_cases h : i ∈ S ∧ j ∈ S
  · simp only [emb0, dif_pos h]
    exact continuous_id.matrix_elem _ _
  · simp only [emb0, dif_neg h]
    exact continuous_const


set_option backward.isDefEq.respectTransparency false in
theorem exp_embed (e : Fin k ≃ S) (X : Matrix (Fin k) (Fin k) ℂ) :
    NormedSpace.exp (emb0 e X) = emb0 e (NormedSpace.exp X) + (1 - emb0 e 1) := by
  letI : NormedRing (Matrix (Fin k) (Fin k) ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℂ (Matrix (Fin k) (Fin k) ℂ) := Matrix.linftyOpNormedAlgebra
  letI : NormedRing (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℂ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedAlgebra
  have h1 := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) X
  have h2 := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) (emb0 e X)
  have h3 := (h1.map (blockEmbeddingAddHom e) (continuous_embed e)).add
    (hasSum_ite_eq 0 (1 - emb0 e 1))
  refine h2.unique ?_
  convert h3 using 1
  all_goals try rfl
  funext m
  rcases m with _ | m
  · simp [emb0Add_apply]
  · simp [emb0Add_apply, emb0_smul, embed_pow_succ]

def resB (e : Fin k ≃ S) (M : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin k) (Fin k) ℂ :=
  fun a b => M (e a) (e b)

theorem restrict_embed (e : Fin k ≃ S) (X : Matrix (Fin k) (Fin k) ℂ) : resB e (emb0 e X) = X := by
  ext a b
  exact emb0_apply_coe_coe e X a b

theorem embed_restrict (e : Fin k ≃ S) (M : Matrix (Fin n) (Fin n) ℂ) (hM : ∀ i j, (i ∉ S ∨ j ∉ S) → M i j = 0) :
    emb0 e (resB e M) = M := by
  ext i j
  by_cases hi : i ∈ S
  · by_cases hj : j ∈ S
    · obtain ⟨a, rfl⟩ := exists_equiv_coe_eq_of_mem e hi
      obtain ⟨b, rfl⟩ := exists_equiv_coe_eq_of_mem e hj
      rw [emb0_apply_coe_coe]
      rfl
    · rw [emb0_apply_of_right_not_mem e _ hj, hM i j (Or.inr hj)]
  · rw [emb0_apply_of_left_not_mem e _ hi, hM i j (Or.inl hi)]

theorem embed_conjTranspose (e : Fin k ≃ S) (X : Matrix (Fin k) (Fin k) ℂ) :
    emb0 e Xᴴ = (emb0 e X)ᴴ := by
  ext i j
  rw [Matrix.conjTranspose_apply]
  by_cases hi : i ∈ S
  · by_cases hj : j ∈ S
    · obtain ⟨a, rfl⟩ := exists_equiv_coe_eq_of_mem e hi
      obtain ⟨b, rfl⟩ := exists_equiv_coe_eq_of_mem e hj
      rw [emb0_apply_coe_coe, emb0_apply_coe_coe, Matrix.conjTranspose_apply]
    · rw [emb0_apply_of_right_not_mem e _ hj, emb0_apply_of_left_not_mem e _ hj, star_zero]
  · rw [emb0_apply_of_left_not_mem e _ hi, emb0_apply_of_right_not_mem e _ hi, star_zero]

theorem sum_norm_sq_embed (e : Fin k ≃ S) (X : Matrix (Fin k) (Fin k) ℂ) :
    (∑ i, ∑ j, ‖emb0 e X i j‖ ^ 2) = ∑ a, ∑ b, ‖X a b‖ ^ 2 := by
  rw [sum_eq_sum_equiv_of_eq_zero_of_not_mem e]
  · refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [sum_eq_sum_equiv_of_eq_zero_of_not_mem e]
    · simp only [emb0_apply_coe_coe]
    · intro j hj
      simp [emb0_apply_of_right_not_mem e X hj]
  · intro i hi
    simp [emb0_apply_of_left_not_mem e X hi]

end PI.AprimeInfG
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.ChartChg
section
noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Topology

theorem chart_change {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] {Y : Type} [MeasurableSpace Y]
    (m : Measure Y) (χ : E → Y) (V : Set E) (f : E → ℝ)
    (hχ : ∀ S ⊆ V, MeasurableSet S → m (χ '' S) = ∫⁻ x in S, ENNReal.ofReal (f x) ∂μ)
    (ψ : E → E) (ψ' : E → E →L[ℝ] E) (U : Set E) (hψ : ∀ x ∈ U, HasFDerivWithinAt ψ (ψ' x) U x)
    (hinj : Set.InjOn ψ U) (hψV : ψ '' U ⊆ V) (A : Set E) (hAU : A ⊆ U) (hA : MeasurableSet A) :
    m ((χ ∘ ψ) '' A) = ∫⁻ p in A, ENNReal.ofReal (|(ψ' p).det| * f (ψ p)) ∂μ := by
  have hd : ∀ x ∈ A, HasFDerivWithinAt ψ (ψ' x) A x := fun x hx => (hψ x (hAU hx)).mono hAU
  have hinjA : Set.InjOn ψ A := hinj.mono hAU
  have hmeas : MeasurableSet (ψ '' A) := measurable_image_of_fderivWithin hA hd hinjA
  rw [Set.image_comp, hχ _ ((Set.image_mono hAU).trans hψV) hmeas,
    lintegral_image_eq_lintegral_abs_det_fderiv_mul μ hA hd hinjA]
  refine lintegral_congr fun p => ?_
  rw [ENNReal.ofReal_mul (abs_nonneg _)]

theorem chart_change_cont {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (f : E → ℝ) (ψ : E → E) (ψ' : E → E →L[ℝ] E) (x₀ : E) (hψ : ContinuousAt ψ x₀)
    (hf : ContinuousAt f (ψ x₀)) (hd : ContinuousAt (fun p => (ψ' p).det) x₀) :
    ContinuousAt (fun p => |(ψ' p).det| * f (ψ p)) x₀ := (continuous_abs.continuousAt.comp hd).mul (hf.comp hψ)

end PI.AprimeInfW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.ExistsLocalSolutionContDiffAt
section
noncomputable section

namespace PI.AprimeInfW

open Topology Filter

theorem exists_local_solution_contDiffAt {V : Type} [AddCommGroup V] [TopologicalSpace V] {N : ℕ}
    (e : V ≃ₜ (Fin N → ℝ)) (he : ∀ x y, e (x + y) = e x + e y)
    (B : V → V → V) (hB1 : ∀ x x' y, B (x + x') y = B x y + B x' y)
    (hB2 : ∀ x y y', B x (y + y') = B x y + B x y')
    (hBc : Continuous (fun p : V × V => B p.1 p.2))
    (L : V → V) (hL : ∀ x y, L (x + y) = L x + L y) (hLc : Continuous L)
    (x0 : V) (hD : ∀ u, B x0 u + B u x0 + L u = u + u) :
    ∃ g : V → V, ContinuousAt g (B x0 x0 + L x0) ∧ g (B x0 x0 + L x0) = x0 ∧
      (∀ᶠ y in 𝓝 (B x0 x0 + L x0), B (g y) (g y) + L (g y) = y) ∧
      ContDiffAt ℝ 1 (fun y => e (g (e.symm y))) (e (B x0 x0 + L x0)) ∧
      HasFDerivAt (fun y => e (g (e.symm y))) ((1 / 2 : ℝ) • ContinuousLinearMap.id ℝ (Fin N → ℝ))
        (e (B x0 x0 + L x0)) := by
  classical
  have hes : ∀ u w, e.symm (u + w) = e.symm u + e.symm w := by
    intro u w
    apply e.injective
    rw [he]
    simp
  let b : (Fin N → ℝ) → (Fin N → ℝ) → (Fin N → ℝ) := fun u w => e (B (e.symm u) (e.symm w))
  let l : (Fin N → ℝ) → (Fin N → ℝ) := fun u => e (L (e.symm u))
  have hb1 : ∀ u u' w, b (u + u') w = b u w + b u' w := by
    intro u u' w
    simp only [b, hes, hB1, he]
  have hb2 : ∀ u w w', b u (w + w') = b u w + b u w' := by
    intro u w w'
    simp only [b, hes, hB2, he]
  have hl1 : ∀ u u', l (u + u') = l u + l u' := by
    intro u u'
    simp only [l, hes, hL, he]
  have hbc : Continuous (fun p : (Fin N → ℝ) × (Fin N → ℝ) => b p.1 p.2) :=
    e.continuous.comp (hBc.comp ((e.symm.continuous.comp continuous_fst).prodMk
      (e.symm.continuous.comp continuous_snd)))
  have hlc : Continuous l := e.continuous.comp (hLc.comp e.symm.continuous)
  have hbs1 : ∀ (c : ℝ) u w, b (c • u) w = c • b u w := by
    intro c u w
    exact map_real_smul (AddMonoidHom.mk' (fun u => b u w) (fun u u' => hb1 u u' w))
      (hbc.comp (continuous_id.prodMk continuous_const)) c u
  have hbs2 : ∀ (c : ℝ) u w, b u (c • w) = c • b u w := by
    intro c u w
    exact map_real_smul (AddMonoidHom.mk' (fun w => b u w) (fun w w' => hb2 u w w'))
      (hbc.comp (continuous_const.prodMk continuous_id)) c w
  let b₂ : (Fin N → ℝ) →ₗ[ℝ] (Fin N → ℝ) →ₗ[ℝ] (Fin N → ℝ) := LinearMap.mk₂ ℝ b hb1 hbs1 hb2 hbs2
  let bL : (Fin N → ℝ) →L[ℝ] (Fin N → ℝ) →L[ℝ] (Fin N → ℝ) :=
    LinearMap.toContinuousLinearMap
      ((LinearMap.toContinuousLinearMap : ((Fin N → ℝ) →ₗ[ℝ] (Fin N → ℝ)) ≃ₗ[ℝ]
        ((Fin N → ℝ) →L[ℝ] (Fin N → ℝ))).toLinearMap ∘ₗ b₂)
  let lL : (Fin N → ℝ) →L[ℝ] (Fin N → ℝ) := (AddMonoidHom.mk' l hl1).toRealLinearMap hlc
  have hbL : ∀ u w, bL u w = b u w := fun u w => rfl
  have hlL : ∀ u, lL u = l u := fun u => rfl
  let Ft : (Fin N → ℝ) → (Fin N → ℝ) := fun u => bL u u + lL u
  have hFt : ∀ u, Ft u = e (B (e.symm u) (e.symm u) + L (e.symm u)) := by
    intro u
    simp only [Ft, hbL, hlL, b, l, he]
  set u0 := e x0 with hu0
  have hy0 : Ft u0 = e (B x0 x0 + L x0) := by rw [hFt, hu0, e.symm_apply_apply]
  have hTwo : ∀ w, bL u0 w + bL w u0 + lL w = (2 : ℝ) • w := by
    intro w
    have h := congrArg e (hD (e.symm w))
    rw [he, he, he, e.apply_symm_apply] at h
    rw [hbL, hbL, hlL, two_smul]
    simpa [b, l, hu0] using h
  let f₁ : (Fin N → ℝ) →L[ℝ] (Fin N → ℝ) := (2 : ℝ) • ContinuousLinearMap.id ℝ (Fin N → ℝ)
  let f₂ : (Fin N → ℝ) →L[ℝ] (Fin N → ℝ) := (1 / 2 : ℝ) • ContinuousLinearMap.id ℝ (Fin N → ℝ)
  have h12 : Function.LeftInverse f₂ f₁ := fun w => by
    simp only [f₁, f₂, ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, smul_smul]
    norm_num
  have h21 : Function.RightInverse f₂ f₁ := fun w => by
    simp only [f₁, f₂, ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, smul_smul]
    norm_num
  let fe : (Fin N → ℝ) ≃L[ℝ] (Fin N → ℝ) := ContinuousLinearEquiv.equivOfInverse f₁ f₂ h12 h21
  have hFs : HasStrictFDerivAt Ft (fe : (Fin N → ℝ) →L[ℝ] (Fin N → ℝ)) u0 := by
    have h0 := (bL.hasStrictFDerivAt_of_bilinear (hasStrictFDerivAt_id u0)
      (hasStrictFDerivAt_id u0)).add lL.hasStrictFDerivAt
    refine h0.congr_fderiv ?_
    ext1 w
    show bL u0 w + bL w u0 + lL w = (fe : (Fin N → ℝ) →L[ℝ] (Fin N → ℝ)) w
    rw [hTwo]
    rfl
  have hcd : ContDiffAt ℝ 1 Ft u0 :=
    ((bL.isBoundedBilinearMap.contDiff.comp (contDiff_id.prodMk contDiff_id)).add
      lL.contDiff).contDiffAt
  have hs : HasStrictFDerivAt Ft (fe : (Fin N → ℝ) →L[ℝ] (Fin N → ℝ)) u0 :=
    hcd.hasStrictFDerivAt' hFs.hasFDerivAt one_ne_zero
  let G := hcd.localInverse hFs.hasFDerivAt one_ne_zero
  have hGc : ContinuousAt G (Ft u0) := hs.localInverse_continuousAt
  have hGa : G (Ft u0) = u0 := hs.localInverse_apply_image
  have hGr : ∀ᶠ w in 𝓝 (Ft u0), Ft (G w) = w := hs.eventually_right_inverse
  have hGd : ContDiffAt ℝ 1 G (Ft u0) := hcd.to_localInverse hFs.hasFDerivAt one_ne_zero
  have hGf : HasFDerivAt G ((fe.symm : (Fin N → ℝ) →L[ℝ] (Fin N → ℝ))) (Ft u0) :=
    hs.to_localInverse.hasFDerivAt
  rw [hy0] at hGc hGa hGr hGd hGf
  refine ⟨fun y => e.symm (G (e y)), ?_, ?_, ?_, ?_, ?_⟩
  · exact e.symm.continuous.continuousAt.comp (hGc.comp e.continuous.continuousAt)
  · simp only [hGa, hu0, e.symm_apply_apply]
  · have ht : ∀ᶠ y in 𝓝 (B x0 x0 + L x0), Ft (G (e y)) = e y :=
      (e.continuous.tendsto (B x0 x0 + L x0)).eventually hGr
    filter_upwards [ht] with y hy
    rw [hFt] at hy
    exact e.injective (by rw [he]; simpa [he] using hy)
  · have hfun : (fun y => e (e.symm (G (e (e.symm y))))) = G := by
      funext y
      simp
    rw [hfun]
    exact hGd
  · have hfun : (fun y => e (e.symm (G (e (e.symm y))))) = G := by
      funext y
      simp
    rw [hfun]
    convert hGf using 1
    ext1 w
    rfl

end PI.AprimeInfW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.ExistsLocalSolve
section
noncomputable section

namespace PI.AprimeInfW

open Topology Filter

private theorem local_right_inverse_lemma {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (F : E → E) (f' : E ≃L[ℝ] E) (a : E)
    (hf : HasStrictFDerivAt F (f' : E →L[ℝ] E) a) :
    ∃ φ : E → E, ContinuousAt φ (F a) ∧ φ (F a) = a ∧ ∀ᶠ y in 𝓝 (F a), F (φ y) = y :=
  ⟨hf.localInverse F f' a, hf.localInverse_continuousAt, hf.localInverse_apply_image,
    hf.eventually_right_inverse⟩

theorem exists_local_solve {V : Type} [AddCommGroup V] [TopologicalSpace V] {N : ℕ}
    (e : V ≃ₜ (Fin N → ℝ)) (he : ∀ x y, e (x + y) = e x + e y)
    (B : V → V → V) (hB1 : ∀ x x' y, B (x + x') y = B x y + B x' y)
    (hB2 : ∀ x y y', B x (y + y') = B x y + B x y')
    (hBc : Continuous (fun p : V × V => B p.1 p.2))
    (L : V → V) (hL : ∀ x y, L (x + y) = L x + L y) (hLc : Continuous L)
    (x0 : V) (hD : ∀ u, B x0 u + B u x0 + L u = u + u) :
    ∃ g : V → V, ContinuousAt g (B x0 x0 + L x0) ∧ g (B x0 x0 + L x0) = x0 ∧
      ∀ᶠ y in 𝓝 (B x0 x0 + L x0), B (g y) (g y) + L (g y) = y := by
  have hs : ∀ a b : Fin N → ℝ, e.symm (a + b) = e.symm a + e.symm b := fun a b =>
    e.injective (by rw [he]; simp)
  let b : (Fin N → ℝ) → (Fin N → ℝ) → (Fin N → ℝ) := fun z w => e (B (e.symm z) (e.symm w))
  have hb1 : ∀ z z' w, b (z + z') w = b z w + b z' w := fun z z' w => by
    simp only [b]; rw [hs, hB1, he]
  have hb2 : ∀ z w w', b z (w + w') = b z w + b z w' := fun z w w' => by
    simp only [b]; rw [hs, hB2, he]
  have hpair : Continuous fun p : (Fin N → ℝ) × (Fin N → ℝ) => (e.symm p.1, e.symm p.2) :=
    (e.symm.continuous.comp continuous_fst).prodMk (e.symm.continuous.comp continuous_snd)
  have hbc : Continuous fun p : (Fin N → ℝ) × (Fin N → ℝ) => b p.1 p.2 :=
    e.continuous.comp (hBc.comp hpair)
  have hb3 : ∀ (c : ℝ) z w, b (c • z) w = c • b z w := fun c z w =>
    map_real_smul (AddMonoidHom.mk' (fun z => b z w) fun z z' => hb1 z z' w)
      (hbc.comp (continuous_id.prodMk continuous_const)) c z
  have hb4 : ∀ (c : ℝ) z w, b z (c • w) = c • b z w := fun c z w =>
    map_real_smul (AddMonoidHom.mk' (fun w => b z w) fun w w' => hb2 z w w')
      (hbc.comp (continuous_const.prodMk continuous_id)) c w
  let l : (Fin N → ℝ) → (Fin N → ℝ) := fun z => e (L (e.symm z))
  have hl1 : ∀ z z', l (z + z') = l z + l z' := fun z z' => by
    simp only [l]; rw [hs, hL, he]
  have hlc : Continuous l := e.continuous.comp (hLc.comp e.symm.continuous)
  let lc : (Fin N → ℝ) →L[ℝ] (Fin N → ℝ) := (AddMonoidHom.mk' l hl1).toRealLinearMap hlc
  let β₂ : (Fin N → ℝ) →ₗ[ℝ] (Fin N → ℝ) →ₗ[ℝ] (Fin N → ℝ) := LinearMap.mk₂ ℝ b hb1 hb3 hb2 hb4
  let βc : (Fin N → ℝ) →L[ℝ] (Fin N → ℝ) →L[ℝ] (Fin N → ℝ) :=
    LinearMap.toContinuousLinearMap
      ((LinearMap.toContinuousLinearMap : ((Fin N → ℝ) →ₗ[ℝ] (Fin N → ℝ)) ≃ₗ[ℝ]
        ((Fin N → ℝ) →L[ℝ] (Fin N → ℝ))).toLinearMap ∘ₗ β₂)
  have hF : ∀ z, e (B (e.symm z) (e.symm z) + L (e.symm z)) = βc z z + lc z := fun z => by
    rw [he]; rfl
  have hD' : ∀ u, βc (e x0) u + βc u (e x0) + lc u = (2 : ℝ) • u := fun u => by
    show e (B (e.symm (e x0)) (e.symm u)) + e (B (e.symm u) (e.symm (e x0))) + e (L (e.symm u))
      = (2 : ℝ) • u
    rw [← he, ← he, e.symm_apply_apply, hD, he, e.apply_symm_apply, two_smul]
  have hder : HasStrictFDerivAt (fun z => βc z z + lc z)
      ((2 : ℝ) • ContinuousLinearMap.id ℝ (Fin N → ℝ)) (e x0) := by
    have h1 := (βc.hasStrictFDerivAt_of_bilinear (hasStrictFDerivAt_id (e x0))
      (hasStrictFDerivAt_id (e x0))).add lc.hasStrictFDerivAt
    refine h1.congr_fderiv (ContinuousLinearMap.ext fun u => ?_)
    change _ = (2 : ℝ) • u
    rw [← hD' u]
    rfl
  let f' : (Fin N → ℝ) ≃L[ℝ] (Fin N → ℝ) := ContinuousLinearEquiv.equivOfInverse
    ((2 : ℝ) • ContinuousLinearMap.id ℝ (Fin N → ℝ))
    ((1 / 2 : ℝ) • ContinuousLinearMap.id ℝ (Fin N → ℝ))
    (fun u => by simp [smul_smul]) (fun u => by simp [smul_smul])
  have hf : HasStrictFDerivAt (fun z => e (B (e.symm z) (e.symm z) + L (e.symm z)))
      (f' : (Fin N → ℝ) →L[ℝ] (Fin N → ℝ)) (e x0) := by
    have hfun : (fun z => e (B (e.symm z) (e.symm z) + L (e.symm z))) = fun z => βc z z + lc z :=
      funext hF
    rw [hfun]
    exact hder.congr_fderiv (ContinuousLinearMap.ext fun u => rfl)
  obtain ⟨φ, h1, h2, h3⟩ := local_right_inverse_lemma _ f' (e x0) hf
  simp only [e.symm_apply_apply] at h1 h2 h3
  refine ⟨fun y => e.symm (φ (e y)), ?_, ?_, ?_⟩
  · exact e.symm.continuous.continuousAt.comp (h1.comp e.continuous.continuousAt)
  · simp only [h2, e.symm_apply_apply]
  · exact (e.continuous.continuousAt.tendsto.eventually h3).mono fun y hy => e.injective hy

end PI.AprimeInfW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.ImgLim
section
noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Topology Filter

theorem img_ratio {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]
    {f : E → E} {f' : E → (E →L[ℝ] E)} {U : Set E} {x₀ : E}
    (hf' : ∀ x ∈ U, HasFDerivWithinAt f (f' x) U x) (hinj : Set.InjOn f U)
    (hc : ContinuousAt (fun x => |(f' x).det|) x₀)
    (A : ℕ → Set E) (hAm : ∀ n, MeasurableSet (A n)) (hAU : ∀ n, A n ⊆ U) (hA0 : ∀ n, 0 < μ (A n))
    (hAt : ∀ n, μ (A n) < ⊤) (hsh : ∀ V ∈ 𝓝 x₀, ∀ᶠ n in atTop, A n ⊆ V) :
    Tendsto (fun n => (μ (f '' A n)).toReal / (μ (A n)).toReal) atTop (𝓝 |(f' x₀).det|) := by
  have key : ∀ n, μ (f '' A n) = ∫⁻ x in A n, ENNReal.ofReal |(f' x).det| ∂μ := fun n =>
    (lintegral_abs_det_fderiv_eq_addHaar_image μ (hAm n)
      (fun x hx => (hf' x (hAU n hx)).mono (hAU n)) (hinj.mono (hAU n))).symm
  rw [Metric.tendsto_nhds]
  intro ε hε
  set d := |(f' x₀).det| with hd
  have hV : (fun x => |(f' x).det|) ⁻¹' Set.Ioo (d - ε / 2) (d + ε / 2) ∈ 𝓝 x₀ :=
    hc (Ioo_mem_nhds (by linarith) (by linarith))
  filter_upwards [hsh _ hV] with n hn
  have hm0 := hA0 n
  have hmt := hAt n
  have hmr : 0 < (μ (A n)).toReal := ENNReal.toReal_pos hm0.ne' hmt.ne
  have up : ∫⁻ x in A n, ENNReal.ofReal |(f' x).det| ∂μ ≤ ENNReal.ofReal (d + ε / 2) * μ (A n) := by
    calc _ ≤ ∫⁻ _ in A n, ENNReal.ofReal (d + ε / 2) ∂μ :=
          lintegral_mono_ae ((ae_restrict_iff' (hAm n)).2 (Eventually.of_forall fun x hx =>
            ENNReal.ofReal_le_ofReal (hn hx).2.le))
      _ = _ := setLIntegral_const _ _
  have lo : ENNReal.ofReal (d - ε / 2) * μ (A n) ≤ ∫⁻ x in A n, ENNReal.ofReal |(f' x).det| ∂μ := by
    calc _ = ∫⁻ _ in A n, ENNReal.ofReal (d - ε / 2) ∂μ := (setLIntegral_const _ _).symm
      _ ≤ _ := lintegral_mono_ae ((ae_restrict_iff' (hAm n)).2 (Eventually.of_forall fun x hx =>
            ENNReal.ofReal_le_ofReal (hn hx).1.le))
  have hupt : ENNReal.ofReal (d + ε / 2) * μ (A n) ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hmt.ne
  have hIt : ∫⁻ x in A n, ENNReal.ofReal |(f' x).det| ∂μ ≠ ⊤ := ne_top_of_le_ne_top hupt up
  have u1 : (∫⁻ x in A n, ENNReal.ofReal |(f' x).det| ∂μ).toReal ≤ (d + ε / 2) * (μ (A n)).toReal := by
    have := ENNReal.toReal_mono hupt up
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)] at this
  have l1 : (d - ε / 2) * (μ (A n)).toReal ≤ (∫⁻ x in A n, ENNReal.ofReal |(f' x).det| ∂μ).toReal := by
    have := ENNReal.toReal_mono hIt lo
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal'] at this
    exact le_trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hmr.le) this
  rw [key n, Real.dist_eq, abs_sub_lt_iff]
  constructor
  · rw [sub_lt_iff_lt_add, div_lt_iff₀ hmr]; nlinarith
  · rw [sub_lt_comm, lt_div_iff₀ hmr]; nlinarith

end PI.AprimeInfW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.Imports
section
open Matrix LinearMap Module

noncomputable section

namespace HcS.E

def hdual {S K V : Type*} [CommRing S] [Field K] [StarRing K] [Algebra S K] [AddCommGroup V]
    [Module K V] [Module S V] [IsScalarTower S K V] (B : V →ₗ⋆[K] V →ₗ[K] K)
    (L : Submodule S V) : Submodule S V :=
  ⨅ y ∈ L, (1 : Submodule S K).comap ((B y).restrictScalars S)

end HcS.E
end
end

