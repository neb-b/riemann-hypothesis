module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusStrictLowerComparisonNearIdentity
section
open scoped Matrix Matrix.Norms.Frobenius

namespace GlobalTheory

theorem frobCmp_normSq {r : ℕ} (A : Matrix (Fin r) (Fin r) ℂ) :
    ‖A‖ ^ 2 = ∑ i, ∑ j, ‖A i j‖ ^ 2 := by
  rw [Matrix.frobenius_norm_def]
  simp_rw [Real.rpow_two]
  rw [← Real.sqrt_eq_rpow, Real.sq_sqrt (by positivity)]

theorem frobCmp_le {r : ℕ} (A B : Matrix (Fin r) (Fin r) ℂ)
    (h : ∀ i j, ‖A i j‖ ≤ ‖B i j‖) : ‖A‖ ≤ ‖B‖ := by
  have hsq : ‖A‖ ^ 2 ≤ ‖B‖ ^ 2 := by
    rw [frobCmp_normSq, frobCmp_normSq]
    gcongr with i _ j _
    exact h i j
  nlinarith [norm_nonneg A, norm_nonneg B]

theorem frobCmp_le_const {r : ℕ} (A : Matrix (Fin r) (Fin r) ℂ) (ε : ℝ) (hε : 0 ≤ ε)
    (h : ∀ i j, ‖A i j‖ ≤ ε) : ‖A‖ ≤ r * ε := by
  have hsq : ‖A‖ ^ 2 ≤ ((r : ℝ) * ε) ^ 2 := by
    rw [frobCmp_normSq]
    calc ∑ i, ∑ j, ‖A i j‖ ^ 2 ≤ ∑ _i : Fin r, ∑ _j : Fin r, ε ^ 2 := by
          gcongr with i _ j _
          exact h i j
      _ = ((r : ℝ) * ε) ^ 2 := by
          simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
  have : 0 ≤ (r : ℝ) * ε := by positivity
  nlinarith [norm_nonneg A]

theorem frobenius_lower_comparison : ∀ (r : ℕ) (g n b B W H : Matrix (Fin r) (Fin r) ℂ) (δ : ℝ), 0 ≤ δ → (r : ℝ) * δ ≤ 1 / 100 → (∀ a c : Fin r, a < c → n a c = 0) → (∀ a : Fin r, n a a = 1) → (∀ a c : Fin r, c < a → ‖n a c‖ ≤ δ) → (∀ a c : Fin r, c < a → b a c = 0) → (∀ a : Fin r, |‖b a a‖ ^ 2 - 1| ≤ 6 * δ) → (∀ a c : Fin r, a < c → ‖b a c‖ ≤ 6 * δ) → (∀ a c : Fin r, c < a → B a c = 0) → (∀ a c : Fin r, a ≤ c → W a c = 0) → (∀ a c : Fin r, a ≤ c → H a c = 0) → g * n = b → g * W = H * b + B → ∑ a, ∑ c, ‖W a c‖ ^ 2 ≤ 2 * ∑ a, ∑ c, ‖H a c‖ ^ 2 := by
  intro r g n b B W H δ hδ hrδ hn_up hn_diag hn_low hb_low hb_diag hb_up hB hW hH hgn hgW
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · simp
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hδ1 : δ ≤ 1 / 100 := by nlinarith

  have hnT : n.BlockTriangular OrderDual.toDual := fun i j hij => hn_up i j (by simpa using hij)
  have hdet : n.det = 1 := by
    rw [Matrix.det_of_lowerTriangular n hnT]; simp [hn_diag]
  have hu : IsUnit n.det := by rw [hdet]; exact isUnit_one
  letI := n.invertibleOfIsUnitDet hu
  have hinvT : n⁻¹.BlockTriangular OrderDual.toDual :=
    Matrix.blockTriangular_inv_of_blockTriangular hnT
  obtain ⟨Y, hY⟩ : ∃ Y, Y = n⁻¹ * W := ⟨_, rfl⟩
  have hYlow : ∀ a c, a ≤ c → Y a c = 0 := by
    intro a c hac
    rw [hY, Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro k _
    by_cases hk : a < k
    · rw [hinvT (by simpa using hk), zero_mul]
    · rw [hW k c (le_trans (not_lt.mp hk) hac), mul_zero]
  have hWnY : W = n * Y := by
    rw [hY, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.one_mul]
  have hg : g = b * n⁻¹ := by
    rw [← hgn, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.mul_one]
  have hbY : b * Y = H * b + B := by rw [← hgW, hg, hY, Matrix.mul_assoc]

  obtain ⟨D, hD⟩ : ∃ D : Matrix (Fin r) (Fin r) ℂ, D = Matrix.diagonal (fun a => b a a) :=
    ⟨_, rfl⟩
  obtain ⟨u, hu'⟩ : ∃ u, u = b - D := ⟨_, rfl⟩
  have hbDu : b = D + u := by rw [hu']; abel
  have hdlow : ∀ a, (0.969 : ℝ) ≤ ‖b a a‖ := by
    intro a
    have h1 := (abs_le.mp (hb_diag a)).1
    nlinarith [norm_nonneg (b a a)]
  have hdup : ∀ a, ‖b a a‖ ≤ (1.03 : ℝ) := by
    intro a
    have h1 := (abs_le.mp (hb_diag a)).2
    nlinarith [norm_nonneg (b a a)]
  have hunorm : ‖u‖ ≤ 6 / 100 := by
    have h := frobCmp_le_const u (6 * δ) (by positivity) (by
      intro a c
      rw [hu', Matrix.sub_apply, hD]
      rcases lt_trichotomy a c with hac | rfl | hac
      · rw [Matrix.diagonal_apply_ne _ (ne_of_lt hac), sub_zero]; exact hb_up a c hac
      · simp; positivity
      · rw [Matrix.diagonal_apply_ne _ (ne_of_gt hac), sub_zero, hb_low a c hac, norm_zero]
        positivity)
    nlinarith
  have hn1 : ‖n - 1‖ ≤ 1 / 100 := by
    have h := frobCmp_le_const (n - 1) δ hδ (by
      intro a c
      rw [Matrix.sub_apply]
      rcases lt_trichotomy a c with hac | rfl | hac
      · rw [hn_up a c hac, Matrix.one_apply_ne (ne_of_lt hac), sub_zero, norm_zero]; exact hδ
      · rw [hn_diag, Matrix.one_apply_eq, sub_self, norm_zero]; exact hδ
      · rw [Matrix.one_apply_ne (ne_of_gt hac), sub_zero]; exact hn_low a c hac)
    linarith

  have hM : D * Y = H * D + H * u - u * Y + B := by
    have e1 : D * Y = b * Y - u * Y := by rw [hbDu, Matrix.add_mul]; abel
    rw [e1, hbY, hbDu, Matrix.mul_add]; abel
  have hkey : ‖D * Y‖ ≤ ‖H * D + H * u - u * Y‖ := by
    apply frobCmp_le
    intro a c
    by_cases hca : c < a
    · rw [hM, Matrix.add_apply, hB a c hca, add_zero]
    · rw [hD, Matrix.diagonal_mul, hYlow a c (not_lt.mp hca), mul_zero, norm_zero]
      exact norm_nonneg _
  have hDY : (0.969 : ℝ) * ‖Y‖ ≤ ‖D * Y‖ := by
    have h : ‖(0.969 : ℝ) • Y‖ ≤ ‖D * Y‖ := by
      apply frobCmp_le
      intro a c
      rw [Matrix.smul_apply, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num),
        hD, Matrix.diagonal_mul, norm_mul]
      exact mul_le_mul_of_nonneg_right (hdlow a) (norm_nonneg _)
    rwa [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num)] at h
  have hHD : ‖H * D‖ ≤ (1.03 : ℝ) * ‖H‖ := by
    have h : ‖H * D‖ ≤ ‖(1.03 : ℝ) • H‖ := by
      apply frobCmp_le
      intro a c
      rw [Matrix.smul_apply, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num),
        hD, Matrix.mul_diagonal, norm_mul, mul_comm]
      exact mul_le_mul_of_nonneg_right (hdup c) (norm_nonneg _)
    rwa [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num)] at h
  have hHu : ‖H * u‖ ≤ ‖H‖ * ‖u‖ := Matrix.frobenius_norm_mul H u
  have huY : ‖u * Y‖ ≤ ‖u‖ * ‖Y‖ := Matrix.frobenius_norm_mul u Y
  have htri : ‖H * D + H * u - u * Y‖ ≤ ‖H * D‖ + ‖H * u‖ + ‖u * Y‖ :=
    (norm_sub_le _ _).trans (by gcongr; exact norm_add_le _ _)
  have hHn := norm_nonneg H
  have hYn := norm_nonneg Y
  have hun := norm_nonneg u
  have hY12 : ‖Y‖ ≤ 1.2 * ‖H‖ := by nlinarith
  have hWY : ‖W‖ ≤ (1.01 : ℝ) * ‖Y‖ := by
    have e : W = Y + (n - 1) * Y := by rw [hWnY, Matrix.sub_mul, Matrix.one_mul]; abel
    have h1 : ‖W‖ ≤ ‖Y‖ + ‖n - 1‖ * ‖Y‖ := by
      rw [e]; exact (norm_add_le _ _).trans (by gcongr; exact Matrix.frobenius_norm_mul _ _)
    nlinarith [norm_nonneg (n - 1)]
  have hWn := norm_nonneg W
  rw [← frobCmp_normSq, ← frobCmp_normSq]
  nlinarith

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusSubalgebraCounitalComul
section
open scoped TensorProduct

namespace GlobalTheory

theorem frobSubalgebra_counit : ∀ (p : ℕ) [Fact p.Prime] (k A : Type) [Field k] [CommRing A] [Algebra k A] [CharP k p] [PerfectRing k p] (ε : A →ₐ[k] k) (Δ : A →ₐ[k] A ⊗[k] A), ((∀ a : A, TensorProduct.lid k A (LinearMap.rTensor A ε.toLinearMap (Δ a)) = a) ∧ (∀ a : A, TensorProduct.rid k A (LinearMap.lTensor A ε.toLinearMap (Δ a)) = a)) → ∃ B : Subalgebra k A, (∀ a, a ∈ B ↔ ∃ c : A, c ^ p = a) ∧ ∃ Δ' : B →ₐ[k] B ⊗[k] B, ((∀ a : B, TensorProduct.lid k B (LinearMap.rTensor B (ε.comp B.val).toLinearMap (Δ' a)) = a) ∧ (∀ a : B, TensorProduct.rid k B (LinearMap.lTensor B (ε.comp B.val).toLinearMap (Δ' a)) = a)) := by
  intro p _ k A _ _ _ _ _ ε Δ ⟨hl, hr⟩
  have injA : Function.Injective (algebraMap k A) := fun x y h => by
    simpa using congrArg ε h
  haveI : CharP A p := charP_of_injective_algebraMap injA p
  let εε : A ⊗[k] A →ₐ[k] k := Algebra.TensorProduct.lift ε ε (fun _ _ => Commute.all _ _)
  have injAA : Function.Injective (algebraMap k (A ⊗[k] A)) := fun x y h => by
    simpa only [AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply] using congrArg εε h
  haveI : CharP (A ⊗[k] A) p := charP_of_injective_algebraMap injAA p
  let B : Subalgebra k A :=
    { carrier := {a | ∃ c : A, c ^ p = a}
      mul_mem' := by rintro _ _ ⟨c, rfl⟩ ⟨d, rfl⟩; exact ⟨c * d, mul_pow c d p⟩
      add_mem' := by rintro _ _ ⟨c, rfl⟩ ⟨d, rfl⟩; exact ⟨c + d, add_pow_char c d p⟩
      algebraMap_mem' := by
        intro r
        obtain ⟨s, hs⟩ := surjective_frobenius k p r
        exact ⟨algebraMap k A s, by rw [← map_pow, ← hs, frobenius_def]⟩ }
  refine ⟨B, fun a => Iff.rfl, ?_⟩
  let j : B ⊗[k] B →ₐ[k] A ⊗[k] A := Algebra.TensorProduct.map B.val B.val
  have hj : Function.Injective j :=
    TensorProduct.map_injective_of_flat_flat B.val.toLinearMap B.val.toLinearMap
      Subtype.val_injective Subtype.val_injective
  have hpow : ∀ t : A ⊗[k] A, t ^ p ∈ j.range := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp [zero_pow (Fact.out : p.Prime).ne_zero]⟩
    | tmul a b =>
      exact ⟨(⟨a ^ p, a, rfl⟩ : B) ⊗ₜ (⟨b ^ p, b, rfl⟩ : B), by
        simp [j, Algebra.TensorProduct.tmul_pow]⟩
    | add x y hx hy => rw [add_pow_char]; exact add_mem hx hy
  have hΔ : ∀ b : B, Δ (B.val b) ∈ j.range := by
    rintro ⟨_, c, rfl⟩
    simpa [map_pow] using hpow (Δ c)
  let e := AlgEquiv.ofInjective j hj
  let Δ' : B →ₐ[k] B ⊗[k] B := e.symm.toAlgHom.comp ((Δ.comp B.val).codRestrict j.range hΔ)
  have hjΔ : ∀ b : B, j (Δ' b) = Δ (B.val b) := by
    intro b
    have h1 := e.apply_symm_apply ⟨Δ (B.val b), hΔ b⟩
    exact congrArg Subtype.val h1
  have kl : ∀ x : B ⊗[k] B, ((TensorProduct.lid k B (LinearMap.rTensor B (ε.comp B.val).toLinearMap x) : B) : A)
      = TensorProduct.lid k A (LinearMap.rTensor A ε.toLinearMap (j x)) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [j]
    | add x y hx hy => simp only [map_add (f := _), Subalgebra.coe_add, hx, hy]
  have kr : ∀ x : B ⊗[k] B, ((TensorProduct.rid k B (LinearMap.lTensor B (ε.comp B.val).toLinearMap x) : B) : A)
      = TensorProduct.rid k A (LinearMap.lTensor A ε.toLinearMap (j x)) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [j]
    | add x y hx hy => simp only [map_add (f := _), Subalgebra.coe_add, hx, hy]
  refine ⟨Δ', fun b => ?_, fun b => ?_⟩
  · apply Subtype.ext
    rw [kl, hjΔ]; exact hl _
  · apply Subtype.ext
    rw [kr, hjΔ]; exact hr _

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FundamentalDomainIntegralMulRight
section
open MeasureTheory

namespace GlobalTheory

theorem fundamentalDomain_integral_mul_right {G : Type} [Group G] [MeasurableSpace G]
    [MeasurableMul G] (μ : Measure G) [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant]
    (Γ : Subgroup G) [Countable Γ] (𝓕 : Set G) (f : G → ℂ) (a : G)
    (h : IsFundamentalDomain Γ 𝓕 μ) (hf : ∀ γ ∈ Γ, ∀ g, f (γ * g) = f g) :
    (IntegrableOn f 𝓕 μ ↔ IntegrableOn (fun g => f (g * a)) 𝓕 μ) ∧
      ∫ g in 𝓕, f (g * a) ∂μ = ∫ g in 𝓕, f g ∂μ := by
  have hmp : MeasurePreserving (fun g : G => g * a) μ μ := measurePreserving_mul_right μ a
  have hme : MeasurableEmbedding (fun g : G => g * a) := measurableEmbedding_mulRight a
  have h' : IsFundamentalDomain Γ ((fun g : G => g * a) ⁻¹' 𝓕) μ :=
    h.preimage_of_equiv (e := id) hmp.quasiMeasurePreserving Function.bijective_id
      (fun γ x => by simp [Subgroup.smul_def, mul_assoc])
  have hfa : ∀ (γ : Γ) (x : G), (fun g => f (g * a)) (γ • x) = (fun g => f (g * a)) x := by
    intro γ x
    simp only [Subgroup.smul_def, smul_eq_mul, mul_assoc]
    exact hf γ γ.2 _
  refine ⟨?_, ?_⟩
  · rw [h.integrableOn_iff h' (f := fun g => f (g * a)) hfa]
    exact (hmp.integrableOn_comp_preimage hme (f := f) (s := 𝓕)).symm
  · rw [h.setIntegral_eq h' (f := fun g => f (g * a)) hfa]
    exact hmp.setIntegral_preimage_emb hme f 𝓕

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FundamentalSequenceContinuityAll
section
open TensorProduct Polynomial

namespace GlobalTheory

theorem torsion_of_one_tmul_eq_zero (D K M : Type) [CommRing D] [IsDomain D] [Field K]
    [Algebra D K] [FaithfulSMul D K] [AddCommGroup M] [Module D M] (m : M)
    (h : (1 : K) ⊗ₜ[D] m = 0) : ∃ d : D, d ≠ 0 ∧ d • m = 0 := by
  letI : Algebra (FractionRing D) K := FractionRing.liftAlgebra D K
  haveI : IsScalarTower D (FractionRing D) K := FractionRing.isScalarTower_liftAlgebra D K
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap (FractionRing D) K)
    (by rw [LinearMap.ker_eq_bot]; exact (algebraMap (FractionRing D) K).injective)
  have hg1 : g 1 = 1 := by
    have := LinearMap.congr_fun hg 1
    simpa using this
  have h2 : (1 : FractionRing D) ⊗ₜ[D] m = 0 := by
    have := congrArg ((g.restrictScalars D).rTensor M) h
    simpa [hg1] using this
  obtain ⟨⟨d, hd⟩, hdm⟩ := (IsLocalizedModule.eq_zero_iff (nonZeroDivisors D)
    (TensorProduct.mk D (FractionRing D) M 1)).1 h2
  exact ⟨d, nonZeroDivisors.ne_zero hd, hdm⟩

theorem exists_not_mem_ker_smul_mem_map_of_one_tmul_eq_zero (A B K : Type) [CommRing A] [CommRing B]
    [Algebra A B] [Field K] [Algebra A K] (b : B) (h : (1 : K) ⊗ₜ[A] b = 0) :
    ∃ f : A, f ∉ RingHom.ker (algebraMap A K) ∧
      f • b ∈ (RingHom.ker (algebraMap A K)).map (algebraMap A B) := by
  set P := RingHom.ker (algebraMap A K) with hP
  haveI : P.IsPrime := RingHom.ker_isPrime _
  letI : Algebra (A ⧸ P) K := (RingHom.kerLift (algebraMap A K)).toAlgebra
  haveI : IsScalarTower A (A ⧸ P) K := IsScalarTower.of_algebraMap_eq' (by ext a; rfl)
  haveI : FaithfulSMul (A ⧸ P) K :=
    (faithfulSMul_iff_algebraMap_injective (A ⧸ P) K).2 (RingHom.kerLift_injective _)
  let I := P.map (algebraMap A B)
  let q : B →ₗ[A] B ⧸ I := (Ideal.Quotient.mkₐ A I).toLinearMap
  let Φ : K ⊗[A] B →ₗ[A] K ⊗[A ⧸ P] (B ⧸ I) :=
    (TensorProduct.mapOfCompatibleSMul (A ⧸ P) A A K (B ⧸ I)) ∘ₗ q.lTensor K
  have h1 : (1 : K) ⊗ₜ[A ⧸ P] (Ideal.Quotient.mk I b) = 0 := by
    have hΦ : Φ ((1 : K) ⊗ₜ[A] b) = (1 : K) ⊗ₜ[A ⧸ P] (Ideal.Quotient.mk I b) := rfl
    rw [← hΦ, h, map_zero]
  obtain ⟨d, hd0, hdb⟩ := torsion_of_one_tmul_eq_zero (A ⧸ P) K (B ⧸ I) _ h1
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective d
  refine ⟨f, fun hf => hd0 (Ideal.Quotient.eq_zero_iff_mem.2 hf), ?_⟩
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  have : Ideal.Quotient.mk I (f • b) = (Ideal.Quotient.mk P f) • Ideal.Quotient.mk I b := by
    rw [Algebra.smul_def, map_mul, Algebra.smul_def]
    rfl
  rw [this, hdb]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisOfFiniteGeneratingAutomorphisms
section
namespace GlobalTheory

theorem galois_of_finite_generating_automorphisms : ∀ (K K' : Type) [Field K] [Field K'] (i : K →+* K'), i.Finite → ∀ (Γ : Type) [Finite Γ] (s : Γ → (K' ≃+* K')), (∀ g x, s g (i x) = i x) → (∀ y : K', (∀ g, s g y = y) → y ∈ i.range) → (letI := i.toAlgebra; IsGalois K K') ∧ ∀ σ : K' ≃+* K', (∀ x, σ (i x) = i x) → σ ∈ Submonoid.closure (Set.range s) := by
  intro K K' _ _ i hfin Γ _ s hs hfix
  letI := i.toAlgebra
  haveI : FiniteDimensional K K' := hfin
  let t : Γ → (K' ≃ₐ[K] K') := fun g => AlgEquiv.ofRingEquiv (f := s g) (hs g)
  let H : Subgroup (K' ≃ₐ[K] K') := Subgroup.closure (Set.range t)
  have hH : IntermediateField.fixedField H = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    have h1 : ∀ g, s g y = y := fun g => hy ⟨t g, Subgroup.subset_closure ⟨g, rfl⟩⟩
    obtain ⟨x, rfl⟩ := hfix y h1
    exact IntermediateField.algebraMap_mem _ x
  have hG : IsGalois K K' := by
    apply IsGalois.of_fixedField_eq_bot
    rw [eq_bot_iff, ← hH]
    exact IntermediateField.fixedField_le le_top
  refine ⟨hG, ?_⟩
  intro σ hσ
  have hHtop : H = ⊤ := by
    rw [← IntermediateField.fixingSubgroup_fixedField H, hH, IntermediateField.fixingSubgroup_bot]
  let σ' : K' ≃ₐ[K] K' := AlgEquiv.ofRingEquiv (f := σ) hσ
  have hmem : σ' ∈ Submonoid.closure (Set.range t) := by
    rw [← Subgroup.closure_toSubmonoid_of_finite]
    show σ' ∈ H
    rw [hHtop]; exact Subgroup.mem_top _
  let φ : (K' ≃ₐ[K] K') →* (K' ≃+* K') :=
    { toFun := fun τ => τ.toRingEquiv
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hmap := Submonoid.mem_map_of_mem φ hmem
  rw [MonoidHom.map_mclosure, ← Set.range_comp] at hmap
  have hc : (φ ∘ t) = s := by
    funext g; ext y; rfl
  have hσ' : φ σ' = σ := by ext y; rfl
  rwa [hc, hσ'] at hmap

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GammaRealFunctionalEquationConstantEvenInteger
section
namespace GlobalTheory

theorem gammaℝ_functional_constant_even :
    ∀ (d : ℝ), 0 < d → ∀ (f s : ℕ), 1 ≤ s → ∀ A B : ℂ,
      (d : ℂ) ^ (((2 * s : ℕ) : ℂ) / 2) * Complex.Gammaℝ ((2 * s : ℕ) : ℂ) ^ f * A =
        (d : ℂ) ^ ((1 - ((2 * s : ℕ) : ℂ)) / 2) * Complex.Gammaℝ (1 - ((2 * s : ℕ) : ℂ)) ^ f * B →
      (((2 * s - 1).factorial : ℕ) : ℂ) ^ f * ((d ^ (((2 * s : ℕ) : ℝ) - 1 / 2) : ℝ) : ℂ) *
        ((2 * (Real.pi : ℂ) * Complex.I) ^ (2 * s * f))⁻¹ * A = (2 : ℂ)⁻¹ ^ f * B := by
  intro d hd f s hs A B hAB
  set k : ℂ := ((2 * s : ℕ) : ℂ) with hk
  have hk' : k = 2 * (s : ℂ) := by rw [hk]; push_cast; ring
  have hh : Complex.Gammaℝ (1 - k) ≠ 0 := by
    rw [Ne, Complex.Gammaℝ_eq_zero_iff]
    rintro ⟨n, hn⟩
    have h1 : ((1 : ℤ) : ℂ) = ((2 * s - 2 * n : ℤ) : ℂ) := by
      push_cast; rw [hk'] at hn; linear_combination hn
    have h2 := Int.cast_injective h1
    omega
  have hodd : ∀ n : ℕ, k ≠ -(2 * n + 1) := by
    intro n hn
    have h1 : ((2 * s : ℤ) : ℂ) = ((-(2 * n + 1) : ℤ) : ℂ) := by
      push_cast; rw [← hk']; exact hn
    have h2 := Int.cast_injective h1
    omega
  have hratio := Complex.Gammaℝ_div_Gammaℝ_one_sub hodd
  have hΓ : Complex.Gamma k = (((2 * s - 1).factorial : ℕ) : ℂ) := by
    have : k = ((2 * s - 1 : ℕ) : ℂ) + 1 := by
      rw [hk]; norm_cast; omega
    rw [this, Complex.Gamma_nat_eq_factorial]
  have hcos : Complex.cos ((Real.pi : ℂ) * k / 2) = (-1) ^ s := by
    rw [hk', show (Real.pi : ℂ) * (2 * s) / 2 = (s : ℂ) * Real.pi by ring]
    rw [show (s : ℂ) * Real.pi = (((s : ℝ) * Real.pi : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_cos, Real.cos_nat_mul_pi]
    push_cast; ring
  have hpow : (2 * (Real.pi : ℂ)) ^ (-k) = ((2 * (Real.pi : ℂ)) ^ (2 * s))⁻¹ := by
    rw [Complex.cpow_neg, hk, Complex.cpow_natCast]
  have hg : Complex.Gammaℝ k = Complex.Gammaℝ (1 - k) *
      (2 * ((2 * (Real.pi : ℂ)) ^ (2 * s))⁻¹ * (((2 * s - 1).factorial : ℕ) : ℂ) * (-1) ^ s) := by
    rw [div_eq_iff hh, Complex.Gammaℂ_def, hΓ, hcos, hpow] at hratio
    rw [hratio]; ring
  have hd0 : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  have hE : ((d ^ (((2 * s : ℕ) : ℝ) - 1 / 2) : ℝ) : ℂ) = (d : ℂ) ^ (k - 1 / 2) := by
    rw [Complex.ofReal_cpow hd.le]; congr 1; rw [hk]; push_cast; ring
  have hD : (d : ℂ) ^ (k / 2) = (d : ℂ) ^ ((1 - k) / 2) * (d : ℂ) ^ (k - 1 / 2) := by
    rw [← Complex.cpow_add _ _ hd0]; congr 1; ring
  have hD2 : (d : ℂ) ^ ((1 - k) / 2) ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff]; tauto
  have hB : B = (d : ℂ) ^ (k - 1 / 2) *
      (2 * ((2 * (Real.pi : ℂ)) ^ (2 * s))⁻¹ * (((2 * s - 1).factorial : ℕ) : ℂ) * (-1) ^ s) ^ f * A := by
    rw [hD, hg, mul_pow] at hAB
    have hne : (d : ℂ) ^ ((1 - k) / 2) * Complex.Gammaℝ (1 - k) ^ f ≠ 0 :=
      mul_ne_zero hD2 (pow_ne_zero _ hh)
    apply mul_left_cancel₀ hne
    rw [← hAB]; ring
  rw [hE, hB]
  have hI : (2 * (Real.pi : ℂ) * Complex.I) ^ (2 * s * f) =
      ((2 * (Real.pi : ℂ)) ^ (2 * s)) ^ f * ((-1 : ℂ) ^ s) ^ f := by
    rw [pow_mul, ← mul_pow, mul_pow (2 * (Real.pi : ℂ)) Complex.I, pow_mul Complex.I 2 s, Complex.I_sq]
  have hm : (((-1 : ℂ) ^ s) ^ f)⁻¹ = ((-1 : ℂ) ^ s) ^ f := by
    rw [← inv_pow, ← inv_pow, inv_neg_one]
  rw [hI, mul_inv, hm, ← inv_pow]
  have h2 : (2 : ℂ)⁻¹ ^ f * (2 : ℂ) ^ f = 1 := by
    rw [← mul_pow, inv_mul_cancel₀ two_ne_zero, one_pow]
  linear_combination (-((((2 * s - 1).factorial : ℕ) : ℂ) ^ f * (d : ℂ) ^ (k - 1 / 2) *
    (((2 * (Real.pi : ℂ)) ^ (2 * s))⁻¹) ^ f * ((-1 : ℂ) ^ s) ^ f * A)) * h2

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlAdicCompletionEntriesBoundedOfIsCompact
section
open NumberField IsDedekindDomain Filter

noncomputable section

namespace GlobalTheory.BCT.SuppFin

variable {E : Type} [Field E] [NumberField E]

theorem isOpen_vle (w : HeightOneSpectrum (𝓞 E)) (m : ℤ) :
    IsOpen {y : w.adicCompletion E | Valued.v y ≤ WithZero.exp m} := by
  obtain ⟨c, hc⟩ := HeightOneSpectrum.valuedAdicCompletion_surjective E w (WithZero.exp m)
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [map_zero] at hc
    exact WithZero.exp_ne_zero hc.symm
  have : {y : w.adicCompletion E | Valued.v y ≤ WithZero.exp m} =
      {y | Valued.v.restrict y ≤ Valued.v.restrict c} := by
    ext y
    simp only [Set.mem_ofPred_eq, Valuation.restrict_le_iff, hc]
  rw [this]
  exact Valued.isOpen_closedBall _ (by simp [hc0])

theorem exists_bound_of_isCompact (w : HeightOneSpectrum (𝓞 E)) {K : Set (w.adicCompletion E)}
    (hK : IsCompact K) : ∃ N : ℤ, ∀ z ∈ K, Valued.v z ≤ WithZero.exp N := by
  have hcov : K ⊆ ⋃ N : ℤ, {y : w.adicCompletion E | Valued.v y ≤ WithZero.exp N} := by
    intro z _
    rw [Set.mem_iUnion]
    by_cases hz : Valued.v z = 0
    · exact ⟨0, by simp [hz]⟩
    · exact ⟨WithZero.log (Valued.v z), by simp [WithZero.exp_log hz]⟩
  obtain ⟨N, hN⟩ := hK.elim_directed_cover _ (fun N => isOpen_vle w N) hcov
    (Monotone.directed_le fun a b hab y hy => le_trans hy (WithZero.exp_le_exp.2 hab))
  exact ⟨N, fun z hz => hN hz⟩

theorem gl_entries_bounded_of_isCompact : ∀ (E : Type) [Field E] [NumberField E]
    (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) (D : Set (GL (Fin n) (w.adicCompletion E))),
    IsCompact D → ∃ N : ℤ, ∀ h ∈ D, ∀ i j,
      Valued.v (h.val i j) ≤ WithZero.exp N ∧ Valued.v ((h⁻¹).val i j) ≤ WithZero.exp N := by
  intro E _ _ w n D hD
  have h1 : ∀ i j, ∃ N : ℤ, ∀ h ∈ D, Valued.v (h.val i j) ≤ WithZero.exp N := by
    intro i j
    obtain ⟨N, hN⟩ := exists_bound_of_isCompact w
      (hD.image (Units.continuous_val.matrix_elem i j))
    exact ⟨N, fun h hh => hN _ ⟨h, hh, rfl⟩⟩
  have h2 : ∀ i j, ∃ N : ℤ, ∀ h ∈ D, Valued.v ((h⁻¹).val i j) ≤ WithZero.exp N := by
    intro i j
    obtain ⟨N, hN⟩ := exists_bound_of_isCompact w
      (hD.image ((Units.continuous_coe_inv).matrix_elem i j))
    exact ⟨N, fun h hh => hN _ ⟨h, hh, rfl⟩⟩
  choose N1 hN1 using h1
  choose N2 hN2 using h2
  refine ⟨((Finset.univ.sup (fun p : Fin n × Fin n => (N1 p.1 p.2).toNat) : ℕ) : ℤ) ⊔
      ((Finset.univ.sup (fun p : Fin n × Fin n => (N2 p.1 p.2).toNat) : ℕ) : ℤ), ?_⟩
  intro h hh i j
  have a1 : N1 i j ≤ ((Finset.univ.sup (fun p : Fin n × Fin n => (N1 p.1 p.2).toNat) : ℕ) : ℤ) :=
    (Int.self_le_toNat _).trans (Int.ofNat_le.2
      (Finset.le_sup (f := fun p : Fin n × Fin n => (N1 p.1 p.2).toNat) (Finset.mem_univ (i, j))))
  have a2 : N2 i j ≤ ((Finset.univ.sup (fun p : Fin n × Fin n => (N2 p.1 p.2).toNat) : ℕ) : ℤ) :=
    (Int.self_le_toNat _).trans (Int.ofNat_le.2
      (Finset.le_sup (f := fun p : Fin n × Fin n => (N2 p.1 p.2).toNat) (Finset.mem_univ (i, j))))
  exact ⟨(hN1 i j h hh).trans (WithZero.exp_le_exp.2 (a1.trans le_sup_left)),
    (hN2 i j h hh).trans (WithZero.exp_le_exp.2 (a2.trans le_sup_right))⟩

end GlobalTheory.BCT.SuppFin
end
end

