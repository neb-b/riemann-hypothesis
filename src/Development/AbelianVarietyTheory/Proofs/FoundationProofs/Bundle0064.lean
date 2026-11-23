module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0037
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0057
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0058
public import Development.AbelianVarietyTheory.Definitions.Foundations.CyclotomicDvdExpandOfCoprime
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0046
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0003

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.EichlerPeriodCocycleMemCocyclesAndEq
section
open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold

namespace GlobalTheory.HeckeFamilyMatrices.PerCoc

theorem polySlash_apply (w : ℕ) (g : Matrix (Fin 2) (Fin 2) ℤ) (p : ℂ[X]) :
    slP w g p = ∑ i ∈ Finset.range (w + 1), p.coeff i •
      ((C ((g 0 0 : ℤ) : ℂ) * X + C ((g 0 1 : ℤ) : ℂ)) ^ i *
        (C ((g 1 0 : ℤ) : ℂ) * X + C ((g 1 1 : ℤ) : ℂ)) ^ (w - i)) := by
  simp only [slP, LinearMap.sum_apply, LinearMap.comp_apply, lcoeff_apply,
    LinearMap.toSpanSingleton_apply]

theorem homogenize_eq_sum (w : ℕ) (p : ℂ[X]) :
    p.homogenize w = ∑ i ∈ Finset.range (w + 1),
      p.coeff i • ((MvPolynomial.X 0 : MvPolynomial (Fin 2) ℂ) ^ i * MvPolynomial.X 1 ^ (w - i)) := by
  rw [homogenize, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i ≤ w := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  rw [← homogenize_monomial hi', ← homogenize_X_pow hi', ← homogenize_smul, smul_X_eq_monomial]

theorem polySlash_eq_aeval (w : ℕ) (g : Matrix (Fin 2) (Fin 2) ℤ) (p : ℂ[X]) :
    slP w g p = MvPolynomial.aeval
      ![C ((g 0 0 : ℤ) : ℂ) * X + C ((g 0 1 : ℤ) : ℂ), C ((g 1 0 : ℤ) : ℂ) * X + C ((g 1 1 : ℤ) : ℂ)]
      (p.homogenize w) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [polySlash_apply, homogenize_eq_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, map_mul, map_pow, map_pow, MvPolynomial.aeval_X, MvPolynomial.aeval_X]
  rfl

theorem isHomogeneous_lin (a b : ℂ) :
    (MvPolynomial.C a * MvPolynomial.X 0 + MvPolynomial.C b * MvPolynomial.X 1 :
      MvPolynomial (Fin 2) ℂ).IsHomogeneous 1 :=
  ((MvPolynomial.isHomogeneous_X ℂ (0 : Fin 2)).C_mul a).add
    ((MvPolynomial.isHomogeneous_X ℂ (1 : Fin 2)).C_mul b)

theorem homogenize_slP (w : ℕ) (g : Matrix (Fin 2) (Fin 2) ℤ) (p : ℂ[X]) :
    (slP w g p).homogenize w = ∑ i ∈ Finset.range (w + 1), MvPolynomial.C (p.coeff i) *
      ((MvPolynomial.C ((g 0 0 : ℤ) : ℂ) * MvPolynomial.X 0 + MvPolynomial.C ((g 0 1 : ℤ) : ℂ) * MvPolynomial.X 1) ^ i *
        (MvPolynomial.C ((g 1 0 : ℤ) : ℂ) * MvPolynomial.X 0 +
          MvPolynomial.C ((g 1 1 : ℤ) : ℂ) * MvPolynomial.X 1) ^ (w - i)) := by
  apply homogenize_eq_of_isHomogeneous
  · refine MvPolynomial.IsHomogeneous.sum _ _ _ fun i hi => ?_
    have hi' : i ≤ w := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have h := (((isHomogeneous_lin ((g 0 0 : ℤ) : ℂ) ((g 0 1 : ℤ) : ℂ)).pow i).mul
      ((isHomogeneous_lin ((g 1 0 : ℤ) : ℂ) ((g 1 1 : ℤ) : ℂ)).pow (w - i))).C_mul (p.coeff i)
    rwa [one_mul, one_mul, Nat.add_sub_of_le hi'] at h
  · set_option synthInstance.maxHeartbeats 100000 in
      rw [polySlash_apply, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [map_mul, map_pow, map_add (f := _), MvPolynomial.aeval_C, MvPolynomial.aeval_X, Matrix.cons_val_zero,
      Matrix.cons_val_one, mul_one, ← C_eq_algebraMap, smul_eq_C_mul]

theorem polySlash_polySlash (w : ℕ) (g h : Matrix (Fin 2) (Fin 2) ℤ) (p : ℂ[X]) :
    slP w h (slP w g p) = slP w (g * h) p := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [polySlash_eq_aeval w h, homogenize_slP, polySlash_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [map_mul, map_pow, map_add (f := _), MvPolynomial.aeval_C, MvPolynomial.aeval_X, Matrix.cons_val_zero,
      Matrix.cons_val_one, ← C_eq_algebraMap, smul_eq_C_mul, Matrix.mul_apply, Fin.sum_univ_two, Int.cast_add,
      Int.cast_mul]
  congr 3 <;> ring

theorem polySlash_mem_degreeLT (w : ℕ) (g : Matrix (Fin 2) (Fin 2) ℤ) (p : ℂ[X]) :
    slP w g p ∈ degreeLT ℂ (w + 1) := by
  rw [polySlash_apply]
  refine Submodule.sum_mem _ fun i hi => Submodule.smul_mem _ _ ?_
  have hi' : i ≤ w := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  rw [mem_degreeLT]
  refine lt_of_le_of_lt degree_le_natDegree ?_
  have h1 : ∀ a b : ℂ, (C a * X + C b).natDegree ≤ 1 := fun a b => natDegree_linear_le
  have h2 := natDegree_mul_le_of_le (natDegree_pow_le_of_le i (h1 ((g 0 0 : ℤ) : ℂ) ((g 0 1 : ℤ) : ℂ)))
    (natDegree_pow_le_of_le (w - i) (h1 ((g 1 0 : ℤ) : ℂ) ((g 1 1 : ℤ) : ℂ)))
  rw [mul_one, mul_one, Nat.add_sub_of_le hi'] at h2
  exact_mod_cast Nat.lt_succ_of_le h2

theorem eichler_I (w : ℕ) (f : ℍ → ℂ) : eichler w f UpperHalfPlane.I = 0 := by
  simp [eichler]

theorem slash_eq_self {Γ : Subgroup SL(2, ℤ)} {k : ℤ} (f : ModularForm Γ k) (γ : Γ) :
    (⇑f) ∣[k] (γ : SL(2, ℤ)) = ⇑f := by
  rw [ModularForm.SL_slash]
  exact f.slash_action_eq' _ ⟨γ, γ.2, rfl⟩

theorem per_eq (Γ : Subgroup SL(2, ℤ)) (k : ℕ) (hk : 2 ≤ k) (f : ModularForm Γ (k : ℤ)) (γ : Γ) (τ : ℍ) :
    per Γ (k - 2) ⇑f γ =
      slP (k - 2) (mat γ) (eichler (k - 2) ⇑f ((γ : SL(2, ℤ)) • τ)) - eichler (k - 2) ⇑f τ := by
  obtain ⟨c, hc⟩ := GlobalTheory.T.eichlerIntegralFromI_slash_change_of_variables k hk ⇑f f.holo' γ
  rw [slash_eq_self] at hc
  rw [per, hc, hc, eichler_I]
  ring

theorem per_mem_Z1_and_eq_slP_eichler_sub : ∀ (Γ : Subgroup SL(2, ℤ)) (k : ℕ), 2 ≤ k → ∀ f : ModularForm Γ (k : ℤ),
    per Γ (k - 2) ⇑f ∈ Z1 Γ (k - 2) ∧ ∀ (γ : Γ) (τ : ℍ), per Γ (k - 2) ⇑f γ =
      slP (k - 2) (mat γ) (eichler (k - 2) ⇑f ((γ : SL(2, ℤ)) • τ)) - eichler (k - 2) ⇑f τ := by
  intro Γ k hk f
  refine ⟨⟨fun γ => polySlash_mem_degreeLT _ _ _, fun γ δ => ?_⟩, per_eq Γ k hk f⟩
  rw [per_eq Γ k hk f γ ((δ : SL(2, ℤ)) • UpperHalfPlane.I), map_sub, polySlash_polySlash]
  simp only [per, mat, Subgroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, mul_smul]
  ring

end GlobalTheory.HeckeFamilyMatrices.PerCoc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.EichlerPeriodPolynomialLimitAtCusp
section
open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold

namespace GlobalTheory.EichlerLimit

theorem trunc_mem (w : ℕ) (R : ℂ[X]) :
    (∑ j ∈ Finset.range (w + 1), C (R.coeff j) * X ^ j) ∈ degreeLT ℂ (w + 1) := by
  refine Submodule.sum_mem _ fun j hj => ?_
  rw [mem_degreeLT]
  refine (degree_C_mul_X_pow_le _ _).trans_lt ?_
  exact_mod_cast Finset.mem_range.1 hj

theorem trunc_coeff (w : ℕ) (R : ℂ[X]) {j : ℕ} (hj : j ≤ w) :
    (∑ i ∈ Finset.range (w + 1), C (R.coeff i) * X ^ i).coeff j = R.coeff j := by
  rw [finsetSum_coeff]
  simp only [coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]
  simp [Finset.mem_range, Nat.lt_succ_of_le hj]

theorem eichler_mem (w : ℕ) (f : ℍ → ℂ) (τ : ℍ) : eichler w f τ ∈ degreeLT ℂ (w + 1) := by
  unfold eichler
  refine Submodule.sum_mem _ fun j hj => ?_
  rw [mem_degreeLT]
  refine (degree_C_mul_X_pow_le _ _).trans_lt ?_
  exact_mod_cast Finset.mem_range.1 hj

theorem bound_rate {F : ℍ → ℂ} {C c c' : ℝ} (hc : c' ≤ c)
    (hF : ∀ τ : ℍ, 1 ≤ τ.im → ‖F τ‖ ≤ C * Real.exp (-c * τ.im)) :
    ∀ τ : ℍ, 1 ≤ τ.im → ‖F τ‖ ≤ max C 0 * Real.exp (-c' * τ.im) := by
  intro τ hτ
  refine (hF τ hτ).trans ?_
  have h1 : Real.exp (-c * τ.im) ≤ Real.exp (-c' * τ.im) :=
    Real.exp_le_exp.2 (by nlinarith [mul_nonneg (sub_nonneg.2 hc) (τ.im_pos.le)])
  calc C * Real.exp (-c * τ.im) ≤ max C 0 * Real.exp (-c * τ.im) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le
    _ ≤ max C 0 * Real.exp (-c' * τ.im) := mul_le_mul_of_nonneg_left h1 (le_max_right _ _)

theorem polySlash_eichler_limit : ∀ (k : ℕ) (f h : ℍ → ℂ) (p : ℂ[X]) (σ : SL(2, ℤ)) (Cf cf Ch ch : ℝ), 2 ≤ k → 0 < cf → 0 < ch → MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f → MDifferentiable 𝓘(ℂ) 𝓘(ℂ) h → MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (f ∣[(k : ℤ)] σ) → MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (h ∣[(k : ℤ)] σ) → (∀ τ : ℍ, 1 ≤ τ.im → ‖(f ∣[(k : ℤ)] σ) τ‖ ≤ Cf * Real.exp (-cf * τ.im)) → (∀ τ : ℍ, 1 ≤ τ.im → ‖(h ∣[(k : ℤ)] σ) τ‖ ≤ Ch * Real.exp (-ch * τ.im)) → p ∈ degreeLT ℂ (k - 1) → ∃ (Q : ℂ[X]) (C' c : ℝ), Q ∈ degreeLT ℂ (k - 2 + 1) ∧ 0 < c ∧ ∀ τ : ℍ, 1 ≤ τ.im → ∀ j ≤ k - 2, ‖(slP (k - 2) (mat σ) (eichler (k - 2) f (σ • τ) - (eichler (k - 2) h (σ • τ)).map (starRingEnd ℂ) - p) - Q).coeff j‖ ≤ C' * Real.exp (-c * τ.im) * (1 + ‖(τ : ℂ)‖) ^ (k - 2) := by
  intro k f h p σ Cf cf Ch ch hk hcf hch hf hh hfs hhs bf bh _hp
  obtain ⟨C1, hC1⟩ := GlobalTheory.T.eichlerIntegralFromI_slash_change_of_variables k hk f hf σ
  obtain ⟨C2, hC2⟩ := GlobalTheory.T.eichlerIntegralFromI_slash_change_of_variables k hk h hh σ
  have hc : 0 < min cf ch := lt_min hcf hch
  obtain ⟨Lf, Kf, hLf⟩ := _root_.GlobalTheory.HeckeFamilyMatrices.eichler_tail (k - 2) (f ∣[(k : ℤ)] σ) (max Cf 0) (min cf ch) hfs hc
    (bound_rate (min_le_left _ _) bf)
  obtain ⟨Lh, Kh, hLh⟩ := _root_.GlobalTheory.HeckeFamilyMatrices.eichler_tail (k - 2) (h ∣[(k : ℤ)] σ) (max Ch 0) (min cf ch) hhs hc
    (bound_rate (min_le_right _ _) bh)
  set R : ℂ[X] := Lf + C1 - (Lh + C2).map (starRingEnd ℂ) - slP (k - 2) (mat σ) p with hR
  refine ⟨∑ j ∈ Finset.range (k - 2 + 1), C (R.coeff j) * X ^ j, Kf + Kh, min cf ch,
    trunc_mem _ _, hc, ?_⟩
  intro τ hτ j hj
  have key : slP (k - 2) (mat σ) (eichler (k - 2) f (σ • τ) - (eichler (k - 2) h (σ • τ)).map (starRingEnd ℂ) - p)
      = eichler (k - 2) (f ∣[(k : ℤ)] σ) τ + C1
        - (eichler (k - 2) (h ∣[(k : ℤ)] σ) τ + C2).map (starRingEnd ℂ) - slP (k - 2) (mat σ) p := by
    rw [map_sub, map_sub, hC1, ← (_root_.GlobalTheory.HeckeFamilyMatrices.SlPAct.polySlash_act (k - 2) (mat σ) 1 _ (eichler_mem _ _ _)).2.2.2, hC2]
  have e1 := hLf τ hτ j hj
  have e2 := hLh τ hτ j hj
  rw [coeff_sub] at e1 e2
  rw [coeff_sub, key, trunc_coeff _ _ hj, hR]
  simp only [coeff_sub, coeff_add, coeff_map, map_add (f := _)]
  calc _ = ‖((eichler (k - 2) (f ∣[(k : ℤ)] σ) τ).coeff j - Lf.coeff j)
        - (starRingEnd ℂ) ((eichler (k - 2) (h ∣[(k : ℤ)] σ) τ).coeff j - Lh.coeff j)‖ := by
          congr 1; rw [map_sub]; ring
    _ ≤ _ := norm_sub_le _ _
    _ = ‖(eichler (k - 2) (f ∣[(k : ℤ)] σ) τ).coeff j - Lf.coeff j‖
        + ‖(eichler (k - 2) (h ∣[(k : ℤ)] σ) τ).coeff j - Lh.coeff j‖ := by rw [Complex.norm_conj]
    _ ≤ _ := by rw [add_mul, add_mul]; exact add_le_add e1 e2

end GlobalTheory.EichlerLimit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.EisensteinPieceUnitSetLevelSuccEq
section
noncomputable section
open Finset
open scoped Classical
open GlobalTheory.KummerEisensteinGalois

namespace GlobalTheory.KummerEisensteinGalois.LevelT

theorem vp_cmul {K : Type} [Field K] [CharZero K] (p : ℕ) (hp : 0 < p) (f g : ℕ → K) (r : ℕ) :
    vp p (cmul f g) r = cmul (vp p f) (vp p g) r := by
  by_cases h : p ∣ r
  · obtain ⟨r', rfl⟩ := h
    rw [UpSplit.cmul_vp_vp p hp]
    simp [vp, Nat.mul_div_cancel_left _ hp]
  · rw [show vp p (cmul f g) r = 0 by simp [vp, h]]
    unfold cmul
    symm
    apply sum_eq_zero
    intro i hi
    have hi' : i ≤ r := Nat.lt_succ_iff.mp (mem_range.mp hi)
    by_cases hpi : p ∣ i
    · have : ¬ p ∣ r - i := by
        intro h2
        apply h
        have := Nat.dvd_add h2 hpi
        rwa [Nat.sub_add_cancel hi'] at this
      simp [vp, this]
    · simp [vp, hpi]

theorem cauchyProduct_fourfold_finsetSum {K : Type} [Field K] {α : Type} (s₁ s₂ s₃ s₄ : Finset α) (f g : α → α → ℕ → K) (r : ℕ) :
    ∑ a ∈ s₁, ∑ b ∈ s₂, ∑ c ∈ s₃, ∑ d ∈ s₄, cmul (f a b) (g c d) r =
      cmul (fun i => ∑ a ∈ s₁, ∑ b ∈ s₂, f a b i) (fun i => ∑ c ∈ s₃, ∑ d ∈ s₄, g c d i) r := by
  unfold cmul
  simp_rw [Finset.sum_comm (s := s₄) (t := range (r + 1))]
  simp_rw [Finset.sum_comm (s := s₃) (t := range (r + 1))]
  simp_rw [Finset.sum_comm (s := s₂) (t := range (r + 1))]
  simp_rw [Finset.sum_comm (s := s₁) (t := range (r + 1))]
  refine sum_congr rfl fun i _ => ?_
  rw [Finset.sum_mul]; refine sum_congr rfl fun a _ => ?_
  rw [Finset.sum_mul]; refine sum_congr rfl fun b _ => ?_
  rw [Finset.mul_sum]; refine sum_congr rfl fun c _ => ?_
  rw [Finset.mul_sum]

theorem dvd_castHom_val_iff {p : ℕ} [Fact p.Prime] {n : ℕ} (hn : 1 ≤ n) (x : ZMod (p ^ (n + 1))) :
    p ∣ (ZMod.castHom (pow_dvd_pow p (Nat.le_succ n)) (ZMod (p ^ n)) x).val ↔ p ∣ x.val := by
  rw [ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.val_natCast,
    Nat.dvd_mod_iff (dvd_pow_self p (by omega))]

theorem sum_preimage_fibre (p : ℕ) [Fact p.Prime] (n : ℕ) (hn : 1 ≤ n) (K : Type) [CommRing K]
    (X : Finset (GL (Fin 2) (ZMod (p ^ n))))
    (hX : ∀ γ ∈ X, ¬ p ∣ ((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ n))) 0 0).val ∧ ¬ p ∣ ((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ n))) 1 0).val)
    (G : GL (Fin 2) (ZMod (p ^ n)) → K)
    (Φ : ZMod (p ^ (n + 1)) → ZMod (p ^ (n + 1)) → ZMod (p ^ (n + 1)) → ZMod (p ^ (n + 1)) → K) :
    ∑ γ ∈ (univ.filter fun γ : GL (Fin 2) (ZMod (p ^ (n + 1))) => Matrix.GeneralLinearGroup.map (ZMod.castHom (pow_dvd_pow p (Nat.le_succ n)) (ZMod (p ^ n))) γ ∈ X),
      G (Matrix.GeneralLinearGroup.map (ZMod.castHom (pow_dvd_pow p (Nat.le_succ n)) (ZMod (p ^ n))) γ) * Φ ((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ (n + 1)))) 0 0) ((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ (n + 1)))) 0 1) ((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ (n + 1)))) 1 0) ((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ (n + 1)))) 1 1) =
    ∑ γ ∈ X, G γ * ∑ y₀₀ ∈ (univ.filter (fun y : ZMod (p ^ (n + 1)) => ZMod.castHom (pow_dvd_pow p (Nat.le_succ n)) (ZMod (p ^ n)) y = (γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ n))) 0 0)), ∑ y₀₁ ∈ (univ.filter (fun y : ZMod (p ^ (n + 1)) => ZMod.castHom (pow_dvd_pow p (Nat.le_succ n)) (ZMod (p ^ n)) y = (γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ n))) 0 1)), ∑ y₁₀ ∈ (univ.filter (fun y : ZMod (p ^ (n + 1)) => ZMod.castHom (pow_dvd_pow p (Nat.le_succ n)) (ZMod (p ^ n)) y = (γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ n))) 1 0)), ∑ y₁₁ ∈ (univ.filter (fun y : ZMod (p ^ (n + 1)) => ZMod.castHom (pow_dvd_pow p (Nat.le_succ n)) (ZMod (p ^ n)) y = (γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ n))) 1 1)), Φ y₀₀ y₀₁ y₁₀ y₁₁ := by
  set ρ := ZMod.castHom (pow_dvd_pow p (Nat.le_succ n)) (ZMod (p ^ n)) with hρ
  have hS : (univ.filter fun γ : GL (Fin 2) (ZMod (p ^ (n + 1))) => Matrix.GeneralLinearGroup.map ρ γ ∈ X) =
      (unitSet p (n + 1)).filter (fun γ => Matrix.GeneralLinearGroup.map ρ γ ∈ X) := by
    ext γ
    simp only [mem_filter, mem_univ, true_and, unitSet]
    constructor
    · intro h
      obtain ⟨h1, h2⟩ := hX _ h
      have e1 : ((Matrix.GeneralLinearGroup.map ρ γ : GL (Fin 2) (ZMod (p ^ n))) : Matrix (Fin 2) (Fin 2) (ZMod (p ^ n))) 0 0 = ρ ((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ (n + 1)))) 0 0) := rfl
      have e2 : ((Matrix.GeneralLinearGroup.map ρ γ : GL (Fin 2) (ZMod (p ^ n))) : Matrix (Fin 2) (Fin 2) (ZMod (p ^ n))) 1 0 = ρ ((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ (n + 1)))) 1 0) := rfl
      rw [e1, hρ, dvd_castHom_val_iff hn] at h1
      rw [e2, hρ, dvd_castHom_val_iff hn] at h2
      exact ⟨⟨h1, h2⟩, h⟩
    · exact fun h => h.2
  have hX' : (unitSet p n).filter (fun γ => γ ∈ X) = X := by
    ext γ
    simp only [mem_filter, unitSet, mem_univ, true_and]
    exact ⟨fun h => h.2, fun h => ⟨hX γ h, h⟩⟩
  rw [hS, Finset.sum_filter]
  have h1 := _root_.GlobalTheory.KummerEisensteinGalois.sum_unitSet_succ_fibre p n K (fun g => if g ∈ X then G g else 0) Φ hn
  simp only [ite_mul, zero_mul] at h1
  rw [h1, ← Finset.sum_filter, hX']

end GlobalTheory.KummerEisensteinGalois.LevelT


open GlobalTheory.KummerEisensteinGalois.LevelT in
theorem GlobalTheory.KummerEisensteinGalois.pieceT_unitSet_level_succ : ∀ (p : ℕ) [Fact p.Prime] (N n m k : ℕ) (K : Type) [Field K] [CharZero K] (ψ : DirichletCharacter K (p ^ m)) (c d : ℤ) (w w' v v' : ℤ × ℤ) (ζ : K) (X : Finset (GL (Fin 2) (ZMod (p ^ n)))), IsPrimitiveRoot ζ (N * p ^ (n + 1)) → 0 < N → ¬ p ∣ N → 1 ≤ m → m ≤ n → 3 ≤ k → ¬ (p : ℤ) ∣ c → ¬ (p : ℤ) ∣ d → (p : ℤ) * v.1 ≡ w.1 [ZMOD N] → (p : ℤ) * v.2 ≡ w.2 [ZMOD N] → (p : ℤ) * v'.1 ≡ w'.1 [ZMOD N] → (p : ℤ) * v'.2 ≡ w'.2 [ZMOD N] → (∀ γ ∈ X, ¬ p ∣ ((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ n))) 0 0).val ∧ ¬ p ∣ ((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ n))) 1 0).val) → ∀ r : ℕ, pieceT N p (n + 1) m k ψ c d v v' ζ (Finset.univ.filter fun γ => Matrix.GeneralLinearGroup.map (ZMod.castHom (pow_dvd_pow p (Nat.le_succ n)) (ZMod (p ^ n))) γ ∈ X) r = vp p (pieceT N p n m k ψ c d w w' (ζ ^ p) X) r := by
  intro p _ N n m k K _ _ ψ c d w w' v v' ζ X hζ hN hpN hm hmn hk hc hd h1 h2 h3 h4 hX r
  have hp0 : 0 < p := (Fact.out : p.Prime).pos
  have hn : 1 ≤ n := le_trans hm hmn
  have hdet : ∀ γ : GL (Fin 2) (ZMod (p ^ (n + 1))),
      ((((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ (n + 1))))).det.val : ℕ) : ZMod (p ^ m)) =
      ((((Matrix.GeneralLinearGroup.map (ZMod.castHom (pow_dvd_pow p (Nat.le_succ n)) (ZMod (p ^ n))) γ : GL (Fin 2) (ZMod (p ^ n))) : Matrix (Fin 2) (Fin 2) (ZMod (p ^ n))).det.val : ℕ) : ZMod (p ^ m)) := by
    intro γ
    have hcast : ∀ {a : ℕ} [NeZero a] (y : ZMod a) (h : p ^ m ∣ a),
        ((y.val : ℕ) : ZMod (p ^ m)) = ZMod.castHom h (ZMod (p ^ m)) y := by
      intro a _ y h
      rw [ZMod.castHom_apply, ZMod.natCast_val]
    have e : ((Matrix.GeneralLinearGroup.map (ZMod.castHom (pow_dvd_pow p (Nat.le_succ n)) (ZMod (p ^ n))) γ : GL (Fin 2) (ZMod (p ^ n))) : Matrix (Fin 2) (Fin 2) (ZMod (p ^ n))) =
        ((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ (n + 1))))).map (ZMod.castHom (pow_dvd_pow p (Nat.le_succ n)) (ZMod (p ^ n))) := rfl
    rw [hcast _ (pow_dvd_pow p (by omega : m ≤ n + 1)), hcast _ (pow_dvd_pow p hmn), e, ← RingHom.mapMatrix_apply, ← RingHom.map_det,
      ← RingHom.comp_apply]
    congr 1
    exact Subsingleton.elim _ _
  have hRHS : vp p (pieceT N p n m k ψ c d w w' (ζ ^ p) X) r =
      -((p : K) ^ ((n : ℤ) * ((k : ℤ) - 4))) * ∑ γ ∈ X,
        ψ ((((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ n)))).det.val : ℕ) : ZMod (p ^ m)) *
        vp p (cmul (smF c (k - 1) (N * p ^ n) (ζ ^ p) (rowT N p n γ 0 w).1 (rowT N p n γ 0 w).2)
           (smF d 1 (N * p ^ n) (ζ ^ p) (rowT N p n γ 1 w').1 (rowT N p n γ 1 w').2)) r := by
    unfold vp pieceT
    split_ifs <;> simp
  rw [hRHS]
  unfold pieceT
  have hsum := sum_preimage_fibre p n hn K X hX (fun γ => ψ ((((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ n)))).det.val : ℕ) : ZMod (p ^ m)))
    (fun y₀₀ y₀₁ y₁₀ y₁₁ => cmul (smF c (k - 1) (N * p ^ (n + 1)) ζ ((N : ℤ) * (y₀₀.val : ℤ) + (p : ℤ) ^ (n + 1) * v.1) ((N : ℤ) * (y₀₁.val : ℤ) + (p : ℤ) ^ (n + 1) * v.2))
      (smF d 1 (N * p ^ (n + 1)) ζ ((N : ℤ) * (y₁₀.val : ℤ) + (p : ℤ) ^ (n + 1) * v'.1) ((N : ℤ) * (y₁₁.val : ℤ) + (p : ℤ) ^ (n + 1) * v'.2)) r)
  have hL : ∑ γ ∈ (Finset.univ.filter fun γ => Matrix.GeneralLinearGroup.map (ZMod.castHom (pow_dvd_pow p (Nat.le_succ n)) (ZMod (p ^ n))) γ ∈ X), ψ ((((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ (n + 1))))).det.val : ℕ) : ZMod (p ^ m)) *
      cmul (smF c (k - 1) (N * p ^ (n + 1)) ζ (rowT N p (n + 1) γ 0 v).1 (rowT N p (n + 1) γ 0 v).2)
           (smF d 1 (N * p ^ (n + 1)) ζ (rowT N p (n + 1) γ 1 v').1 (rowT N p (n + 1) γ 1 v').2) r =
      ∑ γ ∈ (Finset.univ.filter fun γ => Matrix.GeneralLinearGroup.map (ZMod.castHom (pow_dvd_pow p (Nat.le_succ n)) (ZMod (p ^ n))) γ ∈ X), ψ ((((Matrix.GeneralLinearGroup.map (ZMod.castHom (pow_dvd_pow p (Nat.le_succ n)) (ZMod (p ^ n))) γ : GL (Fin 2) (ZMod (p ^ n))) : Matrix (Fin 2) (Fin 2) (ZMod (p ^ n))).det.val : ℕ) : ZMod (p ^ m)) *
      cmul (smF c (k - 1) (N * p ^ (n + 1)) ζ ((N : ℤ) * (((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ (n + 1)))) 0 0).val : ℤ) + (p : ℤ) ^ (n + 1) * v.1) ((N : ℤ) * (((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ (n + 1)))) 0 1).val : ℤ) + (p : ℤ) ^ (n + 1) * v.2))
      (smF d 1 (N * p ^ (n + 1)) ζ ((N : ℤ) * (((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ (n + 1)))) 1 0).val : ℤ) + (p : ℤ) ^ (n + 1) * v'.1) ((N : ℤ) * (((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ (n + 1)))) 1 1).val : ℤ) + (p : ℤ) ^ (n + 1) * v'.2)) r := by
    refine sum_congr rfl fun γ _ => ?_
    rw [hdet]
    rfl
  rw [hL, hsum]
  have hp' : (p : K) ≠ 0 := by exact_mod_cast hp0.ne'
  have hj : 1 ≤ k - 1 := by omega
  have hstep : ∀ γ ∈ X,
      (∑ y₀₀ ∈ (univ.filter (fun y : ZMod (p ^ (n + 1)) => ZMod.castHom (pow_dvd_pow p (Nat.le_succ n)) (ZMod (p ^ n)) y = (γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ n))) 0 0)), ∑ y₀₁ ∈ (univ.filter (fun y : ZMod (p ^ (n + 1)) => ZMod.castHom (pow_dvd_pow p (Nat.le_succ n)) (ZMod (p ^ n)) y = (γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ n))) 0 1)), ∑ y₁₀ ∈ (univ.filter (fun y : ZMod (p ^ (n + 1)) => ZMod.castHom (pow_dvd_pow p (Nat.le_succ n)) (ZMod (p ^ n)) y = (γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ n))) 1 0)), ∑ y₁₁ ∈ (univ.filter (fun y : ZMod (p ^ (n + 1)) => ZMod.castHom (pow_dvd_pow p (Nat.le_succ n)) (ZMod (p ^ n)) y = (γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ n))) 1 1)),
        cmul (smF c (k - 1) (N * p ^ (n + 1)) ζ ((N : ℤ) * (y₀₀.val : ℤ) + (p : ℤ) ^ (n + 1) * v.1) ((N : ℤ) * (y₀₁.val : ℤ) + (p : ℤ) ^ (n + 1) * v.2))
          (smF d 1 (N * p ^ (n + 1)) ζ ((N : ℤ) * (y₁₀.val : ℤ) + (p : ℤ) ^ (n + 1) * v'.1) ((N : ℤ) * (y₁₁.val : ℤ) + (p : ℤ) ^ (n + 1) * v'.2)) r) =
      ((p : K) ^ ((2 : ℤ) - ((k - 1 : ℕ) : ℤ)) * (p : K) ^ ((2 : ℤ) - ((1 : ℕ) : ℤ))) *
        vp p (cmul (smF c (k - 1) (N * p ^ n) (ζ ^ p) (rowT N p n γ 0 w).1 (rowT N p n γ 0 w).2)
           (smF d 1 (N * p ^ n) (ζ ^ p) (rowT N p n γ 1 w').1 (rowT N p n γ 1 w').2)) r := by
    intro γ hγ
    have hu : ¬ p ∣ ((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ n))) 0 0).val ∧ ¬ p ∣ ((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ n))) 1 0).val := by
      exact hX γ hγ
    rw [cauchyProduct_fourfold_finsetSum]
    simp only [_root_.GlobalTheory.KummerEisensteinGalois.RowFibre.smF_sum_lifts p N n (k - 1) K ζ c ((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ n))) 0 0) ((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ n))) 0 1) v.1 v.2 w.1 w.2 hζ hN hpN hn hj hc hu.1 h1 h2,
      _root_.GlobalTheory.KummerEisensteinGalois.RowFibre.smF_sum_lifts p N n 1 K ζ d ((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ n))) 1 0) ((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ n))) 1 1) v'.1 v'.2 w'.1 w'.2 hζ hN hpN hn le_rfl hd hu.2 h3 h4]
    rw [vp_cmul p hp0]
    unfold cmul
    rw [Finset.mul_sum]
    refine sum_congr rfl fun i _ => ?_
    simp only [rowT]
    ring
  rw [Finset.sum_congr rfl (fun γ hγ => by rw [hstep γ hγ])]
  have hsc : -((p : K) ^ (((n + 1 : ℕ) : ℤ) * ((k : ℤ) - 4))) *
      ((p : K) ^ ((2 : ℤ) - ((k - 1 : ℕ) : ℤ)) * (p : K) ^ ((2 : ℤ) - ((1 : ℕ) : ℤ))) =
      -((p : K) ^ ((n : ℤ) * ((k : ℤ) - 4))) := by
    rw [← zpow_add₀ hp', neg_mul, ← zpow_add₀ hp']
    congr 2
    push_cast [Nat.cast_sub (by omega : 1 ≤ k)]
    ring
  rw [← hsc, Finset.mul_sum, Finset.mul_sum]
  refine sum_congr rfl fun γ _ => ?_
  ring
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsColemanLevelRingBasisOneAddXPow
section
noncomputable section
open PowerSeries

namespace GlobalTheory.Col

variable {R : Type} [CommRing R]

theorem cyc_eq_coe_taylor (p m : ℕ) :
    cyc R p m = ((Polynomial.taylor 1 (Polynomial.cyclotomic (p ^ m) R) : Polynomial R) : PowerSeries R) := by
  unfold cyc
  rw [Polynomial.taylor_apply, Polynomial.comp, ← Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.hom_eval₂]
  have h1 : (Polynomial.coeToPowerSeries.ringHom : Polynomial R →+* PowerSeries R).comp Polynomial.C = PowerSeries.C := by
    ext a; simp
  have h2 : (Polynomial.coeToPowerSeries.ringHom : Polynomial R →+* PowerSeries R) (Polynomial.X + Polynomial.C 1) = 1 + PowerSeries.X := by
    simp [add_comm]
  rw [h1, h2]

theorem taylor_cyclotomic_dist (p m : ℕ) [hp : Fact p.Prime] :
    (Polynomial.taylor 1 (Polynomial.cyclotomic (p ^ m) R)).IsDistinguishedAt (Ideal.span {(p : R)}) := by
  have hmap : Polynomial.taylor 1 (Polynomial.cyclotomic (p ^ m) R)
      = (Polynomial.taylor 1 (Polynomial.cyclotomic (p ^ m) ℤ)).map (Int.castRingHom R) := by
    rw [Polynomial.taylor_apply, Polynomial.taylor_apply, Polynomial.map_comp, Polynomial.map_cyclotomic]
    simp
  have hW : (Polynomial.taylor 1 (Polynomial.cyclotomic (p ^ m) ℤ)).IsWeaklyEisensteinAt (Ideal.span {(p : ℤ)}) := by
    rcases m with _ | n
    · refine ⟨fun {k} hk => ?_⟩
      simp only [pow_zero, Polynomial.cyclotomic_one, Polynomial.taylor_apply, Polynomial.sub_comp, Polynomial.X_comp,
        Polynomial.one_comp] at hk ⊢
      have : (Polynomial.X + Polynomial.C (1 : ℤ) - 1) = Polynomial.X := by simp
      rw [this] at hk ⊢
      simp at hk
      subst hk
      simp
    · exact (cyclotomic_prime_pow_comp_X_add_one_isEisensteinAt p n).isWeaklyEisensteinAt
  have hW' := hW.map (Int.castRingHom R)
  rw [Ideal.map_span, Set.image_singleton, map_natCast, ← hmap] at hW'
  refine { toIsWeaklyEisensteinAt := hW', monic := ?_ }
  rw [Polynomial.taylor_apply]
  exact (Polynomial.cyclotomic.monic _ R).comp_X_add_C 1

def levEquiv (p m : ℕ) [hp : Fact p.Prime] [IsAdicComplete (Ideal.span {(p : R)}) R] :
    AdjoinRoot (Polynomial.cyclotomic (p ^ m) R) ≃ₐ[R] lev R p m :=
  (Ideal.quotientEquivAlg (Ideal.span {Polynomial.cyclotomic (p ^ m) R})
      (Ideal.span {Polynomial.taylor 1 (Polynomial.cyclotomic (p ^ m) R)}) (Polynomial.taylorEquiv (1 : R))
      (by rw [Ideal.map_span, Set.image_singleton]; rfl)).trans
    ((taylor_cyclotomic_dist (R := R) p m).algEquivQuotient.trans
      (Ideal.quotientEquivAlgOfEq R (by rw [cyc_eq_coe_taylor])))

theorem levEquiv_root (p m : ℕ) [hp : Fact p.Prime] [IsAdicComplete (Ideal.span {(p : R)}) R] :
    levEquiv p m (AdjoinRoot.root (Polynomial.cyclotomic (p ^ m) R)) = ev R p m (1 + X) := by
  change levEquiv p m (Ideal.Quotient.mk _ Polynomial.X) = _
  have h1 : Ideal.quotientEquivAlg (Ideal.span {Polynomial.cyclotomic (p ^ m) R})
      (Ideal.span {Polynomial.taylor 1 (Polynomial.cyclotomic (p ^ m) R)}) (Polynomial.taylorEquiv (1 : R))
      (by rw [Ideal.map_span, Set.image_singleton]; rfl) (Ideal.Quotient.mk _ Polynomial.X)
      = Ideal.Quotient.mk _ (Polynomial.X + Polynomial.C 1) := by
    rw [Ideal.quotientEquivAlg_mk]
    congr 1
    exact Polynomial.taylor_X 1
  have h : levEquiv p m (Ideal.Quotient.mk (Ideal.span {Polynomial.cyclotomic (p ^ m) R}) Polynomial.X)
      = (Ideal.quotientEquivAlgOfEq R (by rw [cyc_eq_coe_taylor]))
          ((taylor_cyclotomic_dist (R := R) p m).algEquivQuotient
            (Ideal.quotientEquivAlg (Ideal.span {Polynomial.cyclotomic (p ^ m) R})
      (Ideal.span {Polynomial.taylor 1 (Polynomial.cyclotomic (p ^ m) R)}) (Polynomial.taylorEquiv (1 : R))
      (by rw [Ideal.map_span, Set.image_singleton]; rfl) (Ideal.Quotient.mk _ Polynomial.X))) := rfl
  rw [h, h1, Polynomial.IsDistinguishedAt.algEquivQuotient_apply]
  simp only [Ideal.quotient_map_mkₐ, Ideal.Quotient.mkₐ_eq_mk, Ideal.quotientEquivAlgOfEq_mk]
  simp [add_comm]

theorem lev_basis : ∀ (R : Type) [CommRing R] (p m : ℕ) [hp : Fact p.Prime], IsAdicComplete (Ideal.span {(p : R)}) R →
    ∃ b : Module.Basis (Fin (Nat.totient (p ^ m))) R (lev R p m), ∀ i, b i = ev R p m ((1 + X) ^ (i : ℕ)) := by
  intro R _ p m hp hc
  rcases subsingleton_or_nontrivial R with hs | hs
  · haveI : Subsingleton (lev R p m) := Module.subsingleton R _
    exact ⟨Module.Basis.ofRepr (LinearEquiv.ofSubsingleton _ _), fun i => Subsingleton.elim _ _⟩
  let pb := AdjoinRoot.powerBasis' (Polynomial.cyclotomic.monic (p ^ m) R)
  have hd : pb.dim = Nat.totient (p ^ m) := by
    simp [pb, Polynomial.natDegree_cyclotomic]
  refine ⟨(pb.basis.map (levEquiv p m).toLinearEquiv).reindex (finCongr hd), fun i => ?_⟩
  rw [Module.Basis.reindex_apply, Module.Basis.map_apply, PowerBasis.coe_basis]
  simp [pb, levEquiv_root]

end GlobalTheory.Col
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFrobEqMulField
section
open GlobalTheory.Col PowerSeries

namespace GlobalTheory.LangWitt

open Matrix

section Field

variable {p : ℕ} [hp : Fact p.Prime] {k : Type} [Field k] [CharP k p] [IsAlgClosed k]

end Field

section Witt

variable {p : ℕ} [hp : Fact p.Prime] {k : Type} [Field k] [CharP k p]

variable [IsAlgClosed k]

theorem map_add' {R S : Type} [Ring R] [Ring S] (f : R →+* S) {d : ℕ}
    (A B : Matrix (Fin d) (Fin d) R) : (A + B).map f = A.map f + B.map f :=
  map_add f.mapMatrix A B

end Witt

end GlobalTheory.LangWitt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsMulLinearIndependentAlgebraicOverPadicInteStatement
section
open GlobalTheory.K5
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_mul_linearIndependent_algebraicOverPadicIntegers : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
    ∀ y ∈ Submodule.span (O0 p) {x : Ω | IsAlgZp (p := p) x},
    ∃ (n : ℕ) (a : Fin n → Ω) (f : Fin n → O0 p) (g : O0 p), (∀ i, IsAlgZp (p := p) (a i)) ∧
      LinearIndependent (O0 p) a ∧ g ≠ 0 ∧
      algebraMap (O0 p) Ω g * y = ∑ i, algebraMap (O0 p) Ω (f i) * a i := by
  exact @GlobalTheory.K5.algSpan_reprInd
end

