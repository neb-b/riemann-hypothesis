module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1055
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsDominantOfSection
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrthogonalAnisotropicPairPlaneMatricesFacts
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published GlobalTheory.QSA GlobalTheory.PlaneSU
open scoped TensorProduct Quaternion

noncomputable section

namespace GlobalTheory.PlaneSU

open Matrix

section PlaneFacts

variable {F E : Type} [Field F] [Field E] [Algebra F E] {M : ℕ}

theorem planeFacts_hE_conj (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) (J : Matrix (Fin M) (Fin M) E)
    (hJ : ∀ i j, σ (J j i) = J i j) (x y : Fin M → E) : σ (hE σ J x y) = hE σ J y x := by
  unfold hE Formalism.UG.hform
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_mul, AlgHom.coe_toRingHom, hσ, hJ]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem planeFacts_cTJ_apply (σ : E →ₐ[F] E) (J : Matrix (Fin M) (Fin M) E) (e₁ e₂ : Fin M → E)
    (k : Fin 2) (j : Fin M) :
    (Formalism.UG.cT (σ : E →+* E) (planeA e₁ e₂) * J) k j = ∑ i, σ (![e₁, e₂] k i) * J i j := by
  simp [Matrix.mul_apply, Formalism.UG.cT, planeA]

theorem planeFacts_gram_apply (σ : E →ₐ[F] E) (J : Matrix (Fin M) (Fin M) E) (e₁ e₂ : Fin M → E)
    (k l : Fin 2) :
    (Formalism.UG.cT (σ : E →+* E) (planeA e₁ e₂) * J * planeA e₁ e₂) k l = hE σ J (![e₁, e₂] k) (![e₁, e₂] l) := by
  rw [Matrix.mul_apply]
  simp_rw [planeFacts_cTJ_apply]
  simp only [planeA, Matrix.of_apply, hE, Formalism.UG.hform, Finset.sum_mul, AlgHom.coe_toRingHom]
  rw [Finset.sum_comm]

theorem planeFacts_mulVec_apply (σ : E →ₐ[F] E) (J : Matrix (Fin M) (Fin M) E) (e₁ e₂ : Fin M → E)
    (v : Fin M → E) (k : Fin 2) :
    ((Formalism.UG.cT (σ : E →+* E) (planeA e₁ e₂) * J) *ᵥ v) k = hE σ J (![e₁, e₂] k) v := by
  simp only [Matrix.mulVec, dotProduct]
  simp_rw [planeFacts_cTJ_apply]
  simp only [hE, Formalism.UG.hform, Finset.sum_mul, AlgHom.coe_toRingHom]
  rw [Finset.sum_comm]

theorem planeB_facts : ∀ (F E : Type) [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E), (∀ x, σ (σ x) = x) → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ e₁ e₂ : Fin M → E, hE σ J e₁ e₂ = 0 → hE σ J e₁ e₁ ≠ 0 → hE σ J e₂ e₂ ≠ 0 → σ (hE σ J e₁ e₁) = hE σ J e₁ e₁ ∧ σ (hE σ J e₂ e₂) = hE σ J e₂ e₂ ∧ planeB σ J e₁ e₂ * planeA e₁ e₂ = 1 ∧ Formalism.UG.cT (σ : E →+* E) (planeA e₁ e₂) * J = planeH σ J e₁ e₂ * planeB σ J e₁ e₂ ∧ J * planeA e₁ e₂ = Formalism.UG.cT (σ : E →+* E) (planeB σ J e₁ e₂) * planeH σ J e₁ e₂ ∧ ∀ v : Fin M → E, (planeB σ J e₁ e₂).mulVec v = 0 ↔ (hE σ J e₁ v = 0 ∧ hE σ J e₂ v = 0) := by
  intro F E _ _ _ σ hσ M J hJ e₁ e₂ h12 h1 h2
  have hc := planeFacts_hE_conj σ hσ J hJ.1
  have h21 : hE σ J e₂ e₁ = 0 := by rw [← hc, h12, map_zero]
  have s1 : σ (hE σ J e₁ e₁) = hE σ J e₁ e₁ := hc _ _
  have s2 : σ (hE σ J e₂ e₂) = hE σ J e₂ e₂ := hc _ _
  set a₁ := hE σ J e₁ e₁ with ha₁
  set a₂ := hE σ J e₂ e₂ with ha₂
  set A := planeA e₁ e₂ with hA
  have gram : Formalism.UG.cT (σ : E →+* E) A * J * A = planeH σ J e₁ e₂ := by
    ext k l
    rw [planeFacts_gram_apply]
    fin_cases k <;> fin_cases l <;> simp [planeH, h12, h21, ha₁, ha₂]
  have dd : Matrix.diagonal ![a₁⁻¹, a₂⁻¹] * Matrix.diagonal ![a₁, a₂] = 1 := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1; ext k; fin_cases k <;> simp [h1, h2]
  have dd' : Matrix.diagonal ![a₁, a₂] * Matrix.diagonal ![a₁⁻¹, a₂⁻¹] = 1 := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1; ext k; fin_cases k <;> simp [h1, h2]
  have cTJ : Formalism.UG.cT (σ : E →+* E) J = J := by
    ext i j; simp [Formalism.UG.cT, hJ.1]
  have cTcT : Formalism.UG.cT (σ : E →+* E) (Formalism.UG.cT (σ : E →+* E) A) = A := by
    ext i j; simp [Formalism.UG.cT, hσ]
  have cTd : Formalism.UG.cT (σ : E →+* E) (Matrix.diagonal ![a₁⁻¹, a₂⁻¹]) = Matrix.diagonal ![a₁⁻¹, a₂⁻¹] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Formalism.UG.cT, map_inv₀, s1, s2]
  refine ⟨s1, s2, ?_, ?_, ?_, ?_⟩
  · unfold planeB
    rw [← ha₁, ← ha₂, ← hA]
    have gram' : Formalism.UG.cT (σ : E →+* E) A * (J * A) = planeH σ J e₁ e₂ := by rw [← Matrix.mul_assoc, gram]
    simp only [Matrix.mul_assoc]
    rw [gram']
    unfold planeH
    rw [← ha₁, ← ha₂, dd]
  · unfold planeB planeH
    rw [← ha₁, ← ha₂, ← hA, ← Matrix.mul_assoc, ← Matrix.mul_assoc, dd', Matrix.one_mul]
  · unfold planeB planeH
    rw [← ha₁, ← ha₂, ← hA, Formalism.UG.cT_mul, Formalism.UG.cT_mul, cTJ, cTcT, cTd, Matrix.mul_assoc, Matrix.mul_assoc A, dd, Matrix.mul_one]
  · intro v
    have hv : ∀ k, (planeB σ J e₁ e₂ *ᵥ v) k = ![a₁⁻¹, a₂⁻¹] k * hE σ J (![e₁, e₂] k) v := by
      intro k
      unfold planeB
      rw [Matrix.mul_assoc, ← Matrix.mulVec_mulVec, Matrix.mulVec_diagonal, planeFacts_mulVec_apply]
    constructor
    · intro h
      have k0 := hv 0
      have k1 := hv 1
      rw [h] at k0 k1
      simp only [Pi.zero_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at k0 k1
      exact ⟨(mul_eq_zero.mp k0.symm).resolve_left (inv_ne_zero h1),
        (mul_eq_zero.mp k1.symm).resolve_left (inv_ne_zero h2)⟩
    · rintro ⟨z1, z2⟩
      funext k
      rw [hv]
      fin_cases k <;> simp [z1, z2]

end PlaneFacts

end GlobalTheory.PlaneSU
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ParabolicMatrixFamilyDiagIsUnit
section
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical

set_option autoImplicit false

namespace GlobalTheory.FlagPush

theorem mul_diag_of_par {ι : Type} {m : ι → ℕ} {K : Type} [Field K] {O O' : Subring K} {S T : Mat m K}
    (hS : Par m O S) (hT : Par m O' T) (τ : ι) (i : Fin (m τ)) :
    (S * T) τ i i = S τ i i * T τ i i := by
  rw [Pi.mul_apply, Matrix.mul_apply]
  refine Finset.sum_eq_single i (fun l _ hl => ?_) (fun h => absurd (Finset.mem_univ i) h)
  rcases lt_or_gt_of_ne hl with h | h
  · rw [(hT τ).2.2.2 l i l.isLt h, mul_zero]
  · rw [(hS τ).2.2.2 i l i.isLt h, zero_mul]

theorem diag_of_par : ∀ (ι : Type) (m : ι → ℕ) (K : Type) [Field K] (O : Subring K) (S : Mat m K), Par m O S →
    ∀ x : Root m, S x.1 x.2 x.2 ≠ 0 ∧ (S x.1 x.2 x.2)⁻¹ ∈ O ∧ S⁻¹ x.1 x.2 x.2 = (S x.1 x.2 x.2)⁻¹ ∧
      ∀ T : Mat m K, Par m ⊤ T → (S * T) x.1 x.2 x.2 = S x.1 x.2 x.2 * T x.1 x.2 x.2 := by
  intro ι m K _ O S hS x
  have hSi : Par m O S⁻¹ := hS.inv
  have h1 : S x.1 x.2 x.2 * S⁻¹ x.1 x.2 x.2 = 1 := by
    rw [← mul_diag_of_par hS hSi, Mat.mul_inv hS.det_ne]
    exact Matrix.one_apply_eq _
  have hne : S x.1 x.2 x.2 ≠ 0 := left_ne_zero_of_mul_eq_one h1
  have hinv : S⁻¹ x.1 x.2 x.2 = (S x.1 x.2 x.2)⁻¹ := eq_inv_of_mul_eq_one_right h1
  refine ⟨hne, ?_, hinv, fun T hT => mul_diag_of_par hS hT x.1 x.2⟩
  rw [← hinv]
  exact (hSi x.1).1 x.2 x.2

end GlobalTheory.FlagPush
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PiolaIdentityWirtingerAntiholomorphic
section
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

noncomputable section

namespace GlobalTheory.GoodTop.Piola

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
  [IsScalarTower ℝ ℂ E]

theorem hasFDerivAt_dbar_apply {f : E → ℂ} {z : E} (hf : ContDiffAt ℝ 2 f z) (u : E) :
    HasFDerivAt (fun x => dbar f x u)
      ((1 / 2 : ℂ) • ((ContinuousLinearMap.apply ℝ ℂ u).comp (fderiv ℝ (fderiv ℝ f) z) +
        Complex.I • (ContinuousLinearMap.apply ℝ ℂ (Complex.I • u)).comp (fderiv ℝ (fderiv ℝ f) z))) z := by
  have hD : DifferentiableAt ℝ (fderiv ℝ f) z :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have h : ∀ a : E, HasFDerivAt (fun x => fderiv ℝ f x a)
      ((ContinuousLinearMap.apply ℝ ℂ a).comp (fderiv ℝ (fderiv ℝ f) z)) z :=
    fun a => (ContinuousLinearMap.apply ℝ ℂ a).hasFDerivAt.comp z hD.hasFDerivAt
  exact ((h u).add ((h (Complex.I • u)).const_smul Complex.I)).const_smul (1 / 2 : ℂ)

theorem dbar_dbar_symm {f : E → ℂ} {z : E} (hf : ContDiffAt ℝ 2 f z) (v w : E) :
    dbar (fun x => dbar f x w) z v = dbar (fun x => dbar f x v) z w := by
  have hs : IsSymmSndFDerivAt ℝ f z := hf.isSymmSndFDerivAt (by simp)
  rw [dbar_eq_of_hasFDerivAt (hasFDerivAt_dbar_apply hf w),
    dbar_eq_of_hasFDerivAt (hasFDerivAt_dbar_apply hf v)]
  simp only [antilinPart_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.coe_comp', Function.comp_apply, ContinuousLinearMap.apply_apply]
  rw [hs v w, hs v (Complex.I • w), hs (Complex.I • v) w, hs (Complex.I • v) (Complex.I • w)]
  ring_nf

theorem dbar_finset_prod {ι : Type*} [DecidableEq ι] (s : Finset ι) {g : ι → E → ℂ} {z : E}
    (hg : ∀ i ∈ s, DifferentiableAt ℝ (g i) z) (u : E) :
    dbar (fun x => ∏ i ∈ s, g i x) z u = ∑ k ∈ s, dbar (g k) z u * ∏ i ∈ s.erase k, g i z := by
  have h := HasFDerivAt.finsetProd (fun i hi => (hg i hi).hasFDerivAt)
  rw [dbar_eq_of_hasFDerivAt h]
  simp only [antilinPart_apply, dbar_apply, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun k _ => by ring

end GlobalTheory.GoodTop.Piola

namespace GlobalTheory.GoodTop

theorem piola_dbar {n : ℕ} (f : Fin n → V n → ℂ) (j : Fin n) (v : V n)
    (hf : ∀ i, i ≠ j → ContDiffAt ℝ 2 (f i) v) :
    ∑ w : Equiv.Perm (Fin n), ((Equiv.Perm.sign w : ℤ) : ℂ) *
      dbar (fun x => ∏ i ∈ Finset.univ.erase j, dbar (f i) x (coordVec (w i))) v (coordVec (w j)) = 0 := by
  have e : ∀ w : Equiv.Perm (Fin n),
      dbar (fun x => ∏ i ∈ Finset.univ.erase j, dbar (f i) x (coordVec (w i))) v (coordVec (w j)) =
      ∑ k ∈ Finset.univ.erase j, dbar (fun x => dbar (f k) x (coordVec (w k))) v (coordVec (w j)) *
        ∏ i ∈ (Finset.univ.erase j).erase k, dbar (f i) v (coordVec (w i)) := fun w =>
    Piola.dbar_finset_prod (g := fun i x => dbar (f i) x (coordVec (w i))) _
      (fun i hi => (Piola.hasFDerivAt_dbar_apply (hf i (Finset.ne_of_mem_erase hi)) _).differentiableAt) _
  simp only [e, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun k hk => ?_
  have hkj : k ≠ j := Finset.ne_of_mem_erase hk
  set T : Equiv.Perm (Fin n) → ℂ := fun w => ((Equiv.Perm.sign w : ℤ) : ℂ) *
    (dbar (fun x => dbar (f k) x (coordVec (w k))) v (coordVec (w j)) *
        ∏ i ∈ (Finset.univ.erase j).erase k, dbar (f i) v (coordVec (w i))) with hT
  have h1 : ∀ w, T (w * Equiv.swap j k) = -T w := by
    intro w
    have hp : ∏ i ∈ (Finset.univ.erase j).erase k, dbar (f i) v (coordVec ((w * Equiv.swap j k) i)) =
        ∏ i ∈ (Finset.univ.erase j).erase k, dbar (f i) v (coordVec (w i)) := by
      refine Finset.prod_congr rfl fun i hi => ?_
      rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne
        (Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hi)) (Finset.ne_of_mem_erase hi)]
    simp only [hT]
    rw [hp, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, Equiv.swap_apply_left, Equiv.swap_apply_right,
      Piola.dbar_dbar_symm (hf k hkj) (coordVec (w k)) (coordVec (w j)), Equiv.Perm.sign_mul,
      Equiv.Perm.sign_swap hkj.symm]
    simp
  have h2 : ∑ w, T w = -∑ w, T w := by
    rw [← Finset.sum_neg_distrib, ← Equiv.sum_comp (Equiv.mulRight (Equiv.swap j k)) T]
    exact Finset.sum_congr rfl fun w _ => h1 w
  show ∑ w, T w = 0
  linear_combination (1 / 2 : ℂ) * h2

end GlobalTheory.GoodTop
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PoincareCoordinateLengthMemIccAndPos
section
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

namespace GlobalTheory.GoodTop

theorem poinWt_mem_Icc_and_pos : ∀ {n : ℕ} (S : Finset (Fin n)) (v : V n), (∀ a ∈ S, ‖v a‖ ≤ 1 / 2) →
    (∀ a, 0 ≤ poinWt S v a ∧ poinWt S v a ≤ 1) ∧ ((∀ a ∈ S, v a ≠ 0) → ∀ a, 0 < poinWt S v a) := by
  intro n S v hS
  refine ⟨fun a => ?_, fun hne a => ?_⟩
  · unfold poinWt
    split_ifs with ha
    · refine ⟨mul_nonneg (norm_nonneg _) (abs_nonneg _), ?_⟩
      rcases (norm_nonneg (v a)).eq_or_lt with h0 | hpos
      · rw [← h0]; simp
      · have h1 : ‖v a‖ ≤ 1 := (hS a ha).trans (by norm_num)
        have := Real.abs_log_mul_self_lt _ hpos h1
        rw [abs_mul, abs_of_pos hpos] at this
        linarith
    · exact ⟨zero_le_one, le_rfl⟩
  · unfold poinWt
    split_ifs with ha
    · have hpos : 0 < ‖v a‖ := norm_pos_iff.mpr (hne a ha)
      have hlt : ‖v a‖ < 1 := (hS a ha).trans_lt (by norm_num)
      have hlog : Real.log ‖v a‖ < 0 := Real.log_neg hpos hlt
      exact mul_pos hpos (abs_pos.mpr hlog.ne)
    · exact zero_lt_one

end GlobalTheory.GoodTop
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarisedTopChernCoeffConj
section
set_option autoImplicit false

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

namespace GlobalTheory.GoodTop

theorem sum_prod_perm_mul_comm {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] (A : Fin n → Matrix r r ℂ)
    (P : Matrix r r ℂ) (π : Equiv.Perm (Fin n)) :
    ∑ p : Fin n → r, ∏ i, (A i * P) (p i) (p (π i)) = ∑ p : Fin n → r, ∏ i, (P * A i) (p i) (p (π i)) := by
  simp only [Matrix.mul_apply]
  have h1 : ∀ f : Fin n → r → ℂ, ∏ i, ∑ j, f i j = ∑ s : Fin n → r, ∏ i, f i (s i) := fun f => by
    rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  simp only [h1]
  rw [Finset.sum_comm]
  symm
  refine Fintype.sum_equiv (Equiv.arrowCongr π.symm (Equiv.refl r)) _ _ fun t => ?_
  refine Finset.sum_congr rfl fun p _ => ?_
  simp only [Finset.prod_mul_distrib, Equiv.arrowCongr_apply, Equiv.symm_symm, Equiv.coe_refl, Function.comp, id]
  rw [mul_comm, Equiv.prod_comp π fun i => P (t i) (p i)]

theorem mixTop_conj {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] (K : Fin n → EndValuedForm11Coeffs n r) (P : Matrix r r ℂ)
    (hP : IsUnit P.det) : mixTop (fun i a b => P⁻¹ * K i a b * P) = mixTop K := by
  unfold mixTop
  congr 1
  have hdet : ∀ M : Fin n → Fin n → ℂ, (Matrix.of M).det =
      ∑ w : Equiv.Perm (Fin n), ((Equiv.Perm.sign w : ℤ) : ℂ) * ∏ i, M i (w i) := fun M => by
    rw [← Matrix.det_transpose, Matrix.det_apply']
    simp
  simp only [hdet, Finset.mul_sum]
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun π _ => ?_
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun w _ => ?_
  simp only [← Finset.mul_sum]
  congr 2
  rw [sum_prod_perm_mul_comm (fun i => P⁻¹ * K i (u i) (w i)) P π]
  simp only [← Matrix.mul_assoc, Matrix.mul_nonsing_inv P hP, Matrix.one_mul]

end GlobalTheory.GoodTop
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarisedTopChernCoeffLinearSubstitution
section
set_option autoImplicit false

noncomputable section

open scoped Matrix

namespace GlobalTheory.GoodTop

namespace MixSubst

variable {n : ℕ}

theorem det_rows_sum (x : Fin n → Fin n → ℂ) (k : Fin n → Fin n → Fin n → ℂ) :
    (Matrix.of fun i d => ∑ c, x i c * k i c d).det =
      ∑ c : Fin n → Fin n, (∏ i, x i (c i)) * (Matrix.of fun i d => k i (c i) d).det := by
  have h : (Matrix.of fun i d => ∑ c, x i c * k i c d) = fun i => ∑ c, x i c • k i c := by
    ext i j
    simp
  rw [h]
  change (Matrix.detRowAlternating : AlternatingMap ℂ (Fin n → ℂ) ℂ (Fin n)) _ = _
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← AlternatingMap.coe_multilinearMap, MultilinearMap.map_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [MultilinearMap.map_smul_univ, smul_eq_mul]
  rfl

theorem sum_sign_prod (J : Matrix (Fin n) (Fin n) ℂ) (c : Fin n → Fin n) :
    ∑ u : Equiv.Perm (Fin n), ((Equiv.Perm.sign u : ℤ) : ℂ) * ∏ i, J (c i) (u i) = (J.submatrix c id).det := by
  rw [← Matrix.det_transpose, Matrix.det_apply']
  rfl

theorem alt_sum (J : Matrix (Fin n) (Fin n) ℂ) (k : Fin n → Fin n → Fin n → ℂ) :
    ∑ u : Equiv.Perm (Fin n), ((Equiv.Perm.sign u : ℤ) : ℂ) *
        (Matrix.of fun i d => ∑ c, J c (u i) * k i c d).det =
      J.det * ∑ u : Equiv.Perm (Fin n), ((Equiv.Perm.sign u : ℤ) : ℂ) * (Matrix.of fun i d => k i (u i) d).det := by
  have h1 : ∀ u : Equiv.Perm (Fin n), (Matrix.of fun i d => ∑ c, J c (u i) * k i c d).det =
      ∑ c : Fin n → Fin n, (∏ i, J (c i) (u i)) * (Matrix.of fun i d => k i (c i) d).det :=
    fun u => det_rows_sum (fun i c => J c (u i)) k
  simp_rw [h1, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [← mul_assoc, ← Finset.sum_mul, sum_sign_prod]
  symm
  refine Fintype.sum_of_injective (fun σ : Equiv.Perm (Fin n) => (σ : Fin n → Fin n)) DFunLike.coe_injective _ _
    (fun c hc => ?_) (fun σ => ?_)
  · have hinj : ¬ Function.Injective c := fun h =>
      hc ⟨Equiv.ofBijective c (Finite.injective_iff_bijective.mp h), rfl⟩
    obtain ⟨i, j, hij, hne⟩ : ∃ i j, c i = c j ∧ i ≠ j := by
      simp only [Function.Injective, not_forall] at hinj
      obtain ⟨i, j, h, h'⟩ := hinj
      exact ⟨i, j, h, h'⟩
    rw [Matrix.det_zero_of_row_eq hne (by ext l; simp [hij]), zero_mul]
  · rw [Matrix.det_permute, mul_comm J.det]

theorem alt_sum_two (J J' : Matrix (Fin n) (Fin n) ℂ) (k : Fin n → Fin n → Fin n → ℂ) :
    ∑ u : Equiv.Perm (Fin n), ((Equiv.Perm.sign u : ℤ) : ℂ) *
        (Matrix.of fun i b => ∑ c, ∑ d, J c (u i) * J' d b * k i c d).det =
      J.det * J'.det *
        ∑ u : Equiv.Perm (Fin n), ((Equiv.Perm.sign u : ℤ) : ℂ) * (Matrix.of fun i d => k i (u i) d).det := by
  have h1 : ∀ u : Equiv.Perm (Fin n), (Matrix.of fun i b => ∑ c, ∑ d, J c (u i) * J' d b * k i c d) =
      (Matrix.of fun i d => ∑ c, J c (u i) * k i c d) * J' := by
    intro u
    ext i b
    simp only [Matrix.of_apply, Matrix.mul_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  simp_rw [h1, Matrix.det_mul, ← mul_assoc, ← Finset.sum_mul]
  rw [alt_sum]
  ring

end MixSubst

theorem mixTop_subst {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] (K : Fin n → EndValuedForm11Coeffs n r)
    (J J' : Matrix (Fin n) (Fin n) ℂ) :
    mixTop (fun i a b => ∑ c, ∑ d, (J c a * J' d b) • K i c d) = J.det * J'.det * mixTop K := by
  unfold mixTop
  rw [mul_left_comm]
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun π _ => ?_
  simp_rw [mul_assoc ((Equiv.Perm.sign π : ℤ) : ℂ), ← Finset.mul_sum]
  rw [mul_left_comm, ← MixSubst.alt_sum_two J J' (fun i c d => K i c d (p i) (p (π i)))]
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]

end GlobalTheory.GoodTop
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarisedTopChernCoeffUpdateAdd
section
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

set_option autoImplicit false

namespace GlobalTheory.GoodTop

theorem mixTop_update_add : ∀ {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] (K : Fin n → EndValuedForm11Coeffs n r) (j : Fin n) (L L' : EndValuedForm11Coeffs n r), mixTop (Function.update K j (L + L')) = mixTop (Function.update K j L) + mixTop (Function.update K j L') := by
  intro n r _ _ K j L L'
  have key : ∀ (M : EndValuedForm11Coeffs n r) (p : Fin n → r) (π u : Equiv.Perm (Fin n)),
      (Matrix.of fun i b => Function.update K j M i (u i) b (p i) (p (π i))) =
        (Matrix.of fun i b => K i (u i) b (p i) (p (π i))).updateRow j
          (fun b => M (u j) b (p j) (p (π j))) := by
    intro M p π u
    ext i b
    by_cases h : i = j
    · subst h
      simp
    · simp [Matrix.updateRow_ne h, Function.update_of_ne h]
  unfold mixTop
  rw [← mul_add]
  congr 1
  simp only [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun π _ => Finset.sum_congr rfl fun u _ => ?_
  rw [key, key, key, ← mul_add, ← Matrix.det_updateRow_add]
  rfl

end GlobalTheory.GoodTop
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarisedTopChernCoeffUpdateSmul
section
set_option autoImplicit false

open GlobalTheory.GoodTop

namespace GlobalTheory.GoodTop

theorem mixTop_update_smul {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] (K : Fin n → EndValuedForm11Coeffs n r) (j : Fin n)
    (t : ℂ) (L : EndValuedForm11Coeffs n r) :
    mixTop (Function.update K j (t • L)) = t * mixTop (Function.update K j L) := by
  have key : ∀ (M : EndValuedForm11Coeffs n r) (p : Fin n → r) (π u : Equiv.Perm (Fin n)),
      (Matrix.of fun i b => Function.update K j M i (u i) b (p i) (p (π i))) =
        (Matrix.of fun i b => K i (u i) b (p i) (p (π i))).updateRow j
          (fun b => M (u j) b (p j) (p (π j))) := by
    intro M p π u
    ext i b
    by_cases h : i = j
    · subst h; simp
    · simp [Matrix.updateRow_ne h, Function.update_of_ne h]
  have h2 : ∀ (p : Fin n → r) (π u : Equiv.Perm (Fin n)),
      (Matrix.of fun i b => Function.update K j (t • L) i (u i) b (p i) (p (π i))).det =
        t * (Matrix.of fun i b => Function.update K j L i (u i) b (p i) (p (π i))).det := by
    intro p π u
    rw [key, key, ← Matrix.det_updateRow_smul]
    rfl
  unfold mixTop
  simp only [h2, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun π _ => Finset.sum_congr rfl fun u _ => ?_
  ring

end GlobalTheory.GoodTop
end

