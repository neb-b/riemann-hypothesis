module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0019
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfM
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.FirstMinimumInvariantContinuousPosOnFrames
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1311
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0712
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0213
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1288
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMemChart
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0242
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0197
public import Development.AbelianVarietyTheory.Definitions.Divisors.LineBundleGlobalSectionsDimCongrPicardClass
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0043
public import ReciprocityTheory.SemistableReduction.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1300
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1303
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1259
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1275
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1282
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1310
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0040
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0904
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1290
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0922
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1217
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1304
public import Development.AbelianVarietyTheory.Definitions.Divisors.CompEqOneIffPush

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DbarDerivCutoffNormSqBoundAnnulus
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory
open Complex ComplexConjugate

theorem wdb_normSq_div {n : ℕ} (ρ : ℝ) (j : Fin n) (z : V n) :
    wdb n j (fun w : V n => (((‖w‖ ^ 2 / ρ ^ 2 : ℝ)) : ℂ)) z = z j / (ρ ^ 2 : ℝ) := by
  have h1 := ((hasStrictFDerivAt_norm_sq z).hasFDerivAt).const_smul ((ρ ^ 2)⁻¹ : ℝ)
  have e : (fun w : V n => ‖w‖ ^ 2 / ρ ^ 2) = fun w => ((ρ ^ 2)⁻¹ : ℝ) • ‖w‖ ^ 2 := by
    funext w; simp [smul_eq_mul, div_eq_inv_mul]
  have hv : HasFDerivAt (fun w : V n => ‖w‖ ^ 2 / ρ ^ 2) (((ρ ^ 2)⁻¹ : ℝ) • (2 • innerSL ℝ z)) z := by
    rw [e]; exact h1
  unfold wdb
  rw [fderiv_ofReal_apply hv.differentiableAt, fderiv_ofReal_apply hv.differentiableAt, hv.fderiv]
  simp only [bas, ContinuousLinearMap.smul_apply, innerSL_apply_apply, smul_eq_mul, nsmul_eq_mul]
  have hr : ∀ x y : V n, inner ℝ x y = re (inner ℂ x y) := by
    intro x y
    rw [PiLp.inner_apply, PiLp.inner_apply, Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [mul_comm]
  rw [hr, hr, inner_smul_right,
    EuclideanSpace.inner_single_right]
  rw [div_eq_mul_inv (z j), ← Complex.ofReal_inv]
  generalize (ρ ^ 2)⁻¹ = r
  apply Complex.ext <;> simp <;> ring

theorem wdb_cutoff_sq_le : ∀ (χ : ℝ → ℝ) (A : ℝ), ContDiff ℝ ∞ χ → (∀ t, 0 ≤ χ t ∧ χ t ≤ 1) → (∀ t, t ≤ 1 / 4 → χ t = 1) → (∀ t, 1 ≤ t → χ t = 0) → (∀ t, |deriv χ t| ≤ A) → ∀ (n : ℕ) (ρ : ℝ), 0 < ρ → ∀ (z : V n) (ξ : Fin n → ℂ), ‖∑ j, wdb n j (fun w => ((χ (‖w‖ ^ 2 / ρ ^ 2) : ℝ) : ℂ)) z * (starRingEnd ℂ) (ξ j)‖ ^ 2 ≤ if ρ / 2 ≤ ‖z‖ ∧ ‖z‖ < ρ then A ^ 2 / ρ ^ 2 * ∑ j, ‖ξ j‖ ^ 2 else 0 := by
  intro χ A hχ h01 h1 h0 hA n ρ hρ z ξ
  have hdχ : Differentiable ℝ χ := hχ.differentiable (by simp)
  have hv : DifferentiableAt ℝ (fun w : V n => ‖w‖ ^ 2 / ρ ^ 2) z :=
    by
    have := (differentiableAt_id (x := z)).norm_sq ℝ
    simpa [div_eq_mul_inv] using this.mul_const ((ρ ^ 2)⁻¹)
  set t := ‖z‖ ^ 2 / ρ ^ 2 with ht
  have hw : ∀ j, wdb n j (fun w => ((χ (‖w‖ ^ 2 / ρ ^ 2) : ℝ) : ℂ)) z =
      ((deriv χ t : ℝ) : ℂ) * (z j / ((ρ ^ 2 : ℝ) : ℂ)) := by
    intro j
    rw [wdb_ofReal_comp (k := χ) (v := fun w : V n => ‖w‖ ^ 2 / ρ ^ 2) (hdχ _) hv,
      wdb_normSq_div]
  simp_rw [hw]
  have hsum : ∑ j, ((deriv χ t : ℝ) : ℂ) * (z j / ((ρ ^ 2 : ℝ) : ℂ)) * (starRingEnd ℂ) (ξ j) =
      ((deriv χ t : ℝ) : ℂ) / ((ρ ^ 2 : ℝ) : ℂ) * ∑ j, z j * (starRingEnd ℂ) (ξ j) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [hsum]
  split_ifs with hann
  · have hCS : ‖∑ j, z j * (starRingEnd ℂ) (ξ j)‖ ^ 2 ≤ ‖z‖ ^ 2 * ∑ j, ‖ξ j‖ ^ 2 := by
      calc ‖∑ j, z j * (starRingEnd ℂ) (ξ j)‖ ^ 2 ≤ (∑ j, ‖z j‖ * ‖ξ j‖) ^ 2 := by
            apply pow_le_pow_left₀ (norm_nonneg _)
            refine (norm_sum_le _ _).trans (le_of_eq ?_)
            exact Finset.sum_congr rfl fun j _ => by rw [norm_mul, Complex.norm_conj]
        _ ≤ (∑ j, ‖z j‖ ^ 2) * ∑ j, ‖ξ j‖ ^ 2 := Finset.sum_mul_sq_le_sq_mul_sq _ _ _
        _ = ‖z‖ ^ 2 * ∑ j, ‖ξ j‖ ^ 2 := by rw [EuclideanSpace.norm_sq_eq]
    have hz : ‖z‖ ^ 2 ≤ ρ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hann.2.le 2
    have hS : ‖∑ j, z j * (starRingEnd ℂ) (ξ j)‖ ^ 2 ≤ ρ ^ 2 * ∑ j, ‖ξ j‖ ^ 2 :=
      hCS.trans (mul_le_mul_of_nonneg_right hz (Finset.sum_nonneg fun j _ => by positivity))
    have hd : |deriv χ t| ^ 2 ≤ A ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (hA t) 2
    have hρ2 : (0 : ℝ) < ρ ^ 2 := by positivity
    rw [norm_mul, norm_div, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_pos hρ2, mul_pow, div_pow]
    calc |deriv χ t| ^ 2 / (ρ ^ 2) ^ 2 * ‖∑ j, z j * (starRingEnd ℂ) (ξ j)‖ ^ 2
        ≤ A ^ 2 / (ρ ^ 2) ^ 2 * (ρ ^ 2 * ∑ j, ‖ξ j‖ ^ 2) := by gcongr
      _ = A ^ 2 / ρ ^ 2 * ∑ j, ‖ξ j‖ ^ 2 := by field_simp
  · have hd0 : deriv χ t = 0 := by
      rcases not_and_or.mp hann with h | h
      · push_neg at h
        have ht4 : t ≤ 1 / 4 := by
          rw [ht, div_le_iff₀ (by positivity)]; nlinarith [norm_nonneg z]
        apply IsLocalMax.deriv_eq_zero
        exact Filter.Eventually.of_forall fun s => by rw [h1 t ht4]; exact (h01 s).2
      · push_neg at h
        have ht1 : 1 ≤ t := by
          rw [ht, le_div_iff₀ (by positivity)]; nlinarith
        apply IsLocalMin.deriv_eq_zero
        exact Filter.Eventually.of_forall fun s => by rw [h0 t ht1]; exact (h01 s).1
    rw [hd0]; simp

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DblESymmToLinearMap
section
noncomputable section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.WeilTr MeasureTheory GlobalTheory.DoublingEv
open scoped Matrix ENNReal

namespace GlobalTheory.DblInt

theorem elim_dot' {R : Type} [CommRing R] {κ κ' : Type} [Fintype κ] [Fintype κ'] (u v : κ → R) (x y : κ' → R) :
    Sum.elim u x ⬝ᵥ Sum.elim v y = u ⬝ᵥ v + x ⬝ᵥ y := by
  simp [dotProduct, Fintype.sum_sum_type]

section Coord

variable {R : Type} [CommRing R] {E : Type} [CommRing E] [Algebra R E] (c : E →ₐ[R] E)
  {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

theorem hTens_dbl (JA : Matrix α α E) (JB : Matrix β β E) (w w' : Matrix α (β ⊕ β) E) :
    hTens c JA (dbl JB) w w' = hTens c JA JB w.toCols₁ w'.toCols₁ - hTens c JA JB w.toCols₂ w'.toCols₂ := by
  simp only [hTens, dbl, Fintype.sum_sum_type, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
    Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, Matrix.neg_apply, mul_zero, zero_mul,
    Finset.sum_const_zero, add_zero, zero_add, Matrix.toCols₁_apply, Matrix.toCols₂_apply, mul_neg, neg_mul,
    Finset.sum_neg_distrib, Finset.sum_add_distrib]
  rw [← sub_eq_add_neg]

theorem symp_dbl (ξ : E) (JA : Matrix α α E) (JB : Matrix β β E) (w w' : Matrix α (β ⊕ β) E) :
    symp c ξ JA (dbl JB) w w' = symp c ξ JA JB w.toCols₁ w'.toCols₁ - symp c ξ JA JB w.toCols₂ w'.toCols₂ := by
  unfold symp
  rw [hTens_dbl, mul_sub, map_sub]

variable [Invertible (2 : R)] {κ : Type} [Fintype κ] {ξ : E} {JA : Matrix α α E} {JB : Matrix β β E}

def dblCo (d : Darboux (symp c ξ JA JB) κ) : Darboux (symp c ξ JA (dbl JB)) (κ ⊕ κ) where
  e :=
    { toFun := fun w => (Sum.elim (d.e w.toCols₁).1 (d.e w.toCols₂).1, Sum.elim (d.e w.toCols₁).2 (-(d.e w.toCols₂).2))
      map_add' := fun w w' => by
        have h1 : (w + w').toCols₁ = w.toCols₁ + w'.toCols₁ := by ext; simp
        have h2 : (w + w').toCols₂ = w.toCols₂ + w'.toCols₂ := by ext; simp
        rw [h1, h2, map_add (f := _), map_add (f := _)]
        ext k <;> cases k <;> simp [add_comm]
      map_smul' := fun a w => by
        have h1 : (a • w).toCols₁ = a • w.toCols₁ := by ext; simp
        have h2 : (a • w).toCols₂ = a • w.toCols₂ := by ext; simp
        rw [h1, h2, map_smul, map_smul]
        ext k <;> cases k <;> simp
      invFun := fun p => Matrix.fromCols (d.e.symm (p.1 ∘ Sum.inl, p.2 ∘ Sum.inl))
        (d.e.symm (p.1 ∘ Sum.inr, -(p.2 ∘ Sum.inr)))
      left_inv := fun w => by
        simp only [Sum.elim_comp_inl, Sum.elim_comp_inr, neg_neg, Prod.mk.eta, LinearEquiv.symm_apply_apply]
        exact Matrix.fromCols_toCols w
      right_inv := fun p => by
        simp only [Matrix.toCols₁_fromCols, Matrix.toCols₂_fromCols, LinearEquiv.apply_symm_apply, neg_neg,
          Sum.elim_comp_inl_inr] }
  form w w' := by
    simp only [LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk]
    rw [symp_dbl, d.form, d.form, elim_dot', elim_dot', dotProduct_neg, dotProduct_neg]
    ring

theorem dblCo_isDblCoord (d : Darboux (symp c ξ JA JB) κ) : IsDblCoord c ξ JA JB d (dblCo c d) := fun w₁ w₂ => by
  simp [dblCo]

end Coord

section Equivs

variable {R : Type}

def conjE {X : Type} (T : (X → ℂ) ≃ₗ[ℂ] (X → ℂ)) : (X → ℂ) ≃ₗ[ℂ] (X → ℂ) :=
  LinearEquiv.ofLinear (conjMap T.toLinearMap) (conjMap T.symm.toLinearMap)
    (LinearMap.ext fun φ => by simp [conjMap_apply]) (LinearMap.ext fun φ => by simp [conjMap_apply])

theorem conjE_apply {X : Type} (T : (X → ℂ) ≃ₗ[ℂ] (X → ℂ)) (φ : X → ℂ) : conjE T φ = star (T (star φ)) := rfl

def partLE {κ κ' : Type} (T : ((κ → R) → ℂ) ≃ₗ[ℂ] ((κ → R) → ℂ)) : ((κ ⊕ κ' → R) → ℂ) ≃ₗ[ℂ] ((κ ⊕ κ' → R) → ℂ) :=
  LinearEquiv.ofLinear (partL T.toLinearMap) (partL T.symm.toLinearMap)
    (LinearMap.ext fun Φ => funext fun s => by simp [partL_apply])
    (LinearMap.ext fun Φ => funext fun s => by simp [partL_apply])

def partRE {κ κ' : Type} (T : ((κ' → R) → ℂ) ≃ₗ[ℂ] ((κ' → R) → ℂ)) : ((κ ⊕ κ' → R) → ℂ) ≃ₗ[ℂ] ((κ ⊕ κ' → R) → ℂ) :=
  LinearEquiv.ofLinear (partR T.toLinearMap) (partR T.symm.toLinearMap)
    (LinearMap.ext fun Φ => funext fun s => by simp [partR_apply])
    (LinearMap.ext fun Φ => funext fun s => by simp [partR_apply])

def dblE {κ : Type} (T : ((κ → R) → ℂ) ≃ₗ[ℂ] ((κ → R) → ℂ)) : ((κ ⊕ κ → R) → ℂ) ≃ₗ[ℂ] ((κ ⊕ κ → R) → ℂ) :=
  (partRE (conjE T)).trans (partLE T)

end Equivs

end GlobalTheory.DblInt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegreeNonnegOfCurveDegreeNonnegOverZmod
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechPic GlobalTheory.ProjVar GlobalTheory.TrueGeo
open GlobalTheory.LB (toMod)
open GlobalTheory.VB (degOfRank)

namespace GlobalTheory.CurveDevissage

theorem interNum_one_nonneg {k : Type} [Field k] {V : Scheme.{0}} [Algebra k Γ(V, ⊤)]
    (hp : IsProjOver (strHom k (X := V))) (hd : topologicalKrullDim V ≤ 1) {N : LB V} (hN : N.IsLB)
    (h : ∀ (Z : Scheme.{0}) (i : Z ⟶ V) [IsClosedImmersion i] [IsIntegral Z] [Algebra k Γ(Z, ⊤)],
      (∀ r : k, i.appTop (algebraMap k Γ(V, ⊤) r) = algebraMap k Γ(Z, ⊤) r) →
      topologicalKrullDim Z = 1 → 0 ≤ topSelfIntersection k (N.pull i) 1)
    (F : V.Modules) (hF : QCoh.IsFiniteQC F) : 0 ≤ interNum k F ![N] := by
  have := isNoetherian_of_isProjOver hp
  have hL : ∀ i, ((![N] : Fin 1 → LB V) i).IsLB := fun i => by fin_cases i; exact hN
  refine QCoh.devissage V (fun F => 0 ≤ interNum k F ![N])
    (fun F hF => (interNum_eq_zero_of_isZero k hF hL).ge) (fun S hS h₁ h₃ p₁ p₃ => ?_)
    (fun Z hZ _ G hG => ?_) F hF
  · rw [interNum_shortExact hS hL
      (finiteCohTwists_of_isProjOver (algebraMap_eq_strHom k V) _ hp)
      (finiteCohTwists_of_isProjOver (algebraMap_eq_strHom k V) _ hp)]
    exact add_nonneg p₁ p₃
  · have := isIntegral_red hZ
    letI := algebraΓAlong k (redι Z)
    have hi := appTop_algebraMap_along k (redι Z)
    have hpZ : IsProjOver (strHom k (X := (Scheme.IdealSheafData.vanishingIdeal Z).subscheme)) := by
      rw [← comp_strHom hi]
      exact ProjSpace.isProjOver_comp_of_isClosedImmersion _ hp
    have hM := LB.isLB_pull hN (redι Z)
    have e : (fun i => ((![N] : Fin 1 → LB V) i).pull (redι Z)) = ![N.pull (redι Z)] := by
      funext i; fin_cases i; rfl
    have e' : (fun _ : Fin 1 => N.pull (redι Z)) = ![N.pull (redι Z)] := by
      funext i; fin_cases i; rfl
    rw [interNum_pushforward_of_isClosedImmersion hi G hL, e]
    have hdZ : topologicalKrullDim (Scheme.IdealSheafData.vanishingIdeal Z).subscheme ≤ 1 :=
      (redι Z).isClosedEmbedding.isInducing.topologicalKrullDim_le.trans hd
    rcases hdZ.eq_or_lt with h1 | h1
    · rw [VB.interNum_one_eq_genRank_mul k _ hpZ h1 G _ hM]
      refine mul_nonneg (Nat.cast_nonneg _) ?_
      have := h _ (redι Z) hi h1
      rwa [topSelf_def, e'] at this
    · refine (interNum_eq_zero_of_isProjOver (algebraMap_eq_strHom k _) G hpZ ?_
        fun i => by fin_cases i; exact hM).ge
      rw [Fintype.card_fin]
      exact (QCoh.suppDim_le G).trans_lt h1

theorem degOfRank_nonneg : ∀ (p : ℕ) [Fact p.Prime] (V : Scheme.{0}) [Algebra (ZMod p) Γ(V, ⊤)], IsProjOver (strHom (ZMod p) (X := V)) → topologicalKrullDim V ≤ 1 → ∀ N : LB V, N.IsLB → (∀ (Z : Scheme.{0}) (i : Z ⟶ V) [IsClosedImmersion i] [IsIntegral Z] [Algebra (ZMod p) Γ(Z, ⊤)], topologicalKrullDim Z = 1 → 0 ≤ topSelfIntersection (ZMod p) (N.pull i) 1) → 0 ≤ degOfRank (ZMod p) (toMod N) 1 := by
  intro p _ V _ hp hd N hN h
  have := Twist.isFiniteQC_twist (F := structureModule V) hN
  have h1 := interNum_one_nonneg hp hd hN (fun Z i _ _ _ _ hZ => h Z i hZ)
    (twist (structureModule V) N) this
  have h2 := interNum_twist_cons (ZMod p) (structureModule V) (P := ![]) hN isEmptyElim
  have h3 : chi (ZMod p) (twist (structureModule V) N) = chi (ZMod p) (toMod N) :=
    chi_congr _ (Twist.unitTwistIso N)
  have h4 : interNum (ZMod p) (twist (structureModule V) N) ![N] =
    chi (ZMod p) (twist (structureModule V) N) - chi (ZMod p) (structureModule V) :=
    h2.trans (congrArg₂ (· - ·) (interNum_of_isEmpty _ _ _) (interNum_of_isEmpty _ _ _))
  rw [degOfRank]
  push_cast
  linarith

end GlobalTheory.CurveDevissage
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetRationalSectionsEqPowProductLinearForms
section
open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice GlobalTheory.HSShort

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSShort

theorem det_symbolBlock {E ι κ : Type} [Field E] [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (w : κ → E) (e : ℕ) (r : κ → κ → E) :
    (Matrix.of fun (i i' : ι × κ) => if i.1 = i'.1 then w i.2 ^ e * r i'.2 i.2 else 0).det =
      (∏ p, w p) ^ (e * Fintype.card ι) *
        (Matrix.of fun (i i' : ι × κ) => if i.1 = i'.1 then r i'.2 i.2 else 0).det := by
  have h : (Matrix.of fun (i i' : ι × κ) => if i.1 = i'.1 then w i.2 ^ e * r i'.2 i.2 else 0) =
      Matrix.diagonal (fun i : ι × κ => w i.2 ^ e) *
        Matrix.of fun (i i' : ι × κ) => if i.1 = i'.1 then r i'.2 i.2 else 0 := by
    ext i i'
    simp only [Matrix.of_apply, Matrix.diagonal_mul]
    split_ifs <;> simp
  rw [h, Matrix.det_mul, Matrix.det_diagonal, Fintype.prod_prod_type]
  simp only [Finset.prod_pow, Finset.prod_const, Finset.card_univ]
  rw [← pow_mul, mul_comm (Fintype.card ι)]

theorem det_rational_eq_pow : ∀ (F A : Type) [Field F] [NumberField F] [AddCommGroup A] [Module F A] [Module (𝓞 F) A] [IsScalarTower (𝓞 F) F A] (S : Sys F A), S.Hyp → ∀ (E A' : Type) [Field E] [Algebra F E] [AddCommGroup A'] [Module E A'] (s : Fin S.D → Fin S.N → F) (δ : ℕ) (Φ : S.Flat E A' (fun i k => algebraMap F E (s i k)) δ) (d : ℕ) (b : Module.Basis (Fin d) F (S.V S.T)) (c : Fin d → A →ₗ[F] F), S.IsCo b c → ∀ (col : Fin d → S.Col) (m : Fin δ → S.V 0) (ix : (Σ a : Fin (S.T - S.D), MonoDeg (Fin S.D) a) × Fin δ ↪ Fin d), S.Shape δ col m ix → S.deepRank s ≤ (Finset.univ.filter fun k => (col k).j = S.D).card → ∃ γ : E, ∀ l : Fin S.N → E, aeval (join (fun i k => algebraMap F E (s i k)) l) (S.det c col) = γ * (∏ p, ∑ k, l k * Φ.y p k) ^ S.expo := by
  intro F A _ _ _ _ _ _ S hS E A' _ _ _ _ s δ Φ d b c hc col m ix hsh hrank
  classical
  obtain ⟨c', -, hev⟩ := _root_.GlobalTheory.HSShort.ColEval.columns_eval F A S hS E A' (fun i k => algebraMap F E (s i k)) δ Φ d b c hc
  have hsym := _root_.GlobalTheory.HSShort.symbols_of_columns F A S hS E A' (fun i k => algebraMap F E (s i k)) δ Φ d col m ix hsh
  obtain ⟨hfd, hfr, -⟩ := _root_.GlobalTheory.HSShort.deepStep_finrank F A S hS E A' s δ Φ
  obtain ⟨hcard, -, -⟩ := _root_.GlobalTheory.HSShort.monomial_counts S.D S.T hS.one_le hS.le_T
  let v : (Fin S.N → E) → Fin d → A' := fun l k =>
    word Φ.mul (fun q j => join (fun i k => algebraMap F E (s i k)) l ((col k).β q, j)) (Φ.ι (col k).x)
  let ω : A' [⋀^Fin d]→ₗ[E] E := (Matrix.detRowAlternating).compLinearMap (LinearMap.pi c')
  have hdet : ∀ l, aeval (join (fun i k => algebraMap F E (s i k)) l) (S.det c col) = ω (v l) := by
    intro l
    rw [Sys.det, AlgHom.map_det, AlternatingMap.compLinearMap_apply]
    change _ = Matrix.det (fun k i => c' i (v l k))
    rw [← Matrix.det_transpose]
    congr 1
    ext i k
    simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, Matrix.transpose_apply]
    exact (hev (col i) (join (fun i k => algebraMap F E (s i k)) l)).2 k

  let ix' : (Σ a : Fin (S.T - S.D), MonoDeg (Fin S.D) a × Fin δ) ↪ Fin d :=
    (Equiv.sigmaProdDistrib (fun a : Fin (S.T - S.D) => MonoDeg (Fin S.D) a) (Fin δ)).symm.toEmbedding.trans ix
  have hix' : ∀ q, ix' q = ix (⟨q.1, q.2.1⟩, q.2.2) := fun q => rfl

  have hind : ∀ l k, k ∉ Set.range ix → v l k = v 0 k := by
    intro l k hk
    have hL : (fun q j => join (fun i k => algebraMap F E (s i k)) l ((col k).β q, j)) = (fun q j => join (fun i k => algebraMap F E (s i k)) 0 ((col k).β q, j)) := by
      rcases hsh.rest k hk with ⟨-, hβ⟩ | hj
      · funext q j
        obtain ⟨i, hi⟩ := Fin.exists_castSucc_eq.mpr (hβ q)
        rw [← hi]
        simp [join]
      · have ht : (col k).t = 0 := by have := (col k).add; omega
        funext q
        exact absurd q.isLt (by omega)
    show word Φ.mul _ _ = word Φ.mul _ _
    rw [hL]

  have hzq : ∀ q : (Σ a : Fin (S.T - S.D), MonoDeg (Fin S.D) a × Fin δ),
      ∃ x : A', ∃ hx : x ∈ Φ.U q.1, Φ.sym q.1 ⟨x, hx⟩ = Pi.single q.2 1 := by
    rintro ⟨a, α, p⟩
    obtain ⟨k₀, hk₀⟩ := Function.ne_iff.mp (Φ.y_ne p)
    have hk₀' : Φ.y p k₀ ≠ 0 := hk₀
    have ht : Φ.y p k₀ ^ (S.T - (a : ℕ)) ≠ 0 := pow_ne_zero _ hk₀'
    have hmem : (Pi.single p (Φ.y p k₀ ^ (S.T - (a : ℕ)))⁻¹ : Fin δ → E) ∈
        (Submodule.span E (Φ.ι '' S.V 0)).map Φ.res := by
      rw [Φ.onto]; exact Submodule.mem_top
    obtain ⟨m₀, hm₀, hres⟩ := hmem
    obtain ⟨h, hh⟩ := Φ.mono a a.2 α (fun _ => Pi.single k₀ 1) m₀ hm₀
    refine ⟨_, h, ?_⟩
    funext i
    obtain ⟨α', p'⟩ := i
    rw [hh, hres]
    by_cases hp : p' = p
    · rw [hp]
      by_cases hα : α' = α
      · rw [hα]
        simp [Finset.prod_const, Pi.single_apply, ht]
      · have hα' : α'.1 ≠ α.1 := fun e => hα (Subtype.ext e)
        simp [hα', hα]
    · simp [hp, Pi.single_apply]
  choose zq hzqU hzqS using hzq
  let z : Fin d → A' := Function.extend ix' zq (v 0)
  have hz_ix : ∀ q, z (ix' q) = zq q := fun q => ix'.injective.extend_apply zq (v 0) q
  have hz : ∀ q, z (ix' q) ∈ Φ.U q.1 := fun q => (hz_ix q).symm ▸ hzqU q
  have hzs : ∀ q, Φ.sym q.1 ⟨z (ix' q), hz q⟩ = Pi.single q.2 1 := by
    intro q
    have e : (⟨z (ix' q), hz q⟩ : Φ.U q.1) = ⟨zq q, hzqU q⟩ := Subtype.ext (hz_ix q)
    rw [e]; exact hzqS q
  have hzout : ∀ l k, k ∉ Set.range ix' → z k = v l k := by
    intro l k hk
    show Function.extend ix' zq (v 0) k = _
    rw [Function.extend_apply' _ _ _ hk]
    have hk' : k ∉ Set.range ix := by
      rintro ⟨q, rfl⟩; exact hk ⟨(Equiv.sigmaProdDistrib _ _) q, rfl⟩
    exact (hind l k hk').symm

  let J : Finset (Fin d) := Finset.univ.filter fun k => (col k).j = S.D
  have hnotix : ∀ k, (col k).j = S.D → k ∉ Set.range ix := by
    rintro k hk ⟨q, rfl⟩
    have := hsh.x_j q
    have := hS.one_le
    omega
  have hv : ∀ l q, v l (ix' q) ∈ Φ.U q.1 := fun l q => ((hsym l).1 q.1 q.2.1 q.2.2).fst
  have hJ : ∀ l, ∀ k ∈ J, k ∉ Set.range ix' ∧ v l k ∈ Φ.U (S.T - S.D) := by
    intro l k hk
    have hk' : (col k).j = S.D := (Finset.mem_filter.mp hk).2
    refine ⟨?_, (hsym l).2 k (hnotix k hk') hk'⟩
    rintro ⟨q, hq⟩
    exact hnotix k hk' ⟨_, (hix' q).symm.trans hq⟩
  haveI := hfd
  have hrank' : Module.finrank E (Φ.U (S.T - S.D)) ≤ J.card := hfr ▸ hrank
  let B : ∀ a : Fin (S.T - S.D), Matrix (MonoDeg (Fin S.D) a × Fin δ) (MonoDeg (Fin S.D) a × Fin δ) E :=
    fun a => Matrix.of fun i i' => if i.1 = i'.1 then Φ.res (Φ.ι (m i'.2)) i.2 else 0
  have hexp : ∑ a : Fin (S.T - S.D), (S.T - (a : ℕ)) * Fintype.card (MonoDeg (Fin S.D) a) = S.expo := by
    rw [Sys.expo, ← Fin.sum_univ_eq_sum_range]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Nat.card_eq_fintype_card, hcard, mul_comm]
  refine ⟨(∏ a, (B a).det) * ω z, fun l => ?_⟩
  rw [hdet]
  have key := _root_.GlobalTheory.FiltDet.det_filtration_symbols E A' (S.T - S.D) d (fun a => MonoDeg (Fin S.D) a × Fin δ) Φ.U (fun a => Φ.sym a)
    Φ.le (fun a x => Φ.ker a a.2 x) ix' J (v l) (hv l) (hJ l) hrank' z hz hzs (hzout l) ω
  rw [key]
  have hblock : ∀ a : Fin (S.T - S.D),
      (Matrix.of fun i i' : MonoDeg (Fin S.D) a × Fin δ => Φ.sym a ⟨v l (ix' ⟨a, i'⟩), hv l ⟨a, i'⟩⟩ i).det =
        (∏ p, ∑ k, l k * Φ.y p k) ^ ((S.T - (a : ℕ)) * Fintype.card (MonoDeg (Fin S.D) a)) * (B a).det := by
    intro a
    have hM : (Matrix.of fun i i' : MonoDeg (Fin S.D) a × Fin δ => Φ.sym a ⟨v l (ix' ⟨a, i'⟩), hv l ⟨a, i'⟩⟩ i) =
        Matrix.of fun (i i' : MonoDeg (Fin S.D) a × Fin δ) =>
          if i.1 = i'.1 then (∑ k, l k * Φ.y i.2 k) ^ (S.T - (a : ℕ)) * Φ.res (Φ.ι (m i'.2)) i.2 else 0 := by
      ext i i'
      refine (((hsym l).1 a i'.1 i'.2).snd i.1 i.2).trans ?_
      simp only [Matrix.of_apply, Subtype.val_inj]
    rw [hM, det_symbolBlock (ι := MonoDeg (Fin S.D) a) (fun p => ∑ k, l k * Φ.y p k) (S.T - (a : ℕ))
      (fun p' p => Φ.res (Φ.ι (m p')) p)]
  simp only [hblock]
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hexp]
  ring

end GlobalTheory.HSShort
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiscreteRationalPointsSubgroup
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.UnipMass

namespace GlobalTheory.RatUDiscreteSub

theorem discreteTopology_subgroupOf : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (N : Subgroup (UA σ J)),
    DiscreteTopology ((ratU σ J).subgroupOf N) := by
  intro F E _ _ _ _ _ σ n J N
  haveI := GlobalTheory.RatUDiscrete.discreteTopology_ratU F E σ n J
  let φ : (ratU σ J).subgroupOf N → ratU σ J := fun x => ⟨x.1.1, Subgroup.mem_subgroupOf.1 x.2⟩
  have h2 : Topology.IsEmbedding (fun x : (ratU σ J).subgroupOf N => ((x : N) : UA σ J)) :=
    Topology.IsEmbedding.subtypeVal.comp Topology.IsEmbedding.subtypeVal
  have hφ : Topology.IsEmbedding φ :=
    (Topology.IsEmbedding.of_comp_iff (Topology.IsEmbedding.subtypeVal (p := fun x : UA σ J => x ∈ ratU σ J))).1 h2
  exact hφ.discreteTopology

end GlobalTheory.RatUDiscreteSub
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledFockVacuumEqSmulVacuumMulConjStatement
section
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift GlobalTheory.RealLift.Dbl

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubledFockVacuum_eq_smul_vacuum_mul_conj : DerEx → VacLine → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (α β κ : Type) [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] (P Q R S : ℕ) (ψ : AddChar (AF F) ℂ)
    (τ : ∀ w : InfinitePlace F, EmbOver E w) (JA : Matrix α α (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (JB : Matrix β β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))
    (d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ) (dd : Darboux (symp (R := AF F) (cA σ) (-1) JA (dbl JB)) (κ ⊕ κ))
    (a b : ℂ) (A : InfinitePlace F → Matrix α (Ix P Q) ℂ) (C : InfinitePlace F → Matrix β (Ix R S) ℂ)
    (Φ : Tens F P Q R S →ₗ[ℂ] SInf F κ) (Φd : Tens F P Q (R + S) (S + R) →ₗ[ℂ] SInf F (κ ⊕ κ)),
    IsCMExt F E σ → IsStd ψ → Framed τ JA JB a b A C → IsFockMap ψ τ d A C Φ → IsDblCoord (cA σ) (-1) JA JB d dd →
    IsFockMap ψ τ dd A (fun w => dblM (C w)) Φd →
    ∃ z : ℂ, z ≠ 0 ∧ ∀ x : κ ⊕ κ → mixedEmbedding.mixedSpace F,
      Φd (PiTensorProduct.tprod ℂ fun _ => 1) x = z * Φ (PiTensorProduct.tprod ℂ fun _ => 1) (x ∘ Sum.inl) *
        star (Φ (PiTensorProduct.tprod ℂ fun _ => 1) (x ∘ Sum.inr)) := by
  first | exact @GlobalTheory.RealLift.VacBox.vac_box | exact GlobalTheory.RealLift.VacBox.vac_box | (intros; apply GlobalTheory.RealLift.VacBox.vac_box <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertSchemeFiniteFreeAlgebraAffineExistsStatement
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hilbert_scheme_finite_free_algebra_affine_exists : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] [Module.Free A B] [Module.Finite A B] (r : ℕ), ∃ (H : Scheme.{0}) (h : H ⟶ Spec (CommRingCat.of A)) (U : Scheme.{0}) (u : U ⟶ pullback (Spec.map (CommRingCat.ofHom (algebraMap A B))) h), IsProper h ∧ IsClosedImmersion u ∧ IsFinite (u ≫ pullback.snd _ h) ∧ Flat (u ≫ pullback.snd _ h) ∧ (∀ y, (u ≫ pullback.snd _ h).finrank y = r) ∧ ∀ (T : Scheme.{0}) (g : T ⟶ Spec (CommRingCat.of A)) (V : Scheme.{0}) (v : V ⟶ pullback (Spec.map (CommRingCat.ofHom (algebraMap A B))) g), IsClosedImmersion v → IsFinite (v ≫ pullback.snd _ g) → Flat (v ≫ pullback.snd _ g) → (∀ y, (v ≫ pullback.snd _ g).finrank y = r) → ∃! f : T ⟶ H, ∃ hf : f ≫ h = g, ∃ w : V ⟶ U, IsPullback v w (pullback.map _ g _ h (𝟙 _) f (𝟙 _) (by simp) (by rw [Category.comp_id, hf])) u := by
  first | (exact @GlobalTheory.HilbAff.hilbertScheme_exists) | (exact GlobalTheory.HilbAff.hilbertScheme_exists) | (intros; apply GlobalTheory.HilbAff.hilbertScheme_exists <;> assumption)
end

