module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PartialZetaFunctionalEquation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0157
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0178
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0241
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0253
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0213
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0206
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0225
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0251
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BasicIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0228
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0169
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0192
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0191
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0245
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0004
public import ReciprocityTheory.AnalyticForms.AnalyticCharts.Osgood

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeEisensteinWeightTwoQExpansion
section
noncomputable section

open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

namespace GlobalTheory.HeckeTwoExp

variable {F : Type} [Field F] [NumberField F]

theorem hTrans_zero (ν y : ℝ) (hy : y ≠ 0) :
    hTrans 0 ν y = if 0 < ν * y then
      -4 * (Real.pi : ℂ) ^ 2 * ((|ν| : ℝ) : ℂ) * ((Real.exp (-(2 * Real.pi * (ν * y))) : ℝ) : ℂ) else 0 := by
  rcases hy.lt_or_gt with h | h
  · have e := hTrans_zero_neg (-ν) y
    rw [neg_neg] at e
    rw [← e, _root_.GlobalTheory.HeckeTwo.hTrans_sigma_zero_eq _ _ (neg_pos.2 h)]
    by_cases hν : 0 < -ν
    · have h2 : 0 < ν * y := by nlinarith
      rw [if_pos hν, if_pos h2, abs_of_neg (by linarith : ν < 0),
        show -(2 * Real.pi * -ν * -y) = -(2 * Real.pi * (ν * y)) by ring]
    · have h2 : ¬ 0 < ν * y := by nlinarith
      rw [if_neg hν, if_neg h2]
  · rw [_root_.GlobalTheory.HeckeTwo.hTrans_sigma_zero_eq _ _ h]
    by_cases hν : 0 < ν
    · have h2 : 0 < ν * y := mul_pos hν h
      rw [if_pos hν, if_pos h2, abs_of_pos hν, show 2 * Real.pi * ν * y = 2 * Real.pi * (ν * y) by ring]
    · have h2 : ¬ 0 < ν * y := by nlinarith
      rw [if_neg hν, if_neg h2]

theorem fTerm_zero [IsTotallyReal F] {z : Emb F → ℂ} (hz : z ∈ upperHalf F) {b ν : F} (hb : b ≠ 0) (hν : ν ≠ 0) :
    fTerm 0 z b ν = if ∀ τ : Emb F, 0 < τ (ν * b) then
      (-4 * (Real.pi : ℂ) ^ 2) ^ Fintype.card (Emb F) * ((|(Algebra.norm ℚ ν : ℝ)| : ℝ) : ℂ) * qPow (ν * b) z
      else 0 := by
  have hyτ : ∀ τ : Emb F, τ b * (z τ).im ≠ 0 := fun τ => mul_ne_zero ((map_ne_zero τ).2 hb) (hz τ).ne'
  unfold fTerm
  simp only [hTrans_zero _ _ (hyτ _)]
  split_ifs with hc
  · have hc' : ∀ τ : Emb F, 0 < τ ν * (τ b * (z τ).im) := fun τ => by
      have := hc τ; rw [map_mul] at this; rw [← mul_assoc]; exact mul_pos this (hz τ)
    rw [Finset.prod_congr rfl fun τ _ => by rw [if_pos (hc' τ)]]
    rw [abs_norm_eq_prod, qPow, Finset.mul_sum, Complex.exp_sum]
    rw [show ((-4 * (Real.pi : ℂ) ^ 2) ^ Fintype.card (Emb F) * ∏ τ : Emb F, ((|τ ν| : ℝ) : ℂ)) *
        ∏ x : Emb F, Complex.exp (2 * (Real.pi : ℂ) * I * ((x (ν * b) : ℂ) * z x)) =
        ∏ τ : Emb F, ((-4 * (Real.pi : ℂ) ^ 2) * ((|τ ν| : ℝ) : ℂ) *
          Complex.exp (2 * (Real.pi : ℂ) * I * ((τ (ν * b) : ℂ) * z τ))) by
      rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [mul_comm, mul_assoc, Complex.ofReal_exp, ← Complex.exp_add]
    congr 1; congr 1
    conv_rhs => rw [← Complex.re_add_im (z τ)]
    simp only [map_mul]
    push_cast
    linear_combination (-2 * (Real.pi : ℂ) * (τ ν : ℂ) * (τ b : ℂ) * ((z τ).im : ℂ)) * I_sq
  · push_neg at hc
    obtain ⟨τ, hτ⟩ := hc
    have : ¬ 0 < τ ν * (τ b * (z τ).im) := by
      rw [map_mul] at hτ; rw [← mul_assoc]; exact not_lt.2 (mul_nonpos_of_nonpos_of_nonneg hτ (hz τ).le)
    exact Finset.prod_eq_zero (Finset.mem_univ τ) (by rw [if_neg this, mul_zero])

theorem bOne_zero_expansion [IsTotallyReal F] (𝔞 𝔟 : Frac F) (z : Emb F → ℂ) (hz : z ∈ upperHalf F) :
    Summable (qClass 𝔞 𝔟 2 z) ∧
      (cK F 2 : ℂ) * (kFac F 0 * (omegaFactor 𝔞 : ℂ) * bOne 𝔞 𝔟 0 z) / (omegaFactor 𝔞 : ℂ) ^ 2 =
        ∑' c, qClass 𝔞 𝔟 2 z c := by
  have hS := _root_.GlobalTheory.HeckeTwoSum.summable_qClass F 𝔞 𝔟 z hz
  refine ⟨hS, ?_⟩
  have hn : (nrm 𝔞 : ℂ) ≠ 0 := by exact_mod_cast nrm_ne_zero 𝔞
  have hs : ((dF F ^ ((1 : ℝ) / 2) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.rpow_pos_of_pos (dF_pos (F := F)) _).ne'
  have hcK : (cK F 2 : ℂ) = ((dF F ^ ((1 : ℝ) / 2) : ℝ) : ℂ) := by
    unfold cK; norm_num
  have hL : (cK F 2 : ℂ) * (kFac F 0 * (omegaFactor 𝔞 : ℂ) * bOne 𝔞 𝔟 0 z) / (omegaFactor 𝔞 : ℂ) ^ 2 =
      (kFac F 0 / (nrm 𝔞 : ℂ)) * bOne 𝔞 𝔟 0 z := by
    rw [hcK, omegaFactor]; push_cast
    push_cast at hs
    field_simp
  rw [hL, bOne, ← tsum_mul_left, tsum_qClass_eq 𝔞 𝔟 z hS]
  refine tsum_congr fun c => ?_
  rw [← tsum_mul_left]
  refine tsum_congr fun ν => ?_
  rw [fTerm_zero hz c.out.2.2 ν.2.2]
  split_ifs with hc
  · have hk := kFac_zero_mul (F := F)
    unfold qTerm
    simp only [show (2:ℕ) - 1 = 1 from rfl, pow_one, Complex.ofReal_div]
    linear_combination (((|(Algebra.norm ℚ ν.1 : ℝ)| : ℝ) : ℂ) / (nrm 𝔞 : ℂ) * qPow (ν.1 * c.out.1) z) * hk
  · rw [mul_zero]

theorem bOne_zero_qExpansion : ∀ (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyReal F]
    (𝔞 𝔟 : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F), ∀ z ∈ GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.upperHalf F,
    Summable (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.qClass 𝔞 𝔟 2 z) ∧ (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.cK F 2 : ℂ) * (GlobalTheory.HeckeTwo.kFac F 0 *
      (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.omegaFactor 𝔞 : ℂ) * GlobalTheory.HeckeTwo.bOne 𝔞 𝔟 0 z) / (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.omegaFactor 𝔞 : ℂ) ^ 2 =
      ∑' c, GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.qClass 𝔞 𝔟 2 z c :=
  fun _ _ _ _ 𝔞 𝔟 z hz => bOne_zero_expansion 𝔞 𝔟 z hz

end GlobalTheory.HeckeTwoExp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeEisensteinZeroFrequencyPartIsSmoothHolomorphic
section
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

noncomputable section

namespace GlobalTheory.HeckeTwo

namespace BZeroGood

theorem card_emb_totReal (F : Type) [Field F] [NumberField F] [IsTotallyReal F] :
    Fintype.card (Emb F) = Module.finrank ℚ F := by
  rw [← Embeddings.card F ℂ]
  refine Fintype.card_of_bijective (f := fun τ : F →+* ℝ => Complex.ofRealHom.comp τ) ⟨fun τ τ' h => ?_, fun φ => ?_⟩
  · ext x
    exact Complex.ofReal_injective (RingHom.congr_fun h x)
  · exact ⟨(IsTotallyReal.complexEmbedding_isReal φ).embedding, RingHom.ext fun x =>
      (IsTotallyReal.complexEmbedding_isReal φ).coe_embedding_apply x⟩

theorem halfPlane_mem_nhds_zero : halfPlane ∈ nhds (0 : ℂ) := by
  refine (isOpen_lt continuous_const Complex.continuous_re).mem_nhds ?_
  show (-1 / 2 : ℝ) < (0 : ℂ).re
  norm_num

theorem _root_.GlobalTheory.HeckeTwo.bZero_isGood (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyReal F] (hf : 2 ≤ Module.finrank ℚ F)
    (𝔞 𝔟 : Frac F) (Zb R : ℂ → ℂ) (hR : Differentiable ℂ R) (hZ : ∀ s : ℂ, s ≠ 1 → Zb s = R s / (s - 1)) :
    IsGood (bZero Zb 𝔞 𝔟) := by
  set f := Fintype.card (Emb F) with hfdef
  have hf2 : 2 ≤ f := by rw [hfdef, card_emb_totReal F]; exact hf
  set E : ℂ → ℂ := fun σ => if σ = 0 then 0 else
    kFac F σ * (omegaFactor 𝔞 : ℂ) * ((nrm 𝔟 : ℝ) : ℂ) ^ (-1 - 2 * σ) * Zb (1 + 2 * σ) * cConst σ ^ f with hE
  set G : ℂ → ℂ := fun σ =>
    kFac F σ * (omegaFactor 𝔞 : ℂ) * ((nrm 𝔟 : ℝ) : ℂ) ^ (-1 - 2 * σ) * (R (1 + 2 * σ) / 2) *
      dslope cConst 0 σ * cConst σ ^ (f - 1) with hG
  have hEG : E = G := by
    funext σ
    simp only [hE, hG]
    split_ifs with h0
    · subst h0
      rw [_root_.GlobalTheory.HeckeTwo.cConst_zero, zero_pow (by omega), mul_zero]
    · rw [dslope_of_ne _ h0, slope_def_field, _root_.GlobalTheory.HeckeTwo.cConst_zero, hZ _ (by
          intro h; apply h0; linear_combination h / 2)]
      have hf1 : f = (f - 1) + 1 := by omega
      rw [hf1, pow_succ]
      simp only [Nat.add_sub_cancel]
      field_simp
      ring
  have hGd : DifferentiableOn ℂ G halfPlane := by
    intro σ hσ
    have hσ' : -1 - 2 * σ ≠ 0 := by
      intro h
      have : σ.re = -1 / 2 := by
        have := congrArg Complex.re h
        simp at this
        linarith
      simp only [halfPlane, Set.mem_setOf_eq] at hσ
      linarith
    have h1 : DifferentiableAt ℂ (fun σ : ℂ => ((nrm 𝔟 : ℝ) : ℂ) ^ (-1 - 2 * σ)) σ :=
      DifferentiableAt.const_cpow ((differentiableAt_const _).sub (differentiableAt_id.const_mul _)) (Or.inr hσ')
    have h2 : DifferentiableAt ℂ (fun σ : ℂ => R (1 + 2 * σ)) σ :=
      (hR _).comp σ ((differentiableAt_const _).add (differentiableAt_id.const_mul _))
    have h3 : DifferentiableWithinAt ℂ (dslope cConst 0) halfPlane σ :=
      ((differentiableOn_dslope halfPlane_mem_nhds_zero).2 _root_.GlobalTheory.HeckeTwo.cConst_differentiableOn) σ hσ
    have h4 : DifferentiableWithinAt ℂ cConst halfPlane σ := _root_.GlobalTheory.HeckeTwo.cConst_differentiableOn σ hσ
    exact ((((kFac_differentiable σ).differentiableWithinAt.mul (differentiableWithinAt_const _)).mul
      h1.differentiableWithinAt).mul (h2.differentiableWithinAt.div_const _)).mul h3 |>.mul (h4.pow _)
  have hB : bZero Zb 𝔞 𝔟 = fun σ z => E σ * ∏ τ : Emb F, (((z τ).im : ℝ) : ℂ) ^ (-1 - 2 * σ) := by
    funext σ z
    simp only [bZero, hE]
    split_ifs
    · simp
    · rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
      ring
  rw [hB]
  exact GlobalTheory.HeckeTwoMul.isGood_mul F E _ (hEG ▸ hGd) ⟨fun σ _ => _root_.GlobalTheory.upperHalf_prodImPow_contDiffOn F σ, fun w z hz => _root_.GlobalTheory.HeckeTwo.prodIm_wirtWord_differentiableOn F w z hz⟩

end BZeroGood

end GlobalTheory.HeckeTwo
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertCoordinateMapBijectiveOfLeAffine
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

namespace GlobalTheory.HilbAff

theorem coord_bijective_of_le_affine : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (N r : ℕ) (e : Module.Basis (Fin N) A B) (σ : Fin r ↪ Fin N) (Z : Scheme.{0}) (y : (GlobalTheory.HilbAff.functor A B r).obj (op Z)) (W W' : Z.affineOpens), (W' : Z.Opens) ≤ W → Function.Bijective (GlobalTheory.HilbAff.coord A B e σ y W) → Function.Bijective (GlobalTheory.HilbAff.coord A B e σ y W') := by
  intro A B _ _ _ N r e σ Z y W W' hle hW
  have hbas : ∀ f : Γ(Z, W), Function.Bijective (coord A B e σ y (Z.basicOpen f)) := by
    intro f
    rw [GlobalTheory.T.affineHilbertCoordinateMap_basicOpen_bijective A B N r e σ Z y W f]
    exact ⟨LocalizedModule.map_injective _ _ hW.1, LocalizedModule.map_surjective _ _ hW.2⟩
  let s : Set Γ(Z, W') := {g | Function.Bijective (coord A B e σ y (Z.basicOpen g))}
  have hspan : Ideal.span s = ⊤ := by
    rw [← W'.2.self_le_iSup_basicOpen_iff]
    intro x hx
    obtain ⟨f, g, hfg, hxf⟩ := exists_basicOpen_le_affine_inter W.2 W'.2 x ⟨hle hx, hx⟩
    refine TopologicalSpace.Opens.mem_iSup.2 ⟨⟨g, ?_⟩, ?_⟩
    · show Function.Bijective _
      rw [← hfg]; exact hbas f
    · show x ∈ Z.basicOpen g
      rw [← hfg]; exact hxf
  exact bijective_of_localized_span s hspan _ fun g => (GlobalTheory.T.affineHilbertCoordinateMap_basicOpen_bijective A B N r e σ Z y W' g.1).1 g.2

end GlobalTheory.HilbAff
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertEisensteinNonconstantTermsHasSum
section
open scoped nonZeroDivisors

noncomputable section

namespace GlobalTheory.EisNonConst
open NumberField GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.SlopeTestRemainingChoices.EisFibre

theorem qTerm_norm {F : Type} [Field F] [NumberField F] (𝔞 : Frac F) (k : ℕ) (z : Emb F → ℂ) (p : F × F) :
    ((‖qTerm 𝔞 k z p‖ : ℝ) : ℂ) = qTerm 𝔞 k (fun τ => Complex.I * ((z τ).im : ℂ)) p := by
  have hr : (0 : ℝ) ≤ (|(Algebra.norm ℚ p.1 : ℝ)| / nrm 𝔞) ^ (k - 1) := by
    apply pow_nonneg; apply div_nonneg (abs_nonneg _)
    unfold nrm; exact_mod_cast FractionalIdeal.absNorm_nonneg _
  unfold qTerm qPow
  rw [norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_of_nonneg hr]
  push_cast
  congr 1
  congr 1
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im, Complex.re_sum, Complex.im_sum, Finset.mul_sum]

theorem nonconst_terms : ∀ (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyReal F], GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent.Lipschitz →
  ∀ (𝔞 𝔟 : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F) (k : ℕ), 2 ≤ k → Even k →
  (∀ z ∈ GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.upperHalf F, Summable (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.eisClass 𝔞 𝔟 k 0 z)) →
  ∀ z ∈ GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.upperHalf F, Summable (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.qClass 𝔞 𝔟 k z) ∧
    HasSum (fun c : {c : Quotient (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latRel 𝔞 𝔟) // c.out.1.2 ≠ 0} => GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.eisClass 𝔞 𝔟 k 0 z c)
      ((GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.omegaFactor 𝔞 : ℂ) ^ k / (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.cK F k : ℂ) * ∑' c, GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.qClass 𝔞 𝔟 k z c) := by
  intro F _ _ _ hL 𝔞 𝔟 k hk2 hke hsum z hz
  obtain ⟨e1, he1⟩ := _root_.GlobalTheory.LatFibre.exists_equiv F 𝔞 𝔟
  obtain ⟨e2, he2⟩ := _root_.GlobalTheory.Div.QFibre.qFibres F 𝔞 𝔟
  set C : ℂ := (omegaFactor 𝔞 : ℂ) ^ k / (cK F k : ℂ) with hC
  set y : Emb F → ℂ := fun τ => Complex.I * ((z τ).im : ℂ) with hy_def
  have hdF : 0 < dF F := abs_pos.2 (by exact_mod_cast discr_ne_zero F)
  have hN : 0 < nrm 𝔞 := by
    unfold nrm
    have h2 : FractionalIdeal.absNorm (𝔞 : FractionalIdeal (𝓞 F)⁰ F) ≠ 0 := by
      rw [Ne, FractionalIdeal.absNorm_eq_zero_iff]; exact 𝔞.ne_zero
    exact_mod_cast lt_of_le_of_ne (FractionalIdeal.absNorm_nonneg _) h2.symm
  have hCne : C ≠ 0 := by
    have h1 : 0 < omegaFactor 𝔞 := mul_pos (Real.rpow_pos_of_pos hdF _) hN
    have h2 : 0 < cK F k := mul_pos (pow_pos (by exact_mod_cast Nat.factorial_pos _) _) (Real.rpow_pos_of_pos hdF _)
    rw [hC]
    exact div_ne_zero (pow_ne_zero _ (by exact_mod_cast h1.ne')) (by exact_mod_cast h2.ne')
  have hy : y ∈ upperHalf F := fun τ => by simpa [hy_def] using hz τ

  have hlat : ∀ w ∈ upperHalf F, Summable (fun x : (Σ _β : NzCls 𝔟, (latM 𝔞 : Set F)) =>
      eisTerm k 0 w ((x.2 : F), rep x.1)) := by
    intro w hw
    have h1 : Summable (fun c : {c : Quotient (latRel 𝔞 𝔟) // c.out.1.2 ≠ 0} => eisClass 𝔞 𝔟 k 0 w c) :=
      (hsum w hw).subtype _
    have h2 := (e1.summable_iff (f := fun c : {c : Quotient (latRel 𝔞 𝔟) // c.out.1.2 ≠ 0} => eisClass 𝔞 𝔟 k 0 w c)).2 h1
    refine h2.congr fun x => ?_
    simp only [Function.comp_apply]
    exact he1 k hke 0 w x

  have hqfib : ∀ β : NzCls 𝔟, Summable (fun ν : posCone 𝔞 (rep β) => ‖qTerm 𝔞 k z (ν.1, rep β)‖) := by
    intro β
    have := (GlobalTheory.EisPerB.lattice_sum_eq_cone_sum F hL 𝔞 k hk2 hke (rep β) (rep_ne_zero β) y hy).1
    rw [← Complex.summable_ofReal]
    refine this.congr fun ν => ?_
    exact (qTerm_norm 𝔞 k z _).symm
  have hqsig : Summable (fun x : (Σ β : NzCls 𝔟, posCone 𝔞 (rep β)) => qTerm 𝔞 k z (x.2.1, rep x.1)) := by
    refine Summable.of_norm ?_
    rw [summable_sigma_of_nonneg (fun _ => norm_nonneg _)]
    refine ⟨hqfib, ?_⟩
    have hmarg : Summable (fun β : NzCls 𝔟 => ∑' a : (latM 𝔞 : Set F), ‖eisTerm k 0 y ((a : F), rep β)‖) :=
      (summable_norm_iff.2 (hlat y hy)).sigma
    refine Summable.of_nonneg_of_le (fun _ => tsum_nonneg fun _ => norm_nonneg _) (fun β => ?_) (hmarg.mul_left ‖C‖⁻¹)
    obtain ⟨-, hP⟩ := GlobalTheory.EisPerB.lattice_sum_eq_cone_sum F hL 𝔞 k hk2 hke (rep β) (rep_ne_zero β) y hy
    have hfib := hqfib β
    have hT : ((∑' ν : posCone 𝔞 (rep β), ‖qTerm 𝔞 k z (ν.1, rep β)‖ : ℝ) : ℂ) =
        ∑' ν : posCone 𝔞 (rep β), qTerm 𝔞 k y (ν.1, rep β) := by
      rw [Complex.ofReal_tsum]
      exact tsum_congr fun ν => qTerm_norm 𝔞 k z _
    have hE : ∑' ν : posCone 𝔞 (rep β), qTerm 𝔞 k y (ν.1, rep β) =
        C⁻¹ * ∑' a : (latM 𝔞 : Set F), eisTerm k 0 y ((a : F), rep β) := by
      rw [hP.tsum_eq, ← mul_assoc, inv_mul_cancel₀ hCne, one_mul]
    have hnn : 0 ≤ ∑' ν : posCone 𝔞 (rep β), ‖qTerm 𝔞 k z (ν.1, rep β)‖ := tsum_nonneg fun _ => norm_nonneg _
    calc ∑' ν : posCone 𝔞 (rep β), ‖qTerm 𝔞 k z (ν.1, rep β)‖
        = ‖((∑' ν : posCone 𝔞 (rep β), ‖qTerm 𝔞 k z (ν.1, rep β)‖ : ℝ) : ℂ)‖ := by
          rw [Complex.norm_real, Real.norm_of_nonneg hnn]
      _ = ‖C‖⁻¹ * ‖∑' a : (latM 𝔞 : Set F), eisTerm k 0 y ((a : F), rep β)‖ := by
          rw [hT, hE, norm_mul, norm_inv]
      _ ≤ ‖C‖⁻¹ * ∑' a : (latM 𝔞 : Set F), ‖eisTerm k 0 y ((a : F), rep β)‖ := by
          gcongr
          exact norm_tsum_le_tsum_norm ((summable_norm_iff.2 (hlat y hy)).sigma_factor β)
  have hq : Summable (qClass 𝔞 𝔟 k z) := by
    have : Summable (qClass 𝔞 𝔟 k z ∘ e2) := hqsig.congr fun x => (he2 k z x).symm
    exact (e2.summable_iff).1 this
  refine ⟨hq, ?_⟩

  have hQ : HasSum (fun β : NzCls 𝔟 => ∑' ν : posCone 𝔞 (rep β), qTerm 𝔞 k z (ν.1, rep β)) (∑' c, qClass 𝔞 𝔟 k z c) := by
    have h1 : HasSum (fun x => qTerm 𝔞 k z (x.2.1, rep x.1) : (Σ β : NzCls 𝔟, posCone 𝔞 (rep β)) → ℂ) (∑' c, qClass 𝔞 𝔟 k z c) := by
      have := (e2.hasSum_iff (f := qClass 𝔞 𝔟 k z)).2 hq.hasSum
      exact this.congr_fun fun x => (he2 k z x).symm
    exact h1.sigma fun β => (hqsig.sigma_factor β).hasSum
  have hL1 : HasSum (fun x : (Σ _β : NzCls 𝔟, (latM 𝔞 : Set F)) => eisTerm k 0 z ((x.2 : F), rep x.1))
      (C * ∑' c, qClass 𝔞 𝔟 k z c) := by
    have hs := (hlat z hz).hasSum
    have hg := hs.sigma fun β => (GlobalTheory.EisPerB.lattice_sum_eq_cone_sum F hL 𝔞 k hk2 hke (rep β) (rep_ne_zero β) z hz).2
    rw [(hQ.mul_left C).unique hg]
    exact hs
  have : HasSum (fun x => eisClass 𝔞 𝔟 k 0 z (e1 x).1) (C * ∑' c, qClass 𝔞 𝔟 k z c) :=
    hL1.congr_fun fun x => he1 k hke 0 z x
  exact (e1.hasSum_iff (f := fun c : {c : Quotient (latRel 𝔞 𝔟) // c.out.1.2 ≠ 0} => eisClass 𝔞 𝔟 k 0 z c)).1 this

end GlobalTheory.EisNonConst
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeMetricGramMatrixLocalHolomorphicImPart
section
open Matrix Complex Filter Topology
open scoped ComplexOrder ContDiff ComplexConjugate
open GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram GlobalTheory.HermFrame

noncomputable section

namespace GlobalTheory.HodgeGramLocal

section General

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
  [IsScalarTower ℝ ℂ E]

theorem del_im_of_differentiableAt {F : E → ℂ} {z : E} (hF : DifferentiableAt ℂ F z) (ξ : E) :
    del (fun x => ((F x).im : ℂ)) z ξ = (1 / (2 * I)) * fderiv ℂ F z ξ := by
  have hR : DifferentiableAt ℝ F z := hF.restrictScalars ℝ
  have hc : DifferentiableAt ℝ (fun x => conj (F x)) z :=
    (conjCLE : ℂ →L[ℝ] ℂ).differentiableAt.comp z hR
  have e : (fun x => ((F x).im : ℂ)) = fun x => (1 / (2 * I)) • (F x - conj (F x)) := by
    funext x; rw [im_eq_sub_conj, smul_eq_mul]; ring
  rw [e, del_const_smul _ (hR.fun_sub hc), ContinuousLinearMap.smul_apply, del_sub hR hc,
    ContinuousLinearMap.sub_apply, del_conj, dbar_eq_zero hF, del_eq_fderiv hF]
  simp

theorem ddbar_im_of_contDiffAt {F : E → ℂ} {z : E} (hF : ContDiffAt ℂ 2 F z) :
    ddbar (fun x => ((F x).im : ℂ)) z = 0 := by
  have h := leviForm_re_eq_zero (f := fun x => -I * F x) (contDiffAt_const.mul hF)
  have e : (fun x => ((F x).im : ℂ)) = fun x => (((-I * F x).re : ℝ) : ℂ) := by
    funext x; simp
  rw [e]; exact h

theorem contDiffAt_im_of_analyticAt {F : E → ℂ} {z : E} (hF : AnalyticAt ℂ F z)
    {k : WithTop ℕ∞} : ContDiffAt ℝ k (fun x => ((F x).im : ℂ)) z :=
  (ofRealCLM.comp imCLM).contDiff.contDiffAt.comp z (hF.contDiffAt.restrict_scalars ℝ)

end General

def locLog (w₀ w : ℂ) : ℂ := Complex.log (w / w₀) + Complex.log w₀

theorem exp_locLog {w₀ w : ℂ} (h0 : w₀ ≠ 0) (h : w / w₀ ∈ slitPlane) :
    exp (locLog w₀ w) = w := by
  rw [locLog, exp_add, exp_log (slitPlane_ne_zero h), exp_log h0, div_mul_cancel₀ _ h0]

theorem hasDerivAt_locLog {w₀ w : ℂ} (h : w / w₀ ∈ slitPlane) :
    HasDerivAt (locLog w₀) (1 / w₀ / (w / w₀)) w :=
  (((hasDerivAt_id w).div_const w₀).clog h).add_const _

end GlobalTheory.HodgeGramLocal

namespace GlobalTheory.HodgeGramLocal

variable {n a g : ℕ}

def locEntry (ha : a ≤ n) (τ₀ : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ)
    (B : Fin a → Matrix (Fin g) (Fin g) ℤ) (z : Fin n → ℂ) (j k : Fin g) (x : Fin n → ℂ) : ℂ :=
  τ₀ x j k + ∑ i, locLog (z (Fin.castLE ha i)) (x (Fin.castLE ha i)) / (2 * Real.pi * I) *
    ((B i j k : ℤ) : ℂ)

theorem isOpen_polydisc (n : ℕ) : IsOpen (polydisc n 1) := by
  rw [show polydisc n 1 = ⋂ k, {z : Fin n → ℂ | ‖z k‖ < 1} by ext; simp [polydisc]]
  exact isOpen_iInter_of_finite fun k =>
    isOpen_lt (continuous_norm.comp (continuous_apply k)) continuous_const

theorem hodgeGram_local (n a g rk : ℕ) (ha : a ≤ n) (τ₀ : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ)
    (B : Fin a → Matrix (Fin g) (Fin g) ℤ) (hP : IsPeriodChart rk τ₀ B) :
    ∀ z ∈ punctured ha 1, MContDiffAt ∞ (hodgeGram ha τ₀ B) z ∧
      (∀ ξ, mdel (hodgeGram ha τ₀ B) z ξ = (1 / (2 * Complex.I)) •
        ((Matrix.of fun j k => fderiv ℂ (fun x => τ₀ x j k) z ξ) +
          ∑ i, (ξ (Fin.castLE ha i) / (2 * Real.pi * Complex.I * z (Fin.castLE ha i))) •
            ((B i).map (Int.cast : ℤ → ℝ)).map Complex.ofReal)) ∧
      ∀ ξ η, mddbar (hodgeGram ha τ₀ B) z ξ η = 0 := by
  intro z hz
  let V : Set (Fin n → ℂ) := {x | x ∈ polydisc n 1 ∧
    ∀ i : Fin a, x (Fin.castLE ha i) / z (Fin.castLE ha i) ∈ slitPlane}
  have hVo : IsOpen V := by
    have h2 : IsOpen {x : Fin n → ℂ |
        ∀ i : Fin a, x (Fin.castLE ha i) / z (Fin.castLE ha i) ∈ slitPlane} := by
      simp only [Set.setOf_forall]
      exact isOpen_iInter_of_finite fun i => isOpen_slitPlane.preimage (by fun_prop)
    exact (isOpen_polydisc n).inter h2
  have hzV : z ∈ V := ⟨hz.1, fun i => by rw [div_self (hz.2 i)]; exact one_mem_slitPlane⟩
  have hV : V ∈ 𝓝 z := hVo.mem_nhds hzV
  have hd : (2 * (Real.pi : ℂ) * I) ≠ 0 := by simp [Real.pi_ne_zero, I_ne_zero]

  have hterm : ∀ (j k : Fin g) (i : Fin a) (x : Fin n → ℂ), x ∈ V →
      HasFDerivAt (fun y : Fin n → ℂ => locLog (z (Fin.castLE ha i)) (y (Fin.castLE ha i)) /
        (2 * Real.pi * I) * ((B i j k : ℤ) : ℂ))
        ((1 / z (Fin.castLE ha i) / (x (Fin.castLE ha i) / z (Fin.castLE ha i)) /
          (2 * Real.pi * I) * ((B i j k : ℤ) : ℂ)) •
          ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n => ℂ) (Fin.castLE ha i)) x :=
    fun j k i x hx => by
      have h1 := ((hasDerivAt_locLog (hx.2 i)).div_const (2 * (Real.pi : ℂ) * I)).mul_const
        ((B i j k : ℤ) : ℂ)
      have h2 : HasFDerivAt (fun y : Fin n → ℂ => y (Fin.castLE ha i))
          (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n => ℂ) (Fin.castLE ha i)) x :=
        hasFDerivAt_apply _ _
      exact h1.comp_hasFDerivAt x h2
  have hτ : ∀ j k, ∀ x ∈ V, HasFDerivAt (fun y => τ₀ y j k) (fderiv ℂ (fun y => τ₀ y j k) x) x :=
    fun j k x hx => ((hP.holo j k).differentiableAt ((isOpen_polydisc n).mem_nhds hx.1)).hasFDerivAt
  have hloc : ∀ j k, ∀ x ∈ V, HasFDerivAt (locEntry ha τ₀ B z j k)
      (fderiv ℂ (fun y => τ₀ y j k) x + ∑ i, (1 / z (Fin.castLE ha i) /
        (x (Fin.castLE ha i) / z (Fin.castLE ha i)) / (2 * Real.pi * I) * ((B i j k : ℤ) : ℂ)) •
          ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n => ℂ) (Fin.castLE ha i)) x :=
    fun j k x hx => (hτ j k x hx).add (HasFDerivAt.fun_sum fun i _ => hterm j k i x hx)
  have hdiff : ∀ j k, DifferentiableOn ℂ (locEntry ha τ₀ B z j k) V := fun j k x hx =>
    (hloc j k x hx).differentiableAt.differentiableWithinAt
  have hF : ∀ j k, AnalyticAt ℂ (locEntry ha τ₀ B z j k) z := fun j k =>
    ReciprocityTheory.AnForm.Osgood.osgood n V _ hVo (hdiff j k) z hzV
  have heq : ∀ x ∈ V, hodgeGram ha τ₀ B x = of fun j k => ((locEntry ha τ₀ B z j k x).im : ℂ) := by
    intro x hx
    have hL : ∀ i, exp ((fun i => locLog (z (Fin.castLE ha i)) (x (Fin.castLE ha i))) i) =
        x (Fin.castLE ha i) := fun i => exp_locLog (hz.2 i) (hx.2 i)
    rw [hodgeGram, ← im_period ha τ₀ B x _ hL]
    ext j k
    simp [period, locEntry, Matrix.sum_apply]
  have hev : hodgeGram ha τ₀ B =ᶠ[𝓝 z] fun x => of fun j k => ((locEntry ha τ₀ B z j k x).im : ℂ) :=
    Filter.eventually_of_mem hV heq
  have hev' : ∀ j k, (fun x => hodgeGram ha τ₀ B x j k) =ᶠ[𝓝 z]
      fun x => ((locEntry ha τ₀ B z j k x).im : ℂ) := fun j k =>
    Filter.eventually_of_mem hV fun x hx => by
      show hodgeGram ha τ₀ B x j k = _
      rw [heq x hx]; rfl
  refine ⟨fun j k => (contDiffAt_im_of_analyticAt (hF j k)).congr_of_eventuallyEq (hev' j k),
    fun ξ => ?_, fun ξ η => ?_⟩
  · rw [mdel_congr hev]
    ext j k
    simp only [mdel_apply, of_apply]
    rw [del_im_of_differentiableAt (hF j k).differentiableAt, (hloc j k z hzV).fderiv]
    simp [Matrix.sum_apply, div_self (hz.2 _)]
    refine Finset.sum_congr rfl fun i _ => ?_
    field_simp
  · ext j k
    rw [mddbar_apply, ddbar_congr (hev' j k),
      ddbar_im_of_contDiffAt ((hF j k).contDiffAt)]
    rfl

end GlobalTheory.HodgeGramLocal
end
end

