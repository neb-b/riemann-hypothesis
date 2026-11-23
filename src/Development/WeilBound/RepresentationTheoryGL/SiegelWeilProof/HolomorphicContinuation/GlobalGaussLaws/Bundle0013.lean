module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslationInvariantFunctionalRestrict
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1382
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle0011
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle0012
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0196
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SchwartzBilinear.Bundle0002

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.AwayInA
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct SchwartzMap
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.AwayPf

variable {D : D7} {n : ℕ}

theorem evalPoly_congr {m : ℕ} (p : MvPolynomial (D.what₂.Tau × Fin m × Fin n × Bool) ℂ) (τ : D.what₂.Tau)
    (hp : ∀ v ∈ p.vars, v.1 ≠ τ) (z z' : D.what₂.Tau → Matrix (Fin m) (Fin n) ℂ) (h : ∀ τ', τ' ≠ τ → z τ' = z' τ') :
    evalPoly p z = evalPoly p z' := by
  unfold evalPoly
  change MvPolynomial.eval₂ (RingHom.id ℂ) _ p = MvPolynomial.eval₂ (RingHom.id ℂ) _ p
  apply MvPolynomial.eval₂_congr
  intro i c hi hc
  have hv : i ∈ p.vars := (MvPolynomial.mem_vars_iff_mem_support i).2 ⟨c, (MvPolynomial.mem_support_iff).2 hc, hi⟩
  have e := h i.1 (hp i hv)
  simp only [e]

theorem gAway_congr (V : HSp D) (l : D.what₂.Tau → ℝ) (s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (τ : D.what₂.Tau) (z z' : D.what₂.Tau → Matrix (Fin V.rank) (Fin n) ℂ) (h : ∀ τ', τ' ≠ τ → z τ' = z' τ') :
    gAway V l s τ z = gAway V l s τ z' := by
  classical
  unfold gAway
  congr 2
  refine Finset.sum_congr rfl (fun τ' hτ' => ?_)
  rw [h τ' (Finset.mem_filter.1 hτ').2]

theorem dep (θ : InfFam D) (V : HSp D) (l : D.what₂.Tau → ℝ) (s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (τ : D.what₂.Tau) {Ψ : Mx D V.rank n → ℂ} (hΨ : Ψ ∈ awayA θ V n l s τ) (x x' : Mx D V.rank n)
    (hx : ∀ τ', τ' ≠ τ → compAt θ τ' x = compAt θ τ' x') (hf : x.map (finPart D) = x'.map (finPart D)) :
    Ψ x = Ψ x' := by
  induction hΨ using Submodule.span_induction with
  | mem φ hφ =>
    obtain ⟨p, g, _, hp, rfl⟩ := hφ
    simp only
    have hf' : (fun i j => finPart D (x i j)) = (fun i j => finPart D (x' i j)) := hf
    rw [evalPoly_congr p τ hp _ _ hx, gAway_congr V l s τ _ _ hx, hf']
  | zero => rfl
  | add a b _ _ ha hb => simp only [Pi.add_apply, ha, hb]
  | smul c a _ ha => simp only [Pi.smul_apply, ha]

end PositivityTheory.Rg.Sw.Glob.AwayPf
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.DCalcB
section
noncomputable section

open Matrix MvPolynomial

namespace PositivityTheory.Rg.Sw.Glob

namespace DCalcBH

open DCalcH

variable {m n : ℕ}

theorem norm_vS (u : Fin m → Fin n → ℂ) (X : Fin n → ℝ) (s : ℝ) (a : Fin m) (j : Fin n) :
    ‖vS u X s a j‖ ^ 2 = ‖u a j‖ ^ 2 * Real.exp (s * X j) ^ 2 := by
  simp only [DCalcH.vS, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]

def nS (u : Fin m → Fin n → ℂ) (X : Fin n → ℝ) (s : ℝ) : ℝ := ∑ a, ∑ j, ‖u a j‖ ^ 2 * Real.exp (s * X j) ^ 2

theorem gs_vS (c : ℝ) (u : Fin m → Fin n → ℂ) (X : Fin n → ℝ) (s : ℝ) :
    gs c (vS u X s) = Complex.exp (((-(c * nS u X s)) : ℝ) : ℂ) := by
  simp only [gs, nS, norm_vS, Complex.ofReal_neg]

theorem nS_hasDeriv (u : Fin m → Fin n → ℂ) (X : Fin n → ℝ) (s : ℝ) :
    HasDerivAt (nS u X) (∑ a, ∑ j, 2 * X j * ‖vS u X s a j‖ ^ 2) s := by
  have h : ∀ a j, HasDerivAt (fun s => ‖u a j‖ ^ 2 * Real.exp (s * X j) ^ 2)
      (2 * X j * ‖vS u X s a j‖ ^ 2) s := by
    intro a j
    rw [norm_vS]
    have h1 : HasDerivAt (fun s : ℝ => s * X j) (X j) s := by
      simpa using (hasDerivAt_id s).mul_const (X j)
    refine (((h1.exp).pow 2).const_mul (‖u a j‖ ^ 2)).congr_deriv ?_
    rw [show (2 : ℕ) - 1 = 1 from rfl, pow_one]
    push_cast
    ring
  have h3 := HasDerivAt.sum (u := Finset.univ) fun a _ => HasDerivAt.sum (u := Finset.univ) fun j _ => h a j
  have e : nS u X = ∑ a, ∑ j, fun s : ℝ => ‖u a j‖ ^ 2 * Real.exp (s * X j) ^ 2 := by
    ext y
    simp [nS, Finset.sum_apply]
  rw [e]
  exact h3

theorem gs_hasDeriv (c : ℝ) (u : Fin m → Fin n → ℂ) (X : Fin n → ℝ) (s : ℝ) :
    HasDerivAt (fun s : ℝ => gs c (vS u X s))
      (gs c (vS u X s) * (-(2 * c : ℂ) * ∑ a, ∑ j, (X j : ℂ) * ((‖vS u X s a j‖ ^ 2 : ℝ) : ℂ))) s := by
  simp_rw [gs_vS]
  have h := ((nS_hasDeriv u X s).const_mul c).neg.ofReal_comp.cexp
  refine h.congr_deriv ?_
  congr 1
  push_cast
  rw [neg_mul]
  congr 1
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

def fF (c : ℝ) (X : Fin n → ℝ) (P : PX m n) (u : Fin m → Fin n → ℂ) (s : ℝ) : ℂ :=
  ((Real.exp (s * (m : ℝ) * ∑ j, X j) : ℝ) : ℂ) * fP c P (vS u X s)

theorem fF_hasDeriv (c : ℝ) (X : Fin n → ℝ) (P : PX m n) (u : Fin m → Fin n → ℂ) (s : ℝ) :
    HasDerivAt (fF c X P u) (fF c X (dil c X P) u s) s := by
  have he : HasDerivAt (fun s : ℝ => ((Real.exp (s * (m : ℝ) * ∑ j, X j) : ℝ) : ℂ))
      ((((m : ℝ) * ∑ j, X j : ℝ) : ℂ) * ((Real.exp (s * (m : ℝ) * ∑ j, X j) : ℝ) : ℂ)) s := by
    have := hasDerivAt_expX ((m : ℝ) * ∑ j, X j) s
    simp only [mul_assoc] at this ⊢
    exact this
  have h := he.mul ((eval_hasDeriv P u X s).mul (gs_hasDeriv c u X s))
  unfold fF fP
  have efun : (fun s : ℝ => ((Real.exp (s * (m : ℝ) * ∑ j, X j) : ℝ) : ℂ) * (evX P (vS u X s) * gs c (vS u X s))) =
      fun s => ((Real.exp (s * (m : ℝ) * ∑ j, X j) : ℝ) : ℂ) * (evX P (vS u X s) * gs c (vS u X s)) := rfl
  refine h.congr_deriv ?_
  simp only [Pi.mul_apply]
  rw [evX_dil]
  push_cast
  ring

theorem fF_iter (c : ℝ) (X : Fin n → ℝ) (u : Fin m → Fin n → ℂ) (r : ℕ) :
    iteratedDeriv r (fF c X 1 u) = fF c X ((dil c X ^ r) 1) u := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [iteratedDeriv_succ, ih]
    funext s
    rw [(fF_hasDeriv c X ((dil c X ^ r) 1) u s).deriv, pow_succ', Module.End.mul_apply]

end DCalcBH

end PositivityTheory.Rg.Sw.Glob
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.DecompAway
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.StdUnn Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob

open PositivityTheory.Rg.Sw.Glob.DecH

theorem decompAway : DecompAway := by
  intro D n θ τ ι hθ hι g
  obtain ⟨-, hιy⟩ := hι
  have hg : Formalism.UG.cT (sigR (AF D.host.F) D.sp.cm.sig) (mat g) * (Jst D n).map (incA D) * mat g =
      (Jst D n).map (incA D) := g.2
  set Y := compAt θ τ (mat g) with hYdef
  have hY : Yᴴ * reidx (JJ n) * Y = reidx (JJ n) := by
    have := congrArg (compAt θ τ) hg
    rwa [DA.compAt_mul, DA.compAt_mul, DA.compAt_conjT θ hθ, DA.compAt_Jst θ hθ] at this
  have hinv : compAt θ τ (mat g⁻¹) * Y = 1 := by
    rw [hYdef, ← DA.compAt_mul, ← DA.mat_mul, inv_mul_cancel, DA.mat_one, DA.compAt_one]
  have hYu : IsUnit Y.det := Matrix.isUnit_det_of_left_inverse hinv
  set M : M2 n := Y.submatrix finSumFinEquiv finSumFinEquiv with hMdef
  have hMY : reidx M = Y := by ext i j; simp [reidx, hMdef]
  have hMG : InG M := by
    have h2 : JJ n = (reidx (JJ n)).submatrix finSumFinEquiv finSumFinEquiv := by ext i j; simp [reidx]
    unfold InG
    rw [h2, hMdef, conjTranspose_submatrix, submatrix_mul_equiv, submatrix_mul_equiv, hY]
  have hMu : IsUnit M.det := by rw [hMdef, det_submatrix_equiv_self]; exact hYu
  set y := mkGR M hMu hMG with hydef
  have hιY : compAt θ τ (mat (ι y)) = Y := by rw [(hιy y).1, hydef, mR_mkGR, hMY]
  have htriv : compAt θ τ (mat (g * (ι y)⁻¹)) = 1 := by
    have h3 : compAt θ τ (mat (g * (ι y)⁻¹)) * Y = Y := by
      calc compAt θ τ (mat (g * (ι y)⁻¹)) * Y = compAt θ τ (mat (g * (ι y)⁻¹)) * compAt θ τ (mat (ι y)) := by rw [hιY]
        _ = compAt θ τ (mat (g * (ι y)⁻¹ * ι y)) := by rw [DA.mat_mul (g * (ι y)⁻¹) (ι y), DA.compAt_mul]
        _ = Y := by rw [inv_mul_cancel_right]
    calc compAt θ τ (mat (g * (ι y)⁻¹)) = compAt θ τ (mat (g * (ι y)⁻¹)) * Y * Y⁻¹ := by
          rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hYu, Matrix.mul_one]
      _ = 1 := by rw [h3, Matrix.mul_nonsing_inv _ hYu]
  refine ⟨g * (ι y)⁻¹, y, htriv, by group, ?_⟩
  generalize g * (ι y)⁻¹ = x at htriv ⊢
  intro y'
  apply DA.mat_inj
  rw [DA.mat_mul, DA.mat_mul]
  apply GlobalTheory.StabAtPlace.mx_ext hθ
  · rw [DA.finMap_mul, DA.finMap_mul, (hιy y').2.2, Matrix.mul_one, Matrix.one_mul]
  · intro τ'
    rw [DA.compAt_mul, DA.compAt_mul]
    by_cases h : τ' = τ
    · subst h
      rw [htriv, Matrix.mul_one, Matrix.one_mul]
    · rw [(hιy y').2.1 τ' h, Matrix.mul_one, Matrix.one_mul]

end PositivityTheory.Rg.Sw.Glob
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.DetNeOfPosDef
section
noncomputable section

open Matrix
open scoped ComplexOrder

namespace PositivityTheory.Rg.Sw.Glob

namespace DSiegH

variable {n : ℕ} {A B C D : Matrix (Fin n) (Fin n) ℂ}

theorem cross_form_linear_fractional_eq_conjTranspose_sub (h1 : Aᴴ * C = Cᴴ * A) (h2 : Bᴴ * D = Dᴴ * B) (h3 : Aᴴ * D - Cᴴ * B = 1) (h4 : Bᴴ * C - Dᴴ * A = -1)
    (W : Matrix (Fin n) (Fin n) ℂ) : (A * W + B)ᴴ * (C * W + D) - (C * W + D)ᴴ * (A * W + B) = Wᴴ - W := by
  have e : (A * W + B)ᴴ * (C * W + D) - (C * W + D)ᴴ * (A * W + B) =
      Wᴴ * (Aᴴ * C - Cᴴ * A) * W + Wᴴ * (Aᴴ * D - Cᴴ * B) + (Bᴴ * C - Dᴴ * A) * W + (Bᴴ * D - Dᴴ * B) := by
    simp only [conjTranspose_add, conjTranspose_mul]
    noncomm_ring
  rw [e, sub_eq_zero.2 h1, h3, h4, sub_eq_zero.2 h2]
  noncomm_ring

theorem det_ne (h1 : Aᴴ * C = Cᴴ * A) (h2 : Bᴴ * D = Dᴴ * B) (h3 : Aᴴ * D - Cᴴ * B = 1) (h4 : Bᴴ * C - Dᴴ * A = -1)
    (W : Matrix (Fin n) (Fin n) ℂ) (hW : ∀ v : Fin n → ℂ, v ≠ 0 → star v ⬝ᵥ ((Wᴴ - W) *ᵥ v) ≠ 0) :
    (C * W + D).det ≠ 0 := by
  intro h0
  obtain ⟨v, hv, hQv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
  have key := congrArg (fun M : Matrix (Fin n) (Fin n) ℂ => star v ⬝ᵥ (M *ᵥ v)) (cross_form_linear_fractional_eq_conjTranspose_sub h1 h2 h3 h4 W)
  simp only [Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, hQv, Matrix.mulVec_zero, zero_sub, dotProduct_neg] at key
  have e : star v ⬝ᵥ ((C * W + D)ᴴ *ᵥ ((A * W + B) *ᵥ v)) = 0 := by
    rw [Matrix.dotProduct_mulVec, ← Matrix.star_mulVec, hQv, star_zero, zero_dotProduct]
  rw [e, neg_zero] at key
  exact hW v hv (by rw [Matrix.sub_mulVec] at *; simpa [dotProduct_sub] using key.symm)

theorem im_formula (h1 : Aᴴ * C = Cᴴ * A) (h2 : Bᴴ * D = Dᴴ * B) (h3 : Aᴴ * D - Cᴴ * B = 1) (h4 : Bᴴ * C - Dᴴ * A = -1)
    (W : Matrix (Fin n) (Fin n) ℂ) (hQ : IsUnit (C * W + D).det) :
    (A * W + B) * (C * W + D)⁻¹ - ((A * W + B) * (C * W + D)⁻¹)ᴴ =
      ((C * W + D)⁻¹)ᴴ * (W - Wᴴ) * (C * W + D)⁻¹ := by
  set P := A * W + B
  set Q := C * W + D
  have hQQ : Q * Q⁻¹ = 1 := Matrix.mul_nonsing_inv _ hQ
  have hQh : (Q⁻¹)ᴴ * Qᴴ = 1 := by rw [← conjTranspose_mul, hQQ, conjTranspose_one]
  have hc : Pᴴ * Q - Qᴴ * P = Wᴴ - W := cross_form_linear_fractional_eq_conjTranspose_sub h1 h2 h3 h4 W
  have e1 : P * Q⁻¹ = (Q⁻¹)ᴴ * (Qᴴ * P) * Q⁻¹ := by rw [← Matrix.mul_assoc, hQh, Matrix.one_mul]
  have e2 : (P * Q⁻¹)ᴴ = (Q⁻¹)ᴴ * (Pᴴ * Q) * Q⁻¹ := by
    rw [conjTranspose_mul, Matrix.mul_assoc, Matrix.mul_assoc, hQQ, Matrix.mul_one]
  rw [e2, e1, ← Matrix.sub_mul, ← Matrix.mul_sub]
  congr 2
  have : Qᴴ * P - Pᴴ * Q = -(Pᴴ * Q - Qᴴ * P) := by abel
  rw [this, hc]
  abel

theorem siegel_of (h1 : Aᴴ * C = Cᴴ * A) (h2 : Bᴴ * D = Dᴴ * B) (h3 : Aᴴ * D - Cᴴ * B = 1) (h4 : Bᴴ * C - Dᴴ * A = -1)
    (W : Matrix (Fin n) (Fin n) ℂ) (hQ : IsUnit (C * W + D).det) (a : ℂ)
    (hW : (a • (W - Wᴴ)).PosDef) :
    (a • ((A * W + B) * (C * W + D)⁻¹ - ((A * W + B) * (C * W + D)⁻¹)ᴴ)).PosDef := by
  rw [im_formula h1 h2 h3 h4 W hQ]
  have e : a • (((C * W + D)⁻¹)ᴴ * (W - Wᴴ) * (C * W + D)⁻¹) =
      ((C * W + D)⁻¹)ᴴ * (a • (W - Wᴴ)) * (C * W + D)⁻¹ := by
    rw [Matrix.mul_smul, Matrix.smul_mul]
  rw [e]
  exact hW.conjTranspose_mul_mul_same
    (Matrix.mulVec_injective_iff_isUnit.2 ((Matrix.isUnit_iff_isUnit_det _).2 (Matrix.isUnit_nonsing_inv_det _ hQ)))

theorem posDef_diag_re (w : Fin n → ℂ) (hw : ∀ j, 0 < (w j).re) (a : ℂ)
    (s : ℂ) (hs : s = Complex.I ∨ s = -Complex.I) (hsa : a * s * 2 = 1) :
    (a • (s • diagonal w - (s • diagonal w)ᴴ)).PosDef := by
  have e : a • (s • diagonal w - (s • diagonal w)ᴴ) = diagonal fun j => ((w j).re : ℂ) := by
    rw [conjTranspose_smul, diagonal_conjTranspose]
    ext i j
    by_cases hij : i = j
    · subst hij
      have hst : star s = -s := by
        rcases hs with rfl | rfl <;> simp [Complex.conj_I]
      simp only [Matrix.smul_apply, Matrix.sub_apply, diagonal_apply_eq, smul_eq_mul, hst, Pi.star_apply]
      have hw' : (w i : ℂ) + star (w i) = 2 * ((w i).re : ℂ) := by
        rw [Complex.star_def, Complex.add_conj]; push_cast; ring
      calc a * (s * w i - -s * star (w i)) = a * s * ((w i : ℂ) + star (w i)) := by ring
        _ = a * s * (2 * ((w i).re : ℂ)) := by rw [hw']
        _ = ((w i).re : ℂ) := by linear_combination ((w i).re : ℂ) * hsa
    · simp [hij]
  rw [e, Matrix.posDef_diagonal_iff]
  intro j
  exact_mod_cast hw j

theorem det_ne_of_posDef (h1 : Aᴴ * C = Cᴴ * A) (h2 : Bᴴ * D = Dᴴ * B) (h3 : Aᴴ * D - Cᴴ * B = 1)
    (h4 : Bᴴ * C - Dᴴ * A = -1) (W : Matrix (Fin n) (Fin n) ℂ) (a : ℂ) (ha : a ≠ 0) (hX : (a • (W - Wᴴ)).PosDef) :
    (C * W + D).det ≠ 0 := by
  refine det_ne h1 h2 h3 h4 W fun v hv => ?_
  have e : Wᴴ - W = (-a⁻¹) • (a • (W - Wᴴ)) := by
    rw [smul_smul, neg_mul, inv_mul_cancel₀ ha, neg_one_smul, neg_sub]
  rw [e, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
  exact mul_ne_zero (neg_ne_zero.2 (inv_ne_zero ha)) (hX.dotProduct_mulVec_pos hv).ne'

end DSiegH

open DRealH DSiegH in
theorem dSieg : DSieg := by
  intro n y X z hz
  obtain ⟨h1, h2, h3, h4⟩ := blocks_of_inG (g := mR y) y.2
  set A := (mR y).toBlocks₁₁ with hA
  set B := (mR y).toBlocks₁₂ with hB
  set C := (mR y).toBlocks₂₁ with hC
  set D := (mR y).toBlocks₂₂ with hD
  set w : Fin n → ℂ := fun j => Complex.exp (2 * z * X j) with hwdef
  set E : Matrix (Fin n) (Fin n) ℂ := diagonal fun j => Complex.exp (z * X j) with hE
  set F : Matrix (Fin n) (Fin n) ℂ := diagonal fun j => Complex.exp (-(z * X j)) with hF
  have hwre : ∀ j, 0 < (w j).re := by
    intro j
    simp only [hwdef, Complex.exp_re]
    refine mul_pos (Real.exp_pos _) (Real.cos_pos_of_mem_Ioo ⟨?_, ?_⟩)
    all_goals
      have hj := hz j
      have him : (2 * z * (X j : ℂ)).im = 2 * (z.im * X j) := by simp [Complex.mul_im]; ring
      rw [him]
      rw [abs_lt] at hj
      linarith [hj.1, hj.2]
  have hM : mR y * aC X z = fromBlocks (A * E) (B * F) (C * E) (D * F) := by
    have e : mR y = fromBlocks A B C D := (fromBlocks_toBlocks _).symm
    rw [e]
    unfold aC
    rw [fromBlocks_multiply]
    simp only [Matrix.mul_zero, add_zero, zero_add, hE, hF]
  have hFu : IsUnit F.det := by
    rw [hF, det_diagonal]
    exact isUnit_iff_ne_zero.2 (Finset.prod_ne_zero_iff.2 fun j _ => Complex.exp_ne_zero _)
  have hFF : F * F⁻¹ = 1 := Matrix.mul_nonsing_inv _ hFu
  have hWF : ∀ s : ℂ, E * (s • 1) = (s • diagonal w) * F := by
    intro s
    rw [hE, hF, Matrix.smul_mul, diagonal_mul_diagonal, Matrix.mul_smul, Matrix.mul_one]
    congr 1
    congr 1
    funext j
    rw [hwdef, ← Complex.exp_add]
    congr 1; ring
  have hblk : ∀ s : ℂ, ((mR y * aC X z).toBlocks₂₁ * (s • 1) + (mR y * aC X z).toBlocks₂₂) = (C * (s • diagonal w) + D) * F ∧
      ((mR y * aC X z).toBlocks₁₁ * (s • 1) + (mR y * aC X z).toBlocks₁₂) = (A * (s • diagonal w) + B) * F := by
    intro s
    rw [hM]
    simp only [toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₁₂, toBlocks_fromBlocks₂₁, toBlocks_fromBlocks₂₂]
    constructor
    · rw [Matrix.mul_assoc, hWF, Matrix.add_mul, Matrix.mul_assoc]
    · rw [Matrix.mul_assoc, hWF, Matrix.add_mul, Matrix.mul_assoc]
  have hpt : ∀ s : ℂ, ptZ y X z s = (A * (s • diagonal w) + B) * (C * (s • diagonal w) + D)⁻¹ := by
    intro s
    simp only [ptZ]
    rw [(hblk s).1, (hblk s).2, Matrix.mul_inv_rev, ← Matrix.mul_assoc, Matrix.mul_assoc _ F, hFF, Matrix.mul_one]
  have hI2 : -(Complex.I / 2) ≠ 0 := by simp [Complex.I_ne_zero]
  have hI2' : Complex.I / 2 ≠ 0 := by simp [Complex.I_ne_zero]
  have hX1 : ((-(Complex.I / 2)) • ((Complex.I • diagonal w) - (Complex.I • diagonal w)ᴴ)).PosDef :=
    posDef_diag_re w hwre _ Complex.I (Or.inl rfl) (by ring_nf; rw [Complex.I_sq]; ring)
  have hX2 : ((Complex.I / 2) • (((-Complex.I) • diagonal w) - ((-Complex.I) • diagonal w)ᴴ)).PosDef :=
    posDef_diag_re w hwre _ (-Complex.I) (Or.inr rfl) (by ring_nf; rw [Complex.I_sq]; ring)
  have hQ1 := det_ne_of_posDef h1 h2 h3 h4 _ _ hI2 hX1
  have hQ2 := det_ne_of_posDef h1 h2 h3 h4 _ _ hI2' hX2
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold IsSiegel
    rw [hpt]
    exact siegel_of h1 h2 h3 h4 _ (isUnit_iff_ne_zero.2 hQ1) _ hX1
  · unfold IsSiegel
    rw [hpt, conjTranspose_conjTranspose]
    have e : ∀ Z : Matrix (Fin n) (Fin n) ℂ, (-(Complex.I / 2)) • (Zᴴ - Z) = (Complex.I / 2) • (Z - Zᴴ) := by
      intro Z; rw [← neg_sub, smul_neg, neg_smul, neg_neg]
    rw [e]
    exact siegel_of h1 h2 h3 h4 _ (isUnit_iff_ne_zero.2 hQ2) _ hX2
  · rw [(hblk _).1, det_mul]; exact mul_ne_zero hQ1 (isUnit_iff_ne_zero.1 hFu)
  · rw [(hblk _).1, det_mul]; exact mul_ne_zero hQ2 (isUnit_iff_ne_zero.1 hFu)

end PositivityTheory.Rg.Sw.Glob
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.GCSchA
section
noncomputable section

open scoped Matrix ComplexOrder
open Matrix

namespace PositivityTheory.Rg.Sw.Glob.GCSchH

variable {m n : ℕ}

theorem trace_gramB (Z : Matrix (Fin n) (Fin n) ℂ) (ε : Fin m → Bool) (b : Bool) (u : Fin m → Fin n → ℂ) :
    (Z * gramB ε b u).trace = ∑ a ∈ Finset.univ.filter (fun a => ε a = b), star (u a) ⬝ᵥ (Zᵀ *ᵥ u a) := by
  set S := Finset.univ.filter (fun a => ε a = b)
  have hG : ∀ i j, gramB ε b u j i = ∑ a ∈ S, star (u a j) * u a i := fun i j => GaussH.gramB_apply ε b u j i
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, hG, Finset.mul_sum, dotProduct, mulVec,
    Matrix.transpose_apply, Pi.star_apply]
  calc _ = ∑ i, ∑ a ∈ S, ∑ j, Z i j * (star (u a j) * u a i) := Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ a ∈ S, ∑ i, ∑ j, Z i j * (star (u a j) * u a i) := Finset.sum_comm
    _ = ∑ a ∈ S, ∑ j, ∑ i, Z i j * (star (u a j) * u a i) := Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = _ := Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring

theorem im_quad (W : Matrix (Fin n) (Fin n) ℂ) (y : Fin n → ℂ) :
    (star y ⬝ᵥ (W *ᵥ y)).im = (star y ⬝ᵥ (((-(Complex.I / 2)) • (W - Wᴴ)) *ᵥ y)).re := by
  have hs : star (star y ⬝ᵥ (W *ᵥ y)) = star y ⬝ᵥ (Wᴴ *ᵥ y) := by
    rw [Matrix.star_dotProduct, Matrix.star_mulVec, star_star, ← Matrix.dotProduct_mulVec]
  rw [Matrix.smul_mulVec, dotProduct_smul, Matrix.sub_mulVec, dotProduct_sub, ← hs]
  set s := star y ⬝ᵥ (W *ᵥ y)
  simp only [smul_eq_mul, Complex.mul_re, Complex.sub_re, Complex.sub_im, Complex.star_def, Complex.conj_re,
    Complex.conj_im, Complex.neg_re, Complex.neg_im, Complex.div_re, Complex.div_im, Complex.I_re, Complex.I_im]
  norm_num
  ring

theorem coercive_of_pos {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (Q : V →L[ℝ] V →L[ℝ] ℂ) (h : ∀ x, x ≠ 0 → 0 < (Q x x).re) : ∃ κ, 0 < κ ∧ ∀ x, κ * ‖x‖ ^ 2 ≤ (Q x x).re :=
  _root_.UpperTheory.Reformulated.B.P6.r24a.PositivityTheory.Rg.Sw.Glob.GCSchH.coercive_of_pos Q h

end PositivityTheory.Rg.Sw.Glob.GCSchH
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.GaussB
section
noncomputable section

open scoped Matrix ComplexOrder
open Matrix

namespace PositivityTheory.Rg.Sw.Glob.GaussH

variable {n : ℕ}

theorem inG_rel {g : M2 n} (hg : InG g) :
    g.toBlocks₁₁ᴴ * g.toBlocks₂₁ = g.toBlocks₂₁ᴴ * g.toBlocks₁₁ ∧
    g.toBlocks₁₂ᴴ * g.toBlocks₂₂ = g.toBlocks₂₂ᴴ * g.toBlocks₁₂ ∧
    g.toBlocks₁₁ᴴ * g.toBlocks₂₂ - g.toBlocks₂₁ᴴ * g.toBlocks₁₂ = 1 := by
  have h := hg
  unfold InG JJ at h
  rw [← Matrix.fromBlocks_toBlocks g, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply,
    Matrix.fromBlocks_multiply] at h
  simp only [Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one, Matrix.mul_neg, zero_add, add_zero, Matrix.neg_mul,
    Matrix.one_mul, Matrix.toBlocks_fromBlocks₁₁, Matrix.toBlocks_fromBlocks₁₂, Matrix.toBlocks_fromBlocks₂₁,
    Matrix.toBlocks_fromBlocks₂₂] at h
  obtain ⟨h1, h2, h3, h4⟩ := Matrix.fromBlocks_inj.1 h
  refine ⟨?_, ?_, ?_⟩
  · have := h1; rw [neg_add_eq_sub, sub_eq_zero] at this; exact this
  · have := h4; rw [neg_add_eq_sub, sub_eq_zero] at this; exact this
  · have := h2; rw [neg_add_eq_sub] at this; exact this

theorem inK_blocks {g : M2 n} (hg : InK g) : g.toBlocks₂₁ = -g.toBlocks₁₂ ∧ g.toBlocks₂₂ = g.toBlocks₁₁ := by
  obtain ⟨hG, hU⟩ := hg
  have hinv : g * gᴴ = 1 := mul_eq_one_comm.1 hU
  have hc : JJ n * g = g * JJ n := by
    calc JJ n * g = (g * gᴴ) * JJ n * g := by rw [hinv, Matrix.one_mul]
      _ = g * (gᴴ * JJ n * g) := by simp only [Matrix.mul_assoc]
      _ = g * JJ n := by rw [hG]
  unfold JJ at hc
  rw [← Matrix.fromBlocks_toBlocks g, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply] at hc
  simp only [Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one, Matrix.mul_neg, zero_add, add_zero, Matrix.neg_mul,
    Matrix.one_mul, Matrix.toBlocks_fromBlocks₁₁, Matrix.toBlocks_fromBlocks₁₂, Matrix.toBlocks_fromBlocks₂₁,
    Matrix.toBlocks_fromBlocks₂₂] at hc
  obtain ⟨h1, h2, h3, h4⟩ := Matrix.fromBlocks_inj.1 hc
  exact ⟨h1, h2⟩

end PositivityTheory.Rg.Sw.Glob.GaussH
end
end

