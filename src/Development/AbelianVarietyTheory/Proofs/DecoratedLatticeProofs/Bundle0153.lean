module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0008
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ContinuousResTSymm
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ComplexEmbeddingHermitianQuadrupleSum
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0237
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0057
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0126
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0138
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0129
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0002
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaSourceAction
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0221
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0248
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsThetaFunctionDoublingSeesawOfStandardChar
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (resL resR)

noncomputable section

namespace GlobalTheory.Core.Rk.DeltaTheta

variable {D : D7}

def fstH (A B : HSp D) : WO (dblSp A) B →+ WO A B where
  toFun := resL A B
  map_zero' := rfl
  map_add' _ _ := rfl

def sndH (A B : HSp D) : WO (dblSp A) B →+ WO A B where
  toFun x := -resR A B x
  map_zero' := neg_zero
  map_add' x y := neg_add (resR A B x) (resR A B y)

theorem continuous_fstH (A B : HSp D) : Continuous (fstH A B) :=
  continuous_matrix fun i _ => continuous_id.matrix_elem i _

theorem continuous_sndH (A B : HSp D) : Continuous (sndH A B) := by
  obtain ⟨i1, -⟩ := GlobalTheory.MixModel.lattice_Mx D B.rank A.rank
  have h : Continuous (resR A B) := continuous_matrix fun i _ => continuous_id.matrix_elem i _
  exact h.neg

theorem map_fstH {R : Type} [CommRing R] (φ : AE D →+* R) (A B : HSp D) {u : WO (dblSp A) B} (h : u.map φ = 0) :
    (fstH A B u).map φ = 0 :=
  Matrix.ext fun i j => congrFun (congrFun h i) (finSumFinEquiv (Sum.inl j))

theorem map_sndH {R : Type} [CommRing R] (φ : AE D →+* R) (A B : HSp D) {u : WO (dblSp A) B} (h : u.map φ = 0) :
    (sndH A B u).map φ = 0 :=
  Matrix.ext fun i j => by
    have e : φ (u i (finSumFinEquiv (Sum.inr j))) = 0 := congrFun (congrFun h i) (finSumFinEquiv (Sum.inr j))
    change φ (-(u i (finSumFinEquiv (Sum.inr j)))) = 0
    rw [map_neg, e, neg_zero]

theorem hO_dbl (A B : HSp D) (x y : WO (dblSp A) B) :
    hO (dblSp A) B x y = hO A B (fstH A B x) (fstH A B y) - hO A B (sndH A B x) (sndH A B y) := by
  have hi : (dblSp A).gram⁻¹ = blkMat finSumFinEquiv A.gram⁻¹ (-A.gram⁻¹) := Matrix.inv_eq_left_inv (by
    rw [gram_hdbl, dblGram, blkMat_mul, neg_mul_neg, Matrix.nonsing_inv_mul _ (GlobalTheory.MixModel.gram_isUnit_det A), blkMat_one])
  simp only [hO, hi, ← finSumFinEquiv.sum_comp, Fintype.sum_sum_type, fstH, sndH, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    resR, Matrix.of_apply,
    blkMat, Matrix.submatrix_apply, Equiv.symm_apply_apply, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
    Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, Matrix.neg_apply, map_zero,
    map_neg, zero_mul, Finset.sum_const_zero, add_zero, zero_add, neg_mul, mul_neg, neg_neg,
    Finset.sum_neg_distrib, sub_eq_add_neg]
  rfl

theorem symplOH_dbl (A B : HSp D) (x y : WO (dblSp A) B) :
    symplOH (dblSp A) B x y =
      symplOH A B (fstH A B x) (fstH A B y) - symplOH A B (sndH A B x) (sndH A B y) := by
  simp only [GlobalTheory.MixModel.symplOH_eq, hO_dbl, map_sub]

theorem conj_char {G : Type} [AddCommGroup G] (ψ : AddChar G ℂ) (h : ∀ x, ‖ψ x‖ = 1) (x : G) :
    conj (ψ x) = ψ (-x) := by
  rw [AddChar.map_neg_eq_inv, Complex.inv_eq_conj (h x)]

theorem isThetaFunO_delta {ψ : AddChar (AF D.host.F) ℂ} (hn : ∀ x, ‖ψ x‖ = 1) {A B : HSp D} {f₁ f₂ : WO A B → ℂ}
    (h₁ : IsThetaFunO ψ A B f₁) (h₂ : IsThetaFunO ψ A B f₂) : IsThetaFunO ψ (dblSp A) B (delta A B f₁ f₂) := by
  have hd : delta A B f₁ f₂ = fun w => f₁ (fstH A B w) * conj (f₂ (sndH A B w)) := rfl
  rw [hd]
  refine ⟨fun γ w => ?_, ?_, ?_, fun k L hL h0 w => ?_⟩
  · have e₁ : fstH A B (ratW B (dblSp A) γ) =
        ratW B A (Matrix.of fun i j => γ i (finSumFinEquiv (Sum.inl j))) := rfl
    have e₂ : sndH A B (ratW B (dblSp A) γ) =
        ratW B A (Matrix.of fun i j => -γ i (finSumFinEquiv (Sum.inr j))) :=
      Matrix.ext fun i j => (map_neg (incA D) _).symm
    rw [map_add (f := _), map_add (f := _), symplOH_dbl, e₁, e₂, h₁.quasi, h₂.quasi, map_mul, conj_char ψ hn, neg_neg, neg_sub,
      sub_eq_add_neg, AddChar.map_add_eq_mul]
    ring
  · obtain ⟨U₁, hU₁, k₁⟩ := h₁.level
    obtain ⟨U₂, hU₂, k₂⟩ := h₂.level
    refine ⟨U₁.comap (fstH A B) ⊓ U₂.comap (sndH A B),
      (hU₁.preimage (continuous_fstH A B)).inter (hU₂.preimage (continuous_sndH A B)), fun u hu h0 => ?_⟩
    funext w
    have e₁ := congrFun (k₁ _ hu.1 (map_fstH _ _ _ h0)) (fstH A B w)
    have e₂ := congrFun (k₂ _ hu.2 (map_sndH _ _ _ h0)) (sndH A B w)
    simp only [heisO] at e₁ e₂ ⊢
    rw [← e₁, ← e₂, symplOH_dbl, sub_eq_add_neg, AddChar.map_add_eq_mul, map_add (f := _), map_add (f := _), map_mul, conj_char ψ hn]
    ring
  · exact (h₁.cont.comp (continuous_fstH A B)).mul
      (Complex.continuous_conj.comp (h₂.cont.comp (continuous_sndH A B)))
  · simp only [map_add (f := _)]
    exact (h₁.smooth k ((fstH A B).comp L) ((continuous_fstH A B).comp hL) (fun t => map_fstH _ _ _ (h0 t)) _).mul
      (Complex.conjCLE.contDiff.comp (h₂.smooth k ((sndH A B).comp L) ((continuous_sndH A B).comp hL)
        (fun t => map_sndH _ _ _ (h0 t)) _))

theorem main : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D), IsStdChar D ψ (-1) → ∀ f₁ f₂, IsThetaFunO ψ A B f₁ → IsThetaFunO ψ A B f₂ → IsThetaFunO ψ (dblSp A) B (delta A B f₁ f₂) :=
  fun _ _ _ _ hψ _ _ h₁ h₂ => isThetaFunO_delta hψ.1.2.1 h₁ h₂

end GlobalTheory.Core.Rk.DeltaTheta

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsThetaFunctionSuperpositionOrthogonalSlices
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.SuperposS

variable {D : D7}

theorem symplOH_zero_right {S T : HSp D} (x : WO S T) : symplOH S T x 0 = 0 := by
  simpa using GlobalTheory.OrientedHeis.symplOH_add_right (S := S) (T := T) x 0 0

theorem symplOH_zero_left {S T : HSp D} (x : WO S T) : symplOH S T 0 x = 0 := by
  simpa using GlobalTheory.OrientedHeis.symplOH_add_left (S := S) (T := T) 0 0 x

theorem psi_neg_mul (ψ : AddChar (AF D.host.F) ℂ) (s : AF D.host.F) : ψ (-s) * ψ s = 1 := by
  rw [← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one]

variable {S A B T : HSp D} (o : OrthDec S A B)

theorem symm_add (r u : WO A T) (y : WO B T) :
    (o.resS T).symm (u + r, y) = (o.resS T).symm (u, y) + (o.resS T).symm (r, 0) := by
  rw [← map_add (f := _)]; simp

theorem sympl_ext_right (r u : WO A T) (y : WO B T) :
    symplOH S T ((o.resS T).symm (u, y)) ((o.resS T).symm (r, 0)) = symplOH A T u r := by
  rw [o.symplOH_resS, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
  simp [symplOH_zero_right]

theorem sympl_ext_left (r u : WO A T) (y : WO B T) :
    symplOH S T ((o.resS T).symm (r, 0)) ((o.resS T).symm (u, y)) = symplOH A T r u := by
  rw [o.symplOH_resS, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
  simp [symplOH_zero_left]

def ext0 (T : HSp D) : WO A T →+ WO S T := (o.resS T).symm.toAddMonoidHom.comp (AddMonoidHom.inl _ _)

theorem matrixExtendByZero_apply (r : WO A T) : ext0 o T r = (o.resS T).symm (r, 0) := rfl

theorem continuous_wittExtendByZero : Continuous (ext0 o T) :=
  (o.continuous_resS_symm T).comp (continuous_id.prodMk continuous_const)

theorem matrixExtendByZero_map {R : Type} [Semiring R] (f : AE D →+* R) (r : WO A T) (h : r.map f = 0) : (ext0 o T r).map f = 0 := by
  rw [matrixExtendByZero_apply, o.resS_symm_apply, Matrix.zero_mul, add_zero, Matrix.map_mul, h, Matrix.zero_mul]

theorem homExtensionByZeroOrthDecomp_rational (γ : Matrix (Fin T.rank) (Fin A.rank) D.host.E) : ext0 o T (ratW T A γ) = ratW T S (γ * o.qA) := by
  rw [matrixExtendByZero_apply, o.resS_symm_apply, Matrix.zero_mul, add_zero, OrthDec.pA, ratW, ratW, rat, Matrix.map_mul]

end GlobalTheory.SuperposS

namespace GlobalTheory.SuperposS

theorem superpos_isTheta : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S A B T : HSp D) (o : OrthDec S A B) (F : WO S T → ℂ), IsThetaFunO ψ S T F → ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) (k : Ω → WO B T) (a : Ω → ℂ), Measurable k → Integrable a μ → IsThetaFunO ψ A T fun u => ∫ w, a w * F ((o.resS T).symm (u, k w)) ∂μ := by
  intro D ψ hψ S A B T o F hF Ω _ μ k a hk ha
  haveI : BorelSpace (WO B T) := ⟨rfl⟩
  haveI : BorelSpace (WO S T) := ⟨rfl⟩
  obtain ⟨C, hC⟩ := GlobalTheory.IsoMean.isThetaFunO_bounded S T ψ hψ F hF
  have hFm : ∀ u : WO A T, Measurable fun w => F ((o.resS T).symm (u, k w)) := fun u =>
    (hF.cont.comp ((o.continuous_resS_symm T).comp (continuous_const.prodMk continuous_id))).measurable.comp hk
  refine ⟨fun γ u => ?_, ?_, ?_, ?_⟩
  ·
    beta_reduce
    have e : ∀ w, a w * F ((o.resS T).symm (ratW T A γ + u, k w)) =
        ψ (-symplOH A T (ratW T A γ) u) * (a w * F ((o.resS T).symm (u, k w))) := by
      intro w
      rw [add_comm, symm_add, add_comm, ← matrixExtendByZero_apply, homExtensionByZeroOrthDecomp_rational, hF.quasi, ← homExtensionByZeroOrthDecomp_rational, matrixExtendByZero_apply, sympl_ext_left]
      ring
    simp_rw [e]
    exact integral_const_mul _ _
  ·
    obtain ⟨U, hU, hl⟩ := hF.level
    refine ⟨U.comap (ext0 o T), hU.preimage (continuous_wittExtendByZero o), fun u hu h0 => ?_⟩
    have hj := hl _ hu (matrixExtendByZero_map o _ u h0)
    funext v
    simp only [heisO]
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
    simp only []
    have e := congrFun hj ((o.resS T).symm (v, k w))
    simp only [heisO] at e
    rw [symm_add, ← matrixExtendByZero_apply]
    conv_rhs => rw [← e]
    rw [matrixExtendByZero_apply, sympl_ext_right]
    ring
  ·
    obtain ⟨-, -, i3, -⟩ := GlobalTheory.MixModel.lattice_Mx D T.rank A.rank
    haveI : FirstCountableTopology (WO A T) := @TopologicalSpace.SecondCountableTopology.to_firstCountableTopology _ _ i3
    refine continuous_of_dominated (bound := fun w => ‖a w‖ * C) (fun u => ?_) (fun u => ?_) (ha.norm.mul_const C) ?_
    · exact ha.aestronglyMeasurable.mul (hFm u).aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun w => ?_
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hC _) (norm_nonneg _)
    · refine Filter.Eventually.of_forall fun w => ?_
      exact continuous_const.mul (hF.cont.comp ((o.continuous_resS_symm T).comp (continuous_id.prodMk continuous_const)))
  ·
    intro n L hLc hL0 w
    obtain ⟨θ, hθ⟩ := GlobalTheory.Member.exists_isInfFam_family D
    obtain ⟨σ, h⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
    let L' : (Fin n → ℝ) →+ WO S T := (ext0 o T).comp L
    have hL'c : Continuous L' := (continuous_wittExtendByZero o).comp hLc
    have hL'0 : ∀ t, (L' t).map (finPart D) = 0 := fun t => matrixExtendByZero_map o _ (L t) (hL0 t)
    let M : (Fin n → ℝ) →L[ℝ] GlobalTheory.FockCompare.RW T S :=
      ((GlobalTheory.FockCompare.piW θ T S).comp L').toRealLinearMap ((GlobalTheory.FockCompare.continuous_pi' hθ T S).comp hL'c)
    let N : (Fin n → ℝ) →L[ℝ] GlobalTheory.FockCompare.RW T A :=
      ((GlobalTheory.FockCompare.piW θ T A).comp L).toRealLinearMap ((GlobalTheory.FockCompare.continuous_pi' hθ T A).comp hLc)
    have hM : ∀ t, L' t = GlobalTheory.FockCompare.iotaW σ T S (M t) := fun t => (h.iota_pi (hL'0 t)).symm
    have hN : ∀ t, L t = GlobalTheory.FockCompare.iotaW σ T A (N t) := fun t => (h.iota_pi (hL0 t)).symm
    let om := LinearMap.toContinuousLinearMap (GlobalTheory.OrientedHeis.omO A T (GlobalTheory.FockCompare.piW θ T A w))
    have key : ∀ t, (∫ x, a x * F ((o.resS T).symm (w + L t, k x)) ∂μ) =
        Complex.exp (-(Real.pi * Complex.I) * ((om (N (-t)) : ℝ) : ℂ)) *
          ∫ x, a x * heisO ψ S T (GlobalTheory.FockCompare.iotaW σ T S (M t)) F ((o.resS T).symm (w, k x)) ∂μ := by
      intro t
      have hph : ψ (-symplOH A T w (L t)) = Complex.exp (-(Real.pi * Complex.I) * ((om (N (-t)) : ℝ) : ℂ)) := by
        have e1 : -symplOH A T w (L t) = symplOH A T w (L (-t)) := by
          rw [map_neg]
          have := GlobalTheory.OrientedHeis.symplOH_add_right (S := A) (T := T) w (L t) (-L t)
          rw [add_neg_cancel, symplOH_zero_right] at this
          linear_combination this
        rw [e1, hN (-t), GlobalTheory.OrientedHeis.psi_symplOH h hψ]
        rfl
      rw [← hph, ← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      simp only [heisO]
      rw [← hM, symm_add, ← matrixExtendByZero_apply]
      show _ = _ * (a x * (ψ (symplOH S T ((o.resS T).symm (w, k x)) ((o.resS T).symm (L t, 0))) * _))
      rw [sympl_ext_right]
      change a x * F (_ + ext0 o T (L t)) = ψ (-symplOH A T w (L t)) * (a x * (ψ (symplOH A T w (L t)) * F (_ + ext0 o T (L t))))
      have := psi_neg_mul ψ (symplOH A T w (L t))
      linear_combination (-(a x * F ((o.resS T).symm (w, k x) + (ext0 o T) (L t)))) * this
    have hf : (fun t => (fun u => ∫ x, a x * F ((o.resS T).symm (u, k x)) ∂μ) (w + L t)) = fun t =>
        Complex.exp (-(Real.pi * Complex.I) * ((om (N (-t)) : ℝ) : ℂ)) *
          ∫ x, a x * heisO ψ S T (GlobalTheory.FockCompare.iotaW σ T S (M t)) F ((o.resS T).symm (w, k x)) ∂μ :=
      funext key
    rw [hf]
    refine ContDiff.mul ?_ ((_root_.GlobalTheory.SuperposSmooth.main D θ σ h ψ hψ S T F hF Ω μ _ a ?_ ha).comp M.contDiff)
    · exact Complex.contDiff_exp.comp (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp
        (om.contDiff.comp (N.contDiff.comp contDiff_neg))))
    · exact ((o.continuous_resS_symm T).comp (continuous_const.prodMk continuous_id)).measurable.comp hk

end GlobalTheory.SuperposS

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelPlacesDatumInvLeftMulTargetLevel
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChainOnto.LevelMove

section Mat

variable {κ : Type} [CommRing κ] {a b r t j : ℕ}

def IsTopB (r t : ℕ) (y : Matrix (Fin b) (Fin a) κ) (g : GL (Fin a) κ) : Prop :=
  LowZero a y ∧ g.val = topL a y ∧ g ∈ blockTri (blkOf r t)

theorem IsTopB.move (hab : a ≤ b) (ea : a = r + j * t) (eb : b = r + (j + 1) * t)
    {y : Matrix (Fin b) (Fin a) κ} {g : GL (Fin a) κ} {H : GL (Fin b) κ} (h : IsTopB r t y g)
    (hT : H ∈ blockTri (blkOf r t)) :
    IsTopB r t ((H⁻¹).val * y) ((upperLeftBlock hab H)⁻¹ * g) := by
  obtain ⟨h1, h2, h3⟩ := h
  have t2 := GlobalTheory.StepLaw.TypeDatum.mem_twoBlockTriangular_of_blockTriangular ea eb hT
  have tm := GlobalTheory.StepLaw.TypeDatum.top_mem hab t2 hT
  have hinv : upperLeftBlock hab H⁻¹ = (upperLeftBlock hab H)⁻¹ := extendOne_inv _ t2
  have e1 := GlobalTheory.StepLaw.TypeDatum.topL_mul hab (Subgroup.inv_mem _ t2) h1 1
  have e2 := GlobalTheory.StepLaw.TypeDatum.lowZero_mul (Subgroup.inv_mem _ t2) h1 1
  rw [Matrix.mul_one] at e1 e2
  rw [Matrix.mul_one] at e1
  refine ⟨e2, ?_, Subgroup.mul_mem _ (Subgroup.inv_mem _ tm) h3⟩
  rw [e1, hinv, ← h2, Units.val_mul]

theorem restrictBlock_inv_mul_block_triangular_move (hab : a ≤ b) (ha : r ≤ a) (hb : r ≤ b) (ea : a = r + j * t) (eb : b = r + (j + 1) * t)
    {g : GL (Fin a) κ} {H : GL (Fin b) κ} (hg : g ∈ blockTri (blkOf r t)) (hT : H ∈ blockTri (blkOf r t)) :
    upperLeftBlock ha ((upperLeftBlock hab H)⁻¹ * g) = (upperLeftBlock hb H)⁻¹ * upperLeftBlock ha g := by
  have t2 := GlobalTheory.StepLaw.TypeDatum.mem_twoBlockTriangular_of_blockTriangular ea eb hT
  have tm := GlobalTheory.StepLaw.TypeDatum.top_mem hab t2 hT
  have le := blockTri_blkOf_le (κ := κ) (n := a) r t
  have m2 : upperLeftBlock ha ((upperLeftBlock hab H)⁻¹ * g) = upperLeftBlock ha (upperLeftBlock hab H)⁻¹ * upperLeftBlock ha g :=
    extendMatrixByIdentityAlongIndices_mul _ (le (Subgroup.inv_mem _ tm)) (le hg)
  have m3 : upperLeftBlock ha (upperLeftBlock hab H)⁻¹ = (upperLeftBlock ha (upperLeftBlock hab H))⁻¹ := extendOne_inv _ (le tm)
  rw [m2, m3, GlobalTheory.StepLaw.TypeDatum.restrictTopBlock_restrictTopBlock hab ha hb t2 hT]

theorem char_move (hab : a ≤ b) (ea : a = r + j * t) (eb : b = r + (j + 1) * t) {A : Type} [CommGroup A]
    (χ : ℕ → κˣ →* A) {g : GL (Fin a) κ} {H : GL (Fin b) κ} (hg : g ∈ blockTri (blkOf r t))
    (hT : H ∈ blockTri (blkOf r t)) :
    (∏ c ∈ Finset.range j, χ (c + 1) (dBlk (blkOf r t) (c + 1) ((upperLeftBlock hab H)⁻¹ * g))) *
        (χ (j + 1) (Matrix.GeneralLinearGroup.det ((upperLeftBlock hab H)⁻¹ * g)))⁻¹ =
      (∏ c ∈ Finset.range (j + 1), χ (c + 1) (dBlk (blkOf r t) (c + 1) H))⁻¹ *
        χ (j + 1) (Matrix.GeneralLinearGroup.det H) *
        ((∏ c ∈ Finset.range j, χ (c + 1) (dBlk (blkOf r t) (c + 1) g)) *
          (χ (j + 1) (Matrix.GeneralLinearGroup.det g))⁻¹) := by
  have h := GlobalTheory.StepLaw.TypeDatum.char_law hab ea eb χ hg (Subgroup.one_mem _) hT
  have d1 : ∀ c, dBlk (blkOf r t) c (1 : GL (Fin a) κ) = 1 := fun c => blockDiagonalExtendByOnePrimeField_one _ _
  simp only [mul_one, d1, map_one, Finset.prod_const_one, one_mul] at h
  rw [inv_mul_eq_iff_eq_mul] at h
  rw [h]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

end Mat

section Dat

variable {D : D7} {a b r t k : ℕ} (ha : r ≤ a) (Pg : Finset (Pl D.host.E)) (P : LevelP Pg r ℂ)
  (χ : ℕ → ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (ξ χj : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ)
  (y : ∀ PP : Pl D.host.E, Matrix (Fin b) (Fin a) (kP PP))

theorem omegaG_of_top (g : ∀ PP : ↥Pg, GL (Fin a) (kP PP.1)) (hg : ∀ PP : ↥Pg, IsTopB r t (y PP.1) (g PP))
    (hm : (fun PP : ↥Pg => upperLeftBlock ha (g PP)) ∈ P.H) :
    omegaG (Lev.datY a r t k ha Pg ∅ P χ ξ Lev.Frm.B) χj y =
      ((P.chi ⟨_, hm⟩ * ∏ PP : ↥Pg, ((∏ c ∈ Finset.range k, χ (c + 1) PP.1 (dBlk (blkOf r t) (c + 1) (g PP))) *
        (χj PP.1 (Matrix.GeneralLinearGroup.det (g PP)))⁻¹) : ℂˣ) : ℂ) := by
  unfold omegaG
  split_ifs with h
  · have e : h.2.choose = g := funext fun PP =>
      Units.ext ((h.2.choose_spec.1 PP).trans (hg PP).2.1.symm)
    have e2 : (Lev.datY a r t k ha Pg ∅ P χ ξ Lev.Frm.B).P.chi
        ⟨fun PP => upperLeftBlock (Lev.datY a r t k ha Pg ∅ P χ ξ Lev.Frm.B).hr (h.2.choose PP), h.2.choose_spec.2.2⟩ =
        P.chi ⟨_, hm⟩ := by
      show P.chi _ = P.chi _
      congr 1
      exact Subtype.ext (funext fun PP => congrArg (fun x => upperLeftBlock ha x) (congrFun e PP))
    rw [e2]
    simp only [e, Finset.prod_mul_distrib, Units.val_mul, Units.coe_prod, Units.val_inv_eq_inv_val, mul_assoc]
    rfl
  · exfalso
    exact h ⟨fun PP hP => (hg ⟨PP, hP⟩).1, g, fun PP => (hg PP).2.1, fun PP => (hg PP).2.2, hm⟩

theorem omegaG_of_notTop (hg : ¬ ∃ g : ∀ PP : ↥Pg, GL (Fin a) (kP PP.1), (∀ PP : ↥Pg, IsTopB r t (y PP.1) (g PP)) ∧
      (fun PP : ↥Pg => upperLeftBlock ha (g PP)) ∈ P.H) :
    omegaG (Lev.datY a r t k ha Pg ∅ P χ ξ Lev.Frm.B) χj y = 0 := by
  unfold omegaG
  split_ifs with h
  · exfalso
    obtain ⟨h1, g, g1, g2, g3⟩ := h
    exact hg ⟨g, fun PP => ⟨h1 PP.1 PP.2, g1 PP, g2 PP⟩, g3⟩
  · rfl

end Dat

end GlobalTheory.ChainOnto.LevelMove

namespace GlobalTheory.ChainOnto

open LevelMove

theorem omegaG_levelP_move : ∀ (D : D7) (a b r t k : ℕ) (ha : r ≤ a) (hb : r ≤ b), a = r + k * t → b = r + (k + 1) * t → ∀ (Pg : Finset (Pl D.host.E)) (P : LevelP Pg r ℂ) (χ : ℕ → ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (H : ∀ PP : Pl D.host.E, GL (Fin b) (kP PP)), (∀ PP ∈ Pg, H PP ∈ blockTri (blkOf r t)) → ∀ hP : (fun PP : ↥Pg => upperLeftBlock hb (H PP.1)) ∈ P.H, ∀ y : ∀ PP : Pl D.host.E, Matrix (Fin b) (Fin a) (kP PP), omegaG (Lev.datY a r t k ha Pg ∅ P χ ξ Lev.Frm.B) (χ (k + 1)) (fun PP => ((H PP)⁻¹).val * y PP) = (((P.chi ⟨_, hP⟩ * ∏ PP ∈ Pg, ∏ i ∈ Finset.range (k + 1), χ (i + 1) PP (dBlk (blkOf r t) (i + 1) (H PP)))⁻¹ * ∏ PP ∈ Pg, χ (k + 1) PP (Matrix.GeneralLinearGroup.det (H PP)) : ℂˣ) : ℂ) * omegaG (Lev.datY a r t k ha Pg ∅ P χ ξ Lev.Frm.B) (χ (k + 1)) y := by
  intro D a b r t k ha hb ea eb Pg P χ ξ H hH hP y
  have hab : a ≤ b := by rw [ea, eb, add_mul]; omega
  by_cases h : ∃ g : ∀ PP : ↥Pg, GL (Fin a) (kP PP.1), (∀ PP : ↥Pg, IsTopB r t (y PP.1) (g PP)) ∧
      (fun PP : ↥Pg => upperLeftBlock ha (g PP)) ∈ P.H
  · obtain ⟨g, hg, hm⟩ := h
    have hg' : ∀ PP : ↥Pg, IsTopB r t (((H PP.1)⁻¹).val * y PP.1) ((upperLeftBlock hab (H PP.1))⁻¹ * g PP) :=
      fun PP => (hg PP).move hab ea eb (hH _ PP.2)
    have hr : (fun PP : ↥Pg => upperLeftBlock ha ((upperLeftBlock hab (H PP.1))⁻¹ * g PP)) =
        (fun PP : ↥Pg => upperLeftBlock hb (H PP.1))⁻¹ * (fun PP : ↥Pg => upperLeftBlock ha (g PP)) :=
      funext fun PP => restrictBlock_inv_mul_block_triangular_move hab ha hb ea eb (hg PP).2.2 (hH _ PP.2)
    have hm' : (fun PP : ↥Pg => upperLeftBlock ha ((upperLeftBlock hab (H PP.1))⁻¹ * g PP)) ∈ P.H := by
      rw [hr]; exact P.H.mul_mem (P.H.inv_mem hP) hm
    have hc : P.chi ⟨_, hm'⟩ = (P.chi ⟨_, hP⟩)⁻¹ * P.chi ⟨_, hm⟩ := by
      rw [← map_inv, ← map_mul]; congr 1; exact Subtype.ext hr
    have hx : ∀ PP : ↥Pg, (∏ c ∈ Finset.range k, χ (c + 1) PP.1 (dBlk (blkOf r t) (c + 1) ((upperLeftBlock hab (H PP.1))⁻¹ * g PP))) *
        (χ (k + 1) PP.1 (Matrix.GeneralLinearGroup.det ((upperLeftBlock hab (H PP.1))⁻¹ * g PP)))⁻¹ =
        (∏ c ∈ Finset.range (k + 1), χ (c + 1) PP.1 (dBlk (blkOf r t) (c + 1) (H PP.1)))⁻¹ *
          χ (k + 1) PP.1 (Matrix.GeneralLinearGroup.det (H PP.1)) *
          ((∏ c ∈ Finset.range k, χ (c + 1) PP.1 (dBlk (blkOf r t) (c + 1) (g PP))) *
            (χ (k + 1) PP.1 (Matrix.GeneralLinearGroup.det (g PP)))⁻¹) :=
      fun PP => char_move hab ea eb (fun c => χ c PP.1) (hg PP).2.2 (hH _ PP.2)
    rw [omegaG_of_top ha Pg P χ ξ _ (fun PP => ((H PP)⁻¹).val * y PP) _ hg' hm', omegaG_of_top ha Pg P χ ξ _ y g hg hm,
      hc, ← Units.val_mul]
    congr 1
    rw [Finset.prod_congr rfl fun PP _ => hx PP, Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_inv_distrib,
      ← Finset.prod_coe_sort Pg (fun PP => χ (k + 1) PP (Matrix.GeneralLinearGroup.det (H PP))),
      ← Finset.prod_coe_sort Pg (fun PP => ∏ i ∈ Finset.range (k + 1), χ (i + 1) PP (dBlk (blkOf r t) (i + 1) (H PP)))]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  · have h' : ¬ ∃ g : ∀ PP : ↥Pg, GL (Fin a) (kP PP.1),
        (∀ PP : ↥Pg, IsTopB r t ((fun PP => ((H PP)⁻¹).val * y PP) PP.1) (g PP)) ∧ (fun PP : ↥Pg => upperLeftBlock ha (g PP)) ∈ P.H := by
      rintro ⟨g, hg, hm⟩
      refine h ⟨fun PP => (upperLeftBlock hab (H PP.1)⁻¹)⁻¹ * g PP, fun PP => ?_, ?_⟩
      · have e : y PP.1 = ((H PP.1)⁻¹⁻¹).val * (((H PP.1)⁻¹).val * y PP.1) := by
          rw [← Matrix.mul_assoc, ← Units.val_mul, inv_inv, mul_inv_cancel, Units.val_one, Matrix.one_mul]
        rw [e]
        exact (hg PP).move hab ea eb (Subgroup.inv_mem _ (hH _ PP.2))
      · have hr : (fun PP : ↥Pg => upperLeftBlock ha ((upperLeftBlock hab (H PP.1)⁻¹)⁻¹ * g PP)) =
            (fun PP : ↥Pg => upperLeftBlock hb (H PP.1)⁻¹)⁻¹ * (fun PP : ↥Pg => upperLeftBlock ha (g PP)) :=
          funext fun PP => restrictBlock_inv_mul_block_triangular_move hab ha hb ea eb (hg PP).2.2 (Subgroup.inv_mem _ (hH _ PP.2))
        have i2 : (fun PP : ↥Pg => upperLeftBlock hb (H PP.1)⁻¹) = (fun PP : ↥Pg => upperLeftBlock hb (H PP.1))⁻¹ :=
          funext fun PP => extendOne_inv _ (blockTri_blkOf_le r t (hH _ PP.2))
        rw [hr, i2, inv_inv]
        exact P.H.mul_mem hP hm
    rw [omegaG_of_notTop ha Pg P χ ξ _ y h, omegaG_of_notTop ha Pg P χ ξ _ _ h', mul_zero]

end GlobalTheory.ChainOnto

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LowestKTypeMemDiscreteSeriesKFiniteVectors
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.LiftRows GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LowKFin

theorem lowT_mem_kfin (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (τ : D.what₂.Tau)
    (v : lowT M τ) : ((v : M.sm τ) : M.H τ) ∈ GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.kfin M τ := by
  have hv : ((v : M.sm τ) : M.H τ) ∈ lowKSub (M.ε τ) (M.lam τ) (M.σ τ) := v.2
  refine (sSup_le ?_ : lowKSub (M.ε τ) (M.lam τ) (M.σ τ) ≤ GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.kfin M τ) hv
  rintro T hT x hx
  exact Submodule.subset_span ⟨T, hT.1, hx, hT.2.1⟩

end GlobalTheory.LowKFin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MultTApplyRapidDec
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ChainOnto.MultRapid

theorem multT_apply_rapidDec : GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (θ : InfFam D), IsInfFam θ → ∀ (J : Set (GA D V)) (χ : GA D V → ℂ), ∀ F ∈ MultT θ M J χ, ∀ v : SmT M, IsAutFunSm θ V (F v) ∧ IsCuspFun V (F v) ∧ GlobalTheory.Grow.RapidDec V (F v) := by
  intro hP D V S M θ hθ J χ F hF v
  obtain ⟨ha, hc⟩ := GlobalTheory.PairLift.LowAllPf.multT_apply_smooth_cusp θ M J χ F hF v
  exact ⟨ha, hc, GlobalTheory.Grow.rapidDec_of_cuspForm hP hθ ha hc⟩

end GlobalTheory.ChainOnto.MultRapid
end
end

