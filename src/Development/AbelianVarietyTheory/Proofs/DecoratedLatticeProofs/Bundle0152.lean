module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0221
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle0004
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

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralRealUnitaryHaarEqProdUpqHaar
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HaarReal
open Formalism.IndefR.Eqv

theorem continuous_psiT (D : D7) (τ : D.what₂.Tau) : Continuous (psiT D τ) := by
  have hsum : ∀ x : AE D, psiT D τ x = ∑ c, psiT D τ (algebraMap (AF D.host.F) (AE D) ((basAF D).repr x c)) *
      psiT D τ (basAF D c) := by
    intro x
    conv_lhs => rw [← (basAF D).sum_repr x]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Algebra.smul_def, map_mul]
  have hc : ∀ c, Continuous fun x : AE D => (basAF D).repr x c := fun c =>
    (continuous_apply c).comp (G5.tensCoordH (basE D) (AF D.host.F)).continuous
  have halg : Continuous fun a : AF D.host.F => psiT D τ (algebraMap (AF D.host.F) (AE D) a) := by
    have e : (fun a : AF D.host.F => psiT D τ (algebraMap (AF D.host.F) (AE D) a)) =
        fun a => thetaC D τ ((fstA D.host.F a) ⊗ₜ[D.host.F] (1 : D.host.E)) := by
      funext a
      simp only [psiT, RingHom.comp_apply, Algebra.TensorProduct.algebraMap_apply, infPart,
        AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul, map_one]
      rfl
    rw [e]
    exact ((isInfFam_thetaC D) τ).2.comp continuous_fst
  have hfun : (⇑(psiT D τ) : AE D → ℂ) = fun x => ∑ c, psiT D τ (algebraMap (AF D.host.F) (AE D)
      ((basAF D).repr x c)) * psiT D τ (basAF D c) := funext hsum
  rw [hfun]
  exact continuous_finsetSum _ fun c _ => (halg.comp (hc c)).mul continuous_const

end GlobalTheory.HaarReal

namespace GlobalTheory.HaarReal

open Formalism.IndefR.Eqv Formalism.MainNotions.StandardLattice

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S)

theorem fr_mul_inv (τ : D.what₂.Tau) : M.fr τ * (M.fr τ)⁻¹ = 1 :=
  Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp (M.fr_unit τ))

theorem inv_mul_fr (τ : D.what₂.Tau) : (M.fr τ)⁻¹ * M.fr τ = 1 :=
  Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp (M.fr_unit τ))

def toJ (τ : D.what₂.Tau) (g : Matrix (Fin V.rank) (Fin V.rank) ℂ) : Matrix (Fin V.rank) (Fin V.rank) ℂ :=
  M.fr τ * g * (M.fr τ)⁻¹

theorem ofFr_toJ (τ : D.what₂.Tau) (g : Matrix (Fin V.rank) (Fin V.rank) ℂ) :
    GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ofFr M τ (toJ M τ g) = g := by
  unfold GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ofFr toJ
  calc (M.fr τ)⁻¹ * (M.fr τ * g * (M.fr τ)⁻¹) * M.fr τ
      = ((M.fr τ)⁻¹ * M.fr τ) * g * ((M.fr τ)⁻¹ * M.fr τ) := by simp only [Matrix.mul_assoc]
    _ = g := by rw [inv_mul_fr, Matrix.one_mul, Matrix.mul_one]

theorem toJ_ofFr (τ : D.what₂.Tau) (u : Matrix (Fin V.rank) (Fin V.rank) ℂ) :
    toJ M τ (GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ofFr M τ u) = u := by
  unfold GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ofFr toJ
  calc M.fr τ * ((M.fr τ)⁻¹ * u * M.fr τ) * (M.fr τ)⁻¹
      = (M.fr τ * (M.fr τ)⁻¹) * u * (M.fr τ * (M.fr τ)⁻¹) := by simp only [Matrix.mul_assoc]
    _ = u := by rw [fr_mul_inv, Matrix.one_mul, Matrix.mul_one]

theorem toJ_mul (τ : D.what₂.Tau) (g h : Matrix (Fin V.rank) (Fin V.rank) ℂ) :
    toJ M τ (g * h) = toJ M τ g * toJ M τ h := by
  unfold toJ
  calc M.fr τ * (g * h) * (M.fr τ)⁻¹ = M.fr τ * g * ((M.fr τ)⁻¹ * M.fr τ) * h * (M.fr τ)⁻¹ := by
        rw [inv_mul_fr, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    _ = M.fr τ * g * (M.fr τ)⁻¹ * (M.fr τ * h * (M.fr τ)⁻¹) := by simp only [Matrix.mul_assoc]

theorem toJ_one (τ : D.what₂.Tau) : toJ M τ 1 = 1 := by
  unfold toJ; rw [Matrix.mul_one, fr_mul_inv]

theorem inUJ_toJ (τ : D.what₂.Tau) (g : Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (hg : gᴴ * gramAt D V τ * g = gramAt D V τ) : Formalism.REAL.inUJ (M.ε τ) (toJ M τ g) := by
  have hG := M.fr_gram τ
  have h1 : ((M.fr τ)⁻¹)ᴴ * (M.fr τ)ᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, fr_mul_inv, Matrix.conjTranspose_one]
  unfold Formalism.REAL.inUJ toJ
  calc (M.fr τ * g * (M.fr τ)⁻¹)ᴴ * Formalism.REAL.Jm (M.ε τ) * (M.fr τ * g * (M.fr τ)⁻¹)
      = ((M.fr τ)⁻¹)ᴴ * (gᴴ * ((M.fr τ)ᴴ * Formalism.REAL.Jm (M.ε τ) * M.fr τ) * g) * (M.fr τ)⁻¹ := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = ((M.fr τ)⁻¹)ᴴ * (M.fr τ)ᴴ * Formalism.REAL.Jm (M.ε τ) * (M.fr τ * (M.fr τ)⁻¹) := by
        rw [hG, hg, ← hG]; simp only [Matrix.mul_assoc]
    _ = Formalism.REAL.Jm (M.ε τ) := by rw [h1, fr_mul_inv, Matrix.one_mul, Matrix.mul_one]

theorem unit_ofFr (τ : D.what₂.Tau) (u : Matrix (Fin V.rank) (Fin V.rank) ℂ) (hu : Formalism.REAL.inUJ (M.ε τ) u) :
    (GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ofFr M τ u)ᴴ * gramAt D V τ * GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ofFr M τ u = gramAt D V τ := by
  have hG := M.fr_gram τ
  have h1 : ((M.fr τ)⁻¹)ᴴ * (M.fr τ)ᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, fr_mul_inv, Matrix.conjTranspose_one]
  unfold Formalism.REAL.inUJ at hu
  unfold GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ofFr
  rw [← hG]
  calc ((M.fr τ)⁻¹ * u * M.fr τ)ᴴ * ((M.fr τ)ᴴ * Formalism.REAL.Jm (M.ε τ) * M.fr τ) * ((M.fr τ)⁻¹ * u * M.fr τ)
      = (M.fr τ)ᴴ * uᴴ * (((M.fr τ)⁻¹)ᴴ * (M.fr τ)ᴴ) * Formalism.REAL.Jm (M.ε τ) * (M.fr τ * (M.fr τ)⁻¹) * u * M.fr τ := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = (M.fr τ)ᴴ * (uᴴ * Formalism.REAL.Jm (M.ε τ) * u) * M.fr τ := by
        rw [h1, fr_mul_inv, Matrix.mul_one, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    _ = (M.fr τ)ᴴ * Formalism.REAL.Jm (M.ε τ) * M.fr τ := by rw [hu]

theorem inUJ_umat {n : ℕ} {ε : Fin n → Bool} (u : Formalism.REAL.UJ ε) : Formalism.REAL.inUJ ε (umat u) := u.2

def uJ (τ : D.what₂.Tau) (g : Matrix (Fin V.rank) (Fin V.rank) ℂ) (hg : gᴴ * gramAt D V τ * g = gramAt D V τ) :
    Formalism.REAL.UJ (M.ε τ) :=
  ⟨⟨toJ M τ g, toJ M τ (ginv D V τ g), by rw [← toJ_mul, mul_ginv D V τ g hg, toJ_one],
    by rw [← toJ_mul, ginv_mul D V τ g hg, toJ_one]⟩, inUJ_toJ M τ g hg⟩

theorem infMat_mul (τ : D.what₂.Tau) (g h : GA D V) :
    infMat D.sp.cm.sig V.gram (thetaC D τ) (g * h) =
      infMat D.sp.cm.sig V.gram (thetaC D τ) g * infMat D.sp.cm.sig V.gram (thetaC D τ) h := by
  rw [infMat_thetaC, infMat_thetaC, infMat_thetaC, matA_mul, Matrix.map_mul]

def fwd (g : GinfC V) : ∀ τ, Formalism.REAL.UJ (M.ε τ) := fun τ =>
  uJ M τ (infMat D.sp.cm.sig V.gram (thetaC D τ) (g : GA D V)) (infMat_unitary' D V _ τ)

theorem unitFam_ofFr (us : ∀ τ, Formalism.REAL.UJ (M.ε τ)) :
    IsUnitFam D V fun τ => GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ofFr M τ (umat (us τ)) :=
  fun τ => unit_ofFr M τ _ (inUJ_umat (us τ))

def bwd (us : ∀ τ, Formalism.REAL.UJ (M.ε τ)) : GinfC V :=
  ⟨famH D V (fun τ => GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ofFr M τ (umat (us τ))) (unitFam_ofFr M us),
    famH_mem_GinfC D V _ _⟩

theorem continuous_matA : Continuous (matA D V) :=
  Units.continuous_val.comp continuous_subtype_val

theorem continuous_famM : Continuous (famM D V) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  exact (continuous_glueA D _).comp ((continuous_splitInv D).comp (continuous_pi fun τ =>
    (continuous_apply j).comp ((continuous_apply i).comp (continuous_apply τ))))

theorem continuous_fwd : Continuous (fwd M) := by
  refine continuous_pi fun τ => Continuous.subtype_mk (Units.continuous_iff.2 ⟨?_, ?_⟩) _
  · refine (((continuous_const (y := M.fr τ)).matrix_mul (((continuous_matA).comp continuous_subtype_val).matrix_map
      (continuous_psiT D τ))).matrix_mul (continuous_const (y := (M.fr τ)⁻¹))).congr fun g => ?_
    show M.fr τ * _ * _ = toJ M τ (infMat D.sp.cm.sig V.gram (thetaC D τ) (g : GA D V))
    rw [toJ, infMat_thetaC]; rfl
  · have c0 : Continuous fun g : GinfC V => (matA D V (g : GA D V)).map (psiT D τ) :=
      ((continuous_matA).comp continuous_subtype_val).matrix_map (continuous_psiT D τ)
    refine (((continuous_const (y := M.fr τ)).matrix_mul (((continuous_const (y := (gramAt D V τ)⁻¹)).matrix_mul
      c0.matrix_conjTranspose).matrix_mul (continuous_const (y := gramAt D V τ)))).matrix_mul
      (continuous_const (y := (M.fr τ)⁻¹))).congr fun g => ?_
    show M.fr τ * _ * _ = toJ M τ (ginv D V τ (infMat D.sp.cm.sig V.gram (thetaC D τ) (g : GA D V)))
    rw [toJ, ginv, infMat_thetaC]

theorem continuous_bwd : Continuous (bwd M) := by
  have hu : ∀ τ, Continuous fun us : (∀ τ, Formalism.REAL.UJ (M.ε τ)) => umat (us τ) := fun τ =>
    (Units.continuous_val.comp continuous_subtype_val).comp (continuous_apply τ)
  have hg : Continuous fun us : (∀ τ, Formalism.REAL.UJ (M.ε τ)) => fun τ => GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ofFr M τ (umat (us τ)) :=
    continuous_pi fun τ => (continuous_const.matrix_mul (hu τ)).matrix_mul continuous_const
  refine Continuous.subtype_mk (continuous_induced_rng.2 (Units.continuous_iff.2 ⟨?_, ?_⟩)) _
  · exact continuous_famM.comp hg
  · have hi : Continuous fun us : (∀ τ, Formalism.REAL.UJ (M.ε τ)) =>
        fun τ => ginv D V τ (GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ofFr M τ (umat (us τ))) :=
      continuous_pi fun τ => (continuous_const.matrix_mul ((continuous_apply τ).comp hg).matrix_conjTranspose).matrix_mul
        continuous_const
    exact continuous_famM.comp hi

def eqv : GinfC V ≃ₜ* (∀ τ, Formalism.REAL.UJ (M.ε τ)) where
  toFun := fwd M
  invFun := bwd M
  left_inv g := by
    apply Subtype.ext
    apply (famH_unique D V _ (unitFam_ofFr M (fwd M g)) (g : GA D V) g.2 ?_).symm
    intro τ
    change _ = GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ofFr M τ (toJ M τ _)
    rw [ofFr_toJ]
  right_inv us := by
    funext τ
    refine Subtype.ext (Units.ext ?_)
    show toJ M τ (infMat D.sp.cm.sig V.gram (thetaC D τ) (famH D V _ (unitFam_ofFr M us))) = umat (us τ)
    rw [infMat_famH, toJ_ofFr]
  map_mul' g h := by
    funext τ
    apply Subtype.ext
    apply Units.ext
    show toJ M τ (infMat D.sp.cm.sig V.gram (thetaC D τ) ((g : GA D V) * h)) =
      toJ M τ (infMat D.sp.cm.sig V.gram (thetaC D τ) g) * toJ M τ (infMat D.sp.cm.sig V.gram (thetaC D τ) h)
    rw [infMat_mul, toJ_mul]
  continuous_toFun := continuous_fwd M
  continuous_invFun := continuous_bwd M

theorem ofFr_eqv (g : GinfC V) (τ : D.what₂.Tau) :
    GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ofFr M τ (umat (eqv M g τ)) = infMat D.sp.cm.sig V.gram (thetaC D τ) (g : GA D V) :=
  ofFr_toJ M τ _

end GlobalTheory.HaarReal

namespace GlobalTheory.HaarReal

open Formalism.IndefR.Eqv Formalism.MainNotions.StandardLattice

theorem integral_prod_eq : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (θ : InfFam D), IsInfFam θ → ∀ (mR : Measure (GinfC V)) (μ : ∀ τ, Measure (Formalism.REAL.UJ (M.ε τ))), mR.IsHaarMeasure → (∀ τ, (μ τ).IsHaarMeasure) → ∃ c : ℝ, 0 < c ∧ ∀ F : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ → ℂ, (∀ τ, Integrable (fun u : Formalism.REAL.UJ (M.ε τ) => F τ (GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ofFr M τ (umat u))) (μ τ)) → Integrable (fun g : GinfC V => ∏ τ, F τ (Formalism.MainNotions.StandardLattice.infMat D.sp.cm.sig V.gram (θ τ) (g : GA D V))) mR ∧ ∫ g : GinfC V, ∏ τ, F τ (Formalism.MainNotions.StandardLattice.infMat D.sp.cm.sig V.gram (θ τ) (g : GA D V)) ∂mR = (c : ℂ) * ∏ τ, ∫ u : Formalism.REAL.UJ (M.ε τ), F τ (GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ofFr M τ (umat u)) ∂μ τ := by
  intro D V S M θ hθ mR μ hmR hμ
  obtain rfl : θ = thetaC D := eq_thetaC D hθ
  set e := eqv M
  haveI : (mR.map e).IsHaarMeasure := e.isHaarMeasure_map mR
  set c := (mR.map e).haarScalarFactor (Measure.pi μ)
  have hc : 0 < c := Measure.haarScalarFactor_pos_of_isHaarMeasure _ _
  have key : mR.map e = c • Measure.pi μ := Measure.isMulLeftInvariant_eq_smul _ _
  set E : GinfC V ≃ᵐ (∀ τ, Formalism.REAL.UJ (M.ε τ)) := e.toHomeomorph.toMeasurableEquiv
  have hmap : mR.map E = c • Measure.pi μ := key
  refine ⟨c, hc, fun F hF => ?_⟩
  set f' : (∀ τ, Formalism.REAL.UJ (M.ε τ)) → ℂ := fun us => ∏ τ, F τ (GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ofFr M τ (umat (us τ)))
  have hf : (fun g : GinfC V => ∏ τ, F τ (infMat D.sp.cm.sig V.gram (thetaC D τ) (g : GA D V))) = f' ∘ E := by
    funext g
    simp only [f', Function.comp_apply]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [← ofFr_eqv M g τ]
    rfl
  have hpi : Integrable f' (Measure.pi μ) :=
    Integrable.fintype_prod_dep (f := fun τ (u : Formalism.REAL.UJ (M.ε τ)) => F τ (GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ofFr M τ (umat u))) hF
  rw [hf]
  refine ⟨(integrable_map_equiv E f').mp (by rw [hmap]; exact hpi.smul_measure_nnreal), ?_⟩
  show ∫ x, f' (E x) ∂mR = _
  rw [← integral_map_equiv E f', hmap, integral_smul_nnreal_measure,
    integral_fintype_prod_eq_prod (f := fun τ (u : Formalism.REAL.UJ (M.ε τ)) => F τ (GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ofFr M τ (umat u)))]
  rw [NNReal.smul_def, Complex.real_smul]

end GlobalTheory.HaarReal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsThetaFunSuperpositionTargetOrthSummand
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.SuperposT

theorem symplOH_zero_left {D : D7} {S T : HSp D} (y : WO S T) : symplOH S T 0 y = 0 := by
  have h := GlobalTheory.OrientedHeis.symplOH_add_left (S := S) (T := T) 0 0 y
  rw [add_zero] at h
  linear_combination -h

theorem symplOH_zero_right {D : D7} {S T : HSp D} (x : WO S T) : symplOH S T x 0 = 0 := by
  have h := GlobalTheory.OrientedHeis.symplOH_add_right (S := S) (T := T) x 0 0
  rw [add_zero] at h
  linear_combination -h

theorem psi_neg_mul {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (s : AF D.host.F) : ψ (-s) * ψ s = 1 := by
  rw [← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one]

theorem symplOH_resT_symm {D : D7} {T A B : HSp D} (o : OrthDec T A B) (S : HSp D) (u u' : WO S A) (v v' : WO S B) :
    symplOH S T ((o.resT S).symm (u, v)) ((o.resT S).symm (u', v')) = symplOH S A u u' + symplOH S B v v' := by
  rw [o.symplOH_resT, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]

theorem superpos_target : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (T A B S : HSp D) (o : OrthDec T A B) (F : WO S T → ℂ), IsThetaFunO ψ S T F → ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) (k : Ω → WO S B) (a : Ω → ℂ), Measurable k → Integrable a μ → IsThetaFunO ψ S A fun u => ∫ w, a w * F ((o.resT S).symm (u, k w)) ∂μ := by
  intro D ψ hψ T A B S o F hF Ω _ μ k a hk ha
  haveI : BorelSpace (Mx D B.rank S.rank) := ⟨rfl⟩
  haveI : BorelSpace (WO S T) := ⟨rfl⟩
  obtain ⟨-, -, i3, -⟩ := GlobalTheory.MixModel.lattice_Mx D A.rank S.rank
  haveI : FirstCountableTopology (WO S A) := @TopologicalSpace.SecondCountableTopology.to_firstCountableTopology _ _ i3
  obtain ⟨C, hC⟩ := GlobalTheory.IsoMean.isThetaFunO_bounded S T ψ hψ F hF
  set e := o.resT S with he
  have hsplit : ∀ (u u' : WO S A) (v : WO S B), e.symm (u + u', v) = e.symm (u, v) + e.symm (u', 0) := by
    intro u u' v
    rw [← map_add (f := _), Prod.mk_add_mk, add_zero]
  have hmeas : ∀ (F' : WO S T → ℂ), Continuous F' → ∀ (c : WO S T) (u : WO S A),
      AEStronglyMeasurable (fun ξ => F' (e.symm (u, k ξ) + c)) μ := by
    intro F' hF' c u
    exact ((hF'.comp (((o.continuous_resT_symm S).comp (continuous_const.prodMk continuous_id)).add
      continuous_const)).measurable.comp hk).aestronglyMeasurable

  let φ : WO S A →+ WO S T := e.symm.toAddMonoidHom.comp (AddMonoidHom.inl (WO S A) (WO S B))
  have hφ : ∀ u, φ u = e.symm (u, 0) := fun u => rfl
  have hφc : Continuous φ := (o.continuous_resT_symm S).comp (continuous_id.prodMk continuous_const)
  have hφmap : ∀ (R : Type) [CommRing R] (f : Formalism.L2.Theta.AE D →+* R) (u : WO S A), u.map f = 0 → (φ u).map f = 0 := by
    intro R _ f u hu
    rw [hφ, he, o.resT_symm_apply, Matrix.mul_zero, add_zero, Matrix.map_mul, hu, Matrix.mul_zero]
  refine ⟨fun γ u => ?_, ?_, ?_, ?_⟩
  ·
    have hr : e.symm (ratW A S γ, 0) = ratW T S (o.iA * γ) := by
      rw [he, o.resT_symm_apply, Matrix.mul_zero, add_zero]
      exact (rat_mul _ _).symm
    have h1 : ∀ ξ, F (e.symm (ratW A S γ + u, k ξ)) =
        ψ (-(symplOH S A (ratW A S γ) u)) * F (e.symm (u, k ξ)) := by
      intro ξ
      rw [add_comm (ratW A S γ) u, hsplit, add_comm, hr, hF.quasi, ← hr, symplOH_resT_symm, symplOH_zero_left, add_zero]
    simp_rw [h1]
    rw [← integral_const_mul]
    congr 1
    funext ξ
    ring
  ·
    obtain ⟨U, hU, hl⟩ := hF.level
    refine ⟨U.comap φ, hU.preimage hφc, fun u hu h0 => ?_⟩
    have hl' := hl (φ u) hu (hφmap _ _ u h0)
    funext w
    simp only [heisO]
    rw [← integral_const_mul]
    congr 1
    funext ξ
    have h2 := congrFun hl' (e.symm (w, k ξ))
    simp only [heisO] at h2
    rw [hφ, symplOH_resT_symm, symplOH_zero_right, add_zero, ← hsplit] at h2
    rw [mul_left_comm, h2]
  ·
    refine continuous_of_dominated (bound := fun ξ => ‖a ξ‖ * C) (fun u => ?_) (fun u => ?_) (ha.norm.mul_const C) ?_
    · have := hmeas F hF.cont 0 u
      simp only [add_zero] at this
      exact ha.aestronglyMeasurable.mul this
    · exact Filter.Eventually.of_forall fun ξ => by
        rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hC _) (norm_nonneg _)
    · exact Filter.Eventually.of_forall fun ξ => continuous_const.mul
        (hF.cont.comp ((o.continuous_resT_symm S).comp (continuous_id.prodMk continuous_const)))
  ·
    intro n L hLc hL0 w
    obtain ⟨θ, hθ⟩ := GlobalTheory.Member.exists_isInfFam_family D
    obtain ⟨σ, h⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
    let L' : (Fin n → ℝ) →+ WO S T := φ.comp L
    have hL'c : Continuous L' := hφc.comp hLc
    have hL'0 : ∀ t, (L' t).map (finPart D) = 0 := fun t => hφmap _ _ _ (hL0 t)
    let M : (Fin n → ℝ) →L[ℝ] GlobalTheory.FockCompare.RW T S :=
      ((GlobalTheory.FockCompare.piW θ T S).comp L').toRealLinearMap ((GlobalTheory.FockCompare.continuous_pi' hθ T S).comp hL'c)
    let N : (Fin n → ℝ) →L[ℝ] GlobalTheory.FockCompare.RW A S :=
      ((GlobalTheory.FockCompare.piW θ A S).comp L).toRealLinearMap ((GlobalTheory.FockCompare.continuous_pi' hθ A S).comp hLc)
    have hM : ∀ t, L' t = GlobalTheory.FockCompare.iotaW σ T S (M t) := fun t => (h.iota_pi (hL'0 t)).symm
    have hN : ∀ t, L t = GlobalTheory.FockCompare.iotaW σ A S (N t) := fun t => (h.iota_pi (hL0 t)).symm
    let om := LinearMap.toContinuousLinearMap (GlobalTheory.OrientedHeis.omO S A (GlobalTheory.FockCompare.piW θ A S w))
    have key : ∀ t, (∫ x, a x * F (e.symm (w + L t, k x)) ∂μ) =
        Complex.exp (-(Real.pi * Complex.I) * ((om (N (-t)) : ℝ) : ℂ)) *
          ∫ x, a x * heisO ψ S T (GlobalTheory.FockCompare.iotaW σ T S (M t)) F (e.symm (w, k x)) ∂μ := by
      intro t
      have hph : ψ (-symplOH S A w (L t)) = Complex.exp (-(Real.pi * Complex.I) * ((om (N (-t)) : ℝ) : ℂ)) := by
        have e1 : -symplOH S A w (L t) = symplOH S A w (L (-t)) := by
          rw [map_neg]
          have := GlobalTheory.OrientedHeis.symplOH_add_right (S := S) (T := A) w (L t) (-L t)
          rw [add_neg_cancel, symplOH_zero_right] at this
          linear_combination this
        rw [e1, hN (-t), GlobalTheory.OrientedHeis.psi_symplOH h hψ]
        rfl
      rw [← hph, ← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      simp only [heisO]
      rw [← hM, hsplit]
      have hs : symplOH S T (e.symm (w, k x)) (L' t) = symplOH S A w (L t) := by
        show symplOH S T (e.symm (w, k x)) (e.symm (L t, 0)) = _
        rw [symplOH_resT_symm, symplOH_zero_right, add_zero]
      rw [hs]
      change a x * F (_ + L' t) = ψ (-symplOH S A w (L t)) * (a x * (ψ (symplOH S A w (L t)) * F (_ + L' t)))
      have := psi_neg_mul ψ (symplOH S A w (L t))
      linear_combination (-(a x * F (e.symm (w, k x) + L' t))) * this
    have hf : (fun t => (fun u => ∫ x, a x * F (e.symm (u, k x)) ∂μ) (w + L t)) = fun t =>
        Complex.exp (-(Real.pi * Complex.I) * ((om (N (-t)) : ℝ) : ℂ)) *
          ∫ x, a x * heisO ψ S T (GlobalTheory.FockCompare.iotaW σ T S (M t)) F (e.symm (w, k x)) ∂μ :=
      funext key
    rw [hf]
    refine ContDiff.mul ?_ ((GlobalTheory.SuperposSmooth.main D θ σ h ψ hψ S T F hF Ω μ _ a ?_ ha).comp M.contDiff)
    · exact Complex.contDiff_exp.comp (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp
        (om.contDiff.comp (N.contDiff.comp contDiff_neg))))
    · exact ((o.continuous_resT_symm S).comp (continuous_const.prodMk continuous_id)).measurable.comp hk

end GlobalTheory.SuperposT

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelPlacesDatumMulRightSourceLevel
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ChainOnto.RightMove

variable {D : D7}

theorem topL_mul {κ : Type} [CommRing κ] {a b : ℕ} (y : Matrix (Fin b) (Fin a) κ) (γ : Matrix (Fin a) (Fin a) κ) :
    topL a (y * γ) = topL a y * γ := by
  ext i j
  by_cases hi : i.val < b
  · simp [topL, Matrix.mul_apply, hi]
  · simp [topL, Matrix.mul_apply, hi]

theorem lowZero_mul {κ : Type} [CommRing κ] {a b : ℕ} {y : Matrix (Fin b) (Fin a) κ} (hy : LowZero a y)
    (γ : Matrix (Fin a) (Fin a) κ) : LowZero a (y * γ) := by
  intro i j hi _
  rw [Matrix.mul_apply]
  exact Finset.sum_eq_zero fun l _ => by rw [hy i l hi l.2, zero_mul]

abbrev Cond {a b : ℕ} (L : LevDat D.host.E ℂ a) (y : ∀ PP : Pl D.host.E, Matrix (Fin b) (Fin a) (kP PP)) : Prop :=
  (∀ PP ∈ L.Pg, LowZero a (y PP)) ∧ ∃ g : ∀ PP : ↥L.Pg, GL (Fin a) (kP PP.1),
    (∀ PP : ↥L.Pg, ((g PP : GL (Fin a) _) : Matrix (Fin a) (Fin a) _) = topL a (y PP.1)) ∧
    (∀ PP : ↥L.Pg, g PP ∈ blockTri (blkOf L.r L.t)) ∧ (fun PP => upperLeftBlock L.hr (g PP)) ∈ L.P.H

theorem cond_mul {a b : ℕ} (L : LevDat D.host.E ℂ a) (γ : ∀ PP : Pl D.host.E, GL (Fin a) (kP PP))
    (hγ : ∀ PP ∈ L.Pg, γ PP ∈ blockTri (blkOf L.r L.t)) (hP : (fun PP : ↥L.Pg => upperLeftBlock L.hr (γ PP.1)) ∈ L.P.H)
    (y z : ∀ PP : Pl D.host.E, Matrix (Fin b) (Fin a) (kP PP)) (hz : ∀ PP, z PP = y PP * (γ PP).val)
    (h : Cond L y) : Cond L z := by
  obtain ⟨h1, g, h2, h3, h4⟩ := h
  refine ⟨fun PP hP' => (hz PP).symm ▸ lowZero_mul (h1 PP hP') _, fun PP => g PP * γ PP.1, fun PP => ?_,
    fun PP => mul_mem (h3 PP) (hγ PP.1 PP.2), ?_⟩
  · rw [Units.val_mul, h2, hz, topL_mul]
  · have e : (fun PP : ↥L.Pg => upperLeftBlock L.hr (g PP * γ PP.1)) =
        (fun PP => upperLeftBlock L.hr (g PP)) * (fun PP : ↥L.Pg => upperLeftBlock L.hr (γ PP.1)) := by
      funext PP
      exact extendMatrixByIdentityAlongIndices_mul _ (blockTri_blkOf_le _ _ (h3 PP)) (blockTri_blkOf_le _ _ (hγ PP.1 PP.2))
    rw [e]
    exact mul_mem h4 hP

theorem omegaG_mul_right : ∀ (D : D7) (a b : ℕ) (L : LevDat D.host.E ℂ a) (χ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (G : ∀ PP : Pl D.host.E, GL (Fin a) (kP PP)), (∀ PP ∈ L.Pg, G PP ∈ blockTri (blkOf L.r L.t)) → ∀ hP : (fun PP : ↥L.Pg => upperLeftBlock L.hr (G PP.1)) ∈ L.P.H, ∀ y : ∀ PP : Pl D.host.E, Matrix (Fin b) (Fin a) (kP PP), omegaG L χ (fun PP => y PP * (G PP).val) = ((L.P.chi ⟨_, hP⟩ * (∏ PP ∈ L.Pg, ∏ i ∈ Finset.range L.s, L.cg (i + 1) PP (dBlk (blkOf L.r L.t) (i + 1) (G PP))) * ∏ PP ∈ L.Pg, (χ PP (Matrix.GeneralLinearGroup.det (G PP)))⁻¹ : ℂˣ) : ℂ) * omegaG L χ y := by
  intro D a b L χ G hG hP y
  have hGi : ∀ PP ∈ L.Pg, (G PP)⁻¹ ∈ blockTri (blkOf L.r L.t) := fun PP h => inv_mem (hG PP h)
  have hPi : (fun PP : ↥L.Pg => upperLeftBlock L.hr (G PP.1)⁻¹) ∈ L.P.H := by
    have e : (fun PP : ↥L.Pg => upperLeftBlock L.hr (G PP.1)⁻¹) = (fun PP : ↥L.Pg => upperLeftBlock L.hr (G PP.1))⁻¹ := by
      funext PP
      exact extendOne_inv _ (blockTri_blkOf_le _ _ (hG PP.1 PP.2))
    rw [e]
    exact inv_mem hP
  unfold omegaG
  by_cases hy : Cond L y
  · have hy' : Cond L (fun PP => y PP * (G PP).val) := cond_mul L G hG hP y _ (fun _ => rfl) hy
    rw [dite_eq_left hy', dite_eq_left hy]
    have key : ∀ PP : ↥L.Pg, hy'.2.choose PP = hy.2.choose PP * G PP.1 := fun PP => Units.ext (by
      rw [Units.val_mul, hy'.2.choose_spec.1 PP, hy.2.choose_spec.1 PP, topL_mul])
    have hc : (⟨fun PP => upperLeftBlock L.hr (hy'.2.choose PP), hy'.2.choose_spec.2.2⟩ : L.P.H) =
        ⟨fun PP => upperLeftBlock L.hr (hy.2.choose PP), hy.2.choose_spec.2.2⟩ * ⟨_, hP⟩ :=
      Subtype.ext (funext fun PP => by
        show upperLeftBlock L.hr (hy'.2.choose PP) = upperLeftBlock L.hr (hy.2.choose PP) * upperLeftBlock L.hr (G PP.1)
        rw [key]
        exact extendMatrixByIdentityAlongIndices_mul _ (blockTri_blkOf_le _ _ (hy.2.choose_spec.2.1 PP)) (blockTri_blkOf_le _ _ (hG PP.1 PP.2)))
    have hd : ∀ PP : ↥L.Pg, ∀ c : ℕ, dBlk (blkOf L.r L.t) c (hy'.2.choose PP) =
        dBlk (blkOf L.r L.t) c (hy.2.choose PP) * dBlk (blkOf L.r L.t) c (G PP.1) := fun PP c => by
      rw [key]; exact diag_block_det_mul (hy.2.choose_spec.2.1 PP) (hG PP.1 PP.2)
    rw [hc, map_mul]
    simp only [hd]
    simp only [key, map_mul, Units.val_mul, mul_inv, Finset.prod_mul_distrib, Units.val_inv_eq_inv_val, Units.coe_prod]
    rw [← Finset.prod_coe_sort L.Pg (fun PP => ((χ PP (Matrix.GeneralLinearGroup.det (G PP)) : ℂˣ) : ℂ)⁻¹),
      ← Finset.prod_coe_sort L.Pg (fun PP => ∏ i ∈ Finset.range L.s, ((L.cg (i + 1) PP (dBlk (blkOf L.r L.t) (i + 1) (G PP)) : ℂˣ) : ℂ))]
    ring
  · have hy' : ¬ Cond L (fun PP => y PP * (G PP).val) := fun h => hy (cond_mul L (fun PP => (G PP)⁻¹) hGi hPi _ y
      (fun PP => by rw [Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]) h)
    rw [dite_eq_right hy', dite_eq_right hy, mul_zero]

end GlobalTheory.ChainOnto.RightMove
end
end

