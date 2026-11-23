module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.TCoefMInMMul
public import Development.AbelianVarietyTheory.Definitions.Divisors.RangeShape
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1055
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MuPowLambdaProductCoeffMuVariablePencilEmbedding
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0173
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0154
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0184
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousFamF
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1079
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1116
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1082
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1071
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1698
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1696
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1668
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1692
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1487
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1502
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslatesEqPrimFrameLat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1617
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
public import Formalism.LocalToGlobal.Divisibility.NumbersLemmas
public import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.DepthCond
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0313
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0305
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1666
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1687
public import Development.AbelianVarietyTheory.Counterexamples.RotationExamples.PhaseBreaksTargetParts
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1000
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0072
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0983
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1006
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1693
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0033
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagonalLagrangianInvariantForm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1592
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1643
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1675
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormHeckeLFunctionLeZetaThreeHalvesPow
public import Formalism.PairingDivisors.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsFinSetSplitPlacesCoprimeConductor
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0644
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExplicitFormula.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1233
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0003
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1559
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1364
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1242
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MeasureToRealEqMass
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0683
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0498
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0452
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1654
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OscillatorModelExtensionFirst
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1635

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalPseudoCoefficientExistenceUnitaryGroup
section
open GlobalTheory.PsCo.Pc1

namespace GlobalTheory.PsCo.Pc

theorem localPC_holds : LocalPC :=
  GlobalTheory.PsCo.Pc1.localPC_of_steps GlobalTheory.PsCo.Pc1.A.stAlg GlobalTheory.PsCo.Pc1.stProfile_holds
    GlobalTheory.PsCo.Pc1.stFam GlobalTheory.PsCo.Pc1.Homot.stHomot GlobalTheory.PsCo.Pcd.stLim
    GlobalTheory.ShapeSmoothFinite.stShape GlobalTheory.PsCo.Pc1.orbInt_adSpan_eq_zero GlobalTheory.PsCo.Pc1.stOrbCpt
    GlobalTheory.PsCo.NonEll.stNonEll GlobalTheory.PsCo.Pc3.stTr GlobalTheory.PsCo.Pc3.stTrAd GlobalTheory.T.maximalCompact_pseudoCoefficientData

end GlobalTheory.PsCo.Pc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalWeilOperatorIsometrySchwartzBruhatStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel

open scoped GlobalTheory.VacAny
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localWeilOperator_isometry_schwartzBruhat : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {a a' : ℕ}
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Γ.V Γ.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Γ.V' Γ.W), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ X om om' →
    ∀ (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) (x : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ Γ.V'.J), x ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt σ Γ.V' (evFin F v) →
    ∀ φ φ₁ : (Fin a' × Fin (a + a') → Fv F v) → ℂ, φ ∈ GlobalTheory.WeilM.SB _ → φ₁ ∈ GlobalTheory.WeilM.SB _ →
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (evFin F v) (om' (x, 1)) φ φ₁ →
      ∀ μ : @Measure (Fin a' × Fin (a + a') → Fv F v) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
        ∫⁻ y, ‖φ₁ y‖ₑ ^ 2 ∂μ = ∫⁻ y, ‖φ y‖ₑ ^ 2 ∂μ := by
  first | exact @GlobalTheory.LocalIsom.lintegral_sq_eq_of_acts | exact GlobalTheory.LocalIsom.lintegral_sq_eq_of_acts | (intros; apply GlobalTheory.LocalIsom.lintegral_sq_eq_of_acts <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowFormOfEmb
section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Module
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links
open Formalism.IndefR.Cx Formalism.IndefR.FWT Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.FormTies GlobalTheory.BigOn
open GlobalTheory.LiftLower GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature
open scoped InnerProductSpace Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LowForm

section Abstract

variable {K X Y : Type} [Field K] [AddCommGroup X] [Module K X] [AddCommGroup Y] [Module K Y]

theorem exists_descent {H W : Type} [AddCommGroup H] [Module ℂ H] [AddCommGroup W] [Module ℂ W] {σ₁ σ₂ : K →+* ℂ} (e : σ₁ = σ₂)
    (φ : Y →ₛₗ[σ₁] W) (ψ : X →ₛₗ[σ₂] H) (T : H →ₗ[ℂ] W) (c : ℂ) (h : ∀ x, ∃! y, φ y = c • T (ψ x)) :
    ∃ θ : X →ₗ[K] Y, ∀ x, φ (θ x) = c • T (ψ x) := by
  subst e
  choose f hf hu using h
  refine ⟨⟨⟨f, fun x x' => (hu _ _ ?_).symm⟩, fun a x => (hu _ _ ?_).symm⟩, hf⟩
  · simp only [map_add (f := _), hf, smul_add]
  · simp only [map_smulₛₗ, hf, RingHom.id_apply, smul_comm c]

theorem mem_orth_ker [FiniteDimensional K X] {H W : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup W]
    [InnerProductSpace ℂ W] {σ : K →+* ℂ} (θ : X →ₗ[K] Y) (j : X →ₛₗ[σ] H) (jW : Y →ₛₗ[σ] W) (th : H →ₗ[ℂ] W)
    (U : W ≃ₗᵢ[ℂ] W) (g : W →ₗ[ℂ] W) (κ : ℂ) (h1 : Submodule.span ℂ (Set.range j) = ⊤)
    (h2 : ∀ (n : ℕ) (b : Fin n → Y), LinearIndependent K b → LinearIndependent ℂ fun k => jW (b k))
    (h3 : ∀ x, U (jW (θ x)) = κ • g (th (j x))) {x : X} (h4 : ∀ u, θ u = 0 → ⟪j x, j u⟫_ℂ = 0) :
    j x ∈ (LinearMap.ker th)ᗮ := by
  have key := GlobalTheory.ker_le_span_image_ker_of_semilinear K X Y H W σ θ j jW
    ((U.symm.toLinearEquiv : W →ₗ[ℂ] W) ∘ₗ (κ • (g ∘ₗ th))) h1 h2 fun x => by
      show U.symm (κ • g (th (j x))) = _
      rw [← h3, U.symm_apply_apply]
  have h5 : LinearMap.ker th ≤ Submodule.span ℂ (j '' (LinearMap.ker θ : Set X)) := fun w hw => key (by
    show U.symm (κ • g (th w)) = 0
    rw [LinearMap.mem_ker.1 hw, map_zero, smul_zero, map_zero])
  refine Submodule.orthogonal_le h5 ((Submodule.mem_orthogonal' _ _).2 fun w hw => ?_)
  have h6 : Submodule.span ℂ (j '' (LinearMap.ker θ : Set X)) ≤ LinearMap.ker (innerₛₗ ℂ (j x)) := by
    rw [Submodule.span_le]
    rintro _ ⟨u, hu, rfl⟩
    exact h4 u hu
  exact h6 hw

theorem re_inner_self {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (x : H) : (⟪x, x⟫_ℂ).re = ‖x‖ ^ 2 :=
  inner_self_eq_norm_sq (𝕜 := ℂ) x

theorem csumAt_conj [NumberField K] [StarRing K] (S : CSD K) (σ : K →+* ℂ) (f g : S.Forms) :
    csumAt S ((starRingEnd ℂ).comp σ) f g = starRingEnd ℂ (csumAt S σ f g) := by
  unfold csumAt
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [dotProduct, Matrix.mulVec, Matrix.map_apply, Pi.star_apply, map_sum, map_mul, RingHom.comp_apply]
  rfl

end Abstract

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {F : Face D A}

theorem toF_mem (i : Fin D.R.m) (t : T0) (y : Fin ((A.fam.L i t).dZ (liftLvl F) (liftSub R F i t)) → D.what₂.LL) :
    (A.fam.L i t).toF (liftLvl F) (liftSub R F i t) y ∈ liftSub R F i t := by
  obtain ⟨f, hf, e⟩ : ((A.fam.L i t).zE (liftLvl F) (liftSub R F i t)).mulVec y ∈
    (A.fam.L i t).Z0 (liftLvl F) (liftSub R F i t) := (subspace_image_spec _ _ _).2.le ⟨y, rfl⟩
  have : (A.fam.L i t).toF (liftLvl F) (liftSub R F i t) y = f :=
    (congrArg (A.fam.L i t).S.basis.equivFun.symm e.symm).trans ((A.fam.L i t).S.basis.equivFun.symm_apply_apply f)
  exact this ▸ hf

theorem norm_wC (i : Fin D.R.m) (v : InfinitePlace D.what₂.LL) (z : Fin (finrank D.what₂.LL (R.WL F false i)) → D.what₂.LL) :
    ‖(R.toCx F).wC false i v (cpt v.embedding z)‖ ^ 2 =
      (RealDat.nP F false)⁻¹ * ‖(R.FW i).j (sgAt D.what₂.embLL v) (coordMap R F i z)‖ ^ 2 := by
  have e : ((Tw.out (s := twAt D.what₂.embLL v) ((R.toCx F).wC false i v (cpt v.embedding z)) :
      R.WS F false i (sgAt D.what₂.embLL v)) : (R.HW i (sgAt D.what₂.embLL v)).H) =
      (((Real.sqrt (RealDat.nP F false))⁻¹ : ℝ) : ℂ) • (R.FW i).j (sgAt D.what₂.embLL v) (coordMap R F i z) := by
    have e0 : (R.toCx F).wC false i v (cpt v.embedding z) = ∑ k, v.embedding (z k) • (R.toCx F).bW false i v k := rfl
    refine (congrArg (fun a => ((Tw.out (s := twAt D.what₂.embLL v) a : R.WS F false i (sgAt D.what₂.embLL v)) :
      (R.HW i (sgAt D.what₂.embLL v)).H)) e0).trans ?_
    refine (congrArg Subtype.val (out_sum _)).trans ((Submodule.coe_sum _ _ _).trans ?_)
    unfold coordMap
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Fintype.linearCombination_apply, map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    show cj (twAt D.what₂.embLL v) (v.embedding (z k)) •
      ((((Real.sqrt (RealDat.nP F false))⁻¹ : ℝ) : ℂ) • (R.FW i).j (sgAt D.what₂.embLL v) (R.bL F false i k)) = _
    rw [map_smulₛₗ, emb_eq D.what₂.embLL v, cj_cj, smul_comm]
  have e2 := congrArg norm e
  refine (congrArg (· ^ 2) e2).trans ?_
  show ‖_ • _‖ ^ 2 = _
  rw [norm_smul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs, inv_pow, Real.sq_sqrt (RealDat.nP_pos false).le]

end GlobalTheory.LowForm

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedProjectionPreservesSchwartzAdmStatement
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.LatVac
open scoped Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mixed_projection_preserves_schwartz_adm : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (v : Pl (F := F)) (φ₀ : (κ → Fv F v) → ℂ), φ₀ ∈ SB (κ → Fv F v) → ∀ l : ((κ → Fv F v) → ℂ) →ₗ[ℂ] ℂ,
    (∀ Φ ∈ schA F κ, GlobalTheory.MixedForm.proj v φ₀ l Φ ∈ schA F κ) ∧
      ∀ L ∈ (adeleClass F).adm κ, L ∘ₗ GlobalTheory.MixedForm.proj v φ₀ l ∈ (adeleClass F).adm κ := by
  first | exact @GlobalTheory.MixedForm.proj_schA_adm | exact GlobalTheory.MixedForm.proj_schA_adm | (intros; apply GlobalTheory.MixedForm.proj_schA_adm <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormCompletedHeckeLCMOneLePhragmenLindelof
section
open NumberField IsDedekindDomain GlobalTheory.CMVal

noncomputable section
namespace GlobalTheory.HeckeLOneBound
open GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds

theorem norm_factor (s c : ℂ) :
    ‖2 * (2 * (Real.pi : ℂ)) ^ (-(s + c)) * Complex.Gamma (s + c)‖ =
      2 * (2 * Real.pi) ^ (-(s.re + c.re)) * ‖Complex.Gamma (s + c)‖ := by
  have h2 : (2 * (Real.pi : ℂ)) = ((2 * Real.pi : ℝ) : ℂ) := by push_cast; ring
  rw [norm_mul, norm_mul, h2, Complex.norm_cpow_eq_rpow_re_of_pos (by positivity)]
  simp

theorem norm_archFactor_real {I : Type} [Fintype I] (n : I → ℤ) {x : ℝ} (hx : 0 < x) :
    ‖archFactor n (x : ℂ)‖ = ∏ i, (2 * (2 * Real.pi) ^ (-(x + ((|n i| : ℤ) : ℝ) / 2)) *
      Real.Gamma (x + ((|n i| : ℤ) : ℝ) / 2)) := by
  unfold archFactor
  rw [norm_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [norm_factor]
  have hc : ((x : ℂ) + ((|n i| : ℤ) : ℂ) / 2) = ((x + ((|n i| : ℤ) : ℝ) / 2 : ℝ) : ℂ) := by
    simp only [Complex.ofReal_add, Complex.ofReal_div, Complex.ofReal_intCast, Complex.ofReal_ofNat]
  have h0 : (0 : ℝ) ≤ ((|n i| : ℤ) : ℝ) := by exact_mod_cast abs_nonneg (n i)
  rw [hc, Complex.Gamma_ofReal, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.Gamma_pos_of_pos (by linarith))]
  congr 3
  simp

theorem norm_archFactor_le {I : Type} [Fintype I] (n : I → ℤ) {s : ℂ} (hs : 0 < s.re) :
    ‖archFactor n s‖ ≤ ‖archFactor n (s.re : ℂ)‖ := by
  rw [norm_archFactor_real n hs]
  unfold archFactor
  rw [norm_prod]
  refine Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) fun i _ => ?_
  rw [norm_factor]
  have h0 : (0 : ℝ) ≤ ((|n i| : ℤ) : ℝ) := by exact_mod_cast abs_nonneg (n i)
  have hre : (s + ((|n i| : ℤ) : ℂ) / 2).re = s.re + ((|n i| : ℤ) : ℝ) / 2 := by simp
  have hre' : (((|n i| : ℤ) : ℂ) / 2).re = ((|n i| : ℤ) : ℝ) / 2 := by simp
  rw [hre']
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have := PI.EF.norm_Gamma_le (w := s + ((|n i| : ℤ) : ℂ) / 2) (by rw [hre]; linarith)
  rwa [hre] at this

theorem pl_strip {f : ℂ → ℂ} (hf : Differentiable ℂ f) {a b C : ℝ} (hab : a < b)
    (hbd : ∃ C' : ℝ, ∀ s : ℂ, a ≤ s.re → s.re ≤ b → ‖f s‖ ≤ C')
    (ha : ∀ s : ℂ, s.re = a → ‖f s‖ ≤ C) (hb : ∀ s : ℂ, s.re = b → ‖f s‖ ≤ C)
    {z : ℂ} (hza : a ≤ z.re) (hzb : z.re ≤ b) : ‖f z‖ ≤ C := by
  refine PhragmenLindelof.vertical_strip hf.diffContOnCl ?_ ha hb hza hzb
  refine ⟨0, div_pos Real.pi_pos (sub_pos.2 hab), 0, ?_⟩
  obtain ⟨C', hC'⟩ := hbd
  refine Asymptotics.IsBigO.of_bound C' ?_
  refine Filter.eventually_inf_principal.2 (Filter.Eventually.of_forall fun z hz => ?_)
  simp only [zero_mul, Real.exp_zero, norm_one, mul_one]
  exact hC' z hz.1.le hz.2.le

theorem factor_three_halves_le {c : ℝ} (hc : 1 ≤ c) :
    2 * (2 * Real.pi) ^ (-(3 / 2 + c)) * Real.Gamma (3 / 2 + c) ≤
      2 * (2 * Real.pi) ^ (-(1 + c)) * Real.Gamma (1 + c) * (1 + c) := by
  have hpi : 1 ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
  have h1 : (2 * Real.pi) ^ (-(3 / 2 + c)) ≤ (2 * Real.pi) ^ (-(1 + c)) :=
    Real.rpow_le_rpow_of_exponent_le hpi (by linarith)
  have h2 : Real.Gamma (3 / 2 + c) ≤ Real.Gamma (1 + c + 1) :=
    Real.Gamma_strictMonoOn_Ici.monotoneOn (Set.mem_Ici.2 (by linarith)) (Set.mem_Ici.2 (by linarith)) (by linarith)
  rw [Real.Gamma_add_one (by linarith)] at h2
  have hg : 0 ≤ Real.Gamma (3 / 2 + c) := (Real.Gamma_pos_of_pos (by linarith)).le
  have hp : 0 ≤ (2 * Real.pi) ^ (-(1 + c)) := by positivity
  calc 2 * (2 * Real.pi) ^ (-(3 / 2 + c)) * Real.Gamma (3 / 2 + c)
      ≤ 2 * (2 * Real.pi) ^ (-(1 + c)) * Real.Gamma (3 / 2 + c) := by gcongr
    _ ≤ 2 * (2 * Real.pi) ^ (-(1 + c)) * ((1 + c) * Real.Gamma (1 + c)) := by gcongr
    _ = _ := by ring

theorem archFactor_three_halves_le {I : Type} [Fintype I] (m : I → ℤ) (hm : ∀ i, 0 < m i) :
    ‖archFactor (fun i => 2 * m i) (3 / 2)‖ ≤ ‖archFactor (fun i => 2 * m i) 1‖ * ∏ i, (1 + (m i : ℝ)) := by
  have e32 : (3 / 2 : ℂ) = ((3 / 2 : ℝ) : ℂ) := by push_cast; ring
  have e1 : (1 : ℂ) = ((1 : ℝ) : ℂ) := by simp
  rw [e32, e1, norm_archFactor_real _ (by norm_num), norm_archFactor_real _ (by norm_num), ← Finset.prod_mul_distrib]
  refine Finset.prod_le_prod₀ (fun i _ => ?_) fun i _ => ?_
  · have : 0 < 3 / 2 + ((|2 * m i| : ℤ) : ℝ) / 2 := by
      have : (0 : ℝ) ≤ ((|2 * m i| : ℤ) : ℝ) := by exact_mod_cast abs_nonneg _
      linarith
    have := Real.Gamma_pos_of_pos this
    positivity
  · have hc : ((|2 * m i| : ℤ) : ℝ) / 2 = (m i : ℝ) := by
      rw [abs_of_pos (by have := hm i; omega)]; push_cast; ring
    rw [hc]
    exact factor_three_halves_le (by exact_mod_cast hm i)

end GlobalTheory.HeckeLOneBound

namespace GlobalTheory.HeckeLOneBound
open GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds

theorem norm_heckeL_one_le : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ),
    GlobalTheory.Published.HeckeFunctionalEquationAbs → GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds.CompletedLBoundedInStrips → IsCMType φ →
    ∀ (χ : HChar E) (m : I → ℤ) (a : HeightOneSpectrum (𝓞 E) →₀ ℕ) (Λ : ℂ → ℂ),
    IsUnitary χ → TrivOnF χ → HasInf χ φ m → (∀ i, 0 < m i) → (∀ v, ExpAt χ v (a v)) → IsHeckeL χ Λ →
    ‖Λ 1‖ ≤ ‖riemannZeta (3 / 2)‖ ^ Module.finrank ℚ E *
      ((((discr E).natAbs * a.prod fun v k => Ideal.absNorm v.asIdeal ^ k : ℕ) : ℝ)) * ∏ i, (1 + (m i : ℝ)) := by
  intro E _ _ _ I _ φ hFE hB hφ χ m a Λ hu htr hinf hpos ha hL
  set n : I → ℤ := fun i => 2 * m i with hn_def
  set A : ℕ := (discr E).natAbs * a.prod fun v k => Ideal.absNorm v.asIdeal ^ k with hA_def
  set Z : ℝ := ‖riemannZeta (3 / 2)‖ ^ Module.finrank ℚ E with hZ_def
  have hinf' : Formalism.L2.Host.HChar.HasInf χ φ n := hinf
  obtain ⟨i₀⟩ := GlobalTheory.LValNe.nonempty_of_isCMType hφ
  have hn : ∃ i, n i ≠ 0 := ⟨i₀, by have := hpos i₀; simp only [hn_def]; omega⟩
  have hn' : ∃ i, (fun i => -n i) i ≠ 0 := ⟨i₀, by have := hpos i₀; simp only [hn_def]; omega⟩
  have hu' := GlobalTheory.Published.HeckeFEModel.isUnitary_inv hu
  have hinv := GlobalTheory.Published.HeckeFEModel.hasInf_inv hinf'
  obtain ⟨Λc, hΛc, hbc⟩ := hB E I φ hφ χ n hu hinf' hn
  obtain ⟨Λc', hΛc', -⟩ := hB E I φ hφ χ⁻¹ (fun i => -n i) hu' hinv hn'
  obtain ⟨ε, hε, hfe⟩ := hFE E I φ hφ χ n a Λc Λc' hu hinf' hn ha hΛc hΛc'
  have hL' : IsHeckeL χ⁻¹ Λ := _root_.GlobalTheory.CMVal.isHeckeL_inv_of_trivOnF E χ Λ htr hL
  have harch : archFactor (fun i => -n i) = archFactor n := by
    funext s; unfold archFactor; simp only [abs_neg]
  have hApos : 0 < A := by
    refine Nat.mul_pos (Int.natAbs_pos.2 (discr_ne_zero E)) ?_
    unfold Finsupp.prod
    exact Finset.prod_pos fun v _ => pow_pos (Nat.pos_of_ne_zero fun h => v.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)) _
  have hA1 : (1 : ℝ) ≤ (A : ℝ) := by exact_mod_cast hApos
  have hZ0 : 0 ≤ Z := by positivity
  set F : ℝ := ‖archFactor n (3 / 2)‖ with hF_def
  have hF0 : 0 ≤ F := norm_nonneg _

  have hline : ∀ s : ℂ, s.re = 3 / 2 → ‖Λc s‖ ≤ F * Z := fun s hs => by
    rw [hΛc.eq_mul hL (by rw [hs]; norm_num), norm_mul]
    have h1 := norm_archFactor_le n (s := s) (by rw [hs]; norm_num)
    rw [hs] at h1
    have h1' : ‖archFactor n s‖ ≤ F := by
      rw [hF_def]; convert h1 using 3; push_cast; ring
    exact mul_le_mul h1' (_root_.GlobalTheory.HeckeLBound.norm_heckeL_le E χ Λ s hu hL hs.ge) (norm_nonneg _) hF0
  have hline' : ∀ s : ℂ, s.re = 3 / 2 → ‖Λc' s‖ ≤ F * Z := fun s hs => by
    rw [hΛc'.eq_mul hL' (by rw [hs]; norm_num), norm_mul, harch]
    have h1 := norm_archFactor_le n (s := s) (by rw [hs]; norm_num)
    rw [hs] at h1
    have h1' : ‖archFactor n s‖ ≤ F := by
      rw [hF_def]; convert h1 using 3; push_cast; ring
    exact mul_le_mul h1' (_root_.GlobalTheory.HeckeLBound.norm_heckeL_le E χ⁻¹ Λ s hu' hL' hs.ge) (norm_nonneg _) hF0

  have hleft : ∀ s : ℂ, s.re = -1 / 2 → ‖Λc s‖ ≤ A * F * Z := fun s hs => by
    rw [hfe s, norm_mul, norm_mul, hε, one_mul, Complex.norm_natCast_cpow_of_pos hApos]
    have hre : (1 / 2 - s).re = 1 := by
      simp only [Complex.sub_re, hs]; norm_num
    rw [hre, Real.rpow_one, mul_assoc]
    refine mul_le_mul_of_nonneg_left (hline' _ ?_) (by positivity)
    simp only [Complex.sub_re, Complex.one_re, hs]; norm_num
  have hright : ∀ s : ℂ, s.re = 3 / 2 → ‖Λc s‖ ≤ A * F * Z := fun s hs => by
    refine (hline s hs).trans ?_
    rw [mul_assoc]
    exact le_mul_of_one_le_left (by positivity) hA1

  have hbd := hbc (-1 / 2) (3 / 2) (by norm_num)
  have h1 : ‖Λc 1‖ ≤ A * F * Z :=
    pl_strip hΛc.1 (by norm_num) hbd hleft hright (by norm_num) (by norm_num)

  have hg : ∀ i, Complex.Gamma ((1 : ℂ) + ((|n i| : ℤ) : ℂ) / 2) ≠ 0 := fun i => by
    refine Complex.Gamma_ne_zero_of_re_pos ?_
    have : (0 : ℝ) ≤ ((|n i| : ℤ) : ℝ) := by exact_mod_cast abs_nonneg (n i)
    simp only [Complex.add_re, Complex.one_re, Complex.div_re, Complex.intCast_re, Complex.intCast_im]
    norm_num
    positivity
  have e1 := GlobalTheory.LValNe.completed_eq hΛc hL hg
  have hG : 0 < ‖archFactor n 1‖ := norm_pos_iff.2 (GlobalTheory.LValNe.archFactor_ne_zero hg)
  have hrat := archFactor_three_halves_le m hpos
  rw [e1, norm_mul] at h1
  have hP0 : 0 ≤ ∏ i, (1 + (m i : ℝ)) :=
    Finset.prod_nonneg fun i _ => by have : (0 : ℝ) < m i := by exact_mod_cast hpos i
                                     linarith
  have key : ‖archFactor n 1‖ * ‖Λ 1‖ ≤ ‖archFactor n 1‖ * (Z * (A : ℝ) * ∏ i, (1 + (m i : ℝ))) := by
    refine h1.trans ?_
    have : A * F * Z ≤ A * (‖archFactor n 1‖ * ∏ i, (1 + (m i : ℝ))) * Z := by gcongr
    refine this.trans (le_of_eq ?_)
    ring
  exact le_of_mul_le_mul_left key hG

end GlobalTheory.HeckeLOneBound

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OpenKLeFockStab
section
open NumberField MeasureTheory Finset
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open GlobalTheory.NormSum (Pair Tup)
open GlobalTheory.FunObj.SqNum GlobalTheory.SqTop
open GlobalTheory.CMVal (IsHeckeL)

noncomputable section
namespace GlobalTheory.NormAdelic
attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ t0 : ℂ} {Q : ℕ} {P : Pair D cc δ t0 Q}

theorem minorPol_ne_zero {a d : ℕ} {n : D.what₂.Tau → ℕ} (T : Tup D a d n) : GlobalTheory.NormSum.minorPol D T ≠ 0 := by
  unfold GlobalTheory.NormSum.minorPol
  refine Finset.prod_ne_zero_iff.2 fun τ _ => Finset.prod_ne_zero_iff.2 fun j _ => ?_
  set f : Fin a × Fin a → Formalism.MainNotions.GL3Theta.Idx D a d := fun p => (τ, (T τ j).1 p.1, p.2) with hf
  have hfi : Function.Injective f := by
    intro p q e
    simp only [hf, Prod.mk.injEq] at e
    exact Prod.ext ((T τ j).2.injective e.2.1) e.2.2
  have e : (Matrix.of fun i i' : Fin a => (MvPolynomial.X (τ, (T τ j).1 i, i') : MvPolynomial (Formalism.MainNotions.GL3Theta.Idx D a d) ℂ)) =
      (MvPolynomial.rename f).toRingHom.mapMatrix (Matrix.mvPolynomialX (Fin a) (Fin a) ℂ) := by
    ext i i'
    simp [Matrix.mvPolynomialX, hf]
  rw [e, ← RingHom.map_det]
  intro h0
  exact Matrix.det_mvPolynomialX_ne_zero (Fin a) ℂ
    ((MvPolynomial.rename_injective f hfi) (h0.trans (map_zero _).symm))

end GlobalTheory.NormAdelic
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OscillatorModelExtensionSecond
section
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AdTh.SerAll


open NumberField Matrix Complex MeasureTheory IsDedekindDomain in
open scoped TensorProduct Classical ComplexConjugate in
attribute [local instance] _root_.Formalism.BasicNotions.Host.cmStar in
theorem _root_.GlobalTheory.AdTh.SerAll.lieFac_eq_pow {E : Type} [Field E] [NumberField E] [IsCMField E]
    {H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (Dw : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H) {x : ℝ} (hx : 0 < x)
    (a : (E →+* ℂ) × ℕ → ℕ) :
    _root_.Formalism.L2.Pj.lieFac Dw x a = (Real.sqrt (2 * Real.pi * x))⁻¹ ^ _root_.GlobalTheory.PtId.degW Dw a := by
  have hy : 0 < 2 * Real.pi * x := by positivity
  rw [Real.sqrt_eq_rpow, ← Real.rpow_neg hy.le, ← Real.rpow_natCast, ← Real.rpow_mul hy.le,
    Real.rpow_def_of_pos hy]
  unfold _root_.Formalism.L2.Pj.lieFac _root_.GlobalTheory.PtId.degW
  congr 1
  push_cast
  ring


end GlobalTheory.AdTh.SerAll
end
end

