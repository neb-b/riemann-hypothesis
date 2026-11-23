module

public import Mathlib
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0469
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0461
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0057
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasDerivAtAndIsTheta
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0249
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.NotIsFinitePartOfBot
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0467
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0463
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0012
public import GroundTheory.AutomorphicForms.CuspidalDiscreteness
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0471
public import GroundTheory.AutomorphicForms.AnisotropicUnitaryCompact
public import CompanionTheory.AutomorphicTheory.SiegelWeilFiniteness.Bridge
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0007
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0014
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0434
public import GroundTheory.AutomorphicForms.AnisotropicUnitaryHeight
public import GroundTheory.AutomorphicForms.ReductionMahler
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0465
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
public import GroundTheory.AutomorphicForms.CuspidalDiscreteness.CuspFormsHeight
public import GroundTheory.AutomorphicForms.CuspidalDiscreteness.DecayUniform
public import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.GKStable
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0454
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0436
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0437
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0464
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeckeCosetSumCompact
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousRs
section
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.WSum

variable {D : D7} {r : ℕ}

def rs (σ : (D.what₂.Tau → ℂ) →+ AE D) (s : ℝ) : AE D := σ fun _ => (s : ℂ)

theorem rs_add (σ : (D.what₂.Tau → ℂ) →+ AE D) (s t : ℝ) : rs σ (s + t) = rs σ s + rs σ t := by
  unfold rs
  rw [← map_add (f := _)]
  congr 1
  funext x
  simp

theorem rs_zero (σ : (D.what₂.Tau → ℂ) →+ AE D) : rs σ 0 = 0 := by
  unfold rs
  have : (fun _ : D.what₂.Tau => ((0 : ℝ) : ℂ)) = 0 := by funext; simp
  rw [this, map_zero]

theorem finPart_cA (z : AE D) :
    finPart D (cA D z) = sigR (Af D.host.F) D.sp.cm.sig (finPart D z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a x => rfl
  | add a b ha hb => rw [RingHom.map_add (f := _), RingHom.map_add (f := _), RingHom.map_add (f := _), RingHom.map_add (f := _), ha, hb]

theorem cA_rs {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D} (hσ : GlobalTheory.FockCompare.Chart θ σ) (s : ℝ) :
    cA D (rs σ s) = rs σ s := by
  refine sub_eq_zero.1 (hσ.ext _ ?_ fun τ => ?_)
  · have h0 : finPart D (rs σ s) = 0 := hσ.fin _
    rw [RingHom.map_sub, finPart_cA, h0, map_zero, sub_zero]
  · have hcm := Formalism.MainNotions.UnusedSlot34.isCMExt_D D
    rw [RingHom.map_sub, RingHom.map_sub, GlobalTheory.PhaseReal.infPart_cA,
      GlobalTheory.Mem.VolExists.infEmb_sigR hcm (hσ.inf τ)]
    unfold rs
    rw [hσ.comp]
    simp

theorem continuous_rs {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D} (hσ : GlobalTheory.FockCompare.Chart θ σ) :
    Continuous (rs σ) :=
  hσ.cont.comp (continuous_pi fun _ => Complex.continuous_ofReal)

def path {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D} (hσ : GlobalTheory.FockCompare.Chart θ σ) (a : HermE D r) :
    ℝ →+ hermA D r where
  toFun s := ⟨rs σ s • a.1.map (incA D), by
    show adj (rs σ s • a.1.map (incA D)) = rs σ s • a.1.map (incA D)
    rw [adj_smul, cA_rs hσ]
    congr 1
    exact GlobalTheory.CompanionTheory.HermPoisson.rat_mem_hermA a⟩
  map_zero' := by
    apply Subtype.ext
    show rs σ 0 • a.1.map (incA D) = 0
    rw [rs_zero, zero_smul]
  map_add' s t := by
    apply Subtype.ext
    show rs σ (s + t) • a.1.map (incA D) = rs σ s • a.1.map (incA D) + rs σ t • a.1.map (incA D)
    rw [rs_add, add_smul]

def lam (θ : InfFam D) (α : D.host.F) (t : AE D) : ℝ :=
  -∑ τ, (θ τ (infPart D (incA D (algebraMap D.host.F D.host.E α) * t))).re

def multM (θ : InfFam D) (α : D.host.F) (V : HSp D) (a : HermE D r) (y : Mx D V.rank r) : ℝ :=
  lam θ α (Matrix.trace (HMul.hMul (a.1.map (incA D)) (inner V y y) : Mx D r r))

def pairF (θ : InfFam D) (α : D.host.F) (a β : HermE D r) : ℝ :=
  lam θ α (incA D (Matrix.trace (β.1 * a.1)))

end GlobalTheory.CompanionTheory.WSum
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConvolutionMaximalCompactEquivariant
section
open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CompanionTheory.SmoothRep
open scoped ContDiff

noncomputable section

namespace GlobalTheory.CompanionTheory.SmoothRep

theorem tst_conj_Kinf {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}
    (U : Subgroup (GL (Fin a) (Af E))) {β : Lie E a → ℂ} (hβ : ConjInv β) (k : Kinf E a) (y : GA E a) :
    tst U β ((infGL E a (Unitary.toUnits k))⁻¹ * (y * infGL E a (Unitary.toUnits k))) = tst U β y := by
  have e : ((infGL E a (Unitary.toUnits k))⁻¹ * (y * infGL E a (Unitary.toUnits k)))⁻¹ =
      (infGL E a (Unitary.toUnits k))⁻¹ * y⁻¹ * infGL E a (Unitary.toUnits k) := by group
  have hf : GeneralLinearGroup.map (pFin E) ((infGL E a (Unitary.toUnits k))⁻¹ * y⁻¹ * infGL E a (Unitary.toUnits k)) =
      GeneralLinearGroup.map (pFin E) y⁻¹ := by
    simp only [map_mul, map_inv, pFin_infGL, inv_one, one_mul, mul_one]
  have hi : GeneralLinearGroup.map (pInf E) ((infGL E a (Unitary.toUnits k))⁻¹ * y⁻¹ * infGL E a (Unitary.toUnits k)) =
      (Unitary.toUnits k)⁻¹ * GeneralLinearGroup.map (pInf E) y⁻¹ * Unitary.toUnits k := by
    rw [map_mul, map_mul, map_inv, pInf_infGL]
  have hc := hβ k⁻¹ (toL (GeneralLinearGroup.map (pInf E) y⁻¹).val)
  have hv : toL ((k⁻¹ : Kinf E a).1 * Matrix.of (toL (GeneralLinearGroup.map (pInf E) y⁻¹).val) * star (k⁻¹ : Kinf E a).1) =
      toL ((Unitary.toUnits k)⁻¹ * GeneralLinearGroup.map (pInf E) y⁻¹ * Unitary.toUnits k).val := by
    have h1 : ((Unitary.toUnits k)⁻¹ : GL (Fin a) (Cinf E)).val = (k⁻¹ : Kinf E a).1 := by
      rw [← map_inv]; rfl
    have h2 : star (k⁻¹ : Kinf E a).1 = k.1 := by
      change star (star k.1) = k.1
      exact star_star _
    rw [h2, Units.val_mul, Units.val_mul, h1]
    rfl
  unfold tst ker
  rw [e, hf, hi, ← hv, hc]

theorem convR_tst_cpt : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (μ : Measure (GA E a)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (U : Subgroup (GL (Fin a) (Af E))) (β : Lie E a → ℂ), ConjInv β → ∀ (F : L2 (latticeGL E a) μ) (k : Kinf E a) (x : GA E a), convR μ (tst U β) (lift (latticeGL E a) (R (latticeGL E a) μ (infGL E a (Unitary.toUnits k)) F)) x = convR μ (tst U β) (lift (latticeGL E a) F) (x * infGL E a (Unitary.toUnits k)) := by
  intro E _ _ _ a μ _ _ U β hβ F k x
  have h1 : ∀ᵐ y ∂μ, lift (latticeGL E a) (R (latticeGL E a) μ (infGL E a (Unitary.toUnits k)) F) (x * y) =
      lift (latticeGL E a) F (x * y * infGL E a (Unitary.toUnits k)) :=
    (measurePreserving_mul_left μ x).quasiMeasurePreserving.ae (lift_R (infGL E a (Unitary.toUnits k)) F)
  simp only [AutomorphicL2Unitary.convR]
  rw [← integral_mul_left_eq_self
      (fun y => tst U β y * lift (latticeGL E a) F (x * infGL E a (Unitary.toUnits k) * y)) (infGL E a (Unitary.toUnits k))⁻¹,
    ← integral_mul_right_eq_self
      (fun y => tst U β ((infGL E a (Unitary.toUnits k))⁻¹ * y) *
        lift (latticeGL E a) F (x * infGL E a (Unitary.toUnits k) * ((infGL E a (Unitary.toUnits k))⁻¹ * y)))
      (infGL E a (Unitary.toUnits k))]
  refine integral_congr_ae (h1.mono fun y hy => ?_)
  have e : x * infGL E a (Unitary.toUnits k) * ((infGL E a (Unitary.toUnits k))⁻¹ * (y * infGL E a (Unitary.toUnits k))) =
      x * y * infGL E a (Unitary.toUnits k) := by group
  simp only [tst_conj_Kinf U hβ k y, e, hy]

end GlobalTheory.CompanionTheory.SmoothRep
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConvolutionRightInvariantOpenCompact
section
open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CompanionTheory.SmoothRep
open scoped ContDiff

noncomputable section

namespace GlobalTheory.CompanionTheory.SmoothRep

theorem tst_finGL_inv_mul {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}
    (U : Subgroup (GL (Fin a) (Af E))) (β : Lie E a → ℂ) (u : GL (Fin a) (Af E)) (hu : u ∈ U)
    (y : GA E a) : tst U β ((finGL E a u)⁻¹ * y) = tst U β y := by
  have hinv : ((finGL E a u)⁻¹ * y)⁻¹ = y⁻¹ * finGL E a u := by
    rw [_root_.mul_inv_rev, inv_inv]
  have hfin : GeneralLinearGroup.map (pFin E) (y⁻¹ * finGL E a u)
      = GeneralLinearGroup.map (pFin E) y⁻¹ * u := by
    rw [map_mul, pFin_finGL]
  have hinf : GeneralLinearGroup.map (pInf E) (y⁻¹ * finGL E a u)
      = GeneralLinearGroup.map (pInf E) y⁻¹ := by
    rw [map_mul, pInf_finGL, mul_one]
  unfold tst ker
  rw [hinv, hfin, hinf]
  by_cases hm : GeneralLinearGroup.map (pFin E) y⁻¹ ∈ U
  · rw [if_pos (U.mul_mem hm hu), if_pos hm]
  · rw [if_neg (fun h => hm (by simpa using U.mul_mem h (U.inv_mem hu))), if_neg hm]

theorem convR_tst_mul_finGL (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ)
    (μ : Measure (GA E a)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant]
    (U : Subgroup (GL (Fin a) (Af E))) (β : Lie E a → ℂ) (Fl : GA E a → ℂ)
    (u : GL (Fin a) (Af E)) (hu : u ∈ U) (x : GA E a) :
    convR μ (tst U β) Fl (x * finGL E a u) = convR μ (tst U β) Fl x := by
  unfold convR
  have h := integral_mul_left_eq_self (μ := μ)
    (fun y => tst U β ((finGL E a u)⁻¹ * y) * Fl (x * y)) (finGL E a u)
  simp only [inv_mul_cancel_left] at h
  simp only [tst_finGL_inv_mul U β u hu] at h
  simpa only [mul_assoc] using h

theorem convR_tst_right_invariant : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (μ : Measure (GA E a)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (U : Subgroup (GL (Fin a) (Af E))) (β : Lie E a → ℂ) (Fl : GA E a → ℂ) (u : GL (Fin a) (Af E)), u ∈ U → ∀ x : GA E a, convR μ (tst U β) Fl (x * finGL E a u) = convR μ (tst U β) Fl x := by
  intro E _ _ _ a μ _ _ U β Fl u hu x
  exact convR_tst_mul_finGL E a μ U β Fl u hu x

end GlobalTheory.CompanionTheory.SmoothRep
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalDecompositionOfCompactStatement
section
open NumberField MeasureTheory Topology GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.UnitaryBC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspidal_decomposition_of_compact : (∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (μ : Measure (GA E a)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (f : GA E a → ℂ), Continuous f → HasCompactSupport f → IsCompactOperator (repOp (Rcusp μ) μ f)) → GlobalTheory.Published.CuspDiscreteDecompositionGL := by
  first | exact @GlobalTheory.CompanionTheory.CuspGL.cuspDiscreteDecompositionGL_of_compact | exact GlobalTheory.CompanionTheory.CuspGL.cuspDiscreteDecompositionGL_of_compact | (intros; apply GlobalTheory.CompanionTheory.CuspGL.cuspDiscreteDecompositionGL_of_compact <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CvecSurjective
section
set_option linter.unusedSectionVars false
set_option maxSynthPendingDepth 1

noncomputable section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RedCov
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal NumberField.AdeleRing
open GroundTheory.Automorphic GroundTheory.Automorphic.Anisotropic

namespace GlobalTheory.CompanionTheory.RedCov.Bridge

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)


variable (F E n) in
abbrev dimN : ℕ := Fintype.card (Fin n × Fin (Module.finrank F E))

def trG : GAd σ J →* GL (Fin (dimN F E n)) (AF F) :=
  (trHom (ι := Fin n) (Module.finBasis F E) (AF F)).comp (matHom (AF F) σ J)


variable (F) in
def cvec (v : Fin n → E) : Fin (dimN F E n) → F := fun p =>
  (Module.finBasis F E).repr (v ((Fintype.equivFin (Fin n × Fin (Module.finrank F E))).symm p).1)
    ((Fintype.equivFin (Fin n × Fin (Module.finrank F E))).symm p).2

theorem cvec_injective : Function.Injective (cvec F : (Fin n → E) → Fin (dimN F E n) → F) := by
  intro u v h
  funext i
  apply (Module.finBasis F E).repr.injective
  ext k
  simpa [cvec] using congrFun h (Fintype.equivFin (Fin n × Fin (Module.finrank F E)) (i, k))

theorem cvec_surjective : Function.Surjective (cvec F : (Fin n → E) → Fin (dimN F E n) → F) := by
  intro x
  refine ⟨fun i => (Module.finBasis F E).equivFun.symm fun k => x (Fintype.equivFin _ (i, k)), ?_⟩
  funext p
  simp [cvec, Module.Basis.equivFun_symm_apply, Finsupp.single_apply]

theorem cvec_ne_zero {v : Fin n → E} (hv : v ≠ 0) : cvec F v ≠ 0 := by
  intro h
  apply hv
  apply cvec_injective (F := F)
  rw [h]
  funext p
  simp [cvec]

theorem ratVec_cvec (v : Fin n → E) :
    Reduction.ratVec (cvec F v) = resVec (ι := Fin n) (Module.finBasis F E) (AF F) (ratV F v) := by
  funext p
  simp only [Reduction.ratVec, cvec, resVec, Function.comp_apply, coordsVec, coords, ratV, inclR]
  simp [Algebra.TensorProduct.basis_repr_tmul]

theorem hv_eq (ξ : Fin n → AF F ⊗[F] E) :
    hv ξ = Reduction.adelicNorm (resVec (ι := Fin n) (Module.finBasis F E) (AF F) ξ) := rfl

theorem hgt_eq (g : GAd σ J) (v : Fin n → E) : hgt σ J g v = Reduction.height (trG σ J g) (cvec F v) := by
  rw [Reduction.height, ratVec_cvec, trG, MonoidHom.comp_apply, resVec_vecMul_trHom, hgt, hv_eq, map_inv]

section Top

attribute [local instance] tensorTopology finite_of_isQuadraticExtension isModuleTopology_tensor
  isTopologicalRing_tensor

theorem continuous_trG : Continuous (trG σ J) :=
  (continuous_trHom (ι := Fin n) (Module.finBasis F E) (AF F)).comp (isEmbedding_matHom (AF F) σ J).continuous

end Top

theorem exists_hgt_le {C : Set (GAd σ J)} (hC : IsCompact C) {v : Fin n → E} (hv : v ≠ 0) :
    ∃ B : ℝ, ∀ c ∈ C, hgt σ J c v ≤ B := by
  obtain ⟨P, -, hP⟩ := Reduction.exists_adelicNorm_vecMul_le_mul (hC.image (continuous_trG σ J))
  refine ⟨P * Reduction.adelicNorm (Reduction.ratVec (cvec F v)), fun c hc => ?_⟩
  rw [hgt_eq]
  exact hP _ ⟨c, hc, rfl⟩ _ (Reduction.hasFiniteContent_ratVec (cvec_ne_zero hv))

end GlobalTheory.CompanionTheory.RedCov.Bridge
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DenominatorBoundByHeightStatement
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
open GlobalTheory.Doubling (absE)
open GlobalTheory.CompanionTheory.GodementH
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.denominator_bound_by_height : ∀ (F : Type) [Field F] [NumberField F] (y : F), ∃ m : ℕ, 0 < m ∧ (m : ℝ≥0) ≤ ∏ᶠ v : Pl (F := F), max 1 ‖algebraMap F (Fv F v) y‖₊ ∧
    IsIntegral ℤ ((m : F) * y) := by
  first | exact @GlobalTheory.CompanionTheory.GodementH.Den.denominator_le | exact GlobalTheory.CompanionTheory.GodementH.Den.denominator_le | (intros; apply GlobalTheory.CompanionTheory.GodementH.Den.denominator_le <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsNearMinimalVector
section
noncomputable section
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RedCov
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.CompanionTheory.RedCov

open GroundTheory.Automorphic GroundTheory.Automorphic.Anisotropic GroundTheory.Automorphic.Reduction

section NearMin

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {n : ℕ}

def ratCoords [Algebra.IsQuadraticExtension F E] (u : Fin n → E) :
    Fin (Fintype.card (Fin n × Fin (Module.finrank F E))) → F :=
  resVec (Module.finBasis F E) F (fun i => inclR (F := F) F (u i))

theorem hv_eq_adelicNorm_resVec [Algebra.IsQuadraticExtension F E] (ξ : Fin n → AF F ⊗[F] E) :
    hv (F := F) (E := E) ξ = adelicNorm (resVec (Module.finBasis F E) (AF F) ξ) := rfl

theorem ratCoords_ne_zero [Algebra.IsQuadraticExtension F E] {u : Fin n → E} (hu : u ≠ 0) :
    ratCoords (F := F) u ≠ 0 := by
  intro h0
  apply hu
  have h1 : (fun i => inclR (F := F) F (u i)) = fun _ : Fin n => (0 : F ⊗[F] E) := by
    apply resVec_injective (Module.finBasis F E) F
    rw [show resVec (Module.finBasis F E) F (fun i => inclR (F := F) F (u i)) = 0 from h0]
    funext p
    simp [resVec, coordsVec]
  funext i
  have h2 := congrFun h1 i
  exact Algebra.TensorProduct.includeRight_injective (algebraMap F F).injective
    (h2.trans (map_zero _).symm)

theorem resVec_ratV [Algebra.IsQuadraticExtension F E] (u : Fin n → E) :
    resVec (Module.finBasis F E) (AF F) (ratV F u) = ratVec (ratCoords (F := F) u) := by
  have h := resVec_baseMap (Module.finBasis F E) (Algebra.ofId F (AF F))
    (fun i => inclR (F := F) F (u i))
  have e : (fun i => baseMap (Algebra.ofId F (AF F)) (inclR (F := F) F (u i))) = ratV F u := by
    funext i
    simp [ratV, inclR, baseMap]
  rw [e] at h
  rw [h]
  rfl

variable (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E)

theorem exists_pos_le_hgt [Algebra.IsQuadraticExtension F E] (g : GAd σ J) :
    ∃ c : ℝ, 0 < c ∧ ∀ u : Fin n → E, u ≠ 0 → c ≤ hgt σ J g u := by
  set T := trHom (Module.finBasis F E) (AF F) (matHom _ σ J g) with hT
  obtain ⟨P, hP, h⟩ := exists_adelicNorm_vecMul_le_mul (K := F) (C := {T⁻¹}) isCompact_singleton
  refine ⟨1 / P, one_div_pos.2 hP, fun u hu => ?_⟩
  have hx := ratCoords_ne_zero (F := F) hu
  have e2 : hgt σ J g u = adelicNorm (ratVec (ratCoords (F := F) u) ᵥ* (T : Matrix (Fin (Fintype.card (Fin n × Fin (Module.finrank F E))))
      (Fin (Fintype.card (Fin n × Fin (Module.finrank F E)))) (AF F))) := by
    rw [hT, ← resVec_ratV, resVec_vecMul_trHom, ← hv_eq_adelicNorm_resVec, hgt, map_inv]
  have h3 := h T⁻¹ rfl _ ((hasFiniteContent_ratVec hx).vecMul T)
  rw [← e2, Matrix.vecMul_vecMul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
    Matrix.vecMul_one] at h3
  rw [div_le_iff₀ hP, mul_comm]
  exact (one_le_adelicNorm_ratVec hx).trans h3

end NearMin

theorem exists_isotropic_of_isWittFrame {F E : Type} [Field F] [Field E] [Algebra F E]
    {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {r : ℕ}
    {X Y : Matrix (Fin n) (Fin (r + 1)) E} (h : IsWittFrame σ J X Y) :
    ∃ v : Fin n → E, v ≠ 0 ∧ hE σ J v v = 0 := by
  refine ⟨Xᵀ 0, fun h0 => ?_, ?_⟩
  · have h1 := congrFun (congrFun h.xy 0) 0
    have hc : ∀ i, X i 0 = 0 := fun i => congrFun h0 i
    simp [cT, Matrix.mul_apply, hc] at h1
  · have h1 := congrFun (congrFun h.xx 0) 0
    simp only [cT, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul, Matrix.zero_apply] at h1
    rw [Finset.sum_comm] at h1
    simpa [hE, Formalism.UG.hform] using h1

theorem exists_nearMin : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E), IsWittFrame σ J X Y → ∀ g : GAd σ J, ∃ v, NearMin σ J g v := by
  intro F E _ _ _ _ _ σ hCM n J _ r X Y hW g
  haveI : Algebra.IsQuadraticExtension F E := ⟨hCM.2.2.1⟩
  obtain ⟨c, hc, hlow⟩ := exists_pos_le_hgt σ J g
  obtain ⟨v₀, hv₀, hi₀⟩ := exists_isotropic_of_isWittFrame hW
  let S : Set ℝ := {t | ∃ u : Fin n → E, u ≠ 0 ∧ hE σ J u u = 0 ∧ t = hgt σ J g u}
  have hne : S.Nonempty := ⟨_, v₀, hv₀, hi₀, rfl⟩
  have hbdd : BddBelow S := ⟨c, by rintro _ ⟨u, hu, -, rfl⟩; exact hlow u hu⟩
  have hm : c ≤ sInf S := le_csInf hne (by rintro _ ⟨u, hu, -, rfl⟩; exact hlow u hu)
  have hm0 : 0 < sInf S := hc.trans_le hm
  obtain ⟨_, ⟨v, hv, hi, rfl⟩, hlt⟩ := exists_lt_of_csInf_lt hne (show sInf S < 2 * sInf S by linarith)
  refine ⟨v, hv, hi, fun u hu hiu => ?_⟩
  have : sInf S ≤ hgt σ J g u := csInf_le hbdd ⟨u, hu, hiu, rfl⟩
  linarith

end GlobalTheory.CompanionTheory.RedCov

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteAdelicRestrictionMeasureStatement
section
open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL
open GroundTheory.Automorphic
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_adelic_restriction_measure : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (μ : Measure (GA E a))
    [μ.IsHaarMeasure] [MeasurableSpace (AutomorphicForm.archGroup E a)]
    [BorelSpace (AutomorphicForm.archGroup E a)] (U : Set (AdelicGLn.FiniteAdelicGL E a)),
    IsCompact U → U ∈ 𝓝 (1 : AdelicGLn.FiniteAdelicGL E a) →
    ((μ.restrict ((fun h : GA E a => (AdelicGLn.prodEquiv E a h).2) ⁻¹' U)).map
      (fun h : GA E a => AutomorphicForm.archEquiv E a (AdelicGLn.prodEquiv E a h).1)).IsHaarMeasure := by
  first | exact @GlobalTheory.CompanionTheory.GrowthHaar.isHaarMeasure_map_restrict | exact GlobalTheory.CompanionTheory.GrowthHaar.isHaarMeasure_map_restrict | (intros; apply GlobalTheory.CompanionTheory.GrowthHaar.isHaarMeasure_map_restrict <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FinitePlaceMinorHeightBoundStatement
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
open GlobalTheory.Doubling (absE)
open GlobalTheory.CompanionTheory.GodementH
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_place_minor_height_bound : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (v : Pl (F := F)) (X : GL ι (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (κ : Matrix ι ι (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))),
    (∀ i j, absFin F v (compFin F E v (κ i j)) ≤ 1) → ∀ f e : Fin n → ι,
    absFin F v (compFin F E v ((X.1 * κ).submatrix f e).det) ≤ htFin F v (Formalism.UG.bc (compFin F E v) X) ^ n := by
  first | exact @GlobalTheory.CompanionTheory.GodementH.absFin_minor_mul_le | exact GlobalTheory.CompanionTheory.GodementH.absFin_minor_mul_le | (intros; apply GlobalTheory.CompanionTheory.GodementH.absFin_minor_mul_le <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeckeCosetSumCompactStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcN.F2
open scoped Classical TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hecke_coset_sum_compact : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n a b : ℕ) (h : a + b = n) (w : Pl E) (K' : Subgroup (GLw n w)), IsOpen (K' : Set (GLw n w)) → K' ≤ GlobalTheory.LFun.KGL w (n := n) → (∀ k ∈ GlobalTheory.LFun.KGL w (n := n), ∀ k' ∈ K', k * k' * k⁻¹ ∈ K') → ∀ X : Finset (GLw n w), (∀ x ∈ X, x ∈ GlobalTheory.LFun.KGL w (n := n)) → (∀ k ∈ GlobalTheory.LFun.KGL w (n := n), ∃! x ∈ X, x⁻¹ * k ∈ K') → ∀ φ : GLw n w → ℂ, (∀ g, ∀ k ∈ K', φ (g * k) = φ g) → HasCompactSupport φ → hint (GlobalTheory.LFun.KGL w (n := n)) φ = ((X.card : ℂ))⁻¹ * ∑ y ∈ X, hint ((GlobalTheory.LFun.KGL w (n := a)).prod (GlobalTheory.LFun.KGL w (n := b))) fun m => hint (intMat a b w) fun Y => φ (blk h w m (Multiplicative.toAdd Y) * y) := by
  first | exact @GlobalTheory.CompanionTheory.IntDec.integral_decomposition | exact GlobalTheory.CompanionTheory.IntDec.integral_decomposition | (intros; apply GlobalTheory.CompanionTheory.IntDec.integral_decomposition <;> assumption)
end

