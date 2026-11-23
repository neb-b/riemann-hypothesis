module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
public import Mathlib
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0593
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3126
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3130
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0001
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0109
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0110
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3128
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0107
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ThetaIntegralKernelLieAlgebraStable
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1561
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0011
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0108

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BottomTripleIntegralEqConstMulLocal
section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.ConstRatio
theorem bottom_triple_integral_factorization (hPr : _root_.GlobalTheory.FunPr.ThetaLocalInputs) (hK : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree)
    (hM : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching) (hL : LNe) :
    GBig fun {D} T _ _ G _ _ _ _ => ∀ W : G.Weil, IsStdChar D W.ψ (-1) → ∀ (i j : Fin D.R.m) (A A' WW : HSp D)
      (X : GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.Tri T A A' WW), IsBottomTri W i j X → ∃ lam : T → ℂ, GlobalTheory.ConstRatio.Factor X W.ψ W.θ lam := by
  obtain ⟨c, h⟩ := _root_.GlobalTheory.T.bottom_triple_integral_factorization_of_real hPr hK hM
  obtain ⟨c', h'⟩ := _root_.GlobalTheory.T.first_occurrence_theta_lift_ne_zero hPr hK hM hL
  refine ⟨max c c', fun ε CF hCF => ?_⟩
  obtain ⟨C0, x0, h⟩ := h ε CF (le_of_max_le_left hCF)
  obtain ⟨C1, x1, h'⟩ := h' ε CF (le_of_max_le_right hCF)
  refine ⟨max C0 C1, max x0 x1, fun C hC D large₂ a b r T Lc μ hLc G W hW i j A A' WW X hX => ?_⟩
  obtain ⟨Pi, p, p', J, hs, hJ, hlam, hI'⟩ :=
    h C (le_of_max_le_left hC) D large₂ a (le_of_max_le_left b) r T Lc μ hLc G W hW i j A A' WW X hX
  have hnv := h' C (le_of_max_le_right hC) D large₂ a (le_of_max_le_right b) r T Lc μ hLc G W i j A A' WW X hX
  obtain ⟨P', g', hg'⟩ := (hnv μ).2
  have hP' : p' P' ≠ 0 := fun h0 => hg' (by rw [hI' μ P', h0]; simp)
  choose lam hlam using hlam
  have key : ∀ t, lam t ≠ 0 ∧ Function.Injective (J t) := fun t => by
    obtain ⟨P, g, hPg⟩ := (hnv t).1
    rw [hlam t P] at hPg
    refine ⟨fun h0 => hPg (by simp [h0]), (hJ t).resolve_left fun h0 => hPg (by simp [h0])⟩
  refine ⟨lam, fun t => (key t).1, Pi, p, p', J, hs, fun t => (key t).2, fun t P g => (hX.integrable t).1 P g,
    fun t P => hlam t P, fun t P' _ => hI' t P', P', hP', fun t g => (hX.integrable t).2 P' g⟩
end GlobalTheory.ConstRatio
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bottom_triple_integral_eq_const_mul_local : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching → LNe → GBig fun {D} T _ _ G _ _ _ _ => ∀ W : G.Weil, IsStdChar D W.ψ (-1) → ∀ (i j : Fin D.R.m) (A A' WW : HSp D) (X : GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.Tri T A A' WW), IsBottomTri W i j X → ∃ lam : T → ℂ, GlobalTheory.ConstRatio.Factor X W.ψ W.θ lam := by
  first | exact @_root_.GlobalTheory.ConstRatio.bottom_triple_integral_factorization | exact _root_.GlobalTheory.ConstRatio.bottom_triple_integral_factorization | (intros; apply _root_.GlobalTheory.ConstRatio.bottom_triple_integral_factorization <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ThetaStageKernelCharacterization
section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.StageKer
end GlobalTheory.StageKer
theorem GlobalTheory.StageKer.theta_stage_kernel_eq : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
  GBig fun {D} T _ _ G μ₀ _ _ _ => ∀ (W : G.Weil) (S : GridChoice W Set.univ), IsStdChar D W.ψ (-1) →
    NumbersIn D.what₂.embLL S μ₀ → ∀ (i j : Fin D.R.m) (p q : ℕ) (A A' WW : HSp D) (X : Tri T A A' WW), GlobalTheory.SqTower.IsStageC W i j p q X →
      ∀ t t' P, X.I W.ψ W.θ t P = 0 → X.I W.ψ W.θ t' P = 0 := by
  intro hP hK hL
  obtain ⟨c, hc⟩ := GlobalTheory.SqTop.Model.gBig_and (GlobalTheory.SqTop.Model.gBig_and _root_.GlobalTheory.StageDict.stage_dictionary (_root_.GlobalTheory.T.theta_stage_liftable hP hK hL)) (_root_.GlobalTheory.T.theta_small_rank_stage_holds hP hK hL)
  refine ⟨c, fun ε CF hCF => ?_⟩
  obtain ⟨C0, x0, h⟩ := hc ε CF hCF
  refine ⟨C0, x0, fun C hC D large₂ a b r T Lc μ hLc G W S hW hN i j p q A A' WW X hX => ?_⟩
  obtain ⟨⟨h1, h3⟩, h4⟩ := h C hC D large₂ a b r T Lc μ hLc G
  obtain ⟨FA, FA', FW, ea, eb, hD⟩ := h1 W S hW hN i j p q A A' WW X hX
  obtain ⟨lam, s, hlam, hs⟩ := h3 W S hW hN i j p q A A' WW X hX
  obtain ⟨P0, hc0, hne0⟩ := h4 W S hW hN i j p q A A' WW X hX
  obtain ⟨Pr, qP, hq⟩ := _root_.GlobalTheory.T.thetaIntegral_factors_through_kType hP hK hL D W.ψ W.θ W.ψ_std W.θ_is A A' WW FA FA' FW ea eb
  have hIs := hX.2.2.2.2.2.2.2
  have key : ∀ t P, X.I W.ψ W.θ t P = 0 ↔ qP P = 0 := by
    intro t
    obtain ⟨hTr, hInf, hf, -, hk, -⟩ := hD t
    obtain ⟨Pf, y, J, hJ, hI⟩ := hq _ _ hTr hInf X.m X.fd hIs.meas (X.ω t) (hIs.weil t) (X.f t) hf
    have eI : ∀ P, X.I W.ψ W.θ t P = J (qP P ⊗ₜ y) := fun P => by
      rw [← hI P]; funext h; simp only [GlobalTheory.SquareComm.thetaInt, GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.Tri.I, hk]
    have hne : X.I W.ψ W.θ t (s P0) ≠ 0 := by
      rw [hs t P0 (hc0 t)]; exact smul_ne_zero (hlam t) (hne0 t)
    have hy : y ≠ 0 := by
      rintro rfl; apply hne; rw [eI, TensorProduct.tmul_zero, map_zero]
    have hJi : Function.Injective J := hJ.resolve_left (by
      intro hJ0; apply hne; rw [eI, hJ0]; rfl)
    intro P
    rw [eI, map_eq_zero_iff J hJi]
    constructor
    · intro h0; by_contra hq0; exact GlobalTheory.StageKer.tmul_ne_zero_of_ne hq0 hy h0
    · intro h0; rw [h0, TensorProduct.zero_tmul]
  intro t t' P h0
  exact (key t' P).2 ((key t P).1 h0)
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_stage_kernel_characterization : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
  GBig fun {D} T _ _ G μ₀ _ _ _ => ∀ (W : G.Weil) (S : GridChoice W Set.univ), IsStdChar D W.ψ (-1) →
    NumbersIn D.what₂.embLL S μ₀ → ∀ (i j : Fin D.R.m) (p q : ℕ) (A A' WW : HSp D) (X : Tri T A A' WW), GlobalTheory.SqTower.IsStageC W i j p q X →
      ∀ t t' P, X.I W.ψ W.θ t P = 0 → X.I W.ψ W.θ t' P = 0 := by
  first | exact @_root_.GlobalTheory.StageKer.theta_stage_kernel_eq | exact _root_.GlobalTheory.StageKer.theta_stage_kernel_eq | (intros; apply _root_.GlobalTheory.StageKer.theta_stage_kernel_eq <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TripleExistenceOfTheta
section
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta
open IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
namespace GlobalTheory.SqTop
attribute [local instance] Formalism.BasicNotions.Host.cmStar
theorem triEx_holds_alt : GlobalTheory.Published.HoweDualityReal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree →
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching → LNe → TriEx := by
  intro hH hP hK hM hL
  obtain ⟨CF1, H1⟩ := _root_.GlobalTheory.T.bottom_theta_norm_eq_prod_local_factors hH hP hK hM hL
  obtain ⟨CF2, H2⟩ := _root_.GlobalTheory.T.first_occurrence_theta_lift_ne_zero hP hK hM hL
  refine ⟨max CF1 CF2, fun ε CF hCF => ?_⟩
  obtain ⟨C1, x1, G1⟩ := H1 ε CF (le_trans (le_max_left _ _) hCF)
  obtain ⟨C2, x2, G2⟩ := H2 ε CF (le_trans (le_max_right _ _) hCF)
  refine ⟨max C1 C2, max x1 x2, fun C hC D large₂ he hx hR T Lc μ₀ hμ G W _ i j => ?_⟩
  obtain ⟨A, A', WW, X, hX⟩ := GlobalTheory.RowTest.exists_bottomTri hμ G W i j
  obtain ⟨Pi, p, p', J, hs, ⟨P', hP'⟩, hJ, hI, hI'⟩ :=
    G1 C (le_trans (le_max_left _ _) hC) D large₂ he (le_trans (le_max_left _ _) hx) hR T Lc μ₀ hμ G W i j A A' WW X hX
  have hN := G2 C (le_trans (le_max_right _ _) hC) D large₂ he (le_trans (le_max_right _ _) hx) hR T Lc μ₀ hμ G W i j A A' WW X hX
  choose lam hlam using hI
  have hinj : ∀ t, Function.Injective (J t) := fun t => by
    refine (hJ t).resolve_left fun h0 => ?_
    obtain ⟨Q, h, hQ⟩ := (hN t).2
    exact hQ (by rw [hI' t Q, h0]; rfl)
  have hlam0 : ∀ t, lam t ≠ 0 := fun t h0 => by
    obtain ⟨Q, h, hQ⟩ := (hN t).1
    exact hQ (by rw [hlam t Q, h0, zero_smul]; rfl)
  have hF : GlobalTheory.ConstRatio.Factor X W.ψ W.θ lam :=
    ⟨hlam0, Pi, p, p', J, hs, hinj, fun t P h => (hX.integrable t).1 P h, hlam, fun t Q _ => hI' t Q,
      P', hP', fun t h => (hX.integrable t).2 P' h⟩
  haveI : Nonempty T := ⟨μ₀⟩
  exact ⟨A, A', WW, X, lam, hX, hF.isConst⟩
end GlobalTheory.SqTop
end
end

section
open GlobalTheory.SqTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.triEx_of_howe_duality_real : GlobalTheory.Published.HoweDualityReal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching → LNe → TriEx := by
  first | exact @_root_.GlobalTheory.SqTop.triEx_holds_alt | exact _root_.GlobalTheory.SqTop.triEx_holds_alt | (intros; apply _root_.GlobalTheory.SqTop.triEx_holds_alt <;> assumption)
end
end

