module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0438
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0432
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0015
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0556
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.VacuumSplitPlaceIndicatorBase
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1227
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1234
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0433
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0295
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1515
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilModelRationalStructure
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0290
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0305
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0397
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0002

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedUpwardThetaIntegralConverges
section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped ComplexConjugate
open GlobalTheory.UpArrowConv
namespace GlobalTheory.UpArrowConv
theorem upward_theta_integral_converges : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ i, i < D.R.m → ∀ Φ, IsThetaFunO R.ψ (GlobalTheory.Grid.neg (G.P (i + 1)).V) (G.P i).V Φ → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.P i) φ → (∀ h, IntegrableOn (fun g => starRingEnd ℂ (thetaKO (G.dn i).ω h g Φ) * φ g) (G.mP i).fd (G.mP i).ν) := by
  intro _ hP D _ G₀ _ _ Pl0 T A Ks _ _ _ R G hR hG i hi Φ hΦ φ hφ h
  have hω := (hG.arrows.dn i hi).weil
  have hm := (hG.meas.P i hi.le).2 (by omega)
  have key := conj_thetaKO_mul_integrableOn hP.cuspRapidDecay hR.inf hω hΦ hm.1.1 hm.2 hφ.1 hφ.2.1
    ((GlobalTheory.Grid.ofSgn true _).symm h)
  have e : (fun g => starRingEnd ℂ (thetaKO (G.dn i).ω h g Φ) * φ g) =
      fun g => starRingEnd ℂ (thetaKO ((G.dn i).ω.toSgn true) ((GlobalTheory.Grid.ofSgn true _).symm h) g Φ) * φ g :=
    funext fun g => by rw [thetaKO_toSgn]
  rw [e]
  exact key
end GlobalTheory.UpArrowConv
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_upward_theta_integral_converges : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ i, i < D.R.m → ∀ Φ, IsThetaFunO R.ψ (GlobalTheory.Grid.neg (G.P (i + 1)).V) (G.P i).V Φ → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.P i) φ → (∀ h, IntegrableOn (fun g => starRingEnd ℂ (thetaKO (G.dn i).ω h g Φ) * φ g) (G.mP i).fd (G.mP i).ν) := by
  first | exact @_root_.GlobalTheory.UpArrowConv.upward_theta_integral_converges | exact _root_.GlobalTheory.UpArrowConv.upward_theta_integral_converges | (intros; apply _root_.GlobalTheory.UpArrowConv.upward_theta_integral_converges <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedUpwardThetaLiftIsSmoothAutomorphic
section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
noncomputable section
namespace GlobalTheory.UpConjLift
theorem upward_theta_lift_isSmoothAutomorphic : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ i, i < D.R.m → ∀ Φ, IsThetaFunO R.ψ (GlobalTheory.Grid.neg (G.P (i + 1)).V) (G.P i).V Φ → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.P i) φ → (∀ h, IntegrableOn (fun g => starRingEnd ℂ (thetaKO (G.dn i).ω h g Φ) * φ g) (G.mP i).fd (G.mP i).ν) → IsAutFunSm R.θ (G.P (i + 1)).V (fun h => ∫ g in (G.mP i).fd, starRingEnd ℂ (thetaKO (G.dn i).ω h g Φ) * φ g ∂(G.mP i).ν) := by
  intro _ hPr D _ G₀ _ _ Pl0 T A Ks _ _ _ R G hR hG i hi Φ hΦ φ hφ _
  have hq : GlobalTheory.Mem.Th.IsQuot (G.P i).V (G.mP i).ν (G.mP i).fd := by
    have := (hG.meas.P i hi.le).2 (by omega)
    exact ⟨this.1.1, this.2⟩
  exact (conj_lift hPr.cuspRapidDecay hR.inf (G.dn i).ω (hG.arrows.dn i hi).weil hΦ hq ⟨hφ.1, hφ.2.1⟩).2
end GlobalTheory.UpConjLift
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_upward_theta_lift_isSmoothAutomorphic : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ i, i < D.R.m → ∀ Φ, IsThetaFunO R.ψ (GlobalTheory.Grid.neg (G.P (i + 1)).V) (G.P i).V Φ → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.P i) φ → (∀ h, IntegrableOn (fun g => starRingEnd ℂ (thetaKO (G.dn i).ω h g Φ) * φ g) (G.mP i).fd (G.mP i).ν) → IsAutFunSm R.θ (G.P (i + 1)).V (fun h => ∫ g in (G.mP i).fd, starRingEnd ℂ (thetaKO (G.dn i).ω h g Φ) * φ g ∂(G.mP i).ν) := by
  first | exact @_root_.GlobalTheory.UpConjLift.upward_theta_lift_isSmoothAutomorphic | exact _root_.GlobalTheory.UpConjLift.upward_theta_lift_isSmoothAutomorphic | (intros; apply _root_.GlobalTheory.UpConjLift.upward_theta_lift_isSmoothAutomorphic <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedWeilRepresentationConvergence
section
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
namespace GlobalTheory.WeilConv
theorem twisted_weil_representation_convergence : GlobalTheory.Published.SiegelSetUnitary → _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.SquareSt.WeilConvergence :=
  fun hRT _ => weilConvergence_of_siegelSet hRT
end GlobalTheory.WeilConv
end
end

section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_theta_integral_converges : GlobalTheory.Published.SiegelSetUnitary → _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.SquareSt.WeilConvergence := by
  first | exact @_root_.GlobalTheory.WeilConv.twisted_weil_representation_convergence | exact _root_.GlobalTheory.WeilConv.twisted_weil_representation_convergence | (intros; apply _root_.GlobalTheory.WeilConv.twisted_weil_representation_convergence <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.VDoubleEigenspaceSplitOfLine
section
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix
noncomputable section
namespace GlobalTheory.VDblEigSplit
theorem vDouble_eigenfunction_split : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F), Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) v → v ∉ X.T → PsiUnr B.ψ v → (2 : 𝓞 F) ∉ v.asIdeal →
    G.M.vac v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 →
    ∀ (d' : Darboux (symp (cA σ) (-1 : AE F E) (incM F G.W.J) (incM F G.V.J)) (Fin a × Fin (a + a'))),
    (∀ x : Matrix (Fin a) (Fin (a + a')) (AE F E), d'.e xᵀ = G.M.co.e x) →
    ∀ (dd : Darboux (symp (cA σ) (-1 : AE F E) (incM F G.W.J) (dbl (incM F G.V.J))) ((Fin a × Fin (a + a')) ⊕ (Fin a × Fin (a + a'))))
      (omd : GlobalTheory.DblVac.UD σ G.V →* Module.End ℂ (((Fin a × Fin (a + a')) ⊕ (Fin a × Fin (a + a')) → AF F) → ℂ)),
    IsDblCoord (cA σ) (-1 : AE F E) (incM F G.W.J) (incM F G.V.J) d' dd →
    IsUWeilSplit (cA σ) (adeleClass F) B.ψ (-1 : AE F E) (incM F G.W.J) (dbl (incM F G.V.J)) dd (X.β / X.α) (diagCols (Fin a)) omd →
    ∀ r : (Fin a × Fin (a + a') → AF F) → ℂ, Rest (evFin F v) (G.M.vac v) r →
    ∀ g ∈ GlobalTheory.DblVac.KD σ G.V v, ∃ μ : ℂ,
      omd g (boxFun (tens (evFin F v) (G.M.vac v) r) (fun x => star (tens (evFin F v) (G.M.vac v) r x))) =
        μ • boxFun (tens (evFin F v) (G.M.vac v) r) (fun x => star (tens (evFin F v) (G.M.vac v) r x)) := by
  intro _ F E _ _ _ _ _ σ B a a' G X om om' hT v _ _ hunr _ _
  exact vdbl_eigen_of_unr F E σ B a a' G X om om' hT v hunr
end GlobalTheory.VDblEigSplit
end
end

section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.vDouble_eigenspace_split_of_line : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F), Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) v → v ∉ X.T → PsiUnr B.ψ v → (2 : 𝓞 F) ∉ v.asIdeal →
    G.M.vac v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 →
    ∀ (d' : Darboux (symp (cA σ) (-1 : AE F E) (incM F G.W.J) (incM F G.V.J)) (Fin a × Fin (a + a'))),
    (∀ x : Matrix (Fin a) (Fin (a + a')) (AE F E), d'.e xᵀ = G.M.co.e x) →
    ∀ (dd : Darboux (symp (cA σ) (-1 : AE F E) (incM F G.W.J) (dbl (incM F G.V.J))) ((Fin a × Fin (a + a')) ⊕ (Fin a × Fin (a + a'))))
      (omd : GlobalTheory.DblVac.UD σ G.V →* Module.End ℂ (((Fin a × Fin (a + a')) ⊕ (Fin a × Fin (a + a')) → AF F) → ℂ)),
    IsDblCoord (cA σ) (-1 : AE F E) (incM F G.W.J) (incM F G.V.J) d' dd →
    IsUWeilSplit (cA σ) (adeleClass F) B.ψ (-1 : AE F E) (incM F G.W.J) (dbl (incM F G.V.J)) dd (X.β / X.α) (diagCols (Fin a)) omd →
    ∀ r : (Fin a × Fin (a + a') → AF F) → ℂ, Rest (evFin F v) (G.M.vac v) r →
    ∀ g ∈ GlobalTheory.DblVac.KD σ G.V v, ∃ μ : ℂ,
      omd g (boxFun (tens (evFin F v) (G.M.vac v) r) (fun x => star (tens (evFin F v) (G.M.vac v) r x))) =
        μ • boxFun (tens (evFin F v) (G.M.vac v) r) (fun x => star (tens (evFin F v) (G.M.vac v) r x)) := by
  first | exact @_root_.GlobalTheory.VDblEigSplit.vDouble_eigenfunction_split | exact _root_.GlobalTheory.VDblEigSplit.vDouble_eigenfunction_split | (intros; apply _root_.GlobalTheory.VDblEigSplit.vDouble_eigenfunction_split <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.WeilCoinvariantsVanishOnLineDerivatives
section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
noncomputable section
namespace GlobalTheory.CoinvLine
variable {D : D7}
theorem coinvariants_kill_line_derivative : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁)
    (B : Fr X) (α β : (AE D)ˣ →* Circle) (ωA : WRep W X) (ωB : WRep W₁ X) (Pi : ModuleCat.{0} ℂ)
    (rf : GA D X → Module.End ℂ Pi) (rl : D.what₂.Tau → Matrix (Fin X.rank) (Fin X.rank) ℂ → Module.End ℂ Pi)
    (p : (WO W X → ℂ) →ₗ[ℂ] Pi) (p' : (WO W₁ X → ℂ) →ₗ[ℂ] Pi),
    IsInfFam θ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ → IsTriple W W₁ X α β → IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p' →
    ∀ (Vs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E W₁.rank) (hJ : Vs.J = (-1 : D.host.E) • W₁.gram),
    ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines D.sp.cm.sig Vs, ∀ Ψ ∈ algF ψ θ false A₁ B, ∀ Ψ₁ ∈ algF ψ θ false A₁ B,
    (∀ z, HasDerivAt (fun t : ℝ => ωB (GlobalTheory.ConjUTransport.conjUInv W₁ (-1) (neg_ne_zero.2 one_ne_zero) hJ
      (γ (Multiplicative.ofAdd t)), 1) Ψ z) (Ψ₁ z) 0) → p' Ψ₁ = 0 := by
  intro _ D ψ θ W W₁ X A A₁ B α β ωA ωB Pi rf rl p p' hθ _ _ hM Vs hJ γ hγ Ψ hΨ Ψ₁ _ hder
  have hω : IsWeilDatumO ψ W₁ X α (α / β) ωB := hM.weilB
  have hψ : IsStdChar D ψ (-1) := hω.std
  have hc : (-1 : D.host.E) ≠ 0 := neg_ne_zero.2 one_ne_zero
  obtain ⟨g, h1, h2, h3, h4⟩ := GlobalTheory.OmegaDer.exists_line W₁ hc Vs hJ γ hγ
  have hg : ∀ t : ℝ, GlobalTheory.ConjUTransport.conjUInv W₁ (-1) (neg_ne_zero.2 one_ne_zero) hJ (γ (Multiplicative.ofAdd t)) = g t :=
    fun t => by rw [← h1 t]; exact (GlobalTheory.ConjUTransport.conjEquiv W₁ (-1) hc hJ).left_inv (g t)
  obtain ⟨Z, hZ⟩ := GlobalTheory.OmegaDer.exists_expInf hθ W₁ g h2 h3 h4
  have hst := fun τ => hM.mapB.stabM.2 τ (Z τ).1 (Z τ).2 Ψ hΨ
  choose Ψ' hΨ' hd using hst
  have hk : ∀ τ, p' (Ψ' τ) = 0 := fun τ => hM.mapB.invl τ (Z τ).1 (Z τ).2 Ψ hΨ (Ψ' τ) (hΨ' τ) (hd τ)
  have hsum : Ψ₁ = ∑ τ, Ψ' τ := by
    funext z
    rw [Finset.sum_apply]
    have e1 : (fun t : ℝ => ωB (GlobalTheory.ConjUTransport.conjUInv W₁ (-1) (neg_ne_zero.2 one_ne_zero) hJ
        (γ (Multiplicative.ofAdd t)), 1) Ψ z) = fun t : ℝ => ωB (GlobalTheory.SmoothForms.expInf θ W₁ (t • Z), 1) Ψ z := by
      funext t; rw [hg t, hZ t]
    have hz := hder z
    rw [e1] at hz
    rcases isEmpty_or_nonempty D.what₂.Tau with h0 | h0
    · have e : ∀ t : ℝ, t • Z = Z := fun t => funext fun τ => isEmptyElim τ
      simp only [e] at hz
      simp only [Finset.univ_eq_empty, Finset.sum_empty]
      exact hz.unique (hasDerivAt_const _ _)
    · let 𝒮 : Set (GA D W₁ → ℂ) := {φ | ∃ f z, IsThetaFunO ψ W₁ X f ∧ φ = fun g => ωB (g, 1) f z}
      have hΘ := isThetaFunO_of_mem_algF hθ hψ A₁ B hΨ
      refine hz.unique (GlobalTheory.OmegaDer.der_sum hθ 𝒮 ?_ ?_ ⟨Ψ, z, hΘ, rfl⟩ Z (fun τ => Ψ' τ z) fun τ => hd τ z)
      · rintro _ ⟨f, z, hf, rfl⟩
        exact (hω.om_cont f hf z).comp (continuous_id.prodMk continuous_const)
      · rintro _ ⟨f, z, hf, rfl⟩ τ' Y hY
        obtain ⟨G, hG', h⟩ := GlobalTheory.LieScalar.genS hθ hω τ' Y hY f hf
        refine ⟨_, ⟨G, z, hG', rfl⟩, fun g => ?_⟩
        have := h (g, 1) z
        simpa only [MonoidHom.inl_apply, Prod.mk_mul_mk, mul_one] using this
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hsum, map_sum]
  exact Finset.sum_eq_zero fun τ _ => hk τ
end GlobalTheory.CoinvLine
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_coinvariants_vanish_on_line_derivatives : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁)
    (B : Fr X) (α β : (AE D)ˣ →* Circle) (ωA : WRep W X) (ωB : WRep W₁ X) (Pi : ModuleCat.{0} ℂ)
    (rf : GA D X → Module.End ℂ Pi) (rl : D.what₂.Tau → Matrix (Fin X.rank) (Fin X.rank) ℂ → Module.End ℂ Pi)
    (p : (WO W X → ℂ) →ₗ[ℂ] Pi) (p' : (WO W₁ X → ℂ) →ₗ[ℂ] Pi),
    IsInfFam θ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ → IsTriple W W₁ X α β → IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p' →
    ∀ (Vs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E W₁.rank) (hJ : Vs.J = (-1 : D.host.E) • W₁.gram),
    ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines D.sp.cm.sig Vs, ∀ Ψ ∈ algF ψ θ false A₁ B, ∀ Ψ₁ ∈ algF ψ θ false A₁ B,
    (∀ z, HasDerivAt (fun t : ℝ => ωB (GlobalTheory.ConjUTransport.conjUInv W₁ (-1) (neg_ne_zero.2 one_ne_zero) hJ
      (γ (Multiplicative.ofAdd t)), 1) Ψ z) (Ψ₁ z) 0) → p' Ψ₁ = 0 := by
  first | exact @_root_.GlobalTheory.CoinvLine.coinvariants_kill_line_derivative | exact _root_.GlobalTheory.CoinvLine.coinvariants_kill_line_derivative | (intros; apply _root_.GlobalTheory.CoinvLine.coinvariants_kill_line_derivative <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.WeilModelRationalStructure
section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped ComplexConjugate
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
noncomputable section
namespace GlobalTheory.RealDict.CompactCoinv
section Oriented
variable {D : D7} {V W : HSp D} {θ : InfFam D} {ψ : AddChar (AF D.host.F) ℂ} {χS χT : (AE D)ˣ →* Circle}
  {ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)}
end Oriented
section Theta
end Theta
section Reading
variable {D : D7}
end Reading
end GlobalTheory.RealDict.CompactCoinv
namespace GlobalTheory.RealDict
open GlobalTheory.RealDict.CompactCoinv
theorem sub_mem_map_coinv_alt : _root_.GlobalTheory.FunPr.ThetaLocalInputs →
  ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
  ∀ (ε : Bool) (M X : HSp D) (A : Fr M) (B : Fr X) (χS χT : (AE D)ˣ →* Circle) (ω : WRep M X) (eS eT : D.what₂.Tau → ℚ),
  IsWeil ψ ε M X χS χT ω → (∀ τ, HasInfExp D χS τ (eS τ) ∧ HasInfExp D χT τ (eT τ)) →
  ∀ (Xs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E M.rank) (Ws : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E X.rank)
    (Mo : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model D.sp.cm.sig Xs Ws) (ψ' : AddChar (AF D.host.F) ℂ)
    (χX χW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Xs Ws)
    (τ : ∀ w : InfinitePlace D.host.F, GlobalTheory.AdelicU.EmbOver D.host.E w),
    GlobalTheory.RealDict.PublishedHyps D Xs Ws Mo ψ' χX χW om τ → GlobalTheory.RealDict.IsPairReading ψ ε A B ω Xs Ws Mo ψ' om τ →
    ∀ Φ : PolF D X.rank M.rank →ₗ[ℂ] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf D.host.F (Fin M.rank × Fin X.rank),
    Function.Injective Φ → LinearMap.range Φ = Mo.Pol ψ' τ → GlobalTheory.RealDict.IsFockMap ψ θ ε A B Mo Φ →
      ∀ k ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.KInf D.sp.cm.sig Xs τ, ∀ f ∈ Mo.Pol ψ' τ, ∀ f₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf D.host.F (Fin M.rank × Fin X.rank),
          GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) (om (k, 1)) f f₁ → f₁ - f ∈ (GlobalTheory.RealQuot.coinv ε A B eT).map Φ := by
  intro _ D ψ θ hψ hθ ε M X A B χS χT ω eS eT hω he Xs Ws Mo ψ' χX χW om τ hP hR Φ _ hrange hΦ k hk f hf f₁ hA
  obtain ⟨f₀, r, hvac, h0, hr⟩ := hΦ
  obtain ⟨hCM, -, -, -, -, -, -, -, -, -, hW, -⟩ := hP
  rw [← hrange] at hf
  obtain ⟨P, rfl⟩ := hf
  have hc : sgE (D := D) ε ≠ 0 := by cases ε <;> simp [sgE]
  obtain ⟨g, hgk, hg⟩ := exists_conjU M hc hR.JX k
  obtain ⟨P', hP', hm⟩ := moves_sgn hθ A B hω he hvac h0 g (mem_GinfC_of_conj g _ hg hk.1) (fun t => by
    obtain ⟨t', h1, h2, -⟩ := hR.cart (InfinitePlace.mk ((tauE D t).comp (algebraMap D.host.F D.host.E)))
    obtain rfl := eq_of_conj_over t t' _ h1
    rw [infMat_of_conj hθ hCM g _ hg _ _ h1, ← h2]
    exact hk.2 _) P
  have h1 : GlobalTheory.TripleRead.toUX X (Equiv.refl (Fin X.rank)) hR.JW 1 = 1 := Subtype.ext (Units.ext rfl)
  have h2 := hR.transp _ (hr P).1.2 g 1
  rw [hgk, h1, (hr P).2] at h2
  have h3 := thO_inj Mo hψ (Formalism.L2.Theta.gram_det_ne (sgn ε M))
    (om_mem_schA hW (k, 1) (hr P).1.2) (hr P').1.2 (h2.trans (Eq.trans hP' (hr P').2.symm))
  have hr0 : r ≠ 0 := by
    rintro rfl
    apply h0
    rw [← GlobalTheory.LieScalar.ptF_one (ψ := ψ) (θ := θ) (frSgn ε A) B f₀, ← (hr 1).2]
    funext x
    simp [GlobalTheory.TripleRead.thO, thetaSum, Darboux.rho, schr, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens]
  have h4 : (f₁ : _ → ℂ) = Φ P' := eq_of_tens (hr P).1.1 hr0 ((hA r (hr P).1).symm.trans h3)
  rw [DFunLike.coe_injective h4, ← map_sub]
  exact ⟨_, hm, rfl⟩
end GlobalTheory.RealDict
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped ComplexConjugate
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_model_rational_structure_alt : _root_.GlobalTheory.FunPr.ThetaLocalInputs →
  ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
  ∀ (ε : Bool) (M X : HSp D) (A : Fr M) (B : Fr X) (χS χT : (AE D)ˣ →* Circle) (ω : WRep M X) (eS eT : D.what₂.Tau → ℚ),
  IsWeil ψ ε M X χS χT ω → (∀ τ, HasInfExp D χS τ (eS τ) ∧ HasInfExp D χT τ (eT τ)) →
  ∀ (Xs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E M.rank) (Ws : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E X.rank)
    (Mo : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model D.sp.cm.sig Xs Ws) (ψ' : AddChar (AF D.host.F) ℂ)
    (χX χW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Xs Ws)
    (τ : ∀ w : InfinitePlace D.host.F, GlobalTheory.AdelicU.EmbOver D.host.E w),
    GlobalTheory.RealDict.PublishedHyps D Xs Ws Mo ψ' χX χW om τ → GlobalTheory.RealDict.IsPairReading ψ ε A B ω Xs Ws Mo ψ' om τ →
    ∀ Φ : PolF D X.rank M.rank →ₗ[ℂ] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf D.host.F (Fin M.rank × Fin X.rank),
    Function.Injective Φ → LinearMap.range Φ = Mo.Pol ψ' τ → GlobalTheory.RealDict.IsFockMap ψ θ ε A B Mo Φ →
      ∀ k ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.KInf D.sp.cm.sig Xs τ, ∀ f ∈ Mo.Pol ψ' τ, ∀ f₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf D.host.F (Fin M.rank × Fin X.rank),
          GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) (om (k, 1)) f f₁ → f₁ - f ∈ (GlobalTheory.RealQuot.coinv ε A B eT).map Φ := by
  first | exact @_root_.GlobalTheory.RealDict.sub_mem_map_coinv_alt | exact _root_.GlobalTheory.RealDict.sub_mem_map_coinv_alt | (intros; apply _root_.GlobalTheory.RealDict.sub_mem_map_coinv_alt <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.WeilRepresentationLevelEqConductor
section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open scoped ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.WeilLevel
theorem weil_representation_level_eq_conductor : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (f : WO S T → ℂ), _root_.GlobalTheory.FunPr.ThetaLocalInputs → IsWeilDatumO ψ S T χS χT om → IsThetaFunO ψ S T f → ∃ U : Subgroup (GA D T), IsOpen (U : Set (GA D T)) ∧ ∀ k ∈ U, k ∈ GfC T → om (1, k) f = f := by
  intro D ψ S T χS χT om f _ hW hf
  have hψ := hW.std
  obtain ⟨U, hUo, hU⟩ := hf.level
  obtain ⟨N, K, hNU, hKo, hAR, hKN, hKA⟩ := stab ψ S T hψ U hUo
  have hfN : ∀ u ∈ N, u.map (infPart D) = 0 → heisO ψ S T u f = f := fun u hu h0 => hU u (hNU hu) h0
  obtain ⟨-, hcomp, -⟩ := GlobalTheory.HeisThetaLaws.heis_theta_laws D ψ hψ S T
  have hMV : ∀ k ∈ K, k ∈ GfC T → ∀ g, IsThetaFunO ψ S T g → (∀ u ∈ N, u.map (infPart D) = 0 → heisO ψ S T u g = g) →
      IsThetaFunO ψ S T (om (1, k) g) ∧ ∀ u ∈ N, u.map (infPart D) = 0 → heisO ψ S T u (om (1, k) g) = om (1, k) g := by
    intro k hk hkf g hg hgN
    refine ⟨hW.om_pres _ g hg, fun u hu hu0 => ?_⟩
    obtain ⟨h1, h2⟩ := hKN k⁻¹ (K.inv_mem hk) ((GfC T).inv_mem hkf) u hu hu0
    have e := hW.om_heis 1 k (actO S T 1 k⁻¹ u) g hg
    have e2 := GlobalTheory.AdelicLatMove.actO_actO_inv S T 1 k u
    rw [inv_one] at e2
    rw [e2, hgN _ h1 h2] at e
    exact e.symm
  have hMC : ∀ k ∈ K, k ∈ GfC T → ∀ w g, IsThetaFunO ψ S T g → (∀ u ∈ N, u.map (infPart D) = 0 → heisO ψ S T u g = g) →
      (∀ l ∈ N, l.map (infPart D) = 0 → ψ (symplO S T w l) = 1) →
      om (1, k) (heisO ψ S T w g) = heisO ψ S T w (om (1, k) g) := by
    intro k hk hkf w g hg hgN hw
    obtain ⟨d1, d2, d3⟩ := hKA k hk hkf w hw
    have e := hcomp w (actO S T 1 k w - w) (om (1, k) g)
    rw [(hMV k hk hkf g hg hgN).2 _ d1 d2, d3, one_smul, add_sub_cancel] at e
    rw [hW.om_heis 1 k w g hg, e]
  have hsc : ∀ k ∈ K, k ∈ GfC T → ∃ c : ℂ, ∀ g, IsThetaFunO ψ S T g → (∀ u ∈ N, u.map (infPart D) = 0 → heisO ψ S T u g = g) → om (1, k) g = c • g := by
    intro k hk hkf
    exact scalar_of_prod hψ N (om (1, k)) hAR (fun g hg hgN => (hMV k hk hkf g hg hgN).1) (hMC k hk hkf)
      (prodId ψ S T hψ N (om (1, k)) (hMV k hk hkf) (hMC k hk hkf)
        (fun μ 𝓕 hμ h𝓕 g hg _ => hW.om_unit μ 𝓕 hμ h𝓕 (1, k) g hg))
  by_cases hf0 : ∃ x₀, f x₀ ≠ 0
  · obtain ⟨x₀, hx₀⟩ := hf0
    let F : GA D T → ℂ := fun k => om (1, k) f x₀ / f x₀
    have hFc : Continuous F :=
      ((hW.om_cont f hf x₀).comp (continuous_const.prodMk continuous_id)).div_const _
    have hF1 : F 1 = 1 := by
      show om (1, 1) f x₀ / f x₀ = 1
      rw [show ((1, 1) : GA D S × GA D T) = 1 from rfl, map_one, Module.End.one_apply, div_self hx₀]
    have hFc' : ∀ k ∈ K, k ∈ GfC T → ∀ c : ℂ, (∀ g, IsThetaFunO ψ S T g → (∀ u ∈ N, u.map (infPart D) = 0 → heisO ψ S T u g = g) → om (1, k) g = c • g) →
        F k = c := by
      intro k hk hkf c hc
      show om (1, k) f x₀ / f x₀ = c
      rw [hc f hf hfN, Pi.smul_apply, smul_eq_mul, mul_div_assoc, div_self hx₀, mul_one]
    have hFm : ∀ a ∈ K, a ∈ GfC T → ∀ b ∈ K, b ∈ GfC T → F (a * b) = F a * F b := by
      intro a ha haf b hb hbf
      obtain ⟨ca, hca⟩ := hsc a ha haf
      obtain ⟨cb, hcb⟩ := hsc b hb hbf
      rw [hFc' a ha haf ca hca, hFc' b hb hbf cb hcb]
      show om (1, a * b) f x₀ / f x₀ = ca * cb
      rw [show ((1, a * b) : GA D S × GA D T) = (1, a) * (1, b) by simp, map_mul, Module.End.mul_apply,
        hcb f hf hfN, map_smul, hca f hf hfN, smul_smul, Pi.smul_apply, smul_eq_mul, mul_div_assoc, div_self hx₀,
        mul_one, mul_comm]
    obtain ⟨V, hVo, hV⟩ := openKer T K hKo F hFc hF1 hFm
    refine ⟨V ⊓ K, hVo.inter hKo, fun k hk hkf => ?_⟩
    obtain ⟨c, hc⟩ := hsc k hk.2 hkf
    have h1 : c = 1 := by rw [← hFc' k hk.2 hkf c hc]; exact hV k hk.1 hkf
    rw [hc f hf hfN, h1, one_smul]
  · push_neg at hf0
    have : f = 0 := funext hf0
    refine ⟨⊤, isOpen_univ, fun k _ _ => ?_⟩
    rw [this, map_zero]
end GlobalTheory.WeilLevel
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open scoped ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twist_weil_level_eq_conductor : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (f : WO S T → ℂ), _root_.GlobalTheory.FunPr.ThetaLocalInputs → IsWeilDatumO ψ S T χS χT om → IsThetaFunO ψ S T f → ∃ U : Subgroup (GA D T), IsOpen (U : Set (GA D T)) ∧ ∀ k ∈ U, k ∈ GfC T → om (1, k) f = f := by
  first | exact @_root_.GlobalTheory.WeilLevel.weil_representation_level_eq_conductor | exact _root_.GlobalTheory.WeilLevel.weil_representation_level_eq_conductor | (intros; apply _root_.GlobalTheory.WeilLevel.weil_representation_level_eq_conductor <;> assumption)
end
end

