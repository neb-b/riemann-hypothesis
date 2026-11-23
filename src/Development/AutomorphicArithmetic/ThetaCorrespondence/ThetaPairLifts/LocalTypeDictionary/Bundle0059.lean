module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteInfiniteScalarBounds
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0001
public import Mathlib
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0612
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0593
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0015
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0607
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0067
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0619
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0053
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2813
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1557
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0033
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefiniteBottomTowerConstantsDifferByFactor
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0124
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0866
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MeasureToRealEqMass
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0145
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0868
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0197
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0252
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0160
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0245
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ResidueVanishing.Rethread
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.ThetaCoefficients.ResCore

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.FiniteInfiniteScalarBounds
section
section
noncomputable section
namespace GlobalTheory.ScalAA
open IsDedekindDomain NumberField
open Formalism.DivisionValues (vw lw)
section Abstract
variable {K : Type} [Field K] [NumberField K]
end Abstract
end GlobalTheory.ScalAA
noncomputable section
namespace GlobalTheory.ScalAA
open IsDedekindDomain NumberField Formalism.BasicNotions
open Formalism.DivisionValues (vw lw)
open scoped nonZeroDivisors Pointwise
section IdealSum
variable {E : Type} [Field E] [NumberField E]
end IdealSum
section Host
variable (D : D7)
end Host
end GlobalTheory.ScalAA
noncomputable section
namespace GlobalTheory.ScalAA
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SumSize GlobalTheory.RowClaim GlobalTheory.RowTest
open Formalism.DivisionValues (vw lw)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw
  GlobalTheory.FunObj.borelSpaceKw
section Scalar
variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) {U : Set T}
end Scalar
end GlobalTheory.ScalAA
noncomputable section
namespace GlobalTheory.ScalAA
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SumSize GlobalTheory.RowClaim GlobalTheory.RowTest
open Formalism.DivisionValues (vw lw)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw
  GlobalTheory.FunObj.borelSpaceKw
section Core
variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}
end Core
theorem finScalK_and_infScalK_of_theta_inputs : _root_.GlobalTheory.FunPr.ThetaLocalInputs → FinScalK ∧ InfScalK := by
  intro _
  refine ⟨⟨0, fun CF _ => ⟨2, fun ε C hC => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F s ch _ _ hF => ?_⟩⟩⟩,
    ⟨0, fun CF _ => ⟨2, fun ε C hC => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F s ch _ _ hF => ?_⟩⟩⟩⟩
  · exact (core s ch hF hC).1
  · exact (core s ch hF hC).2
end GlobalTheory.ScalAA
end
end
end
end
end

section
open GlobalTheory.SumSize GlobalTheory.RowClaim
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_and_infinite_scalar_bounds : _root_.GlobalTheory.FunPr.ThetaLocalInputs → FinScalK ∧ InfScalK := by
  first | exact @_root_.GlobalTheory.ScalAA.finScalK_and_infScalK_of_theta_inputs | exact _root_.GlobalTheory.ScalAA.finScalK_and_infScalK_of_theta_inputs | (intros; apply _root_.GlobalTheory.ScalAA.finScalK_and_infScalK_of_theta_inputs <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.JetOfMovedVacuumNonvanishing
section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
noncomputable section
namespace GlobalTheory.MovedJetNZ
open GlobalTheory.Grid (neg ofSgn)
end GlobalTheory.MovedJetNZ
end
namespace GlobalTheory.MovedJetNZ
open GlobalTheory.Grid (neg ofSgn)
theorem moved_vacuum_jet_ne_zero : ∀ {D : D7} {T : Type} [Finite T] {L : LevCh D T} {μ₀ : T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → L.Is μ₀ →
    IsBottomTri W i j X → ∀ (t : T), ∀ γ ∈ Formalism.L2.Theta.GQ A, ∀ a ∈ GinfC A, ∀ γ' ∈ Formalism.L2.Theta.GQ WW, ∀ a' ∈ GinfC WW,
      γ * a ∈ GfC A → γ' * a' ∈ GfC WW →
      ∃ k : FVar D WW.rank A.rank →₀ ℕ, pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.ω t (γ, γ') X.vac) (MvPolynomial.monomial k 1) 0 ≠ 0 := by
  intro D T _ L μ₀ sc G W i j A A' WW X _ hI _ hX t γ hγ _ _ γ' hγ' _ _ _ _
  classical
  have hIs := hX.is
  have hψ : IsStdChar D W.ψ (-1) := hIs.isVac.1
  have hθ : IsInfFam W.θ := hIs.isVac.2.inf
  set om' := (X.ω t).toSgn true with hom'
  have hom := hIs.weil t
  have hsA : ∀ τ, X.rA.s τ = 1 := fun τ => (hX.std.2.2 τ).1
  have hsW : ∀ τ, X.rW.s τ = 1 := fun τ => (hX.stdW.2.2 τ).1
  have hBA : ∀ τ, X.rA.B τ = 1 := fun τ => by rw [(hX.std.2.2 τ).2]
  obtain ⟨k₀, hk₀⟩ := vac_jet_ne_zero hI hX
  by_contra hall
  push_neg at hall
  set γs := (ofSgn true A).symm γ with hγs
  have hγsQ : γs ∈ GQ (neg A) :=
    (GlobalTheory.SgnIdent.mem_GQ_sgn true A γs).2 (by rw [hγs, MulEquiv.apply_symm_apply]; exact hγ)
  have hg : X.ω t (γ, γ') X.vac = om' (γs, γ') X.vac := by
    show _ = (X.ω t) ((ofSgn true A) ((ofSgn true A).symm γ), γ') X.vac
    rw [MulEquiv.apply_symm_apply]
  simp only [hg] at hall
  have hvθ : IsThetaFunO W.ψ (neg A) WW X.vac := hIs.isVac.2.theta
  have hgθ : IsThetaFunO W.ψ (neg A) WW (om' (γs, γ') X.vac) := hom.om_pres _ _ hvθ
  have hzero : ∀ P, pureTensorO W.ψ W.θ (neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (om' (γs, γ') X.vac) P 0 = 0 := by
    intro P
    set_option synthInstance.maxHeartbeats 100000 in
      rw [P.as_sum, map_sum, Finset.sum_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    have e : MvPolynomial.monomial k (P.coeff k) = P.coeff k • MvPolynomial.monomial k 1 := by
      rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
    rw [e, map_smul, Pi.smul_apply, hall k, smul_zero]
  have hop := GlobalTheory.OrientedHeis.om_pureTensorO D W.ψ W.θ (neg A) WW _ _ om' hom hθ (fun τ => -X.rA.s τ) (fun τ => -X.rA.s τ)
    X.rA.B (fun τ => compAt W.θ τ (Formalism.L2.Theta.mt (neg A) γs) * X.rA.B τ) X.rW.s X.rW.s X.rW.B
    (fun τ => compAt W.θ τ (Formalism.L2.Theta.mt WW γ') * X.rW.B τ) γs γ' (fun τ => by rw [hsA]; simp) (fun τ => by rw [hsW]; simp)
    (fun τ => rfl) (fun τ => rfl) X.vac hvθ (MvPolynomial.monomial k₀ 1)
  have haut := hom.om_aut γs hγsQ γ' hγ' _ hop.1
  apply hk₀
  rw [← haut, hop.2]
  have hBW : ∀ τ, X.rW.B τ = 1 := fun τ => by rw [(hX.stdW.2.2 τ).2]
  have e1 : (fun τ => compAt W.θ τ (Formalism.L2.Theta.mt (neg A) γs) * X.rA.B τ) =
      fun τ => X.rA.B τ * compAt W.θ τ (Formalism.L2.Theta.mt (neg A) γs) := by
    funext τ; rw [hBA, Matrix.mul_one, Matrix.one_mul]
  have e2 : (fun τ => compAt W.θ τ (Formalism.L2.Theta.mt WW γ') * X.rW.B τ) =
      fun τ => X.rW.B τ * compAt W.θ τ (Formalism.L2.Theta.mt WW γ') := by
    funext τ; rw [hBW, Matrix.mul_one, Matrix.one_mul]
  have es : (fun τ => -X.rA.s τ) = fun _ => (-1 : Matrix (Fin A.rank) (Fin A.rank) ℂ) := funext fun τ => by rw [hsA]
  have et : X.rW.s = fun _ => (1 : Matrix (Fin WW.rank) (Fin WW.rank) ℂ) := funext hsW
  rw [e1, e2]
  rw [es, et] at hzero ⊢
  change pureTensorO W.ψ W.θ (negSp A) WW (fun _ => -1) (fun _ => 1) _ _ _ _ _ = _
  rw [GlobalTheory.FockNegSubst.pureTensorO_negSp_subst D W.ψ W.θ A WW hψ hθ _ _ _ _ _ hgθ]
  exact hzero _
end GlobalTheory.MovedJetNZ
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jet_of_moved_vacuum_nonvanishing : ∀ {D : D7} {T : Type} [Finite T] {L : LevCh D T} {μ₀ : T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → L.Is μ₀ →
    IsBottomTri W i j X → ∀ (t : T), ∀ γ ∈ Formalism.L2.Theta.GQ A, ∀ a ∈ GinfC A, ∀ γ' ∈ Formalism.L2.Theta.GQ WW, ∀ a' ∈ GinfC WW,
      γ * a ∈ GfC A → γ' * a' ∈ GfC WW →
      ∃ k : FVar D WW.rank A.rank →₀ ℕ, pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.ω t (γ, γ') X.vac) (MvPolynomial.monomial k 1) 0 ≠ 0 := by
  first | exact @_root_.GlobalTheory.MovedJetNZ.moved_vacuum_jet_ne_zero | exact _root_.GlobalTheory.MovedJetNZ.moved_vacuum_jet_ne_zero | (intros; apply _root_.GlobalTheory.MovedJetNZ.moved_vacuum_jet_ne_zero <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.JetsDivPeriodIsAlgebraic
section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
noncomputable section
namespace GlobalTheory.BotTransJet
open GlobalTheory.Grid (neg)
end GlobalTheory.BotTransJet
namespace GlobalTheory.BotTransJet
open GlobalTheory.Grid (neg)
theorem isAlgebraic_pureTensorO_div_period : ∀ {D : D7} {T : Type} [Finite T] {L : LevCh D T} {μ₀ : T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → L.Is μ₀ →
    IsBottomTri W i j X →
    ∀ dg : D.what₂.Tau →₀ ℕ, ∃ Ω : ℂ, Ω ≠ 0 ∧ ∀ u : WO (GlobalTheory.Grid.neg A) WW, u.map (infPart D) = 0 →
      ∀ k : FVar D WW.rank A.rank →₀ ℕ, Finsupp.mapDomain Prod.fst k = dg →
        IsAlgebraic ℚ (pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B
          (heisO W.ψ (GlobalTheory.Grid.neg A) WW u X.vac) (MvPolynomial.monomial k 1) 0 / Ω) := by
  intro D T _ L μ₀ sc G W i j A A' WW X hP hI hL hX dg
  classical
  have hIs := hX.is
  have hψ : IsStdChar D W.ψ (-1) := hIs.isVac.1
  have hθ : IsInfFam W.θ := hIs.isVac.2.inf
  set f : WO A WW → ℂ := fun w => starRingEnd ℂ (X.vac w) with hfdef
  have hf0 : IsVacO W.ψ W.θ A WW X.rA.s X.rW.s X.rA.Λ X.rW.Λ f :=
    GlobalTheory.VacConj.isVacO_conj_negSp W.ψ W.θ A WW X.rA.s X.rW.s _ _ X.vac hIs.isVac
  have hf : IsVacO W.ψ W.θ A WW X.rA.s X.rW.s (colLat (1 : GL (Fin A.rank) D.host.E) : Set _)
      (colLat (1 : GL (Fin WW.rank) D.host.E) : Set _) f := by
    rw [← std_eq_colLat_one X.rA.Λ hX.std.2.1, ← std_eq_colLat_one X.rW.Λ hX.stdW.2.1]
    exact hf0
  have hS : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (1 : GL (Fin A.rank) D.host.E).1 * A.gram *
      (1 : GL (Fin A.rank) D.host.E).1 = 1 := by
    rw [hX.std.1]
    simp [Formalism.UG.cT]
  have hW : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (1 : GL (Fin WW.rank) D.host.E).1 * WW.gram *
      (1 : GL (Fin WW.rank) D.host.E).1 = 1 := by
    rw [hX.stdW.1]
    simp [Formalism.UG.cT]
  have hcA : ∀ τ, IsCartanInv (gramAt D A τ) (X.rA.s τ) := fun τ => (hIs.rigA.2.2 τ).1
  have hcW : ∀ τ, IsCartanInv (gramAt D WW τ) (X.rW.s τ) := fun τ => (hIs.rigW.2.2 τ).1
  have hBA : (fun τ => (1 : GL (Fin A.rank) D.host.E).1.map (tauE D τ)) = X.rA.B := by
    funext τ
    rw [(hX.std.2.2 τ).2]
    simp
  have hBW : (fun τ => (1 : GL (Fin WW.rank) D.host.E).1.map (tauE D τ)) = X.rW.B := by
    funext τ
    rw [(hX.stdW.2.2 τ).2]
    simp
  obtain ⟨δ, hC, hδ⟩ := GlobalTheory.FunObj.exists_delta D
  obtain ⟨t0, ht0⟩ := ((hI D).t0Ex D.host.ccK δ hC).1
  have hev : Even (A.rank * WW.rank) := even_bot hX
  obtain ⟨e0, he0, -⟩ := GlobalTheory.Vacuum.exists_vacuum D D.host.ccK δ hC t0 ht0 A.rank WW.rank hev
  obtain ⟨c, hc⟩ := GlobalTheory.FockPos.fock_jets_eq_unit_mul_period_jets W.ψ W.θ A WW X.rA.s X.rW.s 1 1 hS hW hcA hcW δ t0 hC hδ
    ht0 e0 he0 f hf
  have hΩ : starRingEnd ℂ ((c : ℂ) * dg.prod fun τ n => GlobalTheory.FunObj.period δ τ ^ n) ≠ 0 :=
    (map_ne_zero _).2 (mul_ne_zero c.ne_zero (Finsupp.prod_ne_zero_iff.2 fun τ _ =>
      pow_ne_zero _ (GlobalTheory.FunObj.period_ne_zero hδ τ)))
  refine ⟨_, hΩ, fun u hu k hk => ?_⟩
  obtain ⟨m, a, s, ha, hs, hjet⟩ := _root_.GlobalTheory.T.finite_translate_jets_fock hP hI W.ψ W.θ A WW X.rA.s X.rW.s 1 1 hS hW hcA hcW δ t0 hC hδ ht0 e0 he0 f hf
    c (fun k => hc k) u hu
  have hconj := jet_negSp_heis W.ψ W.θ hψ hθ A WW X.rA.s X.rW.s X.rA.B X.rW.B X.vac u k
  have hprod : (k.prod fun v n => GlobalTheory.FunObj.period δ v.1 ^ n) = dg.prod fun τ n => GlobalTheory.FunObj.period δ τ ^ n := by
    rw [← hk, Finsupp.prod_mapDomain_index (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)]
  have hcoef : TaylorLogMetric.CoefIn D (StandardLatticesGL3.comb D (TaylorLogMetric.tor0 D D.host.ccK δ) a s e0) TaylorLogMetric.Qbar :=
    ((hI D).alg D.host.ccK δ hC t0 ht0 A.rank WW.rank (StandardLatticesGL3.stdL D A.rank) (StandardLatticesGL3.stdL D WW.rank)
      (GlobalTheory.MovedVacuum.sd_stdL D _) (GlobalTheory.MovedVacuum.sd_stdL D _) hev e0 he0.2.2.2.1).2.2.1 m a s
      (fun l => (mem_algebraicClosure_iff).2 (ha l)) hs
  have hY : IsAlgebraic ℚ (GL3Theta.applyAt0 D (MvPolynomial.monomial k 1) (StandardLatticesGL3.comb D (TaylorLogMetric.tor0 D D.host.ccK δ) a s e0)) := by
    refine applyAt0_isAlgebraic (fun α => ?_) hcoef
    rw [MvPolynomial.coeff_monomial]
    split_ifs
    · exact isAlgebraic_one
    · exact isAlgebraic_zero
  change IsAlgebraic ℚ (pureTensorO W.ψ W.θ (negSp A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (heisO W.ψ (negSp A) WW u X.vac)
    (MvPolynomial.monomial k 1) 0 / _)
  rw [hconj, ← hBA, ← hBW, hjet k, hprod, show ∀ x y z : ℂ, x * (y * z) = (x * y) * z from fun _ _ _ => (mul_assoc _ _ _).symm,
    map_mul, mul_div_cancel_left₀ _ hΩ]
  exact conj_isAlgebraic hY
end GlobalTheory.BotTransJet
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bottom_translate_jets_algebraic : ∀ {D : D7} {T : Type} [Finite T] {L : LevCh D T} {μ₀ : T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → L.Is μ₀ →
    IsBottomTri W i j X →
    ∀ dg : D.what₂.Tau →₀ ℕ, ∃ Ω : ℂ, Ω ≠ 0 ∧ ∀ u : WO (GlobalTheory.Grid.neg A) WW, u.map (infPart D) = 0 →
      ∀ k : FVar D WW.rank A.rank →₀ ℕ, Finsupp.mapDomain Prod.fst k = dg →
        IsAlgebraic ℚ (pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B
          (heisO W.ψ (GlobalTheory.Grid.neg A) WW u X.vac) (MvPolynomial.monomial k 1) 0 / Ω) := by
  first | exact @_root_.GlobalTheory.BotTransJet.isAlgebraic_pureTensorO_div_period | exact _root_.GlobalTheory.BotTransJet.isAlgebraic_pureTensorO_div_period | (intros; apply _root_.GlobalTheory.BotTransJet.isAlgebraic_pureTensorO_div_period <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.KerMinorMulRealOfRealInvariant
section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
open scoped Matrix
namespace GlobalTheory.BotRealInv
theorem ker_minor_mul_real_of_real_invariant : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
    (∀ D, GlobalTheory.NormSum.Inp D) → GlobalTheory.SqTop.BotSmall →
    GlobalTheory.SqTop.GBig fun {D} T _ _ G _ _ _ _ => ∀ (W : G.Weil), IsStdChar D W.ψ (-1) → ∀ (i j : Fin D.R.m) (A A' WW : HSp D)
      (X : Tri T A A' WW) (δ t0 : ℂ), IsBottomTri W i j X → ∀ (s : T) (Q : ℕ) (P P' : Pair D ⊤ δ t0 Q),
        IsBottom G s i j (GlobalTheory.SqTop.modT G s) P P' → ∀ (ea : P'.a = A'.rank) (ed : P'.d = WW.rank) (T' : Tup D P'.a P'.d P'.n)
          (h : GA D WW), ∀ k ∈ GinfC A', ∀ g : GA D A',
            X.ker' W.ψ W.θ s (GlobalTheory.BotFormula.minorF ea ed T') h (g * k) = X.ker' W.ψ W.θ s (GlobalTheory.BotFormula.minorF ea ed T') h g := by
  intro _ _ _ _ _
  refine ⟨0, fun ε CF _ => ⟨0, 0, fun C _ D large₂ _ _ _ T L μ₀ hL G W _ i j A A' WW X δ t0 hX t Q P P' hB ea ed T' h g hg x => ?_⟩⟩
  have hθ : IsInfFam W.θ := hX.is.isVac.2.inf
  have hV : HSpace.gram A' = 1 := hX.std'.1
  have hVW : HSpace.gram WW = 1 := hX.stdW.1
  have hW : IsWeilDatumO W.ψ A' WW (L.mu t (j + 1) * L.eta ^ (rankV D i j % 2))
      ((L.mu t (j + 1) * L.eta ^ (rankV D i j % 2)) / (G.ch.chi (D.R.m - i) * L.eta ^ (rankV D i j % 2))) (X.ω' t) :=
    hX.is.weil' t
  have hinf := GlobalTheory.BotWeights.hasInf_of_chars P' _ hB.chars'.2
  have hinf' : (nuH G t i j).HasInfQ (tauE D) fun τ => -((P'.W.ep' * P'.W.chV'.n τ : ℤ) : ℚ) / 2 := by
    refine ⟨fun τ => -(P'.W.ep' * P'.W.chV'.n τ), fun τ => by push_cast; ring, fun k => ?_⟩
    have h1 := hinf k
    rw [Formalism.L2.Host.HChar.inf_inv, Units.val_inv_eq_inv_val, inv_eq_iff_eq_inv, ← Finset.prod_inv_distrib] at h1
    rw [h1]
    exact Finset.prod_congr rfl fun τ _ => (zpow_neg _ _).symm
  have hb : ∀ τ, HasInfExp D ((L.mu t (j + 1) * L.eta ^ (rankV D i j % 2)) /
      (G.ch.chi (D.R.m - i) * L.eta ^ (rankV D i j % 2))) τ (-((P'.W.ep' * P'.W.chV'.n τ : ℤ) : ℚ) / 2) := by
    rw [succ_mul_succ_sub_one_div_succ]
    exact GlobalTheory.HeckeInfExp.hasInfExp_of_chrEq D _ _ _ (chrEq_nu G t i j hL) hinf'
  have he₂ : ∀ τ, (((P'.n τ : ℕ) : ℤ) : ℚ) = -(-((P'.W.ep' * P'.W.chV'.n τ : ℤ) : ℚ) / 2 + (WW.rank : ℚ) / 2) := fun τ => by
    have h2 : ((2 * (P'.n τ : ℤ) : ℤ) : ℚ) = ((P'.W.ep' * P'.W.chV'.n τ - (P'.d : ℤ) : ℤ) : ℚ) := by rw [P'.wt τ]
    rw [← ed]
    push_cast at h2 ⊢
    linarith
  choose a ha using fun τ => GlobalTheory.SplitCharExp.exists_hasInfExp D W.θ _ A'.rank τ hθ hW.hecS hW.resS
  choose e₁ he₁ using fun τ => GlobalTheory.SplitParity.exists_int_add_half D _ A'.rank τ (a τ) hW.hecS hW.resS (ha τ)
  have hψ : Continuous W.ψ := hX.is.isVac.1.1.1
  have es : X.rA'.s = fun _ => 1 := funext fun τ => (hX.std'.2.2 τ).1
  have eB : X.rA'.B = fun _ => 1 := funext fun τ => (hX.std'.2.2 τ).2
  have esW : X.rW.s = fun _ => 1 := funext fun τ => (hX.stdW.2.2 τ).1
  have eBW : X.rW.B = fun _ => 1 := funext fun τ => (hX.stdW.2.2 τ).2
  have hf : IsThetaFunO W.ψ A' WW (X.f' t) := (GlobalTheory.ConstRatio.theta_f hX.is t).2
  have ho := GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum (hX.is.idem t)
  have hv : ∀ τ, IsFockVacAt (heisO W.ψ A' WW) W.θ τ (cplxO 1 1) (X.f' t) := fun τ => by
    have h0 := hX.is.isVac'.2.fock τ
    rw [es, esW] at h0
    exact GlobalTheory.DatumFock.isFockVacAt_of_isThetaAt hψ hθ ho.conj.infPart_eq ho.conj.conj.infPart_eq (hX.is.snd t)
      hX.is.isVac'.2.theta hf h0
  have hBS : ∀ τ, ((fun _ => (1 : Matrix (Fin A'.rank) (Fin A'.rank) ℂ)) τ)ᴴ * gramAt D A' τ * 1 = 1 := fun τ => by
    rw [GlobalTheory.RealColAct.gramAt_of_gram_one hV]; simp
  have hBT : ∀ τ, ((fun _ => (1 : Matrix (Fin WW.rank) (Fin WW.rank) ℂ)) τ)ᴴ * gramAt D WW τ * 1 = 1 := fun τ => by
    rw [GlobalTheory.RealColAct.gramAt_of_gram_one hVW]; simp
  have key := GlobalTheory.RealFockPos.om_pureTensorO_pos D W.ψ W.θ A' WW _ _ (X.ω' t) hW hθ (fun _ => 1) (fun _ => 1) hBS hBT
    a _ ha hb e₁ (fun τ => (P'.n τ : ℤ)) he₁ he₂ (X.f' t) hf hv g hg 1 (one_mem _) (GlobalTheory.BotFormula.minorF ea ed T')
  simp only [inv_one, Matrix.one_mul, Matrix.mul_one, GlobalTheory.StdUnn.CartanMove.compAt_mt_one, Matrix.det_one, one_zpow, mul_one]
    at key
  have hc : (∏ τ, (compAt W.θ τ (Formalism.L2.Theta.mt A' g)).det ^ (P'.n τ : ℤ)) *
      ∏ τ, ((compAt W.θ τ (Formalism.L2.Theta.mt A' g))⁻¹).det ^ P'.n τ = 1 := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_eq_one fun τ _ => ?_
    have h1 := GlobalTheory.OrientedHeis.compAt_mt_mul_inv (θ := W.θ) τ g
    rw [Matrix.inv_eq_right_inv h1, zpow_natCast, ← mul_pow, ← Matrix.det_mul, h1, Matrix.det_one, one_pow]
  rw [substF_minorF, map_smul, smul_smul, hc, one_smul] at key
  unfold Tri.ker' thetaKO
  rw [es, eB, esW, eBW]
  have e : ((x * g, h) : Formalism.L2.Theta.GA D A' × Formalism.L2.Theta.GA D WW) = (x, h) * (g, 1) := by simp
  rw [e, map_mul, Module.End.mul_apply, key]
end GlobalTheory.BotRealInv
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.minor_kernel_real_invariant : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
    (∀ D, GlobalTheory.NormSum.Inp D) → GlobalTheory.SqTop.BotSmall →
    GlobalTheory.SqTop.GBig fun {D} T _ _ G _ _ _ _ => ∀ (W : G.Weil), IsStdChar D W.ψ (-1) → ∀ (i j : Fin D.R.m) (A A' WW : HSp D)
      (X : Tri T A A' WW) (δ t0 : ℂ), IsBottomTri W i j X → ∀ (s : T) (Q : ℕ) (P P' : Pair D ⊤ δ t0 Q),
        IsBottom G s i j (GlobalTheory.SqTop.modT G s) P P' → ∀ (ea : P'.a = A'.rank) (ed : P'.d = WW.rank) (T' : Tup D P'.a P'.d P'.n)
          (h : GA D WW), ∀ k ∈ GinfC A', ∀ g : GA D A',
            X.ker' W.ψ W.θ s (GlobalTheory.BotFormula.minorF ea ed T') h (g * k) = X.ker' W.ψ W.θ s (GlobalTheory.BotFormula.minorF ea ed T') h g := by
  first | exact @_root_.GlobalTheory.BotRealInv.ker_minor_mul_real_of_real_invariant | exact _root_.GlobalTheory.BotRealInv.ker_minor_mul_real_of_real_invariant | (intros; apply _root_.GlobalTheory.BotRealInv.ker_minor_mul_real_of_real_invariant <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.KplugFill
section
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.Exh GlobalTheory.RegSW
noncomputable section
namespace GlobalTheory.Core.Rk.Exh.Top
theorem downNe_k_of_hypotheses' : ResidueKilled.DM → GlobalTheory.IndefiniteRowSideFullHecke.SimplePoleTwistedLift.SimplePole → ∀ D : D7, EulerRight D → DownNe D :=
  fun hDM hSP => downNe_of_core hDM PositivityTheory.Rg.Rsw.resCore hSP
end GlobalTheory.Core.Rk.Exh.Top
end
end
end

