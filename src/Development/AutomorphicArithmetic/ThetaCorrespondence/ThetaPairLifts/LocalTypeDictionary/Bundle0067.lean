module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0632
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0001
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0063
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0003
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0017
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0003
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0015
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0440
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0464
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0635
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0593
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0607
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0122
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2849
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1557
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1490
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DefiniteThetaPairTermsNormsIndependentRepresenta
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0224
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0432
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0633
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0181
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaGrowthOfThetaSquareIntegrable
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspAlongOfPairLifts
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.TypeAtOfDiscreteSeries
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0469
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsKFiniteIteratedCompactAverageApprox
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0534
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0042
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FirstVertexWeilOrbitValue
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0431
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0473
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0477
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0503

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.MovedKappaRationalOfArithmetic
section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC
open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC
namespace GlobalTheory.MovedKappaArith
end GlobalTheory.MovedKappaArith
namespace GlobalTheory.MovedKappaArith
theorem movedKappa_unique : _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type}
    {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}
    (ch : Choice R), ch.Is → ∀ (p : Pair T), DefPair D.R.m p → ∀ (x : FinPt ch.G p.small) (y : FinPt ch.G p.big),
    ∀ κ κ' : ℂ, (∀ k : FVar D (ch.G.pT p).rank (ch.G.pS p).rank →₀ ℕ,
      fockIn ch.W ch.S.N.frC p (ch.W.om p (ch.G.toPair p ((x * ch.S.N.u p.small : FinPt ch.G p.small) : Formalism.L2.Theta.GA D (ch.G.V p.small)) ((y * ch.S.N.u p.big : FinPt ch.G p.big) : Formalism.L2.Theta.GA D (ch.G.V p.big))) (ch.S.Z.vac p))
        (MvPolynomial.monomial k 1) 0 = ch.S.Z.c0 p * opp p ((k.prod fun v e => period ch.S.Z.δ v.1 ^ e) *
          Formalism.MainNotions.GL3Theta.applyAt0 D (MvPolynomial.monomial k 1) fun z => κ * Iop D (tor0 D D.host.ccK ch.S.Z.δ) (La0 D (tor0 D D.host.ccK ch.S.Z.δ) _ _) (Formalism.MainNotions.TaylorLogMetric.La D (tor0 D D.host.ccK ch.S.Z.δ) (GlobalTheory.MovedDict.srcLat ch.S.toGridChoice p x y) (GlobalTheory.MovedDict.tgtLat ch.S.toGridChoice p x y)) (ch.S.Z.e0 p) z)) → (∀ k : FVar D (ch.G.pT p).rank (ch.G.pS p).rank →₀ ℕ,
      fockIn ch.W ch.S.N.frC p (ch.W.om p (ch.G.toPair p ((x * ch.S.N.u p.small : FinPt ch.G p.small) : Formalism.L2.Theta.GA D (ch.G.V p.small)) ((y * ch.S.N.u p.big : FinPt ch.G p.big) : Formalism.L2.Theta.GA D (ch.G.V p.big))) (ch.S.Z.vac p))
        (MvPolynomial.monomial k 1) 0 = ch.S.Z.c0 p * opp p ((k.prod fun v e => period ch.S.Z.δ v.1 ^ e) *
          Formalism.MainNotions.GL3Theta.applyAt0 D (MvPolynomial.monomial k 1) fun z => κ' * Iop D (tor0 D D.host.ccK ch.S.Z.δ) (La0 D (tor0 D D.host.ccK ch.S.Z.δ) _ _) (Formalism.MainNotions.TaylorLogMetric.La D (tor0 D D.host.ccK ch.S.Z.δ) (GlobalTheory.MovedDict.srcLat ch.S.toGridChoice p x y) (GlobalTheory.MovedDict.tgtLat ch.S.toGridChoice p x y)) (ch.S.Z.e0 p) z)) → κ = κ' := by
  intro hPr hInp D Γ _ _ Pl0 T A Ks _ _ _ R ch hIs p hp x y κ κ' h1 h2
  set F := Iop D (tor0 D D.host.ccK ch.S.Z.δ) (La0 D (tor0 D D.host.ccK ch.S.Z.δ) _ _) (Formalism.MainNotions.TaylorLogMetric.La D (tor0 D D.host.ccK ch.S.Z.δ) (GlobalTheory.MovedDict.srcLat ch.S.toGridChoice p x y) (GlobalTheory.MovedDict.tgtLat ch.S.toGridChoice p x y)) (ch.S.Z.e0 p) with hFdef
  have hF : Differentiable ℂ F :=
    _root_.GlobalTheory.MovedDict.Entire.differentiable_moved_operator_eval hPr hInp ch hIs p hp x y
  obtain ⟨hsd, hsd'⟩ := _root_.GlobalTheory.MovedSD.moved_series_decomposition hPr hInp ch hIs p hp x y
  have hF0 : F ≠ 0 := selfDualIntertwiner_baseVector_ne_zero ch.S.Z.crv ch.S.Z.pt0 (ch.S.Z.e0_is p hp) hsd hsd'
  obtain ⟨α, hα⟩ := GlobalTheory.NatFamily.exists_taylor_ne D hF hF0
  have e := (h1 α).symm.trans (h2 α)
  rw [applyAt0_monomial, applyAt0_monomial, GlobalTheory.ProdThetaConj.taylor_const_mul hF,
    GlobalTheory.ProdThetaConj.taylor_const_mul hF] at e
  have e' := (opp p).injective (mul_left_cancel₀ (ch.S.Z.c0 p).ne_zero e)
  have hP : (α.prod fun v e => period ch.S.Z.δ v.1 ^ e) ≠ 0 :=
    Finsupp.prod_ne_zero_iff.2 fun v _ => pow_ne_zero _ (GlobalTheory.FunObj.period_ne_zero (GlobalTheory.TwoTorsionPt.delta_ne ch.S.Z.crv) v.1)
  have hfac : (α.prod fun _ n => (n.factorial : ℂ)) ≠ 0 :=
    Finsupp.prod_ne_zero_iff.2 fun _ _ => Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
  have e'' := mul_left_cancel₀ (mul_ne_zero hP hfac) (by simpa only [mul_assoc] using e')
  exact mul_right_cancel₀ hα e''
end GlobalTheory.MovedKappaArith
namespace GlobalTheory.MovedKappaArith
theorem movedKappa_arithmetic : _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type}
    {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}
    (ch : Choice R), ch.Is → ∀ (p : Pair T), DefPair D.R.m p → ∀ (x : FinPt ch.G p.small) (y : FinPt ch.G p.big),
    ∀ κ : ℂ, (∀ k : FVar D (ch.G.pT p).rank (ch.G.pS p).rank →₀ ℕ,
      fockIn ch.W ch.S.N.frC p (ch.W.om p (ch.G.toPair p ((x * ch.S.N.u p.small : FinPt ch.G p.small) : Formalism.L2.Theta.GA D (ch.G.V p.small)) ((y * ch.S.N.u p.big : FinPt ch.G p.big) : Formalism.L2.Theta.GA D (ch.G.V p.big))) (ch.S.Z.vac p))
        (MvPolynomial.monomial k 1) 0 = ch.S.Z.c0 p * opp p ((k.prod fun v e => period ch.S.Z.δ v.1 ^ e) *
          Formalism.MainNotions.GL3Theta.applyAt0 D (MvPolynomial.monomial k 1) fun z => κ * Iop D (tor0 D D.host.ccK ch.S.Z.δ) (La0 D (tor0 D D.host.ccK ch.S.Z.δ) _ _) (Formalism.MainNotions.TaylorLogMetric.La D (tor0 D D.host.ccK ch.S.Z.δ) (GlobalTheory.MovedDict.srcLat ch.S.toGridChoice p x y) (GlobalTheory.MovedDict.tgtLat ch.S.toGridChoice p x y)) (ch.S.Z.e0 p) z)) →
    Mod1All κ ∧ (∀ (q : ℕ) [Fact q.Prime], EqAt D q (GlobalTheory.SumSize.latAt ch.S.toGridChoice p.small x) (stdL D _) →
      EqAt D q (GlobalTheory.SumSize.latAt ch.S.toGridChoice p.big y) (stdL D _) → ∀ lam : Qbar →+* ℂ_[q], ‖lamC lam κ‖ = 1) := by
  intro hPr hInp D Γ _ _ Pl0 T A Ks _ _ _ R ch hIs p hp x y κ hj
  obtain ⟨κ₀, hm, hu, hj₀⟩ := _root_.GlobalTheory.T.exists_unique_moved_kappa_jet hPr hInp ch hIs p hp x y
  obtain rfl := _root_.GlobalTheory.MovedKappaArith.movedKappa_unique hPr hInp ch hIs p hp x y κ κ₀ hj hj₀
  exact ⟨hm, hu⟩
end GlobalTheory.MovedKappaArith
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC
open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.movedKappa_rational_of_arithmetic : _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type}
    {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}
    (ch : Choice R), ch.Is → ∀ (p : Pair T), DefPair D.R.m p → ∀ (x : FinPt ch.G p.small) (y : FinPt ch.G p.big),
    ∀ κ : ℂ, (∀ k : FVar D (ch.G.pT p).rank (ch.G.pS p).rank →₀ ℕ,
      fockIn ch.W ch.S.N.frC p (ch.W.om p (ch.G.toPair p ((x * ch.S.N.u p.small : FinPt ch.G p.small) : Formalism.L2.Theta.GA D (ch.G.V p.small)) ((y * ch.S.N.u p.big : FinPt ch.G p.big) : Formalism.L2.Theta.GA D (ch.G.V p.big))) (ch.S.Z.vac p))
        (MvPolynomial.monomial k 1) 0 = ch.S.Z.c0 p * opp p ((k.prod fun v e => period ch.S.Z.δ v.1 ^ e) *
          Formalism.MainNotions.GL3Theta.applyAt0 D (MvPolynomial.monomial k 1) fun z => κ * Iop D (tor0 D D.host.ccK ch.S.Z.δ) (La0 D (tor0 D D.host.ccK ch.S.Z.δ) _ _) (Formalism.MainNotions.TaylorLogMetric.La D (tor0 D D.host.ccK ch.S.Z.δ) (GlobalTheory.MovedDict.srcLat ch.S.toGridChoice p x y) (GlobalTheory.MovedDict.tgtLat ch.S.toGridChoice p x y)) (ch.S.Z.e0 p) z)) →
    Mod1All κ ∧ (∀ (q : ℕ) [Fact q.Prime], EqAt D q (GlobalTheory.SumSize.latAt ch.S.toGridChoice p.small x) (stdL D _) →
      EqAt D q (GlobalTheory.SumSize.latAt ch.S.toGridChoice p.big y) (stdL D _) → ∀ lam : Qbar →+* ℂ_[q], ‖lamC lam κ‖ = 1) := by
  first | exact @_root_.GlobalTheory.MovedKappaArith.movedKappa_arithmetic | exact _root_.GlobalTheory.MovedKappaArith.movedKappa_arithmetic | (intros; apply _root_.GlobalTheory.MovedKappaArith.movedKappa_arithmetic <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.SplitVacuumAlgebraicCombination
section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
noncomputable section
namespace GlobalTheory.SplitVacAlg
open GlobalTheory.MovedAlg
section Comb
variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {f₀ : WO S T → ℂ}
end Comb
set_option maxHeartbeats 1000000 in
theorem split_vacuum_algebraic_combination : ∀ {D : D7} {T : Type} [Finite T] {L : LevCh D T} {μ₀ : T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → L.Is μ₀ →
    IsBottomTri W i j X → ∀ (t : T) (N : ℕ) (e : AE D) (P : Pl D.host.E), Formalism.L2.NTheta.IsIdemAt e P → ((N : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal →
    ∀ h ∈ GfC WW, Formalism.L2.Theta.SuppAt e WW h →
      GlobalTheory.MovedAlg.IsAlgComb W.ψ (GlobalTheory.Grid.neg A) WW X.vac (X.ω t (1, h) X.vac) := by
  intro D T _ L μ₀ sc G W i j A A' WW X hPr hInp hLμ hX t N e P hP _ h hh hs
  classical
  have hψ : ∀ u v : WO (GlobalTheory.Grid.neg A) WW, u.map (infPart D) = 0 → v.map (infPart D) = 0 →
      IsAlgebraic ℚ (W.ψ (symplOH (GlobalTheory.Grid.neg A) WW u v)) :=
    fun u v hu hv => _root_.GlobalTheory.PsiFinAlgebraic.isAlgebraic_psi_symplOH hX.is.isVac.1 (GlobalTheory.Grid.neg A) WW u v hu hv
  have hchr := _root_.GlobalTheory.T.isAlgebraic_splitCharacter_twist hPr hInp hLμ hX
  have vac : IsAlgComb W.ψ (GlobalTheory.Grid.neg A) WW X.vac X.vac := isAlgComb_self
  have detAlg : ∀ (e' : AE D) (he' : IsSplitIdem D e') (g : GA D WW),
      IsAlgebraic ℚ (((G.ch.chi (D.R.m - i) * L.eta ^ (rankV D i j % 2)) (GlobalTheory.VecInv.detAt e' he'.1 WW g) : Circle) : ℂ) :=
    fun e' he' g => hchr e' he' _ (by
      change e' * (Formalism.L2.Theta.mt WW g).det + (1 - e') =
        e' * (e' * (Formalism.L2.Theta.mt WW g).det + (1 - e')) + (1 - e')
      rw [mul_add, ← mul_assoc, he'.1, mul_sub, mul_one, he'.1, sub_self, add_zero])
  have hecke : ∀ (e' : AE D) (he' : IsSplitIdem D e') (ϖ : 𝓞 D.host.E) (k : ℕ) (α : GA D WW),
      Formalism.L2.NTheta.IsHeckeElt (stdLatSp WW hX.stdW.1) e' (ϖ : D.host.E) k α →
      IsAlgComb W.ψ (GlobalTheory.Grid.neg A) WW X.vac (X.ω t (1, α) X.vac) := by
    intro e' he' ϖ k α hα
    obtain ⟨Δ, hΔ, heq⟩ := _root_.GlobalTheory.RowEx.BottomHecke.vacuum_hecke hX t e' he' ϖ k α hα
    rw [heq]
    exact (isAlgComb_sum Δ hΔ).smul (isAlg_mul (detAlg e' he' α) (isAlg_sqrt_inv _))
  obtain ⟨ϖ, hϖ, hϖ2⟩ : ∃ ϖ : 𝓞 D.host.E, ϖ ∈ P.asIdeal ∧ ϖ ∉ P.asIdeal ^ 2 :=
    SetLike.exists_of_lt (by
      simpa using Ideal.pow_right_strictAnti P.asIdeal P.ne_bot P.isPrime.ne_top (by norm_num : 1 < 2))
  have gen := _root_.GlobalTheory.SplitCartanGen.supp_mem_closure (stdLatSp WW hX.stdW.1) P e ϖ hP hϖ hϖ2 h hh hs
  refine Submonoid.closure_induction
    (motive := fun x _ => IsAlgComb W.ψ (GlobalTheory.Grid.neg A) WW X.vac (X.ω t (1, x) X.vac)) ?_ ?_ ?_ gen
  · intro x hx
    rcases hx with (⟨hk, hks⟩ | ⟨k, hα⟩) | ⟨k, hα⟩
    · rw [_root_.GlobalTheory.StabVacSplit.stab_vac_split hX t e hP.1 x hk hks]
      exact vac.smul (detAlg e hP.1 x)
    · exact hecke e hP.1 ϖ k x hα
    · have hc := ((GlobalTheory.SplitPlace.split_local (stdLatSp WW hX.stdW.1) P e hP).2.2 ϖ hϖ hϖ2).2 k x⁻¹ hα |>.1
      have h2 := hecke (cA D e) (GlobalTheory.SplitScalar.isSplitIdem_conj hP.1)
        ⟨star (ϖ : D.host.E), ϖ.2.map (starRingEnd D.host.E).toIntAlgHom⟩ k _ hc
      exact (congrArg (fun y : GA D WW => IsAlgComb W.ψ (GlobalTheory.Grid.neg A) WW X.vac (X.ω t (1, y) X.vac))
        (inv_inv x)).mp h2
  · show IsAlgComb W.ψ (GlobalTheory.Grid.neg A) WW X.vac (X.ω t 1 X.vac)
    rw [map_one]
    exact vac
  · intro x y _ _ hx hy
    have e1 : ((1 : GA D A), x * y) = (1, x) * (1, y) := by simp
    rw [e1, map_mul, Module.End.mul_apply]
    exact om_algComb hX hψ t 1 x hx hy
end GlobalTheory.SplitVacAlg
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
theorem _root_.GlobalTheory.T.split_place_vacuum_algebraic : ∀ {D : D7} {T : Type} [Finite T] {L : LevCh D T} {μ₀ : T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → L.Is μ₀ →
    IsBottomTri W i j X → ∀ (t : T) (N : ℕ) (e : AE D) (P : Pl D.host.E), Formalism.L2.NTheta.IsIdemAt e P → ((N : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal →
    ∀ h ∈ GfC WW, Formalism.L2.Theta.SuppAt e WW h →
      GlobalTheory.MovedAlg.IsAlgComb W.ψ (GlobalTheory.Grid.neg A) WW X.vac (X.ω t (1, h) X.vac) := by
  first | exact @_root_.GlobalTheory.SplitVacAlg.split_vacuum_algebraic_combination | exact _root_.GlobalTheory.SplitVacAlg.split_vacuum_algebraic_combination | (intros; apply _root_.GlobalTheory.SplitVacAlg.split_vacuum_algebraic_combination <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.StandardModuleBottomDatumExists
section
section
noncomputable section
section
open NumberField IsDedekindDomain
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 lamOf Th La Iop Qbar lamC)
open Formalism.MainNotions.StandardLatticesGL3 (TT stdL pt oddE0 Wd La0 Crv inc OhE IntU)
open GlobalTheory.NormSum (Pair intG)
open GlobalTheory.FunObj.SqNum (hatId CongOne skewLat unitBlock cosetVec)
open GlobalTheory.NormExact (Reads Setup IsFinIdl HasFinPart finPt)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (InId IsUnitDet unitChar stdFst)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdRead
namespace GlobalTheory.StdRead
variable {D : D7}
variable {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts}
end GlobalTheory.StdRead
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
namespace GlobalTheory.StdRead
theorem standard_module_bottom_datum : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
    (∀ D, GlobalTheory.NormSum.Inp D) → GlobalTheory.SqTop.BotSmall →
    GlobalTheory.SqTop.GBig fun {D} T _ _ G _ _ _ _ => ∀ (W : G.Weil), IsStdChar D W.ψ (-1) → ∀ (i j : Fin D.R.m) (A A' WW : HSp D)
      (X : Tri T A A' WW) (δ t0 : ℂ), IsBottomTri W i j X → X.rW.β = 1 →
      ∀ (r : ℂ) (rc : ℝ), r ≠ 0 → (Formalism.MainNotions.StandardLatticesGL3.Crv D ⊤ δ → r = -δ) → (∀ τ, rc * ‖r‖ ^ 2 = 2 * ‖tauE D τ D.host.xi0‖) →
        (∀ (s : T) (Q : ℕ) (P P' : Pair D ⊤ δ t0 Q), IsBottom G s i j (GlobalTheory.SqTop.modT G s) P P' →
          ∀ (ea : P.a = A.rank) (ed : P.d = WW.rank),
            GlobalTheory.AdForm.xiN W.θ A WW ea.symm ed.symm r rc (fun w => starRingEnd ℂ (X.f s w)) ∈ TT D (tor0 D ⊤ δ) P.a P.d ∧
            ∀ (h : GA D P.d) (g : GA D WW) (x : GA D P.a) (y : GA D A),
              GlobalTheory.BotFormula.IsFinPt WW g h → GlobalTheory.BotFormula.IsFinPt A y x →
              GlobalTheory.AdForm.xiN W.θ A WW ea.symm ed.symm r rc (fun w => starRingEnd ℂ (X.ω s (y, g) (X.f s) w)) =
                P.W.Om x h (GlobalTheory.AdForm.xiN W.θ A WW ea.symm ed.symm r rc (fun w => starRingEnd ℂ (X.f s w)))) →
      ∃ κ : ℂ, κ ≠ 0 ∧
        ∀ (s : T) (Q : ℕ) (P P' : Pair D ⊤ δ t0 Q), IsBottom G s i j (GlobalTheory.SqTop.modT G s) P P' →
        ∃ u : ℂ, u ≠ 0 ∧ u ∈ Qbar ∧ (∀ (p : ℕ) [Fact p.Prime], ¬ p ∣ GlobalTheory.SqTop.Qn G s → ∀ lam : Qbar →+* ℂ_[p], ‖lamC lam u‖ = 1) ∧
          ∀ (ea : P.a = A.rank) (ed : P.d = WW.rank),
            GlobalTheory.AdForm.xiN W.θ A WW ea.symm ed.symm r rc (fun w => starRingEnd ℂ (X.f s w)) = (κ * starRingEnd ℂ u) • P.F := by
  intro _ _ _ hInp _
  refine ⟨0, fun ε CF _ => ⟨0, 0, fun C _ D large₂ _ _ hR T Lc μ₀ hL G => ?_⟩⟩
  intro W hW i j A A' WW X δ t0 hX hβ r rc _ hr hrc _
  have hI := hInp D
  by_cases hC : Crv D ⊤ δ
  swap
  · exact ⟨1, one_ne_zero, fun s Q P _ _ => absurd P.crv hC⟩
  obtain rfl := hr hC
  have hcc : D.host.ccK = ⊤ := hR.size.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hIs := hX.is
  have hθ : IsInfFam W.θ := hIs.isVac.2.inf
  have hsc : GlobalTheory.NormExact.IsScale D ⊤ 1 := hcc ▸ GlobalTheory.NormExact.isScale_one D
  have hs : GlobalTheory.NormExact.Setup W.ψ W.θ A WW ⊤ δ 1 := ⟨hW, hθ, hX.std.1, hX.stdW.1, hC, hsc⟩
  have hδ := GlobalTheory.NormExact.delta_ne_zero hC
  have hrc' : rc = (area (lamOf D ⊤ δ))⁻¹ := by
    obtain ⟨τ⟩ : Nonempty D.what₂.Tau := ⟨D.eTau.symm 1⟩
    have h1 := hrc τ
    have h2 := GlobalTheory.NormExact.normSq_scale top_ne_bot hsc δ τ
    have hA := GlobalTheory.NormExact.area_pos hC
    have hx := GlobalTheory.NormExact.xiR_pos D
    rw [map_one, mul_one] at h2
    rw [norm_neg, ← Complex.normSq_eq_norm_sq, h2, GlobalTheory.FockPos.norm_embedding_xi0_eq] at h1
    field_simp
    have : 2 * Formalism.L2.Pj.xiR D * (rc * area (lamOf D ⊤ δ) - 1) = 0 := by linear_combination h1
    have h3 := (mul_eq_zero.1 this).resolve_left (by positivity)
    linarith
  subst hrc'
  have hΛ : ∀ {V : HSp D} (ρ : GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.Rig V), ρ.IsStd → ρ.Λ = stdL D V.rank := fun ρ h => by
    ext y
    rw [h.2.1]
    simp [stdL, Submodule.mem_pi, Submodule.mem_one]
  have hΛA := hΛ X.rA hX.std
  have hΛW := hΛ X.rW hX.stdW
  have hv : IsVacO W.ψ W.θ A WW (fun _ => 1) (fun _ => 1) (stdL D A.rank : Set (Fin A.rank → D.host.E))
      (stdL D WW.rank : Set (Fin WW.rank → D.host.E)) (fun w => starRingEnd ℂ (X.vac w)) := by
    have h := GlobalTheory.VacConj.isVacO_conj_negSp W.ψ W.θ A WW X.rA.s X.rW.s _ _ X.vac hIs.isVac
    rwa [hΛA, hΛW, show X.rA.s = fun _ => 1 from funext fun τ => (hX.std.2.2 τ).1,
      show X.rW.s = fun _ => 1 from funext fun τ => (hX.stdW.2.2 τ).1] at h
  obtain ⟨G0, hG0, hne, hread⟩ := _root_.GlobalTheory.VacRead.vacuum_reads_theta W.ψ W.θ A WW rfl rfl δ hcc hs _ hv
  obtain ⟨κ, hκ, hc⟩ := exists_const hI δ t0 G0 hG0 hne
  have hc' : ∀ (a d : ℕ) (ea : a = A.rank) (ed : d = WW.rank) (e0 : VC D a d → ℂ), GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D ⊤ δ) t0 →
      oddE0 D ⊤ δ t0 a d e0 → e0 ≠ 0 → ∃ u, IsPh u ∧ (κ * u) • e0 ∈ Th D (tor0 D ⊤ δ) (stdL D a) (stdL D d) ∧
        GlobalTheory.NormExact.Reads W.ψ W.θ ea.symm ed.symm ⊤ δ 1 ((κ * u) • e0) (fun w => starRingEnd ℂ (X.vac w)) := by
    rintro a d rfl rfl e0 h1 h2 h3
    obtain ⟨u, hu, e⟩ := hc e0 hC h1 h2 h3
    exact ⟨u, hu, e ▸ hG0, e ▸ hread⟩
  refine ⟨κ, hκ, fun s Q P P' hB => ?_⟩
  have ea : P.a = A.rank := hB.rank.1.trans hX.rank.symm
  have ed : P.d = WW.rank := by rw [hB.rank.2.2.1, ← hIs.rank, hX.rank, hX.rank']
  obtain ⟨u, hu, hTh, hrd⟩ := hc' _ _ ea ed P.e0 P.pt0 P.vac P.W.nz
  obtain ⟨c0, cI⟩ := _root_.GlobalTheory.NuExpModulus.main G hL s i j (X.c s) (hIs.expo s)
  obtain ⟨q1, q2⟩ := GlobalTheory.SqTop.BotT.pde_ne_q hR
  have hm : GoodMod (X.e s) (GlobalTheory.SqTop.modT G s) := ⟨_, _, hIs.idem s, c0, cI.symm,
    GlobalTheory.FunObj.StdDatum.TwBig.modT_isCoprime_bb hL G s (GlobalTheory.T.gridConductorIdealCM_isCoprime_halfDifferent G.pl q1 q2)⟩
  have hν : GlobalTheory.NormExact.HasFinPart (G.nu s i (j + 1))⁻¹ P.W.chV' P.W.ep' := fun x y hxy => by
    rw [hB.chars.2 y, MonoidHom.inv_apply, Circle.coe_inv, _root_.GlobalTheory.FinIdlRead.chr_finIdl _ _ (chrEq_nu G s i j hL) x y hxy]
    exact (Units.val_inv_eq_inv_val _).symm
  obtain ⟨Tm, hTm, hf⟩ := _root_.GlobalTheory.ConjSchr.conj_schroedinger_neg W.ψ hW A WW _ _ _ _ _ _ (hIs.fst s)
  have eν : Lc.mu s (j + 1) * Lc.eta ^ (rankV D i j % 2) / (G.ch.chi (D.R.m - i) * Lc.eta ^ (rankV D i j % 2)) =
      G.nu s i (j + 1) := mul_div_mul_right_eq_div _ _ _
  have eI : X.ideal (locPl G) s = GlobalTheory.SqTop.modT G s := cI
  rw [hΛA, hΛW] at hTm
  rw [eν, eI, hβ] at hf
  obtain ⟨u', hu', hrf⟩ := reads_std hI P ea.symm ed.symm hcc hs hv hTh hrd hm hν (killsCong hL G s i j)
    (hΛA ▸ hIs.rigA.2.1) hB.std hTm hf
  have hw := (hu.mul hu').conj
  refine ⟨_, fun h => by simpa [h] using hw.1, hw.2.1, fun p _ _ lam => hw.2.2 p lam, fun ea' ed' => ?_⟩
  rw [xiN_eq hθ _ _ hδ hrf, Complex.conj_conj, mul_assoc]
end GlobalTheory.StdRead
end
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
theorem _root_.GlobalTheory.T.standard_module_bottom_datum_exists : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
    (∀ D, GlobalTheory.NormSum.Inp D) → GlobalTheory.SqTop.BotSmall →
    GlobalTheory.SqTop.GBig fun {D} T _ _ G _ _ _ _ => ∀ (W : G.Weil), IsStdChar D W.ψ (-1) → ∀ (i j : Fin D.R.m) (A A' WW : HSp D)
      (X : Tri T A A' WW) (δ t0 : ℂ), IsBottomTri W i j X → X.rW.β = 1 →
      ∀ (r : ℂ) (rc : ℝ), r ≠ 0 → (Formalism.MainNotions.StandardLatticesGL3.Crv D ⊤ δ → r = -δ) → (∀ τ, rc * ‖r‖ ^ 2 = 2 * ‖tauE D τ D.host.xi0‖) →
        (∀ (s : T) (Q : ℕ) (P P' : Pair D ⊤ δ t0 Q), IsBottom G s i j (GlobalTheory.SqTop.modT G s) P P' →
          ∀ (ea : P.a = A.rank) (ed : P.d = WW.rank),
            GlobalTheory.AdForm.xiN W.θ A WW ea.symm ed.symm r rc (fun w => starRingEnd ℂ (X.f s w)) ∈ TT D (tor0 D ⊤ δ) P.a P.d ∧
            ∀ (h : GA D P.d) (g : GA D WW) (x : GA D P.a) (y : GA D A),
              GlobalTheory.BotFormula.IsFinPt WW g h → GlobalTheory.BotFormula.IsFinPt A y x →
              GlobalTheory.AdForm.xiN W.θ A WW ea.symm ed.symm r rc (fun w => starRingEnd ℂ (X.ω s (y, g) (X.f s) w)) =
                P.W.Om x h (GlobalTheory.AdForm.xiN W.θ A WW ea.symm ed.symm r rc (fun w => starRingEnd ℂ (X.f s w)))) →
      ∃ κ : ℂ, κ ≠ 0 ∧
        ∀ (s : T) (Q : ℕ) (P P' : Pair D ⊤ δ t0 Q), IsBottom G s i j (GlobalTheory.SqTop.modT G s) P P' →
        ∃ u : ℂ, u ≠ 0 ∧ u ∈ Qbar ∧ (∀ (p : ℕ) [Fact p.Prime], ¬ p ∣ GlobalTheory.SqTop.Qn G s → ∀ lam : Qbar →+* ℂ_[p], ‖lamC lam u‖ = 1) ∧
          ∀ (ea : P.a = A.rank) (ed : P.d = WW.rank),
            GlobalTheory.AdForm.xiN W.θ A WW ea.symm ed.symm r rc (fun w => starRingEnd ℂ (X.f s w)) = (κ * starRingEnd ℂ u) • P.F := by
  first | exact @_root_.GlobalTheory.StdRead.standard_module_bottom_datum | exact _root_.GlobalTheory.StdRead.standard_module_bottom_datum | (intros; apply _root_.GlobalTheory.StdRead.standard_module_bottom_datum <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistCuspFormApproxThetaLift
section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
noncomputable section
namespace GlobalTheory.CuspFormApprox
theorem cuspForm_approx_of_thetaLift (hU : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (N : GlobalTheory.Grid.Node D) (φ : GA D N.V → ℂ), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType θ N φ → ∀ (A : ℕ) (ε : ℝ), 0 < ε → ∃ (n : ℕ) (F : Fin n → N.Maps) (v : Fin n → Formalism.IndefR.Links.SmT N.M), (∀ l, F l ∈ N.Cusp θ) ∧ ∀ g, ‖φ g - ∑ l, F l (v l) g‖ * GlobalTheory.Grow.quotHeight N.V g ^ A ≤ ε) : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ t i j, i ≤ D.R.m → j < D.R.m → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.V i (j + 1)) φ → ∀ b : ℕ, IntegrableOn (fun g => GlobalTheory.Grow.quotHeight (G.V i (j + 1)).V g ^ b * ‖φ g‖) (G.meas t i (j + 1)).fd (G.meas t i (j + 1)).ν ∧ ∀ ε : ℝ, 0 < ε → ∃ (n : ℕ) (Fs : Fin n → (G.V i (j + 1)).Maps) (vs : Fin n → SmT (G.V i (j + 1)).M), (∀ k, Fs k ∈ (G.V i (j + 1)).Cusp R.θ) ∧ IntegrableOn (fun g => GlobalTheory.Grow.quotHeight (G.V i (j + 1)).V g ^ b * ‖(∑ k, Fs k (vs k) g) - φ g‖) (G.meas t i (j + 1)).fd (G.meas t i (j + 1)).ν ∧ ∫ g in (G.meas t i (j + 1)).fd, GlobalTheory.Grow.quotHeight (G.V i (j + 1)).V g ^ b * ‖(∑ k, Fs k (vs k) g) - φ g‖ ∂(G.meas t i (j + 1)).ν ≤ ε := by
  intro _ hP D _ G₀ _ _ Pl0 T A Ks _ _ _ R G hR hG t i j hi hj φ hφ b
  obtain ⟨hμ, h𝓕⟩ := GlobalTheory.PairLift.haar_vert hR hG t hi (j := j + 1) hj
  exact ⟨integrableOn_quotHeight_pow_mul_norm hP.cuspRapidDecay hR.inf hμ h𝓕 hφ b,
    weighted_uniform_approx_cusp_forms hμ h𝓕 hφ.1.cont b (hU D R.θ hR.inf hP _ φ hφ b)⟩
theorem cuspForm_approx_thetaLift : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ t i j, i ≤ D.R.m → j < D.R.m → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.V i (j + 1)) φ → ∀ b : ℕ, IntegrableOn (fun g => GlobalTheory.Grow.quotHeight (G.V i (j + 1)).V g ^ b * ‖φ g‖) (G.meas t i (j + 1)).fd (G.meas t i (j + 1)).ν ∧ ∀ ε : ℝ, 0 < ε → ∃ (n : ℕ) (Fs : Fin n → (G.V i (j + 1)).Maps) (vs : Fin n → SmT (G.V i (j + 1)).M), (∀ k, Fs k ∈ (G.V i (j + 1)).Cusp R.θ) ∧ IntegrableOn (fun g => GlobalTheory.Grow.quotHeight (G.V i (j + 1)).V g ^ b * ‖(∑ k, Fs k (vs k) g) - φ g‖) (G.meas t i (j + 1)).fd (G.meas t i (j + 1)).ν ∧ ∫ g in (G.meas t i (j + 1)).fd, GlobalTheory.Grow.quotHeight (G.V i (j + 1)).V g ^ b * ‖(∑ k, Fs k (vs k) g) - φ g‖ ∂(G.meas t i (j + 1)).ν ≤ ε :=
  _root_.GlobalTheory.CuspFormApprox.cuspForm_approx_of_thetaLift _root_.GlobalTheory.T.twist_cusp_form_approx_weighted
end GlobalTheory.CuspFormApprox
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twist_cuspForm_approx_thetaLift : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ t i j, i ≤ D.R.m → j < D.R.m → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.V i (j + 1)) φ → ∀ b : ℕ, IntegrableOn (fun g => GlobalTheory.Grow.quotHeight (G.V i (j + 1)).V g ^ b * ‖φ g‖) (G.meas t i (j + 1)).fd (G.meas t i (j + 1)).ν ∧ ∀ ε : ℝ, 0 < ε → ∃ (n : ℕ) (Fs : Fin n → (G.V i (j + 1)).Maps) (vs : Fin n → SmT (G.V i (j + 1)).M), (∀ k, Fs k ∈ (G.V i (j + 1)).Cusp R.θ) ∧ IntegrableOn (fun g => GlobalTheory.Grow.quotHeight (G.V i (j + 1)).V g ^ b * ‖(∑ k, Fs k (vs k) g) - φ g‖) (G.meas t i (j + 1)).fd (G.meas t i (j + 1)).ν ∧ ∫ g in (G.meas t i (j + 1)).fd, GlobalTheory.Grow.quotHeight (G.V i (j + 1)).V g ^ b * ‖(∑ k, Fs k (vs k) g) - φ g‖ ∂(G.meas t i (j + 1)).ν ≤ ε := by
  first | exact @_root_.GlobalTheory.CuspFormApprox.cuspForm_approx_thetaLift | exact _root_.GlobalTheory.CuspFormApprox.cuspForm_approx_thetaLift | (intros; apply _root_.GlobalTheory.CuspFormApprox.cuspForm_approx_thetaLift <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistFirstRowScalarMultiple
section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open Matrix ValuativeRel GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.RowVacScalar GlobalTheory.FirstRowTermLaw GlobalTheory.FirstRowEndLaw
noncomputable section
namespace GlobalTheory.FirstRowScalar
variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts}
variable {G : GridData L sc} {W : G.Weil} {U : Set T}
section Red
open GlobalTheory.FunObj.Comparison₂
variable {S κ K : Type} [CommRing S] [CommRing κ] [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] {φ : S →+* κ} {ψ : S →+* K} {r t j a : ℕ} {ea : Ix (Fin r) (Fin t) j ≃ Fin a}
end Red
theorem firstRow_scalar_multiple : _root_.GlobalTheory.FunPr.ThetaLocalInputs → SumOKK → Big fun {D} {_Γ} _ _ {_Pl0} {T} {_A} {_Ks} _ _ _ {R} ch =>
    ∀ (t : T) (k : FinPt ch.G (.grid 0 D.R.m)), finG (ch.G.V (.grid 0 D.R.m)) k ∈ ch.S.levRow t 0 (Nat.zero_le _) →
    ∀ (hk : toXf k ∈ (levEnv D.sp.X' R.βX (R.datXt t)).J) (c : ℂ),
      ch.W.om (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T) (ch.G.toPair (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T) ((ch.S.N.u (.grid 0 D.R.m))⁻¹ * k * ch.S.N.u (.grid 0 D.R.m)).1 1) (ch.S.Z.vac (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T)) = c • ch.S.Z.vac (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T) →
      (((levEnv D.sp.X' R.βX (R.datXt t)).χ ⟨toXf k, hk⟩ : ℂˣ) : ℂ) * c *
          ∏ w : locPl ch.G t, GlobalTheory.FirstRowEndLaw.endLam ch.G t w.1 (GlobalTheory.FirstRowTermLaw.kapAt ch.S.toGridChoice t w.1 k) =
        ∏ w : locPl ch.G t, (locGrid ch.G t w).edgeFactor .one
          (Pi.mulSingle (0, D.R.m) (GlobalTheory.FirstRowTermLaw.kapAt ch.S.toGridChoice t w k)) (.ex 0 D.R.m) :=
  fun _ _ => ⟨0, fun _ _ _ => ⟨0, fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s ch _ _ t k hk hk' c hc =>
    scalar_of_is ch.S.toGridChoice s.core.lev t k hk hk' c hc⟩⟩
end GlobalTheory.FirstRowScalar
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twist_firstRow_scalar_multiple : _root_.GlobalTheory.FunPr.ThetaLocalInputs → SumOKK → Big fun {D} {_Γ} _ _ {_Pl0} {T} {_A} {_Ks} _ _ _ {R} ch =>
    ∀ (t : T) (k : FinPt ch.G (.grid 0 D.R.m)), finG (ch.G.V (.grid 0 D.R.m)) k ∈ ch.S.levRow t 0 (Nat.zero_le _) →
    ∀ (hk : toXf k ∈ (levEnv D.sp.X' R.βX (R.datXt t)).J) (c : ℂ),
      ch.W.om (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T) (ch.G.toPair (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T) ((ch.S.N.u (.grid 0 D.R.m))⁻¹ * k * ch.S.N.u (.grid 0 D.R.m)).1 1) (ch.S.Z.vac (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T)) = c • ch.S.Z.vac (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T) →
      (((levEnv D.sp.X' R.βX (R.datXt t)).χ ⟨toXf k, hk⟩ : ℂˣ) : ℂ) * c *
          ∏ w : locPl ch.G t, GlobalTheory.FirstRowEndLaw.endLam ch.G t w.1 (GlobalTheory.FirstRowTermLaw.kapAt ch.S.toGridChoice t w.1 k) =
        ∏ w : locPl ch.G t, (locGrid ch.G t w).edgeFactor .one
          (Pi.mulSingle (0, D.R.m) (GlobalTheory.FirstRowTermLaw.kapAt ch.S.toGridChoice t w k)) (.ex 0 D.R.m) := by
  first | exact @_root_.GlobalTheory.FirstRowScalar.firstRow_scalar_multiple | exact _root_.GlobalTheory.FirstRowScalar.firstRow_scalar_multiple | (intros; apply _root_.GlobalTheory.FirstRowScalar.firstRow_scalar_multiple <;> assumption)
end
end

