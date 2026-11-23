module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0625
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0001
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0005
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.MovedVacuumRootExistsAlgebraic
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0049
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0044
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
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0628
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0593
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0607
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0618
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SqrtDivMulEqSqrtMul
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InvolutionSphericalHeckeAnti
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0295
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0305
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0430
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1043
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1227
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0601
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0583
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0571
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0377
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0298
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0539
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0057
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0040
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2838
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0052
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0043
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1595

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ExistsUniqueMovedKappaJet
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
noncomputable section
namespace GlobalTheory.MovedKappaEx
theorem jet_kappa_unique : _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type}
    {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}
    (ch : Choice R), ch.Is → ∀ (p : Pair T), DefPair D.R.m p → ∀ (x : FinPt ch.G p.small) (y : FinPt ch.G p.big) (κ κ' : ℂ),
    JetKap ch p x y κ → JetKap ch p x y κ' → κ = κ' := by
  intro hPr hInp D Γ _ _ Pl0 T A Ks _ _ _ R ch hIs p hp x y κ κ' h1 h2
  set F := Iop D (tor0 D D.host.ccK ch.S.Z.δ) (La0 D (tor0 D D.host.ccK ch.S.Z.δ) _ _) (Formalism.MainNotions.TaylorLogMetric.La D (tor0 D D.host.ccK ch.S.Z.δ) (GlobalTheory.MovedDict.srcLat ch.S.toGridChoice p x y) (GlobalTheory.MovedDict.tgtLat ch.S.toGridChoice p x y)) (ch.S.Z.e0 p) with hFdef
  have hF : Differentiable ℂ F :=
    _root_.GlobalTheory.MovedDict.Entire.differentiable_moved_operator_eval hPr hInp ch hIs p hp x y
  obtain ⟨hsd, hsd'⟩ := _root_.GlobalTheory.MovedSD.moved_series_decomposition hPr hInp ch hIs p hp x y
  have hF0 : F ≠ 0 := selfDualLattice_intertwiner_baseVector_ne_zero ch.S.Z.crv ch.S.Z.pt0 (ch.S.Z.e0_is p hp) hsd hsd'
  obtain ⟨α, hα⟩ := GlobalTheory.NatFamily.exists_taylor_ne D hF hF0
  have e := (h1 α).symm.trans (h2 α)
  rw [applyAt0_monomial', applyAt0_monomial', GlobalTheory.ProdThetaConj.taylor_const_mul hF,
    GlobalTheory.ProdThetaConj.taylor_const_mul hF] at e
  have e' := (opp p).injective (mul_left_cancel₀ (ch.S.Z.c0 p).ne_zero e)
  have hP : (α.prod fun v e => period ch.S.Z.δ v.1 ^ e) ≠ 0 :=
    Finsupp.prod_ne_zero_iff.2 fun v _ => pow_ne_zero _ (GlobalTheory.FunObj.period_ne_zero (GlobalTheory.TwoTorsionPt.delta_ne ch.S.Z.crv) v.1)
  have hfac : (α.prod fun _ n => (n.factorial : ℂ)) ≠ 0 :=
    Finsupp.prod_ne_zero_iff.2 fun _ _ => Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
  have e'' := mul_left_cancel₀ (mul_ne_zero hP hfac) (by simpa only [mul_assoc] using e')
  exact mul_right_cancel₀ hα e''
end GlobalTheory.MovedKappaEx
namespace GlobalTheory.MovedKappaEx
theorem exists_moved_kappa : _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type}
    {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}
    (ch : Choice R), ch.Is → ∀ (p : Pair T), DefPair D.R.m p → ∀ (x : FinPt ch.G p.small) (y : FinPt ch.G p.big),
    ∃ κ₀ : ℂ, Mod1All κ₀ ∧
    (∀ (q : ℕ) [Fact q.Prime], EqAt D q (GlobalTheory.SumSize.latAt ch.S.toGridChoice p.small x) (stdL D _) →
      EqAt D q (GlobalTheory.SumSize.latAt ch.S.toGridChoice p.big y) (stdL D _) → ∀ lam : Qbar →+* ℂ_[q], ‖lamC lam κ₀‖ = 1) ∧
    ∀ k : FVar D (ch.G.pT p).rank (ch.G.pS p).rank →₀ ℕ,
      fockIn ch.W ch.S.N.frC p (ch.W.om p (ch.G.toPair p ((x * ch.S.N.u p.small : FinPt ch.G p.small) : Formalism.L2.Theta.GA D (ch.G.V p.small)) ((y * ch.S.N.u p.big : FinPt ch.G p.big) : Formalism.L2.Theta.GA D (ch.G.V p.big))) (ch.S.Z.vac p))
        (MvPolynomial.monomial k 1) 0 = ch.S.Z.c0 p * opp p ((k.prod fun v e => period ch.S.Z.δ v.1 ^ e) *
          Formalism.MainNotions.GL3Theta.applyAt0 D (MvPolynomial.monomial k 1) fun z => κ₀ * Iop D (tor0 D D.host.ccK ch.S.Z.δ) (La0 D (tor0 D D.host.ccK ch.S.Z.δ) _ _) (Formalism.MainNotions.TaylorLogMetric.La D (tor0 D D.host.ccK ch.S.Z.δ) (GlobalTheory.MovedDict.srcLat ch.S.toGridChoice p x y) (GlobalTheory.MovedDict.tgtLat ch.S.toGridChoice p x y)) (ch.S.Z.e0 p) z) := by
  intro hPr hInp D Γ _ _ Pl0 T A Ks _ _ _ R ch hIs p hp x y
  obtain ⟨hns, hnb⟩ := hp.nodes
  have chain : ∀ Q : Finset ℕ, (∀ q ∈ Q, q.Prime) →
      (∀ q ∈ Q, EqAt D q (GlobalTheory.SumSize.latAt ch.S.toGridChoice p.small x) (stdL D _) ∧
        EqAt D q (GlobalTheory.SumSize.latAt ch.S.toGridChoice p.big y) (stdL D _)) →
      ∃ κ, Mod1All κ ∧ (∀ q ∈ Q, ∀ (_ : Fact q.Prime), UnitAt q κ) ∧ JetKap ch p x y κ := by
    intro Q hQ hQx
    obtain ⟨r, s, x₀, hr, hs, hx₀, hsx, rfl⟩ := _root_.GlobalTheory.T.movedKappa_decomposition_exists hPr hInp ch hIs _ hns Q hQ x
    obtain ⟨r', s', y₀, hr', hs', hy₀, hsy, rfl⟩ := _root_.GlobalTheory.T.movedKappa_decomposition_exists hPr hInp ch hIs _ hnb Q hQ y
    obtain ⟨κ₀, hm₀, hu₀, hj₀⟩ := _root_.GlobalTheory.T.moved_vacuum_has_algebraic_root hPr hInp ch hIs p hp x₀ y₀ hx₀ hy₀
    have stepS : ∀ g ∈ splitOff (ch.G.V p.small) Q, ∀ (x' : FinPt ch.G p.small) (κ : ℂ), JetKap ch p x' y₀ κ → Mod1All κ →
        (∀ q ∈ Q, ∀ (_ : Fact q.Prime), UnitAt q κ) →
        ∃ κ', Mod1All κ' ∧ (∀ q ∈ Q, ∀ (_ : Fact q.Prime), UnitAt q κ') ∧ JetKap ch p (g * x') y₀ κ' := by
      have gen : ∀ g : FinPt ch.G p.small, (∃ e, IsSplitIdem D e ∧ (∀ q ∈ Q, OffPrime e q) ∧
          SuppAt e _ (g : GA D (ch.G.V p.small))) → ∀ (x' : FinPt ch.G p.small) (κ : ℂ), JetKap ch p x' y₀ κ → Mod1All κ →
          (∀ q ∈ Q, ∀ (_ : Fact q.Prime), UnitAt q κ) →
          ∃ κ', Mod1All κ' ∧ (∀ q ∈ Q, ∀ (_ : Fact q.Prime), UnitAt q κ') ∧ JetKap ch p (g * x') y₀ κ' := by
        rintro g ⟨e, he, hoff, hsupp⟩ x' κ hj hm hu
        obtain ⟨c, hc, hcu, hjc⟩ := _root_.GlobalTheory.T.splitting_of_moved_kappa_twist hPr hInp ch hIs p hp x' y₀ κ hj e he g 1 hsupp
          (by rw [OneMemClass.coe_one]; exact GlobalTheory.LeviSplitChar.suppAt_one e _)
        rw [one_mul] at hjc
        exact ⟨c * κ, GlobalTheory.FamilyTieProof.mod1All_mul' hc hm,
          fun q hq hf => unitAt_mul hc hm (@hcu q hf (hoff q hq)) (hu q hq hf), hjc⟩
      intro g hg
      induction hg using Subgroup.closure_induction'' with
      | mem g hg => exact gen g hg
      | inv_mem g hg =>
        obtain ⟨e, he, hoff, hsupp⟩ := hg
        exact gen g⁻¹ ⟨e, he, hoff, by rw [InvMemClass.coe_inv]; exact GlobalTheory.SplitPlace.suppAt_inv hsupp⟩
      | one => intro x' κ hj hm hu; exact ⟨κ, hm, hu, by rwa [one_mul]⟩
      | mul g₁ g₂ _ _ h1 h2 =>
        intro x' κ hj hm hu
        obtain ⟨κ₁, hm₁, hu₁, hj₁⟩ := h2 x' κ hj hm hu
        obtain ⟨κ₂, hm₂, hu₂, hj₂⟩ := h1 _ κ₁ hj₁ hm₁ hu₁
        exact ⟨κ₂, hm₂, hu₂, by rwa [mul_assoc]⟩
    have stepB : ∀ g ∈ splitOff (ch.G.V p.big) Q, ∀ (y' : FinPt ch.G p.big) (κ : ℂ), JetKap ch p (s * x₀) y' κ → Mod1All κ →
        (∀ q ∈ Q, ∀ (_ : Fact q.Prime), UnitAt q κ) →
        ∃ κ', Mod1All κ' ∧ (∀ q ∈ Q, ∀ (_ : Fact q.Prime), UnitAt q κ') ∧ JetKap ch p (s * x₀) (g * y') κ' := by
      have gen : ∀ g : FinPt ch.G p.big, (∃ e, IsSplitIdem D e ∧ (∀ q ∈ Q, OffPrime e q) ∧
          SuppAt e _ (g : GA D (ch.G.V p.big))) → ∀ (y' : FinPt ch.G p.big) (κ : ℂ), JetKap ch p (s * x₀) y' κ → Mod1All κ →
          (∀ q ∈ Q, ∀ (_ : Fact q.Prime), UnitAt q κ) →
          ∃ κ', Mod1All κ' ∧ (∀ q ∈ Q, ∀ (_ : Fact q.Prime), UnitAt q κ') ∧ JetKap ch p (s * x₀) (g * y') κ' := by
        rintro g ⟨e, he, hoff, hsupp⟩ y' κ hj hm hu
        obtain ⟨c, hc, hcu, hjc⟩ := _root_.GlobalTheory.T.splitting_of_moved_kappa_twist hPr hInp ch hIs p hp (s * x₀) y' κ hj e he 1 g
          (by rw [OneMemClass.coe_one]; exact GlobalTheory.LeviSplitChar.suppAt_one e _) hsupp
        rw [one_mul] at hjc
        exact ⟨c * κ, GlobalTheory.FamilyTieProof.mod1All_mul' hc hm,
          fun q hq hf => unitAt_mul hc hm (@hcu q hf (hoff q hq)) (hu q hq hf), hjc⟩
      intro g hg
      induction hg using Subgroup.closure_induction'' with
      | mem g hg => exact gen g hg
      | inv_mem g hg =>
        obtain ⟨e, he, hoff, hsupp⟩ := hg
        exact gen g⁻¹ ⟨e, he, hoff, by rw [InvMemClass.coe_inv]; exact GlobalTheory.SplitPlace.suppAt_inv hsupp⟩
      | one => intro y' κ hj hm hu; exact ⟨κ, hm, hu, by rwa [one_mul]⟩
      | mul g₁ g₂ _ _ h1 h2 =>
        intro y' κ hj hm hu
        obtain ⟨κ₁, hm₁, hu₁, hj₁⟩ := h2 y' κ hj hm hu
        obtain ⟨κ₂, hm₂, hu₂, hj₂⟩ := h1 _ κ₁ hj₁ hm₁ hu₁
        exact ⟨κ₂, hm₂, hu₂, by rwa [mul_assoc]⟩
    obtain ⟨κ₁, hm₁, hu₁, hj₁⟩ := stepS s hs x₀ κ₀ hj₀ hm₀ (fun q _ hf => @hu₀ q hf)
    obtain ⟨κ₂, hm₂, hu₂, hj₂⟩ := stepB s' hs' y₀ κ₁ hj₁ hm₁ hu₁
    obtain ⟨c, hc, hcu, hjc⟩ := _root_.GlobalTheory.T.rational_jet_move_exists hPr hInp ch hIs p hp _ _ κ₂ hj₂ r r' hr hr'
    refine ⟨c * κ₂, GlobalTheory.FamilyTieProof.mod1All_mul' hc hm₂, fun q hq hf => unitAt_mul hc hm₂ ?_ (hu₂ q hq hf), ?_⟩
    · obtain ⟨hqx, hqy⟩ := hQx q hq
      rw [mul_assoc] at hqx hqy
      exact @hcu q hf (hsx q hq) (hsy q hq) hqx hqy
    · rw [mul_assoc, mul_assoc]
      exact hjc
  obtain ⟨κ₀, hm, -, hj⟩ := chain ∅ (by simp) (by simp)
  refine ⟨κ₀, hm, fun q hf hx hy lam => ?_, hj⟩
  obtain ⟨κq, -, hu, hjq⟩ := chain {q} (by simpa using hf.out) (by simpa using ⟨hx, hy⟩)
  obtain rfl := _root_.GlobalTheory.MovedKappaEx.jet_kappa_unique hPr hInp ch hIs p hp x y κ₀ κq hj hjq
  exact hu q (Finset.mem_singleton_self q) hf lam
end GlobalTheory.MovedKappaEx
end
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
theorem _root_.GlobalTheory.T.exists_unique_moved_kappa_jet : _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type}
    {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}
    (ch : Choice R), ch.Is → ∀ (p : Pair T), DefPair D.R.m p → ∀ (x : FinPt ch.G p.small) (y : FinPt ch.G p.big),
    ∃ κ₀ : ℂ, Mod1All κ₀ ∧
    (∀ (q : ℕ) [Fact q.Prime], EqAt D q (GlobalTheory.SumSize.latAt ch.S.toGridChoice p.small x) (stdL D _) →
      EqAt D q (GlobalTheory.SumSize.latAt ch.S.toGridChoice p.big y) (stdL D _) → ∀ lam : Qbar →+* ℂ_[q], ‖lamC lam κ₀‖ = 1) ∧
    ∀ k : FVar D (ch.G.pT p).rank (ch.G.pS p).rank →₀ ℕ,
      fockIn ch.W ch.S.N.frC p (ch.W.om p (ch.G.toPair p ((x * ch.S.N.u p.small : FinPt ch.G p.small) : Formalism.L2.Theta.GA D (ch.G.V p.small)) ((y * ch.S.N.u p.big : FinPt ch.G p.big) : Formalism.L2.Theta.GA D (ch.G.V p.big))) (ch.S.Z.vac p))
        (MvPolynomial.monomial k 1) 0 = ch.S.Z.c0 p * opp p ((k.prod fun v e => period ch.S.Z.δ v.1 ^ e) *
          Formalism.MainNotions.GL3Theta.applyAt0 D (MvPolynomial.monomial k 1) fun z => κ₀ * Iop D (tor0 D D.host.ccK ch.S.Z.δ) (La0 D (tor0 D D.host.ccK ch.S.Z.δ) _ _) (Formalism.MainNotions.TaylorLogMetric.La D (tor0 D D.host.ccK ch.S.Z.δ) (GlobalTheory.MovedDict.srcLat ch.S.toGridChoice p x y) (GlobalTheory.MovedDict.tgtLat ch.S.toGridChoice p x y)) (ch.S.Z.e0 p) z) := by
  first | exact @_root_.GlobalTheory.MovedKappaEx.exists_moved_kappa | exact _root_.GlobalTheory.MovedKappaEx.exists_moved_kappa | (intros; apply _root_.GlobalTheory.MovedKappaEx.exists_moved_kappa <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.IsAlgebraicSplitCharacterTwist
section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
noncomputable section
namespace GlobalTheory.SplitCharAlg
open Formalism.L2.Host
open scoped TensorProduct
end GlobalTheory.SplitCharAlg
namespace GlobalTheory.SplitCharAlg
theorem splitCharacter_value_isAlgebraic : ∀ {D : D7} {T : Type} [Finite T] {L : LevCh D T} {μ₀ : T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → L.Is μ₀ →
    IsBottomTri W i j X → ∀ e : AE D, IsSplitIdem D e → ∀ x : (AE D)ˣ, (x : AE D) = e * x + (1 - e) →
      IsAlgebraic ℚ (((G.ch.chi (D.R.m - i) * L.eta ^ (rankV D i j % 2)) x : Circle) : ℂ) := by
  intro D T _ L μ₀ sc G W i j A A' WW X _ _ hL _ e he x hx
  obtain ⟨w, y, rfl⟩ := exists_locIdele he x hx
  have hi1 : 1 ≤ D.R.m - (i : ℕ) := by have := i.2; omega
  have hi2 : D.R.m - (i : ℕ) ≤ D.R.m := Nat.sub_le _ _
  have hchi : (((G.ch.chi (D.R.m - i)) (GlobalTheory.LFun.locIdele D.host.F w y) : Circle) : ℂ) =
      (((G.ch.chiH (D.R.m - i)).loc w y : ℂˣ) : ℂ) :=
    congrArg (fun f => ((f y : ℂˣ) : ℂ)) (GlobalTheory.LFun.locChar_eq_of_chrEq (G.ch.chi_eq _ hi1 hi2) w)
  have heta : ((L.eta (GlobalTheory.LFun.locIdele D.host.F w y) : Circle) : ℂ) = ((L.C.eta.loc w y : ℂˣ) : ℂ) :=
    congrArg (fun f => ((f y : ℂˣ) : ℂ)) (GlobalTheory.LFun.locChar_eq_of_chrEq hL.eta w)
  rw [MonoidHom.mul_apply, Circle.coe_mul, MonoidHom.pow_apply, Circle.coe_pow, hchi, heta]
  exact (isAlgebraic_loc (G.ch.inf _ hi1 hi2) w y).mul ((isAlgebraic_loc L.C.isEta.inf w y).pow _)
end GlobalTheory.SplitCharAlg
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
theorem _root_.GlobalTheory.T.isAlgebraic_splitCharacter_twist : ∀ {D : D7} {T : Type} [Finite T] {L : LevCh D T} {μ₀ : T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → L.Is μ₀ →
    IsBottomTri W i j X → ∀ e : AE D, IsSplitIdem D e → ∀ x : (AE D)ˣ, (x : AE D) = e * x + (1 - e) →
      IsAlgebraic ℚ (((G.ch.chi (D.R.m - i) * L.eta ^ (rankV D i j % 2)) x : Circle) : ℂ) := by
  first | exact @_root_.GlobalTheory.SplitCharAlg.splitCharacter_value_isAlgebraic | exact _root_.GlobalTheory.SplitCharAlg.splitCharacter_value_isAlgebraic | (intros; apply _root_.GlobalTheory.SplitCharAlg.splitCharacter_value_isAlgebraic <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.KerProjectionMaximalThetaSubspace
section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
namespace GlobalTheory.SquareAgree.KerPMax
theorem ker_projection_maximal_thetaSubspace : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁)
    (B : Fr X) (α β : (AE D)ˣ →* Circle) (ν : Measure (GA D W)) (𝓕 : Set (GA D W)) (ν₁ : Measure (GA D W₁))
    (𝓕₁ : Set (GA D W₁)) (ωA : WRep W X) (ωB : WRep W₁ X) (e : Fin X.rank ≃ Fin (W.rank + W₁.rank))
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank)
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (cA : Matrix (Fin W.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W X)
    (cB : Matrix (Fin W₁.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W₁ X),
    IsInfFam θ → IsTriple W W₁ X α β → IsOver ψ θ A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB →
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' →
    ∀ Pi rf rl p p', IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p' →
    ∀ N N' : Submodule ℂ ((Fin W₁.rank × Fin (W.rank + W₁.rank) → AF D.host.F) → ℂ), (∀ Φ₀D, Φ₀D ∈ N ↔ Φ₀D ∈ algD Γ.M' Bs.ψ Bs.emb ∧ ∃ Φ₀ ∈ algF ψ θ false A₁ B, IsDatum Γ.M' ψ cB Φ₀D Φ₀ ∧ p' Φ₀ = 0) →
      IsThetaSubG Γ.M' Bs.ψ Bs.emb om' N' → N ≤ N' → N' = N ∨ N' = algD Γ.M' Bs.ψ Bs.emb := by
  intro hP D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB hθ hT hO hT' Pi rf rl p p' hm N N' hN hN' hle
  have hstd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ := by rw [← hO.psi]; exact hT'.base.std
  obtain ⟨hz, hlin⟩ := isDatum_linear Γ.M' ψ hstd cB
  have hfun : ∀ ΦD ∈ algD Γ.M' Bs.ψ Bs.emb, ∀ Φ₀, IsDatum Γ.M' ψ cB ΦD Φ₀ → Φ₀ ∈ algF ψ θ false A₁ B := by
    intro ΦD hΦD Φ₀ hD
    obtain ⟨Φ₁, hΦ₁, hD₁⟩ := hO.algB' ΦD hΦD
    rw [IsDatum.fun_eq Γ.M' ψ cB cB.surjective hD hD₁]
    exact hΦ₁
  let S : Submodule ℂ Pi :=
    { carrier := {x | ∃ ΦD ∈ N', ∃ Φ₀, IsDatum Γ.M' ψ cB ΦD Φ₀ ∧ p' Φ₀ = x}
      zero_mem' := ⟨0, N'.zero_mem, 0, hz, map_zero p'⟩
      add_mem' := by
        rintro _ _ ⟨ΦD, hΦD, Φ₀, hD, rfl⟩ ⟨ΨD, hΨD, Ψ₀, hE, rfl⟩
        refine ⟨ΦD + ΨD, N'.add_mem hΦD hΨD, Φ₀ + Ψ₀, ?_, map_add p' _ _⟩
        simpa using hlin ΦD ΨD Φ₀ Ψ₀ 1 hD hE
      smul_mem' := by
        rintro c _ ⟨ΦD, hΦD, Φ₀, hD, rfl⟩
        refine ⟨c • ΦD, N'.smul_mem c hΦD, c • Φ₀, ?_, map_smul p' c Φ₀⟩
        simpa using hlin 0 ΦD 0 Φ₀ c hz hD }
  have hc1 : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W₁ (-1) hO.JW₁ 1 = 1 :=
    Subtype.ext (by simp [GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU, map_one])
  have hS1 : ∀ g ∈ GfC X, ∀ x ∈ S, rf g x ∈ S := by
    rintro g hg _ ⟨ΦD, hΦD, Φ₀, hD, rfl⟩
    have hΦ₀ := hfun ΦD (hN'.le hΦD) Φ₀ hD
    have hW := hO.weilB ΦD Φ₀ hD 1 g
    rw [hc1] at hW
    exact ⟨_, _root_.GlobalTheory.T.adelic_stabilizer_finite_of_theta_subgroup hP D X W.rank W₁.rank e Bs Γ Xc om om' hT' hO.JX N' hN' g hg ΦD hΦD, _, hW,
      hm.mapB.eqf g hg Φ₀ hΦ₀⟩
  have hS2 : ∀ τ, ∀ Y ∈ lieAt X τ, ∀ x ∈ S, rl τ Y x ∈ S := by
    rintro τ Y hY _ ⟨ΦD, hΦD, Φ₀, hD, rfl⟩
    obtain ⟨ΨD, hΨD, Φ₁, hΦ₁, hE, hder⟩ := _root_.GlobalTheory.T.adelic_stabilizer_lie_ker_polarization hP D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB
      hθ hT hO hT' Pi rf rl p p' hm N' hN' τ Y hY ΦD hΦD Φ₀ hD
    exact ⟨ΨD, hΨD, Φ₁, hE, hm.mapB.eql τ Y hY Φ₀ (hfun _ (hN'.le hΦD) _ hD) Φ₁ hΦ₁ hder⟩
  rcases hm.irred.2 S hS1 hS2 with h0 | h1
  · left
    refine le_antisymm (fun ΦD hΦD => ?_) hle
    obtain ⟨Φ₁, hΦ₁, hD₁⟩ := hO.algB' ΦD (hN'.le hΦD)
    have hx : p' Φ₁ ∈ S := ⟨ΦD, hΦD, Φ₁, hD₁, rfl⟩
    rw [h0, Submodule.mem_bot] at hx
    exact (hN ΦD).2 ⟨hN'.le hΦD, Φ₁, hΦ₁, hD₁, hx⟩
  · right
    refine le_antisymm hN'.le (fun ΨD hΨD => ?_)
    obtain ⟨Ψ₀, hΨ₀, hE⟩ := hO.algB' ΨD hΨD
    have hx : p' Ψ₀ ∈ S := h1 ▸ Submodule.mem_top
    obtain ⟨ΦD, hΦD, Φ₀, hD, hpe⟩ := hx
    have hdiff : ΨD - ΦD ∈ N := by
      refine (hN _).2 ⟨(algD _ _ _).sub_mem hΨD (hN'.le hΦD), Ψ₀ - Φ₀,
        (algF ψ θ false A₁ B).sub_mem hΨ₀ (hfun _ (hN'.le hΦD) _ hD), ?_, ?_⟩
      · simpa [sub_eq_add_neg] using hlin ΨD ΦD Ψ₀ Φ₀ (-1) hE hD
      · rw [map_sub, hpe, sub_self]
    simpa using N'.add_mem (hle hdiff) hΦD
end GlobalTheory.SquareAgree.KerPMax
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
theorem _root_.GlobalTheory.T.thetaKernel_projection_isMax : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁)
    (B : Fr X) (α β : (AE D)ˣ →* Circle) (ν : Measure (GA D W)) (𝓕 : Set (GA D W)) (ν₁ : Measure (GA D W₁))
    (𝓕₁ : Set (GA D W₁)) (ωA : WRep W X) (ωB : WRep W₁ X) (e : Fin X.rank ≃ Fin (W.rank + W₁.rank))
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank)
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (cA : Matrix (Fin W.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W X)
    (cB : Matrix (Fin W₁.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W₁ X),
    IsInfFam θ → IsTriple W W₁ X α β → IsOver ψ θ A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB →
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' →
    ∀ Pi rf rl p p', IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p' →
    ∀ N N' : Submodule ℂ ((Fin W₁.rank × Fin (W.rank + W₁.rank) → AF D.host.F) → ℂ), (∀ Φ₀D, Φ₀D ∈ N ↔ Φ₀D ∈ algD Γ.M' Bs.ψ Bs.emb ∧ ∃ Φ₀ ∈ algF ψ θ false A₁ B, IsDatum Γ.M' ψ cB Φ₀D Φ₀ ∧ p' Φ₀ = 0) →
      IsThetaSubG Γ.M' Bs.ψ Bs.emb om' N' → N ≤ N' → N' = N ∨ N' = algD Γ.M' Bs.ψ Bs.emb := by
  first | exact @_root_.GlobalTheory.SquareAgree.KerPMax.ker_projection_maximal_thetaSubspace | exact _root_.GlobalTheory.SquareAgree.KerPMax.ker_projection_maximal_thetaSubspace | (intros; apply _root_.GlobalTheory.SquareAgree.KerPMax.ker_projection_maximal_thetaSubspace <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.KernelConjMeanPairingStandardKType
section
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.SumSize GlobalTheory.KerConjMean GlobalTheory.SumSize.OppConj
namespace GlobalTheory.KerConjMean
attribute [local instance] Formalism.BasicNotions.Host.cmStar
section Std
variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R)
end Std
theorem kernel_conj_mean_pairing_standard_KType : _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → DictK → DepthK → PairStdK := by
  intro hP hI hD hDp
  obtain ⟨C1, hC1, hmean⟩ := GlobalTheory.T.exists_const_mean_logArea_logThetaNorm_le
  obtain ⟨F1, k1⟩ := _root_.GlobalTheory.T.kernel_conjugation_average hP hI hD hDp C1 hC1
  obtain ⟨F2, k2⟩ := _root_.GlobalTheory.KerConjMean.ratTopAt_big
  obtain ⟨F3, k3⟩ := _root_.GlobalTheory.T.conjRowAt_of_dict_depth hP hI hD hDp C1 hC1
  obtain ⟨F4, k4⟩ := _root_.GlobalTheory.KerConjMean.ratRowAt_big
  refine ⟨max (max F1 F2) (max F3 F4), fun CF hCF => ?_⟩
  obtain ⟨C01, l1⟩ := k1 CF (by simp only [max_le_iff] at hCF; exact hCF.1.1)
  obtain ⟨C02, l2⟩ := k2 CF (by simp only [max_le_iff] at hCF; exact hCF.1.2)
  obtain ⟨C03, l3⟩ := k3 CF (by simp only [max_le_iff] at hCF; exact hCF.2.1)
  obtain ⟨C04, l4⟩ := k4 CF (by simp only [max_le_iff] at hCF; exact hCF.2.2)
  refine ⟨2 * max (max C01 C02) (max C03 C04), fun ε C hC => ?_⟩
  have hC' : max (max C01 C02) (max C03 C04) ≤ C / 2 := by linarith
  simp only [max_le_iff] at hC'
  obtain ⟨x1, m1⟩ := l1 ε (C / 2) hC'.1.1
  obtain ⟨x2, m2⟩ := l2 ε (C / 2) hC'.1.2
  obtain ⟨x3, m3⟩ := l3 ε (C / 2) hC'.2.1
  obtain ⟨x4, m4⟩ := l4 ε (C / 2) hC'.2.2
  refine ⟨max (max x1 x2) (max x3 x4), fun D large₂ hε hx Γ _ _ Pl0 T A Ks _ _ _ R F hS ch hIs hAt hF => ?_⟩
  simp only [max_le_iff] at hx
  obtain ⟨hL1, hLrd, hLd⟩ := sizes D large₂ Γ Pl0 T A Ks R F hS
  obtain ⟨hmA, hmT⟩ := hmean D (hI D) ch.S.Z.δ ch.S.Z.t0 ch.S.Z.crv ch.S.Z.pt0 _ hL1 hLrd hLd
  exact pairStdAt_of ch C large₂.sc.b C1 hmA hmT
    (fun σ => _root_.GlobalTheory.KerConjMean.ext_finite_nonempty D (hI D) ch.S.Z.δ ch.S.Z.t0 ch.S.Z.crv ch.S.Z.pt0 σ)
    (m2 D large₂ hε hx.1.2 Γ Pl0 T A Ks R F hS ch hIs hAt hF)
    (m1 D large₂ hε hx.1.1 Γ Pl0 T A Ks R F hS ch hIs hAt hF)
    (m4 D large₂ hε hx.2.2 Γ Pl0 T A Ks R F hS ch hIs hAt hF)
    (m3 D large₂ hε hx.2.1 Γ Pl0 T A Ks R F hS ch hIs hAt hF)
end GlobalTheory.KerConjMean
end
end

section
open GlobalTheory.SumSize GlobalTheory.RowClaim GlobalTheory.SumSize.OppConj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conj_mean_kernel_pairing : _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → DictK → DepthK → PairStdK := by
  first | exact @_root_.GlobalTheory.KerConjMean.kernel_conj_mean_pairing_standard_KType | exact _root_.GlobalTheory.KerConjMean.kernel_conj_mean_pairing_standard_KType | (intros; apply _root_.GlobalTheory.KerConjMean.kernel_conj_mean_pairing_standard_KType <;> assumption)
end
end

