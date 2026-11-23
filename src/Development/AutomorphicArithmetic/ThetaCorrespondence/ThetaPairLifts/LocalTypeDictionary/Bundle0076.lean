module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0464
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalBlockDetBlockTriangular
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0466
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1577
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2822
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0628
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0604
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0585
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0633
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0636
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0656
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0593
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0003
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0015
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0522
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0639
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0144
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0069
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle0003

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistFlipStartHighestVector
section
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
namespace GlobalTheory.FlipStart
theorem flipStart_highestVector : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.RowClaim.Big fun {D} _ _ _ _ {T} _ _ _ _ _ {R} ch => ∀ (t : T) (j : Fin D.R.m) (g : Sch ch.G (.down t 0 j)), (j : ℕ) + 1 = D.R.m → HEq g (R.vX t) → ∃ c : ℂˣ, c ∈ xiVals R.toLevCh t ∧ ∀ e : AE D, IsIdemSum e (locPl ch.G t) → ∀ Φ : ch.G.Datum, IsLocVec ch.W (.mu t 0 j) e (ch.rm.vT 0 j) ((c : ℂ) • GlobalTheory.FlipStart.givenFn ch.S.B t Φ e (.down t 0 j)) g := by
  intro _
  refine ⟨0, fun ε CF _ => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F s ch hch _ => ?_⟩⟩
  intro t j g hj hg
  refine ⟨1, one_mem _, fun e he Φ => ?_⟩
  rw [Units.val_one, one_smul]
  obtain ⟨e', he', hθ⟩ := _root_.GlobalTheory.FlipTopChain.last_step_theta s ch hch t j g hj hg
  have hL : R.toLevCh.Is A.μ0 := s.core.lev
  have hS : IsSelfDualC (ch.G.pS (.mu t 0 j)) (ch.G.latS (.mu t 0 j)) :=
    (colY_isV D T R.toLevCh A.μ0 hL j j.2.le).sd
  have hT : IsSelfDualC (ch.G.pT (.mu t 0 j)) (ch.G.latT (.mu t 0 j)) :=
    (colY_isV D T R.toLevCh A.μ0 hL (j + 1) j.2).sd
  have hv := ch.rm.vT_is t 0 j (Nat.zero_le _) j.2
  have hsub : GlobalTheory.FlipTop.topPl R.toLevCh t ⊆ locPl ch.G t := by
    classical
    intro w hw
    rcases Finset.mem_union.1 hw with h | h
    · exact Finset.mem_union_left _ (levelChainTypePlaces_subset_chosenPlaces ch.G hL t h)
    · exact Finset.mem_union_right _ h
  obtain ⟨h1, h2⟩ := _root_.GlobalTheory.ThetaEnlarge.isThetaAt_enlarge hS hT hv he he' hsub (GlobalTheory.T.gridFirstColumnStep_isSchwartzBruhat_half ch.G ch.S.B hL t he' j j.2) hθ
  have hAA : ∀ w ∈ locPl ch.G t, w ∉ GlobalTheory.FlipTop.topPl R.toLevCh t →
      ((∀ a ∈ D.host.AA, Valued.v (algebraMap D.host.E (Kw w) a) ≤ 1) ∧
        ∃ a ∈ D.host.AA, Valued.v (algebraMap D.host.E (Kw w) a) = 1) := by
    intro w hw _
    have hb := GlobalTheory.FunObj.Good.badInt_notMem hL (GlobalTheory.FlipIntegrand.pde_ne_q_of_setting s) (hch.guard t) hw
    have h2q := fun h => hb (GlobalTheory.HalfCompare.mem_of_dvd h (Dvd.intro _ rfl))
    have hN := fun h => hb (GlobalTheory.HalfCompare.mem_of_dvd h (Dvd.intro_left _ rfl))
    refine ⟨fun a ha => ?_, ⟨_, GlobalTheory.HostClear.absNorm_mem_AA D, ?_⟩⟩
    · rw [GlobalTheory.FunObj.Good.valued_alg]
      exact GlobalTheory.FunObj.Good.valuation_le_one_of_mem h2q (Or.inl ha)
    · rw [GlobalTheory.FunObj.Good.valued_alg]
      exact GlobalTheory.FunObj.Good.valuation_nat hN
  rw [_root_.GlobalTheory.FlipTop.prodHalf_topFn_eq_givenFn ch.G ch.S.B hL t he he' hAA Φ j j.2] at h1 h2
  exact ⟨h1, h2⟩
end GlobalTheory.FlipStart
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twist_flipStart_highestVector : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.RowClaim.Big fun {D} _ _ _ _ {T} _ _ _ _ _ {R} ch => ∀ (t : T) (j : Fin D.R.m) (g : Sch ch.G (.down t 0 j)), (j : ℕ) + 1 = D.R.m → HEq g (R.vX t) → ∃ c : ℂˣ, c ∈ xiVals R.toLevCh t ∧ ∀ e : AE D, IsIdemSum e (locPl ch.G t) → ∀ Φ : ch.G.Datum, IsLocVec ch.W (.mu t 0 j) e (ch.rm.vT 0 j) ((c : ℂ) • GlobalTheory.FlipStart.givenFn ch.S.B t Φ e (.down t 0 j)) g := by
  first | exact @_root_.GlobalTheory.FlipStart.flipStart_highestVector | exact _root_.GlobalTheory.FlipStart.flipStart_highestVector | (intros; apply _root_.GlobalTheory.FlipStart.flipStart_highestVector <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistRealProjectionAverageMonomial
section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
noncomputable section
theorem GlobalTheory.RealProj.realProjection_average_monomial : ∀ {D : D7} {T : Type} [Finite T] {L : LevCh D T} {μ₀ : T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → L.Is μ₀ →
    IsBottomTri W i j X →
    ∃ n : D.what₂.Tau → ℕ, ∀ (κ : Measure (GinfC A')), κ.IsMulLeftInvariant → IsProbabilityMeasure κ →
      ∀ (t : T), ∀ x ∈ GfC A', ∀ h ∈ GfC WW, ∀ k : FVar D WW.rank A'.rank →₀ ℕ,
        ∃ (m : ℕ) (r : Fin m → ℂ) (U : Fin m → GlobalTheory.NormSum.Tup D A'.rank WW.rank n), (∀ p, IsAlgebraic ℚ (r p)) ∧
          ∫ g, X.ker' W.ψ W.θ t (MvPolynomial.monomial k 1) h (x * (g : GA D A')) ∂κ =
            ∑ p, r p * X.ker' W.ψ W.θ t (GlobalTheory.NormSum.minorPol D (U p)) h x := by
  intro D T _ L μ₀ sc G W i j A A' WW X hPr hInp hL hB
  obtain ⟨m, ρ, hρm, hρs, hact⟩ := _root_.GlobalTheory.T.twist_boundary_real_action hPr hInp hL hB
  obtain ⟨n, hn⟩ := _root_.GlobalTheory.MinorFrame.AvgCore.average_monomial_eq_sum_prodMinors (ι := D.what₂.Tau) A'.rank WW.rank m
  refine ⟨n, fun κ hκ hκp t x hx h hh k => ?_⟩
  let Λ : GlobalTheory.MinorFrame.Pol D.what₂.Tau WW.rank A'.rank →ₗ[ℂ] ℂ :=
    (LinearMap.proj (R := ℂ) (φ := fun _ : WO A' WW => ℂ) 0).comp
      ((X.ω' t (x, h)).comp (pureTensorO W.ψ W.θ A' WW X.rA'.s X.rW.s X.rA'.B X.rW.B (X.f' t)))
  have hΛ : ∀ P, Λ P = X.ker' W.ψ W.θ t P h x := fun P => rfl
  obtain ⟨hTop, -, -, -, hBorel⟩ := Formalism.IndefR.Eqv.ga_facts D A'
  haveI : BorelSpace (GinfC A') := Subtype.borelSpace _
  have hleft (u : GinfC A') : AEMeasurable (u * ·) κ :=
    (continuous_const_mul u).measurable.aemeasurable
  obtain ⟨M, r, U, hr, hI⟩ := hn κ hκp hκ hleft ρ hρm hρs Λ k
  refine ⟨M, r, U, hr, ?_⟩
  have e : (fun g : GinfC A' => X.ker' W.ψ W.θ t (MvPolynomial.monomial k 1) h (x * (g : GA D A'))) =
      fun g => (∏ τ, (ρ g τ : Matrix (Fin A'.rank) (Fin A'.rank) ℂ).det ^ (m τ)) *
        Λ (GlobalTheory.MinorFrame.colSub (fun τ => (ρ g τ : Matrix (Fin A'.rank) (Fin A'.rank) ℂ)) (MvPolynomial.monomial k 1)) := by
    funext g; rw [hact t x hx h hh g, hΛ]
  rw [e, hI]
  rfl
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
theorem _root_.GlobalTheory.T.twist_realProjection_average_monomial : ∀ {D : D7} {T : Type} [Finite T] {L : LevCh D T} {μ₀ : T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → L.Is μ₀ →
    IsBottomTri W i j X →
    ∃ n : D.what₂.Tau → ℕ, ∀ (κ : Measure (GinfC A')), κ.IsMulLeftInvariant → IsProbabilityMeasure κ →
      ∀ (t : T), ∀ x ∈ GfC A', ∀ h ∈ GfC WW, ∀ k : FVar D WW.rank A'.rank →₀ ℕ,
        ∃ (m : ℕ) (r : Fin m → ℂ) (U : Fin m → GlobalTheory.NormSum.Tup D A'.rank WW.rank n), (∀ p, IsAlgebraic ℚ (r p)) ∧
          ∫ g, X.ker' W.ψ W.θ t (MvPolynomial.monomial k 1) h (x * (g : GA D A')) ∂κ =
            ∑ p, r p * X.ker' W.ψ W.θ t (GlobalTheory.NormSum.minorPol D (U p)) h x := by
  first | exact @_root_.GlobalTheory.RealProj.realProjection_average_monomial | exact _root_.GlobalTheory.RealProj.realProjection_average_monomial | (intros; apply _root_.GlobalTheory.RealProj.realProjection_average_monomial <;> assumption)
end
end

