module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0052
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHaarSmul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2842
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2904
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3129
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1561
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3095
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2708
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareStandingTripleThetaSecond
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2832
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2818
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2822
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlResidueSurjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3121
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2936
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PolynomialRouteSubmodule
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0291
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ExistsNeZeroOfIsMatch
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TripleFrameBaseExists
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0301
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0324
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0694
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0695
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0320
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0323
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0492
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0693
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.EmbeddingXiZeroNeZero
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0524
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0504
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0295
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0489
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1665
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1645
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0518
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawWeilGlobalFactor
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0290
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0302
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0311
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0386
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0305
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilModelRationalStructure
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LieActionFockOperatorsScalarsTrace
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0479
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0532
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0427
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0493
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilModelCharacterMatch
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0541
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilModelArchimedeanExponent
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsWeilModelOfExponents
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0285
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LsumMapDomainSome
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0001

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta Formalism.L2.DIV IsDedekindDomain NumberField MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SqTower GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.ChainFr GlobalTheory.SquareDict GlobalTheory.SquareComm
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.ConstRatio (Factor)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.ThetaRegularizationComparison


open GlobalTheory.RegCompare in
theorem thetaInt_wop_intg {D : D7} {M X : HSp D} {ω : GlobalTheory.Grid.WRep M X} {ν : Measure (GA D M)} {𝓕 : Set (GA D M)}
    (hν : IsHaarFD M ν 𝓕) {Φ : WO M X → ℂ} (hL : ∀ γ ∈ GQ M, ∀ g h, thetaKO ω (γ * g) h Φ = thetaKO ω g h Φ)
    (hΦ : Intg ω ν 𝓕 Φ) (z : GA D M →₀ ℂ) : thetaInt ω ν 𝓕 (wop ω z Φ) = zdeg z • thetaInt ω ν 𝓕 Φ := by
  haveI := hν.1
  have key := fun h k => setIntegral_mul_right' M ν 𝓕 hν.2 (fun g => thetaKO ω g h Φ)
    (fun γ hγ u => hL γ hγ u h) (hΦ h) k
  have hi : ∀ k, Intg ω ν 𝓕 (ω (k, 1) Φ) := fun k h => by simpa only [thetaKO_right] using (key h k).1
  have he : ∀ k, thetaInt ω ν 𝓕 (ω (k, 1) Φ) = thetaInt ω ν 𝓕 Φ := fun k => by
    funext h
    simp only [thetaInt, thetaKO_right]
    exact (key h k).2
  rw [wop_apply, thetaInt_sum _ fun k _ => (hi k).smul _]
  simp only [thetaInt_smul, he, zdeg, Finsupp.sum, Finset.sum_smul]


theorem tmul_cancel_left {P Q : Type} [AddCommGroup P] [Module ℂ P] [AddCommGroup Q] [Module ℂ Q] {x : P} (hx : x ≠ 0) {u u' : Q}
    (h : x ⊗ₜ[ℂ] u = x ⊗ₜ[ℂ] u') : u = u' := by
  obtain ⟨l, hl⟩ := Module.Projective.exists_dual_eq_one ℂ hx
  have := congrArg (TensorProduct.lid ℂ Q ∘ LinearMap.rTensor Q l) h
  simpa [hl] using this

theorem tmul_cancel_right {P Q : Type} [AddCommGroup P] [Module ℂ P] [AddCommGroup Q] [Module ℂ Q] {y : Q} (hy : y ≠ 0) {u u' : P}
    (h : u ⊗ₜ[ℂ] y = u' ⊗ₜ[ℂ] y) : u = u' :=
  tmul_cancel_left hy (by simpa using congrArg (TensorProduct.comm ℂ P Q) h)

theorem eq_of_regConst (hK : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree) {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts}
    {G : GridData L sc} {μ₀ : T} (hL : L.Is μ₀) {W : G.Weil} {B : Frames G} {ρ : RealMatch W} {t : T} {i j : Fin D.R.m}
    (hst : SquareStanding G t) {M : Vol G} (hM : M.Is t) {Θ Θ'} (hΘ : IsMatched B t ρ i j Θ Θ') {g g₁}
    (hne : ∫ u in M.fd _, kerBig W Θ g g₁ u ∂M.ν _ ≠ 0) {z} (hz : zdeg z ≠ 0)
    (hi : IntegrableOn (translates z (kerSmall W Θ' g g₁)) (M.fd _) (M.ν _)) {c c₀ : ℂ}
    (hc : zdeg z * ∫ u in M.fd _, kerBig W Θ g g₁ u ∂M.ν _ = c * ∫ u in M.fd _, translates z (kerSmall W Θ' g g₁) u ∂M.ν _)
    (h₀ : RegConst W B ρ t i j c₀) : c₀ = c := by
  obtain ⟨J, hJ⟩ := reg_const hK hL W B ρ t i j hst M hM Θ Θ' hΘ g g₁
  obtain ⟨z₀, hz₀, ⟨-, hi₀⟩, e₀⟩ := h₀ M hM Θ Θ' hΘ g g₁
  rw [hJ z hi] at hc
  rw [hJ z₀ hi₀] at e₀
  have e1 : ∫ u in M.fd _, kerBig W Θ g g₁ u ∂M.ν _ = c * J := mul_left_cancel₀ hz (by linear_combination hc)
  have e2 : ∫ u in M.fd _, kerBig W Θ g g₁ u ∂M.ν _ = c₀ * J := mul_left_cancel₀ hz₀ (by linear_combination e₀)
  have hJ0 : J ≠ 0 := fun h => hne (by rw [e1, h, mul_zero])
  exact mul_right_cancel₀ hJ0 (e2.symm.trans e1)


end GlobalTheory.ThetaRegularizationComparison

end
