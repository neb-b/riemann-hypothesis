module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.IndefiniteRowSideFullHecke.QuasiFamilyPeriods

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {ρ : ℕ} {B : BesLev D ρ} {J : JacLev D ρ}
  {L' : HSp D} {ζ' : Fin L'.rank → D.host.E}

def conjTr (l : Link B L' ζ') (S : HSp D) (f : WO B.L S → ℂ) : WO S L' → ℂ := fun w => star (f (l.κ S w))

def JacobiConj (ψ : AddChar (AF D.host.F) ℂ) (J : JacLev D ρ) (l : Link B L' ζ') : Prop :=
  ∀ n ∈ flagN J.d, ∀ f : WO B.L J.W₀ → ℂ,
    conjTr l J.W₀ (jacT ψ J.d B.L (yZero B.L ρ B.ζ) n f) = jacS ψ J.d L' (zEll L' ρ ζ') n (conjTr l J.W₀ f)

structure IsQuasiFam (ψ : AddChar (AF D.host.F) ℂ) (S L : HSp D) (Y : GA D S → WO S L → ℂ) : Prop where
  cont : Continuous fun p : GA D S × WO S L => Y p.1 p.2
  quasi : ∀ h γ w, Y h (ratW L S γ + w) = ψ (-(symplOH S L (ratW L S γ) w)) * Y h w
  left : ∀ γ ∈ GQ S, ∀ h w, Y (γ * h) w = Y h (w ⬝ mt S γ)

structure PeriodsAgree (s : StepBF ψ B J) (l : Link B L' ζ') (φ : GA D B.A → ℂ) (Ξ : WO B.V₀ J.W₀ → ℂ)
    (G' : GA D J.W → ℂ) : Prop where

  handInt : ∀ (h : GA D J.W₀) (w : WO J.W₀ L'), IntegrableOn
    (fun h₀ => φ h₀ * s.om₀ (B.o.emb (h₀, 1), h) Ξ ((B.o.resS J.W₀).symm (0, l.κ J.W₀ w))) B.vA.𝓕 B.vA.μ

  kerInt : ∀ n ∈ flagN J.d, ∀ h : GA D J.W₀,
    IntegrableOn (fun h₀ => φ h₀ * fjKer ψ J.d B.o B.ζ s.om₀ Ξ h₀ n h) B.vA.𝓕 B.vA.μ

  ker_eq : ∀ n ∈ flagN J.d, ∀ h : GA D J.W₀,
    ∫ h₀ in B.vA.𝓕, φ h₀ * fjKer ψ J.d B.o B.ζ s.om₀ Ξ h₀ n h ∂B.vA.μ = J.ker ψ ζ' (handBF s l φ Ξ) n h

  absProd : AbsConv J.v0.μ J.v0.𝓕 J.vN.ν J.vN.𝓝 (fjAllFun ψ J.d B.o B.ζ s.om₀ B.vA.μ B.vA.𝓕 φ G' Ξ)

  absCons : AbsConv J.v0.μ J.v0.𝓕 J.vN.ν J.vN.𝓝 (fjSrcKerFun ψ J.d (J.ker ψ ζ' (handBF s l φ Ξ)) G')

  per_eq : J.perAll ψ B s.om₀ φ G' Ξ = J.per ψ ζ' (handBF s l φ Ξ) G'

def PeriodLink (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (ρ : ℕ) (B : BesLev D ρ) (J : JacLev D ρ) (s : StepBF ψ B J)
    (L' : HSp D) (ζ' : Fin L'.rank → D.host.E), IsLineVec L' ζ' → ∀ l : Link B L' ζ',
    JacobiConj ψ J l ∧
    ∀ φ : GA D B.A → ℂ, IsContAut B.A φ → ∀ Ξ : WO B.V₀ J.W₀ → ℂ, IsThetaFunO ψ B.V₀ J.W₀ Ξ →
      IsThetaFam ψ J.W₀ L' (handBF s l φ Ξ) ∧
      ∀ G' : GA D J.W → ℂ, RapidDec J.W G' → PeriodsAgree s l φ Ξ G'

def PeriodLinkQuasi (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (ρ : ℕ) (B : BesLev D ρ) (J : JacLev D ρ) (s : StepBF ψ B J)
    (L' : HSp D) (ζ' : Fin L'.rank → D.host.E), IsLineVec L' ζ' → ∀ l : Link B L' ζ',
    JacobiConj ψ J l ∧
    ∀ φ : GA D B.A → ℂ, IsContAut B.A φ → ∀ Ξ : WO B.V₀ J.W₀ → ℂ, IsThetaFunO ψ B.V₀ J.W₀ Ξ →
      IsQuasiFam ψ J.W₀ L' (handBF s l φ Ξ) ∧
      ∀ G' : GA D J.W → ℂ, RapidDec J.W G' → PeriodsAgree s l φ Ξ G'

end GlobalTheory.IndefiniteRowSideFullHecke.QuasiFamilyPeriods

end
