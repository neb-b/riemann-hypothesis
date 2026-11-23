module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0011
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualFamilyOfIsLattice

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Definitions.LatticeFrames.DoubleCollapse
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl

variable {D : D7}

def SplitPt.IsIdele {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k)
    (x : kˣ) (a : (AE D)ˣ) : Prop := (a : AE D) = p.sec x + (1 - p.e)

def chrPow (χ : (AE D)ˣ →* Circle) (a : (AE D)ˣ) (e : ℤ) : ℂ := ((χ a ^ e : Circle) : ℂ)

def LiftExact (D : D7) : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (q : Unif k)
    (χ : AddChar k Circle) (hχ : HasConductor χ 1), ∃ e : ℤ, (e = 1 ∨ e = -1) ∧
    ∀ (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D),
    CoCpt S → ∀ (vS : Vol S) (χS χT : (AE D)ˣ →* Circle) (om : Om S T), IsWeilDatumO ψ S T χS χT om →
    CharUnramAt D χS p.v → CharUnramAt D χT p.v → ∀ (α : Frame p S n') (β : Frame p T n) (P : Pair k n') (Q : Pair k n),
    ∀ a, p.IsIdele q.unit a → ∀ (LS : Lat S) (LT : Lat T) (f₀ f : WO S T → ℂ), Over ψ α β LS LT f₀ (phiOne P Q) f →
    ∀ φ₀, RamAt α P φ₀ → ∀ ε : 𝓀[k]ˣ,
      sOp β Q q (resChar χ hχ q) ε (liftT om vS.μ vS.𝓕 φ₀ f) =
        ((((resCard k : ℝ) ^ (((Fintype.card n : ℝ) - Fintype.card n') / 2) : ℝ) : ℂ) * chrPow χS a e * chrPow χT a (-e)) •
          liftT om vS.μ vS.𝓕 (sOp α P q (resChar χ hχ q) ε φ₀) f

def RamUnitary (D : D7) : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k)
    (n : Type) [Fintype n] [DecidableEq n] (q : Unif k) (χ : AddChar k Circle) (hχ : HasConductor χ 1) (ε : 𝓀[k]ˣ) (S : HSp D),
    CoCpt S → ∀ (vS : Vol S) (β : Frame p S n) (P : Pair k n) (φ φ' : GA D S → ℂ), RamAt β P φ → RamAt β P φ' →
      ∫ g in vS.𝓕, sOp β P q (resChar χ hχ q) ε φ g * star (sOp β P q (resChar χ hχ q) ε φ' g) ∂vS.μ =
        (resCard k : ℂ) ^ Fintype.card n * ∫ g in vS.𝓕, φ g * star (φ' g) ∂vS.μ

end GlobalTheory.FinPl

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.LatticeFrames.SphericalEisensteinSeriesOnGroup
section
noncomputable section

open scoped Matrix NNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RegSch

variable {D : D7}

structure Lvl (V : HSp D) where

  L : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)

  c : GL (Fin V.rank) (AE D)

def Lvl.K {V : HSp D} (l : Lvl V) : Subgroup (GA D V) := levelAll D.sp.cm.sig V.gram l.L l.c

def Lvl.Good {V : HSp D} (l : Lvl V) : Prop :=
  Submodule.IsFullLattice D.host.E l.L ∧ (∀ v, IsSelfDualAt D.sp.cm.sig V.gram l.L v) ∧ IsMaj V l.c

def Lvl.form {V : HSp D} (l : Lvl V) : Mx D V.rank V.rank := adj (l.c⁻¹).1 * (l.c⁻¹).1

theorem Lvl.Good.isCompact_K {V : HSp D} {l : Lvl V} (h : l.Good) : IsCompact (l.K : Set (GA D V)) :=
  haveI := h.1
  isCompact_levelAll (isCMExt_host D) _ _ _

section SlopeTestRemainingChoices

variable {T T₀ : HSp D} {r : ℕ} (d : HypDec T T₀ r) (K : Subgroup (GA D T))

def sphericalSectionIwasawa (s : ℂ) : GA D T → ℂ := fun h => npow (iwAbs (absDet d) K h) (s + rhoH T r)

def sphericalEisensteinSeriesOnGroup (h : GA D T) : ℂ → ℂ := fun s => cosetSum (stab d) (GQ T) (sphericalSectionIwasawa d K s) h

end SlopeTestRemainingChoices

section Centre

variable (θ : InfFam D) (n : ℕ) (τ : D.what₂.Tau)

end Centre

section Ops

variable {n : ℕ}

def projS {T : HSp D} {K : Subgroup (GA D T)} (ν : Measure K) (Φ : Mx D T.rank n → ℂ) : Mx D T.rank n → ℂ :=
  fun x => ∫ k, Φ (mt T (k : GA D T)⁻¹ * x) ∂ν

def ikS {T T' : HSp D} {t : ℕ} (d : HypDec T T' t) (μ : Measure (Mx D t n)) (Φ : Mx D T.rank n → ℂ) : Mx D T'.rank n → ℂ :=
  fun a => ∫ x, Φ (d.jX * x + d.j0 * a) ∂μ

variable (θ : InfFam D) (τ : D.what₂.Tau)

variable {θ} {V V₀ : HSp D} {r : ℕ} (ω : StdUnn.G D n →* Module.End ℂ (schwartzA θ V.rank n))

variable (d : HypDec V V₀ r) (K : Subgroup (GA D V))

def eisS (H : StdUnn.G D n → ℝ≥0) (Φ : schwartzA θ V.rank n) (g : StdUnn.G D n) : ℂ → ℂ :=
  fun s => cosetSum (StdUnn.P D n) (StdUnn.GF D n) (StdUnn.sect ω H Φ s) g

end Ops

end GlobalTheory.RegSch

end
end

