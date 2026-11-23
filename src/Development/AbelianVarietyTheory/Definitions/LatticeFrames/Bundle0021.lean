module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0166
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0145
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0164
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1240
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0070
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0013
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TailRd
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.OnFramesRdApply
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValLastX
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.VacOfShape

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Definitions.LatticeFrames.ConclusionZero
section
noncomputable section
namespace GlobalTheory.Core.Rk.IP.FockModel
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem resEta_one_dbl (A : HSp D) {χ : (AE D)ˣ →* Circle} {k : ℕ} (hr : ResEta D χ k) : ResEta D 1 (dblSp A).rank :=
  ⟨hr.1, fun e he a => by
    have h4 := he.2.2.1 (idF D a)
    have h5 : Units.map (Algebra.norm (AF D.host.F) : AE D →* AF D.host.F) (idF D a) = a ^ 2 := Units.ext (by
      change Algebra.norm (AF D.host.F) (algebraMap (AF D.host.F) (AE D) a.1) = _
      have := t2Space_adeleRing' (F := D.host.F)
      have : Nontrivial (AF D.host.F) :=
        (NumberField.AdeleRing.algebraMap_injective (NumberField.RingOfIntegers D.host.F) D.host.F).nontrivial
      rw [Algebra.norm_algebraMap, Module.finrank_baseChange, D.sp.cm.deg2, Units.val_pow_eq_pow_val])
    rw [h5, map_pow] at h4
    change (1 : Circle) = e a ^ (A.rank + A.rank)
    rw [← two_mul, pow_mul, h4, one_pow]⟩

end GlobalTheory.Core.Rk.IP.FockModel

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.LatticeFrames.SOnCols
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.KJInf Formalism.L2.Forms GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing GlobalTheory.FinPl
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeeSaw

variable {D : D7} {c : Comm D} {ρ : RealD c} {t : Tup c} (A : ClsK ρ t)
  {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {ι : Type} (o : TDat c k ι)

def ClsK.IsFam (j : ℕ) (hj : j ≤ D.R.m) (Φ : t.Ch j → c.Fr j → GA D (c.X j) → ℂ) : Prop :=
  ∃ val : ∀ β, A.cl j β → FrN D (ρ.N j) → ℂ, (∀ β a, val β a ∈ ValC _ (ρ.lam j)) ∧
    ∀ β y, ∀ γ ∈ GQ (c.X j), ∀ a, ∀ x ∈ GinfC (c.X j), ∀ (κ : A.U j β) y',
      IsTr (ρ.r j hj x) (ρ.fr j y) y' → Φ β y (γ * (A.h j β a * x) * κ.1) = (A.chi j β κ : ℂ) * val β a y'

structure ClsK.LevT : Prop where
  stab : ∀ j, j ≤ D.R.m → ∀ β i g, g • o.Q j i = o.Q j i → ∃ h : (o.β j i).gl g ∈ A.U j β, A.chi j β ⟨_, h⟩ = 1
  dec : ∀ j, j ≤ D.R.m → ∀ β, ∀ κ ∈ A.U j β, ∃ g : ι → GL (Fin (c.X j).rank) k, (∀ i, g i • o.Q j i = o.Q j i) ∧
    ∃ κ' ∈ grpOff (c.X j) (fun x => ∃ i, x = (o.p i).v), κ = (o.I.map fun i => (o.β j i).gl (g i)).prod * κ'

structure ClsK.FullT : Prop where
  ram : ∀ j, j ≤ D.R.m → ∀ ψ ∈ t.Ram j, ∀ β y, t.rd j β ψ y ∈ o.Ram j
  full : ∀ j hj Φ, A.IsFam j hj Φ → (∀ β y, Φ β y ∈ o.Ram j) → ∃ ψ ∈ t.Ram j, ∀ β y, t.rd j β ψ y = Φ β y

def SOnCols (D : D7) : Prop :=
  ∀ (c : Comm D) (ρ : RealD c) (t : Tup c) (A : ClsK ρ t) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (o : TDat c k ι), c.Is → ρ.Is → A.Forms →
    o.I.Nodup → (∀ i, i ∈ o.I) → (Function.Injective fun i => (o.p i).v) → A.LevT o → A.FullT o →
    ∃ S : ∀ j, (ι → 𝓀[k]ˣ) → t.Col j → t.Col j, ∀ j, j ≤ D.R.m → ∀ η, ∀ ψ ∈ t.Ram j,
      S j η ψ ∈ t.Ram j ∧ ∀ β y, t.rd j β (S j η ψ) y = o.S (fun _ => η) j (t.rd j β ψ y)

def RamIff (D : D7) : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (n : Type) [Fintype n] [DecidableEq n] (S : HSp D) (β : Frame p S n) (P : Pair k n)
    (g : 𝓀[k]ˣ → GL n k), (∀ s, g s • P = s • P) → ∀ φ : GA D S → ℂ,
      RamAt β P φ ↔ IsContAut S φ ∧ (∀ x, x • P = P → rTrans (β.gl x) φ = φ) ∧ ∑ᶠ s, rTrans (β.gl (g s)) φ = 0

end GlobalTheory.SeeSaw

end
end

