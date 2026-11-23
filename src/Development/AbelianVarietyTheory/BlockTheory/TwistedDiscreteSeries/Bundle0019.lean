module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0016
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalZero
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.Doubling
open MeasureTheory Matrix
open scoped TensorProduct ContDiff ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def resL (A B : HSp D) (x : WO (dblSp A) B) : WO A B := Matrix.of fun i j => x i (finSumFinEquiv (Sum.inl j))

def resR (A B : HSp D) (x : WO (dblSp A) B) : WO A B := Matrix.of fun i j => x i (finSumFinEquiv (Sum.inr j))

def lagr (A B : HSp D) (w : WO A B) : WO (dblSp A) B :=
  Matrix.of fun i j => Sum.elim (fun k => w i k) (fun k => -w i k) (finSumFinEquiv.symm j)

def delta (A B : HSp D) (f₁ f₂ : WO A B → ℂ) : WO (dblSp A) B → ℂ :=
  fun x => f₁ (resL A B x) * conj (f₂ (-resR A B x))

def ip (A B : HSp D) (ν : Measure (WO A B)) (𝓕 : Set (WO A B)) (f₁ f₂ : WO A B → ℂ) : ℂ :=
  ∫ w in 𝓕, f₁ w * conj (f₂ w) ∂ν

def evZero (A B : HSp D) (ν : Measure (WO A B)) (𝓕 : Set (WO A B)) (φ : WO (dblSp A) B → ℂ) : ℂ :=
  ∫ w in 𝓕, φ (lagr A B w) ∂ν

def swSec (A B : HSp D) (omh : GA D (dblSp A) × GA D B →* Module.End ℂ (WO (dblSp A) B → ℂ))
    (ν : Measure (WO A B)) (𝓕 : Set (WO A B)) (φ : WO (dblSp A) B → ℂ) : GA D (dblSp A) → ℂ :=
  fun g => evZero A B ν 𝓕 (omh (g, 1) φ)

def sZero (A B : HSp D) : ℂ := ((B.rank : ℂ) - (A.rank : ℂ)) / 2

def IsKFinVec {S T : HSp D} (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (K : Subgroup (GA D S))
    (φ : WO S T → ℂ) : Prop :=
  FiniteDimensional ℂ (Submodule.span ℂ {f : WO S T → ℂ | ∃ k ∈ K, f = om (k, 1) φ})

def IsSmoothOn (V : HSp D) (Φ : GA D V → ℂ) : Prop :=
  Continuous Φ ∧
  (∃ U : Subgroup (GA D V), IsOpen (U : Set (GA D V)) ∧ ∀ k ∈ U, k ∈ GfC V → ∀ g, Φ (g * k) = Φ g) ∧
  ∀ θ : InfFam D, IsInfFam θ →
    ∀ (k : ℕ) (τs : Fin k → D.what₂.Tau) (Xs : Fin k → Matrix (Fin V.rank) (Fin V.rank) ℂ),
      (∀ i, Xs i ∈ lieAt V (τs i)) → ∀ g,
        ContDiff ℝ ∞ fun t : Fin k → ℝ => Φ (g * (List.ofFn fun i => oneP θ V (τs i) (Xs i) (t i)).prod)

section Clauses

variable (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D) (χB : (AE D)ˣ →* Circle)
  (om : GA D A × GA D B →* Module.End ℂ (WO A B → ℂ))
  (omh : GA D (dblSp A) × GA D B →* Module.End ℂ (WO (dblSp A) B → ℂ))

def ThetaClause : Prop :=
  ∀ f₁ f₂, IsThetaFunO ψ A B f₁ → IsThetaFunO ψ A B f₂ →
    IsThetaFunO ψ (dblSp A) B (delta A B f₁ f₂) ∧
    ∀ (g₁ g₂ : GA D A) (h : GA D B),
      omh (io A (g₁, g₂), h) (delta A B f₁ f₂) =
        (((χB (detA A g₂))⁻¹ : Circle) : ℂ) • delta A B (om (g₁, h) f₁) (om (g₂, h) f₂) ∧
      thetaKO omh (io A (g₁, g₂)) h (delta A B f₁ f₂) =
        thetaKO om g₁ h f₁ * conj (thetaKO om g₂ h f₂) * (((χB (detA A g₂))⁻¹ : Circle) : ℂ)

variable (ν : Measure (WO A B)) (𝓕 : Set (WO A B))

def SectionClause : Prop :=
  ∀ φ, IsThetaFunO ψ (dblSp A) B φ →
    IntegrableOn (fun w => φ (lagr A B w)) 𝓕 ν ∧
    (∀ h : GA D B, evZero A B ν 𝓕 (omh (1, h) φ) = evZero A B ν 𝓕 φ) ∧
    (∀ (p : siegel A) (g : GA D (dblSp A)), swSec A B omh ν 𝓕 φ (p * g) =
      (χB⁻¹ (aP A p) : Circle) * npow (absA D (aP A p)) (sZero A B + (A.rank : ℂ) / 2) * swSec A B omh ν 𝓕 φ g) ∧
    IsSmoothOn (dblSp A) (swSec A B omh ν 𝓕 φ) ∧
    ∀ a : GL (Fin A.rank) (AE D), IsMaj A a → IsKFinVec omh (Khat A a) φ →
      swSec A B omh ν 𝓕 φ ∈ degPS A a χB⁻¹ (sZero A B)

def CoefClause : Prop :=
  ∀ f₁ f₂, IsThetaFunO ψ A B f₁ → IsThetaFunO ψ A B f₂ →
    evZero A B ν 𝓕 (delta A B f₁ f₂) = ip A B ν 𝓕 f₁ f₂ ∧
    ∀ g : GA D A, swSec A B omh ν 𝓕 (delta A B f₁ f₂) (io A (g, 1)) = ip A B ν 𝓕 (om (g, 1) f₁) f₂

end Clauses

def DoublingIso (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D) (χA χB : (AE D)ˣ →* Circle)
    (om : GA D A × GA D B →* Module.End ℂ (WO A B → ℂ)), IsWeilDatumO ψ A B χA χB om →
    ∃ omh : GA D (dblSp A) × GA D B →* Module.End ℂ (WO (dblSp A) B → ℂ),
      IsWeilDatumO ψ (dblSp A) B 1 χB omh ∧ ThetaClause ψ A B χB om omh ∧
      AllSome (fun m : Measure (WO A B) × Set (WO A B) => IsCovolOne (ratL B A) m.1 m.2) fun m =>
        SectionClause ψ A B χB omh m.1 m.2 ∧ CoefClause ψ A B om omh m.1 m.2

section Basic₂

variable (A B : HSp D)

@[simp] theorem resL_lagr (w : WO A B) : resL A B (lagr A B w) = w := by
  ext i j; simp [resL, lagr]

@[simp] theorem resR_lagr (w : WO A B) : resR A B (lagr A B w) = -w := by
  ext i j; simp only [resR, lagr, Matrix.of_apply, Equiv.symm_apply_apply, Sum.elim_inr, Matrix.neg_apply]

theorem delta_lagr (f₁ f₂ : WO A B → ℂ) (w : WO A B) : delta A B f₁ f₂ (lagr A B w) = f₁ w * conj (f₂ w) := by
  simp [delta]

theorem evZero_delta (ν : Measure (WO A B)) (𝓕 : Set (WO A B)) (f₁ f₂ : WO A B → ℂ) :
    evZero A B ν 𝓕 (delta A B f₁ f₂) = ip A B ν 𝓕 f₁ f₂ := by
  simp only [evZero, ip, delta_lagr]

end Basic₂

end GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero

end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
section
namespace I195MixedCoordinates_7862ec877d0c1b045a76795f

open Formalism.BasicNotions Formalism.BasicNotions.TH
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.MixModel MeasureTheory
attribute [local instance] Formalism.BasicNotions.Host.cmStar

public noncomputable abbrev source
    {D : D7} {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (T : HSp D)
    (ψ : AddChar (AF D.host.F) ℂ) (μ : Measure (Mx D T.rank ρ))
    (𝓕 : Set (Mx D T.rank ρ)) (f : WO S T → ℂ) (x : Mx D T.rank ρ) : WO S₀ T → ℂ :=
  fun w₀ => ∫ a in 𝓕, heisO ψ S T (a * d.pY)
    (heisO ψ S T (x * d.pX) (heisO ψ S T (w₀ * d.p0) f)) 0 ∂μ

end I195MixedCoordinates_7862ec877d0c1b045a76795f

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix GlobalTheory.MixModel

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction

variable {D : D7}

abbrev VA (S : HSp D) : Type := Fin S.rank → AE D

def form (S : HSp D) (u v : VA S) : AE D := (fun i => cA D (v i)) ⬝ᵥ (gA S *ᵥ u)

def act (S : HSp D) (g : GA D S) (y : VA S) : VA S := mt S g *ᵥ y

def transv (S : HSp D) (w v : VA S) (y : VA S) : VA S :=
  y + form S y v • w - form S y w • v - (half D * form S v v * form S y w) • w

def IsTransv (S : HSp D) (w v : VA S) (g : GA D S) : Prop := ∀ y, act S g y = transv S w v y

def vecX {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (a : Fin ρ → AE D) : VA S := d.jX *ᵥ a

def ratVec {n : ℕ} (a : Fin n → D.host.E) : Fin n → AE D := fun i => incA D (a i)

def TransvUnitary (D : D7) : Prop :=
  ∀ (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (a : Fin ρ → AE D) (v : VA S), form S (vecX d a) v = 0 →
    ∃ u : GA D S, IsTransv S (vecX d a) v u

def TransvConj (D : D7) : Prop :=
  ∀ (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (a : Fin ρ → AE D) (v : VA S), form S (vecX d a) v = 0 →
    ∀ u g : GA D S, IsTransv S (vecX d a) v u → IsTransv S (act S g (vecX d a)) (act S g v) (g * u * g⁻¹)

def TransvTrivial (D : D7) : Prop :=
  ∀ (S S₀ T : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (ψ : AddChar (AF D.host.F) ℂ) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om →
    ∀ (μ : Measure (Mx D T.rank ρ)) (𝓕 : Set (Mx D T.rank ρ)), IsCovolOne (ratMx D T.rank ρ) μ 𝓕 →
    ∀ (a : Fin ρ → D.host.E) (v : VA S), form S (vecX d (ratVec a)) v = 0 →
    ∀ u : GA D S, IsTransv S (vecX d (ratVec a)) v u →
    ∀ x : Mx D T.rank ρ, x *ᵥ ratVec a = 0 →
    ∀ f : WO S T → ℂ, IsThetaFunO ψ S T f →
      (_root_.I195MixedCoordinates_7862ec877d0c1b045a76795f.source d) T ψ μ 𝓕 (om (u, 1) f) x = (_root_.I195MixedCoordinates_7862ec877d0c1b045a76795f.source d) T ψ μ 𝓕 f x

def TransvLemma (D : D7) : Prop := TransvUnitary D ∧ TransvConj D ∧ TransvTrivial D

end GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction

end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.VacuumFockVectors
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField
open GlobalTheory.Chain
open GlobalTheory.Ker (ipO)

namespace GlobalTheory.IndefiniteRowSideFullHecke.VacuumFockVectors

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {V W : HSp D} {S S' : D.what₂.Tau → SPar}

def creOp (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (M : DSModel V S) (M' : DSModel W S')
    (l : FVar D W.rank V.rank) (g : WO V W → ℂ) : WO V W → ℂ :=
  aPlusAll (heisO ψ V W) θ (fun τ => cplxO (cart M τ) (cart M' τ)) (onb M) (onb M') l g

def annOp (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (M : DSModel V S) (M' : DSModel W S')
    (l : FVar D W.rank V.rank) (g : WO V W → ℂ) : WO V W → ℂ :=
  (-(fockScale D l.1 : ℂ)⁻¹) •
    annih (heisO ψ V W) θ l.1 (cplxO (cart M l.1) (cart M' l.1)) (unitMap (onb M l.1) (onb M' l.1) l.2.1 l.2.2) g

def multiFact {ι : Type} (α : ι →₀ ℕ) : ℕ := α.prod fun _ k => k.factorial


open Classical in
def FockLaws (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (M : DSModel V S) (M' : DSModel W S')
    (f : WO V W → ℂ) : Prop :=
  (∀ P : PolF D W.rank V.rank, IsThetaFunO ψ V W (ptOf ψ θ M M' f P)) ∧
  (∀ (l l' : FVar D W.rank V.rank) (g : WO V W → ℂ), IsThetaFunO ψ V W g →
    creOp ψ θ M M' l (creOp ψ θ M M' l' g) = creOp ψ θ M M' l' (creOp ψ θ M M' l g)) ∧
  (∀ (l l' : FVar D W.rank V.rank) (g : WO V W → ℂ), IsThetaFunO ψ V W g →
    annOp ψ θ M M' l (creOp ψ θ M M' l' g) - creOp ψ θ M M' l' (annOp ψ θ M M' l g) = if l = l' then g else 0) ∧
  (∀ (μ : Measure (WO V W)) (𝓕 : Set (WO V W)), μ.IsAddHaarMeasure →
    IsAddFundamentalDomain (ratL W V) 𝓕 μ → ∀ α β : FVar D W.rank V.rank →₀ ℕ,
      ipO μ 𝓕 (ptOf ψ θ M M' f (MvPolynomial.monomial α 1)) (ptOf ψ θ M M' f (MvPolynomial.monomial β 1)) =
        if α = β then (multiFact α : ℂ) * ipO μ 𝓕 f f else 0) ∧
  Function.Injective (ptOf ψ θ M M' f)

def VacuumFock (D : D7) : Prop :=
  ∀ (V W : HSp D) (S S' : D.what₂.Tau → SPar) (M : DSModel V S) (M' : DSModel W S')
    (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
    ∀ f : WO V W → ℂ, IsVacVec ψ θ M M' f → FockLaws ψ θ M M' f

theorem ptOf_one (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (M : DSModel V S) (M' : DSModel W S')
    (f : WO V W → ℂ) : ptOf ψ θ M M' f 1 = f := by
  have h : (1 : PolF D W.rank V.rank) = MvPolynomial.basisMonomials _ ℂ 0 := by simp
  unfold ptOf pureTensorO pureTensorL
  rw [h, Module.Basis.constr_basis]
  simp [opPow]

end GlobalTheory.IndefiniteRowSideFullHecke.VacuumFockVectors

end
end

