module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0025
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0033
public import Development.AbelianVarietyTheory.Definitions.Foundations.ContinuousOfMemCcSmooth
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.EmbedsLevelZeroDepthZero

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GeometricConstantEquiv
section
noncomputable section

open NumberField IsDedekindDomain

namespace GlobalTheory.IndefiniteRowSideFullHecke.GeometricConstantEquiv

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (i : Fin D.R.m) (w : WeightFamilies.Wt D ((i : ℕ) + 1))

abbrev Cusp : Type := T.cuspA ((i : ℕ) + 1) (wtA w) w.n

local instance cuspModule : Module T.Q.c.F (Cusp T i w) :=
  (T.cuspA ((i : ℕ) + 1) (wtA w) w.n).module

abbrev res (σ : D.what₂.LL →+* ℂ) : T.Q.c.F →+* ℂ := σ.comp (algebraMap T.Q.c.F D.what₂.LL)

def iotaW : (T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (Fin (Wc D i).rank → D.host.E) :=
  LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast (rank_Wc i)) ∘ₗ T.iota ((i : ℕ) + 1)

def IsLift (g : G) (κ : GA D (Wc D i)) : Prop :=
  Lev.IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g) κ

set_option synthInstance.maxHeartbeats 100000

def IsGeo (ρ : G →* Module.End T.Q.c.F (Cusp T i w)) : Prop :=
  ∃ lev : G → (T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (T.Q.Dw ((i : ℕ) + 1)).La,
    LevIs R i (iotaW T i) T.Q.l.M (T.Q.l.Mb.map (T.Q.H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E)) lev ∧
    ActLev (Xo := T.Q.Xo ((i : ℕ) + 1)) T.Q.c (fun g => (lev g, LinearMap.id)) ∧
    ∀ g (f : Cusp T i w), ((ρ g f : Cusp T i w) : T.R ((i : ℕ) + 1)) =
      actLev (Xo := T.Q.Xo ((i : ℕ) + 1)) T.Q.c (fun g => (lev g, LinearMap.id)) g (f : T.R ((i : ℕ) + 1))

def ReadTwist (ρ : G →* Module.End T.Q.c.F (Cusp T i w)) : Prop :=
  ∀ σ : D.what₂.LL →+* ℂ, GoodEmb T.Q.c (res T σ) → ∀ hV : T.V ((i : ℕ) + 1) (res T σ) = Wc D i,
    ∀ (g : G) (κ : GA D (T.V ((i : ℕ) + 1) (res T σ))), IsLift T R i g (cast (congrArg (GA D) hV) κ) →
      ∀ (f : Cusp T i w) (x : GA D (T.V ((i : ℕ) + 1) (res T σ))),
        T.phiJ ((i : ℕ) + 1) (res T σ) (wtA w) ((ρ g f : Cusp T i w) : T.R ((i : ℕ) + 1)) x =
          σ (((R.FW i).chi g : D.what₂.LLˣ) : D.what₂.LL) *
            T.phiJ ((i : ℕ) + 1) (res T σ) (wtA w) (f : T.R ((i : ℕ) + 1)) (x * κ)

def IsIntegralForm (f : Cusp T i w) : Prop :=
  ∀ (la : HeightOneSpectrum (𝓞 T.Q.c.F)) (y : T.PtM ((i : ℕ) + 1) la),
    T.nrmM ((i : ℕ) + 1) la y (f : T.R ((i : ℕ) + 1)) ≤ 1

def KeepsIntegral (ρ : G →* Module.End T.Q.c.F (Cusp T i w)) : Prop :=
  ∀ g f, IsIntegralForm T i w f → IsIntegralForm T i w (ρ g f)

def ConstEquiv : Prop :=
  ∀ σ : D.what₂.LL →+* ℂ, GoodEmb T.Q.c (res T σ) → ∀ hV : T.V ((i : ℕ) + 1) (res T σ) = Wc D i,
    ∀ ρ : G →* Module.End T.Q.c.F (Cusp T i w), IsGeo T R i w ρ →
    ∀ chi : G →* (T.Q.c.F)ˣ,
      (∀ g, algebraMap T.Q.c.F D.what₂.LL (chi g : T.Q.c.F) = (((R.FW i).chi g : D.what₂.LLˣ) : D.what₂.LL)) →
    ∀ ℓ : G → GA D (T.V ((i : ℕ) + 1) (res T σ)), (∀ g, IsLift T R i g (cast (congrArg (GA D) hV) (ℓ g))) →
      CEquiv (T.V ((i : ℕ) + 1) (res T σ)) (res T σ)
        ((rdU (T.U ((i : ℕ) + 1) (res T σ))).comp (T.cuspA ((i : ℕ) + 1) (wtA w) w.n).subtype)
        (T.dict ((i : ℕ) + 1) (res T σ)) (T.mu ((i : ℕ) + 1) (res T σ)) (T.cE ((i : ℕ) + 1) (res T σ)) ρ chi ℓ


omit [Algebra T.Q.c.F D.what₂.LL] in
def IsKappa : Prop :=
  ∀ τ : D.what₂.Tau,
    (∀ k : Fin (D.R.sigW ((i : ℕ) + 1)).1, w.aP τ k = aPl D i ((Wc D i).sig (tauE D τ)).1 τ k) ∧
    (∀ k : Fin (D.R.sigW ((i : ℕ) + 1)).2,
      w.aM τ k = aMi D i ((Wc D i).sig (tauE D τ)).1 ((Wc D i).sig (tauE D τ)).2 τ k) ∧ w.n = D.R.nV

def GeoActAt : Prop :=
  ∃ ρ : G →* Module.End T.Q.c.F (Cusp T i w), IsGeo T R i w ρ ∧ ReadTwist T R i w ρ ∧ KeepsIntegral T i w ρ

end GlobalTheory.IndefiniteRowSideFullHecke.GeometricConstantEquiv
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HeckeTransferRankOne
section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain

namespace GlobalTheory.IndefiniteRowSideFullHecke.HeckeTransferRankOne

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT
  Formalism.L2.Pj

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

section Real

variable {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

end Real

theorem rank_Vc (i : Fin D.R.m) : (Vc D i).rank = D.R.nV ∧ D.R.nV = D.R.r + D.R.t :=
  ⟨D.sp.V_rank _ (Nat.le_add_left _ _) i.2, rfl⟩

end GlobalTheory.IndefiniteRowSideFullHecke.HeckeTransferRankOne
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.StandardMaximalParabolic
section
open MeasureTheory ValuativeRel GlobalTheory.SmGL GlobalTheory.SplitWeil

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.StandardMaximalParabolic

section Groups

variable (R : Type) [CommRing R] {a b r : ℕ}

def stdMaxParab (h : a + b = r) : Subgroup (GL (Fin r) R) := parab R (two (stdSum h))

def stdMaxRad (h : a + b = r) : Subgroup (GL (Fin r) R) := unipRad R (two (stdSum h))

variable {R}

def conjBy {G : Type} [Group G] (g : G) (H : Subgroup G) : Subgroup G := H.map (MulAut.conj g).toMonoidHom

def IsParabRad (P N : Subgroup (GL (Fin r) R)) : Prop :=
  ∃ (s : ℕ) (d : Fin s → ℕ) (h : ∑ i, d i = r) (g : GL (Fin r) R),
    P = conjBy g (parab R (stdBlocks d h)) ∧ N = conjBy g (unipRad R (stdBlocks d h))

def NoFixed {Q W : Type} [Group Q] [AddCommGroup W] [Module ℂ W] (τ : Representation ℂ Q W) (H : Subgroup Q) : Prop :=
  ∀ w : W, (∀ u ∈ H, τ u w = w) → w = 0

end Groups

def idemGL (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {r : ℕ}
    [MeasurableSpace (GL (Fin r) k)] (μ : Measure (GL (Fin r) k)) {W : Type} [AddCommGroup W] [Module ℂ W]
    (τ : Representation ℂ (GL (Fin r) 𝓀[k]) W) : GL (Fin r) k → ℂ :=
  GlobalTheory.Orb.typeIdem μ (GlobalTheory.LocGL.redK k (Fin r)) τ

def TypeConstTermVanish : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (r a b : ℕ) (h : a + b = r), 0 < a → 0 < b →
  ∀ (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (τ : Representation ℂ (GL (Fin r) 𝓀[k]) W),
    τ.IsIrreducible → NoFixed τ (stdMaxRad 𝓀[k] h) →
  ∀ [MeasurableSpace (GL (Fin r) k)] [BorelSpace (GL (Fin r) k)] (μ : Measure (GL (Fin r) k)) [μ.IsHaarMeasure],
  ∀ φ ∈ SB (GL (Fin r) k), ∀ f : GL (Fin r) k → ℂ,
    (f = GlobalTheory.AutomorphicL2Unitary.conv μ (idemGL k μ τ) φ ∨ f = GlobalTheory.AutomorphicL2Unitary.conv μ φ (idemGL k μ τ)) →
  ∀ P N : Subgroup (GL (Fin r) k), IsParabRad P N → (∃ g₀, P ≤ conjBy g₀ (stdMaxParab k h)) →
  ∀ (ν : Measure N) [ν.IsHaarMeasure] (x y : GL (Fin r) k),
    Integrable (fun u : N => f (x * u * y)) ν ∧ ∫ u : N, f (x * u * y) ∂ν = 0

theorem mem_conjBy {G : Type} [Group G] {g x : G} {H : Subgroup G} : x ∈ conjBy g H ↔ g⁻¹ * x * g ∈ H :=
  ⟨by rintro ⟨u, hu, rfl⟩; simpa [mul_assoc] using hu, fun h => ⟨_, h, by simp [mul_assoc]⟩⟩

theorem mem_stdMaxParab {R : Type} [CommRing R] {a b r : ℕ} (h : a + b = r) {g : GL (Fin r) R} :
    g ∈ stdMaxParab R h ↔ ∀ i j : Fin r, (j : ℕ) < a → a ≤ (i : ℕ) → (g : Matrix (Fin r) (Fin r) R) i j = 0 := by
  rw [stdMaxParab, mem_parab_two]
  refine ⟨fun H i j hj hi => ?_, fun H j i => H _ _ (by simp) (by simp)⟩
  have := H ⟨i - a, by omega⟩ ⟨j, hj⟩
  have e1 : stdSum h (Sum.inr ⟨i - a, by omega⟩) = i := Fin.ext (by simp; omega)
  have e2 : stdSum h (Sum.inl ⟨j, hj⟩) = j := Fin.ext (by simp)
  rwa [e1, e2] at this

end GlobalTheory.IndefiniteRowSideFullHecke.StandardMaximalParabolic
end
end

