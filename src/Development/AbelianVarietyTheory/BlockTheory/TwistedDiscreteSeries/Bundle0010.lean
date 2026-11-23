module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0027
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0013
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0033
public import Development.AbelianVarietyTheory.Definitions.Jets.EmbShortThLeThetaPlain
public import Formalism.LocalToGlobal.IndefiniteReal.RealSeparation.Bundle0002

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.IsometryCarriesCharacter
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.IndefR.Lev Formalism.IndefR.Links Formalism.IndefR.Mult
open scoped TensorProduct

namespace GlobalTheory.IndefiniteRowSideFullHecke.IsometryCarriesCharacter

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

abbrev mmul {A : Type} [CommRing A] {l m n : ℕ} (x : Matrix (Fin l) (Fin m) A) (y : Matrix (Fin m) (Fin n) A) :
    Matrix (Fin l) (Fin n) A := x * y

def IsIsom (V V' : HSp D) (R : Type) [CommRing R] [Algebra D.host.F R]
    (j : Matrix (Fin V'.rank) (Fin V.rank) (D.host.E ⊗[D.host.F] R)) : Prop :=
  Function.Bijective j.mulVec ∧
    Formalism.UG.cT (Formalism.UG.sigR D.sp.cm.sig R) j * V'.gram.map (Formalism.UG.inclE (F := D.host.F) R) * j =
      V.gram.map (Formalism.UG.inclE (F := D.host.F) R)

def IsLocLatIsom (V V' : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E))
    (Λ' : Submodule (𝓞 D.host.E) (Fin V'.rank → D.host.E)) (v : HeightOneSpectrum (𝓞 D.host.F))
    (j : Matrix (Fin V'.rank) (Fin V.rank) (D.host.E ⊗[D.host.F] v.adicCompletion D.host.F)) : Prop :=
  IsIsom V V' (v.adicCompletion D.host.F) j ∧
    j.mulVec '' (Formalism.L2.Herm.locL v Λ : Set _) = (Formalism.L2.Herm.locL v Λ' : Set _)

def IsLatIsom (V V' : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E))
    (Λ' : Submodule (𝓞 D.host.E) (Fin V'.rank → D.host.E)) (j : Matrix (Fin V'.rank) (Fin V.rank) (EAf D)) : Prop :=
  IsIsom V V' (Formalism.L2.Herm.Af D.host.F) j ∧
    j.mulVec '' (Formalism.L2.Herm.hatL (F := D.host.F) Λ : Set _) = (Formalism.L2.Herm.hatL (F := D.host.F) Λ' : Set _)

def OnePlaceOver (T : Set (Formalism.L2.DIV.Pl D.host.E)) : Prop :=
  ∀ PP ∈ T, ∀ PP' ∈ T, ¬ IsConjPl PP PP'

def MatchesAt (V V' : HSp D) (β : GL (Fin V.rank) (EAf D)) (β' : GL (Fin V'.rank) (EAf D))
    (T : Set (Formalism.L2.DIV.Pl D.host.E)) (j : Matrix (Fin V'.rank) (Fin V.rank) (EAf D)) : Prop :=
  ∃ u : Matrix (Fin V'.rank) (Fin V.rank) (Formalism.L2.Herm.intAf D.host.F D.host.E),
    mmul β'.val (u.map (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype) = mmul j β.val ∧
      ∀ PP ∈ T, ∀ a b, Formalism.L2.DIV.resS D.host.F PP (u a b) = if a.val = b.val then 1 else 0

def castDat {n n' : ℕ} (h : n = n') (L : Formalism.L2.DIV.LevDat D.host.E ℂ n) : Formalism.L2.DIV.LevDat D.host.E ℂ n' where
  r := L.r
  hr := L.hr.trans h.le
  t := L.t
  s := L.s
  Pg := L.Pg
  Q := L.Q
  P := L.P
  cg := L.cg
  xq := L.xq

def IsConjBy (V V' : HSp D) (j : Matrix (Fin V'.rank) (Fin V.rank) (EAf D)) (φ : GfC V ≃ₜ* GfC V') : Prop :=
  ∀ g : GfC V, mmul (finE V' (φ g : GA D V')).val j = mmul j (finE V (g : GA D V)).val

def inA (V : HSp D) (R : Finset (GfC V)) : Finset (GA D V) := R.map (Function.Embedding.subtype _)

def imA {V V' : HSp D} (φ : GfC V ≃ₜ* GfC V') (R : Finset (GfC V)) : Finset (GA D V') :=
  inA V' (R.map φ.toEquiv.toEmbedding)

def ReadIn {n : ℕ} (L : Formalism.L2.DIV.LevDat D.host.E ℂ n) (T : Set (Formalism.L2.DIV.Pl D.host.E)) : Prop :=
  (∀ PP ∈ L.Pg, PP ∈ T) ∧ ∀ PP ∈ L.Q, PP ∈ T

structure Carries (V V' : HSp D) (h : V.rank = V'.rank)
    (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (Λ' : Submodule (𝓞 D.host.E) (Fin V'.rank → D.host.E))
    (β : GL (Fin V.rank) (EAf D)) (β' : GL (Fin V'.rank) (EAf D)) (M : ℕ) (T : Set (Formalism.L2.DIV.Pl D.host.E))
    (φ : GfC V ≃ₜ* GfC V') : Prop where

  stabLoc : ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (g : GfC V),
    Formalism.UG.bc (Formalism.UG.prV v) (finE V (g : GA D V)) ∈ Formalism.UG.levelVL D.sp.cm.sig V.gram v Λ ↔
      Formalism.UG.bc (Formalism.UG.prV v) (finE V' (φ g : GA D V')) ∈ Formalism.UG.levelVL D.sp.cm.sig V'.gram v Λ'

  supp : ∀ (f : Formalism.L2.Theta.AE D) (g : GfC V), SuppF V f (g : GA D V) ↔ SuppF V' f (φ g : GA D V')

  det : ∀ g : GfC V, (Formalism.L2.Theta.mt V' (φ g : GA D V')).det = (Formalism.L2.Theta.mt V (g : GA D V)).det

  lev : ∀ L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank, ReadIn L T → ∀ g : GfC V,
    (g : GA D V) ∈ levG V β L ↔ (φ g : GA D V') ∈ levG V' β' (castDat h L)

  chi : ∀ L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank, ReadIn L T → ∀ g : GfC V, (g : GA D V) ∈ levG V β L →
    levChi V' β' (castDat h L) (φ g : GA D V') = levChi V β L (g : GA D V)

  lift : ∀ L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank, ReadIn L T → ∀ (g0 : Formalism.L2.DIV.G0 L.Pg L.r) (g : GfC V),
    IsLevelLift V β L g0 (g : GA D V) ↔ IsLevelLift V' β' (castDat h L) g0 (φ g : GA D V')

  sph : ∀ S : Finset (HeightOneSpectrum (𝓞 D.host.F)),
    (∀ v : HeightOneSpectrum (𝓞 D.host.F), (M : 𝓞 D.host.F) ∈ v.asIdeal → v ∈ S) →
    ∀ g : GfC V, (g : GA D V) ∈ KsphC V S ↔ (φ g : GA D V') ∈ KsphC V' S

  heckeElt : ∀ (P : Formalism.L2.DIV.Pl D.host.E) (e : Formalism.L2.Theta.AE D) (ϖ : D.host.E) (k : ℕ),
    (M : 𝓞 D.host.E) ∉ P.asIdeal → Formalism.L2.NTheta.IsIdemAt e P → ∀ g : GfC V,
    Formalism.L2.NTheta.IsHeckeElt V e ϖ k (g : GA D V) ↔ Formalism.L2.NTheta.IsHeckeElt V' e ϖ k (φ g : GA D V')

  heckeAt : ∀ (P : Formalism.L2.DIV.Pl D.host.E) (k : ℕ), (M : 𝓞 D.host.E) ∉ P.asIdeal → ∀ g : GfC V,
    IsHeckeAt V P k (g : GA D V) ↔ IsHeckeAt V' P k (φ g : GA D V')

  divAt : ∀ (P : Formalism.L2.DIV.Pl D.host.E) (e f : Formalism.L2.Theta.AE D) (ϖ : D.host.E) (d : List ℤ),
    (M : 𝓞 D.host.E) ∉ P.asIdeal → IsPrimeIdem P e f → ∀ g : GfC V,
    DivAt V e ϖ d (g : GA D V) ↔ DivAt V' e ϖ d (φ g : GA D V')

  opAt : ∀ L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank, ReadIn L T →
    ∀ (S : Finset (HeightOneSpectrum (𝓞 D.host.F))) (P : Formalism.L2.DIV.Pl D.host.E) (k : ℕ),
    (M : 𝓞 D.host.E) ∉ P.asIdeal → ∀ R : Finset (GfC V),
    IsHeckeOpAt V (levS V β L) (levChi V β L) S P k (inA V R) ↔
      IsHeckeOpAt V' (levS V' β' (castDat h L)) (levChi V' β' (castDat h L)) S P k (imA φ R)

  opFull : ∀ L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank, ReadIn L T →
    ∀ (S : Finset (HeightOneSpectrum (𝓞 D.host.F))) (P : Formalism.L2.DIV.Pl D.host.E) (d : List ℤ),
    (M : 𝓞 D.host.E) ∉ P.asIdeal → ∀ R : Finset (GfC V),
    Hecke₂ V (levS V β L) (levChi V β L) S P d (inA V R) ↔
      Hecke₂ V' (levS V' β' (castDat h L)) (levChi V' β' (castDat h L)) S P d (imA φ R)

def GlobalIsometry (D : D7) : Prop :=
  ∀ (V V' : HSp D), V.rank = V'.rank →
    ∀ (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (Λ' : Submodule (𝓞 D.host.E) (Fin V'.rank → D.host.E))
      (β : GL (Fin V.rank) (EAf D)) (β' : GL (Fin V'.rank) (EAf D)) (N N' : ℕ),
      IsSDFrame V β Λ N → IsSDFrame V' β' Λ' N' →
      ∀ T : Set (Formalism.L2.DIV.Pl D.host.E), OnePlaceOver T →
        ∃ j, IsLatIsom V V' Λ Λ' j ∧ MatchesAt V V' β β' T j

def InducedIso (D : D7) : Prop :=
  ∀ (V V' : HSp D) (h : V.rank = V'.rank)
    (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (Λ' : Submodule (𝓞 D.host.E) (Fin V'.rank → D.host.E))
    (β : GL (Fin V.rank) (EAf D)) (β' : GL (Fin V'.rank) (EAf D)) (N N' : ℕ),
    IsSDFrame V β Λ N → IsSDFrame V' β' Λ' N' →
    ∀ (T : Set (Formalism.L2.DIV.Pl D.host.E)) (j : Matrix (Fin V'.rank) (Fin V.rank) (EAf D)),
      IsLatIsom V V' Λ Λ' j → MatchesAt V V' β β' T j →
      ∃ φ : GfC V ≃ₜ* GfC V', IsConjBy V V' j φ ∧ Carries V V' h Λ Λ' β β' (N * N') T φ

end GlobalTheory.IndefiniteRowSideFullHecke.IsometryCarriesCharacter

end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.LevelGroupLifts
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.LevelGroupLifts

open NumberField Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.Pj Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level)
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def idealLatHat (V : HSp D) (I : Ideal (𝓞 D.host.E)) :
    AddSubgroup (Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E) :=
  AddSubgroup.closure {w | ∃ b ∈ I, ∃ z ∈ latGHat V 1, w = halfVec V b z}

def IsLift (V : HSp D) {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} (Dw : Datum H) (l : Level H)
    (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E))
    (g : LaMod Dw l ≃ₗ[𝓞 D.host.E] LaMod Dw l) (k : GA D V) : Prop :=
  k ∈ GfC V ∧ gLat V k = (latHat V : Set (Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E)) ∧
    ∀ a b : Dw.La, (Submodule.Quotient.mk b : LaMod Dw l) = g (Submodule.Quotient.mk a) →
      (finHom V k).1.mulVec (finVec V (ι a)) - finVec V (ι b) ∈ idealLatHat V l.Mb

abbrev LevGrp (T : CoreJ D) (j : ℕ) : Type :=
  LaMod (T.Q.Dw j) T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (T.Q.Dw j) T.Q.l

def iotaAt (T : CoreJ D) (j : ℕ) (σ : T.Q.c.F →+* ℂ) (hr : (T.V j σ).rank = D.R.r) :
    (T.Q.Dw j).La →ₗ[𝓞 D.host.E] (Fin (T.V j σ).rank → D.host.E) :=
  LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast hr) ∘ₗ T.iota j

attribute [local instance 2000] Submodule.module

def IsGeoRep (T : CoreJ D) (j : ℕ) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ)
    (ρ : LevGrp T j →* (T.cuspA j a n →ₗ[T.Q.c.F] T.cuspA j a n)) : Prop :=
  ∀ g f, ((ρ g f : T.cuspA j a n) : T.R j) =
    actLev (Xo := T.Q.Xo j) T.Q.c (GlobalTheory.FormTies.levFull (T.Q.Dw j) T.Q.l) g (f : T.R j)

def IsChiDet (T : CoreJ D) (j : ℕ) {V : HSp D} (ℓ : LevGrp T j → GA D V) (chi : LevGrp T j →* T.Q.c.Fˣ) : Prop :=
  ∀ g x, FinUnit x → IsDetRoot V (ℓ g) x →
    T.σ₀ ((chi g : T.Q.c.Fˣ) : T.Q.c.F) * ((T.chiW j T.σ₀ x : Circle) : ℂ) = 1

def UnitConstEquivariant : Prop :=
  ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, InR D j → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n →
    ∀ (ρ : LevGrp T j →* (T.cuspA j a n →ₗ[T.Q.c.F] T.cuspA j a n)), IsGeoRep T j a n ρ →
    ∀ (chi : LevGrp T j →* T.Q.c.Fˣ) (σ : T.Q.c.F →+* ℂ), GoodEmb T.Q.c σ →
    ∀ (hr : (T.V j σ).rank = D.R.r) (ℓ : LevGrp T j → GA D (T.V j σ)),
      (∀ g, IsLift (T.V j σ) (T.Q.Dw j) T.Q.l (iotaAt T j σ hr) g (ℓ g)) → IsChiDet T j ℓ chi →
      ∃ c' : (T.U j σ).Comp → ℂ, CUnit c' ∧
        EquivariantFiniteGroup (T.V j σ) σ ((rdU (T.U j σ)).comp (T.cuspA j a n).subtype) (T.dict j σ)
          (muPin (T.V j σ) (T.dict j σ) (T.mu j σ) c') ρ chi ℓ

end GlobalTheory.IndefiniteRowSideFullHecke.LevelGroupLifts
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.PartialLFunctionCharacter
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Mult IsDedekindDomain NumberField

namespace GlobalTheory.IndefiniteRowSideFullHecke.PartialLFunctionCharacter

variable {D : D7}

def TrivialOnF (χ : (AE D)ˣ →* Circle) : Prop := ∀ a : (AF D.host.F)ˣ, χ (idF D a) = 1

def lPartial (S : Finset (HeightOneSpectrum (𝓞 D.host.F))) (χ : (AE D)ˣ →* Circle) (s : ℂ) : ℂ :=
  ∏' P : {P : HeightOneSpectrum (𝓞 D.host.E) // OffS D S P}, Mi.lfac χ P.1 s

def IsPartialL (S : Finset (HeightOneSpectrum (𝓞 D.host.F))) (χ : (AE D)ˣ →* Circle) (Λ : ℂ → ℂ) : Prop :=
  Differentiable ℂ Λ ∧ ∀ s : ℂ, 1 < s.re →
    HasProd (fun P : {P : HeightOneSpectrum (𝓞 D.host.E) // OffS D S P} => Mi.lfac χ P.1 s) (Λ s)

def IsFiniteL (χ : (AE D)ˣ →* Circle) (Λ : ℂ → ℂ) : Prop :=
  Differentiable ℂ Λ ∧ ∀ s : ℂ, 1 < s.re →
    HasProd (fun P : HeightOneSpectrum (𝓞 D.host.E) => Mi.lfac χ P s) (Λ s)

def PosUpTo (t : ℕ) (Λ : ℂ → ℂ) : Prop := ∀ n : ℕ, 1 ≤ n → n ≤ t → (Λ n).im = 0 ∧ 0 < (Λ n).re

def HeckeRatioPos (D : D7) : Prop :=
  ∀ μ μ' : (AE D)ˣ →* Circle, IsHeckeChar D μ → IsHeckeChar D μ' → TrivialOnF μ → TrivialOnF μ' →
    (∃ (τ : D.what₂.Tau) (e e' : ℚ), HasInfExp D μ τ (-e) ∧ HasInfExp D μ' τ (-e') ∧ e ≠ e') →
    ∀ t : ℕ,
      (∃ Λ : ℂ → ℂ, IsFiniteL (μ * μ'⁻¹) Λ ∧ PosUpTo t Λ) ∧
      ∀ S : Finset (HeightOneSpectrum (𝓞 D.host.F)), ∃ Λ : ℂ → ℂ, IsPartialL S (μ * μ'⁻¹) Λ ∧ PosUpTo t Λ

theorem IsPartialL.eq_lPartial {S : Finset (HeightOneSpectrum (𝓞 D.host.F))} {χ : (AE D)ˣ →* Circle} {Λ : ℂ → ℂ}
    (h : IsPartialL S χ Λ) {s : ℂ} (hs : 1 < s.re) : Λ s = lPartial S χ s := (h.2 s hs).tprod_eq.symm

theorem eq_of_eqOn_re {f g : ℂ → ℂ} (hf : Differentiable ℂ f) (hg : Differentiable ℂ g)
    (h : ∀ s : ℂ, 1 < s.re → f s = g s) : f = g := by
  refine AnalyticOnNhd.eq_of_eventuallyEq (𝕜 := ℂ) (z₀ := 2) (fun z _ => hf.analyticAt z) (fun z _ => hg.analyticAt z) ?_
  have : {s : ℂ | 1 < s.re} ∈ nhds (2 : ℂ) :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by simp)
  exact Filter.mem_of_superset this h

theorem IsPartialL.unique {S : Finset (HeightOneSpectrum (𝓞 D.host.F))} {χ : (AE D)ˣ →* Circle} {Λ Λ' : ℂ → ℂ}
    (h : IsPartialL S χ Λ) (h' : IsPartialL S χ Λ') : Λ = Λ' :=
  eq_of_eqOn_re h.1 h'.1 fun _ hs => (h.eq_lPartial hs).trans (h'.eq_lPartial hs).symm

end GlobalTheory.IndefiniteRowSideFullHecke.PartialLFunctionCharacter

end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.UniformModerateGrowthLevel
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Matrix
open Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links
open scoped TensorProduct ContDiff

namespace GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicParabolicSmoothFunctions

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {W : HSp D} {S : D.what₂.Tau → SPar}

def pMinus (M : DSModel W S) (τ : D.what₂.Tau) : Set (Matrix (Fin W.rank) (Fin W.rank) ℂ) :=
  {Z | ∀ a b, ¬ (M.ε τ a = false ∧ M.ε τ b = true) → (M.fr τ * Z * (M.fr τ)⁻¹) a b = 0}

abbrev KMap (M : DSModel W S) : Type :=
  MultilinearMap (RingHom.id ℂ) (fun τ : D.what₂.Tau => lowT M τ) (GA D W → ℂ)


variable (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))


variable (W) in
def IsSmoothFn (φ : GA D W → ℂ) : Prop :=
  ∀ (k : ℕ) (τs : Fin k → D.what₂.Tau) (Xs : Fin k → Matrix (Fin W.rank) (Fin W.rank) ℂ),
    (∀ i, Xs i ∈ lieAt W (τs i)) → ∀ g,
      ContDiff ℝ ∞ fun t : Fin k → ℝ => φ (g * (List.ofFn fun i => oneP θ W (τs i) (Xs i) (t i)).prod)


variable (W) in
def IsUnifModGrowth (φ : GA D W → ℂ) : Prop :=
  ∃ N : ℕ, ∀ l : List (D.what₂.Tau × Matrix (Fin W.rank) (Fin W.rank) ℂ), (∀ p ∈ l, p.2 ∈ lieAt W p.1) →
    ∀ x, ∃ C : ℝ, ∀ g ∈ GinfC W,
      ‖(l.foldr (fun p f => Rder θ W p.1 p.2 f) φ) (x * g)‖ ≤ C * normInf θ W g ^ N


def RestrictsTo (M : DSModel W S) (T : Formalism.IndefR.Mult.MMap M) (U : KMap M) : Prop :=
  ∀ e : ∀ τ, lowT M τ, T (fun τ => (e τ : M.sm τ)) = U e

theorem single_mem_pMinus (M : DSModel W S) (τ : D.what₂.Tau) {a b : Fin W.rank} (ha : M.ε τ a = false)
    (hb : M.ε τ b = true) : (M.fr τ)⁻¹ * Matrix.single a b (1 : ℂ) * M.fr τ ∈ pMinus M τ := by
  have hu : IsUnit (M.fr τ).det := (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
  have h : M.fr τ * ((M.fr τ)⁻¹ * Matrix.single a b (1 : ℂ) * M.fr τ) * (M.fr τ)⁻¹ = Matrix.single a b 1 := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.one_mul, Matrix.mul_assoc,
      Matrix.mul_nonsing_inv _ hu, Matrix.mul_one]
  intro c d hcd
  rw [h, Matrix.single_apply, ite_eq_right]
  rintro ⟨rfl, rfl⟩
  exact hcd ⟨ha, hb⟩

end GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicParabolicSmoothFunctions

end
end

