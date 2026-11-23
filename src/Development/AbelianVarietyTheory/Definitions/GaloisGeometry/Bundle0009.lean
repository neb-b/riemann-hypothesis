module

public import Mathlib
public import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.Bundle0004
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0007
public import Formalism.SharpRestriction.LevelLetterCocycles.RamifiedCoefficientChains
public import Formalism.SharpRestriction.LevelLetterCocycles.DecompositionData
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NotDvdCondN

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Definitions.GaloisGeometry.HeckeCharEqOfLAdicRealisation
section
noncomputable section

namespace GlobalTheory.StringRepresentationDecomposition

open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions.N Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal

def epsQ (D : D7) (i : D.nd.Loc) (g : G D.host.E D.nd.Om) : Qbar (D.nd.l i) :=
  iotaOQ D.nd D.naut i ((Formalism.MainNotions.N.Glob.epsO D.nd i g : (D.nd.O i)ˣ) : D.nd.O i)

def IsStringRep (D : D7) (i : D.nd.Loc) (p : Part D.naut.CG)
    (R : G D.host.E D.nd.Om →* GL (Fin p.a) (Qbar (D.nd.l i))) : Prop :=
  Continuous (fun g => ((R g : GL _ _) : Matrix (Fin p.a) (Fin p.a) (Qbar (D.nd.l i)))) ∧ IsSSRep R ∧
    ∀ w, w ∉ placesOver D.host.E (D.nd.l i) →
      D.naut.wdOf i R w = D.naut.lpTw (D.naut.locG p.π w) (((p.d : ℝ) - 1) / 2 + (1 - (D.R.nV : ℝ)) / 2)

def SSList : Prop :=
  ∀ (k : Type) [Field k] (Γ : Type) [Group Γ] (n : ℕ) (ρ : Γ →* GL (Fin n) k),
    ∃ L : List (Σ m : ℕ, Γ →* GL (Fin m) k), (∀ p ∈ L, 1 ≤ p.1 ∧ IsIrrSub p.2 ⊤) ∧
      ∀ g, ((ρ g : GL _ _) : Matrix (Fin n) (Fin n) k).charpoly =
        (L.map fun p => ((p.2 g : GL _ _) : Matrix (Fin p.1) (Fin p.1) k).charpoly).prod

def SSRankUnique : Prop :=
  ∀ (k : Type) [Field k] (Γ : Type) [Group Γ] (L L' : List (Σ m : ℕ, Γ →* GL (Fin m) k)),
    (∀ p ∈ L, 1 ≤ p.1 ∧ AbsIrrSub p.2 ⊤) → (∀ p ∈ L', 1 ≤ p.1 ∧ AbsIrrSub p.2 ⊤) →
    (∀ g, (L.map fun p => ((p.2 g : GL _ _) : Matrix (Fin p.1) (Fin p.1) k).charpoly).prod =
      (L'.map fun p => ((p.2 g : GL _ _) : Matrix (Fin p.1) (Fin p.1) k).charpoly).prod) →
    ((L.map fun p => p.1 : List ℕ) : Multiset ℕ) = ((L'.map fun p => p.1 : List ℕ) : Multiset ℕ)

def EigenCharTwist : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (Γ : Type) [Group Γ] (n : ℕ) (ρ : Γ →* GL (Fin n) K)
    (L : List (Σ m : ℕ, Γ →* GL (Fin m) K)) (χ : Γ →* Kˣ),
    IsSSRep ρ → (∀ p ∈ L, IsSSRep p.2) →
    (∀ g, ((ρ g : GL _ _) : Matrix (Fin n) (Fin n) K).charpoly =
      (L.map fun p => ((p.2 g : GL _ _) : Matrix (Fin p.1) (Fin p.1) K).charpoly).prod) →
    (∃ v : Fin n → K, v ≠ 0 ∧ ∀ g, ((ρ g : GL _ _) : Matrix (Fin n) (Fin n) K).mulVec v = ((χ g : Kˣ) : K) • v) →
    ∃ p ∈ L, ∃ v : Fin p.1 → K, v ≠ 0 ∧
      ∀ g, ((p.2 g : GL _ _) : Matrix (Fin p.1) (Fin p.1) K).mulVec v = ((χ g : Kˣ) : K) • v

def ValRingModel : Prop :=
  ∀ (l : ℕ) [Fact l.Prime],
    ∃ (A : Type) (_ : CommRing A) (_ : IsLocalRing A) (_ : IsAlgClosed (IsLocalRing.ResidueField A))
      (j : A →+* Qbar l), Function.Injective j ∧ Set.range j = {x : Qbar l | ‖x‖ ≤ 1} ∧
      (∀ x : A, x ∈ IsLocalRing.maximalIdeal A ↔ ‖j x‖ < 1) ∧
      ∀ (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ]
        (n : ℕ) (ρ : Γ →* GL (Fin n) (Qbar l)),
        Continuous (fun g => ((ρ g : GL _ _) : Matrix (Fin n) (Fin n) (Qbar l))) →
        ∃ (ρ0 : Γ →* GL (Fin n) A) (P : GL (Fin n) (Qbar l)), ∀ g,
          ((ρ g : GL _ _) : Matrix (Fin n) (Fin n) (Qbar l)) =
            (P : Matrix (Fin n) (Fin n) (Qbar l)) * ((ρ0 g : GL _ _) : Matrix (Fin n) (Fin n) A).map j *
              ((P⁻¹ : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l))

def RbEx (D : D7) : Prop := ∀ i : D.nd.Loc, HG D.nd D.naut i → ∃ rb, IsRhoBar D.nd i rb

def Numerics : Prop :=
  ∀ (r t d n a : ℕ) (A : Multiset ℕ), 1 < r → 2 ≤ t → a < d → (d : ℤ) - 1 - 2 * a = (t : ℤ) - 1 → A.sum = n → (∀ x ∈ A, 1 ≤ x) →
    1 ≤ n → d • A ≤ r ::ₘ Multiset.replicate t 1 → n = 1 ∧ d = t

def Rest : Prop :=
  ∀ (ι : Type) [Fintype ι] (d : ι → ℕ) (A : ι → Multiset ℕ) (r : ℕ), (∀ k, 1 ≤ d k) → (∀ k, A k ≠ 0) →
    ∑ k, d k • A k = {r} → Fintype.card ι = 1 ∧ ∀ k, d k = 1 ∧ A k = {r}

def EigPd (D : D7) : Prop :=
  ∀ i : D.nd.Loc, HG D.nd D.naut i → ∀ w ∈ D.nd.S i,
      w ∈ placesOver D.host.E (if D.nd.l i = D.host.pde then D.host.pde' else D.host.pde) →
      ∀ rb, IsRhoBar D.nd i rb →
      ¬ (((rb (D.nd.gam0 i w) : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) _).charpoly).IsRoot
        (IsLocalRing.residue (D.nd.O i) (chi1 D.nd i (D.nd.gam0 i w)))

def HOneTwo (D : D7) : Prop :=
  ∀ (i : D.nd.Loc) (rb : G D.host.E D.nd.Om →* GL (Fin D.R.r) (IsLocalRing.ResidueField (D.nd.O i))) (w : PlE D.host),
    w ∈ D.nd.S i → IsRhoBar D.nd i rb →
    ¬ (((rb (D.nd.gam0 i w) : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) _).charpoly).IsRoot
      (IsLocalRing.residue (D.nd.O i) (chi1 D.nd i (D.nd.gam0 i w))) →
    ∀ e : ℤ, Formalism.MainNotions.SumRepresentations.At.HOneTwoZero D.nd i w
      (Formalism.MainNotions.N.twistRep (Formalism.MainNotions.N.glRep rb) (Formalism.MainNotions.SumRepresentations.At.chiEpsBar D.nd i e))

end GlobalTheory.StringRepresentationDecomposition

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThickLetterWordLatticeSurjectionHypotheses
section
noncomputable section

namespace GlobalTheory.HTW.RecS

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.HTW.Rec

variable {D : D7} (L : SizeData₂ D) (HW : HWOf D.loc) (i : D.nd.Loc)
  (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)
  (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
  (Cx : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (hG : Good (D.nbr i w hw).Kw 1 Cx.LL)

abbrev nLet : ℕ := Module.finrank ℚ_[D.nd.l i] ↥(K0 (D.nbr i w hw).Kw)

abbrev WW : Wach (D.loc (D.nd.l i)) (D.nbr i w hw).Kw Cx.LL := (HW (D.nd.l i)).W (D.nbr i w hw).Kw 1 Cx.LL hG

def IsSubOfTwistedDualSums (T : Lat (D.nbr i w hw).Kw Cx.LL) : Prop :=
  IsSubOfSums T.ρ fun x : D.nd.X i => ⇑(TruncatedSeriesCountingIdentities.locC Cx (rDuO D.nd i r x))

def IsTwistedDualOfGaloisRep (T : Lat (D.nbr i w hw).Kw Cx.LL) : Prop := IsMatRep T (TruncatedSeriesCountingIdentities.locC Cx (T2O D.nd i ρ π))

variable (Wd : NWord (nLet i w hw))

structure WordBase : Prop where
  unram : (D.nbr i w hw).Kw.1 ≤ MaximalUnramifiedExtension (D.nd.l i)
  deg : Br.DegW D.nbr i w hw
  split : ∀ _ft : Fintype (↥(D.nbr i w hw).Kw.1 →ₐ[ℚ_[D.nd.l i]] ↥Cx.LL.1),
    Splits (Qp := ℚ_[D.nd.l i]) (K := ↥(D.nbr i w hw).Kw.1) ↥Cx.LL.1
  t1 : ∀ T₁, IsSubOfTwistedDualSums i r w hw Cx T₁ → IsCrys ((D.loc (D.nd.l i)).PD (D.nbr i w hw).Kw) T₁.ρ ∧
    (∀ a, TruncatedSeriesCountingBounds.JumpsAt (WW HW i w hw Cx hG) T₁ a (Wd.win a)) ∧ LiftingTheory.JumpsLet (WW HW i w hw Cx hG) T₁ Wd.Mi Wd.hi
  t2 : ∀ T₂, IsTwistedDualOfGaloisRep i ρ π w hw Cx T₂ → IsCrys ((D.loc (D.nd.l i)).PD (D.nbr i w hw).Kw) T₂.ρ ∧
    ∀ (_ft : Fintype (↥(D.nbr i w hw).Kw.1 →ₐ[ℚ_[D.nd.l i]] ↥Cx.LL.1)) (a),
      TruncatedSeriesCountingBounds.lowCount (WW HW i w hw Cx hG) T₂ a Wd.η ≤ (Wd.m : ℤ)
  t2win : ∀ T₂, IsTwistedDualOfGaloisRep i ρ π w hw Cx T₂ →
    (∀ a, TruncatedSeriesCountingBounds.JumpsAt (WW HW i w hw Cx hG) T₂ a (Wd.win a)) ∧ LiftingTheory.JumpsLet (WW HW i w hw Cx hG) T₂ Wd.Mi Wd.hi
  num : WordNum L Wd
  small : Small Wd ∧ 1 ≤ Wd.S ∧ 1 ≤ Wd.η

def ThickLetterWordLatticeSurjectionHypotheses : Prop :=
  ∀ (_ft : Fintype (↥(D.nbr i w hw).Kw.1 →ₐ[ℚ_[D.nd.l i]] ↥Cx.LL.1)) T₁ T₂ (F : LatHom T₁.L T₂.L),
    IsSubOfTwistedDualSums i r w hw Cx T₁ → IsTwistedDualOfGaloisRep i ρ π w hw Cx T₂ → F.Onto →
      TruncatedSeriesCountingBounds.HidaSetting ((D.loc (D.nd.l i)).PD (D.nbr i w hw).Kw) (WW HW i w hw Cx hG) T₁ T₂ F
        Wd.b Wd.w Wd.S Wd.η Wd.m Wd.up Wd.sz Wd.Mi Wd.hi

def AlternatingWordLatticeSurjectionHypotheses (d : ℕ) : Prop :=
  ∀ (_nz : NeZero (nLet i w hw)) T₁ T₂ (F : LatHom T₁.L T₂.L),
    IsSubOfTwistedDualSums i r w hw Cx T₁ → IsTwistedDualOfGaloisRep i ρ π w hw Cx T₂ → F.Onto →
      RamifiedCoefficientChains.SetCS (WW HW i w hw Cx hG) d T₁ T₂ F Wd.sz Wd.S Wd.η Wd.m

structure PtIn : Prop where
  good : GoodR D.nd i r
  cont : TruncatedSeriesCountingIdentities.FamilyContinuous i r
  mem : π ∈ D.nd.Z i
  dec : TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π
  contρ : Continuous fun g => rhoO D.nd i ρ π g
  crys : ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) x,
    IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (rTwO D.nd i r x)))

def JointB (C₂ : ℝ) : Prop :=
  ∀ i, InertUnr D (D.nd.l i) → IsRowB L (D.nd.l i) → ∀ r ρ π, PtIn i r ρ π → ∀ w hw,
    (D.nbr i w hw).Kw.1 ≤ MaximalUnramifiedExtension (D.nd.l i) ∧
    ∀ (Cx : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (hG : Good (D.nbr i w hw).Kw 1 Cx.LL), ∃ Wd : NWord (nLet i w hw),
      WordBase L HW i r ρ π w hw Cx hG Wd ∧ ThickLetterWordLatticeSurjectionHypotheses HW i r ρ π w hw Cx hG Wd ∧ 11 ≤ D.nd.l i ∧
      jA L (D.nd.l i) + 1 ≤ nLet i w hw ∧
      C₂ * ((jA L (D.nd.l i) : ℝ) + 1) * (((Wd.w + Wd.S + Wd.η : ℕ) : ℝ) + 1) ≤ (Wd.b : ℝ) ∧
      TruncatedSeriesCountingBounds.Clusters (jA L (D.nd.l i)) (TruncatedSeriesCountingBounds.Thick Wd.b Wd.η Wd.sz)

def JointCD : Prop :=
  ∀ i, InertUnr D (D.nd.l i) → ∀ r ρ π, PtIn i r ρ π → ∀ w hw,
    (D.nbr i w hw).Kw.1 ≤ MaximalUnramifiedExtension (D.nd.l i) ∧
    ∀ (Cx : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (hG : Good (D.nbr i w hw).Kw 1 Cx.LL), ∃ Wd : NWord (nLet i w hw),
      WordBase L HW i r ρ π w hw Cx hG Wd ∧ ThickLetterWordLatticeSurjectionHypotheses HW i r ρ π w hw Cx hG Wd ∧ 11 ≤ D.nd.l i ∧ WordBox L Wd ∧
      (WordsNT Wd ∨ ∃ d, WordsAT (D.nd.l i) Wd d ∧ AlternatingWordLatticeSurjectionHypotheses HW i r ρ π w hw Cx hG Wd d)

end GlobalTheory.HTW.RecS
end
end

