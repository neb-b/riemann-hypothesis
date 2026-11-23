module

public import Mathlib
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.LevelLetterCocycles.DataN
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.HeckeSplitOne
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MonodromyZeroOfWeilDeligneRepClassIff

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsobaricDiscreteSelfDualStrongMultiplicityOne
section
noncomputable section

namespace GlobalTheory.RowCopy

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

def RowSize (D : D7) : Prop :=
  ∀ (i : D.nd.Loc) (σ : D.what₂.FT), D.what₂.isot (D.nd.j i) σ ≠ ⊥ →
    ∀ w : PlE D.host, IsSplitPl D.host w → D.naut.unr (D.naut.locW i σ w) →
    ∀ α ∈ D.naut.frobEig (D.naut.locW i σ w),
      ‖α‖ < ((Ideal.absNorm w.asIdeal : ℕ) : ℝ) ^ (((D.R.t : ℝ) - 1) / 2)

def HeckeSplitOne (D : D7) : Prop :=
  ∀ ν ν' : D.naut.CG 1,
    (∀ᶠ w in Filter.cofinite, IsSplitPl D.host w → D.naut.locG ν w = D.naut.locG ν' w) → ν = ν'

def ThetaOne (D : D7) : Prop :=
  ∀ (i : D.nd.Loc) (σ : D.what₂.FT), D.what₂.isot (D.nd.j i) σ ≠ ⊥ → ∃ P, thetaOf D.nd D.naut i σ P

def LamPos (D : D7) (μ : D.what₂.Tup) (j : ℕ) : Prop :=
  ∀ σ : D.what₂.FT,
    (∀ f ∈ D.what₂.isot j σ, D.what₂.thetaP μ j (D.what₂.thetaT μ j f) = ((D.what₂.lamP μ j σ : ℝ) : ℂ) • f) ∧
    (D.what₂.isot j σ ≠ ⊥ → 0 < D.what₂.lamP μ j σ)

def JointOccurrenceCondition (D : D7) : Prop :=
  ∀ (σ : D.what₂.FT) (k : Fin 2) (v : D.nd.PlG k), D.ntypes.cuspidal σ →
    Formalism.MainNotions.N.TameGen D.nd (D.nd.plOm.1 (D.naut.plGw k v)) (D.ntypes.tg k v) →
    ∀ i : D.nd.Loc, D.nd.l i ≠ D.host.g k → D.what₂.isot (D.nd.j i) σ ≠ ⊥ → D.nd.goodRow σ →
      haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
      haveI : Fact (D.what₂.places.resChar (D.nd.w i)).Prime := ⟨D.what₂.places.resChar_prime (D.nd.w i)⟩
      Matrix.charpoly ((D.ntypes.rbar σ (D.nd.w i) (D.ntypes.tg k v) : GL (Fin D.R.r) _) :
          Matrix (Fin D.R.r) (Fin D.R.r) _) =
        ((Formalism.CyclotomicNorms.rootsBar (D.nd.lab k σ v)).map fun x =>
          X - C (D.ntypes.iota k v (D.nd.w i) (Formalism.CyclotomicNorms.primeToPart (D.what₂.places.resChar (D.nd.w i)) x))).prod ∧
      ∃ φ : G D.host.E D.nd.Om,
        D.ntypes.rbar σ (D.nd.w i) (φ * D.ntypes.tg k v * φ⁻¹) = D.ntypes.rbar σ (D.nd.w i) (D.ntypes.tg k v) ^ D.host.g k

def RbarTie (D : D7) : Prop :=
  (∀ (σ : D.what₂.FT) (lam : D.what₂.places.Pl), (∃ a : D.nd.Loc, D.nd.w a = lam) →
    Formalism.MainNotions.N.IsSSRep (D.ntypes.rbar σ lam)) ∧
  ∀ (i : D.nd.Loc) (σ : D.what₂.FT), D.what₂.isot (D.nd.j i) σ ≠ ⊥ → D.nd.goodRow σ →
    ∀ (Sig : List (Part D.naut.CG)) (ρ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin D.R.r) (D.nd.O i)),
      Formalism.MainNotions.N.HasParamW D.nd D.naut i σ Sig → Formalism.MainNotions.N.IsRepOfSig D.nd D.naut i Sig ρ →
      ∀ g, (((D.ntypes.rbar σ (D.nd.w i) g : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) _).charpoly).map
          (Formalism.MainNotions.N.fbCast (D.nd.w_l i) (D.what₂.places.resChar_prime (D.nd.w i)) (D.nd.lPrime i).out).toRingHom =
        ((ρ g : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O i)).charpoly.map
          ((D.naut.kFbar i).comp (IsLocalRing.residue (D.nd.O i)))

def TempCSD (D : D7) : Prop :=
  ∀ (a : ℕ) (π : D.naut.CG a), 1 ≤ a → D.naut.csd π → D.naut.ralg π → ∀ w, D.naut.tempered (D.naut.locG π w)

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)

def ParUpRec (i : N.Loc) : Prop :=
  ∀ x ∈ ZgoodN N A i, ∀ Sig, HasParamX N A i x Sig →
    (MjSig N A i Sig).map (what₂.thetaT (N.mu i) (N.j i)) ≤ eigC N A i x

def DownMemRec (i : N.Loc) : Prop :=
  ∀ x ∈ ZgoodN N A i, ∀ Sig, HasParamX N A i x Sig →
    (eigC N A i x).map (what₂.thetaP (N.mu i) (N.j i)) ≤ MjSig N A i Sig

def TypeNZRec (i : N.Loc) : Prop :=
  ∀ x ∈ ZgoodN N A i, ∀ F ∈ eigC N A i x, what₂.thetaP (N.mu i) (N.j i) F = 0 → F = 0

def GoodPartRec (i : N.Loc) : Prop :=
  goodPartM N A i = ⨆ x ∈ ZgoodN N A i, ⨆ Sig ∈ {Sig | HasParamX N A i x Sig}, MjSig N A i Sig

def TieLab : Prop :=
  (∀ (k : Fin 2) (v : N.PlG k) (a : A.LP (A.plGw k v)) (s : ℝ),
    A.items₂ k (A.plGw k v) (A.lpTw a s) = A.items₂ k (A.plGw k v) a) ∧
  ∀ (k : Fin 2) (v : N.PlG k) (a : A.LP (A.plGw k v)), (A.items₂ k (A.plGw k v) a).natDegree ≤ A.lpDim a

def IsobaricCuspidalStrongMultiplicityOne : Prop :=
  ∀ Pa Pa' : List (Part A.CG), (∀ p ∈ Pa, 1 ≤ p.a ∧ p.d = 1) → (∀ p ∈ Pa', 1 ≤ p.a ∧ p.d = 1) →
    (∀ᶠ w in Filter.cofinite, isoLoc N A Pa w = isoLoc N A Pa' w) → Pa.Perm Pa'

def IsobaricDiscreteSelfDualStrongMultiplicityOne : Prop :=
  ∀ Pa Pa' : List (Part A.CG), (∀ p ∈ Pa, 1 ≤ p.a ∧ 1 ≤ p.d ∧ A.csd p.π) →
    (∀ p ∈ Pa', 1 ≤ p.a ∧ 1 ≤ p.d ∧ A.csd p.π) →
    (∀ᶠ w in Filter.cofinite, isoLoc N A Pa w = isoLoc N A Pa' w) → Pa.Perm Pa'

end GlobalTheory.RowCopy
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RankOneUnitary
section
noncomputable section

namespace GlobalTheory.RowTie

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain
open GlobalTheory.WeilDeligne GlobalTheory.ThetaExh

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)

structure WDTie where

  e : ∀ w : PlE H, A.LP w ≃ WD (E := H.E) (A := N.plOm.1 w) (w := w) (N.plOm.2 w)
  dim : ∀ w (a : A.LP w), (e w a).lpDim = A.lpDim a
  zero : ∀ w, e w (A.lpZero w) = WD.lpZero (N.plOm.2 w)
  sum : ∀ w (a b : A.LP w), e w (A.lpSum a b) = (e w a).lpSum (e w b)
  tw : ∀ w (a : A.LP w) (s : ℝ), e w (A.lpTw a s) = (e w a).lpTw s
  char : ∀ w (a χ : A.LP w), A.lpDim χ = 1 → e w (A.lpChar a χ) = (e w a).lpChar (e w χ)
  mono0 : ∀ w (a : A.LP w), A.mono0 a ↔ (e w a).mono0
  unr : ∀ w (a : A.LP w), A.unr a ↔ (e w a).unr
  frobEig : ∀ w (a : A.LP w), A.unr a → A.frobEig a = (e w a).frobEig
  tempered : ∀ w (a : A.LP w), A.tempered a ↔ (e w a).tempered
  inePol : ∀ w (a : A.LP w), ∀ σ ∈ Ine (F := H.E) (N.plOm.1 w), A.inePol a σ = (e w a).inePol σ

def WDTie.eig {N : NData R H what₂} {A : NAut N} (T : WDTie N A) (w : PlE H) (a : A.LP w) (σ : G H.E N.Om) :
    Multiset ℂ := ((T.e w a).inePol σ).roots

def CharLaws : Prop := ∀ (w : PlE H) (a b χ χ' : A.LP w) (s : ℝ), A.lpDim χ = 1 → A.lpDim χ' = 1 →
  A.lpChar (A.lpSum a b) χ = A.lpSum (A.lpChar a χ) (A.lpChar b χ) ∧
  A.lpChar (A.lpTw a s) χ = A.lpTw (A.lpChar a χ) s ∧
  A.lpChar a (A.lpTw χ s) = A.lpTw (A.lpChar a χ) s ∧
  A.lpChar (A.lpChar a χ) χ' = A.lpChar a (A.lpChar χ χ') ∧
  A.lpChar a (A.lpUnr w {1}) = a

def Cancel : Prop := ∀ (w : PlE H) (a b c : A.LP w), A.lpSum a c = A.lpSum b c → a = b

def PairLift (i : N.Loc) : Prop := ∀ σ P, Pairs N A i σ P → ∀ w, IsSplitPl H w →
  A.locV i P w = liftPar N A i w (A.locW i σ w)

def BCEx (i : N.Loc) : Prop := ∀ P : A.AV i, ∃ Pa, IsBCV N A i P Pa

def ChebSplit : Prop := ∀ S : Finset (PlE H), Dense {σ : G H.E N.Om | ∃ w : PlE H, w ∉ S ∧ IsSplitPl H w ∧
  ∃ B : ValuationSubring N.Om, IsPlaceOver (F := H.E) B w ∧ IsFrob (F := H.E) B (normV w) σ}

def SplitBC (i : N.Loc) : Prop := ∀ P P' : A.AV i,
  (∀ᶠ w in Filter.cofinite, IsSplitPl H w → A.locV i P w = A.locV i P' w) →
  ∀ Pa Pa', IsBCV N A i P Pa → IsBCV N A i P' Pa' → Pa.Perm Pa'

def RepOfLoc (i : N.Loc) : Prop := ∀ P P' : A.AV i,
  (∀ w, IsSplitPl H w → A.locV i P w = A.locV i P' w) →
  (∀ w, ¬ IsSplitPl H w → ubc R.nV (A.satV i P w) = ubc R.nV (A.satV i P' w)) → P = P'

def twSum (L : List ((Σ a : ℕ, A.CG a) × ℝ)) (w : PlE H) : A.LP w :=
  L.foldr (fun p acc => A.lpSum (A.lpTw (A.locG p.1.2 w) p.2) acc) (A.lpZero w)

def IsobaricRigid : Prop := ∀ L L' : List ((Σ a : ℕ, A.CG a) × ℝ), (∀ p ∈ L, 1 ≤ p.1.1) → (∀ p ∈ L', 1 ≤ p.1.1) →
  (∀ᶠ w in Filter.cofinite, twSum N A L w = twSum N A L' w) → L.Perm L'

def RankOneUnitary {N : NData R H what₂} {A : NAut N} (T : WDTie N A) : Prop :=
  ∀ (π : A.CG 1) (w : PlE H) (σ : G H.E N.Om), IsFrob (F := H.E) (N.plOm.1 w) (normV w) σ →
    ∀ α ∈ T.eig w (A.locG π w) σ, ‖α‖ = 1

def IotaRed (D : D7) : Prop := ∀ i : D.nd.Loc,
  haveI : Fact (D.what₂.places.resChar (D.nd.w i)).Prime := ⟨D.what₂.places.resChar_prime (D.nd.w i)⟩
  ∃ (B : ValuationSubring ℂ) (κ : IsLocalRing.ResidueField B ≃+* Formalism.CyclotomicNorms.Fbar (D.what₂.places.resChar (D.nd.w i))),
    (∀ y : D.nd.O i, ∃ h : iotaO D.nd D.naut i y ∈ B,
      fbCast (D.nd.w_l i) (D.what₂.places.resChar_prime (D.nd.w i)) (D.nd.lPrime i).out
        (κ (IsLocalRing.residue B ⟨_, h⟩)) = D.naut.kFbar i (IsLocalRing.residue (D.nd.O i) y)) ∧
    ∀ k v x, ∃ h : D.ntypes.teichC k x ∈ B, D.ntypes.iota k v (D.nd.w i) x = κ (IsLocalRing.residue B ⟨_, h⟩)

end GlobalTheory.RowTie
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.GaloisGeometry.SplitRep
section
noncomputable section

namespace GlobalTheory.SplitCoef

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual

def SplitRep {k Γ : Type} [Field k] [Group Γ] {a : ℕ} (ρ : Γ →* GL (Fin a) k) : Prop :=
  ∀ W, IsIrrSub ρ W → AbsIrrSub ρ W

def OSplitAt (D : D7) (i : D.nd.Loc) : Prop :=
  ∀ (x : D.nd.X i) (r : GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)), IsHeckeGalois D.nd i x r →
    SplitRep (mapRep (algebraMap (D.nd.O i) (Kf D.nd i)) r)

def OSplit (D : D7) : Prop := ∀ i, OSplitAt D i

end GlobalTheory.SplitCoef

end
end

