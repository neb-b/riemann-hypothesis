module

public import Mathlib
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.LevelLetterCocycles.ExistsIdealDenominator
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0018
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0004
public import Formalism.LocalRingCardinality.DataForced
public import Formalism.SharpRestriction.Divisibility.CartierLocalBounds
public import Formalism.SharpRestriction.Divisibility.LiftErrorLocal
public import Formalism.LocalRingCardinality.Bundle0003

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions
open scoped TensorProduct

namespace Formalism.MainNotions.PDVN

variable (D : Formalism.BasicNotions.D7)

def QOk (i : D.ntw.Tw) (Q : Finset (HeightOneSpectrum (𝓞 D.host.E))) : Prop :=
  Formalism.MainNotions.BlochKatoReduction.Gen.QOk D.ntw i Q

def SOk (i : D.ntw.Tw) (lam : D.ntw.abelian₂ i) (s : ℤ) : Prop :=
  Formalism.MainNotions.BlochKatoReduction.Gen.SOk D.ntw i lam s

def IntAfter (i : D.ntw.Tw) (n : ℕ) (x : FractionRing (D.ntw.O i)) : Prop :=
  ∃ y : D.ntw.O i, algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i)) y =
    ((D.ntw.l i : ℕ) : FractionRing (D.ntw.O i)) ^ n * x

structure Loc where

  cE : ∀ i, D.ntw.abelian₂ i → ℕ

  kap : ∀ i, D.ntw.abelian₂ i → ℕ

  ffP : Finset ℕ

  a0 : ℕ → ℕ
  a0_mem_one_two : ∀ p ∈ ffP, a0 p = 1 ∨ a0 p = 2

  g_mem : ∀ k, D.host.g k ∈ ffP
  pde_mem : D.host.pde ∈ ffP ∧ D.host.pde' ∈ ffP

variable {D} in
def Loc.wt (X : Loc D) (i : D.ntw.Tw) (lam : D.ntw.abelian₂ i) : ℝ :=
  (X.kap i lam : ℝ) + (D.ntw.s2 i lam : ℝ) * (D.R.f : ℝ)

def ThetaDenominatorValues (X : Loc D) (C : ℝ) : Prop :=
  ∃ n : ∀ i, D.ntw.abelian₂ i → ℕ,
    (∀ i (lam : D.ntw.abelian₂ i) (s : ℤ), D.ntw.NonzeroIndexPlace i → SOk D i lam s → D.ntw.l i ≠ 2 →
      (∀ P ∈ placesOver D.host.E (D.ntw.l i), P.asIdeal.ramificationIdx ℤ = 1) →
      D.ntw.l i ∉ X.ffP → n i lam = 0) ∧
    (∀ i (lam : D.ntw.abelian₂ i) (s : ℤ), D.ntw.NonzeroIndexPlace i → SOk D i lam s → D.ntw.l i ∣ D.host.condN →
      (n i lam : ℝ) ≤ X.wt i lam * (2 + C * Formalism.MainNotions.ExistsIdealDenominator.vdd D (D.ntw.l i))) ∧
    (∀ i (lam : D.ntw.abelian₂ i) (s : ℤ), D.ntw.NonzeroIndexPlace i → SOk D i lam s → D.ntw.l i ∈ X.ffP → (n i lam : ℝ) ≤ C * (X.a0 (D.ntw.l i) : ℝ) * X.wt i lam) ∧
    ∀ i, D.ntw.NonzeroIndexPlace i → ∀ (Q : Finset (HeightOneSpectrum (𝓞 D.host.E))), QOk D i Q →
      ∀ (lam : D.ntw.abelian₂ i) (s : ℤ), SOk D i lam s → ∀ δ, IntAfter D i (X.cE i lam + n i lam) (D.ntw.th i Q lam δ)



def oW (l : ℕ) [Fact l.Prime] (E : Type) [Field E] [NumberField E] (Λ : Type) [AddCommGroup Λ]
    [Module (𝓞 E) Λ] (a : 𝓞 E) : (ℂ_[l] ⊗[ℤ] Λ) →ₗ[ℂ_[l]] (ℂ_[l] ⊗[ℤ] Λ) :=
  LinearMap.baseChange ℂ_[l] (DistribSMul.toAddMonoidHom Λ a).toIntLinearMap

structure PtTie {l : ℕ} [Fact l.Prime] (E : Type) [Field E] [NumberField E] {Λ σ : Type} [AddCommGroup Λ]
    [Module (𝓞 E) Λ] (Y : Formalism.MainNotions.ExistsIdealDenominator.PtGeo l Λ σ) {Bx Ex : Type} (lx : σ → Bx) (le : σ → Ex)
    (slx : Bx → (𝓞 E →+* ℂ_[l])) where

  HA : Type
  [acgHA : AddCommGroup HA]
  [modHA : Module ℂ_[l] HA]
  LA : Type
  [acgLA : AddCommGroup LA]
  [modLA : Module ℂ_[l] LA]
  pr : HA →ₗ[ℂ_[l]] LA
  pr_surj : Function.Surjective pr

  oH : 𝓞 E →+* Module.End ℂ_[l] HA
  oL : 𝓞 E →+* Module.End ℂ_[l] LA
  pr_o : ∀ a h, pr (oH a h) = oL a (pr h)

  bx : Module.Basis Bx ℂ_[l] LA
  bx_eig : ∀ a x, oL a (bx x) = slx x a • bx x

  sle : Ex → (𝓞 E →+* ℂ_[l])
  be : Module.Basis Ex ℂ_[l] (ℂ_[l] ⊗[ℤ] Λ)
  be_eig : ∀ a e, oW l E Λ a (be e) = sle e a • be e

  th : 𝓞 E →+* 𝓞 E
  mu : HA →ₗ[ℂ_[l]] (ℂ_[l] ⊗[ℤ] Λ) →ₗ[ℂ_[l]] Y.H
  mu_bal : ∀ a h w, mu (oH a h) w = mu h (oW l E Λ (th a) w)

  fil : Y.Fil = Submodule.span ℂ_[l] {v | ∃ h w, pr h = 0 ∧ v = mu h w}

  letters : ∀ sA : LA →ₗ[ℂ_[l]] HA, pr ∘ₗ sA = LinearMap.id → ∃ b : Module.Basis σ ℂ_[l] (Y.H ⧸ Y.Fil),
    ∀ u, b u = Y.Fil.mkQ (mu (sA (bx (lx u))) (be (le u)))

  all_pairs : ∀ x e, slx x = (sle e).comp th → ∃ u, lx u = x ∧ le u = e

  EL_eq : Y.EL = {L | ∃ sA : LA →ₗ[ℂ_[l]] HA, pr ∘ₗ sA = LinearMap.id ∧ (∀ a, sA ∘ₗ oL a = oH a ∘ₗ sA) ∧
    ∀ u, L u = mu (sA (bx (lx u))) (be (le u))}

attribute [instance] PtTie.acgHA PtTie.modHA PtTie.acgLA PtTie.modLA









def AO (i : D.ntw.Tw) (j : ℕ) (b : Bool) : Module.End (D.ntw.O i) (D.nexp.Fm i j b) :=
  Formalism.MainNotions.IntegralHeckeForms.AO D.nexp i j b

def V0 (i : D.ntw.Tw) (j : ℕ) (b : Bool) : Submodule (FractionRing (D.ntw.O i)) (D.nexp.Fm i j b) :=
  Formalism.MainNotions.IntegralHeckeForms.V0 D.nexp i j b

def M0 (i : D.ntw.Tw) (j : ℕ) (b : Bool) : Submodule (D.ntw.O i) (D.nexp.Fm i j b) :=
  Formalism.MainNotions.IntegralHeckeForms.Mall D.nexp i j b

def Mj (i : D.ntw.Tw) (j : ℕ) (b : Bool) : Submodule (D.ntw.O i) (D.nexp.Fm i j b) :=
  M0 D i j b ⊓ (V0 D i j b).restrictScalars (D.ntw.O i)

def ConjugationNormInvariance : Prop :=
  (∀ (i : D.ntw.Tw) (b : Bool), ∃ c : MonoidAlgebra (D.ntw.O i) (G0g D.nd),
    MonoidAlgebra.map (algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i))).toAddMonoidHom c =
      ((D.what₂.restRowsFiniteGroupCard : ℕ) : FractionRing (D.ntw.O i)) • D.nexp.eAlg i b) ∧
  ∀ (i : D.ntw.Tw), ∀ j ∈ Finset.Icc 1 D.R.m, ∀ b : Bool, (M0 D i j b).map (AO D i j b) ≤ Mj D i j b





def wJ (j : ℕ) : ℝ := ∑ ρ : D.what₂.Tau, DV.wSz D j ρ

def wMax : ℝ := (SizeData₂.lifts D).fold max 0 (wJ D)

def onBoundJ (L : SizeData₂ D) (C : ℝ) : ℝ :=
  C * (L.sc.L * Real.log (D.R.k : ℝ) * (D.R.m : ℝ) * wMax D +
    (D.R.f : ℝ) * (D.R.m : ℝ) * L.sc.b * Real.log L.sc.x)



structure ThetaDenominatorData where

  dat : ∀ i j b, Set (D.nexp.Dat i j b)

def OffG (w : D.what₂.places.Pl) : Prop := ∀ i0 : Fin 2, ¬ LiftErrorLocal.Over D i0 w

def GGAt (CH : NChoice D) (w : D.what₂.places.Pl) : Prop := ∀ j ∈ LiftErrorLocal.lifts D, ∀ b : Bool,
  ∀ B1 B2 : Submodule (D.ntw.O (CH.twI w)) (D.nexp.Fm (CH.twI w) j b),
    B1.FG → B2 ≤ B1 → LiftErrorLocal.spK B2 = LiftErrorLocal.spK B1 → LiftErrorLocal.GStab B1 → LiftErrorLocal.GStab B2 →
    LiftErrorLocal.delq D * LiftErrorLocal.lenQ (D.ntw.l (CH.twI w)) (LiftErrorLocal.psiPart B1) (LiftErrorLocal.psiPart B2) ≤
      LiftErrorLocal.lenQ (D.ntw.l (CH.twI w)) B1 B2 + (LiftErrorLocal.rkK B1 : ℝ) * LiftErrorLocal.vU D (CH.twI w)

def SHAt (CH : NChoice D) (w : D.what₂.places.Pl) : Prop := ∀ j ∈ LiftErrorLocal.lifts D, ∀ b : Bool,
  (LiftErrorLocal.rkK (D.nexp.Bsup (CH.twI w) j b) : ℝ) / LiftErrorLocal.delq D ≤
                 2 * (Module.finrank (FractionRing (D.ntw.O (CH.twI w))) (IntegralHeckeForms.Fm0 D.nexp (CH.twI w) j b) : ℝ) ∧
    Module.finrank (FractionRing (D.ntw.O (CH.twI w))) (IntegralHeckeForms.V0 D.nexp (CH.twI w) j b) = D.what₂.D0 ∧
    (Module.finrank (FractionRing (D.ntw.O (CH.twI w))) (IntegralHeckeForms.Fm0 D.nexp (CH.twI w) j b) : ℝ) ≤ 2 * D.what₂.D0 ∧
    (D.nexp.Bsup (CH.twI w) j b).map (IntegralHeckeForms.AO D.nexp (CH.twI w) j b) ≤ D.nexp.Bsup (CH.twI w) j b

def SHbAt (CH : NChoice D) (w : D.what₂.places.Pl) : Prop := ∀ j ∈ LiftErrorLocal.lifts D, ∀ b : Bool,
  LiftErrorLocal.rkK (IntegralHeckeForms.Mall D.nexp (CH.twI w) j b) =
                 Module.finrank (FractionRing (D.ntw.O (CH.twI w))) (IntegralHeckeForms.Fm0 D.nexp (CH.twI w) j b) ∧
    LiftErrorLocal.rkK (LiftErrorLocal.Mj D (CH.twI w) j b) = D.what₂.D0

def ShareAtTypePrimes (CH : NChoice D) : Prop := ∀ (i0 : Fin 2) w, LiftErrorLocal.Over D i0 w → TwistedAt D w → SHAt D CH w

section Run

variable {D} {CH : NChoice D} (X : LiftErrorLocal.Loc D CH)

def UAt (w : D.what₂.places.Pl) : Prop := ∀ j ∈ LiftErrorLocal.lifts D, ∀ b : Bool,
  IntegralHeckeForms.eThPMt D.nexp (CH.twI w) j b (CH.k' w) (CH.Q w) (X.psiW w b) ≤ LiftErrorLocal.twistV0Submodule D CH w j b ∧
    (D.what₂.Ij (D.what₂.muTw w) j (LiftErrorLocal.plS CH w b) : ℝ) ≤
      (D.what₂.places.ramIdx (LiftErrorLocal.plS CH w b) : ℝ) * X.IsgTw w j b

def LKAt (w : D.what₂.places.Pl) : Prop := ∀ j (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (b : Bool),
  (D.nexp.Bsup (CH.twI w) j b).FG ∧ LiftErrorLocal.GStab (D.nexp.Bsup (CH.twI w) j b) ∧
    X.ThN w j h1 h2 b ≤ D.nexp.Bsup (CH.twI w) j b

def DepAt (L : SizeData₂ D) (T : ThetaDenominatorData D) (er : ℕ → ℕ → ℝ) (w : D.what₂.places.Pl) : Prop :=
  ∀ j (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (b : Bool), ∃ c : D.ntw.O (CH.twI w), c ≠ 0 ∧
    (∀ x ∈ LiftErrorLocal.psiPart (LiftErrorLocal.GSpan (X.ThN w j h1 h2 b)),
      ∃ z ∈ IntegralHeckeForms.Th D.nexp (CH.twI w) j b (T.dat (CH.twI w) j b),
        ((Nat.card D.nexp.U : ℕ) : D.ntw.O (CH.twI w)) • x = c • z) ∧
    ((X.W j h1 h2).eLa X.TO (X.run j).nus (X.laK (LiftErrorLocal.plS CH w b)) : ℝ) /
        (eWL X.B.KO (X.laK (LiftErrorLocal.plS CH w b)) : ℝ) -
      LiftErrorLocal.vDv (D.ntw.O (CH.twI w)) (D.ntw.l (CH.twI w)) c ≤ L.F j w + er j (D.what₂.places.resChar w)

def WBAt : Prop := ∀ j (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (i0 : Fin 2) la, X.laOver i0 la →
  ∀ F ∈ X.WWB j la (X.run j).wL (X.run j).n1 (X.run j).n2, ∃ s : 𝓞 X.B.KO, s ∉ la.asIdeal ∧
    s • F ∈ (X.W j h1 h2).WWc (X.run j).S.sW (X.run j).wL

def DomRun (L : SizeData₂ D) (CP : ℝ) : Prop := ∀ j (_h1 : 1 ≤ j) (_h2 : j ≤ D.R.m), WeightAlgebra.DomAt D L j (X.run j).nW CP

def AdmRun (L : SizeData₂ D) (H : WeightAlgebra.KHyp) (C2 A2 CR CT CRd : ℝ) : Prop :=
  DomRun X L H.C1 → LiftErrorLocal.ArchimedeanSignatureMatching D L X H C2 A2 CR CT ∧ LiftErrorLocal.LemmaBWeightBound D X CRd ∧ WBAt X ∧ LiftErrorLocal.adm11 D L X H C2 A2 CR CT CRd

end Run

structure ONObj (CH : NChoice D) (Xd : DivX D) where
  X : LiftErrorLocal.Loc D CH
  X' : LiftErrorLocal.Loc D CH

  I_eq : X'.I = X.I
  c6 : CartierLocalBounds.Loc D Xd X.P6
  c6' : CartierLocalBounds.Loc D Xd X'.P6
  T : ThetaDenominatorData D

def TwistedPlacesCover : Prop := Formalism.MainNotions.N.LocsCoverTw D

section AdmON

variable {D} (L : SizeData₂ D) {CH : NChoice D} {Xd : DivX D} (O : ONObj D CH Xd)

def admA (CA : ℝ) : Prop := LiftErrorLocal.ConjugationNormInvariance D L O.X CA

def unitBoundAtTwistedPlaces : Prop := ∀ w, TwistedAt D w → UAt O.X w

def OffTypePrimeConditions : Prop := ∀ w, OffG D w → TwistedAt D w → GGAt D CH w ∧ SHAt D CH w ∧ SHbAt D CH w ∧
  (D.what₂.places.resChar w ≠ D.host.pde → LKAt O.X w) ∧ (D.what₂.places.resChar w = D.host.pde → LKAt O.X' w)

def OrbitContentCond (C6 : ℝ) : Prop := CartierLocalBounds.Conclusion5 D Xd O.X.P6 O.c6 C6 ∧ CartierLocalBounds.Conclusion5 D Xd O.X'.P6 O.c6' C6

def DepthFromContent (C6 Cd : ℝ) : Prop := OrbitContentCond O C6 →
  ∃ er : ℕ → ℕ → ℝ, (∀ j l, 0 ≤ er j l) ∧
    (∀ j ∈ SizeData₂.lifts D, ∀ S : Finset ℕ, ∑ l ∈ S, Real.log (l : ℝ) * er j l ≤ onBoundJ D L Cd) ∧
    (∀ w, OffG D w → TwistedAt D w → D.what₂.places.resChar w ≠ D.host.pde → DepAt O.X L O.T er w) ∧
    ∀ w, OffG D w → TwistedAt D w → D.what₂.places.resChar w = D.host.pde → DepAt O.X' L O.T er w

def TypePrimeSizeConds (Cs : ℝ) : Prop :=
  1 ≤ Real.log L.sc.x ∧
    ((O.X.TO : ℝ) + (D.R.f : ℝ) * (D.R.nV : ℝ) ^ 2) * (Real.log (D.host.g 0 : ℝ) + Real.log (D.host.g 1 : ℝ)) ≤
      onBoundJ D L Cs

def AdmON (H : WeightAlgebra.KHyp) (C2 A2 CR CT CRd C6 Cd Cs CA : ℝ) : Prop :=
  L.FDef ∧ AdmRun O.X L H C2 A2 CR CT CRd ∧ AdmRun O.X' L H C2 A2 CR CT CRd ∧ admA L O CA ∧ unitBoundAtTwistedPlaces O ∧
    OffTypePrimeConditions O ∧ OrbitContentCond O C6 ∧ DepthFromContent L O C6 Cd ∧ TypePrimeSizeConds L O Cs ∧ TwistedPlacesCover D ∧ ShareAtTypePrimes D CH

end AdmON

abbrev ONObjF {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Type 1 :=
  ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), ONObj (Fm.D x i) (Fm.ex x hx i).nch (Fm.X x i)

section FamON

variable {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (OF : ONObjF Fm)


end FamON

end Formalism.MainNotions.PDVN

end
