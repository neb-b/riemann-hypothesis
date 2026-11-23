module

public import Mathlib
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.ParamsHeightRankConstant
public import Formalism.SharpRestriction.LevelLetterCocycles.IntegralHeckeForms
public import Formalism.SharpRestriction.LevelLetterCocycles.BlochKatoPhases
public import Formalism.LocalRingCardinality.DataNChoice
public import Formalism.LocalRingCardinality.Bundle0002
public import Formalism.SharpRestriction.ParConsts
public import Formalism.SharpRestriction.LevelLetterCocycles.DataN

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.CharPolyRootsConstruction
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.CharPolyRootsConstruction

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial

def SameSS {k Γ V W : Type} [Field k] [Group Γ] [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
    (ρ : Representation k Γ V) (σ : Representation k Γ W) : Prop :=
  ∃ (s : CompositionSeries (Submodule (MonoidAlgebra k Γ) ρ.asModule))
    (t : CompositionSeries (Submodule (MonoidAlgebra k Γ) σ.asModule)),
    s.head = ⊥ ∧ s.last = ⊤ ∧ t.head = ⊥ ∧ t.last = ⊤ ∧
    ∃ f : Fin s.length ≃ Fin t.length, ∀ j : Fin s.length,
      Nonempty ((↥(s j.succ) ⧸ (s j.castSucc).submoduleOf (s j.succ)) ≃ₗ[MonoidAlgebra k Γ]
        (↥(t (f j).succ) ⧸ (t (f j).castSucc).submoduleOf (t (f j).succ)))

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R}

section HidaSetting

variable (N : NData R H what₂) (i : N.Loc)
  (r : N.X i → (GE N →* GL (Fin R.nV) (N.O i))) (ρ : N.X i → (GE N →* GL (Fin R.r) (N.O i)))

def repBar (x : N.X i) : Representation (kk N i) (GE N) (Fin R.nV → kk N i) :=
  matRep (mapM (IsLocalRing.residue (N.O i)) (rO N i r x))

def ContSemisimple : Prop :=
  ∀ x, Continuous (fun g => rO N i r x g) ∧ IsSS (repK N i r x)

def CharPolyInT : Prop :=
  ∀ (h : GE N) (d : ℕ),
    (fun x => (Matrix.det (1 - (X : (N.O i)[X]) • (rO N i r x h).map (C (R := N.O i)))).coeff d) ∈ N.T i

def Constituents : Prop :=
  (∀ x, AbsIrrDistinct (repK N i r x)) ∧
  (∀ x y, SameSS (repBar N i r x) (repBar N i r y)) ∧
  (∀ x (h : GE N), ∃ s : Multiset (kk N i),
    ((rO N i r x h).map (IsLocalRing.residue (N.O i))).charpoly = (s.map fun a => X - C a).prod)

def ThetaShape : Prop :=
  ∀ x ∈ N.Z i,
    (∃ e : (Fin R.nV → KK N i) ≃ₗ[KK N i] ((Fin R.r → KK N i) × (Fin R.t → KK N i)),
      ∀ g u, e ((mapM (toK N i) (rO N i r x) g).mulVec u) =
        ((mapM (toK N i) (rhoO N i ρ x) g).mulVec (e u).1,
          fun c : Fin R.t => toK N i ((N.chi i ((c : ℕ) + 1) g : (N.O i)ˣ) : N.O i) * (e u).2 c)) ∧
    AbsIrrSub (mapRep (IsLocalRing.residue (N.O i)) (ρ x)) ⊤

def HidaSetting : Prop :=
  ContSemisimple N i r ∧ CharPolyInT N i r ∧ Constituents N i r ∧ ThetaShape N i r ρ

end HidaSetting

section Enlarge

variable (N : NData R H what₂) (i : N.Loc) (N₁ : NData R H what₂) (i₁ : N₁.Loc)
  (σ : N.Om ≃ₐ[H.E] N₁.Om) (φ : N.O i →+* N₁.O i₁) (β : N.X i ≃ N₁.X i₁)

variable {N i N₁ i₁}

end Enlarge

end GlobalTheory.IndefiniteRowSideFullHecke.CharPolyRootsConstruction

end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.GoodPairSystems
section
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions

namespace GlobalTheory.IndefiniteRowSideFullHecke.GoodPairSystems

variable (D : D7)

abbrev TwDatum : Type :=
  Σ (i : D.ntw.Tw) (Q : Finset (PlE D.host)) (k : ℕ), (D.ntw.RCG i Q →* (D.ntw.Ok i k)ˣ)

def Twisted (w : D.what₂.places.Pl) : Prop := D.what₂.muAt w ≠ D.what₂.mu0

def SameBelow (w w' : D.what₂.places.Pl) : Prop :=
  ∀ x : ↥D.LL0, 0 ≤ D.what₂.places.val w (x : D.what₂.LL) ↔ 0 ≤ D.what₂.places.val w' (x : D.what₂.LL)

def SamePair (w w' : D.what₂.places.Pl) : Prop :=
  SameBelow D w w' ∨ SameBelow D (D.what₂.places.conj w) w'

def LiesUnder (i : D.ntw.Tw) (w : D.what₂.places.Pl) : Prop :=
  ∀ x : 𝓞 ↥D.LL0,
    (∃ y ∈ IsLocalRing.maximalIdeal (D.ntw.O0 i),
      algebraMap (D.ntw.O0 i) (FractionRing (D.ntw.O0 i)) y = D.ntw.emb0 i (x : ↥D.LL0)) ↔
    0 < D.what₂.places.val w ((x : ↥D.LL0) : D.what₂.LL)

def TwistedPlaceSettings (twI : D.what₂.places.Pl → D.ntw.Tw) : Prop :=
  (∀ w, Twisted D w → D.ntw.l (twI w) = D.what₂.places.resChar w ∧
    (LiesUnder D (twI w) w ∨ LiesUnder D (twI w) (D.what₂.places.conj w))) ∧
  ∀ w w', Twisted D w → Twisted D w' → SamePair D w w' → twI w = twI w'

def namedPrimes : Set ℕ :=
  {2, 3, 5, D.host.g 0, D.host.g 1, D.host.pde, D.host.pde'} ∪ Set.range fun u : D.what₂.Word => (D.mem u).A.T

variable {D}

def expDat (xd : ThData D) : IntegralHeckeForms.XD D := ⟨xd.xd0, xd.thetaBase_invariant_action⟩

def GoodDatum (xd : ThData D) (N0 : D.ntw.Tw → ℕ) (A : Finset (PlE D.host)) (t : TwDatum D) : Prop :=
  (∀ P ∈ t.2.1, ∀ P', IsConjPl D.host P P' → P' ∈ t.2.1) ∧
  (∀ P ∈ t.2.1, ∀ p ∈ namedPrimes D, P ∉ placesOver D.host.E p) ∧
  (∀ lam : D.ntw.abelian₂ t.1, (∑ δ, D.ntw.th t.1 ∅ lam δ) ≠ 0) ∧
  (∀ j ∈ Finset.Icc 1 D.R.m, ∀ b : Bool,
    IntegralHeckeForms.FullRk D.nexp (expDat xd) t.1 j b (IntegralHeckeForms.SgJ D.nexp (expDat xd) t.1 j b)) ∧
  ∃ S : ∀ (j : ℕ) (b : Bool), Finset (D.nexp.Dat t.1 j b),
    (∀ j ∈ Finset.Icc 1 D.R.m, ∀ b : Bool,
      IntegralHeckeForms.BasisOf D.nexp t.1 j b (IntegralHeckeForms.SgJ D.nexp (expDat xd) t.1 j b) (S j b)) ∧
    ∀ a : ℤ, IsCoprime a (D.ntw.l t.1 : ℤ) →
      IntegralHeckeForms.GoodTw D.nexp (BlochKatoReduction.bk0 D) (expDat xd) N0 t.1 (((D.ntw.l t.1 : ℝ) ^ 2)⁻¹) S A t.2.1 t.2.2.1
        (t.2.2.2 ^ a)

def GoodSystem (xd : ThData D) (N0 : D.ntw.Tw → ℕ) (A : D.ntw.Tw → Finset (PlE D.host))
    (t : D.what₂.places.Pl → TwDatum D) : Prop :=
  TwistedPlaceSettings D (fun w => (t w).1) ∧
  (∀ w, Twisted D w → GoodDatum xd N0 (A (t w).1) (t w)) ∧
  (∀ w w', Twisted D w → Twisted D w' → SamePair D w w' → t w = t w') ∧
  ∀ w w', Twisted D w → Twisted D w' → ¬ SamePair D w w' →
    ∀ P ∈ (t w).2.1, ∀ P' ∈ (t w').2.1, ∀ p : ℕ, p.Prime →
      ¬ (P ∈ placesOver D.host.E p ∧ P' ∈ placesOver D.host.E p)

def recorded (c : NChoice D) (w : D.what₂.places.Pl) : TwDatum D :=
  ⟨c.twI w, c.Q w, c.k' w, BlochKatoReduction.Gen.psiAt (c.sd w) (c.psi' w)⟩

def TwGoodAt (c : NChoice D) (xd : ThData D) (N0 : D.ntw.Tw → ℕ) : Prop :=
  GoodSystem xd N0 (fun _ => ∅) (recorded c) ∧
  ∀ w, Twisted D w → D.what₂.places.conj w ≠ w → c.sd (D.what₂.places.conj w) = !c.sd w

def ExistsChoice (xd : ThData D) (N0 : D.ntw.Tw → ℕ) : Prop :=
  (∃ twI, TwistedPlaceSettings D twI) ∧
  ∀ twI, TwistedPlaceSettings D twI → ∀ A : D.ntw.Tw → Finset (PlE D.host),
    ∃ t : D.what₂.places.Pl → TwDatum D, (∀ w, (t w).1 = twI w) ∧ GoodSystem xd N0 A t

def WithToricIntegralityConstant (D : D7) (P : (D.ntw.Tw → ℕ) → Prop) : Prop :=
  (∃ N0, BlochKatoReduction.adm9 D N0) ∧ ∀ N0, BlochKatoReduction.adm9 D N0 → P N0

def FamTwGood {eps : ℝ} (Fm : FamP eps) : Prop :=
  ∃ x0 : ℝ, ∀ x, x0 ≤ x → ∀ (hx : Fm.x1 < x) (i : Fm.Ix x),
    WithToricIntegralityConstant (Fm.D x i) fun N0 => TwGoodAt (Fm.ex x hx i).nch (Fm.ex x hx i).xd N0

def TwGoodClosed (𝒞 : FamClass) : Prop := Closed 𝒞 fun Fm _ => FamTwGood Fm

open NumberField IsDedekindDomain in
variable (D : _root_.Formalism.BasicNotions.D7) in
variable {D} in
theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.GoodPairSystems.twisted_conj (w : D.what₂.places.Pl) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.GoodPairSystems.Twisted D (D.what₂.places.conj w) ↔ _root_.GlobalTheory.IndefiniteRowSideFullHecke.GoodPairSystems.Twisted D w := by
  unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.GoodPairSystems.Twisted
  rw [_root_.Formalism.BasicNotions.Rows.Data.muAt_conj]

end GlobalTheory.IndefiniteRowSideFullHecke.GoodPairSystems

end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ResidualConstruction
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField Polynomial

section Base

variable {Γ : Type} [Group Γ] {X : Type} {A : Type} [CommRing A] [IsDomain A] [IsLocalRing A] {n r t : ℕ}

abbrev mat {B : Type} [CommRing B] {k : ℕ} (σ : Γ →* GL (Fin k) B) (g : Γ) : Matrix (Fin k) (Fin k) B :=
  ((σ g : GL (Fin k) B) : Matrix (Fin k) (Fin k) B)

abbrev toFr (A : Type) [CommRing A] : A →+* FractionRing A := algebraMap A (FractionRing A)

def overK {k : ℕ} (σ : Γ →* GL (Fin k) A) : Representation (FractionRing A) Γ (Fin k → FractionRing A) :=
  matRep (mapM (toFr A) ((Units.coeHom _).comp σ))

def InRing (T : Subalgebra A (X → A)) (rep : X → (Γ →* GL (Fin n) A))
    (a : X → Matrix (Fin n) (Fin n) A) : Prop :=
  ∃ (m : ℕ) (f : Fin m → X → A) (h : Fin m → Γ), (∀ k, f k ∈ T) ∧
    a = ∑ k, fun x => f k x • mat (rep x) (h k)

def InMatrixCongruenceModule (T : Subalgebra A (X → A)) (rep : X → (Γ →* GL (Fin n) A)) (π : X)
    (e s : X → Matrix (Fin n) (Fin n) A) : Prop :=
  ∃ (m : ℕ) (j : Fin m → X → A) (a : Fin m → X → Matrix (Fin n) (Fin n) A),
    (∀ k, j k ∈ T ∧ j k π = 0 ∧ InRing T rep (a k)) ∧
    s = ∑ k, fun x => j k x • (e x * a k x * e x)

def CharPolyIn (T : Subalgebra A (X → A)) (rep : X → (Γ →* GL (Fin n) A)) : Prop :=
  ∀ (h : Γ) (d : ℕ), (fun x => (mat (rep x) h).charpolyRev.coeff d) ∈ T

def ResidualSame (rep : X → (Γ →* GL (Fin n) A)) : Prop :=
  ∀ (x y : X) (h : Γ), ((mat (rep x) h).map (IsLocalRing.residue A)).charpoly =
    ((mat (rep y) h).map (IsLocalRing.residue A)).charpoly

def IsDecomp (σ : Γ →* GL (Fin n) A) (ρ : Γ →* GL (Fin r) A) (χ : ℕ → (Γ →* Aˣ))
    (e : (Fin n → FractionRing A) ≃ₗ[FractionRing A] ((Fin r → FractionRing A) × (Fin t → FractionRing A))) :
    Prop :=
  ∀ g u, e (overK σ g u) =
    (overK ρ g (e u).1, fun c : Fin t => toFr A ((χ ((c : ℕ) + 1) g : Aˣ) : A) * (e u).2 c)

def HidaSetting (t : ℕ) (T : Subalgebra A (X → A)) (Z : Finset X) (rep : X → (Γ →* GL (Fin n) A))
    (ρ : X → (Γ →* GL (Fin r) A)) (χ : ℕ → (Γ →* Aˣ)) : Prop :=
  IsLocalRing T ∧ (∀ x y : X, x ≠ y → ∃ f ∈ T, (f : X → A) x ≠ (f : X → A) y) ∧
  (∀ x, IsSS (overK (rep x))) ∧
  CharPolyIn T rep ∧
  (∀ x, AbsIrrDistinct (overK (rep x))) ∧ ResidualSame rep ∧
  (∀ x ∈ Z, ∃ e, IsDecomp (t := t) (rep x) (ρ x) χ e) ∧
  (∀ x ∈ Z, AbsIrrSub (mapRep (IsLocalRing.residue A) (ρ x)) ⊤)

def blockPol (e M : Matrix (Fin n) (Fin n) A) : A[X] :=
  Matrix.det ((Polynomial.X : A[X]) • e.map (C (R := A)) - M.map (C (R := A)) + 1 - e.map (C (R := A)))

def IsChoice (t : ℕ) (T : Subalgebra A (X → A)) (rep : X → (Γ →* GL (Fin n) A))
    (ρ : X → (Γ →* GL (Fin r) A)) (χ : ℕ → (Γ →* Aˣ)) (π : X) (g0 : Γ) (L : ℕ)
    (eB e1 X0 : X → Matrix (Fin n) (Fin n) A) : Prop :=
  (InRing T rep eB ∧ InRing T rep e1 ∧ eB * eB = eB ∧ e1 * e1 = e1 ∧ eB * e1 = 0 ∧ e1 * eB = 0) ∧
  (∃ e, IsDecomp (t := t) (rep π) (ρ π) χ e ∧
    (∀ u, e (((eB π).map (toFr A)).mulVec u) = (0, (e u).2)) ∧
    ∃ ε : Matrix (Fin r) (Fin r) (FractionRing A), ε.rank = 1 ∧
      ∀ u, e (((e1 π).map (toFr A)).mulVec u) = (ε.mulVec (e u).1, 0)) ∧
  (∃ (ϖ : A) (s : X → Matrix (Fin n) (Fin n) A), Irreducible ϖ ∧ InMatrixCongruenceModule T rep π eB s ∧
    X0 = fun x => eB x * mat (rep x) g0 * eB x + ϖ ^ L • s x) ∧
  ∀ x, (((blockPol (eB x) (X0 x)).map (toFr A)).rootSet (AlgebraicClosure (FractionRing A))).ncard = t

def RootsIn (t : ℕ) (B : Type) [CommRing B] [Algebra A B] (eB X0 : X → Matrix (Fin n) (Fin n) A) : Prop :=
  ∀ x, ∃ α : Fin t → FractionRing B,
    (blockPol (eB x) (X0 x)).map ((toFr B).comp (algebraMap A B)) = ∏ c, (Polynomial.X - C (α c))

end Base

section Record

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (i : N.Loc)

def IsInertiaCyclotomicGeneratorElement (g0 : GE N) : Prop :=
  (∃ w ∈ placesOver H.E (N.l i), g0 ∈ Ine (F := H.E) (N.plOm.1 w)) ∧
  ∃ u : ℤ_[N.l i]ˣ, ((cycZ (F := H.E) (Ω := N.Om) (N.l i) g0 : ℤ_[N.l i]ˣ) : ℤ_[N.l i]) =
    1 + (N.l i : ℤ_[N.l i]) ^ N.s0 i * (u : ℤ_[N.l i])

def IsEnlargement (rep : N.X i → (GE N →* GL (Fin R.nV) (N.O i)))
    (ρ : N.X i → (GE N →* GL (Fin R.r) (N.O i)))
    (A : Type) [CommRing A] [Algebra A (N.O i)] (TA : Subalgebra A (N.X i → A))
    (repA : N.X i → (GE N →* GL (Fin R.nV) A)) (ρA : N.X i → (GE N →* GL (Fin R.r) A))
    (χA : ℕ → (GE N →* Aˣ)) : Prop :=
  Function.Injective (algebraMap A (N.O i)) ∧
  Subalgebra.toSubmodule (N.T i) =
    Submodule.span (N.O i) ((fun f : N.X i → A => fun x => algebraMap A (N.O i) (f x)) '' (TA : Set _)) ∧
  (∀ x, rep x = mapRep (algebraMap A (N.O i)) (repA x)) ∧
  (∀ x ∈ N.Z i, ρ x = mapRep (algebraMap A (N.O i)) (ρA x)) ∧
  ∀ c, 1 ≤ c → c ≤ R.t → ∀ g, ((N.chi i c g : (N.O i)ˣ) : N.O i) = algebraMap A (N.O i) ((χA c g : Aˣ) : A)

def RepCont (rep : N.X i → (GE N →* GL (Fin R.nV) (N.O i))) : Prop :=
  ∀ x, Continuous fun g => mat (rep x) g

def ConsExist : Prop :=
  ∀ (rep : N.X i → (GE N →* GL (Fin R.nV) (N.O i))) (ρ : N.X i → (GE N →* GL (Fin R.r) (N.O i)))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra ℤ_[N.l i] A]
    [Module.Finite ℤ_[N.l i] A] [Algebra A (N.O i)] [IsScalarTower ℤ_[N.l i] A (N.O i)]
    (TA : Subalgebra A (N.X i → A)) (repA : N.X i → (GE N →* GL (Fin R.nV) A))
    (ρA : N.X i → (GE N →* GL (Fin R.r) A)) (χA : ℕ → (GE N →* Aˣ)),
    RepCont N i rep → IsEnlargement N i rep ρ A TA repA ρA χA → HidaSetting R.t TA (N.Z i) repA ρA χA →
    (∀ π ∈ N.Z i, ∀ g0, IsInertiaCyclotomicGeneratorElement N i g0 → ∀ L : ℕ,
      ∃ eB e1 X0, IsChoice R.t TA repA ρA χA π g0 L eB e1 X0) ∧
    (∀ (g0 : N.X i → GE N) (L : N.X i → ℕ)
        (eB e1 X0 : N.X i → N.X i → Matrix (Fin R.nV) (Fin R.nV) A),
      (∀ π ∈ N.Z i, IsInertiaCyclotomicGeneratorElement N i (g0 π) ∧ IsChoice R.t TA repA ρA χA π (g0 π) (L π) (eB π) (e1 π) (X0 π)) →
      ∃ (B : Type) (_ : CommRing B) (_ : IsDomain B) (_ : IsDiscreteValuationRing B) (_ : Algebra A B),
        Module.Finite A B ∧ Function.Injective (algebraMap A B) ∧
        ∀ π ∈ N.Z i, RootsIn R.t B (eB π) (X0 π)) ∧
    (∀ π ∈ N.Z i, ∀ g0 L eB e1 X0, IsInertiaCyclotomicGeneratorElement N i g0 → IsChoice R.t TA repA ρA χA π g0 L eB e1 X0 →
      RootsIn R.t (N.O i) eB X0 →
      ∃ S : IdempotentChoiceData N i, S.g0 = g0 ∧
        (∀ x, S.eB x = (eB x).map (algebraMap A (N.O i))) ∧
        (∀ x, S.e1 x = (e1 x).map (algebraMap A (N.O i))) ∧
        (∀ x, S.X0 x = (X0 x).map (algebraMap A (N.O i))) ∧
        GoodCongruenceObjects N rep ρ π S)

theorem isEnlargement_self (rep : N.X i → (GE N →* GL (Fin R.nV) (N.O i)))
    (ρ : N.X i → (GE N →* GL (Fin R.r) (N.O i))) :
    IsEnlargement N i rep ρ (N.O i) (N.T i) rep ρ (N.chi i) := by
  refine ⟨fun _ _ h => h, ?_, fun x => ?_, fun x _ => ?_, fun _ _ _ _ => rfl⟩
  · have : ((fun f : N.X i → N.O i => fun x => algebraMap (N.O i) (N.O i) (f x)) '' (N.T i : Set _)) =
        (Subalgebra.toSubmodule (N.T i) : Set _) := by
      simp
    rw [this, Submodule.span_eq]
  · ext g a b
    rfl
  · ext g a b
    rfl

end Record

end GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices

end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.SemisimplificationConstituents
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.SemisimplificationConstituents

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

section Rep

variable {k : Type} [Field k] {Γ : Type} [Group Γ]

def IsSemisimplificationOf {W V : Type} [AddCommGroup W] [Module k W] [AddCommGroup V] [Module k V]
    (s : Representation k Γ W) (ρ : Representation k Γ V) : Prop :=
  IsSS s ∧ ∃ (m : ℕ) (Ws : Fin m → Submodule k W) (e : W ≃ₗ[k] V),
    (∀ j, Stable s (Ws j)) ∧ DirectSum.IsInternal Ws ∧
    ∀ j g, ∀ v ∈ Ws j, ρ g (e v) - e (s g v) ∈ (⨆ j' ∈ Set.Iio j, Ws j').map (e : W →ₗ[k] V)

end Rep

section Loc

variable (D : D7) (i : D.nd.Loc)

end Loc

end GlobalTheory.IndefiniteRowSideFullHecke.SemisimplificationConstituents

end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.SplitPlaceTypes
section
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory.IndefiniteRowSideFullHecke.SplitPlaceTypes

section Host

variable {R : Ranks} (H : Host R)

def SplitRowPrime (l : ℕ) : Prop :=
  l.Prime ∧ 5 ≤ l ∧ l ≠ H.q ∧ l ≠ H.d ∧ (∀ k, l ≠ H.g k) ∧ H.cls l = PrimeClass.splitK

def halfType (s : Bool) : Set (H.E →+* ℂ) :=
  match s with
  | true => H.cmType
  | false => {φ | φ.comp (H.conj : H.E →+* H.E) ∈ H.cmType}

def PlacesSplit (l : ℕ) : Prop :=
  ∀ w ∈ placesOver H.E l,
    w.asIdeal.ramificationIdx ℤ = 1 ∧
    (∃ w' ∈ placesOver H.E l, IsConjPl H w w') ∧
    ∀ w', IsConjPl H w w' → w' ≠ w

end Host

section Loc

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂}
  (nbr : Br.NBr N) (i : N.Loc)

def EmbIn (s : Bool) (w : HeightOneSpectrum (𝓞 H.E)) (hw : w ∈ placesOver H.E (N.l i))
    (τ : Br.Kw nbr i w hw →ₐ[ℚ_[N.l i]] Br.LL nbr i w hw) : Prop :=
  (∀ x : H.E, ∃ y : what₂.LL, Br.toLLK (nbr i w hw) (N.embK i y) = τ (Br.cEw nbr i w hw x)) ∧
  ∃ φ ∈ halfType H s,
    ∀ (x : H.E) (y : what₂.LL), Br.toLLK (nbr i w hw) (N.embK i y) = τ (Br.cEw nbr i w hw x) →
      what₂.embLL y = φ x

def PlIn (s : Bool) (w : HeightOneSpectrum (𝓞 H.E)) (hw : w ∈ placesOver H.E (N.l i)) : Prop :=
  Nonempty (Br.Kw nbr i w hw →ₐ[ℚ_[N.l i]] Br.LL nbr i w hw) ∧ ∀ τ, EmbIn nbr i s w hw τ

def columns (s : Bool) : Set (HeightOneSpectrum (𝓞 H.E)) :=
  {w | ∃ hw : w ∈ placesOver H.E (N.l i), PlIn nbr i s w hw}

def TypesPair : Prop :=
  (∀ (w : HeightOneSpectrum (𝓞 H.E)) (hw : w ∈ placesOver H.E (N.l i)),
    Loc.K0 (nbr i w hw).Kw = (nbr i w hw).Kw.1) ∧
  (∀ (w : HeightOneSpectrum (𝓞 H.E)) (hw : w ∈ placesOver H.E (N.l i)) τ,
    ¬ (EmbIn nbr i true w hw τ ∧ EmbIn nbr i false w hw τ)) ∧
  (∀ (w w' : HeightOneSpectrum (𝓞 H.E)) (hw : w ∈ placesOver H.E (N.l i))
      (hw' : w' ∈ placesOver H.E (N.l i)), IsConjPl H w w' →
    (PlIn nbr i true w hw ∧ PlIn nbr i false w' hw') ∨
      (PlIn nbr i false w hw ∧ PlIn nbr i true w' hw')) ∧
  ∀ s : Bool,
    (∀ w ∈ placesOver H.E (N.l i), ∀ w', IsConjPl H w w' →
      Xor (w ∈ columns nbr i s) (w' ∈ columns nbr i s)) ∧
    (columns nbr i s).Finite ∧
    ∀ w ∈ placesOver H.E (N.l i), locDeg H.E w * (columns nbr i s).ncard = R.f

end Loc

def SplitRow_at (D : D7) : Prop :=
  (∀ l : ℕ, SplitRowPrime D.host l → PlacesSplit D.host l) ∧
  ∀ i : D.nd.Loc, SplitRowPrime D.host (D.nd.l i) → TypesPair (N := D.nd) D.nbr i

end GlobalTheory.IndefiniteRowSideFullHecke.SplitPlaceTypes

end
end

