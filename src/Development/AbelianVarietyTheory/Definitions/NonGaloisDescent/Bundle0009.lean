module

public import Mathlib
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EqOfPowEqOneOfNormSubLt
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ResBound
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0007
public import Formalism.SharpRestriction.LevelLetterCocycles.BlochKatoPhases

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdmSt
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst TensorProduct
open scoped Formalism.Per

namespace GlobalTheory.PMon

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l)

def Fil (a : ℤ) : Set P.R.BdR := ((P.PD (botExt l)).Fil a : Set P.R.BdR)

def fr (l : ℕ) [Fact l.Prime] (m : ℕ) : ↥(MaximalUnramifiedExtension l) →+* ↥(MaximalUnramifiedExtension l) := ((frobUr l ^ m : ↥(MaximalUnramifiedExtension l) →ₐ[ℚ_[l]] ↥(MaximalUnramifiedExtension l)) : ↥(MaximalUnramifiedExtension l) →+* ↥(MaximalUnramifiedExtension l))

def kd : ↥(MaximalUnramifiedExtension l) →+* P.R.BdR := (algebraMap (Om l) P.R.BdR).comp (algebraMap ↥(MaximalUnramifiedExtension l) (Om l))

def ks : ↥(MaximalUnramifiedExtension l) →+* Bst P := (Polynomial.C : P.R.B →+* Bst P).comp (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B)

def ev (m : ℕ) (b : P.R.B) : P.R.BdR := P.ιB (P.φB^[m] b)

def tz (a : ℤ) : P.R.BdR := P.ιB (((isUnit_tB P).unit ^ a : P.R.Bˣ) : P.R.B)

variable {n : Type} [Fintype n] [DecidableEq n]

def UnitM (U : GL n P.R.BdR) : Prop :=
  (∀ i j, (U : Matrix n n P.R.BdR) i j ∈ Fil P 0) ∧ ∀ i j, ((U⁻¹ : GL n P.R.BdR) : Matrix n n P.R.BdR) i j ∈ Fil P 0

variable {K : FinExt l}

structure IsRat (r : ℕ) (ρ : ↥(GK K) →* GL n ↥(MaximalUnramifiedExtension l)) : Prop where

  pos : 0 < r

  le : ∀ c : ↥(MaximalUnramifiedExtension l), fr l r c = c → (c : Om l) ∈ K.1

  rat : ∀ g i j, fr l r ((ρ g : Matrix n n ↥(MaximalUnramifiedExtension l)) i j) = (ρ g : Matrix n n ↥(MaximalUnramifiedExtension l)) i j

  cont : ∀ i j, Continuous fun g => (((ρ g : Matrix n n ↥(MaximalUnramifiedExtension l)) i j : ↥(MaximalUnramifiedExtension l)) : Om l)

def matD (ρ : ↥(GK K) →* GL n ↥(MaximalUnramifiedExtension l)) (m : ℕ) (g : ↥(GK K)) : Matrix n n P.R.BdR :=
  (ρ g : Matrix n n ↥(MaximalUnramifiedExtension l)).map fun c => kd P (fr l m c)

def AdmDR (ρ : ↥(GK K) →* GL n ↥(MaximalUnramifiedExtension l)) : Prop :=
  ∀ m : ℕ, ∃ Q : GL n P.R.BdR, ∀ g : ↥(GK K),
    matD P ρ m g * (Q : Matrix n n P.R.BdR).map (P.actQdR (g : GQ l)) = Q

def Framed {r : ℕ} (ρ : ↥(GK K) →* GL n ↥(MaximalUnramifiedExtension l)) (w : Fin r → n → ℤ) : Prop :=
  ∀ m : Fin r, ∃ U : GL n P.R.BdR, UnitM P U ∧ ∀ g : ↥(GK K),
    matD P ρ m g * (U : Matrix n n P.R.BdR).map (P.actQdR (g : GQ l)) =
      (U : Matrix n n P.R.BdR) * Matrix.diagonal fun j =>
        algebraMap ℚ_[l] P.R.BdR ((P.χQ (g : GQ l) ^ w m j : ℚ_[l]ˣ) : ℚ_[l])

def AdmSt (ρ : ↥(GK K) →* GL n ↥(MaximalUnramifiedExtension l)) : Prop :=
  ∃ (K' : FinExt l) (hK : K.1 ≤ K'.1) (Q : GL n (Bst P)), ∀ g : ↥(GK K'),
    (ρ ⟨g, GK_le hK g.2⟩ : Matrix n n ↥(MaximalUnramifiedExtension l)).map (ks P) *
      (Q : Matrix n n (Bst P)).map (actSt P (g : GQ l)) = Q

def Splits (r : ℕ) (ρ : ↥(GK K) →* GL n ↥(MaximalUnramifiedExtension l)) : Prop :=
  ∃ (s : Finset n) (p : GL n ↥(MaximalUnramifiedExtension l)), s.Nonempty ∧ s ≠ Finset.univ ∧
    (∀ i j, fr l r ((p : Matrix n n ↥(MaximalUnramifiedExtension l)) i j) = (p : Matrix n n ↥(MaximalUnramifiedExtension l)) i j) ∧
    ∀ g i j, i ∉ s → j ∈ s → ((p⁻¹ * ρ g * p : GL n ↥(MaximalUnramifiedExtension l)) : Matrix n n ↥(MaximalUnramifiedExtension l)) i j = 0

def eps {α : Type} [DecidableEq α] (x y z : α) : ℤ := if z = x then -1 else if z = y then 1 else 0


variable {P} in
def Plus {AI : LocAinf l P} (T : LocTied l P AI) (b : P.R.B) : Prop :=
  ∃ (N : ℕ) (x : Formalism.Per.Acris l), T.eB ((l : P.R.B) ^ N * b) = algebraMap (Formalism.Per.Acris l) (Formalism.Per.Bcris l) x

end GlobalTheory.PMon

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GlobalCore
section
noncomputable section

namespace GlobalTheory.Cut

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal

def matKO {O : Type} [CommRing O] [IsDomain O] {k : ℕ} (A : Matrix (Fin k) (Fin k) O) :
    KOG O k →ₗ[O] KOG O k :=
  (stdG O (FractionRing O) k).mapQ (stdG O (FractionRing O) k)
    (((A.map (algebraMap O (FractionRing O))).mulVecLin).restrictScalars O) (by
      rintro _ ⟨u, rfl⟩
      refine ⟨A.mulVec u, ?_⟩
      funext j
      exact RingHom.map_mulVec (algebraMap O (FractionRing O)) A u j)

variable {D : D7} (i : D.nd.Loc)

def ccOff (Xs : Set (D.nd.X i)) (π : D.nd.X i) : Ideal (D.nd.O i) :=
  Ideal.span {a | ∃ f ∈ D.nd.T i, (∀ x ∈ Xs, x ∉ D.nd.Z i → f x = 0) ∧ a = f π}

def vccOff (Xs : Set (D.nd.X i)) (π : D.nd.X i) : ℚ :=
  lenUnit (O := D.nd.O i) (D.nd.l i) (D.nd.O i ⧸ ccOff i Xs π)

def lenQ (a : D.nd.O i) : ℕ∞ := Module.length (D.nd.O i) (D.nd.O i ⧸ Ideal.span {a})

variable (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (S : IdempotentChoiceData D.nd i) (Xs : Set (D.nd.X i))

def cocW {k : ℕ} (ψ : (S.X' → MatN D.nd i) → Matrix (Fin k) (Fin k) (D.nd.O i)) :
    Submodule (D.nd.O i) (GE D.nd → KOG (D.nd.O i) k) :=
  Submodule.span (D.nd.O i)
    {c | ∃ φ : (S.X' → MatN D.nd i) →ₗ[D.nd.O i] KOG (D.nd.O i) k,
      (∀ a, InR' D.nd r S a → ∀ y, InY D.nd r S y → φ (a * y) = matKO (ψ a) (φ y)) ∧
      (∀ y, InY D.nd r S y → (∀ x', S.p x' ∈ Xs → y x' = 0) → φ y = 0) ∧
      c = fun γ => φ (yg D.nd r S γ)}

def cocRho : Submodule (D.nd.O i) (GE D.nd → KOG (D.nd.O i) D.R.r) := cocW i r S Xs S.ψρ

def cocChi (c : Fin D.R.t) : Submodule (D.nd.O i) (GE D.nd → KOG (D.nd.O i) 1) :=
  cocW i r S Xs fun a => S.ψχ c a • (1 : Matrix (Fin 1) (Fin 1) (D.nd.O i))

def locFun {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (w : HeightOneSpectrum (𝓞 D.host.E))
    (hw : w ∈ placesOver D.host.E (D.nd.l i)) (c : GE D.nd → KOG (D.nd.O i) k) :
    Br.G D.nbr i w hw → (Fin k → Br.LL D.nbr i w hw) ⧸ (Br.locLat D.nbr i w hw M).T :=
  fun g => Br.phi (D.nbr i w hw) k (c ((Br.iota D.nbr i w hw g : Gw D.nd w) : GE D.nd))

def IsFinL {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (c : GE D.nd → KOG (D.nd.O i) k) : Prop :=
  ∀ w hw, locFun i M w hw c ∈ HfD (Br.PD D.loc D.nbr i w hw) (Br.locLat D.nbr i w hw M)

def resIne {k : ℕ} (C : Submodule (D.nd.O i) (GE D.nd → KOG (D.nd.O i) k)) (v : HeightOneSpectrum (𝓞 D.host.E)) :
    Submodule (D.nd.O i) (↥(Ine (F := D.host.E) (D.nd.plOm.1 v)) → KOG (D.nd.O i) k) :=
  C.map (LinearMap.funLeft (D.nd.O i) (KOG (D.nd.O i) k) Subtype.val)

def QuadAt (v : HeightOneSpectrum (𝓞 D.host.E)) : Prop :=
  ∀ x ∈ Xs, ∀ γ ∈ Ine (F := D.host.E) (D.nd.plOm.1 v),
    (rO D.nd i r x γ - 1) *
      (rO D.nd i r x γ - ((chiU D.nd i 1 γ : (D.nd.O i)ˣ) : D.nd.O i) • (1 : MatN D.nd i)) = 0

def PolyAt (π : D.nd.X i) (v : HeightOneSpectrum (𝓞 D.host.E)) : Prop :=
  ∃ P : Polynomial (D.nd.T i),
    (∀ x ∈ Xs, ∀ γ ∈ Ine (F := D.host.E) (D.nd.plOm.1 v),
      Polynomial.aeval (rO D.nd i r x (D.nd.gam0 i v)) (P.map (evT D.nd i x)) *
        (rO D.nd i r x γ - ((chiU D.nd i 1 γ : (D.nd.O i)ˣ) : D.nd.O i) • (1 : MatN D.nd i)) = 0) ∧
    IsUnit ((P.map (evT D.nd i π)).eval (D.nd.zeta i v))

def NoChiOff : Prop :=
  ∀ x ∈ Xs, x ∉ D.nd.Z i → ∀ u : Fin D.R.nV → KK D.nd i,
    (∀ g, (mapM (toK D.nd i) (rTwO D.nd i r x) g).mulVec u = u) → u = 0

def UnrOut : Prop :=
  ∀ v, v ∉ placesOver D.host.E (D.nd.l i) → v ∉ D.nd.S i → v ∉ D.nd.Q i →
    ∀ x ∈ Xs, ∀ γ ∈ Ine (F := D.host.E) (D.nd.plOm.1 v), rTwO D.nd i r x γ = 1

def GlobalCore : Prop :=
  ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (Xs : Set (D.nd.X i)) (eρ eχ : ℕ)
    (S : IdempotentChoiceData D.nd i),
    GoodR D.nd i r → GoodCongruenceObjects D.nd r ρ π S → π ∈ D.nd.Z i → π ∈ Xs →
    NoChiOff i r Xs → UnrOut i r Xs →
    (∀ v ∈ D.nd.S i, (QuadAt i r Xs v ∧ IsUnit (D.nd.zeta i v - 1)) ∨ PolyAt i r Xs π v) →
    (∀ v ∈ D.nd.Q i, QuadAt i r Xs v ∧ D.nd.zeta i v ≠ 1) →
    (∀ w (hw : w ∈ placesOver D.host.E (D.nd.l i)), GlobalTheory.Pass.HfChar i w hw ∧
      GlobalTheory.Pass.LocBound i w hw r Xs (WpO D.nd i ρ π) eρ ∧
      ∀ c ∈ Finset.Icc 1 D.R.t, GlobalTheory.Pass.LocBound i w hw r Xs (chiRatO D.nd i c) eχ) →
    Br.sFin D.loc D.nbr i ρ π →
    (∀ e ∈ Finset.Ioo 0 D.R.t, Formalism.GaloisCohomology.shaLen (D.nd.ldat (D.nd.l i)) (e : ℤ) < ⊤) →
    vccOff i Xs π ≤
      (((placesOver D.host.E (D.nd.l i)).ncard * (eρ + D.R.t * eχ) : ℕ) : ℚ) +
      Br.sPi D.loc D.nbr i ρ π + (∑ e ∈ Finset.Ioo 0 D.R.t, (D.what₂.shaLen (D.nd.l i) e : ℚ)) +
      (padicValNat (D.nd.l i) (hE D.host) : ℚ) + 4 * (D.R.nV : ℚ) * D.nd.vdel i +
      (D.R.t : ℚ) * ∑ q ∈ D.nd.Q i,
        lenUnit (O := D.nd.O i) (D.nd.l i) (D.nd.O i ⧸ Ideal.span {D.nd.zeta i q - 1})

end GlobalTheory.Cut

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsCharLab
section
noncomputable section

namespace GlobalTheory.GLp

open Polynomial GlobalTheory.GLq
open scoped Classical

variable (g : ℕ) [Fact g.Prime]

def inc (n : ℕ) : GL (Fin n) ℤ_[g] →* GL (Fin n) ℚ_[g] :=
  Matrix.GeneralLinearGroup.map (algebraMap ℤ_[g] ℚ_[g])

def red (n : ℕ) : GL (Fin n) ℤ_[g] →* Gn g n := Matrix.GeneralLinearGroup.map (PadicInt.toZMod (p := g))

def lift (n : ℕ) (x : Gn g n) : GL (Fin n) ℚ_[g] := inc g n (Function.invFun (red g n) x)

variable {g} {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

def fixK1 (π : Representation ℂ (GL (Fin n) ℚ_[g]) V) : Submodule ℂ V :=
  ⨅ k : (red g n).ker, LinearMap.ker (π (inc g n k) - LinearMap.id)

def actK (π : Representation ℂ (GL (Fin n) ℚ_[g]) V) (a : MonoidAlgebra ℂ (Gn g n)) : V →ₗ[ℂ] V :=
  ∑ x : Gn g n, a.coeff x • π (lift g n x)

def IsIrrRep {G : Type} [Group G] (π : Representation ℂ G V) : Prop :=
  Nontrivial V ∧ ∀ W : Submodule ℂ V, (∀ x, ∀ v ∈ W, π x v ∈ W) → W = ⊥ ∨ W = ⊤

def blk (a b n : ℕ) (x : Gn g a) (y : Gn g b) : Gn g n :=
  toG (fun i j : Fin n =>
    if (i : ℕ) < a ∧ (j : ℕ) < a then Formalism.MainNotions.ArithmeticCylinders.entN (x : Mt g a) i j
    else if a ≤ (i : ℕ) ∧ a ≤ (j : ℕ) then Formalism.MainNotions.ArithmeticCylinders.entN (y : Mt g b) (i - a) (j - a) else 0)

def IsParVec (π : Representation ℂ (GL (Fin n) ℚ_[g]) V) (a b : ℕ) (χ : (ZMod g)ˣ →* ℂˣ) (v : V) : Prop :=
  v ∈ fixK1 π ∧
    (∀ u : Gn g n, InPar a (u : Mt g n) → tl a (u : Mt g n) = 1 → br a b (u : Mt g n) = 1 → π (lift g n u) v = v) ∧
    ∀ y : Gn g b, π (lift g n (blk a b n 1 y)) v = ((χ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ) • v

def actTop (π : Representation ℂ (GL (Fin n) ℚ_[g]) V) (a b : ℕ) (e : MonoidAlgebra ℂ (Gn g a)) : V →ₗ[ℂ] V :=
  ∑ x : Gn g a, e.coeff x • π (lift g n (blk a b n x 1))

def IsCharLab (L : LabelDatum g) (χ : (ZMod g)ˣ →* ℂˣ) (c : ZMod g) : Prop :=
  c ≠ 0 ∧ ∀ u : (ZMod g)ˣ, algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g) u = L.gen 1 →
    ((χ u : ℂˣ) : ℂ) = L.teich (algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g) c)

end GlobalTheory.GLp
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.JSmul
section
noncomputable section
namespace GlobalTheory.Present
open scoped LaurentSeries PowerSeries
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n₀ : ℕ}
    (W : LocWach PD LL O v n₀) {k : Type} [Field k] [Algebra O k]

def DΔ (T : LocLat G Qp LL O) : AddSubgroup (W.DD T) where
  carrier := {x | ∀ δ ∈ W.DelF, W.γD T δ x = x}
  zero_mem' := fun δ _ => map_zero _
  add_mem' := fun ha hb δ hδ => by rw [map_add (f := _), ha δ hδ, hb δ hδ]
  neg_mem' := fun ha δ hδ => by rw [map_neg, ha δ hδ]

def Onto (T : LocLat G Qp LL O) (A : Ob k G) (q : ↥T.L.T →ₗ[O] (Fin A.m → k)) : Prop :=
  Function.Surjective q ∧ ∀ σ x, q (latRep T.L σ x) = A.ρ σ (q x)

structure Pres {l n : ℕ} {R : RingPG k l} (F : DFun R n G) (ι : k⸨X⸩ →ₐ[k] k⸨X⸩) (τ : ZMod n → ZMod n₀)
    (γ : W.Gam) where
  ι_v : ι (vv k) = ((PowerSeries.map (algebraMap O k) W.π₀₁ : k⟦X⟧) : k⸨X⸩)
  obj : ∀ (T : LocLat G Qp LL O) (A : Ob k G) q, Onto T A q → F.Obj A

  j : ∀ (T : LocLat G Qp LL O) (A : Ob k G), (↥T.L.T →ₗ[O] (Fin A.m → k)) → ZMod n → (↥(DΔ W T) →+ Vc k A.m)
  j_surj : ∀ T A q, Onto T A q → ∀ i, Function.Surjective (j T A q i)
  j_smul : ∀ T A q, Onto T A q → ∀ i (a : LetA O n₀) (c : k⟦X⟧) (x y : ↥(DΔ W T)),
    ι (c : k⸨X⸩) = ((PowerSeries.map (algebraMap O k) (a (τ i)) : k⟦X⟧) : k⸨X⸩) →
    (y : W.DD T) = a • (x : W.DD T) → j T A q i y = c • j T A q i x
  j_φ : ∀ T A q, Onto T A q → ∀ i (x y : ↥(DΔ W T)), (y : W.DD T) = W.φD T x →
    j T A q i y = (F.D A).φ i (j T A q (i - 1) x)
  j_γ : ∀ T A q, Onto T A q → ∀ i (x y : ↥(DΔ W T)), (y : W.DD T) = W.γD T γ x →
    j T A q i y = (F.D A).γ i (j T A q i x)
  j_ker : ∀ T A q, Onto T A q → ∀ (T' : LocLat G Qp LL O) (f : LatHom T'.L T.L), Function.Injective f.f →
    (∀ x : ↥T.L.T, q x = 0 ↔ ∃ y ∈ T'.L.T, f.f y = x) → ∀ i (x : ↥(DΔ W T)),
    j T A q i x = 0 ↔ ∃ y, W.map f y = (letE (τ i) : LetA O n₀) • (x : W.DD T)
  j_map : ∀ T A q T' A' q', Onto T A q → Onto T' A' q' → ∀ (f : LatHom T.L T'.L)
    (g : (Fin A.m → k) →ₗ[k] (Fin A'.m → k)), IsHom A A' g →
    (∀ (x : ↥T.L.T) (x' : ↥T'.L.T), (x' : T'.V) = f.f x → q' x' = g (q x)) →
    ∀ i (x : ↥(DΔ W T)) (y : ↥(DΔ W T')), (y : W.DD T') = W.map f x → j T' A' q' i y = F.map A A' g i (j T A q i x)
  j_unit : ∀ q, Onto W.one (chr 1 : Ob k G) q → ∀ x : ↥(DΔ W W.one),
    W.N W.one = Submodule.span (LetA O n₀) {(x : W.DD W.one)} → ∀ i,
    Submodule.span k⟦X⟧ {j W.one (chr 1) q i x} = Submodule.span k⟦X⟧ {F.unit i}

end GlobalTheory.Present

namespace GlobalTheory.TopSteps.TopSit
open scoped LaurentSeries PowerSeries
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.PhiGam GlobalTheory.Models GlobalTheory.Present
variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} (S : TopSit P)

abbrev W (H : LocHW l P) := H.W S.K 1 S.LL S.hyp.1.2.1.2.2

def RealD (H : LocHW l P) : Prop :=
  ∀ (k : Type) [Field k] [Algebra S.O k] [CharP k l], S.IsRes k →
    ∃ (R : RingPG k l) (ι : k⸨X⸩ →ₐ[k] k⸨X⸩), GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.IsCyclotomic R ι ∧
    ∃ (F : DFun R S.n S.G) (τ : ZMod S.n → ZMod (Module.finrank ℚ_[l] ↥(K0 S.K))) (γ : (S.W H).Gam),
      (∀ i, (S.W H).emb (τ i) = S.emb i) ∧ ((S.W H).χΓ γ : S.O) = 1 + (l : S.O) ∧
      Nonempty (Pres (S.W H) F ι τ γ)

end GlobalTheory.TopSteps.TopSit
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MemRootsBarXSubC
section
noncomputable section
namespace GlobalTheory.GLq.Model
open Polynomial Formalism.CyclotomicNorms

variable (g : ℕ) [hg : Fact g.Prime]

theorem N_pos {d : ℕ} (hd : 0 < d) : 0 < g ^ d - 1 := Nat.sub_pos_of_lt (Nat.one_lt_pow hd.ne' hg.out.one_lt)


open Formalism.MainNotions.ArithmeticCylinders
variable {g}

theorem thetaOf_gen_pow (L : LabelDatum g) {d : ℕ} (hd : 0 < d) {x : Fbar g} (hx : x ^ (g ^ d - 1) = 1) (n : ℕ) :
    thetaOf L d x (L.gen d ^ n) = L.teich x ^ n := by
  have hex : ∃ m : ℕ, L.gen d ^ n = L.gen d ^ m := ⟨n, rfl⟩
  rw [thetaOf, dite_eq_left hex]
  have hm := hex.choose_spec
  have hN := N_pos g hd
  have hP : IsPrimitiveRoot (L.gen d) (g ^ d - 1) :=
    L.gen_order d hd ▸ IsPrimitiveRoot.orderOf (L.gen d)

  have h1 : n % (g ^ d - 1) = hex.choose % (g ^ d - 1) := by
    apply hP.pow_inj (Nat.mod_lt _ hN) (Nat.mod_lt _ hN)
    rw [← L.gen_order d hd, pow_mod_orderOf, pow_mod_orderOf]
    exact hm
  have h2 : orderOf (L.teich x) ∣ g ^ d - 1 :=
    orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hx, map_one])
  have h3 : n % orderOf (L.teich x) = hex.choose % orderOf (L.teich x) := Nat.ModEq.of_dvd h2 h1
  calc L.teich x ^ hex.choose = L.teich x ^ (hex.choose % orderOf (L.teich x)) :=
        (pow_mod_orderOf _ _).symm
    _ = L.teich x ^ (n % orderOf (L.teich x)) := by rw [h3]
    _ = L.teich x ^ n := pow_mod_orderOf _ _

theorem toG_coe {n : ℕ} (x : Gn g n) : toG (x : Mt g n) = x := by
  rw [toG, dite_eq_left x.isUnit]
  exact Units.ext (IsUnit.unit_spec _)

theorem tl_self {n : ℕ} (M : Mt g n) : tl n M = M := by
  ext i j
  simp [tl, entN]

theorem hc_full {n : ℕ} (α : Gn g n → ℂ) (hα : IsClass α) : hc n 0 α (fun _ => 1) n = α := by
  funext x

  have hpar : ∀ M : Mt g n, InPar n M := fun M i j _ hi => absurd i.isLt (not_lt.mpr hi)
  have hα' : ∀ y : Gn g n, α (y⁻¹ * x * y) = α x := fun y => by
    simpa using hα x y⁻¹
  have hcard : (Fintype.card (Gn g n) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  simp only [hc, hcT, hpar, if_true, mul_one, tl_self, toG_coe, hα', Finset.sum_const,
    Finset.filter_true, Finset.card_univ, nsmul_eq_mul]
  exact inv_mul_cancel_left₀ hcard _

end GlobalTheory.GLq.Model
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TripleAtt
section
noncomputable section

namespace GlobalTheory.TripleGal

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N}

def rd (i : X.Tw) (ι : FractionRing (X.O0 i) →+* ℂ) : X.O0 i →+* ℂ :=
  ι.comp (algebraMap (X.O0 i) (FractionRing (X.O0 i)))

def cj (D : Formalism.BasicNotions.D7) : D.host.E →+* D.host.E :=
  (D.host.conj : D.host.E ≃ₐ[ℚ] D.host.E).toRingEquiv.toRingHom

def UnrRho (i : X.Tw) (s : X.Sig i) : Prop :=
  ∀ v, v ∉ placesOver D.host.E (X.l i) → (∀ k, v ∉ placesOver D.host.E (D.host.g k)) →
    ∀ A : ValuationSubring N.Om, IsPlaceOver A v → ∀ σ ∈ Ine (F := D.host.E) A, X.rhoS i s σ = 1

def HodgeL (bkP : BKPh X) (i : X.Tw) (s : X.Sig i) : Prop :=
  ∀ v (hv : v ∈ placesOver D.host.E (X.l i)), ∀ r ∈ ({X.rhoS i s, Tgl i s} : Set _),
    (bkP.br i v hv).IsdRW (D.loc (X.l i)) (r.comp (DecV N v).subtype) ∧
    ((∀ k, X.l i ≠ D.host.g k) → (bkP.br i v hv).IsCrysW (D.loc (X.l i)) (r.comp (DecV N v).subtype)) ∧
    (bkP.br i v hv).IsPotCrysW (D.loc (X.l i)) (r.comp (DecV N v).subtype)

def NoInv (i : X.Tw) (M : Formalism.MainNotions.BlochKatoReduction.Gen.GE N → Matrix (Fin D.R.r) (Fin D.R.r) (X.O0 i)) (v : HeightOneSpectrum (𝓞 D.host.E)) : Prop :=
  ∀ A : ValuationSubring N.Om, IsPlaceOver A v →
    ∀ x : Fin D.R.r → FractionRing (X.O0 i), (∀ g ∈ Dec (F := D.host.E) A,
      ((M g).map (algebraMap (X.O0 i) (FractionRing (X.O0 i)))).mulVec x = x) → x = 0

def NegCount (bkP : BKPh X) (i : X.Tw) (s : X.Sig i) : Prop :=
  ∀ v v' (hv : v ∈ placesOver D.host.E (X.l i)) (hv' : v' ∈ placesOver D.host.E (X.l i))
    (τ : EmbV bkP i v hv) (τ' : EmbV bkP i v' hv'), IsConjEmb bkP i v v' hv hv' τ τ' →
    dimD bkP i v hv (Tgl i s) τ + dimD bkP i v' hv' (Tgl i s) τ' =
      dimFil0 bkP i v hv (Tgl i s) τ + dimFil0 bkP i v' hv' (Tgl i s) τ' + D.R.r

def Pure (i : X.Tw) (s : X.Sig i) (ι : FractionRing (X.O0 i) →+* ℂ) : Prop :=
  ∀ v, v ∉ placesOver D.host.E (X.l i) → v ∉ Spl (X := X) i → ∀ A : ValuationSubring N.Om, IsPlaceOver (F := D.host.E) A v →
    ∀ σ : Formalism.MainNotions.BlochKatoReduction.Gen.GE N, IsFrob (F := D.host.E) A (normV v) σ → ∀ z : ℂ,
      ((Tmat i s σ).charpoly.map (rd i ι)).IsRoot z → ‖z‖ = ((normV v : ℕ) : ℝ) ^ ((1 - (D.R.t : ℝ)) / 2)

def ReadEmb (bkP : BKPh X) (i : X.Tw) (ι : FractionRing (X.O0 i) →+* ℂ) (v : HeightOneSpectrum (𝓞 D.host.E))
    (hv : v ∈ placesOver D.host.E (X.l i)) (τ : EmbV bkP i v hv) (τc : D.host.E →+* ℂ) : Prop :=
  ∀ (x : D.host.E) (n d : X.O0 i), IsFrac bkP i v hv (τ (cE bkP i v hv x)) n d → rd i ι d * τc x = rd i ι n

def JumpsAre (bkP : BKPh X) (i : X.Tw) (s : X.Sig i) (ι : FractionRing (X.O0 i) →+* ℂ)
    (J : (D.host.E →+* ℂ) → Multiset ℤ) : Prop :=
  ∀ v (hv : v ∈ placesOver D.host.E (X.l i)) (τ : EmbV bkP i v hv) (τc : D.host.E →+* ℂ), ReadEmb bkP i ι v hv τ τc →
    ∀ a : ℤ, Formalism.WeaklyAdmissibleFiltrations.multV (PDv bkP i v hv) (repV bkP i v hv (Tgl i s)) τ a = ((J τc).count a : ℤ)

def GoodJ (D : Formalism.BasicNotions.D7) (J : (D.host.E →+* ℂ) → Multiset ℤ) : Prop :=
  ∀ τc, Multiset.card (J τc) = D.R.r ∧ J (τc.comp (cj D)) = (J τc).map (fun a => (D.R.t : ℤ) - 1 - a) ∧
    ∀ a ∈ J τc, a < -1 ∨ (D.R.t : ℤ) < a

def CharDual (i : X.Tw) (s : X.Sig i) : Prop :=
  ∀ g g' : Formalism.MainNotions.BlochKatoReduction.Gen.GE N, (∀ x, g' x = X.cc (g (X.cc.symm x))) →
    (Tdual i s g').charpoly = ((((eps0 X i g : (X.O0 i)ˣ) : X.O0 i) ^ D.R.t) • Tmat i s g).charpoly

def FrobDual (i : X.Tw) (s : X.Sig i) : Prop :=
  ∀ P, P ∉ X.S0 i → Formalism.BasicNotions.IsSplitPl D.host P → (∀ P', IsConjPl D.host P P' → P' ∉ X.S0 i) →
    ∀ A : ValuationSubring N.Om, IsPlaceOver (F := D.host.E) A P →
    ∀ g g' : Formalism.MainNotions.BlochKatoReduction.Gen.GE N, IsFrob (F := D.host.E) A (normV P) g → (∀ x, g' x = X.cc (g (X.cc.symm x))) →
    (Tdual i s g').charpoly = ((((eps0 X i g : (X.O0 i)ˣ) : X.O0 i) ^ D.R.t) • Tmat i s g).charpoly

def HkFrob (i : X.Tw) (s : X.Sig i) : Prop :=
  ∀ P, P ∉ X.S0 i → Formalism.BasicNotions.IsSplitPl D.host P → ∀ σ : Formalism.MainNotions.BlochKatoReduction.Gen.GE N, IsFrob (F := D.host.E) (N.plOm.1 P) (normV P) σ⁻¹ →
    ∀ k, k ≤ D.R.r → (-1 : X.O i) ^ k * ((normV P : ℕ) : X.O i) ^ (k * (k - 1) / 2) * X.hEig i s k P =
      algebraMap (X.O0 i) (X.O i)
        ((((((eps0 X i σ : (X.O0 i)ˣ) : X.O0 i) ^ D.R.t) • Tmat i s σ).charpolyRev).coeff k)


def HkSat (A : NAut N) (i : X.Tw) (s : X.Sig i) (ι : FractionRing (X.O0 i) →+* ℂ) (π : A.CG D.R.r) : Prop :=
  ∀ P, P ∉ X.S0 i → Formalism.BasicNotions.IsSplitPl D.host P → ∀ k, k ≤ D.R.r → ∃ h : X.O0 i,
    X.hEig i s k P = algebraMap (X.O0 i) (X.O i) h ∧
    rd i ι h = ((normV P : ℕ) : ℂ) ^ (((k : ℂ) * ((D.R.r : ℂ) - k)) / 2) *
      ((A.frobEig (A.locG π P)).map fun a => a⁻¹ * ((normV P : ℕ) : ℂ) ^ (-((D.R.r : ℂ) + D.R.t) / 2)).esymm k

structure RowFacts (A : NAut N) (i : X.Tw) (π₁ π : A.CG D.R.r) : Prop where
  unr₁ : ∀ w, (∀ k, w ∉ placesOver D.host.E (D.host.g k)) → A.unr (A.locG π₁ w)
  mono₁ : ∀ w, A.mono0 (A.locG π₁ w)
  unr : ∀ w, (∀ k, w ∉ placesOver D.host.E (D.host.g k)) → w ∉ X.pD i → A.unr (A.locG π w)
  mono : ∀ w, A.mono0 (A.locG π w)
  csd : A.csd π
  ralg : A.ralg π
  anti : ∀ τc, A.infG π (τc.comp (cj D)) = (A.infG π τc).map fun z => -z
  window : ∀ τc, ∀ z ∈ A.infG π τc, ∀ a : ℤ, (a : ℂ) = -z + ((D.R.t : ℂ) - 1) / 2 → a < -1 ∨ (D.R.t : ℤ) < a

end GlobalTheory.TripleGal

end
end

