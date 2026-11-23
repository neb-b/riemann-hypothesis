module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0066
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0010
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.NumberField
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatDegree
public import Mathlib
public import Development.AutomorphicSpectrum.Statements.TowerExistence.GoodTowerExistsX
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0003
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0002
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.HodgeComparisonCompatibility
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.CmpSt
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.LocalAtPlaces
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0006
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0106
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0036
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.HasMultiplier
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.HeckeSectionsIsotropicCommutatorPairingPower
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.TowerOrigin
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.SumFundCoMulSumIic
public import Development.WeilBound.CoreStatements.FlagImmersions.Transport
public import Development.WeilBound.CoreStatements.VolumeEquality.Bundle0002
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0032
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0141
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle0004
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsSheetCover
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsProved
public import GroundTheory.HeightsAndTheta.Heights.CountingLowerBound.Assembly
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0135
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0001

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.FlagImmersions.FibSandwich
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl

namespace RootFieldNumerics.RF

def Tied {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {Xo : Moduli D l}
    {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {S : Finset ℕ} {Ω : Type} [Field Ω]
    {K : Type} [Fintype K] {J : K → Type} {y : (Σ k, J k) → Ω} (𝔐 : HodgeCpt Y S y) {F : Type} [Field F]
    (z : Spec (CommRingCat.of F) ⟶ 𝔐.X) (y₀ : Sp F ⟶ Xo.XF c) (vb : epsAt z ⟶ 𝔐.t.G)
    (v : epsAt (under y₀) ⟶ Xo.univ.t.G) : Prop :=
  ∃ v' : epsAt (y₀ ≫ Y.j) ⟶ Y.t.G, SameVec Y y₀ v v' ∧ vb.left ≫ 𝔐.m.φ = v'.left

def cP (p : ℕ) : ℝ := if p = 2 then 2 else 1 / ((p : ℝ) - 1)

def CptEx : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) [NumberField c.F] (Y : Model Xo c (algebraMap (𝓞 c.F) c.F))
    (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)]
    (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y),
    ∃ (U : Set (Xo.XF c)) (Z : CptOver Y U), IsClopen U ∧ IsIrreducible U ∧ genPt 𝔐.ξ₀ = genPt (Z.ξ₀ ≫ Y.j)

def PeriodOf : Prop :=
  GlobalTheory.CompanionTheory.Ar.Top.Given →
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) [NumberField c.F] (Y : Model Xo c (algebraMap (𝓞 c.F) c.F))
    (U : Set (Xo.XF c)) (Z : CptOver Y U), 1 ≤ D.p → 1 ≤ D.q → IsClopen U → IsIrreducible U → Z.IsGeom →
    ∃ (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty) (i : Fin FU.n),
      IsTypeFn H D.p D.q ty ∧ ∀ y : Sp ℂ ⟶ Xo.XF c, y ≫ pullback.snd _ _ = spMap (algebraMap c.F ℂ) →
        (Set.range y ⊆ U ↔ ∃ P, IsPeriod (FU.Di i) ty P ∧ under y = FU.u i P)

def SmoothLine : Prop :=
  ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Fintype K] (J : K → Type)
    [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (F' : Type) [Field F'] [NumberField F'] (ψ : F' →+* Ω) (L : Lat ξ Ω)
    (a : K → ℤ) (e₀ c₀ : Ω) (cinf : (F' →+* ℂ) → ℝ) (n : ℕ),
    (∀ q : X, genPt ξ ⤳ q) → (CoordTie ℤ ξ fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → NormalCpt ξ →
    OverInt y ψ → Birational y → IsArithVar (mCoordIdeal y) n → L.IsDegOn Set.univ y a e₀ →
    (∀ p ∈ genFibre ℤ ξ, L.IsGenAt p (c₀ * e₀)) → (∀ σ, 0 < cinf σ) →
    (∀ σ, cinf (ComplexEmbedding.conjugate σ) = cinf σ) →
    ∃ A : HermLine J, A.a = a ∧ IsSmoothHerm A ∧ IsConjInvariantH A ∧
      (∀ (σ : F' →+* ℂ) z (g h : MRing J) (dg dh : K → ℕ), PtOver y ψ σ z → IsMultiHomog g dg → IsMultiHomog h dh →
        (∀ k, (dg k : ℤ) - dh k = A.a k) → aeval y g = c₀ * aeval y h → ‖evC z g‖ = cinf σ * A.h z * ‖evC z h‖) ∧
      ∀ w ∈ mcPts (mCoordIdeal y), ∃ (g h : MRing J) (dg dh : K → ℕ), IsMultiHomog g dg ∧ IsMultiHomog h dh ∧
        (∀ k, (dg k : ℤ) - dh k = a k) ∧ aeval y g = c₀ * aeval y h ∧ evC w h ≠ 0

def PointEx : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) [NumberField c.F] (Y : Model Xo c (algebraMap (𝓞 c.F) c.F))
    (U : Set (Xo.XF c)) (Z : CptOver Y U) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)]
    (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y)
    (F' : Type) [Field F'] [NumberField F'] (ψ : F' →+* Ω) (p : Nat.Primes) (κ' : F' →+* ℂ_[p]),
    genPt 𝔐.ξ₀ = genPt (Z.ξ₀ ≫ Y.j) →
    ∃ (V L : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V) (_ : Field L) (_ : CharZero L)
      (_ : Algebra V L) (_ : IsFractionRing V L) (j : L →+* ℂ_[p]) (ψL : F' →+* L) (z : Spec (CommRingCat.of V) ⟶ 𝔐.X),
      (∀ a : L, ‖j a‖ ≤ 1 ↔ a ∈ (algebraMap V L).range) ∧ j.comp ψL = κ' ∧
      𝔐.Interior (Spec.map (CommRingCat.ofHom (algebraMap V L)) ≫ z) ∧
      (∀ a : F', ValAt 𝔐.ξ (Spec.map (CommRingCat.ofHom (algebraMap V L)) ≫ z) (ψ a) (ψL a)) ∧
      ∀ a : F', ‖κ' a‖ ≤ 1 → ψ a ∈ regAt 𝔐.ξ ⟨centre z, 𝔐.all _⟩

def ValuePhi : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) [NumberField c.F] (Y : Model Xo c (algebraMap (𝓞 c.F) c.F))
    (U : Set (Xo.XF c)) (Z : CptOver Y U) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)]
    (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y)
    (τ : CMType H) (i : Z.Ω →+* Ω) (j : Z.V →+ 𝔐.Li) (a : ⋀[Z.Ω]^D.p Z.V) (b : ⋀[Z.Ω]^D.q Z.V)
    (a' : ⋀[Ω]^D.p 𝔐.Li) (b' : ⋀[Ω]^D.q 𝔐.Li) (φ : FrameFn Xo c) (L : Type) [Field L] [CharZero L] (s : c.F →+* L)
    (z : Spec (CommRingCat.of L) ⟶ 𝔐.X) (bp : Fin D.p → 𝔐.Li) (bq : Fin D.q → 𝔐.Li)
    (vp : Fin D.p → (epsAt z ⟶ 𝔐.t.G)) (vq : Fin D.q → (epsAt z ⟶ 𝔐.t.G)) (α κ : Ω) (u : L),
    CptIn.IsTie Z 𝔐 i j → IsLineFn U τ.1 φ →
    IsLineGenOn (Z.eig τ.1) (Z.eig (ComplexEmbedding.conjugate τ.1)) D.p D.q a b Z.genFib →
    Represents Y U τ.1 Z.M a b φ → CptIn.IsPullWedge i j a a' → CptIn.IsPullWedge i j b b' → 𝔐.Interior z →
    (∀ x : c.F, ValAt 𝔐.ξ z (𝔐.cst x) (s x)) → (𝔐.V (.inl τ)).IsFrameAt bp ⟨centre z, 𝔐.all _⟩ →
    (𝔐.V (.inr τ)).IsFrameAt bq ⟨centre z, 𝔐.all _⟩ → (∀ k, 𝔐.M.ValAt z (bp k) (vp k)) →
    (∀ k, 𝔐.M.ValAt z (bq k) (vq k)) → a' = α • exteriorPower.ιMulti Ω _ bp → b' = κ • exteriorPower.ιMulti Ω _ bq →
    ValAt 𝔐.ξ z (α / κ) u →
    ∃ (y₀ : Sp L ⟶ Xo.XF c) (v : Vecs y₀ D.p) (w : Vecs y₀ D.q), z ≫ 𝔐.f = y₀ ≫ Y.j ∧ IsFramed U τ.1 s y₀ v w ∧
      φ L y₀ v w = u ∧ (∀ k, Tied 𝔐 z y₀ (vp k) (v k)) ∧ ∀ k, Tied 𝔐 z y₀ (vq k) (w k)

def IntFrames : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) [NumberField c.F] (Y : Model Xo c (algebraMap (𝓞 c.F) c.F))
    (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)]
    (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y)
    (V L : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field L] [CharZero L] [Algebra V L]
    [IsFractionRing V L] (z : Spec (CommRingCat.of V) ⟶ 𝔐.X) (y₀ : Sp L ⟶ Xo.XF c),
    (Spec.map (CommRingCat.ofHom (algebraMap V L)) ≫ z) ≫ 𝔐.f = y₀ ≫ Y.j →
    ∃ (T : SAB H (Sp V)) (tK : SAB H (Sp L)) (m : SABMap tK Xo.univ.t (under y₀))
      (m' : SABMap tK T (spMap (algebraMap V L))) (g : ℕ)
      (MC : LieModel 𝔐.t.G (Spec.map (CommRingCat.ofHom (algebraMap V L)) ≫ z) (Fin g → L))
      (MU : LieModel Xo.univ.t.G (under y₀) (Fin g → L)) (ρC : 𝓞 E →+* Module.End L (Fin g → L)),
      MC.IsActOf 𝔐.t.act.act ρC ∧ MU.IsActOf Xo.univ.t.act.act ρC ∧ (∀ e, Tied 𝔐 _ y₀ (MC.pt e) (MU.pt e)) ∧
      (∀ x, x ∈ 𝔐.M.fibAt 𝔐.M.lat z MC ↔ ∀ k, x k ∈ (algebraMap V L).range) ∧
      ∀ (σ : 𝓞 E →+* V) (n : ℕ) (x : Fin n → Fin g → L), LinearIndependent L x →
        Submodule.span V (Set.range x) =
          𝔐.M.fibAt 𝔐.M.lat z MC ⊓ (eigSp ρC ((algebraMap V L).comp σ)).restrictScalars V →
        IsIntFrame m m' ((algebraMap V L).comp σ) (fun k => MU.pt (x k))

def FibSandwich : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) [NumberField c.F] (Y : Model Xo c (algebraMap (𝓞 c.F) c.F))
    (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)]
    (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y)
    (V L : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field L] [CharZero L] [Algebra V L]
    [IsFractionRing V L] (p : Nat.Primes) (j : L →+* ℂ_[p]) (z : Spec (CommRingCat.of V) ⟶ 𝔐.X) (g : ℕ)
    (MC : LieModel 𝔐.t.G (Spec.map (CommRingCat.ofHom (algebraMap V L)) ≫ z) (Fin g → L))
    (ρC : 𝓞 E →+* Module.End L (Fin g → L)) (s : CMType H ⊕ CMType H) (σ : 𝓞 E →+* V)
    (b : Fin (labelRk D s) → 𝔐.Li),
    (∀ a : L, ‖j a‖ ≤ 1 ↔ a ∈ (algebraMap V L).range) → MC.IsActOf 𝔐.t.act.act ρC →
    (∀ a, ValAt 𝔐.ξ z (𝔐.emb s a) (σ a)) → (𝔐.V s).IsFrameAt b ⟨centre z, 𝔐.all _⟩ →
    ∃ x : Fin (labelRk D s) → Fin g → L,
      (∀ k, 𝔐.M.ValAt (Spec.map (CommRingCat.ofHom (algebraMap V L)) ≫ z) (b k) (MC.pt (x k))) ∧
      ((p : ℕ) ∉ S → ¬ ((p : ℕ) : ℤ) ∣ discr E → Submodule.span V (Set.range x) =
        𝔐.M.fibAt 𝔐.M.lat z MC ⊓ (eigSp ρC ((algebraMap V L).comp σ)).restrictScalars V) ∧
      ((p : ℕ) ∈ S → HT.HTFree 𝔐 p → ∀ (κ : Ω) (κz : V), HT.Sandwich 𝔐 p κ → ValAt 𝔐.ξ z κ κz →
        𝔐.M.fibAt 𝔐.M.lat z MC ⊓ (eigSp ρC ((algebraMap V L).comp σ)).restrictScalars V ≤
          Submodule.span V (Set.range x) ∧
        ∀ d : 𝓞 E, (s.isLeft → d ∈ differentIdeal ℤ (𝓞 E)) → ∀ w ∈ Submodule.span V (Set.range x),
          (κz * σ d) • w ∈ 𝔐.M.fibAt 𝔐.M.lat z MC ⊓ (eigSp ρC ((algebraMap V L).comp σ)).restrictScalars V)

def LocalCmp : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) [NumberField c.F] (Y : Model Xo c (algebraMap (𝓞 c.F) c.F))
    (U : Set (Xo.XF c)) (Z : CptOver Y U) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)]
    (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y)
    (Fl : 𝔐.Flag) (τ : CMType H) (i : Z.Ω →+* Ω) (j : Z.V →+ 𝔐.Li) (a : ⋀[Z.Ω]^D.p Z.V) (b : ⋀[Z.Ω]^D.q Z.V)
    (a' : ⋀[Ω]^D.p 𝔐.Li) (b' : ⋀[Ω]^D.q 𝔐.Li) (d₁ d₂ : Ω) (φ : FrameFn Xo c)
    (F' : Type) [Field F'] [NumberField F'] (ι : c.F →+* F') (ψ : F' →+* Ω) (p : Nat.Primes) (κ' : F' →+* ℂ_[p])
    (π : F') (m : ℕ) (k : ℤ) (t : ℝ),
    genPt 𝔐.ξ₀ = genPt (Z.ξ₀ ≫ Y.j) → CptIn.IsTie Z 𝔐 i j → IsLineFn U τ.1 φ →
    IsLineGenOn (Z.eig τ.1) (Z.eig (ComplexEmbedding.conjugate τ.1)) D.p D.q a b Z.genFib →
    Represents Y U τ.1 Z.M a b φ → CptIn.IsPullWedge i j a a' → CptIn.IsPullWedge i j b b' → d₁ ≠ 0 → d₂ ≠ 0 →
    a' = d₁ • (exteriorPower.ιMulti Ω _ (Fl.b (.inl τ))) → b' = d₂ • (exteriorPower.ιMulti Ω _ (Fl.b (.inr τ))) →
    a' ≠ 0 → b' ≠ 0 → ψ.comp ι = 𝔐.cst → π ≠ 0 → 0 < m →
    (∀ x : Cpt 𝔐.ξ, (∀ u : F', ‖κ' u‖ ≤ 1 → ψ u ∈ regAt 𝔐.ξ x) →
      OrderAt (lineLat (𝔐.V (.inl τ)) (𝔐.V (.inr τ)) (labelRk D (.inl τ)) (labelRk D (.inr τ))
        (exteriorPower.ιMulti Ω _ (Fl.b (.inl τ))) (exteriorPower.ιMulti Ω _ (Fl.b (.inr τ)))) (d₁ / d₂) (ψ π) m k x) →
    HasFinNorm U τ.1 φ p (κ'.comp ι) t →
    ((p : ℕ) ∉ S → ¬ ((p : ℕ) : ℤ) ∣ discr E → (k : ℝ) / m * Real.log ‖κ' π‖ = t) ∧
    ((p : ℕ) ∈ S → HT.HTFree 𝔐 p → ∀ κ : Ω, HT.IsCp p κ → HT.Sandwich 𝔐 p κ →
      ∀ d ∈ differentIdeal ℤ (𝓞 E), d ≠ 0 → |(k : ℝ) / m * Real.log ‖κ' π‖ - t| ≤
        ((D.p + D.q : ℕ) : ℝ) * (cP p * Real.log (p : ℕ) - Real.log ‖κ' (ι (tauIn c τ.1 d))‖))

def ChiEx : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [NeZero H.d], ∃ χ : DirichletCharacter ℂ H.d,
    GlobalTheory.IsKroneckerChar χ ∧ (GlobalTheory.CM.logOm E χ).re =
      Real.eulerMascheroniConstant + Real.log (2 * Real.pi) - Real.log (hostRd E) - hostLval H

def Numerics : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (p q : ℕ) (F F' : Type) [Field F] [NumberField F]
    [Field F'] [NumberField F'] (ι : F →+* F') (σ : 𝓞 E →+* F) (N : LogNorms F)
    (r : HeightOneSpectrum (𝓞 F') →₀ ℚ) (bad : Finset ℕ), Function.Injective σ → 2 ∈ bad → (∀ ℓ ∈ bad, ℓ.Prime) →
    N.IsAdelic → N.deg = ((p : ℝ) - q) / 2 *
      (Real.eulerMascheroniConstant + Real.log (2 * Real.pi) - Real.log (hostRd E) - hostLval H) →
    (∀ (ℓ : Nat.Primes) (κ' : F' →+* ℂ_[ℓ]) (v : HeightOneSpectrum (𝓞 F')) (π : F'),
      (∀ a : F', v.valuation F' a ≤ 1 ↔ ‖κ' a‖ ≤ 1) → v.valuation F' π = WithZero.exp (-1 : ℤ) →
      ((ℓ : ℕ) ∉ bad → (r v : ℝ) * Real.log ‖κ' π‖ = N.fin ℓ (κ'.comp ι)) ∧
      ((ℓ : ℕ) ∈ bad → ∀ d ∈ differentIdeal ℤ (𝓞 E), d ≠ 0 → |(r v : ℝ) * Real.log ‖κ' π‖ - N.fin ℓ (κ'.comp ι)| ≤
        ((p + q : ℕ) : ℝ) * (cP ℓ * Real.log (ℓ : ℕ) - Real.log ‖κ' (ι (σ d))‖))) →
    NearRecord (p + q) bad (hostRd E) (hostLval H)
      (((r.sum fun v x => (x : ℝ) * Real.log (Ideal.absNorm v.asIdeal)) - ∑ s : F' →+* ℂ, N.inf (s.comp ι)) /
        (Module.finrank ℚ F' : ℝ))

end RootFieldNumerics.RF
end
end

-- bundled from Development.WeilBound.CoreStatements.FlagImmersions.GlobalModelTowerBounds
section
open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.LowerBoundFree (ComponentData ComponentSetting degMu ArLimExists slX)

namespace RootFieldNumerics

theorem global_model_tower_bounds : Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (l : Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) [DecidableEq (CMType H)] (T : RootTower (CMType H) (D.p + D.q)) (o : GoodOrigin Y T) (II : IntersectionSystem), IsGlobal Xo l c Y → o.Extra → IsFullIntersectionSystem II → 1 ≤ D.p → 1 ≤ D.q → ∀ B a, (T.M B a).EffDiff T.nu := by
  intro _ E _ _ _ _ H D Xo l c Y _ T o II _ _ _ _ _ B a
  obtain ⟨n₀, N₀, hn, -, hne, hmem⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Small.OriginEps.section_on_model E H D l (Xo l) c _ _ Y (o.S B) (T.M B a) (o.Sys a) (o.Fx a)
    (o.Or B a) T.nu (o.nu_eq a)
  refine ⟨(o.Fx a).kA * (o.Fx a).q', n₀, Nat.mul_pos ?_ (o.Fx a).q'_pos, hn, _, hne, hmem⟩
  rw [← (o.Or B a).kA_eq]
  exact (T.M B a).kA_pos

end RootFieldNumerics
end

-- bundled from Development.WeilBound.CoreStatements.FlagImmersions.IpZeroRight
section
open NumberField Matrix GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

noncomputable section

namespace RootFieldNumerics.PC

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {g : ℕ} {Λ : Type} [AddCommGroup Λ] [Module (𝓞 E) Λ]

theorem mem_eig {V : Type} [AddCommGroup V] [Module ℂ V] {ρ : 𝓞 E →+* Module.End ℂ V} {s : 𝓞 E →+* ℂ} {x : V} :
    x ∈ eigSp ρ s ↔ ∀ a, ρ a x = s a • x := by
  simp [eigSp, Submodule.mem_iInf, sub_eq_zero]

theorem ip_sum (R : RiemLat E g Λ) {ι κ : Type} [Fintype ι] [Fintype κ] (a : ι → ℂ) (c : κ → ℂ) (u : ι → Fin g → ℂ)
    (w : κ → Fin g → ℂ) :
    R.ip (∑ k, a k • u k) (∑ l, c l • w l) = ∑ k, ∑ l, star (a k) * c l * R.ip (u k) (w l) := by
  simp only [RiemLat.ip, star_sum, star_smul, mulVec_sum, mulVec_smul, sum_dotProduct, dotProduct_sum, smul_dotProduct,
    dotProduct_smul, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem ip_conj (R : RiemLat E g Λ) (x y : Fin g → ℂ) : (starRingEnd ℂ) (R.ip x y) = R.ip y x :=
  conj_hermForm R.herm y x

theorem ip_zero_left (R : RiemLat E g Λ) (y : Fin g → ℂ) : R.ip 0 y = 0 := by simp [RiemLat.ip]

theorem ip_zero_right (R : RiemLat E g Λ) (y : Fin g → ℂ) : R.ip y 0 = 0 := by simp [RiemLat.ip]

theorem exists_onb (R : RiemLat E g Λ) (W : Submodule ℂ (Fin g → ℂ)) {m : ℕ} (hm : Module.finrank ℂ W = m) :
    ∃ e : Fin m → Fin g → ℂ, (∀ i, e i ∈ W) ∧ (∀ i j, R.ip (e i) (e j) = if i = j then 1 else 0) ∧
      ∀ z ∈ W, ∃ α : Fin m → ℂ, z = ∑ i, α i • e i := by
  classical
  obtain ⟨c, hc⟩ := GlobalTheory.T.hermitian_restriction_orthonormal_coords g m R.Hm R.herm R.pos W hm
  have hinj : Function.Injective (c.comp W.subtype) := by
    refine (injective_iff_map_eq_zero _).2 fun z hz => ?_
    by_contra h0
    have h1 := R.pos z fun h => h0 (Subtype.ext h)
    have hz' : c z = 0 := hz
    rw [hc z z.2 z z.2, hz'] at h1
    simp at h1
  have hsur : Function.Surjective (c.comp W.subtype) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simp [hm])).1 hinj
  choose e he using fun i => hsur (Pi.single i 1)
  refine ⟨fun i => e i, fun i => (e i).2, fun i j => ?_, fun z hz => ⟨c z, ?_⟩⟩
  · have h1 : c (e i) = Pi.single i 1 := he i
    have h2 : c (e j) = Pi.single j 1 := he j
    rw [RiemLat.ip, hc _ (e i).2 _ (e j).2, h1, h2]
    simp [Pi.single_apply, eq_comm]
  · have h : (⟨z, hz⟩ : W) = ∑ i, c z i • e i := by
      apply hinj
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      simp only [map_smul, he]
      ext k
      simp [Pi.single_apply]
    simpa using congrArg Subtype.val h

section Cx

variable (b : Module.Basis (Fin (2 * g)) ℤ Λ)

def Pc (R : RiemLat E g Λ) : (Fin (2 * g) → ℂ) →ₗ[ℂ] (Fin g → ℂ) := Fintype.linearCombination ℂ fun k => R.P (b k)

theorem Pc_apply (R : RiemLat E g Λ) (ξ : Fin (2 * g) → ℂ) : Pc b R ξ = ∑ k, ξ k • R.P (b k) := rfl

def io (a : Λ) : Fin (2 * g) → ℂ := fun k => (b.repr a k : ℂ)

theorem star_io (a : Λ) : star (io b a) = io b a := by
  ext k
  simp [io]

theorem Pc_io (R : RiemLat E g Λ) (a : Λ) : Pc b R (io b a) = R.P a := by
  conv_rhs => rw [← b.sum_repr a]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Pc_apply, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_zsmul, io, Int.cast_smul_eq_zsmul]

def act (a : 𝓞 E) (ξ : Fin (2 * g) → ℂ) : Fin (2 * g) → ℂ := ∑ k, ξ k • io b (a • b k)

theorem Pc_act (R : RiemLat E g Λ) (a : 𝓞 E) (ξ : Fin (2 * g) → ℂ) : Pc b R (act b a ξ) = R.B a (Pc b R ξ) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [act, map_sum, Pc_apply b R ξ, map_sum]
  simp only [map_smul, Pc_io, R.act]

theorem star_act (a : 𝓞 E) (ξ : Fin (2 * g) → ℂ) : star (act b a ξ) = act b a (star ξ) := by
  simp only [act, star_sum, star_smul, star_io, Pi.star_apply]

theorem exists_real (R : RiemLat E g Λ) (e : Fin g → ℂ) : ∃ ξ, star ξ = ξ ∧ Pc b R ξ = e := by
  have he : e ∈ Submodule.span ℝ (Set.range R.P) := by rw [SheetDecomposition.Riem.span_top]; trivial
  induction he using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, rfl⟩ := hx
    exact ⟨_, star_io b a, Pc_io b R a⟩
  | zero => exact ⟨0, star_zero _, map_zero _⟩
  | add x y _ _ hx hy =>
    obtain ⟨ξ, h1, h2⟩ := hx
    obtain ⟨ξ', h1', h2'⟩ := hy
    exact ⟨ξ + ξ', by rw [star_add, h1, h1'], by rw [map_add (f := _), h2, h2']⟩
  | smul r x _ hx =>
    obtain ⟨ξ, h1, h2⟩ := hx
    exact ⟨(r : ℂ) • ξ, by rw [star_smul, h1]; simp, by rw [map_smul, h2]; rfl⟩

theorem exists_pair (R : RiemLat E g Λ) (e e' : Fin g → ℂ) : ∃ η, Pc b R η = e ∧ Pc b R (star η) = e' := by
  obtain ⟨ξ, h1, h2⟩ := exists_real b R ((2⁻¹ : ℂ) • (e + e'))
  obtain ⟨ξ', h1', h2'⟩ := exists_real b R ((2⁻¹ * Complex.I : ℂ) • (e' - e))
  refine ⟨ξ + Complex.I • ξ', ?_, ?_⟩
  · rw [map_add (f := _), map_smul, h2, h2', smul_smul]
    ext k
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    linear_combination (2⁻¹ * (e' k - e k)) * Complex.I_mul_I
  · rw [star_add, star_smul, h1, h1', map_add (f := _), map_smul, h2, h2', smul_smul]
    ext k
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Complex.star_def, Complex.conj_I]
    linear_combination (-2⁻¹ * (e' k - e k)) * Complex.I_mul_I

theorem ext_pair (R : RiemLat E g Λ) {η η' : Fin (2 * g) → ℂ} (h : Pc b R η = Pc b R η')
    (h' : Pc b R (star η) = Pc b R (star η')) : η = η' := by
  let Θ : (Fin (2 * g) → ℂ) →ₗ[ℂ] (Fin g → ℂ) × (Fin g → ℂ) :=
    (Pc b R).prod (Fintype.linearCombination ℂ fun k => star (R.P (b k)))
  have hΘ : ∀ ξ, Θ ξ = (Pc b R ξ, star (Pc b R (star ξ))) := fun ξ => by
    refine Prod.ext rfl ?_
    show ∑ k, ξ k • star (R.P (b k)) = star (∑ k, star ξ k • R.P (b k))
    simp only [star_sum, star_smul, Pi.star_apply, star_star]
  have hs : Function.Surjective Θ := fun ⟨e, e'⟩ => by
    obtain ⟨η, h1, h2⟩ := exists_pair b R e (star e')
    exact ⟨η, by rw [hΘ, h1, h2, star_star]⟩
  refine (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simp [two_mul])).2 hs ?_
  rw [hΘ, hΘ, h, h']

theorem psi_eq (R : RiemLat E g Λ) (ξ ξ' : Fin (2 * g) → ℂ) :
    R.ip (Pc b R ξ) (Pc b R ξ') - R.ip (Pc b R (star ξ')) (Pc b R (star ξ)) =
      ∑ k, ∑ l, star (ξ k) * ξ' l * (2 * (R.form (b l) (b k) : ℂ) * Complex.I) := by
  simp only [Pc_apply, ip_sum]
  rw [Finset.sum_comm (f := fun k l => star (star ξ' k) * star ξ l * R.ip (R.P (b k)) (R.P (b l))), ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  have h := Complex.sub_conj (R.ip (R.P (b k)) (R.P (b l)))
  have h2 : (R.ip (R.P (b k)) (R.P (b l))).im = R.form (b l) (b k) := R.im _ _
  rw [ip_conj, h2] at h
  push_cast at h
  rw [← h, Pi.star_apply, Pi.star_apply, star_star]
  ring

end Cx

theorem mem_of_eig {Ψ : Type} [Fintype Ψ] (B : 𝓞 E →+* Module.End ℂ (Fin g → ℂ)) {σ : Ψ → (𝓞 E →+* ℂ)} (hσ : IsCMFam σ)
    (W : Submodule ℂ (Fin g → ℂ)) (h : ∀ τ, eigSp B (σ τ) ≤ W) (h' : ∀ τ, eigSp B ((starRingEnd ℂ).comp (σ τ)) ≤ W) :
    W = ⊤ := by
  refine top_unique fun z _ => ?_
  obtain ⟨y, hy, rfl⟩ := SheetDecomposition.Riem.exists_decomp B z
  refine W.sum_mem fun s _ => ?_
  by_cases e : ∃ τ, σ τ = s.comp (algebraMap (𝓞 E) E)
  · obtain ⟨τ, e⟩ := e
    exact h τ (e ▸ hy s)
  · obtain ⟨τ, e'⟩ := not_not.1 (mt (hσ.2 _).2 e)
    refine h' τ ?_
    have : (starRingEnd ℂ).comp (σ τ) = s.comp (algebraMap (𝓞 E) E) := by
      rw [e']
      ext a
      simp
    exact this ▸ hy s

end RootFieldNumerics.PC
end
end

-- bundled from Development.WeilBound.CoreStatements.FlagImmersions.RootModelNefFibresBase
section
open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.LowerBoundFree (ComponentData ComponentSetting degMu ArLimExists slX)

namespace RootFieldNumerics

theorem geoNum_zero_nonneg' {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] (W : Ideal (MRing ι))
    (a : Fin 0 → K → ℤ) : 0 ≤ geoNum 0 W a := by
  rw [geoNum]
  split_ifs
  · exact Int.natCast_nonneg _
  · exact le_rfl

theorem geoNum_one_nonneg' {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] (W : Ideal (MRing ι))
    (a : K → ℤ) (ha : ∀ k, 0 ≤ a k) : 0 ≤ geoNum 1 W (fun _ => a) := by
  rw [geoNum]
  split_ifs
  · refine Finset.sum_nonneg fun k _ => mul_nonneg (ha k) ?_
    refine finsum_nonneg fun V => finsum_nonneg fun _ => ?_
    exact mul_nonneg (Int.natCast_nonneg _) (geoNum_zero_nonneg' _ _)
  · exact le_rfl

end RootFieldNumerics

theorem RootFieldNumerics.root_model_nef_fibres_base : ∀ (Ψ : Type) [Fintype Ψ] (N : ℕ) (M : RootModel Ψ N), (∀ k, 0 ≤ M.A.a k) → M.NefFib 0 1 := by
  intro Ψ _ N M hA p _ W _
  unfold GlobalTheory.CompanionTheory.Ar.Top.RootModel.curveDeg
  refine Finset.sum_nonneg fun j _ => ?_
  rcases j with _ | r
  · have hk : (0:ℝ) < M.kA := by exact_mod_cast M.kA_pos
    have hg := RootFieldNumerics.geoNum_one_nonneg' W M.A.a hA
    simp only [GlobalTheory.CompanionTheory.Ar.Top.RootModel.coef, GlobalTheory.CompanionTheory.Ar.Top.RootModel.line]
    exact mul_nonneg (by positivity) (by exact_mod_cast hg)
  · simp [GlobalTheory.CompanionTheory.Ar.Top.RootModel.coef]
end

