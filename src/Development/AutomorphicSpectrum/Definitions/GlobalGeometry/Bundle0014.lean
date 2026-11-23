module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsEigFrames
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle0004
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0013
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0012
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0010
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0011
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.HasBaseDegreeSetting

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUniqueLeftBasisCoordsAdicCompletion
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar.Cusp

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

def FibreLatVec {X : Scheme.{0}} (t : SAB H X) (z : Sp ℂ ⟶ X) {g : ℕ} {Λ : Type} [AddCommGroup Λ] [Module (𝓞 E) Λ]
    (R : RiemLat E g Λ) {A₀ : Type} (x : A₀ → Fin g → ℂ) (v : A₀ → (epsAt z ⟶ t.G)) : Prop :=
  ∃ (A : Over (Sp ℂ)) (_ : GrpObj A) (φ : A.left ⟶ t.G.left) (u : HolUnif A (t.PP.L.pull φ) g) (χ : u.Λ → ℂ),
    IsGrpPullback A t.G z φ ∧ u.IsAH R.Hm χ ∧
    (∀ a p, (u.ex (R.B a p)).left ≫ φ = (u.ex p).left ≫ φ ≫ (t.act.act a).left) ∧
    Function.Injective R.P ∧ (∀ p, p ∈ u.Λ ↔ p ∈ Set.range R.P) ∧
    ∀ i, ∃ v' : epsR ℂ ⟶ A, v'.left ≫ φ = (v i).left ∧ u.IsDiff (x i) v'

def FibreLat {X : Scheme.{0}} (t : SAB H X) (z : Sp ℂ ⟶ X) {g : ℕ} {Λ : Type} [AddCommGroup Λ] [Module (𝓞 E) Λ]
    (R : RiemLat E g Λ) : Prop :=
  FibreLatVec t z R (A₀ := Empty) (fun i => i.elim) fun i => i.elim

def AbPart.IsCochars {S : Scheme.{0}} {t : SAB H S} {K : Type} [Field K] {z : Sp K ⟶ S} (P : AbPart t z) {V : Type}
    [AddCommGroup V] [Module K V] (MV : LieModel P.tK.G (𝟙 (Sp K)) V) (I : AddSubgroup V) : Prop :=
  letI := P.τ.addCommGroup
  ∃ MT : LieModel (splitTorus (Sp K) P.τ.X) (𝟙 _) (P.τ.X →+ K), IsCocharLie MT ∧
    ∀ x, x ∈ I ↔ ∃ δ : P.τ.X →+ ℤ, MV.pt x = MT.pt ((Int.castAddHom K).comp δ) ≫ P.τ.i

variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

namespace HodgeCpt

variable {Y : Model Xo c β} {S : Finset ℕ} {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type}
  {y : (Σ k, J k) → Ω} (𝔐 : HodgeCpt Y S y)

def LabVal {R : Type} [CommRing R] [IsLocalRing R] (z : Sp R ⟶ 𝔐.X) {A₀ : Type} (lab : A₀ → CMType H ⊕ CMType H)
    (σ : A₀ → (𝓞 E →+* R)) : Prop :=
  ∀ i a, ValAt 𝔐.ξ z (𝔐.emb (lab i) a) (σ i a)

def IsCuspWeight (sm : CMType H → CMType H ⊕ CMType H) (U : ((Σ k, J k) → ℂ) → ℝ) : Prop :=
  ∀ (z : Sp ℂ ⟶ 𝔐.X) w, CoordsAt 𝔐.ξ y z w → 𝔐.Interior z →
    ∃ (g : ℕ) (Λ : Type) (_ : AddCommGroup Λ) (_ : Module (𝓞 E) Λ) (R : RiemLat E g Λ) (σ : CMType H → (𝓞 E →+* ℂ)),
      FibreLat 𝔐.t z R ∧ 𝔐.LabVal z sm σ ∧ U w = R.cuspW σ

def GeoPhi (sm : CMType H → CMType H ⊕ CMType H) (z : Sp ℂ ⟶ 𝔐.X) {m : ℕ} (b : CMType H → Fin m → 𝔐.Li) (ν : ℝ) : Prop :=
  ∃ (P : AbPart 𝔐.t z) (V : Type) (_ : AddCommGroup V) (_ : Module ℂ V) (MV : LieModel P.tK.G (𝟙 (Sp ℂ)) V)
    (ρ : 𝓞 E →+* Module.End ℂ V) (I : AddSubgroup V) (hb : V → V → ℂ) (σ : CMType H → (𝓞 E →+* ℂ))
    (bz : CMType H → Fin m → V),
    MV.IsActOf P.tK.act.act ρ ∧ P.IsCochars MV I ∧ 𝔐.LabVal z sm σ ∧
    (∀ x x', HodgeIP P.tB.G P.tB.PP.L (𝟙 _) (MV.pt x ≫ P.τ.q ≫ P.e.hom) (MV.pt x' ≫ P.τ.q ≫ P.e.hom) (hb x x')) ∧
    (∀ τ k, ∃ v : epsAt z ⟶ 𝔐.t.G, 𝔐.M.ValAt z (b τ k) v ∧ (MV.pt (bz τ k)).left ≫ P.m.φ = v.left) ∧
    PhiNormSq ρ hb I (4 * Real.pi)⁻¹ σ bz ν

def VS (S' : Finset ℕ) (s : CMType H ⊕ CMType H) : Lat 𝔐.ξ 𝔐.Li := Lat.patch S' (𝔐.dR s) fun p => 𝔐.HT p s

def withS (S' : Finset ℕ) (hp : ∀ p ∈ S', p.Prime) (hR : ∀ p ∈ S', 4 ≤ 𝔐.R p)
    (ht : ∀ p ∈ S', FullTorsion 𝔐.t.G 𝔐.ξ (p ^ 𝔐.R p)) (hvb : ∀ s, (𝔐.VS S' s).IsVB (labelRk D s) (𝔐.Vgen s)) :
    HodgeCpt Y S' y :=
  { 𝔐 with S_prime := hp, R_ge := hR, tors := ht, vb := hvb }

variable {L : Type} [Field L] [NumberField L] {V : Type} [AddCommGroup V] [Module L V] [Module (𝓞 L) V]

def FibLat (Vl : Lat 𝔐.ξ 𝔐.Li) (z : Sp (𝓞 L) ⟶ 𝔐.X) (P : AbPart 𝔐.t (spMap (algebraMap (𝓞 L) L) ≫ z))
    (MV : LieModel P.tK.G (𝟙 (Sp L)) V) : Submodule (𝓞 L) V :=
  ⨅ 𝔭 : PrimeSpectrum (𝓞 L), Submodule.span (𝓞 L) {x | ∃ s ∉ 𝔭.asIdeal, s • x ∈ Submodule.span (𝓞 L)
    {x' | ∃ e ∈ Vl ⟨z 𝔭, 𝔐.all _⟩, ∃ v : epsAt (spMap (algebraMap (𝓞 L) L) ≫ z) ⟶ 𝔐.t.G,
      𝔐.M.ValAt (spMap (algebraMap (𝓞 L) L) ≫ z) e v ∧ (MV.pt x').left ≫ P.m.φ = v.left}}

def IsLinPtOf [IsScalarTower (𝓞 L) L V] (z : Sp (𝓞 L) ⟶ 𝔐.X) (P : AbPart 𝔐.t (spMap (algebraMap (𝓞 L) L) ≫ z))
    (MV : LieModel P.tK.G (𝟙 (Sp L)) V) (A : LinPt E L (CMType H) V) : Prop :=
  MV.IsActOf P.tK.act.act A.ρ ∧ 𝔐.LabVal (spMap (algebraMap (𝓞 L) L) ≫ z) id A.σ ∧
    (∀ x, x ∈ A.Λ ↔ ∃ v : epsAt z ⟶ 𝔐.t.G, IsTanAt 𝔐.t.G z v ∧
      (MV.pt x).left ≫ P.m.φ = spMap (dualMap (algebraMap (𝓞 L) L)) ≫ v.left) ∧
    P.IsCochars MV A.I ∧ IsPrincipal P.tB ∧
    ∃ (t' : SAB H (Sp (𝓞 L))) (m' : SABMap P.tB t' (spMap (algebraMap (𝓞 L) L)))
      (MB : LieModel t'.G (𝟙 _) A.Bq.carrier), IsFibre (HodgeIP t'.G t'.PP.L) (𝟙 _) A.Bq MB ∧
      ∀ x : A.Λ, ((MV.pt x ≫ P.τ.q ≫ P.e.hom).left ≫ m'.φ = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap (𝓞 L) L)) ≫ (MB.pt (A.f x)).left)

end HodgeCpt

variable {II : IntersectionSystem} {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {Ω : Type} [Field Ω]
  [Algebra ℚ Ω] {W : CMType H → Type} [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] {Y : Model Xo c β}
  {S₀ : Finset ℕ} {Dc : ComponentData II (CMType H) K J Ω W} {Hd : HodgeData Dc} (Or : CptOrigin Y S₀ Dc Hd)

def CptOrigin.IsSmallPart {w : (Σ k, J k) → ℂ} (d : MuFrameAt Hd w) (s : CMType H → Fin (Dc.N - Dc.j) → Or.𝔐.Li) : Prop :=
  ∀ τ k, s τ k ∈ Or.𝔐.Vgen (Or.sm τ) ∧ Or.i τ (d.b τ (tailIdx Dc.j_le_N k)) - s τ k ∈ Or.𝔐.Vgen (Or.bg τ)

def CptOrigin.PhiWeight (z : Sp ℂ ⟶ Or.𝔐.X) (w : (Σ k, J k) → ℂ) (x : ℝ) : Prop :=
  ∃ (d : MuFrameAt Hd w) (s : CMType H → Fin (Dc.N - Dc.j) → Or.𝔐.Li) (ν : ℝ), Or.IsSmallPart d s ∧
    Or.𝔐.GeoPhi Or.sm z s ν ∧ 0 < ν ∧
    x = Real.log (‖valAt Dc.y d.u w‖ * ∏ k, ‖w ⟨k, d.c k⟩‖ ^ Hd.aMu k) + Real.log ν / 2

def CptOrigin.Good : Prop := (∀ p ∈ S₀, HT.HTFree Or.𝔐 p) ∧ ∀ p ∈ Dc.S, HT.HTFree Or.𝔐 p

end GlobalTheory.CompanionTheory.Ar
end
end

-- bundled from Development.AutomorphicSpectrum.Definitions.GlobalGeometry.HasBaseDegreeSettingStrict
section
namespace GlobalTheory.CompanionTheory.Ar.Top

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree
open GroundTheory.Heights₂.Heights.LowerBoundFree

def StokesAt {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ]
    [DecidableEq Ψ] {Ω : Type} [Field Ω] [Algebra ℚ Ω] {E : Ψ → Type} [∀ τ, AddCommGroup (E τ)] [∀ τ, Module Ω (E τ)]
    {D : ComponentData II Ψ K ι Ω E} {O Lt : Type} [CommRing O] [AddCommGroup Lt] [Module O Lt]
    (X : ComponentSetting D O Lt) (B : ℕ) : Prop :=
  ∀ a : ℝ, StokesLimit.Hyp X B a →
    ((D.n + 1 : ℕ) : ℝ) * (a - meanU X.H X.Cd / 2) * degMu X.H ≤ arLim X.H X.S B

def RootTower.HasBaseDegreeSettingStrict {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ} (T : RootTower Ψ N)
    (II : IntersectionSystem) (Ch Cu rd Lval : ℝ) (B : ℕ) (c : T.Comp) : Prop :=
  ∃ (K : Type) (_ : Fintype K) (ι : K → Type) (_ : ∀ k, Fintype (ι k)) (Ω : Type) (_ : Field Ω) (_ : Algebra ℚ Ω)
    (E : Ψ → Type) (_ : ∀ τ, AddCommGroup (E τ)) (_ : ∀ τ, Module Ω (E τ)) (D : ComponentData II Ψ K ι Ω E)
    (O Lt : Type) (_ : CommRing O) (_ : AddCommGroup Lt) (_ : Module O Lt) (X : ComponentSetting D O Lt),
    D.N = N ∧ D.j = T.j ∧ X.rd = rd ∧ X.Lval = Lval ∧
    CuspBundlePos X ∧ MUConjInvariant X ∧ HtInterior Ch X ∧ HtBoundary Ch X ∧ CuspMean Cu X ∧ 0 < degMu X.H ∧
    ArLimExists X.H X.S B ∧ StokesAt X B ∧
    T.PPc II B c (testPoly T.j) = slX X B * (((dimX Ψ N T.j : ℝ) + 1) * (T.vol c * testDeg Ψ N T.j))

end GlobalTheory.CompanionTheory.Ar.Top
end

