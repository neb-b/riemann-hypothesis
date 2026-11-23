module

public import Mathlib
public import Formalism.SharpRestriction.LevelLetterCocycles.ElementDenominator
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsIterateDerivative
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsAlgebraMapEqRoot
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0007
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0008
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0010
public import Formalism.AdmissibleDesigns.Bundle0001
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0016
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0015
public import Formalism.SharpRestriction.LevelLetterCocycles.BlochKatoPhases
public import Formalism.SharpRestriction.LevelLetterCocycles.IntegralHeckeForms

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
section
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal Matrix
open scoped Formalism.Per

namespace GlobalTheory.BKGal

def IsEps {l : ℕ} [Fact l.Prime] (ε : OCb l) : Prop := ε.untilt = 1 ∧ ∃ δ : OCb l, δ ^ l = ε ∧ δ.untilt ≠ 1

def muOf {l : ℕ} [Fact l.Prime] (x : OCb l) : Ainf l := WittVector.teichmuller l x - 1

section General

variable {l : ℕ} [hl : Fact l.Prime] {a : ℕ} [NeZero a] {e : ℕ} [NeZero e]
  {O K : Type} [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O]
  [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K]
  (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e)
  {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  {G : Type} [Group G] [TopologicalSpace G]


variable (l O) in
def toB : OA l O →ₐ[O] OB l O := (toOB l O).comp (toOCr l O)


variable {t ϖ} in
def IsCrisCmp {P : PhiMod O K l e a ι} {T : LocLat G ℚ_[l] K O} (I : Ident t ϖ P T)
    (jB : (ι → OB l O) ≃ₗ[OB l O] TW (OB l O) T) : Prop :=
  ∀ (c : ι → OA l O) (z : TW (OA l O) T), I.j (inclL t ϖ P c) = TWincl (inclO l O) T z →
    jB (fun i => toB l O (c i)) = TWincl (toB l O) T z

def IsCrisVal (P : PhiMod O K l e a ι) {T : LocLat G ℚ_[l] K O}
    (jB : (ι → OB l O) ≃ₗ[OB l O] TW (OB l O) T) (w : ι → OW l O) (b : TW (OB l O) T) : Prop :=
  ∃ (m : OA l O) (c : ι → OA l O), IsUnit (toB l O m) ∧ inclO l O m • w = inclL t ϖ P c ∧
    toB l O m • b = jB fun i => toB l O (c i)

abbrev actB (s : G →* GQ l) (T : LocLat G ℚ_[l] K O) (g : G) : TW (OB l O) T →ₗ[O] TW (OB l O) T :=
  TWact (galOB O (s g)) T g

def IsCobOf (s : G →* GQ l) (T : LocLat G ℚ_[l] K O) (b : TW (OB l O) T) (c : G → T.V) : Prop :=
  ∀ (g : G) (n : ℕ) (x : ↥T.L.T), (x : T.V) = (l : K) ^ n • c g →
    (1 : OB l O) ⊗ₜ[O] x = (l : O) ^ n • (actB s T g b - b)

variable [TameDescentExponentData K l e a]


variable (K) in
def Covers (h : GQ l) (γ : TameGal K l e a) : Prop :=
  ∀ f f' : ZMod a → A O K, (∀ τ, (f' τ : K⟦X⟧) = ringAct γ (fun σ => (f σ : K⟦X⟧)) τ) →
    galOA O h (ϖ.iTot t K f) = ϖ.iTot t K f'


variable {t ϖ} in
def IsGalDesc (s : G →* GQ l) {P : PhiMod O K l e a ι} {T : LocLat G ℚ_[l] K O} (I : Ident t ϖ P T)
    (Δ : Descent P) : Prop :=
  ∀ (g : G) (γ : TameGal K l e a), Covers K t ϖ (s g) γ → ∀ v v' : ME P, v'.1 = Δ.act γ v.1 →
    I.act (s g) g (toW t ϖ P v) = toW t ϖ P v'

def IsHoriz (s : G →* GQ l) (P : PhiMod O K l e a ι) {T : LocLat G ℚ_[l] K O}
    (jB : (ι → OB l O) ≃ₗ[OB l O] TW (OB l O) T) : Prop :=
  ∀ g : G, s g ∈ GK (ϖ.field a) → ∀ (d : P.D) (h : P.xi d ∈ P.MMl),
    actB s T g (jB (toBcris t ϖ P ⟨P.xi d, h⟩)) = jB (toBcris t ϖ P ⟨P.xi d, h⟩)

structure GalDat (s : G →* GQ l) {η H : ℕ} (D : BKDat O K l e a ι η H) (T : LocLat G ℚ_[l] K O) where

  I : Ident t ϖ D.toPhiMod T

  jB : (ι → OB l O) ≃ₗ[OB l O] TW (OB l O) T
  cmp : IsCrisCmp I jB
  desc : IsGalDesc s I D.desc
  stable : ∀ g : G, ∀ v ∈ LA t ϖ D.toPhiMod, I.act (s g) g v ∈ LA t ϖ D.toPhiMod
  horiz : IsHoriz t ϖ s D.toPhiMod jB

namespace GalDat

variable {t ϖ} {s : G →* GQ l} {η H : ℕ} {D : BKDat O K l e a ι η H} {T : LocLat G ℚ_[l] K O}
  (R : GalDat t ϖ s D T)

def IsPotential (y : Vec K a ι) (b : TW (OB l O) T) : Prop :=
  ∃ (hy : y ∈ ME D.toPhiMod) (m₀ : ι → OW l O) (σ : D.MMl) (b₀ : TW (OB l O) T),
    phiW t ϖ D.toPhiMod m₀ - m₀ = toW t ϖ D.toPhiMod ⟨y, hy⟩ ∧ σ.1 ∈ D.desc.inv ∧ D.conn σ.1 = D.zeta y ∧
    IsCrisVal t ϖ D.toPhiMod R.jB (phiW t ϖ D.toPhiMod m₀) b₀ ∧ b = R.jB (toBcris t ϖ D.toPhiMod σ) - b₀

def ClassOf (y : Vec K a ι) (c : G → T.V) : Prop := ∃ b, R.IsPotential y b ∧ IsCobOf s T b c

end GalDat

end General

section Ql

variable {l : ℕ} [hl : Fact l.Prime]


variable (l) in
abbrev Gl : Type := ↥(GK (Formalism.MainNotions.ElementDenominator.qlExt l))


variable (l) in
abbrev sQ : Gl l →* GQ l := (GK (Formalism.MainNotions.ElementDenominator.qlExt l)).subtype

abbrev QLat (LL : FinExt l) : Type 1 := LocLat (Gl l) ℚ_[l] ↥LL.1 ↥(OL LL)

def inclG (F : FinExt l) : ↥(GK F) →* Gl l :=
  Subgroup.inclusion (GK_le (K := Formalism.MainNotions.ElementDenominator.qlExt l) (K' := F) bot_le)

def resF {LL : FinExt l} (T : QLat LL) (F : FinExt l) : LocLat ↥(GK F) ℚ_[l] ↥LL.1 ↥(OL LL) :=
  resLoc T (inclG F) (continuous_subtype_val.subtype_mk _)

variable {e : ℕ} (a : ℕ) [NeZero a] (ϖ : PiSys l e) (Pl : LocPrime l) {LL : FinExt l}

set_option synthInstance.maxHeartbeats 100000 in
def TameType (T : QLat LL) (Sig : Finset (ZMod e)) : Prop :=
  ∀ g ∈ IK (Formalism.MainNotions.ElementDenominator.qlExt l), ∀ w : ↥LL.1, (w : Om l) * ϖ.seq 0 = (g : GQ l) (ϖ.seq 0) →
    ∀ x ∈ Dcris (Pl.PD (ϖ.field a)) (resF T (ϖ.field a)).ρ,
      Polynomial.aeval (actVB (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.ρ g : Module.End ↥LL.1 (T.V ⊗[ℚ_[l]] Pl.R.B))
        (∏ c ∈ Sig, (Polynomial.X - Polynomial.C (w ^ c.val))) x = 0

structure IsGood (T : QLat LL) (Sig : Finset (ZMod e)) (U : Finset ℤ) : Prop where
  crys : IsCrys (Pl.PD (ϖ.field a)) (resF T (ϖ.field a)).ρ
  type : TameType a ϖ Pl T Sig
  jumps : ∀ τ, JumpsInV (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.ρ τ (U : Set ℤ)

variable [NeZero e] [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a]

structure Pack (η H : ℕ) (T : QLat LL) where

  n : ℕ

  D : BKDat ↥(OL LL) ↥LL.1 l e a (Fin n) η H

  R : GalDat (thetaW a LL) ϖ (sQ l) D T
  isBK : IsBK (T := resF T (ϖ.field a)) (R.I.res (inclG (ϖ.field a)) (continuous_subtype_val.subtype_mk _))

end Ql

end GlobalTheory.BKGal
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWildInertiaCyclotomicElement
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.CoefDuty

def LatInt (D : D7) (M : MtFam D) (Q : Finset (PlE D.host)) (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m)
    (w : D.what₂.places.Pl) : Prop :=
  (∀ y ∈ (D.what₂.MtLat (D.what₂.muTw w) j).gen, y ∈ Set.range (D.what₂.jMt (D.what₂.muTw w) j)) ∧
  ∀ (v : PlE D.host) (k : ℕ) (s : SplitPlace D.host.E) (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)),
    GenAt D (D.what₂.places.resChar w) Q v k → IsConjPl D.host v s.w → IsUnif D.host.E s.v ϖ →
    ∀ y ∈ (D.what₂.MtLat (D.what₂.muTw w) j).gen, ∃ c : D.what₂.Mt (D.what₂.muTw w) j → D.what₂.LL,
      (∀ g, 0 ≤ D.what₂.places.val w (c g)) ∧
      NG.tN (M (D.what₂.muTw w) j h1 h2).J s ϖ k ((M (D.what₂.muTw w) j h1 h2).real y) =
        (M (D.what₂.muTw w) j h1 h2).real (∑ g ∈ (D.what₂.MtLat (D.what₂.muTw w) j).gen, D.what₂.embLL (c g) • g)

section Plain

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

def IsInvForm (a : NG.AlgWt L n) (β : a.W →ₗ⋆[ℂ] a.W →ₗ[ℂ] ℂ) : Prop :=
  (∀ x y, β x y = starRingEnd ℂ (β y x)) ∧ (∀ x, x ≠ 0 → 0 < (β x x).re) ∧
    ∀ (γ : GQ L n) x y, β (a.ρ γ x) (a.ρ γ y) = β x y

def IsBounded (J : Subgroup (GAf L n)) : Prop := ∃ F : Finset (GAf L n), ∀ κ ∈ J, ∃ f ∈ F, f⁻¹ * κ ∈ Umax L n

def IsClassReps (J : Subgroup (GAf L n)) (T : Finset (GAf L n)) : Prop :=
  ∀ g : GAf L n, ∃! t, t ∈ T ∧ ∃ (γ : GQ L n) (κ : GAf L n), κ ∈ J ∧ g = (γ : GAf L n) * t * κ

def classSum (a : NG.AlgWt L n) (β : a.W →ₗ⋆[ℂ] a.W →ₗ[ℂ] ℂ) (J : Subgroup (GAf L n)) (T : Finset (GAf L n))
    (f f' : GAf L n → a.W) : ℂ :=
  ∑ t ∈ T, ((Nat.card {γ : GQ L n // t⁻¹ * (γ : GAf L n) * t ∈ J} : ℕ) : ℂ)⁻¹ * β (f t) (f' t)

def IsPetersson (a : NG.AlgWt L n) (B : (GAf L n → a.W) →ₗ⋆[ℂ] (GAf L n → a.W) →ₗ[ℂ] ℂ) : Prop :=
  ∀ f ∈ NG.AFall L n a.ρ, ∀ f' ∈ NG.AFall L n a.ρ, B f f' = starRingEnd ℂ (B f' f) ∧ (f ≠ 0 → 0 < (B f f).re) ∧
    ∀ h, B (NG.rt L n h f) (NG.rt L n h f') = B f f'

end Plain

def ClassSum {D : D7} {μ : D.what₂.Tup} {j : ℕ} (X : MtReal D μ j) : Prop :=
  IsBounded X.J ∧ ∃ (β : X.wt.W →ₗ⋆[ℂ] X.wt.W →ₗ[ℂ] ℂ) (T : Finset (GAf D.host.E D.R.nV)) (c : ℝ),
    IsInvForm X.wt β ∧ IsClassReps X.J T ∧ 0 < c ∧
    ∀ x y : D.what₂.Mt μ j, inner ℂ x y = (c : ℂ) * classSum X.wt β X.J T (X.real x) (X.real y)

def EigSet {D : D7} {μ : D.what₂.Tup} {j : ℕ} (X : MtReal D μ j) (l : ℕ) (Q : Finset (PlE D.host)) :
    Set (PlE D.host → ℕ → ℂ) :=
  {c | (∀ v k, ¬ GenAt D l Q v k → c v k = 0) ∧ ∃ y : D.what₂.Mt μ j, y ≠ 0 ∧
    ∀ (v : PlE D.host) (k : ℕ) (s : SplitPlace D.host.E) (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)),
      GenAt D l Q v k → IsConjPl D.host v s.w → IsUnif D.host.E s.v ϖ →
      NG.tN X.J s ϖ k (X.real y) = c v k • X.real y}


open Classical in
def ptSys (D : D7) (i : D.nd.Loc) (x : D.nd.X i) : PlE D.host → ℕ → ℂ := fun v k =>
  if GenAt D (D.nd.l i) (D.nd.Q i) v k then iotaOC D i ((D.nd.hT i v k : D.nd.X i → D.nd.O i) x) else 0

section Record

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R}

def Contains (N : NData R H what₂) (A : NAut N) (i : N.Loc) (S : Set ℂ) : Prop :=
  ∀ z ∈ S, ∃ x, A.iotaQC i (A.iotaQ i x) = z

def Live (N : NData R H what₂) (i : N.Loc) : Prop :=
  ∃ π ∈ N.Z i, ∃ (r : GE N →* GL (Fin R.nV) (N.O i)) (ρ : GE N →* GL (Fin R.r) (N.O i)),
    IsHeckeGalois N i π r ∧ (∃ e, GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.IsDecomp (t := R.t) r ρ (N.chi i) e) ∧
    AbsIrrSub (mapRep (IsLocalRing.residue (N.O i)) ρ) ⊤

def ZDecomp (N : NData R H what₂) (i : N.Loc) : Prop :=
  ∀ π ∈ N.Z i, ∀ r : GE N →* GL (Fin R.nV) (N.O i), IsHeckeGalois N i π r →
    ∃ (ρ : GE N →* GL (Fin R.r) (N.O i)), ∃ e, GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.IsDecomp (t := R.t) r ρ (N.chi i) e

def IsWildInertiaCyclotomicElement (N : NData R H what₂) (i : N.Loc) (g0 : GE N) : Prop :=
  GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.IsInertiaCyclotomicGeneratorElement N i g0 ∧ ((∃ k, N.l i = H.g k) → ∀ w ∈ placesOver H.E (N.l i),
    g0 ∈ Ine (F := H.E) (N.plOm.1 w) → g0 ∈ wildSet N (N.plOm.1 w))

def TakenWild (N : NData R H what₂) (i : N.Loc) (rep : N.X i → (GE N →* GL (Fin R.nV) (N.O i)))
    (ρ : N.X i → (GE N →* GL (Fin R.r) (N.O i))) : Prop :=
  ∃ (A : Type) (_ : CommRing A) (_ : IsDomain A) (_ : IsDiscreteValuationRing A) (_ : Algebra ℤ_[N.l i] A)
    (_ : Module.Finite ℤ_[N.l i] A) (_ : Algebra A (N.O i)) (_ : IsScalarTower ℤ_[N.l i] A (N.O i))
    (TA : Subalgebra A (N.X i → A)) (repA : N.X i → (GE N →* GL (Fin R.nV) A))
    (ρA : N.X i → (GE N →* GL (Fin R.r) A)) (χA : ℕ → (GE N →* Aˣ)),
    GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.IsEnlargement N i rep ρ A TA repA ρA χA ∧ GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.HidaSetting R.t TA (N.Z i) repA ρA χA ∧
    ∀ π ∈ N.Z i, ∃ g0 L eB e1 X0, IsWildInertiaCyclotomicElement N i g0 ∧ GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.IsChoice R.t TA repA ρA χA π g0 L eB e1 X0 ∧
      GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.RootsIn R.t (N.O i) eB X0

def Chosen (N : NData R H what₂) (A : NAut N) (i : N.Loc) (S : Set ℂ) : Prop :=
  ∃ (rep : N.X i → (GE N →* GL (Fin R.nV) (N.O i))) (ρ : N.X i → (GE N →* GL (Fin R.r) (N.O i))),
    GoodR N i rep ∧ GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.HidaSetting R.t (N.T i) (N.Z i) rep ρ (N.chi i) ∧
    ∀ π ∈ N.Z i, ∃ g0 L eB e1 X0, IsWildInertiaCyclotomicElement N i g0 ∧
      GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.IsChoice R.t (N.T i) rep ρ (N.chi i) π g0 L eB e1 X0 ∧
      ∀ x, ∃ α : Fin R.t → ℂ, (∀ c, α c ∈ S) ∧
        (GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.blockPol (eB x) (X0 x)).map (iotaO N A i) = ∏ c, (X - C (α c))

structure LocExt (N₀ N₁ : NData R H what₂) (A₀ : NAut N₀) (A₁ : NAut N₁) (i₀ : N₀.Loc) (i₁ : N₁.Loc) where
  l_eq : N₀.l i₀ = N₁.l i₁
  φ : N₀.O i₀ →+* N₁.O i₁
  φ_iota : ∀ z, iotaO N₁ A₁ i₁ (φ z) = iotaO N₀ A₀ i₀ z
  φ_alg : ∀ (z : ℤ_[N₀.l i₀]) (z' : ℤ_[N₁.l i₁]), HEq z z' → φ (algebraMap _ _ z) = algebraMap _ _ z'
  e : N₁.X i₁ ≃ N₀.X i₀
  out : ∀ v, SplitOut N₁ i₁ v ↔ SplitOut N₀ i₀ v
  hT : ∀ v k x, SplitOut N₁ i₁ v → 1 ≤ k → k ≤ R.nV →
    (N₁.hT i₁ v k : N₁.X i₁ → N₁.O i₁) x = φ ((N₀.hT i₀ v k : N₀.X i₀ → N₀.O i₀) (e x))
  Z : ∀ x, x ∈ N₁.Z i₁ ↔ e x ∈ N₀.Z i₀
  γ : GE N₁ ≃* GE N₀
  γ_cont : Continuous γ
  γ_cont' : Continuous γ.symm
  frob : ∀ (w : PlE H) (σ : GE N₁), (∃ B : ValuationSubring N₁.Om, IsPlaceOver (F := H.E) B w ∧ IsFrob (F := H.E) B (normV w) σ) ↔
    ∃ B : ValuationSubring N₀.Om, IsPlaceOver (F := H.E) B w ∧ IsFrob (F := H.E) B (normV w) (γ σ)
  ine : ∀ (w : PlE H) (σ : GE N₁), σ ∈ Ine (F := H.E) (N₁.plOm.1 w) ↔ γ σ ∈ Ine (F := H.E) (N₀.plOm.1 w)
  wild : ∀ (w : PlE H) (σ : GE N₁), σ ∈ wildSet N₁ (N₁.plOm.1 w) ↔ γ σ ∈ wildSet N₀ (N₀.plOm.1 w)
  cyc : ∀ σ : GE N₁, HEq (cycZ (F := H.E) (Ω := N₀.Om) (N₀.l i₀) (γ σ)) (cycZ (F := H.E) (Ω := N₁.Om) (N₁.l i₁) σ)
  chi : ∀ c, 1 ≤ c → c ≤ R.t → ∀ σ : GE N₁,
    ((N₁.chi i₁ c σ : (N₁.O i₁)ˣ) : N₁.O i₁) = φ ((N₀.chi i₀ c (γ σ) : (N₀.O i₀)ˣ) : N₀.O i₀)

end Record

def TakenAll (D : D7) : Prop := ∀ i, Live D.nd i → ∃ r ρ, GoodR D.nd i r ∧ TakenWild D.nd i r ρ

def Large (D : D7) : Prop := SumRepresentations.hypO D ∧ GlobalTheory.SplitCoef.OSplit D ∧ TakenAll D

def Duties (D : D7) : Prop :=
  SumRepresentations.hypO D ∧ (∀ i r, GoodR D.nd i r → AbsIrreducibleDistinct D i r) ∧ Formalism.MainNotions.N.K.Rows.AllDesignConditions D ∧ TypePrimeCongruences.TypePrimeWildIdempotentChoice D

end GlobalTheory.CoefDuty

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivSupOfIsotypicPartsInternalDirectSum
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.IntegralHeckeForms
open scoped TensorProduct

namespace GlobalTheory.SupLaw.Model

open GlobalTheory.TwAll

variable (D : D7)

abbrev Pt (j : ℕ) : Type := {_g : G0g D.nd // j ∈ Finset.Icc 1 D.R.m}

abbrev KK (i : D.ntw.Tw) : Type := FractionRing (D.ntw.O i)

variable (A : ∀ (i : D.ntw.Tw) (j : ℕ), ℕ → PlE D.host → Module.End (KK D i) (Pt D j → KK D i))
  (s : ∀ i : D.ntw.Tw, ℕ → KK D i)



end GlobalTheory.SupLaw.Model

end
end

