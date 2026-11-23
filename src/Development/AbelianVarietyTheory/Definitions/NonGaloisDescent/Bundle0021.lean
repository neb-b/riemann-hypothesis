module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
public import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.DisjointSplitLevelPlaces
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
public import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.XiValIffXiAt
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
public import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0002

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdjFormula
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RawLift

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

def ThetaSchur (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (S T' : HSp D), IsStdChar D ψ (-1) →
    ∀ (μ : Measure (WO S T')) (𝓕 : Set (WO S T')), IsCovolOne (ratL T' S) μ 𝓕 →
    ∀ L : Module.End ℂ (WO S T' → ℂ), (∀ f, IsThetaFunO ψ S T' f → IsThetaFunO ψ S T' (L f)) →
      (∃ C : ℝ, ∀ f, IsThetaFunO ψ S T' f → nrm2 μ 𝓕 (L f) ≤ C * nrm2 μ 𝓕 f) →
      (∀ w f, IsThetaFunO ψ S T' f → L (heisO ψ S T' w f) = heisO ψ S T' w (L f)) →
      ∃ c : ℂ, ∀ f, IsThetaFunO ψ S T' f → L f = c • f

abbrev levW (R : RealDat D A Ks) (i : Fin D.R.m) : Subgroup (GA D (Wc D i)) := levG _ (R.βW i) (R.datWp i R.triv)

def coef (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (μ : Measure (WO (Vc D i) (Wc D i))) (𝓕 : Set (WO (Vc D i) (Wc D i)))
    (g : GA D (Wc D i)) : ℂ :=
  thetaIP μ 𝓕 (R.ωP i t (1, g) (R.vP i t)) (R.vP i t) / thetaIP μ 𝓕 (R.vP i t) (R.vP i t)

def jointVec (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) (w : (R.cV i).W) :
    WO (Vc D i) (Wc D i) → ℂ :=
  R.ptP i t (R.ioP i (PiTensorProduct.tprod ℂ v) w)

def IsUnitVec (R : RealDat D A Ks) (i : Fin D.R.m) (v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) : Prop :=
  ∀ ρ, ‖((v ρ : (R.MW i (sg0 D A)).sm ρ) : (R.MW i (sg0 D A)).H ρ)‖ = 1

def val (R : RealDat D A Ks) (i : Fin D.R.m) (v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) (x : (R.HW i (sg0 D A)).H) :
    GA D (Wc D i) → ℂ :=
  (R.HW i (sg0 D A)).e x fun ρ => v ρ

def AdjFormula (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) : Prop :=
  ∀ th, IsRaw R i t th → ∀ v, IsUnitVec R i v → ∀ (n : ℕ) (b : OrthonormalBasis (Fin n) ℂ (R.cV i).W),
    ∃ a : ℝ, 0 < a ∧ ∀ x y, ⟪LinearMap.adjoint th x, LinearMap.adjoint th y⟫_ℂ =
      (a : ℂ) * ∑ k, ∫ h in R.fdV i t,
        star (upLift (R.ωP i t) (R.νW i) (R.fdW i) (jointVec R i t v (b k)) (val R i v x) h) *
          upLift (R.ωP i t) (R.νW i) (R.fdW i) (jointVec R i t v (b k)) (val R i v y) h ∂(R.νV i t)

def LevFix (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) : Prop :=
  ∀ k ∈ levW R i, ∀ P, R.ωP i t (1, k) (R.ptP i t P) = R.ptP i t P

def FactInf (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) : Prop :=
  ∀ μ 𝓕, IsCovolOne (ratL (Wc D i) (Vc D i)) μ 𝓕 → ∀ u ∈ GinfC (Wc D i), ∀ γ ∈ GfC (Wc D i), ∀ P P',
    thetaIP μ 𝓕 (R.ωP i t (1, u * γ) (R.ptP i t P)) (R.ptP i t P') =
      thetaIP μ 𝓕 (R.ωP i t (1, u) (R.ptP i t P)) (R.ptP i t P') * coef R i t μ 𝓕 γ

def RealLow (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) : Prop :=
  ∀ μ 𝓕, IsCovolOne (ratL (Wc D i) (Vc D i)) μ 𝓕 → ∀ v, IsUnitVec R i v → ∀ w, ∀ u ∈ GinfC (Wc D i),
    thetaIP μ 𝓕 (jointVec R i t v w) (R.ωP i t (1, u) (jointVec R i t v w)) =
      thetaIP μ 𝓕 (jointVec R i t v w) (jointVec R i t v w) *
        ∏ ρ, ⟪((v ρ : (R.MW i (sg0 D A)).sm ρ) : (R.MW i (sg0 D A)).H ρ),
          (R.MW i (sg0 D A)).rep ρ (infMat D.sp.cm.sig (Wc D i).gram (R.θ ρ) u)
            ((v ρ : (R.MW i (sg0 D A)).sm ρ) : (R.MW i (sg0 D A)).H ρ)⟫_ℂ

def VecNe (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) : Prop :=
  ∀ μ 𝓕, IsCovolOne (ratL (Wc D i) (Vc D i)) μ 𝓕 → thetaIP μ 𝓕 (R.vP i t) (R.vP i t) ≠ 0 ∧
    ∃ v w, IsUnitVec R i v ∧ thetaIP μ 𝓕 (jointVec R i t v w) (jointVec R i t v w) ≠ 0

def trPair (R : RealDat D A Ks) (i : Fin D.R.m) (γ : GA D (Wc D i)) (x y : (R.HW i (sg0 D A)).H) : ℂ :=
  ipAt (R.MW i (sg0 D A)) (R.νW i) (R.fdW i) ((R.HW i (sg0 D A)).e x)
    (heckeOn (R.MW i (sg0 D A)) {γ} ((R.HW i (sg0 D A)).e y))

def FinSum (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) : Prop :=
  ∀ th, IsRaw R i t th → ∀ μ 𝓕, IsCovolOne (ratL (Wc D i) (Vc D i)) μ 𝓕 → ∃ a : ℝ, 0 < a ∧ ∀ x y,
    HasSum (fun q : GfC (Wc D i) ⧸ (levW R i).subgroupOf (GfC (Wc D i)) =>
      (a : ℂ) * (coef R i t μ 𝓕 (q.out : GfC (Wc D i)) * trPair R i (q.out : GfC (Wc D i)) x y))
      ⟪LinearMap.adjoint th x, LinearMap.adjoint th y⟫_ℂ

def TrivAt (V : HSp D) (f : AE D) (g : GA D V) : Prop := ∀ a b, f * (mt V g - 1) a b = 0

def IsFinIdem (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) (f : AE D) : Prop :=
  ∃ ε, IsPlaceIdem D v ε ∧ f = algebraMap (AF D.host.F) (AE D) ε

def FinMult (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) : Prop :=
  ∀ μ 𝓕, IsCovolOne (ratL (Wc D i) (Vc D i)) μ 𝓕 → ∀ v f, IsFinIdem D v f →
    ∀ γ ∈ GfC (Wc D i), TrivAt (Wc D i) f γ → ∀ k, SuppF (Wc D i) f k →
      coef R i t μ 𝓕 (γ * k) = coef R i t μ 𝓕 γ * coef R i t μ 𝓕 k

def BadSupp (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) : Prop :=
  ∀ μ 𝓕, IsCovolOne (ratL (Wc D i) (Vc D i)) μ 𝓕 → ∀ P, P ∈ R.Pg ∨ P ∈ R.Q t → ∀ e f, IsPrimeIdem P e f →
    ∀ k, SuppF (Wc D i) f k → k ∉ levW R i → coef R i t μ 𝓕 k = 0

def latIndex (W : HSp D) (g : GA D W) : ℕ :=
  ((Formalism.L2.NTheta.LamHat W).map (finMat D.sp.cm.sig W.gram g).mulVecLin.toAddMonoidHom).relIndex (Formalism.L2.NTheta.LamHat W)

def GoodMod (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) : Prop :=
  ∀ μ 𝓕, IsCovolOne (ratL (Wc D i) (Vc D i)) μ 𝓕 → ∀ v f, IsFinIdem D v f →
    (∀ P, P ∈ R.Pg ∨ P ∈ R.Q t → ∀ e f', IsPrimeIdem P e f' → f' ≠ f) → ∀ k, SuppF (Wc D i) f k →
      ‖coef R i t μ 𝓕 k‖ ^ 2 * (latIndex (Wc D i) k : ℝ) ^ (Vc D i).rank = 1

def IndexSum (W : HSp D) (n : ℕ) : Prop :=
  ∃ s : HeightOneSpectrum (𝓞 D.host.F) → ℝ, Summable s ∧ (∀ v, s v < 1) ∧ ∀ v f, IsFinIdem D v f →
    ∀ C : Finset (GA D W), (∀ g ∈ C, SuppF W f g ∧ g ∉ KsphC W ∅) → (∀ g ∈ C, ∀ g' ∈ C, g⁻¹ * g' ∈ KsphC W ∅ → g = g') →
      ∑ g ∈ C, (latIndex W g : ℝ) ^ (-(n : ℝ) / 2) ≤ s v

def LocSmall (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) : Prop :=
  ∀ μ 𝓕, IsCovolOne (ratL (Wc D i) (Vc D i)) μ 𝓕 →
    ∃ s : HeightOneSpectrum (𝓞 D.host.F) → ℝ, Summable s ∧ (∀ v, s v < 1) ∧ ∀ v f, IsFinIdem D v f →
      ∀ C : Finset (GA D (Wc D i)), (∀ g ∈ C, SuppF (Wc D i) f g ∧ g ∉ levW R i) →
        (∀ g ∈ C, ∀ g' ∈ C, g⁻¹ * g' ∈ levW R i → g = g') → ∑ g ∈ C, ‖coef R i t μ 𝓕 g‖ ≤ s v

def LevProd (R : RealDat D A Ks) (i : Fin D.R.m) : Prop :=
  levW R i ≤ GfC (Wc D i) ∧ (∀ k ∈ levW R i, levChi _ (R.βW i) (R.datWp i R.triv) k = 1) ∧
  ∃ cmp : HeightOneSpectrum (𝓞 D.host.F) → (GA D (Wc D i) →* GA D (Wc D i)),
    (∀ v f, IsFinIdem D v f → ∀ g, SuppF (Wc D i) f (cmp v g) ∧ TrivAt (Wc D i) f (g * (cmp v g)⁻¹)) ∧
    (∀ g ∈ GfC (Wc D i), (g ∈ levW R i ↔ ∀ v, cmp v g ∈ levW R i) ∧ {v | cmp v g ∉ levW R i}.Finite)

def TransLaws (R : RealDat D A Ks) (i : Fin D.R.m) : Prop :=
  (∀ v f, IsFinIdem D v f → ∀ α, SuppF (Wc D i) f α → ∃ C : Finset (GA D (Wc D i)), (∀ γ ∈ C, SuppF (Wc D i) f γ) ∧
      IsCosetRep (Wc D i) {k | k ∈ levW R i ∧ SuppF (Wc D i) f k} α C) ∧
  (∀ v f, IsFinIdem D v f → ∀ α, SuppF (Wc D i) f α → ∀ C : Finset (GA D (Wc D i)), (∀ γ ∈ C, SuppF (Wc D i) f γ) →
      IsCosetRep (Wc D i) {k | k ∈ levW R i ∧ SuppF (Wc D i) f k} α C →
      ∀ y, ∃ y', (R.HW i (sg0 D A)).e y' = heckeOn (R.MW i (sg0 D A)) C ((R.HW i (sg0 D A)).e y) ∧
        ∀ γ ∈ GfC (Wc D i), ∀ x, trPair R i γ x y' = ∑ δ ∈ C, trPair R i (γ * δ) x y) ∧
  (∀ γ ∈ GfC (Wc D i), ∃ B : (R.HW i (sg0 D A)).H →L[ℂ] (R.HW i (sg0 D A)).H, ‖B‖ ≤ 1 ∧ ∀ x y, trPair R i γ x y = ⟪x, B y⟫_ℂ) ∧
  (∀ γ ∈ GfC (Wc D i), ∀ k ∈ levW R i, ∀ k' ∈ levW R i, ∀ x y, trPair R i (k * γ * k') x y = trPair R i γ x y) ∧
  (∀ γ ∈ GfC (Wc D i), ∀ x y, trPair R i γ⁻¹ x y = star (trPair R i γ y x)) ∧
  ∀ x y, trPair R i 1 x y = ⟪x, y⟫_ℂ

end GlobalTheory.RawLift

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CompIntField
section
set_option autoImplicit false

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta IsDedekindDomain NumberField Formalism.IndefR.Datum Formalism.IndefR.Lev Formalism.IndefR.NX
open scoped TensorProduct
open Classical

namespace GlobalTheory.TowerCov

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def IsLevN (E : ExpSet D) (N : ℕ) : Prop :=
  N ≠ 0 ∧ (∀ p : ℕ, p.Prime → p ∣ N →
    p ≠ 2 ∧ Nat.Coprime p E.l ∧ (∀ a, p ≠ E.pde a) ∧ (∀ a, p ≠ E.gp a) ∧ D.host.cls p = .splitK ∧
      ¬ p ∣ Ideal.absNorm D.host.ccK) ∧ Squarefree N

def LevN (E : ExpSet D) : Type := {N : ℕ // IsLevN E N}

section Fields

variable (E : ExpSet D) {O : Type} [CommRing O] (C : CoefLat E O) (Base : Set (GA D E.W → ℂ))
  (LQ : LevN E → Subfield ℂ) (Rat : ∀ N : LevN E, Submodule (LQ N) (GA D E.W → ℂ))
  (Λ : Subring ℂ) (BaseInt : Submodule Λ (GA D E.W → ℂ)) (Int : LevN E → Submodule Λ (GA D E.W → ℂ))

variable {E C Base LQ Rat Λ BaseInt Int}

end Fields

section Covers

open Formalism.L2.Pj Formalism.IndefR.FWT GlobalTheory.CoverRead

variable {E : ExpSet D} {T : CoreJ D} {j : ℕ} {σ : T.Q.c.F →+* ℂ} (hV : T.V j σ = E.W)
  (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) (z : ℂ)

def placesIn {L : Type} [Field L] [NumberField L] (ι : L →+* ℂ) (Λ : Subring ℂ) : Set (HeightOneSpectrum (𝓞 L)) :=
  {la | ∀ x : L, la.valuation L x ≤ 1 → ι x ∈ Λ}

end Covers

end GlobalTheory.TowerCov
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ZintZero
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.CuspRep

namespace GlobalTheory.RSJ

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}


variable (E) in
def pFin : Ad E →+* Af E := RingHom.snd (InfiniteAdeleRing E) (Af E)

def secRow {R : Type*} [CommRing R] (y : Fin a → R) : Matrix (Fin a) (Fin a) R :=
  Matrix.of fun i j => if (i : ℕ) + 1 = a then y j else (1 : Matrix (Fin a) (Fin a) R) i j


open Classical in
def secInv (y : Fin a → Cinf E) : GL (Fin a) (Cinf E) :=
  if h : IsUnit (secRow y).det then (Matrix.nonsingInvUnit (secRow y) h)⁻¹ else 1

def rowAct (ξ : Fin a → E) (g : GA E a) : Fin a → Ad E :=
  Matrix.vecMul (fun i => algebraMap E (Ad E) (ξ i)) (g : Matrix (Fin a) (Fin a) (Ad E))


variable (E) in
def natLat (N : ℕ) : Set (Af E) :=
  {x | ∃ z : Af E, (∀ v : HeightOneSpectrum (𝓞 E), z v ∈ v.adicCompletionIntegers E) ∧ x = (N : Af E) * z}


open Classical in
def indN (N : ℕ) (y : Fin a → Af E) : ℂ :=
  if ∀ i : Fin a, y i - (if (i : ℕ) + 1 = a then 1 else 0) ∈ natLat E N then 1 else 0


variable (E a) in
def detPow (x : ℝ) (g : GA E a) : ℝ := ‖((chiDet a (GlobalTheory.HeckeGal.Model.absPow E x) g : ℂˣ) : ℂ)‖

def Psi (φ φ' : GA E a → ℂ) (Φ : (Fin a → Cinf E) → ℂ) (N : ℕ) (g : GA E a) (y : Fin a → Ad E) : ℂ :=
  φ (g * infGL E a (secInv fun i => pInf E (y i))) * starRingEnd ℂ (φ' (g * infGL E a (secInv fun i => pInf E (y i)))) *
    Φ (fun i => pInf E (y i)) * indN N (fun i => pFin E (y i))

def thetaSum (φ φ' : GA E a → ℂ) (Φ : (Fin a → Cinf E) → ℂ) (N : ℕ) (g : GA E a) : ℂ :=
  ∑' ξ : {ξ : Fin a → E // ξ ≠ 0}, Psi φ φ' Φ N g (rowAct ξ.1 g)

def Zint (μ : Measure (GA E a)) (𝓕 : Set (GA E a)) (φ φ' : GA E a → ℂ) (Φ : (Fin a → Cinf E) → ℂ) (N : ℕ) (x : ℝ) : ℂ :=
  ∫ g in 𝓕, thetaSum φ φ' Φ N g * (detPow E a x g : ℂ) ∂μ

end GlobalTheory.RSJ
end
end

