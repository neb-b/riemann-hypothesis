module

public import Mathlib
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Formalism.HermitianCurvature.StatementD
public import Formalism.HermitianCurvature.BesselNonvanishingReduction
public import Formalism.PeriodIntegrals.Bundle0021
public import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
public import Formalism.HarderNarasimhan.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SecondLabelsNonempty

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Admissible
section
namespace GlobalTheory.ThA

open Formalism.FourierDecayAlt MeasureTheory Formalism.QuantumDeterminants Matrix
open scoped InnerProductSpace

noncomputable section

def aT (k r : ℕ) (α : ℂ) : B.Mat k r :=
  Matrix.diagonal fun i => if i.val < r then α ^ (r - i.val)
    else if i.val ≤ r + k then 1 else ((star α) ^ (i.val - (r + k)))⁻¹

def conjF {k r : ℕ} {V : Type*} (α : ℂ) (F : B.Mat k r → V) : B.Mat k r → V :=
  fun x => F (aT k r α * x * (aT k r α)⁻¹)

def KH (k r : ℕ) : Set (B.Mat k r) :=
  UH (Hpk k r) ∩ (Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ : Set _)

def IsStdOf {k r : ℕ} (L : Formalism.MainNotions.S.LocBessel k r) (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)
    (Bs : B.RealPlaceData k r L.Wp L.Wq) : Prop :=
  Bs.z = L.z ∧ Bs.z' = L.z' ∧ Bs.π = L.π ∧ Bs.π' = L.π' ∧ Bs.μW = L.μW ∧ Bs.μW' = L.μW' ∧
    Bs.μN = D.muN k r ∧ Bs.μsec = μsec

def IsRatioN (k r : ℕ) (cN : ℝ) : Prop :=
  0 < cN ∧ Formalism.MainNotions.S.haarLie (Nset k r) 1 = ENNReal.ofReal cN • D.muN k r

def lamN {k r : ℕ} (L : Formalism.MainNotions.S.LocBessel k r) (cN : ℝ) : ℝ :=
  L.κN.toReal * cN * ‖cStd / L.c‖ ^ B.kap k r

end

end GlobalTheory.ThA
end

-- bundled from Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
section
open MeasureTheory NumberField Matrix Finset
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.Count

open Formalism.MainNotions.S

def dOp {n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) : ℝ :=
  Real.log ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin g)‖

def dHS {n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) : ℝ :=
  Real.sqrt (∑ j, (Real.log ((Matrix.isHermitian_conjTranspose_mul_self g).eigenvalues j) / 2) ^ 2)

def rkR {n : ℕ} (ε : Fin n → Bool) : ℕ :=
  min (univ.filter fun a => ε a = true).card (univ.filter fun a => ε a = false).card

def decE (q : ℕ) (h d : ℝ) : ℝ := Real.exp (-(h / 8) * min (2 * d ^ 2) (d / Real.sqrt q))

def IsGauge {n : ℕ} (ε : Fin n → Bool) (c : ℝ) : Prop :=
  Filter.Tendsto
    (fun r : ℝ => c * (Formalism.REAL.muG ε {g | Real.sqrt (Formalism.REAL.hs (uMat g - 1)) ≤ r}).toReal / r ^ (n ^ 2))
    (nhdsWithin 0 (Set.Ioi 0))
    (nhds (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (n ^ 2))) 1)).toReal)

def layerProd (n f : ℕ) {a : ℕ} (j : Fin a → ℕ) (τ : Fin a → ℝ) (G : ℝ → ℝ) : ℝ :=
  (∏ i, ∏ k ∈ univ.filter (fun k => i < k),
      G (τ i / τ k) ^ (2 * j i * j k * f) * G (τ i * τ k) ^ (2 * j i * j k * f)) *
    ∏ i, G (τ i) ^ (2 * j i * (n - 2 * ∑ l, j l) * f) * G (τ i ^ 2) ^ (j i ^ 2 * f)

variable (I : AutInst)

def lamX (x : I.GA) : Submodule (𝓞 I.E) (Fin I.n → I.E) :=
  Submodule.span (𝓞 I.E)
    {y | I.fmat x.2⁻¹ *ᵥ (fun i => Formalism.UG.inclE (F := I.F) (Af I.F) (y i)) ∈ I.Lf}


open Classical in
def frm (x : I.GA) : InfinitePlace I.E → Matrix (Fin I.n) (Fin I.n) ℂ := fun w =>
  if w.embedding = I.φ (w.comap (algebraMap I.F I.E)) then
    I.P (w.comap (algebraMap I.F I.E)) * uMat (x.1 (w.comap (algebraMap I.F I.E)))
  else (I.P (w.comap (algebraMap I.F I.E)) * uMat (x.1 (w.comap (algebraMap I.F I.E)))).map (starRingEnd ℂ)

abbrev bas : Module.Basis (Fin I.n) I.E (Fin I.n → I.E) := Pi.basisFun I.E (Fin I.n)

def least (x : I.GA) : ℝ := Formalism.HN.leastSize (bas I) (frm I x) (lamX I x)

def tau1 (x : I.GA) : ℝ := min (1 / 2) (least I x)

def stepLe (x : I.GA) (t : ℝ) : Submodule (𝓞 I.E) (Fin I.n → I.E) :=
  sSup {N | N ≤ lamX I x ∧ N ≠ ⊥ ∧ Formalism.HN.largestSize (bas I) (frm I x) N ≤ t}

def stepLt (x : I.GA) (t : ℝ) : Submodule (𝓞 I.E) (Fin I.n → I.E) :=
  sSup {N | N ≤ lamX I x ∧ N ≠ ⊥ ∧ Formalism.HN.largestSize (bas I) (frm I x) N < t}

def HasFlag (x : I.GA) {a : ℕ} (S : Fin (a + 1) → Submodule (𝓞 I.E) (Fin I.n → I.E)) (τ : Fin a → ℝ) : Prop :=
  S 0 = ⊥ ∧ StrictMono S ∧ S (Fin.last a) = stepLt I x (1 / 2) ∧ StrictMono τ ∧
    (∀ i, 0 < τ i ∧ τ i < 1 / 2 ∧ S i.succ = stepLe I x (τ i) ∧
      Formalism.HN.sizeQ (bas I) (frm I x) (S i.succ) (S i.castSucc) = τ i) ∧
    ∀ t : ℝ, t < 1 / 2 → stepLe I x t ∈ Set.range S

def HasType (x : I.GA) {a : ℕ} (j : Fin a → ℕ) (τ : Fin a → ℝ) : Prop :=
  ∃ S, HasFlag I x S τ ∧ ∀ i, Formalism.HN.rkK (S i.succ) = Formalism.HN.rkK (S i.castSucc) + j i

def perpIn (x : I.GA) (S : Submodule (𝓞 I.E) (Fin I.n → I.E)) : Submodule (𝓞 I.E) (Fin I.n → I.E) :=
  Submodule.span (𝓞 I.E) {y | y ∈ lamX I x ∧ ∀ s ∈ S, Formalism.UG.hform (starRingEnd I.E) I.J s y = 0}

def nearSet (x : I.GA) (δ : ℝ) : Set I.GA :=
  {γ | γ ∈ I.GFset ∧ (x⁻¹ * γ * x).2 ∈ I.Kset ∧
    ∀ v, Real.sqrt (Formalism.REAL.hs (uMat ((x⁻¹ * γ * x).1 v) - 1)) ≤ δ}

def kern (φ : I.GA → ℂ) (x y : I.GA) : ℂ := ∑' γ : I.GFset, φ (x⁻¹ * γ.1 * y)

variable (B : RowsAut)

def IsDSData (d : InfinitePlace B.I.F → ℝ) : Prop :=
  ∀ v, Formalism.QuantumDeterminants.IsHCParam (B.lam v) ∧ IsDS (B.I.ε v) (B.lam v) (B.σ v) ∧
    IsLowUnit (B.I.ε v) (B.lam v) (B.σ v) (B.w v) ∧ IsFdeg (Formalism.REAL.muG (B.I.ε v)) (B.σ v) (d v)

def SigIs (p q : ℕ) : Prop := ∀ v, B.I.pAt v = p ∧ B.I.qAt v = q

def GapGe (h : ℝ) : Prop := ∀ v, Formalism.QuantumDeterminants.GapAtLeast (B.I.ε v) (B.lam v) h

def ph (d : InfinitePlace B.I.F → ℝ) (g : B.I.Ginf) : ℂ :=
  ((∏ v, d v : ℝ) : ℂ) * star (∏ v, ⟪B.w v, B.σ v (uMat (g v)) (B.w v)⟫_ℂ)

def phe (d : InfinitePlace B.I.F → ℝ) (x : B.I.GA) : ℂ := ph B d x.1 * B.e x.2

def mainTerm (d : InfinitePlace B.I.F → ℝ) : ℝ := B.I.Dstar (∏ v, d v) B.μf B.fund B.e

def prob (A : Set B.I.GA) : ℝ := ((B.I.muA B.μf) (A ∩ B.fund)).toReal / B.I.vol B.μf B.fund

def IsNear (d : InfinitePlace B.I.F → ℝ) (ep : ℝ) (x γ : B.I.GA) : Prop :=
  γ ∈ B.I.GFset ∧ phe B d (x⁻¹ * γ * x) ≠ 0 ∧ ∀ v, dHS (uMat ((x⁻¹ * γ * x).1 v)) ≤ ep

def bigX (b : ℝ) : ℝ := (B.I.n : ℝ) * B.I.f * B.I.rd * B.g * b

def epN : ℝ := 1 / 10 ^ 6 / ((B.I.n : ℝ) ^ 8 * (B.I.f : ℝ) ^ 2)

def tauStar (q : ℕ) (b : ℝ) : ℝ := (bigX B b)⁻¹ ^ (11 * q)

def CountHyp (Cg : ℝ) (n₀ : ℕ) (d : InfinitePlace B.I.F → ℝ) (p q : ℕ) (b : ℝ) : Prop :=
  IsDSData B d ∧ SigIs B p q ∧ n₀ ≤ B.I.n ∧ q ^ 2 ≤ B.I.n ∧
    Real.log B.I.rd ≤ Real.exp B.I.n ∧ Real.log B.I.f ≤ Real.sqrt B.I.n ∧ 2 ≤ b ∧
    Real.log b ≤ Real.exp (1 / 16 * B.I.n * B.I.f * Real.log B.I.n) ∧
    (∀ v a, |B.lam v a| ≤ b ^ 2) ∧ 1 ≤ B.g ∧ (B.g : ℝ) ≤ b ^ Cg ∧
    B.g₀.Prime ∧ 4 * B.I.n < B.g₀ ∧
    (Ideal.primesOver (Ideal.span {(B.g₀ : ℤ)}) (𝓞 B.I.E)).ncard = Module.finrank ℚ B.I.E ∧
    GapGe B (8 * 10 ^ 14 * (Cg + 4) * (B.I.n : ℝ) ^ 19 * (B.I.f : ℝ) ^ 5 * Real.log (b * B.I.rd))

end GlobalTheory.Count
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MatrixOfBesselTwoSidedAction
section
noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S
open scoped InnerProductSpace

namespace GlobalTheory.SgInf

abbrev Mat (k r : ℕ) := Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ

abbrev GG (k r : ℕ) : Set (Mat k r) := UH (Hpk k r)

def opn {n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) : ℝ := ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) g‖

def IsClosedSub (k r : ℕ) (S : Set (Mat k r)) : Prop :=
  S ⊆ GG k r ∧ IsClosed S ∧ (1 : Mat k r) ∈ S ∧ (∀ a ∈ S, ∀ b ∈ S, a * b ∈ S) ∧ ∀ a ∈ S, a⁻¹ ∈ S

def rmulM {k r : ℕ} (a : Mat k r) (x : Mt k r) : Mt k r := Matrix.of x * a

def invM {k r : ℕ} (x : Mt k r) : Mt k r := ((Matrix.of x : Mat k r)⁻¹ : Mat k r)

def IsUnimod {k r : ℕ} (S : Set (Mat k r)) (μ : Measure (Mt k r)) : Prop :=
  (∀ s ∈ S, μ.map (rmulM s) = μ) ∧ μ.map invM = μ

def normInt {k r : ℕ} (μ : Measure (Mt k r)) (A : ℝ) : ENNReal :=
  ∫⁻ x, ENNReal.ofReal (opn (Matrix.of x) ^ (-A)) ∂μ

def hPart (k r : ℕ) (s : Mat k r) : Mat k r := fun i j =>
  if (r ≤ i.val ∧ i.val ≤ r + k) ∧ (r ≤ j.val ∧ j.val ≤ r + k) then s i j else if i = j then 1 else 0

variable {k r : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable {Wp : Type*} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
variable {Wq : Type*} [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]

def PiS (ψ : Mat k r → ℂ) (π : Mat k r → (Wp →L[ℂ] Wp)) (s : Mat k r) : Wp →L[ℂ] Wp :=
  ψ ((hPart k r s)⁻¹ * s) • π (hPart k r s)

def coef (σ : Mat k r → (H →L[ℂ] H)) (u v : H) (g : Mat k r) : ℂ := ⟪v, σ g u⟫_ℂ

def SchurH (μ : Measure (Mt k r)) (σ : Mat k r → (H →L[ℂ] H)) (d : ℝ) : Prop :=
  0 < d ∧ ∀ v w v' w' : H,
    Integrable (fun g : Mt k r => coef σ v w (Matrix.of g) * star (coef σ v' w' (Matrix.of g))) μ ∧
    ∫ g, coef σ v w (Matrix.of g) * star (coef σ v' w' (Matrix.of g)) ∂μ = ⟪v', v⟫_ℂ * ⟪w, w'⟫_ℂ / (d : ℂ)

def DD (σ : Mat k r → (H →L[ℂ] H)) (w : H) : Submodule ℂ H :=
  Submodule.span ℂ {v | ∃ g ∈ GG k r, v = σ g w}

def Decay (σ : Mat k r → (H →L[ℂ] H)) (V : Set H) (a : ℝ) : Prop :=
  ∀ u ∈ V, ∀ v ∈ V, ∃ C : ℝ, ∀ g ∈ GG k r, ‖coef σ u v g‖ ≤ C * opn g ^ (-a)

def Std (σ : Mat k r → (H →L[ℂ] H)) (w : H) (a : ℝ) (μG : Measure (Mt k r)) (d : ℝ) : Prop :=
  1 ≤ k ∧ IsURepOn (GG k r) σ ∧ IsIrredOn (GG k r) σ ∧ ‖w‖ = 1 ∧ IsHaarOn (GG k r) μG ∧ SchurH μG σ d ∧
    2 * ((2 * r + k + 1 : ℕ) : ℝ) ^ 5 ≤ a ∧ Decay σ (DD σ w) a ∧ CompleteSpace H

def StdSm (σ : Mat k r → (H →L[ℂ] H)) (w : H) (a : ℝ) (μG : Measure (Mt k r)) (d : ℝ) : Prop :=
  Std σ w a μG d ∧ IsSmoothVec σ w

def Side (z : Fin (2 * r + k + 1) → ℂ) (π : Mat k r → (Wp →L[ℂ] Wp)) (μS : Measure (Mt k r)) : Prop :=
  inWb k r z ∧ 0 < Tz k r z ∧ IsURepOn (UWset k r z) π ∧ IsHaarOn (Sset k r z) μS ∧
    FiniteDimensional ℂ Wp

def SideIrr (z : Fin (2 * r + k + 1) → ℂ) (π : Mat k r → (Wp →L[ℂ] Wp)) (μS : Measure (Mt k r)) : Prop :=
  Side z π μS ∧ IsIrredOn (UWset k r z) π ∧ Nontrivial Wp

def be [CompleteSpace Wp] (ψ : Mat k r → ℂ) (π : Mat k r → (Wp →L[ℂ] Wp)) (μS : Measure (Mt k r))
    (σ : Mat k r → (H →L[ℂ] H)) (u u' : H) : Wp →L[ℂ] Wp :=
  ∫ s, coef σ u u' (Matrix.of s) • PiS ψ π (Matrix.of s)⁻¹ ∂μS

def Afun [CompleteSpace Wp] (ψ : Mat k r → ℂ) (π : Mat k r → (Wp →L[ℂ] Wp)) (μS : Measure (Mt k r))
    (σ : Mat k r → (H →L[ℂ] H)) (u v : H) (ξ : Wp) (x : Mat k r) : Wp :=
  be ψ π μS σ (σ x u) v ξ

def rk1 (a : Wp) (b : Wq) : Wq →L[ℂ] Wp := (innerSL ℂ b).smulRight a

def Greg (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) : Set (Mat k r) :=
  {γ | γ ∈ GG k r ∧ (∀ l : Fin (r + 2), l.val ≤ r → Dmin k r z z' γ l ≠ 0) ∧ Gf k r z z' γ ≠ 0}

def act2 (γ : Mat k r) (p : Mt k r × Mt k r) : Mt k r := Matrix.of p.1 * γ * (Matrix.of p.2)⁻¹

def IsDis (Ω : Set (Mat k r)) (μG μS μS' ν : Measure (Mt k r)) : Prop :=
  SigmaFinite ν ∧ ν {x | Matrix.of x ∉ Ω} = 0 ∧ ∀ f : Mt k r → ENNReal, Measurable f →
    ∫⁻ x, f x ∂μG = ∫⁻ γ, (∫⁻ p, f (act2 (Matrix.of γ) p) ∂(μS.prod μS')) ∂ν

def orbNormInt (μS μS' : Measure (Mt k r)) (b : ℝ) (γ : Mat k r) : ENNReal :=
  ∫⁻ p, ENNReal.ofReal (opn (Matrix.of (act2 γ p)) ^ (-b)) ∂(μS.prod μS')

def Iint [CompleteSpace Wp] (ψ ψ' : Mat k r → ℂ) (π : Mat k r → (Wp →L[ℂ] Wp))
    (π' : Mat k r → (Wq →L[ℂ] Wq)) (μS μS' : Measure (Mt k r)) (σ : Mat k r → (H →L[ℂ] H)) (x y : H)
    (ξ : Wp) (ξ' : Wq) (γ : Mat k r) : Wq →L[ℂ] Wp :=
  ∫ p, coef σ x y (Matrix.of (act2 γ p)) •
    rk1 (PiS ψ π (Matrix.of p.1)⁻¹ ξ) (PiS ψ' π' (Matrix.of p.2)⁻¹ ξ') ∂(μS.prod μS')

def OO [CompleteSpace Wp] (μ : Measure (Mt k r)) (Φ : Mat k r → Wp) (Φ' : Mat k r → Wq) (γ : Mat k r) :
    Wq →L[ℂ] Wp :=
  ∫ x, rk1 (Φ (Matrix.of x)) (Φ' (γ⁻¹ * Matrix.of x)) ∂μ

def IsFolner (S : Set (Mat k r)) (μ : Measure (Mt k r)) (Om : ℕ → Set (Mt k r)) : Prop :=
  (∀ j, MeasurableSet (Om j) ∧ (∀ x ∈ Om j, Matrix.of x ∈ S) ∧ Bornology.IsBounded (Om j) ∧
    0 < μ (Om j) ∧ μ (Om j) < ⊤) ∧
  ∀ C : Set (Mat k r), IsCompact C → C ⊆ S → ∃ Oc : ℕ → Set (Mt k r),
    (∀ j, MeasurableSet (Oc j) ∧ Oc j ⊆ Om j ∧ ∀ c ∈ C, ∀ x ∈ Oc j, lmulM c x ∈ Om j) ∧
    Filter.Tendsto (fun j => μ (Oc j) / μ (Om j)) Filter.atTop (nhds 1)

def MultOne (z : Fin (2 * r + k + 1) → ℂ) (ψ : Mat k r → ℂ) (σ : Mat k r → (H →L[ℂ] H))
    (π : Mat k r → (Wp →L[ℂ] Wp)) : Prop :=
  ∀ B B' : H → Wp, IsBesselMapSm z ψ σ π B → IsBesselMapSm z ψ σ π B' →
    ∃ a : ℂ, (∀ x ∈ smoothVecs (k := k) (r := r) σ, B x = a • B' x) ∨
      (∀ x ∈ smoothVecs (k := k) (r := r) σ, B' x = a • B x)

def NonVan [CompleteSpace Wp] (z : Fin (2 * r + k + 1) → ℂ) (ψ : Mat k r → ℂ) (σ : Mat k r → (H →L[ℂ] H))
    (π : Mat k r → (Wp →L[ℂ] Wp)) (w : H) (μG ν : Measure (Mt k r)) : Prop :=
  ∃ W : Mat k r → Wp,
    AEStronglyMeasurable (fun x => W (Matrix.of x)) μG ∧ AEStronglyMeasurable (fun x => W (Matrix.of x)) ν ∧
    IsSPsiEquiv z ψ π W ∧ l2SG ν W < ⊤ ∧ l2SG ν W ≠ 0 ∧
    ∀ x ∈ GG k r, rconv μG (eFun μG σ w) W x = W x

def IsEll [CompleteSpace Wp] (z : Fin (2 * r + k + 1) → ℂ) (ψ : Mat k r → ℂ) (π : Mat k r → (Wp →L[ℂ] Wp))
    (μS : Measure (Mt k r)) (σ : Mat k r → (H →L[ℂ] H)) (V : Set H) (l : H → Wp) : Prop :=
  IsBesselMapSm z ψ σ π l ∧ (∃ u ∈ V, l u ≠ 0) ∧ ∀ u ∈ V, ∀ u' ∈ V, be ψ π μS σ u u' = rk1 (l u) (l u')

def Vinf (σ : Mat k r → (H →L[ℂ] H)) (w : H) : Submodule ℂ H :=
  Submodule.span ℂ {v | ∃ (Ys : List (Mat k r)) (g : Mat k r), (∀ Y ∈ Ys, InLieHpk k r Y) ∧ g ∈ GG k r ∧
    v = dsigW σ Ys (σ g w)}

def dil (k r : ℕ) (τ : ℝ) : Mat k r := Matrix.diagonal fun i =>
  if i.val < r then (τ : ℂ) ^ (r - i.val) else if i.val ≤ r + k then 1 else ((τ : ℂ) ^ (i.val - (r + k)))⁻¹

theorem of_invM (x : Mt k r) : (Matrix.of (invM x) : Mat k r) = (Matrix.of x : Mat k r)⁻¹ := rfl

theorem invM_invM (x : Mt k r) (h : IsUnit (Matrix.of x : Mat k r).det) : invM (invM x) = x := by
  show ((((Matrix.of x : Mat k r)⁻¹ : Mat k r))⁻¹ : Mat k r) = Matrix.of x
  exact Matrix.nonsing_inv_nonsing_inv _ h

theorem measurable_invM : Measurable (invM : Mt k r → Mt k r) := by
  have hc : Continuous fun x : Mt k r => (Matrix.of x : Mat k r) := by exact continuous_id
  have hdet : Measurable fun x : Mt k r => ((Matrix.of x : Mat k r).det)⁻¹ :=
    hc.matrix_det.measurable.inv
  have hadj : ∀ i j, Measurable fun x : Mt k r => (Matrix.of x : Mat k r).adjugate i j :=
    fun i j => ((continuous_apply_apply i j).comp hc.matrix_adjugate).measurable
  refine Measurable.of_eval fun i => Measurable.of_eval fun j => ?_
  have key : (fun x : Mt k r => invM x i j) =
      fun x => ((Matrix.of x : Mat k r).det)⁻¹ * (Matrix.of x : Mat k r).adjugate i j := by
    funext x
    simp [invM, Matrix.inv_def, Ring.inverse_eq_inv']
  rw [key]
  exact hdet.mul (hadj i j)

theorem of_rmulM (a : Mat k r) (x : Mt k r) : (Matrix.of (rmulM a x) : Mat k r) = Matrix.of x * a := rfl

theorem continuous_rmulM (a : Mat k r) : Continuous (rmulM a : Mt k r → Mt k r) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [rmulM, Matrix.mul_apply, Matrix.of_apply]
  exact continuous_finsetSum _ fun l _ => (continuous_apply_apply i l).mul continuous_const

theorem matrix_of_besselTwoSidedAction (γ : Mat k r) (p : Mt k r × Mt k r) :
    (Matrix.of (act2 γ p) : Mat k r) = Matrix.of p.1 * γ * Matrix.of (invM p.2) := rfl

theorem opn_nonneg {n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) : 0 ≤ opn g := norm_nonneg _

theorem opn_mul_le {n : ℕ} (g h : Matrix (Fin n) (Fin n) ℂ) : opn (g * h) ≤ opn g * opn h := by
  simp only [opn, map_mul]
  exact norm_mul_le _ _

theorem opn_one {n : ℕ} : opn (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) = 1 := by
  simp [opn]

theorem hPart_one : hPart k r 1 = 1 := by
  funext i j
  simp only [hPart]
  split_ifs with h1 h2 <;> simp [Matrix.one_apply, *]

theorem PiS_one (ψ : Mat k r → ℂ) (π : Mat k r → (Wp →L[ℂ] Wp)) : PiS ψ π 1 = ψ 1 • π 1 := by
  simp [PiS, hPart_one]

theorem coef_smul_left (σ : Mat k r → (H →L[ℂ] H)) (c : ℂ) (u v : H) (g : Mat k r) :
    coef σ (c • u) v g = c * coef σ u v g := by
  simp [coef]

theorem coef_smul_right (σ : Mat k r → (H →L[ℂ] H)) (c : ℂ) (u v : H) (g : Mat k r) :
    coef σ u (c • v) g = star c * coef σ u v g := by
  simp [coef, mul_comm]

theorem coef_add_left (σ : Mat k r → (H →L[ℂ] H)) (u u' v : H) (g : Mat k r) :
    coef σ (u + u') v g = coef σ u v g + coef σ u' v g := by
  simp [coef]

theorem coef_add_right (σ : Mat k r → (H →L[ℂ] H)) (u v v' : H) (g : Mat k r) :
    coef σ u (v + v') g = coef σ u v g + coef σ u v' g := by
  simp [coef]

theorem rankOneInnerOperator_apply (a : Wp) (b η : Wq) : rk1 a b η = ⟪b, η⟫_ℂ • a := rfl

theorem norm_rankOneInnerOperator (a : Wp) (b : Wq) : ‖rk1 a b‖ = ‖a‖ * ‖b‖ := by
  rw [rk1, ContinuousLinearMap.norm_smulRight_apply, innerSL_apply_norm, mul_comm]

theorem mem_DD (σ : Mat k r → (H →L[ℂ] H)) (w : H) {g : Mat k r} (hg : g ∈ GG k r) : σ g w ∈ DD σ w := Submodule.subset_span ⟨g, hg, rfl⟩

theorem Decay.mono {σ : Mat k r → (H →L[ℂ] H)} {V V' : Set H} {a : ℝ} (h : Decay σ V a) (hV : V' ⊆ V) :
    Decay σ V' a := fun u hu v hv => h u (hV hu) v (hV hv)

theorem Greg_subset (z z' : Fin (2 * r + k + 1) → ℂ) : Greg k r z z' ⊆ GG k r := fun _ hγ => hγ.1

end GlobalTheory.SgInf
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.SemilocalFrames.OfRoots
section
noncomputable section

open scoped Classical

namespace GlobalTheory.LoopV

open NumberField Matrix Formalism.MainNotions.S

variable {K : Type} [Field K] {N : ℕ}

def StrUp (x : Matrix (Fin N) (Fin N) K) : Prop := ∀ i j, j ≤ i → x i j = 0

def StrLo (x : Matrix (Fin N) (Fin N) K) : Prop := ∀ i j, i ≤ j → x i j = 0

def expT (x : Matrix (Fin N) (Fin N) K) : Matrix (Fin N) (Fin N) K :=
  ∑ i ∈ Finset.range N, ((i.factorial : K)⁻¹) • x ^ i

def stabU (Z : Matrix (Fin N) (Fin N) K) : Set (Matrix (Fin N) (Fin N) K) :=
  {a | IsUpUni a ∧ IsLoUni (Z * a * Z⁻¹)}

def lieU (Z : Matrix (Fin N) (Fin N) K) : Set (Matrix (Fin N) (Fin N) K) :=
  {x | StrUp x ∧ StrLo (Z * x * Z.adjugate)}

def roots (w : Matrix (Fin N) (Fin N) K) : Finset (Fin N × Fin N) :=
  Finset.univ.filter fun q => q.1 < q.2 ∧ ∃ i j, j < i ∧ w i q.1 ≠ 0 ∧ w j q.2 ≠ 0

def ofRoots (R : Finset (Fin N × Fin N)) (c : R → ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  fun i j => if h : (i, j) ∈ R then c ⟨(i, j), h⟩ else if i = j then 1 else 0

def EntIn [NumberField K] (I : Ideal (𝓞 K)) (x : Matrix (Fin N) (Fin N) K) : Prop :=
  ∀ i j, ∃ o ∈ I, ((o : 𝓞 K) : K) = x i j

end GlobalTheory.LoopV

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ToGlob0
section
noncomputable section

namespace GlobalTheory.Diag.PG

open Formalism.BasicNotions

variable (D : D7)

structure Glob0 (x eps CD Cg : ℝ) : Prop where
  nums : RankNums x eps CD D.R.m D.R.f D.R.k (Real.log D.host.rdE) (D.s.Del : ℝ)
  g_win : ∀ i, ((D.R.k : ℝ) * bx x eps) ^ 8 ≤ (D.host.g i : ℝ) ∧ (D.host.g i : ℝ) ≤ bx x eps ^ Cg
  gap : ∀ τ (j : ℕ) (h : j + 1 < D.R.m), x ^ (eps / 100) * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 * x ^ eps ≤
    (((D.hc τ).b ⟨j + 1, h⟩ - (D.hc τ).b ⟨j, by omega⟩ : ℚ) : ℝ)
  cloud : ∀ τ (i : Fin (D.R.k - 1)), 0 ≤ (((D.hc τ).v i : ℚ) : ℝ) ∧
    (((D.hc τ).v i : ℚ) : ℝ) ≤ 4 * (D.R.k : ℝ) * (D.s.Del : ℝ)
  off : ∀ τ, ¬ Top D τ → 4 * (D.R.k : ℝ) * (D.s.Del : ℝ) ≤ uFirst D τ - vFirst D τ ∧
    uFirst D τ - vFirst D τ ≤ 8 * (D.R.k : ℝ) * (D.s.Del : ℝ) ∧ uLast D τ = vLast D τ - 1 / 2
  rd_lo : 2 ≤ D.host.rdE

def DuWin (C0 : ℝ) : Prop :=
  ∀ u, (D.mem u).A.GamP ^ (-2 : ℤ) * D.what₂.Dstar / C0 ≤ (D.duS u : ℝ) ∧
    (D.duS u : ℝ) ≤ (D.mem u).A.GamP ^ (-2 : ℤ) * D.what₂.Dstar * C0

variable {D}

end GlobalTheory.Diag.PG

end
end

