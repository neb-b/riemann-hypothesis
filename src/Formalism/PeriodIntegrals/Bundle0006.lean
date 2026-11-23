module

public import Mathlib

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.PhiCubeOfFactor
section
noncomputable section

open Classical

namespace PI.PhiCubeOfFactor

def IsIntP {p : ℕ} [Fact p.Prime] (x : ℂ_[p]) : Prop := ‖x‖ ≤ 1

def IntegralMv {σ : Type*} {p : ℕ} [Fact p.Prime] (F : MvPowerSeries σ ℂ_[p]) : Prop :=
  ∀ n, IsIntP (MvPowerSeries.coeff n F)

abbrev Xv {p : ℕ} [Fact p.Prime] {σ : Type*} (i : σ) : MvPowerSeries σ ℂ_[p] := MvPowerSeries.X i

section

variable {p : ℕ} [Fact p.Prime] (l ex : PowerSeries ℂ_[p]) {σ : Type*}

def lg (a : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] := PowerSeries.subst a l

def pt (x : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] := PowerSeries.subst x ex

def add (a b : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] := pt ex (lg l a + lg l b)

def sub (a b : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] := pt ex (lg l a - lg l b)

end

def logMv {σ : Type*} {p : ℕ} [Fact p.Prime] (F : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] :=
  fun α => ∑ n ∈ Finset.range ((α.sum fun _ k => k) + 1),
    if n = 0 then 0 else (-1 : ℂ_[p]) ^ (n + 1) * MvPowerSeries.coeff α ((F - 1) ^ n) / (n : ℂ_[p])

def expMv {σ : Type*} {p : ℕ} [Fact p.Prime] (F : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] :=
  fun α => ∑ n ∈ Finset.range ((α.sum fun _ k => k) + 1),
    MvPowerSeries.coeff α (F ^ n) / (n.factorial : ℂ_[p])

def Simeq {σ : Type*} {p : ℕ} [Fact p.Prime] (f g : MvPowerSeries σ ℂ_[p]) : Prop :=
  MvPowerSeries.constantCoeff (f - g) = 0 ∧ IntegralMv (expMv (f - g))

def phAt {p : ℕ} [Fact p.Prime] {σ : Type*} (E : PowerSeries ℂ_[p]) (a : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] :=
  PowerSeries.subst a (-logMv E : PowerSeries ℂ_[p])

def eAt {p : ℕ} [Fact p.Prime] {σ : Type*} (E : PowerSeries ℂ_[p]) (a : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] :=
  PowerSeries.subst a E

def Lemma : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (l ex E : PowerSeries ℂ_[p]) (Q : MvPowerSeries (Fin 2) ℂ_[p]),
    PowerSeries.constantCoeff ex = 0 → PowerSeries.subst ex l = PowerSeries.X →
    PowerSeries.constantCoeff E = 1 →
    add l ex (Xv 0) (Xv 1) * sub l ex (Xv 0) (Xv 1) * eAt E (add l ex (Xv 0) (Xv 1)) *
        eAt E (sub l ex (Xv 0) (Xv 1)) =
      Q * eAt E (Xv 0 : MvPowerSeries (Fin 2) ℂ_[p]) ^ 2 * eAt E (Xv 1 : MvPowerSeries (Fin 2) ℂ_[p]) ^ 2 →
    (∃ n : MvPowerSeries (Fin 2) ℂ_[p], IntegralMv n ∧ MvPowerSeries.constantCoeff n = 1 ∧
      Q = add l ex (Xv 0) (Xv 1) * sub l ex (Xv 0) (Xv 1) * n) →
    Simeq (phAt E (add l ex (Xv 0) (Xv 1)) + phAt E (sub l ex (Xv 0) (Xv 1)) : MvPowerSeries (Fin 2) ℂ_[p])
      (2 * phAt E (Xv 0) + 2 * phAt E (Xv 1))

end PI.PhiCubeOfFactor
end
end

-- bundled from Formalism.PeriodIntegrals.QuotInv
section
open MeasureTheory Matrix
open scoped ENNReal

noncomputable section

namespace PI

abbrev MtM (m : ℕ) := Fin m → Fin m → ℂ

def lmulQ {m : ℕ} (a : Matrix (Fin m) (Fin m) ℂ) (x : MtM m) : MtM m := a * Matrix.of x

def rmulQ {m : ℕ} (a : Matrix (Fin m) (Fin m) ℂ) (x : MtM m) : MtM m := Matrix.of x * a

def IsMatGroup {m : ℕ} (G : Set (Matrix (Fin m) (Fin m) ℂ)) : Prop :=
  IsClosed G ∧ (1 : Matrix (Fin m) (Fin m) ℂ) ∈ G ∧ (∀ a ∈ G, ∀ b ∈ G, a * b ∈ G) ∧
    ∀ a ∈ G, a⁻¹ ∈ G ∧ a * a⁻¹ = 1

def IsHaarOnM {m : ℕ} (S : Set (Matrix (Fin m) (Fin m) ℂ)) (μ : Measure (MtM m)) : Prop :=
  SigmaFinite μ ∧ μ ≠ 0 ∧ μ {x | Matrix.of x ∉ S} = 0 ∧
    ∀ s ∈ S, μ.map (lmulQ s) = μ

def IsRightInvM {m : ℕ} (S : Set (Matrix (Fin m) (Fin m) ℂ)) (μ : Measure (MtM m)) : Prop :=
  ∀ s ∈ S, μ.map (rmulQ s) = μ

def IsQuotM {m : ℕ} (μG μS ν : Measure (MtM m)) : Prop :=
  ∀ f : MtM m → ℝ≥0∞, Measurable f →
    ∫⁻ x, f x ∂μG = ∫⁻ x, (∫⁻ s, f (fun i j => (Matrix.of s * Matrix.of x) i j) ∂μS) ∂ν

def QuotientSetting {m : ℕ} (G S : Set (Matrix (Fin m) (Fin m) ℂ)) (μG μS ν : Measure (MtM m)) : Prop :=
  IsMatGroup G ∧ IsMatGroup S ∧ S ⊆ G ∧ IsHaarOnM G μG ∧ IsHaarOnM S μS ∧ IsRightInvM G μG ∧ IsRightInvM S μS ∧
    IsQuotM μG μS ν

def QuotInv : Prop :=
  ∀ (m : ℕ) (G S : Set (Matrix (Fin m) (Fin m) ℂ)) (μG μS ν : Measure (MtM m)), QuotientSetting G S μG μS ν →
    ∀ F : MtM m → ℝ≥0∞, Measurable F →
      (∀ s ∈ S, ∀ x : MtM m, Matrix.of x ∈ G → F (fun i j => (s * Matrix.of x) i j) = F x) →
      ∀ g ∈ G, ∫⁻ x, F (fun i j => (Matrix.of x * g) i j) ∂ν = ∫⁻ x, F x ∂ν

end PI

end
end

-- bundled from Formalism.PeriodIntegrals.QuotNuSigma
section
noncomputable section

open MeasureTheory
open scoped ENNReal

namespace PI.QuotNuSigma

def Target : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    (μG : Measure G) [IsFiniteMeasureOnCompacts μG] (A B : Set G) (μA μB ν : Measure G),
    (SigmaFinite μA ∧ μA ≠ 0 ∧ μA Aᶜ = 0 ∧ ∀ s ∈ A, μA.map (fun x => s * x) = μA) →
    (SigmaFinite μB ∧ μB ≠ 0 ∧ μB Bᶜ = 0 ∧ ∀ s ∈ B, μB.map (fun x => s * x) = μB) →
    (∀ f : G → ℝ≥0∞, Measurable f →
      ∫⁻ x, f x ∂μG = ∫⁻ x, (∫⁻ s, f (s * x) ∂((μA.prod μB).map (fun p => p.1 * p.2))) ∂ν) →
    SigmaFinite ν

end PI.QuotNuSigma
end
end

-- bundled from Formalism.PeriodIntegrals.RhsWLim
section
noncomputable section

open MeasureTheory Filter Topology Matrix
open scoped ENNReal ContDiff

namespace PI.RhsWLim

def UH {ι : Type*} [Fintype ι] [DecidableEq ι] (H : Matrix ι ι ℂ) : Set (Matrix ι ι ℂ) :=
  {g | gᴴ * H * g = H}

def eI (k r : ℕ) (a : Fin r) : Fin (2 * r + k + 1) := ⟨a.val, by omega⟩

def esI (k r : ℕ) (a : Fin r) : Fin (2 * r + k + 1) := ⟨2 * r + k - a.val, by omega⟩

def Hpk (k r : ℕ) : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ := fun i j =>
  if i.val < r ∧ i.val + j.val = 2 * r + k then 1
  else if j.val < r ∧ i.val + j.val = 2 * r + k then 1
  else if r ≤ i.val ∧ i.val ≤ r + k ∧ i = j then (if i.val = r + k then -1 else 1)
  else 0

def bvec {m : ℕ} (i : Fin m) : Fin m → ℂ := Pi.single i 1

abbrev Mt (k r : ℕ) := Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → ℂ

def lmulM {k r : ℕ} (a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (x : Mt k r) : Mt k r :=
  a * Matrix.of x

abbrev Mat (k r : ℕ) := Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ

abbrev GV (k r : ℕ) : Set (Mat k r) := UH (Hpk k r)

def UWb (k r : ℕ) : Set (Mat k r) :=
  {g | g ∈ GV k r ∧ ∀ a : Fin r, g *ᵥ bvec (eI k r a) = bvec (eI k r a) ∧ g *ᵥ bvec (esI k r a) = bvec (esI k r a)}

def IsHaarOn {k r : ℕ} (S : Set (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ))
    (μ : Measure (Mt k r)) : Prop :=
  SigmaFinite μ ∧ μ ≠ 0 ∧ μ {x | Matrix.of x ∉ S} = 0 ∧
    ∀ s ∈ S, μ.map (lmulM s) = μ

def realifyFun {m : ℕ} (X : Matrix (Fin m) (Fin m) ℂ) : Fin m × Fin m × Bool → ℝ :=
  fun p => if p.2.2 then (X p.1 p.2.1).im else (X p.1 p.2.1).re

def unrealify {m : ℕ} (x : EuclideanSpace ℝ (Fin m × Fin m × Bool)) : Matrix (Fin m) (Fin m) ℂ :=
  fun i j => ⟨x (i, j, false), x (i, j, true)⟩

def lieOf {m : ℕ} (S : Set (Matrix (Fin m) (Fin m) ℂ)) : Set (Matrix (Fin m) (Fin m) ℂ) :=
  {X | ∀ t : ℝ, NormedSpace.exp ((t : ℂ) • X) ∈ S}

def lieE {m : ℕ} (S : Set (Matrix (Fin m) (Fin m) ℂ)) : Submodule ℝ (EuclideanSpace ℝ (Fin m × Fin m × Bool)) :=
  Submodule.span ℝ ((fun X => (WithLp.equiv 2 _).symm (realifyFun X)) '' lieOf S)

def wI (k r : ℕ) (j : Fin (k + 1)) : Fin (2 * r + k + 1) := ⟨r + j.val, by omega⟩

def herm {ι : Type*} [Fintype ι] (H : Matrix ι ι ℂ) (v w : ι → ℂ) : ℂ := star w ⬝ᵥ (H *ᵥ v)

def inWb (k r : ℕ) (v : Fin (2 * r + k + 1) → ℂ) : Prop :=
  ∀ i : Fin (2 * r + k + 1), (i.val < r ∨ r + k < i.val) → v i = 0

def Tz (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) : ℝ := -(herm (Hpk k r) z z).re

def UWset (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) :
    Set (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :=
  {g | g ∈ UH (Hpk k r) ∧
    (∀ a : Fin r, g *ᵥ bvec (eI k r a) = bvec (eI k r a) ∧ g *ᵥ bvec (esI k r a) = bvec (esI k r a)) ∧
    g *ᵥ z = z}

def Hb (k : ℕ) : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ :=
  Matrix.diagonal fun j => if j = Fin.last k then -1 else 1

def wbPart (k r : ℕ) (v : Fin (2 * r + k + 1) → ℂ) : Fin (k + 1) → ℂ := fun j => v (wI k r j)

def IsSection (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) :
    Prop :=
  (∀ i j : Fin (k + 1), ContDiffOn ℝ ∞ (fun ζ => μsec ζ i j) {ζ : ℂ | Tz k r z * Tz k r z' < Complex.normSq ζ}) ∧
  ∀ ζ : ℂ, Tz k r z * Tz k r z' < Complex.normSq ζ →
    Matrix.conjTranspose (μsec ζ) * Hb k * μsec ζ = Hb k ∧ herm (Hb k) (μsec ζ *ᵥ wbPart k r z') (wbPart k r z) = ζ

def embWb (k r : ℕ) (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) : Mat k r := fun i j =>
  if h : (r ≤ i.val ∧ i.val ≤ r + k) ∧ (r ≤ j.val ∧ j.val ≤ r + k) then μ ⟨i.val - r, by omega⟩ ⟨j.val - r, by omega⟩
  else if i = j ∧ ¬ (r ≤ i.val ∧ i.val ≤ r + k) then 1 else 0

def zWeight (k : ℕ) (T T' : ℝ) (ζ : ℂ) : ℝ :=
  if T * T' ≤ Complex.normSq ζ then (Complex.normSq ζ - T * T') ^ (k - 1) else 0

def volU (j : ℕ) : ℝ := ∏ i ∈ Finset.range j, (2 * Real.pi) ^ (i + 1) / (i.factorial : ℝ)

def wbConst (k : ℕ) (T T' a a' : ℝ) : ℝ :=
  2 * volU k ^ 2 / ((T * T') ^ k * volU (k - 1) * a * a')

variable {k r : ℕ}

def expBall (S : Set (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)) (ρ : ℝ) : Set (Mt k r) :=
  (fun x : lieE S =>
      fun i j => NormedSpace.exp (unrealify (x : EuclideanSpace ℝ _)) i j) '' Metric.ball 0 ρ

def rhsW (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (μW μW' : Measure (Mt k r))
    (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (φ : Mt k r → ℝ≥0∞) : ℝ≥0∞ :=
  ∫⁻ ζ : ℂ, ENNReal.ofReal (zWeight k (Tz k r z) (Tz k r z') ζ) *
    ∫⁻ h, ∫⁻ h', φ (fun i j => (Matrix.of h * embWb k r (μsec ζ) * (Matrix.of h')⁻¹) i j) ∂μW' ∂μW

def zeta0 (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) : ℂ := ((2 * Real.sqrt (Tz k r z * Tz k r z') : ℝ) : ℂ)

def mBase (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) :
    Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ :=
  embWb k r (μsec (zeta0 k r z z'))

def bBall (k r : ℕ) (ρ : ℝ) : Set (Mt k r) := expBall (k := k) (r := r) (UWb k r) ρ

def mBall (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (ρ : ℝ) :
    Set (Mt k r) :=
  {x | (fun i j => ((mBase k r z z' μsec)⁻¹ * Matrix.of x) i j) ∈ bBall k r ρ}

def bVol (k r : ℕ) (ρ : ℝ) : ℝ :=
  (volume (Metric.ball (0 : lieE (UWb k r)) ρ)).toReal

structure WbData (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (μW μW' : Measure (Mt k r)) (a a' : ℝ)
    (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) : Prop where
  k_pos : 1 ≤ k
  z_mem : inWb k r z
  z'_mem : inWb k r z'
  T_pos : 0 < Tz k r z
  T'_pos : 0 < Tz k r z'
  haarW : IsHaarOn (UWset k r z) μW
  haarW' : IsHaarOn (UWset k r z') μW'
  a_pos : 0 < a
  a'_pos : 0 < a'
  massW : μW Set.univ = ENNReal.ofReal a
  massW' : μW' Set.univ = ENNReal.ofReal a'
  sec : IsSection k r z z' μsec

def RhsWLim : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (μW μW' : Measure (Mt k r)) (a a' : ℝ) μsec,
    WbData k r z z' μW μW' a a' μsec →
    Tendsto (fun ρ : ℝ => (rhsW k r z z' μW μW' μsec ((mBall k r z z' μsec ρ).indicator 1)).toReal / bVol k r ρ)
      (𝓝[>] 0) (𝓝 (wbConst k (Tz k r z) (Tz k r z') a a')⁻¹)

end PI.RhsWLim
end
end

-- bundled from Formalism.PeriodIntegrals.RowLetter
section
open MvPolynomial

noncomputable section

namespace PI.RL

def genM (R : Type) [CommRing R] (m : ℕ) :
    Matrix (Fin (m + 1)) (Fin (m + 1)) (MvPolynomial (Fin (m + 1) × Fin (m + 1)) R) :=
  Matrix.of fun a s => X (a, s)

def Nv (R : Type) [CommRing R] (m : ℕ) (vec : Bool) (c : Fin (m + 1)) :
    MvPolynomial (Fin (m + 1) × Fin (m + 1)) R :=
  if vec then X (c, 0) else (genM R m).adjugate (Fin.last m) c

def theta (R : Type) [CommRing R] (m : ℕ) (vec : Bool) :
    MvPolynomial (Fin (m + 1)) R →ₐ[R] MvPolynomial (Fin (m + 1) × Fin (m + 1)) R :=
  aeval (Nv R m vec)

def Hd (R : Type) [CommRing R] (k d : ℕ) : Submodule R (MvPolynomial (Fin k) R) :=
  restrictSupport R {μ | ∑ c, μ c = d}

def RE (K : Type) [CommRing K] (k : ℕ) (a b : Fin k) (f : MvPolynomial (Fin k × Fin k) K) : MvPolynomial (Fin k × Fin k) K :=
  ∑ t : Fin k, X (a, t) * pderiv (b, t) f

def TE (K : Type) [CommRing K] (k : ℕ) (vec : Bool) (d : ℕ) (a b : Fin k) (f : MvPolynomial (Fin k) K) : MvPolynomial (Fin k) K :=
  if vec then X a * pderiv b f else (if a = b then (d : K) • f else 0) - X b * pderiv a f

end PI.RL

namespace PI

open PI.RL

def RowLetter : Prop :=
  ∀ (K : Type) [Field K] (m : ℕ) (vec : Bool) (d : ℕ) (a b : Fin (m + 1)), ∀ P ∈ Hd K (m + 1) d,
    RE K (m + 1) a b (theta K m vec P) = theta K m vec (TE K (m + 1) vec d a b P)

end PI
end
end

-- bundled from Formalism.PeriodIntegrals.RowWtSpan
section
open MvPolynomial

noncomputable section

namespace PI.RW

def colW (r n : ℕ) : Fin r × Fin n → (Fin n → ℕ) := fun v => Pi.single v.2 1

def colAddGen (R : Type*) [CommRing R] {r n : ℕ} (l j : Fin n) :
    MvPolynomial (Fin r × Fin n) R →ₐ[R] MvPolynomial (Option (Fin r × Fin n)) R :=
  aeval fun v => if v.2 = j then X (some v) + X none * X (some (v.1, l)) else X (some v)

def dualWeyl (R : Type*) [CommRing R] (r n : ℕ) (ν : Fin n → ℕ) :
    Submodule R (MvPolynomial (Fin r × Fin n) R) :=
  weightedHomogeneousSubmodule R (colW r n) ν ⊓
    ⨅ (l : Fin n) (j : Fin n) (_ : l < j),
      LinearMap.ker ((colAddGen R (r := r) l j).toLinearMap -
        (rename (R := R) (some : Fin r × Fin n → Option (Fin r × Fin n))).toLinearMap)

def initMinor (R : Type*) [CommRing R] {r n s : ℕ} (I : Fin s → Fin r) (hs : s ≤ n) :
    MvPolynomial (Fin r × Fin n) R :=
  (Matrix.of fun p q : Fin s => (X (I p, Fin.castLE hs q) : MvPolynomial (Fin r × Fin n) R)).det

def bideterminant (R : Type*) [CommRing R] {r n K : ℕ} (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ n)
    (I : ∀ k, Fin (sz k) → Fin r) : MvPolynomial (Fin r × Fin n) R :=
  ∏ k : Fin K, initMinor R (I k) (hsz k)

def shapeDeg {n K : ℕ} (sz : Fin K → ℕ) (t : Fin n) : ℕ :=
  (Finset.univ.filter fun k : Fin K => t.val < sz k).card

def RE (K : Type) [CommRing K] (k : ℕ) (a b : Fin k) (f : MvPolynomial (Fin k × Fin k) K) : MvPolynomial (Fin k × Fin k) K :=
  ∑ t : Fin k, X (a, t) * pderiv (b, t) f

def BideterminantMem : Prop :=
  ∀ (R : Type) [CommRing R] (r n K : ℕ) (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ n)
    (I : ∀ k, Fin (sz k) → Fin r),
    bideterminant R sz hsz I ∈ dualWeyl R r n (shapeDeg sz)

def BideterminantSpan : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] (k n : ℕ) (ν : Fin n → ℕ),
    dualWeyl R k n ν ≤ Submodule.span R {f | ∃ (K : ℕ) (sz : Fin K → ℕ) (hsz : ∀ i, sz i ≤ n) (I : ∀ i, Fin (sz i) → Fin k),
      shapeDeg sz = ν ∧ (∀ i, StrictMono (I i)) ∧ f = bideterminant R sz hsz I}

end PI.RW

namespace PI

open PI.RW

def RowWtSpan : Prop :=
  ∀ (K : Type) [Field K] (m : ℕ) (ν : Fin (m + 1) → ℕ), Antitone ν →
    ∃ (J : Type) (b : J → MvPolynomial (Fin (m + 1) × Fin (m + 1)) K) (μ : J → Fin (m + 1) → ℕ),
      Submodule.span K (Set.range b) = dualWeyl K (m + 1) (m + 1) ν ∧
      (∀ i a, RE K (m + 1) a a (b i) = (μ i a : K) • b i) ∧ ∀ i a, μ i a ≤ ν 0

end PI
end
end

-- bundled from Formalism.PeriodIntegrals.SSAscent
section
namespace PI

namespace SSAscent

section Rep

variable {Γ : Type} [Group Γ] {k : Type} [Field k] {a : ℕ}

def IsInv (ρ : Γ →* GL (Fin a) k) (W : Submodule k (Fin a → k)) : Prop :=
  ∀ g, ∀ v ∈ W, (ρ g : Matrix (Fin a) (Fin a) k).mulVec v ∈ W

def IsSSRep (ρ : Γ →* GL (Fin a) k) : Prop :=
  ∀ W, IsInv ρ W → ∃ W', IsInv ρ W' ∧ IsCompl W W'

end Rep

def mapRep {Γ : Type} [Group Γ] {A B : Type} [CommRing A] [CommRing B] {a : ℕ} (f : A →+* B)
    (ρ : Γ →* GL (Fin a) A) : Γ →* GL (Fin a) B :=
  (Units.map (f.mapMatrix : Matrix (Fin a) (Fin a) A →+* Matrix (Fin a) (Fin a) B).toMonoidHom).comp ρ

end SSAscent

open SSAscent

def SSAscent : Prop :=
  ∀ (K L : Type) [Field K] [CharZero K] [Field L] [Algebra K L] (Γ : Type) [Group Γ] (a : ℕ)
    (ρ : Γ →* GL (Fin a) K), IsSSRep ρ → IsSSRep (mapRep (algebraMap K L) ρ)

end PI
end

-- bundled from Formalism.PeriodIntegrals.ScGapBig
section
namespace PI.ScGapBig

def rk48 (k r : ℕ) : ℕ := 2 * r + k + 1

def GapBig (k r : ℕ) (b : Fin (2 * r + 2) → ℝ) : Prop :=
  ∃ t : ℕ, Odd t ∧ rk48 k r + 5 ≤ t ∧ 1801 ≤ rk48 k r + t ∧
    ∀ (j : Fin (2 * r + 2)) (hj : j.val + 1 < 2 * r + 2),
      2 * ((rk48 k r + (2 * r + 2) * t : ℕ) : ℝ) ^ 3 + (t : ℝ) + 3 < b ⟨j.val + 1, hj⟩ - b j

def ScGapBig : Prop :=
  ∀ (k r : ℕ) (b : Fin (2 * r + 2) → ℝ), 1801 ≤ rk48 k r →
    (∀ (j : Fin (2 * r + 2)) (hj : j.val + 1 < 2 * r + 2),
      16 * (rk48 k r : ℝ) ^ 19 ≤ b ⟨j.val + 1, hj⟩ - b j) →
    GapBig k r b

end PI.ScGapBig
end

-- bundled from Formalism.PeriodIntegrals.SmithMat
section
namespace PI

open Matrix

def SmithDiag.{u} : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] (n : ℕ)
    (A : Matrix (Fin n) (Fin n) R),
    ∃ (U V : Matrix (Fin n) (Fin n) R) (d : Fin n → R),
      IsUnit U ∧ IsUnit V ∧ U * A * V = diagonal d

def SmithMat.{u} : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] (n : ℕ)
    (A : Matrix (Fin n) (Fin n) R),
    ∃ (U V : Matrix (Fin n) (Fin n) R) (d : Fin n → R),
      IsUnit U ∧ IsUnit V ∧ U * A * V = diagonal d ∧ ∀ i j, i ≤ j → d i ∣ d j

end PI
end

-- bundled from Formalism.PeriodIntegrals.SumAntidiagonalTuple
section
namespace PI

def SumAntidiagonalTuple : Prop :=
  ∀ D T : ℕ, D < T →
    ∑ k ∈ Finset.range (T - D), (Finset.Nat.antidiagonalTuple D k).card = Nat.choose (T - 1) D

end PI
end

