module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallyExistsFiniteSubsetNonzeroLocus

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.IntegralBound
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers

open scoped ComplexOrder

namespace GlobalTheory.HSCore

section Lattice

variable {K : Type} [Field K] [NumberField K]

def vecHt {n : ℕ} (a : Fin n → K) (c : (K →+* ℂ) → ℝ) : ℝ :=
  ((∑ᶠ v : FinitePlace K, Real.log (⨆ k, v (a k))) + ∑ τ : K →+* ℂ, Real.log (c τ)) / (Module.finrank ℚ K : ℝ)

end Lattice

section Geometry

variable {K : Type} [Field K] [NumberField K] (X : Data K) (s : Fin X.D → Fin X.N → K)

def filV (a : ℕ) : Submodule K (X.V X.T) := (Fil (X.ideal s) a (spaceV X s)).comap (X.V X.T).subtype

variable {X s}

def symV {hs : X.IsGood s} {δ : ℕ} (Co : Coord X.toGeo hs δ) (a : ℕ) :
    filV X s a →ₗ[K] (MonoDeg (Fin X.D) a × Fin δ → K) :=
  if h : a ≤ X.T then
    (LinearMap.pi fun q : MonoDeg (Fin X.D) a × Fin δ =>
      (LinearMap.proj q.2 : (Fin δ → K) →ₗ[K] K) ∘ₗ (Co.ev (X.T - a)).toLinearMap ∘ₗ LinearMap.proj q.1) ∘ₗ
      hs.sym (Nat.sub_add_cancel h) (spaceV X s) ∘ₗ (X.V X.T).subtype.restrict fun _ hx => hx
  else 0

def Coord.gen {G : Geo K} {s : Fin G.D → Fin G.N → K} {hs : G.IsGood s} {δ : ℕ} (Co : Coord G hs δ) (k : Fin G.n) (p : Fin δ) : K :=
  ∑ j, G.w j k * Co.y p j

def Coord.c₁ {G : Geo K} {s : Fin G.D → Fin G.N → K} {hs : G.IsGood s} {δ : ℕ} (Co : Coord G hs δ) (σ : K →+* ℂ) (p : Fin δ) : ℝ :=
  archSize (G.A σ) fun k => σ (Co.y p k)


end Geometry

def RegSeq {Y : Scheme.{0}} {L : LB Y} (hL : L.IsLB) (F : Y.Modules) (t : List L.Sec) : Prop :=
  List.rec (motive := fun _ => Y.Modules → Prop) (fun _ => True)
    (fun a _ ih G => Mono (GlobalTheory.cutHom G hL a) ∧ ih (GlobalTheory.cut G hL a)) t F

theorem regSeq_cons {Y : Scheme.{0}} {L : LB Y} (hL : L.IsLB) (F : Y.Modules) (a : L.Sec) (r : List L.Sec) :
    RegSeq hL F (a :: r) ↔ Mono (GlobalTheory.cutHom F hL a) ∧ RegSeq hL (GlobalTheory.cut F hL a) r := Iff.rfl

def VanishFrom {Y : Scheme.{0}} (L : LB Y) (F : Y.Modules) (j₀ : ℤ) : Prop :=
  ∀ j : ℤ, j₀ ≤ j → ∀ q : ℕ, 0 < q → Subsingleton (coh (GlobalTheory.twistZ F L j) q)

end GlobalTheory.HSCore
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.JoinCastSucc
section
set_option autoImplicit false

noncomputable section

open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights GlobalTheory.ChowHt GlobalTheory.Adelic
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)

namespace GlobalTheory.HSChoice

def join {R : Type} {D N : ℕ} (u : Fin D → Fin N → R) (ξ : Fin N → R) : Fin (D + 1) × Fin N → R :=
  fun p => Fin.lastCases (motive := fun _ => R) (ξ p.2) (fun i => u i p.2) p.1

def spec {F E : Type} [CommRing F] [CommRing E] [Algebra F E] {D N : ℕ} (s : Fin D → Fin N → E)
    (f : MvPolynomial (Fin (D + 1) × Fin N) F) : MvPolynomial (Fin 1 × Fin N) E :=
  aeval (join (fun i j => C (s i j)) fun j => X (0, j)) f

def lin {K : Type} [CommRing K] {N : ℕ} (y : Fin N → K) : MvPolynomial (Fin 1 × Fin N) K := ∑ j, X ((0 : Fin 1), j) * C (y j)

def finPart {K ι : Type} [Field K] [NumberField K] (g : MvPolynomial ι K) : ℝ :=
  (∑ᶠ v : FinitePlace K, Real.log (gaussAbs v g)) / (Module.finrank ℚ K : ℝ)

def mean (K : Type) [Field K] [NumberField K] (a : (K →+* ℂ) → ℝ) : ℝ := (∑ τ, a τ) / (Module.finrank ℚ K : ℝ)

structure ShortLat {F : Type} [Field F] [NumberField F] {N n : ℕ} (w : Matrix (Fin N) (Fin n) F)
    (A : (F →+* ℂ) → Matrix (Fin N) (Fin N) ℂ) (Λ : ℝ) : Prop where
  pos : 0 < N
  spans : Submodule.span F (Set.range w.col) = ⊤
  int : ∀ u ∈ Submodule.span (𝓞 F) (Set.range w.col), u ∈ Submodule.span ℤ (Set.range w.col)
  det : ∀ σ, (A σ).det ≠ 0
  conj : ConjCompat A
  le : ∀ k σ, frameNorm (A σ) (fun j => σ (w j k)) ≤ Λ
  one_le : 1 ≤ Λ

def NoSquare {K : Type} [Field K] {N : ℕ} (g : MvPolynomial (Fin 1 × Fin N) K) : Prop :=
  g ≠ 0 ∧ ∀ y : Fin N → K, y ≠ 0 → ¬ lin y ^ 2 ∣ g

theorem join_last {R : Type} {D N : ℕ} (u : Fin D → Fin N → R) (ξ : Fin N → R) (j : Fin N) : join u ξ (Fin.last D, j) = ξ j := by
  simp [join]

theorem join_castSucc {R : Type} {D N : ℕ} (u : Fin D → Fin N → R) (ξ : Fin N → R) (i : Fin D) (j : Fin N) :
    join u ξ (i.castSucc, j) = u i j := by
  simp [join]

namespace Check

theorem lin_ne {K : Type} [Field K] {N : ℕ} {y : Fin N → K} (hy : y ≠ 0) : lin y ≠ 0 := by
  intro h
  apply hy
  funext j
  have := congrArg (eval (fun p : Fin 1 × Fin N => if p.2 = j then (1:K) else 0)) h
  simpa [lin] using this

end Check

end GlobalTheory.HSChoice
end
end

