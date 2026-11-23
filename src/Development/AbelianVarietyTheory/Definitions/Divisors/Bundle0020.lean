module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.SlopeBoundOfConditionsWithErrorForFrames
public import Formalism.SharpRestriction.Divisibility.WeightThresholdDefs
public import Formalism.LocalRingCardinality.DataParams₂
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RealCusp
public import GroundTheory.AutomorphicForms.Bundle0022
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.DividedWeightUnique
section
open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions Formalism.L2.Indef.Tree NumberField

noncomputable section

namespace GlobalTheory.MeanTop

structure Wts (ι : Type) (N : ℕ) where

  kc : ℕ

  p : ℕ

  T : ℕ

  Dd : ℕ

  c0 : ℤ

  h0 : ℤ

  S : ℝ

  eta : ℝ

  b : ℝ

  w : ι → ℝ

  u : ι → Fin N → ℤ

  u1 : ι → Fin N → ℤ

namespace Wts

variable {ι : Type} {N : ℕ} (W : Wts ι N)

def u' : ι → Fin N → ℤ := fun τ i => if (i : ℕ) < W.p then W.u1 τ i else W.u1 τ i + 3 * (N : ℤ)

def g : ℝ := (W.h0 : ℝ) / (4 * W.T)

def IsDiv : Prop :=
  ∀ τ, (∀ a : Fin N, (a : ℕ) + 1 = W.kc → W.u1 τ a = 0) ∧ ∀ a b : Fin N, (b : ℕ) = a + 1 →
    W.u1 τ a - W.u1 τ b =
      (W.u τ a - W.u τ b + if (b : ℕ) = W.p then -W.c0 - (2 * (N : ℤ) - 2) else 2) / ((W.T : ℤ) + W.Dd + 1)

structure Hyp : Prop where
  kc_pos : 1 ≤ W.kc
  kc_lt : W.kc < W.p
  p_lt : W.p < N
  small : N - W.p < W.p
  weightConst_nonneg : 0 ≤ W.c0
  anchor : ∀ τ (a : Fin N), (a : ℕ) + 1 = W.kc → W.u τ a = 0
  h1 : 4 * W.Dd + 4 ≤ W.T
  h2 : 4 * (W.c0 + 2 * N + W.T + W.Dd + 1) ≤ W.h0 ∧ 24 * (N : ℤ) * W.T ≤ W.h0
  h3node : ∀ τ (a : Fin N), W.kc ≤ (a : ℕ) → |(W.u τ a : ℝ) + W.w τ| ≤ W.eta + W.S + N
  h3cloud : ∀ τ (a : Fin N), (a : ℕ) < W.kc → 0 ≤ W.u τ a ∧ (W.u τ a : ℝ) ≤ W.S
  h3w : ∀ τ, 4 * ((W.eta + W.S + N) + W.S + W.c0 + 2 * N) + 20 * N * W.T ≤ W.w τ
  h4 : ∀ τ (a b : Fin N), (b : ℕ) = a + 1 →
    ((b : ℕ) ≠ W.p → ((W.T : ℤ) + W.Dd + 2) * ((W.T : ℤ) + W.Dd + 2 + 2 * N) ≤ W.u τ a - W.u τ b + 2) ∧
    (W.kc ≤ (a : ℕ) → W.h0 - 1 ≤ W.u τ a - W.u τ b) ∧ ((b : ℕ) = W.p → W.h0 ≤ W.u τ a - W.u τ b)
  h5 : ∀ τ a, |(W.u τ a : ℝ)| + W.c0 + 4 * N ≤ 2 * W.b

end Wts

def l1 {ι : Type} [Fintype ι] {N : ℕ} (v : ι → Fin N → ℤ) : ℝ := ∑ τ, ∑ i, |(v τ i : ℝ)|

def reWt {ι : Type} {N : ℕ} (v : ι → Fin N → ℤ) : ι → Fin N → ℝ := fun τ i => (v τ i : ℝ)

def vDiff (D : D7) (p : ℕ) : ℝ := (padicValNat p (WeightThresholdDefs.dE D) : ℝ) / (Module.finrank ℚ D.host.E : ℝ)

structure Shifts where

  Pe : Finset ℕ

  e : ℕ → ℝ

  C7 : ℝ

  Pa : ℝ

  Pinf : ℝ

  PPe : ℝ

  XW : ℝ

variable {D : D7} (Y : ShimX D.what₂.Tau) {K : Type} [Field K] [NumberField K] [StarRing K] {P : SlopeBoundParameters}

def bZero (W : Wts D.what₂.Tau Y.N) : ℝ := WeightThresholdDefs.bigB0 Y (reWt W.u') W.g

def totalShift (W : Wts D.what₂.Tau Y.N) (A : Shifts) : ℝ :=
  (∑ p ∈ A.Pe, A.e p * Real.log p) +
    (∑ p ∈ GlobalTheory.FlagAr.setB Y (bZero Y W), (WeightThresholdDefs.cP p + A.C7 * vDiff D p) * (l1 W.u' + A.Pa) * Real.log p) +
    (l1 W.u1 + 6 * A.Pinf) / 2

end GlobalTheory.MeanTop

namespace GlobalTheory.MeanTop.Inhab

open Filter Topology

def wts (ι : Type) (N kc p T Dd c0 G V : ℕ) (b : ℝ) : Wts ι N where
  kc := kc
  p := p
  T := T
  Dd := Dd
  c0 := c0
  h0 := ((T : ℤ) + Dd + 1) * G - 1
  S := ((T : ℝ) + Dd + 1) * G * N
  eta := 2 * N + c0
  b := b
  w := fun _ => ((T : ℝ) + Dd + 1) * V
  u := fun _ i => (((T : ℤ) + Dd + 1) * G - 1) * ((kc : ℤ) - 1 - (i : ℕ)) -
    (if kc ≤ (i : ℕ) then ((T : ℤ) + Dd + 1) * V else 0) - (if p ≤ (i : ℕ) then 2 * (N : ℤ) + c0 else 0)
  u1 := fun _ i => (G : ℤ) * ((kc : ℤ) - 1 - (i : ℕ)) - (if kc ≤ (i : ℕ) then (V : ℤ) else 0)

theorem dividedWeight_unique {ι : Type} {N : ℕ} (W : Wts ι N) (v : ι → Fin N → ℤ) (hk : 1 ≤ W.kc) (hN : W.kc ≤ N) (h : W.IsDiv)
    (h' : Wts.IsDiv { W with u1 := v }) : v = W.u1 := by
  funext τ
  have step : ∀ a c : Fin N, (c : ℕ) = a + 1 → v τ a - W.u1 τ a = v τ c - W.u1 τ c := fun a c hc => by
    have e1 := (h τ).2 a c hc
    have e2 := (h' τ).2 a c hc
    simp only at e2
    omega
  have hN0 : 0 < N := by omega
  have all : ∀ n (hn : n < N), v τ ⟨n, hn⟩ - W.u1 τ ⟨n, hn⟩ = v τ ⟨0, hN0⟩ - W.u1 τ ⟨0, hN0⟩ := by
    intro n
    induction n with
    | zero => intro _; rfl
    | succ n ih => intro hn; rw [← ih (by omega)]; exact (step ⟨n, by omega⟩ ⟨n + 1, hn⟩ rfl).symm
  have a1 := (h τ).1 ⟨W.kc - 1, by omega⟩ (by simp only; omega)
  have a2 := (h' τ).1 ⟨W.kc - 1, by omega⟩ (by simp only; omega)
  simp only at a2
  have a3 := all (W.kc - 1) (by omega)
  funext i
  have a4 := all i i.isLt
  simp only [Fin.eta] at a4
  omega

theorem f_pos (D : D7) : 1 ≤ D.R.f := by
  have := D.R.two_le_m
  have := D.R.m_le_f
  show 1 ≤ 2 * D.R.ord
  omega

end GlobalTheory.MeanTop.Inhab
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsOb1NeZero
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Obs.Model

section General

variable {R R₀ : Type} [CommRing R] [CommRing R₀] {I : Ideal R} {π : R →+* R₀}

variable (hI : I ^ 2 = 0) (hs : Function.Surjective π) (hk : RingHom.ker π = I)

include hI in
theorem mul_eq_zero_of_mem {a b : R} (ha : a ∈ I) (hb : b ∈ I) : a * b = 0 := by
  have := Ideal.mul_mem_mul ha hb
  rw [← pow_two, hI] at this
  simpa using this

variable {R₁ : Type} [CommRing R₁] [Algebra R₀ R₁]



include hI hs in
theorem exists_isSig (α : Aug I π R₁) {B B₀ : Type} [CommRing B] [Algebra R B] [CommRing B₀] [Algebra R₀ B₀]
    (p : B →+* B₀) (semi : SemiHom π p) (surj : Function.Surjective p)
    (ker : ∀ b, p b = 0 ↔ b ∈ I.map (algebraMap R B)) : ∃ σ, α.IsSig p σ := by
  have key : ∀ (y : R₁) (b b' : B), p b = p b' → α.k y • b = α.k y • b' := by
    intro y b b' h
    have h0 : b - b' ∈ I.map (algebraMap R B) := (ker _).1 (by rw [map_sub, h, sub_self])
    rw [← sub_eq_zero, ← smul_sub, Algebra.smul_def]
    exact mul_eq_zero_of_mem (map_sq hI B) (Ideal.mem_map_of_mem _ (α.mem y)) h0
  have e := Function.surjInv_eq surj
  let f : R₁ →+ B₀ →+ B := AddMonoidHom.mk' (fun y ↦ AddMonoidHom.mk' (fun b ↦ α.k y • Function.surjInv surj b)
    fun b b' ↦ by rw [← smul_add]; exact key _ _ _ (by rw [map_add (f := _), e, e, e])) fun y y' ↦ by
      ext b; simp [add_smul]
  refine ⟨TensorProduct.liftAddHom f fun r y b ↦ ?_, fun y b ↦ ?_⟩
  · obtain ⟨r, rfl⟩ := hs r
    change α.k (π r • y) • Function.surjInv surj b = α.k y • Function.surjInv surj (π r • b)
    rw [α.smul, mul_comm, mul_smul]
    exact key _ _ _ (by rw [semi, e, e])
  · exact key _ _ _ (e _)

variable {C C' : Type} [Category.{0} C] [Category.{0} C'] {F : C ⥤ CommAlgCat.{0} R₀} {F' : C' ⥤ CommAlgCat.{0} R₀}



end General

section Unique

variable {R R₀ : Type} [CommRing R] [CommRing R₀] {I : Ideal R} {π : R →+* R₀} {R₁ : Type} [CommRing R₁] [Algebra R₀ R₁]

variable {C C' : Type} [Category.{0} C] [Category.{0} C'] {F : C ⥤ CommAlgCat.{0} R₀} {F' : C' ⥤ CommAlgCat.{0} R₀}

end Unique

section Line

open Polynomial

variable {R R₀ : Type} [CommRing R] [CommRing R₀] {I : Ideal R} {π : R →+* R₀} {R₁ : Type} [CommRing R₁] [Algebra R₀ R₁]
variable (hI : I ^ 2 = 0) (hs : Function.Surjective π) (hk : RingHom.ker π = I)



variable {C : Type} [Category.{0} C]




end Line

end GlobalTheory.Obs.Model
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.LocPoly
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Polynomial GroundTheory.Automorphic UpperTheory.V
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin)
open UpperTheory.V.TR (Rinf Lie chart infGL pInf toL rmul invSet CuspSub)
open scoped ContDiff

namespace GlobalTheory.HenQ

section Fin

variable {K : Type} [Field K] [NumberField K] {n : ℕ}

end Fin

section Inf

variable {K : Type} [Field K] [NumberField K] {n : ℕ}


open Classical in
def pdL (v : InfinitePlace K) (i j : Fin n) (F : Lie K n → ℂ) (x : Lie K n) : ℂ :=
  fderiv ℝ F x (toL (Matrix.single i j (Pi.single v 1)))


def detD (v : InfinitePlace K) (F : Lie K n → ℂ) (x : Lie K n) : ℂ :=
  ∑ p : Equiv.Perm (Fin n), (((Equiv.Perm.sign p : ℤˣ) : ℤ) : ℂ) * (List.finRange n).foldr (fun j G => pdL v (p j) j G) F x

def IsTest (Φ : Lie K n → ℂ) : Prop := ContDiff ℝ ∞ Φ ∧ HasCompactSupport Φ ∧ tsupport Φ ⊆ invSet K n

variable [IsTotallyReal K]

end Inf

end GlobalTheory.HenQ
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.SlopeTestRemainingChoices
section
open MvPolynomial Formalism.DegreeFormula Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions Formalism.MainNotions.WeightThresholdDefs Filter Topology Classical

noncomputable section

namespace GlobalTheory.Mean4

open GlobalTheory.FlagPoly GlobalTheory.FlagAr

variable {D : D7} (Y : ShimX D.what₂.Tau)

abbrev Wt : Type := D.what₂.Tau → Fin Y.N → ℝ

abbrev Fn : Type := Pol D.what₂.Tau Y.N →ₗ[ℝ] ℝ

structure SlopeTestRemainingChoices where

  dir : Wt Y

  w : Y.Comp → ℝ

  Ps : ℝ → Y.Comp → MvPolynomial (Option (D.what₂.Tau × Fin Y.N)) ℝ

  ht : Y.ALB → Y.Pt → ℝ

  dense : Y.Comp → Set Y.Pt → Prop

def testI : ℝ := ∑ τ, degFl D.what₂.Tau Y.N (pLow Y.j τ 1 * curveCl D.what₂.Tau Y.N Y.j)

variable {Y} (A : SlopeTestRemainingChoices Y) (Φ : ℝ → Fn Y) (hh : Fn Y)


end GlobalTheory.Mean4
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.UnrOutside
section
noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host

namespace GlobalTheory.JSW

open GlobalTheory.CuspRep

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}


open Classical in
def sat (π : CG E a) (w : HeightOneSpectrum (𝓞 E)) : Multiset ℂˣ :=
  if h : ∃ B, π.HasSat w B then h.choose else 0

def UnrOutside (S : Finset (HeightOneSpectrum (𝓞 E))) (π : CG E a) : Prop := ∀ w ∉ S, ∃ B, π.HasSat w B

def locL (q : ℕ) (B B' : Multiset ℂˣ) (s : ℂ) : ℂ :=
  ((B ×ˢ B').map fun p : ℂˣ × ℂˣ => (1 - (p.1 : ℂ) * p.2 * (q : ℂ) ^ (-s))⁻¹).prod

def partialL (S : Finset (HeightOneSpectrum (𝓞 E))) {b : ℕ} (π : CG E a) (π' : CG E b) (s : ℂ) : ℂ :=
  ∏' w : {w : HeightOneSpectrum (𝓞 E) // w ∉ S}, locL (Ideal.absNorm w.1.asIdeal) (sat π w.1) (sat π' w.1) s

end GlobalTheory.JSW
end
end

