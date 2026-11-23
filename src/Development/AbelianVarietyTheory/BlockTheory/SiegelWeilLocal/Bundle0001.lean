module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0006

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.AutomorphicBallCount
section
open NumberField

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.AutomorphicBallCount

open Formalism.MainNotions.S GlobalTheory.Count

def ballSet (I : AutInst) (x : I.GA) (r : InfinitePlace I.F → ℝ) : Set I.GA :=
  {γ | γ ∈ I.GFset ∧ (x⁻¹ * γ * x).2 ∈ I.Kset ∧ ∀ v, dHS (uMat ((x⁻¹ * γ * x).1 v)) ≤ r v}

def bigA (I : AutInst) (x : I.GA) : ℝ :=
  (3 * Real.sqrt (I.n : ℝ) / (tau1 I x) ^ 2) ^ (2 * (I.n ^ 2 * I.f))

def AutBallCount : Prop :=
  ∀ (I : AutInst), 1 ≤ I.n → ∀ (x : I.GA) (r : InfinitePlace I.F → ℝ), (∀ v, 0 ≤ r v) →
    (ballSet I x r).Finite ∧
      ((ballSet I x r).ncard : ℝ) ≤ bigA I x * Real.exp (2 * (I.n : ℝ) ^ 2 * ∑ v, r v)

end GlobalTheory.IndefiniteRowSideFullHecke.AutomorphicBallCount
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.CenteredPerpendicularSets
section
open NumberField Matrix Finset

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.CenteredPerpendicularSets

open Formalism.MainNotions.S GlobalTheory.Count

section Lie

variable {A : Type} [CommRing A] {n : ℕ}

def perpSet (s : A →+* A) (J : Matrix (Fin n) (Fin n) A) (W : Submodule A (Fin n → A)) : Set (Fin n → A) :=
  {y | ∀ w ∈ W, Formalism.UG.hform s J w y = 0}

def IsSkew (s : A →+* A) (J Y : Matrix (Fin n) (Fin n) A) : Prop :=
  ∀ u u' : Fin n → A, Formalism.UG.hform s J (Y *ᵥ u) u' + Formalism.UG.hform s J u (Y *ᵥ u') = 0

def InNil (s : A →+* A) (J : Matrix (Fin n) (Fin n) A) (W : Submodule A (Fin n → A))
    (Y : Matrix (Fin n) (Fin n) A) : Prop :=
  IsSkew s J Y ∧ (∀ u, Y *ᵥ u ∈ perpSet s J W) ∧ (∀ u ∈ perpSet s J W, Y *ᵥ u ∈ W) ∧ ∀ u ∈ W, Y *ᵥ u = 0

def InCen (s : A →+* A) (J : Matrix (Fin n) (Fin n) A) (W : Submodule A (Fin n → A))
    (Y : Matrix (Fin n) (Fin n) A) : Prop :=
  InNil s J W Y ∧ ∀ u ∈ perpSet s J W, Y *ᵥ u = 0

end Lie

variable (I : AutInst)

def spanAt (R : Submodule (𝓞 I.E) (Fin I.n → I.E)) (v : InfinitePlace I.F) : Submodule ℂ (Fin I.n → ℂ) :=
  Submodule.span ℂ ((fun w : Fin I.n → I.E => fun i => I.φ v (w i)) '' (R : Set _))

def nilReal (R : Submodule (𝓞 I.E) (Fin I.n → I.E)) : Set (InfinitePlace I.F → Matrix (Fin I.n) (Fin I.n) ℂ) :=
  {Y | ∀ v, InNil (starRingEnd ℂ) (I.J.map (I.φ v)) (spanAt I R v) (Y v)}

def cenReal (R : Submodule (𝓞 I.E) (Fin I.n → I.E)) : Set (InfinitePlace I.F → Matrix (Fin I.n) (Fin I.n) ℂ) :=
  {Y | ∀ v, InCen (starRingEnd ℂ) (I.J.map (I.φ v)) (spanAt I R v) (Y v)}

def nilInt (x : I.GA) (R : Submodule (𝓞 I.E) (Fin I.n → I.E)) : Set (Matrix (Fin I.n) (Fin I.n) I.E) :=
  {Y | InNil (starRingEnd I.E) I.J (Submodule.span I.E (R : Set (Fin I.n → I.E))) Y ∧
    ∀ u ∈ lamX I x, Y *ᵥ u ∈ lamX I x}

def cenInt (x : I.GA) (R : Submodule (𝓞 I.E) (Fin I.n → I.E)) : Set (Matrix (Fin I.n) (Fin I.n) I.E) :=
  {Y | InCen (starRingEnd I.E) I.J (Submodule.span I.E (R : Set (Fin I.n → I.E))) Y ∧
    ∀ u ∈ lamX I x, Y *ᵥ u ∈ lamX I x}

def diagEmb (Y : Matrix (Fin I.n) (Fin I.n) I.E) : InfinitePlace I.F → Matrix (Fin I.n) (Fin I.n) ℂ :=
  fun v => Y.map (I.φ v)

def normAt (x : I.GA) (Y : InfinitePlace I.F → Matrix (Fin I.n) (Fin I.n) ℂ) : ℝ :=
  Real.sqrt (∑ v, Formalism.REAL.hs (uMat (x.1 v)⁻¹ * (I.P v)⁻¹ * Y v * I.P v * uMat (x.1 v)))

def nextSize {a : ℕ} (τ : Fin a → ℝ) (i : Fin a) : ℝ :=
  if h : (i : ℕ) + 1 < a then τ ⟨(i : ℕ) + 1, h⟩ else 1 / 2

end GlobalTheory.IndefiniteRowSideFullHecke.CenteredPerpendicularSets
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.CuspidalFrames
section
open MeasureTheory NumberField
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.CuspidalFrames

open Formalism.MainNotions.S GlobalTheory.Count

def IsCuspidalFrame (B : RowsAut) (Rφ : B.I.L2 B.μf B.fund →L[ℂ] B.I.L2 B.μf B.fund)
    (T : Fin B.D → (B.Hs →L[ℂ] B.I.L2 B.μf B.fund)) : Prop :=
  (∀ i, T i ∈ B.I.eHom B.σs B.μf B.fund B.R B.Re) ∧
    (∀ i, T i ∈ B.I.HomS B.σs B.μf B.fund B.R) ∧
    (∀ i u, ‖T i u‖ = ‖u‖) ∧
    (∀ i j, i ≠ j → ∀ u u', ⟪T i u, T j u'⟫_ℂ = 0) ∧
    Submodule.span ℂ (Set.range T) = B.I.eHom B.σs B.μf B.fund B.R B.Re ∧
    (∀ i u, B.I.IsCuspFn (B.I.muA B.μf) (B.I.ext (T i u))) ∧
    (∀ i u, ∀ k ∈ B.I.Kg B.g, B.R (1, k) (T i u) = T i u) ∧
    Orthonormal ℂ (fun i => T i (B.tens B.w)) ∧
    Submodule.span ℂ (Set.range fun i => T i (B.tens B.w)) = LinearMap.range Rφ.toLinearMap

end GlobalTheory.IndefiniteRowSideFullHecke.CuspidalFrames
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.DeepKernelBound
section
open MeasureTheory NumberField

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound

open Formalism.MainNotions.S GlobalTheory.Count

def dimN (B : RowsAut) : ℕ := B.I.n ^ 2 * B.I.f

def stepBe (n : ℕ) (b : ℝ) (P : ℕ) : ℝ :=
  Real.sqrt n * b ^ 2 + 3 / 2 * ((n : ℝ) * Real.sqrt n) + 3 * (P : ℝ)

def radRh (B : RowsAut) (q : ℕ) (τ : ℝ) : ℝ :=
  (B.I.n : ℝ) ^ 2 * Real.sqrt B.I.f * B.g * B.I.rd * (2 * τ) ^ ((1 : ℝ) / q) / 4

def DeepKernelBound : Prop :=
  ∀ (Cg : ℝ) (n₀ : ℕ) (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (p q : ℕ) (b : ℝ)
    (c : InfinitePlace B.I.F → ℝ) (x : B.I.GA),
    0 ≤ Cg → 8 ≤ n₀ → 1 ≤ q → CountHyp B Cg n₀ d p q b →
    (∀ v, IsGauge (B.I.ε v) (c v)) →
    least B.I x < tauStar B q b →
    (kern B.I (phe B d) x x).re ≤
      (2 * radRh B q (least B.I x) * Real.sqrt B.I.f *
            stepBe B.I.n b (8 * q * dimN B + dimN B)) ^ (16 * q * dimN B) *
        (6 * stepBe B.I.n b (8 * q * dimN B + dimN B)) ^ dimN B *
        Real.exp B.I.f *
        (17 * Real.sqrt B.I.n / least B.I x ^ 2) ^ (2 * dimN B) *
        (B.D : ℝ) * (∏ v, c v) / (B.μf (B.I.Kg B.g)).toReal

end GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.DeepSetBound
section
open MeasureTheory NumberField

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.DeepSet

open Formalism.MainNotions.S GlobalTheory.Count

def deepSet (B : RowsAut) (q : ℕ) (b : ℝ) : Set B.I.GA :=
  {x | x ∈ B.fund ∧ least B.I x < tauStar B q b}

def DeepBound : Prop :=
  ∀ Cg : ℝ, 0 ≤ Cg → ∃ n₀ : ℕ, ∀ (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (p q : ℕ) (b : ℝ),
    1 ≤ q → CountHyp B Cg n₀ d p q b →
      ∫⁻ x in deepSet B q b, ENNReal.ofReal (kern B.I (phe B d) x x).re ∂(B.I.muA B.μf) ≤
        ENNReal.ofReal ((B.D : ℝ) * Real.exp (-((B.I.n : ℝ) ^ 2 * (B.I.f : ℝ))))

end GlobalTheory.IndefiniteRowSideFullHecke.DeepSet
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.DefiniteFiniteCount
section
open NumberField MeasureTheory

namespace GlobalTheory.IndefiniteRowSideFullHecke.DefiniteFiniteCount

open Formalism.MainNotions.S GlobalTheory.Count

def DefiniteHyp (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (p : ℕ) : Prop :=
  IsDSData B d ∧ SigIs B p 0 ∧ 1 ≤ p ∧ 1 ≤ B.g ∧ B.g₀.Prime ∧ 4 * B.I.n < B.g₀ ∧
    (Ideal.primesOver (Ideal.span {(B.g₀ : ℤ)}) (𝓞 B.I.E)).ncard = Module.finrank ℚ B.I.E

theorem DefiniteHyp.rank_eq {B : RowsAut} {d : InfinitePlace B.I.F → ℝ} {p : ℕ}
    (h : DefiniteHyp B d p) : B.I.n = p := by
  obtain ⟨v⟩ : Nonempty (InfinitePlace B.I.F) := inferInstance
  obtain ⟨hp, hq⟩ := h.2.1 v
  unfold AutInst.pAt at hp
  unfold AutInst.qAt at hq
  have hall : ∀ a, B.I.ε v a = true := by
    intro a
    by_contra ha
    have hm : a ∈ (Finset.univ.filter fun a => B.I.ε v a = false) := by
      simpa using ha
    rw [Finset.card_eq_zero.mp hq] at hm
    simp at hm
  rw [← hp, Finset.filter_true_of_mem fun a _ => hall a]
  simp

end GlobalTheory.IndefiniteRowSideFullHecke.DefiniteFiniteCount
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.FarTermSum
section
open MeasureTheory NumberField
open scoped ENNReal

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.FarTermsModerate

open Formalism.MainNotions.S GlobalTheory.Count

variable (B : RowsAut)

def farSet (d : InfinitePlace B.I.F → ℝ) (x : B.I.GA) : Set B.I.GA :=
  {γ | γ ∈ B.I.GFset ∧ ¬ IsNear B d (epN B) x γ}

def farSum (d : InfinitePlace B.I.F → ℝ) (x : B.I.GA) : ℝ≥0∞ :=
  ∑' γ : farSet B d x, ‖phe B d (x⁻¹ * γ.1 * x)‖ₑ

def moderate (q : ℕ) (b : ℝ) : Set B.I.GA :=
  {x | x ∈ B.fund ∧ tauStar B q b ≤ least B.I x}

def FarModerate : Prop :=
  ∀ Cg : ℝ, 0 ≤ Cg → ∃ n₀ : ℕ, ∀ (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (p q : ℕ) (b : ℝ),
    1 ≤ q → CountHyp B Cg n₀ d p q b →
      ∫⁻ x in moderate B q b, farSum B d x ∂(B.I.muA B.μf) ≤
        ENNReal.ofReal (Real.exp (-((B.I.n : ℝ) ^ 2 * (B.I.f : ℝ))) * mainTerm B d)

end GlobalTheory.IndefiniteRowSideFullHecke.FarTermsModerate
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.FarTermsLatticeBound
section
open NumberField

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.FarTermsLatticeBound

open Formalism.MainNotions.S GlobalTheory.Count

def farSet (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (ep : ℝ) (x : B.I.GA) : Set B.I.GA :=
  {γ | γ ∈ B.I.GFset ∧ ¬ IsNear B d ep x γ}

def latFactor (I : AutInst) (x : I.GA) : ℝ :=
  (3 * Real.sqrt (I.n : ℝ) / tau1 I x ^ 2) ^ (2 * (I.n ^ 2 * I.f))

end GlobalTheory.IndefiniteRowSideFullHecke.FarTermsLatticeBound
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.LatticeCountingTheorem
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.LatticeCountingTheorem

open NumberField Formalism.MainNotions.S

def CountingTheorem : Prop :=
  ∀ Cg : ℝ, ∃ n₀ : ℕ, ∀ (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (p q : ℕ) (b : ℝ),
    GlobalTheory.Count.CountHyp B Cg n₀ d p q b →
      FiniteDimensional ℂ (B.I.eHom B.σs B.μf B.fund B.R B.Re) ∧
        |(B.D : ℝ) - GlobalTheory.Count.mainTerm B d| ≤
          Real.exp (-(1 / 16 * (B.I.n : ℝ) * (B.I.f : ℝ) * Real.log (B.I.n : ℝ))) *
            GlobalTheory.Count.mainTerm B d

end GlobalTheory.IndefiniteRowSideFullHecke.LatticeCountingTheorem
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.NearNonzeroTerms
section
open MeasureTheory NumberField
open scoped ENNReal

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.NearNonzeroTerms

open Formalism.MainNotions.S GlobalTheory.Count

variable (B : RowsAut)

def moderate (q : ℕ) (b : ℝ) : Set B.I.GA := {x | x ∈ B.fund ∧ tauStar B q b ≤ least B.I x}

def nearNe (d : InfinitePlace B.I.F → ℝ) (x : B.I.GA) : Set B.I.GA :=
  {γ | IsNear B d (epN B) x γ ∧ γ ≠ 1}

def nearAbs (d : InfinitePlace B.I.F → ℝ) (x : B.I.GA) : ℝ≥0∞ :=
  ∑' γ : nearNe B d x, ‖phe B d (x⁻¹ * γ.1 * x)‖ₑ

def nearBound (d : InfinitePlace B.I.F → ℝ) : ℝ :=
  Real.exp (-(1 / 4 * (B.I.n : ℝ) * (B.I.f : ℝ) * Real.log (B.I.n : ℝ))) * mainTerm B d

def NearModerate : Prop :=
  ∀ Cg : ℝ, 0 ≤ Cg → ∃ n₀ : ℕ, ∀ (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (p q : ℕ) (b : ℝ),
    1 ≤ q → CountHyp B Cg n₀ d p q b →
      ∫⁻ x in moderate B q b, nearAbs B d x ∂(B.I.muA B.μf) ≤ ENNReal.ofReal (nearBound B d)

theorem nearAbs_eq_zero (d : InfinitePlace B.I.F → ℝ) (x : B.I.GA)
    (h : ∀ γ, IsNear B d (epN B) x γ → γ = 1) : nearAbs B d x = 0 := by
  haveI : IsEmpty (nearNe B d x) := ⟨fun γ => γ.2.2 (h γ.1 γ.2.1)⟩
  simp [nearAbs]

end GlobalTheory.IndefiniteRowSideFullHecke.NearNonzeroTerms
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.OrbitStepSpace
section
open Matrix Finset

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace

open Formalism.MainNotions.S

section Defs

variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def orbit (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (X : Matrix (Fin n) (Fin n) ℂ) (v : H) : ℝ → H :=
  fun t => σ (NormedSpace.exp ((t : ℂ) • X)) v

def dAct (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (X : Matrix (Fin n) (Fin n) ℂ) (v : H) : H :=
  deriv (orbit σ X v) 0

def IsDiffVec (ε : Fin n → Bool) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (v : H) : Prop :=
  ∀ X, Formalism.REAL.inG ε X → DifferentiableAt ℝ (orbit σ X v) 0

def dWord (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (l : List (Matrix (Fin n) (Fin n) ℂ)) (v : H) : H :=
  l.foldr (dAct σ) v

def stepSpace (ε : Fin n → Bool) (lam : Fin n → ℝ) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (P : ℕ) :
    Submodule ℂ H :=
  Submodule.span ℂ {v | ∃ (l : List (Matrix (Fin n) (Fin n) ℂ)) (u : H), l.length ≤ P ∧
    (∀ X ∈ l, Formalism.REAL.inG ε X) ∧ u ∈ lowKSub ε lam σ ∧ v = dWord σ l u}

def IsONFamily (ε : Fin n → Bool) (E : Fin (n ^ 2) → Matrix (Fin n) (Fin n) ℂ) : Prop :=
  (∀ i, Formalism.REAL.inG ε (E i)) ∧ ∀ i j, (Matrix.trace (E i * (E j)ᴴ)).re = if i = j then 1 else 0

def stepConst (n : ℕ) (b : ℝ) (P : ℕ) : ℝ :=
  (n : ℝ) ^ (1 / 2 : ℝ) * b ^ 2 + 3 / 2 * (n : ℝ) ^ (3 / 2 : ℝ) + 3 * (P : ℝ)

theorem stepSpace_zero (ε : Fin n → Bool) (lam : Fin n → ℝ) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) :
    stepSpace ε lam σ 0 = lowKSub ε lam σ := by
  have : {v | ∃ (l : List (Matrix (Fin n) (Fin n) ℂ)) (u : H), l.length ≤ 0 ∧
      (∀ X ∈ l, Formalism.REAL.inG ε X) ∧ u ∈ lowKSub ε lam σ ∧ v = dWord σ l u} = (lowKSub ε lam σ : Set H) := by
    ext v
    constructor
    · rintro ⟨l, u, hl, -, hu, rfl⟩
      have : l = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hl)
      subst this
      exact hu
    · intro hv
      exact ⟨[], v, le_rfl, by simp, hv, rfl⟩
  rw [stepSpace, this, Submodule.span_eq]

theorem stepSpace_mono (ε : Fin n → Bool) (lam : Fin n → ℝ) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) :
    Monotone (stepSpace ε lam σ) := by
  intro P Q h
  refine Submodule.span_mono ?_
  rintro v ⟨l, u, hl, h1, h2, h3⟩
  exact ⟨l, u, hl.trans h, h1, h2, h3⟩

end Defs

end GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.PointwiseKernelBound
section
open NumberField Finset

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.PointwiseKernelBound

open Formalism.MainNotions.S GlobalTheory.Count

def decHS (q : ℕ) (h t : ℝ) : ℝ := Real.exp (-(h / 8) * min (t ^ 2) (t / Real.sqrt (2 * (q : ℝ))))

end GlobalTheory.IndefiniteRowSideFullHecke.PointwiseKernelBound
end
end

