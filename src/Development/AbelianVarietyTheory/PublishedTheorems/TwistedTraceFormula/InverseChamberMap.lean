module

public import Mathlib

@[expose] public section

noncomputable section

open MeasureTheory Finset
open scoped InnerProductSpace ContDiff Classical

namespace GlobalTheory.Chamber

variable {k : ℕ}

abbrev A0 (k : ℕ) : Type := EuclideanSpace ℝ (Fin k)

abbrev SV (k : ℕ) : Type := Fin k → SignType

def vec (u : SV k) : A0 k := WithLp.toLp 2 fun i => (u i : ℝ)

def Below (u u' : SV k) : Prop := ∀ i, u i ≠ 0 → u' i = u i

def IsPar (P : Finset (SV k)) : Prop := 0 ∉ P ∧ ∀ u ∈ P, ∀ u' ∈ P, Below u u' ∨ Below u' u

def aP (P : Finset (SV k)) : Submodule ℝ (A0 k) := Submodule.span ℝ (vec '' (P : Set (SV k)))

def pr (P : Finset (SV k)) : A0 k →L[ℝ] A0 k := (aP P).starProjection

def IsLevi (𝔞 : Submodule ℝ (A0 k)) : Prop := ∃ P, IsPar P ∧ aP P = 𝔞

def aMQ (𝔞 : Submodule ℝ (A0 k)) (Q : Finset (SV k)) : Submodule ℝ (A0 k) := 𝔞 ⊓ (aP Q)ᗮ

def parF (𝔞 : Submodule ℝ (A0 k)) (R : Finset (SV k)) : Finset (Finset (SV k)) :=
  univ.filter fun Q => IsPar Q ∧ aP Q ≤ 𝔞 ∧ R ⊆ Q

def parP (𝔞 : Submodule ℝ (A0 k)) (R : Finset (SV k)) : Finset (Finset (SV k)) :=
  univ.filter fun P => IsPar P ∧ aP P = 𝔞 ∧ R ⊆ P

def between (P R : Finset (SV k)) : Finset (Finset (SV k)) := P.powerset.filter (R ⊆ ·)

def wt (Q : Finset (SV k)) (u : SV k) : A0 k := vec u - pr Q (vec u)

def rt (P : Finset (SV k)) (u : SV k) : A0 k := wt (P.erase u) u

def tau (P Q : Finset (SV k)) (H : A0 k) : ℝ := if ∀ u ∈ P \ Q, 0 < ⟪rt P u, H⟫_ℝ then 1 else 0

def tauHat (P Q : Finset (SV k)) (H : A0 k) : ℝ := if ∀ u ∈ P \ Q, 0 < ⟪wt Q u, H⟫_ℝ then 1 else 0

def gamP (P R : Finset (SV k)) (X H : A0 k) : ℝ :=
  ∑ S ∈ between P R, (-1) ^ (S \ R).card * tau P S H * tauHat S R (H - X)

def gamM (𝔞 : Submodule ℝ (A0 k)) (Q : Finset (SV k)) (X : Finset (SV k) → A0 k) (H : A0 k) : ℝ :=
  ∑ P ∈ parF 𝔞 Q, (-1) ^ (P \ Q).card * tauHat P Q (H - X P)

def IsOrth (𝔞 : Submodule ℝ (A0 k)) (X : Finset (SV k) → A0 k) : Prop :=
  ∀ P ∈ parF 𝔞 ∅, ∀ Q ⊆ P, X Q = pr Q (X P)

def IsGMFam (𝔞 : Submodule ℝ (A0 k)) (c : Finset (SV k) → A0 k → ℂ) : Prop :=
  ∀ P ∈ parF 𝔞 ∅, ContDiff ℝ ∞ (c P) ∧ ∀ Q ⊆ P, ∀ l, c Q l = c P (pr Q l)

def eL (l H : A0 k) : ℂ := Complex.exp (Complex.I * (⟪l, H⟫_ℝ : ℝ))

def expFam (X : Finset (SV k) → A0 k) : Finset (SV k) → A0 k → ℂ := fun P l => eL l (X P)

def epsOf (s : Finset (SV k)) (b : SV k → A0 k) (l : A0 k) : ℂ :=
  (√(Matrix.gram ℝ fun u : s => b u).det : ℝ) * ∏ u ∈ s, (Complex.I * (⟪l, b u⟫_ℝ : ℝ))⁻¹

def eps (P Q : Finset (SV k)) : A0 k → ℂ := epsOf (P \ Q) (rt P)

def epsHat (P Q : Finset (SV k)) : A0 k → ℂ := epsOf (P \ Q) (wt Q)

def generic (k : ℕ) : Set (A0 k) := {l | ∀ P, IsPar P → ∀ Q ⊆ P, ∀ u ∈ P \ Q, ⟪l, wt Q u⟫_ℝ ≠ 0}

def sumM (𝔞 : Submodule ℝ (A0 k)) (Q : Finset (SV k)) (c : Finset (SV k) → A0 k → ℂ) (l : A0 k) : ℂ :=
  ∑ P ∈ parP 𝔞 Q, eps P Q l * c P l

def sumP (P R : Finset (SV k)) (c : Finset (SV k) → A0 k → ℂ) (l : A0 k) : ℂ :=
  ∑ S ∈ between P R, (-1) ^ (P \ S).card * epsHat P S l * eps S R l * c S l

def cM (𝔞 : Submodule ℝ (A0 k)) (Q : Finset (SV k)) (c : Finset (SV k) → A0 k → ℂ) : A0 k → ℂ :=
  extendFrom (generic k) (sumM 𝔞 Q c)

def cP (P R : Finset (SV k)) (c : Finset (SV k) → A0 k → ℂ) : A0 k → ℂ := extendFrom (generic k) (sumP P R c)

def stdVec (j : Fin k) : SV k := fun i => if i ≤ j then 1 else 0

def stdPar (J : Finset (Fin k)) : Finset (SV k) := J.image stdVec

def invSV (π : Equiv.Perm (Fin k)) (ε : Fin k → SignTypeˣ) (u : SV k) : SV k := fun i => ε i * u (π i)

def inverseChamberMap (π : Equiv.Perm (Fin k)) (ε : Fin k → SignTypeˣ) (H : A0 k) : A0 k :=
  WithLp.toLp 2 fun i => ((ε i : SignType) : ℝ) * H (π i)

def weylPar (π : Equiv.Perm (Fin k)) (ε : Fin k → SignTypeˣ) : Finset (SV k) := (stdPar univ).image (invSV π ε)

def Regular (c : ℝ) (T : A0 k) : Prop := (∀ i j, i < j → c ≤ T i - T j) ∧ ∀ i, c ≤ T i

theorem mem_parF {𝔞 : Submodule ℝ (A0 k)} {R Q : Finset (SV k)} : Q ∈ parF 𝔞 R ↔ IsPar Q ∧ aP Q ≤ 𝔞 ∧ R ⊆ Q := by
  simp [parF]

theorem isPar_stdPar (J : Finset (Fin k)) : IsPar (stdPar J) := by
  refine ⟨fun h => ?_, fun u hu u' hu' => ?_⟩
  · obtain ⟨j, -, e⟩ := mem_image.1 h
    simpa [stdVec] using congrFun e j
  · obtain ⟨j, -, rfl⟩ := mem_image.1 hu
    obtain ⟨j', -, rfl⟩ := mem_image.1 hu'
    have key : ∀ a b : Fin k, a ≤ b → Below (stdVec a) (stdVec b) := fun a b h i hi => by
      have : i ≤ a := by by_contra e; exact hi (if_neg e)
      simp [stdVec, this, this.trans h]
    exact (le_total j j').imp (key _ _) (key _ _)

end GlobalTheory.Chamber

end
