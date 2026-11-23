module

public import Formalism.HermitianCurvature.Bundle0002
public import Mathlib
public import Formalism.YangianSpanCharacter.Bundle0001

@[expose] public section

-- bundled from Formalism.HermitianCurvature.LowerBlockNormalisedBoundFromComponents
section
namespace Formalism.FourierDecayAlt.PairingProductCorollary

open Finset
open scoped ComplexOrder

noncomputable section

def cg {K d : ℕ} (grid : Fin K → Fin (d + 1) → ℝ) (a : Fin K) : ℝ :=
  ∑ i, |F7.lagCo (grid a) i|

def coProd {K d : ℕ} (grid : Fin K → Fin (d + 1) → ℝ) (j : Fin K → Fin (d + 1)) : ℝ :=
  ∏ a, F7.lagCo (grid a) (j a)

def qProd {K d : ℕ} (q : ℝ → ℝ) (w : List (F7.WLetter ℝ)) (grid : Fin K → Fin (d + 1) → ℝ)
    (j : Fin K → Fin (d + 1)) : ℝ :=
  ∏ a, F7.qW q w (grid a (j a))

def nnProd {K d : ℕ} (nn : ℝ → ℝ) (h : ℝ) (grid : Fin K → Fin (d + 1) → ℝ)
    (j : Fin K → Fin (d + 1)) : ℝ :=
  ∏ a, nn (grid a (j a) + h)

def LowerBlockNormalisedBoundFromComponents : Prop :=
  ∀ (K d : ℕ) (grid : Fin K → Fin (d + 1) → ℝ) (q nn : ℝ → ℝ) (w : List (F7.WLetter ℝ)) (o W0 : ℂ)
    (RL RV : (Fin K → Fin (d + 1)) → ℝ) (wt wt' bw Qw BB : ℝ),
    (∀ a, Function.Injective (grid a)) →
    (∀ a i, 0 < q (grid a i) ∧ 0 < F7.qW q w (grid a i) ∧ 0 < nn (grid a i) ∧ 0 < nn (grid a i + 1)) →
    (∀ a i, q (grid a i) ≤ Qw * F7.qW q w (grid a i)) →
    (∀ a i, nn (grid a i) * nn (grid a i + 1) / q (grid a i) ≤ BB ^ 2) →
    0 ≤ BB → 0 ≤ wt → 0 ≤ wt' → 0 < bw → (∀ j, 0 ≤ RL j ∧ 0 ≤ RV j) →
    ‖o‖ ^ K * ‖W0‖ ≤ ∑ j, |coProd grid j| * Real.sqrt (RL j * RV j / qProd q w grid j) →
    ‖o‖ ^ K * (wt * wt' / bw * ‖W0‖) ≤
      (∏ a, cg grid a) * (Real.sqrt Qw * BB) ^ K *
        ∑ j, F7.thGrid grid j *
          ((wt ^ 2 * RL j / (bw * nnProd nn 0 grid j) + wt' ^ 2 * RV j / (bw * nnProd nn 1 grid j)) / 2)

def PairingGramInequality (Ntt : ℂ) (Nt Nt' : ℝ) : Prop := ‖Ntt‖ ^ 2 ≤ Nt * Nt'

def minFac (L o : ℝ) (K : ℕ) : ℝ := if L < o then (L / o) ^ K else 1

def oAbs {ι : Type} (t t' : ι → ℂ) (v : ι) : ℝ := ‖1 / t v - 1 / t' v‖

def LeadingBlockSeveralPlacesBound : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (K : ℕ) (abelian₂ : ι → ℝ) (t t' : ι → ℂ) (Ntt : ℂ)
    (Nt Nt' S1 S2 : ℝ),
    (∀ v, t v ≠ 0 ∧ t' v ≠ 0) → (∀ v, 0 ≤ abelian₂ v) → 0 ≤ Nt → 0 ≤ Nt' → 0 ≤ S1 → 0 ≤ S2 →
    PairingGramInequality Ntt Nt Nt' →
    Nt ≤ (∏ v ∈ univ.filter (fun v => 2 * abelian₂ v < oAbs t t' v ∧ ‖t v‖ ≤ ‖t' v‖),
      (‖t v‖ * abelian₂ v) ^ (2 * K)) * S1 →
    Nt' ≤ (∏ v ∈ univ.filter (fun v => 2 * abelian₂ v < oAbs t t' v ∧ ¬ ‖t v‖ ≤ ‖t' v‖),
      (‖t' v‖ * abelian₂ v) ^ (2 * K)) * S2 →
    ‖Ntt‖ ≤ (∏ v, minFac (2 * abelian₂ v) (oAbs t t' v) K) * ((S1 + S2) / 2)

end

end Formalism.FourierDecayAlt.PairingProductCorollary
end

-- bundled from Formalism.HermitianCurvature.StatementTA
section
namespace Formalism.FourierDecayAlt.TA

open Finset Filter Topology
open scoped InnerProductSpace ComplexConjugate

abbrev Pt (E : Type) := List (ℕ × E)

def lvl {E : Type} (p : Pt E) : ℕ := (p.map Prod.fst).sum

def IsPt {E : Type} [Zero E] (i : ℕ) (p : Pt E) : Prop :=
  lvl p = i ∧ ∀ b ∈ p, 1 ≤ b.1 ∧ b.2 ≠ 0

def ext {E : Type} (h : Pt E) (s : ℕ) (t : E) : Pt E := h ++ [(s, t)]

def PSDOn {α : Type} (P : Finset α) (k : α → α → ℂ) : Prop :=
  (∀ x ∈ P, ∀ y ∈ P, k y x = conj (k x y)) ∧
  ∀ a : α → ℂ, 0 ≤ (∑ x ∈ P, ∑ y ∈ P, conj (a x) * k x y * a y).re

section forms
variable {E : Type} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

noncomputable def gram (k : Pt E → Pt E → ℂ) (V : Pt E → H) (P : Finset (Pt E)) : ℂ :=
  ∑ p ∈ P, ∑ p' ∈ P, k p p' * ⟪V p, V p'⟫_ℂ

end forms

def LatSum {E : Type} [AddCommGroup E] (L : AddSubgroup E) (c : E → ℝ) (ep : ℝ) : Prop :=
  (∀ x, 0 ≤ c x) ∧ ∀ S : Finset E, (∀ x ∈ S, x ∈ L ∧ x ≠ 0) → ∑ x ∈ S, c x ≤ ep

structure Data (E : Type) [Field E] where
  r : ℕ
  K : ℕ → Pt E → Pt E → ℂ
  Th : ℕ → ℕ → E → Pt E → Pt E → ℂ
  e : ℕ → ℝ
  La : ℕ → ℕ → AddSubgroup E
  Lf : ℕ → ℕ → AddSubgroup E
  Lv : ℕ → AddSubgroup E

section axioms
variable {E : Type} [Field E] [DecidableEq E]

def KernelSupport (D : Data E) : Prop :=
  ∀ i s, 1 ≤ s → s ≤ i → i ≤ D.r + 1 → ∀ (h h' : Pt E) (t t' : E),
    IsPt (i - s) h → IsPt (i - s) h' → t ≠ 0 → t' ≠ 0 →
    (1 / t - 1 / t' ∉ D.Lf i s ∨ (i = D.r + 1 ∧ s = 1 ∧ t ≠ t')) →
    D.K i (ext h s t) (ext h' s t') = 0

def ThetaDomination (D : Data E) : Prop :=
  ∀ i s, 1 ≤ s → s ≤ i → i ≤ D.r + 1 →
    (∀ (t : E) (Hd : Finset (Pt E)), (∀ h ∈ Hd, IsPt (i - s) h) → PSDOn Hd (D.Th i s t)) ∧
    (∀ t l : E, l ∈ D.La i s → D.Th i s (t + l) = D.Th i s t) ∧
    (∀ (t : E) (Hd : Finset (Pt E)), t ≠ 0 → (∀ h ∈ Hd, IsPt (i - s) h) →
      PSDOn Hd (fun h h' => D.Th i s t h h' - D.K i (ext h s t) (ext h' s t))) ∧
    (∀ (R : Finset E) (Hd : Finset (Pt E)), (∀ x ∈ R, ∀ y ∈ R, x - y ∈ D.La i s → x = y) →
      (∀ h ∈ Hd, IsPt (i - s) h) →
      PSDOn Hd (fun h h' => ((1 + D.e i : ℝ) : ℂ) * D.K (i - s) h h' - ∑ t ∈ R, D.Th i s t h h'))

end axioms

section estimates
variable {E : Type} [Field E] [DecidableEq E] {H : Type} [NormedAddCommGroup H]
  [InnerProductSpace ℂ H] {W : Type} [Fintype W]

end estimates

section levels
variable {E : Type} [Field E] [DecidableEq E] {H : Type} [NormedAddCommGroup H]
  [InnerProductSpace ℂ H] {W : Type} [Fintype W]


end levels

end Formalism.FourierDecayAlt.TA
end

-- bundled from Formalism.HermitianCurvature.StatementW
section
namespace Formalism.FourierDecayAlt.W

open Matrix Formalism.YangianSpanCharacter.T NumberField

variable {R B : Type} [CommRing R] [Ring B] [Algebra R B]

def IsRTT (M : R → Matrix (Fin 2) (Fin 2) B) : Prop :=
  ∀ Y Y' : R, ((Y' - Y) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) B) - Pf B) * E1 (M Y') * E2 (M Y) =
    E2 (M Y) * E1 (M Y') * ((Y' - Y) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) B) - Pf B)

def IsDet (M : R → Matrix (Fin 2) (Fin 2) B) (q : R → R) : Prop :=
  ∀ Y : R, (M (Y + 1))ᵀ * Formalism.YangianSpanCharacter.T.J B * M Y = algebraMap R B (q Y) • Formalism.YangianSpanCharacter.T.J B ∧
    M Y * Formalism.YangianSpanCharacter.T.J B * (M (Y + 1))ᵀ = algebraMap R B (q Y) • Formalism.YangianSpanCharacter.T.J B

def EntriesCommute (M N : R → Matrix (Fin 2) (Fin 2) B) : Prop :=
  ∀ (Y Y' : R) (i j k l : Fin 2), M Y i j * N Y' k l = N Y' k l * M Y i j

end Formalism.FourierDecayAlt.W
end

