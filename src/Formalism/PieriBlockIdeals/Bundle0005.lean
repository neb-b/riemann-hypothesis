module

public import Formalism.PieriBlockIdeals.Bundle0001
public import Formalism.PieriBlockIdeals.Bundle0003
public import Formalism.PieriBlockIdeals.Bundle0004

@[expose] public section

-- bundled from Formalism.PieriBlockIdeals.FactorialValuationSum
section
noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Formalism.CohomologicalDescent.UnitNormBounds

open Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LD

def U (k j t : ℕ) (lam : Fin (k + j) → ℕ) (a : Fin (k + j)) : ℤ :=
  (lam a : ℤ) + ((k : ℤ) + (j : ℤ) + (t : ℤ) - 1 - (a.val : ℤ))

def maxB (t w : ℕ) : ℤ := (w : ℤ) + (t : ℤ) - 1

def dual {r : ℕ} (M : ℕ) (lam : Fin r → ℕ) : Fin r → ℕ := fun b => M - lam (Fin.rev b)

def label (k j t M : ℕ) (lam : Fin (k + j) → ℕ) (b : Fin (k + j)) (col : ℕ) : ℤ :=
  U k j t lam (Fin.rev b) - ((col : ℤ) - (dual M lam b : ℤ) + 1)

def cont (t w M : ℕ) (ct : ℤ) : ℤ := ((M - w : ℕ) : ℤ) - (ct - maxB t w)

structure Rows (k j t w M : ℕ) (lam : Fin (k + j) → ℕ) (xm xp : ℤ) : Prop where
  low : ∀ a, w ≤ lam a
  high : ∀ a, lam a ≤ M
  cloud : ∀ a : Fin (k + j), a.val < k → xm ≤ U k j t lam a ∧ U k j t lam a ≤ xp
  rest : ∀ a : Fin (k + j), k ≤ a.val → U k j t lam a < xm
  above : maxB t w < xm
  le : xm ≤ xp

def GoodLabels : Prop :=
  ∀ (k j t w M i : ℕ) (lam : Fin (k + j) → ℕ), (∀ a, w ≤ lam a ∧ lam a ≤ M) →
    ∀ tau ∈ shapes t (M - w) i (dual M lam), ∀ (b : Fin (k + j)) (col : ℕ), dual M lam b ≤ col → col < tau b →
      maxB t w < label k j t M lam b col ∧ label k j t M lam b col ≤ U k j t lam (Fin.rev b) - 1

def boxesOfLabel (t w M : ℕ) {r : ℕ} (lam tau : Fin r → ℕ) (ct : ℤ) : ℕ :=
  boxesOfContent (dual M lam) tau (cont t w M ct)

def cloudBoxes (k j t w M : ℕ) (lam tau : Fin (k + j) → ℕ) (ct : ℤ) : ℕ :=
  (Finset.univ.filter fun b : Fin (k + j) => (Fin.rev b).val < k ∧
    ((dual M lam b : ℤ) ≤ cont t w M ct + (b.val : ℤ) ∧ cont t w M ct + (b.val : ℤ) < (tau b : ℤ))).card

def CountsRows : Prop :=
  ∀ (k j t w M i : ℕ) (lam : Fin (k + j) → ℕ) (xm xp : ℤ), Rows k j t w M lam xm xp →
    ∀ tau ∈ shapes t (M - w) i (dual M lam), ∀ ct : ℤ,
      boxesOfLabel t w M lam tau ct ≤ (if ct < xm then j else 0) + cloudBoxes k j t w M lam tau ct

def CountsCloud : Prop :=
  ∀ (k j t w M i : ℕ) (lam : Fin (k + j) → ℕ),
    ∀ tau ∈ shapes t (M - w) i (dual M lam), ∀ ct : ℤ,
      cloudBoxes k j t w M lam tau ct ≤ k ∧ cloudBoxes k j t w M lam tau ct ≤ t

def CountsDeep : Prop :=
  ∀ (k j t w M i : ℕ) (lam : Fin (k + j) → ℕ) (xm xp : ℤ), Rows k j t w M lam xm xp →
    ∀ tau ∈ shapes t (M - w) i (dual M lam), ∀ ct : ℤ, ct < xm →
      (cloudBoxes k j t w M lam tau ct : ℤ) * (xm - ct) ≤ (i : ℤ)

def MuBound : Prop :=
  ∀ (k j t w M i : ℕ) (lam : Fin (k + j) → ℕ) (xm xp : ℤ), Rows k j t w M lam xm xp → ∀ ct : ℤ,
    (mu t (M - w) i (dual M lam) (cont t w M ct) : ℝ) ≤
      (if ct < xm then (j : ℝ) else 0) +
        min (min (k : ℝ) (t : ℝ)) (if ct < xm then (i : ℝ) / ((xm - ct : ℤ) : ℝ) else (k : ℝ))

def DnValSum : Prop :=
  ∀ (l k j t w M i : ℕ) (lam : Fin (k + j) → ℕ) (xm xp : ℤ), l.Prime → Rows k j t w M lam xm xp →
    padicValInt l (Dn t (M - w) i (dual M lam)) =
      ∑ ct ∈ Finset.Ioo (maxB t w) xp, mu t (M - w) i (dual M lam) (cont t w M ct) * vl l (ct - maxB t w)

def FactorialValuationSum : Prop :=
  ∀ (l : ℕ) (xm mB : ℤ), l.Prime → mB < xm →
    ∑ ct ∈ Finset.Ioo mB xm, vl l (ct - mB) = padicValNat l ((xm - mB - 1).toNat).factorial ∧
      (padicValNat l ((xm - mB - 1).toNat).factorial : ℝ) ≤ (((xm - mB : ℤ) : ℝ) - 1) / ((l : ℝ) - 1)

def harm (l h : ℕ) (i : ℝ) : ℝ :=
  if h < l then 0 else (i / (l : ℝ)) * (1 + Real.log ((h : ℝ) / (l : ℝ)))

def labelSumBoundPos (l k t h : ℕ) (i : ℝ) (xm xp mB : ℤ) : ℝ :=
  (k : ℝ) * (((xp - xm : ℤ) : ℝ) / (l : ℝ) + IlInd l xm xp mB) +
    (if ((d0 l (xm - mB) : ℕ) : ℤ) < xm - mB then
      min (min (k : ℝ) (t : ℝ)) (i / (d0 l (xm - mB) : ℝ)) else 0) +
    harm l h i

def HarmPosLog : Prop :=
  ∀ (l h : ℕ) (i : ℝ), 0 ≤ i →
    harm l h i ≤ (i / (l : ℝ)) * (1 + Real.posLog ((h : ℝ) / (l : ℝ))) ∧
      (1 ≤ l → l ≤ h → harm l h i = (i / (l : ℝ)) * (1 + Real.posLog ((h : ℝ) / (l : ℝ))))

def LabelSumPlus : Prop :=
  ∀ (l k t h : ℕ) (i : ℝ) (xm xp mB : ℤ), l.Prime → 0 ≤ i → mB < xm → xm ≤ xp →
    xp - mB ≤ (h : ℤ) → h < l ^ 2 →
    labelLHS l k t i xm xp mB ≤ labelSumBoundPos l k t h i xm xp mB

def Step2Val : Prop :=
  ∀ (l k j t w M h i : ℕ) (lam : Fin (k + j) → ℕ) (xm xp : ℤ), l.Prime → Rows k j t w M lam xm xp →
    xp - maxB t w ≤ (h : ℤ) → h < l ^ 2 →
    (padicValInt l (Dn t (M - w) i (dual M lam)) : ℝ) ≤
      (j : ℝ) * ((((xm - maxB t w : ℤ) : ℝ) - 1) / ((l : ℝ) - 1)) +
        labelSumBoundPos l k t h (i : ℝ) xm xp (maxB t w)

def Step2ValUpTo : Prop :=
  ∀ (l k j t w M h i : ℕ) (I : ℝ) (lam : Fin (k + j) → ℕ) (xm xp : ℤ), l.Prime → Rows k j t w M lam xm xp →
    xp - maxB t w ≤ (h : ℤ) → h < l ^ 2 → (i : ℝ) ≤ I →
    (padicValInt l (Dn t (M - w) i (dual M lam)) : ℝ) ≤
      (j : ℝ) * (((h : ℝ) - 1) / ((l : ℝ) - 1)) + labelSumBoundPos l k t h I xm xp (maxB t w)

def cPrime (l k j t q h ecl : ℕ) (xm xp mB : ℤ) (I : ℝ) : ℝ :=
  ((q : ℝ) + 2 * (j : ℝ)) * (((h : ℝ) - 1) / ((l : ℝ) - 1)) + (ecl : ℝ) + labelSumBoundPos l k t h I xm xp mB

def cCoarse (l k j t q h N' ecl : ℕ) (xm xp mB : ℤ) (I : ℝ) : ℝ :=
  ((q : ℝ) + 2 * (j : ℝ)) * (((h : ℝ) + (N' : ℝ)) / ((l : ℝ) - 1) + 6) + (ecl : ℝ) +
    (k : ℝ) * (((xp - xm : ℤ) : ℝ) / (l : ℝ) + IlInd l xm xp mB) +
    (if ((d0 l (xm - mB) : ℕ) : ℤ) < xm - mB then
      min (min (k : ℝ) (t : ℝ)) (I / (d0 l (xm - mB) : ℝ)) else 0) +
    (I / (l : ℝ)) * (1 + Real.posLog ((h : ℝ) / (l : ℝ)))

def UN (N : ℕ) (lam : ℕ → ℕ) (a : ℕ) : ℤ := (lam a : ℤ) + (N : ℤ) - 1 - (a : ℤ)

end Formalism.CohomologicalDescent.UnitNormBounds
end
end

-- bundled from Formalism.PieriBlockIdeals.LastGradedOfGradedAlone
section
open MvPolynomial

namespace Formalism.CohomologicalDescent.LD

open Formalism.GradedWeylDivisibility

def dualWt {r : ℕ} (M : ℕ) (κ : Fin r → ℕ) : Fin r → ℕ := fun a => M - κ (Fin.rev a)

def DualWtSpec : Prop :=
  ∀ (r M : ℕ) (κ : Fin r → ℕ), ((∀ a, κ a ≤ M) → dualWt M (dualWt M κ) = κ) ∧ (∀ a, dualWt M κ a ≤ M) ∧
    (Antitone κ → Antitone (dualWt M κ))

def BlockDual : Prop :=
  ∀ (p q w M : ℕ) (κ : Fin q → ℕ),
    (fun a : Fin (p + q) => dualWt M (blockWtLast p q w κ) (Fin.cast (Nat.add_comm p q) a)) =
      blockWt p q (M - w) (dualWt M κ)

def DepthDual : Prop :=
  ∀ (p q w M i : ℕ) (μ : Fin (q + p) → ℕ), w ≤ M → (∀ a, μ a ≤ M) →
    (IsDepthLast p q w μ i ↔
      IsDepth p q (M - w) (fun a : Fin (p + q) => M - μ (Fin.rev (Fin.cast (Nat.add_comm p q) a))) i)

def WtBound : Prop :=
  ∀ (r M : ℕ) (ν μ : Fin r → ℕ), Antitone ν → (∀ a, ν a ≤ M) → nablaWt r ν μ ≠ ⊥ → ∀ a, μ a ≤ M

def ExpDual : Prop :=
  ∀ (l r M : ℕ) (ν μ : Fin r → ℕ) (e : ℕ), l.Prime → Antitone ν → (∀ a, ν a ≤ M) → (∀ a, μ a ≤ M) →
    (ExpLe l r ν μ e ↔ ExpLe l r (fun a => M - ν (Fin.rev a)) (fun a => M - μ (Fin.rev a)) e)

def LastGradedOfGraded : Prop := ExpDual → LemmaDGraded → LemmaDLastGraded

noncomputable def genDet (r : ℕ) : MvPolynomial (Fin r × Fin r) ℤ :=
  (Matrix.of fun a s : Fin r => (X (a, s) : MvPolynomial (Fin r × Fin r) ℤ)).det

noncomputable def cofMap (r : ℕ) :
    MvPolynomial (Fin r × Fin r) ℤ →ₐ[ℤ] MvPolynomial (Fin r × Fin r) ℤ :=
  aeval fun v : Fin r × Fin r =>
    (Matrix.of fun a s : Fin r => (X (a, s) : MvPolynomial (Fin r × Fin r) ℤ)).adjugate (Fin.rev v.2) (Fin.rev v.1)

def NablaDual : Prop :=
  ∀ (r M : ℕ) (ν : Fin r → ℕ), Antitone ν → (∀ a, ν a ≤ M) → ∀ x ∈ dualWeyl ℤ r r ν,
    ∃ g ∈ dualWeyl ℤ r r (dualWt M ν), genDet r ^ (∑ a, ν a) * g = genDet r ^ M * cofMap r x

def WeylDual : Prop :=
  ∀ (r M : ℕ) (ν : Fin r → ℕ), Antitone ν → (∀ a, ν a ≤ M) → ∀ x ∈ weyl ℤ r r le_rfl ν,
    ∃ g ∈ weyl ℤ r r le_rfl (dualWt M ν), genDet r ^ (∑ a, ν a) * g = genDet r ^ M * cofMap r x

def DualWeight : Prop :=
  ∀ (r M : ℕ) (μ : Fin r → ℕ) (x g : MvPolynomial (Fin r × Fin r) ℤ), (∀ a, μ a ≤ M) →
    IsWeightedHomogeneous (rowW r r) x μ → genDet r ^ (∑ a, μ a) * g = genDet r ^ M * cofMap r x →
      IsWeightedHomogeneous (rowW r r) g (dualWt M μ)

def CofCof : Prop :=
  ∀ r : ℕ, cofMap r (genDet r) = genDet r ^ (r - 1) ∧
    ∀ (N : ℕ) (x : MvPolynomial (Fin r × Fin r) ℤ), x.IsHomogeneous N →
      genDet r ^ N * cofMap r (cofMap r x) = genDet r ^ ((r - 1) * N) * x

def ExpDualOfLattices : Prop := NablaDual → WeylDual → DualWeight → CofCof → ExpDual

def LastGradedOfGradedAlone : Prop := LemmaDGraded → LemmaDLastGraded

end Formalism.CohomologicalDescent.LD
end

