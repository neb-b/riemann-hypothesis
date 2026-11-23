module

public import Formalism.PieriBlockIdeals.Bundle0003
public import Mathlib
public import Formalism.PieriBlockIdeals.Bundle0001
public import Formalism.RankGapBounds.Bundle0001
public import Formalism.PieriBlockIdeals.LemmaWFromLattice
public import Formalism.PieriBlockIdeals.MertensReciprocalElementary

@[expose] public section

-- bundled from Formalism.PieriBlockIdeals.BranchingBoundLastGradedOneRow
section
open MvPolynomial

namespace Formalism.CohomologicalDescent.LD

open Formalism.GradedWeylDivisibility

def LemmaDLastGradedAt (l p q w M : ℕ) (lam2 : Fin q → ℕ) (ξ : Fin (q + p) → ℤ) : Prop :=
  ∀ (i' : ℤ) (eL : ℕ),
    (∀ μ2 : Fin q → ℕ, depth2 ξ (blockWtLast p q w lam2) (blockWtLast p q w μ2) ≤ i' → ExpLe l q lam2 μ2 eL) →
    ∀ (i : ℕ) (μ : Fin (q + p) → ℕ), IsDepthLast p q w μ i → depth2 ξ (blockWtLast p q w lam2) μ ≤ i' →
      ExpLe l (q + p) (blockWtLast p q w lam2) μ
        (eL + padicValInt l (Dn p (M - w) i fun b : Fin q => M - lam2 (Fin.rev b)))

def LemmaDLastGraded : Prop :=
  ∀ (l p q w M : ℕ) (lam2 : Fin q → ℕ) (ξ : Fin (q + p) → ℤ), l.Prime → Antitone lam2 →
    (∀ b, w ≤ lam2 b ∧ lam2 b ≤ M) → Antitone ξ → LemmaDLastGradedAt l p q w M lam2 ξ

def BranchingBoundLastGradedOneRow : Prop :=
  ∀ (l q w M : ℕ) (lam2 : Fin q → ℕ) (ξ : Fin (q + 1) → ℤ), l.Prime → Antitone lam2 →
    (∀ b, w ≤ lam2 b ∧ lam2 b ≤ M) → Antitone ξ → LemmaDLastGradedAt l 1 q w M lam2 ξ

def LastGradedImpliesLast : Prop := LemmaDLastGraded → LemmaDLast

def OneRowBoundOfLastGraded : Prop := LemmaDLastGraded → BranchingBoundLastGradedOneRow

def Depth2Levi : Prop :=
  ∀ (p q w : ℕ) (lam2 μ2 : Fin q → ℕ) (ξ : Fin (q + p) → ℤ),
    depth2 ξ (blockWtLast p q w lam2) (blockWtLast p q w μ2) =
      ∑ b : Fin q, ξ (Fin.castAdd p b) * ((lam2 b : ℤ) - (μ2 b : ℤ))

def DepthLastIff : Prop :=
  ∀ (p q w i : ℕ) (lam2 : Fin q → ℕ) (μ : Fin (q + p) → ℕ), ∑ a, μ a = ∑ a, blockWtLast p q w lam2 a →
    (IsDepthLast p q w μ i ↔
      depth2 (fun a : Fin (q + p) => if a.val < q then 1 else 0) (blockWtLast p q w lam2) μ = (i : ℤ))

def Depth2Dual : Prop :=
  ∀ (r M : ℕ) (ξ : Fin r → ℤ) (lam μ : Fin r → ℕ), (∀ a, lam a ≤ M) → (∀ a, μ a ≤ M) →
    depth2 (fun a => -ξ (Fin.rev a)) (fun a => M - lam (Fin.rev a)) (fun a => M - μ (Fin.rev a)) = depth2 ξ lam μ ∧
      (Antitone ξ → Antitone fun a => -ξ (Fin.rev a))

def PeelBoundLast : Prop :=
  BranchingBoundLastGradedOneRow → ∀ (l q w M : ℕ) (lam2 : Fin q → ℕ) (ξ : Fin (q + 1) → ℤ), l.Prime → Antitone lam2 →
    (∀ b, w ≤ lam2 b ∧ lam2 b ≤ M) → Antitone ξ →
    ∀ (i' : ℤ) (eL : ℕ),
      (∀ μ2 : Fin q → ℕ, depth2 ξ (blockWtLast 1 q w lam2) (blockWtLast 1 q w μ2) ≤ i' → ExpLe l q lam2 μ2 eL) →
      ∀ μ : Fin (q + 1) → ℕ, depth2 ξ (blockWtLast 1 q w lam2) μ ≤ i' →
        ExpLe l (q + 1) (blockWtLast 1 q w lam2) μ (eL + (M + q - w - 1) / (l - 1))

def res {α : Type} (r : ℕ) (f : ℕ → α) : Fin r → α := fun a => f a.val

def varpi (c : ℕ) : ℕ → ℤ := fun a => if a < c then 1 else 0

def ExpUpTo (l r : ℕ) (lam : ℕ → ℕ) (ξ : ℕ → ℤ) (I : ℤ) (e : ℕ) : Prop :=
  ∀ μ : Fin r → ℕ, depth2 (res r ξ) (res r lam) μ ≤ I → ExpLe l r (res r lam) μ e

def PeelRows : Prop :=
  BranchingBoundLastGradedOneRow → ∀ (l n s h : ℕ) (lam : ℕ → ℕ) (ξ : ℕ → ℤ), l.Prime →
    (∀ a b, a ≤ b → b < n + s → lam b ≤ lam a) → lam 0 + (n + s) ≤ h + lam (n + s - 1) + 1 → Antitone ξ →
    ∀ (I : ℤ) (e : ℕ), ExpUpTo l n lam ξ I e → ExpUpTo l (n + s) lam ξ I (e + s * ((h - 1) / (l - 1)))

noncomputable def blockCost (l n t I : ℕ) (lam : ℕ → ℕ) : ℕ :=
  (Finset.range (I + 1)).sup fun i =>
    padicValInt l (Dn t (lam 0 - lam n) i fun b : Fin n => lam 0 - res n lam (Fin.rev b))

def BlockStep : Prop :=
  LemmaDLast → ∀ (l n t : ℕ) (lam : ℕ → ℕ), l.Prime → 1 ≤ t →
    (∀ a b, a ≤ b → b < n + t → lam b ≤ lam a) → (∀ a, n ≤ a → a < n + t → lam a = lam n) →
    ∀ eL : ℕ, (∀ μ2 : Fin n → ℕ, ExpLe l n (res n lam) μ2 eL) →
      ∀ I : ℕ, ExpUpTo l (n + t) lam (varpi n) (I : ℤ) (eL + blockCost l n t I lam)

def ApplicationSteps : Prop :=
  LemmaDLastGraded → ∀ (l k j t q h : ℕ) (lam : ℕ → ℕ), l.Prime → 1 ≤ t →
    (∀ a b, a ≤ b → b < k + j + t + q → lam b ≤ lam a) →
    (∀ a, k + j ≤ a → a < k + j + t → lam a = lam (k + j)) →
    lam 0 + (k + j + t + q) ≤ h + lam (k + j + t + q - 1) + 1 →
    ∀ ecl : ℕ, (∀ μ : Fin k → ℕ, ExpLe l k (res k lam) μ ecl) →
      ∀ I : ℕ, ExpUpTo l (k + j + t + q) lam (varpi (k + j)) (I : ℤ)
        (q * ((h - 1) / (l - 1)) + blockCost l (k + j) t I lam + j * ((h - 1) / (l - 1)) + ecl)

end Formalism.CohomologicalDescent.LD
end

-- bundled from Formalism.PieriBlockIdeals.ExZTranslate
section
noncomputable section

namespace Formalism.CohomologicalDescent.LA

def InclZTwist : Prop :=
  ∀ (r : ℕ) (ν : Fin r → ℕ) (c l e : ℕ), Antitone ν → l.Prime →
    (InclZ r r le_rfl (fun a => ν a + c) l e ↔ InclZ r r le_rfl ν l e)

def ExZTwist : Prop :=
  ∀ (r : ℕ) (ν : Fin r → ℕ) (c l : ℕ), Antitone ν → l.Prime →
    exZ r r le_rfl (fun a => ν a + c) l = exZ r r le_rfl ν l

end Formalism.CohomologicalDescent.LA
end
end

-- bundled from Formalism.PieriBlockIdeals.ExponentBoundCounterexample
section
open MvPolynomial CategoryTheory TensorProduct

noncomputable section

namespace Formalism.CohomologicalDescent.SL2BinomialLattices

open Formalism.GradedWeylDivisibility Formalism.RankGapBounds.JumpSetsAlt Formalism.CohomologicalDescent.LA

universe u v u' v'

def LgLog : Prop :=
  ∀ l y : ℕ, (Nat.log l y : ℝ) * Real.log l ≤ Real.log y

structure Shape (N k h S eta : ℕ) (xm lo : ℤ) (U : Fin N → ℤ) : Prop where
  anti : StrictAnti U
  inRange : ∀ a, 0 ≤ U a ∧ U a ≤ (h : ℤ)
  k_le : k ≤ N
  cloudIn : ∀ a : Fin N, a.val < k → xm ≤ U a ∧ U a ≤ xm + (S : ℤ)
  restIn : ∀ a : Fin N, k ≤ a.val → lo ≤ U a ∧ U a ≤ lo + (eta : ℤ)

def eCl {N : ℕ} (U : Fin N → ℤ) (k l : ℕ) : ℕ :=
  ∑ p ∈ (posPairs N).filter (fun p => p.2.val < k), Formalism.RankGapBounds.JumpSetsAlt.maxVal l (U p.1 - U p.2 - 1).toNat

def eRest {N : ℕ} (U : Fin N → ℤ) (k l : ℕ) : ℕ :=
  ∑ p ∈ (posPairs N).filter (fun p => k ≤ p.1.val), Formalism.RankGapBounds.JumpSetsAlt.maxVal l (U p.1 - U p.2 - 1).toNat

def eCross {N : ℕ} (U : Fin N → ℤ) (k l : ℕ) : ℕ :=
  ∑ p ∈ (posPairs N).filter (fun p => p.1.val < k ∧ k ≤ p.2.val),
    Formalism.RankGapBounds.JumpSetsAlt.maxVal l (U p.1 - U p.2 - 1).toNat

def ESplit3 : Prop :=
  ∀ (N k l : ℕ) (U : Fin N → ℤ), eExp U l = eCl U k l + eRest U k l + eCross U k l

def ChooseSplit : Prop :=
  ∀ N k : ℕ, k ≤ N →
    k.choose 2 + (N - k).choose 2 + k * (N - k) = N.choose 2 ∧
    ((posPairs N).filter (fun p => p.2.val < k)).card = k.choose 2 ∧
    ((posPairs N).filter (fun p => k ≤ p.1.val)).card = (N - k).choose 2 ∧
    ((posPairs N).filter (fun p => p.1.val < k ∧ k ≤ p.2.val)).card = k * (N - k)

def ThreeBounds : Prop :=
  ∀ (l N k h S eta : ℕ) (xm lo : ℤ) (U : Fin N → ℤ), l.Prime → Shape N k h S eta xm lo U →
    eCl U k l ≤ k.choose 2 * Nat.log l S ∧ (S ≤ l → eCl U k l = 0) ∧
    eRest U k l ≤ (N - k).choose 2 * Nat.log l eta ∧ (eta ≤ l → eRest U k l = 0) ∧
    eCross U k l ≤ k * (N - k) * Nat.log l h ∧
    k * (N - k) * Nat.log l h ≤ k * (N - k) * Nat.log l (2 * h + N)

def SizeLarge : Prop :=
  ∀ (l N k h S eta ex m t : ℕ) (xm lo : ℤ) (U : Fin N → ℤ), l.Prime →
    Shape N k h S eta xm lo U → ex ≤ eExp U l → eta ≤ l → N - k ≤ m + t →
    (ex : ℝ) * Real.log l ≤
        (k : ℝ) * ((N - k : ℕ) : ℝ) * Real.log h + (k.choose 2 : ℝ) * Real.log S ∧
      (k : ℝ) * ((N - k : ℕ) : ℝ) * Real.log h + (k.choose 2 : ℝ) * Real.log S ≤
        (k : ℝ) * ((m : ℝ) + t) * Real.log (3 * (h : ℝ)) + (k : ℝ) ^ 2 * Real.log ((S : ℝ) + k)

end Formalism.CohomologicalDescent.SL2BinomialLattices
end
end

-- bundled from Formalism.PieriBlockIdeals.MultiplicityZeroThickEmbedding
section
noncomputable section

open Finset

namespace Formalism.CohomologicalDescent.WorkedExample

open Formalism.CohomologicalDescent

def MwFlip : Prop :=
  ∀ (l : ℕ) (b h : ℤ) (t κ : ℕ) (U : Finset ℤ),
    mwCount l (h - (b + t - 1)) t κ (U.image fun u => h - u) = mwCount l b t κ U

def LinkageFlip : Prop :=
  ∀ (K : Type) [CommRing K] (N : ℕ) (U U' : Fin N → ℤ) (c c' h : ℤ),
    (∏ a, (Polynomial.X + Polynomial.C (((U a + c : ℤ)) : K))) =
      ∏ a, (Polynomial.X + Polynomial.C (((U' a + c : ℤ)) : K)) →
    (∏ a, (Polynomial.X + Polynomial.C (((h - U a + c' : ℤ)) : K))) =
      ∏ a, (Polynomial.X + Polynomial.C (((h - U' a + c' : ℤ)) : K))

structure Labels (ι : Type) (N : ℕ) where
  cc : ι → ι
  Φ : Set ι
  U : ι → Fin N → ℤ
  U' : ι → Fin N → ℤ
  bot : ι → ℤ

namespace Labels

variable {ι : Type} {N : ℕ}

def Refl (D : Labels ι N) (σ : Equiv.Perm ι) (h t : ℕ) : Prop :=
  (∀ i, D.cc (D.cc i) = i) ∧ (∀ i, σ (D.cc i) = D.cc (σ i)) ∧ (∀ i, i ∈ D.Φ ∨ D.cc i ∈ D.Φ) ∧
  (∀ i a, D.U (D.cc i) a = (h : ℤ) - D.U i (Fin.rev a)) ∧
  (∀ i a, D.U' (D.cc i) a = (h : ℤ) - D.U' i (Fin.rev a)) ∧
  (∀ i, D.bot (D.cc i) = (h : ℤ) - (D.bot i + (t : ℤ) - 1))

def Linked (D : Labels ι N) (F : Type) [Field F] (t : ℕ) (cst : ι → ℤ) : Prop :=
  ∀ i ∈ D.Φ, StrictAnti (D.U i) ∧ StrictAnti (D.U' i) ∧
    (∀ s : Fin t, ∃ a, D.U i a = D.bot i + ((s : ℕ) : ℤ)) ∧
    (∏ a, (Polynomial.X + Polynomial.C (((D.U i a + cst i : ℤ)) : F))) =
      ∏ a, (Polynomial.X + Polynomial.C (((D.U' i a + cst i : ℤ)) : F))

def Carried (D : Labels ι N) (ep : ι → ι) (J : ι → Fin N → ℤ) (botJ : ι → ℤ) : Prop :=
  (ep = id ∨ ep = D.cc) ∧ (∀ i, J (ep i) = D.U' i) ∧ (∀ i, botJ (ep i) = D.bot i)

def mw (D : Labels ι N) (l t κ : ℕ) (i : ι) : ℕ :=
  mwCount l (D.bot i) t κ (Finset.univ.image (D.U i))

end Labels

def ShapeAt {ι : Type} (k j t q : ℕ) (D : Labels ι (k + j + t + q)) (τ : ι) : Prop :=
  (∀ a, 0 ≤ D.U τ a) ∧ ∑ a, D.U τ a = ∑ a, D.U' τ a ∧
  ∀ a : Fin (k + j + t + q), k + j ≤ (a : ℕ) → (a : ℕ) < k + j + t →
    D.U τ a = D.bot τ + ((k + j + t - 1 - (a : ℕ) : ℕ) : ℤ)

def DepthBound {ι : Type} (k j t q l h : ℕ) (D : Labels ι (k + j + t + q)) (σ : Equiv.Perm ι)
    (τ : ι) : Prop :=
  ∑ a ∈ Finset.univ.filter (fun a : Fin (k + j + t + q) => (a : ℕ) < k + j),
      (D.U τ a - D.U' τ a) ≤
    (q : ℤ) * h +
      ((l : ℤ) * (D.mw l t (h / (l - 1)) (σ τ) : ℤ) + (D.mw l t (h / (l - 1)) τ : ℤ)) *
        ((t : ℤ) + 2 * ((h / (l - 1) : ℕ) : ℤ))

def MwLetters : Prop :=
  ∀ (ι : Type) (N : ℕ) (D : Labels ι N) (σ : Equiv.Perm ι) (h t : ℕ), D.Refl σ h t →
    ∀ (l κ : ℕ) (i : ι), D.mw l t κ (D.cc i) = D.mw l t κ i

def LinkedAll : Prop :=
  ∀ (ι : Type) (N : ℕ) (D : Labels ι N) (σ : Equiv.Perm ι) (h t : ℕ) (F : Type) [Field F]
    (cst : ι → ℤ), D.Refl σ h t → D.Linked F t cst →
    ∀ i, StrictAnti (D.U i) ∧ StrictAnti (D.U' i) ∧
      (∀ s : Fin t, ∃ a, D.U i a = D.bot i + ((s : ℕ) : ℤ)) ∧
      (∏ a, (Polynomial.X + Polynomial.C (((D.U i a + 0 : ℤ)) : F))) =
        ∏ a, (Polynomial.X + Polynomial.C (((D.U' i a + 0 : ℤ)) : F))

def WEOrientLattice : Prop :=
  ∀ (ι : Type) [Fintype ι] (σ : Equiv.Perm ι) (k j t q l h : ℕ) [Fact l.Prime] (O F L : Type)
    [CommRing O] [IsDomain O] [Algebra ℤ_[l] O] [Field F] [CharP F l] [Field L] (I : Ideal O)
    [IsAdicComplete I O] (W : FrobeniusPeriodChange.WLat ι t (k + j + t + q) O F) (u : ℤ_[l]ˣ) (c : ℤ_[l])
    (D : Labels ι (k + j + t + q)) (cst : ι → ℤ)
    (ep : ι → ι) (J : ι → Fin (k + j + t + q) → ℤ) (botJ : ι → ℤ) (kap : ι → Fin t → ℤ) (τ : ι)
    (ζ : O) (em : O →+* L) (jj : ℕ → PowerSeries O →+* PowerSeries L),
    l ≠ 2 → t + 2 * (h / (l - 1)) < l →
    D.Refl σ h t → D.Linked F t cst → D.Carried ep J botJ →
    FrobeniusPeriodChange.NInputs W σ l h u c J (fun i s => botJ i + ((s : ℕ) : ℤ)) kap I ζ em jj →
    ShapeAt k j t q D τ →
    DepthBound k j t q l h D σ τ

end Formalism.CohomologicalDescent.WorkedExample
end
end

