module

public import Mathlib

@[expose] public section

open Finset

noncomputable section

namespace Formalism.BranchingDeterminantCap

def MultPlace : Prop :=
  ∀ (q k r : ℕ) (Nn : ℕ → ℕ), 2 ≤ q → 1 ≤ k → k ≤ r → r ≤ q → Nn 0 = 1 →
    (∀ j, Nn j ≤ r.choose j) →
    ∀ gam : ℕ → ℝ, gam 0 = 1 → (∀ l, gam (l + 1) = (q : ℝ) ^ (l + 1) - (q : ℝ) ^ l) →
      (q : ℝ) ^ k * (1 - 1 / (q : ℝ)) ≤ ∑ j ∈ range (k + 1), (Nn j : ℝ) * gam (k - j) ∧
      ∑ j ∈ range (k + 1), (Nn j : ℝ) * gam (k - j) ≤
        (q : ℝ) ^ k * (1 + (2 * (r : ℝ) - 1) / (q : ℝ))

def MultProd : Prop :=
  ∀ (Pv : Type) [Fintype Pv] (q nn : Pv → ℝ) (k : ℕ) (f r g : ℝ),
    (Fintype.card Pv : ℝ) = 2 * f → 1 ≤ r → 0 < g → (∀ v, g ≤ q v) → 4 * f * r ≤ g →
    (∀ v, q v ^ k * (1 - 1 / q v) ≤ nn v ∧ nn v ≤ q v ^ k * (1 + (2 * r - 1) / q v)) →
      (1 - 8 * f * r / g) * ∏ v, q v ^ k ≤ ∏ v, nn v ∧
      ∏ v, nn v ≤ (1 + 8 * f * r / g) * ∏ v, q v ^ k

def TransferDeg : Prop :=
  ∀ (S : Type) [Fintype S] (rk nS dgA dgB : S → ℝ) (la degP : ℝ),
    (∀ s, |dgB s - nS s * dgA s| ≤ 13 / 2 * la * (nS s * rk s)) →
    ∑ s, dgB s ≤ degP → degP ≤ (∑ s, dgB s) + 2 * la * (∑ s, nS s * rk s) →
    0 ≤ la → (∀ s, 0 ≤ nS s * rk s) →
      |degP - ∑ s, nS s * dgA s| ≤ 17 / 2 * la * (∑ s, nS s * rk s)

def TransferMean : Prop :=
  ∀ (S : Type) [Fintype S] (rk nS dg : S → ℝ) (nbar de la ka HH0 muP0 muPs muR0 muRs : ℝ),
    0 < nbar → 0 ≤ de → de ≤ 1 / 3 → 0 ≤ la → 0 ≤ ka → (∀ s, 0 ≤ rk s) → 0 < ∑ s, rk s →
    (∀ s, (1 - de) * nbar ≤ nS s ∧ nS s ≤ (1 + de) * nbar) →
    |muR0 - muP0| ≤ ka * la → |muRs - muPs| ≤ ka * la →
    (∀ s, dg s ≤ rk s * (HH0 + ka * la)) →
    (∑ s, nS s * dg s) - 17 / 2 * la * (∑ s, nS s * rk s) ≤ muPs * (∑ s, nS s * rk s) →
    muP0 * (∑ s, rk s) ≤ (∑ s, dg s) + 2 * la * (∑ s, rk s) →
      0 ≤ -muR0 + HH0 + (2 * ka + 2) * la ∧
      -muRs ≤ -muR0 + 3 * de * (-muR0 + HH0 + (2 * ka + 2) * la) + (2 * ka + 21 / 2) * la

def Interlace {n : ℕ} (lam : Fin (n + 1) → ℤ) (sg : Fin n → ℤ) : Prop :=
  ∀ i : Fin n, sg i ≤ lam i.castSucc ∧ lam i.succ ≤ sg i

def d0 {n : ℕ} (lam : Fin (n + 1) → ℤ) (sg : Fin n → ℤ) : ℤ := ∑ i : Fin n, (sg i - lam i.succ)

def d1 {n : ℕ} (lam : Fin (n + 1) → ℤ) (sg : Fin n → ℤ) : ℤ :=
  ∑ i : Fin n, min (lam i.castSucc - lam i.succ) (d0 lam sg)

def rset {n : ℕ} (lam : Fin (n + 1) → ℤ) (sg : Fin n → ℤ) (i : Fin n) : Finset ℤ :=
  Finset.Icc (lam i.succ) (min (lam i.castSucc) (lam i.succ + d0 lam sg))

def capEig {n : ℕ} (lam : Fin (n + 1) → ℤ) (sg mu : Fin n → ℤ) : ℤ :=
  ∏ i : Fin n, ∏ v ∈ (rset lam sg i).erase (sg i), ∏ j : Fin n, ((v - (i : ℤ)) - (mu j - (j : ℤ)))

def cCap {n : ℕ} (lam : Fin (n + 1) → ℤ) (sg : Fin n → ℤ) : ℤ := capEig lam sg sg

def InterlaceIdent : Prop :=
  ∀ (n : ℕ) (lam : Fin (n + 1) → ℤ) (sg : Fin n → ℤ), Interlace lam sg →
    (∑ i, lam i) - (∑ i, sg i) = lam 0 - d0 lam sg ∧
    (∑ i : Fin n, (lam i.castSucc - sg i)) = lam 0 - lam (Fin.last n) - d0 lam sg ∧
    0 ≤ d0 lam sg ∧ 0 ≤ d1 lam sg ∧ (∀ i, sg i ∈ rset lam sg i) ∧
    (∀ i, (((rset lam sg i).erase (sg i)).card : ℤ) = min (lam i.castSucc - lam i.succ) (d0 lam sg))

def ConstituentRange : Prop :=
  ∀ (n : ℕ) (lam : Fin (n + 1) → ℤ) (sg mu : Fin n → ℤ), Interlace lam sg → Interlace lam mu →
    d0 lam mu = d0 lam sg → ∀ i, mu i ∈ rset lam sg i

def CapConst : Prop :=
  ∀ (n : ℕ) (lam : Fin (n + 1) → ℤ) (sg : Fin n → ℤ), Interlace lam sg →
    cCap lam sg ≠ 0 ∧
    |cCap lam sg| ≤ (lam 0 - lam (Fin.last n) + (n : ℤ) - 1) ^ (n * (d1 lam sg).toNat)

def WeylDimBound : Prop :=
  ∀ (n : ℕ) (nu : Fin (n + 1) → ℤ), Antitone nu →
    1 ≤ ∏ p ∈ (Finset.univ : Finset (Fin (n + 1) × Fin (n + 1))).filter (fun p => p.1 < p.2),
        (((nu p.1 - nu p.2 : ℤ) : ℝ) + ((p.2 : ℕ) : ℝ) - ((p.1 : ℕ) : ℝ)) /
          (((p.2 : ℕ) : ℝ) - ((p.1 : ℕ) : ℝ)) ∧
    ∏ p ∈ (Finset.univ : Finset (Fin (n + 1) × Fin (n + 1))).filter (fun p => p.1 < p.2),
        (((nu p.1 - nu p.2 : ℤ) : ℝ) + ((p.2 : ℕ) : ℝ) - ((p.1 : ℕ) : ℝ)) /
          (((p.2 : ℕ) : ℝ) - ((p.1 : ℕ) : ℝ)) ≤
      (((nu 0 - nu (Fin.last n) : ℤ) : ℝ) + (n : ℝ)) ^ ((n + 1) * n / 2)

end Formalism.BranchingDeterminantCap
