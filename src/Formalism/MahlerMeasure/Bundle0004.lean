module

public import Formalism.MahlerMeasure.Bundle0003
public import Formalism.MahlerMeasure.MahlerMeasureProofs.Bundle0001
public import Formalism.MahlerMeasure.Bundle0001
public import Formalism.MahlerMeasure.MahlerMeasureProofs.Mahler
public import Mathlib

@[expose] public section

-- bundled from Formalism.MahlerMeasure.HasOrder
section
namespace Formalism.GM.M

open MvPolynomial Finset

def HasOrder {σ : Type} {p : ℕ} [Fact p.Prime] (v : σ) (e : ℕ) (f : MvPolynomial σ ℚ_[p]) : Prop :=
  (∀ m ∈ f.support, e ≤ m v) ∧ ∃ m ∈ f.support, m v = e

noncomputable def initPart {σ : Type} {p : ℕ} [Fact p.Prime] (v : σ) (e : ℕ) (f : MvPolynomial σ ℚ_[p]) :
    MvPolynomial σ ℚ_[p] :=
  ∑ m ∈ f.support, if m v = e then monomial m (f.coeff m) else 0

noncomputable def tieGam (p : ℕ) [Fact p.Prime] {N r : ℕ} (LL : Letters (N + 1)) (ρ : Fin r) (z n : ℕ)
    (f f' : MvPolynomial (Fin (N + 1) × Fin r) ℚ_[p]) : ℚ_[p] :=
  (((LL.deg (Fin.last N) + n + r + z - 1).choose (LL.deg (Fin.last N)) : ℕ) : ℚ_[p]) *
    fock p (tiePhiAt p (LL.snoc n) (Fin.castSucc (Fin.last N)) (Fin.last (N + 1)) z (freeze p LL ρ n f))
      (freeze p LL ρ n f') /
    ((((n - LL.total).factorial * LL.total.factorial : ℕ) : ℚ_[p]) * ∏ i, ((LL.deg i).factorial : ℚ_[p]))

def GamDeg : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (N r : ℕ) (LL : Letters (N + 1)) (ρ : Fin r) (z e e' : ℕ)
    (f f' : MvPolynomial (Fin (N + 1) × Fin r) ℚ_[p]),
    1 ≤ r → LL.vec (Fin.last N) = true → f ∈ Pol p r LL → f' ∈ Pol p r LL →
    HasOrder (Fin.last N, ρ) e f → HasOrder (Fin.last N, ρ) e' f' →
    ∃ P : Polynomial ℚ_[p], P.natDegree ≤ LL.total + LL.deg (Fin.last N) - max e e' ∧
      ∀ n, LL.total ≤ n → tieGam p LL ρ z n f f' = P.eval (n : ℚ_[p])

def GamLead : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (N r : ℕ) (LL : Letters (N + 1)) (ρ : Fin r) (z e : ℕ)
    (f f' : MvPolynomial (Fin (N + 1) × Fin r) ℚ_[p]) (P : Polynomial ℚ_[p]),
    1 ≤ r → LL.vec (Fin.last N) = true → f ∈ Pol p r LL → f' ∈ Pol p r LL →
    HasOrder (Fin.last N, ρ) e f → HasOrder (Fin.last N, ρ) e f' →
    (∀ n, LL.total ≤ n → tieGam p LL ρ z n f f' = P.eval (n : ℚ_[p])) →
    P.coeff (LL.total + LL.deg (Fin.last N) - e) =
      ((e.factorial * (z + e).choose e : ℕ) : ℚ_[p]) *
        fock p (initPart (Fin.last N, ρ) e f) (initPart (Fin.last N, ρ) e f') /
        ((((LL.deg (Fin.last N)).factorial * LL.total.factorial : ℕ) : ℚ_[p]) *
          ∏ i, ((LL.deg i).factorial : ℚ_[p]))

end Formalism.GM.M
end

-- bundled from Formalism.MahlerMeasure.LegendreDigits
section
namespace Formalism.GM.Top
open Formalism.GM
theorem detBlockLead : DetBlockLead := determinant_block_leading_term
end Formalism.GM.Top
end

-- bundled from Formalism.MahlerMeasure.LieRoots
section
namespace Formalism.GM

open Finset Polynomial

open Classical in
def LieMat : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K : Type) [NormedField K] [NormedAlgebra ℚ_[p] K] [IsUltrametricDist K]
    (n del₀ h : ℕ) (E : ℝ) (c : Fin n → Fin n → ℕ → K) (t₀ : ℤ)
    (U V : Matrix (Fin n) (Fin n) K) (d : Fin n → K),
    (∀ i j k, ‖c i j k‖ ≤ 1) → (∀ i j, ‖U i j‖ ≤ 1) → (∀ i j, ‖V i j‖ ≤ 1) →
    ‖U.det‖ = 1 → ‖V.det‖ = 1 → 0 ≤ E → del₀ ≤ p ^ h →
    (binMatK K del₀ c).map (Polynomial.eval (t₀ : K)) = U * Matrix.diagonal d * V →
    (gaussR (Real.toNNReal ((p : ℝ) ^ (-E)))
        (((binMatK K del₀ c).det).comp (Polynomial.C ((p : K) ^ h) * X + Polynomial.C (t₀ : K))) : ℝ) ≤
      (p : ℝ) ^ (-(E * (univ.filter (fun i => ‖d i‖ ≤ (p : ℝ) ^ (-E))).card))

def LieRoots : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K : Type) [NormedField K] [NormedAlgebra ℚ_[p] K] [IsUltrametricDist K]
    (h β : ℕ) (E : ℝ) (D : K[X]) (lead : K) (roots : Multiset K) (t₀ : ℤ),
    0 ≤ E → lead ≠ 0 →
    D = Polynomial.C lead * (roots.map (fun ζ => X - Polynomial.C ζ)).prod →
    (gaussR (Real.toNNReal ((p : ℝ) ^ (-E)))
        (D.comp (Polynomial.C ((p : K) ^ h) * X + Polynomial.C (t₀ : K))) : ℝ) ≤ (p : ℝ) ^ (-(E * β)) →
    (β : ℝ) * E ≤
      (-Real.logb p ‖lead‖ + (roots.map (fun ζ => vmin p h ((t₀ : K) - ζ))).sum) +
        E * ((roots.filter (fun ζ => ‖(t₀ : K) - ζ‖ ≤ (p : ℝ) ^ (-(h : ℤ)))).card : ℝ)

end Formalism.GM
end

-- bundled from Formalism.MahlerMeasure.QuotientUpperBoundsOfPowerBounds
section
namespace Formalism.GM

open Finset Polynomial

def progr (t₀ d : ℤ) (j : ℕ) : ℤ := t₀ + d * (j : ℤ)

def WindowCountAP : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K : Type) [NormedField K] [NormedAlgebra ℚ_[p] K] [IsUltrametricDist K]
    (ζ : K) (t₀ d : ℤ) (Y₀ h : ℕ), IsCoprime d (p : ℤ) →
    ∑ j ∈ range Y₀, vmin p h ((progr t₀ d j : K) - ζ) ≤ ∑ i ∈ Icc 1 h, ((Y₀ : ℝ) / (p : ℝ) ^ i + 1)

open Classical in
def DiscsDisjointAP : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K : Type) [NormedField K] [NormedAlgebra ℚ_[p] K] [IsUltrametricDist K]
    (roots : Multiset K) (t₀ d : ℤ) (Y₀ h : ℕ), IsCoprime d (p : ℤ) → Y₀ ≤ p ^ h →
    ∑ j ∈ range Y₀, (roots.filter (fun ζ => ‖(progr t₀ d j : K) - ζ‖ ≤ (p : ℝ) ^ (-(h : ℤ)))).card ≤
      roots.card

open Classical in
def WindowMeanAP : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K : Type) [NormedField K] [NormedAlgebra ℚ_[p] K] [IsUltrametricDist K]
    (roots : Multiset K) (lam La₀ E : ℝ) (n₀ del₀ : ℕ) (t₀ d : ℤ) (Y₀ h : ℕ) (β : ℤ → ℕ),
    IsCoprime d (p : ℤ) → 0 < Y₀ → Y₀ ≤ p ^ h → 0 < E →
    roots.card ≤ del₀ * n₀ →
    lam + (roots.card : ℝ) / ((p : ℝ) - 1) ≤ (n₀ : ℝ) * La₀ →
    (∀ j ∈ range Y₀,
      (β (progr t₀ d j) : ℝ) * E ≤ (lam + (roots.map (fun ζ => vmin p h ((progr t₀ d j : K) - ζ))).sum) +
        E * ((roots.filter (fun ζ => ‖(progr t₀ d j : K) - ζ‖ ≤ (p : ℝ) ^ (-(h : ℤ)))).card : ℝ)) →
    (∑ j ∈ range Y₀, (β (progr t₀ d j) : ℝ)) / (Y₀ : ℝ) ≤
      (n₀ : ℝ) * ((del₀ : ℝ) / Y₀ + (La₀ + (del₀ : ℝ) * h / Y₀) / E)


open Classical in
def WindowFullAP : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K : Type) [NormedField K] [NormedAlgebra ℚ_[p] K] [IsUltrametricDist K]
    (n del₀ h : ℕ) (E : ℝ) (c : Fin n → Fin n → ℕ → K) (lead : K) (roots : Multiset K) (t₀ d : ℤ) (Y₀ : ℕ)
    (La₀ : ℝ) (U V : ℤ → Matrix (Fin n) (Fin n) K) (dg : ℤ → Fin n → K),
    IsCoprime d (p : ℤ) → 0 < Y₀ → Y₀ ≤ p ^ h → del₀ ≤ p ^ h → 0 < E → lead ≠ 0 → (∀ i j k, ‖c i j k‖ ≤ 1) →
    (binMatK K del₀ c).det = Polynomial.C lead * (roots.map (fun ζ => X - Polynomial.C ζ)).prod →
    (∀ j ∈ range Y₀, (∀ a b, ‖U (progr t₀ d j) a b‖ ≤ 1) ∧ (∀ a b, ‖V (progr t₀ d j) a b‖ ≤ 1) ∧
      ‖(U (progr t₀ d j)).det‖ = 1 ∧ ‖(V (progr t₀ d j)).det‖ = 1 ∧
      (binMatK K del₀ c).map (Polynomial.eval ((progr t₀ d j : ℤ) : K)) =
        U (progr t₀ d j) * Matrix.diagonal (dg (progr t₀ d j)) * V (progr t₀ d j)) →
    -Real.logb p ‖lead‖ + (roots.card : ℝ) / ((p : ℝ) - 1) ≤ (n : ℝ) * La₀ →
    (∑ j ∈ range Y₀, ((univ.filter (fun i => ‖dg (progr t₀ d j) i‖ ≤ (p : ℝ) ^ (-E))).card : ℝ)) / (Y₀ : ℝ) ≤
      (n : ℝ) * ((del₀ : ℝ) / Y₀ + (La₀ + (del₀ : ℝ) * h / Y₀) / E)

def QuotientUpperBoundsOfPowerBounds : Prop :=
  ∀ (p a Y k Ns Qn be : ℝ) (D₁ L₁ Rj Rn : ℤ),
    1 < p → 0 < a → 0 < Y → 0 < k → 0 < Ns → 0 < Qn →
    be ≤ 4 * a * p ^ (-D₁ - L₁ - Rj) →
    a / (8 * Y * k ^ 2 * Ns * p ^ D₁ * Qn) < p ^ (Rn + 1) →
    128 * k ^ 2 * Ns * Y ^ 2 ≤ p ^ (L₁ - 1) →
    be / (Qn * p ^ (Rn - Rj)) ≤ 32 * p * Y * k ^ 2 * Ns * p ^ (-L₁) ∧
      32 * p * Y * k ^ 2 * Ns * p ^ (-L₁) ≤ 1 / (4 * Y)

noncomputable def lgV2 (p a r : ℕ) : ℝ := Real.logb p (8 * a + r) + 1

end Formalism.GM
end

