module

public import Formalism.MahlerMeasure.Bundle0002

@[expose] public section

-- bundled from Formalism.MahlerMeasure.IsFrozenInv
section
namespace Formalism.GM.M

open MvPolynomial Finset

def Letters.snoc {N : ℕ} (LL : Letters N) (n : ℕ) : Letters (N + 1) where
  vec := Fin.lastCases false LL.vec
  deg := Fin.lastCases n LL.deg

def Letters.total {N : ℕ} (LL : Letters N) : ℕ := ∑ i, LL.deg i

noncomputable def freezeSub (p : ℕ) [Fact p.Prime] {N r : ℕ} (LL : Letters N) (ρ : Fin r) :
    Fin N × Fin r → MvPolynomial (Fin (N + 1) × Fin r) ℚ_[p] :=
  fun ⟨i, c⟩ =>
    if LL.vec i then
      (if c = ρ then ∑ c', X (Fin.castSucc i, c') * X (Fin.last N, c')
       else X (Fin.last N, ρ) * X (Fin.castSucc i, c))
    else
      (if c = ρ then X (Fin.last N, ρ) * X (Fin.castSucc i, ρ)
       else X (Fin.last N, ρ) * X (Fin.castSucc i, c) - X (Fin.castSucc i, ρ) * X (Fin.last N, c))

noncomputable def freeze (p : ℕ) [Fact p.Prime] {N r : ℕ} (LL : Letters N) (ρ : Fin r) (n : ℕ)
    (f : MvPolynomial (Fin N × Fin r) ℚ_[p]) : MvPolynomial (Fin (N + 1) × Fin r) ℚ_[p] :=
  X (Fin.last N, ρ) ^ (n - LL.total) * aeval (freezeSub p LL ρ) f

def IsFrozenInv (p : ℕ) [Fact p.Prime] {N r : ℕ} (LL : Letters N) (ρ : Fin r) (n : ℕ)
    (F : MvPolynomial (Fin (N + 1) × Fin r) ℚ_[p]) : Prop :=
  ∀ c, c ≠ ρ → glAct p (LL.snoc n) (N + 1) c ρ F = 0

def FreezeInto : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (N r : ℕ) (LL : Letters N) (ρ : Fin r) (n : ℕ), LL.total ≤ n →
    ∀ f ∈ Pol p r LL,
      freeze p LL ρ n f ∈ Pol p r (LL.snoc n) ∧ IsFrozenInv p LL ρ n (freeze p LL ρ n f) ∧
      (f ∈ IntPol p (Fin N × Fin r) → freeze p LL ρ n f ∈ IntPol p (Fin (N + 1) × Fin r))

def FreezeBij : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (N r : ℕ) (LL : Letters N) (ρ : Fin r) (n : ℕ), LL.total ≤ n →
    (∀ f ∈ Pol p r LL, ∀ g ∈ Pol p r LL, freeze p LL ρ n f = freeze p LL ρ n g → f = g) ∧
    (∀ F ∈ PolZ p r (LL.snoc n), IsFrozenInv p LL ρ n F → ∃ f ∈ PolZ p r LL, freeze p LL ρ n f = F)

def FreezeY : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (N r : ℕ) [NeZero r] (LL : Letters N) (ρ : Fin r) (n : ℕ) {q : ℕ}
    (J : Fin q → ℕ) (Mt : Fin q → WithTop ℤ), LL.total ≤ n → (∀ k, J k ≤ N) →
    ∀ f ∈ Pol p r LL, (f ∈ Y p LL J Mt ↔ freeze p LL ρ n f ∈ Y p (LL.snoc n) J Mt)

def FreezeStep : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (N r : ℕ) (LL : Letters N) (ρ : Fin r) (n : ℕ), LL.total ≤ n →
    ∀ f : MvPolynomial (Fin N × Fin r) ℚ_[p],
      X (Fin.last N, ρ) * freeze p LL ρ n f = freeze p LL ρ (n + 1) f

end Formalism.GM.M
end

-- bundled from Formalism.MahlerMeasure.IsIntegral
section
namespace Formalism.GM.M

open MvPolynomial Finset

def IsIntegral' {σ : Type} (p : ℕ) [Fact p.Prime] (u : MvPolynomial σ ℚ_[p]) : Prop :=
  ∀ m, ‖u.coeff m‖ ≤ 1

def PhiInt : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (σ : Type) (r : ℕ) (w e : Fin r → σ), Function.Injective w → Function.Injective e →
    (∀ c d, w c ≠ e d) → 1 ≤ r →
    ∀ (o n z : ℕ) (u : MvPolynomial σ ℚ_[p]), IsIntegral' p u →
      IsIntegral' p (((p : ℚ_[p]) ^ ((r + 1) * (Nat.log p (o + n + r + z) + 1))) • Formalism.GM.tiePhi w e o n z u)

end Formalism.GM.M
end

-- bundled from Formalism.MahlerMeasure.StatementD
section
namespace Formalism.GM

open Finset Polynomial

noncomputable def gaussR {K : Type} [NormedField K] (ρ : NNReal) (P : K[X]) : NNReal :=
  P.support.sup (fun k => ‖P.coeff k‖₊ * ρ ^ k)

def GaussMulRad : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] (ρ : NNReal) (P Q : K[X]), 0 < ρ →
    gaussR ρ (P * Q) = gaussR ρ P * gaussR ρ Q

noncomputable def binK (K : Type) [Field K] (k : ℕ) : K[X] :=
  Polynomial.C (((k.factorial : K))⁻¹) * descPochhammer K k

def MahlerK : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K : Type) [NormedField K] [NormedAlgebra ℚ_[p] K] (h k : ℕ) (t₀ : ℤ), k ≤ p ^ h →
    ∀ m : ℕ, ‖((binK K k).comp (Polynomial.C ((p : K) ^ h) * X + Polynomial.C (t₀ : K))).coeff m‖ ≤ 1

def SmithZp : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (n : ℕ) (M : Matrix (Fin n) (Fin n) ℤ_[p]),
    ∃ (U V : Matrix (Fin n) (Fin n) ℤ_[p]) (d : Fin n → ℤ_[p]),
      IsUnit U.det ∧ IsUnit V.det ∧ M = U * Matrix.diagonal d * V

noncomputable def binMatK (K : Type) [Field K] {n : ℕ} (del₀ : ℕ) (c : Fin n → Fin n → ℕ → K) :
    Matrix (Fin n) (Fin n) K[X] :=
  fun i j => ∑ k ∈ range (del₀ + 1), Polynomial.C (c i j k) * binK K k


open Classical in
def ValuationWindowLowerBound : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K : Type) [NormedField K] [NormedAlgebra ℚ_[p] K] [IsUltrametricDist K]
    (n del₀ h : ℕ) (E : ℝ) (c : Fin n → Fin n → ℕ → K) (lead : K) (roots : Multiset K) (t₀ : ℤ)
    (U V : Matrix (Fin n) (Fin n) K) (d : Fin n → K),
    (∀ i j k, ‖c i j k‖ ≤ 1) → (∀ i j, ‖U i j‖ ≤ 1) → (∀ i j, ‖V i j‖ ≤ 1) →
    ‖U.det‖ = 1 → ‖V.det‖ = 1 → 0 ≤ E → del₀ ≤ p ^ h → lead ≠ 0 →
    (binMatK K del₀ c).det = Polynomial.C lead * (roots.map (fun ζ => X - Polynomial.C ζ)).prod →
    (binMatK K del₀ c).map (Polynomial.eval (t₀ : K)) = U * Matrix.diagonal d * V →
    ((univ.filter (fun i => ‖d i‖ ≤ (p : ℝ) ^ (-E))).card : ℝ) * E ≤
      (-Real.logb p ‖lead‖ + (roots.map (fun ζ => vmin p h ((t₀ : K) - ζ))).sum) +
        E * ((roots.filter (fun ζ => ‖(t₀ : K) - ζ‖ ≤ (p : ℝ) ^ (-(h : ℤ)))).card : ℝ)


end Formalism.GM
end

-- bundled from Formalism.MahlerMeasure.TieVars
section
namespace Formalism.GM.M

open MvPolynomial Finset

noncomputable def fockK {k σ : Type} [Field k] (F G : MvPolynomial σ k) : k :=
  ∑ m ∈ F.support, F.coeff m * G.coeff m * (m.prod fun _ j => (j.factorial : k))

noncomputable def tieEh {k σ : Type} [Field k] {r : ℕ} (w e : Fin r → σ) (zv sv : σ) :
    MvPolynomial σ k →ₗ[k] MvPolynomial σ k :=
  LinearMap.mulLeft k (X zv * X sv + ∑ c, X (w c) * X (e c))

noncomputable def tieFh {k σ : Type} [Field k] {r : ℕ} (w e : Fin r → σ) (zv sv : σ) :
    MvPolynomial σ k →ₗ[k] MvPolynomial σ k :=
  (pderiv zv).toLinearMap ∘ₗ (pderiv sv).toLinearMap + Formalism.GM.tieF w e

noncomputable def tieP {k σ : Type} [Field k] {r : ℕ} (w e : Fin r → σ) (zv sv : σ) (o n z : ℕ)
    (y : MvPolynomial σ k) : MvPolynomial σ k :=
  ∑ l ∈ range (o + 1),
    (((-1 : k) ^ l) / (((l.factorial : k) ^ 2) * ((o + n + r + z - 1).choose l : k))) •
      ((tieEh w e zv sv) ^ l) (((Formalism.GM.tieF w e) ^ l) (X zv ^ z * y))

def TieVars {σ : Type} {r : ℕ} (w e : Fin r → σ) (zv sv : σ) : Prop :=
  Function.Injective w ∧ Function.Injective e ∧ (∀ c d, w c ≠ e d) ∧ (∀ c, w c ≠ zv ∧ w c ≠ sv ∧ e c ≠ zv ∧
    e c ≠ sv) ∧ zv ≠ sv

def ZSFree {k σ : Type} [Field k] (zv sv : σ) (y : MvPolynomial σ k) : Prop :=
  ∀ m ∈ y.support, m zv = 0 ∧ m sv = 0

end Formalism.GM.M
end

